use rug::Integer;
use witgen_native::{typed::*, Error};

#[test]
fn word_primitives_match_double_width_test_oracle() {
    for a in [0, 1, u64::MAX - 1, u64::MAX] {
        for b in [0, 1, u64::MAX - 1, u64::MAX] {
            for carry in [false, true] {
                let sum = a as u128 + b as u128 + carry as u128;
                assert_eq!(adc(a, b, carry), (sum as u64, sum >> 64 != 0));
                let borrow = (a as u128) < b as u128 + carry as u128;
                assert_eq!(
                    sbb(a, b, carry),
                    (a.wrapping_sub(b).wrapping_sub(carry as u64), borrow)
                );
            }
        }
    }
    assert!(bit_at([0, 0, 0, 1 << 63], 255));
    assert!(!bit_at([u64::MAX; 4], 256));
}

#[test]
fn field_identity_codecs_preserve_full_width_and_reject_aliases() {
    let base = field_modulus(1).unwrap();
    let scalar = field_modulus(2).unwrap();
    assert!(base > scalar);
    let value: Integer = scalar.clone() - 1;
    let json = serde_json::Value::String(value.to_string());
    let word = parse_word_field::<2>(&json).unwrap();
    assert_eq!(word_field_decimal(word), value.to_string());
    assert_eq!(parse_nat_field::<2>(&json).unwrap().0, value);
    assert_eq!(
        secp_scalar_to_nat(secp_scalar_from_nat(&value).unwrap()),
        value
    );
    assert_eq!(
        secp_base_to_nat(secp_base_from_nat(&(base.clone() - 1)).unwrap()),
        base.clone() - 1
    );
    assert!(matches!(
        parse_word_field::<2>(&serde_json::json!(scalar.to_string())),
        Err(Error::NonCanonicalField { .. })
    ));
    assert!(field_modulus(3).is_err());
    assert!(parse_word_field::<99>(&serde_json::json!("0")).is_err());
}

#[test]
fn raw_nat_neg_inv_cover_all_prime_fields_without_changing_inputs() {
    fn check<const ID: u8>() {
        let p = field_modulus(ID).unwrap();
        for a in [
            Integer::from(0),
            Integer::from(1),
            p.clone() - 1,
            p.clone(),
            p.clone() + 1,
            p.clone() * 2,
            (Integer::from(1) << 600) + 17,
        ] {
            let original = NatField::<ID>(a.clone());
            let neg = nat_field_neg(original.clone()).unwrap().0;
            let inv = nat_field_inv(original.clone()).unwrap().0;
            assert_eq!(original.0, a);
            assert!(neg >= 0 && neg < p);
            assert!(inv >= 0 && inv < p);
            assert_eq!((a.clone() + neg) % &p, 0);
            if a.clone() % &p == 0 {
                assert_eq!(inv, 0);
            } else {
                assert_eq!((a * inv) % &p, 1);
            }
        }
        assert!(matches!(
            nat_field_neg(NatField::<ID>(Integer::from(-1))),
            Err(Error::NegativeNatural)
        ));
        assert!(matches!(
            nat_field_inv(NatField::<ID>(Integer::from(-1))),
            Err(Error::NegativeNatural)
        ));
    }
    check::<0>();
    check::<1>();
    check::<2>();
    assert!(matches!(
        nat_field_neg(NatField::<99>(Integer::from(0))),
        Err(Error::UnknownField(99))
    ));
    assert!(matches!(
        nat_field_inv(NatField::<99>(Integer::from(0))),
        Err(Error::UnknownField(99))
    ));
}

/// Independent integer oracle: square chosen signed roots, never call a sqrt helper.
fn check_sqrt_vectors(id: u8, sqrt: impl Fn(Integer) -> Option<Integer>) {
    let p = field_modulus(id).unwrap();
    for root in [
        Integer::from(0),
        Integer::from(1),
        Integer::from(2),
        Integer::from(17),
        (Integer::from(1) << 200) + 17,
        p.clone() / 2,
        p.clone() - 2,
        p.clone() - 1,
    ] {
        let square = root.clone().square() % &p;
        let expected = root.clone().min((p.clone() - &root) % &p);
        let actual = sqrt(square.clone()).expect("chosen square has a root");
        assert_eq!(actual, expected, "field {id}, chosen root {root}");
        assert_eq!(actual.clone().square() % &p, square);
        assert!(actual <= p.clone() - &actual);
    }
    let exponent: Integer = (p.clone() - 1) / 2;
    let mut nonresidue = Integer::from(2);
    while nonresidue.clone().pow_mod(&exponent, &p).unwrap() == 1 {
        nonresidue += 1;
    }
    assert_eq!(nonresidue.clone().pow_mod(&exponent, &p).unwrap(), p - 1);
    assert_eq!(sqrt(nonresidue), None);
}

#[test]
fn native_sqrt_all_prime_fields_uses_smallest_integer_root() {
    check_sqrt_vectors(0, |a| {
        bn254_sqrt(witgen_native::bn254_from_nat(&a).unwrap()).map(witgen_native::bn254_to_nat)
    });
    check_sqrt_vectors(1, |a| {
        secp_base_sqrt(secp_base_from_nat(&a).unwrap()).map(secp_base_to_nat)
    });
    check_sqrt_vectors(2, |a| {
        secp_scalar_sqrt(secp_scalar_from_nat(&a).unwrap()).map(secp_scalar_to_nat)
    });
}

#[test]
fn native_sqrt_corrects_both_arkworks_sign_choices() {
    fn check<F: ark_ff::PrimeField>(
        id: u8,
        parse: fn(&Integer) -> witgen_native::Result<F>,
        to_nat: fn(F) -> Integer,
        sqrt: fn(F) -> Option<F>,
    ) {
        let p = field_modulus(id).unwrap();
        let mut signs = [false; 2];
        for i in 1..=64 {
            let root: Integer = (Integer::from(i) << 180) + i;
            let square = root.clone().square() % &p;
            let input = parse(&square).unwrap();
            let ark_root = to_nat(input.sqrt().unwrap());
            signs[usize::from(ark_root > p.clone() - &ark_root)] = true;
            // Expected result is from a chosen integer root, not Arkworks sqrt.
            assert_eq!(
                to_nat(sqrt(input).unwrap()),
                root.clone().min(p.clone() - root)
            );
        }
        assert_eq!(
            signs,
            [true, true],
            "field {id}: must exercise both Arkworks root signs"
        );
    }
    check(
        0,
        witgen_native::bn254_from_nat,
        witgen_native::bn254_to_nat,
        bn254_sqrt,
    );
    check(1, secp_base_from_nat, secp_base_to_nat, secp_base_sqrt);
    check(
        2,
        secp_scalar_from_nat,
        secp_scalar_to_nat,
        secp_scalar_sqrt,
    );
}

#[test]
fn nat_sqrt_reduces_raw_values_without_changing_pack_or_input_codec() {
    fn check<const ID: u8>() {
        let p = field_modulus(ID).unwrap();
        check_sqrt_vectors(ID, |a| {
            // Include very wide multiples; the explicit sqrt must reduce, not pack.
            let raw = NatField::<ID>(a + (p.clone() << 600));
            let original = raw.clone();
            let root: Option<NatField<ID>> = nat_field_sqrt(raw.clone()).unwrap();
            assert_eq!(raw, original);
            root.map(|r| r.0)
        });
        for a in [p.clone(), p.clone() * 2] {
            assert_eq!(nat_field_sqrt(NatField::<ID>(a)).unwrap().unwrap().0, 0);
        }
        assert!(matches!(
            nat_field_sqrt(NatField::<ID>(Integer::from(-1))),
            Err(Error::NegativeNatural)
        ));
        assert!(matches!(
            parse_nat_field::<ID>(&serde_json::json!(p.to_string())),
            Err(Error::NonCanonicalField { .. })
        ));
    }
    check::<0>();
    check::<1>();
    check::<2>();
    assert!(matches!(
        nat_field_sqrt(NatField::<99>(Integer::from(0))),
        Err(Error::UnknownField(99))
    ));
}

fn check_sub_vectors(id: u8, sub: impl Fn(Integer, Integer) -> Integer) {
    let p = field_modulus(id).unwrap();
    let values = [
        Integer::from(0),
        Integer::from(1),
        Integer::from(2),
        p.clone() - 1,
        (Integer::from(1) << 200) + 17,
    ];
    for a in &values {
        for b in &values {
            let difference = sub(a.clone(), b.clone());
            assert!(difference >= 0 && difference < p);
            // Independent characterizing equation, not the implementation formula.
            assert_eq!((difference + b) % &p, *a);
        }
    }
}

#[test]
fn native_sub_all_prime_fields_is_canonical_modular_difference() {
    check_sub_vectors(0, |a, b| {
        witgen_native::bn254_to_nat(bn254_sub(
            witgen_native::bn254_from_nat(&a).unwrap(),
            witgen_native::bn254_from_nat(&b).unwrap(),
        ))
    });
    check_sub_vectors(1, |a, b| {
        secp_base_to_nat(secp_base_sub(
            secp_base_from_nat(&a).unwrap(),
            secp_base_from_nat(&b).unwrap(),
        ))
    });
    check_sub_vectors(2, |a, b| {
        secp_scalar_to_nat(secp_scalar_sub(
            secp_scalar_from_nat(&a).unwrap(),
            secp_scalar_from_nat(&b).unwrap(),
        ))
    });
}

#[test]
fn nat_sub_reduces_both_raw_operands_without_normalizing_inputs() {
    fn check<const ID: u8>() {
        let p = field_modulus(ID).unwrap();
        check_sub_vectors(ID, |a, b| {
            let raw_a = NatField::<ID>(a + (p.clone() << 600));
            let raw_b = NatField::<ID>(b + p.clone() * 7);
            let originals = (raw_a.clone(), raw_b.clone());
            let difference = nat_field_sub(raw_a.clone(), raw_b.clone()).unwrap().0;
            assert_eq!((raw_a, raw_b), originals);
            difference
        });
        for (a, b) in [(-1, 0), (0, -1)] {
            assert!(matches!(
                nat_field_sub(
                    NatField::<ID>(Integer::from(a)),
                    NatField::<ID>(Integer::from(b))
                ),
                Err(Error::NegativeNatural)
            ));
        }
    }
    check::<0>();
    check::<1>();
    check::<2>();
    assert!(matches!(
        nat_field_sub(
            NatField::<99>(Integer::from(0)),
            NatField::<99>(Integer::from(0))
        ),
        Err(Error::UnknownField(99))
    ));
}

#[test]
fn point_eq_compares_math_not_sec1_or_projective_representations() {
    use ark_ff::Field;
    let g = point_generator();
    let (x, y) = to_affine(g).unwrap();
    let z = SecpBase::from(17u64);
    let rescaled = SecpPoint::new_unchecked(x * z.square(), y * z.square() * z, z);
    assert_ne!(g.z, rescaled.z);
    let equal: bool = point_eq(g, rescaled);
    assert!(equal);
    let compressed = parse_point(&serde_json::json!(point_hex(g))).unwrap();
    let uncompressed = parse_point(&serde_json::json!(concat!(
        "0479be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798",
        "483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8"
    )))
    .unwrap();
    assert!(point_eq(compressed, uncompressed));
    assert!(point_eq(point_identity(), point_add(g, point_inv(g))));
    assert!(point_eq(point_inv(g), point_inv(rescaled)));
    assert!(!point_eq(g, point_inv(g)));
    assert!(!point_eq(g, point_identity()));
    assert!(!point_eq(point_identity(), g));
}

#[test]
fn msm_uses_typed_terms_and_full_width_canonical_scalars() {
    let g = point_generator();
    let neg_g = point_inv(g);
    let id = point_identity();
    let zero = SecpScalar::from(0u64);
    let one = SecpScalar::from(1u64);
    let two = SecpScalar::from(2u64);
    let three = SecpScalar::from(3u64);
    let minus_one = secp_scalar_from_nat(&(field_modulus(2).unwrap() - 1)).unwrap();
    assert_eq!(point_msm(vec![]).unwrap(), id);
    for (s, p) in [
        (zero, g),
        (one, g),
        (minus_one, g),
        (minus_one, id),
        (two, neg_g),
    ] {
        assert_eq!(point_msm(vec![(s, p)]).unwrap(), point_mul(s, p));
    }
    assert_eq!(
        point_msm(vec![(two, g), (three, g)]).unwrap(),
        point_add(point_add(g, g), point_add(point_add(g, g), g))
    );
    assert_eq!(point_msm(vec![(one, g), (one, neg_g)]).unwrap(), id);
    assert_eq!(point_msm(vec![(minus_one, g), (one, g)]).unwrap(), id);
    assert_eq!(
        point_msm(vec![(minus_one, g), (minus_one, neg_g)]).unwrap(),
        id
    );
    assert_eq!(
        point_msm(vec![(one, g); 40]).unwrap(),
        point_mul(SecpScalar::from(40u64), g)
    );
    let high = secp_scalar_from_nat(&(Integer::from(1) << 255)).unwrap();
    let complement =
        secp_scalar_from_nat(&(field_modulus(2).unwrap() - (Integer::from(1) << 255))).unwrap();
    assert_eq!(point_msm(vec![(high, g), (complement, g)]).unwrap(), id);
    let (x, y) = to_affine(g).unwrap();
    let z = SecpBase::from(17u64);
    let rescaled = SecpPoint::new_unchecked(x * z * z, y * z * z * z, z);
    assert_eq!(point_msm(vec![(one, rescaled), (one, neg_g)]).unwrap(), id);
}

#[test]
fn real_curve_operations_and_explicit_affine_optionality() {
    assert_eq!(
        std::any::TypeId::of::<SecpPoint>(),
        std::any::TypeId::of::<ark_secp256k1::Projective>()
    );
    assert_eq!(
        std::any::TypeId::of::<SecpBase>(),
        std::any::TypeId::of::<ark_secp256k1::Fq>()
    );
    assert_eq!(
        std::any::TypeId::of::<SecpScalar>(),
        std::any::TypeId::of::<ark_secp256k1::Fr>()
    );
    let g = point_generator();
    assert_eq!(point_add(g, g), point_mul(SecpScalar::from(2u64), g));
    assert_eq!(point_mul(SecpScalar::from(0u64), g), point_identity());
    assert_eq!(point_mul(SecpScalar::from(1u64), g), g);
    let minus_one = secp_scalar_from_nat(&(field_modulus(2).unwrap() - 1)).unwrap();
    assert_eq!(point_mul(minus_one, g), point_inv(g));
    assert_eq!(point_add(g, point_inv(g)), point_identity());
    let coords = to_affine(g).unwrap();
    assert_eq!(from_affine(coords), Some(g));
    assert_eq!(to_affine(point_identity()), None);
    let zero = secp_base_from_nat(&Integer::from(0)).unwrap();
    assert_eq!(from_affine((zero, zero)), None);
    let encoded = point_hex(g);
    assert_eq!(parse_point(&serde_json::json!(encoded)).unwrap(), g);
    assert_eq!(
        parse_point(&serde_json::json!("00")).unwrap(),
        point_identity()
    );
    assert!(parse_point(&serde_json::json!("zz")).is_err());
}
