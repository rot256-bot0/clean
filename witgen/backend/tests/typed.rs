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
