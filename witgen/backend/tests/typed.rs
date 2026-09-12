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
    assert_eq!(point_add(g, g), point_scale(SecpScalar::from(2u64), g));
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
    assert_eq!(secp_base_to_nat(point_x(point_identity())), 0);
}
