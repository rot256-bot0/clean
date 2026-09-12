use rug::Integer;
use witgen_native::*;

#[test]
fn arkworks_field_quadratic() {
    let x = f17_from_u64(3).unwrap();
    let y = f17_from_u64(4).unwrap();
    let square = f17_mul(x, x);
    assert_eq!(f17_to_u64(square), 9);
    assert_eq!(f17_to_u64(f17_add(square, y)), 13);
    assert!(f17_from_u64(17).is_err());
}

#[test]
fn gmp_integers_are_not_machine_words() {
    let x = Integer::from(1) << 130u32;
    let product = nat_mul(&x, &x);
    let expected = Integer::from(1) << 260u32;
    assert_eq!(product, expected);
    assert_eq!(nat_div(&product, &x).unwrap(), x);
    assert_eq!(nat_mod(&product, &x).unwrap(), 0);
    assert!(word_from_nat(&product).is_err());
}

#[test]
fn remaining_arithmetic_and_cell_encoders() {
    let a = nat_from_str("77").unwrap();
    let b = nat_from_str("13").unwrap();
    assert_eq!(nat_add(&a, &b), 90);
    assert_eq!(nat_div(&a, &b).unwrap(), 5);
    assert_eq!(nat_mod(&a, &b).unwrap(), 12);
    assert_eq!(word_mul(u64::MAX, 2), u64::MAX - 1);
    assert_eq!(f257_to_u64(f257_from_u64(256).unwrap()), 256);
    assert!(f257_from_u64(257).is_err());
    assert_eq!(f257_to_u64(f257_from_nat(&a).unwrap()), 77);
    assert!(f257_from_nat(&Integer::from(257)).is_err());
    assert_eq!(f17_to_u64(f17_from_nat(&Integer::from(16)).unwrap()), 16);
    assert!(f17_from_nat(&Integer::from(17)).is_err());
}

#[test]
fn domains_and_zero_divisors_are_checked() {
    assert!(nat_from_str("-1").is_err());
    assert!(nat_div(&Integer::from(5), &Integer::from(0)).is_err());
    assert!(nat_mod(&Integer::from(5), &Integer::from(0)).is_err());
    assert!(word_div(5, 0).is_err());
    assert!(word_mod(5, 0).is_err());
    assert_eq!(word_add(u64::MAX, 1), 0);
}
