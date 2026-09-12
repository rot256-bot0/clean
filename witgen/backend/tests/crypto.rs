use ark_ff::PrimeField;
use rug::Integer;
use witgen_native::*;

#[test]
fn bn254_uses_the_scalar_field_and_preserves_all_limbs() {
    let modulus = nat_from_str(BN254_MODULUS).unwrap();
    assert_eq!(Bn254Scalar::MODULUS.to_string(), BN254_MODULUS);
    assert_eq!(modulus.significant_bits(), 254);
    for n in [
        Integer::from(0),
        Integer::from(1),
        (Integer::from(1) << 200) + 123,
        modulus.clone() - 1,
    ] {
        let value = bn254_from_nat(&n).unwrap();
        assert_eq!(bn254_to_nat(value), n);
        assert_eq!(bn254_to_decimal(value), n.to_string());
    }
}

#[test]
fn full_width_arithmetic_matches_independent_gmp_reduction() {
    let p = nat_from_str(BN254_MODULUS).unwrap();
    let x = p.clone() - 2;
    let y = (Integer::from(1) << 200) + 17;
    let a = bn254_from_nat(&x).unwrap();
    let b = bn254_from_nat(&y).unwrap();
    let sum = nat_mod(&nat_add(&x, &y), &p).unwrap();
    let product = nat_mod(&nat_mul(&x, &y), &p).unwrap();
    assert_eq!(bn254_to_nat(bn254_add(a, b)), sum);
    assert_eq!(bn254_to_nat(bn254_mul(a, b)), product);
    assert_eq!(bn254_to_nat(bn254_mul(a, a)), 4);
    let last = bn254_from_nat(&(p.clone() - 1)).unwrap();
    assert_eq!(bn254_to_nat(bn254_add(last, Bn254Scalar::from(1))), 0);
}

#[test]
fn noncanonical_and_negative_inputs_are_not_silently_reduced() {
    let p = nat_from_str(BN254_MODULUS).unwrap();
    assert!(matches!(
        bn254_from_nat(&p),
        Err(Error::NonCanonicalField { field: "bn254" })
    ));
    assert!(matches!(
        bn254_from_nat(&(p + 1)),
        Err(Error::NonCanonicalField { .. })
    ));
    assert!(matches!(
        bn254_from_nat(&Integer::from(-1)),
        Err(Error::NegativeNatural)
    ));
    assert!(matches!(
        bn254_from_str("not a number"),
        Err(Error::ParseInteger(_))
    ));
}
