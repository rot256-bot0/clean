//! BN254 scalar-field provider. All codecs preserve all four 64-bit limbs.
//! Parameters match ark-bn254's Fr (not the distinct BN254 base field Fq):
//! https://docs.rs/ark-bn254/0.4.0/src/ark_bn254/fields/fr.rs.html
use crate::{nat_from_str, Error, Result};
use ark_ff::{BigInt, Fp256, MontBackend, MontConfig, PrimeField};
use rug::{integer::Order, Integer};

pub const BN254_MODULUS: &str =
    "21888242871839275222246405745257275088548364400416034343698204186575808495617";

#[derive(MontConfig)]
#[modulus = "21888242871839275222246405745257275088548364400416034343698204186575808495617"]
#[generator = "5"]
pub struct Bn254ScalarConfig;
pub type Bn254Scalar = Fp256<MontBackend<Bn254ScalarConfig, 4>>;

pub fn bn254_modulus() -> Integer {
    Integer::from_digits(&Bn254Scalar::MODULUS.0, Order::Lsf)
}

pub fn bn254_from_nat(value: &Integer) -> Result<Bn254Scalar> {
    if value < &0 {
        return Err(Error::NegativeNatural);
    }
    if value >= &bn254_modulus() {
        return Err(Error::NonCanonicalField { field: "bn254" });
    }
    let digits = value.to_digits::<u64>(Order::Lsf);
    if digits.len() > 4 {
        return Err(Error::NonCanonicalField { field: "bn254" });
    }
    let limbs = std::array::from_fn(|i| digits.get(i).copied().unwrap_or(0));
    Bn254Scalar::from_bigint(BigInt(limbs)).ok_or(Error::NonCanonicalField { field: "bn254" })
}

pub fn bn254_from_str(value: &str) -> Result<Bn254Scalar> {
    bn254_from_nat(&nat_from_str(value)?)
}

pub fn bn254_to_nat(value: Bn254Scalar) -> Integer {
    Integer::from_digits(&value.into_bigint().0, Order::Lsf)
}

pub fn bn254_to_decimal(value: Bn254Scalar) -> String {
    bn254_to_nat(value).to_string()
}

pub fn bn254_add(a: Bn254Scalar, b: Bn254Scalar) -> Bn254Scalar {
    a + b
}
pub fn bn254_mul(a: Bn254Scalar, b: Bn254Scalar) -> Bn254Scalar {
    a * b
}
