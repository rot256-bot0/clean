//! Native providers. Their foreign-library semantics are an explicit trust boundary.
//! Nat-valued Integer arguments come from the checked input decoder or Nat operations.
use ark_ff::{Fp64, MontBackend, MontConfig, PrimeField};
use rug::Integer;

#[derive(MontConfig)]
#[modulus = "17"]
#[generator = "3"]
pub struct F17Config;
pub type F17 = Fp64<MontBackend<F17Config, 1>>;

#[derive(MontConfig)]
#[modulus = "257"]
#[generator = "3"]
pub struct F257Config;
pub type F257 = Fp64<MontBackend<F257Config, 1>>;

pub fn f17_from_u64(value: u64) -> Result<F17, String> {
    if value < 17 {
        Ok(F17::from(value))
    } else {
        Err("field17 input is not a canonical residue".into())
    }
}

pub fn f17_to_u64(value: F17) -> u64 {
    value.into_bigint().0[0]
}

pub fn f17_from_nat(value: &Integer) -> Result<F17, String> {
    f17_from_u64(word_from_nat(value)?)
}

pub fn f257_from_nat(value: &Integer) -> Result<F257, String> {
    f257_from_u64(word_from_nat(value)?)
}

pub fn f257_from_u64(n: u64) -> Result<F257, String> {
    if n < 257 {
        Ok(F257::from(n))
    } else {
        Err("field257 value is not a canonical residue".into())
    }
}

pub fn f257_to_u64(value: F257) -> u64 {
    value.into_bigint().0[0]
}

pub fn f17_add(a: F17, b: F17) -> F17 {
    a + b
}

pub fn f17_mul(a: F17, b: F17) -> F17 {
    a * b
}

pub fn nat_from_str(value: &str) -> Result<Integer, String> {
    let n = Integer::from_str_radix(value, 10).map_err(|e| e.to_string())?;
    if n < 0 {
        Err("Nat input must be nonnegative".into())
    } else {
        Ok(n)
    }
}

pub fn nat_mul(a: &Integer, b: &Integer) -> Integer {
    Integer::from(a * b)
}

pub fn nat_add(a: &Integer, b: &Integer) -> Integer {
    Integer::from(a + b)
}

pub fn nat_div(a: &Integer, b: &Integer) -> Result<Integer, String> {
    if a < &0 || b <= &0 {
        Err("Nat division requires a nonnegative numerator and positive divisor".into())
    } else {
        Ok(Integer::from(a / b))
    }
}

pub fn nat_mod(a: &Integer, b: &Integer) -> Result<Integer, String> {
    if a < &0 || b <= &0 {
        Err("Nat remainder requires a nonnegative numerator and positive divisor".into())
    } else {
        Ok(Integer::from(a % b))
    }
}

pub fn word_from_nat(value: &Integer) -> Result<u64, String> {
    value
        .to_u64()
        .ok_or_else(|| "Nat value does not fit in u64".into())
}

pub fn word_add(a: u64, b: u64) -> u64 {
    a.wrapping_add(b)
}

pub fn word_mul(a: u64, b: u64) -> u64 {
    a.wrapping_mul(b)
}

pub fn word_div(a: u64, b: u64) -> Result<u64, String> {
    a.checked_div(b).ok_or_else(|| "zero divisor".into())
}

pub fn word_mod(a: u64, b: u64) -> Result<u64, String> {
    a.checked_rem(b).ok_or_else(|| "zero divisor".into())
}
