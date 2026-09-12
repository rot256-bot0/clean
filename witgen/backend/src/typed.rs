//! Primitive and codec seam for typed method-library exports.
//! U64 arithmetic helpers use only word operations; Integer conversions are ABI-only.
use crate::{Error, Result};
use ark_ec::{AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{AdditiveGroup, BigInt, BigInteger, Field, PrimeField};
use rug::{integer::Order, Integer};
use serde_json::Value;

pub type Word4 = [u64; 4];
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WordField<const ID: u8>(pub Word4);
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NatField<const ID: u8>(pub Integer);
pub type SecpBase = ark_secp256k1::Fq;
pub type SecpScalar = ark_secp256k1::Fr;
pub type SecpPoint = ark_secp256k1::Projective;

pub const FIELD_MODULI: [&str; 3] = [
    crate::BN254_MODULUS,
    "115792089237316195423570985008687907853269984665640564039457584007908834671663",
    "115792089237316195423570985008687907852837564279074904382605163141518161494337",
];
pub const FIELD_NAMES: [&str; 3] = ["bn254", "secp256k1.Base", "secp256k1.Scalar"];

pub fn field_modulus(id: u8) -> Result<Integer> {
    crate::nat_from_str(
        FIELD_MODULI
            .get(id as usize)
            .ok_or(Error::UnknownField(id))?,
    )
}

pub fn adc(a: u64, b: u64, carry: bool) -> (u64, bool) {
    let (low, c0) = a.overflowing_add(b);
    let (word, c1) = low.overflowing_add(u64::from(carry));
    (word, c0 || c1)
}
pub fn sbb(a: u64, b: u64, borrow: bool) -> (u64, bool) {
    let (low, b0) = a.overflowing_sub(b);
    let (word, b1) = low.overflowing_sub(u64::from(borrow));
    (word, b0 || b1)
}
pub fn bit_at(a: Word4, index: usize) -> bool {
    index < 256 && ((a[index / 64] >> (index % 64)) & 1) != 0
}

pub fn parse_nat(value: &Value) -> Result<Integer> {
    let text = value.as_str().ok_or(Error::InvalidInputType {
        expected: "decimal string",
    })?;
    crate::nat_from_str(text)
}
pub fn parse_u64(value: &Value) -> Result<u64> {
    crate::word_from_nat(&parse_nat(value)?)
}
pub fn parse_word4(value: &Value) -> Result<Word4> {
    let values = value.as_array().ok_or(Error::InvalidInputType {
        expected: "four-word array",
    })?;
    if values.len() != 4 {
        return Err(Error::InputLength {
            expected: 4,
            actual: values.len(),
        });
    }
    Ok([
        parse_u64(&values[0])?,
        parse_u64(&values[1])?,
        parse_u64(&values[2])?,
        parse_u64(&values[3])?,
    ])
}
fn canonical(value: Integer, id: u8) -> Result<Integer> {
    let modulus = field_modulus(id)?;
    if value < 0 {
        return Err(Error::NegativeNatural);
    }
    if value >= modulus {
        return Err(Error::NonCanonicalField {
            field: FIELD_NAMES[id as usize],
        });
    }
    Ok(value)
}
pub fn parse_nat_field<const ID: u8>(value: &Value) -> Result<NatField<ID>> {
    Ok(NatField(canonical(parse_nat(value)?, ID)?))
}
pub fn parse_word_field<const ID: u8>(value: &Value) -> Result<WordField<ID>> {
    let value = canonical(parse_nat(value)?, ID)?;
    let digits = value.to_digits::<u64>(Order::Lsf);
    // Canonical residues for this registered family are all below 2^256.
    if digits.len() > 4 {
        return Err(Error::WordOverflow);
    }
    Ok(WordField(std::array::from_fn(|i| {
        digits.get(i).copied().unwrap_or(0)
    })))
}
pub fn word_field_decimal<const ID: u8>(value: WordField<ID>) -> String {
    Integer::from_digits(&value.0, Order::Lsf).to_string()
}
pub fn word4_json(value: Word4) -> Value {
    serde_json::json!(value.map(|word| word.to_string()))
}

fn field_from_nat<F: PrimeField<BigInt = BigInt<4>>>(value: &Integer, id: u8) -> Result<F> {
    let value = canonical(value.clone(), id)?;
    let digits = value.to_digits::<u64>(Order::Lsf);
    if digits.len() > 4 {
        return Err(Error::NonCanonicalField {
            field: FIELD_NAMES[id as usize],
        });
    }
    F::from_bigint(BigInt(std::array::from_fn(|i| {
        digits.get(i).copied().unwrap_or(0)
    })))
    .ok_or(Error::NonCanonicalField {
        field: FIELD_NAMES[id as usize],
    })
}
pub fn secp_base_from_nat(value: &Integer) -> Result<SecpBase> {
    field_from_nat(value, 1)
}
pub fn secp_scalar_from_nat(value: &Integer) -> Result<SecpScalar> {
    field_from_nat(value, 2)
}
pub fn secp_base_from_str(value: &str) -> Result<SecpBase> {
    secp_base_from_nat(&crate::nat_from_str(value)?)
}
pub fn secp_scalar_from_str(value: &str) -> Result<SecpScalar> {
    secp_scalar_from_nat(&crate::nat_from_str(value)?)
}
pub fn secp_base_to_nat(value: SecpBase) -> Integer {
    Integer::from_digits(&value.into_bigint().0, Order::Lsf)
}
pub fn secp_scalar_to_nat(value: SecpScalar) -> Integer {
    Integer::from_digits(&value.into_bigint().0, Order::Lsf)
}
pub fn secp_base_add(a: SecpBase, b: SecpBase) -> SecpBase {
    a + b
}
pub fn secp_base_mul(a: SecpBase, b: SecpBase) -> SecpBase {
    a * b
}
pub fn secp_base_square(a: SecpBase) -> SecpBase {
    a.square()
}
pub fn secp_scalar_add(a: SecpScalar, b: SecpScalar) -> SecpScalar {
    a + b
}
pub fn secp_scalar_mul(a: SecpScalar, b: SecpScalar) -> SecpScalar {
    a * b
}
pub fn secp_scalar_square(a: SecpScalar) -> SecpScalar {
    a.square()
}
pub fn bn254_square(a: crate::Bn254Scalar) -> crate::Bn254Scalar {
    a.square()
}

pub fn point_generator() -> SecpPoint {
    SecpPoint::generator()
}
pub fn point_identity() -> SecpPoint {
    SecpPoint::ZERO
}
pub fn point_add(a: SecpPoint, b: SecpPoint) -> SecpPoint {
    a + b
}
pub fn point_scale(scalar: SecpScalar, point: SecpPoint) -> SecpPoint {
    point * scalar
}
pub fn point_inv(point: SecpPoint) -> SecpPoint {
    -point
}
pub fn to_affine(point: SecpPoint) -> Option<(SecpBase, SecpBase)> {
    point.into_affine().xy()
}
pub fn from_affine(pair: (SecpBase, SecpBase)) -> Option<SecpPoint> {
    // Arkworks uses a distinguished affine encoding for infinity. A pair supplied
    // as affine coordinates must satisfy the curve equation, never become that sentinel.
    if pair.1.square() != pair.0.square() * pair.0 + SecpBase::from(7u64) {
        return None;
    }
    let point = ark_secp256k1::Affine::new_unchecked(pair.0, pair.1);
    if point.is_on_curve() && point.is_in_correct_subgroup_assuming_on_curve() {
        Some(point.into_group())
    } else {
        None
    }
}
pub fn point_x(point: SecpPoint) -> SecpBase {
    to_affine(point)
        .map(|pair| pair.0)
        .unwrap_or(SecpBase::ZERO)
}
pub fn point_hex(point: SecpPoint) -> String {
    match to_affine(point) {
        None => "00".to_owned(),
        Some((x, y)) => {
            let mut bytes = vec![if y.into_bigint().is_odd() { 3u8 } else { 2u8 }];
            bytes.extend(x.into_bigint().to_bytes_be());
            bytes.iter().map(|byte| format!("{byte:02x}")).collect()
        }
    }
}
pub fn parse_point(value: &Value) -> Result<SecpPoint> {
    let text = value.as_str().ok_or(Error::InvalidInputType {
        expected: "SEC1 hex string",
    })?;
    if ![2, 66, 130].contains(&text.len()) {
        return Err(Error::InvalidPointEncoding);
    }
    fn digit(x: u8) -> Option<u8> {
        match x {
            b'0'..=b'9' => Some(x - b'0'),
            b'a'..=b'f' => Some(x - b'a' + 10),
            b'A'..=b'F' => Some(x - b'A' + 10),
            _ => None,
        }
    }
    let bytes = text
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            Ok((digit(pair[0]).ok_or(Error::InvalidPointEncoding)? << 4)
                | digit(pair[1]).ok_or(Error::InvalidPointEncoding)?)
        })
        .collect::<Result<Vec<u8>>>()?;
    if bytes == [0] {
        return Ok(point_identity());
    }
    let field = |bytes: &[u8]| {
        secp_base_from_nat(&Integer::from_digits(bytes, Order::MsfBe))
            .map_err(|_| Error::InvalidPointEncoding)
    };
    let pair = match (bytes[0], bytes.len()) {
        (4, 65) => (field(&bytes[1..33])?, field(&bytes[33..65])?),
        (prefix @ (2 | 3), 33) => {
            let x = field(&bytes[1..33])?;
            let mut y = (x.square() * x + SecpBase::from(7u64))
                .sqrt()
                .ok_or(Error::InvalidPointEncoding)?;
            if y.into_bigint().is_odd() != (prefix == 3) {
                y = -y;
            }
            if y.into_bigint().is_odd() != (prefix == 3) {
                return Err(Error::InvalidPointEncoding);
            }
            (x, y)
        }
        _ => return Err(Error::InvalidPointEncoding),
    };
    from_affine(pair).ok_or(Error::InvalidPointEncoding)
}
