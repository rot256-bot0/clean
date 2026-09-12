// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct ModMul {
    pub product: rug::Integer,
    pub quotient: rug::Integer,
    pub remainder: rug::Integer,
}

pub fn generate(
    a: rug::Integer,
    b: rug::Integer,
    modulus: rug::Integer,
) -> witgen_native::Result<ModMul> {
    let _wg0: rug::Integer = witgen_native::nat_mul(&a, &b);
    let _wg1: rug::Integer = witgen_native::nat_div(&_wg0, &modulus)?;
    let _wg2: rug::Integer = witgen_native::nat_mod(&_wg0, &modulus)?;
    let _wg3: ModMul = ModMul {
        product: (_wg0).clone(),
        quotient: (_wg1).clone(),
        remainder: (_wg2).clone(),
    };
    Ok((_wg3).clone())
}
