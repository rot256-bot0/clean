// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct SplitWitness {
    pub low: rug::Integer,
    pub high: rug::Integer,
}

pub fn generate(x: rug::Integer) -> witgen_native::Result<SplitWitness> {
    let _wg0: rug::Integer = witgen_native::nat_from_str("65536")?;
    let _wg1: rug::Integer = witgen_native::nat_mod(&x, &_wg0)?;
    let _wg2: rug::Integer = witgen_native::nat_div(&x, &_wg0)?;
    let _wg3: SplitWitness = SplitWitness {
        low: (_wg1).clone(),
        high: (_wg2).clone(),
    };
    Ok((_wg3).clone())
}
