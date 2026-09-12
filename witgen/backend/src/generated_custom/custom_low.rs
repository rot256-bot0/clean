// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct SplitWitness {
    pub low: rug::Integer,
    pub high: rug::Integer,
}

pub fn generate(x: rug::Integer) -> witgen_native::Result<rug::Integer> {
    let _wg0: rug::Integer = witgen_native::nat_from_str("65536")?;
    let _wg1: rug::Integer = witgen_native::nat_mod(&x, &_wg0)?;
    let _wg2: rug::Integer = witgen_native::nat_div(&x, &_wg0)?;
    let _wg3: SplitWitness = SplitWitness {
        low: (_wg1).clone(),
        high: (_wg2).clone(),
    };
    let _wg4: rug::Integer = (_wg3.low).clone();
    Ok((_wg4).clone())
}
