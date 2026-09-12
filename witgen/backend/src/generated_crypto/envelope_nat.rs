// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct QuadWitness {
    pub square: rug::Integer,
    pub output: rug::Integer,
}

#[derive(Clone, Debug)]
pub struct QuadEnvelope {
    pub trace: QuadWitness,
}

pub fn generate(x: rug::Integer, y: rug::Integer) -> witgen_native::Result<QuadEnvelope> {
    let _wg0: rug::Integer = witgen_native::nat_mul(&x, &x);
    let _wg1: rug::Integer = witgen_native::nat_from_str(
        "21888242871839275222246405745257275088548364400416034343698204186575808495617",
    )?;
    let _wg2: rug::Integer = witgen_native::nat_mod(&_wg0, &_wg1)?;
    let _wg3: rug::Integer = witgen_native::nat_add(&_wg2, &y);
    let _wg4: rug::Integer = witgen_native::nat_from_str(
        "21888242871839275222246405745257275088548364400416034343698204186575808495617",
    )?;
    let _wg5: rug::Integer = witgen_native::nat_mod(&_wg3, &_wg4)?;
    let _wg6: QuadWitness = QuadWitness {
        square: (_wg2).clone(),
        output: (_wg5).clone(),
    };
    let _wg7: QuadEnvelope = QuadEnvelope {
        trace: (_wg6).clone(),
    };
    let _wg8: QuadWitness = (_wg7.trace).clone();
    let _wg9: QuadEnvelope = QuadEnvelope {
        trace: (_wg8).clone(),
    };
    Ok((_wg9).clone())
}

pub fn populate(cells: &mut [witgen_native::Bn254Scalar; 4]) -> witgen_native::Result<()> {
    let result = generate(
        rug::Integer::from(witgen_native::bn254_to_nat(cells[0])),
        rug::Integer::from(witgen_native::bn254_to_nat(cells[1])),
    )?;
    let _cell0 = witgen_native::bn254_from_nat(&result.trace.square)?;
    let _cell1 = witgen_native::bn254_from_nat(&result.trace.output)?;
    cells[2] = _cell0;
    cells[3] = _cell1;
    Ok(())
}
