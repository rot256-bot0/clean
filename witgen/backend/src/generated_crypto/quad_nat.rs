// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct QuadWitness {
    pub square: rug::Integer,
    pub output: rug::Integer,
}

pub fn generate(x: rug::Integer, y: rug::Integer) -> witgen_native::Result<QuadWitness> {
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
    Ok((_wg6).clone())
}

pub fn populate(cells: &mut [witgen_native::Bn254Scalar; 4]) -> witgen_native::Result<()> {
    let result = generate(
        rug::Integer::from(witgen_native::bn254_to_nat(cells[0])),
        rug::Integer::from(witgen_native::bn254_to_nat(cells[1])),
    )?;
    let _cell0 = witgen_native::bn254_from_nat(&result.square)?;
    let _cell1 = witgen_native::bn254_from_nat(&result.output)?;
    cells[2] = _cell0;
    cells[3] = _cell1;
    Ok(())
}
