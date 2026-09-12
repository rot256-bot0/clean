// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct QuadWitness {
    pub square: witgen_native::Bn254Scalar,
    pub output: witgen_native::Bn254Scalar,
}

#[derive(Clone, Debug)]
pub struct QuadEnvelope {
    pub trace: QuadWitness,
}

pub fn generate(
    x: witgen_native::Bn254Scalar,
    y: witgen_native::Bn254Scalar,
) -> witgen_native::Result<QuadEnvelope> {
    let _wg0: witgen_native::Bn254Scalar = witgen_native::bn254_mul(x, x);
    let _wg1: witgen_native::Bn254Scalar = witgen_native::bn254_add(_wg0, y);
    let _wg2: QuadWitness = QuadWitness {
        square: _wg0,
        output: _wg1,
    };
    let _wg3: QuadEnvelope = QuadEnvelope {
        trace: (_wg2).clone(),
    };
    let _wg4: QuadWitness = (_wg3.trace).clone();
    let _wg5: QuadEnvelope = QuadEnvelope {
        trace: (_wg4).clone(),
    };
    Ok((_wg5).clone())
}

pub fn populate(cells: &mut [witgen_native::Bn254Scalar; 4]) -> witgen_native::Result<()> {
    let result = generate(cells[0], cells[1])?;
    let _cell0 = result.trace.square;
    let _cell1 = result.trace.output;
    cells[2] = _cell0;
    cells[3] = _cell1;
    Ok(())
}
