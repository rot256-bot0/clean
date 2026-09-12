// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct Quad {
    pub square: witgen_native::F17,
    pub output: witgen_native::F17,
}

pub fn generate(x: witgen_native::F17, y: witgen_native::F17) -> Result<Quad, String> {
    let _wg0: witgen_native::F17 = witgen_native::f17_mul(x, x);
    let _wg1: witgen_native::F17 = witgen_native::f17_add(_wg0, y);
    let _wg2: Quad = Quad {
        square: _wg0,
        output: _wg1,
    };
    Ok((_wg2).clone())
}

pub fn populate(cells: &mut [witgen_native::F17; 4]) -> Result<(), String> {
    let result = generate(cells[0], cells[1])?;
    let _cell0 = result.square;
    let _cell1 = result.output;
    cells[2] = _cell0;
    cells[3] = _cell1;
    Ok(())
}
