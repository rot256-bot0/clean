// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct Quad {
    pub square: u64,
    pub output: u64,
}

pub fn generate(x: u64, y: u64) -> Result<Quad, String> {
    let _wg0: u64 = witgen_native::word_mul(x, x);
    let _wg1: u64 = 17_u64;
    let _wg2: u64 = witgen_native::word_mod(_wg0, _wg1)?;
    let _wg3: u64 = witgen_native::word_add(_wg2, y);
    let _wg4: u64 = 17_u64;
    let _wg5: u64 = witgen_native::word_mod(_wg3, _wg4)?;
    let _wg6: Quad = Quad {
        square: _wg2,
        output: _wg5,
    };
    Ok((_wg6).clone())
}

pub fn populate(cells: &mut [witgen_native::F17; 4]) -> Result<(), String> {
    let result = generate(
        witgen_native::f17_to_u64(cells[0]),
        witgen_native::f17_to_u64(cells[1]),
    )?;
    let _cell0 = witgen_native::f17_from_u64(result.square)?;
    let _cell1 = witgen_native::f17_from_u64(result.output)?;
    cells[2] = _cell0;
    cells[3] = _cell1;
    Ok(())
}
