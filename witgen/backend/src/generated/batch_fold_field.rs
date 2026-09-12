// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct Quad {
    pub square: witgen_native::F17,
    pub output: witgen_native::F17,
}

pub fn generate(
    enabled: bool,
    xs: Vec<witgen_native::F17>,
    c: witgen_native::F17,
) -> Result<Vec<Quad>, String> {
    let _wg0: Vec<Quad> = Vec::new();
    let _wg11: Vec<Quad> = {
        let mut _wg2: Vec<Quad> = (_wg0).clone();
        for _wg1 in xs.iter().cloned() {
            _wg2 = {
                let _wg8: Quad = if enabled {
                    let _wg3: witgen_native::F17 = witgen_native::f17_mul(_wg1, _wg1);
                    let _wg4: witgen_native::F17 = witgen_native::f17_add(_wg3, c);
                    let _wg5: Quad = Quad {
                        square: _wg3,
                        output: _wg4,
                    };
                    (_wg5).clone()
                } else {
                    let _wg6: witgen_native::F17 = witgen_native::f17_from_u64(0_u64)?;
                    let _wg7: Quad = Quad {
                        square: _wg6,
                        output: _wg6,
                    };
                    (_wg7).clone()
                };
                let _wg10: Vec<Quad> = {
                    let mut _wg9 = (_wg2).clone();
                    _wg9.push((_wg8).clone());
                    _wg9
                };
                (_wg10).clone()
            };
        }
        _wg2
    };
    Ok((_wg11).clone())
}

pub fn populate(cells: &mut [witgen_native::F17; 11]) -> Result<(), String> {
    let _bit0 = witgen_native::f17_to_u64(cells[0]);
    if _bit0 > 1 {
        return Err("non-Boolean input cell".into());
    }
    let result = generate(_bit0 == 1, vec![cells[1], cells[2], cells[3]], cells[4])?;
    if result.len() != 3 {
        return Err("witness result length mismatch".into());
    }
    let _cell0 = result[0].square;
    let _cell1 = result[0].output;
    let _cell2 = result[1].square;
    let _cell3 = result[1].output;
    let _cell4 = result[2].square;
    let _cell5 = result[2].output;
    cells[5] = _cell0;
    cells[6] = _cell1;
    cells[7] = _cell2;
    cells[8] = _cell3;
    cells[9] = _cell4;
    cells[10] = _cell5;
    Ok(())
}
