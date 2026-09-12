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
) -> witgen_native::Result<Vec<Quad>> {
    let _wg8: Vec<Quad> = {
        let mut _wg1: Vec<Quad> = Vec::with_capacity(xs.len());
        for _wg0 in xs.iter().cloned() {
            _wg1.push({
                let _wg7: Quad = if enabled {
                    let _wg2: witgen_native::F17 = witgen_native::f17_mul(_wg0, _wg0);
                    let _wg3: witgen_native::F17 = witgen_native::f17_add(_wg2, c);
                    let _wg4: Quad = Quad {
                        square: _wg2,
                        output: _wg3,
                    };
                    (_wg4).clone()
                } else {
                    let _wg5: witgen_native::F17 = witgen_native::f17_from_u64(0_u64)?;
                    let _wg6: Quad = Quad {
                        square: _wg5,
                        output: _wg5,
                    };
                    (_wg6).clone()
                };
                (_wg7).clone()
            });
        }
        _wg1
    };
    Ok((_wg8).clone())
}

pub fn populate(cells: &mut [witgen_native::F17; 11]) -> witgen_native::Result<()> {
    let _bit0 = witgen_native::f17_to_u64(cells[0]);
    if _bit0 > 1 {
        return Err(witgen_native::Error::NonBooleanCell { slot: 0 });
    }
    let result = generate(_bit0 == 1, vec![cells[1], cells[2], cells[3]], cells[4])?;
    if result.len() != 3 {
        return Err(witgen_native::Error::WitnessLength {
            expected: 3,
            actual: result.len(),
        });
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
