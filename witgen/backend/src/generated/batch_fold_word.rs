// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct Quad {
    pub square: u64,
    pub output: u64,
}

pub fn generate(enabled: bool, xs: Vec<u64>, c: u64) -> witgen_native::Result<Vec<Quad>> {
    let _wg0: Vec<Quad> = Vec::new();
    let _wg15: Vec<Quad> = {
        let mut _wg2: Vec<Quad> = (_wg0).clone();
        for _wg1 in xs.iter().cloned() {
            _wg2 = {
                let _wg12: Quad = if enabled {
                    let _wg3: u64 = witgen_native::word_mul(_wg1, _wg1);
                    let _wg4: u64 = 17_u64;
                    let _wg5: u64 = witgen_native::word_mod(_wg3, _wg4)?;
                    let _wg6: u64 = witgen_native::word_add(_wg5, c);
                    let _wg7: u64 = 17_u64;
                    let _wg8: u64 = witgen_native::word_mod(_wg6, _wg7)?;
                    let _wg9: Quad = Quad {
                        square: _wg5,
                        output: _wg8,
                    };
                    (_wg9).clone()
                } else {
                    let _wg10: u64 = 0_u64;
                    let _wg11: Quad = Quad {
                        square: _wg10,
                        output: _wg10,
                    };
                    (_wg11).clone()
                };
                let _wg14: Vec<Quad> = {
                    let mut _wg13 = (_wg2).clone();
                    _wg13.push((_wg12).clone());
                    _wg13
                };
                (_wg14).clone()
            };
        }
        _wg2
    };
    Ok((_wg15).clone())
}

pub fn populate(cells: &mut [witgen_native::F17; 11]) -> witgen_native::Result<()> {
    let _bit0 = witgen_native::f17_to_u64(cells[0]);
    if _bit0 > 1 {
        return Err(witgen_native::Error::NonBooleanCell { slot: 0 });
    }
    let result = generate(
        _bit0 == 1,
        vec![
            witgen_native::f17_to_u64(cells[1]),
            witgen_native::f17_to_u64(cells[2]),
            witgen_native::f17_to_u64(cells[3]),
        ],
        witgen_native::f17_to_u64(cells[4]),
    )?;
    if result.len() != 3 {
        return Err(witgen_native::Error::WitnessLength {
            expected: 3,
            actual: result.len(),
        });
    }
    let _cell0 = witgen_native::f17_from_u64(result[0].square)?;
    let _cell1 = witgen_native::f17_from_u64(result[0].output)?;
    let _cell2 = witgen_native::f17_from_u64(result[1].square)?;
    let _cell3 = witgen_native::f17_from_u64(result[1].output)?;
    let _cell4 = witgen_native::f17_from_u64(result[2].square)?;
    let _cell5 = witgen_native::f17_from_u64(result[2].output)?;
    cells[5] = _cell0;
    cells[6] = _cell1;
    cells[7] = _cell2;
    cells[8] = _cell3;
    cells[9] = _cell4;
    cells[10] = _cell5;
    Ok(())
}
