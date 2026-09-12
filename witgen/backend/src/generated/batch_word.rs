// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct Quad {
    pub square: u64,
    pub output: u64,
}

pub fn generate(enabled: bool, xs: Vec<u64>, c: u64) -> Result<Vec<Quad>, String> {
    let _wg12: Vec<Quad> = {
        let mut _wg1: Vec<Quad> = Vec::with_capacity(xs.len());
        for _wg0 in xs.iter().cloned() {
            _wg1.push({
                let _wg11: Quad = if enabled {
                    let _wg2: u64 = witgen_native::word_mul(_wg0, _wg0);
                    let _wg3: u64 = 17_u64;
                    let _wg4: u64 = witgen_native::word_mod(_wg2, _wg3)?;
                    let _wg5: u64 = witgen_native::word_add(_wg4, c);
                    let _wg6: u64 = 17_u64;
                    let _wg7: u64 = witgen_native::word_mod(_wg5, _wg6)?;
                    let _wg8: Quad = Quad {
                        square: _wg4,
                        output: _wg7,
                    };
                    (_wg8).clone()
                } else {
                    let _wg9: u64 = 0_u64;
                    let _wg10: Quad = Quad {
                        square: _wg9,
                        output: _wg9,
                    };
                    (_wg10).clone()
                };
                (_wg11).clone()
            });
        }
        _wg1
    };
    Ok((_wg12).clone())
}

pub fn populate(cells: &mut [witgen_native::F17; 11]) -> Result<(), String> {
    let _bit0 = witgen_native::f17_to_u64(cells[0]);
    if _bit0 > 1 {
        return Err("non-Boolean input cell".into());
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
        return Err("witness result length mismatch".into());
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
