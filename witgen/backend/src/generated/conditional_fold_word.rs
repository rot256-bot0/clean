// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct Quad {
    pub square: u64,
    pub output: u64,
}

pub fn generate(enabled: bool, xs: Vec<u64>, offset: u64) -> Result<Vec<Quad>, String> {
    let _wg14: Vec<Quad> = if enabled {
        let _wg0: Vec<Quad> = Vec::new();
        let _wg12: Vec<Quad> = {
            let mut _wg2: Vec<Quad> = (_wg0).clone();
            for _wg1 in xs.iter().cloned() {
                _wg2 = {
                    let _wg3: u64 = witgen_native::word_mul(_wg1, _wg1);
                    let _wg4: u64 = 17_u64;
                    let _wg5: u64 = witgen_native::word_mod(_wg3, _wg4)?;
                    let _wg6: u64 = witgen_native::word_add(_wg5, offset);
                    let _wg7: u64 = 17_u64;
                    let _wg8: u64 = witgen_native::word_mod(_wg6, _wg7)?;
                    let _wg9: Quad = Quad {
                        square: _wg5,
                        output: _wg8,
                    };
                    let _wg11: Vec<Quad> = {
                        let mut _wg10 = (_wg2).clone();
                        _wg10.push((_wg9).clone());
                        _wg10
                    };
                    (_wg11).clone()
                };
            }
            _wg2
        };
        (_wg12).clone()
    } else {
        let _wg13: Vec<Quad> = Vec::new();
        (_wg13).clone()
    };
    Ok((_wg14).clone())
}
