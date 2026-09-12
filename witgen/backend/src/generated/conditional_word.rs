// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct Quad {
    pub square: u64,
    pub output: u64,
}

pub fn generate(enabled: bool, xs: Vec<u64>, offset: u64) -> Result<Vec<Quad>, String> {
    let _wg11: Vec<Quad> = if enabled {
        let _wg9: Vec<Quad> = {
            let mut _wg1: Vec<Quad> = Vec::with_capacity(xs.len());
            for _wg0 in xs.iter().cloned() {
                _wg1.push({
                    let _wg2: u64 = witgen_native::word_mul(_wg0, _wg0);
                    let _wg3: u64 = 17_u64;
                    let _wg4: u64 = witgen_native::word_mod(_wg2, _wg3)?;
                    let _wg5: u64 = witgen_native::word_add(_wg4, offset);
                    let _wg6: u64 = 17_u64;
                    let _wg7: u64 = witgen_native::word_mod(_wg5, _wg6)?;
                    let _wg8: Quad = Quad {
                        square: _wg4,
                        output: _wg7,
                    };
                    (_wg8).clone()
                });
            }
            _wg1
        };
        (_wg9).clone()
    } else {
        let _wg10: Vec<Quad> = Vec::new();
        (_wg10).clone()
    };
    Ok((_wg11).clone())
}
