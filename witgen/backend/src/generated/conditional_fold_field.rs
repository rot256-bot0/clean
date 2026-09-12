// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct Quad {
    pub square: witgen_native::F17,
    pub output: witgen_native::F17,
}

pub fn generate(
    enabled: bool,
    xs: Vec<witgen_native::F17>,
    offset: witgen_native::F17,
) -> witgen_native::Result<Vec<Quad>> {
    let _wg10: Vec<Quad> = if enabled {
        let _wg0: Vec<Quad> = Vec::new();
        let _wg8: Vec<Quad> = {
            let mut _wg2: Vec<Quad> = (_wg0).clone();
            for _wg1 in xs.iter().cloned() {
                _wg2 = {
                    let _wg3: witgen_native::F17 = witgen_native::f17_mul(_wg1, _wg1);
                    let _wg4: witgen_native::F17 = witgen_native::f17_add(_wg3, offset);
                    let _wg5: Quad = Quad {
                        square: _wg3,
                        output: _wg4,
                    };
                    let _wg7: Vec<Quad> = {
                        let mut _wg6 = (_wg2).clone();
                        _wg6.push((_wg5).clone());
                        _wg6
                    };
                    (_wg7).clone()
                };
            }
            _wg2
        };
        (_wg8).clone()
    } else {
        let _wg9: Vec<Quad> = Vec::new();
        (_wg9).clone()
    };
    Ok((_wg10).clone())
}
