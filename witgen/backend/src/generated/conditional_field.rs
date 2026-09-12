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
    let _wg7: Vec<Quad> = if enabled {
        let _wg5: Vec<Quad> = {
            let mut _wg1: Vec<Quad> = Vec::with_capacity(xs.len());
            for _wg0 in xs.iter().cloned() {
                _wg1.push({
                    let _wg2: witgen_native::F17 = witgen_native::f17_mul(_wg0, _wg0);
                    let _wg3: witgen_native::F17 = witgen_native::f17_add(_wg2, offset);
                    let _wg4: Quad = Quad {
                        square: _wg2,
                        output: _wg3,
                    };
                    (_wg4).clone()
                });
            }
            _wg1
        };
        (_wg5).clone()
    } else {
        let _wg6: Vec<Quad> = Vec::new();
        (_wg6).clone()
    };
    Ok((_wg7).clone())
}
