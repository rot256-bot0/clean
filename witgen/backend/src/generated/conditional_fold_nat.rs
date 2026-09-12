// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct Quad {
    pub square: rug::Integer,
    pub output: rug::Integer,
}

pub fn generate(
    enabled: bool,
    xs: Vec<rug::Integer>,
    offset: rug::Integer,
) -> Result<Vec<Quad>, String> {
    let _wg14: Vec<Quad> = if enabled {
        let _wg0: Vec<Quad> = Vec::new();
        let _wg12: Vec<Quad> = {
            let mut _wg2: Vec<Quad> = (_wg0).clone();
            for _wg1 in xs.iter().cloned() {
                _wg2 = {
                    let _wg3: rug::Integer = witgen_native::nat_mul(&_wg1, &_wg1);
                    let _wg4: rug::Integer = witgen_native::nat_from_str("17")?;
                    let _wg5: rug::Integer = witgen_native::nat_mod(&_wg3, &_wg4)?;
                    let _wg6: rug::Integer = witgen_native::nat_add(&_wg5, &offset);
                    let _wg7: rug::Integer = witgen_native::nat_from_str("17")?;
                    let _wg8: rug::Integer = witgen_native::nat_mod(&_wg6, &_wg7)?;
                    let _wg9: Quad = Quad {
                        square: (_wg5).clone(),
                        output: (_wg8).clone(),
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
