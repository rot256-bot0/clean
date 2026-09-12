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
    let _wg11: Vec<Quad> = if enabled {
        let _wg9: Vec<Quad> = {
            let mut _wg1: Vec<Quad> = Vec::with_capacity(xs.len());
            for _wg0 in xs.iter().cloned() {
                _wg1.push({
                    let _wg2: rug::Integer = witgen_native::nat_mul(&_wg0, &_wg0);
                    let _wg3: rug::Integer = witgen_native::nat_from_str("17")?;
                    let _wg4: rug::Integer = witgen_native::nat_mod(&_wg2, &_wg3)?;
                    let _wg5: rug::Integer = witgen_native::nat_add(&_wg4, &offset);
                    let _wg6: rug::Integer = witgen_native::nat_from_str("17")?;
                    let _wg7: rug::Integer = witgen_native::nat_mod(&_wg5, &_wg6)?;
                    let _wg8: Quad = Quad {
                        square: (_wg4).clone(),
                        output: (_wg7).clone(),
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
