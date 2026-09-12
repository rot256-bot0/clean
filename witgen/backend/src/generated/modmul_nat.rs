// Generated from typed witness IR. Do not hand-edit.

#[derive(Clone, Debug)]
pub struct ModMul {
    pub product: rug::Integer,
    pub quotient: rug::Integer,
    pub remainder: rug::Integer,
}

pub fn generate(a: rug::Integer, b: rug::Integer, modulus: rug::Integer) -> Result<ModMul, String> {
    let _wg0: rug::Integer = witgen_native::nat_mul(&a, &b);
    let _wg1: rug::Integer = witgen_native::nat_div(&_wg0, &modulus)?;
    let _wg2: rug::Integer = witgen_native::nat_mod(&_wg0, &modulus)?;
    let _wg3: ModMul = ModMul {
        product: (_wg0).clone(),
        quotient: (_wg1).clone(),
        remainder: (_wg2).clone(),
    };
    Ok((_wg3).clone())
}

pub fn populate(cells: &mut [witgen_native::F257; 6]) -> Result<(), String> {
    let _raw0 = witgen_native::f257_to_u64(cells[0]);
    let _raw1 = witgen_native::f257_to_u64(cells[1]);
    let _raw2 = witgen_native::f257_to_u64(cells[2]);
    if _raw2 == 0 || _raw2 > 16 || _raw0 >= _raw2 || _raw1 >= _raw2 {
        return Err("modmul circuit input assumptions failed".into());
    }
    let result = generate(
        rug::Integer::from(witgen_native::f257_to_u64(cells[0])),
        rug::Integer::from(witgen_native::f257_to_u64(cells[1])),
        rug::Integer::from(witgen_native::f257_to_u64(cells[2])),
    )?;
    let _cell0 = witgen_native::f257_from_nat(&result.product)?;
    let _cell1 = witgen_native::f257_from_nat(&result.quotient)?;
    let _cell2 = witgen_native::f257_from_nat(&result.remainder)?;
    cells[3] = _cell0;
    cells[4] = _cell1;
    cells[5] = _cell2;
    Ok(())
}
