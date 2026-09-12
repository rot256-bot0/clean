use witgen_native::typed;

// method 0: "u64.field.add"
fn method_0(
    a0: typed::Word4,
    a1: typed::Word4,
    a2: typed::Word4,
) -> witgen_native::Result<typed::Word4> {
    let v0: bool = false;
    let v1: u64 = a0.clone()[0];
    let v2: u64 = a0.clone()[1];
    let v3: u64 = a0.clone()[2];
    let v4: u64 = a0.clone()[3];
    let v5: u64 = a1.clone()[0];
    let v6: u64 = a1.clone()[1];
    let v7: u64 = a1.clone()[2];
    let v8: u64 = a1.clone()[3];
    let v9: u64 = a2.clone()[0];
    let v10: u64 = a2.clone()[1];
    let v11: u64 = a2.clone()[2];
    let v12: u64 = a2.clone()[3];
    let v13: u64 = typed::adc(v5.clone(), v9.clone(), v0.clone()).0;
    let v14: bool = typed::adc(v5.clone(), v9.clone(), v0.clone()).1;
    let v15: u64 = typed::adc(v6.clone(), v10.clone(), v14.clone()).0;
    let v16: bool = typed::adc(v6.clone(), v10.clone(), v14.clone()).1;
    let v17: u64 = typed::adc(v7.clone(), v11.clone(), v16.clone()).0;
    let v18: bool = typed::adc(v7.clone(), v11.clone(), v16.clone()).1;
    let v19: u64 = typed::adc(v8.clone(), v12.clone(), v18.clone()).0;
    let v20: bool = typed::adc(v8.clone(), v12.clone(), v18.clone()).1;
    let v21: u64 = typed::sbb(v13.clone(), v1.clone(), v0.clone()).0;
    let v22: bool = typed::sbb(v13.clone(), v1.clone(), v0.clone()).1;
    let v23: u64 = typed::sbb(v15.clone(), v2.clone(), v22.clone()).0;
    let v24: bool = typed::sbb(v15.clone(), v2.clone(), v22.clone()).1;
    let v25: u64 = typed::sbb(v17.clone(), v3.clone(), v24.clone()).0;
    let v26: bool = typed::sbb(v17.clone(), v3.clone(), v24.clone()).1;
    let v27: u64 = typed::sbb(v19.clone(), v4.clone(), v26.clone()).0;
    let v28: bool = typed::sbb(v19.clone(), v4.clone(), v26.clone()).1;
    let v29: typed::Word4 = [v13.clone(), v15.clone(), v17.clone(), v19.clone()];
    let v30: typed::Word4 = [v21.clone(), v23.clone(), v25.clone(), v27.clone()];
    let v31: bool = !v28.clone();
    let v32: bool = v20.clone() || v31.clone();
    let v33: typed::Word4 = if v32.clone() {
        v30.clone()
    } else {
        v29.clone()
    };
    Ok(v33.clone())
}

// method 1: "u64.field.mul"
fn method_1(
    a0: typed::Word4,
    a1: typed::Word4,
    a2: typed::Word4,
) -> witgen_native::Result<typed::Word4> {
    let v34: typed::Word4 = [0u64, 0u64, 0u64, 0u64];
    let v41: typed::Word4 = {
        let mut acc36: typed::Word4 = v34.clone();
        for index35 in (0..256usize).rev() {
            acc36 = {
                let v37: typed::Word4 = method_0(a0.clone(), acc36.clone(), acc36.clone())?;
                let v38: typed::Word4 = method_0(a0.clone(), v37.clone(), a2.clone())?;
                let v39: bool = typed::bit_at(a1.clone(), index35.clone());
                let v40: typed::Word4 = if v39.clone() {
                    v38.clone()
                } else {
                    v37.clone()
                };
                v40.clone()
            };
        }
        acc36
    };
    Ok(v41.clone())
}

// method 2: "u64.field.square"
fn method_2(a0: typed::Word4, a1: typed::Word4) -> witgen_native::Result<typed::Word4> {
    let v42: typed::Word4 = method_1(a0.clone(), a1.clone(), a1.clone())?;
    Ok(v42.clone())
}

// method 3: "field.0.add.u64"
fn method_3(
    a0: typed::WordField<0>,
    a1: typed::WordField<0>,
) -> witgen_native::Result<typed::WordField<0>> {
    let v43: typed::Word4 = (a0.clone()).0;
    let v44: typed::Word4 = (a1.clone()).0;
    let v45: typed::Word4 = [
        4891460686036598785u64,
        2896914383306846353u64,
        13281191951274694749u64,
        3486998266802970665u64,
    ];
    let v46: typed::Word4 = method_0(v45.clone(), v43.clone(), v44.clone())?;
    let v47: typed::WordField<0> = typed::WordField::<0>(v46.clone());
    Ok(v47.clone())
}

// method 4: "field.0.mul.u64"
fn method_4(
    a0: typed::WordField<0>,
    a1: typed::WordField<0>,
) -> witgen_native::Result<typed::WordField<0>> {
    let v48: typed::Word4 = (a0.clone()).0;
    let v49: typed::Word4 = (a1.clone()).0;
    let v50: typed::Word4 = [
        4891460686036598785u64,
        2896914383306846353u64,
        13281191951274694749u64,
        3486998266802970665u64,
    ];
    let v51: typed::Word4 = method_1(v50.clone(), v48.clone(), v49.clone())?;
    let v52: typed::WordField<0> = typed::WordField::<0>(v51.clone());
    Ok(v52.clone())
}

// method 5: "field.0.square.u64"
fn method_5(a0: typed::WordField<0>) -> witgen_native::Result<typed::WordField<0>> {
    let v53: typed::Word4 = (a0.clone()).0;
    let v54: typed::Word4 = [
        4891460686036598785u64,
        2896914383306846353u64,
        13281191951274694749u64,
        3486998266802970665u64,
    ];
    let v55: typed::Word4 = method_2(v54.clone(), v53.clone())?;
    let v56: typed::WordField<0> = typed::WordField::<0>(v55.clone());
    Ok(v56.clone())
}

// method 6: "field.1.add.u64"
fn method_6(
    a0: typed::WordField<1>,
    a1: typed::WordField<1>,
) -> witgen_native::Result<typed::WordField<1>> {
    let v57: typed::Word4 = (a0.clone()).0;
    let v58: typed::Word4 = (a1.clone()).0;
    let v59: typed::Word4 = [
        18446744069414583343u64,
        18446744073709551615u64,
        18446744073709551615u64,
        18446744073709551615u64,
    ];
    let v60: typed::Word4 = method_0(v59.clone(), v57.clone(), v58.clone())?;
    let v61: typed::WordField<1> = typed::WordField::<1>(v60.clone());
    Ok(v61.clone())
}

// method 7: "field.1.mul.u64"
fn method_7(
    a0: typed::WordField<1>,
    a1: typed::WordField<1>,
) -> witgen_native::Result<typed::WordField<1>> {
    let v62: typed::Word4 = (a0.clone()).0;
    let v63: typed::Word4 = (a1.clone()).0;
    let v64: typed::Word4 = [
        18446744069414583343u64,
        18446744073709551615u64,
        18446744073709551615u64,
        18446744073709551615u64,
    ];
    let v65: typed::Word4 = method_1(v64.clone(), v62.clone(), v63.clone())?;
    let v66: typed::WordField<1> = typed::WordField::<1>(v65.clone());
    Ok(v66.clone())
}

// method 8: "field.1.square.u64"
fn method_8(a0: typed::WordField<1>) -> witgen_native::Result<typed::WordField<1>> {
    let v67: typed::Word4 = (a0.clone()).0;
    let v68: typed::Word4 = [
        18446744069414583343u64,
        18446744073709551615u64,
        18446744073709551615u64,
        18446744073709551615u64,
    ];
    let v69: typed::Word4 = method_2(v68.clone(), v67.clone())?;
    let v70: typed::WordField<1> = typed::WordField::<1>(v69.clone());
    Ok(v70.clone())
}

// method 9: "field.2.add.u64"
fn method_9(
    a0: typed::WordField<2>,
    a1: typed::WordField<2>,
) -> witgen_native::Result<typed::WordField<2>> {
    let v71: typed::Word4 = (a0.clone()).0;
    let v72: typed::Word4 = (a1.clone()).0;
    let v73: typed::Word4 = [
        13822214165235122497u64,
        13451932020343611451u64,
        18446744073709551614u64,
        18446744073709551615u64,
    ];
    let v74: typed::Word4 = method_0(v73.clone(), v71.clone(), v72.clone())?;
    let v75: typed::WordField<2> = typed::WordField::<2>(v74.clone());
    Ok(v75.clone())
}

// method 10: "field.2.mul.u64"
fn method_10(
    a0: typed::WordField<2>,
    a1: typed::WordField<2>,
) -> witgen_native::Result<typed::WordField<2>> {
    let v76: typed::Word4 = (a0.clone()).0;
    let v77: typed::Word4 = (a1.clone()).0;
    let v78: typed::Word4 = [
        13822214165235122497u64,
        13451932020343611451u64,
        18446744073709551614u64,
        18446744073709551615u64,
    ];
    let v79: typed::Word4 = method_1(v78.clone(), v76.clone(), v77.clone())?;
    let v80: typed::WordField<2> = typed::WordField::<2>(v79.clone());
    Ok(v80.clone())
}

// method 11: "field.2.square.u64"
fn method_11(a0: typed::WordField<2>) -> witgen_native::Result<typed::WordField<2>> {
    let v81: typed::Word4 = (a0.clone()).0;
    let v82: typed::Word4 = [
        13822214165235122497u64,
        13451932020343611451u64,
        18446744073709551614u64,
        18446744073709551615u64,
    ];
    let v83: typed::Word4 = method_2(v82.clone(), v81.clone())?;
    let v84: typed::WordField<2> = typed::WordField::<2>(v83.clone());
    Ok(v84.clone())
}

// program: "field.0.add"
pub fn program_0(
    a0: typed::WordField<0>,
    a1: typed::WordField<0>,
) -> witgen_native::Result<typed::WordField<0>> {
    let v85: typed::WordField<0> = method_3(a0.clone(), a1.clone())?;
    Ok(v85.clone())
}

fn program_0_decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::WordField<0>> {
    Ok(typed::parse_word_field::<0>(value)?)
}

fn program_0_encode_0(value: typed::WordField<0>) -> serde_json::Value {
    serde_json::Value::String(typed::word_field_decimal::<0>(value))
}

pub fn program_0_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 2 {
        return Err(witgen_native::Error::InputArity {
            expected: 2,
            actual: inputs.len(),
        });
    }
    Ok(program_0_encode_0(program_0(
        program_0_decode_0(&inputs[0])?,
        program_0_decode_0(&inputs[1])?,
    )?))
}

// program: "field.0.mul"
pub fn program_1(
    a0: typed::WordField<0>,
    a1: typed::WordField<0>,
) -> witgen_native::Result<typed::WordField<0>> {
    let v86: typed::WordField<0> = method_4(a0.clone(), a1.clone())?;
    Ok(v86.clone())
}

fn program_1_decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::WordField<0>> {
    Ok(typed::parse_word_field::<0>(value)?)
}

fn program_1_encode_0(value: typed::WordField<0>) -> serde_json::Value {
    serde_json::Value::String(typed::word_field_decimal::<0>(value))
}

pub fn program_1_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 2 {
        return Err(witgen_native::Error::InputArity {
            expected: 2,
            actual: inputs.len(),
        });
    }
    Ok(program_1_encode_0(program_1(
        program_1_decode_0(&inputs[0])?,
        program_1_decode_0(&inputs[1])?,
    )?))
}

// program: "field.0.square"
pub fn program_2(a0: typed::WordField<0>) -> witgen_native::Result<typed::WordField<0>> {
    let v87: typed::WordField<0> = method_5(a0.clone())?;
    Ok(v87.clone())
}

fn program_2_decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::WordField<0>> {
    Ok(typed::parse_word_field::<0>(value)?)
}

fn program_2_encode_0(value: typed::WordField<0>) -> serde_json::Value {
    serde_json::Value::String(typed::word_field_decimal::<0>(value))
}

pub fn program_2_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 1 {
        return Err(witgen_native::Error::InputArity {
            expected: 1,
            actual: inputs.len(),
        });
    }
    Ok(program_2_encode_0(program_2(program_2_decode_0(
        &inputs[0],
    )?)?))
}

// program: "field.1.add"
pub fn program_3(
    a0: typed::WordField<1>,
    a1: typed::WordField<1>,
) -> witgen_native::Result<typed::WordField<1>> {
    let v88: typed::WordField<1> = method_6(a0.clone(), a1.clone())?;
    Ok(v88.clone())
}

fn program_3_decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::WordField<1>> {
    Ok(typed::parse_word_field::<1>(value)?)
}

fn program_3_encode_0(value: typed::WordField<1>) -> serde_json::Value {
    serde_json::Value::String(typed::word_field_decimal::<1>(value))
}

pub fn program_3_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 2 {
        return Err(witgen_native::Error::InputArity {
            expected: 2,
            actual: inputs.len(),
        });
    }
    Ok(program_3_encode_0(program_3(
        program_3_decode_0(&inputs[0])?,
        program_3_decode_0(&inputs[1])?,
    )?))
}

// program: "field.1.mul"
pub fn program_4(
    a0: typed::WordField<1>,
    a1: typed::WordField<1>,
) -> witgen_native::Result<typed::WordField<1>> {
    let v89: typed::WordField<1> = method_7(a0.clone(), a1.clone())?;
    Ok(v89.clone())
}

fn program_4_decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::WordField<1>> {
    Ok(typed::parse_word_field::<1>(value)?)
}

fn program_4_encode_0(value: typed::WordField<1>) -> serde_json::Value {
    serde_json::Value::String(typed::word_field_decimal::<1>(value))
}

pub fn program_4_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 2 {
        return Err(witgen_native::Error::InputArity {
            expected: 2,
            actual: inputs.len(),
        });
    }
    Ok(program_4_encode_0(program_4(
        program_4_decode_0(&inputs[0])?,
        program_4_decode_0(&inputs[1])?,
    )?))
}

// program: "field.1.square"
pub fn program_5(a0: typed::WordField<1>) -> witgen_native::Result<typed::WordField<1>> {
    let v90: typed::WordField<1> = method_8(a0.clone())?;
    Ok(v90.clone())
}

fn program_5_decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::WordField<1>> {
    Ok(typed::parse_word_field::<1>(value)?)
}

fn program_5_encode_0(value: typed::WordField<1>) -> serde_json::Value {
    serde_json::Value::String(typed::word_field_decimal::<1>(value))
}

pub fn program_5_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 1 {
        return Err(witgen_native::Error::InputArity {
            expected: 1,
            actual: inputs.len(),
        });
    }
    Ok(program_5_encode_0(program_5(program_5_decode_0(
        &inputs[0],
    )?)?))
}

// program: "field.2.add"
pub fn program_6(
    a0: typed::WordField<2>,
    a1: typed::WordField<2>,
) -> witgen_native::Result<typed::WordField<2>> {
    let v91: typed::WordField<2> = method_9(a0.clone(), a1.clone())?;
    Ok(v91.clone())
}

fn program_6_decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::WordField<2>> {
    Ok(typed::parse_word_field::<2>(value)?)
}

fn program_6_encode_0(value: typed::WordField<2>) -> serde_json::Value {
    serde_json::Value::String(typed::word_field_decimal::<2>(value))
}

pub fn program_6_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 2 {
        return Err(witgen_native::Error::InputArity {
            expected: 2,
            actual: inputs.len(),
        });
    }
    Ok(program_6_encode_0(program_6(
        program_6_decode_0(&inputs[0])?,
        program_6_decode_0(&inputs[1])?,
    )?))
}

// program: "field.2.mul"
pub fn program_7(
    a0: typed::WordField<2>,
    a1: typed::WordField<2>,
) -> witgen_native::Result<typed::WordField<2>> {
    let v92: typed::WordField<2> = method_10(a0.clone(), a1.clone())?;
    Ok(v92.clone())
}

fn program_7_decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::WordField<2>> {
    Ok(typed::parse_word_field::<2>(value)?)
}

fn program_7_encode_0(value: typed::WordField<2>) -> serde_json::Value {
    serde_json::Value::String(typed::word_field_decimal::<2>(value))
}

pub fn program_7_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 2 {
        return Err(witgen_native::Error::InputArity {
            expected: 2,
            actual: inputs.len(),
        });
    }
    Ok(program_7_encode_0(program_7(
        program_7_decode_0(&inputs[0])?,
        program_7_decode_0(&inputs[1])?,
    )?))
}

// program: "field.2.square"
pub fn program_8(a0: typed::WordField<2>) -> witgen_native::Result<typed::WordField<2>> {
    let v93: typed::WordField<2> = method_11(a0.clone())?;
    Ok(v93.clone())
}

fn program_8_decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::WordField<2>> {
    Ok(typed::parse_word_field::<2>(value)?)
}

fn program_8_encode_0(value: typed::WordField<2>) -> serde_json::Value {
    serde_json::Value::String(typed::word_field_decimal::<2>(value))
}

pub fn program_8_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 1 {
        return Err(witgen_native::Error::InputArity {
            expected: 1,
            actual: inputs.len(),
        });
    }
    Ok(program_8_encode_0(program_8(program_8_decode_0(
        &inputs[0],
    )?)?))
}

// program: "field_0_u64_methods"
pub fn program_9(
    a0: typed::WordField<0>,
    a1: typed::WordField<0>,
) -> witgen_native::Result<typed::WordField<0>> {
    let v94: typed::WordField<0> = method_5(a0.clone())?;
    let v95: typed::WordField<0> = method_4(v94.clone(), a1.clone())?;
    let v96: typed::WordField<0> = typed::WordField::<0>([5u64, 0u64, 0u64, 0u64]);
    let v97: typed::WordField<0> = method_3(v95.clone(), v96.clone())?;
    Ok(v97.clone())
}

fn program_9_decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::WordField<0>> {
    Ok(typed::parse_word_field::<0>(value)?)
}

fn program_9_encode_0(value: typed::WordField<0>) -> serde_json::Value {
    serde_json::Value::String(typed::word_field_decimal::<0>(value))
}

pub fn program_9_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 2 {
        return Err(witgen_native::Error::InputArity {
            expected: 2,
            actual: inputs.len(),
        });
    }
    Ok(program_9_encode_0(program_9(
        program_9_decode_0(&inputs[0])?,
        program_9_decode_0(&inputs[1])?,
    )?))
}

// program: "field_1_u64_methods"
pub fn program_10(
    a0: typed::WordField<1>,
    a1: typed::WordField<1>,
) -> witgen_native::Result<typed::WordField<1>> {
    let v98: typed::WordField<1> = method_8(a0.clone())?;
    let v99: typed::WordField<1> = method_7(v98.clone(), a1.clone())?;
    let v100: typed::WordField<1> = typed::WordField::<1>([5u64, 0u64, 0u64, 0u64]);
    let v101: typed::WordField<1> = method_6(v99.clone(), v100.clone())?;
    Ok(v101.clone())
}

fn program_10_decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::WordField<1>> {
    Ok(typed::parse_word_field::<1>(value)?)
}

fn program_10_encode_0(value: typed::WordField<1>) -> serde_json::Value {
    serde_json::Value::String(typed::word_field_decimal::<1>(value))
}

pub fn program_10_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 2 {
        return Err(witgen_native::Error::InputArity {
            expected: 2,
            actual: inputs.len(),
        });
    }
    Ok(program_10_encode_0(program_10(
        program_10_decode_0(&inputs[0])?,
        program_10_decode_0(&inputs[1])?,
    )?))
}

// program: "field_2_u64_methods"
pub fn program_11(
    a0: typed::WordField<2>,
    a1: typed::WordField<2>,
) -> witgen_native::Result<typed::WordField<2>> {
    let v102: typed::WordField<2> = method_11(a0.clone())?;
    let v103: typed::WordField<2> = method_10(v102.clone(), a1.clone())?;
    let v104: typed::WordField<2> = typed::WordField::<2>([5u64, 0u64, 0u64, 0u64]);
    let v105: typed::WordField<2> = method_9(v103.clone(), v104.clone())?;
    Ok(v105.clone())
}

fn program_11_decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::WordField<2>> {
    Ok(typed::parse_word_field::<2>(value)?)
}

fn program_11_encode_0(value: typed::WordField<2>) -> serde_json::Value {
    serde_json::Value::String(typed::word_field_decimal::<2>(value))
}

pub fn program_11_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 2 {
        return Err(witgen_native::Error::InputArity {
            expected: 2,
            actual: inputs.len(),
        });
    }
    Ok(program_11_encode_0(program_11(
        program_11_decode_0(&inputs[0])?,
        program_11_decode_0(&inputs[1])?,
    )?))
}

pub fn run_json(
    program: usize,
    inputs: &[serde_json::Value],
) -> witgen_native::Result<serde_json::Value> {
    match program {
        0 => program_0_json(inputs),
        1 => program_1_json(inputs),
        2 => program_2_json(inputs),
        3 => program_3_json(inputs),
        4 => program_4_json(inputs),
        5 => program_5_json(inputs),
        6 => program_6_json(inputs),
        7 => program_7_json(inputs),
        8 => program_8_json(inputs),
        9 => program_9_json(inputs),
        10 => program_10_json(inputs),
        11 => program_11_json(inputs),
        _ => Err(witgen_native::Error::UnknownProgram(program.to_string())),
    }
}
