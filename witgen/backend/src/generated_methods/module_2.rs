use witgen_native::typed;

// program: "field_1_native"
pub fn run(a0: typed::SecpBase, a1: typed::SecpBase) -> witgen_native::Result<typed::SecpBase> {
    let v0: typed::SecpBase = typed::secp_base_square(a0.clone());
    let v1: typed::SecpBase = typed::secp_base_mul(v0.clone(), a1.clone());
    let v2: typed::SecpBase = typed::secp_base_from_nat(
        &(rug::Integer::from_str_radix("5", 10)?
            % rug::Integer::from_str_radix(
                "115792089237316195423570985008687907853269984665640564039457584007908834671663",
                10,
            )?),
    )?;
    let v3: typed::SecpBase = typed::secp_base_add(v1.clone(), v2.clone());
    Ok(v3.clone())
}

fn decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::SecpBase> {
    Ok(typed::secp_base_from_nat(&typed::parse_nat(value)?)?)
}

fn encode_0(value: typed::SecpBase) -> serde_json::Value {
    serde_json::Value::String(typed::secp_base_to_nat(value).to_string())
}

pub fn run_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 2 {
        return Err(witgen_native::Error::InputArity {
            expected: 2,
            actual: inputs.len(),
        });
    }
    Ok(encode_0(run(decode_0(&inputs[0])?, decode_0(&inputs[1])?)?))
}
