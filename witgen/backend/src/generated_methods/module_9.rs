use witgen_native::typed;

// program: "secp_to_affine"
pub fn run(
    a0: typed::SecpPoint,
) -> witgen_native::Result<Option<(typed::SecpBase, typed::SecpBase)>> {
    let v0: Option<(typed::SecpBase, typed::SecpBase)> = typed::to_affine(a0.clone());
    Ok(v0.clone())
}

fn decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::SecpPoint> {
    Ok(typed::parse_point(value)?)
}

fn encode_2(value: typed::SecpBase) -> serde_json::Value {
    serde_json::Value::String(typed::secp_base_to_nat(value).to_string())
}

fn encode_1(value: (typed::SecpBase, typed::SecpBase)) -> serde_json::Value {
    serde_json::Value::Array(vec![encode_2(value.0), encode_2(value.1)])
}

fn encode_0(value: Option<(typed::SecpBase, typed::SecpBase)>) -> serde_json::Value {
    match value {
        Some(x) => encode_1(x),
        None => serde_json::Value::Null,
    }
}

pub fn run_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 1 {
        return Err(witgen_native::Error::InputArity {
            expected: 1,
            actual: inputs.len(),
        });
    }
    Ok(encode_0(run(decode_0(&inputs[0])?)?))
}
