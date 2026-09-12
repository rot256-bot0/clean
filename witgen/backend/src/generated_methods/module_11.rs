use witgen_native::typed;

// program: "curve_eq"
pub fn run(a0: typed::SecpPoint, a1: typed::SecpPoint) -> witgen_native::Result<bool> {
    let v0: bool = typed::point_eq(a0.clone(), a1.clone());
    Ok(v0.clone())
}

fn decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::SecpPoint> {
    Ok(typed::parse_point(value)?)
}

fn encode_0(value: bool) -> serde_json::Value {
    serde_json::Value::Bool(value)
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
