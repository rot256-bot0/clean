use witgen_native::typed;

// program: "curve_const_identity"
pub fn run() -> witgen_native::Result<typed::SecpPoint> {
    let v0: typed::SecpPoint = typed::point_identity();
    Ok(v0.clone())
}

fn encode_0(value: typed::SecpPoint) -> serde_json::Value {
    serde_json::Value::String(typed::point_hex(value))
}

pub fn run_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 0 {
        return Err(witgen_native::Error::InputArity {
            expected: 0,
            actual: inputs.len(),
        });
    }
    Ok(encode_0(run()?))
}
