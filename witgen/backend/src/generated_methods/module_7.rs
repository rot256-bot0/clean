use witgen_native::typed;

// program: "secp_generator_affine_roundtrip"
pub fn run() -> witgen_native::Result<Option<typed::SecpPoint>> {
    let v0: typed::SecpPoint = typed::point_generator();
    let v1: Option<(typed::SecpBase, typed::SecpBase)> = typed::to_affine(v0.clone());
    let v4: Option<typed::SecpPoint> = match v1.clone() {
        Some(some2) => {
            let v3: Option<typed::SecpPoint> = typed::from_affine(some2.clone());
            v3.clone()
        }
        None => None,
    };
    Ok(v4.clone())
}

fn encode_1(value: typed::SecpPoint) -> serde_json::Value {
    serde_json::Value::String(typed::point_hex(value))
}

fn encode_0(value: Option<typed::SecpPoint>) -> serde_json::Value {
    match value {
        Some(x) => encode_1(x),
        None => serde_json::Value::Null,
    }
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
