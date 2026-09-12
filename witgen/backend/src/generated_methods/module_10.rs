use witgen_native::typed;

// program: "secp_affine_roundtrip"
pub fn run(a0: typed::SecpPoint) -> witgen_native::Result<Option<typed::SecpPoint>> {
    let v0: Option<(typed::SecpBase, typed::SecpBase)> = typed::to_affine(a0.clone());
    let v4: Option<typed::SecpPoint> = match v0.clone() {
        None => {
            let v2: Option<typed::SecpPoint> = None::<typed::SecpPoint>;
            v2.clone()
        }
        Some(_some1) => {
            let v3: Option<typed::SecpPoint> = typed::from_affine(_some1.clone());
            v3.clone()
        }
    };
    Ok(v4.clone())
}

fn decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::SecpPoint> {
    Ok(typed::parse_point(value)?)
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
    if inputs.len() != 1 {
        return Err(witgen_native::Error::InputArity {
            expected: 1,
            actual: inputs.len(),
        });
    }
    Ok(encode_0(run(decode_0(&inputs[0])?)?))
}
