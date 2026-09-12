use witgen_native::typed;

// program: "secp_from_affine"
pub fn run(
    a0: (typed::SecpBase, typed::SecpBase),
) -> witgen_native::Result<Option<typed::SecpPoint>> {
    let v0: Option<typed::SecpPoint> = typed::from_affine(a0.clone());
    Ok(v0.clone())
}

fn decode_1(value: &serde_json::Value) -> witgen_native::Result<typed::SecpBase> {
    Ok(typed::secp_base_from_nat(&typed::parse_nat(value)?)?)
}

fn decode_0(
    value: &serde_json::Value,
) -> witgen_native::Result<(typed::SecpBase, typed::SecpBase)> {
    Ok({
        let pair = value
            .as_array()
            .ok_or(witgen_native::Error::InvalidInputType {
                expected: "pair array",
            })?;
        if pair.len() != 2 {
            return Err(witgen_native::Error::InputLength {
                expected: 2,
                actual: pair.len(),
            });
        }
        (decode_1(&pair[0])?, decode_1(&pair[1])?)
    })
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
