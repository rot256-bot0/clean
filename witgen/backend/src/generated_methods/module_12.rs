use witgen_native::typed;

// program: "curve_msm"
pub fn run(
    a0: Vec<(typed::SecpScalar, typed::SecpPoint)>,
) -> witgen_native::Result<typed::SecpPoint> {
    let v0: typed::SecpPoint = typed::point_msm(a0.clone())?;
    Ok(v0.clone())
}

fn decode_2(value: &serde_json::Value) -> witgen_native::Result<typed::SecpScalar> {
    Ok(typed::secp_scalar_from_nat(&typed::parse_nat(value)?)?)
}

fn decode_3(value: &serde_json::Value) -> witgen_native::Result<typed::SecpPoint> {
    Ok(typed::parse_point(value)?)
}

fn decode_1(
    value: &serde_json::Value,
) -> witgen_native::Result<(typed::SecpScalar, typed::SecpPoint)> {
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
        (decode_2(&pair[0])?, decode_3(&pair[1])?)
    })
}

fn decode_0(
    value: &serde_json::Value,
) -> witgen_native::Result<Vec<(typed::SecpScalar, typed::SecpPoint)>> {
    Ok({
        let values = value
            .as_array()
            .ok_or(witgen_native::Error::InvalidInputType {
                expected: "list array",
            })?;
        values
            .iter()
            .map(decode_1)
            .collect::<witgen_native::Result<Vec<_>>>()?
    })
}

fn encode_0(value: typed::SecpPoint) -> serde_json::Value {
    serde_json::Value::String(typed::point_hex(value))
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
