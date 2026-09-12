use witgen_native::typed;

// program: "curve_msm_constructed"
pub fn run(a0: typed::SecpScalar, a1: typed::SecpPoint) -> witgen_native::Result<typed::SecpPoint> {
    let v0: (typed::SecpScalar, typed::SecpPoint) = (a0.clone(), a1.clone());
    let v1: Vec<(typed::SecpScalar, typed::SecpPoint)> =
        Vec::<(typed::SecpScalar, typed::SecpPoint)>::new();
    let v3: Vec<(typed::SecpScalar, typed::SecpPoint)> = {
        let mut items2 = vec![v0.clone()];
        items2.extend(v1.clone());
        items2
    };
    let v4: typed::SecpPoint = typed::point_msm(v3.clone())?;
    Ok(v4.clone())
}

fn decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::SecpScalar> {
    Ok(typed::secp_scalar_from_nat(&typed::parse_nat(value)?)?)
}

fn decode_1(value: &serde_json::Value) -> witgen_native::Result<typed::SecpPoint> {
    Ok(typed::parse_point(value)?)
}

fn encode_0(value: typed::SecpPoint) -> serde_json::Value {
    serde_json::Value::String(typed::point_hex(value))
}

pub fn run_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 2 {
        return Err(witgen_native::Error::InputArity {
            expected: 2,
            actual: inputs.len(),
        });
    }
    Ok(encode_0(run(decode_0(&inputs[0])?, decode_1(&inputs[1])?)?))
}
