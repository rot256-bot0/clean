use witgen_native::typed;

// program: "secp_mixed_fields"
pub fn run(
    a0: typed::SecpScalar,
    a1: typed::SecpScalar,
    a2: typed::SecpBase,
) -> witgen_native::Result<typed::SecpBase> {
    let v0: typed::SecpScalar = typed::secp_scalar_square(a0.clone());
    let v1: typed::SecpScalar = typed::secp_scalar_mul(v0.clone(), a1.clone());
    let v2: typed::SecpScalar = typed::secp_scalar_add(v1.clone(), a0.clone());
    let v3: typed::SecpPoint = typed::point_generator();
    let v4: typed::SecpPoint = typed::point_scale(v2.clone(), v3.clone());
    let v5: typed::SecpPoint = typed::point_inv(v3.clone());
    let v6: typed::SecpPoint = typed::point_add(v4.clone(), v5.clone());
    let v7: typed::SecpBase = typed::point_x(v6.clone());
    let v8: typed::SecpBase = typed::point_x(v3.clone());
    let v9: typed::SecpBase = typed::secp_base_square(a2.clone());
    let v10: typed::SecpBase = typed::secp_base_mul(v9.clone(), v7.clone());
    let v11: typed::SecpBase = typed::secp_base_add(v10.clone(), v8.clone());
    Ok(v11.clone())
}

fn decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::SecpScalar> {
    Ok(typed::secp_scalar_from_nat(&typed::parse_nat(value)?)?)
}

fn decode_1(value: &serde_json::Value) -> witgen_native::Result<typed::SecpBase> {
    Ok(typed::secp_base_from_nat(&typed::parse_nat(value)?)?)
}

fn encode_0(value: typed::SecpBase) -> serde_json::Value {
    serde_json::Value::String(typed::secp_base_to_nat(value).to_string())
}

pub fn run_json(inputs: &[serde_json::Value]) -> witgen_native::Result<serde_json::Value> {
    if inputs.len() != 3 {
        return Err(witgen_native::Error::InputArity {
            expected: 3,
            actual: inputs.len(),
        });
    }
    Ok(encode_0(run(
        decode_0(&inputs[0])?,
        decode_0(&inputs[1])?,
        decode_1(&inputs[2])?,
    )?))
}
