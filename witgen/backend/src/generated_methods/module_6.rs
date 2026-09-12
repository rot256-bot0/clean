use witgen_native::typed;

// program: "secp_mixed_fields"
pub fn run(
    a0: typed::SecpScalar,
    a1: typed::SecpScalar,
) -> witgen_native::Result<Option<typed::SecpBase>> {
    let v0: typed::SecpScalar = typed::secp_scalar_square(a0.clone());
    let v1: typed::SecpScalar = typed::secp_scalar_mul(v0.clone(), a1.clone());
    let v2: typed::SecpScalar = typed::secp_scalar_add(v1.clone(), a0.clone());
    let v3: typed::SecpPoint = typed::point_generator();
    let v4: typed::SecpPoint = typed::point_mul(v2.clone(), v3.clone());
    let v5: typed::SecpPoint = typed::point_inv(v3.clone());
    let v6: typed::SecpPoint = typed::point_add(v4.clone(), v5.clone());
    let v7: Option<(typed::SecpBase, typed::SecpBase)> = typed::to_affine(v6.clone());
    let v16: Option<typed::SecpBase> = match v7.clone() {
        None => {
            let v9: Option<typed::SecpBase> = None::<typed::SecpBase>;
            v9.clone()
        }
        Some(_some8) => {
            let v10: typed::SecpBase = (_some8.clone()).0;
            let v11: typed::SecpBase = (_some8.clone()).1;
            let v12: typed::SecpBase = typed::secp_base_square(v10.clone());
            let v13: typed::SecpBase = typed::secp_base_mul(v12.clone(), v11.clone());
            let v14: typed::SecpBase = typed::secp_base_add(v13.clone(), v10.clone());
            let v15: Option<typed::SecpBase> = Some(v14.clone());
            v15.clone()
        }
    };
    Ok(v16.clone())
}

fn decode_0(value: &serde_json::Value) -> witgen_native::Result<typed::SecpScalar> {
    Ok(typed::secp_scalar_from_nat(&typed::parse_nat(value)?)?)
}

fn encode_1(value: typed::SecpBase) -> serde_json::Value {
    serde_json::Value::String(typed::secp_base_to_nat(value).to_string())
}

fn encode_0(value: Option<typed::SecpBase>) -> serde_json::Value {
    match value {
        Some(x) => encode_1(x),
        None => serde_json::Value::Null,
    }
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
