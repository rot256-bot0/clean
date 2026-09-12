use witgen_native::typed;

// program: "field_0_native"
pub fn run(
    a0: witgen_native::Bn254Scalar,
    a1: witgen_native::Bn254Scalar,
) -> witgen_native::Result<witgen_native::Bn254Scalar> {
    let v0: witgen_native::Bn254Scalar = typed::bn254_square(a0.clone());
    let v1: witgen_native::Bn254Scalar = witgen_native::bn254_mul(v0.clone(), a1.clone());
    let v2: witgen_native::Bn254Scalar = witgen_native::bn254_from_nat(
        &(rug::Integer::from_str_radix("5", 10)?
            % rug::Integer::from_str_radix(
                "21888242871839275222246405745257275088548364400416034343698204186575808495617",
                10,
            )?),
    )?;
    let v3: witgen_native::Bn254Scalar = witgen_native::bn254_add(v1.clone(), v2.clone());
    Ok(v3.clone())
}

fn decode_0(value: &serde_json::Value) -> witgen_native::Result<witgen_native::Bn254Scalar> {
    Ok(witgen_native::bn254_from_nat(&typed::parse_nat(value)?)?)
}

fn encode_0(value: witgen_native::Bn254Scalar) -> serde_json::Value {
    serde_json::Value::String(witgen_native::bn254_to_nat(value).to_string())
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
