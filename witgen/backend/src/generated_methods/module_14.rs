use witgen_native::typed;

// program: "curve_const_generator"
pub fn run() -> witgen_native::Result<typed::SecpPoint> {
    let v0: typed::SecpPoint = typed::point_const(
        typed::secp_base_from_str(
            "55066263022277343669578718895168534326250603453777594175500187360389116729240",
        )?,
        typed::secp_base_from_str(
            "32670510020758816978083085130507043184471273380659243275938904335757337482424",
        )?,
    );
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
