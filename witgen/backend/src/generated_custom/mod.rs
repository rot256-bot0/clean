// Generated typed-program dispatch.
pub mod custom_low;
pub mod custom_split;
fn parse_scalar(value: &serde_json::Value, semantic: &str) -> witgen_native::Result<rug::Integer> {
    let text = if let Some(s) = value.as_str() {
        s.to_string()
    } else if let Some(n) = value.as_u64() {
        n.to_string()
    } else {
        return Err(witgen_native::Error::InvalidInputType {
            expected: "nonnegative decimal integer",
        });
    };
    let n = witgen_native::nat_from_str(&text)?;
    if semantic == "field17" && n >= 17 {
        return Err(witgen_native::Error::NonCanonicalField { field: "field17" });
    }
    if semantic == "bn254" && n >= witgen_native::bn254_modulus() {
        return Err(witgen_native::Error::NonCanonicalField { field: "bn254" });
    }
    Ok(n)
}

pub fn dispatch(
    program: &str,
    inputs: &[serde_json::Value],
) -> witgen_native::Result<serde_json::Value> {
    match program {
        "custom_split" => {
            if inputs.len() != 1 {
                return Err(witgen_native::Error::InputArity {
                    expected: 1,
                    actual: inputs.len(),
                });
            }
            let result = custom_split::generate(parse_scalar(&inputs[0], "nat")?)?;
            Ok(
                serde_json::json!({"program": "custom_split", "value": serde_json::json!({"low": serde_json::Value::String((&(&result).low).to_string()), "high": serde_json::Value::String((&(&result).high).to_string())})}),
            )
        }
        "custom_low" => {
            if inputs.len() != 1 {
                return Err(witgen_native::Error::InputArity {
                    expected: 1,
                    actual: inputs.len(),
                });
            }
            let result = custom_low::generate(parse_scalar(&inputs[0], "nat")?)?;
            Ok(
                serde_json::json!({"program": "custom_low", "value": serde_json::Value::String((&result).to_string())}),
            )
        }
        _ => Err(witgen_native::Error::UnknownProgram(program.to_owned())),
    }
}
