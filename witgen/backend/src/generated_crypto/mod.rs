// Generated typed-program dispatch.
pub mod envelope_bn254;
pub mod envelope_nat;
pub mod quad_bn254;
pub mod quad_nat;
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
        "quad_bn254" => {
            if inputs.len() != 2 {
                return Err(witgen_native::Error::InputArity {
                    expected: 2,
                    actual: inputs.len(),
                });
            }
            let mut cells = [witgen_native::Bn254Scalar::from(0u64); 4];
            cells[0] = witgen_native::bn254_from_nat(&parse_scalar(&inputs[0], "bn254")?)?;
            cells[1] = witgen_native::bn254_from_nat(&parse_scalar(&inputs[1], "bn254")?)?;
            quad_bn254::populate(&mut cells)?;
            Ok(
                serde_json::json!({"program": "quad_bn254", "cells": cells.into_iter().map(witgen_native::bn254_to_decimal).collect::<Vec<_>>()}),
            )
        }
        "quad_nat" => {
            if inputs.len() != 2 {
                return Err(witgen_native::Error::InputArity {
                    expected: 2,
                    actual: inputs.len(),
                });
            }
            let mut cells = [witgen_native::Bn254Scalar::from(0u64); 4];
            cells[0] = witgen_native::bn254_from_nat(&parse_scalar(&inputs[0], "bn254")?)?;
            cells[1] = witgen_native::bn254_from_nat(&parse_scalar(&inputs[1], "bn254")?)?;
            quad_nat::populate(&mut cells)?;
            Ok(
                serde_json::json!({"program": "quad_nat", "cells": cells.into_iter().map(witgen_native::bn254_to_decimal).collect::<Vec<_>>()}),
            )
        }
        "envelope_bn254" => {
            if inputs.len() != 2 {
                return Err(witgen_native::Error::InputArity {
                    expected: 2,
                    actual: inputs.len(),
                });
            }
            let mut cells = [witgen_native::Bn254Scalar::from(0u64); 4];
            cells[0] = witgen_native::bn254_from_nat(&parse_scalar(&inputs[0], "bn254")?)?;
            cells[1] = witgen_native::bn254_from_nat(&parse_scalar(&inputs[1], "bn254")?)?;
            envelope_bn254::populate(&mut cells)?;
            Ok(
                serde_json::json!({"program": "envelope_bn254", "cells": cells.into_iter().map(witgen_native::bn254_to_decimal).collect::<Vec<_>>()}),
            )
        }
        "envelope_nat" => {
            if inputs.len() != 2 {
                return Err(witgen_native::Error::InputArity {
                    expected: 2,
                    actual: inputs.len(),
                });
            }
            let mut cells = [witgen_native::Bn254Scalar::from(0u64); 4];
            cells[0] = witgen_native::bn254_from_nat(&parse_scalar(&inputs[0], "bn254")?)?;
            cells[1] = witgen_native::bn254_from_nat(&parse_scalar(&inputs[1], "bn254")?)?;
            envelope_nat::populate(&mut cells)?;
            Ok(
                serde_json::json!({"program": "envelope_nat", "cells": cells.into_iter().map(witgen_native::bn254_to_decimal).collect::<Vec<_>>()}),
            )
        }
        _ => Err(witgen_native::Error::UnknownProgram(program.to_owned())),
    }
}
