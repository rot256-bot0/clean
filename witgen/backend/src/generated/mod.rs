// Generated typed-program dispatch.
pub mod batch_field;
pub mod batch_fold_field;
pub mod batch_fold_nat;
pub mod batch_fold_word;
pub mod batch_nat;
pub mod batch_word;
pub mod conditional_field;
pub mod conditional_fold_field;
pub mod conditional_fold_nat;
pub mod conditional_fold_word;
pub mod conditional_nat;
pub mod conditional_word;
pub mod modmul_nat;
pub mod modmul_nat_raw;
pub mod modmul_word;
pub mod quadratic_field;
pub mod quadratic_nat;
pub mod quadratic_word;
fn parse_scalar(value: &serde_json::Value, semantic: &str) -> Result<rug::Integer, String> {
    let text = if let Some(s) = value.as_str() {
        s.to_string()
    } else if let Some(n) = value.as_u64() {
        n.to_string()
    } else {
        return Err("expected a nonnegative decimal integer".into());
    };
    let n = witgen_native::nat_from_str(&text)?;
    if semantic == "field17" && n >= 17 {
        return Err("source field17 input is not canonical".into());
    }
    Ok(n)
}

pub fn dispatch(program: &str, inputs: &[serde_json::Value]) -> Result<serde_json::Value, String> {
    match program {
        "quadratic_field" => {
            if inputs.len() != 2 {
                return Err("input arity mismatch".into());
            }
            let mut cells = [witgen_native::F17::from(0u64); 4];
            cells[0] = witgen_native::f17_from_nat(&parse_scalar(&inputs[0], "field17")?)?;
            cells[1] = witgen_native::f17_from_nat(&parse_scalar(&inputs[1], "field17")?)?;
            quadratic_field::populate(&mut cells)?;
            Ok(
                serde_json::json!({"program": "quadratic_field", "cells": cells.into_iter().map(witgen_native::f17_to_u64).collect::<Vec<_>>()}),
            )
        }
        "quadratic_nat" => {
            if inputs.len() != 2 {
                return Err("input arity mismatch".into());
            }
            let mut cells = [witgen_native::F17::from(0u64); 4];
            cells[0] = witgen_native::f17_from_nat(&parse_scalar(&inputs[0], "field17")?)?;
            cells[1] = witgen_native::f17_from_nat(&parse_scalar(&inputs[1], "field17")?)?;
            quadratic_nat::populate(&mut cells)?;
            Ok(
                serde_json::json!({"program": "quadratic_nat", "cells": cells.into_iter().map(witgen_native::f17_to_u64).collect::<Vec<_>>()}),
            )
        }
        "quadratic_word" => {
            if inputs.len() != 2 {
                return Err("input arity mismatch".into());
            }
            let mut cells = [witgen_native::F17::from(0u64); 4];
            cells[0] = witgen_native::f17_from_nat(&parse_scalar(&inputs[0], "field17")?)?;
            cells[1] = witgen_native::f17_from_nat(&parse_scalar(&inputs[1], "field17")?)?;
            quadratic_word::populate(&mut cells)?;
            Ok(
                serde_json::json!({"program": "quadratic_word", "cells": cells.into_iter().map(witgen_native::f17_to_u64).collect::<Vec<_>>()}),
            )
        }
        "modmul_nat" => {
            if inputs.len() != 3 {
                return Err("input arity mismatch".into());
            }
            let mut cells = [witgen_native::F257::from(0u64); 6];
            cells[0] = witgen_native::f257_from_nat(&parse_scalar(&inputs[0], "nat")?)?;
            cells[1] = witgen_native::f257_from_nat(&parse_scalar(&inputs[1], "nat")?)?;
            cells[2] = witgen_native::f257_from_nat(&parse_scalar(&inputs[2], "nat")?)?;
            modmul_nat::populate(&mut cells)?;
            Ok(
                serde_json::json!({"program": "modmul_nat", "cells": cells.into_iter().map(witgen_native::f257_to_u64).collect::<Vec<_>>()}),
            )
        }
        "modmul_word" => {
            if inputs.len() != 3 {
                return Err("input arity mismatch".into());
            }
            let mut cells = [witgen_native::F257::from(0u64); 6];
            cells[0] = witgen_native::f257_from_nat(&parse_scalar(&inputs[0], "nat")?)?;
            cells[1] = witgen_native::f257_from_nat(&parse_scalar(&inputs[1], "nat")?)?;
            cells[2] = witgen_native::f257_from_nat(&parse_scalar(&inputs[2], "nat")?)?;
            modmul_word::populate(&mut cells)?;
            Ok(
                serde_json::json!({"program": "modmul_word", "cells": cells.into_iter().map(witgen_native::f257_to_u64).collect::<Vec<_>>()}),
            )
        }
        "modmul_nat_raw" => {
            if inputs.len() != 3 {
                return Err("input arity mismatch".into());
            }
            let result = modmul_nat_raw::generate(
                parse_scalar(&inputs[0], "nat")?,
                parse_scalar(&inputs[1], "nat")?,
                parse_scalar(&inputs[2], "nat")?,
            )?;
            Ok(
                serde_json::json!({"program": "modmul_nat_raw", "value": serde_json::json!({"product": serde_json::Value::String((&(&result).product).to_string()), "quotient": serde_json::Value::String((&(&result).quotient).to_string()), "remainder": serde_json::Value::String((&(&result).remainder).to_string())})}),
            )
        }
        "conditional_field" => {
            if inputs.len() != 3 {
                return Err("input arity mismatch".into());
            }
            let result = conditional_field::generate(
                (&inputs[0])
                    .as_bool()
                    .ok_or_else(|| "expected Boolean input".to_string())?,
                (&inputs[1])
                    .as_array()
                    .ok_or_else(|| "expected array input".to_string())?
                    .iter()
                    .map(|item_0| -> Result<witgen_native::F17, String> {
                        Ok(witgen_native::f17_from_nat(&parse_scalar(
                            item_0, "field17",
                        )?)?)
                    })
                    .collect::<Result<Vec<_>, String>>()?,
                witgen_native::f17_from_nat(&parse_scalar(&inputs[2], "field17")?)?,
            )?;
            Ok(
                serde_json::json!({"program": "conditional_field", "value": serde_json::Value::Array((&result).iter().map(|output_0| serde_json::json!({"square": serde_json::Value::String(witgen_native::f17_to_u64(*(&(output_0).square)).to_string()), "output": serde_json::Value::String(witgen_native::f17_to_u64(*(&(output_0).output)).to_string())})).collect())}),
            )
        }
        "conditional_nat" => {
            if inputs.len() != 3 {
                return Err("input arity mismatch".into());
            }
            let result = conditional_nat::generate(
                (&inputs[0])
                    .as_bool()
                    .ok_or_else(|| "expected Boolean input".to_string())?,
                (&inputs[1])
                    .as_array()
                    .ok_or_else(|| "expected array input".to_string())?
                    .iter()
                    .map(|item_0| -> Result<rug::Integer, String> {
                        Ok(parse_scalar(item_0, "field17")?)
                    })
                    .collect::<Result<Vec<_>, String>>()?,
                parse_scalar(&inputs[2], "field17")?,
            )?;
            Ok(
                serde_json::json!({"program": "conditional_nat", "value": serde_json::Value::Array((&result).iter().map(|output_0| serde_json::json!({"square": serde_json::Value::String((&(output_0).square).to_string()), "output": serde_json::Value::String((&(output_0).output).to_string())})).collect())}),
            )
        }
        "conditional_word" => {
            if inputs.len() != 3 {
                return Err("input arity mismatch".into());
            }
            let result = conditional_word::generate(
                (&inputs[0])
                    .as_bool()
                    .ok_or_else(|| "expected Boolean input".to_string())?,
                (&inputs[1])
                    .as_array()
                    .ok_or_else(|| "expected array input".to_string())?
                    .iter()
                    .map(|item_0| -> Result<u64, String> {
                        Ok(witgen_native::word_from_nat(&parse_scalar(
                            item_0, "field17",
                        )?)?)
                    })
                    .collect::<Result<Vec<_>, String>>()?,
                witgen_native::word_from_nat(&parse_scalar(&inputs[2], "field17")?)?,
            )?;
            Ok(
                serde_json::json!({"program": "conditional_word", "value": serde_json::Value::Array((&result).iter().map(|output_0| serde_json::json!({"square": serde_json::Value::String((&(output_0).square).to_string()), "output": serde_json::Value::String((&(output_0).output).to_string())})).collect())}),
            )
        }
        "conditional_fold_field" => {
            if inputs.len() != 3 {
                return Err("input arity mismatch".into());
            }
            let result = conditional_fold_field::generate(
                (&inputs[0])
                    .as_bool()
                    .ok_or_else(|| "expected Boolean input".to_string())?,
                (&inputs[1])
                    .as_array()
                    .ok_or_else(|| "expected array input".to_string())?
                    .iter()
                    .map(|item_0| -> Result<witgen_native::F17, String> {
                        Ok(witgen_native::f17_from_nat(&parse_scalar(
                            item_0, "field17",
                        )?)?)
                    })
                    .collect::<Result<Vec<_>, String>>()?,
                witgen_native::f17_from_nat(&parse_scalar(&inputs[2], "field17")?)?,
            )?;
            Ok(
                serde_json::json!({"program": "conditional_fold_field", "value": serde_json::Value::Array((&result).iter().map(|output_0| serde_json::json!({"square": serde_json::Value::String(witgen_native::f17_to_u64(*(&(output_0).square)).to_string()), "output": serde_json::Value::String(witgen_native::f17_to_u64(*(&(output_0).output)).to_string())})).collect())}),
            )
        }
        "conditional_fold_nat" => {
            if inputs.len() != 3 {
                return Err("input arity mismatch".into());
            }
            let result = conditional_fold_nat::generate(
                (&inputs[0])
                    .as_bool()
                    .ok_or_else(|| "expected Boolean input".to_string())?,
                (&inputs[1])
                    .as_array()
                    .ok_or_else(|| "expected array input".to_string())?
                    .iter()
                    .map(|item_0| -> Result<rug::Integer, String> {
                        Ok(parse_scalar(item_0, "field17")?)
                    })
                    .collect::<Result<Vec<_>, String>>()?,
                parse_scalar(&inputs[2], "field17")?,
            )?;
            Ok(
                serde_json::json!({"program": "conditional_fold_nat", "value": serde_json::Value::Array((&result).iter().map(|output_0| serde_json::json!({"square": serde_json::Value::String((&(output_0).square).to_string()), "output": serde_json::Value::String((&(output_0).output).to_string())})).collect())}),
            )
        }
        "conditional_fold_word" => {
            if inputs.len() != 3 {
                return Err("input arity mismatch".into());
            }
            let result = conditional_fold_word::generate(
                (&inputs[0])
                    .as_bool()
                    .ok_or_else(|| "expected Boolean input".to_string())?,
                (&inputs[1])
                    .as_array()
                    .ok_or_else(|| "expected array input".to_string())?
                    .iter()
                    .map(|item_0| -> Result<u64, String> {
                        Ok(witgen_native::word_from_nat(&parse_scalar(
                            item_0, "field17",
                        )?)?)
                    })
                    .collect::<Result<Vec<_>, String>>()?,
                witgen_native::word_from_nat(&parse_scalar(&inputs[2], "field17")?)?,
            )?;
            Ok(
                serde_json::json!({"program": "conditional_fold_word", "value": serde_json::Value::Array((&result).iter().map(|output_0| serde_json::json!({"square": serde_json::Value::String((&(output_0).square).to_string()), "output": serde_json::Value::String((&(output_0).output).to_string())})).collect())}),
            )
        }
        "batch_field" => {
            if inputs.len() != 3 {
                return Err("input arity mismatch".into());
            }
            let mut cells = [witgen_native::F17::from(0u64); 11];
            let _flag0 = inputs[0]
                .as_bool()
                .ok_or_else(|| "expected Boolean input".to_string())?;
            cells[0] = witgen_native::F17::from(if _flag0 { 1u64 } else { 0u64 });
            let _array1 = inputs[1]
                .as_array()
                .ok_or_else(|| "expected array input".to_string())?;
            if _array1.len() != 3 {
                return Err("input array length differs from circuit layout".into());
            }
            cells[1] = witgen_native::f17_from_nat(&parse_scalar(&_array1[0], "field17")?)?;
            cells[2] = witgen_native::f17_from_nat(&parse_scalar(&_array1[1], "field17")?)?;
            cells[3] = witgen_native::f17_from_nat(&parse_scalar(&_array1[2], "field17")?)?;
            cells[4] = witgen_native::f17_from_nat(&parse_scalar(&inputs[2], "field17")?)?;
            batch_field::populate(&mut cells)?;
            Ok(
                serde_json::json!({"program": "batch_field", "cells": cells.into_iter().map(witgen_native::f17_to_u64).collect::<Vec<_>>()}),
            )
        }
        "batch_nat" => {
            if inputs.len() != 3 {
                return Err("input arity mismatch".into());
            }
            let mut cells = [witgen_native::F17::from(0u64); 11];
            let _flag0 = inputs[0]
                .as_bool()
                .ok_or_else(|| "expected Boolean input".to_string())?;
            cells[0] = witgen_native::F17::from(if _flag0 { 1u64 } else { 0u64 });
            let _array1 = inputs[1]
                .as_array()
                .ok_or_else(|| "expected array input".to_string())?;
            if _array1.len() != 3 {
                return Err("input array length differs from circuit layout".into());
            }
            cells[1] = witgen_native::f17_from_nat(&parse_scalar(&_array1[0], "field17")?)?;
            cells[2] = witgen_native::f17_from_nat(&parse_scalar(&_array1[1], "field17")?)?;
            cells[3] = witgen_native::f17_from_nat(&parse_scalar(&_array1[2], "field17")?)?;
            cells[4] = witgen_native::f17_from_nat(&parse_scalar(&inputs[2], "field17")?)?;
            batch_nat::populate(&mut cells)?;
            Ok(
                serde_json::json!({"program": "batch_nat", "cells": cells.into_iter().map(witgen_native::f17_to_u64).collect::<Vec<_>>()}),
            )
        }
        "batch_word" => {
            if inputs.len() != 3 {
                return Err("input arity mismatch".into());
            }
            let mut cells = [witgen_native::F17::from(0u64); 11];
            let _flag0 = inputs[0]
                .as_bool()
                .ok_or_else(|| "expected Boolean input".to_string())?;
            cells[0] = witgen_native::F17::from(if _flag0 { 1u64 } else { 0u64 });
            let _array1 = inputs[1]
                .as_array()
                .ok_or_else(|| "expected array input".to_string())?;
            if _array1.len() != 3 {
                return Err("input array length differs from circuit layout".into());
            }
            cells[1] = witgen_native::f17_from_nat(&parse_scalar(&_array1[0], "field17")?)?;
            cells[2] = witgen_native::f17_from_nat(&parse_scalar(&_array1[1], "field17")?)?;
            cells[3] = witgen_native::f17_from_nat(&parse_scalar(&_array1[2], "field17")?)?;
            cells[4] = witgen_native::f17_from_nat(&parse_scalar(&inputs[2], "field17")?)?;
            batch_word::populate(&mut cells)?;
            Ok(
                serde_json::json!({"program": "batch_word", "cells": cells.into_iter().map(witgen_native::f17_to_u64).collect::<Vec<_>>()}),
            )
        }
        "batch_fold_field" => {
            if inputs.len() != 3 {
                return Err("input arity mismatch".into());
            }
            let mut cells = [witgen_native::F17::from(0u64); 11];
            let _flag0 = inputs[0]
                .as_bool()
                .ok_or_else(|| "expected Boolean input".to_string())?;
            cells[0] = witgen_native::F17::from(if _flag0 { 1u64 } else { 0u64 });
            let _array1 = inputs[1]
                .as_array()
                .ok_or_else(|| "expected array input".to_string())?;
            if _array1.len() != 3 {
                return Err("input array length differs from circuit layout".into());
            }
            cells[1] = witgen_native::f17_from_nat(&parse_scalar(&_array1[0], "field17")?)?;
            cells[2] = witgen_native::f17_from_nat(&parse_scalar(&_array1[1], "field17")?)?;
            cells[3] = witgen_native::f17_from_nat(&parse_scalar(&_array1[2], "field17")?)?;
            cells[4] = witgen_native::f17_from_nat(&parse_scalar(&inputs[2], "field17")?)?;
            batch_fold_field::populate(&mut cells)?;
            Ok(
                serde_json::json!({"program": "batch_fold_field", "cells": cells.into_iter().map(witgen_native::f17_to_u64).collect::<Vec<_>>()}),
            )
        }
        "batch_fold_nat" => {
            if inputs.len() != 3 {
                return Err("input arity mismatch".into());
            }
            let mut cells = [witgen_native::F17::from(0u64); 11];
            let _flag0 = inputs[0]
                .as_bool()
                .ok_or_else(|| "expected Boolean input".to_string())?;
            cells[0] = witgen_native::F17::from(if _flag0 { 1u64 } else { 0u64 });
            let _array1 = inputs[1]
                .as_array()
                .ok_or_else(|| "expected array input".to_string())?;
            if _array1.len() != 3 {
                return Err("input array length differs from circuit layout".into());
            }
            cells[1] = witgen_native::f17_from_nat(&parse_scalar(&_array1[0], "field17")?)?;
            cells[2] = witgen_native::f17_from_nat(&parse_scalar(&_array1[1], "field17")?)?;
            cells[3] = witgen_native::f17_from_nat(&parse_scalar(&_array1[2], "field17")?)?;
            cells[4] = witgen_native::f17_from_nat(&parse_scalar(&inputs[2], "field17")?)?;
            batch_fold_nat::populate(&mut cells)?;
            Ok(
                serde_json::json!({"program": "batch_fold_nat", "cells": cells.into_iter().map(witgen_native::f17_to_u64).collect::<Vec<_>>()}),
            )
        }
        "batch_fold_word" => {
            if inputs.len() != 3 {
                return Err("input arity mismatch".into());
            }
            let mut cells = [witgen_native::F17::from(0u64); 11];
            let _flag0 = inputs[0]
                .as_bool()
                .ok_or_else(|| "expected Boolean input".to_string())?;
            cells[0] = witgen_native::F17::from(if _flag0 { 1u64 } else { 0u64 });
            let _array1 = inputs[1]
                .as_array()
                .ok_or_else(|| "expected array input".to_string())?;
            if _array1.len() != 3 {
                return Err("input array length differs from circuit layout".into());
            }
            cells[1] = witgen_native::f17_from_nat(&parse_scalar(&_array1[0], "field17")?)?;
            cells[2] = witgen_native::f17_from_nat(&parse_scalar(&_array1[1], "field17")?)?;
            cells[3] = witgen_native::f17_from_nat(&parse_scalar(&_array1[2], "field17")?)?;
            cells[4] = witgen_native::f17_from_nat(&parse_scalar(&inputs[2], "field17")?)?;
            batch_fold_word::populate(&mut cells)?;
            Ok(
                serde_json::json!({"program": "batch_fold_word", "cells": cells.into_iter().map(witgen_native::f17_to_u64).collect::<Vec<_>>()}),
            )
        }
        _ => Err("unknown exported program".into()),
    }
}
