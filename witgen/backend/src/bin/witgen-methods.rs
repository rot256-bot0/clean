#[allow(dead_code)]
#[path = "../generated_methods/module_0.rs"]
mod module_0;
#[allow(dead_code)]
#[path = "../generated_methods/module_1.rs"]
mod module_1;
#[allow(dead_code)]
#[path = "../generated_methods/module_10.rs"]
mod module_10;
#[allow(dead_code)]
#[path = "../generated_methods/module_11.rs"]
mod module_11;
#[allow(dead_code)]
#[path = "../generated_methods/module_12.rs"]
mod module_12;
#[allow(dead_code)]
#[path = "../generated_methods/module_13.rs"]
mod module_13;
#[allow(dead_code)]
#[path = "../generated_methods/module_14.rs"]
mod module_14;
#[allow(dead_code)]
#[path = "../generated_methods/module_15.rs"]
mod module_15;
#[allow(dead_code)]
#[path = "../generated_methods/shared_u64.rs"]
mod module_16;
#[allow(dead_code)]
#[path = "../generated_methods/module_2.rs"]
mod module_2;
#[allow(dead_code)]
#[path = "../generated_methods/module_3.rs"]
mod module_3;
#[allow(dead_code)]
#[path = "../generated_methods/module_4.rs"]
mod module_4;
#[allow(dead_code)]
#[path = "../generated_methods/module_5.rs"]
mod module_5;
#[allow(dead_code)]
#[path = "../generated_methods/module_6.rs"]
mod module_6;
#[allow(dead_code)]
#[path = "../generated_methods/module_7.rs"]
mod module_7;
#[allow(dead_code)]
#[path = "../generated_methods/module_8.rs"]
mod module_8;
#[allow(dead_code)]
#[path = "../generated_methods/module_9.rs"]
mod module_9;
use std::io::{self, BufRead};
fn execute(request: &serde_json::Value) -> witgen_native::Result<serde_json::Value> {
    let program = request["program"]
        .as_str()
        .ok_or(witgen_native::Error::InvalidInputType {
            expected: "program string",
        })?;
    let inputs = request["inputs"]
        .as_array()
        .ok_or(witgen_native::Error::InvalidInputType {
            expected: "input array",
        })?;
    match program {
        "field_0_native" => module_0::run_json(inputs),
        "field_0_nat_methods" => module_1::run_json(inputs),
        "field_1_native" => module_2::run_json(inputs),
        "field_1_nat_methods" => module_3::run_json(inputs),
        "field_2_native" => module_4::run_json(inputs),
        "field_2_nat_methods" => module_5::run_json(inputs),
        "secp_mixed_fields" => module_6::run_json(inputs),
        "secp_generator_affine_roundtrip" => module_7::run_json(inputs),
        "secp_from_affine" => module_8::run_json(inputs),
        "secp_to_affine" => module_9::run_json(inputs),
        "secp_affine_roundtrip" => module_10::run_json(inputs),
        "curve_eq" => module_11::run_json(inputs),
        "curve_msm" => module_12::run_json(inputs),
        "curve_msm_constructed" => module_13::run_json(inputs),
        "curve_const_generator" => module_14::run_json(inputs),
        "curve_const_identity" => module_15::run_json(inputs),
        "field.0.add" => module_16::run_json(0, inputs),
        "field.0.mul" => module_16::run_json(1, inputs),
        "field.0.square" => module_16::run_json(2, inputs),
        "field.1.add" => module_16::run_json(3, inputs),
        "field.1.mul" => module_16::run_json(4, inputs),
        "field.1.square" => module_16::run_json(5, inputs),
        "field.2.add" => module_16::run_json(6, inputs),
        "field.2.mul" => module_16::run_json(7, inputs),
        "field.2.square" => module_16::run_json(8, inputs),
        "field_0_u64_methods" => module_16::run_json(9, inputs),
        "field_1_u64_methods" => module_16::run_json(10, inputs),
        "field_2_u64_methods" => module_16::run_json(11, inputs),
        _ => Err(witgen_native::Error::UnknownProgram(program.to_owned())),
    }
}
fn main() {
    for line in io::stdin().lock().lines() {
        let result = line
            .map_err(witgen_native::Error::from)
            .and_then(|s| serde_json::from_str(&s).map_err(witgen_native::Error::from))
            .and_then(|x| execute(&x));
        let output = match result {
            Ok(v) => serde_json::json!({"ok":v}),
            Err(e) => serde_json::json!({"error":e.code(),"message":e.to_string()}),
        };
        println!("{}", output);
    }
}
