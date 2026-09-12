#[path = "../generated_custom/mod.rs"]
mod generated;
use std::io::{self, BufRead};

fn run(request: &serde_json::Value) -> witgen_native::Result<serde_json::Value> {
    let program = request
        .get("program")
        .ok_or(witgen_native::Error::MissingField("program"))?;
    let name = program
        .as_str()
        .ok_or(witgen_native::Error::InvalidInputType {
            expected: "program string",
        })?;
    let input = request
        .get("inputs")
        .ok_or(witgen_native::Error::MissingField("inputs"))?;
    let inputs = input
        .as_array()
        .ok_or(witgen_native::Error::InvalidInputType {
            expected: "inputs array",
        })?;
    generated::dispatch(name, inputs)
}

fn main() {
    for line in io::stdin().lock().lines() {
        let response = match line {
            Ok(text) => match serde_json::from_str::<serde_json::Value>(&text) {
                Ok(request) => run(&request),
                Err(error) => Err(witgen_native::Error::Json(error)),
            },
            Err(error) => Err(witgen_native::Error::Io(error)),
        };
        match response {
            Ok(value) => println!("{}", value),
            Err(error) => println!(
                "{}",
                serde_json::json!({"error": error.to_string(), "error_code": error.code()})
            ),
        }
    }
}
