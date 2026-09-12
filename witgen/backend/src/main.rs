mod generated;
use std::io::{self, BufRead};

fn run(request: &serde_json::Value) -> Result<serde_json::Value, String> {
    let name = request
        .get("program")
        .and_then(|v| v.as_str())
        .ok_or("missing program")?;
    let inputs = request
        .get("inputs")
        .and_then(|v| v.as_array())
        .ok_or("missing inputs")?;
    generated::dispatch(name, inputs)
}

fn main() {
    for line in io::stdin().lock().lines() {
        let response = match line {
            Ok(text) => match serde_json::from_str::<serde_json::Value>(&text) {
                Ok(request) => run(&request),
                Err(error) => Err(error.to_string()),
            },
            Err(error) => Err(error.to_string()),
        };
        match response {
            Ok(value) => println!("{}", value),
            Err(error) => println!("{}", serde_json::json!({"error": error})),
        }
    }
}
