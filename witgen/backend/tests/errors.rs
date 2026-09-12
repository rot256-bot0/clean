use std::error::Error as StdError;
use witgen_native::Error;

fn standard_error<E: StdError + 'static>() {}

#[test]
fn errors_are_typed_and_implement_standard_error() {
    standard_error::<Error>();
    let result: witgen_native::Result<()> = Err(Error::DivisionByZero);
    assert!(matches!(result, Err(Error::DivisionByZero)));
    assert_eq!(Error::DivisionByZero.code(), "division_by_zero");
    assert_eq!(Error::DivisionByZero.to_string(), "zero divisor");
}

#[test]
fn underlying_errors_are_preserved_as_sources() {
    let integer = rug::Integer::from_str_radix("not-an-integer", 10).unwrap_err();
    let error = Error::from(integer);
    assert!(matches!(error, Error::ParseInteger(_)));
    assert!(error
        .source()
        .unwrap()
        .is::<rug::integer::ParseIntegerError>());

    let json = serde_json::from_str::<serde_json::Value>("{").unwrap_err();
    let error = Error::from(json);
    assert!(matches!(error, Error::Json(_)));
    assert!(error.source().unwrap().is::<serde_json::Error>());

    let error = Error::from(std::io::Error::new(
        std::io::ErrorKind::InvalidData,
        "bad input",
    ));
    assert!(matches!(error, Error::Io(_)));
    assert!(error.source().unwrap().is::<std::io::Error>());
}

#[test]
fn structured_payloads_survive_without_parsing_messages() {
    let error = Error::WitnessLength {
        expected: 3,
        actual: 2,
    };
    assert!(matches!(
        error,
        Error::WitnessLength {
            expected: 3,
            actual: 2
        }
    ));
    assert_eq!(error.code(), "witness_length");
    assert!(error.to_string().contains("expected 3, got 2"));
}
