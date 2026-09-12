//! Typed failures shared by native providers, generated witnesses and the CLI.
use std::{error::Error as StdError, fmt, io};

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
#[non_exhaustive]
pub enum Error {
    NonCanonicalField { field: &'static str },
    NegativeNatural,
    DivisionByZero,
    WordOverflow,
    ParseInteger(rug::integer::ParseIntegerError),
    MissingField(&'static str),
    InvalidInputType { expected: &'static str },
    InputArity { expected: usize, actual: usize },
    InputLength { expected: usize, actual: usize },
    NonBooleanCell { slot: usize },
    CircuitAssumptions { circuit: &'static str },
    WitnessLength { expected: usize, actual: usize },
    UnknownProgram(String),
    UnknownField(u8),
    InvalidPointEncoding,
    Json(serde_json::Error),
    Io(io::Error),
}

impl Error {
    /// Stable discriminator for clients; messages are only for diagnostics.
    pub fn code(&self) -> &'static str {
        match self {
            Self::NonCanonicalField { .. } => "noncanonical_field",
            Self::NegativeNatural => "negative_natural",
            Self::DivisionByZero => "division_by_zero",
            Self::WordOverflow => "word_overflow",
            Self::ParseInteger(_) => "invalid_integer",
            Self::MissingField(_) => "missing_field",
            Self::InvalidInputType { .. } => "invalid_input_type",
            Self::InputArity { .. } => "input_arity",
            Self::InputLength { .. } => "input_length",
            Self::NonBooleanCell { .. } => "nonboolean_cell",
            Self::CircuitAssumptions { .. } => "circuit_assumptions",
            Self::WitnessLength { .. } => "witness_length",
            Self::UnknownProgram(_) => "unknown_program",
            Self::UnknownField(_) => "unknown_field",
            Self::InvalidPointEncoding => "invalid_point_encoding",
            Self::Json(_) => "invalid_json",
            Self::Io(_) => "io",
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NonCanonicalField { field } => {
                write!(f, "{field} value is not a canonical residue")
            }
            Self::NegativeNatural => f.write_str("Nat value must be nonnegative"),
            Self::DivisionByZero => f.write_str("zero divisor"),
            Self::WordOverflow => f.write_str("Nat value does not fit in u64"),
            Self::ParseInteger(source) => write!(f, "invalid decimal integer: {source}"),
            Self::MissingField(field) => write!(f, "missing required field: {field}"),
            Self::InvalidInputType { expected } => write!(f, "expected {expected} input"),
            Self::InputArity { expected, actual } => {
                write!(f, "input arity mismatch: expected {expected}, got {actual}")
            }
            Self::InputLength { expected, actual } => write!(
                f,
                "input array length mismatch: expected {expected}, got {actual}"
            ),
            Self::NonBooleanCell { slot } => write!(f, "non-Boolean input cell at slot {slot}"),
            Self::CircuitAssumptions { circuit } => {
                write!(f, "{circuit} circuit input assumptions failed")
            }
            Self::WitnessLength { expected, actual } => write!(
                f,
                "witness result length mismatch: expected {expected}, got {actual}"
            ),
            Self::UnknownProgram(program) => write!(f, "unknown exported program: {program}"),
            Self::UnknownField(id) => write!(f, "unknown field identity: {id}"),
            Self::InvalidPointEncoding => f.write_str("invalid secp256k1 point encoding"),
            Self::Json(source) => write!(f, "invalid JSON: {source}"),
            Self::Io(source) => write!(f, "input/output error: {source}"),
        }
    }
}

impl StdError for Error {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::ParseInteger(source) => Some(source),
            Self::Json(source) => Some(source),
            Self::Io(source) => Some(source),
            _ => None,
        }
    }
}

impl From<rug::integer::ParseIntegerError> for Error {
    fn from(source: rug::integer::ParseIntegerError) -> Self {
        Self::ParseInteger(source)
    }
}
impl From<serde_json::Error> for Error {
    fn from(source: serde_json::Error) -> Self {
        Self::Json(source)
    }
}
impl From<io::Error> for Error {
    fn from(source: io::Error) -> Self {
        Self::Io(source)
    }
}
