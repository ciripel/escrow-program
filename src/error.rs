//! Error types

use num_derive::FromPrimitive;
use solana_program::{decode_error::DecodeError, program_error::ProgramError};
use thiserror::Error;

/// Errors that may be returned by the Escrow program.
#[derive(Clone, Debug, Error, FromPrimitive)]
pub enum EscrowError {
    // 0
    /// Invalid instruction number passed in.
    #[error("Invalid instruction")]
    InvalidInstruction,
    /// Lamport balance below rent-exempt threshold.
    #[error("Lamport balance below rent-exempt threshold")]
    NotRentExempt,
}

impl From<EscrowError> for ProgramError {
    fn from(e: EscrowError) -> Self {
        ProgramError::Custom(e as u32)
    }
}

impl<T> DecodeError<T> for EscrowError {
    fn type_of() -> &'static str {
        "Escrow Error"
    }
}
