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
    InvalidInstruction = 0,
    /// Lamport balance below rent-exempt threshold.
    #[error("Lamport balance below rent-exempt threshold")]
    NotRentExempt,
    /// Expected amount of token to be paid by initializer is not correct
    #[error("Expected amount of token to be paid by initializer is not correct")]
    ExpectedAmountMismatch,
    /// Can't send coins back to owner
    #[error("Can't send coins back to owner")]
    AmountOverflow,
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
