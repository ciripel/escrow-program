//! Program state processor

use crate::error::EscrowError;
use num_traits::FromPrimitive;
use solana_program::{decode_error::DecodeError, msg, program_error::PrintProgramError};

impl PrintProgramError for EscrowError {
    fn print<E>(&self)
    where
        E: 'static + std::error::Error + DecodeError<E> + PrintProgramError + FromPrimitive,
    {
        match self {
            // 0
            EscrowError::InvalidInstruction => msg!("Error: Invalid instruction"),
        }
    }
}
