//! An Escrow program for the Solana blockchain

use solana_program::{entrypoint::ProgramResult, program_error::ProgramError, pubkey::Pubkey};

// .
// ├─ src
// │  ├─ lib.rs -> registering modules
// │  ├─ entrypoint.rs -> entrypoint to the program
// │  ├─ instruction.rs -> program API, (de)serializing instruction data
// │  ├─ processor.rs -> program logic
// │  ├─ state.rs -> program objects, (de)serializing state
// │  ├─ error.rs -> program specific errors
// ├─ .gitignore
// ├─ Cargo.lock
// ├─ Cargo.toml
// ├─ Xargo.toml

pub mod error;
pub mod instruction;
pub mod processor;
pub mod state;

#[cfg(not(feature = "no-entrypoint"))]
pub mod entrypoint;

solana_program::declare_id!("EWteUw3TUuQniV6pA3c4YjJSo2x6JzMMSfgia7m9gm49");

/// Checks that the supplied program ID is the correct one for EscrowProgram
pub fn check_program_account(escrow_program_id: &Pubkey) -> ProgramResult {
    if escrow_program_id != &id() {
        return Err(ProgramError::IncorrectProgramId);
    }
    Ok(())
}
