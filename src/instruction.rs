//! Instruction types

use solana_program::{
    instruction::{AccountMeta, Instruction},
    program_error::ProgramError,
    pubkey::Pubkey,
};
use std::{convert::TryInto, mem::size_of};

use crate::{check_program_account, error::EscrowError::InvalidInstruction};

pub enum EscrowInstruction {
    /// Starts the trade by creating and populating an escrow account and transferring ownership of the given temp token account to the PDA
    ///
    ///
    /// Accounts expected:
    ///
    /// 0. `[signer]` The (Owner) account of the person (Alice) initializing the escrow
    /// 1. `[writable]` Temporary token (X) account that should be created prior to this instruction and owned by the initializer (Alice)
    /// 2. `[]` The initializer's (Alice) token account for the token (Y) they will receive should the trade go through
    /// 3. `[writable]` The escrow account, it will hold all necessary info about the trade.
    /// 4. `[]` The token program (SPL-token program)
    InitEscrow {
        /// The amount initializer (Alice) expects to receive of token Y for amount of X tokens
        amount: u64, // as a u64 because that's the max possible supply of a token
    },
    /// Accepts a trade
    ///
    ///
    /// Accounts expected:
    ///
    /// 0. `[signer]` The (Owner) account of the person (Bob) taking the trade
    /// 1. `[writable]` The taker's (Bob) token account for the token (Y) they send
    /// 2. `[writable]` The taker's (Bob) token account for the token (X) they will receive should the trade go through
    /// 3. `[writable]` The PDA's temp token account to get tokens (X) from and eventually close (Account 1. from InitEscrow)
    /// 4. `[writable]` The initializer's (Alice) main account to send their rent fees to (Account 0. from InitEscrow)
    /// 5. `[writable]` The initializer's (Alice) token account that will receive tokens (Account 2. from InitEscrow)
    /// 6. `[writable]` The escrow account holding the escrow info (Account 3. from InitEscrow)
    /// 7. `[]` The token program (SPL-token program)
    /// 8. `[]` The PDA account (?)
    Exchange {
        /// the amount the taker (Bob) expects to be paid in the other token (X)
        amount: u64, // as a u64 because that's the max possible supply of a token
    },
}

impl EscrowInstruction {
    /// Unpacks a byte buffer into a [EscrowInstruction](enum.EscrowInstruction.html).
    pub fn unpack(input: &[u8]) -> Result<Self, ProgramError> {
        let (tag, rest) = input.split_first().ok_or(InvalidInstruction)?;

        Ok(match tag {
            0 => Self::InitEscrow {
                amount: Self::unpack_amount(rest)?,
            },
            1 => Self::Exchange {
                amount: Self::unpack_amount(rest)?,
            },
            _ => return Err(InvalidInstruction.into()),
        })
    }

    /// Packs a [EscrowInstruction](enum.EscrowInstruction.html) into a byte buffer.
    pub fn pack(&self) -> Vec<u8> {
        let mut buf = Vec::with_capacity(size_of::<Self>());
        match self {
            &Self::InitEscrow { amount } => {
                buf.push(0);
                buf.extend_from_slice(&amount.to_le_bytes());
            }
            &Self::Exchange { amount } => {
                buf.push(1);
                buf.extend_from_slice(&amount.to_le_bytes());
            }
        };
        buf
    }

    fn unpack_amount(input: &[u8]) -> Result<u64, ProgramError> {
        let amount = input
            .get(..8)
            .and_then(|slice| slice.try_into().ok())
            .map(u64::from_le_bytes)
            .ok_or(InvalidInstruction)?;
        Ok(amount)
    }
}

// /// Creates a `InitEscrow` instruction.
pub fn init_escrow(
    escrow_program_id: &Pubkey,
    initializer_pubkey: &Pubkey,
    temp_token_account_pubkey: &Pubkey,
    token_to_receive_account_pubkey: &Pubkey,
    escrow_account_pubkey: &Pubkey,
    amount: u64,
) -> Result<Instruction, ProgramError> {
    check_program_account(escrow_program_id)?;
    let data = EscrowInstruction::InitEscrow { amount }.pack();

    let accounts = vec![
        AccountMeta::new(*initializer_pubkey, true),
        AccountMeta::new(*temp_token_account_pubkey, false),
        AccountMeta::new_readonly(*token_to_receive_account_pubkey, false),
        AccountMeta::new(*escrow_account_pubkey, false),
        AccountMeta::new_readonly(spl_token::id(), false),
    ];

    Ok(Instruction {
        program_id: *escrow_program_id,
        accounts,
        data,
    })
}
