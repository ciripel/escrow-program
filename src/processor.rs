//! Program state processor

use crate::{error::EscrowError, instruction::EscrowInstruction, state::Escrow};
use num_traits::FromPrimitive;
use solana_program::{
    account_info::{next_account_info, AccountInfo},
    decode_error::DecodeError,
    entrypoint::ProgramResult,
    msg,
    program::{invoke, invoke_signed},
    program_error::{PrintProgramError, ProgramError},
    program_pack::{IsInitialized, Pack},
    pubkey::Pubkey,
    sysvar::{rent::Rent, Sysvar},
};
use spl_token::state::Account as TokenAccount;

pub struct Processor;
impl Processor {
    pub fn process(
        program_id: &Pubkey,
        accounts: &[AccountInfo],
        instruction_data: &[u8],
    ) -> ProgramResult {
        let instruction = EscrowInstruction::unpack(instruction_data)?;

        match instruction {
            EscrowInstruction::InitEscrow { amount } => {
                msg!("Instruction: InitEscrow");
                Self::process_init_escrow(accounts, amount, program_id)
            }
            EscrowInstruction::Exchange { amount } => {
                msg!("Instruction: Exchange");
                Self::process_exchange(accounts, amount, program_id)
            }
        }
    }

    fn process_init_escrow(
        accounts: &[AccountInfo],
        amount: u64,
        program_id: &Pubkey,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let initializer = next_account_info(account_info_iter)?;

        if !initializer.is_signer {
            return Err(ProgramError::MissingRequiredSignature);
        }

        let temp_token_account = next_account_info(account_info_iter)?;

        let token_to_receive_account = next_account_info(account_info_iter)?;
        spl_token::check_program_account(token_to_receive_account.owner)?;

        let escrow_account = next_account_info(account_info_iter)?;
        let rent = Rent::get()?;

        if !rent.is_exempt(escrow_account.lamports(), escrow_account.data_len()) {
            return Err(EscrowError::NotRentExempt.into());
        }

        let mut escrow_info = Escrow::unpack_unchecked(&escrow_account.try_borrow_data()?)?;
        if escrow_info.is_initialized() {
            return Err(ProgramError::AccountAlreadyInitialized);
        }

        escrow_info.is_initialized = true;
        escrow_info.initializer_pubkey = *initializer.key;
        escrow_info.temp_token_account_pubkey = *temp_token_account.key;
        escrow_info.initializer_token_to_receive_account_pubkey = *token_to_receive_account.key;
        escrow_info.expected_amount = amount;

        Escrow::pack(escrow_info, &mut escrow_account.try_borrow_mut_data()?)?;

        let (pda, _bump_seed) = Pubkey::find_program_address(&[b"escrow"], program_id);

        let token_program = next_account_info(account_info_iter)?;
        spl_token::check_program_account(token_program.key)?;

        let owner_change_ix = spl_token::instruction::set_authority(
            token_program.key,
            temp_token_account.key,
            Some(&pda),
            spl_token::instruction::AuthorityType::AccountOwner,
            initializer.key,
            &[initializer.key],
        )?;

        msg!("Calling the token program to transfer token account ownership...");
        invoke(
            &owner_change_ix,
            &[
                temp_token_account.clone(),
                initializer.clone(),
                token_program.clone(),
            ],
        )?;

        Ok(())
    }

    fn process_exchange(
        accounts: &[AccountInfo],
        amount_expected_by_taker: u64,
        program_id: &Pubkey,
    ) -> ProgramResult {
        let account_info_iter = &mut accounts.iter();
        let taker = next_account_info(account_info_iter)?;

        if !taker.is_signer {
            return Err(ProgramError::MissingRequiredSignature);
        }

        let takers_sending_token_account = next_account_info(account_info_iter)?;
        spl_token::check_program_account(takers_sending_token_account.owner)?;

        let takers_token_to_receive_account = next_account_info(account_info_iter)?;
        spl_token::check_program_account(takers_token_to_receive_account.owner)?;

        let pdas_temp_token_account = next_account_info(account_info_iter)?;
        spl_token::check_program_account(pdas_temp_token_account.owner)?;
        let pdas_temp_token_account_info =
            TokenAccount::unpack(&pdas_temp_token_account.try_borrow_data()?)?;
        let (pda, bump_seed) = Pubkey::find_program_address(&[b"escrow"], program_id);

        if amount_expected_by_taker != pdas_temp_token_account_info.amount {
            return Err(EscrowError::ExpectedAmountMismatch.into());
        }

        let initializer = next_account_info(account_info_iter)?;

        let initializer_token_to_receive_account = next_account_info(account_info_iter)?;
        spl_token::check_program_account(initializer_token_to_receive_account.owner)?;

        let escrow_account = next_account_info(account_info_iter)?;
        let escrow_info = Escrow::unpack(&escrow_account.try_borrow_data()?)?;
        if escrow_info.temp_token_account_pubkey != *pdas_temp_token_account.key {
            return Err(ProgramError::InvalidAccountData);
        }

        if escrow_info.initializer_pubkey != *initializer.key {
            return Err(ProgramError::InvalidAccountData);
        }

        if escrow_info.initializer_token_to_receive_account_pubkey
            != *initializer_token_to_receive_account.key
        {
            return Err(ProgramError::InvalidAccountData);
        }

        let token_program = next_account_info(account_info_iter)?;
        spl_token::check_program_account(token_program.key)?;

        let transfer_to_initializer_ix = spl_token::instruction::transfer(
            token_program.key,
            takers_sending_token_account.key,
            initializer_token_to_receive_account.key,
            taker.key,
            &[taker.key],
            escrow_info.expected_amount,
        )?;
        msg!("Calling the token program to transfer tokens to the escrow's initializer...");
        invoke(
            &transfer_to_initializer_ix,
            &[
                takers_sending_token_account.clone(),
                initializer_token_to_receive_account.clone(),
                taker.clone(),
                token_program.clone(),
            ],
        )?;

        let pda_account = next_account_info(account_info_iter)?;

        let transfer_to_taker_ix = spl_token::instruction::transfer(
            token_program.key,
            pdas_temp_token_account.key,
            takers_token_to_receive_account.key,
            &pda,
            &[&pda],
            pdas_temp_token_account_info.amount,
        )?;
        msg!("Calling the token program to transfer tokens to the taker...");
        invoke_signed(
            &transfer_to_taker_ix,
            &[
                pdas_temp_token_account.clone(),
                takers_token_to_receive_account.clone(),
                pda_account.clone(),
                token_program.clone(),
            ],
            &[&[&b"escrow"[..], &[bump_seed]]],
        )?;

        let close_pdas_temp_acc_ix = spl_token::instruction::close_account(
            token_program.key,
            pdas_temp_token_account.key,
            initializer.key,
            &pda,
            &[&pda],
        )?;
        msg!("Calling the token program to close pda's temp account...");
        invoke_signed(
            &close_pdas_temp_acc_ix,
            &[
                token_program.clone(),
                pdas_temp_token_account.clone(),
                initializer.clone(),
                pda_account.clone(),
            ],
            &[&[&b"escrow"[..], &[bump_seed]]],
        )?;

        msg!("Closing the escrow account...");
        **initializer.lamports.borrow_mut() = initializer
            .lamports()
            .checked_add(escrow_account.lamports())
            .ok_or(EscrowError::AmountOverflow)?;
        **escrow_account.lamports.borrow_mut() = 0;
        *escrow_account.try_borrow_mut_data()? = &mut [];

        Ok(())
    }
}

impl PrintProgramError for EscrowError {
    fn print<E>(&self)
    where
        E: 'static + std::error::Error + DecodeError<E> + PrintProgramError + FromPrimitive,
    {
        match self {
            // 0
            EscrowError::InvalidInstruction => msg!("Error: Invalid instruction"),
            EscrowError::NotRentExempt => msg!("Lamport balance below rent-exempt threshold"),
            EscrowError::ExpectedAmountMismatch => {
                msg!("Expected amount of token to be paid by initializer is not correct")
            }
            EscrowError::AmountOverflow => msg!("Can't send coins back to owner"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::instruction::init_escrow;

    use super::*;

    use solana_program::{instruction::Instruction, program_error};
    use solana_sdk::account::{
        create_account_for_test, create_is_signer_account_infos, Account as SolanaAccount,
    };

    struct SyscallStubs {}
    impl solana_sdk::program_stubs::SyscallStubs for SyscallStubs {
        fn sol_log(&self, _message: &str) {}

        fn sol_invoke_signed(
            &self,
            _instruction: &Instruction,
            _account_infos: &[AccountInfo],
            _signers_seeds: &[&[&[u8]]],
        ) -> ProgramResult {
            Err(ProgramError::Custom(99)) // Just a custom error other than the ones already implemented in ProgramError
        }

        fn sol_get_clock_sysvar(&self, _var_addr: *mut u8) -> u64 {
            program_error::UNSUPPORTED_SYSVAR
        }

        fn sol_get_epoch_schedule_sysvar(&self, _var_addr: *mut u8) -> u64 {
            program_error::UNSUPPORTED_SYSVAR
        }

        #[allow(deprecated)]
        fn sol_get_fees_sysvar(&self, _var_addr: *mut u8) -> u64 {
            program_error::UNSUPPORTED_SYSVAR
        }

        fn sol_get_rent_sysvar(&self, var_addr: *mut u8) -> u64 {
            unsafe {
                *(var_addr as *mut _ as *mut Rent) = Rent::default();
            }
            solana_program::entrypoint::SUCCESS
        }
    }

    fn do_process_instruction(
        instruction: Instruction,
        accounts: Vec<&mut SolanaAccount>,
    ) -> ProgramResult {
        {
            use std::sync::Once;
            static ONCE: Once = Once::new();

            ONCE.call_once(|| {
                solana_sdk::program_stubs::set_syscall_stubs(Box::new(SyscallStubs {}));
            });
        }

        let mut meta = instruction
            .accounts
            .iter()
            .zip(accounts)
            .map(|(account_meta, account)| (&account_meta.pubkey, account_meta.is_signer, account))
            .collect::<Vec<_>>();

        let account_infos = create_is_signer_account_infos(&mut meta);
        Processor::process(&instruction.program_id, &account_infos, &instruction.data)
    }

    fn return_escrow_error_as_program_error() -> ProgramError {
        EscrowError::ExpectedAmountMismatch.into()
    }

    fn rent_sysvar() -> SolanaAccount {
        create_account_for_test(&Rent::default())
    }

    fn token_account_minimum_balance() -> u64 {
        Rent::default().minimum_balance(TokenAccount::get_packed_len())
    }

    fn escrow_minimum_balance() -> u64 {
        Rent::default().minimum_balance(Escrow::get_packed_len())
    }

    #[test]
    fn test_print_error() {
        let error = return_escrow_error_as_program_error();
        error.print::<EscrowError>();
    }

    #[test]
    #[should_panic(expected = "Custom(2)")]
    fn test_error_unwrap() {
        Err::<(), ProgramError>(return_escrow_error_as_program_error()).unwrap();
    }

    #[test]
    fn test_account_size() {
        assert_eq!(Escrow::get_packed_len(), 105);
    }

    #[test]
    fn test_pack_unpack() {
        // Escrow
        let check = Escrow {
            is_initialized: true,
            initializer_pubkey: Pubkey::new(&[2; 32]),
            temp_token_account_pubkey: Pubkey::new(&[3; 32]),
            initializer_token_to_receive_account_pubkey: Pubkey::new(&[4; 32]),
            expected_amount: 5,
        };

        let mut packed = vec![0; Escrow::get_packed_len() + 1];
        assert_eq!(
            Err(ProgramError::InvalidAccountData),
            Escrow::pack(check, &mut packed)
        );

        let mut packed = vec![0; Escrow::get_packed_len() - 1];
        assert_eq!(
            Err(ProgramError::InvalidAccountData),
            Escrow::pack(check, &mut packed)
        );

        let mut packed = vec![0; Escrow::get_packed_len()];
        Escrow::pack(check, &mut packed).unwrap();
        let expect = vec![
            1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
            2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
            3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
            4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 0, 0, 0, 0, 0, 0, 0,
        ];
        assert_eq!(packed, expect);
        let unpacked = Escrow::unpack(&packed).unwrap();
        assert_eq!(unpacked, check);
    }

    #[test]
    fn test_init_escrow() {
        let program_id = crate::id();
        let token_program_id = spl_token::id();
        let initializer_pubkey = Pubkey::new_unique();
        let mut initializer_account = SolanaAccount::default();

        let temp_token_account_pubkey = Pubkey::new_unique();
        let mut temp_token_account = SolanaAccount::new(
            token_account_minimum_balance(),
            TokenAccount::get_packed_len(),
            &token_program_id,
        );

        let initializer_token_to_receive_account_pubkey = Pubkey::new_unique();
        let mut initializer_token_to_receive_account = SolanaAccount::new(
            token_account_minimum_balance(),
            TokenAccount::get_packed_len(),
            &token_program_id,
        );

        let escrow_account_pubkey = Pubkey::new_unique();
        let mut escrow_account = SolanaAccount::new(100, Escrow::get_packed_len(), &program_id);

        let mut rent_sysvar = rent_sysvar();

        // escrow is not rent exempt
        assert_eq!(
            Err(EscrowError::NotRentExempt.into()),
            do_process_instruction(
                init_escrow(
                    &program_id,
                    &initializer_pubkey,
                    &temp_token_account_pubkey,
                    &initializer_token_to_receive_account_pubkey,
                    &escrow_account_pubkey,
                    20
                )
                .unwrap(),
                vec![
                    &mut initializer_account,
                    &mut temp_token_account,
                    &mut initializer_token_to_receive_account,
                    &mut escrow_account,
                    &mut rent_sysvar
                ]
            )
        );

        escrow_account.lamports = escrow_minimum_balance();

        // create new escrow
        do_process_instruction(
            init_escrow(
                &program_id,
                &initializer_pubkey,
                &temp_token_account_pubkey,
                &initializer_token_to_receive_account_pubkey,
                &escrow_account_pubkey,
                20,
            )
            .unwrap(),
            vec![
                &mut initializer_account,
                &mut temp_token_account,
                &mut initializer_token_to_receive_account,
                &mut escrow_account,
                &mut rent_sysvar,
            ],
        )
        .unwrap_or_default();

        // Do not allow to create twice
        assert_eq!(
            Err(ProgramError::AccountAlreadyInitialized.into()),
            do_process_instruction(
                init_escrow(
                    &program_id,
                    &initializer_pubkey,
                    &temp_token_account_pubkey,
                    &initializer_token_to_receive_account_pubkey,
                    &escrow_account_pubkey,
                    20,
                )
                .unwrap(),
                vec![
                    &mut initializer_account,
                    &mut temp_token_account,
                    &mut initializer_token_to_receive_account,
                    &mut escrow_account,
                    &mut rent_sysvar,
                ],
            )
        );
    }
}
