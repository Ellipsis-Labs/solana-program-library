//! Program entrypoint

use {
    crate::{error::TokenError, processor::Processor},
    solana_nostd_entrypoint::{
        basic_panic_impl, entrypoint_nostd, noalloc_allocator,
        solana_program::{
            entrypoint::ProgramResult, program_error::PrintProgramError, pubkey::Pubkey,
        },
        NoStdAccountInfo,
    },
};

entrypoint_nostd!(process_instruction, 16);
noalloc_allocator!();
basic_panic_impl!();
fn process_instruction(
    program_id: &Pubkey,
    accounts: &[NoStdAccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    if let Err(error) =
        Processor::<NoStdAccountInfo>::process(program_id, accounts, instruction_data)
    {
        // catch the error so we can print it
        error.print::<TokenError>();
        return Err(error);
    }
    Ok(())
}
