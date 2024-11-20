use std::ops::DerefMut;

use solana_nostd_entrypoint::NoStdAccountInfo;
use solana_program::{
    account_info::AccountInfo as SolanaAccountInfo, program_error::ProgramError, pubkey::Pubkey,
};

pub trait IAccountInfo {
    fn lamports(&self) -> u64;
    fn key(&self) -> &Pubkey;
    fn owner(&self) -> &Pubkey;
    fn is_signer(&self) -> bool;
    fn is_writable(&self) -> bool;
    fn data_len(&self) -> usize;
    fn reassign(&self, new_owner: &Pubkey);
    fn realloc(&self, new_len: usize, is_mutable: bool) -> Result<(), ProgramError>;
    unsafe fn borrow_data(&self) -> &[u8];
    unsafe fn borrow_data_mut(&self) -> &mut [u8];
    unsafe fn borrow_mut_lamports(&self) -> &mut u64;
}

impl IAccountInfo for NoStdAccountInfo {
    fn lamports(&self) -> u64 {
        unsafe { *self.unchecked_borrow_lamports() }
    }

    fn key(&self) -> &Pubkey {
        NoStdAccountInfo::key(self)
    }

    fn owner(&self) -> &Pubkey {
        NoStdAccountInfo::owner(self)
    }

    fn is_signer(&self) -> bool {
        NoStdAccountInfo::is_signer(self)
    }

    fn is_writable(&self) -> bool {
        NoStdAccountInfo::is_writable(self)
    }

    fn data_len(&self) -> usize {
        NoStdAccountInfo::data_len(self)
    }

    unsafe fn borrow_mut_lamports(&self) -> &mut u64 {
        unsafe { NoStdAccountInfo::unchecked_borrow_mut_lamports(self) }
    }

    unsafe fn borrow_data(&self) -> &[u8] {
        unsafe { NoStdAccountInfo::unchecked_borrow_data(self) }
    }

    unsafe fn borrow_data_mut(&self) -> &mut [u8] {
        unsafe { NoStdAccountInfo::unchecked_borrow_mut_data(self) }
    }

    fn reassign(&self, new_owner: &Pubkey) {
        NoStdAccountInfo::reassign(self, new_owner)
    }

    fn realloc(&self, new_len: usize, is_mutable: bool) -> Result<(), ProgramError> {
        NoStdAccountInfo::realloc(self, new_len, is_mutable)
    }
}

impl<'a> IAccountInfo for SolanaAccountInfo<'a> {
    fn lamports(&self) -> u64 {
        SolanaAccountInfo::lamports(self)
    }

    fn key(&self) -> &Pubkey {
        &self.key
    }

    fn owner(&self) -> &Pubkey {
        &self.owner
    }

    fn is_signer(&self) -> bool {
        self.is_signer
    }

    fn is_writable(&self) -> bool {
        self.is_writable
    }

    fn data_len(&self) -> usize {
        self.data.borrow().len()
    }

    fn reassign(&self, new_owner: &Pubkey) {
        SolanaAccountInfo::assign(self, new_owner);
    }

    fn realloc(&self, new_len: usize, is_mutable: bool) -> Result<(), ProgramError> {
        SolanaAccountInfo::realloc(self, new_len, is_mutable)
    }

    unsafe fn borrow_data(&self) -> &[u8] {
        // SAFETY: The caller must ensure exclusive access to the data
        let data = self.data.borrow();
        core::slice::from_raw_parts(data.as_ptr(), data.len())
    }

    unsafe fn borrow_data_mut(&self) -> &mut [u8] {
        // SAFETY: The caller must ensure exclusive access to the data
        let mut data = self.data.borrow_mut();
        core::slice::from_raw_parts_mut(data.as_mut_ptr(), data.len())
    }

    /// super unsafe, but only used in tests
    unsafe fn borrow_mut_lamports(&self) -> &mut u64 {
        // SAFETY: The caller must ensure exclusive access to the lamports
        &mut *(core::ptr::from_mut(self.lamports.borrow_mut().deref_mut()))
    }
}
