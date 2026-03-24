#![cfg_attr(not(test), no_std)]

// See https://wiki.osdev.org/FAT

mod state_machine;
pub use state_machine::*;
mod read_file;
pub use read_file::*;
mod stream_file;
pub use stream_file::*;
mod bpb;
pub use bpb::*;
mod dir_entry;
pub use dir_entry::*;
