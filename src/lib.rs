#![no_std]
#![cfg_attr(docsrs, feature(doc_auto_cfg))]

#[macro_use]
extern crate static_assertions;

pub mod mbr;
pub use mbr::{Mbr, MbrInplace, MbrPartition};

pub mod gpt;
pub use gpt::{Gpt, GptHeader, GptPartition};

extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "std")]
pub use std::io::Read as DiskRead;

#[cfg(feature = "std")]
pub use std::io::Write as DiskWrite;

#[cfg(feature = "std")]
pub use std::io::Seek as DiskSeek;

#[cfg(feature = "std")]
pub use std::io::SeekFrom;

#[cfg(not(feature = "std"))]
pub trait DiskRead {
    fn read(&mut self, but: &mut [u8]) -> Result<usize, IoError>;
}

#[cfg(not(feature = "std"))]
pub trait DiskWrite {
    fn write(&mut self, but: &[u8]) -> Result<usize, IoError>;
}

#[cfg(not(feature = "std"))]
pub enum SeekFrom {
    Start(u64),
    End(i64),
    Current(i64),
}

#[cfg(not(feature = "std"))]
pub trait DiskSeek {
    fn seek(&mut self, pos: SeekFrom) -> Result<u64, IoError>;
}
