#![no_std]

#[macro_use]
extern crate static_assertions;

mod gpt;
pub mod mbr;
pub use mbr::{Mbr, MbrInplace, MbrPartition};

pub use gpt::{Gpt, GptHeader};

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

#[derive(Clone, Copy, Debug)]
pub enum IoError {}

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

macro_rules! packed_field_accessors {
    ($field:ident, $type:ty) => {
        #[must_use]
        pub fn $field(&self) -> $type {
            unsafe { core::ptr::read_unaligned(core::ptr::addr_of!(self.$field)) }
        }
    };
    ($field:ident, $type:ty, $accq:vis) => {
        $accq fn $field(&self) -> $type {
            unsafe { core::ptr::read_unaligned(core::ptr::addr_of!(self.$field)) }
        }
    };
    ($field:ident, $field_setter:ident, $type:ty) => {
        #[must_use]
        pub fn $field(&self) -> $type {
            unsafe { core::ptr::read_unaligned(core::ptr::addr_of!(self.$field)) }
        }

        pub fn $field_setter(&mut self, value: $type) {
            unsafe { core::ptr::write_unaligned(core::ptr::addr_of_mut!(self.$field), value) }
        }
    };
    ($field:ident, $field_setter:ident, $type:ty, $accq:vis) => {
        $accq fn $field(&self) -> $type {
            unsafe { core::ptr::read_unaligned(core::ptr::addr_of!(self.$field)) }
        }

        $accq fn $field_setter(&mut self, value: $type) {
            unsafe { core::ptr::write_unaligned(core::ptr::addr_of_mut!(self.$field), value) }
        }
    };
}

pub(crate) use packed_field_accessors;
