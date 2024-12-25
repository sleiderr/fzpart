//! MBR (_Master Boot Record_) partion table handling
//!
//! Legacy structure used to store partition information on hard drives, stored on the first
//! logical block of the drive.
//!
//! It limits the number of partition to 4 (without using _EBR_), and the partition sizes to 2 Terabytes at most.

use core::{mem::MaybeUninit, slice};

/// Size of the *MBR* header, in bytes.
pub const MBR_BOOTSTRAP_SIZE: usize = 446;

/// Magic boot signature for the *MBR* header (little-endian format).
pub const MBR_MAGIC_LE: u16 = 0xaa55;

/// The Master Boot Record is the first sector of a storage device that
/// contains important metadata, including bootstrap code, a partition
/// table, and a boot signature.
///
/// This structure provides methods for reading, writing, and manipulating
/// these fields.
///
/// # Examples
///
/// ```
/// use fzpart::Mbr;
///
/// let mut mbr = Mbr::new();
///
/// mbr.check_validity().unwrap();
/// let new_boot = [0xeb, 0xfe];
///
/// mbr.update_bootcode(&new_boot);
/// ```
#[derive(Debug)]
pub struct Mbr {
    bootstrap: [u8; MBR_BOOTSTRAP_SIZE],
    partitions: MbrPartitionTable,
    boot_sig: u16,
}

/// Error type when dealing with [`Mbr`].
#[derive(Debug)]
pub enum MbrError {
    /// A buffer too large was provided.    
    InvalidBufferSize,

    /// The signature field in this [`Mbr`] contains an invalid value.
    InvalidSignature,

    /// The provided bootcode was too large for the bootstrap field in this [`Mbr`].
    BootcodeTooLarge,
}

impl Mbr {
    /// Creates a new, empty (but valid) MBR.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    ///
    /// let mbr = Mbr::new();
    /// mbr.check_validity().unwrap();
    /// ```
    pub fn new() -> Self {
        Self {
            bootstrap: [0u8; MBR_BOOTSTRAP_SIZE],
            partitions: MbrPartitionTable::new(),
            boot_sig: MBR_MAGIC_LE,
        }
    }

    /// Reads the MBR from a raw bytes buffer.
    ///
    /// This creates a copy, and does not operate in-place.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    ///
    /// let mut mbr_buf = [0u8; 0x200];
    /// mbr_buf[0x1FF] = 0xaa;
    /// mbr_buf[0x1FE] = 0x55;
    ///
    /// Mbr::parse_from_buf(&mbr_buf).unwrap();
    /// ```
    pub fn parse_from_buf(buf: &[u8]) -> Result<Self, MbrError> {
        if buf.len() < size_of::<Mbr>() {
            return Err(MbrError::InvalidBufferSize);
        }

        let partition_table = unsafe {
            let mut uninit_partition_table = MaybeUninit::<MbrPartitionTable>::uninit();
            let part_buffer = slice::from_raw_parts_mut(
                uninit_partition_table.as_mut_ptr() as *mut u8,
                size_of::<MbrPartitionTable>(),
            );

            part_buffer.copy_from_slice(
                &buf[MBR_BOOTSTRAP_SIZE..MBR_BOOTSTRAP_SIZE + size_of::<MbrPartitionTable>()],
            );

            uninit_partition_table.assume_init()
        };

        let boot_sig = u16::from_le_bytes(
            buf[0x1FE..0x200]
                .try_into()
                .map_err(|_| MbrError::InvalidBufferSize)?,
        );

        let mbr = Mbr {
            bootstrap: buf[0..MBR_BOOTSTRAP_SIZE]
                .try_into()
                .map_err(|_| MbrError::InvalidBufferSize)?,
            partitions: partition_table,
            boot_sig,
        };

        mbr.check_validity()?;

        Ok(mbr)
    }

    /// Writes this MBR to a mutable bytes buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    ///
    /// let mut mbr_buf = [0u8; 0x200];
    ///
    /// let mbr = Mbr::new();
    /// mbr.write(&mut mbr_buf);
    /// ```
    pub fn write(&self, buf: &mut [u8]) -> Result<(), MbrError> {
        if buf.len() < size_of::<Mbr>() {
            return Err(MbrError::InvalidBufferSize);
        }

        unsafe {
            let mbr_buf = slice::from_raw_parts(self as *const Mbr as *const u8, size_of::<Mbr>());
            buf[0..size_of::<Mbr>()].copy_from_slice(mbr_buf);
        }

        Ok(())
    }

    /// Returns the bootstrap code contained in this MBR.
    ///
    /// The bootstrap code, is the executable code stored in the first 446 bytes
    /// of a Master Boot Record (MBR). This code is typically used to initialize
    /// the boot process on a system, though it may also be empty or contain
    /// custom data.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    ///
    /// let mbr = Mbr::new();
    ///
    /// assert!(mbr.bootcode() == [0u8; 446]);
    /// ```
    pub fn bootcode(&self) -> &[u8] {
        &self.bootstrap
    }

    ///
    /// Updates the bootstrap code in this MBR.
    ///
    /// This function replaces the existing bootstrap code with the provided data.
    /// If the provided `bootcode` exceeds the maximum size for bootstrap code
    /// (typically 446 bytes), the function returns an error.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    ///
    /// let mut mbr = Mbr::new();
    /// let bootcode = [0xeb, 0xfe];
    ///
    /// mbr.update_bootcode(&bootcode);
    /// ```
    pub fn update_bootcode(&mut self, bootcode: &[u8]) -> Result<(), MbrError> {
        if bootcode.len() > MBR_BOOTSTRAP_SIZE {
            return Err(MbrError::BootcodeTooLarge);
        }

        self.bootstrap.fill(0);
        self.bootstrap[..bootcode.len()].copy_from_slice(bootcode);

        Ok(())
    }

    /// Returns a reference to the partition table in this `Mbr`.
    ///
    /// The partition table contains entries describing up to four primary partitions
    /// in the Master Boot Record (_MBR_).
    ///
    /// # Notes
    ///
    /// This function provides read-only access to the partition table.
    /// To modify the partition table, use [`Mbr::partitions_mut`].
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    ///
    /// let mbr = Mbr::new();
    ///
    /// mbr.partitions();
    /// ```
    pub fn partitions(&self) -> &MbrPartitionTable {
        &self.partitions
    }

    /// Returns a mutable reference to the partition table in this MBR.
    ///
    /// The partition table contains entries describing up to four primary partitions
    /// in the Master Boot Record (MBR). This function allows you to modify those entries.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    ///
    /// let mbr = Mbr::new();
    ///
    /// mbr.partitions_mut();
    /// ```
    pub fn partitions_mut(&mut self) -> &mut MbrPartitionTable {
        &mut self.partitions
    }

    /// Checks if this MBR is valid (correct signature, ...).
    ///
    /// Returns an error describing what is wrong if it's not a valid MBR.
    ///
    /// # Examples
    ///
    /// ```
    /// let mbr = Mbr::new();
    ///
    /// mbr.check_validity().unwrap();
    /// ```
    pub fn check_validity(&self) -> Result<(), MbrError> {
        if !self.check_signature() {
            return Err(MbrError::InvalidSignature);
        }

        Ok(())
    }

    #[inline]
    fn check_signature(&self) -> bool {
        self.boot_sig == MBR_MAGIC_LE
    }
}

#[derive(Debug)]
pub struct MbrPartitionTable {
    partitions: [MbrPartition; 4],
}

impl MbrPartitionTable {
    fn new() -> Self {
        Self {
            partitions: [MbrPartition::default(); 4],
        }
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub struct MbrPartition {
    attributes: u8,
    chs_start: [u8; 3],
    part_type: u8,
    chs_last: [u8; 3],
    lba_start: u32,
    sectors_count: u32,
}

#[cfg(test)]
mod tests {
    use super::Mbr;
    extern crate std;
    use std::prelude::*;

    const DUMMY_MBR: [u8; 0x200] = [
        0x33, 0xed, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90,
        0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90,
        0x90, 0x90, 0x33, 0xed, 0xfa, 0x8e, 0xd5, 0xbc, 0x00, 0x7c, 0xfb, 0xfc, 0x66, 0x31, 0xdb,
        0x66, 0x31, 0xc9, 0x66, 0x53, 0x66, 0x51, 0x06, 0x57, 0x8e, 0xdd, 0x8e, 0xc5, 0x52, 0xbe,
        0x00, 0x7c, 0xbf, 0x00, 0x06, 0xb9, 0x00, 0x01, 0xf3, 0xa5, 0xea, 0x4b, 0x06, 0x00, 0x00,
        0x52, 0xb4, 0x41, 0xbb, 0xaa, 0x55, 0x31, 0xc9, 0x30, 0xf6, 0xf9, 0xcd, 0x13, 0x72, 0x16,
        0x81, 0xfb, 0x55, 0xaa, 0x75, 0x10, 0x83, 0xe1, 0x01, 0x74, 0x0b, 0x66, 0xc7, 0x06, 0xf3,
        0x06, 0xb4, 0x42, 0xeb, 0x15, 0xeb, 0x02, 0x31, 0xc9, 0x5a, 0x51, 0xb4, 0x08, 0xcd, 0x13,
        0x5b, 0x0f, 0xb6, 0xc6, 0x40, 0x50, 0x83, 0xe1, 0x3f, 0x51, 0xf7, 0xe1, 0x53, 0x52, 0x50,
        0xbb, 0x00, 0x7c, 0xb9, 0x04, 0x00, 0x66, 0xa1, 0xb0, 0x07, 0xe8, 0x44, 0x00, 0x0f, 0x82,
        0x80, 0x00, 0x66, 0x40, 0x80, 0xc7, 0x02, 0xe2, 0xf2, 0x66, 0x81, 0x3e, 0x40, 0x7c, 0xfb,
        0xc0, 0x78, 0x70, 0x75, 0x09, 0xfa, 0xbc, 0xec, 0x7b, 0xea, 0x44, 0x7c, 0x00, 0x00, 0xe8,
        0x83, 0x00, 0x69, 0x73, 0x6f, 0x6c, 0x69, 0x6e, 0x75, 0x78, 0x2e, 0x62, 0x69, 0x6e, 0x20,
        0x6d, 0x69, 0x73, 0x73, 0x69, 0x6e, 0x67, 0x20, 0x6f, 0x72, 0x20, 0x63, 0x6f, 0x72, 0x72,
        0x75, 0x70, 0x74, 0x2e, 0x0d, 0x0a, 0x66, 0x60, 0x66, 0x31, 0xd2, 0x66, 0x03, 0x06, 0xf8,
        0x7b, 0x66, 0x13, 0x16, 0xfc, 0x7b, 0x66, 0x52, 0x66, 0x50, 0x06, 0x53, 0x6a, 0x01, 0x6a,
        0x10, 0x89, 0xe6, 0x66, 0xf7, 0x36, 0xe8, 0x7b, 0xc0, 0xe4, 0x06, 0x88, 0xe1, 0x88, 0xc5,
        0x92, 0xf6, 0x36, 0xee, 0x7b, 0x88, 0xc6, 0x08, 0xe1, 0x41, 0xb8, 0x01, 0x02, 0x8a, 0x16,
        0xf2, 0x7b, 0xcd, 0x13, 0x8d, 0x64, 0x10, 0x66, 0x61, 0xc3, 0xe8, 0x1e, 0x00, 0x4f, 0x70,
        0x65, 0x72, 0x61, 0x74, 0x69, 0x6e, 0x67, 0x20, 0x73, 0x79, 0x73, 0x74, 0x65, 0x6d, 0x20,
        0x6c, 0x6f, 0x61, 0x64, 0x20, 0x65, 0x72, 0x72, 0x6f, 0x72, 0x2e, 0x0d, 0x0a, 0x5e, 0xac,
        0xb4, 0x0e, 0x8a, 0x3e, 0x62, 0x04, 0xb3, 0x07, 0xcd, 0x10, 0x3c, 0x0a, 0x75, 0xf1, 0xcd,
        0x18, 0xf4, 0xeb, 0xfd, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xec, 0x01, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0xf6, 0xe6, 0x6e, 0x08, 0x00, 0x00, 0x80, 0x01, 0x02, 0x00,
        0x00, 0xab, 0xff, 0xff, 0x40, 0x00, 0x00, 0x00, 0xc0, 0x4f, 0xa9, 0x00, 0x00, 0xab, 0xff,
        0xff, 0xef, 0xab, 0xff, 0xff, 0x00, 0x50, 0xa9, 0x00, 0x00, 0x58, 0x05, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x55, 0xaa,
    ];

    #[test]
    pub fn parse_standard_mbr_from_buffer() {
        Mbr::parse_from_buf(&DUMMY_MBR).unwrap();
    }

    #[test]
    pub fn write_mbr_to_buf() {
        let mut buf = [0u8; size_of::<Mbr>()];
        let mbr = Mbr::new();

        mbr.write(&mut buf).unwrap();

        Mbr::parse_from_buf(&buf).unwrap();
    }
}
