//! MBR (_Master Boot Record_) partion table handling
//!
//! Legacy structure used to store partition information on hard drives, stored on the first
//! logical block of the drive.
//!
//! It limits the number of partition to 4 (without using _EBR_), and the partition sizes to 2 Terabytes at most.

use core::{
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    ptr, slice,
};

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
#[repr(C, packed(1))]
pub struct Mbr {
    bootstrap: [u8; MBR_BOOTSTRAP_SIZE],

    /// Partition table for this `Mbr`.
    ///
    /// The partition table contains entries describing up to four primary partitions
    /// in the Master Boot Record (MBR).
    pub partitions: [MbrPartition; 4],

    boot_sig: u16,
}

/// Represents an in-place view of an MBR structure in a mutable buffer.
///
/// The `MbrInplace` struct allows you to work with an [`Mbr`] directly
/// within a raw buffer of bytes. This is useful for low-level operations
/// where the MBR resides in a contiguous memory buffer, such as a disk
/// sector or a memory-mapped file.
///
/// # Safety
///
/// The `MbrInplace` struct assumes the buffer contains valid data for an MBR.
/// Care must be taken when interpreting or modifying the buffer to avoid
/// undefined behavior.
pub struct MbrInplace<'a> {
    _bytes_buf: &'a mut [u8],
    mbr: &'a mut Mbr,
}

impl<'a> MbrInplace<'a> {
    /// Creates an `MbrInplace` instance from a mutable byte buffer.
    ///
    /// The buffer is assumed to contain a valid MBR structure.
    ///
    /// # Safety
    ///
    /// - The buffer must be large enough to hold an `Mbr` structure.
    ///
    /// - This function uses unsafe code to reinterpret the buffer as an `Mbr`.
    ///   Ensure the buffer contains valid data to avoid undefined behavior.
    pub fn from_buf(buf: &'a mut [u8]) -> Result<Self, MbrError> {
        if buf.len() < size_of::<Mbr>() {
            return Err(MbrError::InvalidBufferSize);
        }

        let mbr = unsafe { &mut *(buf.as_mut_ptr().cast::<Mbr>()) };

        let mbr_inplace = MbrInplace {
            _bytes_buf: buf,
            mbr,
        };

        mbr_inplace.check_validity()?;

        Ok(mbr_inplace)
    }
}

impl DerefMut for MbrInplace<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.mbr
    }
}

impl Deref for MbrInplace<'_> {
    type Target = Mbr;

    fn deref(&self) -> &Self::Target {
        self.mbr
    }
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
    InvalidPartition,
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
            partitions: [MbrPartition::default(); 4],
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
            let mut uninit_partition_table = MaybeUninit::<[MbrPartition; 4]>::uninit();
            let part_buffer = slice::from_raw_parts_mut(
                uninit_partition_table.as_mut_ptr().cast(),
                4 * size_of::<MbrPartition>(),
            );

            part_buffer.copy_from_slice(
                &buf[MBR_BOOTSTRAP_SIZE..MBR_BOOTSTRAP_SIZE + 4 * size_of::<MbrPartition>()],
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
            let mbr_buf = slice::from_raw_parts(ptr::from_ref(self).cast(), size_of::<Mbr>());
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

    /// Checks if this MBR is valid (correct signature, ...).
    ///
    /// Returns an error describing what is wrong if it's not a valid MBR.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    ///
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

impl Default for Mbr {
    fn default() -> Self {
        Self::new()
    }
}

/// Represents an individual partition entry in an MBR partition table.
///
/// The MBR partition table can contain up to four such entries, each describing
/// a primary partition's attributes, location, and size. This struct is designed
/// to match the exact layout of an MBR partition entry on disk.
///
/// # Examples
///
/// ```
/// use fzpart::Mbr;
/// use fzpart::mbr::MbrPartitionType;
///
/// let mut mbr = Mbr::new();
///
/// mbr.partitions[0].set_sectors_count(1024);
/// mbr.partitions[0].set_partition_type(MbrPartitionType::LinuxNative);
///
/// assert!(mbr.partitions[0].is_used());
/// ```
#[derive(Clone, Copy, Debug, Default)]
#[repr(C, packed(1))]
pub struct MbrPartition {
    attributes: u8,

    chs_start: [u8; 3],
    part_type: u8,
    chs_last: [u8; 3],

    start_lba: u32,
    sectors_count: u32,
}

impl MbrPartition {
    /// Returns `Some(true)` if this partition is flagged as _active_ (or bootable).
    ///
    /// Only one partition should be active in a [`Mbr`]
    ///
    /// # Errors
    ///
    /// This function will return [`MbrError::InvalidPartition`] if the partition contains an
    /// invalid value in its _active_ field.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    ///
    /// let mbr = Mbr::new();
    ///
    /// assert!(!mbr.partitions[0].is_active().unwrap());
    /// ```
    pub fn is_active(&self) -> Result<bool, MbrError> {
        match self.attributes {
            0 => Ok(false),
            (0x80..0x8F) => Ok(true),
            _ => Err(MbrError::InvalidPartition),
        }
    }

    /// Sets the _active_ (or bootable) flag for this partition.
    ///
    /// Only one partition should be active in a [`Mbr`]
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    ///
    /// let mut mbr = Mbr::new();
    /// mbr.partitions[0].set_active(true);
    ///
    /// assert!(mbr.partitions[0].is_active().unwrap());
    /// ```
    #[inline]
    pub fn set_active(&mut self, active: bool) {
        self.attributes = if active { 0x80 } else { 0 }
    }

    /// Returns `true` if this entry corresponds to a valid partition.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    /// use fzpart::mbr::MbrPartitionType;
    ///
    /// let mut mbr = Mbr::new();
    ///
    /// assert!(!mbr.partitions[0].is_used());
    ///
    /// mbr.partitions[0].set_sectors_count(1024);
    /// mbr.partitions[0].set_partition_type(MbrPartitionType::LinuxNative);
    ///
    /// assert!(mbr.partitions[0].is_used());
    /// ```
    pub fn is_used(&self) -> bool {
        self.part_type != 0 && self.sectors_count != 0
    }

    /// Returns the size of this partition, in sectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    ///
    /// let mbr = Mbr::new();
    ///
    /// assert_eq!(mbr.partitions[0].sectors_count(), 0);
    /// ```
    #[inline]
    pub fn sectors_count(&self) -> u32 {
        self.sectors_count
    }

    /// Sets the size of this partition, in sectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    ///
    /// let mut mbr = Mbr::new();
    ///
    /// mbr.partitions[0].set_sectors_count(1024);
    ///
    /// assert_eq!(mbr.partitions[0].sectors_count(), 1024);
    /// ```
    #[inline]
    pub fn set_sectors_count(&mut self, count: u32) {
        self.sectors_count = count;
    }

    /// Returns this partition's starting LBA.
    ///
    /// The _LBA_ is encoded using 32 bits, which limits the maximum partition size to 2TB.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    ///
    /// let mbr = Mbr::new();
    ///
    /// assert_eq!(mbr.partitions[0].start_lba(), 0);
    /// ```
    #[inline]
    pub fn start_lba(&self) -> u32 {
        self.start_lba
    }

    /// Sets this partition's starting LBA.
    ///
    /// The _LBA_ is encoded using 32 bits, which limits the maximum partition size to 2TB.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    ///
    /// let mut mbr = Mbr::new();
    ///
    /// mbr.partitions[0].set_start_lba(1024);
    ///
    /// assert_eq!(mbr.partitions[0].start_lba(), 1024);
    /// ```
    #[inline]
    pub fn set_start_lba(&mut self, lba: u32) {
        self.start_lba = lba;
    }

    /// Returns the [`MbrPartitionType`] for this partition.
    ///
    /// It is intended to specify the filesystem contained in this partition, but there is no clear
    /// standard.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    /// use fzpart::mbr::MbrPartitionType;
    ///
    /// let mbr = Mbr::new();
    ///
    /// assert!(matches!(mbr.partitions[0].partition_type(), MbrPartitionType::Empty));
    /// ```
    #[inline]
    pub fn partition_type(&self) -> MbrPartitionType {
        self.part_type.into()
    }

    /// Sets the [`MbrPartitionType`] for this partition.
    ///
    /// It is intended to specify the filesystem contained in this partition, but there is no clear
    /// standard.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Mbr;
    /// use fzpart::mbr::MbrPartitionType;
    ///
    /// let mut mbr = Mbr::new();
    ///
    /// mbr.partitions[0].set_partition_type(MbrPartitionType::LinuxNative);
    ///
    /// assert!(matches!(mbr.partitions[0].partition_type(), MbrPartitionType::LinuxNative));
    /// ```
    #[inline]
    pub fn set_partition_type(&mut self, part_type: MbrPartitionType) {
        self.part_type = part_type.into();
    }
}

/// Known partition IDs for various filesystems, used in MBR partition entries.
pub enum MbrPartitionType {
    Empty,
    DOSFat12,
    XenixRoot,
    XenixUsr,
    DOS3Fat16,
    Extended,
    DOS331Fat16,
    OS2IFS,
    NTFS,
    Fat32,
    Fat32LBA,
    EXFAT,
    DOSFat16LBA,
    ExtendedLBA,
    LinuxSwap,
    LinuxNative,
    LinuxExtended,
    LinuxLVM,
    BSDI,
    OpenBSD,
    MacOSX,
    MacOSXBoot,
    MacOSXHFS,
    LUKS,
    GPT,
    EFI,
    Unknown,
}

impl From<MbrPartitionType> for u8 {
    fn from(value: MbrPartitionType) -> Self {
        match value {
            MbrPartitionType::Empty => 0,
            MbrPartitionType::DOSFat12 => 1,
            MbrPartitionType::XenixRoot => 2,
            MbrPartitionType::XenixUsr => 3,
            MbrPartitionType::DOS3Fat16 => 4,
            MbrPartitionType::Extended => 5,
            MbrPartitionType::DOS331Fat16 => 6,
            MbrPartitionType::OS2IFS => 7,
            MbrPartitionType::NTFS => 7,
            MbrPartitionType::EXFAT => 7,
            MbrPartitionType::Fat32 => 0xB,
            MbrPartitionType::Fat32LBA => 0xC,
            MbrPartitionType::DOSFat16LBA => 0xE,
            MbrPartitionType::ExtendedLBA => 0xF,
            MbrPartitionType::LinuxSwap => 0x82,
            MbrPartitionType::LinuxNative => 0x83,
            MbrPartitionType::LinuxExtended => 0x85,
            MbrPartitionType::LinuxLVM => 0x8E,
            MbrPartitionType::BSDI => 0x9F,
            MbrPartitionType::OpenBSD => 0xA6,
            MbrPartitionType::MacOSX => 0xA8,
            MbrPartitionType::MacOSXBoot => 0xAB,
            MbrPartitionType::MacOSXHFS => 0xAF,
            MbrPartitionType::LUKS => 0xE8,
            MbrPartitionType::GPT => 0xEE,
            MbrPartitionType::EFI => 0xEF,
            MbrPartitionType::Unknown => 0xEA,
        }
    }
}

impl From<u8> for MbrPartitionType {
    fn from(value: u8) -> Self {
        match value {
            0 => Self::Empty,
            1 => Self::DOSFat12,
            2 => Self::XenixRoot,
            3 => Self::XenixUsr,
            4 => Self::DOS3Fat16,
            5 => Self::Extended,
            6 => Self::DOS331Fat16,
            7 => Self::NTFS,
            0xB => Self::Fat32,
            0xC => Self::Fat32LBA,
            0xE => Self::DOSFat16LBA,
            0xF => Self::ExtendedLBA,
            0x82 => Self::LinuxSwap,
            0x83 => Self::LinuxNative,
            0x85 => Self::LinuxExtended,
            0x8E => Self::LinuxLVM,
            0x9F => Self::BSDI,
            0xA6 => Self::OpenBSD,
            0xA8 => Self::MacOSX,
            0xAB => Self::MacOSXBoot,
            0xAF => Self::MacOSXHFS,
            0xE8 => Self::LUKS,
            0xEE => Self::GPT,
            0xEF => Self::EFI,
            _ => Self::Unknown,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::mbr::MbrPartitionType;

    use super::Mbr;
    extern crate std;
    use base64::prelude::*;

    const DUMMY_MBR: &str = "M+2QkJCQkJCQkJCQkJCQkJCQkJCQkJCQkJCQkJCQkJAz7fqO1bwAfPv8ZjHbZjHJZlNmUQZXjt2OxVK+AHy/AAa5AAHzpepLBgAAUrRBu6pVMckw9vnNE3IWgftVqnUQg+EBdAtmxwbzBrRC6xXrAjHJWlG0CM0TWw+2xkBQg+E/UffhU1JQuwB8uQQAZqGwB+hEAA+CgABmQIDHAuLyZoE+QHz7wHhwdQn6vOx76kR8AADogwBpc29saW51eC5iaW4gbWlzc2luZyBvciBjb3JydXB0Lg0KZmBmMdJmAwb4e2YTFvx7ZlJmUAZTagFqEInmZvc26HvA5AaI4YjFkvY27nuIxgjhQbgBAooW8nvNE41kEGZhw+geAE9wZXJhdGluZyBzeXN0ZW0gbG9hZCBlcnJvci4NCl6stA6KPmIEswfNEDwKdfHNGPTr/QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA7AEAAAAAAAD25m4IAACAAQIAAKv//0AAAADAT6kAAKv//++r//8AUKkAAFgFAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAVao=";

    #[test]
    pub fn parse_standard_mbr_from_buffer() {
        let mbr_bytes = BASE64_STANDARD.decode(DUMMY_MBR).unwrap();

        Mbr::parse_from_buf(&mbr_bytes).unwrap();
    }

    #[test]
    pub fn write_mbr_to_buf() {
        let mut buf = [0u8; size_of::<Mbr>()];
        let mbr = Mbr::new();

        mbr.write(&mut buf).unwrap();

        Mbr::parse_from_buf(&buf).unwrap();
    }

    #[test]
    pub fn read_partition_table() {
        let mbr_bytes = BASE64_STANDARD.decode(DUMMY_MBR).unwrap();

        let mbr = Mbr::parse_from_buf(&mbr_bytes).unwrap();

        assert!(mbr.partitions[0].is_active().unwrap());
        assert!(!mbr.partitions[1].is_active().unwrap());

        assert_eq!(mbr.partitions[0].sectors_count(), 11096000);
        assert_eq!(mbr.partitions[0].start_lba(), 64);

        assert_eq!(mbr.partitions[1].sectors_count(), 350208);
        assert_eq!(
            mbr.partitions[1].start_lba(),
            mbr.partitions[0].start_lba() + mbr.partitions[0].sectors_count
        );

        assert!(matches!(
            mbr.partitions[1].partition_type(),
            MbrPartitionType::EFI
        ));
    }
}
