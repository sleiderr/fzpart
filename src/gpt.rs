//! This module provides tools for working with GUID Partition Tables (GPT), a modern
//! partitioning system used in UEFI-based systems. GPT replaces the older Master Boot Record (MBR)
//! format and is designed to support larger disks, more partitions, and better data reliability.
//!
//! A **GUID Partition Table (GPT)** is a partitioning scheme that stores metadata at both the start
//! and end of a disk. It supports:
//!
//! - Disks larger than 2TB.
//! - Up to 128 partitions (by default) with flexible sizes and boundaries.
//! - Metadata integrity through CRC32 checksums for headers and partition entries.
//! - Unique partition identification using GUIDs.
//! - Redundant metadata for recovery in case of corruption.
//!
//! ## Features
//!
//! This module provides a clean interface for reading, writing, and managing GPT structures.
//! It abstracts the low-level details of the GPT format, making it easier to build tools and utilities
//! for partition management. It provides:
//!
//! - Parsing, validation, and modification of GPT headers.
//! - **Partition Operations:**
//!   - Iterate over partitions, skipping unused or invalid entries.
//!   - Retrieve partitions by index.
//!   - Add, update, or delete partitions.
//! - **Backup Support:** Work with alternate (backup) GPT headers and partition tables.
//! - **Integrity Checks:** Detect overlapping partitions, validate checksums, and ensure table correctness.
//!
//! ## Compatibility
//!
//! This module works with any structure providing a storage device API through the implementation
//! of the [`DiskRead`] and [`DiskSeek`] traits, allowing it to interact with a wide variety of
//! storage backends, including raw block devices and virtual disks.
//!
//! If the `std` crate feature is enabled, [`DiskSeek`] and [`DiskRead`] are aliases to
//! [`std::io::Seek`] and [`std::io::Read`]. In a `no-std` environment, you need to provide your
//! own implementation of those two traits to provide a simple API to interact with the storage
//! devices.
//!
//! To access all of the functionalities of this module, the device-like structure should also
//! implement [`DiskWrite`], an alias to [`std::io::Write`] if the `std` feature is enabled.
//!
//! ## Example
//!
//! ```rust
//! use fzpart::{Gpt, GptPartition};
//! use std::io::Cursor;
//!
//! let mut device: Cursor<Vec<u8>> = Cursor::new(vec![0u8; 0x200 * 1024]);
//!
//! let mut gpt: Gpt<Cursor<Vec<u8>>, 0x200> = Gpt::new_on_device(device, 0, 1023).unwrap();
//!
//! gpt.header.set_first_usable_lba(400);
//!
//! assert_eq!(gpt.header.first_usable_lba(), 400);
//! assert_eq!(gpt.header.compute_checksum(), gpt.header.checksum());
//!
//! let mut part = GptPartition::default();
//! part.set_start_lba(400);
//! part.set_last_lba(800);
//! part.set_type_guid(1);
//!
//! gpt.append_partition(part).unwrap();
//!
//! assert_eq!(gpt.iter_partitions().count(), 1);
//! assert_eq!(gpt.get_partition(0).unwrap().start_lba(), 400);
//! ```

use core::{
    cell::RefCell,
    mem::{offset_of, MaybeUninit},
    slice,
};

#[cfg(feature = "alloc")]
use alloc::{string::String, vec::Vec};
use crc32fast::Hasher;
use zerocopy::{FromBytes, Immutable, IntoBytes};
use zerocopy_derive::{FromBytes, Immutable, IntoBytes};

use crate::{DiskRead, DiskSeek, DiskWrite, SeekFrom};

const GPT_HEADER_OFFSET: u64 = 0x200;
const GPT_SIG: &[u8; 8] = b"EFI PART";
const GPT_REVISION: u32 = 0x0001_0000;
const GPT_TABLE_SIZE: u32 = 1 << 17;

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
    ($field:ident, $field_setter:ident, $type:ty, $post_call:expr) => {
        #[must_use]
        pub fn $field(&self) -> $type {
            unsafe { core::ptr::read_unaligned(core::ptr::addr_of!(self.$field)) }
        }

        pub fn $field_setter(&mut self, value: $type) {
            unsafe { core::ptr::write_unaligned(core::ptr::addr_of_mut!(self.$field), value) }
            $post_call(self);
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

/// Represents any error that can occur when working with a [`Gpt`].
#[derive(Clone, Copy, Debug)]
pub enum GptError {
    /// A specific partition in the [`Gpt`] is invalid, or an invalid operation on a partition was
    /// attempted.
    ///
    /// Tuple containing the index of the partition which caused the error, as well as a
    /// description of the error using a [`GptPartitionError`] variant.
    InvalidPartition(u32, GptPartitionError),

    /// An I/O operation to the underlying device failed.
    IoError,

    /// The [`GptHeader`] checksum value is invalid.
    InvalidHeaderChecksum {
        /// Checksum value stored in the [`GptHeader`].
        expected: u32,

        /// Checksum value computed from the [`GptHeader`].
        actual: u32,
    },

    /// The partition table checksum is invalid.
    InvalidPartitionsChecksum {
        /// Partition table checksum value stored in the [`GptHeader`].
        expected: u32,

        /// Checksum value computed from the partition table entries.
        actual: u32,
    },

    /// The [`GptHeader`] signature is invalid.
    InvalidSignature,

    /// Attempted to access a partition entry that does not exist.
    NoSuchPartition,

    /// Attempted to access a partition entry outside of the bounds defined in the [`GptHeader`].
    OutOfBounds,

    /// The partition table is full and cannot accommodate more partitions.
    TableFull,

    /// Partitions in the table overlap with each other.
    OverlappingPartitions,
}

/// Represents any error than can occur when working with a [`GptPartition`].
#[derive(Clone, Copy, Debug)]
pub enum GptPartitionError {
    /// The *LBA* (_logical block address_) range for this partition is invalid.
    InvalidLbaRange,

    /// The partition name is invalid (should be at most 35 characters of valid UTF-16).
    InvalidName,
}

/// Represents the header of a [`Gpt`] (_GUID Partition Table_).
///
/// This header contains metadata about the partition table, and is replicated once on the storage
/// device (alternate header, located in the last sector).
///
/// # Examples
///
/// ```
/// use fzpart::Gpt;
/// use std::io::Cursor;
///
/// // Create a new device with 1024 512bytes sectors.
/// let mut device: Cursor<Vec<u8>> = Cursor::new(vec![0u8; 0x200 * 1024]);
///
/// let mut gpt: Gpt<Cursor<Vec<u8>>, 0x200> = Gpt::new_on_device(device, 0, 1023).unwrap();
///
/// gpt.header.set_first_usable_lba(400);
///
/// assert_eq!(gpt.header.first_usable_lba(), 400);
/// assert_eq!(gpt.header.compute_checksum(), gpt.header.checksum());
/// ```
#[derive(Clone, Debug, PartialEq, Eq, FromBytes, IntoBytes, Immutable)]
#[repr(packed(1), C)]
pub struct GptHeader {
    /// Identifies EFI-compatible partition table header.
    /// Should contain the string "EFI PART".
    signature: [u8; 8],

    /// Revision number for this header.
    revision: u32,

    /// Size of the header in bytes.
    size: u32,

    /// CRC32 checksum for the header.
    checksum: u32,

    reserved: [u8; 4],

    /// The LBA that contains this structure.
    lba: u64,

    /// The LBA of the alternate `GPT` header.
    alternate_lba: u64,

    /// First logical block that may be used by a partition.
    first_usable_lba: u64,

    /// Last logical block that may be used by a partition.
    last_usable_lba: u64,

    /// GUID used to identify the disk.
    guid: u128,

    /// Starting LBA of the GUID Partition Entry array.
    partition_start_lba: u64,

    /// Number of partitions entries in the GUID Partition Entry array.
    partition_entries_count: u32,

    /// Size in bytes of each entry in the GUID Partition Entry array.
    partition_entry_size: u32,

    /// CRC32 of the GUID Partition Entry array.
    partition_entries_checksum: u32,
}

assert_eq_size!(GptHeader, [u8; 0x5C]);
assert_eq_align!(GptHeader, u8);

impl GptHeader {
    /// Returns the checksum of the [`Gpt`] header part (_CRC32_).
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Gpt;
    /// use std::io::Cursor;
    ///
    /// // Create a new device with 1024 512bytes sectors.
    /// let mut device: Cursor<Vec<u8>> = Cursor::new(vec![0u8; 0x200 * 1024]);
    ///
    /// let mut gpt: Gpt<Cursor<Vec<u8>>, 0x200> = Gpt::new_on_device(device, 0, 1023).unwrap();
    ///
    /// assert_eq!(gpt.header.compute_checksum(), gpt.header.checksum());
    /// ```
    #[must_use]
    pub fn compute_checksum(&self) -> u32 {
        let chksum_offset = offset_of!(GptHeader, checksum);
        let bytes = self.as_bytes();

        let mut crc32_hasher = Hasher::new();

        crc32_hasher.update(&bytes[..chksum_offset]);
        crc32_hasher.update(&[0u8; size_of::<u32>()]);
        crc32_hasher.update(&bytes[chksum_offset + size_of::<u32>()..]);

        crc32_hasher.finalize()
    }

    fn update_checksum(&mut self) {
        self.checksum = self.compute_checksum();
    }

    fn is_valid(&self) -> Result<(), GptError> {
        if &self.signature != GPT_SIG {
            return Err(GptError::InvalidSignature);
        }

        let computed_checksum = self.compute_checksum();

        if computed_checksum != self.checksum {
            return Err(GptError::InvalidHeaderChecksum {
                expected: self.checksum,
                actual: computed_checksum,
            });
        }

        Ok(())
    }

    packed_field_accessors!(
        signature,
        set_signature,
        [u8; 8],
        GptHeader::update_checksum
    );
    packed_field_accessors!(revision, set_revision, u32, GptHeader::update_checksum);
    packed_field_accessors!(lba, set_lba, u64, GptHeader::update_checksum);
    packed_field_accessors!(
        alternate_lba,
        set_alternate_lba,
        u64,
        GptHeader::update_checksum
    );
    packed_field_accessors!(
        first_usable_lba,
        set_first_usable_lba,
        u64,
        GptHeader::update_checksum
    );
    packed_field_accessors!(
        last_usable_lba,
        set_last_usable_lba,
        u64,
        GptHeader::update_checksum
    );
    packed_field_accessors!(guid, set_guid, u128, GptHeader::update_checksum);
    packed_field_accessors!(checksum, u32);
    packed_field_accessors!(partition_start_lba, u64);
    packed_field_accessors!(partition_entries_count, u32);
    packed_field_accessors!(partition_entry_size, u32);
    packed_field_accessors!(partition_entries_checksum, u32, pub(self));
}

/// Represents an individual partition entry in a [`Gpt`] (_GUID Partition Table_).
///
/// Each entry describes a partition type, location, attributes and a human-readable name (UTF-16
/// encoded).
///
/// This structure directly maps the layout of a _GPT_ partition, as defined in the UEFI
/// specification, ensuring compatibility.
///
/// # Examples
///
/// ```
/// use fzpart::GptPartition;
///
/// let mut part = GptPartition::default();
///
/// part.set_start_lba(1024);
/// part.set_last_lba(4096);
/// part.set_name("my_part");
///
/// assert_eq!(part.name().unwrap(), "my_part");
/// assert_eq!(part.size(), 3072);
/// ```
#[derive(Clone, Copy, Debug, FromBytes, IntoBytes, Immutable)]
#[repr(packed(1), C)]
pub struct GptPartition {
    /// Defines the purpose and type of this partition.
    type_guid: u128,

    /// GUID unique for every partition entry.
    partition_guid: u128,

    /// Starting LBA of this partition.
    start_lba: u64,

    /// Last LBA of this partition.
    last_lba: u64,

    /// Partition's attributes bits.
    attributes: u64,

    /// Null-terminated string containing a human-readable name of this partition.
    partition_name: [u16; 36],
}

assert_eq_size!(GptPartition, [u8; 0x80]);
assert_eq_align!(GptPartition, u8);

impl GptPartition {
    /// Returns the size of this partition, in sectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::GptPartition;
    ///
    /// let mut part = GptPartition::default();
    ///
    /// part.set_start_lba(1024);
    /// part.set_last_lba(4096);
    ///
    /// assert_eq!(part.size(), 3072);
    /// ```
    pub fn size(&self) -> u64 {
        self.last_lba - self.start_lba
    }

    /// Returns `true` if this partition is being used.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::GptPartition;
    ///
    /// let mut part = GptPartition::default();
    ///
    /// assert!(!part.is_used());
    /// part.set_type_guid(1);
    /// assert!(part.is_used());
    /// ```
    pub fn is_used(&self) -> bool {
        self.type_guid != 0
    }

    /// Checks if this partition's structure is valid.
    ///
    /// If this partition cannot be used in a [`Gpt`] (invalid start / end LBAs, ...), returns an `Err`
    /// describing the issue.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::{GptPartition, gpt::GptPartitionError};
    ///
    /// let mut part = GptPartition::default();
    ///
    /// part.set_start_lba(4096);
    /// part.set_last_lba(1024);
    ///
    /// assert!(matches!(part.check_correctness(), Err(GptPartitionError::InvalidLbaRange)));
    ///
    /// part.set_start_lba(1024);
    /// part.set_last_lba(4096);
    ///
    /// assert!(part.check_correctness().is_ok());
    /// ```
    pub fn check_correctness(&self) -> Result<(), GptPartitionError> {
        if self.start_lba() > self.last_lba() {
            return Err(GptPartitionError::InvalidLbaRange);
        }

        Ok(())
    }

    /// Sets the partition name as a UTF-16 encoded string.
    ///
    /// This converts the provided UTF-8 string into UTF-16 encoding, required by the _UEFI_
    /// standards.
    ///
    /// # Errors
    ///
    /// Returns an `Err` if the provided name is too long (more than 35 characters).
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::GptPartition;
    ///
    /// let mut part = GptPartition::default();
    ///
    /// part.set_name("my_part").unwrap();
    ///
    /// assert_eq!(part.name().unwrap(), "my_part");
    /// ```
    #[cfg(feature = "alloc")]
    pub fn set_name(&mut self, name: &str) -> Result<(), GptPartitionError> {
        let mut utf16_encoding = name.encode_utf16().collect::<Vec<_>>();

        if utf16_encoding.len() >= 36 {
            return Err(GptPartitionError::InvalidName);
        }

        utf16_encoding.resize(36, 0);

        self.set_partition_name(utf16_encoding.try_into().unwrap());

        Ok(())
    }

    /// Returns the partition name as a UTF-8 encoded string.
    ///
    /// This converts the UTF-16 encoded partition name to UTF-8, after removing the trailing zero
    /// bytes.
    ///
    /// # Errors
    ///
    /// Returns an `Err` if the partition name is an invalid UTF-16 sequence.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::GptPartition;
    ///
    /// let mut part = GptPartition::default();
    ///
    /// part.set_name("my_part").unwrap();
    ///
    /// assert_eq!(part.name().unwrap(), "my_part");
    /// ```
    #[cfg(feature = "alloc")]
    pub fn name(&self) -> Result<String, GptPartitionError> {
        let name_buf = self.partition_name();
        let filtered_buf: Vec<u16> = name_buf.into_iter().take_while(|&c| c != 0).collect();

        String::from_utf16(&filtered_buf).map_err(|_| GptPartitionError::InvalidName)
    }

    packed_field_accessors!(type_guid, set_type_guid, u128);
    packed_field_accessors!(start_lba, set_start_lba, u64);
    packed_field_accessors!(last_lba, set_last_lba, u64);
    packed_field_accessors!(partition_name, set_partition_name, [u16; 36], pub(self));
}

impl Default for GptPartition {
    fn default() -> Self {
        Self {
            type_guid: Default::default(),
            partition_guid: Default::default(),
            start_lba: Default::default(),
            last_lba: Default::default(),
            attributes: Default::default(),
            partition_name: [0u16; 36],
        }
    }
}

/// Represents a **GUID Partition Table** (_GPT_).
///
/// The _GPT_ is a partitioning standard defined by the UEFI specifications, improving the
/// legacy _Master Boot Record_ ([`Mbr`](crate::Mbr)).
///
/// This provides a convenient way to interact with a GPT partitioned disk, and handles internaly
/// all raw reads / writes to and from the disk device, as well as ensuring consistenty inside of
/// the partition table.
///
/// It uses two generic parameters:
///
/// - `D` : A type representing a disk device API. It should implement at least [`DiskRead`] and
///         [`DiskSeek`], and [`DiskWrite`] is required to access all of the methods (especially those
///         requiring an update of the partition scheme).
///
/// - `S` : The size of a sector on the disk, in bytes. This supports any type of disk device, as
///         long as they can be accessed using standard APIs, and as such it cannot dynamically retrieve
///         the sector size. Therefore, it must be known at compile time (but the default value of `0x200`
///         should be correct in almost all usual cases).
///
/// # Examples
///
/// ```
/// use fzpart::{Gpt, GptPartition};
/// use std::io::Cursor;
///
/// let mut device: Cursor<Vec<u8>> = Cursor::new(vec![0u8; 0x200 * 1024]);
///
/// let mut gpt: Gpt<Cursor<Vec<u8>>, 0x200> = Gpt::new_on_device(device, 0, 1023).unwrap();
///
/// gpt.header.set_first_usable_lba(400);
///
/// assert_eq!(gpt.header.first_usable_lba(), 400);
/// assert_eq!(gpt.header.compute_checksum(), gpt.header.checksum());
///
/// let mut part = GptPartition::default();
/// part.set_start_lba(400);
/// part.set_last_lba(800);
/// part.set_type_guid(1);
///
/// gpt.append_partition(part).unwrap();
///
/// assert_eq!(gpt.iter_partitions().count(), 1);
/// assert_eq!(gpt.get_partition(0).unwrap().start_lba(), 400);
/// ```
pub struct Gpt<D, const S: u64 = 0x200>
where
    D: DiskRead + DiskSeek,
{
    pub header: GptHeader,
    device_mapping: RefCell<D>,
}

impl<D, const S: u64> Gpt<D, S>
where
    D: DiskRead + DiskSeek,
{
    /// Parses a `Gpt` structure from a disk device.
    ///
    /// The provided `device_mapping` must implement [`DiskRead`] and [`DiskSeek`], as this
    /// function will handle all reads from the device to properly load the `Gpt`.
    ///
    /// # Errors
    ///
    /// - [`GptError::IoError`]: if any error occured during an I/O operation to the disk.
    /// - [`GptError::InvalidHeaderChecksum`]: the _CRC32C_ header checksum is invalid (corrupted
    ///                                        `Gpt`)..
    /// - [`GptError::InvalidSignature`]: the [`GptHeader`] signature is invalid. The device might
    ///                                   not be partitioned using _GPT_, or the table is corrupted.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Gpt;
    /// use std::io::Cursor;
    ///
    /// let mut buf = [0u8; 0x200 * 1024];
    /// let mut device: Cursor<&mut [u8]> = Cursor::new(&mut buf);
    ///
    /// Gpt::<Cursor<&mut [u8]>, 0x200>::new_on_device(device, 1, 1023).unwrap();
    /// let gpt = Gpt::<Cursor<&mut [u8]>, 0x200>::parse_from_device(Cursor::new(&mut
    /// buf)).unwrap();
    ///
    /// assert!(gpt.check_table_correctness().is_ok());
    /// ```
    pub fn parse_from_device(mut device_mapping: D) -> Result<Self, GptError> {
        device_mapping
            .seek(SeekFrom::Start(GPT_HEADER_OFFSET))
            .map_err(|_| GptError::IoError)?;

        let mut buf = [0u8; size_of::<GptHeader>()];
        device_mapping
            .read(&mut buf)
            .map_err(|_| GptError::IoError)?;
        let header = GptHeader::read_from_bytes(&buf).map_err(|_| GptError::IoError)?;

        header.is_valid()?;

        let table = Gpt {
            header,
            device_mapping: RefCell::new(device_mapping),
        };

        Ok(table)
    }

    /// Returns an iterator over the valid partitions in the `Gpt`.
    ///
    /// The iterator goes through the partition entry array, skipping any unused or invalid
    /// partition. The indices in this iterator are consistent with the partitions
    /// returned by the [`Gpt::get_partition`] method.
    ///
    /// # Examples:
    ///
    /// ```
    /// use fzpart::{Gpt, GptPartition};
    /// use fzpart::gpt::GptError;
    /// use std::io::Cursor;
    ///
    /// let mut device: Cursor<Vec<u8>> = Cursor::new(vec![0u8; 0x200 * 1024]);
    /// let mut gpt: Gpt<Cursor<Vec<u8>>, 0x200> = Gpt::new_on_device(device, 0, 1023).unwrap();
    ///
    /// let mut part_a = GptPartition::default();
    /// part_a.set_start_lba(400);
    /// part_a.set_last_lba(800);
    /// part_a.set_type_guid(1);
    /// part_a.set_name("part_a");
    ///
    /// let mut part_b = GptPartition::default();
    /// part_b.set_start_lba(801);
    /// part_b.set_last_lba(920);
    /// part_b.set_type_guid(1);
    /// part_b.set_name("part_b");
    ///
    /// gpt.append_partition(part_a).unwrap();
    /// gpt.append_partition(part_b).unwrap();
    ///
    /// assert_eq!(gpt.iter_partitions().count(), 2);
    /// assert_eq!(gpt.iter_partitions().map(|part| part.name().unwrap()).collect::<Vec<_>>(),
    /// ["part_a", "part_b"]);
    /// ```
    pub fn iter_partitions(&self) -> GptPartitionsIterator<'_, D, S> {
        GptPartitionsIterator {
            table: self,
            cursor: 0,
            skip_empty: true,
        }
    }

    /// Retrieves a partition from the `Gpt` from its index in the partition array.
    ///
    /// Partitions are 0-indexed, and unused ones are skipped. This index matches the position of
    /// the partition in the iterator returned by the [`Gpt::iter_partitions`] method.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::{Gpt, GptPartition};
    /// use fzpart::gpt::GptError;
    /// use std::io::Cursor;
    ///
    /// let mut device: Cursor<Vec<u8>> = Cursor::new(vec![0u8; 0x200 * 1024]);
    /// let mut gpt: Gpt<Cursor<Vec<u8>>, 0x200> = Gpt::new_on_device(device, 0, 1023).unwrap();
    ///
    /// let mut part = GptPartition::default();
    /// part.set_start_lba(400);
    /// part.set_last_lba(800);
    /// part.set_type_guid(1);
    ///
    /// gpt.append_partition(part).unwrap();
    ///
    /// assert_eq!(gpt.get_partition(0).unwrap().start_lba(), 400);
    /// assert!(matches!(gpt.get_partition(1), None));
    /// ```
    pub fn get_partition(&self, part_id: u32) -> Option<GptPartition> {
        self.iter_partitions().nth(usize::try_from(part_id).ok()?)
    }

    /// Returns `Ok` if this _Gpt_ is correct (according to the _UEFI_ specifications).
    ///
    /// # Errors
    ///
    /// Returns an `Err` if this _Gpt_ is not usable, with:
    ///
    /// - [`GptError::InvalidHeaderChecksum`]: the _CRC32C_ header checksum is invalid (corrupted
    ///                                        `Gpt`).
    /// - [`GptError::InvalidPartitionsChecksum`]: the _CRC32C_ checksum of the partition entries array
    ///                                            is invalid (corrupted `Gpt`).
    /// - [`GptError::InvalidSignature`]: the [`GptHeader`] signature is invalid. The device might
    ///                                   not be partitioned using _GPT_, or the table is corrupted.
    /// - [`GptError::OverlappingPartitions`] : if two partitions range overlap (this check requires the
    ///                                         `alloc` crate feature).
    /// - [`GptError::InvalidPartition`]: if any individual partition has an issue (described by a
    ///                                   [`GptPartitionError`] variant).
    ///
    /// # Examples
    ///
    /// ```    
    /// use fzpart::Gpt;
    /// use std::io::Cursor;
    ///
    /// let mut buf = [0u8; 0x200 * 1024];
    /// let mut device: Cursor<&mut [u8]> = Cursor::new(&mut buf);
    ///
    /// let mut gpt = Gpt::<Cursor<&mut [u8]>, 0x200>::new_on_device(device, 1, 1023).unwrap();
    ///
    /// assert!(gpt.check_table_correctness().is_ok());
    /// ```
    pub fn check_table_correctness(&self) -> Result<(), GptError> {
        self.header.is_valid()?;

        let computed_checksum = self.compute_partitions_checksum();

        if computed_checksum != self.header.partition_entries_checksum {
            return Err(GptError::InvalidPartitionsChecksum {
                expected: self.header.partition_entries_checksum(),
                actual: computed_checksum,
            });
        }

        #[cfg(feature = "alloc")]
        {
            let overlappings =
                find_overlapping_partitions(self.iter_partitions().collect::<Vec<_>>());

            if !overlappings.is_empty() {
                return Err(GptError::OverlappingPartitions);
            }
        }

        for (part, idx) in self.iter_partitions().zip(0u32..) {
            part.check_correctness()
                .map_err(|err| GptError::InvalidPartition(idx, err))?;
        }

        Ok(())
    }

    fn update_checksums(&mut self) {
        let partitions_chksum = self.compute_partitions_checksum();
        self.header.partition_entries_checksum = partitions_chksum;

        let header_chksum = self.header.compute_checksum();
        self.header.checksum = header_chksum;
    }

    fn compute_partitions_checksum(&self) -> u32 {
        let mut crc32_hasher = Hasher::new();

        self.iter_entries()
            .for_each(|part| crc32_hasher.update(part.as_bytes()));

        crc32_hasher.finalize()
    }

    fn read_from_device<T>(&self, offset: u64) -> Result<T, GptError>
    where
        T: FromBytes,
    {
        let mut device = self.device_mapping.borrow_mut();
        device
            .seek(SeekFrom::Start(offset))
            .map_err(|_| GptError::IoError)?;

        if cfg!(feature = "alloc") {
            let mut buf = alloc::vec![0u8; size_of::<T>()];

            let read = device.read(&mut buf).map_err(|_| GptError::IoError)?;

            if read != size_of::<T>() {
                return Err(GptError::IoError);
            }

            T::read_from_bytes(&buf).map_err(|_| GptError::IoError)
        } else {
            unsafe {
                let mut uninit_data: MaybeUninit<T> = MaybeUninit::uninit();

                let read = device
                    .read(slice::from_raw_parts_mut(
                        uninit_data.as_mut_ptr().cast(),
                        size_of::<T>(),
                    ))
                    .map_err(|_| GptError::IoError)?;

                if read != size_of::<T>() {
                    return Err(GptError::IoError);
                }

                Ok(uninit_data.assume_init())
            }
        }
    }

    fn read_alternate(&self) -> Result<GptHeader, GptError> {
        self.read_from_device(S * self.header.alternate_lba())
    }

    #[cfg(feature = "alloc")]
    fn would_new_partitions_overlap(&self, new_part: Vec<GptPartition>) -> bool {
        let mut partitions = self.iter_partitions().collect::<Vec<_>>();
        partitions.extend(new_part);

        let overlappings = find_overlapping_partitions(partitions);

        !overlappings.is_empty()
    }

    fn read_partition_entry(&self, part_id: u32) -> Result<GptPartition, GptError> {
        if part_id >= self.header.partition_entry_size() {
            return Err(GptError::OutOfBounds);
        }

        let (primary, _) = self.partition_offset(part_id);

        self.read_from_device::<GptPartition>(primary)
    }

    fn iter_entries(&self) -> GptPartitionsIterator<'_, D, S> {
        GptPartitionsIterator {
            table: self,
            cursor: 0,
            skip_empty: false,
        }
    }

    fn partition_offset(&self, part_id: u32) -> (u64, u64) {
        let offset_in_table = u64::from(part_id * self.header.partition_entry_size());
        let primary_offset = self.header.partition_start_lba() * S + offset_in_table;

        let alternate_offset = S * self.header.alternate_lba()
            - u64::from(self.header.partition_entries_count() * self.header.partition_entry_size())
            + offset_in_table;

        (primary_offset, alternate_offset)
    }

    fn find_first_empty_slot(&self) -> Option<u32> {
        self.iter_entries()
            .position(|part| part.type_guid == 0)
            .map(|idx| u32::try_from(idx).ok())?
    }
}

impl<D, const S: u64> Gpt<D, S>
where
    D: DiskRead + DiskWrite + DiskSeek,
{
    /// Partitions the given device using a `GPT`, using the provided `header_lba` and `alternate_lba`
    /// locations to store the headers.
    ///
    /// The `alternate_lba` must be located in the last LBA of the device.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the `GPT` creation went wrong, with:
    ///
    /// - [`GptError::IoError`]: if any error occured during an I/O operation to the disk, or if
    ///                          the **[**`header_lba`, `alternate_lba`**]** bounds provided are
    ///                          invalid for this device.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::{Gpt, GptPartition};
    /// use std::io::Cursor;
    ///
    /// let mut device: Cursor<Vec<u8>> = Cursor::new(vec![0u8; 0x200 * 1024]);
    ///
    /// let mut gpt: Gpt<Cursor<Vec<u8>>, 0x200> = Gpt::new_on_device(device, 0, 1023).unwrap();
    ///
    /// assert!(gpt.check_table_correctness().is_ok());
    /// ```
    #[cfg(feature = "std")]
    pub fn new_on_device(device: D, header_lba: u64, alternate_lba: u64) -> Result<Self, GptError> {
        // TODO: create another function that takes the uuud as an argument to remove dependency on
        // std
        use uuid::Uuid;

        let first_usable_lba = 1 + header_lba + u64::from(GPT_TABLE_SIZE) / S;

        let last_usable_lba = alternate_lba - u64::from(GPT_TABLE_SIZE) / S - 1;

        if alternate_lba < 1 + u64::from(GPT_TABLE_SIZE) / S || first_usable_lba > last_usable_lba {
            return Err(GptError::IoError);
        }

        let header = GptHeader {
            signature: *GPT_SIG,
            revision: GPT_REVISION,
            size: u32::try_from(size_of::<GptHeader>()).expect("invalid gpt header size"),
            checksum: 0,
            reserved: [0u8; 4],
            lba: header_lba,
            alternate_lba,
            first_usable_lba,
            last_usable_lba,
            guid: Uuid::new_v4().to_u128_le(),
            partition_start_lba: header_lba + 1,
            partition_entries_count: GPT_TABLE_SIZE
                / u32::try_from(size_of::<GptPartition>()).expect("invalid gpt partition size"),
            partition_entry_size: u32::try_from(size_of::<GptPartition>())
                .expect("invalid gpt partition size"),
            partition_entries_checksum: 0,
        };

        let mut gpt = Self {
            header,
            device_mapping: RefCell::new(device),
        };

        gpt.update_checksums();
        gpt.write_header()?;
        gpt.write_alternate()?;

        Ok(gpt)
    }

    /// Restores the primary _GPT_ header and partition array from the backup.
    ///
    /// This can be attempted when the _GPT_ is corrupted, a backup of the entire structure is
    /// kept at the end of the device.
    ///
    /// # Errors
    ///
    /// Returns `Err` if the `GPT` restoration went wrong, or if the alternate structure is
    /// corrupted as well with:
    ///
    /// - [`GptError::IoError`]: if any error occured during an I/O operation to the disk
    /// - [`GptError::InvalidHeaderChecksum`]: the _CRC32C_ header checksum is invalid (corrupted
    ///                                        `Gpt`)..
    /// - [`GptError::InvalidSignature`]: the [`GptHeader`] signature is invalid. The device might
    ///                                   not be partitioned using _GPT_, or the table is corrupted.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::Gpt;
    /// use std::io::Cursor;
    ///
    /// let mut device: Cursor<Vec<u8>> = Cursor::new(vec![0u8; 0x200 * 1024]);
    ///
    /// let mut gpt: Gpt<Cursor<Vec<u8>>, 0x200> = Gpt::new_on_device(device, 0, 1023).unwrap();
    ///
    /// assert!(gpt.restore_from_alternate().is_ok());
    /// ```
    pub fn restore_from_alternate(&mut self) -> Result<(), GptError> {
        self.restore_main_header_from_alternate()?;
        self.restore_partitions_from_alternate()?;

        Ok(())
    }

    /// Removes a partition from the table.
    ///
    /// The `part_id` must match the indices used by the [`Gpt::iter_partitions`] iterator, same as
    /// with the [`Gpt::get_partition`] method.
    ///
    /// # Errors
    ///
    /// - [`GptError::IoError`]: if any error occured during an I/O operation to the disk.
    /// - [`GptError::OutOfBounds`]: if the provided `part_id` is bigger than the number of used
    ///                              partitions.
    /// - [`GptError::NoSuchPartition`]: there is no partition with the provided `part_id`.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::{Gpt, GptPartition};
    /// use fzpart::gpt::GptError;
    /// use std::io::Cursor;
    ///
    /// let mut device: Cursor<Vec<u8>> = Cursor::new(vec![0u8; 0x200 * 1024]);
    /// let mut gpt: Gpt<Cursor<Vec<u8>>, 0x200> = Gpt::new_on_device(device, 0, 1023).unwrap();
    ///
    /// let mut part = GptPartition::default();
    /// part.set_start_lba(400);
    /// part.set_last_lba(800);
    /// part.set_type_guid(1);
    /// gpt.append_partition(part).unwrap();
    ///
    /// assert!(gpt.remove_partition(0).is_ok());
    ///
    /// assert!(matches!(gpt.remove_partition(0), Err(GptError::NoSuchPartition)));
    /// ```
    pub fn remove_partition(&mut self, part_id: u32) -> Result<(), GptError> {
        self.get_partition(part_id)
            .ok_or(GptError::NoSuchPartition)?;

        let (primary, alternate) = self.partition_offset(part_id);

        self.write_to_device(primary, &[0u8; size_of::<GptPartition>()])?;
        self.write_to_device(alternate, &[0u8; size_of::<GptPartition>()])?;

        self.update_checksums();

        Ok(())
    }

    /// Appends a partition to the table.
    ///
    /// Uses the next available slot in the _GPT_ partition array.
    ///
    /// # Errors
    ///
    /// - [`GptError::IoError`]: if any error occured during an I/O operation to the disk.
    /// - [`GptError::TableFull`]: if the _GPT_ partition array is full. We do not support dynamic
    ///                            resizing of the _GPT_ to fit additional partitions.
    /// - [`GptError::OverlappingPartitions`]: The new partition range would overlap with an existing partition.
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::{Gpt, GptPartition};
    /// use fzpart::gpt::GptError;
    /// use std::io::Cursor;
    ///
    /// let mut device: Cursor<Vec<u8>> = Cursor::new(vec![0u8; 0x200 * 1024]);
    /// let mut gpt: Gpt<Cursor<Vec<u8>>, 0x200> = Gpt::new_on_device(device, 0, 1023).unwrap();
    ///
    /// let mut part = GptPartition::default();
    /// part.set_start_lba(400);
    /// part.set_last_lba(800);
    /// part.set_type_guid(1);
    ///
    /// gpt.append_partition(part).unwrap();
    ///
    /// assert!(gpt.get_partition(0).is_some())
    /// ```
    pub fn append_partition(&mut self, new_part: GptPartition) -> Result<(), GptError> {
        let empty_idx = self.find_first_empty_slot().ok_or(GptError::TableFull)?;

        #[cfg(feature = "alloc")]
        {
            if self.would_new_partitions_overlap(alloc::vec![new_part]) {
                return Err(GptError::OverlappingPartitions);
            }
        }

        self.write_partition_entry(empty_idx, &new_part)
    }

    /// Updates a partion entry in the _GPT_.
    ///
    /// The `part_id` must match the indices used by the [`Gpt::iter_partitions`] iterator, same as
    /// with the [`Gpt::get_partition`] method.
    ///
    /// # Errors
    ///
    /// - [`GptError::IoError`]: if any error occured during an I/O operation to the disk.
    /// - [`GptError::NoSuchPartition`]: there is no partition with the provided `part_id`.
    /// - [`GptError::OverlappingPartitions`]: The new partition range would overlap with an existing
    ///                                        partition (this check requires the `alloc` crate feature
    ///                                        to be enabled).
    ///
    /// # Examples
    ///
    /// ```
    /// use fzpart::{Gpt, GptPartition};
    /// use fzpart::gpt::GptError;
    /// use std::io::Cursor;
    ///
    /// let mut device: Cursor<Vec<u8>> = Cursor::new(vec![0u8; 0x200 * 1024]);
    /// let mut gpt: Gpt<Cursor<Vec<u8>>, 0x200> = Gpt::new_on_device(device, 0, 1023).unwrap();
    ///
    /// let mut part = GptPartition::default();
    /// part.set_start_lba(400);
    /// part.set_last_lba(800);
    /// part.set_type_guid(1);
    /// gpt.append_partition(part).unwrap();
    ///
    /// let mut part = gpt.get_partition(0).unwrap();
    /// part.set_start_lba(500);
    ///
    /// gpt.update_partition(0, part);
    ///
    /// assert_eq!(gpt.get_partition(0).unwrap().start_lba(), 500);
    /// ```
    pub fn update_partition(
        &mut self,
        part_id: u32,
        new_part: GptPartition,
    ) -> Result<(), GptError> {
        let (_, idx) = self
            .iter_entries()
            .zip(0u32..)
            .filter(|(part, _)| part.is_used())
            .nth(usize::try_from(part_id).map_err(|_| GptError::OutOfBounds)?)
            .ok_or(GptError::NoSuchPartition)?;
        new_part
            .check_correctness()
            .map_err(|err| GptError::InvalidPartition(part_id, err))?;

        #[cfg(feature = "alloc")]
        {
            let mut partitions = self
                .iter_partitions()
                .enumerate()
                .filter_map(|(idx, part)| {
                    if idx == usize::try_from(part_id).unwrap_or(0) {
                        None
                    } else {
                        Some(part)
                    }
                })
                .collect::<Vec<_>>();
            partitions.push(new_part);

            if !find_overlapping_partitions(partitions).is_empty() {
                return Err(GptError::OverlappingPartitions);
            }
        }
        self.write_partition_entry(idx, &new_part)
    }

    fn restore_partitions_from_alternate(&mut self) -> Result<(), GptError> {
        let (_, alternate_start) = self.partition_offset(0);

        for part_idx in 0..self.header.partition_entries_count() {
            self.write_partition_entry(
                part_idx,
                &self.read_from_device::<GptPartition>(
                    alternate_start
                        + u64::try_from(
                            size_of::<GptPartition>()
                                * usize::try_from(part_idx).map_err(|_| GptError::IoError)?,
                        )
                        .map_err(|_| GptError::IoError)?,
                )?,
            )?;
        }

        Ok(())
    }

    fn restore_main_header_from_alternate(&mut self) -> Result<(), GptError> {
        let alternate = self.read_alternate()?;
        alternate.is_valid()?;
        self.header = alternate;

        self.write_header()?;

        Ok(())
    }

    fn write_header(&mut self) -> Result<(), GptError> {
        self.write_to_device::<GptHeader>(S * self.header.lba(), &self.header.clone())
    }

    fn write_alternate(&mut self) -> Result<(), GptError> {
        self.write_to_device(S * self.header.alternate_lba(), &self.header.clone())
    }

    fn write_partition_entry(
        &mut self,
        entry_id: u32,
        new_part: &GptPartition,
    ) -> Result<(), GptError> {
        let (primary, alternate) = self.partition_offset(entry_id);
        self.write_to_device::<GptPartition>(primary, new_part)?;
        self.write_to_device::<GptPartition>(alternate, new_part)?;

        self.update_checksums();
        self.write_alternate()?;

        Ok(())
    }

    fn write_to_device<T>(&mut self, offset: u64, obj: &T) -> Result<(), GptError>
    where
        T: IntoBytes + Immutable,
    {
        self.device_mapping
            .borrow_mut()
            .seek(SeekFrom::Start(offset))
            .map_err(|_| GptError::IoError)?;

        let bytes_written = self
            .device_mapping
            .borrow_mut()
            .write(obj.as_bytes())
            .map_err(|_| GptError::IoError)?;

        if bytes_written != size_of::<T>() {
            return Err(GptError::IoError);
        }

        Ok(())
    }
}

/// An iterator over the partition entries in a [`Gpt`].
pub struct GptPartitionsIterator<'a, D, const S: u64>
where
    D: DiskRead + DiskSeek,
{
    table: &'a Gpt<D, S>,
    cursor: u32,
    skip_empty: bool,
}

impl<D, const S: u64> Iterator for GptPartitionsIterator<'_, D, S>
where
    D: DiskRead + DiskSeek,
{
    type Item = GptPartition;

    fn next(&mut self) -> Option<Self::Item> {
        let part = self.table.read_partition_entry(self.cursor).ok()?;
        self.cursor += 1;

        if self.skip_empty && part.type_guid == 0 {
            return self.next();
        }

        Some(part)
    }
}

#[cfg(feature = "alloc")]
fn find_overlapping_partitions(mut partitions: Vec<GptPartition>) -> Vec<Vec<GptPartition>> {
    partitions.sort_by_key(GptPartition::start_lba);

    let mut partitions_groups: Vec<Vec<GptPartition>> = Vec::with_capacity(partitions.len());
    let mut curr_group_end = 0;

    for part in partitions {
        if part.start_lba() > curr_group_end {
            curr_group_end = part.last_lba();
            partitions_groups.push(alloc::vec![part]);
            continue;
        }

        curr_group_end = core::cmp::max(part.last_lba(), curr_group_end);
        partitions_groups.last_mut().unwrap().push(part);
    }

    partitions_groups.retain(|grp| grp.len() > 1);

    partitions_groups
}

#[cfg(test)]
#[cfg(feature = "std")]
mod tests {
    use std::{io::Cursor, vec::Vec};

    use super::Gpt;

    const GPT_DUMP: &[u8] = include_bytes!("../tests/dummy_gpt.bin");

    #[test]
    pub fn parse_gpt_from_buf() {
        let gpt_dump = Cursor::new(GPT_DUMP);
        let gpt: Gpt<Cursor<&[u8]>> = Gpt::parse_from_device(gpt_dump).unwrap();

        assert_eq!(gpt.header.partition_entries_count(), 128);
        assert_eq!(gpt.header.lba(), 1);
        assert_eq!(gpt.header.last_usable_lba(), 264158);
    }

    #[test]
    pub fn gpt_update_header() {
        let gpt_dump = Cursor::new(GPT_DUMP);
        let mut gpt: Gpt<Cursor<&[u8]>> = Gpt::parse_from_device(gpt_dump).unwrap();

        gpt.header.set_last_usable_lba(27278);

        assert_eq!(gpt.header.last_usable_lba(), 27278);
        assert!(gpt.check_table_correctness().is_ok());
    }

    #[test]
    pub fn new_gpt_in_buf() {
        let mut buf = [0u8; 0x200 * 1024];
        let device: Cursor<&mut [u8]> = Cursor::new(&mut buf);

        let gpt_in_dev = Gpt::<Cursor<&mut [u8]>, 0x200>::new_on_device(device, 1, 1023).unwrap();
        assert!(gpt_in_dev.check_table_correctness().is_ok());
        let gpt =
            Gpt::<Cursor<&mut [u8]>, 0x200>::parse_from_device(Cursor::new(&mut buf)).unwrap();

        assert!(gpt.check_table_correctness().is_ok());
    }

    #[test]
    pub fn parse_gpt_partitions() {
        let gpt_dump = Cursor::new(GPT_DUMP);
        let gpt: Gpt<Cursor<&[u8]>> = Gpt::parse_from_device(gpt_dump).unwrap();

        for part in gpt.iter_partitions() {
            assert!(part.is_used());
        }

        let partitions = gpt.iter_partitions().collect::<Vec<_>>();

        assert_eq!(partitions[0].name().unwrap(), "part_a");
        assert_eq!(partitions[1].name().unwrap(), "part_b");

        assert_eq!(partitions[0].start_lba(), 40);
        assert_eq!(partitions[1].start_lba(), 131112);
        assert!(gpt.check_table_correctness().is_ok());
    }

    #[test]
    pub fn gpt_partitions_checksum() {
        let gpt_dump = Cursor::new(GPT_DUMP);
        let gpt: Gpt<Cursor<&[u8]>> = Gpt::parse_from_device(gpt_dump).unwrap();

        assert_eq!(
            gpt.compute_partitions_checksum(),
            gpt.header.partition_entries_checksum()
        );
        assert!(gpt.check_table_correctness().is_ok());
    }

    #[test]
    pub fn gpt_partition_overlapping_check() {
        let gpt_dump = Cursor::new(GPT_DUMP.iter().cloned().collect::<Vec<_>>());
        let mut gpt: Gpt<Cursor<Vec<u8>>> = Gpt::parse_from_device(gpt_dump).unwrap();

        let mut part_a = gpt.get_partition(0).unwrap();
        part_a.set_start_lba(2727);

        gpt.update_partition(0, part_a).unwrap();
        assert!(gpt.check_table_correctness().is_ok());
    }

    #[test]
    pub fn gpt_append_partition() {
        let gpt_dump = Cursor::new(GPT_DUMP.iter().cloned().collect::<Vec<_>>());
        let mut gpt: Gpt<Cursor<Vec<u8>>> = Gpt::parse_from_device(gpt_dump).unwrap();

        let mut part_a = gpt.get_partition(0).unwrap();
        part_a.set_start_lba(27272727);
        part_a.set_last_lba(27272728);

        gpt.append_partition(part_a).unwrap();

        assert_eq!(gpt.iter_partitions().count(), 3);

        let partitions = gpt.iter_partitions().collect::<Vec<_>>();

        assert_eq!(partitions[2].name().unwrap(), "part_a");

        assert_eq!(partitions[2].start_lba(), 27272727);

        assert_eq!(gpt.read_alternate().unwrap(), gpt.header);
        assert!(gpt.check_table_correctness().is_ok());
    }

    #[test]
    pub fn gpt_update_partition() {
        let gpt_dump = Cursor::new(GPT_DUMP.iter().cloned().collect::<Vec<_>>());
        let mut gpt: Gpt<Cursor<Vec<u8>>> = Gpt::parse_from_device(gpt_dump).unwrap();

        let mut part_a = gpt.get_partition(0).unwrap();
        part_a.set_start_lba(2727);
        part_a.set_name("frost").unwrap();

        gpt.update_partition(0, part_a).unwrap();

        let partitions = gpt.iter_partitions().collect::<Vec<_>>();

        assert_eq!(partitions[0].name().unwrap(), "frost");

        assert_eq!(partitions[0].start_lba(), 2727);

        assert_eq!(gpt.read_alternate().unwrap(), gpt.header);
        assert!(gpt.check_table_correctness().is_ok());
    }

    #[test]
    pub fn gpt_remove_partition() {
        let gpt_dump = Cursor::new(GPT_DUMP.iter().cloned().collect::<Vec<_>>());
        let mut gpt: Gpt<Cursor<Vec<u8>>> = Gpt::parse_from_device(gpt_dump).unwrap();

        gpt.remove_partition(0).unwrap();

        let partitions = gpt.iter_partitions().collect::<Vec<_>>();

        assert_eq!(partitions.len(), 1);

        assert_eq!(partitions[0].name().unwrap(), "part_b");
        assert!(gpt.check_table_correctness().is_ok());
    }

    #[test]
    pub fn gpt_alternate_partition_offset() {
        let gpt_dump = Cursor::new(GPT_DUMP);
        let gpt: Gpt<Cursor<&[u8]>> = Gpt::parse_from_device(gpt_dump).unwrap();

        let (primary, alternate) = gpt.partition_offset(0);

        assert_eq!(
            alternate - gpt.header.last_usable_lba() * 0x200,
            primary - 0x200
        );

        let (primary, alternate) = gpt.partition_offset(1);

        assert_eq!(
            alternate - gpt.header.last_usable_lba() * 0x200,
            primary - 0x200
        );
    }
}
