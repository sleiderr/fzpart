use core::{
    cell::UnsafeCell,
    mem::MaybeUninit,
    ptr::{addr_of, from_ref, read_unaligned},
    slice::{self, from_raw_parts},
};

use alloc::string::String;

use crate::{DiskRead, DiskSeek, DiskWrite, SeekFrom, packed_field_accessors};

const GPT_HEADER_OFFSET: u64 = 0x200;
const GPT_SIG: &[u8; 8] = b"EFI PART";

#[derive(Clone, Copy, Debug)]
pub enum GptError {
    InvalidPartition,
    IoError,
    InvalidHeaderChecksum(u32, u32),
    InvalidSignature,
}

#[derive(Debug)]
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
    #[must_use]
    pub fn compute_checksum(&self) -> u32 {
        let chksum_field = self.checksum;

        unsafe {
            addr_of!(self.checksum).cast::<u32>().cast_mut().write(0);
            let hash = crc32fast::hash(from_raw_parts(
                from_ref(self).cast(),
                size_of::<GptHeader>(),
            ));
            addr_of!(self.checksum)
                .cast::<u32>()
                .cast_mut()
                .write(chksum_field);

            hash
        }
    }

    fn is_valid(&self) -> Result<(), GptError> {
        if &self.signature != GPT_SIG {
            return Err(GptError::InvalidSignature);
        }

        let expected_checksum = self.compute_checksum();

        if expected_checksum != self.checksum {
            return Err(GptError::InvalidHeaderChecksum(
                expected_checksum,
                self.checksum,
            ));
        }

        Ok(())
    }

    packed_field_accessors!(signature, set_signature, [u8; 8]);
    packed_field_accessors!(revision, set_revision, u32);
    packed_field_accessors!(lba, set_lba, u64);
    packed_field_accessors!(alternate_lba, set_alternate_lba, u64);
    packed_field_accessors!(first_usable_lba, set_first_usable_lba, u64);
    packed_field_accessors!(last_usable_lba, set_last_usable_lba, u64);
    packed_field_accessors!(guid, set_guid, u128);
    packed_field_accessors!(partition_start_lba, u64);
    packed_field_accessors!(partition_entries_count, u32);
    packed_field_accessors!(partition_entry_size, u32);
    packed_field_accessors!(partition_entries_checksum, u32, pub(self));
}

#[repr(packed(1), C)]
pub struct GptPartition {
    /// Defines the purpose and type of this partition.
    type_guid: u128,

    /// GUID unique for every partition entry.
    partition_guid: u128,

    /// Starting LBA of this partition.
    starting_lba: u64,

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
    /// Returns this partition's sectors count.
    ///
    /// The _sector count_ is encoded using 32 bits, which limits the maximum partition size to 2TB.
    ///
    /// # Examples
    ///
    /// ```
    /// ```
    pub fn size(&self) -> u64 {
        self.last_lba - self.starting_lba
    }

    pub fn is_used(&self) -> bool {
        self.type_guid != 0
    }

    pub fn name(&self) -> Result<String, GptError> {
        unsafe {
            let name_buf = read_unaligned(addr_of!(self.partition_name));
            String::from_utf16(&name_buf).map_err(|_| GptError::InvalidPartition)
        }
    }
}

impl Default for GptPartition {
    fn default() -> Self {
        Self {
            type_guid: Default::default(),
            partition_guid: Default::default(),
            starting_lba: Default::default(),
            last_lba: Default::default(),
            attributes: Default::default(),
            partition_name: [0u16; 36],
        }
    }
}

pub struct Gpt<D>
where
    D: DiskRead,
{
    pub header: GptHeader,
    device_mapping: UnsafeCell<D>,
}

impl<D> Gpt<D>
where
    D: DiskRead + DiskSeek,
{
    pub fn parse_from_device(mut device_mapping: D) -> Result<Self, GptError> {
        device_mapping
            .seek(SeekFrom::Start(GPT_HEADER_OFFSET))
            .map_err(|_| GptError::IoError)?;

        let header = unsafe {
            let mut uninit_header: MaybeUninit<GptHeader> = MaybeUninit::uninit();
            device_mapping
                .read(slice::from_raw_parts_mut(
                    uninit_header.as_mut_ptr().cast(),
                    size_of::<GptHeader>(),
                ))
                .map_err(|_| GptError::IoError)?;

            uninit_header.assume_init()
        };

        header.is_valid()?;

        Ok(Gpt {
            header,
            device_mapping: UnsafeCell::new(device_mapping),
        })
    }
}

impl<D> Gpt<D> where D: DiskRead + DiskWrite + DiskSeek {}

#[cfg(test)]
mod tests {
    use std::io::Cursor;

    use super::Gpt;
    use base64::prelude::*;

    const GPT_DISK_DUMP: &str = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA7gAAAAEAAAD/BwQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAVapFRkkgUEFSVAAAAQBcAAAAWaj9XQAAAAABAAAAAAAAAP8HBAAAAAAAIgAAAAAAAADeBwQAAAAAABSWWrX/9bRAqBnTWMJ7e4QCAAAAAAAAAIAAAACAAAAAAVHo0AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAK89xg+DhHJHjnk9adhHfeTgKQeQ2MI7RriK9NAozzsNKAAAAAAAAAAnAAIAAAAAAAAAAAAAAAAAcABhAHIAdABfAGEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAArz3GD4OEckeOeT1p2Ed95EKe9HINBAxMkRpP2yjM5FYoAAIAAAAAACcABAAAAAAAAAAAAAAAAABwAGEAcgB0AF8AYgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=";

    #[test]
    pub fn parse_gpt_from_buf() {
        let gpt_dump = Cursor::new(BASE64_STANDARD.decode(GPT_DISK_DUMP).unwrap());
        let gpt = Gpt::parse_from_device(gpt_dump).unwrap();

        assert_eq!(gpt.header.partition_entries_count(), 128);
        assert_eq!(gpt.header.lba(), 1);
        assert_eq!(gpt.header.last_usable_lba(), 264158);
    }
}
