use core::{
    cell::RefCell,
    mem::MaybeUninit,
    ptr::{addr_of, from_ref, read_unaligned},
    slice::{self, from_raw_parts},
};

#[cfg(feature = "alloc")]
use alloc::{string::String, vec::Vec};

use crate::{DiskRead, DiskSeek, DiskWrite, SeekFrom, packed_field_accessors};

const GPT_HEADER_OFFSET: u64 = 0x200;
const GPT_SIG: &[u8; 8] = b"EFI PART";

#[derive(Clone, Copy, Debug)]
pub enum GptError {
    InvalidPartition,
    IoError,
    InvalidHeaderChecksum(u32, u32),
    InvalidSignature,
    NoSuchPartition,
    OutOfBounds,
    TableFull,
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

#[derive(Debug)]
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
    /// Returns this partition's sectors count.
    ///
    /// The _sector count_ is encoded using 32 bits, which limits the maximum partition size to 2TB.
    ///
    /// # Examples
    ///
    /// ```
    /// ```
    pub fn size(&self) -> u64 {
        self.last_lba - self.start_lba
    }

    pub fn is_used(&self) -> bool {
        self.type_guid != 0
    }

    #[cfg(feature = "alloc")]
    pub fn name(&self) -> Result<String, GptError> {
        unsafe {
            let name_buf = read_unaligned(addr_of!(self.partition_name));
            let filtered_buf: Vec<u16> = name_buf.into_iter().take_while(|&c| c != 0).collect();

            String::from_utf16(&filtered_buf).map_err(|_| GptError::InvalidPartition)
        }
    }

    packed_field_accessors!(type_guid, set_type_guid, u128);
    packed_field_accessors!(start_lba, set_start_lba, u64);
    packed_field_accessors!(last_lba, set_last_lba, u64);
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

pub struct Gpt<D, const S: u64 = 0x200>
where
    D: DiskRead,
{
    pub header: GptHeader,
    device_mapping: RefCell<D>,
}

impl<D, const S: u64> Gpt<D, S>
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
            device_mapping: RefCell::new(device_mapping),
        })
    }

    pub fn get_partition(&self, part_id: u32) -> Result<GptPartition, GptError> {
        self.iter_partitions()
            .nth(usize::try_from(part_id).map_err(|_| GptError::OutOfBounds)?)
            .ok_or(GptError::OutOfBounds)
    }

    pub fn iter_partitions(&self) -> GptPartitionsIterator<'_, D, S> {
        GptPartitionsIterator {
            table: self,
            cursor: 0,
            skip_empty: true,
        }
    }

    fn read_partition_entry(&self, part_id: u32) -> Result<GptPartition, GptError> {
        self.device_mapping
            .borrow_mut()
            .seek(SeekFrom::Start(self.partition_offset(part_id)))
            .map_err(|_| GptError::IoError)?;

        let part = unsafe {
            let mut uninit_part: MaybeUninit<GptPartition> = MaybeUninit::uninit();

            let bytes_read = self
                .device_mapping
                .borrow_mut()
                .read(slice::from_raw_parts_mut(
                    uninit_part.as_mut_ptr().cast(),
                    size_of::<GptPartition>(),
                ))
                .map_err(|_| GptError::IoError)?;

            if bytes_read != size_of::<GptPartition>() {
                return Err(GptError::OutOfBounds);
            }

            uninit_part.assume_init()
        };

        Ok(part)
    }

    fn iter_entries(&self) -> GptPartitionsIterator<'_, D, S> {
        GptPartitionsIterator {
            table: self,
            cursor: 0,
            skip_empty: false,
        }
    }

    fn partition_offset(&self, part_id: u32) -> u64 {
        self.header.partition_start_lba() * S
            + u64::from(part_id * self.header.partition_entry_size())
    }

    fn find_first_empty_slot(&self) -> Option<u32> {
        self.iter_entries()
            .position(|part| part.type_guid == 0)
            .map(|idx| u32::try_from(idx).ok())?
    }
}

impl<D> Gpt<D>
where
    D: DiskRead + DiskWrite + DiskSeek,
{
    pub fn remove_partition(&mut self, part_id: u32) -> Result<(), GptError> {
        self.get_partition(part_id)?;

        self.device_mapping
            .borrow_mut()
            .seek(SeekFrom::Start(self.partition_offset(part_id)))
            .map_err(|_| GptError::IoError)?;

        let bytes_written = self
            .device_mapping
            .borrow_mut()
            .write(&[0u8; size_of::<GptPartition>()])
            .map_err(|_| GptError::IoError)?;

        if bytes_written != size_of::<GptPartition>() {
            return Err(GptError::IoError);
        }

        Ok(())
    }

    pub fn append_partition(&mut self, new_part: GptPartition) -> Result<(), GptError> {
        let empty_idx = self.find_first_empty_slot().ok_or(GptError::TableFull)?;

        self.write_partition_entry(empty_idx, new_part)
    }

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

        self.write_partition_entry(idx, new_part)
    }

    fn write_partition_entry(
        &mut self,
        entry_id: u32,
        new_part: GptPartition,
    ) -> Result<(), GptError> {
        self.device_mapping
            .borrow_mut()
            .seek(SeekFrom::Start(self.partition_offset(entry_id)))
            .map_err(|_| GptError::IoError)?;

        let bytes_written = unsafe {
            self.device_mapping
                .borrow_mut()
                .write(slice::from_raw_parts(
                    addr_of!(new_part).cast(),
                    size_of::<GptPartition>(),
                ))
                .map_err(|_| GptError::IoError)?
        };

        if bytes_written != size_of::<GptPartition>() {
            return Err(GptError::IoError);
        }

        Ok(())
    }
}

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

#[cfg(test)]
mod tests {
    use std::{io::Cursor, vec::Vec};

    use super::Gpt;
    use base64::prelude::*;

    const GPT_DISK_DUMP: &str = "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA7gAAAAEAAAD/BwQAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAVapFRkkgUEFSVAAAAQBcAAAAWaj9XQAAAAABAAAAAAAAAP8HBAAAAAAAIgAAAAAAAADeBwQAAAAAABSWWrX/9bRAqBnTWMJ7e4QCAAAAAAAAAIAAAACAAAAAAVHo0AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAK89xg+DhHJHjnk9adhHfeTgKQeQ2MI7RriK9NAozzsNKAAAAAAAAAAnAAIAAAAAAAAAAAAAAAAAcABhAHIAdABfAGEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAArz3GD4OEckeOeT1p2Ed95EKe9HINBAxMkRpP2yjM5FYoAAIAAAAAACcABAAAAAAAAAAAAAAAAABwAGEAcgB0AF8AYgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=";

    #[test]
    pub fn parse_gpt_from_buf() {
        let gpt_dump = Cursor::new(BASE64_STANDARD.decode(GPT_DISK_DUMP).unwrap());
        let gpt: Gpt<Cursor<Vec<u8>>> = Gpt::parse_from_device(gpt_dump).unwrap();

        assert_eq!(gpt.header.partition_entries_count(), 128);
        assert_eq!(gpt.header.lba(), 1);
        assert_eq!(gpt.header.last_usable_lba(), 264158);
    }

    #[test]
    pub fn parse_gpt_partitions() {
        let gpt_dump = Cursor::new(BASE64_STANDARD.decode(GPT_DISK_DUMP).unwrap());
        let gpt: Gpt<Cursor<Vec<u8>>> = Gpt::parse_from_device(gpt_dump).unwrap();

        for part in gpt.iter_partitions() {
            assert!(part.is_used());
        }

        let partitions = gpt.iter_partitions().collect::<Vec<_>>();

        assert_eq!(partitions[0].name().unwrap(), "part_a");
        assert_eq!(partitions[1].name().unwrap(), "part_b");

        assert_eq!(partitions[0].start_lba(), 40);
        assert_eq!(partitions[1].start_lba(), 131112);
    }

    #[test]
    pub fn gpt_append_partition() {
        let gpt_dump = Cursor::new(BASE64_STANDARD.decode(GPT_DISK_DUMP).unwrap());
        let mut gpt: Gpt<Cursor<Vec<u8>>> = Gpt::parse_from_device(gpt_dump).unwrap();

        let mut part_a = gpt.get_partition(0).unwrap();
        part_a.set_start_lba(2727);

        gpt.append_partition(part_a).unwrap();

        assert_eq!(gpt.iter_partitions().count(), 3);

        let partitions = gpt.iter_partitions().collect::<Vec<_>>();

        assert_eq!(partitions[2].name().unwrap(), "part_a");

        assert_eq!(partitions[2].start_lba(), 2727);
    }

    #[test]
    pub fn gpt_update_partition() {
        let gpt_dump = Cursor::new(BASE64_STANDARD.decode(GPT_DISK_DUMP).unwrap());
        let mut gpt: Gpt<Cursor<Vec<u8>>> = Gpt::parse_from_device(gpt_dump).unwrap();

        let mut part_a = gpt.get_partition(0).unwrap();
        part_a.set_start_lba(2727);

        gpt.update_partition(0, part_a).unwrap();

        let partitions = gpt.iter_partitions().collect::<Vec<_>>();

        assert_eq!(partitions[0].name().unwrap(), "part_a");

        assert_eq!(partitions[0].start_lba(), 2727);
    }

    #[test]
    pub fn gpt_remove_partition() {
        let gpt_dump = Cursor::new(BASE64_STANDARD.decode(GPT_DISK_DUMP).unwrap());
        let mut gpt: Gpt<Cursor<Vec<u8>>> = Gpt::parse_from_device(gpt_dump).unwrap();

        gpt.remove_partition(0).unwrap();

        let partitions = gpt.iter_partitions().collect::<Vec<_>>();

        assert_eq!(partitions.len(), 1);

        assert_eq!(partitions[0].name().unwrap(), "part_b");
    }
}
