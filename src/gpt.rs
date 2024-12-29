use core::{
    cell::RefCell,
    mem::MaybeUninit,
    ptr::{addr_of, from_ref, read_unaligned},
    slice::{self, from_raw_parts},
};

#[cfg(feature = "alloc")]
use alloc::{string::String, vec::Vec};
use crc32fast::Hasher;

use crate::{DiskRead, DiskSeek, DiskWrite, SeekFrom, packed_field_accessors};

const GPT_HEADER_OFFSET: u64 = 0x200;
const GPT_SIG: &[u8; 8] = b"EFI PART";

#[derive(Clone, Copy, Debug)]
pub enum GptError {
    InvalidPartition(u32, GptPartitionError),
    IoError,
    InvalidHeaderChecksum(u32, u32),
    InvalidPartitionsChecksum(u32, u32),
    InvalidSignature,
    NoSuchPartition,
    OutOfBounds,
    TableFull,
    OverlappingPartitions,
}

#[derive(Clone, Copy, Debug)]
pub enum GptPartitionError {
    InvalidLbaRange,
    InvalidName,
}

#[derive(Clone, Debug, PartialEq, Eq)]
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

#[derive(Clone, Copy, Debug)]
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

    pub fn check_correctness(&self) -> Result<(), GptPartitionError> {
        if self.start_lba() > self.last_lba() {
            return Err(GptPartitionError::InvalidLbaRange);
        }

        Ok(())
    }

    #[cfg(feature = "alloc")]
    pub fn name(&self) -> Result<String, GptPartitionError> {
        unsafe {
            let name_buf = read_unaligned(addr_of!(self.partition_name));
            let filtered_buf: Vec<u16> = name_buf.into_iter().take_while(|&c| c != 0).collect();

            String::from_utf16(&filtered_buf).map_err(|_| GptPartitionError::InvalidName)
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

        let table = Gpt {
            header,
            device_mapping: RefCell::new(device_mapping),
        };

        Ok(table)
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

    pub fn compute_partitions_checksum(&self) -> u32 {
        let mut crc32_hasher = Hasher::new();

        unsafe {
            self.iter_entries().for_each(|part| {
                crc32_hasher.update(slice::from_raw_parts(
                    addr_of!(part).cast(),
                    size_of::<GptPartition>(),
                ))
            });
        }

        crc32_hasher.finalize()
    }

    pub fn update_checksums(&mut self) {
        let partitions_chksum = self.compute_partitions_checksum();
        let header_chksum = self.header.compute_checksum();

        self.header.checksum = header_chksum;
        self.header.partition_entries_checksum = partitions_chksum;
    }

    pub fn check_table_correctness(&self) -> Result<(), GptError> {
        self.header.is_valid()?;

        let expected_checksum = self.compute_partitions_checksum();

        if expected_checksum != self.header.partition_entries_checksum {
            return Err(GptError::InvalidPartitionsChecksum(
                expected_checksum,
                self.header.partition_entries_checksum(),
            ));
        }

        #[cfg(feature = "alloc")]
        {
            let overlappings =
                self.find_overlapping_partitions(self.iter_partitions().collect::<Vec<_>>());

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

    unsafe fn read_from_device<T>(&self, offset: u64) -> Result<T, GptError> {
        let mut device = self.device_mapping.borrow_mut();
        device
            .seek(SeekFrom::Start(offset))
            .map_err(|_| GptError::IoError)?;

        let data = unsafe {
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

            uninit_data.assume_init()
        };

        Ok(data)
    }

    fn read_alternate(&self) -> Result<GptHeader, GptError> {
        unsafe { self.read_from_device(S * self.header.alternate_lba()) }
    }

    fn would_new_partitions_overlap(&self, new_part: Vec<GptPartition>) -> bool {
        let mut partitions = self.iter_partitions().collect::<Vec<_>>();
        partitions.extend(new_part.into_iter());

        let overlappings = self.find_overlapping_partitions(partitions);

        !overlappings.is_empty()
    }

    #[cfg(feature = "alloc")]
    fn find_overlapping_partitions(
        &self,
        mut partitions: Vec<GptPartition>,
    ) -> Vec<Vec<GptPartition>> {
        partitions.sort_by(|part_a, part_b| part_a.start_lba().cmp(&part_b.start_lba()));

        let mut partitions_groups: Vec<Vec<GptPartition>> = Vec::with_capacity(partitions.len());
        let mut curr_group_end = 0;

        for part in partitions {
            if part.start_lba() >= curr_group_end {
                curr_group_end = part.last_lba();
                partitions_groups.push(alloc::vec![part]);
                continue;
            }

            if part.start_lba() < curr_group_end {
                curr_group_end = core::cmp::max(part.last_lba(), curr_group_end);
                partitions_groups.last_mut().unwrap().push(part);
            }
        }

        partitions_groups.retain(|grp| grp.len() > 1);

        partitions_groups
    }

    fn read_partition_entry(&self, part_id: u32) -> Result<GptPartition, GptError> {
        if part_id >= self.header.partition_entry_size() {
            return Err(GptError::OutOfBounds);
        }

        unsafe { self.read_from_device::<GptPartition>(self.partition_offset(part_id)) }
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

impl<D, const S: u64> Gpt<D, S>
where
    D: DiskRead + DiskWrite + DiskSeek,
{
    pub fn restore_main_header_from_alternate(&mut self) -> Result<(), GptError> {
        let alternate = self.read_alternate()?;
        self.header = alternate;

        self.write_header()?;

        Ok(())
    }

    fn write_header(&mut self) -> Result<(), GptError> {
        self.write_to_device::<GptHeader>(S * self.header.lba(), self.header.clone())
    }

    fn update_alternate(&mut self) -> Result<(), GptError> {
        self.write_to_device(S * self.header.alternate_lba(), self.header.clone())
    }

    pub fn remove_partition(&mut self, part_id: u32) -> Result<(), GptError> {
        self.get_partition(part_id)?;

        self.write_to_device(
            self.partition_offset(part_id),
            [0u8; size_of::<GptPartition>()],
        )?;

        self.update_checksums();

        Ok(())
    }

    pub fn append_partition(&mut self, new_part: GptPartition) -> Result<(), GptError> {
        let empty_idx = self.find_first_empty_slot().ok_or(GptError::TableFull)?;

        #[cfg(feature = "alloc")]
        {
            if self.would_new_partitions_overlap(alloc::vec![new_part]) {
                return Err(GptError::OverlappingPartitions);
            }
        }
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
        new_part
            .check_correctness()
            .map_err(|err| GptError::InvalidPartition(part_id, err))?;

        #[cfg(feature = "alloc")]
        {
            let mut partitions = self
                .iter_partitions()
                .enumerate()
                .filter_map(|(idx, part)| {
                    if idx != usize::try_from(part_id).unwrap_or(0) {
                        return Some(part);
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            partitions.push(new_part);

            if !self.find_overlapping_partitions(partitions).is_empty() {
                return Err(GptError::OverlappingPartitions);
            }
        }
        self.write_partition_entry(idx, new_part)
    }

    fn write_partition_entry(
        &mut self,
        entry_id: u32,
        new_part: GptPartition,
    ) -> Result<(), GptError> {
        self.write_to_device(self.partition_offset(entry_id), new_part)?;

        self.update_checksums();
        self.update_alternate()?;

        Ok(())
    }

    fn write_to_device<T>(&mut self, offset: u64, obj: T) -> Result<(), GptError> {
        self.device_mapping
            .borrow_mut()
            .seek(SeekFrom::Start(offset))
            .map_err(|_| GptError::IoError)?;

        let bytes_written = unsafe {
            self.device_mapping
                .borrow_mut()
                .write(slice::from_raw_parts(addr_of!(obj).cast(), size_of::<T>()))
                .map_err(|_| GptError::IoError)?
        };

        if bytes_written != size_of::<T>() {
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
    }

    #[test]
    pub fn gpt_partitions_checksum() {
        let gpt_dump = Cursor::new(GPT_DUMP);
        let gpt: Gpt<Cursor<&[u8]>> = Gpt::parse_from_device(gpt_dump).unwrap();

        assert_eq!(
            gpt.compute_partitions_checksum(),
            gpt.header.partition_entries_checksum()
        );
    }

    #[test]
    pub fn gpt_partition_overlapping_check() {
        let gpt_dump = Cursor::new(GPT_DUMP.iter().cloned().collect::<Vec<_>>());
        let mut gpt: Gpt<Cursor<Vec<u8>>> = Gpt::parse_from_device(gpt_dump).unwrap();

        let mut part_a = gpt.get_partition(0).unwrap();
        part_a.set_start_lba(2727);

        gpt.update_partition(0, part_a).unwrap();
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
    }

    #[test]
    pub fn gpt_update_partition() {
        let gpt_dump = Cursor::new(GPT_DUMP.iter().cloned().collect::<Vec<_>>());
        let mut gpt: Gpt<Cursor<Vec<u8>>> = Gpt::parse_from_device(gpt_dump).unwrap();

        let mut part_a = gpt.get_partition(0).unwrap();
        part_a.set_start_lba(2727);

        gpt.update_partition(0, part_a).unwrap();

        let partitions = gpt.iter_partitions().collect::<Vec<_>>();

        assert_eq!(partitions[0].name().unwrap(), "part_a");

        assert_eq!(partitions[0].start_lba(), 2727);

        assert_eq!(gpt.read_alternate().unwrap(), gpt.header);
    }

    #[test]
    pub fn gpt_remove_partition() {
        let gpt_dump = Cursor::new(GPT_DUMP.iter().cloned().collect::<Vec<_>>());
        let mut gpt: Gpt<Cursor<Vec<u8>>> = Gpt::parse_from_device(gpt_dump).unwrap();

        gpt.remove_partition(0).unwrap();

        let partitions = gpt.iter_partitions().collect::<Vec<_>>();

        assert_eq!(partitions.len(), 1);

        assert_eq!(partitions[0].name().unwrap(), "part_b");
    }
}
