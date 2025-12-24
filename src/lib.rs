#![cfg_attr(not(feature = "std"), no_std)]

// See https://wiki.osdev.org/FAT

use core::num::NonZero;

use bitflags::bitflags;
use zerocopy::{
    FromBytes, Immutable, IntoBytes, KnownLayout,
    little_endian::{U16, U32},
    transmute_ref,
};

/// BPB (BIOS Parameter Block)
#[derive(Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
#[repr(C)]
pub struct Bpb {
    instructions: [u8; 3],
    oem_identifier: [u8; 8],
    bytes_per_sector: U16,
    sectors_per_cluster: u8,
    reserved_sectors: U16,
    number_of_tables: u8,
    root_directory_entries: U16,
    /// If there are >65535 sectors, this will have a value of `0`, and you should read large sector count instead
    number_of_sectors: U16,
    /// https://en.wikipedia.org/wiki/Design_of_the_FAT_file_system#BPB20_OFS_0Ah
    media_descriptor_type: u8,
    /// Number of sectors per FAT. FAT12/FAT16 only.
    sectors_per_fat: U16,
    sectors_per_track: U16,
    heads_or_sides: U16,
    hidden_sectors: U32,
    large_sector_count: U32,
    extension_bytes: [u8; 0x1DC],
}

/// FAT 12 and FAT 16
#[derive(Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
#[repr(C)]
pub struct ExtendedBootRecordFat12 {
    todo: [u8; 0x1DC],
}

#[derive(Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
#[repr(C)]
pub struct ExtendedBootRecordFat32 {
    sectors_per_fat: U32,
    flags: U16,
    fat_version_number: U16,
    root_dir_cluster_number: U32,
    fs_info_sector_number: U16,
    backup_boot_sector_sector_number: U16,
    _reserved_0: [u8; 12],
    drive_number: u8,
    windows_nt_flags: u8,
    /// must be 0x28 or 0x29
    signature: u8,
    volume_id_serial_number: U32,
    volume_label_str: [u8; 11],
    /// System identifier string. Always "FAT32   ". The spec says never to trust the contents of this string for any use.
    system_identifier_str: [u8; 8],
    boot_code: [u8; 420],
    /// Bootable partition signature 0xAA55.
    bootable_partition_signature: U16,
}

#[derive(Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
#[repr(C)]
pub struct ExtendedBootRecordExFat {
    todo: [u8; 0x1DC],
}

#[derive(Debug)]
pub enum FataType {
    Fat12,
    Fat16,
    Fat32,
    ExFat,
}

#[derive(Debug)]
pub struct NextClusterError(u32);

impl Bpb {
    fn total_sectors(&self) -> Option<NonZero<u32>> {
        NonZero::new(self.number_of_sectors.into()).or(NonZero::new(self.large_sector_count.into()))
    }

    /// The number of sectors allocated to the root dir
    fn root_dir_sectors(&self) -> u16 {
        self.root_directory_entries
            .get()
            .div_ceil(self.bytes_per_sector.get())
    }

    fn sectors_per_fat(&self) -> u32 {
        if let Some(sectors_per_fat) = NonZero::new(self.sectors_per_fat.get()) {
            sectors_per_fat.get().into()
        } else {
            let fat32_info: &ExtendedBootRecordFat32 = transmute_ref!(&self.extension_bytes);
            fat32_info.sectors_per_fat.get()
        }
    }

    pub fn fat_type(&self) -> FataType {
        let data_sectors = self.total_sectors().unwrap().get()
            - (u32::from(self.reserved_sectors.get())
                + (u32::from(self.number_of_tables) * self.sectors_per_fat())
                + u32::from(self.root_dir_sectors()));
        let total_clusters = data_sectors / u32::from(self.sectors_per_cluster);
        if self.bytes_per_sector.get() == 0 {
            FataType::ExFat
        } else if total_clusters < 4085 {
            FataType::Fat12
        } else if total_clusters < 65525 {
            FataType::Fat16
        } else {
            FataType::Fat32
        }
    }

    pub fn root_dir_start_cluster(&self) -> u32 {
        match self.fat_type() {
            FataType::Fat12 | FataType::Fat16 => 0,
            FataType::Fat32 | FataType::ExFat => {
                let fat32_info: &ExtendedBootRecordFat32 = transmute_ref!(&self.extension_bytes);
                fat32_info.root_dir_cluster_number.get()
            }
        }
    }

    /// Returns the position in **bytes** of the start of a sector based on a sector number.
    pub fn cluster_start(&self, cluster_number: u32) -> u64 {
        let fat_start_sector = u32::from(self.reserved_sectors.get());
        let data_start_sector =
            fat_start_sector + u32::from(self.number_of_tables) * self.sectors_per_fat();
        let cluster_sector =
            data_start_sector + (cluster_number - 2) * u32::from(self.sectors_per_cluster);
        u64::from(cluster_sector) * u64::from(self.bytes_per_sector.get())
    }

    /// Use this to know how much to read
    pub fn bytes_per_cluster(&self) -> u64 {
        u64::from(self.sectors_per_cluster) * u64::from(self.bytes_per_sector.get())
    }

    /// Returns the position in bytes of where to read the cluster info
    pub fn cluster_info_start(&self, cluster_number: u32) -> u64 {
        let fat_start_bytes =
            u64::from(self.reserved_sectors.get()) * u64::from(self.bytes_per_sector.get());
        fat_start_bytes + cluster_number as u64 * self.cluster_info_size() as u64
    }

    /// Returns the number of bytes you need to read to get information about the next cluster
    pub fn cluster_info_size(&self) -> usize {
        match self.fat_type() {
            // Technically for FAT 12 you only need 1.5 bytes, but this means we need 2
            FataType::Fat12 | FataType::Fat16 => size_of::<U16>(),
            FataType::Fat32 => size_of::<U32>(),
            FataType::ExFat => todo!(),
        }
    }

    /// Panics if the size of the slice is not equal to [`Self::cluster_info_size`].
    /// https://en.wikipedia.org/wiki/Design_of_the_FAT_file_system#Cluster_values.
    pub fn next_cluster_number(
        &self,
        cluster_info: &[u8],
    ) -> Result<Option<u32>, NextClusterError> {
        match self.fat_type() {
            FataType::Fat12 => todo!("calculate if upper or lower 1.5 bytes should be used"),
            FataType::Fat16 => todo!(),
            FataType::Fat32 => {
                let info = u32::from_le_bytes(cluster_info.try_into().unwrap()) & 0xFFFFFFF;
                match info {
                    // End of chain marker
                    0x0000001 | 0xFFFFFF8..=0xFFFFFFF => Ok(None),
                    // Next cluster
                    0x0000002..=0xFFFFFEF => Ok(Some(info)),
                    // This cluster is reserved or bad
                    info => Err(NextClusterError(info)),
                }
            }
            FataType::ExFat => todo!(),
        }
    }
}

#[derive(Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
#[repr(C)]
pub struct DirSector {
    pub entries: [[u8; 32]; 16],
}

/// Directories on FAT12/16/32
#[derive(Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
#[repr(C)]
pub struct Fat12DirEntry {
    file_name: [u8; 11],
    attributes: u8,
    reserved_for_windows_nt: u8,
    /// Creation time in hundredths of a second, although the official FAT Specification from Microsoft says it is tenths of a second.
    /// Range 0-199 inclusive. Based on simple tests, Ubuntu16.10 stores either 0 or 100 while Windows7 stores 0-199 in this field.
    creation_time_within_second: u8,
    creation_time: U16,
    creation_date: U16,
    last_accessed_date: U16,
    /// The high 16 bits of this entry's first cluster number. For FAT 12 and FAT 16 this is always zero.
    cluster_number_high: [u8; 2],
    last_modification_time: U16,
    last_modification_date: U16,
    /// The low 16 bits of this entry's first cluster number. Use this number to find the first cluster for this entry.
    cluster_number_low: [u8; 2],
    size: U32,
}

#[derive(Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
#[repr(C)]
pub struct LongFileNameEntry {
    /// File names can be so long that they need multiple long file name entries
    /// The order number tells us the order of long file name entries, although they should already be sorted
    /// Bits 0-5 the sequence number
    /// Bit 6 indicates that this is the last long file name entry for this file
    /// Bit 7 is always 0
    order: u8,
    /// First 5 characters
    chars_0_4: [U16; 5],
    /// Attribute. Always equals 0x0F. (the long file name attribute)
    attribute: u8,
    /// Long entry type. Zero for name entries.
    long_entry_type: u8,
    /// Checksum generated of the short file name when the file was created.
    /// The short filename can change without changing the long filename in cases where the partition is mounted on a system which does not support long filenames.
    checksum: u8,
    /// The next 6, 2-byte characters of this entry.
    chars_5_10: [U16; 6],
    always_zero: [u8; 2],
    /// The final 2, 2-byte characters of this entry.
    chars_11_12: [U16; 2],
}

#[derive(Debug, Default)]
pub struct Date(u16);
#[derive(Debug, Default)]
pub struct Time(u16);

/// A Rusty representation of a directory entry
#[derive(Debug, Default)]
pub struct DirEntry {
    /// The name is supposed to be null-terminated, but here we store the length as a usize instead
    pub name: heapless::Vec<u16, 255>,
    pub read_only: bool,
    pub hidden: bool,
    pub system: bool,
    pub volume_id: bool,
    pub directory: bool,
    pub archive: bool,
    pub creation_date: Date,
    pub creation_time: Time,
    pub creation_time_within_second: u8,
    pub last_accessed_date: Date,
    pub last_modified_date: Date,
    pub last_modified_time: Time,
    pub first_cluster_number: u32,
    /// The size of the file in bytes.
    pub size: u32,
}

#[derive(Debug, Default)]
pub struct DirEntryParser {
    name: heapless::Vec<heapless::Vec<u16, 13>, 20>,
}

#[derive(Debug)]
pub enum ParseEntryOutput {
    KeepReadingToParseCurrentEntry(DirEntryParser),
    /// If the data is `None`, that means this entry was deleted
    KeepReadingToParseNextEntry(Option<DirEntry>),
    /// This entry doesn't exist and there are no more entries after this one
    DoneReadingEntries,
}

#[derive(Debug)]
pub enum ParseEntryError {
    /// File names can be max 255 chars
    /// There can be max 20 long file name entries (each entry can have up to 13 chars)
    /// This erorr means there were >20 long file name entries
    LfnOverflow,
    /// This error means that although there were <=20 long file name entries, their total chars was >255
    NameOverflow,
}

bitflags! {
    pub struct DirEntryAttributes: u8 {
        const READ_ONLY = 0x1;
        const HIDDEN = 0x2;
        const SYSTEM = 0x04;
        const VOLUME_ID = 0x08;
        const DIRECTORY = 0x10;
        const ARCHIVE = 0x20;
    }
}

impl DirEntryParser {
    pub fn parse_entry(
        mut self,
        entry_bytes: &[u8; 32],
    ) -> Result<ParseEntryOutput, ParseEntryError> {
        Ok({
            // https://people.cs.umass.edu/~liberato/courses/2019-spring-compsci365/lecture-notes/11-fats-and-directory-entries/
            let entry: &Fat12DirEntry = transmute_ref!(entry_bytes);
            let attributes = DirEntryAttributes::from_bits_retain(entry.attributes);
            if attributes.contains(
                DirEntryAttributes::READ_ONLY
                    | DirEntryAttributes::HIDDEN
                    | DirEntryAttributes::SYSTEM
                    | DirEntryAttributes::VOLUME_ID,
            ) {
                // Long file name
                self.name
                    .push({
                        let mut chunk = heapless::Vec::default();
                        let entry: &LongFileNameEntry = transmute_ref!(entry_bytes);
                        'iter_slices: for slice in [
                            entry.chars_0_4.as_slice(),
                            entry.chars_5_10.as_slice(),
                            entry.chars_11_12.as_slice(),
                        ] {
                            for u16 in slice {
                                let char = u16.get();
                                if char != 0 {
                                    // This will never fail because there can't be >13 u16s
                                    chunk.push(char).unwrap();
                                } else {
                                    // null terminated, end
                                    break 'iter_slices;
                                }
                            }
                        }
                        chunk
                    })
                    .map_err(|_| ParseEntryError::LfnOverflow)?;
                ParseEntryOutput::KeepReadingToParseCurrentEntry(self)
            } else if entry.file_name[0] == 0xe5 {
                ParseEntryOutput::KeepReadingToParseNextEntry(None)
            } else if entry.file_name[0] == 0x00 {
                ParseEntryOutput::DoneReadingEntries
            } else {
                let volume_id = attributes.contains(DirEntryAttributes::VOLUME_ID);
                ParseEntryOutput::KeepReadingToParseNextEntry(Some(DirEntry {
                    name: if !self.name.is_empty() {
                        // Long file name entries are in reverse order for some reason
                        self.name.into_iter().rev().flatten().collect()
                    } else {
                        let mut name = heapless::Vec::default();
                        for &char in &entry.file_name[..8] {
                            if char != b' ' {
                                name.push(u16::from(char)).unwrap();
                            } else {
                                break;
                            }
                        }
                        if !volume_id {
                            name.push(u16::from(b'.')).unwrap();
                        }
                        for &char in &entry.file_name[8..] {
                            if char != b' ' {
                                name.push(u16::from(char)).unwrap();
                            } else {
                                break;
                            }
                        }
                        name
                    },
                    read_only: attributes.contains(DirEntryAttributes::READ_ONLY),
                    hidden: attributes.contains(DirEntryAttributes::HIDDEN),
                    system: attributes.contains(DirEntryAttributes::SYSTEM),
                    volume_id,
                    directory: attributes.contains(DirEntryAttributes::DIRECTORY),
                    archive: attributes.contains(DirEntryAttributes::ARCHIVE),
                    creation_date: Date(entry.creation_date.get()),
                    creation_time: Time(entry.creation_time.get()),
                    creation_time_within_second: entry.creation_time_within_second,
                    last_accessed_date: Date(entry.last_accessed_date.get()),
                    last_modified_date: Date(entry.last_modification_date.get()),
                    last_modified_time: Time(entry.last_modification_time.get()),
                    first_cluster_number: u32::from_le_bytes([
                        entry.cluster_number_low[0],
                        entry.cluster_number_low[1],
                        entry.cluster_number_high[0],
                        entry.cluster_number_high[1],
                    ]),
                    size: entry.size.get(),
                }))
            }
        })
    }
}
