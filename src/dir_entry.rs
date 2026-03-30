use bitflags::bitflags;
use zerocopy::{
    FromBytes, Immutable, IntoBytes, KnownLayout,
    little_endian::{U16, U32},
    transmute_ref,
};

pub type DirEntrySlot = [u8; 32];

pub const DIR_SLOT_SIZE: usize = size_of::<DirEntrySlot>();

#[derive(Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
#[repr(C)]
pub struct DirSector {
    pub entries: [DirEntrySlot; 16],
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
pub struct Date(pub u16);
#[derive(Debug, Default)]
pub struct Time(pub u16);

/// A Rusty representation of a directory entry
#[derive(Debug, Default)]
pub struct ParsedDirEntry {
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

#[derive(Debug, Default)]
pub struct DirEntryParser {
    name: heapless::Vec<heapless::Vec<u16, 13>, 20>,
}

#[derive(Debug)]
pub enum ProcessSlotOutput {
    /// An entry was parsed. Create a new parser and read the next slot to continue reading all dir entries.
    EntryParsed(ParsedDirEntry),
    /// Continue reading the next slot to process an entry.
    InProgress(DirEntryParser),
    /// This slot was empty. Create a new parser and read the next slot.
    EmptySlot,
    /// There are no more entiries in the dir. Don't read the next slot.
    EndOfDir,
}

impl DirEntryParser {
    pub fn process_slot(
        mut self,
        slot: &DirEntrySlot,
    ) -> Result<ProcessSlotOutput, ParseEntryError> {
        Ok({
            // https://people.cs.umass.edu/~liberato/courses/2019-spring-compsci365/lecture-notes/11-fats-and-directory-entries/
            let entry: &Fat12DirEntry = transmute_ref!(slot);
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
                        let entry: &LongFileNameEntry = transmute_ref!(slot);
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
                ProcessSlotOutput::InProgress(self)
            } else if entry.file_name[0] == 0xe5 {
                ProcessSlotOutput::EmptySlot
            } else if entry.file_name[0] == 0x00 {
                ProcessSlotOutput::EndOfDir
            } else {
                let volume_id = attributes.contains(DirEntryAttributes::VOLUME_ID);
                ProcessSlotOutput::EntryParsed(ParsedDirEntry {
                    name: if !self.name.is_empty() {
                        // Long file name entries are in reverse order for some reason
                        self.name.into_iter().rev().flatten().collect()
                    } else {
                        let mut name = heapless::Vec::default();
                        if volume_id {
                            let mut trim_end = None;
                            for (index, char) in entry.file_name.iter().copied().enumerate() {
                                trim_end = if char == b' ' { Some(index) } else { None };
                                name.push(u16::from(char)).unwrap();
                            }
                            if let Some(trim_end) = trim_end {
                                name.truncate(trim_end);
                            }
                        } else {
                            {
                                let mut trim_end = None;
                                for (index, char) in
                                    entry.file_name[..8].iter().copied().enumerate()
                                {
                                    trim_end = if char == b' ' { Some(index) } else { None };
                                    name.push(u16::from(char)).unwrap();
                                }
                                if let Some(trim_end) = trim_end {
                                    name.truncate(trim_end);
                                }
                            }
                            name.push(u16::from(b'.')).unwrap();
                            let name_len_after_dot = name.len();
                            {
                                let mut trim_end = None;
                                for (index, char) in
                                    entry.file_name[8..].iter().copied().enumerate()
                                {
                                    trim_end = if char == b' ' { Some(index) } else { None };
                                    name.push(u16::from(char)).unwrap();
                                }
                                if let Some(trim_end) = trim_end {
                                    name.truncate(name_len_after_dot + trim_end);
                                }
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
                })
            }
        })
    }
}
