use core::{char::DecodeUtf16Error, convert::Infallible, iter, num::NonZero, ops::Deref, slice};

use bitflags::bitflags;
use oem_cp::Cp437;
use zerocopy::{
    FromBytes, Immutable, IntoBytes, KnownLayout,
    little_endian::{U16, U32},
    transmute_ref,
};

pub type DirEntrySlot = [u8; 32];

pub const DIR_SLOT_SIZE: NonZero<u32> = NonZero::new(size_of::<DirEntrySlot>() as u32).unwrap();

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

#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(Debug, Default)]
pub struct Date(pub u16);

#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(Debug, Default)]
pub struct Time(pub u16);

/// Decode the string. For long file names, this will decode UTF-16. For short file names (which includes volume ids), this will decode with code page 437 (United States).
///
/// You can use the iterator of chars to compare the name with a `str` without allocating. You can also use `core::alloc::String`, or `heapless::String<Chars::MAX_UT8_LEN>`.
pub trait Chars {
    const MAX_UTF8_LEN: usize;

    type Error;

    fn chars(&self) -> impl Iterator<Item = Result<char, Self::Error>>;
}

/// Encoded with OEM code pages.
/// Most of the times it is valid ASCII, but if it has non-ASCII characters, then they are encoded in a certain code page.
/// The default code page is 437 (United States). But the FAT partition doesn't tell you which code page it is.
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(Debug)]
pub struct VolumeIdName(heapless::Vec<u8, 11>);

impl VolumeIdName {
    /// The volume id name is commonly stored as code page 437, although technically it doesn't
    /// need to be 437, and it could be a different code page.
    ///
    /// This crate provides convenience functions to decode the name assuming it's in code page 437.
    /// This value is the maximum length after decoding and re-encoding into UTF-8. It is useful to
    /// use as the max len value if storing in a `heapless::String`.
    pub const MAX_CP437_UTF8_LEN: usize = 33;

    /// Use this as an easy way of getting the volume name as a string.
    ///
    /// You can use this to construct a [`heapless::String`] (encoded in UTF-8) or re-encode it
    /// into something else.
    pub fn chars_cp437(&self) -> impl Iterator<Item = char> {
        self.0.iter().copied().map(|byte| Cp437::from(byte).into())
    }
}

impl Chars for VolumeIdName {
    /// The volume id name is commonly stored as code page 437, although technically it doesn't
    /// need to be 437, and it could be a different code page.
    ///
    /// This crate provides convenience functions to decode the name assuming it's in code page 437.
    /// This value is the maximum length after decoding and re-encoding into UTF-8. It is useful to
    /// use as the max len value if storing in a `heapless::String`.
    const MAX_UTF8_LEN: usize = Self::MAX_CP437_UTF8_LEN;

    type Error = Infallible;

    fn chars(&self) -> impl Iterator<Item = Result<char, Self::Error>> {
        self.chars_cp437().map(Ok)
    }
}

impl From<VolumeIdName> for heapless::Vec<u8, 11> {
    fn from(value: VolumeIdName) -> Self {
        value.0
    }
}

impl Deref for VolumeIdName {
    type Target = heapless::Vec<u8, 11>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A short file name is encoded in code page format (and is typically valid ASCII).
/// This library inserts the "." character into the name.
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ShortFileName(heapless::Vec<u8, 12>);

impl ShortFileName {
    /// Up to 11 cp437, max 3 UTF-8 bytes per byte of cp437.
    /// Up to 1 "." character, always 1 byte in UTF-8.
    pub const MAX_CP437_UTF8_LEN: usize = 34;

    pub fn chars_cp437(&self) -> impl Iterator<Item = char> {
        self.0.iter().copied().map(|byte| Cp437::from(byte).into())
    }
}

impl Chars for ShortFileName {
    /// Up to 11 cp437, max 3 UTF-8 bytes per byte of cp437.
    /// Up to 1 "." character, always 1 byte in UTF-8.
    const MAX_UTF8_LEN: usize = Self::MAX_CP437_UTF8_LEN;

    type Error = Infallible;

    fn chars(&self) -> impl Iterator<Item = Result<char, Self::Error>> {
        self.chars_cp437().map(Ok)
    }
}

impl From<ShortFileName> for heapless::Vec<u8, 12> {
    fn from(value: ShortFileName) -> Self {
        value.0
    }
}

impl Deref for ShortFileName {
    type Target = heapless::Vec<u8, 12>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A long file name is (supposed to be) formatted as UTF-16, with a max of u16 * 255.
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LongFileName(heapless::Vec<u16, 255>);

impl Chars for LongFileName {
    /// One UTF-16 u16 can be a maximum of 3 UTF-8 u8s.
    const MAX_UTF8_LEN: usize = 255 * 3;

    type Error = DecodeUtf16Error;

    fn chars(&self) -> impl Iterator<Item = Result<char, Self::Error>> {
        char::decode_utf16(self.0.iter().copied())
    }
}

impl From<LongFileName> for heapless::Vec<u16, 255> {
    fn from(value: LongFileName) -> Self {
        value.0
    }
}

impl Deref for LongFileName {
    type Target = heapless::Vec<u16, 255>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// Name for files and directories.
#[allow(clippy::large_enum_variant)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum FileName {
    Short(ShortFileName),
    Long(LongFileName),
}

impl Chars for FileName {
    const MAX_UTF8_LEN: usize = LongFileName::MAX_UTF8_LEN;

    type Error = <LongFileName as Chars>::Error;

    fn chars(&self) -> impl Iterator<Item = Result<char, Self::Error>> {
        let mut i = 0;
        iter::from_fn(move || {
            let r = match self {
                Self::Short(name) => name.chars().nth(i).map(|result| Ok(result.unwrap())),
                Self::Long(name) => name.chars().nth(i),
            };
            i += 1;
            r
        })
    }
}

#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(Debug)]
pub enum FileSizeAndCluster {
    /// The file size is `0`, so it doesn't have any clusters.
    Empty,
    /// The file size is at least `1` so it has at least one cluster so it has a start cluster.
    NotEmpty {
        size: NonZero<u32>,
        first_cluster_number: u32,
    },
}

/// A Rusty representation of a directory entry.
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(Debug)]
pub enum ParsedDirEntry {
    /// A label for the partition, such as "MY SD CARD". Only present in the root dir. Always all caps.
    VolumeId { name: VolumeIdName },
    File {
        name: FileName,
        hidden: bool,
        system: bool,
        archive: bool,
        creation_date: Date,
        creation_time: Time,
        creation_time_within_second: u8,
        last_accessed_date: Date,
        last_modified_date: Date,
        last_modified_time: Time,
        size_and_cluster: FileSizeAndCluster,
    },
    Dir {
        name: FileName,
        hidden: bool,
        system: bool,
        archive: bool,
        creation_date: Date,
        creation_time: Time,
        creation_time_within_second: u8,
        last_accessed_date: Date,
        last_modified_date: Date,
        last_modified_time: Time,
        first_cluster_number: u32,
    },
    /// The `.` entry. Not present in the root dir. Useful for checking the creation time of a dir without reading the parent dir.
    CurrentDir {
        creation_date: Date,
        creation_time: Time,
        creation_time_within_second: u8,
        first_cluster_number: u32,
        hidden: bool,
        system: bool,
        archive: bool,
    },
    /// The `..` entry. Not present in the root dir. Useful for traversing up in the tree of files.
    ParentDir {
        creation_date: Date,
        creation_time: Time,
        creation_time_within_second: u8,
        first_cluster_number: u32,
        hidden: bool,
        system: bool,
        archive: bool,
    },
}

impl Chars for ParsedDirEntry {
    const MAX_UTF8_LEN: usize = <FileName as Chars>::MAX_UTF8_LEN;

    type Error = <FileName as Chars>::Error;

    fn chars(&self) -> impl Iterator<Item = Result<char, Self::Error>> {
        let mut i = 0;
        iter::from_fn(move || {
            let r = match self {
                Self::VolumeId { name } => name.chars().nth(i).map(|result| Ok(result.unwrap())),
                Self::Dir { name, .. } => name.chars().nth(i),
                Self::File { name, .. } => name.chars().nth(i),
                Self::CurrentDir { .. } => ".".chars().map(Ok).nth(i),
                Self::ParentDir { .. } => "..".chars().map(Ok).nth(i),
            };
            i += 1;
            r
        })
    }
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

bitflags! {
    pub struct WindowsNtFlags: u8 {
        const LOWERCASE_NAME = 1 << 3;
        const LOWERCASE_EXTENSION = 1 << 4;
    }
}

#[derive(Debug, Default)]
pub struct DirEntryParser {
    name: heapless::Vec<heapless::Vec<u16, 13>, 20>,
}

#[allow(clippy::large_enum_variant)]
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
                ProcessSlotOutput::EntryParsed(
                    if attributes.contains(DirEntryAttributes::VOLUME_ID) {
                        ParsedDirEntry::VolumeId {
                            name: VolumeIdName({
                                let mut name = heapless::Vec::default();
                                let mut trim_end = None;
                                for (index, char) in entry.file_name.iter().copied().enumerate() {
                                    if char == b' ' {
                                        if trim_end.is_none() {
                                            trim_end = Some(index);
                                        }
                                    } else {
                                        trim_end = None;
                                    };
                                    name.push(char).unwrap();
                                }
                                if let Some(trim_end) = trim_end {
                                    name.truncate(trim_end);
                                }
                                name
                            }),
                        }
                    } else {
                        let name = if !self.name.is_empty() {
                            FileName::Long(LongFileName({
                                // Long file name entries are in reverse order for some reason
                                self.name.into_iter().rev().flatten().collect()
                            }))
                        } else {
                            FileName::Short(ShortFileName({
                                let mut name = heapless::Vec::default();
                                let windows_nt_flags =
                                    WindowsNtFlags::from_bits_retain(entry.reserved_for_windows_nt);
                                {
                                    let mut trim_end = None;
                                    for (index, char) in
                                        entry.file_name[..8].iter().copied().enumerate()
                                    {
                                        if char == b' ' {
                                            if trim_end.is_none() {
                                                trim_end = Some(index);
                                            }
                                        } else {
                                            trim_end = None;
                                        };
                                        let char = char::from(char);
                                        let char = if windows_nt_flags
                                            .contains(WindowsNtFlags::LOWERCASE_NAME)
                                        {
                                            char.to_ascii_lowercase()
                                        } else {
                                            char
                                        };
                                        let mut char_u16 = Default::default();
                                        char.encode_utf8(slice::from_mut(&mut char_u16));
                                        name.push(char_u16).unwrap();
                                    }
                                    if let Some(trim_end) = trim_end {
                                        name.truncate(trim_end);
                                    }
                                }
                                if entry.file_name[8] != b' ' {
                                    name.push(b'.').unwrap();
                                    let name_len_after_dot = name.len();
                                    let mut trim_end = None;
                                    for (index, char) in
                                        entry.file_name[8..].iter().copied().enumerate()
                                    {
                                        if char == b' ' {
                                            if trim_end.is_none() {
                                                trim_end = Some(index);
                                            }
                                        } else {
                                            trim_end = None;
                                        };
                                        let char = char::from(char);
                                        let char = if windows_nt_flags
                                            .contains(WindowsNtFlags::LOWERCASE_EXTENSION)
                                        {
                                            char.to_ascii_lowercase()
                                        } else {
                                            char
                                        };
                                        let mut char_u16 = Default::default();
                                        char.encode_utf8(slice::from_mut(&mut char_u16));
                                        name.push(char_u16).unwrap();
                                    }
                                    if let Some(trim_end) = trim_end {
                                        name.truncate(name_len_after_dot + trim_end);
                                    }
                                }
                                name
                            }))
                        };
                        let hidden = attributes.contains(DirEntryAttributes::HIDDEN);
                        let system = attributes.contains(DirEntryAttributes::SYSTEM);
                        let archive = attributes.contains(DirEntryAttributes::ARCHIVE);
                        let creation_date = Date(entry.creation_date.get());
                        let creation_time = Time(entry.creation_time.get());
                        let creation_time_within_second = entry.creation_time_within_second;
                        let last_modified_date = Date(entry.last_modification_date.get());
                        let last_modified_time = Time(entry.last_modification_time.get());
                        let first_cluster_number = u32::from_le_bytes([
                            entry.cluster_number_low[0],
                            entry.cluster_number_low[1],
                            entry.cluster_number_high[0],
                            entry.cluster_number_high[1],
                        ]);
                        let last_accessed_date = Date(entry.last_accessed_date.get());
                        if name
                            == FileName::Short(ShortFileName(
                                heapless::Vec::from_slice(b".").unwrap(),
                            ))
                        {
                            ParsedDirEntry::CurrentDir {
                                creation_date,
                                creation_time,
                                creation_time_within_second,
                                first_cluster_number,
                                hidden,
                                system,
                                archive,
                            }
                        } else if name
                            == FileName::Short(ShortFileName(
                                heapless::Vec::from_slice(b"..").unwrap(),
                            ))
                        {
                            ParsedDirEntry::ParentDir {
                                creation_date,
                                creation_time,
                                creation_time_within_second,
                                first_cluster_number,
                                hidden,
                                system,
                                archive,
                            }
                        } else if attributes.contains(DirEntryAttributes::DIRECTORY) {
                            ParsedDirEntry::Dir {
                                name,
                                hidden,
                                system,
                                archive,
                                creation_date,
                                creation_time,
                                creation_time_within_second,
                                last_accessed_date,
                                last_modified_date,
                                last_modified_time,
                                first_cluster_number,
                            }
                        } else {
                            ParsedDirEntry::File {
                                name,
                                hidden,
                                system,
                                archive,
                                creation_date,
                                creation_time,
                                creation_time_within_second,
                                last_accessed_date,
                                last_modified_date,
                                last_modified_time,
                                size_and_cluster: match NonZero::new(entry.size.get()) {
                                    Some(size) => FileSizeAndCluster::NotEmpty {
                                        size,
                                        first_cluster_number,
                                    },
                                    None => FileSizeAndCluster::Empty,
                                },
                            }
                        }
                    },
                )
            }
        })
    }
}
