use zerocopy::{
    FromBytes, Immutable, IntoBytes, KnownLayout,
    little_endian::{U16, U32},
};

/// BPB (BIOS Parameter Block)
#[derive(Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
#[repr(C)]
pub struct Bpb {
    pub(crate) instructions: [u8; 3],
    pub(crate) oem_identifier: [u8; 8],
    pub(crate) bytes_per_sector: U16,
    pub(crate) sectors_per_cluster: u8,
    pub(crate) reserved_sectors: U16,
    pub(crate) number_of_tables: u8,
    pub(crate) root_directory_entries: U16,
    /// If there are >65535 sectors, this will have a value of `0`, and you should read large sector count instead
    pub(crate) number_of_sectors: U16,
    /// <https://en.wikipedia.org/wiki/Design_of_the_FAT_file_system#BPB20_OFS_0Ah>
    pub(crate) media_descriptor_type: u8,
    /// Number of sectors per FAT. FAT12/FAT16 only.
    pub(crate) sectors_per_fat: U16,
    pub(crate) sectors_per_track: U16,
    pub(crate) heads_or_sides: U16,
    pub(crate) hidden_sectors: U32,
    pub(crate) large_sector_count: U32,
    pub(crate) extension_bytes: [u8; 0x1DC],
}

// /// FAT 12 and FAT 16
// #[derive(Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
// #[repr(C)]
// pub struct ExtendedBootRecordFat12 {
//     todo: [u8; 0x1DC],
// }

#[derive(Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
#[repr(C)]
pub struct ExtendedBootRecordFat32 {
    pub(crate) sectors_per_fat: U32,
    pub(crate) flags: U16,
    pub(crate) fat_version_number: U16,
    pub(crate) root_dir_cluster_number: U32,
    pub(crate) fs_info_sector_number: U16,
    pub(crate) backup_boot_sector_sector_number: U16,
    pub(crate) _reserved_0: [u8; 12],
    pub(crate) drive_number: u8,
    pub(crate) windows_nt_flags: u8,
    /// must be 0x28 or 0x29
    pub(crate) signature: u8,
    pub(crate) volume_id_serial_number: U32,
    pub(crate) volume_label_str: [u8; 11],
    /// System identifier string. Always "FAT32   ". The spec says never to trust the contents of this string for any use.
    pub(crate) system_identifier_str: [u8; 8],
    pub(crate) boot_code: [u8; 420],
    /// Bootable partition signature 0xAA55.
    pub(crate) bootable_partition_signature: U16,
}

// #[derive(Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
// #[repr(C)]
// pub struct ExtendedBootRecordExFat {
//     todo: [u8; 0x1DC],
// }
