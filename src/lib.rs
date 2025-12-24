#![cfg_attr(not(feature = "std"), no_std)]

// See https://wiki.osdev.org/FAT

use core::num::NonZero;

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
    extended_bytes: [u8; 0x1DC],
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

#[derive(Debug)]
pub enum FataType {
    Fat12,
    Fat16,
    Fat32,
    ExFat,
}

impl Bpb {
    pub fn total_sectors(&self) -> Option<NonZero<u32>> {
        NonZero::new(self.number_of_sectors.into()).or(NonZero::new(self.large_sector_count.into()))
    }

    pub fn fat_type(&self) -> FataType {
        let sectors_per_fat =
            if let Some(sectors_per_fat) = NonZero::new(self.sectors_per_fat.get()) {
                sectors_per_fat.get().into()
            } else {
                let fat32_info: &ExtendedBootRecordFat32 = transmute_ref!(&self.extended_bytes);
                fat32_info.sectors_per_fat.get()
            };
        let root_dir_sectors = self
            .root_directory_entries
            .get()
            .div_ceil(self.bytes_per_sector.get());
        let first_data_sector = self.reserved_sectors.get()
            + (u16::from(self.number_of_tables) * self.sectors_per_fat.get())
            + root_dir_sectors;
        let first_fat_sector = self.reserved_sectors.get();
        let data_sectors = self.total_sectors().unwrap().get()
            - u32::from(
                self.reserved_sectors.get()
                    + (u16::from(self.number_of_tables) * self.sectors_per_fat)
                    + root_dir_sectors,
            );
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
}
