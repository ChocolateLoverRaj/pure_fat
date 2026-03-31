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

// #[derive(Debug, FromBytes, IntoBytes, Immutable, KnownLayout)]
// #[repr(C)]
// pub struct ExtendedBootRecordExFat {
//     todo: [u8; 0x1DC],
// }

#[derive(Debug, Clone, Copy)]
pub enum FatType {
    Fat12,
    Fat16,
    Fat32,
    ExFat,
}

#[derive(Debug, Clone, Copy)]
pub struct NextClusterError(pub u32);

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

    pub fn fat_type(&self) -> FatType {
        let data_sectors = self.total_sectors().unwrap().get()
            - (u32::from(self.reserved_sectors.get())
                + (u32::from(self.number_of_tables) * self.sectors_per_fat())
                + u32::from(self.root_dir_sectors()));
        let total_clusters = data_sectors / u32::from(self.sectors_per_cluster);
        if self.bytes_per_sector.get() == 0 {
            FatType::ExFat
        } else if total_clusters < 4085 {
            FatType::Fat12
        } else if total_clusters < 65525 {
            FatType::Fat16
        } else {
            FatType::Fat32
        }
    }

    pub fn root_dir_cluster_number(&self) -> u32 {
        match self.fat_type() {
            FatType::Fat12 | FatType::Fat16 => 0,
            FatType::Fat32 | FatType::ExFat => {
                let fat32_info: &ExtendedBootRecordFat32 = transmute_ref!(&self.extension_bytes);
                fat32_info.root_dir_cluster_number.get()
            }
        }
    }

    /// Returns the position in **bytes** of the start of a sector based on a sector number.
    pub fn cluster_position(&self, cluster_number: u32) -> u64 {
        let fat_start_sector = u32::from(self.reserved_sectors.get());
        let data_start_sector =
            fat_start_sector + u32::from(self.number_of_tables) * self.sectors_per_fat();
        let cluster_sector =
            data_start_sector + (cluster_number - 2) * u32::from(self.sectors_per_cluster);
        u64::from(cluster_sector) * u64::from(self.bytes_per_sector.get())
    }

    /// Use this to know how much to read
    pub fn bytes_per_cluster(&self) -> u32 {
        u32::from(self.sectors_per_cluster) * u32::from(self.bytes_per_sector.get())
    }

    pub(crate) fn fat_table_start(&self) -> u64 {
        u64::from(self.reserved_sectors.get()) * u64::from(self.bytes_per_sector.get())
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
            FatType::Fat12 | FatType::Fat16 => size_of::<U16>(),
            FatType::Fat32 => size_of::<U32>(),
            FatType::ExFat => todo!(),
        }
    }

    /// Panics if the size of the slice is not equal to [`Self::cluster_info_size`].
    /// <https://en.wikipedia.org/wiki/Design_of_the_FAT_file_system#Cluster_values>.
    pub fn next_cluster_number(
        &self,
        cluster_info: &[u8],
    ) -> Result<Option<u32>, NextClusterError> {
        match self.fat_type() {
            FatType::Fat12 => todo!("calculate if upper or lower 1.5 bytes should be used"),
            FatType::Fat16 => todo!(),
            FatType::Fat32 => {
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
            FatType::ExFat => todo!(),
        }
    }
}

pub const MAX_CLUSTER_INFO_SIZE: NonZero<u32> = NonZero::new(size_of::<U32>() as u32).unwrap();
