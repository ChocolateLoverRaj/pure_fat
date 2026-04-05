use core::num::NonZero;

use zerocopy::{
    little_endian::{U16, U32},
    transmute_ref,
};

use crate::{Bpb, ExtendedBootRecordFat32};

#[derive(Debug, Clone, Copy)]
pub struct ParsedBpb {
    fat_type: FatType,
    /// The position (in bytes) of the File Attributes Table
    fat_table_position: u64,
    /// The position of the first cluster
    clusters_position: u64,
    root_dir_cluster_number: u32,
    bytes_per_cluster: NonZero<u32>,
}

#[derive(Debug)]
pub enum FromBpbError {
    ZeroSectorsPerCluster,
    // TODO: This means it's ExFAT. Instead of treating it as an error we should handle ExFAT.
    ZeroBytesPerSector,
    ZeroTotalSectors,
    ZeroSectorsPerFat,
}

impl TryFrom<Bpb> for ParsedBpb {
    type Error = FromBpbError;

    fn try_from(value: Bpb) -> Result<Self, Self::Error> {
        let sectors_per_cluster =
            NonZero::new(value.sectors_per_cluster).ok_or(FromBpbError::ZeroSectorsPerCluster)?;
        let bytes_per_sector =
            NonZero::new(value.bytes_per_sector.get()).ok_or(FromBpbError::ZeroBytesPerSector)?;
        let total_sectors = NonZero::new(u32::from(value.number_of_sectors.get()))
            .or(NonZero::new(value.large_sector_count.get()))
            .ok_or(FromBpbError::ZeroTotalSectors)?;
        let sectors_per_fat = if let Some(seectors_per_fat) =
            NonZero::new(value.sectors_per_fat.get())
        {
            seectors_per_fat.into()
        } else {
            let fat32_info: &ExtendedBootRecordFat32 = transmute_ref!(&value.extension_bytes);
            NonZero::new(fat32_info.sectors_per_fat.get()).ok_or(FromBpbError::ZeroSectorsPerFat)?
        };

        let fat_type = {
            let root_dir_sectors = value
                .root_directory_entries
                .get()
                .div_ceil(bytes_per_sector.get());
            let data_sectors = total_sectors.get()
                - (u32::from(value.reserved_sectors.get())
                    + (u32::from(value.number_of_tables) * sectors_per_fat.get())
                    + u32::from(root_dir_sectors));
            let total_clusters = data_sectors / u32::from(sectors_per_cluster.get());
            if total_clusters < 4085 {
                FatType::Fat12
            } else if total_clusters < 65525 {
                FatType::Fat16
            } else {
                FatType::Fat32
            }
        };

        Ok(Self {
            fat_type,
            fat_table_position: {
                u64::from(value.reserved_sectors.get()) * u64::from(bytes_per_sector.get())
            },
            clusters_position: {
                let fat_start_sector = u32::from(value.reserved_sectors.get());
                let data_start_sector =
                    fat_start_sector + u32::from(value.number_of_tables) * sectors_per_fat.get();
                u64::from(data_start_sector) * u64::from(bytes_per_sector.get())
            },
            root_dir_cluster_number: match fat_type {
                FatType::Fat12 | FatType::Fat16 => 0,
                FatType::Fat32 | FatType::ExFat => {
                    let fat32_info: &ExtendedBootRecordFat32 =
                        transmute_ref!(&value.extension_bytes);
                    fat32_info.root_dir_cluster_number.get()
                }
            },
            bytes_per_cluster: NonZero::<u32>::from(sectors_per_cluster)
                .checked_mul(bytes_per_sector.into())
                .unwrap(),
        })
    }
}

#[derive(Debug, Clone, Copy)]
pub enum FatType {
    Fat12,
    Fat16,
    Fat32,
    ExFat,
}

#[derive(Debug, Clone, Copy)]
pub struct NextClusterError(pub u32);

impl ParsedBpb {
    pub fn fat_type(&self) -> FatType {
        self.fat_type
    }

    pub fn root_dir_start_cluster_number(&self) -> u32 {
        self.root_dir_cluster_number
    }

    /// Returns the position in **bytes** of the start of a sector based on a sector number.
    pub fn cluster_position(&self, cluster_number: u32) -> u64 {
        self.clusters_position + (cluster_number - 2) as u64 * self.bytes_per_cluster.get() as u64
    }

    /// Size of a cluster (in bytes).
    pub fn cluster_size(&self) -> NonZero<u32> {
        self.bytes_per_cluster
    }

    /// Returns the position in bytes of where to read the cluster info
    pub fn cluster_info_start(&self, cluster_number: u32) -> u64 {
        self.fat_table_position + cluster_number as u64 * self.cluster_info_size().get() as u64
    }

    /// Returns the number of bytes you need to read to get information about the next cluster
    pub fn cluster_info_size(&self) -> NonZero<u32> {
        match self.fat_type {
            // Technically for FAT 12 you only need 1.5 bytes, but this means we need 2
            FatType::Fat12 | FatType::Fat16 => {
                NonZero::new(size_of::<U16>().try_into().unwrap()).unwrap()
            }
            FatType::Fat32 => NonZero::new(size_of::<U32>().try_into().unwrap()).unwrap(),
            FatType::ExFat => todo!(),
        }
    }

    /// Panics if the size of the slice is not equal to [`Self::cluster_info_size`].
    /// <https://en.wikipedia.org/wiki/Design_of_the_FAT_file_system#Cluster_values>.
    pub fn next_cluster_number(
        &self,
        cluster_info: &[u8],
    ) -> Result<Option<u32>, NextClusterError> {
        match self.fat_type {
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
