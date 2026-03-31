use core::num::NonZero;

use zerocopy::little_endian::{U16, U32};

use crate::{Bpb, FatType, NextClusterError};

#[derive(Debug, Clone, Copy)]
pub struct ParsedBpb {
    fat_type: FatType,
    /// THe position (in bytes) of the File Attributes Table
    fat_table_position: u64,
    /// The position of the first cluster
    clusters_position: u64,
    root_dir_cluster_number: u32,
    bytes_per_cluster: NonZero<u32>,
}

#[derive(Debug)]
pub enum FromBpbError {
    ZeroSectorsPerCluster,
    ZeroBytesPerSector,
}

impl TryFrom<Bpb> for ParsedBpb {
    type Error = FromBpbError;

    fn try_from(value: Bpb) -> Result<Self, Self::Error> {
        let sectors_per_cluster =
            NonZero::new(value.sectors_per_cluster).ok_or(FromBpbError::ZeroSectorsPerCluster)?;
        let bytes_per_sector =
            NonZero::new(value.bytes_per_sector.get()).ok_or(FromBpbError::ZeroBytesPerSector)?;

        Ok(Self {
            fat_type: value.fat_type(),
            fat_table_position: value.fat_table_start(),
            clusters_position: value.cluster_position(2),
            root_dir_cluster_number: value.root_dir_cluster_number(),
            bytes_per_cluster: NonZero::<u32>::from(sectors_per_cluster)
                .checked_mul(bytes_per_sector.into())
                .unwrap(),
        })
    }
}

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
