use core::num::NonZero;

use crate::{MAX_CLUSTER_INFO_SIZE, NextClusterError, ParsedBpb};

/// The way you read a file
#[derive(Debug)]
pub struct ReadFile {
    bpb: ParsedBpb,
    cluster_number: u32,
    bytes_left_to_read: NonZero<u32>,
}

#[derive(Debug)]
pub enum NextOutput {
    Continue(ReadFile),
    Done,
}

#[derive(Debug)]
pub enum NextError {
    NextClusterError(NextClusterError),
    NoNextCluster,
}

/// Just a position and a length of a segment of a partition (the position starts from the start
/// of the partition). Not required to be aligned to or a multiple of anything.
#[derive(Debug)]
pub struct PartitionSegment {
    pub position: u64,
    pub len: NonZero<u32>,
}

impl ReadFile {
    pub fn new(bpb: ParsedBpb, start_cluster_number: u32, file_len: NonZero<u32>) -> Self {
        Self {
            bpb,
            cluster_number: start_cluster_number,
            bytes_left_to_read: file_len,
        }
    }

    pub fn read_segment(&self) -> PartitionSegment {
        PartitionSegment {
            position: self.bpb.cluster_position(self.cluster_number),
            len: self.bpb.cluster_size().min(self.bytes_left_to_read),
        }
    }

    pub const NEXT_INSTRUCTIONS_MAX_BUFFER_LEN: NonZero<u32> = MAX_CLUSTER_INFO_SIZE;

    pub fn next_instructions(&self) -> PartitionSegment {
        PartitionSegment {
            position: self.bpb.cluster_info_start(self.cluster_number),
            len: self.bpb.cluster_info_size(),
        }
    }

    pub fn next(self, cluster_info: &[u8]) -> Result<NextOutput, NextError> {
        if let Some(new_bytes_left_to_read) = self
            .bytes_left_to_read
            .get()
            .checked_sub(self.bpb.cluster_size().get())
            .and_then(NonZero::new)
        {
            match self
                .bpb
                .next_cluster_number(cluster_info)
                .map_err(NextError::NextClusterError)?
            {
                Some(next_cluster_number) => Ok(NextOutput::Continue(Self {
                    bpb: self.bpb,
                    cluster_number: next_cluster_number,
                    bytes_left_to_read: new_bytes_left_to_read,
                })),
                None => Err(NextError::NoNextCluster),
            }
        } else {
            Ok(NextOutput::Done)
        }
    }
}
