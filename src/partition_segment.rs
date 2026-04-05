use core::num::NonZero;

/// Just a position and a length of a segment of a partition (the position starts from the start
/// of the partition). Not required to be aligned to or a multiple of anything.
#[derive(Debug)]
pub struct PartitionSegment {
    pub position: u64,
    pub len: NonZero<u32>,
}
