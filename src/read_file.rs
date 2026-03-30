use core::cmp::min;

use crate::{Bpb, StateMachine};

pub enum ReadFileInput<'a> {
    DoneReadingPart,
    ReadClusterInfo(&'a [u8]),
}

#[derive(Debug)]
pub struct ReadFilePart {
    pub address_in_buffer: usize,
    pub address_in_partition: u64,
    pub copy_len: usize,
}

#[derive(Debug)]
pub struct ReadClusterInfo {
    pub address_in_partition: u64,
    pub len: usize,
}

#[derive(Debug)]
pub enum ReadFileOutput {
    Done,
    ReadFilePart(ReadFilePart),
    ReadClusterInfo(ReadClusterInfo),
}

pub struct ReadFile<'a> {
    bpb: &'a Bpb,
    start: u32,
    len: u32,
    cluster_number: u32,
    /// The file address represented by the start of the cluster
    cluster_file_address: u32,
    position_in_buffer: usize,
}

impl<'a> ReadFile<'a> {
    pub fn new(bpb: &'a Bpb, start_cluster_number: u32, start: u32, len: u32) -> Self {
        Self {
            bpb,
            start,
            len,
            cluster_number: start_cluster_number,
            cluster_file_address: 0,
            position_in_buffer: 0,
        }
    }
}

impl StateMachine for ReadFile<'_> {
    type Input<'a> = ReadFileInput<'a>;
    type Output = ReadFileOutput;

    fn output(&self) -> Self::Output {
        if self.position_in_buffer as u32 == self.len {
            ReadFileOutput::Done
        } else if self.cluster_file_address + self.bpb.bytes_per_cluster()
            > self.start + self.position_in_buffer as u32
        {
            ReadFileOutput::ReadFilePart(ReadFilePart {
                address_in_buffer: self.position_in_buffer,
                address_in_partition: self.bpb.cluster_position(self.cluster_number)
                    + (self.start + self.position_in_buffer as u32 - self.cluster_file_address)
                        as u64,
                copy_len: min(
                    self.cluster_file_address as usize + self.bpb.bytes_per_cluster() as usize
                        - self.position_in_buffer,
                    self.len as usize - self.position_in_buffer,
                ),
            })
        } else {
            ReadFileOutput::ReadClusterInfo(ReadClusterInfo {
                address_in_partition: self.bpb.cluster_info_start(self.cluster_number),
                len: self.bpb.cluster_info_size(),
            })
        }
    }

    fn input(&mut self, input: Self::Input<'_>) {
        match input {
            ReadFileInput::DoneReadingPart => match self.output() {
                ReadFileOutput::ReadFilePart(read_file_part) => {
                    self.position_in_buffer += read_file_part.copy_len;
                }
                _ => unreachable!(),
            },
            ReadFileInput::ReadClusterInfo(cluster_info) => {
                // TODO: Don't panic
                self.cluster_number = self.bpb.next_cluster_number(cluster_info).unwrap().unwrap();
                self.cluster_file_address += self.bpb.bytes_per_cluster();
            }
        }
    }
}
