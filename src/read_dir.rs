use core::num::NonZero;

use crate::{
    DIR_SLOT_SIZE, DirEntryParser, NextClusterError, ParseEntryError, ParsedBpb, ParsedDirEntry,
    ProcessSlotOutput, read_file::PartitionSegment,
};

#[derive(Debug)]
pub struct ReadDir {
    bpb: ParsedBpb,
    cluster_number: u32,
    /// If `None`, that means we need to find out what the next cluster is before setting the slot index to `Some(0)`.
    slot_index: Option<u32>,
    dir_entry_parser: DirEntryParser,
}

#[derive(Debug)]
pub enum Next {
    Continue(ReadDir),
    Done,
}

#[derive(Debug)]
pub struct ProcessDataOutput {
    dir_entry: Option<ParsedDirEntry>,
    next: Next,
}

#[derive(Debug)]
pub enum ProcessDataError {
    ParseEntry(ParseEntryError),
    NextCluster(NextClusterError),
    NoNextCluster,
}

impl ReadDir {
    pub fn new(bpb: ParsedBpb, start_cluster_number: u32) -> Self {
        Self {
            bpb,
            cluster_number: start_cluster_number,
            slot_index: Some(0),
            dir_entry_parser: DirEntryParser::default(),
        }
    }

    pub const MAX_READ_BUFFER_LEN: NonZero<u32> = DIR_SLOT_SIZE;

    pub fn read_instruction(&self) -> PartitionSegment {
        match self.slot_index {
            Some(slot_index) => PartitionSegment {
                position: self.bpb.cluster_position(self.cluster_number)
                    + (slot_index * self.bpb.cluster_info_size().get()) as u64,
                len: DIR_SLOT_SIZE,
            },
            None => PartitionSegment {
                position: self.bpb.cluster_info_start(self.cluster_number),
                len: self.bpb.cluster_info_size(),
            },
        }
    }

    pub fn process_data(mut self, data: &[u8]) -> Result<ProcessDataOutput, ProcessDataError> {
        Ok(match &mut self.slot_index {
            Some(slot_index) => {
                match self
                    .dir_entry_parser
                    .process_slot(data.try_into().unwrap())
                    .map_err(ProcessDataError::ParseEntry)?
                {
                    ProcessSlotOutput::InProgress(new_parser) => {
                        *slot_index += 1;
                        if *slot_index == self.bpb.cluster_size().get() / DIR_SLOT_SIZE {
                            self.slot_index = None;
                        }
                        self.dir_entry_parser = new_parser;
                        ProcessDataOutput {
                            dir_entry: None,
                            next: Next::Continue(self),
                        }
                    }
                    ProcessSlotOutput::EntryParsed(parsed_dir_entry) => {
                        *slot_index += 1;
                        if *slot_index == self.bpb.cluster_size().get() / DIR_SLOT_SIZE {
                            self.slot_index = None;
                        }
                        self.dir_entry_parser = Default::default();
                        ProcessDataOutput {
                            dir_entry: Some(parsed_dir_entry),
                            next: Next::Continue(self),
                        }
                    }
                    ProcessSlotOutput::EmptySlot => {
                        self.dir_entry_parser = Default::default();
                        *slot_index += 1;
                        if *slot_index == self.bpb.cluster_size().get() / DIR_SLOT_SIZE {
                            self.slot_index = None;
                        }
                        ProcessDataOutput {
                            dir_entry: None,
                            next: Next::Continue(self),
                        }
                    }
                    ProcessSlotOutput::EndOfDir => ProcessDataOutput {
                        dir_entry: None,
                        next: Next::Done,
                    },
                }
            }
            None => {
                self.cluster_number = self
                    .bpb
                    .next_cluster_number(data.try_into().unwrap())
                    .map_err(ProcessDataError::NextCluster)?
                    .ok_or(ProcessDataError::NoNextCluster)?;
                self.slot_index = Some(0);
                ProcessDataOutput {
                    dir_entry: None,
                    next: Next::Continue(self),
                }
            }
        })
    }
}
