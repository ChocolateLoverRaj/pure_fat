use core::num::NonZero;

use crate::{
    DIR_SLOT_SIZE, DirEntryParser, NextClusterError, ParseEntryError, ParsedBpb, ParsedDirEntry,
    PartitionSegment, ProcessSlotOutput,
};

/// To read a dir, first create a [`ReadDir`] with [`ReadDir::new`] or [`ReadDir::new_root`]. Then call [`ReadDir::read_instruction`] to know what part of the partition to read. Read the segment and input it to [`ReadDir::process_data`]. If the output contains a [`ReadDir`], repeat the process to continue reading more entries.
#[derive(Debug)]
pub struct ReadDir {
    bpb: ParsedBpb,
    cluster_number: u32,
    /// If `None`, that means we need to find out what the next cluster is before setting the slot index to `Some(0)`.
    slot_index: Option<u32>,
    dir_entry_parser: DirEntryParser,
}

#[derive(Debug)]
pub struct ProcessDataOutput {
    pub dir_entry: Option<ParsedDirEntry>,
    /// If `Some`, that means there could be more dir entries and you should continue reading the next slot. If `None`, that means that there are no more dir entries and you should stop reading this dir.
    pub next: Option<ReadDir>,
}

#[derive(Debug)]
pub enum ProcessDataError {
    ParseEntry(ParseEntryError),
    NextCluster(NextClusterError),
    NoNextCluster,
}

impl ReadDir {
    pub fn new(bpb: ParsedBpb, first_cluster_number: u32) -> Self {
        Self {
            bpb,
            cluster_number: first_cluster_number,
            slot_index: Some(0),
            dir_entry_parser: DirEntryParser::default(),
        }
    }

    pub fn new_root(bpb: ParsedBpb) -> Self {
        Self::new(bpb, bpb.root_dir_start_cluster_number())
    }

    pub const MAX_READ_BUFFER_LEN: NonZero<u32> = DIR_SLOT_SIZE;

    pub fn read_instruction(&self) -> PartitionSegment {
        match self.slot_index {
            Some(slot_index) => PartitionSegment {
                position: self.bpb.cluster_position(self.cluster_number)
                    + (slot_index * DIR_SLOT_SIZE.get()) as u64,
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
                            next: Some(self),
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
                            next: Some(self),
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
                            next: Some(self),
                        }
                    }
                    ProcessSlotOutput::EndOfDir => ProcessDataOutput {
                        dir_entry: None,
                        next: None,
                    },
                }
            }
            None => {
                self.cluster_number = self
                    .bpb
                    .next_cluster_number(data)
                    .map_err(ProcessDataError::NextCluster)?
                    .ok_or(ProcessDataError::NoNextCluster)?;
                self.slot_index = Some(0);
                ProcessDataOutput {
                    dir_entry: None,
                    next: Some(self),
                }
            }
        })
    }
}
