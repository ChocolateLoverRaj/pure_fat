use std::{
    fs::File,
    io::{Read, Seek, SeekFrom},
    num::NonZero,
};

use pure_fat::{
    Bpb, DIR_SLOT_SIZE, DirEntryParser, MAX_CLUSTER_INFO_SIZE, ParsedBpb, ProcessSlotOutput,
    read_file::{NextOutput, PartitionSegment, ReadFile},
};
use zerocopy::transmute;

fn main() {
    let mut file = File::open("fat_32.bin").unwrap();
    let mut buffer = [Default::default(); size_of::<Bpb>()];
    file.read_exact(&mut buffer).unwrap();
    let bpb: Bpb = transmute!(buffer);
    let bpb = ParsedBpb::try_from(bpb).unwrap();
    let fat_type = bpb.fat_type();
    let cluster_size = bpb.cluster_size();
    println!("Cluster size: {cluster_size} B");
    println!("FAT type: {fat_type:?}");
    let mut cluster_number = bpb.root_dir_start_cluster_number();
    let mut buffer = [Default::default(); MAX_CLUSTER_INFO_SIZE.get() as usize];
    'read_dir: loop {
        println!("Cluster: {cluster_number}");
        let cluster_position = bpb.cluster_position(cluster_number);
        let mut slot_buffer = [Default::default(); DIR_SLOT_SIZE.get() as usize];
        let mut parser = DirEntryParser::default();
        for i in 0..bpb.cluster_size().get() / DIR_SLOT_SIZE {
            file.seek(SeekFrom::Start(
                cluster_position + (i * DIR_SLOT_SIZE.get()) as u64,
            ))
            .unwrap();
            file.read_exact(&mut slot_buffer).unwrap();
            match parser.process_slot(&slot_buffer).unwrap() {
                ProcessSlotOutput::InProgress(new_parser) => {
                    parser = new_parser;
                }
                ProcessSlotOutput::EntryParsed(entry) => {
                    let name = heapless::String::<255>::from_utf16(&entry.name).unwrap();
                    println!("{name:?} {entry:?}");

                    if entry.directory {
                        println!("  TODO");
                    } else if !entry.directory
                        && !entry.volume_id
                        && let Some(file_len) = NonZero::new(entry.size)
                    {
                        let mut read_file =
                            ReadFile::new(bpb, entry.first_cluster_number, file_len);
                        loop {
                            let segment = read_file.read_segment();
                            println!("  {segment:?}");
                            let mut buffer = [Default::default();
                                ReadFile::NEXT_INSTRUCTIONS_MAX_BUFFER_LEN.get() as usize];
                            let PartitionSegment { position, len } = read_file.next_instructions();
                            let buffer = &mut buffer[..len.get() as usize];
                            file.seek(SeekFrom::Start(position)).unwrap();
                            file.read_exact(buffer).unwrap();
                            match read_file.next(buffer).unwrap() {
                                NextOutput::Continue(new_read_file) => {
                                    read_file = new_read_file;
                                }
                                NextOutput::Done => break,
                            }
                        }
                    }

                    parser = Default::default();
                }
                ProcessSlotOutput::EmptySlot => {
                    parser = Default::default();
                }
                ProcessSlotOutput::EndOfDir => {
                    break 'read_dir;
                }
            }
        }

        file.seek(SeekFrom::Start(bpb.cluster_info_start(cluster_number)))
            .unwrap();
        let cluster_info_buffer = &mut buffer[..bpb.cluster_info_size().get() as usize];
        file.read_exact(cluster_info_buffer).unwrap();
        match bpb.next_cluster_number(cluster_info_buffer).unwrap() {
            Some(next_cluster_number) => {
                cluster_number = next_cluster_number;
            }
            None => {
                break;
            }
        }
    }
}
