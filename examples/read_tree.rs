use std::{
    fs::File,
    io::{Read, Seek, SeekFrom},
};

use pure_fat::{Bpb, DIR_SLOT_SIZE, DirEntryParser, MAX_CLUSTER_INFO_SIZE, ProcessSlotOutput};
use zerocopy::transmute;

fn main() {
    let mut file = File::open("fat_32.bin").unwrap();
    let mut buffer = [Default::default(); size_of::<Bpb>()];
    file.read_exact(&mut buffer).unwrap();
    let bpb: Bpb = transmute!(buffer);
    let fat_type = bpb.fat_type();
    println!("{fat_type:?}");
    let mut cluster_number = bpb.root_dir_cluster_number();
    let mut buffer = [Default::default(); MAX_CLUSTER_INFO_SIZE];
    'read_dir: loop {
        println!("Cluster: {cluster_number}");
        let cluster_position = bpb.cluster_position(cluster_number);
        file.seek(SeekFrom::Start(cluster_position)).unwrap();
        let mut slot_buffer = [Default::default(); DIR_SLOT_SIZE];
        let mut parser = DirEntryParser::default();
        for _ in 0..bpb.bytes_per_cluster() / DIR_SLOT_SIZE as u32 {
            file.read_exact(&mut slot_buffer).unwrap();
            match parser.process_slot(&slot_buffer).unwrap() {
                ProcessSlotOutput::InProgress(new_parser) => {
                    parser = new_parser;
                }
                ProcessSlotOutput::EntryParsed(entry) => {
                    let name = heapless::String::<255>::from_utf16(&entry.name).unwrap();
                    println!("{name:?} {entry:?}");
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
        let cluster_info_buffer = &mut buffer[..bpb.cluster_info_size()];
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
