use std::{
    fs::File,
    io::{Read, Seek, SeekFrom},
    num::NonZero,
};

use pure_fat::{
    Bpb, Chars, FileSizeAndCluster, ParsedBpb, ParsedDirEntry,
    read_dir::{Next, ProcessDataOutput, ReadDir},
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
    let mut read_dir = ReadDir::new_root(bpb);
    loop {
        let PartitionSegment { position, len } = read_dir.read_instruction();
        file.seek(SeekFrom::Start(position)).unwrap();
        let mut buffer = [Default::default(); ReadDir::MAX_READ_BUFFER_LEN.get() as usize];
        let buffer = &mut buffer[..len.get() as usize];
        file.read_exact(buffer).unwrap();
        let ProcessDataOutput { dir_entry, next } = read_dir.process_data(buffer).unwrap();
        if let Some(entry) = dir_entry {
            const N: usize = ParsedDirEntry::MAX_UTF8_LEN;
            let name = entry
                .chars()
                .map(Result::unwrap)
                .collect::<heapless::String<N>>();
            println!("{name:?} {entry:?}");

            match entry {
                ParsedDirEntry::File {
                    name,
                    hidden,
                    system,
                    archive,
                    creation_date,
                    creation_time,
                    creation_time_within_second,
                    last_accessed_date,
                    last_modified_date,
                    last_modified_time,
                    size_and_cluster,
                } => match size_and_cluster {
                    FileSizeAndCluster::Empty => {
                        println!("  <empty>");
                    }
                    FileSizeAndCluster::NotEmpty {
                        size,
                        first_cluster_number,
                    } => {
                        let mut read_file = ReadFile::new(bpb, first_cluster_number, size);
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
                },
                _ => {}
            }
        }
        match next {
            Next::Continue(new_read_dir) => {
                read_dir = new_read_dir;
            }
            Next::Done => break,
        }
    }
}
