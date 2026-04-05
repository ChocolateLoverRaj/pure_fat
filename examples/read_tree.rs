use std::{
    fs::File,
    io::{Read, Seek, SeekFrom},
};

use hex_display::HexDisplayExt;
use pure_fat::{
    Bpb, Chars, FileSizeAndCluster, ParsedBpb, ParsedDirEntry, PartitionSegment,
    read_dir::{ProcessDataOutput, ReadDir},
    read_file::{NextOutput, ReadFile},
};
use sha2::{Digest, Sha256};
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
    // We store `None` elements to properly keep track of the indent level
    let mut read_dir_stack = vec![Some(ReadDir::new_root(bpb))];
    while let Some(next) = read_dir_stack.pop() {
        let read_dir = match next {
            Some(read_dir) => read_dir,
            None => continue,
        };
        let indent_level = read_dir_stack.len();
        let print_indents = || {
            for _ in 0..indent_level {
                print!("  ");
            }
        };
        let PartitionSegment { position, len } = read_dir.read_instruction();
        file.seek(SeekFrom::Start(position)).unwrap();
        let mut buffer = [Default::default(); ReadDir::MAX_READ_BUFFER_LEN.get() as usize];
        let buffer = &mut buffer[..len.get() as usize];
        file.read_exact(buffer).unwrap();
        let ProcessDataOutput { dir_entry, next } = read_dir.process_data(buffer).unwrap();
        read_dir_stack.push(next);
        if let Some(entry) = dir_entry {
            const N: usize = ParsedDirEntry::MAX_UTF8_LEN;
            let name = entry
                .chars()
                .map(Result::unwrap)
                .collect::<heapless::String<N>>();
            match entry {
                ParsedDirEntry::VolumeId { name: _ } => {
                    print_indents();
                    println!("{name:?} (volume id)");
                }
                ParsedDirEntry::File {
                    name: _,
                    size_and_cluster,
                    ..
                } => {
                    print_indents();
                    println!("{name:?} (file)");
                    match size_and_cluster {
                        FileSizeAndCluster::Empty => {
                            print_indents();
                            println!("  <empty>");
                        }
                        FileSizeAndCluster::NotEmpty {
                            size,
                            first_cluster_number,
                        } => {
                            let mut read_file = ReadFile::new(bpb, first_cluster_number, size);
                            let mut hasher = Sha256::new();
                            loop {
                                let PartitionSegment { position, len } = read_file.read_segment();
                                let mut buffer = [Default::default(); 512];
                                let mut bytes_read = 0;
                                file.seek(SeekFrom::Start(position)).unwrap();
                                while bytes_read < len.get() {
                                    let bytes_to_read =
                                        (len.get() - bytes_read).min(buffer.len() as u32);
                                    let buffer = &mut buffer[..bytes_to_read as usize];
                                    file.read_exact(buffer).unwrap();
                                    hasher.update(buffer);
                                    bytes_read += bytes_to_read;
                                }

                                let mut buffer = [Default::default();
                                    ReadFile::NEXT_INSTRUCTIONS_MAX_BUFFER_LEN.get() as usize];
                                let PartitionSegment { position, len } =
                                    read_file.next_instructions();
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
                            print_indents();
                            let digest = hasher.finalize();
                            let digest = digest.hex();
                            println!("  sha256: {digest}");
                        }
                    }
                }
                ParsedDirEntry::Dir {
                    name: _,
                    first_cluster_number,
                    ..
                } => {
                    print_indents();
                    println!("{name:?} (dir)");
                    read_dir_stack.push(Some(ReadDir::new(bpb, first_cluster_number)));
                }
                _ => {}
            }
        }
    }
}
