use std::{fs::File, io::Read};

use pure_fat::Bpb;
use zerocopy::transmute;

fn main() {
    let mut file = File::open("fat_32.bin").unwrap();
    let mut buffer = [Default::default(); size_of::<Bpb>()];
    file.read_exact(&mut buffer).unwrap();
    let bpb: Bpb = transmute!(buffer);
    let fat_type = bpb.fat_type();
    println!("{fat_type:?}");
}
