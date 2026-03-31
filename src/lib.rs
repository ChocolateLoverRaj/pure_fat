//! # FAT format
//! This will be about FAT12, FAT16, FAT32, and ExFAT. This driver currently only supports FAT32
//! and the information below might only be true for FAT32.
//!
//! The first 512B of all FAT partitions are the BPB (BIOS Parameter Block). There are some common
//! fields, and then there are fields that are specific to a type of FAT. The BPB tells you which
//! FAT type it is, and information like the total size and teh size of a cluster.
//!
//! Each file is stored in clusters. This means that a 1 B file will take up one entire cluster.
//! Each cluster has a number which is basically the index of the cluster, and all clusters are
//! stored consecutively in the partition. If a file needs multiple clusters, then they don't have
//! to be consecutive clusters. The File Allocation Table (FAT) stores which cluster goes after
//! a cluster, forming a linked-list for each file.
//!
//! A directory is just like a file but it has a special data structure to represent files it
//! contains. A directory is basically an array of slots. Each slot has a constant len. Each slot
//! can describe the partition label, a sub-directory, or a file inside the directory. Each slot
//! contains the name of the label / dir / file. If the name is too long, then multiple slots are
//! used to store the name. The BPB tells you where the root directory is stored.
//!
//! The overall structure of a FAT partition is:
//! - BPB
//! - File Allocation Table
//! - Files (including root directory)
//!
//! Sources:
//! - <https://wiki.osdev.org/FAT>
//! - <https://en.wikipedia.org/wiki/File_Allocation_Table>
//! - <https://en.wikipedia.org/wiki/Design_of_the_FAT_file_system>
//! - <https://people.cs.umass.edu/~liberato/courses/2019-spring-compsci365/lecture-notes/11-fats-and-directory-entries/>
#![no_std]
mod bpb;
pub use bpb::*;
mod dir_entry;
pub use dir_entry::*;
mod parsed_bpb;
pub mod read_file;
pub use parsed_bpb::*;
pub mod read_dir;
