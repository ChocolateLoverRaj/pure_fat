# `pure_fat`
[![Crates.io Version](https://img.shields.io/crates/v/pure_fat)](https://crates.io/crates/pure_fat)
[![docs.rs](https://img.shields.io/docsrs/pure_fat)](https://docs.rs/pure_fat/latest/pure_fat/)

A super flexible Rust library for parsing FAT file systems.

## Features
- `no_std` without `alloc`
- No `unsafe` code
- Very minimal
- Parse FAT12, FAT16, and FAT32  
- Read directories
- Read files
- Stream files

## Usage
I designed the API to not have async or any kind of callbacks. It can be used no matter how you access the disk, but the API is currently very un-ergonomic. See https://github.com/ChocolateLoverRaj/rust-esp32c3-examples/blob/ca5ab80f178cc1bf08281818cf2877f046f00d45/sd_card_speaker/src/main.rs for example usage.

## Use cases
- Reading folders and files in embedded
- Streaming a file to play a wav file from an SD card
