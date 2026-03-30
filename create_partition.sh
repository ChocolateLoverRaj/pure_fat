#!/usr/bin/env bash
IMG_NAME="fat_32.bin"
truncate -s 0 "$IMG_NAME"
truncate -s 36M "$IMG_NAME"
mkfs.vfat -F 32 -I -n "FAT32 DRIVE" "$IMG_NAME"
mcopy -i $IMG_NAME ./test.txt ::test.txt
mmd -i $IMG_NAME ::test_dir
mdir -i fat_32.bin
