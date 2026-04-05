#!/usr/bin/env bash
IMG_NAME="fat_32.bin"
truncate -s 0 "$IMG_NAME"
truncate -s 36M "$IMG_NAME"
mkfs.vfat -F 32 -I -n "FAT32 DRIVE" "$IMG_NAME"

# For testing reading a file
mcopy -i $IMG_NAME ./test.txt "::TEST.TXT"

# For testing different file names
mcopy -i $IMG_NAME ./empty.txt "::A.B"
mcopy -i $IMG_NAME ./empty.txt "::A_really_long_file_name_which_should_take_up_multiple_long_file_name_slots"
mcopy -i $IMG_NAME ./empty.txt "::.HIDDEN"
mcopy -i $IMG_NAME ./empty.txt "::A B.C"
mcopy -i $IMG_NAME ./empty.txt "::A.B C"
mcopy -i $IMG_NAME ./empty.txt "::low_low.txt"
mcopy -i $IMG_NAME ./empty.txt "::low_up.TXT"
mcopy -i $IMG_NAME ./empty.txt "::UP_UP.TXT"
mcopy -i $IMG_NAME ./empty.txt "::UP_LOW.txt"
mcopy -i $IMG_NAME ./empty.txt "::Mixed.txt"

# For testing a directory that takes up more than 1 cluster
for i in {1..10}
do
    mcopy -i $IMG_NAME ./empty.txt "::empty_$i.txt"
done

mmd -i $IMG_NAME ::test_dir
mcopy -i $IMG_NAME ./test.txt "::test_dir/a"
mcopy -i $IMG_NAME ./empty.txt "::test_dir/b"

mdir -i fat_32.bin
