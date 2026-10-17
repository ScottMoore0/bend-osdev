#!/usr/bin/env bash
# Differential test: images written by mke2fs (ext2, ext3, ext4, with and
# without metadata_csum, 1 KiB and 4 KiB blocks) from random trees, read
# through the package and compared with the trees and with debugfs; and
# corrupted images, which must be refused (see gen.py). Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
PATH=$PATH:/usr/sbin:/sbin  # where e2fsprogs lives
for t in python3 mke2fs debugfs e2fsck dumpe2fs tune2fs; do
  command -v "$t" > /dev/null || { echo "$t missing"; exit 77; }
done
read -r -a bend <<< "${BEND:-bend}"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
n=$(python3 gen.py "${SEED:-2026}" "$work") || exit 1
got=$(for f in cases-*.bend; do "${bend[@]}" "$f" 2>&1; done)
if [ "$got" = "$(cat expected.txt)" ]; then
  echo "$n match"
else
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
