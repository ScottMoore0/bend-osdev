#!/usr/bin/env bash
# Differential tests, both seeded by $SEED (default 2026). Exit 77 skips.
#
# Reading (gen.py): images written by mke2fs (ext2, ext3, ext4, with and
# without metadata_csum, 1 KiB and 4 KiB blocks) from random trees, read
# through the package and compared with the trees and with debugfs; and
# corrupted images, which must be refused.
#
# Writing (wgen.py): random sequences of operations run through the
# package's writer on images made by mke2fs and by the package's own mkfs,
# compared with a model written in Python, and every image written checked
# with e2fsck -fn and read back with debugfs.
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
if [ "$got" != "$(cat expected.txt)" ]; then
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi

mkdir "$work/w"
python3 wgen.py gen "${SEED:-2026}" "$work/w" > /dev/null || exit 1
"${bend[@]}" wmain.bend "$work/w/cases.txt" > "$work/w/out.txt" 2> "$work/w/err.txt" || { tail -20 "$work/w/err.txt"; exit 1; }
w=$(python3 wgen.py check "$work/w" "$work/w/out.txt") || { printf '%s\n' "$w" | tail -20; exit 1; }
echo "reading: $n match; writing: $w"
