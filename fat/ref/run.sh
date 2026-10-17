#!/usr/bin/env bash
# Differential test: the package against an independent FAT reader and
# image builder (gen.py, written from the specification), fsck.fat, and
# images made by mkfs.fat and filled by mtools (see gen.py). Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
export PATH="$PATH:/usr/sbin:/sbin"
for t in python3 mkfs.fat fsck.fat mmd mcopy mdir; do
  command -v "$t" > /dev/null || { echo "$t missing (apt: dosfstools mtools)"; exit 77; }
done
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 gen.py "${SEED:-2026}") || exit 1
got=$("${bend[@]}" cases.bend 2>&1)
if [ "$got" = "$(cat expected.txt)" ]; then
  echo "$n match"
else
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
