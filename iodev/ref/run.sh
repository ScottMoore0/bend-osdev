#!/usr/bin/env bash
# Differential test (see gen.py): random image files read and written
# through FileDev (under an overlay), MemDev and ImgDev, against Python's
# own reads of the same files; every saved image compared with Python's.
# Exit 77 skips: python3 missing.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 gen.py "${SEED:-2026}") || exit 1
got=$("${bend[@]}" cases.bend work/ops.bin 2>&1)
if [ "$got" != "$(cat expected.txt)" ]; then
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
while read -r out exp; do
  cmp -s "$out" "$exp" || { echo "saved image $out differs from $exp"; exit 1; }
done < saves.txt
echo "$n match"
