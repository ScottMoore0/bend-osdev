#!/usr/bin/env bash
# Differential test (see gen.py): the package's decoder against frames from
# libzstd, the zstd tool, an independent writer (zstdref.py) and hand-built
# frames, and corruptions of them; the package's compressor checked by
# zstdref.py's decoder, libzstd and `zstd -d`. libzstd and the zstd tool
# are used when present; without them the checks against zstdref.py still
# run. Exit 77 skips: python3 missing.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 gen.py "${SEED:-2026}") || exit 1
got=$("${bend[@]}" cases.bend cases.bin 2>&1)
if [ "$got" != "$(cat expected.txt)" ]; then
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
"${bend[@]}" cases.bend ccases.bin > ccases.out 2>&1
m=$(python3 gen.py verify ccases.out) || { printf '%s\n' "$m" | tail -20; exit 1; }
rm -f ccases.out
echo "$n match; $m"
