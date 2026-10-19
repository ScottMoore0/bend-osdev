#!/usr/bin/env bash
# Differential test (see gen.py): the decoder against Python's zlib module
# and the gzip tool on streams they make, streams built by hand and damaged
# copies; the compressor's streams decoded by both. Exit 77 skips: python3
# or its zlib module missing.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
python3 -c "import zlib, gzip" 2> /dev/null || { echo "python3 zlib module missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 gen.py "${SEED:-2026}") || exit 1
mapfile -t args < args.txt
got=$("${bend[@]}" runner.bend "${args[@]}" 2>&1 | sed "s/ error .*/ error/")
if [ "$got" != "$(cat expected.txt)" ]; then
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
m=$(python3 gen.py verify) || { printf '%s\n' "$m"; exit 1; }
rm -rf work args.txt expected.txt
echo "$n cases match; $m"
