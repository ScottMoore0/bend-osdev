#!/usr/bin/env bash
# Differential test: the decoder against Python's lzma module and the xz tool
# (see gen.py). Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
command -v xz > /dev/null || { echo "xz missing"; exit 77; }
python3 -c "import lzma" 2> /dev/null || { echo "python3 lzma missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 gen.py "${SEED:-2026}") || exit 1
got=$(for f in cases[0-9][0-9].bend; do "${bend[@]}" "$f" 2>&1; done)
if [ "$got" = "$(cat expected.txt)" ]; then
  echo "$n match"
else
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
