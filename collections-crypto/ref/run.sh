#!/usr/bin/env bash
# Differential test: collections-crypto through crypto's interfaces against
# Python's cryptography and hashlib, and gen.py's models where Python has no
# implementation (see gen.py). Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
python3 -c "import cryptography" 2> /dev/null || { echo "python3 cryptography missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 -B gen.py "${SEED:-2026}") || exit 1
got=$(for f in cases[0-9][0-9].bend; do "${bend[@]}" "$f" 2>&1; done)
if [ "$got" = "$(cat expected.txt)" ]; then
  echo "$n match"
else
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
