#!/usr/bin/env bash
# Differential test: every construction against the Linux kernel's (through
# AF_ALG), Python's cryptography, hmac and hashlib, and ref/model.py's
# AEGIS-128 (which shares this package's author; see gen.py). Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
python3 -c "import cryptography" 2> /dev/null || { echo "python3 cryptography missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 -B gen.py "${SEED:-2026}") || exit 1
got=$("${bend[@]}" cases.bend 2>&1)
if [ "$got" = "$(cat expected.txt)" ]; then
  echo "$n match"
else
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
