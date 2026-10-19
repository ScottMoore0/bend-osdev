#!/usr/bin/env bash
# Differential test: oid against openssl and Python cryptography
# (see gen.py). Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
command -v openssl > /dev/null || { echo "openssl missing"; exit 77; }
python3 -c "import cryptography" 2> /dev/null || { echo "python3 cryptography missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 gen.py "${SEED:-2026}") || { echo "$n"; exit 1; }
got=$("${bend[@]}" cases.bend 2>&1)
if [ "$got" = "$(cat expected.txt)" ]; then
  echo "$n match"
else
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
