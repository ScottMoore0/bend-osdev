#!/usr/bin/env bash
# Differential test: every cipher against implementations outside this
# package (Python's cryptography where it has the cipher, the openssl
# command for ARIA, and the specification models in model.py), on random keys, blocks and messages
# (see gen.py). Exit 77 skips (no python3).
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
python3 -c "import cryptography" 2> /dev/null || echo "python3 cryptography missing: comparing with model.py only"
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 -B gen.py "${SEED:-2026}") || exit 1
got=$("${bend[@]}" cases.bend 2>&1)
if [ "$got" = "$(cat expected.txt)" ]; then
  echo "$n match"
else
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
