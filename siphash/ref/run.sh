#!/usr/bin/env bash
# Differential test: SipHash against the openssl command, HalfSipHash against
# ref/model.py (see gen.py). Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
command -v openssl > /dev/null || { echo "openssl missing"; exit 77; }
openssl mac -macopt hexkey:000102030405060708090a0b0c0d0e0f SIPHASH < /dev/null > /dev/null 2>&1 || { echo "openssl lacks SipHash"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 -B gen.py "${SEED:-2026}") || exit 1
got=$(for f in cases[0-9][0-9].bend; do "${bend[@]}" "$f" 2>&1; done)
if [ "$got" = "$(cat expected.txt)" ]; then
  echo "$n match"
else
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
