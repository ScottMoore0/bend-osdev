#!/usr/bin/env bash
# Differential test: bend-kit-hash through the adapter, and bend-osdev's own
# CRC-32, Adler-32, XXH64 and SipHash-1-3 beside it, against Python's zlib,
# the lz4, zstd and openssl commands, and ref/model.py (see gen.py). Exit 77
# skips.
set -uo pipefail
cd "$(dirname "$0")"
for t in python3 lz4 zstd openssl; do
  command -v $t > /dev/null || { echo "$t missing"; exit 77; }
done
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
