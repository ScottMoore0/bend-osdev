#!/usr/bin/env bash
# Differential test: the reader against readelf and against an independent
# reader written from the specification, on ELF files built by gcc and by
# hand (see gen.py). Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
command -v readelf > /dev/null || { echo "readelf missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
n=$(python3 gen.py "${SEED:-2026}" "$tmp") || exit 1
got=$("${bend[@]}" cases.bend 2>&1)
if [ "$got" = "$(cat expected.txt)" ]; then
  echo "$n match"
else
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
