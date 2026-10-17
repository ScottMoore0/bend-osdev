#!/usr/bin/env bash
# Differential test: the reader against an independent builder and reader
# written here from the specifications (gen.py), on images it builds, and
# on images genisoimage and xorriso build (checked against their source
# trees and isoinfo). Exit 77 skips: without python3 nothing runs; without
# genisoimage, xorriso or isoinfo the independent part runs and must match,
# and the run is reported as a skip, since the third-party part is missing.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
missing=""
for t in genisoimage xorriso isoinfo; do command -v "$t" > /dev/null || missing="$missing $t"; done
read -r -a bend <<< "${BEND:-bend}"
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
n=$(python3 gen.py "${SEED:-2026}" "$tmp") || exit 1
got=$("${bend[@]}" cases.bend 2>&1)
if [ "$got" = "$(cat expected.txt)" ]; then
  if [ -n "$missing" ]; then echo "$n match; missing:$missing"; exit 77; fi
  echo "$n match"
else
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
