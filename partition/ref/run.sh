#!/usr/bin/env bash
# Differential test: MBR and GPT tables written by sfdisk and sgdisk, against
# what the package parses, validates and rebuilds (see gen.py). Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
for t in python3 sgdisk sfdisk truncate; do
  command -v "$t" > /dev/null || { echo "$t missing"; exit 77; }
done
read -r -a bend <<< "${BEND:-bend}"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
n=$(python3 gen.py "${SEED:-2026}" "$work") || exit 1
got=$("${bend[@]}" cases.bend 2>&1)
if [ "$got" = "$(cat expected.txt)" ]; then
  echo "$n match"
else
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
