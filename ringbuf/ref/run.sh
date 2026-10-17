#!/usr/bin/env bash
# Differential test: random operation sequences against Python's
# collections.deque (see gen.py). Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 gen.py "${SEED:-2026}") || exit 1
got=$("${bend[@]}" cases.bend 2>&1)
if [ "$got" = "$(cat expected.txt)" ]; then
  echo "$n match"
else
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
