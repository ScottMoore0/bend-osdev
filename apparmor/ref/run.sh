#!/usr/bin/env bash
# Differential test: random policies and queries against an independent
# Python model, and apparmor_parser as a black-box syntax check when it is
# installed (see gen.py). Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 gen.py "${SEED:-2026}" "${POLICIES:-20}") || { printf '%s\n' "$n"; exit 1; }
got=$(for f in cases-*.bend; do "${bend[@]}" "$f" 2>&1; done)
if [ "$got" = "$(cat expected.txt)" ]; then
  printf '%s\n' "$n" | tail -1
else
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
