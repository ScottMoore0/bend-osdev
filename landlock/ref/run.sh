#!/usr/bin/env bash
# Differential test: the package against an independent Python model on
# random rulesets, and against the running kernel's Landlock where it has it
# (see gen.py). Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 gen.py "${SEED:-2026}") || exit 1
got=$(for f in cases-*.bend; do "${bend[@]}" "$f" 2>&1; done)
if [ "$got" = "$(cat expected.txt)" ]; then
  echo "$n: match"
else
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
