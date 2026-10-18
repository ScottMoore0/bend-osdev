#!/usr/bin/env bash
# Differential test (see gen.py): the package's decoder against frames from
# an independent writer and from the lz4 tool, and corruptions of them; the
# package's compressor checked by an independent decoder and by `lz4 -d`.
# Exit 77 skips: python3 missing, or the lz4 tool missing (then the checks
# that need no tool still run, and must pass).
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 gen.py "${SEED:-2026}") || exit 1
got=$("${bend[@]}" cases.bend 2>&1)
if [ "$got" != "$(cat expected.txt)" ]; then
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
: > ccases.out
for f in ccases[0-9][0-9].bend; do "${bend[@]}" "$f" >> ccases.out 2>&1; done
m=$(python3 gen.py verify ccases.out) || { printf '%s\n' "$m" | tail -20; tail -3 ccases.out | cut -c1-200; exit 1; }
rm -f ccases.out
# the LZ4HC ratios first, then the summary line
printf '%s\n' "$m" | sed '$d'
m=$(printf '%s\n' "$m" | tail -1)
if ! command -v lz4 > /dev/null; then
  echo "$n match; $m; lz4 tool missing, its checks skipped"
  exit 77
fi
echo "$n match; $m"
