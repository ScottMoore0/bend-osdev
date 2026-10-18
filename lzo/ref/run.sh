#!/usr/bin/env bash
# Differential test (see gen.py): the package's decoder against streams and
# lzop files from an independent writer (and from the lzop tool, when
# installed), and corruptions of them; the package's compressor checked by
# an independent decoder (and by `lzop -d`, when installed).
# Exit 77 skips: only when python3 is missing. Without the lzop tool every
# check that needs no tool still runs, and must pass.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 gen.py "${SEED:-2026}") || exit 1
: > cases.out
for f in cases[0-9][0-9].bend; do "${bend[@]}" "$f" >> cases.out 2>&1; done
if ! diff -q expected.txt cases.out > /dev/null; then
  diff expected.txt cases.out | head -20 | cut -c1-200
  exit 1
fi
: > ccases.out
for f in ccases[0-9][0-9].bend; do "${bend[@]}" "$f" >> ccases.out 2>&1; done
m=$(python3 gen.py verify ccases.out) || { printf '%s\n' "$m" | tail -20; tail -3 ccases.out | cut -c1-200; exit 1; }
rm -f cases.out ccases.out
if command -v lzop > /dev/null; then
  echo "$n match; $m"
else
  echo "$n match; $m; lzop tool missing, its checks skipped"
fi
