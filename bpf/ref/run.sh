#!/usr/bin/env bash
# Differential test: the interpreter, the validator and seccomp against an
# independent implementation (gen.py) on random programs, and seccomp filters
# against the running Linux kernel. Exit 77 skips: python3 is missing, or
# installing a seccomp filter is not permitted (the rest still runs).
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
out=$(python3 gen.py "${SEED:-2026}"); code=$?
printf '%s\n' "$out" | tail -n +2
case $code in 0|3) ;; *) exit 1;; esac
n=$(printf '%s\n' "$out" | head -1)
got=$("${bend[@]}" cases.bend 2>&1)
if [ "$got" != "$(cat expected.txt)" ]; then
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
if [ $code = 3 ]; then
  echo "$n match; kernel skipped"
  exit 77
fi
echo "$n match; kernel agrees"
