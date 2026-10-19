#!/usr/bin/env bash
# Tests the clock effect against Python's reading of CLOCK_MONOTONIC (see
# check.py), natively and on the JavaScript lane (when BEND runs programs
# through scripts/bend-run.sh, which honours BEND_LANE). Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
now() { python3 -c 'import time; print(time.clock_gettime_ns(time.CLOCK_MONOTONIC))'; }
res=()
for lane in native js; do
  before=$(now)
  out=$(BEND_LANE=$lane "${bend[@]}" stamps.bend 2>&1)
  after=$(now)
  r=$(printf '%s\n' "$out" | python3 -B check.py "$lane" "$before" "$after") || { echo "$r"; printf '%s\n' "$out" | head -5; exit 1; }
  res+=("$r")
done
echo "${res[0]}; ${res[1]}"
