#!/usr/bin/env bash
# Differential tests: the jitter core with SHA3-256 against model.py
# (gen.py), and SHAKE256 and the core with XDRBG-256 against hashlib and
# model_xdrbg.py (gen_xdrbg.py), written from Müller's paper, the XDRBG
# paper and SP 800-90B, on recorded and synthetic deltas. Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
summary=()
for t in "" _xdrbg; do
  n=$(python3 "gen$t.py" "${SEED:-2026}") || exit 1
  got=$("${bend[@]}" "cases$t.bend" 2>&1)
  if [ "$got" = "$(cat "expected$t.txt")" ]; then
    summary+=("$n")
  else
    echo "gen$t.py:"
    diff <(cat "expected$t.txt") <(printf '%s\n' "$got") | head -20
    exit 1
  fi
done
echo "$(IFS=';'; echo "${summary[*]}" | sed 's/;/; /g') match"
