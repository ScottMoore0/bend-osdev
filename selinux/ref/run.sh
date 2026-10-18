#!/usr/bin/env bash
# Differential test: random small CIL policies and queries, through the
# package and through the independent Python model in gen.py. When secilc is
# installed (apt package secilc), each generated policy is also compiled by
# it, as a black box: it must accept exactly the policies the package loads
# (it refuses the others for the reason the package gives: a misused
# constraint operand, a name transition in a booleanif, a neverallow
# violation, conflicting transitions). Exit 77 skips.
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
note="secilc not installed"
if command -v secilc > /dev/null; then
  bad=0; k=0
  for f in cil/pol*.cil; do
    want=$(grep -c "^policy $k: loaded" expected.txt)
    if secilc -o /dev/null -f /dev/null "$f" > /dev/null 2>&1; then have=1; else have=0; fi
    if [ "$want" != "$have" ]; then echo "secilc disagrees on $f (package loads: $want, secilc accepts: $have)"; bad=1; fi
    k=$((k + 1))
  done
  [ $bad = 0 ] || exit 1
  note="secilc agrees on $k policies"
fi
echo "$n match ($note)"
