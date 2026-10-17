#!/usr/bin/env bash
# Checks packages:  scripts/check.sh [package...]   (default: all of them)
#
# For each package x, in x/:
#   1. bend PROOF.bend --check-only     must print ALL PROOFS CHECK
#   2. bend check.bend                  must print the file's #| lines
#   3. ref/run.sh, if present           exit 0 passes, 77 skips (a tool is
#                                       missing), anything else fails
# VERDICT=1 also runs PROOF.bend --verdict (needs Lean 4.34.0).
# BEND names the command to run (default: bend); it may be several words,
# e.g. BEND="bun ~/bend/bend2/main.ts".
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
read -r -a bend <<< "${BEND:-bend}"
export BEND_NO_TELEMETRY=1

if [ $# -eq 0 ]; then
  set -- $(cd "$root" && for d in */; do d=${d%/}; [ -f "$d/$d.bend" ] && echo "$d"; done)
fi

failed=()
note() { printf '  %-8s %s\n' "$1" "$2"; }
for p in "$@"; do
  dir="$root/$p"
  echo "== $p"
  if [ ! -f "$dir/$p.bend" ]; then note FAIL "no $p/$p.bend"; failed+=("$p"); continue; fi
  ok=1

  out=$(cd "$dir" && "${bend[@]}" PROOF.bend --check-only 2>&1)
  if [ "$(printf '%s\n' "$out" | head -1)" = "ALL PROOFS CHECK" ]; then note ok "proofs"
  else note FAIL "proofs"; printf '%s\n' "$out" | head -20 | sed 's/^/      /'; ok=0; fi

  if [ "${VERDICT:-0}" = 1 ]; then
    out=$(cd "$dir" && "${bend[@]}" PROOF.bend --verdict 2>&1)
    if [ "$(printf '%s\n' "$out" | head -1)" = "ALL PROOFS CHECK" ]; then note ok "verdict"
    else note FAIL "verdict"; printf '%s\n' "$out" | head -20 | sed 's/^/      /'; ok=0; fi
  fi

  want=$(grep '^#|' "$dir/check.bend" | sed 's/^#|//')
  got=$(cd "$dir" && "${bend[@]}" check.bend 2>&1)
  if [ "$got" = "$want" ]; then note ok "check.bend"
  else note FAIL "check.bend"; diff <(printf '%s\n' "$want") <(printf '%s\n' "$got") | head -20 | sed 's/^/      /'; ok=0; fi

  if [ -f "$dir/ref/run.sh" ]; then
    out=$(cd "$dir" && BEND="${bend[*]}" bash ref/run.sh 2>&1); code=$?
    case $code in
      0) note ok "ref: $(printf '%s\n' "$out" | tail -1)";;
      77) note skip "ref: $(printf '%s\n' "$out" | tail -1)";;
      *) note FAIL "ref"; printf '%s\n' "$out" | tail -20 | sed 's/^/      /'; ok=0;;
    esac
  fi
  [ $ok = 1 ] || failed+=("$p")
done

echo
if [ ${#failed[@]} -eq 0 ]; then echo "all $# packages pass"; else echo "failing: ${failed[*]}"; exit 1; fi
