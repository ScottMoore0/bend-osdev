#!/usr/bin/env bash
# Checks packages:  scripts/check.sh [package...]   (default: all of them)
#
# For each package x, in x/:
#   1. bend PROOF.bend --check-only     must print ALL PROOFS CHECK; so must
#                                       each further proof file
#                                       PROOF_<part>.bend, if the package has
#                                       any (CONVENTIONS.md, Laws)
#   2. bend check.bend                  must print the file's #| lines
#   3. ref/run.sh, if present           exit 0 passes, 77 skips (a tool is
#                                       missing), anything else fails
# VERDICT=1 also runs each proof file with --verdict (needs Lean 4.34.0).
# BEND names the command to run (default: bend); it may be several words,
# e.g. BEND="bun ~/bend/bend2/main.ts".
#
# Programs (check.bend, the ref tests' cases) run as native binaries through
# scripts/bend-run.sh, which needs clang 14 or newer ($CC or on PATH);
# BEND_LANE=js runs them on bend's JavaScript lane instead. A program the C
# backend refuses (bendlang/bend#1069) runs on the JavaScript lane, and the
# report says so.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
read -r -a bend <<< "${BEND:-bend}"
export BEND_NO_TELEMETRY=1
export BEND_CMD="${bend[*]}"
run=(bash "$root/scripts/bend-run.sh")
export BEND_RUN_LOG=$(mktemp)
trap 'rm -f "$BEND_RUN_LOG"' EXIT

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

  # PROOF.bend, then the package's further proof files (PROOF_<part>.bend),
  # each checked in a process of its own
  for pf in PROOF.bend $(cd "$dir" && ls PROOF_*.bend 2>/dev/null); do
    what=""; [ "$pf" = PROOF.bend ] || what=" ${pf%.bend}"
    out=$(cd "$dir" && "${bend[@]}" "$pf" --check-only 2>&1)
    if [ "$(printf '%s\n' "$out" | head -1)" = "ALL PROOFS CHECK" ]; then note ok "proofs$what"
    else note FAIL "proofs$what"; printf '%s\n' "$out" | head -20 | sed 's/^/      /'; ok=0; fi

    if [ "${VERDICT:-0}" = 1 ]; then
      out=$(cd "$dir" && "${bend[@]}" "$pf" --verdict 2>&1)
      if [ "$(printf '%s\n' "$out" | head -1)" = "ALL PROOFS CHECK" ]; then note ok "verdict$what"
      else note FAIL "verdict$what"; printf '%s\n' "$out" | head -20 | sed 's/^/      /'; ok=0; fi
    fi
  done

  want=$(grep '^#|' "$dir/check.bend" | sed 's/^#|//')
  got=$(cd "$dir" && "${run[@]}" check.bend 2>&1)
  if [ "$got" = "$want" ]; then note ok "check.bend"
  else note FAIL "check.bend"; diff <(printf '%s\n' "$want") <(printf '%s\n' "$got") | head -20 | sed 's/^/      /'; ok=0; fi

  if [ -f "$dir/ref/run.sh" ]; then
    out=$(cd "$dir" && BEND="${run[*]}" bash ref/run.sh 2>&1); code=$?
    case $code in
      0) note ok "ref: $(printf '%s\n' "$out" | tail -1)";;
      77) note skip "ref: $(printf '%s\n' "$out" | tail -1)";;
      *) note FAIL "ref"; printf '%s\n' "$out" | tail -20 | sed 's/^/      /'; ok=0;;
    esac
  fi
  if [ -s "$BEND_RUN_LOG" ]; then
    note js "on the JavaScript lane: $(sort -u "$BEND_RUN_LOG" | tr '
' ' ')"
    : > "$BEND_RUN_LOG"
  fi
  [ $ok = 1 ] || failed+=("$p")
done

echo
if [ ${#failed[@]} -eq 0 ]; then echo "all $# packages pass"; else echo "failing: ${failed[*]}"; exit 1; fi
