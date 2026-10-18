#!/usr/bin/env bash
# Runs a Bend program natively:  scripts/bend-run.sh <file.bend> [args]
#
# `bend file.bend` checks the file, then runs main on its JavaScript lane.
# That lane is far slower, uses several times the memory, and overflows its
# stack at some tens of thousands of nested calls, so the checks run programs
# as native binaries instead: this builds file.bend with `bend -o` (which
# needs clang 14 or newer, found through $CC or on PATH) and runs the binary.
#
# Checks (--check-only, --verdict) and builds (-o) pass straight through to
# bend. BEND_CMD names the bend command (default: bend; it may be several
# words). BEND_LANE=js runs on the JavaScript lane instead, as `bend
# file.bend` does.
set -uo pipefail
read -r -a bend <<< "${BEND_CMD:-bend}"
case " $* " in
  *" --check-only "*|*" --verdict "*|*" -o "*) exec "${bend[@]}" "$@";;
esac
if [ "${BEND_LANE:-native}" = js ]; then exec "${bend[@]}" "$@"; fi
file=$1; shift
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
# (in its own shell, so that a build killed for memory is reported here, not
# by the shell on this script's stderr)
bash -c '"$@" > "$0" 2>&1' "$tmp/build.log" "${bend[@]}" "$file" -o "$tmp/prog" 2> /dev/null
code=$?
if [ $code -ne 0 ]; then
  # Two builds fall back to the JavaScript lane, recorded in $BEND_RUN_LOG:
  # code the C backend refuses (more than 247 live one-word values in one
  # segment, bendlang/bend#1069; W64-heavy code hits it), and a build killed
  # for memory (a very large generated case file)
  why=""
  if grep -q "arity over 247" "$tmp/build.log"; then why="#1069"
  elif [ $code -ge 128 ]; then why="build killed"; fi
  if [ -n "$why" ]; then
    if [ -n "${BEND_RUN_LOG:-}" ]; then echo "$file ($why)" >> "$BEND_RUN_LOG"; fi
    exec "${bend[@]}" "$file" "$@"
  fi
  cat "$tmp/build.log"
  exit 1
fi
"$tmp/prog" "$@"
