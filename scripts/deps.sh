#!/usr/bin/env bash
# Checks each package's imports against its DEPS file:
#   scripts/deps.sh [package...]   (default: all of them)
#
# A package may import Base, its own files, the bend-osdev packages listed in
# its DEPS (by directory name), and the hub packages listed there
# (name@version). Imports in ref/ (test generators' output) are not checked.
# Also fails on a DEPS line nothing imports, so DEPS stays exact.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
if [ $# -eq 0 ]; then
  set -- $(cd "$root" && for d in */; do d=${d%/}; [ -f "$d/$d.bend" ] && echo "$d"; done)
fi
bad=0
for p in "$@"; do
  dir="$root/$p"
  if [ ! -f "$dir/DEPS" ]; then echo "$p: no DEPS file"; bad=1; continue; fi
  allowed=$(grep -v '^\s*\(#\|$\)' "$dir/DEPS" | sort -u)
  used=$(find "$dir" -name '*.bend' -not -path "$dir/ref/*" -exec grep -hE '^import ' {} + \
    | sed -E 's/^import +//; s/ +as .*//' \
    | while read -r m; do
        case "$m" in
          Base) ;;
          ./*) ;;
          ../*) m=${m#../}; echo "${m%%/*}";;
          *@*) echo "${m%%/*}";;
          *) echo "?$m";;
        esac
      done | sort -u)
  extra=$(comm -23 <(printf '%s\n' "$used" | grep .) <(printf '%s\n' "$allowed" | grep .))
  unused=$(comm -13 <(printf '%s\n' "$used" | grep .) <(printf '%s\n' "$allowed" | grep .))
  if [ -n "$extra" ]; then echo "$p: imports not in DEPS: $(echo $extra)"; bad=1; fi
  if [ -n "$unused" ]; then echo "$p: DEPS lists unused: $(echo $unused)"; bad=1; fi
  [ -z "$extra$unused" ] && echo "$p: ok ($(echo ${used:-none}))"
done
exit $bad
