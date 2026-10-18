#!/usr/bin/env bash
# Differential test: the package against an independent FAT reader and
# image builder (gen.py, written from the specification), fsck.fat, and
# images made by mkfs.fat and filled by mtools (see gen.py); then the
# writer against an independent model (wgen.py), fsck.fat and mtools.
# Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
export PATH="$PATH:/usr/sbin:/sbin" PYTHONDONTWRITEBYTECODE=1
for t in python3 mkfs.fat fsck.fat mmd mcopy mdir mtype; do
  command -v "$t" > /dev/null || { echo "$t missing (apt: dosfstools mtools)"; exit 77; }
done
read -r -a bend <<< "${BEND:-bend}"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
n=$(python3 gen.py "${SEED:-2026}" "$work") || exit 1
got=$(for f in cases-*.bend; do "${bend[@]}" "$f" 2>&1; done)
if [ "$got" != "$(cat expected.txt)" ]; then
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi

m=$(python3 wgen.py "${SEED:-2026}" "$work") || exit 1
got=$("${bend[@]}" wcases.bend 2>&1)
if [ "$got" != "$(cat wexpected.txt)" ]; then
  diff <(cat wexpected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
c=$(python3 wgen.py check "$work") || { printf '%s\n' "$c"; exit 1; }
echo "read: $n match; write: $m match, $c"
