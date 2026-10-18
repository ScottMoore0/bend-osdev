#!/usr/bin/env bash
# Differential test (see gen.py): random files changed in place through
# the effects, against Python's own seek, read and write of a copy of each
# file; one of them a sparse file over 4 GiB. The files live in a fresh
# directory under $TMPDIR (default /tmp), removed afterwards.
# Exit 77 skips: python3 missing.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
work=$(mktemp -d "${TMPDIR:-/tmp}/bend-osdev-fileio-ref.XXXXXX") || exit 1
trap 'rm -rf "$work"' EXIT
n=$(python3 gen.py "${SEED:-2026}" "$work") || exit 1
got=$("${bend[@]}" cases.bend "$work/ops.bin" 2>&1)
if [ "$got" != "$(cat "$work/expected.txt")" ]; then
  diff <(cat "$work/expected.txt") <(printf '%s\n' "$got") | head -20
  exit 1
fi
python3 gen.py --compare "$work" || exit 1
echo "$n match, every file byte for byte"
