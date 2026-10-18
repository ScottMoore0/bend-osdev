#!/usr/bin/env bash
# Differential test: random operation sequences on the tree against an
# independent Python model (see gen.py). Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
python3 gen.py "${SEED:-2026}" > /dev/null || exit 1
got=$(mktemp)
trap 'rm -f "$got"' EXIT
"${bend[@]}" cases.bend > "$got" 2>&1
python3 gen.py --compare "$got"
