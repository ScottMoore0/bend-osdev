#!/usr/bin/env bash
# Differential test: Fdt.build, Fdt.parse, the property decoders and the
# lookups against an independent Python writer and reader (gen.py), and
# against dtc and fdtdump (device-tree-compiler) when they are installed.
# Exit 77 skips: python3 missing, or (after the Python cases pass) dtc or
# fdtdump missing.
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
printf '%s\n' "$got" > output.txt
p=$(python3 gen.py --post output.txt) || { echo "$p"; exit 1; }
echo "$n; $p"
if ! command -v dtc > /dev/null || ! command -v fdtdump > /dev/null; then
  echo "the Python cases match; dtc or fdtdump missing (apt: device-tree-compiler)"
  exit 77
fi
