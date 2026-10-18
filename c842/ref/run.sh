#!/usr/bin/env bash
# Differential test (see gen.py): the package against the recorded Linux
# vectors (linux-vectors.txt) in both directions, and against model.py.
# Exit 77 skips: only when python3 is missing.
#
# The Linux vectors are data from one run of Linux's 842 as a black box. To
# record them again (optional; needs the QEMU VM and test module outside
# this repository, see ../README.md):
#   bend-audit/kmod842/record.py requests REQ
#   bend-audit/kmod842/run-vm.sh REQ OUT
#   bend-audit/kmod842/record.py vectors REQ OUT > linux-vectors.txt
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 gen.py "${SEED:-2026}") || { echo "gen.py failed: $n"; exit 1; }
got=$("${bend[@]}" runner.bend 2>&1)
if [ "$got" != "$(cat expected.txt)" ]; then
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20 | cut -c1-200
  exit 1
fi
rm -f cases.bin expected.txt
echo "$n match"
