#!/usr/bin/env bash
# Differential test: the tables, the AML encodings and the interpreter
# against an independent reader, writer and evaluator written in Python from
# the specification (gen.py), on random inputs. When they can be had, also:
#   - real tables: every table in $ACPI_TABLES (a directory of acpidump -b
#     output), else in /sys/firmware/acpi/tables when it is readable (it
#     needs root), read through the registry, and the DSDT and SSDTs loaded,
#     with the devices they define compared with a static walk of the AML
#   - iasl (apt: acpica-tools): ASL programs compiled by it and run
# Exit 77 skips: python3 missing. Without iasl the Python cases still run,
# and the report says that the iasl part was not.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
args=("${SEED:-2026}")
dir="${ACPI_TABLES:-/sys/firmware/acpi/tables}"
if [ -d "$dir" ] && [ -r "$dir/DSDT" -o -n "${ACPI_TABLES:-}" ] 2> /dev/null; then args+=(--tables "$dir"); fi
have_iasl=0
if command -v iasl > /dev/null; then args+=(--iasl); have_iasl=1; fi
n=$(python3 gen.py "${args[@]}") || exit 1
got=$("${bend[@]}" runner.bend 2>&1)
if [ "$got" != "$(cat expected.txt)" ]; then
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
if [ $have_iasl = 0 ]; then
  echo "$n match; iasl missing (apt: acpica-tools), its programs not run"
else
  echo "$n match"
fi
