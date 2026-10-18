#!/usr/bin/env bash
# Differential test: random rule sets and packets through the package and
# through an independent Python model of nftables evaluation (gen.py, which
# shares an author with the package; see the README). Exit 77 skips.
#
# When nft is installed and may talk to the kernel (it needs CAP_NET_ADMIN,
# which a user namespace gives), the rule sets gen.py could write in nft syntax are also given to
# `nft --check -f`, which validates their syntax only: comparing verdicts
# with the kernel's would need root and a network namespace to send the
# packets through.
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
# The probe is a one-table rule set in a regular file: nft refuses other
# files (/dev/null included), and an empty rule set never reaches the kernel.
# Without CAP_NET_ADMIN, nft runs in a new user and network namespace
# (unshare -rn), where it has that capability.
note="nft not installed: syntax check skipped"
if command -v nft > /dev/null; then
  probe=$(mktemp); trap 'rm -f "$probe"' EXIT
  printf 'table inet probe {\n}\n' > "$probe"
  nft=()
  if nft --check -f "$probe" > /dev/null 2>&1; then
    nft=(nft)
  elif unshare -rn nft --check -f "$probe" > /dev/null 2>&1; then
    nft=(unshare -rn nft)
  fi
  if [ ${#nft[@]} != 0 ]; then
    bad=0
    for f in nft/*.nft; do
      "${nft[@]}" --check -f "$f" > /dev/null 2>&1 || { echo "nft --check refuses $f:"; "${nft[@]}" --check -f "$f" 2>&1 | head -5; bad=1; }
    done
    [ $bad = 0 ] || exit 1
    note="nft --check accepts all $(ls nft/*.nft | wc -l) rule sets written in nft syntax"
  else
    note="nft cannot reach the kernel here: syntax check skipped"
  fi
fi
echo "$n match; $note"
