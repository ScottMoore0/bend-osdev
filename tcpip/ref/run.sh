#!/usr/bin/env bash
# Differential tests (exit 77 skips):
#   1. the TCP connection against ref/model.py, an independent Python model of
#      RFC 9293, 6298 and 5681, on random event scripts through sim.bend's
#      two-endpoint network (gen.py writes the scripts and the model's traces);
#   2. when a user and network namespace with a TAP device can be made without
#      privileges (unshare -rn, /dev/net/tun, ip, ping), the whole stack
#      against Linux's own: ping, UDP and TCP echo, both closes, an active
#      open, and 10% loss (linux.py, with peer.bend built natively).
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 gen.py "${SEED:-2026}" "${CASES:-100}") || exit 1
got=$("${bend[@]}" cases.bend 2>&1)
if [ "$got" != "$(cat expected.txt)" ]; then
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
model="model: $n match"
if unshare -rn true 2> /dev/null && [ -c /dev/net/tun ] && command -v ip > /dev/null && command -v ping > /dev/null; then
  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp"' EXIT
  if ! "${bend[@]}" peer.bend -o "$tmp/peer" > "$tmp/build.log" 2>&1; then
    tail -20 "$tmp/build.log"
    exit 1
  fi
  if ! out=$(timeout 300 unshare -rn python3 linux.py "$tmp/peer" 2>&1); then
    printf '%s\n' "$out" | tail -20
    exit 1
  fi
  linux="linux: $(printf '%s\n' "$out" | tail -1)"
else
  linux="linux: skipped (no unprivileged user namespace, /dev/net/tun, ip or ping)"
fi
echo "$model; $linux"
