#!/usr/bin/env bash
# The size measurement (not run by check.sh): a 64 MB image file written
# by Python, then every block read through a FileDev (measure.bend, built
# natively), timed with peak RAM, and the byte sum and hash compared with
# Python's; then every block rewritten in place through a FileRW
# (measure_rw.bend), timed, and the file checked by Python. Usage:
# measure.sh [dir] [MB] [block size]; the image goes in dir (default
# $TMPDIR or /tmp; keep it off slow mounts).
set -uo pipefail
cd "$(dirname "$0")"
dir=${1:-${TMPDIR:-/tmp}}; mb=${2:-64}; bs=${3:-4096}
img="$dir/bend-osdev-iodev-measure.img"
read -r -a bend <<< "${BEND_CMD:-bend}"
want=$(python3 - "$img" "$mb" "$bs" <<'PY'
import random, sys
path, mb = sys.argv[1], int(sys.argv[2])
data = random.Random(2026).randbytes(mb << 20)
open(path, "wb").write(data)
h = 0
for b in data:
    h = (h * 31 + b) & 0xFFFFFFFF
print("blocks %d bytes %d sum %d hash %d" % (len(data) // int(sys.argv[3] if len(sys.argv) > 3 else 4096), len(data) & 0xFFFFFFFF, sum(data) & 0xFFFFFFFF, h))
PY
)
"${bend[@]}" measure.bend -o "$dir/bend-osdev-iodev-measure" > /dev/null || exit 1
for mode in count sum; do
  got=$( { /usr/bin/time -f "%es %MKB" "$dir/bend-osdev-iodev-measure" "$img" "$bs" "$mode"; } 2>&1 )
  echo "$mode: $got" | tr '\n' ' '; echo
done
echo "python: $want"
# every block rewritten in place through FileRW (measure_rw.bend), block n
# filled with n mod 256, and the file checked by Python
"${bend[@]}" measure_rw.bend -o "$dir/bend-osdev-iodev-measure-rw" > /dev/null || exit 1
got=$( { /usr/bin/time -f "%es %MKB" "$dir/bend-osdev-iodev-measure-rw" "$img" "$bs"; } 2>&1 )
echo "rewrite: $got" | tr '\n' ' '; echo
python3 - "$img" "$bs" <<'PY'
import sys
path, bs = sys.argv[1], int(sys.argv[2])
data = open(path, "rb").read()
bad = [i for i in range(0, len(data), bs) if data[i:i + bs] != bytes([(i // bs) & 255]) * len(data[i:i + bs])]
print("python: rewrite " + ("matches" if not bad else "differs at block %d" % (bad[0] // bs)))
PY
rm -f "$img" "$dir/bend-osdev-iodev-measure" "$dir/bend-osdev-iodev-measure-rw"
