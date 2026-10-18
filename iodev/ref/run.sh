#!/usr/bin/env bash
# Differential test (see gen.py): random image files read and written
# through FileDev (under an overlay), MemDev and ImgDev, against Python's
# own reads of the same files, and through FileRW on bend-osdev-fileio's
# effects, written in place, against Python's own writes to a copy; every
# saved or written image compared with Python's. Then a sparse image over
# 4 GiB through FileRW (big.bend), in a fresh directory under $TMPDIR
# (default /tmp), removed afterwards; it is left out where the file system
# keeps no sparse files.
# Exit 77 skips: python3 missing.
set -uo pipefail
cd "$(dirname "$0")"
command -v python3 > /dev/null || { echo "python3 missing"; exit 77; }
read -r -a bend <<< "${BEND:-bend}"
n=$(python3 gen.py "${SEED:-2026}") || exit 1
got=$("${bend[@]}" cases.bend work/ops.bin 2>&1)
if [ "$got" != "$(cat expected.txt)" ]; then
  diff <(cat expected.txt) <(printf '%s\n' "$got") | head -20
  exit 1
fi
while read -r out exp; do
  cmp -s "$out" "$exp" || { echo "saved image $out differs from $exp"; exit 1; }
done < saves.txt

big=$(mktemp -d "${TMPDIR:-/tmp}/bend-osdev-iodev-big.XXXXXX") || exit 1
trap 'rm -rf "$big"' EXIT
m=$(python3 gen.py --big "${SEED:-2026}" "$big"); code=$?
case $code in
  0)
    got=$("${bend[@]}" big.bend "$big/big-ops.bin" 2>&1)
    if [ "$got" != "$(cat "$big/big-expected.txt")" ]; then
      diff <(cat "$big/big-expected.txt") <(printf '%s\n' "$got") | head -20
      exit 1
    fi
    python3 gen.py --same "$big/big.img" "$big/big.twin" || exit 1
    m="$m match";;
  77) ;;
  *) echo "$m"; exit 1;;
esac
echo "$n match; $m"
