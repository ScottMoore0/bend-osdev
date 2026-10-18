#!/usr/bin/env bash
# Differential test: images written by mke2fs, e2fsck and debugfs (and logs
# written by model.py), read, recovered and written by the package, and the
# answers compared with the trees, debugfs, e2fsck and model.py; then what
# the package wrote (recovered images, committed transactions, htree
# directories) checked with the tools, and the built directories read back
# (see gen.py). run.bend is built once and runs both query files. Then
# journalled writes (jgen.py, jmain.bend): ext2's operations written
# through the journal on images mke2fs made, compared with the same
# operations done directly, checked with e2fsck -fn and debugfs, and
# crashed after six numbers of steps, each crash recovered by e2fsck and
# by the package (see jgen.py). Exit 77 skips.
set -uo pipefail
cd "$(dirname "$0")"
PATH=$PATH:/usr/sbin:/sbin  # where e2fsprogs lives
export PYTHONDONTWRITEBYTECODE=1
for t in python3 mke2fs debugfs e2fsck tune2fs; do
  command -v "$t" > /dev/null || { echo "$t missing"; exit 77; }
done
read -r -a bend <<< "${BEND:-bend}"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
seed=${SEED:-2026}
python3 gen.py prepare "$seed" "$work" > "$work/gen1.log" 2>&1 || { cat "$work/gen1.log"; exit 1; }
if "${bend[@]}" run.bend -o "$work/prog" > "$work/build.log" 2>&1 && [ -x "$work/prog" ]; then
  runner=("$work/prog")
else
  runner=("${bend[@]}" run.bend)
fi
compare() {
  if ! cmp -s "$1" "$2"; then
    diff "$1" "$2" | head -20 | cut -c1-240
    exit 1
  fi
}
"${runner[@]}" "$work/q1.txt" > "$work/got1" 2>&1
compare "$work/q1.expected" "$work/got1"
python3 gen.py verify "$seed" "$work" "$work/got1" > "$work/gen2.log" 2>&1 || { cat "$work/gen2.log"; exit 1; }
"${runner[@]}" "$work/q2.txt" > "$work/got2" 2>&1
compare "$work/q2.expected" "$work/got2"
mkdir "$work/j"
python3 jgen.py gen "$seed" "$work/j" > "$work/jgen.log" 2>&1 || { cat "$work/jgen.log"; exit 1; }
if "${bend[@]}" jmain.bend -o "$work/jprog" > "$work/jbuild.log" 2>&1 && [ -x "$work/jprog" ]; then
  jrunner=("$work/jprog")
else
  jrunner=("${bend[@]}" jmain.bend)
fi
"${jrunner[@]}" "$work/j/jcases.txt" > "$work/j/out.txt" 2> "$work/j/err.txt" || { tail -20 "$work/j/err.txt"; exit 1; }
jw=$(python3 jgen.py check "$work/j" "$work/j/out.txt") || { printf '%s\n' "$jw" | tail -20; exit 1; }
echo "$(cat "$work/gen1.log"); $(cat "$work/gen2.log"); journalled writes: $jw; all match"
