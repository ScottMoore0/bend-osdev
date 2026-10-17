#!/usr/bin/env python3
"""Differential test cases for bend-osdev-blockdev: Dev.read_bytes and
MemDev.read_block on random images, block sizes and ranges, against a model
written here from the interface's documented behaviour (an image padded with
zeros to whole blocks; a read past the end fails; a zero-length read always
succeeds)."""
import os, random, sys

def model_bytes(img, bs, off, n):
    count = (len(img) + bs - 1) // bs
    padded = img + bytes(count * bs - len(img))
    if n == 0:
        return "ok "
    if off + n <= len(padded):
        return "ok " + padded[off:off + n].hex()
    return "err"

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []
    for k in range(60):
        bs = rng.choice([1, 2, 3, 4, 7, 16, 64])
        img = bytes(rng.randrange(256) for _ in range(rng.randrange(0, 120)))
        off = rng.randrange(0, len(img) + 20)
        n = rng.randrange(0, 40)
        lst = "[" + ", ".join(map(str, img)) + "]"
        lines.append('    IO.print(show(D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, D.MemDev.of_octets(%dn, B.Octets.of_list(%s)), %dn, %dn)))' % (bs, lst, off, n))
        expect.append(model_bytes(img, bs, off, n))
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("import Base\nimport ../../bytes/bytes.bend as B\nimport ../blockdev.bend as D\n\n")
        f.write("def show(r: Result<&2, &2, D.DevError, B.Octets>) -> String:\n  match r:\n    case Done{o}:\n      \"ok \" ++ B.Octets.hex(o)\n    case Fail{e}:\n      \"err\"\n\n")
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")

main()
