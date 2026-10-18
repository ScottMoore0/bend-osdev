#!/usr/bin/env python3
"""Differential test cases for bend-osdev-blockdev, against a model written
here from the interface's documented behaviour (an image padded with zeros
to whole blocks; a read past the end fails; a zero-length read always
succeeds; a write of the wrong length or past the last block is refused and
changes nothing). The model shares an author with the package.

Three kinds of case:
  * Dev.read_bytes on MemDev (the pure interface);
  * ODev.read_bytes on ImgDev (the owned interface, on the Array image);
  * a sequence of ImgDev.write_block calls, then the whole image read back.
Writes ref/cases.bend and ref/expected.txt.
"""
import os, random, sys

def model_bytes(img, bs, off, n):
    count = (len(img) + bs - 1) // bs
    padded = img + bytes(count * bs - len(img))
    if n == 0:
        return "ok "
    if off + n <= len(padded):
        return "ok " + padded[off:off + n].hex()
    return "err"

def octets(bs):
    return "B.Octets.of_list([%s])" % ", ".join(map(str, bs))

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []
    for k in range(60):
        bs = rng.choice([1, 2, 3, 4, 7, 16, 64])
        img = bytes(rng.randrange(256) for _ in range(rng.randrange(0, 120)))
        off = rng.randrange(0, len(img) + 20)
        n = rng.randrange(0, 40)
        lines.append('    IO.print(show(D.Dev.read_bytes(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, D.MemDev.of_octets(%dn, %s), %dn, %dn)))' % (bs, octets(img), off, n))
        expect.append(model_bytes(img, bs, off, n))
    for k in range(40):
        w = rng.choice([1, 2, 4, 16])
        bs = 4 * w
        img = bytes(rng.randrange(256) for _ in range(rng.randrange(0, 200)))
        off = rng.randrange(0, len(img) + 20)
        n = rng.randrange(0, 60)
        lines.append('    IO.print(ishow(D.ODev.read_bytes(~I.ImgDev, ~I.ImgDev.block_size, ~I.ImgDev.read_block, I.ImgDev.of_octets(%dn, %s), %dn, %dn)))' % (w, octets(img), off, n))
        expect.append(model_bytes(img, bs, off, n))
    for k in range(40):
        w = rng.choice([1, 2, 4, 16])
        bs = 4 * w
        img = bytes(rng.randrange(256) for _ in range(rng.randrange(1, 200)))
        count = (len(img) + bs - 1) // bs
        blocks = [bytearray((img + bytes(count * bs - len(img)))[i * bs:(i + 1) * bs]) for i in range(count)]
        ws, codes = [], []
        for _ in range(rng.randrange(1, 12)):
            r = rng.random()
            blk = rng.randrange(count + 2)
            ln = bs if r < 0.8 else rng.choice([0, bs - 1, bs + 1])
            data = bytes(rng.randrange(256) for _ in range(ln))
            ws.append("IWr{%dn, %s}" % (blk, octets(data)))
            if ln != bs:
                codes.append("L")
            elif blk >= count:
                codes.append("R")
            else:
                blocks[blk][:] = data
                codes.append("o")
        lines.append('    IO.print(writes([%s], I.ImgDev.of_octets(%dn, %s), %dn, ""))' % (", ".join(ws), w, octets(img), count * bs))
        expect.append("".join(codes) + "|ok " + b"".join(blocks).hex())
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write(HEADER)
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")

HEADER = '''import Base
import ../../bytes/bytes.bend as B
import ../blockdev.bend as D
import ../imgdev.bend as I

def show(r: Result<&2, &2, D.DevError, B.Octets>) -> String:
  match r:
    case Done{o}:
      "ok " ++ B.Octets.hex(o)
    case Fail{e}:
      "err"

def ishow(r: I.ImgDev & Result<&2, &2, D.DevError, B.Octets>) -> String:
  (img, x) = r
  show(x)

def code(r: Result<&2, &2, D.DevError, Unit>) -> String:
  match r:
    case Done{u}:
      "o"
    case Fail{D.DevBadLength{e, g}}:
      "L"
    case Fail{D.DevOutOfRange{n}}:
      "R"
    case Fail{D.DevFailed{c}}:
      "F"

type IWrite is Data:
  IWr{block: Nat, data: B.Octets}

def wrote(r: I.ImgDev & Result<&2, &2, D.DevError, Unit>, k: I.ImgDev -> String -> String) -> String:
  (img, x) = r
  k(img, code(x))

# the writes in order, their results, then the whole image
def writes(ws: List<&2, IWrite>, img: I.ImgDev, +total: Nat, +acc: String) -> String:
  match ws:
    case Nil{}:
      acc ++ "|" ++ ishow(D.ODev.read_bytes(~I.ImgDev, ~I.ImgDev.block_size, ~I.ImgDev.read_block, img, 0n, total))
    case Con{IWr{n, data}, t}:
      wrote(I.ImgDev.write_block(img, n, data), i2 => s => writes(t, i2, total, acc ++ s))

'''

main()
