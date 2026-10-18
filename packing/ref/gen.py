#!/usr/bin/env python3
"""Differential test cases for bend-osdev-packing.

The reference is model.py: where each bit of the buffer lies under the
quirks, computed as index arithmetic from the quirks' documented meaning
(the package itself reorders lists of bytes and bits instead). Python
integers stand in for the field values.

Writes ref/cases.bend (random buffers, quirks, fields and values; pack,
pack_masked, unpack and bit) and ref/expected.txt.
"""
import os, random, sys
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model

def lit(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"

def b(x):
    return "True{}" if x else "False{}"

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    defs, expect = [], []
    for c in range(300):
        L = rng.choice([1, 2, 3, 4, 4, 8, 8, 12, 16, 6])
        quirks = (rng.random() < 0.5, rng.random() < 0.5, rng.random() < 0.5)
        if (quirks[1] or quirks[2]) and L % 4 and rng.random() < 0.85:
            L += 4 - L % 4
        buf = [rng.randrange(256) for _ in range(L)]
        if rng.random() < 0.85:
            end = rng.randrange(8 * L)
            start = min(8 * L - 1, end + rng.randrange(64))
        else:
            start, end = rng.randrange(8 * L + 8), rng.randrange(8 * L + 8)
            if rng.random() < 0.3:
                start = end + 64 + rng.randrange(4)
        w = max(start - end + 1, 1)
        if rng.random() < 0.7:
            v = rng.randrange(1 << min(w, 64))
        else:
            v = rng.randrange(1 << 64)
        k = rng.randrange(8 * L + 4)
        q = "V.PkQuirks{%s, %s, %s}" % tuple(b(x) for x in quirks)
        bl = "B.Octets.of_list(%s)" % lit(buf)
        val = "W.W64.from_parts(%d, %d)" % (v >> 32, v & 0xffffffff)
        kind = rng.randrange(4)
        if kind == 0:
            body = "show_b(P.packing.pack(%s, %s, %dn, %dn, %s))" % (q, bl, start, end, val)
            exp = model.pack(buf, start, end, v, quirks)
        elif kind == 1:
            body = "show_b(P.packing.pack_masked(%s, %s, %dn, %dn, %s))" % (q, bl, start, end, val)
            exp = model.pack(buf, start, end, v, quirks, True)
        elif kind == 2:
            body = "show_v(P.packing.unpack(%s, %s, %dn, %dn))" % (q, bl, start, end)
            exp = model.unpack(buf, start, end, quirks)
        else:
            if (quirks[1] or quirks[2]) and L % 4:
                buf = buf + [0] * (4 - L % 4)
                L = len(buf)
                bl = "B.Octets.of_list(%s)" % lit(buf)
            body = "Bool.show(P.packing.bit(%s, %s, %dn))" % (q, bl, k)
            exp = str(model.bit(buf, k, quirks))
        defs.append("def c%d() -> String:\n  %s\n" % (c, body))
        expect.append(exp)
    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write('''import Base
import ../../bytes/bytes.bend as B
import ../../word64/word64.bend as W
import ../view.bend as V
import ../packing.bend as P

def err(e: P.PkError) -> String:
  match e:
    case P.PkBadRange{}:
      "PkBadRange"
    case P.PkTooWide{}:
      "PkTooWide"
    case P.PkOutOfBuffer{}:
      "PkOutOfBuffer"
    case P.PkBadLength{}:
      "PkBadLength"
    case P.PkOverflow{}:
      "PkOverflow"

def show_b(r: Result<&2, &2, P.PkError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.hex(o)
    case Fail{e}:
      err(e)

def show_v(r: Result<&2, &2, P.PkError, W.W64>) -> String:
  match r:
    case Done{v}:
      W.W64.show_hex(v)
    case Fail{e}:
      err(e)

''')
        f.write("\n".join(defs) + "\n")
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join("    IO.print(c%d())" % i for i in range(len(defs))) + "\n")
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print(len(defs), "cases")

main()
