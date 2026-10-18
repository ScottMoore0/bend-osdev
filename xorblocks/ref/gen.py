#!/usr/bin/env python3
"""Differential test cases for bend-osdev-xorblocks.

Writes ref/cases.bend (a Bend program printing xorblocks' results on each
case) and ref/expected.txt (the same values from Python's own bytes and
integers): the XOR of random blocks of random, often unequal, lengths under
both length policies, xor_blocks into a destination, and the XOR of a list
of blocks. Python has no xor_blocks of its own, so the reference is the
definition, written here: bytes XORed pairwise, the shorter block padded
with zeros (or the longer cut).
"""
import os, random, sys


def xor_pad(a, b):
    n = max(len(a), len(b))
    a, b = a + bytes(n - len(a)), b + bytes(n - len(b))
    return bytes(x ^ y for x, y in zip(a, b))


def xor_cut(a, b):
    return bytes(x ^ y for x, y in zip(a, b))


def lit(b):
    # build long blocks a piece at a time (list literals stop at about 3000)
    parts = ["B.Octets.of_list([%s])" % ", ".join(str(x) for x in b[i:i + 512]) for i in range(0, len(b), 512)]
    if not parts:
        return "B.Octets.empty()"
    out = parts[-1]
    for p in reversed(parts[:-1]):
        out = "B.Octets.append(%s, %s)" % (p, out)
    return out


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    defs, lines, expect = [], [], []

    def case(name, expr, want):
        # one def per case keeps main small (bendlang/bend#1069)
        defs.append("def c_%s() -> String:\n  B.Octets.hex(%s)\n" % (name, expr))
        lines.append('    IO.print("%s " ++ c_%s())' % (name, name))
        expect.append("%s %s" % (name, want.hex()))

    def block():
        n = rng.choice([0, 1, 2, 3, 7, 16, 31, 64, 100, rng.randrange(1, 300)])
        return rng.randbytes(n)

    for k in range(40):
        a, b = block(), block()
        if k % 3 == 0:
            b = rng.randbytes(len(a))
        case("pad_%d" % k, "X.Xorb.xor(%s, %s)" % (lit(a), lit(b)), xor_pad(a, b))
        case("cut_%d" % k, "X.Xorb.xor_cut(%s, %s)" % (lit(a), lit(b)), xor_cut(a, b))
    for k in range(20):
        d = block()
        srcs = [block() for _ in range(rng.randrange(0, 5))]
        want, cut = d, d
        for s in srcs:
            want, cut = xor_pad(want, s), xor_cut(cut, s)
        srcl = "[%s]" % ", ".join(lit(s) for s in srcs)
        case("into_%d" % k, "X.Xorb.into(%s, %s)" % (lit(d), srcl), want)
        case("into_cut_%d" % k, "X.Xorb.into_with(X.XorbShorter{}, %s, %s)" % (lit(d), srcl), cut)
        all_ = b""
        for s in srcs:
            all_ = xor_pad(all_, s)
        case("all_%d" % k, "X.Xorb.all(%s)" % srcl, all_)

    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("import Base\nimport ../../bytes/bytes.bend as B\nimport ../xorblocks.bend as X\n\n")
        f.write("\n".join(defs))
        f.write("\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")


main()
