#!/usr/bin/env python3
"""Differential test cases for bend-osdev-word64.

Writes ref/cases.bend (a Bend program printing each operation's result) and
ref/expected.txt (the same results from Python's integers, which are exact):
arithmetic modulo 2^64, division (by zero: quotient 0, remainder a), the bit
operations, shifts by 0 to 70 bits, comparisons, and decimal and hex text,
on random words and on the edge values 0, 1, 2^32 - 1, 2^32, 2^63 and
2^64 - 1.
"""
import os, random, sys

M = 2 ** 64
EDGE = [0, 1, 2 ** 32 - 1, 2 ** 32, 2 ** 63, M - 1, 0xdeadbeefcafebabe]

def w(x):
    return "W.W64.from_parts(%d, %d)" % (x >> 32, x & 0xffffffff)

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    vals = EDGE + [rng.getrandbits(64) for _ in range(40)] + [rng.getrandbits(rng.randrange(1, 64)) for _ in range(20)]
    lines, expect = [], []
    def case(label, expr, want):
        lines.append('    IO.print("%s " ++ %s)' % (label, expr))
        expect.append("%s %s" % (label, want))
    hexs = lambda x: "W.W64.show_hex(%s)" % x
    for i in range(60):
        a, b = rng.choice(vals), rng.choice(vals)
        if i % 7 == 0:
            b = 0
        A, B = w(a), w(b)
        case("add%d" % i, hexs("W.W64.add(%s, %s)" % (A, B)), "%016x" % ((a + b) % M))
        case("sub%d" % i, hexs("W.W64.sub(%s, %s)" % (A, B)), "%016x" % ((a - b) % M))
        case("mul%d" % i, hexs("W.W64.mul(%s, %s)" % (A, B)), "%016x" % ((a * b) % M))
        case("div%d" % i, hexs("W.W64.div(%s, %s)" % (A, B)), "%016x" % (a // b if b else 0))
        case("mod%d" % i, hexs("W.W64.mod(%s, %s)" % (A, B)), "%016x" % (a % b if b else a))
        case("and%d" % i, hexs("W.W64.and(%s, %s)" % (A, B)), "%016x" % (a & b))
        case("or%d" % i, hexs("W.W64.or(%s, %s)" % (A, B)), "%016x" % (a | b))
        case("xor%d" % i, hexs("W.W64.xor(%s, %s)" % (A, B)), "%016x" % (a ^ b))
        case("not%d" % i, hexs("W.W64.not(%s)" % A), "%016x" % (a ^ (M - 1)))
        k = rng.choice([0, 1, 31, 32, 33, 63, 64, 70, rng.randrange(0, 64)])
        case("shl%d" % i, hexs("W.W64.shl(%s, %dn)" % (A, k)), "%016x" % ((a << k) % M))
        case("shr%d" % i, hexs("W.W64.shr(%s, %dn)" % (A, k)), "%016x" % (a >> k))
        c = "LT" if a < b else ("EQ" if a == b else "GT")
        case("lt%d" % i, "Bool.show(W.W64.is_lt(%s, %s))" % (A, B), "True" if a < b else "False")
        case("eq%d" % i, "Bool.show(W.W64.is_eq(%s, %s))" % (A, B), "True" if a == b else "False")
        case("show%d" % i, "W.W64.show(%s)" % A, str(a))
    for i, n in enumerate([0, 1, 2 ** 32 - 1, 2 ** 32 + 5, 2 ** 47 + 3]):
        hi, lo = n >> 32, n & 0xffffffff
        nat = "Nat.add(Nat.mul(%dn, W.W64.two32()), %dn)" % (hi, lo)
        case("fromnat%d" % i, hexs("W.W64.from_nat(%s)" % nat), "%016x" % n)
        case("tonat%d" % i, "Nat.show(W.W64.to_nat(%s))" % w(n), str(n))
    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write("import Base\nimport ../word64.bend as W\n\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")

main()
