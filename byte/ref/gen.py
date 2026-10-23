#!/usr/bin/env python3
"""Differential test cases for bend-osdev-byte.

Writes ref/cases.bend (a Bend program printing each operation's result) and
ref/expected.txt (the same results from Python's integers): for ByteU8 and
ByteU16, arithmetic modulo 2^8 and 2^16, the bit operations, shifts by one
bit, increments, comparisons, Nat and decimal views and from_nat of any
Nat; and for a U32, its low 8 and 16 bits, its bytes 0 to 3, and four bytes
joined both ways and two as a 16-bit word. Edge values (0, 1, the maximum,
the top bit alone) and random ones.
"""
import os, random, sys


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []

    def case(label, expr, want):
        lines.append('    IO.print("%s " ++ %s)' % (label, expr))
        expect.append("%s %s" % (label, want))

    def b2s(x):
        return "True" if x else "False"

    for bits, ty, f in ((8, "By.ByteU8", "u8"), (16, "Wd.ByteU16", "u16")):
        m = 1 << bits
        vals = [0, 1, m - 1, m >> 1, (m >> 1) - 1] + [rng.randrange(m) for _ in range(25)]
        mk = lambda x: "%s.from_nat(%dn)" % (ty, x)
        show = lambda e: "%s.show(%s)" % (ty, e)
        for i in range(60):
            a, b = rng.choice(vals), rng.choice(vals)
            A, B = mk(a), mk(b)
            case("%s.add%d" % (f, i), show("%s.add(%s, %s)" % (ty, A, B)), (a + b) % m)
            case("%s.sub%d" % (f, i), show("%s.sub(%s, %s)" % (ty, A, B)), (a - b) % m)
            case("%s.mul%d" % (f, i), show("%s.mul(%s, %s)" % (ty, A, B)), (a * b) % m)
            case("%s.and%d" % (f, i), show("%s.and(%s, %s)" % (ty, A, B)), a & b)
            case("%s.or%d" % (f, i), show("%s.or(%s, %s)" % (ty, A, B)), a | b)
            case("%s.xor%d" % (f, i), show("%s.xor(%s, %s)" % (ty, A, B)), a ^ b)
            case("%s.not%d" % (f, i), show("%s.not(%s)" % (ty, A)), a ^ (m - 1))
            case("%s.inc%d" % (f, i), show("%s.inc(%s)" % (ty, A)), (a + 1) % m)
            case("%s.shl%d" % (f, i), show("%s.shl(%s)" % (ty, A)), (a << 1) % m)
            case("%s.shr%d" % (f, i), show("%s.shr(%s)" % (ty, A)), a >> 1)
            case("%s.cmp%d" % (f, i), "Bool.show(%s.is_eq(%s, %s)) ++ Bool.show(%s.is_lt(%s, %s)) ++ Bool.show(%s.is_le(%s, %s)) ++ Bool.show(%s.is_gt(%s, %s)) ++ Bool.show(%s.is_ge(%s, %s))" % (
                ty, A, B, ty, A, B, ty, A, B, ty, A, B, ty, A, B),
                b2s(a == b) + b2s(a < b) + b2s(a <= b) + b2s(a > b) + b2s(a >= b))
            case("%s.nat%d" % (f, i), "Nat.show(%s.to_nat(%s))" % (ty, A), a)
            case("%s.u32_%d" % (f, i), "U32.show(%s.to_u32(%s))" % (ty, A), a)
        for i in range(10):
            n = rng.randrange(1 << 20) if i else m
            case("%s.from_nat%d" % (f, i), show(mk(n)), n % m)

    u32s = [0, 1, 255, 256, 65535, 65536, 0xFFFFFFFF, 0x12345678, 0x80000000] + [rng.getrandbits(32) for _ in range(30)]
    for i, a in enumerate(u32s):
        case("to_byte%d" % i, "By.ByteU8.show(By.ByteU32.to_byte(%d))" % a, a & 255)
        case("to_word16_%d" % i, "Wd.ByteU16.show(Wd.ByteU32.to_word16(%d))" % a, a & 65535)
        for k in range(4):
            case("byte%d_%d" % (i, k), "By.ByteU8.show(By.ByteU32.byte(%d, %dn))" % (a, k), (a >> (8 * k)) & 255)
    for i in range(30):
        bs = [rng.randrange(256) for _ in range(4)]
        B = ["By.ByteU8.from_nat(%dn)" % x for x in bs]
        case("of_bytes%d" % i, "U32.show(By.ByteU32.of_bytes(%s))" % ", ".join(B), int.from_bytes(bytes(bs), "little"))
        case("of_bytes_be%d" % i, "U32.show(By.ByteU32.of_bytes_be(%s))" % ", ".join(B), int.from_bytes(bytes(bs), "big"))
        case("u16_of_bytes%d" % i, "Wd.ByteU16.show(Wd.ByteU16.of_bytes(%s, %s))" % (B[0], B[1]), bs[0] | (bs[1] << 8))

    # in parts of 50 prints: one do block of thousands overflows the checker
    chunks = [lines[i:i + 50] for i in range(0, len(lines), 50)]
    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write("import Base\nimport ../byte.bend as By\nimport ../word16.bend as Wd\n\n")
        for c, chunk in enumerate(chunks):
            f.write("def part%d() -> IO(Unit):\n  do IO<Unit>:\n" % c + "\n".join(chunk) + "\n\n")
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "".join("    part%d()\n" % c for c in range(len(chunks))))
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")


main()
