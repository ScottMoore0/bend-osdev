#!/usr/bin/env python3
"""Differential test cases for bend-osdev-khash.

Writes ref/cases.bend (a Bend program printing each hash of each case) and
ref/expected.txt (the same from a Python model of lookup3 written from
Jenkins' description: hashlittle for jhash, hashword for jhash2 and the
word forms, and Python's integers for the golden-ratio hashes). The model
is checked first against the values Jenkins publishes with lookup3.
"""
import os, random, sys

M = 0xFFFFFFFF


def rot(x, k):
    return ((x << k) | (x >> (32 - k))) & M


def mix(a, b, c):
    a = (a - c) & M; a ^= rot(c, 4); c = (c + b) & M
    b = (b - a) & M; b ^= rot(a, 6); a = (a + c) & M
    c = (c - b) & M; c ^= rot(b, 8); b = (b + a) & M
    a = (a - c) & M; a ^= rot(c, 16); c = (c + b) & M
    b = (b - a) & M; b ^= rot(a, 19); a = (a + c) & M
    c = (c - b) & M; c ^= rot(b, 4); b = (b + a) & M
    return a, b, c


def final(a, b, c):
    c ^= b; c = (c - rot(b, 14)) & M
    a ^= c; a = (a - rot(c, 11)) & M
    b ^= a; b = (b - rot(a, 25)) & M
    c ^= b; c = (c - rot(b, 16)) & M
    a ^= c; a = (a - rot(c, 4)) & M
    b ^= a; b = (b - rot(a, 14)) & M
    c ^= b; c = (c - rot(b, 24)) & M
    return a, b, c


def hashlittle(k, iv):
    n = len(k)
    a = b = c = (0xDEADBEEF + n + iv) & M
    i = 0
    while n > 12:
        a = (a + int.from_bytes(k[i:i + 4], "little")) & M
        b = (b + int.from_bytes(k[i + 4:i + 8], "little")) & M
        c = (c + int.from_bytes(k[i + 8:i + 12], "little")) & M
        a, b, c = mix(a, b, c)
        n -= 12
        i += 12
    if n == 0:
        return c
    t = k[i:] + bytes(12 - n)
    a = (a + int.from_bytes(t[0:4], "little")) & M
    b = (b + int.from_bytes(t[4:8], "little")) & M
    c = (c + int.from_bytes(t[8:12], "little")) & M
    return final(a, b, c)[2]


def hashword(ws, iv):
    n = len(ws)
    a = b = c = (0xDEADBEEF + (n << 2) + iv) & M
    i = 0
    while n > 3:
        a = (a + ws[i]) & M; b = (b + ws[i + 1]) & M; c = (c + ws[i + 2]) & M
        a, b, c = mix(a, b, c)
        n -= 3
        i += 3
    if n == 0:
        return c
    t = ws[i:] + [0] * (3 - n)
    a = (a + t[0]) & M; b = (b + t[1]) & M; c = (c + t[2]) & M
    return final(a, b, c)[2]


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    # Jenkins' published check values (lookup3's driver)
    assert hashlittle(b"", 0) == 0xDEADBEEF and hashlittle(b"", 0xDEADBEEF) == 0xBD5B7DDE
    assert hashlittle(b"Four score and seven years ago", 0) == 0x17770551
    assert hashlittle(b"Four score and seven years ago", 1) == 0xCD628161
    lines, expect = [], []

    def case(name, call, want):
        lines.append('    IO.print("%s " ++ %s)' % (name, call))
        expect.append("%s %s" % (name, want))
    for k in range(120):
        n = rng.choice([rng.randrange(40), rng.randrange(200), 12, 13, 24, 25])
        data = bytes(rng.randrange(256) for _ in range(n))
        iv = rng.randrange(1 << 32)
        case("jhash_%d" % k, "U32.show(J.Jhash.jhash(B.Octets.of_list([%s]), %d))" % (", ".join(map(str, data)), iv), hashlittle(data, iv))
        ws = [rng.randrange(1 << 32) for _ in range(rng.randrange(12))]
        case("jhash2_%d" % k, "U32.show(J.Jhash.jhash2([%s], %d))" % (", ".join(map(str, ws)), iv), hashword(ws, iv))
        a, b, c = (rng.randrange(1 << 32) for _ in range(3))
        case("jhash_3words_%d" % k, "U32.show(J.Jhash.jhash_3words(%d, %d, %d, %d))" % (a, b, c, iv), hashword([a, b, c], iv))
        case("jhash_2words_%d" % k, "U32.show(J.Jhash.jhash_2words(%d, %d, %d))" % (a, b, iv), hashword([a, b], iv))
        case("jhash_1word_%d" % k, "U32.show(J.Jhash.jhash_1word(%d, %d))" % (a, iv), hashword([a], iv))
        bits = rng.randrange(33)
        case("hash_32_%d" % k, "U32.show(G.KHash.hash_32(%d, %dn))" % (a, bits), ((a * 0x61C88647) & M) >> (32 - bits))
        v = rng.randrange(1 << 64)
        bits = rng.randrange(33)
        case("hash_64_%d" % k, "U32.show(G.KHash.hash_64(W.W64.from_parts(%d, %d), %dn))" % (v >> 32, v & M, bits), ((v * 0x61C8864680B583EB) & ((1 << 64) - 1)) >> (64 - bits))
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("import Base\nimport ../../word64/word64.bend as W\nimport ../../bytes/bytes.bend as B\nimport ../khash.bend as J\nimport ../golden.bend as G\n\n")
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(map(str, expect)) + "\n")
    print(len(expect), "cases")


main()
