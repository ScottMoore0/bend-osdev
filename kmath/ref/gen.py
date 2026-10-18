#!/usr/bin/env python3
"""Differential test cases for bend-osdev-kmath.

Writes ref/cases.bend (a Bend program printing kmath's results) and
ref/expected.txt (the same from Python, outside this repository):
  * gcd, lcm, powers, square roots, 64-bit division (signed and unsigned):
    Python's math.gcd, math.lcm, pow, math.isqrt and exact integers;
  * reciprocal division: Python's floor division;
  * best rational approximation: fractions.Fraction.limit_denominator when
    only the denominator binds, and an exhaustive search over every
    denominator for small bounds (cases where two fractions tie are left
    out);
  * CORDIC: math.cos and math.sin; the largest error over all the angles
    must stay within the documented bound (64 units of 2^-30), and the
    case prints only whether it does;
  * primality and the next prime: trial division in Python.
"""
import math, os, random, sys
from fractions import Fraction

M32, M64 = (1 << 32) - 1, (1 << 64) - 1


def w64(x):
    return "W.W64.from_parts(%d, %d)" % (x >> 32, x & M32)


def nat(x):
    if x <= M32:
        return "%dn" % x
    return "Nat.add(Nat.mul(%dn, Nat.add(4294967295n, 1n)), %dn)" % (x >> 32, x & M32)


def s64(x):
    return x - (1 << 64) if x >> 63 else x


def tdiv(a, b):
    q = abs(a) // abs(b)
    return q if (a < 0) == (b < 0) else -q


def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def best(n, d, mn, md):
    x = Fraction(n, d)
    cands = []
    for q in range(1, md + 1):
        p = min(mn, max(0, round(x * q)))
        for pp in (p - 1, p, p + 1):
            if 0 <= pp <= mn:
                cands.append((abs(x - Fraction(pp, q)), Fraction(pp, q)))
    e = min(c[0] for c in cands)
    vals = {c[1] for c in cands if c[0] == e}
    return vals.pop() if len(vals) == 1 else None


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []

    def case(name, call, want):
        lines.append('    IO.print("%s " ++ %s)' % (name, call))
        expect.append("%s %s" % (name, want))

    for k in range(40):
        a, b = rng.randrange(1 << rng.choice([8, 20, 40])), rng.randrange(1 << rng.choice([8, 20, 40]))
        if k < 3:
            a, b = [(0, 0), (0, 12), (12, 0)][k]
        case("gcd_%d" % k, "Nat.show(K.KMath.gcd(%s, %s))" % (nat(a), nat(b)), math.gcd(a, b))
        a2, b2 = rng.randrange(1, 1 << 20), rng.randrange(1, 1 << 20)
        case("lcm_%d" % k, "Nat.show(K.KMath.lcm(%s, %s))" % (nat(a2), nat(b2)), math.lcm(a2, b2))
        x, y = rng.randrange(1 << 32), rng.randrange(1 << 32)
        case("gcd32_%d" % k, "U32.show(K.KMath.gcd32(%d, %d))" % (x, y), math.gcd(x, y))
        base = rng.randrange(2, 40)
        e = rng.randrange(0, int(47 / math.log2(base)))
        case("pow_%d" % k, "Nat.show(K.KMath.pow(%dn, %d))" % (base, e), base ** e)
        case("pow32_%d" % k, "U32.show(K.KMath.pow32(%d, %d))" % (x, y), pow(x, y, 1 << 32))
        n = rng.choice([x, rng.randrange(1 << 16), (rng.randrange(1 << 16)) ** 2, M32])
        case("isqrt_%d" % k, "U32.show(S.KMath.isqrt(%d))" % n, math.isqrt(n))
        big = rng.choice([rng.randrange(1 << 64), rng.randrange(1 << 40), M64, (rng.randrange(1 << 32)) ** 2])
        case("isqrt64_%d" % k, "U32.show(S.KMath.isqrt64(%s))" % w64(big), math.isqrt(big))
        d32 = rng.choice([rng.randrange(1, 1 << 32), rng.randrange(1, 100), 1, M32])
        case("div_u64_rem_%d" % k, "dv(D.KMath.div_u64_rem(%s, %d))" % (w64(big), d32), "%d %d" % divmod(big, d32))
        d64 = rng.choice([rng.randrange(1, 1 << 64), rng.randrange(1, 1 << 33), 1])
        case("div64_u64_rem_%d" % k, "pr(D.KMath.div64_u64_rem(%s, %s))" % (w64(big), w64(d64)), "%d %d" % divmod(big, d64))
        case("round_up_%d" % k, "W.W64.show(D.KMath.div64_u64_round_up(%s, %s))" % (w64(big), w64(d64)), -(-big // d64))
        sn, sd = s64(rng.randrange(1 << 64)), s64(rng.choice([rng.randrange(1, 1 << 64), rng.randrange(1, 100)]))
        if sd == 0:
            sd = 1
        q = tdiv(sn, sd)
        case("div64_s64_rem_%d" % k, "pr(D.KMath.div64_s64_rem(%s, %s))" % (w64(sn & M64), w64(sd & M64)), "%d %d" % (q & M64, (sn - q * sd) & M64))
        sd32 = s64((rng.choice([rng.randrange(1, 1 << 31), -rng.randrange(1, 1 << 31)])) & M64)
        q = tdiv(sn, sd32)
        case("div_s64_rem_%d" % k, "dv(D.KMath.div_s64_rem(%s, %d))" % (w64(sn & M64), sd32 & M32), "%d %d" % (q & M64, (sn - q * sd32) & M32))
    for k in range(60):
        d = rng.choice([rng.randrange(1, 1 << 32), rng.randrange(1, 1000), 1 << rng.randrange(32), M32, 1, 2, 3, 7])
        a = rng.choice([rng.randrange(1 << 32), M32, 0, d, d - 1, (d * rng.randrange(1, 4)) & M32])
        case("recip_%d" % k, "U32.show(R.KRecip.divide(%d, R.KRecip.of(%d)))" % (a, d), a // d)
    k = 0
    while k < 40:
        n, d = rng.randrange(1 << rng.choice([10, 32])), rng.randrange(1, 1 << rng.choice([10, 32]))
        if k % 2 == 0:
            md = rng.randrange(1, 1 << 16)
            want = Fraction(n, d).limit_denominator(md)
            mn = M32
            if want.numerator > mn:
                continue
        else:
            n, d = rng.randrange(1000), rng.randrange(1, 1000)
            mn, md = rng.randrange(1, 60), rng.randrange(1, 60)
            want = best(n, d, mn, md)
            if want is None:
                continue
        case("rational_%d" % k, "rat(Q.KMath.rational_best(%d, %d, %d, %d))" % (n, d, mn, md), "%d/%d" % (want.numerator, want.denominator))
        k += 1
    # CORDIC's error, over many angles: whether every one is within the bound
    angles = [rng.randrange(1 << 32) for _ in range(4000)] + [0, 1 << 30, 1 << 31, 3 << 30, M32, (1 << 30) - 1, (1 << 30) + 1]

    def want(a):
        t = a * 2 * math.pi / 2 ** 32
        return round(math.cos(t) * 2 ** 30) & M32, round(math.sin(t) * 2 ** 30) & M32
    chunks = []
    for i in range(0, len(angles), 200):
        xs = []
        for a in angles[i:i + 200]:
            xs += [a, *want(a)]
        chunks.append("cordic_ok([%s])" % ", ".join(map(str, xs)))
    lines.append('    IO.print("cordic " ++ Bool.show(%s))' % ", ".join(["Bool.and(" + c for c in chunks[:-1]] + [chunks[-1]]) + ")" * (len(chunks) - 1))
    expect.append("cordic True")
    for k, a in enumerate(angles[:12]):
        lines.append('    IO.print("cordic_%d " ++ cerr(%d, %d, %d))' % (k, a, *want(a)))
        expect.append("cordic_%d ok" % k)
    for k in range(30):
        n = rng.choice([rng.randrange(1 << 32), rng.randrange(100), rng.randrange(1 << 16), 4294967291, 4294967279, 65537 * 65537 % (1 << 32), 65521 * 65521])
        case("prime_%d" % k, "Bool.show(P.KMath.is_prime(%d))" % n, is_prime(n))
        m = rng.choice([rng.randrange(1 << 32), rng.randrange(1000), 4294967290, 4294967291])
        nx = m + 1
        while nx <= M32 and not is_prime(nx):
            nx += 1
        case("next_prime_%d" % k, "U32.show(P.KMath.next_prime(%d))" % m, nx if nx <= M32 else 0)
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("import Base\nimport ../../word64/word64.bend as W\nimport ../kmath.bend as K\nimport ../isqrt.bend as S\n"
                "import ../div64.bend as D\nimport ../reciprocal.bend as R\nimport ../rational.bend as Q\n"
                "import ../cordic.bend as C\nimport ../prime.bend as P\n\n")
        f.write(open(os.path.join(here, "helpers.bend")).read())
        f.write("\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(map(str, expect)) + "\n")
    print(len(expect), "cases")


main()
