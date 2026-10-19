#!/usr/bin/env python3
"""Differential test cases for bend-osdev-bch.

Writes ref/cases.bend (a Bend program printing bch's results) and
ref/expected.txt (the same from an independent model written here):

  * the field: exponent and logarithm tables of x, not multiplication
    bit by bit;
  * the generator: the product of (x + alpha^e) over the cyclotomic cosets
    of m0 .. m0 + 2t - 1, checked to have binary coefficients, kept as an
    integer (bit i the coefficient of x^i);
  * encoding: the remainder of D(x) x^r by g(x), by long division on
    integers, not a shift register;
  * decoding: Peterson's direct method instead of Berlekamp-Massey (the
    number of errors is the largest v <= t whose v-by-v syndrome matrix is
    nonsingular, and the locator solves that linear system by Gaussian
    elimination); the error positions are found by trying every position.
    A result whose syndromes are not all zero is a failure;
  * bytes: bits taken most (or least) significant first, and packed into
    bytes padded with zero bits.

Each case encodes random data (often shortened), flips random bits
(sometimes more than t), and decodes; the expected line is the codeword or
ECC, and then the decoded result or "fail".
"""
import os, random, sys


class Field:
    """GF(2^m) by exponent and logarithm tables of x (the polynomial must
    be primitive), built by repeated multiplication by x"""

    def __init__(self, m, poly):
        self.m, self.poly, self.n = m, poly, (1 << m) - 1
        self.exp, self.log = [0] * (2 * self.n), [0] * (self.n + 1)
        a = 1
        for i in range(self.n):
            self.exp[i] = self.exp[i + self.n] = a
            self.log[a] = i
            a <<= 1
            if a >> m:
                a ^= poly

    def mul(self, a, b):
        if a == 0 or b == 0:
            return 0
        return self.exp[self.log[a] + self.log[b]]

    def pow(self, a, e):
        if a == 0:
            return 0 if e else 1
        return self.exp[self.log[a] * e % self.n]

    def inv(self, a):
        return self.pow(a, self.n - 1)


def generator(F, t, m0):
    exps = set()
    for j in range(m0, m0 + 2 * t):
        e = j % F.n
        while e not in exps:
            exps.add(e)
            e = 2 * e % F.n
    g = [1]  # lowest coefficient first, over GF(2^m)
    for e in sorted(exps):
        r = F.pow(2, e)
        h = [0] * (len(g) + 1)
        for i, c in enumerate(g):
            h[i] ^= F.mul(c, r)
            h[i + 1] ^= c
        g = h
    assert all(c in (0, 1) for c in g)
    return sum(c << i for i, c in enumerate(g))


def deg(p):
    return p.bit_length() - 1


def pmod(a, g):
    dg = deg(g)
    while a and deg(a) >= dg:
        a ^= g << (deg(a) - dg)
    return a


def to_int(bits):
    v = 0
    for b in bits:
        v = 2 * v + b
    return v


def parity(g, bits):
    r = deg(g)
    p = pmod(to_int(bits) << r, g)
    return [(p >> (r - 1 - i)) & 1 for i in range(r)]


def syndromes(F, t, m0, w):
    """S_j = sum of alpha^(j p) over the positions p of the 1 bits"""
    npos = len(w)
    ones = [npos - 1 - i for i, b in enumerate(w) if b]
    out = []
    for j in range(m0, m0 + 2 * t):
        acc = 0
        for p in ones:
            acc ^= F.exp[j * p % F.n]
        out.append(acc)
    return out


def solve(F, A, b):
    """Gaussian elimination over the field; None if singular."""
    n = len(A)
    M = [row[:] + [bb] for row, bb in zip(A, b)]
    for col in range(n):
        piv = next((r for r in range(col, n) if M[r][col]), None)
        if piv is None:
            return None
        M[col], M[piv] = M[piv], M[col]
        iv = F.inv(M[col][col])
        M[col] = [F.mul(iv, v) for v in M[col]]
        for r in range(n):
            if r != col and M[r][col]:
                f = M[r][col]
                M[r] = [v ^ F.mul(f, u) for v, u in zip(M[r], M[col])]
    return [M[r][n] for r in range(n)]


def correct(F, t, m0, g, w):
    """(corrected word, flips) or None"""
    npos, r = len(w), deg(g)
    if not (r < npos <= F.n):
        return None
    S = syndromes(F, t, m0, w)
    if not any(S):
        return list(w), 0
    for v in range(t, 0, -1):
        A = [[S[i + l] for l in range(v)] for i in range(v)]
        sol = solve(F, A, [S[i + v] for i in range(v)])
        if sol is not None:
            lam = [1] + sol[::-1]
            break
    else:
        return None
    ainv = F.inv(2)
    locs = []
    for p in range(npos):
        z = F.pow(ainv, p)
        acc = 0
        for c in reversed(lam):
            acc = F.mul(acc, z) ^ c
        if acc == 0:
            locs.append(p)
    if len(locs) != len(lam) - 1:
        return None
    out = list(w)
    for p in locs:
        out[npos - 1 - p] ^= 1
    if any(syndromes(F, t, m0, out)):
        return None
    return out, len(locs)


def bits_of(data, msb):
    out = []
    for b in data:
        order = range(7, -1, -1) if msb else range(8)
        out.extend((b >> i) & 1 for i in order)
    return out


def pack(bits, msb):
    out = []
    for k in range(0, len(bits), 8):
        v = 0
        for i, b in enumerate(bits[k:k + 8]):
            v |= b << (7 - i if msb else i)
        out.append(v)
    return out


def hexs(xs):
    return "".join("%02x" % x for x in xs)


BIT_CODES = [  # name, Bend expression, m, poly, t, m0
    ("b15_7", "C.Bch.bch15_7()", 4, 19, 2, 1),
    ("b15_5", "C.Bch.bch15_5()", 4, 19, 3, 1),
    ("b31_3", "C.Bch.code(M.Gfm.gf32(), 3, 1)", 5, 37, 3, 1),
    ("b31_m0", "C.Bch.code(M.Gfm.gf32(), 2, 0)", 5, 37, 2, 0),
    ("b63_4", "C.Bch.code(M.GfmField{6n, 67}, 4, 1)", 6, 67, 4, 1),
]

BYTE_CODES = [  # name, Bend expression, t
    ("nand4", "C.Bch.nand_t4()", 4),
    ("nand8", "C.Bch.nand_t8()", 8),
    ("nand16", "C.Bch.nand_t16()", 16),
]


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    defs, lines, expect = [], [], []

    def blist(bits):
        return "[%s]" % ", ".join("True{}" if b else "False{}" for b in bits)

    def olist(xs):
        return "B.Octets.of_list([%s])" % ", ".join(str(x) for x in xs)

    def bstr(bits):
        return "".join(str(b) for b in bits)

    for name, expr, m, poly, t, m0 in BIT_CODES:
        F = Field(m, poly)
        g = generator(F, t, m0)
        r = deg(g)
        for k in range(10):
            kmax = F.n - r
            klen = rng.choice([kmax, rng.randrange(1, kmax + 1)])
            data = [rng.randrange(2) for _ in range(klen)]
            cw = data + parity(g, data)
            nerr = rng.choice([t, rng.randrange(0, t + 1), t + 1, t + 2])
            w = list(cw)
            for i in rng.sample(range(len(cw)), min(len(cw), nerr)):
                w[i] ^= 1
            res = correct(F, t, m0, g, w)
            want = bstr(cw) + " | " + ("fail" if res is None else bstr(res[0][:len(w) - r]))
            nm = "%s_%d" % (name, k)
            defs.append("def e_%s() -> String:\n  showb(E.Bch.encode_bits(%s, %s))\n" % (nm, expr, blist(data)))
            defs.append("def d_%s() -> String:\n  showb(D.Bch.decode_bits(%s, %s))\n" % (nm, expr, blist(w)))
            lines.append('    IO.print("%s " ++ e_%s() ++ " | " ++ d_%s())' % (nm, nm, nm))
            expect.append("%s %s" % (nm, want))

    F = Field(13, 0x201B)
    for name, expr, t in BYTE_CODES:
        g = generator(F, t, 1)
        r = deg(g)
        for k in range(5):
            msb = k != 3
            order = "T.BchMsbFirst{}" if msb else "T.BchLsbFirst{}"
            dlen = rng.choice([512, rng.randrange(1, 513)])
            data = [rng.randrange(256) for _ in range(dlen)]
            db = bits_of(data, msb)
            par = parity(g, db)
            ecc = pack(par, msb)
            eb = bits_of(ecc, msb)
            nerr = rng.choice([t, rng.randrange(0, t + 1), t + 1, t + 3])
            both = db + eb
            for i in rng.sample(range(len(db) + r), nerr):
                both[i] ^= 1
            if len(eb) > r and rng.random() < 0.5:
                both[len(db) + rng.randrange(r, len(eb))] ^= 1  # a padding bit
            rd, re = pack(both[:len(db)], msb), pack(both[len(db):], msb)
            rdb, reb = bits_of(rd, msb), bits_of(re, msb)
            res = correct(F, t, 1, g, rdb + reb[:r])
            if res is None:
                dec = "fail"
            else:
                w, n = res
                dec = "%s %s %d" % (hexs(pack(w[:len(rdb)], msb)), hexs(pack(w[len(rdb):] + reb[r:], msb)), n)
            nm = "%s_%d" % (name, k)
            defs.append("def e_%s() -> String:\n  showo(D.Bch.encode_with(%s, %s, %s))\n" % (nm, order, expr, olist(data)))
            defs.append("def d_%s() -> String:\n  showd(D.Bch.decode_with(%s, %s, %s, %s))\n" % (nm, order, expr, olist(rd), olist(re)))
            lines.append('    IO.print("%s " ++ e_%s() ++ " | " ++ d_%s())' % (nm, nm, nm))
            expect.append("%s %s | %s" % (nm, hexs(ecc), dec))

    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write("import Base\nimport ../../bytes/bytes.bend as B\nimport ../../gf/gfm.bend as M\nimport ../code.bend as C\nimport ../bits.bend as T\nimport ../encode.bend as E\nimport ../bch.bend as D\n\n")
        f.write("def bits(xs: List<&2, Bool>) -> String:\n  match xs:\n    case Nil{}:\n      \"\"\n    case Con{b, t}:\n      match b:\n        case True{}:\n          \"1\" ++ bits(t)\n        case False{}:\n          \"0\" ++ bits(t)\n\n")
        f.write("def showb(r: Result<&2, &2, E.BchError, List<&2, Bool>>) -> String:\n  match r:\n    case Done{w}:\n      bits(w)\n    case Fail{e}:\n      \"fail\"\n\n")
        f.write("def showo(r: Result<&2, &2, E.BchError, B.Octets>) -> String:\n  match r:\n    case Done{o}:\n      B.Octets.hex(o)\n    case Fail{e}:\n      \"fail\"\n\n")
        f.write("def showd(r: Result<&2, &2, E.BchError, D.BchDecoded>) -> String:\n  match r:\n    case Done{x}:\n      match x:\n        case D.BchDecoded{d, e, n}:\n          B.Octets.hex(d) ++ \" \" ++ B.Octets.hex(e) ++ \" \" ++ Nat.show(n)\n    case Fail{e}:\n      \"fail\"\n\n")
        f.write("\n".join(defs))
        f.write("\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")


main()
