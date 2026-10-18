#!/usr/bin/env python3
"""Differential test cases for bend-osdev-rs.

Writes ref/cases.bend (a Bend program printing rs's results) and
ref/expected.txt (the same from an independent model written here):

  * the field: carry-less multiplication reduced by the field polynomial;
  * the generator: the product of (x - beta^(fcr+i)), beta = alpha^prim;
  * encoding: polynomial long division of M(x) x^(2t) by g(x), not a
    shift register;
  * decoding: Peterson's direct method instead of Berlekamp-Massey and
    Forney (Geisel, NASA TM-102162, sections 4.3.2 and 4.5.1): erasures are
    folded in by the modified syndromes, the number of errors is the
    largest v whose v-by-v syndrome matrix is nonsingular, the locator
    solves that linear system, its roots are found by trying every
    position, and the error and erasure values solve the linear system
    S_j = sum_k Y_k X_k^(fcr+j) by Gaussian elimination. A result whose
    syndromes are not all zero is a failure.

Python's reedsolo is not used: it is not installed here, and the meaning
of its fcr/prim/generator parameters is not documented on its PyPI page.

Each case encodes a random message (often shortened), adds random errors
(sometimes more than the code can correct) and erasures, and decodes; the
expected line is the codeword, and then the decoded message or "fail".
"""
import os, random, sys


class Field:
    def __init__(self, m, poly):
        self.m, self.poly, self.n = m, poly, (1 << m) - 1

    def mul(self, a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            a <<= 1
            if a >> self.m:
                a ^= self.poly
            b >>= 1
        return r

    def pow(self, a, e):
        r = 1
        for _ in range(e % self.n if a else e):
            r = self.mul(r, a)
        return r

    def inv(self, a):
        return self.pow(a, self.n - 1)


def pmul(F, p, q):  # lowest coefficient first
    r = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] ^= F.mul(a, b)
    return r


def generator(F, fcr, prim, nroots):
    beta = F.pow(2, prim)
    g = [1]
    for i in range(nroots):
        g = pmul(F, g, [F.pow(beta, fcr + i), 1])
    return g


def encode(F, fcr, prim, nroots, msg):
    g = generator(F, fcr, prim, nroots)  # lowest first, monic
    # long division of msg(x) x^nroots (msg highest first)
    rem = list(msg) + [0] * nroots
    for i in range(len(msg)):
        c = rem[i]
        if c:
            for j in range(nroots + 1):
                rem[i + j] ^= F.mul(c, g[nroots - j])
    return list(msg) + rem[len(msg):]


def syndromes(F, fcr, prim, nroots, w):
    beta = F.pow(2, prim)
    out = []
    for i in range(nroots):
        x = F.pow(beta, fcr + i)
        acc = 0
        for s in w:
            acc = F.mul(acc, x) ^ s
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


def decode(F, fcr, prim, nroots, w, eras):
    npos = len(w)
    beta = F.pow(2, prim)
    S = syndromes(F, fcr, prim, nroots, w)
    if not any(S):
        return w[:npos - nroots]
    epos = [npos - 1 - i for i in eras]
    gamma = [1]
    for p in epos:
        gamma = pmul(F, gamma, [1, F.pow(beta, p)])
    e = len(epos)
    T = pmul(F, S, gamma)[:nroots]
    T = T[e:]  # the modified syndromes
    locs = []
    for v in range((len(T)) // 2, -1, -1):
        if v == 0:
            lam = [1]
            break
        A = [[T[i + l] for l in range(v)] for i in range(v)]
        b = [T[i + v] for i in range(v)]
        sol = solve(F, A, b)
        if sol is not None:
            lam = [1] + sol[::-1]  # Lambda_1 .. Lambda_v
            break
    else:
        return None
    v = len(lam) - 1
    binv = F.inv(beta)
    for p in range(npos):
        z = F.pow(binv, p)
        acc = 0
        for c in reversed(lam):
            acc = F.mul(acc, z) ^ c
        if acc == 0:
            locs.append(p)
    if len(locs) != v:
        return None
    allp = epos + locs
    if not allp:
        return None
    X = [F.pow(beta, p) for p in allp]
    k = len(allp)
    if k > nroots:
        return None
    A = [[F.pow(x, fcr + j) for x in X] for j in range(k)]
    Y = solve(F, A, S[:k])
    if Y is None:
        return None
    out = list(w)
    for p, y in zip(allp, Y):
        out[npos - 1 - p] ^= y
    if any(syndromes(F, fcr, prim, nroots, out)):
        return None
    return out[:npos - nroots]


CODES = [  # name, Bend expression, m, poly, fcr, prim, nroots
    ("geisel", "C.Rs.geisel15_9()", 4, 19, 1, 1, 6),
    ("rs255", "C.Rs.rs255_223()", 8, 0x11D, 1, 1, 32),
    ("rs8p16", "C.Rs.rs8_p16()", 8, 0x11D, 0, 1, 16),
    ("ccsds", "C.Rs.ccsds()", 8, 0x187, 112, 11, 32),
    ("ccsds8", "C.Rs.ccsds_e8()", 8, 0x187, 120, 11, 16),
    ("gf8", "C.Rs.code(M.GfmField{3n, 11}, 1, 1, 4)", 3, 11, 1, 1, 4),
    ("gf32", "C.Rs.code(M.Gfm.gf32(), 3, 2, 6)", 5, 37, 3, 2, 6),
    ("gf13", "C.Rs.code(M.Gfm.bch13(), 5, 7, 8)", 13, 0x201B, 5, 7, 8),
]


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    defs, lines, expect = [], [], []

    def lst(xs):
        return "[%s]" % ", ".join(str(x) for x in xs)

    for name, expr, m, poly, fcr, prim, nroots in CODES:
        F = Field(m, poly)
        n = F.n
        count = 6 if n > 300 else 10
        for k in range(count):
            kmax = n - nroots
            short = rng.randrange(1, min(kmax, 40) + 1)
            klen = short if n > 300 else rng.choice([kmax, short])
            msg = [rng.randrange(1 << m) for _ in range(klen)]
            cw = encode(F, fcr, prim, nroots, msg)
            t = nroots // 2
            ne = rng.choice([0, 0, rng.randrange(0, nroots + 1)])
            budget = nroots - ne
            nerr = rng.choice([budget // 2, rng.randrange(0, budget // 2 + 1), budget // 2 + 1, t + 2])
            idx = rng.sample(range(len(cw)), min(len(cw), ne + nerr))
            eras, errs = sorted(idx[:ne]), idx[ne:]
            w = list(cw)
            for i in idx:
                w[i] ^= rng.randrange(1 if i in errs else 0, 1 << m)
            res = decode(F, fcr, prim, nroots, w, eras)
            want = " ".join(str(x) for x in cw) + " | " + ("fail" if res is None else " ".join(str(x) for x in res))
            nm = "%s_%d" % (name, k)
            defs.append("def e_%s() -> String:\n  showr(E.Rs.encode(%s, %s))\n" % (nm, expr, lst(msg)))
            defs.append("def d_%s() -> String:\n  showr(D.Rs.decode(%s, %s, %s))\n" % (nm, expr, lst(w), "[%s]" % ", ".join("%dn" % i for i in eras)))
            lines.append('    IO.print("%s " ++ e_%s() ++ " | " ++ d_%s())' % (nm, nm, nm))
            expect.append("%s %s" % (nm, want))

    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("import Base\nimport ../../gf/gfm.bend as M\nimport ../code.bend as C\nimport ../encode.bend as E\nimport ../rs.bend as D\n\n")
        f.write("def showl(xs: List<&2, U32>) -> String:\n  match xs:\n    case Nil{}:\n      \"\"\n    case Con{x, Nil{}}:\n      U32.show(x)\n    case Con{x, t}:\n      U32.show(x) ++ \" \" ++ showl(t)\n\n")
        f.write("def showr(r: Result<&2, &2, E.RsError, List<&2, U32>>) -> String:\n  match r:\n    case Done{w}:\n      showl(w)\n    case Fail{e}:\n      \"fail\"\n\n")
        f.write("\n".join(defs))
        f.write("\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")


main()
