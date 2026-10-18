#!/usr/bin/env python3
"""Differential test cases for bend-osdev-dim.

Writes ref/cases.bend (a Bend program that runs random sample sequences
through dim.bend under random parameters: tables of 1 to 6 profiles, start
indices, significance thresholds, tired counts and both criteria chains)
and ref/expected.txt (the same sequences on the Python model below).

The model is written from the same document as the package (the kernel's
Documentation/networking/net_dim.rst, as the README restates it) and shares
an author with it: there is no external oracle. As it runs it also checks
the laws on every step: the index stays within the table and moves by at
most one, a step that reports no change keeps the index, and (for tables
of two or more profiles and max_steps of at least 2) a run of identical
samples is at rest after settle_bound samples, every further one leaving
the state as it is.
"""
import os, random, sys

M64 = (1 << 64) - 1


def rate(v, t):
    return (v * 1000) // t


def rates(s):
    pk, by, ev, co, el = s
    return {"bytes": rate(by, el), "pkts": rate(pk, el), "events": rate(ev, el), "comps": rate(co, el)}


def cmp_rate(pct, a, b):
    if a == b:
        return 0
    if b < a:
        return 1 if b * pct < (a - b) * 100 else 0
    return -1 if b * pct < (b - a) * 100 else 0


def compare(chain, pct, new, old):
    for metric, higher_better in chain:
        c = cmp_rate(pct, new[metric], old[metric])
        if c != 0:
            return "better" if (c > 0) == higher_better else "worse"
    return "same"


class Dim:
    """going (right, steps right, steps left), parked on top, or parked
    tired (the direction that tired it, samples spent)"""

    def __init__(self, profiles, start, pct, tired, maxs, chain):
        self.n, self.pct, self.tired, self.maxs, self.chain = len(profiles), pct, tired, maxs, chain
        self.ix = start if start < self.n else 0
        self.mode = ("going", True, 0, 0)
        self.prev = None

    def key(self):
        return (self.ix, self.mode, None if self.prev is None else tuple(sorted(self.prev.items())))

    def walk(self, right, rs, ls):
        can = (self.ix + 1 < self.n) if right else (self.ix > 0)
        if not can:
            self.mode = ("tired", right, 0)          # on the edge
            return False
        if right:
            self.ix, rs = self.ix + 1, rs + 1
        else:
            self.ix, ls = self.ix - 1, ls + 1
        if self.maxs <= (rs if right else ls):
            self.mode = ("tired", right, 0)          # too tired
        else:
            self.mode = ("going", right, rs, ls)     # stepped
        return True

    def step(self, s):
        if s[4] == 0:
            return False
        r = rates(s)
        if self.prev is None:
            self.prev = r
            return False
        c = compare(self.chain, self.pct, r, self.prev)
        self.prev = r
        m = self.mode
        if m[0] == "going":
            if c == "same":
                self.mode = ("top",)
                return False
            return self.walk(m[1] if c == "better" else not m[1], m[2], m[3])
        if m[0] == "top":
            if c == "same":
                return False
            return self.walk(self.ix == 0, 0, 0)
        if self.tired <= m[2]:
            return self.walk(not m[1], 0, 0)
        self.mode = ("tired", m[1], m[2] + 1)
        return False


def show_mode(m):
    if m[0] == "going":
        return "right" if m[1] else "left"
    if m[0] == "top":
        return "top"
    return "tired%d" % m[2]


def run(params, samples):
    d = Dim(*params)
    out = []
    i = 0
    while i < len(samples):
        s = samples[i]
        before = d.ix
        ch = d.step(s)
        assert 0 <= d.ix < d.n and abs(d.ix - before) <= 1
        assert ch or d.ix == before
        out.append("%d%s:%s" % (d.ix, "*" if ch else "", show_mode(d.mode)))
        i += 1
    return " ".join(out)


def check_settles(params, samples, s):
    # after settle_bound identical samples the state is at rest (for two or
    # more profiles and max_steps of at least 2)
    d = Dim(*params)
    for x in samples:
        d.step(x)
    for _ in range(4 + 2 * params[3]):
        d.step(s)
    k = d.key()
    for _ in range(10):
        d.step(s)
        assert d.key() == k


CHAINS = {
    "D.DimParams.chain_default()": [("bytes", True), ("pkts", True), ("events", False)],
    "D.DimParams.chain_completions()": [("comps", True), ("events", False)],
}

PROGRAM = """import Base
import ../dim.bend as D

def mode(m: D.DimMode) -> String:
  match m:
    case D.DimGoing{True{}, rs, ls}:
      "right"
    case D.DimGoing{False{}, rs, ls}:
      "left"
    case D.DimParkedTop{}:
      "top"
    case D.DimParkedTired{d, k}:
      "tired" ++ Nat.show(k)

def flag(c: Bool) -> String:
  match c:
    case True{}:
      "*"
    case False{}:
      ""

def trace(ss: List<&2, D.DimSample>, +p: D.DimParams, st: D.Dim, sep: String) -> String:
  match ss:
    case Nil{}:
      ""
    case Con{s, rest}:
      +r = D.Dim.step(p, st, s)
      +st1 = D.DimStep.state(r)
      sep ++ Nat.show(D.Dim.index(st1)) ++ flag(D.DimStep.changed(r)) ++ ":" ++ mode(D.Dim.mode(st1)) ++ trace(rest, p, st1, " ")

def go(+p: D.DimParams, ss: List<&2, D.DimSample>) -> String:
  trace(ss, p, D.Dim.new(p), "")

def main() -> IO(Unit):
  do IO<Unit>:
%s
"""


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect, total = [], [], 0
    for n in range(40):
        size = rng.randrange(1, 7)
        profiles = [(rng.randrange(1, 300), rng.randrange(1, 300)) for _ in range(size)]
        start = rng.randrange(size + 2)
        pct = rng.choice([0, 5, 10, 10, 25, 50])
        tired = rng.choice([0, 1, 2, 3, 5])
        maxs = rng.choice([0, 1, 2, 3, 4, 10])
        chain = rng.choice(list(CHAINS))
        params = (profiles, start, pct, tired, maxs, CHAINS[chain])
        samples = []
        b, p, e, c = rng.randrange(1, 10**9), rng.randrange(1, 10**6), rng.randrange(1, 10**4), rng.randrange(1, 10**5)
        for _ in range(rng.randrange(10, 60)):
            r = rng.random()
            if r < 0.3:
                pass                      # the same interval again
            elif r < 0.9:
                f = rng.choice([0.5, 0.8, 0.95, 1.0, 1.05, 1.2, 1.5])
                b, p = min(int(b * f) + 1, 2**32 - 1), min(int(p * rng.choice([0.9, 1.0, 1.1])) + 1, 2**32 - 1)
                e, c = min(int(e * rng.choice([0.8, 1.0, 1.25])) + 1, 2**32 - 1), min(int(c * f) + 1, 2**32 - 1)
            el = 0 if rng.random() < 0.05 else rng.choice([1000, 1000, 1000, 2000, 250, rng.randrange(1, 10**6)])
            samples.append((p, b, e, c, el))
        # and a tail of identical samples, longer than the settle bound
        tail = (p, b, e, c, rng.choice([1000, 777]))
        if size >= 2 and maxs >= 2:
            check_settles(params, samples, tail)
        samples += [tail] * (6 + 2 * tired)
        total += len(samples)
        ps = "[%s]" % ", ".join("D.DimProfile{%d, %d}" % q for q in profiles)
        prm = "{D.DimParams{%s, %dn, %d, %dn, %dn, %s} : D.DimParams}" % (ps, start, pct, tired, maxs, chain)
        ss = "[%s]" % ", ".join("D.DimSample{%d, %d, %d, %d, %d}" % s for s in samples)
        lines.append('    IO.print("case %d " ++ go(%s, %s))' % (n, prm, ss))
        expect.append("case %d %s" % (n, run(params, samples)))
    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write(PROGRAM % "\n".join(lines))
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print("%d samples in 40 sequences" % total)


main()
