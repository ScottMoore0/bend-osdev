#!/usr/bin/env python3
"""Differential test cases for bend-osdev-errseq.

Writes ref/cases.bend (a Bend program that runs random event sequences
through errseq.bend: a writer recording errors, and several observers
sampling, checking and checking-and-advancing, under both options) and
ref/expected.txt (the same sequences on the Python model below).

The model is written from the behaviour the README states (the errseq
document's, in this package's words): it shares an author with the package
and is not an independent oracle. Beside the traces, it checks the
documented properties on every sequence as it runs: each observer learns of
an error it has not seen exactly once, a fresh observer learns only of
errors after it sampled, and with no new error there is no report.
"""
import os, random, sys


class Model:
    """count of errors, the latest, and whether an observer was told of it"""

    def __init__(self, report_unseen):
        self.seq, self.err, self.seen = 0, 0, True
        self.report_unseen = report_unseen

    def set(self, e):
        if e != 0:
            self.seq, self.err, self.seen = self.seq + 1, e, False

    def sample(self):
        if self.report_unseen and not self.seen:
            return max(self.seq - 1, 0)
        return self.seq

    def check(self, c):
        return None if c == self.seq else self.err

    def advance(self, c):
        if c == self.seq:
            return c, None
        self.seen = True
        return self.seq, self.err


def show(r):
    return "none" if r is None else "error %d" % r


def run(report_unseen, events, nobs):
    m = Model(report_unseen)
    cur = [m.sample() for _ in range(nobs)]
    # for the property checks: per observer, the errors recorded since it
    # last learned of one (or since it sampled)
    pending = [0] * nobs
    unseen_at_sample = [report_unseen and not m.seen for _ in range(nobs)]
    out = []
    for ev in events:
        kind = ev[0]
        if kind == "set":
            m.set(ev[1])
            if ev[1] != 0:
                pending = [p + 1 for p in pending]
            out.append("set %d" % ev[1])
        elif kind == "sample":
            i = ev[1]
            unseen_at_sample[i] = report_unseen and not m.seen
            cur[i] = m.sample()
            pending[i] = 0
            out.append("sample %d" % i)
        elif kind == "check":
            i = ev[1]
            r = m.check(cur[i])
            assert (r is not None) == (pending[i] > 0 or unseen_at_sample[i]), ev
            out.append("check %d %s" % (i, show(r)))
        else:
            i = ev[1]
            cur[i], r = m.advance(cur[i])
            assert (r is not None) == (pending[i] > 0 or unseen_at_sample[i]), ev
            if r is not None:
                assert r == m.err
            pending[i] = 0
            unseen_at_sample[i] = False
            out.append("adv %d %s" % (i, show(r)))
    return out


def bend_ev(ev):
    if ev[0] == "set":
        return "ESet{%d}" % ev[1]
    return {"sample": "ESample", "check": "ECheck", "adv": "EAdv"}[ev[0]] + "{%dn}" % ev[1]


PROGRAM = """import Base
import ../errseq.bend as E

type Ev is Data:
  ESet{e: U32}
  ESample{i: Nat}
  ECheck{i: Nat}
  EAdv{i: Nat}

def show(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      "none"
    case Some{e}:
      "error " ++ U32.show(e)

def cur(cs: List<&2, E.ErrseqCursor>, i: Nat) -> E.ErrseqCursor:
  Maybe.default(&2, E.ErrseqCursor, List.get(&2, E.ErrseqCursor, cs, i), E.ErrseqCursor{0n})

def go(+o: E.ErrseqOptions, evs: List<&2, Ev>, s: E.Errseq, cs: List<&2, E.ErrseqCursor>, acc: String) -> String:
  match evs:
    case Nil{}:
      acc
    case Con{ESet{+e}, t}:
      go(o, t, E.Errseq.set(s, e), cs, acc ++ "\nset " ++ U32.show(e))
    case Con{ESample{+i}, t}:
      +s1 = s
      go(o, t, s1, List.set(&2, E.ErrseqCursor, cs, i, E.Errseq.sample(o, s1)), acc ++ "\nsample " ++ Nat.show(i))
    case Con{ECheck{+i}, t}:
      +s1 = s
      +cs1 = cs
      go(o, t, s1, cs1, acc ++ "\ncheck " ++ Nat.show(i) ++ " " ++ show(E.Errseq.check(s1, cur(cs1, i))))
    case Con{EAdv{+i}, t}:
      +cs1 = cs
      +r = E.Errseq.check_and_advance(s, cur(cs1, i))
      go(o, t, E.ErrseqCheck.state(r), List.set(&2, E.ErrseqCursor, cs1, i, E.ErrseqCheck.cursor(r)), acc ++ "\nadv " ++ Nat.show(i) ++ " " ++ show(E.ErrseqCheck.error(r)))

def start(+o: E.ErrseqOptions, +n: Nat, evs: List<&2, Ev>) -> String:
  +s = E.Errseq.new()
  go(o, evs, s, List.replicate(E.ErrseqCursor, n, E.Errseq.sample(o, s)), "")

def main() -> IO(Unit):
  do IO<Unit>:
%s
"""


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect, total = [], [], 0
    for n in range(40):
        report_unseen = n % 2 == 1
        nobs = rng.randrange(1, 5)
        events = []
        for _ in range(rng.randrange(20, 120)):
            r = rng.random()
            if r < 0.3:
                events.append(("set", rng.choice([0, 5, 5, 28, 4095, rng.getrandbits(32)])))
            elif r < 0.45:
                events.append(("sample", rng.randrange(nobs)))
            elif r < 0.65:
                events.append(("check", rng.randrange(nobs)))
            else:
                events.append(("adv", rng.randrange(nobs)))
        total += len(events)
        opts = "E.ErrseqOptions.kernel()" if report_unseen else "E.ErrseqOptions.default()"
        lines.append('    IO.print("case %d" ++ start(%s, %dn, [%s]))' % (n, opts, nobs, ", ".join(bend_ev(e) for e in events)))
        expect.append("case %d" % n)
        expect.extend(run(report_unseen, events, nobs))
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write(PROGRAM % "\n".join(lines))
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print("%d events in 40 sequences" % total)


main()
