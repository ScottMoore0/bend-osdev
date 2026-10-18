#!/usr/bin/env python3
"""Differential test cases for bend-osdev-ratelimit.

Writes ref/cases.bend (a Bend program that runs random sequences of checks
and reports through ratelimit.bend, under both window policies) and
ref/expected.txt (the same sequences on the Python model below).

The model is written from the behaviour the README states: it shares an
author with the package and is not an independent oracle. As it runs it
also checks the documented properties on every sequence: for the sliding
policy and nondecreasing times, no stretch of time of length interval holds
more than burst allowed events (the trace form of the window law, which
LAWS.bend states only step by step); after a quiet interval an event is
allowed; and a report's count is the number of refusals since the last one.
"""
import os, random, sys

M64 = (1 << 64) - 1


class Model:
    def __init__(self, fixed, interval, burst):
        self.fixed, self.interval, self.burst = fixed, interval, burst
        self.log = []                 # sliding: kept times, newest first
        self.begin, self.count, self.open = 0, 0, False
        self.missed = 0

    def within(self, now, t):
        return ((now - t) & M64) < self.interval

    def recent(self, now):
        if self.fixed:
            return self.count if self.open and self.within(now, self.begin) else 0
        return sum(1 for t in self.log if self.within(now, t))

    def check(self, now):
        if self.interval == 0:
            return True
        if self.fixed:
            if not (self.open and self.within(now, self.begin)):
                self.begin, self.count, self.open = now, 0, True
            ok = self.count < self.burst
            if ok:
                self.count += 1
        else:
            self.log = [t for t in self.log if self.within(now, t)]
            ok = len(self.log) < self.burst
            if ok:
                self.log.insert(0, now)
        if not ok:
            self.missed += 1
        return ok

    def report(self):
        n, self.missed = self.missed, 0
        return n


def run(fixed, interval, burst, events, monotone):
    m = Model(fixed, interval, burst)
    out, allowed_times, refused_since = [], [], 0
    for ev in events:
        if ev is None:
            n = m.report()
            assert n == refused_since
            refused_since = 0
            out.append("report %d" % n)
            continue
        quiet = m.recent(ev) == 0
        ok = m.check(ev)
        if quiet and burst > 0:
            assert ok
        if not ok:
            refused_since += 1
        else:
            allowed_times.append(ev)
            if monotone and not fixed and interval > 0:
                assert sum(1 for t in allowed_times if ((ev - t) & M64) < interval) <= burst
        out.append("allow" if ok else "deny")
    return out


def w64(x):
    return "W.W64.from_parts(%d, %d)" % (x >> 32, x & 0xFFFFFFFF)


PROGRAM = """import Base
import ../../word64/word64.bend as W
import ../ratelimit.bend as R

type Ev is Data:
  ECheck{t: W.W64}
  EReport{}

def go(evs: List<&2, Ev>, s: R.RateLimit, acc: String) -> String:
  match evs:
    case Nil{}:
      acc
    case Con{ECheck{+t}, rest}:
      +r = R.RateLimit.check(s, t)
      go(rest, R.RateLimitStep.state(r), acc ++ "\\n" ++ Bool.pick(String, R.RateLimitStep.allowed(r), "allow", "deny"))
    case Con{EReport{}, rest}:
      +r = R.RateLimit.report(s)
      go(rest, R.RateLimitReport.state(r), acc ++ "\\nreport " ++ Nat.show(R.RateLimitReport.suppressed(r)))

def main() -> IO(Unit):
  do IO<Unit>:
%s
"""


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect, total = [], [], 0
    for n in range(40):
        fixed = n % 2 == 1
        interval = rng.choice([0, 1, 5, 10, 37, rng.randrange(1, 100)])
        burst = rng.choice([0, 1, 2, 3, 5, rng.randrange(1, 8)])
        monotone = n % 4 < 3
        # times start anywhere, sometimes near 2^64 so that they wrap
        t = rng.choice([0, rng.getrandbits(64), M64 - rng.randrange(200)])
        events = []
        for _ in range(rng.randrange(30, 150)):
            if rng.random() < 0.08:
                events.append(None)
                continue
            if monotone:
                t = (t + rng.choice([0, 0, 1, 1, 2, 3, rng.randrange(max(1, 2 * interval + 2))])) & M64
            else:
                t = (t + rng.randrange(-20, 40)) & M64
            events.append(t)
        total += len(events)
        new = "R.RateLimit.new_with(%s, %s, %d)" % ("R.RateLimitFixed{}" if fixed else "R.RateLimitSliding{}", w64(interval), burst)
        evs = ", ".join("EReport{}" if e is None else "ECheck{%s}" % w64(e) for e in events)
        lines.append('    IO.print("case %d" ++ go([%s], %s, ""))' % (n, evs, new))
        expect.append("case %d" % n)
        expect.extend(run(fixed, interval, burst, events, monotone))
    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write(PROGRAM % "\n".join(lines))
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print("%d events in 40 sequences" % total)


main()
