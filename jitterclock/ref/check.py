#!/usr/bin/env python3
"""Checks one run of stamps.bend against Python's own reading of
CLOCK_MONOTONIC (time.clock_gettime_ns), taken just before and just after
the run:

    python3 check.py LANE BEFORE AFTER < output

The output is two lines: 200 stamps, then their deltas. Every lane: the
stamps never go back, the deltas are exactly the differences of
consecutive stamps (Python's integers), and the stamps span no more time
than Python saw pass. Native lane (clock_gettime(CLOCK_MONOTONIC), the
clock Python reads): every stamp lies between Python's two readings. The
JavaScript lane's clock (process.hrtime.bigint() under Bun) is monotonic
but counts from its own origin, so there the stamps are not compared with
Python's readings, only their span.
"""
import sys

lane, before, after = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
lines = sys.stdin.read().split("\n")
ts = [int(x) for x in lines[0].split()]
ds = [int(x) for x in lines[1].split()]
bad = []
if len(ts) != 200:
    bad.append("%d stamps, not 200" % len(ts))
if any(b < a for a, b in zip(ts, ts[1:])):
    bad.append("a stamp went back")
if ds != [(b - a) % (1 << 64) for a, b in zip(ts, ts[1:])]:
    bad.append("the deltas are not the stamps' differences")
if ts and ts[-1] - ts[0] > after - before:
    bad.append("the stamps span %d ns, more than the %d ns Python saw" % (ts[-1] - ts[0], after - before))
if lane == "native" and ts and not (before <= ts[0] and ts[-1] <= after):
    bad.append("the stamps are not within Python's readings")
if bad:
    print(lane + ": " + "; ".join(bad))
    sys.exit(1)
print("%s: 200 stamps, %d ns apart on average" % (lane, (ts[-1] - ts[0]) // 199))
