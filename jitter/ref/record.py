#!/usr/bin/env python3
"""Records time deltas for the jitter tests: the nanoseconds each SHA3-256
of a counter takes, measured with time.perf_counter_ns (a monotonic
clock), as jitterclock measures its hash loop. Writes one delta per line.

    python3 record.py N > recorded.txt

recorded.txt in this directory was made this way (N = 4000), on WSL2
(Linux 6.6) on an x86-64 PC, and is kept so that the tests are
repeatable; any recording works.
"""
import hashlib, sys, time

n = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
out = []
prev = time.perf_counter_ns()
for i in range(n):
    hashlib.sha3_256(i.to_bytes(8, "little")).digest()
    now = time.perf_counter_ns()
    out.append(now - prev)
    prev = now
sys.stdout.write("".join("%d\n" % d for d in out))
