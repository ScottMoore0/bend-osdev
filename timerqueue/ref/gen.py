#!/usr/bin/env python3
"""Differential test cases for bend-osdev-timerqueue.

Writes ref/cases.bend (a Bend program that runs random sequences of adds,
deletes, next-expiry queries and expiries through the default timer queue,
TimerQueueList) and ref/expected.txt (the same sequences on a Python model
built on heapq, Python's binary heap, with deleted timers dropped lazily).

The model is written from the behaviour the README states and shares an
author with the package; the heap is a different data structure from the
package's sorted list, but there is no external timer queue to compare
with. As it runs, the model also checks the documented properties: every
expiry answers timers in nondecreasing expiry order, ties by insertion
order, all due and none deleted, and leaves only timers that expire later;
the next expiry is the minimum of the timers held.
"""
import heapq, os, random, sys

M64 = (1 << 64) - 1


def run(events):
    heap, live, handles, out, nid = [], set(), [], [], 0
    for ev in events:
        kind = ev[0]
        if kind == "add":
            heapq.heappush(heap, (ev[1], nid))
            live.add(nid)
            handles.append((ev[1], nid))
            out.append("add %d" % nid)
            nid += 1
        elif kind == "del":
            if ev[1] < len(handles):
                live.discard(handles[ev[1]][1])
            out.append("del")
        elif kind == "next":
            while heap and heap[0][1] not in live:
                heapq.heappop(heap)
            if heap:
                assert heap[0][0] == min(e for e, i in heap if i in live)
            out.append("next %s" % (heap[0][0] if heap else "none"))
        else:
            now, fired = ev[1], []
            while heap and (heap[0][1] not in live or heap[0][0] <= now):
                e, i = heapq.heappop(heap)
                if i in live:
                    live.discard(i)
                    fired.append((e, i))
            assert fired == sorted(fired)
            assert all(i not in live for e, i in fired)
            assert all(e > now for e, i in heap if i in live)
            out.append("fired" + "".join(" %d#%d" % f for f in fired))
    return out


def w64(x):
    return "W.W64.from_parts(%d, %d)" % (x >> 32, x & 0xFFFFFFFF)


PROGRAM = """import Base
import ../../word64/word64.bend as W
import ../timer.bend as T
import ../timerqueue.bend as Q

type Ev is Data:
  EAdd{t: W.W64}
  EDel{k: Nat}
  ENext{}
  EExp{t: W.W64}

def show(xs: List<&2, T.TqTimer>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, t}:
      " " ++ W.W64.show(T.TqTimer.expiry(x)) ++ "#" ++ Nat.show(T.TqTimer.id(x)) ++ show(t)

def next(m: Maybe<&2, W.W64>) -> String:
  match m:
    case None{}:
      "none"
    case Some{t}:
      W.W64.show(t)

def handle(hs: List<&2, T.TqTimer>, k: Nat) -> T.TqTimer:
  Maybe.default(&2, T.TqTimer, List.get(&2, T.TqTimer, hs, k), T.TqTimer{W.W64.zero(), 1000000n})

def go(evs: List<&2, Ev>, q: Q.TimerQueue<List<&2, T.TqTimer>>, hs: List<&2, T.TqTimer>, acc: String) -> String:
  match evs:
    case Nil{}:
      acc
    case Con{EAdd{+t}, rest}:
      +r = Q.TimerQueueList.add(q, t)
      +x = Q.TqAdded.timer(List<&2, T.TqTimer>, r)
      go(rest, Q.TqAdded.queue(List<&2, T.TqTimer>, r), List.append(&2, T.TqTimer, hs, [x]), acc ++ "\\nadd " ++ Nat.show(T.TqTimer.id(x)))
    case Con{EDel{+k}, rest}:
      +hs1 = hs
      go(rest, Q.TimerQueueList.delete(q, handle(hs1, k)), hs1, acc ++ "\\ndel")
    case Con{ENext{}, rest}:
      +q1 = q
      go(rest, q1, hs, acc ++ "\\nnext " ++ next(Q.TimerQueueList.next_expiry(q1)))
    case Con{EExp{+t}, rest}:
      +r = Q.TimerQueueList.expire(q, t)
      go(rest, Q.TqExpired.queue(List<&2, T.TqTimer>, r), hs, acc ++ "\\nfired" ++ show(Q.TqExpired.fired(List<&2, T.TqTimer>, r)))

def main() -> IO(Unit):
  do IO<Unit>:
%s
"""


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect, total = [], [], 0
    for n in range(40):
        # times near 0, around 2^32 (where the high half changes) or anywhere
        base = rng.choice([0, (1 << 32) - 50, rng.getrandbits(64) & ~0xFFFF])
        span = rng.choice([20, 100, 1000])
        now, events, added = base, [], 0
        for _ in range(rng.randrange(20, 120)):
            r = rng.random()
            if r < 0.45:
                events.append(("add", (base + rng.randrange(span)) & M64))
                added += 1
            elif r < 0.6:
                events.append(("del", rng.randrange(added + 2)))
            elif r < 0.7:
                events.append(("next",))
            else:
                now = (now + rng.randrange(span // 4 + 1)) & M64
                events.append(("exp", now))
        total += len(events)
        def ev(e):
            if e[0] == "add":
                return "EAdd{%s}" % w64(e[1])
            if e[0] == "del":
                return "EDel{%dn}" % e[1]
            if e[0] == "next":
                return "ENext{}"
            return "EExp{%s}" % w64(e[1])
        lines.append('    IO.print("case %d" ++ go([%s], Q.TimerQueueList.new(), [], ""))' % (n, ", ".join(ev(e) for e in events)))
        expect.append("case %d" % n)
        expect.extend(run(events))
    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write(PROGRAM % "\n".join(lines))
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print("%d events in 40 sequences" % total)


main()
