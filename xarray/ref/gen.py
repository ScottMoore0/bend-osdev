#!/usr/bin/env python3
"""Differential test cases for bend-osdev-xarray.

Writes ref/cases.bend (a Bend program that runs random sequences of XArray
operations and prints the answer of every query) and ref/expected.txt (the
same answers from an independent model written here: a Python dict from index
to value, and one Python set per mark).

The model follows the behaviour the README documents:
  * store(i, v) puts v at i; the index keeps its marks; insert(i, v) does the
    same if i holds no entry, and is busy (changing nothing) if it does;
  * erase(i) removes the entry at i and clears its marks;
  * find(s) is the smallest index >= s holding an entry, find_last(s) the
    largest <= s; range(a, b) lists the entries with a <= index <= b in
    ascending order (none when a > b);
  * set_mark(i, m) marks i only if i holds an entry; clear_mark(i, m) unmarks
    it; find_marked(s, m) is the smallest marked index >= s.

Each sequence starts from the empty array. Indices are drawn so that the tree
is exercised at both ends and in the middle: small indices, clusters around a
few random bases, the extremes (0, 2^31 - 1, 2^31, 2^32 - 1) and uniform
32-bit values, with most operations reusing an index seen before.
"""
import os, random, sys

TOP = 2 ** 32 - 1
EXTREMES = [0, 1, 2 ** 31 - 1, 2 ** 31, TOP - 1, TOP]


class Model:
    def __init__(self):
        self.d = {}
        self.marks = [set(), set(), set()]

    def store(self, i, v):
        self.d[i] = v

    def erase(self, i):
        self.d.pop(i, None)
        for s in self.marks:
            s.discard(i)

    def find(self, s):
        ks = [k for k in self.d if k >= s]
        return min(ks) if ks else None

    def find_last(self, s):
        ks = [k for k in self.d if k <= s]
        return max(ks) if ks else None

    def range(self, a, b):
        return sorted((k, v) for k, v in self.d.items() if a <= k <= b)

    def set_mark(self, i, m):
        if i in self.d:
            self.marks[m].add(i)

    def clear_mark(self, i, m):
        self.marks[m].discard(i)

    def find_marked(self, s, m):
        ks = [k for k in self.marks[m] if k >= s]
        return min(ks) if ks else None


def show(x):
    return "none" if x is None else str(x)


def sequence(rng, n):
    """n random operations, as (Bend constructor, expected line or None)."""
    model = Model()
    bases = [rng.randrange(TOP + 1) for _ in range(3)]
    seen = []

    def index():
        r = rng.random()
        if seen and r < 0.6:
            i = rng.choice(seen)
            if rng.random() < 0.3:  # a neighbour of a known index
                i = min(TOP, max(0, i + rng.choice([-2, -1, 1, 2])))
            return i
        r = rng.random()
        if r < 0.3:
            i = rng.randrange(64)
        elif r < 0.6:
            i = min(TOP, max(0, rng.choice(bases) + rng.randrange(-32, 33)))
        elif r < 0.75:
            i = rng.choice(EXTREMES)
        else:
            i = rng.randrange(TOP + 1)
        seen.append(i)
        return i

    ops = []
    for _ in range(n):
        r = rng.random()
        if r < 0.25:
            i, v = index(), rng.randrange(TOP + 1)
            model.store(i, v)
            ops.append(("OStore{%d, %d}" % (i, v), None))
        elif r < 0.29:
            i, v = index(), rng.randrange(TOP + 1)
            busy = i in model.d
            if not busy:
                model.store(i, v)
            ops.append(("OInsert{%d, %d}" % (i, v), "I " + ("busy" if busy else "ok")))
        elif r < 0.33:
            i = index()
            model.erase(i)
            ops.append(("OErase{%d}" % i, None))
        elif r < 0.45:
            i = index()
            ops.append(("OLoad{%d}" % i, "L " + show(model.d.get(i))))
        elif r < 0.55:
            s = index()
            ops.append(("OFind{%d}" % s, "F " + show(model.find(s))))
        elif r < 0.63:
            s = index()
            ops.append(("OLast{%d}" % s, "B " + show(model.find_last(s))))
        elif r < 0.66:
            ops.append(("OEmpty{}", "E " + ("1" if not model.d else "0")))
        elif r < 0.72:
            a, b = sorted([index(), index()])
            if rng.random() < 0.1:
                a, b = b, a
            body = "".join(" %d=%d" % kv for kv in model.range(a, b))
            ops.append(("ORange{%d, %d}" % (a, b), "R" + body))
        elif r < 0.82:
            i, m = index(), rng.randrange(3)
            model.set_mark(i, m)
            ops.append(("OSet{%d, %d}" % (i, m), None))
        elif r < 0.87:
            i, m = index(), rng.randrange(3)
            model.clear_mark(i, m)
            ops.append(("OClear{%d, %d}" % (i, m), None))
        elif r < 0.93:
            i, m = index(), rng.randrange(3)
            ops.append(("OMark{%d, %d}" % (i, m), "M " + ("1" if i in model.marks[m] else "0")))
        else:
            s, m = index(), rng.randrange(3)
            ops.append(("OFindMarked{%d, %d}" % (s, m), "FM " + show(model.find_marked(s, m))))
    # every sequence ends by asking whether the array is empty
    ops.append(("OEmpty{}", "E " + ("1" if not model.d else "0")))
    return ops


PROGRAM = '''import Base
import ../xarray.bend as X

type Op is Data:
  OStore{i: U32, v: U32}
  OInsert{i: U32, v: U32}
  OErase{i: U32}
  OLoad{i: U32}
  OFind{s: U32}
  OLast{s: U32}
  OEmpty{}
  ORange{a: U32, b: U32}
  OSet{i: U32, m: U32}
  OClear{i: U32, m: U32}
  OMark{i: U32, m: U32}
  OFindMarked{s: U32, m: U32}

def mark_of.go(n: Nat) -> X.XMark:
  match n:
    case 0n:
      X.XMark0{}
    case 1n+p:
      match p:
        case 0n:
          X.XMark1{}
        case 1n+q:
          X.XMark2{}

def mark_of(m: U32) -> X.XMark:
  mark_of.go(U32.to_nat(m))

def show_index(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      "none"
    case Some{k}:
      U32.show(k)

def show_bool(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def show_entries(xs: List<&2, X.XEntry<U32>>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      match h:
        case X.XEntry{k, v}:
          " " ++ U32.show(k) ++ "=" ++ U32.show(v) ++ show_entries(t)

def show_insert(r: Result<&2, &2, X.XArrayError, X.XArray<U32>>) -> String:
  match r:
    case Fail{e}:
      "busy"
    case Done{t}:
      "ok"

def after_insert(r: Result<&2, &2, X.XArrayError, X.XArray<U32>>, t: X.XArray<U32>) -> X.XArray<U32>:
  match r:
    case Fail{e}:
      t
    case Done{u}:
      u

# the line a query prints ("" for an update)
def line(op: Op, +t: X.XArray<U32>) -> String:
  match op:
    case OLoad{i}:
      "L " ++ show_index(X.XArray.load(U32, t, i))
    case OInsert{i, v}:
      "I " ++ show_insert(X.XArray.insert(U32, t, i, v))
    case OFind{s}:
      "F " ++ show_index(X.XArray.find(U32, t, s))
    case OLast{s}:
      "B " ++ show_index(X.XArray.find_last(U32, t, s))
    case OEmpty{}:
      "E " ++ show_bool(X.XArray.is_empty(U32, t))
    case ORange{a, b}:
      "R" ++ show_entries(X.XArray.range(U32, t, a, b))
    case OMark{i, m}:
      "M " ++ show_bool(X.XArray.get_mark(U32, t, i, mark_of(m)))
    case OFindMarked{s, m}:
      "FM " ++ show_index(X.XArray.find_marked(U32, t, s, mark_of(m)))
    case other:
      ""

# the array after an update (unchanged after a query)
def apply(op: Op, +t: X.XArray<U32>) -> X.XArray<U32>:
  match op:
    case OStore{i, v}:
      X.XArray.store(U32, t, i, v)
    case OInsert{i, v}:
      after_insert(X.XArray.insert(U32, t, i, v), t)
    case OErase{i}:
      X.XArray.erase(U32, t, i)
    case OSet{i, m}:
      X.XArray.set_mark(U32, t, i, mark_of(m))
    case OClear{i, m}:
      X.XArray.clear_mark(U32, t, i, mark_of(m))
    case other:
      t

# two lines joined, skipping an empty one
def join(l: String, r: String) -> String:
  match l:
    case SNil{}:
      r
    case SCon{h, t}:
      match r:
        case SNil{}:
          SCon{h, t}
        case SCon{rh, rt}:
          SCon{h, t} ++ "\\n" ++ SCon{rh, rt}

def run(ops: List<&2, Op>, +t: X.XArray<U32>) -> String:
  match ops:
    case Nil{}:
      ""
    case Con{+op, rest}:
      join(line(op, t), run(rest, apply(op, t)))

%s
def main() -> IO(Unit):
  do IO<Unit>:
%s
'''


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    seqs = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    length = int(sys.argv[3]) if len(sys.argv) > 3 else 300
    defs, calls, expect = [], [], []
    for k in range(seqs):
        cons = []
        for c, e in sequence(rng, length):
            cons.append(c)
            if e is not None:
                expect.append(e)
        # one def per sequence: a list literal of a few hundred elements
        defs.append("def seq%d() -> List<&2, Op>:\n  [%s]\n" % (k, ", ".join(cons)))
        calls.append("    IO.print(run(seq%d(), X.XArray.empty(U32)))" % k)
    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write(PROGRAM % ("\n".join(defs), "\n".join(calls)))
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "queries over", seqs * length, "operations in", seqs, "sequences")


main()
