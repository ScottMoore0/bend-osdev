#!/usr/bin/env python3
"""Differential test cases for bend-osdev-maple.

  python3 gen.py [seed]        writes ref/cases.bend (random operation
                               sequences, run on the tree) and
                               ref/expected.txt (the same sequences run on
                               the model below); prints the case count
  python3 gen.py --compare F   compares the tree's output (file F) with
                               expected.txt; exit 1 on a difference

The model is independent of the Bend code: a sorted Python list of
(first, last, value) triples over Python integers (so nothing wraps),
written from the README's description of the behaviour:

  * a range [first, last] holds every index first <= i <= last; no two
    entries share an index; ranges with first > last are refused (store
    fails, set and clear change nothing);
  * storing [a, b] removes every entry it overlaps and puts back the parts
    of them outside [a, b] (an entry spanning [a, b] leaves two parts);
    clearing [a, b] does the same without the new entry; erasing i clears
    the whole range of the entry holding i;
  * find(i) is the first entry with last >= i, next(i) the first with
    first > i, prev(i) the last with last < i;
  * empty_area(min, max, size) is the lowest s with s .. s + size - 1 all
    free and min <= s, s + size - 1 <= max: found here by listing the free
    runs of [min, max] (and, for narrow ranges, checked again by trying
    every s).

Balance is checked on every "stat" line: the tree reports its height, valid,
balanced and leveled; all must hold, and the height must not exceed the
largest a B-tree of that order and size can have (every node but the root
holds at least k = (order + 1) // 2 items and a root branch at least 2, so
a tree of height h >= 1 holds at least 2 k^h entries).
"""
import os, random, sys

U32MAX = 2 ** 32 - 1


class Model:
    def __init__(self):
        self.items = []  # (first, last, value), sorted by first

    def _cut(self, a, b):
        keep = []
        for f, l, v in self.items:
            if l < a or f > b:
                keep.append((f, l, v))
                continue
            if f < a:
                keep.append((f, a - 1, v))
            if l > b:
                keep.append((b + 1, l, v))
        return keep

    def set_range(self, a, b, v):
        if a > b:
            return False
        self.items = sorted(self._cut(a, b) + [(a, b, v)])
        return True

    def clear_range(self, a, b):
        if a <= b:
            self.items = sorted(self._cut(a, b))

    def lookup(self, i):
        for it in self.items:
            if it[0] <= i <= it[1]:
                return it
        return None

    def erase(self, i):
        it = self.lookup(i)
        if it is not None:
            self.clear_range(it[0], it[1])

    def load(self, i):
        it = self.lookup(i)
        return None if it is None else it[2]

    def find(self, i):
        return next((it for it in self.items if it[1] >= i), None)

    def next(self, i):
        return next((it for it in self.items if it[0] > i), None)

    def prev(self, i):
        return next((it for it in reversed(self.items) if it[1] < i), None)

    def free_runs(self, lo, hi):
        runs, start = [], lo
        for f, l, _ in self.items:
            if l < start:
                continue
            if f > hi:
                break
            if f > start:
                runs.append((start, f - 1))
            start = l + 1
            if start > hi:
                return runs
        runs.append((start, hi))
        return runs

    def empty_area(self, lo, hi, size):
        if size == 0:
            return "bad size"
        if hi < lo:
            return "bad range %d %d" % (lo, hi)
        ans = next((s for s, e in self.free_runs(lo, hi) if e - s + 1 >= size), None)
        if hi - lo <= 2000:  # narrow: try every start
            free = lambda i: self.lookup(i) is None
            brute = next((s for s in range(lo, hi - size + 2) if all(free(i) for i in range(s, s + size))), None)
            assert ans == brute, (lo, hi, size, ans, brute)
        return "busy" if ans is None else str(ans)


def max_height(n, order):
    k = (order + 1) // 2
    h = 0
    while 2 * k ** (h + 1) <= n:
        h += 1
    return h


def show(it):
    return "%d-%d:%d" % it


def show_list(xs):
    return "".join(" " + show(it) for it in xs)


def show_maybe(it):
    return " none" if it is None else " " + show(it)


ORDERS = [16, 3, 4, 5, 7, 16]


def sequence(rng, k):
    """One random operation sequence: (order, Bend ops, expected lines)."""
    m = Model()
    order = ORDERS[k % len(ORDERS)]
    scale = [16, 64, 1000, U32MAX][k % 4]
    grow = k % 6 == 5  # a long sequence: the tree grows large, then shrinks
    nops = int(os.environ.get("MAPLE_GROW", "500")) if grow else rng.randrange(20, 120)

    def key():
        if scale == U32MAX and rng.random() < 0.2:
            return rng.choice([0, 1, U32MAX - 1, U32MAX])
        return rng.randrange(scale + 1)

    def rng_range(width):
        a = key()
        if rng.random() < 0.06:
            return a, (a - 1 - rng.randrange(width + 1)) % (U32MAX + 1)  # inverted
        return a, min(U32MAX, a + rng.randrange(width + 1))

    def width():
        return rng.choice([0, 0, 1, 3, scale // 16 + 1, scale // 4 + 1])

    ops, out = [], []
    for i in range(nops):
        r = rng.random()
        if grow and rng.random() < 0.6:
            r = 0.0 if i < nops * 0.6 else 0.30  # mostly stores, then mostly clears
        if r < 0.28:
            a, b = rng_range(width())
            v = rng.randrange(1000)
            m.set_range(a, b, v)
            ops.append("RSet{%d, %d, %d}" % (a, b, v))
        elif r < 0.30:
            a, b = rng_range(width())
            v = rng.randrange(1000)
            ok = m.set_range(a, b, v)
            ops.append("RStore{%d, %d, %d}" % (a, b, v))
            out.append("store ok" if ok else "store inverted %d %d" % (a, b))
        elif r < 0.34:
            i0, v = key(), rng.randrange(1000)
            m.set_range(i0, i0, v)
            ops.append("RPut{%d, %d}" % (i0, v))
        elif r < 0.42:
            a, b = rng_range(width())
            m.clear_range(a, b)
            ops.append("RClear{%d, %d}" % (a, b))
        elif r < 0.46:
            if m.items and rng.random() < 0.7:
                f, l, _ = rng.choice(m.items)
                i0 = rng.randrange(f, l + 1)
            else:
                i0 = key()
            m.erase(i0)
            ops.append("RErase{%d}" % i0)
        elif r < 0.56:
            i0 = key()
            ops.append("RLoad{%d}" % i0)
            v = m.load(i0)
            out.append("load %d: %s" % (i0, "none" if v is None else str(v)))
        elif r < 0.60:
            i0 = key()
            ops.append("RLookup{%d}" % i0)
            out.append("lookup %d:%s" % (i0, show_maybe(m.lookup(i0))))
        elif r < 0.66:
            i0 = key()
            ops.append("RFind{%d}" % i0)
            out.append("find %d:%s" % (i0, show_maybe(m.find(i0))))
        elif r < 0.72:
            i0 = rng.choice(m.items)[1] if m.items and rng.random() < 0.5 else key()
            ops.append("RNext{%d}" % i0)
            out.append("next %d:%s" % (i0, show_maybe(m.next(i0))))
        elif r < 0.78:
            i0 = rng.choice(m.items)[0] if m.items and rng.random() < 0.5 else key()
            ops.append("RPrev{%d}" % i0)
            out.append("prev %d:%s" % (i0, show_maybe(m.prev(i0))))
        elif r < 0.82:
            ops.append("RIter{}")
            out.append("iter:%s" % show_list(m.items))
        elif r < 0.94:
            lo, hi = rng_range(scale // 2 + 1) if rng.random() < 0.9 else (key(), key())
            size = rng.choice([0, 1, 1, 2, 3, 5, scale // 32 + 1, scale // 8 + 1, rng.randrange(scale + 2)])
            if rng.random() < 0.03:
                size = U32MAX
            ops.append("RGap{%d, %d, %d}" % (lo, hi, size))
            out.append("gap %d %d %d: %s" % (lo, hi, size, m.empty_area(lo, hi, size)))
        else:
            ops.append("RStat{}")
            out.append(stat(m, order))
    ops.append("RIter{}")
    out.append("iter:%s" % show_list(m.items))
    ops.append("RStat{}")
    out.append(stat(m, order))
    return order, ops, out


def stat(m, order):
    n = len(m.items)
    return "stat %d %d True True True" % (n, max_height(n, order))


BEND_HEAD = """import Base
import ../model.bend as M
import ../node.bend as N
import ../maple.bend as T
import ../gap.bend as G

type RefOp is Data:
  RSet{a: U32, b: U32, v: U32}
  RStore{a: U32, b: U32, v: U32}
  RPut{i: U32, v: U32}
  RClear{a: U32, b: U32}
  RErase{i: U32}
  RLoad{i: U32}
  RLookup{i: U32}
  RFind{i: U32}
  RNext{i: U32}
  RPrev{i: U32}
  RIter{}
  RGap{min: U32, max: U32, size: U32}
  RStat{}

def show_e(e: M.MapleEntry<U32, U32>) -> String:
  match e:
    case M.MapleEntry{f, l, v}:
      U32.show(f) ++ "-" ++ U32.show(l) ++ ":" ++ U32.show(v)

def show_list(xs: List<&2, M.MapleEntry<U32, U32>>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, r}:
      " " ++ show_e(x) ++ show_list(r)

def show_maybe(m: Maybe<&2, M.MapleEntry<U32, U32>>) -> String:
  match m:
    case None{}:
      " none"
    case Some{x}:
      " " ++ show_e(x)

def show_value(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      "none"
    case Some{v}:
      U32.show(v)

def show_gap(r: Result<&2, &2, M.MapleError<U32>, U32>) -> String:
  match r:
    case Done{s}:
      U32.show(s)
    case Fail{M.MapleBusy{}}:
      "busy"
    case Fail{M.MapleBadSize{}}:
      "bad size"
    case Fail{M.MapleBadRange{a, b}}:
      "bad range " ++ U32.show(a) ++ " " ++ U32.show(b)
    case Fail{M.MapleInverted{a, b}}:
      "inverted"

def store_line(r: Result<&2, &2, M.MapleError<U32>, N.MapleTree<U32, U32>>) -> String:
  match r:
    case Fail{M.MapleInverted{a, b}}:
      "store inverted " ++ U32.show(a) ++ " " ++ U32.show(b)
    case Fail{e}:
      "store other"
    case Done{u}:
      "store ok"

# find from 0, then next from each answer, at most fuel times
def iter(fuel: Nat, +t: N.MapleTree<U32, U32>, cur: Maybe<&2, M.MapleEntry<U32, U32>>) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+p:
      match cur:
        case None{}:
          ""
        case Some{+x}:
          " " ++ show_e(x) ++ iter(p, t, T.Maple32.next(U32, t, M.MapleEntry.last(U32, U32, x)))

def iter_pick(same: Bool, a: String, b: String) -> String:
  match same:
    case True{}:
      "iter:" ++ a
    case False{}:
      "iter mismatch:" ++ a ++ " /" ++ b

# the entries, checked against iteration by find and next
def iter_line(+t: N.MapleTree<U32, U32>) -> String:
  +a = show_list(T.Maple32.entries(U32, t))
  +b = iter(1n+T.Maple32.size(U32, t), t, T.Maple32.find(U32, t, 0))
  iter_pick(String.eq(a, b), a, b)

def stat(+t: N.MapleTree<U32, U32>) -> String:
  "stat " ++ Nat.show(T.Maple32.size(U32, t)) ++ " " ++ Nat.show(T.Maple32.height(U32, t)) ++ " " ++ Bool.show(T.Maple32.valid(U32, t)) ++ " " ++ Bool.show(T.Maple32.balanced(U32, t)) ++ " " ++ Bool.show(T.Maple32.leveled(U32, t))

def run(ops: List<&2, RefOp>, +t: N.MapleTree<U32, U32>) -> List<&2, String>:
  match ops:
    case Nil{}:
      Nil{}
    case Con{RSet{a, b, v}, rest}:
      run(rest, T.Maple32.set_range(U32, t, a, b, v))
    case Con{RStore{+a, +b, +v}, rest}:
      Con{store_line(T.Maple32.store_range(U32, t, a, b, v)), run(rest, T.Maple32.set_range(U32, t, a, b, v))}
    case Con{RPut{i, v}, rest}:
      run(rest, T.Maple32.store(U32, t, i, v))
    case Con{RClear{a, b}, rest}:
      run(rest, T.Maple32.clear_range(U32, t, a, b))
    case Con{RErase{i}, rest}:
      run(rest, T.Maple32.erase(U32, t, i))
    case Con{RLoad{+i}, rest}:
      Con{"load " ++ U32.show(i) ++ ": " ++ show_value(T.Maple32.load(U32, t, i)), run(rest, t)}
    case Con{RLookup{+i}, rest}:
      Con{"lookup " ++ U32.show(i) ++ ":" ++ show_maybe(T.Maple32.lookup(U32, t, i)), run(rest, t)}
    case Con{RFind{+i}, rest}:
      Con{"find " ++ U32.show(i) ++ ":" ++ show_maybe(T.Maple32.find(U32, t, i)), run(rest, t)}
    case Con{RNext{+i}, rest}:
      Con{"next " ++ U32.show(i) ++ ":" ++ show_maybe(T.Maple32.next(U32, t, i)), run(rest, t)}
    case Con{RPrev{+i}, rest}:
      Con{"prev " ++ U32.show(i) ++ ":" ++ show_maybe(T.Maple32.prev(U32, t, i)), run(rest, t)}
    case Con{RIter{}, rest}:
      Con{iter_line(t), run(rest, t)}
    case Con{RGap{+a, +b, +s}, rest}:
      Con{"gap " ++ U32.show(a) ++ " " ++ U32.show(b) ++ " " ++ U32.show(s) ++ ": " ++ show_gap(G.Maple32.empty_area(U32, t, a, b, s)), run(rest, t)}
    case Con{RStat{}, rest}:
      Con{stat(t), run(rest, t)}

def print_all(xs: List<&2, String>) -> IO(Unit):
  match xs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{h, r}:
      do IO<Unit>:
        IO.print(h)
        print_all(r)

"""


def compare(got_path):
    here = os.path.dirname(os.path.abspath(__file__))
    want = open(os.path.join(here, "expected.txt")).read().splitlines()
    got = open(got_path).read().splitlines()
    bad = 0
    if len(want) != len(got):
        print("line count: expected %d, got %d" % (len(want), len(got)))
        bad += 1
    for i, (w, g) in enumerate(zip(want, got)):
        if w.startswith("stat ") and g.startswith("stat "):
            wn, wh, *wf = w.split()[1:]
            gn, gh, *gf = g.split()[1:]
            ok = (wn, wf) == (gn, gf) and int(gh) <= int(wh)
        else:
            ok = w == g
        if not ok:
            bad += 1
            if bad <= 10:
                print("line %d:\n  expected %s\n  got      %s" % (i + 1, w, g))
    if bad:
        sys.exit(1)
    print("%d cases match" % len(want))


def main():
    if len(sys.argv) > 2 and sys.argv[1] == "--compare":
        compare(sys.argv[2])
        return
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    defs, mains, expect = [], [], []
    for k in range(int(os.environ.get("MAPLE_SEQS", "48"))):
        order, ops, out = sequence(rng, k)
        defs.append("def seq%d() -> List<&2, RefOp>:\n  [%s]\n" % (k, ", ".join(ops)))
        mains.append("    print_all(run(seq%d(), T.Maple32.empty_with(U32, N.MapleOptions{%dn})))" % (k, order))
        expect.extend(out)
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write(BEND_HEAD + "\n".join(defs) + "\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(mains) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")


main()
