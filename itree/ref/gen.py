#!/usr/bin/env python3
"""Differential test cases for bend-osdev-itree.

  python3 gen.py [seed]        writes ref/cases.bend (random operation
                               sequences, run on the tree) and
                               ref/expected.txt (the same sequences run on
                               the model below); prints the case count
  python3 gen.py --compare F   compares the tree's output (file F) with
                               expected.txt; exit 1 on a difference

The model is independent of the Bend code: a plain Python list of
(start, last, value) triples, scanned in full for every query, written from
the README's description of the behaviour:

  * intervals are closed, [start, last]; [s, l] overlaps [a, b] when
    s <= b and a <= l;
  * an interval is stored at most once; setting it again replaces its value;
    an interval with start > last is refused (insert fails, set ignores it);
  * results come in key order: by start, then by last;
  * next(a, b, s, l) is the first overlapping interval whose key comes after
    (s, l).

Balance is checked on every "stat" line: the tree reports its height, which
must not exceed the largest height an AVL tree of that size can have (a
tree of height h has at least N(h) nodes, N(0) = 0, N(1) = 1,
N(h) = N(h-1) + N(h-2) + 1), and its own checks valid and balanced must hold.
"""
import os, random, sys

U32MAX = 2 ** 32 - 1


class Model:
    def __init__(self):
        self.items = []  # (start, last, value), in no particular order

    def set(self, s, l, v):
        if s > l:
            return False
        self.items = [it for it in self.items if (it[0], it[1]) != (s, l)]
        self.items.append((s, l, v))
        return True

    def remove(self, s, l):
        self.items = [it for it in self.items if (it[0], it[1]) != (s, l)]

    def in_order(self):
        return sorted(self.items, key=lambda it: (it[0], it[1]))

    def overlapping(self, a, b):
        return [it for it in self.in_order() if it[0] <= b and a <= it[1]]

    def first(self, a, b):
        ov = self.overlapping(a, b)
        return ov[0] if ov else None

    def next(self, a, b, s, l):
        for it in self.overlapping(a, b):
            if (it[0], it[1]) > (s, l):
                return it
        return None

    def lookup(self, s, l):
        for it in self.items:
            if (it[0], it[1]) == (s, l):
                return it[2]
        return None

    def max_last(self):
        return max((it[1] for it in self.items), default=None)


def max_avl_height(n):
    sizes = [0, 1]
    while sizes[-1] <= n:
        sizes.append(sizes[-1] + sizes[-2] + 1)
    return len(sizes) - 2  # the largest h with N(h) <= n


def show(it):
    return "%d-%d:%d" % it


def show_list(xs):
    return "".join(" " + show(it) for it in xs)


def show_maybe(it):
    return " none" if it is None else " " + show(it)


def sequence(rng, k):
    """One random operation sequence: (Bend op, expected lines)."""
    m = Model()
    scale = [16, 64, 1000, U32MAX][k % 4]
    grow = k % 6 == 5  # a long sequence: the tree grows large, then shrinks
    nops = 600 if grow else rng.randrange(20, 120)

    def key():
        if scale == U32MAX and rng.random() < 0.2:
            return rng.choice([0, 1, U32MAX - 1, U32MAX])
        return rng.randrange(scale + 1)

    def interval():
        s = key()
        if rng.random() < 0.08:
            return s, (s - 1 - rng.randrange(scale // 4 + 1)) % (U32MAX + 1)  # often inverted
        return s, min(U32MAX, s + rng.randrange(scale // 4 + 2))

    ops, out = [], []
    for i in range(nops):
        r = rng.random()
        if grow and rng.random() < 0.6:
            r = 0.0 if i < nops * 0.6 else 0.5  # mostly sets, then mostly removes
        if r < 0.35:
            s, l = interval()
            v = rng.randrange(1000)
            m.set(s, l, v)
            ops.append("RSet{%d, %d, %d}" % (s, l, v))
        elif r < 0.42:
            s, l = interval()
            v = rng.randrange(1000)
            ok = m.set(s, l, v)
            ops.append("RIns{%d, %d, %d}" % (s, l, v))
            out.append("ins ok" if ok else "ins inverted %d %d" % (s, l))
        elif r < 0.55:
            if m.items and rng.random() < 0.8:
                s, l, _ = rng.choice(m.items)
            else:
                s, l = interval()
            m.remove(s, l)
            ops.append("RRem{%d, %d}" % (s, l))
        elif r < 0.65:
            a, b = interval()
            if a > b:
                a, b = b, a
            ops.append("ROv{%d, %d}" % (a, b))
            out.append("ov %d %d:%s" % (a, b, show_list(m.overlapping(a, b))))
        elif r < 0.70:
            p = key()
            ops.append("RStab{%d}" % p)
            out.append("stab %d:%s" % (p, show_list(m.overlapping(p, p))))
        elif r < 0.76:
            a, b = interval()
            if a > b:
                a, b = b, a
            ops.append("RFirst{%d, %d}" % (a, b))
            out.append("first %d %d:%s" % (a, b, show_maybe(m.first(a, b))))
        elif r < 0.82:
            a, b = interval()
            if a > b:
                a, b = b, a
            if m.items and rng.random() < 0.7:
                s, l, _ = rng.choice(m.items)
            else:
                s, l = key(), key()
            ops.append("RNext{%d, %d, %d, %d}" % (a, b, s, l))
            out.append("next %d %d %d %d:%s" % (a, b, s, l, show_maybe(m.next(a, b, s, l))))
        elif r < 0.88:
            a, b = interval()
            if a > b:
                a, b = b, a
            ops.append("RIter{%d, %d}" % (a, b))
            out.append("iter %d %d:%s" % (a, b, show_list(m.overlapping(a, b))))
        elif r < 0.94:
            if m.items and rng.random() < 0.6:
                s, l, _ = rng.choice(m.items)
            else:
                s, l = interval()
            ops.append("RLook{%d, %d}" % (s, l))
            v = m.lookup(s, l)
            out.append("look %d %d: %s" % (s, l, "none" if v is None else str(v)))
        else:
            ops.append("RStat{}")
            out.append(stat(m))
    ops.append("RStat{}")
    out.append(stat(m))
    return ops, out


def stat(m):
    n = len(m.items)
    ml = m.max_last()
    return "stat %d %d True True %s" % (n, max_avl_height(n), "none" if ml is None else str(ml))


BEND_HEAD = """import Base
import ../itree.bend as T

type RefOp is Data:
  RSet{s: U32, l: U32, v: U32}
  RIns{s: U32, l: U32, v: U32}
  RRem{s: U32, l: U32}
  ROv{a: U32, b: U32}
  RStab{p: U32}
  RFirst{a: U32, b: U32}
  RNext{a: U32, b: U32, s: U32, l: U32}
  RIter{a: U32, b: U32}
  RLook{s: U32, l: U32}
  RStat{}

def show_e(e: T.ITreeEntry<U32, U32>) -> String:
  match e:
    case T.ITreeEntry{s, l, v}:
      U32.show(s) ++ "-" ++ U32.show(l) ++ ":" ++ U32.show(v)

def show_list(xs: List<&2, T.ITreeEntry<U32, U32>>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, r}:
      " " ++ show_e(x) ++ show_list(r)

def show_maybe(m: Maybe<&2, T.ITreeEntry<U32, U32>>) -> String:
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

# first, then next from each answer, at most fuel times
def iter(fuel: Nat, +t: T.ITree<U32, U32>, +a: U32, +b: U32, cur: Maybe<&2, T.ITreeEntry<U32, U32>>) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+p:
      match cur:
        case None{}:
          ""
        case Some{+x}:
          " " ++ show_e(x) ++ iter(p, t, a, b, T.ITree32.next(U32, t, a, b, T.ITreeEntry.start(U32, U32, x), T.ITreeEntry.last(U32, U32, x)))

def ins_line(+s: U32, +l: U32, r: Result<&2, &2, T.ITreeError<U32>, T.ITree<U32, U32>>) -> String:
  match r:
    case Fail{e}:
      "ins inverted " ++ U32.show(s) ++ " " ++ U32.show(l)
    case Done{u}:
      "ins ok"

def stat(+t: T.ITree<U32, U32>) -> String:
  "stat " ++ Nat.show(T.ITree32.size(U32, t)) ++ " " ++ Nat.show(T.ITree32.height(U32, t)) ++ " " ++ Bool.show(T.ITree32.valid(U32, t)) ++ " " ++ Bool.show(T.ITree32.balanced(U32, t)) ++ " " ++ show_value(T.ITree32.max_last(U32, t))

def run(ops: List<&2, RefOp>, +t: T.ITree<U32, U32>) -> List<&2, String>:
  match ops:
    case Nil{}:
      Nil{}
    case Con{RSet{s, l, v}, rest}:
      run(rest, T.ITree32.set(U32, t, s, l, v))
    case Con{RIns{+s, +l, +v}, rest}:
      Con{ins_line(s, l, T.ITree32.insert(U32, t, s, l, v)), run(rest, T.ITree32.set(U32, t, s, l, v))}
    case Con{RRem{s, l}, rest}:
      run(rest, T.ITree32.remove(U32, t, s, l))
    case Con{ROv{+a, +b}, rest}:
      Con{"ov " ++ U32.show(a) ++ " " ++ U32.show(b) ++ ":" ++ show_list(T.ITree32.overlapping(U32, t, a, b)), run(rest, t)}
    case Con{RStab{+p}, rest}:
      Con{"stab " ++ U32.show(p) ++ ":" ++ show_list(T.ITree32.stab(U32, t, p)), run(rest, t)}
    case Con{RFirst{+a, +b}, rest}:
      Con{"first " ++ U32.show(a) ++ " " ++ U32.show(b) ++ ":" ++ show_maybe(T.ITree32.first(U32, t, a, b)), run(rest, t)}
    case Con{RNext{+a, +b, +s, +l}, rest}:
      Con{"next " ++ U32.show(a) ++ " " ++ U32.show(b) ++ " " ++ U32.show(s) ++ " " ++ U32.show(l) ++ ":" ++ show_maybe(T.ITree32.next(U32, t, a, b, s, l)), run(rest, t)}
    case Con{RIter{+a, +b}, rest}:
      Con{"iter " ++ U32.show(a) ++ " " ++ U32.show(b) ++ ":" ++ iter(1n+T.ITree32.size(U32, t), t, a, b, T.ITree32.first(U32, t, a, b)), run(rest, t)}
    case Con{RLook{+s, +l}, rest}:
      Con{"look " ++ U32.show(s) ++ " " ++ U32.show(l) ++ ": " ++ show_value(T.ITree32.lookup(U32, t, s, l)), run(rest, t)}
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
            wn, wh, wv, wb, wm = w.split()[1:]
            gn, gh, gv, gb, gm = g.split()[1:]
            ok = (wn, wv, wb, wm) == (gn, gv, gb, gm) and int(gh) <= int(wh)
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
    for k in range(48):
        ops, out = sequence(rng, k)
        defs.append("def seq%d() -> List<&2, RefOp>:\n  [%s]\n" % (k, ", ".join(ops)))
        mains.append("    print_all(run(seq%d(), T.ITree32.empty(U32)))" % k)
        expect.extend(out)
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write(BEND_HEAD + "\n".join(defs) + "\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(mains) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")


main()
