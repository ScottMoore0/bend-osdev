#!/usr/bin/env python3
"""Differential test cases for bend-osdev-algo.

Writes ref/cases.bend (a Bend program printing each function's result on
each case) and ref/expected.txt (the same values computed by Python):
  * bit search: int.bit_count, int.bit_length and bit arithmetic on Python's
    arbitrary-precision integers, for random U32 and W64 values and edge
    cases;
  * bitmaps: a direct scan of the bits of Python integers;
  * binary search: the standard library's bisect.bisect_left, on random
    sorted lists, for both the list reference and the Array implementation.
"""
import bisect, os, random, sys

def ffs(x):
    return (x & -x).bit_length()

def ctz(x, w):
    return ffs(x) - 1 if x else w

def show_maybe(v):
    return "none" if v is None else str(v)

def bend_list(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []

    def case(expr, value):
        lines.append('    IO.print(%s)' % expr)
        expect.append(value)

    words = [0, 1, 2, 3, 2**31, 2**32 - 1, 40, 2**16] + [rng.getrandbits(32) for _ in range(40)]
    words += [rng.getrandbits(32) & ~((1 << rng.randrange(32)) - 1) for _ in range(10)]
    for k, x in enumerate(words):
        p = "%d " % k
        case('"pc %s" ++ Nat.show(A.bits32.popcount(%d))' % (p, x), "pc %s%d" % (p, bin(x).count("1")))
        case('"ffs %s" ++ Nat.show(A.bits32.ffs(%d))' % (p, x), "ffs %s%d" % (p, ffs(x)))
        case('"fls %s" ++ Nat.show(A.bits32.fls(%d))' % (p, x), "fls %s%d" % (p, x.bit_length()))
        case('"ctz %s" ++ Nat.show(A.bits32.ctz(%d))' % (p, x), "ctz %s%d" % (p, ctz(x, 32)))
        case('"clz %s" ++ Nat.show(A.bits32.clz(%d))' % (p, x), "clz %s%d" % (p, 32 - x.bit_length()))
        j = rng.randrange(34)
        case('"test %s" ++ Bool.show(A.bits32.test(%d, %dn))' % (p, x, j), "test %s%s" % (p, "True" if j < 32 and x >> j & 1 else "False"))

    longs = [0, 1, 2**63, 2**64 - 1, 2**32, 2**32 - 1] + [rng.getrandbits(64) for _ in range(20)]
    longs += [rng.getrandbits(64) & ~((1 << rng.randrange(64)) - 1) for _ in range(6)]
    for k, x in enumerate(longs):
        p = "%d " % k
        w = "W.W64.from_parts(%d, %d)" % (x >> 32, x & 0xFFFFFFFF)
        case('"pc64 %s" ++ Nat.show(A.bits64.popcount(%s))' % (p, w), "pc64 %s%d" % (p, bin(x).count("1")))
        case('"first64 %s" ++ show_maybe(A.bits64.first_set(%s))' % (p, w), "first64 %s%s" % (p, show_maybe(ffs(x) - 1 if x else None)))
        case('"last64 %s" ++ show_maybe(A.bits64.last_set(%s))' % (p, w), "last64 %s%s" % (p, show_maybe(x.bit_length() - 1 if x else None)))
        case('"ctz64 %s" ++ Nat.show(A.bits64.ctz(%s))' % (p, w), "ctz64 %s%d" % (p, ctz(x, 64)))
        case('"clz64 %s" ++ Nat.show(A.bits64.clz(%s))' % (p, w), "clz64 %s%d" % (p, 64 - x.bit_length()))

    for k in range(30):
        n = rng.randrange(0, 5)
        dens = rng.choice([0.02, 0.5, 0.98])
        ws = [sum((rng.random() < dens) << b for b in range(32)) for _ in range(n)]
        bits = sum(w << (32 * i) for i, w in enumerate(ws))
        size = rng.randrange(0, 32 * n + 10)
        start = rng.randrange(0, size + 5)
        nxt_set = next((i for i in range(start, size) if bits >> i & 1), size)
        nxt_clr = next((i for i in range(start, size) if not bits >> i & 1), size)
        p = "%d " % k
        case('"next_set %s" ++ Nat.show(M.bitmap.next_set(%s, %dn, %dn))' % (p, bend_list(ws), size, start), "next_set %s%d" % (p, nxt_set))
        case('"next_clear %s" ++ Nat.show(M.bitmap.next_clear(%s, %dn, %dn))' % (p, bend_list(ws), size, start), "next_clear %s%d" % (p, nxt_clr))

    for k in range(40):
        n = rng.randrange(0, 40)
        top = rng.choice([10, 1000, 2**32])
        xs = sorted(rng.randrange(top) for _ in range(n))
        key = rng.choice(xs) if xs and rng.random() < 0.5 else rng.randrange(top)
        lb = bisect.bisect_left(xs, key)
        fnd = lb if lb < n and xs[lb] == key else None
        depth = max(n - 1, 0).bit_length()
        p = "%d " % k
        case('"lb %s" ++ Nat.show(S.bsearch.lower_bound(%s, %d))' % (p, bend_list(xs), key), "lb %s%d" % (p, lb))
        case('"find %s" ++ show_maybe(S.bsearch.find(%s, %d))' % (p, bend_list(xs), key), "find %s%s" % (p, show_maybe(fnd)))
        arr = "fill(%s, 0, [0 : U32^%dn])" % (bend_list(xs), depth)
        case('"alb %s" ++ show_val(S.bsearch.array_lower_bound(%s, %d, %d))' % (p, arr, n, key), "alb %s%d" % (p, lb))
        case('"afind %s" ++ show_opt(S.bsearch.array_find(%s, %d, %d))' % (p, arr, n, key), "afind %s%s" % (p, show_maybe(fnd)))

    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("""import Base
import ../../word64/word64.bend as W
import ../algo.bend as A
import ../bitmap.bend as M
import ../bsearch.bend as S

def show_maybe(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "none"
    case Some{v}:
      Nat.show(v)

def fill(xs: List<&2, U32>, +i: U32, a: Array<U32>) -> Array<U32>:
  match xs:
    case Nil{}:
      a
    case Con{x, t}:
      fill(t, U32.inc(i), Array.set(U32, a, i, x))

def show_val(r: Array<U32> & U32) -> String:
  (a, x) = r
  U32.show(x)

def show_opt(r: Array<U32> & Maybe<&2, U32>) -> String:
  (a, m) = r
  match m:
    case None{}:
      "none"
    case Some{v}:
      U32.show(v)

""")
        # one def per 40 lines: a single long do block overflows the checker
        chunks = [lines[i:i + 40] for i in range(0, len(lines), 40)]
        for c, chunk in enumerate(chunks):
            f.write("def part%d() -> IO(Unit):\n  do IO<Unit>:\n" % c + "\n".join(chunk) + "\n\n")
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "".join("    part%d()\n" % c for c in range(len(chunks))))
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")

main()
