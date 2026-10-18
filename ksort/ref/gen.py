#!/usr/bin/env python3
"""Differential test cases for bend-osdev-ksort, against Python's sorted.

Python's sorted is a stable sort (the language reference guarantees it), so
it is an independent reference for both orderings ksort offers:

* list_sort with U32.is_le and U32.is_ge, on random lists: sorted(xs) and
  sorted(xs, reverse=True);
* list_sort_by with the key x >> 8, on lists with many equal keys: the very
  same list as sorted(xs, key=lambda x: x >> 8), elements of equal key in
  their input order (stability);
* heap_sort on Arrays of 2^d slots (d from 0 to 9) with n from 0 to 2^d:
  the first n slots are sorted(their old values), the rest unchanged;
  heap_sort_by with the key x >> 8 (not stable): the first n slots' keys are
  sorted, and their values are the same multiset.

Writes ref/cases.bend and ref/expected.txt.
"""
import os, random, sys

def lit(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"

def show(xs):
    return ",".join(str(x) for x in xs) if xs else "-"

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    defs, calls, expect = [], [], []
    n_cases = 0
    for c in range(30):
        n = rng.choice([0, 1, 2, 3, rng.randrange(200), rng.randrange(400)])
        top = rng.choice([4, 1000, 2**32])
        xs = [rng.randrange(top) for _ in range(n)]
        defs.append("def c%d() -> String:\n  +xs = {%s : List<&2, U32>}\n  show(K.ksort.list_sort(~U32, ~U32.is_le, xs)) ++ \" \" ++ show(K.ksort.list_sort(~U32, ~U32.is_ge, xs))\n" % (c, lit(xs)))
        expect.append(show(sorted(xs)) + " " + show(sorted(xs, reverse=True)))
        calls.append("c%d()" % c)
        n_cases += 1
    for c in range(30, 50):
        n = rng.randrange(300)
        xs = [rng.randrange(8) * 256 + rng.randrange(256) for _ in range(n)]
        defs.append("def c%d() -> String:\n  show(K.ksort.list_sort_by(~U32, ~key8, %s))\n" % (c, lit(xs)))
        expect.append(show(sorted(xs, key=lambda x: x >> 8)))
        calls.append("c%d()" % c)
        n_cases += 1
    for c in range(50, 80):
        d = rng.randrange(10)
        size = 2 ** d
        xs = [rng.randrange(2048) for _ in range(size)]
        n = rng.choice([0, size, rng.randrange(size + 1)])
        by = c >= 70
        if by:
            defs.append("def c%d() -> String:\n  keys(heap_by(%dn, %s, %d), %dn)\n" % (c, d, lit(xs), n, n))
            pre = xs[:n]
            ks = sorted(x >> 8 for x in pre)
            expect.append(show(ks) + " " + show(sorted(pre)) + " " + show(xs[n:]))
        else:
            defs.append("def c%d() -> String:\n  show(heap(%dn, %s, %d))\n" % (c, d, lit(xs), n))
            expect.append(show(sorted(xs[:n]) + xs[n:]))
        calls.append("c%d()" % c)
        n_cases += 1
    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write("""import Base
import ../ksort.bend as K
import ../heapsort.bend as H

def show(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      "-"
    case Con{x, Nil{}}:
      U32.show(x)
    case Con{x, t}:
      U32.show(x) ++ "," ++ show(t)

def key8(x: U32) -> Nat:
  U32.to_nat(U32.shrn(x, 8n))

def slots(xs: List<&1, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{x, slots(t)}

def fill.go(xs: List<&2, U32>, a: Array<U32>, +i: U32) -> Array<U32>:
  match xs:
    case Nil{}:
      a
    case Con{x, t}:
      fill.go(t, Array.set(U32, a, i, x), U32.inc(i))

def heap(d: Nat, xs: List<&2, U32>, n: U32) -> List<&2, U32>:
  slots(Array.to_list(~U32, H.ksort.heap_sort(~U32, ~U32.is_le, fill.go(xs, Array.new(U32, d, 0), 0), n)))

def heap_by(d: Nat, xs: List<&2, U32>, n: U32) -> List<&2, U32>:
  slots(Array.to_list(~U32, H.ksort.heap_sort_by(~U32, ~key8, fill.go(xs, Array.new(U32, d, 0), 0), n)))

def shift8(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{U32.shrn(x, 8n), shift8(t)}

# the keys of the first n slots, their values sorted, and the other slots
def keys(+ys: List<&2, U32>, +n: Nat) -> String:
  +pre = List.take(&2, U32, ys, n)
  show(shift8(pre)) ++ " " ++ show(K.ksort.list_sort(~U32, ~U32.is_le, pre)) ++ " " ++ show(List.drop(&2, U32, ys, n))

""")
        f.write("\n".join(defs) + "\n")
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join("    IO.print(%s)" % c for c in calls) + "\n")
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print(n_cases, "sorts")

main()
