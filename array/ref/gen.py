#!/usr/bin/env python3
"""Differential test cases for bend-osdev-array.

Writes ref/cases.bend (a Bend program that runs random sequences of
Array.set and Array.get on arrays built by Array.new, and prints every read
and the final slots) and ref/expected.txt (the same from a Python list
model: 2^d slots, an index masked to its low d bits).

The model is written here from Base's documentation of Array ("indexes wrap
around", "the slot count is a power of two"); it shares an author with the
package. What it checks is that the compiled runtime, which holds an array
natively, agrees with the model the laws prove of Base's definitions.
"""
import random, sys

def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    rng = random.Random(seed)
    cases, expected, ops_total = [], [], 0
    for c in range(40):
        d = rng.choice([0, 1, 2, 3, 4, 5, 6, 8, 10])
        n = 1 << d
        model = [0] * n
        ops, out = [], []
        for _ in range(rng.randint(20, 160)):
            r = rng.random()
            if r < 0.15:
                i = rng.getrandbits(32)            # any U32: the mask wraps it
            elif r < 0.3:
                i = rng.choice([0, n - 1, n, 2 * n - 1, 4294967295])
            else:
                i = rng.randrange(n)
            i &= 0xFFFFFFFF
            if rng.random() < 0.5:
                v = rng.getrandbits(32)
                ops.append("ArrSet{%d, %d}" % (i, v))
                model[i & (n - 1)] = v
            else:
                ops.append("ArrGet{%d}" % i)
                out.append(str(model[i & (n - 1)]))
        ops_total += len(ops)
        cases.append((d, ops))
        expected.append(" ".join(out) + "|" + " ".join(map(str, model)))
    with open("cases.bend", "w") as f:
        f.write(HEADER)
        for k, (d, ops) in enumerate(cases):
            f.write("def case%d() -> String:\n" % k)
            f.write("  run([%s], (Array.new(U32, %dn, 0), 0), False{}, \"\")\n\n"
                    % (", ".join(ops), d))
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n")
        for k in range(len(cases)):
            f.write("    IO.print(case%d())\n" % k)
    with open("expected.txt", "w") as f:
        f.write("\n".join(expected) + "\n")
    print("%d sequences, %d operations" % (len(cases), ops_total))

HEADER = '''import Base

type ArrOp is Data:
  ArrSet{i: U32, v: U32}
  ArrGet{i: U32}

def words(xs: List<U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, Nil{}}:
      U32.show(h)
    case Con{h, t}:
      U32.show(h) ++ " " ++ words(t)

def shown(g: Bool, x: U32, first: Bool) -> String:
  match g first:
    case False{} _:
      ""
    case True{} True{}:
      U32.show(x)
    case True{} False{}:
      " " ++ U32.show(x)

# r: the array and the value the previous operation read (g: whether it was
# a read); acc: the reads so far
def run(ops: List<&2, ArrOp>, r: Array<U32> & U32, g: Bool, +acc: String) -> String:
  match ops:
    case Nil{}:
      (a, x) = r
      +s = acc ++ shown(g, x, String.is_empty(acc))
      s ++ "|" ++ words(Array.to_list(~U32, a))
    case Con{ArrSet{i, v}, t}:
      (a, x) = r
      +s = acc ++ shown(g, x, String.is_empty(acc))
      run(t, (Array.set(U32, a, i, v), 0), False{}, s)
    case Con{ArrGet{+i}, t}:
      (a, x) = r
      +s = acc ++ shown(g, x, String.is_empty(acc))
      run(t, Array.get(U32, a, i), True{}, s)

'''

main()
