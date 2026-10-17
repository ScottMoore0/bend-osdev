#!/usr/bin/env python3
"""Differential test cases for bend-osdev-idalloc.

There is no ID allocator outside this repository to run (the kernel's IDR
and IDA live inside the kernel), so the reference is a model written here
from the behaviour the README states, on a Python dict: allocation scans up
from min for the first ID not in the dict.

Writes ref/cases.bend (a Bend program that runs random operation sequences
on an Idr<U32> and prints each result) and ref/expected.txt (the model's
results).
"""
import os, random, sys

def model(ops):
    d, out = {}, []
    for op in ops:
        kind = op[0]
        if kind == "alloc":
            _, lo, hi, v = op
            if lo > hi:
                out.append("a badrange")
                continue
            i = lo
            while i in d:
                i += 1
            if i > hi:
                out.append("a exhausted")
            else:
                d[i] = v
                out.append("a %d" % i)
        elif kind == "free":
            d.pop(op[1], None)
            out.append("f")
        elif kind == "find":
            out.append("g %s" % d.get(op[1], "none"))
        elif kind == "remove":
            out.append("r %s" % d.pop(op[1], "none"))
        elif kind == "replace":
            _, k, v = op
            if k in d:
                out.append("p %d" % d[k])
                d[k] = v
            else:
                out.append("p notfound")
    out.append("i " + ",".join(str(k) for k in sorted(d)))
    return out

def bend_op(op):
    kind = op[0]
    if kind == "alloc":
        return "OAlloc{%dn, %dn, %d}" % op[1:]
    if kind == "replace":
        return "OReplace{%dn, %d}" % op[1:]
    name = {"free": "OFree", "find": "OFind", "remove": "ORemove"}[kind]
    return "%s{%dn}" % (name, op[1])

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    seqs = []
    for _ in range(40):
        span = rng.choice([4, 12, 40])
        ops = []
        for _ in range(rng.randrange(5, 60)):
            r = rng.random()
            k = rng.randrange(span)
            if r < 0.45:
                lo = rng.randrange(span) if rng.random() < 0.4 else 0
                if rng.random() < 0.08:
                    ops.append(("alloc", lo + 1, lo, rng.randrange(1000)))
                else:
                    ops.append(("alloc", lo, lo + rng.randrange(span), rng.randrange(1000)))
            elif r < 0.65:
                ops.append(("free", k))
            elif r < 0.8:
                ops.append(("find", k))
            elif r < 0.9:
                ops.append(("remove", k))
            else:
                ops.append(("replace", k, rng.randrange(1000)))
        seqs.append(ops)
    lines, expect = [], []
    for n, ops in enumerate(seqs):
        lines.append('    IO.print("seq %d\\n" ++ run([%s], {(I.idr.new(U32), \"\") : I.Idr<U32> & String}))' % (n, ", ".join(bend_op(o) for o in ops)))
        expect.append("seq %d" % n)
        expect.extend(model(ops))
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("""import Base
import ../idalloc.bend as I

type Op is Data:
  OAlloc{min: Nat, max: Nat, v: U32}
  OFree{k: Nat}
  OFind{k: Nat}
  ORemove{k: Nat}
  OReplace{k: Nat, v: U32}

def show_m(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      "none"
    case Some{v}:
      U32.show(v)

def show_ids(ks: List<&2, Nat>) -> String:
  match ks:
    case Nil{}:
      ""
    case Con{k, Nil{}}:
      Nat.show(k)
    case Con{k, t}:
      Nat.show(k) ++ "," ++ show_ids(t)

def alloc_line(res: Result<&2, &2, I.IdError, I.IdrAlloc<U32>>) -> String:
  match res:
    case Done{I.IdrAlloc{t, i}}:
      "a " ++ Nat.show(i)
    case Fail{I.IdExhausted{}}:
      "a exhausted"
    case Fail{e}:
      "a badrange"

def replace_line(res: Result<&2, &2, I.IdError, I.IdrOld<U32>>) -> String:
  match res:
    case Done{I.IdrOld{t, o}}:
      "p " ++ U32.show(o)
    case Fail{e}:
      "p notfound"

def replace_state(res: Result<&2, &2, I.IdError, I.IdrOld<U32>>, r: I.Idr<U32>) -> I.Idr<U32>:
  match res:
    case Done{I.IdrOld{t, o}}:
      t
    case Fail{e}:
      r

def remove_line(p: I.Idr<U32> & Maybe<&2, U32>) -> String:
  (r, m) = p
  "r " ++ show_m(m)

def remove_state(p: I.Idr<U32> & Maybe<&2, U32>) -> I.Idr<U32>:
  (r, m) = p
  r

# the state after op, and its line of output
def step(op: Op, +r: I.Idr<U32>) -> I.Idr<U32> & String:
  match op:
    case OAlloc{+min, +max, +v}:
      +res = I.idr.alloc_range(U32, r, I.IdRange{min, max}, v)
      (I.idr.state(U32, res, r), alloc_line(res))
    case OFree{k}:
      (I.idr.free(U32, r, k), "f")
    case OFind{k}:
      (r, "g " ++ show_m(I.idr.find(U32, r, k)))
    case ORemove{+k}:
      (remove_state(I.idr.remove(U32, r, k)), remove_line(I.idr.remove(U32, r, k)))
    case OReplace{+k, +v}:
      +res = I.idr.replace(U32, r, k, v)
      (replace_state(res, r), replace_line(res))

def run.add(out: String, q: I.Idr<U32> & String) -> I.Idr<U32> & String:
  (r, line) = q
  (r, out ++ line ++ "\\n")

def run.step(op: Op, p: I.Idr<U32> & String) -> I.Idr<U32> & String:
  (r, out) = p
  run.add(out, step(op, r))

def run.fin(p: I.Idr<U32> & String) -> String:
  (r, out) = p
  out ++ "i " ++ show_ids(I.idr.ids(U32, r))

def run(ops: List<&2, Op>, p: I.Idr<U32> & String) -> String:
  match ops:
    case Nil{}:
      run.fin(p)
    case Con{op, t}:
      run(t, run.step(op, p))

""")
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(sum(len(s) for s in seqs), "operations in", len(seqs), "sequences")

main()
