#!/usr/bin/env python3
"""Differential test cases for bend-osdev-ringbuf.

Writes ref/cases.bend (a Bend program that runs random operation sequences
on rings of several capacities, each on the Array ring of ringbuf.bend and
on the list model of model.bend, and prints each result) and
ref/expected.txt (the same operations on Python's collections.deque with a
capacity check, an implementation outside this repository, for both).

The sequences are long enough that the counters pass the capacity many
times, so the slot index wraps and the counters are renormalised often.
"""
import collections, os, random, sys

def model(order, ops):
    cap = 1 << order
    q, out = collections.deque(), []
    for op in ops:
        kind = op[0]
        if kind == "push":
            if len(q) == cap:
                out.append("push full")
            else:
                q.append(op[1])
                out.append("push ok")
        elif kind == "pop":
            out.append("pop %d" % q.popleft() if q else "pop empty")
        elif kind == "peek":
            out.append("peek %d" % q[0] if q else "peek empty")
        elif kind == "push_list":
            n = min(len(op[1]), cap - len(q))
            q.extend(op[1][:n])
            out.append("in %d" % n)
        elif kind == "pop_list":
            n = min(op[1], len(q))
            out.append("out " + ",".join(str(q.popleft()) for _ in range(n)))
        out.append("len %d avail %d" % (len(q), cap - len(q)))
    return out

def bend_op(op):
    kind = op[0]
    if kind == "push":
        return "OPush{%d}" % op[1]
    if kind == "pop":
        return "OPop{}"
    if kind == "peek":
        return "OPeek{}"
    if kind == "push_list":
        return "OPushList{[%s]}" % ", ".join(str(x) for x in op[1])
    return "OPopList{%dn}" % op[1]

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []
    total = 0
    for n in range(24):
        order = rng.choice([0, 1, 2, 3, 4])
        cap = 1 << order
        ops = []
        for _ in range(rng.randrange(20, 120)):
            r = rng.random()
            if r < 0.4:
                ops.append(("push", rng.getrandbits(32)))
            elif r < 0.7:
                ops.append(("pop",))
            elif r < 0.8:
                ops.append(("peek",))
            elif r < 0.9:
                ops.append(("push_list", [rng.getrandbits(32) for _ in range(rng.randrange(cap + 3))]))
            else:
                ops.append(("pop_list", rng.randrange(cap + 3)))
        total += len(ops)
        lines.append('    IO.print("ring %d" ++ run([%s], {(R.ring.new(%dn), "") : R.RingBuf & String}))' % (n, ", ".join(bend_op(o) for o in ops), order))
        expect.append("ring %d" % n)
        expect.extend(model(order, ops))
        lines.append('    IO.print("model %d" ++ m.run([%s], {(M.model.new(%dn), "") : M.RingModel & String}))' % (n, ", ".join(bend_op(o) for o in ops), order))
        expect.append("model %d" % n)
        expect.extend(model(order, ops))
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write(r'''import Base
import ../ringbuf.bend as R
import ../model.bend as M

type Op is Data:
  OPush{x: U32}
  OPop{}
  OPeek{}
  OPushList{xs: List<&2, U32>}
  OPopList{n: Nat}

def show_list(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, Nil{}}:
      U32.show(x)
    case Con{x, t}:
      U32.show(x) ++ "," ++ show_list(t)

def push_line(p: R.RingBuf & Result<&2, &2, R.RingError, Unit>) -> R.RingBuf & String:
  (r, res) = p
  match res:
    case Done{u}:
      (r, "push ok")
    case Fail{e}:
      (r, "push full")

def take_line(name: String, p: R.RingBuf & Result<&2, &2, R.RingError, U32>) -> R.RingBuf & String:
  (r, res) = p
  match res:
    case Done{x}:
      (r, name ++ " " ++ U32.show(x))
    case Fail{e}:
      (r, name ++ " empty")

def in_line(p: R.RingBuf & Nat) -> R.RingBuf & String:
  (r, n) = p
  (r, "in " ++ Nat.show(n))

def out_line(p: R.RingBuf & List<&2, U32>) -> R.RingBuf & String:
  (r, xs) = p
  (r, "out " ++ show_list(xs))

def step(op: Op, r: R.RingBuf) -> R.RingBuf & String:
  match op:
    case OPush{x}:
      push_line(R.ring.push(r, x))
    case OPop{}:
      take_line("pop", R.ring.pop(r))
    case OPeek{}:
      take_line("peek", R.ring.peek(r))
    case OPushList{xs}:
      in_line(R.ring.push_list(r, xs))
    case OPopList{n}:
      out_line(R.ring.pop_list(r, n))

def counts.avail(out: String, p: R.RingBuf & Nat) -> R.RingBuf & String:
  (r, n) = p
  (r, out ++ " avail " ++ Nat.show(n))

def counts(out: String, p: R.RingBuf & Nat) -> R.RingBuf & String:
  (r, n) = p
  counts.avail(out ++ "len " ++ Nat.show(n), R.ring.avail(r))

def run.add(out: String, q: R.RingBuf & String) -> R.RingBuf & String:
  (r, line) = q
  counts(out ++ "\n" ++ line ++ "\n", R.ring.len(r))

def run.step(op: Op, p: R.RingBuf & String) -> R.RingBuf & String:
  (r, out) = p
  run.add(out, step(op, r))

def run.fin(p: R.RingBuf & String) -> String:
  (r, out) = p
  out

def run(ops: List<&2, Op>, p: R.RingBuf & String) -> String:
  match ops:
    case Nil{}:
      run.fin(p)
    case Con{op, t}:
      run(t, run.step(op, p))

def m.push_line(p: M.RingModel & Result<&2, &2, R.RingError, Unit>) -> M.RingModel & String:
  (r, res) = p
  match res:
    case Done{u}:
      (r, "push ok")
    case Fail{e}:
      (r, "push full")

def m.take_line(name: String, p: M.RingModel & Result<&2, &2, R.RingError, U32>) -> M.RingModel & String:
  (r, res) = p
  match res:
    case Done{x}:
      (r, name ++ " " ++ U32.show(x))
    case Fail{e}:
      (r, name ++ " empty")

def m.in_line(p: M.RingModel & Nat) -> M.RingModel & String:
  (r, n) = p
  (r, "in " ++ Nat.show(n))

def m.out_line(p: M.RingModel & List<&2, U32>) -> M.RingModel & String:
  (r, xs) = p
  (r, "out " ++ show_list(xs))

def m.step(op: Op, r: M.RingModel) -> M.RingModel & String:
  match op:
    case OPush{x}:
      m.push_line(M.model.push(r, x))
    case OPop{}:
      m.take_line("pop", M.model.pop(r))
    case OPeek{}:
      m.take_line("peek", M.model.peek(r))
    case OPushList{xs}:
      m.in_line(M.model.push_list(r, xs))
    case OPopList{n}:
      m.out_line(M.model.pop_list(r, n))

def m.add(out: String, q: M.RingModel & String) -> M.RingModel & String:
  (+r, line) = q
  (r, out ++ "
" ++ line ++ "
len " ++ Nat.show(M.model.len(r)) ++ " avail " ++ Nat.show(M.model.avail(r)))

def m.run.step(op: Op, p: M.RingModel & String) -> M.RingModel & String:
  (r, out) = p
  m.add(out, m.step(op, r))

def m.run.fin(p: M.RingModel & String) -> String:
  (r, out) = p
  out

def m.run(ops: List<&2, Op>, p: M.RingModel & String) -> String:
  match ops:
    case Nil{}:
      m.run.fin(p)
    case Con{op, t}:
      m.run(t, m.run.step(op, p))

''')
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(total, "operations in 24 sequences, on the Array ring and on the model")

main()
