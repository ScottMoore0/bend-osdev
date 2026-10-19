#!/usr/bin/env python3
"""Differential test cases for bend-osdev-genalloc.

There is no general-purpose pool allocator outside this repository to run
(the kernel's genalloc lives inside the kernel), so the reference is a model
written here from the behaviour the README states: chunks of granule bits,
allocation by each fit algorithm, frees by address.

Writes ref/cases.bend (random sequences of add, alloc and free on pools of
several granule orders, with every fit algorithm) and ref/expected.txt.
"""
import os, random, sys

def model(order, ops):
    g = 1 << order
    chunks = []  # [addr, bits]
    out = []
    def runs(bits):
        rs, i = [], 0
        while i < len(bits):
            if bits[i]:
                i += 1
                continue
            j = i
            while j < len(bits) and not bits[j]:
                j += 1
            rs.append((i, j - i))
            i = j
        return rs
    def run_free(bits, s, n):
        return s + n <= len(bits) and not any(bits[s:s + n])
    def lowest(bits, n, off, a):
        a = max(a, 1)
        for s in range(len(bits) + 1):
            if (off + s * g) % a == 0 and run_free(bits, s, n):
                return s
        return None
    def pow2(n):
        p = 1
        while p < n:
            p *= 2
        return p
    def fit(algo, data, bits, n, base):
        if algo == 0:
            return lowest(bits, n, 0, 1)
        if algo == 1:
            best = None
            for (s, l) in runs(bits):
                if l >= n and (best is None or l < best[1]):
                    best = (s, l)
            return None if best is None else best[0]
        if algo == 2:
            return lowest(bits, n, base, data)
        if algo == 3:
            return lowest(bits, n, 0, pow2(n) * g)
        if algo == 4:
            if data % g != 0:
                return None
            s = data // g
            return s if run_free(bits, s, n) else None
    for op in ops:
        if op[0] == "add":
            _, addr, size = op
            n = size // g
            if n == 0:
                out.append("add GpBadSize")
                continue
            end = addr + n * g
            if any(not (end <= b or b + len(u) * g <= addr) for (b, u) in chunks):
                out.append("add GpOverlap")
                continue
            chunks.append([addr, [False] * n])
            out.append("add ok")
        elif op[0] == "alloc":
            _, algo, size, data = op
            if size == 0:
                out.append("alloc GpBadSize")
                continue
            n = max((size + g - 1) // g, 1)
            res = None
            for c, (b, u) in enumerate(chunks):
                s = fit(algo, data, u, n, b)
                if s is not None:
                    res = (c, s)
                    break
            if res is None:
                out.append("alloc GpNoSpace")
                continue
            c, s = res
            b, u = chunks[c]
            for k in range(s, s + n):
                u[k] = True
            out.append("alloc %d %d %d %d" % (b + s * g, c, s, n))
        else:
            _, addr, size = op
            if size == 0:
                out.append("free GpBadSize")
                continue
            n = max((size + g - 1) // g, 1)
            hit = None
            for c, (b, u) in enumerate(chunks):
                if b <= addr < b + len(u) * g:
                    hit = c
                    break
            if hit is None:
                out.append("free GpNotInPool")
                continue
            b, u = chunks[hit]
            if (addr - b) % g != 0:
                out.append("free GpMisaligned")
                continue
            s = (addr - b) // g
            if s + n > len(u) or not all(u[s:s + n]):
                out.append("free GpNotInUse")
                continue
            for k in range(s, s + n):
                u[k] = False
            out.append("free ok")
    free = sum(u.count(False) for (b, u) in chunks) * g
    used = sum(u.count(True) for (b, u) in chunks) * g
    out.append("sizes %d %d %d" % (free, used, sum(len(u) for (b, u) in chunks) * g))
    return out

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    defs, calls, expect = [], [], []
    total = 0
    for k in range(40):
        order = rng.choice([0, 2, 4, 6])
        g = 1 << order
        ops, live = [], []
        base = rng.randrange(1000) * 4
        for _ in range(rng.randrange(1, 4)):
            ops.append(("add", base, rng.randrange(0, 40) * g + rng.randrange(g)))
            base += rng.randrange(30, 60) * g
        for _ in range(rng.randrange(10, 40)):
            r = rng.random()
            if r < 0.06:
                ops.append(("add", rng.randrange(base + 100), rng.randrange(200)))
            elif r < 0.6:
                algo = rng.randrange(5)
                size = rng.choice([0, 1, g, rng.randrange(1, 12 * g)])
                data = rng.choice([1, 2, 4, 8, 64, 3]) * g if algo == 2 else (rng.randrange(20) * g + (rng.randrange(g) if rng.random() < 0.2 else 0) if algo == 4 else 0)
                ops.append(("alloc", algo, size, data))
            else:
                ops.append(("free", rng.randrange(base + 50), rng.randrange(1, 4 * g)))
        # free some real allocations too: replay the model to find them
        out = model(order, ops)
        allocs = [(int(l.split()[1]), op[2]) for l, op in zip(out, ops) if l.startswith("alloc ") and l.split()[1].isdigit()]
        for (a, sz) in rng.sample(allocs, min(len(allocs), 4)):
            ops.append(("free", a, sz))
        ops.append(("alloc", 0, g, 0))
        out = model(order, ops)
        def bop(op):
            if op[0] == "add":
                return "OAdd{%dn, %dn}" % op[1:]
            if op[0] == "alloc":
                return "OAlloc{%dn, %dn, %dn}" % op[1:]
            return "OFree{%dn, %dn}" % op[1:]
        defs.append("def c%d() -> String:\n  run([%s], G.genpool.new(%dn), \"\")\n" % (k, ", ".join(bop(o) for o in ops), order))
        calls.append("c%d()" % k)
        expect.append("\\n".join(out))
        total += len(ops)
    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write('''import Base
import ../genalloc.bend as G
import ../fit.bend as F

type Op is Data:
  OAdd{addr: Nat, size: Nat}
  OAlloc{algo: Nat, size: Nat, data: Nat}
  OFree{addr: Nat, size: Nat}

def err(e: G.GpError) -> String:
  match e:
    case G.GpBadSize{}:
      "GpBadSize"
    case G.GpNoSpace{}:
      "GpNoSpace"
    case G.GpBadFit{c}:
      "GpBadFit"
    case G.GpOverlap{}:
      "GpOverlap"
    case G.GpNotInPool{}:
      "GpNotInPool"
    case G.GpMisaligned{}:
      "GpMisaligned"
    case G.GpNotInUse{}:
      "GpNotInUse"

def pool_line(w: String, r: Result<&2, &2, G.GpError, G.GpPool>) -> String:
  match r:
    case Done{q}:
      w ++ " ok"
    case Fail{e}:
      w ++ " " ++ err(e)

def alloc_line(r: Result<&2, &2, G.GpError, G.GpAlloc>) -> String:
  match r:
    case Done{G.GpAlloc{q, a, c, s, n}}:
      "alloc " ++ Nat.show(a) ++ " " ++ Nat.show(c) ++ " " ++ Nat.show(s) ++ " " ++ Nat.show(n)
    case Fail{e}:
      "alloc " ++ err(e)

def alloc_with(algo: Nat, +p: G.GpPool, +size: Nat, +d: Nat) -> Result<&2, &2, G.GpError, G.GpAlloc>:
  match algo:
    case 0n:
      G.genpool.alloc(~F.genpool.first_fit, p, size, G.GpNoData{})
    case 1n+a1:
      match a1:
        case 0n:
          G.genpool.alloc(~F.genpool.best_fit, p, size, G.GpNoData{})
        case 1n+a2:
          match a2:
            case 0n:
              G.genpool.alloc(~F.genpool.first_fit_align, p, size, G.GpAlign{d})
            case 1n+a3:
              match a3:
                case 0n:
                  G.genpool.alloc(~F.genpool.first_fit_order_align, p, size, G.GpNoData{})
                case 1n+a4:
                  G.genpool.alloc(~F.genpool.fixed_offset, p, size, G.GpOffset{d})

def sizes(+p: G.GpPool) -> String:
  "sizes " ++ Nat.show(G.genpool.avail(p)) ++ " " ++ Nat.show(G.genpool.allocated(p)) ++ " " ++ Nat.show(G.genpool.size(p))

def run(ops: List<&2, Op>, +p: G.GpPool, out: String) -> String:
  match ops:
    case Nil{}:
      out ++ sizes(p)
    case Con{OAdd{+a, +s}, t}:
      +r = G.genpool.add(p, a, s)
      run(t, G.genpool.pool(r, p), out ++ pool_line("add", r) ++ "\\n")
    case Con{OAlloc{+algo, +s, +d}, t}:
      +r = alloc_with(algo, p, s, d)
      run(t, G.genpool.state(r, p), out ++ alloc_line(r) ++ "\\n")
    case Con{OFree{+a, +s}, t}:
      +r = G.genpool.free(p, a, s)
      run(t, G.genpool.pool(r, p), out ++ pool_line("free", r) ++ "\\n")

''')
        f.write("\n".join(defs) + "\n")
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join("    IO.print(%s)" % c for c in calls) + "\n")
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(e.replace("\\n", "\n") for e in expect) + "\n")
    print(total, "operations in", len(defs), "sequences")

main()
