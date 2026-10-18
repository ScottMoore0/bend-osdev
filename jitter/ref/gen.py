#!/usr/bin/env python3
"""Differential test cases for bend-osdev-jitter.

Writes ref/cases.bend (a Bend program that reads bytes from delta lists
through the package, with SHA3-256 as the conditioner) and
ref/expected.txt (the same from model.py, written from Müller's paper and
SP 800-90B, with hashlib's SHA3-256).

Sources: the deltas recorded in recorded.txt (record.py: SHA3-256 hash
loops timed with a monotonic clock), read whole and in two reads that
carry the state across; pseudo-random deltas of several spreads; several
parameter sets (osr 1, 2, 3, 5; no block or two blocks discarded; the
memory and the common domain separators); and failing sources: a constant
delta, zero deltas, a run of one value in the middle of good deltas (the
RCT), one value too common in a window without long runs (the APT), and
too few deltas.
"""
import os, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import model  # noqa: E402

CHUNK = 400


def params_bend(p):
    return "J.JitParams{%dn, %dn, %dn, %dn, %dn, %d, %dn}" % (
        p["osr"], p["safety"], p["rct_cutoff"], p["apt_window"], p["apt_cutoff"], p["domain"], p["prime"])


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    rng = random.Random(seed)
    recorded = [int(l) for l in open(os.path.join(HERE, "recorded.txt"))]
    cases = []  # (name, params, deltas, reads: list of n)

    def spread(n, lo, hi):
        return [rng.randrange(lo, hi) for _ in range(n)]

    P3 = model.params(3)
    cases.append(("recorded 64", P3, recorded, [64]))
    cases.append(("recorded 20 then 30", P3, recorded, [20, 30]))
    cases.append(("random 900-1100", P3, spread(2100, 900, 1100), [32]))
    cases.append(("random 0-50 (zeros among them)", P3, spread(2400, 0, 50), [16]))
    cases.append(("random 64-bit", P3, [rng.randrange(0, 1 << 64) for _ in range(3000)], [40]))
    for osr in (1, 2, 5):
        p = model.params(osr)
        cases.append(("osr %d" % osr, p, spread(800 * osr + 400, 200, 400), [8]))
    p0 = dict(P3, prime=0)
    cases.append(("no block discarded", p0, recorded[:1200], [32]))
    p2 = dict(P3, prime=2, domain=3)
    cases.append(("two discarded, domain 3", p2, recorded, [16]))
    p1 = dict(model.params(1), domain=1, safety=0)
    cases.append(("osr 1, no safety factor, domain 1", p1, spread(1400, 1000, 1100), [96]))
    # failures
    cases.append(("constant", P3, [1234] * 300, [32]))
    cases.append(("zeros", P3, [0] * 300, [32]))
    good = spread(2200, 500, 600)
    cases.append(("a run of 91 in good deltas", P3, good[:700] + [9999] * 91 + good[700:], [32]))
    cases.append(("a run of 90 in good deltas", P3, good[:700] + [9999] * 90 + good[700:], [32]))
    apt = []
    for i in range(1100):  # every other delta 777, the rest varied: no runs, a common value
        apt.append(777 if i % 2 == 0 else rng.randrange(1000, 2000))
    pa = dict(P3, apt_cutoff=200)
    cases.append(("one value half the time, APT cutoff 200", pa, apt, [32]))
    cases.append(("one value half the time, default APT", P3, apt + spread(1500, 1000, 2000), [32]))
    cases.append(("too few deltas", P3, spread(500, 100, 200), [32]))
    cases.append(("zero bytes", P3, [], [0]))

    defs, lines, expect = [], [], []
    for ci, (name, p, ds, reads) in enumerate(cases):
        chunks = [ds[i:i + CHUNK] for i in range(0, len(ds), CHUNK)]
        for k, ch in enumerate(chunks):
            defs.append("def c%d.d%d() -> List<&2, W.W64>:\n  [%s]\n" % (
                ci, k, ", ".join("W.W64.from_parts(%d, %d)" % (d >> 32, d & 0xFFFFFFFF) for d in ch)))
        body = "Nil{}"
        for k in reversed(range(len(chunks))):
            body = "List.append(&2, W.W64, c%d.d%d(), %s)" % (ci, k, body)
        defs.append("def c%d.ds() -> List<&2, W.W64>:\n  %s\n" % (ci, body))
        # the model
        j = model.Jitter(p)
        rest = list(ds)
        outs = []
        for n in reads:
            status, out, used = j.read(rest, n)
            rest = rest[used:]
            outs.append("ok %s left %d" % (out.hex(), len(rest)) if status == "ok" else
                        ("need more %d" % len(out) if status == "need more" else status))
            if status != "ok":
                break
        expect.append("%s: %s" % (name, " / ".join(outs)))
        # the package: reads chained through the state and the rest
        defs.append("def c%d.p() -> J.JitParams:\n  %s\n" % (ci, params_bend(p)))
        defs.append("def c%d.run() -> String:\n  +p = c%d.p()\n  chain([%s], p, JS.JitSha3.read(p, JS.JitSha3.init(p), c%d.ds(), %dn))\n" % (
            ci, ci, ", ".join("%dn" % n for n in reads[1:]), ci, reads[0]))
        lines.append('    IO.print("%s: " ++ c%d.run())' % (name, ci))

    header = """import Base
import ../../bytes/bytes.bend as B
import ../../word64/word64.bend as W
import ../../crypto/inst_sha3.bend as S3
import ../jitter.bend as J
import ../sha3.bend as JS

def why(e: J.JitError) -> String:
  match e:
    case J.JitRctFailure{}:
      "rct"
    case J.JitAptFailure{}:
      "apt"
    case J.JitNotEnough{h, n}:
      "not enough"
    case J.JitNeedMore{h}:
      "need more " ++ Nat.show(h)

def show(+p: J.JitParams, r: Result<&2, &2, J.JitError, J.JitOut<S3.CrSha3State>>) -> String:
  match r:
    case Fail{e}:
      why(e)
    case Done{o}:
      match o:
        case J.JitOut{out, st, rest}:
          "ok " ++ B.Octets.hex(out) ++ " left " ++ Nat.show(List.length(&2, W.W64, rest))

# the reads after the first, each from the state and deltas the one before
# left; r is the read before
def chain(ns: List<&2, Nat>, +p: J.JitParams, r: Result<&2, &2, J.JitError, J.JitOut<S3.CrSha3State>>) -> String:
  match ns:
    case Nil{}:
      show(p, r)
    case Con{n, more}:
      match r:
        case Fail{e}:
          why(e)
        case Done{o}:
          match o:
            case J.JitOut{out, st, rest}:
              +rest2 = rest
              "ok " ++ B.Octets.hex(out) ++ " left " ++ Nat.show(List.length(&2, W.W64, rest2)) ++ " / " ++ chain(more, p, JS.JitSha3.read(p, st, rest2, n))

"""
    with open(os.path.join(HERE, "cases.bend"), "w", newline="\n") as f:
        f.write(header + "\n".join(defs) + "\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(HERE, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print("%d cases, %d deltas" % (len(cases), sum(len(c[2]) for c in cases)))


if __name__ == "__main__":
    main()
