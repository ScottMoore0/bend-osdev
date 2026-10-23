#!/usr/bin/env python3
"""Differential test cases for bend-osdev-jitter's XDRBG conditioner.

Writes ref/cases_xdrbg.bend (a Bend program that runs the package's
SHAKE256 and reads bytes from delta lists with XDRBG-256 as the
conditioner) and ref/expected_xdrbg.txt (the same from hashlib's
SHAKE256 and model_xdrbg.py, written from Müller's paper and the XDRBG
paper).

SHAKE256: messages of lengths around the 136-byte rate, fed whole and in
pieces, read at offsets and lengths that cross squeezed blocks.

XDRBG: the deltas recorded in recorded.txt (record.py), read whole and in
two reads that carry the state across; pseudo-random deltas; several
parameter sets (osr 1, 2, 5; no block or two blocks discarded; the common
domain separator); the XDRBG's own parameters (an additional input alpha,
and other sizes of V and of the output, through the generic
JitXdrbg.take); and failing sources (a constant delta, a run of 91 equal
deltas, one value too common for the APT, too few deltas).
"""
import hashlib, os, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
import model  # noqa: E402
import model_xdrbg  # noqa: E402

CHUNK = 400


def params_bend(p):
    return "J.JitParams{%dn, %dn, %dn, %dn, %dn, %d, %dn}" % (
        p["osr"], p["safety"], p["rct_cutoff"], p["apt_window"], p["apt_cutoff"], p["domain"], p["prime"])


def octets(bs):
    return "B.Octets.of_list([%s])" % ", ".join(str(b) for b in bs)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    rng = random.Random(seed)
    recorded = [int(l) for l in open(os.path.join(HERE, "recorded.txt"))]
    defs, lines, expect = [], [], []

    # SHAKE256 against hashlib
    reads = [(0, 32), (0, 200), (100, 72), (130, 20), (136, 8), (270, 300), (0, 0), (5, 1)]
    for ci, ml in enumerate([0, 1, 3, 135, 136, 137, 271, 272, 300]):
        m = bytes(rng.randrange(256) for _ in range(ml))
        cuts = sorted(rng.randrange(ml + 1) for _ in range(2))
        pieces = [m[:cuts[0]], m[cuts[0]:cuts[1]], m[cuts[1]:]]
        st = "S.JitShake.init()"
        for pc in pieces:
            st = "S.JitShake.update(%s, %s)" % (st, octets(pc))
        defs.append("def s%d.st() -> S.JitShakeState:\n  %s\n" % (ci, st))
        for i, n in reads:
            want = hashlib.shake_256(m).digest(i + n)[i:]
            lines.append('    IO.print("shake %d bytes in %s, %d at %d: " ++ B.Octets.hex(S.JitShake.read(s%d.st(), %dn, %dn)))' % (
                ml, "+".join(str(len(pc)) for pc in pieces), n, i, ci, i, n))
            expect.append("shake %d bytes in %s, %d at %d: %s" % (
                ml, "+".join(str(len(pc)) for pc in pieces), n, i, want.hex()))

    # XDRBG against the model
    cases = []  # (name, params, deltas, reads, xdrbg parameters: (alpha, vsize, outsize) or None)

    def spread(n, lo, hi):
        return [rng.randrange(lo, hi) for _ in range(n)]

    P3 = model.params(3)
    cases.append(("recorded 64", P3, recorded, [64], None))
    cases.append(("recorded 20 then 30", P3, recorded, [20, 30], None))
    cases.append(("random 900-1100", P3, spread(2100, 900, 1100), [32], None))
    cases.append(("random 64-bit", P3, [rng.randrange(0, 1 << 64) for _ in range(3000)], [40], None))
    for osr in (1, 2, 5):
        cases.append(("osr %d" % osr, model.params(osr), spread(800 * osr + 400, 200, 400), [8], None))
    cases.append(("no block discarded", dict(P3, prime=0), recorded[:1200], [32], None))
    cases.append(("two discarded, domain 3", dict(P3, prime=2, domain=3), recorded, [16], None))
    alpha = bytes(rng.randrange(256) for _ in range(16))
    cases.append(("alpha of 16 bytes", P3, spread(2100, 900, 1100), [48], (alpha, 64, 32)))
    cases.append(("alpha of 84 bytes, no block discarded", dict(P3, prime=0), spread(1000, 900, 1100), [32],
                  (bytes(rng.randrange(256) for _ in range(84)), 64, 32)))
    cases.append(("V of 32 bytes, blocks of 64", dict(P3, prime=0), spread(2000, 900, 1100), [100], (b"", 32, 64)))
    cases.append(("V of 200 bytes, blocks of 150", dict(P3, prime=0), spread(1000, 900, 1100), [150], (b"", 200, 150)))
    cases.append(("constant", P3, [1234] * 300, [32], None))
    good = spread(2200, 500, 600)
    cases.append(("a run of 91 in good deltas", P3, good[:700] + [9999] * 91 + good[700:], [32], None))
    apt = [777 if i % 2 == 0 else rng.randrange(1000, 2000) for i in range(1100)]
    cases.append(("one value half the time, APT cutoff 200", dict(P3, apt_cutoff=200), apt, [32], None))
    cases.append(("too few deltas", P3, spread(500, 100, 200), [32], None))
    cases.append(("zero bytes", P3, [], [0], None))

    for ci, (name, p, ds, nreads, xp) in enumerate(cases):
        chunks = [ds[i:i + CHUNK] for i in range(0, len(ds), CHUNK)]
        for k, ch in enumerate(chunks):
            defs.append("def c%d.d%d() -> List<&2, W.W64>:\n  [%s]\n" % (
                ci, k, ", ".join("W.W64.from_parts(%d, %d)" % (d >> 32, d & 0xFFFFFFFF) for d in ch)))
        body = "Nil{}"
        for k in reversed(range(len(chunks))):
            body = "List.append(&2, W.W64, c%d.d%d(), %s)" % (ci, k, body)
        defs.append("def c%d.ds() -> List<&2, W.W64>:\n  %s\n" % (ci, body))
        # the model
        if xp is None:
            j = model_xdrbg.Jitter(p)
        else:
            j = model_xdrbg.Jitter(p, alpha=xp[0], vsize=xp[1], outsize=xp[2])
        rest = list(ds)
        outs = []
        for n in nreads:
            status, out, used = j.read(rest, n)
            rest = rest[used:]
            outs.append("ok %s left %d" % (out.hex(), len(rest)) if status == "ok" else
                        ("need more %d" % len(out) if status == "need more" else status))
            if status != "ok":
                break
        expect.append("%s: %s" % (name, " / ".join(outs)))
        # the package
        defs.append("def c%d.p() -> J.JitParams:\n  %s\n" % (ci, params_bend(p)))
        if xp is None:
            first = "JX.JitXdrbg256.read(p, JX.JitXdrbg256.init(p), c%d.ds(), %dn)" % (ci, nreads[0])
        else:
            defs.append("def c%d.xp() -> X.JitXdrbgParams:\n  X.JitXdrbgParams{%dn, %dn, %s}\n" % (ci, xp[1], xp[2], octets(xp[0])))
            defs.append("def c%d.take(pool: X.JitXdrbgPool<S.JitShakeState>) -> J.JitTaken<X.JitXdrbgPool<S.JitShakeState>>:\n"
                        "  X.JitXdrbg.take(~S.JitShakeState, ~S.JitShake.init(), ~S.JitShake.update, ~S.JitShake.read, ~c%d.xp(), pool)\n" % (ci, ci))
            first = ("J.JitCore.read(~X.JitXdrbgPool<S.JitShakeState>, ~136n, ~JX.JitXdrbg256.update, ~S3.CrSha3.sha3_256, ~c%d.take, "
                     "p, JX.JitXdrbg256.init(p), c%d.ds(), %dn)" % (ci, ci, nreads[0]))
        defs.append("def c%d.run() -> String:\n  +p = c%d.p()\n  chain([%s], p, %s)\n" % (
            ci, ci, ", ".join("%dn" % n for n in nreads[1:]), first))
        lines.append('    IO.print("%s: " ++ c%d.run())' % (name, ci))

    header = """import Base
import ../../bytes/bytes.bend as B
import ../../word64/word64.bend as W
import ../../crypto/inst_sha3.bend as S3
import ../jitter.bend as J
import ../shake.bend as S
import ../xdrbg.bend as X
import ../xdrbg256.bend as JX

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

def show(+p: J.JitParams, r: Result<&2, &2, J.JitError, J.JitOut<X.JitXdrbgPool<S.JitShakeState>>>) -> String:
  match r:
    case Fail{e}:
      why(e)
    case Done{o}:
      match o:
        case J.JitOut{out, st, rest}:
          "ok " ++ B.Octets.hex(out) ++ " left " ++ Nat.show(List.length(&2, W.W64, rest))

# the reads after the first (with XDRBG-256), each from the state and
# deltas the one before left; r is the read before
def chain(ns: List<&2, Nat>, +p: J.JitParams, r: Result<&2, &2, J.JitError, J.JitOut<X.JitXdrbgPool<S.JitShakeState>>>) -> String:
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
              "ok " ++ B.Octets.hex(out) ++ " left " ++ Nat.show(List.length(&2, W.W64, rest2)) ++ " / " ++ chain(more, p, JX.JitXdrbg256.read(p, st, rest2, n))

"""
    with open(os.path.join(HERE, "cases_xdrbg.bend"), "w", newline="\n") as f:
        f.write(header + "\n".join(defs) + "\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(HERE, "expected_xdrbg.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print("%d SHAKE256 reads, %d XDRBG cases, %d deltas" % (
        len(reads) * 9, len(cases), sum(len(c[2]) for c in cases)))


if __name__ == "__main__":
    main()
