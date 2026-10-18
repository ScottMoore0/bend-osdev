#!/usr/bin/env python3
"""Differential test cases for bend-osdev-c842.

Writes, in ref/:
  * cases.bin, the records runner.bend runs (see its header);
  * expected.txt, the answers it must print.

The cases come from two sources:

1. The recorded Linux vectors (linux-vectors.txt, written by running Linux's
   842 as a black box: see OBSERVATIONS.md and ../README.md). In both
   directions:
   * every stream Linux compressed must decode, in the package, to its input;
   * for every input, the package's encoder (default strategy, and 4-bit
     tables) and its literal stream must write exactly the streams Linux was
     given, so that Linux's answer (it decoded each to the input) holds for
     the package as it is;
   * every fuzzed stream must get from the package the answer Linux gave:
     the same bytes, or a failure Linux reports with the same errno
     (EOVERFLOW: C842Truncated; ENOSPC: C842OutputTooLarge; EINVAL: the
     others, and the model, below, names which).

2. model.py, an independent model written from the same documents, which
   shares an author with the package. Random inputs (random, text, runs,
   zeros, repeated chunks) are compressed by the package (checked and
   unchecked, several strategies) and must give the model's bytes; fuzzed
   streams (valid and malformed) and the package's own streams are decoded
   and must give the model's answer; streams are decoded in pieces through
   the reader; and the format's token parser must agree with the decoder on
   where a stream fails.

    gen.py [SEED]     write the cases; print how many
"""
import hashlib, os, random, struct, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import model

NAMES = {"truncated": "Truncated", "too_large": "OutputTooLarge", "bad_template": "BadTemplate",
         "bad_pointer": "BadPointer", "bad_repeat": "BadRepeat", "bad_short": "BadShort", "bad_crc": "BadCrc"}
ERRNO_OF = {"Truncated": -75, "OutputTooLarge": -28}


def answer(r):
    return "=" + r[1].hex() if r[0] == "ok" else "!" + NAMES[r[1]]


def strategy_arg(s):
    if s[0] == "none":
        return 0
    return (s[1] << 16) | (s[2] << 8) | s[3]


class Cases:
    def __init__(self):
        self.recs = []
        self.want = []

    def add(self, op, arg, data, want):
        self.recs.append(op.encode() + struct.pack(">II", arg, len(data)) + bytes(data))
        self.want.append(want)


def unhex(x):
    return b"" if x == "-" else bytes.fromhex(x)


def linux(cases):
    """Cases from linux-vectors.txt; also checks the model against it."""
    C, D = [], []
    for line in open(os.path.join(HERE, "linux-vectors.txt")):
        if line.startswith("#"):
            continue
        f = line.split()
        if f[0] == "C":
            C.append((unhex(f[1]), int(f[2]), unhex(f[3])))
        else:
            D.append((int(f[1]), unhex(f[2]), int(f[3]), f[4]))
    n = 0
    # Linux's streams decode to their inputs
    for x, ret, out in C:
        if ret == 0:
            assert model.decode(out) == ("ok", x)
            cases.add("d", 1 << 30, out, "=" + x.hex())
            n += 1
        else:
            assert x == b"" and ret == -22  # the crypto API refuses empty input
    # the package's streams, as Linux was given them: per input, the default
    # encoder, the 4-bit-table encoder and the literal stream (the empty
    # input: the default encoder only)
    k = 0
    for x, ret, out in C:
        group = [("u", model.DEFAULT), ("u", ("hash", 4, 4, 4)), ("l", None)] if x else [("u", model.DEFAULT)]
        for op, s in group:
            cap, stream, dret, dout = D[k]
            k += 1
            assert dret == 0 and dout == "len=%d,sha256=%s" % (len(x), hashlib.sha256(x).hexdigest()), dout
            assert stream == (model.encode(x, s) if op == "u" else model.literals(x))
            cases.add(op, strategy_arg(s) if s else 0, x, "=" + stream.hex())
            n += 1
    # fuzzed streams: Linux's answer
    for cap, s, ret, out in D[k:]:
        m = model.decode(s, cap)
        if ret == 0:
            assert m == ("ok", unhex(out)), (s.hex(), m)
        else:
            assert m[0] == "err" and ERRNO_OF.get(NAMES[m[1]], -22) == ret, (s.hex(), m, ret)
        cases.add("d", cap, s, answer(m))
        n += 1
    return n


# Inputs

WORDS = [b"the ", b"842 ", b"phrase ", b"chunk ", b"zero ", b"index ", b"ring ", b"fifo ", b"\x00" * 8]


def data(rng, n):
    kind = rng.randrange(7)
    if kind == 0:
        return bytes(rng.randrange(256) for _ in range(n))
    if kind == 1:
        return bytes(rng.choice(b"ab\x00") for _ in range(n))
    if kind == 2:
        return b"".join(rng.choice(WORDS) for _ in range(n // 3 + 1))[:n]
    if kind == 3:
        blocks = [bytes(rng.randrange(256) for _ in range(8)) for _ in range(rng.randrange(1, 8))] + [bytes(8)]
        return b"".join(rng.choice(blocks) * rng.randrange(1, 80) for _ in range(n // 8 + 1))[:n]
    if kind == 4:
        return bytes(n)
    if kind == 5:
        x = bytearray(rng.randrange(256) for _ in range(n))
        for _ in range(n // 8):
            a, b, l = rng.randrange(max(n, 1)), rng.randrange(max(n, 1)), rng.choice([2, 4, 8, 16])
            x[b:b + l] = x[a:a + l]
        return bytes(x[:n])
    # far repeats: phrases from more than 2 KB back
    x = bytearray(rng.randrange(256) for _ in range(n))
    for _ in range(n // 32):
        a = rng.randrange(max(n, 1))
        b = min(n, a + rng.choice([2040, 2048, 2056, 2100, 4000, 504, 512, 520]))
        l = rng.choice([2, 4, 8])
        x[b:b + l] = x[a:a + l]
    return bytes(x[:n])


STRATS = [model.DEFAULT, ("none",), ("hash", 4, 4, 4), ("hash", 1, 1, 1), ("hash", 12, 13, 16), ("hash", 16, 16, 16)]

# fuzzed streams (as bend-audit/kmod842/fuzz.py, which made Linux's): literal
# chunks, then random templates (pointers mostly valid), RPT, Z8, short data
# (sometimes count 0), codes 26 and 31; END with the right CRC mostly; then
# sometimes cut, a bit flipped or bytes added


def partial(s):
    """The model's output up to the end (ignoring the CRC), or None."""
    w = model.Writer()
    r = model.decode(s, 1 << 30)
    if r[0] == "ok":
        return r[1]
    if r[1] != "bad_crc":
        return None
    # decode again, with the CRC of what came out (the model checks it last)
    out = []
    orig = model.crc

    def grab(d):
        out.append(bytes(d))
        return orig(d)
    model.crc = grab
    try:
        model.decode(s, 1 << 30)
    finally:
        model.crc = orig
    return out[0] if out else None


def fuzz(rng):
    w = model.Writer()
    n = 0
    for _ in range(rng.randrange(0, 12)):
        w.put(0, 5)
        w.put(rng.randrange(1 << 64), 64)
        n += 8
    for _ in range(rng.randrange(1, 40)):
        r = rng.random()
        if r < 0.55:
            t = rng.randrange(26)
            w.put(t, 5)
            here = n
            for f in model.TEMPLATES[t]:
                if f == "LL":
                    w.put(rng.randrange(65536), 16)
                    here += 2
                else:
                    size, width, hist = model.PTR[f]
                    idx = rng.randrange(1 << width)
                    if rng.random() < 0.97:
                        for _ in range(20):
                            if model.pointer_pos(here, idx, f) is not None:
                                break
                            idx = rng.randrange(1 << width)
                    w.put(idx, width)
                    here += size
        elif r < 0.65:
            w.put(27, 5)
            w.put(rng.randrange(64), 6)
        elif r < 0.72:
            w.put(28, 5)
        elif r < 0.80:
            c = rng.randrange(8) if rng.random() < 0.95 else 0
            w.put(29, 5)
            w.put(c, 3)
            for _ in range(c):
                w.put(rng.randrange(256), 8)
        elif r < 0.81:
            w.put(rng.choice([26, 31]), 5)
            w.put(rng.randrange(1 << 20), 20)
        else:
            w.put(0, 5)
            w.put(rng.randrange(1 << 64), 64)
        tmp = model.Writer()
        tmp.bits = list(w.bits)
        tmp.put(30, 5)
        tmp.put(0, 32)
        o = partial(tmp.pack())
        if o is None:
            break
        n = len(o)
    tmp = model.Writer()
    tmp.bits = list(w.bits)
    tmp.put(30, 5)
    tmp.put(0, 32)
    out = partial(tmp.pack())
    w.put(30, 5)
    w.put(model.crc(out) if (out is not None and rng.random() < 0.93) else rng.randrange(1 << 32), 32)
    s = w.pack()
    m = rng.random()
    if m < 0.05:
        s = s[:rng.randrange(len(s))]
    elif m < 0.10:
        b = bytearray(s)
        b[rng.randrange(len(b))] ^= 1 << rng.randrange(8)
        s = bytes(b)
    elif m < 0.13:
        s = s + bytes(rng.randrange(256) for _ in range(rng.randrange(1, 9)))
    return s


def ours(cases, rng):
    n = 0
    sizes = [0, 1, 7, 8, 9, 15, 16, 17, 63, 64, 65, 511, 512, 513, 520, 2047, 2048, 2049, 2056, 4096, 6000]
    sizes += [rng.randrange(0, 3000) for _ in range(40)] + [rng.randrange(3000, 12000) for _ in range(4)]
    for size in sizes:
        x = data(rng, size)
        s = rng.choice(STRATS)
        # the check never falls back to the literal stream on these inputs
        assert model.compress(x, s) == model.encode(x, s), (size, s)
        cases.add("c", strategy_arg(s), x, "=" + model.compress(x, s).hex())
        cases.add("u", strategy_arg(s), x, "=" + model.encode(x, s).hex())
        cases.add("l", 0, x, "=" + model.literals(x).hex())
        z = model.encode(x, s)
        cases.add("d", len(x), z, "=" + x.hex())
        n += 4
        if x:
            cases.add("d", len(x) - 1, z, answer(model.decode(z, len(x) - 1)))
            cases.add("p", rng.randrange(1, 40), z, "=" + x.hex())
            n += 2
    for _ in range(1500):
        s = fuzz(rng)
        cap = rng.choice([1 << 30, 1 << 30, 1 << 30, rng.randrange(0, 600)])
        r = model.decode(s, cap)
        cases.add("d", cap, s, answer(r))
        n += 1
        if rng.random() < 0.1:
            cases.add("p", rng.randrange(1, 9), s, answer(model.decode(s, 1 << 30)))
            n += 1
        if rng.random() < 0.1:
            # the token parser fails where the decoder fails on the format
            # (truncation, codes 26 and 31, short data count 0)
            rr = model.decode(s, 1 << 30)
            if rr[0] == "err" and rr[1] in ("truncated", "bad_template", "bad_short"):
                cases.add("t", 0, s, "!" + NAMES[rr[1]])
                n += 1
    return n


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    rng = random.Random(seed)
    cases = Cases()
    nl = linux(cases)
    no = ours(cases, rng)
    with open(os.path.join(HERE, "cases.bin"), "wb") as f:
        for r in cases.recs:
            f.write(r)
    with open(os.path.join(HERE, "expected.txt"), "w") as f:
        for k, w in enumerate(cases.want):
            f.write("%d %s\n" % (k, w))
    print("%d cases (%d from the Linux vectors, %d against the model)" % (nl + no, nl, no))


main()
