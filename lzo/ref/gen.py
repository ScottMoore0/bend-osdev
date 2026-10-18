#!/usr/bin/env python3
"""Differential test cases for bend-osdev-lzo.

No LZO implementation was installed when this was written (no lzop tool,
no Python lzo module), so this file holds an independent one, written here
from the same documents as the package and from nothing else (no LZO source
code was read):
  * Documentation/staging/lzo.rst from the Linux kernel ("LZO stream format
    as understood by Linux's LZO decompressor"), for the LZO1X stream;
  * the lzop file-format notes, for the .lzo container.
It has
  * a decoder, written as an instruction-at-a-time parser (the package's
    decoder is a byte-at-a-time state machine), which names each failure as
    the package does, at the same point of the stream;
  * an encoder that writes every encoding the documentation describes: the
    first-byte literal runs (18..255) and the long literal run (0000LLLL,
    with length bytes), M1 after 1 to 3 literals (2 bytes, distance up to
    1024), M1 after 4 literals or more (3 bytes, distance 2049 to 3072), M2,
    M3 and M4 (with and without length bytes), 0 to 3 literals in the S bits,
    choosing among the valid encodings at random;
  * an lzop reader and writer (Adler-32 and CRC-32 from Python's zlib).
It shares an author with the package, so it checks the package against a
second reading of the documents, not against the reference implementation.
When the lzop tool is installed, it is the reference in both directions.

Writes, in ref/:
  * casesNN.bend (Bend programs printing the package's answer for each case)
    and expected.txt (the answers expected): streams written here decoded by
    the package; the output limit; corruptions (the package must answer
    exactly what this decoder answers); streaming in pieces; lzop files
    written here, and corruptions of them; lzop files from the lzop tool;
  * ccasesNN.bend, which print the package's compressed streams and lzop
    files, and ccases.json, their inputs; `gen.py verify OUT` checks the
    package's output OUT: every stream and file must decode back to its
    input with this file's decoder, and with `lzop -d` when installed.
"""
import json, os, random, shutil, struct, subprocess, sys, tempfile, zlib

# The LZO1X stream: decoder (the bytes, or the name of the failure)

class Fail(Exception):
    pass

def decompress(src, maxout):
    out = bytearray()
    n = len(src)
    pos = [0]

    def byte():
        if pos[0] >= n:
            raise Fail("Truncated")
        b = src[pos[0]]
        pos[0] += 1
        return b

    def length(v, bits, extra):
        # the length field: v & mask, or (when 0) mask + 255 per zero byte + the last byte
        if v:
            return v + extra
        total = (1 << bits) - 1
        while True:
            b = byte()
            if b == 0:
                total += 255
            else:
                return total + b + extra

    def literals(k):
        for _ in range(k):
            b = byte()
            if len(out) >= maxout:
                raise Fail("OutputTooLarge")
            out.append(b)

    def copy(dist, ln):
        if dist > len(out):
            raise Fail("BadDistance")
        for _ in range(ln):
            if len(out) >= maxout:
                raise Fail("OutputTooLarge")
            out.append(out[-dist])

    try:
        state = 0          # literals copied by the last instruction: 0, 1-3, or 4 (4 or more)
        b = byte()
        if b >= 18:        # the first byte: b - 17 literals
            t = b - 17
            literals(t)
            state = t if t < 4 else 4
            b = byte()
        while True:
            if b < 16:
                if state == 0:            # a run of 4 literals or more
                    literals(length(b & 15, 4, 3))
                    state = 4
                    b = byte()
                    continue
                h = byte()
                if state == 4:            # M1 after 4 literals or more: 3 bytes, 2049..3072
                    dist, ln = (h << 2) + ((b >> 2) & 3) + 2049, 3
                else:                     # M1 after 1 to 3 literals: 2 bytes, up to 1024
                    dist, ln = (h << 2) + ((b >> 2) & 3) + 1, 2
                s = b & 3
            elif b < 32:                  # M4
                ln = length(b & 7, 3, 2)
                lo, hi = byte(), byte()
                d = (lo | hi << 8) >> 2
                dist = 16384 + ((b >> 3) & 1) * 16384 + d
                if dist == 16384:         # the end marker
                    if pos[0] != n:
                        raise Fail("Trailing")
                    return bytes(out)
                s = lo & 3
            elif b < 64:                  # M3
                ln = length(b & 31, 5, 2)
                lo, hi = byte(), byte()
                dist, s = ((lo | hi << 8) >> 2) + 1, lo & 3
            else:                         # M2
                h = byte()
                ln = 3 + ((b >> 5) & 1) if b < 128 else 5 + ((b >> 5) & 3)
                dist, s = (h << 3) + ((b >> 2) & 7) + 1, b & 3
            copy(dist, ln)
            literals(s)
            state = s
            b = byte()
    except Fail as e:
        return str(e)

assert decompress(bytes([17, 0, 0]), 0) == b""
assert decompress(bytes([20, 97, 98, 99, 168, 0, 17, 0, 0]), 9) == b"abcabcabc"

# The LZO1X stream: encoder

def len_field(v, bits, extra):
    """(field, length bytes) for a length v."""
    r = v - extra
    if 0 < r < (1 << bits):
        return r, b""
    r -= (1 << bits) - 1
    ext = bytearray()
    while r > 255:
        ext.append(0)
        r -= 255
    ext.append(r)
    return 0, bytes(ext)

def encodings(ln, dist, state):
    """The encodings for a match of ln bytes at dist, after literals of this state."""
    e = []
    if state == "few" and ln == 2 and dist <= 1024:
        e.append("m1few")
    if state == "many" and ln == 3 and 2049 <= dist <= 3072:
        e.append("m1many")
    if 3 <= ln <= 8 and dist <= 2048:
        e.append("m2")
    if ln >= 3 and dist <= 16384:
        e.append("m3")
    if ln >= 3 and 16385 <= dist <= 49151:
        e.append("m4")
    return e

def put_match(out, kind, ln, dist, s):
    if kind == "m1few":
        d = dist - 1
        out += bytes([(d & 3) << 2 | s, d >> 2])
    elif kind == "m1many":
        d = dist - 2049
        out += bytes([(d & 3) << 2 | s, d >> 2])
    elif kind == "m2":
        d = dist - 1
        out += bytes([(ln - 1) << 5 | (d & 7) << 2 | s, d >> 3])
    elif kind == "m3":
        f, ext = len_field(ln, 5, 2)
        d = dist - 1
        out += bytes([32 | f]) + ext + bytes([(d & 63) << 2 | s, d >> 6])
    else:
        f, ext = len_field(ln, 3, 2)
        t = dist - 16384
        out += bytes([16 | (t >> 14) << 3 | f]) + ext + bytes([(t & 63) << 2 | s, (t & 16383) >> 6])

def put_run(out, lits, first, rng):
    """A literal run: at the start of the stream, or after a match with S = 0."""
    k = len(lits)
    if k == 0:
        return
    if first and (k <= 3 or (k <= 238 and rng.random() < 0.7)):
        out.append(17 + k)
    else:
        assert k >= 4
        f, ext = len_field(k, 4, 3)
        out += bytes([f]) + ext
    out += lits

def compress(data, rng):
    """A greedy LZ77 encoder over hash chains, choosing encodings at random."""
    n, i, out = len(data), 0, bytearray()
    chains = {}
    lits = bytearray()
    pend = None                  # the last match, waiting for its S bits
    def state_of(k):
        if k == 0:
            return "zero"
        return "few" if k <= 3 else "many"

    def flush(lits):
        nonlocal pend
        k = len(lits)
        if pend is None:
            put_run(out, bytes(lits), True, rng)
        else:
            kind, ln, dist = pend
            put_match(out, kind, ln, dist, k if k <= 3 else 0)
            if k <= 3:
                out.extend(lits)
            else:
                put_run(out, bytes(lits), False, rng)
        pend = None

    while i < n:
        best_ln, best_d = 0, 0
        if i + 3 <= n:
            for p in reversed(chains.get(data[i:i + 3], [])[-8:]):
                d = i - p
                if d > 49151:
                    continue
                ln = 0
                while i + ln < n and data[p + ln] == data[i + ln] and ln < 2000:
                    ln += 1
                if ln > best_ln:
                    best_ln, best_d = ln, d
        k = len(lits)
        st = state_of(k)
        choice = None
        if best_ln >= 3:
            ln = best_ln
            if rng.random() < 0.2:
                ln = rng.randrange(3, best_ln + 1)
            if st == "many" and 2049 <= best_d <= 3072 and rng.random() < 0.5:
                ln = 3
            opts = encodings(ln, best_d, st)
            if opts:
                choice = (rng.choice(opts), ln, best_d)
        elif st == "few" and i + 2 <= n and rng.random() < 0.5:
            for p in range(i - 1, max(0, i - 1024) - 1, -1):
                if data[p:p + 2] == data[i:i + 2]:
                    choice = ("m1few", 2, i - p)
                    break
        if choice is not None and rng.random() < 0.95:
            flush(lits)
            lits = bytearray()
            pend = choice
            for q in range(i, min(i + choice[1], n - 2)):
                chains.setdefault(data[q:q + 3], []).append(q)
            i += choice[1]
        else:
            if i + 3 <= n:
                chains.setdefault(data[i:i + 3], []).append(i)
            lits.append(data[i])
            i += 1
    flush(lits)
    out += bytes([17, 0, 0])
    return bytes(out)

# The lzop container

MAGIC = bytes([137, 76, 90, 79, 0, 13, 10, 26, 10])

def lzop_header(flags, name=b"", method=1, level=5, mode=0, mtime=0, version=0x1030, lib=0x2080, need=0x0940):
    f = struct.pack(">HHHBBIIII", version, lib, need, method, level, flags, mode, mtime, 0) + bytes([len(name)]) + name
    s = zlib.crc32(f) if flags & 0x1000 else zlib.adler32(f)
    return MAGIC + f + struct.pack(">I", s)

def lzop_block(raw, comp, flags):
    stored = comp is None or len(comp) >= len(raw)
    out = struct.pack(">II", len(raw), len(raw) if stored else len(comp))
    if flags & 1:
        out += struct.pack(">I", zlib.adler32(raw))
    if flags & 0x100:
        out += struct.pack(">I", zlib.crc32(raw))
    if not stored:
        if flags & 2:
            out += struct.pack(">I", zlib.adler32(comp))
        if flags & 0x200:
            out += struct.pack(">I", zlib.crc32(comp))
    return out + (raw if stored else comp)

def lzop_write(data, rng, flags, bsize, **hdr):
    out = lzop_header(flags, **hdr)
    for j in range(0, len(data), bsize):
        raw = data[j:j + bsize]
        out += lzop_block(raw, compress(raw, rng), flags)
    return out + bytes(4)

def lzop_read(src, maxout, verify=True):
    """The content, or the name of the failure, in the package's order."""
    def be(i, k):
        if i + k > len(src):
            raise Fail("Truncated")
        return int.from_bytes(src[i:i + k], "big")
    try:
        if src[:9] != MAGIC:
            raise Fail("BadMagic")
        if be(9, 2) < 0x0940:
            raise Fail("BadVersion")
        be(11, 2)
        if be(13, 2) > 0x1040:
            raise Fail("BadVersion")
        if not 1 <= be(15, 1) <= 3:
            raise Fail("BadMethod")
        be(16, 1)
        flags = be(17, 4)
        if flags & (0x40 | 0x400 | 0x800):
            raise Fail("Unsupported")
        be(21, 4); be(25, 4); be(29, 4)
        nl = be(33, 1)
        s = be(34 + nl, 4)
        f = src[9:34 + nl]
        if s != (zlib.crc32(f) if flags & 0x1000 else zlib.adler32(f)):
            raise Fail("BadHeaderChecksum")
        p, room, out = 38 + nl, maxout, bytearray()
        while True:
            dst = be(p, 4)
            if dst == 0:
                if p + 4 != len(src):
                    raise Fail("Trailing")
                return bytes(out)
            if dst > 64 << 20:
                raise Fail("BadBlockSize")
            if dst > room:
                raise Fail("OutputTooLarge")
            n = be(p + 4, 4)
            if n > dst:
                raise Fail("BadBlockSize")
            comp = n < dst
            q = p + 8
            sums = {}
            for bit, name in [(1, "ad"), (0x100, "cd"), (2, "ac"), (0x200, "cc")]:
                if flags & bit and (comp or name in ("ad", "cd")):
                    sums[name] = be(q, 4)
                    q += 4
            if q + n > len(src):
                raise Fail("Truncated")
            data = src[q:q + n]
            if verify and comp:
                if ("ac" in sums and sums["ac"] != zlib.adler32(data)) or ("cc" in sums and sums["cc"] != zlib.crc32(data)):
                    raise Fail("BadChecksum")
            if comp:
                raw = decompress(data, dst)
                if isinstance(raw, str):
                    raise Fail(raw)
                if len(raw) != dst:
                    raise Fail("BadBlockSize")
            else:
                raw = data
            if verify:
                if ("ad" in sums and sums["ad"] != zlib.adler32(raw)) or ("cd" in sums and sums["cd"] != zlib.crc32(raw)):
                    raise Fail("BadChecksum")
            out += raw
            room -= dst
            p = q + n
    except Fail as e:
        return str(e)

# The lzop tool, when installed

TOOL = shutil.which("lzop")

def tool(args, data):
    with tempfile.TemporaryDirectory() as d:
        f = os.path.join(d, "in")
        open(f, "wb").write(data)
        return subprocess.run(["lzop", "-c"] + args + [f], check=True, capture_output=True).stdout

def tool_decode(src):
    """The tool's content of the file src, or its complaint."""
    r = subprocess.run(["lzop", "-dc"], input=src, capture_output=True)
    if r.returncode == 0:
        return r.stdout
    return "lzop -d: " + (r.stderr.decode(errors="replace").strip().split("\n") or [""])[0]

# Inputs

def sample(rng, n):
    """Compressible bytes: runs, repeats near and far, text, noise."""
    out = bytearray()
    words = [bytes(rng.randrange(97, 123) for _ in range(rng.randrange(2, 9))) for _ in range(12)]
    while len(out) < n:
        kind = rng.randrange(6)
        if kind == 0:
            out += bytes([rng.randrange(256)]) * rng.randrange(1, 400)
        elif kind == 1 and out:
            off = rng.randrange(1, min(len(out), 49151) + 1)
            for _ in range(rng.randrange(2, 300)):
                out.append(out[-off])
        elif kind == 2:
            out += b" ".join(rng.choice(words) for _ in range(rng.randrange(1, 30)))
        elif kind == 3:
            out += bytes(rng.randrange(256) for _ in range(rng.randrange(1, 40)))
        elif kind == 4 and len(out) >= 2:
            p = rng.randrange(len(out) - 1)
            out += out[p:p + rng.randrange(1, 100)]
        else:
            out += bytes(rng.randrange(4) for _ in range(rng.randrange(1, 60)))
    return bytes(out[:n])

def far(rng, n):
    """Noise with copies from far back: matches at M4 distances."""
    out = bytearray(rng.randrange(256) for _ in range(min(n, 17000)))
    while len(out) < n:
        if len(out) > 16400 and rng.random() < 0.5:
            off = rng.randrange(16385, min(len(out), 49151) + 1)
            for _ in range(rng.randrange(3, 40)):
                out.append(out[-off])
        else:
            out += bytes(rng.randrange(256) for _ in range(rng.randrange(1, 200)))
    return bytes(out[:n])

def text(rng, n):
    words = ["the", "lzo", "stream", "match", "distance", "literal", "state", "bend", "kernel",
             "page", "of", "and", "a", "to", "in", "is", "with", "data", "compression"]
    out = []
    while sum(len(w) + 1 for w in out) < n:
        out.append(rng.choice(words))
    return (" ".join(out)).encode()[:n]

def kinds(rng, n):
    k = rng.randrange(4)
    if k == 0:
        return "random", bytes(rng.randrange(256) for _ in range(n))
    if k == 1:
        return "text", text(rng, n)
    if k == 2:
        return "repetitive", (bytes(rng.randrange(256) for _ in range(rng.randrange(1, 9))) * (n + 1))[:n]
    return "mixed", sample(rng, n)

def corrupt(rng, src):
    s = bytearray(src)
    for _ in range(rng.randrange(1, 3)):
        kind = rng.randrange(5)
        if kind == 0 and s:
            s[rng.randrange(len(s))] = rng.randrange(256)
        elif kind == 1 and s:
            s[rng.randrange(len(s))] ^= 1 << rng.randrange(8)
        elif kind == 2 and s:
            del s[rng.randrange(len(s))]
        elif kind == 3:
            s.insert(rng.randrange(len(s) + 1), rng.randrange(256))
        else:
            del s[rng.randrange(len(s) + 1):]
    return bytes(s)

# Bend programs

HEAD = """import Base
import ../../bytes/bytes.bend as B
import ../error.bend as E
import ../decode.bend as D
import ../lzop.bend as P

def show(r: Result<&2, &2, E.LzoError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "!" ++ E.LzoError.show(e)
    case Done{o}:
      "=" ++ B.Octets.hex(o)

"""

CHEAD = """import Base
import ../../bytes/bytes.bend as B
import ../encode.bend as C
import ../lzop.bend as P

def same.pick(b: Bool) -> String:
  match b:
    case True{}:
      "same"
    case False{}:
      "fallback"

# "same" if the checked compressor kept the matcher's stream (no fallback)
def same(+opts: C.LzoCompressOptions, +o: B.Octets) -> String:
  same.pick(B.Octets.is_eq(C.lzo1x_compress_with(opts, o), C.lzo1x_compress_unchecked(opts, o)))

"""

def bl(data):
    # Bend's runtime overflows its stack on list literals of a few thousand
    # elements, so long inputs are joined from short pieces
    if len(data) > 1000:
        return "B.Octets.concat([" + ", ".join(bl(data[i:i + 1000]) for i in range(0, len(data), 1000)) + "])"
    return "B.Octets.of_list([" + ", ".join(str(b) for b in data) + "])"

def bb(b):
    return "True{}" if b else "False{}"

def show(r):
    return "!" + r if isinstance(r, str) else "=" + r.hex()

def write_programs(here, prefix, head, defs, lines, budget):
    """Programs of at most `budget` bytes of source each (the checker's memory)."""
    for old in os.listdir(here):
        if old.startswith(prefix) and old.endswith(".bend") and old[len(prefix):-5].isdigit():
            os.remove(os.path.join(here, old))
    groups, cur, size = [], [], 0
    for d, l in zip(defs, lines):
        if cur and size + len(d) > budget:
            groups.append(cur)
            cur, size = [], 0
        cur.append((d, l))
        size += len(d)
    if cur:
        groups.append(cur)
    for j, g in enumerate(groups):
        with open(os.path.join(here, "%s%02d.bend" % (prefix, j)), "w") as f:
            f.write(head + "\n".join(d for d, _ in g) + "\n")
            f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(l for _, l in g) + "\n")
    return len(groups)

COPTS = "C.LzoCompressOptions{%dn, %d}"

def wopts(o):
    return "P.LzopWriteOptions{%d, %s, %s, %s, %s, %s, 1, 5, %s, 0, 0, %s}" % (
        o["bsize"], bb(o["ad"]), bb(o["cd"]), bb(o["ac"]), bb(o["cc"]), bb(o["hc"]),
        bl(o["name"].encode()), COPTS % (o["bits"], o["far"]))

def flags_of(o):
    return (1 if o["ad"] else 0) | (2 if o["ac"] else 0) | (0x100 if o["cd"] else 0) | (0x200 if o["cc"] else 0) | (0x1000 if o["hc"] else 0)

def gen_compress(rng):
    defs, lines, cases = [], [], []

    def add(kind, call, info, data):
        k = len(cases)
        defs.append("def d%d() -> B.Octets:\n  %s\n\ndef c%d() -> String:\n  %s\n" % (k, bl(data), k, call.replace("DATA", "d%d()" % k)))
        lines.append('    IO.print("%d " ++ c%d())' % (k, k))
        cases.append(dict(info, kind=kind))

    for n in [0, 1, 2, 3, 4, 5, 17, 18, 19, 238, 239, 300, 1000, 4000] + [rng.randrange(0, 3000) for _ in range(10)]:
        what, data = kinds(rng, n)
        bits, fard = rng.choice([(14, 49151), (14, 49151), (10, 2048), (12, 16384), (16, 49151)])
        o = COPTS % (bits, fard)
        add("stream", 'B.Octets.hex(C.lzo1x_compress_with(%s, DATA)) ++ " " ++ same(%s, DATA)' % (o, o), dict(data=data.hex(), what=what), data)
    for _ in range(2):
        data = far(rng, rng.randrange(17000, 20000))
        add("stream", 'B.Octets.hex(C.lzo1x_compress(DATA)) ++ " " ++ same(C.LzoCompressOptions.default(), DATA)', dict(data=data.hex(), what="far"), data)
    for n in [0, 1, 300, 3000] + [rng.randrange(0, 3000) for _ in range(5)]:
        what, data = kinds(rng, n)
        o = dict(bsize=rng.choice([262144, 1000, 4096, 100]), ad=rng.random() < 0.7, cd=rng.random() < 0.4,
                 ac=rng.random() < 0.4, cc=rng.random() < 0.3, hc=rng.random() < 0.3,
                 name=rng.choice(["", "a.txt", "some/file"]), bits=14, far=49151)
        add("lzop", "B.Octets.hex(P.lzop_compress(%s, DATA))" % wopts(o), dict(data=data.hex(), what=what, opts=o), data)
    for _ in range(3):
        what, data = kinds(rng, rng.randrange(0, 3000))
        cuts = sorted(rng.randrange(len(data) + 1) for _ in range(rng.randrange(0, 4)))
        pieces = [data[a:b] for a, b in zip([0] + cuts, cuts + [len(data)])]
        o = dict(bsize=rng.choice([500, 2000]), ad=True, cd=rng.random() < 0.5, ac=rng.random() < 0.5,
                 cc=False, hc=False, name="s", bits=14, far=49151)
        add("lzop", "B.Octets.hex(P.lzop_stream(%s, [%s]))" % (wopts(o), ", ".join(bl(x) for x in pieces)),
            dict(data=data.hex(), what=what, opts=o, pieces=len(pieces)), b"")
    return defs, lines, cases

def verify(here, outfile):
    """Check the package's compressed output: it must decode to the input."""
    cases = json.load(open(os.path.join(here, "ccases.json")))
    got = [l.split(" ") for l in open(outfile).read().strip().split("\n")]
    if len(got) != len(cases):
        print("expected %d lines, got %d" % (len(cases), len(got)))
        return 1
    bad, tooled, smaller = 0, 0, 0
    for k, (c, g) in enumerate(zip(cases, got)):
        why = None
        data = bytes.fromhex(c["data"])
        comp = bytes.fromhex(g[1]) if len(g) > 1 else b""
        if c["kind"] == "stream":
            ok = decompress(comp, len(data)) == data and g[2] == "same"
            if c["what"] == "repetitive" and len(data) >= 100:
                ok = ok and len(comp) * 4 < len(data)
                smaller += 1
        else:
            ok = lzop_read(comp, len(data)) == data
            if TOOL:
                got_tool = tool_decode(comp)
                if isinstance(got_tool, str):
                    why = got_tool
                ok = ok and got_tool == data
                tooled += 1
        if not ok:
            bad += 1
            print("case %d (%s) does not decode back%s" % (k, c["kind"], (" (%s)" % why) if why else ""))
    if bad:
        return 1
    print("%d compressed (%d through lzop -d; %d repetitive inputs below a quarter of their size)" % (len(cases), tooled, smaller))
    return 0

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    defs, lines, expect = [], [], []

    def case(call, want):
        k = len(expect)
        defs.append("def case%d() -> String:\n  %s\n" % (k, call))
        lines.append('    IO.print("%d " ++ case%d())' % (k, k))
        expect.append("%d %s" % (k, show(want)))

    streams = []
    # round trips: streams written here, every encoding
    for n in [0, 1, 2, 3, 4, 5, 17, 18, 19, 20, 237, 238, 239, 274, 300, 1000, 2100, 3100] + [rng.randrange(0, 3000) for _ in range(22)]:
        data = sample(rng, n)
        src = compress(data, rng)
        assert decompress(src, len(data)) == data
        streams.append((src, len(data)))
        case("show(D.lzo1x_decompress(%s, %dn))" % (bl(src), len(data) + rng.randrange(0, 3)), data)
    for _ in range(2):           # M4 distances
        data = far(rng, rng.randrange(17000, 20000))
        src = compress(data, rng)
        assert decompress(src, len(data)) == data
        case("show(D.lzo1x_decompress(%s, %dn))" % (bl(src), len(data)), data)
    # the output limit, one below the size
    for src, n in streams[18:24]:
        if n > 0:
            want = decompress(src, n - 1)
            assert want == "OutputTooLarge"
            case("show(D.lzo1x_decompress(%s, %dn))" % (bl(src), n - 1), want)
    # streaming: the pieces give what the whole gives
    for _ in range(10):
        src, n = rng.choice(streams)
        if rng.random() < 0.3:
            src = corrupt(rng, src)
        cuts = sorted(rng.randrange(len(src) + 1) for _ in range(rng.randrange(0, 4)))
        pieces = [src[a:b] for a, b in zip([0] + cuts, cuts + [len(src)])]
        case("show(D.reader_decompress(%dn, [%s]))" % (n + 10, ", ".join(bl(p) for p in pieces)), decompress(src, n + 10))
    # corruptions: the package answers what this decoder answers
    for _ in range(110):
        src, n = rng.choice(streams)
        bad = corrupt(rng, src)
        room = n + rng.randrange(0, 64)
        case("show(D.lzo1x_decompress(%s, %dn))" % (bl(bad), room), decompress(bad, room))
    # lzop files written here, across the flags
    files = []
    for _ in range(16):
        what, data = kinds(rng, rng.choice([0, 1, 300, rng.randrange(0, 3000)]))
        flags = rng.choice([1, 0, 1 | 2, 0x100, 0x100 | 0x200, 1 | 2 | 0x100 | 0x200, 1 | 0x1000, 3 | 0x1000])
        src = lzop_write(data, rng, flags, rng.choice([262144, 1000, 333]), name=rng.choice([b"", b"x.lzo", b"dir/name"]),
                         method=rng.choice([1, 2, 3]), level=rng.randrange(1, 10), mode=rng.choice([0, 33188]),
                         mtime=rng.randrange(1 << 32))
        assert lzop_read(src, len(data)) == data
        files.append((src, len(data)))
        case("show(P.lzop_decompress(P.LzopOptions{%d, True{}}, %s))" % (len(data) + 5, bl(src)), data)
    # the lzop tool's files, across its levels
    if TOOL:
        for k in range(20):
            what, data = kinds(rng, rng.choice([0, 1, 15, rng.randrange(0, 12000)]))
            src = tool([rng.choice(["-1", "-3", "-7", "-9"])], data)
            assert lzop_read(src, len(data)) == data
            files.append((src, len(data)))
            case("show(P.lzop_decompress(P.LzopOptions{%d, True{}}, %s))" % (len(data), bl(src)), data)
    for _ in range(40):
        src, n = rng.choice(files)
        bad = corrupt(rng, src)
        room, ver = n + rng.randrange(0, 64), rng.random() < 0.8
        case("show(P.lzop_decompress(P.LzopOptions{%d, %s}, %s))" % (room, bb(ver), bl(bad)), lzop_read(bad, room, ver))

    nprog = write_programs(here, "cases", HEAD, defs, lines, 400000)
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    cdefs, clines, ccases = gen_compress(rng)
    write_programs(here, "ccases", CHEAD, cdefs, clines, 400000)
    with open(os.path.join(here, "ccases.json"), "w") as f:
        json.dump(ccases, f)
    rejected = sum(1 for e in expect if " !" in e)
    print("%d cases (%d rejected%s)" % (len(expect), rejected, ", lzop tool files included" if TOOL else ""))

if len(sys.argv) > 1 and sys.argv[1] == "verify":
    sys.exit(verify(os.path.dirname(os.path.abspath(__file__)), sys.argv[2]))
main()
