#!/usr/bin/env python3
"""Differential test cases for bend-osdev-lz4.

There is no lz4 tool or Python lz4 module to compare with, so this file holds
an independent implementation, written here from the LZ4 project's
specifications (lz4_Block_format.md, lz4_Frame_format.md) and the xxHash
specification (XXH32):
  * a block encoder: a greedy LZ77 matcher with a hash table, that emits
    valid sequences (overlapping matches, long literal and match lengths, and
    the end-of-block rules);
  * a frame writer: every FLG option, linked and independent blocks,
    uncompressed blocks, several blocks per frame, skippable frames, several
    frames per stream;
  * a block and frame decoder, which rejects what the specification calls
    malformed, naming the failure as the package does.
They share an author with the package, so they check it against a second
reading of the specification, not against the reference implementation.

When the reference lz4 tool is installed, it is the reference for both
directions: the package decodes the tool's frames (across its options), and
the tool decodes the package's frames.

Writes ref/cases.bend (a Bend program printing the package's answer for each
case) and ref/expected.txt (the answers expected):
  * round trips: random inputs, encoded here, decoded by the package;
  * corruptions: encoded inputs with bytes flipped, deleted, inserted or cut
    off; the package must answer exactly what this decoder answers (the same
    bytes, or the same failure);
  * the lz4 tool's frames, across its options, decoded by the package.
It also writes ref/ccasesNN.bend, which print the package's compressed blocks
and frames, and ref/ccases.json, the inputs; `gen.py verify OUT` checks the
package's output OUT: every block and frame must decode back to its input
with this file's decoder and, when installed, with `lz4 -d`.
"""
import json, os, random, shutil, subprocess, sys, tempfile

# XXH32 (xxHash specification)

P1, P2, P3, P4, P5 = 2654435761, 2246822519, 3266489917, 668265263, 374761393
MASK = 0xFFFFFFFF

def rotl(x, r):
    return ((x << r) | (x >> (32 - r))) & MASK

def xxh32(data, seed=0):
    n, i = len(data), 0
    if n >= 16:
        v = [(seed + P1 + P2) & MASK, (seed + P2) & MASK, seed, (seed - P1) & MASK]
        while i + 16 <= n:
            for k in range(4):
                lane = int.from_bytes(data[i:i + 4], "little")
                v[k] = (rotl((v[k] + lane * P2) & MASK, 13) * P1) & MASK
                i += 4
        h = (rotl(v[0], 1) + rotl(v[1], 7) + rotl(v[2], 12) + rotl(v[3], 18)) & MASK
    else:
        h = (seed + P5) & MASK
    h = (h + n) & MASK
    while i + 4 <= n:
        h = (rotl((h + int.from_bytes(data[i:i + 4], "little") * P3) & MASK, 17) * P4) & MASK
        i += 4
    while i < n:
        h = (rotl((h + data[i] * P5) & MASK, 11) * P1) & MASK
        i += 1
    h ^= h >> 15
    h = (h * P2) & MASK
    h ^= h >> 13
    h = (h * P3) & MASK
    h ^= h >> 16
    return h

assert xxh32(b"") == 0x02CC5D05 and xxh32(b"abc") == 0x32D153FF

# The block format: encoder

MINMATCH, LASTLITERALS, MFLIMIT = 4, 5, 12

def put_len(out, r):
    while r >= 255:
        out.append(255)
        r -= 255
    out.append(r)

def put_seq(out, lits, off, ml):
    L = len(lits)
    m = 0 if off is None else ml - MINMATCH
    out.append(min(L, 15) << 4 | min(m, 15))
    if L >= 15:
        put_len(out, L - 15)
    out += lits
    if off is not None:
        out += off.to_bytes(2, "little")
        if m >= 15:
            put_len(out, m - 15)

def compress_block(data, hist=b"", rng=None):
    """A greedy LZ77 block encoder. Matches may reach back into hist."""
    full = bytes(hist[-65535:]) + bytes(data)
    base, n = len(full) - len(data), len(data)
    table = {}
    for p in range(max(0, base - 65535), base - 3):
        table[full[p:p + 4]] = p
    out, anchor, i = bytearray(), 0, 0
    while i + MFLIMIT <= n:          # the last match starts 12 bytes or more before the end
        seq = full[base + i:base + i + 4]
        cand = table.get(seq)
        table[seq] = base + i
        if cand is None or base + i - cand > 65535 or (rng and rng.random() < 0.1):
            i += 1
            continue
        ml = MINMATCH
        while i + ml < n - LASTLITERALS and full[cand + ml] == full[base + i + ml]:
            ml += 1                  # it ends 5 bytes or more before the end; it may overlap
        put_seq(out, data[anchor:i], base + i - cand, ml)
        for p in range(i + 1, min(i + ml, n - 3)):
            table[full[base + p:base + p + 4]] = base + p
        i += ml
        anchor = i
    put_seq(out, data[anchor:], None, 0)
    return bytes(out)

# The block format: decoder (answers the bytes, or the name of the failure)

def decompress_block(src, hist, maxout):
    """The block's bytes, or an error name. hist: the bytes it may refer back into."""
    out, i, n, last = bytearray(), 0, len(src), 0
    while True:
        if i >= n:
            return "Truncated"
        t = src[i]; i += 1
        L = t >> 4
        if L == 15:
            while True:
                if i >= n:
                    return "Truncated"
                b = src[i]; i += 1
                L += b
                if b != 255:
                    break
        if len(out) + min(L, n - i) > maxout:
            return "OutputTooLarge"
        if i + L > n:
            return "Truncated"
        out += src[i:i + L]; i += L
        if i == n:                   # the last sequence: literals only
            if t & 15 or (last and (L < LASTLITERALS or L + last < MFLIMIT)):
                return "BadBlockEnd"
            return bytes(out)
        if i + 2 > n:
            return "Truncated"
        off = src[i] | src[i + 1] << 8; i += 2
        M = (t & 15) + MINMATCH
        if t & 15 == 15:
            while True:
                if i >= n:
                    return "Truncated"
                b = src[i]; i += 1
                M += b
                if b != 255:
                    break
        if off == 0 or off > len(hist) + len(out):
            return "BadOffset"
        if len(out) + M > maxout:
            return "OutputTooLarge"
        for _ in range(M):
            k = len(out) - off
            out.append(out[k] if k >= 0 else hist[len(hist) + k])
        last = M

# The frame format: writer

MAGIC, SKIP = 0x184D2204, 0x184D2A50
BMAX = {4: 1 << 16, 5: 1 << 18, 6: 1 << 20, 7: 1 << 22}

def le32(v):
    return (v & MASK).to_bytes(4, "little")

def write_frame(data, rng, dict_=b"", indep=True, bsum=False, csize=False, csum=False,
                dict_id=None, code=4, raw_prob=0.2):
    flg = 0x40 | indep << 5 | bsum << 4 | csize << 3 | csum << 2 | (dict_id is not None)
    desc = bytes([flg, code << 4])
    if csize:
        desc += len(data).to_bytes(8, "little")
    if dict_id is not None:
        desc += le32(dict_id)
    out = bytearray(le32(MAGIC) + desc + bytes([(xxh32(desc) >> 8) & 255]))
    pos, hist = 0, bytes(dict_)
    while pos < len(data):
        k = min(rng.choice([rng.randrange(1, 700), 4096, BMAX[code]]), len(data) - pos, BMAX[code])
        chunk = data[pos:pos + k]
        comp = compress_block(chunk, dict_ if indep else hist, rng)
        if len(comp) >= len(chunk) or rng.random() < raw_prob:
            stored, size = chunk, len(chunk) | 0x80000000
        else:
            stored, size = comp, len(comp)
        out += le32(size) + stored
        if bsum:
            out += le32(xxh32(stored))
        hist += chunk
        pos += k
    out += le32(0)
    if csum:
        out += le32(xxh32(data))
    return bytes(out)

def skippable(rng):
    body = bytes(rng.randrange(256) for _ in range(rng.randrange(0, 20)))
    return le32(SKIP + rng.randrange(16)) + le32(len(body)) + body

# The frame format: decoder

def u32(src, i):
    return int.from_bytes(src[i:i + 4], "little") if i + 4 <= len(src) else None

def decompress_frame_at(src, i, dict_, room, verify):
    """(content, index after the frame), or an error name."""
    magic = u32(src, i)
    if magic is None:
        return "Truncated"
    if magic != MAGIC:
        return "BadMagic"
    if i + 6 > len(src):
        return "Truncated"
    flg, bd = src[i + 4], src[i + 5]
    if flg & 0xC0 != 0x40:
        return "BadVersion"
    if flg & 2 or bd & 0x8F or (bd >> 4) < 4:
        return "BadDescriptor"
    bmax = BMAX[bd >> 4]
    dlen = 2 + (8 if flg & 8 else 0) + (4 if flg & 1 else 0)
    if i + 4 + dlen >= len(src):
        return "Truncated"
    desc = src[i + 4:i + 4 + dlen]
    if src[i + 4 + dlen] != (xxh32(desc) >> 8) & 255:
        return "BadHeaderChecksum"
    size = int.from_bytes(desc[2:10], "little") if flg & 8 else None
    j, out = i + 5 + dlen, bytearray()
    while True:
        w = u32(src, j)
        if w is None:
            return "Truncated"
        j += 4
        if w == 0:
            break
        n = w & 0x7FFFFFFF
        if n > bmax:
            return "BlockTooLarge"
        if j + n > len(src):
            return "Truncated"
        data = src[j:j + n]; j += n
        if flg & 16:
            s = u32(src, j)
            if s is None:
                return "Truncated"
            if verify and s != xxh32(data):
                return "BadBlockChecksum"
            j += 4
        if w & 0x80000000:
            if n > room - len(out):
                return "OutputTooLarge"
            out += data
        else:
            hist = dict_ if flg & 32 else bytes(dict_) + bytes(out)
            blk = decompress_block(data, hist, min(room - len(out), bmax, (n + 1) * 256))
            if isinstance(blk, str):
                return blk
            out += blk
    if size is not None and size != len(out):
        return "BadContentSize"
    if flg & 4:
        s = u32(src, j)
        if s is None:
            return "Truncated"
        if verify and s != xxh32(out):
            return "BadContentChecksum"
        j += 4
    return bytes(out), j

def decompress_stream(src, dict_, maxout, verify=True):
    """The content of one frame or more, or an error name."""
    if not src:
        return "Truncated"
    i, out = 0, bytearray()
    while i < len(src):
        m = u32(src, i)
        if m is None:
            return "Truncated"
        if m == MAGIC:
            r = decompress_frame_at(src, i, dict_, maxout - len(out), verify)
            if isinstance(r, str):
                return r
            out += r[0]
            i = r[1]
        elif m & 0xFFFFFFF0 == SKIP:
            k = u32(src, i + 4)
            if k is None or i + 8 + k > len(src):
                return "Truncated"
            i += 8 + k
        else:
            return "BadMagic"
    return bytes(out)


# The reference lz4 tool

TOOL = shutil.which("lz4")

def tool(args, data):
    with tempfile.TemporaryDirectory() as d:
        src, dst = os.path.join(d, "in"), os.path.join(d, "out")
        with open(src, "wb") as f:
            f.write(data)
        subprocess.run([TOOL, "-q", "-f"] + args + [src, dst], check=True)
        with open(dst, "rb") as f:
            return f.read()

def tool_decode(frame, dict_=None):
    with tempfile.TemporaryDirectory() as d:
        src, dst, dic = os.path.join(d, "in.lz4"), os.path.join(d, "out"), os.path.join(d, "dict")
        with open(src, "wb") as f:
            f.write(frame)
        extra = []
        if dict_ is not None:
            with open(dic, "wb") as f:
                f.write(dict_)
            extra = ["-D", dic]
        r = subprocess.run([TOOL, "-q", "-d", "-f"] + extra + [src, dst])
        if r.returncode != 0:
            return None
        with open(dst, "rb") as f:
            return f.read()

TOOL_OPTS = [["-1"], ["-9"], ["-12"], ["-B4"], ["-B5"], ["-B6"], ["-B7"], ["--content-size"],
             ["--no-frame-crc"], ["-BD"], ["-BX"], ["-B256"], ["-BD", "-B512"], ["-BD", "-B1024", "-9"],
             ["-BX", "-B300", "--content-size"], ["-BD", "-B128", "--no-frame-crc", "-12"], ["-3", "-BD", "-B2048"]]

# a frame around one block, for the tool to decode: independent, no checksum
def wrap_block(comp, n):
    desc = bytes([0x60, 0x40])
    hc = bytes([(xxh32(desc) >> 8) & 255])
    if comp is None:
        return None
    return le32(MAGIC) + desc + hc + le32(len(comp)) + comp + le32(0)

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
            off = rng.randrange(1, min(len(out), 65535) + 1)
            for _ in range(rng.randrange(4, 300)):
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

HEAD = """import Base
import ../../bytes/bytes.bend as B
import ../block.bend as K
import ../frame.bend as F
import ../lz4.bend as L

def show(r: Result<&2, &2, K.Lz4Error, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "!" ++ K.Lz4Error.show(e)
    case Done{o}:
      "=" ++ B.Octets.hex(o)

def show_frame(r: Result<&2, &2, K.Lz4Error, F.Lz4Frame>) -> String:
  match r:
    case Fail{e}:
      "!" ++ K.Lz4Error.show(e)
    case Done{F.Lz4Frame{c, rest}}:
      "=" ++ B.Octets.hex(c) ++ " " ++ B.Octets.hex(rest)

"""

def bl(data):
    # Bend 2.0.37's runtime overflows its stack on list literals of a few
    # thousand elements, so long inputs are joined from short pieces
    if len(data) > 1000:
        return "B.Octets.concat([" + ", ".join(bl(data[i:i + 1000]) for i in range(0, len(data), 1000)) + "])"
    return "B.Octets.of_list([" + ", ".join(str(b) for b in data) + "])"

def show(r):
    return "!" + r if isinstance(r, str) else "=" + r.hex()

def opts(room, verify, d):
    return "F.Lz4Options{%d, %s, %s}" % (room, "True{}" if verify else "False{}", bl(d))

CHEAD = """import Base
import ../../bytes/bytes.bend as B
import ../compress.bend as C

def feed_all(ps: List<&2, B.Octets>, r: C.Lz4Written, acc: B.Octets) -> B.Octets:
  match ps:
    case Nil{}:
      match r:
        case C.Lz4Written{w, bytes}:
          B.Octets.append(B.Octets.append(acc, bytes), C.frame_finish(w))
    case Con{p, t}:
      match r:
        case C.Lz4Written{w, bytes}:
          feed_all(t, C.frame_feed(w, p), B.Octets.append(acc, bytes))

def stream(opts: C.Lz4FrameOptions, ps: List<&2, B.Octets>) -> B.Octets:
  feed_all(ps, C.frame_start(opts), B.Octets.empty())

def same.pick(b: Bool) -> String:
  match b:
    case True{}:
      "same"
    case False{}:
      "fallback"

# "same" if the checked compressor kept the matcher's block (no fallback)
def same(+o: B.Octets) -> String:
  same.pick(B.Octets.is_eq(C.block_compress(o), C.block_compress_unchecked(o)))

"""

def bb(b):
    return "True{}" if b else "False{}"

def fopts(o):
    return "C.Lz4FrameOptions{C.%s{}, %d, %s, %s, %s, %s}" % (
        {4: "Lz4Max64KB", 5: "Lz4Max256KB", 6: "Lz4Max1MB", 7: "Lz4Max4MB"}[o["code"]], o["bsize"],
        bb(o["indep"]), bb(o["bsum"]), bb(o["csum"]), bb(o["csize"]))

def text(rng, n):
    words = ["the", "lz4", "frame", "block", "match", "offset", "literal", "token", "bend", "kernel",
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

def gen_compress(rng, here):
    """ccases.bend: the package's compressed blocks and frames; ccases.json: the inputs."""
    defs, lines, cases = [], [], []

    def add(kind, call, info, data):
        k = len(cases)
        defs.append("def d%d() -> B.Octets:\n  %s\n\ndef c%d() -> String:\n  %s\n" % (k, bl(data), k, call.replace("DATA", "d%d()" % k)))
        lines.append('    IO.print("%d " ++ c%d())' % (k, k))
        cases.append(dict(info, kind=kind))

    for n in [0, 1, 5, 12, 13, 14, 20, 100, 1000, 4000, 8000] + [rng.randrange(0, 8000) for _ in range(20)]:
        what, data = kinds(rng, n)
        add("block", 'B.Octets.hex(C.block_compress(DATA)) ++ " " ++ same(DATA)', dict(data=data.hex(), what=what), data)
    for _ in range(8):
        d = sample(rng, rng.randrange(1, 2000))
        data = (d[rng.randrange(len(d)):] + text(rng, rng.randrange(0, 2000)))[:rng.randrange(0, 3000)]
        add("dict", "B.Octets.hex(C.block_compress_dict(%s, DATA))" % bl(d), dict(data=data.hex(), dict=d.hex()), data)
    for n in [0, 1, 300, 5000, 8000] + [rng.randrange(0, 8000) for _ in range(15)]:
        what, data = kinds(rng, n)
        o = dict(code=rng.choice([4, 4, 5, 6, 7]), bsize=rng.choice([0, 65536, 1000, 4096, 100]),
                 indep=rng.random() < 0.5, bsum=rng.random() < 0.5, csum=rng.random() < 0.7, csize=rng.random() < 0.5)
        add("frame", "B.Octets.hex(C.frame_compress(%s, DATA))" % fopts(o), dict(data=data.hex(), what=what, opts=o), data)
    t = text(rng, 3000)
    add("frame", "B.Octets.hex(C.compress(DATA))", dict(data=t.hex(), what="default"), t)
    for _ in range(8):
        what, data = kinds(rng, rng.randrange(0, 6000))
        cuts = sorted(rng.randrange(len(data) + 1) for _ in range(rng.randrange(0, 4)))
        pieces = [data[a:b] for a, b in zip([0] + cuts, cuts + [len(data)])]
        o = dict(code=4, bsize=rng.choice([0, 500, 2000]), indep=rng.random() < 0.5, bsum=rng.random() < 0.5,
                 csum=rng.random() < 0.7, csize=False)
        add("frame", "B.Octets.hex(stream(%s, [%s]))" % (fopts(o), ", ".join(bl(x) for x in pieces)),
            dict(data=data.hex(), what=what, opts=o, pieces=len(pieces)), b"")
    return defs, lines, cases

def verify(here, outfile):
    """Check the package's compressed output: it must decode to the input."""
    cases = json.load(open(os.path.join(here, "ccases.json")))
    got = [l.split(" ") for l in open(outfile).read().strip().split("\n")]
    if len(got) != len(cases):
        print("expected %d lines, got %d" % (len(cases), len(got)))
        return 1
    bad, tooled, smaller, ours, theirs = 0, 0, 0, 0, 0
    for k, (c, g) in enumerate(zip(cases, got)):
        data = bytes.fromhex(c["data"])
        comp = bytes.fromhex(g[1]) if len(g) > 1 else b""
        if c["kind"] == "block":
            ok = decompress_block(comp, b"", len(data)) == data and g[2] == "same"
            if TOOL:
                ok = ok and tool_decode(wrap_block(comp, len(data))) == data
                tooled += 1
            if c["what"] == "repetitive" and len(data) >= 100:
                ok = ok and len(comp) * 4 < len(data)
                smaller += 1
        elif c["kind"] == "dict":
            d = bytes.fromhex(c["dict"])
            ok = decompress_block(comp, d, len(data)) == data
            if TOOL:
                frame = le32(MAGIC) + bytes([0x40, 0x40, (xxh32(bytes([0x40, 0x40])) >> 8) & 255]) + le32(len(comp)) + comp + le32(0)
                ok = ok and tool_decode(frame, d[-65536:]) == data
                tooled += 1
        else:
            ok = decompress_stream(comp, b"", len(data)) == data
            if c.get("what") == "default":
                ok = ok and comp[4:7] == bytes([0x64, 0x40, 0xA7])
            if TOOL:
                ok = ok and tool_decode(comp) == data
                tooled += 1
                ours += len(comp)
                theirs += len(tool(["-1"], data))
        if not ok:
            bad += 1
            print("case %d (%s) does not decode back" % (k, c["kind"]))
    if bad:
        return 1
    ratio = " frames %d bytes against lz4 -1's %d;" % (ours, theirs) if TOOL else ""
    print("%d compressed (%d through lz4 -d;%s %d repetitive inputs below a quarter of their size)" % (len(cases), tooled, ratio, smaller))
    return 0

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []

    defs = []

    def case(call, want, shower="show"):
        k = len(expect)
        defs.append("def case%d() -> String:\n  %s(%s)\n" % (k, shower, call))
        lines.append('    IO.print("%d " ++ case%d())' % (k, k))
        expect.append("%d %s" % (k, want if shower != "show" else show(want)))

    sizes = [0, 1, 4, 5, 11, 12, 13, 14, 15, 16, 20, 64, 255, 270, 300, 525, 1000, 1500, 2000, 3000]
    blocks = []
    # round trips: blocks
    for n in sizes + [rng.randrange(0, 2500) for _ in range(40)]:
        data = sample(rng, n)
        comp = compress_block(data, b"", rng if rng.random() < 0.5 else None)
        assert decompress_block(comp, b"", len(data)) == data
        blocks.append((comp, len(data)))
        case("K.block_decompress(%s, %dn)" % (bl(comp), len(data)), data)
    # round trips: blocks after a dictionary
    for _ in range(15):
        d = sample(rng, rng.randrange(1, 800))
        data = (d[rng.randrange(len(d)):] + sample(rng, rng.randrange(0, 600)))[:rng.randrange(0, 900)]
        comp = compress_block(data, d)
        assert decompress_block(comp, d, len(data)) == data
        case("K.block_decompress_dict(%s, %s, %dn)" % (bl(d), bl(comp), len(data)), data)
    # an output limit below the size: rejected
    for comp, n in blocks[20:30]:
        if n > 0:
            want = decompress_block(comp, b"", n - 1)
            assert want == "OutputTooLarge"
            case("K.block_decompress(%s, %dn)" % (bl(comp), n - 1), want)
    # round trips: frames and streams
    frames = []
    for _ in range(40):
        data = sample(rng, rng.choice([0, 1, 13, rng.randrange(0, 4000)]))
        d = sample(rng, rng.randrange(1, 300)) if rng.random() < 0.2 else b""
        o = dict(indep=rng.random() < 0.5, bsum=rng.random() < 0.5, csize=rng.random() < 0.5,
                 csum=rng.random() < 0.5, code=rng.choice([4, 4, 5, 6, 7]),
                 dict_id=rng.randrange(1 << 32) if d and rng.random() < 0.7 else None)
        src = write_frame(data, rng, d, **o)
        want = data
        if rng.random() < 0.3:      # more frames, and skippable frames
            more = sample(rng, rng.randrange(0, 500))
            src = skippable(rng) + src + skippable(rng) + write_frame(more, rng, d, indep=True, csum=True)
            want = data + more
        assert decompress_stream(src, d, len(want)) == want
        frames.append((src, d, len(want)))
        case("L.decompress_with(%s, %s)" % (opts(len(want), True, d), bl(src)), want)
    # the defaults, and one frame with the input after it
    plain = write_frame(sample(rng, 700), rng, b"", csum=True, bsum=True)
    case("L.decompress(%s)" % bl(plain), decompress_stream(plain, b"", 1 << 26))
    tail = bytes([1, 2, 3])
    one = write_frame(b"frame then more", rng, b"", csum=True) + tail
    case("F.frame_decompress(F.Lz4Options.default(), %s)" % bl(one), "=%s %s" % (b"frame then more".hex(), tail.hex()), "show_frame")
    # the lz4 tool's frames, across its options
    if TOOL:
        for k in range(60):
            what, data = kinds(rng, rng.choice([0, 1, 15, rng.randrange(0, 12000)]))
            args = TOOL_OPTS[k % len(TOOL_OPTS)]
            src = tool(args, data)
            assert decompress_stream(src, b"", len(data)) == data, args
            frames.append((src, b"", len(data)))
            case("L.decompress_with(%s, %s)" % (opts(len(data), True, b""), bl(src)), data)

    # corruptions: the package answers what this decoder answers
    for _ in range(140):
        comp, n = rng.choice(blocks)
        bad = corrupt(rng, comp)
        room = n + rng.randrange(0, 64)
        case("K.block_decompress(%s, %dn)" % (bl(bad), room), decompress_block(bad, b"", room))
    for _ in range(100):
        src, d, n = rng.choice(frames)
        bad = corrupt(rng, src)
        room = n + rng.randrange(0, 64)
        verify = rng.random() < 0.8
        case("L.decompress_with(%s, %s)" % (opts(room, verify, d), bl(bad)), decompress_stream(bad, d, room, verify))

    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write(HEAD + "\n".join(defs) + "\n")
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    cdefs, clines, ccases = gen_compress(rng, here)
    # several programs: Bend's checker runs out of memory on one this large
    for old in os.listdir(here):
        if old.startswith("ccases") and old.endswith(".bend"):
            os.remove(os.path.join(here, old))
    per = 16
    for j in range(0, len(cdefs), per):
        with open(os.path.join(here, "ccases%02d.bend" % (j // per)), "w") as f:
            f.write(CHEAD + "\n".join(cdefs[j:j + per]) + "\n")
            f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(clines[j:j + per]) + "\n")
    with open(os.path.join(here, "ccases.json"), "w") as f:
        json.dump(ccases, f)
    rejected = sum(1 for e in expect if " !" in e)
    print("%d cases (%d rejected%s)" % (len(expect), rejected, ", lz4 tool frames included" if TOOL else ""))

if len(sys.argv) > 1 and sys.argv[1] == "verify":
    sys.exit(verify(os.path.dirname(os.path.abspath(__file__)), sys.argv[2]))
main()
