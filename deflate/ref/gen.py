#!/usr/bin/env python3
"""Differential test cases for bend-osdev-deflate.

  gen.py SEED     writes the case files into ref/work/, the runner's arguments
                  (args.txt) and the expected output (expected.txt); prints
                  the number of cases
  gen.py verify   checks the streams the package compressed (work/*.out named
                  in args.txt): each must decode back to its input with
                  Python's zlib and gzip modules and, for gzip files, the
                  gzip tool; prints a summary with the compression ratios

Decoding: streams made by Python's zlib module (zlib 1.3) in all three formats
(raw DEFLATE, zlib, gzip), at every level 0 to 9, with every strategy
(default, filtered, Huffman only, RLE, fixed), several window sizes and
memory levels, and by the gzip tool at levels 1, 6 and 9; several gzip
members, trailing bytes; streams built by hand that zlib refuses (each kind
of bad header and bad code, built with this file's own bit writer); and
damaged copies of many streams (a bit flipped, a byte changed or zeroed,
bytes deleted or inserted, the end cut off). The expected answer, the
output's length and zlib CRC-32 or an error, is zlib's for raw and zlib
streams and the gzip tool's for gzip files (exit status 0 or 2, "trailing
garbage ignored", is success; 1 is an error). Many streams of all three
formats are also decoded through the format's streaming decoder, fed in
pieces (three, or single bytes for files under 4 KB), with the same
expected answer.

Encoding: the package compresses inputs at every level, with every strategy
and block type, in all three formats, and through each format's streaming
writer; each must decode back to its input, and a streaming writer's stream
must be the one-shot stream byte for byte.
"""
import binascii, gzip, os, random, shutil, subprocess, sys, zlib

HERE = os.path.dirname(os.path.abspath(__file__))
WORK = os.path.join(HERE, "work")
ROOT = os.path.dirname(os.path.dirname(HERE))
TOOL = shutil.which("gzip")


# A small DEFLATE bit writer, for the streams zlib cannot be asked to make

class Bits:
    def __init__(self):
        self.v, self.n = 0, 0

    def put(self, val, n):  # a field, low bit first (RFC 1951, 3.1.1)
        self.v |= (val & ((1 << n) - 1)) << self.n
        self.n += n

    def code(self, c, n):  # a Huffman code, high bit first
        for i in range(n - 1, -1, -1):
            self.put((c >> i) & 1, 1)

    def bytes(self):
        return self.v.to_bytes((self.n + 7) // 8, "little")


def canon(lens):  # RFC 1951, 3.2.2
    mx = max(lens + [0])
    count = [0] * (mx + 2)
    for l in lens:
        if l:
            count[l] += 1
    code, nxt = 0, [0] * (mx + 2)
    for b in range(1, mx + 1):
        code = (code + count[b - 1]) << 1
        nxt[b] = code
    out = {}
    for i, l in enumerate(lens):
        if l:
            out[i] = (nxt[l], l)
            nxt[l] += 1
    return out


ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15]
FIXED = [8] * 144 + [9] * 112 + [7] * 24 + [8] * 8


def complete(used):  # code lengths of a complete code for these symbols
    out = {}
    k = len(used)
    if k == 1:
        out[used[0]] = 1
        return out
    m = (k - 1).bit_length()
    short = 2 ** m - k
    for j, s in enumerate(used):
        out[s] = m - 1 if j < short else m
    return out


def dynamic(lit, dist, syms, final=1, rle=None, clen=None, hlit=None, hdist=None):
    """A dynamic block: lit/dist code lengths, then symbols (('l', v) or
    ('d', v), with optional extra bits (value, n))."""
    w = Bits()
    w.put(final, 1)
    w.put(2, 2)
    w.put((len(lit) - 257) if hlit is None else hlit, 5)
    w.put((len(dist) - 1) if hdist is None else hdist, 5)
    seq = rle if rle is not None else [(l, 0, 0) for l in lit + dist]
    if clen is None:
        clen = [0] * 19
        for s, l in complete(sorted(set(x for x, _, _ in seq))).items():
            clen[s] = l
    w.put(15, 4)
    for i in range(19):
        w.put(clen[ORDER[i]], 3)
    cc = canon(clen)
    for s, eb, ev in seq:
        c, n = cc[s]
        w.code(c, n)
        if eb:
            w.put(ev, eb)
    lc, dc = canon(lit), canon(dist)
    for kind, v, *extra in syms:
        c, n = (lc if kind == "l" else dc)[v]
        w.code(c, n)
        if extra:
            w.put(extra[0], extra[1])
    return w.bytes()


def fixed(syms, final=1):
    w = Bits()
    w.put(final, 1)
    w.put(1, 2)
    lc, dc = canon(FIXED), canon([5] * 32)
    for kind, v, *extra in syms:
        c, n = (lc if kind == "l" else dc)[v]
        w.code(c, n)
        if extra:
            w.put(extra[0], extra[1])
    return w.bytes()


def handmade():
    """Streams built by hand, most of them malformed."""
    A = [("l", 65), ("l", 256)]
    two = [0] * 65 + [1] + [0] * 190 + [1]  # 'A' and 256, one bit each
    four = [0] * 65 + [2] + [0] * 190 + [2, 2, 2]  # A, 256, 257, 258
    out = {
        "btype3": bytes([7, 0, 0]),
        "btype3_nonfinal": bytes([6, 0, 0]),
        "stored": bytes([1, 3, 0, 252, 255]) + b"abc",
        "stored_badnlen": bytes([1, 3, 0, 252, 254]) + b"abc",
        "stored_short": bytes([1, 3, 0, 252, 255]) + b"ab",
        "stored_nonfinal": bytes([0, 3, 0, 252, 255]) + b"abc",
        "stored_trailing": bytes([1, 3, 0, 252, 255]) + b"abcXYZ",
        "stored_empty": bytes([1, 0, 0, 255, 255]),
        "fixed_A": fixed(A),
        "fixed_286": fixed([("l", 65), ("l", 286), ("l", 256)]),
        "fixed_287": fixed([("l", 65), ("l", 287), ("l", 256)]),
        "fixed_dist30": fixed([("l", 65), ("l", 257), ("d", 30), ("l", 256)]),
        "fixed_dist31": fixed([("l", 65), ("l", 257), ("d", 31), ("l", 256)]),
        "fixed_far": fixed([("l", 65), ("l", 257), ("d", 1), ("l", 256)]),
        "fixed_far_extra": fixed([("l", 65), ("l", 66), ("l", 257), ("d", 4, 1, 1), ("l", 256)]),
        "fixed_overlap": fixed([("l", 65), ("l", 66), ("l", 284, 30, 5), ("d", 1), ("l", 256)]),
        "fixed_first_match": fixed([("l", 257), ("d", 0), ("l", 256)]),
        "fixed_258": fixed([("l", 65), ("l", 285), ("d", 0), ("l", 256)]),
        "fixed_nonfinal": fixed(A, final=0),
        "dyn_two": dynamic(two, [1], A),
        "dyn_lit_incomplete": dynamic([8] * 256 + [8], [5] * 30, A),
        "dyn_lit_over": dynamic([8] * 256 + [9, 9], [1, 1], A),
        "dyn_lit_fixed286": dynamic(FIXED[:286], [5] * 30, A),
        "dyn_hlit30": dynamic(FIXED, [5] * 30, A),
        "dyn_hdist30": dynamic(two, [1] + [0] * 30, A),
        "dyn_hdist31": dynamic(two, [1] + [0] * 31, A),
        "dyn_hdist29": dynamic(two, [1] + [0] * 29, A),
        "dyn_dist_none": dynamic(two, [0], A),
        "dyn_dist_two": dynamic(two, [1, 1], A),
        "dyn_dist_single2": dynamic(two, [2], A),
        "dyn_dist_incomplete": dynamic(two, [1, 0, 2], A),
        "dyn_dist_over": dynamic(two, [1, 2, 2, 2], A),
        "dyn_end_only": dynamic([0] * 256 + [1], [1], [("l", 256)]),
        "dyn_end_only2": dynamic([0] * 256 + [2], [1], [("l", 256)]),
        "dyn_no_end": dynamic([0] * 65 + [1] + [0] * 191, [1], [("l", 65)]),
        "dyn_four": dynamic(four, [1], [("l", 65), ("l", 257), ("d", 0), ("l", 256)]),
        "dyn_rep16_first": dynamic(two, [1], A, rle=[(16, 2, 0)] + [(l, 0, 0) for l in (two + [1])[3:]]),
        "dyn_rep_past": dynamic(two, [1], A, rle=[(l, 0, 0) for l in two[:-1]] + [(1, 0, 0), (18, 7, 10)]),
        "dyn_clen_incomplete": dynamic(two, [1], A, clen=[2 if i in (0, 1) else 0 for i in range(19)]),
        "dyn_clen_over": dynamic(two, [1], A, clen=[1 if i in (0, 1, 2) else 0 for i in range(19)]),
        "dyn_clen_ok": dynamic(two, [1], A, clen=[1 if i in (0, 1) else 0 for i in range(19)]),
    }
    # a length code with no distance codes; an unused one-bit distance code
    for name, dl, bit in [("dyn_dist_none_used", [0], 0), ("dyn_dist_unused_bit", [1], 1), ("dyn_dist_used_bit", [1], 0)]:
        w = Bits()
        w.put(1, 1)
        w.put(2, 2)
        w.put(len(four) - 257, 5)
        w.put(0, 5)
        lens = four + dl
        clen = [0] * 19
        for s, l in complete(sorted(set(lens))).items():
            clen[s] = l
        w.put(15, 4)
        for i in range(19):
            w.put(clen[ORDER[i]], 3)
        cc = canon(clen)
        for s in lens:
            w.code(*cc[s])
        lc = canon(four)
        w.code(*lc[65])
        w.code(*lc[257])
        w.put(bit, 1)
        w.code(*lc[256])
        out[name] = w.bytes()
    # a single literal/length code (256 only, one bit) followed by its
    # unused code
    w = Bits()
    w.put(1, 1)
    w.put(2, 2)
    w.put(0, 5)
    w.put(0, 5)
    w.put(15, 4)
    clen = [0] * 19
    clen[0] = clen[1] = 1
    for i in range(19):
        w.put(clen[ORDER[i]], 3)
    for s in [0] * 256 + [1, 1]:
        w.put(s, 1)
    w.put(1, 1)
    out["dyn_lit_unused_bit"] = w.bytes() + b"\0\0"
    return out


def inputs(rng):
    words = [b"deflate ", b"inflate ", b"huffman ", b"window ", b"block ", b"lz77 ", b"zlib\n", b"gzip, "]
    text = lambda n: b"".join(rng.choice(words) for _ in range(n))
    docs = b""
    for f in ["CONVENTIONS.md", "AGENTS.md", "REVIEW.md", "README.md"]:
        p = os.path.join(ROOT, f)
        if os.path.exists(p):
            docs += open(p, "rb").read()
    runs = b"".join(bytes([rng.randrange(256)]) * k for k in [1, 2, 3, 4, 5, 257, 258, 259, 300, 600, 1000])
    return [
        ("empty", b""),
        ("one", b"x"),
        ("hello", b"hello, hello, hello, deflate!\n"),
        ("words", text(800)),
        ("prose", docs[:20000]),
        ("runs", runs),
        ("zeros", bytes(70000)),
        ("random", bytes(rng.randrange(256) for _ in range(4000))),
        ("all256", bytes(range(256)) * 3),
        ("twobytes", bytes(rng.choice(b"ab") for _ in range(3000))),
        ("mixed", text(200) + bytes(rng.randrange(256) for _ in range(700)) + bytes(900) + text(200)),
        ("far", text(300) + bytes(rng.randrange(256) for _ in range(33000)) + text(300)),
    ]


def big_inputs(rng):
    docs = b""
    for d in sorted(os.listdir(ROOT)):
        p = os.path.join(ROOT, d, "README.md")
        if os.path.exists(p):
            docs += open(p, "rb").read()
    return [("bigtext", docs[:150000])]


def zcompress(data, fmt, level=6, strategy=0, wbits=15, mem=8):
    w = {"raw": -wbits, "zlib": wbits, "gzip": 16 + wbits}[fmt]
    c = zlib.compressobj(level, zlib.DEFLATED, w, mem, strategy)
    return c.compress(data) + c.flush()


def tool_gzip(data, level):
    return subprocess.run([TOOL, "-%d" % level, "-c", "-n"], input=data, capture_output=True, check=True).stdout


def judge(stream, fmt):
    """The expected runner line's tail: 'LEN CRC' or 'error'."""
    if fmt == "g":
        if TOOL:
            p = subprocess.run([TOOL, "-dc"], input=stream, capture_output=True)
            if p.returncode not in (0, 2):
                return "error"
            out = p.stdout
        else:
            try:
                out = gzip.decompress(stream)
            except Exception:
                return "error"
    else:
        try:
            out = zlib.decompress(stream, -15 if fmt == "r" else 15)
        except Exception:
            return "error"
    return "%d %d" % (len(out), binascii.crc32(out))


def damage(rng, s):
    """Damaged copies of s."""
    out = []
    if not s:
        return out
    for _ in range(2):
        i = rng.randrange(len(s))
        out.append(("flip", s[:i] + bytes([s[i] ^ (1 << rng.randrange(8))]) + s[i + 1:]))
    i = rng.randrange(len(s))
    out.append(("byte", s[:i] + bytes([rng.randrange(256)]) + s[i + 1:]))
    i = rng.randrange(len(s))
    out.append(("zero", s[:i] + b"\0" + s[i + 1:]))
    i = rng.randrange(len(s))
    out.append(("del", s[:i] + s[i + rng.randrange(1, 4):]))
    i = rng.randrange(len(s) + 1)
    out.append(("ins", s[:i] + bytes(rng.randrange(256) for _ in range(rng.randrange(1, 4))) + s[i:]))
    out.append(("cut", s[:rng.randrange(len(s))]))
    return out


def main(seed):
    rng = random.Random(seed)
    os.makedirs(WORK, exist_ok=True)
    for f in os.listdir(WORK):
        os.remove(os.path.join(WORK, f))
    args, expect = [], []
    count = [0]

    def write(name, data):
        path = os.path.join("work", name + ".in")
        with open(os.path.join(HERE, path), "wb") as f:
            f.write(data)
        return path

    def dec(name, stream, fmt, pieces=False):
        path = write(name, stream)
        want = judge(stream, fmt)
        args.extend(["d" + fmt, path, name])
        expect.append(name + " " + want)
        if pieces:
            args.extend(["p" + fmt, path, name + "~p"])
            expect.append(name + "~p " + want)
        count[0] += 1

    words = {"d": "lv", "f": "fast", "r": "rle", "h": "huff", "F": "fixed", "D": "dyn", "S": "stored", "s": "stream"}

    def comp(name, data, fmt, strat, level):
        name = "c_%s_%s_%s%d" % (name, fmt, words[strat], level)
        path = write(name, data)
        args.extend(["c" + fmt + strat + str(level), path, "work/" + name])
        expect.append("work/" + name + " written")
        count[0] += 1

    ins = inputs(rng)
    streams = []
    # decoding: zlib's streams
    for name, data in ins:
        for lv in range(10):
            for fmt in ("raw", "zlib", "gzip"):
                if name in ("prose", "words", "mixed", "far", "random") or lv in (0, 1, 6, 9):
                    s = zcompress(data, fmt, lv)
                    dec("z_%s_%s_%d" % (name, fmt, lv), s, fmt[0], pieces=(lv in (1, 9) and fmt == "raw") or lv == 6)
                    streams.append((fmt[0], s))
        for st in range(1, 5):
            for lv in (1, 6, 9):
                s = zcompress(data, "raw", lv, st)
                dec("z_%s_raw_%d_s%d" % (name, lv, st), s, "r", pieces=(lv == 6))
                streams.append(("r", s))
    for name in ("prose", "far"):
        data = dict(ins)[name]
        for wb in range(9, 16):
            dec("z_%s_w%d" % (name, wb), zcompress(data, "zlib", 9, 0, wb), "z")
        for mem in (1, 9):
            dec("z_%s_m%d" % (name, mem), zcompress(data, "raw", 6, 0, 15, mem), "r")
    # decoding: the gzip tool's files, several members, trailing bytes
    if TOOL:
        for name, data in ins:
            for lv in (1, 6, 9):
                s = tool_gzip(data, lv)
                dec("t_%s_%d" % (name, lv), s, "g", pieces=(lv == 6))
                streams.append(("g", s))
    g1 = gzip.compress(b"hello gzip\n", mtime=0)
    g2 = gzip.compress(dict(ins)["words"], mtime=0)
    for tname, tail in [("two", g2), ("zeros", bytes(5)), ("zero1", b"\0"), ("garbage", b"garbage"),
                        ("one", b"A"), ("magic1", b"\x1f"), ("magic2", b"\x1f\x8b"), ("zero_garbage", b"\0A"),
                        ("badmember", b"\x1f\x8b\x07" + bytes(20)), ("partial", g2[:15])]:
        dec("gz_trail_" + tname, g1 + tail, "g", pieces=True)
    h = bytearray(g1[:10])
    h[3] = 2
    c16 = binascii.crc32(bytes(h)) & 0xFFFF
    gzhdr = {
        "fhcrc": bytes(h) + bytes([c16 & 255, c16 >> 8]) + g1[10:],
        "fhcrc_bad": bytes(h) + bytes([(c16 & 255) ^ 1, c16 >> 8]) + g1[10:],
        "fname": bytes(g1[:3]) + bytes([8]) + g1[4:10] + b"name.txt\0" + g1[10:],
        "fcomment": bytes(g1[:3]) + bytes([16]) + g1[4:10] + b"a comment\0" + g1[10:],
        "fextra": bytes(g1[:3]) + bytes([4]) + g1[4:10] + bytes([4, 0]) + b"AB\0\0" + g1[10:],
        "fextra_short": bytes(g1[:3]) + bytes([4]) + g1[4:10] + bytes([200, 0]) + b"AB",
        "fname_unterminated": bytes(g1[:3]) + bytes([8]) + g1[4:10] + b"name",
        "reserved": bytes(g1[:3]) + bytes([32]) + g1[4:],
        "method7": bytes(g1[:2]) + bytes([7]) + g1[3:],
        "badmagic": b"\x1f\x8c" + g1[2:],
        "empty": b"",
        "one": b"\x1f",
        "badcrc": g1[:-8] + bytes([g1[-8] ^ 1]) + g1[-7:],
        "badsize": g1[:-1] + bytes([g1[-1] ^ 1]),
        "header_only": g1[:10],
    }
    for k, v in gzhdr.items():
        dec("gz_" + k, v, "g", pieces=True)
    zgood = zlib.compress(b"hello hello zlib")

    def zhdr(cmf, flevel=2, fdict=0):
        flg = (flevel << 6) | (fdict << 5)
        flg += (31 - (cmf * 256 + flg) % 31) % 31
        return bytes([cmf, flg])
    zhd = {
        "good": zgood,
        "trailing": zgood + b"xyz",
        "badadler": zgood[:-1] + bytes([zgood[-1] ^ 1]),
        "shortadler": zgood[:-1],
        "noadler": zgood[:-4],
        "fdict": zhdr(0x78, 2, 1) + b"\0\0\0\1" + zgood[2:],
        "badfcheck": bytes([0x78, 0x9D]) + zgood[2:],
        "cm7": zhdr(0x77) + zgood[2:],
        "cm7_badfcheck": bytes([0x77, 0x9C]) + zgood[2:],
        "cinfo8": zhdr(0x88) + zgood[2:],
        "cinfo0": zhdr(0x08) + zgood[2:],
        "flevel0": zhdr(0x78, 0) + zgood[2:],
        "empty": b"",
        "onebyte": b"\x78",
        "headeronly": zgood[:2],
    }
    for k, v in zhd.items():
        dec("zl_" + k, v, "z", pieces=True)
    for k, v in handmade().items():
        dec("hm_" + k, v, "r", pieces=True)
        streams.append(("r", v))
    # damaged copies
    pick = [s for s in streams if len(s[1]) < 30000]
    rng.shuffle(pick)
    for i, (fmt, s) in enumerate(pick[:90]):
        for j, (kind, d) in enumerate(damage(rng, s)):
            dec("bad%d_%s_%s%d" % (i, fmt, kind, j), d, fmt, pieces=(i % 3 == 0))
    # encoding
    for name, data in ins + big_inputs(rng):
        lvs = range(10) if name not in ("bigtext",) else (1, 6, 9)
        for lv in lvs:
            comp(name, data, "r", "d", lv)
        if name == "bigtext":
            continue
        for st in "frhFDS":
            comp(name, data, "r", st, 6)
        for lv in (1, 6, 9):
            comp(name, data, "r", "s", lv)
        for fmt in "zg":
            for lv in (0, 1, 6, 9):
                comp(name, data, fmt, "d", lv)
            comp(name, data, fmt, "s", 6)
    with open(os.path.join(HERE, "args.txt"), "w") as f:
        f.write("\n".join(args) + "\n")
    with open(os.path.join(HERE, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(count[0])


def fallback(data):
    out = b""
    i = 0
    while i < len(data):
        n = min(255, len(data) - i)
        out += bytes([0, n, 0, 255 - n, 255]) + data[i:i + n]
        i += n
    return out + bytes([1, 0, 0, 255, 255])


def verify():
    args = open(os.path.join(HERE, "args.txt")).read().split("\n")
    cases = [args[i:i + 3] for i in range(0, len(args) - 2, 3)]
    n, sizes = 0, {}
    for act, path, name in cases:
        if not act.startswith("c"):
            continue
        fmt, strat, lv = act[1], act[2], int(act[3])
        data = open(os.path.join(HERE, path), "rb").read()
        out = open(os.path.join(HERE, name + ".out"), "rb").read()
        name = os.path.basename(name)
        if fmt == "r":
            got = zlib.decompress(out, -15)
            if out == fallback(data) and data:
                raise SystemExit("%s: the fallback was used" % name)
        elif fmt == "z":
            got = zlib.decompress(out)
        else:
            got = gzip.decompress(out)
            if TOOL:
                p = subprocess.run([TOOL, "-dc"], input=out, capture_output=True)
                if p.returncode != 0 or p.stdout != data:
                    raise SystemExit("%s: gzip -d does not give the input back" % name)
        if got != data:
            raise SystemExit("%s: does not decode back to its input" % name)
        if strat == "s":
            one = open(os.path.join(WORK, name.replace("_stream", "_lv") + ".out"), "rb").read()
            if one != out:
                raise SystemExit("%s: the streaming writer's stream differs" % name)
        if fmt == "r" and strat == "d":
            sizes[(name.split("_")[1], lv)] = (len(data), len(out), len(zcompress(data, "raw", lv)))
        n += 1
    lines = []
    for inp in ("prose", "words", "bigtext"):
        row = []
        for lv in (1, 6, 9):
            if (inp, lv) in sizes:
                d, ours, theirs = sizes[(inp, lv)]
                row.append("L%d %d/%d" % (lv, ours, theirs))
        if row:
            lines.append("%s %d bytes (ours/zlib): %s" % (inp, sizes[(inp, 6)][0], ", ".join(row)))
    print("%d compressed streams decode back; %s" % (n, "; ".join(lines)))


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "verify":
        verify()
    else:
        main(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
