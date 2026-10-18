#!/usr/bin/env python3
"""Differential test cases for bend-osdev-zstd.

Python's standard library has no Zstandard, so the independent
implementation is zstdref.py, written here from RFC 8878 (it shares an
author with the package: a second reading of the same document). The
reference library, libzstd, is the independent check when it is installed
(it is called through ctypes, as a black box), and so is the zstd tool.

  gen.py [SEED]      writes ref/cases.bin (the decoding cases, records that
                     ref/cases.bend reads and answers) and ref/expected.txt
                     (the answers expected), and ref/ccases.bin and
                     ref/ccases.json (the compression cases); prints a
                     summary
  gen.py edges       prints each hand-built frame's answer, zstdref.py's
                     (the package's) and libzstd's: the experiments behind
                     the README's choices
  gen.py verify OUT  checks OUT, cases.bend's output on ccases.bin: every
                     frame must decode back to its input with zstdref.py,
                     with libzstd and with zstd -d

Decoding cases:
  * frames libzstd writes (levels -5 to 19, with and without checksums, with
    dictionaries it trains and raw-content dictionaries), and frames the
    zstd tool writes, when they are installed;
  * frames zstdref.py writes, over every part of the format: raw, RLE and
    compressed blocks; raw, RLE, Huffman (1 and 4 streams, direct and
    FSE-coded weights) and treeless literals; predefined, RLE,
    FSE-compressed and repeated sequence tables; window descriptors,
    content sizes, checksums, dictionary IDs, skippable frames, several
    frames in a stream;
  * frames written byte by byte from RFC 8878's descriptions (gen.py's
    hand-built frames, below), among them every failure the package names;
  * corruptions of the above: bytes changed, deleted, inserted or cut off;
    the package must answer what zstdref.py answers, the same bytes or the
    same failure;
  * output limits one byte short of the content.
"""
import ctypes, json, os, random, shutil, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import zstdref as Z  # noqa: E402

# libzstd, through ctypes (a black box: its documented API only)


class Lib:
    def __init__(self):
        self.lib = None
        for name in ("libzstd.so.1", "libzstd.so", "libzstd.dylib"):
            try:
                self.lib = ctypes.CDLL(name)
                break
            except OSError:
                pass
        if self.lib is None:
            return
        L, sz, vp, ci = self.lib, ctypes.c_size_t, ctypes.c_void_p, ctypes.c_int
        for fn, res, args in [
            ("ZSTD_compressBound", sz, [sz]), ("ZSTD_isError", ctypes.c_uint, [sz]),
            ("ZSTD_getErrorName", ctypes.c_char_p, [sz]), ("ZSTD_createCCtx", vp, []),
            ("ZSTD_createDCtx", vp, []), ("ZSTD_freeCCtx", sz, [vp]), ("ZSTD_freeDCtx", sz, [vp]),
            ("ZSTD_CCtx_setParameter", sz, [vp, ci, ci]), ("ZSTD_DCtx_setParameter", sz, [vp, ci, ci]),
            ("ZSTD_compress2", sz, [vp, vp, sz, vp, sz]), ("ZSTD_decompressDCtx", sz, [vp, vp, sz, vp, sz]),
            ("ZSTD_CCtx_loadDictionary", sz, [vp, vp, sz]), ("ZSTD_DCtx_loadDictionary", sz, [vp, vp, sz]),
            ("ZSTD_versionString", ctypes.c_char_p, []), ("ZDICT_isError", ctypes.c_uint, [sz]),
            ("ZDICT_trainFromBuffer", sz, [vp, sz, vp, vp, ctypes.c_uint])]:
            f = getattr(L, fn)
            f.restype, f.argtypes = res, args

    def ok(self):
        return self.lib is not None

    def version(self):
        return self.lib.ZSTD_versionString().decode()

    def _check(self, r):
        if self.lib.ZSTD_isError(r):
            raise RuntimeError(self.lib.ZSTD_getErrorName(r).decode())
        return r

    def compress(self, data, level=3, checksum=1, wlog=0, dict_=None):
        L = self.lib
        c = L.ZSTD_createCCtx()
        try:
            # ZSTD_c_compressionLevel 100, ZSTD_c_windowLog 101,
            # ZSTD_c_contentSizeFlag 200, ZSTD_c_checksumFlag 201
            for k, v in [(100, level), (201, checksum), (200, 1)] + ([(101, wlog)] if wlog else []):
                self._check(L.ZSTD_CCtx_setParameter(c, k, v))
            if dict_:
                self._check(L.ZSTD_CCtx_loadDictionary(c, dict_, len(dict_)))
            cap = L.ZSTD_compressBound(len(data))
            buf = ctypes.create_string_buffer(cap)
            r = self._check(L.ZSTD_compress2(c, buf, cap, data, len(data)))
            return buf.raw[:r]
        finally:
            L.ZSTD_freeCCtx(c)

    def decompress(self, data, cap, dict_=None):
        """the content, or None if libzstd refuses the frame"""
        L = self.lib
        d = L.ZSTD_createDCtx()
        try:
            L.ZSTD_DCtx_setParameter(d, 100, 31)   # ZSTD_d_windowLogMax
            if dict_:
                self._check(L.ZSTD_DCtx_loadDictionary(d, dict_, len(dict_)))
            buf = ctypes.create_string_buffer(max(cap, 1))
            r = L.ZSTD_decompressDCtx(d, buf, max(cap, 1), data, len(data))
            return None if L.ZSTD_isError(r) else buf.raw[:r]
        finally:
            L.ZSTD_freeDCtx(d)

    def train(self, samples, size):
        blob = b"".join(samples)
        sizes = (ctypes.c_size_t * len(samples))(*[len(s) for s in samples])
        buf = ctypes.create_string_buffer(size)
        r = self.lib.ZDICT_trainFromBuffer(buf, size, blob, sizes, len(samples))
        return None if self.lib.ZDICT_isError(r) else buf.raw[:r]


def tool(args, data):
    """the zstd tool's output on data, or None"""
    if not shutil.which("zstd"):
        return None
    r = subprocess.run(["zstd", "-q", "-c"] + args, input=data, capture_output=True)
    return r.stdout if r.returncode == 0 else None

# Inputs


def corpus():
    """text from this repository's documents (its own, so stable)"""
    root = os.path.dirname(os.path.dirname(HERE))
    out = b""
    for name in ("README.md", "CONVENTIONS.md", "AGENTS.md", "REVIEW.md"):
        p = os.path.join(root, name)
        if os.path.exists(p):
            out += open(p, "rb").read()
    return out or bytes(range(256)) * 64


def inputs(rng, text, n, top):
    for _ in range(n):
        size = rng.choice([0, 1, 2, 7, 30, 100, 400, 1500, 5000, top])
        kind = rng.randrange(5)
        if kind == 0:
            yield bytes(rng.randrange(256) for _ in range(size))
        elif kind == 1:
            s = rng.randrange(max(1, len(text) - size))
            yield (text * (1 + size // max(1, len(text))))[s:s + size]
        elif kind == 2:
            yield bytes(rng.choice(b"abcde") for _ in range(size))
        elif kind == 3:
            unit = bytes(rng.randrange(256) for _ in range(rng.randrange(1, 40)))
            yield (unit * (size // len(unit) + 1))[:size]
        else:
            yield bytes([rng.randrange(256)]) * size

# The case files: records ref/cases.bend reads (see its header)


def le32(n):
    return n.to_bytes(4, "little")


def answer(data=None, err=None):
    if err is not None:
        return "ERR " + err
    return "%d %016x" % (len(data), Z.xxh64(data))


class Cases:
    def __init__(self):
        self.recs, self.expect = [], []

    def add(self, name, frame, want, limit=64 << 20, dict_=b"", verify=True):
        self.recs.append(bytes([0, 0 if limit is None else 1]) + le32(limit or 0) + bytes([1 if verify else 0])
                         + le32(len(dict_)) + dict_ + le32(len(frame)) + frame)
        self.expect.append((name, want))

    def write(self, path):
        with open(path, "wb") as fh:
            fh.write(b"".join(self.recs))
        return ["%d %s" % (k, want) for k, (name, want) in enumerate(self.expect)]


def compression_cases(rng, text):
    """(name, data, options) for the compressor"""
    out = []
    for k, data in enumerate(inputs(rng, text, 100, 30000)):
        bs, ck, m = 131072, True, True
        r = rng.random()
        if r < 0.2:
            bs = rng.choice([1, 100, 1000, 4096])
        elif r < 0.3:
            ck = False
        elif r < 0.4:
            m = False
        out.append(("c%d" % k, data, (bs, ck, m)))
    return out


def write_ccases(cc):
    with open(os.path.join(HERE, "ccases.bin"), "wb") as fh:
        for name, data, (bs, ck, m) in cc:
            fh.write(bytes([1]) + le32(bs) + bytes([int(ck), int(m)]) + le32(len(data)) + data)
    with open(os.path.join(HERE, "ccases.json"), "w") as fh:
        json.dump([[name, data.hex()] for name, data, _ in cc], fh)


def verify(path):
    """check the package's compressed frames (the ccases output in path)"""
    lib = Lib()
    want = {str(k): bytes.fromhex(h) for k, (name, h) in enumerate(json.load(open(os.path.join(HERE, "ccases.json"))))}
    seen, bad, total_in, total_out, fallback = 0, 0, 0, 0, 0
    for line in open(path):
        parts = line.split()
        if len(parts) != 3 or parts[0] not in want:
            print("unexpected line:", line[:200].rstrip())
            bad += 1
            continue
        name, hexframe, same = parts
        data, frame = want[name], bytes.fromhex(hexframe)
        seen += 1
        total_in += len(data)
        total_out += len(frame)
        if same != "True":
            fallback += 1
            print(name, "fell back to raw blocks")
            bad += 1
        try:
            got = Z.decompress(frame, max_out=1 << 30)
        except Z.ZstdError as e:
            got = "error " + e.kind
        if got != data:
            print(name, "zstdref.py:", got if isinstance(got, str) else "%d bytes" % len(got))
            bad += 1
        if lib.ok() and lib.decompress(frame, len(data)) != data:
            print(name, "libzstd does not give it back")
            bad += 1
        t = tool(["-d"], frame)
        if shutil.which("zstd") and t != data:
            print(name, "zstd -d does not give it back")
            bad += 1
    if seen != len(want):
        print("%d of %d frames" % (seen, len(want)))
        bad += 1
    print("%d compressed frames decode back (%d to %d bytes)%s" % (seen, total_in, total_out, "" if not bad else ", %d problems" % bad))
    return 1 if bad else 0


def ref_answer(frame, limit=64 << 20, dict_=b"", verify=True):
    try:
        return answer(Z.decompress(frame, max_out=limit if limit is not None else 1 << 62, dict_bytes=dict_, verify=verify))
    except Z.ZstdError as e:
        return answer(err=e.kind)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    rng = random.Random(seed)
    lib = Lib()
    text = corpus()
    cases = Cases()
    count = {"lib": 0, "tool": 0, "ref": 0, "hand": 0, "corrupt": 0, "limit": 0}
    pool = []   # (frame, dict) pairs to corrupt

    def add(kind, frame, data, dict_=b""):
        want = ref_answer(frame, dict_=dict_)
        assert want == answer(data), "zstdref.py disagrees on a %s frame" % kind
        cases.add("%s%d" % (kind, count[kind]), frame, want, dict_=dict_)
        count[kind] += 1
        pool.append((frame, dict_))

    # frames libzstd writes
    if lib.ok():
        samples = [text[s:s + rng.randrange(40, 300)] for s in (rng.randrange(len(text) - 300) for _ in range(200))]
        trained = lib.train(samples, 4096)
        for data in inputs(rng, text, 120, 40000):
            level = rng.choice([-5, -1, 1, 3, 5, 9, 15, 19])
            dict_ = b""
            r = rng.random()
            if r < 0.15 and trained:
                dict_ = trained
            elif r < 0.25:
                dict_ = text[:rng.randrange(100, 3000)]
            frame = lib.compress(data, level=level, checksum=rng.randrange(2), dict_=dict_)
            back = lib.decompress(frame, len(data), dict_)
            assert back == data, (len(data), level, len(dict_), back if back is None else len(back))
            add("lib", frame, data, dict_)
    # frames the zstd tool writes
    for data in inputs(rng, text, 10, 20000):
        frame = tool([rng.choice(["-1", "-3", "-19", "--fast=3"])], data)
        if frame is None:
            break
        add("tool", frame, data)
    # frames zstdref.py writes
    for data in inputs(rng, text, 160, 20000):
        kw = {}
        if rng.random() < 0.4:
            kw["window_desc"] = rng.choice([0, 3, 8, 13, 7 << 3])
            kw["content_size"] = rng.random() < 0.5
        if rng.random() < 0.4:
            kw["block_size"] = rng.choice([50, 700, 3000])
        dict_ = b""
        if rng.random() < 0.2:
            dict_ = text[:rng.randrange(50, 2000)]
        frame = Z.compress_frame(data, rng, checksum=rng.random() < 0.6, dict_bytes=dict_, **kw)
        if rng.random() < 0.2:
            frame = Z.skippable(rng.randrange(20), rng.randrange(16)) + frame
        if rng.random() < 0.2:
            more = next(inputs(rng, text, 1, 3000))
            frame += Z.compress_frame(more, rng, dict_bytes=dict_)
            data += more
        add("ref", frame, data, dict_)
    # hand-built frames
    for name, frame, dict_ in hand_frames(rng):
        cases.add("hand%d" % count["hand"], frame, ref_answer(frame, dict_=dict_), dict_=dict_)
        count["hand"] += 1
    # corruptions
    for k in range(400):
        frame, dict_ = rng.choice(pool)
        b = bytearray(frame)
        op = rng.randrange(4)
        if not b:
            continue
        i = rng.randrange(len(b))
        if op == 0:
            b[i] ^= 1 << rng.randrange(8)
        elif op == 1:
            del b[i]
        elif op == 2:
            b.insert(i, rng.randrange(256))
        else:
            del b[i:]
        cases.add("corrupt%d" % k, bytes(b), ref_answer(bytes(b), dict_=dict_), dict_=dict_)
        count["corrupt"] += 1
    # output limits: one byte short
    for k in range(20):
        frame, dict_ = rng.choice(pool)
        n = len(Z.decompress(frame, dict_bytes=dict_))
        if n == 0:
            continue
        cases.add("limit%d" % k, frame, ref_answer(frame, limit=n - 1, dict_=dict_), limit=n - 1, dict_=dict_)
        cases.add("limitok%d" % k, frame, ref_answer(frame, limit=n, dict_=dict_), limit=n, dict_=dict_)
        count["limit"] += 2
    cc = compression_cases(rng, text)
    write_ccases(cc)
    lines = cases.write(os.path.join(HERE, "cases.bin"))
    with open(os.path.join(HERE, "expected.txt"), "w") as fh:
        fh.write("\n".join(lines) + "\n")
    print("%d decoding cases (%s), %d compression cases%s" % (len(cases.expect), ", ".join("%s %d" % kv for kv in count.items()), len(cc),
          "; libzstd %s" % lib.version() if lib.ok() else "; libzstd missing"))


def hand_frames(rng):
    """Frames written byte by byte from RFC 8878's descriptions."""
    H = Z.frame_header
    B = Z.block_header
    out = []
    out.append(("empty input", b"", b""))
    out.append(("skippable only", Z.skippable(5), b""))
    out.append(("raw block", H(3, checksum=False) + B(1, 0, 3) + b"abc", b""))
    out.append(("trailing 2 bytes", H(3, checksum=False) + B(1, 0, 3) + b"abc" + b"\x01\x02", b""))
    out.append(("bad magic", b"\x01\x02\x03\x04" + b"abc", b""))
    out.append(("unused bit", H(3, checksum=False, unused_bit=True) + B(1, 0, 3) + b"abc", b""))
    out.append(("reserved bit", b"\x28\xb5\x2f\xfd\x28\x03" + B(1, 0, 3) + b"abc", b""))
    out.append(("block type 3", H(3, checksum=False) + B(1, 3, 3) + b"abc", b""))
    out.append(("rle block", H(5, checksum=True) + B(1, 1, 5) + b"z" + (Z.xxh64(b"zzzzz") & 0xFFFFFFFF).to_bytes(4, "little"), b""))
    out.append(("bad checksum", H(5, checksum=True) + B(1, 1, 5) + b"z" + b"\x00\x00\x00\x00", b""))
    out.append(("content size", H(4, checksum=False) + B(1, 0, 3) + b"abc", b""))
    out.append(("window 2^41", H(None, checksum=False, window_desc=31 << 3) + B(1, 0, 3) + b"abc", b""))
    out.append(("block too large", H(None, checksum=False, window_desc=0) + B(1, 0, 2000) + bytes(2000), b""))
    out.append(("dictionary id", H(3, checksum=False, dict_id=77) + B(1, 0, 3) + b"abc", b""))
    body = Z.lit_header_raw(0, 3) + b"abc" + b"\x00"
    out.append(("no sequences", H(None, checksum=False, window_desc=0) + B(1, 2, len(body)) + body, b""))
    body = Z.lit_header_raw(0, 3) + b"abc" + b"\x00\x05"
    out.append(("bytes after zero sequences", H(None, checksum=False, window_desc=0) + B(1, 2, len(body)) + body, b""))
    out.append(("comp block size 0", H(None, checksum=False, window_desc=0) + B(1, 2, 0), b""))
    seq = Z.seq_section([(2, 4, 4), (0, 3, 4)], {}, rng, {"ll": 0, "of": 0, "ml": 0})
    body = Z.lit_header_raw(0, 2) + b"qq" + seq
    out.append(("repeat offset 1 minus 1 is 0", H(None, checksum=False, window_desc=0) + B(1, 2, len(body)) + body, b""))
    seq = Z.seq_section([(5, 4, 4)], {}, rng, {"ll": 0, "of": 0, "ml": 0})
    body = Z.lit_header_raw(0, 2) + b"qq" + seq
    out.append(("literals exhausted", H(None, checksum=False, window_desc=0) + B(1, 2, len(body)) + body, b""))
    body = (3 | (3 << 4) | (2 << 14)).to_bytes(3, "little") + b"\x01\x01" + b"\x00"
    out.append(("treeless at start", H(None, checksum=False, window_desc=0) + B(1, 2, len(body)) + body, b""))
    body = Z.lit_header_raw(0, 0) + b"\x01" + bytes([3 << 6]) + b"\x01"
    out.append(("repeat mode at start", H(None, checksum=False, window_desc=0) + B(1, 2, len(body)) + body, b""))
    body = Z.lit_header_raw(0, 0) + b"\x01" + bytes([1]) + b"\x01"
    out.append(("modes reserved bits", H(None, checksum=False, window_desc=0) + B(1, 2, len(body)) + body, b""))
    body = Z.lit_header_raw(0, 10) + b"abc"
    out.append(("raw literals past the block", H(None, checksum=False, window_desc=0) + B(1, 2, len(body)) + body, b""))
    seq = Z.seq_section([(0, 1500 + 3, 10)], {}, rng, {"ll": 0, "of": 0, "ml": 0})
    body = Z.lit_header_raw(0, 0) + seq
    out.append(("offset past the window", H(None, checksum=False, window_desc=0) + B(0, 0, 1000) + bytes(range(256)) * 3 + bytes(232) + B(0, 0, 1000) + bytes(1000) + B(1, 2, len(body)) + body, b""))
    d = bytes(range(256)) * 8
    for back, name in ((1024 + 500 + 3, "dictionary within the window"), (2048 + 500 + 3, "dictionary start"), (2048 + 501 + 3, "before the dictionary")):
        seq = Z.seq_section([(0, back, 4)], {}, rng, {"ll": 0, "of": 0, "ml": 0})
        body = Z.lit_header_raw(0, 0) + seq
        out.append((name, H(None, checksum=False, window_desc=0) + B(0, 0, 500) + bytes(500) + B(1, 2, len(body)) + body, d))
    seq = Z.seq_section([(0, 1024 + 1500 + 3, 4)], {}, rng, {"ll": 0, "of": 0, "ml": 0})
    body = Z.lit_header_raw(0, 0) + seq
    out.append(("dictionary after the window", H(None, checksum=False, window_desc=0) + B(0, 0, 750) + bytes(750) + B(0, 0, 750) + bytes(750) + B(1, 2, len(body)) + body, d))
    for n in (3, 5, 6):
        lits = bytes(b"ab"[i % 2] for i in range(n))
        w, codes = Z.huf_build(lits)
        tree = Z.huf_tree_desc(w, rng, "direct")
        seg = (n + 3) // 4
        parts = [lits[0:seg], lits[seg:2 * seg], lits[2 * seg:3 * seg], lits[3 * seg:]]
        ss = [Z.huf_stream(codes, p) for p in parts]
        sb = tree + b"".join(len(s).to_bytes(2, "little") for s in ss[:3]) + b"".join(ss)
        body = (2 | (1 << 2) | (n << 4) | (len(sb) << 14)).to_bytes(3, "little") + sb + b"\x00"
        out.append(("4 streams of %d" % n, H(None, checksum=False, window_desc=0) + B(1, 2, len(body)) + body, b""))
    return out


def edges():
    """the experiments behind the README's choices: each hand-built frame,
    zstdref.py's answer (the package's) and libzstd's"""
    lib = Lib()
    for name, frame, dict_ in hand_frames(random.Random(2026)):
        mine = ref_answer(frame, dict_=dict_)
        if not lib.ok():
            theirs = "libzstd missing"
        else:
            back = lib.decompress(frame, 1 << 20, dict_)
            theirs = "refused" if back is None else "%d bytes" % len(back)
        print("%-30s %-28s libzstd: %s" % (name, mine, theirs))


if __name__ == "__main__":
    if len(sys.argv) > 2 and sys.argv[1] == "verify":
        sys.exit(verify(sys.argv[2]))
    if len(sys.argv) > 1 and sys.argv[1] == "edges":
        sys.exit(edges())
    main()
