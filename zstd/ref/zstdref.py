"""An independent Zstandard implementation, for bend-osdev-zstd's tests.

Written here from RFC 8878 ("Zstandard Compression and the
'application/zstd' Media Type", Y. Collet and M. Kucherawy, February 2021)
and the xxHash specification (xxhash_spec.md, XXH64), with no other
implementation's source read. It shares an author with the Bend package, so
it checks the package against a second reading of the same documents; the
reference library (libzstd, through ctypes) and the zstd tool, when present,
are the independent checks (see gen.py).

  decompress(src, max_out, dict_bytes, verify, max_window) -> bytes, or
  raises ZstdError(kind), kind naming the failure as the package does;
  compress_frame(data, ...) -> a frame, from a writer that exercises every
  part of the format (block types, literals types, 1 and 4 Huffman streams,
  direct and FSE-coded weights, treeless literals, every sequence mode).
"""

M64 = (1 << 64) - 1

# XXH64 (xxhash_spec.md)

XP1 = 0x9E3779B185EBCA87
XP2 = 0xC2B2AE3D27D4EB4F
XP3 = 0x165667B19E3779F9
XP4 = 0x85EBCA77C2B2AE63
XP5 = 0x27D4EB2F165667C5


def rotl64(x, r):
    return ((x << r) | (x >> (64 - r))) & M64


def xround(acc, lane):
    acc = (acc + lane * XP2) & M64
    return (rotl64(acc, 31) * XP1) & M64


def xmerge(acc, v):
    acc ^= xround(0, v)
    return (acc * XP1 + XP4) & M64


def xxh64(data, seed=0):
    n, i = len(data), 0
    if n >= 32:
        v = [(seed + XP1 + XP2) & M64, (seed + XP2) & M64, seed & M64, (seed - XP1) & M64]
        while i + 32 <= n:
            for k in range(4):
                v[k] = xround(v[k], int.from_bytes(data[i:i + 8], "little"))
                i += 8
        h = (rotl64(v[0], 1) + rotl64(v[1], 7) + rotl64(v[2], 12) + rotl64(v[3], 18)) & M64
        for k in range(4):
            h = xmerge(h, v[k])
    else:
        h = (seed + XP5) & M64
    h = (h + n) & M64
    while i + 8 <= n:
        h ^= xround(0, int.from_bytes(data[i:i + 8], "little"))
        h = (rotl64(h, 27) * XP1 + XP4) & M64
        i += 8
    if i + 4 <= n:
        h ^= (int.from_bytes(data[i:i + 4], "little") * XP1) & M64
        h = (rotl64(h, 23) * XP2 + XP3) & M64
        i += 4
    while i < n:
        h ^= (data[i] * XP5) & M64
        h = (rotl64(h, 11) * XP1) & M64
        i += 1
    h ^= h >> 33
    h = (h * XP2) & M64
    h ^= h >> 29
    h = (h * XP3) & M64
    h ^= h >> 32
    return h


assert xxh64(b"") == 0xEF46DB3751D8E999


class ZstdError(Exception):
    def __init__(self, kind):
        Exception.__init__(self, kind)
        self.kind = kind


def fail(kind):
    raise ZstdError(kind)


MAGIC = 0xFD2FB528
DICT_MAGIC = 0xEC30A437
BLOCK_MAX = 131072


def highbit(n):
    return n.bit_length() - 1

# Bitstreams


def backward_bits(stream, err):
    """The bits of a backward bitstream, in the order a decoder reads them:
    from the bit below the last byte's highest set bit (the end mark) down,
    then each earlier byte from its bit 7 to its bit 0."""
    if not stream or stream[-1] == 0:
        fail(err)
    last = stream[-1]
    bits = [(last >> k) & 1 for k in range(highbit(last) - 1, -1, -1)]
    for b in reversed(stream[:-1]):
        bits.extend((b >> k) & 1 for k in range(7, -1, -1))
    return bits


class BitReader:
    def __init__(self, bits, err):
        self.bits, self.pos, self.err = bits, 0, err

    def left(self):
        return len(self.bits) - self.pos

    def read(self, n):
        if n > self.left():
            fail(self.err)
        v = 0
        for _ in range(n):
            v = 2 * v + self.bits[self.pos]
            self.pos += 1
        return v


def pack_backward(fields):
    """A backward bitstream whose reader meets the fields (value, nbits) in
    order, each most significant bit first."""
    bits = []
    for v, n in fields:
        bits.extend((v >> k) & 1 for k in range(n - 1, -1, -1))
    fwd = list(reversed(bits)) + [1]
    while len(fwd) % 8:
        fwd.append(0)
    return bytes(sum(fwd[i + k] << k for k in range(8)) for i in range(0, len(fwd), 8))


class ForwardBits:
    """A little-endian bit reader over bytes (FSE table descriptions)."""

    def __init__(self, data, pos, err):
        self.data, self.bit, self.start, self.err = data, pos * 8, pos, err

    def read(self, n):
        v = 0
        for k in range(n):
            i = self.bit >> 3
            if i >= len(self.data):
                fail(self.err)
            v |= ((self.data[i] >> (self.bit & 7)) & 1) << k
            self.bit += 1
        return v

    def bytes_used(self):
        return (self.bit + 7) // 8 - self.start

# FSE (RFC 8878 section 4.1)


def fse_read(data, pos, max_al, max_sym, err):
    """A table description at data[pos:]: (probabilities, accuracy log,
    bytes used). A probability of -1 means "less than 1"."""
    r = ForwardBits(data, pos, err)
    al = r.read(4) + 5
    if al > max_al:
        fail(err)
    remaining = 1 << al
    probs = []
    while remaining > 0:
        if len(probs) > max_sym:
            fail(err)
        top = remaining + 1
        nb = top.bit_length()          # the least n with 2^n > top
        low = (1 << nb) - 1 - top
        v = r.read(nb - 1)
        if v >= low:
            v |= r.read(1) << (nb - 1)
            if v >= (1 << (nb - 1)):
                v -= low
        p = v - 1
        probs.append(p)
        remaining -= abs(p)
        if remaining < 0:
            fail(err)
        if p == 0:
            while True:
                rep = r.read(2)
                for _ in range(rep):
                    if len(probs) > max_sym:
                        fail(err)
                    probs.append(0)
                if rep < 3:
                    break
    if len(probs) > max_sym + 1:
        fail(err)
    return probs, al, r.bytes_used()


def fse_build(probs, al):
    """The decoding table: (symbol, number of bits, baseline) per state."""
    size = 1 << al
    sym = [0] * size
    high = size - 1
    for s, p in enumerate(probs):
        if p == -1:
            sym[high] = s
            high -= 1
    pos, step, mask = 0, (size >> 1) + (size >> 3) + 3, size - 1
    for s, p in enumerate(probs):
        for _ in range(max(p, 0)):
            sym[pos] = s
            pos = (pos + step) & mask
            while pos > high:
                pos = (pos + step) & mask
    nxt = [1 if p == -1 else max(p, 0) for p in probs]
    table = []
    for st in range(size):
        s = sym[st]
        x = nxt[s]
        nxt[s] += 1
        nb = al - highbit(x)
        table.append((s, nb, (x << nb) - size))
    return table


def fse_rle(sym):
    return [(sym, 0, 0)]


def table_al(t):
    return highbit(len(t))


LL_DEFAULT = [4, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 1, 1, 1, 1, 1, -1, -1, -1, -1]
ML_DEFAULT = [1, 4, 3, 2, 2, 2, 2, 2, 2] + [1] * 37 + [-1] * 7
OF_DEFAULT = [1, 1, 1, 1, 1, 1, 2, 2, 2] + [1] * 15 + [-1] * 5
assert sum(abs(p) for p in LL_DEFAULT) == 64 and len(LL_DEFAULT) == 36
assert sum(abs(p) for p in ML_DEFAULT) == 64 and len(ML_DEFAULT) == 53
assert sum(abs(p) for p in OF_DEFAULT) == 32 and len(OF_DEFAULT) == 29

LL_BASE = list(range(16)) + [16, 18, 20, 22, 24, 28, 32, 40, 48, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536]
LL_BITS = [0] * 16 + [1, 1, 1, 1, 2, 2, 3, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
ML_BASE = list(range(3, 35)) + [35, 37, 39, 41, 43, 47, 51, 59, 67, 83, 99, 131, 259, 515, 1027, 2051, 4099, 8195, 16387, 32771, 65539]
ML_BITS = [0] * 32 + [1, 1, 1, 1, 2, 2, 3, 3, 4, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16]
assert len(LL_BASE) == len(LL_BITS) == 36 and len(ML_BASE) == len(ML_BITS) == 53

# kind, accuracy log maximum, symbol maximum, predefined table
FIELDS = {"ll": (9, 35, LL_DEFAULT, 6), "of": (8, 31, OF_DEFAULT, 5), "ml": (9, 52, ML_DEFAULT, 6)}

# Huffman (RFC 8878 section 4.2)


def fse_weights(data, err):
    """Huffman weights coded with FSE: two interleaved states."""
    probs, al, used = fse_read(data, 0, 6, 255, err)
    t = fse_build(probs, al)
    r = BitReader(backward_bits(data[used:], err), err)
    s1, s2 = r.read(al), r.read(al)
    out = []

    def emit(s):
        if len(out) >= 255:
            fail(err)
        out.append(t[s][0])

    while True:
        emit(s1)
        if r.left() < t[s1][1]:
            emit(s2)
            break
        s1 = t[s1][2] + r.read(t[s1][1])
        emit(s2)
        if r.left() < t[s2][1]:
            emit(s1)
            break
        s2 = t[s2][2] + r.read(t[s2][1])
    return out


def huf_read(data, pos):
    """A tree description at data[pos:]: (code table, bytes used). The
    table maps a code (value, length) to its symbol."""
    err = "BadHuffmanTree"
    if pos >= len(data):
        fail(err)
    h = data[pos]
    if h < 128:
        if pos + 1 + h > len(data):
            fail(err)
        weights = fse_weights(data[pos + 1:pos + 1 + h], err)
        used = 1 + h
    else:
        n = h - 127
        nbytes = (n + 1) // 2
        if pos + 1 + nbytes > len(data):
            fail(err)
        weights = []
        for i in range(n):
            b = data[pos + 1 + i // 2]
            weights.append(b >> 4 if i % 2 == 0 else b & 15)
        used = 1 + nbytes
    return huf_from_weights(weights, err), used


def huf_from_weights(weights, err="BadHuffmanTree"):
    if any(w > 11 for w in weights):
        fail(err)
    total = sum(1 << (w - 1) for w in weights if w > 0)
    if total == 0:
        fail(err)
    maxbits = highbit(total) + 1
    if maxbits > 11:
        fail(err)
    rest = (1 << maxbits) - total
    if rest & (rest - 1):
        fail(err)
    ws = list(weights) + [highbit(rest) + 1]
    return huf_codes(ws, maxbits)


def huf_codes(ws, maxbits):
    """symbol -> (code, length), from the weights, as RFC 8878 assigns
    them: by weight, lowest first, then by symbol."""
    codes, start = {}, 0
    for w in range(1, maxbits + 1):
        for s, ws_ in enumerate(ws):
            if ws_ == w:
                nb = maxbits + 1 - w
                codes[s] = (start >> (w - 1), nb)
                start += 1 << (w - 1)
    assert start == 1 << maxbits
    return codes


def huf_decode_stream(codes, stream, count):
    err = "BadHuffmanStream"
    bits = backward_bits(stream, err)
    lookup = {(c, n): s for s, (c, n) in codes.items()}
    maxbits = max(n for _, n in codes.values())
    out, pos = [], 0
    for _ in range(count):
        v, n = 0, 0
        while True:
            if pos >= len(bits) or n >= maxbits:
                fail(err)
            v = 2 * v + bits[pos]
            pos += 1
            n += 1
            if (v, n) in lookup:
                out.append(lookup[(v, n)])
                break
    if pos != len(bits):
        fail(err)
    return out

# Literals (RFC 8878 section 3.1.1.3.1)


def literals(block, st, block_max):
    err = "BadLiteralsHeader"
    if not block:
        fail(err)
    b0 = block[0]
    kind, sf = b0 & 3, (b0 >> 2) & 3
    if kind in (0, 1):
        if sf in (0, 2):
            hl, regen = 1, b0 >> 3
        elif sf == 1:
            if len(block) < 2:
                fail(err)
            hl, regen = 2, (b0 >> 4) + (block[1] << 4)
        else:
            if len(block) < 3:
                fail(err)
            hl, regen = 3, (b0 >> 4) + (block[1] << 4) + (block[2] << 12)
        if regen > block_max:
            fail(err)
        if kind == 0:
            if hl + regen > len(block):
                fail(err)
            return list(block[hl:hl + regen]), hl + regen
        if hl + 1 > len(block):
            fail(err)
        return [block[hl]] * regen, hl + 1
    hl, bits = {0: (3, 10), 1: (3, 10), 2: (4, 14), 3: (5, 18)}[sf]
    if len(block) < hl:
        fail(err)
    v = int.from_bytes(block[:hl], "little") >> 4
    regen, comp = v & ((1 << bits) - 1), v >> bits
    if regen > block_max or hl + comp > len(block):
        fail(err)
    body = block[hl:hl + comp]
    if kind == 2:
        codes, used = huf_read(body, 0)
        st["huf"] = codes
        body = body[used:]
    else:
        if st["huf"] is None:
            fail("NoHuffmanTree")
        codes = st["huf"]
    if sf != 0 and regen < 6:
        fail(err)
    if sf == 0:
        out = huf_decode_stream(codes, body, regen)
    else:
        e = "BadHuffmanStream"
        if len(body) < 6:
            fail(e)
        s1, s2, s3 = (int.from_bytes(body[k:k + 2], "little") for k in (0, 2, 4))
        s4 = len(body) - 6 - s1 - s2 - s3
        seg = (regen + 3) // 4
        if s4 < 0 or 3 * seg > regen:
            fail(e)
        p, out = 6, []
        for size, count in ((s1, seg), (s2, seg), (s3, seg), (s4, regen - 3 * seg)):
            out += huf_decode_stream(codes, body[p:p + size], count)
            p += size
    return out, hl + comp

# Sequences (RFC 8878 section 3.1.1.3.2)


def seq_table(block, pos, field, mode, st):
    max_al, max_sym, default, dal = FIELDS[field]
    if mode == 0:
        t = fse_build(default, dal)
    elif mode == 1:
        if pos >= len(block):
            fail("BadSequencesHeader")
        if block[pos] > max_sym:
            fail("BadFseTable")
        t = fse_rle(block[pos])
        pos += 1
    elif mode == 2:
        probs, al, used = fse_read(block, pos, max_al, max_sym, "BadFseTable")
        t = fse_build(probs, al)
        pos += used
    else:
        if st[field] is None:
            fail("NoFseTable")
        t = st[field]
    st[field] = t
    return t, pos


def sequences(block, st):
    """The sequences of the section block[0:]: (ll, offset value, ml)."""
    err = "BadSequencesHeader"
    if not block:
        fail(err)
    b0 = block[0]
    if b0 == 0:
        if len(block) != 1:
            fail(err)
        return []
    if b0 < 128:
        n, pos = b0, 1
    elif b0 < 255:
        if len(block) < 2:
            fail(err)
        n, pos = ((b0 - 128) << 8) + block[1], 2
    else:
        if len(block) < 3:
            fail(err)
        n, pos = block[1] + (block[2] << 8) + 0x7F00, 3
    if pos >= len(block):
        fail(err)
    modes = block[pos]
    pos += 1
    if modes & 3:
        fail(err)
    tll, pos = seq_table(block, pos, "ll", modes >> 6, st)
    tof, pos = seq_table(block, pos, "of", (modes >> 4) & 3, st)
    tml, pos = seq_table(block, pos, "ml", (modes >> 2) & 3, st)
    e = "BadSequenceStream"
    r = BitReader(backward_bits(block[pos:], e), e)
    sll, sof, sml = r.read(table_al(tll)), r.read(table_al(tof)), r.read(table_al(tml))
    out = []
    for i in range(n):
        llc, ofc, mlc = tll[sll][0], tof[sof][0], tml[sml][0]
        ofv = (1 << ofc) + r.read(ofc)
        ml = ML_BASE[mlc] + r.read(ML_BITS[mlc])
        ll = LL_BASE[llc] + r.read(LL_BITS[llc])
        out.append((ll, ofv, ml))
        if i < n - 1:
            sll = tll[sll][2] + r.read(tll[sll][1])
            sml = tml[sml][2] + r.read(tml[sml][1])
            sof = tof[sof][2] + r.read(tof[sof][1])
    if r.left():
        fail(e)
    return out

# Blocks and frames


class Frame:
    pass


def execute(seqs, lits, f, block_max):
    """Run the sequences: the block's bytes, appended to f.out."""
    out, start = f.out, len(f.out)
    li = 0
    for ll, ofv, ml in seqs:
        if ll > len(lits) - li:
            fail("LiteralsExhausted")
        out.extend(lits[li:li + ll])
        li += ll
        if len(out) - start > block_max:
            fail("BlockTooLarge")
        rep = f.rep
        if ofv > 3:
            off = ofv - 3
            f.rep = [off, rep[0], rep[1]]
        else:
            k = ofv - 1 if ll > 0 else ofv
            if k == 0:
                off = rep[0]
            elif k == 1:
                off = rep[1]
                f.rep = [rep[1], rep[0], rep[2]]
            elif k == 2:
                off = rep[2]
                f.rep = [rep[2], rep[0], rep[1]]
            else:
                off = rep[0] - 1
                f.rep = [off, rep[0], rep[1]]
        p = len(out) - f.base
        limit = p + len(f.dict) if p <= f.window else f.window
        if off == 0 or off > limit:
            fail("BadOffset")
        if len(out) - start + ml > block_max:
            fail("BlockTooLarge")
        for _ in range(ml):
            q = len(out) - off
            out.append(out[q] if q >= f.base else f.dict[len(f.dict) - (f.base - q)])
    out.extend(lits[li:])
    if len(out) - start > block_max:
        fail("BlockTooLarge")


def parse_dict(d):
    """(id, content, entropy state or None)."""
    if len(d) < 8 or int.from_bytes(d[:4], "little") != DICT_MAGIC:
        return 0, list(d), None
    err = "BadDictionary"
    did = int.from_bytes(d[4:8], "little")
    try:
        codes, used = huf_read(d, 8)
        pos = 8 + used
        tabs = {}
        for field in ("of", "ml", "ll"):
            max_al, max_sym, _, _ = FIELDS[field]
            probs, al, used = fse_read(d, pos, max_al, max_sym, err)
            tabs[field] = fse_build(probs, al)
            pos += used
    except ZstdError:
        fail(err)
    if pos + 12 > len(d):
        fail(err)
    rep = [int.from_bytes(d[pos + 4 * k:pos + 4 * k + 4], "little") for k in range(3)]
    content = list(d[pos + 12:])
    if any(r == 0 or r > len(content) for r in rep):
        fail(err)
    return did, content, {"huf": codes, "ll": tabs["ll"], "of": tabs["of"], "ml": tabs["ml"], "rep": rep}


def decompress(src, max_out=64 << 20, dict_bytes=b"", verify=True, max_window=1 << 27):
    """The content of the stream src: one frame or more, zstd and
    skippable, back to back."""
    did, dcontent, dent = parse_dict(dict_bytes)
    out, pos, frames = [], 0, 0
    n = len(src)
    while True:
        if pos == n:
            break
        if n - pos < 4:
            fail("Truncated")
        magic = int.from_bytes(src[pos:pos + 4], "little")
        pos += 4
        frames += 1
        if magic & 0xFFFFFFF0 == 0x184D2A50:
            if n - pos < 4:
                fail("Truncated")
            size = int.from_bytes(src[pos:pos + 4], "little")
            pos += 4
            if n - pos < size:
                fail("Truncated")
            pos += size
            continue
        if magic != MAGIC:
            fail("BadMagic")
        pos = frame(src, pos, out, max_out, did, dcontent, dent, verify, max_window)
    return bytes(out)


def frame(src, pos, out, max_out, did, dcontent, dent, verify, max_window):
    n = len(src)
    if pos >= n:
        fail("Truncated")
    fhd = src[pos]
    if fhd & 8:
        fail("ReservedBit")
    single = (fhd >> 5) & 1
    fcs_size = {0: 1 if single else 0, 1: 2, 2: 4, 3: 8}[fhd >> 6]
    did_size = {0: 0, 1: 1, 2: 2, 3: 4}[fhd & 3]
    checksum = (fhd >> 2) & 1
    hlen = 1 + (0 if single else 1) + did_size + fcs_size
    if n - pos < hlen:
        fail("Truncated")
    p = pos + 1
    if not single:
        wd = src[p]
        p += 1
        wlog = 10 + (wd >> 3)
        window = (1 << wlog) + ((1 << wlog) >> 3) * (wd & 7)
    fdid = int.from_bytes(src[p:p + did_size], "little")
    p += did_size
    fcs = None
    if fcs_size:
        fcs = int.from_bytes(src[p:p + fcs_size], "little")
        if fcs_size == 2:
            fcs += 256
        p += fcs_size
    if single:
        window = fcs
    pos = p
    if window > max_window:
        fail("WindowTooLarge")
    if fdid != 0 and fdid != did:
        fail("DictionaryMismatch")
    f = Frame()
    f.out, f.base, f.window, f.dict = out, len(out), window, dcontent
    st = {"huf": None, "ll": None, "of": None, "ml": None}
    f.rep = [1, 4, 8]
    if dent is not None:
        st = {k: dent[k] for k in ("huf", "ll", "of", "ml")}
        f.rep = list(dent["rep"])
    block_max = min(window, BLOCK_MAX)
    while True:
        if n - pos < 3:
            fail("Truncated")
        h = int.from_bytes(src[pos:pos + 3], "little")
        pos += 3
        last, btype, bsize = h & 1, (h >> 1) & 3, h >> 3
        if btype == 3:
            fail("BadBlockType")
        if bsize > block_max:
            fail("BlockTooLarge")
        room = max_out - len(out)
        if btype == 0:
            # the room for a raw block is taken at its header, as for RLE
            if bsize > room:
                fail("OutputTooLarge")
            if n - pos < bsize:
                fail("Truncated")
            out.extend(src[pos:pos + bsize])
            pos += bsize
        elif btype == 1:
            if n - pos < 1:
                fail("Truncated")
            if bsize > room:
                fail("OutputTooLarge")
            out.extend([src[pos]] * bsize)
            pos += 1
        else:
            if n - pos < bsize:
                fail("Truncated")
            block = src[pos:pos + bsize]
            pos += bsize
            mark = len(out)
            lits, used = literals(block, st, block_max)
            seqs = sequences(block[used:], st)
            execute(seqs, lits, f, block_max)
            if len(out) > max_out:
                del out[mark:]
                fail("OutputTooLarge")
        if last:
            break
    content = out[f.base:]
    if fcs is not None and len(content) != fcs:
        fail("BadContentSize")
    if checksum:
        if n - pos < 4:
            fail("Truncated")
        want = int.from_bytes(src[pos:pos + 4], "little")
        pos += 4
        if verify and want != xxh64(bytes(content)) & 0xFFFFFFFF:
            fail("BadChecksum")
    return pos

# The writer
#
# A frame writer that can produce every part of the format, chosen by
# options or at random (rng), so the decoder under test meets them all.


class BitWriter:
    """Little-endian bits (FSE table descriptions)."""

    def __init__(self):
        self.bits = []

    def write(self, v, n):
        self.bits.extend((v >> k) & 1 for k in range(n))

    def bytes(self):
        b = self.bits + [0] * (-len(self.bits) % 8)
        return bytes(sum(b[i + k] << k for k in range(8)) for i in range(0, len(b), 8))


def fse_write(probs, al):
    w = BitWriter()
    w.write(al - 5, 4)
    remaining, i = 1 << al, 0
    while remaining > 0:
        p = probs[i]
        v = p + 1
        top = remaining + 1
        nb = top.bit_length()
        low = (1 << nb) - 1 - top
        if v < low:
            w.write(v, nb - 1)
        elif v < (1 << (nb - 1)):
            w.write(v, nb)
        else:
            w.write(v + low, nb)
        remaining -= abs(p)
        i += 1
        if p == 0:
            z = 0
            while i + z < len(probs) and probs[i + z] == 0:
                z += 1
            i += z
            while z >= 3:
                w.write(3, 2)
                z -= 3
            w.write(z, 2)
    assert i == len(probs), "probabilities after the total"
    return w.bytes()


def fse_normalize(counts, al, rng=None):
    """Probabilities summing to 2^al for the symbol counts (a list); every
    present symbol gets at least 1 (or -1, "less than 1", at random)."""
    total = sum(counts)
    size = 1 << al
    probs = []
    for c in counts:
        if c == 0:
            probs.append(0)
        else:
            q = c * size // total
            if q < 1:
                probs.append(-1 if rng is not None and rng.random() < 0.5 else 1)
            else:
                probs.append(q)
    while sum(abs(p) for p in probs) != size:
        diff = size - sum(abs(p) for p in probs)
        k = max(range(len(probs)), key=lambda j: probs[j])
        if probs[k] + diff >= 1:
            probs[k] += diff
        elif probs[k] > 1:
            probs[k] -= 1
        else:
            return None
    while probs and probs[-1] == 0:
        probs.pop()
    return probs


def fse_encode_states(table, syms):
    """Decoder states s_0..s_{n-1} for the symbols, each reachable from the
    one before, and the update bits (value, n) between them."""
    by = {}
    for s, (x, nb, base) in enumerate(table):
        by.setdefault(x, []).append((s, nb, base))
    n = len(syms)
    states = [None] * n
    # the last state: one with the most bits, so that a stream can end there
    states[n - 1] = max(by[syms[n - 1]], key=lambda e: e[1])[0]
    ups = [None] * (n - 1)
    for i in range(n - 2, -1, -1):
        t = states[i + 1]
        for s, nb, base in by[syms[i]]:
            if base <= t < base + (1 << nb):
                states[i] = s
                ups[i] = (t - base, nb)
                break
        else:
            raise AssertionError("no state")
    return states, ups


def huf_lengths(freq, limit=11):
    import heapq
    syms = [s for s in range(len(freq)) if freq[s]]
    heap = [(freq[s], k, [s]) for k, s in enumerate(syms)]
    heapq.heapify(heap)
    lens = {s: 0 for s in syms}
    k = len(heap)
    while len(heap) > 1:
        a, _, sa = heapq.heappop(heap)
        b, _, sb = heapq.heappop(heap)
        for s in sa + sb:
            lens[s] += 1
        heapq.heappush(heap, (a + b, k, sa + sb))
        k += 1
    for s in lens:
        lens[s] = min(lens[s], limit)
    unit = lambda l: 1 << (limit - l)
    target = 1 << limit
    kraft = sum(unit(l) for l in lens.values())
    order = sorted(lens, key=lambda s: (freq[s], s))
    while kraft > target:
        for s in order:
            if lens[s] < limit and kraft > target:
                kraft -= unit(lens[s] + 1)
                lens[s] += 1
    while kraft < target:
        for s in reversed(order):
            if lens[s] > 1 and kraft + unit(lens[s]) <= target:
                kraft += unit(lens[s])
                lens[s] -= 1
                break
        else:
            raise AssertionError("cannot complete the code")
    return lens


def huf_build(lits):
    """(weights for symbols 0..max-1, the code table) for the literals,
    which hold two different bytes or more."""
    freq = [0] * 256
    for b in lits:
        freq[b] += 1
    lens = huf_lengths(freq)
    maxbits = max(lens.values())
    top = max(lens)
    ws = [maxbits + 1 - lens[s] if s in lens else 0 for s in range(top + 1)]
    return ws[:-1], huf_codes(ws, maxbits)


def huf_tree_desc(weights, rng, force=None):
    """A tree description: direct (4 bits per weight) or FSE-coded."""
    n = len(weights)
    use_fse = force == "fse" or (force is None and (n > 128 or rng.random() < 0.5))
    if force == "direct" or (not use_fse and n <= 128):
        if n > 128:
            raise ValueError("too many weights")
        body = bytearray([127 + n])
        for i in range(0, n, 2):
            body.append((weights[i] << 4) | (weights[i + 1] if i + 1 < n else 0))
        return bytes(body)
    if n < 2:
        raise ValueError("too few weights")
    counts = [0] * 13
    for w in weights:
        counts[w] += 1
    if max(counts) == n:
        raise ValueError("one weight only")
    probs = None
    for al in (6, 5):
        probs = fse_normalize(counts, al, rng)
        if probs is not None:
            break
    t = fse_build(probs, al)
    s1, u1 = fse_encode_states(t, weights[0::2])
    s2, u2 = fse_encode_states(t, weights[1::2])
    fields = [(s1[0], al), (s2[0], al)]
    for i in range(max(len(u1), len(u2))):
        if i < len(u1):
            fields.append(u1[i])
        if i < len(u2):
            fields.append(u2[i])
    # the stream must end where the decoder stops: right after the update
    # into the last state of the stream holding the next-to-last weight
    last_state = (s1 if n % 2 == 0 else s2)[-1]
    if t[last_state][1] == 0:
        raise ValueError("cannot end")
    desc = fse_write(probs, al) + pack_backward(fields)
    if len(desc) >= 128:
        raise ValueError("too long")
    got = fse_weights(desc, "BadHuffmanTree")
    if got != list(weights):
        raise ValueError("weights do not round trip")
    return bytes([len(desc)]) + desc


def huf_stream(codes, syms):
    return pack_backward([codes[s] for s in syms])


def lit_header_raw(kind, n):
    if n < 32:
        return bytes([kind | (n << 3)])
    if n < 4096:
        return bytes([kind | 4 | ((n & 15) << 4), n >> 4])
    return bytes([kind | 12 | ((n & 15) << 4), (n >> 4) & 255, n >> 12])


def lit_section(lits, st, rng, mode=None):
    """The literals section for these literals; mode: raw, rle, huf1, huf4,
    treeless1, treeless4 (or chosen at random)."""
    n = len(lits)
    if mode is None:
        if n == 0:
            mode = "raw"
        elif len(set(lits)) == 1:
            mode = rng.choice(["rle", "raw"])
        else:
            mode = rng.choice(["raw", "huf1", "huf4", "huf4", "treeless1", "treeless4"])
    if mode in ("huf1", "treeless1") and n > 1023:
        mode = mode[:-1] + "4"
    if mode.startswith("treeless") and (st.get("huf") is None or any(b not in st["huf"] for b in lits)):
        mode = "huf" + mode[-1]
    if mode.startswith("huf") and len(set(lits)) < 2:
        mode = "raw"
    if mode.endswith("4") and (n < 6 or n >= 1 << 18):
        mode = (mode[:-1] + "1") if n <= 1023 else "raw"
    if mode == "rle" and len(set(lits)) != 1:
        mode = "raw"
    if mode == "raw":
        return lit_header_raw(0, n) + bytes(lits)
    if mode == "rle":
        return lit_header_raw(1, n) + bytes([lits[0]])
    if mode.startswith("huf"):
        weights, codes = huf_build(lits)
        tree = None
        for force in (None, "direct", "fse"):
            try:
                tree = huf_tree_desc(weights, rng, force)
                break
            except ValueError:
                pass
        if tree is None:
            return lit_header_raw(0, n) + bytes(lits)
        st["huf"] = codes
        kind = 2
    else:
        codes, tree, kind = st["huf"], b"", 3
    if mode.endswith("1"):
        body = tree + huf_stream(codes, lits)
        formats = [(0, 3, 10)]
    else:
        seg = (n + 3) // 4
        parts = [lits[0:seg], lits[seg:2 * seg], lits[2 * seg:3 * seg], lits[3 * seg:]]
        ss = [huf_stream(codes, p) for p in parts]
        body = tree + b"".join(len(s).to_bytes(2, "little") for s in ss[:3]) + b"".join(ss)
        formats = [(1, 3, 10), (2, 4, 14), (3, 5, 18)]
    comp = len(body)
    for sf, hl, bits in formats:
        if n < (1 << bits) and comp < (1 << bits):
            v = kind | (sf << 2) | (n << 4) | (comp << (4 + bits))
            return v.to_bytes(hl, "little") + body
    return lit_header_raw(0, n) + bytes(lits)


def code_of(v, base):
    c = 0
    while c + 1 < len(base) and base[c + 1] <= v:
        c += 1
    return c


def seq_section(seqs, st, rng, modes=None):
    """seqs: (ll, offset value, ml)."""
    n = len(seqs)
    if n == 0:
        return b"\x00"
    if n < 128:
        head = bytes([n])
    elif n < 0x7F00:
        head = bytes([128 + (n >> 8), n & 255])
    else:
        head = bytes([255, (n - 0x7F00) & 255, (n - 0x7F00) >> 8])
    llc = [code_of(ll, LL_BASE) for ll, _, _ in seqs]
    ofc = [highbit(ofv) for _, ofv, _ in seqs]
    mlc = [code_of(ml, ML_BASE) for _, _, ml in seqs]
    mode_bits, tables, tabs = 0, b"", {}
    for shift, field, codes in ((6, "ll", llc), (4, "of", ofc), (2, "ml", mlc)):
        max_al, max_sym, default, dal = FIELDS[field]
        prev = st.get(field)
        choices = []
        if all(c < len(default) and default[c] != 0 for c in codes):
            choices.append(0)
        if len(set(codes)) == 1:
            choices.append(1)
        choices.append(2)
        if prev is not None and all(any(e[0] == c for e in prev) for c in codes):
            choices.append(3)
        m = modes[field] if modes and modes.get(field) in choices else rng.choice(choices)
        if m == 0:
            t = fse_build(default, dal)
        elif m == 1:
            t = fse_rle(codes[0])
            tables += bytes([codes[0]])
        elif m == 2:
            counts = [0] * (max(codes) + 1)
            for c in codes:
                counts[c] += 1
            if len(set(codes)) == 1:
                counts.append(1)       # a second symbol, never used
            al = rng.randint(5, max_al)
            probs = fse_normalize(counts, al, rng)
            while probs is None:
                al += 1
                probs = fse_normalize(counts, al, rng)
            t = fse_build(probs, al)
            tables += fse_write(probs, al)
        else:
            t = prev
        st[field] = t
        tabs[field] = t
        mode_bits |= m << shift
    sl, ul = fse_encode_states(tabs["ll"], llc)
    so, uo = fse_encode_states(tabs["of"], ofc)
    sm, um = fse_encode_states(tabs["ml"], mlc)
    fields = [(sl[0], table_al(tabs["ll"])), (so[0], table_al(tabs["of"])), (sm[0], table_al(tabs["ml"]))]
    for i, (ll, ofv, ml) in enumerate(seqs):
        fields.append((ofv - (1 << ofc[i]), ofc[i]))
        fields.append((ml - ML_BASE[mlc[i]], ML_BITS[mlc[i]]))
        fields.append((ll - LL_BASE[llc[i]], LL_BITS[llc[i]]))
        if i < n - 1:
            fields += [ul[i], um[i], uo[i]]
    return head + bytes([mode_bits]) + tables + pack_backward(fields)


def rep_after(rep, ll, ofv):
    """The repeat offsets after a sequence, and its offset, as RFC 8878
    (section 3.1.2.5) updates them."""
    if ofv > 3:
        off = ofv - 3
        return [off, rep[0], rep[1]], off
    k = ofv - 1 if ll > 0 else ofv
    if k == 0:
        return list(rep), rep[0]
    if k == 1:
        return [rep[1], rep[0], rep[2]], rep[1]
    if k == 2:
        return [rep[2], rep[0], rep[1]], rep[2]
    return [rep[0] - 1, rep[0], rep[1]], rep[0] - 1


def match_seqs(data, start, end, rep, reach, rng, min_match=4):
    """Greedy matching of data[start:end], with data[:start] as history a
    match may reach back into (reach(i): how far back from position i):
    (sequences with offset values, literals, the repeat offsets after)."""
    seqs, lits = [], []
    table = {}
    for i in range(max(0, start - reach(start)), start):
        if i + 4 <= len(data):
            table[bytes(data[i:i + 4])] = i
    i, lit_start = start, start
    rep = list(rep)
    while i + min_match <= end:
        key = bytes(data[i:i + 4])
        ll = i - lit_start
        cands = list(rep) + ([i - table[key]] if key in table else [])
        best, best_off = 0, 0
        lim = reach(i)
        for off in cands:
            if off <= 0 or off > i or off > lim:
                continue
            l = 0
            while i + l < end and data[i + l - off] == data[i + l] and l < 100000:
                l += 1
            if l > best:
                best, best_off = l, off
        table[key] = i
        if best >= min_match:
            ml = best if rng.random() < 0.9 else max(3, best - rng.randrange(best - 2))
            ofv = None
            # repeat codes, as the decoder reads them (ll = 0 shifts them)
            reps = [(1, rep[0]), (2, rep[1]), (3, rep[2])] if ll > 0 else [(1, rep[1]), (2, rep[2]), (3, rep[0] - 1)]
            for code, r in reps:
                if r == best_off:
                    ofv = code
                    break
            if ofv is None:
                ofv = best_off + 3
            rep, _ = rep_after(rep, ll, ofv)
            seqs.append((ll, ofv, ml))
            lits.extend(data[lit_start:i])
            for j in range(i + 1, min(i + ml, end - 3)):
                table[bytes(data[j:j + 4])] = j
            i += ml
            lit_start = i
        else:
            i += 1
    lits.extend(data[lit_start:end])
    return seqs, lits, rep


def frame_header(size, checksum=True, single=None, window_desc=None, dict_id=0, fcs_bytes=None, did_bytes=None, unused_bit=False):
    """size: the content size, or None for a header without it. A frame is
    single-segment (no window descriptor) unless window_desc is given."""
    if single is None:
        single = size is not None and window_desc is None
    if fcs_bytes is None:
        if size is None:
            fcs_bytes = 0
        elif size < 256:
            fcs_bytes = 1 if single else 4
        elif size < 65536 + 256:
            fcs_bytes = 2
        elif size < 1 << 32:
            fcs_bytes = 4
        else:
            fcs_bytes = 8
    flag = {0: 0, 1: 0, 2: 1, 4: 2, 8: 3}[fcs_bytes]
    if did_bytes is None:
        did_bytes = 0 if dict_id == 0 else (1 if dict_id < 256 else 2 if dict_id < 65536 else 4)
    fhd = (flag << 6) | (int(single) << 5) | (int(checksum) << 2) | {0: 0, 1: 1, 2: 2, 4: 3}[did_bytes] | (16 if unused_bit else 0)
    out = bytearray(MAGIC.to_bytes(4, "little")) + bytes([fhd])
    if not single:
        out.append(window_desc if window_desc is not None else (17 - 10) << 3)
    out += dict_id.to_bytes(did_bytes, "little")
    if fcs_bytes:
        v = size - 256 if fcs_bytes == 2 else size
        out += v.to_bytes(fcs_bytes, "little")
    return bytes(out)


def window_of(desc):
    wlog = 10 + (desc >> 3)
    return (1 << wlog) + ((1 << wlog) >> 3) * (desc & 7)


def block_header(last, btype, size):
    return (int(last) | (btype << 1) | (size << 3)).to_bytes(3, "little")


def compress_frame(data, rng, checksum=True, content_size=True, window_desc=None, block_size=BLOCK_MAX,
                   dict_bytes=b"", dict_id=None, kinds=("raw", "rle", "comp"), lit_mode=None, seq_modes=None,
                   single=None):
    """A frame holding data. kinds: the block types to choose from, per
    block, among those that fit ("raw", "rle", "comp")."""
    data = bytes(data)
    did, dcontent, dent = parse_dict(dict_bytes) if dict_bytes else (0, [], None)
    if dict_id is None:
        dict_id = did
    if single is None:
        single = content_size and window_desc is None
    if single:
        window = len(data)
    else:
        if window_desc is None:
            window_desc = (17 - 10) << 3
        window = window_of(window_desc)
    out = bytearray(frame_header(len(data) if content_size else None, checksum, single, None if single else window_desc, dict_id))
    st = {"huf": None, "ll": None, "of": None, "ml": None}
    rep = [1, 4, 8]
    if dent is not None:
        st = {k: dent[k] for k in ("huf", "ll", "of", "ml")}
        rep = list(dent["rep"])
    dlen = len(dcontent)
    hist = bytes(dcontent) + data
    bsize = max(1, min(block_size, window, BLOCK_MAX)) if window else 1
    pos = 0
    while True:
        chunk = data[pos:pos + bsize]
        last = pos + len(chunk) >= len(data)
        choice = [k for k in kinds if k != "rle" or (chunk and len(set(chunk)) == 1)] or ["raw"]
        k = rng.choice(choice)
        if k == "raw":
            out += block_header(last, 0, len(chunk)) + chunk
        elif k == "rle":
            out += block_header(last, 1, len(chunk)) + chunk[:1]
        else:
            # how far back a match at hist[i] may reach (RFC 8878 section 5:
            # into the dictionary while the frame is within its window)
            reach = lambda i: (i - dlen + dlen) if i - dlen <= window else window
            seqs, lits, rep2 = match_seqs(hist, dlen + pos, dlen + pos + len(chunk), rep, reach, rng)
            st2 = dict(st)
            body = lit_section(lits, st2, rng, lit_mode) + seq_section(seqs, st2, rng, seq_modes)
            if len(body) > min(window, BLOCK_MAX):
                out += block_header(last, 0, len(chunk)) + chunk
            else:
                out += block_header(last, 2, len(body)) + body
                rep, st = rep2, st2
        pos += len(chunk)
        if last:
            break
    if checksum:
        out += (xxh64(data) & 0xFFFFFFFF).to_bytes(4, "little")
    return bytes(out)


def skippable(n, k=0):
    return (0x184D2A50 + k).to_bytes(4, "little") + n.to_bytes(4, "little") + bytes((7 * j) & 255 for j in range(n))
