#!/usr/bin/env python3
"""An independent model of the 842 format, for the differential test.

Written from the same sources as the package (see ../README.md): Blaner et
al. 2013 (IBM J. Res. & Dev. 57(6), paper 3) for the phrases, pointers,
histories, Z8, RPT and the 69-bit chunk; US 2006/0106870 A1, Figure 3, for
the template table; and the black-box observations of Linux's 842 logged in
OBSERVATIONS.md for the template codes, END, short data, the CRC, the bit
order, padding and the decoder's answers. It shares an author with the
package, so it checks the package against a second reading of those
sources, not against IBM's or Linux's implementation.

    decode(src, max) -> ("ok", bytes) | ("err", kind)
    encode(data, strategy=DEFAULT) -> bytes      the package's compressor
    literals(data) -> bytes                       the literal-only stream
    worst(n) -> int                               the worst-case length
"""

# The 26 templates (US 2006/0106870 A1, Figure 3; Linux uses its numbering,
# OBSERVATIONS.md, E2): each a list of sub-phrases
TEMPLATES = [s.split() for s in [
    "LL LL LL LL", "LL LL LL P2", "LL LL P2 LL", "LL LL P2 P2", "LL LL P4",
    "LL P2 LL LL", "LL P2 LL P2", "LL P2 P2 LL", "LL P2 P2 P2", "LL P2 P4",
    "P2 LL LL LL", "P2 LL LL P2", "P2 LL P2 LL", "P2 LL P2 P2", "P2 LL P4",
    "P2 P2 LL LL", "P2 P2 LL P2", "P2 P2 P2 LL", "P2 P2 P2 P2", "P2 P2 P4",
    "P4 LL LL", "P4 LL P2", "P4 P2 LL", "P4 P2 P2", "P4 P4", "P8"]]
REPEAT, ZERO, SHORT, END = 27, 28, 29, 30
# pointer: (phrase size, index bits, history bytes)
PTR = {"P2": (2, 8, 512), "P4": (4, 9, 2048), "P8": (8, 8, 2048)}
# Linux's errno for each failure (OBSERVATIONS.md)
ERRNO = {"truncated": -75, "too_large": -28, "bad_template": -22,
         "bad_pointer": -22, "bad_repeat": -22, "bad_short": -22, "bad_crc": -22}


def crc(data):
    """CRC-32, polynomial 0x04C11DB7, most significant bit first, initial
    value 0, no final XOR (OBSERVATIONS.md, E1)."""
    c = 0
    for b in data:
        c ^= b << 24
        for _ in range(8):
            c = ((c << 1) ^ 0x04C11DB7) & 0xFFFFFFFF if c & 0x80000000 else (c << 1) & 0xFFFFFFFF
    return c


class Bits:
    """Most significant bit first, as the stream is written."""
    def __init__(self, src):
        self.src = src
        self.pos = 0

    def get(self, n):
        if self.pos + n > 8 * len(self.src):
            raise Fail("truncated")
        v = 0
        for _ in range(n):
            v = (v << 1) | ((self.src[self.pos >> 3] >> (7 - (self.pos & 7))) & 1)
            self.pos += 1
        return v


class Fail(Exception):
    pass


def pointer_pos(n, index, kind):
    """The position a pointer reads: the latest position congruent to
    index * size modulo the history, below the output length rounded down
    to 8 bytes; None if there is none (OBSERVATIONS.md, E3 and E6)."""
    size, _, hist = PTR[kind]
    t8 = n - n % 8
    p = (t8 // hist) * hist + index * size
    if p >= t8:
        p -= hist
    return p if p >= 0 else None


def decode(src, maximum=1 << 30):
    out = bytearray()
    r = Bits(src)

    def put(bs):
        if len(out) + len(bs) > maximum:
            raise Fail("too_large")
        out.extend(bs)

    try:
        while True:
            t = r.get(5)
            if t < 26:
                for f in TEMPLATES[t]:
                    if f == "LL":
                        put(r.get(16).to_bytes(2, "big"))
                    else:
                        size, width, _ = PTR[f]
                        p = pointer_pos(len(out), r.get(width), f)
                        if p is None:
                            raise Fail("bad_pointer")
                        put(bytes(out[p:p + size]))
            elif t == REPEAT:
                n = r.get(6) + 1
                if len(out) < 8:
                    raise Fail("bad_repeat")
                put(bytes(out[-8:]) * n)
            elif t == ZERO:
                put(bytes(8))
            elif t == SHORT:
                n = r.get(3)
                if n == 0:
                    raise Fail("bad_short")
                put(bytes(r.get(8) for _ in range(n)))
            elif t == END:
                if r.get(32) != crc(out):
                    raise Fail("bad_crc")
                return ("ok", bytes(out))
            else:
                raise Fail("bad_template")
    except Fail as e:
        return ("err", e.args[0])


class Writer:
    def __init__(self):
        self.bits = []

    def put(self, v, n):
        for i in range(n - 1, -1, -1):
            self.bits.append((v >> i) & 1)

    def pack(self):
        """Zero bits to a whole number of 8-byte words (OBSERVATIONS.md, E1)."""
        b = self.bits + [0] * ((-len(self.bits)) % 64)
        return bytes(int("".join(map(str, b[i:i + 8])), 2) for i in range(0, len(b), 8))


def finish(w, data):
    w.put(END, 5)
    w.put(crc(data), 32)
    return w


def short(w, tail):
    if tail:
        w.put(SHORT, 5)
        w.put(len(tail), 3)
        for b in tail:
            w.put(b, 8)


def literals(data):
    """Every chunk as template 0, the tail as short data, END and the CRC."""
    return literal_writer(data).pack()


def literal_writer(data):
    w = Writer()
    k = len(data) - len(data) % 8
    for i in range(0, k, 8):
        w.put(0, 5)
        for j in range(i, i + 8, 2):
            w.put(data[j] * 256 + data[j + 1], 16)
    short(w, data[k:])
    return finish(w, data)


def worst_bits(n):
    """69 bits per chunk (Blaner et al.), the tail's short data, END and CRC."""
    tail = n % 8
    return 69 * (n // 8) + (8 + 8 * tail if tail else 0) + 37


def worst(n):
    return 8 * ((worst_bits(n) + 63) // 64)


# The compressor (the package's encode.bend and match.bend, as a model)

MASK = 0xFFFFFFFF


def fnv(bs, bits):
    """FNV-1a, 32 bits, its top `bits` bits: the matcher's hash."""
    h = 2166136261
    for b in bs:
        h = ((h ^ b) * 16777619) & MASK
    return h >> (32 - bits)


# strategies: ("hash", bits8, bits4, bits2) or ("none",)
DEFAULT = ("hash", 10, 11, 10)


def cost(f):
    return {"LL": 16, "P2": 8, "P4": 9, "P8": 8}[f]


def encode(data, strategy=DEFAULT):
    """The encoder's stream, unchecked (the package's compress_unchecked)."""
    return encode_writer(data, strategy).pack()


def compress(data, strategy=DEFAULT):
    """The checked stream (the package's compress_with): the encoder's, if
    it is no longer than the worst case before padding (the literal
    stream's length) and decodes back; else the literal stream."""
    m = encode_writer(data, strategy)
    if len(m.bits) <= worst_bits(len(data)) and decode(m.pack(), len(data)) == ("ok", bytes(data)):
        return m.pack()
    return literals(data)


def encode_writer(data, strategy=DEFAULT):
    """Greedy, chunk by chunk: a run of the previous chunk is RPT; eight
    zero bytes are Z8; otherwise the template with the fewest bits whose
    pointers the matcher finds (ties: the lowest code). The tail is short
    data. The matcher keeps, for each phrase size, a direct-mapped table of
    the latest aligned position of a phrase with that hash; a candidate is
    used only if its bytes are the phrase and the decoder would read that
    position (pointer_pos)."""
    w = Writer()
    n8 = len(data) - len(data) % 8
    tables = None
    if strategy[0] == "hash":
        tables = {8: {}, 4: {}, 2: {}}
        bits = {8: strategy[1], 4: strategy[2], 2: strategy[3]}
    run = 0
    for i in range(0, n8, 8):
        chunk = data[i:i + 8]
        if i >= 8 and chunk == data[i - 8:i]:
            run += 1
            if run == 64:
                w.put(REPEAT, 5)
                w.put(63, 6)
                run = 0
        else:
            if run:
                w.put(REPEAT, 5)
                w.put(run - 1, 6)
                run = 0
            if chunk == bytes(8):
                w.put(ZERO, 5)
            else:
                encode_chunk(w, data, i, tables, bits if tables else None)
        if tables is not None:
            for size in (8, 4, 2):
                for j in range(i, i + 8, size):
                    tables[size][fnv(data[j:j + size], bits[size])] = j
    if run:
        w.put(REPEAT, 5)
        w.put(run - 1, 6)
    short(w, data[n8:])
    return finish(w, data)


def find(data, i, j, size, tables, bits):
    """The pointer index for the phrase at j (in the chunk at i), or None."""
    if tables is None:
        return None
    kind = "P%d" % size
    p = tables[size].get(fnv(data[j:j + size], bits[size]))
    if p is None or data[p:p + size] != data[j:j + size]:
        return None
    _, _, hist = PTR[kind]
    index = (p % hist) // size
    if pointer_pos(i, index, kind) != p:
        return None
    return index


def encode_chunk(w, data, i, tables, bits):
    found = {}
    for size in (8, 4, 2):
        for j in range(i, i + 8, size):
            found[(size, j)] = find(data, i, j, size, tables, bits)
    best = None
    for t, fields in enumerate(TEMPLATES):
        j = i
        ok = True
        c = 5
        for f in fields:
            size = 2 if f == "LL" else int(f[1])
            if f != "LL" and found[(size, j)] is None:
                ok = False
                break
            c += cost(f)
            j += size
        if ok and (best is None or c < best[0]):
            best = (c, t)
    t = best[1]
    w.put(t, 5)
    j = i
    for f in TEMPLATES[t]:
        if f == "LL":
            w.put(data[j] * 256 + data[j + 1], 16)
            j += 2
        else:
            size, width, _ = PTR[f]
            w.put(found[(size, j)], width)
            j += size
