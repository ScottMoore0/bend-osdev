"""An independent model of what bend-osdev-ext4 computes, for ref/gen.py.

Written here from the same documents as the package (the ext4 disk-layout
and jbd2 documentation) and from the tools' black-box behaviour, so it
shares an author with the package; gen.py checks it against debugfs and
e2fsck wherever they can answer the same question.
"""
import struct

M32 = 0xFFFFFFFF

# CRC-32C, the raw register (ext4 and jbd2 chain it without inversions)
_T = []
for _i in range(256):
    _c = _i
    for _ in range(8):
        _c = (_c >> 1) ^ 0x82F63B78 if _c & 1 else _c >> 1
    _T.append(_c)

def crc32c(c, data):
    for b in data:
        c = _T[(c ^ b) & 255] ^ (c >> 8)
    return c

# Directory hashes

def _rol(x, s):
    return ((x << s) | (x >> (32 - s))) & M32

def _char(c, signed):
    return c - 256 if signed and c >= 128 else c

def _pack(msg, num, signed):
    n = len(msg)
    pad = (n | (n << 8)) & M32
    pad = (pad | (pad << 16)) & M32
    out, val = [], pad
    for i, c in enumerate(msg[:num * 4]):
        val = (_char(c, signed) + (val << 8)) & M32
        if i % 4 == 3:
            out.append(val)
            val = pad
    out.append(val)
    out += [pad] * num
    return out[:num]

def _md4(buf, w):
    a, b, c, d = buf
    def f(x, y, z): return z ^ (x & (y ^ z))
    def g(x, y, z): return ((x & y) + ((x ^ y) & z)) & M32
    def h(x, y, z): return x ^ y ^ z
    steps = [(f, 0, 0, 3), (f, 1, 0, 7), (f, 2, 0, 11), (f, 3, 0, 19), (f, 4, 0, 3), (f, 5, 0, 7), (f, 6, 0, 11), (f, 7, 0, 19),
             (g, 1, 0x5A827999, 3), (g, 3, 0x5A827999, 5), (g, 5, 0x5A827999, 9), (g, 7, 0x5A827999, 13),
             (g, 0, 0x5A827999, 3), (g, 2, 0x5A827999, 5), (g, 4, 0x5A827999, 9), (g, 6, 0x5A827999, 13),
             (h, 3, 0x6ED9EBA1, 3), (h, 7, 0x6ED9EBA1, 9), (h, 2, 0x6ED9EBA1, 11), (h, 6, 0x6ED9EBA1, 15),
             (h, 1, 0x6ED9EBA1, 3), (h, 5, 0x6ED9EBA1, 9), (h, 0, 0x6ED9EBA1, 11), (h, 4, 0x6ED9EBA1, 15)]
    regs = [a, b, c, d]
    # step k updates register (0, 3, 2, 1)[k % 4] from the other three
    for k, (fn, i, kk, s) in enumerate(steps):
        r = (0, 3, 2, 1)[k % 4]
        x, y, z = regs[(r + 1) % 4], regs[(r + 2) % 4], regs[(r + 3) % 4]
        regs[r] = _rol((regs[r] + fn(x, y, z) + w[i] + kk) & M32, s)
    return [(buf[i] + regs[i]) & M32 for i in range(4)]

def _tea(buf, w):
    s, b0, b1 = 0, buf[0], buf[1]
    a, b, c, d = w
    for _ in range(16):
        s = (s + 0x9E3779B9) & M32
        b0 = (b0 + ((((b1 << 4) + a) & M32) ^ ((b1 + s) & M32) ^ (((b1 >> 5) + b) & M32))) & M32
        b1 = (b1 + ((((b0 << 4) + c) & M32) ^ ((b0 + s) & M32) ^ (((b0 >> 5) + d) & M32))) & M32
    return [(buf[0] + b0) & M32, (buf[1] + b1) & M32, buf[2], buf[3]]

def _legacy(name, signed):
    h0, h1 = 0x12A3FE2D, 0x37ABE8F9
    for c in name:
        h = (h1 + (h0 ^ ((_char(c, signed) * 7152373) & M32))) & M32
        if h & 0x80000000:
            h = (h - 0x7FFFFFFF) & M32
        h1, h0 = h0, h
    return (h0 << 1) & M32

def dxhash(name, version, seed=(0, 0, 0, 0)):
    """(major, minor) of a name under hash version 0 to 5, or None"""
    buf = list(seed) if any(seed) else [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476]
    signed = version < 3
    v = version % 3
    if version > 5:
        return None
    if v == 0:
        major, minor = _legacy(name, signed), 0
    elif v == 1:
        for p in range(0, len(name), 32):
            buf = _md4(buf, _pack(name[p:], 8, signed))
        major, minor = buf[1], buf[2]
    else:
        for p in range(0, len(name), 16):
            buf = _tea(buf, _pack(name[p:], 4, signed))
        major, minor = buf[0], buf[1]
    major &= ~1 & M32
    if major == 0xFFFFFFFE:
        major = 0xFFFFFFFC
    return major, minor

# The htree writer: entries sorted by hash (stably), leaves filled while
# entries fit and ending only between different hashes, an index above

def _rec(n):
    return (n + 8 + 3) // 4 * 4

def htree_blocks(bs, version, signed, seed, iseed, filetype, ino, parent, levels, pad, ents):
    """the blocks the package's writer makes: ents are (ino, ft, name)"""
    v = version + (0 if signed else 3)
    hashed = [(dxhash(n, v, seed)[0], i, ft, n) for (i, ft, n) in ents]
    hashed.sort(key=lambda e: e[0])
    cap = bs - (12 if iseed is not None else 0)
    leaves, cur, used, lo, prev = [], [], 0, 0, 0
    for e in hashed:
        sz = _rec(len(e[3]))
        if cur and used + sz > cap and e[0] > prev:
            leaves.append((lo, cur))
            cur, used, lo = [], 0, e[0]
        cur.append(e)
        used += sz
        prev = e[0]
    leaves.append((lo, cur))
    for lo, es in leaves:
        if sum(_rec(len(e[3])) for e in es) > cap:
            return None
    tail = iseed is not None
    rlimit = (bs - 32) // 8 - (1 if tail else 0)
    nlimit = (bs - 8) // 8 - (1 if tail else 0)
    def nodes_for(n):
        k = 0
        while n > rlimit:
            n = -(-n // nlimit)
            k += n
        return k
    n = len(leaves)
    while 1 + n + nodes_for(n) < pad:
        n += 1
    last = leaves[-1][1][-1][0] if leaves[-1][1] else leaves[-1][0]
    leaves += [(last + 2, [])] * (n - len(leaves))
    blocks = []
    for lo, es in leaves:
        body, used = b"", 0
        if not es:
            body = struct.pack("<IHBB", 0, cap, 0, 0) + bytes(cap - 8)
        for k, (h, i, ft, name) in enumerate(es):
            sz = _rec(len(name))
            rec = cap - used if k == len(es) - 1 else sz
            body += struct.pack("<IHBB", i, rec, len(name), ft if filetype else 0) + name + bytes(rec - 8 - len(name))
            used += sz
        if tail:
            body += struct.pack("<IHBB", 0, 12, 0, 0xDE) + struct.pack("<I", crc32c(iseed, body))
        blocks.append(body)
    items = [(lo, 1 + k) for k, (lo, es) in enumerate(leaves)]
    nodes, nxt, lv = [], 1 + len(leaves), 0
    while len(items) > rlimit:
        if lv + 1 >= levels:
            return None
        up = []
        for k in range(0, len(items), nlimit):
            g = items[k:k + nlimit]
            nodes.append(_index(bs, iseed, struct.pack("<IHBB", 0, bs % 65536, 0, 0), 8, nlimit, g))
            up.append((g[0][0], nxt))
            nxt += 1
        items, lv = up, lv + 1
    ft2 = 2 if filetype else 0
    head = struct.pack("<IHBB", ino, 12, 1, ft2) + b".\0\0\0" + struct.pack("<IHBB", parent, bs - 12, 2, ft2) + b"..\0\0"
    head += struct.pack("<IBBBB", 0, version, 8, lv, 0)
    root = _index(bs, iseed, head, 32, rlimit, items)
    return [root] + blocks + nodes

def _index(bs, iseed, head, off, limit, items):
    idx = struct.pack("<HHI", limit, len(items), items[0][1]) + b"".join(struct.pack("<II", h, b) for h, b in items[1:])
    body = head + idx
    body += bytes(off + limit * 8 - len(body))
    if iseed is not None:
        c = crc32c(iseed, body[:off + len(items) * 8])
        c = crc32c(c, bytes(4))
        c = crc32c(c, bytes(4))
        body += bytes(4) + struct.pack("<I", c)
    return body + bytes(bs - len(body))

# The jbd2 journal

MAGIC = 0xC03B3998

class Geom:
    def __init__(self, jsb):
        (self.magic, self.btype, _, self.bs, self.maxlen, self.first, self.seq, self.start,
         self.errno) = struct.unpack_from(">IIIIIIIIi", jsb, 0)
        v2 = self.btype == 4
        self.compat, self.incompat, self.ro = struct.unpack_from(">III", jsb, 0x24) if v2 else (0, 0, 0)
        self.uuid = jsb[0x30:0x40]
        self.csum = 3 if self.incompat & 0x10 else 2 if self.incompat & 0x8 else 0
        self.wide = bool(self.incompat & 0x2)
        self.seed = crc32c(M32, self.uuid)
        self.tag = 16 if self.csum == 3 else 8 + (4 if self.wide else 0) + (2 if self.csum == 2 else 0)
        self.tail = 4 if self.csum else 0

    def next(self, p):
        p += 1
        return self.first if p >= self.maxlen else p

def jsb_with(jsb, start, seq, set_incompat=0):
    b = bytearray(jsb)
    struct.pack_into(">II", b, 0x18, seq & M32, start)
    if set_incompat:
        struct.pack_into(">I", b, 0x28, struct.unpack_from(">I", b, 0x28)[0] | set_incompat)
    inc = struct.unpack_from(">I", b, 0x28)[0]
    if struct.unpack_from(">I", b, 4)[0] == 4 and inc & 0x18:
        struct.pack_into(">I", b, 0xFC, 0)
        struct.pack_into(">I", b, 0xFC, crc32c(M32, bytes(b[:1024])))
    return bytes(b)

def _hdr(kind, seq):
    return struct.pack(">III", MAGIC, kind, seq & M32)

def _seal(g, body):
    body += bytes(g.bs - g.tail - len(body))
    if g.tail:
        body += struct.pack(">I", crc32c(crc32c(g.seed, body), bytes(4)))
    return body

def tag_csum(g, seq, data):
    c = crc32c(crc32c(g.seed, struct.pack(">I", seq & M32)), data)
    return c if g.csum == 3 else c & 0xFFFF if g.csum == 2 else 0

def desc_block(g, seq, tags, uuid):
    body = _hdr(1, seq)
    for k, (blk, flags, cs) in enumerate(tags):
        lo, hi = blk & M32, blk >> 32
        if g.csum == 3:
            body += struct.pack(">IIII", lo, flags, hi, cs)
        else:
            body += struct.pack(">IHH", lo, cs, flags) + (struct.pack(">I", hi) if g.wide else b"") + (bytes(2) if g.csum == 2 else b"")
        if not flags & 2:
            body += uuid
    return _seal(g, body)

def revoke_block(g, seq, blocks):
    ents = b"".join(struct.pack(">Q" if g.wide else ">I", b) for b in blocks)
    return _seal(g, _hdr(5, seq) + struct.pack(">I", 16 + len(ents)) + ents)

def commit_block(g, seq, sec, nsec):
    body = _hdr(2, seq) + bytes(36) + struct.pack(">QI", sec, nsec)
    body += bytes(g.bs - len(body))
    if g.csum:
        b = bytearray(body)
        struct.pack_into(">I", b, 16, crc32c(g.seed, bytes(b)))
        body = bytes(b)
    return body

def transaction(g, seq, writes, revokes, sec=0, nsec=0, uuid=None):
    """the log blocks of one transaction, as the package's writer lays them
    out: revoke blocks, descriptors with their data, the commit"""
    uuid = g.uuid if uuid is None else uuid
    out = []
    rcap = (g.bs - 16 - g.tail) // (8 if g.wide else 4)
    for k in range(0, len(revokes), rcap):
        out.append(revoke_block(g, seq, revokes[k:k + rcap]))
    dcap = (g.bs - 12 - g.tail - 16) // g.tag
    for k in range(0, len(writes), dcap):
        group = writes[k:k + dcap]
        tags, datas = [], []
        for j, (blk, data) in enumerate(group):
            esc = data[:4] == struct.pack(">I", MAGIC)
            stored = bytes(4) + data[4:] if esc else data
            flags = (1 if esc else 0) | (2 if j else 0) | (8 if j == len(group) - 1 else 0)
            tags.append((blk, flags, tag_csum(g, seq, stored)))
            datas.append(stored)
        out.append(desc_block(g, seq, tags, uuid))
        out += datas
    out.append(commit_block(g, seq, sec, nsec))
    return out

def _tags(g, blk):
    p, end, tags = 12, g.bs - g.tail, []
    while p + g.tag <= end:
        if g.csum == 3:
            lo, flags, hi, cs = struct.unpack_from(">IIII", blk, p)
        else:
            lo, cs, flags = struct.unpack_from(">IHH", blk, p)
            hi = struct.unpack_from(">I", blk, p + 8)[0] if g.wide else 0
        tags.append(((hi & 0xFFFF) << 32 | lo if g.wide else lo, flags, cs))
        p += g.tag + (0 if flags & 2 else 16)
        if flags & 8 or p + g.tag > end:
            break
    return tags

def _tail_ok(g, blk, verify):
    if not (verify and g.csum):
        return True
    return struct.unpack_from(">I", blk, g.bs - 4)[0] == crc32c(crc32c(g.seed, blk[:g.bs - 4]), bytes(4))

def recover(g, read, verify=True, skip_bad=True):
    """(writes in replay order, transactions, skipped, next ID), or a
    string naming a failure; read(p) is log block p"""
    if g.start == 0:
        return [], 0, 0, g.seq
    p, seq, txs, cur = g.start, g.seq, [], ([], [])
    for _ in range(g.maxlen):
        blk = read(p)
        m, kind, s = struct.unpack_from(">III", blk, 0)
        if m != MAGIC or s != seq & M32:
            break
        if kind == 1:
            if not _tail_ok(g, blk, verify):
                return "Ext4BadLogCsum"
            q = g.next(p)
            for t in _tags(g, blk):
                cur[0].append((t, q))
                q = g.next(q)
            p = q
        elif kind == 5:
            n = struct.unpack_from(">I", blk, 12)[0]
            if not _tail_ok(g, blk, verify) or n < 16 or n > g.bs - g.tail:
                return "Ext4BadLogCsum"
            w = 8 if g.wide else 4
            for k in range(16, 16 + (n - 16) // w * w, w):
                v = struct.unpack_from(">Q" if g.wide else ">I", blk, k)[0]
                cur[1].append((v & 0xFFFFFFFFFFFF) if g.wide else v)
            p = g.next(p)
        elif kind == 2:
            if verify and g.csum:
                b = bytearray(blk)
                struct.pack_into(">I", b, 16, 0)
                if crc32c(g.seed, bytes(b)) != struct.unpack_from(">I", blk, 16)[0]:
                    break
            txs.append((seq, cur))
            cur, seq, p = ([], []), seq + 1, g.next(p)
        else:
            break
    revoked = {}
    for s, (puts, rvs) in txs:
        for b in rvs:
            revoked[b] = max(revoked.get(b, -1), s)
    out, skipped = [], 0
    for s, (puts, rvs) in txs:
        for (blkno, flags, cs), src in puts:
            if revoked.get(blkno, -1) >= s:
                continue
            data = read(src)
            if verify and g.csum and tag_csum(g, s, data) != cs:
                if not skip_bad:
                    return "Ext4ReplayCsum"
                skipped += 1
                continue
            if flags & 1:
                data = struct.pack(">I", MAGIC) + data[4:]
            out.append((blkno, data))
    nxt = (txs[-1][0] + 2) if txs else g.seq + 1
    return out, len(txs), skipped, nxt

# the superblock with incompat bits changed and its checksum resealed
def super_with(sb, set_bits=0, clear_bits=0):
    b = bytearray(sb)
    inc = struct.unpack_from("<I", b, 0x60)[0]
    struct.pack_into("<I", b, 0x60, (inc | set_bits) & ~clear_bits & M32)
    if struct.unpack_from("<I", b, 0x64)[0] & 0x400:
        struct.pack_into("<I", b, 0x3FC, crc32c(M32, bytes(b[:0x3FC])))
    return bytes(b)
