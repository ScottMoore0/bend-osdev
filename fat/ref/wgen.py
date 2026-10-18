#!/usr/bin/env python3
"""Differential test of bend-osdev-fat's writer (write.bend, format.bend).

  wgen.py SEED WORK    writes ref/wcases-NN.bend (one Bend program per case:
                       an image, a sequence of operations run through the
                       package, one line printed per operation, then the
                       blocks the package wrote dumped into WORK) and
                       ref/wexpected.txt (the lines the model below prints);
  wgen.py check WORK   puts each dump back into its image and checks it:
                       byte for byte against the model's image, with
                       fsck.fat -n, with mdir and mtype (mtools) against the
                       model's tree, and with gen.py's reader.

The model (Model) is a FAT writer written here from Microsoft's "FAT:
General Overview of On-Disk Format" (version 1.03) by the package's author,
so it is not independent of the package's reading of the specification; it
works on a bytearray image and makes the same documented choices as the
package (first fit from the FSInfo hint, where a new entry run goes, what
format writes, which FAT sectors are rewritten). fsck.fat and mtools are the
independent checks: every image the package writes must pass fsck.fat -n,
and mtools must list and read back what the model says was written.

The cases: volumes formatted by the package (FAT12, FAT16 and FAT32, sector
sizes 512 to 4096, a small fixed root, a volume filled until it is full) and
volumes made by mkfs.fat and filled by mcopy and mmd, each given a random
sequence of operations: creating files and directories (short names, long
names, names that need numeric tails, invalid names), writing at random
offsets (gaps past the end), appending, truncating both ways, deleting,
removing empty and non-empty directories, renaming within and across
directories (and into itself), setting times and attributes (read-only
files refused), listing, reading and looking up paths.
"""
import json, os, random, shutil, struct, subprocess, sys, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen as G

BLOCK = 512
FatErr = G.FatErr
EOC = G.EOC
BAD = G.BAD
MASK = {12: 0xFFF, 16: 0xFFFF, 32: 0x0FFFFFFF}

LONG_BAD = set([34, 42, 47, 58, 60, 62, 63, 92, 124])
SHORT_BAD = set([34, 42, 43, 44, 46, 47, 58, 59, 60, 61, 62, 63, 91, 92, 93, 124])

def short_char(c):
    return 32 < c < 127 and c not in SHORT_BAD

def upper(c):
    return c - 32 if 97 <= c <= 122 else c

def le16(v):
    return struct.pack("<H", v & 0xFFFF)

def le32(v):
    return struct.pack("<I", v & 0xFFFFFFFF)

def h32(data):
    return G.h32(data)

def gen_bytes(n, seed):
    """The harness's test data: a linear congruential generator."""
    out = bytearray(n)
    x = seed & 0xFFFFFFFF
    for i in range(n):
        x = (x * 1103515245 + 12345) & 0xFFFFFFFF
        out[i] = (x >> 16) & 255
    return bytes(out)

# ---------------------------------------------------------------- names

def codes(s):
    return [ord(c) for c in s]

def text(xs):
    return "".join(chr(c) for c in xs)

def trim(xs):
    i = 0
    while i < len(xs) and xs[i] == 32:
        i += 1
    xs = xs[i:]
    j = len(xs)
    while j > 0 and xs[j - 1] in (32, 46):
        j -= 1
    return xs[:j]

def check_name(s):
    xs = trim(codes(s))
    n = len(G.units_of(text(xs)))
    if not (0 < n <= 255 and all(c >= 32 and c not in LONG_BAD for c in xs)):
        raise FatErr("bad name")
    return text(xs)

def name11(base, ext):
    return bytes((base + [32] * 8)[:8] + (ext + [32] * 3)[:3])

def basis(xs):
    conv = [u if (u == 32 or u == 46 or short_char(u)) else 95 for u in map(upper, xs)]
    s = [c for c in conv if c != 32]
    i = 0
    while i < len(s) and s[i] == 46:
        i += 1
    s = s[i:]
    base = s[:s.index(46)] if 46 in s else s
    ext = s[len(s) - s[::-1].index(46):] if 46 in s else []
    return base[:8], ext[:3]

def has_lower(xs):
    return any(97 <= c <= 122 for c in xs)

def has_upper(xs):
    return any(65 <= c <= 90 for c in xs)

def make_alias(nt_case, name, taken):
    """(short name, NT flags, long-name units or None) for a new entry."""
    xs = codes(name)
    s = G.short_of(name)
    if s is not None and s not in taken:
        base = xs[:xs.index(46)] if 46 in xs else xs
        ext = xs[len(xs) - xs[::-1].index(46):] if 46 in xs else []
        if nt_case:
            if (has_lower(base) and has_upper(base)) or (has_lower(ext) and has_upper(ext)):
                return s, 0, G.units_of(name)
            return s, (8 if has_lower(base) else 0) | (16 if has_lower(ext) else 0), None
        if has_lower(base) or has_lower(ext):
            return s, 0, G.units_of(name)
        return s, 0, None
    b, e = basis(xs)
    for n in range(1, 1000000):
        tail = [126] + codes(str(n))
        cand = name11(b[:max(0, 8 - len(tail))] + tail, e)
        if cand not in taken:
            return cand, 0, G.units_of(name)
    raise FatErr("no short name free")

def lfn_entries(units, short11):
    k = (len(units) + 12) // 13
    chk = G.lfn_checksum(short11)
    out = []
    for i in range(k, 0, -1):
        piece = units[(i - 1) * 13:i * 13]
        if len(piece) < 13:
            piece = piece + [0] + [0xFFFF] * (12 - len(piece))
        e = bytearray(32)
        e[0] = i | (0x40 if i == k else 0)
        for j in range(5):
            struct.pack_into("<H", e, 1 + 2 * j, piece[j])
        e[11], e[12], e[13] = 0x0F, 0, chk
        for j in range(6):
            struct.pack_into("<H", e, 14 + 2 * j, piece[5 + j])
        for j in range(2):
            struct.pack_into("<H", e, 28 + 2 * j, piece[11 + j])
        out.append(bytes(e))
    return out

# ---------------------------------------------------------------- times

def enc_date(y, m, d):
    return (((y - 1980) & 127) << 9) | ((m & 15) << 5) | (d & 31)

def enc_time(h, mi, s):
    return ((h & 31) << 11) | ((mi & 63) << 5) | ((s // 2) & 31)

class Clock:
    def __init__(self, y=1980, mo=1, d=1, h=0, mi=0, s=0, tenth=0):
        self.y, self.mo, self.d, self.h, self.mi, self.s, self.tenth = y, mo, d, h, mi, s, tenth

    def date(self):
        return enc_date(self.y, self.mo, self.d)

    def time(self):
        return enc_time(self.h, self.mi, self.s)

    def bend(self):
        return "X.FatClock{R.FatDate{%d, %d, %d}, R.FatTime{%d, %d, %d}, %d}" % (self.y, self.mo, self.d, self.h, self.mi, self.s, self.tenth)

def dirent(name, attr, nt, tenth, ctime, cdate, adate, cluster, wtime, wdate, size):
    return name + bytes([attr & 255, nt & 255, tenth & 255]) + struct.pack("<HHHHHHHI", ctime, cdate, adate, (cluster >> 16) & 0xFFFF, wtime, wdate, cluster & 0xFFFF, size)

def new_entry(name, nt, attr, cluster, size, now):
    d, t = now.date(), now.time()
    return dirent(name, attr, nt, now.tenth, t, d, d, cluster, t, d, size)

def written(raw, cluster, size, now):
    e = bytearray(raw)
    e[11] |= 0x20
    struct.pack_into("<H", e, 18, now.date())
    struct.pack_into("<H", e, 20, (cluster >> 16) & 0xFFFF)
    struct.pack_into("<H", e, 22, now.time())
    struct.pack_into("<H", e, 24, now.date())
    struct.pack_into("<H", e, 26, cluster & 0xFFFF)
    struct.pack_into("<I", e, 28, size & 0xFFFFFFFF)
    return bytes(e)

# ---------------------------------------------------------------- format

FMT_DEFAULT = dict(bps=512, spc=0, rsvd=0, nfats=2, rootent=512, media=0xF8, spt=63, heads=255, hidden=0, drive=0x80, volid=0, label=b"NO NAME    ", oem=b"MSWIN4.1", fsinfo=1, backup=6)

def fmt_bend(o):
    return "K.FatFormatOptions{%d, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d, B.Octets.of_string(\"%s\"), B.Octets.of_string(\"%s\"), %d, %d}" % (
        o["bps"], o["spc"], o["rsvd"], o["nfats"], o["rootent"], o["media"], o["spt"], o["heads"], o["hidden"], o["drive"], o["volid"],
        o["label"].decode(), o["oem"].decode(), o["fsinfo"], o["backup"])

def fit(b, n, pad):
    return (bytes(b) + bytes([pad]) * n)[:n]

def boot_sector(kind, bps, spc, rsvd, nfats, rootent, tot, media, fatsz, o):
    f32 = kind == 32
    small = tot < 65536 and not f32
    head = (b"\xeb\x58\x90" if f32 else b"\xeb\x3c\x90") + fit(o["oem"], 8, 32)
    head += struct.pack("<HBHBHHBHHHII", bps, spc, rsvd, nfats, rootent, tot if small else 0, media, 0 if f32 else fatsz, o["spt"], o["heads"], o["hidden"], 0 if small else tot)
    ext = bytes([o["drive"], 0, 41]) + le32(o["volid"]) + fit(o["label"], 11, 32) + fit(("FAT%d" % kind).encode(), 8, 32)
    if f32:
        head += struct.pack("<IHHIHH", fatsz, 0, 0, 2, o["fsinfo"], o["backup"]) + bytes(12)
    b = fit(head + ext, 510, 0) + b"\x55\xaa" + bytes(max(0, bps - 512))
    return b

def fsinfo_sector(free, nxt, bps):
    s = le32(0x41615252) + bytes(480) + le32(0x61417272) + le32(free) + le32(nxt) + bytes(12) + le32(0xAA550000)
    return s + bytes(max(0, bps - 512))

def mount_check(b):
    """The reader's checks on a boot sector (gen.py's Reader.mount)."""
    img = bytearray(b) + bytearray(512)
    r = G.Reader(img)
    return r.mount_bpb() if hasattr(r, "mount_bpb") else None

def layout(kind, tot, o):
    bps = o["bps"]
    rsvd = o["rsvd"] or (32 if kind == 32 else 1)
    per = bps // 32
    rootent = 0 if kind == 32 else ((o["rootent"] + per - 1) // per) * per
    nfats, fsinfo, bk = o["nfats"], o["fsinfo"], o["backup"]
    rootsecs = rootent * 32 // bps if bps else 0
    ok = (bps in (512, 1024, 2048, 4096) and 0 < nfats < 256 and (kind == 32 or 0 < rootent < 65536) and 0 < rsvd < 65536
          and (kind != 32 or (0 < fsinfo < rsvd and 0 < bk and bk + 1 < rsvd)) and tot <= 0xFFFFFFFF)
    if not ok:
        raise FatErr("bad format parameter")
    spc0 = o["spc"]
    spcs = [1, 2, 4, 8, 16, 32, 64, 128] if spc0 == 0 else ([spc0] if spc0 in (1, 2, 4, 8, 16, 32, 64, 128) else [])
    b = kind
    first = None
    chosen = None
    for spc in spcs:
        data = max(0, tot - (rsvd + rootsecs))
        den = 8 * bps * spc + b * nfats
        fatsz = ((data + 2 * spc) * b + den - 1) // den
        c = max(0, data - nfats * fatsz) // spc
        if spc * bps > 32768:
            break
        if 0 < c <= 268435445 and G.spec_type(c) == kind and rsvd + nfats * fatsz + rootsecs < tot:
            chosen = (spc, fatsz, c)
            break
        if first is None:
            first = (spc, fatsz, c)
    if chosen is None:
        if first is None:
            raise FatErr("bad format parameter")
        raise FatErr("cluster count %d outside the FAT type" % first[2])
    spc, fatsz, c = chosen
    boot = boot_sector(kind, bps, spc, rsvd, nfats, rootent, tot, o["media"], fatsz, o)
    # the reader's own checks on the boot sector, as format does
    r = G.Reader(bytearray(boot) + bytearray(1024))
    try:
        r.mount()
    except FatErr:
        raise
    if r.kind != kind or r.count != c:
        raise FatErr("cluster count %d outside the FAT type" % c)
    return dict(kind=kind, bps=bps, spc=spc, rsvd=rsvd, nfats=nfats, rootent=rootent, rootsecs=rootsecs, fatsz=fatsz, clusters=c, boot=boot, tot=tot)

def format_image(img, kind, tot, o):
    L = layout(kind, tot, o)
    bps, rsvd, fatsz, nfats = L["bps"], L["rsvd"], L["fatsz"], L["nfats"]
    def put(off, data):
        img[off:off + len(data)] = data
    put(0, bytes(rsvd * bps))
    put(0, L["boot"])
    if kind == 32:
        info = fsinfo_sector(L["clusters"] - 1, 3, bps)
        put(o["fsinfo"] * bps, info)
        put(o["backup"] * bps, L["boot"])
        put((o["backup"] + 1) * bps, info)
    head = {12: bytes([o["media"], 255, 255]), 16: bytes([o["media"], 255, 255, 255]),
            32: bytes([o["media"], 255, 255, 15, 255, 255, 255, 15, 255, 255, 255, 15])}[kind]
    for i in range(nfats):
        at = (rsvd + i * fatsz) * bps
        put(at, bytes(fatsz * bps))
        put(at, head)
    root = (rsvd + nfats * fatsz) * bps
    data_start = root + L["rootsecs"] * bps
    if kind == 32:
        at, n = data_start, L["spc"] * bps
    else:
        at, n = root, L["rootent"] * 32
    put(at, bytes(n))
    lab = fit(o["label"], 11, 32)
    if lab != b"NO NAME    ":
        put(at, dirent(lab, 8, 0, 0, 0, 33, 33, 0, 0, 33, 0))
    return L["clusters"]

# ---------------------------------------------------------------- the model

class Node:
    def __init__(self, long, raw, span):
        self.n = G.Node(long, raw)
        self.raw, self.span = raw, span

class View:
    pass

class Model:
    """The writer on a bytearray image."""

    def __init__(self, img):
        self.img = img
        self.opened = False
        self.clock = Clock()
        self.nt_case, self.from_hint, self.read_only = False, True, True

    # -- opening

    def open(self, nt_case, from_hint, read_only):
        r = G.Reader(self.img)
        r.mount()
        b = bytes(self.img[0:512])
        bps, spc, rsvd, nfats, rootent = struct.unpack_from("<HBHBH", b, 11)
        flags = struct.unpack_from("<H", b, 40)[0]
        fsinfo = struct.unpack_from("<H", b, 48)[0]
        self.r = r
        self.kind, self.bps, self.spc, self.cb = r.kind, r.bps, r.spc, r.cbytes
        self.count = r.count + 2
        self.fat_start, self.nfats = r.fat_start, nfats
        fatsz = struct.unpack_from("<H", b, 22)[0] or struct.unpack_from("<I", b, 36)[0]
        self.fat_bytes = fatsz * bps
        self.fat0 = rsvd * bps
        self.mirrored = self.kind != 32 or not (flags & 128)
        self.root_start, self.rootent, self.data_start = r.root_start, r.rootent, r.data_start
        self.root_cluster = r.root_cluster
        self.fsinfo_at = fsinfo * bps
        self.map = [self.fat_entry(n) for n in range(self.count)]
        self.free = sum(1 for n in range(2, self.count) if self.map[n] == 0)
        self.info, self.hint = False, 2
        if self.kind == 32:
            s = bytes(self.img[self.fsinfo_at:self.fsinfo_at + 512])
            if len(s) == 512:
                lead, = struct.unpack_from("<I", s, 0)
                st, fr, nxt = struct.unpack_from("<III", s, 484)
                tr, = struct.unpack_from("<I", s, 508)
                if (lead, st, tr) == (0x41615252, 0x61417272, 0xAA550000):
                    self.info = True
                    self.hint = nxt if 2 <= nxt < self.count else 2
        self.dirty = []
        self.nt_case, self.from_hint, self.read_only = nt_case, from_hint, read_only
        self.opened = True
        return "ok %d %d" % (self.free, self.hint)

    def fat_entry(self, n):
        k = self.kind
        if k == 12:
            off = self.fat_start + n + n // 2
            w = self.img[off] | self.img[off + 1] << 8
            return w >> 4 if n & 1 else w & 0xFFF
        if k == 16:
            return struct.unpack_from("<H", self.img, self.fat_start + 2 * n)[0]
        return struct.unpack_from("<I", self.img, self.fat_start + 4 * n)[0] & 0x0FFFFFFF

    # -- the map

    def get(self, n):
        return self.map[n] if n < self.count else 0

    def set(self, n, v):
        self.map[n] = v & MASK[self.kind]

    def wrap(self, c):
        return c if 2 <= c < self.count else 2

    def is_free(self, c):
        return 2 <= c < self.count and self.get(c) == 0

    def find_free(self, h):
        c = self.wrap(h)
        fuel = max(0, self.count - 3)
        while True:
            if self.is_free(c):
                return c
            if fuel == 0:
                return None
            fuel -= 1
            c = self.wrap(c + 1)

    def claim(self, k, start):
        found = self.find_free(start)
        cs = []
        for _ in range(k):
            if found is None:
                raise FatErr("disk full")
            c = found
            self.set(c, EOC[self.kind])
            found = self.find_free(c + 1)
            cs.append(c)
        return cs

    def start(self):
        return self.hint if self.from_hint else 2

    def took(self, cs, extra):
        self.free -= len(cs)
        self.hint = self.wrap((cs[-1] if cs else self.hint - 1) + 1)
        self.dirty += cs + extra

    def grow(self, chain, k):
        if k == 0:
            return chain, []
        if not chain:
            cs = self.claim(k, self.start())
            for a, b in zip(cs, cs[1:]):
                self.set(a, b)
            self.took(cs, [])
            return cs, cs
        last = chain[-1]
        cs = self.claim(k, self.start())
        prev = last
        for c in cs:
            self.set(prev, c)
            prev = c
        self.took(cs, [last])
        return chain + cs, cs

    def release(self, cs):
        for c in cs:
            self.set(c, 0)
        self.free += len(cs)
        self.dirty += cs

    def cut(self, c):
        self.set(c, EOC[self.kind])
        self.dirty.append(c)

    def chain(self, start):
        if start == 0:
            return []
        if not (2 <= start < self.count):
            raise FatErr("cluster out of range %d" % start)
        fuel = max(0, self.count - 2)
        out, c = [], start
        while True:
            if fuel == 0:
                raise FatErr("chain loops")
            fuel -= 1
            v = self.get(c)
            if v == 0:
                raise FatErr("free cluster in chain %d" % c)
            if v == BAD[self.kind]:
                raise FatErr("bad cluster in chain %d" % c)
            if v > BAD[self.kind]:
                out.append(c)
                return out
            if not (v >= 2 and v < self.count):
                raise FatErr("cluster out of range %d" % v)
            out.append(c)
            c = v

    # -- flushing

    def encode_sector(self, s, old):
        k, bps = self.kind, self.bps
        out = bytearray(old)
        if k == 16:
            first = s * bps // 2
            for i in range(bps // 2):
                n = first + i
                if n < self.count:
                    out[2 * i:2 * i + 2] = le16(self.get(n))
        elif k == 32:
            first = s * bps // 4
            for i in range(bps // 4):
                n = first + i
                if n < self.count:
                    was = struct.unpack_from("<I", old, 4 * i)[0]
                    out[4 * i:4 * i + 4] = le32((was & 0xF0000000) | (self.get(n) & 0x0FFFFFFF))
        else:
            for j in range(bps):
                o = s * bps + j
                kk, r = o // 3, o % 3
                e0, e1 = 2 * kk, 2 * kk + 1
                v0, v1 = self.get(e0), self.get(e1)
                in0, in1 = e0 < self.count, e1 < self.count
                ob = old[j]
                b1 = (((v0 >> 8) & 15) if in0 else (ob & 15)) | (((v1 & 15) << 4) if in1 else (ob & 240))
                if r == 0:
                    out[j] = (v0 & 255) if in0 else ob
                elif r == 1:
                    out[j] = b1
                else:
                    out[j] = ((v1 >> 4) & 255) if in1 else ob
        return bytes(out)

    def flush(self):
        width = 4 if self.kind == 32 else 2
        secs = set()
        for c in self.dirty:
            off = c + c // 2 if self.kind == 12 else c * width
            secs.add(off // self.bps)
            secs.add((off + width - 1) // self.bps)
        for s in sorted(secs):
            old = bytes(self.img[self.fat_start + s * self.bps:self.fat_start + (s + 1) * self.bps])
            new = self.encode_sector(s, old)
            if self.mirrored:
                for i in range(self.nfats):
                    at = self.fat0 + i * self.fat_bytes + s * self.bps
                    self.img[at:at + self.bps] = new
            else:
                at = self.fat_start + s * self.bps
                self.img[at:at + self.bps] = new
        if self.info and self.dirty:
            self.img[self.fsinfo_at + 488:self.fsinfo_at + 496] = le32(self.free) + le32(self.hint)
        self.dirty = []

    # -- directories

    def coff(self, c):
        return self.data_start + (c - 2) * self.cb

    def chain_sectors(self, cs):
        return [self.coff(c) + j * self.bps for c in cs for j in range(self.spc)]

    def view(self, d):
        """d: None for the root, else a directory's first cluster."""
        v = View()
        v.dir = d
        per = self.bps // 32
        if d is None and self.kind != 32:
            v.fixed, v.clusters = True, []
            n = (self.rootent * 32 + self.bps - 1) // self.bps
            v.sectors = [self.root_start + k * self.bps for k in range(n)]
            v.slots = self.rootent
        else:
            c = self.root_cluster if d is None else d
            v.fixed = False
            v.clusters = self.chain(c)
            v.sectors = self.chain_sectors(v.clusters)
            v.slots = len(v.sectors) * per
        v.holes, end = [], None
        st = {"run": None, "nodes": [], "ended": False, "seen": 0}
        left, i = v.slots, 0
        for off in v.sectors:
            if end is not None:
                break
            k = min(per, left)
            data = bytes(self.img[off:off + k * 32])
            for j in range(k):
                b0 = data[32 * j]
                if end is None:
                    if b0 == 0:
                        end = i + j
                    elif b0 == 0xE5:
                        v.holes.append(i + j)
            for j in range(k):
                self.scan_entry(st, data[32 * j:32 * j + 32])
            left -= k
            i += k
        v.end = v.slots if end is None else end
        v.nodes = st["nodes"]
        return v

    def scan_entry(self, st, raw):
        """dir.bend's FatScan.step, strict, with each node's span."""
        if st["ended"]:
            return
        if st["seen"] >= 65536:
            raise FatErr("directory too long")
        st["seen"] += 1
        at = st["seen"] - 1
        b0 = raw[0]
        if b0 == 0:
            if st["run"] is not None:
                raise FatErr("long name sequence broken")
            st["ended"] = True
        elif b0 == 0xE5:
            if st["run"] is not None:
                raise FatErr("long name sequence broken")
        elif raw[11] & 0x3F == 0x0F:
            ordv, chk = raw[0], raw[13]
            us = [struct.unpack_from("<H", raw, o)[0] for o in (1, 3, 5, 7, 9, 14, 16, 18, 20, 22, 24, 28, 30)]
            run = st["run"]
            if ordv & 0x40:
                if run is not None:
                    raise FatErr("long name sequence broken")
                n = ordv & 63
                if 1 <= n <= 20:
                    st["run"] = [n - 1, chk, us, at]
                else:
                    raise FatErr("long name sequence broken")
            else:
                if run is None:
                    raise FatErr("long name sequence broken")
                if not (ordv == run[0] and run[0] != 0):
                    raise FatErr("long name sequence broken")
                if chk != run[1]:
                    raise FatErr("long name checksum mismatch")
                st["run"] = [run[0] - 1, chk, us + run[2], run[3]]
        else:
            run, long, first = st["run"], [], at
            st["run"] = None
            if run is not None:
                if run[0] != 0:
                    raise FatErr("long name sequence broken")
                if G.lfn_checksum(raw[0:11]) != run[1]:
                    raise FatErr("long name checksum mismatch")
                long = run[2]
                if 0 in long:
                    long = long[:long.index(0)]
                first = run[3]
            attr = raw[11]
            listed = not (attr & 0x08 and not attr & 0x10) and raw[0] != 0x2E
            if listed:
                st["nodes"].append(Node(long, raw, (first, at)))

    def find(self, v, name):
        want = G.units_of(name)
        short = G.short_of(name)
        for nd in v.nodes:
            if (nd.n.long and G.same(want, nd.n.long)) or (short is not None and G.same(list(short), list(nd.n.name11))):
                return nd
        return None

    def place_index(self, v, k):
        start, ln, prev = 0, 0, 0
        for h in v.holes:
            join = ln > 0 and prev + 1 == h
            s2 = start if join else h
            l2 = (ln if join else 0) + 1
            if l2 == k:
                return s2
            start, ln, prev = s2, l2, h
        if prev + 1 == v.end:
            return start if ln > 0 else v.end
        return v.end

    def place(self, v, k):
        """(sectors, start, added clusters); may grow the directory."""
        start = self.place_index(v, k)
        need = start + k
        if need > 65536:
            raise FatErr("directory full")
        if need <= v.slots:
            return list(v.sectors), start, []
        if v.fixed:
            raise FatErr("root directory full")
        per = self.cb // 32
        chain, added = self.grow(v.clusters, (need - v.slots + per - 1) // per)
        return list(v.sectors) + self.chain_sectors(added), start, added

    def slot(self, sectors, i):
        per = self.bps // 32
        k = i // per
        return (sectors[k] if k < len(sectors) else 0) + (i % per) * 32

    def put_entries(self, sectors, start, added, es):
        for c in added:
            self.img[self.coff(c):self.coff(c) + self.cb] = bytes(self.cb)
        for j, e in enumerate(es):
            off = self.slot(sectors, start + j)
            self.img[off:off + 32] = e

    def erase(self, v, nd):
        a, b = nd.span
        for i in range(a, b + 1):
            off = self.slot(v.sectors, i)
            self.img[off] = 0xE5

    def rewrite(self, v, nd, raw):
        off = self.slot(v.sectors, nd.span[1])
        self.img[off:off + 32] = raw

    # -- paths

    @staticmethod
    def parts(path):
        return [text(trim(codes(p))) for p in path.split("/") if p]

    @staticmethod
    def dir_of(nd):
        c = nd.n.cluster
        return None if c == 0 else c

    def walk(self, parts):
        here, seen = None, [0]
        for c in parts:
            v = self.view(here)
            nd = self.find(v, c)
            if nd is None:
                raise FatErr("not found")
            if not nd.n.is_dir():
                raise FatErr("not a directory")
            here = self.dir_of(nd)
            seen.append(0 if here is None else here)
        return here, seen

    def locate(self, path):
        ps = self.parts(path)
        if not ps:
            return None, None
        d, _ = self.walk(ps[:-1])
        v = self.view(d)
        nd = self.find(v, ps[-1])
        if nd is None:
            raise FatErr("not found")
        return v, nd

    def parent(self, path):
        ps = self.parts(path)
        if not ps:
            raise FatErr("name exists")
        name = check_name(ps[-1])
        d, seen = self.walk(ps[:-1])
        return self.view(d), seen, name

    def entries(self, alias, raw):
        short, nt, long = alias
        es = lfn_entries(long, short) if long else []
        return es + [raw]

    # -- operations (each answers its line's text)

    def changed(self, fn):
        snap = (list(self.map), self.free, self.hint, list(self.dirty))
        try:
            fn()
            return "ok %d" % self.free
        except FatErr as e:
            self.map, self.free, self.hint, self.dirty = snap
            return "error " + str(e)

    def make(self, path, is_dir):
        def go():
            v, seen, name = self.parent(path)
            if self.find(v, name) is not None:
                raise FatErr("name exists")
            alias = make_alias(self.nt_case, name, [nd.n.name11 for nd in v.nodes])
            c = 0
            if is_dir:
                ch, _ = self.grow([], 1)
                c = ch[0]
            es = self.entries(alias, new_entry(alias[0], alias[1], 0x10 if is_dir else 0x20, c, 0, self.clock))
            sectors, start, added = self.place(v, len(es))
            if is_dir:
                at = self.coff(c)
                self.img[at:at + self.cb] = bytes(self.cb)
                parent = 0 if v.dir is None else v.dir
                dots = new_entry(b".          ", 0, 0x10, c, 0, self.clock) + new_entry(b"..         ", 0, 0x10, parent, 0, self.clock)
                self.img[at:at + 64] = dots
            self.put_entries(sectors, start, added, es)
            self.flush()
        return self.changed(go)

    def at_file(self, path, write):
        v, nd = self.locate(path)
        if nd is None:
            raise FatErr("is the root directory")
        if nd.n.is_dir():
            raise FatErr("is a directory")
        if write and self.read_only and nd.n.attr & 1:
            raise FatErr("read-only file")
        return v, nd

    def put_range(self, chain, off, data):
        cs = chain[off // self.cb:]
        within = off % self.cb
        i = 0
        for c in cs:
            if i >= len(data):
                break
            k = min(self.cb - within, len(data) - i)
            at = self.coff(c) + within
            self.img[at:at + k] = data[i:i + k]
            i += k
            within = 0

    def put(self, v, nd, off, data):
        size = nd.n.size
        new = max(size, off + len(data))
        if new > 0xFFFFFFFF:
            raise FatErr("file too large")
        chain = self.chain(nd.n.cluster)
        need = max(0, -(-new // self.cb) - len(chain))
        chain, _ = self.grow(chain, need)
        if off > size:
            self.put_range(chain, size, bytes(off - size))
        self.put_range(chain, off, data)
        self.rewrite(v, nd, written(nd.raw, chain[0] if chain else 0, new, self.clock))
        self.flush()

    def write(self, path, off, data):
        def go():
            v, nd = self.at_file(path, True)
            self.put(v, nd, off, data)
        return self.changed(go)

    def append(self, path, data):
        def go():
            v, nd = self.at_file(path, True)
            self.put(v, nd, nd.n.size, data)
        return self.changed(go)

    def truncate(self, path, n):
        def go():
            v, nd = self.at_file(path, True)
            size = nd.n.size
            if n > size:
                self.put(v, nd, size, bytes(n - size))
                return
            keep = -(-n // self.cb)
            chain = self.chain(nd.n.cluster)
            self.release(chain[keep:])
            if keep > 0:
                kept = chain[:keep]
                self.cut(kept[-1] if kept else 0)
            self.rewrite(v, nd, written(nd.raw, 0 if keep == 0 else (chain[0] if chain else 0), n, self.clock))
            self.flush()
        return self.changed(go)

    def unlink(self, path):
        def go():
            v, nd = self.at_file(path, True)
            chain = self.chain(nd.n.cluster)
            self.erase(v, nd)
            self.release(chain)
            self.flush()
        return self.changed(go)

    def rmdir(self, path):
        def go():
            v, nd = self.locate(path)
            if nd is None:
                raise FatErr("is the root directory")
            if not nd.n.is_dir():
                raise FatErr("not a directory")
            d = self.dir_of(nd)
            sub = self.view(d)
            if sub.nodes:
                raise FatErr("directory not empty")
            chain = self.chain(0 if d is None else d)
            self.erase(v, nd)
            self.release(chain)
            self.flush()
        return self.changed(go)

    def rename(self, a, b):
        def go():
            va, nd = self.locate(a)
            if nd is None:
                raise FatErr("is the root directory")
            isdir = nd.n.is_dir()
            vb, seen, name = self.parent(b)
            same = va.dir == vb.dir
            if isdir and nd.n.cluster in seen:
                raise FatErr("move into itself")
            hit = self.find(vb, name)
            if hit is not None and not (same and hit.span == nd.span):
                raise FatErr("name exists")
            taken = [x.n.name11 for x in vb.nodes]
            if same and nd.n.name11 in taken:
                taken.remove(nd.n.name11)
            alias = make_alias(self.nt_case, name, taken)
            raw = bytearray(nd.raw)
            raw[0:11] = alias[0]
            raw[12] = alias[1]
            es = self.entries(alias, bytes(raw))
            sectors, start, added = self.place(vb, len(es))
            self.put_entries(sectors, start, added, es)
            self.erase(va, nd)
            if isdir and not same:
                at = self.coff(nd.n.cluster) + 32
                parent = 0 if vb.dir is None else vb.dir
                struct.pack_into("<H", self.img, at + 20, (parent >> 16) & 0xFFFF)
                struct.pack_into("<H", self.img, at + 26, parent & 0xFFFF)
            self.flush()
        return self.changed(go)

    def set_times(self, path, c, w, a):
        def go():
            v, nd = self.locate(path)
            if nd is None:
                raise FatErr("is the root directory")
            e = bytearray(nd.raw)
            e[13] = c.tenth & 255
            struct.pack_into("<HHH", e, 14, c.time(), c.date(), enc_date(*a))
            struct.pack_into("<HH", e, 22, w.time(), w.date())
            self.rewrite(v, nd, bytes(e))
        return self.changed(go)

    def set_attr(self, path, at):
        def go():
            v, nd = self.locate(path)
            if nd is None:
                raise FatErr("is the root directory")
            e = bytearray(nd.raw)
            e[11] = (e[11] & 24) | (at & 39)
            self.rewrite(v, nd, bytes(e))
        return self.changed(go)

    @staticmethod
    def show(nd):
        n = nd.n
        return "%s|%s|%d|%s|%d|%d" % (G.esc(n.name()), "D" if n.is_dir() else "F", n.size, G.esc(n.short_text()), n.attr, n.cluster)

    def ls(self, path):
        try:
            v, nd = self.locate(path)
            if nd is not None and not nd.n.is_dir():
                raise FatErr("not a directory")
            sub = self.view(None if nd is None else self.dir_of(nd))
            return "%d%s" % (len(sub.nodes), "".join(" " + self.show(x) + ";" for x in sub.nodes))
        except FatErr as e:
            return "error " + str(e)

    def read(self, path):
        try:
            v, nd = self.at_file(path, False)
            chain = self.chain(nd.n.cluster)
            size = nd.n.size
            if size == 0:
                return "0 %08x" % h32(b"")
            out = bytearray()
            cs = chain
            for c in cs:
                k = min(self.cb, size - len(out))
                out += self.img[self.coff(c):self.coff(c) + k]
                if len(out) >= size:
                    break
            if len(out) < size:
                raise FatErr("chain shorter than file")
            return "%d %08x" % (size, h32(bytes(out)))
        except FatErr as e:
            return "error " + str(e)

    def stat(self, path):
        try:
            v, nd = self.locate(path)
            return "root" if nd is None else self.show(nd)
        except FatErr as e:
            return "error " + str(e)

    # -- the tree, for the checks

    def tree(self):
        """path -> (is_dir, size, data, the path through short names) for
        every node."""
        out = {}
        def go(d, prefix, sprefix):
            for nd in self.view(d).nodes:
                p = prefix + "/" + nd.n.name()
                sp = sprefix + "/" + nd.n.short_text()
                if nd.n.is_dir():
                    out[p] = (True, 0, None, sp)
                    go(self.dir_of(nd), p, sp)
                else:
                    chain = self.chain(nd.n.cluster)
                    data = bytearray()
                    for c in chain:
                        data += self.img[self.coff(c):self.coff(c) + self.cb]
                    out[p] = (False, nd.n.size, bytes(data[:nd.n.size]), sp)
        go(None, "", "")
        return out

# ---------------------------------------------------------------- the cases

def bstr(s):
    return G.bend_str(s)

class Case:
    PER_DEF = 40

    def __init__(self, name, img, src, count):
        self.name, self.m, self.src, self.count = name, Model(img), src, count
        self.ops, self.lines = [], []

    def op(self, ctor, line):
        self.lines.append("%s.%d %s" % (self.name, len(self.ops), line))
        self.ops.append(ctor)

    def bend(self, work, k):
        """The case's defs (its operations, at most PER_DEF a def, and its
        image's blocks) and the line of main that runs it."""
        dump = os.path.join(work, self.name + ".dump")
        out = []
        n = 0
        for b in range(0, len(self.ops), self.PER_DEF):
            out.append("def c%d_ops%d() -> List<&2, H.WOp>:\n  [%s]\n" % (k, n, ", ".join(self.ops[b:b + self.PER_DEF])))
            n += 1
        lst = "c%d_ops%d()" % (k, n - 1)
        for j in reversed(range(n - 1)):
            lst = "List.append(&2, H.WOp, c%d_ops%d(), %s)" % (k, j, lst)
        nz = []
        if self.src:
            with open(self.src, "rb") as f:
                data = f.read()
            nz = [i // BLOCK for i in range(0, len(data), BLOCK) if any(data[i:i + BLOCK])]
        out.append("def c%d_blocks() -> List<&2, Nat>:\n  %s\n" % (k, G.Cases.nat_list(nz)))
        run = "    H.WRun.case(\"%s\", \"%s\", c%d_blocks(), %dn, %s, \"%s\")" % (self.name, self.src or "", k, self.count, lst, dump)
        return "\n".join(out), run

# operations, each run on the model and recorded

def op_format(cs, kind, tot, o):
    try:
        line = "ok %d" % format_image(cs.m.img, kind, tot, o)
    except FatErr as e:
        line = "error " + str(e)
    cs.op("H.WFormat{P.Fat%d{}, %dn, %s}" % (kind, tot, fmt_bend(o)), line)

def op_open(cs, nt_case=False, from_hint=True, read_only=True):
    try:
        line = cs.m.open(nt_case, from_hint, read_only)
    except FatErr as e:
        line = "error " + str(e)
    b = lambda x: "True{}" if x else "False{}"
    cs.op("H.WOpen{X.FatWOptions{%s, %s, %s}}" % (b(nt_case), b(from_hint), b(read_only)), line)

def op_clock(cs, c):
    cs.m.clock = c
    cs.op("H.WClock{%s}" % c.bend(), "clock")

def op_mkdir(cs, p):
    cs.op("H.WMkdir{%s}" % bstr(p), cs.m.make(p, True))

def op_create(cs, p):
    cs.op("H.WCreate{%s}" % bstr(p), cs.m.make(p, False))

def op_write(cs, p, off, n, seed):
    cs.op("H.WWrite{%s, %dn, %dn, %d}" % (bstr(p), off, n, seed), cs.m.write(p, off, gen_bytes(n, seed)))

def op_append(cs, p, n, seed):
    cs.op("H.WAppend{%s, %dn, %d}" % (bstr(p), n, seed), cs.m.append(p, gen_bytes(n, seed)))

def op_trunc(cs, p, n):
    cs.op("H.WTrunc{%s, %dn}" % (bstr(p), n), cs.m.truncate(p, n))

def op_unlink(cs, p):
    cs.op("H.WUnlink{%s}" % bstr(p), cs.m.unlink(p))

def op_rmdir(cs, p):
    cs.op("H.WRmdir{%s}" % bstr(p), cs.m.rmdir(p))

def op_rename(cs, a, b):
    cs.op("H.WRename{%s, %s}" % (bstr(a), bstr(b)), cs.m.rename(a, b))

def op_times(cs, p, c, w, a):
    cs.op("H.WTimes{%s, X.FatTimes{%s, %s, R.FatDate{%d, %d, %d}}}" % (bstr(p), c.bend(), w.bend(), a[0], a[1], a[2]), cs.m.set_times(p, c, w, a))

def op_attr(cs, p, a):
    cs.op("H.WAttr{%s, %d}" % (bstr(p), a), cs.m.set_attr(p, a))

def op_ls(cs, p):
    cs.op("H.WLs{%s}" % bstr(p), cs.m.ls(p))

def op_read(cs, p):
    cs.op("H.WRead{%s}" % bstr(p), cs.m.read(p))

def op_stat(cs, p):
    cs.op("H.WStat{%s}" % bstr(p), cs.m.stat(p))

# random sequences

NAMES = ["README.TXT", "readme.txt", "Read Me.txt", "notes", "NOTES", "a", "B", "kernel.elf", "BOOTX64.EFI", "efi",
         "Long File Name.txt", "Long File Name 2.txt", "Long File Name 3.txt", "longfi~1.txt", "a+b=c", "[brackets]",
         "semi;colon", "café crème.txt", "日本語の名前", "emoji \U0001F600 face", "two.dots.here", ".hidden", "x" * 13,
         "y" * 26 + ".z", "trailing dot.", " leading space", "MiXeD.TxT", "UPPER.TXT", "lower.txt", "Mixed.txt",
         "abcdefgh.ijk", "abcdefghi.jk", "a.bcde", "data file %d.bin", "LOG%d.TXT", "file%d", "Some Directory", "sub dir %d"]

def rand_name(rng):
    n = rng.choice(NAMES)
    if "%d" in n:
        n = n % rng.randrange(40)
    if rng.random() < 0.15:
        n = "".join(rng.choice("abcdefghijklmnopqrstuvwxyz0123456789 _-.") for _ in range(rng.randrange(1, 40))).strip(" .") or "z"
    return n

def flip(rng, s):
    return "".join(c.swapcase() if c.isascii() and rng.random() < 0.5 else c for c in s)

def known(m):
    """The paths of the model's tree (dirs, files) through long names, and
    some through short names."""
    dirs, files = ["/"], []
    if not m.opened:
        return dirs, files, {}
    try:
        t = m.tree()
    except FatErr:
        return dirs, files, {}
    for p, (isdir, size, data, short) in t.items():
        (dirs if isdir else files).append(p)
    return dirs, files, t

def child(rng, d, name):
    return (d.rstrip("/") + "/" + name) if d != "/" else "/" + name

def random_ops(cs, rng, n, max_write=6000):
    m = cs.m
    for step in range(n):
        dirs, files, t = known(m)
        k = rng.random()
        if k < 0.14:
            op_create(cs, child(rng, rng.choice(dirs), rand_name(rng)))
        elif k < 0.22:
            op_mkdir(cs, child(rng, rng.choice(dirs), rand_name(rng)))
        elif k < 0.36 and files:
            p = rng.choice(files)
            size = t[p][1]
            off = rng.choice([0, size, rng.randrange(size + 1), size + rng.randrange(1, 3 * m.cb)])
            op_write(cs, flip(rng, p) if rng.random() < 0.2 else p, off, rng.randrange(1, max_write), rng.randrange(1 << 31))
        elif k < 0.44 and files:
            op_append(cs, rng.choice(files), rng.randrange(0, max_write // 2), rng.randrange(1 << 31))
        elif k < 0.50 and files:
            p = rng.choice(files)
            size = t[p][1]
            op_trunc(cs, p, rng.choice([0, size // 2, max(0, size - 1), size, size + rng.randrange(1, 2 * m.cb)]))
        elif k < 0.57 and files:
            op_unlink(cs, rng.choice(files))
        elif k < 0.62 and len(dirs) > 1:
            op_rmdir(cs, rng.choice(dirs[1:]))
        elif k < 0.72 and (files or len(dirs) > 1):
            src = rng.choice(files + dirs[1:])
            to = child(rng, rng.choice(dirs), rand_name(rng) if rng.random() < 0.8 else flip(rng, src.rsplit("/", 1)[1]))
            op_rename(cs, src, to)
        elif k < 0.75 and (files or len(dirs) > 1):
            p = rng.choice(files + dirs[1:])
            c = Clock(rng.randrange(1980, 2100), rng.randrange(1, 13), rng.randrange(1, 29), rng.randrange(24), rng.randrange(60), rng.randrange(60), rng.randrange(200))
            w = Clock(rng.randrange(1980, 2100), rng.randrange(1, 13), rng.randrange(1, 29), rng.randrange(24), rng.randrange(60), rng.randrange(60))
            op_times(cs, p, c, w, (rng.randrange(1980, 2100), rng.randrange(1, 13), rng.randrange(1, 29)))
        elif k < 0.79 and files:
            op_attr(cs, rng.choice(files), rng.choice([0, 1, 2, 4, 32, 33, 39, 255]))
        elif k < 0.85:
            op_ls(cs, rng.choice(dirs + files[:1]))
        elif k < 0.92 and files:
            op_read(cs, rng.choice(files))
        elif k < 0.96:
            p = rng.choice(dirs + files + ["/no such", "/" + rand_name(rng)])
            op_stat(cs, flip(rng, p) if rng.random() < 0.5 else p)
        elif k < 0.98:
            op_clock(cs, Clock(rng.randrange(1980, 2108), rng.randrange(1, 13), rng.randrange(1, 32), rng.randrange(24), rng.randrange(60), rng.randrange(60), rng.randrange(200)))
        elif k < 0.99:
            op_create(cs, child(rng, rng.choice(dirs), rng.choice(["", "a:b", "q?", "  ", "...", "x" * 256, "tab\there"])))
        else:
            kind = rng.randrange(7)
            p = rng.choice(files + dirs)
            if kind == 0:
                op_write(cs, rng.choice(dirs), 0, 10, 1)
            elif kind == 1:
                op_unlink(cs, "/")
            elif kind == 2:
                op_rename(cs, "/", "/x")
            elif kind == 3:
                op_create(cs, "/no such dir/" + rand_name(rng))
            elif kind == 4:
                op_create(cs, child(rng, p, "under"))
            elif kind == 5:
                op_rmdir(cs, p)
            else:
                op_times(cs, "/", Clock(), Clock(), (1980, 1, 1))

def final_listing(cs):
    dirs, files, t = known(cs.m)
    for d in dirs:
        op_ls(cs, d)
    for f in files:
        op_read(cs, f)

def mtools_source(rng, work, tag, kind, kb, spc, tree):
    """An image made by mkfs.fat and filled by mmd and mcopy (an entry the
    tools refuse is left out)."""
    img = os.path.join(work, tag + ".src")
    if os.path.exists(img):
        os.unlink(img)
    subprocess.run(["mkfs.fat", "-C", img, str(kb), "-F", str(kind), "-S", "512", "-s", str(spc), "-n", "MTOOLS", "-i", "%08x" % rng.randrange(1 << 32)],
                   check=True, capture_output=True)
    env = dict(os.environ, MTOOLS_SKIP_CHECK="1", MTOOLS_NO_VFAT="0")
    def put(t, path):
        for name, val in t.items():
            sub = path + "/" + name
            if isinstance(val, dict):
                if subprocess.run(["mmd", "-i", img, "::" + sub], env=env, capture_output=True).returncode == 0:
                    put(val, sub)
            else:
                src = os.path.join(work, "src")
                with open(src, "wb") as f:
                    f.write(val)
                subprocess.run(["mcopy", "-i", img, src, "::" + sub], env=env, capture_output=True)
    put(tree, "")
    with open(img, "rb") as f:
        data = bytearray(f.read())
    return img, data

def build(seed, work):
    rng = random.Random(seed)
    cases = []
    def blank(name, kind, tot, o, nops, max_write=6000, nt=False):
        o = dict(FMT_DEFAULT, **o)
        count = tot * o["bps"] // BLOCK
        cs = Case(name, bytearray(count * BLOCK), None, count)
        op_format(cs, kind, tot, o)
        op_open(cs, nt_case=nt)
        random_ops(cs, rng, nops, max_write)
        final_listing(cs)
        cases.append(cs)
    blank("f12", 12, 2880, {}, 160)
    blank("f12r", 12, 800, {"rootent": 16, "spc": 2, "label": b"SMALL ROOT "}, 60, nt=True)
    cs = cases[-1]
    for i in range(14):
        op_create(cs, "/Root File %d.txt" % i if i % 2 else "/R%d.TXT" % i)
    op_mkdir(cs, "/full")
    random_ops(cs, rng, 20)
    final_listing(cs)
    blank("f16", 16, 20000, {"volid": 0x1234ABCD}, 150)
    cs = cases[-1]
    # fragmentation: small files, every other one deleted, then a large one
    op_mkdir(cs, "/frag")
    for i in range(30):
        op_create(cs, "/frag/f%d" % i)
        op_write(cs, "/frag/f%d" % i, 0, 700, i)
    for i in range(0, 30, 2):
        op_unlink(cs, "/frag/f%d" % i)
    op_create(cs, "/frag/big file.bin")
    op_write(cs, "/frag/big file.bin", 0, 40000, 7)
    op_rename(cs, "/frag", "/Some Directory/frag moved")
    op_mkdir(cs, "/Some Directory")
    op_rename(cs, "/frag", "/Some Directory/frag moved")
    op_read(cs, "/Some Directory/frag moved/big file.bin")
    op_ls(cs, "/Some Directory/frag moved")
    random_ops(cs, rng, 30)
    final_listing(cs)
    blank("f16k", 16, 9000, {"bps": 2048, "spc": 2, "nfats": 1}, 100)
    blank("f32", 32, 70000, {"label": b"BEND FAT32 "}, 140, max_write=20000)
    blank("f12k", 12, 300, {"bps": 4096, "rootent": 128}, 60)
    # a volume filled until it is full
    o = dict(FMT_DEFAULT, rootent=32)
    cs = Case("full", bytearray(160 * BLOCK), None, 160)
    op_format(cs, 12, 160, o)
    op_open(cs)
    for i in range(12):
        op_create(cs, "/F%d" % i)
        op_write(cs, "/F%d" % i, 0, 15000, i)
    op_mkdir(cs, "/D")
    op_unlink(cs, "/F3")
    op_write(cs, "/F11", 20000, 1, 99)
    random_ops(cs, rng, 30)
    final_listing(cs)
    cases.append(cs)
    # formats that cannot be made
    cs = Case("fbad", bytearray(64 * BLOCK), None, 64)
    op_format(cs, 16, 64, FMT_DEFAULT)
    op_format(cs, 32, 64, FMT_DEFAULT)
    op_format(cs, 12, 64, dict(FMT_DEFAULT, bps=1000))
    op_format(cs, 12, 64, dict(FMT_DEFAULT, spc=3))
    op_format(cs, 12, 64, dict(FMT_DEFAULT, spc=4))
    op_open(cs)
    op_ls(cs, "/")
    cases.append(cs)
    # images made by mkfs.fat and mcopy, updated by the package
    for i, (kind, kb, spc) in enumerate([(12, 1440, 1), (16, 9000, 4), (32, 34000, 1)]):
        tree = G.rand_tree(rng, 2, 6, 512 * spc, ascii_only=True)
        src, data = mtools_source(rng, work, "m%d" % i, kind, kb, spc, tree)
        count = len(data) // BLOCK
        cs = Case("m%d" % i, data, src, count)
        op_open(cs, from_hint=(i != 1))
        random_ops(cs, rng, 120)
        final_listing(cs)
        cases.append(cs)
    return cases

# All the cases go in one program, wcases.bend: building the writer natively
# takes about half a minute of the C compiler, so each case file would pay it
# again (every def holds at most PER_DEF operations, so each builds natively)
def write_cases(here, work, cases):
    for old in os.listdir(here):
        if old.startswith("wcases") and old.endswith(".bend"):
            os.unlink(os.path.join(here, old))
    expect, meta, defs, runs = [], [], [], []
    for k, cs in enumerate(cases):
        d, r = cs.bend(work, k)
        defs.append(d)
        runs.append(r)
        expect += cs.lines + [cs.name + " end"]
        model = os.path.join(work, cs.name + ".model")
        with open(model, "wb") as f:
            f.write(bytes(cs.m.img))
        tree = cs.m.tree() if cs.m.opened else {}
        meta.append(dict(name=cs.name, src=cs.src, count=cs.count, model=model,
                         dump=os.path.join(work, cs.name + ".dump"),
                         tree={p: [v[0], v[1], (h32(v[2]) if v[2] is not None else 0), v[3]] for p, v in tree.items()}))
    head = ["import Base", "import ../../bytes/bytes.bend as B", "import ../bpb.bend as P", "import ../dirent.bend as R",
            "import ../format.bend as K", "import ../write.bend as X", "import ./wharness.bend as H", "",
            "def str_of(xs: List<&2, U32>) -> String:\n  match xs:\n    case Nil{}:\n      \"\"\n    case Con{h, t}:\n      SCon{Char.from_u32(h), str_of(t)}\n"]
    with open(os.path.join(here, "wcases.bend"), "w", encoding="utf-8") as f:
        f.write("\n".join(head + defs) + "\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(runs) + "\n")
    with open(os.path.join(here, "wexpected.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(expect) + "\n")
    with open(os.path.join(work, "wcases.json"), "w", encoding="utf-8") as f:
        json.dump(meta, f)
    return len(expect)

# ---------------------------------------------------------------- the checks

def check(work):
    meta = json.load(open(os.path.join(work, "wcases.json"), encoding="utf-8"))
    env = dict(os.environ, MTOOLS_SKIP_CHECK="1")
    n = 0
    for c in meta:
        img = bytearray(open(c["src"], "rb").read()) if c["src"] else bytearray(c["count"] * BLOCK)
        d = open(c["dump"], "rb").read()
        for i in range(0, len(d), 516):
            b, = struct.unpack_from("<I", d, i)
            img[b * BLOCK:(b + 1) * BLOCK] = d[i + 4:i + 516]
        model = open(c["model"], "rb").read()
        if bytes(img) != model:
            diff = next(i for i in range(len(model)) if img[i] != model[i])
            sys.exit("%s: the package's image differs from the model's at byte %d (block %d): %s vs %s" % (
                c["name"], diff, diff // BLOCK, bytes(img[diff:diff + 16]).hex(), model[diff:diff + 16].hex()))
        p = os.path.join(work, c["name"] + ".img")
        with open(p, "wb") as f:
            f.write(img)
        if not c["tree"] and c["name"] == "fbad":
            n += 1
            continue
        r = subprocess.run(["fsck.fat", "-n", p], capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit("%s: fsck.fat -n refused the package's image:\n%s%s" % (c["name"], r.stdout, r.stderr))
        n += 1
        # mdir lists every path; mtype reads back every file
        listing = subprocess.run(["mdir", "-i", p, "-/", "-b", "-a", "::/"], env=env, capture_output=True, text=True)
        paths = sorted(l[3:].rstrip("/") for l in listing.stdout.splitlines() if l.startswith("::/"))
        # (mdir shows a character past U+FFFF, a surrogate pair, as "__")
        bmp = lambda q: "".join("__" if ord(ch) > 0xFFFF else ch for ch in q)
        want = sorted(bmp(q[1:]) for q in c["tree"])
        if paths != want:
            sys.exit("%s: mdir lists %s, the model %s" % (c["name"], paths, want))
        n += 1
        for q, (isdir, size, h, short) in c["tree"].items():
            if isdir:
                continue
            # (through the short names: mtools takes [ ] * ? as wildcards)
            got = subprocess.run(["mtype", "-i", p, "::" + short], env=env, capture_output=True).stdout
            if len(got) != size or h32(got) != h:
                sys.exit("%s: mtype %s gives %d bytes (%08x), the model %d (%08x)" % (c["name"], q, len(got), h32(got), size, h))
            n += 1
        # gen.py's reader agrees with the model's tree
        rd = G.Reader(img)
        rd.mount()
        for q, (isdir, size, h, short) in c["tree"].items():
            nd = rd.resolve(q)
            assert nd.is_dir() == isdir, q
            if not isdir:
                assert nd.size == size and h32(b"".join(rd.stream(nd))) == h, q
        n += 1
    print("%d image checks" % n)

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    if sys.argv[1] == "check":
        check(sys.argv[2])
        return
    seed, work = int(sys.argv[1]), sys.argv[2]
    cases = build(seed, work)
    print(write_cases(here, work, cases), "lines,", len(cases), "cases")

if __name__ == "__main__":
    main()
