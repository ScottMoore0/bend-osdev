#!/usr/bin/env python3
"""Differential test cases for bend-osdev-fat.

Writes ref/cases.bend (a Bend program that mounts each image through the
package and prints one line per operation, through ref/harness.bend) and
ref/expected.txt (the same lines from an independent reader written here).

Two sources of images:
  * an image builder written here from Microsoft's "FAT: General Overview of
    On-Disk Format" (version 1.03): FAT12, FAT16 and FAT32 at several sector
    and cluster sizes, random directory trees, short names, long names
    (Unicode, surrogate pairs, exactly 13 and 26 units), fragmented files,
    directories that span clusters; then corrupted copies (boot sector
    fields, chains that loop, leave the volume, reach free or bad clusters or
    end early, long-name checksums and ordinals). fsck.fat -n checks every
    clean image the builder writes;
  * images made by mkfs.fat and filled by mmd and mcopy (dosfstools and
    mtools), checked against their source trees and mdir's listing.

The reader below (Reader) is written from the same specification by the
package's author; it is checked against the builder's own record of each
tree, and on the mtools images against the source trees and mdir.

FAT32 needs at least 65525 clusters, so FAT32 images are about 34 MB; the
images are passed to Bend as sparse devices (only the 512-byte blocks that
are not all zero) and read a block at a time.
"""
import os, random, shutil, struct, subprocess, sys, tempfile

BLOCK = 512

class FatErr(Exception):
    pass

# ---------------------------------------------------------------- the format

SHORT_OK = set(range(33, 127)) - set(b'"*+,./:;<=>?[\\]|')

def lfn_checksum(name11):
    s = 0
    for b in name11:
        s = (((s & 1) << 7) + (s >> 1) + b) & 0xFF
    return s

def upper(cs):
    return [c - 32 if 97 <= c <= 122 else c for c in cs]

def short_of(name):
    """The 11-byte short name a path component stands for, or None."""
    if name == ".":
        return b".".ljust(11)
    if name == "..":
        return b"..".ljust(11)
    cs = [ord(c) for c in name]
    if "." in name:
        i = name.rindex(".")
        base, ext = cs[:i], cs[i + 1:]
    else:
        base, ext = cs, []
    if not (1 <= len(base) <= 8 and len(ext) <= 3 and all(c in SHORT_OK for c in base + ext)):
        return None
    return bytes(upper(base)).ljust(8) + bytes(upper(ext)).ljust(3)

def units_of(s):
    b = s.encode("utf-16-le")
    return [b[i] | b[i + 1] << 8 for i in range(0, len(b), 2)]

def text_of(us):
    return bytes(x for u in us for x in (u & 255, u >> 8)).decode("utf-16-le", "surrogatepass")

def esc(s):
    out = []
    for c in s:
        o = ord(c)
        if 32 <= o < 127 and c not in "\\|;":
            out.append(c)
        else:
            out.append("\\u%08x" % o)
    return "".join(out)

def same(a, b):
    return upper(a) == upper(b)

EOC = {12: 0xFFF, 16: 0xFFFF, 32: 0x0FFFFFFF}
BAD = {12: 0xFF7, 16: 0xFFF7, 32: 0x0FFFFFF7}

def fat_get(kind, fat, n):
    if kind == 12:
        off = n + n // 2
        w = fat[off] | fat[off + 1] << 8
        return w >> 4 if n & 1 else w & 0xFFF
    if kind == 16:
        return struct.unpack_from("<H", fat, 2 * n)[0]
    return struct.unpack_from("<I", fat, 4 * n)[0] & 0x0FFFFFFF

def fat_set(kind, fat, n, v):
    if kind == 12:
        off = n + n // 2
        w = fat[off] | fat[off + 1] << 8
        w = (w & 0x000F) | (v & 0xFFF) << 4 if n & 1 else (w & 0xF000) | (v & 0xFFF)
        fat[off], fat[off + 1] = w & 255, w >> 8
    elif kind == 16:
        struct.pack_into("<H", fat, 2 * n, v & 0xFFFF)
    else:
        old = struct.unpack_from("<I", fat, 4 * n)[0]
        struct.pack_into("<I", fat, 4 * n, (old & 0xF0000000) | (v & 0x0FFFFFFF))

# ---------------------------------------------------------------- the builder

def lfn_entries(name, short11):
    us = units_of(name)
    k = (len(us) + 12) // 13
    chk = lfn_checksum(short11)
    out = []
    for i in range(k, 0, -1):
        piece = us[(i - 1) * 13:i * 13]
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

def short_entry(name11, attr, cluster, size, rng, nt=0):
    e = bytearray(32)
    e[0:11] = name11
    e[11], e[12] = attr, nt
    e[13] = rng.randrange(200)
    date = lambda: (rng.randrange(128) << 9) | (rng.randrange(1, 13) << 5) | rng.randrange(1, 29)
    time = lambda: (rng.randrange(24) << 11) | (rng.randrange(60) << 5) | rng.randrange(30)
    struct.pack_into("<HHHHHHHI", e, 14, time(), date(), date(), cluster >> 16, time(), date(), cluster & 0xFFFF, size)
    return bytes(e)

def basis(name):
    """A short name for a long one: upper case, unusable characters as '_'."""
    s = name.lstrip(".")
    i = s.rfind(".")
    base, ext = (s[:i], s[i + 1:]) if i > 0 else (s, "")
    fix = lambda t: "".join(c if ord(c) in SHORT_OK else "_" for c in t.upper() if c not in " .")
    return (fix(base) or "X")[:6], fix(ext)[:3]

def names_for(name, taken):
    """(short name, NT case flags, long name or None) for a new entry."""
    s = short_of(name)
    if s is not None and s not in taken:
        i = name.rfind(".")
        base, ext = (name[:i], name[i + 1:]) if i > 0 else (name, "")
        flags = 0
        ok = True
        for part, bit in ((base, 8), (ext, 16)):
            if part == part.upper():
                continue
            if part == part.lower():
                flags |= bit
            else:
                ok = False
        if ok:
            return s, flags, None
    b, e = basis(name)
    n = 1
    while True:
        tail = "~%d" % n
        s = (b[:8 - len(tail)] + tail).encode().ljust(8) + e.encode().ljust(3)
        if s not in taken:
            return s, 0, name
        n += 1

class Image:
    """A volume being built, in memory."""

    def __init__(self, kind, bps, spc, clusters, rng, nfats=2, rootent=512, rsvd=None, media=0xF8, pool=900):
        self.kind, self.bps, self.spc, self.rng = kind, bps, spc, rng
        self.cbytes = bps * spc
        self.rsvd = rsvd if rsvd else (32 if kind == 32 else 1 + rng.randrange(3))
        self.rootent = 0 if kind == 32 else rootent
        self.nfats = nfats
        fat_bytes = ((clusters + 2) * kind + 7) // 8
        self.fatsz = -(-fat_bytes // bps)
        rootsecs = -(-self.rootent * 32 // bps)
        meta = self.rsvd + nfats * self.fatsz + rootsecs
        self.tot = meta + clusters * spc + rng.randrange(spc)
        self.clusters = clusters
        assert (self.tot - meta) // spc == clusters
        assert spec_type(clusters) == kind
        self.img = bytearray(self.tot * bps)
        self.fat = bytearray(self.fatsz * bps)
        self.root_start = (self.rsvd + nfats * self.fatsz) * bps
        self.data_start = (self.rsvd + nfats * self.fatsz + rootsecs) * bps
        fat_set(kind, self.fat, 0, (0x0FFFFF00 if kind == 32 else 0xFF00) | media)
        fat_set(kind, self.fat, 1, EOC[kind])
        self.free = list(range(2, 2 + min(clusters, pool)))
        rng.shuffle(self.free)
        self.free.sort(key=lambda c: c + rng.randrange(40))  # mostly in order, some jumps
        self.media = media
        self.root_cluster = None
        self.used = 0

    def alloc(self, n):
        cs = [self.free.pop(0) for _ in range(n)]
        self.used += n
        for a, b in zip(cs, cs[1:]):
            fat_set(self.kind, self.fat, a, b)
        if cs:
            end = EOC[self.kind] if self.rng.random() < 0.7 else EOC[self.kind] - self.rng.randrange(8)
            fat_set(self.kind, self.fat, cs[-1], end)
        return cs

    def coff(self, c):
        return self.data_start + (c - 2) * self.cbytes

    def write_chain(self, cs, data):
        for i, c in enumerate(cs):
            piece = data[i * self.cbytes:(i + 1) * self.cbytes]
            self.img[self.coff(c):self.coff(c) + len(piece)] = piece

    def build(self, tree):
        """tree: {"name": bytes (a file) or dict (a directory)}. Returns the
        record of what was written: path -> (is_dir, size, data)."""
        record = {}
        if self.kind == 32:
            n = self.dir_clusters(tree, False)
            cs = self.alloc(n)
            self.root_cluster = cs[0]
            self.fill_dir(tree, cs, 0, "", record, True)
        else:
            self.fill_dir(tree, None, 0, "", record, True)
        self.boot_sector()
        return record

    def dir_entries_count(self, tree, dots):
        n = 2 if dots else 1
        taken = set()
        for name in tree:
            s, f, lfn = names_for(name, taken)
            taken.add(s)
            n += 1 + (len(lfn_entries(lfn, s)) if lfn else 0)
        return n

    def dir_clusters(self, tree, dots):
        return max(1, -(-self.dir_entries_count(tree, dots) * 32 // self.cbytes))

    def fill_dir(self, tree, cs, dotdot, path, record, is_root):
        entries = []
        if not is_root:
            entries.append(short_entry(b".".ljust(11), 0x10, cs[0], 0, self.rng))
            entries.append(short_entry(b"..".ljust(11), 0x10, dotdot, 0, self.rng))
        else:
            entries.append(short_entry(LABEL, 0x08, 0, 0, self.rng))
        taken = set()
        for name, val in tree.items():
            s, flags, lfn = names_for(name, taken)
            taken.add(s)
            sub = path + "/" + name
            if isinstance(val, dict):
                kcs = self.alloc(self.dir_clusters(val, True))
                # ".." of a directory in the root holds 0, even on FAT32
                self.fill_dir(val, kcs, 0 if is_root else cs[0], sub, record, False)
                attr, cl, size = 0x10, kcs[0], 0
                record[sub] = (True, 0, None)
            else:
                n = -(-len(val) // self.cbytes)
                fcs = self.alloc(n)
                self.write_chain(fcs, val)
                attr = 0x20 | (self.rng.choice([0, 0, 0, 1, 2]))
                cl, size = (fcs[0] if fcs else 0), len(val)
                record[sub] = (False, size, val)
            if lfn:
                entries.extend(lfn_entries(lfn, s))
            entries.append(short_entry(s, attr, cl, size, self.rng, flags))
        raw = b"".join(entries)
        if cs is None:
            assert len(entries) <= self.rootent
            self.img[self.root_start:self.root_start + len(raw)] = raw
        else:
            assert len(raw) <= len(cs) * self.cbytes
            self.write_chain(cs, raw)

    def boot_sector(self):
        b = bytearray(self.bps)
        b[0:3] = b"\xeb\x3c\x90" if self.kind != 32 else b"\xeb\x58\x90"
        b[3:11] = b"BENDFAT "
        tot16, tot32 = (self.tot, 0) if self.tot < 65536 and self.kind != 32 else (0, self.tot)
        fatsz16 = self.fatsz if self.kind != 32 else 0
        struct.pack_into("<HBHBHHBHHHII", b, 11, self.bps, self.spc, self.rsvd, self.nfats, self.rootent,
                         tot16, self.media, fatsz16, 63, 255, 0, tot32)
        volid = self.rng.randrange(1 << 32)
        label = LABEL
        if self.kind == 32:
            struct.pack_into("<IHHIHH", b, 36, self.fatsz, 0, 0, self.root_cluster, 1, 6)
            ext = 64
        else:
            ext = 36
        b[ext], b[ext + 2] = 0x80, 0x29
        struct.pack_into("<I", b, ext + 3, volid)
        b[ext + 7:ext + 18] = label
        b[ext + 18:ext + 26] = {12: b"FAT12   ", 16: b"FAT16   ", 32: b"FAT32   "}[self.kind]
        b[510], b[511] = 0x55, 0xAA
        self.img[0:self.bps] = b
        if self.kind == 32:
            fsi = bytearray(self.bps)
            struct.pack_into("<I", fsi, 0, 0x41615252)
            struct.pack_into("<III", fsi, 484, 0x61417272, self.clusters - self.used, self.free[0] if self.free else 0xFFFFFFFF)
            struct.pack_into("<I", fsi, 508, 0xAA550000)
            self.img[self.bps:2 * self.bps] = fsi
            self.img[6 * self.bps:7 * self.bps] = b
            self.img[7 * self.bps:8 * self.bps] = fsi
        for i in range(self.nfats):
            off = (self.rsvd + i * self.fatsz) * self.bps
            self.img[off:off + len(self.fat)] = self.fat

LABEL = b"BEND FAT   "

def spec_type(clusters):
    return 12 if clusters < 4085 else 16 if clusters < 65525 else 32

# ---------------------------------------------------------------- the reader

class Node:
    def __init__(self, long, raw):
        self.long, self.raw = long, raw
        self.name11 = raw[0:11]
        self.attr = raw[11]
        self.nt = raw[12]
        self.cluster = struct.unpack_from("<H", raw, 20)[0] << 16 | struct.unpack_from("<H", raw, 26)[0]
        self.size = struct.unpack_from("<I", raw, 28)[0]

    def is_dir(self):
        return bool(self.attr & 0x10)

    def short_text(self):
        xs = list(self.name11)
        if xs[0] == 5:
            xs[0] = 0xE5
        base = bytes(xs[:8]).rstrip(b" ")
        ext = bytes(xs[8:11]).rstrip(b" ")
        low = lambda t, on: bytes(c + 32 if on and 65 <= c <= 90 else c for c in t)
        base, ext = low(base, self.nt & 8), low(ext, self.nt & 16)
        t = "".join(chr(c) for c in base)
        return t + ("." + "".join(chr(c) for c in ext) if ext else "")

    def name(self):
        return text_of(self.long) if self.long else self.short_text()

    def show(self):
        return "%s|%s|%d|%s" % (esc(self.name()), "D" if self.is_dir() else "F", self.size, esc(self.short_text()))

class Reader:
    """A FAT reader from the specification, refusing what the package
    refuses, in the order the package checks it."""

    def __init__(self, img, strict=True, max_cluster=32768):
        self.img, self.strict, self.max_cluster = img, strict, max_cluster

    def rd(self, off, n):
        if off + n > len(self.img):
            raise FatErr("device: block %d out of range" % (len(self.img) // BLOCK))
        return bytes(self.img[off:off + n])

    def mount(self):
        b = self.rd(0, 512)
        (bps, spc, rsvd, nfats, rootent, tot16, media, fatsz16, _spt, _heads, _hidden, tot32) = struct.unpack_from("<HBHBHHBHHHII", b, 11)
        fatsz32, flags, ver, rootclus, fsinfo = struct.unpack_from("<IHHIH", b, 36)
        sig = struct.unpack_from("<H", b, 510)[0]
        tot = tot16 or tot32
        fatsz = fatsz16 or fatsz32
        if sig != 0xAA55: raise FatErr("no 0x55AA signature")
        if not ((b[0] == 0xEB and b[2] == 0x90) or b[0] == 0xE9): raise FatErr("bad jump instruction")
        if bps not in (512, 1024, 2048, 4096): raise FatErr("bad bytes per sector %d" % bps)
        if spc not in (1, 2, 4, 8, 16, 32, 64, 128): raise FatErr("bad sectors per cluster %d" % spc)
        if bps * spc > self.max_cluster: raise FatErr("cluster too large %d" % (bps * spc))
        if rsvd == 0: raise FatErr("no reserved sectors")
        if nfats == 0: raise FatErr("no FATs")
        if not (media == 0xF0 or media >= 0xF8): raise FatErr("bad media %d" % media)
        if tot == 0: raise FatErr("bad total sectors")
        if fatsz == 0: raise FatErr("bad FAT size")
        rootsecs = (rootent * 32 + bps - 1) // bps
        meta = rsvd + nfats * fatsz + rootsecs
        if not meta < tot: raise FatErr("volume too small")
        count = (tot - meta) // spc
        if count == 0: raise FatErr("volume too small")
        if count > 268435445: raise FatErr("bad total sectors")
        kind = spec_type(count)
        need = {12: ((count + 2) * 3 + 1) // 2, 16: (count + 2) * 2, 32: (count + 2) * 4}[kind]
        if need > fatsz * bps: raise FatErr("bad FAT size")
        active = (flags & 15) if kind == 32 and flags & 128 else 0
        if not active < nfats: raise FatErr("no FATs")
        if kind == 32:
            if rootent != 0: raise FatErr("bad root entry count")
            if fatsz16 != 0: raise FatErr("bad FAT size")
            if tot16 != 0: raise FatErr("bad total sectors")
            if ver != 0: raise FatErr("bad FAT32 version")
            if not 2 <= rootclus <= count + 1: raise FatErr("bad root cluster %d" % rootclus)
        elif rootent == 0:
            raise FatErr("bad root entry count")
        self.kind, self.bps, self.spc, self.count = kind, bps, spc, count
        self.cbytes = bps * spc
        self.fat_start = (rsvd + active * fatsz) * bps
        self.root_start = (rsvd + nfats * fatsz) * bps
        self.rootent = rootent
        self.data_start = (rsvd + nfats * fatsz + rootsecs) * bps
        self.root_cluster = rootclus
        self.fsinfo_at = fsinfo * bps
        ext = 64 if kind == 32 else 36
        self.volid = struct.unpack_from("<I", b, ext + 3)[0]
        self.label = b[ext + 7:ext + 18]
        return "%s %d" % ({12: "FAT12", 16: "FAT16", 32: "FAT32"}[kind], count)

    def valid(self, c):
        return 2 <= c <= self.count + 1

    def link(self, c):
        """The next cluster after c, or None at the end of the chain."""
        if self.kind == 12:
            off = self.fat_start + c + c // 2
            w = struct.unpack("<H", self.rd(off, 2))[0]
            v = w >> 4 if c & 1 else w & 0xFFF
        else:
            v = fat_get(self.kind, self.rd(self.fat_start + (4 if self.kind == 32 else 2) * c, 4 if self.kind == 32 else 2), 0)
        if v == 0: raise FatErr("free cluster in chain %d" % c)
        if v == BAD[self.kind]: raise FatErr("bad cluster in chain %d" % c)
        if v > BAD[self.kind]: return None
        if not self.valid(v): raise FatErr("cluster out of range %d" % v)
        return v

    def walk(self, start):
        if start == 0:
            return []
        if not self.valid(start):
            raise FatErr("cluster out of range %d" % start)
        out, c, fuel = [], start, self.count
        while True:
            if fuel == 0:
                raise FatErr("chain loops")
            fuel -= 1
            out.append(c)
            nxt = self.link(c)
            if nxt is None:
                return out
            c = nxt

    # directories

    def bad(self, msg):
        if self.strict:
            raise FatErr(msg)

    def scan(self, d, want=None):
        """The listed nodes of directory d (None: the root), or the first that
        want (a path component) names."""
        st = {"run": None, "found": [], "ended": False, "seen": 0}
        def entry(raw):
            if st["ended"]:
                return
            if st["seen"] >= 65536:
                raise FatErr("directory too long")
            st["seen"] += 1
            b0 = raw[0]
            if b0 == 0:
                if st["run"] is not None:
                    st["run"] = None
                    self.bad("long name sequence broken")
                st["ended"] = True
            elif b0 == 0xE5:
                if st["run"] is not None:
                    st["run"] = None
                    self.bad("long name sequence broken")
            elif raw[11] & 0x3F == 0x0F:
                ordv, chk = raw[0], raw[13]
                us = [struct.unpack_from("<H", raw, o)[0] for o in (1, 3, 5, 7, 9, 14, 16, 18, 20, 22, 24, 28, 30)]
                run = st["run"]
                if ordv & 0x40:
                    if run is not None:
                        st["run"] = None
                        self.bad("long name sequence broken")
                        return
                    n = ordv & 63
                    if 1 <= n <= 20:
                        st["run"] = [n - 1, chk, us]
                    else:
                        self.bad("long name sequence broken")
                else:
                    if run is None:
                        self.bad("long name sequence broken")
                    elif not (ordv == run[0] and run[0] != 0):
                        st["run"] = None
                        self.bad("long name sequence broken")
                    elif chk != run[1]:
                        st["run"] = None
                        self.bad("long name checksum mismatch")
                    else:
                        st["run"] = [run[0] - 1, chk, us + run[2]]
            else:
                run, long = st["run"], []
                st["run"] = None
                if run is not None:
                    if run[0] != 0:
                        self.bad("long name sequence broken")
                    elif lfn_checksum(raw[0:11]) != run[1]:
                        self.bad("long name checksum mismatch")
                    else:
                        long = run[2]
                        if 0 in long:
                            long = long[:long.index(0)]
                node = Node(long, raw)
                listed = not (node.attr & 0x08 and not node.attr & 0x10) and raw[0] != 0x2E
                if listed:
                    hit = want is None or (bool(node.long) and same(units_of(want), node.long)) or (short_of(want) is not None and same(list(short_of(want)), list(node.name11)))
                    if hit:
                        st["found"].append(node)
                        if want is not None:
                            st["ended"] = True
        def region(off, n):
            for i in range(0, n, self.bps):
                if st["ended"]:
                    return
                piece = self.rd(off + i, min(self.bps, n - i))
                for j in range(0, len(piece) - 31, 32):
                    entry(piece[j:j + 32])
        if d is None and self.kind != 32:
            region(self.root_start, self.rootent * 32)
        else:
            c = self.root_cluster if d is None else d
            if not self.valid(c):
                raise FatErr("cluster out of range %d" % c)
            fuel = self.count + 1
            while c is not None:
                if fuel == 0:
                    raise FatErr("chain loops")
                fuel -= 1
                region(self.coff(c), self.cbytes)
                if st["ended"]:
                    break
                c = self.link(c)
        return st["found"]

    def coff(self, c):
        return self.data_start + (c - 2) * self.cbytes

    def resolve(self, path):
        here = None  # the root
        for comp in [p for p in path.split("/") if p]:
            if here is None:
                d = None
            elif here.is_dir():
                d = here.cluster if here.cluster != 0 else None
            else:
                raise FatErr("not a directory")
            found = self.scan(d, comp)
            if not found:
                raise FatErr("not found")
            here = found[0]
        return here

    def listdir(self, path):
        here = self.resolve(path)
        if here is not None and not here.is_dir():
            raise FatErr("not a directory")
        return self.scan(None if here is None or here.cluster == 0 else here.cluster)

    # files: the same steps as the package's cursor

    def open(self, node):
        if node is None or node.is_dir():
            raise FatErr("is a directory")
        if node.size == 0:
            return None
        if not self.valid(node.cluster):
            raise FatErr("cluster out of range %d" % node.cluster)
        return [node.cluster, 0, node.size, self.count]

    def next(self, cur):
        c, sector, left, fuel = cur
        n = min(self.bps, left)
        data = self.rd(self.coff(c) + sector * self.bps, n)
        left -= n
        if left == 0:
            return data, None
        if (sector + 1) * self.bps < self.cbytes:
            return data, [c, sector + 1, left, fuel]
        if fuel == 0:
            raise FatErr("chain loops")
        nxt = self.link(c)
        if nxt is None:
            raise FatErr("chain shorter than file")
        return data, [nxt, 0, left, fuel - 1]

    def stream(self, node):
        cur = self.open(node)
        if cur is None:
            return [b""]
        out = []
        while True:
            data, cur = self.next(cur)
            out.append(data)
            if cur is None:
                return out

    def read(self, node, off, ln):
        cur = self.open(node)
        size = node.size
        start = min(off, size)
        n = min(ln, size - start)
        if n == 0:
            return b""
        c = node.cluster
        for _ in range(start // self.cbytes):
            c = self.link(c)
            if c is None:
                raise FatErr("chain shorter than file")
        within = start % self.cbytes
        skip = within % self.bps
        cur = [c, within // self.bps, n + skip, self.count]
        out = []
        while True:
            data, cur = self.next(cur)
            out.append(data)
            if cur is None:
                break
        return b"".join(out)[skip:]

# ---------------------------------------------------------------- outputs

def h32(data):
    h = 0
    for b in data:
        h = (h * 31 + b) & 0xFFFFFFFF
    return h

def show_bytes(data):
    s = "%d %08x" % (len(data), h32(data))
    return s + (" " + data.hex() if len(data) <= 48 else "")

def bend_str(s):
    if all(32 <= ord(c) < 127 and c not in '"\\' for c in s):
        return '"%s"' % s
    return "str_of([%s])" % ", ".join(str(ord(c)) for c in s)

class Cases:
    def __init__(self):
        self.images, self.lines, self.expect = [], [], []

    def image(self, tag, img):
        blocks = []
        for i in range(0, len(img), BLOCK):
            blk = bytes(img[i:i + BLOCK])
            if any(blk):
                blocks.append("R.H.block(%dn, 512n, \"%s\")" % (i // BLOCK, blk.rstrip(b"\0").hex()))
        count = -(-len(img) // BLOCK)
        self.images.append((tag, count, blocks))
        self.cur = tag
        self.calls = []

    def op(self, label, call, result):
        tag = self.cur
        lit = label.replace("\\", "\\\\").replace('"', '\\"')
        self.lines.append((tag, '    IO.print("%s %s " ++ %s)' % (tag, lit, call)))
        self.expect.append("%s %s %s" % (tag, label, result))

    def write(self, here):
        with open(os.path.join(here, "cases.bend"), "w") as f:
            f.write("import Base\nimport ../bpb.bend as P\nimport ./harness.bend as R\n\n")
            f.write("def str_of(xs: List<&2, U32>) -> String:\n  match xs:\n    case Nil{}:\n      \"\"\n    case Con{h, t}:\n      SCon{Char.from_u32(h), str_of(t)}\n\n")
            f.write("def strict() -> P.FatOptions:\n  P.FatOptions.default()\n\n")
            f.write("def lenient() -> P.FatOptions:\n  P.FatOptions.lenient()\n\n")
            for tag, count, blocks in self.images:
                # the block list in pieces, so no list literal is long (the
                # last piece first: a def may call only defs above it)
                for k in reversed(range(0, max(1, len(blocks)), 40)):
                    part = blocks[k:k + 40]
                    nxt = "blocks_%s_%d()" % (tag, k + 40) if k + 40 < len(blocks) else "[]"
                    f.write("def blocks_%s_%d() -> List<&2, R.SparseBlock>:\n  List.append(&2, R.SparseBlock, [%s], %s)\n\n" % (tag, k, ", ".join(part), nxt))
                f.write("def dev_%s() -> R.SparseDev:\n  R.SparseDev{512n, %dn, blocks_%s_0()}\n\n" % (tag, count, tag))
                f.write("def run_%s(+d: R.SparseDev) -> IO(Unit):\n  do IO<Unit>:\n" % tag)
                body = [l for t, l in self.lines if t == tag]
                f.write("\n".join(body) + "\n\n")
            f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n")
            for tag, count, blocks in self.images:
                f.write("    run_%s(dev_%s())\n" % (tag, tag))
        with open(os.path.join(here, "expected.txt"), "w") as f:
            f.write("\n".join(self.expect) + "\n")

def result(fn):
    try:
        return fn()
    except FatErr as e:
        return "error " + str(e)

def opts(strict):
    return "strict()" if strict else "lenient()"

def ops_mount(cs, img, strict=True):
    r = Reader(img, strict, 32768 if strict else 65536)
    cs.op("mount", "R.H.mount(d, %s)" % opts(strict), result(r.mount))
    return r

def ops_ls(cs, r, path, strict=True):
    def go():
        r.strict = strict
        ns = r.listdir(path)
        return "%d%s" % (len(ns), "".join(" " + n.show() + ";" for n in ns))
    cs.op("ls " + esc(path), "R.H.ls(d, %s, %s)" % (opts(strict), bend_str(path)), result(go))

def ops_stat(cs, r, path):
    def go():
        n = r.resolve(path)
        return "root" if n is None else n.show()
    cs.op("stat " + esc(path), "R.H.stat(d, strict(), %s)" % bend_str(path), result(go))

def ops_read(cs, r, path, off, ln):
    def go():
        n = r.resolve(path)
        return show_bytes(r.read(n, off, ln))
    cs.op("read %s %d %d" % (esc(path), off, ln), "R.H.read(d, strict(), %s, %d, %d)" % (bend_str(path), off, ln), result(go))

def ops_stream(cs, r, path):
    def go():
        pieces = r.stream(r.resolve(path))
        data = b"".join(pieces)
        return "%d %08x %s" % (len(data), h32(data), "True" if all(len(p) <= r.bps for p in pieces) else "False")
    cs.op("stream " + esc(path), "R.H.stream(d, strict(), %s)" % bend_str(path), result(go))

def ops_walk(cs, r, path):
    def go():
        n = r.resolve(path)
        if n is None:
            raise FatErr("is a directory")
        return str(len(r.walk(n.cluster)))
    cs.op("walk " + esc(path), "R.H.walk(d, strict(), %s)" % bend_str(path), result(go))

def ops_fsinfo(cs, r):
    def go():
        if r.kind != 32:
            raise FatErr("bad FSInfo")
        b = r.rd(r.fsinfo_at, 512)
        lead, = struct.unpack_from("<I", b, 0)
        st, free, nxt = struct.unpack_from("<III", b, 484)
        trail, = struct.unpack_from("<I", b, 508)
        if (lead, st, trail) != (0x41615252, 0x61417272, 0xAA550000):
            raise FatErr("bad FSInfo")
        return "%d %d" % (free, nxt)
    cs.op("fsinfo", "R.H.fsinfo(d, strict())", result(go))

def ops_label(cs, r):
    cs.op("label", "R.H.label(d, strict())", result(lambda: "%08x %s" % (r.volid, esc("".join(chr(c) for c in r.label)))))

def flip_case(rng, s):
    return "".join(c.swapcase() if c.isascii() and rng.random() < 0.5 else c for c in s)

def short_path(r, path):
    """The path through each component's short name."""
    out, here = [], None
    for comp in [p for p in path.split("/") if p]:
        d = None if here is None or here.cluster == 0 else here.cluster
        here = r.scan(d, comp)[0]
        out.append(here.short_text())
    return "/" + "/".join(out)

def check_record(r, record):
    """The reader agrees with what the builder wrote (or the source tree)."""
    for path, (is_dir, size, data) in record.items():
        n = r.resolve(path)
        assert n.is_dir() == is_dir, path
        if not is_dir:
            assert n.size == size, path
            assert b"".join(r.stream(n)) == data, path
    dirs = [""] + [p for p, v in record.items() if v[0]]
    for d in dirs:
        names = sorted(n.name() for n in r.listdir(d or "/"))
        want = sorted(p[len(d) + 1:] for p in record if p.rsplit("/", 1)[0] == d)
        assert names == want, (d, names, want)

def all_ops(cs, img, record, rng, fsinfo=False):
    r = ops_mount(cs, img)
    ops_label(cs, r)
    if fsinfo:
        ops_fsinfo(cs, r)
    check_record(r, record)
    dirs = ["/"] + [p for p, v in record.items() if v[0]]
    for d in dirs:
        ops_ls(cs, r, d)
    files = [p for p, v in record.items() if not v[0]]
    for p in files:
        size = record[p][1]
        if size <= 4096:
            ops_read(cs, r, p, 0, 4294967295)
        ops_stream(cs, r, p)
        for _ in range(2):
            off = rng.randrange(size + 20)
            ops_read(cs, r, p, off, rng.randrange(1, 700))
    for p in rng.sample(files, min(4, len(files))):
        ops_walk(cs, r, p)
    for p in rng.sample(list(record), min(6, len(record))):
        ops_stat(cs, r, flip_case(rng, p))
        ops_stat(cs, r, short_path(r, p))
    ops_stat(cs, r, "/")
    ops_stat(cs, r, "/no such file")
    if files:
        ops_stat(cs, r, files[0] + "/below")
    return r

# ---------------------------------------------------------------- trees

LONG_NAMES = ["Read Me.txt", "a much longer file name.data", "Mixed Case.Bin", "x" * 13, "y" * 26 + ".z",
              "café crème.txt", "日本語の名前", "emoji \U0001F600 face", "two.dots.here",
              ".hidden", "trailing space ", "lower.txt", "UPPER.TXT", "MiXeD", "notes", "a+b=c", "[brackets]", "semi;colon"]

def rand_name(rng, taken):
    while True:
        k = rng.random()
        if k < 0.35:
            n = "".join(rng.choice("ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_") for _ in range(rng.randrange(1, 9)))
            if rng.random() < 0.6:
                n += "." + "".join(rng.choice("ABCDEFGHIJKLMNOPQRSTUVWXYZ") for _ in range(rng.randrange(1, 4)))
        elif k < 0.5:
            n = "".join(rng.choice("abcdefghij") for _ in range(rng.randrange(1, 9))) + ".txt"
        elif k < 0.8:
            n = rng.choice(LONG_NAMES)
            if rng.random() < 0.5:
                n = "%s %d" % (n, rng.randrange(1000))
        else:
            n = "".join(rng.choice("abcdefghijklmnopqrstuvwxyz ABC-_0123456789") for _ in range(rng.randrange(9, 60))).strip() or "z"
        n = n.rstrip(" .") or "q"
        if n.upper() not in taken:
            taken.add(n.upper())
            return n

def rand_tree(rng, depth, width, cbytes, ascii_only=False):
    tree, taken = {}, set()
    for _ in range(rng.randrange(1, width + 1)):
        name = rand_name(rng, taken)
        if ascii_only and not name.isascii():
            continue
        if depth > 0 and rng.random() < 0.3:
            tree[name] = rand_tree(rng, depth - 1, width, cbytes, ascii_only)
        else:
            k = rng.random()
            size = 0 if k < 0.1 else cbytes * rng.randrange(1, 3) if k < 0.25 else rng.randrange(1, 3 * cbytes + 100)
            size = min(size, 9000)
            tree[name] = bytes(rng.randrange(256) for _ in range(size))
    return tree

# ---------------------------------------------------------------- tools

def have(*tools):
    return all(shutil.which(t) for t in tools)

def fsck(img, tmp):
    p = os.path.join(tmp, "fsck.img")
    with open(p, "wb") as f:
        f.truncate(len(img))
        for i in range(0, len(img), 65536):
            chunk = img[i:i + 65536]
            if any(chunk):
                f.seek(i)
                f.write(chunk)
    r = subprocess.run(["fsck.fat", "-n", p], capture_output=True, text=True)
    os.unlink(p)
    if r.returncode != 0:
        sys.exit("fsck.fat -n refused a built image:\n" + r.stdout + r.stderr)

def mtools_image(rng, tmp, kind, kb, spc, tree):
    """An image made by mkfs.fat and filled by mmd and mcopy from tree."""
    img = os.path.join(tmp, "m.img")
    if os.path.exists(img):
        os.unlink(img)
    subprocess.run(["mkfs.fat", "-C", img, str(kb), "-F", str(kind), "-S", "512", "-s", str(spc), "-n", "MTOOLS", "-i", "%08x" % rng.randrange(1 << 32)],
                   check=True, capture_output=True)
    env = dict(os.environ, MTOOLS_SKIP_CHECK="1", MTOOLS_NO_VFAT="0")
    record = {}
    def put(t, path):
        for name, val in t.items():
            sub = path + "/" + name
            if isinstance(val, dict):
                subprocess.run(["mmd", "-i", img, "::" + sub], check=True, env=env, capture_output=True)
                record[sub] = (True, 0, None)
                put(val, sub)
            else:
                src = os.path.join(tmp, "src")
                with open(src, "wb") as f:
                    f.write(val)
                subprocess.run(["mcopy", "-i", img, src, "::" + sub], check=True, env=env, capture_output=True)
                record[sub] = (False, len(val), val)
    put(tree, "")
    listing = subprocess.run(["mdir", "-i", img, "-/", "-b", "-a", "::/"], check=True, env=env, capture_output=True, text=True).stdout
    mdir_paths = sorted(l[3:].rstrip("/") for l in listing.splitlines() if l.startswith("::/"))
    with open(img, "rb") as f:
        data = bytearray(f.read())
    return data, record, mdir_paths

# ---------------------------------------------------------------- main

def corrupt(img, off, val, width=1):
    c = bytearray(img)
    c[off:off + width] = val.to_bytes(width, "little")
    return c

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    cs = Cases()
    tmp = tempfile.mkdtemp()
    try:
        # (kind, bytes per sector, sectors per cluster, clusters, root entries)
        configs = [(12, 512, 1, 300, 64), (12, 512, 4, 1000, 512), (12, 1024, 1, 4084, 128), (12, 4096, 2, 60, 128),
                   (16, 512, 1, 4085, 512), (16, 2048, 4, 5000, 256), (32, 512, 1, 65525, 0), (32, 1024, 1, 65600, 0)]
        built = []
        for i, (kind, bps, spc, clusters, rootent) in enumerate(configs):
            im = Image(kind, bps, spc, clusters, rng, rootent=rootent or 512)
            tree = rand_tree(rng, 2, 7, im.cbytes)
            if i == 1:
                # a directory spanning clusters: many long names
                tree["Many Entries Here"] = {"long file name number %d.txt" % k: bytes([k]) * k for k in range(40)}
            record = im.build(tree)
            fsck(im.img, tmp)
            tag = "b%d" % i
            cs.image(tag, im.img)
            all_ops(cs, im.img, record, rng, fsinfo=(kind == 32))
            built.append((tag, im, record))

        # corrupted boot sectors (on the FAT12 image b0 and the FAT32 image b6)
        base12, base32 = built[0][1].img, built[6][1].img
        bpb_cases = [
            ("c_jump", base12, 0, 0, 1), ("c_sig", base12, 510, 0x1234, 2), ("c_bps", base12, 11, 500, 2),
            ("c_spc", base12, 13, 3, 1), ("c_rsvd", base12, 14, 0, 2), ("c_nfats", base12, 16, 0, 1),
            ("c_media", base12, 21, 0x12, 1), ("c_root0", base12, 17, 0, 2), ("c_fatsz", base12, 22, 0, 2),
            ("c_tiny", base12, 19, 8, 2), ("c_big", base12, 13, 128, 1),
            ("c_ver", base32, 42, 1, 2), ("c_rootclus", base32, 44, 1, 4), ("c_rootent32", base32, 17, 16, 2),
            ("c_fatsz32", base32, 36, 4, 4),
        ]
        for tag, base, off, val, w in bpb_cases:
            c = corrupt(base, off, val, w)
            if tag == "c_tiny":
                c = corrupt(c, 32, 0, 4)
            cs.image(tag, c)
            ops_mount(cs, c)
            if tag == "c_big":
                ops_mount(cs, c, strict=False)

        # corrupted chains, on copies of the FAT16 image b4
        tag0, im, record = built[4]
        files = [p for p, v in record.items() if not v[0] and v[1] > 2 * im.cbytes]
        dirs = [p for p, v in record.items() if v[0]]
        r = Reader(im.img)
        r.mount()
        def fat_corrupt(fn):
            fat = bytearray(im.fat)
            fn(fat)
            c = bytearray(im.img)
            for k in range(im.nfats):
                off = (im.rsvd + k * im.fatsz) * im.bps
                c[off:off + len(fat)] = fat
            return c
        target = files[0]
        chain = r.walk(r.resolve(target).cluster)
        chain_cases = [
            ("k_loop", lambda f: fat_set(16, f, chain[-1], chain[0])),
            ("k_range", lambda f: fat_set(16, f, chain[0], im.clusters + 5)),
            ("k_free", lambda f: fat_set(16, f, chain[1], 0)),
            ("k_bad", lambda f: fat_set(16, f, chain[0], BAD[16])),
            ("k_short", lambda f: fat_set(16, f, chain[0], EOC[16])),
            ("k_self", lambda f: fat_set(16, f, chain[1], chain[1])),
        ]
        for tag, fn in chain_cases:
            c = fat_corrupt(fn)
            cs.image(tag, c)
            rr = ops_mount(cs, c)
            ops_walk(cs, rr, target)
            ops_stream(cs, rr, target)
            ops_read(cs, rr, target, 0, 4294967295)
            ops_read(cs, rr, target, im.cbytes + 3, 100)

        # a directory chain that loops: fill a directory exactly, then point
        # its last cluster at its first
        im2 = Image(16, 512, 1, 4085, rng)
        full = {"F%03d.TXT" % k: b"x" for k in range(16 * 3)}
        rec2 = im2.build({"FULL": full, "other file.txt": b"hello"})
        r2 = Reader(im2.img)
        r2.mount()
        dch = r2.walk(r2.resolve("/FULL").cluster)
        assert len(dch) == 4  # 48 entries + "." and ".." in 512-byte clusters
        fat = bytearray(im2.fat)
        fat_set(16, fat, dch[-1], dch[0])
        c = bytearray(im2.img)
        for k in range(im2.nfats):
            off = (im2.rsvd + k * im2.fatsz) * im2.bps
            c[off:off + len(fat)] = fat
        cs.image("k_dirloop", c)
        rr = ops_mount(cs, c)
        ops_ls(cs, rr, "/FULL")
        ops_stat(cs, rr, "/FULL/no such")
        ops_ls(cs, rr, "/")

        # long names: a checksum changed, an ordinal changed, an orphan
        tag0, im, record = built[1]
        r = Reader(im.img)
        r.mount()
        root = im.img[im.root_start:im.root_start + im.rootent * 32]
        idx = [k for k in range(0, len(root), 32) if root[k] not in (0, 0xE5) and root[k + 11] & 0x3F == 0x0F]
        assert len(idx) >= 2
        first = idx[0]
        lfn_cases = [("l_chk_all", "all"), ("l_chk_one", "one"), ("l_ord", "ord"), ("l_orphan", "orphan")]
        for tag, how in lfn_cases:
            c = bytearray(im.img)
            k = im.root_start + first
            if how == "all":
                j = k
                while c[j + 11] & 0x3F == 0x0F:
                    c[j + 13] ^= 0x5A
                    j += 32
            elif how == "one":
                c[k + 13] ^= 0x01
            elif how == "ord":
                c[k] = (c[k] & 0x40) | ((c[k] & 0x3F) + 1)
            else:
                c[k] = 0x41 if c[k] != 0x41 else 0x42
                c[k + 13] ^= 0xFF
            cs.image(tag, c)
            rr = ops_mount(cs, c)
            ops_ls(cs, rr, "/", strict=True)
            ops_ls(cs, rr, "/", strict=False)

        # images made by mkfs.fat, filled by mmd and mcopy
        for i, (kind, kb, spc) in enumerate([(12, 360, 1), (12, 1440, 4), (16, 2400, 1), (16, 9000, 4), (32, 34000, 1)]):
            tree = rand_tree(rng, 2, 6, 512 * spc, ascii_only=True)
            data, record, mdir_paths = mtools_image(rng, tmp, kind, kb, spc, tree)
            assert mdir_paths == sorted(p[1:] for p in record), (mdir_paths, sorted(record))
            r = Reader(data)
            assert r.mount().startswith("FAT%d" % kind)
            tag = "m%d" % i
            cs.image(tag, data)
            all_ops(cs, data, record, rng, fsinfo=(kind == 32))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    cs.write(here)
    print(len(cs.expect), "cases,", len(cs.images), "images")

main()
