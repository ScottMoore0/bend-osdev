#!/usr/bin/env python3
"""Differential test cases for bend-osdev-iso9660.

Usage: gen.py SEED TMPDIR

Writes ref/cases.bend (a Bend program that loads each image a block at a
time, opens it with the package, walks it, streams every file and reads
some byte ranges) and ref/expected.txt (the same, from the reader below).

The references:
  * an independent ISO 9660 / Joliet / Rock Ridge image builder and reader,
    written here from ECMA-119 (4th edition), SUSP 1.12, RRIP 1.12 and the
    Joliet specification. It shares an author with the package, so it is
    checked against the tools below as well;
  * genisoimage and xorriso (-as mkisofs) build images from random trees;
    the reader's listing and file contents are checked against the source
    tree, and against `isoinfo -l` (plain, -J and -R);
  * `isoinfo -d -l` reads the images the builder here writes, so the
    builder is checked too.
Without genisoimage, xorriso or isoinfo the third-party part is skipped
(the count of skipped images is printed).
"""
import os, random, shutil, struct, subprocess, sys, zlib

SECTOR = 2048

# ---------------------------------------------------------------- encoding

def both16(v):
    return struct.pack('<H', v & 0xFFFF) + struct.pack('>H', v & 0xFFFF)

def both32(v):
    return struct.pack('<I', v) + struct.pack('>I', v)

def dir_date(t):
    y, mo, d, h, mi, s, off = t
    return bytes([y - 1900, mo, d, h, mi, s, off & 0xFF])

def vol_date(t):
    if t is None:
        return b'0' * 16 + b'\0'
    y, mo, d, h, mi, s, cs, off = t
    return ('%04d%02d%02d%02d%02d%02d%02d' % (y, mo, d, h, mi, s, cs)).encode() + bytes([off & 0xFF])

def pad_field(s, n, fill=b' '):
    s = s[:n]
    return s + fill * (n - len(s))

DATE = (2026, 10, 17, 12, 34, 56, 4)

# ---------------------------------------------------------------- tree model

class Node:
    def __init__(self, name, kind, data=b'', target='', children=None):
        self.name, self.kind, self.data, self.target = name, kind, data, target
        self.children = children if children is not None else []

def rand_name(rng, n, alphabet='abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-'):
    return ''.join(rng.choice(alphabet) for _ in range(n))

def rand_tree(rng, depth, long_names=True, symlinks=True, many=0, max_name=40):
    """A random tree: files, directories, symbolic links."""
    root = Node('', 'd')
    used = set()
    def fresh(lo, hi, ext=True):
        while True:
            n = rand_name(rng, rng.randrange(lo, hi))
            if ext and rng.random() < 0.6:
                n += '.' + rand_name(rng, rng.randrange(1, 4), 'abcdefghijklmnopqrstuvwxyz')
            if n.lower() not in used:
                used.add(n.lower())
                return n
    def fill(d, level):
        for _ in range(rng.randrange(1, 5)):
            size = rng.choice([0, 1, 7, 100, 2047, 2048, 2049, 5000, rng.randrange(0, 9000)])
            d.children.append(Node(fresh(1, max_name if long_names else 8), 'f', bytes(rng.randrange(256) for _ in range(size))))
        if symlinks and rng.random() < 0.7:
            tgt = rng.choice(['../x', 'a/b/c', '/abs/path/to/file', '.', '..', 'plain', rand_name(rng, 50) + '/' + rand_name(rng, 3)])
            d.children.append(Node(fresh(1, 20), 'l', target=tgt))
        if level < depth:
            for _ in range(rng.randrange(1, 3)):
                sub = Node(fresh(1, 20 if long_names else 8, ext=False), 'd')
                d.children.append(sub)
                fill(sub, level + 1)
    fill(root, 1)
    if many:
        big = Node('many', 'd')
        for i in range(many):
            big.children.append(Node('entry_with_a_long_name_%03d.txt' % i, 'f', ('file %d\n' % i).encode()))
        root.children.append(big)
    return root

def deep_tree(rng, depth):
    """A chain of directories deep enough that genisoimage relocates it."""
    root = Node('', 'd')
    cur = root
    for i in range(depth):
        nd = Node('level%d' % i, 'd')
        cur.children.append(nd)
        cur.children.append(Node('f%d.txt' % i, 'f', ('at level %d\n' % i).encode()))
        cur = nd
    cur.children.append(Node('bottom.txt', 'f', b'the bottom\n'))
    return root

def write_tree(node, path):
    os.makedirs(path, exist_ok=True)
    for c in node.children:
        p = os.path.join(path, c.name)
        if c.kind == 'd':
            write_tree(c, p)
        elif c.kind == 'f':
            with open(p, 'wb') as f:
                f.write(c.data)
        else:
            os.symlink(c.target, p)

# ---------------------------------------------------------------- the builder

ER_ID = b'RRIP_1991A'
ER_DES = b'THE ROCK RIDGE INTERCHANGE PROTOCOL PROVIDES SUPPORT FOR POSIX FILE SYSTEM SEMANTICS'
ER_SRC = b'PLEASE CONTACT DISC PUBLISHER FOR SPECIFICATION SOURCE.  SEE PUBLISHER IDENTIFIER IN PRIMARY VOLUME DESCRIPTOR FOR CONTACT INFORMATION.'

def susp(sig, data, ver=1):
    return sig + bytes([len(data) + 4, ver]) + data

def rr_px(mode, links, ino):
    return susp(b'PX', both32(mode) + both32(links) + both32(0) + both32(0) + both32(ino))

def rr_tf():
    return susp(b'TF', bytes([0x0E]) + dir_date(DATE) * 3)

def rr_nm(name):
    """NM entries, split in pieces of 100 bytes (CONTINUE on all but the last)."""
    out = []
    pieces = [name[i:i + 100] for i in range(0, len(name), 100)] or [b'']
    for k, p in enumerate(pieces):
        out.append(susp(b'NM', bytes([1 if k < len(pieces) - 1 else 0]) + p))
    return out

def rr_sl(target):
    comps = []
    t = target
    if t.startswith('/'):
        comps.append((8, b''))
        t = t[1:]
    for part in [p for p in t.split('/') if p != ''] if t else []:
        if part == '.':
            comps.append((2, b''))
        elif part == '..':
            comps.append((4, b''))
        else:
            b = part.encode()
            while len(b) > 30:          # split long components (CONTINUE)
                comps.append((1, b[:30]))
                b = b[30:]
            comps.append((0, b))
    recs = b''.join(bytes([f, len(c)]) + c for f, c in comps)
    return [susp(b'SL', bytes([0]) + recs)]

def d_name(s, used, isdir):
    up = ''.join(ch if ch.isalnum() and ch.isascii() else '_' for ch in s.upper())
    if isdir:
        base, ext = up.replace('.', '_')[:31], None
    else:
        stem, _, e = s.rpartition('.') if '.' in s else (s, '', '')
        base = ''.join(ch if ch.isalnum() and ch.isascii() else '_' for ch in stem.upper())[:26] or '_'
        ext = ''.join(ch if ch.isalnum() and ch.isascii() else '_' for ch in e.upper())[:3]
    k = 0
    while True:
        b = base if k == 0 else (base[:max(1, len(base) - len(str(k)))] + str(k))
        name = b if isdir else b + '.' + ext
        if name not in used:
            used.add(name)
            return name.encode() + (b'' if isdir else b';1')
        k += 1

class Rec:
    """A directory record being laid out."""
    def __init__(self, ident, node, isdir, self_of=None, parent_of=None):
        self.ident, self.node, self.isdir = ident, node, isdir
        self.self_of, self.parent_of = self_of, parent_of
        self.su_inline = []   # SUSP entries in the record
        self.su_ce = []       # SUSP entries in its continuation area
        self.ce_loc = None    # (block, offset, length)
        self.extents = []     # [(block, size)] for files
        self.multi = []       # sizes of the extents of a multi-extent file

class Builder:
    def __init__(self, root, joliet=False, rr=False, force_ce=(), multi_extent=(), volid='BENDISO'):
        self.root, self.joliet, self.rr = root, joliet, rr
        self.force_ce, self.multi_extent, self.volid = set(force_ce), set(multi_extent), volid
        self.ino = 1

    # the records of a directory, for one hierarchy
    def records(self, d, parent, joliet):
        recs = [Rec(b'\0', d, True, self_of=d), Rec(b'\1', parent, True, parent_of=d)]
        used = set()
        kids = []
        for c in d.children:
            if c.kind == 'l' and not (self.rr and not joliet):
                continue
            if joliet:
                ident = c.name[:64].encode('utf-16-be') + ('' if c.kind == 'd' else ';1').encode('utf-16-be')
            else:
                ident = d_name(c.name, used, c.kind == 'd')
            kids.append(Rec(ident, c, c.kind == 'd'))
        kids.sort(key=lambda r: r.ident)
        recs += kids
        if self.rr and not joliet:
            for r in recs:
                self.add_rr(r, d)
        return recs

    def add_rr(self, r, d):
        node = r.node
        if r.self_of is not None and d is self.root:
            r.su_inline.append(susp(b'SP', b'\xbe\xef\x00'))
            r.su_ce.append(susp(b'ER', bytes([len(ER_ID), len(ER_DES), len(ER_SRC), 1]) + ER_ID + ER_DES + ER_SRC))
        if node.kind == 'd':
            mode, links = 0o040755, 2
        elif node.kind == 'l':
            mode, links = 0o120777, 1
        else:
            mode, links = 0o100644, 1
        es = [rr_px(mode, links, self.ino), rr_tf()]
        self.ino += 1
        if r.self_of is None and r.parent_of is None:
            es += rr_nm(node.name.encode())
            if node.kind == 'l':
                es += rr_sl(node.target)
        if r.self_of is None and r.parent_of is None and node.name in self.force_ce:
            r.su_ce += es
        else:
            fixed = 33 + len(r.ident) + (1 - len(r.ident) % 2)
            room = 255 - fixed - sum(len(e) for e in r.su_inline) - 28
            inline = []
            for k, e in enumerate(es):
                if sum(len(x) for x in inline) + len(e) <= room or (k == len(es) - 1 and sum(len(x) for x in inline) + len(e) <= room + 28 and not r.su_ce):
                    inline.append(e)
                else:
                    r.su_ce += es[k:]
                    break
            r.su_inline += inline

    def rec_bytes(self, r, ext, size, flags):
        su = b''.join(r.su_inline)
        if r.su_ce:
            b, o, l = r.ce_loc or (0, 0, 0)
            su += susp(b'CE', both32(b) + both32(o) + both32(l))
        fi = r.ident
        pad = b'\0' if len(fi) % 2 == 0 else b''
        length = 33 + len(fi) + len(pad) + len(su)
        assert length <= 255, length
        return (bytes([length, 0]) + both32(ext) + both32(size) + dir_date(DATE) +
                bytes([flags, 0, 0]) + both16(1) + bytes([len(fi)]) + fi + pad + su)

    def expand(self, r):
        """A record, or the records of a multi-extent file."""
        if r.node.kind == 'f' and r.node.name in self.multi_extent and not r.self_of and not r.parent_of:
            n = len(r.node.data)
            sizes = []
            while n > 4096:
                sizes.append(4096)
                n -= 4096
            sizes.append(n)
            return sizes
        return None

    def layout(self):
        # directories, breadth first, for each hierarchy
        hier = [False] + ([True] if self.joliet else [])
        self.dirs = {}
        for j in hier:
            order = []
            q = [(self.root, self.root)]
            while q:
                d, p = q.pop(0)
                order.append((d, p))
                kids = [c for c in d.children if c.kind == 'd']
                q += [(c, d) for c in kids]
            self.dirs[j] = order
        self.recs = {}
        for j in hier:
            for d, p in self.dirs[j]:
                self.recs[(j, id(d))] = self.records(d, p, j)
        # sizes of directories (records never cross a sector)
        def dir_size(recs):
            used, sectors = 0, 1
            for r in recs:
                n = len(self.rec_bytes(r, 0, 0, 0))
                count = len(self.expand(r) or [0])
                for _ in range(count):
                    if used + n > SECTOR:
                        sectors += 1
                        used = 0
                    used += n
            return sectors * SECTOR
        self.dsize = {k: dir_size(v) for k, v in self.recs.items()}
        nxt = 16 + 1 + (1 if self.joliet else 0) + 1
        # path tables (one sector each, L and M, per hierarchy)
        self.pt = {}
        for j in hier:
            self.pt[j] = (nxt, nxt + 1)
            nxt += 2
        self.dloc = {}
        for j in hier:
            for d, p in self.dirs[j]:
                self.dloc[(j, id(d))] = nxt
                nxt += self.dsize[(j, id(d))] // SECTOR
        # continuation areas
        self.ce_sectors = []
        cur, used = None, SECTOR
        for k in sorted(self.recs, key=lambda k: self.dloc[k]):
            for r in self.recs[k]:
                if r.su_ce:
                    area = b''.join(r.su_ce)
                    if used + len(area) > SECTOR:
                        cur = nxt
                        nxt += 1
                        used = 0
                        self.ce_sectors.append([cur, b''])
                    r.ce_loc = (cur, used, len(area))
                    self.ce_sectors[-1][1] += area
                    used += len(area)
        # file data, shared by both hierarchies
        self.floc = {}
        def files(d):
            for c in d.children:
                if c.kind == 'f':
                    yield c
                elif c.kind == 'd':
                    yield from files(c)
        for f in files(self.root):
            self.floc[id(f)] = nxt
            nxt += max(1, (len(f.data) + SECTOR - 1) // SECTOR) if f.data else 0
        self.total = nxt

    def dir_bytes(self, j, d):
        out, sector = b'', b''
        recs = self.recs[(j, id(d))]
        for r in recs:
            if r.self_of is not None:
                items = [(self.dloc[(j, id(d))], self.dsize[(j, id(d))], 2)]
            elif r.parent_of is not None:
                items = [(self.dloc[(j, id(r.node))], self.dsize[(j, id(r.node))], 2)]
            elif r.node.kind == 'd':
                items = [(self.dloc[(j, id(r.node))], self.dsize[(j, id(r.node))], 2)]
            elif r.node.kind == 'l':
                items = [(0, 0, 0)]
            else:
                loc = self.floc[id(r.node)] if r.node.data else 0
                sizes = self.expand(r)
                if sizes:
                    items, b = [], loc
                    for k, s in enumerate(sizes):
                        items.append((b, s, 0x80 if k < len(sizes) - 1 else 0))
                        b += s // SECTOR
                else:
                    items = [(loc, len(r.node.data), 0)]
            for ext, size, flags in items:
                rb = self.rec_bytes(r, ext, size, flags)
                if len(sector) + len(rb) > SECTOR:
                    out += sector + b'\0' * (SECTOR - len(sector))
                    sector = b''
                sector += rb
        out += sector + b'\0' * (SECTOR - len(sector))
        return out + b'\0' * (self.dsize[(j, id(d))] - len(out))

    def path_table(self, j, big):
        order = self.dirs[j]
        num = {id(d): k + 1 for k, (d, p) in enumerate(order)}
        out = b''
        for d, p in order:
            if d is self.root:
                ident = b'\0'
            else:
                rec = [r for r in self.recs[(j, id(p))] if r.node is d and r.self_of is None and r.parent_of is None][0]
                ident = rec.ident
            loc = self.dloc[(j, id(d))]
            out += bytes([len(ident), 0]) + (struct.pack('>I', loc) if big else struct.pack('<I', loc))
            out += struct.pack('>H' if big else '<H', num[id(p)]) + ident + (b'\0' if len(ident) % 2 else b'')
        return out

    def vd(self, kind, j):
        root = self.root
        rr = Rec(b'\0', root, True, self_of=root)
        rootrec = self.rec_bytes(rr, self.dloc[(j, id(root))], self.dsize[(j, id(root))], 2)
        assert len(rootrec) == 34
        txt = (lambda s, n: (s.encode('utf-16-be') + b'\0 ' * n)[:n]) if j else (lambda s, n: pad_field(s.encode(), n))
        ptl, ptm = self.pt[j]
        b = bytes([kind]) + b'CD001' + bytes([1, 0])
        b += txt('LINUX', 32) + txt(self.volid, 32) + b'\0' * 8 + both32(self.total)
        b += (pad_field(b'%/E', 32, b'\0') if j else b'\0' * 32)
        b += both16(1) + both16(1) + both16(SECTOR) + both32(len(self.path_table(j, False)))
        b += struct.pack('<I', ptl) + struct.pack('<I', 0) + struct.pack('>I', ptm) + struct.pack('>I', 0)
        b += rootrec
        b += txt('', 128) + txt('BEND OSDEV', 128) + txt('', 128) + txt('GEN.PY', 128)
        b += txt('', 37) + txt('', 37) + txt('', 37)
        b += vol_date(DATE + (16,)) + vol_date(DATE + (16,)) + vol_date(None) + vol_date(None)
        b += bytes([1, 0])
        assert len(b) == 883, len(b)
        return b + b'\0' * (SECTOR - len(b))

    def build(self):
        self.layout()
        img = bytearray(self.total * SECTOR)
        def put(n, data):
            img[n * SECTOR:n * SECTOR + len(data)] = data
        put(16, self.vd(1, False))
        s = 17
        if self.joliet:
            put(s, self.vd(2, True))
            s += 1
        put(s, bytes([255]) + b'CD001' + bytes([1]))
        for j in self.dirs:
            l, m = self.pt[j]
            put(l, self.path_table(j, False))
            put(m, self.path_table(j, True))
            for d, p in self.dirs[j]:
                put(self.dloc[(j, id(d))], self.dir_bytes(j, d))
        for n, data in self.ce_sectors:
            put(n, data)
        def files(d):
            for c in d.children:
                if c.kind == 'f':
                    yield c
                elif c.kind == 'd':
                    yield from files(c)
        for f in files(self.root):
            if f.data:
                put(self.floc[id(f)], f.data)
        return bytes(img)

# ---------------------------------------------------------------- the reader

class IsoErr(Exception):
    pass

class Reader:
    """An ISO 9660 reader: plain, Joliet and Rock Ridge naming."""
    def __init__(self, img, naming='auto', endian='check', strip=True, follow=True):
        self.img, self.endian, self.strip, self.follow = img, endian, strip, follow
        self.descs = []
        n = 16
        while True:
            if n - 16 >= 32:
                raise IsoErr('no descriptor set terminator')
            s = self.sector(n)
            if s[1:6] != b'CD001':
                raise IsoErr('no CD001 at sector %d' % n)
            if not (s[6] == 1 or (s[0] == 2 and s[6] == 2)):
                raise IsoErr('bad descriptor version at sector %d' % n)
            self.descs.append((s[0], s, n))
            if s[0] == 255:
                break
            n += 1
        prim = [s for t, s, n in self.descs if t == 1]
        if not prim:
            raise IsoErr('no primary volume descriptor')
        self.pvd = prim[0]
        self.space = self.b32(self.pvd, 80)
        bs = self.b16(self.pvd, 128)
        if bs != 2048:
            raise IsoErr('logical block size %d' % bs)
        self.boot = None
        for t, s, n in self.descs:
            if t == 0:
                self.boot = struct.unpack('<I', s[71:75])[0]
                break
        self.jl, self.svd = 0, None
        for t, s, n in self.descs:
            if t == 2 and s[88:90] == b'%/' and s[90] in (0x40, 0x43, 0x45):
                lv = {0x40: 1, 0x43: 2, 0x45: 3}[s[90]]
                if lv > self.jl:
                    self.jl, self.svd = lv, s
        self.skip = None
        if naming in ('auto', 'rockridge'):
            root = self.record(self.pvd[156:190], 0)
            first = self.record(self.sector(root['extent']), 0)
            su = first['su']
            if len(su) >= 7 and su[0:2] == b'SP' and su[4:6] == b'\xbe\xef':
                es = self.entries(su, 0)
                if any(e[0] in (b'RR', b'PX') or (e[0] == b'ER' and self.er_id(e[1]) in (b'RRIP_1991A', b'IEEE_P1282', b'IEEE_1282')) for e in es):
                    self.skip = su[6]
        if naming == 'auto':
            naming = 'rockridge' if self.skip is not None else ('joliet' if self.jl else 'plain')
        if naming == 'rockridge' and self.skip is None:
            raise IsoErr('no rock ridge')
        if naming == 'joliet' and not self.jl:
            raise IsoErr('no joliet')
        self.naming = naming
        self.rootrec = self.record((self.svd if naming == 'joliet' else self.pvd)[156:190], 0)

    def sector(self, n):
        if (n + 1) * SECTOR > len(self.img):
            raise IsoErr('device: block %d out of range' % n)
        return self.img[n * SECTOR:(n + 1) * SECTOR]

    def b32(self, b, off):
        lo, hi = struct.unpack('<I', b[off:off + 4])[0], struct.unpack('>I', b[off + 4:off + 8])[0]
        if self.endian == 'check' and lo != hi:
            raise IsoErr('both-endian halves differ at %d' % off)
        return hi if self.endian == 'big' else lo

    def b16(self, b, off):
        lo, hi = struct.unpack('<H', b[off:off + 2])[0], struct.unpack('>H', b[off + 2:off + 4])[0]
        if self.endian == 'check' and lo != hi:
            raise IsoErr('both-endian halves differ at %d' % off)
        return hi if self.endian == 'big' else lo

    def record(self, b, off):
        if len(b) - off < 33:
            raise IsoErr('truncated')
        r = b[off:]
        ln = r[0]
        rec = {'extent': self.b32(r, 2), 'size': self.b32(r, 10), 'flags': r[25], 'ea': r[1], 'unit': r[26]}
        self.b16(r, 28)
        lfi = r[32]
        if lfi < 1:
            raise IsoErr('bad identifier length %d' % lfi)
        fixed = 33 + lfi + (1 - lfi % 2)
        if fixed > ln:
            raise IsoErr('bad record length %d' % ln)
        if len(r) < ln:
            raise IsoErr('truncated')
        rec['ident'] = r[33:33 + lfi]
        rec['su'] = r[fixed:ln]
        rec['len'] = ln
        return rec

    def er_id(self, data):
        return data[4:4 + data[0]]

    def area(self, xs):
        out, i = [], 0
        while len(xs) - i >= 4:
            if xs[i] == 0 or xs[i:i + 2] == b'ST':
                break
            l = xs[i + 2]
            if l < 4 or i + l > len(xs):
                raise IsoErr('bad system use entry')
            out.append((xs[i:i + 2], xs[i + 4:i + l]))
            i += l
        return out

    def entries(self, su, skip, fuel=16):
        out = []
        xs = su[skip:]
        while True:
            es = self.area(xs)
            out += es
            ces = [e for e in es if e[0] == b'CE']
            if not ces:
                return out
            if fuel == 0:
                raise IsoErr('too many continuation areas')
            d = ces[0][1]
            if len(d) < 24:
                raise IsoErr('bad continuation area')
            b, o, l = self.b32(d, 0), self.b32(d, 8), self.b32(d, 16)
            blk = self.sector(b)
            if o + l > SECTOR:
                raise IsoErr('bad continuation area')
            xs = blk[o:o + l]
            fuel -= 1

    def rr(self, rec):
        es = self.entries(rec['su'], self.skip)
        info = {'name': None, 'link': None, 'cl': None, 're': False, 'px': None}
        comps = None
        for sig, d in es:
            if sig == b'PX':
                if len(d) < 32:
                    raise IsoErr('bad rock ridge PX')
                info['px'] = [self.b32(d, k) for k in (0, 8, 16, 24)]
            elif sig == b'PN':
                if len(d) < 16:
                    raise IsoErr('bad rock ridge PN')
            elif sig == b'NM':
                if len(d) < 1:
                    raise IsoErr('bad rock ridge NM')
                part = b'.' if d[0] & 2 else (b'..' if d[0] & 4 else d[1:])
                info['name'] = (info['name'] or b'') + part
            elif sig == b'SL':
                if len(d) < 1:
                    raise IsoErr('bad rock ridge SL')
                i, rs = 1, []
                while i < len(d):
                    if i + 2 > len(d) or i + 2 + d[i + 1] > len(d):
                        raise IsoErr('bad rock ridge SL')
                    rs.append((d[i], d[i + 2:i + 2 + d[i + 1]]))
                    i += 2 + d[i + 1]
                comps = (comps or []) + rs
            elif sig == b'CL':
                if len(d) < 8:
                    raise IsoErr('bad rock ridge CL')
                info['cl'] = self.b32(d, 0)
            elif sig == b'PL':
                if len(d) < 8:
                    raise IsoErr('bad rock ridge PL')
            elif sig == b'RE':
                info['re'] = True
            elif sig == b'TF':
                if len(d) < 1:
                    raise IsoErr('bad rock ridge TF')
                size = 17 if d[0] & 128 else 7
                need = 1 + size * bin(d[0] & 127).count('1')
                if len(d) < need:
                    raise IsoErr('bad rock ridge TF')
        if comps is not None:
            out, sep = '', False
            for fl, txt in comps:
                if fl & 8:
                    out += '/'
                elif fl & 2:
                    out += ('/' if sep else '') + '.'
                elif fl & 4:
                    out += ('/' if sep else '') + '..'
                else:
                    out += ('/' if sep else '') + txt.decode('latin-1')
                sep = not (fl & 8) and not (fl & 1)
            info['link'] = out
        return info

    def strip_name(self, s, plain):
        if not self.strip:
            return s
        r = s[::-1]
        k = 0
        while k < len(r) and r[k].isdigit():
            k += 1
        if k > 0 and k < len(r) and r[k] == ';':
            s = r[k + 1:][::-1]
        if plain and s.endswith('.'):
            s = s[:-1]
        return s

    def dir_records(self, ext, size):
        out = []
        left = size
        for i in range((size + SECTOR - 1) // SECTOR):
            blk = self.sector(ext + i)[:max(0, min(SECTOR, left))]
            off = 0
            while off < len(blk) and blk[off] != 0:
                r = self.record(blk, off)
                out.append(r)
                off += r['len']
            left -= SECTOR
        return out

    def listdir(self, ext, size):
        out, pending = [], []
        for r in self.dir_records(ext, size):
            if r['ident'] in (b'\0', b'\1'):
                continue
            exts = pending + [(r['extent'] + r['ea'], r['size'])]
            if r['flags'] & 0x80:
                pending = exts
                continue
            pending = []
            isdir = bool(r['flags'] & 2)
            link = None
            if self.naming == 'joliet':
                if len(r['ident']) % 2:
                    raise IsoErr('bad joliet name')
                name = self.strip_name(r['ident'].decode('utf-16-be'), False)
            elif self.naming == 'rockridge':
                info = self.rr(r)
                if self.follow and info['re']:
                    continue
                name = info['name'].decode('latin-1') if info['name'] is not None else self.strip_name(r['ident'].decode('latin-1'), True)
                link = info['link']
                if self.follow and info['cl'] is not None:
                    me = self.record(self.sector(info['cl']), 0)
                    exts = [(me['extent'] + me['ea'], me['size'])]
                    isdir = True
            else:
                name = self.strip_name(r['ident'].decode('latin-1'), True)
            out.append({'name': name, 'dir': isdir, 'exts': exts, 'link': link, 'unit': r['unit']})
        return out

    def walk(self, prefix='', ext=None, size=None, depth=64):
        if ext is None:
            ext, size = self.rootrec['extent'] + self.rootrec['ea'], self.rootrec['size']
        if ext + (size + SECTOR - 1) // SECTOR > self.space:
            raise IsoErr('extent %d out of range' % ext)
        items = []
        for e in self.listdir(ext, size):
            path = prefix + '/' + e['name']
            items.append((path, e))
            if e['dir'] and depth > 0:
                items += self.walk(path, e['exts'][0][0], e['exts'][0][1], depth - 1)
        return items

    def data(self, e):
        out = b''
        for b, s in e['exts']:
            out += self.img[b * SECTOR:b * SECTOR + s]
        return out

def show_name(s):
    return ''.join(c if 32 <= ord(c) < 127 and c != '\\' else '\\u{%x}' % ord(c) for c in s)

def item_line(path, e):
    size = sum(s for b, s in e['exts'])
    kind = 'd' if e['dir'] else ('l' if e['link'] is not None else 'f')
    return '%s %s %d%s' % (kind, show_name(path), size, (' -> ' + show_name(e['link'])) if e['link'] is not None else '')

# ---------------------------------------------------------------- tools

def have(*tools):
    return all(shutil.which(t) for t in tools)

def run(cmd):
    return subprocess.run(cmd, check=True, capture_output=True).stdout

def isoinfo_listing(path, flag):
    """{(dir, name, size): count} from isoinfo -l (flag: '', '-J' or '-R');
    a multi-extent file is listed once per extent."""
    out = run(['isoinfo'] + ([flag] if flag else []) + ['-l', '-i', path]).decode('latin-1')
    res, cur = {}, None
    for ln in out.split('\n'):
        if ln.startswith('Directory listing of '):
            cur = ln[len('Directory listing of '):].rstrip('/')
            continue
        if ']' not in ln or cur is None:
            continue
        head, _, name = ln.partition(']')
        name = name[2:].rstrip(' ')
        if ' -> ' in name:
            name = name.split(' -> ')[0]
        if name in ('.', '..'):
            continue
        size = int(head.split()[4])
        res[(cur, name, size)] = res.get((cur, name, size), 0) + 1
    return res

def same(a, b, what):
    if a != b:
        ka, kb = set(a), set(b)
        print(what, 'only isoinfo:', sorted(ka - kb)[:5], 'only reader:', sorted(kb - ka)[:5],
              'counts:', [(k, a[k], b[k]) for k in ka & kb if a[k] != b[k]][:5], file=sys.stderr)
        raise AssertionError(what)

def reader_listing(rd, last_only=True):
    """The same from the reader (isoinfo lists a multi-extent file by its
    last extent only)."""
    res = {}
    for path, e in rd.walk():
        d, _, n = path.rpartition('/')
        for b, s in (e['exts'][-1:] if last_only else e['exts']):
            res[(d, n, s)] = res.get((d, n, s), 0) + 1
    return res

def tree_items(node, prefix=''):
    out = []
    for c in node.children:
        p = prefix + '/' + c.name
        out.append((p, c))
        if c.kind == 'd':
            out += tree_items(c, p)
    return out

def check_against_tree(rd, tree, what, symlinks):
    """The reader's walk gives the tree back: names, kinds, link targets, data."""
    got = {p: e for p, e in rd.walk()}
    # genisoimage keeps the directory relocated directories were moved to
    # (empty once their RE entries are hidden)
    if '/rr_moved' in got and not any(p.startswith('/rr_moved/') for p in got):
        del got['/rr_moved']
    want = {p: c for p, c in tree_items(tree) if symlinks or c.kind != 'l'}
    assert set(got) == set(want), (what, sorted(set(got) ^ set(want))[:10])
    for p, c in want.items():
        e = got[p]
        assert e['dir'] == (c.kind == 'd'), (what, p)
        if c.kind == 'l':
            assert e['link'] == c.target, (what, p, e['link'], c.target)
        if c.kind == 'f':
            assert rd.data(e) == c.data, (what, p)

# ---------------------------------------------------------------- the cases

NAMING = {'auto': 'V.IsoNamingAuto{}', 'plain': 'V.IsoNamingPlain{}', 'joliet': 'V.IsoNamingJoliet{}', 'rockridge': 'V.IsoNamingRockRidge{}'}
ENDIAN = {'check': 'F.IsoEndianCheck{}', 'little': 'F.IsoEndianLittle{}', 'big': 'F.IsoEndianBig{}'}

def bend_str(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"') + '"'

def expect_case(img, naming, endian, ranges, follow=True):
    try:
        rd = Reader(img, naming, endian, follow=follow)
    except IsoErr as e:
        return ['open: ' + str(e)]
    try:
        items = rd.walk()
    except IsoErr as e:
        return ['walk: ' + str(e)]
    out = ['naming ' + rd.naming]
    for p, e in items:
        out.append(item_line(p, e))
    for p, e in items:
        if not e['dir'] and e['link'] is None:
            data = rd.data(e)
            out.append('crc %s %08x %d' % (show_name(p), zlib.crc32(data), len(data)))
    for p, off, n in ranges:
        e = dict(items)[p]
        data = rd.data(e)[off:off + n]
        out.append('range %s %d %d %08x %d' % (show_name(p), off, n, zlib.crc32(data), len(data)))
    if rd.boot is not None:
        out.append(boot_line(rd))
    return out

def boot_line(rd):
    c = rd.sector(rd.boot)
    words = struct.unpack('<16H', c[:32])
    if c[0] != 1 or sum(words) & 0xFFFF or c[30:32] != bytes([0x55, 0xAA]):
        return 'boot: bad boot catalog'
    seg, sec = struct.unpack('<H', c[34:36])[0], struct.unpack('<H', c[38:40])[0]
    rba = struct.unpack('<I', c[40:44])[0]
    return 'boot %d %s %d %d %d %d %d' % (rd.boot, 'bootable' if c[32] == 0x88 else 'not', c[33], seg, c[36], sec, rba)

def pick_ranges(rng, img, naming):
    try:
        rd = Reader(img, naming)
        items = [(p, e) for p, e in rd.walk() if not e['dir'] and e['link'] is None and sum(s for b, s in e['exts']) > 0]
    except IsoErr:
        return []
    out = []
    items.sort(key=lambda pe: -sum(s for b, s in pe[1]['exts']))
    for p, e in items[:2] + rng.sample(items, min(2, len(items))):
        size = sum(s for b, s in e['exts'])
        off = rng.randrange(0, size + 10)
        out.append((p, off, rng.randrange(0, 6000)))
    return out

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    tmp = sys.argv[2] if len(sys.argv) > 2 else '/tmp/iso9660-ref'
    os.makedirs(tmp, exist_ok=True)
    rng = random.Random(seed)
    cases = []   # (label, path, naming, endian, follow, ranges, expected lines)
    images = {}

    def add_image(label, img):
        path = os.path.join(tmp, label + '.iso')
        with open(path, 'wb') as f:
            f.write(img)
        images[label] = (path, img)
        return path

    def add_case(label, naming='auto', endian='check', follow=True, ranges=None):
        path, img = images[label]
        if ranges is None:
            ranges = pick_ranges(rng, img, naming)
        cases.append((label, path, len(img) // SECTOR, naming, endian, follow, ranges, expect_case(img, naming, endian, ranges, follow)))

    # Images from the builder here
    t1 = rand_tree(rng, 3, many=70)
    longs = [c.name for p, c in tree_items(t1) if c.kind == 'f'][:2]
    t1.children.append(Node('a name long enough to need two NM entries, ' + 'x' * 120 + '.txt', 'f', b'long name\n'))
    t1.children.append(Node('in-a-continuation-area.txt', 'f', b'NM and PX in a CE area\n'))
    t1.children.append(Node('multi.bin', 'f', bytes(rng.randrange(256) for _ in range(10000))))
    t1.children.append(Node('ln', 'l', target='/a/very/long/link/target/component/that/splits/' + 'q' * 70))
    b1 = Builder(t1, joliet=True, rr=True, force_ce=['in-a-continuation-area.txt'] + longs, multi_extent=['multi.bin'])
    own_rj = b1.build()
    add_image('own_rj', own_rj)
    for nm in ('auto', 'plain', 'joliet'):
        add_case('own_rj', nm)
    # ranges across the extents of the multi-extent file, and past its end
    add_case('own_rj', 'rockridge', ranges=[('/multi.bin', 3000, 5000), ('/multi.bin', 4090, 20), ('/multi.bin', 8190, 4000), ('/multi.bin', 0, 10000), ('/multi.bin', 10000, 5)])
    rd = Reader(own_rj, 'rockridge')
    check_against_tree(rd, t1, 'own_rj rr', True)
    t2 = rand_tree(rng, 2, long_names=False, symlinks=False)
    own_plain = Builder(t2).build()
    add_image('own_plain', own_plain)
    add_case('own_plain', 'auto')
    add_case('own_plain', 'rockridge')
    add_case('own_plain', 'joliet')
    t3 = rand_tree(rng, 2, symlinks=False, max_name=60)
    own_j = Builder(t3, joliet=True).build()
    add_image('own_j', own_j)
    add_case('own_j', 'auto')
    check_against_tree(Reader(own_j, 'joliet'), t3, 'own_j joliet', False)

    # Corruptions of the builder's images, and what each must give
    def corrupt(label, base, edits, naming='auto', endian='check', want=None):
        img = bytearray(images[base][1])
        for off, val in edits:
            img[off:off + len(val)] = val
        add_image(label, bytes(img))
        add_case(label, naming, endian, ranges=[])
        got = cases[-1][-1]
        assert want is None or got == [want], (label, got, want)
    pvd = 16 * SECTOR
    corrupt('bad_cd001', 'own_rj', [(pvd + 1, b'CD002')], want='open: no CD001 at sector 16')
    corrupt('bad_version', 'own_rj', [(pvd + 6, b'\x05')], want='open: bad descriptor version at sector 16')
    corrupt('bad_space', 'own_rj', [(pvd + 84, b'\0\0\0\1')], want='open: both-endian halves differ at 80')
    corrupt('bad_space_le', 'own_rj', [(pvd + 84, b'\0\0\0\1')], endian='little')
    corrupt('bad_blocksize', 'own_rj', [(pvd + 128, both16(1024))], want='open: logical block size 1024')
    corrupt('no_primary', 'own_rj', [(pvd, b'\x03')], want='open: no primary volume descriptor')
    # the first record after "\0" and "\1" of a subdirectory
    sub = [c for c in t1.children if c.kind == 'd'][0]
    loc = b1.dloc[(False, id(sub))] * SECTOR
    r0 = own_rj[loc]
    r1 = own_rj[loc + r0]
    rec = loc + r0 + r1
    corrupt('bad_reclen', 'own_rj', [(rec, b'\x14')], naming='plain', want='walk: bad record length 20')
    corrupt('bad_lenfi', 'own_rj', [(rec + 32, b'\0')], naming='plain', want='walk: bad identifier length 0')
    corrupt('bad_extent', 'own_rj', [(rec + 6, b'\xff')], naming='plain', want='walk: both-endian halves differ at 2')
    # a subdirectory's extent past the volume (both halves agreeing)
    subrec = [r for r in b1.recs[(False, id(t1))] if r.node is sub][0]
    sub_rb = b1.rec_bytes(subrec, b1.dloc[(False, id(sub))], b1.dsize[(False, id(sub))], 2)
    at_sub = own_rj.find(sub_rb[:33], 16 * SECTOR)
    assert at_sub > 0
    corrupt('bad_dir_extent', 'own_rj', [(at_sub + 2, both32(100000))], naming='plain', want='walk: extent 100000 out of range')
    lfi = own_rj[rec + 32]
    su = rec + 33 + lfi + (1 - lfi % 2)
    assert own_rj[su:su + 2] == b'PX'
    corrupt('bad_susp_len', 'own_rj', [(su + 2, b'\x02')], naming='rockridge', want='walk: bad system use entry')
    corrupt('bad_susp_past', 'own_rj', [(su + 2, b'\xf0')], naming='rockridge', want='walk: bad system use entry')
    corrupt('bad_px', 'own_rj', [(su + 2, b'\x0c'), (su + 12, b'TF\x04\x01')], naming='rockridge', want='walk: bad rock ridge PX')
    # a record with a CE entry: point it past the end of its block
    rec_ce = None
    for k, recs in b1.recs.items():
        if not k[0]:
            for r in recs:
                if r.su_ce and r.self_of is None and r.parent_of is None:
                    rec_ce = r
                    break
        if rec_ce:
            break
    ce_bytes = susp(b'CE', both32(rec_ce.ce_loc[0]) + both32(rec_ce.ce_loc[1]) + both32(rec_ce.ce_loc[2]))
    at = own_rj.find(ce_bytes)
    assert at > 0
    corrupt('bad_ce', 'own_rj', [(at + 12, both32(2040))], naming='rockridge', want='walk: bad continuation area')
    jroot = b1.dloc[(True, id(t1))] * SECTOR
    j0 = own_rj[jroot]
    j1 = own_rj[jroot + j0]
    jrec = jroot + j0 + j1
    jl = own_rj[jrec + 32]
    corrupt('bad_joliet', 'own_rj', [(jrec + 32, bytes([jl - 1]))], naming='joliet', want='walk: bad joliet name')

    n_tool, skipped = 0, 0
    # Images from genisoimage and xorriso, checked against their trees and isoinfo
    if have('genisoimage', 'isoinfo'):
        for k in range(3):
            t = rand_tree(rng, 3, many=40 if k == 0 else 0, max_name=40)
            src = os.path.join(tmp, 'tree%d' % k)
            write_tree(t, src)
            variants = [('gi_plain%d' % k, []), ('gi_j%d' % k, ['-J']), ('gi_r%d' % k, ['-R']), ('gi_rj%d' % k, ['-r', '-J'])]
            for label, flags in variants:
                path = os.path.join(tmp, label + '.iso')
                run(['genisoimage', '-quiet', '-no-pad'] + flags + ['-V', 'GI%d' % k, '-o', path, src])
                img = open(path, 'rb').read()
                images[label] = (path, img)
                rd = Reader(img, 'auto')
                if '-R' in flags or '-r' in flags:
                    check_against_tree(rd, t, label, True)
                    same(isoinfo_listing(path, '-R'), reader_listing(rd, True), label)
                elif '-J' in flags:
                    check_against_tree(rd, t, label, False)
                    same(isoinfo_listing(path, '-J'), reader_listing(Reader(img, 'joliet', strip=False), True), label)
                rp = Reader(img, 'plain', strip=False)
                same(isoinfo_listing(path, ''), reader_listing(rp), label)
                add_case(label, 'auto')
                n_tool += 1
            add_case('gi_rj%d' % k, 'joliet')
            add_case('gi_rj%d' % k, 'plain')
        # deep directories: genisoimage relocates them (RE, CL, PL)
        t = deep_tree(rng, 10)
        src = os.path.join(tmp, 'deep')
        write_tree(t, src)
        path = os.path.join(tmp, 'gi_deep.iso')
        run(['genisoimage', '-quiet', '-no-pad', '-R', '-o', path, src])
        img = open(path, 'rb').read()
        images['gi_deep'] = (path, img)
        check_against_tree(Reader(img, 'auto'), t, 'gi_deep', True)
        add_case('gi_deep', 'auto')
        add_case('gi_deep', 'auto', follow=False, ranges=[])
        n_tool += 1
        # El Torito: a no-emulation boot image
        src = os.path.join(tmp, 'boot')
        write_tree(Node('', 'd', children=[Node('boot.img', 'f', bytes(rng.randrange(256) for _ in range(8192))), Node('readme.txt', 'f', b'boot me\n')]), src)
        path = os.path.join(tmp, 'gi_boot.iso')
        run(['genisoimage', '-quiet', '-no-pad', '-R', '-b', 'boot.img', '-c', 'boot.cat', '-no-emul-boot', '-boot-load-size', '4', '-o', path, src])
        img = open(path, 'rb').read()
        images['gi_boot'] = (path, img)
        info = run(['isoinfo', '-d', '-i', path]).decode('latin-1')
        rd = Reader(img, 'auto')
        assert 'boot catalog is in sector %d' % rd.boot in info, info
        c = rd.sector(rd.boot)
        rba = struct.unpack('<I', c[40:44])[0]
        for want in ('boot catalog is in sector %d' % rd.boot, 'Bootid %x' % c[32], 'Boot media %d' % c[33],
                     'Nsect %x' % struct.unpack('<H', c[38:40])[0], 'Bootoff %X %d' % (rba, rba)):
            assert want in info, (want, info)
        add_case('gi_boot', 'auto')
        n_tool += 1
        # isoinfo reads the builder's images
        for label in ('own_rj', 'own_plain', 'own_j'):
            path, img = images[label]
            info = run(['isoinfo', '-d', '-i', path]).decode('latin-1')
            assert 'Volume id: BENDISO' in info, info
            assert 'Logical block size is: 2048' in info, info
            assert 'Volume size is: %d' % (len(img) // SECTOR) in info, info
            if label == 'own_rj':
                assert 'Rock Ridge signatures version 1 found' in info, info
                assert 'Joliet with UCS level 3 found' in info, info
                same(isoinfo_listing(path, '-R'), reader_listing(Reader(img, 'rockridge'), True), label)
                same(isoinfo_listing(path, '-J'), reader_listing(Reader(img, 'joliet', strip=False), True), label)
            same(isoinfo_listing(path, ''), reader_listing(Reader(img, 'plain', strip=False)), label)
    else:
        skipped += 14
    if have('xorriso', 'isoinfo'):
        for k in range(2):
            t = rand_tree(rng, 3, many=30 if k else 0, max_name=40)
            src = os.path.join(tmp, 'xtree%d' % k)
            write_tree(t, src)
            label = 'xo_rj%d' % k
            path = os.path.join(tmp, label + '.iso')
            run(['xorriso', '-as', 'mkisofs', '-quiet', '-R', '-J', '-V', 'XO%d' % k, '-o', path, src])
            img = open(path, 'rb').read()
            images[label] = (path, img)
            check_against_tree(Reader(img, 'auto'), t, label, True)
            check_against_tree(Reader(img, 'joliet'), t, label + ' joliet', False)
            same(isoinfo_listing(path, '-R'), reader_listing(Reader(img, 'auto'), True), label)
            add_case(label, 'auto')
            add_case(label, 'joliet')
            n_tool += 1
    else:
        skipped += 2

    # cases.bend and expected.txt
    lines, expect = [], []
    for label, path, nblocks, naming, endian, follow, ranges, exp in cases:
        rs = '[' + ', '.join('Rg{%s, %dn, %dn}' % (bend_str(p), off, n) for p, off, n in ranges) + ']'
        lines.append('    run_case(%s, %s, %dn, %s, %s, %s, %s)' % (bend_str(label), bend_str(path), nblocks, NAMING[naming], ENDIAN[endian], 'True{}' if follow else 'False{}', rs))
        expect.append('== ' + label)
        expect += exp
    with open(os.path.join(here, 'cases.bend'), 'w') as f:
        f.write(open(os.path.join(here, 'harness.bend')).read())
        f.write('\ndef main() -> IO(Unit):\n  do IO<Unit>:\n' + '\n'.join(lines) + '\n')
    with open(os.path.join(here, 'expected.txt'), 'w', encoding='utf-8') as f:
        f.write('\n'.join(expect) + '\n')
    print('%d cases on %d images (%d built by genisoimage/xorriso; %d tool images skipped)' % (len(cases), len(images), n_tool, skipped))

main()
