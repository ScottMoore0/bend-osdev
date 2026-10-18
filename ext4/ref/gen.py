#!/usr/bin/env python3
"""Differential test for bend-osdev-ext4 (see run.sh).

  gen.py prepare SEED WORK        images, WORK/q1.txt and WORK/expected1.txt
  gen.py verify SEED WORK GOT1    checks the package's journal recoveries,
                                  commits and htree directories with the
                                  tools; WORK/q2.txt and WORK/expected2.txt

Images are made by mke2fs 1.47.0 (-O dir_index,has_journal,inline_data,
ea_inode,metadata_csum) from random trees (mke2fs -d), indexed by
e2fsck -fD, given attributes and journal transactions by debugfs, or given
logs written by model.py's writer. Expected answers come from the trees,
from debugfs (stat, ls, ea_list, dx_hash, journal_run) and from model.py,
an independent model of the formats written here (it shares an author with
the package); gen.py checks the model against debugfs where both answer.
Phase 2 checks what the package wrote: recovered images with e2fsck -fn
and against debugfs's journal_run, committed transactions by replaying them
with debugfs and with e2fsck, and directories the htree writer built by
writing them into an image (e2fsck -fn, debugfs, and lookups by the
package itself).
"""
import os, pickle, random, re, shutil, struct, subprocess, sys, uuid, zlib

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import model

FEATURES = "dir_index,has_journal,inline_data,ea_inode,metadata_csum"
ALNUM = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-."
HIGH = b"\xc3\xa9\xe2\x82\xac\xff\x80\xe9"

def run(cmd, check=True, **kw):
    r = subprocess.run(cmd, capture_output=True, **kw)
    if check and r.returncode != 0:
        raise SystemExit("failed (%d): %r\n%s" % (r.returncode, cmd, r.stderr.decode("latin1")))
    return r

def debugfs(img, req, write=False):
    args = ["debugfs"] + (["-w"] if write else []) + ["-R", req, img]
    return subprocess.run([a if isinstance(a, bytes) else a.encode() for a in args], capture_output=True).stdout

def debugfs_script(img, lines):
    path = img + ".cmds"
    with open(path, "wb") as f:
        f.write(b"\n".join(lines) + b"\n")
    run(["debugfs", "-w", "-f", path, img])

def h(b):
    return b.hex()

def lcg(seed, n):
    s, out = seed, []
    for _ in range(n):
        s = (s * 1103515245 + 12345) & 0xFFFFFFFF
        out.append((s >> 16) & 255)
    return bytes(reversed(out))

def name(rng, lo, hi, high=False):
    n = rng.randrange(lo, hi)
    chars = ALNUM + (HIGH if high else b"")
    while True:
        s = bytes(rng.choice(chars) for _ in range(n))
        if s not in (b".", b"..") and not s.startswith(b"-"):
            return s

class Image:
    def __init__(self, name, path, bs, count, verify=True):
        self.name, self.path, self.bs, self.count, self.verify = name, path, bs, count, verify
        self.q, self.exp = [], []

    def tokens(self):
        data = open(self.path, "rb").read()
        nz = [i for i in range(len(data) // self.bs) if any(data[i * self.bs:(i + 1) * self.bs])]
        t = ["image", self.name, self.path, str(self.bs), str(self.count), "1" if self.verify else "0", str(len(nz))]
        return t + [str(i) for i in nz] + self.q + ["run"]

    def expected(self):
        return ["== " + self.name, "open ok"] + self.exp

def mkfs(path, bs, blocks, extra=(), inodes=None, root=None, env=None):
    with open(path, "wb") as f:
        f.truncate(blocks * bs)
    cmd = ["mke2fs", "-q", "-F", "-t", "ext4", "-b", str(bs), "-O", FEATURES] + list(extra)
    if inodes:
        cmd += ["-N", str(inodes)]
    if root:
        cmd += ["-d", root]
    run(cmd + [path], env=env)

def ino_of(img, path):
    out = debugfs(img, b"stat " + path)
    m = re.search(rb"Inode: (\d+)", out)
    return int(m.group(1)) if m else None

def ls_p(img, path):
    """debugfs's listing: (inode, mode, name) in block order"""
    out = debugfs(img, b"ls -p " + path)
    ents = []
    for line in out.split(b"\n"):
        if not line.startswith(b"/"):
            continue
        parts = line.split(b"/")
        ents.append((int(parts[1]), int(parts[2], 8), b"/".join(parts[5:-2])))
    return ents

def ea_list(img, path):
    out = debugfs(img, b"ea_list " + path)
    names = []
    for line in out.split(b"\n")[1:]:
        m = re.match(rb"  (\S+) \((\d+)\)", line)
        if m:
            names.append((m.group(1), int(m.group(2))))
    return names

# Reading: trees, lookups, listings, contents, attributes, hashes

def reading_image(work, tag, rng, bs, blocks, hash_alg, unsigned, n_long, n_mid):
    root = os.path.join(work, tag + ".tree")
    shutil.rmtree(root, ignore_errors=True)
    os.makedirs(root)
    files = {}
    target = os.path.join(root, "target")
    with open(target, "wb") as f:
        f.write(b"many names, one inode")
    files[b"/target"] = b"many names, one inode"
    dirs = {b"/long": [], b"/mid": [], b"/small": [], b"/tiny": [], b"/sub": [], b"/sub/deeper": []}
    for d in dirs:
        os.makedirs(os.path.join(root, d.decode("latin1")[1:]).encode("latin1"), exist_ok=True)
    used = set()
    def fresh(lo, hi):
        while True:
            n = name(rng, lo, hi, unsigned)
            if n not in used:
                used.add(n)
                return n
    for _ in range(n_long):
        n = fresh(30, 70)
        os.link(target, os.path.join(root.encode(), b"long", n))
        dirs[b"/long"].append(n)
    for _ in range(n_mid):
        n = fresh(1, 16)
        data = bytes(rng.randrange(256) for _ in range(rng.choice([0, 3, 20, 59, 60, 61, 100, 140, 300, 2000])))
        with open(os.path.join(root.encode(), b"mid", n), "wb") as f:
            f.write(data)
        files[b"/mid/" + n] = data
        dirs[b"/mid"].append(n)
    for d, k in ((b"/small", 2), (b"/tiny", 7)):
        for _ in range(k):
            n = fresh(1, 9)
            data = bytes(rng.randrange(256) for _ in range(rng.randrange(0, 90)))
            with open(os.path.join(root.encode(), d[1:], n), "wb") as f:
                f.write(data)
            files[d + b"/" + n] = data
            dirs[d].append(n)
    for k in range(6):
        n = b"f%d" % k
        data = bytes(rng.randrange(256) for _ in range(rng.choice([10, 55, 90, 150, 1500, 5000])))
        with open(os.path.join(root.encode(), b"sub", b"deeper", n), "wb") as f:
            f.write(data)
        files[b"/sub/deeper/" + n] = data
    for p, ds, fs in os.walk(root):
        for x in fs + ds + [p]:
            os.utime(os.path.join(p, x) if x != p else p, (1700000000, 1700000000))
    img = os.path.join(work, tag + ".img")
    mkfs(img, bs, blocks, inodes=n_mid + 64, root=root)
    run(["tune2fs", "-E", "hash_alg=%s" % hash_alg, img])
    if unsigned:
        debugfs(img, b"ssv flags 2", write=True)
    subprocess.run(["e2fsck", "-fyD", img], capture_output=True)
    # attributes: in the inode, in the attribute block, in an EA inode
    attrs = {}
    cmds = []
    for k, path in enumerate(sorted(p for p in files if p.startswith(b"/sub/deeper/"))):
        vals = {}
        for j, size in enumerate(rng.sample([3, 30, 200, bs // 2, bs], rng.randrange(1, 4))):
            v = bytes(rng.randrange(1, 256) for _ in range(size))
            vf = os.path.join(work, "%s.ea%d.%d" % (tag, k, j))
            with open(vf, "wb") as f:
                f.write(v)
            an = b"user.a%d_%d" % (j, size)
            cmds.append(b"ea_set -f " + vf.encode() + b" " + path + b" " + an)
            vals[an] = v
        attrs[path] = vals
    debugfs_script(img, cmds)
    subprocess.run(["e2fsck", "-fy", img], capture_output=True)
    extra = []
    for _ in range(rng.randrange(2, 6)):
        extra.append(fresh(1, 12))
    if grow_inline_dir(img, bs, b"/small", extra, b"/target"):
        dirs[b"/small"] += extra
        inline_links = [b"/small/" + n for n in extra]
    else:
        inline_links = []
    fsck = subprocess.run(["e2fsck", "-fn", img], capture_output=True)
    if fsck.returncode != 0:
        raise SystemExit("the reading image %s is not clean" % tag)
    im = Image(tag, img, bs, blocks)
    tino = ino_of(img, b"/target")
    for p in inline_links:
        im.q += ["lookup", h(p)]
        im.exp.append("lookup %s %d file" % (h(p), tino))
    # contents as debugfs reads them (debugfs prints all 60 bytes of an
    # inline file's i_block, whatever its size)
    for p in sorted(files)[:12]:
        if debugfs(img, b"cat " + p)[:len(files[p])] != files[p]:
            raise SystemExit("debugfs reads %r differently from the tree" % p)
    for n in rng.sample(dirs[b"/long"], min(1000, len(dirs[b"/long"]))):
        im.q += ["lookup", h(b"/long/" + n)]
        im.exp.append("lookup %s %d file" % (h(b"/long/" + n), tino))
    for path in sorted(files):
        i = ino_of(img, path)
        im.q += ["lookup", h(path), "read", h(path)]
        im.exp.append("lookup %s %d file" % (h(path), i))
        im.exp.append("read %s %d %d" % (h(path), len(files[path]), zlib.crc32(files[path])))
    for _ in range(40):
        p = rng.choice([b"/long/", b"/mid/", b"/tiny/", b"/"]) + name(rng, 1, 40, unsigned)
        if p.split(b"/")[-1] in used:
            continue
        im.q += ["lookup", h(p)]
        im.exp.append("lookup %s err Ext4NotFound" % h(p))
    for d in (b"/small", b"/tiny", b"/mid", b"/sub", b"/"):
        im.q += ["list", h(d)]
        for i, mode, n in ls_p(img, d):
            ft = 2 if mode & 0o170000 == 0o040000 else 1
            im.exp.append("ent %s %s %d %d" % (h(d), h(n), i, ft))
        im.exp.append("ls %s end" % h(d))
    for path, vals in attrs.items():
        im.q += ["xattrs", h(path)]
        im.exp.append("xattrs %s" % h(path) + "".join(" %s=%d" % (h(n), sz) for n, sz in ea_list(img, path)))
        for an, v in vals.items():
            im.q += ["xattr", h(path), h(an)]
            im.exp.append("xattr %s %s %d %d" % (h(path), h(an), len(v), zlib.crc32(v)))
    im.q += ["xattr", h(b"/target"), h(b"user.none")]
    im.exp.append("xattr %s %s err Ext4NoXattr" % (h(b"/target"), h(b"user.none")))
    # hashes: the model, checked against debugfs for some
    for k in range(60):
        v = rng.randrange(6)
        seed = [rng.randrange(1 << 32) for _ in range(4)] if rng.random() < 0.4 else [0, 0, 0, 0]
        n = name(rng, 1, 90, True)
        mj, mn = model.dxhash(n, v, seed)
        if k < 15:
            us = str(uuid.UUID(bytes=b"".join(struct.pack("<I", x) for x in seed)))
            out = debugfs(img, b"dx_hash -h %d -s %s %s" % (v, us.encode(), n))
            m = re.search(rb"is 0x([0-9a-f]+) \(minor 0x([0-9a-f]+)\)", out)
            if not m or (int(m.group(1), 16), int(m.group(2), 16)) != (mj, mn):
                raise SystemExit("model hash disagrees with debugfs: %r %d %r" % (n, v, seed))
        im.q += ["hash", str(v)] + [str(x) for x in seed] + [h(n)]
        im.exp.append("hash %d %s %d %d" % (v, h(n), mj, mn))
    return im

# The journal

def jblocks(img):
    return [int(x) for x in debugfs(img, b"blocks <8>").split()]

def free_blocks(img, n, start):
    out = debugfs(img, b"ffb %d %d" % (n, start))
    m = re.search(rb"Free blocks found: ([\d ]+)", out)
    return [int(x) for x in m.group(1).split()] if m else []

def block_count(img):
    out = debugfs(img, b"stats")
    return int(re.search(rb"Block count:\s+(\d+)", out).group(1))

def get_block(path, bs, n):
    with open(path, "rb") as f:
        f.seek(n * bs)
        return f.read(bs)

def put_block(path, bs, n, data):
    assert len(data) == bs
    with open(path, "r+b") as f:
        f.seek(n * bs)
        f.write(data)

def sb_loc(bs):
    return (1, 0) if bs == 1024 else (0, 1024)

def sb_bytes(path, bs):
    n, off = sb_loc(bs)
    return get_block(path, bs, n)[off:off + 1024]

def with_sb(path, bs, sb):
    n, off = sb_loc(bs)
    blk = get_block(path, bs, n)
    return n, blk[:off] + sb + blk[off + 1024:]

def journal_image(work, tag, bs, wide):
    img = os.path.join(work, tag + ".img")
    mkfs(img, bs, 4096 if bs == 4096 else 16384, extra=[] if wide else ["-O", "^64bit"])
    return img

def crafted(work, tag, rng, bs, csum, wide, tail):
    """a log written by model.py's writer: random transactions of writes to
    free blocks and revokes, starting near the journal's end so it wraps,
    and an ending: complete, incomplete, or a corrupted commit, descriptor
    or data block"""
    img = journal_image(work, tag, bs, wide)
    jb = jblocks(img)
    raw = bytearray(get_block(img, bs, jb[0]))
    inc = 1 | (2 if wide else 0) | (16 if csum == 3 else 8 if csum == 2 else 0)
    struct.pack_into(">I", raw, 0x28, inc)
    if csum:
        raw[0x50] = 4
    g = model.Geom(bytes(raw))
    pool = free_blocks(img, 40, block_count(img) // 2 + rng.randrange(200))
    seq = rng.choice([1, rng.randrange(2, 1 << 31), 0xFFFFFFFE])
    start = rng.randrange(g.maxlen - 12, g.maxlen)
    p, s, written = start, seq, []
    ntx = rng.randrange(1, 6)
    for k in range(ntx):
        ws = []
        for b in rng.sample(pool, rng.randrange(1, 6)):
            d = bytes(rng.randrange(256) for _ in range(bs))
            if rng.random() < 0.2:
                d = struct.pack(">I", model.MAGIC) + d[4:]
            ws.append((b, d))
        rv = rng.sample(written, min(len(written), rng.randrange(0, 3))) if written and rng.random() < 0.6 else []
        if rng.random() < 0.15:
            rv.append(ws[0][0])
        written += [b for b, _ in ws]
        blocks = model.transaction(g, s, ws, rv, 1700000000, 0)
        if k == ntx - 1:
            descs = [j for j, b in enumerate(blocks) if struct.unpack_from(">I", b, 4)[0] == 1]
            if tail == "incomplete":
                blocks = blocks[:-1]
            elif tail == "bad-commit":
                blocks[-1] = blocks[-1][:100] + bytes([blocks[-1][100] ^ 1]) + blocks[-1][101:]
            elif tail == "bad-desc":
                i = descs[0]
                blocks[i] = blocks[i][:bs - 40] + bytes([blocks[i][bs - 40] ^ 1]) + blocks[i][bs - 39:]
            elif tail == "bad-data":
                i = descs[0] + 1
                blocks[i] = blocks[i][:200] + bytes([blocks[i][200] ^ 1]) + blocks[i][201:]
        for b in blocks:
            put_block(img, bs, jb[p], b)
            p = g.next(p)
        s += 1
    put_block(img, bs, jb[p], bytes(bs))
    put_block(img, bs, jb[0], model.jsb_with(bytes(raw), start, seq))
    n, blk = with_sb(img, bs, model.super_with(sb_bytes(img, bs), set_bits=4))
    put_block(img, bs, n, blk)
    return img

def via_debugfs(work, tag, rng, bs, csum_arg, wide):
    """transactions written by debugfs's journal commands (journal_open,
    journal_write, journal_close)"""
    img = journal_image(work, tag, bs, wide)
    pool = free_blocks(img, 30, block_count(img) // 2)
    cmds = [b"jo" + csum_arg]
    written = []
    for k in range(rng.randrange(2, 6)):
        if written and rng.random() < 0.35:
            rv = rng.sample(written, min(len(written), rng.randrange(1, 3)))
            cmds.append(b"jw -r " + b",".join(b"%d" % b for b in rv))
            continue
        ws = rng.sample(pool, rng.randrange(1, 5))
        df = os.path.join(work, "%s.jw%d" % (tag, k))
        with open(df, "wb") as f:
            f.write(bytes(rng.randrange(256) for _ in range(bs * len(ws))))
        cmds.append(b"jw -b " + b",".join(b"%d" % b for b in ws) + b" " + df.encode())
        written += ws
    cmds.append(b"jc")
    debugfs_script(img, cmds)
    return img

def recovery_query(tag, rng, img, bs, state, verify=True, skip=True):
    jb = jblocks(img)
    g = model.Geom(get_block(img, bs, jb[0]))
    res = model.recover(g, lambda p: get_block(img, bs, jb[p]), verify, skip)
    count = os.path.getsize(img) // bs
    im = Image(tag, img, bs, count)
    if isinstance(res, str):
        im.q += ["recover", "1" if verify else "0", "1" if skip else "0", "0"]
        im.exp.append("recover err " + res)
        return im
    writes, ntx, skipped, nxt = res
    homes = sorted(set(b for b, _ in writes))
    sbn, _ = sb_loc(bs)
    show = sorted(set(homes) | {jb[0], sbn} | set(rng.sample(range(count), 4)))
    final = {}
    for b, d in writes:
        final[b] = d
    if g.start:
        final[jb[0]] = model.jsb_with(get_block(img, bs, jb[0]), 0, nxt)
    n, blk = with_sb(img, bs, model.super_with(sb_bytes(img, bs), clear_bits=4))
    final[n] = blk
    im.q += ["recover", "1" if verify else "0", "1" if skip else "0", str(len(show))] + [str(b) for b in show]
    im.exp.append("recover %d %d %d %d" % (ntx, len(writes), skipped, nxt))
    for b in show:
        im.exp.append("blk %d %s" % (b, h(final.get(b, get_block(img, bs, b)))))
    if verify and skip:
        # the tools' replay: a check of the model, and phase 2's reference
        jr = img + ".jr"
        shutil.copyfile(img, jr)
        debugfs(jr, b"jr", write=True)
        # (after skipping a block for its checksum e2fsprogs reports an
        # error and leaves s_sequence as it was; the package moves it on, as
        # after any recovery: README.md, "Specification")
        for b in homes + ([jb[0]] if g.start and not skipped else []):
            if get_block(jr, bs, b) != final[b]:
                raise SystemExit("%s: model and debugfs's journal_run disagree on block %d" % (tag, b))
        state.append(("recover", tag, img, bs, show, homes + ([jb[0]] if not skipped else [])))
    return im

def commit_query(work, tag, rng, bs, csum_arg, wide, state):
    img = journal_image(work, tag, bs, wide)
    if csum_arg:
        debugfs_script(img, [b"jo" + csum_arg, b"jc"])
    jb = jblocks(img)
    jsb = get_block(img, bs, jb[0])
    g = model.Geom(jsb)
    pool = free_blocks(img, 400, block_count(img) // 2)
    ws, specs = [], []
    for b in rng.sample(pool, rng.randrange(1, 300 if rng.random() < 0.3 else 8)):
        seed, magic = rng.randrange(1 << 32), rng.random() < 0.2
        d = lcg(seed, bs)
        if magic:
            d = struct.pack(">I", model.MAGIC) + d[4:]
        ws.append((b, d))
        specs += [str(b), str(seed), "1" if magic else "0"]
    taken = set(b for b, _ in ws)
    rv = rng.sample([b for b in pool if b not in taken], rng.randrange(0, 3))
    blocks = model.transaction(g, g.seq, ws, rv, 1700000000, 0)
    homes = [jb[g.first + k] for k in range(len(blocks))]
    sbn, _ = sb_loc(bs)
    show = homes + [jb[0], sbn]
    final = dict(zip(homes, blocks))
    final[jb[0]] = model.jsb_with(jsb, g.first, g.seq, set_incompat=1 if rv else 0)
    n, blk = with_sb(img, bs, model.super_with(sb_bytes(img, bs), set_bits=4))
    final[n] = blk
    im = Image(tag, img, bs, os.path.getsize(img) // bs)
    im.q += ["commit", str(len(rv))] + [str(b) for b in rv] + [str(len(ws))] + specs + [str(len(show))] + [str(b) for b in show]
    im.exp.append("commit %d %d" % (g.seq, len(blocks)))
    for b in show:
        im.exp.append("blk %d %s" % (b, h(final[b])))
    state.append(("commit", tag, img, bs, show, ws, rv))
    return im

# The htree writer

def build_query(work, tag, rng, bs, n_ents, hash_alg, unsigned, state):
    root = os.path.join(work, tag + ".tree")
    shutil.rmtree(root, ignore_errors=True)
    os.makedirs(os.path.join(root, "w", "sub"))
    target = os.path.join(root, "t")
    open(target, "wb").close()
    used = set()
    for _ in range(n_ents):
        n = name(rng, 1, 60, unsigned)
        if n in used or n == b"sub":
            continue
        used.add(n)
        os.link(target, os.path.join(root.encode(), b"w", n))
    img = os.path.join(work, tag + ".img")
    mkfs(img, bs, 4096 if bs == 4096 else 16384, inodes=64, root=root)
    run(["tune2fs", "-E", "hash_alg=%s" % hash_alg, img])
    if unsigned:
        debugfs(img, b"ssv flags 2", write=True)
    ino = ino_of(img, b"/w")
    gen = int(re.search(rb"Generation: (\d+)", debugfs(img, b"stat /w")).group(1))
    nblk = len(debugfs(img, b"blocks /w").split())
    ents = [(i, 2 if mode & 0o170000 == 0o040000 else 1, n) for i, mode, n in ls_p(img, b"/w") if n not in (b".", b"..")]
    sb = sb_bytes(img, bs)
    hseed = list(struct.unpack_from("<4I", sb, 0xEC))
    fl = struct.unpack_from("<I", sb, 0x160)[0]
    signed = bool(fl & 1) or not (fl & 2)
    fseed = model.crc32c(model.M32, sb[104:120])
    iseed = model.crc32c(model.crc32c(fseed, struct.pack("<I", ino)), struct.pack("<I", gen))
    blocks = model.htree_blocks(bs, sb[0xFC], signed, hseed, iseed, True, ino, 2, 2, nblk, ents)
    im = Image(tag, img, bs, os.path.getsize(img) // bs)
    im.q += ["build", str(ino), str(gen), "2", str(nblk), str(len(ents))]
    for i, ft, n in ents:
        im.q += [str(i), str(ft), h(n)]
    if blocks is None:
        im.exp.append("build err Ext4HtreeTooBig")
        return im
    im.exp.append("build %d" % len(blocks))
    for k, b in enumerate(blocks):
        im.exp.append("dirblk %d %s" % (k, h(b)))
    state.append(("build", tag, img, bs, ents, nblk))
    return im

# An inline directory with entries in its system.data value: e2fsprogs
# never writes one (it moves a full inline directory to a block), the
# kernel does, so gen.py writes one by hand into an inline directory
# mke2fs made: the entries go into the system.data value in the inode's
# attribute area, i_size grows, and the inode checksum is recomputed

def inode_loc(img, ino):
    out = debugfs(img, b"imap <%d>" % ino)
    m = re.search(rb"located at block (\d+), offset 0x([0-9a-f]+)", out)
    return int(m.group(1)), int(m.group(2), 16)

def inode_csum(raw, ino, fseed):
    gen = struct.unpack_from("<I", raw, 100)[0]
    seed = model.crc32c(model.crc32c(fseed, struct.pack("<I", ino)), struct.pack("<I", gen))
    z = bytearray(raw)
    struct.pack_into("<H", z, 124, 0)
    struct.pack_into("<H", z, 130, 0)
    c = model.crc32c(seed, bytes(z))
    b = bytearray(raw)
    struct.pack_into("<H", b, 124, c & 0xFFFF)
    struct.pack_into("<H", b, 130, c >> 16)
    return bytes(b)

def put_inode(img, bs, ino, raw, fseed):
    blk, off = inode_loc(img, ino)
    data = bytearray(get_block(img, bs, blk))
    data[off:off + len(raw)] = inode_csum(raw, ino, fseed)
    put_block(img, bs, blk, bytes(data))

def get_inode(img, bs, ino, isz):
    blk, off = inode_loc(img, ino)
    return get_block(img, bs, blk)[off:off + isz]

def grow_inline_dir(img, bs, path, names, target):
    sb = sb_bytes(img, bs)
    isz = struct.unpack_from("<H", sb, 88)[0]
    fseed = model.crc32c(model.M32, sb[104:120])
    ino, tino = ino_of(img, path), ino_of(img, target)
    raw = bytearray(get_inode(img, bs, ino, isz))
    area = 128 + struct.unpack_from("<H", raw, 128)[0]
    assert struct.unpack_from("<I", raw, area)[0] == 0xEA020000
    base, p, lowest, entry = area + 4, area + 4, isz - (area + 4), None
    while struct.unpack_from("<I", raw, p)[0] != 0:
        nl, ni, vo, vi, vs = struct.unpack_from("<BBHII", raw, p)
        if ni == 7 and raw[p + 16:p + 16 + nl] == b"data":
            entry = p
        elif vs:
            lowest = min(lowest, vo)
        p += (16 + nl + 3) // 4 * 4
    room = lowest - (p + 4 - base)
    value = b""
    for k, n in enumerate(names):
        rec = (8 + len(n) + 3) // 4 * 4
        value += struct.pack("<IHBB", tino, rec, len(n), 1) + n + bytes(rec - 8 - len(n))
    if len(value) > room:
        return 0
    # the last entry's rec_len reaches the value's end
    k = 0
    starts = []
    while k < len(value):
        starts.append(k)
        k += struct.unpack_from("<H", value, k + 4)[0]
    value = bytearray(value)
    struct.pack_into("<H", value, starts[-1] + 4, len(value) - starts[-1])
    off = (lowest - len(value)) // 4 * 4
    raw[base + off:base + off + len(value)] = value
    struct.pack_into("<HI", raw, entry + 2, off, 0)
    struct.pack_into("<I", raw, entry + 8, len(value))
    struct.pack_into("<I", raw, 4, 60 + len(value))
    put_inode(img, bs, ino, bytes(raw), fseed)
    traw = bytearray(get_inode(img, bs, tino, isz))
    struct.pack_into("<H", traw, 26, struct.unpack_from("<H", traw, 26)[0] + len(names))
    put_inode(img, bs, tino, bytes(traw), fseed)
    return len(names)

# Phase 2: what the package wrote, checked with the tools

def blocks_out(lines):
    out = {}
    for line in lines:
        if line.startswith("blk "):
            _, n, x = line.split()
            out[int(n)] = bytes.fromhex(x)
    return out

def section(got, tag):
    lines, on = [], False
    for line in got:
        if line.startswith("== "):
            on = line == "== " + tag
            continue
        if on:
            lines.append(line)
    return lines

def verify(work, got, state, rng):
    images, checks = [], 0
    for item in state:
        kind, tag, img, bs = item[:4]
        lines = section(got, tag)
        if kind == "recover":
            show, homes = item[4], item[5]
            mine = img + ".mine"
            shutil.copyfile(img, mine)
            for b, d in blocks_out(lines).items():
                put_block(mine, bs, b, d)
            r = subprocess.run(["e2fsck", "-fn", mine], capture_output=True)
            if r.returncode != 0:
                raise SystemExit("%s: e2fsck -fn finds the recovered image unclean:\n%s" % (tag, r.stdout.decode("latin1")[-2000:]))
            # the tools' own replays: debugfs's journal_run, and e2fsck's
            fsck = img + ".fsck"
            shutil.copyfile(img, fsck)
            subprocess.run(["e2fsck", "-fy", fsck], capture_output=True)
            for ref in (img + ".jr", fsck):
                for b in homes:
                    if get_block(mine, bs, b) != get_block(ref, bs, b):
                        raise SystemExit("%s: block %d differs from %s" % (tag, b, ref))
            checks += 1
        elif kind == "commit":
            ws, rv = item[5], item[6]
            mine = img + ".mine"
            shutil.copyfile(img, mine)
            for b, d in blocks_out(lines).items():
                put_block(mine, bs, b, d)
            for tool, path in (("debugfs", mine + ".jr"), ("e2fsck", mine + ".fsck")):
                shutil.copyfile(mine, path)
                if tool == "debugfs":
                    debugfs(path, b"jr", write=True)
                else:
                    subprocess.run(["e2fsck", "-fy", path], capture_output=True)
                for b, d in ws:
                    if get_block(path, bs, b) != d:
                        raise SystemExit("%s: %s's replay of the committed transaction differs at block %d" % (tag, tool, b))
            r = subprocess.run(["e2fsck", "-fn", mine + ".jr"], capture_output=True)
            if r.returncode != 0:
                raise SystemExit("%s: e2fsck -fn finds the image unclean after replaying the commit" % tag)
            checks += 1
        elif kind == "build":
            ents, nblk = item[4], item[5]
            dirb = {}
            for line in lines:
                if line.startswith("dirblk "):
                    _, k, x = line.split()
                    dirb[int(k)] = bytes.fromhex(x)
            if not dirb:
                continue
            mine = img + ".htree"
            shutil.copyfile(img, mine)
            for _ in range(len(dirb) - nblk):
                debugfs(mine, b"expand_dir /w", write=True)
            phys = [int(x) for x in debugfs(mine, b"blocks /w").split()]
            if len(phys) != len(dirb):
                raise SystemExit("%s: the directory has %d blocks for %d built" % (tag, len(phys), len(dirb)))
            for k, b in enumerate(phys):
                put_block(mine, bs, b, dirb[k])
            fl = int(re.search(rb"Flags: 0x([0-9a-f]+)", debugfs(mine, b"stat /w")).group(1), 16)
            debugfs(mine, b"sif /w flags 0x%x" % (fl | 0x1000), write=True)
            r = subprocess.run(["e2fsck", "-fn", mine], capture_output=True)
            if r.returncode != 0:
                raise SystemExit("%s: e2fsck -fn rejects the built htree directory:\n%s" % (tag, r.stdout.decode("latin1")[-2000:]))
            if b"Root node dump" not in debugfs(mine, b"htree_dump /w"):
                raise SystemExit("%s: debugfs does not see an htree" % tag)
            im = Image(tag + "-htree", mine, bs, os.path.getsize(mine) // bs)
            for i, ft, n in rng.sample(ents, min(600, len(ents))):
                im.q += ["lookup", h(b"/w/" + n)]
                im.exp.append("lookup %s %d %s" % (h(b"/w/" + n), i, "dir" if ft == 2 else "file"))
                if rng.random() < 0.1:
                    dn = debugfs(mine, b"stat /w/" + n)
                    if not re.search(rb"Inode: %d " % i, dn):
                        raise SystemExit("%s: debugfs does not find %r in the built directory" % (tag, n))
            for _ in range(20):
                n = name(rng, 1, 60)
                if any(n == e[2] for e in ents):
                    continue
                im.q += ["lookup", h(b"/w/" + n)]
                im.exp.append("lookup %s err Ext4NotFound" % h(b"/w/" + n))
            images.append(im)
            checks += 1
    return images, checks

def write(work, stem, images):
    with open(os.path.join(work, stem + ".txt"), "w") as f:
        for im in images:
            f.write(" ".join(im.tokens()) + "\n")
    with open(os.path.join(work, stem + ".expected"), "w") as f:
        for im in images:
            f.write("\n".join(im.expected()) + "\n")

def main():
    phase, seed, work = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    rng = random.Random(seed)
    if phase == "prepare":
        state, images = [], []
        images.append(reading_image(work, "read-1k", rng, 1024, 16384, "half_md4", False, 3000, 120))
        images.append(reading_image(work, "read-4k-tea-unsigned", rng, 4096, 4096, "tea", True, 400, 60))
        images.append(reading_image(work, "read-1k-legacy", rng, 1024, 8192, "legacy", False, 300, 40))
        for k, (bs, arg, wide) in enumerate([(1024, b"", True), (1024, b" -c -v 2", True), (4096, b" -c", True), (1024, b" -c", False)]):
            tag = "jbd-%d" % k
            images.append(recovery_query(tag, rng, via_debugfs(work, tag, rng, bs, arg, wide), bs, state))
        for k, (bs, csum, wide, tail) in enumerate([(1024, 3, True, "ok"), (1024, 0, True, "incomplete"), (1024, 2, True, "bad-commit"),
                                                    (4096, 3, True, "bad-desc"), (1024, 3, True, "bad-data"), (1024, 0, False, "ok"),
                                                    (1024, 3, False, "incomplete"), (4096, 2, True, "ok")]):
            tag = "craft-%d-%s" % (k, tail)
            images.append(recovery_query(tag, rng, crafted(work, tag, rng, bs, csum, wide, tail), bs, state))
        tag = "craft-strict"
        images.append(recovery_query(tag, rng, crafted(work, tag, rng, 1024, 3, True, "bad-data"), 1024, state, True, False))
        for k, (bs, arg, wide) in enumerate([(1024, b"", True), (1024, b" -c", True), (4096, b" -c -v 2", True), (1024, b" -c", False), (4096, b"", False)]):
            images.append(commit_query(work, "commit-%d" % k, rng, bs, arg, wide, state))
        for k, (bs, n, alg, uns) in enumerate([(1024, 500, "half_md4", False), (1024, 3500, "half_md4", False), (4096, 900, "tea", True), (1024, 200, "legacy", False)]):
            images.append(build_query(work, "build-%d" % k, rng, bs, n, alg, uns, state))
        write(work, "q1", images)
        with open(os.path.join(work, "state"), "wb") as f:
            pickle.dump(state, f)
        print(sum(len(im.exp) for im in images), "answers,", len(images), "images")
    else:
        got = open(sys.argv[4], encoding="latin1").read().split("\n")
        state = pickle.load(open(os.path.join(work, "state"), "rb"))
        images, checks = verify(work, got, state, rng)
        write(work, "q2", images)
        print(checks, "tool checks;", sum(len(im.exp) for im in images), "answers on", len(images), "built directories")

main()
