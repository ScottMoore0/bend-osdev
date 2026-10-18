#!/usr/bin/env python3
"""Differential test cases for bend-osdev-ext2.

  gen.py SEED DIR

Builds small ext2, ext3 and ext4 images in DIR with mke2fs, each populated
(mke2fs -d) from a random directory tree written here: nested directories,
empty, small and large files, sparse files (holes; one reaching the triply
indirect block), fast and slow symbolic links, absolute links, chains and
loops, and a directory of many entries (indexed by e2fsck -D on some
images). Then it writes ref/cases-NN.bend (one Bend program per image, which
reads the image a block at a time through ref/image.bend's device and asks it
the queries of ref/driver.bend) and ref/expected.txt, the answers expected:

  * listings, inode numbers, sizes, modes and link counts from the tree on
    disk and from `debugfs -R "ls -l"` and `debugfs -R stat`, which must
    agree with each other;
  * file contents (streamed a block at a time, CRC-32) from the files on
    disk, checked against `debugfs -R cat`; byte ranges from the files;
  * block numbers from `debugfs -R bmap`;
  * symbolic link targets from os.readlink, and path lookups that follow
    links from a model of path resolution written here;
  * refusals: images corrupted after mke2fs wrote them (raw bytes, or
    structured edits through `debugfs -w`, which keeps checksums right) must
    be refused with the error the corruption calls for.

The images stay in DIR (run.sh makes it a temporary directory); only
cases-NN.bend and expected.txt are written into ref/.
"""
import os, random, shutil, stat, string, struct, subprocess, sys, zlib

HERE = os.path.dirname(os.path.abspath(__file__))

def run(*args):
    return subprocess.run(args, check=True, capture_output=True, text=True).stdout

def dbg(img, cmd, write=False):
    args = ["debugfs"] + (["-w"] if write else []) + ["-R", cmd, img]
    return subprocess.run(args, capture_output=True, text=True).stdout

def h(b):
    return b.hex()

# ---------------------------------------------------------------- trees

NAMECH = string.ascii_letters + string.digits + "._-"

def rname(rng, used, lo=1, hi=24):
    while True:
        n = "".join(rng.choice(NAMECH) for _ in range(rng.randint(lo, hi)))
        if n not in (".", "..", "lost+found") and n not in used:
            used.add(n)
            return n

def write_sparse(path, islands, size):
    with open(path, "wb") as f:
        for off, data in islands:
            f.seek(off)
            f.write(data)
        f.truncate(size)

def make_tree(rng, root, cfg):
    """A random tree under root; cfg: big (allow a large file), tri (a
    file reaching the triply indirect block), many (a directory of many
    entries)."""
    os.makedirs(root)
    dirs = [root]
    files, links = [], []
    def rdir():
        return rng.choice(dirs)
    used = {d: set() for d in dirs}
    def name_in(d, lo=1, hi=24):
        used.setdefault(d, set())
        return rname(rng, used[d], lo, hi)
    for _ in range(rng.randint(3, 6)):
        parent = rng.choice(dirs)
        if len(os.path.relpath(parent, root).split(os.sep)) > 3:
            continue
        d = os.path.join(parent, name_in(parent))
        os.mkdir(d)
        dirs.append(d)
    # files
    for _ in range(rng.randint(6, 12)):
        d = rdir()
        p = os.path.join(d, name_in(d))
        kind = rng.choice(["empty", "tiny", "small", "small", "medium"])
        n = {"empty": 0, "tiny": rng.randint(1, 60), "small": rng.randint(100, 3000), "medium": rng.randint(5000, 20000)}[kind]
        with open(p, "wb") as f:
            f.write(bytes(rng.randrange(256) for _ in range(n)))
        files.append(p)
    if cfg.get("big"):
        p = os.path.join(root, name_in(root))
        n = rng.randint(cfg["big"] // 2, cfg["big"])
        with open(p, "wb") as f:
            f.write(bytes(rng.randrange(256) for _ in range(n)))
        files.append(p)
    # sparse files: islands of data between holes
    d = rdir()
    p = os.path.join(d, name_in(d))
    islands = []
    off = rng.randint(0, 3000)
    for _ in range(rng.randint(5, 9)):
        islands.append((off, bytes(rng.randrange(1, 256) for _ in range(rng.randint(1, 2500)))))
        off += rng.randint(8000, 40000)
    write_sparse(p, islands, off)
    files.append(p)
    sparse = (p, islands)
    if cfg.get("tri"):
        p = os.path.join(root, name_in(root))
        write_sparse(p, [(rng.randint(0, 100), b"head"), (cfg["tri"], b"far" * 30)], cfg["tri"] + 90)
        files.append(p)
    if cfg.get("many"):
        d = os.path.join(root, name_in(root))
        os.mkdir(d)
        dirs.append(d)
        for i in range(cfg["many"]):
            p = os.path.join(d, name_in(d, 20, 60))
            with open(p, "wb") as f:
                f.write(str(i).encode())
            files.append(p)
    if cfg.get("wide"):
        # a directory of many empty files: listed, and its last file looked
        # up, but not read one by one
        d = os.path.join(root, name_in(root))
        os.mkdir(d)
        dirs.append(d)
        for i in range(cfg["wide"]):
            p = os.path.join(d, name_in(d, 8, 16))
            open(p, "wb").close()
        files.append(p)
    # a long name
    d = rdir()
    p = os.path.join(d, name_in(d, 200, 255))
    open(p, "wb").write(b"long name")
    files.append(p)
    # symbolic links: relative fast ones, slow ones, absolute, to a
    # directory, dangling, a chain and a loop
    def rel(frm, to):
        return os.path.relpath(to, os.path.dirname(frm))
    for _ in range(rng.randint(2, 4)):
        d = rdir()
        lp = os.path.join(d, name_in(d))
        t = rng.choice(files)
        os.symlink(rel(lp, t), lp)
        links.append(lp)
    for _ in range(2):
        d = rdir()
        lp = os.path.join(d, name_in(d))
        t = rng.choice(files)
        target = rel(lp, t)
        # pad the target past 60 bytes with ./ segments
        target = ("./" * ((80 - len(target)) // 2 + 1)) + target
        os.symlink(target, lp)
        links.append(lp)
    d = rdir()
    lp = os.path.join(d, name_in(d))
    os.symlink("/" + os.path.relpath(rng.choice(files), root), lp)
    links.append(lp)
    sub = [x for x in dirs if x != root] or [root]
    d = rdir()
    lp = os.path.join(d, name_in(d))
    os.symlink(rel(lp, rng.choice(sub)), lp)
    links.append(lp)
    lp = os.path.join(root, name_in(root))
    os.symlink("no/such/" + "x" * rng.randint(1, 120), lp)
    links.append(lp)
    a = os.path.join(root, name_in(root))
    b = os.path.join(root, name_in(root))
    os.symlink(os.path.basename(a), b)
    os.symlink(os.path.basename(rng.choice([x for x in links if os.path.dirname(x) == root] or [b])), a)
    links += [a, b]
    l1 = os.path.join(root, name_in(root))
    l2 = os.path.join(root, name_in(root))
    os.symlink(os.path.basename(l1), l2)
    os.symlink(rel(l1, rng.choice(files)), l1)
    links += [l1, l2]
    return dirs, files, links, sparse

# ---------------------------------------------------------------- the model

def resolve(root, path, hops, follow_last):
    """Path resolution as the package defines it: from the root, a link in
    the middle of a path (or at its end, with follow_last) is followed while
    hops remain; ".." and "." are the directories' own entries."""
    never = hops == 0
    def comps(p):
        return [c for c in p.split("/") if c]
    cur = root
    rest = comps(path)
    steps = 0
    while rest:
        steps += 1
        c = rest.pop(0)
        if not os.path.isdir(cur) or os.path.islink(cur):
            return ("err", "Ext2NotDir")
        if c == "..":
            nxt = cur if cur == root else os.path.dirname(cur)
        elif c == ".":
            nxt = cur
        else:
            nxt = os.path.join(cur, c)
            if not os.path.lexists(nxt):
                return ("err", "Ext2NotFound")
        if os.path.islink(nxt) and (rest or (follow_last and not never)):
            if hops == 0:
                return ("err", "Ext2SymlinkInPath" if never else "Ext2SymlinkLoop")
            hops -= 1
            t = os.readlink(nxt)
            base = root if t.startswith("/") else cur
            rest = comps(t) + rest
            cur = base
            continue
        cur = nxt
    return ("ok", cur)

# ---------------------------------------------------------------- debugfs

def ls_l(img, path):
    out = []
    for line in dbg(img, "ls -l %s" % path).splitlines():
        w = line.split(None, 8)
        if len(w) == 9 and w[0].isdigit():
            out.append((int(w[0]), int(w[1], 8), w[8]))
    return out

def dstat(img, path):
    out = dbg(img, "stat %s" % path)
    info = {}
    for line in out.splitlines():
        w = line.split()
        if line.startswith("Inode:"):
            info["ino"] = int(w[1])
            info["mode"] = int(w[5], 8)
        if "Links:" in line:
            info["links"] = int(w[w.index("Links:") + 1])
        if line.startswith("User:") and "Size:" in w:
            info["size"] = int(w[w.index("Size:") + 1])
    return info

def dumpe2fs(img):
    out = subprocess.run(["dumpe2fs", "-h", img], capture_output=True, text=True).stdout
    d = {}
    for line in out.splitlines():
        if ":" in line:
            k, v = line.split(":", 1)
            d[k.strip()] = v.strip()
    return d

def imap(img, path):
    out = dbg(img, "imap %s" % path)
    blk = off = None
    for line in out.splitlines():
        w = line.split()
        if "located at block" in line:
            blk = int(w[3].rstrip(","))
            off = int(w[5], 16)
    return blk, off

def bmap(img, path, l):
    out = dbg(img, "bmap %s %d" % (path, l)).split()
    return 0 if "(uninit)" in out else int(out[0])

# ---------------------------------------------------------------- images

def bend_path(p):
    return 'B.Octets.of_string("%s")' % p

def opts(verify=True, incompat=None, recovery=False):
    o = "O.Ext2Options.default()"
    if not verify:
        o = "O.Ext2Options.with_verify(%s, False{})" % o
    if incompat is not None:
        o = "O.Ext2Options.with_incompat(%s, %d)" % (o, incompat)
    if recovery:
        o = "O.Ext2Options.with_recovery(%s, True{})" % o
    return o

class Image:
    def __init__(self, name, path, devbs, options="O.Ext2Options.default()"):
        self.name, self.path, self.devbs, self.options = name, path, devbs, options
        self.queries, self.expect = [], []
    def q(self, query, *lines):
        self.queries.append(query)
        self.expect.extend(lines)
    def bend(self):
        count = (os.path.getsize(self.path) + self.devbs - 1) // self.devbs
        nz = []
        with open(self.path, "rb") as f:
            for k in range(count):
                if any(f.read(self.devbs)):
                    nz.append(k)
        # long lists are built from pieces (a literal over a few thousand
        # elements is too deep for the runtime)
        # (each piece in front of the rest, so no append walks more than
        # one piece)
        pieces = ["[%s]" % ", ".join("%dn" % k for k in nz[i:i + 500]) for i in range(0, len(nz), 500)] or ["[]"]
        lst = pieces[-1]
        for p in reversed(pieces[:-1]):
            lst = "List.append(&2, Nat, %s, %s)" % (p, lst)
        return 'R.Ext2Img{"%s", "%s", %dn, %dn, %s, %s, [%s]}' % (self.name, self.path, self.devbs, count, lst, self.options, ", ".join(self.queries))

def fs_info(img):
    d = dumpe2fs(img)
    bs = int(d["Block size"])
    blocks = int(d["Block count"])
    first = int(d["First block"])
    bpg = int(d["Blocks per group"])
    groups = (blocks - first + bpg - 1) // bpg
    feats = d.get("Filesystem features", "").split()
    return bs, blocks, groups, feats

def ftype(p, filetype):
    if not filetype:
        return 0
    st = os.lstat(p)
    if stat.S_ISLNK(st.st_mode):
        return 7
    if stat.S_ISDIR(st.st_mode):
        return 2
    return 1

def kind(p):
    st = os.lstat(p)
    return "symlink" if stat.S_ISLNK(st.st_mode) else "dir" if stat.S_ISDIR(st.st_mode) else "file"

def tree_queries(rng, im, img, root, dirs, files, links, sums=()):
    bs, blocks, groups, feats = fs_info(img)
    filetype = "filetype" in feats
    im.expect.append("open ok %d %d %d" % (bs, blocks, groups))
    inode_of = {"/": 2}
    # listings: debugfs's, checked against the tree
    for d in sorted(dirs):
        rp = "/" + os.path.relpath(d, root) if d != root else "/"
        ents = ls_l(img, rp)
        names = sorted(n for _, _, n in ents)
        want = sorted([".", ".."] + os.listdir(d) + (["lost+found"] if d == root else []))
        assert names == want, ("listing", rp, names, want)
        lines = []
        for ino, mode, n in ents:
            full = os.path.join(d, n)
            if n == ".":
                ft = 2 if filetype else 0
            elif n == "..":
                ft = 2 if filetype else 0
            elif n == "lost+found" and d == root:
                ft = 2 if filetype else 0
            else:
                ft = ftype(full, filetype)
                inode_of[os.path.join(rp, n) if rp != "/" else "/" + n] = ino
            lines.append("ls %s %s %d %d" % (h(rp.encode()), h(n.encode()), ino, ft))
        lines.append("ls %s end" % h(rp.encode()))
        im.q("R.Ext2QLs{%s}" % bend_path(rp), *lines)
    def rel(p):
        return "/" + os.path.relpath(p, root)
    # stat every path
    for p in sorted(set(dirs[1:] + files + links)):
        rp = rel(p)
        st = os.lstat(p)
        info = dstat(img, rp)
        assert info["ino"] == inode_of[rp], (rp, info, inode_of[rp])
        assert info["mode"] == st.st_mode & 0o7777, (rp, info, oct(st.st_mode))
        k = kind(p)
        size = info["size"]
        if k == "file":
            assert size == st.st_size, (rp, size, st.st_size, info)
        if k == "symlink":
            assert size == len(os.readlink(p).encode()), (rp, size, os.readlink(p), info)
        im.q("R.Ext2QStat{%s}" % bend_path(rp), "stat %s %d %s %d %d %d" % (h(rp.encode()), info["ino"], k, size, info["links"], st.st_mode & 0o7777))
    # file contents, streamed; and ranges
    for p in sorted(files):
        rp = rel(p)
        data = open(p, "rb").read()
        if len(data) < 4096:
            assert subprocess.run(["debugfs", "-R", "cat %s" % rp, img], capture_output=True).stdout == data, rp
        nblk = (len(data) + bs - 1) // bs
        if len(data) > 1 << 20:
            # the far sparse file: its blocks are tested by bmap and its
            # last bytes by a range (streaming 70 MB of holes is too slow)
            off = len(data) - 100
            im.q("R.Ext2QRange{%s, %dn, %dn}" % (bend_path(rp), off, 200), "range %s %d %d =%s" % (h(rp.encode()), off, 200, h(data[off:])))
            continue
        im.q("R.Ext2QCat{%s}" % bend_path(rp), "cat %s %d %d %d" % (h(rp.encode()), nblk, len(data), zlib.crc32(data)))
    for p in rng.sample(sorted(files), min(4, len(files))):
        rp = rel(p)
        data = open(p, "rb").read()
        off = rng.randint(0, len(data) + 5)
        n = rng.randint(0, 120)
        im.q("R.Ext2QRange{%s, %dn, %dn}" % (bend_path(rp), off, n), "range %s %d %d =%s" % (h(rp.encode()), off, n, h(data[off:off + n])))
    # whole files by range, as length and CRC-32
    for p in sums:
        rp = rel(p)
        data = open(p, "rb").read()
        im.q("R.Ext2QSum{%s, 0n, %dn}" % (bend_path(rp), len(data)), "sum %s 0 %d %d %d" % (h(rp.encode()), len(data), len(data), zlib.crc32(data)))
    # block numbers
    far = [p for p in files if os.path.getsize(p) > 1 << 20]
    for p in far + rng.sample(sorted(files), min(4, len(files))):
        rp = rel(p)
        size = os.path.getsize(p)
        nblk = (size + bs - 1) // bs
        for l in sorted(set([0, nblk - 1, rng.randint(0, max(nblk - 1, 0)), nblk])):
            if l < 0:
                continue
            if l >= nblk:
                want = "err Ext2PastEnd"
            else:
                b = bmap(img, rp, l)
                want = "hole" if b == 0 else str(b)
            im.q("R.Ext2QMap{%s, %dn}" % (bend_path(rp), l), "bmap %s %d %s" % (h(rp.encode()), l, want))
    # links, and lookups through them
    for p in sorted(links):
        rp = rel(p)
        im.q("R.Ext2QLink{%s}" % bend_path(rp), "link %s =%s" % (h(rp.encode()), h(os.readlink(p).encode())))
    probes = [rel(p) for p in links]
    for p in links:
        if os.path.isdir(p):
            for c in os.listdir(p)[:2]:
                probes.append(rel(p) + "/" + c)
    probes += ["/" + rel(rng.choice(files)).lstrip("/") + "/x", "/no-such-name", "/" + rel(rng.choice(dirs)).lstrip("/") + "/../" + rel(rng.choice(files)).lstrip("/")]
    for rp in probes:
        for hops in (0, 1, 8):
            r = resolve(root, rp, hops, True)
            if r[0] == "ok":
                got = r[1]
                ino = 2 if got == root else inode_of["/" + os.path.relpath(got, root)]
                want = str(ino)
            else:
                want = "err " + r[1]
            im.q("R.Ext2QFollow{%s, %dn}" % (bend_path(rp), hops), "follow %s %d %s" % (h(rp.encode()), hops, want))
    return inode_of

# ---------------------------------------------------------------- crc32c (for patching superblocks)

def crc32c_raw(c, data):
    for b in data:
        c ^= b
        for _ in range(8):
            c = (c >> 1) ^ 0x82F63B78 if c & 1 else c >> 1
    return c

def patch(img, off, data):
    with open(img, "r+b") as f:
        f.seek(off)
        f.write(data)

def read(img, off, n):
    with open(img, "rb") as f:
        f.seek(off)
        return f.read(n)

def fix_sb_csum(img):
    sb = read(img, 1024, 1024)
    if struct.unpack("<I", sb[100:104])[0] & 0x400:
        patch(img, 1024 + 1020, struct.pack("<I", crc32c_raw(0xFFFFFFFF, sb[:1020])))

def set_sb_u32(img, off, v, fix=True):
    patch(img, 1024 + off, struct.pack("<I", v))
    if fix:
        fix_sb_csum(img)

# ---------------------------------------------------------------- main

CONFIGS = [  # name, mke2fs arguments, size in MiB, device block size, tree options, post-processing
    ("ext2-1k", ["-t", "ext2", "-b", "1024"], 3, 1024, {"big": 300000, "tri": 70 * 1024 * 1024}, None),
    ("ext2-4k", ["-t", "ext2", "-b", "4096"], 4, 4096, {"big": 200000}, None),
    ("ext2-groups", ["-t", "ext2", "-b", "1024", "-g", "1024", "-N", "96"], 3, 512, {"many": 40}, None),
    ("ext2-rev0", ["-t", "ext2", "-r", "0", "-b", "1024"], 2, 1024, {}, None),
    ("ext2-htree", ["-t", "ext2", "-b", "1024"], 3, 1024, {"many": 120}, "e2fsck"),
    ("ext3-1k", ["-t", "ext3", "-b", "1024"], 3, 1024, {"big": 100000, "tri": 70 * 1024 * 1024}, None),
    ("ext2-4k-gdtcsum", ["-t", "ext2", "-b", "4096", "-O", "uninit_bg"], 4, 1024, {}, None),
    ("ext4-1k", ["-t", "ext4", "-b", "1024"], 3, 1024, {"big": 250000, "tri": 70 * 1024 * 1024}, None),
    ("ext4-4k", ["-t", "ext4", "-b", "4096"], 4, 512, {"big": 200000}, None),
    ("ext4-nocsum", ["-t", "ext4", "-b", "1024", "-O", "^metadata_csum"], 3, 1024, {}, None),
    ("ext4-no64bit", ["-t", "ext4", "-b", "1024", "-O", "^64bit"], 3, 1024, {}, None),
    ("ext4-metabg", ["-t", "ext4", "-b", "1024", "-g", "256", "-N", "160", "-O", "meta_bg,^resize_inode"], 5, 1024, {"many": 100}, None),
    ("ext4-groups", ["-t", "ext4", "-b", "1024", "-g", "1024", "-N", "96"], 3, 4096, {"many": 40}, None),
    ("ext4-csumseed", ["-t", "ext4", "-b", "1024", "-O", "metadata_csum_seed"], 3, 1024, {}, "newuuid"),
    ("ext4-htree", ["-t", "ext4", "-b", "1024"], 3, 1024, {"many": 150}, "e2fsck+fallocate"),
    # larger inputs: a file of 100 to 160 KB read whole by range, and a
    # directory of 3000 entries
    ("ext4-large", ["-t", "ext4", "-b", "1024", "-N", "3200"], 6, 1024, {"big": 160000, "wide": 3000, "sum": True}, None),
]

def build(work, rng, name, args, mib, cfg):
    root = os.path.join(work, name + ".tree")
    dirs, files, links, sparse = make_tree(rng, root, cfg)
    img = os.path.join(work, name + ".img")
    with open(img, "wb") as f:
        f.truncate(mib * 1024 * 1024)
    run("mke2fs", "-q", "-F", "-E", "root_owner=0:0", *args, "-d", root, img)
    return img, root, dirs, files, links, sparse

def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 2026
    work = sys.argv[2]
    rng = random.Random(seed)
    images = []
    built = {}
    for name, args, mib, devbs, cfg, post in CONFIGS:
        img, root, dirs, files, links, sparse = build(work, rng, name, args, mib, cfg)
        if post and "e2fsck" in post:
            subprocess.run(["e2fsck", "-fyD", img], capture_output=True)
        if post == "newuuid":
            run("tune2fs", "-U", "random", img)
        if post and "fallocate" in post:
            # an unwritten extent in the sparse file's first hole: it must
            # read as zeros
            p, islands = sparse
            rp = "/" + os.path.relpath(p, root)
            first = (islands[0][0] + len(islands[0][1]) + 1023) // 1024 + 1
            last = islands[1][0] // 1024 - 1
            assert first + 1 < last, (first, last)
            dbg(img, "fallocate %s %d %d" % (rp, first, first + 2), write=True)
            assert "[u]" in dbg(img, "stat %s" % rp), "no unwritten extent"
        assert subprocess.run(["e2fsck", "-fn", img], capture_output=True).returncode == 0, name
        im = Image(name, img, devbs)
        im.expect.append("== " + name)
        sums = [p for p in files if cfg.get("sum") and p != sparse[0] and 20000 < os.path.getsize(p) <= 1 << 20]
        inode_of = tree_queries(rng, im, img, root, dirs, files, links, sums)
        im.expect.append("end")
        images.append(im)
        built[name] = (img, root, files, inode_of)
    images += corruptions(work, rng, built)
    # one program per image: Bend 2.0.37 does not give back the memory one
    # image's reads use, so each image runs in a process of its own
    for old in os.listdir(HERE):
        if old.startswith("cases-") and old.endswith(".bend"):
            os.remove(os.path.join(HERE, old))
    for k, im in enumerate(images):
        with open(os.path.join(HERE, "cases-%02d.bend" % k), "w") as f:
            f.write("import Base\nimport ../../bytes/bytes.bend as B\nimport ../options.bend as O\nimport ./driver.bend as R\n\n")
            f.write("def main() -> IO(Unit):\n  R.Ext2Img.run(" + im.bend() + ")\n")
    lines = [l for im in images for l in im.expect]
    with open(os.path.join(HERE, "expected.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    print(len(lines), "lines,", sum(len(im.queries) + 1 for im in images), "cases,", len(images), "images")

def corruptions(work, rng, built):
    out = []
    def copy(base, name):
        src = built[base][0]
        dst = os.path.join(work, name + ".img")
        shutil.copy(src, dst)
        return dst
    def image(name, img, devbs=1024, options="O.Ext2Options.default()"):
        im = Image(name, img, devbs, options)
        im.expect.append("== " + name)
        out.append(im)
        return im
    def some_file(base):
        img, root, files, inode_of = built[base]
        cand = [p for p in sorted(files) if not os.path.islink(p) and 100 < os.path.getsize(p) < 20000]
        p = rng.choice(cand)
        rp = "/" + os.path.relpath(p, root)
        return rp, open(p, "rb").read()
    def opened(im, img):
        bs, blocks, groups, feats = fs_info(img)
        im.expect.append("open ok %d %d %d" % (bs, blocks, groups))
    # the superblock
    img = copy("ext2-1k", "bad-magic")
    patch(img, 1024 + 56, b"\0\0")
    image("bad-magic", img).expect.append("open err Ext2BadMagic")
    img = copy("ext4-1k", "bad-sb-csum")
    sb = bytearray(read(img, 1024, 1024)); sb[120] ^= 1
    patch(img, 1024, bytes(sb))
    image("bad-sb-csum", img).expect.append("open err Ext2BadSuperCsum")
    im = image("bad-sb-csum-unverified", img, 1024, opts(verify=False))
    opened(im, img)
    rp, data = some_file("ext4-1k")
    im.q("R.Ext2QCat{%s}" % bend_path(rp), "cat %s %d %d %d" % (h(rp.encode()), (len(data) + 1023) // 1024, len(data), zlib.crc32(data)))
    im.expect.append("end")
    img = copy("ext4-nocsum", "inline-data")
    dbg(img, "feature inline_data", write=True)
    image("inline-data", img).expect.append("open err Ext2Unsupported inline_data")
    img = copy("ext4-1k", "encrypt")
    dbg(img, "feature encrypt", write=True)
    image("encrypt", img).expect.append("open err Ext2Unsupported encrypt")
    img = copy("ext2-1k", "compression")
    v = struct.unpack("<I", read(img, 1024 + 96, 4))[0]
    set_sb_u32(img, 96, v | 1)
    image("compression", img).expect.append("open err Ext2Unsupported compression")
    image("ext2-only-reader", built["ext4-1k"][0], 1024, opts(incompat=2)).expect.append("open err Ext2Unsupported extent")
    img = copy("ext3-1k", "needs-recovery")
    v = struct.unpack("<I", read(img, 1024 + 96, 4))[0]
    set_sb_u32(img, 96, v | 4)
    image("needs-recovery", img).expect.append("open err Ext2NeedsRecovery")
    im = image("needs-recovery-allowed", img, 1024, opts(recovery=True))
    opened(im, img)
    im.expect.append("end")
    img = copy("ext2-4k", "bad-log-block-size")
    set_sb_u32(img, 24, 9)
    image("bad-log-block-size", img).expect.append("open err Ext2BadBlockSize")
    img = copy("ext2-1k", "bad-inode-size")
    patch(img, 1024 + 88, struct.pack("<H", 100))
    image("bad-inode-size", img).expect.append("open err Ext2BadInodeSize")
    img = copy("ext2-groups", "bad-inode-count")
    v = struct.unpack("<I", read(img, 1024, 4))[0]
    set_sb_u32(img, 0, v + 1)
    image("bad-inode-count", img).expect.append("open err Ext2BadGeometry")
    # group descriptors
    for base, name in (("ext4-1k", "bad-group-csum"), ("ext2-4k-gdtcsum", "bad-group-csum16")):
        img = copy(base, name)
        bs = fs_info(img)[0]
        gdt = (1 if bs == 1024 else 0) + 1
        b = bytearray(read(img, gdt * bs + 14, 1)); b[0] ^= 1
        patch(img, gdt * bs + 14, bytes(b))
        im = image(name, img)
        opened(im, img)
        im.q("R.Ext2QStat{%s}" % bend_path("/"), "stat %s err Ext2BadGroupCsum" % h(b"/"))
        im.expect.append("end")
    # inodes
    rp, data = some_file("ext4-1k")
    img = copy("ext4-1k", "bad-inode-csum")
    blk, off = imap(img, rp)
    b = bytearray(read(img, blk * 1024 + off + 16, 1)); b[0] ^= 1
    patch(img, blk * 1024 + off + 16, bytes(b))
    im = image("bad-inode-csum", img)
    opened(im, img)
    im.q("R.Ext2QStat{%s}" % bend_path(rp), "stat %s err Ext2BadInodeCsum" % h(rp.encode()))
    im.expect.append("end")
    im = image("bad-inode-csum-unverified", img, 1024, opts(verify=False))
    opened(im, img)
    im.q("R.Ext2QCat{%s}" % bend_path(rp), "cat %s %d %d %d" % (h(rp.encode()), (len(data) + 1023) // 1024, len(data), zlib.crc32(data)))
    im.expect.append("end")
    # extents (no metadata_csum, so the inode's own checksum does not hide them)
    for name, at, val, want in (("bad-extent-magic", 40, b"\0\0", "Ext2BadExtentMagic"), ("deep-extent", 46, struct.pack("<H", 9), "Ext2ExtentTooDeep"), ("bad-extent-max", 44, struct.pack("<H", 5), "Ext2BadExtentHeader"), ("bad-extent-start", 60, struct.pack("<I", 0x7FFFFFF0), "Ext2BadBlockRef")):
        rp, data = some_file("ext4-nocsum")
        img = copy("ext4-nocsum", name)
        blk, off = imap(img, rp)
        patch(img, blk * 1024 + off + at, val)
        im = image(name, img)
        opened(im, img)
        im.q("R.Ext2QCat{%s}" % bend_path(rp), "cat %s err %s" % (h(rp.encode()), want))
        im.expect.append("end")
    # an extent tree block's checksum
    img0, root0, files0, _ = built["ext4-1k"]
    for p in sorted(files0):
        rp = "/" + os.path.relpath(p, root0)
        st = dbg(img0, "stat %s" % rp)
        if "(ETB0):" in st:
            etb = int(st.split("(ETB0):")[1].split(",")[0].split()[0])
            img = copy("ext4-1k", "bad-extent-csum")
            patch(img, etb * 1024 + 8, b"\x5a")
            im = image("bad-extent-csum", img)
            opened(im, img)
            im.q("R.Ext2QCat{%s}" % bend_path(rp), "cat %s err Ext2BadExtentCsum" % h(rp.encode()))
            im.expect.append("end")
            break
    else:
        raise SystemExit("no extent tree block in ext4-1k")
    # block maps
    rp, data = some_file("ext2-1k")
    img = copy("ext2-1k", "bad-block-ref")
    blk, off = imap(img, rp)
    patch(img, blk * 1024 + off + 40, struct.pack("<I", 0x7FFFFFF0))
    im = image("bad-block-ref", img)
    opened(im, img)
    im.q("R.Ext2QCat{%s}" % bend_path(rp), "cat %s err Ext2BadBlockRef" % h(rp.encode()))
    im.expect.append("end")
    # directory entries
    for name, base, at, val, want in (("bad-rec-len", "ext2-1k", 4, struct.pack("<H", 13), "Ext2BadDirent"), ("rec-len-past-block", "ext2-4k", 16, struct.pack("<H", 8192), "Ext2BadDirent"), ("bad-dirent-inode", "ext2-1k", 12, struct.pack("<I", 0x7FFFFFFF), "Ext2BadDirent"), ("bad-dir-csum", "ext4-1k", 10, b"\x5a", "Ext2BadDirCsum")):
        img = copy(base, name)
        bs = fs_info(img)[0]
        b0 = bmap(img, "/", 0)
        patch(img, b0 * bs + at, val)
        im = image(name, img)
        opened(im, img)
        im.q("R.Ext2QLs{%s}" % bend_path("/"), "ls %s err %s" % (h(b"/"), want))
        im.expect.append("end")
    im = image("bad-dir-csum-unverified", os.path.join(work, "bad-dir-csum.img"), 1024, opts(verify=False))
    opened(im, im.path)
    info = dstat(built["ext4-1k"][0], "/lost+found")
    im.q("R.Ext2QStat{%s}" % bend_path("/lost+found"), "stat %s 11 dir %d %d %d" % (h(b"/lost+found"), info["size"], info["links"], info["mode"]))
    im.expect.append("end")
    return out

main()
