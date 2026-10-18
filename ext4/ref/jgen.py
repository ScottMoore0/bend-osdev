#!/usr/bin/env python3
"""The journalled-writes test for bend-osdev-ext4 (see run.sh).

  jgen.py gen SEED WORK         images and WORK/jcases.txt for jmain.bend
  jgen.py check WORK OUT        checks jmain.bend's output (OUT)

Images with a journal are made by mke2fs 1.47.0 (ext3 and ext4, 1 KiB and
4 KiB blocks, journals without checksums and with csum_v2 and csum_v3) from
random trees (mke2fs -d). Each case is a list of transactions of ext2's
operations (mkdir, create, write, append, truncate, symlink, link, unlink,
rmdir, rename), drawn at random and meant to succeed, run by the package
journalled (data=journal or data=ordered) and, for comparison, directly
(ext2's writer, no journal). The check:

  * the journalled image differs from the direct one only in the journal's
    blocks;
  * it passes e2fsck -fn, and debugfs reads back the tree a model of the
    operations (written here, from POSIX's documented behaviour) expects;
  * crashes: the last transaction of a crash case is cut after 6 numbers of
    its steps (nothing logged yet, half the log, all but the commit block,
    just committed, half the checkpoint, all but the last step). Each
    crashed image is recovered by e2fsck (-fy -E journal_only, on a copy)
    and by the package (jmain prints both the crashed and the recovered
    image); the two recoveries must agree on every block outside the
    journal (but for what e2fsck stamps from the clock in the superblock,
    and the group descriptors' summaries it recomputes from the bitmaps as
    it writes them back) and on the journal's s_start (0), and the
    package's recovered
    image must pass e2fsck -fn and hold the tree from before the
    transaction (cut before the commit: every block but the journal's and
    blocks free before the transaction is as it was) or after it (cut at or
    after the commit: every block outside the journal is the complete
    run's).
"""
import json, os, random, re, shutil, struct, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import model

ENV = dict(os.environ, PATH=os.environ.get("PATH", "") + ":/usr/sbin:/sbin")
TIME = 1700000000

def run(*args, check=False):
    r = subprocess.run(args, capture_output=True, env=ENV)
    if check and r.returncode != 0:
        raise SystemExit("failed (%d): %r\n%s" % (r.returncode, args, r.stderr.decode("latin-1")))
    return r

def lcg(n, seed):
    out = bytearray(n)
    s = seed & 0xFFFFFFFF
    for i in range(n):
        s = (s * 1103515245 + 12345) & 0xFFFFFFFF
        out[i] = (s >> 16) & 255
    return bytes(out)

# ------------------------------------------------------------- the model

class Dir:
    def __init__(self):
        self.children = {}

class File:
    def __init__(self, data=b""):
        self.data = bytearray(data)

class Link:
    def __init__(self, target):
        self.target = target

class Tree:
    def __init__(self):
        self.root = Dir()

    def lookup(self, path):
        node = self.root
        for c in [c for c in path.split(b"/") if c]:
            node = node.children[c]
        return node

    def parent(self, path):
        cs = [c for c in path.split(b"/") if c]
        return self.lookup(b"/" + b"/".join(cs[:-1])), cs[-1]

    def apply(self, op):
        k, a = op[0], op[1:]
        if k in ("m", "c", "s"):
            d, n = self.parent(a[0])
            assert n not in d.children
            d.children[n] = Dir() if k == "m" else File() if k == "c" else Link(a[1])
        elif k == "l":
            d, n = self.parent(a[1])
            d.children[n] = self.lookup(a[0])
        elif k in ("u", "r"):
            d, n = self.parent(a[0])
            del d.children[n]
        elif k == "n":
            d, n = self.parent(a[0])
            node = d.children.pop(n)
            d2, n2 = self.parent(a[1])
            d2.children[n2] = node
        elif k == "w":
            f, off, data = self.lookup(a[0]), a[1], lcg(a[2], a[3])
            if len(f.data) < off:
                f.data += bytes(off - len(f.data))
            f.data[off:off + len(data)] = data
        elif k == "a":
            f = self.lookup(a[0])
            f.data += lcg(a[1], a[2])
        elif k == "t":
            f, size = self.lookup(a[0]), a[1]
            if size < len(f.data):
                del f.data[size:]
            else:
                f.data += bytes(size - len(f.data))

    def snapshot(self):
        """path -> kind and contents, and the groups of paths sharing a file"""
        out, ids = {}, {}
        def walk(d, path):
            for n, c in sorted(d.children.items()):
                p = path + b"/" + n
                if isinstance(c, Dir):
                    out[p] = ("d",)
                    walk(c, p)
                elif isinstance(c, File):
                    out[p] = ("f", bytes(c.data))
                    ids.setdefault(id(c), []).append(p)
                else:
                    out[p] = ("l", c.target)
        walk(self.root, b"")
        return out, sorted(sorted(g) for g in ids.values() if len(g) > 1)

    def paths(self, kind):
        res = []
        def walk(d, path):
            for n, c in d.children.items():
                p = path + b"/" + n
                if isinstance(c, kind):
                    res.append(p)
                if isinstance(c, Dir) and n != b"lost+found":
                    walk(c, p)
        if kind is Dir:
            res.append(b"")
        walk(self.root, b"")
        return res

def copy_tree(t):
    """a deep copy that keeps hard links shared"""
    memo = {}
    def cp(n):
        if id(n) in memo:
            return memo[id(n)]
        if isinstance(n, Dir):
            m = Dir()
            memo[id(n)] = m
            m.children = {k: cp(v) for k, v in n.children.items()}
        elif isinstance(n, File):
            m = File(n.data)
            memo[id(n)] = m
        else:
            m = Link(n.target)
            memo[id(n)] = m
        return m
    out = Tree()
    out.root = cp(t.root)
    return out

# ---------------------------------------------------------------- images

def build_src(rng, host, tree):
    """a random tree on the host for mke2fs -d, and in the model"""
    tree.root.children[b"lost+found"] = Dir()
    dirs = [(host, tree.root)]
    for k in range(rng.randrange(2, 5)):
        hp, d = rng.choice(dirs)
        name = b"d%d" % k
        os.mkdir(os.path.join(hp, name.decode()))
        nd = Dir()
        d.children[name] = nd
        dirs.append((os.path.join(hp, name.decode()), nd))
    for k in range(rng.randrange(3, 8)):
        hp, d = rng.choice(dirs)
        name = b"f%d" % k
        data = lcg(rng.choice([0, 10, 1000, 5000, 20000]), rng.randrange(1 << 30))
        with open(os.path.join(hp, name.decode()), "wb") as f:
            f.write(data)
        d.children[name] = File(data)

def nonzero(img, bs):
    data = open(img, "rb").read()
    return [i for i in range(len(data) // bs) if any(data[i * bs:(i + 1) * bs])], len(data) // bs

def get_block(path, bs, n):
    with open(path, "rb") as f:
        f.seek(n * bs)
        return f.read(bs)

def put_block(path, bs, n, data):
    with open(path, "r+b") as f:
        f.seek(n * bs)
        f.write(data)

def jblocks(img):
    return [int(x) for x in run("debugfs", "-R", "blocks <8>", img).stdout.split()]

def set_journal_csum(img, bs, v):
    """the journal superblock given csum_v2 or csum_v3 (crc32c), resealed"""
    jb = jblocks(img)
    raw = bytearray(get_block(img, bs, jb[0]))
    inc = struct.unpack_from(">I", raw, 0x28)[0] & ~0x18
    struct.pack_into(">I", raw, 0x28, inc | (16 if v == 3 else 8))
    raw[0x50] = 4
    put_block(img, bs, jb[0], model.jsb_with(bytes(raw), 0, struct.unpack_from(">I", raw, 0x18)[0]))

def make_image(work, rng, name, args, blocks, bs, csum):
    host = os.path.join(work, name + ".src")
    os.mkdir(host)
    tree = Tree()
    build_src(rng, host, tree)
    img = os.path.join(work, name + ".img")
    run("mke2fs", "-q", "-F", "-b", str(bs), "-d", host, "-E", "lazy_itable_init=0", *args, img, str(blocks), check=True)
    if csum:
        set_journal_csum(img, bs, csum)
    r = run("e2fsck", "-fn", img)
    if r.returncode != 0:
        raise SystemExit("%s: e2fsck rejects the image mke2fs made" % name)
    return img, tree

# ----------------------------------------------------------- operations

def hx(b):
    return b.hex() if b else "-"

def op_line(op):
    k, a = op[0], op[1:]
    if k in ("m", "c"):
        return "%s %s %d" % (k, hx(a[0]), a[1])
    if k in ("s", "l", "n"):
        return "%s %s %s" % (k, hx(a[0]), hx(a[1]))
    if k in ("u", "r"):
        return "%s %s" % (k, hx(a[0]))
    if k == "w":
        return "w %s %d %d %d" % (hx(a[0]), a[1], a[2], a[3])
    if k == "a":
        return "a %s %d %d" % (hx(a[0]), a[1], a[2])
    if k == "t":
        return "t %s %d" % (hx(a[0]), a[1])
    raise ValueError(k)

class Names:
    def __init__(self):
        self.n = 0
    def new(self, rng):
        self.n += 1
        return b"%s%d" % (rng.choice([b"n", b"name_", b"a_longer_file_name_"]), self.n)

def random_op(rng, tree, names, big):
    """one operation meant to succeed, applied to the model"""
    while True:
        k = "w" if big else rng.choice("mmccwwwaatslunr")
        dirs = tree.paths(Dir)
        files = tree.paths(File)
        links = tree.paths(Link)
        if k == "m":
            op = ("m", rng.choice(dirs) + b"/" + names.new(rng), 493)
        elif k == "c":
            op = ("c", rng.choice(dirs) + b"/" + names.new(rng), 420)
        elif k == "s":
            tgt = rng.choice([b"short", b"/" + b"x" * rng.randrange(60, 200)])
            op = ("s", rng.choice(dirs) + b"/" + names.new(rng), tgt)
        elif k in "wat" and files:
            f = rng.choice(files)
            size = len(tree.lookup(f).data)
            if k == "w":
                n = big if big else rng.choice([1, 100, 3000, 9000])
                op = ("w", f, 0 if big else rng.randrange(0, size + 5000), n, rng.randrange(1 << 30))
            elif k == "a":
                op = ("a", f, rng.choice([1, 500, 5000]), rng.randrange(1 << 30))
            else:
                op = ("t", f, rng.choice([0, size // 2, size + 3000]))
        elif k == "l" and files:
            op = ("l", rng.choice(files), rng.choice(dirs) + b"/" + names.new(rng))
        elif k == "u" and (files or links):
            op = ("u", rng.choice(files + links))
        elif k == "r":
            empty = [d for d in dirs[1:] if not tree.lookup(d).children and not d.endswith(b"lost+found")]
            if not empty:
                continue
            op = ("r", rng.choice(empty))
        elif k == "n" and (files or links):
            op = ("n", rng.choice(files + links), rng.choice(dirs) + b"/" + names.new(rng))
        else:
            continue
        tree.apply(op)
        return op

# ----------------------------------------------------------------- gen

# name, mke2fs arguments, blocks, block size, journal checksum, mode,
# crash, transactions (each a number of operations), a big write's size
CASES = [
    ("ext3-1k-journal", ["-t", "ext3"], 8192, 1024, 0, "j", True, [8], 0),
    ("ext3-1k-ordered", ["-t", "ext3"], 8192, 1024, 0, "o", True, [8], 0),
    ("ext4-4k-journal-v3", ["-t", "ext4"], 8192, 4096, 3, "j", True, [8], 0),
    ("ext4-4k-ordered-v3", ["-t", "ext4"], 8192, 4096, 3, "o", True, [8], 0),
    ("ext4-1k-ordered-v2", ["-t", "ext4", "-O", "^64bit"], 16384, 1024, 2, "o", True, [6], 0),
    ("ext4-1k-journal-v3-big", ["-t", "ext4"], 16384, 1024, 3, "j", True, [3], 200000),
    ("ext3-4k-multi", ["-t", "ext3"], 4096, 4096, 0, "j", False, [3, 4, 2, 5], 0),
    ("ext4-1k-multi-ordered", ["-t", "ext4"], 16384, 1024, 3, "o", False, [4, 3, 4], 0),
    ("ext3-1k-full-journal", ["-t", "ext3", "-J", "size=1"], 8192, 1024, 0, "j", False, [1], 1200000),
    ("ext3-1k-full-ordered", ["-t", "ext3", "-J", "size=1"], 8192, 1024, 0, "o", True, [1], 1200000),
]

def gen(seed, work):
    rng = random.Random(seed)
    lines, plan = [], []
    for name, args, blocks, bs, csum, mode, crash, txs, big in CASES:
        img, tree = make_image(work, rng, name, args, blocks, bs, csum)
        nz, count = nonzero(img, bs)
        lines += ["C " + name, "F %s %d %d" % (img, bs, count)]
        for k in range(0, len(nz), 200):
            lines.append("Z " + " ".join(map(str, nz[k:k + 200])))
        lines.append("M %s %d %d" % (mode, 1 if crash else 0, TIME))
        names = Names()
        snaps = [tree.snapshot()]
        full = name.endswith("full-journal")
        for n in txs:
            lines.append("T")
            before = copy_tree(tree)
            for i in range(n):
                op = random_op(rng, tree, names, big if i == 0 and big else 0)
                if big and i == 0 and op[0] != "w":
                    raise SystemExit("the big write was not drawn")
                lines.append(op_line(op))
            if full:
                tree = before
            snaps.append(tree.snapshot())
        lines.append("E")
        plan.append({"name": name, "img": img, "bs": bs, "count": count, "mode": mode, "crash": crash,
                     "txs": len(txs), "full": full,
                     "snaps": [(enc(s), [[hx(p) for p in g] for g in gs]) for s, gs in snaps]})
    with open(os.path.join(work, "jcases.txt"), "w") as f:
        f.write("\n".join(lines) + "\n")
    with open(os.path.join(work, "jplan.json"), "w") as f:
        json.dump(plan, f)
    print("%d cases, %d transactions" % (len(plan), sum(len(c[7]) for c in CASES)))

def enc(snap):
    return {hx(p): [v[0]] + ([v[1].hex()] if len(v) > 1 else []) for p, v in snap.items()}

# --------------------------------------------------------------- check

def image_tree(img, work):
    """the tree debugfs reads from an image (rdump for contents, ls -p for
    kinds and inode numbers)"""
    out = img + ".rdump"
    shutil.rmtree(out, ignore_errors=True)
    os.makedirs(out)
    run("debugfs", "-R", "rdump / " + out, img)
    snap, inodes = {}, {}
    def walk(path, host):
        r = run("debugfs", "-R", "ls -p " + (path.decode("latin-1") or "/"), img).stdout.decode("latin-1")
        for line in r.splitlines():
            parts = line.split("/")
            if len(parts) < 7:
                continue
            ino, mode, name = int(parts[1]), int(parts[2], 8), parts[5].encode("latin-1")
            if name in (b".", b"..", b"") or ino == 0:
                continue
            p = path + b"/" + name
            hp = os.path.join(host, name.decode("latin-1"))
            if mode & 0o170000 == 0o040000:
                snap[hx(p)] = ["d"]
                walk(p, hp)
            elif mode & 0o170000 == 0o120000:
                snap[hx(p)] = ["l", os.readlink(hp).encode("latin-1").hex()]
            else:
                snap[hx(p)] = ["f", open(hp, "rb").read().hex()]
                inodes.setdefault(ino, []).append(hx(p))
    walk(b"", out)
    return snap, sorted(sorted(g) for g in inodes.values() if len(g) > 1)

def free_blocks(img):
    """the blocks free in an image's bitmaps (dumpe2fs)"""
    out = run("dumpe2fs", img).stdout.decode("latin-1")
    free = set()
    for m in re.finditer(r"^\s+Free blocks: (.*)$", out, re.M):
        for part in m.group(1).split(","):
            part = part.strip()
            if not part:
                continue
            a, _, b = part.partition("-")
            free.update(range(int(a), int(b or a) + 1))
    return free

def rebuild(src, dst, blocks, bs):
    shutil.copyfile(src, dst)
    for n, d in blocks.items():
        put_block(dst, bs, n, d)

def blocks_of(lines):
    out = {}
    for l in lines:
        _, n, h = l.split(" ", 2)
        out[int(n)] = bytes.fromhex(h)
    return out

def differing(a, b, bs, count):
    fa, fb = open(a, "rb").read(), open(b, "rb").read()
    return [n for n in range(count) if fa[n * bs:(n + 1) * bs] != fb[n * bs:(n + 1) * bs]]

# the superblock fields e2fsck stamps from the clock when it replays a
# journal (s_wtime, s_lastcheck, s_kbytes_written), and the checksum over
# them: masked when two recoveries are compared
STAMPED = [(0x30, 4), (0x40, 4), (0x178, 8), (0x3FC, 4)]

def masked_super(path, bs):
    n, off = (1, 0) if bs == 1024 else (0, 1024)
    blk = bytearray(get_block(path, bs, n))
    for o, k in STAMPED:
        blk[off + o:off + o + k] = bytes(k)
    return bytes(blk)

# the group descriptor summaries e2fsck recomputes from the bitmaps when it
# writes the descriptors back after a replay (bg_flags' INODE_UNINIT,
# bg_itable_unused, and the checksum over them): a transaction that frees
# every inode it took in a group leaves the descriptor as the writer left
# it, which e2fsck then rewrites as an untouched group's
def gdt_blocks(path, bs):
    sb = get_block(path, bs, 1 if bs == 1024 else 0)[0 if bs == 1024 else 1024:][:1024]
    first, = struct.unpack_from("<I", sb, 20)
    count, = struct.unpack_from("<I", sb, 4)
    bpg, = struct.unpack_from("<I", sb, 32)
    wide = struct.unpack_from("<I", sb, 0x60)[0] & 0x80
    dsz = struct.unpack_from("<H", sb, 0xFE)[0] if wide else 32
    groups = -(-(count - first) // bpg)
    return list(range(first + 1, first + 1 + -(-groups * dsz // bs))), dsz

def masked_descs(path, bs):
    bl, dsz = gdt_blocks(path, bs)
    out = []
    for b in bl:
        blk = bytearray(get_block(path, bs, b))
        for o in range(0, bs, dsz):
            blk[o + 18] &= 0xFE
            blk[o + 28:o + 32] = bytes(4)
            if dsz >= 64:
                blk[o + 0x32:o + 0x34] = bytes(2)
        out.append(bytes(blk))
    return bl, out

def check(work, outfile):
    plan = json.load(open(os.path.join(work, "jplan.json")))
    text = open(outfile, encoding="latin-1").read().splitlines()
    sections, cur = {}, None
    for line in text:
        if line.startswith("case "):
            cur = line[5:]
            sections[cur] = []
        elif cur is not None:
            sections[cur].append(line)
    bad, ntx, ncut, nfsck = [], 0, 0, 0
    for c in plan:
        name, img, bs, count = c["name"], c["img"], c["bs"], c["count"]
        def fail(msg):
            bad.append("%s: %s" % (name, msg))
        lines = sections.get(name)
        if lines is None or not lines or lines[-1] != "done":
            fail("no complete output")
            continue
        jb = set(jblocks(img))
        # outcomes
        txl = [l for l in lines if l.startswith("tx ")]
        dl = [l for l in lines if l.startswith("direct ")]
        want = "err Ext4JournalFull" if c["full"] else "ok"
        if len(txl) != c["txs"] or any(" ".join(l.split()[2:4]) != want and l.split()[2] != want for l in txl):
            fail("transactions: %s (want %s)" % (txl, want))
            continue
        if any(l.split()[2] != "ok" for l in dl):
            fail("direct: %s" % dl)
            continue
        ntx += len(txl)
        # journalled against direct
        diff = [int(x) for x in [l for l in lines if l.startswith("differ")][0].split()[1:]]
        outside = [n for n in diff if n not in jb]
        if not c["full"] and outside:
            fail("journalled and direct images differ outside the journal: %s" % outside[:10])
        # the final image
        i = lines.index("final")
        final = img + ".final"
        rebuild(img, final, blocks_of(lines[i + 1:-1]), bs)
        r = run("e2fsck", "-fn", final)
        nfsck += 1
        if r.returncode != 0:
            fail("e2fsck -fn rejects the final image:\n" + r.stdout.decode("latin-1")[-1500:])
            continue
        want_snap = c["snaps"][-1]
        if list(image_tree(final, work)) != [want_snap[0], want_snap[1]]:
            fail("the final image's tree is not the model's")
        if not c["crash"]:
            continue
        # crashes of the last transaction
        before, after = c["snaps"][-2], c["snaps"][-1]
        free = free_blocks(img)
        k = 0
        while k < len(lines):
            l = lines[k]
            if not l.startswith("cut "):
                k += 1
                continue
            parts = l.split()
            if parts[2] == "err":
                fail(l)
                break
            n, at = int(parts[1]), int(parts[2])
            j = k + 1
            while lines[j].startswith("blk "):
                j += 1
            crashed = img + ".cut%d" % n
            rebuild(img, crashed, blocks_of(lines[k + 1:j]), bs)
            if not lines[j].startswith("rec %d ok" % n):
                fail("recovery after %d steps: %s" % (n, lines[j]))
                break
            m = j + 1
            while m < len(lines) and lines[m].startswith("blk "):
                m += 1
            ours = img + ".rec%d" % n
            rebuild(img, ours, blocks_of(lines[j + 1:m]), bs)
            k = m
            ncut += 1
            theirs = img + ".fsck%d" % n
            shutil.copyfile(crashed, theirs)
            run("e2fsck", "-fy", "-E", "journal_only", theirs)
            sbn = 1 if bs == 1024 else 0
            gdt, mo = masked_descs(ours, bs)
            d = [b for b in differing(ours, theirs, bs, count) if b not in jb and b != sbn and b not in gdt]
            if masked_super(ours, bs) != masked_super(theirs, bs):
                d.append(sbn)
            if mo != masked_descs(theirs, bs)[1]:
                d += gdt
            if d:
                fail("after %d steps: the package's recovery and e2fsck's differ at blocks %s" % (n, d[:10]))
            j0 = sorted(jb)[0]
            for path in (ours, theirs):
                if struct.unpack_from(">I", get_block(path, bs, j0), 28)[0] != 0:
                    fail("after %d steps: %s's journal is not empty" % (n, path))
            r = run("e2fsck", "-fn", ours)
            nfsck += 1
            if r.returncode != 0:
                fail("after %d steps: e2fsck -fn rejects the recovered image:\n%s" % (n, r.stdout.decode("latin-1")[-1500:]))
                continue
            snap = after if n >= at else before
            if list(image_tree(ours, work)) != [snap[0], snap[1]]:
                fail("after %d steps (commit at %d): the recovered tree is not the one %s the transaction" % (n, at, "after" if n >= at else "before"))
            if n >= at:
                d = [b for b in differing(ours, final, bs, count) if b not in jb]
                if d:
                    fail("after %d steps: the recovered image differs from the complete run at %s" % (n, d[:10]))
            else:
                d = [b for b in differing(ours, img, bs, count) if b not in jb and b not in free]
                if d:
                    fail("after %d steps: the recovered image differs from the old one at %s" % (n, d[:10]))
    if bad:
        print("\n".join(bad[:20]))
        sys.exit(1)
    print("%d cases, %d transactions, %d crashes recovered as e2fsck does, %d e2fsck -fn" % (len(plan), ntx, ncut, nfsck))

if __name__ == "__main__":
    if sys.argv[1] == "gen":
        gen(int(sys.argv[2]), sys.argv[3])
    else:
        check(sys.argv[2], sys.argv[3])
