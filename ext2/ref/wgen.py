#!/usr/bin/env python3
"""Differential test of the writer (bend-osdev-ext2's ops, run, mkfs).

  wgen.py gen SEED WORK     build the images and write WORK/cases.txt
  wgen.py check WORK OUT    check the program's output OUT against the model

gen builds images in WORK with mke2fs (ext2, ext3, ext4 in several shapes,
each populated from a small tree with mke2fs -d), and lists cases made on a
blank device by the package's own mkfs; for each image it draws a random
sequence of operations (create, mkdir, symlink, link, unlink, rmdir,
rename, write, append, truncate; about a third of them meant to be
refused) and runs them through a model of the filesystem written here from
POSIX's and ext2's documented behaviour (so it shares an author with the
package, but not its code), recording what each operation should answer
and the tree it should leave. A few cases run with the whole-filesystem
check after every operation, with another allocation policy, with
checksums refused, or on an image corrupted after the fact (where the
package's fsck must find the corruption).

check compares, for every case: each operation's outcome with the model's;
the tree the package reads back (kinds, sizes, link counts, CRC-32 of the
contents, link targets) with the model's; the image itself, rebuilt from
the output, with e2fsck -fn (which must accept it) and with debugfs (ls -p:
names, kinds, sizes, and which names share an inode; rdump: contents and
link targets).
"""
import json, os, random, shutil, string, struct, subprocess, sys, zlib

HERE = os.path.dirname(os.path.abspath(__file__))
PATH_ENV = dict(os.environ, PATH=os.environ.get("PATH", "") + ":/usr/sbin:/sbin")

def run(*args, **kw):
    return subprocess.run(args, capture_output=True, env=PATH_ENV, **kw)

def lcg(n, seed):
    out = bytearray(n)
    s = seed & 0xFFFFFFFF
    for i in range(n):
        s = (s * 1103515245 + 12345) & 0xFFFFFFFF
        out[i] = (s >> 16) & 255
    return bytes(out)

# ---------------------------------------------------------------- the model

class Refused(Exception):
    def __init__(self, kind):
        Exception.__init__(self, kind)
        self.kind = kind

class Dir:
    def __init__(self, parent=None):
        self.children = {}
        self.parent = parent if parent is not None else self
        self.indexed = False

class File:
    def __init__(self, data=b""):
        self.data = bytearray(data)
        self.unwritten = set()

class Link:
    def __init__(self, target):
        self.target = target

class Model:
    def __init__(self, bs):
        self.root = Dir()
        self.root.children[b"lost+found"] = Dir(self.root)
        self.bs = bs
        self.csum_refused = False

    # paths
    def comps(self, path):
        return [c for c in path.split(b"/") if c]

    def resolve(self, path):
        cur = self.root
        cs = self.comps(path)
        for i, c in enumerate(cs):
            if not isinstance(cur, Dir):
                raise Refused("Ext2NotDir")
            if c == b".":
                nxt = cur
            elif c == b"..":
                nxt = cur.parent
            else:
                nxt = cur.children.get(c)
            if nxt is None:
                raise Refused("Ext2NotFound")
            if isinstance(nxt, Link) and i < len(cs) - 1:
                raise Refused("Ext2SymlinkInPath")
            cur = nxt
        return cur

    def split(self, path):
        cs = self.comps(path)
        if not cs:
            raise Refused("Ext2BadName")
        return b"/" + b"/".join(cs[:-1]), cs[-1]

    def check_name(self, name):
        if len(name) == 0 or len(name) > 255 or b"\0" in name or name in (b".", b".."):
            raise Refused("Ext2BadName")

    def dir_at(self, path):
        d = self.resolve(path)
        if not isinstance(d, Dir):
            raise Refused("Ext2NotDir")
        return d

    def place(self, path):
        parent, name = self.split(path)
        self.check_name(name)
        p = self.dir_at(parent)
        if name in p.children:
            raise Refused("Ext2Exists")
        return p, name

    def target(self, path):
        parent, name = self.split(path)
        self.check_name(name)
        p = self.dir_at(parent)
        c = p.children.get(name)
        if c is None:
            raise Refused("Ext2NotFound")
        return p, name, c

    def editable(self, d):
        if d.indexed:
            raise Refused("Ext2HtreeDir")

    def writable(self):
        if self.csum_refused:
            raise Refused("Ext2CannotWrite")

    def regular(self, path):
        n = self.resolve(path)
        if isinstance(n, Dir):
            raise Refused("Ext2IsDir")
        if not isinstance(n, File):
            raise Refused("Ext2CannotWrite")
        return n

    # operations: each raises Refused, or changes the model
    def create(self, path, mode):
        self.writable()
        p, name = self.place(path)
        self.editable(p)
        p.children[name] = File()

    def mkdir(self, path, mode):
        self.writable()
        p, name = self.place(path)
        self.editable(p)
        p.children[name] = Dir(p)

    def symlink(self, path, target):
        self.writable()
        if len(target) == 0 or len(target) >= self.bs:
            raise Refused("Ext2BadName")
        p, name = self.place(path)
        self.editable(p)
        p.children[name] = Link(target)

    def link(self, target, path):
        self.writable()
        t = self.resolve(target)
        if isinstance(t, Dir):
            raise Refused("Ext2IsDir")
        p, name = self.place(path)
        self.editable(p)
        p.children[name] = t

    def unlink(self, path):
        self.writable()
        p, name, c = self.target(path)
        if isinstance(c, Dir):
            raise Refused("Ext2IsDir")
        self.editable(p)
        del p.children[name]

    def rmdir(self, path):
        self.writable()
        p, name, c = self.target(path)
        if not isinstance(c, Dir):
            raise Refused("Ext2NotDir")
        if c.children:
            raise Refused("Ext2NotEmpty")
        self.editable(p)
        del p.children[name]

    def below(self, d, s):
        # whether directory d is s or lies below it
        cur = d
        for _ in range(10000):
            if cur is s:
                return True
            if cur is self.root:
                return False
            cur = cur.parent
        return True

    def rename(self, src, dst):
        self.writable()
        sp, sname, s = self.target(src)
        dparent, dname = self.split(dst)
        self.check_name(dname)
        dp = self.dir_at(dparent)
        t = dp.children.get(dname)
        if t is s:
            return
        if t is not None:
            if isinstance(s, Dir):
                if not isinstance(t, Dir):
                    raise Refused("Ext2NotDir")
                if t.children:
                    raise Refused("Ext2NotEmpty")
            elif isinstance(t, Dir):
                raise Refused("Ext2IsDir")
        if isinstance(s, Dir) and self.below(dp, s):
            raise Refused("Ext2RenameLoop")
        self.editable(dp)
        self.editable(sp)
        del sp.children[sname]
        dp.children[dname] = s
        if isinstance(s, Dir):
            s.parent = dp

    def write(self, path, off, data):
        self.writable()
        f = self.regular(path)
        self.put(f, off, data)

    def put(self, f, off, data):
        if data:
            first, last = off // self.bs, (off + len(data) - 1) // self.bs
            if any(first <= b <= last for b in f.unwritten):
                raise Refused("Ext2Unwritten")
            if len(f.data) < off:
                f.data.extend(b"\0" * (off - len(f.data)))
            f.data[off:off + len(data)] = data

    def append(self, path, data):
        self.writable()
        f = self.regular(path)
        self.put(f, len(f.data), data)

    def truncate(self, path, size):
        self.writable()
        f = self.regular(path)
        if size < len(f.data):
            del f.data[size:]
            keep = (size + self.bs - 1) // self.bs
            f.unwritten = set(b for b in f.unwritten if b < keep)
        else:
            f.data.extend(b"\0" * (size - len(f.data)))

    # the tree: path -> (kind, size, links, crc or None, target or None), and
    # which paths name the same file
    def listing(self):
        refs = {}
        def walk(d, path):
            for name, n in d.children.items():
                refs.setdefault(id(n), []).append(path + b"/" + name)
                if isinstance(n, Dir):
                    walk(n, path + b"/" + name)
        walk(self.root, b"")
        out = {}
        def walk2(d, path):
            for name, n in d.children.items():
                p = path + b"/" + name
                if isinstance(n, Dir):
                    subdirs = sum(1 for c in n.children.values() if isinstance(c, Dir))
                    out[p] = ("dir", None, 2 + subdirs, None, None)
                    walk2(n, p)
                elif isinstance(n, File):
                    crc = zlib.crc32(bytes(n.data)) if len(n.data) < (1 << 20) else "big"
                    out[p] = ("file", len(n.data), len(refs[id(n)]), crc, None)
                else:
                    out[p] = ("symlink", len(n.target), len(refs[id(n)]), None, n.target.hex())
        walk2(self.root, b"")
        groups = [sorted(v) for v in refs.values() if len(v) > 1]
        return out, groups

    def stored(self):
        """the bytes the model's files hold (for keeping clear of a full
        filesystem)"""
        seen, total = set(), 0
        def walk(d):
            nonlocal total
            for n in d.children.values():
                if id(n) in seen:
                    continue
                seen.add(id(n))
                if isinstance(n, Dir):
                    total += self.bs
                    walk(n)
                elif isinstance(n, File):
                    total += len(n.data)
                else:
                    total += len(n.target)
        walk(self.root)
        return total

    def paths(self):
        out = []
        def walk(d, path):
            for name, n in d.children.items():
                p = path + b"/" + name
                out.append((p, n))
                if isinstance(n, Dir):
                    walk(n, p)
        walk(self.root, b"")
        return out

# ---------------------------------------------------------------- trees and images

NAMECH = string.ascii_letters + string.digits + "._-"

def rname(rng, lo=1, hi=12):
    while True:
        n = "".join(rng.choice(NAMECH) for _ in range(rng.randint(lo, hi)))
        if n not in (".", "..", "lost+found"):
            return n.encode()

def build_tree(rng, root, model, cfg):
    """a small host tree for mke2fs -d, mirrored into the model"""
    os.makedirs(root)
    dirs = [(root, model.root)]
    for _ in range(rng.randint(2, 4)):
        hp, md = rng.choice(dirs)
        name = rname(rng)
        if name in md.children:
            continue
        os.mkdir(os.path.join(hp, name.decode()))
        nd = Dir(md)
        md.children[name] = nd
        dirs.append((os.path.join(hp, name.decode()), nd))
    files = []
    for _ in range(rng.randint(3, 7)):
        hp, md = rng.choice(dirs)
        name = rname(rng)
        if name in md.children:
            continue
        n = rng.choice([0, rng.randint(1, 50), rng.randint(100, 3000), rng.randint(5000, 20000)])
        data = lcg(n, rng.randrange(1 << 30))
        open(os.path.join(hp, name.decode()), "wb").write(data)
        f = File(data)
        md.children[name] = f
        files.append((os.path.join(hp, name.decode()), f))
    if files:
        src, f = rng.choice(files)
        hp, md = rng.choice(dirs)
        name = rname(rng)
        if name not in md.children:
            os.link(src, os.path.join(hp, name.decode()))
            md.children[name] = f
    for _ in range(rng.randint(1, 3)):
        hp, md = rng.choice(dirs)
        name = rname(rng)
        if name in md.children:
            continue
        t = rname(rng, 1, 120) if rng.random() < 0.5 else b"x" * rng.randint(60, 90)
        os.symlink(t.decode(), os.path.join(hp, name.decode()))
        md.children[name] = Link(t)
    if cfg.get("many"):
        hp, md = dirs[0]
        name = b"many"
        os.mkdir(os.path.join(hp, "many"))
        nd = Dir(md)
        md.children[name] = nd
        for i in range(cfg["many"]):
            fn = ("entry-%04d-" % i + "y" * 30).encode()
            open(os.path.join(hp, "many", fn.decode()), "wb").write(b"%d" % i)
            nd.children[fn] = File(b"%d" % i)

# ---------------------------------------------------------------- operations

def hx(b):
    return b.hex()

class Op:
    def __init__(self, kind, args, bend):
        self.kind, self.args, self.bend = kind, args, bend

def hp(p):
    return hx(p) if p else "-"

def make_op(kind, *args):
    a = args
    if kind == "create":
        line = "c %s %d" % (hp(a[0]), a[1])
    elif kind == "mkdir":
        line = "m %s %d" % (hp(a[0]), a[1])
    elif kind == "symlink":
        line = "s %s %s" % (hp(a[0]), hp(a[1]))
    elif kind == "link":
        line = "l %s %s" % (hp(a[0]), hp(a[1]))
    elif kind == "unlink":
        line = "u %s" % hp(a[0])
    elif kind == "rmdir":
        line = "r %s" % hp(a[0])
    elif kind == "rename":
        line = "n %s %s" % (hp(a[0]), hp(a[1]))
    elif kind == "write":
        line = "w %s %d %d %d" % (hp(a[0]), a[1], a[2], a[3])
    elif kind == "append":
        line = "a %s %d %d" % (hp(a[0]), a[1], a[2])
    elif kind == "truncate":
        line = "t %s %d" % (hp(a[0]), a[1])
    elif kind == "fsck":
        line = "f"
    else:
        raise ValueError(kind)
    return Op(kind, args, line)

def apply(model, op):
    """the outcome the model expects: 'ok' or the error kind"""
    k, a = op.kind, op.args
    try:
        if k == "create":
            model.create(a[0], a[1])
        elif k == "mkdir":
            model.mkdir(a[0], a[1])
        elif k == "symlink":
            model.symlink(a[0], a[1])
        elif k == "link":
            model.link(a[0], a[1])
        elif k == "unlink":
            model.unlink(a[0])
        elif k == "rmdir":
            model.rmdir(a[0])
        elif k == "rename":
            model.rename(a[0], a[1])
        elif k == "write":
            model.write(a[0], a[1], lcg(a[2], a[3]))
        elif k == "append":
            model.append(a[0], lcg(a[1], a[2]))
        elif k == "truncate":
            model.truncate(a[0], a[1])
        elif k == "fsck":
            return "fsck ok"
        return "ok"
    except Refused as e:
        return "err " + e.kind

def random_ops(rng, model, n, budget, cfg):
    ops = []
    bs = model.bs
    big = cfg.get("big", 30000)
    for _ in range(n):
        ps = model.paths()
        dirs = [b"/"] + [p for p, x in ps if isinstance(x, Dir)]
        files = [p for p, x in ps if isinstance(x, File)]
        anyp = [p for p, x in ps]
        def newpath():
            d = rng.choice(dirs)
            return d.rstrip(b"/") + b"/" + rname(rng)
        def somepath():
            r = rng.random()
            if r < 0.7 and anyp:
                return rng.choice(anyp)
            if r < 0.85:
                return newpath()
            return rng.choice([b"/", b"/no/such/dir/x", (rng.choice(files) + b"/x") if files else b"/zz", b"/" + b"n" * 256, b"/.", b"/lost+found/.."])
        full = model.stored() > budget
        r = rng.random()
        if r < 0.12:
            op = make_op("create", newpath() if rng.random() < 0.85 else somepath(), rng.choice([0o644, 0o600, 0o755]))
        elif r < 0.2:
            op = make_op("mkdir", newpath() if rng.random() < 0.85 else somepath(), 0o755)
        elif r < 0.26:
            t = rname(rng, 1, 50) if rng.random() < 0.6 else (b"t" * rng.randint(60, bs + 5))
            op = make_op("symlink", newpath() if rng.random() < 0.85 else somepath(), t)
        elif r < 0.32:
            op = make_op("link", rng.choice(files) if files and rng.random() < 0.8 else somepath(), newpath() if rng.random() < 0.85 else somepath())
        elif r < 0.4:
            op = make_op("unlink", rng.choice(files) if files and rng.random() < 0.7 else somepath())
        elif r < 0.46:
            ed = [p for p, x in ps if isinstance(x, Dir) and not x.children]
            op = make_op("rmdir", rng.choice(ed) if ed and rng.random() < 0.6 else somepath())
        elif r < 0.56:
            src = somepath()
            dst = newpath() if rng.random() < 0.6 else somepath()
            op = make_op("rename", src, dst)
        elif r < 0.74 and not full:
            p = rng.choice(files) if files and rng.random() < 0.85 else somepath()
            size = len(model.resolve(p).data) if p in files else 0
            off = rng.choice([0, size, rng.randint(0, size + 1), rng.randint(0, 3 * bs), size + rng.randint(0, 4 * bs)])
            if rng.random() < cfg.get("far", 0.0):
                off = rng.randint(270 * 1024, 400 * 1024)
            n = rng.choice([1, rng.randint(1, 200), rng.randint(1, 3 * bs), rng.randint(1, big)])
            op = make_op("write", p, off, n, rng.randrange(1 << 30))
        elif r < 0.84 and not full:
            p = rng.choice(files) if files and rng.random() < 0.85 else somepath()
            op = make_op("append", p, rng.choice([1, rng.randint(1, 3 * bs), rng.randint(1, big)]), rng.randrange(1 << 30))
        elif r < 0.95:
            p = rng.choice(files) if files and rng.random() < 0.85 else somepath()
            size = len(model.resolve(p).data) if p in files else 0
            op = make_op("truncate", p, rng.choice([0, size // 2, max(0, size - rng.randint(0, 2 * bs)), size + rng.randint(0, 3 * bs)]))
        else:
            fl = [p for p, x in ps if isinstance(x, File) and x.data]
            if len(fl) >= 2:
                a, b = rng.sample(fl, 2)
                op = make_op("rename", a, b)
            else:
                op = make_op("create", newpath(), 0o644)
        ops.append((op, apply(model, op)))
    return ops

def fragmenting_ops(rng, model, rounds):
    """two files appended to in turn, a block at a time: many extents"""
    ops = []
    for name in (b"/frag-a", b"/frag-b"):
        op = make_op("create", name, 0o644)
        ops.append((op, apply(model, op)))
    for i in range(rounds):
        for name in (b"/frag-a", b"/frag-b"):
            op = make_op("append", name, model.bs, rng.randrange(1 << 30))
            ops.append((op, apply(model, op)))
    for name, size in ((b"/frag-a", model.bs * rounds // 3), (b"/frag-b", 5)):
        op = make_op("truncate", name, size)
        ops.append((op, apply(model, op)))
    return ops

# ---------------------------------------------------------------- the cases

MKE2FS = [  # name, mke2fs arguments, MiB, block size, tree options, options
    ("ext2-1k", ["-t", "ext2", "-b", "1024"], 3, 1024, {}, {"far": 0.08}),
    ("ext2-4k", ["-t", "ext2", "-b", "4096"], 4, 4096, {}, {}),
    ("ext2-rev0", ["-t", "ext2", "-r", "0", "-b", "1024"], 2, 1024, {}, {}),
    ("ext2-gdtcsum", ["-t", "ext2", "-b", "1024", "-O", "uninit_bg", "-g", "1024", "-N", "128"], 3, 1024, {}, {}),
    ("ext3-1k", ["-t", "ext3", "-b", "1024"], 3, 1024, {}, {}),
    ("ext4-1k", ["-t", "ext4", "-b", "1024"], 3, 1024, {}, {"far": 0.05}),
    ("ext4-4k", ["-t", "ext4", "-b", "4096"], 6, 4096, {}, {}),
    ("ext4-nocsum", ["-t", "ext4", "-b", "1024", "-O", "^metadata_csum"], 3, 1024, {}, {}),
    ("ext4-no64bit", ["-t", "ext4", "-b", "1024", "-O", "^64bit"], 3, 1024, {}, {}),
    ("ext4-groups", ["-t", "ext4", "-b", "1024", "-g", "1024", "-N", "128"], 3, 1024, {}, {}),
    ("ext4-metabg", ["-t", "ext4", "-b", "1024", "-g", "256", "-N", "160", "-O", "meta_bg,^resize_inode"], 3, 1024, {}, {}),
    ("ext4-htree", ["-t", "ext4", "-b", "1024"], 3, 1024, {"many": 120}, {"htree": True}),
]

def nonzero(img, bs):
    data = open(img, "rb").read()
    return [i for i in range(len(data) // bs) if any(data[i * bs:(i + 1) * bs])], len(data) // bs

def chunked(name, items, typ, size=30):
    """defs of at most size items each, joined: (defs, expression)"""
    defs, parts = [], []
    for k in range(0, len(items), size):
        dn = "%s_%d" % (name, k // size)
        defs.append("def %s() -> List<&2, %s>:\n  [%s]\n" % (dn, typ, ",\n   ".join(items[k:k + size])))
        parts.append("%s()" % dn)
    expr = "Nil{}"
    for p in reversed(parts):
        expr = "List.append(&2, %s, %s, %s)" % (typ, p, expr)
    return defs, expr

def wopts(check="Local", alloc="default", csum="Update", extents=True, time=1700000000):
    return "W %s %s %s %d %d" % (check.lower(), alloc.lower(), csum.lower(), 1 if extents else 0, time)

def gen(seed, work):
    rng = random.Random(seed)
    cases = []   # (name, source expr, bs, count, wo expr, ops, model, extra)
    for name, args, mib, bs, tcfg, ocfg in MKE2FS:
        model = Model(bs)
        root = os.path.join(work, name + ".tree")
        build_tree(rng, root, model, tcfg)
        img = os.path.join(work, name + ".img")
        with open(img, "wb") as f:
            f.truncate(mib << 20)
        r = run("mke2fs", "-q", "-F", "-E", "root_owner=0:0", *args, "-d", root, img)
        assert r.returncode == 0, r.stderr
        if ocfg.get("htree"):
            run("e2fsck", "-fyD", img)
            model.root.children[b"many"].indexed = True
        assert run("e2fsck", "-fn", img).returncode == 0, name
        nz, count = nonzero(img, bs)
        budget = (count * bs) // 4
        ops = random_ops(rng, model, 45, budget, ocfg)
        if ocfg.get("htree"):
            for op in (make_op("create", b"/many/new", 0o644), make_op("unlink", b"/many/" + sorted(model.root.children[b"many"].children)[0]), make_op("create", b"/notmany", 0o644)):
                ops.append((op, apply(model, op)))
        cases.append(dict(name=name, src=("file", img, nz), bs=bs, count=count, wo=wopts(), ops=ops, model=model))
    # the same image, other options
    for base, cname, wo, extra in (("ext4-1k", "ext4-1k-full", wopts(check="Full"), 20), ("ext2-1k", "ext2-1k-firstfit-full", wopts(check="Full", alloc="first_fit"), 20), ("ext4-1k", "ext4-1k-nocheck-maps", wopts(check="None", extents=False), 40)):
        b = [c for c in cases if c["name"] == base][0]
        model = Model(b["bs"])
        img = b["src"][1]
        # the model of the image as mke2fs made it: rebuild from the tree
        shutil.rmtree(os.path.join(work, cname + ".tree"), ignore_errors=True)
        model = model_of_image(img, b["bs"])
        ops = random_ops(rng, model, extra, (b["count"] * b["bs"]) // 4, {})
        cases.append(dict(name=cname, src=b["src"], bs=b["bs"], count=b["count"], wo=wo, ops=ops, model=model))
    # many extents (a depth-1 tree): two files growing in turn
    b = [c for c in cases if c["name"] == "ext4-1k"][0]
    model = model_of_image(b["src"][1], 1024)
    ops = fragmenting_ops(rng, model, 70) + [(make_op("fsck"), "fsck ok")]
    cases.append(dict(name="ext4-1k-extents", src=b["src"], bs=1024, count=b["count"], wo=wopts(), ops=ops, model=model))
    # checksums refused: every write refused, the image unchanged
    model = model_of_image(b["src"][1], 1024)
    model.csum_refused = True
    ops = random_ops(rng, model, 6, 1 << 30, {})
    cases.append(dict(name="ext4-1k-csum-refused", src=b["src"], bs=1024, count=b["count"], wo=wopts(csum="Refuse"), ops=ops, model=model))
    # an unwritten extent (fallocate): writes into it refused
    img = os.path.join(work, "ext4-unwritten.img")
    shutil.copy(b["src"][1], img)
    model = model_of_image(img, 1024)
    run("debugfs", "-w", "-R", "write /dev/null /prealloc", img)
    run("debugfs", "-w", "-R", "fallocate /prealloc 0 3", img)
    run("debugfs", "-w", "-R", "sif /prealloc size 4096", img)
    assert run("e2fsck", "-fn", img).returncode == 0
    f = File(b"\0" * 4096)
    f.unwritten = {0, 1, 2, 3}
    model.root.children[b"prealloc"] = f
    nz, count = nonzero(img, 1024)
    ops = []
    for op in (make_op("write", b"/prealloc", 10, 5, 1), make_op("append", b"/prealloc", 100, 2), make_op("truncate", b"/prealloc", 1000), make_op("write", b"/prealloc", 10, 5, 3), make_op("truncate", b"/prealloc", 0), make_op("write", b"/prealloc", 0, 3000, 4)):
        ops.append((op, apply(model, op)))
    cases.append(dict(name="ext4-unwritten", src=("file", img, nz), bs=1024, count=count, wo=wopts(), ops=ops, model=model))
    # corruptions the package's fsck must find
    for cname, how in (("corrupt-bitmap", "bitmap"), ("corrupt-links", "links"), ("corrupt-count", "count")):
        img = os.path.join(work, cname + ".img")
        shutil.copy([c for c in cases if c["name"] == "ext2-1k"][0]["src"][1], img)
        corrupt(img, how)
        nz, count = nonzero(img, 1024)
        model = model_of_image(img, 1024)
        cases.append(dict(name=cname, src=("file", img, nz), bs=1024, count=count, wo=wopts(check="None"), ops=[(make_op("fsck"), "fsck err Ext2CheckFailed")], model=model, corrupt=True))
    # filesystems made by the package's mkfs
    MKFS = [  # name, profile, blocks, log block, inode size, ratio, blocks per group, check
        ("mkfs-ext2", "ext2", 2048, 0, 256, 4096, 0, "Local"),
        ("mkfs-ext2-groups", "ext2", 4096, 0, 128, 8192, 1024, "Full"),
        ("mkfs-ext2-2k", "ext2", 1500, 1, 256, 8192, 0, "Local"),
        ("mkfs-ext4", "ext4", 1024, 2, 256, 16384, 0, "Local"),
        ("mkfs-ext4-1k-groups", "ext4", 6000, 0, 256, 4096, 2048, "Full"),
        ("mkfs-ext4-128", "ext4", 3000, 0, 128, 4096, 0, "Local"),
    ]
    for cname, prof, blocks, log, isz, ratio, bpg, check in MKFS:
        bs = 1024 << log
        uuid = bytes(rng.randrange(256) for _ in range(16))
        mo = "K %s %d %d %d %d %d 1700000000 %s %d %d" % (prof, blocks, log, isz, ratio, bpg, hx(uuid), bs, blocks)
        model = Model(bs)
        n = 40 if check == "Local" else 25
        ops = random_ops(rng, model, n, (blocks * bs) // 4, {})
        cases.append(dict(name=cname, src=("mkfs", mo), bs=bs, count=blocks, wo=wopts(check=check), ops=ops, model=model, mkfs=dict(profile=prof, blocks=blocks, bs=bs, isz=isz)))
    write_cases(cases, work)
    plan = []
    for c in cases:
        listing, groups = c["model"].listing()
        plan.append(dict(name=c["name"], bs=c["bs"], count=c["count"], outcomes=[o for _, o in c["ops"]],
                         tree={hx(k): v for k, v in listing.items()}, groups=[[hx(p) for p in g] for g in groups],
                         corrupt=c.get("corrupt", False), mkfs=c.get("mkfs"),
                         contents={hx(p): hx(bytes(x.data)) for p, x in c["model"].paths() if isinstance(x, File) and len(x.data) < (1 << 20)},
                         big={hx(p): [len(x.data), zlib.crc32(bytes(x.data))] for p, x in c["model"].paths() if isinstance(x, File) and len(x.data) >= (1 << 20)}))
    json.dump(plan, open(os.path.join(work, "plan.json"), "w"))
    print(len(cases), "cases,", sum(len(c["ops"]) for c in cases), "operations")

def model_of_image(img, bs):
    """the model of an image, read with debugfs (rdump and ls -p)"""
    model = Model(bs)
    del model.root.children[b"lost+found"]
    out = os.path.join(os.path.dirname(img), "rdump-" + os.path.basename(img))
    shutil.rmtree(out, ignore_errors=True)
    os.makedirs(out)
    run("debugfs", "-R", "rdump / " + out, img)
    inode_of = {}
    def walk(path, d, host):
        r = run("debugfs", "-R", "ls -p " + (path.decode() or "/"), img).stdout.decode("latin-1")
        for line in r.splitlines():
            parts = line.split("/")
            if len(parts) < 7:
                continue
            ino, mode, name = int(parts[1]), int(parts[2], 8), parts[5].encode("latin-1")
            if name in (b".", b"..", b"") or ino == 0:
                continue
            hp = os.path.join(host, name.decode("latin-1"))
            if mode & 0o170000 == 0o040000:
                nd = Dir(d)
                d.children[name] = nd
                walk(path + b"/" + name, nd, hp)
            elif ino in inode_of:
                d.children[name] = inode_of[ino]
            elif mode & 0o170000 == 0o120000:
                inode_of[ino] = Link(os.readlink(hp).encode("latin-1"))
                d.children[name] = inode_of[ino]
            else:
                inode_of[ino] = File(open(hp, "rb").read())
                d.children[name] = inode_of[ino]
    walk(b"", model.root, out)
    return model

def corrupt(img, how):
    sb = open(img, "rb").read()[1024:2048]
    if how == "bitmap":
        # a used block (the root directory's) marked free; freeb moves the
        # free counts with it, so only the bitmap is wrong
        r = run("debugfs", "-R", "stat /", img).stdout.decode()
        blk = int(r.split("BLOCKS:")[1].split(":")[1].split()[0].split("-")[0])
        run("debugfs", "-w", "-R", "freeb %d" % blk, img)
    elif how == "links":
        run("debugfs", "-w", "-R", "sif / links_count 7", img)
    elif how == "count":
        r = run("dumpe2fs", "-h", img).stdout.decode()
        free = int([l for l in r.splitlines() if l.startswith("Free inodes:")][0].split()[-1])
        run("debugfs", "-w", "-R", "ssv free_inodes_count %d" % (free + 3), img)

def write_cases(cases, work):
    out = []
    for c in cases:
        out.append("C " + c["name"])
        if c["src"][0] == "file":
            out.append("F %s %d %d" % (c["src"][1], c["bs"], c["count"]))
            nz = c["src"][2]
            for k in range(0, len(nz), 100):
                out.append("Z " + " ".join(str(x) for x in nz[k:k + 100]))
        else:
            out.append(c["src"][1])
        out.append(c["wo"])
        out += [op.bend for op, _ in c["ops"]]
        out.append("E")
    open(os.path.join(work, "cases.txt"), "w").write(chr(10).join(out) + chr(10))

# ---------------------------------------------------------------- checking

def check(work, outfile):
    plan = json.load(open(os.path.join(work, "plan.json")))
    text = open(outfile, encoding="latin-1").read().splitlines()
    sections, cur = {}, None
    for line in text:
        if line.startswith("== "):
            cur = line[3:]
            sections[cur] = []
        elif cur is not None:
            sections[cur].append(line)
    bad = []
    nops = 0
    for c in plan:
        name = c["name"]
        def fail(msg):
            bad.append("%s: %s" % (name, msg))
        lines = sections.get(name)
        if lines is None:
            fail("no output")
            continue
        outs = [l for l in lines if l.startswith("op ")]
        got = [" ".join(l.split(" ")[2:]).split(":")[0] for l in outs]
        want = c["outcomes"]
        nops += len(want)
        if len(got) != len(want):
            fail("%d outcomes, %d expected: %s" % (len(got), len(want), lines[:3]))
        for k, (g, w) in enumerate(zip(got, want)):
            if g != w:
                fail("op %d: %s, expected %s (%s)" % (k, outs[k], w, ""))
        if any(l.startswith("mkfs err") or l.startswith("open err") for l in lines):
            fail([l for l in lines if " err " in l][0])
            continue
        # the tree the package reads back
        tree = {}
        for l in lines:
            if l.startswith("t "):
                parts = l.split(" ")
                if parts[2] == "err":
                    fail(l)
                    continue
                tree[parts[1]] = parts[2:]
        if not c["corrupt"]:
            want_tree = c["tree"]
            for p, (kind, size, links, crc, target) in want_tree.items():
                g = tree.get(p)
                if g is None:
                    fail("missing %s" % bytes.fromhex(p))
                    continue
                if g[0] != kind or int(g[2]) != links or (size is not None and int(g[1]) != size):
                    fail("%s: %s, expected %s" % (bytes.fromhex(p), g, (kind, size, links)))
                if kind == "file" and crc != "big" and g[3] != str(crc):
                    fail("%s: crc %s, expected %s" % (bytes.fromhex(p), g[3], crc))
                if kind == "symlink" and g[4] != target:
                    fail("%s: target %s" % (bytes.fromhex(p), g[4]))
            for p in tree:
                if p not in want_tree and bytes.fromhex(p) != b"/lost+found":
                    fail("extra %s" % bytes.fromhex(p))
        # the image
        blocks = {}
        for l in lines:
            if l.startswith("blk "):
                _, n, h = l.split(" ", 2)
                blocks[int(n)] = bytes.fromhex(h)
        img = os.path.join(work, name + ".out.img")
        with open(img, "wb") as f:
            f.truncate(c["count"] * c["bs"])
            for n, b in blocks.items():
                f.seek(n * c["bs"])
                f.write(b)
        if c["corrupt"]:
            continue
        r = run("e2fsck", "-fn", img)
        if r.returncode != 0:
            fail("e2fsck: " + r.stdout.decode("latin-1")[-1500:])
            continue
        m = model_of_image(img, c["bs"])
        listing, groups = m.listing()
        if {hx(k): list(v) for k, v in listing.items()} != {k: list(v) for k, v in c["tree"].items()}:
            diff = set(listing) ^ set(bytes.fromhex(k) for k in c["tree"])
            fail("debugfs tree differs: %s" % sorted(diff)[:5])
        if sorted(sorted(hx(p) for p in g) for g in groups) != sorted(sorted(g) for g in c["groups"]):
            fail("debugfs hard links differ")
        for p, data in c["contents"].items():
            n = dict(m.paths()).get(bytes.fromhex(p))
            if n is None or bytes(n.data).hex() != data:
                fail("debugfs content of %s differs" % bytes.fromhex(p))
        for p, (size, crc) in c["big"].items():
            n = dict(m.paths()).get(bytes.fromhex(p))
            if n is None or len(n.data) != size or zlib.crc32(bytes(n.data)) != crc:
                fail("debugfs content of %s differs" % bytes.fromhex(p))
        os.remove(img)
    if bad:
        print("\n".join(bad[:40]))
        print("%d problems" % len(bad))
        sys.exit(1)
    print("%d cases, %d operations match" % (len(plan), nops))

if __name__ == "__main__":
    if sys.argv[1] == "gen":
        gen(int(sys.argv[2]), sys.argv[3])
    else:
        check(sys.argv[2], sys.argv[3])
