#!/usr/bin/env python3
"""Differential test cases for bend-osdev-landlock.

Writes ref/cases-NN.bend (Bend programs printing the package's answer to
each case) and ref/expected.txt (the answers of an independent Python model
of Landlock, written here from landlock(7), landlock_create_ruleset(2),
landlock_add_rule(2), landlock_restrict_self(2) and the kernel's
userspace-api/landlock document; it shares an author with the package).

When the running kernel supports Landlock, every filesystem case whose
rulesets the kernel's ABI can express is also run for real: a forked child
builds the rulesets with landlock_create_ruleset and landlock_add_rule on a
scratch directory tree, enforces them with landlock_restrict_self, makes the
system call (open, opendir, execve, truncate, mknod, mkdir, mkfifo, symlink,
bind of a UNIX socket, unlink, rmdir, rename, link) and reports the errno,
which must be the model's answer. So do the API cases the kernel can run
(creating rulesets, adding rules, the layer limit). Network and scoping
cases need ABI 4 and 6; on an older kernel they are checked against the
model only.

  python3 gen.py [seed]        prints "<cases> cases, <kernel> on the kernel (ABI n)"
"""
import ctypes, errno, os, random, shutil, socket, stat, struct, sys, tempfile

# ---------------------------------------------------------------------------
# The model, on the kernel's bit masks

FS = ["EXECUTE", "WRITE_FILE", "READ_FILE", "READ_DIR", "REMOVE_DIR", "REMOVE_FILE", "MAKE_CHAR", "MAKE_DIR",
      "MAKE_REG", "MAKE_SOCK", "MAKE_FIFO", "MAKE_BLOCK", "MAKE_SYM", "REFER", "TRUNCATE", "IOCTL_DEV"]
B = {n: 1 << i for i, n in enumerate(FS)}
NET = ["BIND_TCP", "CONNECT_TCP"]
SCOPE = ["ABSTRACT_UNIX_SOCKET", "SIGNAL"]
FILE_RIGHTS = B["EXECUTE"] | B["WRITE_FILE"] | B["READ_FILE"] | B["TRUNCATE"] | B["IOCTL_DEV"]
ALL_FS = (1 << 16) - 1

def abi_fs(v):
    m = 0
    if v >= 1: m |= (1 << 13) - 1
    if v >= 2: m |= B["REFER"]
    if v >= 3: m |= B["TRUNCATE"]
    if v >= 5: m |= B["IOCTL_DEV"]
    return m

def abi_net(v):
    return 3 if v >= 4 else 0

def abi_scope(v):
    return 3 if v >= 6 else 0

KINDS = ["reg", "dir", "chr", "blk", "fifo", "sock", "sym"]
MAKE = {"reg": "MAKE_REG", "dir": "MAKE_DIR", "chr": "MAKE_CHAR", "blk": "MAKE_BLOCK", "fifo": "MAKE_FIFO",
        "sock": "MAKE_SOCK", "sym": "MAKE_SYM"}

def remove_right(k):
    return B["REMOVE_DIR"] if k == "dir" else B["REMOVE_FILE"]

def carried(k):
    return ALL_FS if k == "dir" else FILE_RIGHTS

class Ruleset:
    def __init__(self, fs, net, scope):
        self.fs, self.net, self.scope = fs, net, scope
        self.paths = []   # (components, mask)
        self.ports = []   # (port, mask)

def beneath(p, q):
    return p[:len(q)] == q

def granted(rs, p):
    m = 0
    for q, a in rs.paths:
        if beneath(p, q):
            m |= a
    return m & rs.fs

def handles(rs, bit):
    if bit == B["REFER"]:
        return rs.fs != 0
    return rs.fs & bit != 0

def layer_allows(rs, p, req):
    g = granted(rs, p)
    for i in range(16):
        bit = 1 << i
        if req & bit and handles(rs, bit) and not g & bit:
            return False
    return True

def allows(layers, p, req):
    return all(layer_allows(rs, p, req) for _, rs in layers)

def layer_move(rs, src, dst, kind, remove):
    ok = layer_allows(rs, dst, B[MAKE[kind]]) and (not remove or layer_allows(rs, src, remove_right(kind)))
    if not ok:
        return "EACCES"
    if src == dst:
        return "OK"
    if not (layer_allows(rs, src, B["REFER"]) and layer_allows(rs, dst, B["REFER"])):
        return "EXDEV"
    if granted(rs, dst) & carried(kind) & ~granted(rs, src):
        return "EXDEV"
    return "OK"

def move(layers, src, dst, kind, remove):
    rs = [layer_move(r, src, dst, kind, remove) for _, r in layers]
    if "EACCES" in rs: return "EACCES"
    if "EXDEV" in rs: return "EXDEV"
    return "OK"

def net_allows(layers, port, bit):
    for _, rs in layers:
        if rs.net & bit:
            g = 0
            for p, a in rs.ports:
                if p == port:
                    g |= a
            if not g & rs.net & bit:
                return False
    return True

def scope_allows(layers, target_ids, bit):
    return all(i in target_ids for i, rs in layers if rs.scope & bit)

OPEN_REQ = lambda r, w, t: (B["READ_FILE"] if r else 0) | (B["WRITE_FILE"] if w else 0) | (B["TRUNCATE"] if t else 0)

def decide(layers, op):
    k = op[0]
    if k == "open":
        return "OK" if allows(layers, op[1], OPEN_REQ(op[2], op[3], op[4])) else "EACCES"
    if k == "exec":  # execve opens the file to read it, too
        return "OK" if allows(layers, op[1], B["EXECUTE"] | B["READ_FILE"]) else "EACCES"
    if k in ("readdir", "truncate", "ioctl"):
        bit = {"readdir": "READ_DIR", "truncate": "TRUNCATE", "ioctl": "IOCTL_DEV"}[k]
        return "OK" if allows(layers, op[1], B[bit]) else "EACCES"
    if k == "create":
        return "OK" if allows(layers, op[1], B[MAKE[op[2]]]) else "EACCES"
    if k == "remove":
        return "OK" if allows(layers, op[1], remove_right(op[2])) else "EACCES"
    if k == "rename":
        return move(layers, op[1], op[2], op[3], True)
    if k == "link":
        return move(layers, op[1], op[2], op[3], False)
    if k in ("bind", "connect"):
        return "OK" if net_allows(layers, op[1], 1 if k == "bind" else 2) else "EACCES"
    if k in ("signal", "abstract"):
        return "OK" if scope_allows(layers, op[1], 2 if k == "signal" else 1) else "EPERM"
    raise ValueError(k)

# The system calls, as the model answers them (error names as the package's)

def create(abi, strict, fs, net, scope):
    if not strict:
        return ("ok", fs & abi_fs(abi), net & abi_net(abi), scope & abi_scope(abi))
    if abi == 0:
        return ("fail", "LandlockNotSupported")
    if fs & ~abi_fs(abi) or net & ~abi_net(abi) or scope & ~abi_scope(abi):
        return ("fail", "LandlockUnknownAccess")
    if not (fs or net or scope):
        return ("fail", "LandlockEmptyRuleset")
    return ("ok", fs, net, scope)

def add_path(abi, strict, handled, is_dir, allowed):
    if not strict:
        a = allowed & abi_fs(abi)
        if allowed and not a:
            return ("ok", 0)
        allowed = a
    if not allowed:
        return ("fail", "LandlockEmptyRule")
    if allowed & ~handled:
        return ("fail", "LandlockRuleNotHandled")
    if not is_dir and allowed & ~FILE_RIGHTS:
        return ("fail", "LandlockDirRightOnFile")
    return ("ok", 1)

def add_port(abi, strict, handled, port, allowed):
    if not strict:
        a = allowed & abi_net(abi)
        if allowed and not a:
            return ("ok", 0)
        allowed = a
    if not allowed:
        return ("fail", "LandlockEmptyRule")
    if allowed & ~handled:
        return ("fail", "LandlockRuleNotHandled")
    if port > 65535:
        return ("fail", "LandlockBadPort")
    return ("ok", 1)

ERRNO = {"LandlockNotSupported": "EOPNOTSUPP", "LandlockUnknownAccess": "EINVAL", "LandlockEmptyRuleset": "ENOMSG",
         "LandlockEmptyRule": "ENOMSG", "LandlockRuleNotHandled": "EINVAL", "LandlockDirRightOnFile": "EINVAL",
         "LandlockBadPort": "EINVAL", "LandlockTooManyLayers": "E2BIG", "LandlockNoNewPrivs": "EPERM"}

def show_create(r):
    return "fail " + r[1] if r[0] == "fail" else "ok %d %d %d" % r[1:]

def show_add(r):
    return "fail " + r[1] if r[0] == "fail" else "ok %d" % r[1]

# ---------------------------------------------------------------------------
# The kernel

libc = ctypes.CDLL(None, use_errno=True)
libc.syscall.restype = ctypes.c_long
SYS_CREATE, SYS_ADD, SYS_RESTRICT = 444, 445, 446

class Attr(ctypes.Structure):
    _fields_ = [("fs", ctypes.c_uint64)]

class PathBeneath(ctypes.Structure):
    _pack_ = 1
    _fields_ = [("allowed", ctypes.c_uint64), ("fd", ctypes.c_int32)]

def sc(*a):
    r = libc.syscall(*[ctypes.c_long(x) if isinstance(x, int) else x for x in a])
    return r, ctypes.get_errno()

def kernel_abi():
    if not sys.platform.startswith("linux"):
        return 0
    r, e = sc(SYS_CREATE, None, 0, 1)
    return r if r > 0 else 0

def k_layer(root, rs):
    a = Attr(rs.fs)
    fd, e = sc(SYS_CREATE, ctypes.byref(a), ctypes.sizeof(a), 0)
    if fd < 0:
        return "create " + errno.errorcode[e]
    for q, m in rs.paths:
        pfd = os.open(os.path.join(root, *q) if q else root, os.O_PATH)
        pb = PathBeneath(m, pfd)
        r, e = sc(SYS_ADD, fd, 1, ctypes.byref(pb), 0)
        os.close(pfd)
        if r < 0:
            return "add " + errno.errorcode[e]
    libc.prctl(38, 1, 0, 0, 0)  # PR_SET_NO_NEW_PRIVS
    r, e = sc(SYS_RESTRICT, fd, 0)
    os.close(fd)
    if r < 0:
        return "restrict " + errno.errorcode[e]
    return None

def in_child(fn):
    """Runs fn in a forked child; answers what it writes (nothing if it execs)."""
    rd, wr = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(rd)
        try:
            res = fn()
        except Exception as ex:  # report, never fall through into the parent's code
            res = "EXC " + repr(ex)
        os.write(wr, str(res).encode())
        os._exit(0)
    os.close(wr)
    out = b""
    while True:
        chunk = os.read(rd, 4096)
        if not chunk:
            break
        out += chunk
    os.close(rd)
    os.waitpid(pid, 0)
    return out.decode() or "OK"

# A static x86-64 program that exits 0, for execve (the scratch tree has no
# dynamic loader beneath it, and READ_FILE may be handled)
def exit0_elf():
    code = b"\xb8\x3c\x00\x00\x00\x31\xff\x0f\x05"  # mov eax, 60; xor edi, edi; syscall
    ehdr = struct.pack("<4sBBBBB7xHHIQQQIHHHHHH", b"\x7fELF", 2, 1, 1, 0, 0, 2, 62, 1, 0x400078, 64, 0, 0, 64, 56, 1, 0, 0, 0)
    phdr = struct.pack("<IIQQQQQQ", 1, 5, 0, 0x400000, 0x400000, 120 + len(code), 120 + len(code), 0x1000)
    return ehdr + phdr + code

DIRS = [("a",), ("a", "b"), ("a", "b", "c"), ("d",), ("d", "e"), ("d", "k")]
FILES = [("r",), ("a", "f"), ("a", "b", "g"), ("d", "h"), ("d", "e", "i"), ("a", "x")]
EMPTY_DIRS = [(("a", "b"), "c"), (("d",), "k")]
FILE_IN = [((), "r"), (("a",), "f"), (("a", "b"), "g"), (("d",), "h"), (("d", "e"), "i")]
ALL_DIRS = [()] + DIRS

def make_tree(root):
    for d in DIRS:
        os.mkdir(os.path.join(root, *d))
    for f in FILES:
        with open(os.path.join(root, *f), "wb") as h:
            h.write(exit0_elf() if f == ("a", "x") else b"data\n")
    os.chmod(os.path.join(root, "a", "x"), 0o755)

def k_op(root, op):
    j = lambda q, *n: os.path.join(root, *q, *n)
    k = op[0]
    if k == "open":
        r, w, t = op[2], op[3], op[4]
        flags = (os.O_RDWR if r and w else os.O_WRONLY if w else os.O_RDONLY) | (os.O_TRUNC if t else 0)
        os.close(os.open(j(op[1]), flags))
    elif k == "readdir":
        os.listdir(j(op[1]))
    elif k == "exec":
        os.execv(j(op[1]), [j(op[1])])
    elif k == "truncate":
        os.truncate(j(op[1]), 0)
    elif k == "create":
        p = j(op[1], "new")
        kind = op[2]
        if kind == "reg": os.mknod(p, stat.S_IFREG | 0o644)
        elif kind == "dir": os.mkdir(p)
        elif kind == "fifo": os.mkfifo(p)
        elif kind == "sym": os.symlink("target", p)
        elif kind == "sock": socket.socket(socket.AF_UNIX).bind(p)
    elif k == "remove":
        if op[2] == "dir": os.rmdir(j(op[1], op[3]))
        else: os.unlink(j(op[1], op[3]))
    elif k == "rename":
        os.rename(j(op[1], op[4]), j(op[2], "moved"))
    elif k == "link":
        os.link(j(op[1], op[4]), j(op[2], "linked"))

def k_run(layers, op):
    root = tempfile.mkdtemp(prefix="landlock-ref-")
    try:
        make_tree(root)
        def child():
            for _, rs in layers:
                err = k_layer(root, rs)
                if err:
                    return err
            try:
                k_op(root, op)
                return "OK"
            except OSError as ex:
                return errno.errorcode[ex.errno]
        return in_child(child)
    finally:
        shutil.rmtree(root, ignore_errors=True)

def k_api(fn):
    return in_child(fn)

# ---------------------------------------------------------------------------
# Cases

def bend_bool(b):
    return "True{}" if b else "False{}"

def bend_path(q):
    return '"/' + "/".join(q) + '"'

def bend_rs(rs):
    pr = "[" + ", ".join("(%s, %d)" % (bend_path(q), m) for q, m in rs.paths) + "]"
    po = "[" + ", ".join("(%d, %d)" % (p, m) for p, m in rs.ports) + "]"
    return "rs(%d, %d, %d, %s, %s)" % (rs.fs, rs.net, rs.scope, pr, po)

def bend_dom(layers):
    return "dm([" + ", ".join(bend_rs(rs) for _, rs in layers) + "])"

def bend_op(op):
    k = op[0]
    if k == "open":
        return "L.LandlockOpOpen{pp(%s), %s, %s, %s}" % (bend_path(op[1]), bend_bool(op[2]), bend_bool(op[3]), bend_bool(op[4]))
    if k in ("readdir", "exec", "truncate", "ioctl"):
        c = {"readdir": "ReadDir", "exec": "Exec", "truncate": "Truncate", "ioctl": "Ioctl"}[k]
        return "L.LandlockOp%s{pp(%s)}" % (c, bend_path(op[1]))
    if k in ("create", "remove"):
        return "L.LandlockOp%s{pp(%s), kd(%dn)}" % ("Create" if k == "create" else "Remove", bend_path(op[1]), KINDS.index(op[2]))
    if k in ("rename", "link"):
        return "L.LandlockOp%s{pp(%s), pp(%s), kd(%dn)}" % ("Rename" if k == "rename" else "Link", bend_path(op[1]), bend_path(op[2]), KINDS.index(op[3]))
    if k in ("bind", "connect"):
        return "L.LandlockOp%s{%d}" % ("Bind" if k == "bind" else "Connect", op[1])
    if k in ("signal", "abstract"):
        return "L.LandlockOp%s{tg([%s])}" % ("Signal" if k == "signal" else "ConnectAbstract", ", ".join(str(i) for i in op[1]))

def rand_sub(rng, mask, p=0.5):
    return sum(1 << i for i in range(32) if mask >> i & 1 and rng.random() < p)

def rand_fs_layer(rng, abi, kernel_ok):
    hm = abi_fs(abi)
    handled = rand_sub(rng, hm, rng.choice([0.15, 0.3, 0.6, 0.9]))
    if handled == 0:
        handled = 1 << rng.choice([i for i in range(16) if hm >> i & 1])
    rs = Ruleset(handled, 0, 0)
    for _ in range(rng.randrange(0, 7)):
        if rng.random() < 0.75:
            q = rng.choice(ALL_DIRS)
            allowed = rand_sub(rng, handled, rng.choice([0.5, 0.8, 1.0]))
        else:
            q = rng.choice(FILES)
            allowed = rand_sub(rng, handled & FILE_RIGHTS, 0.7)
        if allowed:
            rs.paths.append((q, allowed))
    return rs

def rand_fs_op(rng, abi):
    k = rng.choice(["open", "open", "readdir", "exec", "truncate", "create", "create", "remove", "remove",
                    "rename", "rename", "rename", "link", "link"])
    if k == "open":
        r, w = rng.choice([(True, False), (False, True), (True, True)])
        return ("open", rng.choice(FILES[:-1]), r, w, rng.random() < 0.3)
    if k == "readdir":
        return ("readdir", rng.choice(ALL_DIRS))
    if k == "exec":
        return ("exec", ("a", "x"))
    if k == "truncate":
        return ("truncate", rng.choice(FILES[:-1]))
    if k == "create":
        return ("create", rng.choice(ALL_DIRS), rng.choice(["reg", "dir", "fifo", "sym", "sock"]))
    if k == "remove":
        if rng.random() < 0.4:
            d, n = rng.choice(EMPTY_DIRS)
            return ("remove", d, "dir", n)
        d, n = rng.choice(FILE_IN)
        return ("remove", d, "reg", n)
    if k == "rename":
        if rng.random() < 0.3:
            d, n = rng.choice(EMPTY_DIRS)
            dst = rng.choice([x for x in ALL_DIRS if x != d + (n,)])
            return ("rename", d, dst, "dir", n)
        d, n = rng.choice(FILE_IN)
        dst = d if rng.random() < 0.25 else rng.choice(ALL_DIRS)
        return ("rename", d, dst, "reg", n)
    d, n = rng.choice(FILE_IN)
    dst = d if rng.random() < 0.2 else rng.choice(ALL_DIRS)
    return ("link", d, dst, "reg", n)

def model_op(op):
    """The operation in the model's terms (the file names dropped)."""
    if op[0] == "remove":
        return op[:3]
    if op[0] in ("rename", "link"):
        return op[:4]
    return op

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    kabi = kernel_abi()
    exprs, expect = [], []
    kernel = 0

    def case(expr, want, label):
        exprs.append('ck("%s", %s)' % (label, expr))
        expect.append("%s %s" % (label, want))

    # filesystem accesses, on the kernel's ABI when it has Landlock (else 3)
    for i in range(260):
        abi = kabi if kabi else 3
        layers = [(j + 1, rand_fs_layer(rng, abi, True)) for j in range(rng.choice([1, 1, 2, 3]))]
        op = rand_fs_op(rng, abi)
        want = decide(layers, model_op(op))
        if kabi:
            got = k_run(layers, op)
            if got != want:
                print("kernel and model disagree on fs %d: kernel %s, model %s" % (i, got, want), file=sys.stderr)
                print("  layers", [(hex(rs.fs), rs.paths) for _, rs in layers], "op", op, file=sys.stderr)
                sys.exit(1)
            kernel += 1
        case("F.LandlockDecision.show(L.Landlock.check(%s, %s))" % (bend_dom(layers), bend_op(model_op(op))), want, "fs%d" % i)

    # filesystem accesses on every ABI, every file type and IOCTL_DEV (the model)
    for i in range(80):
        abi = rng.randrange(1, 7)
        layers = [(j + 1, rand_fs_layer(rng, abi, False)) for j in range(rng.choice([1, 2, 3]))]
        k = rng.choice(["create", "remove", "rename", "link", "ioctl", "open"])
        d = rng.choice(ALL_DIRS)
        kind = rng.choice(KINDS)
        if k == "create": op = ("create", d, kind)
        elif k == "remove": op = ("remove", d, kind)
        elif k == "rename": op = ("rename", d, rng.choice(ALL_DIRS), kind)
        elif k == "link": op = ("link", d, rng.choice(ALL_DIRS), kind)
        elif k == "ioctl": op = ("ioctl", rng.choice(FILES))
        else: op = ("open", rng.choice(FILES), True, rng.random() < 0.5, rng.random() < 0.5)
        case("F.LandlockDecision.show(L.Landlock.check(%s, %s))" % (bend_dom(layers), bend_op(op)), decide(layers, op), "fsm%d" % i)

    # network (ABI 4): random port rules, bind and connect
    for i in range(80):
        layers = []
        for j in range(rng.choice([1, 2])):
            rs = Ruleset(rand_sub(rng, B["READ_FILE"] | B["WRITE_FILE"], 0.3), rng.randrange(0, 4), 0)
            for _ in range(rng.randrange(0, 4)):
                a = rand_sub(rng, rs.net, 0.7)
                if a:
                    rs.ports.append((rng.choice([22, 80, 443, 8080]), a))
            layers.append((j + 1, rs))
        op = (rng.choice(["bind", "connect"]), rng.choice([22, 80, 443, 8080]))
        case("F.LandlockDecision.show(L.Landlock.check(%s, %s))" % (bend_dom(layers), bend_op(op)), decide(layers, op), "net%d" % i)

    # scoping (ABI 6): targets in the same domain, nested, a sibling, outside
    for i in range(60):
        n = rng.choice([1, 2, 3])
        layers = [(j + 1, Ruleset(0, 0, rng.randrange(0, 4))) for j in range(n)]
        ids = [j + 1 for j in range(n)]
        t = rng.choice(["same", "nested", "parent", "sibling", "none"])
        target = {"same": ids, "nested": ids + [50], "parent": ids[:-1], "sibling": ids[:-1] + [60], "none": []}[t]
        op = (rng.choice(["signal", "abstract"]), target)
        case("F.LandlockDecision.show(L.Landlock.check(%s, %s))" % (bend_dom(layers), bend_op(op)), decide(layers, op), "scope%d" % i)

    # landlock_create_ruleset: every ABI, both choices
    for i in range(70):
        abi = rng.randrange(0, 7)
        strict = rng.random() < 0.6
        fs = rand_sub(rng, ALL_FS, rng.choice([0, 0.1, 0.5]))
        net = rng.randrange(0, 4) if rng.random() < 0.4 else 0
        scope = rng.randrange(0, 4) if rng.random() < 0.3 else 0
        if kabi and i % 2 == 0:  # half of them as the kernel can run them
            abi, strict, net, scope = kabi, True, 0, 0
        want = show_create(create(abi, strict, fs, net, scope))
        if kabi and strict and abi == kabi and not net and not scope:
            def fn(fs=fs):
                a = Attr(fs)
                r, e = sc(SYS_CREATE, ctypes.byref(a), ctypes.sizeof(a), 0)
                return "ok" if r >= 0 else errno.errorcode[e]
            got = k_api(fn)
            exp = "ok" if want.startswith("ok") else ERRNO[want.split()[1]]
            if got != exp:
                print("kernel and model disagree on create %d: %s %s" % (i, got, want), file=sys.stderr)
                sys.exit(1)
            kernel += 1
        case("cr(%dn, %s, %d, %d, %d)" % (abi, bend_bool(strict), fs, net, scope), want, "create%d" % i)

    # landlock_add_rule, path beneath: on a directory or a file
    for i in range(70):
        abi = rng.randrange(1, 7)
        strict = rng.random() < 0.6
        if kabi and i % 2 == 0:
            abi, strict = kabi, True
        handled = rand_sub(rng, abi_fs(abi), 0.5) or 1
        allowed = rand_sub(rng, rng.choice([ALL_FS, abi_fs(abi), handled, handled, handled & FILE_RIGHTS]), rng.choice([0, 0.3, 0.6]))
        q = rng.choice(ALL_DIRS + FILES)
        is_dir = q not in FILES
        want = show_add(add_path(abi, strict, handled, is_dir, allowed))
        if kabi and strict and abi == kabi:
            def fn(handled=handled, allowed=allowed, q=q):
                root = tempfile.mkdtemp(prefix="landlock-ref-")
                try:
                    make_tree(root)
                    a = Attr(handled)
                    fd, e = sc(SYS_CREATE, ctypes.byref(a), ctypes.sizeof(a), 0)
                    pfd = os.open(os.path.join(root, *q), os.O_PATH)
                    r, e = sc(SYS_ADD, fd, 1, ctypes.byref(PathBeneath(allowed, pfd)), 0)
                    return "ok" if r >= 0 else errno.errorcode[e]
                finally:
                    shutil.rmtree(root, ignore_errors=True)
            got = k_api(fn)
            exp = "ok" if want.startswith("ok") else ERRNO[want.split()[1]]
            if got != exp:
                print("kernel and model disagree on add_rule %d: %s %s" % (i, got, want), file=sys.stderr)
                sys.exit(1)
            kernel += 1
        case("ap(%dn, %s, %d, %s, %s, %d)" % (abi, bend_bool(strict), handled, bend_path(q), bend_bool(is_dir), allowed), want, "addpath%d" % i)

    # landlock_add_rule, net port
    for i in range(40):
        abi = rng.randrange(1, 7)
        strict = rng.random() < 0.6
        handled = rng.randrange(0, 4) & abi_net(abi)
        allowed = rng.randrange(0, 4)
        port = rng.choice([0, 80, 443, 65535, 65536, 100000])
        want = show_add(add_port(abi, strict, handled, port, allowed))
        case("ao(%dn, %s, %d, %d, %d)" % (abi, bend_bool(strict), handled, port, allowed), want, "addport%d" % i)

    # the layer limit
    for n in (15, 16, 17):
        want = "ok %d" % n if n <= 16 else "fail LandlockTooManyLayers"
        if kabi:
            def fn(n=n):
                for j in range(n):
                    a = Attr(B["READ_FILE"])
                    fd, e = sc(SYS_CREATE, ctypes.byref(a), ctypes.sizeof(a), 0)
                    libc.prctl(38, 1, 0, 0, 0)
                    r, e = sc(SYS_RESTRICT, fd, 0)
                    if r < 0:
                        return errno.errorcode[e]
                return "ok"
            got = k_api(fn)
            if got != ("ok" if n <= 16 else "E2BIG"):
                print("kernel and model disagree on %d layers: %s" % (n, got), file=sys.stderr)
                sys.exit(1)
            kernel += 1
        case("ly(%dn)" % n, want, "layers%d" % n)

    head = open(os.path.join(here, "head.bend")).read()
    for old in os.listdir(here):
        if old.startswith("cases-") and old.endswith(".bend"):
            os.remove(os.path.join(here, old))
    per = 120
    for k in range(0, len(exprs), per):
        chunk = exprs[k:k + per]
        with open(os.path.join(here, "cases-%02d.bend" % (k // per)), "w") as f:
            f.write(head)
            f.write("\ndef cases() -> List<&2, String>:\n  [" + ",\n   ".join(chunk) + "]\n")
            f.write("\ndef main() -> IO(Unit):\n  out(cases())\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print("%d cases, %d on the kernel (%s)" % (len(expect), kernel, "Landlock ABI %d" % kabi if kabi else "no Landlock"))

main()
