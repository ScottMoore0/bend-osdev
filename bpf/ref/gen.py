#!/usr/bin/env python3
"""Differential test cases for bend-osdev-bpf.

Writes ref/cases.bend (a Bend program that prints the package's answer for
each case) and ref/expected.txt (the answers of an independent classic BPF
and seccomp implementation, written here from the BSD bpf(4) manual page,
McCanne and Jacobson (USENIX 1993) and the seccomp(2) manual page).

Cases: random valid packet filters over random packets; random invalid and
undecodable programs (the first rule each breaks); unvalidated programs that
run off their end or use a bad scratch index; random seccomp filters over
random struct seccomp_data, alone and stacked.

Then, where the running kernel allows it, the seccomp cases whose filters
answer only ERRNO or ALLOW are also checked against Linux itself: a forked
child sets PR_SET_NO_NEW_PRIVS, installs the filters with PR_SET_SECCOMP,
makes harmless system calls (getppid and friends) with chosen arguments,
and reports which ones failed with which errno. Filters, many of them
broken or reading scratch memory before writing it, check that the kernel
accepts exactly what the validator (with its default options) accepts. The
kernel only confirms the model here; the expected answers never depend on
it.

Prints the case count, then one line about the kernel. Exit status 0, or 3
when installing a seccomp filter is not permitted (the kernel part skipped).
"""
import ctypes, os, platform, random, struct, sys

M32 = 0xFFFFFFFF

# ---------------------------------------------------------------- the model

LD, LDX, ST, STX, ALU, JMP, RET, MISC = range(8)
W, H, B = 0x00, 0x08, 0x10
IMM, ABS, IND, MEM, LEN, MSH = 0x00, 0x20, 0x40, 0x60, 0x80, 0xA0
ADD, SUB, MUL, DIV, OR, AND, LSH, RSH, NEG, MOD, XOR = 0x00, 0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80, 0x90, 0xA0
JA, JEQ, JGT, JGE, JSET = 0x00, 0x10, 0x20, 0x30, 0x40
K, X = 0x00, 0x08
RA = 0x10
TAX, TXA = 0x00, 0x80

def valid_codes():
    c = set()
    for s in (W, H, B):
        c.add(LD | s | ABS); c.add(LD | s | IND)
    c |= {LD | W | IMM, LD | W | LEN, LD | W | MEM, LDX | W | IMM, LDX | W | MEM, LDX | W | LEN, LDX | B | MSH, ST, STX}
    for op in (ADD, SUB, MUL, DIV, OR, AND, LSH, RSH, MOD, XOR):
        c.add(ALU | op | K); c.add(ALU | op | X)
    c.add(ALU | NEG)
    c.add(JMP | JA)
    for op in (JEQ, JGT, JGE, JSET):
        c.add(JMP | op | K); c.add(JMP | op | X)
    c |= {RET | K, RET | RA, MISC | TAX, MISC | TXA}
    return c

CODES = valid_codes()
assert len(CODES) == 49

class Err(Exception):
    pass

def decode(prog):
    for pc, (code, jt, jf, k) in enumerate(prog):
        if code not in CODES:
            raise Err("bad opcode %d at %d" % (code, pc))

def is_mem(code):
    return code in (LD | W | MEM, LDX | W | MEM, ST, STX)

def mem_init(prog):
    """every scratch read follows a write on every path from the start,
    where the instruction after a return counts as reached from it (as the
    running kernel counts it)"""
    n = len(prog)
    into = [None] * n  # slots written on every path seen so far; None: none
    into[0] = 0
    for pc, (code, jt, jf, k) in enumerate(prog):
        m = into[pc]
        if m is None:
            continue
        cls = code & 7
        if code in (LD | W | MEM, LDX | W | MEM) and not m >> k & 1:
            raise Err("scratch read before write at %d" % pc)
        if cls in (ST, STX):
            m |= 1 << k
        if cls == RET:
            succ = [pc + 1] if pc + 1 < n else []
        elif code == JMP | JA:
            succ = [pc + 1 + k]
        elif cls == JMP:
            succ = [pc + 1 + jt, pc + 1 + jf]
        else:
            succ = [pc + 1]
        for t in succ:
            into[t] = m if into[t] is None else into[t] & m

def validate(prog, limit=4096, need_mem_init=True):
    n = len(prog)
    if n == 0:
        raise Err("empty program")
    if n > limit:
        raise Err("program too long: %d" % n)
    for pc, (code, jt, jf, k) in enumerate(prog):
        r = n - pc - 1  # instructions after this one
        cls = code & 7
        if is_mem(code):
            if k >= 16:
                raise Err("scratch index out of range at %d" % pc)
        if cls == ALU and (code & 0xF0) in (DIV, MOD) and (code & 8) == K and k == 0:
            raise Err("division by constant zero at %d" % pc)
        if cls == RET:
            continue
        if code == JMP | JA:
            if not k < r:
                raise Err("jump out of range at %d" % pc)
            continue
        if cls == JMP:
            if jt > 255 or jf > 255:
                raise Err("jump offset over 255 at %d" % pc)
            if not (jt < r and jf < r):
                raise Err("jump out of range at %d" % pc)
            continue
        if r == 0:
            raise Err("no return after %d" % pc)
    if need_mem_init:
        mem_init(prog)

class Stop(Exception):
    def __init__(self, v):
        self.v = v

def load(data, order, size, off):
    n = {W: 4, H: 2, B: 1}[size]
    if off + n > len(data):
        raise Stop(0)
    return int.from_bytes(bytes(data[off:off + n]), order)

def run(prog, data, order="big"):
    """The answer of a decoded program, or Err for what an unvalidated
    program can do wrong."""
    A = X = 0
    mem = [0] * 16
    pc = 0
    try:
        while True:
            if pc >= len(prog):
                raise Err("ran past the end")
            code, jt, jf, k = prog[pc]
            pc += 1
            cls = code & 7
            if cls in (LD, LDX):
                mode, size = code & 0xE0, code & 0x18
                if mode == IMM:
                    v = k
                elif mode == LEN:
                    v = len(data) & M32
                elif mode == MEM:
                    if k >= 16:
                        raise Err("scratch index %d" % k)
                    v = mem[k]
                elif mode == ABS:
                    v = load(data, order, size, k)
                elif mode == IND:
                    v = load(data, order, size, X + k)
                elif mode == MSH:
                    v = 4 * (load(data, order, B, k) & 15)
                if cls == LD:
                    A = v
                else:
                    X = v
            elif cls in (ST, STX):
                if k >= 16:
                    raise Err("scratch index %d" % k)
                mem[k] = A if cls == ST else X
            elif cls == ALU:
                op = code & 0xF0
                v = X if code & 8 else k
                if op == NEG:
                    A = -A & M32
                elif op in (DIV, MOD) and v == 0:
                    return 0
                else:
                    A = {ADD: lambda: A + v, SUB: lambda: A - v, MUL: lambda: A * v, DIV: lambda: A // v,
                         OR: lambda: A | v, AND: lambda: A & v, XOR: lambda: A ^ v, MOD: lambda: A % v,
                         LSH: lambda: A << v if v < 32 else 0, RSH: lambda: A >> v if v < 32 else 0}[op]() & M32
            elif cls == JMP:
                op = code & 0xF0
                if op == JA:
                    pc += k
                else:
                    v = X if code & 8 else k
                    hit = {JEQ: A == v, JGT: A > v, JGE: A >= v, JSET: (A & v) != 0}[op]
                    pc += jt if hit else jf
            elif cls == RET:
                return A if code & RA else k
            elif cls == MISC:
                if code & 0xF8 == TXA:
                    A = X
                else:
                    X = A
    except Stop as s:
        return s.v

# seccomp(2)
KILL_PROCESS, KILL_THREAD, TRAP, ERRNO = 0x80000000, 0, 0x00030000, 0x00050000
USER_NOTIF, TRACE, LOG, ALLOW = 0x7FC00000, 0x7FF00000, 0x7FFC0000, 0x7FFF0000
PRECEDENCE = [KILL_PROCESS, KILL_THREAD, TRAP, ERRNO, USER_NOTIF, TRACE, LOG, ALLOW]
NAMES = {KILL_PROCESS: "KILL_PROCESS", KILL_THREAD: "KILL_THREAD", TRAP: "TRAP", ERRNO: "ERRNO",
         USER_NOTIF: "USER_NOTIF", TRACE: "TRACE", LOG: "LOG", ALLOW: "ALLOW"}

def action(v):
    """(action, data) of a return value; an unnamed action is KILL_PROCESS"""
    act, data = v & 0xFFFF0000, v & 0xFFFF
    if act not in NAMES:
        return (KILL_PROCESS, 0)
    return (act, data if act in (TRAP, ERRNO, TRACE) else 0)

def show_action(a):
    act, data = a
    return NAMES[act] + ("(%d)" % data if act in (TRAP, ERRNO, TRACE) else "")

def combine(actions):
    """the first-seen action of the highest precedence, most recent first"""
    best = None
    for a in actions:
        if best is None or PRECEDENCE.index(a[0]) < PRECEDENCE.index(best[0]):
            best = a
    return best if best is not None else (ALLOW, 0)

def seccomp_validate(prog):
    validate(prog)
    for pc, (code, jt, jf, k) in enumerate(prog):
        if code & 7 == LD and code & 0xE0 in (ABS, IND) or code == LDX | B | MSH:
            if not (code == LD | W | ABS and k % 4 == 0 and k < 64):
                raise Err("load not allowed in seccomp at %d" % pc)
        if code & 7 == ALU and code & 0xF0 == MOD:
            raise Err("instruction not allowed in seccomp at %d" % pc)

def seccomp_bytes(nr, arch, ip, args):
    return list(struct.pack("<iIQ6Q", nr - (1 << 32) if nr >= 1 << 31 else nr, arch, ip, *args))

def seccomp_run(prog, data):
    return action(run(prog, data, "little"))

def install_all(filters, path=32768):
    """the stack after installing each filter, oldest first, or Err"""
    stack = []
    for f in filters:
        decode(f)
        seccomp_validate(f)
        total = len(f) + sum(len(g) + 4 for g in stack)
        if total > path:
            raise Err("seccomp filters too long: %d" % total)
        stack.insert(0, f)
    return stack

# ---------------------------------------------------------- random programs

def rand_k(rng):
    return rng.choice([0, 1, 2, 3, 4, 7, 8, 12, 14, 15, 16, 20, 23, 31, 32, 33, 255, 256, 65535, 0x7FFFFFFF, 0x80000000, M32, rng.randrange(1 << 32), rng.randrange(64)])

def rand_insn(rng, r, off_max=80):
    """a random instruction with r instructions after it (r > 0)"""
    kind = rng.randrange(20)
    if kind < 3:
        return (LD | rng.choice((W, H, B)) | ABS, 0, 0, rng.randrange(off_max if rng.random() < 0.2 else 34))
    if kind < 4:
        return (LD | rng.choice((W, H, B)) | IND, 0, 0, rng.randrange(off_max // 4))
    if kind < 5:
        return rng.choice([(LD | W | IMM, 0, 0, rand_k(rng)), (LD | W | LEN, 0, 0, 0), (LDX | W | IMM, 0, 0, rng.choice([0, 1, 2, 5, 14, 31, 32, 40, rand_k(rng)])), (LDX | W | LEN, 0, 0, 0), (LDX | B | MSH, 0, 0, rng.randrange(off_max))])
    if kind < 7:
        return (rng.choice((LD | W | MEM, LDX | W | MEM, ST, STX)), 0, 0, rng.randrange(16))
    if kind < 11:
        op = rng.choice((ADD, SUB, MUL, DIV, OR, AND, LSH, RSH, MOD, XOR, NEG))
        if op == NEG:
            return (ALU | NEG, 0, 0, 0)
        src = rng.choice((K, X))
        k = rand_k(rng) if src == K else 0
        if op in (DIV, MOD) and src == K and k == 0:
            k = 3
        if op in (LSH, RSH) and src == K:
            k = rng.randrange(40)
        return (ALU | op | src, 0, 0, k)
    if kind < 16:
        if rng.random() < 0.15:
            return (JMP | JA, 0, 0, rng.randrange(r))
        op = rng.choice((JEQ, JGT, JGE, JSET))
        src = rng.choice((K, X))
        k = rand_k(rng) if src == K else 0
        return (JMP | op | src, rng.randrange(min(r, 256)), rng.randrange(min(r, 256)), k)
    if kind < 18:
        return (MISC | rng.choice((TAX, TXA)), 0, 0, 0)
    return rng.choice([(RET | K, 0, 0, rng.randrange(1 << 32)), (RET | RA, 0, 0, 0)])

def rand_prog(rng, n, **kw):
    prog = [rand_insn(rng, n - i - 1, **kw) for i in range(n - 1)]
    prog.append(rng.choice([(RET | K, 0, 0, rng.randrange(1, 1 << 32)), (RET | RA, 0, 0, 0)]))
    return prog

def break_prog(rng, prog):
    """a copy of a valid program that breaks one rule, or is not decodable"""
    p = list(prog)
    n = len(p)
    i = rng.randrange(n)
    how = rng.randrange(9)
    if how == 0:
        p[i] = (JMP | JA, 0, 0, n - i - 1 + rng.randrange(3))
    elif how == 1:
        p[i] = (JMP | JEQ | K, n - i - 1 + rng.randrange(2), 0, 5)
    elif how == 2:
        p[i] = (JMP | JGT | X, 0, rng.choice([n - i - 1, 256, 300]), 0)
    elif how == 3:
        p.append((LD | W | IMM, 0, 0, 1))
    elif how == 4:
        p[i] = (rng.choice((LD | W | MEM, LDX | W | MEM, ST, STX)), 0, 0, rng.choice([16, 17, 255, M32]))
    elif how == 5:
        p[i] = (ALU | rng.choice((DIV, MOD)) | K, 0, 0, 0)
    elif how == 6:
        p[i] = (rng.choice([0x0E, 0x08, 0xB4, 0xC4, 0x86, 0x25 | 0x80, 0x10000 | 6, rng.randrange(65536)]), 0, 0, 1)
    elif how == 7:
        p = []
    else:
        p = p + [(RET | K, 0, 0, 0)] * (4097 - n)
    return p

def rand_packet(rng):
    n = rng.choice([0, 1, 3, 14, 20]) if rng.random() < 0.2 else rng.randrange(34, 100)
    return [rng.randrange(256) for _ in range(n)]

# seccomp filters

def rand_ret_value(rng, kernel):
    if kernel:
        return rng.choice([ALLOW, ERRNO | rng.randrange(1, 4096)])
    return rng.choice([ALLOW, ALLOW, ERRNO | rng.randrange(65536), TRAP | rng.randrange(65536), TRACE | rng.randrange(65536),
                       KILL_PROCESS, KILL_THREAD, USER_NOTIF, LOG, rng.randrange(1 << 32), ERRNO | 0x10000 | rng.randrange(65536)])

SC_OFFSETS = [0, 4, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60]

def rand_sc_insn(rng, r, kernel):
    """a random seccomp instruction (never BPF_MOD, which seccomp refuses)"""
    kind = rng.randrange(20)
    if kind < 5:
        return (LD | W | ABS, 0, 0, rng.choice(SC_OFFSETS if kernel else SC_OFFSETS + [8, 12]))
    if kind < 6:
        return rng.choice([(LD | W | IMM, 0, 0, rand_k(rng)), (LD | W | LEN, 0, 0, 0), (LDX | W | IMM, 0, 0, rand_k(rng)), (LDX | W | LEN, 0, 0, 0)])
    if kind < 8:
        return (rng.choice((LD | W | MEM, LDX | W | MEM, ST, STX)), 0, 0, rng.randrange(4))
    if kind < 11:
        op = rng.choice((ADD, SUB, MUL, DIV, OR, AND, LSH, RSH, XOR, NEG))
        if op == NEG:
            return (ALU | NEG, 0, 0, 0)
        src = K if kernel and op in (DIV, MOD, LSH, RSH) else rng.choice((K, X))
        k = rand_k(rng) if src == K else 0
        if op in (DIV, MOD) and src == K and k == 0:
            k = 7
        if op in (LSH, RSH) and src == K:
            k = rng.randrange(32)
        return (ALU | op | src, 0, 0, k)
    if kind < 17:
        if rng.random() < 0.1:
            return (JMP | JA, 0, 0, rng.randrange(r))
        op = rng.choice((JEQ, JGT, JGE, JSET))
        src = rng.choice((K, X))
        k = rand_k(rng) if src == K else 0
        return (JMP | op | src, rng.randrange(min(r, 256)), rng.randrange(min(r, 256)), k)
    if kind < 19:
        return (MISC | rng.choice((TAX, TXA)), 0, 0, 0)
    if kernel:
        return (RET | K, 0, 0, rand_ret_value(rng, True))
    return rng.choice([(RET | K, 0, 0, rand_ret_value(rng, False)), (RET | RA, 0, 0, 0)])

TEST_CALLS = [110, 111, 102, 104, 107, 108]  # getppid getpgrp getuid getgid geteuid getegid (x86-64)
AUDIT_ARCH_X86_64 = 0xC000003E

def rand_sc_filter(rng, kernel):
    n = rng.randrange(2, 24)
    body = [(LD | W | IMM, 0, 0, rand_k(rng))] + [(ST, 0, 0, j) for j in range(4)] if kernel else []
    body += [rand_sc_insn(rng, n - i - 1, kernel) for i in range(n - 1)]
    body.append((RET | K, 0, 0, rand_ret_value(rng, kernel)) if kernel or rng.random() < 0.8 else (RET | RA, 0, 0, 0))
    if not kernel:
        if rng.random() < 0.85:
            body = [(LD | W | IMM, 0, 0, rand_k(rng))] + [(ST, 0, 0, j) for j in range(4)] + body
        return body
    # let every other system call through, so the child can report and exit
    m = len(TEST_CALLS)
    pro = [(LD | W | ABS, 0, 0, 0)] + [(JMP | JEQ | K, m - i, 0, nr) for i, nr in enumerate(TEST_CALLS)] + [(RET | K, 0, 0, ALLOW)]
    return pro + body

def rand_args(rng):
    return [rng.choice([0, 1, 2, 7, 0xFFFFFFFF, 1 << 32, (1 << 64) - 1, rng.randrange(1 << 64), rng.randrange(256)]) for _ in range(6)]

def rand_call(rng, kernel):
    if kernel:
        return (rng.choice(TEST_CALLS), AUDIT_ARCH_X86_64, 0, rand_args(rng))
    return (rng.choice(TEST_CALLS + [0, 1, 59, 231, rng.randrange(1 << 32)]), rng.choice([AUDIT_ARCH_X86_64, 0x40000003, 0xC00000B7]), rng.randrange(1 << 64), rand_args(rng))

# ------------------------------------------------------------- the kernel

PR_SET_NO_NEW_PRIVS, PR_SET_SECCOMP, SECCOMP_MODE_FILTER = 38, 22, 2

class SockFilter(ctypes.Structure):
    _fields_ = [("code", ctypes.c_ushort), ("jt", ctypes.c_ubyte), ("jf", ctypes.c_ubyte), ("k", ctypes.c_uint)]

class SockFprog(ctypes.Structure):
    _fields_ = [("len", ctypes.c_ushort), ("filter", ctypes.POINTER(SockFilter))]

def libc():
    c = ctypes.CDLL(None, use_errno=True)
    c.prctl.argtypes = [ctypes.c_int, ctypes.c_ulong, ctypes.c_void_p, ctypes.c_ulong, ctypes.c_ulong]
    c.prctl.restype = ctypes.c_int
    c.syscall.argtypes = [ctypes.c_long] * 7
    c.syscall.restype = ctypes.c_long
    return c

def in_child(job):
    """run job() in a forked child; its bytes come back, or None if it died"""
    r, w = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(r)
        try:
            out = job()
        except BaseException:
            out = b"exception"
        os.write(w, out)
        os._exit(0)
    os.close(w)
    data = b""
    while True:
        chunk = os.read(r, 65536)
        if not chunk:
            break
        data += chunk
    os.close(r)
    _, status = os.waitpid(pid, 0)
    return data if os.WIFEXITED(status) else None

def install(c, prog):
    arr = (SockFilter * max(len(prog), 1))(*[SockFilter(code & 0xFFFF, jt, jf, k) for code, jt, jf, k in prog])
    fp = SockFprog(len(prog), arr)
    if c.prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, ctypes.cast(ctypes.pointer(fp), ctypes.c_void_p), 0, 0) != 0:
        return ctypes.get_errno()
    return 0

def kernel_job(filters, calls):
    def job():
        c = libc()
        real = [c.syscall(nr, *([0] * 6)) for nr, _, _, _ in calls]
        if c.prctl(PR_SET_NO_NEW_PRIVS, 1, None, 0, 0) != 0:
            return b"noprivs %d" % ctypes.get_errno()
        for f in filters:
            e = install(c, f)
            if e:
                return b"install %d" % e
        out = []
        for (nr, _, _, args), rv in zip(calls, real):
            ctypes.set_errno(0)
            v = c.syscall(nr, *[a if a < 1 << 63 else a - (1 << 64) for a in args])
            e = ctypes.get_errno()
            out.append("ALLOW" if v == rv and v != -1 else "ERRNO(%d)" % e if v == -1 else "?%d" % v)
        return " ".join(out).encode()
    return in_child(job)

def kernel_accepts(prog):
    def job():
        c = libc()
        if c.prctl(PR_SET_NO_NEW_PRIVS, 1, None, 0, 0) != 0:
            return b"noprivs"
        return b"ok" if install(c, prog) == 0 else b"refused"
    return in_child(job)

def kernel_available():
    if platform.system() != "Linux" or platform.machine() != "x86_64" or not hasattr(os, "fork"):
        return "not Linux on x86-64"
    got = kernel_job([[(RET | K, 0, 0, ALLOW)]], [(110, AUDIT_ARCH_X86_64, 0, [0] * 6)])
    if got != b"ALLOW":
        return "installing a filter is not permitted (%r)" % got
    return None

# -------------------------------------------------------------- the cases

def raw(prog):
    return "[" + ", ".join("I.BpfRaw{%d, %d, %d, %d}" % p for p in prog) + "]"

def octets(data):
    return "B.Octets.of_list([" + ", ".join(map(str, data)) + "])"

def w64(v):
    return "W.W64.from_parts(%d, %d)" % (v >> 32, v & M32)

def sdata(call):
    nr, arch, ip, args = call
    return "S.SeccompData{%d, %d, %s}" % (nr, arch, ", ".join(w64(v) for v in [ip] + args))

def answer(f):
    try:
        return f()
    except Err as e:
        return "error: %s" % e

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []

    def case(bend, want):
        lines.append('    IO.print("%d " ++ %s)' % (len(lines), bend))
        expect.append("%d %s" % (len(expect), want))

    # valid packet filters
    for _ in range(260):
        prog = rand_prog(rng, rng.randrange(1, 30))
        try:
            mem_init(prog)
        except Err:
            # write the slots it reads first (A is 0), most of the time
            reads = sorted({k for code, _, _, k in prog if code in (LD | W | MEM, LDX | W | MEM)})
            prog = [(ST, 0, 0, k) for k in reads] + prog
        data = rand_packet(rng)
        validate(prog)
        case("t_packet(%s, %s)" % (octets(data), raw(prog)), str(run(prog, data)))
    # programs that break a rule, or do not decode
    for _ in range(90):
        prog = break_prog(rng, rand_prog(rng, rng.randrange(1, 12)))
        if len(prog) > 200:
            continue
        def check():
            decode(prog)
            validate(prog)
            return "ok"
        case("t_prepared(%s)" % raw(prog), answer(check))
    # unvalidated runs: what an invalid program does
    for _ in range(40):
        prog = break_prog(rng, rand_prog(rng, rng.randrange(1, 12)))
        if any(code not in CODES for code, _, _, _ in prog) or len(prog) > 200:
            continue
        data = rand_packet(rng)
        case("t_unchecked(%s, %s)" % (octets(data), raw(prog)), answer(lambda: str(run(prog, data))))
    # seccomp filters, one at a time
    for _ in range(150):
        f = rand_sc_filter(rng, False)
        call = rand_call(rng, False)
        def one():
            install_all([f])
            return show_action(seccomp_run(f, seccomp_bytes(*call)))
        case("t_filter(%s, %s)" % (raw(f), sdata(call)), answer(one))
    # stacks of filters
    kernel_cases = []
    for i in range(130):
        kernel = i >= 50
        fs = [rand_sc_filter(rng, kernel) for _ in range(rng.randrange(1, 4))]
        calls = [rand_call(rng, kernel) for _ in range(4 if kernel else 1)]
        for call in calls:
            def stack():
                st = install_all(fs)
                return show_action(combine([seccomp_run(f, seccomp_bytes(*call)) for f in st]))
            case("t_stack([%s], %s)" % (", ".join(raw(f) for f in fs), sdata(call)), answer(stack))
        if kernel:
            kernel_cases.append((fs, calls, [combine([seccomp_run(f, seccomp_bytes(*c)) for f in reversed(fs)]) for c in calls]))
    # seccomp validation, also against the kernel
    refusals = []
    for i in range(60):
        f = rand_sc_filter(rng, True)
        if i % 4 >= 2:
            f = break_prog(rng, f)
        if i % 4 == 1 or i % 4 >= 2 and rng.random() < 0.3 and f:
            j = rng.randrange(len(f))
            f[j] = rng.choice([(ALU | MOD | K, 0, 0, 3), (ALU | MOD | X, 0, 0, 0), (LD | H | ABS, 0, 0, 0), (LD | B | ABS, 0, 0, 4), (LD | W | ABS, 0, 0, rng.choice([2, 64, 65, 1000])), (LD | W | IND, 0, 0, 0), (LDX | B | MSH, 0, 0, 0)])
        def chk():
            install_all([f])
            return "ok"
        want = answer(chk)
        if len(f) <= 200:
            case("t_installed(%s)" % raw(f), want)
        # the kernel takes 16-bit opcodes and 8-bit offsets
        if all(code < 65536 and jt < 256 and jf < 256 for code, jt, jf, _ in f):
            refusals.append((f, want == "ok"))
    # scratch memory after a jump (unreached: allowed) and after a return
    # (counted as reached from it: refused)
    for f in ([(LD | W | IMM, 0, 0, 0), (ST, 0, 0, 0), (JMP | JA, 0, 0, 1), (LD | W | MEM, 0, 0, 1), (RET | K, 0, 0, ALLOW)],
              [(LD | W | IMM, 0, 0, 0), (JMP | JEQ | K, 1, 1, 0), (LD | W | MEM, 0, 0, 1), (RET | K, 0, 0, ALLOW)],
              [(LD | W | IMM, 0, 0, 0), (RET | K, 0, 0, ALLOW), (LD | W | MEM, 0, 0, 1), (RET | K, 0, 0, ALLOW)]):
        def chk():
            install_all([f])
            return "ok"
        want = answer(chk)
        case("t_installed(%s)" % raw(f), want)
        refusals.append((f, want == "ok"))
    # scratch memory: filters with some of their first stores removed, so
    # that some reads come before writes on some paths
    for i in range(120):
        f = rand_sc_filter(rng, True)
        start = len(TEST_CALLS) + 3
        for j in range(start, start + 4):
            if rng.random() < 0.5:
                f[j] = (MISC | TAX, 0, 0, 0)
        def chk():
            install_all([f])
            return "ok"
        want = answer(chk)
        case("t_installed(%s)" % raw(f), want)
        refusals.append((f, want == "ok"))

    with open(os.path.join(here, "cases.bend"), "w") as out:
        out.write(PRELUDE)
        # one long do block is too deep for the compiler: 40 cases a part
        parts = [lines[i:i + 40] for i in range(0, len(lines), 40)]
        for j, part in enumerate(parts):
            out.write("def part%d() -> IO(Unit):\n  do IO<Unit>:\n" % j + "\n".join(part) + "\n\n")
        out.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join("    part%d()" % j for j in range(len(parts))) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as out:
        out.write("\n".join(expect) + "\n")
    print(len(expect), "cases")

    why = kernel_available()
    if why:
        print("kernel: skipped, " + why)
        sys.exit(3)
    bad = 0
    for fs, calls, want in kernel_cases:
        got = kernel_job(fs, calls)
        want_s = " ".join(show_action(a) for a in want)
        if got is None or got.decode() != want_s:
            bad += 1
            print("kernel disagrees: want %s, got %r, filters %r, calls %r" % (want_s, got, fs, calls))
    for f, ok in refusals:
        got = kernel_accepts(f)
        if got != (b"ok" if ok else b"refused"):
            bad += 1
            print("kernel %r a filter the model %s: %r" % (got, "accepts" if ok else "refuses", f))
    if bad:
        sys.exit(1)
    print("kernel: %d stacked-filter cases (%d system calls) and %d validation cases agree" % (len(kernel_cases), sum(len(c) for _, c, _ in kernel_cases), len(refusals)))

PRELUDE = '''import Base
import ../../bytes/bytes.bend as B
import ../../word64/word64.bend as W
import ../insn.bend as I
import ../validate.bend as V
import ../bpf.bend as R
import ../seccomp.bend as S

def t_show(r: Result<&2, &2, I.BpfError, U32>) -> String:
  match r:
    case Fail{e}:
      "error: " ++ I.BpfError.show(e)
    case Done{v}:
      U32.show(v)

def t_show_act(r: Result<&2, &2, I.BpfError, S.SeccompAction>) -> String:
  match r:
    case Fail{e}:
      "error: " ++ I.BpfError.show(e)
    case Done{a}:
      S.SeccompAction.show(a)

def t_packet.go(o: B.Octets, p: Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>) -> String:
  match p:
    case Fail{e}:
      "error: " ++ I.BpfError.show(e)
    case Done{ops}:
      t_show(R.bpf_run(R.bpf_packet(o), ops))

# decode, validate and run
def t_packet(o: B.Octets, rs: List<&2, I.BpfRaw>) -> String:
  t_packet.go(o, V.bpf_prepare(V.bpf_maxinsns(), rs))

def t_prepared.go(p: Result<&2, &2, I.BpfError, List<&2, I.BpfOp>>) -> String:
  match p:
    case Fail{e}:
      "error: " ++ I.BpfError.show(e)
    case Done{ops}:
      "ok"

def t_prepared(rs: List<&2, I.BpfRaw>) -> String:
  t_prepared.go(V.bpf_prepare(V.bpf_maxinsns(), rs))

# decode and run, without validating
def t_unchecked(o: B.Octets, rs: List<&2, I.BpfRaw>) -> String:
  t_packet.go(o, I.bpf_decode(rs))

def t_install.go(s: Result<&2, &2, I.BpfError, List<&2, List<&2, I.BpfOp>>>, rs: List<&2, I.BpfRaw>) -> Result<&2, &2, I.BpfError, List<&2, List<&2, I.BpfOp>>>:
  match s:
    case Fail{e}:
      Fail{e}
    case Done{st}:
      S.seccomp_install(S.seccomp_limits(), st, rs)

# install each filter, the oldest first
def t_install(fs: List<&2, List<&2, I.BpfRaw>>, s: Result<&2, &2, I.BpfError, List<&2, List<&2, I.BpfOp>>>) -> Result<&2, &2, I.BpfError, List<&2, List<&2, I.BpfOp>>>:
  match fs:
    case Nil{}:
      s
    case Con{f, t}:
      t_install(t, t_install.go(s, f))

def t_stack.go(s: Result<&2, &2, I.BpfError, List<&2, List<&2, I.BpfOp>>>, d: S.SeccompData) -> String:
  match s:
    case Fail{e}:
      "error: " ++ I.BpfError.show(e)
    case Done{st}:
      t_show_act(S.seccomp_eval(st, S.seccomp_order(), d))

def t_stack(fs: List<&2, List<&2, I.BpfRaw>>, d: S.SeccompData) -> String:
  t_stack.go(t_install(fs, Done{[]}), d)

def t_filter(f: List<&2, I.BpfRaw>, d: S.SeccompData) -> String:
  t_stack([f], d)

def t_installed.go(s: Result<&2, &2, I.BpfError, List<&2, List<&2, I.BpfOp>>>) -> String:
  match s:
    case Fail{e}:
      "error: " ++ I.BpfError.show(e)
    case Done{st}:
      "ok"

def t_installed(f: List<&2, I.BpfRaw>) -> String:
  t_installed.go(t_install([f], Done{[]}))

'''

main()
