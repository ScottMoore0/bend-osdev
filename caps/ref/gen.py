#!/usr/bin/env python3
"""Differential test cases for bend-osdev-caps.

Writes ref/cases.bend (a Bend program printing the result of each case) and
ref/expected.txt (the same results from an independent Python model of the
rules in capabilities(7), execve(2), capset(2) and prctl(2), written here
from those pages):
  * execve on random credentials and files (root and non-root, set-user-ID,
    set-group-ID, file capabilities with and without the effective bit,
    SECBIT_NOROOT, ignored set-ID bits, file capabilities off);
  * capset, PR_CAPBSET_DROP, PR_CAP_AMBIENT_RAISE and PR_CAP_AMBIENT_LOWER
    on random credentials and requests;
  * the capability names, against capsh --decode (libcap's tool) when it is
    installed.
The cases include states that break the invariants, so the model is
compared on every input the Bend code accepts, not only on reachable ones.
"""
import glob, os, random, shutil, subprocess, sys

NCAP = 41
FULL = (1 << NCAP) - 1
SETPCAP = 8
NAMES = ["chown", "dac_override", "dac_read_search", "fowner", "fsetid", "kill", "setgid", "setuid", "setpcap",
         "linux_immutable", "net_bind_service", "net_broadcast", "net_admin", "net_raw", "ipc_lock", "ipc_owner",
         "sys_module", "sys_rawio", "sys_chroot", "sys_ptrace", "sys_pacct", "sys_admin", "sys_boot", "sys_nice",
         "sys_resource", "sys_time", "sys_tty_config", "mknod", "lease", "audit_write", "audit_control", "setfcap",
         "mac_override", "mac_admin", "syslog", "wake_alarm", "block_suspend", "audit_read", "perfmon", "bpf",
         "checkpoint_restore"]

def bit(k):
    return 1 << k

def sub(a, b):
    return a & ~b == 0

# The model. A credential is (ruid, euid, suid, noroot, no_ambient_raise,
# (P, I, E, B, A)); a file is (owner, setuid, setgid, caps) with caps None or
# (permitted, inheritable, effective); a kernel is (last_cap, file_caps).

def execve(kern, cred, f, ign):
    ruid, euid, suid, noroot, nar, (P, I, E, B, A) = cred
    owner, su, sg, fcaps = f
    last, file_caps_on = kern
    # execve(2): the set-ID bits and file capabilities are ignored with
    # no_new_privs, nosuid or ptrace; file capabilities also with no_file_caps
    neweuid = owner if (su and not ign) else euid
    fc = None if (ign or not file_caps_on) else fcaps
    privileged = fc is not None or (not ign and (su or sg))
    # capabilities(7), "Capabilities and execution of programs by root"
    rootish = not noroot and (ruid == 0 or neweuid == 0)
    exception = fc is not None and ruid != 0 and neweuid == 0
    if rootish and not exception:
        fp, fi = FULL, FULL
    elif fc is not None:
        fp, fi = fc[0], fc[1]
    else:
        fp, fi = 0, 0
    feff = (not noroot and neweuid == 0) or (fc is not None and fc[2])
    # "Transformation of capabilities during execve()"
    A2 = 0 if privileged else A
    P2 = (I & fi) | (fp & B) | A2
    E2 = P2 if feff else A2
    # "Safety checking for capability-dumb binaries"
    if fc is not None and fc[2] and not sub(fc[0], P2):
        return ("err", "dumb")
    return ("ok", (ruid, neweuid, neweuid, noroot, nar, (P2, I, E2, B, A2)))

def capset(cred, e, p, i):
    ruid, euid, suid, noroot, nar, (P, I, E, B, A) = cred
    if not sub(p, P):
        return ("err", "grows")
    if not sub(e, p):
        return ("err", "eff")
    if not sub(i, I | B):
        return ("err", "bounded")
    if not (E & bit(SETPCAP)) and not sub(i, I | P):
        return ("err", "inhperm")
    return ("ok", (ruid, euid, suid, noroot, nar, (p, i, e, B, A & p & i)))

def valid_cap(kern, x):
    return x < NCAP and x <= kern[0]

def bset_drop(kern, cred, x):
    ruid, euid, suid, noroot, nar, (P, I, E, B, A) = cred
    if not valid_cap(kern, x):
        return ("err", "inval")
    if not E & bit(SETPCAP):
        return ("err", "nosetpcap")
    return ("ok", (ruid, euid, suid, noroot, nar, (P, I, E, B & ~bit(x), A)))

def amb_raise(kern, cred, x):
    ruid, euid, suid, noroot, nar, (P, I, E, B, A) = cred
    if not valid_cap(kern, x):
        return ("err", "inval")
    if nar:
        return ("err", "locked")
    if not (P & bit(x) and I & bit(x)):
        return ("err", "notallowed")
    return ("ok", (ruid, euid, suid, noroot, nar, (P, I, E, B, A | bit(x))))

def amb_lower(kern, cred, x):
    ruid, euid, suid, noroot, nar, (P, I, E, B, A) = cred
    if not valid_cap(kern, x):
        return ("err", "inval")
    return ("ok", (ruid, euid, suid, noroot, nar, (P, I, E, B, A & ~bit(x))))

def show(r):
    if r[0] == "err":
        return "err " + r[1]
    ruid, euid, suid, noroot, nar, sets = r[1]
    return "ok %d %d %d " % (ruid, euid, suid) + " ".join("%016x" % s for s in sets)

# Random inputs: sets drawn from a few capabilities so that they overlap

def rset(rng):
    pick = rng.random()
    if pick < 0.1:
        return 0
    if pick < 0.2:
        return FULL
    pool = rng.sample(range(NCAP), 6) + [SETPCAP, 13, 21]
    s = 0
    for k in pool:
        if rng.random() < 0.45:
            s |= bit(k)
    return s

def rcred(rng, valid):
    P, I, B = rset(rng), rset(rng), rng.choice([FULL, rset(rng)])
    E = P & rset(rng) if valid else rset(rng)
    A = P & I & rset(rng) if valid else rset(rng)
    ruid = rng.choice([0, 1000])
    euid = rng.choice([ruid, 0, 1000])
    return (ruid, euid, euid, rng.random() < 0.15, rng.random() < 0.15, (P, I, E, B, A))

def rfile(rng):
    caps = None
    if rng.random() < 0.5:
        caps = (rset(rng), rset(rng), rng.random() < 0.5)
    return (rng.choice([0, 1000]), rng.random() < 0.3, rng.random() < 0.2, caps)

def rkern(rng):
    return (rng.choice([40, 40, 40, 38]), rng.random() < 0.85)

def bset(s):
    return "C.CapSet.from_list([%s])" % ", ".join(str(k) for k in range(NCAP) if s >> k & 1)

def bbool(b):
    return "True{}" if b else "False{}"

def bcred(c):
    ruid, euid, suid, noroot, nar, sets = c
    return "C.CapCred{%d, %d, %d, %s, %s, C.CapState{%s}}" % (ruid, euid, suid, bbool(noroot), bbool(nar), ", ".join(bset(s) for s in sets))

def bfile(f):
    owner, su, sg, caps = f
    bc = "None{}" if caps is None else "Some{C.CapFileSets{%s, %s, %s}}" % (bset(caps[0]), bset(caps[1]), bbool(caps[2]))
    return "C.CapFile{%d, %s, %s, %s}" % (owner, bbool(su), bbool(sg), bc)

def bkern(k):
    return "C.CapsKernel{%d, %s}" % (k[0], bbool(k[1]))

PRELUDE = '''import Base
import ../caps.bend as C
import ../exec.bend as E
import ../adjust.bend as A

def err(e: C.CapsError) -> String:
  match e:
    case C.CapsInvalidCap{}:
      "inval"
    case C.CapsPermittedGrows{}:
      "grows"
    case C.CapsEffectiveNotPermitted{}:
      "eff"
    case C.CapsInheritableNotBounded{}:
      "bounded"
    case C.CapsInheritableNotPermitted{}:
      "inhperm"
    case C.CapsNoSetpcap{}:
      "nosetpcap"
    case C.CapsAmbientRaiseLocked{}:
      "locked"
    case C.CapsAmbientNotAllowed{}:
      "notallowed"
    case C.CapsCapabilityDumb{}:
      "dumb"

def show(r: Result<&2, &2, C.CapsError, C.CapCred>) -> String:
  match r:
    case Fail{e}:
      "err " ++ err(e)
    case Done{C.CapCred{ru, eu, sv, nr, na, C.CapState{p, i, e, b, a}}}:
      "ok " ++ U32.show(ru) ++ " " ++ U32.show(eu) ++ " " ++ U32.show(sv) ++ " " ++ C.CapSet.show(p) ++ " " ++ C.CapSet.show(i) ++ " " ++ C.CapSet.show(e) ++ " " ++ C.CapSet.show(b) ++ " " ++ C.CapSet.show(a)

def name(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      "none"
    case Some{s}:
      s
'''

def capsh_names():
    """capsh --decode for each bit, or None when capsh is not installed."""
    if not shutil.which("capsh"):
        return None
    out = []
    for k in range(NCAP):
        r = subprocess.run(["capsh", "--decode=%x" % bit(k)], capture_output=True, text=True)
        out.append(r.stdout.strip().split("=", 1)[1])
    return out

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []
    def case(tag, call, result):
        lines.append('    IO.print("%s " ++ show(%s))' % (tag, call))
        expect.append("%s %s" % (tag, show(result)))
    for n in range(300):
        k, c, f, ign = rkern(rng), rcred(rng, rng.random() < 0.7), rfile(rng), rng.random() < 0.15
        r = execve(k, c, f, ign)
        if r[0] == "ok":  # the model's own sets obey the invariants proved in LAWS.bend
            P, I, E, B, A = r[1][5]
            assert sub(E, P) and sub(A, P) and B == c[5][3] and sub(P, B | c[5][1] | c[5][4])
        case("execve %d" % n, "E.Caps.execve(%s, %s, %s, %s)" % (bkern(k), bcred(c), bfile(f), bbool(ign)), r)
    for n in range(150):
        c = rcred(rng, rng.random() < 0.7)
        P = c[5][0]
        # requests that mostly pass the permitted rule, so the later rules are reached
        p = P & rset(rng) if rng.random() < 0.8 else rset(rng)
        e = p & rset(rng) if rng.random() < 0.8 else rset(rng)
        i = (c[5][1] | (P & rset(rng))) & rng.choice([FULL, c[5][3] | c[5][1]]) if rng.random() < 0.6 else rset(rng)
        case("capset %d" % n, "A.Caps.capset(%s, %s, %s, %s)" % (bcred(c), bset(e), bset(p), bset(i)), capset(c, e, p, i))
    for n in range(80):
        k, c = rkern(rng), rcred(rng, True)
        if rng.random() < 0.6:  # give it CAP_SETPCAP, so that most drops succeed
            P, I, E, B, A = c[5]
            c = c[:5] + ((P | bit(SETPCAP), I, E | bit(SETPCAP), B, A),)
        x = rng.randrange(NCAP) if rng.random() < 0.7 else rng.choice([SETPCAP, 39, 40, 41, 63])
        case("drop %d" % n, "A.Caps.bset_drop(%s, %s, %d)" % (bkern(k), bcred(c), x), bset_drop(k, c, x))
    for n in range(80):
        k, c = rkern(rng), rcred(rng, True)
        both = [j for j in range(NCAP) if c[5][0] & c[5][1] & bit(j)]
        if both and rng.random() < 0.6:  # mostly a capability that may be raised
            x = rng.choice(both)
        else:
            x = rng.choice([rng.randrange(NCAP), 13, 21, 39, 41])
        case("raise %d" % n, "A.Caps.ambient_raise(%s, %s, %d)" % (bkern(k), bcred(c), x), amb_raise(k, c, x))
    for n in range(60):
        k, c = rkern(rng), rcred(rng, True)
        x = rng.randrange(NCAP) if rng.random() < 0.85 else 41
        case("lower %d" % n, "A.Caps.ambient_lower(%s, %s, %d)" % (bkern(k), bcred(c), x), amb_lower(k, c, x))
    # the kernel's own text form of this process's sets (/proc/self/status)
    try:
        with open("/proc/self/status") as st:
            for ln in st:
                if ln.startswith("Cap") and ":" in ln:
                    key, val = ln.split(":")
                    val = val.strip()
                    if int(val, 16) >> NCAP == 0:
                        lines.append('    IO.print("status %s " ++ C.CapSet.show(%s))' % (key, bset(int(val, 16))))
                        expect.append("status %s %s" % (key, val))
    except OSError:
        pass
    decoded = capsh_names()
    for k in range(NCAP + 1):
        want = ("CAP_" + NAMES[k].upper()) if k < NCAP else "none"
        if decoded is not None and k < NCAP:
            assert decoded[k] == "cap_" + NAMES[k], "the name table disagrees with capsh: %d %s" % (k, decoded[k])
        lines.append('    IO.print("name %d " ++ name(C.Cap.name(%d)))' % (k, k))
        expect.append("name %d %s" % (k, want))
    # The cases in files of FILE cases (cases-00.bend, ...), each in parts of
    # 40 so that no do block is too deep. The native build specialises each
    # operation at every call site: one file of all the cases took clang
    # about 3 GB.
    for old in glob.glob(os.path.join(here, "cases-*.bend")):
        os.remove(old)
    FILE = int(os.environ.get("CAPS_FILE", "120"))
    for fi, j0 in enumerate(range(0, len(lines), FILE)):
        chunk = lines[j0:j0 + FILE]
        with open(os.path.join(here, "cases-%02d.bend" % fi), "w") as f:
            f.write(PRELUDE)
            parts = [chunk[j:j + 40] for j in range(0, len(chunk), 40)]
            for j, part in enumerate(parts):
                f.write("\ndef part%d() -> IO(Unit):\n  do IO<Unit>:\n" % j + "\n".join(part) + "\n")
            f.write("\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join("    part%d()" % j for j in range(len(parts))) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases" + ("" if decoded is not None else " (capsh missing: names from the model only)"))

main()
