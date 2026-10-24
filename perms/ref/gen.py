#!/usr/bin/env python3
"""Differential test cases for bend-osdev-perms.

Writes ref/cases.bend (a Bend program printing the result of each case) and
ref/expected.txt (the same results from outside this repository):
  * the kernel: os.access on temporary files and directories this user owns,
    with modes set by os.chmod (the owner class), and on existing system files
    owned by other users and groups (the group and other classes), for every
    request; this user has no capabilities, so no override applies;
  * an independent Python model, written from POSIX.1-2017 (file access
    permissions), path_resolution(7), umask(2) and acl(5), on random inputs:
    mode checks with and without privileges, umask, the ACL check algorithm,
    ACL validity, and sticky-directory deletion.
Every kernel answer is also checked against the model.
"""
import os, random, stat, sys, tempfile

R, W, X = 4, 2, 1

# The model

def class_bits(proc, f):
    uid, gid, groups, privs = proc
    fuid, fgid, mode, is_dir = f
    if uid == fuid:
        return mode >> 6 & 7
    if gid == fgid or fgid in groups:
        return mode >> 3 & 7
    return mode & 7

def granted_by_privs(privs, f):
    override, read_search = privs[0], privs[1]
    fuid, fgid, mode, is_dir = f
    g = 0
    if override:
        g |= R | W
        if is_dir or mode & 0o111:
            g |= X
    if read_search:
        g |= R
        if is_dir:
            g |= X
    return g

def needed(proc, f, req):
    return req & ~granted_by_privs(proc[3], f) & 7

def contains(entry, req):
    return entry & req == req

def access(proc, f, req):
    return contains(class_bits(proc, f), needed(proc, f, req))

def umask_create(mode, umask):
    return mode & 0o7777 & ~(umask & 0o777)

def in_group(proc, g):
    return proc[1] == g or g in proc[2]

def acl_check(acl, proc, f, req):
    """acl(5), ACCESS CHECK ALGORITHM. acl = (uo, users, go, groups, mask, other)."""
    uo, users, go, groups, mask, other = acl
    q = needed(proc, f, req)
    uid = proc[0]
    if uid == f[0]:
        return contains(uo, q)
    for qual, p in users:
        if qual == uid:
            return contains(p, q) and (mask is None or contains(mask, q))
    matching = ([go] if in_group(proc, f[1]) else []) + [p for qual, p in groups if in_group(proc, qual)]
    if in_group(proc, f[1]) or any(in_group(proc, qual) for qual, p in groups):
        if mask is not None:
            return contains(mask, q) and any(contains(p, q) for p in matching)
        return contains(go, q)
    return contains(other, q)

TAGS = ["uo", "user", "go", "group", "mask", "other"]

def acl_parse(entries):
    """acl(5), VALID ACLs: the first error in list order, then the missing entries."""
    base = {}
    users, groups = [], []
    for tag, qual, p in entries:
        if tag in ("uo", "go", "other", "mask"):
            if tag in base:
                return "dupentry"
            base[tag] = p
        else:
            lst = users if tag == "user" else groups
            if any(q == qual for q, _ in lst):
                return "dupqual"
            lst.append((qual, p))
    for tag, err in (("uo", "nouo"), ("go", "nogo"), ("other", "noother")):
        if tag not in base:
            return err
    if (users or groups) and "mask" not in base:
        return "maskreq"
    return ("ok", (base["uo"], users, base["go"], groups, base.get("mask"), base["other"]))

def may_delete(proc, d, f):
    sticky = d[2] & 0o1000
    ok = (not sticky) or proc[0] == f[0] or proc[0] == d[0] or proc[3][2]
    return bool(ok) and access(proc, d, W | X)

# Bend literals

def bb(b):
    return "True{}" if b else "False{}"

def brwx(v):
    return "M.PermsRwx{%s, %s, %s}" % (bb(v & R), bb(v & W), bb(v & X))

def bproc(p):
    uid, gid, groups, privs = p
    return "P.PermsProc{%d, %d, [%s], P.PermsPrivs{%s}}" % (uid, gid, ", ".join(str(g) for g in groups), ", ".join(bb(x) for x in privs))

def bfile(f):
    return "P.PermsFile{%d, %d, %d, %s}" % (f[0], f[1], f[2], bb(f[3]))

def bids(xs):
    return "[" + ", ".join("A.PermsAclId{%d, %s}" % (q, brwx(p)) for q, p in xs) + "]"

def bacl(a):
    uo, users, go, groups, mask, other = a
    bm = "None{}" if mask is None else "Some{%s}" % brwx(mask)
    return "A.PermsAcl{%s, %s, %s, %s, %s, %s}" % (brwx(uo), bids(users), brwx(go), bids(groups), bm, brwx(other))

BTAG = {"uo": "A.PermsAclUserObj{}", "user": "A.PermsAclUser{}", "go": "A.PermsAclGroupObj{}", "group": "A.PermsAclGroup{}", "mask": "A.PermsAclMask{}", "other": "A.PermsAclOther{}"}

def bentries(es):
    return "[" + ", ".join("A.PermsAclEntry{%s, %d, %s}" % (BTAG[t], q, brwx(p)) for t, q, p in es) + "]"

PRELUDE = '''import Base
import ../mode.bend as M
import ../perms.bend as P
import ../acl.bend as A
import ../sticky.bend as S

def yn(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def parsed(r: Result<&2, &2, A.PermsError, A.PermsAcl>) -> String:
  match r:
    case Done{a}:
      "ok " ++ U32.show(A.PermsAcl.to_mode(a, 0))
    case Fail{A.PermsAclNoUserObj{}}:
      "nouo"
    case Fail{A.PermsAclNoGroupObj{}}:
      "nogo"
    case Fail{A.PermsAclNoOther{}}:
      "noother"
    case Fail{A.PermsAclDuplicateEntry{}}:
      "dupentry"
    case Fail{A.PermsAclDuplicateQualifier{}}:
      "dupqual"
    case Fail{A.PermsAclMaskRequired{}}:
      "maskreq"
'''

def acl_to_mode(a):
    uo, users, go, groups, mask, other = a
    return uo << 6 | (go if mask is None else mask) << 3 | other

def yn(b):
    return "yes" if b else "no"

def kernel_cases():
    """(proc, file, request, answer) from os.access, for this user."""
    if not hasattr(os, "getuid"):
        return []
    me = (os.getuid(), os.getgid(), sorted(set(os.getgroups()) - {os.getgid()}), (False, False, False))
    out = []
    rng = random.Random(7)
    with tempfile.TemporaryDirectory() as d:
        for k in range(40):
            is_dir = k % 4 == 3
            path = os.path.join(d, "f%d" % k)
            if is_dir:
                os.mkdir(path)
            else:
                open(path, "w").close()
            mode = rng.randrange(0o1000)
            os.chmod(path, mode)
            st = os.stat(path)
            f = (st.st_uid, st.st_gid, stat.S_IMODE(st.st_mode), is_dir)
            for req in range(8):
                out.append((me, f, req, os.access(path, req)))
            os.chmod(path, 0o700)
    # files of other users and groups: skip those with ACLs or on read-only mounts
    for top in ("/etc", "/usr/bin", "/var/log", "/var/lib", "/usr/sbin", "/var/spool", "/var/cache"):
        if not os.path.isdir(top) or not os.access(top, X):
            continue
        try:
            names = sorted(os.listdir(top))[:200]
        except OSError:
            continue
        for name in names:
            path = os.path.join(top, name)
            try:
                st = os.lstat(path)
                if stat.S_ISLNK(st.st_mode) or any(x.startswith("system.posix_acl") for x in os.listxattr(path)):
                    continue
                ro = os.statvfs(path).f_flag & os.ST_RDONLY
            except OSError:
                continue
            if st.st_uid == me[0] and st.st_gid in [me[1]] + me[2]:
                continue
            f = (st.st_uid, st.st_gid, stat.S_IMODE(st.st_mode), stat.S_ISDIR(st.st_mode))
            for req in range(8):
                if ro and req & W:
                    continue
                out.append((me, f, req, os.access(path, req)))
    return out

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []
    def case(tag, call, want):
        lines.append('    IO.print("%s " ++ %s)' % (tag, call))
        expect.append("%s %s" % (tag, want))
    kc = kernel_cases()
    classes = set()
    for n, (proc, f, req, got) in enumerate(kc):
        assert got == access(proc, f, req), ("the model disagrees with the kernel", proc, f, req, got)
        classes.add(("owner" if proc[0] == f[0] else "group" if in_group(proc, f[1]) else "other"))
        case("kernel %d" % n, "yn(P.Perms.access_u32(%s, %s, %d))" % (bproc(proc), bfile(f), req), yn(got))
    ids = [0, 1000, 1001, 1002]
    def rproc():
        privs = tuple(rng.random() < 0.2 for _ in range(3))
        return (rng.choice(ids), rng.choice(ids + [4, 27]), rng.sample([4, 27, 1001, 1002], rng.randrange(3)), privs)
    def rfile():
        return (rng.choice(ids), rng.choice(ids + [4, 27]), rng.randrange(0o10000), rng.random() < 0.3)
    for n in range(300):
        p, f, req = rproc(), rfile(), rng.randrange(8)
        case("mode %d" % n, "yn(P.Perms.access_u32(%s, %s, %d))" % (bproc(p), bfile(f), req), yn(access(p, f, req)))
    for n in range(100):
        mode, um = rng.randrange(1 << 16), rng.randrange(1 << 12)
        case("umask %d" % n, "U32.show(M.Mode.create(%d, %d))" % (mode, um), str(umask_create(mode, um)))
    def racl():
        users = [(q, rng.randrange(8)) for q in rng.sample(ids, rng.randrange(3))]
        groups = [(q, rng.randrange(8)) for q in rng.sample(ids + [4, 27], rng.randrange(3))]
        mask = rng.randrange(8) if (users or groups or rng.random() < 0.3) else None
        return (rng.randrange(8), users, rng.randrange(8), groups, mask, rng.randrange(8))
    for n in range(300):
        a, p, f, req = racl(), rproc(), rfile(), rng.randrange(1, 8)
        case("acl %d" % n, "yn(A.Perms.access_acl(%s, %s, %s, M.PermsRwx.of_u32(%d)))" % (bacl(a), bproc(p), bfile(f), req), yn(acl_check(a, p, f, req)))
    for n in range(150):
        es = []
        for _ in range(rng.randrange(2, 8)):
            t = rng.choice(TAGS + ["uo", "go", "other"])
            es.append((t, rng.choice([0, 1000, 1001]) if t in ("user", "group") else 0, rng.randrange(8)))
        pick = rng.random()
        if pick < 0.7:  # a well-formed ACL, shuffled, and sometimes broken in one way
            a = racl()
            es = [("uo", 0, a[0]), ("go", 0, a[2]), ("other", 0, a[5])] + [("user", q, p) for q, p in a[1]] + [("group", q, p) for q, p in a[3]] + ([] if a[4] is None else [("mask", 0, a[4])])
            if pick >= 0.35:
                how = rng.randrange(4)
                if how == 0:  # drop the mask (and make sure a named entry needs it)
                    es = [e for e in es if e[0] != "mask"] + [("user", 1002, 7)]
                elif how == 1:  # a second entry for a named user
                    es += [("user", 1001, 5), ("user", 1001, 1), ("mask", 0, 7)]
                elif how == 2:  # drop a base entry
                    gone = rng.choice(["uo", "go", "other"])
                    es = [e for e in es if e[0] != gone]
                else:  # a second named group with the same qualifier
                    es += [("group", 27, 4), ("group", 27, 2)]
            rng.shuffle(es)
        r = acl_parse(es)
        want = r if isinstance(r, str) else "ok %d" % acl_to_mode(r[1])
        case("valid %d" % n, "parsed(A.PermsAcl.of_entries(%s))" % bentries(es), want)
    for n in range(150):
        p, d, f = rproc(), rfile(), rfile()
        d = (d[0], d[1], d[2] | (0o1000 if rng.random() < 0.5 else 0), True)
        case("delete %d" % n, "yn(S.Perms.may_delete(%s, %s, %s))" % (bproc(p), bfile(d), bfile(f)), yn(may_delete(p, d, f)))
    # several programs of at most 1000 cases (cases_0.bend, cases_1.bend, ...),
    # which run.sh runs in order: compiled natively as one program, the 6080
    # cases took clang past 6 GB
    for old in os.listdir(here):
        if old.startswith("cases") and old.endswith(".bend"):
            os.remove(os.path.join(here, old))
    for k, j0 in enumerate(range(0, len(lines), 1000)):
        with open(os.path.join(here, "cases_%d.bend" % k), "w") as f:
            f.write(PRELUDE)
            chunk = lines[j0:j0 + 1000]
            parts = [chunk[j:j + 40] for j in range(0, len(chunk), 40)]
            for j, part in enumerate(parts):
                f.write("\ndef part%d() -> IO(Unit):\n  do IO<Unit>:\n" % j + "\n".join(part) + "\n")
            f.write("\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join("    part%d()" % j for j in range(len(parts))) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases (%d from the kernel, classes: %s)" % (len(kc), ", ".join(sorted(classes)) or "none"))

main()
