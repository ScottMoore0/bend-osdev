#!/usr/bin/env python3
"""Differential test cases for bend-osdev-fdt.

An independent devicetree blob writer and reader, written in Python from the
Devicetree Specification v0.4, chapter 5, shares an author with the package.
dtc and fdtdump (the device-tree-compiler package) are third-party
references, used when installed:

  * build:  random trees; Fdt.build (simple strings block) and Fdt.build_with
    (FdtStringsDedup) must give the bytes this writer gives; with dtc, the
    deduplicated blob must also be the bytes `dtc -I dts -O dtb` writes for
    the same tree;
  * parse:  blobs from this writer (sometimes version 16, with NOPs, gaps
    between blocks, bytes after totalsize), half of them corrupted; Fdt.parse
    must give the tree, or the error, this reader gives;
  * dtc:    random .dts sources compiled by dtc; Fdt.parse must read the tree
    the source describes;
  * values: the typed property decoders against this file's decoders;
  * lookups: paths, aliases and phandles in random trees.

`gen.py SEED` writes cases00.bend, cases01.bend, ..., expected.txt and
trees.txt; `gen.py --post OUTPUT` then hands every blob Fdt.build wrote to
dtc (`-I dtb -O dts`, then back to a blob) and fdtdump, and checks that dtc
reads back the same tree.
"""
import os, random, re, shutil, struct, subprocess, sys, tempfile

MAGIC = 0xD00DFEED
# the case files main writes (cases00.bend, cases01.bend, ...) hold at most
# about this many bytes of cases each
FILE_BYTES = 150000
HERE = os.path.dirname(os.path.abspath(__file__))


def pad4(n):
    return (4 - n % 4) % 4


def be32(v):
    return struct.pack(">I", v & 0xFFFFFFFF)


# A tree is (name: bytes, props: [(name, value)], children: [tree]).

def write(tree, rsv, boot, dedup=False, nops=None, version=17, gaps=(0, 0, 0), tail=b""):
    """A blob: header, reservation block, structure block, strings block.
    nops: a random.Random to sprinkle FDT_NOP tokens with; gaps: zero bytes
    before the reservation, structure and strings blocks (multiples of 8, 4
    and anything); tail: bytes after totalsize."""
    strings, table, st = bytearray(), {}, bytearray()

    def nameoff(k):
        # dedup: a name whose bytes and NUL occur already (also as the tail
        # of a longer name) takes that offset, as dtc does
        if dedup and strings.find(k + b"\0") >= 0:
            return strings.find(k + b"\0")
        table[k] = len(strings)
        strings.extend(k + b"\0")
        return table[k]

    def nop():
        if nops is not None and nops.random() < 0.15:
            st.extend(be32(4))

    def node(n):
        name, props, kids = n
        nop()
        st.extend(be32(1) + name + b"\0" + bytes(pad4(len(name) + 1)))
        for k, v in props:
            nop()
            st.extend(be32(3) + be32(len(v)) + be32(nameoff(k)) + v + bytes(pad4(len(v))))
        for c in kids:
            node(c)
        nop()
        st.extend(be32(2))

    node(tree)
    nop()
    st.extend(be32(9))
    rsvb = b"".join(struct.pack(">QQ", a, s) for a, s in rsv) + bytes(16)
    o_rsv = 40 + gaps[0]
    o_st = o_rsv + len(rsvb) + gaps[1]
    o_str = o_st + len(st) + gaps[2]
    total = o_str + len(strings)
    hdr = struct.pack(">10I", MAGIC, total, o_st, o_str, o_rsv, version, 16, boot, len(strings), len(st))
    out = hdr + bytes(gaps[0]) + rsvb + bytes(gaps[1]) + bytes(st) + bytes(gaps[2]) + bytes(strings)
    assert len(out) == total
    return out + tail


class Bad(Exception):
    pass


def u32at(b, i):
    return struct.unpack(">I", b[i:i + 4])[0]


def read(b, versions="16-17", nop_ok=True, props_first=True):
    """(version, boot, rsv, tree) or raise Bad(error), checking in the order
    the package documents."""
    if len(b) < 4:
        raise Bad("too_short")
    if u32at(b, 0) != MAGIC:
        raise Bad("bad_magic")
    if len(b) < 40:
        raise Bad("too_short")
    _, ts, ost, ostr, orsv, v, lc, boot, sstr, sst = struct.unpack(">10I", b[:40])
    more = {"16-17": v == 16, "17": False, "compat": v >= 16}[versions]
    if not (v == 17 or more):
        raise Bad("bad_version")
    if not (lc <= 17 and lc <= v):
        raise Bad("bad_last_comp")
    if not (40 <= ts <= len(b)):
        raise Bad("bad_total_size")
    if not (orsv % 8 == 0 and 40 <= orsv <= ts):
        raise Bad("bad_rsvmap")
    send = ost + sst if v >= 17 else ost
    if not (ost % 4 == 0 and 40 <= ost and send <= ts):
        raise Bad("bad_struct")
    if not (40 <= ostr and ostr + sstr <= ts):
        raise Bad("bad_strings")
    region = b[:ts]
    rsv, i = [], orsv
    while True:
        if i + 16 > len(region):
            raise Bad("rsv_unterminated")
        a, s = struct.unpack(">QQ", region[i:i + 16])
        i += 16
        if a == 0 and s == 0:
            break
        rsv.append((a, s))
    block = region[ost:ost + sst] if v >= 17 else region[ost:]
    toks = lex(block, strict_end=v >= 17)
    tree = build_tree(toks, region[ostr:ostr + sstr], nop_ok, props_first)
    return v, boot, rsv, tree


def lex(blk, strict_end):
    toks, i = [], 0

    def word():
        nonlocal i
        if i + 4 > len(blk):
            raise Bad("truncated")
        i += 4
        return u32at(blk, i - 4)

    while True:
        tag = word()
        if tag == 1:
            j = blk.find(b"\0", i)
            if j < 0:
                raise Bad("truncated")
            name = blk[i:j]
            i = j + 1 + pad4(j - i + 1)
            if i > len(blk):
                raise Bad("truncated")
            toks.append(("begin", name))
        elif tag == 2:
            toks.append(("end",))
        elif tag == 3:
            n = word()
            off = word()
            if i + n + pad4(n) > len(blk):
                raise Bad("truncated")
            toks.append(("prop", off, blk[i:i + n]))
            i += n + pad4(n)
        elif tag == 4:
            toks.append(("nop",))
        elif tag == 9:
            if strict_end and i < len(blk):
                raise Bad("after_end")
            return toks
        else:
            raise Bad("bad_token %d" % tag)


def build_tree(toks, strs, nop_ok, props_first):
    stack, root = [], None
    for t in toks:
        if t[0] == "begin":
            if root is not None:
                raise Bad("unbalanced")
            stack.append((t[1], [], []))
        elif t[0] == "end":
            if not stack:
                raise Bad("unbalanced")
            n = stack.pop()
            if stack:
                stack[-1][2].append(n)
            else:
                root = n
        elif t[0] == "prop":
            if not stack:
                raise Bad("unbalanced")
            j = strs.find(b"\0", t[1]) if t[1] < len(strs) else -1
            if j < 0:
                raise Bad("bad_nameoff")
            if props_first and stack[-1][2]:
                raise Bad("prop_after_node")
            stack[-1][1].append((strs[t[1]:j], t[2]))
        elif not nop_ok:
            raise Bad("nop_refused")
    if root is None and not stack:
        raise Bad("no_root")
    if stack:
        raise Bad("unbalanced")
    return root


def dump(n):
    name, props, kids = n
    return name.hex() + "{" + "".join(k.hex() + "=" + v.hex() + ";" for k, v in props) + "".join(dump(c) for c in kids) + "}"


def summary(b, **opts):
    try:
        v, boot, rsv, tree = read(b, **opts)
    except Bad as e:
        return "error " + e.args[0]
    return "ok %d %d [%s ] %s" % (v, boot, "".join(" %016x:%016x" % r for r in rsv), dump(tree))


# Random trees

NAMECH = b"abcdefghijklmnopqrstuvwxyz0123456789,._+-"
STD = [b"compatible", b"reg", b"#address-cells", b"#size-cells", b"model", b"status", b"device_type",
       b"interrupts", b"clock-frequency", b"ranges", b"bootargs", b"linux,phandle", b"phandle"]


def rname(rng, wild=False):
    s = bytes(rng.choice(NAMECH) for _ in range(rng.randrange(1, 12)))
    if wild and rng.random() < 0.1:
        s += bytes([rng.randrange(1, 256)])
    return s


def rvalue(rng):
    kind = rng.random()
    if kind < 0.3:
        return be32(rng.choice([0, 1, 2, rng.randrange(1 << 32)]))
    if kind < 0.4:
        return rname(rng) + b"\0"
    if kind < 0.55:
        return b"".join(rname(rng) + b"\0" for _ in range(rng.randrange(0, 4)))
    n = rng.choice([0, 0, 1, 2, 3, 5, 8, rng.randrange(9, 48)])
    return bytes(rng.randrange(256) for _ in range(n))


def rtree(rng, depth=0, name=b"", wild=False, unique=False):
    props, used = [], set()
    for _ in range(rng.randrange(0, 5)):
        k = rng.choice(STD[:11]) if rng.random() < 0.3 else rname(rng, wild)
        if unique and k in used:
            continue
        used.add(k)
        props.append((k, rvalue(rng)))
    kids, knames = [], set()
    if depth < 3:
        for _ in range(rng.randrange(0, 4 - depth)):
            nm = rname(rng, wild)
            if rng.random() < 0.4:
                nm += b"@" + ("%x" % rng.randrange(1 << 20)).encode()
            if unique and nm in knames:
                continue
            knames.add(nm)
            kids.append(rtree(rng, depth + 1, nm, wild, unique))
    return (name, props, kids)


def rrsv(rng):
    return [(rng.randrange(1, 1 << 64), rng.randrange(1 << 64)) for _ in range(rng.choice([0, 0, 1, 2, 3]))]


# The same tree as Bend source

def bbytes(b):
    if len(b) <= 1000:
        return "B.Octets.of_list([" + ", ".join(str(x) for x in b) + "])"
    return "B.Octets.concat([" + ", ".join(bbytes(b[i:i + 1000]) for i in range(0, len(b), 1000)) + "])"


def btree(n):
    name, props, kids = n
    return "T.FdtNode{%s, [%s], [%s]}" % (bbytes(name), ", ".join("T.FdtProp{%s, %s}" % (bbytes(k), bbytes(v)) for k, v in props), ", ".join(btree(c) for c in kids))


def brsv(rsv):
    return "[" + ", ".join("R.FdtRsv{W.W64.from_parts(%d, %d), W.W64.from_parts(%d, %d)}" % (a >> 32, a & 0xFFFFFFFF, s >> 32, s & 0xFFFFFFFF) for a, s in rsv) + "]"


# The same tree as dts source, for dtc

def dts(tree, rsv):
    out = "/dts-v1/;\n" + "".join("/memreserve/ 0x%x 0x%x;\n" % r for r in rsv)

    def node(n, top):
        name, props, kids = n
        s = ("/" if top else name.decode()) + " {\n"
        for k, v in props:
            s += k.decode() + (" = [" + " ".join("%02x" % x for x in v) + "];\n" if v else ";\n")
        return s + "".join(node(c, False) for c in kids) + "};\n"

    return out + node(tree, True)


def dtc_compile(src, boot, d):
    p = os.path.join(d, "t.dts")
    with open(p, "w") as f:
        f.write(src)
    r = subprocess.run(["dtc", "-q", "-I", "dts", "-O", "dtb", "-b", str(boot), p], capture_output=True)
    if r.returncode != 0:
        raise RuntimeError("dtc refused a source: " + r.stderr.decode())
    return r.stdout


# Corruption

def corrupt(rng, b):
    b = bytearray(b)
    kind = rng.choice(["truncate", "magic", "version", "lastcomp", "total", "offset", "size", "byte", "token", "nameoff", "unbalance", "rsv"])
    hdr = list(struct.unpack(">10I", bytes(b[:40])))
    _, ts, ost, ostr, orsv, v, lc, boot, sstr, sst = hdr

    def put(i, x):
        hdr[i] = x & 0xFFFFFFFF
        b[:40] = struct.pack(">10I", *hdr)

    if kind == "truncate":
        return bytes(b[:rng.randrange(len(b))])
    if kind == "magic":
        b[rng.randrange(4)] ^= 1 << rng.randrange(8)
    elif kind == "version":
        put(5, rng.choice([1, 2, 3, 15, 16, 18, 20]))
    elif kind == "lastcomp":
        put(6, rng.choice([17, 18, 99]))
    elif kind == "total":
        put(1, rng.choice([0, 39, ts - 1, ts + 1, ts + 100]))
    elif kind == "offset":
        i = rng.choice([2, 3, 4])
        put(i, hdr[i] + rng.choice([-41, -4, -1, 1, 4, 8, 1000]))
    elif kind == "size":
        i = rng.choice([8, 9])
        put(i, hdr[i] + rng.choice([-8, -4, -1, 1, 4, 1000]))
    elif kind == "byte":
        i = rng.randrange(40, len(b))
        b[i] = rng.randrange(256)
    elif kind == "token":
        i = ost + 4 * rng.randrange(max(1, sst // 4))
        b[i:i + 4] = be32(rng.choice([0, 5, 6, 8, 10, 0xFFFFFFFF, 2, 9, 1]))
    elif kind == "nameoff":
        i = ost
        while i + 12 <= ost + sst and u32at(b, i) != 3:
            i += 4
        if i + 12 <= ost + sst:
            b[i + 8:i + 12] = be32(rng.choice([sstr, sstr + 5, 0xFFFFFFF0, max(0, sstr - 1)]))
    elif kind == "unbalance":
        i = ost + sst - 8
        b[i:i + 4] = be32(rng.choice([4, 1, 3]))
    else:
        i = orsv + 16 * rng.randrange(3)
        b[i:i + 16] = bytes(rng.randrange(256) for _ in range(16))
    return bytes(b)


# Typed values, as the package decodes them

def show_u32(v):
    return "ok %d" % u32at(v, 0) if len(v) == 4 else "error bad_length"


def show_u64(v):
    return "ok %016x" % struct.unpack(">Q", v)[0] if len(v) == 8 else "error bad_length"


def show_str(v):
    j = v.find(b"\0")
    return "ok " + v[:j].hex() if j >= 0 and j == len(v) - 1 else "error bad_string"


def show_strs(v):
    if not v:
        return "ok"
    if v[-1] != 0:
        return "error bad_string"
    return "ok" + "".join(" " + s.hex() for s in v[:-1].split(b"\0"))


def cells(v):
    if len(v) % 4:
        raise Bad("bad_length")
    return [u32at(v, i) for i in range(0, len(v), 4)]


def show_cells(v):
    try:
        return "ok" + "".join(" %d" % c for c in cells(v))
    except Bad as e:
        return "error " + e.args[0]


def num(cs):
    return 0 if not cs else cs[0] if len(cs) == 1 else (cs[0] << 32) | cs[1]


def show_reg(ac, sc, v):
    try:
        if not (ac <= 2 and sc <= 2 and ac + sc != 0):
            raise Bad("bad_cells")
        cs = cells(v)
        if len(cs) % (ac + sc):
            raise Bad("bad_length")
        k = ac + sc
        return "ok" + "".join(" %016x:%016x" % (num(cs[i:i + ac]), num(cs[i + ac:i + k])) for i in range(0, len(cs), k))
    except Bad as e:
        return "error " + e.args[0]


# Lookups, as the package defines them

def child(n, k):
    for c in n[2]:
        if c[0] == k:
            return c
    if b"@" not in k:
        for c in n[2]:
            if c[0].split(b"@")[0] == k:
                return c
    return None


def comps(p):
    return [c for c in p.split(b"/") if c]


def walk(cs, n):
    for c in cs:
        if n is None:
            return None
        n = child(n, c)
    return n


def find(root, path):
    if path.startswith(b"/"):
        return walk(comps(path), root)
    cs = comps(path)
    if not cs:
        return None
    al = child(root, b"aliases")
    if al is None:
        return None
    v = next((v for k, v in al[1] if k == cs[0]), None)
    if v is None:
        return None
    j = v.find(b"\0")
    if j < 0 or j != len(v) - 1:
        return None
    return walk(comps(v[:-1]) + cs[1:], root)


def phandle_of(n, ph):
    for key in (b"phandle", b"linux,phandle"):
        v = next((v for k, v in n[1] if k == key), None)
        if v is not None and len(v) == 4 and u32at(v, 0) == ph:
            return True
    return False


def find_ph(n, ph):
    if phandle_of(n, ph):
        return n
    for c in n[2]:
        r = find_ph(c, ph)
        if r is not None:
            return r
    return None


def show_node(n):
    return "none" if n is None else dump(n)


def paths(n, pre=b""):
    out = []
    for c in n[2]:
        p = pre + b"/" + c[0]
        out.append(p)
        out += paths(c, p)
    return out


# A large tree, built the same way here and in the Bend prelude (big.tree):
# past the sizes at which the package's list code overflowed Bend's stack
# before it was made tail-recursive

def big_tree(nb, nd):
    def dev(i):
        return (b"dev@%d" % i, [(b"compatible", b"acme,widget\0"), (b"reg", be32(i) + be32(16)), (b"status", b"okay\0"), (b"id", be32(i + 1))], [])
    buses = [(b"bus@%d" % b, [(b"#address-cells", be32(1)), (b"#size-cells", be32(1))], [dev(b * nd + j) for j in range(nd)]) for b in range(nb)]
    return (b"", [(b"#address-cells", be32(1)), (b"#size-cells", be32(1)), (b"compatible", b"acme,board\0")],
            [(b"aliases", [(b"serial0", b"/bus@0/dev@0\0")], [])] + buses)


def fnv(b):
    """FNV-1a, 32 bits: the fingerprint the Bend side prints for a large blob"""
    h = 2166136261
    for x in b:
        h = ((h ^ x) * 16777619) & 0xFFFFFFFF
    return "%d %d" % (len(b), h)


def main(seed):
    rng = random.Random(seed)
    lines, expect, trees = [], [], []
    have_dtc = shutil.which("dtc") is not None

    def case(label, bend, want):
        lines.append('    IO.print("%s " ++ %s)' % (label, bend))
        expect.append("%s %s" % (label, want))

    # build: the bytes of the simple and the deduplicated writers
    same_as_dtc = 0
    with tempfile.TemporaryDirectory() as d:
        for k in range(30):
            t, rs, boot = rtree(rng, unique=True), rrsv(rng), rng.choice([0, 1, rng.randrange(1 << 32)])
            simple, dedup = write(t, rs, boot), write(t, rs, boot, dedup=True)
            assert read(simple)[3] == t and read(dedup)[3] == t
            if have_dtc:
                assert dtc_compile(dts(t, rs), boot, d) == dedup, "dtc writes other bytes than the dedup writer"
                same_as_dtc += 1
            trees.append((k, t))
            case("build %d" % k, "B.Octets.hex(F.Fdt.build(%s, %s, %d))" % (btree(t), brsv(rs), boot), simple.hex())
            case("dedup %d" % k, "B.Octets.hex(F.Fdt.build_with(T.FdtStringsDedup{}, %s, %s, %d))" % (btree(t), brsv(rs), boot), dedup.hex())

        # large: a tree of 600 devices (75 KB with the simple strings block)
        t, rs = big_tree(4, 150), [(0x10000000, 0x10000)]
        simple, dedup = write(t, rs, 0), write(t, rs, 0, dedup=True)
        assert read(simple)[3] == t and read(dedup)[3] == t
        if have_dtc:
            assert dtc_compile(dts(t, rs), 0, d) == dedup, "dtc writes other bytes than the dedup writer (large tree)"
            same_as_dtc += 1
        case("large build", "fp(F.Fdt.build(big.tree(4n, 150n), big.rsv(), 0))", fnv(simple))
        case("large dedup", "fp(F.Fdt.build_with(T.FdtStringsDedup{}, big.tree(4n, 150n), big.rsv(), 0))", fnv(dedup))
        case("large parse", "big.parsed(F.Fdt.parse(F.FdtOptions.default(), F.Fdt.build_with(T.FdtStringsDedup{}, big.tree(4n, 150n), big.rsv(), 0)))", fnv(dedup))

        # parse: blobs from this writer, half corrupted
        for k in range(140):
            t, rs, boot = rtree(rng, wild=True), rrsv(rng), rng.randrange(1 << 32)
            v16 = rng.random() < 0.2
            b = write(t, rs, boot, dedup=rng.random() < 0.5, nops=rng if rng.random() < 0.3 else None,
                      version=16 if v16 else 17,
                      gaps=(8 * rng.choice([0, 0, 1]), 4 * rng.choice([0, 0, 1, 3]), rng.choice([0, 0, 1, 7])),
                      tail=bytes(rng.choice([0, 0, 0, 3, 16])))
            if k % 2:
                b = corrupt(rng, b)
            case("parse %d" % k, "show(F.Fdt.parse(F.FdtOptions.default(), %s))" % bbytes(b), summary(b))

        # the options: NOPs refused, version 17 only, properties after children allowed
        t = (b"", [(b"a", b"1")], [(b"n", [], [])])
        nopped = write(t, [], 0, nops=random.Random(3))
        late = bytearray(write(t, [], 0))
        # move the property after the child: swap the prop token and the child's tokens
        st = struct.unpack(">I", late[8:12])[0]
        body = bytes(late[st + 8:st + 8 + 16])   # FDT_PROP a "1"
        kid = bytes(late[st + 24:st + 24 + 12])  # FDT_BEGIN_NODE n, FDT_END_NODE
        late[st + 8:st + 36] = kid + body
        for label, opts, py in [("nop refused", "F.FdtOptions{H.FdtV16V17{}, T.FdtTreeRules{False{}, True{}}}", dict(nop_ok=False)),
                                ("nop allowed", "F.FdtOptions.default()", {}),
                                ("late prop strict", "F.FdtOptions.default()", {}),
                                ("late prop lenient", "F.FdtOptions{H.FdtV16V17{}, T.FdtTreeRules{True{}, False{}}}", dict(props_first=False)),
                                ("v16 only17", "F.FdtOptions{H.FdtV17Only{}, T.FdtTreeRules.default()}", dict(versions="17")),
                                ("v20 compat", "F.FdtOptions{H.FdtVCompatible{}, T.FdtTreeRules.default()}", dict(versions="compat")),
                                ("v20 default", "F.FdtOptions.default()", {})]:
            b = nopped if label.startswith("nop") else bytes(late) if label.startswith("late") else write(t, [], 0, version=16 if label.startswith("v16") else 20)
            case(label, "show(F.Fdt.parse(%s, %s))" % (opts, bbytes(b)), summary(b, **py))

        # dtc: random sources compiled by dtc, read by the package
        n_dtc = 0
        if have_dtc:
            for k in range(25):
                t, rs, boot = rtree(rng, unique=True), rrsv(rng), rng.randrange(1 << 16)
                b = dtc_compile(dts(t, rs), boot, d)
                assert read(b) == (17, boot, rs, t), "dtc's blob does not hold the source's tree"
                case("dtc %d" % k, "show(F.Fdt.parse(F.FdtOptions.default(), %s))" % bbytes(b), summary(b))
                n_dtc += 1

    # values
    for k in range(60):
        v = rvalue(rng) if k % 2 else bytes(rng.randrange(256) for _ in range(rng.choice([0, 4, 8, 7, 12, 16, 24])))
        if k % 5 == 0:
            v = rname(rng) + bytes([0, rng.randrange(256)])[:rng.choice([1, 2])]
        if k % 5 == 1:
            v = b"".join(rname(rng) + bytes(1) for _ in range(rng.randrange(1, 4)))
        bv = bbytes(v)
        case("u32 %d" % k, "r32(P.FdtProp.u32(%s))" % bv, show_u32(v))
        case("u64 %d" % k, "r64(P.FdtProp.u64(%s))" % bv, show_u64(v))
        case("str %d" % k, "rstr(P.FdtProp.string(%s))" % bv, show_str(v))
        case("strs %d" % k, "rstrs(P.FdtProp.strings(%s))" % bv, show_strs(v))
        case("cells %d" % k, "rcells(P.FdtProp.cells(%s))" % bv, show_cells(v))
        ac, sc = rng.choice([(1, 1), (2, 1), (2, 2), (1, 0), (0, 1), (2, 0), (0, 0), (3, 1)])
        case("reg %d" % k, "rreg(P.FdtProp.reg(%dn, %dn, %s))" % (ac, sc, bv), show_reg(ac, sc, v))

    # lookups
    for k in range(20):
        t = rtree(rng)
        ps = paths(t)
        al = []
        for i, p in enumerate(ps[:3]):
            al.append((b"al%d" % i, p + b"\0"))
        t = (t[0], t[1], t[2] + [(b"aliases", al, [])])
        phs = []
        def number(n, depth=0):
            props = list(n[1])
            if rng.random() < 0.5:
                ph = rng.randrange(1, 50)
                props.append((rng.choice([b"phandle", b"linux,phandle"]), be32(ph)))
                phs.append(ph)
            return (n[0], props, [number(c, depth + 1) for c in n[2]])
        t = number(t)
        queries = ps[:4] + [p.split(b"@")[0] for p in ps[:3]] + [b"/", b"/nonexistent", b"al0", b"al1/x", b"nope"]
        bt = btree(t)
        for j, q in enumerate(queries):
            case("find %d %d" % (k, j), "node(Pa.FdtNode.find(%s, \"%s\"))" % (bt, q.decode()), show_node(find(t, q)))
        for j, ph in enumerate(phs[:3] + [99]):
            case("phandle %d %d" % (k, j), "node(Pa.FdtNode.find_phandle(%s, %d))" % (bt, ph), show_node(find_ph(t, ph)))

    # in groups of a few cases each, so that no def is too large to check,
    # and in case files of at most about FILE_BYTES each, run one after the
    # other, so that no native build of one needs more than about a GB
    groups = [lines[i:i + 8] for i in range(0, len(lines), 8)]
    files, size = [[]], 0
    for g, ls in enumerate(groups):
        n = sum(len(l) for l in ls)
        if files[-1] and size + n > FILE_BYTES:
            files.append([])
            size = 0
        files[-1].append(g)
        size += n
    for old in os.listdir(HERE):
        if re.fullmatch(r"cases\d+\.bend", old):
            os.remove(os.path.join(HERE, old))
    for n, mine in enumerate(files):
        with open(os.path.join(HERE, "cases%02d.bend" % n), "w", newline="\n") as f:
            f.write(PRELUDE)
            for g in mine:
                f.write("def part%d() -> IO(Unit):\n  do IO<Unit>:\n%s\n\n" % (g, "\n".join(groups[g])))
            f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join("    part%d()" % g for g in mine) + "\n")
    with open(os.path.join(HERE, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    with open(os.path.join(HERE, "trees.txt"), "w", newline="\n") as f:
        for k, t in trees:
            f.write("%d %s\n" % (k, dump(t)))
    print("%d cases (%s)" % (len(expect), "dtc: %d sources compiled, %d blobs byte-identical to dtc's" % (n_dtc, same_as_dtc) if have_dtc else "dtc not installed: its cases skipped"))


def post(output):
    """dtc and fdtdump on every blob Fdt.build and Fdt.build_with wrote."""
    if not (shutil.which("dtc") and shutil.which("fdtdump")):
        print("dtc or fdtdump not installed: the post check skipped")
        return
    trees = {}
    with open(os.path.join(HERE, "trees.txt")) as f:
        for line in f:
            k, d = line.split()
            trees[k] = d
    n = 0
    with tempfile.TemporaryDirectory() as d, open(output) as f:
        for line in f:
            kind, k, hexs = line.split()[0], line.split()[1], line.split()[-1]
            if kind not in ("build", "dedup"):
                continue
            blob = os.path.join(d, "b.dtb")
            with open(blob, "wb") as g:
                g.write(bytes.fromhex(hexs))
            # dtc reads the blob as the tree it was built from (dtc writes it
            # out again, and this file's reader reads that)
            again = subprocess.run(["dtc", "-q", "-I", "dtb", "-O", "dtb", blob], capture_output=True, check=True).stdout
            got = dump(read(again)[3])
            if got != trees[k]:
                sys.exit("dtc read %s %s as another tree:\n%s\n%s" % (kind, k, got, trees[k]))
            # and decompiles it, naming every node (the .dts text is not
            # compiled back: dtc writes "\0" before a digit ambiguously)
            src = subprocess.run(["dtc", "-q", "-I", "dtb", "-O", "dts", blob], capture_output=True, check=True).stdout
            names = [bytes.fromhex(x) for x in re.findall(r"([0-9a-f]*)\{", trees[k])[1:]]
            if not all(nm in src for nm in names):
                sys.exit("dtc's source for %s %s misses a node" % (kind, k))
            fd = subprocess.run(["fdtdump", blob], capture_output=True)
            if fd.returncode != 0 or b"magic:" not in fd.stdout:
                sys.exit("fdtdump refused %s %s" % (kind, k))
            n += 1
    print("dtc and fdtdump read back %d blobs" % n)


PRELUDE = '''import Base
import ../../word64/word64.bend as W
import ../../bytes/bytes.bend as B
import ../error.bend as E
import ../header.bend as H
import ../rsvmap.bend as R
import ../tree.bend as T
import ../props.bend as P
import ../path.bend as Pa
import ../fdt.bend as F

def err(e: E.FdtError) -> String:
  match e:
    case E.FdtTooShort{}:
      "too_short"
    case E.FdtBadMagic{}:
      "bad_magic"
    case E.FdtBadVersion{}:
      "bad_version"
    case E.FdtBadLastComp{}:
      "bad_last_comp"
    case E.FdtBadTotalSize{}:
      "bad_total_size"
    case E.FdtBadRsvmap{}:
      "bad_rsvmap"
    case E.FdtBadStruct{}:
      "bad_struct"
    case E.FdtBadStrings{}:
      "bad_strings"
    case E.FdtRsvUnterminated{}:
      "rsv_unterminated"
    case E.FdtBadToken{t}:
      "bad_token " ++ U32.show(t)
    case E.FdtTruncated{}:
      "truncated"
    case E.FdtAfterEnd{}:
      "after_end"
    case E.FdtUnbalanced{}:
      "unbalanced"
    case E.FdtNoRoot{}:
      "no_root"
    case E.FdtPropAfterNode{}:
      "prop_after_node"
    case E.FdtNopRefused{}:
      "nop_refused"
    case E.FdtBadNameOff{}:
      "bad_nameoff"
    case E.FdtBadLength{}:
      "bad_length"
    case E.FdtBadString{}:
      "bad_string"
    case E.FdtBadCells{}:
      "bad_cells"

def props(ps: List<&2, T.FdtProp>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{p, t}:
      match p:
        case T.FdtProp{k, v}:
          B.Octets.hex(k) ++ "=" ++ B.Octets.hex(v) ++ ";" ++ props(t)

def forest(ns: List<&2, T.FdtNode>) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{n, t}:
      match n:
        case T.FdtNode{nm, ps, cs}:
          B.Octets.hex(nm) ++ "{" ++ props(ps) ++ forest(cs) ++ "}" ++ forest(t)

def rsvs(rs: List<&2, R.FdtRsv>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{r, t}:
      match r:
        case R.FdtRsv{a, s}:
          " " ++ W.W64.show_hex(a) ++ ":" ++ W.W64.show_hex(s) ++ rsvs(t)

def show(r: Result<&2, &2, E.FdtError, F.FdtBlob>) -> String:
  match r:
    case Done{b}:
      match b:
        case F.FdtBlob{v, boot, rs, root}:
          "ok " ++ U32.show(v) ++ " " ++ U32.show(boot) ++ " [" ++ rsvs(rs) ++ " ] " ++ forest([root])
    case Fail{e}:
      "error " ++ err(e)

def node(m: Maybe<&2, T.FdtNode>) -> String:
  match m:
    case Some{n}:
      forest([n])
    case None{}:
      "none"

def r32(r: Result<&2, &2, E.FdtError, U32>) -> String:
  match r:
    case Done{v}:
      "ok " ++ U32.show(v)
    case Fail{e}:
      "error " ++ err(e)

def r64(r: Result<&2, &2, E.FdtError, W.W64>) -> String:
  match r:
    case Done{v}:
      "ok " ++ W.W64.show_hex(v)
    case Fail{e}:
      "error " ++ err(e)

def rstr(r: Result<&2, &2, E.FdtError, B.Octets>) -> String:
  match r:
    case Done{v}:
      "ok " ++ B.Octets.hex(v)
    case Fail{e}:
      "error " ++ err(e)

def strl(ss: List<&2, B.Octets>) -> String:
  match ss:
    case Nil{}:
      ""
    case Con{s, t}:
      " " ++ B.Octets.hex(s) ++ strl(t)

def rstrs(r: Result<&2, &2, E.FdtError, List<&2, B.Octets>>) -> String:
  match r:
    case Done{v}:
      "ok" ++ strl(v)
    case Fail{e}:
      "error " ++ err(e)

def celll(cs: List<&2, U32>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{c, t}:
      " " ++ U32.show(c) ++ celll(t)

def rcells(r: Result<&2, &2, E.FdtError, List<&2, U32>>) -> String:
  match r:
    case Done{v}:
      "ok" ++ celll(v)
    case Fail{e}:
      "error " ++ err(e)

def regl(rs: List<&2, P.FdtReg>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{r, t}:
      match r:
        case P.FdtReg{a, s}:
          " " ++ W.W64.show_hex(a) ++ ":" ++ W.W64.show_hex(s) ++ regl(t)

def rreg(r: Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>) -> String:
  match r:
    case Done{v}:
      "ok" ++ regl(v)
    case Fail{e}:
      "error " ++ err(e)

# A large tree (gen.py: big_tree), and a blob's length and FNV-1a hash

def big.s(x: String) -> B.Octets:
  B.Octets.of_string(x)

def big.dev(+i: Nat) -> T.FdtNode:
  T.FdtNode{big.s("dev@" ++ Nat.show(i)), [T.FdtProp{big.s("compatible"), P.FdtProp.of_text("acme,widget")}, T.FdtProp{big.s("reg"), P.FdtProp.of_cells([U32.from_nat(i), 16])}, T.FdtProp{big.s("status"), P.FdtProp.of_text("okay")}, T.FdtProp{big.s("id"), P.FdtProp.of_u32(U32.from_nat(1n+i))}], []}

def big.devs(k: Nat, +base: Nat, acc: List<&2, T.FdtNode>) -> List<&2, T.FdtNode>:
  match k:
    case 0n:
      acc
    case 1n+(+q):
      big.devs(q, base, Con{big.dev(Nat.add(base, q)), acc})

def big.bus(+b: Nat, +nd: Nat) -> T.FdtNode:
  T.FdtNode{big.s("bus@" ++ Nat.show(b)), [T.FdtProp{big.s("#address-cells"), P.FdtProp.of_u32(1)}, T.FdtProp{big.s("#size-cells"), P.FdtProp.of_u32(1)}], big.devs(nd, Nat.mul(b, nd), Nil{})}

def big.buses(k: Nat, +nd: Nat, acc: List<&2, T.FdtNode>) -> List<&2, T.FdtNode>:
  match k:
    case 0n:
      acc
    case 1n+(+q):
      big.buses(q, nd, Con{big.bus(q, nd), acc})

def big.tree(nb: Nat, nd: Nat) -> T.FdtNode:
  T.FdtNode{big.s(""), [T.FdtProp{big.s("#address-cells"), P.FdtProp.of_u32(1)}, T.FdtProp{big.s("#size-cells"), P.FdtProp.of_u32(1)}, T.FdtProp{big.s("compatible"), P.FdtProp.of_text("acme,board")}], Con{T.FdtNode{big.s("aliases"), [T.FdtProp{big.s("serial0"), P.FdtProp.of_text("/bus@0/dev@0")}], []}, big.buses(nb, nd, Nil{})}}

def big.rsv() -> List<&2, R.FdtRsv>:
  [R.FdtRsv{W.W64.from_u32(268435456), W.W64.from_u32(65536)}]

def fnv.go(xs: List<&2, U32>, h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case Con{b, t}:
      fnv.go(t, U32.mul(U32.xor(h, b), 16777619))

def fp(+o: B.Octets) -> String:
  Nat.show(B.Octets.len(o)) ++ " " ++ U32.show(fnv.go(B.Octets.to_list(o), 2166136261))

# a parsed blob, written again with the deduplicated strings block
def big.parsed(r: Result<&2, &2, E.FdtError, F.FdtBlob>) -> String:
  match r:
    case Done{b}:
      match b:
        case F.FdtBlob{v, boot, rs, root}:
          fp(F.Fdt.build_with(T.FdtStringsDedup{}, root, rs, boot))
    case Fail{e}:
      "error " ++ err(e)

'''

if __name__ == "__main__":
    if len(sys.argv) > 2 and sys.argv[1] == "--post":
        post(sys.argv[2])
    else:
        main(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
