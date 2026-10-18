#!/usr/bin/env python3
"""Differential test cases for bend-osdev-nftables.

nft is not available here (and running packets through the kernel's
nf_tables needs root and network namespaces), so the reference is an
independent model of nftables rule evaluation written in Python from the same
documentation as the package (the nft(8) manual page and the nftables wiki's
descriptions of chains, verdicts, sets, maps and limits). It shares an author
with the package, so it guards against slips in the Bend code (a wrong
offset, a verdict handled in the wrong place, a set misordered, a counter or
bucket updated wrongly), not against a shared misreading of the
documentation; the README says so.

The Python model is written in a different style on purpose: chains are run
by plain recursion with an explicit level, packets are raw bytes packed with
struct, sets are lists checked with Python's bytes comparison, and the limit
is min(cap, credit + elapsed * rate).

Writes ref/cases.bend (a Bend program that builds each rule set and packet
and prints each evaluation) and ref/expected.txt (the Python model's
results). Each case is one rule set and a few packets sent one after another
at increasing times, the state (counters, limits) carried from one to the
next.
"""
import os, random, struct, sys

MAX_DEPTH = 16

# ---- the independent model

def key_contains(lo, hi, v):
    return lo <= v <= hi

def build_set(elems):
    """elems: list of (lo, hi, data). nft refuses an interval whose low end is
    above its high end, or one that overlaps an element already in the set;
    a test set that is refused stands for the empty set (cases.bend's so())."""
    out = []
    for lo, hi, d in elems:
        if lo > hi:
            return []
        for (a, b, _) in out:
            if not (hi < a or b < lo):
                return []
        out.append((lo, hi, d))
    return out

class PSet:
    """a set as written (raw, in the order given) and as nft holds it"""
    def __init__(self, raw):
        self.raw = raw
        self.elems = build_set(raw)

def set_lookup(s, v):
    for lo, hi, d in s.elems:
        if key_contains(lo, hi, v):
            return (True, d)
    return (False, None)

class Pkt:
    def __init__(self, raw, iif, oif, mark, ctstate, ctmark):
        self.raw = raw
        self.iif, self.oif, self.mark = iif, oif, mark
        self.ctstate, self.ctmark = ctstate, ctmark
        v = raw[0] >> 4
        if v == 4:
            hl = (raw[0] & 15) * 4
            self.l4proto, self.nfproto = raw[9], 2
        else:
            hl = 40
            self.l4proto, self.nfproto = raw[6], 10
        rest = raw[hl:]
        self.th = None
        p = self.l4proto
        if p == 6 and len(rest) >= 20 and (rest[12] >> 4) >= 5 and len(rest) >= (rest[12] >> 4) * 4:
            self.th = rest
        elif p == 17 and len(rest) >= 8:
            self.th = rest
        elif p in (1, 58) and len(rest) >= 8:
            self.th = rest
        self.length = len(raw)

def load(src, sets, pkt):
    kind = src[0]
    if kind == "payload":
        _, base, off, ln = src
        data = {"nh": pkt.raw, "th": pkt.th, "ll": None}[base]
        if data is None or off + ln > len(data):
            return None
        return data[off:off + ln]
    if kind == "meta":
        k = src[1]
        if k == "l4proto":
            return bytes([pkt.l4proto])
        if k == "nfproto":
            return bytes([pkt.nfproto])
        return struct.pack(">I", {"iif": pkt.iif, "oif": pkt.oif, "mark": pkt.mark, "length": pkt.length}[k])
    if kind == "ct":
        return struct.pack(">I", pkt.ctstate if src[1] == "state" else pkt.ctmark)
    if kind == "imm":
        return src[1]
    if kind == "bitwise":
        v = load(src[1], sets, pkt)
        if v is None:
            return None
        m, x = src[2], src[3]
        return bytes(((b & (m[i] if i < len(m) else 255)) ^ (x[i] if i < len(x) else 0)) for i, b in enumerate(v))
    if kind == "concat":
        a, b = load(src[1], sets, pkt), load(src[2], sets, pkt)
        return None if a is None or b is None else a + b
    if kind == "map":
        k = load(src[1], sets, pkt)
        s = resolve(src[2], sets)
        if k is None or s is None:
            return None
        hit, d = set_lookup(s, k)
        if hit and d is not None and d[0] == "value":
            return d[1]
        return None
    raise ValueError(kind)

def resolve(ref, sets):
    if ref[0] == "anon":
        return ref[1]
    return sets.get(ref[1])

def test(t, v, sets):
    kind = t[0]
    if kind == "cmp":
        op, w = t[1], t[2]
        return {"eq": v == w, "ne": v != w, "lt": v < w, "le": v <= w, "gt": v > w, "ge": v >= w}[op]
    if kind == "range":
        return t[1] <= v <= t[2]
    if kind == "notrange":
        return not (t[1] <= v <= t[2])
    s = resolve(t[1], sets)
    if s is None:
        return False
    hit = set_lookup(s, v)[0]
    return hit if kind == "in" else not hit

class State:
    def __init__(self):
        self.counters = {}  # id -> [packets, bytes], in order of first use
        self.buckets = {}   # id -> [credit, last]

def limit(st, ident, spec, now, length):
    rate, unit, burst, bybytes, over = spec
    cap = (burst if burst else rate) * unit
    cost = (length if bybytes else 1) * unit
    if ident in st.buckets:
        credit, last = st.buckets[ident]
        elapsed = now - last if now >= last else 0
        credit = min(cap, credit + elapsed * rate)
    else:
        credit = cap
    conform = credit >= cost
    if conform:
        credit -= cost
    st.buckets[ident] = [credit, now]
    return conform != over

def eval_rule(rule, sets, pkt, st, now):
    """None (no verdict) or a verdict tuple"""
    for x in rule:
        kind = x[0]
        if kind == "match":
            v = load(x[1], sets, pkt)
            if v is None or not test(x[2], v, sets):
                return None
        elif kind == "counter":
            c = st.counters.setdefault(x[1], [0, 0])
            c[0] += 1
            c[1] += pkt.length
        elif kind == "limit":
            if not limit(st, x[1], x[2], now, pkt.length):
                return None
        elif kind in ("markset", "ctmarkset"):
            v = load(x[1], sets, pkt)
            if v is None or len(v) < 4:
                return None
            m = struct.unpack(">I", v[:4])[0]
            if kind == "markset":
                pkt.mark = m
            else:
                pkt.ctmark = m
        elif kind == "vmap":
            v = load(x[1], sets, pkt)
            s = resolve(x[2], sets)
            if v is None or s is None:
                return None
            hit, d = set_lookup(s, v)
            if not hit or d is None or d[0] != "verdict":
                return None
            return d[1]
        elif kind == "verdict":
            return x[1]
    return None

class Budget(Exception):
    pass

def run_chain(table, rules, fuel, level, pkt, st, now, steps):
    """('ret', None, deepest) or ('stop', final, deepest)"""
    deepest = level
    for rule in rules:
        steps[0] += 1
        if steps[0] > 20000:
            raise Budget()
        v = eval_rule(rule, table["sets"], pkt, st, now)
        if v is None or v[0] == "continue":
            continue
        k = v[0]
        if k in ("accept", "drop", "reject", "queue"):
            return ("stop", v, deepest)
        if k == "return":
            return ("ret", None, deepest)
        if fuel == 0:
            return ("stop", ("drop",), deepest)
        if v[1] not in table["chains"]:
            return ("stop", ("drop",), deepest)
        r = run_chain(table, table["chains"][v[1]]["rules"], fuel - 1, level + 1, pkt, st, now, steps)
        deepest = max(deepest, r[2])
        if k == "goto":
            return (r[0], r[1], deepest)
        if r[0] == "stop":
            return ("stop", r[1], deepest)
    return ("ret", None, deepest)

def sees(fam, proto):
    return (fam, proto) in (("ip", "ipv4"), ("ip6", "ipv6"), ("inet", "ipv4"), ("inet", "ipv6"))

def eval_hook(rs, proto, hook, pkt, st, now):
    chains = []
    for t in rs:
        if not sees(t["family"], proto):
            continue
        for name in t["order"]:
            c = t["chains"][name]
            if c["base"] and c["base"][0] == hook:
                chains.append((c["base"][1], len(chains), t, c))
    chains.sort(key=lambda e: (e[0], e[1]))  # by signed priority; stable
    deepest = 0
    steps = [0]
    for prio, _, t, c in chains:
        r = run_chain(t, c["rules"], MAX_DEPTH, 0, pkt, st, now, steps)
        deepest = max(deepest, r[2])
        if r[0] == "ret":
            if c["base"][2] == "drop":
                return (("drop",), deepest)
            continue
        if r[1][0] == "accept":
            continue
        return (r[1], deepest)
    return (("accept",), deepest)

def show_final(v):
    k = v[0]
    if k == "accept":
        return "accept"
    if k == "drop":
        return "drop"
    if k == "queue":
        return "queue num %d" % v[1] + (" bypass" if v[2] else "")
    how = v[1]
    if how[0] == "default":
        return "reject"
    if how[0] == "tcp":
        return "reject with tcp reset"
    return "reject with %s %d" % (how[0], how[1])

def show(v, pkt, st, depth):
    s = "%s mark=%d ctmark=%d depth=%d" % (show_final(v), pkt.mark, pkt.ctmark, depth)
    for ident, (n, b) in st.counters.items():
        s += " c%d=%d/%d" % (ident, n, b)
    return s

# ---- random rule sets and packets

V4 = [bytes([10, 0, 0, 1]), bytes([10, 0, 0, 2]), bytes([192, 168, 1, 5]), bytes([172, 16, 0, 9])]
V6 = [bytes([32, 1, 13, 184] + [0] * 11 + [1]), bytes([254, 128] + [0] * 13 + [1]), bytes([0] * 15 + [1])]
PORTS = [22, 53, 80, 443, 8080, 1234]
HOOKS = ["input", "forward", "output", "prerouting", "postrouting"]

def r16(v):
    return struct.pack(">H", v)

def gen_packet(rng):
    v6 = rng.random() < 0.35
    proto = rng.choice([6, 6, 17, 17, 58 if v6 else 1, 47])
    data = bytes(rng.randrange(256) for _ in range(rng.randrange(0, 12)))
    if proto == 6:
        opt = bytes(rng.randrange(256) for _ in range(4)) if rng.random() < 0.2 else b""
        off = 5 + len(opt) // 4
        l4 = r16(rng.choice(PORTS + [rng.randrange(65536)])) + r16(rng.choice(PORTS)) + struct.pack(">II", rng.randrange(2**32), rng.randrange(2**32)) + bytes([off << 4 | rng.randrange(16), rng.randrange(256)]) + struct.pack(">HHH", rng.randrange(65536), rng.randrange(65536), rng.randrange(65536)) + opt
    elif proto == 17:
        l4 = r16(rng.choice(PORTS)) + r16(rng.choice(PORTS)) + r16(8 + len(data)) + r16(rng.randrange(65536))
    elif proto in (1, 58):
        l4 = bytes([rng.choice([0, 3, 8, 128, 129]), rng.randrange(4)]) + r16(rng.randrange(65536)) + struct.pack(">I", rng.randrange(2**32))
    else:
        l4 = b""
    if rng.random() < 0.1:
        l4 = l4[:rng.randrange(len(l4) + 1)]  # a cut-short transport header
        data = b""
    body = l4 + data
    if v6:
        nh = struct.pack(">IHBB", (6 << 28) | rng.randrange(1 << 20), len(body), proto, rng.randrange(256)) + rng.choice(V6) + rng.choice(V6)
    else:
        opt = bytes(rng.randrange(256) for _ in range(4)) if rng.random() < 0.15 else b""
        ihl = 5 + len(opt) // 4
        nh = bytes([64 | ihl, rng.randrange(256)]) + r16(len(opt) + 20 + len(body)) + r16(rng.randrange(65536)) + r16(rng.randrange(65536)) + bytes([rng.randrange(256), proto]) + r16(rng.randrange(65536)) + rng.choice(V4) + rng.choice(V4) + opt
    raw = nh + body
    ct = rng.choice([1, 2, 4, 8, 2, 8, 64])
    return Pkt(raw, rng.randrange(1, 4), rng.randrange(0, 3), rng.choice([0, 0, 1, 2, 7]), ct, rng.choice([0, 0, 5]))

def gen_value(rng, kind):
    """a source and a value it may hold"""
    if kind == "saddr4":
        return ("payload", "nh", 12, 4), rng.choice(V4)
    if kind == "daddr4":
        return ("payload", "nh", 16, 4), rng.choice(V4)
    if kind == "saddr6":
        return ("payload", "nh", 8, 16), rng.choice(V6)
    if kind == "dport":
        return ("payload", "th", 2, 2), r16(rng.choice(PORTS))
    if kind == "sport":
        return ("payload", "th", 0, 2), r16(rng.choice(PORTS))
    if kind == "l4proto":
        return ("meta", "l4proto"), bytes([rng.choice([6, 17, 1, 58])])
    if kind == "nfproto":
        return ("meta", "nfproto"), bytes([rng.choice([2, 10])])
    if kind == "mark":
        return ("meta", "mark"), struct.pack(">I", rng.choice([0, 1, 2, 7]))
    if kind == "iif":
        return ("meta", "iif"), struct.pack(">I", rng.randrange(1, 4))
    if kind == "length":
        return ("meta", "length"), struct.pack(">I", rng.randrange(20, 90))
    if kind == "ctmark":
        return ("ct", "mark"), struct.pack(">I", rng.choice([0, 5]))
    if kind == "proto":
        return ("payload", "nh", 9, 1), bytes([rng.choice([6, 17, 1])])
    if kind == "far":
        return ("payload", "nh", rng.randrange(30, 60), rng.randrange(1, 5)), bytes([rng.randrange(256)])
    if kind == "ll":
        return ("payload", "ll", 12, 2), r16(2048)
    if kind == "ctstate":
        return ("bitwise", ("ct", "state"), struct.pack(">I", rng.choice([2, 6, 8, 65])), b""), bytes(4)
    if kind == "tcpflags":
        return ("bitwise", ("payload", "th", 13, 1), bytes([rng.choice([2, 16, 18])]), b""), bytes([rng.choice([0, 2, 16])])
    raise ValueError(kind)

# SAFE: the case is generated within what the nft syntax printer below can
# write, so that `nft --check` can read it (about one case in three)
SAFE = False
SAFE_KINDS = ["saddr4", "daddr4", "saddr6", "dport", "sport", "l4proto", "mark", "length", "ctmark", "proto", "far"]

KINDS = ["saddr4", "daddr4", "saddr6", "dport", "dport", "sport", "l4proto", "nfproto", "mark", "iif", "length", "ctmark", "proto", "far", "ll", "tcpflags", "ctstate"]

def gen_elems(rng, sample, n, data_kind=None, chains=()):
    """n elements near the value sample (same width), possibly overlapping"""
    out = []
    w = len(sample)
    for _ in range(n):
        base = int.from_bytes(sample, "big")
        if rng.random() < 0.5:
            lo = hi = base if rng.random() < 0.6 else rng.randrange(1 << (8 * min(w, 2))) << (8 * max(0, w - 2))
        else:
            lo = max(0, base - rng.randrange(0, 300))
            hi = min((1 << (8 * w)) - 1, base + rng.randrange(0, 300))
            if rng.random() < 0.1:
                lo, hi = hi, lo
        d = None
        if data_kind == "value":
            d = ("value", struct.pack(">I", rng.choice([1, 2, 9])))
        elif data_kind == "verdict":
            d = ("verdict", gen_verdict(rng, chains, terminal_only=False))
        e = (lo.to_bytes(w, "big"), hi.to_bytes(w, "big"), d)
        # mostly disjoint elements; now and then one that nft refuses
        if build_set(out + [e]) or rng.random() < 0.05:
            out.append(e)
        sample = (rng.randrange(1 << (8 * w))).to_bytes(w, "big") if rng.random() < 0.3 else sample
    return out

def gen_verdict(rng, chains, terminal_only=False):
    r = rng.random()
    if r < 0.25:
        return ("accept",)
    if r < 0.45:
        return ("drop",)
    if r < 0.5:
        if SAFE:
            return ("reject", ("default",))
        return ("reject", rng.choice([("default",), ("tcp",), ("icmp", 3), ("icmpv6", 1), ("icmpx", 2)]))
    if r < 0.55:
        return ("queue", rng.randrange(4), not SAFE and rng.random() < 0.5)
    if r < 0.62:
        return ("continue",)
    if r < 0.7:
        return ("return",)
    if SAFE and not chains:
        return ("accept",)
    target = rng.choice(list(chains) + ([] if SAFE else ["missing"])) if chains else "missing"
    return ("jump" if r < 0.88 else "goto", target)

def gen_test(rng, sample, sets):
    r = rng.random()
    if r < 0.45:
        return ("cmp", rng.choice(["eq", "eq", "ne", "lt", "le", "gt", "ge"]), sample)
    if r < 0.6:
        lo = int.from_bytes(sample, "big")
        w = len(sample)
        a, b = max(0, lo - rng.randrange(50)), min((1 << 8 * w) - 1, lo + rng.randrange(50))
        return ("notrange" if rng.random() < 0.3 else "range", a.to_bytes(w, "big"), b.to_bytes(w, "big"))
    if r < 0.8 or not sets or SAFE:
        ref = ("anon", PSet(gen_elems(rng, sample, rng.randrange(1, 4))))
    else:
        ref = ("named", rng.choice(list(sets) + ["nosuch"]))
    return ("notin" if rng.random() < 0.25 else "in", ref)

def gen_expr(rng, chains, sets, ids):
    r = rng.random()
    if r < 0.6:
        src, sample = gen_value(rng, rng.choice(SAFE_KINDS if SAFE else KINDS))
        if not SAFE and rng.random() < 0.1:
            src2, sample2 = gen_value(rng, rng.choice(["dport", "l4proto", "mark"]))
            src, sample = ("concat", src, src2), sample + sample2
        return ("match", src, gen_test(rng, sample, sets))
    if r < 0.72:
        return ("counter", rng.choice(ids))
    if r < 0.8:
        if SAFE:
            return ("limit", rng.choice(ids), (rng.randrange(1, 4), 1000, rng.randrange(0, 3), False, rng.random() < 0.3))
        return ("limit", rng.choice(ids), (rng.randrange(1, 4), rng.choice([10, 100, 1000]), rng.randrange(0, 3), rng.random() < 0.2, rng.random() < 0.3))
    if r < 0.9:
        kind = "markset" if rng.random() < 0.7 else "ctmarkset"
        if SAFE or rng.random() < 0.5:
            return (kind, ("imm", struct.pack(">I", rng.choice([1, 2, 3]))))
        src, sample = gen_value(rng, rng.choice(["saddr4", "dport", "l4proto"]))
        return (kind, ("map", src, ("anon", PSet(gen_elems(rng, sample, rng.randrange(1, 3), "value")))))
    if SAFE:
        return ("counter", rng.choice(ids))
    src, sample = gen_value(rng, rng.choice(["dport", "saddr4", "l4proto"]))
    return ("vmap", src, ("anon", PSet(gen_elems(rng, sample, rng.randrange(1, 4), "verdict", chains))))

def gen_rule(rng, chains, sets, ids):
    xs = [gen_expr(rng, chains, sets, ids) for _ in range(rng.randrange(0, 3))]
    if rng.random() < 0.75:
        xs.append(("verdict", gen_verdict(rng, chains)))
    return xs

def gen_ruleset(rng):
    rs = []
    ids = [rng.randrange(1, 6) for _ in range(3)]
    for ti in range(rng.randrange(1, 4)):
        fam = rng.choice(["ip", "ip6", "inet", "inet"])
        names = ["c%d" % i for i in range(rng.randrange(1, 5))]
        sets = {}
        for si in range(rng.randrange(0, 3)):
            src, sample = gen_value(rng, rng.choice(["saddr4", "dport", "mark"]))
            sets["s%d" % si] = PSet(gen_elems(rng, sample, rng.randrange(1, 4)))
        bases = {}
        for i, n in enumerate(names):
            bases[n] = None
            if i == 0 or rng.random() < 0.3:
                prio = rng.choice([-300, -150, -100, 0, 0, 10, 50, 100])
                bases[n] = (rng.choice(HOOKS[:2]) if rng.random() < 0.8 else rng.choice(HOOKS), prio, rng.choice(["accept", "drop"]))
        chains = {}
        for i, n in enumerate(names):
            # nft refuses jumps to base chains and jumps that loop: a SAFE
            # case jumps only forward, to regular chains
            targets = [m for m in names[i + 1:] if bases[m] is None] if SAFE else names
            chains[n] = {"base": bases[n], "rules": [gen_rule(rng, targets, sets, ids) for _ in range(rng.randrange(0, 4))]}
        rs.append({"name": "t%d" % ti, "family": fam, "order": names, "chains": chains, "sets": sets, "elems": None})
    return rs


# ---- nft syntax, for `nft --check -f` (a syntax check only)

class Unsafe(Exception):
    pass

def n_int(b):
    return "0x" + b.hex() if b else "0"

def n_src(src):
    k = src[0]
    if k == "payload":
        return "@%s,%d,%d" % (src[1], src[2] * 8, src[3] * 8)
    if k == "meta" and src[1] in ("mark", "length", "l4proto"):
        return "meta " + src[1]
    if k == "ct" and src[1] == "mark":
        return "ct mark"
    raise Unsafe()

def n_elems(s):
    if not s.elems:
        raise Unsafe()
    return "{ " + ", ".join(n_int(lo) if lo == hi else "%s-%s" % (n_int(lo), n_int(hi)) for lo, hi, d in s.elems) + " }"

def n_test(t):
    k = t[0]
    if k == "cmp":
        return {"eq": "==", "ne": "!=", "lt": "<", "le": "<=", "gt": ">", "ge": ">="}[t[1]] + " " + n_int(t[2])
    if k == "range":
        return "%s-%s" % (n_int(t[1]), n_int(t[2]))
    if k == "notrange":
        return "!= %s-%s" % (n_int(t[1]), n_int(t[2]))
    if t[1][0] != "anon":
        raise Unsafe()
    return ("" if k == "in" else "!= ") + n_elems(t[1][1])

def n_verdict(v, chains):
    k = v[0]
    if k in ("accept", "drop", "continue", "return"):
        return k
    if k in ("jump", "goto"):
        if v[1] not in chains or chains[v[1]]["base"]:
            raise Unsafe()
        return "%s %s" % (k, v[1])
    if k == "queue" and not v[2]:
        return "queue num %d" % v[1]
    if k == "reject" and v[1][0] == "default":
        return "reject"
    raise Unsafe()

def n_expr(x, chains):
    k = x[0]
    if k == "match":
        return n_src(x[1]) + " " + n_test(x[2])
    if k == "counter":
        return "counter"
    if k == "limit":
        rate, unit, burst, byb, over = x[2]
        if unit != 1000 or byb:
            raise Unsafe()
        return "limit rate %s%d/second burst %d packets" % ("over " if over else "", rate, burst if burst else rate)
    if k in ("markset", "ctmarkset") and x[1][0] == "imm":
        return ("meta mark set " if k == "markset" else "ct mark set ") + n_int(x[1][1])
    if k == "verdict":
        return n_verdict(x[1], chains)
    raise Unsafe()

def n_acyclic(t):
    """nft refuses a rule set whose jumps and gotos loop"""
    edges = {n: {x[1][1] for r in t["chains"][n]["rules"] for x in r if x[0] == "verdict" and x[1][0] in ("jump", "goto")} for n in t["order"]}
    state = {}
    def visit(n):
        if state.get(n) == 1:
            raise Unsafe()
        if state.get(n) == 2:
            return
        state[n] = 1
        for m in edges.get(n, ()):
            visit(m)
        state[n] = 2
    for n in t["order"]:
        visit(n)

def nft_text(rs):
    out = []
    for t in rs:
        n_acyclic(t)
        out.append("table %s %s {" % (t["family"], t["name"]))
        for n in t["order"]:
            c = t["chains"][n]
            out.append("  chain %s {" % n)
            if c["base"]:
                out.append("    type filter hook %s priority %d; policy %s;" % c["base"])
            for r in c["rules"]:
                if r:
                    out.append("    " + " ".join(n_expr(x, t["chains"]) for x in r))
            out.append("  }")
        out.append("}")
    return "\n".join(out) + "\n"

# ---- Bend text

def bl(b):
    return "[" + ", ".join(str(x) for x in b) + "]"

def bo(b):
    return "ol(%s)" % bl(b)

def b_verdict(v):
    k = v[0]
    if k == "accept":
        return "V.NftAccept{}"
    if k == "drop":
        return "V.NftDrop{}"
    if k == "continue":
        return "V.NftContinue{}"
    if k == "return":
        return "V.NftReturn{}"
    if k == "jump":
        return 'V.NftJump{"%s"}' % v[1]
    if k == "goto":
        return 'V.NftGoto{"%s"}' % v[1]
    if k == "queue":
        return "V.NftQueue{%d, %s}" % (v[1], "True{}" if v[2] else "False{}")
    how = v[1]
    w = {"default": "V.NftRejectDefault{}", "tcp": "V.NftRejectTcpReset{}"}.get(how[0])
    if w is None:
        w = {"icmp": "V.NftRejectIcmp{%d}", "icmpv6": "V.NftRejectIcmpv6{%d}", "icmpx": "V.NftRejectIcmpx{%d}"}[how[0]] % how[1]
    return "V.NftReject{%s}" % w

def b_set(s):
    out = []
    for lo, hi, d in s.raw:
        if d is None:
            dd = "S.NftNoData{}"
        elif d[0] == "value":
            dd = "S.NftDataValue{%s}" % bo(d[1])
        else:
            dd = "S.NftDataVerdict{%s}" % b_verdict(d[1])
        out.append("S.NftElem{%s, %s, %s}" % (bo(lo), bo(hi), dd))
    return "so(S.NftSet.of_list([%s]))" % ", ".join(out)

def b_ref(ref, raw_elems=None):
    if ref[0] == "anon":
        return "X.NftSetAnon{%s}" % b_set(ref[1])
    return 'X.NftSetNamed{"%s"}' % ref[1]

def b_src(src):
    k = src[0]
    if k == "payload":
        base = {"nh": "X.NftBaseNh{}", "th": "X.NftBaseTh{}", "ll": "X.NftBaseLl{}"}[src[1]]
        return "X.NftSrcPayload{%s, %dn, %dn}" % (base, src[2], src[3])
    if k == "meta":
        return "X.NftSrcMeta{X.NftMeta%s{}}" % {"iif": "Iif", "oif": "Oif", "mark": "Mark", "l4proto": "L4proto", "length": "Length", "nfproto": "Nfproto"}[src[1]]
    if k == "ct":
        return "X.NftSrcCt{X.NftCt%s{}}" % ("State" if src[1] == "state" else "Mark")
    if k == "imm":
        return "X.NftSrcImm{%s}" % bo(src[1])
    if k == "bitwise":
        return "X.NftSrcBitwise{%s, %s, %s}" % (b_src(src[1]), bo(src[2]), bo(src[3]))
    if k == "concat":
        return "X.NftSrcConcat{%s, %s}" % (b_src(src[1]), b_src(src[2]))
    if k == "map":
        return "X.NftSrcMap{%s, %s}" % (b_src(src[1]), b_ref(src[2]))
    raise ValueError(k)

def b_test(t):
    k = t[0]
    if k == "cmp":
        return "X.NftCmp{X.NftOp%s{}, %s}" % (t[1].capitalize(), bo(t[2]))
    if k == "range":
        return "X.NftRange{%s, %s}" % (bo(t[1]), bo(t[2]))
    if k == "notrange":
        return "X.NftNotRange{%s, %s}" % (bo(t[1]), bo(t[2]))
    return "X.Nft%s{%s}" % ("In" if k == "in" else "NotIn", b_ref(t[1]))

def b_expr(x):
    k = x[0]
    if k == "match":
        return "X.NftMatch{%s, %s}" % (b_src(x[1]), b_test(x[2]))
    if k == "counter":
        return "X.NftCount{%d}" % x[1]
    if k == "limit":
        rate, unit, burst, byb, over = x[2]
        return "X.NftLimit{%d, X.NftLimitSpec{%d, %d, %d, %s, %s}}" % (x[1], rate, unit, burst, "True{}" if byb else "False{}", "True{}" if over else "False{}")
    if k == "markset":
        return "X.NftMarkSet{%s}" % b_src(x[1])
    if k == "ctmarkset":
        return "X.NftCtMarkSet{%s}" % b_src(x[1])
    if k == "vmap":
        return "X.NftVmap{%s, %s}" % (b_src(x[1]), b_ref(x[2]))
    return "X.NftVerdictStmt{%s}" % b_verdict(x[1])

def b_prio(p):
    return "F.NftPrio.of(True{}, %d)" % -p if p < 0 else str(p)

def b_ruleset(rs):
    tables = []
    for t in rs:
        chains = []
        for n in t["order"]:
            c = t["chains"][n]
            if c["base"]:
                hook = {"input": "Input", "forward": "Forward", "output": "Output", "prerouting": "Prerouting", "postrouting": "Postrouting"}[c["base"][0]]
                base = "Some{C.NftBaseSpec{F.Nft%s{}, %s, %s}}" % (hook, b_prio(c["base"][1]), "V.NftPolicyAccept{}" if c["base"][2] == "accept" else "V.NftPolicyDrop{}")
            else:
                base = "None{}"
            rules = ", ".join("X.NftRule{[%s]}" % ", ".join(b_expr(x) for x in r) for r in c["rules"])
            chains.append('C.NftChain{"%s", %s, [%s]}' % (n, base, rules))
        sets = ", ".join('S.NftNamedSet{"%s", %s}' % (k, b_set(v)) for k, v in t["sets"].items())
        fam = {"ip": "F.NftIp{}", "ip6": "F.NftIp6{}", "inet": "F.NftInet{}"}[t["family"]]
        tables.append('C.NftTable{"%s", %s, [%s], [%s]}' % (t["name"], fam, ", ".join(chains), sets))
    return "C.NftRuleset{[%s]}" % ", ".join(tables)

def b_packet(p):
    return "pk(X.NftPacket.of_ip(%d, %d, %d, X.NftCt{%d, %d}, B.Octets.of_list(%s)))" % (p.iif, p.oif, p.mark, p.ctstate, p.ctmark, bl(p.raw))

PRELUDE = """import Base
import ../../bytes/bytes.bend as B
import ../../word64/word64.bend as W
import ../family.bend as F
import ../verdict.bend as V
import ../sets.bend as S
import ../expr.bend as X
import ../chains.bend as C
import ../eval.bend as E
import ../nftables.bend as N

def ol(xs: List<&2, U32>) -> B.Octets:
  B.Octets.of_list(xs)

def so(r: Result<&2, &2, F.NftError, S.NftSet>) -> S.NftSet:
  match r:
    case Done{s}:
      s
    case Fail{e}:
      S.NftSet.empty()

def pk(r: Result<&2, &2, F.NftError, X.NftPacket>) -> X.NftPacket:
  match r:
    case Done{p}:
      p
    case Fail{e}:
      X.NftPacket{X.NftMeta{0, 0, 0, 0, 0, 0}, X.NftCt{0, 0}, X.NftL2None{}, X.NftL3None{}, X.NftL4None{}, B.Octets.empty()}

def ev(rs: C.NftRuleset, proto: F.NftProto, hook: F.NftHook, now: U32, p: X.NftPacket, st: X.NftState) -> N.NftResult:
  N.Nft.eval_default(rs, proto, hook, W.W64.from_u32(now), p, st)

"""

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    ncases = int(sys.argv[2]) if len(sys.argv) > 2 else 80
    defs, prints, expect = [], [], []
    nftdir = os.path.join(here, "nft")
    os.makedirs(nftdir, exist_ok=True)
    for old in os.listdir(nftdir):
        os.remove(os.path.join(nftdir, old))
    nfiles = 0
    k = 0
    global SAFE
    while k < ncases:
        SAFE = k % 3 == 0
        rs = gen_ruleset(rng)
        hook = rng.choice(HOOKS[:2]) if rng.random() < 0.85 else rng.choice(HOOKS)
        pkts = [gen_packet(rng) for _ in range(rng.randrange(1, 4))]
        times = sorted(rng.randrange(0, 3000) for _ in pkts)
        if rng.random() < 0.2:
            times = times[::-1]  # time going backwards: no refill
        st = State()
        try:
            outs = []
            for p, t in zip(pkts, times):
                pp = Pkt(p.raw, p.iif, p.oif, p.mark, p.ctstate, p.ctmark)
                v, d = eval_hook(rs, "ipv4" if p.raw[0] >> 4 == 4 else "ipv6", hook, pp, st, t)
                outs.append(show(v, pp, st, d))
        except Budget:
            continue
        try:
            text = nft_text(rs)
            with open(os.path.join(nftdir, "case%d.nft" % k), "w", newline="\n") as f:
                f.write(text)
            nfiles += 1
        except Unsafe:
            pass
        hk = {"input": "Input", "forward": "Forward", "output": "Output", "prerouting": "Prerouting", "postrouting": "Postrouting"}[hook]
        lines = ["def rs%d() -> C.NftRuleset:\n  %s\n" % (k, b_ruleset(rs))]
        body = ["def run%d() -> String:" % k, "  +rs = rs%d()" % k]
        prev = "X.NftState.empty()"
        shows = []
        for i, (p, t) in enumerate(zip(pkts, times)):
            proto = "F.NftProtoIpv4{}" if p.raw[0] >> 4 == 4 else "F.NftProtoIpv6{}"
            body.append("  +r%d = ev(rs, %s, F.Nft%s{}, %d, %s, %s)" % (i, proto, hk, t, b_packet(p), prev))
            prev = "N.NftResult.st(r%d)" % i
            shows.append("N.NftResult.show(r%d)" % i)
        body.append("  " + ' ++ " | " ++ '.join(shows))
        lines.append("\n".join(body) + "\n")
        defs.extend(lines)
        prints.append('    IO.print("%d " ++ run%d())' % (k, k))
        expect.append("%d %s" % (k, " | ".join(outs)))
        k += 1
    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write(PRELUDE + "\n".join(defs) + "\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(prints) + "\n")
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print("%d cases (%d packets)" % (len(expect), sum(e.count("|") + 1 for e in expect)))

main()
