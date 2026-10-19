#!/usr/bin/env python3
"""Differential test cases for bend-osdev-nlattr.

Three references:

* the running kernel: an RTM_GETLINK dump over a NETLINK_ROUTE socket
  (Python's socket module, no privileges needed) gives attribute blobs the
  kernel built; the package parses each one, and its IFLA_IFNAME (3) and
  IFLA_MTU (4) must be what `ip -j link show` (iproute2) reports, and its
  attribute list what the model below parses;
* a model of RFC 3549's attribute format and the kernel documentation's
  rules, written here: building random attribute trees, parsing random and
  damaged buffers (strict and liberal), and validating against random
  policies;
* the model's build and parse must agree with each other (parse after
  build).

Writes ref/cases.bend and ref/expected.txt; prints how many cases.
"""
import json, os, random, socket, struct, subprocess, sys
sys.dont_write_bytecode = True

ORDERS = {"le": "<", "be": ">"}

def pad(n):
    return (4 - n % 4) % 4

def build(attrs, order="le"):
    out = b""
    for (t, nd, nb, payload) in attrs:
        f = t | (0x8000 if nd else 0) | (0x4000 if nb else 0)
        n = 4 + len(payload)
        out += struct.pack(ORDERS[order] + "HH", n, f) + payload + b"\0" * pad(n)
    return out

def parse(buf, order="le", strict=True):
    out, off = [], 0
    while True:
        rem = len(buf) - off
        if rem == 0:
            return out
        if rem < 4:
            return out if not strict else "NlTrailing"
        n, f = struct.unpack_from(ORDERS[order] + "HH", buf, off)
        if n < 4 or n - 4 > rem - 4:
            return "NlBadLength"
        payload = buf[off + 4: off + n]
        out.append((f & 0x3fff, bool(f & 0x8000), bool(f & 0x4000), payload))
        off = min(len(buf), off + n + pad(n))

def show(attrs):
    if isinstance(attrs, str):
        return attrs
    if not attrs:
        return "-"
    return " ".join("%d%s%s:%s" % (t, "N" if nd else "", "B" if nb else "", p.hex()) for (t, nd, nb, p) in attrs)

# Policies: lists of rules, as the package's NlRule
def validate(policies, pol, attrs, strict, depth=10):
    work = [(depth, pol, list(attrs))]
    while work:
        d, p, xs = work.pop(0)
        if not xs:
            continue
        a, rest = xs[0], xs[1:]
        t, nd, nb, pl = a
        rules = policies[p] if p < len(policies) else []
        rule = rules[t] if t < len(rules) else None
        l = len(pl)
        r = None
        if rule is None:
            if strict:
                return "NlUnknown %d" % t
        else:
            k = rule[0]
            if k == "unspec":
                if l < rule[1]: return "NlTooShort %d" % t
            elif k in ("u8", "u16", "u32", "u64"):
                size = {"u8": 1, "u16": 2, "u32": 4, "u64": 8}[k]
                if strict:
                    if l < size: return "NlTooShort %d" % t
                    if l > size: return "NlTooLarge %d" % t
                elif l < size:
                    return "NlTooShort %d" % t
            elif k == "string":
                sl = l - 1 if l and pl[-1] == 0 else l
                if rule[1] and sl > rule[1]: return "NlTooLarge %d" % t
            elif k == "nulstring":
                if not (l and pl[-1] == 0): return "NlNoNul %d" % t
                if rule[1] and l - 1 > rule[1]: return "NlTooLarge %d" % t
            elif k == "flag":
                if l != 0: return "NlNotFlag %d" % t
            elif k == "binary":
                if l < rule[1]: return "NlTooShort %d" % t
                if rule[2] and l > rule[2]: return "NlTooLarge %d" % t
            elif k == "nested":
                if strict and not nd: return "NlNoNestedFlag %d" % t
                if d == 0: return "NlTooDeep"
                inner = parse(pl, "le", strict)
                if isinstance(inner, str): return inner
                r = (d - 1, rule[1], inner)
            elif k == "reject":
                return "NlUnknown %d" % t
        work = ([r] if r else []) + [(d, p, rest)] + work
    return None

def bend_bytes(b):
    return "B.Octets.of_list([%s])" % ", ".join(str(x) for x in b)

def bend_attr(a):
    t, nd, nb, p = a
    return "N.NlAttr{%dn, %s, %s, %s}" % (t, "True{}" if nd else "False{}", "True{}" if nb else "False{}", bend_bytes(p))

def bend_rule(r):
    k = r[0]
    if k == "unspec":
        return "P.NlUnspec{%dn}" % r[1]
    if k == "string":
        return "P.NlString{%dn}" % r[1]
    if k == "nulstring":
        return "P.NlNulString{%dn}" % r[1]
    if k == "nested":
        return "P.NlNested{%dn}" % r[1]
    if k == "binary":
        return "P.NlBinary{%dn, %dn}" % (r[1], r[2])
    return {"u8": "P.NlU8{}", "u16": "P.NlU16{}", "u32": "P.NlU32{}", "u64": "P.NlU64{}", "flag": "P.NlFlag{}", "reject": "P.NlReject{}"}[k]

def rand_payload(rng):
    n = rng.choice([0, 1, 2, 3, 4, 5, 8, rng.randrange(40)])
    return bytes(rng.randrange(256) for _ in range(n))

def rand_attrs(rng, depth):
    out = []
    for _ in range(rng.randrange(0, 5)):
        t = rng.choice([rng.randrange(8), rng.randrange(16384)])
        if depth and rng.random() < 0.25:
            out.append((t, rng.random() < 0.8, False, build(rand_attrs(rng, depth - 1))))
        else:
            out.append((t, False, rng.random() < 0.2, rand_payload(rng)))
    return out

def kernel_links():
    """(attribute blob, ifname, mtu) for each link, from an RTM_GETLINK dump"""
    s = socket.socket(socket.AF_NETLINK, socket.SOCK_RAW, socket.NETLINK_ROUTE)
    s.bind((0, 0))
    s.send(struct.pack("=LHHLL", 32, 18, 0x301, 1, 0) + struct.pack("=BxHiII", 0, 0, 0, 0, 0))
    blobs, done = [], False
    while not done:
        data = s.recv(65536)
        off = 0
        while off < len(data):
            ln, ty = struct.unpack_from("=LH", data, off)
            if ty == 3:
                done = True
                break
            if ty == 16:
                blobs.append(data[off + 32: off + ln])
            off += (ln + 3) & ~3
    links = json.loads(subprocess.run(["ip", "-j", "link", "show"], capture_output=True, text=True, check=True).stdout)
    return blobs, links

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    defs, expect = [], []
    def case(body, exp):
        defs.append("def c%d() -> String:\n  %s\n" % (len(defs), body))
        expect.append(exp)
    # the kernel's attributes
    try:
        blobs, links = kernel_links()
    except OSError:
        blobs, links = [], []
    for blob, link in zip(blobs, links):
        attrs = parse(blob)
        names = [p for (t, nd, nb, p) in attrs if t == 3]
        mtus = [p for (t, nd, nb, p) in attrs if t == 4]
        assert names and names[0].rstrip(b"\0").decode() == link["ifname"], "model and ip disagree on the name"
        assert mtus and struct.unpack("<I", mtus[0])[0] == link["mtu"], "model and ip disagree on the MTU"
        case("kernel(%s)" % bend_bytes(blob), "%s %s %d" % (show(attrs), link["ifname"], link["mtu"]))
    # build and parse
    for _ in range(60):
        attrs = rand_attrs(rng, 2)
        order = rng.choice(["le", "be"])
        o = "H.NlLittle{}" if order == "le" else "H.NlBig{}"
        case("round(%s, %s)" % (o, "[%s]" % ", ".join(bend_attr(a) for a in attrs)), build(attrs, order).hex() + " " + show(parse(build(attrs, order), order)))
    # damaged buffers
    for _ in range(60):
        buf = bytearray(build(rand_attrs(rng, 1)))
        r = rng.random()
        if r < 0.3 and buf:
            del buf[rng.randrange(len(buf)):]
        elif r < 0.6 and len(buf) > 1:
            buf[rng.randrange(2)] = rng.randrange(256)
        else:
            buf += bytes(rng.randrange(256) for _ in range(rng.randrange(6)))
        case("both(%s)" % bend_bytes(buf), show(parse(bytes(buf), "le", True)) + " | " + show(parse(bytes(buf), "le", False)))
    # validation
    kinds = ["u8", "u16", "u32", "u64", "flag", "string", "nulstring", "binary", "unspec", "nested", "reject"]
    for _ in range(80):
        policies = []
        for _ in range(2):
            rules = []
            for _ in range(rng.randrange(1, 9)):
                k = rng.choice(kinds)
                if k in ("string", "nulstring"):
                    rules.append((k, rng.choice([0, 2, 5, 40])))
                elif k == "binary":
                    rules.append((k, rng.randrange(4), rng.choice([0, 3, 8])))
                elif k == "unspec":
                    rules.append((k, rng.randrange(5)))
                elif k == "nested":
                    rules.append((k, rng.randrange(2)))
                else:
                    rules.append((k,))
            policies.append(rules)
        attrs = []
        for _ in range(rng.randrange(0, 5)):
            t = rng.randrange(9)
            if rng.random() < 0.3:
                attrs.append((t, rng.random() < 0.7, False, build([(rng.randrange(9), False, False, rand_payload(rng)) for _ in range(rng.randrange(3))])))
            else:
                p = rand_payload(rng)
                if rng.random() < 0.3:
                    p = p + b"\0"
                attrs.append((t, False, False, p))
        strict = rng.random() < 0.5
        res = validate(policies, 0, attrs, strict)
        pset = "[%s]" % ", ".join("P.NlPolicy{[%s]}" % ", ".join(bend_rule(r) for r in rules) for rules in policies)
        case("check(%s, %s, %s)" % ("True{}" if strict else "False{}", pset, bend_attr_list(attrs)), res or "ok")
    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write(PRELUDE)
        f.write("\n".join(defs) + "\n")
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join("    IO.print(c%d())" % i for i in range(len(defs))) + "\n")
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print(len(defs), "cases (%d kernel links)" % len(blobs))

def bend_attr_list(attrs):
    return "[%s]" % ", ".join(bend_attr(a) for a in attrs)

PRELUDE = '''import Base
import ../../bytes/bytes.bend as B
import ../header.bend as H
import ../nlattr.bend as N
import ../policy.bend as P

def err(e: N.NlError) -> String:
  match e:
    case N.NlBadType{t}:
      "NlBadType " ++ Nat.show(t)
    case N.NlTooLong{t}:
      "NlTooLong " ++ Nat.show(t)
    case N.NlBadLength{}:
      "NlBadLength"
    case N.NlTrailing{}:
      "NlTrailing"
    case N.NlUnknown{t}:
      "NlUnknown " ++ Nat.show(t)
    case N.NlTooShort{t}:
      "NlTooShort " ++ Nat.show(t)
    case N.NlTooLarge{t}:
      "NlTooLarge " ++ Nat.show(t)
    case N.NlNoNul{t}:
      "NlNoNul " ++ Nat.show(t)
    case N.NlNotFlag{t}:
      "NlNotFlag " ++ Nat.show(t)
    case N.NlNoNestedFlag{t}:
      "NlNoNestedFlag " ++ Nat.show(t)
    case N.NlTooDeep{}:
      "NlTooDeep"

def show_a(a: N.NlAttr) -> String:
  match a:
    case N.NlAttr{t, nd, nb, p}:
      Nat.show(t) ++ Bool.pick(String, nd, "N", "") ++ Bool.pick(String, nb, "B", "") ++ ":" ++ B.Octets.hex(p)

def show_as(as: List<&2, N.NlAttr>) -> String:
  match as:
    case Nil{}:
      "-"
    case Con{a, Nil{}}:
      show_a(a)
    case Con{a, t}:
      show_a(a) ++ " " ++ show_as(t)

def show_p(r: Result<&2, &2, N.NlError, List<&2, N.NlAttr>>) -> String:
  match r:
    case Done{as}:
      show_as(as)
    case Fail{e}:
      err(e)

def name(+m: Maybe<&2, N.NlAttr>) -> String:
  match m:
    case Some{a}:
      B.Octets.to_string(B.Octets.take(Nat.sub(B.Octets.len(N.nla.payload(a)), 1n), N.nla.payload(a)))
    case None{}:
      "none"

def mtu(m: Maybe<&2, N.NlAttr>) -> String:
  match m:
    case Some{a}:
      Maybe.default(&2, String, Maybe.map(&2, U32, String, v => U32.show(v), N.nla.get_u32(H.NlLittle{}, a)), "none")
    case None{}:
      "none"

def kernel.go(r: Result<&2, &2, N.NlError, List<&2, N.NlAttr>>) -> String:
  match r:
    case Done{+as}:
      show_as(as) ++ " " ++ name(N.nla.find(as, 3n)) ++ " " ++ mtu(N.nla.find(as, 4n))
    case Fail{e}:
      err(e)

def kernel(b: B.Octets) -> String:
  kernel.go(N.nla.parse(N.nla.opts_default(), b))

def round.go(+o: H.NlOrder, r: Result<&2, &2, N.NlError, B.Octets>) -> String:
  match r:
    case Done{+b}:
      B.Octets.hex(b) ++ " " ++ show_p(N.nla.parse(N.NlOpts{o, True{}}, b))
    case Fail{e}:
      err(e)

def round(+o: H.NlOrder, as: List<&2, N.NlAttr>) -> String:
  round.go(o, N.nla.build(o, as))

def both(+b: B.Octets) -> String:
  show_p(N.nla.parse(N.nla.opts_default(), b)) ++ " | " ++ show_p(N.nla.parse(N.nla.opts_liberal(H.NlLittle{}), b))

def check.go(r: Result<&2, &2, N.NlError, Unit>) -> String:
  match r:
    case Done{u}:
      "ok"
    case Fail{e}:
      err(e)

def check(strict: Bool, set: List<&2, P.NlPolicy>, as: List<&2, N.NlAttr>) -> String:
  match strict:
    case True{}:
      check.go(P.nla.validate(P.nla.check_strict(H.NlLittle{}), set, 0n, 1000n, as))
    case False{}:
      check.go(P.nla.validate(P.nla.check_liberal(H.NlLittle{}), set, 0n, 1000n, as))

'''

main()
