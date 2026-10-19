#!/usr/bin/env python3
"""Differential test cases for bend-osdev-asn1.

Two references:

* `openssl asn1parse` (the system's OpenSSL): every DER input is parsed by
  it too, and the element structure it prints (offsets, depth, header and
  contents lengths, primitive or constructed) must be the one this file's
  model of ITU-T X.690 gives; every input cut short must be refused by it;
* a model of X.690, written here from the Recommendation: an encoder of
  random element trees (DER, and BER variants: lengths in more octets than
  needed, indefinite lengths, constructed strings, SETs out of order), and
  the tree each input stands for.

Each case's input is decoded by the package under DER and under BER rules;
the trees printed must be the model's, the DER re-encoding of the BER tree
must be the model's DER encoding, and inputs that are not BER (cut short,
lengths past the end, octets after the element, a long-form length octet FF)
must be refused under both rules.

Writes ref/cases.bend and ref/expected.txt; prints how many cases.
"""
import os, random, re, subprocess, sys, tempfile
sys.dont_write_bytecode = True

STRINGS = {3, 4, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 30}
PRIM_ONLY = {1, 2, 5, 6, 9, 10, 13}
CONS_ONLY = {16, 17}
CLS = "UACP"


def ident(cls, cons, num):
    first = (cls << 6) | (0x20 if cons else 0)
    if num < 31:
        return bytes([first | num])
    ds = []
    while True:
        ds.append(num & 0x7F)
        num >>= 7
        if num == 0:
            break
    ds.reverse()
    return bytes([first | 31]) + bytes([0x80 | d for d in ds[:-1]] + [ds[-1]])


def length(n, extra=0):
    if n < 128 and extra == 0:
        return bytes([n])
    bs = n.to_bytes(max(1, (n.bit_length() + 7) // 8), "big")
    bs = bytes(extra) + bs
    return bytes([0x80 | len(bs)]) + bs


# a node: ("p", cls, num, content) or ("c", cls, num, [children])
def der(node):
    if node[0] == "p":
        _, c, n, body = node
        return ident(c, False, n) + length(len(body)) + body
    _, c, n, kids = node
    body = b"".join(der(k) for k in kids)
    return ident(c, True, n) + length(len(body)) + body


def ber(node, rng):
    """an encoding of node with BER's freedoms taken at random"""
    if node[0] == "p":
        _, c, n, body = node
        return ident(c, False, n) + length(len(body), rng.choice([0, 0, 1, 2])) + body
    _, c, n, kids = node
    body = b"".join(ber(k, rng) for k in kids)
    if rng.random() < 0.4:
        return ident(c, True, n) + b"\x80" + body + b"\x00\x00"
    return ident(c, True, n) + length(len(body), rng.choice([0, 0, 1])) + body


def show(node, d=0):
    if node[0] == "p":
        _, c, n, body = node
        return "%d%s%dp%s" % (d, CLS[c], n, body.hex())
    _, c, n, kids = node
    return " ".join(["%d%s%dc%d" % (d, CLS[c], n, len(kids))] + [show(k, d + 1) for k in kids])


def rand_tag(rng, cons):
    while True:
        c = rng.choice([0, 0, 1, 2, 2, 3])
        n = rng.choice([rng.randrange(0, 31), rng.randrange(31, 200), rng.randrange(200, 1 << 20)])
        if c == 0:
            if n == 0 or n > 36:
                continue
            if cons and (n in PRIM_ONLY or n in STRINGS):
                continue
            if not cons and n in CONS_ONLY:
                continue
        return c, n


def rand_node(rng, depth):
    if depth > 3 or rng.random() < 0.45:
        c, n = rand_tag(rng, False)
        size = rng.choice([0, 1, 2, 5, 30, 127, 128, 200, rng.randrange(0, 400)])
        return ("p", c, n, rng.randbytes(size))
    c, n = rand_tag(rng, True)
    kids = [rand_node(rng, depth + 1) for _ in range(rng.randrange(0, 4))]
    if c == 0 and n == 17:
        kids.sort(key=lambda k: der(k).ljust(2048, b"\x00"))
    return ("c", c, n, kids)


def asn1parse(data):
    """openssl asn1parse's elements: (offset, depth, header, length) or None"""
    with tempfile.NamedTemporaryFile(delete=False) as f:
        f.write(data)
        name = f.name
    try:
        p = subprocess.run(["openssl", "asn1parse", "-inform", "DER", "-in", name], capture_output=True, text=True, errors="replace")
    finally:
        os.unlink(name)
    if p.returncode != 0 or "Error" in p.stdout or "Error" in p.stderr:
        return None
    out = []
    for ln in p.stdout.splitlines():
        m = re.match(r"\s*(\d+):d=\s*(\d+)\s+hl=\s*(\d+)\s+l=\s*(\d+|inf)\s+(prim|cons):", ln)
        if m:
            out.append((int(m.group(1)), int(m.group(2)), int(m.group(3)), m.group(4), m.group(5)))
    return out


def model_elems(data, node, off=0, d=0, acc=None, berform=False):
    """the (offset, depth, header, length, form) list openssl prints for a
    DER encoding of node"""
    acc = [] if acc is None else acc
    hl = len(ident(node[1], node[0] == "c", node[2]))
    if node[0] == "p":
        hl += len(length(len(node[3])))
        acc.append((off, d, hl, str(len(node[3])), "prim"))
        return acc
    body = b"".join(der(k) for k in node[3])
    hl += len(length(len(body)))
    acc.append((off, d, hl, str(len(body)), "cons"))
    o = off + hl
    for k in node[3]:
        model_elems(data, k, o, d + 1, acc)
        o += len(der(k))
    return acc


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    have_openssl = subprocess.run(["sh", "-c", "command -v openssl"], capture_output=True).returncode == 0
    defs, lines, expect = [], [], []
    checked = [0]

    def case(name, data, want_der, want_ber, want_enc):
        defs.append('def c_%s() -> String:\n  run(hx("%s"))\n' % (name, data.hex()))
        lines.append('    IO.print("%s " ++ c_%s())' % (name, name))
        expect.append("%s %s | %s | %s" % (name, want_der, want_ber, want_enc))

    for k in range(60):
        node = rand_node(rng, 0)
        d = der(node)
        if have_openssl:
            got = asn1parse(d)
            if got != model_elems(d, node):
                raise SystemExit("openssl asn1parse disagrees with the model on %s:\n%s\n%s" % (d.hex(), got, model_elems(d, node)))
            checked[0] += 1
        case("der%d" % k, d, show(node), show(node), d.hex())
        # a BER encoding of the same tree
        b = ber(node, rng)
        if b != d:
            case("ber%d" % k, b, "ERR", show(node), d.hex())
        # inputs that are not BER at all
        if len(d) > 2:
            cut = d[:rng.randrange(1, len(d))]
            if have_openssl and asn1parse(cut) is not None:
                raise SystemExit("openssl asn1parse accepts a cut input %s" % cut.hex())
            case("cut%d" % k, cut, "ERR", "ERR", "-")
        case("trail%d" % k, d + b"\x00", "ERR", "ERR", "-")
    # hand-made cases: X.690's examples and edge cases
    fixed = [
        ("x690seq", ("c", 0, 16, [("p", 0, 22, b"Smith"), ("p", 0, 1, bytes([255]))]), True),
        ("x690oid", ("p", 0, 6, bytes.fromhex("883703")), True),
        ("x690tag3", ("c", 2, 2, [("p", 1, 3, b"Jones")]), True),
        ("ff_len", bytes.fromhex("04ff00"), False),
        ("past_end", bytes.fromhex("3005020101"), False),
        ("bad_tag", bytes.fromhex("1f1e00"), False),
        ("lead80", bytes.fromhex("1f801f00"), False),
        ("eoc_top", bytes.fromhex("0000"), False),
        ("prim_indef", bytes.fromhex("048001000000"), False),
    ]
    for name, data, ok in fixed:
        if ok:
            d = der(data)
            case(name, d, show(data), show(data), d.hex())
        else:
            case(name, data, "ERR", "ERR", "-")
    # SET OF out of order: BER only
    s = ("c", 0, 17, [("p", 0, 2, b"\x02"), ("p", 0, 2, b"\x01")])
    case("set_order", der(s), "ERR", show(s), der(s).hex())
    # constructed OCTET STRING: BER only
    cs = ("c", 0, 4, [("p", 0, 4, b"ab"), ("p", 0, 4, b"c")])
    case("cons_string", der(cs), "ERR", show(cs), der(cs).hex())

    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write(open(os.path.join(here, "show.bend.in")).read())
        f.write("\n".join(defs))
        f.write("\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print("%d cases (%d checked against openssl asn1parse)" % (len(expect), checked[0]))


main()
