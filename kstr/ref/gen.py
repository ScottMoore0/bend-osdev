#!/usr/bin/env python3
"""Differential test cases for bend-osdev-kstr.

Writes ref/cases.bend (a Bend program printing kstr's results) and
ref/expected.txt (the same from Python):
  * formatting: Python's own printf-style % operator (an implementation of
    C's rules outside this repository) for %d %i %u %x %X %o with the
    flags - 0 + and space and a width;
  * parsing: Python's int() on the digits, with the kstrtox rules this
    package documents (the prefix, one trailing newline, the sign, the
    ranges) written out here;
  * hex dumps and option matching: a model of the documented layouts.
"""
import os, random, sys

M32, M64 = (1 << 32) - 1, (1 << 64) - 1


def bl(bs):
    return "B.Octets.of_list([%s])" % ", ".join(str(b) for b in bs)


def strip(s):
    return s[:-1] if s.endswith("\n") else s


def digits_ok(s, base):
    return s != "" and all(c in "0123456789abcdefABCDEF"[:base if base <= 10 else 10 + 2 * (base - 10)] or
                           (base > 10 and c.lower() in "abcdef"[:base - 10]) for c in s)


def first_bad(s, base, off):
    for i, c in enumerate(s):
        v = int(c, 16) if c.lower() in "0123456789abcdef" else 99
        if v >= base:
            return off + i
    return None


def parse(s, base, signed, bits):
    """the documented kstrtox result: ('ok', v) or an error"""
    s = strip(s)
    neg, off = False, 0
    if s[:1] == "+":
        s, off = s[1:], 1
    elif s[:1] == "-":
        if not signed:
            return ("bad", 0)
        neg, s, off = True, s[1:], 1
    if base == 0:
        if s[:1] == "0" and s[1:2] in ("x", "X") and len(s) > 2 and s[2].lower() in "0123456789abcdef":
            base, s, off = 16, s[2:], off + 2
        elif s[:1] == "0":
            base = 8
        else:
            base = 10
    elif base == 16 and s[1:2] in ("x", "X"):
        if s[:1] != "0":
            return ("bad", off + 1)
        s, off = s[2:], off + 2
    if s == "":
        return ("empty",)
    acc = 0
    for i, c in enumerate(s):
        v = int(c, 16) if c.lower() in "0123456789abcdef" else 99
        if v >= base:
            return ("bad", off + i)
        acc = acc * base + v
        if acc >> bits:
            return ("range",)
    if signed:
        lim = 1 << (bits - 1)
        if (neg and acc > lim) or (not neg and acc >= lim):
            return ("range",)
        if neg:
            acc = (-acc) & ((1 << bits) - 1)
    return ("ok", acc)


def show(r):
    if r[0] == "ok":
        return str(r[1])
    if r[0] == "bad":
        return "bad char %d" % r[1]
    return {"empty": "empty", "range": "range"}[r[0]]


def hexline(bs, rowsize, groupsize, ascii, little):
    row = 32 if rowsize == 32 else 16
    bs = bs[:row]
    if not bs:
        return ""
    g = groupsize if groupsize in (1, 2, 4, 8) and len(bs) % groupsize == 0 else 1
    groups = []
    for i in range(0, len(bs), g):
        chunk = bs[i:i + g]
        groups.append((chunk[::-1] if little else chunk).hex())
    h = " ".join(groups)
    if not ascii:
        return h
    col = row * 2 + row // g + 1
    return h + " " * (col - len(h)) + "".join(chr(b) if 32 <= b <= 126 else "." for b in bs)


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []

    def case(name, call, want):
        lines.append('    IO.print("%s " ++ %s)' % (name, call))
        expect.append("%s %s" % (name, want))

    # formatting, against Python's % operator
    convs = [("d", "KConvD"), ("i", "KConvD"), ("u", "KConvU"), ("x", "KConvX"), ("X", "KConvXUpper"), ("o", "KConvO")]
    for k in range(150):
        ch, con = rng.choice(convs)
        # C ignores + and space for the unsigned conversions; Python does not
        flags = "".join(f for f in ("-0+ " if ch in "di" else "-0") if rng.random() < 0.3)
        width = rng.choice(["", str(rng.randrange(1, 25))])
        v = rng.choice([rng.randrange(1 << 64), rng.randrange(1 << 32), rng.randrange(1000), 0, M64, 1 << 63])
        pyv = (v - (1 << 64) if v >> 63 else v) if ch in "di" else v
        pyfmt = "%" + flags + width + ("d" if ch in "ui" else ch)
        want = pyfmt % pyv
        fmt = "%" + flags + width + ch
        case("fmt_%d" % k, 'sres(F.KStr.sprintf(B.Octets.of_string("<%s>"), [W.W64.from_parts(%d, %d)]))' % (fmt, v >> 32, v & M32), "<" + want + ">")
    # hex32 and parsing it back
    for k in range(40):
        v = rng.randrange(1 << 32)
        case("hex32_%d" % k, "r32(K.KStr.to_u32(F.KStr.hex32(%d), 16))" % v, v)
    # parsing, by the documented rules
    alpha = "0123456789abcdefxX+-\n g"
    for k in range(300):
        kind = rng.randrange(4)
        if kind == 0:
            base = rng.choice([8, 10, 16])
            v = rng.choice([rng.randrange(1 << 32), rng.randrange(1 << 34), rng.randrange(100)])
            s = {8: "%o", 10: "%d", 16: rng.choice(["%x", "0x%x", "%X"])}[base] % v
        elif kind == 1:
            base = 0
            v = rng.randrange(1 << 33)
            s = rng.choice(["%d" % v, "0%o" % v, "0x%x" % v, "0X%X" % v])
        else:
            base = rng.choice([0, 8, 10, 16])
            s = "".join(rng.choice(alpha) for _ in range(rng.randrange(0, 12)))
        if rng.random() < 0.3:
            s = rng.choice(["+", "-", ""]) + s
        if rng.random() < 0.3:
            s += "\n"
        data = list(s.encode())
        for name, fn, signed, bits in (("u32", "to_u32", False, 32), ("s32", "to_s32", True, 32)):
            case("%s_%d" % (name, k), "r32(K.KStr.%s(%s, %d))" % (fn, bl(data), base), show(parse(s, base, signed, bits)))
        for name, fn, signed, bits in (("u64", "to_u64", False, 64), ("s64", "to_s64", True, 64)):
            case("%s_%d" % (name, k), "r64(K.KStr.%s(%s, %d))" % (fn, bl(data), base), show(parse(s, base, signed, bits)))
    # hex dumps
    for k in range(40):
        n = rng.randrange(0, 40)
        bs = bytes(rng.randrange(256) for _ in range(n))
        rs, gs = rng.choice([16, 32, 8]), rng.choice([1, 2, 4, 8, 3])
        asc, little = rng.random() < 0.7, rng.random() < 0.7
        b = lambda x: "True{}" if x else "False{}"
        case("hexdump_%d" % k, 'q(H.KStr.hex_dump_line(H.KDump{%dn, %dn, %s, %s}, %s))' % (rs, gs, b(asc), b(little), bl(bs)), "'" + hexline(bs, rs, gs, asc, little) + "'")
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("import Base\nimport ../../word64/word64.bend as W\nimport ../../bytes/bytes.bend as B\nimport ../kstr.bend as K\n"
                "import ../format.bend as F\nimport ../hexdump.bend as H\n\n")
        f.write(open(os.path.join(here, "helpers.bend")).read())
        # in parts of 200, so that no one def is too deep for the checker
        parts = [lines[i:i + 200] for i in range(0, len(lines), 200)]
        for i, p in enumerate(parts):
            f.write("\ndef part%d() -> IO(Unit):\n  do IO<Unit>:\n" % i + "\n".join(p) + "\n")
        f.write("\ndef main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join("    part%d()" % i for i in range(len(parts))) + "\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(map(str, expect)) + "\n")
    print(len(expect), "cases")


main()
