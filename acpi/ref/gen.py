#!/usr/bin/env python3
"""Differential test cases for bend-osdev-acpi.

An independent reader and writer of the ACPI tables and of AML, and an
independent AML evaluator for the programs it generates, written here from
the ACPI Specification 6.5 (and the HPET and PCI Firmware specifications
for those tables). It shares an author with the package, so it catches
slips of implementation, not a shared misreading.

  python3 gen.py SEED          writes cases.txt and expected.txt
  python3 gen.py SEED --tables DIR   also reads every *.dat / table file
                               in DIR (acpidump -b output, or
                               /sys/firmware/acpi/tables) as real tables
  python3 gen.py SEED --iasl   also compiles the ASL programs below with
                               iasl (a black box) and checks their results

Each line of cases.txt is a case for runner.bend; each line of expected.txt
is what the runner must print for it.
"""
import os, random, shutil, struct, subprocess, sys, tempfile

U64 = (1 << 64) - 1
U32 = (1 << 32) - 1

def le(n, v):
    return (v & ((1 << (8 * n)) - 1)).to_bytes(n, "little")

def u(b, off, n):
    """an n-byte little-endian field; zero where the bytes end"""
    chunk = b[off:off + n]
    chunk = chunk + bytes(n - len(chunk)) if off < len(b) else bytes(n)
    return int.from_bytes(chunk[:n], "little")

def hx(b):
    return bytes(b).hex()

def w64(v):
    return "%016x" % (v & U64)

def checksum(b):
    return sum(b) & 255

def fix(b, i):
    b = bytearray(b)
    b[i] = 0
    b[i] = (256 - checksum(b)) & 255
    return bytes(b)

# ---------------------------------------------------------------------------
# Tables (ACPI 6.5 chapter 5)

def header(sig, length, rev, oem=b"BENDOS", tid=b"REFTEST ", orev=1, cid=b"REF ", crev=1):
    return sig + le(4, length) + bytes([rev, 0]) + oem[:6].ljust(6, b" ") + tid[:8].ljust(8, b" ") + le(4, orev) + cid[:4].ljust(4, b" ") + le(4, crev)

def table(sig, rev, body, **kw):
    t = header(sig, 36 + len(body), rev, **kw) + body
    return fix(t, 9)

def gas(space, width, off, acc, addr):
    return bytes([space, width, off, acc]) + le(8, addr)

def show_gas(b, i):
    return "{%d %d %d %d %s}" % (u(b, i, 1), u(b, i + 1, 1), u(b, i + 2, 1), u(b, i + 3, 1), w64(u(b, i + 4, 8)))

class Bad(Exception):
    pass

def sdt_check(o):
    """the checks every table passes (header.bend: AcpiSdt.check)"""
    if len(o) < 8:
        raise Bad("TooShort 36 %d" % len(o))
    n = u(o, 4, 4)
    if not (36 <= n <= len(o)):
        raise Bad("BadLength %d" % n)
    raw = o[:n]
    if checksum(raw) != 0:
        raise Bad("BadChecksum %d" % checksum(raw))
    return raw

def entries(body, off0):
    """type/length structures (entries.bend)"""
    out, off = [], 0
    while off < len(body):
        k = body[off]
        l = body[off + 1] if off + 1 < len(body) else 0
        if l < 2 or off + l > len(body):
            raise Bad("BadEntry %d %d" % (off0 + off, k))
        out.append((k, off0 + off, body[off:off + l]))
        off += l
    return out

MADT_MIN = {0: 8, 1: 12, 2: 10, 3: 8, 4: 6, 5: 12, 9: 16, 10: 12, 11: 76, 12: 24, 13: 24, 14: 16, 15: 20, 16: 16}

def madt_entry(k, off, d):
    if len(d) < MADT_MIN.get(k, 2):
        raise Bad("BadEntry %d %d" % (off, k))
    if k == 0:
        return "lapic %d %d %d" % (u(d, 2, 1), u(d, 3, 1), u(d, 4, 4))
    if k == 1:
        return "ioapic %d %d %d" % (u(d, 2, 1), u(d, 4, 4), u(d, 8, 4))
    if k == 2:
        return "iso %d %d %d %d" % (u(d, 2, 1), u(d, 3, 1), u(d, 4, 4), u(d, 8, 2))
    if k == 3:
        return "nmisrc %d %d" % (u(d, 2, 2), u(d, 4, 4))
    if k == 4:
        return "lapicnmi %d %d %d" % (u(d, 2, 1), u(d, 3, 2), u(d, 5, 1))
    if k == 5:
        return "override " + w64(u(d, 4, 8))
    if k == 9:
        return "x2apic %d %d %d" % (u(d, 4, 4), u(d, 8, 4), u(d, 12, 4))
    if k == 10:
        return "x2nmi %d %d %d" % (u(d, 2, 2), u(d, 4, 4), u(d, 8, 1))
    if k == 11:
        return "gicc %d %d %d %d %d %d %s %s %s %s %s %s %d %d %d" % (
            u(d, 4, 4), u(d, 8, 4), u(d, 12, 4), u(d, 16, 4), u(d, 20, 4), u(d, 56, 4),
            w64(u(d, 24, 8)), w64(u(d, 32, 8)), w64(u(d, 40, 8)), w64(u(d, 48, 8)), w64(u(d, 60, 8)),
            w64(u(d, 68, 8)), u(d, 76, 1), u(d, 78, 2), u(d, 80, 2))
    if k == 12:
        return "gicd %d %s %d" % (u(d, 4, 4), w64(u(d, 8, 8)), u(d, 20, 1))
    if k == 13:
        return "gicmsi %d %s %d %d %d" % (u(d, 4, 4), w64(u(d, 8, 8)), u(d, 16, 4), u(d, 20, 2), u(d, 22, 2))
    if k == 14:
        return "gicr %s %d" % (w64(u(d, 4, 8)), u(d, 12, 4))
    if k == 15:
        return "gicits %d %s" % (u(d, 4, 4), w64(u(d, 8, 8)))
    if k == 16:
        return "wakeup %d %s" % (u(d, 2, 2), w64(u(d, 8, 8)))
    return "other %d %s" % (k, hx(d[2:]))

def madt_dump(o):
    raw = sdt_check(o)
    if raw[:4] != b"APIC":
        raise Bad("BadSignature " + hx(raw[:4]))
    body = raw[36:]
    if len(body) < 8:
        raise Bad("TooShort 44 %d" % (36 + len(body)))
    es = [madt_entry(k, off, d) for k, off, d in entries(body[8:], 44)]
    return "MADT %d %d [%s]" % (u(body, 0, 4), u(body, 4, 4), "; ".join(es))

SRAT_MIN = {0: 16, 1: 40, 2: 24, 3: 18, 4: 12, 5: 32, 6: 32}

def srat_entry(k, off, d):
    if len(d) < SRAT_MIN.get(k, 2):
        raise Bad("BadEntry %d %d" % (off, k))
    if k == 0:
        dom = u(d, 2, 1) | (u(d, 9, 3) << 8)
        return "lapic %d %d %d %d %d" % (dom, u(d, 3, 1), u(d, 4, 4), u(d, 8, 1), u(d, 12, 4))
    if k == 1:
        return "mem %d %s %s %d" % (u(d, 2, 4), w64(u(d, 8, 8)), w64(u(d, 16, 8)), u(d, 28, 4))
    if k == 2:
        return "x2apic %d %d %d %d" % (u(d, 4, 4), u(d, 8, 4), u(d, 12, 4), u(d, 16, 4))
    if k == 3:
        return "gicc %d %d %d %d" % (u(d, 2, 4), u(d, 6, 4), u(d, 10, 4), u(d, 14, 4))
    if k == 4:
        return "its %d %d" % (u(d, 2, 4), u(d, 8, 4))
    if k in (5, 6):
        return "gen %d %d %d %s %d" % (k, u(d, 3, 1), u(d, 4, 4), hx(d[8:24]), u(d, 24, 4))
    return "other %d %s" % (k, hx(d[2:]))

def srat_dump(o):
    raw = sdt_check(o)
    if raw[:4] != b"SRAT":
        raise Bad("BadSignature " + hx(raw[:4]))
    body = raw[36:]
    if len(body) < 12:
        raise Bad("TooShort 48 %d" % (36 + len(body)))
    es = [srat_entry(k, off, d) for k, off, d in entries(body[12:], 48)]
    return "SRAT [%s]" % "; ".join(es)

def fadt_dump(o):
    raw = sdt_check(o)
    if raw[:4] != b"FACP":
        raise Bad("BadSignature " + hx(raw[:4]))
    if len(raw) < 116:
        raise Bad("TooShort 116 %d" % len(raw))
    b = raw
    core_fields = [(36, 4), (40, 4), (44, 1), (45, 1), (46, 2), (48, 4), (52, 1), (53, 1), (54, 1), (55, 1),
                   (56, 4), (60, 4), (64, 4), (68, 4), (72, 4), (76, 4), (80, 4), (84, 4),
                   (88, 1), (89, 1), (90, 1), (91, 1), (92, 1), (93, 1), (94, 1), (95, 1),
                   (96, 2), (98, 2), (100, 2), (102, 2), (104, 1), (105, 1), (106, 1), (107, 1), (108, 1), (109, 2), (112, 4)]
    core = ",".join(str(u(b, i, n)) for i, n in core_fields)
    n = len(b)
    if n >= 244:
        ext = ",".join([show_gas(b, 116), str(u(b, 128, 1)), str(u(b, 129, 2)), str(u(b, 131, 1)), w64(u(b, 132, 8)), w64(u(b, 140, 8))] + [show_gas(b, 148 + 12 * i) for i in range(8)])
    else:
        ext = "none"
    sleep = show_gas(b, 244) + "," + show_gas(b, 256) if n >= 268 else "none"
    hyp = w64(u(b, 268, 8)) if n >= 276 else "none"
    dsdt = u(b, 40, 4)
    facs = u(b, 36, 4)
    pm1a = "{1 %d 0 0 %s}" % ((u(b, 88, 1) * 8) & 255, w64(u(b, 56, 4)))
    if n >= 244:
        if u(b, 140, 8):
            dsdt = u(b, 140, 8)
        if u(b, 132, 8):
            facs = u(b, 132, 8)
        if u(b, 148 + 4, 8):
            pm1a = show_gas(b, 148)
    return "FADT %s ext %s sleep %s hyp %s dsdt %s facs %s pm1a %s" % (core, ext, sleep, hyp, w64(dsdt), w64(facs), pm1a)

def hpet_dump(o):
    raw = sdt_check(o)
    if raw[:4] != b"HPET":
        raise Bad("BadSignature " + hx(raw[:4]))
    if len(raw) < 56:
        raise Bad("TooShort 56 %d" % len(raw))
    return "HPET %d %s %d %d %d" % (u(raw, 36, 4), show_gas(raw, 40), u(raw, 52, 1), u(raw, 53, 2), u(raw, 55, 1))

def mcfg_dump(o):
    raw = sdt_check(o)
    if raw[:4] != b"MCFG":
        raise Bad("BadSignature " + hx(raw[:4]))
    body = raw[36:]
    if len(body) < 8 or (len(body) - 8) % 16:
        raise Bad("BadSize %d" % len(body))
    es = []
    for i in range(8, len(body), 16):
        es.append("%s %d %d %d" % (w64(u(body, i, 8)), u(body, i + 8, 2), u(body, i + 10, 1), u(body, i + 11, 1)))
    return "MCFG [%s]" % "; ".join(es)

def slit_dump(o):
    raw = sdt_check(o)
    if raw[:4] != b"SLIT":
        raise Bad("BadSignature " + hx(raw[:4]))
    body = raw[36:]
    if len(body) < 8:
        raise Bad("TooShort 44 %d" % (36 + len(body)))
    n = u(body, 0, 8)
    if n >= 65536 or 8 + n * n > len(body):
        raise Bad("BadSize %d" % len(body))
    return "SLIT %d %s" % (n, hx(body[8:8 + n * n]))

def bgrt_dump(o):
    raw = sdt_check(o)
    if raw[:4] != b"BGRT":
        raise Bad("BadSignature " + hx(raw[:4]))
    if len(raw) < 56:
        raise Bad("TooShort 56 %d" % len(raw))
    return "BGRT %d %d %d %s %d %d" % (u(raw, 36, 2), u(raw, 38, 1), u(raw, 39, 1), w64(u(raw, 40, 8)), u(raw, 48, 4), u(raw, 52, 4))

def sdtlist_dump(o, sig, w):
    raw = sdt_check(o)
    if raw[:4] != sig:
        raise Bad("BadSignature " + hx(raw[:4]))
    body = raw[36:]
    if len(body) % w:
        raise Bad("BadSize %d" % len(body))
    return "SDT [%s]" % ",".join(w64(u(body, i, w)) for i in range(0, len(body), w))

def rsdp_dump(o):
    if len(o) < 20:
        raise Bad("TooShort 20 %d" % len(o))
    if o[:8] != b"RSD PTR ":
        raise Bad("BadSignature " + hx(o[:8]))
    if checksum(o[:20]):
        raise Bad("RsdpBadChecksum %d" % checksum(o[:20]))
    rev = o[15]
    if rev < 2:
        ext = "none"
    else:
        if len(o) < 36:
            raise Bad("TooShort 36 %d" % len(o))
        n = u(o, 20, 4)
        if not (36 <= n <= len(o)):
            raise Bad("BadLength %d" % n)
        if checksum(o[:n]):
            raise Bad("RsdpBadExtChecksum %d" % checksum(o[:n]))
        ext = "%d %s" % (n, w64(u(o, 24, 8)))
    return "RSDP %s %d %d %s" % (hx(o[9:15]), rev, u(o, 16, 4), ext)

# the registry's default dispatch (registry.bend)
REGISTRY = {b"APIC": madt_dump, b"FACP": fadt_dump, b"HPET": hpet_dump, b"MCFG": mcfg_dump, b"SRAT": srat_dump,
            b"SLIT": slit_dump, b"BGRT": bgrt_dump,
            b"RSDT": lambda o: sdtlist_dump(o, b"RSDT", 4), b"XSDT": lambda o: sdtlist_dump(o, b"XSDT", 8)}

def registry_dump(o):
    try:
        raw = sdt_check(o)
        sig = raw[:4]
        if sig in (b"DSDT", b"SSDT"):
            return "AML %d" % (len(raw) - 36)
        if sig in REGISTRY:
            return REGISTRY[sig](raw)
        return "RAW %d" % (len(raw) - 36)
    except Bad as e:
        return str(e)

# Random tables

def rnd_bytes(r, n):
    return bytes(r.randrange(256) for _ in range(n))

def rnd_madt_entry(r):
    k = r.choice([0, 0, 1, 2, 3, 4, 5, 9, 10, 11, 12, 13, 14, 15, 16, 7, 0x80])
    lens = {0: 8, 1: 12, 2: 10, 3: 8, 4: 6, 5: 12, 9: 16, 10: 12, 11: r.choice([76, 80, 82]), 12: 24, 13: 24, 14: 16, 15: 20, 16: 16}
    n = lens.get(k, r.randrange(2, 20))
    return bytes([k, n]) + rnd_bytes(r, n - 2)

def rnd_srat_entry(r):
    k = r.choice([0, 1, 1, 2, 3, 4, 5, 6, 9])
    lens = {0: 16, 1: 40, 2: 24, 3: 18, 4: 12, 5: 32, 6: 32}
    n = lens.get(k, r.randrange(2, 20))
    return bytes([k, n]) + rnd_bytes(r, n - 2)

def rnd_table(r):
    kind = r.choice(["madt", "madt", "fadt", "hpet", "mcfg", "srat", "slit", "bgrt", "xsdt", "rsdt", "raw"])
    if kind == "madt":
        body = le(4, r.randrange(1 << 32)) + le(4, r.randrange(2)) + b"".join(rnd_madt_entry(r) for _ in range(r.randrange(0, 8)))
        return table(b"APIC", 5, body)
    if kind == "fadt":
        n = r.choice([116, 244, 268, 276])
        return table(b"FACP", r.choice([1, 3, 5, 6]), rnd_bytes(r, n - 36))
    if kind == "hpet":
        return table(b"HPET", 1, rnd_bytes(r, 20))
    if kind == "mcfg":
        return table(b"MCFG", 1, bytes(8) + b"".join(rnd_bytes(r, 16) for _ in range(r.randrange(0, 4))))
    if kind == "srat":
        return table(b"SRAT", 3, le(4, 1) + bytes(8) + b"".join(rnd_srat_entry(r) for _ in range(r.randrange(0, 6))))
    if kind == "slit":
        n = r.randrange(0, 6)
        return table(b"SLIT", 1, le(8, n) + rnd_bytes(r, n * n))
    if kind == "bgrt":
        return table(b"BGRT", 1, rnd_bytes(r, 20))
    if kind == "xsdt":
        return table(b"XSDT", 1, b"".join(le(8, r.randrange(1 << 64)) for _ in range(r.randrange(0, 5))))
    if kind == "rsdt":
        return table(b"RSDT", 1, b"".join(le(4, r.randrange(1 << 32)) for _ in range(r.randrange(0, 5))))
    return table(b"OEM1", 1, rnd_bytes(r, r.randrange(0, 30)))

def corrupt(r, t):
    how = r.choice(["checksum", "length", "truncate", "entry", "sig"])
    t = bytearray(t)
    if how == "checksum":
        i = r.randrange(36, len(t)) if len(t) > 36 else 10
        t[i] ^= 1 + r.randrange(255)
    elif how == "length":
        v = r.choice([0, 35, len(t) + 1 + r.randrange(100)])
        t[4:8] = le(4, v)
        t = bytearray(fix(t, 9))
    elif how == "truncate":
        t = t[:r.randrange(0, len(t))]
    elif how == "entry" and t[:4] in (b"APIC", b"SRAT") and len(t) > 50:
        start = 44 if t[:4] == b"APIC" else 48
        if len(t) > start + 2:
            t[start + 1] = r.choice([0, 1, 255])
            t = bytearray(fix(t, 9))
    else:
        t[0:4] = b"APIX" if t[:4] == b"APIC" else t[0:4]
        t = bytearray(fix(t, 9))
    return bytes(t)

def rnd_rsdp(r):
    rev = r.choice([0, 2, 2])
    first = b"RSD PTR " + b"\0" + rnd_bytes(r, 6) + bytes([rev]) + le(4, r.randrange(1 << 32))
    first = fix(first, 8)
    if rev < 2:
        o = first
    else:
        o = fix(first + le(4, 36) + le(8, r.randrange(1 << 64)) + b"\0" + bytes(3), 32)
    if r.random() < 0.3:
        o = bytearray(o)
        o[r.randrange(len(o))] ^= 0x10
        o = bytes(o)
    return o

# ---------------------------------------------------------------------------
# AML encoding (ACPI 6.5 chapter 20)

def pkglength_value(v, size=None):
    """the PkgLength encoding of v (in the given number of bytes, else the
    shortest)"""
    if size is None:
        size = 1 if v < 64 else 2 if v < 4096 else 3 if v < (1 << 20) else 4
    if size == 1:
        assert v < 64
        return bytes([v])
    lead = ((size - 1) << 6) | (v & 15)
    return bytes([lead] + [(v >> (4 + 8 * i)) & 255 for i in range(size - 1)])

def pkg(body):
    """a package: its PkgLength (counting itself) and its contents"""
    n = len(body)
    for size in (1, 2, 3, 4):
        if (size == 1 and n + 1 < 64) or (size == 2 and n + 2 < 4096) or (size == 3 and n + 3 < (1 << 20)) or size == 4:
            return pkglength_value(n + size, size) + body

def pkglength_decode(b):
    if not b:
        return "AmlTruncated"
    lead = b[0]
    count = lead >> 6
    if count == 0:
        return "%d rest %s" % (lead & 63, hx(b[1:]))
    if lead & 0x30:
        return "AmlBadPkgLength"
    if len(b) < 1 + count:
        return "AmlTruncated"
    v = lead & 15
    for i in range(count):
        v |= b[1 + i] << (4 + 8 * i)
    return "%d rest %s" % (v, hx(b[1 + count:]))

LEAD = set(b"ABCDEFGHIJKLMNOPQRSTUVWXYZ_")
NAMECH = LEAD | set(b"0123456789")
BACKSLASH = chr(92)

def seg(s):
    s = s[:4]
    return (s + "_" * (4 - len(s))).encode()

def name_parse(text):
    """(root, up, segments) from text: a backslash for the root, carets for
    parents, segments separated by dots"""
    root = text.startswith(BACKSLASH)
    t = text[1:] if root else text
    up = 0
    while not root and t.startswith("^"):
        up += 1
        t = t[1:]
    segs = [seg(p) for p in t.split(".")] if t else []
    return root, up, segs

def name_encode(text):
    root, up, segs = name_parse(text)
    pre = b"\x5c" if root else b"^" * up
    if not segs:
        path = b"\0"
    elif len(segs) == 1:
        path = segs[0]
    elif len(segs) == 2:
        path = b"." + segs[0] + segs[1]
    else:
        path = b"/" + bytes([len(segs)]) + b"".join(segs)
    return pre + path

def name_show(root, up, segs):
    return (BACKSLASH if root else "^" * up) + ".".join(s.decode() for s in segs)

def seg_ok(s):
    return len(s) == 4 and s[0] in LEAD and all(c in NAMECH for c in s[1:])

def name_decode(b):
    """the NameString at the front of b, and the rest (aml_name.bend)"""
    i = 0
    root = False
    up = 0
    if i < len(b) and b[i] == 0x5C:
        root = True
        i += 1
    else:
        while i < len(b) and b[i] == 0x5E:
            up += 1
            i += 1
    if i >= len(b):
        return "AmlTruncated"
    c = b[i]
    if c == 0:
        return "%s rest %s" % (name_show(root, up, []), hx(b[i + 1:]))
    if c == 0x2E:
        n, i = 2, i + 1
    elif c == 0x2F:
        if i + 1 >= len(b):
            return "AmlTruncated"
        n, i = b[i + 1], i + 2
        if n == 0:
            return "AmlBadName"
    elif c in LEAD:
        n = 1
    else:
        return "AmlBadName"
    segs = []
    for _ in range(n):
        s = b[i:i + 4]
        if len(s) < 4:
            return "AmlTruncated"
        if not seg_ok(s):
            return "AmlBadName"
        segs.append(s)
        i += 4
    return "%s rest %s" % (name_show(root, up, segs), hx(b[i:]))

def aml_int(v):
    v &= U64
    if v == 0:
        return b"\0"
    if v == 1:
        return b"\1"
    if v == U64:
        return b"\xff"
    if v < 256:
        return b"\x0a" + le(1, v)
    if v < 65536:
        return b"\x0b" + le(2, v)
    if v < (1 << 32):
        return b"\x0c" + le(4, v)
    return b"\x0e" + le(8, v)

# Programs: expressions and statements as tuples, encoded and evaluated here
#   ("int", v) ("str", s) ("arg", i) ("local", i) ("name", path)
#   ("op", opcode, a, b)        Add .. XOr, Mod: Target NullName
#   ("un", opcode, a)           Not, FindSetLeftBit, FindSetRightBit
#   ("div", a, b)               Divide, both targets NullName: the quotient
#   ("lnot", a) ("land", a, b) ("lor", a, b) ("cmp", opcode, a, b)
#   ("call", path, [args])
#   ("pkg", [elements]) ("buf", bytes) ("elem", pkg-expr, index)   DerefOf(Index(...))
#   ("size", expr) ("concat", a, b) ("toint", a)
# statements:
#   ("store", expr, target)  target: ("local", i) or ("name", path)
#   ("opt", opcode, a, b, target)   an operator with its result in target
#   ("inc", target) ("dec", target) ("if", cond, [then], [else]) ("ret", expr)
#   ("loop", local, count, [body])  Store(0, L); While (LLess(L, count)) { body; Increment(L) }

OPS = {"add": 0x72, "sub": 0x74, "mul": 0x77, "shl": 0x79, "shr": 0x7A, "and": 0x7B, "nand": 0x7C, "or": 0x7D, "nor": 0x7E, "xor": 0x7F, "mod": 0x85}
NONE = b"\0"

def enc_target(t):
    if t[0] == "local":
        return bytes([0x60 + t[1]])
    if t[0] == "name":
        return name_encode(t[1])
    raise ValueError(t)

def enc(e):
    k = e[0]
    if k == "int":
        return aml_int(e[1])
    if k == "str":
        return b"\x0d" + e[1].encode() + b"\0"
    if k == "arg":
        return bytes([0x68 + e[1]])
    if k == "local":
        return bytes([0x60 + e[1]])
    if k == "name":
        return name_encode(e[1])
    if k == "op":
        return bytes([e[1]]) + enc(e[2]) + enc(e[3]) + NONE
    if k == "un":
        return bytes([e[1]]) + enc(e[2]) + NONE
    if k == "div":
        return b"\x78" + enc(e[1]) + enc(e[2]) + NONE + NONE
    if k == "lnot":
        return b"\x92" + enc(e[1])
    if k == "land":
        return b"\x90" + enc(e[1]) + enc(e[2])
    if k == "lor":
        return b"\x91" + enc(e[1]) + enc(e[2])
    if k == "cmp":
        return bytes([e[1]]) + enc(e[2]) + enc(e[3])
    if k == "call":
        return name_encode(e[1]) + b"".join(enc(a) for a in e[2])
    if k == "pkg":
        return b"\x12" + pkg(bytes([len(e[1])]) + b"".join(enc(x) for x in e[1]))
    if k == "buf":
        return b"\x11" + pkg(aml_int(len(e[1])) + e[1])
    if k == "elem":
        return b"\x83\x88" + enc(e[1]) + enc(e[2]) + NONE
    if k == "size":
        return b"\x87" + enc(e[1])
    if k == "concat":
        return b"\x73" + enc(e[1]) + enc(e[2]) + NONE
    if k == "toint":
        return b"\x99" + enc(e[1]) + NONE
    raise ValueError(e)

def enc_stmt(s):
    k = s[0]
    if k == "store":
        return b"\x70" + enc(s[1]) + enc_target(s[2])
    if k == "opt":
        return bytes([s[1]]) + enc(s[2]) + enc(s[3]) + enc_target(s[4])
    if k == "inc":
        return b"\x75" + enc_target(s[1])
    if k == "dec":
        return b"\x76" + enc_target(s[1])
    if k == "if":
        out = b"\xa0" + pkg(enc(s[1]) + b"".join(enc_stmt(x) for x in s[2]))
        if s[3] is not None:
            out += b"\xa1" + pkg(b"".join(enc_stmt(x) for x in s[3]))
        return out
    if k == "ret":
        return b"\xa4" + enc(s[1])
    if k == "loop":
        l, n, body = s[1], s[2], s[3]
        return b"\x70\x00" + bytes([0x60 + l]) + b"\xa2" + pkg(b"\x95" + bytes([0x60 + l]) + aml_int(n) + b"".join(enc_stmt(x) for x in body) + b"\x75" + bytes([0x60 + l]))
    raise ValueError(s)

def enc_method(name, nargs, body):
    return b"\x14" + pkg(name_encode(name) + bytes([nargs]) + b"".join(enc_stmt(s) for s in body))

def enc_name(name, e):
    return b"\x08" + name_encode(name) + enc(e)

# Evaluation (chapter 19 for what each operator does; 19.3.5.7 for the
# conversions)

class AmlError(Exception):
    pass

class Return(Exception):
    def __init__(self, v):
        self.v = v

def fit(wide, v):
    return v & (U64 if wide else U32)

def to_int(wide, v):
    k = v[0]
    if k == "int":
        return fit(wide, v[1])
    if k == "buf":
        n = 8 if wide else 4
        return int.from_bytes(v[1][:n].ljust(n, b"\0"), "little")
    if k == "str":
        digits = 16 if wide else 8
        acc = 0
        for c in v[1][:digits]:
            ch = chr(c)
            if ch in "0123456789abcdefABCDEF":
                acc = acc * 16 + int(ch, 16)
            else:
                break
        return acc
    raise AmlError("AmlBadType")

def to_str(wide, v):
    k = v[0]
    if k == "str":
        return v[1]
    if k == "int":
        return ("%0*X" % (16 if wide else 8, fit(wide, v[1]))).encode()
    if k == "buf":
        return " ".join("%02X" % c for c in v[1]).encode()
    raise AmlError("AmlBadType")

def to_buf(wide, v):
    k = v[0]
    if k == "buf":
        return v[1]
    if k == "int":
        return le(8 if wide else 4, v[1])
    if k == "str":
        return v[1] + b"\0"
    raise AmlError("AmlBadType")

def cmp_values(wide, a, b):
    if a[0] == "int":
        x, y = fit(wide, a[1]), to_int(wide, b)
    elif a[0] == "str":
        x, y = a[1], to_str(wide, b)
    elif a[0] == "buf":
        x, y = a[1], to_buf(wide, b)
    else:
        raise AmlError("AmlBadType")
    return (x > y) - (x < y)

def fsb(x, left):
    if x == 0:
        return 0
    if left:
        return x.bit_length()
    return (x & -x).bit_length()

def op2(wide, op, x, y):
    if op == 0x72:
        return fit(wide, x + y)
    if op == 0x74:
        return fit(wide, x - y)
    if op == 0x77:
        return fit(wide, x * y)
    if op == 0x79:
        return 0 if y >= 64 else fit(wide, x << y)
    if op == 0x7A:
        return 0 if y >= 64 else x >> y
    if op == 0x7B:
        return x & y
    if op == 0x7C:
        return fit(wide, ~(x & y))
    if op == 0x7D:
        return x | y
    if op == 0x7E:
        return fit(wide, ~(x | y))
    if op == 0x7F:
        return x ^ y
    if op == 0x85:
        if y == 0:
            raise AmlError("AmlDivZero")
        return x % y
    raise ValueError(op)

class Machine:
    def __init__(self, wide, methods, names):
        self.wide = wide
        self.methods = methods
        self.names = dict(names)

    def ones(self):
        return U64 if self.wide else U32

    def ev(self, e, env):
        k = e[0]
        w = self.wide
        if k == "int":
            return ("int", fit(w, e[1]))
        if k == "str":
            return ("str", e[1].encode())
        if k == "arg":
            return env["args"][e[1]] if e[1] < len(env["args"]) else ("uninit",)
        if k == "local":
            return env["locals"].get(e[1], ("uninit",))
        if k == "name":
            if e[1] not in self.names:
                raise AmlError("AmlUndefined " + e[1])
            return self.names[e[1]]
        if k == "op":
            x = to_int(w, self.ev(e[2], env))
            y = to_int(w, self.ev(e[3], env))
            return ("int", op2(w, e[1], x, y))
        if k == "un":
            x = to_int(w, self.ev(e[2], env))
            if e[1] == 0x80:
                return ("int", fit(w, ~x))
            return ("int", fsb(x, e[1] == 0x81))
        if k == "div":
            x = to_int(w, self.ev(e[1], env))
            y = to_int(w, self.ev(e[2], env))
            if y == 0:
                raise AmlError("AmlDivZero")
            return ("int", x // y)
        if k == "lnot":
            return ("int", 0 if to_int(w, self.ev(e[1], env)) else self.ones())
        if k in ("land", "lor"):
            x = to_int(w, self.ev(e[1], env)) != 0
            y = to_int(w, self.ev(e[2], env)) != 0
            r = (x and y) if k == "land" else (x or y)
            return ("int", self.ones() if r else 0)
        if k == "cmp":
            a = self.ev(e[2], env)
            b = self.ev(e[3], env)
            c = cmp_values(w, a, b)
            r = {0x93: c == 0, 0x94: c > 0, 0x95: c < 0}[e[1]]
            return ("int", self.ones() if r else 0)
        if k == "call":
            args = [self.ev(a, env) for a in e[2]]
            return self.call(e[1], args)
        if k == "pkg":
            return ("pkg", [self.ev(x, env) for x in e[1]])
        if k == "buf":
            return ("buf", e[1])
        if k == "elem":
            p = self.ev(e[1], env)
            i = to_int(w, self.ev(e[2], env))
            if p[0] == "pkg":
                if i >= len(p[1]):
                    raise AmlError("AmlRange")
                return p[1][i]
            if p[0] in ("buf", "str"):
                if i >= len(p[1]):
                    raise AmlError("AmlRange")
                return ("int", p[1][i])
            raise AmlError("AmlBadType")
        if k == "size":
            v = self.ev(e[1], env)
            if v[0] in ("str", "buf", "pkg"):
                return ("int", len(v[1]))
            raise AmlError("AmlBadType")
        if k == "concat":
            a = self.ev(e[1], env)
            b = self.ev(e[2], env)
            if a[0] == "int":
                return ("buf", to_buf(w, a) + le(8 if w else 4, to_int(w, b)))
            if a[0] == "str":
                return ("str", a[1] + to_str(w, b))
            if a[0] == "buf":
                return ("buf", a[1] + to_buf(w, b))
            raise AmlError("AmlBadType")
        if k == "toint":
            v = self.ev(e[1], env)
            if v[0] == "str":
                s = v[1]
                if s[:2] in (b"0x", b"0X"):
                    return ("int", fit(w, to_int(w, ("str", s[2:]))))
                acc = 0
                for c in s[:20]:
                    if 48 <= c <= 57:
                        acc = acc * 10 + c - 48
                    else:
                        break
                return ("int", fit(w, acc & U64))
            return ("int", to_int(w, v))
        raise ValueError(e)

    def store(self, t, v, env):
        if t[0] == "local":
            env["locals"][t[1]] = v
        else:
            if t[1] not in self.names:
                raise AmlError("AmlUndefined " + t[1])
            old = self.names[t[1]]
            if old[0] == "int":
                v = ("int", to_int(self.wide, v))
            elif old[0] == "str":
                v = ("str", to_str(self.wide, v))
            elif old[0] == "buf":
                b = to_buf(self.wide, v)
                n = len(old[1])
                v = ("buf", b[:n].ljust(n, b"\0"))
            self.names[t[1]] = v

    def read(self, t, env):
        if t[0] == "local":
            return env["locals"].get(t[1], ("uninit",))
        return self.ev(t, env)

    def run(self, ss, env):
        for s in ss:
            k = s[0]
            if k == "store":
                self.store(s[2], self.ev(s[1], env), env)
            elif k == "opt":
                x = to_int(self.wide, self.ev(s[2], env))
                y = to_int(self.wide, self.ev(s[3], env))
                self.store(s[4], ("int", op2(self.wide, s[1], x, y)), env)
            elif k in ("inc", "dec"):
                x = to_int(self.wide, self.read(s[1], env))
                self.store(s[1], ("int", fit(self.wide, x + (1 if k == "inc" else -1))), env)
            elif k == "if":
                if to_int(self.wide, self.ev(s[1], env)):
                    self.run(s[2], env)
                elif s[3] is not None:
                    self.run(s[3], env)
            elif k == "ret":
                raise Return(self.ev(s[1], env))
            elif k == "loop":
                env["locals"][s[1]] = ("int", 0)
                while to_int(self.wide, env["locals"][s[1]]) < s[2]:
                    self.run(s[3], env)
                    env["locals"][s[1]] = ("int", fit(self.wide, to_int(self.wide, env["locals"][s[1]]) + 1))
            else:
                raise ValueError(s)

    def call(self, path, args):
        nargs, body = self.methods[path]
        env = {"args": args, "locals": {}}
        try:
            self.run(body, env)
        except Return as r:
            return r.v
        return ("uninit",)

def show_value(v):
    k = v[0]
    if k == "int":
        return "0x%x" % v[1]
    if k == "str":
        return '"' + v[1].decode("latin-1") + '"'
    if k == "buf":
        return "buf[" + " ".join("%02x" % c for c in v[1]) + "]"
    if k == "pkg":
        return "{" + ", ".join(show_value(x) for x in v[1]) + "}"
    return "uninit"

# ---------------------------------------------------------------------------
# Random programs

def rnd_int(r):
    return r.choice([0, 1, 2, 7, 255, 256, 4096, 65535, 65536, U32, 1 << 32, U64, r.randrange(1 << 64), r.randrange(1 << 16), r.randrange(1 << 8)])

def rnd_expr(r, depth, nargs, locs):
    """an Integer expression; locs: the Locals assigned so far"""
    choices = ["int", "int", "op", "op", "un", "logic", "cmp", "div"]
    if nargs:
        choices += ["arg", "arg"]
    if locs:
        choices += ["local", "local"]
    if depth <= 0:
        choices = [c for c in choices if c in ("int", "arg", "local")]
    k = r.choice(choices)
    if k == "int":
        return ("int", rnd_int(r))
    if k == "arg":
        return ("arg", r.randrange(nargs))
    if k == "local":
        return ("local", r.choice(sorted(locs)))
    sub = lambda: rnd_expr(r, depth - 1, nargs, locs)
    if k == "op":
        op = r.choice(list(OPS.values()))
        b = ("int", r.randrange(70)) if op in (0x79, 0x7A) else sub()
        if op == 0x85 and r.random() < 0.8:
            b = ("int", 1 + r.randrange(1000))
        return ("op", op, sub(), b)
    if k == "un":
        return ("un", r.choice([0x80, 0x81, 0x82]), sub())
    if k == "logic":
        return r.choice([("lnot", sub()), ("land", sub(), sub()), ("lor", sub(), sub())])
    if k == "cmp":
        return ("cmp", r.choice([0x93, 0x94, 0x95]), sub(), sub())
    if k == "div":
        return ("div", sub(), ("int", 1 + r.randrange(100)) if r.random() < 0.9 else sub())
    raise ValueError(k)

def rnd_body(r, depth, nargs, locs, loop_ok=True):
    ss = []
    for _ in range(r.randrange(1, 4)):
        k = r.choice(["store", "store", "opt", "inc", "if", "loop"] if depth > 0 else ["store", "opt", "inc"])
        if k == "store":
            l = r.randrange(0, 5)
            ss.append(("store", rnd_expr(r, 2, nargs, locs), ("local", l)))
            locs.add(l)
        elif k == "opt":
            l = r.randrange(0, 5)
            op = r.choice([0x72, 0x74, 0x7B, 0x7D, 0x7F])
            ss.append(("opt", op, rnd_expr(r, 1, nargs, locs), rnd_expr(r, 1, nargs, locs), ("local", l)))
            locs.add(l)
        elif k == "inc" and locs - {7}:
            ss.append((r.choice(["inc", "dec"]), ("local", r.choice(sorted(locs - {7})))))
        elif k == "if":
            then_locs, else_locs = set(locs), set(locs)
            then = rnd_body(r, depth - 1, nargs, then_locs, loop_ok)
            els = rnd_body(r, depth - 1, nargs, else_locs, loop_ok) if r.random() < 0.5 else None
            ss.append(("if", rnd_expr(r, 1, nargs, locs), then, els))
            locs |= then_locs & (else_locs if els is not None else locs)
        elif k == "loop" and loop_ok:
            body_locs = set(locs)
            body = rnd_body(r, depth - 1, nargs, body_locs, False)
            ss.append(("loop", 7, r.randrange(0, 6), body))
            locs |= {7}
    return ss

def rnd_program(r):
    """a definition block: a helper method, data Names, and TEST"""
    nargs = r.randrange(0, 3)
    methods = {}
    hb = [("ret", ("op", r.choice([0x72, 0x77, 0x7F]), ("arg", 0), ("arg", 1)))]
    methods[BACKSLASH + "HLP1"] = (2, hb)
    names = {BACKSLASH + "NUM0": ("int", rnd_int(r)), BACKSLASH + "STR0": ("str", b"ab"), BACKSLASH + "BUF0": ("buf", rnd_bytes(r, 4))}
    locs = set()
    body = rnd_body(r, 2, nargs, locs)
    tail = r.choice(["expr", "call", "pkg", "name", "str", "buf", "size"])
    if tail == "expr":
        ret = rnd_expr(r, 3, nargs, locs)
    elif tail == "call":
        ret = ("call", BACKSLASH + "HLP1", [rnd_expr(r, 1, nargs, locs), rnd_expr(r, 1, nargs, locs)])
    elif tail == "pkg":
        ret = ("pkg", [rnd_expr(r, 1, nargs, locs) for _ in range(r.randrange(0, 4))] + [("str", "x")])
        if r.random() < 0.5:
            ret = ("elem", ret, ("int", r.randrange(len(ret[1]) + 1)))
    elif tail == "name":
        body.append(("store", rnd_expr(r, 1, nargs, locs), ("name", BACKSLASH + "NUM0")))
        ret = ("op", 0x72, ("name", BACKSLASH + "NUM0"), ("int", 1))
    elif tail == "str":
        ret = ("concat", ("name", BACKSLASH + "STR0"), r.choice([("str", "cd"), rnd_expr(r, 1, nargs, locs)]))
    elif tail == "buf":
        body.append(("store", rnd_expr(r, 1, nargs, locs), ("name", BACKSLASH + "BUF0")))
        ret = ("concat", ("name", BACKSLASH + "BUF0"), ("buf", rnd_bytes(r, 2)))
    else:
        ret = ("size", r.choice([("str", "hello"), ("buf", rnd_bytes(r, 5)), ("pkg", [("int", 1), ("int", 2)])]))
    body.append(("ret", ret))
    methods[BACKSLASH + "TEST"] = (nargs, body)
    aml = b"".join(enc_name(n, (v[0], v[1].decode() if v[0] == "str" else v[1])) for n, v in names.items())
    aml += enc_method(BACKSLASH + "HLP1", 2, hb) + enc_method(BACKSLASH + "TEST", nargs, body)
    args = [("int", rnd_int(r)) for _ in range(nargs)]
    return aml, methods, names, args

def run_program(wide, methods, names, args):
    m = Machine(wide, methods, names)
    try:
        args = [("int", fit(wide, a[1])) for a in args]
        return show_value(m.call(BACKSLASH + "TEST", args))
    except AmlError as e:
        return str(e)

# Fields over SystemMemory (19.6.48; 5.5.2.4): accesses of the access width,
# read-modify-write by the update rule

ACC = {0: 1, 1: 1, 2: 2, 3: 4, 4: 8, 5: 1}

def field_read(mem, base, off, bits, acc):
    w = ACC[acc]
    v = 0
    for k in range(off // (8 * w), (off + bits - 1) // (8 * w) + 1):
        unit = int.from_bytes(bytes(mem.get(base + k * w + i, 0) for i in range(w)), "little")
        lo, hi = max(off, 8 * w * k), min(off + bits, 8 * w * (k + 1))
        part = (unit >> (lo - 8 * w * k)) & ((1 << (hi - lo)) - 1)
        v |= part << (lo - off)
    return v

def field_write(mem, base, off, bits, acc, rule, x):
    w = ACC[acc]
    for k in range(off // (8 * w), (off + bits - 1) // (8 * w) + 1):
        lo, hi = max(off, 8 * w * k), min(off + bits, 8 * w * (k + 1))
        n, s = hi - lo, lo - 8 * w * k
        hole = ((1 << n) - 1) << s
        piece = ((x >> (lo - off)) & ((1 << n) - 1)) << s
        if n == 8 * w:
            old = 0
        elif rule == 1:
            old = (1 << (8 * w)) - 1
        elif rule == 2:
            old = 0
        else:
            old = int.from_bytes(bytes(mem.get(base + k * w + i, 0) for i in range(w)), "little")
        new = (old & ~hole & ((1 << (8 * w)) - 1)) | piece
        for i in range(w):
            mem[base + k * w + i] = (new >> (8 * i)) & 255

def rnd_field_case(r):
    base = 0x1000
    size = 16
    acc = r.choice([0, 1, 2, 3, 4])
    rule = r.choice([0, 1, 2])
    w = ACC[acc]
    fields, off, elems = [], 0, b""
    while len(fields) < r.randrange(2, 5):
        if r.random() < 0.2:
            skip = r.randrange(1, 9)
            elems += b"\0" + pkglength_value(skip)
            off += skip
        bits = r.choice([1, 3, 4, 8, 12, 16, 32, r.randrange(1, 40)])
        if off + bits > size * 8:
            break
        name = "F%03d" % len(fields)
        fields.append((name, off, bits))
        elems += name.encode() + pkglength_value(bits)
        off += bits
    if len(fields) < 2:
        return None
    region = b"\x5b\x80" + name_encode("RAM0") + bytes([0]) + aml_int(base) + aml_int(size)
    flags = (acc & 15) | (rule << 5)
    field = b"\x5b\x81" + pkg(name_encode("RAM0") + bytes([flags]) + elems)
    wr, rd = r.choice(fields), r.choice(fields)
    x = r.randrange(1 << 64)
    body = enc_stmt(("store", ("int", x), ("name", wr[0]))) + enc_stmt(("ret", ("name", rd[0])))
    aml = region + field + b"\x14" + pkg(name_encode("TEST") + b"\0" + body)
    init = rnd_bytes(r, size)
    mem = {base + i: init[i] for i in range(size)}
    field_write(mem, base, wr[1], wr[2], acc, rule, x & ((1 << wr[2]) - 1) if wr[2] < 64 else x)
    got = field_read(mem, base, rd[1], rd[2], acc)
    after = bytes(mem[base + i] for i in range(size))
    return aml, init, "0x%x %s" % (got, hx(after))

# Resource templates (6.4)

def res_rnd(r):
    k = r.choice(["irq", "irq2", "dma", "io", "fio", "m32", "m32f", "w16", "d32", "q64", "xirq"])
    if k == "irq":
        m, f = r.randrange(65536), r.randrange(256)
        return bytes([0x23]) + le(2, m) + bytes([f]), "irq mask %d flags %d" % (m, f)
    if k == "irq2":
        m = r.randrange(65536)
        return bytes([0x22]) + le(2, m), "irq mask %d flags 1" % m, bytes([0x23]) + le(2, m) + bytes([1])
    if k == "dma":
        m, f = r.randrange(256), r.randrange(256)
        return bytes([0x2A, m, f]), "dma mask %d flags %d" % (m, f)
    if k == "io":
        dc, mn, mx, al, l = r.randrange(2), r.randrange(65536), r.randrange(65536), r.randrange(256), r.randrange(256)
        return bytes([0x47, dc]) + le(2, mn) + le(2, mx) + bytes([al, l]), "io %d-%d align %d len %d" % (mn, mx, al, l)
    if k == "fio":
        b, l = r.randrange(65536), r.randrange(256)
        return bytes([0x4B]) + le(2, b) + bytes([l]), "fixed io %d len %d" % (b, l)
    if k == "m32":
        wr, mn, mx, al, l = r.randrange(2), r.randrange(1 << 32), r.randrange(1 << 32), r.randrange(1 << 32), r.randrange(1 << 32)
        return bytes([0x85]) + le(2, 17) + bytes([wr]) + le(4, mn) + le(4, mx) + le(4, al) + le(4, l), "mem32 %d-%d len %d" % (mn, mx, l)
    if k == "m32f":
        wr, b, l = r.randrange(2), r.randrange(1 << 32), r.randrange(1 << 32)
        return bytes([0x86]) + le(2, 9) + bytes([wr]) + le(4, b) + le(4, l), "mem32 fixed %d len %d" % (b, l)
    if k in ("w16", "d32", "q64"):
        width = {"w16": 2, "d32": 4, "q64": 8}[k]
        tag = {"w16": 0x88, "d32": 0x87, "q64": 0x8A}[k]
        kind, gf, tf = r.randrange(3), r.randrange(16), r.randrange(256)
        vals = [r.randrange(1 << (8 * width)) for _ in range(5)]
        d = bytes([kind, gf, tf]) + b"".join(le(width, v) for v in vals)
        return bytes([tag]) + le(2, len(d)) + d, "addr%d type %d %s-%s len %s" % (8 * width, kind, w64(vals[1]), w64(vals[2]), w64(vals[4]))
    n = r.randrange(1, 4)
    f = r.randrange(32)
    irqs = [r.randrange(1 << 32) for _ in range(n)]
    d = bytes([f, n]) + b"".join(le(4, i) for i in irqs)
    return bytes([0x89]) + le(2, len(d)) + d, "extirq flags %d %s" % (f, ",".join(str(i) for i in irqs))

def res_case(r):
    """a template, its descriptors as text, and the template as the package
    writes it (an IRQ descriptor always in its 3-byte form)"""
    parts = [res_rnd(r) for _ in range(r.randrange(0, 5))]
    o = b"".join(p[0] for p in parts) + b"\x79\x00"
    canon = b"".join(p[2] if len(p) > 2 else p[0] for p in parts) + b"\x79\x00"
    return o, "; ".join(p[1] for p in parts), canon

# Physical memory with an RSDP leading to tables (acpi.bend: AcpiTables.load)

def rnd_machine(r):
    base = 0x200000
    blobs, addr = [], base
    def place(t):
        nonlocal addr
        a = addr
        blobs.append((a, t))
        addr += (len(t) + 15) // 16 * 16 + 16 * r.randrange(0, 4)
        return a
    facs = b"FACS" + le(4, 64) + rnd_bytes(r, 24) + bytes([2]) + bytes(27)
    dsdt = table(b"DSDT", 2, b"\x08" + name_encode("ABCD") + aml_int(5))
    a_facs = place(facs)
    a_dsdt = place(dsdt)
    fadt_body = bytearray(rnd_bytes(r, 276 - 36))
    fadt_body[0:4] = le(4, a_facs)
    fadt_body[4:8] = le(4, a_dsdt)
    fadt_body[132 - 36:140 - 36] = le(8, 0)
    fadt_body[140 - 36:148 - 36] = le(8, a_dsdt if r.random() < 0.5 else 0)
    listed = [("FACP", place(table(b"FACP", 6, bytes(fadt_body))))]
    for _ in range(r.randrange(1, 4)):
        t = rnd_table(r)
        if t[:4] in (b"XSDT", b"RSDT", b"FACP"):
            continue
        if r.random() < 0.2:
            t = corrupt(r, t)
        listed.append((t[:4].decode("latin-1"), place(t)))
    xsdt = table(b"XSDT", 1, b"".join(le(8, a) for n, a in listed))
    a_xsdt = place(xsdt)
    rsdp = fix(fix(b"RSD PTR " + b"\0" + b"BENDOS" + bytes([2]) + le(4, 0), 8) + le(4, 36) + le(8, a_xsdt) + b"\0" + bytes(3), 32)
    image = bytearray(addr - base)
    for a, t in blobs:
        image[a - base:a - base + len(t)] = t
    lines = []
    for n, a in listed + [("DSDT", a_dsdt)]:
        # the loader reads a table's first 8 bytes, then as many bytes as
        # its length field says (acpi.bend: AcpiTables.read_table)
        length = u(image, a - base + 4, 4)
        if a - base + length > len(image):
            lines.append("%s NotMapped %s" % (w64(a), w64(a)))
            continue
        o = bytes(image[a - base:a - base + length])
        lines.append("%s %s" % (w64(a), registry_name(o)))
    return rsdp, base, bytes(image), ", ".join(lines) + "; FACS ok"

def registry_name(o):
    """the parser that reads a table, or its error (registry.bend)"""
    d = registry_dump(o)
    if d.startswith("RAW") or d.startswith("AML"):
        return o[:4].decode("latin-1")
    for k, n in (("MADT", "APIC"), ("FADT", "FACP"), ("HPET", "HPET"), ("MCFG", "MCFG"), ("SRAT", "SRAT"), ("SLIT", "SLIT"), ("BGRT", "BGRT")):
        if d.startswith(k + " "):
            return n
    if d.startswith("SDT"):
        return o[:4].decode("latin-1")
    return d

# ---------------------------------------------------------------------------
# The same programs written with the package's builder (aml_term.bend), so
# that its encoding is compared byte for byte. The runner builds them from
# tokens in postfix order (runner.bend: rpn.*): a term's operands, then the
# term.

def hname(s):
    return s.encode().hex()

def rterm(e, out):
    k = e[0]
    if k == "int":
        out.append("i:%d:%d" % ((e[1] >> 32) & U32, e[1] & U32))
    elif k == "str":
        out.append("s:" + e[1].encode().hex())
    elif k == "arg":
        out.append("a:%d" % e[1])
    elif k == "local":
        out.append("l:%d" % e[1])
    elif k == "name":
        out.append("n:" + hname(e[1]))
    elif k == "op":
        rterm(e[2], out)
        rterm(e[3], out)
        out.append("none")
        out.append("op:%d:3" % e[1])
    elif k == "un":
        rterm(e[2], out)
        out.append("none")
        out.append("op:%d:2" % e[1])
    elif k == "div":
        rterm(e[1], out)
        rterm(e[2], out)
        out.append("div")
    elif k == "lnot":
        rterm(e[1], out)
        out.append("lnot")
    elif k in ("land", "lor"):
        rterm(e[1], out)
        rterm(e[2], out)
        out.append(k)
    elif k == "cmp":
        rterm(e[2], out)
        rterm(e[3], out)
        out.append("op:%d:2" % e[1])
    elif k == "call":
        for a in e[2]:
            rterm(a, out)
        out.append("call:%s:%d" % (hname(e[1]), len(e[2])))
    elif k == "pkg":
        for x in e[1]:
            rterm(x, out)
        out.append("pkg:%d" % len(e[1]))
    elif k == "buf":
        out.append("buf:" + hx(e[1]))
    elif k == "elem":
        rterm(e[1], out)
        rterm(e[2], out)
        out.append("elem")
    elif k in ("size", "toint"):
        rterm(e[1], out)
        out.append(k)
    elif k == "concat":
        rterm(e[1], out)
        rterm(e[2], out)
        out.append("concat")
    else:
        raise ValueError(e)

def rstmts(ss, out):
    n = 0
    for s in ss:
        n += rstmt(s, out)
    return n

def rstmt(s, out):
    """the tokens of a statement; how many terms it leaves (a loop is two)"""
    k = s[0]
    if k == "store":
        rterm(s[1], out)
        rterm(s[2], out)
        out.append("store")
    elif k == "opt":
        rterm(s[2], out)
        rterm(s[3], out)
        rterm(s[4], out)
        out.append("op:%d:3" % s[1])
    elif k in ("inc", "dec"):
        rterm(s[1], out)
        out.append(k)
    elif k == "if":
        rterm(s[1], out)
        n1 = rstmts(s[2], out)
        if s[3] is None:
            out.append("if:%d" % n1)
        else:
            n2 = rstmts(s[3], out)
            out.append("ifelse:%d:%d" % (n1, n2))
    elif k == "ret":
        rterm(s[1], out)
        out.append("ret")
    elif k == "loop":
        l, cnt, body = s[1], s[2], s[3]
        out += ["zero", "l:%d" % l, "store"]
        out += ["l:%d" % l, "i:%d:%d" % ((cnt >> 32) & U32, cnt & U32), "op:149:2"]
        n = rstmts(body, out)
        out += ["l:%d" % l, "inc"]
        out.append("while:%d" % (n + 1))
        return 2
    else:
        raise ValueError(s)
    return 1

def rprogram(methods, names):
    out = []
    for n, v in names.items():
        rterm((v[0], v[1].decode()) if v[0] == "str" else v, out)
        out.append("name:" + hname(n))
    for p in (BACKSLASH + "HLP1", BACKSLASH + "TEST"):
        nargs, body = methods[p]
        n = rstmts(body, out)
        out.append("method:%s:%d:%d" % (hname(p), nargs, n))
    return " ".join(out)

# ---------------------------------------------------------------------------
# Real tables (acpidump -b output, or /sys/firmware/acpi/tables): each read
# through the registry, and the DSDT and SSDTs loaded, with the devices
# they define listed. The Python side finds devices by walking the
# definition blocks (Scope, Device, Processor, PowerResource, ThermalZone),
# without running any code.

def walk_devices(aml, scope, out):
    """the Devices (and Processors, PowerResources, ThermalZones) a term
    list defines, found without running it: Scope and the device terms are
    entered, the other common terms (Name, Method, OperationRegion, Field,
    If, Else, While, External, Alias, Mutex, Event) are stepped over, and the
    walk of a list stops at any other term (so it finds a subset)"""
    n = len(aml)
    def name_at(j):
        root = False
        up = 0
        k = j
        if k < n and aml[k] == 0x5C:
            root = True
            k += 1
        while k < n and aml[k] == 0x5E:
            up += 1
            k += 1
        c = aml[k] if k < n else 0
        if c == 0:
            return root, up, [], k + 1
        if c == 0x2E:
            return root, up, [aml[k + 1:k + 5], aml[k + 5:k + 9]], k + 9
        if c == 0x2F:
            cnt = aml[k + 1] if k + 1 < n else 0
            return root, up, [aml[k + 2 + 4 * s:k + 6 + 4 * s] for s in range(cnt)], k + 2 + 4 * cnt
        return root, up, [aml[k:k + 4]], k + 4
    def path(root, up, segs):
        p = [] if root else list(scope)
        for _ in range(up):
            if p:
                p.pop()
        return p + [s.decode("latin-1") for s in segs]
    def pkglen(j):
        lead = aml[j]
        cnt = lead >> 6
        if cnt == 0:
            return lead & 63, j + 1
        v = lead & 15
        for s in range(cnt):
            v |= aml[j + 1 + s] << (4 + 8 * s)
        return v, j + 1 + cnt
    def data(j):
        """the end of a constant data object at j, or None"""
        c = aml[j]
        if c in (0x00, 0x01, 0xFF):
            return j + 1
        size = {0x0A: 2, 0x0B: 3, 0x0C: 5, 0x0E: 9}.get(c)
        if size:
            return j + size
        if c == 0x0D:
            return aml.index(0, j + 1) + 1
        if c in (0x11, 0x12, 0x13):
            v, _ = pkglen(j + 1)
            return j + 1 + v
        return None
    i = 0
    while i < n:
        op = aml[i]
        ext = aml[i + 1] if op == 0x5B and i + 1 < n else None
        if op == 0x10 or ext in (0x82, 0x83, 0x84, 0x85):
            start = i + (2 if ext is not None else 1)
            v, j = pkglen(start)
            end = start + v
            root, up, segs, j2 = name_at(j)
            p = path(root, up, segs)
            if ext is not None:
                out.append(p)
                j2 += {0x82: 0, 0x83: 6, 0x84: 3, 0x85: 0}[ext]
            walk_devices(aml[j2:end], p, out)
            i = end
        elif op in (0x14, 0xA0, 0xA1, 0xA2) or ext in (0x81, 0x86, 0x87):
            start = i + (2 if ext is not None else 1)
            v, _ = pkglen(start)
            i = start + v
        elif op == 0x08:
            _, _, _, j = name_at(i + 1)
            e = data(j)
            if e is None:
                return
            i = e
        elif ext == 0x80:
            _, _, _, j = name_at(i + 2)
            e1 = data(j + 1)
            e2 = data(e1) if e1 is not None else None
            if e2 is None:
                return
            i = e2
        elif op == 0x15:
            _, _, _, j = name_at(i + 1)
            i = j + 2
        elif op == 0x06:
            _, _, _, j = name_at(i + 1)
            _, _, _, i = name_at(j)
        elif ext == 0x01:
            _, _, _, j = name_at(i + 2)
            i = j + 1
        elif ext == 0x02:
            _, _, _, i = name_at(i + 2)
        else:
            return

def real_cases(d):
    """(label, path, expected) for each table file in d, and the devices"""
    out = []
    amls = []
    for f in sorted(os.listdir(d)):
        p = os.path.join(d, f)
        if not os.path.isfile(p):
            continue
        try:
            with open(p, "rb") as fh:
                o = fh.read()
        except OSError:
            continue
        if len(o) < 36 or o[:4] in (b"FACS", b"RSD "):
            continue
        out.append(("real " + f, p, registry_dump(o)))
        if o[:4] in (b"DSDT", b"SSDT") and sdt_ok(o):
            amls.append((0 if o[:4] == b"DSDT" else 1, p, o))
    amls.sort(key=lambda x: x[0])
    devs = []
    for _, p, o in amls:
        found = []
        walk_devices(o[36:u(o, 4, 4)], [], found)
        devs += [BACKSLASH + ".".join(x) for x in found]
    return out, [p for _, p, _ in amls], sorted(set(devs))

def sdt_ok(o):
    try:
        sdt_check(o)
        return True
    except Bad:
        return False

# ---------------------------------------------------------------------------
# ASL compiled by iasl (a black box): each program, its method, and what
# the method returns

ASL_PROGRAMS = [
    ("Method (TEST, 0) { Return (0x0F) }", "0xf"),
    ("Method (TEST, 0) { Local0 = 0\n Local1 = 0\n While (Local1 < 10) { Local0 += Local1\n Local1++ }\n Return (Local0) }", "0x2d"),
    ("Name (PKG0, Package () { 1, \"two\", Buffer () { 3 } })\nMethod (TEST, 0) { Return (DerefOf (PKG0 [1])) }", '"two"'),
    ("Method (TEST, 0) { Name (BUF0, ResourceTemplate () { IRQNoFlags () { 5 } })\n CreateWordField (BUF0, 1, IRQ0)\n IRQ0 = 0x80\n Return (BUF0) }", "buf[22 80 00 79 00]"),
    ("Method (HELP, 2) { Return (Arg0 * Arg1) }\nMethod (TEST, 0) { Return (HELP (6, 7)) }", "0x2a"),
    ("Method (TEST, 0) { If (_OSI (\"Windows 2015\")) { Return (1) } Return (0) }", "0x1"),
]

def iasl_cases(work):
    """compile each program with iasl; (label, aml bytes, expected)"""
    out = []
    for k, (body, want) in enumerate(ASL_PROGRAMS):
        src = os.path.join(work, "p%d.asl" % k)
        with open(src, "w") as f:
            f.write('DefinitionBlock ("", "DSDT", 2, "BENDOS", "REFTEST", 1)\n{\n%s\n}\n' % body)
        r = subprocess.run(["iasl", "-p", os.path.join(work, "p%d" % k), src], capture_output=True)
        aml_path = os.path.join(work, "p%d.aml" % k)
        if r.returncode != 0 or not os.path.exists(aml_path):
            raise SystemExit("iasl failed on program %d:\n%s" % (k, r.stdout.decode() + r.stderr.decode()))
        with open(aml_path, "rb") as f:
            t = f.read()
        out.append(("iasl %d" % k, t, want))
    return out

# ---------------------------------------------------------------------------
# The cases: one line of cases.txt each (kind|label|fields, read by
# runner.bend), and the line expected.txt says it prints

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    argv = sys.argv[1:]
    seed = int(argv[0]) if argv and argv[0].isdigit() else 2026
    tables_dir = argv[argv.index("--tables") + 1] if "--tables" in argv else None
    use_iasl = "--iasl" in argv
    r = random.Random(seed)
    lines, expect = [], []
    def case(kind, label, fields, want):
        lines.append("|".join([kind, label] + [str(f) for f in fields]))
        expect.append(label + " " + want)

    # checksums
    for k in range(10):
        o = rnd_bytes(r, r.randrange(0, 60))
        case("checksum", "checksum %d" % k, [hx(o)], str(checksum(o)))
    # tables, through the registry
    for k in range(70):
        t = rnd_table(r)
        if r.random() < 0.35:
            t = corrupt(r, t)
        case("table", "table %d" % k, [hx(t)], registry_dump(t))
    # headers: decoded and written back
    for k in range(8):
        t = rnd_table(r)
        case("header", "header %d" % k, [hx(t)], hx(t[:36]))
    # the RSDP
    for k in range(16):
        o = rnd_rsdp(r)
        try:
            want = rsdp_dump(o)
        except Bad as e:
            want = str(e)
        case("rsdp", "rsdp %d" % k, [hx(o)], want)
    # physical memory walks
    for k in range(5):
        rp, base, image, want = rnd_machine(r)
        case("machine", "machine %d" % k, [hx(rp), base, hx(image)], want)
    # PkgLength: the writer, and the reader on every form (shortest or not)
    for k in range(40):
        v = r.choice([0, 1, 63, 64, 4095, 4096, (1 << 20) - 1, 1 << 20, (1 << 28) - 1, r.randrange(1 << 28), r.randrange(4096)])
        case("pkenc", "pkglength enc %d" % k, [v], hx(pkglength_value(v)))
        fits = [s for s in (1, 2, 3, 4) if (s == 1 and v < 64) or (s > 1 and v < (1 << (4 + 8 * (s - 1))))]
        b = pkglength_value(v, r.choice(fits))
        rest = rnd_bytes(r, r.randrange(0, 3))
        if r.random() < 0.15 and b[0] >> 6:
            b = bytes([b[0] | 0x30]) + b[1:]
        if r.random() < 0.1:
            b = b[:-1]
            rest = b""
        case("pkdec", "pkglength dec %d" % k, [hx(b + rest)], pkglength_decode(b + rest))
    # NameStrings
    for k in range(40):
        root = r.random() < 0.4
        up = 0 if root else r.choice([0, 0, 1, 2])
        nseg = r.choice([0, 1, 1, 2, 2, 3, 4, 6])
        segs = []
        for _ in range(nseg):
            s = r.choice("ABCDEFGHIJKLMNOPQRSTUVWXYZ_") + "".join(r.choice("ABCDEFGHIJKLMNOPQRSTUVWXYZ_0123456789") for _ in range(3))
            segs.append(s)
        text = (BACKSLASH if root else "^" * up) + ".".join(segs)
        case("nameenc", "name enc %d" % k, [text.encode().hex()], hx(name_encode(text)))
        b = name_encode(text) + rnd_bytes(r, r.randrange(0, 3))
        if r.random() < 0.2:
            b = bytearray(b)
            b[r.randrange(len(b))] = r.choice([0x31, 0x20, 0x2E, 0x2F, 0x00, 0x7F])
            b = bytes(b)
        if r.random() < 0.1:
            b = b[:r.randrange(len(b))]
        case("namedec", "name dec %d" % k, [hx(b)], name_decode(b))
    # AML programs: run by the package, evaluated here; some also written
    # with the package's builder
    for k in range(60):
        aml, methods, names, args = rnd_program(r)
        wide = r.random() < 0.8
        sargs = ",".join("%d:%d" % ((a[1] >> 32) & U32, a[1] & U32) for a in args)
        case("aml", "aml %d" % k, ["1" if wide else "0", hx(aml), (BACKSLASH + "TEST").encode().hex(), sargs], run_program(wide, methods, names, args))
        if k < 30:
            case("build", "build %d" % k, [rprogram(methods, names)], hx(aml))
    # fields over SystemMemory
    k = 0
    while k < 25:
        c = rnd_field_case(r)
        if c is None:
            continue
        aml, init, want = c
        case("field", "field %d" % k, [hx(aml), hx(init)], want)
        k += 1
    # resource templates: read, shown, and written back
    for k in range(25):
        o, want, canon = res_case(r)
        case("res", "resource %d" % k, [hx(o)], want + " | " + hx(canon))
    n_real = n_iasl = 0
    if tables_dir:
        out, amls, devs = real_cases(tables_dir)
        for label, p, want in out:
            case("real", label, [os.path.abspath(p).encode().hex()], want)
        if amls:
            case("realdevs", "real devices", [",".join(os.path.abspath(p) for p in amls).encode().hex(), " ".join(devs).encode().hex()], "all %d found" % len(devs))
        n_real = len(out)
    if use_iasl:
        with tempfile.TemporaryDirectory() as work:
            for label, t, want in iasl_cases(work):
                case("iasl", label, [hx(t)], want)
                n_iasl += 1
    with open(os.path.join(here, "cases.txt"), "w", newline="\n") as f:
        f.write("\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print("%d cases (%d real tables, %d iasl programs)" % (len(expect), n_real, n_iasl))

main()
