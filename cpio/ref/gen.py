#!/usr/bin/env python3
"""Differential test cases for bend-osdev-cpio.

There is no cpio tool to compare against, so this file holds a second,
independent encoder and decoder for the newc (070701) and crc (070702)
formats, written in Python from the cpio(5) manual page and the kernel's
initramfs buffer format documentation. It shares an author with the package,
so it is a weaker reference than a third-party tool would be.

Writes ref/cases.bend (a Bend program) and ref/expected.txt (what it must
print), in both directions:
  * build: random entry lists in either format; Bend's Cpio.build must give
    the bytes this encoder gives;
  * parse: archives from this encoder, written with either case of hex digit
    and sometimes padded to a 512-byte block, and corrupted copies of them
    (truncated, a bad magic, a non-hex digit, a zero name size, a missing
    NUL, changed data); Bend's Cpio.parse must give the entries, or the
    error, this decoder gives.
"""
import os, random, sys

TRAILER = b"TRAILER!!!"


def pad4(n):
    return (4 - n % 4) % 4


def encode_entry(fmt, e, upper=True):
    ino, mode, uid, gid, nlink, mtime, dmaj, dmin, rmaj, rmin, name, data = e
    check = (sum(data) & 0xFFFFFFFF) if fmt == "crc" else 0
    fields = [ino, mode, uid, gid, nlink, mtime, len(data), dmaj, dmin, rmaj, rmin, len(name) + 1, check]
    digits = "".join(("%08X" if upper else "%08x") % f for f in fields)
    out = (b"070702" if fmt == "crc" else b"070701") + digits.encode() + name + b"\0"
    out += b"\0" * pad4(len(out))
    out += data + b"\0" * pad4(len(data))
    return out


def encode(fmt, entries, upper=True):
    out = b"".join(encode_entry(fmt, e, upper) for e in entries)
    return out + encode_entry(fmt, (0, 0, 0, 0, 1, 0, 0, 0, 0, 0, TRAILER, b""), upper)


class Bad(Exception):
    pass


def decode(buf):
    """The entries before the trailer, or raise Bad(error name)."""
    pos, entries = 0, []
    while True:
        if pos == len(buf):
            raise Bad("no trailer")
        if len(buf) - pos < 6:
            raise Bad("truncated")
        magic = buf[pos:pos + 6]
        if magic not in (b"070701", b"070702"):
            raise Bad("bad magic")
        pos += 6
        fields = []
        for _ in range(13):
            text = buf[pos:pos + 8]
            if len(text) < 8:
                raise Bad("truncated")
            if any(c not in b"0123456789abcdefABCDEF" for c in text):
                raise Bad("bad hex")
            fields.append(int(text, 16))
            pos += 8
        ino, mode, uid, gid, nlink, mtime, filesize, dmaj, dmin, rmaj, rmin, namesize, check = fields
        if namesize == 0:
            raise Bad("bad name size")
        name = buf[pos:pos + namesize - 1]
        if len(name) < namesize - 1:
            raise Bad("truncated")
        pos += namesize - 1
        if pos >= len(buf):
            raise Bad("truncated")
        if buf[pos] != 0:
            raise Bad("no nul")
        pos += 1
        if name == TRAILER:
            return entries
        pos += pad4(110 + namesize)
        if pos > len(buf):
            raise Bad("truncated")
        data = buf[pos:pos + filesize]
        if len(data) < filesize:
            raise Bad("truncated")
        pos += filesize + pad4(filesize)
        if pos > len(buf):
            raise Bad("truncated")
        if magic == b"070702" and sum(data) & 0xFFFFFFFF != check:
            raise Bad("bad checksum")
        entries.append((ino, mode, uid, gid, nlink, mtime, dmaj, dmin, rmaj, rmin, name, data))


def summary(buf):
    try:
        es = decode(buf)
    except Bad as b:
        return "error: " + b.args[0]
    return "ok" + "".join(" %s;%s;%s" % (",".join(str(f) for f in e[:10]), e[10].hex(), e[11].hex()) for e in es)


NAMECHARS = b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789/._-"
MODES = [0o100644, 0o100755, 0o040755, 0o120777, 0o020666, 0o060660, 0o010644, 0o140755]


def rand_entry(rng):
    def u32():
        return rng.choice([0, 1, rng.randrange(1 << 16), rng.randrange(1 << 32), 0xFFFFFFFF])
    name = bytes(rng.choice(NAMECHARS) for _ in range(rng.randrange(1, 24)))
    if rng.random() < 0.1:
        name = bytes([rng.randrange(1, 256)]) + name  # a byte outside ASCII
    n = rng.choice([0, 0, 1, 2, 3, 4, rng.randrange(5, 40), rng.randrange(40, 160)])
    data = bytes(rng.randrange(256) for _ in range(n))
    mode = rng.choice(MODES) if rng.random() < 0.8 else u32()
    return (u32(), mode, u32(), u32(), rng.choice([1, 2, u32()]), u32(), u32(), u32(), u32(), u32(), name, data)


def bend_bytes(b):
    return "B.Octets.of_list([" + ", ".join(str(x) for x in b) + "])"


def bend_entry(e):
    return "C.CpioEntry{%s, %s, %s}" % (", ".join(str(f) for f in e[:10]), bend_bytes(e[10]), bend_bytes(e[11]))


def corrupt(rng, fmt, entries, buf):
    """A malformed copy of buf, and a word for what was done."""
    kind = rng.choice(["truncate", "magic", "hex", "namesize", "nul", "data", "trailer"])
    if kind == "truncate":
        return buf[:rng.randrange(len(buf))]
    if kind == "magic":
        b = bytearray(buf)
        b[rng.randrange(6)] = rng.choice(b"3489x")
        return bytes(b)
    if kind == "hex":
        b = bytearray(buf)
        b[6 + rng.randrange(104)] = rng.choice(b"gGxz -")
        return bytes(b)
    if kind == "trailer":  # stop just before the trailer
        return encode(fmt, entries)[:-len(encode_entry(fmt, (0, 0, 0, 0, 1, 0, 0, 0, 0, 0, TRAILER, b"")))]
    if not entries:
        return buf[:-1]
    if kind == "namesize":  # the first entry's namesize field becomes 0
        return buf[:94] + b"00000000" + buf[102:]
    if kind == "nul":  # the first entry's NUL becomes a letter
        ns = int(buf[94:102], 16)
        b = bytearray(buf)
        b[110 + ns - 1] = ord("x")
        return bytes(b)
    # change a byte of the first entry's data (crc: a bad checksum)
    ns, fs = int(buf[94:102], 16), int(buf[54:62], 16)
    if fs == 0:
        return buf[:-3]
    b = bytearray(buf)
    at = 110 + ns + pad4(110 + ns) + rng.randrange(fs)
    b[at] = (b[at] + 1 + rng.randrange(255)) % 256
    return bytes(b)


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    lines, expect = [], []
    builds = [[]] + [[rand_entry(rng) for _ in range(rng.randrange(1, 4))] for _ in range(39)]
    for k, es in enumerate(builds):
        fmt = rng.choice(["newc", "crc"])
        out = encode(fmt, es)
        assert decode(out) == es, "the reference decoder disagrees with its encoder"
        ctor = "C.CpioCrc{}" if fmt == "crc" else "C.CpioNewc{}"
        lines.append('    IO.print("build %d " ++ B.Octets.hex(C.Cpio.build(%s, [%s])))' % (k, ctor, ", ".join(bend_entry(e) for e in es)))
        expect.append("build %d %s" % (k, out.hex()))
    for k in range(60):
        fmt = rng.choice(["newc", "crc"])
        es = [rand_entry(rng) for _ in range(rng.randrange(0, 4))]
        buf = encode(fmt, es, upper=rng.random() < 0.5)
        if rng.random() < 0.3:
            buf += b"\0" * pad4(len(buf))
            buf += b"\0" * ((512 - len(buf) % 512) % 512)
        if k % 2 == 1:
            buf = corrupt(rng, fmt, es, buf)
        else:
            assert decode(buf) == es
        lines.append('    IO.print("parse %d " ++ show(C.Cpio.parse(%s)))' % (k, bend_bytes(buf)))
        expect.append("parse %d %s" % (k, summary(buf)))
    with open(os.path.join(here, "cases.bend"), "w", newline="\n") as f:
        f.write(PRELUDE)
        f.write("def main() -> IO(Unit):\n  do IO<Unit>:\n" + "\n".join(lines) + "\n")
    with open(os.path.join(here, "expected.txt"), "w", newline="\n") as f:
        f.write("\n".join(expect) + "\n")
    print(len(expect), "cases")


PRELUDE = '''import Base
import ../../bytes/bytes.bend as B
import ../cpio.bend as C

def err(e: C.CpioError) -> String:
  match e:
    case C.CpioTruncated{}:
      "truncated"
    case C.CpioBadMagic{}:
      "bad magic"
    case C.CpioBadHex{}:
      "bad hex"
    case C.CpioBadNameSize{}:
      "bad name size"
    case C.CpioNoNul{}:
      "no nul"
    case C.CpioBadChecksum{}:
      "bad checksum"
    case C.CpioNoTrailer{}:
      "no trailer"

def entry(e: C.CpioEntry) -> String:
  match e:
    case C.CpioEntry{ino, mode, uid, gid, nlink, mtime, dmaj, dmin, rmaj, rmin, name, data}:
      U32.show(ino) ++ "," ++ U32.show(mode) ++ "," ++ U32.show(uid) ++ "," ++ U32.show(gid) ++ "," ++ U32.show(nlink) ++ "," ++ U32.show(mtime) ++ "," ++ U32.show(dmaj) ++ "," ++ U32.show(dmin) ++ "," ++ U32.show(rmaj) ++ "," ++ U32.show(rmin) ++ ";" ++ B.Octets.hex(name) ++ ";" ++ B.Octets.hex(data)

def entries(es: List<&2, C.CpioEntry>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{e, t}:
      " " ++ entry(e) ++ entries(t)

def show(m: Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>) -> String:
  match m:
    case Fail{e}:
      "error: " ++ err(e)
    case Done{es}:
      "ok" ++ entries(es)

'''

main()
