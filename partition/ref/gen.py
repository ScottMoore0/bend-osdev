#!/usr/bin/env python3
"""Differential test cases for bend-osdev-partition.

  gen.py SEED DIR

Makes small disk images in DIR with sgdisk (GPT) and sfdisk (MBR), then
writes ref/cases.bend (a Bend program that reads the images' tables and
prints what the package parses, validates and rebuilds) and ref/expected.txt
(the same facts as the tools report them):
  * GPT: `sgdisk -p` (disk GUID, usable LBAs, table location and size) and
    `sgdisk -i` (each partition's type and unique GUID, first and last LBA,
    attributes, name), cross-checked against `sfdisk -J`; `sgdisk -v` for
    the CRCs of untouched images; the package's rebuilt header blocks and
    protective MBR must equal the bytes sgdisk wrote;
  * images with one byte of the primary header or of the entry array
    changed after sgdisk wrote them: the package must refuse that header
    (or that array), and Python's zlib must agree the stored CRC is wrong;
  * MBR: `sfdisk -J` (disk identifier, each partition's start, size, type
    and boot flag); the CHS fields are decoded here from the raw bytes, as
    the classic layout defines them; the rebuilt sector must equal sfdisk's.
"""
import json, os, random, struct, subprocess, sys, uuid, zlib

def run(*args):
    return subprocess.run(args, check=True, capture_output=True, text=True).stdout

NAMES = ["EFI system", "root", "home", "swap", "root ü", "données", "数据", "x" * 36, ""]
# (sgdisk does not print names outside the BMP correctly, so the UTF-16
# surrogate pairs are tested by vectors in LAWS.bend instead)
CODES = ["EF00", "8300", "0700", "8200", "EF02", "8E00", "FD00", "8302"]
ATTRS = [0, 1, 2, 60, 63]
SECTOR = 512

def sgdisk_info(img, n):
    out = run("sgdisk", "-i", str(n), img)
    info = {}
    for line in out.splitlines():
        if line.startswith("Partition GUID code:"):
            info["type"] = line.split(":", 1)[1].split()[0].lower()
        elif line.startswith("Partition unique GUID:"):
            info["uuid"] = line.split(":", 1)[1].strip().lower()
        elif line.startswith("First sector:"):
            info["first"] = int(line.split(":", 1)[1].split()[0])
        elif line.startswith("Last sector:"):
            info["last"] = int(line.split(":", 1)[1].split()[0])
        elif line.startswith("Attribute flags:"):
            info["attrs"] = line.split(":", 1)[1].strip().lower()
        elif line.startswith("Partition name:"):
            v = line.split(":", 1)[1].strip()
            info["name"] = v[1:-1]
    return info

def sgdisk_disk(img):
    out = run("sgdisk", "-p", img)
    d = {}
    for line in out.splitlines():
        if line.startswith("Disk ") and "sectors" in line and ":" in line:
            d["sectors"] = int(line.split(":", 1)[1].split()[0])
        elif line.startswith("Disk identifier (GUID):"):
            d["guid"] = line.split(":", 1)[1].strip().lower()
        elif line.startswith("Partition table holds up to"):
            d["count"] = int(line.split()[5])
        elif line.startswith("Main partition table begins at sector"):
            d["elba"] = int(line.split()[6])
        elif line.startswith("First usable sector is"):
            w = line.replace(",", "").split()
            d["first"], d["last"] = int(w[4]), int(w[9])
    return d

def flip(img, off):
    with open(img, "r+b") as f:
        f.seek(off)
        b = f.read(1)
        f.seek(off)
        f.write(bytes([b[0] ^ 1]))

def crc_ok_header(blk):
    size = struct.unpack("<I", blk[12:16])[0]
    h = bytearray(blk[:size]); h[16:20] = b"\0\0\0\0"
    return zlib.crc32(bytes(h)) == struct.unpack("<I", blk[16:20])[0]

def make_gpt(rng, d, k, corrupt):
    img = os.path.join(d, "g%d.img" % k)
    mib = rng.choice([3, 4, 6])
    with open(img, "wb") as f:
        f.truncate(mib * 1024 * 1024)
    disk = str(uuid.UUID(int=rng.getrandbits(128), version=4))
    args = ["sgdisk", "-a", "8", "-U", disk]
    n = rng.choice([1, 2, 3, 4, 4])
    start = 2048
    parts = []
    for i in range(1, n + 1):
        size = rng.randrange(8, 600)
        end = start + size - 1
        name = rng.choice(NAMES)
        args += ["-n", "%d:%d:%d" % (i, start, end), "-t", "%d:%s" % (i, rng.choice(CODES)),
                 "-u", "%d:%s" % (i, uuid.UUID(int=rng.getrandbits(128), version=4))]
        if name:
            args += ["-c", "%d:%s" % (i, name)]
        for b in rng.sample(ATTRS, rng.randrange(0, 3)):
            args += ["-A", "%d:set:%d" % (i, b)]
        parts.append(i)
        start = end + 1 + rng.randrange(0, 64) * 8
        start = (start + 7) // 8 * 8
    run(*(args + [img]))
    disk_info = sgdisk_disk(img)
    infos = [sgdisk_info(img, i) for i in parts]
    verify = run("sgdisk", "-v", img)
    assert "No problems found" in verify, verify
    sf = json.loads(run("sfdisk", "-J", img))["partitiontable"]
    assert sf["id"].lower() == disk_info["guid"]
    for p, info in zip(sf["partitions"], infos):
        assert p["start"] == info["first"] and p["size"] == info["last"] - info["first"] + 1
        assert p["type"].lower() == info["type"] and p["uuid"].lower() == info["uuid"]
        assert p.get("name", "") == info["name"]
    if corrupt == "header":
        flip(img, SECTOR + 20)  # the reserved field: no field changes, the CRC fails
    elif corrupt == "entries":
        flip(img, 2 * SECTOR + 127 * 128 + 40)  # inside the last (unused) entry
    with open(img, "rb") as f:
        raw = f.read()
    N = disk_info["sectors"]
    assert N * SECTOR == len(raw)
    lba1 = raw[SECTOR:2 * SECTOR]
    bak = raw[(N - 1) * SECTOR:N * SECTOR]
    ents = raw[2 * SECTOR:2 * SECTOR + 16384]
    bents = raw[(N - 33) * SECTOR:(N - 1) * SECTOR]
    pvalid = crc_ok_header(lba1)
    assert pvalid == (corrupt != "header")
    stored = lambda blk: struct.unpack("<I", blk[88:92])[0]
    pent = zlib.crc32(ents) == stored(lba1)
    bent = zlib.crc32(bents) == stored(bak)
    assert pent == (corrupt != "entries") and bent
    pre = "g%d" % k
    exp = []
    exp.append("%s scheme %s" % (pre, "gpt" if pvalid else "bad gpt: bad header CRC"))
    hdr = lambda my, alt, elba: "%d %d %d %d %s %d %d 128" % (my, alt, disk_info["first"], disk_info["last"], disk_info["guid"], elba, disk_info["count"])
    exp.append("%s primary %s %s" % (pre, hdr(1, N - 1, disk_info["elba"]), "valid" if pvalid else "bad header CRC"))
    exp.append("%s backup %s valid" % (pre, hdr(N - 1, 1, disk_info["last"] + 1)))
    exp.append("%s entries %s %s" % (pre, pent, bent))
    for i, info in zip(parts, infos):
        exp.append("%s p%d %s %s %d %d %s '%s'" % (pre, i, info["type"], info["uuid"], info["first"], info["last"], info["attrs"], info["name"]))
    exp.append("%s rebuild %s True True" % (pre, corrupt is None))
    call = '    u%s : Unit <- gpt_case("%s", "%s", %d)' % (pre, pre, img, (N - 1) * SECTOR)
    return call, exp

MBR_TYPES = [0x83, 0x07, 0x0C, 0x82, 0xEF, 0x8E, 0x0B, 0xDA]

def chs(b):
    return "%d/%d/%d" % (b[0], b[1] & 63, ((b[1] & 192) << 2) | b[2])

def make_mbr(rng, d, k):
    img = os.path.join(d, "m%d.img" % k)
    with open(img, "wb") as f:
        f.truncate(rng.choice([2, 3, 4]) * 1024 * 1024)
    ident = rng.getrandbits(32)
    lines = ["label: dos", "label-id: 0x%08x" % ident]
    start = 2048
    n = rng.randrange(1, 5)
    boot = rng.randrange(0, n + 1)  # n: no bootable partition
    for i in range(n):
        size = rng.randrange(8, 900)
        lines.append("start=%d, size=%d, type=%x%s" % (start, size, rng.choice(MBR_TYPES), ", bootable" if i == boot else ""))
        start += size + rng.randrange(0, 50)
    subprocess.run(["sfdisk", "-q", img], input="\n".join(lines) + "\n", check=True, capture_output=True, text=True)
    sf = json.loads(run("sfdisk", "-J", img))["partitiontable"]
    with open(img, "rb") as f:
        raw = f.read(512)
    pre = "m%d" % k
    exp = ["%s scheme mbr" % pre, "%s sig %d" % (pre, int(sf["id"], 16))]
    for i, p in enumerate(sf["partitions"]):
        rec = raw[446 + 16 * i:462 + 16 * i]
        assert struct.unpack("<II", rec[8:16]) == (p["start"], p["size"])
        exp.append("%s p%d %d %d %d %d %s %s" % (pre, i + 1, 128 if p.get("bootable") else 0, int(p["type"], 16), p["start"], p["size"], chs(rec[1:4]), chs(rec[5:8])))
    exp.append("%s rebuild True" % pre)
    call = '    u%s : Unit <- mbr_case("%s", "%s")' % (pre, pre, img)
    return call, exp

HEAD = r'''import Base
import ../../word64/word64.bend as W
import ../../bytes/bytes.bend as B
import ../../uuid/uuid.bend as U
import ../mbr.bend as M
import ../gpt.bend as G
import ../partition.bend as P

def got(m: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(B.Octets):
  (f, r) = m
  do IO<B.Octets>:
    xs : List<&2, U32> <- IO.pass(List<&2, U32>, r)
    u : Unit <- File.close(f)
    return B.Octets.of_list(xs)

def read_at(path: String, off: U32, n: U32) -> IO(B.Octets):
  do IO<B.Octets>:
    f : File <- IO.try(File, File.open(path, "r"))
    m : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_at(f, off, n)
    got(m)

def show_hdr(r: Result<&2, &2, G.GptError, G.GptHeader>) -> String:
  match r:
    case Done{G.GptHeader{rev, size, crc, my, alt, first, last, guid, elba, count, esize, ecrc}}:
      W.W64.show(my) ++ " " ++ W.W64.show(alt) ++ " " ++ W.W64.show(first) ++ " " ++ W.W64.show(last) ++ " " ++ U.Uuid.show(guid) ++ " " ++ W.W64.show(elba) ++ " " ++ U32.show(count) ++ " " ++ U32.show(esize)
    case Fail{e}:
      "error: " ++ G.GptError.show(e)

def valid(r: Result<&2, &2, G.GptError, G.GptHeader>) -> String:
  match r:
    case Done{h}:
      "valid"
    case Fail{e}:
      G.GptError.show(e)

def entry_line(used: Bool, +pre: String, i: U32, e: G.GptEntry) -> String:
  match used:
    case True{}:
      match e:
        case G.GptEntry{+t, +u, +first, +last, +attr, +name}:
          "\n" ++ pre ++ " p" ++ U32.show(i) ++ " " ++ U.Uuid.show(t) ++ " " ++ U.Uuid.show(u) ++ " " ++ W.W64.show(first) ++ " " ++ W.W64.show(last) ++ " " ++ W.W64.show_hex(attr) ++ " '" ++ G.GptEntry.name_text(G.GptEntry{t, u, first, last, attr, name}) ++ "'"
    case False{}:
      ""

def entry_lines(es: List<&2, G.GptEntry>, +pre: String, +i: U32) -> String:
  match es:
    case Nil{}:
      ""
    case Con{+e, t}:
      entry_line(G.GptEntry.is_used(e), pre, i, e) ++ entry_lines(t, pre, U32.add(i, 1))

def entries_of(r: Result<&2, &2, G.GptError, List<&2, G.GptEntry>>) -> List<&2, G.GptEntry>:
  match r:
    case Done{es}:
      es
    case Fail{e}:
      Nil{}

def alternate(h: G.GptHeader) -> W.W64:
  match h:
    case G.GptHeader{rev, size, crc, my, alt, first, last, guid, elba, count, esize, ecrc}:
      alt

def gpt_report(+pre: String, +lba0: B.Octets, +lba1: B.Octets, +ents: B.Octets, +bak: B.Octets, +bents: B.Octets, r: Result<&2, &2, G.GptError, G.GptHeader>, rb: Result<&2, &2, G.GptError, G.GptHeader>) -> String:
  match r rb:
    case Done{+h} Done{+hb}:
      +es = entries_of(G.Gpt.entries(h, ents))
      pre ++ " scheme " ++ P.PartitionScheme.show(P.Partition.detect(lba0, lba1)) ++ "\n" ++ pre ++ " primary " ++ show_hdr(Done{h}) ++ " " ++ valid(G.Gpt.validate_header(lba1)) ++ "\n" ++ pre ++ " backup " ++ show_hdr(Done{hb}) ++ " " ++ valid(G.Gpt.validate_header(bak)) ++ "\n" ++ pre ++ " entries " ++ Bool.show(G.Gpt.entries_crc_ok(h, ents)) ++ " " ++ Bool.show(G.Gpt.entries_crc_ok(hb, bents)) ++ entry_lines(es, pre, 1) ++ "\n" ++ pre ++ " rebuild " ++ Bool.show(B.Octets.is_eq(G.Gpt.build(h, es), lba1)) ++ " " ++ Bool.show(B.Octets.is_eq(G.Gpt.build_header(G.GptHeader.backup(h)), bak)) ++ " " ++ Bool.show(B.Octets.is_eq(M.Mbr.build(B.Octets.empty(), M.Mbr.protective(alternate(h))), lba0))
    case _ _:
      pre ++ " unreadable"

def gpt_report2(+pre: String, +lba0: B.Octets, +lba1: B.Octets, +ents: B.Octets, +bak: B.Octets, +bents: B.Octets) -> String:
  gpt_report(pre, lba0, lba1, ents, bak, bents, G.Gpt.parse_header(lba1), G.Gpt.parse_header(bak))

def gpt_case(+pre: String, +path: String, +last: U32) -> IO(Unit):
  do IO<Unit>:
    lba0 : B.Octets <- read_at(path, 0, 512)
    lba1 : B.Octets <- read_at(path, 512, 512)
    ents : B.Octets <- read_at(path, 1024, 16384)
    bak : B.Octets <- read_at(path, last, 512)
    bents : B.Octets <- read_at(path, U32.sub(last, 16384), 16384)
    IO.print(gpt_report2(pre, lba0, lba1, ents, bak, bents))

def chs(c: M.MbrChs) -> String:
  match c:
    case M.MbrChs{h, s, y}:
      U32.show(h) ++ "/" ++ U32.show(s) ++ "/" ++ U32.show(y)

def mbr_line.go(used: Bool, +pre: String, i: U32, e: M.MbrEntry) -> String:
  match used:
    case False{}:
      ""
    case True{}:
      match e:
        case M.MbrEntry{status, first, os_type, last, lba, sectors}:
          "\n" ++ pre ++ " p" ++ U32.show(i) ++ " " ++ U32.show(status) ++ " " ++ U32.show(os_type) ++ " " ++ U32.show(lba) ++ " " ++ U32.show(sectors) ++ " " ++ chs(first) ++ " " ++ chs(last)

def mbr_line(+pre: String, i: U32, +e: M.MbrEntry) -> String:
  mbr_line.go(M.MbrEntry.is_used(e), pre, i, e)

def mbr_report(+pre: String, +lba0: B.Octets, r: Result<&2, &2, M.MbrError, M.Mbr>) -> String:
  match r:
    case Done{+m}:
      match m:
        case M.Mbr{sig, p0, p1, p2, p3}:
          pre ++ " scheme " ++ P.PartitionScheme.show(P.Partition.detect(lba0, B.Octets.zeros(512n))) ++ "\n" ++ pre ++ " sig " ++ U32.show(sig) ++ mbr_line(pre, 1, p0) ++ mbr_line(pre, 2, p1) ++ mbr_line(pre, 3, p2) ++ mbr_line(pre, 4, p3) ++ "\n" ++ pre ++ " rebuild " ++ Bool.show(B.Octets.is_eq(M.Mbr.build(M.Mbr.boot_code(lba0), m), lba0))
    case Fail{e}:
      pre ++ " error: " ++ M.MbrError.show(e)

def mbr_report2(+pre: String, +lba0: B.Octets) -> String:
  mbr_report(pre, lba0, M.Mbr.parse(lba0))

def mbr_case(+pre: String, +path: String) -> IO(Unit):
  do IO<Unit>:
    lba0 : B.Octets <- read_at(path, 0, 512)
    IO.print(mbr_report2(pre, lba0))

def main() -> IO(Unit):
  do IO<Unit>:
'''

def main():
    here = os.path.dirname(os.path.abspath(__file__))
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 2026)
    d = sys.argv[2]
    calls, expect = [], []
    for k, corrupt in enumerate([None] * 10 + ["header", "entries"]):
        c, e = make_gpt(rng, d, k, corrupt)
        calls.append(c); expect += e
    for k in range(6):
        c, e = make_mbr(rng, d, k)
        calls.append(c); expect += e
    with open(os.path.join(here, "cases.bend"), "w", encoding="utf-8") as f:
        f.write(HEAD + "\n".join(calls) + "\n    IO.print(\"done\")\n")
    with open(os.path.join(here, "expected.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(expect) + "\ndone\n")
    print(len(expect), "facts from", len(calls), "images")

main()
