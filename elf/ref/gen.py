#!/usr/bin/env python3
"""Differential test cases for bend-osdev-elf.

Usage: gen.py SEED DIR

Writes ELF files into DIR, ref/cases.bend (a Bend program that dumps each
file with ref/dump.bend) and ref/expected.txt (the same dump from a reader
written here, independently, from the gABI and the ELF-64 Object File Format).
The reader is checked against readelf (GNU binutils) on every well-formed
file: the ELF header, program headers, section headers, section names and
symbol tables must agree field by field.

The files:
  * built by gcc, when it is installed (64-bit only): a static executable, a
    position-independent executable, a shared object, an object file, and a
    dynamically linked executable (with .dynsym and symbol versions);
  * written here from the specification: ELF32 and ELF64, little- and
    big-endian, with random program headers, sections and symbols; one with
    extended numbering (e_phnum PN_XNUM, e_shnum 0, e_shstrndx SHN_XINDEX);
  * malformed: a bad magic, class, data encoding or version, truncated
    headers and tables, offsets past the end, bad entry sizes, bad string
    offsets. These are not compared with readelf, which reports and carries
    on; the expected answer is the specification's (the reader here).
"""
import os, random, re, shutil, struct, subprocess, sys

# ---------------------------------------------------------------------------
# The reader (from the specification), printing the dump format of dump.bend

class Bad(Exception):
    pass

PN_XNUM = SHN_XINDEX = 0xFFFF

def err_name(e):
    return str(e.args[0])

def u(fmt, data, off):
    n = struct.calcsize(fmt)
    if off + n > len(data):
        raise Bad("truncated")
    return struct.unpack_from(fmt, data, off)

def hx(v):
    return "%016x" % v

def parse_header(d):
    if len(d) < 4 or d[:4] != b"\x7fELF":
        raise Bad("bad-magic")
    if len(d) < 52:
        raise Bad("truncated")
    if d[4] not in (1, 2):
        raise Bad("bad-class")
    if d[5] not in (1, 2):
        raise Bad("bad-data")
    if d[6] != 1:
        raise Bad("bad-version")
    is64, e = d[4] == 2, ">" if d[5] == 2 else "<"
    h = {"is64": is64, "e": e, "osabi": d[7], "abiversion": d[8]}
    fmt = e + ("HHIQQQIHHHHHH" if is64 else "HHIIIIIHHHHHH")
    names = ["type", "machine", "version", "entry", "phoff", "shoff", "flags", "ehsize", "phentsize", "phnum", "shentsize", "shnum", "shstrndx"]
    h.update(zip(names, u(fmt, d, 16)))
    return h

def small(v):
    if v >= 2 ** 32:
        raise Bad("offset-out-of-range")
    return v

def seek(d, off):
    if small(off) > len(d):
        raise Bad("offset-out-of-range")
    return off

def parse_shdr(d, h, off):
    if h["is64"]:
        f = u(h["e"] + "IIQQQQIIQQ", d, off)
    else:
        f = u(h["e"] + "IIIIIIIIII", d, off)
    return dict(zip(["name", "type", "flags", "addr", "offset", "size", "link", "info", "addralign", "entsize"], f))

def section0(d, h):
    if h["shoff"] == 0:
        raise Bad("no-section-table")
    if h["shentsize"] < (64 if h["is64"] else 40):
        raise Bad("bad-entry-size")
    return parse_shdr(d, h, seek(d, h["shoff"]))

def shnum(d, h):
    if h["shnum"] != 0:
        return h["shnum"]
    if h["shoff"] == 0:
        return 0
    return small(section0(d, h)["size"])

def phnum(d, h):
    return section0(d, h)["info"] if h["phnum"] == PN_XNUM else h["phnum"]

def shstrndx(d, h):
    return section0(d, h)["link"] if h["shstrndx"] == SHN_XINDEX else h["shstrndx"]

def table(d, n, entsize, size, off, parse):
    if n != 0 and entsize < size:
        raise Bad("bad-entry-size")
    if n == 0:
        return []
    base = seek(d, off)
    return [parse(base + i * entsize) for i in range(n)]

def parse_phdr(d, h, off):
    if h["is64"]:
        t, fl, o, va, pa, fs, ms, al = u(h["e"] + "IIQQQQQQ", d, off)
    else:
        t, o, va, pa, fs, ms, fl, al = u(h["e"] + "IIIIIIII", d, off)
    return dict(type=t, flags=fl, offset=o, vaddr=va, paddr=pa, filesz=fs, memsz=ms, align=al)

def phdrs(d, h):
    return table(d, phnum(d, h), h["phentsize"], 56 if h["is64"] else 32, h["phoff"], lambda o: parse_phdr(d, h, o))

def shdrs(d, h):
    return table(d, shnum(d, h), h["shentsize"], 64 if h["is64"] else 40, h["shoff"], lambda o: parse_shdr(d, h, o))

def section_bytes(d, s):
    if s["type"] == 8:
        return b""
    n = small(s["size"])
    off = seek(d, s["offset"])
    if off + n > len(d):
        raise Bad("offset-out-of-range")
    return d[off:off + n]

def bytes_at(d, ss, i):
    if i >= len(ss):
        raise Bad("bad-index")
    return section_bytes(d, ss[i])

def string(tab, i):
    if i > len(tab):
        raise Bad("bad-string")
    j = tab.find(b"\0", i)
    if j < 0:
        raise Bad("bad-string")
    return tab[i:j]

def parse_sym(d, h, off):
    if h["is64"]:
        nm, info, other, ndx, val, sz = u(h["e"] + "IBBHQQ", d, off)
    else:
        nm, val, sz, info, other, ndx = u(h["e"] + "IIIBBH", d, off)
    return dict(name=nm, value=val, size=sz, info=info, other=other, shndx=ndx)

def symbols(d, h, s):
    data = section_bytes(d, s)
    es, size = small(s["entsize"]), small(s["size"])
    if es < (24 if h["is64"] else 16) or size % es != 0:
        raise Bad("bad-entry-size")
    return [parse_sym(data, h, i * es) for i in range(size // es)]

def try_(f, default=None):
    try:
        return f(), None
    except Bad as e:
        return default, err_name(e)

def text(b):
    return "".join(chr(c) for c in b)

def show_name(tab, i):
    v, e = try_(lambda: string(tab, i))
    return "!" + e if e else "'" + text(v) + "'"

def dump(d):
    out = []
    h, e = try_(lambda: parse_header(d))
    if e:
        return ["error " + e]
    out.append("header class=%s data=%s osabi=%d abiversion=%d type=%d machine=%d version=%d entry=%s phoff=%s shoff=%s flags=%d ehsize=%d phentsize=%d phnum=%d shentsize=%d shnum=%d shstrndx=%d" % (
        "64" if h["is64"] else "32", "be" if h["e"] == ">" else "le", h["osabi"], h["abiversion"], h["type"], h["machine"], h["version"],
        hx(h["entry"]), hx(h["phoff"]), hx(h["shoff"]), h["flags"], h["ehsize"], h["phentsize"], h["phnum"], h["shentsize"], h["shnum"], h["shstrndx"]))
    counts = [try_(lambda f=f: str(f(d, h))) for f in (phnum, shnum, shstrndx)]
    out.append("counts phnum=%s shnum=%s shstrndx=%s" % tuple(v if v is not None else err for v, err in counts))
    ps, e = try_(lambda: phdrs(d, h))
    if e:
        out.append("phdrs error " + e)
    else:
        for i, p in enumerate(ps):
            out.append("ph %d type=%d flags=%d offset=%s vaddr=%s paddr=%s filesz=%s memsz=%s align=%s" % (
                i, p["type"], p["flags"], hx(p["offset"]), hx(p["vaddr"]), hx(p["paddr"]), hx(p["filesz"]), hx(p["memsz"]), hx(p["align"])))
    ss, e = try_(lambda: shdrs(d, h))
    if e:
        out.append("shdrs error " + e)
        return out
    names, _ = try_(lambda: bytes_at(d, ss, shstrndx(d, h)), b"")
    for i, s in enumerate(ss):
        out.append("sh %d name=%s type=%d flags=%s addr=%s offset=%s size=%s link=%d info=%d align=%s entsize=%s" % (
            i, show_name(names, s["name"]), s["type"], hx(s["flags"]), hx(s["addr"]), hx(s["offset"]), hx(s["size"]), s["link"], s["info"], hx(s["addralign"]), hx(s["entsize"])))
    for s in ss:
        if s["type"] not in (2, 11):
            continue
        v, e = try_(lambda: string(names, s["name"]))
        sec = "?" if e else text(v)
        strtab, _ = try_(lambda: bytes_at(d, ss, s["link"]), b"")
        ys, e = try_(lambda: symbols(d, h, s))
        if e:
            out.append("syms %s error %s" % (sec, e))
            continue
        for i, y in enumerate(ys):
            out.append("sym %s %d name=%s value=%s size=%s bind=%d type=%d other=%d shndx=%d" % (
                sec, i, show_name(strtab, y["name"]), hx(y["value"]), hx(y["size"]), y["info"] >> 4, y["info"] & 15, y["other"], y["shndx"]))
    return out

# ---------------------------------------------------------------------------
# readelf: the reader above must agree with it on every well-formed file

SHT = {"NULL": 0, "PROGBITS": 1, "SYMTAB": 2, "STRTAB": 3, "RELA": 4, "HASH": 5, "DYNAMIC": 6, "NOTE": 7, "NOBITS": 8, "REL": 9,
       "SHLIB": 10, "DYNSYM": 11, "INIT_ARRAY": 14, "FINI_ARRAY": 15, "PREINIT_ARRAY": 16, "GROUP": 17,
       "GNU_HASH": 0x6ffffff6, "VERDEF": 0x6ffffffd, "VERNEED": 0x6ffffffe, "VERSYM": 0x6fffffff,
       "X86_64_UNWIND": 0x70000001, "LLVM_ADDRSIG": 0x6fff4c03, "GNU_ATTRIBUTES": 0x6ffffff5}
PT = {"NULL": 0, "LOAD": 1, "DYNAMIC": 2, "INTERP": 3, "NOTE": 4, "SHLIB": 5, "PHDR": 6, "TLS": 7,
      "GNU_EH_FRAME": 0x6474e550, "GNU_STACK": 0x6474e551, "GNU_RELRO": 0x6474e552, "GNU_PROPERTY": 0x6474e553}
ET = {"NONE": 0, "REL": 1, "EXEC": 2, "DYN": 3, "CORE": 4}
EM = {"Advanced Micro Devices X86-64": 62, "Intel 80386": 3, "PowerPC": 20, "PowerPC64": 21, "Sparc": 2, "Sparc v9": 43}
STT = {"NOTYPE": 0, "OBJECT": 1, "FUNC": 2, "SECTION": 3, "FILE": 4, "COMMON": 5, "TLS": 6, "IFUNC": 10}
STB = {"LOCAL": 0, "GLOBAL": 1, "WEAK": 2, "UNIQUE": 10}
STV = {"DEFAULT": 0, "INTERNAL": 1, "HIDDEN": 2, "PROTECTED": 3}
SHF = {"W": 1, "A": 2, "X": 4, "M": 16, "S": 32, "I": 64, "L": 128, "O": 256, "G": 512, "T": 1024, "C": 2048, "E": 0x80000000}

def same(what, a, b):
    if a != b:
        raise AssertionError("readelf disagrees on %s: %r (here) vs %r (readelf)" % (what, a, b))

def num(s):
    return int(s, 0) if s.startswith("0x") else int(s)

def check_readelf(path, d):
    out = subprocess.run(["readelf", "-h", "-l", "-S", "-s", "--wide", path], capture_output=True, text=True).stdout
    h = parse_header(d)
    hdr = dict(re.findall(r"^  ([A-Za-z/ ]+):\s+(.*)$", out, re.M))
    same("class", hdr["Class"], "ELF64" if h["is64"] else "ELF32")
    same("data", "big endian" in hdr["Data"], h["e"] == ">")
    same("OS/ABI", hdr["OS/ABI"], "UNIX - System V" if h["osabi"] == 0 else hdr["OS/ABI"])
    same("ABI version", int(hdr["ABI Version"]), h["abiversion"])
    same("type", ET[hdr["Type"].split()[0]], h["type"])
    same("machine", EM[hdr["Machine"]], h["machine"])
    same("version", num(hdr["Version"]), h["version"])
    same("entry", num(hdr["Entry point address"]), h["entry"])
    same("phoff", int(hdr["Start of program headers"].split()[0]), h["phoff"])
    same("shoff", int(hdr["Start of section headers"].split()[0]), h["shoff"])
    same("flags", num(hdr["Flags"].split(",")[0]), h["flags"])
    same("ehsize", int(hdr["Size of this header"].split()[0]), h["ehsize"])
    same("phentsize", int(hdr["Size of program headers"].split()[0]), h["phentsize"])
    same("shentsize", int(hdr["Size of section headers"].split()[0]), h["shentsize"])
    # "0 (8)": the field, then the count from section 0
    def counted(key, field, resolved):
        f = hdr[key].split()
        same(key, int(f[0]), field)
        same(key + " (resolved)", int(f[1].strip("()")) if len(f) > 1 else int(f[0]), resolved)
    counted("Number of program headers", h["phnum"], phnum(d, h))
    counted("Number of section headers", h["shnum"], shnum(d, h))
    counted("Section header string table index", h["shstrndx"], shstrndx(d, h))
    # program headers
    ps = phdrs(d, h)
    rows = re.findall(r"^  ([A-Z_]+|LOOS\+0x[0-9a-f]+|LOPROC\+0x[0-9a-f]+)\s+(0x[0-9a-f]+) (0x[0-9a-f]+) (0x[0-9a-f]+) (0x[0-9a-f]+) (0x[0-9a-f]+) ([RWE ]{3}) (0x[0-9a-f]+)$", out, re.M)
    same("program header count", len(rows), len(ps))
    for p, r in zip(ps, rows):
        same("p_type", PT[r[0]], p["type"])
        same("p_offset/p_vaddr/p_paddr/p_filesz/p_memsz", [num(x) for x in r[1:6]], [p["offset"], p["vaddr"], p["paddr"], p["filesz"], p["memsz"]])
        same("p_flags", (4 if "R" in r[6] else 0) | (2 if "W" in r[6] else 0) | (1 if "E" in r[6] else 0), p["flags"])
        same("p_align", num(r[7]), p["align"])
    # section headers
    ss = shdrs(d, h)
    names = bytes_at(d, ss, shstrndx(d, h)) if ss else b""
    rows = re.findall(r"^  \[ *(\d+)\] (.*?) +([A-Z_0-9]+) +([0-9a-f]+) ([0-9a-f]+) ([0-9a-f]+) ([0-9a-f]+) +([A-Za-z]*) +(\d+) +(\d+) +(\d+)$", out, re.M)
    same("section count", len(rows), len(ss))
    for s, r in zip(ss, rows):
        same("section name", r[1].strip(), text(string(names, s["name"])))
        same("sh_type", SHT[r[2]], s["type"])
        same("sh_addr/sh_offset/sh_size/sh_entsize", [int(x, 16) for x in r[3:7]], [s["addr"], s["offset"], s["size"], s["entsize"]])
        same("sh_flags", sum(SHF[c] for c in r[7]), s["flags"])
        same("sh_link/sh_info/sh_addralign", [int(x) for x in r[8:11]], [s["link"], s["info"], s["addralign"]])
    # symbol tables
    tables = re.split(r"^Symbol table '", out, flags=re.M)[1:]
    symsecs = [s for s in ss if s["type"] in (2, 11)]
    same("symbol table count", len(tables), len(symsecs))
    for s, t in zip(symsecs, tables):
        same("symbol table name", t.split("'")[0], text(string(names, s["name"])))
        strtab = bytes_at(d, ss, s["link"])
        rows = re.findall(r"^ +\d+: ([0-9a-f]+) +(\S+) (\S+) +(\S+) +(\S+) +(\S+) ?(.*)$", t, re.M)
        ys = symbols(d, h, s)
        same("symbol count", len(rows), len(ys))
        for y, r in zip(ys, rows):
            same("st_value", int(r[0], 16), y["value"])
            same("st_size", num(r[1]), y["size"])
            same("st_type", STT[r[2]], y["info"] & 15)
            same("st_bind", STB[r[3]], y["info"] >> 4)
            same("st_other (visibility)", STV[r[4]], y["other"] & 3)
            same("st_shndx", {"UND": 0, "ABS": 0xFFF1, "COM": 0xFFF2}.get(r[5], None) if not r[5].isdigit() else int(r[5]), y["shndx"])
            nm = text(string(strtab, y["name"]))
            shown = r[6].strip()
            if s["type"] == 11 and shown != nm:  # readelf adds .dynsym's versions: "puts@GLIBC_2.2.5 (2)"
                shown = re.sub(r"@\S*( \(\d+\))?$", "", shown)
            if not (y["info"] & 15 == 3 and nm == ""):  # readelf names section symbols after their section
                same("symbol name", nm, shown)

# ---------------------------------------------------------------------------
# Writing ELF files, from the specification

def write_elf(is64, big, machine, etype, phs, secs, syms, rng, osabi=0, extended=False, shoff_override=None):
    """phs: list of phdr dicts; secs: list of (name, type, flags, data, extra)
    with extra a dict of overrides; syms: (name, value, size, info, other, shndx).
    Section order: NULL, secs..., .symtab, .strtab, .shstrtab."""
    e = ">" if big else "<"
    W = "Q" if is64 else "I"
    hsize, phsize, shsize, symsize = (64, 56, 64, 24) if is64 else (52, 32, 40, 16)
    body = bytearray()
    def place(data, align=1):
        while (hsize + len(phs) * phsize + len(body)) % align:
            body.append(0)
        off = hsize + len(phs) * phsize + len(body)
        body.extend(data)
        return off
    names = [n for n, *_ in secs] + [".symtab", ".strtab", ".shstrtab"]
    shstr = b"\0" + b"".join(n.encode() + b"\0" for n in names)
    name_off = {}
    pos = 1
    for n in names:
        name_off[n] = pos
        pos += len(n) + 1
    strtab = bytearray(b"\0")
    sym_name = []
    for nm, *_ in syms:
        if nm:
            sym_name.append(len(strtab)); strtab.extend(nm.encode() + b"\0")
        else:
            sym_name.append(0)
    headers = [dict(name=0, type=0, flags=0, addr=0, offset=0, size=0, link=0, info=0, addralign=0, entsize=0)]
    for n, t, fl, data, extra in secs:
        off = place(b"" if t == 8 else data, 4)
        sh = dict(name=name_off[n], type=t, flags=fl, addr=rng.randrange(2 ** (64 if is64 else 32)) if fl & 2 else 0, offset=off, size=len(data), link=0, info=0, addralign=4, entsize=0)
        sh.update(extra)
        headers.append(sh)
    symtab = b""
    for (nm, val, sz, info, other, ndx), no in zip(syms, sym_name):
        if is64:
            symtab += struct.pack(e + "IBBHQQ", no, info, other, ndx, val, sz)
        else:
            symtab += struct.pack(e + "IIIBBH", no, val, sz, info, other, ndx)
    nsec = len(secs) + 1
    locals_ = sum(1 for s in syms if s[3] >> 4 == 0)
    headers.append(dict(name=name_off[".symtab"], type=2, flags=0, addr=0, offset=place(symtab, 8), size=len(symtab), link=nsec + 1, info=locals_, addralign=8, entsize=symsize))
    headers.append(dict(name=name_off[".strtab"], type=3, flags=0, addr=0, offset=place(bytes(strtab)), size=len(strtab), link=0, info=0, addralign=1, entsize=0))
    headers.append(dict(name=name_off[".shstrtab"], type=3, flags=0, addr=0, offset=place(shstr), size=len(shstr), link=0, info=0, addralign=1, entsize=0))
    shoff = place(b"", 8)
    count, strndx = len(headers), len(headers) - 1
    e_phnum, e_shnum, e_shstrndx = len(phs), count, strndx
    if extended:
        headers[0].update(size=count, link=strndx, info=len(phs))
        e_phnum, e_shnum, e_shstrndx = PN_XNUM, 0, SHN_XINDEX
    for sh in headers:
        body.extend(struct.pack(e + "II" + W * 4 + "II" + W * 2, sh["name"], sh["type"], sh["flags"], sh["addr"], sh["offset"], sh["size"], sh["link"], sh["info"], sh["addralign"], sh["entsize"]))
    ident = b"\x7fELF" + bytes([2 if is64 else 1, 2 if big else 1, 1, osabi, 0]) + bytes(7)
    hdr = ident + struct.pack(e + "HHI" + W * 3 + "IHHHHHH", etype, machine, 1, rng.randrange(2 ** (64 if is64 else 32)), hsize if phs else 0,
                              shoff if shoff_override is None else shoff_override, 0, hsize, phsize, e_phnum, shsize, e_shnum, e_shstrndx)
    ph = b""
    for p in phs:
        if is64:
            ph += struct.pack(e + "IIQQQQQQ", p["type"], p["flags"], p["offset"], p["vaddr"], p["paddr"], p["filesz"], p["memsz"], p["align"])
        else:
            ph += struct.pack(e + "IIIIIIII", p["type"], p["offset"], p["vaddr"], p["paddr"], p["filesz"], p["memsz"], p["flags"], p["align"])
    return bytearray(hdr + ph + bytes(body))

def random_elf(rng, is64, big, extended=False):
    bits = 64 if is64 else 32
    machine = {(True, False): 62, (True, True): rng.choice([21, 43]), (False, False): 3, (False, True): rng.choice([20, 2])}[(is64, big)]
    phs = []
    for _ in range(rng.randrange(1 if extended else 0, 5)):
        fs = rng.randrange(0, 4096)
        phs.append(dict(type=rng.choice([1, 1, 4, 6, 7, 0x6474e551]), flags=rng.randrange(8), offset=rng.randrange(2 ** 16),
                        vaddr=rng.randrange(2 ** bits), paddr=rng.randrange(2 ** bits), filesz=fs, memsz=fs + rng.randrange(4096), align=rng.choice([1, 4, 8, 4096, 65536])))
    secs = [(".text", 1, 6, bytes(rng.randrange(256) for _ in range(rng.randrange(1, 40))), {}),
            (".data", 1, 3, bytes(rng.randrange(256) for _ in range(rng.randrange(0, 20))), {}),
            (".bss", 8, 3, bytes(rng.randrange(1, 64)), {}),
            (".rodata.str", 1, 2 | 16 | 32, b"hello\0elf\0", {"entsize": 1})]
    shndx = len(secs) + 1  # .symtab is the section after them
    syms = [("", 0, 0, 0, 0, 0)]
    for k in range(rng.randrange(1, 10)):
        bind = 0 if k < 2 else rng.choice([1, 1, 2])
        syms.append(("sym_%d_%s" % (k, "".join(rng.choice("abcxyz_") for _ in range(rng.randrange(1, 9)))), rng.randrange(2 ** bits), rng.randrange(2 ** rng.choice([4, 16, bits])),
                     (bind << 4) | rng.choice([0, 1, 2, 4]), rng.randrange(4), rng.choice([0, 1, 2, 3, 0xFFF1])))
    syms.sort(key=lambda s: s[3] >> 4 != 0)  # locals first, as the gABI requires
    return write_elf(is64, big, machine, rng.choice([1, 2, 3]), phs, secs, syms, rng, extended=extended)

def malformed(rng):
    """(name, bytes): each breaks one rule"""
    good = bytes(random_elf(rng, True, False))
    good32 = bytes(random_elf(rng, False, True))
    e64 = parse_header(good)
    e32 = parse_header(good32)
    def patch(d, off, fmt, v):
        d = bytearray(d); struct.pack_into(fmt, d, off, v); return bytes(d)
    def patch_shdr(d, h, i, field, v):
        fields = ["name", "type", "flags", "addr", "offset", "size", "link", "info", "addralign", "entsize"]
        if h["is64"]:
            offs = [0, 4, 8, 16, 24, 32, 40, 44, 48, 56]; fmt = "IIQQQQIIQQ"
        else:
            offs = list(range(0, 40, 4)); fmt = "I" * 10
        k = fields.index(field)
        return patch(d, h["shoff"] + i * h["shentsize"] + offs[k], h["e"] + fmt[k], v)
    n64, n32 = shnum(good, e64), shnum(good32, e32)
    out = [
        ("bad_magic", b"\x7fELG" + good[4:]),
        ("not_elf", b"#!/bin/sh\necho not an ELF file\n"),
        ("empty", b""),
        ("short", good[:20]),
        ("short_51", good32[:51]),
        ("bad_class", good[:4] + b"\x03" + good[5:]),
        ("bad_data", good[:5] + b"\x00" + good[6:]),
        ("bad_version", good[:6] + b"\x00" + good[7:]),
        ("elf64_cut_63", good[:63]),
        ("shdrs_cut", good[:e64["shoff"] + 10]),
        ("shoff_past_end", patch(good, 40, "<Q", len(good) + 100)),
        ("shoff_huge", patch(good, 40, "<Q", 2 ** 40)),
        ("phoff_past_end", patch(patch(good, 56, "<H", 2), 32, "<Q", len(good) + 8)),
        ("shentsize_small", patch(good, 58, "<H", 32)),
        ("phentsize_small", patch(patch(good, 56, "<H", 1), 54, "<H", 8)),
        ("shstrndx_past_table", patch(good, 62, "<H", n64 + 5)),
        ("phnum_xnum_no_sections", patch(patch(good, 56, "<H", PN_XNUM), 40, "<Q", 0)),
        ("names_offset_past_end", patch_shdr(good32, e32, n32 - 1, "offset", len(good32) + 1)),
        ("names_size_past_end", patch_shdr(good32, e32, n32 - 1, "size", len(good32))),
        ("name_past_table", patch_shdr(good32, e32, 1, "name", 100000)),
        ("symtab_entsize_zero", patch_shdr(good, e64, n64 - 3, "entsize", 0)),
        ("symtab_entsize_small", patch_shdr(good32, e32, n32 - 3, "entsize", 12)),
        ("symtab_size_uneven", patch_shdr(good, e64, n64 - 3, "size", 25)),
        ("strtab_link_bad", patch_shdr(good, e64, n64 - 3, "link", 99)),
        ("strtab_unterminated", patch_shdr(good32, e32, n32 - 2, "size", 3)),
    ]
    return out

def gcc_files(d):
    if not shutil.which("gcc"):
        return []
    srcs = {
        "s.c": "static int counter;\nint value = 42;\nvoid _start(void) { counter++; for (;;) {} }\n",
        "l.c": "int shared_value = 7;\nint add(int a, int b) { return a + b + shared_value; }\nstatic int helper(int x) { return x * 2; }\nint twice(int x) { return helper(x); }\n",
        "m.c": "#include <stdio.h>\nint main(void) { puts(\"hi\"); return 0; }\n",
    }
    for n, s in srcs.items():
        with open(os.path.join(d, n), "w") as f:
            f.write(s)
    # small files: byte strings are lists, and reading at an offset walks them
    F = ["-Os", "-fno-asynchronous-unwind-tables", "-fno-stack-protector", "-Wl,--build-id=none", "-Wl,-z,noseparate-code"]
    builds = [
        ("gcc_static", F + ["-nostdlib", "-static", "s.c"]),
        ("gcc_static_nmagic", F + ["-nostdlib", "-static", "-Wl,-n", "-Wl,--no-warn-rwx-segments", "s.c"]),
        ("gcc_pie", F + ["-nostdlib", "-fPIE", "-pie", "s.c"]),
        ("gcc_shared.so", F + ["-nostdlib", "-fPIC", "-shared", "l.c"]),
        ("gcc_object.o", F + ["-c", "l.c"]),
        ("gcc_dynamic", F + ["m.c"]),
    ]
    out = []
    for name, args in builds:
        r = subprocess.run(["gcc", "-o", name] + args, cwd=d, capture_output=True)
        if r.returncode == 0:
            out.append(name)
    return out

def main():
    seed, d = int(sys.argv[1]), sys.argv[2]
    rng = random.Random(seed)
    here = os.path.dirname(os.path.abspath(__file__))
    files = []  # (label, path, well-formed)
    for name in gcc_files(d):
        files.append((name, os.path.join(d, name), True))
    k = 0
    for is64 in (True, False):
        for big in (False, True):
            for _ in range(3):
                files.append(("spec_%s_%s_%d" % ("elf64" if is64 else "elf32", "be" if big else "le", k), random_elf(rng, is64, big), True))
                k += 1
    files.append(("spec_extended_numbering_elf64", random_elf(rng, True, False, extended=True), True))
    files.append(("spec_extended_numbering_elf32be", random_elf(rng, False, True, extended=True), True))
    for name, data in malformed(rng):
        files.append(("bad_" + name, bytes(data), False))
    lines, expect = [], []
    have_readelf = shutil.which("readelf") is not None
    checked = 0
    for label, src, ok in files:
        path = os.path.join(d, label)
        if not isinstance(src, str):
            with open(path, "wb") as f:
                f.write(src)
        data = open(path, "rb").read()
        if ok and have_readelf:
            check_readelf(path, data)
            checked += 1
        lines.append('("%s", "%s")' % (label, path))
        expect.append("file " + label)
        expect.extend(dump(data))
    with open(os.path.join(here, "cases.bend"), "w") as f:
        f.write("import Base\nimport ./dump.bend as D\n\ndef main() -> IO(Unit):\n  D.dump_files([" + ", ".join(lines) + "])\n")
    with open(os.path.join(here, "expected.txt"), "w") as f:
        f.write("\n".join(expect) + "\n")
    print("%d files (%d checked against readelf), %d lines" % (len(files), checked, len(expect)))

main()
