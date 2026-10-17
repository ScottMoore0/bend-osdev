#!/usr/bin/env python3
# Writes elf/elf.bend, header.bend, sections.bend, segments.bend and
# symbols.bend from gen/src/*.bend.in, expanding each "#@ACCESSORS Type" line
# into the field accessors of that record. Run from anywhere:
#   python3 elf/gen/accessors.py
# (fields.bend has no accessors and is edited directly.)
import os, re

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.dirname(HERE)
W = "W.W64"
TYPES = {
 "ElfHeader": [("is64","Bool"),("big","Bool"),("osabi","U32"),("abiversion","U32"),("e_type","U32"),("e_machine","U32"),("e_version","U32"),("e_entry",W),("e_phoff",W),("e_shoff",W),("e_flags","U32"),("e_ehsize","U32"),("e_phentsize","U32"),("e_phnum","U32"),("e_shentsize","U32"),("e_shnum","U32"),("e_shstrndx","U32")],
 "ElfPhdr": [("p_type","U32"),("p_flags","U32"),("p_offset",W),("p_vaddr",W),("p_paddr",W),("p_filesz",W),("p_memsz",W),("p_align",W)],
 "ElfShdr": [("sh_name","U32"),("sh_type","U32"),("sh_flags",W),("sh_addr",W),("sh_offset",W),("sh_size",W),("sh_link","U32"),("sh_info","U32"),("sh_addralign",W),("sh_entsize",W)],
 "ElfSym": [("st_name","U32"),("st_value",W),("st_size",W),("st_info","U32"),("st_other","U32"),("st_shndx","U32")],
}

def acc(t):
    fs = TYPES[t]
    out = ["# the fields of an %s" % t, ""]
    for f, ty in fs:
        pat = ", ".join("x" if g == f else "_" for g, _ in fs)
        out.append("def %s.%s(r: %s) -> %s:\n  match r:\n    case %s{%s}:\n      x\n" % (t, f, t, ty, t, pat))
    return "\n".join(out)

for name in sorted(os.listdir(os.path.join(HERE, "src"))):
    if not name.endswith(".bend.in"):
        continue
    with open(os.path.join(HERE, "src", name), newline="") as f:
        src = f.read()
    src = re.sub(r"^#@ACCESSORS (\w+)$", lambda m: acc(m.group(1)), src, flags=re.M)
    with open(os.path.join(OUT, name[:-len(".in")]), "w", newline="\n") as f:
        f.write(src)
