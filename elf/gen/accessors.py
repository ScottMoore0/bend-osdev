#!/usr/bin/env python3
# Writes elf/*.bend from gen/src/*.bend.in, expanding three directives:
#   #@ACCESSORS Type          the field accessors of record Type
#   #@ENUM Name               a type of named codes from ENUMS (below)
#   #@TABLE Type P N          the table code of an entry type Type, read with
#                             the Bool parameters P (comma-separated, e.g.
#                             is64,big) and normalised with N (- for none):
#                             Type.parse, the structural table reader
#                             (table.list.ref) and its tail-recursive form,
#                             read_table, write_table and normal_table (each
#                             with its structural .ref form). The template
#                             supplies Type.parse.list(P, xs), Type.write(P, x)
#                             and Type.normal(N, x) above the directive.
# Run from anywhere:
#   python3 elf/gen/accessors.py
# (fields.bend and strtab.bend have no directives and are edited directly.)
import os, re

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.dirname(HERE)
W = "W.W64"
U = "U32"
TYPES = {
 "ElfHeader": [("is64","Bool"),("big","Bool"),("osabi",U),("abiversion",U),("e_type",U),("e_machine",U),("e_version",U),("e_entry",W),("e_phoff",W),("e_shoff",W),("e_flags",U),("e_ehsize",U),("e_phentsize",U),("e_phnum",U),("e_shentsize",U),("e_shnum",U),("e_shstrndx",U)],
 "ElfPhdr": [("p_type",U),("p_flags",U),("p_offset",W),("p_vaddr",W),("p_paddr",W),("p_filesz",W),("p_memsz",W),("p_align",W)],
 "ElfShdr": [("sh_name",U),("sh_type",U),("sh_flags",W),("sh_addr",W),("sh_offset",W),("sh_size",W),("sh_link",U),("sh_info",U),("sh_addralign",W),("sh_entsize",W)],
 "ElfSym": [("st_name",U),("st_value",W),("st_size",W),("st_info",U),("st_other",U),("st_shndx",U)],
 "ElfReloc": [("r_offset",W),("r_info",W),("r_addend",W)],
 "ElfDyn": [("d_tag",W),("d_val",W)],
 "ElfNote": [("n_namesz",U),("n_descsz",U),("n_type",U),("name","B.Octets"),("desc","B.Octets")],
 "ElfVersym": [("vs_ndx",U)],
 "ElfVerdef": [("vd_version",U),("vd_flags",U),("vd_ndx",U),("vd_cnt",U),("vd_hash",U),("vd_aux",U),("vd_next",U)],
 "ElfVerdaux": [("vda_name",U),("vda_next",U)],
 "ElfVerneed": [("vn_version",U),("vn_cnt",U),("vn_file",U),("vn_aux",U),("vn_next",U)],
 "ElfVernaux": [("vna_hash",U),("vna_flags",U),("vna_other",U),("vna_name",U),("vna_next",U)],
 "ElfVerdefEntry": [("vdef","ElfVerdef"),("names","List<&2, ElfVerdaux>")],
 "ElfVerneedEntry": [("vneed","ElfVerneed"),("vers","List<&2, ElfVernaux>")],
}
# the short names PROOF.bend's lemmas use (sym_table_eq, ...)
SHORT = {"ElfPhdr": "phdr", "ElfShdr": "shdr", "ElfSym": "sym", "ElfReloc": "rel", "ElfDyn": "dyn",
         "ElfVersym": "versym", "ElfVerdef": "verdef", "ElfVerdaux": "verdaux", "ElfVerneed": "verneed",
         "ElfVernaux": "vernaux"}

# Named codes: #@ENUM Name expands to the type Name (one constructor per
# code), Name.code(k), Name.name(k), Name.all() and Name.of_code(c). The
# codes are decimal (Bend has no hex literals): (constructor, code, name).
ENUMS = {
 # d_tag (gABI, "Dynamic Section"; the GNU and LSB ones from the LSB Core
 # specification, "Dynamic Section", confirmed by readelf's names for them)
 "ElfDynTag": [(c, v, n) for c, v, n in [
  ("ElfDtNull", 0, "DT_NULL"), ("ElfDtNeeded", 1, "DT_NEEDED"), ("ElfDtPltrelsz", 2, "DT_PLTRELSZ"),
  ("ElfDtPltgot", 3, "DT_PLTGOT"), ("ElfDtHash", 4, "DT_HASH"), ("ElfDtStrtab", 5, "DT_STRTAB"),
  ("ElfDtSymtab", 6, "DT_SYMTAB"), ("ElfDtRela", 7, "DT_RELA"), ("ElfDtRelasz", 8, "DT_RELASZ"),
  ("ElfDtRelaent", 9, "DT_RELAENT"), ("ElfDtStrsz", 10, "DT_STRSZ"), ("ElfDtSyment", 11, "DT_SYMENT"),
  ("ElfDtInit", 12, "DT_INIT"), ("ElfDtFini", 13, "DT_FINI"), ("ElfDtSoname", 14, "DT_SONAME"),
  ("ElfDtRpath", 15, "DT_RPATH"), ("ElfDtSymbolic", 16, "DT_SYMBOLIC"), ("ElfDtRel", 17, "DT_REL"),
  ("ElfDtRelsz", 18, "DT_RELSZ"), ("ElfDtRelent", 19, "DT_RELENT"), ("ElfDtPltrel", 20, "DT_PLTREL"),
  ("ElfDtDebug", 21, "DT_DEBUG"), ("ElfDtTextrel", 22, "DT_TEXTREL"), ("ElfDtJmprel", 23, "DT_JMPREL"),
  ("ElfDtBindNow", 24, "DT_BIND_NOW"), ("ElfDtInitArray", 25, "DT_INIT_ARRAY"),
  ("ElfDtFiniArray", 26, "DT_FINI_ARRAY"), ("ElfDtInitArraysz", 27, "DT_INIT_ARRAYSZ"),
  ("ElfDtFiniArraysz", 28, "DT_FINI_ARRAYSZ"), ("ElfDtRunpath", 29, "DT_RUNPATH"),
  ("ElfDtFlags", 30, "DT_FLAGS"), ("ElfDtPreinitArray", 32, "DT_PREINIT_ARRAY"),
  ("ElfDtPreinitArraysz", 33, "DT_PREINIT_ARRAYSZ"), ("ElfDtSymtabShndx", 34, "DT_SYMTAB_SHNDX"),
  ("ElfDtRelrsz", 35, "DT_RELRSZ"), ("ElfDtRelr", 36, "DT_RELR"), ("ElfDtRelrent", 37, "DT_RELRENT"),
  ("ElfDtGnuHash", 0x6ffffef5, "DT_GNU_HASH"), ("ElfDtVersym", 0x6ffffff0, "DT_VERSYM"),
  ("ElfDtRelacount", 0x6ffffff9, "DT_RELACOUNT"), ("ElfDtRelcount", 0x6ffffffa, "DT_RELCOUNT"),
  ("ElfDtFlags1", 0x6ffffffb, "DT_FLAGS_1"), ("ElfDtVerdef", 0x6ffffffc, "DT_VERDEF"),
  ("ElfDtVerdefnum", 0x6ffffffd, "DT_VERDEFNUM"), ("ElfDtVerneed", 0x6ffffffe, "DT_VERNEED"),
  ("ElfDtVerneednum", 0x6fffffff, "DT_VERNEEDNUM")]],
}

def enum(t):
    es = ENUMS[t]
    out = ["# The named codes of %s" % t, "type %s is Data:" % t]
    out += ["  %s{}" % c for c, _, _ in es]
    out.append("")
    out.append("# each name's code\ndef %s.code(k: %s) -> U32:\n  match k:" % (t, t))
    for c, v, _ in es:
        out.append("    case %s{}:\n      %d" % (c, v))
    out.append("")
    out.append("# each code's name, as the specification writes it\ndef %s.name(k: %s) -> String:\n  match k:" % (t, t))
    for c, _, n in es:
        out.append("    case %s{}:\n      \"%s\"" % (c, n))
    out.append("")
    out.append("# every named code, in the order of their codes\ndef %s.all() -> List<&2, %s>:\n  [%s]" % (t, t, ", ".join("%s{}" % c for c, _, _ in es)))
    out.append("")
    out.append(f"""def {t}.of_code.pick(hit: Bool, k: {t}) -> Maybe<&2, {t}>:
  match hit:
    case True{{}}:
      Some{{k}}
    case False{{}}:
      None{{}}

def {t}.of_code.go(ks: List<&2, {t}>, +c: U32, found: Maybe<&2, {t}>) -> Maybe<&2, {t}>:
  match ks:
    case Nil{{}}:
      found
    case Con{{+k, r}}:
      match found:
        case Some{{f}}:
          Some{{f}}
        case None{{}}:
          {t}.of_code.go(r, c, {t}.of_code.pick(U32.is_eq({t}.code(k), c), k))

# the name of a code, if it has one
def {t}.of_code(c: U32) -> Maybe<&2, {t}>:
  {t}.of_code.go({t}.all(), c, None{{}})""")
    return "\n".join(out)

def acc(t):
    fs = TYPES[t]
    out = ["# the fields of an %s" % t, ""]
    for f, ty in fs:
        pat = ", ".join("x" if g == f else "_" for g, _ in fs)
        out.append("def %s.%s(r: %s) -> %s:\n  match r:\n    case %s{%s}:\n      x\n" % (t, f, t, ty, t, pat))
    return "\n".join(out)

def table(t, ps, ns):
    P = [p for p in ps.split(",")]
    N = [] if ns == "-" else ns.split(",")
    nm = SHORT[t]
    R = "Result<&2, &2, F.ElfError, %s>" % t
    RL = "Result<&2, &2, F.ElfError, List<&2, %s>>" % t
    pa = ", ".join(P)                                  # is64, big
    pp = ", ".join("+%s: Bool" % p for p in P)         # +is64: Bool, +big: Bool
    pl = ", ".join("%s: Bool" % p for p in P)          # is64: Bool, big: Bool
    na = "".join("%s, " % p for p in N)                # is64,
    np = "".join("+%s: Bool, " % p for p in N)         # +is64: Bool,
    return f"""# Public: one entry, and a table

# the entry at the start of o (ElfTruncated if o is too short)
def {t}.parse({pl}, o: B.Octets) -> {R}:
  {t}.parse.list({pa}, B.Octets.to_list(o))

# Internal: n entries, step bytes apart (structural: the reference the proofs
# reason about)
def {t}.table.list.ref(n: Nat, {pp}, +step: Nat, +xs: List<&2, U32>) -> {RL}:
  match n:
    case 0n:
      Done{{Nil{{}}}}
    case 1n+p:
      F.elf_cons({t}, {t}.parse.list({pa}, xs), {t}.table.list.ref(p, {pa}, step, B.drop(step, xs)))

# the entries read so far are kept reversed in acc; the first failure ends it
def {t}.table.go(n: Nat, acc: {RL}, {pp}, +step: Nat, +xs: List<&2, U32>) -> {RL}:
  match n:
    case 0n:
      match acc:
        case Fail{{e}}:
          Fail{{e}}
        case Done{{rs}}:
          Done{{F.elf_rev_onto({t}, rs, Nil{{}})}}
    case 1n+p:
      match acc:
        case Fail{{e}}:
          Fail{{e}}
        case Done{{rs}}:
          {t}.table.go(p, F.elf_push({t}, {t}.parse.list({pa}, xs), rs), {pa}, step, B.drop(step, xs))

# n entries, step bytes apart: table.list.ref, tail-recursive (PROOF.bend:
# {nm}_table_eq), so a table can have any number of entries
def {t}.table.list(n: Nat, {pp}, +step: Nat, +xs: List<&2, U32>) -> {RL}:
  {t}.table.go(n, Done{{Nil{{}}}}, {pa}, step, xs)

# Public: n entries, step bytes apart, from the start of o
def {t}.read_table({pl}, n: Nat, step: Nat, o: B.Octets) -> {RL}:
  {t}.table.list(n, {pa}, step, B.Octets.to_list(o))

# a table's bytes, its entries packed (structural)
def {t}.write_table.ref({pp}, xs: List<&2, {t}>) -> B.Octets:
  match xs:
    case Nil{{}}:
      B.Octets.empty()
    case Con{{x, r}}:
      B.Octets.append({t}.write({pa}, x), {t}.write_table.ref({pa}, r))

# the entries rs (the table's entries, last first) in front of acc
def {t}.write_table.go({pp}, rs: List<&2, {t}>, acc: B.Octets) -> B.Octets:
  match rs:
    case Nil{{}}:
      acc
    case Con{{x, r}}:
      {t}.write_table.go({pa}, r, B.Octets.append({t}.write({pa}, x), acc))

# a table's bytes, built from the last entry back, tail-recursively
# (write_table.ref is the structural form; PROOF.bend: {nm}_write_eq)
def {t}.write_table({pp}, xs: List<&2, {t}>) -> B.Octets:
  {t}.write_table.go({pa}, F.elf_rev_onto({t}, xs, Nil{{}}), B.Octets.empty())

def {t}.normal_table.ref({np}xs: List<&2, {t}>) -> List<&2, {t}>:
  match xs:
    case Nil{{}}:
      Nil{{}}
    case Con{{x, r}}:
      Con{{{t}.normal({na}x), {t}.normal_table.ref({na}r)}}

def {t}.normal_table.go({np}xs: List<&2, {t}>, acc: List<&2, {t}>) -> List<&2, {t}>:
  match xs:
    case Nil{{}}:
      F.elf_rev_onto({t}, acc, Nil{{}})
    case Con{{x, r}}:
      {t}.normal_table.go({na}r, Con{{{t}.normal({na}x), acc}})

# every entry as the file stores it, tail-recursively (normal_table.ref is
# the structural form; PROOF.bend: {nm}_normal_eq)
def {t}.normal_table({np}xs: List<&2, {t}>) -> List<&2, {t}>:
  {t}.normal_table.go({na}xs, Nil{{}})
"""

def main():
    for name in sorted(os.listdir(os.path.join(HERE, "src"))):
        if not name.endswith(".bend.in"):
            continue
        with open(os.path.join(HERE, "src", name), newline="") as f:
            src = f.read()
        src = re.sub(r"^#@ACCESSORS (\w+)$", lambda m: acc(m.group(1)), src, flags=re.M)
        src = re.sub(r"^#@ENUM (\w+)$", lambda m: enum(m.group(1)), src, flags=re.M)
        src = re.sub(r"^#@TABLE (\w+) (\S+) (\S+)$", lambda m: table(m.group(1), m.group(2), m.group(3)), src, flags=re.M)
        with open(os.path.join(OUT, name[:-len(".in")]), "w", newline="\n") as f:
            f.write(src)

if __name__ == "__main__":
    main()
