# bend-osdev-elf, dynamic.bend: the dynamic section (gABI, "Dynamic Section";
# ELF-64 Object File Format, section 9): Elf32_Dyn and Elf64_Dyn entries, one
# by one and as the table of a SHT_DYNAMIC section; the common d_tag values,
# named (ElfDynTag); and the strings some entries point to (DT_NEEDED,
# DT_SONAME, DT_RPATH, DT_RUNPATH: offsets into the section at the dynamic
# section's sh_link).
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./fields.bend as F
import ./header.bend as H
import ./sections.bend as S
import ./strtab.bend as T

# A dynamic section entry: d_tag and d_un (d_val or d_ptr, one field here). In
# ELF32 both are widened to W64 (d_tag, an Elf32_Sword, is not sign-extended:
# no tag is negative).
type ElfDyn is Data:
  ElfDyn{d_tag: W.W64, d_val: W.W64}

# the fields of an ElfDyn

def ElfDyn.d_tag(r: ElfDyn) -> W.W64:
  match r:
    case ElfDyn{x, _}:
      x

def ElfDyn.d_val(r: ElfDyn) -> W.W64:
  match r:
    case ElfDyn{_, x}:
      x


# an entry's size: 16 bytes in ELF64, 8 in ELF32
def ElfDyn.size(is64: Bool) -> U32:
  match is64:
    case True{}:
      16
    case False{}:
      8

# The named codes of ElfDynTag
type ElfDynTag is Data:
  ElfDtNull{}
  ElfDtNeeded{}
  ElfDtPltrelsz{}
  ElfDtPltgot{}
  ElfDtHash{}
  ElfDtStrtab{}
  ElfDtSymtab{}
  ElfDtRela{}
  ElfDtRelasz{}
  ElfDtRelaent{}
  ElfDtStrsz{}
  ElfDtSyment{}
  ElfDtInit{}
  ElfDtFini{}
  ElfDtSoname{}
  ElfDtRpath{}
  ElfDtSymbolic{}
  ElfDtRel{}
  ElfDtRelsz{}
  ElfDtRelent{}
  ElfDtPltrel{}
  ElfDtDebug{}
  ElfDtTextrel{}
  ElfDtJmprel{}
  ElfDtBindNow{}
  ElfDtInitArray{}
  ElfDtFiniArray{}
  ElfDtInitArraysz{}
  ElfDtFiniArraysz{}
  ElfDtRunpath{}
  ElfDtFlags{}
  ElfDtPreinitArray{}
  ElfDtPreinitArraysz{}
  ElfDtSymtabShndx{}
  ElfDtRelrsz{}
  ElfDtRelr{}
  ElfDtRelrent{}
  ElfDtGnuHash{}
  ElfDtVersym{}
  ElfDtRelacount{}
  ElfDtRelcount{}
  ElfDtFlags1{}
  ElfDtVerdef{}
  ElfDtVerdefnum{}
  ElfDtVerneed{}
  ElfDtVerneednum{}

# each name's code
def ElfDynTag.code(k: ElfDynTag) -> U32:
  match k:
    case ElfDtNull{}:
      0
    case ElfDtNeeded{}:
      1
    case ElfDtPltrelsz{}:
      2
    case ElfDtPltgot{}:
      3
    case ElfDtHash{}:
      4
    case ElfDtStrtab{}:
      5
    case ElfDtSymtab{}:
      6
    case ElfDtRela{}:
      7
    case ElfDtRelasz{}:
      8
    case ElfDtRelaent{}:
      9
    case ElfDtStrsz{}:
      10
    case ElfDtSyment{}:
      11
    case ElfDtInit{}:
      12
    case ElfDtFini{}:
      13
    case ElfDtSoname{}:
      14
    case ElfDtRpath{}:
      15
    case ElfDtSymbolic{}:
      16
    case ElfDtRel{}:
      17
    case ElfDtRelsz{}:
      18
    case ElfDtRelent{}:
      19
    case ElfDtPltrel{}:
      20
    case ElfDtDebug{}:
      21
    case ElfDtTextrel{}:
      22
    case ElfDtJmprel{}:
      23
    case ElfDtBindNow{}:
      24
    case ElfDtInitArray{}:
      25
    case ElfDtFiniArray{}:
      26
    case ElfDtInitArraysz{}:
      27
    case ElfDtFiniArraysz{}:
      28
    case ElfDtRunpath{}:
      29
    case ElfDtFlags{}:
      30
    case ElfDtPreinitArray{}:
      32
    case ElfDtPreinitArraysz{}:
      33
    case ElfDtSymtabShndx{}:
      34
    case ElfDtRelrsz{}:
      35
    case ElfDtRelr{}:
      36
    case ElfDtRelrent{}:
      37
    case ElfDtGnuHash{}:
      1879047925
    case ElfDtVersym{}:
      1879048176
    case ElfDtRelacount{}:
      1879048185
    case ElfDtRelcount{}:
      1879048186
    case ElfDtFlags1{}:
      1879048187
    case ElfDtVerdef{}:
      1879048188
    case ElfDtVerdefnum{}:
      1879048189
    case ElfDtVerneed{}:
      1879048190
    case ElfDtVerneednum{}:
      1879048191

# each code's name, as the specification writes it
def ElfDynTag.name(k: ElfDynTag) -> String:
  match k:
    case ElfDtNull{}:
      "DT_NULL"
    case ElfDtNeeded{}:
      "DT_NEEDED"
    case ElfDtPltrelsz{}:
      "DT_PLTRELSZ"
    case ElfDtPltgot{}:
      "DT_PLTGOT"
    case ElfDtHash{}:
      "DT_HASH"
    case ElfDtStrtab{}:
      "DT_STRTAB"
    case ElfDtSymtab{}:
      "DT_SYMTAB"
    case ElfDtRela{}:
      "DT_RELA"
    case ElfDtRelasz{}:
      "DT_RELASZ"
    case ElfDtRelaent{}:
      "DT_RELAENT"
    case ElfDtStrsz{}:
      "DT_STRSZ"
    case ElfDtSyment{}:
      "DT_SYMENT"
    case ElfDtInit{}:
      "DT_INIT"
    case ElfDtFini{}:
      "DT_FINI"
    case ElfDtSoname{}:
      "DT_SONAME"
    case ElfDtRpath{}:
      "DT_RPATH"
    case ElfDtSymbolic{}:
      "DT_SYMBOLIC"
    case ElfDtRel{}:
      "DT_REL"
    case ElfDtRelsz{}:
      "DT_RELSZ"
    case ElfDtRelent{}:
      "DT_RELENT"
    case ElfDtPltrel{}:
      "DT_PLTREL"
    case ElfDtDebug{}:
      "DT_DEBUG"
    case ElfDtTextrel{}:
      "DT_TEXTREL"
    case ElfDtJmprel{}:
      "DT_JMPREL"
    case ElfDtBindNow{}:
      "DT_BIND_NOW"
    case ElfDtInitArray{}:
      "DT_INIT_ARRAY"
    case ElfDtFiniArray{}:
      "DT_FINI_ARRAY"
    case ElfDtInitArraysz{}:
      "DT_INIT_ARRAYSZ"
    case ElfDtFiniArraysz{}:
      "DT_FINI_ARRAYSZ"
    case ElfDtRunpath{}:
      "DT_RUNPATH"
    case ElfDtFlags{}:
      "DT_FLAGS"
    case ElfDtPreinitArray{}:
      "DT_PREINIT_ARRAY"
    case ElfDtPreinitArraysz{}:
      "DT_PREINIT_ARRAYSZ"
    case ElfDtSymtabShndx{}:
      "DT_SYMTAB_SHNDX"
    case ElfDtRelrsz{}:
      "DT_RELRSZ"
    case ElfDtRelr{}:
      "DT_RELR"
    case ElfDtRelrent{}:
      "DT_RELRENT"
    case ElfDtGnuHash{}:
      "DT_GNU_HASH"
    case ElfDtVersym{}:
      "DT_VERSYM"
    case ElfDtRelacount{}:
      "DT_RELACOUNT"
    case ElfDtRelcount{}:
      "DT_RELCOUNT"
    case ElfDtFlags1{}:
      "DT_FLAGS_1"
    case ElfDtVerdef{}:
      "DT_VERDEF"
    case ElfDtVerdefnum{}:
      "DT_VERDEFNUM"
    case ElfDtVerneed{}:
      "DT_VERNEED"
    case ElfDtVerneednum{}:
      "DT_VERNEEDNUM"

# every named code, in the order of their codes
def ElfDynTag.all() -> List<&2, ElfDynTag>:
  [ElfDtNull{}, ElfDtNeeded{}, ElfDtPltrelsz{}, ElfDtPltgot{}, ElfDtHash{}, ElfDtStrtab{}, ElfDtSymtab{}, ElfDtRela{}, ElfDtRelasz{}, ElfDtRelaent{}, ElfDtStrsz{}, ElfDtSyment{}, ElfDtInit{}, ElfDtFini{}, ElfDtSoname{}, ElfDtRpath{}, ElfDtSymbolic{}, ElfDtRel{}, ElfDtRelsz{}, ElfDtRelent{}, ElfDtPltrel{}, ElfDtDebug{}, ElfDtTextrel{}, ElfDtJmprel{}, ElfDtBindNow{}, ElfDtInitArray{}, ElfDtFiniArray{}, ElfDtInitArraysz{}, ElfDtFiniArraysz{}, ElfDtRunpath{}, ElfDtFlags{}, ElfDtPreinitArray{}, ElfDtPreinitArraysz{}, ElfDtSymtabShndx{}, ElfDtRelrsz{}, ElfDtRelr{}, ElfDtRelrent{}, ElfDtGnuHash{}, ElfDtVersym{}, ElfDtRelacount{}, ElfDtRelcount{}, ElfDtFlags1{}, ElfDtVerdef{}, ElfDtVerdefnum{}, ElfDtVerneed{}, ElfDtVerneednum{}]

def ElfDynTag.of_code.pick(hit: Bool, k: ElfDynTag) -> Maybe<&2, ElfDynTag>:
  match hit:
    case True{}:
      Some{k}
    case False{}:
      None{}

def ElfDynTag.of_code.go(ks: List<&2, ElfDynTag>, +c: U32, found: Maybe<&2, ElfDynTag>) -> Maybe<&2, ElfDynTag>:
  match ks:
    case Nil{}:
      found
    case Con{+k, r}:
      match found:
        case Some{f}:
          Some{f}
        case None{}:
          ElfDynTag.of_code.go(r, c, ElfDynTag.of_code.pick(U32.is_eq(ElfDynTag.code(k), c), k))

# the name of a code, if it has one
def ElfDynTag.of_code(c: U32) -> Maybe<&2, ElfDynTag>:
  ElfDynTag.of_code.go(ElfDynTag.all(), c, None{})

# Internal: reading from a list

def ElfDyn.parse.d64(+big: Bool, +xs: List<&2, U32>) -> Result<&2, &2, F.ElfError, ElfDyn>:
  do Result<&2, &2, F.ElfError, ElfDyn>:
    d_tag : W.W64 <- F.elf_r64(big, xs, 0n)
    d_val : W.W64 <- F.elf_r64(big, xs, 8n)
    return ElfDyn{d_tag, d_val}

def ElfDyn.parse.d32(+big: Bool, +xs: List<&2, U32>) -> Result<&2, &2, F.ElfError, ElfDyn>:
  do Result<&2, &2, F.ElfError, ElfDyn>:
    d_tag : W.W64 <- F.elf_r32w(big, xs, 0n)
    d_val : W.W64 <- F.elf_r32w(big, xs, 4n)
    return ElfDyn{d_tag, d_val}

def ElfDyn.parse.list(is64: Bool, big: Bool, xs: List<&2, U32>) -> Result<&2, &2, F.ElfError, ElfDyn>:
  match is64:
    case True{}:
      ElfDyn.parse.d64(big, xs)
    case False{}:
      ElfDyn.parse.d32(big, xs)

# Public: writing one entry (its bytes), and the entry as the file stores it

def ElfDyn.write(+is64: Bool, +big: Bool, d: ElfDyn) -> B.Octets:
  match d:
    case ElfDyn{d_tag, d_val}:
      B.Octets.append(F.elf_wword(is64, big, d_tag), F.elf_wword(is64, big, d_val))

# the entry as the file stores it (ELF32 keeps the low 32 bits)
def ElfDyn.normal(+is64: Bool, d: ElfDyn) -> ElfDyn:
  match d:
    case ElfDyn{d_tag, d_val}:
      ElfDyn{F.elf_fit(is64, d_tag), F.elf_fit(is64, d_val)}

# Public: one entry, and a table

# the entry at the start of o (ElfTruncated if o is too short)
def ElfDyn.parse(is64: Bool, big: Bool, o: B.Octets) -> Result<&2, &2, F.ElfError, ElfDyn>:
  ElfDyn.parse.list(is64, big, B.Octets.to_list(o))

# Internal: n entries, step bytes apart (structural: the reference the proofs
# reason about)
def ElfDyn.table.list.ref(n: Nat, +is64: Bool, +big: Bool, +step: Nat, +xs: List<&2, U32>) -> Result<&2, &2, F.ElfError, List<&2, ElfDyn>>:
  match n:
    case 0n:
      Done{Nil{}}
    case 1n+p:
      F.elf_cons(ElfDyn, ElfDyn.parse.list(is64, big, xs), ElfDyn.table.list.ref(p, is64, big, step, B.drop(step, xs)))

# the entries read so far are kept reversed in acc; the first failure ends it
def ElfDyn.table.go(n: Nat, acc: Result<&2, &2, F.ElfError, List<&2, ElfDyn>>, +is64: Bool, +big: Bool, +step: Nat, +xs: List<&2, U32>) -> Result<&2, &2, F.ElfError, List<&2, ElfDyn>>:
  match n:
    case 0n:
      match acc:
        case Fail{e}:
          Fail{e}
        case Done{rs}:
          Done{F.elf_rev_onto(ElfDyn, rs, Nil{})}
    case 1n+p:
      match acc:
        case Fail{e}:
          Fail{e}
        case Done{rs}:
          ElfDyn.table.go(p, F.elf_push(ElfDyn, ElfDyn.parse.list(is64, big, xs), rs), is64, big, step, B.drop(step, xs))

# n entries, step bytes apart: table.list.ref, tail-recursive (PROOF.bend:
# dyn_table_eq), so a table can have any number of entries
def ElfDyn.table.list(n: Nat, +is64: Bool, +big: Bool, +step: Nat, +xs: List<&2, U32>) -> Result<&2, &2, F.ElfError, List<&2, ElfDyn>>:
  ElfDyn.table.go(n, Done{Nil{}}, is64, big, step, xs)

# Public: n entries, step bytes apart, from the start of o
def ElfDyn.read_table(is64: Bool, big: Bool, n: Nat, step: Nat, o: B.Octets) -> Result<&2, &2, F.ElfError, List<&2, ElfDyn>>:
  ElfDyn.table.list(n, is64, big, step, B.Octets.to_list(o))

# a table's bytes, its entries packed (structural)
def ElfDyn.write_table.ref(+is64: Bool, +big: Bool, xs: List<&2, ElfDyn>) -> B.Octets:
  match xs:
    case Nil{}:
      B.Octets.empty()
    case Con{x, r}:
      B.Octets.append(ElfDyn.write(is64, big, x), ElfDyn.write_table.ref(is64, big, r))

# the entries rs (the table's entries, last first) in front of acc
def ElfDyn.write_table.go(+is64: Bool, +big: Bool, rs: List<&2, ElfDyn>, acc: B.Octets) -> B.Octets:
  match rs:
    case Nil{}:
      acc
    case Con{x, r}:
      ElfDyn.write_table.go(is64, big, r, B.Octets.append(ElfDyn.write(is64, big, x), acc))

# a table's bytes, built from the last entry back, tail-recursively
# (write_table.ref is the structural form; PROOF.bend: dyn_write_eq)
def ElfDyn.write_table(+is64: Bool, +big: Bool, xs: List<&2, ElfDyn>) -> B.Octets:
  ElfDyn.write_table.go(is64, big, F.elf_rev_onto(ElfDyn, xs, Nil{}), B.Octets.empty())

def ElfDyn.normal_table.ref(+is64: Bool, xs: List<&2, ElfDyn>) -> List<&2, ElfDyn>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, r}:
      Con{ElfDyn.normal(is64, x), ElfDyn.normal_table.ref(is64, r)}

def ElfDyn.normal_table.go(+is64: Bool, xs: List<&2, ElfDyn>, acc: List<&2, ElfDyn>) -> List<&2, ElfDyn>:
  match xs:
    case Nil{}:
      F.elf_rev_onto(ElfDyn, acc, Nil{})
    case Con{x, r}:
      ElfDyn.normal_table.go(is64, r, Con{ElfDyn.normal(is64, x), acc})

# every entry as the file stores it, tail-recursively (normal_table.ref is
# the structural form; PROOF.bend: dyn_normal_eq)
def ElfDyn.normal_table(+is64: Bool, xs: List<&2, ElfDyn>) -> List<&2, ElfDyn>:
  ElfDyn.normal_table.go(is64, xs, Nil{})


# Tags

def ElfDyn.tag.go(small: Bool, lo: U32) -> Maybe<&2, ElfDynTag>:
  match small:
    case True{}:
      ElfDynTag.of_code(lo)
    case False{}:
      None{}

# the entry's tag, if it is one of the named ones
def ElfDyn.tag(d: ElfDyn) -> Maybe<&2, ElfDynTag>:
  +t = ElfDyn.d_tag(d)
  ElfDyn.tag.go(U32.is_eq(W.W64.hi(t), 0), W.W64.lo(t))

# whether the entry is DT_NULL, which ends the dynamic array
def ElfDyn.is_null(d: ElfDyn) -> Bool:
  W.W64.is_zero(ElfDyn.d_tag(d))

# (ended: the last entry kept, at the head of acc, is DT_NULL)
def ElfDyn.until_null.go(ds: List<&2, ElfDyn>, ended: Bool, acc: List<&2, ElfDyn>) -> List<&2, ElfDyn>:
  match ds ended:
    case _ True{}:
      F.elf_rev_onto(ElfDyn, acc, Nil{})
    case Nil{} False{}:
      F.elf_rev_onto(ElfDyn, acc, Nil{})
    case Con{+d, r} False{}:
      ElfDyn.until_null.go(r, ElfDyn.is_null(d), Con{d, acc})

# the entries up to and including the first DT_NULL, which ends the array
# (gABI); all of them if there is none. A section may hold DT_NULL entries
# after the end as padding.
def ElfDyn.until_null(ds: List<&2, ElfDyn>) -> List<&2, ElfDyn>:
  ElfDyn.until_null.go(ds, False{}, Nil{})

# the string an entry's d_val points to (DT_NEEDED, DT_SONAME, DT_RPATH,
# DT_RUNPATH), given the indexed string table at the dynamic section's
# sh_link; ElfOffsetOutOfRange if d_val is 2^32 or more
def ElfDyn.string(strtab: T.ElfStrtab, d: ElfDyn) -> Result<&2, &2, F.ElfError, B.Octets>:
  do Result<&2, &2, F.ElfError, B.Octets>:
    i : U32 <- F.elf_small(ElfDyn.d_val(d))
    s : B.Octets <- T.ElfStrtab.string(strtab, i)
    return s

# The dynamic section

# whether section s is the dynamic section (SHT_DYNAMIC, 6)
def ElfDyn.is_section(s: S.ElfShdr) -> Bool:
  U32.is_eq(S.ElfShdr.sh_type(s), 6)

def ElfDyn.section.pick(hit: Bool, s: S.ElfShdr) -> Maybe<&2, S.ElfShdr>:
  match hit:
    case True{}:
      Some{s}
    case False{}:
      None{}

def ElfDyn.section.go(ss: List<&2, S.ElfShdr>, found: Maybe<&2, S.ElfShdr>) -> Maybe<&2, S.ElfShdr>:
  match ss:
    case Nil{}:
      found
    case Con{+s, r}:
      match found:
        case Some{f}:
          Some{f}
        case None{}:
          ElfDyn.section.go(r, ElfDyn.section.pick(ElfDyn.is_section(s), s))

# the first SHT_DYNAMIC section of a section header table (the gABI allows
# one)
def ElfDyn.section(ss: List<&2, S.ElfShdr>) -> Maybe<&2, S.ElfShdr>:
  ElfDyn.section.go(ss, None{})

def ElfDyn.all.go(d: B.Octets, +is64: Bool, big: Bool, +entsize: U32, size: U32) -> Result<&2, &2, F.ElfError, List<&2, ElfDyn>>:
  do Result<&2, &2, F.ElfError, List<&2, ElfDyn>>:
    n : U32 <- F.elf_count(entsize, ElfDyn.size(is64), size)
    ds : List<&2, ElfDyn> <- ElfDyn.read_table(is64, big, U32.to_nat(n), U32.to_nat(entsize), d)
    return ds

# The entries of section s of the file o, whose header is h: sh_size /
# sh_entsize entries (ElfDyn.until_null keeps those before the end).
# ElfBadSectionType unless s is SHT_DYNAMIC; ElfBadEntrySize unless
# sh_entsize is at least an entry's size and divides sh_size.
def ElfDyn.all(o: B.Octets, +h: H.ElfHeader, +s: S.ElfShdr) -> Result<&2, &2, F.ElfError, List<&2, ElfDyn>>:
  do Result<&2, &2, F.ElfError, List<&2, ElfDyn>>:
    ok : Unit <- F.elf_check(ElfDyn.is_section(s), F.ElfBadSectionType{})
    d : B.Octets <- S.ElfShdr.bytes(o, s)
    entsize : U32 <- F.elf_small(S.ElfShdr.sh_entsize(s))
    size : U32 <- F.elf_small(S.ElfShdr.sh_size(s))
    ds : List<&2, ElfDyn> <- ElfDyn.all.go(d, H.ElfHeader.is64(h), H.ElfHeader.big(h), entsize, size)
    return ds
