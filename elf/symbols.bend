# bend-osdev-elf, symbols.bend: symbol tables (gABI, "Symbol Table"; ELF-64
# Object File Format, section 7): entries one by one, the table of a
# SHT_SYMTAB or SHT_DYNSYM section, st_info's binding and type, and names.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./fields.bend as F
import ./header.bend as H
import ./sections.bend as S

# A symbol table entry. st_info and st_other are bytes, st_shndx is 16 bits;
# in ELF32, st_value and st_size are widened to W64.
type ElfSym is Data:
  ElfSym{st_name: U32, st_value: W.W64, st_size: W.W64, st_info: U32, st_other: U32, st_shndx: U32}

# the fields of an ElfSym

def ElfSym.st_name(r: ElfSym) -> U32:
  match r:
    case ElfSym{x, _, _, _, _, _}:
      x

def ElfSym.st_value(r: ElfSym) -> W.W64:
  match r:
    case ElfSym{_, x, _, _, _, _}:
      x

def ElfSym.st_size(r: ElfSym) -> W.W64:
  match r:
    case ElfSym{_, _, x, _, _, _}:
      x

def ElfSym.st_info(r: ElfSym) -> U32:
  match r:
    case ElfSym{_, _, _, x, _, _}:
      x

def ElfSym.st_other(r: ElfSym) -> U32:
  match r:
    case ElfSym{_, _, _, _, x, _}:
      x

def ElfSym.st_shndx(r: ElfSym) -> U32:
  match r:
    case ElfSym{_, _, _, _, _, x}:
      x


# an entry's size: 24 bytes in ELF64, 16 in ELF32
def ElfSym.size(is64: Bool) -> U32:
  match is64:
    case True{}:
      24
    case False{}:
      16

# st_info's binding and type, and st_other's visibility (gABI: ELF32_ST_BIND,
# ELF32_ST_TYPE, ELF32_ST_VISIBILITY; the same for ELF64)

def ElfSym.bind(s: ElfSym) -> U32:
  U32.shrn(B.byte(ElfSym.st_info(s)), 4n)

def ElfSym.type(s: ElfSym) -> U32:
  U32.and(15, ElfSym.st_info(s))

def ElfSym.visibility(s: ElfSym) -> U32:
  U32.and(3, ElfSym.st_other(s))

# st_info from a binding and a type (ELF32_ST_INFO)
def ElfSym.info(bind: U32, kind: U32) -> U32:
  U32.or(U32.shln(U32.and(15, bind), 4n), U32.and(15, kind))

# Internal: reading from a list

def ElfSym.parse.y64(+big: Bool, +xs: List<&2, U32>) -> Result<&2, &2, F.ElfError, ElfSym>:
  do Result<&2, &2, F.ElfError, ElfSym>:
    st_name : U32 <- F.elf_r32(big, xs, 0n)
    st_info : U32 <- F.elf_r8(xs, 4n)
    st_other : U32 <- F.elf_r8(xs, 5n)
    st_shndx : U32 <- F.elf_r16(big, xs, 6n)
    st_value : W.W64 <- F.elf_r64(big, xs, 8n)
    st_size : W.W64 <- F.elf_r64(big, xs, 16n)
    return ElfSym{st_name, st_value, st_size, st_info, st_other, st_shndx}

def ElfSym.parse.y32(+big: Bool, +xs: List<&2, U32>) -> Result<&2, &2, F.ElfError, ElfSym>:
  do Result<&2, &2, F.ElfError, ElfSym>:
    st_name : U32 <- F.elf_r32(big, xs, 0n)
    st_value : W.W64 <- F.elf_r32w(big, xs, 4n)
    st_size : W.W64 <- F.elf_r32w(big, xs, 8n)
    st_info : U32 <- F.elf_r8(xs, 12n)
    st_other : U32 <- F.elf_r8(xs, 13n)
    st_shndx : U32 <- F.elf_r16(big, xs, 14n)
    return ElfSym{st_name, st_value, st_size, st_info, st_other, st_shndx}

def ElfSym.parse.list(is64: Bool, big: Bool, xs: List<&2, U32>) -> Result<&2, &2, F.ElfError, ElfSym>:
  match is64:
    case True{}:
      ElfSym.parse.y64(big, xs)
    case False{}:
      ElfSym.parse.y32(big, xs)

# n entries, step bytes apart (structural: the reference the proofs reason
# about)
def ElfSym.table.list.ref(n: Nat, +is64: Bool, +big: Bool, +step: Nat, +xs: List<&2, U32>) -> Result<&2, &2, F.ElfError, List<&2, ElfSym>>:
  match n:
    case 0n:
      Done{Nil{}}
    case 1n+p:
      F.elf_cons(ElfSym, ElfSym.parse.list(is64, big, xs), ElfSym.table.list.ref(p, is64, big, step, B.drop(step, xs)))

# the entries read so far are kept reversed in acc; the first failure ends it
def ElfSym.table.go(n: Nat, acc: Result<&2, &2, F.ElfError, List<&2, ElfSym>>, +is64: Bool, +big: Bool, +step: Nat, +xs: List<&2, U32>) -> Result<&2, &2, F.ElfError, List<&2, ElfSym>>:
  match n:
    case 0n:
      match acc:
        case Fail{e}:
          Fail{e}
        case Done{rs}:
          Done{F.elf_rev_onto(ElfSym, rs, Nil{})}
    case 1n+p:
      match acc:
        case Fail{e}:
          Fail{e}
        case Done{rs}:
          ElfSym.table.go(p, F.elf_push(ElfSym, ElfSym.parse.list(is64, big, xs), rs), is64, big, step, B.drop(step, xs))

# n entries, step bytes apart: table.list.ref, tail-recursive (PROOF.bend:
# sym_table_eq), so a table can have any number of entries
def ElfSym.table.list(n: Nat, +is64: Bool, +big: Bool, +step: Nat, +xs: List<&2, U32>) -> Result<&2, &2, F.ElfError, List<&2, ElfSym>>:
  ElfSym.table.go(n, Done{Nil{}}, is64, big, step, xs)

# Public: one entry, and a table

# the symbol table entry at the start of o (ElfTruncated if o is too short)
def ElfSym.parse(is64: Bool, big: Bool, o: B.Octets) -> Result<&2, &2, F.ElfError, ElfSym>:
  ElfSym.parse.list(is64, big, B.Octets.to_list(o))

# n entries, step bytes apart, from the start of o
def ElfSym.read_table(is64: Bool, big: Bool, n: Nat, step: Nat, o: B.Octets) -> Result<&2, &2, F.ElfError, List<&2, ElfSym>>:
  ElfSym.table.list(n, is64, big, step, B.Octets.to_list(o))

def ElfSym.write(is64: Bool, +big: Bool, s: ElfSym) -> B.Octets:
  match is64 s:
    case True{} ElfSym{st_name, st_value, st_size, st_info, st_other, st_shndx}:
      B.Octets.concat([F.elf_w32(big, st_name), B.Octets.of_list([st_info, st_other]), F.elf_w16(big, st_shndx), F.elf_w64(big, st_value), F.elf_w64(big, st_size)])
    case False{} ElfSym{st_name, st_value, st_size, st_info, st_other, st_shndx}:
      B.Octets.concat([F.elf_w32(big, st_name), F.elf_w32(big, W.W64.lo(st_value)), F.elf_w32(big, W.W64.lo(st_size)), B.Octets.of_list([st_info, st_other]), F.elf_w16(big, st_shndx)])

# the entry as the file stores it: st_info and st_other keep their low 8 bits,
# st_shndx its low 16, and ELF32 the low 32 bits of st_value and st_size
def ElfSym.normal(+is64: Bool, s: ElfSym) -> ElfSym:
  match s:
    case ElfSym{st_name, st_value, st_size, st_info, st_other, st_shndx}:
      ElfSym{st_name, F.elf_fit(is64, st_value), F.elf_fit(is64, st_size), B.byte(st_info), B.byte(st_other), B.low16(st_shndx)}

# a table's bytes, its entries packed
def ElfSym.write_table.ref(+is64: Bool, +big: Bool, ss: List<&2, ElfSym>) -> B.Octets:
  match ss:
    case Nil{}:
      B.Octets.empty()
    case Con{s, t}:
      B.Octets.append(ElfSym.write(is64, big, s), ElfSym.write_table.ref(is64, big, t))

# the entries rs (the table's entries, last first) in front of acc
def ElfSym.write_table.go(+is64: Bool, +big: Bool, rs: List<&2, ElfSym>, acc: B.Octets) -> B.Octets:
  match rs:
    case Nil{}:
      acc
    case Con{s, t}:
      ElfSym.write_table.go(is64, big, t, B.Octets.append(ElfSym.write(is64, big, s), acc))

# a table's bytes, built from the last entry back, tail-recursively
# (write_table.ref is the structural form; PROOF.bend: sym_write_eq)
def ElfSym.write_table(+is64: Bool, +big: Bool, ss: List<&2, ElfSym>) -> B.Octets:
  ElfSym.write_table.go(is64, big, F.elf_rev_onto(ElfSym, ss, Nil{}), B.Octets.empty())

def ElfSym.normal_table.ref(+is64: Bool, ss: List<&2, ElfSym>) -> List<&2, ElfSym>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      Con{ElfSym.normal(is64, s), ElfSym.normal_table.ref(is64, t)}

def ElfSym.normal_table.go(+is64: Bool, ss: List<&2, ElfSym>, acc: List<&2, ElfSym>) -> List<&2, ElfSym>:
  match ss:
    case Nil{}:
      F.elf_rev_onto(ElfSym, acc, Nil{})
    case Con{s, t}:
      ElfSym.normal_table.go(is64, t, Con{ElfSym.normal(is64, s), acc})

# every entry as the file stores it, tail-recursively (normal_table.ref is
# the structural form; PROOF.bend: sym_normal_eq)
def ElfSym.normal_table(+is64: Bool, ss: List<&2, ElfSym>) -> List<&2, ElfSym>:
  ElfSym.normal_table.go(is64, ss, Nil{})

# The symbol table of a section

def ElfSym.all.go(d: B.Octets, +is64: Bool, big: Bool, +entsize: U32, +size: U32) -> Result<&2, &2, F.ElfError, List<&2, ElfSym>>:
  do Result<&2, &2, F.ElfError, List<&2, ElfSym>>:
    ok : Unit <- F.elf_check(U32.is_ge(entsize, ElfSym.size(is64)), F.ElfBadEntrySize{})
    ok2 : Unit <- F.elf_check(U32.is_eq(U32.mod(size, entsize), 0), F.ElfBadEntrySize{})
    ss : List<&2, ElfSym> <- ElfSym.read_table(is64, big, U32.to_nat(U32.div(size, entsize)), U32.to_nat(entsize), d)
    return ss

# The symbols of section s (SHT_SYMTAB or SHT_DYNSYM) of the file o, whose
# header is h: sh_size / sh_entsize entries. ElfBadEntrySize unless sh_entsize
# is at least an entry's size and divides sh_size.
def ElfSym.all(o: B.Octets, +h: H.ElfHeader, +s: S.ElfShdr) -> Result<&2, &2, F.ElfError, List<&2, ElfSym>>:
  do Result<&2, &2, F.ElfError, List<&2, ElfSym>>:
    d : B.Octets <- S.ElfShdr.bytes(o, s)
    entsize : U32 <- F.elf_small(S.ElfShdr.sh_entsize(s))
    size : U32 <- F.elf_small(S.ElfShdr.sh_size(s))
    ss : List<&2, ElfSym> <- ElfSym.all.go(d, H.ElfHeader.is64(h), H.ElfHeader.big(h), entsize, size)
    return ss

# a symbol's name, given the bytes of its string table (the section at the
# symbol table's sh_link)
def ElfSym.name(strtab: B.Octets, s: ElfSym) -> Result<&2, &2, F.ElfError, B.Octets>:
  S.ElfShdr.string(strtab, ElfSym.st_name(s))
