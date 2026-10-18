# bend-osdev-elf: reading and writing ELF files (System V ABI, generic ABI,
# chapter 4 "Object Files" and chapter 5 "Program Loading"; the ELF-64 Object
# File Format, version 1.5), in both classes (ELF32, ELF64) and both data
# encodings (little- and big-endian).
#
# This file is the main concern: a whole file at once (its header, program
# headers, section headers and section names), finding a section by name, and
# a section's symbols. The parts live beside it: fields.bend (the error type),
# header.bend, segments.bend, sections.bend, symbols.bend, strtab.bend (string
# tables indexed by offset), relocs.bend, dynamic.bend, notes.bend and
# versions.bend, each usable on its own.
#
# Every 64-bit field is a W64 (bend-osdev-word64); an ELF32 file's 32-bit
# addresses, offsets and sizes are widened, so one record type serves both
# classes. Byte strings are Octets (bend-osdev-bytes). Every reader answers a
# Result: Fail{e} names what was wrong (fields.bend's ElfError), never a wrong
# value. Offsets and sizes of 2^32 or more fail with ElfOffsetOutOfRange: no
# byte string that long fits in memory.
import Base
import ../bytes/bytes.bend as B
import ./fields.bend as F
import ./header.bend as H
import ./sections.bend as S
import ./segments.bend as P
import ./symbols.bend as Y
import ./strtab.bend as T

# A file's tables: its header, its program headers, its section headers, and
# the bytes of its section-name string table (empty if it has none)
type ElfFile is Data:
  ElfFile{header: H.ElfHeader, segments: List<&2, P.ElfPhdr>, sections: List<&2, S.ElfShdr>, shstrtab: B.Octets}

def ElfFile.header(f: ElfFile) -> H.ElfHeader:
  match f:
    case ElfFile{h, _, _, _}:
      h

def ElfFile.segments(f: ElfFile) -> List<&2, P.ElfPhdr>:
  match f:
    case ElfFile{_, ps, _, _}:
      ps

def ElfFile.sections(f: ElfFile) -> List<&2, S.ElfShdr>:
  match f:
    case ElfFile{_, _, ss, _}:
      ss

def ElfFile.shstrtab(f: ElfFile) -> B.Octets:
  match f:
    case ElfFile{_, _, _, t}:
      t

# the section-name string table; none if the index is SHN_UNDEF
def ElfFile.names.go(undef: Bool, o: B.Octets, ss: List<&2, S.ElfShdr>, i: U32) -> Result<&2, &2, F.ElfError, B.Octets>:
  match undef:
    case True{}:
      Done{B.Octets.empty()}
    case False{}:
      S.ElfShdr.bytes_at(o, ss, i)

def ElfFile.names(+o: B.Octets, +h: H.ElfHeader, ss: List<&2, S.ElfShdr>) -> Result<&2, &2, F.ElfError, B.Octets>:
  do Result<&2, &2, F.ElfError, B.Octets>:
    +i : U32 <- S.ElfShdr.shstrndx(o, h)
    t : B.Octets <- ElfFile.names.go(U32.is_eq(i, 0), o, ss, i)
    return t

# The tables of the file o; the first failure if any of them is malformed
def ElfFile.read_with(opts: H.ElfOptions, +o: B.Octets) -> Result<&2, &2, F.ElfError, ElfFile>:
  do Result<&2, &2, F.ElfError, ElfFile>:
    # the header is at most 64 bytes: only those become a list
    +h : H.ElfHeader <- H.ElfHeader.parse_with(opts, B.Octets.take(64n, o))
    ps : List<&2, P.ElfPhdr> <- P.ElfPhdr.all(o, h)
    +ss : List<&2, S.ElfShdr> <- S.ElfShdr.all(o, h)
    t : B.Octets <- ElfFile.names(o, h, ss)
    return ElfFile{h, ps, ss, t}

def ElfFile.read(+o: B.Octets) -> Result<&2, &2, F.ElfError, ElfFile>:
  ElfFile.read_with(H.ElfOptions.default(), o)

# a section's name
def ElfFile.section_name(f: ElfFile, s: S.ElfShdr) -> Result<&2, &2, F.ElfError, B.Octets>:
  S.ElfShdr.name(ElfFile.shstrtab(f), s)

def ElfFile.name_is(r: Result<&2, &2, F.ElfError, B.Octets>, name: B.Octets) -> Bool:
  match r:
    case Done{n}:
      B.Octets.is_eq(n, name)
    case Fail{e}:
      False{}

def ElfFile.find.pick(hit: Bool, s: S.ElfShdr) -> Maybe<&2, S.ElfShdr>:
  match hit:
    case True{}:
      Some{s}
    case False{}:
      None{}

# the first of ss named name, unless found holds one already; tail-recursive,
# so a file can have any number of sections
def ElfFile.find.go(ss: List<&2, S.ElfShdr>, found: Maybe<&2, S.ElfShdr>, +names: T.ElfStrtab, +name: B.Octets) -> Maybe<&2, S.ElfShdr>:
  match ss:
    case Nil{}:
      found
    case Con{+s, t}:
      match found:
        case Some{f}:
          Some{f}
        case None{}:
          ElfFile.find.go(t, ElfFile.find.pick(ElfFile.name_is(S.ElfShdr.name_in(names, s), name), s), names, name)

# the section-name string table, indexed (strtab.bend), for naming many
# sections: S.ElfShdr.name_in(ElfFile.section_names(f), s)
def ElfFile.section_names(f: ElfFile) -> T.ElfStrtab:
  T.ElfStrtab.of(ElfFile.shstrtab(f))

# the first section named name (".symtab", ".dynsym", ".text", ...); the
# names are looked up through an index, built once
def ElfFile.find_section(+f: ElfFile, name: B.Octets) -> Maybe<&2, S.ElfShdr>:
  ElfFile.find.go(ElfFile.sections(f), None{}, ElfFile.section_names(f), name)

# the symbols of section s of the file o, read as f
def ElfFile.symbols(o: B.Octets, f: ElfFile, s: S.ElfShdr) -> Result<&2, &2, F.ElfError, List<&2, Y.ElfSym>>:
  Y.ElfSym.all(o, ElfFile.header(f), s)

# the bytes of the string table of section s (the section at its sh_link):
# for a symbol table, its symbols' names
def ElfFile.strtab(o: B.Octets, f: ElfFile, s: S.ElfShdr) -> Result<&2, &2, F.ElfError, B.Octets>:
  S.ElfShdr.bytes_at(o, ElfFile.sections(f), S.ElfShdr.sh_link(s))
