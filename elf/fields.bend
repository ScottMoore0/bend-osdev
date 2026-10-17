# bend-osdev-elf, fields.bend: what every part of an ELF file shares. The error
# type, and (internal) the byte-order field readers and writers and the exact
# slicing the readers need.
#
# The readers work on the bytes as a list (B.Octets.to_list), so that reading
# at an offset walks the list once; the public defs in the other files take
# and answer Octets.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B

# Why a file was rejected
type ElfError is Data:
  # fewer bytes than the ELF header, or a table entry, needs
  ElfTruncated{}
  # e_ident does not start with 0x7f 'E' 'L' 'F'
  ElfBadMagic{}
  # EI_CLASS is neither ELFCLASS32 nor ELFCLASS64
  ElfBadClass{}
  # EI_DATA is neither ELFDATA2LSB nor ELFDATA2MSB
  ElfBadData{}
  # EI_VERSION is not EV_CURRENT
  ElfBadVersion{}
  # an offset or size past the end of the file (or of 2^32 or more)
  ElfOffsetOutOfRange{}
  # a table's entry size is smaller than its entries, or does not divide its size
  ElfBadEntrySize{}
  # a section index (e_shstrndx, sh_link) past the section header table
  ElfBadIndex{}
  # a string offset past its string table, or a string without its NUL
  ElfBadString{}
  # the counts are in section 0 (e_phnum PN_XNUM, e_shstrndx SHN_XINDEX), but
  # there is no section header table
  ElfNoSectionTable{}

# Internal helpers. Nothing below is public.

def elf_need(-A: Data, m: Maybe<&2, A>, e: ElfError) -> Result<&2, &2, ElfError, A>:
  match m:
    case Some{x}:
      Done{x}
    case None{}:
      Fail{e}

def elf_check(ok: Bool, e: ElfError) -> Result<&2, &2, ElfError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

# the bytes from offset n on; None if n is past the end
def elf_skip(n: Nat, xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match n:
    case 0n:
      Some{xs}
    case 1n+p:
      match xs:
        case Nil{}:
          None{}
        case Con{h, t}:
          elf_skip(p, t)

def elf_take.cons(h: U32, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{t}:
      Some{Con{h, t}}
    case None{}:
      None{}

# exactly the first n bytes; None if there are fewer
def elf_take(n: Nat, xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match n:
    case 0n:
      Some{Nil{}}
    case 1n+p:
      match xs:
        case Nil{}:
          None{}
        case Con{h, t}:
          elf_take.cons(h, elf_take(p, t))

# whether there are at least n bytes
def elf_at_least(n: Nat, xs: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match xs:
        case Nil{}:
          False{}
        case Con{h, t}:
          elf_at_least(p, t)

# whether the first byte is NUL (False for the empty string)
def elf_nul_first(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      U32.is_eq(B.byte(h), 0)

# the bytes before the first NUL, if there is one; nul: whether the first byte
# of xs is NUL
def elf_cstr.go(xs: List<&2, U32>, nul: Bool) -> Maybe<&2, List<&2, U32>>:
  match xs nul:
    case Nil{} _:
      None{}
    case Con{h, t} True{}:
      Some{Nil{}}
    case Con{h, +t} False{}:
      elf_take.cons(B.byte(h), elf_cstr.go(t, elf_nul_first(t)))

def elf_cstr(+xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  elf_cstr.go(xs, elf_nul_first(xs))

# a W64 offset or size as a U32, if it is below 2^32
def elf_small.go(fits: Bool, v: U32) -> Result<&2, &2, ElfError, U32>:
  match fits:
    case True{}:
      Done{v}
    case False{}:
      Fail{ElfOffsetOutOfRange{}}

def elf_small(+v: W.W64) -> Result<&2, &2, ElfError, U32>:
  elf_small.go(U32.is_eq(W.W64.hi(v), 0), W.W64.lo(v))

# the bytes from offset off on
def elf_seek(xs: List<&2, U32>, +off: W.W64) -> Result<&2, &2, ElfError, List<&2, U32>>:
  do Result<&2, &2, ElfError, List<&2, U32>>:
    o : U32 <- elf_small(off)
    r : List<&2, U32> <- elf_need(List<&2, U32>, elf_skip(U32.to_nat(o), xs), ElfOffsetOutOfRange{})
    return r

# Fields, in the file's byte order (big: most significant byte first)

def elf_u16(big: Bool, xs: List<&2, U32>, i: Nat) -> Maybe<&2, U32>:
  match big:
    case True{}:
      B.be16_at(xs, i)
    case False{}:
      B.le16_at(xs, i)

def elf_u32(big: Bool, xs: List<&2, U32>, i: Nat) -> Maybe<&2, U32>:
  match big:
    case True{}:
      B.be32_at(xs, i)
    case False{}:
      B.le32_at(xs, i)

def elf_u64(big: Bool, xs: List<&2, U32>, i: Nat) -> Maybe<&2, W.W64>:
  match big:
    case True{}:
      B.be64_at(xs, i)
    case False{}:
      B.le64_at(xs, i)

def elf_widen(m: Maybe<&2, U32>) -> Maybe<&2, W.W64>:
  match m:
    case Some{v}:
      Some{W.W64.from_parts(0, v)}
    case None{}:
      None{}

# a 32-bit field widened to W64 (an ELF32 address, offset or size)
def elf_u32w(big: Bool, xs: List<&2, U32>, i: Nat) -> Maybe<&2, W.W64>:
  elf_widen(elf_u32(big, xs, i))

def elf_w16(big: Bool, v: U32) -> B.Octets:
  match big:
    case True{}:
      B.Octets.be16(v)
    case False{}:
      B.Octets.le16(v)

def elf_w32(big: Bool, v: U32) -> B.Octets:
  match big:
    case True{}:
      B.Octets.be32(v)
    case False{}:
      B.Octets.le32(v)

def elf_w64(big: Bool, v: W.W64) -> B.Octets:
  match big:
    case True{}:
      B.Octets.be64(v)
    case False{}:
      B.Octets.le64(v)

# a class-sized word (Elf64_Addr, Elf64_Off, Elf64_Xword; Elf32_Addr, Elf32_Off,
# Elf32_Word): 8 bytes in ELF64, the low 4 bytes in ELF32
def elf_wword(is64: Bool, big: Bool, v: W.W64) -> B.Octets:
  match is64:
    case True{}:
      elf_w64(big, v)
    case False{}:
      elf_w32(big, W.W64.lo(v))

# what a class-sized word reads back as: all of it in ELF64, its low 32 bits
# in ELF32
def elf_fit(is64: Bool, v: W.W64) -> W.W64:
  match is64:
    case True{}:
      v
    case False{}:
      W.W64.from_parts(0, W.W64.lo(v))

# an entry in front of the rest of a table
def elf_cons(-A: Data, r: Result<&2, &2, ElfError, A>, rs: Result<&2, &2, ElfError, List<&2, A>>) -> Result<&2, &2, ElfError, List<&2, A>>:
  match r rs:
    case Done{x} Done{xs}:
      Done{Con{x, xs}}
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}

# A table of n entries of size bytes, entsize apart, is sound if it is empty or
# entsize is at least size.
def elf_table_ok(+n: U32, entsize: U32, size: U32) -> Bool:
  Bool.or(U32.is_eq(n, 0), U32.is_ge(entsize, size))

# the bytes of a table of n entries at offset off (none are needed if n is 0)
def elf_region.go(empty: Bool, xs: List<&2, U32>, off: W.W64) -> Result<&2, &2, ElfError, List<&2, U32>>:
  match empty:
    case True{}:
      Done{Nil{}}
    case False{}:
      elf_seek(xs, off)

def elf_region(xs: List<&2, U32>, off: W.W64, n: U32) -> Result<&2, &2, ElfError, List<&2, U32>>:
  elf_region.go(U32.is_eq(n, 0), xs, off)

# Fields read for a structure: a field past the end means the input ends
# inside the structure

def elf_r8(xs: List<&2, U32>, i: Nat) -> Result<&2, &2, ElfError, U32>:
  elf_need(U32, B.at(xs, i), ElfTruncated{})

def elf_r16(big: Bool, xs: List<&2, U32>, i: Nat) -> Result<&2, &2, ElfError, U32>:
  elf_need(U32, elf_u16(big, xs, i), ElfTruncated{})

def elf_r32(big: Bool, xs: List<&2, U32>, i: Nat) -> Result<&2, &2, ElfError, U32>:
  elf_need(U32, elf_u32(big, xs, i), ElfTruncated{})

def elf_r64(big: Bool, xs: List<&2, U32>, i: Nat) -> Result<&2, &2, ElfError, W.W64>:
  elf_need(W.W64, elf_u64(big, xs, i), ElfTruncated{})

def elf_r32w(big: Bool, xs: List<&2, U32>, i: Nat) -> Result<&2, &2, ElfError, W.W64>:
  elf_need(W.W64, elf_u32w(big, xs, i), ElfTruncated{})
