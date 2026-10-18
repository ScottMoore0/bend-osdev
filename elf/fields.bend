# bend-osdev-elf, fields.bend: what every part of an ELF file shares. The error
# type, and (internal) the byte-order field readers and writers, the exact
# slicing the readers need, the reference string lookup, and the walk along a
# chain of entries linked by offsets (symbol versions).
#
# The readers of one structure work on its bytes as a list (B.Octets.to_list);
# the readers of a whole file walk to what they read through Octets first
# (below), and the public defs in the other files take and answer Octets.
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
  # a section of another type than the reader needs (relocations from a
  # section neither SHT_REL nor SHT_RELA, a dynamic section not SHT_DYNAMIC,
  # notes not SHT_NOTE, ...)
  ElfBadSectionType{}

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
# of xs is NUL; acc: the bytes before xs, reversed (tail-recursive, so a
# string, or a table missing its NUL, can be of any length)
def elf_cstr.go(xs: List<&2, U32>, nul: Bool, acc: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match xs nul:
    case Nil{} _:
      None{}
    case Con{h, t} True{}:
      Some{B.rev(acc)}
    case Con{h, +t} False{}:
      elf_cstr.go(t, elf_nul_first(t), Con{B.byte(h), acc})

def elf_cstr(+xs: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  elf_cstr.go(xs, elf_nul_first(xs), Nil{})

# The reference string lookup: the NUL-terminated string at offset n of a
# string table's bytes xs (without its NUL), None if n is not inside xs or
# there is no NUL after it. Structural in xs (and tail-recursive, so offsets
# of any size); strtab.bend's index is proved equal to it (PROOF.bend).
def elf_string.list(xs: List<&2, U32>, n: Nat) -> Maybe<&2, List<&2, U32>>:
  match xs n:
    case Nil{} _:
      None{}
    case Con{h, t} 0n:
      elf_cstr(Con{h, t})
    case Con{h, t} 1n+p:
      elf_string.list(t, p)

# a looked-up string as the public lookups answer it
def elf_string.result(m: Maybe<&2, List<&2, U32>>) -> Result<&2, &2, ElfError, B.Octets>:
  match m:
    case Some{s}:
      Done{B.Octets.of_list(s)}
    case None{}:
      Fail{ElfBadString{}}

# a W64 offset or size as a U32, if it is below 2^32
def elf_small.go(fits: Bool, v: U32) -> Result<&2, &2, ElfError, U32>:
  match fits:
    case True{}:
      Done{v}
    case False{}:
      Fail{ElfOffsetOutOfRange{}}

def elf_small(+v: W.W64) -> Result<&2, &2, ElfError, U32>:
  elf_small.go(U32.is_eq(W.W64.hi(v), 0), W.W64.lo(v))

# Octets-level access: a reader of a whole file walks to the bytes it reads
# (B.Octets.drop shares the rest) and converts only those to a list, so that
# reading a table or a section of a large file does not hold a list of the
# whole file

def elf_skip.oct.at(m: Maybe<&2, U32>, +n: Nat, o: B.Octets) -> Maybe<&2, B.Octets>:
  match m:
    case Some{b}:
      Some{B.Octets.drop(n, o)}
    case None{}:
      None{}

# the bytes from offset n on; None if n is past the end
def elf_skip.oct(n: Nat, +o: B.Octets) -> Maybe<&2, B.Octets>:
  match n:
    case 0n:
      Some{o}
    case 1n+(+p):
      elf_skip.oct.at(B.Octets.at(o, p), 1n+p, o)

def elf_take.oct.at(m: Maybe<&2, U32>, +n: Nat, o: B.Octets) -> Maybe<&2, B.Octets>:
  match m:
    case Some{b}:
      Some{B.Octets.take(n, o)}
    case None{}:
      None{}

# exactly the first n bytes; None if there are fewer
def elf_take.oct(n: Nat, +o: B.Octets) -> Maybe<&2, B.Octets>:
  match n:
    case 0n:
      Some{B.Octets.empty()}
    case 1n+(+p):
      elf_take.oct.at(B.Octets.at(o, p), 1n+p, o)

# the first n bytes of o as a list (fewer if o is shorter)
def elf_head(n: Nat, o: B.Octets) -> List<&2, U32>:
  B.Octets.to_list(B.Octets.take(n, o))

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

# a signed 32-bit value (an Elf32_Sword) sign-extended to 64 bits
def elf_sign(neg: Bool) -> U32:
  match neg:
    case True{}:
      4294967295
    case False{}:
      0

def elf_sext(+v: U32) -> W.W64:
  W.W64.from_parts(elf_sign(U32.is_ge(v, 2147483648)), v)

# what a class-sized word reads back as: all of it in ELF64, its low 32 bits
# in ELF32
def elf_fit(is64: Bool, v: W.W64) -> W.W64:
  match is64:
    case True{}:
      v
    case False{}:
      W.W64.from_parts(0, W.W64.lo(v))

# a list reversed in front of acc
def elf_rev_onto(-A: Data, xs: List<&2, A>, acc: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      elf_rev_onto(A, t, Con{h, acc})

# an entry pushed onto the entries read so far (kept reversed)
def elf_push(-A: Data, r: Result<&2, &2, ElfError, A>, rs: List<&2, A>) -> Result<&2, &2, ElfError, List<&2, A>>:
  match r:
    case Done{x}:
      Done{Con{x, rs}}
    case Fail{e}:
      Fail{e}

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

# the number of entries in a section of size bytes whose entries, of esize
# bytes each, are entsize apart: ElfBadEntrySize unless entsize is at least
# esize and divides size
def elf_count(+entsize: U32, esize: U32, +size: U32) -> Result<&2, &2, ElfError, U32>:
  do Result<&2, &2, ElfError, U32>:
    ok : Unit <- elf_check(U32.is_ge(entsize, esize), ElfBadEntrySize{})
    ok2 : Unit <- elf_check(U32.is_eq(U32.mod(size, entsize), 0), ElfBadEntrySize{})
    return U32.div(size, entsize)

# Chains: entries linked by offsets from one to the next (symbol versions)

# a link of a chain: an entry, and the bytes from the next entry on (None at
# the end of the chain)
type ElfLink<-A: Data> is Data:
  ElfLink{x: A, next: Maybe<&2, B.Octets>}

# up to n entries of a chain, the first read already (r); step reads the
# entry at the start of some bytes and finds the next; the entries read so
# far are kept reversed in acc. The chain ends after n entries, or at an
# entry with no next one.
def elf_chain.go(~A: Data, ~step: Bool -> B.Octets -> Result<&2, &2, ElfError, ElfLink<A>>, n: Nat, +big: Bool, r: Result<&2, &2, ElfError, ElfLink<A>>, acc: List<&2, A>) -> Result<&2, &2, ElfError, List<&2, A>>:
  match n:
    case 0n:
      Done{elf_rev_onto(A, acc, Nil{})}
    case 1n+p:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{ElfLink{x, next}}:
          match next:
            case None{}:
              Done{elf_rev_onto(A, Con{x, acc}, Nil{})}
            case Some{o}:
              elf_chain.go(~A, ~step, p, big, step(big, o), Con{x, acc})

# n entries of a chain starting at the start of o (none if n is 0)
def elf_chain.start(~A: Data, ~step: Bool -> B.Octets -> Result<&2, &2, ElfError, ElfLink<A>>, n: Nat, +big: Bool, o: B.Octets) -> Result<&2, &2, ElfError, List<&2, A>>:
  match n:
    case 0n:
      Done{Nil{}}
    case 1n+p:
      elf_chain.go(~A, ~step, 1n+p, big, step(big, o), Nil{})

# the bytes of o from offset off on; ElfOffsetOutOfRange if off is past the
# end (or 2^32 or more)
def elf_seek.oct(+o: B.Octets, +off: W.W64) -> Result<&2, &2, ElfError, B.Octets>:
  do Result<&2, &2, ElfError, B.Octets>:
    k : U32 <- elf_small(off)
    r : B.Octets <- elf_need(B.Octets, elf_skip.oct(U32.to_nat(k), o), ElfOffsetOutOfRange{})
    return r

# the next entry of a chain, off bytes after this one, which starts o: none if
# off is 0 (the end of the chain); ElfOffsetOutOfRange if it is past the end
def elf_link.next.go(end: Bool, +o: B.Octets, +off: U32) -> Result<&2, &2, ElfError, Maybe<&2, B.Octets>>:
  match end:
    case True{}:
      Done{None{}}
    case False{}:
      do Result<&2, &2, ElfError, Maybe<&2, B.Octets>>:
        r : B.Octets <- elf_seek.oct(o, W.W64.from_parts(0, off))
        return Some{r}

def elf_link.next(+o: B.Octets, +off: U32) -> Result<&2, &2, ElfError, Maybe<&2, B.Octets>>:
  elf_link.next.go(U32.is_eq(off, 0), o, off)

# the offset a packed chain's entry links to the next with: 0 for the last
def elf_link.off(last: Bool, off: U32) -> U32:
  match last:
    case True{}:
      0
    case False{}:
      off

def elf_region.oct.go(empty: Bool, o: B.Octets, off: W.W64) -> Result<&2, &2, ElfError, B.Octets>:
  match empty:
    case True{}:
      Done{B.Octets.empty()}
    case False{}:
      elf_seek.oct(o, off)

# the bytes of a table of n entries at offset off (none are needed if n is 0)
def elf_region.oct(o: B.Octets, off: W.W64, n: U32) -> Result<&2, &2, ElfError, B.Octets>:
  elf_region.oct.go(U32.is_eq(n, 0), o, off)

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
