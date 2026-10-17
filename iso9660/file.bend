# bend-osdev-iso9660, file.bend: reading a file's data (ECMA-119, 4th
# edition, 6.5 and 9.1). A file is one extent, or several (multi-extent),
# each a run of logical blocks from its location (after any extended
# attribute record) holding its data length in bytes. Reading never goes
# past a file's data length: the last block of an extent is cut there.
#
# Two ways in: streaming, a block at a time (IsoCursor: start, next), and a
# byte range (read). Interleaved files (file unit size not 0) are refused.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as BD
import ./fields.bend as F
import ./dirrec.bend as R
import ./dir.bend as DR

# Streaming

# where a stream is: the extents left (the current one first, none of them
# empty), the block reached in the current one, and its bytes left
type IsoCursor is Data:
  IsoCursor{extents: List<&2, DR.IsoExtent>, block: Nat, left: U32}

# what a step of a stream gives: the end, or the next piece and the rest
type IsoChunk is Data:
  IsoChunkEnd{}
  IsoChunkData{data: B.Octets, next: IsoCursor}

def iso.file.nonempty.pick(empty: Bool, x: DR.IsoExtent, rest: List<&2, DR.IsoExtent>) -> List<&2, DR.IsoExtent>:
  match empty:
    case True{}:
      rest
    case False{}:
      Con{x, rest}

# the extents with the empty ones left out
def iso.file.nonempty(xs: List<&2, DR.IsoExtent>) -> List<&2, DR.IsoExtent>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{DR.IsoExtent{b, +s}, t}:
      iso.file.nonempty.pick(U32.is_eq(s, 0), DR.IsoExtent{b, s}, iso.file.nonempty(t))

# a stream at the start of these extents
def iso.file.cursor(+xs: List<&2, DR.IsoExtent>) -> IsoCursor:
  match xs:
    case Nil{}:
      IsoCursor{Nil{}, 0n, 0}
    case Con{DR.IsoExtent{b, s}, t}:
      IsoCursor{xs, 0n, s}

def iso.file.ok(dir: Bool, inter: Bool, +name: String, +e: DR.IsoEntry) -> Result<&2, &2, F.IsoError, DR.IsoEntry>:
  match dir inter:
    case True{} _:
      Fail{F.IsoIsDirectory{name}}
    case False{} True{}:
      Fail{F.IsoInterleaved{}}
    case False{} False{}:
      Done{e}

# a file entry that can be read: not a directory, not interleaved
def iso.file.check(+e: DR.IsoEntry) -> Result<&2, &2, F.IsoError, DR.IsoEntry>:
  match e:
    case DR.IsoEntry{+n, d, s, x, R.IsoDirRec{ea, ex, sz, dt, fl, us, gp, vs, id, su}, rr}:
      iso.file.ok(d, Bool.not(U32.is_eq(us, 0)), n, e)

# a stream at the start of a file
def Iso.file_start(e: DR.IsoEntry) -> Result<&2, &2, F.IsoError, IsoCursor>:
  Result.map(&2, &2, F.IsoError, DR.IsoEntry, IsoCursor, x => iso.file.cursor(iso.file.nonempty(DR.IsoEntry.extents_of(x))), iso.file.check(e))

# the cursor after taking n bytes of the current extent (left of them were left)
def iso.file.after(done: Bool, xs: List<&2, DR.IsoExtent>, +i: Nat, left: U32) -> IsoCursor:
  match done:
    case True{}:
      match xs:
        case Nil{}:
          IsoCursor{Nil{}, 0n, 0}
        case Con{x, t}:
          iso.file.cursor(t)
    case False{}:
      IsoCursor{xs, 1n+i, left}

def iso.file.piece(+xs: List<&2, DR.IsoExtent>, +i: Nat, +left: U32, blk: B.Octets) -> IsoChunk:
  +n = U32.min(left, 2048)
  +rest = U32.sub(left, n)
  IsoChunkData{B.Octets.take(U32.to_nat(n), blk), iso.file.after(U32.is_eq(rest, 0), xs, i, rest)}

def iso.file.piece.r(+xs: List<&2, DR.IsoExtent>, +i: Nat, +left: U32, r: Result<&2, &2, F.IsoError, B.Octets>) -> Result<&2, &2, F.IsoError, IsoChunk>:
  match r:
    case Done{blk}:
      Done{iso.file.piece(xs, i, left, blk)}
    case Fail{e}:
      Fail{e}

# the next piece of a stream: the next block of the file, cut at its data
# length, or the end
def Iso.file_next(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, d: D, c: IsoCursor) -> Result<&2, &2, F.IsoError, IsoChunk>:
  match c:
    case IsoCursor{Nil{}, i, left}:
      Done{IsoChunkEnd{}}
    case IsoCursor{Con{DR.IsoExtent{+b, s}, t}, +i, +left}:
      iso.file.piece.r(Con{DR.IsoExtent{b, s}, t}, i, left, F.iso.read_sector(~D, ~read_block, d, Nat.add(U32.to_nat(b), i)))

# A byte range

def iso.file.dev(r: Result<&2, &2, BD.DevError, B.Octets>) -> Result<&2, &2, F.IsoError, B.Octets>:
  F.iso.dev(r)

# n bytes from byte off of an extent at block b (n and off within it)
def iso.file.span(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, d: D, b: U32, off: Nat, n: Nat) -> Result<&2, &2, F.IsoError, B.Octets>:
  iso.file.dev(BD.Dev.read_bytes(~D, ~block_size, ~read_block, d, Nat.add(Nat.mul(U32.to_nat(b), 2048n), off), n))

def iso.file.range(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, xs: List<&2, DR.IsoExtent>, +d: D, +off: Nat, +len: Nat) -> Result<&2, &2, F.IsoError, B.Octets>:
  match xs:
    case Nil{}:
      Done{B.Octets.empty()}
    case Con{DR.IsoExtent{b, s}, t}:
      +size = U32.to_nat(s)
      +n = Nat.min(len, Nat.sub(size, off))
      do Result<&2, &2, F.IsoError, B.Octets>:
        here : B.Octets <- iso.file.span(~D, ~block_size, ~read_block, d, b, Nat.min(off, size), n)
        more : B.Octets <- iso.file.range(~D, ~block_size, ~read_block, t, d, Nat.sub(off, size), Nat.sub(len, n))
        return B.Octets.append(here, more)

# the bytes from off to off + len of a file, or fewer where the file ends
# (no byte past its data length is read or answered)
def Iso.file_read(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, +d: D, e: DR.IsoEntry, +off: Nat, +len: Nat) -> Result<&2, &2, F.IsoError, B.Octets>:
  Result.bind(&2, &2, F.IsoError, DR.IsoEntry, B.Octets, iso.file.check(e), x => iso.file.range(~D, ~block_size, ~read_block, DR.IsoEntry.extents_of(x), d, off, len))
