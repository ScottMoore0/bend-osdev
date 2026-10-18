# bend-osdev-ext2: reading a file's data, through its block map (ext2/3) or
# its extent tree (ext4, the inode's EXTENTS_FL flag), a block at a time or
# by byte range, never past the file's size. Holes, and unwritten extents,
# read as zeros. Symbolic link targets: fast ones (under 60 bytes, no data
# block) are i_block itself; slow ones are the link's data.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./super.bend as S
import ./inode.bend as N
import ./blockmap.bend as M
import ./extent.bend as X

# the number of blocks a file's size needs
def Ext2File.blocks_needed(+fs: S.Ext2Fs, +i: N.Ext2Inode) -> Nat:
  +bs = S.Ext2Fs.block_size(fs)
  Nat.div(Nat.add(N.Ext2Inode.size_nat(i), Nat.sub(bs, 1n)), bs)

def Ext2File.map.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, extents: Bool, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +l: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  match extents:
    case True{}:
      X.Ext2Extent.map(~Dv, ~block_size, ~read_block, d, fs, N.Ext2Inode.number_of(i), N.Ext2Inode.generation(i), N.Ext2Inode.block(i), l)
    case False{}:
      M.Ext2Map.map(~Dv, ~block_size, ~read_block, d, fs, N.Ext2Inode.number_of(i), N.Ext2Inode.block(i), l)

def Ext2File.map.inline(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, inline: Bool, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +l: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  match inline:
    case True{}:
      Fail{E.Ext2InlineData{N.Ext2Inode.number_of(i)}}
    case False{}:
      Ext2File.map.go(~Dv, ~block_size, ~read_block, N.Ext2Inode.has_flag(i, N.Ext2Inode.flag_extents()), d, fs, i, l)

def Ext2File.map.within(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, within: Bool, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +l: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  match within:
    case False{}:
      Fail{E.Ext2PastEnd{N.Ext2Inode.number_of(i), l}}
    case True{}:
      Ext2File.map.inline(~Dv, ~block_size, ~read_block, N.Ext2Inode.has_flag(i, N.Ext2Inode.flag_inline_data()), d, fs, i, l)

# the block holding logical block l of a file: Some{block}, or None for a
# hole; Ext2PastEnd for a block the file's size does not reach. Every block
# it answers is inside the filesystem.
def Ext2File.map(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +l: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  M.Ext2Map.final(fs, N.Ext2Inode.number_of(i), Ext2File.map.within(~Dv, ~block_size, ~read_block, Nat.is_lt(l, Ext2File.blocks_needed(fs, i)), d, fs, i, l))

def Ext2File.data(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, m: Maybe<&2, Nat>, +len: Nat) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  match m:
    case None{}:
      Done{B.Octets.zeros(len)}
    case Some{p}:
      do Result<&2, &2, E.Ext2Error, B.Octets>:
        o : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, p)
        return B.Octets.take(len, o)

# the bytes of logical block l of a file: a whole block, but only up to the
# file's size in its last block
def Ext2File.read_block(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +l: Nat) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  +bs = S.Ext2Fs.block_size(fs)
  do Result<&2, &2, E.Ext2Error, B.Octets>:
    m : Maybe<&2, Nat> <- Ext2File.map(~Dv, ~block_size, ~read_block, d, fs, i, l)
    Ext2File.data(~Dv, ~block_size, ~read_block, d, fs, m, Nat.min(bs, Nat.sub(N.Ext2Inode.size_nat(i), Nat.mul(l, bs))))

# Streaming: a reader is a file and the next block to read

type Ext2Reader is Data:
  Ext2Reader{inode: N.Ext2Inode, next: Nat}

type Ext2Chunk is Data:
  Ext2Piece{data: B.Octets, rest: Ext2Reader}
  Ext2Eof{}

# a reader at the start of a file
def Ext2File.start(i: N.Ext2Inode) -> Ext2Reader:
  Ext2Reader{i, 0n}

def Ext2Reader.position(r: Ext2Reader) -> Nat:
  match r:
    case Ext2Reader{i, k}:
      k

def Ext2File.next.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, more: Bool, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +k: Nat) -> Result<&2, &2, E.Ext2Error, Ext2Chunk>:
  match more:
    case True{}:
      do Result<&2, &2, E.Ext2Error, Ext2Chunk>:
        o : B.Octets <- Ext2File.read_block(~Dv, ~block_size, ~read_block, d, fs, i, k)
        return Ext2Piece{o, Ext2Reader{i, Nat.add(k, 1n)}}
    case False{}:
      Done{Ext2Eof{}}

# the next block of a file (its last one cut at the size), and the reader
# after it; Ext2Eof once the size is reached
def Ext2File.next(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, r: Ext2Reader) -> Result<&2, &2, E.Ext2Error, Ext2Chunk>:
  match r:
    case Ext2Reader{+i, +k}:
      Ext2File.next.go(~Dv, ~block_size, ~read_block, Nat.is_lt(k, Ext2File.blocks_needed(fs, i)), d, fs, i, k)

# Byte ranges

# the blocks of a range, a tail call each: r is the read of the block before
# logical block l (Done{empty} at the start), acc the blocks read before it,
# last first; count blocks are left. The first failure is the answer.
def Ext2File.range.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, count: Nat, r: Result<&2, &2, E.Ext2Error, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +l: Nat, acc: List<&2, B.Octets>) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  match count r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{o}:
      Done{B.Octets.concat(List.reverse(&2, B.Octets, Con{o, acc}))}
    case 1n+c Done{o}:
      Ext2File.range.go(~Dv, ~block_size, ~read_block, c, Ext2File.read_block(~Dv, ~block_size, ~read_block, d, fs, i, l), d, fs, i, Nat.add(l, 1n), Con{o, acc})

def Ext2File.range.some(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, empty: Bool, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +off: Nat, +end: Nat) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  match empty:
    case True{}:
      Done{B.Octets.empty()}
    case False{}:
      +bs = S.Ext2Fs.block_size(fs)
      +first = Nat.div(off, bs)
      do Result<&2, &2, E.Ext2Error, B.Octets>:
        o : B.Octets <- Ext2File.range.go(~Dv, ~block_size, ~read_block, Nat.sub(Nat.div(Nat.add(end, Nat.sub(bs, 1n)), bs), first), Done{B.Octets.empty()}, d, fs, i, first, Nil{})
        return B.Octets.slice(Nat.sub(off, Nat.mul(first, bs)), Nat.sub(end, off), o)

# the bytes of a file from byte off, len of them, or fewer where the file
# ends first; reads only the blocks the range covers
def Ext2File.read_range(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +off: Nat, len: Nat) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  +end = Nat.min(Nat.add(off, len), N.Ext2Inode.size_nat(i))
  Ext2File.range.some(~Dv, ~block_size, ~read_block, Nat.is_le(end, off), d, fs, i, off, end)

# the whole file, as one Octets (an Octets costs about 940 bytes of memory a
# byte today, so stream anything over a megabyte or so)
def Ext2File.read_all(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  Ext2File.read_range(~Dv, ~block_size, ~read_block, d, fs, i, 0n, N.Ext2Inode.size_nat(i))

# Symbolic links

# the blocks i_blocks counts for the extended-attribute block, if any
def Ext2File.acl_units.huge(huge: Bool, bs: Nat) -> Nat:
  match huge:
    case True{}:
      1n
    case False{}:
      Nat.div(bs, 512n)

def Ext2File.acl_units(has_acl: Bool, +fs: S.Ext2Fs, +i: N.Ext2Inode) -> Nat:
  match has_acl:
    case True{}:
      Ext2File.acl_units.huge(Bool.and(S.Ext2Super.has_ro_compat(S.Ext2Fs.sb(fs), S.Ext2Super.ro_compat_huge_file()), N.Ext2Inode.has_flag(i, N.Ext2Inode.flag_huge_file())), S.Ext2Fs.block_size(fs))
    case False{}:
      0n

# whether a symbolic link keeps its target in i_block: under 60 bytes, no
# extent tree, and no data block (i_blocks counts only an attribute block)
def Ext2File.is_fast_symlink(+fs: S.Ext2Fs, +i: N.Ext2Inode) -> Bool:
  +acl = Ext2File.acl_units(Bool.not(Nat.is_eq(W.W64.to_nat(N.Ext2Inode.file_acl(i)), 0n)), fs, i)
  Bool.and(Nat.is_lt(N.Ext2Inode.size_nat(i), 60n), Bool.and(Bool.not(N.Ext2Inode.has_flag(i, N.Ext2Inode.flag_extents())), Nat.is_le(W.W64.to_nat(N.Ext2Inode.blocks(i)), acl)))

def Ext2File.readlink.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, fast: Bool, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  match fast:
    case True{}:
      Done{B.Octets.take(N.Ext2Inode.size_nat(i), N.Ext2Inode.block(i))}
    case False{}:
      Ext2File.read_all(~Dv, ~block_size, ~read_block, d, fs, i)

# the target of a symbolic link (Ext2NotSymlink for any other inode)
def Ext2File.readlink(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  do Result<&2, &2, E.Ext2Error, B.Octets>:
    S.Ext2.require(N.Ext2Inode.is_symlink(i), E.Ext2NotSymlink{N.Ext2Inode.number_of(i)})
    Ext2File.readlink.go(~Dv, ~block_size, ~read_block, Ext2File.is_fast_symlink(fs, i), d, fs, i)
