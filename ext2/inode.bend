# bend-osdev-ext2: inodes (Poirier, "Inode Table"; the ext4 disk-layout
# documentation, "Index Nodes": the 64-bit size, the high halves of the
# owner and block count in osd2, the extra fields after the first 128 bytes
# and the checksum split between bytes 124 and 130).
#
# Inode n (from 1) is entry (n - 1) mod s_inodes_per_group of the inode
# table of group (n - 1) div s_inodes_per_group.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./field.bend as F
import ./csum.bend as K
import ./super.bend as S
import ./group.bend as G

# Inode numbers and where they live

type Ext2InodeLoc is Data:
  Ext2InodeLoc{group: Nat, index: Nat}

def Ext2InodeLoc.group(l: Ext2InodeLoc) -> Nat:
  match l:
    case Ext2InodeLoc{g, i}:
      g

def Ext2InodeLoc.index(l: Ext2InodeLoc) -> Nat:
  match l:
    case Ext2InodeLoc{g, i}:
      i

# the group and index of inode n, with ipg inodes per group (there is no
# inode 0: it answers group 0, index 0, and readers refuse it first)
def Ext2Inode.locate(+ipg: Nat, n: Nat) -> Ext2InodeLoc:
  match n:
    case 0n:
      Ext2InodeLoc{0n, 0n}
    case 1n+k:
      +j = k
      Ext2InodeLoc{Nat.div(j, ipg), Nat.mod(j, ipg)}

# the inode number at a group and index
def Ext2Inode.number(+ipg: Nat, l: Ext2InodeLoc) -> Nat:
  match l:
    case Ext2InodeLoc{g, i}:
      1n+Nat.add(Nat.mul(g, ipg), i)

# The inode record

type Ext2Inode is Data:
  Ext2Inode{number: Nat, mode: U32, uid: U32, gid: U32, size: W.W64, atime: U32, ctime: U32, mtime: U32, dtime: U32, links: U32, blocks: W.W64, flags: U32, generation: U32, file_acl: W.W64, block: B.Octets, extra_isize: U32, checksum: U32}

def Ext2Inode.number_of(i: Ext2Inode) -> Nat:
  match i:
    case Ext2Inode{n, md, u, g, sz, at, ct, mt, dt, ln, bl, fl, gen, acl, blk, ex, ck}:
      n

def Ext2Inode.mode(i: Ext2Inode) -> U32:
  match i:
    case Ext2Inode{n, md, u, g, sz, at, ct, mt, dt, ln, bl, fl, gen, acl, blk, ex, ck}:
      md

def Ext2Inode.uid(i: Ext2Inode) -> U32:
  match i:
    case Ext2Inode{n, md, u, g, sz, at, ct, mt, dt, ln, bl, fl, gen, acl, blk, ex, ck}:
      u

def Ext2Inode.gid(i: Ext2Inode) -> U32:
  match i:
    case Ext2Inode{n, md, u, g, sz, at, ct, mt, dt, ln, bl, fl, gen, acl, blk, ex, ck}:
      g

def Ext2Inode.size(i: Ext2Inode) -> W.W64:
  match i:
    case Ext2Inode{n, md, u, g, sz, at, ct, mt, dt, ln, bl, fl, gen, acl, blk, ex, ck}:
      sz

def Ext2Inode.mtime(i: Ext2Inode) -> U32:
  match i:
    case Ext2Inode{n, md, u, g, sz, at, ct, mt, dt, ln, bl, fl, gen, acl, blk, ex, ck}:
      mt

def Ext2Inode.links(i: Ext2Inode) -> U32:
  match i:
    case Ext2Inode{n, md, u, g, sz, at, ct, mt, dt, ln, bl, fl, gen, acl, blk, ex, ck}:
      ln

def Ext2Inode.blocks(i: Ext2Inode) -> W.W64:
  match i:
    case Ext2Inode{n, md, u, g, sz, at, ct, mt, dt, ln, bl, fl, gen, acl, blk, ex, ck}:
      bl

def Ext2Inode.flags(i: Ext2Inode) -> U32:
  match i:
    case Ext2Inode{n, md, u, g, sz, at, ct, mt, dt, ln, bl, fl, gen, acl, blk, ex, ck}:
      fl

def Ext2Inode.generation(i: Ext2Inode) -> U32:
  match i:
    case Ext2Inode{n, md, u, g, sz, at, ct, mt, dt, ln, bl, fl, gen, acl, blk, ex, ck}:
      gen

def Ext2Inode.file_acl(i: Ext2Inode) -> W.W64:
  match i:
    case Ext2Inode{n, md, u, g, sz, at, ct, mt, dt, ln, bl, fl, gen, acl, blk, ex, ck}:
      acl

# i_block: the 60 bytes of block pointers, extent tree root, or fast
# symbolic link target
def Ext2Inode.block(i: Ext2Inode) -> B.Octets:
  match i:
    case Ext2Inode{n, md, u, g, sz, at, ct, mt, dt, ln, bl, fl, gen, acl, blk, ex, ck}:
      blk

def Ext2Inode.checksum(i: Ext2Inode) -> U32:
  match i:
    case Ext2Inode{n, md, u, g, sz, at, ct, mt, dt, ln, bl, fl, gen, acl, blk, ex, ck}:
      ck

# the size as a Nat (48 bits at most: see Ext2Field.join)
def Ext2Inode.size_nat(+i: Ext2Inode) -> Nat:
  +s = Ext2Inode.size(i)
  F.Ext2Field.join(W.W64.hi(s), W.W64.lo(s))

# i_flags bits
def Ext2Inode.flag_index() -> U32:
  4096

def Ext2Inode.flag_huge_file() -> U32:
  262144

def Ext2Inode.flag_extents() -> U32:
  524288

def Ext2Inode.flag_inline_data() -> U32:
  268435456

def Ext2Inode.has_flag(+i: Ext2Inode, bit: U32) -> Bool:
  F.Ext2Field.has(Ext2Inode.flags(i), bit)

# The file type, from the top four bits of i_mode

type Ext2Kind is Data:
  Ext2Fifo{}
  Ext2CharDev{}
  Ext2Directory{}
  Ext2BlockDev{}
  Ext2Regular{}
  Ext2Symlink{}
  Ext2Socket{}
  Ext2Unknown{mode: U32}

def Ext2Kind.of_nat(n: Nat, +mode: U32) -> Ext2Kind:
  match n:
    case 1n:
      Ext2Fifo{}
    case 2n:
      Ext2CharDev{}
    case 4n:
      Ext2Directory{}
    case 6n:
      Ext2BlockDev{}
    case 8n:
      Ext2Regular{}
    case 10n:
      Ext2Symlink{}
    case 12n:
      Ext2Socket{}
    case _:
      Ext2Unknown{mode}

def Ext2Kind.of_mode(+mode: U32) -> Ext2Kind:
  Ext2Kind.of_nat(U32.to_nat(U32.shrn(U32.and(mode, 61440), 12n)), mode)

def Ext2Kind.show(k: Ext2Kind) -> String:
  match k:
    case Ext2Fifo{}:
      "fifo"
    case Ext2CharDev{}:
      "chardev"
    case Ext2Directory{}:
      "dir"
    case Ext2BlockDev{}:
      "blockdev"
    case Ext2Regular{}:
      "file"
    case Ext2Symlink{}:
      "symlink"
    case Ext2Socket{}:
      "socket"
    case Ext2Unknown{m}:
      "unknown"

def Ext2Inode.kind(+i: Ext2Inode) -> Ext2Kind:
  Ext2Kind.of_mode(Ext2Inode.mode(i))

def Ext2Kind.is_dir(k: Ext2Kind) -> Bool:
  match k:
    case Ext2Directory{}:
      True{}
    case _:
      False{}

def Ext2Kind.is_symlink(k: Ext2Kind) -> Bool:
  match k:
    case Ext2Symlink{}:
      True{}
    case _:
      False{}

def Ext2Inode.is_dir(+i: Ext2Inode) -> Bool:
  Ext2Kind.is_dir(Ext2Inode.kind(i))

def Ext2Inode.is_symlink(+i: Ext2Inode) -> Bool:
  Ext2Kind.is_symlink(Ext2Inode.kind(i))

# Parsing an inode record of isz bytes

def Ext2Inode.extra(big: Bool, +raw: B.Octets) -> U32:
  match big:
    case True{}:
      F.Ext2Field.u16(raw, 128n)
    case False{}:
      0

# whether the extra fields hold i_checksum_hi (bytes 130 and 131)
def Ext2Inode.hi_fits(+isz: Nat, +extra: U32) -> Bool:
  Bool.and(Nat.is_lt(128n, isz), U32.is_le(4, extra))

def Ext2Inode.csum_hi(fits: Bool, +raw: B.Octets) -> U32:
  match fits:
    case True{}:
      U32.shln(F.Ext2Field.u16(raw, 130n), 16n)
    case False{}:
      0

def Ext2Inode.parse(n: Nat, +isz: Nat, +raw: B.Octets) -> Ext2Inode:
  +ex = Ext2Inode.extra(Nat.is_lt(128n, isz), raw)
  Ext2Inode{n, F.Ext2Field.u16(raw, 0n), U32.or(F.Ext2Field.u16(raw, 2n), U32.shln(F.Ext2Field.u16(raw, 120n), 16n)), U32.or(F.Ext2Field.u16(raw, 24n), U32.shln(F.Ext2Field.u16(raw, 122n), 16n)), W.W64.from_parts(F.Ext2Field.u32(raw, 108n), F.Ext2Field.u32(raw, 4n)), F.Ext2Field.u32(raw, 8n), F.Ext2Field.u32(raw, 12n), F.Ext2Field.u32(raw, 16n), F.Ext2Field.u32(raw, 20n), F.Ext2Field.u16(raw, 26n), W.W64.from_parts(F.Ext2Field.u16(raw, 116n), F.Ext2Field.u32(raw, 28n)), F.Ext2Field.u32(raw, 32n), F.Ext2Field.u32(raw, 100n), W.W64.from_parts(F.Ext2Field.u16(raw, 118n), F.Ext2Field.u32(raw, 104n)), B.Octets.slice(40n, 60n, raw), ex, U32.or(F.Ext2Field.u16(raw, 124n), Ext2Inode.csum_hi(Ext2Inode.hi_fits(isz, ex), raw))}

# Checksums (metadata_csum)

def Ext2Inode.csum_cmp(ok: Bool, +n: Nat, stored: U32, c: U32, i: Ext2Inode) -> Result<&2, &2, E.Ext2Error, Ext2Inode>:
  match ok:
    case True{}:
      Done{i}
    case False{}:
      Fail{E.Ext2BadInodeCsum{n, stored, c}}

def Ext2Inode.csum_width(fits: Bool, c: U32) -> U32:
  match fits:
    case True{}:
      c
    case False{}:
      K.Ext2Csum.low16(c)

def Ext2Inode.verify(on: Bool, +fs: S.Ext2Fs, +n: Nat, +isz: Nat, +raw: B.Octets, +i: Ext2Inode) -> Result<&2, &2, E.Ext2Error, Ext2Inode>:
  match on:
    case True{}:
      +fits = Ext2Inode.hi_fits(isz, Ext2Inode.extra(Nat.is_lt(128n, isz), raw))
      +iseed = K.Ext2Csum.inode_seed(S.Ext2Fs.seed(fs), U32.from_nat(n), Ext2Inode.generation(i))
      +c = Ext2Inode.csum_width(fits, K.Ext2Csum.inode(iseed, raw, isz, fits))
      Ext2Inode.csum_cmp(U32.is_eq(c, Ext2Inode.checksum(i)), n, Ext2Inode.checksum(i), c, i)
    case False{}:
      Done{i}

# Reading inode n

def Ext2Inode.read.table(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +n: Nat, +index: Nat, +table: Nat) -> Result<&2, &2, E.Ext2Error, Ext2Inode>:
  +isz = S.Ext2Fs.inode_size(fs)
  +bs = S.Ext2Fs.block_size(fs)
  +off = Nat.mul(index, isz)
  do Result<&2, &2, E.Ext2Error, Ext2Inode>:
    S.Ext2.require(Nat.is_lt(table, S.Ext2Fs.blocks(fs)), E.Ext2BadBlockRef{n, table})
    +blk : Nat = Nat.add(table, Nat.div(off, bs))
    S.Ext2.require(Nat.is_lt(blk, S.Ext2Fs.blocks(fs)), E.Ext2BadBlockRef{n, blk})
    o : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, blk)
    +raw : B.Octets = B.Octets.slice(Nat.mod(off, bs), isz, o)
    Ext2Inode.verify(S.Ext2Fs.verify_meta(fs), fs, n, isz, raw, Ext2Inode.parse(n, isz, raw))

# inode n, checked: 1 <= n <= s_inodes_count, and its checksum (when the
# image has metadata_csum and the options ask for it). Reads the group's
# descriptor and the one block of the inode table that holds the inode.
def Ext2Inode.read(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +n: Nat) -> Result<&2, &2, E.Ext2Error, Ext2Inode>:
  +loc = Ext2Inode.locate(S.Ext2Fs.inodes_per_group(fs), n)
  do Result<&2, &2, E.Ext2Error, Ext2Inode>:
    S.Ext2.require(Bool.and(Nat.is_lt(0n, n), Nat.is_le(n, S.Ext2Fs.inodes_count(fs))), E.Ext2BadInodeNumber{n})
    g : G.Ext2Group <- G.Ext2Group.read(~Dv, ~block_size, ~read_block, d, fs, Ext2InodeLoc.group(loc))
    Ext2Inode.read.table(~Dv, ~block_size, ~read_block, d, fs, n, Ext2InodeLoc.index(loc), G.Ext2Group.inode_table(g))
