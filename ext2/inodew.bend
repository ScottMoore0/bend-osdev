# bend-osdev-ext2: writing inodes. An inode is written as its whole record
# (inode_size bytes), read raw, changed field by field in place (so the
# fields this package does not use survive), and written back with its
# checksum recomputed (metadata_csum: the low 16 bits at byte 124, the high
# ones at byte 130 when the extra fields hold them).
#
# Field offsets: Poirier, "Inode Table"; the ext4 disk-layout documentation,
# "Index Nodes" (i_size_high at 108, i_blocks_high at 116, i_uid_high and
# i_gid_high at 120 and 122, i_extra_isize at 128, i_crtime at 144).
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./field.bend as F
import ./csum.bend as K
import ./super.bend as S
import ./group.bend as G
import ./inode.bend as N
import ./patch.bend as P
import ./meta.bend as T

# Where inode n's record is

type Ext2InodeAt is Data:
  Ext2InodeAt{block: Nat, offset: Nat}

def Ext2InodeW.at.table(+fs: S.Ext2Fs, +n: Nat, +index: Nat, desc: G.Ext2Group) -> Result<&2, &2, E.Ext2Error, Ext2InodeAt>:
  +bs = S.Ext2Fs.block_size(fs)
  +off = Nat.mul(index, S.Ext2Fs.inode_size(fs))
  +blk = Nat.add(G.Ext2Group.inode_table(desc), Nat.div(off, bs))
  do Result<&2, &2, E.Ext2Error, Ext2InodeAt>:
    S.Ext2.require(Nat.is_lt(blk, S.Ext2Fs.blocks(fs)), E.Ext2BadBlockRef{n, blk})
    return Ext2InodeAt{blk, Nat.mod(off, bs)}

# the block and byte offset of inode n's record
def Ext2InodeW.at(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +n: Nat) -> Result<&2, &2, E.Ext2Error, Ext2InodeAt>:
  +loc = N.Ext2Inode.locate(S.Ext2Fs.inodes_per_group(fs), n)
  do Result<&2, &2, E.Ext2Error, Ext2InodeAt>:
    S.Ext2.require(Bool.and(Nat.is_lt(0n, n), Nat.is_le(n, S.Ext2Fs.inodes_count(fs))), E.Ext2BadInodeNumber{n})
    desc : G.Ext2Group <- G.Ext2Group.read(~Dv, ~block_size, ~read_block, d, fs, N.Ext2InodeLoc.group(loc))
    Ext2InodeW.at.table(fs, n, N.Ext2InodeLoc.index(loc), desc)

def Ext2InodeW.read_at(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +n: Nat, at: Ext2InodeAt) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  match at:
    case Ext2InodeAt{blk, off}:
      +isz = S.Ext2Fs.inode_size(fs)
      do Result<&2, &2, E.Ext2Error, B.Octets>:
        o : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, blk)
        +raw : B.Octets = B.Octets.slice(off, isz, o)
        i : N.Ext2Inode <- N.Ext2Inode.verify(S.Ext2Fs.verify_meta(fs), fs, n, isz, raw, N.Ext2Inode.parse(n, isz, raw))
        return raw

# inode n's record, its checksum verified as the reader verifies it
def Ext2InodeW.read_raw(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +n: Nat) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  do Result<&2, &2, E.Ext2Error, B.Octets>:
    at : Ext2InodeAt <- Ext2InodeW.at(~Dv, ~block_size, ~read_block, d, fs, n)
    Ext2InodeW.read_at(~Dv, ~block_size, ~read_block, d, fs, n, at)

# Fields of a raw record

def Ext2IRaw.mode(+raw: B.Octets) -> U32:
  F.Ext2Field.u16(raw, 0n)

def Ext2IRaw.links(+raw: B.Octets) -> U32:
  F.Ext2Field.u16(raw, 26n)

def Ext2IRaw.flags(+raw: B.Octets) -> U32:
  F.Ext2Field.u32(raw, 32n)

def Ext2IRaw.generation(+raw: B.Octets) -> U32:
  F.Ext2Field.u32(raw, 100n)

def Ext2IRaw.size(+raw: B.Octets) -> Nat:
  F.Ext2Field.join(F.Ext2Field.u32(raw, 108n), F.Ext2Field.u32(raw, 4n))

# i_blocks, in its own units (512 bytes, or blocks with HUGE_FILE)
def Ext2IRaw.blocks(+raw: B.Octets) -> Nat:
  F.Ext2Field.join(F.Ext2Field.u16(raw, 116n), F.Ext2Field.u32(raw, 28n))

def Ext2IRaw.file_acl(+raw: B.Octets) -> Nat:
  F.Ext2Field.join(F.Ext2Field.u16(raw, 118n), F.Ext2Field.u32(raw, 104n))

def Ext2IRaw.iblock(+raw: B.Octets) -> B.Octets:
  B.Octets.slice(40n, 60n, raw)

def Ext2IRaw.set_mode(+raw: B.Octets, v: U32) -> B.Octets:
  P.Ext2Patch.u16(raw, 0n, v)

def Ext2IRaw.set_links(+raw: B.Octets, v: U32) -> B.Octets:
  P.Ext2Patch.u16(raw, 26n, v)

def Ext2IRaw.set_flags(+raw: B.Octets, v: U32) -> B.Octets:
  P.Ext2Patch.u32(raw, 32n, v)

def Ext2IRaw.set_size(+raw: B.Octets, +n: Nat) -> B.Octets:
  P.Ext2Patch.split(raw, 4n, 108n, 4n, n)

def Ext2IRaw.set_blocks(+raw: B.Octets, +n: Nat) -> B.Octets:
  P.Ext2Patch.split(raw, 28n, 116n, 2n, n)

def Ext2IRaw.set_iblock(+raw: B.Octets, +ib: B.Octets) -> B.Octets:
  P.Ext2Patch.bytes(raw, 40n, B.Octets.take(60n, ib))

def Ext2IRaw.set_dtime(+raw: B.Octets, v: U32) -> B.Octets:
  P.Ext2Patch.u32(raw, 20n, v)

# ctime and mtime (a change to the inode's data or its entries)
def Ext2IRaw.touch(+raw: B.Octets, +t: U32) -> B.Octets:
  P.Ext2Patch.u32(P.Ext2Patch.u32(raw, 12n, t), 16n, t)

def Ext2IRaw.set_ctime(+raw: B.Octets, +t: U32) -> B.Octets:
  P.Ext2Patch.u32(raw, 12n, t)

def Ext2IRaw.units.pick(huge: Bool, +bs: Nat) -> Nat:
  match huge:
    case True{}:
      1n
    case False{}:
      Nat.div(bs, 512n)

# the i_blocks units of one filesystem block for this inode
def Ext2IRaw.units(+fs: S.Ext2Fs, +raw: B.Octets) -> Nat:
  +huge = Bool.and(S.Ext2Super.has_ro_compat(S.Ext2Fs.sb(fs), S.Ext2Super.ro_compat_huge_file()), F.Ext2Field.has(Ext2IRaw.flags(raw), N.Ext2Inode.flag_huge_file()))
  Ext2IRaw.units.pick(huge, S.Ext2Fs.block_size(fs))

# i_blocks moved by plus and minus filesystem blocks
def Ext2IRaw.add_blocks(+fs: S.Ext2Fs, +raw: B.Octets, +plus: Nat, +minus: Nat) -> B.Octets:
  +u = Ext2IRaw.units(fs, raw)
  Ext2IRaw.set_blocks(raw, Nat.sub(Nat.add(Ext2IRaw.blocks(raw), Nat.mul(plus, u)), Nat.mul(minus, u)))

def Ext2IRaw.has_flag(+raw: B.Octets, bit: U32) -> Bool:
  F.Ext2Field.has(Ext2IRaw.flags(raw), bit)

def Ext2IRaw.inode(+fs: S.Ext2Fs, +n: Nat, +raw: B.Octets) -> N.Ext2Inode:
  N.Ext2Inode.parse(n, S.Ext2Fs.inode_size(fs), raw)

# Checksums and writing

def Ext2InodeW.csum.hi(fits: Bool, +raw: B.Octets, +c: U32) -> B.Octets:
  match fits:
    case True{}:
      P.Ext2Patch.u16(raw, 130n, U32.shrn(c, 16n))
    case False{}:
      raw

def Ext2InodeW.csum.go(on: Bool, +fs: S.Ext2Fs, +n: Nat, +raw: B.Octets) -> B.Octets:
  match on:
    case True{}:
      +isz = S.Ext2Fs.inode_size(fs)
      +fits = N.Ext2Inode.hi_fits(isz, N.Ext2Inode.extra(Nat.is_lt(128n, isz), raw))
      +iseed = K.Ext2Csum.inode_seed(S.Ext2Fs.seed(fs), U32.from_nat(n), Ext2IRaw.generation(raw))
      +c = K.Ext2Csum.inode(iseed, raw, isz, fits)
      Ext2InodeW.csum.hi(fits, P.Ext2Patch.u16(raw, 124n, U32.and(65535, c)), c)
    case False{}:
      raw

# inode n's record with its checksum recomputed (metadata_csum)
def Ext2InodeW.csum(+fs: S.Ext2Fs, +n: Nat, +raw: B.Octets) -> B.Octets:
  Ext2InodeW.csum.go(T.Ext2Meta.has_meta(fs), fs, n, raw)

def Ext2InodeW.write_at(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +n: Nat, +raw: B.Octets, at: Ext2InodeAt) -> Result<&2, &2, E.Ext2Error, Dv>:
  match at:
    case Ext2InodeAt{+blk, +off}:
      do Result<&2, &2, E.Ext2Error, Dv>:
        o : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, blk)
        T.Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d, fs, blk, P.Ext2Patch.bytes(o, off, Ext2InodeW.csum(fs, n, B.Octets.take(S.Ext2Fs.inode_size(fs), raw))))

# inode n's record replaced by raw, its checksum recomputed
def Ext2InodeW.write_raw(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +n: Nat, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    at : Ext2InodeAt <- Ext2InodeW.at(~Dv, ~block_size, ~read_block, d, fs, n)
    Ext2InodeW.write_at(~Dv, ~block_size, ~read_block, ~write_block, d, fs, n, raw, at)

# New records

# the extra fields' size a new inode gets: s_min_extra_isize, at least 32
# (what mke2fs gives), when the record has room past 128 bytes
def Ext2InodeW.extra_size(+fs: S.Ext2Fs) -> Nat:
  +isz = S.Ext2Fs.inode_size(fs)
  Nat.min(Nat.sub(isz, 128n), Nat.max(32n, U32.to_nat(S.Ext2Super.min_extra_isize(S.Ext2Fs.sb(fs)))))

def Ext2InodeW.crtime.pick(fits: Bool, +raw: B.Octets, t: U32) -> B.Octets:
  match fits:
    case True{}:
      P.Ext2Patch.u32(raw, 144n, t)
    case False{}:
      raw

def Ext2InodeW.extra.pick(big: Bool, +raw: B.Octets, +extra: Nat, +t: U32) -> B.Octets:
  match big:
    case True{}:
      Ext2InodeW.crtime.pick(Nat.is_le(20n, extra), P.Ext2Patch.u16(raw, 128n, U32.from_nat(extra)), t)
    case False{}:
      raw

# a new inode's record: mode (type and permissions), owner, time (access,
# change, modification and creation), links, flags and i_block
def Ext2InodeW.fresh(+fs: S.Ext2Fs, mode: U32, +uid: U32, +gid: U32, +t: U32, links: U32, flags: U32, +iblock: B.Octets) -> B.Octets:
  +isz = S.Ext2Fs.inode_size(fs)
  +r0 = P.Ext2Patch.u16(P.Ext2Patch.u16(P.Ext2Patch.u16(B.Octets.zeros(isz), 0n, mode), 2n, U32.and(65535, uid)), 24n, U32.and(65535, gid))
  +r1 = P.Ext2Patch.u32(P.Ext2Patch.u32(P.Ext2Patch.u32(r0, 8n, t), 12n, t), 16n, t)
  +r2 = Ext2IRaw.set_iblock(Ext2IRaw.set_flags(Ext2IRaw.set_links(r1, links), flags), iblock)
  +r3 = P.Ext2Patch.u16(P.Ext2Patch.u16(r2, 120n, U32.shrn(uid, 16n)), 122n, U32.shrn(gid, 16n))
  Ext2InodeW.extra.pick(Nat.is_lt(128n, isz), r3, Ext2InodeW.extra_size(fs), t)
