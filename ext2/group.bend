# bend-osdev-ext2: block group descriptors (Poirier, "Block Group Descriptor
# Table"; the ext4 disk-layout documentation, "Block Group Descriptors": 32
# bytes, or s_desc_size bytes (at least 64) with the 64bit feature, whose
# second half holds the high halves of the block numbers and counts).
#
# The descriptor table follows the superblock: it starts at block
# s_first_data_block + 1. With meta_bg, the descriptors of meta group m
# (s_desc_per_block groups, from group m * per_block) are instead in the
# first block of group m * per_block after its superblock backup, for every
# m from s_first_meta_bg on.
import Base
import ../bytes/bytes.bend as B
import ../uuid/uuid.bend as U
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./field.bend as F
import ./csum.bend as K
import ./super.bend as S

type Ext2Group is Data:
  Ext2Group{block_bitmap: Nat, inode_bitmap: Nat, inode_table: Nat, free_blocks: U32, free_inodes: U32, used_dirs: U32, flags: U32, itable_unused: U32, checksum: U32}

def Ext2Group.inode_table(g: Ext2Group) -> Nat:
  match g:
    case Ext2Group{bb, ib, it, fb, fi, ud, fl, iu, ck}:
      it

def Ext2Group.checksum(g: Ext2Group) -> U32:
  match g:
    case Ext2Group{bb, ib, it, fb, fi, ud, fl, iu, ck}:
      ck

def Ext2Group.wide(wide: Bool, +o: B.Octets, i: Nat) -> U32:
  match wide:
    case True{}:
      F.Ext2Field.u32(o, i)
    case False{}:
      0

def Ext2Group.wide16(wide: Bool, +o: B.Octets, i: Nat) -> U32:
  match wide:
    case True{}:
      F.Ext2Field.u16(o, i)
    case False{}:
      0

# a descriptor's fields; wide: a 64-byte descriptor (the 64bit feature)
def Ext2Group.parse(+wide: Bool, +o: B.Octets) -> Ext2Group:
  Ext2Group{F.Ext2Field.join(Ext2Group.wide(wide, o, 32n), F.Ext2Field.u32(o, 0n)), F.Ext2Field.join(Ext2Group.wide(wide, o, 36n), F.Ext2Field.u32(o, 4n)), F.Ext2Field.join(Ext2Group.wide(wide, o, 40n), F.Ext2Field.u32(o, 8n)), U32.or(F.Ext2Field.u16(o, 12n), U32.shln(Ext2Group.wide16(wide, o, 44n), 16n)), U32.or(F.Ext2Field.u16(o, 14n), U32.shln(Ext2Group.wide16(wide, o, 46n), 16n)), U32.or(F.Ext2Field.u16(o, 16n), U32.shln(Ext2Group.wide16(wide, o, 48n), 16n)), F.Ext2Field.u16(o, 18n), U32.or(F.Ext2Field.u16(o, 28n), U32.shln(Ext2Group.wide16(wide, o, 50n), 16n)), F.Ext2Field.u16(o, 30n)}

# Where a group starts, and whether it holds a superblock backup

# whether g is a power of b (b, b^2, ...): p is the power reached, eq and lt
# compare it with g; the next power is computed only while p < g
def Ext2Group.is_power(n: Nat, eq: Bool, lt: Bool, +g: Nat, +b: Nat, +p: Nat) -> Bool:
  match n eq lt:
    case 0n _ _:
      False{}
    case 1n+k True{} _:
      True{}
    case 1n+k False{} True{}:
      +q = Nat.mul(p, b)
      Ext2Group.is_power(k, Nat.is_eq(g, q), Nat.is_lt(q, g), g, b, q)
    case 1n+k False{} False{}:
      False{}

def Ext2Group.is_power_of(+g: Nat, +b: Nat) -> Bool:
  Ext2Group.is_power(48n, Nat.is_eq(g, b), Nat.is_lt(b, g), g, b, b)

def Ext2Group.sparse(+g: Nat) -> Bool:
  Bool.or(Nat.is_le(g, 1n), Bool.or(Ext2Group.is_power_of(g, 3n), Bool.or(Ext2Group.is_power_of(g, 5n), Ext2Group.is_power_of(g, 7n))))

def Ext2Group.sparse2(+g: Nat, bgs: U32 & U32) -> Bool:
  (+b0, +b1) = bgs
  Bool.or(Nat.is_eq(g, 0n), Bool.or(Bool.and(Nat.is_lt(0n, U32.to_nat(b0)), Nat.is_eq(g, U32.to_nat(b0))), Bool.and(Nat.is_lt(0n, U32.to_nat(b1)), Nat.is_eq(g, U32.to_nat(b1)))))

def Ext2Group.has_super.pick(two: Bool, sparse: Bool, +g: Nat, +sb: S.Ext2Super) -> Bool:
  match two sparse:
    case True{} _:
      Ext2Group.sparse2(g, S.Ext2Super.backup_bgs(sb))
    case False{} True{}:
      Ext2Group.sparse(g)
    case False{} False{}:
      True{}

# whether group g holds a backup of the superblock (and of the descriptors):
# every group, or with sparse_super groups 0, 1 and the powers of 3, 5 and
# 7, or with sparse_super2 group 0 and the two in s_backup_bgs
def Ext2Group.has_super(+fs: S.Ext2Fs, +g: Nat) -> Bool:
  +sb = S.Ext2Fs.sb(fs)
  Ext2Group.has_super.pick(S.Ext2Super.has_compat(sb, S.Ext2Super.compat_sparse_super2()), S.Ext2Super.has_ro_compat(sb, S.Ext2Super.ro_compat_sparse_super()), g, sb)

# the first block of group g
def Ext2Group.first_block(+fs: S.Ext2Fs, g: Nat) -> Nat:
  +sb = S.Ext2Fs.sb(fs)
  Nat.add(U32.to_nat(S.Ext2Super.first_data_block(sb)), Nat.mul(g, U32.to_nat(S.Ext2Super.blocks_per_group(sb))))

# Where descriptor g is: its block, and its byte offset in that block

type Ext2DescLoc is Data:
  Ext2DescLoc{block: Nat, offset: Nat}

def Ext2Group.desc_loc.pick(meta: Bool, +fs: S.Ext2Fs, +g: Nat, +per: Nat) -> Ext2DescLoc:
  match meta:
    case True{}:
      +off = Nat.mul(Nat.mod(g, per), S.Ext2Fs.desc_size(fs))
      +first = Nat.mul(Nat.div(g, per), per)
      Ext2DescLoc{Nat.add(Ext2Group.first_block(fs, first), U32.to_nat(Bool.to_u32(Ext2Group.has_super(fs, first)))), off}
    case False{}:
      +off = Nat.mul(Nat.mod(g, per), S.Ext2Fs.desc_size(fs))
      Ext2DescLoc{Nat.add(Nat.add(U32.to_nat(S.Ext2Super.first_data_block(S.Ext2Fs.sb(fs))), 1n), Nat.div(g, per)), off}

def Ext2Group.desc_loc(+fs: S.Ext2Fs, +g: Nat) -> Ext2DescLoc:
  +per = Nat.div(S.Ext2Fs.block_size(fs), S.Ext2Fs.desc_size(fs))
  +sb = S.Ext2Fs.sb(fs)
  Ext2Group.desc_loc.pick(Bool.and(S.Ext2Super.has_incompat(sb, S.Ext2Super.incompat_meta_bg()), Nat.is_le(U32.to_nat(S.Ext2Super.first_meta_bg(sb)), Nat.div(g, per))), fs, g, per)

# Checksums

def Ext2Group.verify.cmp(ok: Bool, g: Nat, stored: U32, c: U32, desc: Ext2Group) -> Result<&2, &2, E.Ext2Error, Ext2Group>:
  match ok:
    case True{}:
      Done{desc}
    case False{}:
      Fail{E.Ext2BadGroupCsum{g, stored, c}}

def Ext2Group.verify.go(k: S.Ext2CsumKind, +fs: S.Ext2Fs, +g: Nat, +raw: B.Octets, +desc: Ext2Group) -> Result<&2, &2, E.Ext2Error, Ext2Group>:
  match k:
    case S.Ext2CsumMeta{}:
      +stored = Ext2Group.checksum(desc)
      +c = K.Ext2Csum.group(S.Ext2Fs.seed(fs), U32.from_nat(g), raw, S.Ext2Fs.desc_size(fs))
      Ext2Group.verify.cmp(U32.is_eq(c, stored), g, stored, c, desc)
    case S.Ext2CsumGdt{}:
      +stored = Ext2Group.checksum(desc)
      +c = K.Ext2Csum.group16(U.Uuid.to_bytes(S.Ext2Super.uuid(S.Ext2Fs.sb(fs))), U32.from_nat(g), raw, S.Ext2Fs.desc_size(fs))
      Ext2Group.verify.cmp(U32.is_eq(c, stored), g, stored, c, desc)
    case S.Ext2CsumNone{}:
      Done{desc}

# the bytes of descriptor g, from the block that holds it
def Ext2Group.decode(+fs: S.Ext2Fs, +g: Nat, +blk: B.Octets, off: Nat) -> Result<&2, &2, E.Ext2Error, Ext2Group>:
  +raw = B.Octets.slice(off, S.Ext2Fs.desc_size(fs), blk)
  Ext2Group.verify.go(S.Ext2Fs.csum(fs), fs, g, raw, Ext2Group.parse(S.Ext2Fs.has_incompat(fs, S.Ext2Super.incompat_64bit()), raw))

def Ext2Group.read.at(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +g: Nat, loc: Ext2DescLoc) -> Result<&2, &2, E.Ext2Error, Ext2Group>:
  match loc:
    case Ext2DescLoc{blk, off}:
      do Result<&2, &2, E.Ext2Error, Ext2Group>:
        o : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, blk)
        Ext2Group.decode(fs, g, o, off)

# descriptor g, checked (its checksum, when the image has one and the options
# ask for it)
def Ext2Group.read(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +g: Nat) -> Result<&2, &2, E.Ext2Error, Ext2Group>:
  do Result<&2, &2, E.Ext2Error, Ext2Group>:
    S.Ext2.require(Nat.is_lt(g, S.Ext2Fs.groups(fs)), E.Ext2BadGroup{g})
    Ext2Group.read.at(~Dv, ~block_size, ~read_block, d, fs, g, Ext2Group.desc_loc(fs, g))
