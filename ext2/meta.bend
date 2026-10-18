# bend-osdev-ext2: writing the filesystem's metadata through a device: bytes
# and blocks, the superblock (its free counts and checksum), the group
# descriptors (their counts, flags and checksums) and the bitmaps (read,
# rebuilt when a group's bitmap was never initialised, and written with their
# checksums).
#
# The writer takes blockdev's pure interface and a pure write
# (write_block: Dv -> Nat -> Octets -> Result<DevError, Dv>, what
# MemDev.write_block is), as template arguments: the reader's functions and
# laws apply unchanged to every device a write hands back, and a write that
# fails leaves the caller's device as it was.
#
# Layout: the ext4 disk-layout documentation, "The Super Block" (s_free_*,
# s_checksum), "Block Group Descriptors" (bg_free_*, bg_flags:
# INODE_UNINIT 1, BLOCK_UNINIT 2, ITABLE_ZEROED 4, bg_itable_unused, the
# bitmap checksums) and "Checksums" (a bitmap's is crc32c over its
# clusters_per_group / 8 or inodes_per_group / 8 bytes from the
# filesystem's seed; a descriptor's as group.bend reads it).
import Base
import ../bytes/bytes.bend as B
import ../uuid/uuid.bend as U
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./field.bend as F
import ./csum.bend as K
import ./super.bend as S
import ./group.bend as G
import ./patch.bend as P
import ./bitmap.bend as M

# A device and a value: what a write that also answers something hands back
type Ext2Out<-Dv: Data, -A: Data> is Data:
  Ext2Out{dev: Dv, value: A}

def Ext2Out.dev(-Dv: Data, -A: Data, o: Ext2Out<Dv, A>) -> Dv:
  match o:
    case Ext2Out{d, x}:
      d

def Ext2Out.value(-Dv: Data, -A: Data, o: Ext2Out<Dv, A>) -> A:
  match o:
    case Ext2Out{d, x}:
      x

# Device writes

def Ext2Dev.lift(-Dv: Data, r: Result<&2, &2, D.DevError, Dv>) -> Result<&2, &2, E.Ext2Error, Dv>:
  match r:
    case Done{d}:
      Done{d}
    case Fail{e}:
      Fail{E.Ext2Dev{e}}

# device block k replaced by piece at byte skip: written whole when the piece
# covers the block, else read, patched and written
def Ext2Dev.write_part(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, whole: Bool, +d: Dv, +k: Nat, +skip: Nat, +piece: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  match whole:
    case True{}:
      Ext2Dev.lift(Dv, write_block(d, k, piece))
    case False{}:
      do Result<&2, &2, E.Ext2Error, Dv>:
        blk : B.Octets <- S.Ext2.dev(read_block(d, k))
        Ext2Dev.lift(Dv, write_block(d, k, P.Ext2Patch.bytes(blk, skip, piece)))

# count device blocks from block k, of dbs bytes, written from data (whose
# first byte goes to byte offset off); r is the device so far
def Ext2Dev.write.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, count: Nat, r: Result<&2, &2, E.Ext2Error, Dv>, +dbs: Nat, +k: Nat, +off: Nat, +data: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  match count r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{d}:
      Done{d}
    case 1n+c Done{+d}:
      +skip = Nat.sub(off, Nat.mul(k, dbs))
      +n = Nat.min(Nat.sub(dbs, skip), B.Octets.len(data))
      +r2 = Ext2Dev.write_part(~Dv, ~block_size, ~read_block, ~write_block, Bool.and(Nat.is_eq(skip, 0n), Nat.is_eq(n, dbs)), d, k, skip, B.Octets.take(n, data))
      Ext2Dev.write.go(~Dv, ~block_size, ~read_block, ~write_block, c, r2, dbs, Nat.add(k, 1n), Nat.add(off, n), B.Octets.drop(n, data))

# the bytes data written at byte offset off of the device
def Ext2Dev.write_bytes(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +off: Nat, +data: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  +dbs = block_size(d)
  +first = Nat.div(off, dbs)
  +end = Nat.add(off, B.Octets.len(data))
  Ext2Dev.write.go(~Dv, ~block_size, ~read_block, ~write_block, Nat.sub(Nat.div(Nat.add(end, Nat.sub(dbs, 1n)), dbs), first), Done{d}, dbs, first, off, data)

# filesystem block n replaced by data (block_size(fs) bytes)
def Ext2Fs.write_block(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +n: Nat, +data: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    S.Ext2.require(Nat.is_eq(B.Octets.len(data), S.Ext2Fs.block_size(fs)), E.Ext2CheckFailed{"a block write of the wrong length"})
    S.Ext2.require(Nat.is_lt(n, S.Ext2Fs.blocks(fs)), E.Ext2BadBlockRef{0n, n})
    Ext2Dev.write_bytes(~Dv, ~block_size, ~read_block, ~write_block, d, Nat.mul(n, S.Ext2Fs.block_size(fs)), data)

# The superblock

def Ext2Meta.ro_compat(+raw: B.Octets) -> U32:
  F.Ext2Field.u32(raw, 100n)

def Ext2Meta.incompat(+raw: B.Octets) -> U32:
  F.Ext2Field.u32(raw, 96n)

def Ext2Meta.super_csum.pick(on: Bool, +raw: B.Octets) -> B.Octets:
  match on:
    case True{}:
      P.Ext2Patch.u32(raw, 1020n, K.Ext2Csum.super(raw))
    case False{}:
      raw

# a superblock's 1024 bytes with s_checksum recomputed (when it has
# metadata_csum)
def Ext2Meta.super_csum(+raw: B.Octets) -> B.Octets:
  Ext2Meta.super_csum.pick(F.Ext2Field.has(Ext2Meta.ro_compat(raw), 1024), raw)

# the superblock's 1024 bytes written at byte 1024, checksum recomputed
def Ext2Meta.write_super(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  Ext2Dev.write_bytes(~Dv, ~block_size, ~read_block, ~write_block, d, 1024n, Ext2Meta.super_csum(raw))

def Ext2Meta.sb_wide(+raw: B.Octets) -> Bool:
  F.Ext2Field.has(Ext2Meta.incompat(raw), 128)

def Ext2Meta.hi.pick(wide: Bool, +raw: B.Octets, off: Nat) -> U32:
  match wide:
    case True{}:
      F.Ext2Field.u32(raw, off)
    case False{}:
      0

def Ext2Meta.hi_bytes(wide: Bool) -> Nat:
  match wide:
    case True{}:
      4n
    case False{}:
      0n

# s_free_blocks_count (the high half with the 64bit feature)
def Ext2Meta.sb_free_blocks(+raw: B.Octets) -> Nat:
  F.Ext2Field.join(Ext2Meta.hi.pick(Ext2Meta.sb_wide(raw), raw, 344n), F.Ext2Field.u32(raw, 12n))

def Ext2Meta.sb_set_free_blocks(+raw: B.Octets, +n: Nat) -> B.Octets:
  P.Ext2Patch.split(raw, 12n, 344n, Ext2Meta.hi_bytes(Ext2Meta.sb_wide(raw)), n)

def Ext2Meta.sb_free_inodes(+raw: B.Octets) -> Nat:
  F.Ext2Field.nat(raw, 16n)

def Ext2Meta.sb_set_free_inodes(+raw: B.Octets, +n: Nat) -> B.Octets:
  P.Ext2Patch.u32(raw, 16n, U32.from_nat(n))

# the superblock's free counts moved: blocks by +bplus -bminus, inodes by
# +iplus -iminus (refused if a count would fall below zero)
def Ext2Meta.adjust_super(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +bplus: Nat, +bminus: Nat, +iplus: Nat, +iminus: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    +raw : B.Octets <- S.Ext2Super.read(~Dv, ~block_size, ~read_block, d)
    +fb : Nat = Nat.add(Ext2Meta.sb_free_blocks(raw), bplus)
    +fi : Nat = Nat.add(Ext2Meta.sb_free_inodes(raw), iplus)
    S.Ext2.require(Bool.and(Nat.is_le(bminus, fb), Nat.is_le(iminus, fi)), E.Ext2CheckFailed{"the superblock's free counts would fall below zero"})
    Ext2Meta.write_super(~Dv, ~block_size, ~read_block, ~write_block, d, Ext2Meta.sb_set_free_inodes(Ext2Meta.sb_set_free_blocks(raw, Nat.sub(fb, bminus)), Nat.sub(fi, iminus)))

# Geometry

def Ext2Meta.bpg(+fs: S.Ext2Fs) -> Nat:
  U32.to_nat(S.Ext2Super.blocks_per_group(S.Ext2Fs.sb(fs)))

def Ext2Meta.first_data_block(+fs: S.Ext2Fs) -> Nat:
  U32.to_nat(S.Ext2Super.first_data_block(S.Ext2Fs.sb(fs)))

# the number of blocks of group g (the last may be short)
def Ext2Meta.group_blocks(+fs: S.Ext2Fs, +g: Nat) -> Nat:
  Nat.min(Ext2Meta.bpg(fs), Nat.sub(S.Ext2Fs.blocks(fs), G.Ext2Group.first_block(fs, g)))

# the group holding block b
def Ext2Meta.group_of(+fs: S.Ext2Fs, +b: Nat) -> Nat:
  Nat.div(Nat.sub(b, Ext2Meta.first_data_block(fs)), Ext2Meta.bpg(fs))

# descriptors per block, and the blocks the descriptor table takes
def Ext2Meta.desc_per_block(+fs: S.Ext2Fs) -> Nat:
  Nat.div(S.Ext2Fs.block_size(fs), S.Ext2Fs.desc_size(fs))

def Ext2Meta.gdt_blocks(+fs: S.Ext2Fs) -> Nat:
  +per = Ext2Meta.desc_per_block(fs)
  Nat.div(Nat.add(S.Ext2Fs.groups(fs), Nat.sub(per, 1n)), per)

def Ext2Meta.wide(+fs: S.Ext2Fs) -> Bool:
  Nat.is_le(64n, S.Ext2Fs.desc_size(fs))

# the kind of checksum the image carries (whatever the reader verifies)
def Ext2Meta.kind(+fs: S.Ext2Fs) -> S.Ext2CsumKind:
  S.Ext2Super.csum_kind(S.Ext2Fs.sb(fs))

def Ext2Meta.is_meta(k: S.Ext2CsumKind) -> Bool:
  match k:
    case S.Ext2CsumMeta{}:
      True{}
    case _:
      False{}

def Ext2Meta.is_none(k: S.Ext2CsumKind) -> Bool:
  match k:
    case S.Ext2CsumNone{}:
      True{}
    case _:
      False{}

# whether the image has metadata_csum
def Ext2Meta.has_meta(+fs: S.Ext2Fs) -> Bool:
  Ext2Meta.is_meta(Ext2Meta.kind(fs))

# whether bg_flags and bg_itable_unused mean anything (gdt_csum or
# metadata_csum)
def Ext2Meta.has_uninit(+fs: S.Ext2Fs) -> Bool:
  Bool.not(Ext2Meta.is_none(Ext2Meta.kind(fs)))

# bg_flags
def Ext2Meta.inode_uninit() -> U32:
  1

def Ext2Meta.block_uninit() -> U32:
  2

def Ext2Meta.itable_zeroed() -> U32:
  4

# Group descriptors: their raw bytes, fields, checksum and writing

def Ext2Meta.desc_check(r: Result<&2, &2, E.Ext2Error, G.Ext2Group>, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  match r:
    case Done{x}:
      Done{raw}
    case Fail{e}:
      Fail{e}

# the bytes of descriptor g (checked as the reader checks them)
def Ext2Meta.desc_read.at(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +g: Nat, loc: G.Ext2DescLoc) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  match loc:
    case G.Ext2DescLoc{blk, +off}:
      do Result<&2, &2, E.Ext2Error, B.Octets>:
        S.Ext2.require(Nat.is_lt(g, S.Ext2Fs.groups(fs)), E.Ext2BadGroup{g})
        +o : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, blk)
        Ext2Meta.desc_check(G.Ext2Group.decode(fs, g, o, off), B.Octets.slice(off, S.Ext2Fs.desc_size(fs), o))

def Ext2Meta.desc_read(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +g: Nat) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  Ext2Meta.desc_read.at(~Dv, ~block_size, ~read_block, d, fs, g, G.Ext2Group.desc_loc(fs, g))

def Ext2Meta.desc(+fs: S.Ext2Fs, +raw: B.Octets) -> G.Ext2Group:
  G.Ext2Group.parse(S.Ext2Fs.has_incompat(fs, S.Ext2Super.incompat_64bit()), raw)

def Ext2Meta.desc_csum.go(k: S.Ext2CsumKind, +fs: S.Ext2Fs, +g: Nat, +raw: B.Octets) -> B.Octets:
  match k:
    case S.Ext2CsumMeta{}:
      P.Ext2Patch.u16(raw, 30n, K.Ext2Csum.group(S.Ext2Fs.seed(fs), U32.from_nat(g), raw, S.Ext2Fs.desc_size(fs)))
    case S.Ext2CsumGdt{}:
      P.Ext2Patch.u16(raw, 30n, K.Ext2Csum.group16(U.Uuid.to_bytes(S.Ext2Super.uuid(S.Ext2Fs.sb(fs))), U32.from_nat(g), raw, S.Ext2Fs.desc_size(fs)))
    case S.Ext2CsumNone{}:
      raw

# descriptor g's bytes with bg_checksum recomputed
def Ext2Meta.desc_csum(+fs: S.Ext2Fs, +g: Nat, +raw: B.Octets) -> B.Octets:
  Ext2Meta.desc_csum.go(Ext2Meta.kind(fs), fs, g, raw)

def Ext2Meta.desc_write.at(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +g: Nat, +raw: B.Octets, loc: G.Ext2DescLoc) -> Result<&2, &2, E.Ext2Error, Dv>:
  match loc:
    case G.Ext2DescLoc{+blk, +off}:
      do Result<&2, &2, E.Ext2Error, Dv>:
        +o : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, blk)
        Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d, fs, blk, P.Ext2Patch.bytes(o, off, Ext2Meta.desc_csum(fs, g, raw)))

# descriptor g replaced by raw (checksum recomputed), in the primary table
def Ext2Meta.desc_write(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +g: Nat, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  Ext2Meta.desc_write.at(~Dv, ~block_size, ~read_block, ~write_block, d, fs, g, raw, G.Ext2Group.desc_loc(fs, g))

def Ext2Meta.set_free_blocks(+fs: S.Ext2Fs, +raw: B.Octets, +v: U32) -> B.Octets:
  P.Ext2Patch.split16(raw, 12n, 44n, Ext2Meta.wide(fs), v)

def Ext2Meta.set_free_inodes(+fs: S.Ext2Fs, +raw: B.Octets, +v: U32) -> B.Octets:
  P.Ext2Patch.split16(raw, 14n, 46n, Ext2Meta.wide(fs), v)

def Ext2Meta.set_used_dirs(+fs: S.Ext2Fs, +raw: B.Octets, +v: U32) -> B.Octets:
  P.Ext2Patch.split16(raw, 16n, 48n, Ext2Meta.wide(fs), v)

def Ext2Meta.set_flags(+raw: B.Octets, +v: U32) -> B.Octets:
  P.Ext2Patch.u16(raw, 18n, v)

def Ext2Meta.set_itable_unused(+fs: S.Ext2Fs, +raw: B.Octets, +v: U32) -> B.Octets:
  P.Ext2Patch.split16(raw, 28n, 50n, Ext2Meta.wide(fs), v)

def Ext2Meta.clear_flag(+raw: B.Octets, +bit: U32) -> B.Octets:
  Ext2Meta.set_flags(raw, U32.and(U32.not(bit), F.Ext2Field.u16(raw, 18n)))

# Bitmaps

# the checksum of the first n bytes of a bitmap
def Ext2Meta.bitmap_csum(+fs: S.Ext2Fs, +bm: B.Octets, n: Nat) -> U32:
  K.Ext2Csum.crc32c(S.Ext2Fs.seed(fs), B.Octets.take(n, bm))

def Ext2Meta.uninit(+fs: S.Ext2Fs, +flags: U32, +bit: U32) -> Bool:
  Bool.and(Ext2Meta.has_uninit(fs), F.Ext2Field.has(flags, bit))

# the blocks of [lo, hi) that fall in [base, base + n), as bit numbers of
# the group starting at base
def Ext2Meta.in_group(+lo: Nat, +hi: Nat, +base: Nat, +n: Nat) -> List<&2, Nat>:
  +a = Nat.max(lo, base)
  +b = Nat.min(hi, Nat.add(base, n))
  M.Ext2Bitmap.range(Nat.sub(a, base), Nat.sub(Nat.max(a, b), base))

# with meta_bg, whether group g holds a copy of its meta group's descriptor
# block (the first, second and last groups of the meta group)
def Ext2Meta.meta_copy(+fs: S.Ext2Fs, +g: Nat) -> Bool:
  +per = Ext2Meta.desc_per_block(fs)
  +j = Nat.mod(g, per)
  +sb = S.Ext2Fs.sb(fs)
  Bool.and(S.Ext2Super.has_incompat(sb, S.Ext2Super.incompat_meta_bg()), Bool.and(Nat.is_le(U32.to_nat(S.Ext2Super.first_meta_bg(sb)), Nat.div(g, per)), Bool.or(Nat.is_le(j, 1n), Nat.is_eq(j, Nat.sub(per, 1n)))))

def Ext2Meta.gdt_len.pick(meta: Bool, +first_meta: Nat, +all: Nat) -> Nat:
  match meta:
    case True{}:
      Nat.min(first_meta, all)
    case False{}:
      all

# the blocks after a superblock copy that the old-style descriptor table and
# its reserved blocks take (with meta_bg the table covers only the first
# s_first_meta_bg descriptor blocks)
def Ext2Meta.gdt_len(+fs: S.Ext2Fs) -> Nat:
  +sb = S.Ext2Fs.sb(fs)
  +old = Ext2Meta.gdt_len.pick(S.Ext2Super.has_incompat(sb, S.Ext2Super.incompat_meta_bg()), U32.to_nat(S.Ext2Super.first_meta_bg(sb)), Ext2Meta.gdt_blocks(fs))
  Nat.add(old, U32.to_nat(S.Ext2Super.reserved_gdt_blocks(sb)))

# the inode table's length in blocks
def Ext2Meta.itable_blocks(+fs: S.Ext2Fs) -> Nat:
  +bs = S.Ext2Fs.block_size(fs)
  Nat.div(Nat.add(Nat.mul(S.Ext2Fs.inodes_per_group(fs), S.Ext2Fs.inode_size(fs)), Nat.sub(bs, 1n)), bs)

def Ext2Meta.flag_bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# the bits of group g's own superblock copy, descriptor table and reserved
# descriptor blocks, and (meta_bg) its copy of its meta group's descriptors
def Ext2Meta.super_bits(+fs: S.Ext2Fs, +g: Nat) -> List<&2, Nat>:
  +sup = Ext2Meta.flag_bit(G.Ext2Group.has_super(fs, g))
  +lead = Nat.mul(sup, Nat.add(1n, Ext2Meta.gdt_len(fs)))
  +lead2 = Nat.add(lead, Ext2Meta.flag_bit(Ext2Meta.meta_copy(fs, g)))
  M.Ext2Bitmap.range(0n, Nat.min(lead2, Ext2Meta.group_blocks(fs, g)))

# the bits of the group at base (n blocks) taken by a group's bitmaps and
# inode table (desc: that group's descriptor)
def Ext2Meta.meta_bits(+fs: S.Ext2Fs, +desc: G.Ext2Group, +base: Nat, +n: Nat) -> List<&2, List<&2, Nat>>:
  +bb = G.Ext2Group.block_bitmap(desc)
  +ib = G.Ext2Group.inode_bitmap(desc)
  +it = G.Ext2Group.inode_table(desc)
  [Ext2Meta.in_group(bb, Nat.add(bb, 1n), base, n), Ext2Meta.in_group(ib, Nat.add(ib, 1n), base, n), Ext2Meta.in_group(it, Nat.add(it, Ext2Meta.itable_blocks(fs)), base, n)]

def Ext2Meta.mark_all(xs: List<&2, List<&2, Nat>>, bm: B.Octets) -> B.Octets:
  match xs:
    case Nil{}:
      bm
    case Con{ks, t}:
      Ext2Meta.mark_all(t, M.Ext2Bitmap.update(bm, ks, True{}))

# every group's metadata that lies in the group at base (n blocks), marked
# on the bitmap r holds, from group gi on
def Ext2Meta.uninit.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, count: Nat, r: Result<&2, &2, E.Ext2Error, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +base: Nat, +n: Nat, +gi: Nat) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  match count r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{bm}:
      Done{bm}
    case 1n+c Done{bm}:
      +r2 = Result.bind(&2, &2, E.Ext2Error, B.Octets, B.Octets, Ext2Meta.desc_read(~Dv, ~block_size, ~read_block, d, fs, gi), raw => Done{Ext2Meta.mark_all(Ext2Meta.meta_bits(fs, Ext2Meta.desc(fs, raw), base, n), bm)})
      Ext2Meta.uninit.go(~Dv, ~block_size, ~read_block, c, r2, d, fs, base, n, Nat.add(gi, 1n))

# the block bitmap a BLOCK_UNINIT group stands for: its superblock and
# descriptor copies, every group's bitmaps and inode table that lie in it,
# and the padding past its end
def Ext2Meta.uninit_block_bitmap(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +g: Nat) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  +bs = S.Ext2Fs.block_size(fs)
  +n = Ext2Meta.group_blocks(fs, g)
  +bm0 = M.Ext2Bitmap.update(M.Ext2Bitmap.make(bs, 0n, n), Ext2Meta.super_bits(fs, g), True{})
  Ext2Meta.uninit.go(~Dv, ~block_size, ~read_block, S.Ext2Fs.groups(fs), Done{bm0}, d, fs, G.Ext2Group.first_block(fs, g), n, 0n)

def Ext2Meta.read_bitmap(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +b: Nat) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  do Result<&2, &2, E.Ext2Error, B.Octets>:
    S.Ext2.require(Bool.and(Nat.is_lt(0n, b), Nat.is_lt(b, S.Ext2Fs.blocks(fs))), E.Ext2BadBlockRef{0n, b})
    S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, b)

def Ext2Meta.block_bitmap.pick(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, uninit: Bool, +d: Dv, +fs: S.Ext2Fs, +g: Nat, +desc: G.Ext2Group) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  match uninit:
    case True{}:
      Ext2Meta.uninit_block_bitmap(~Dv, ~block_size, ~read_block, d, fs, g)
    case False{}:
      Ext2Meta.read_bitmap(~Dv, ~block_size, ~read_block, d, fs, G.Ext2Group.block_bitmap(desc))

# group g's block bitmap (one block; bit k is the group's block k), rebuilt
# when the group is BLOCK_UNINIT
def Ext2Meta.block_bitmap(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +g: Nat, +desc: G.Ext2Group) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  Ext2Meta.block_bitmap.pick(~Dv, ~block_size, ~read_block, Ext2Meta.uninit(fs, G.Ext2Group.flags(desc), Ext2Meta.block_uninit()), d, fs, g, desc)

def Ext2Meta.inode_bitmap.pick(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, uninit: Bool, +d: Dv, +fs: S.Ext2Fs, +desc: G.Ext2Group) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  match uninit:
    case True{}:
      Done{M.Ext2Bitmap.make(S.Ext2Fs.block_size(fs), 0n, S.Ext2Fs.inodes_per_group(fs))}
    case False{}:
      Ext2Meta.read_bitmap(~Dv, ~block_size, ~read_block, d, fs, G.Ext2Group.inode_bitmap(desc))

# a group's inode bitmap (bit k is the group's inode k + 1), all clear when
# the group is INODE_UNINIT
def Ext2Meta.inode_bitmap(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +desc: G.Ext2Group) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  Ext2Meta.inode_bitmap.pick(~Dv, ~block_size, ~read_block, Ext2Meta.uninit(fs, G.Ext2Group.flags(desc), Ext2Meta.inode_uninit()), d, fs, desc)

def Ext2Meta.bitmap_field.pick(on: Bool, +fs: S.Ext2Fs, +raw: B.Octets, +lo: Nat, +hi: Nat, +bm: B.Octets, +n: Nat) -> B.Octets:
  match on:
    case True{}:
      P.Ext2Patch.split16(raw, lo, hi, Ext2Meta.wide(fs), Ext2Meta.bitmap_csum(fs, bm, n))
    case False{}:
      raw

# a group's block bitmap written: the descriptor's bytes (raw) come back
# with BLOCK_UNINIT cleared and the bitmap's checksum set (metadata_csum)
def Ext2Meta.put_block_bitmap(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +raw: B.Octets, +bm: B.Octets) -> Result<&2, &2, E.Ext2Error, Ext2Out<Dv, B.Octets>>:
  do Result<&2, &2, E.Ext2Error, Ext2Out<Dv, B.Octets>>:
    d2 : Dv <- Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d, fs, G.Ext2Group.block_bitmap(Ext2Meta.desc(fs, raw)), bm)
    return Ext2Out{d2, Ext2Meta.bitmap_field.pick(Ext2Meta.has_meta(fs), fs, Ext2Meta.clear_flag(raw, Ext2Meta.block_uninit()), 24n, 56n, bm, Nat.div(Ext2Meta.bpg(fs), 8n))}

# the same for a group's inode bitmap (INODE_UNINIT cleared)
def Ext2Meta.put_inode_bitmap(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +raw: B.Octets, +bm: B.Octets) -> Result<&2, &2, E.Ext2Error, Ext2Out<Dv, B.Octets>>:
  do Result<&2, &2, E.Ext2Error, Ext2Out<Dv, B.Octets>>:
    d2 : Dv <- Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d, fs, G.Ext2Group.inode_bitmap(Ext2Meta.desc(fs, raw)), bm)
    return Ext2Out{d2, Ext2Meta.bitmap_field.pick(Ext2Meta.has_meta(fs), fs, Ext2Meta.clear_flag(raw, Ext2Meta.inode_uninit()), 26n, 58n, bm, Nat.div(S.Ext2Fs.inodes_per_group(fs), 8n))}

# MemDev.write_block as the writer's template argument (whose parameters are
# plain, not reusable): pass ~Ext2Dev.mem_write with ~D.MemDev
def Ext2Dev.mem_write(d: D.MemDev, n: Nat, data: B.Octets) -> Result<&2, &2, D.DevError, D.MemDev>:
  D.MemDev.write_block(d, n, data)
