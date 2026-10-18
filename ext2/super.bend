# bend-osdev-ext2: the superblock (1024 bytes at byte 1024 of the device),
# its validation, and the mounted filesystem's geometry.
#
# Layout: "The Second Extended File System: Internal Layout" (Dave Poirier),
# "Superblock"; the ext4 fields (64-bit counts, descriptor size, checksums)
# from the ext4 disk-layout documentation, "The Super Block".
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../uuid/uuid.bend as U
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./options.bend as O
import ./field.bend as F
import ./csum.bend as K

type Ext2Super is Data:
  Ext2Super{inodes_count: U32, blocks_count: W.W64, r_blocks_count: W.W64, free_blocks_count: W.W64, free_inodes_count: U32, first_data_block: U32, log_block_size: U32, log_cluster_size: U32, blocks_per_group: U32, inodes_per_group: U32, mtime: U32, wtime: U32, magic: U32, state: U32, errors: U32, minor_rev: U32, creator_os: U32, rev_level: U32, first_ino: U32, inode_size: U32, feature_compat: U32, feature_incompat: U32, feature_ro_compat: U32, uuid: U.Uuid, volume_name: B.Octets, reserved_gdt_blocks: U32, desc_size: U32, first_meta_bg: U32, min_extra_isize: U32, log_groups_per_flex: U32, checksum_type: U32, checksum_seed: U32, backup_bgs0: U32, backup_bgs1: U32, checksum: U32}

# Feature bits

# s_feature_compat
def Ext2Super.compat_has_journal() -> U32:
  4

def Ext2Super.compat_dir_index() -> U32:
  32

def Ext2Super.compat_sparse_super2() -> U32:
  512

# s_feature_incompat
def Ext2Super.incompat_filetype() -> U32:
  2

def Ext2Super.incompat_recover() -> U32:
  4

def Ext2Super.incompat_meta_bg() -> U32:
  16

def Ext2Super.incompat_extents() -> U32:
  64

def Ext2Super.incompat_64bit() -> U32:
  128

def Ext2Super.incompat_csum_seed() -> U32:
  8192

# s_feature_ro_compat
def Ext2Super.ro_compat_sparse_super() -> U32:
  1

def Ext2Super.ro_compat_huge_file() -> U32:
  8

def Ext2Super.ro_compat_gdt_csum() -> U32:
  16

def Ext2Super.ro_compat_metadata_csum() -> U32:
  1024

# the names e2fsprogs gives the incompat bits
type Ext2FeatureName is Data:
  Ext2FeatureName{bit: U32, name: String}

def Ext2Super.incompat_names() -> List<&2, Ext2FeatureName>:
  [Ext2FeatureName{1, "compression"}, Ext2FeatureName{2, "filetype"}, Ext2FeatureName{4, "needs_recovery"}, Ext2FeatureName{8, "journal_dev"}, Ext2FeatureName{16, "meta_bg"}, Ext2FeatureName{64, "extent"}, Ext2FeatureName{128, "64bit"}, Ext2FeatureName{256, "mmp"}, Ext2FeatureName{512, "flex_bg"}, Ext2FeatureName{1024, "ea_inode"}, Ext2FeatureName{4096, "dirdata"}, Ext2FeatureName{8192, "metadata_csum_seed"}, Ext2FeatureName{16384, "large_dir"}, Ext2FeatureName{32768, "inline_data"}, Ext2FeatureName{65536, "encrypt"}, Ext2FeatureName{131072, "casefold"}]

def Ext2Super.name_of.pick(hit: Bool, name: String, rest: String) -> String:
  match hit:
    case True{}:
      name
    case False{}:
      rest

def Ext2Super.name_of(xs: List<&2, Ext2FeatureName>, +bit: U32) -> String:
  match xs:
    case Nil{}:
      "incompat bit " ++ U32.show(bit)
    case Con{Ext2FeatureName{b, n}, t}:
      Ext2Super.name_of.pick(U32.is_eq(b, bit), n, Ext2Super.name_of(t, bit))

def Ext2Super.incompat_name(+bit: U32) -> String:
  Ext2Super.name_of(Ext2Super.incompat_names(), bit)

# the lowest set bit of m (0 if none), testing n bits from bit
def Ext2Super.lowest.go(n: Nat, set: Bool, +m: U32, +bit: U32) -> U32:
  match n set:
    case 0n _:
      0
    case 1n+p True{}:
      bit
    case 1n+p False{}:
      +next = U32.shl(bit)
      Ext2Super.lowest.go(p, F.Ext2Field.has(m, next), m, next)

def Ext2Super.lowest(+m: U32) -> U32:
  Ext2Super.lowest.go(32n, F.Ext2Field.has(m, 1), m, 1)

# Parsing: the fields of a 1024-byte superblock (no checks)

def Ext2Super.parse(+o: B.Octets) -> Ext2Super:
  Ext2Super{F.Ext2Field.u32(o, 0n), W.W64.from_parts(F.Ext2Field.u32(o, 336n), F.Ext2Field.u32(o, 4n)), W.W64.from_parts(F.Ext2Field.u32(o, 340n), F.Ext2Field.u32(o, 8n)), W.W64.from_parts(F.Ext2Field.u32(o, 344n), F.Ext2Field.u32(o, 12n)), F.Ext2Field.u32(o, 16n), F.Ext2Field.u32(o, 20n), F.Ext2Field.u32(o, 24n), F.Ext2Field.u32(o, 28n), F.Ext2Field.u32(o, 32n), F.Ext2Field.u32(o, 40n), F.Ext2Field.u32(o, 44n), F.Ext2Field.u32(o, 48n), F.Ext2Field.u16(o, 56n), F.Ext2Field.u16(o, 58n), F.Ext2Field.u16(o, 60n), F.Ext2Field.u16(o, 62n), F.Ext2Field.u32(o, 72n), F.Ext2Field.u32(o, 76n), F.Ext2Field.u32(o, 84n), F.Ext2Field.u16(o, 88n), F.Ext2Field.u32(o, 92n), F.Ext2Field.u32(o, 96n), F.Ext2Field.u32(o, 100n), Maybe.default(&2, U.Uuid, U.Uuid.from_bytes_at(o, 104n), U.Uuid.nil()), B.Octets.slice(120n, 16n, o), F.Ext2Field.u16(o, 206n), F.Ext2Field.u16(o, 254n), F.Ext2Field.u32(o, 260n), F.Ext2Field.u16(o, 348n), F.Ext2Field.u8(o, 372n), F.Ext2Field.u8(o, 373n), F.Ext2Field.u32(o, 624n), F.Ext2Field.u32(o, 588n), F.Ext2Field.u32(o, 592n), F.Ext2Field.u32(o, 1020n)}

# Accessors

def Ext2Super.magic(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      mg

def Ext2Super.uuid(s: Ext2Super) -> U.Uuid:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      uu

def Ext2Super.inodes_count(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      ic

def Ext2Super.blocks_count(s: Ext2Super) -> W.W64:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      bc

def Ext2Super.free_blocks_count(s: Ext2Super) -> W.W64:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      fb

def Ext2Super.free_inodes_count(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      fi

def Ext2Super.first_data_block(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      fdb

def Ext2Super.log_block_size(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      lbs

def Ext2Super.blocks_per_group(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      bpg

def Ext2Super.inodes_per_group(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      ipg

def Ext2Super.state(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      st

def Ext2Super.rev_level(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      rev

def Ext2Super.first_ino.raw(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      fino

def Ext2Super.inode_size.raw(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      isz

def Ext2Super.feature_compat(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      fc

def Ext2Super.feature_incompat(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      fic

def Ext2Super.feature_ro_compat(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      frc

def Ext2Super.volume_name(s: Ext2Super) -> B.Octets:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      vn

def Ext2Super.desc_size.raw(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      dsz

def Ext2Super.first_meta_bg(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      fmbg

def Ext2Super.checksum_type(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      ckt

def Ext2Super.checksum_seed(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      cks

def Ext2Super.backup_bgs(s: Ext2Super) -> U32 & U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      (bb0, bb1)

def Ext2Super.checksum(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      ck

def Ext2Super.reserved_gdt_blocks(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      rgdt

def Ext2Super.min_extra_isize(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      mex

def Ext2Super.r_blocks_count(s: Ext2Super) -> W.W64:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      rb

def Ext2Super.errors(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      er

def Ext2Super.log_groups_per_flex(s: Ext2Super) -> U32:
  match s:
    case Ext2Super{ic, bc, rb, fb, fi, fdb, lbs, lcs, bpg, ipg, mt, wt, mg, st, er, mr, os, rev, fino, isz, fc, fic, frc, uu, vn, rgdt, dsz, fmbg, mex, lgf, ckt, cks, bb0, bb1, ck}:
      lgf

# Derived values

def Ext2Super.has_compat(+s: Ext2Super, bit: U32) -> Bool:
  F.Ext2Field.has(Ext2Super.feature_compat(s), bit)

def Ext2Super.has_incompat(+s: Ext2Super, bit: U32) -> Bool:
  F.Ext2Field.has(Ext2Super.feature_incompat(s), bit)

def Ext2Super.has_ro_compat(+s: Ext2Super, bit: U32) -> Bool:
  F.Ext2Field.has(Ext2Super.feature_ro_compat(s), bit)

# bytes per block: 1024 << s_log_block_size
def Ext2Super.block_size(+s: Ext2Super) -> Nat:
  Nat.mul(1024n, Nat.pow(2n, U32.to_nat(Ext2Super.log_block_size(s))))

# the number of blocks (the high half only with the 64bit feature; 48 bits
# at most, as ext4 allows)
def Ext2Super.block_count.pick(wide: Bool, +bc: W.W64) -> Nat:
  match wide:
    case True{}:
      F.Ext2Field.join(W.W64.hi(bc), W.W64.lo(bc))
    case False{}:
      U32.to_nat(W.W64.lo(bc))

def Ext2Super.block_count(+s: Ext2Super) -> Nat:
  Ext2Super.block_count.pick(Ext2Super.has_incompat(s, Ext2Super.incompat_64bit()), Ext2Super.blocks_count(s))

def Ext2Super.is_rev0(+s: Ext2Super) -> Bool:
  U32.is_eq(Ext2Super.rev_level(s), 0)

# the inode size: 128 in revision 0
def Ext2Super.inode_size.pick(rev0: Bool, isz: U32) -> Nat:
  match rev0:
    case True{}:
      128n
    case False{}:
      U32.to_nat(isz)

def Ext2Super.inode_size(+s: Ext2Super) -> Nat:
  Ext2Super.inode_size.pick(Ext2Super.is_rev0(s), Ext2Super.inode_size.raw(s))

# the first non-reserved inode: 11 in revision 0
def Ext2Super.first_ino.pick(rev0: Bool, fino: U32) -> Nat:
  match rev0:
    case True{}:
      11n
    case False{}:
      U32.to_nat(fino)

def Ext2Super.first_ino(+s: Ext2Super) -> Nat:
  Ext2Super.first_ino.pick(Ext2Super.is_rev0(s), Ext2Super.first_ino.raw(s))

# the group descriptor size: 32, or s_desc_size with the 64bit feature
def Ext2Super.desc_size.pick(wide: Bool, dsz: U32) -> Nat:
  match wide:
    case True{}:
      U32.to_nat(dsz)
    case False{}:
      32n

def Ext2Super.desc_size(+s: Ext2Super) -> Nat:
  Ext2Super.desc_size.pick(Ext2Super.has_incompat(s, Ext2Super.incompat_64bit()), Ext2Super.desc_size.raw(s))

# the number of block groups
def Ext2Super.group_count(+s: Ext2Super) -> Nat:
  +bpg = U32.to_nat(Ext2Super.blocks_per_group(s))
  Nat.div(Nat.add(Nat.sub(Ext2Super.block_count(s), U32.to_nat(Ext2Super.first_data_block(s))), Nat.sub(bpg, 1n)), bpg)

# the volume label, up to its first NUL
def Ext2Super.label.cut(nul: Bool, h: U32, rest: String) -> String:
  match nul:
    case True{}:
      ""
    case False{}:
      SCon{Chr{h}, rest}

def Ext2Super.label.go(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+h, t}:
      Ext2Super.label.cut(U32.is_eq(h, 0), h, Ext2Super.label.go(t))

def Ext2Super.label(+s: Ext2Super) -> String:
  Ext2Super.label.go(B.Octets.to_list(Ext2Super.volume_name(s)))

# Checksums: which kind the image carries

type Ext2CsumKind is Data:
  Ext2CsumNone{}
  Ext2CsumGdt{}
  Ext2CsumMeta{}

def Ext2CsumKind.pick(meta: Bool, gdt: Bool) -> Ext2CsumKind:
  match meta gdt:
    case True{} _:
      Ext2CsumMeta{}
    case False{} True{}:
      Ext2CsumGdt{}
    case False{} False{}:
      Ext2CsumNone{}

def Ext2Super.csum_kind(+s: Ext2Super) -> Ext2CsumKind:
  Ext2CsumKind.pick(Ext2Super.has_ro_compat(s, Ext2Super.ro_compat_metadata_csum()), Ext2Super.has_ro_compat(s, Ext2Super.ro_compat_gdt_csum()))

# the checksum seed: s_checksum_seed with csum_seed, else crc32c(~0, uuid)
def Ext2Super.seed.pick(stored: Bool, +s: Ext2Super) -> U32:
  match stored:
    case True{}:
      Ext2Super.checksum_seed(s)
    case False{}:
      K.Ext2Csum.seed(U.Uuid.to_bytes(Ext2Super.uuid(s)))

def Ext2Super.seed(+s: Ext2Super) -> U32:
  Ext2Super.seed.pick(Ext2Super.has_incompat(s, Ext2Super.incompat_csum_seed()), s)

# The mounted filesystem: the superblock, the options, and the geometry
# derived from them once. csum is the kind of checksum verified (none when
# the options turn verification off).

type Ext2Fs is Data:
  Ext2Fs{sb: Ext2Super, opts: O.Ext2Options, block_size: Nat, blocks: Nat, groups: Nat, desc_size: Nat, inode_size: Nat, inodes_per_group: Nat, seed: U32, csum: Ext2CsumKind}

def Ext2Fs.sb(f: Ext2Fs) -> Ext2Super:
  match f:
    case Ext2Fs{s, o, bs, n, g, ds, isz, ipg, seed, k}:
      s

def Ext2Fs.opts(f: Ext2Fs) -> O.Ext2Options:
  match f:
    case Ext2Fs{s, o, bs, n, g, ds, isz, ipg, seed, k}:
      o

def Ext2Fs.block_size(f: Ext2Fs) -> Nat:
  match f:
    case Ext2Fs{s, o, bs, n, g, ds, isz, ipg, seed, k}:
      bs

def Ext2Fs.blocks(f: Ext2Fs) -> Nat:
  match f:
    case Ext2Fs{s, o, bs, n, g, ds, isz, ipg, seed, k}:
      n

def Ext2Fs.groups(f: Ext2Fs) -> Nat:
  match f:
    case Ext2Fs{s, o, bs, n, g, ds, isz, ipg, seed, k}:
      g

def Ext2Fs.desc_size(f: Ext2Fs) -> Nat:
  match f:
    case Ext2Fs{s, o, bs, n, g, ds, isz, ipg, seed, k}:
      ds

def Ext2Fs.inode_size(f: Ext2Fs) -> Nat:
  match f:
    case Ext2Fs{s, o, bs, n, g, ds, isz, ipg, seed, k}:
      isz

def Ext2Fs.inodes_per_group(f: Ext2Fs) -> Nat:
  match f:
    case Ext2Fs{s, o, bs, n, g, ds, isz, ipg, seed, k}:
      ipg

def Ext2Fs.seed(f: Ext2Fs) -> U32:
  match f:
    case Ext2Fs{s, o, bs, n, g, ds, isz, ipg, seed, k}:
      seed

def Ext2Fs.csum(f: Ext2Fs) -> Ext2CsumKind:
  match f:
    case Ext2Fs{s, o, bs, n, g, ds, isz, ipg, seed, k}:
      k

def Ext2Fs.is_meta.go(k: Ext2CsumKind) -> Bool:
  match k:
    case Ext2CsumMeta{}:
      True{}
    case _:
      False{}

# whether metadata_csum checksums are verified
def Ext2Fs.verify_meta(+f: Ext2Fs) -> Bool:
  Ext2Fs.is_meta.go(Ext2Fs.csum(f))

def Ext2Fs.has_incompat(+f: Ext2Fs, bit: U32) -> Bool:
  Ext2Super.has_incompat(Ext2Fs.sb(f), bit)

def Ext2Fs.inodes_count(+f: Ext2Fs) -> Nat:
  U32.to_nat(Ext2Super.inodes_count(Ext2Fs.sb(f)))

# Validation

def Ext2.require(ok: Bool, e: E.Ext2Error) -> Result<&2, &2, E.Ext2Error, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

# whether x is a power of two, halving it at most n times (one: x is 1;
# even: x is even). No power is ever built, so the test stays cheap for a
# symbolic x too (a proof normalises it).
def Ext2.is_pow2.go(n: Nat, one: Bool, even: Bool, +x: Nat) -> Bool:
  match n one even:
    case 0n _ _:
      False{}
    case 1n+k True{} _:
      True{}
    case 1n+k False{} True{}:
      +h = Nat.div(x, 2n)
      Ext2.is_pow2.go(k, Nat.is_eq(h, 1n), Nat.is_eq(Nat.mod(h, 2n), 0n), h)
    case 1n+k False{} False{}:
      False{}

# whether x is a power of two up to 2^40 (an inode or descriptor size)
def Ext2.is_pow2(+x: Nat) -> Bool:
  Ext2.is_pow2.go(41n, Nat.is_eq(x, 1n), Nat.is_eq(Nat.mod(x, 2n), 0n), x)

# the incompat features this reader refuses (the journal's recover bit is
# judged separately)
def Ext2Super.unsupported(+s: Ext2Super, +o: O.Ext2Options) -> U32:
  match o:
    case O.Ext2Options{inc, v, r, h, m}:
      U32.and(Ext2Super.feature_incompat(s), U32.not(U32.or(inc, Ext2Super.incompat_recover())))

def Ext2Super.check_features(+bad: U32) -> Result<&2, &2, E.Ext2Error, Unit>:
  Ext2.require(U32.is_eq(bad, 0), E.Ext2Unsupported{Ext2Super.incompat_name(Ext2Super.lowest(bad))})

def Ext2Super.recovery_ok(+s: Ext2Super, +o: O.Ext2Options) -> Bool:
  match o:
    case O.Ext2Options{inc, v, r, h, m}:
      Bool.or(r, Bool.not(Ext2Super.has_incompat(s, Ext2Super.incompat_recover())))

def Ext2Super.verify_on(+o: O.Ext2Options) -> Bool:
  match o:
    case O.Ext2Options{inc, v, r, h, m}:
      v

# the superblock checksum, when metadata_csum is on and verification asked for
def Ext2Super.check_csum(on: Bool, +s: Ext2Super, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, Unit>:
  match on:
    case True{}:
      do Result<&2, &2, E.Ext2Error, Unit>:
        Ext2.require(U32.is_eq(Ext2Super.checksum_type(s), 1), E.Ext2BadChecksumType{Ext2Super.checksum_type(s)})
        +c : U32 = K.Ext2Csum.super(raw)
        Ext2.require(U32.is_eq(c, Ext2Super.checksum(s)), E.Ext2BadSuperCsum{Ext2Super.checksum(s), c})
    case False{}:
      Done{Unit{}}

def Ext2Fs.csum_kind(verify: Bool, +s: Ext2Super) -> Ext2CsumKind:
  match verify:
    case True{}:
      Ext2Super.csum_kind(s)
    case False{}:
      Ext2CsumNone{}

# the superblock (1024 bytes), checked, and the filesystem it describes
def Ext2Fs.mount(+opts: O.Ext2Options, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, Ext2Fs>:
  +s = Ext2Super.parse(raw)
  do Result<&2, &2, E.Ext2Error, Ext2Fs>:
    Ext2.require(Nat.is_eq(B.Octets.len(raw), 1024n), E.Ext2BadGeometry{"a superblock is 1024 bytes"})
    Ext2.require(U32.is_eq(Ext2Super.magic(s), 61267), E.Ext2BadMagic{Ext2Super.magic(s)})
    Ext2.require(U32.is_le(Ext2Super.rev_level(s), 1), E.Ext2BadRevision{Ext2Super.rev_level(s)})
    Ext2.require(U32.is_le(Ext2Super.log_block_size(s), 6), E.Ext2BadBlockSize{Ext2Super.log_block_size(s)})
    Ext2Super.check_features(Ext2Super.unsupported(s, opts))
    Ext2.require(Ext2Super.recovery_ok(s, opts), E.Ext2NeedsRecovery{})
    Ext2Super.check_csum(Bool.and(Ext2Super.verify_on(opts), Ext2Super.has_ro_compat(s, Ext2Super.ro_compat_metadata_csum())), s, raw)
    +bs : Nat = Ext2Super.block_size(s)
    +isz : Nat = Ext2Super.inode_size(s)
    Ext2.require(Bool.and(Ext2.is_pow2(isz), Bool.and(Nat.is_le(128n, isz), Nat.is_le(isz, bs))), E.Ext2BadInodeSize{U32.from_nat(isz)})
    +ds : Nat = Ext2Super.desc_size(s)
    Ext2.require(Bool.and(Ext2.is_pow2(ds), Bool.and(Nat.is_le(32n, ds), Nat.is_le(ds, 1024n))), E.Ext2BadDescSize{U32.from_nat(ds)})
    Ext2.require(Bool.or(Bool.not(Ext2Super.has_incompat(s, Ext2Super.incompat_64bit())), Nat.is_le(64n, ds)), E.Ext2BadDescSize{U32.from_nat(ds)})
    +bpg : Nat = U32.to_nat(Ext2Super.blocks_per_group(s))
    +ipg : Nat = U32.to_nat(Ext2Super.inodes_per_group(s))
    Ext2.require(Bool.and(Nat.is_lt(0n, bpg), Nat.is_le(bpg, Nat.mul(8n, bs))), E.Ext2BadGeometry{"blocks per group"})
    Ext2.require(Bool.and(Nat.is_lt(0n, ipg), Nat.is_le(ipg, Nat.mul(8n, bs))), E.Ext2BadGeometry{"inodes per group"})
    +n : Nat = Ext2Super.block_count(s)
    Ext2.require(Nat.is_lt(U32.to_nat(Ext2Super.first_data_block(s)), n), E.Ext2BadGeometry{"first data block"})
    +g : Nat = Ext2Super.group_count(s)
    Ext2.require(Nat.is_eq(U32.to_nat(Ext2Super.inodes_count(s)), Nat.mul(g, ipg)), E.Ext2BadGeometry{"inode count"})
    Ext2.require(Nat.is_le(11n, Ext2Super.first_ino(s)), E.Ext2BadGeometry{"first inode"})
    return Ext2Fs{s, opts, bs, n, g, ds, isz, ipg, Ext2Super.seed(s), Ext2Fs.csum_kind(Ext2Super.verify_on(opts), s)}

# Reading through a device (blockdev's interface, as template arguments)

def Ext2.dev(r: Result<&2, &2, D.DevError, B.Octets>) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  match r:
    case Done{o}:
      Done{o}
    case Fail{e}:
      Fail{E.Ext2Dev{e}}

# the 1024 bytes of the superblock, at byte 1024 of the device
def Ext2Super.read(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  Ext2.dev(D.Dev.read_bytes(~Dv, ~block_size, ~read_block, d, 1024n, 1024n))

# the filesystem on a device, with these options
def Ext2Fs.open(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +opts: O.Ext2Options) -> Result<&2, &2, E.Ext2Error, Ext2Fs>:
  do Result<&2, &2, E.Ext2Error, Ext2Fs>:
    raw : B.Octets <- Ext2Super.read(~Dv, ~block_size, ~read_block, d)
    Ext2Fs.mount(opts, raw)

# filesystem block n (block_size(fs) bytes)
def Ext2Fs.read_block(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: Ext2Fs, n: Nat) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  +bs = Ext2Fs.block_size(fs)
  Ext2.dev(D.Dev.read_bytes(~Dv, ~block_size, ~read_block, d, Nat.mul(n, bs), bs))

# the same filesystem, following up to h symbolic links in a path (the
# other options were fixed when it was opened)
def Ext2Fs.with_symlink_hops(f: Ext2Fs, h: Nat) -> Ext2Fs:
  match f:
    case Ext2Fs{s, o, bs, n, g, ds, isz, ipg, seed, k}:
      Ext2Fs{s, O.Ext2Options.with_symlink_hops(o, h), bs, n, g, ds, isz, ipg, seed, k}
