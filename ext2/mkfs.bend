# bend-osdev-ext2: making a filesystem (mkfs) of revision 1: the
# superblock and its sparse backups, the descriptor table and its backups,
# each group's bitmaps (their padding past the group set) and inode table
# (zeroed, when the options ask), the reserved inodes 1 to 10, the root
# directory (inode 2) and lost+found (inode 11). The result is checked
# before it is answered: it must open (Ext2.open, with the default options)
# and pass Ext2Fsck.full.
#
# Features written, as the options choose: sparse_super, filetype,
# large_file, and for an ext4-compatible image without a journal: extent
# (new files get extent trees), 64bit (64-byte descriptors), metadata_csum
# (every checksum), dir_nlink, extra_isize. Not written: has_journal (the
# journal is bend-osdev-ext4's), resize_inode (no reserved descriptor
# blocks), dir_index, flex_bg, meta_bg, uninit_bg and the uninit flags (every
# group is initialised), huge_file, ext_attr.
#
# Layout: Poirier, "Superblock", "Block Group Descriptor Table", "Block
# Bitmap", "Inode Bitmap", "Inode Table"; the ext4 disk-layout
# documentation, "Blocks", "Layout", "The Super Block", "Block Group
# Descriptors", "Special inodes".
import Base
import ../bytes/bytes.bend as B
import ../uuid/uuid.bend as U
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./options.bend as O
import ./csum.bend as K
import ./super.bend as S
import ./group.bend as G
import ./inode.bend as N
import ./patch.bend as P
import ./bitmap.bend as BM
import ./meta.bend as T
import ./inodew.bend as IW
import ./extentw.bend as EW
import ./dirw.bend as DW
import ./fsck.bend as FK
import ./extent.bend as X2
import ./ext2.bend as X

type Ext2MkfsFeatures is Data:
  Ext2MkfsFeatures{sparse_super: Bool, filetype: Bool, large_file: Bool, extents: Bool, wide: Bool, metadata_csum: Bool, dir_nlink: Bool, extra_isize: Bool}

# plain ext2: sparse_super, filetype, large_file
def Ext2MkfsFeatures.ext2() -> Ext2MkfsFeatures:
  Ext2MkfsFeatures{True{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}}

# ext4 without a journal: ext2's, and extent, 64bit, metadata_csum,
# dir_nlink, extra_isize
def Ext2MkfsFeatures.ext4() -> Ext2MkfsFeatures:
  Ext2MkfsFeatures{True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}}

# What to make:
#   blocks            the filesystem's size in blocks (the pure device
#                     interface has no size, so it is given)
#   log_block         the block size, 1024 << log_block (0 to 5: 1 to 32 KiB)
#   inode_size        bytes per inode (a power of two from 128 to the block)
#   inode_ratio       bytes of filesystem per inode
#   blocks_per_group  0 for the most a bitmap block holds (8 * block size)
#   reserved_percent  blocks reserved for the superuser (s_r_blocks_count)
#   features, uuid, label, time
#   zero              write zeros over the inode tables (unneeded on a
#                     device that reads as zeros, such as MemDev.blank)
type Ext2MkfsOptions is Data:
  Ext2MkfsOptions{blocks: Nat, log_block: Nat, inode_size: Nat, inode_ratio: Nat, blocks_per_group: Nat, reserved_percent: Nat, features: Ext2MkfsFeatures, uuid: U.Uuid, label: B.Octets, time: U32, zero: Bool}

# ext2 of blocks blocks of 1 KiB, an inode per 4 KiB, 256-byte inodes
def Ext2MkfsOptions.ext2(blocks: Nat, uuid: U.Uuid) -> Ext2MkfsOptions:
  Ext2MkfsOptions{blocks, 0n, 256n, 4096n, 0n, 5n, Ext2MkfsFeatures.ext2(), uuid, B.Octets.empty(), 0, True{}}

# ext4 (no journal) of blocks blocks of 4 KiB, an inode per 16 KiB
def Ext2MkfsOptions.ext4(blocks: Nat, uuid: U.Uuid) -> Ext2MkfsOptions:
  Ext2MkfsOptions{blocks, 2n, 256n, 16384n, 0n, 5n, Ext2MkfsFeatures.ext4(), uuid, B.Octets.empty(), 0, True{}}

def Ext2MkfsOptions.with_block(o: Ext2MkfsOptions, v: Nat) -> Ext2MkfsOptions:
  match o:
    case Ext2MkfsOptions{n, l, i, r, g, p, f, u, b, t, z}:
      Ext2MkfsOptions{n, v, i, r, g, p, f, u, b, t, z}

def Ext2MkfsOptions.with_inodes(o: Ext2MkfsOptions, size: Nat, ratio: Nat) -> Ext2MkfsOptions:
  match o:
    case Ext2MkfsOptions{n, l, i, r, g, p, f, u, b, t, z}:
      Ext2MkfsOptions{n, l, size, ratio, g, p, f, u, b, t, z}

def Ext2MkfsOptions.with_group(o: Ext2MkfsOptions, v: Nat) -> Ext2MkfsOptions:
  match o:
    case Ext2MkfsOptions{n, l, i, r, g, p, f, u, b, t, z}:
      Ext2MkfsOptions{n, l, i, r, v, p, f, u, b, t, z}

def Ext2MkfsOptions.with_features(o: Ext2MkfsOptions, v: Ext2MkfsFeatures) -> Ext2MkfsOptions:
  match o:
    case Ext2MkfsOptions{n, l, i, r, g, p, f, u, b, t, z}:
      Ext2MkfsOptions{n, l, i, r, g, p, v, u, b, t, z}

def Ext2MkfsOptions.with_label(o: Ext2MkfsOptions, v: B.Octets) -> Ext2MkfsOptions:
  match o:
    case Ext2MkfsOptions{n, l, i, r, g, p, f, u, b, t, z}:
      Ext2MkfsOptions{n, l, i, r, g, p, f, u, v, t, z}

def Ext2MkfsOptions.with_time(o: Ext2MkfsOptions, v: U32) -> Ext2MkfsOptions:
  match o:
    case Ext2MkfsOptions{n, l, i, r, g, p, f, u, b, t, z}:
      Ext2MkfsOptions{n, l, i, r, g, p, f, u, b, v, z}

def Ext2MkfsOptions.with_zero(o: Ext2MkfsOptions, v: Bool) -> Ext2MkfsOptions:
  match o:
    case Ext2MkfsOptions{n, l, i, r, g, p, f, u, b, t, z}:
      Ext2MkfsOptions{n, l, i, r, g, p, f, u, b, t, v}

def Ext2MkfsOptions.with_reserved(o: Ext2MkfsOptions, v: Nat) -> Ext2MkfsOptions:
  match o:
    case Ext2MkfsOptions{n, l, i, r, g, p, f, u, b, t, z}:
      Ext2MkfsOptions{n, l, i, r, g, v, f, u, b, t, z}

# The geometry a filesystem is laid out by
type Ext2Geo is Data:
  Ext2Geo{bs: Nat, log: Nat, blocks: Nat, first: Nat, bpg: Nat, groups: Nat, ipg: Nat, isz: Nat, ds: Nat, gdt: Nat, itb: Nat, sparse: Bool}

def Ext2Geo.bs(x: Ext2Geo) -> Nat:
  match x:
    case Ext2Geo{a, b, c, e, f, g, h, i, j, k, l, m}:
      a

def Ext2Geo.log(x: Ext2Geo) -> Nat:
  match x:
    case Ext2Geo{a, b, c, e, f, g, h, i, j, k, l, m}:
      b

def Ext2Geo.blocks(x: Ext2Geo) -> Nat:
  match x:
    case Ext2Geo{a, b, c, e, f, g, h, i, j, k, l, m}:
      c

def Ext2Geo.first(x: Ext2Geo) -> Nat:
  match x:
    case Ext2Geo{a, b, c, e, f, g, h, i, j, k, l, m}:
      e

def Ext2Geo.bpg(x: Ext2Geo) -> Nat:
  match x:
    case Ext2Geo{a, b, c, e, f, g, h, i, j, k, l, m}:
      f

def Ext2Geo.groups(x: Ext2Geo) -> Nat:
  match x:
    case Ext2Geo{a, b, c, e, f, g, h, i, j, k, l, m}:
      g

def Ext2Geo.ipg(x: Ext2Geo) -> Nat:
  match x:
    case Ext2Geo{a, b, c, e, f, g, h, i, j, k, l, m}:
      h

def Ext2Geo.isz(x: Ext2Geo) -> Nat:
  match x:
    case Ext2Geo{a, b, c, e, f, g, h, i, j, k, l, m}:
      i

def Ext2Geo.ds(x: Ext2Geo) -> Nat:
  match x:
    case Ext2Geo{a, b, c, e, f, g, h, i, j, k, l, m}:
      j

def Ext2Geo.gdt(x: Ext2Geo) -> Nat:
  match x:
    case Ext2Geo{a, b, c, e, f, g, h, i, j, k, l, m}:
      k

def Ext2Geo.itb(x: Ext2Geo) -> Nat:
  match x:
    case Ext2Geo{a, b, c, e, f, g, h, i, j, k, l, m}:
      l

def Ext2Geo.sparse(x: Ext2Geo) -> Bool:
  match x:
    case Ext2Geo{a, b, c, e, f, g, h, i, j, k, l, m}:
      m

def Ext2MkfsOptions.features(o: Ext2MkfsOptions) -> Ext2MkfsFeatures:
  match o:
    case Ext2MkfsOptions{n, l, i, r, g, p, f, u, b, t, z}:
      f

def Ext2MkfsOptions.uuid(o: Ext2MkfsOptions) -> U.Uuid:
  match o:
    case Ext2MkfsOptions{n, l, i, r, g, p, f, u, b, t, z}:
      u

def Ext2MkfsOptions.label(o: Ext2MkfsOptions) -> B.Octets:
  match o:
    case Ext2MkfsOptions{n, l, i, r, g, p, f, u, b, t, z}:
      b

def Ext2MkfsOptions.time(o: Ext2MkfsOptions) -> U32:
  match o:
    case Ext2MkfsOptions{n, l, i, r, g, p, f, u, b, t, z}:
      t

def Ext2MkfsOptions.zero(o: Ext2MkfsOptions) -> Bool:
  match o:
    case Ext2MkfsOptions{n, l, i, r, g, p, f, u, b, t, z}:
      z

def Ext2MkfsOptions.reserved(o: Ext2MkfsOptions) -> Nat:
  match o:
    case Ext2MkfsOptions{n, l, i, r, g, p, f, u, b, t, z}:
      p

def Ext2MkfsFeatures.wide(f: Ext2MkfsFeatures) -> Bool:
  match f:
    case Ext2MkfsFeatures{s, ft, lf, x, w, c, dn, ei}:
      w

def Ext2MkfsFeatures.extents(f: Ext2MkfsFeatures) -> Bool:
  match f:
    case Ext2MkfsFeatures{s, ft, lf, x, w, c, dn, ei}:
      x

def Ext2MkfsFeatures.csum(f: Ext2MkfsFeatures) -> Bool:
  match f:
    case Ext2MkfsFeatures{s, ft, lf, x, w, c, dn, ei}:
      c

def Ext2MkfsFeatures.sparse(f: Ext2MkfsFeatures) -> Bool:
  match f:
    case Ext2MkfsFeatures{s, ft, lf, x, w, c, dn, ei}:
      s

def Ext2Mkfs.bit(b: Bool, v: U32) -> U32:
  match b:
    case True{}:
      v
    case False{}:
      0

def Ext2Mkfs.incompat(f: Ext2MkfsFeatures) -> U32:
  match f:
    case Ext2MkfsFeatures{s, ft, lf, x, w, c, dn, ei}:
      U32.or(Ext2Mkfs.bit(ft, 2), U32.or(Ext2Mkfs.bit(x, 64), Ext2Mkfs.bit(w, 128)))

def Ext2Mkfs.ro_compat(f: Ext2MkfsFeatures) -> U32:
  match f:
    case Ext2MkfsFeatures{s, ft, lf, x, w, c, dn, ei}:
      U32.or(Ext2Mkfs.bit(s, 1), U32.or(Ext2Mkfs.bit(lf, 2), U32.or(Ext2Mkfs.bit(dn, 32), U32.or(Ext2Mkfs.bit(ei, 64), Ext2Mkfs.bit(c, 1024)))))

# Geometry

def Ext2Mkfs.flag(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def Ext2Mkfs.up(+n: Nat, +m: Nat) -> Nat:
  Nat.mul(Nat.div(Nat.add(n, Nat.sub(m, 1n)), m), m)

def Ext2Mkfs.ceil(+n: Nat, +m: Nat) -> Nat:
  Nat.div(Nat.add(n, Nat.sub(m, 1n)), m)

def Ext2Mkfs.pick(z: Bool, +a: Nat, +b: Nat) -> Nat:
  match z:
    case True{}:
      a
    case False{}:
      b

# the layout of blocks blocks with these options
# the inodes a ratio gives: blocks * bs / ratio, without forming the
# product (ratio and bs are powers of two in practice)
def Ext2Mkfs.per_ratio(big: Bool, +blocks: Nat, +bs: Nat, +ratio: Nat) -> Nat:
  match big:
    case True{}:
      Nat.div(blocks, Nat.max(1n, Nat.div(ratio, bs)))
    case False{}:
      Nat.mul(blocks, Nat.div(bs, ratio))

def Ext2Mkfs.geo.make(o: Ext2MkfsOptions, +blocks: Nat) -> Ext2Geo:
  match o:
    case Ext2MkfsOptions{n, +l, +isz, +ratio, +g, p, +f, u, b, t, z}:
      +bs = Nat.mul(1024n, Nat.pow(2n, l))
      +first = Ext2Mkfs.flag(Nat.is_eq(bs, 1024n))
      +bpg = Ext2Mkfs.pick(Nat.is_eq(g, 0n), Nat.mul(8n, bs), g)
      +groups = Ext2Mkfs.ceil(Nat.sub(blocks, first), bpg)
      +total = Nat.max(16n, Ext2Mkfs.per_ratio(Nat.is_le(bs, ratio), blocks, bs, ratio))
      +m = Nat.max(8n, Nat.div(bs, isz))
      +ipg = Nat.min(Ext2Mkfs.up(Ext2Mkfs.ceil(total, groups), m), Nat.mul(8n, bs))
      +ds = Ext2Mkfs.pick(Ext2MkfsFeatures.wide(f), 64n, 32n)
      Ext2Geo{bs, l, blocks, first, bpg, groups, ipg, isz, ds, Ext2Mkfs.ceil(Nat.mul(groups, ds), bs), Nat.div(Nat.mul(ipg, isz), bs), Ext2MkfsFeatures.sparse(f)}

def Ext2Mkfs.has_super(+geo: Ext2Geo, +g: Nat) -> Bool:
  Bool.or(Bool.not(Ext2Geo.sparse(geo)), G.Ext2Group.sparse(g))

def Ext2Mkfs.lead(+geo: Ext2Geo, +g: Nat) -> Nat:
  Nat.mul(Ext2Mkfs.flag(Ext2Mkfs.has_super(geo, g)), Nat.add(1n, Ext2Geo.gdt(geo)))

# the blocks of group g its metadata takes: superblock and descriptor copy,
# bitmaps, inode table
def Ext2Mkfs.overhead(+geo: Ext2Geo, +g: Nat) -> Nat:
  Nat.add(Ext2Mkfs.lead(geo, g), Nat.add(2n, Ext2Geo.itb(geo)))

def Ext2Mkfs.group_first(+geo: Ext2Geo, +g: Nat) -> Nat:
  Nat.add(Ext2Geo.first(geo), Nat.mul(g, Ext2Geo.bpg(geo)))

def Ext2Mkfs.group_size(+geo: Ext2Geo, +g: Nat) -> Nat:
  Nat.min(Ext2Geo.bpg(geo), Nat.sub(Ext2Geo.blocks(geo), Ext2Mkfs.group_first(geo, g)))

# the blocks of group g in use: its metadata, and in group 0 the root's and
# lost+found's blocks
def Ext2Mkfs.used_blocks(+geo: Ext2Geo, +g: Nat) -> Nat:
  Nat.add(Ext2Mkfs.overhead(geo, g), Nat.mul(2n, Ext2Mkfs.flag(Nat.is_eq(g, 0n))))

def Ext2Mkfs.used_inodes(+g: Nat) -> Nat:
  Nat.mul(11n, Ext2Mkfs.flag(Nat.is_eq(g, 0n)))

def Ext2Mkfs.last_fits(+geo: Ext2Geo) -> Bool:
  +last = Nat.sub(Ext2Geo.groups(geo), 1n)
  Nat.is_lt(Ext2Mkfs.used_blocks(geo, last), Ext2Mkfs.group_size(geo, last))

def Ext2Mkfs.geo.fit(fits: Bool, +o: Ext2MkfsOptions, +geo: Ext2Geo) -> Ext2Geo:
  match fits:
    case True{}:
      geo
    case False{}:
      Ext2Mkfs.geo.make(o, Ext2Mkfs.group_first(geo, Nat.sub(Ext2Geo.groups(geo), 1n)))

def Ext2Mkfs.is_pow2.go(n: Nat, +x: Nat, +p: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+k:
      Bool.or(Nat.is_eq(x, p), Ext2Mkfs.is_pow2.go(k, x, Nat.mul(p, 2n)))

def Ext2Mkfs.opts_ok(o: Ext2MkfsOptions) -> Result<&2, &2, E.Ext2Error, Unit>:
  match o:
    case Ext2MkfsOptions{+n, +l, +isz, +ratio, +g, +p, f, u, b, t, z}:
      +bs = Nat.mul(1024n, Nat.pow(2n, l))
      do Result<&2, &2, E.Ext2Error, Unit>:
        S.Ext2.require(Nat.is_le(l, 5n), E.Ext2BadMkfs{"a block size over 32 KiB"})
        S.Ext2.require(Bool.and(Ext2Mkfs.is_pow2.go(17n, isz, 1n), Bool.and(Nat.is_le(128n, isz), Nat.is_le(isz, bs))), E.Ext2BadMkfs{"an inode size that is not a power of two from 128 to the block size"})
        S.Ext2.require(Bool.or(Nat.is_eq(g, 0n), Bool.and(Nat.is_eq(Nat.mod(g, 8n), 0n), Bool.and(Nat.is_le(8n, g), Nat.is_le(g, Nat.mul(8n, bs))))), E.Ext2BadMkfs{"blocks per group: a multiple of 8, at most 8 times the block size"})
        S.Ext2.require(Nat.is_le(isz, ratio), E.Ext2BadMkfs{"fewer bytes per inode than an inode takes"})
        S.Ext2.require(Nat.is_lt(p, 50n), E.Ext2BadMkfs{"half the blocks or more reserved"})
        S.Ext2.require(Nat.is_le(10n, n), E.Ext2BadMkfs{"too few blocks"})

def Ext2Mkfs.geo_ok(+geo: Ext2Geo) -> Result<&2, &2, E.Ext2Error, Ext2Geo>:
  do Result<&2, &2, E.Ext2Error, Ext2Geo>:
    S.Ext2.require(Nat.is_lt(0n, Ext2Geo.groups(geo)), E.Ext2BadMkfs{"too few blocks"})
    S.Ext2.require(Nat.is_lt(Ext2Mkfs.used_blocks(geo, 0n), Ext2Mkfs.group_size(geo, 0n)), E.Ext2BadMkfs{"too few blocks for the first group's metadata"})
    S.Ext2.require(Ext2Mkfs.last_fits(geo), E.Ext2BadMkfs{"too few blocks for the last group's metadata"})
    S.Ext2.require(Nat.is_le(16n, Ext2Geo.ipg(geo)), E.Ext2BadMkfs{"fewer than 16 inodes per group"})
    S.Ext2.require(Nat.is_eq(Nat.div(Nat.div(Nat.mul(Ext2Geo.groups(geo), Ext2Geo.ipg(geo)), 65536n), 65536n), 0n), E.Ext2BadMkfs{"2^32 inodes or more"})
    return geo

# the layout of the filesystem: as many groups as the blocks make, the last
# dropped (and its blocks left out) when its metadata would not fit in it
def Ext2Mkfs.geometry(+o: Ext2MkfsOptions) -> Result<&2, &2, E.Ext2Error, Ext2Geo>:
  match o:
    case Ext2MkfsOptions{+n, l, i, r, g, p, f, u, b, t, z}:
      do Result<&2, &2, E.Ext2Error, Ext2Geo>:
        Ext2Mkfs.opts_ok(o)
        +geo0 : Ext2Geo = Ext2Mkfs.geo.make(o, n)
        Ext2Mkfs.geo_ok(Ext2Mkfs.geo.fit(Bool.or(Nat.is_le(Ext2Geo.groups(geo0), 1n), Ext2Mkfs.last_fits(geo0)), o, geo0))

# Records

# a field to write: its offset, its width (1, 2 or 4 bytes) and its value
type Ext2Put is Data:
  Ext2Put{off: Nat, width: Nat, v: U32}

def Ext2Mkfs.put.one(+o: B.Octets, w: Nat, +off: Nat, v: U32) -> B.Octets:
  match w:
    case 1n:
      P.Ext2Patch.u8(o, off, v)
    case 2n:
      P.Ext2Patch.u16(o, off, v)
    case _:
      P.Ext2Patch.u32(o, off, v)

def Ext2Mkfs.put(ps: List<&2, Ext2Put>, +o: B.Octets) -> B.Octets:
  match ps:
    case Nil{}:
      o
    case Con{Ext2Put{off, w, v}, t}:
      Ext2Mkfs.put(t, Ext2Mkfs.put.one(o, w, off, v))

def Ext2Mkfs.lo(+n: Nat) -> U32:
  P.Ext2Patch.lo32(n)

def Ext2Mkfs.hi(+n: Nat) -> U32:
  P.Ext2Patch.hi32(n)

# the superblock (1024 bytes, checksum set) of group g's copy, with the
# free counts fb and fi
def Ext2Mkfs.super.counts(+geo: Ext2Geo, +fb: Nat, +fi: Nat, +rb: Nat, +log: U32, +bpg: U32) -> List<&2, Ext2Put>:
  +blocks = Ext2Geo.blocks(geo)
  [Ext2Put{0n, 4n, U32.from_nat(Nat.mul(Ext2Geo.groups(geo), Ext2Geo.ipg(geo)))}, Ext2Put{4n, 4n, Ext2Mkfs.lo(blocks)}, Ext2Put{8n, 4n, Ext2Mkfs.lo(rb)}, Ext2Put{12n, 4n, Ext2Mkfs.lo(fb)}, Ext2Put{16n, 4n, U32.from_nat(fi)}, Ext2Put{20n, 4n, U32.from_nat(Ext2Geo.first(geo))}, Ext2Put{24n, 4n, log}, Ext2Put{28n, 4n, log}, Ext2Put{32n, 4n, bpg}, Ext2Put{36n, 4n, bpg}, Ext2Put{40n, 4n, U32.from_nat(Ext2Geo.ipg(geo))}]

def Ext2Mkfs.super.state(+t: U32, +isz: Nat, +g: Nat) -> List<&2, Ext2Put>:
  [Ext2Put{48n, 4n, t}, Ext2Put{54n, 2n, 65535}, Ext2Put{56n, 2n, 61267}, Ext2Put{58n, 2n, 1}, Ext2Put{60n, 2n, 1}, Ext2Put{64n, 4n, t}, Ext2Put{76n, 4n, 1}, Ext2Put{84n, 4n, 11}, Ext2Put{88n, 2n, U32.from_nat(isz)}, Ext2Put{90n, 2n, U32.from_nat(g)}, Ext2Put{264n, 4n, t}]

def Ext2Mkfs.super.features(+f: Ext2MkfsFeatures, +geo: Ext2Geo, +fb: Nat, +rb: Nat) -> List<&2, Ext2Put>:
  +whi = U32.from_nat(Ext2Mkfs.flag(Ext2MkfsFeatures.wide(f)))
  +extra = U32.from_nat(Nat.mul(32n, Ext2Mkfs.flag(Nat.is_lt(128n, Ext2Geo.isz(geo)))))
  [Ext2Put{96n, 4n, Ext2Mkfs.incompat(f)}, Ext2Put{100n, 4n, Ext2Mkfs.ro_compat(f)}, Ext2Put{254n, 2n, U32.mul(64, whi)}, Ext2Put{336n, 4n, U32.mul(whi, Ext2Mkfs.hi(Ext2Geo.blocks(geo)))}, Ext2Put{340n, 4n, U32.mul(whi, Ext2Mkfs.hi(rb))}, Ext2Put{344n, 4n, U32.mul(whi, Ext2Mkfs.hi(fb))}, Ext2Put{348n, 2n, extra}, Ext2Put{350n, 2n, extra}, Ext2Put{373n, 1n, Ext2Mkfs.bit(Ext2MkfsFeatures.csum(f), 1)}]

# the superblock (1024 bytes, checksum set) of group g's copy, with the
# free counts fb and fi
def Ext2Mkfs.super(+o: Ext2MkfsOptions, +geo: Ext2Geo, +fb: Nat, +fi: Nat, +g: Nat) -> B.Octets:
  +rb = Nat.div(Nat.mul(Ext2Geo.blocks(geo), Ext2MkfsOptions.reserved(o)), 100n)
  +r0 = Ext2Mkfs.put(Ext2Mkfs.super.counts(geo, fb, fi, rb, U32.from_nat(Ext2Geo.log(geo)), U32.from_nat(Ext2Geo.bpg(geo))), B.Octets.zeros(1024n))
  +r1 = Ext2Mkfs.put(Ext2Mkfs.super.state(Ext2MkfsOptions.time(o), Ext2Geo.isz(geo), g), r0)
  +r2 = Ext2Mkfs.put(Ext2Mkfs.super.features(Ext2MkfsOptions.features(o), geo, fb, rb), r1)
  +named = P.Ext2Patch.bytes(P.Ext2Patch.bytes(r2, 104n, U.Uuid.to_bytes(Ext2MkfsOptions.uuid(o))), 120n, B.Octets.take(16n, B.Octets.append(Ext2MkfsOptions.label(o), B.Octets.zeros(16n))))
  T.Ext2Meta.super_csum(named)

# group g's block and inode bitmaps
def Ext2Mkfs.block_bitmap(+geo: Ext2Geo, +g: Nat) -> B.Octets:
  BM.Ext2Bitmap.make(Ext2Geo.bs(geo), Ext2Mkfs.used_blocks(geo, g), Ext2Mkfs.group_size(geo, g))

def Ext2Mkfs.inode_bitmap(+geo: Ext2Geo, +g: Nat) -> B.Octets:
  BM.Ext2Bitmap.make(Ext2Geo.bs(geo), Ext2Mkfs.used_inodes(g), Ext2Geo.ipg(geo))

def Ext2Mkfs.bb(+geo: Ext2Geo, +g: Nat) -> Nat:
  Nat.add(Ext2Mkfs.group_first(geo, g), Ext2Mkfs.lead(geo, g))

def Ext2Mkfs.free_blocks(+geo: Ext2Geo, +g: Nat) -> Nat:
  Nat.sub(Ext2Mkfs.group_size(geo, g), Ext2Mkfs.used_blocks(geo, g))

def Ext2Mkfs.free_inodes(+geo: Ext2Geo, +g: Nat) -> Nat:
  Nat.sub(Ext2Geo.ipg(geo), Ext2Mkfs.used_inodes(g))

def Ext2Mkfs.wide.pick(w: Bool, ps: List<&2, Ext2Put>, more: List<&2, Ext2Put>) -> List<&2, Ext2Put>:
  match w:
    case True{}:
      List.append(&2, Ext2Put, ps, more)
    case False{}:
      ps

# group g's descriptor (fs: the filesystem the superblock describes, for the
# checksums)
def Ext2Mkfs.desc(+o: Ext2MkfsOptions, +geo: Ext2Geo, +fs: S.Ext2Fs, +g: Nat) -> B.Octets:
  +csum = Ext2MkfsFeatures.csum(Ext2MkfsOptions.features(o))
  +bb = Ext2Mkfs.bb(geo, g)
  +fb = U32.from_nat(Ext2Mkfs.free_blocks(geo, g))
  +fi = U32.from_nat(Ext2Mkfs.free_inodes(geo, g))
  +ipg = Ext2Geo.ipg(geo)
  +bcs = T.Ext2Meta.bitmap_csum(fs, Ext2Mkfs.block_bitmap(geo, g), Nat.div(Ext2Geo.bpg(geo), 8n))
  +ics = T.Ext2Meta.bitmap_csum(fs, Ext2Mkfs.inode_bitmap(geo, g), Nat.div(ipg, 8n))
  +ps = {[Ext2Put{0n, 4n, U32.from_nat(bb)}, Ext2Put{4n, 4n, U32.from_nat(Nat.add(bb, 1n))}, Ext2Put{8n, 4n, U32.from_nat(Nat.add(bb, 2n))}, Ext2Put{12n, 2n, U32.and(65535, fb)}, Ext2Put{14n, 2n, U32.and(65535, fi)}, Ext2Put{16n, 2n, U32.mul(2, Ext2Mkfs.bit(Nat.is_eq(g, 0n), 1))}, Ext2Put{18n, 2n, 4}, Ext2Put{24n, 2n, U32.and(65535, U32.mul(Ext2Mkfs.bit(csum, 1), bcs))}, Ext2Put{26n, 2n, U32.and(65535, U32.mul(Ext2Mkfs.bit(csum, 1), ics))}, Ext2Put{28n, 2n, U32.mul(Ext2Mkfs.bit(csum, 1), U32.from_nat(Nat.sub(ipg, Ext2Mkfs.used_inodes(g))))}] : List<&2, Ext2Put>}
  +wide = {[Ext2Put{44n, 2n, U32.shrn(fb, 16n)}, Ext2Put{46n, 2n, U32.shrn(fi, 16n)}, Ext2Put{56n, 2n, U32.mul(Ext2Mkfs.bit(csum, 1), U32.shrn(bcs, 16n))}, Ext2Put{58n, 2n, U32.mul(Ext2Mkfs.bit(csum, 1), U32.shrn(ics, 16n))}] : List<&2, Ext2Put>}
  +raw = Ext2Mkfs.put(Ext2Mkfs.wide.pick(Nat.is_le(64n, Ext2Geo.ds(geo)), ps, wide), B.Octets.zeros(Ext2Geo.ds(geo)))
  T.Ext2Meta.desc_csum(fs, g, raw)

def Ext2Mkfs.descs(n: Nat, +o: Ext2MkfsOptions, +geo: Ext2Geo, +fs: S.Ext2Fs, +g: Nat, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match n:
    case 0n:
      List.reverse(&2, B.Octets, acc)
    case 1n+k:
      Ext2Mkfs.descs(k, o, geo, fs, Nat.add(g, 1n), Con{Ext2Mkfs.desc(o, geo, fs, g), acc})

# the descriptor table's blocks
def Ext2Mkfs.gdt(+o: Ext2MkfsOptions, +geo: Ext2Geo, +fs: S.Ext2Fs) -> B.Octets:
  +table = B.Octets.concat(Ext2Mkfs.descs(Ext2Geo.groups(geo), o, geo, fs, 0n, Nil{}))
  B.Octets.append(table, B.Octets.zeros(Nat.sub(Nat.mul(Ext2Geo.gdt(geo), Ext2Geo.bs(geo)), B.Octets.len(table))))

def Ext2Mkfs.sums.go(n: Nat, +geo: Ext2Geo, +g: Nat, b: Nat, i: Nat) -> FK.Ext2Sums:
  match n:
    case 0n:
      FK.Ext2Sums{b, i}
    case 1n+k:
      Ext2Mkfs.sums.go(k, geo, Nat.add(g, 1n), Nat.add(b, Ext2Mkfs.free_blocks(geo, g)), Nat.add(i, Ext2Mkfs.free_inodes(geo, g)))

# the free blocks and inodes of the whole filesystem
def Ext2Mkfs.sums(+geo: Ext2Geo) -> FK.Ext2Sums:
  Ext2Mkfs.sums.go(Ext2Geo.groups(geo), geo, 0n, 0n, 0n)

# Writing it

def Ext2Mkfs.zeros.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, n: Nat, r: Result<&2, &2, E.Ext2Error, Dv>, +fs: S.Ext2Fs, +b: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  match n r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{d}:
      Done{d}
    case 1n+k Done{+d}:
      Ext2Mkfs.zeros.go(~Dv, ~block_size, ~read_block, ~write_block, k, T.Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d, fs, b, B.Octets.zeros(S.Ext2Fs.block_size(fs))), fs, Nat.add(b, 1n))

# n zero blocks from block b (when zero is on)
def Ext2Mkfs.zeros(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, zero: Bool, +d: Dv, +fs: S.Ext2Fs, +b: Nat, +n: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  match zero:
    case True{}:
      Ext2Mkfs.zeros.go(~Dv, ~block_size, ~read_block, ~write_block, n, Done{d}, fs, b)
    case False{}:
      Done{d}

# group g's superblock and descriptor copies (group 0's are the primary
# ones, written apart)
def Ext2Mkfs.copies(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, has: Bool, +d: Dv, +fs: S.Ext2Fs, +o: Ext2MkfsOptions, +geo: Ext2Geo, +gdt: B.Octets, +g: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  match has:
    case False{}:
      Done{d}
    case True{}:
      +base = Ext2Mkfs.group_first(geo, g)
      +bs = Ext2Geo.bs(geo)
      +sums = Ext2Mkfs.sums(geo)
      do Result<&2, &2, E.Ext2Error, Dv>:
        d1 : Dv <- T.Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d, fs, base, B.Octets.append(Ext2Mkfs.super(o, geo, FK.Ext2Sums.blocks(sums), FK.Ext2Sums.inodes(sums), g), B.Octets.zeros(Nat.sub(bs, 1024n))))
        T.Ext2Dev.write_bytes(~Dv, ~block_size, ~read_block, ~write_block, d1, Nat.mul(Nat.add(base, 1n), bs), gdt)

# group g written: its copies, bitmaps and (zeroed) inode table
def Ext2Mkfs.group(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +o: Ext2MkfsOptions, +geo: Ext2Geo, +gdt: B.Octets, +g: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  +bb = Ext2Mkfs.bb(geo, g)
  do Result<&2, &2, E.Ext2Error, Dv>:
    d1 : Dv <- Ext2Mkfs.copies(~Dv, ~block_size, ~read_block, ~write_block, Bool.and(Ext2Mkfs.has_super(geo, g), Nat.is_lt(0n, g)), d, fs, o, geo, gdt, g)
    d2 : Dv <- T.Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d1, fs, bb, Ext2Mkfs.block_bitmap(geo, g))
    d3 : Dv <- T.Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, Nat.add(bb, 1n), Ext2Mkfs.inode_bitmap(geo, g))
    Ext2Mkfs.zeros(~Dv, ~block_size, ~read_block, ~write_block, Ext2MkfsOptions.zero(o), d3, fs, Nat.add(bb, 2n), Ext2Geo.itb(geo))

def Ext2Mkfs.groups(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, n: Nat, r: Result<&2, &2, E.Ext2Error, Dv>, +fs: S.Ext2Fs, +o: Ext2MkfsOptions, +geo: Ext2Geo, +gdt: B.Octets, +g: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  match n r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{d}:
      Done{d}
    case 1n+k Done{+d}:
      Ext2Mkfs.groups(~Dv, ~block_size, ~read_block, ~write_block, k, Ext2Mkfs.group(~Dv, ~block_size, ~read_block, ~write_block, d, fs, o, geo, gdt, g), fs, o, geo, gdt, Nat.add(g, 1n))

# The root directory, lost+found and the reserved inodes

def Ext2Mkfs.map_of(ext: Bool, +b: Nat) -> B.Octets:
  match ext:
    case True{}:
      EW.Ext2ExtW.node([X2.Ext2Extent{0n, 1n, b, True{}}], 4n, 0n)
    case False{}:
      P.Ext2Patch.u32(B.Octets.zeros(60n), 0n, U32.from_nat(b))

# a directory of one block b: its record
def Ext2Mkfs.dir_record(+fs: S.Ext2Fs, +o: Ext2MkfsOptions, +mode: U32, +links: U32, +b: Nat) -> B.Octets:
  +ext = Ext2MkfsFeatures.extents(Ext2MkfsOptions.features(o))
  +bs = S.Ext2Fs.block_size(fs)
  +flags = Ext2Mkfs.bit(ext, N.Ext2Inode.flag_extents())
  IW.Ext2IRaw.set_blocks(IW.Ext2IRaw.set_size(IW.Ext2InodeW.fresh(fs, mode, 0, 0, Ext2MkfsOptions.time(o), links, flags, Ext2Mkfs.map_of(ext, b)), bs), Nat.div(bs, 512n))

def Ext2Mkfs.reserved.one(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, root: Bool, +d: Dv, +fs: S.Ext2Fs, +raw: B.Octets, +ino: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  match root:
    case True{}:
      Done{d}
    case False{}:
      IW.Ext2InodeW.write_raw(~Dv, ~block_size, ~read_block, ~write_block, d, fs, ino, raw)

def Ext2Mkfs.reserved.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, n: Nat, r: Result<&2, &2, E.Ext2Error, Dv>, +fs: S.Ext2Fs, +raw: B.Octets, +ino: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  match n r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{d}:
      Done{d}
    case 1n+k Done{+d}:
      Ext2Mkfs.reserved.go(~Dv, ~block_size, ~read_block, ~write_block, k, Ext2Mkfs.reserved.one(~Dv, ~block_size, ~read_block, ~write_block, Nat.is_eq(ino, 2n), d, fs, raw, ino), fs, raw, Nat.add(ino, 1n))

# the root (inode 2) and lost+found (inode 11), in the first two blocks
# after group 0's metadata, and the other reserved inodes (1, 3 to 10)
def Ext2Mkfs.tree(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +o: Ext2MkfsOptions, +geo: Ext2Geo) -> Result<&2, &2, E.Ext2Error, Dv>:
  +root = Nat.add(Ext2Mkfs.group_first(geo, 0n), Ext2Mkfs.overhead(geo, 0n))
  +lf = Nat.add(root, 1n)
  +dt = DW.Ext2DirW.ftype(fs, 2)
  +t = Ext2MkfsOptions.time(o)
  +rootblk = DW.Ext2DirW.block_bytes(fs, 2n, 0, [DW.Ext2Slot{2, 12n, dt, B.Octets.of_string(".")}, DW.Ext2Slot{2, 12n, dt, B.Octets.of_string("..")}, DW.Ext2Slot{11, Nat.sub(DW.Ext2DirW.limit(fs), 24n), dt, B.Octets.of_string("lost+found")}])
  +blank = P.Ext2Patch.u32(P.Ext2Patch.u32(P.Ext2Patch.u32(B.Octets.zeros(S.Ext2Fs.inode_size(fs)), 8n, t), 12n, t), 16n, t)
  do Result<&2, &2, E.Ext2Error, Dv>:
    d1 : Dv <- T.Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d, fs, root, rootblk)
    d2 : Dv <- T.Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d1, fs, lf, DW.Ext2DirW.first_block(fs, 11n, 0, 2n))
    d3 : Dv <- IW.Ext2InodeW.write_raw(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, 2n, Ext2Mkfs.dir_record(fs, o, 16877, 3, root))
    d4 : Dv <- IW.Ext2InodeW.write_raw(~Dv, ~block_size, ~read_block, ~write_block, d3, fs, 11n, Ext2Mkfs.dir_record(fs, o, 16832, 2, lf))
    Ext2Mkfs.reserved.go(~Dv, ~block_size, ~read_block, ~write_block, 10n, Done{d4}, fs, blank, 1n)

# a new filesystem checked: it opens with the reader's default options and
# passes Ext2Fsck.full
def Ext2Mkfs.check(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv) -> Result<&2, &2, E.Ext2Error, Unit>:
  Result.bind(&2, &2, E.Ext2Error, S.Ext2Fs, Unit, X.Ext2.open(~Dv, ~block_size, ~read_block, d, O.Ext2Options.default()), fs => FK.Ext2Fsck.full(~Dv, ~block_size, ~read_block, d, fs))

def Ext2Mkfs.confirm(-Dv: Data, p: Result<&2, &2, E.Ext2Error, Unit>, d2: Dv) -> Result<&2, &2, E.Ext2Error, Dv>:
  match p:
    case Done{u}:
      Done{d2}
    case Fail{e}:
      Fail{e}

def Ext2Mkfs.checked(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, r: Result<&2, &2, E.Ext2Error, Dv>) -> Result<&2, &2, E.Ext2Error, Dv>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+d}:
      Ext2Mkfs.confirm(Dv, Ext2Mkfs.check(~Dv, ~block_size, ~read_block, d), d)

# the filesystem written, unchecked
def Ext2Mkfs.build(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +o: Ext2MkfsOptions) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    +geo : Ext2Geo <- Ext2Mkfs.geometry(o)
    +sums : FK.Ext2Sums = Ext2Mkfs.sums(geo)
    +sb : B.Octets = Ext2Mkfs.super(o, geo, FK.Ext2Sums.blocks(sums), FK.Ext2Sums.inodes(sums), 0n)
    +fs : S.Ext2Fs <- S.Ext2Fs.mount(O.Ext2Options.default(), sb)
    +gdt : B.Octets = Ext2Mkfs.gdt(o, geo, fs)
    d1 : Dv <- T.Ext2Meta.write_super(~Dv, ~block_size, ~read_block, ~write_block, d, sb)
    d2 : Dv <- T.Ext2Dev.write_bytes(~Dv, ~block_size, ~read_block, ~write_block, d1, Nat.mul(Nat.add(Ext2Geo.first(geo), 1n), Ext2Geo.bs(geo)), gdt)
    d3 : Dv <- Ext2Mkfs.groups(~Dv, ~block_size, ~read_block, ~write_block, Ext2Geo.groups(geo), Done{d2}, fs, o, geo, gdt, 0n)
    Ext2Mkfs.tree(~Dv, ~block_size, ~read_block, ~write_block, d3, fs, o, geo)

# a new filesystem on the device, as the options say; checked before it is
# answered: it opens with the reader's default options and passes
# Ext2Fsck.full (else Ext2CheckFailed, or the reader's error)
def Ext2Mkfs.make(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +o: Ext2MkfsOptions) -> Result<&2, &2, E.Ext2Error, Dv>:
  Ext2Mkfs.checked(~Dv, ~block_size, ~read_block, Ext2Mkfs.build(~Dv, ~block_size, ~read_block, ~write_block, d, o))
