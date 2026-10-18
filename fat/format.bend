# bend-osdev-fat, format.bend: making a new volume (mkfs): a boot sector
# and BPB for a given size and FAT type, the FATs, the root directory, and
# on FAT32 the FSInfo sector and the backup boot sector.
#
# Microsoft, "FAT: General Overview of On-Disk Format" (version 1.03, 2000),
# section 3 (the BPB, and 3.5: the type is fixed by the count of clusters),
# section 4 (entries 0 and 1 of the FAT: the media byte, and an end of
# chain), section 5 (FSInfo) and section 6 (the volume label entry).
#
# The size of each FAT: the specification's FATSz computation (section 3.5)
# generalised to every entry width and sector size, with room for the two
# reserved entries. For data sectors D (the volume less the reserved sectors
# and the root directory), b bits an entry, S bytes a sector, C sectors a
# cluster and N FATs,
#   FATSz = ceil((D + 2C) * b / (8 * S * C + b * N)),
# which for FAT16 and FAT32 at 512 bytes a sector is the specification's own
# formula with the two reserved entries added, and is what mkfs.fat writes
# (checked on its images). With that FATSz the FAT holds an entry for every
# cluster: 8 * S * FATSz >= b * (count of clusters + 2).
#
# Every layout is checked with the reader's own checks (bpb.bend's
# FatVolume.of_bpb) before it is answered, so a layout always mounts, as the
# type asked for.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./bpb.bend as P
import ./table.bend as T
import ./dirent.bend as R
import ./io.bend as I

# The choices a format makes. sectors_per_cluster 0: the smallest power of 2
# (a cluster at most 32 KB) that gives a count of clusters of the type asked
# for; reserved 0: 1 sector on FAT12/16, 32 on FAT32. root_entries is
# rounded up to fill whole sectors (FAT12/16 only). label: the BS_VolLab
# bytes (cut or padded to 11); unless it is "NO NAME", the root directory
# also gets a volume label entry. fs_info and backup_boot: FAT32's FSInfo
# sector and backup boot sector (the backup FSInfo follows it).
type FatFormatOptions is Data:
  FatFormatOptions{bytes_per_sector: U32, sectors_per_cluster: U32, reserved: U32, fats: U32, root_entries: U32, media: U32, sectors_per_track: U32, heads: U32, hidden: U32, drive: U32, volume_id: U32, label: B.Octets, oem: B.Octets, fs_info: U32, backup_boot: U32}

def FatFormatOptions.default() -> FatFormatOptions:
  FatFormatOptions{512, 0, 0, 2, 512, 248, 63, 255, 0, 128, 0, B.Octets.of_string("NO NAME    "), B.Octets.of_string("MSWIN4.1"), 1, 6}

# A volume's layout: its type, BPB and BS_ fields, and the count of
# clusters the BPB gives
type FatLayout is Data:
  FatLayout{kind: P.FatType, bpb: P.FatBpb, ext: P.FatBootExt, clusters: Nat}

def FatLayout.kind(l: FatLayout) -> P.FatType:
  match l:
    case FatLayout{t, b, x, c}:
      t

def FatLayout.bpb(l: FatLayout) -> P.FatBpb:
  match l:
    case FatLayout{t, b, x, c}:
      b

def FatLayout.ext(l: FatLayout) -> P.FatBootExt:
  match l:
    case FatLayout{t, b, x, c}:
      x

def FatLayout.clusters(l: FatLayout) -> Nat:
  match l:
    case FatLayout{t, b, x, c}:
      c

def FatFormat.bits(t: P.FatType) -> Nat:
  match t:
    case P.Fat12{}:
      12n
    case P.Fat16{}:
      16n
    case P.Fat32{}:
      32n

def FatFormat.is_fat32(t: P.FatType) -> Bool:
  match t:
    case P.Fat32{}:
      True{}
    case _:
      False{}

def FatFormat.same_type(a: P.FatType, b: P.FatType) -> Bool:
  match a b:
    case P.Fat12{} P.Fat12{}:
      True{}
    case P.Fat16{} P.Fat16{}:
      True{}
    case P.Fat32{} P.Fat32{}:
      True{}
    case _ _:
      False{}

def FatFormat.pick(c: Bool, a: Nat, b: Nat) -> Nat:
  match c:
    case True{}:
      a
    case False{}:
      b

# The geometry for one cluster size: the FAT size and the count of clusters

type FatGeom is Data:
  FatGeom{spc: Nat, fat_size: Nat, clusters: Nat}

def FatFormat.geom(+t: P.FatType, +tot: Nat, +bps: Nat, +rsvd: Nat, +nfats: Nat, +rootsecs: Nat, +spc: Nat) -> FatGeom:
  +b = FatFormat.bits(t)
  +data = Nat.sub(tot, Nat.add(rsvd, rootsecs))
  +den = Nat.add(Nat.mul(Nat.mul(8n, bps), spc), Nat.mul(b, nfats))
  +fatsz = Nat.div(Nat.add(Nat.mul(Nat.add(data, Nat.mul(2n, spc)), b), Nat.sub(den, 1n)), den)
  FatGeom{spc, fatsz, Nat.div(Nat.sub(data, Nat.mul(nfats, fatsz)), spc)}

def FatGeom.clusters(g: FatGeom) -> Nat:
  match g:
    case FatGeom{s, f, c}:
      c

# the count of clusters is one of the type's (and the metadata leaves room)
def FatFormat.fits(+t: P.FatType, +tot: Nat, +rsvd: Nat, +nfats: Nat, +rootsecs: Nat, g: FatGeom) -> Bool:
  match g:
    case FatGeom{+s, +f, +c}:
      Bool.and(Bool.and(Nat.is_lt(0n, c), Nat.is_le(c, 268435445n)), Bool.and(FatFormat.same_type(P.FatType.of_clusters(U32.from_nat(c)), t), Nat.is_lt(Nat.add(Nat.add(rsvd, Nat.mul(nfats, f)), rootsecs), tot)))

def FatFormat.choose.none(first: Maybe<&2, FatGeom>) -> Result<&2, &2, E.FatError, FatGeom>:
  match first:
    case Some{g}:
      Fail{E.FatFormatBadType{FatGeom.clusters(g)}}
    case None{}:
      Fail{E.FatFormatBadParam{}}

def FatFormat.choose.next(fits: Bool, small: Bool, g: FatGeom, first: Maybe<&2, FatGeom>, rest: Result<&2, &2, E.FatError, FatGeom>) -> Result<&2, &2, E.FatError, FatGeom>:
  match fits small:
    case True{} True{}:
      Done{g}
    case False{} True{}:
      rest
    case _ False{}:
      FatFormat.choose.none(first)

def FatFormat.choose.first(m: Maybe<&2, FatGeom>, g: FatGeom) -> Maybe<&2, FatGeom>:
  match m:
    case Some{f}:
      Some{f}
    case None{}:
      Some{g}

# the first cluster size of spcs (largest cluster 32 KB) that fits the type
# (first: the first size tried, whose count of clusters a failure reports)
def FatFormat.choose(spcs: List<&2, Nat>, +t: P.FatType, +tot: Nat, +bps: Nat, +rsvd: Nat, +nfats: Nat, +rootsecs: Nat, +first: Maybe<&2, FatGeom>) -> Result<&2, &2, E.FatError, FatGeom>:
  match spcs:
    case Nil{}:
      FatFormat.choose.none(first)
    case Con{+spc, rest}:
      +g = FatFormat.geom(t, tot, bps, rsvd, nfats, rootsecs, spc)
      FatFormat.choose.next(FatFormat.fits(t, tot, rsvd, nfats, rootsecs, g), Nat.is_le(Nat.mul(spc, bps), 32768n), g, first, FatFormat.choose(rest, t, tot, bps, rsvd, nfats, rootsecs, FatFormat.choose.first(first, g)))

def FatFormat.spcs.pick(auto: Bool, ok: Bool, +spc: U32) -> List<&2, Nat>:
  match auto ok:
    case True{} _:
      [1n, 2n, 4n, 8n, 16n, 32n, 64n, 128n]
    case False{} True{}:
      [U32.to_nat(spc)]
    case False{} False{}:
      []

def FatFormat.spcs(+spc: U32) -> List<&2, Nat>:
  FatFormat.spcs.pick(U32.is_eq(spc, 0), Bool.or(U32.is_eq(spc, 0), P.Fat.u32_in(spc, [1, 2, 4, 8, 16, 32, 64, 128])), spc)

# The BPB of a layout

def FatFormat.fs_type(t: P.FatType) -> B.Octets:
  B.Octets.of_string(P.FatType.show(t))

def FatFormat.jump(t: P.FatType) -> B.Octets:
  match t:
    case P.Fat32{}:
      B.Octets.of_list([235, 88, 144])
    case _:
      B.Octets.of_list([235, 60, 144])

def FatFormat.check(ok: Bool) -> Result<&2, &2, E.FatError, Unit>:
  P.Fat.require(ok, E.FatFormatBadParam{})

def FatFormat.verify.kind(ok: Bool, +l: FatLayout) -> Result<&2, &2, E.FatError, FatLayout>:
  match ok:
    case True{}:
      Done{l}
    case False{}:
      Fail{E.FatFormatBadType{FatLayout.clusters(l)}}

def FatFormat.verify.vol(r: Result<&2, &2, E.FatError, P.FatVolume>, +t: P.FatType, +l: FatLayout) -> Result<&2, &2, E.FatError, FatLayout>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+v}:
      FatFormat.verify.kind(Bool.and(FatFormat.same_type(P.FatVolume.kind(v), t), Nat.is_eq(U32.to_nat(P.FatVolume.clusters(v)), FatLayout.clusters(l))), l)

# the layout, once the reader's checks accept its BPB as a volume of type t,
# with the count of clusters computed
def FatFormat.verify(+t: P.FatType, +l: FatLayout) -> Result<&2, &2, E.FatError, FatLayout>:
  FatFormat.verify.vol(P.FatVolume.of_bpb(P.FatOptions.default(), FatLayout.bpb(l)), t, l)

def FatFormat.verify.r(+t: P.FatType, r: Result<&2, &2, E.FatError, FatLayout>) -> Result<&2, &2, E.FatError, FatLayout>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+l}:
      FatFormat.verify(t, l)

def FatFormat.build(+t: P.FatType, +tot: Nat, o: FatFormatOptions, +rsvd: Nat, +rootent: Nat, g: FatGeom) -> FatLayout:
  match o g:
    case FatFormatOptions{bps, spc0, r0, nfats, re0, media, spt, heads, hidden, drive, volid, label, oem, fsinfo, bk} FatGeom{spc, +fatsz, c}:
      +f32 = FatFormat.is_fat32(t)
      +small = Bool.and(Nat.is_lt(tot, 65536n), Bool.not(f32))
      +tot16 = FatFormat.pick(small, tot, 0n)
      +tot32 = FatFormat.pick(small, 0n, tot)
      +fatsz16 = FatFormat.pick(f32, 0n, fatsz)
      +fatsz32 = FatFormat.pick(f32, fatsz, 0n)
      FatLayout{t, P.FatBpb{FatFormat.jump(t), oem, bps, U32.from_nat(spc), U32.from_nat(rsvd), nfats, U32.from_nat(rootent), U32.from_nat(tot16), media, U32.from_nat(fatsz16), spt, heads, hidden, U32.from_nat(tot32), U32.from_nat(fatsz32), 0, 0, 2, fsinfo, bk, 43605}, P.FatBootExt{drive, 41, volid, R.FatDirent.fit_name(label), FatFormat.fs_type(t)}, c}

def FatFormat.rsvd(+t: P.FatType, +r: U32) -> Nat:
  FatFormat.pick(U32.is_eq(r, 0), FatFormat.pick(FatFormat.is_fat32(t), 32n, 1n), U32.to_nat(r))

def FatFormat.rootent(+t: P.FatType, +bps: Nat, +re: U32) -> Nat:
  +per = Nat.div(bps, 32n)
  FatFormat.pick(FatFormat.is_fat32(t), 0n, Nat.mul(Nat.div(Nat.add(U32.to_nat(re), Nat.sub(per, 1n)), per), per))

def Fat.u32_in_nat(+x: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Nat.is_eq(x, h), Fat.u32_in_nat(x, t))

def FatFormat.layout.go(+t: P.FatType, +tot: Nat, +o: FatFormatOptions, +bps: Nat, +rsvd: Nat, +rootent: Nat, +nfats: Nat, +fsinfo: Nat, +bk: Nat, +spc: U32) -> Result<&2, &2, E.FatError, FatLayout>:
  +rootsecs = Nat.div(Nat.mul(rootent, 32n), bps)
  +f32 = FatFormat.is_fat32(t)
  do Result<&2, &2, E.FatError, FatLayout>:
    +u0 : Unit <- FatFormat.check(Fat.u32_in_nat(bps, [512n, 1024n, 2048n, 4096n]))
    +u1 : Unit <- FatFormat.check(Bool.and(Nat.is_lt(0n, nfats), Nat.is_lt(nfats, 256n)))
    +u2 : Unit <- FatFormat.check(Bool.or(f32, Bool.and(Nat.is_lt(0n, rootent), Nat.is_lt(rootent, 65536n))))
    +u3 : Unit <- FatFormat.check(Bool.and(Nat.is_lt(0n, rsvd), Nat.is_lt(rsvd, 65536n)))
    +u4 : Unit <- FatFormat.check(Bool.or(Bool.not(f32), Bool.and(Bool.and(Nat.is_lt(0n, fsinfo), Nat.is_lt(fsinfo, rsvd)), Bool.and(Nat.is_lt(0n, bk), Nat.is_lt(Nat.add(bk, 1n), rsvd)))))
    +u5 : Unit <- FatFormat.check(Nat.is_le(tot, 4294967295n))
    +g : FatGeom <- FatFormat.choose(FatFormat.spcs(spc), t, tot, bps, rsvd, nfats, rootsecs, None{})
    return FatFormat.build(t, tot, o, rsvd, rootent, g)

def FatFormat.layout.raw(+t: P.FatType, +tot: Nat, +o: FatFormatOptions) -> Result<&2, &2, E.FatError, FatLayout>:
  match o:
    case FatFormatOptions{+bps, +spc, +r, +nfats, +re, media, spt, heads, hidden, drive, volid, label, oem, +fsinfo, +bk}:
      FatFormat.layout.go(t, tot, o, U32.to_nat(bps), FatFormat.rsvd(t, r), FatFormat.rootent(t, U32.to_nat(bps), re), U32.to_nat(nfats), U32.to_nat(fsinfo), U32.to_nat(bk), spc)

# the layout of a volume of tot sectors of type t (FatFormatBadParam for a
# choice the BPB cannot hold; FatFormatBadType when no allowed cluster size
# gives a count of clusters of the type, or the reader would take the BPB
# for another type)
def FatFormat.layout(+t: P.FatType, +tot: Nat, +o: FatFormatOptions) -> Result<&2, &2, E.FatError, FatLayout>:
  FatFormat.verify.r(t, FatFormat.layout.raw(t, tot, o))

# Writing a layout to a device (blockdev's owned interface)

# the first bytes of each FAT: entry 0 (the media byte, the other bits set),
# entry 1 (an end of chain) and, on FAT32, entry 2 (the root directory's
# one cluster, an end of chain)
def FatFormat.fat_head(t: P.FatType, +media: U32) -> B.Octets:
  match t:
    case P.Fat12{}:
      B.Octets.of_list([media, 255, 255])
    case P.Fat16{}:
      B.Octets.of_list([media, 255, 255, 255])
    case P.Fat32{}:
      B.Octets.of_list([media, 255, 255, 15, 255, 255, 255, 15, 255, 255, 255, 15])

def FatFormat.sector(+bps: Nat, o: B.Octets) -> B.Octets:
  +x = o
  B.Octets.append(x, B.Octets.zeros(Nat.sub(bps, B.Octets.len(x))))

# the FATs, each zeroed and given its first entries
def FatFormat.fats(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, n: Nat, +at: Nat, +size: Nat, +head: B.Octets) -> I.FatRun<Dv, Unit>:
  match n:
    case 0n:
      I.FatRun.pure(Dv, Unit, Unit{})
    case 1n+p:
      do I.FatRun<Dv, Unit>:
        I.FatOIo.zero(~Dv, ~block_size, ~read_block, ~write_block, at, size)
        I.FatOIo.write(~Dv, ~block_size, ~read_block, ~write_block, at, head)
        FatFormat.fats(~Dv, ~block_size, ~read_block, ~write_block, p, Nat.add(at, size), size, head)

# FAT32's FSInfo sector, its backup boot sector and its backup FSInfo
def FatFormat.fat32(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, f32: Bool, +bps: Nat, +fsinfo: Nat, +bk: Nat, +boot: B.Octets, +clusters: Nat) -> I.FatRun<Dv, Unit>:
  match f32:
    case False{}:
      I.FatRun.pure(Dv, Unit, Unit{})
    case True{}:
      +info = FatFormat.sector(bps, P.FatFsInfo.build(P.FatFsInfo{U32.from_nat(Nat.sub(clusters, 1n)), 3}))
      do I.FatRun<Dv, Unit>:
        I.FatOIo.write(~Dv, ~block_size, ~read_block, ~write_block, Nat.mul(fsinfo, bps), info)
        I.FatOIo.write(~Dv, ~block_size, ~read_block, ~write_block, Nat.mul(bk, bps), boot)
        I.FatOIo.write(~Dv, ~block_size, ~read_block, ~write_block, Nat.mul(Nat.add(bk, 1n), bps), info)

def FatFormat.root_at(root: P.FatRoot, +vol: P.FatVolume) -> Nat:
  match root:
    case P.FatRootFixed{start, n}:
      start
    case P.FatRootChain{c}:
      P.FatVolume.cluster_offset(vol, c)

def FatFormat.root_len(root: P.FatRoot, +vol: P.FatVolume) -> Nat:
  match root:
    case P.FatRootFixed{start, n}:
      Nat.mul(n, 32n)
    case P.FatRootChain{c}:
      P.FatVolume.cluster_bytes(vol)

def FatFormat.label(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, none: Bool, +at: Nat, lab: B.Octets) -> I.FatRun<Dv, Unit>:
  match none:
    case True{}:
      I.FatRun.pure(Dv, Unit, Unit{})
    case False{}:
      I.FatOIo.write(~Dv, ~block_size, ~read_block, ~write_block, at, R.FatDirent.encode(R.FatDirent{lab, 8, 0, 0, 0, 33, 33, 0, 0, 33, 0, 0}))

def FatFormat.ext_label(x: P.FatBootExt) -> B.Octets:
  match x:
    case P.FatBootExt{drive, sig, id, label, fst}:
      label

# the root directory's region (FAT12/16) or cluster (FAT32), zeroed, and the
# volume label entry
def FatFormat.root(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +vol: P.FatVolume, label: B.Octets) -> I.FatRun<Dv, Unit>:
  +at = FatFormat.root_at(P.FatVolume.root(vol), vol)
  +lab = R.FatDirent.fit_name(label)
  do I.FatRun<Dv, Unit>:
    I.FatOIo.zero(~Dv, ~block_size, ~read_block, ~write_block, at, FatFormat.root_len(P.FatVolume.root(vol), vol))
    FatFormat.label(~Dv, ~block_size, ~read_block, ~write_block, B.Octets.is_eq(lab, B.Octets.of_string("NO NAME    ")), at, lab)

def FatFormat.write.go(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, b: P.FatBpb, +l: FatLayout, +vol: P.FatVolume) -> I.FatRun<Dv, FatLayout>:
  match b:
    case P.FatBpb{jump, oem, +bps, spc, +rsvd, +nfats, rootent, tot16, +media, fatsz16, spt, heads, hidden, tot32, fatsz32, flags, ver, rootclus, +fsinfo, +bk, sig}:
      +t = FatLayout.kind(l)
      +n = U32.to_nat(bps)
      +boot = P.FatBpb.build(t, FatLayout.bpb(l), FatLayout.ext(l))
      do I.FatRun<Dv, FatLayout>:
        I.FatOIo.zero(~Dv, ~block_size, ~read_block, ~write_block, 0n, Nat.mul(U32.to_nat(rsvd), n))
        I.FatOIo.write(~Dv, ~block_size, ~read_block, ~write_block, 0n, boot)
        FatFormat.fat32(~Dv, ~block_size, ~read_block, ~write_block, FatFormat.is_fat32(t), n, U32.to_nat(fsinfo), U32.to_nat(bk), boot, FatLayout.clusters(l))
        FatFormat.fats(~Dv, ~block_size, ~read_block, ~write_block, U32.to_nat(nfats), P.FatVolume.fat_start(vol), P.FatVolume.fat_bytes(vol), FatFormat.fat_head(t, media))
        FatFormat.root(~Dv, ~block_size, ~read_block, ~write_block, vol, FatFormat.ext_label(FatLayout.ext(l)))
        return l

# the steps that write a layout: the reserved area zeroed, the boot sector
# (and FAT32's FSInfo and backups), every FAT, the root directory
def FatFormat.steps(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +t: P.FatType, +tot: Nat, +o: FatFormatOptions) -> I.FatRun<Dv, FatLayout>:
  do I.FatRun<Dv, FatLayout>:
    +l : FatLayout <- I.FatRun.lift(Dv, FatLayout, FatFormat.layout(t, tot, o))
    +v : P.FatVolume <- I.FatRun.lift(Dv, P.FatVolume, P.FatVolume.of_bpb(P.FatOptions.default(), FatLayout.bpb(l)))
    FatFormat.write.go(~Dv, ~block_size, ~read_block, ~write_block, FatLayout.bpb(l), l, v)

# a new volume of tot sectors of type t on the device d: the device after
# it, and the layout written
def FatFormat.format(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, d: Dv, +t: P.FatType, +tot: Nat, +o: FatFormatOptions) -> Dv & Result<&2, &2, E.FatError, FatLayout>:
  I.FatRun.exec(Dv, FatLayout, FatFormat.steps(~Dv, ~block_size, ~read_block, ~write_block, t, tot, o), d)
