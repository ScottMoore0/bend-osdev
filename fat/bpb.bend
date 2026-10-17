# bend-osdev-fat, bpb.bend: the boot sector and its BIOS Parameter Block
# (BPB), the volume's geometry derived from it, the FAT type, and the FAT32
# FSInfo sector.
#
# Microsoft, "FAT: General Overview of On-Disk Format" (the FAT32 File System
# Specification, version 1.03, 2000), section 3 (the boot sector and BPB),
# section 3.5 (FAT type determination) and section 5 (FSInfo).
#
# Offsets (all fields little-endian):
#    0 BS_jmpBoot (3)     3 BS_OEMName (8)     11 BPB_BytsPerSec (2)
#   13 BPB_SecPerClus (1) 14 BPB_RsvdSecCnt (2) 16 BPB_NumFATs (1)
#   17 BPB_RootEntCnt (2) 19 BPB_TotSec16 (2)  21 BPB_Media (1)
#   22 BPB_FATSz16 (2)    24 BPB_SecPerTrk (2)  26 BPB_NumHeads (2)
#   28 BPB_HiddSec (4)    32 BPB_TotSec32 (4)
# FAT32 only: 36 BPB_FATSz32 (4), 40 BPB_ExtFlags (2), 42 BPB_FSVer (2),
#   44 BPB_RootClus (4), 48 BPB_FSInfo (2), 50 BPB_BkBootSec (2), 52 reserved
#   (12). Then the BS_ fields (drive, boot signature, volume ID, label, file
#   system type) at 36 on FAT12/16 and at 64 on FAT32. Bytes 510 and 511 hold
#   0x55 0xAA, whatever the sector size.
#
# The FAT type is fixed by the count of clusters alone (section 3.5): fewer
# than 4085 is FAT12, fewer than 65525 FAT16, otherwise FAT32. The label
# strings ("FAT12   " and so on) are never consulted.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E

type FatType is Data:
  Fat12{}
  Fat16{}
  Fat32{}

# The BPB as stored. The FAT32 fields (fat_size32 to backup_boot) are read at
# their offsets whatever the type, as section 3.5 reads BPB_FATSz32; they mean
# something only on a FAT32 volume. signature is the 16-bit word at 510.
type FatBpb is Data:
  FatBpb{jump: B.Octets, oem: B.Octets, bytes_per_sector: U32, sectors_per_cluster: U32, reserved_sectors: U32, num_fats: U32, root_entries: U32, total16: U32, media: U32, fat_size16: U32, sectors_per_track: U32, heads: U32, hidden: U32, total32: U32, fat_size32: U32, ext_flags: U32, fs_version: U32, root_cluster: U32, fs_info: U32, backup_boot: U32, signature: U32}

# The BS_ fields after the BPB: drive number, extended boot signature (0x29
# when the next three are present), volume serial number, label (11 bytes)
# and file system type string (8 bytes, informational only)
type FatBootExt is Data:
  FatBootExt{drive: U32, boot_sig: U32, volume_id: U32, label: B.Octets, fs_type: B.Octets}

# Where the root directory is: a fixed region (FAT12/16; a byte offset and an
# entry count) or a cluster chain (FAT32)
type FatRoot is Data:
  FatRootFixed{start: Nat, entries: Nat}
  FatRootChain{cluster: U32}

# The volume's geometry, in bytes from the start of the device: the FAT type,
# the sector and cluster sizes, the active FAT's offset and size, the number
# of FATs, the root directory, where cluster 2 starts, and the count of
# clusters (valid cluster numbers are 2 to clusters + 1).
type FatVolume is Data:
  FatVolume{kind: FatType, sector: Nat, cluster: Nat, fat_start: Nat, fat_bytes: Nat, fats: Nat, root: FatRoot, data_start: Nat, clusters: U32}

# Choices a reader makes. max_cluster_bytes: the largest cluster accepted
# (the specification allows 32 KB; some systems write 64 KB). strict_names:
# refuse a directory whose long-name entries are out of sequence or do not
# match their short entry's checksum (False: ignore them, as orphans, the way
# the specification describes, and use the short name).
type FatOptions is Data:
  FatOptions{max_cluster_bytes: Nat, strict_names: Bool}

def FatOptions.default() -> FatOptions:
  FatOptions{32768n, True{}}

# 64 KB clusters accepted, and orphaned long names ignored
def FatOptions.lenient() -> FatOptions:
  FatOptions{65536n, False{}}

def FatType.show(t: FatType) -> String:
  match t:
    case Fat12{}:
      "FAT12"
    case Fat16{}:
      "FAT16"
    case Fat32{}:
      "FAT32"

def FatType.of_clusters.pick(lt12: Bool, lt16: Bool) -> FatType:
  match lt12:
    case True{}:
      Fat12{}
    case False{}:
      match lt16:
        case True{}:
          Fat16{}
        case False{}:
          Fat32{}

# the FAT type of a volume with this count of clusters (section 3.5)
def FatType.of_clusters(+n: U32) -> FatType:
  FatType.of_clusters.pick(U32.is_lt(n, 4085), U32.is_lt(n, 65525))

# Reading the boot sector

def FatBpb.decode.go(+xs: List<&2, U32>) -> Maybe<&2, FatBpb>:
  do Maybe<&2, FatBpb>:
    bps : U32 <- B.le16_at(xs, 11n)
    spc : U32 <- B.at(xs, 13n)
    rsvd : U32 <- B.le16_at(xs, 14n)
    nfats : U32 <- B.at(xs, 16n)
    rootent : U32 <- B.le16_at(xs, 17n)
    tot16 : U32 <- B.le16_at(xs, 19n)
    media : U32 <- B.at(xs, 21n)
    fatsz16 : U32 <- B.le16_at(xs, 22n)
    spt : U32 <- B.le16_at(xs, 24n)
    heads : U32 <- B.le16_at(xs, 26n)
    hidden : U32 <- B.le32_at(xs, 28n)
    tot32 : U32 <- B.le32_at(xs, 32n)
    fatsz32 : U32 <- B.le32_at(xs, 36n)
    flags : U32 <- B.le16_at(xs, 40n)
    ver : U32 <- B.le16_at(xs, 42n)
    rootclus : U32 <- B.le32_at(xs, 44n)
    fsinfo : U32 <- B.le16_at(xs, 48n)
    bk : U32 <- B.le16_at(xs, 50n)
    sig : U32 <- B.le16_at(xs, 510n)
    return FatBpb{B.Octets.of_list(B.take(3n, xs)), B.Octets.of_list(B.take(8n, B.drop(3n, xs))), bps, spc, rsvd, nfats, rootent, tot16, media, fatsz16, spt, heads, hidden, tot32, fatsz32, flags, ver, rootclus, fsinfo, bk, sig}

def FatBpb.decode.fin(m: Maybe<&2, FatBpb>) -> Result<&2, &2, E.FatError, FatBpb>:
  match m:
    case Some{b}:
      Done{b}
    case None{}:
      Fail{E.FatTooShort{}}

# the fields of a boot sector (at least 512 bytes), unchecked
def FatBpb.decode(o: B.Octets) -> Result<&2, &2, E.FatError, FatBpb>:
  FatBpb.decode.fin(FatBpb.decode.go(B.Octets.to_list(o)))

def FatBootExt.decode.go(+xs: List<&2, U32>, +at: Nat) -> Maybe<&2, FatBootExt>:
  do Maybe<&2, FatBootExt>:
    drive : U32 <- B.at(xs, at)
    sig : U32 <- B.at(xs, Nat.add(at, 2n))
    id : U32 <- B.le32_at(xs, Nat.add(at, 3n))
    last : U32 <- B.at(xs, Nat.add(at, 25n))
    return FatBootExt{drive, sig, id, B.Octets.of_list(B.take(11n, B.drop(Nat.add(at, 7n), xs))), B.Octets.of_list(B.take(8n, B.drop(Nat.add(at, 18n), xs)))}

def FatBootExt.offset(t: FatType) -> Nat:
  match t:
    case Fat32{}:
      64n
    case _:
      36n

def FatBootExt.decode.fin(m: Maybe<&2, FatBootExt>) -> Result<&2, &2, E.FatError, FatBootExt>:
  match m:
    case Some{x}:
      Done{x}
    case None{}:
      Fail{E.FatTooShort{}}

# the BS_ fields of a boot sector of this FAT type
def FatBootExt.decode(t: FatType, o: B.Octets) -> Result<&2, &2, E.FatError, FatBootExt>:
  FatBootExt.decode.fin(FatBootExt.decode.go(B.Octets.to_list(o), FatBootExt.offset(t)))

# Checking the BPB and deriving the volume (sections 3.1 to 3.5)

def Fat.require(ok: Bool, e: E.FatError) -> Result<&2, &2, E.FatError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

def Fat.u32_in(+x: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(U32.is_eq(x, h), Fat.u32_in(x, t))

def Fat.byte_is(m: Maybe<&2, U32>, +v: U32) -> Bool:
  match m:
    case Some{x}:
      U32.is_eq(x, v)
    case None{}:
      False{}

def Fat.or_else.pick(zero: Bool, a: U32, b: U32) -> U32:
  match zero:
    case True{}:
      b
    case False{}:
      a

# a, or b when a is zero (TotSec16 / TotSec32, FATSz16 / FATSz32)
def Fat.or_else(+a: U32, b: U32) -> U32:
  Fat.or_else.pick(U32.is_eq(a, 0), a, b)

# BS_jmpBoot: 0xEB ?? 0x90, or 0xE9 ?? ??
def FatBpb.jump_ok(o: B.Octets) -> Bool:
  +xs = B.Octets.to_list(o)
  Bool.or(Bool.and(Fat.byte_is(B.at(xs, 0n), 235), Fat.byte_is(B.at(xs, 2n), 144)), Fat.byte_is(B.at(xs, 0n), 233))

# the bytes of a FAT with n entries of this type
def FatType.fat_bytes(t: FatType, +n: Nat) -> Nat:
  match t:
    case Fat12{}:
      Nat.div(Nat.add(Nat.mul(n, 3n), 1n), 2n)
    case Fat16{}:
      Nat.mul(n, 2n)
    case Fat32{}:
      Nat.mul(n, 4n)

# the FAT in use: FAT 0 when the FATs are mirrored (FAT32 BPB_ExtFlags bit 7
# clear, and always on FAT12/16), otherwise the one bits 0 to 3 name
def FatVolume.active.pick(mirrored: Bool, +flags: U32) -> Nat:
  match mirrored:
    case True{}:
      0n
    case False{}:
      U32.to_nat(U32.and(15, flags))

def FatVolume.active(t: FatType, +flags: U32) -> Nat:
  match t:
    case Fat32{}:
      FatVolume.active.pick(U32.is_eq(U32.and(128, flags), 0), flags)
    case _:
      0n

def FatVolume.of_bpb.root(t: FatType, +start: Nat, +entries: Nat, +rootclus: U32) -> FatRoot:
  match t:
    case Fat32{}:
      FatRootChain{rootclus}
    case _:
      FatRootFixed{start, entries}

# FAT32: no fixed root directory, FATSz16 and TotSec16 zero, version 0:0, and
# a root cluster in range; FAT12/16: a fixed root directory
def FatVolume.of_bpb.check(t: FatType, +rootent: U32, +clusters: U32, +tot16: U32, +fatsz16: U32, +ver: U32, +rootclus: U32) -> Result<&2, &2, E.FatError, Unit>:
  match t:
    case Fat32{}:
      do Result<&2, &2, E.FatError, Unit>:
        u0 : Unit <- Fat.require(U32.is_eq(rootent, 0), E.FatBadRootEntries{})
        u1 : Unit <- Fat.require(U32.is_eq(fatsz16, 0), E.FatBadFatSize{})
        u2 : Unit <- Fat.require(U32.is_eq(tot16, 0), E.FatBadTotalSectors{})
        u3 : Unit <- Fat.require(U32.is_eq(ver, 0), E.FatBadVersion{})
        u4 : Unit <- Fat.require(Bool.and(U32.is_ge(rootclus, 2), U32.is_le(rootclus, U32.add(clusters, 1))), E.FatBadRootCluster{rootclus})
        return Unit{}
    case _:
      Fat.require(Bool.not(U32.is_eq(rootent, 0)), E.FatBadRootEntries{})

# the checks that depend on the FAT type, then the volume
def FatVolume.of_bpb.kind(+t: FatType, +bps: Nat, +spc: Nat, +rsvd: Nat, +nfats: Nat, +rootent: U32, +rootsecs: Nat, +fatsz: Nat, +clusters: U32, +tot16: U32, +fatsz16: U32, +ver: U32, +rootclus: U32, +flags: U32) -> Result<&2, &2, E.FatError, FatVolume>:
  +fats_end = Nat.add(rsvd, Nat.mul(nfats, fatsz))
  +active = FatVolume.active(t, flags)
  do Result<&2, &2, E.FatError, FatVolume>:
    u0 : Unit <- Fat.require(Nat.is_le(FatType.fat_bytes(t, Nat.add(U32.to_nat(clusters), 2n)), Nat.mul(fatsz, bps)), E.FatBadFatSize{})
    u1 : Unit <- Fat.require(Nat.is_lt(active, nfats), E.FatBadFatCount{})
    u2 : Unit <- FatVolume.of_bpb.check(t, rootent, clusters, tot16, fatsz16, ver, rootclus)
    return FatVolume{t, bps, Nat.mul(bps, spc), Nat.mul(Nat.add(rsvd, Nat.mul(active, fatsz)), bps), Nat.mul(fatsz, bps), nfats, FatVolume.of_bpb.root(t, Nat.mul(fats_end, bps), U32.to_nat(rootent), rootclus), Nat.mul(Nat.add(fats_end, rootsecs), bps), clusters}

# the counts of section 3.5: root directory sectors, data sectors, clusters
def FatVolume.of_bpb.geom(+bps: Nat, +spc: Nat, +rsvd: Nat, +nfats: Nat, +rootent: U32, +tot: Nat, +fatsz: Nat, +tot16: U32, +fatsz16: U32, +ver: U32, +rootclus: U32, +flags: U32) -> Result<&2, &2, E.FatError, FatVolume>:
  +rootsecs = Nat.div(Nat.add(Nat.mul(U32.to_nat(rootent), 32n), Nat.sub(bps, 1n)), bps)
  +meta = Nat.add(Nat.add(rsvd, Nat.mul(nfats, fatsz)), rootsecs)
  +count = Nat.div(Nat.sub(tot, meta), spc)
  do Result<&2, &2, E.FatError, FatVolume>:
    u0 : Unit <- Fat.require(Nat.is_lt(meta, tot), E.FatTooSmall{})
    u1 : Unit <- Fat.require(Nat.is_lt(0n, count), E.FatTooSmall{})
    u2 : Unit <- Fat.require(Nat.is_le(count, 268435445n), E.FatBadTotalSectors{})
    FatVolume.of_bpb.kind(FatType.of_clusters(U32.from_nat(count)), bps, spc, rsvd, nfats, rootent, rootsecs, fatsz, U32.from_nat(count), tot16, fatsz16, ver, rootclus, flags)

# the volume a BPB describes, or the first check it fails
def FatVolume.of_bpb(opts: FatOptions, b: FatBpb) -> Result<&2, &2, E.FatError, FatVolume>:
  match opts b:
    case FatOptions{+maxc, strict} FatBpb{jump, oem, +bps, +spc, +rsvd, +nfats, +rootent, +tot16, +media, +fatsz16, spt, heads, hidden, +tot32, +fatsz32, +flags, +ver, +rootclus, fsinfo, bk, +sig}:
      +tot = U32.to_nat(Fat.or_else(tot16, tot32))
      +fatsz = U32.to_nat(Fat.or_else(fatsz16, fatsz32))
      +csize = Nat.mul(U32.to_nat(bps), U32.to_nat(spc))
      do Result<&2, &2, E.FatError, FatVolume>:
        u0 : Unit <- Fat.require(U32.is_eq(sig, 43605), E.FatBadSignature{})
        u1 : Unit <- Fat.require(FatBpb.jump_ok(jump), E.FatBadJump{})
        u2 : Unit <- Fat.require(Fat.u32_in(bps, [512, 1024, 2048, 4096]), E.FatBadBytesPerSector{bps})
        u3 : Unit <- Fat.require(Fat.u32_in(spc, [1, 2, 4, 8, 16, 32, 64, 128]), E.FatBadSectorsPerCluster{spc})
        u4 : Unit <- Fat.require(Nat.is_le(csize, maxc), E.FatClusterTooLarge{csize})
        u5 : Unit <- Fat.require(Bool.not(U32.is_eq(rsvd, 0)), E.FatBadReservedSectors{})
        u6 : Unit <- Fat.require(Bool.not(U32.is_eq(nfats, 0)), E.FatBadFatCount{})
        u7 : Unit <- Fat.require(Bool.or(U32.is_eq(media, 240), U32.is_ge(media, 248)), E.FatBadMedia{media})
        u8 : Unit <- Fat.require(Bool.not(Nat.is_eq(tot, 0n)), E.FatBadTotalSectors{})
        u9 : Unit <- Fat.require(Bool.not(Nat.is_eq(fatsz, 0n)), E.FatBadFatSize{})
        FatVolume.of_bpb.geom(U32.to_nat(bps), U32.to_nat(spc), U32.to_nat(rsvd), U32.to_nat(nfats), rootent, tot, fatsz, tot16, fatsz16, ver, rootclus, flags)

# the checked volume of a boot sector
def FatVolume.parse(opts: FatOptions, o: B.Octets) -> Result<&2, &2, E.FatError, FatVolume>:
  do Result<&2, &2, E.FatError, FatVolume>:
    b : FatBpb <- FatBpb.decode(o)
    FatVolume.of_bpb(opts, b)

# Accessors

def FatVolume.kind(v: FatVolume) -> FatType:
  match v:
    case FatVolume{t, sec, clu, fs, fb, n, root, ds, c}:
      t

def FatVolume.sector(v: FatVolume) -> Nat:
  match v:
    case FatVolume{t, sec, clu, fs, fb, n, root, ds, c}:
      sec

def FatVolume.cluster_bytes(v: FatVolume) -> Nat:
  match v:
    case FatVolume{t, sec, clu, fs, fb, n, root, ds, c}:
      clu

def FatVolume.fat_start(v: FatVolume) -> Nat:
  match v:
    case FatVolume{t, sec, clu, fs, fb, n, root, ds, c}:
      fs

def FatVolume.fat_bytes(v: FatVolume) -> Nat:
  match v:
    case FatVolume{t, sec, clu, fs, fb, n, root, ds, c}:
      fb

def FatVolume.fats(v: FatVolume) -> Nat:
  match v:
    case FatVolume{t, sec, clu, fs, fb, n, root, ds, c}:
      n

def FatVolume.root(v: FatVolume) -> FatRoot:
  match v:
    case FatVolume{t, sec, clu, fs, fb, n, root, ds, c}:
      root

def FatVolume.data_start(v: FatVolume) -> Nat:
  match v:
    case FatVolume{t, sec, clu, fs, fb, n, root, ds, c}:
      ds

def FatVolume.clusters(v: FatVolume) -> U32:
  match v:
    case FatVolume{t, sec, clu, fs, fb, n, root, ds, c}:
      c

# the byte offset of cluster n (n from 2)
def FatVolume.cluster_offset(v: FatVolume, n: U32) -> Nat:
  match v:
    case FatVolume{t, sec, +clu, fs, fb, k, root, ds, c}:
      Nat.add(ds, Nat.mul(Nat.sub(U32.to_nat(n), 2n), clu))

# whether n is a cluster of the volume (2 to clusters + 1)
def FatVolume.valid_cluster(v: FatVolume, +n: U32) -> Bool:
  Bool.and(U32.is_ge(n, 2), U32.is_le(n, U32.add(FatVolume.clusters(v), 1)))

# Writing a boot sector (for building images; the reader never writes)

# n bytes: xs cut, or padded with pad
def Fat.fit(n: Nat, +pad: U32, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match xs:
        case Nil{}:
          Con{pad, Fat.fit(p, pad, Nil{})}
        case Con{h, t}:
          Con{h, Fat.fit(p, pad, t)}

def FatBootExt.encode(x: FatBootExt) -> List<&2, U32>:
  match x:
    case FatBootExt{drive, sig, id, label, fstype}:
      Con{drive, Con{0, Con{sig, B.append(B.le32(id), B.append(Fat.fit(11n, 32, B.Octets.to_list(label)), Fat.fit(8n, 32, B.Octets.to_list(fstype))))}}}

def FatBpb.encode.ext(t: FatType, +fatsz32: U32, +flags: U32, +ver: U32, +rootclus: U32, +fsinfo: U32, +bk: U32, x: FatBootExt) -> List<&2, U32>:
  match t:
    case Fat32{}:
      B.append(B.le32(fatsz32), B.append(B.le16(flags), B.append(B.le16(ver), B.append(B.le32(rootclus), B.append(B.le16(fsinfo), B.append(B.le16(bk), B.append(B.zeros(12n), FatBootExt.encode(x))))))))
    case _:
      FatBootExt.encode(x)

# the boot sector of a BPB and its BS_ fields, laid out for this FAT type:
# bytes_per_sector bytes (at least 512), the signature word at 510
def FatBpb.build(t: FatType, b: FatBpb, x: FatBootExt) -> B.Octets:
  match b:
    case FatBpb{jump, oem, +bps, spc, rsvd, nfats, rootent, tot16, media, fatsz16, spt, heads, hidden, tot32, fatsz32, flags, ver, rootclus, fsinfo, bk, sig}:
      +head = List.concat(&2, U32, [Fat.fit(3n, 0, B.Octets.to_list(jump)), Fat.fit(8n, 32, B.Octets.to_list(oem)), B.le16(bps), [spc], B.le16(rsvd), [nfats], B.le16(rootent), B.le16(tot16), [media], B.le16(fatsz16), B.le16(spt), B.le16(heads), B.le32(hidden), B.le32(tot32)])
      B.Octets.of_list(B.append(Fat.fit(510n, 0, B.append(head, FatBpb.encode.ext(t, fatsz32, flags, ver, rootclus, fsinfo, bk, x))), B.append(B.le16(sig), B.zeros(Nat.sub(U32.to_nat(bps), 512n)))))

# FSInfo (section 5): lead signature 0x41615252 at 0, structure signature
# 0x61417272 at 484, the free cluster count at 488, the next free cluster at
# 492, trail signature 0xAA550000 at 508. Both counts are hints (0xFFFFFFFF:
# unknown).
type FatFsInfo is Data:
  FatFsInfo{free_count: U32, next_free: U32}

def FatFsInfo.parse.sig(ok: Bool, free: U32, next: U32) -> Result<&2, &2, E.FatError, FatFsInfo>:
  match ok:
    case True{}:
      Done{FatFsInfo{free, next}}
    case False{}:
      Fail{E.FatBadFsInfo{}}

def FatFsInfo.parse.go(+xs: List<&2, U32>) -> Maybe<&2, Result<&2, &2, E.FatError, FatFsInfo>>:
  do Maybe<&2, Result<&2, &2, E.FatError, FatFsInfo>>:
    lead : U32 <- B.le32_at(xs, 0n)
    struc : U32 <- B.le32_at(xs, 484n)
    free : U32 <- B.le32_at(xs, 488n)
    next : U32 <- B.le32_at(xs, 492n)
    trail : U32 <- B.le32_at(xs, 508n)
    return FatFsInfo.parse.sig(Bool.and(U32.is_eq(lead, 1096897106), Bool.and(U32.is_eq(struc, 1631679090), U32.is_eq(trail, 2857697280))), free, next)

def FatFsInfo.parse.fin(m: Maybe<&2, Result<&2, &2, E.FatError, FatFsInfo>>) -> Result<&2, &2, E.FatError, FatFsInfo>:
  match m:
    case Some{r}:
      r
    case None{}:
      Fail{E.FatTooShort{}}

# the FSInfo sector's hints, its three signatures checked
def FatFsInfo.parse(o: B.Octets) -> Result<&2, &2, E.FatError, FatFsInfo>:
  FatFsInfo.parse.fin(FatFsInfo.parse.go(B.Octets.to_list(o)))

# an FSInfo sector of 512 bytes
def FatFsInfo.build(f: FatFsInfo) -> B.Octets:
  match f:
    case FatFsInfo{free, next}:
      B.Octets.of_list(B.append(B.le32(1096897106), B.append(B.zeros(480n), B.append(B.le32(1631679090), B.append(B.le32(free), B.append(B.le32(next), B.append(B.zeros(12n), B.le32(2857697280))))))))
