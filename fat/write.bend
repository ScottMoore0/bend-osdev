# bend-osdev-fat, write.bend: the writing file system, on blockdev's owned
# interface: opening a volume for writing, and the operations by path
# (creating files and directories, writing, appending, truncating,
# deleting, renaming, setting times and attributes), with reading and
# listing on the same device.
#
# Microsoft, "FAT: General Overview of On-Disk Format" (version 1.03, 2000):
# section 4 (the FAT: every copy kept equal, unless FAT32's BPB_ExtFlags
# turns mirroring off, when only the active FAT is written), section 5
# (FSInfo: its free count and next-free hint kept up to date on FAT32),
# section 6 (directory entries, "." and "..": the ".." of a directory in the
# root holds cluster 0, on FAT32 too) and section 7 (long names).
#
# The writer holds the FAT in memory (map.bend's FatMap, read once when the
# volume is opened) and changes it there; every operation then writes the
# FAT sectors it changed to the device, to each FAT copy, and FSInfo, so the
# volume on the device is consistent after every operation. An operation
# checks everything it can (names, space, emptiness) before it writes, so
# one that fails for any reason but the device's leaves the volume as it
# was (and the caller keeps the state it had). Allocation is first fit from
# the FSInfo hint (FatWOptions.from_hint), or from cluster 2.
#
# Operations take blockdev's owned template arguments (~Dv, ~block_size,
# ~read_block, ~write_block) and a device d, and answer the device and a
# result: d & Done{state after}, or d & Fail{why}.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./bpb.bend as P
import ./table.bend as T
import ./dirent.bend as R
import ./dir.bend as Q
import ./fat.bend as M
import ./io.bend as I
import ./map.bend as A
import ./alias.bend as L
import ./wdir.bend as W

# The writer's choices. nt_case: a name that is an 8.3 name with its base
# and extension each in one case is stored as a short entry alone, its case
# in Windows NT's DIR_NTRes flags (False: a long-name entry keeps the case,
# the specification's way, since it reserves DIR_NTRes). from_hint: allocate
# from FSInfo's next-free hint, moved past each allocation (False: from
# cluster 2 every time). read_only: refuse to write, truncate or delete a
# file with ATTR_READ_ONLY.
type FatWOptions is Data:
  FatWOptions{nt_case: Bool, from_hint: Bool, read_only: Bool}

def FatWOptions.default() -> FatWOptions:
  FatWOptions{False{}, True{}, True{}}

# A moment, as directory entries store it: a date, a time (to 2 seconds)
# and the tenths of a second (0 to 199, the creation time's extra field)
type FatClock is Data:
  FatClock{date: R.FatDate, time: R.FatTime, tenth: U32}

# 1980-01-01 00:00:00, the earliest a FAT date holds
def FatClock.epoch() -> FatClock:
  FatClock{R.FatDate{1980, 1, 1}, R.FatTime{0, 0, 0}, 0}

def FatClock.date(c: FatClock) -> U32:
  match c:
    case FatClock{d, t, x}:
      R.FatDate.encode(d)

def FatClock.time(c: FatClock) -> U32:
  match c:
    case FatClock{d, t, x}:
      R.FatTime.encode(t)

def FatClock.tenth(c: FatClock) -> U32:
  match c:
    case FatClock{d, t, x}:
      x

# An entry's times: created, last written, last accessed (a date only)
type FatTimes is Data:
  FatTimes{create: FatClock, write: FatClock, access: R.FatDate}

# The writer's state: the volume (as fat.bend mounts it), the choices, the
# FAT in memory, the count of free clusters, the next-free hint, the clock
# that stamps entries, the clusters whose FAT entries changed since the
# last flush, whether FSInfo is kept, and the byte offset of the first FAT
type FatW is Data:
  FatW{fs: M.FatFs, wopts: FatWOptions, map: A.FatMap, free: Nat, hint: Nat, clock: FatClock, dirty: List<&2, Nat>, info: Bool, fat0: Nat}

def FatW.fs(w: FatW) -> M.FatFs:
  match w:
    case FatW{fs, o, m, f, h, c, dy, i, z}:
      fs

def FatW.volume(w: FatW) -> P.FatVolume:
  M.FatFs.volume(FatW.fs(w))

def FatW.wopts(w: FatW) -> FatWOptions:
  match w:
    case FatW{fs, o, m, f, h, c, dy, i, z}:
      o

def FatW.map(w: FatW) -> A.FatMap:
  match w:
    case FatW{fs, o, m, f, h, c, dy, i, z}:
      m

def FatW.free_clusters(w: FatW) -> Nat:
  match w:
    case FatW{fs, o, m, f, h, c, dy, i, z}:
      f

def FatW.hint(w: FatW) -> Nat:
  match w:
    case FatW{fs, o, m, f, h, c, dy, i, z}:
      h

def FatW.clock(w: FatW) -> FatClock:
  match w:
    case FatW{fs, o, m, f, h, c, dy, i, z}:
      c

# the state with a new clock (the time later operations stamp)
def FatW.set_clock(w: FatW, now: FatClock) -> FatW:
  match w:
    case FatW{fs, o, m, f, h, c, dy, i, z}:
      FatW{fs, o, m, f, h, now, dy, i, z}

def FatWOptions.nt_case(o: FatWOptions) -> Bool:
  match o:
    case FatWOptions{n, h, r}:
      n

def FatWOptions.from_hint(o: FatWOptions) -> Bool:
  match o:
    case FatWOptions{n, h, r}:
      h

def FatWOptions.read_only(o: FatWOptions) -> Bool:
  match o:
    case FatWOptions{n, h, r}:
      r

def FatW.nt_case(w: FatW) -> Bool:
  FatWOptions.nt_case(FatW.wopts(w))

def FatW.kind(w: FatW) -> P.FatType:
  P.FatVolume.kind(FatW.volume(w))

def FatW.cbytes(w: FatW) -> Nat:
  P.FatVolume.cluster_bytes(FatW.volume(w))

def FatW.options(w: FatW) -> P.FatOptions:
  M.FatFs.options(FatW.fs(w))

def FatW.from_hint(w: FatW) -> Bool:
  FatWOptions.from_hint(FatW.wopts(w))

def FatW.respect_ro(w: FatW) -> Bool:
  FatWOptions.read_only(FatW.wopts(w))

def FatW.pick_nat(c: Bool, a: Nat, b: Nat) -> Nat:
  match c:
    case True{}:
      a
    case False{}:
      b

# where allocation starts: the hint, or cluster 2
def FatW.start(+w: FatW) -> Nat:
  FatW.pick_nat(FatW.from_hint(w), FatW.hint(w), 2n)

# Opening a volume: the boot sector checked (as fat.bend's Fat.mount), the
# active FAT read into a map, and FAT32's FSInfo hint

def FatW.byte.or(+a: U32, +b: U32, +n: Nat) -> U32:
  U32.or(a, U32.shln(U32.and(255, b), n))

# FAT16 entries from bytes: k of them onto acc (latest first)
def FatW.unpack16(k: Nat, xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+p:
      match xs:
        case Con{a, Con{b, t}}:
          FatW.unpack16(p, t, Con{FatW.byte.or(U32.and(255, a), b, 8n), acc})
        case _:
          acc

def FatW.unpack32(k: Nat, xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+p:
      match xs:
        case Con{a, Con{b, Con{c, Con{d, t}}}}:
          FatW.unpack32(p, t, Con{FatW.byte.or(FatW.byte.or(FatW.byte.or(U32.and(255, a), b, 8n), c, 16n), U32.and(15, d), 24n), acc})
        case _:
          acc

# FAT12 entries from bytes, two (three bytes) at a time
def FatW.unpack12(k: Nat, xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+p:
      match xs:
        case Con{a, Con{+b, Con{c, t}}}:
          +e0 = U32.or(U32.and(255, a), U32.shln(U32.and(15, b), 8n))
          +e1 = U32.or(U32.and(15, U32.shrn(U32.and(255, b), 4n)), U32.shln(U32.and(255, c), 4n))
          FatW.unpack12(p, t, Con{e1, Con{e0, acc}})
        case _:
          acc

def FatW.unpack(t: P.FatType, +k: Nat, xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match t:
    case P.Fat12{}:
      FatW.unpack12(Nat.div(Nat.add(k, 1n), 2n), xs, acc)
    case P.Fat16{}:
      FatW.unpack16(k, xs, acc)
    case P.Fat32{}:
      FatW.unpack32(k, xs, acc)

def FatW.width(t: P.FatType) -> Nat:
  match t:
    case P.Fat12{}:
      3n
    case P.Fat16{}:
      2n
    case P.Fat32{}:
      4n

def FatW.rev(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      FatW.rev(t, Con{h, acc})

# the bytes k entries take (FAT12: whole pairs)
def FatW.load.bytes(t: P.FatType, +k: Nat) -> Nat:
  match t:
    case P.Fat12{}:
      Nat.mul(Nat.div(Nat.add(k, 1n), 2n), 3n)
    case P.Fat16{}:
      Nat.mul(k, 2n)
    case P.Fat32{}:
      Nat.mul(k, 4n)

# the entries of the FAT at byte offset at: left entries more, read in
# pieces of per entries (n: the pieces left)
def FatW.load.go(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, n: Nat, +t: P.FatType, +at: Nat, +per: Nat, +left: Nat, acc: List<&2, U32>) -> I.FatRun<Dv, List<&2, U32>>:
  match n:
    case 0n:
      I.FatRun.pure(Dv, List<&2, U32>, acc)
    case 1n+p:
      +k = Nat.min(per, left)
      +bytes = FatW.load.bytes(t, k)
      do I.FatRun<Dv, List<&2, U32>>:
        +o : B.Octets <- I.FatOIo.read(~Dv, ~block_size, ~read_block, at, bytes)
        FatW.load.go(~Dv, ~block_size, ~read_block, p, t, Nat.add(at, bytes), per, Nat.sub(left, k), FatW.unpack(t, k, B.Octets.to_list(o), acc))

def FatW.load.per(t: P.FatType, +sec: Nat, +count: Nat) -> Nat:
  match t:
    case P.Fat12{}:
      Nat.add(count, 1n)
    case P.Fat16{}:
      Nat.mul(16n, sec)
    case P.Fat32{}:
      Nat.mul(8n, sec)

# the active FAT's count entries as a map (FAT12 in one read; FAT16 and
# FAT32 in pieces of 32 sectors, so no read holds the whole FAT)
def FatW.load_map(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, +vol: P.FatVolume, +count: Nat) -> I.FatRun<Dv, A.FatMap>:
  +t = P.FatVolume.kind(vol)
  +per = FatW.load.per(t, P.FatVolume.sector(vol), count)
  do I.FatRun<Dv, A.FatMap>:
    +rs : List<&2, U32> <- FatW.load.go(~Dv, ~block_size, ~read_block, Nat.div(Nat.add(count, Nat.sub(per, 1n)), per), t, P.FatVolume.fat_start(vol), per, count, Nil{})
    return A.FatMap.of_list(t, B.take.fast(count, FatW.rev(rs, Nil{})))

def FatW.fs_info_at(b: P.FatBpb) -> Nat:
  match b:
    case P.FatBpb{jump, oem, +bps, spc, rsvd, nfats, rootent, tot16, media, fatsz16, spt, heads, hidden, tot32, fatsz32, flags, ver, rootclus, +fsinfo, bk, sig}:
      Nat.mul(U32.to_nat(fsinfo), U32.to_nat(bps))

def FatW.fat0(b: P.FatBpb) -> Nat:
  match b:
    case P.FatBpb{jump, oem, +bps, spc, +rsvd, nfats, rootent, tot16, media, fatsz16, spt, heads, hidden, tot32, fatsz32, flags, ver, rootclus, fsinfo, bk, sig}:
      Nat.mul(U32.to_nat(rsvd), U32.to_nat(bps))

def FatW.is_fat32(t: P.FatType) -> Bool:
  match t:
    case P.Fat32{}:
      True{}
    case _:
      False{}

def FatW.info.of(r: Result<&2, &2, E.FatError, P.FatFsInfo>) -> Maybe<&2, P.FatFsInfo>:
  match r:
    case Done{i}:
      Some{i}
    case Fail{e}:
      None{}

# FSInfo's next-free hint, when FSInfo is good and the hint a cluster of the
# volume (else None: no FSInfo is kept)
def FatW.info.read(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, fat32: Bool, +at: Nat) -> I.FatRun<Dv, Maybe<&2, P.FatFsInfo>>:
  match fat32:
    case False{}:
      I.FatRun.pure(Dv, Maybe<&2, P.FatFsInfo>, None{})
    case True{}:
      do I.FatRun<Dv, Maybe<&2, P.FatFsInfo>>:
        +o : B.Octets <- I.FatOIo.read(~Dv, ~block_size, ~read_block, at, 512n)
        return FatW.info.of(P.FatFsInfo.parse(o))

def FatW.info.hint(m: Maybe<&2, P.FatFsInfo>, +count: Nat) -> Nat:
  match m:
    case Some{P.FatFsInfo{f, +n}}:
      FatW.pick_nat(Bool.and(U32.is_ge(n, 2), Nat.is_lt(U32.to_nat(n), count)), U32.to_nat(n), 2n)
    case None{}:
      2n

def FatW.open.steps(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, +opts: P.FatOptions, +wopts: FatWOptions) -> I.FatRun<Dv, FatW>:
  do I.FatRun<Dv, FatW>:
    +o : B.Octets <- I.FatOIo.read(~Dv, ~block_size, ~read_block, 0n, 512n)
    +b : P.FatBpb <- I.FatRun.lift(Dv, P.FatBpb, P.FatBpb.decode(o))
    +fs : M.FatFs <- I.FatRun.lift(Dv, M.FatFs, M.Fat.mount.with(opts, b))
    +vol : P.FatVolume = M.FatFs.volume(fs)
    +count : Nat = Nat.add(U32.to_nat(P.FatVolume.clusters(vol)), 2n)
    +map : A.FatMap <- FatW.load_map(~Dv, ~block_size, ~read_block, vol, count)
    +info : Maybe<&2, P.FatFsInfo> <- FatW.info.read(~Dv, ~block_size, ~read_block, FatW.is_fat32(P.FatVolume.kind(vol)), FatW.fs_info_at(b))
    return FatW{fs, wopts, map, A.FatMap.free_count(map), FatW.info.hint(info, count), FatClock.epoch(), Nil{}, Maybe.is_some(&2, P.FatFsInfo, info), FatW.fat0(b)}

# Flushing: the FAT sectors whose entries changed, written to each FAT copy,
# then FSInfo's free count and hint

# the FAT sectors (from the FAT's start) that hold the entries of cs (a
# sector may be listed more than once)
def FatW.sectors.all(cs: List<&2, Nat>, +t: P.FatType, +bps: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      acc
    case Con{+c, rest}:
      +off = T.FatTable.offset(t, c)
      FatW.sectors.all(rest, t, bps, Con{Nat.div(Nat.add(off, Nat.sub(T.FatTable.width(t), 1n)), bps), Con{Nat.div(off, bps), acc}})

def FatW.dedup.put(same: Bool, +h: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match same:
    case True{}:
      acc
    case False{}:
      Con{h, acc}

def FatW.dedup.same(m: Maybe<&2, Nat>, +h: Nat) -> Bool:
  match m:
    case Some{p}:
      Nat.is_eq(p, h)
    case None{}:
      False{}

# a sorted list without repeats (reversed onto acc; prev: the last kept)
def FatW.dedup(xs: List<&2, Nat>, +prev: Maybe<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case Con{+h, t}:
      +same = FatW.dedup.same(prev, h)
      FatW.dedup(t, Some{h}, FatW.dedup.put(same, h, acc))

# the FAT sectors that hold the entries of cs, each once
def FatW.sectors(cs: List<&2, Nat>, +t: P.FatType, +bps: Nat) -> List<&2, Nat>:
  FatW.dedup(List.sort(~Nat, ~Nat.is_le, FatW.sectors.all(cs, t, bps, Nil{})), None{}, Nil{})

def FatW.le16(+v: U32, acc: List<&2, U32>) -> List<&2, U32>:
  Con{U32.and(255, U32.shrn(v, 8n)), Con{U32.and(255, v), acc}}

def FatW.le32(+v: U32, acc: List<&2, U32>) -> List<&2, U32>:
  Con{U32.and(255, U32.shrn(v, 24n)), Con{U32.and(255, U32.shrn(v, 16n)), Con{U32.and(255, U32.shrn(v, 8n)), Con{U32.and(255, v), acc}}}}

def FatW.pick_list(c: Bool, a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  match c:
    case True{}:
      a
    case False{}:
      b

def FatW.pick_u32(c: Bool, a: U32, b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

# a FAT16 sector's bytes from the map: k entries from entry n (old: the
# bytes on the device, kept past the last entry), reversed onto acc
def FatW.enc16(k: Nat, +m: A.FatMap, +n: Nat, old: List<&2, U32>, +acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+p:
      match old:
        case Con{a, Con{b, t}}:
          FatW.enc16(p, m, Nat.add(n, 1n), t, FatW.pick_list(Nat.is_lt(n, A.FatMap.count(m)), FatW.le16(A.FatMap.get(m, n), acc), Con{b, Con{a, acc}}))
        case _:
          acc

def FatW.enc32(k: Nat, +m: A.FatMap, +n: Nat, old: List<&2, U32>, +acc: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      acc
    case 1n+p:
      match old:
        case Con{+a, Con{+b, Con{+c, Con{+d, t}}}}:
          +was = FatW.byte.or(FatW.byte.or(FatW.byte.or(U32.and(255, a), b, 8n), c, 16n), d, 24n)
          FatW.enc32(p, m, Nat.add(n, 1n), t, FatW.pick_list(Nat.is_lt(n, A.FatMap.count(m)), FatW.le32(T.Fat32.set(was, A.FatMap.get(m, n)), acc), Con{d, Con{c, Con{b, Con{a, acc}}}}))
        case _:
          acc

# byte o of a FAT12 FAT: entries 2k and 2k + 1 share bytes 3k to 3k + 2
def FatW.enc12.byte(+m: A.FatMap, +o: Nat, +old: U32) -> U32:
  +k = Nat.div(o, 3n)
  +r = Nat.mod(o, 3n)
  +e0 = Nat.mul(k, 2n)
  +e1 = Nat.add(e0, 1n)
  +n = A.FatMap.count(m)
  +v0 = A.FatMap.get(m, e0)
  +v1 = A.FatMap.get(m, e1)
  +in0 = Nat.is_lt(e0, n)
  +in1 = Nat.is_lt(e1, n)
  +b1 = U32.or(FatW.pick_u32(in0, U32.and(15, U32.shrn(v0, 8n)), U32.and(15, old)), FatW.pick_u32(in1, U32.shln(U32.and(15, v1), 4n), U32.and(240, old)))
  FatW.pick_u32(Nat.is_eq(r, 0n), FatW.pick_u32(in0, U32.and(255, v0), old), FatW.pick_u32(Nat.is_eq(r, 1n), b1, FatW.pick_u32(in1, U32.and(255, U32.shrn(v1, 4n)), old)))

def FatW.enc12(old: List<&2, U32>, +m: A.FatMap, +o: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match old:
    case Nil{}:
      acc
    case Con{+b, t}:
      FatW.enc12(t, m, Nat.add(o, 1n), Con{FatW.enc12.byte(m, o, b), acc})

# FAT sector s's bytes from the map, the device's bytes old kept where no
# entry is (and FAT32's reserved high 4 bits)
def FatW.encode(t: P.FatType, +m: A.FatMap, +s: Nat, +bps: Nat, old: List<&2, U32>) -> B.Octets:
  match t:
    case P.Fat12{}:
      B.Octets.of_list(FatW.rev(FatW.enc12(old, m, Nat.mul(s, bps), Nil{}), Nil{}))
    case P.Fat16{}:
      B.Octets.of_list(FatW.rev(FatW.enc16(Nat.div(bps, 2n), m, Nat.mul(s, Nat.div(bps, 2n)), old, Nil{}), Nil{}))
    case P.Fat32{}:
      B.Octets.of_list(FatW.rev(FatW.enc32(Nat.div(bps, 4n), m, Nat.mul(s, Nat.div(bps, 4n)), old, Nil{}), Nil{}))

# whether the FATs are mirrored, and the active FAT (FAT32 BPB_ExtFlags)
def FatW.mirrored(b: P.FatBpb, t: P.FatType) -> Bool:
  match b:
    case P.FatBpb{jump, oem, bps, spc, rsvd, nfats, rootent, tot16, media, fatsz16, spt, heads, hidden, tot32, fatsz32, +flags, ver, rootclus, fsinfo, bk, sig}:
      Bool.or(Bool.not(FatW.is_fat32(t)), U32.is_eq(U32.and(128, flags), 0))

# data written at offset off of each of n FATs, size bytes apart
def FatW.copies(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, n: Nat, +at: Nat, +size: Nat, +off: Nat, +data: B.Octets) -> I.FatRun<Dv, Unit>:
  match n:
    case 0n:
      I.FatRun.pure(Dv, Unit, Unit{})
    case 1n+p:
      do I.FatRun<Dv, Unit>:
        I.FatOIo.write(~Dv, ~block_size, ~read_block, ~write_block, Nat.add(at, off), data)
        FatW.copies(~Dv, ~block_size, ~read_block, ~write_block, p, Nat.add(at, size), size, off, data)

def FatW.fat0_of(w: FatW) -> Nat:
  match w:
    case FatW{fs, o, m, f, h, c, dy, i, z}:
      z

def FatW.flush.sector(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +w: FatW, +s: Nat) -> I.FatRun<Dv, Unit>:
  +vol = FatW.volume(w)
  +bps = P.FatVolume.sector(vol)
  +off = Nat.mul(s, bps)
  +b = M.FatFs.bpb(FatW.fs(w))
  +all = FatW.mirrored(b, FatW.kind(w))
  +size = P.FatVolume.fat_bytes(vol)
  do I.FatRun<Dv, Unit>:
    +old : B.Octets <- I.FatOIo.read(~Dv, ~block_size, ~read_block, Nat.add(P.FatVolume.fat_start(vol), off), bps)
    +new : B.Octets = FatW.encode(FatW.kind(w), FatW.map(w), s, bps, B.Octets.to_list(old))
    FatW.copies(~Dv, ~block_size, ~read_block, ~write_block, FatW.pick_nat(all, P.FatVolume.fats(vol), 1n), FatW.pick_nat(all, FatW.fat0_of(w), P.FatVolume.fat_start(vol)), size, off, new)

def FatW.flush.sectors(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, ss: List<&2, Nat>, +w: FatW) -> I.FatRun<Dv, Unit>:
  match ss:
    case Nil{}:
      I.FatRun.pure(Dv, Unit, Unit{})
    case Con{+s, t}:
      do I.FatRun<Dv, Unit>:
        FatW.flush.sector(~Dv, ~block_size, ~read_block, ~write_block, w, s)
        FatW.flush.sectors(~Dv, ~block_size, ~read_block, ~write_block, t, w)

def FatW.info_on(w: FatW) -> Bool:
  match w:
    case FatW{fs, o, m, f, h, c, dy, i, z}:
      i

def FatW.dirty(w: FatW) -> List<&2, Nat>:
  match w:
    case FatW{fs, o, m, f, h, c, dy, i, z}:
      dy

def FatW.clean(w: FatW) -> FatW:
  match w:
    case FatW{fs, o, m, f, h, c, dy, i, z}:
      FatW{fs, o, m, f, h, c, Nil{}, i, z}

def FatW.flush.info(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, on: Bool, +w: FatW) -> I.FatRun<Dv, Unit>:
  match on:
    case False{}:
      I.FatRun.pure(Dv, Unit, Unit{})
    case True{}:
      I.FatOIo.write(~Dv, ~block_size, ~read_block, ~write_block, Nat.add(FatW.fs_info_at(M.FatFs.bpb(FatW.fs(w))), 488n), B.Octets.of_list(B.append(B.le32(U32.from_nat(FatW.free_clusters(w))), B.le32(U32.from_nat(FatW.hint(w))))))

# the changed FAT sectors written to every FAT copy, and FSInfo; the state
# after (nothing left to write)
def FatW.flush(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +w: FatW) -> I.FatRun<Dv, FatW>:
  +ds = FatW.dirty(w)
  do I.FatRun<Dv, FatW>:
    FatW.flush.sectors(~Dv, ~block_size, ~read_block, ~write_block, FatW.sectors(ds, FatW.kind(w), P.FatVolume.sector(FatW.volume(w))), w)
    FatW.flush.info(~Dv, ~block_size, ~read_block, ~write_block, Bool.and(FatW.info_on(w), Bool.not(List.is_empty(&2, Nat, ds))), w)
    return FatW.clean(w)

# Allocation on the state

def FatW.append_nat(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, FatW.append_nat(t, ys)}

def FatW.len(xs: List<&2, Nat>, +n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      FatW.len(t, Nat.add(n, 1n))

def FatW.last(xs: List<&2, Nat>, +d: Nat) -> Nat:
  match xs:
    case Nil{}:
      d
    case Con{h, t}:
      FatW.last(t, h)

# the state after an allocation: its map, k fewer free clusters, the hint
# just past its last cluster (wrapping to cluster 2 past the last cluster
# of the volume), and its clusters (and extra) to flush
def FatW.took(w: FatW, a: A.FatAlloc, +extra: List<&2, Nat>) -> FatW:
  match w a:
    case FatW{fs, o, m, +f, +h, c, dy, i, z} A.FatAlloc{+m2, +cs}:
      +n = FatW.len(cs, 0n)
      FatW{fs, o, m2, Nat.sub(f, n), A.FatMap.wrap(m2, Nat.add(FatW.last(cs, Nat.sub(h, 1n)), 1n)), c, FatW.append_nat(cs, FatW.append_nat(extra, dy)), i, z}

# the state with the clusters cs freed
def FatW.release(w: FatW, +cs: List<&2, Nat>) -> FatW:
  match w:
    case FatW{fs, o, m, +f, h, c, dy, i, z}:
      FatW{fs, o, A.FatMap.free(cs, m), Nat.add(f, FatW.len(cs, 0n)), h, c, FatW.append_nat(cs, dy), i, z}

# the state with cluster c made the end of its chain
def FatW.cut(w: FatW, +c: Nat) -> FatW:
  match w:
    case FatW{fs, o, m, f, h, c0, dy, i, z}:
      FatW{fs, o, A.FatMap.cut(m, c), f, h, c0, Con{c, dy}, i, z}

# A chain grown by k clusters: the state after, and the chain
type FatGrown is Data:
  FatGrown{w: FatW, chain: List<&2, Nat>, added: List<&2, Nat>}

def FatW.grow.got(+w: FatW, +chain: List<&2, Nat>, +extra: List<&2, Nat>, a: A.FatAlloc) -> FatGrown:
  match a:
    case A.FatAlloc{m2, +cs}:
      FatGrown{FatW.took(w, A.FatAlloc{m2, cs}, extra), FatW.append_nat(chain, cs), cs}

def FatW.grow.go(none: Bool, empty: Bool, +w: FatW, +chain: List<&2, Nat>, +k: Nat) -> Result<&2, &2, E.FatError, FatGrown>:
  match none empty:
    case True{} _:
      Done{FatGrown{w, chain, Nil{}}}
    case False{} True{}:
      do Result<&2, &2, E.FatError, FatGrown>:
        +a : A.FatAlloc <- A.FatMap.alloc(FatW.map(w), FatW.start(w), k)
        return FatW.grow.got(w, chain, Nil{}, a)
    case False{} False{}:
      +last = FatW.last(chain, 0n)
      do Result<&2, &2, E.FatError, FatGrown>:
        +a : A.FatAlloc <- A.FatMap.extend(FatW.map(w), last, FatW.start(w), k)
        return FatW.grow.got(w, chain, [last], a)

# chain grown by k clusters (a new chain when it is empty), first fit from
# the state's start (FatDiskFull when k are not free)
def FatW.grow(+w: FatW, +chain: List<&2, Nat>, +k: Nat) -> Result<&2, &2, E.FatError, FatGrown>:
  FatW.grow.go(Nat.is_eq(k, 0n), List.is_empty(&2, Nat, chain), w, chain, k)

def FatGrown.w(g: FatGrown) -> FatW:
  match g:
    case FatGrown{w, c, a}:
      w

def FatGrown.chain(g: FatGrown) -> List<&2, Nat>:
  match g:
    case FatGrown{w, c, a}:
      c

def FatGrown.added(g: FatGrown) -> List<&2, Nat>:
  match g:
    case FatGrown{w, c, a}:
      a

# clusters zeroed on the device
def FatW.zero_clusters(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, cs: List<&2, Nat>, +vol: P.FatVolume) -> I.FatRun<Dv, Unit>:
  match cs:
    case Nil{}:
      I.FatRun.pure(Dv, Unit, Unit{})
    case Con{c, t}:
      do I.FatRun<Dv, Unit>:
        I.FatOIo.zero(~Dv, ~block_size, ~read_block, ~write_block, P.FatVolume.cluster_offset(vol, U32.from_nat(c)), P.FatVolume.cluster_bytes(vol))
        FatW.zero_clusters(~Dv, ~block_size, ~read_block, ~write_block, t, vol)

# File data through a chain

# src written from byte within of the first cluster of cs on (left: its
# bytes still to write; done: once none are)
def FatW.put_range.go(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, cs: List<&2, Nat>, done: Bool, +vol: P.FatVolume, +within: Nat, +left: Nat, +src: I.FatSrc) -> I.FatRun<Dv, Unit>:
  match cs done:
    case _ True{}:
      I.FatRun.pure(Dv, Unit, Unit{})
    case Nil{} False{}:
      I.FatRun.pure(Dv, Unit, Unit{})
    case Con{c, t} False{}:
      +k = Nat.min(Nat.sub(P.FatVolume.cluster_bytes(vol), within), left)
      +left2 = Nat.sub(left, k)
      do I.FatRun<Dv, Unit>:
        I.FatOIo.write_src(~Dv, ~block_size, ~read_block, ~write_block, Nat.add(P.FatVolume.cluster_offset(vol, U32.from_nat(c)), within), I.FatSrc.head(k, src))
        FatW.put_range.go(~Dv, ~block_size, ~read_block, ~write_block, t, Nat.is_eq(left2, 0n), vol, 0n, left2, I.FatSrc.drop(k, src))

def FatW.drop_nat(n: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      xs
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          FatW.drop_nat(p, t)

def FatW.take_nat(n: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          Con{h, FatW.take_nat(p, t)}

# src written at byte off of the file whose clusters are chain
def FatW.put_range(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +chain: List<&2, Nat>, +vol: P.FatVolume, +off: Nat, +src: I.FatSrc) -> I.FatRun<Dv, Unit>:
  +cb = P.FatVolume.cluster_bytes(vol)
  +len = I.FatSrc.len(src)
  FatW.put_range.go(~Dv, ~block_size, ~read_block, ~write_block, FatW.drop_nat(Nat.div(off, cb), chain), Nat.is_eq(len, 0n), vol, Nat.mod(off, cb), len, src)

# len bytes of the file whose clusters are chain, from byte off (pieces of
# at most a cluster, reversed onto acc)
def FatW.get_range.go(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, cs: List<&2, Nat>, done: Bool, +vol: P.FatVolume, +within: Nat, +left: Nat, acc: List<&2, B.Octets>) -> I.FatRun<Dv, List<&2, B.Octets>>:
  match cs done:
    case _ True{}:
      I.FatRun.pure(Dv, List<&2, B.Octets>, acc)
    case Nil{} False{}:
      I.FatRun.fail(Dv, List<&2, B.Octets>, E.FatChainShort{})
    case Con{c, t} False{}:
      +k = Nat.min(Nat.sub(P.FatVolume.cluster_bytes(vol), within), left)
      do I.FatRun<Dv, List<&2, B.Octets>>:
        +o : B.Octets <- I.FatOIo.read(~Dv, ~block_size, ~read_block, Nat.add(P.FatVolume.cluster_offset(vol, U32.from_nat(c)), within), k)
        FatW.get_range.go(~Dv, ~block_size, ~read_block, t, Nat.is_eq(Nat.sub(left, k), 0n), vol, 0n, Nat.sub(left, k), Con{o, acc})

def FatW.rev_octets(xs: List<&2, B.Octets>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      FatW.rev_octets(t, Con{h, acc})

def FatW.get_range(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, +chain: List<&2, Nat>, +vol: P.FatVolume, +off: Nat, +len: Nat) -> I.FatRun<Dv, B.Octets>:
  +cb = P.FatVolume.cluster_bytes(vol)
  do I.FatRun<Dv, B.Octets>:
    +ps : List<&2, B.Octets> <- FatW.get_range.go(~Dv, ~block_size, ~read_block, FatW.drop_nat(Nat.div(off, cb), chain), Nat.is_eq(len, 0n), vol, Nat.mod(off, cb), len, Nil{})
    return B.Octets.concat(FatW.rev_octets(ps, Nil{}))

# Directory entries

def FatW.entry(+name: B.Octets, +nt: U32, +attr: U32, +cluster: Nat, +size: U32, +now: FatClock) -> R.FatDirent:
  +c = U32.from_nat(cluster)
  +d = FatClock.date(now)
  +t = FatClock.time(now)
  R.FatDirent{name, attr, nt, FatClock.tenth(now), t, d, d, U32.shrn(c, 16n), t, d, U32.and(65535, c), size}

# an entry with its first cluster, size, write time and access date changed,
# and ATTR_ARCHIVE set (it has been written)
def FatW.written(d: R.FatDirent, +cluster: Nat, +size: U32, +now: FatClock) -> R.FatDirent:
  match d:
    case R.FatDirent{name, +attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, s}:
      +c = U32.from_nat(cluster)
      +day = FatClock.date(now)
      R.FatDirent{name, U32.or(attr, R.FatAttr.archive()), nt, tenth, ctime, cdate, day, U32.shrn(c, 16n), FatClock.time(now), day, U32.and(65535, c), size}

def FatW.renamed(d: R.FatDirent, +name: B.Octets, +nt: U32) -> R.FatDirent:
  match d:
    case R.FatDirent{n0, attr, nt0, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, s}:
      R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, s}

def FatW.timed(d: R.FatDirent, t: FatTimes) -> R.FatDirent:
  match d t:
    case R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, s} FatTimes{+c, +w, +a}:
      R.FatDirent{name, attr, nt, FatClock.tenth(c), FatClock.time(c), FatClock.date(c), R.FatDate.encode(a), hi, FatClock.time(w), FatClock.date(w), lo, s}

# an entry's attributes: read-only, hidden, system and archive from a (the
# directory and volume-label bits kept as they were)
def FatW.attred(d: R.FatDirent, +a: U32) -> R.FatDirent:
  match d:
    case R.FatDirent{name, +attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, s}:
      R.FatDirent{name, U32.or(U32.and(24, attr), U32.and(39, a)), nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, s}

def FatW.relinked(d: R.FatDirent, +cluster: Nat) -> R.FatDirent:
  match d:
    case R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, s}:
      +c = U32.from_nat(cluster)
      R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, U32.shrn(c, 16n), wtime, wdate, U32.and(65535, c), s}

def FatW.lfns(es: List<&2, R.FatLfn>, tail: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match es:
    case Nil{}:
      tail
    case Con{h, t}:
      Con{R.FatLfn.encode(h), FatW.lfns(t, tail)}

def FatW.entries.go(long: List<&2, U32>, +short: B.Octets, +d: R.FatDirent) -> List<&2, B.Octets>:
  match long:
    case Nil{}:
      [R.FatDirent.encode(d)]
    case Con{h, t}:
      FatW.lfns(R.FatLfn.build(short, Con{h, t}), [R.FatDirent.encode(d)])

# the 32-byte entries a node is stored as: its long-name entries (if any),
# then its short entry
def FatW.entries(a: L.FatAlias, +d: R.FatDirent) -> List<&2, B.Octets>:
  match a:
    case L.FatAlias{+s, nt, long}:
      FatW.entries.go(long, s, d)

def FatW.len_octets(xs: List<&2, B.Octets>, +n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      FatW.len_octets(t, Nat.add(n, 1n))

# Where new entries go: the first free run of k entries of a directory, the
# directory grown (zeroed clusters linked onto its chain) when it needs more

type FatPlace is Data:
  FatPlace{w: FatW, sectors: List<&2, Nat>, start: Nat, added: List<&2, Nat>}

def FatPlace.w(p: FatPlace) -> FatW:
  match p:
    case FatPlace{w, ss, i, a}:
      w

def FatPlace.sectors(p: FatPlace) -> List<&2, Nat>:
  match p:
    case FatPlace{w, ss, i, a}:
      ss

def FatPlace.start(p: FatPlace) -> Nat:
  match p:
    case FatPlace{w, ss, i, a}:
      i

def FatPlace.added(p: FatPlace) -> List<&2, Nat>:
  match p:
    case FatPlace{w, ss, i, a}:
      a

def FatW.rev_nat(xs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      FatW.rev_nat(t, Con{h, acc})

def FatW.place.grown(+v: W.FatDirView, +start: Nat, g: FatGrown) -> FatPlace:
  match g:
    case FatGrown{+w, ch, +added}:
      FatPlace{w, FatW.append_nat(W.FatDirView.sectors(v), FatW.rev_nat(W.FatDirView.chain_sectors(added, FatW.volume(w), Nil{}), Nil{})), start, added}

def FatW.place.go(fits: Bool, +w: FatW, +v: W.FatDirView, +start: Nat, +need: Nat) -> Result<&2, &2, E.FatError, FatPlace>:
  match fits:
    case True{}:
      Done{FatPlace{w, W.FatDirView.sectors(v), start, Nil{}}}
    case False{}:
      +per = Nat.div(FatW.cbytes(w), 32n)
      do Result<&2, &2, E.FatError, FatPlace>:
        +u : Unit <- P.Fat.require(Bool.not(W.FatDirView.fixed(v)), E.FatRootFull{})
        +g : FatGrown <- FatW.grow(w, W.FatDirView.clusters(v), Nat.div(Nat.add(Nat.sub(need, W.FatDirView.slots(v)), Nat.sub(per, 1n)), per))
        return FatW.place.grown(v, start, g)

# k entries placed in the directory v (FatDirFull past 65536 entries,
# FatRootFull when the fixed root has no room, FatDiskFull)
def FatW.place(+w: FatW, +v: W.FatDirView, +k: Nat) -> Result<&2, &2, E.FatError, FatPlace>:
  +start = W.FatDirView.place(v, k)
  +need = Nat.add(start, k)
  do Result<&2, &2, E.FatError, FatPlace>:
    +u : Unit <- P.Fat.require(Nat.is_le(need, 65536n), E.FatDirFull{})
    FatW.place.go(Nat.is_le(need, W.FatDirView.slots(v)), w, v, start, need)

# the entries es written where p placed them (new clusters zeroed first)
def FatW.place.write(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +p: FatPlace, es: List<&2, B.Octets>) -> I.FatRun<Dv, Unit>:
  +vol = FatW.volume(FatPlace.w(p))
  do I.FatRun<Dv, Unit>:
    FatW.zero_clusters(~Dv, ~block_size, ~read_block, ~write_block, FatPlace.added(p), vol)
    W.FatDirView.put(~Dv, ~block_size, ~read_block, ~write_block, es, FatPlace.sectors(p), Nat.div(P.FatVolume.sector(vol), 32n), FatPlace.start(p))

def FatW.dir_cluster(d: Q.FatDir) -> Nat:
  match d:
    case Q.FatDirRoot{}:
      0n
    case Q.FatDirAt{c}:
      U32.to_nat(c)

def FatW.same_dir(a: Q.FatDir, b: Q.FatDir) -> Bool:
  match a b:
    case Q.FatDirRoot{} Q.FatDirRoot{}:
      True{}
    case Q.FatDirAt{x} Q.FatDirAt{y}:
      U32.is_eq(x, y)
    case _ _:
      False{}

# Paths

# a path's components, as names are stored (leading spaces, and trailing
# spaces and periods, ignored)
def FatW.parts.go(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      Con{L.FatAlias.text(L.FatAlias.trim(L.FatAlias.codes(s))), FatW.parts.go(t)}

def FatW.parts(s: String) -> List<&2, String>:
  FatW.parts.go(Q.FatPath.parts(s))

def FatW.hit(m: Maybe<&2, W.FatHit>) -> Result<&2, &2, E.FatError, W.FatHit>:
  match m:
    case Some{h}:
      Done{h}
    case None{}:
      Fail{E.FatNotFound{}}

def FatW.load(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, +w: FatW, d: Q.FatDir) -> I.FatRun<Dv, W.FatDirView>:
  W.FatDirView.load(~Dv, ~block_size, ~read_block, FatW.options(w), FatW.volume(w), FatW.map(w), d)

# The directory a list of components names, and the clusters of the
# directories on the way (root first, 0 for the root)
type FatWay is Data:
  FatWay{dir: Q.FatDir, seen: List<&2, Nat>}

def FatWay.dir(x: FatWay) -> Q.FatDir:
  match x:
    case FatWay{d, s}:
      d

def FatWay.seen(x: FatWay) -> List<&2, Nat>:
  match x:
    case FatWay{d, s}:
      s

def FatW.walk(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, parts: List<&2, String>, +w: FatW, +here: Q.FatDir, +seen: List<&2, Nat>) -> I.FatRun<Dv, FatWay>:
  match parts:
    case Nil{}:
      I.FatRun.pure(Dv, FatWay, FatWay{here, seen})
    case Con{c, t}:
      do I.FatRun<Dv, FatWay>:
        +v : W.FatDirView <- FatW.load(~Dv, ~block_size, ~read_block, w, here)
        +h : W.FatHit <- I.FatRun.lift(Dv, W.FatHit, FatW.hit(W.FatDirView.find(v, c)))
        +d : Q.FatDir <- I.FatRun.lift(Dv, Q.FatDir, Q.FatPath.dir(Q.FatPathNode{W.FatHit.node(h)}))
        FatW.walk(~Dv, ~block_size, ~read_block, t, w, d, Con{FatW.dir_cluster(d), seen})

def FatW.init.go(xs: List<&2, String>, h: String) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h2, t}:
      Con{h, FatW.init.go(t, h2)}

# every component but the last
def FatW.init(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      FatW.init.go(t, h)

def FatW.final(xs: List<&2, String>, d: String) -> String:
  match xs:
    case Nil{}:
      d
    case Con{h, t}:
      FatW.final(t, h)

# What a path names: the root, or a node with the directory it is in
type FatWLoc is Data:
  FatWLocRoot{}
  FatWLocNode{parent: W.FatDirView, hit: W.FatHit}

def FatW.locate.go(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, +parts: List<&2, String>, +w: FatW) -> I.FatRun<Dv, FatWLoc>:
  do I.FatRun<Dv, FatWLoc>:
    +way : FatWay <- FatW.walk(~Dv, ~block_size, ~read_block, FatW.init(parts), w, Q.FatDirRoot{}, [0n])
    +v : W.FatDirView <- FatW.load(~Dv, ~block_size, ~read_block, w, FatWay.dir(way))
    +h : W.FatHit <- I.FatRun.lift(Dv, W.FatHit, FatW.hit(W.FatDirView.find(v, FatW.final(parts, ""))))
    return FatWLocNode{v, h}

def FatW.locate.pick(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, empty: Bool, +parts: List<&2, String>, +w: FatW) -> I.FatRun<Dv, FatWLoc>:
  match empty:
    case True{}:
      I.FatRun.pure(Dv, FatWLoc, FatWLocRoot{})
    case False{}:
      FatW.locate.go(~Dv, ~block_size, ~read_block, parts, w)

# what a path names
def FatW.locate(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, +w: FatW, path: String) -> I.FatRun<Dv, FatWLoc>:
  +parts = FatW.parts(path)
  FatW.locate.pick(~Dv, ~block_size, ~read_block, List.is_empty(&2, String, parts), parts, w)

# A new name's place: the directory it goes in (and the clusters of the
# directories on the way to it), and the name as stored
type FatWNew is Data:
  FatWNew{view: W.FatDirView, seen: List<&2, Nat>, name: String}

def FatW.parent.go(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, +parts: List<&2, String>, +w: FatW) -> I.FatRun<Dv, FatWNew>:
  do I.FatRun<Dv, FatWNew>:
    +name : String <- I.FatRun.lift(Dv, String, L.FatAlias.check(FatW.final(parts, "")))
    +way : FatWay <- FatW.walk(~Dv, ~block_size, ~read_block, FatW.init(parts), w, Q.FatDirRoot{}, [0n])
    +v : W.FatDirView <- FatW.load(~Dv, ~block_size, ~read_block, w, FatWay.dir(way))
    return FatWNew{v, FatWay.seen(way), name}

def FatW.parent.pick(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, empty: Bool, +parts: List<&2, String>, +w: FatW) -> I.FatRun<Dv, FatWNew>:
  match empty:
    case True{}:
      I.FatRun.fail(Dv, FatWNew, E.FatExists{})
    case False{}:
      FatW.parent.go(~Dv, ~block_size, ~read_block, parts, w)

# the directory a new path goes in, and its name (FatExists for the root)
def FatW.parent(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, +w: FatW, path: String) -> I.FatRun<Dv, FatWNew>:
  +parts = FatW.parts(path)
  FatW.parent.pick(~Dv, ~block_size, ~read_block, List.is_empty(&2, String, parts), parts, w)

# Operations

def FatW.node(l: FatWLoc) -> Result<&2, &2, E.FatError, FatWLoc>:
  match l:
    case FatWLocRoot{}:
      Fail{E.FatIsRoot{}}
    case FatWLocNode{v, h}:
      Done{FatWLocNode{v, h}}

def FatWLoc.view(l: FatWLoc) -> W.FatDirView:
  match l:
    case FatWLocRoot{}:
      W.FatDirView{Q.FatDirRoot{}, True{}, Nil{}, Nil{}, 0n, Nil{}, 0n, Q.FatScan.start(P.FatOptions.default(), Q.FatWantAll{})}
    case FatWLocNode{v, h}:
      v

def FatWLoc.hit(l: FatWLoc) -> W.FatHit:
  match l:
    case FatWLocRoot{}:
      W.FatHit{Q.FatNode{Nil{}, R.FatDirent{B.Octets.empty(), 16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}}, Q.FatSpan{0n, 0n}}
    case FatWLocNode{v, h}:
      h

def FatW.absent(m: Maybe<&2, W.FatHit>) -> Result<&2, &2, E.FatError, Unit>:
  match m:
    case None{}:
      Done{Unit{}}
    case Some{h}:
      Fail{E.FatExists{}}

def FatW.dot(+name: String, +cluster: Nat, +now: FatClock) -> B.Octets:
  R.FatDirent.encode(FatW.entry(B.Octets.of_string(name), 0, R.FatAttr.directory(), cluster, 0, now))

# a new directory's first cluster: zeroed, with "." and ".." (cluster 0 for
# the root as parent)
def FatW.mkdir.init(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +w: FatW, +c: Nat, +parent: Nat) -> I.FatRun<Dv, Unit>:
  +vol = FatW.volume(w)
  +at = P.FatVolume.cluster_offset(vol, U32.from_nat(c))
  do I.FatRun<Dv, Unit>:
    I.FatOIo.zero(~Dv, ~block_size, ~read_block, ~write_block, at, P.FatVolume.cluster_bytes(vol))
    I.FatOIo.write(~Dv, ~block_size, ~read_block, ~write_block, at, B.Octets.append(FatW.dot(".", c, FatW.clock(w)), FatW.dot("..", parent, FatW.clock(w))))

# the first cluster of a new node: one cluster for a directory, none for a
# file
def FatW.first(dir: Bool, +w: FatW) -> Result<&2, &2, E.FatError, FatGrown>:
  match dir:
    case True{}:
      FatW.grow(w, Nil{}, 1n)
    case False{}:
      Done{FatGrown{w, Nil{}, Nil{}}}

def FatW.head(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      h

def FatW.made.dir(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, dir: Bool, +w: FatW, +c: Nat, +parent: Nat) -> I.FatRun<Dv, Unit>:
  match dir:
    case True{}:
      FatW.mkdir.init(~Dv, ~block_size, ~read_block, ~write_block, w, c, parent)
    case False{}:
      I.FatRun.pure(Dv, Unit, Unit{})

def FatWNew.view(p: FatWNew) -> W.FatDirView:
  match p:
    case FatWNew{v, s, n}:
      v

def FatWNew.seen(p: FatWNew) -> List<&2, Nat>:
  match p:
    case FatWNew{v, s, n}:
      s

def FatWNew.name(p: FatWNew) -> String:
  match p:
    case FatWNew{v, s, n}:
      n

# a new file (dir False) or directory at path
def FatW.make(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +dir: Bool, +w: FatW, path: String) -> I.FatRun<Dv, FatW>:
  do I.FatRun<Dv, FatW>:
    +p : FatWNew <- FatW.parent(~Dv, ~block_size, ~read_block, w, path)
    +v : W.FatDirView = FatWNew.view(p)
    +name : String = FatWNew.name(p)
    +u : Unit <- I.FatRun.lift(Dv, Unit, FatW.absent(W.FatDirView.find(v, name)))
    +a : L.FatAlias <- I.FatRun.lift(Dv, L.FatAlias, L.FatAlias.make(FatW.nt_case(w), name, W.FatDirView.taken(v)))
    +g : FatGrown <- I.FatRun.lift(Dv, FatGrown, FatW.first(dir, w))
    +c : Nat = FatW.head(FatGrown.chain(g))
    +es : List<&2, B.Octets> = FatW.entries(a, FatW.entry(L.FatAlias.short(a), L.FatAlias.nt(a), FatW.pick_u32(dir, R.FatAttr.directory(), R.FatAttr.archive()), c, 0, FatW.clock(w)))
    +pl : FatPlace <- I.FatRun.lift(Dv, FatPlace, FatW.place(FatGrown.w(g), v, FatW.len_octets(es, 0n)))
    FatW.made.dir(~Dv, ~block_size, ~read_block, ~write_block, dir, FatPlace.w(pl), c, FatW.dir_cluster(W.FatDirView.dir(v)))
    FatW.place.write(~Dv, ~block_size, ~read_block, ~write_block, pl, es)
    FatW.flush(~Dv, ~block_size, ~read_block, ~write_block, FatPlace.w(pl))

# A node to change: the directory it is in, where its entries are, its
# short entry
def FatW.per(w: FatW) -> Nat:
  Nat.div(P.FatVolume.sector(FatW.volume(w)), 32n)

def FatW.rewrite(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +w: FatW, +v: W.FatDirView, +h: W.FatHit, d: R.FatDirent) -> I.FatRun<Dv, Unit>:
  I.FatOIo.write(~Dv, ~block_size, ~read_block, ~write_block, W.FatDirView.slot(W.FatDirView.sectors(v), FatW.per(w), Q.FatSpan.last(W.FatHit.span(h))), R.FatDirent.encode(d))

def FatW.erase(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +w: FatW, +v: W.FatDirView, +h: W.FatHit) -> I.FatRun<Dv, Unit>:
  +sp = W.FatHit.span(h)
  W.FatDirView.erase(~Dv, ~block_size, ~read_block, ~write_block, Nat.add(Nat.sub(Q.FatSpan.last(sp), Q.FatSpan.first(sp)), 1n), W.FatDirView.sectors(v), FatW.per(w), Q.FatSpan.first(sp))

def FatW.file(+w: FatW, +h: W.FatHit, write: Bool) -> Result<&2, &2, E.FatError, Unit>:
  +e = Q.FatNode.entry(W.FatHit.node(h))
  do Result<&2, &2, E.FatError, Unit>:
    +u0 : Unit <- P.Fat.require(Bool.not(R.FatDirent.is_dir(e)), E.FatIsADirectory{})
    P.Fat.require(Bool.not(Bool.and(Bool.and(write, FatW.respect_ro(w)), R.FatDirent.has_attr(e, R.FatAttr.read_only()))), E.FatReadOnly{})

def FatW.size(+h: W.FatHit) -> Nat:
  U32.to_nat(Q.FatNode.size(W.FatHit.node(h)))

def FatW.cluster(+h: W.FatHit) -> Nat:
  U32.to_nat(Q.FatNode.cluster(W.FatHit.node(h)))

# src written at byte off of the file h names (the file grown, and a gap
# past its end zeroed)
def FatW.put(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +w: FatW, +v: W.FatDirView, +h: W.FatHit, +off: Nat, +src: I.FatSrc) -> I.FatRun<Dv, FatW>:
  +size = FatW.size(h)
  +end = Nat.add(off, I.FatSrc.len(src))
  +new = Nat.max(size, end)
  +cb = FatW.cbytes(w)
  do I.FatRun<Dv, FatW>:
    +u : Unit <- I.FatRun.lift(Dv, Unit, P.Fat.require(Nat.is_le(new, 4294967295n), E.FatFileTooLarge{}))
    +chain : List<&2, Nat> <- I.FatRun.lift(Dv, List<&2, Nat>, A.FatMap.chain(FatW.map(w), FatW.cluster(h)))
    +g : FatGrown <- I.FatRun.lift(Dv, FatGrown, FatW.grow(w, chain, Nat.sub(Nat.div(Nat.add(new, Nat.sub(cb, 1n)), cb), FatW.len(chain, 0n))))
    +vol : P.FatVolume = FatW.volume(w)
    FatW.put_range(~Dv, ~block_size, ~read_block, ~write_block, FatGrown.chain(g), vol, size, I.FatSrcZeros{Nat.sub(off, size)})
    FatW.put_range(~Dv, ~block_size, ~read_block, ~write_block, FatGrown.chain(g), vol, off, src)
    FatW.rewrite(~Dv, ~block_size, ~read_block, ~write_block, w, v, h, FatW.written(Q.FatNode.entry(W.FatHit.node(h)), FatW.head(FatGrown.chain(g)), U32.from_nat(new), FatW.clock(w)))
    FatW.flush(~Dv, ~block_size, ~read_block, ~write_block, FatGrown.w(g))

def FatW.at_file(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, +w: FatW, path: String, write: Bool) -> I.FatRun<Dv, FatWLoc>:
  do I.FatRun<Dv, FatWLoc>:
    +l0 : FatWLoc <- FatW.locate(~Dv, ~block_size, ~read_block, w, path)
    +l : FatWLoc <- I.FatRun.lift(Dv, FatWLoc, FatW.node(l0))
    +u : Unit <- I.FatRun.lift(Dv, Unit, FatW.file(w, FatWLoc.hit(l), write))
    return l

# data written at byte off of the file at path
def FatW.write.steps(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +w: FatW, path: String, +off: Nat, data: B.Octets) -> I.FatRun<Dv, FatW>:
  do I.FatRun<Dv, FatW>:
    +l : FatWLoc <- FatW.at_file(~Dv, ~block_size, ~read_block, w, path, True{})
    FatW.put(~Dv, ~block_size, ~read_block, ~write_block, w, FatWLoc.view(l), FatWLoc.hit(l), off, I.FatSrcBytes{data})

# data written at the end of the file at path
def FatW.append.steps(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +w: FatW, path: String, data: B.Octets) -> I.FatRun<Dv, FatW>:
  do I.FatRun<Dv, FatW>:
    +l : FatWLoc <- FatW.at_file(~Dv, ~block_size, ~read_block, w, path, True{})
    FatW.put(~Dv, ~block_size, ~read_block, ~write_block, w, FatWLoc.view(l), FatWLoc.hit(l), FatW.size(FatWLoc.hit(l)), I.FatSrcBytes{data})

def FatW.shrink.cut(none: Bool, +w: FatW, +last: Nat) -> FatW:
  match none:
    case True{}:
      w
    case False{}:
      FatW.cut(w, last)

def FatW.shrink(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +w: FatW, +v: W.FatDirView, +h: W.FatHit, +size: Nat) -> I.FatRun<Dv, FatW>:
  +cb = FatW.cbytes(w)
  +keep = Nat.div(Nat.add(size, Nat.sub(cb, 1n)), cb)
  do I.FatRun<Dv, FatW>:
    +chain : List<&2, Nat> <- I.FatRun.lift(Dv, List<&2, Nat>, A.FatMap.chain(FatW.map(w), FatW.cluster(h)))
    +w1 : FatW = FatW.release(w, FatW.drop_nat(keep, chain))
    +w2 : FatW = FatW.shrink.cut(Nat.is_eq(keep, 0n), w1, FatW.last(FatW.take_nat(keep, chain), 0n))
    FatW.rewrite(~Dv, ~block_size, ~read_block, ~write_block, w, v, h, FatW.written(Q.FatNode.entry(W.FatHit.node(h)), FatW.pick_nat(Nat.is_eq(keep, 0n), 0n, FatW.head(chain)), U32.from_nat(size), FatW.clock(w)))
    FatW.flush(~Dv, ~block_size, ~read_block, ~write_block, w2)

def FatW.truncate.go(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, grow: Bool, +w: FatW, +v: W.FatDirView, +h: W.FatHit, +size: Nat) -> I.FatRun<Dv, FatW>:
  match grow:
    case True{}:
      FatW.put(~Dv, ~block_size, ~read_block, ~write_block, w, v, h, FatW.size(h), I.FatSrcZeros{Nat.sub(size, FatW.size(h))})
    case False{}:
      FatW.shrink(~Dv, ~block_size, ~read_block, ~write_block, w, v, h, size)

# the file at path cut, or grown with zeros, to size bytes
def FatW.truncate.steps(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +w: FatW, path: String, +size: Nat) -> I.FatRun<Dv, FatW>:
  do I.FatRun<Dv, FatW>:
    +l : FatWLoc <- FatW.at_file(~Dv, ~block_size, ~read_block, w, path, True{})
    FatW.truncate.go(~Dv, ~block_size, ~read_block, ~write_block, Nat.is_gt(size, FatW.size(FatWLoc.hit(l))), w, FatWLoc.view(l), FatWLoc.hit(l), size)

# the file at path deleted: its clusters freed, its entries erased
def FatW.unlink.steps(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +w: FatW, path: String) -> I.FatRun<Dv, FatW>:
  do I.FatRun<Dv, FatW>:
    +l : FatWLoc <- FatW.at_file(~Dv, ~block_size, ~read_block, w, path, True{})
    +chain : List<&2, Nat> <- I.FatRun.lift(Dv, List<&2, Nat>, A.FatMap.chain(FatW.map(w), FatW.cluster(FatWLoc.hit(l))))
    FatW.erase(~Dv, ~block_size, ~read_block, ~write_block, w, FatWLoc.view(l), FatWLoc.hit(l))
    FatW.flush(~Dv, ~block_size, ~read_block, ~write_block, FatW.release(w, chain))

def FatW.empty(+v: W.FatDirView) -> Result<&2, &2, E.FatError, Unit>:
  P.Fat.require(List.is_empty(&2, Q.FatNode, W.FatDirView.nodes(v)), E.FatNotEmpty{})

# the empty directory at path deleted
def FatW.rmdir.steps(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +w: FatW, path: String) -> I.FatRun<Dv, FatW>:
  do I.FatRun<Dv, FatW>:
    +l0 : FatWLoc <- FatW.locate(~Dv, ~block_size, ~read_block, w, path)
    +l : FatWLoc <- I.FatRun.lift(Dv, FatWLoc, FatW.node(l0))
    +d : Q.FatDir <- I.FatRun.lift(Dv, Q.FatDir, Q.FatPath.dir(Q.FatPathNode{W.FatHit.node(FatWLoc.hit(l))}))
    +sub : W.FatDirView <- FatW.load(~Dv, ~block_size, ~read_block, w, d)
    +u : Unit <- I.FatRun.lift(Dv, Unit, FatW.empty(sub))
    +chain : List<&2, Nat> <- I.FatRun.lift(Dv, List<&2, Nat>, A.FatMap.chain(FatW.map(w), FatW.dir_cluster(d)))
    FatW.erase(~Dv, ~block_size, ~read_block, ~write_block, w, FatWLoc.view(l), FatWLoc.hit(l))
    FatW.flush(~Dv, ~block_size, ~read_block, ~write_block, FatW.release(w, chain))

# Renaming

def FatW.drop_name.pick(hit: Bool, h: B.Octets, t: List<&2, B.Octets>, rest: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match hit:
    case True{}:
      t
    case False{}:
      Con{h, rest}

def FatW.drop_name(+n: B.Octets, xs: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      FatW.drop_name.pick(B.Octets.is_eq(h, n), h, t, FatW.drop_name(n, t))

def FatW.same_span(a: Q.FatSpan, b: Q.FatSpan) -> Bool:
  match a b:
    case Q.FatSpan{x, y} Q.FatSpan{p, q}:
      Bool.and(Nat.is_eq(x, p), Nat.is_eq(y, q))

# a target name in its directory: free, or the node being renamed itself
# (a change of case)
def FatW.target(m: Maybe<&2, W.FatHit>, +same: Bool, +sp: Q.FatSpan) -> Result<&2, &2, E.FatError, Unit>:
  match m:
    case None{}:
      Done{Unit{}}
    case Some{h}:
      P.Fat.require(Bool.and(same, FatW.same_span(W.FatHit.span(h), sp)), E.FatExists{})

def FatW.member(+x: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(Nat.is_eq(x, h), FatW.member(x, t))

# a directory moved to another directory: its ".." entry (its second)
# relinked to the new parent (0 for the root)
def FatW.reparent(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, move: Bool, +w: FatW, +c: Nat, +parent: Nat) -> I.FatRun<Dv, Unit>:
  match move:
    case False{}:
      I.FatRun.pure(Dv, Unit, Unit{})
    case True{}:
      +at = Nat.add(P.FatVolume.cluster_offset(FatW.volume(w), U32.from_nat(c)), 32n)
      do I.FatRun<Dv, Unit>:
        +o : B.Octets <- I.FatOIo.read(~Dv, ~block_size, ~read_block, at, 32n)
        +d : R.FatDirent <- I.FatRun.lift(Dv, R.FatDirent, R.FatDirent.decode(o))
        I.FatOIo.write(~Dv, ~block_size, ~read_block, ~write_block, at, R.FatDirent.encode(FatW.relinked(d, parent)))

def FatW.taken(same: Bool, +old: B.Octets, +xs: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match same:
    case True{}:
      FatW.drop_name(old, xs)
    case False{}:
      xs

# the node at from moved to the path to (within a directory or across)
def FatW.rename.steps(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +w: FatW, from: String, to: String) -> I.FatRun<Dv, FatW>:
  do I.FatRun<Dv, FatW>:
    +l0 : FatWLoc <- FatW.locate(~Dv, ~block_size, ~read_block, w, from)
    +l : FatWLoc <- I.FatRun.lift(Dv, FatWLoc, FatW.node(l0))
    +va : W.FatDirView = FatWLoc.view(l)
    +h : W.FatHit = FatWLoc.hit(l)
    +n : Q.FatNode = W.FatHit.node(h)
    +isdir : Bool = Q.FatNode.is_dir(n)
    +p : FatWNew <- FatW.parent(~Dv, ~block_size, ~read_block, w, to)
    +vb : W.FatDirView = FatWNew.view(p)
    +same : Bool = FatW.same_dir(W.FatDirView.dir(va), W.FatDirView.dir(vb))
    +u0 : Unit <- I.FatRun.lift(Dv, Unit, P.Fat.require(Bool.not(Bool.and(isdir, FatW.member(U32.to_nat(Q.FatNode.cluster(n)), FatWNew.seen(p)))), E.FatMoveIntoSelf{}))
    +u1 : Unit <- I.FatRun.lift(Dv, Unit, FatW.target(W.FatDirView.find(vb, FatWNew.name(p)), same, W.FatHit.span(h)))
    +old : B.Octets = R.FatDirent.name(Q.FatNode.entry(n))
    +taken : List<&2, B.Octets> = FatW.taken(same, old, W.FatDirView.taken(vb))
    +a : L.FatAlias <- I.FatRun.lift(Dv, L.FatAlias, L.FatAlias.make(FatW.nt_case(w), FatWNew.name(p), taken))
    +es : List<&2, B.Octets> = FatW.entries(a, FatW.renamed(Q.FatNode.entry(n), L.FatAlias.short(a), L.FatAlias.nt(a)))
    +pl : FatPlace <- I.FatRun.lift(Dv, FatPlace, FatW.place(w, vb, FatW.len_octets(es, 0n)))
    FatW.place.write(~Dv, ~block_size, ~read_block, ~write_block, pl, es)
    FatW.erase(~Dv, ~block_size, ~read_block, ~write_block, w, va, h)
    FatW.reparent(~Dv, ~block_size, ~read_block, ~write_block, Bool.and(isdir, Bool.not(same)), w, U32.to_nat(Q.FatNode.cluster(n)), FatW.dir_cluster(W.FatDirView.dir(vb)))
    FatW.flush(~Dv, ~block_size, ~read_block, ~write_block, FatPlace.w(pl))

# the times of the node at path set
def FatW.set_times.steps(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +w: FatW, path: String, +t: FatTimes) -> I.FatRun<Dv, FatW>:
  do I.FatRun<Dv, FatW>:
    +l0 : FatWLoc <- FatW.locate(~Dv, ~block_size, ~read_block, w, path)
    +l : FatWLoc <- I.FatRun.lift(Dv, FatWLoc, FatW.node(l0))
    FatW.rewrite(~Dv, ~block_size, ~read_block, ~write_block, w, FatWLoc.view(l), FatWLoc.hit(l), FatW.timed(Q.FatNode.entry(W.FatHit.node(FatWLoc.hit(l))), t))
    return w

# the attributes of the node at path set (read-only, hidden, system,
# archive; the directory bit stays)
def FatW.set_attr.steps(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, +w: FatW, path: String, +a: U32) -> I.FatRun<Dv, FatW>:
  do I.FatRun<Dv, FatW>:
    +l0 : FatWLoc <- FatW.locate(~Dv, ~block_size, ~read_block, w, path)
    +l : FatWLoc <- I.FatRun.lift(Dv, FatWLoc, FatW.node(l0))
    FatW.rewrite(~Dv, ~block_size, ~read_block, ~write_block, w, FatWLoc.view(l), FatWLoc.hit(l), FatW.attred(Q.FatNode.entry(W.FatHit.node(FatWLoc.hit(l))), a))
    return w

# Reading on the same device

def FatW.stat.of(l: FatWLoc) -> Q.FatPath:
  match l:
    case FatWLocRoot{}:
      Q.FatPathRoot{}
    case FatWLocNode{v, h}:
      Q.FatPathNode{W.FatHit.node(h)}

def FatW.stat.steps(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, +w: FatW, path: String) -> I.FatRun<Dv, Q.FatPath>:
  do I.FatRun<Dv, Q.FatPath>:
    +l : FatWLoc <- FatW.locate(~Dv, ~block_size, ~read_block, w, path)
    return FatW.stat.of(l)

def FatW.list.steps(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, +w: FatW, path: String) -> I.FatRun<Dv, List<&2, Q.FatNode>>:
  do I.FatRun<Dv, List<&2, Q.FatNode>>:
    +p : Q.FatPath <- FatW.stat.steps(~Dv, ~block_size, ~read_block, w, path)
    +d : Q.FatDir <- I.FatRun.lift(Dv, Q.FatDir, Q.FatPath.dir(p))
    +v : W.FatDirView <- FatW.load(~Dv, ~block_size, ~read_block, w, d)
    return W.FatDirView.nodes(v)

def FatW.read.steps(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, +w: FatW, path: String, +off: Nat, +len: Nat) -> I.FatRun<Dv, B.Octets>:
  do I.FatRun<Dv, B.Octets>:
    +l : FatWLoc <- FatW.at_file(~Dv, ~block_size, ~read_block, w, path, False{})
    +h : W.FatHit = FatWLoc.hit(l)
    +size : Nat = FatW.size(h)
    +start : Nat = Nat.min(off, size)
    +chain : List<&2, Nat> <- I.FatRun.lift(Dv, List<&2, Nat>, A.FatMap.chain(FatW.map(w), FatW.cluster(h)))
    FatW.get_range(~Dv, ~block_size, ~read_block, chain, FatW.volume(w), start, Nat.min(len, Nat.sub(size, start)))

# The public operations: each takes a device and answers it with the result

# a volume opened for writing (its boot sector checked, its FAT read)
def FatW.open(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, d: Dv, +opts: P.FatOptions, +wopts: FatWOptions) -> Dv & Result<&2, &2, E.FatError, FatW>:
  I.FatRun.exec(Dv, FatW, FatW.open.steps(~Dv, ~block_size, ~read_block, opts, wopts), d)

# a new empty file (FatExists, FatBadName, FatNotFound for its directory)
def FatW.create(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, d: Dv, +w: FatW, path: String) -> Dv & Result<&2, &2, E.FatError, FatW>:
  I.FatRun.exec(Dv, FatW, FatW.make(~Dv, ~block_size, ~read_block, ~write_block, False{}, w, path), d)

# a new empty directory
def FatW.mkdir(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, d: Dv, +w: FatW, path: String) -> Dv & Result<&2, &2, E.FatError, FatW>:
  I.FatRun.exec(Dv, FatW, FatW.make(~Dv, ~block_size, ~read_block, ~write_block, True{}, w, path), d)

def FatW.write(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, d: Dv, +w: FatW, path: String, +off: Nat, data: B.Octets) -> Dv & Result<&2, &2, E.FatError, FatW>:
  I.FatRun.exec(Dv, FatW, FatW.write.steps(~Dv, ~block_size, ~read_block, ~write_block, w, path, off, data), d)

def FatW.append(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, d: Dv, +w: FatW, path: String, data: B.Octets) -> Dv & Result<&2, &2, E.FatError, FatW>:
  I.FatRun.exec(Dv, FatW, FatW.append.steps(~Dv, ~block_size, ~read_block, ~write_block, w, path, data), d)

def FatW.truncate(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, d: Dv, +w: FatW, path: String, +size: Nat) -> Dv & Result<&2, &2, E.FatError, FatW>:
  I.FatRun.exec(Dv, FatW, FatW.truncate.steps(~Dv, ~block_size, ~read_block, ~write_block, w, path, size), d)

def FatW.unlink(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, d: Dv, +w: FatW, path: String) -> Dv & Result<&2, &2, E.FatError, FatW>:
  I.FatRun.exec(Dv, FatW, FatW.unlink.steps(~Dv, ~block_size, ~read_block, ~write_block, w, path), d)

def FatW.rmdir(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, d: Dv, +w: FatW, path: String) -> Dv & Result<&2, &2, E.FatError, FatW>:
  I.FatRun.exec(Dv, FatW, FatW.rmdir.steps(~Dv, ~block_size, ~read_block, ~write_block, w, path), d)

def FatW.rename(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, d: Dv, +w: FatW, from: String, to: String) -> Dv & Result<&2, &2, E.FatError, FatW>:
  I.FatRun.exec(Dv, FatW, FatW.rename.steps(~Dv, ~block_size, ~read_block, ~write_block, w, from, to), d)

def FatW.set_times(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, d: Dv, +w: FatW, path: String, +t: FatTimes) -> Dv & Result<&2, &2, E.FatError, FatW>:
  I.FatRun.exec(Dv, FatW, FatW.set_times.steps(~Dv, ~block_size, ~read_block, ~write_block, w, path, t), d)

def FatW.set_attr(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Dv & Result<&2, &2, D.DevError, Unit>, d: Dv, +w: FatW, path: String, +a: U32) -> Dv & Result<&2, &2, E.FatError, FatW>:
  I.FatRun.exec(Dv, FatW, FatW.set_attr.steps(~Dv, ~block_size, ~read_block, ~write_block, w, path, a), d)

def FatW.stat(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, d: Dv, +w: FatW, path: String) -> Dv & Result<&2, &2, E.FatError, Q.FatPath>:
  I.FatRun.exec(Dv, Q.FatPath, FatW.stat.steps(~Dv, ~block_size, ~read_block, w, path), d)

def FatW.list(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, d: Dv, +w: FatW, path: String) -> Dv & Result<&2, &2, E.FatError, List<&2, Q.FatNode>>:
  I.FatRun.exec(Dv, List<&2, Q.FatNode>, FatW.list.steps(~Dv, ~block_size, ~read_block, w, path), d)

def FatW.read(~Dv: Type, ~block_size: Dv -> Dv & Nat, ~read_block: Dv -> Nat -> Dv & Result<&2, &2, D.DevError, B.Octets>, d: Dv, +w: FatW, path: String, +off: Nat, +len: Nat) -> Dv & Result<&2, &2, E.FatError, B.Octets>:
  I.FatRun.exec(Dv, B.Octets, FatW.read.steps(~Dv, ~block_size, ~read_block, w, path, off, len), d)
