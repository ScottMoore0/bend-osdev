# bend-osdev-fat: a read-only FAT12, FAT16 and FAT32 file system over
# bend-osdev-blockdev's device interface.
#
# Microsoft, "FAT: General Overview of On-Disk Format" (the FAT32 File System
# Specification, version 1.03, 2000), with its long-name (VFAT) entries.
#
# The entry concern: mounting a volume (reading and checking its boot
# sector) and the operations by path: what a path names, listing a
# directory, reading a file's bytes as a range or a piece at a time. The
# records and the steps underneath are in bpb.bend (the boot sector),
# table.bend (the FAT and cluster chains), dirent.bend (directory entries),
# dir.bend (directories and paths) and file.bend (reading files).
#
# Every operation reads only the blocks it needs: the boot sector, the
# directories on a path, the FAT entries of the chains it follows, and the
# sectors of the bytes asked for.
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
import ./file.bend as F

# A mounted volume: the options it was mounted with, its BPB and its geometry
type FatFs is Data:
  FatFs{opts: P.FatOptions, bpb: P.FatBpb, vol: P.FatVolume}

def FatFs.options(fs: FatFs) -> P.FatOptions:
  match fs:
    case FatFs{o, b, v}:
      o

def FatFs.bpb(fs: FatFs) -> P.FatBpb:
  match fs:
    case FatFs{o, b, v}:
      b

def FatFs.volume(fs: FatFs) -> P.FatVolume:
  match fs:
    case FatFs{o, b, v}:
      v

def FatFs.kind(fs: FatFs) -> P.FatType:
  P.FatVolume.kind(FatFs.volume(fs))

def Fat.mount.with(+opts: P.FatOptions, +b: P.FatBpb) -> Result<&2, &2, E.FatError, FatFs>:
  do Result<&2, &2, E.FatError, FatFs>:
    v : P.FatVolume <- P.FatVolume.of_bpb(opts, b)
    return FatFs{opts, b, v}

# the volume on a device, its boot sector (the first 512 bytes) checked
def Fat.mount(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +opts: P.FatOptions) -> Result<&2, &2, E.FatError, FatFs>:
  do Result<&2, &2, E.FatError, FatFs>:
    o : B.Octets <- T.FatIo.read(~Dv, ~block_size, ~read_block, d, 0n, 512n)
    b : P.FatBpb <- P.FatBpb.decode(o)
    Fat.mount.with(opts, b)

# the BS_ fields of the boot sector (volume ID and label)
def Fat.boot_ext(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, fs: FatFs) -> Result<&2, &2, E.FatError, P.FatBootExt>:
  do Result<&2, &2, E.FatError, P.FatBootExt>:
    o : B.Octets <- T.FatIo.read(~Dv, ~block_size, ~read_block, d, 0n, 512n)
    P.FatBootExt.decode(FatFs.kind(fs), o)

def Fat.fs_info.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, fat32: Bool, +d: Dv, +off: Nat) -> Result<&2, &2, E.FatError, P.FatFsInfo>:
  match fat32:
    case False{}:
      Fail{E.FatBadFsInfo{}}
    case True{}:
      do Result<&2, &2, E.FatError, P.FatFsInfo>:
        o : B.Octets <- T.FatIo.read(~Dv, ~block_size, ~read_block, d, off, 512n)
        P.FatFsInfo.parse(o)

def Fat.is_fat32(t: P.FatType) -> Bool:
  match t:
    case P.Fat32{}:
      True{}
    case _:
      False{}

def Fat.fs_info.at(b: P.FatBpb) -> Nat:
  match b:
    case P.FatBpb{jump, oem, bps, spc, rsvd, nfats, rootent, tot16, media, fatsz16, spt, heads, hidden, tot32, fatsz32, flags, ver, rootclus, fsinfo, bk, sig}:
      Nat.mul(U32.to_nat(fsinfo), U32.to_nat(bps))

# the FAT32 FSInfo sector's hints (FatBadFsInfo on FAT12/16, or when its
# signatures are wrong)
def Fat.fs_info(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: FatFs) -> Result<&2, &2, E.FatError, P.FatFsInfo>:
  Fat.fs_info.go(~Dv, ~block_size, ~read_block, Fat.is_fat32(FatFs.kind(fs)), d, Fat.fs_info.at(FatFs.bpb(fs)))

# By path

# what a path names: the root, or an entry
def Fat.stat(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: FatFs, path: String) -> Result<&2, &2, E.FatError, Q.FatPath>:
  Q.FatPath.resolve(~Dv, ~block_size, ~read_block, d, FatFs.options(fs), FatFs.volume(fs), path)

# the entries of the directory a path names
def Fat.list(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: FatFs, path: String) -> Result<&2, &2, E.FatError, List<&2, Q.FatNode>>:
  do Result<&2, &2, E.FatError, List<&2, Q.FatNode>>:
    p : Q.FatPath <- Fat.stat(~Dv, ~block_size, ~read_block, d, fs, path)
    dir : Q.FatDir <- Q.FatPath.dir(p)
    Q.FatDir.list(~Dv, ~block_size, ~read_block, d, FatFs.options(fs), FatFs.volume(fs), dir)

def Fat.node(p: Q.FatPath) -> Result<&2, &2, E.FatError, Q.FatNode>:
  match p:
    case Q.FatPathRoot{}:
      Fail{E.FatIsADirectory{}}
    case Q.FatPathNode{n}:
      Done{n}

# the bytes of the file a path names, from offset off, at most len of them
# and never past its size
def Fat.read(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: FatFs, path: String, +off: Nat, +len: Nat) -> Result<&2, &2, E.FatError, B.Octets>:
  do Result<&2, &2, E.FatError, B.Octets>:
    p : Q.FatPath <- Fat.stat(~Dv, ~block_size, ~read_block, d, fs, path)
    n : Q.FatNode <- Fat.node(p)
    F.FatFile.read(~Dv, ~block_size, ~read_block, d, FatFs.volume(fs), n, off, len)

# a cursor at the start of the file a path names: read it a piece at a time
# with Fat.next
def Fat.open(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: FatFs, path: String) -> Result<&2, &2, E.FatError, F.FatCursor>:
  do Result<&2, &2, E.FatError, F.FatCursor>:
    p : Q.FatPath <- Fat.stat(~Dv, ~block_size, ~read_block, d, fs, path)
    n : Q.FatNode <- Fat.node(p)
    F.FatFile.open(FatFs.volume(fs), n)

# the next piece of an open file (one sector at most) and the cursor after it
def Fat.next(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, fs: FatFs, cur: F.FatCursor) -> Result<&2, &2, E.FatError, F.FatChunk>:
  F.FatFile.next(~Dv, ~block_size, ~read_block, d, FatFs.volume(fs), cur)
