# bend-osdev-fat, error.bend: why a FAT volume, record, chain, directory or
# path was refused. One constructor per failure, so a caller can tell them
# apart; FatDev wraps the device's own error.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../blockdev/blockdev.bend as D

type FatError is Data:
  # the device failed
  FatDev{e: D.DevError}
  # a record is shorter than its size
  FatTooShort{}
  # the boot sector
  FatBadJump{}
  FatBadSignature{}
  FatBadBytesPerSector{value: U32}
  FatBadSectorsPerCluster{value: U32}
  FatClusterTooLarge{bytes: Nat}
  FatBadReservedSectors{}
  FatBadFatCount{}
  FatBadRootEntries{}
  FatBadTotalSectors{}
  FatBadMedia{value: U32}
  FatBadFatSize{}
  FatBadVersion{}
  FatBadRootCluster{cluster: U32}
  FatTooSmall{}
  FatBadFsInfo{}
  # cluster chains
  FatBadCluster{cluster: U32}
  FatFreeInChain{cluster: U32}
  FatBadInChain{cluster: U32}
  FatChainLoop{}
  FatChainShort{}
  # directories and long names
  FatNotLongEntry{}
  FatLfnBadChecksum{}
  FatLfnBadSequence{}
  FatDirTooLong{}
  # paths
  FatNotFound{}
  FatNotADirectory{}
  FatIsADirectory{}

# a short name for each failure (what check.bend and the reference test print)
def FatError.show(e: FatError) -> String:
  match e:
    case FatDev{D.DevOutOfRange{n}}:
      "device: block " ++ Nat.show(n) ++ " out of range"
    case FatDev{D.DevBadLength{a, b}}:
      "device: bad block length"
    case FatDev{D.DevFailed{c}}:
      "device: failed " ++ U32.show(c)
    case FatTooShort{}:
      "too short"
    case FatBadJump{}:
      "bad jump instruction"
    case FatBadSignature{}:
      "no 0x55AA signature"
    case FatBadBytesPerSector{v}:
      "bad bytes per sector " ++ U32.show(v)
    case FatBadSectorsPerCluster{v}:
      "bad sectors per cluster " ++ U32.show(v)
    case FatClusterTooLarge{n}:
      "cluster too large " ++ Nat.show(n)
    case FatBadReservedSectors{}:
      "no reserved sectors"
    case FatBadFatCount{}:
      "no FATs"
    case FatBadRootEntries{}:
      "bad root entry count"
    case FatBadTotalSectors{}:
      "bad total sectors"
    case FatBadMedia{v}:
      "bad media " ++ U32.show(v)
    case FatBadFatSize{}:
      "bad FAT size"
    case FatBadVersion{}:
      "bad FAT32 version"
    case FatBadRootCluster{c}:
      "bad root cluster " ++ U32.show(c)
    case FatTooSmall{}:
      "volume too small"
    case FatBadFsInfo{}:
      "bad FSInfo"
    case FatBadCluster{c}:
      "cluster out of range " ++ U32.show(c)
    case FatFreeInChain{c}:
      "free cluster in chain " ++ U32.show(c)
    case FatBadInChain{c}:
      "bad cluster in chain " ++ U32.show(c)
    case FatChainLoop{}:
      "chain loops"
    case FatChainShort{}:
      "chain shorter than file"
    case FatNotLongEntry{}:
      "not a long-name entry"
    case FatLfnBadChecksum{}:
      "long name checksum mismatch"
    case FatLfnBadSequence{}:
      "long name sequence broken"
    case FatDirTooLong{}:
      "directory too long"
    case FatNotFound{}:
      "not found"
    case FatNotADirectory{}:
      "not a directory"
    case FatIsADirectory{}:
      "is a directory"
