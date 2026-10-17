# bend-osdev-ext2: the metadata checksums of ext4 (the ext4 disk-layout
# documentation, "Checksums"), computed from bytes.
#
# ext4's crc32c is the raw register of CRC-32C, with neither the initial nor
# the final inversion: crc32c(seed, data). Checksums chain: the filesystem's
# seed is crc32c(~0, uuid) (or s_checksum_seed with the csum_seed feature),
# an inode's seed is crc32c(crc32c(seed, inode number), generation), and each
# structure is checksummed from the seed of what owns it. gdt_csum (the older
# feature) uses crc16 (CRC-16/ARC) over the UUID instead.
import Base
import ../bytes/bytes.bend as B
import ../crc/crc.bend as C

# the CRC-32C register after the bytes o, from register c
def Ext2Csum.crc32c(c: U32, o: B.Octets) -> U32:
  C.Crc32Spec.update(C.crc32c.spec(), c, o)

# the CRC-16/ARC register after the bytes o, from register c
def Ext2Csum.crc16(c: U32, o: B.Octets) -> U32:
  C.Crc32Spec.update(C.crc16.spec(), c, o)

def Ext2Csum.low16(v: U32) -> U32:
  U32.and(v, 65535)

# the filesystem's checksum seed, from its UUID's 16 bytes
def Ext2Csum.seed(uuid: B.Octets) -> U32:
  Ext2Csum.crc32c(4294967295, uuid)

# the superblock's checksum: its first 1020 bytes (s_checksum is the last
# four of the 1024)
def Ext2Csum.super(sb: B.Octets) -> U32:
  Ext2Csum.crc32c(4294967295, B.Octets.take(1020n, sb))

# an inode's seed: the filesystem's, then the inode number and generation
def Ext2Csum.inode_seed(seed: U32, ino: U32, generation: U32) -> U32:
  Ext2Csum.crc32c(Ext2Csum.crc32c(seed, B.Octets.le32(ino)), B.Octets.le32(generation))

# a group descriptor of size bytes (32 or 64), with metadata_csum: the low 16
# bits of crc32c over the group number and the descriptor, its checksum field
# (bytes 30 and 31) read as zero
def Ext2Csum.group(seed: U32, group: U32, +desc: B.Octets, size: Nat) -> U32:
  +c = Ext2Csum.crc32c(Ext2Csum.crc32c(seed, B.Octets.le32(group)), B.Octets.take(30n, desc))
  Ext2Csum.low16(Ext2Csum.crc32c(Ext2Csum.crc32c(c, B.Octets.zeros(2n)), B.Octets.slice(32n, Nat.sub(size, 32n), desc)))

# the same with gdt_csum: crc16 from ~0 over the UUID, the group number and
# the descriptor, the checksum field skipped
def Ext2Csum.group16(uuid: B.Octets, group: U32, +desc: B.Octets, size: Nat) -> U32:
  +c = Ext2Csum.crc16(Ext2Csum.crc16(Ext2Csum.crc16(65535, uuid), B.Octets.le32(group)), B.Octets.take(30n, desc))
  Ext2Csum.crc16(c, B.Octets.slice(32n, Nat.sub(size, 32n), desc))

def Ext2Csum.inode.hi(fits: Bool, c: U32, +raw: B.Octets, +size: Nat) -> U32:
  match fits:
    case True{}:
      +c2 = Ext2Csum.crc32c(Ext2Csum.crc32c(c, B.Octets.slice(128n, 2n, raw)), B.Octets.zeros(2n))
      Ext2Csum.crc32c(c2, B.Octets.slice(132n, Nat.sub(size, 132n), raw))
    case False{}:
      Ext2Csum.crc32c(c, B.Octets.slice(128n, Nat.sub(size, 128n), raw))

def Ext2Csum.inode.big(big: Bool, fits: Bool, c: U32, +raw: B.Octets, +size: Nat) -> U32:
  match big:
    case True{}:
      Ext2Csum.inode.hi(fits, c, raw, size)
    case False{}:
      c

# an inode record of size bytes, from the inode's seed: crc32c over the
# record, its checksum fields (bytes 124-125, and 130-131 when the extra
# fields hold them: hi_fits) read as zero. With hi_fits the checksum is 32
# bits; otherwise only its low 16 bits are stored.
def Ext2Csum.inode(iseed: U32, +raw: B.Octets, +size: Nat, hi_fits: Bool) -> U32:
  +c = Ext2Csum.crc32c(Ext2Csum.crc32c(Ext2Csum.crc32c(iseed, B.Octets.take(124n, raw)), B.Octets.zeros(2n)), B.Octets.slice(126n, 2n, raw))
  Ext2Csum.inode.big(Nat.is_lt(128n, size), hi_fits, c, raw, size)

# an extent tree block, from its inode's seed: the header and eh_max entries
# (12 + 12 * max bytes), followed by the stored checksum
def Ext2Csum.extent_block(iseed: U32, +blk: B.Octets, max: Nat) -> U32:
  Ext2Csum.crc32c(iseed, B.Octets.take(Nat.add(12n, Nat.mul(12n, max)), blk))

# a directory leaf block of bs bytes, from its inode's seed: everything before
# the 12-byte checksum tail
def Ext2Csum.dir_block(iseed: U32, +blk: B.Octets, bs: Nat) -> U32:
  Ext2Csum.crc32c(iseed, B.Octets.take(Nat.sub(bs, 12n), blk))
