# bend-osdev-ext2: what a reader accepts and does, as one record with a named
# default.
#
#   incompat        the incompatible features (a mask of the superblock's
#                   s_feature_incompat bits) the reader agrees to read; an
#                   image with any other incompat bit set is refused, naming
#                   the feature, as a driver must
#   verify          check the metadata checksums the image carries
#                   (metadata_csum: superblock, group descriptors, inodes,
#                   extent blocks, directory blocks; gdt_csum: group
#                   descriptors)
#   allow_recovery  read an image whose journal needs recovery (its metadata
#                   may be stale); off by default, as a driver would replay
#                   the journal first
#   symlink_hops    how many symbolic links a path lookup follows; 0 reports
#                   a symbolic link instead of following it
#   max_depth       the deepest extent tree accepted (ext4 allows 5)
import Base

type Ext2Options is Data:
  Ext2Options{incompat: U32, verify: Bool, allow_recovery: Bool, symlink_hops: Nat, max_depth: Nat}

# the incompat features this package reads: filetype (2), meta_bg (16),
# extents (64), 64bit (128), mmp (256), flex_bg (512), ea_inode (1024),
# csum_seed (8192), largedir (16384). Not read: compression (1),
# journal_dev (8), dirdata (4096), inline_data (32768), encrypt (65536),
# casefold (131072). recover (4) is governed by allow_recovery.
def Ext2Options.all_incompat() -> U32:
  26578

# the plain ext2 subset: filetype only (no extents, no 64-bit descriptors)
def Ext2Options.ext2_incompat() -> U32:
  2

# everything this package can read, checksums verified, symbolic links
# reported, not followed
def Ext2Options.default() -> Ext2Options:
  Ext2Options{Ext2Options.all_incompat(), True{}, False{}, 0n, 5n}

def Ext2Options.with_verify(o: Ext2Options, v: Bool) -> Ext2Options:
  match o:
    case Ext2Options{i, x, r, h, m}:
      Ext2Options{i, v, r, h, m}

def Ext2Options.with_symlink_hops(o: Ext2Options, n: Nat) -> Ext2Options:
  match o:
    case Ext2Options{i, x, r, h, m}:
      Ext2Options{i, x, r, n, m}

def Ext2Options.with_incompat(o: Ext2Options, mask: U32) -> Ext2Options:
  match o:
    case Ext2Options{i, x, r, h, m}:
      Ext2Options{mask, x, r, h, m}

def Ext2Options.with_recovery(o: Ext2Options, a: Bool) -> Ext2Options:
  match o:
    case Ext2Options{i, x, r, h, m}:
      Ext2Options{i, x, a, h, m}

def Ext2Options.with_max_depth(o: Ext2Options, d: Nat) -> Ext2Options:
  match o:
    case Ext2Options{i, x, r, h, m}:
      Ext2Options{i, x, r, h, d}

def Ext2Options.incompat(o: Ext2Options) -> U32:
  match o:
    case Ext2Options{i, x, r, h, m}:
      i

def Ext2Options.verify(o: Ext2Options) -> Bool:
  match o:
    case Ext2Options{i, x, r, h, m}:
      x

def Ext2Options.allow_recovery(o: Ext2Options) -> Bool:
  match o:
    case Ext2Options{i, x, r, h, m}:
      r

def Ext2Options.symlink_hops(o: Ext2Options) -> Nat:
  match o:
    case Ext2Options{i, x, r, h, m}:
      h

def Ext2Options.max_depth(o: Ext2Options) -> Nat:
  match o:
    case Ext2Options{i, x, r, h, m}:
      m
