# bend-osdev-ext4: what the reader, the journal recovery and the journal
# writer accept and do, as records with named defaults.
#
# Ext4Options (reading):
#   ext2            the options of ext2's reader, underneath (features
#                   accepted, ext2's checksums, recovery, symbolic links,
#                   the extent depth bound); the default adds inline_data
#                   to the features ext2 accepts, since this package reads it
#   verify          check this package's checksums and hashes: htree index
#                   blocks (dx_tail), extended attribute blocks (checksum,
#                   block hash), attribute entry hashes
#   signed_default  the hash's char signedness when the superblock sets
#                   neither the signed nor the unsigned directory hash flag
#                   (the reference platform, x86, has signed chars)
#   max_levels      the most htree index levels accepted below the root
#                   (the format allows 2, 3 with large_dir)
#
# Jbd2Options (the journal):
#   verify          check the journal's checksums: its superblock, and
#                   descriptor, revoke and commit blocks (v2/v3)
#   skip_bad_data   a journalled block whose tag checksum fails is skipped
#                   (and counted) rather than failing the replay
#   commit_sec, commit_nsec
#                   the time stamped into commit blocks the writer makes
#                   (the package has no clock)
import Base
import ../ext2/options.bend as XO

type Ext4Options is Data:
  Ext4Options{ext2: XO.Ext2Options, verify: Bool, signed_default: Bool, max_levels: Nat}

# the incompat features ext2's reader accepts plus inline_data (32768),
# which this package reads
def Ext4Options.incompat() -> U32:
  U32.or(XO.Ext2Options.all_incompat(), 32768)

def Ext4Options.default() -> Ext4Options:
  Ext4Options{XO.Ext2Options.with_incompat(XO.Ext2Options.default(), Ext4Options.incompat()), True{}, True{}, 3n}

def Ext4Options.ext2(o: Ext4Options) -> XO.Ext2Options:
  match o:
    case Ext4Options{x, v, s, m}:
      x

def Ext4Options.verify(o: Ext4Options) -> Bool:
  match o:
    case Ext4Options{x, v, s, m}:
      v

def Ext4Options.signed_default(o: Ext4Options) -> Bool:
  match o:
    case Ext4Options{x, v, s, m}:
      s

def Ext4Options.max_levels(o: Ext4Options) -> Nat:
  match o:
    case Ext4Options{x, v, s, m}:
      m

def Ext4Options.with_ext2(o: Ext4Options, e: XO.Ext2Options) -> Ext4Options:
  match o:
    case Ext4Options{x, v, s, m}:
      Ext4Options{e, v, s, m}

# verification on or off, here and in ext2's reader underneath
def Ext4Options.with_verify(o: Ext4Options, b: Bool) -> Ext4Options:
  match o:
    case Ext4Options{x, v, s, m}:
      +c = b
      Ext4Options{XO.Ext2Options.with_verify(x, c), c, s, m}

def Ext4Options.with_signed_default(o: Ext4Options, b: Bool) -> Ext4Options:
  match o:
    case Ext4Options{x, v, s, m}:
      Ext4Options{x, v, b, m}

def Ext4Options.with_max_levels(o: Ext4Options, n: Nat) -> Ext4Options:
  match o:
    case Ext4Options{x, v, s, m}:
      Ext4Options{x, v, s, n}

type Jbd2Options is Data:
  Jbd2Options{verify: Bool, skip_bad_data: Bool, commit_sec: U32, commit_nsec: U32}

def Jbd2Options.default() -> Jbd2Options:
  Jbd2Options{True{}, True{}, 0, 0}

def Jbd2Options.verify(o: Jbd2Options) -> Bool:
  match o:
    case Jbd2Options{v, s, t, n}:
      v

def Jbd2Options.skip_bad_data(o: Jbd2Options) -> Bool:
  match o:
    case Jbd2Options{v, s, t, n}:
      s

def Jbd2Options.commit_sec(o: Jbd2Options) -> U32:
  match o:
    case Jbd2Options{v, s, t, n}:
      t

def Jbd2Options.commit_nsec(o: Jbd2Options) -> U32:
  match o:
    case Jbd2Options{v, s, t, n}:
      n

def Jbd2Options.with_verify(o: Jbd2Options, b: Bool) -> Jbd2Options:
  match o:
    case Jbd2Options{v, s, t, n}:
      Jbd2Options{b, s, t, n}

def Jbd2Options.with_skip_bad_data(o: Jbd2Options, b: Bool) -> Jbd2Options:
  match o:
    case Jbd2Options{v, s, t, n}:
      Jbd2Options{v, b, t, n}

def Jbd2Options.with_commit_time(o: Jbd2Options, sec: U32, nsec: U32) -> Jbd2Options:
  match o:
    case Jbd2Options{v, s, t, n}:
      Jbd2Options{v, s, sec, nsec}
