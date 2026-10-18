# bend-osdev-ext4: the superblock fields ext4 adds that ext2's reader does
# not keep (the ext4 disk-layout documentation, "The Super Block"), and the
# mounted filesystem: ext2's, with those fields and this package's options.
#
#   0xD0  s_journal_uuid[16]   0xE0  s_journal_inum    0xE4  s_journal_dev
#   0xEC  s_hash_seed[4]       0xFC  s_def_hash_version
#   0x160 s_flags (1: signed directory hash, 2: unsigned directory hash)
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../ext2/super.bend as S
import ./error.bend as E
import ./options.bend as O

type Ext4Super is Data:
  Ext4Super{hash_seed: List<&2, U32>, def_hash_version: U32, flags: U32, journal_inum: U32, journal_dev: U32, journal_uuid: B.Octets}

def Ext4Super.u8(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.at(o, i), 0)

def Ext4Super.u32(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.le32_at(o, i), 0)

# the fields, from the superblock's 1024 bytes
def Ext4Super.parse(+o: B.Octets) -> Ext4Super:
  Ext4Super{[Ext4Super.u32(o, 236n), Ext4Super.u32(o, 240n), Ext4Super.u32(o, 244n), Ext4Super.u32(o, 248n)], Ext4Super.u8(o, 252n), Ext4Super.u32(o, 352n), Ext4Super.u32(o, 224n), Ext4Super.u32(o, 228n), B.Octets.slice(208n, 16n, o)}

def Ext4Super.hash_seed(s: Ext4Super) -> List<&2, U32>:
  match s:
    case Ext4Super{h, v, f, j, d, u}:
      h

def Ext4Super.def_hash_version(s: Ext4Super) -> U32:
  match s:
    case Ext4Super{h, v, f, j, d, u}:
      v

def Ext4Super.flags(s: Ext4Super) -> U32:
  match s:
    case Ext4Super{h, v, f, j, d, u}:
      f

def Ext4Super.journal_inum(s: Ext4Super) -> U32:
  match s:
    case Ext4Super{h, v, f, j, d, u}:
      j

def Ext4Super.journal_dev(s: Ext4Super) -> U32:
  match s:
    case Ext4Super{h, v, f, j, d, u}:
      d

def Ext4Super.journal_uuid(s: Ext4Super) -> B.Octets:
  match s:
    case Ext4Super{h, v, f, j, d, u}:
      u

# Feature bits this package uses (s_feature_compat, s_feature_incompat)

def Ext4Super.compat_has_journal() -> U32:
  4

def Ext4Super.compat_dir_index() -> U32:
  32

def Ext4Super.incompat_recover() -> U32:
  4

def Ext4Super.incompat_journal_dev() -> U32:
  8

def Ext4Super.incompat_ea_inode() -> U32:
  1024

def Ext4Super.incompat_large_dir() -> U32:
  16384

def Ext4Super.incompat_inline_data() -> U32:
  32768

# The mounted filesystem

type Ext4Fs is Data:
  Ext4Fs{fs: S.Ext2Fs, x: Ext4Super, opts: O.Ext4Options}

def Ext4Fs.ext2(f: Ext4Fs) -> S.Ext2Fs:
  match f:
    case Ext4Fs{fs, x, o}:
      fs

def Ext4Fs.super(f: Ext4Fs) -> Ext4Super:
  match f:
    case Ext4Fs{fs, x, o}:
      x

def Ext4Fs.opts(f: Ext4Fs) -> O.Ext4Options:
  match f:
    case Ext4Fs{fs, x, o}:
      o

def Ext4Fs.has_compat(+f: Ext4Fs, bit: U32) -> Bool:
  S.Ext2Super.has_compat(S.Ext2Fs.sb(Ext4Fs.ext2(f)), bit)

def Ext4Fs.has_incompat(+f: Ext4Fs, bit: U32) -> Bool:
  S.Ext2Super.has_incompat(S.Ext2Fs.sb(Ext4Fs.ext2(f)), bit)

def Ext4Fs.verify(+f: Ext4Fs) -> Bool:
  O.Ext4Options.verify(Ext4Fs.opts(f))

# whether metadata_csum checksums are checked (the image has them, and the
# options ask for them)
def Ext4Fs.verify_meta(+f: Ext4Fs) -> Bool:
  Bool.and(Ext4Fs.verify(f), S.Ext2Fs.verify_meta(Ext4Fs.ext2(f)))

def Ext4Fs.block_size(+f: Ext4Fs) -> Nat:
  S.Ext2Fs.block_size(Ext4Fs.ext2(f))

def Ext4Fs.seed(+f: Ext4Fs) -> U32:
  S.Ext2Fs.seed(Ext4Fs.ext2(f))

def Ext4Fs.signed.pick(signed: Bool, unsigned: Bool, dflt: Bool) -> Bool:
  match signed unsigned:
    case True{} _:
      True{}
    case False{} True{}:
      False{}
    case False{} False{}:
      dflt

# whether directory hashes read names as signed chars: the superblock's
# flags say, else the options' default
def Ext4Fs.hash_signed(+f: Ext4Fs) -> Bool:
  +fl = Ext4Super.flags(Ext4Fs.super(f))
  Ext4Fs.signed.pick(Bool.not(U32.is_eq(U32.and(fl, 1), 0)), Bool.not(U32.is_eq(U32.and(fl, 2), 0)), O.Ext4Options.signed_default(Ext4Fs.opts(f)))

# the filesystem a superblock's 1024 bytes describe, checked by ext2's
# reader with the options' ext2 part
def Ext4Fs.mount(+opts: O.Ext4Options, +raw: B.Octets) -> Result<&2, &2, E.Ext4Error, Ext4Fs>:
  do Result<&2, &2, E.Ext4Error, Ext4Fs>:
    fs : S.Ext2Fs <- E.Ext4Error.lift(S.Ext2Fs, S.Ext2Fs.mount(O.Ext4Options.ext2(opts), raw))
    return Ext4Fs{fs, Ext4Super.parse(raw), opts}

# the filesystem on a device
def Ext4Fs.open(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +opts: O.Ext4Options) -> Result<&2, &2, E.Ext4Error, Ext4Fs>:
  do Result<&2, &2, E.Ext4Error, Ext4Fs>:
    raw : B.Octets <- E.Ext4Error.lift(B.Octets, S.Ext2Super.read(~Dv, ~block_size, ~read_block, d))
    Ext4Fs.mount(opts, raw)
