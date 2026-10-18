# bend-osdev-ext4: why an image, a read from it, a journal recovery or a
# journal write was refused.
#
# One constructor per failure. A failure of ext2's reader (the superblock,
# descriptors, inodes, block maps, extents, linear directories, and every
# device read) comes back as Ext4Ext2{e}, with ext2's own error inside.
import Base
import ../blockdev/blockdev.bend as D
import ../ext2/error.bend as XE

type Ext4Error is Data:
  # ext2's reader failed (a device read failure is inside it)
  Ext4Ext2{e: XE.Ext2Error}
  # a device write failed
  Ext4DevWrite{e: D.DevError}
  # a device read failed (outside ext2's reader)
  Ext4DevRead{e: D.DevError}
  # the device's blocks do not divide the filesystem's
  Ext4BadDevBlock{fs_block: Nat, dev_block: Nat}
  # hashed directories
  Ext4BadHashVersion{version: U32}
  Ext4BadDxRoot{ino: Nat, why: String}
  Ext4BadDxNode{ino: Nat, block: Nat, why: String}
  Ext4BadDxCsum{ino: Nat, block: Nat, stored: U32, computed: U32}
  Ext4DxTooDeep{ino: Nat, levels: Nat}
  Ext4HtreeTooBig{why: String}
  # extended attributes and inline data
  Ext4BadXattr{ino: Nat, why: String}
  Ext4BadXattrBlock{block: Nat, why: String}
  Ext4BadXattrCsum{block: Nat, stored: U32, computed: U32}
  Ext4BadXattrHash{ino: Nat, stored: U32, computed: U32}
  Ext4NoXattr{name: String}
  Ext4NotInline{ino: Nat}
  Ext4BadInline{ino: Nat, why: String}
  # paths
  Ext4NotFound{name: String}
  Ext4NotDir{ino: Nat}
  Ext4SymlinkInPath{ino: Nat}
  # the journal
  Ext4NoJournal{}
  Ext4ExternalJournal{}
  Ext4BadJournalMagic{magic: U32}
  Ext4BadJournalType{blocktype: U32}
  Ext4BadJournal{why: String}
  Ext4JournalUnsupported{feature: String}
  Ext4BadJournalCsum{stored: U32, computed: U32}
  Ext4JournalBlock{block: Nat}
  Ext4JournalNotEmpty{}
  Ext4JournalFull{needed: Nat, room: Nat}
  Ext4BadJournalWrite{block: Nat, why: String}
  Ext4ReplayCsum{block: Nat, sequence: Nat}
  Ext4BadLogCsum{block: Nat}

def Ext4Error.dev_show(e: D.DevError) -> String:
  match e:
    case D.DevOutOfRange{b}:
      "block " ++ Nat.show(b) ++ " is outside the device"
    case D.DevBadLength{x, g}:
      "a block of " ++ Nat.show(g) ++ " bytes for blocks of " ++ Nat.show(x)
    case D.DevFailed{c}:
      "the device failed (" ++ U32.show(c) ++ ")"

def Ext4Error.csum(stored: U32, computed: U32) -> String:
  " (stored " ++ U32.show(stored) ++ ", computed " ++ U32.show(computed) ++ ")"

# a message for each failure
def Ext4Error.show(e: Ext4Error) -> String:
  match e:
    case Ext4Ext2{x}:
      XE.Ext2Error.show(x)
    case Ext4DevWrite{d}:
      "device write: " ++ Ext4Error.dev_show(d)
    case Ext4DevRead{d}:
      "device read: " ++ Ext4Error.dev_show(d)
    case Ext4BadDevBlock{f, d}:
      "filesystem blocks of " ++ Nat.show(f) ++ " bytes on a device of " ++ Nat.show(d) ++ "-byte blocks"
    case Ext4BadHashVersion{v}:
      "unsupported directory hash version " ++ U32.show(v)
    case Ext4BadDxRoot{i, w}:
      "directory " ++ Nat.show(i) ++ ": bad htree root: " ++ w
    case Ext4BadDxNode{i, b, w}:
      "directory " ++ Nat.show(i) ++ ": bad htree node in block " ++ Nat.show(b) ++ ": " ++ w
    case Ext4BadDxCsum{i, b, s, c}:
      "directory " ++ Nat.show(i) ++ ": bad htree checksum in block " ++ Nat.show(b) ++ Ext4Error.csum(s, c)
    case Ext4DxTooDeep{i, l}:
      "directory " ++ Nat.show(i) ++ ": htree of " ++ Nat.show(l) ++ " index levels is too deep"
    case Ext4HtreeTooBig{w}:
      "cannot build the hashed directory: " ++ w
    case Ext4BadXattr{i, w}:
      "inode " ++ Nat.show(i) ++ ": bad extended attribute: " ++ w
    case Ext4BadXattrBlock{b, w}:
      "bad extended attribute block " ++ Nat.show(b) ++ ": " ++ w
    case Ext4BadXattrCsum{b, s, c}:
      "bad checksum in extended attribute block " ++ Nat.show(b) ++ Ext4Error.csum(s, c)
    case Ext4BadXattrHash{i, s, c}:
      "inode " ++ Nat.show(i) ++ ": bad extended attribute hash" ++ Ext4Error.csum(s, c)
    case Ext4NoXattr{n}:
      "no extended attribute " ++ n
    case Ext4NotInline{i}:
      "inode " ++ Nat.show(i) ++ " does not keep its data inline"
    case Ext4BadInline{i, w}:
      "inode " ++ Nat.show(i) ++ ": bad inline data: " ++ w
    case Ext4NotFound{n}:
      "not found: " ++ n
    case Ext4NotDir{i}:
      "inode " ++ Nat.show(i) ++ " is not a directory"
    case Ext4SymlinkInPath{i}:
      "the path goes through symbolic link " ++ Nat.show(i) ++ " (not followed)"
    case Ext4NoJournal{}:
      "the filesystem has no journal"
    case Ext4ExternalJournal{}:
      "the journal is on another device (unsupported)"
    case Ext4BadJournalMagic{m}:
      "not a journal superblock (magic " ++ U32.show(m) ++ ")"
    case Ext4BadJournalType{t}:
      "unknown journal superblock type " ++ U32.show(t)
    case Ext4BadJournal{w}:
      "bad journal: " ++ w
    case Ext4JournalUnsupported{f}:
      "unsupported journal feature: " ++ f
    case Ext4BadJournalCsum{s, c}:
      "bad journal superblock checksum" ++ Ext4Error.csum(s, c)
    case Ext4JournalBlock{b}:
      "journal block " ++ Nat.show(b) ++ " is outside the journal"
    case Ext4JournalNotEmpty{}:
      "the journal holds transactions not yet replayed"
    case Ext4JournalFull{n, r}:
      "the transaction needs " ++ Nat.show(n) ++ " journal blocks, " ++ Nat.show(r) ++ " are free"
    case Ext4BadJournalWrite{b, w}:
      "cannot journal a write of block " ++ Nat.show(b) ++ ": " ++ w
    case Ext4ReplayCsum{b, s}:
      "bad checksum on the journal's copy of block " ++ Nat.show(b) ++ " in transaction " ++ Nat.show(s)
    case Ext4BadLogCsum{b}:
      "bad checksum in the log's descriptor or revoke block " ++ Nat.show(b) ++ " (nothing replayed)"

# the constructor's name, for tests and logs
def Ext4Error.kind(e: Ext4Error) -> String:
  match e:
    case Ext4Ext2{x}:
      "Ext4Ext2 " ++ XE.Ext2Error.kind(x)
    case Ext4DevWrite{x}:
      "Ext4DevWrite"
    case Ext4DevRead{x}:
      "Ext4DevRead"
    case Ext4BadDevBlock{x, y}:
      "Ext4BadDevBlock"
    case Ext4BadHashVersion{x}:
      "Ext4BadHashVersion"
    case Ext4BadDxRoot{x, y}:
      "Ext4BadDxRoot"
    case Ext4BadDxNode{x, y, z}:
      "Ext4BadDxNode"
    case Ext4BadDxCsum{x, y, z, w}:
      "Ext4BadDxCsum"
    case Ext4DxTooDeep{x, y}:
      "Ext4DxTooDeep"
    case Ext4HtreeTooBig{x}:
      "Ext4HtreeTooBig"
    case Ext4BadXattr{x, y}:
      "Ext4BadXattr"
    case Ext4BadXattrBlock{x, y}:
      "Ext4BadXattrBlock"
    case Ext4BadXattrCsum{x, y, z}:
      "Ext4BadXattrCsum"
    case Ext4BadXattrHash{x, y, z}:
      "Ext4BadXattrHash"
    case Ext4NoXattr{x}:
      "Ext4NoXattr"
    case Ext4NotInline{x}:
      "Ext4NotInline"
    case Ext4BadInline{x, y}:
      "Ext4BadInline"
    case Ext4NotFound{x}:
      "Ext4NotFound"
    case Ext4NotDir{x}:
      "Ext4NotDir"
    case Ext4SymlinkInPath{x}:
      "Ext4SymlinkInPath"
    case Ext4NoJournal{}:
      "Ext4NoJournal"
    case Ext4ExternalJournal{}:
      "Ext4ExternalJournal"
    case Ext4BadJournalMagic{x}:
      "Ext4BadJournalMagic"
    case Ext4BadJournalType{x}:
      "Ext4BadJournalType"
    case Ext4BadJournal{x}:
      "Ext4BadJournal"
    case Ext4JournalUnsupported{x}:
      "Ext4JournalUnsupported"
    case Ext4BadJournalCsum{x, y}:
      "Ext4BadJournalCsum"
    case Ext4JournalBlock{x}:
      "Ext4JournalBlock"
    case Ext4JournalNotEmpty{}:
      "Ext4JournalNotEmpty"
    case Ext4JournalFull{x, y}:
      "Ext4JournalFull"
    case Ext4BadJournalWrite{x, y}:
      "Ext4BadJournalWrite"
    case Ext4ReplayCsum{x, y}:
      "Ext4ReplayCsum"
    case Ext4BadLogCsum{x}:
      "Ext4BadLogCsum"

# a failure of ext2's reader, as this package's
def Ext4Error.lift(-A: Data, r: Result<&2, &2, XE.Ext2Error, A>) -> Result<&2, &2, Ext4Error, A>:
  match r:
    case Done{x}:
      Done{x}
    case Fail{e}:
      Fail{Ext4Ext2{e}}

def Ext4.require(ok: Bool, e: Ext4Error) -> Result<&2, &2, Ext4Error, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}
