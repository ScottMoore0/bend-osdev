# bend-osdev-ext2: why an image, a read from it or a write to it was refused.
#
# One constructor per failure, so a caller can tell them apart. Block and
# inode numbers are Nat; stored and computed checksums are U32.
import Base
import ../blockdev/blockdev.bend as D

type Ext2Error is Data:
  # the device failed (out of range, short block, driver error)
  Ext2Dev{e: D.DevError}
  # the superblock
  Ext2BadMagic{magic: U32}
  Ext2BadBlockSize{log: U32}
  Ext2BadRevision{rev: U32}
  Ext2BadInodeSize{size: U32}
  Ext2BadDescSize{size: U32}
  Ext2BadGeometry{why: String}
  Ext2Unsupported{feature: String}
  Ext2NeedsRecovery{}
  Ext2BadChecksumType{kind: U32}
  Ext2BadSuperCsum{stored: U32, computed: U32}
  # group descriptors and inodes
  Ext2BadGroup{group: Nat}
  Ext2BadGroupCsum{group: Nat, stored: U32, computed: U32}
  Ext2BadInodeNumber{ino: Nat}
  Ext2BadInodeCsum{ino: Nat, stored: U32, computed: U32}
  Ext2InlineData{ino: Nat}
  # file data
  Ext2BadBlockRef{ino: Nat, block: Nat}
  Ext2PastEnd{ino: Nat, block: Nat}
  Ext2BadExtentMagic{ino: Nat, magic: U32}
  Ext2BadExtentHeader{ino: Nat, why: String}
  Ext2ExtentTooDeep{ino: Nat, depth: Nat}
  Ext2BadExtentDepth{ino: Nat, depth: Nat}
  Ext2BadExtentCsum{ino: Nat, block: Nat, stored: U32, computed: U32}
  # directories and paths
  Ext2BadDirent{ino: Nat, offset: Nat, why: String}
  Ext2BadDirCsum{ino: Nat, block: Nat, stored: U32, computed: U32}
  Ext2NoDirTail{ino: Nat, block: Nat}
  Ext2NotDir{ino: Nat}
  Ext2NotSymlink{ino: Nat}
  Ext2NotFound{name: String}
  Ext2SymlinkLoop{}
  Ext2SymlinkInPath{ino: Nat}
  # writing (added with the writer; the reading errors above are unchanged)
  Ext2CannotWrite{why: String}
  Ext2NoSpace{}
  Ext2NoInodes{}
  Ext2Exists{name: String}
  Ext2NotEmpty{ino: Nat}
  Ext2IsDir{ino: Nat}
  Ext2BadName{why: String}
  Ext2TooManyLinks{ino: Nat}
  Ext2HtreeDir{ino: Nat}
  Ext2ExtentFull{ino: Nat}
  Ext2Unwritten{ino: Nat, block: Nat}
  Ext2FileTooBig{ino: Nat}
  Ext2Xattr{ino: Nat}
  Ext2RenameLoop{}
  Ext2BadMkfs{why: String}
  Ext2CheckFailed{what: String}

def Ext2Error.dev_show(e: D.DevError) -> String:
  match e:
    case D.DevOutOfRange{b}:
      "block " ++ Nat.show(b) ++ " is outside the device"
    case D.DevBadLength{x, g}:
      "the device answered " ++ Nat.show(g) ++ " bytes for a block of " ++ Nat.show(x)
    case D.DevFailed{c}:
      "the device failed (" ++ U32.show(c) ++ ")"

def Ext2Error.csum(stored: U32, computed: U32) -> String:
  " (stored " ++ U32.show(stored) ++ ", computed " ++ U32.show(computed) ++ ")"

# a message for each failure
def Ext2Error.show(e: Ext2Error) -> String:
  match e:
    case Ext2Dev{d}:
      "device: " ++ Ext2Error.dev_show(d)
    case Ext2BadMagic{m}:
      "not an ext2/3/4 superblock (magic " ++ U32.show(m) ++ ")"
    case Ext2BadBlockSize{l}:
      "bad block size (log " ++ U32.show(l) ++ ")"
    case Ext2BadRevision{r}:
      "unknown revision " ++ U32.show(r)
    case Ext2BadInodeSize{s}:
      "bad inode size " ++ U32.show(s)
    case Ext2BadDescSize{s}:
      "bad group descriptor size " ++ U32.show(s)
    case Ext2BadGeometry{w}:
      "bad geometry: " ++ w
    case Ext2Unsupported{f}:
      "unsupported feature: " ++ f
    case Ext2NeedsRecovery{}:
      "the journal needs recovery"
    case Ext2BadChecksumType{k}:
      "unknown checksum type " ++ U32.show(k)
    case Ext2BadSuperCsum{s, c}:
      "bad superblock checksum" ++ Ext2Error.csum(s, c)
    case Ext2BadGroup{g}:
      "no group " ++ Nat.show(g)
    case Ext2BadGroupCsum{g, s, c}:
      "bad checksum in group descriptor " ++ Nat.show(g) ++ Ext2Error.csum(s, c)
    case Ext2BadInodeNumber{i}:
      "no inode " ++ Nat.show(i)
    case Ext2BadInodeCsum{i, s, c}:
      "bad checksum in inode " ++ Nat.show(i) ++ Ext2Error.csum(s, c)
    case Ext2InlineData{i}:
      "inode " ++ Nat.show(i) ++ " keeps its data inline (unsupported)"
    case Ext2BadBlockRef{i, b}:
      "inode " ++ Nat.show(i) ++ " refers to block " ++ Nat.show(b) ++ ", outside the filesystem"
    case Ext2PastEnd{i, b}:
      "block " ++ Nat.show(b) ++ " is past the end of inode " ++ Nat.show(i)
    case Ext2BadExtentMagic{i, m}:
      "inode " ++ Nat.show(i) ++ ": bad extent header magic " ++ U32.show(m)
    case Ext2BadExtentHeader{i, w}:
      "inode " ++ Nat.show(i) ++ ": bad extent header: " ++ w
    case Ext2ExtentTooDeep{i, d}:
      "inode " ++ Nat.show(i) ++ ": extent tree of depth " ++ Nat.show(d) ++ " is too deep"
    case Ext2BadExtentDepth{i, d}:
      "inode " ++ Nat.show(i) ++ ": extent node of the wrong depth (" ++ Nat.show(d) ++ ")"
    case Ext2BadExtentCsum{i, b, s, c}:
      "inode " ++ Nat.show(i) ++ ": bad checksum in extent block " ++ Nat.show(b) ++ Ext2Error.csum(s, c)
    case Ext2BadDirent{i, o, w}:
      "directory " ++ Nat.show(i) ++ ": bad entry at byte " ++ Nat.show(o) ++ ": " ++ w
    case Ext2BadDirCsum{i, b, s, c}:
      "directory " ++ Nat.show(i) ++ ": bad checksum in block " ++ Nat.show(b) ++ Ext2Error.csum(s, c)
    case Ext2NoDirTail{i, b}:
      "directory " ++ Nat.show(i) ++ ": block " ++ Nat.show(b) ++ " has no checksum tail"
    case Ext2NotDir{i}:
      "inode " ++ Nat.show(i) ++ " is not a directory"
    case Ext2NotSymlink{i}:
      "inode " ++ Nat.show(i) ++ " is not a symbolic link"
    case Ext2NotFound{n}:
      "not found: " ++ n
    case Ext2SymlinkLoop{}:
      "too many symbolic links"
    case Ext2SymlinkInPath{i}:
      "the path goes through symbolic link " ++ Nat.show(i) ++ " (not followed)"
    case Ext2CannotWrite{w}:
      "this writer does not write the filesystem: " ++ w
    case Ext2NoSpace{}:
      "no free block"
    case Ext2NoInodes{}:
      "no free inode"
    case Ext2Exists{n}:
      "already exists: " ++ n
    case Ext2NotEmpty{i}:
      "directory " ++ Nat.show(i) ++ " is not empty"
    case Ext2IsDir{i}:
      "inode " ++ Nat.show(i) ++ " is a directory"
    case Ext2BadName{w}:
      "bad name: " ++ w
    case Ext2TooManyLinks{i}:
      "inode " ++ Nat.show(i) ++ " has too many links"
    case Ext2HtreeDir{i}:
      "directory " ++ Nat.show(i) ++ " is hash-indexed (written by bend-osdev-ext4, not here)"
    case Ext2ExtentFull{i}:
      "inode " ++ Nat.show(i) ++ ": the extent tree has no room this writer can make"
    case Ext2Unwritten{i, b}:
      "inode " ++ Nat.show(i) ++ ": block " ++ Nat.show(b) ++ " is in an unwritten extent (not written here)"
    case Ext2FileTooBig{i}:
      "inode " ++ Nat.show(i) ++ ": the file would be too big"
    case Ext2Xattr{i}:
      "inode " ++ Nat.show(i) ++ " has an extended attribute block (not freed here)"
    case Ext2RenameLoop{}:
      "a directory cannot be moved below itself"
    case Ext2BadMkfs{w}:
      "cannot make the filesystem: " ++ w
    case Ext2CheckFailed{w}:
      "the result failed its check (the device is left as it was): " ++ w

# the constructor's name, for tests and logs
def Ext2Error.kind(e: Ext2Error) -> String:
  match e:
    case Ext2Dev{x0}:
      "Ext2Dev"
    case Ext2BadMagic{x0}:
      "Ext2BadMagic"
    case Ext2BadBlockSize{x0}:
      "Ext2BadBlockSize"
    case Ext2BadRevision{x0}:
      "Ext2BadRevision"
    case Ext2BadInodeSize{x0}:
      "Ext2BadInodeSize"
    case Ext2BadDescSize{x0}:
      "Ext2BadDescSize"
    case Ext2BadGeometry{x0}:
      "Ext2BadGeometry"
    case Ext2Unsupported{x0}:
      "Ext2Unsupported"
    case Ext2NeedsRecovery{}:
      "Ext2NeedsRecovery"
    case Ext2BadChecksumType{x0}:
      "Ext2BadChecksumType"
    case Ext2BadSuperCsum{x0, x1}:
      "Ext2BadSuperCsum"
    case Ext2BadGroup{x0}:
      "Ext2BadGroup"
    case Ext2BadGroupCsum{x0, x1, x2}:
      "Ext2BadGroupCsum"
    case Ext2BadInodeNumber{x0}:
      "Ext2BadInodeNumber"
    case Ext2BadInodeCsum{x0, x1, x2}:
      "Ext2BadInodeCsum"
    case Ext2InlineData{x0}:
      "Ext2InlineData"
    case Ext2BadBlockRef{x0, x1}:
      "Ext2BadBlockRef"
    case Ext2PastEnd{x0, x1}:
      "Ext2PastEnd"
    case Ext2BadExtentMagic{x0, x1}:
      "Ext2BadExtentMagic"
    case Ext2BadExtentHeader{x0, x1}:
      "Ext2BadExtentHeader"
    case Ext2ExtentTooDeep{x0, x1}:
      "Ext2ExtentTooDeep"
    case Ext2BadExtentDepth{x0, x1}:
      "Ext2BadExtentDepth"
    case Ext2BadExtentCsum{x0, x1, x2, x3}:
      "Ext2BadExtentCsum"
    case Ext2BadDirent{x0, x1, x2}:
      "Ext2BadDirent"
    case Ext2BadDirCsum{x0, x1, x2, x3}:
      "Ext2BadDirCsum"
    case Ext2NoDirTail{x0, x1}:
      "Ext2NoDirTail"
    case Ext2NotDir{x0}:
      "Ext2NotDir"
    case Ext2NotSymlink{x0}:
      "Ext2NotSymlink"
    case Ext2NotFound{x0}:
      "Ext2NotFound"
    case Ext2SymlinkLoop{}:
      "Ext2SymlinkLoop"
    case Ext2SymlinkInPath{x0}:
      "Ext2SymlinkInPath"
    case Ext2CannotWrite{x0}:
      "Ext2CannotWrite"
    case Ext2NoSpace{}:
      "Ext2NoSpace"
    case Ext2NoInodes{}:
      "Ext2NoInodes"
    case Ext2Exists{x0}:
      "Ext2Exists"
    case Ext2NotEmpty{x0}:
      "Ext2NotEmpty"
    case Ext2IsDir{x0}:
      "Ext2IsDir"
    case Ext2BadName{x0}:
      "Ext2BadName"
    case Ext2TooManyLinks{x0}:
      "Ext2TooManyLinks"
    case Ext2HtreeDir{x0}:
      "Ext2HtreeDir"
    case Ext2ExtentFull{x0}:
      "Ext2ExtentFull"
    case Ext2Unwritten{x0, x1}:
      "Ext2Unwritten"
    case Ext2FileTooBig{x0}:
      "Ext2FileTooBig"
    case Ext2Xattr{x0}:
      "Ext2Xattr"
    case Ext2RenameLoop{}:
      "Ext2RenameLoop"
    case Ext2BadMkfs{x0}:
      "Ext2BadMkfs"
    case Ext2CheckFailed{x0}:
      "Ext2CheckFailed"
