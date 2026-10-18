# bend-osdev-ext4: what ext4 has beyond what bend-osdev-ext2 reads: hashed
# (htree) directory lookups, inline data, extended attributes, and the jbd2
# journal (recovery and writing transactions). The entry file: opening a
# filesystem, and paths (lookup, listing, reading, symbolic links,
# attributes), through every kind of directory and file.
#
# Specifications: the ext4 disk-layout documentation and the jbd2 journal
# documentation (kernel.org, Documentation/filesystems/ext4); see README.md
# for the files, the API and what was settled by experiment.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../ext2/inode.bend as N
import ../ext2/file.bend as FL
import ../ext2/dir.bend as DR
import ../ext2/ext2.bend as X
import ./error.bend as E
import ./options.bend as O
import ./super.bend as S
import ./inline.bend as IN
import ./xattr.bend as XA
import ./dir.bend as DI

# the filesystem on a device, checked, with these options
def Ext4.open(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +opts: O.Ext4Options) -> Result<&2, &2, E.Ext4Error, S.Ext4Fs>:
  S.Ext4Fs.open(~Dv, ~block_size, ~read_block, d, opts)

# inode n, checked (by ext2's reader)
def Ext4.inode(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +n: Nat) -> Result<&2, &2, E.Ext4Error, N.Ext2Inode>:
  E.Ext4Error.lift(N.Ext2Inode, N.Ext2Inode.read(~Dv, ~block_size, ~read_block, d, S.Ext4Fs.ext2(fs), n))

def Ext4.found(m: Maybe<&2, DR.Ext2Dirent>, +name: B.Octets) -> Result<&2, &2, E.Ext4Error, DR.Ext2Dirent>:
  match m:
    case Some{e}:
      Done{e}
    case None{}:
      Fail{E.Ext4NotFound{B.Octets.to_string(name)}}

def Ext4.through(link: Bool, rest: List<&2, B.Octets>, +i: N.Ext2Inode) -> Result<&2, &2, E.Ext4Error, Unit>:
  match link rest:
    case True{} Con{h, t}:
      Fail{E.Ext4SymlinkInPath{N.Ext2Inode.number_of(i)}}
    case _ _:
      Done{Unit{}}

# the inode the components lead to from directory cur: each found by
# Ext4Dir.find; a symbolic link before the last component is refused
def Ext4.walk(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, comps: List<&2, B.Octets>, cur: N.Ext2Inode, +d: Dv, +fs: S.Ext4Fs) -> Result<&2, &2, E.Ext4Error, N.Ext2Inode>:
  match comps:
    case Nil{}:
      Done{cur}
    case Con{+c, +rest}:
      do Result<&2, &2, E.Ext4Error, N.Ext2Inode>:
        m : Maybe<&2, DR.Ext2Dirent> <- DI.Ext4Dir.find(~Dv, ~block_size, ~read_block, d, fs, cur, c)
        e : DR.Ext2Dirent <- Ext4.found(m, c)
        +child : N.Ext2Inode <- Ext4.inode(~Dv, ~block_size, ~read_block, d, fs, U32.to_nat(DR.Ext2Dirent.inode(e)))
        Ext4.through(N.Ext2Inode.is_symlink(child), rest, child)
        Ext4.walk(~Dv, ~block_size, ~read_block, rest, child, d, fs)

# the inode a path (an Octets, "/"-separated, from the root) names; a final
# symbolic link is answered itself, one before the end is refused
# (Ext4SymlinkInPath)
def Ext4.lookup(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +path: B.Octets) -> Result<&2, &2, E.Ext4Error, N.Ext2Inode>:
  do Result<&2, &2, E.Ext4Error, N.Ext2Inode>:
    root : N.Ext2Inode <- Ext4.inode(~Dv, ~block_size, ~read_block, d, fs, X.Ext2.root_ino())
    Ext4.walk(~Dv, ~block_size, ~read_block, X.Ext2Path.components(path), root, d, fs)

# the used entries of the directory a path names
def Ext4.list(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +path: B.Octets) -> Result<&2, &2, E.Ext4Error, List<&2, DR.Ext2Dirent>>:
  do Result<&2, &2, E.Ext4Error, List<&2, DR.Ext2Dirent>>:
    i : N.Ext2Inode <- Ext4.lookup(~Dv, ~block_size, ~read_block, d, fs, path)
    DI.Ext4Dir.entries(~Dv, ~block_size, ~read_block, d, fs, i)

def Ext4.read_inode.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, inline: Bool, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  match inline:
    case True{}:
      IN.Ext4Inline.data(~Dv, ~block_size, ~read_block, d, fs, i)
    case False{}:
      E.Ext4Error.lift(B.Octets, FL.Ext2File.read_all(~Dv, ~block_size, ~read_block, d, S.Ext4Fs.ext2(fs), i))

# the whole content of a file, inline or in blocks (stream large files with
# ext2's Ext2File.start and next; inline files are at most an inode's size)
def Ext4.read_inode(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  Ext4.read_inode.go(~Dv, ~block_size, ~read_block, IN.Ext4Inline.is_inline(i), d, fs, i)

# the whole content of the file a path names
def Ext4.read(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +path: B.Octets) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  do Result<&2, &2, E.Ext4Error, B.Octets>:
    i : N.Ext2Inode <- Ext4.lookup(~Dv, ~block_size, ~read_block, d, fs, path)
    Ext4.read_inode(~Dv, ~block_size, ~read_block, d, fs, i)

def Ext4.readlink.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, inline: Bool, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  match inline:
    case True{}:
      IN.Ext4Inline.data(~Dv, ~block_size, ~read_block, d, fs, i)
    case False{}:
      E.Ext4Error.lift(B.Octets, FL.Ext2File.readlink(~Dv, ~block_size, ~read_block, d, S.Ext4Fs.ext2(fs), i))

# the target of the symbolic link a path names (an inline one too)
def Ext4.readlink(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +path: B.Octets) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  do Result<&2, &2, E.Ext4Error, B.Octets>:
    +i : N.Ext2Inode <- Ext4.lookup(~Dv, ~block_size, ~read_block, d, fs, path)
    Ext4.readlink.go(~Dv, ~block_size, ~read_block, Bool.and(N.Ext2Inode.is_symlink(i), IN.Ext4Inline.is_inline(i)), d, fs, i)

# the extended attributes of what a path names
def Ext4.xattrs(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +path: B.Octets) -> Result<&2, &2, E.Ext4Error, List<&2, XA.Ext4Xattr>>:
  do Result<&2, &2, E.Ext4Error, List<&2, XA.Ext4Xattr>>:
    i : N.Ext2Inode <- Ext4.lookup(~Dv, ~block_size, ~read_block, d, fs, path)
    XA.Ext4Xattr.list(~Dv, ~block_size, ~read_block, d, fs, i)

# the value of one extended attribute (by its full name) of what a path names
def Ext4.xattr(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +path: B.Octets, +name: B.Octets) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  do Result<&2, &2, E.Ext4Error, B.Octets>:
    i : N.Ext2Inode <- Ext4.lookup(~Dv, ~block_size, ~read_block, d, fs, path)
    XA.Ext4Xattr.get(~Dv, ~block_size, ~read_block, d, fs, i, name)
