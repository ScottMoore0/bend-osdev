# bend-osdev-ext4: directories of every kind: inline (in the inode),
# hashed (htree, looked up through the index), and linear (ext2's reader).
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../ext2/inode.bend as N
import ../ext2/dir.bend as DR
import ./error.bend as E
import ./super.bend as S
import ./inode.bend as I
import ./htree.bend as T
import ./inline.bend as IN

# whether directory i is hashed: EXT4_INDEX_FL, on a filesystem with
# dir_index (without it the flag is ignored and the directory read linearly)
def Ext4Dir.indexed(+fs: S.Ext4Fs, +i: N.Ext2Inode) -> Bool:
  Bool.and(N.Ext2Inode.has_flag(i, I.Ext4Inode.flag_index()), S.Ext4Fs.has_compat(fs, S.Ext4Super.compat_dir_index()))

def Ext4Dir.find.kind(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, inline: Bool, indexed: Bool, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode, +name: B.Octets) -> Result<&2, &2, E.Ext4Error, Maybe<&2, DR.Ext2Dirent>>:
  match inline indexed:
    case True{} _:
      do Result<&2, &2, E.Ext4Error, Maybe<&2, DR.Ext2Dirent>>:
        es : List<&2, DR.Ext2Dirent> <- IN.Ext4Inline.entries(~Dv, ~block_size, ~read_block, d, fs, i)
        return T.Ext4Htree.find(~DR.Ext2Dirent, ~DR.Ext2Dirent.name, es, name)
    case False{} True{}:
      T.Ext4Htree.lookup_dev(~Dv, ~block_size, ~read_block, d, fs, i, name)
    case False{} False{}:
      E.Ext4Error.lift(Maybe<&2, DR.Ext2Dirent>, DR.Ext2Dir.find(~Dv, ~block_size, ~read_block, d, S.Ext4Fs.ext2(fs), i, name))

# the entry named name in directory i, if any; Ext4NotDir for any other
# inode. An htree directory reads only its index path and one leaf.
def Ext4Dir.find(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode, +name: B.Octets) -> Result<&2, &2, E.Ext4Error, Maybe<&2, DR.Ext2Dirent>>:
  do Result<&2, &2, E.Ext4Error, Maybe<&2, DR.Ext2Dirent>>:
    E.Ext4.require(N.Ext2Inode.is_dir(i), E.Ext4NotDir{N.Ext2Inode.number_of(i)})
    Ext4Dir.find.kind(~Dv, ~block_size, ~read_block, IN.Ext4Inline.is_inline(i), Ext4Dir.indexed(fs, i), d, fs, i, name)

def Ext4Dir.entries.kind(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, inline: Bool, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode) -> Result<&2, &2, E.Ext4Error, List<&2, DR.Ext2Dirent>>:
  match inline:
    case True{}:
      IN.Ext4Inline.entries(~Dv, ~block_size, ~read_block, d, fs, i)
    case False{}:
      E.Ext4Error.lift(List<&2, DR.Ext2Dirent>, DR.Ext2Dir.entries(~Dv, ~block_size, ~read_block, d, S.Ext4Fs.ext2(fs), i))

# every used entry of directory i, "." and ".." first (an htree directory
# read linearly, its leaves in block order)
def Ext4Dir.entries(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode) -> Result<&2, &2, E.Ext4Error, List<&2, DR.Ext2Dirent>>:
  do Result<&2, &2, E.Ext4Error, List<&2, DR.Ext2Dirent>>:
    E.Ext4.require(N.Ext2Inode.is_dir(i), E.Ext4NotDir{N.Ext2Inode.number_of(i)})
    Ext4Dir.entries.kind(~Dv, ~block_size, ~read_block, IN.Ext4Inline.is_inline(i), d, fs, i)
