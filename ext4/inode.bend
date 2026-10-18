# bend-osdev-ext4: an inode's raw record, for the parts ext2's reader does
# not keep: the extra fields after byte 128 and the extended attribute area
# after them (the ext4 disk-layout documentation, "Index Nodes", "Inode
# Size" and "Extended Attributes"), and i_atime, where an EA inode keeps its
# value's hash.
#
# The record is found through ext2's public defs: the inode's group and
# index (Ext2Inode.locate), the group's descriptor (Ext2Group.read) and its
# inode table. ext2's Ext2Inode.read checks the record's checksum; read the
# inode through it first.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../ext2/super.bend as XS
import ../ext2/group.bend as G
import ../ext2/inode.bend as N
import ./error.bend as E
import ./super.bend as S

# the i_flags bits this package uses
def Ext4Inode.flag_index() -> U32:
  4096

def Ext4Inode.flag_ea_inode() -> U32:
  2097152

def Ext4Inode.flag_inline_data() -> U32:
  268435456

# the inode_size bytes of inode n
def Ext4Inode.raw(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +n: Nat) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  +f = S.Ext4Fs.ext2(fs)
  +loc = N.Ext2Inode.locate(XS.Ext2Fs.inodes_per_group(f), n)
  +isz = XS.Ext2Fs.inode_size(f)
  +bs = XS.Ext2Fs.block_size(f)
  +off = Nat.mul(N.Ext2InodeLoc.index(loc), isz)
  do Result<&2, &2, E.Ext4Error, B.Octets>:
    E.Ext4.require(Bool.and(Nat.is_lt(0n, n), Nat.is_le(n, XS.Ext2Fs.inodes_count(f))), E.Ext4BadXattr{n, "no such inode"})
    g : G.Ext2Group <- E.Ext4Error.lift(G.Ext2Group, G.Ext2Group.read(~Dv, ~block_size, ~read_block, d, f, N.Ext2InodeLoc.group(loc)))
    +blk : Nat = Nat.add(G.Ext2Group.inode_table(g), Nat.div(off, bs))
    E.Ext4.require(Nat.is_lt(blk, XS.Ext2Fs.blocks(f)), E.Ext4BadXattr{n, "the inode table is outside the filesystem"})
    o : B.Octets <- E.Ext4Error.lift(B.Octets, XS.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, f, blk))
    return B.Octets.slice(Nat.mod(off, bs), isz, o)

def Ext4Inode.u16(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.le16_at(o, i), 0)

def Ext4Inode.u32(o: B.Octets, i: Nat) -> U32:
  Maybe.default(&2, U32, B.Octets.le32_at(o, i), 0)

def Ext4Inode.atime(+raw: B.Octets) -> U32:
  Ext4Inode.u32(raw, 8n)

def Ext4Inode.extra.pick(big: Bool, +raw: B.Octets) -> Nat:
  match big:
    case True{}:
      U32.to_nat(Ext4Inode.u16(raw, 128n))
    case False{}:
      0n

# where the in-inode attribute area starts: after the 128-byte base record
# and i_extra_isize bytes (none in a 128-byte inode)
def Ext4Inode.ea_offset(+raw: B.Octets) -> Nat:
  Nat.add(128n, Ext4Inode.extra.pick(Nat.is_lt(128n, B.Octets.len(raw)), raw))
