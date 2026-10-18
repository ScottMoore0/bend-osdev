# bend-osdev-ext4: inline data: files and directories kept in the inode
# (the ext4 disk-layout documentation, "Inline Data").
#
# An inode with EXT4_INLINE_DATA_FL keeps its first 60 bytes in i_block and
# the rest in the value of its "system.data" attribute, in the inode body.
# An inline directory keeps its parent's inode number in i_block's first 4
# bytes and entries in the other 56; more entries fill the "system.data"
# value. The two are separate regions: no entry spans them. "." and ".."
# are not stored; the listing gives them first, as a block directory's does.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ../ext2/super.bend as XS
import ../ext2/inode.bend as N
import ../ext2/dir.bend as DR
import ./error.bend as E
import ./super.bend as S
import ./inode.bend as I
import ./xattr.bend as XA

def Ext4Inline.is_inline(+i: N.Ext2Inode) -> Bool:
  N.Ext2Inode.has_flag(i, I.Ext4Inode.flag_inline_data())

def Ext4Inline.data.pick(hit: Bool, x: XA.Ext4Xattr, rest: Maybe<&2, B.Octets>) -> Maybe<&2, B.Octets>:
  match hit:
    case True{}:
      Some{XA.Ext4Xattr.value(x)}
    case False{}:
      rest

# the value of "system.data" (name index 7, name "data") among xs
def Ext4Inline.system_data(xs: List<&2, XA.Ext4Xattr>) -> Maybe<&2, B.Octets>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, t}:
      Ext4Inline.data.pick(Bool.and(U32.is_eq(XA.Ext4Xattr.index(x), 7), B.Octets.is_eq(XA.Ext4Xattr.name(x), B.Octets.of_string("data"))), x, Ext4Inline.system_data(t))

def Ext4Inline.got.none(need: Bool, +ino: Nat) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  match need:
    case True{}:
      Fail{E.Ext4BadInline{ino, "no system.data attribute"}}
    case False{}:
      Done{B.Octets.empty()}

def Ext4Inline.got(m: Maybe<&2, B.Octets>, +need: Bool, +ino: Nat) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  match m:
    case Some{v}:
      Done{v}
    case None{}:
      Ext4Inline.got.none(need, ino)

# the "system.data" value of inode n (empty if there is none and none is
# needed)
def Ext4Inline.extra(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +n: Nat, +need: Bool) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  do Result<&2, &2, E.Ext4Error, B.Octets>:
    raw : B.Octets <- I.Ext4Inode.raw(~Dv, ~block_size, ~read_block, d, fs, n)
    xs : List<&2, XA.Ext4Xattr> <- XA.Ext4Xattr.ibody(raw, n, S.Ext4Fs.verify(fs))
    Ext4Inline.got(Ext4Inline.system_data(xs), need, n)

# Files

def Ext4Inline.data.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, small: Bool, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode, +size: Nat) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  match small:
    case True{}:
      Done{B.Octets.take(size, N.Ext2Inode.block(i))}
    case False{}:
      +n = N.Ext2Inode.number_of(i)
      do Result<&2, &2, E.Ext4Error, B.Octets>:
        v : B.Octets <- Ext4Inline.extra(~Dv, ~block_size, ~read_block, d, fs, n, True{})
        +o : B.Octets = B.Octets.append(N.Ext2Inode.block(i), B.Octets.take(Nat.sub(size, 60n), v))
        E.Ext4.require(Nat.is_eq(B.Octets.len(o), size), E.Ext4BadInline{n, "the data is shorter than the size"})
        return o

# the content of an inline file (or symbolic link): i_block, then the
# system.data value, up to the size
def Ext4Inline.data(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode) -> Result<&2, &2, E.Ext4Error, B.Octets>:
  +size = N.Ext2Inode.size_nat(i)
  do Result<&2, &2, E.Ext4Error, B.Octets>:
    E.Ext4.require(Ext4Inline.is_inline(i), E.Ext4NotInline{N.Ext2Inode.number_of(i)})
    Ext4Inline.data.go(~Dv, ~block_size, ~read_block, Nat.is_le(size, 60n), d, fs, i, size)

# Directories: a region of entries, walked with ext2's codec and checks

type Ext4InStep is Data:
  Ext4InEnd{}
  Ext4InBad{why: String}
  Ext4InEnt{entry: DR.Ext2Dirent, rec_len: Nat}

def Ext4Inline.step.checked(why: Maybe<&2, String>, +e: DR.Ext2Dirent) -> Ext4InStep:
  match why:
    case None{}:
      Ext4InEnt{e, U32.to_nat(DR.Ext2Dirent.rec_len(e))}
    case Some{w}:
      Ext4InBad{w}

def Ext4Inline.step.decoded(m: Maybe<&2, DR.Ext2Dirent>, +avail: Nat, +inodes: Nat) -> Ext4InStep:
  match m:
    case None{}:
      Ext4InBad{"entry header past the end of the region"}
    case Some{+e}:
      Ext4Inline.step.checked(DR.Ext2Dirent.check(e, avail, inodes), e)

def Ext4Inline.step.pick(done: Bool, room: Bool, +filetype: Bool, +o: B.Octets, +avail: Nat, +inodes: Nat) -> Ext4InStep:
  match done room:
    case True{} _:
      Ext4InEnd{}
    case False{} False{}:
      Ext4InBad{"entry header past the end of the region"}
    case False{} True{}:
      Ext4Inline.step.decoded(DR.Ext2Dirent.decode(filetype, o), avail, inodes)

# what is at the start of o, avail bytes of the region left
def Ext4Inline.step(+filetype: Bool, +o: B.Octets, +avail: Nat, +inodes: Nat) -> Ext4InStep:
  Ext4Inline.step.pick(Nat.is_eq(avail, 0n), Nat.is_le(8n, avail), filetype, o, avail, inodes)

def Ext4Inline.keep(unused: Bool, e: DR.Ext2Dirent, acc: List<&2, DR.Ext2Dirent>) -> List<&2, DR.Ext2Dirent>:
  match unused:
    case True{}:
      acc
    case False{}:
      Con{e, acc}

def Ext4Inline.walk(fuel: Nat, st: Ext4InStep, o: B.Octets, +avail: Nat, +filetype: Bool, +inodes: Nat, +ino: Nat, acc: List<&2, DR.Ext2Dirent>) -> Result<&2, &2, E.Ext4Error, List<&2, DR.Ext2Dirent>>:
  match fuel st:
    case 0n _:
      Fail{E.Ext4BadInline{ino, "too many entries"}}
    case 1n+f Ext4InEnd{}:
      Done{List.reverse(&2, DR.Ext2Dirent, acc)}
    case 1n+f Ext4InBad{w}:
      Fail{E.Ext4BadInline{ino, w}}
    case 1n+f Ext4InEnt{+e, +rec}:
      +rest = B.Octets.drop(rec, o)
      +left = Nat.sub(avail, rec)
      Ext4Inline.walk(f, Ext4Inline.step(filetype, rest, left, inodes), rest, left, filetype, inodes, ino, Ext4Inline.keep(U32.is_eq(DR.Ext2Dirent.inode(e), 0), e, acc))

# the used entries of a region of directory entries
def Ext4Inline.region(+o: B.Octets, +filetype: Bool, +inodes: Nat, +ino: Nat) -> Result<&2, &2, E.Ext4Error, List<&2, DR.Ext2Dirent>>:
  +n = B.Octets.len(o)
  Ext4Inline.walk(Nat.add(Nat.div(n, 8n), 2n), Ext4Inline.step(filetype, o, n, inodes), o, n, filetype, inodes, ino, Nil{})

def Ext4Inline.more(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, big: Bool, +d: Dv, +fs: S.Ext4Fs, +ino: Nat, +filetype: Bool, +inodes: Nat) -> Result<&2, &2, E.Ext4Error, List<&2, DR.Ext2Dirent>>:
  match big:
    case False{}:
      Done{Nil{}}
    case True{}:
      do Result<&2, &2, E.Ext4Error, List<&2, DR.Ext2Dirent>>:
        v : B.Octets <- Ext4Inline.extra(~Dv, ~block_size, ~read_block, d, fs, ino, True{})
        Ext4Inline.region(v, filetype, inodes, ino)

def Ext4Inline.ft(filetype: Bool) -> U32:
  match filetype:
    case True{}:
      2
    case False{}:
      0

# the entries of an inline directory: ".", "..", those in i_block, then
# those in the system.data value
def Ext4Inline.entries(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext4Fs, +i: N.Ext2Inode) -> Result<&2, &2, E.Ext4Error, List<&2, DR.Ext2Dirent>>:
  +n = N.Ext2Inode.number_of(i)
  +blk = N.Ext2Inode.block(i)
  +filetype = S.Ext4Fs.has_incompat(fs, XS.Ext2Super.incompat_filetype())
  +inodes = XS.Ext2Fs.inodes_count(S.Ext4Fs.ext2(fs))
  +ft = Ext4Inline.ft(filetype)
  do Result<&2, &2, E.Ext4Error, List<&2, DR.Ext2Dirent>>:
    E.Ext4.require(Ext4Inline.is_inline(i), E.Ext4NotInline{n})
    a : List<&2, DR.Ext2Dirent> <- Ext4Inline.region(B.Octets.slice(4n, 56n, blk), filetype, inodes, n)
    b : List<&2, DR.Ext2Dirent> <- Ext4Inline.more(~Dv, ~block_size, ~read_block, Nat.is_lt(60n, N.Ext2Inode.size_nat(i)), d, fs, n, filetype, inodes)
    return Con{DR.Ext2Dirent{U32.from_nat(n), 12, 1, ft, B.Octets.of_string(".")}, Con{DR.Ext2Dirent{Maybe.default(&2, U32, B.Octets.le32_at(blk, 0n), 0), 12, 2, ft, B.Octets.of_string("..")}, List.append(&2, DR.Ext2Dirent, a, b)}}
