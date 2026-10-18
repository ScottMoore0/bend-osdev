# bend-osdev-ext2: the writer's operations on paths: creating files,
# directories, symbolic links (fast and slow) and hard links; unlinking
# (freeing the inode and its blocks when the last link goes); removing empty
# directories; renaming; and writing, appending to and truncating files.
#
# Every operation takes blockdev's pure interface and a pure write as
# template arguments, the device, the filesystem (opened by Ext2.open) and
# the write options, and answers the device after the operation, or why it
# was refused (Ext2Error). A refused operation hands back no device: the
# caller's device is as it was, so every operation is all or nothing.
#
# Paths are "/"-separated from the root, as the reader's; the parent of the
# last component is looked up as the reader looks paths up (following
# symbolic links as the filesystem's options allow).
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./field.bend as F
import ./super.bend as S
import ./inode.bend as N
import ./file.bend as FL
import ./dir.bend as DR
import ./ext2.bend as X
import ./meta.bend as T
import ./alloc.bend as A
import ./inodew.bend as IW
import ./filew.bend as FW
import ./extentw.bend as EW
import ./dirw.bend as DW
import ./wopts.bend as WO

# What the writer writes

# the incompat features written: filetype, meta_bg, extent, 64bit, flex_bg,
# metadata_csum_seed, large_dir
def Ext2W.incompat_writable() -> U32:
  25298

# the ro_compat features written: sparse_super, large_file, huge_file,
# gdt_csum, dir_nlink, extra_isize, metadata_csum
def Ext2W.ro_compat_writable() -> U32:
  1147

def Ext2W.ro_compat_names() -> List<&2, S.Ext2FeatureName>:
  [S.Ext2FeatureName{1, "sparse_super"}, S.Ext2FeatureName{2, "large_file"}, S.Ext2FeatureName{4, "btree_dir"}, S.Ext2FeatureName{8, "huge_file"}, S.Ext2FeatureName{16, "gdt_csum"}, S.Ext2FeatureName{32, "dir_nlink"}, S.Ext2FeatureName{64, "extra_isize"}, S.Ext2FeatureName{128, "has_snapshot"}, S.Ext2FeatureName{256, "quota"}, S.Ext2FeatureName{512, "bigalloc"}, S.Ext2FeatureName{1024, "metadata_csum"}, S.Ext2FeatureName{2048, "replica"}, S.Ext2FeatureName{4096, "read-only"}, S.Ext2FeatureName{8192, "project"}, S.Ext2FeatureName{16384, "shared_blocks"}, S.Ext2FeatureName{32768, "verity"}, S.Ext2FeatureName{65536, "orphan_present"}]

def Ext2W.refuses_csum(c: WO.Ext2CsumMode, +fs: S.Ext2Fs) -> Bool:
  match c:
    case WO.Ext2CsumRefuse{}:
      T.Ext2Meta.has_uninit(fs)
    case WO.Ext2CsumUpdate{}:
      False{}

# whether this writer may write the filesystem with these options: every
# incompat and ro_compat feature it carries is one written here, the options
# do not refuse its checksums, it is not marked as having errors, its blocks
# are at most 32 KiB (rec_len has no room for 64 KiB), and its journal (if
# any) needs no recovery
def Ext2W.writable(+fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions) -> Result<&2, &2, E.Ext2Error, Unit>:
  +sb = S.Ext2Fs.sb(fs)
  +inc = U32.and(S.Ext2Super.feature_incompat(sb), U32.not(Ext2W.incompat_writable()))
  +ro = U32.and(S.Ext2Super.feature_ro_compat(sb), U32.not(Ext2W.ro_compat_writable()))
  do Result<&2, &2, E.Ext2Error, Unit>:
    S.Ext2.require(U32.is_eq(inc, 0), E.Ext2CannotWrite{"the incompat feature " ++ S.Ext2Super.incompat_name(S.Ext2Super.lowest(inc))})
    S.Ext2.require(U32.is_eq(ro, 0), E.Ext2CannotWrite{"the ro_compat feature " ++ S.Ext2Super.name_of(Ext2W.ro_compat_names(), S.Ext2Super.lowest(ro))})
    S.Ext2.require(Bool.not(Ext2W.refuses_csum(WO.Ext2WriteOptions.csum(wo), fs)), E.Ext2CannotWrite{"metadata checksums (the options refuse them)"})
    S.Ext2.require(U32.is_eq(U32.and(S.Ext2Super.state(sb), 2), 0), E.Ext2CannotWrite{"the filesystem is marked as having errors"})
    S.Ext2.require(Nat.is_le(S.Ext2Fs.block_size(fs), 32768n), E.Ext2CannotWrite{"blocks of 64 KiB"})

# Paths and names

type Ext2PathParts is Data:
  Ext2PathParts{parent: B.Octets, name: B.Octets}

def Ext2W.join(cs: List<&2, B.Octets>, acc: B.Octets) -> B.Octets:
  match cs:
    case Nil{}:
      acc
    case Con{c, t}:
      Ext2W.join(t, B.Octets.append(acc, B.Octets.append(B.Octets.of_string("/"), c)))

def Ext2W.split.go(cs: List<&2, B.Octets>, acc: List<&2, B.Octets>) -> Result<&2, &2, E.Ext2Error, Ext2PathParts>:
  match cs:
    case Nil{}:
      Fail{E.Ext2BadName{"the root directory"}}
    case Con{c, Nil{}}:
      Done{Ext2PathParts{Ext2W.join(List.reverse(&2, B.Octets, acc), B.Octets.empty()), c}}
    case Con{c, Con{c2, t}}:
      Ext2W.split.go(Con{c2, t}, Con{c, acc})

# a path's parent directory and last component
def Ext2W.split(+path: B.Octets) -> Result<&2, &2, E.Ext2Error, Ext2PathParts>:
  Ext2W.split.go(X.Ext2Path.components(path), Nil{})

def Ext2W.has_nul(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      Bool.or(U32.is_eq(x, 0), Ext2W.has_nul(t))

# whether a name can be a directory entry's: 1 to 255 bytes, no NUL, not
# "." or ".."
def Ext2W.check_name(+name: B.Octets) -> Result<&2, &2, E.Ext2Error, Unit>:
  +n = B.Octets.len(name)
  do Result<&2, &2, E.Ext2Error, Unit>:
    S.Ext2.require(Nat.is_lt(0n, n), E.Ext2BadName{"empty"})
    S.Ext2.require(Nat.is_le(n, 255n), E.Ext2BadName{"longer than 255 bytes"})
    S.Ext2.require(Bool.not(Ext2W.has_nul(B.Octets.to_list(name))), E.Ext2BadName{"contains a NUL byte"})
    S.Ext2.require(Bool.not(Bool.or(B.Octets.is_eq(name, B.Octets.of_string(".")), B.Octets.is_eq(name, B.Octets.of_string("..")))), E.Ext2BadName{". or .."})

def Ext2W.is_dir(+i: N.Ext2Inode) -> Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
  do Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
    S.Ext2.require(N.Ext2Inode.is_dir(i), E.Ext2NotDir{N.Ext2Inode.number_of(i)})
    return i

# the directory a path names
def Ext2W.dir_at(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +path: B.Octets) -> Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
  do Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
    i : N.Ext2Inode <- X.Ext2.lookup(~Dv, ~block_size, ~read_block, d, fs, path)
    Ext2W.is_dir(i)

def Ext2W.absent.pick(m: Maybe<&2, DR.Ext2Dirent>, +name: B.Octets) -> Result<&2, &2, E.Ext2Error, Unit>:
  match m:
    case None{}:
      Done{Unit{}}
    case Some{e}:
      Fail{E.Ext2Exists{B.Octets.to_string(name)}}

# that directory i has no entry named name
def Ext2W.absent(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +name: B.Octets) -> Result<&2, &2, E.Ext2Error, Unit>:
  do Result<&2, &2, E.Ext2Error, Unit>:
    m : Maybe<&2, DR.Ext2Dirent> <- DR.Ext2Dir.find(~Dv, ~block_size, ~read_block, d, fs, i, name)
    Ext2W.absent.pick(m, name)

def Ext2W.found(m: Maybe<&2, DR.Ext2Dirent>, +name: B.Octets) -> Result<&2, &2, E.Ext2Error, DR.Ext2Dirent>:
  match m:
    case Some{e}:
      Done{e}
    case None{}:
      Fail{E.Ext2NotFound{B.Octets.to_string(name)}}

# the inode directory i names name
def Ext2W.child(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +i: N.Ext2Inode, +name: B.Octets) -> Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
  do Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
    m : Maybe<&2, DR.Ext2Dirent> <- DR.Ext2Dir.find(~Dv, ~block_size, ~read_block, d, fs, i, name)
    e : DR.Ext2Dirent <- Ext2W.found(m, name)
    N.Ext2Inode.read(~Dv, ~block_size, ~read_block, d, fs, U32.to_nat(DR.Ext2Dirent.inode(e)))

def Ext2W.ftype_of(+fs: S.Ext2Fs, +i: N.Ext2Inode) -> U32:
  DW.Ext2DirW.ftype(fs, DW.Ext2DirW.code(N.Ext2Inode.kind(i)))

# Inodes

# whether new inodes get extent trees
def Ext2W.use_extents(+fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions) -> Bool:
  Bool.and(WO.Ext2WriteOptions.extents(wo), S.Ext2Fs.has_incompat(fs, S.Ext2Super.incompat_extents()))

def Ext2W.new_flags(ext: Bool) -> U32:
  match ext:
    case True{}:
      N.Ext2Inode.flag_extents()
    case False{}:
      0

def Ext2W.new_iblock(ext: Bool) -> B.Octets:
  match ext:
    case True{}:
      EW.Ext2ExtW.empty_root()
    case False{}:
      B.Octets.zeros(60n)

# a new inode's record of the given mode and links, mapped as the options
# say (an extent tree or a block map)
def Ext2W.record(+fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +mode: U32, +links: U32) -> B.Octets:
  +ext = Ext2W.use_extents(fs, wo)
  IW.Ext2InodeW.fresh(fs, mode, WO.Ext2WriteOptions.uid(wo), WO.Ext2WriteOptions.gid(wo), WO.Ext2WriteOptions.time(wo), links, Ext2W.new_flags(ext), Ext2W.new_iblock(ext))

# an inode's link count moved up or down by one (and its change time set)
def Ext2W.relink.go(up: Bool, +raw: B.Octets, +ino: Nat) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  match up:
    case True{}:
      +l = IW.Ext2IRaw.links(raw)
      do Result<&2, &2, E.Ext2Error, B.Octets>:
        S.Ext2.require(U32.is_lt(l, 65000), E.Ext2TooManyLinks{ino})
        return IW.Ext2IRaw.set_links(raw, U32.add(l, 1))
    case False{}:
      +l = IW.Ext2IRaw.links(raw)
      do Result<&2, &2, E.Ext2Error, B.Octets>:
        S.Ext2.require(U32.is_lt(0, l), E.Ext2CheckFailed{"a link count below zero"})
        return IW.Ext2IRaw.set_links(raw, U32.sub(l, 1))

def Ext2W.relink(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, up: Bool) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    +raw : B.Octets <- IW.Ext2InodeW.read_raw(~Dv, ~block_size, ~read_block, d, fs, ino)
    raw2 : B.Octets <- Ext2W.relink.go(up, raw, ino)
    IW.Ext2InodeW.write_raw(~Dv, ~block_size, ~read_block, ~write_block, d, fs, ino, IW.Ext2IRaw.set_ctime(raw2, WO.Ext2WriteOptions.time(wo)))

def Ext2W.release.cut(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, fast: Bool, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
  match fast:
    case True{}:
      Done{T.Ext2Out{d, raw}}
    case False{}:
      FW.Ext2FileW.truncate(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, raw, 0n)

def Ext2W.release.fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, B.Octets>, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +dir: Bool) -> Result<&2, &2, E.Ext2Error, Dv>:
  match out:
    case T.Ext2Out{d1, raw1}:
      do Result<&2, &2, E.Ext2Error, Dv>:
        d2 : Dv <- IW.Ext2InodeW.write_raw(~Dv, ~block_size, ~read_block, ~write_block, d1, fs, ino, IW.Ext2IRaw.set_dtime(IW.Ext2IRaw.set_links(raw1, 0), U32.max(U32.from_nat(Nat.add(S.Ext2Fs.inodes_count(fs), 1n)), WO.Ext2WriteOptions.time(wo))))
        A.Ext2Alloc.free_inode(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, ino, dir)

# an inode whose last link went: its blocks freed (a fast symbolic link has
# none), its record marked deleted, and the inode freed
def Ext2W.release(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  +i = IW.Ext2IRaw.inode(fs, ino, raw)
  do Result<&2, &2, E.Ext2Error, Dv>:
    S.Ext2.require(Nat.is_eq(IW.Ext2IRaw.file_acl(raw), 0n), E.Ext2Xattr{ino})
    out : T.Ext2Out<Dv, B.Octets> <- Ext2W.release.cut(~Dv, ~block_size, ~read_block, ~write_block, Bool.and(N.Ext2Inode.is_symlink(i), FL.Ext2File.is_fast_symlink(fs, i)), d, fs, wo, ino, raw)
    Ext2W.release.fin(~Dv, ~block_size, ~read_block, ~write_block, out, fs, wo, ino, N.Ext2Inode.is_dir(i))

def Ext2W.unlinked(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, last: Bool, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  match last:
    case True{}:
      Ext2W.release(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, raw)
    case False{}:
      IW.Ext2InodeW.write_raw(~Dv, ~block_size, ~read_block, ~write_block, d, fs, ino, IW.Ext2IRaw.set_ctime(IW.Ext2IRaw.set_links(raw, U32.sub(IW.Ext2IRaw.links(raw), 1)), WO.Ext2WriteOptions.time(wo)))

# one link of inode ino gone (a file's: the inode is released with its last)
def Ext2W.drop_link(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    +raw : B.Octets <- IW.Ext2InodeW.read_raw(~Dv, ~block_size, ~read_block, d, fs, ino)
    Ext2W.unlinked(~Dv, ~block_size, ~read_block, ~write_block, U32.is_le(IW.Ext2IRaw.links(raw), 1), d, fs, wo, ino, raw)

# Creating

def Ext2W.add_entry(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, Nat>, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +parent: Nat, +code: U32, +name: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  match out:
    case T.Ext2Out{d, ino}:
      DW.Ext2DirW.add(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, parent, ino, DW.Ext2DirW.ftype(fs, code), name)

# a new inode for a child of the directory parent, its record raw written
def Ext2W.new_inode.fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, Nat>, +fs: S.Ext2Fs, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
  match out:
    case T.Ext2Out{d, +ino}:
      Result.map(&2, &2, E.Ext2Error, Dv, T.Ext2Out<Dv, Nat>, d2 => T.Ext2Out{d2, ino}, IW.Ext2InodeW.write_raw(~Dv, ~block_size, ~read_block, ~write_block, d, fs, ino, raw))

def Ext2W.new_inode(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +parent: Nat, +dir: Bool, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
    out : T.Ext2Out<Dv, Nat> <- A.Ext2Alloc.inode(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, parent, dir)
    Ext2W.new_inode.fin(~Dv, ~block_size, ~read_block, ~write_block, out, fs, raw)

# where a new entry goes: the parent directory (checked to have no entry of
# that name) and the name (checked)
def Ext2W.place(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, pp: Ext2PathParts, +d: Dv, +fs: S.Ext2Fs) -> Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
  match pp:
    case Ext2PathParts{+parent, +name}:
      do Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
        Ext2W.check_name(name)
        +p : N.Ext2Inode <- Ext2W.dir_at(~Dv, ~block_size, ~read_block, d, fs, parent)
        Ext2W.absent(~Dv, ~block_size, ~read_block, d, fs, p, name)
        return p

def Ext2PathParts.name(pp: Ext2PathParts) -> B.Octets:
  match pp:
    case Ext2PathParts{p, n}:
      n

def Ext2PathParts.parent(pp: Ext2PathParts) -> B.Octets:
  match pp:
    case Ext2PathParts{p, n}:
      p

def Ext2W.perm(+mode: U32) -> U32:
  U32.and(4095, mode)

# a new empty regular file (mode: its permission bits)
def Ext2W.create(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +path: B.Octets, +mode: U32) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    +pp : Ext2PathParts <- Ext2W.split(path)
    +p : N.Ext2Inode <- Ext2W.place(~Dv, ~block_size, ~read_block, pp, d, fs)
    +pino : Nat = N.Ext2Inode.number_of(p)
    out : T.Ext2Out<Dv, Nat> <- Ext2W.new_inode(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, pino, False{}, Ext2W.record(fs, wo, U32.or(32768, Ext2W.perm(mode)), 1))
    Ext2W.add_entry(~Dv, ~block_size, ~read_block, ~write_block, out, fs, wo, pino, 1, Ext2PathParts.name(pp))

def Ext2W.mkdir.data(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, Nat>, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +parent: Nat, +mode: U32) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
  match out:
    case T.Ext2Out{d, +ino}:
      +raw = Ext2W.record(fs, wo, U32.or(16384, Ext2W.perm(mode)), 2)
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
        +w : T.Ext2Out<Dv, B.Octets> <- FW.Ext2FileW.write(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, raw, 0n, DW.Ext2DirW.first_block(fs, ino, 0, parent))
        Ext2W.new_inode.fin(~Dv, ~block_size, ~read_block, ~write_block, T.Ext2Out{T.Ext2Out.dev(Dv, B.Octets, w), ino}, fs, T.Ext2Out.value(Dv, B.Octets, w))

# a new empty directory ("." and ".."; its parent gains a link)
def Ext2W.mkdir(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +path: B.Octets, +mode: U32) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    +pp : Ext2PathParts <- Ext2W.split(path)
    +p : N.Ext2Inode <- Ext2W.place(~Dv, ~block_size, ~read_block, pp, d, fs)
    +pino : Nat = N.Ext2Inode.number_of(p)
    S.Ext2.require(U32.is_lt(N.Ext2Inode.links(p), 65000), E.Ext2TooManyLinks{pino})
    a : T.Ext2Out<Dv, Nat> <- A.Ext2Alloc.inode(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, pino, True{})
    out : T.Ext2Out<Dv, Nat> <- Ext2W.mkdir.data(~Dv, ~block_size, ~read_block, ~write_block, a, fs, wo, pino, mode)
    d2 : Dv <- Ext2W.add_entry(~Dv, ~block_size, ~read_block, ~write_block, out, fs, wo, pino, 2, Ext2PathParts.name(pp))
    Ext2W.relink(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, wo, pino, True{})

def Ext2W.symlink.slow(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, Nat>, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +target: B.Octets) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
  match out:
    case T.Ext2Out{+d, +ino}:
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
        +w : T.Ext2Out<Dv, B.Octets> <- FW.Ext2FileW.write(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, Ext2W.record(fs, wo, 41471, 1), 0n, target)
        Ext2W.new_inode.fin(~Dv, ~block_size, ~read_block, ~write_block, T.Ext2Out{T.Ext2Out.dev(Dv, B.Octets, w), ino}, fs, T.Ext2Out.value(Dv, B.Octets, w))

def Ext2W.symlink.data(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, fast: Bool, out: T.Ext2Out<Dv, Nat>, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +target: B.Octets) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
  match fast:
    case True{}:
      +n = B.Octets.len(target)
      +raw = IW.Ext2IRaw.set_size(IW.Ext2InodeW.fresh(fs, 41471, WO.Ext2WriteOptions.uid(wo), WO.Ext2WriteOptions.gid(wo), WO.Ext2WriteOptions.time(wo), 1, 0, B.Octets.append(target, B.Octets.zeros(Nat.sub(60n, n)))), n)
      Ext2W.new_inode.fin(~Dv, ~block_size, ~read_block, ~write_block, out, fs, raw)
    case False{}:
      Ext2W.symlink.slow(~Dv, ~block_size, ~read_block, ~write_block, out, fs, wo, target)

# a new symbolic link to target: fast (in i_block) under 60 bytes, else
# slow (in a data block); the target is 1 to block_size - 1 bytes
def Ext2W.symlink(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +path: B.Octets, +target: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  +n = B.Octets.len(target)
  do Result<&2, &2, E.Ext2Error, Dv>:
    S.Ext2.require(Bool.and(Nat.is_lt(0n, n), Nat.is_lt(n, S.Ext2Fs.block_size(fs))), E.Ext2BadName{"a symbolic link target of that length"})
    +pp : Ext2PathParts <- Ext2W.split(path)
    +p : N.Ext2Inode <- Ext2W.place(~Dv, ~block_size, ~read_block, pp, d, fs)
    +pino : Nat = N.Ext2Inode.number_of(p)
    a : T.Ext2Out<Dv, Nat> <- A.Ext2Alloc.inode(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, pino, False{})
    out : T.Ext2Out<Dv, Nat> <- Ext2W.symlink.data(~Dv, ~block_size, ~read_block, ~write_block, Nat.is_lt(n, 60n), a, fs, wo, target)
    Ext2W.add_entry(~Dv, ~block_size, ~read_block, ~write_block, out, fs, wo, pino, 7, Ext2PathParts.name(pp))

# a new hard link at path to what target names (not a directory; a final
# symbolic link is linked itself, not followed)
def Ext2W.link(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +target: B.Octets, +path: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    +i : N.Ext2Inode <- X.Ext2.lookup_link(~Dv, ~block_size, ~read_block, d, fs, target)
    +ino : Nat = N.Ext2Inode.number_of(i)
    S.Ext2.require(Bool.not(N.Ext2Inode.is_dir(i)), E.Ext2IsDir{ino})
    S.Ext2.require(U32.is_lt(N.Ext2Inode.links(i), 65000), E.Ext2TooManyLinks{ino})
    +pp : Ext2PathParts <- Ext2W.split(path)
    +p : N.Ext2Inode <- Ext2W.place(~Dv, ~block_size, ~read_block, pp, d, fs)
    d2 : Dv <- DW.Ext2DirW.add(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, N.Ext2Inode.number_of(p), ino, Ext2W.ftype_of(fs, i), Ext2PathParts.name(pp))
    Ext2W.relink(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, wo, ino, True{})

# Removing

# the parent directory of an existing entry, and what the entry names
type Ext2Target is Data:
  Ext2Target{dir: N.Ext2Inode, name: B.Octets, inode: N.Ext2Inode}

def Ext2W.target.at(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, pp: Ext2PathParts, +d: Dv, +fs: S.Ext2Fs) -> Result<&2, &2, E.Ext2Error, Ext2Target>:
  match pp:
    case Ext2PathParts{+parent, +name}:
      do Result<&2, &2, E.Ext2Error, Ext2Target>:
        Ext2W.check_name(name)
        +p : N.Ext2Inode <- Ext2W.dir_at(~Dv, ~block_size, ~read_block, d, fs, parent)
        c : N.Ext2Inode <- Ext2W.child(~Dv, ~block_size, ~read_block, d, fs, p, name)
        return Ext2Target{p, name, c}

def Ext2W.target(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +path: B.Octets) -> Result<&2, &2, E.Ext2Error, Ext2Target>:
  do Result<&2, &2, E.Ext2Error, Ext2Target>:
    pp : Ext2PathParts <- Ext2W.split(path)
    Ext2W.target.at(~Dv, ~block_size, ~read_block, pp, d, fs)

def Ext2W.unlink.at(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, t: Ext2Target, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions) -> Result<&2, &2, E.Ext2Error, Dv>:
  match t:
    case Ext2Target{p, +name, +c}:
      +cino = N.Ext2Inode.number_of(c)
      do Result<&2, &2, E.Ext2Error, Dv>:
        S.Ext2.require(Bool.not(N.Ext2Inode.is_dir(c)), E.Ext2IsDir{cino})
        out : T.Ext2Out<Dv, DW.Ext2Slot> <- DW.Ext2DirW.remove(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, N.Ext2Inode.number_of(p), name)
        Ext2W.drop_link(~Dv, ~block_size, ~read_block, ~write_block, T.Ext2Out.dev(Dv, DW.Ext2Slot, out), fs, wo, cino)

# the entry at path removed (not a directory's); the inode is freed with
# its blocks when this was its last link
def Ext2W.unlink(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +path: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    t : Ext2Target <- Ext2W.target(~Dv, ~block_size, ~read_block, d, fs, path)
    Ext2W.unlink.at(~Dv, ~block_size, ~read_block, ~write_block, t, d, fs, wo)

# an empty directory's inode, whose entry has been removed, released (and
# its parent's link from ".." dropped)
def Ext2W.drop_dir(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +parent: Nat, +ino: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    +d2 : Dv <- Ext2W.relink(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, parent, False{})
    raw : B.Octets <- IW.Ext2InodeW.read_raw(~Dv, ~block_size, ~read_block, d2, fs, ino)
    Ext2W.release(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, wo, ino, raw)

def Ext2W.rmdir.at(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, t: Ext2Target, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions) -> Result<&2, &2, E.Ext2Error, Dv>:
  match t:
    case Ext2Target{+p, +name, +c}:
      +cino = N.Ext2Inode.number_of(c)
      +pino = N.Ext2Inode.number_of(p)
      do Result<&2, &2, E.Ext2Error, Dv>:
        S.Ext2.require(N.Ext2Inode.is_dir(c), E.Ext2NotDir{cino})
        empty : Bool <- DW.Ext2DirW.is_empty(~Dv, ~block_size, ~read_block, d, fs, c)
        S.Ext2.require(empty, E.Ext2NotEmpty{cino})
        out : T.Ext2Out<Dv, DW.Ext2Slot> <- DW.Ext2DirW.remove(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, pino, name)
        Ext2W.drop_dir(~Dv, ~block_size, ~read_block, ~write_block, T.Ext2Out.dev(Dv, DW.Ext2Slot, out), fs, wo, pino, cino)

# the empty directory at path removed
def Ext2W.rmdir(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +path: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    t : Ext2Target <- Ext2W.target(~Dv, ~block_size, ~read_block, d, fs, path)
    Ext2W.rmdir.at(~Dv, ~block_size, ~read_block, ~write_block, t, d, fs, wo)

# Renaming

def Ext2W.dotdot(+e: DR.Ext2Dirent) -> Nat:
  U32.to_nat(DR.Ext2Dirent.inode(e))

def Ext2W.up.pick(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, hit: Bool, top: Bool, +d: Dv, +fs: S.Ext2Fs, +cur: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  match hit top:
    case True{} _:
      Fail{E.Ext2RenameLoop{}}
    case False{} True{}:
      Done{None{}}
    case False{} False{}:
      do Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
        i : N.Ext2Inode <- N.Ext2Inode.read(~Dv, ~block_size, ~read_block, d, fs, cur)
        m : Maybe<&2, DR.Ext2Dirent> <- DR.Ext2Dir.find(~Dv, ~block_size, ~read_block, d, fs, i, B.Octets.of_string(".."))
        e : DR.Ext2Dirent <- Ext2W.found(m, B.Octets.of_string(".."))
        return Some{Ext2W.dotdot(e)}

def Ext2W.up(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +moved: Nat, +cur: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  Ext2W.up.pick(~Dv, ~block_size, ~read_block, Nat.is_eq(cur, moved), Nat.is_eq(cur, X.Ext2.root_ino()), d, fs, cur)

# from directory cur up to the root (through ".."), never meeting moved
def Ext2W.no_loop.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, fuel: Nat, r: Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>, +d: Dv, +fs: S.Ext2Fs, +moved: Nat) -> Result<&2, &2, E.Ext2Error, Unit>:
  match fuel r:
    case _ Fail{e}:
      Fail{e}
    case _ Done{None{}}:
      Done{Unit{}}
    case 0n Done{Some{c}}:
      Fail{E.Ext2CheckFailed{"a directory loop above the target"}}
    case 1n+f Done{Some{+c}}:
      Ext2W.no_loop.go(~Dv, ~block_size, ~read_block, f, Ext2W.up(~Dv, ~block_size, ~read_block, d, fs, moved, c), d, fs, moved)

# a directory moved into dir would not end up below itself
def Ext2W.no_loop(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, isdir: Bool, +d: Dv, +fs: S.Ext2Fs, +moved: Nat, +dir: Nat) -> Result<&2, &2, E.Ext2Error, Unit>:
  match isdir:
    case True{}:
      Ext2W.no_loop.go(~Dv, ~block_size, ~read_block, Nat.add(S.Ext2Fs.inodes_count(fs), 1n), Done{Some{dir}}, d, fs, moved)
    case False{}:
      Done{Unit{}}

# a moved directory whose parent changed: its ".." pointed at the new
# parent, the old parent losing a link and the new one gaining it
def Ext2W.reparent(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, moves: Bool, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +s: Nat, +from: Nat, +to: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  match moves:
    case False{}:
      Done{d}
    case True{}:
      do Result<&2, &2, E.Ext2Error, Dv>:
        out : T.Ext2Out<Dv, DW.Ext2Slot> <- DW.Ext2DirW.retarget(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, s, B.Octets.of_string(".."), to, DW.Ext2DirW.ftype(fs, 2))
        d2 : Dv <- Ext2W.relink(~Dv, ~block_size, ~read_block, ~write_block, T.Ext2Out.dev(Dv, DW.Ext2Slot, out), fs, wo, from, False{})
        Ext2W.relink(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, wo, to, True{})

# the target that a rename replaces, released: an empty directory (its
# parent losing the link from its "..") or one link of anything else
def Ext2W.replaced(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, isdir: Bool, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +parent: Nat, +t: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  match isdir:
    case True{}:
      Ext2W.drop_dir(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, parent, t)
    case False{}:
      Ext2W.drop_link(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, t)

# that a rename of s may replace t: a directory only an empty directory,
# anything else only a non-directory
def Ext2W.may_replace(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, sdir: Bool, +d: Dv, +fs: S.Ext2Fs, +t: N.Ext2Inode) -> Result<&2, &2, E.Ext2Error, Unit>:
  match sdir:
    case True{}:
      +tino = N.Ext2Inode.number_of(t)
      do Result<&2, &2, E.Ext2Error, Unit>:
        S.Ext2.require(N.Ext2Inode.is_dir(t), E.Ext2NotDir{tino})
        empty : Bool <- DW.Ext2DirW.is_empty(~Dv, ~block_size, ~read_block, d, fs, t)
        S.Ext2.require(empty, E.Ext2NotEmpty{tino})
    case False{}:
      S.Ext2.require(Bool.not(N.Ext2Inode.is_dir(t)), E.Ext2IsDir{N.Ext2Inode.number_of(t)})

def Ext2W.rename.new(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +sdir: Nat, +sname: B.Octets, +s: N.Ext2Inode, +ddir: Nat, +dname: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  +sino = N.Ext2Inode.number_of(s)
  +isdir = N.Ext2Inode.is_dir(s)
  do Result<&2, &2, E.Ext2Error, Dv>:
    Ext2W.no_loop(~Dv, ~block_size, ~read_block, isdir, d, fs, sino, ddir)
    d1 : Dv <- DW.Ext2DirW.add(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ddir, sino, Ext2W.ftype_of(fs, s), dname)
    o2 : T.Ext2Out<Dv, DW.Ext2Slot> <- DW.Ext2DirW.remove(~Dv, ~block_size, ~read_block, ~write_block, d1, fs, wo, sdir, sname)
    Ext2W.reparent(~Dv, ~block_size, ~read_block, ~write_block, Bool.and(isdir, Bool.not(Nat.is_eq(sdir, ddir))), T.Ext2Out.dev(Dv, DW.Ext2Slot, o2), fs, wo, sino, sdir, ddir)

def Ext2W.rename.replace(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, same: Bool, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +sdir: Nat, +sname: B.Octets, +s: N.Ext2Inode, +ddir: Nat, +dname: B.Octets, +tino: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  match same:
    case True{}:
      Done{d}
    case False{}:
      +sino = N.Ext2Inode.number_of(s)
      +isdir = N.Ext2Inode.is_dir(s)
      do Result<&2, &2, E.Ext2Error, Dv>:
        +t : N.Ext2Inode <- N.Ext2Inode.read(~Dv, ~block_size, ~read_block, d, fs, tino)
        Ext2W.may_replace(~Dv, ~block_size, ~read_block, isdir, d, fs, t)
        Ext2W.no_loop(~Dv, ~block_size, ~read_block, isdir, d, fs, sino, ddir)
        o1 : T.Ext2Out<Dv, DW.Ext2Slot> <- DW.Ext2DirW.retarget(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ddir, dname, sino, Ext2W.ftype_of(fs, s))
        o2 : T.Ext2Out<Dv, DW.Ext2Slot> <- DW.Ext2DirW.remove(~Dv, ~block_size, ~read_block, ~write_block, T.Ext2Out.dev(Dv, DW.Ext2Slot, o1), fs, wo, sdir, sname)
        d3 : Dv <- Ext2W.replaced(~Dv, ~block_size, ~read_block, ~write_block, N.Ext2Inode.is_dir(t), T.Ext2Out.dev(Dv, DW.Ext2Slot, o2), fs, wo, ddir, tino)
        Ext2W.reparent(~Dv, ~block_size, ~read_block, ~write_block, Bool.and(isdir, Bool.not(Nat.is_eq(sdir, ddir))), d3, fs, wo, sino, sdir, ddir)

def Ext2W.rename.over(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, m: Maybe<&2, DR.Ext2Dirent>, src: Ext2Target, +ddir: Nat, +dname: B.Octets, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions) -> Result<&2, &2, E.Ext2Error, Dv>:
  match m src:
    case None{} Ext2Target{sd, sname, s}:
      Ext2W.rename.new(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, N.Ext2Inode.number_of(sd), sname, s, ddir, dname)
    case Some{+e} Ext2Target{sd, sname, +s}:
      Ext2W.rename.replace(~Dv, ~block_size, ~read_block, ~write_block, Nat.is_eq(Ext2W.dotdot(e), N.Ext2Inode.number_of(s)), d, fs, wo, N.Ext2Inode.number_of(sd), sname, s, ddir, dname, Ext2W.dotdot(e))

def Ext2W.rename.at(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, src: Ext2Target, pp: Ext2PathParts, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions) -> Result<&2, &2, E.Ext2Error, Dv>:
  match pp:
    case Ext2PathParts{+dparent, +dname}:
      do Result<&2, &2, E.Ext2Error, Dv>:
        Ext2W.check_name(dname)
        +dd : N.Ext2Inode <- Ext2W.dir_at(~Dv, ~block_size, ~read_block, d, fs, dparent)
        m : Maybe<&2, DR.Ext2Dirent> <- DR.Ext2Dir.find(~Dv, ~block_size, ~read_block, d, fs, dd, dname)
        Ext2W.rename.over(~Dv, ~block_size, ~read_block, ~write_block, m, src, N.Ext2Inode.number_of(dd), dname, d, fs, wo)

# the entry at path from renamed to path to (replacing what to names: a file
# by anything but a directory, an empty directory by a directory); a
# directory moved to another parent has its ".." changed and the link
# counts of both parents moved; a rename onto the same inode does nothing
def Ext2W.rename(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +from: B.Octets, +to: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    src : Ext2Target <- Ext2W.target(~Dv, ~block_size, ~read_block, d, fs, from)
    pp : Ext2PathParts <- Ext2W.split(to)
    Ext2W.rename.at(~Dv, ~block_size, ~read_block, ~write_block, src, pp, d, fs, wo)

# File data

# the regular file a path names (symbolic links followed as the options say)
def Ext2W.regular(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +path: B.Octets) -> Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
  do Result<&2, &2, E.Ext2Error, N.Ext2Inode>:
    +i : N.Ext2Inode <- X.Ext2.lookup(~Dv, ~block_size, ~read_block, d, fs, path)
    S.Ext2.require(Bool.not(N.Ext2Inode.is_dir(i)), E.Ext2IsDir{N.Ext2Inode.number_of(i)})
    S.Ext2.require(U32.is_eq(DW.Ext2DirW.code(N.Ext2Inode.kind(i)), 1), E.Ext2CannotWrite{"not a regular file"})
    return i

# a size the filesystem can hold: under 2 GiB without large_file
def Ext2W.size_ok(+fs: S.Ext2Fs, +end: Nat) -> Result<&2, &2, E.Ext2Error, Unit>:
  S.Ext2.require(Bool.or(Nat.is_lt(Nat.div(end, 65536n), 32768n), S.Ext2Super.has_ro_compat(S.Ext2Fs.sb(fs), 2)), E.Ext2CannotWrite{"a file of 2 GiB or more (large_file is off)"})

def Ext2W.written(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, B.Octets>, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  match out:
    case T.Ext2Out{d, raw}:
      IW.Ext2InodeW.write_raw(~Dv, ~block_size, ~read_block, ~write_block, d, fs, ino, IW.Ext2IRaw.touch(raw, WO.Ext2WriteOptions.time(wo)))

def Ext2W.write.at(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +i: N.Ext2Inode, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +off: Nat, +data: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  +ino = N.Ext2Inode.number_of(i)
  do Result<&2, &2, E.Ext2Error, Dv>:
    Ext2W.size_ok(fs, Nat.add(off, B.Octets.len(data)))
    raw : B.Octets <- IW.Ext2InodeW.read_raw(~Dv, ~block_size, ~read_block, d, fs, ino)
    out : T.Ext2Out<Dv, B.Octets> <- FW.Ext2FileW.write(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, raw, off, data)
    Ext2W.written(~Dv, ~block_size, ~read_block, ~write_block, out, fs, wo, ino)

# the bytes data written into the file at path from byte off (holes before
# it, if off is past the end; the file grows to cover the range)
def Ext2W.write(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +path: B.Octets, +off: Nat, +data: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    i : N.Ext2Inode <- Ext2W.regular(~Dv, ~block_size, ~read_block, d, fs, path)
    Ext2W.write.at(~Dv, ~block_size, ~read_block, ~write_block, i, d, fs, wo, off, data)

# the bytes data written at the end of the file at path
def Ext2W.append(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +path: B.Octets, +data: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    +i : N.Ext2Inode <- Ext2W.regular(~Dv, ~block_size, ~read_block, d, fs, path)
    Ext2W.write.at(~Dv, ~block_size, ~read_block, ~write_block, i, d, fs, wo, N.Ext2Inode.size_nat(i), data)

# the file at path cut or grown to size bytes
def Ext2W.truncate(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +path: B.Octets, +size: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    +i : N.Ext2Inode <- Ext2W.regular(~Dv, ~block_size, ~read_block, d, fs, path)
    +ino : Nat = N.Ext2Inode.number_of(i)
    Ext2W.size_ok(fs, size)
    raw : B.Octets <- IW.Ext2InodeW.read_raw(~Dv, ~block_size, ~read_block, d, fs, ino)
    out : T.Ext2Out<Dv, B.Octets> <- FW.Ext2FileW.truncate(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, raw, size)
    Ext2W.written(~Dv, ~block_size, ~read_block, ~write_block, out, fs, wo, ino)

# Operations as values

type Ext2Op is Data:
  Ext2OpCreate{path: B.Octets, mode: U32}
  Ext2OpMkdir{path: B.Octets, mode: U32}
  Ext2OpSymlink{path: B.Octets, target: B.Octets}
  Ext2OpLink{target: B.Octets, path: B.Octets}
  Ext2OpUnlink{path: B.Octets}
  Ext2OpRmdir{path: B.Octets}
  Ext2OpRename{from: B.Octets, to: B.Octets}
  Ext2OpWrite{path: B.Octets, off: Nat, data: B.Octets}
  Ext2OpAppend{path: B.Octets, data: B.Octets}
  Ext2OpTruncate{path: B.Octets, size: Nat}

def Ext2Op.apply.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, op: Ext2Op, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions) -> Result<&2, &2, E.Ext2Error, Dv>:
  match op:
    case Ext2OpCreate{p, m}:
      Ext2W.create(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, p, m)
    case Ext2OpMkdir{p, m}:
      Ext2W.mkdir(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, p, m)
    case Ext2OpSymlink{p, t}:
      Ext2W.symlink(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, p, t)
    case Ext2OpLink{t, p}:
      Ext2W.link(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, t, p)
    case Ext2OpUnlink{p}:
      Ext2W.unlink(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, p)
    case Ext2OpRmdir{p}:
      Ext2W.rmdir(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, p)
    case Ext2OpRename{a, b}:
      Ext2W.rename(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, a, b)
    case Ext2OpWrite{p, o, x}:
      Ext2W.write(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, p, o, x)
    case Ext2OpAppend{p, x}:
      Ext2W.append(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, p, x)
    case Ext2OpTruncate{p, n}:
      Ext2W.truncate(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, p, n)

# an operation done, unchecked: the writability check, then the work
def Ext2Op.apply(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, op: Ext2Op, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions) -> Result<&2, &2, E.Ext2Error, Dv>:
  do Result<&2, &2, E.Ext2Error, Dv>:
    Ext2W.writable(fs, wo)
    Ext2Op.apply.go(~Dv, ~block_size, ~read_block, ~write_block, op, d, fs, wo)
