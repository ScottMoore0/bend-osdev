# bend-osdev-ext2: checking a filesystem's consistency, as the writer's
# laws state it (a small fsck, written here from the layout documents; not
# e2fsck, which the tests run beside it):
#
#   counts  every group's bitmaps agree with its descriptor's free counts,
#           and the descriptors' sums with the superblock's
#   blocks  no block belongs to two owners (the metadata: superblock and
#           descriptor copies, bitmaps, inode tables; and every inode in
#           use: its data, indirect and extent blocks and its attribute
#           block, shared attribute blocks counted once); every inode's
#           i_blocks counts its blocks; and each group's block bitmap marks
#           exactly the blocks owned
#   links   the directory tree from the root: "." and ".." right, every
#           entry naming an inode in use whose type it records, every inode
#           in use reached, and each inode's link count the number of
#           directory entries naming it
#
# Each answers Done{Unit{}} or Ext2CheckFailed naming the first problem.
# Inode 7 (the resize inode, which maps the reserved descriptor blocks) is
# counted for its doubly indirect block only. Extent trees deeper than one
# level are not walked (Ext2ExtentFull).
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./field.bend as F
import ./super.bend as S
import ./group.bend as G
import ./inode.bend as N
import ./file.bend as FL
import ./dir.bend as DR
import ./blockmap.bend as M
import ./bitmap.bend as BM
import ./meta.bend as T
import ./alloc.bend as A
import ./inodew.bend as IW
import ./mapw.bend as MW
import ./extentw.bend as EW
import ./extent.bend as X
import ./dirw.bend as DW

def Ext2Fsck.fail(what: String) -> E.Ext2Error:
  E.Ext2CheckFailed{what}

# Counts

type Ext2Sums is Data:
  Ext2Sums{blocks: Nat, inodes: Nat}

def Ext2Fsck.group_counts(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +g: Nat) -> Result<&2, &2, E.Ext2Error, Ext2Sums>:
  do Result<&2, &2, E.Ext2Error, Ext2Sums>:
    +raw : B.Octets <- T.Ext2Meta.desc_read(~Dv, ~block_size, ~read_block, d, fs, g)
    +desc : G.Ext2Group = T.Ext2Meta.desc(fs, raw)
    bb : B.Octets <- T.Ext2Meta.block_bitmap(~Dv, ~block_size, ~read_block, d, fs, g, desc)
    ib : B.Octets <- T.Ext2Meta.inode_bitmap(~Dv, ~block_size, ~read_block, d, fs, desc)
    +fb : Nat = BM.Ext2Bitmap.count_clear(bb, T.Ext2Meta.group_blocks(fs, g))
    +fi : Nat = BM.Ext2Bitmap.count_clear(ib, S.Ext2Fs.inodes_per_group(fs))
    +db : Nat = U32.to_nat(G.Ext2Group.free_blocks(desc))
    +di : Nat = U32.to_nat(G.Ext2Group.free_inodes(desc))
    S.Ext2.require(Nat.is_eq(fb, db), Ext2Fsck.fail("group " ++ Nat.show(g) ++ ": " ++ Nat.show(fb) ++ " free blocks in its bitmap, " ++ Nat.show(db) ++ " in its descriptor"))
    S.Ext2.require(Nat.is_eq(fi, di), Ext2Fsck.fail("group " ++ Nat.show(g) ++ ": " ++ Nat.show(fi) ++ " free inodes in its bitmap, " ++ Nat.show(di) ++ " in its descriptor"))
    return Ext2Sums{fb, fi}

def Ext2Fsck.add(r: Result<&2, &2, E.Ext2Error, Ext2Sums>, s: Ext2Sums) -> Result<&2, &2, E.Ext2Error, Ext2Sums>:
  match r s:
    case Done{Ext2Sums{a, b}} Ext2Sums{c, e}:
      Done{Ext2Sums{Nat.add(a, c), Nat.add(b, e)}}
    case Fail{x} _:
      Fail{x}

def Ext2Fsck.counts.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, count: Nat, r: Result<&2, &2, E.Ext2Error, Ext2Sums>, +d: Dv, +fs: S.Ext2Fs, +g: Nat) -> Result<&2, &2, E.Ext2Error, Ext2Sums>:
  match count r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{s}:
      Done{s}
    case 1n+c Done{s}:
      Ext2Fsck.counts.go(~Dv, ~block_size, ~read_block, c, Ext2Fsck.add(Ext2Fsck.group_counts(~Dv, ~block_size, ~read_block, d, fs, g), s), d, fs, Nat.add(g, 1n))

def Ext2Fsck.counts.sb(+raw: B.Octets, s: Ext2Sums) -> Result<&2, &2, E.Ext2Error, Unit>:
  match s:
    case Ext2Sums{+b, +i}:
      +sb = T.Ext2Meta.sb_free_blocks(raw)
      +si = T.Ext2Meta.sb_free_inodes(raw)
      do Result<&2, &2, E.Ext2Error, Unit>:
        S.Ext2.require(Nat.is_eq(b, sb), Ext2Fsck.fail("the groups have " ++ Nat.show(b) ++ " free blocks, the superblock counts " ++ Nat.show(sb)))
        S.Ext2.require(Nat.is_eq(i, si), Ext2Fsck.fail("the groups have " ++ Nat.show(i) ++ " free inodes, the superblock counts " ++ Nat.show(si)))

# the bitmaps and the free counts agree: every group's, and their sums with
# the superblock's
def Ext2Fsck.counts(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs) -> Result<&2, &2, E.Ext2Error, Unit>:
  do Result<&2, &2, E.Ext2Error, Unit>:
    s : Ext2Sums <- Ext2Fsck.counts.go(~Dv, ~block_size, ~read_block, S.Ext2Fs.groups(fs), Done{Ext2Sums{0n, 0n}}, d, fs, 0n)
    raw : B.Octets <- S.Ext2Super.read(~Dv, ~block_size, ~read_block, d)
    Ext2Fsck.counts.sb(raw, s)

# Blocks: who owns what

# len blocks from start owned by owner (0: the filesystem's metadata)
type Ext2Run is Data:
  Ext2Run{start: Nat, len: Nat, owner: Nat}

def Ext2Run.le(a: Ext2Run, b: Ext2Run) -> Bool:
  match a b:
    case Ext2Run{x, l, o} Ext2Run{y, m, p}:
      Nat.is_le(x, y)

def Ext2Fsck.runs_of(xs: List<&2, Nat>, +owner: Nat, acc: List<&2, Ext2Run>) -> List<&2, Ext2Run>:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      Ext2Fsck.runs_of(t, owner, Con{Ext2Run{x, 1n, owner}, acc})

# group g's metadata runs (desc: its descriptor)
def Ext2Fsck.meta_runs(+fs: S.Ext2Fs, +g: Nat, +desc: G.Ext2Group, acc: List<&2, Ext2Run>) -> List<&2, Ext2Run>:
  +first = G.Ext2Group.first_block(fs, g)
  +lead = List.length(&2, Nat, T.Ext2Meta.super_bits(fs, g))
  Con{Ext2Run{first, lead, 0n}, Con{Ext2Run{G.Ext2Group.block_bitmap(desc), 1n, 0n}, Con{Ext2Run{G.Ext2Group.inode_bitmap(desc), 1n, 0n}, Con{Ext2Run{G.Ext2Group.inode_table(desc), T.Ext2Meta.itable_blocks(fs), 0n}, acc}}}}

# an extent tree's runs: its extents and its leaf blocks
def Ext2Fsck.extent_runs(es: List<&2, X.Ext2Extent>, +owner: Nat, acc: List<&2, Ext2Run>) -> List<&2, Ext2Run>:
  match es:
    case Nil{}:
      acc
    case Con{X.Ext2Extent{b, n, s, w}, t}:
      Ext2Fsck.extent_runs(t, owner, Con{Ext2Run{s, n, owner}, acc})

def Ext2Fsck.tree_runs(t: EW.Ext2ExtTree, +owner: Nat) -> List<&2, Ext2Run>:
  match t:
    case EW.Ext2ExtTree{es, ls}:
      Ext2Fsck.extent_runs(es, owner, Ext2Fsck.runs_of(ls, owner, Nil{}))

def Ext2Fsck.nonzero(xs: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case Con{+x, t}:
      Ext2Fsck.nonzero(t, MW.Ext2MapW.ptrs.keep(Nat.is_eq(x, 0n), U32.from_nat(x), acc))

def Ext2Fsck.slot(+ib: B.Octets, +k: Nat) -> List<&2, Nat>:
  Ext2Fsck.nonzero([M.Ext2Map.entry(ib, k)], Nil{})

def Ext2Fsck.direct.go(n: Nat, +ib: B.Octets, +k: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      acc
    case 1n+p:
      Ext2Fsck.direct.go(p, ib, Nat.add(k, 1n), Con{M.Ext2Map.entry(ib, k), acc})

# the twelve direct pointers of a block map
def Ext2Fsck.direct(+ib: B.Octets) -> List<&2, Nat>:
  Ext2Fsck.direct.go(12n, ib, 0n, Nil{})

# every block of a block map: the direct blocks and the trees under the
# three indirect slots
def Ext2Fsck.map_blocks(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +ib: B.Octets) -> Result<&2, &2, E.Ext2Error, List<&2, Nat>>:
  +direct = Ext2Fsck.nonzero(Ext2Fsck.direct(ib), Nil{})
  do Result<&2, &2, E.Ext2Error, List<&2, Nat>>:
    a : List<&2, Nat> <- MW.Ext2MapW.all(~Dv, ~block_size, ~read_block, 1n, Ext2Fsck.slot(ib, 12n), d, fs, ino, direct)
    b : List<&2, Nat> <- MW.Ext2MapW.all(~Dv, ~block_size, ~read_block, 2n, Ext2Fsck.slot(ib, 13n), d, fs, ino, a)
    MW.Ext2MapW.all(~Dv, ~block_size, ~read_block, 3n, Ext2Fsck.slot(ib, 14n), d, fs, ino, b)

# an inode's blocks: its runs, and how many blocks they hold
type Ext2Held is Data:
  Ext2Held{runs: List<&2, Ext2Run>, count: Nat}

def Ext2Fsck.total(rs: List<&2, Ext2Run>, n: Nat) -> Nat:
  match rs:
    case Nil{}:
      n
    case Con{Ext2Run{s, l, o}, t}:
      Ext2Fsck.total(t, Nat.add(n, l))

def Ext2Fsck.held(rs: List<&2, Ext2Run>) -> Ext2Held:
  match rs:
    case Nil{}:
      Ext2Held{Nil{}, 0n}
    case Con{h, t}:
      +all = {Con{h, t} : List<&2, Ext2Run>}
      Ext2Held{all, Ext2Fsck.total(all, 0n)}

def Ext2Fsck.map_held(r: Result<&2, &2, E.Ext2Error, List<&2, Nat>>, +owner: Nat) -> Result<&2, &2, E.Ext2Error, Ext2Held>:
  match r:
    case Done{xs}:
      Done{Ext2Fsck.held(Ext2Fsck.runs_of(xs, owner, Nil{}))}
    case Fail{e}:
      Fail{e}

def Ext2Fsck.tree_held(r: Result<&2, &2, E.Ext2Error, EW.Ext2ExtTree>, +owner: Nat) -> Result<&2, &2, E.Ext2Error, Ext2Held>:
  match r:
    case Done{t}:
      Done{Ext2Fsck.held(Ext2Fsck.tree_runs(t, owner))}
    case Fail{e}:
      Fail{e}

# 0 none, 1 the resize inode's doubly indirect block, 2 an extent tree, 3 a
# block map
def Ext2Fsck.held.mode(fast: Bool, resize: Bool, extents: Bool) -> Nat:
  match fast resize extents:
    case True{} _ _:
      0n
    case False{} True{} _:
      1n
    case False{} False{} True{}:
      2n
    case False{} False{} False{}:
      3n

def Ext2Fsck.held.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, mode: Nat, +d: Dv, +fs: S.Ext2Fs, +n: Nat, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, Ext2Held>:
  match mode:
    case 0n:
      Done{Ext2Held{Nil{}, 0n}}
    case 1n:
      Done{Ext2Fsck.held(Ext2Fsck.runs_of(Ext2Fsck.slot(IW.Ext2IRaw.iblock(raw), 13n), n, Nil{}))}
    case 2n:
      Ext2Fsck.tree_held(EW.Ext2ExtW.load(~Dv, ~block_size, ~read_block, d, fs, n, IW.Ext2IRaw.generation(raw), IW.Ext2IRaw.iblock(raw)), n)
    case _:
      Ext2Fsck.map_held(Ext2Fsck.map_blocks(~Dv, ~block_size, ~read_block, d, fs, n, IW.Ext2IRaw.iblock(raw)), n)

# the blocks inode n (record raw) maps
def Ext2Fsck.inode_held(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +n: Nat, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, Ext2Held>:
  +i = IW.Ext2IRaw.inode(fs, n, raw)
  +fast = Bool.and(N.Ext2Inode.is_symlink(i), FL.Ext2File.is_fast_symlink(fs, i))
  Ext2Fsck.held.go(~Dv, ~block_size, ~read_block, Ext2Fsck.held.mode(fast, Nat.is_eq(n, 7n), N.Ext2Inode.has_flag(i, N.Ext2Inode.flag_extents())), d, fs, n, raw)

# An inode in use, as the links check needs it
type Ext2Use is Data:
  Ext2Use{ino: Nat, links: U32, dir: Bool}

# what the inode scan gathers: the inodes' runs, their attribute blocks, and
# the inodes in use (last first)
type Ext2Owned is Data:
  Ext2Owned{runs: List<&2, Ext2Run>, acls: List<&2, Nat>, uses: List<&2, Ext2Use>}

def Ext2Fsck.acl_of(+a: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  MW.Ext2MapW.ptrs.keep(Nat.is_eq(a, 0n), U32.from_nat(a), acc)

def Ext2Fsck.flag(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def Ext2Fsck.one.fin(h: Ext2Held, +fs: S.Ext2Fs, +n: Nat, +raw: B.Octets, o: Ext2Owned) -> Result<&2, &2, E.Ext2Error, Ext2Owned>:
  match h o:
    case Ext2Held{rs, +c} Ext2Owned{runs, acls, uses}:
      +acl = IW.Ext2IRaw.file_acl(raw)
      +want = Nat.mul(Nat.add(c, Ext2Fsck.flag(Bool.not(Nat.is_eq(acl, 0n)))), IW.Ext2IRaw.units(fs, raw))
      +i = IW.Ext2IRaw.inode(fs, n, raw)
      do Result<&2, &2, E.Ext2Error, Ext2Owned>:
        S.Ext2.require(Bool.or(Nat.is_eq(n, 7n), Nat.is_eq(want, IW.Ext2IRaw.blocks(raw))), Ext2Fsck.fail("inode " ++ Nat.show(n) ++ ": i_blocks is " ++ Nat.show(IW.Ext2IRaw.blocks(raw)) ++ ", its blocks make " ++ Nat.show(want)))
        return Ext2Owned{List.append(&2, Ext2Run, rs, runs), Ext2Fsck.acl_of(acl, acls), Con{Ext2Use{n, IW.Ext2IRaw.links(raw), N.Ext2Inode.is_dir(i)}, uses}}

def Ext2Fsck.one.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, unused: Bool, +d: Dv, +fs: S.Ext2Fs, +n: Nat, +raw: B.Octets, o: Ext2Owned) -> Result<&2, &2, E.Ext2Error, Ext2Owned>:
  match unused:
    case True{}:
      Done{o}
    case False{}:
      do Result<&2, &2, E.Ext2Error, Ext2Owned>:
        S.Ext2.require(Bool.or(Nat.is_lt(n, S.Ext2Super.first_ino(S.Ext2Fs.sb(fs))), Bool.not(U32.is_eq(IW.Ext2IRaw.links(raw), 0))), Ext2Fsck.fail("inode " ++ Nat.show(n) ++ " is in use with no links"))
        h : Ext2Held <- Ext2Fsck.inode_held(~Dv, ~block_size, ~read_block, d, fs, n, raw)
        Ext2Fsck.one.fin(h, fs, n, raw, o)

# inode n, in use: its blocks and its links gathered (a reserved inode with
# mode 0 is not in use for this)
def Ext2Fsck.one(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +n: Nat, o: Ext2Owned) -> Result<&2, &2, E.Ext2Error, Ext2Owned>:
  do Result<&2, &2, E.Ext2Error, Ext2Owned>:
    +raw : B.Octets <- IW.Ext2InodeW.read_raw(~Dv, ~block_size, ~read_block, d, fs, n)
    Ext2Fsck.one.go(~Dv, ~block_size, ~read_block, Bool.and(Nat.is_lt(n, S.Ext2Super.first_ino(S.Ext2Fs.sb(fs))), U32.is_eq(IW.Ext2IRaw.mode(raw), 0)), d, fs, n, raw, o)

def Ext2Fsck.ones(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ks: List<&2, Nat>, r: Result<&2, &2, E.Ext2Error, Ext2Owned>, +d: Dv, +fs: S.Ext2Fs, +base: Nat) -> Result<&2, &2, E.Ext2Error, Ext2Owned>:
  match ks r:
    case _ Fail{e}:
      Fail{e}
    case Nil{} Done{o}:
      Done{o}
    case Con{k, t} Done{o}:
      Ext2Fsck.ones(~Dv, ~block_size, ~read_block, t, Ext2Fsck.one(~Dv, ~block_size, ~read_block, d, fs, Nat.add(Nat.add(base, k), 1n), o), d, fs, base)

# group g's inodes in use, and its metadata runs, gathered
def Ext2Fsck.group(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +g: Nat, o: Ext2Owned) -> Result<&2, &2, E.Ext2Error, Ext2Owned>:
  match o:
    case Ext2Owned{runs, acls, uses}:
      +ipg = S.Ext2Fs.inodes_per_group(fs)
      do Result<&2, &2, E.Ext2Error, Ext2Owned>:
        +raw : B.Octets <- T.Ext2Meta.desc_read(~Dv, ~block_size, ~read_block, d, fs, g)
        +desc : G.Ext2Group = T.Ext2Meta.desc(fs, raw)
        ib : B.Octets <- T.Ext2Meta.inode_bitmap(~Dv, ~block_size, ~read_block, d, fs, desc)
        Ext2Fsck.ones(~Dv, ~block_size, ~read_block, BM.Ext2Bitmap.set_bits(ib, ipg), Done{Ext2Owned{Ext2Fsck.meta_runs(fs, g, desc, runs), acls, uses}}, d, fs, Nat.mul(g, ipg))

def Ext2Fsck.groups(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, count: Nat, r: Result<&2, &2, E.Ext2Error, Ext2Owned>, +d: Dv, +fs: S.Ext2Fs, +g: Nat) -> Result<&2, &2, E.Ext2Error, Ext2Owned>:
  match count r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{o}:
      Done{o}
    case 1n+c Done{o}:
      Ext2Fsck.groups(~Dv, ~block_size, ~read_block, c, Ext2Fsck.group(~Dv, ~block_size, ~read_block, d, fs, g, o), d, fs, Nat.add(g, 1n))

def Ext2Fsck.unique.keep(same: Bool, x: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match same:
    case True{}:
      acc
    case False{}:
      Con{x, acc}

# Runs checked: inside the filesystem, none overlapping another

def Ext2Fsck.unique(xs: List<&2, Nat>, last: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      List.reverse(&2, Nat, acc)
    case Con{+x, t}:
      Ext2Fsck.unique(t, x, Ext2Fsck.unique.keep(Nat.is_eq(x, last), x, acc))

def Ext2Fsck.owner_name.pick(meta: Bool, +o: Nat) -> String:
  match meta:
    case True{}:
      "the filesystem"
    case False{}:
      "inode " ++ Nat.show(o)

def Ext2Fsck.owner_name(+o: Nat) -> String:
  Ext2Fsck.owner_name.pick(Nat.is_eq(o, 0n), o)

# sorted runs: each inside the filesystem and starting at or after the end
# of the one before (end: that end, prev: its owner)
def Ext2Fsck.disjoint(rs: List<&2, Ext2Run>, +fs: S.Ext2Fs, +end: Nat, +prev: Nat) -> Result<&2, &2, E.Ext2Error, Unit>:
  match rs:
    case Nil{}:
      Done{Unit{}}
    case Con{Ext2Run{+s, +l, +o}, t}:
      +e = Nat.add(s, l)
      do Result<&2, &2, E.Ext2Error, Unit>:
        S.Ext2.require(Bool.or(Nat.is_eq(l, 0n), Bool.and(Nat.is_le(T.Ext2Meta.first_data_block(fs), s), Nat.is_le(e, S.Ext2Fs.blocks(fs)))), Ext2Fsck.fail(Ext2Fsck.owner_name(o) ++ " owns block " ++ Nat.show(s) ++ ", outside the filesystem"))
        S.Ext2.require(Bool.or(Nat.is_eq(l, 0n), Nat.is_le(end, s)), Ext2Fsck.fail("block " ++ Nat.show(s) ++ " belongs to " ++ Ext2Fsck.owner_name(prev) ++ " and to " ++ Ext2Fsck.owner_name(o)))
        Ext2Fsck.disjoint(t, fs, Nat.max(end, e), o)

# Each group's block bitmap against the runs (sorted, disjoint)

def Ext2Fsck.bits_in(rs: List<&2, Ext2Run>, +base: Nat, +n: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match rs:
    case Nil{}:
      List.reverse(&2, Nat, acc)
    case Con{Ext2Run{+s, l, o}, t}:
      Ext2Fsck.bits_in(t, base, n, List.reverse.go(&2, Nat, T.Ext2Meta.in_group(s, Nat.add(s, l), base, n), acc))

def Ext2Fsck.bitmap_ok(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +g: Nat, +rs: List<&2, Ext2Run>) -> Result<&2, &2, E.Ext2Error, Unit>:
  +n = T.Ext2Meta.group_blocks(fs, g)
  +want = BM.Ext2Bitmap.update(B.Octets.zeros(S.Ext2Fs.block_size(fs)), Ext2Fsck.bits_in(rs, G.Ext2Group.first_block(fs, g), n, Nil{}), True{})
  do Result<&2, &2, E.Ext2Error, Unit>:
    +raw : B.Octets <- T.Ext2Meta.desc_read(~Dv, ~block_size, ~read_block, d, fs, g)
    bb : B.Octets <- T.Ext2Meta.block_bitmap(~Dv, ~block_size, ~read_block, d, fs, g, T.Ext2Meta.desc(fs, raw))
    S.Ext2.require(BM.Ext2Bitmap.same(want, bb, n), Ext2Fsck.fail("group " ++ Nat.show(g) ++ ": its block bitmap differs from the blocks in use"))

def Ext2Fsck.bitmaps(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, count: Nat, r: Result<&2, &2, E.Ext2Error, Unit>, +d: Dv, +fs: S.Ext2Fs, +g: Nat, +rs: List<&2, Ext2Run>) -> Result<&2, &2, E.Ext2Error, Unit>:
  match count r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{u}:
      Done{u}
    case 1n+c Done{u}:
      Ext2Fsck.bitmaps(~Dv, ~block_size, ~read_block, c, Ext2Fsck.bitmap_ok(~Dv, ~block_size, ~read_block, d, fs, g, rs), d, fs, Nat.add(g, 1n), rs)

# The directory tree and the link counts

type Ext2Visit is Data:
  Ext2Visit{dir: Nat, parent: Nat}

# the inode numbers the entries seen so far name, and the directories still
# to visit
type Ext2Walk is Data:
  Ext2Walk{refs: List<&2, Nat>, queue: List<&2, Ext2Visit>}

def Ext2Fsck.enqueue(isdir: Bool, +ino: Nat, +dir: Nat, q: List<&2, Ext2Visit>) -> List<&2, Ext2Visit>:
  match isdir:
    case True{}:
      Con{Ext2Visit{ino, dir}, q}
    case False{}:
      q

def Ext2Fsck.entry.fin(+ci: N.Ext2Inode, +fs: S.Ext2Fs, +dir: Nat, +e: DR.Ext2Dirent, w: Ext2Walk) -> Result<&2, &2, E.Ext2Error, Ext2Walk>:
  match w:
    case Ext2Walk{refs, q}:
      +ino = N.Ext2Inode.number_of(ci)
      +code = DW.Ext2DirW.ftype(fs, DW.Ext2DirW.code(N.Ext2Inode.kind(ci)))
      do Result<&2, &2, E.Ext2Error, Ext2Walk>:
        S.Ext2.require(U32.is_eq(DR.Ext2Dirent.file_type(e), code), Ext2Fsck.fail("directory " ++ Nat.show(dir) ++ ": the entry " ++ B.Octets.to_string(DR.Ext2Dirent.name(e)) ++ " records file type " ++ U32.show(DR.Ext2Dirent.file_type(e)) ++ ", its inode is of type " ++ U32.show(code)))
        return Ext2Walk{Con{ino, refs}, Ext2Fsck.enqueue(N.Ext2Inode.is_dir(ci), ino, dir, q)}

def Ext2Fsck.entries(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, es: List<&2, DR.Ext2Dirent>, r: Result<&2, &2, E.Ext2Error, Ext2Walk>, +d: Dv, +fs: S.Ext2Fs, +dir: Nat) -> Result<&2, &2, E.Ext2Error, Ext2Walk>:
  match es r:
    case _ Fail{x}:
      Fail{x}
    case Nil{} Done{w}:
      Done{w}
    case Con{+e, t} Done{w}:
      +r2 = Result.bind(&2, &2, E.Ext2Error, N.Ext2Inode, Ext2Walk, N.Ext2Inode.read(~Dv, ~block_size, ~read_block, d, fs, U32.to_nat(DR.Ext2Dirent.inode(e))), ci => Ext2Fsck.entry.fin(ci, fs, dir, e, w))
      Ext2Fsck.entries(~Dv, ~block_size, ~read_block, t, r2, d, fs, dir)

def Ext2Fsck.dot(+e: DR.Ext2Dirent, +name: String, +want: Nat, +dir: Nat) -> Result<&2, &2, E.Ext2Error, Unit>:
  S.Ext2.require(Bool.and(B.Octets.is_eq(DR.Ext2Dirent.name(e), B.Octets.of_string(name)), Nat.is_eq(U32.to_nat(DR.Ext2Dirent.inode(e)), want)), Ext2Fsck.fail("directory " ++ Nat.show(dir) ++ ": its " ++ name ++ " entry is not first or names the wrong inode"))

def Ext2Fsck.visit.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, es: List<&2, DR.Ext2Dirent>, +d: Dv, +fs: S.Ext2Fs, +dir: Nat, +parent: Nat, w: Ext2Walk) -> Result<&2, &2, E.Ext2Error, Ext2Walk>:
  match es w:
    case Con{+a, Con{+b, rest}} Ext2Walk{refs, q}:
      do Result<&2, &2, E.Ext2Error, Ext2Walk>:
        Ext2Fsck.dot(a, ".", dir, dir)
        Ext2Fsck.dot(b, "..", parent, dir)
        Ext2Fsck.entries(~Dv, ~block_size, ~read_block, rest, Done{Ext2Walk{Con{parent, Con{dir, refs}}, q}}, d, fs, dir)
    case _ _:
      Fail{Ext2Fsck.fail("directory " ++ Nat.show(dir) ++ " has no . and .. entries")}

def Ext2Fsck.visit(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, v: Ext2Visit, w: Ext2Walk) -> Result<&2, &2, E.Ext2Error, Ext2Walk>:
  match v:
    case Ext2Visit{+dir, +parent}:
      do Result<&2, &2, E.Ext2Error, Ext2Walk>:
        +i : N.Ext2Inode <- N.Ext2Inode.read(~Dv, ~block_size, ~read_block, d, fs, dir)
        es : List<&2, DR.Ext2Dirent> <- DR.Ext2Dir.entries(~Dv, ~block_size, ~read_block, d, fs, i)
        Ext2Fsck.visit.go(~Dv, ~block_size, ~read_block, es, d, fs, dir, parent, w)

# the inode numbers every entry of the tree names (each directory visited
# once from the entry naming it)
def Ext2Fsck.walk(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, fuel: Nat, r: Result<&2, &2, E.Ext2Error, Ext2Walk>, +d: Dv, +fs: S.Ext2Fs) -> Result<&2, &2, E.Ext2Error, List<&2, Nat>>:
  match fuel r:
    case _ Fail{e}:
      Fail{e}
    case _ Done{Ext2Walk{refs, Nil{}}}:
      Done{refs}
    case 0n Done{w}:
      Fail{Ext2Fsck.fail("more directories than inodes: a directory is named twice")}
    case 1n+f Done{Ext2Walk{refs, Con{v, q}}}:
      Ext2Fsck.walk(~Dv, ~block_size, ~read_block, f, Ext2Fsck.visit(~Dv, ~block_size, ~read_block, d, fs, v, Ext2Walk{refs, q}), d, fs)

type Ext2Count is Data:
  Ext2Count{count: Nat, rest: List<&2, Nat>}

def Ext2Fsck.head_is(xs: List<&2, Nat>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      Nat.is_eq(x, n)

# how many of the leading xs are n, and the rest
def Ext2Fsck.count_eq(xs: List<&2, Nat>, hit: Bool, +n: Nat, c: Nat) -> Ext2Count:
  match xs hit:
    case Con{x, +t} True{}:
      Ext2Fsck.count_eq(t, Ext2Fsck.head_is(t, n), n, Nat.add(c, 1n))
    case _ _:
      Ext2Count{c, xs}

def Ext2Fsck.links.check(cnt: Ext2Count, +u: Ext2Use, us: List<&2, Ext2Use>, +first: Nat) -> Result<&2, &2, E.Ext2Error, Ext2Lists2>:
  match cnt u:
    case Ext2Count{+c, rest} Ext2Use{+n, +l, dir}:
      do Result<&2, &2, E.Ext2Error, Ext2Lists2>:
        S.Ext2.require(Bool.or(Bool.and(Nat.is_lt(n, first), Bool.not(Nat.is_eq(n, 2n))), Nat.is_eq(c, U32.to_nat(l))), Ext2Fsck.fail("inode " ++ Nat.show(n) ++ " has " ++ U32.show(l) ++ " links, and " ++ Nat.show(c) ++ " directory entries name it"))
        return Ext2Lists2{us, rest}

# what is left to compare: the inodes in use and the references
type Ext2Lists2 is Data:
  Ext2Lists2{uses: List<&2, Ext2Use>, refs: List<&2, Nat>}

def Ext2Fsck.ino_of(u: Ext2Use) -> Nat:
  match u:
    case Ext2Use{n, l, d}:
      n

def Ext2Fsck.below(xs: List<&2, Nat>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      Nat.is_lt(x, n)

def Ext2Fsck.first_ref(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      x

def Ext2Fsck.links.step(below: Bool, +refs: List<&2, Nat>, +u: Ext2Use, ut: List<&2, Ext2Use>, +first: Nat) -> Result<&2, &2, E.Ext2Error, Ext2Lists2>:
  match below:
    case True{}:
      Fail{Ext2Fsck.fail("an entry names inode " ++ Nat.show(Ext2Fsck.first_ref(refs)) ++ ", which is not in use")}
    case False{}:
      +n = Ext2Fsck.ino_of(u)
      Ext2Fsck.links.check(Ext2Fsck.count_eq(refs, Ext2Fsck.head_is(refs, n), n, 0n), u, ut, first)

# the inodes in use (ascending) against the references (ascending): each
# inode named as often as its link count says, and nothing else named
def Ext2Fsck.links(fuel: Nat, r: Result<&2, &2, E.Ext2Error, Ext2Lists2>, +first: Nat) -> Result<&2, &2, E.Ext2Error, Unit>:
  match fuel r:
    case _ Fail{e}:
      Fail{e}
    case _ Done{Ext2Lists2{Nil{}, Nil{}}}:
      Done{Unit{}}
    case _ Done{Ext2Lists2{Nil{}, Con{x, t}}}:
      Fail{Ext2Fsck.fail("an entry names inode " ++ Nat.show(x) ++ ", which is not in use")}
    case 0n Done{v}:
      Fail{Ext2Fsck.fail("comparing the link counts: out of steps")}
    case 1n+f Done{Ext2Lists2{Con{+u, ut}, +refs}}:
      +n = Ext2Fsck.ino_of(u)
      Ext2Fsck.links(f, Ext2Fsck.links.step(Ext2Fsck.below(refs, n), refs, u, ut, first), first)

def Ext2Fsck.full.check(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, o: Ext2Owned, +d: Dv, +fs: S.Ext2Fs) -> Result<&2, &2, E.Ext2Error, Unit>:
  match o:
    case Ext2Owned{runs, acls, uses}:
      +all = List.sort(~Ext2Run, ~Ext2Run.le, List.append(&2, Ext2Run, runs, Ext2Fsck.runs_of(Ext2Fsck.unique(A.Ext2Sort.nats(acls), 0n, Nil{}), 0n, Nil{})))
      +us = List.reverse(&2, Ext2Use, uses)
      do Result<&2, &2, E.Ext2Error, Unit>:
        Ext2Fsck.disjoint(all, fs, 0n, 0n)
        Ext2Fsck.bitmaps(~Dv, ~block_size, ~read_block, S.Ext2Fs.groups(fs), Done{Unit{}}, d, fs, 0n, all)
        refs : List<&2, Nat> <- Ext2Fsck.walk(~Dv, ~block_size, ~read_block, Nat.add(S.Ext2Fs.inodes_count(fs), 1n), Done{Ext2Walk{Nil{}, [Ext2Visit{2n, 2n}]}}, d, fs)
        Ext2Fsck.links(Nat.add(List.length(&2, Ext2Use, us), 1n), Done{Ext2Lists2{us, A.Ext2Sort.nats(refs)}}, S.Ext2Super.first_ino(S.Ext2Fs.sb(fs)))

# the whole filesystem checked: counts, blocks and links (see the top)
def Ext2Fsck.full(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs) -> Result<&2, &2, E.Ext2Error, Unit>:
  do Result<&2, &2, E.Ext2Error, Unit>:
    Ext2Fsck.counts(~Dv, ~block_size, ~read_block, d, fs)
    o : Ext2Owned <- Ext2Fsck.groups(~Dv, ~block_size, ~read_block, S.Ext2Fs.groups(fs), Done{Ext2Owned{Nil{}, Nil{}, Nil{}}}, d, fs, 0n)
    Ext2Fsck.full.check(~Dv, ~block_size, ~read_block, o, d, fs)

def Ext2Sums.blocks(s: Ext2Sums) -> Nat:
  match s:
    case Ext2Sums{b, i}:
      b

def Ext2Sums.inodes(s: Ext2Sums) -> Nat:
  match s:
    case Ext2Sums{b, i}:
      i
