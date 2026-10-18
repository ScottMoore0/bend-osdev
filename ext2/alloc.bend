# bend-osdev-ext2: allocating and freeing inodes and blocks through the
# bitmaps, with the group descriptors' free counts (and used_dirs,
# itable_unused, the uninit flags) and the superblock's free counts kept in
# step with every bit set or cleared. Where new inodes and blocks go is the
# write options' allocation policy (wopts.bend).
#
# An allocation reads a group's descriptor and bitmap, sets the bits it
# takes, and writes the bitmap, the descriptor and the superblock; a group
# whose bitmap was never initialised (BLOCK_UNINIT, INODE_UNINIT) is
# initialised first (meta.bend). Nothing is taken that a bitmap marks used,
# and nothing is freed that it marks free (Ext2CheckFailed).
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./super.bend as S
import ./group.bend as G
import ./inode.bend as N
import ./bitmap.bend as M
import ./meta.bend as T
import ./wopts.bend as WO

# Sorting block numbers (a bottom-up merge sort; tail calls throughout)

# whether the first of xs is at most the first of ys
def Ext2Sort.le(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      Nat.is_le(x, y)
    case _ _:
      True{}

# xs and ys (each ascending) merged onto acc (reversed); le compares heads
def Ext2Sort.merge(fuel: Nat, le: Bool, xs: List<&2, Nat>, ys: List<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match fuel le xs ys:
    case 0n _ _ _:
      List.reverse.go(&2, Nat, acc, List.append(&2, Nat, xs, ys))
    case 1n+f _ Nil{} _:
      List.reverse.go(&2, Nat, acc, ys)
    case 1n+f _ Con{x, xt} Nil{}:
      List.reverse.go(&2, Nat, acc, Con{x, xt})
    case 1n+f True{} Con{x, +xt} Con{+y, +yt}:
      Ext2Sort.merge(f, Ext2Sort.le(xt, Con{y, yt}), xt, Con{y, yt}, Con{x, acc})
    case 1n+f False{} Con{+x, +xt} Con{y, +yt}:
      Ext2Sort.merge(f, Ext2Sort.le(Con{x, xt}, yt), Con{x, xt}, yt, Con{y, acc})

def Ext2Sort.merge2(+xs: List<&2, Nat>, +ys: List<&2, Nat>) -> List<&2, Nat>:
  Ext2Sort.merge(Nat.add(List.length(&2, Nat, xs), List.length(&2, Nat, ys)), Ext2Sort.le(xs, ys), xs, ys, Nil{})

# one pass: neighbouring runs merged
def Ext2Sort.pass(rs: List<&2, List<&2, Nat>>, acc: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match rs:
    case Nil{}:
      List.reverse(&2, List<&2, Nat>, acc)
    case Con{a, Nil{}}:
      List.reverse(&2, List<&2, Nat>, Con{a, acc})
    case Con{a, Con{b, t}}:
      Ext2Sort.pass(t, Con{Ext2Sort.merge2(a, b), acc})

def Ext2Sort.passes(fuel: Nat, rs: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match fuel rs:
    case _ Nil{}:
      Nil{}
    case _ Con{a, Nil{}}:
      a
    case 0n Con{a, t}:
      List.append(&2, Nat, a, List.concat(&2, Nat, t))
    case 1n+f Con{a, t}:
      Ext2Sort.passes(f, Ext2Sort.pass(Con{a, t}, Nil{}))

def Ext2Sort.singles(xs: List<&2, Nat>, acc: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match xs:
    case Nil{}:
      List.reverse(&2, List<&2, Nat>, acc)
    case Con{x, t}:
      Ext2Sort.singles(t, Con{[x], acc})

# xs in ascending order
def Ext2Sort.nats(+xs: List<&2, Nat>) -> List<&2, Nat>:
  Ext2Sort.passes(List.length(&2, Nat, xs), Ext2Sort.singles(xs, Nil{}))

# Reading a group's descriptor

def Ext2Alloc.free_inodes_of(r: Result<&2, &2, E.Ext2Error, B.Octets>, +fs: S.Ext2Fs) -> Result<&2, &2, E.Ext2Error, Nat>:
  match r:
    case Done{raw}:
      Done{U32.to_nat(G.Ext2Group.free_inodes(T.Ext2Meta.desc(fs, raw)))}
    case Fail{e}:
      Fail{e}

def Ext2Alloc.group_free_inodes(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +g: Nat) -> Result<&2, &2, E.Ext2Error, Nat>:
  Ext2Alloc.free_inodes_of(T.Ext2Meta.desc_read(~Dv, ~block_size, ~read_block, d, fs, g), fs)

# Choosing a group for an inode

def Ext2Alloc.positive(r: Result<&2, &2, E.Ext2Error, Nat>) -> Result<&2, &2, E.Ext2Error, Bool>:
  match r:
    case Done{n}:
      Done{Nat.is_lt(0n, n)}
    case Fail{e}:
      Fail{e}

# the first group, from start on (wrapping round), with a free inode; r says
# whether the group looked at last (start + i - 1) had one
def Ext2Alloc.near.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, count: Nat, r: Result<&2, &2, E.Ext2Error, Bool>, +d: Dv, +fs: S.Ext2Fs, +start: Nat, +i: Nat) -> Result<&2, &2, E.Ext2Error, Nat>:
  match count r:
    case _ Fail{e}:
      Fail{e}
    case _ Done{True{}}:
      Done{Nat.mod(Nat.sub(Nat.add(start, i), 1n), S.Ext2Fs.groups(fs))}
    case 0n Done{False{}}:
      Fail{E.Ext2NoInodes{}}
    case 1n+c Done{False{}}:
      Ext2Alloc.near.go(~Dv, ~block_size, ~read_block, c, Ext2Alloc.positive(Ext2Alloc.group_free_inodes(~Dv, ~block_size, ~read_block, d, fs, Nat.mod(Nat.add(start, i), S.Ext2Fs.groups(fs)))), d, fs, start, Nat.add(i, 1n))

type Ext2Best is Data:
  Ext2Best{group: Nat, free: Nat}

def Ext2Best.free(b: Ext2Best) -> Nat:
  match b:
    case Ext2Best{g, f}:
      f

def Ext2Alloc.better.pick(more: Bool, b: Ext2Best, +g: Nat, +f: Nat) -> Ext2Best:
  match more:
    case True{}:
      Ext2Best{g, f}
    case False{}:
      b

def Ext2Alloc.better(+b: Ext2Best, +g: Nat, r: Result<&2, &2, E.Ext2Error, Nat>) -> Result<&2, &2, E.Ext2Error, Ext2Best>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+f}:
      Done{Ext2Alloc.better.pick(Nat.is_lt(Ext2Best.free(b), f), b, g, f)}

def Ext2Alloc.spread.fin(any: Bool, g: Nat) -> Result<&2, &2, E.Ext2Error, Nat>:
  match any:
    case True{}:
      Done{g}
    case False{}:
      Fail{E.Ext2NoInodes{}}

# the group with the most free inodes (the lowest among equals)
def Ext2Alloc.spread.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, count: Nat, r: Result<&2, &2, E.Ext2Error, Ext2Best>, +d: Dv, +fs: S.Ext2Fs, +g: Nat) -> Result<&2, &2, E.Ext2Error, Nat>:
  match count r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{Ext2Best{bg, bf}}:
      Ext2Alloc.spread.fin(Nat.is_lt(0n, bf), bg)
    case 1n+c Done{+b}:
      Ext2Alloc.spread.go(~Dv, ~block_size, ~read_block, c, Ext2Alloc.better(b, g, Ext2Alloc.group_free_inodes(~Dv, ~block_size, ~read_block, d, fs, g)), d, fs, Nat.add(g, 1n))


def Ext2Alloc.pick_group(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, pick: WO.Ext2GroupPick, +d: Dv, +fs: S.Ext2Fs, +start: Nat) -> Result<&2, &2, E.Ext2Error, Nat>:
  match pick:
    case WO.Ext2PickFirst{}:
      Ext2Alloc.near.go(~Dv, ~block_size, ~read_block, S.Ext2Fs.groups(fs), Done{False{}}, d, fs, 0n, 0n)
    case WO.Ext2PickNear{}:
      Ext2Alloc.near.go(~Dv, ~block_size, ~read_block, S.Ext2Fs.groups(fs), Done{False{}}, d, fs, start, 0n)
    case WO.Ext2PickSpread{}:
      Ext2Alloc.spread.go(~Dv, ~block_size, ~read_block, S.Ext2Fs.groups(fs), Done{Ext2Best{0n, 0n}}, d, fs, 0n)

def Ext2Alloc.first(xs: List<&2, Nat>, why: String) -> Result<&2, &2, E.Ext2Error, Nat>:
  match xs:
    case Con{x, t}:
      Done{x}
    case Nil{}:
      Fail{E.Ext2CheckFailed{why}}

def Ext2Alloc.u32_bit(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

# with the uninit features, bg_itable_unused covers at most the inodes after
# index idx
def Ext2Alloc.itable_unused.pick(on: Bool, +fs: S.Ext2Fs, +raw: B.Octets, +idx: Nat, +unused: U32) -> B.Octets:
  match on:
    case True{}:
      T.Ext2Meta.set_itable_unused(fs, raw, U32.min(unused, U32.from_nat(Nat.sub(Nat.sub(S.Ext2Fs.inodes_per_group(fs), idx), 1n))))
    case False{}:
      raw

def Ext2Alloc.inode_fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, B.Octets>, +fs: S.Ext2Fs, +g: Nat, +idx: Nat, +dir: Bool, +desc: G.Ext2Group) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
  match out:
    case T.Ext2Out{d2, +raw2}:
      +free = G.Ext2Group.free_inodes(desc)
      +raw3 = T.Ext2Meta.set_used_dirs(fs, T.Ext2Meta.set_free_inodes(fs, raw2, U32.sub(free, 1)), U32.add(G.Ext2Group.used_dirs(desc), Ext2Alloc.u32_bit(dir)))
      +raw4 = Ext2Alloc.itable_unused.pick(T.Ext2Meta.has_uninit(fs), fs, raw3, idx, G.Ext2Group.itable_unused(desc))
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
        S.Ext2.require(U32.is_lt(0, free), E.Ext2CheckFailed{"a group descriptor counts no free inode where its bitmap has one"})
        d3 : Dv <- T.Ext2Meta.desc_write(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, g, raw4)
        d4 : Dv <- T.Ext2Meta.adjust_super(~Dv, ~block_size, ~read_block, ~write_block, d3, 0n, 0n, 0n, 1n)
        return T.Ext2Out{d4, N.Ext2Inode.number(S.Ext2Fs.inodes_per_group(fs), N.Ext2InodeLoc{g, idx})}

# a free inode of group g taken: its number (the lowest free one at or after
# the first non-reserved inode)
def Ext2Alloc.inode_in(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +g: Nat, +dir: Bool) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
  +ipg = S.Ext2Fs.inodes_per_group(fs)
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
    +raw : B.Octets <- T.Ext2Meta.desc_read(~Dv, ~block_size, ~read_block, d, fs, g)
    +desc : G.Ext2Group = T.Ext2Meta.desc(fs, raw)
    +bm : B.Octets <- T.Ext2Meta.inode_bitmap(~Dv, ~block_size, ~read_block, d, fs, desc)
    +from : Nat = Nat.sub(Nat.sub(S.Ext2Super.first_ino(S.Ext2Fs.sb(fs)), 1n), Nat.mul(g, ipg))
    +idx : Nat <- Ext2Alloc.first(M.Ext2Bitmap.find(bm, from, ipg, 1n), "a group with free inodes has none in its bitmap")
    out : T.Ext2Out<Dv, B.Octets> <- T.Ext2Meta.put_inode_bitmap(~Dv, ~block_size, ~read_block, ~write_block, d, fs, raw, M.Ext2Bitmap.set(bm, idx))
    Ext2Alloc.inode_fin(~Dv, ~block_size, ~read_block, ~write_block, out, fs, g, idx, dir, desc)

def Ext2Alloc.policy_pick(dir: Bool, +p: WO.Ext2AllocPolicy) -> WO.Ext2GroupPick:
  match dir:
    case True{}:
      WO.Ext2AllocPolicy.dirs(p)
    case False{}:
      WO.Ext2AllocPolicy.files(p)

# a new inode (a directory's if dir), placed by the options' policy relative
# to the parent directory's inode: its number, and the device
def Ext2Alloc.inode(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +parent: Nat, +dir: Bool) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
  +start = N.Ext2InodeLoc.group(N.Ext2Inode.locate(S.Ext2Fs.inodes_per_group(fs), parent))
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
    +g : Nat <- Ext2Alloc.pick_group(~Dv, ~block_size, ~read_block, Ext2Alloc.policy_pick(dir, WO.Ext2WriteOptions.alloc(wo)), d, fs, start)
    Ext2Alloc.inode_in(~Dv, ~block_size, ~read_block, ~write_block, d, fs, g, dir)

# Blocks

# the blocks taken so far (last first) and how many are still wanted
type Ext2Taken is Data:
  Ext2Taken{blocks: List<&2, Nat>, want: Nat}

def Ext2Alloc.absolute(ks: List<&2, Nat>, +base: Nat, acc: List<&2, Nat>) -> List<&2, Nat>:
  match ks:
    case Nil{}:
      acc
    case Con{k, t}:
      Ext2Alloc.absolute(t, base, Con{Nat.add(base, k), acc})

def Ext2Alloc.take.fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, B.Octets>, +fs: S.Ext2Fs, +g: Nat, +free: U32, +ks: List<&2, Nat>, got: List<&2, Nat>, +want: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Taken>>:
  match out:
    case T.Ext2Out{d2, +raw2}:
      +n = List.length(&2, Nat, ks)
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Taken>>:
        d3 : Dv <- T.Ext2Meta.desc_write(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, g, T.Ext2Meta.set_free_blocks(fs, raw2, U32.sub(free, U32.from_nat(n))))
        return T.Ext2Out{d3, Ext2Taken{Ext2Alloc.absolute(ks, G.Ext2Group.first_block(fs, g), got), Nat.sub(want, n)}}

def Ext2Alloc.take.found(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +g: Nat, +raw: B.Octets, +free: U32, +bm: B.Octets, ks: List<&2, Nat>, got: List<&2, Nat>, +want: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Taken>>:
  match ks:
    case Nil{}:
      Done{T.Ext2Out{d, Ext2Taken{got, want}}}
    case Con{+k, +t}:
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Taken>>:
        out : T.Ext2Out<Dv, B.Octets> <- T.Ext2Meta.put_block_bitmap(~Dv, ~block_size, ~read_block, ~write_block, d, fs, raw, M.Ext2Bitmap.update(bm, Con{k, t}, True{}))
        Ext2Alloc.take.fin(~Dv, ~block_size, ~read_block, ~write_block, out, fs, g, free, Con{k, t}, got, want)

def Ext2Alloc.take.read(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +g: Nat, +lo: Nat, +hi: Nat, got: List<&2, Nat>, +want: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Taken>>:
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Taken>>:
    +raw : B.Octets <- T.Ext2Meta.desc_read(~Dv, ~block_size, ~read_block, d, fs, g)
    +desc : G.Ext2Group = T.Ext2Meta.desc(fs, raw)
    +free : U32 = G.Ext2Group.free_blocks(desc)
    +bm : B.Octets <- T.Ext2Meta.block_bitmap(~Dv, ~block_size, ~read_block, d, fs, g, desc)
    Ext2Alloc.take.found(~Dv, ~block_size, ~read_block, ~write_block, d, fs, g, raw, free, bm, M.Ext2Bitmap.find(bm, lo, hi, Nat.min(want, U32.to_nat(free))), got, want)

def Ext2Alloc.take.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, more: Bool, +d: Dv, +fs: S.Ext2Fs, +g: Nat, +lo: Nat, +hi: Nat, got: List<&2, Nat>, +want: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Taken>>:
  match more:
    case True{}:
      Ext2Alloc.take.read(~Dv, ~block_size, ~read_block, ~write_block, d, fs, g, lo, hi, got, want)
    case False{}:
      Done{T.Ext2Out{d, Ext2Taken{got, want}}}

# free blocks of group g between bits lo and hi taken, up to what is wanted
def Ext2Alloc.take(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, Ext2Taken>, +fs: S.Ext2Fs, +g: Nat, +lo: Nat, +hi: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Taken>>:
  match out:
    case T.Ext2Out{+d, Ext2Taken{got, +want}}:
      Ext2Alloc.take.go(~Dv, ~block_size, ~read_block, ~write_block, Bool.and(Nat.is_lt(0n, want), Nat.is_lt(lo, hi)), d, fs, g, lo, hi, got, want)

def Ext2Alloc.seg_lo(first: Bool, +off: Nat) -> Nat:
  match first:
    case True{}:
      off
    case False{}:
      0n

def Ext2Alloc.seg_hi(last: Bool, +off: Nat, +n: Nat) -> Nat:
  match last:
    case True{}:
      off
    case False{}:
      n

# The groups an allocation visits: the goal group from the goal on, every
# other group after it (wrapping round), then the goal group below the goal.
# Step i of n + 1 (n groups); r holds the device and what was taken.
def Ext2Alloc.blocks.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, count: Nat, r: Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Taken>>, +fs: S.Ext2Fs, +g0: Nat, +off: Nat, +i: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Taken>>:
  match count r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{out}:
      Done{out}
    case 1n+c Done{out}:
      +n = S.Ext2Fs.groups(fs)
      +g = Nat.mod(Nat.add(g0, i), n)
      +first = Nat.is_eq(i, 0n)
      +last = Nat.is_eq(i, n)
      +lo = Ext2Alloc.seg_lo(first, off)
      +hi = Ext2Alloc.seg_hi(last, off, T.Ext2Meta.group_blocks(fs, g))
      Ext2Alloc.blocks.go(~Dv, ~block_size, ~read_block, ~write_block, c, Ext2Alloc.take(~Dv, ~block_size, ~read_block, ~write_block, out, fs, g, lo, hi), fs, g0, off, Nat.add(i, 1n))

def Ext2Alloc.blocks.fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, Ext2Taken>, +count: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
  match out:
    case T.Ext2Out{d, Ext2Taken{got, want}}:
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
        S.Ext2.require(Nat.is_eq(want, 0n), E.Ext2NoSpace{})
        d2 : Dv <- T.Ext2Meta.adjust_super(~Dv, ~block_size, ~read_block, ~write_block, d, 0n, count, 0n, 0n)
        return T.Ext2Out{d2, List.reverse(&2, Nat, got)}

def Ext2Alloc.goal_inside(+fs: S.Ext2Fs, +goal: Nat) -> Bool:
  Bool.and(Nat.is_le(T.Ext2Meta.first_data_block(fs), goal), Nat.is_lt(goal, S.Ext2Fs.blocks(fs)))

# the group a search starts in, and the bit it starts from
def Ext2Alloc.goal_group(pick: WO.Ext2BlockPick, +fs: S.Ext2Fs, +goal: Nat) -> Nat:
  match pick:
    case WO.Ext2BlockFirst{}:
      0n
    case WO.Ext2BlockNear{}:
      Nat.mul(U32.to_nat(Bool.to_u32(Ext2Alloc.goal_inside(fs, goal))), T.Ext2Meta.group_of(fs, goal))

def Ext2Alloc.goal_off(pick: WO.Ext2BlockPick, +fs: S.Ext2Fs, +goal: Nat) -> Nat:
  match pick:
    case WO.Ext2BlockFirst{}:
      0n
    case WO.Ext2BlockNear{}:
      Nat.mul(U32.to_nat(Bool.to_u32(Ext2Alloc.goal_inside(fs, goal))), Nat.sub(goal, G.Ext2Group.first_block(fs, T.Ext2Meta.group_of(fs, goal))))

def Ext2Alloc.blocks.some(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, none: Bool, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +goal: Nat, +count: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
  match none:
    case True{}:
      Done{T.Ext2Out{d, Nil{}}}
    case False{}:
      +pick = WO.Ext2AllocPolicy.blocks(WO.Ext2WriteOptions.alloc(wo))
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
        out : T.Ext2Out<Dv, Ext2Taken> <- Ext2Alloc.blocks.go(~Dv, ~block_size, ~read_block, ~write_block, Nat.add(S.Ext2Fs.groups(fs), 1n), Done{T.Ext2Out{d, Ext2Taken{Nil{}, count}}}, fs, Ext2Alloc.goal_group(pick, fs, goal), Ext2Alloc.goal_off(pick, fs, goal), 0n)
        Ext2Alloc.blocks.fin(~Dv, ~block_size, ~read_block, ~write_block, out, count)

# count free blocks taken, placed by the options' policy from the goal block:
# the blocks (in the order taken: ascending within each group visited) and
# the device; Ext2NoSpace if there are not that many
def Ext2Alloc.blocks(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +goal: Nat, +count: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
  Ext2Alloc.blocks.some(~Dv, ~block_size, ~read_block, ~write_block, Nat.is_eq(count, 0n), d, fs, wo, goal, count)

# Freeing blocks

type Ext2Lists is Data:
  Ext2Lists{a: List<&2, Nat>, b: List<&2, Nat>}

def Ext2Alloc.in_g(xs: List<&2, Nat>, +fs: S.Ext2Fs, +g: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      Nat.is_eq(T.Ext2Meta.group_of(fs, x), g)

# the leading blocks of xs in group g (relative to the group's first block),
# and the rest
def Ext2Alloc.split_group(xs: List<&2, Nat>, same: Bool, +fs: S.Ext2Fs, +g: Nat, acc: List<&2, Nat>) -> Ext2Lists:
  match xs same:
    case Con{+x, +t} True{}:
      Ext2Alloc.split_group(t, Ext2Alloc.in_g(t, fs, g), fs, g, Con{Nat.sub(x, G.Ext2Group.first_block(fs, g)), acc})
    case _ _:
      Ext2Lists{List.reverse(&2, Nat, acc), xs}

def Ext2Alloc.split(+xs: List<&2, Nat>, +fs: S.Ext2Fs) -> Ext2Lists:
  match xs:
    case Nil{}:
      Ext2Lists{Nil{}, Nil{}}
    case Con{+x, t}:
      Ext2Alloc.split_group(xs, True{}, fs, T.Ext2Meta.group_of(fs, x), Nil{})

def Ext2Alloc.free.fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, B.Octets>, +fs: S.Ext2Fs, +g: Nat, +free: U32, +k: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  match out:
    case T.Ext2Out{d2, +raw2}:
      T.Ext2Meta.desc_write(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, g, T.Ext2Meta.set_free_blocks(fs, raw2, U32.add(free, U32.from_nat(k))))

# the blocks ks of group g (bits of the group) freed
def Ext2Alloc.free.group(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +g: Nat, +ks: List<&2, Nat>) -> Result<&2, &2, E.Ext2Error, Dv>:
  +n = T.Ext2Meta.group_blocks(fs, g)
  do Result<&2, &2, E.Ext2Error, Dv>:
    +raw : B.Octets <- T.Ext2Meta.desc_read(~Dv, ~block_size, ~read_block, d, fs, g)
    +desc : G.Ext2Group = T.Ext2Meta.desc(fs, raw)
    +bm : B.Octets <- T.Ext2Meta.block_bitmap(~Dv, ~block_size, ~read_block, d, fs, g, desc)
    +bm2 : B.Octets = M.Ext2Bitmap.update(bm, ks, False{})
    +k : Nat = List.length(&2, Nat, ks)
    S.Ext2.require(Nat.is_eq(M.Ext2Bitmap.count_clear(bm2, n), Nat.add(M.Ext2Bitmap.count_clear(bm, n), k)), E.Ext2CheckFailed{"freeing a block that is not in use"})
    out : T.Ext2Out<Dv, B.Octets> <- T.Ext2Meta.put_block_bitmap(~Dv, ~block_size, ~read_block, ~write_block, d, fs, raw, bm2)
    Ext2Alloc.free.fin(~Dv, ~block_size, ~read_block, ~write_block, out, fs, g, G.Ext2Group.free_blocks(desc), k)

def Ext2Alloc.head_group(xs: List<&2, Nat>, +fs: S.Ext2Fs) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+x, t}:
      T.Ext2Meta.group_of(fs, x)

def Ext2Alloc.free.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, fuel: Nat, r: Result<&2, &2, E.Ext2Error, Dv>, parts: Ext2Lists, +fs: S.Ext2Fs, +g: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  match fuel r parts:
    case _ Fail{e} _:
      Fail{e}
    case _ Done{d} Ext2Lists{Nil{}, rest}:
      Done{d}
    case 0n Done{d} _:
      Fail{E.Ext2CheckFailed{"freeing blocks: out of steps"}}
    case 1n+f Done{+d} Ext2Lists{Con{k, kt}, +rest}:
      Ext2Alloc.free.go(~Dv, ~block_size, ~read_block, ~write_block, f, Ext2Alloc.free.group(~Dv, ~block_size, ~read_block, ~write_block, d, fs, g, Con{k, kt}), Ext2Alloc.split(rest, fs), fs, Ext2Alloc.head_group(rest, fs))

def Ext2Alloc.all_inside(xs: List<&2, Nat>, +fs: S.Ext2Fs) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(Ext2Alloc.goal_inside(fs, x), Ext2Alloc.all_inside(t, fs))

def Ext2Alloc.free_blocks.some(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, none: Bool, +d: Dv, +fs: S.Ext2Fs, +xs: List<&2, Nat>) -> Result<&2, &2, E.Ext2Error, Dv>:
  match none:
    case True{}:
      Done{d}
    case False{}:
      +n = List.length(&2, Nat, xs)
      do Result<&2, &2, E.Ext2Error, Dv>:
        S.Ext2.require(Ext2Alloc.all_inside(xs, fs), E.Ext2CheckFailed{"freeing a block outside the filesystem"})
        d2 : Dv <- Ext2Alloc.free.go(~Dv, ~block_size, ~read_block, ~write_block, Nat.add(n, 1n), Done{d}, Ext2Alloc.split(xs, fs), fs, Ext2Alloc.head_group(xs, fs))
        T.Ext2Meta.adjust_super(~Dv, ~block_size, ~read_block, ~write_block, d2, n, 0n, 0n, 0n)

# the blocks xs freed (in any order; each must be in use, and named once)
def Ext2Alloc.free_blocks(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +xs: List<&2, Nat>) -> Result<&2, &2, E.Ext2Error, Dv>:
  +sorted = Ext2Sort.nats(xs)
  Ext2Alloc.free_blocks.some(~Dv, ~block_size, ~read_block, ~write_block, List.is_empty(&2, Nat, sorted), d, fs, sorted)

# Freeing an inode

def Ext2Alloc.free_inode.fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, B.Octets>, +fs: S.Ext2Fs, +g: Nat, +dir: Bool, +desc: G.Ext2Group) -> Result<&2, &2, E.Ext2Error, Dv>:
  match out:
    case T.Ext2Out{d2, +raw2}:
      +raw3 = T.Ext2Meta.set_used_dirs(fs, T.Ext2Meta.set_free_inodes(fs, raw2, U32.add(G.Ext2Group.free_inodes(desc), 1)), U32.sub(G.Ext2Group.used_dirs(desc), Ext2Alloc.u32_bit(dir)))
      do Result<&2, &2, E.Ext2Error, Dv>:
        d3 : Dv <- T.Ext2Meta.desc_write(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, g, raw3)
        T.Ext2Meta.adjust_super(~Dv, ~block_size, ~read_block, ~write_block, d3, 0n, 0n, 1n, 0n)

# inode ino (a directory's if dir) freed in its bitmap and the counts
def Ext2Alloc.free_inode(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +dir: Bool) -> Result<&2, &2, E.Ext2Error, Dv>:
  +loc = N.Ext2Inode.locate(S.Ext2Fs.inodes_per_group(fs), ino)
  +g = N.Ext2InodeLoc.group(loc)
  +idx = N.Ext2InodeLoc.index(loc)
  do Result<&2, &2, E.Ext2Error, Dv>:
    S.Ext2.require(Bool.and(Nat.is_lt(0n, ino), Nat.is_le(ino, S.Ext2Fs.inodes_count(fs))), E.Ext2BadInodeNumber{ino})
    +raw : B.Octets <- T.Ext2Meta.desc_read(~Dv, ~block_size, ~read_block, d, fs, g)
    +desc : G.Ext2Group = T.Ext2Meta.desc(fs, raw)
    +bm : B.Octets <- T.Ext2Meta.inode_bitmap(~Dv, ~block_size, ~read_block, d, fs, desc)
    S.Ext2.require(M.Ext2Bitmap.test(bm, idx), E.Ext2CheckFailed{"freeing an inode that is not in use"})
    out : T.Ext2Out<Dv, B.Octets> <- T.Ext2Meta.put_inode_bitmap(~Dv, ~block_size, ~read_block, ~write_block, d, fs, raw, M.Ext2Bitmap.clear(bm, idx))
    Ext2Alloc.free_inode.fin(~Dv, ~block_size, ~read_block, ~write_block, out, fs, g, dir, desc)
