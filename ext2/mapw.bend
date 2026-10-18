# bend-osdev-ext2: writing the classic block map (blockmap.bend reads it):
# pointing a logical block at a data block, with the indirect blocks on its
# path allocated (zeroed) as needed, and cutting a map back to its first
# blocks, freeing every data block past the cut and every indirect block
# that maps nothing kept. The map has at most three indirect levels, so each
# level is its own def (no recursion on the depth).
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./field.bend as F
import ./super.bend as S
import ./blockmap.bend as M
import ./patch.bend as P
import ./meta.bend as T
import ./alloc.bend as A
import ./wopts.bend as WO

# a new map (i_block) and the indirect blocks allocated for it
type Ext2MapSet is Data:
  Ext2MapSet{iblock: B.Octets, meta: List<&2, Nat>}

# a block pointer, and the blocks allocated to make it ([] if it existed)
type Ext2Ptr is Data:
  Ext2Ptr{block: Nat, fresh: List<&2, Nat>}

def Ext2MapW.per(+fs: S.Ext2Fs) -> Nat:
  Nat.div(S.Ext2Fs.block_size(fs), 4n)

def Ext2MapW.put(+o: B.Octets, +k: Nat, p: Nat) -> B.Octets:
  P.Ext2Patch.u32(o, Nat.mul(4n, k), U32.from_nat(p))

def Ext2MapW.new_block.fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, List<&2, Nat>>, +fs: S.Ext2Fs) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
  match out:
    case T.Ext2Out{d2, Con{+b, t}}:
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
        d3 : Dv <- T.Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, b, B.Octets.zeros(S.Ext2Fs.block_size(fs)))
        return T.Ext2Out{d3, b}
    case T.Ext2Out{d2, Nil{}}:
      Fail{E.Ext2NoSpace{}}

# a newly allocated block, zeroed
def Ext2MapW.new_block(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +goal: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>:
    out : T.Ext2Out<Dv, List<&2, Nat>> <- A.Ext2Alloc.blocks(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, goal, 1n)
    Ext2MapW.new_block.fin(~Dv, ~block_size, ~read_block, ~write_block, out, fs)

def Ext2MapW.ensure.fresh(-Dv: Data, r: Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Nat>>) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Ptr>>:
  match r:
    case Done{T.Ext2Out{d, +b}}:
      Done{T.Ext2Out{d, Ext2Ptr{b, [b]}}}
    case Fail{e}:
      Fail{e}

def Ext2MapW.ensure.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, m: Maybe<&2, Nat>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +goal: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Ptr>>:
  match m:
    case Some{b}:
      Done{T.Ext2Out{d, Ext2Ptr{b, Nil{}}}}
    case None{}:
      Ext2MapW.ensure.fresh(Dv, Ext2MapW.new_block(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, goal))

# the indirect block a pointer e names, allocated (zeroed) if e is 0
def Ext2MapW.ensure(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +e: Nat, +goal: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Ptr>>:
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Ptr>>:
    m : Maybe<&2, Nat> <- M.Ext2Map.check(fs, ino, e)
    Ext2MapW.ensure.go(~Dv, ~block_size, ~read_block, ~write_block, m, d, fs, wo, goal)

def Ext2MapW.descend.fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, Ext2Ptr>, +fs: S.Ext2Fs, +blk: Nat, +o: B.Octets, +j: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Ptr>>:
  match out:
    case T.Ext2Out{d2, Ext2Ptr{+c, fresh}}:
      match fresh:
        case Nil{}:
          Done{T.Ext2Out{d2, Ext2Ptr{c, Nil{}}}}
        case Con{f, ft}:
          do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Ptr>>:
            d3 : Dv <- T.Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, blk, Ext2MapW.put(o, j, c))
            return T.Ext2Out{d3, Ext2Ptr{c, Con{f, ft}}}

# entry j of indirect block blk, allocated if it is 0 (and blk updated)
def Ext2MapW.descend(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +blk: Nat, +j: Nat, +goal: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Ptr>>:
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2Ptr>>:
    +o : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, blk)
    out : T.Ext2Out<Dv, Ext2Ptr> <- Ext2MapW.ensure(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, M.Ext2Map.entry(o, j), goal)
    Ext2MapW.descend.fin(~Dv, ~block_size, ~read_block, ~write_block, out, fs, blk, o, j)

# Setting a pointer one, two or three levels down

def Ext2MapW.walk1(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +blk: Nat, +idx: Nat, +p: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
    +o : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, blk)
    d2 : Dv <- T.Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d, fs, blk, Ext2MapW.put(o, idx, p))
    return T.Ext2Out{d2, Nil{}}

def Ext2MapW.more(-Dv: Data, out: T.Ext2Out<Dv, List<&2, Nat>>, fresh: List<&2, Nat>) -> T.Ext2Out<Dv, List<&2, Nat>>:
  match out:
    case T.Ext2Out{d, xs}:
      T.Ext2Out{d, List.append(&2, Nat, fresh, xs)}

def Ext2MapW.walk2.fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, Ext2Ptr>, +fs: S.Ext2Fs, +idx: Nat, +p: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
  match out:
    case T.Ext2Out{d2, Ext2Ptr{c, fresh}}:
      Result.map(&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>, T.Ext2Out<Dv, List<&2, Nat>>, r => Ext2MapW.more(Dv, r, fresh), Ext2MapW.walk1(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, c, Nat.mod(idx, Ext2MapW.per(fs)), p))

def Ext2MapW.walk2(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +blk: Nat, +idx: Nat, +p: Nat, +goal: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
    out : T.Ext2Out<Dv, Ext2Ptr> <- Ext2MapW.descend(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, blk, Nat.div(idx, Ext2MapW.per(fs)), goal)
    Ext2MapW.walk2.fin(~Dv, ~block_size, ~read_block, ~write_block, out, fs, idx, p)

def Ext2MapW.walk3.fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, Ext2Ptr>, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +idx: Nat, +p: Nat, +goal: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
  match out:
    case T.Ext2Out{d2, Ext2Ptr{c, fresh}}:
      +per = Ext2MapW.per(fs)
      Result.map(&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>, T.Ext2Out<Dv, List<&2, Nat>>, r => Ext2MapW.more(Dv, r, fresh), Ext2MapW.walk2(~Dv, ~block_size, ~read_block, ~write_block, d2, fs, wo, ino, c, Nat.mod(idx, Nat.mul(per, per)), p, goal))

def Ext2MapW.walk3(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +blk: Nat, +idx: Nat, +p: Nat, +goal: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
  +per = Ext2MapW.per(fs)
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
    out : T.Ext2Out<Dv, Ext2Ptr> <- Ext2MapW.descend(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, blk, Nat.div(idx, Nat.mul(per, per)), goal)
    Ext2MapW.walk3.fin(~Dv, ~block_size, ~read_block, ~write_block, out, fs, wo, ino, idx, p, goal)

def Ext2MapW.walk(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, levels: Nat, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +blk: Nat, +idx: Nat, +p: Nat, +goal: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
  match levels:
    case 1n:
      Ext2MapW.walk1(~Dv, ~block_size, ~read_block, ~write_block, d, fs, blk, idx, p)
    case 2n:
      Ext2MapW.walk2(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, blk, idx, p, goal)
    case _:
      Ext2MapW.walk3(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, blk, idx, p, goal)

def Ext2MapW.set.fin(-Dv: Data, r: T.Ext2Out<Dv, List<&2, Nat>>, ib: B.Octets, fresh: List<&2, Nat>) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2MapSet>>:
  match r:
    case T.Ext2Out{d, xs}:
      Done{T.Ext2Out{d, Ext2MapSet{ib, List.append(&2, Nat, fresh, xs)}}}

def Ext2MapW.set.top(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, Ext2Ptr>, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +iblock: B.Octets, +slot: Nat, +levels: Nat, +index: Nat, +p: Nat, +goal: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2MapSet>>:
  match out:
    case T.Ext2Out{d2, Ext2Ptr{+top, fresh}}:
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2MapSet>>:
        r : T.Ext2Out<Dv, List<&2, Nat>> <- Ext2MapW.walk(~Dv, ~block_size, ~read_block, ~write_block, levels, d2, fs, wo, ino, top, index, p, goal)
        Ext2MapW.set.fin(Dv, r, Ext2MapW.put(iblock, slot, top), fresh)

def Ext2MapW.set.path(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, path: Maybe<&2, M.Ext2MapPath>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +iblock: B.Octets, +p: Nat, +goal: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2MapSet>>:
  match path:
    case None{}:
      Fail{E.Ext2FileTooBig{ino}}
    case Some{M.Ext2MapPath{+slot, +levels, +index}}:
      match levels:
        case 0n:
          Done{T.Ext2Out{d, Ext2MapSet{Ext2MapW.put(iblock, slot, p), Nil{}}}}
        case 1n+k:
          do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2MapSet>>:
            top : T.Ext2Out<Dv, Ext2Ptr> <- Ext2MapW.ensure(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, M.Ext2Map.entry(iblock, slot), goal)
            Ext2MapW.set.top(~Dv, ~block_size, ~read_block, ~write_block, top, fs, wo, ino, iblock, slot, 1n+k, index, p, goal)

# logical block l of the inode ino (whose map is iblock) pointed at block p:
# the new map and the indirect blocks allocated on the way (zeroed, placed
# from goal); Ext2FileTooBig past the triply indirect block
def Ext2MapW.set(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +iblock: B.Octets, +l: Nat, +p: Nat, +goal: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2MapSet>>:
  Ext2MapW.set.path(~Dv, ~block_size, ~read_block, ~write_block, M.Ext2Map.path(l, Ext2MapW.per(fs)), d, fs, wo, ino, iblock, p, goal)

# Cutting a map back

# the map after a cut, and the blocks freed (data and indirect)
type Ext2MapCut is Data:
  Ext2MapCut{iblock: B.Octets, freed: List<&2, Nat>}

def Ext2MapW.ptrs.keep(zero: Bool, v: U32, acc: List<&2, Nat>) -> List<&2, Nat>:
  match zero:
    case True{}:
      acc
    case False{}:
      Con{U32.to_nat(v), acc}

# the non-zero block numbers of a block of block numbers (bytes xs), onto acc
def Ext2MapW.ptrs(xs: List<&2, U32>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Con{+a, Con{+b, Con{+c, Con{+e, t}}}}:
      +v = U32.or(U32.and(255, a), U32.or(U32.shln(U32.and(255, b), 8n), U32.or(U32.shln(U32.and(255, c), 16n), U32.shln(U32.and(255, e), 24n))))
      Ext2MapW.ptrs(t, Ext2MapW.ptrs.keep(U32.is_eq(v, 0), v, acc))
    case _:
      acc

# the pointers in the blocks of a frontier, onto acc
def Ext2MapW.children(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, xs: List<&2, Nat>, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, acc: List<&2, Nat>) -> Result<&2, &2, E.Ext2Error, List<&2, Nat>>:
  match xs:
    case Nil{}:
      Done{acc}
    case Con{+b, t}:
      do Result<&2, &2, E.Ext2Error, List<&2, Nat>>:
        S.Ext2.require(M.Ext2Map.inside(fs, b), E.Ext2BadBlockRef{ino, b})
        o : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, b)
        Ext2MapW.children(~Dv, ~block_size, ~read_block, t, d, fs, ino, Ext2MapW.ptrs(B.Octets.to_list(o), acc))

# every block of the subtrees whose roots are the frontier, levels indirect
# levels above their data
def Ext2MapW.all(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, levels: Nat, frontier: List<&2, Nat>, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, acc: List<&2, Nat>) -> Result<&2, &2, E.Ext2Error, List<&2, Nat>>:
  match levels:
    case 0n:
      Done{List.reverse.go(&2, Nat, frontier, acc)}
    case 1n+k:
      +fr = frontier
      do Result<&2, &2, E.Ext2Error, List<&2, Nat>>:
        kids : List<&2, Nat> <- Ext2MapW.children(~Dv, ~block_size, ~read_block, fr, d, fs, ino, Nil{})
        Ext2MapW.all(~Dv, ~block_size, ~read_block, k, kids, d, fs, ino, List.reverse.go(&2, Nat, fr, acc))

def Ext2MapW.take.pick(zero: Bool, +o: B.Octets, +j: Nat) -> B.Octets:
  match zero:
    case True{}:
      o
    case False{}:
      Ext2MapW.put(o, j, 0n)

# entries j (from j on, n of them) of a block of pointers zeroed when they
# are not 0: the block, and the pointers taken (onto acc)
def Ext2MapW.take(n: Nat, +o: B.Octets, +j: Nat, acc: List<&2, Nat>) -> Ext2MapCut:
  match n:
    case 0n:
      Ext2MapCut{o, acc}
    case 1n+k:
      +e = M.Ext2Map.entry(o, j)
      Ext2MapW.take(k, Ext2MapW.take.pick(Nat.is_eq(e, 0n), o, j), Nat.add(j, 1n), Ext2MapW.ptrs.keep(Nat.is_eq(e, 0n), U32.from_nat(e), acc))

def Ext2MapW.flag(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def Ext2MapW.cut.write(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, c: Ext2MapCut, +d: Dv, +fs: S.Ext2Fs, +blk: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
  match c:
    case Ext2MapCut{o, roots}:
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
        d2 : Dv <- T.Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d, fs, blk, o)
        return T.Ext2Out{d2, roots}

# a singly indirect block (mapping from logical block base) cut at keep
# (base < keep): its entries from keep on taken
def Ext2MapW.cut1(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +blk: Nat, +base: Nat, +keep: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
  +j0 = Nat.sub(keep, base)
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
    o : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, blk)
    Ext2MapW.cut.write(~Dv, ~block_size, ~read_block, ~write_block, Ext2MapW.take(Nat.sub(Ext2MapW.per(fs), j0), o, j0, Nil{}), d, fs, blk)

def Ext2MapW.join(-Dv: Data, out: T.Ext2Out<Dv, List<&2, Nat>>, more: List<&2, Nat>) -> T.Ext2Out<Dv, List<&2, Nat>>:
  match out:
    case T.Ext2Out{d, xs}:
      T.Ext2Out{d, List.append(&2, Nat, xs, more)}

# what cutting a doubly or triply indirect block leaves to do: the blocks
# freed so far, and the child keep falls inside (if any: straddle) with the
# logical block it maps from
type Ext2CutHead is Data:
  Ext2CutHead{freed: List<&2, Nat>, straddle: Bool, child: Nat, base: Nat}

def Ext2MapW.cut.subtrees(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, out: T.Ext2Out<Dv, List<&2, Nat>>, +fs: S.Ext2Fs, +ino: Nat, lower: Nat, straddle: Bool, child: Nat, base: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2CutHead>>:
  match out:
    case T.Ext2Out{+d, roots}:
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2CutHead>>:
        xs : List<&2, Nat> <- Ext2MapW.all(~Dv, ~block_size, ~read_block, lower, roots, d, fs, ino, Nil{})
        return T.Ext2Out{d, Ext2CutHead{xs, straddle, child, base}}

# a block lower + 1 levels above its data (mapping from base), cut at keep:
# the children past the one keep falls in freed whole
def Ext2MapW.cut.head(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +lower: Nat, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +blk: Nat, +base: Nat, +keep: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2CutHead>>:
  +per = Ext2MapW.per(fs)
  +span = Nat.pow(per, lower)
  +rel = Nat.sub(keep, base)
  +j0 = Nat.div(rel, span)
  +r = Nat.mod(rel, span)
  +jf = Nat.add(j0, Ext2MapW.flag(Nat.is_lt(0n, r)))
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2CutHead>>:
    +o : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, blk)
    +c : Nat = M.Ext2Map.entry(o, j0)
    taken : T.Ext2Out<Dv, List<&2, Nat>> <- Ext2MapW.cut.write(~Dv, ~block_size, ~read_block, ~write_block, Ext2MapW.take(Nat.sub(per, jf), o, jf, Nil{}), d, fs, blk)
    Ext2MapW.cut.subtrees(~Dv, ~block_size, ~read_block, taken, fs, ino, lower, Bool.and(Nat.is_lt(0n, r), Bool.not(Nat.is_eq(c, 0n))), c, Nat.add(base, Nat.mul(j0, span)))

def Ext2MapW.cut2.last(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, h: T.Ext2Out<Dv, Ext2CutHead>, +fs: S.Ext2Fs, +keep: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
  match h:
    case T.Ext2Out{+d, Ext2CutHead{xs, straddle, +c, +base}}:
      match straddle:
        case True{}:
          Result.map(&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>, T.Ext2Out<Dv, List<&2, Nat>>, r => Ext2MapW.join(Dv, r, xs), Ext2MapW.cut1(~Dv, ~block_size, ~read_block, ~write_block, d, fs, c, base, keep))
        case False{}:
          Done{T.Ext2Out{d, xs}}

# a doubly indirect block mapping from base cut at keep (base < keep)
def Ext2MapW.cut2(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +blk: Nat, +base: Nat, +keep: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
    h : T.Ext2Out<Dv, Ext2CutHead> <- Ext2MapW.cut.head(~Dv, ~block_size, ~read_block, ~write_block, 1n, d, fs, ino, blk, base, keep)
    Ext2MapW.cut2.last(~Dv, ~block_size, ~read_block, ~write_block, h, fs, keep)

def Ext2MapW.cut3.last(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, h: T.Ext2Out<Dv, Ext2CutHead>, +fs: S.Ext2Fs, +ino: Nat, +keep: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
  match h:
    case T.Ext2Out{+d, Ext2CutHead{xs, straddle, +c, +base}}:
      match straddle:
        case True{}:
          Result.map(&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>, T.Ext2Out<Dv, List<&2, Nat>>, r => Ext2MapW.join(Dv, r, xs), Ext2MapW.cut2(~Dv, ~block_size, ~read_block, ~write_block, d, fs, ino, c, base, keep))
        case False{}:
          Done{T.Ext2Out{d, xs}}

# a triply indirect block mapping from base cut at keep (base < keep)
def Ext2MapW.cut3(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +blk: Nat, +base: Nat, +keep: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
    h : T.Ext2Out<Dv, Ext2CutHead> <- Ext2MapW.cut.head(~Dv, ~block_size, ~read_block, ~write_block, 2n, d, fs, ino, blk, base, keep)
    Ext2MapW.cut3.last(~Dv, ~block_size, ~read_block, ~write_block, h, fs, ino, keep)

def Ext2MapW.cut.part(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, levels: Nat, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +blk: Nat, +base: Nat, +keep: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>>:
  match levels:
    case 1n:
      Ext2MapW.cut1(~Dv, ~block_size, ~read_block, ~write_block, d, fs, blk, base, keep)
    case 2n:
      Ext2MapW.cut2(~Dv, ~block_size, ~read_block, ~write_block, d, fs, ino, blk, base, keep)
    case _:
      Ext2MapW.cut3(~Dv, ~block_size, ~read_block, ~write_block, d, fs, ino, blk, base, keep)

def Ext2MapW.slot.put(-Dv: Data, r: T.Ext2Out<Dv, List<&2, Nat>>, ib: B.Octets, freed: List<&2, Nat>) -> T.Ext2Out<Dv, Ext2MapCut>:
  match r:
    case T.Ext2Out{d, xs}:
      T.Ext2Out{d, Ext2MapCut{ib, List.append(&2, Nat, xs, freed)}}

def Ext2MapW.slot.mode.pick(zero: Bool, all: Bool, part: Bool) -> Nat:
  match zero all part:
    case True{} _ _:
      0n
    case False{} True{} _:
      1n
    case False{} False{} True{}:
      2n
    case False{} False{} False{}:
      0n

# what a cut at keep does to the subtree under an i_block slot that maps
# logical blocks base to base + span - 1: 0 nothing, 1 free it whole, 2 cut
# it
def Ext2MapW.slot.mode(+e: Nat, +keep: Nat, +base: Nat, +span: Nat) -> Nat:
  Ext2MapW.slot.mode.pick(Nat.is_eq(e, 0n), Nat.is_le(keep, base), Nat.is_lt(keep, Nat.add(base, span)))

def Ext2MapW.slot.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, mode: Nat, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +ib: B.Octets, freed: List<&2, Nat>, +slot: Nat, +levels: Nat, +base: Nat, +keep: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2MapCut>>:
  match mode:
    case 0n:
      Done{T.Ext2Out{d, Ext2MapCut{ib, freed}}}
    case 1n:
      Result.map(&2, &2, E.Ext2Error, List<&2, Nat>, T.Ext2Out<Dv, Ext2MapCut>, xs => T.Ext2Out{d, Ext2MapCut{Ext2MapW.put(ib, slot, 0n), List.append(&2, Nat, xs, freed)}}, Ext2MapW.all(~Dv, ~block_size, ~read_block, levels, [M.Ext2Map.entry(ib, slot)], d, fs, ino, Nil{}))
    case _:
      Result.map(&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Nat>>, T.Ext2Out<Dv, Ext2MapCut>, r => Ext2MapW.slot.put(Dv, r, ib, freed), Ext2MapW.cut.part(~Dv, ~block_size, ~read_block, ~write_block, levels, d, fs, ino, M.Ext2Map.entry(ib, slot), base, keep))

# the indirect slot (12, 13 or 14) of levels levels, mapping from base,
# cut at keep
def Ext2MapW.slot(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, Ext2MapCut>, +fs: S.Ext2Fs, +ino: Nat, +slot: Nat, +levels: Nat, +base: Nat, +keep: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2MapCut>>:
  match out:
    case T.Ext2Out{+d, Ext2MapCut{+ib, freed}}:
      Ext2MapW.slot.go(~Dv, ~block_size, ~read_block, ~write_block, Ext2MapW.slot.mode(M.Ext2Map.entry(ib, slot), keep, base, Nat.pow(Ext2MapW.per(fs), levels)), d, fs, ino, ib, freed, slot, levels, base, keep)

# the block map of inode ino (iblock) cut back to its first keep logical
# blocks: the new map, and every data and indirect block freed (which the
# caller frees, with Ext2Alloc.free_blocks)
def Ext2MapW.truncate(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +iblock: B.Octets, +keep: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2MapCut>>:
  +per = Ext2MapW.per(fs)
  +k0 = Nat.min(keep, 12n)
  +b2 = Nat.add(12n, per)
  do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, Ext2MapCut>>:
    o1 : T.Ext2Out<Dv, Ext2MapCut> <- Ext2MapW.slot(~Dv, ~block_size, ~read_block, ~write_block, T.Ext2Out{d, Ext2MapW.take(Nat.sub(12n, k0), iblock, k0, Nil{})}, fs, ino, 12n, 1n, 12n, keep)
    o2 : T.Ext2Out<Dv, Ext2MapCut> <- Ext2MapW.slot(~Dv, ~block_size, ~read_block, ~write_block, o1, fs, ino, 13n, 2n, b2, keep)
    Ext2MapW.slot(~Dv, ~block_size, ~read_block, ~write_block, o2, fs, ino, 14n, 3n, Nat.add(b2, Nat.mul(per, per)), keep)
