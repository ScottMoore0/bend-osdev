# bend-osdev-ext2: writing a file's data, through its block map (mapw.bend)
# or its extent tree (extentw.bend): writing a range (holes in it allocated,
# the rest overwritten in place; a block written in part keeps its other
# bytes), and cutting a file to a size (the blocks past it freed, and the
# bytes of the last block past it zeroed, so a later extension reads zeros).
#
# These work on an inode's raw record and hand back the record changed
# (map, i_blocks, size); the caller writes it (Ext2InodeW.write_raw), so an
# operation that changes an inode several ways writes it once.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./field.bend as F
import ./super.bend as S
import ./group.bend as G
import ./inode.bend as N
import ./blockmap.bend as M
import ./extent.bend as X
import ./patch.bend as P
import ./meta.bend as T
import ./alloc.bend as A
import ./inodew.bend as IW
import ./mapw.bend as MW
import ./extentw.bend as EW
import ./wopts.bend as WO

# A file's map, loaded for writing
type Ext2FMap is Data:
  Ext2FBlocks{iblock: B.Octets}
  Ext2FExtents{tree: EW.Ext2ExtTree}

def Ext2FileW.is_extents(+raw: B.Octets) -> Bool:
  IW.Ext2IRaw.has_flag(raw, N.Ext2Inode.flag_extents())

def Ext2FileW.load.pick(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, extents: Bool, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, Ext2FMap>:
  match extents:
    case True{}:
      Result.map(&2, &2, E.Ext2Error, EW.Ext2ExtTree, Ext2FMap, t => Ext2FExtents{t}, EW.Ext2ExtW.load(~Dv, ~block_size, ~read_block, d, fs, ino, IW.Ext2IRaw.generation(raw), IW.Ext2IRaw.iblock(raw)))
    case False{}:
      Done{Ext2FBlocks{IW.Ext2IRaw.iblock(raw)}}

# an inode's map (inline data is refused: not written here)
def Ext2FileW.load(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, Ext2FMap>:
  do Result<&2, &2, E.Ext2Error, Ext2FMap>:
    S.Ext2.require(Bool.not(IW.Ext2IRaw.has_flag(raw, N.Ext2Inode.flag_inline_data())), E.Ext2InlineData{ino})
    Ext2FileW.load.pick(~Dv, ~block_size, ~read_block, Ext2FileW.is_extents(raw), d, fs, ino, raw)

def Ext2FileW.hit_of(r: Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>) -> Result<&2, &2, E.Ext2Error, EW.Ext2ExtHit>:
  match r:
    case Done{Some{p}}:
      Done{EW.Ext2ExtAt{p}}
    case Done{None{}}:
      Done{EW.Ext2ExtHole{}}
    case Fail{e}:
      Fail{e}

# where logical block l of the file is (with no regard to its size)
def Ext2FileW.lookup(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, m: Ext2FMap, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +l: Nat) -> Result<&2, &2, E.Ext2Error, EW.Ext2ExtHit>:
  match m:
    case Ext2FBlocks{ib}:
      Ext2FileW.hit_of(M.Ext2Map.map(~Dv, ~block_size, ~read_block, d, fs, ino, ib, l))
    case Ext2FExtents{EW.Ext2ExtTree{es, ls}}:
      Done{EW.Ext2ExtW.lookup(es, l)}

def Ext2FileW.cons_hit(r: Result<&2, &2, E.Ext2Error, EW.Ext2ExtHit>, acc: List<&2, EW.Ext2ExtHit>) -> Result<&2, &2, E.Ext2Error, List<&2, EW.Ext2ExtHit>>:
  match r:
    case Done{h}:
      Done{Con{h, acc}}
    case Fail{e}:
      Fail{e}

# where count logical blocks from l on are (r: those before, last first)
def Ext2FileW.hits(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, count: Nat, r: Result<&2, &2, E.Ext2Error, List<&2, EW.Ext2ExtHit>>, +m: Ext2FMap, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +l: Nat) -> Result<&2, &2, E.Ext2Error, List<&2, EW.Ext2ExtHit>>:
  match count r:
    case _ Fail{e}:
      Fail{e}
    case 0n Done{acc}:
      Done{List.reverse(&2, EW.Ext2ExtHit, acc)}
    case 1n+c Done{acc}:
      Ext2FileW.hits(~Dv, ~block_size, ~read_block, c, Ext2FileW.cons_hit(Ext2FileW.lookup(~Dv, ~block_size, ~read_block, m, d, fs, ino, l), acc), m, d, fs, ino, Nat.add(l, 1n))

def Ext2FileW.holes(hs: List<&2, EW.Ext2ExtHit>, n: Nat) -> Nat:
  match hs:
    case Nil{}:
      n
    case Con{EW.Ext2ExtHole{}, t}:
      Ext2FileW.holes(t, Nat.add(n, 1n))
    case Con{h, t}:
      Ext2FileW.holes(t, n)

# the first unwritten block among the hits (from logical block l on)
def Ext2FileW.unwritten(hs: List<&2, EW.Ext2ExtHit>, +l: Nat) -> Maybe<&2, Nat>:
  match hs:
    case Nil{}:
      None{}
    case Con{EW.Ext2ExtUnwritten{}, t}:
      Some{l}
    case Con{h, t}:
      Ext2FileW.unwritten(t, Nat.add(l, 1n))

def Ext2FileW.no_unwritten(m: Maybe<&2, Nat>, +ino: Nat) -> Result<&2, &2, E.Ext2Error, Unit>:
  match m:
    case None{}:
      Done{Unit{}}
    case Some{l}:
      Fail{E.Ext2Unwritten{ino, l}}

# a new block of logical block l mapped to physical p
type Ext2Assign is Data:
  Ext2Assign{l: Nat, p: Nat}

# Writing the data blocks: hs says where each block of the range is; fresh
# are the blocks allocated for its holes, in order

def Ext2FileW.content(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, whole: Bool, existing: Bool, +d: Dv, +fs: S.Ext2Fs, +p: Nat, +skip: Nat, +piece: B.Octets) -> Result<&2, &2, E.Ext2Error, B.Octets>:
  match whole existing:
    case True{} _:
      Done{piece}
    case False{} True{}:
      Result.map(&2, &2, E.Ext2Error, B.Octets, B.Octets, o => P.Ext2Patch.bytes(o, skip, piece), S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, p))
    case False{} False{}:
      Done{P.Ext2Patch.bytes(B.Octets.zeros(S.Ext2Fs.block_size(fs)), skip, piece)}

def Ext2FileW.put.one(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, existing: Bool, +d: Dv, +fs: S.Ext2Fs, +p: Nat, +skip: Nat, +piece: B.Octets) -> Result<&2, &2, E.Ext2Error, Dv>:
  +bs = S.Ext2Fs.block_size(fs)
  do Result<&2, &2, E.Ext2Error, Dv>:
    o : B.Octets <- Ext2FileW.content(~Dv, ~block_size, ~read_block, Bool.and(Nat.is_eq(skip, 0n), Nat.is_eq(B.Octets.len(piece), bs)), existing, d, fs, p, skip, piece)
    T.Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d, fs, p, o)

type Ext2PutState is Data:
  Ext2PutState{fresh: List<&2, Nat>, assigns: List<&2, Ext2Assign>}

# the bytes of the next block's piece: what is left of the block after skip,
# or of the data
def Ext2FileW.piece(+fs: S.Ext2Fs, +skip: Nat, +rest: B.Octets) -> Nat:
  Nat.min(Nat.sub(S.Ext2Fs.block_size(fs), skip), B.Octets.len(rest))

def Ext2FileW.put.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, hs: List<&2, EW.Ext2ExtHit>, r: Result<&2, &2, E.Ext2Error, Dv>, st: Ext2PutState, +fs: S.Ext2Fs, +l: Nat, +skip: Nat, +rest: B.Octets) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Ext2Assign>>>:
  match hs r st:
    case _ Fail{e} _:
      Fail{e}
    case Nil{} Done{d} Ext2PutState{fr, asg}:
      Done{T.Ext2Out{d, List.reverse(&2, Ext2Assign, asg)}}
    case Con{EW.Ext2ExtAt{+p}, t} Done{+d} Ext2PutState{fr, asg}:
      +n = Ext2FileW.piece(fs, skip, rest)
      Ext2FileW.put.go(~Dv, ~block_size, ~read_block, ~write_block, t, Ext2FileW.put.one(~Dv, ~block_size, ~read_block, ~write_block, True{}, d, fs, p, skip, B.Octets.take(n, rest)), Ext2PutState{fr, asg}, fs, Nat.add(l, 1n), 0n, B.Octets.drop(n, rest))
    case Con{EW.Ext2ExtHole{}, t} Done{+d} Ext2PutState{Con{+p, ft}, asg}:
      +n = Ext2FileW.piece(fs, skip, rest)
      Ext2FileW.put.go(~Dv, ~block_size, ~read_block, ~write_block, t, Ext2FileW.put.one(~Dv, ~block_size, ~read_block, ~write_block, False{}, d, fs, p, skip, B.Octets.take(n, rest)), Ext2PutState{ft, Con{Ext2Assign{l, p}, asg}}, fs, Nat.add(l, 1n), 0n, B.Octets.drop(n, rest))
    case _ _ _:
      Fail{E.Ext2CheckFailed{"writing a file: a block with nowhere to go"}}

# Updating the map with the new blocks

def Ext2FileW.set_blocks.next(-Dv: Data, r: Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, MW.Ext2MapSet>>, meta: List<&2, Nat>) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, MW.Ext2MapSet>>:
  match r:
    case Done{T.Ext2Out{d, MW.Ext2MapSet{ib, m2}}}:
      Done{T.Ext2Out{d, MW.Ext2MapSet{ib, List.append(&2, Nat, m2, meta)}}}
    case Fail{e}:
      Fail{e}

def Ext2FileW.set_blocks(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, asg: List<&2, Ext2Assign>, r: Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, MW.Ext2MapSet>>, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, MW.Ext2MapSet>>:
  match asg r:
    case _ Fail{e}:
      Fail{e}
    case Nil{} Done{out}:
      Done{out}
    case Con{Ext2Assign{+l, +p}, t} Done{T.Ext2Out{+d, MW.Ext2MapSet{+ib, meta}}}:
      Ext2FileW.set_blocks(~Dv, ~block_size, ~read_block, ~write_block, t, Ext2FileW.set_blocks.next(Dv, MW.Ext2MapW.set(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, ib, l, p, p), meta), fs, wo, ino)

def Ext2FileW.insert_all(asg: List<&2, Ext2Assign>, es: List<&2, X.Ext2Extent>) -> List<&2, X.Ext2Extent>:
  match asg:
    case Nil{}:
      es
    case Con{Ext2Assign{+l, +p}, t}:
      Ext2FileW.insert_all(t, EW.Ext2ExtW.insert(es, l, p))

def Ext2FileW.last_p(asg: List<&2, Ext2Assign>, best: Nat) -> Nat:
  match asg:
    case Nil{}:
      best
    case Con{Ext2Assign{l, p}, t}:
      Ext2FileW.last_p(t, p)

def Ext2FileW.blocks_fin(-Dv: Data, out: T.Ext2Out<Dv, MW.Ext2MapSet>, +fs: S.Ext2Fs, +raw: B.Octets, +n: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
  match out:
    case T.Ext2Out{d, MW.Ext2MapSet{+ib, meta}}:
      Done{T.Ext2Out{d, IW.Ext2IRaw.add_blocks(fs, IW.Ext2IRaw.set_iblock(raw, ib), Nat.add(n, List.length(&2, Nat, meta)), 0n)}}

def Ext2FileW.extents_fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, EW.Ext2ExtStore>, +fs: S.Ext2Fs, +raw: B.Octets, +plus: Nat, freed: List<&2, Nat>) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
  match out:
    case T.Ext2Out{d, EW.Ext2ExtStore{+ib, added, +spare}}:
      +all = List.append(&2, Nat, freed, spare)
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
        d2 : Dv <- A.Ext2Alloc.free_blocks(~Dv, ~block_size, ~read_block, ~write_block, d, fs, all)
        return T.Ext2Out{d2, IW.Ext2IRaw.add_blocks(fs, IW.Ext2IRaw.set_iblock(raw, ib), Nat.add(plus, List.length(&2, Nat, added)), List.length(&2, Nat, all))}

# the map changed by the new blocks (and, for a block map, the indirect
# blocks on their paths): the raw record with its new map and i_blocks
def Ext2FileW.update_map(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, m: Ext2FMap, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +raw: B.Octets, +asg: List<&2, Ext2Assign>) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
  match m:
    case Ext2FBlocks{ib}:
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
        out : T.Ext2Out<Dv, MW.Ext2MapSet> <- Ext2FileW.set_blocks(~Dv, ~block_size, ~read_block, ~write_block, asg, Done{T.Ext2Out{d, MW.Ext2MapSet{ib, Nil{}}}}, fs, wo, ino)
        Ext2FileW.blocks_fin(Dv, out, fs, raw, List.length(&2, Ext2Assign, asg))
    case Ext2FExtents{EW.Ext2ExtTree{es, ls}}:
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
        out : T.Ext2Out<Dv, EW.Ext2ExtStore> <- EW.Ext2ExtW.store(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, IW.Ext2IRaw.generation(raw), ls, Ext2FileW.insert_all(asg, es), Ext2FileW.last_p(asg, 0n))
        Ext2FileW.extents_fin(~Dv, ~block_size, ~read_block, ~write_block, out, fs, raw, List.length(&2, Ext2Assign, asg), Nil{})

# Writing a range

def Ext2FileW.group_start(+fs: S.Ext2Fs, +ino: Nat) -> Nat:
  G.Ext2Group.first_block(fs, N.Ext2InodeLoc.group(N.Ext2Inode.locate(S.Ext2Fs.inodes_per_group(fs), ino)))

def Ext2FileW.goal.of(h: EW.Ext2ExtHit, +dflt: Nat) -> Nat:
  match h:
    case EW.Ext2ExtAt{p}:
      Nat.add(p, 1n)
    case _:
      dflt

def Ext2FileW.goal.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, start: Bool, +m: Ext2FMap, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +first: Nat) -> Nat:
  match start:
    case True{}:
      Ext2FileW.group_start(fs, ino)
    case False{}:
      +dflt = Ext2FileW.group_start(fs, ino)
      Result.default(&2, &2, E.Ext2Error, Nat, Result.map(&2, &2, E.Ext2Error, EW.Ext2ExtHit, Nat, h => Ext2FileW.goal.of(h, dflt), Ext2FileW.lookup(~Dv, ~block_size, ~read_block, m, d, fs, ino, Nat.sub(first, 1n))), dflt)

# where new blocks of a write from logical block first go: after the
# block before it, when that is mapped, else from the inode's group
def Ext2FileW.goal(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +m: Ext2FMap, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +first: Nat) -> Nat:
  Ext2FileW.goal.go(~Dv, ~block_size, ~read_block, Nat.is_eq(first, 0n), m, d, fs, ino, first)

def Ext2FileW.write.put(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, List<&2, Nat>>, +hs: List<&2, EW.Ext2ExtHit>, +fs: S.Ext2Fs, +first: Nat, +skip: Nat, +data: B.Octets) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, List<&2, Ext2Assign>>>:
  match out:
    case T.Ext2Out{d, fresh}:
      Ext2FileW.put.go(~Dv, ~block_size, ~read_block, ~write_block, hs, Done{d}, Ext2PutState{fresh, Nil{}}, fs, first, skip, data)

def Ext2FileW.write.map(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, List<&2, Ext2Assign>>, +m: Ext2FMap, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
  match out:
    case T.Ext2Out{+d, asg}:
      match asg:
        case Nil{}:
          Done{T.Ext2Out{d, raw}}
        case Con{a, t}:
          Ext2FileW.update_map(~Dv, ~block_size, ~read_block, ~write_block, m, d, fs, wo, ino, raw, Con{a, t})

def Ext2FileW.with_size(-Dv: Data, r: Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>, +end: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
  match r:
    case Done{T.Ext2Out{d, +raw}}:
      Done{T.Ext2Out{d, IW.Ext2IRaw.set_size(raw, Nat.max(IW.Ext2IRaw.size(raw), end))}}
    case Fail{e}:
      Fail{e}

def Ext2FileW.write.some(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, none: Bool, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +raw: B.Octets, +off: Nat, +data: B.Octets) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
  match none:
    case True{}:
      Done{T.Ext2Out{d, raw}}
    case False{}:
      +bs = S.Ext2Fs.block_size(fs)
      +first = Nat.div(off, bs)
      +end = Nat.add(off, B.Octets.len(data))
      +count = Nat.sub(Nat.div(Nat.add(end, Nat.sub(bs, 1n)), bs), first)
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
        +m : Ext2FMap <- Ext2FileW.load(~Dv, ~block_size, ~read_block, d, fs, ino, raw)
        +hs : List<&2, EW.Ext2ExtHit> <- Ext2FileW.hits(~Dv, ~block_size, ~read_block, count, Done{Nil{}}, m, d, fs, ino, first)
        Ext2FileW.no_unwritten(Ext2FileW.unwritten(hs, first), ino)
        a : T.Ext2Out<Dv, List<&2, Nat>> <- A.Ext2Alloc.blocks(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, Ext2FileW.goal(~Dv, ~block_size, ~read_block, m, d, fs, ino, first), Ext2FileW.holes(hs, 0n))
        p : T.Ext2Out<Dv, List<&2, Ext2Assign>> <- Ext2FileW.write.put(~Dv, ~block_size, ~read_block, ~write_block, a, hs, fs, first, Nat.mod(off, bs), data)
        Ext2FileW.with_size(Dv, Ext2FileW.write.map(~Dv, ~block_size, ~read_block, ~write_block, p, m, fs, wo, ino, raw), end)

# the bytes data written into inode ino's data from byte off (raw: its
# record): the holes the range covers get new blocks, the size grows to
# cover the range; the record comes back changed, for the caller to write
def Ext2FileW.write(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +raw: B.Octets, +off: Nat, +data: B.Octets) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
  Ext2FileW.write.some(~Dv, ~block_size, ~read_block, ~write_block, Nat.is_eq(B.Octets.len(data), 0n), d, fs, wo, ino, raw, off, data)

# Cutting to a size

def Ext2FileW.cut.blocks(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, MW.Ext2MapCut>, +fs: S.Ext2Fs, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
  match out:
    case T.Ext2Out{d, MW.Ext2MapCut{+ib, +freed}}:
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
        d2 : Dv <- A.Ext2Alloc.free_blocks(~Dv, ~block_size, ~read_block, ~write_block, d, fs, freed)
        return T.Ext2Out{d2, IW.Ext2IRaw.add_blocks(fs, IW.Ext2IRaw.set_iblock(raw, ib), 0n, List.length(&2, Nat, freed))}

def Ext2FileW.cut.extents(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, c: EW.Ext2ExtCut, ls: List<&2, Nat>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +raw: B.Octets) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
  match c:
    case EW.Ext2ExtCut{es2, freed}:
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
        out : T.Ext2Out<Dv, EW.Ext2ExtStore> <- EW.Ext2ExtW.store(~Dv, ~block_size, ~read_block, ~write_block, d, fs, wo, ino, IW.Ext2IRaw.generation(raw), ls, es2, Ext2FileW.group_start(fs, ino))
        Ext2FileW.extents_fin(~Dv, ~block_size, ~read_block, ~write_block, out, fs, raw, 0n, freed)

def Ext2FileW.cut.map(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, m: Ext2FMap, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +raw: B.Octets, +keep: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
  match m:
    case Ext2FBlocks{ib}:
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
        out : T.Ext2Out<Dv, MW.Ext2MapCut> <- MW.Ext2MapW.truncate(~Dv, ~block_size, ~read_block, ~write_block, d, fs, ino, ib, keep)
        Ext2FileW.cut.blocks(~Dv, ~block_size, ~read_block, ~write_block, out, fs, raw)
    case Ext2FExtents{EW.Ext2ExtTree{es, ls}}:
      Ext2FileW.cut.extents(~Dv, ~block_size, ~read_block, ~write_block, EW.Ext2ExtW.cut(es, keep), ls, d, fs, wo, ino, raw)

def Ext2FileW.zero_tail.at(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, h: EW.Ext2ExtHit, +d: Dv, +fs: S.Ext2Fs, +r: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  match h:
    case EW.Ext2ExtAt{+p}:
      do Result<&2, &2, E.Ext2Error, Dv>:
        o : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, p)
        T.Ext2Fs.write_block(~Dv, ~block_size, ~read_block, ~write_block, d, fs, p, P.Ext2Patch.bytes(o, r, B.Octets.zeros(Nat.sub(S.Ext2Fs.block_size(fs), r))))
    case _:
      Done{d}

def Ext2FileW.zero_tail.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, whole: Bool, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +raw: B.Octets, +size: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  match whole:
    case True{}:
      Done{d}
    case False{}:
      +bs = S.Ext2Fs.block_size(fs)
      do Result<&2, &2, E.Ext2Error, Dv>:
        m : Ext2FMap <- Ext2FileW.load(~Dv, ~block_size, ~read_block, d, fs, ino, raw)
        h : EW.Ext2ExtHit <- Ext2FileW.lookup(~Dv, ~block_size, ~read_block, m, d, fs, ino, Nat.div(size, bs))
        Ext2FileW.zero_tail.at(~Dv, ~block_size, ~read_block, ~write_block, h, d, fs, Nat.mod(size, bs))

# the bytes of the block holding byte size, from size on, zeroed (a cut
# file's last block, so that growing it again reads zeros)
def Ext2FileW.zero_tail(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +raw: B.Octets, +size: Nat) -> Result<&2, &2, E.Ext2Error, Dv>:
  Ext2FileW.zero_tail.go(~Dv, ~block_size, ~read_block, ~write_block, Nat.is_eq(Nat.mod(size, S.Ext2Fs.block_size(fs)), 0n), d, fs, ino, raw, size)

def Ext2FileW.truncate.fin(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, out: T.Ext2Out<Dv, B.Octets>, +fs: S.Ext2Fs, +ino: Nat, +size: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
  match out:
    case T.Ext2Out{d, +raw2}:
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
        d2 : Dv <- Ext2FileW.zero_tail(~Dv, ~block_size, ~read_block, ~write_block, d, fs, ino, raw2, size)
        return T.Ext2Out{d2, IW.Ext2IRaw.set_size(raw2, size)}

def Ext2FileW.truncate.go(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, shrink: Bool, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +raw: B.Octets, +size: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
  match shrink:
    case False{}:
      Done{T.Ext2Out{d, IW.Ext2IRaw.set_size(raw, size)}}
    case True{}:
      +bs = S.Ext2Fs.block_size(fs)
      do Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
        m : Ext2FMap <- Ext2FileW.load(~Dv, ~block_size, ~read_block, d, fs, ino, raw)
        out : T.Ext2Out<Dv, B.Octets> <- Ext2FileW.cut.map(~Dv, ~block_size, ~read_block, ~write_block, m, d, fs, wo, ino, raw, Nat.div(Nat.add(size, Nat.sub(bs, 1n)), bs))
        Ext2FileW.truncate.fin(~Dv, ~block_size, ~read_block, ~write_block, out, fs, ino, size)

# inode ino (raw: its record) cut or grown to size bytes: when it shrinks,
# the blocks past the new end are freed and the last block's bytes past it
# zeroed; when it grows, the new bytes are a hole. The record comes back
# changed, for the caller to write.
def Ext2FileW.truncate(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, ~write_block: Dv -> Nat -> B.Octets -> Result<&2, &2, D.DevError, Dv>, +d: Dv, +fs: S.Ext2Fs, +wo: WO.Ext2WriteOptions, +ino: Nat, +raw: B.Octets, +size: Nat) -> Result<&2, &2, E.Ext2Error, T.Ext2Out<Dv, B.Octets>>:
  Ext2FileW.truncate.go(~Dv, ~block_size, ~read_block, ~write_block, Nat.is_lt(size, IW.Ext2IRaw.size(raw)), d, fs, wo, ino, raw, size)
