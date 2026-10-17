# bend-osdev-ext2: the classic block map of ext2 and ext3 (Poirier, "Inode
# Table", i_block): twelve direct block numbers, then one singly, one doubly
# and one triply indirect block. An indirect block holds block_size / 4
# block numbers; a block number 0 is a hole (it reads as zeros).
#
# Every block number the map answers, and every indirect block it reads,
# lies inside the filesystem (from s_first_data_block to the last block), or
# the map refuses with Ext2BadBlockRef.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./field.bend as F
import ./super.bend as S

# a block number read from the map: 0 is a hole; anything else must be a
# block of the filesystem
def Ext2Map.check.pick(zero: Bool, inside: Bool, +ino: Nat, +p: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  match zero inside:
    case True{} _:
      Done{None{}}
    case False{} True{}:
      Done{Some{p}}
    case False{} False{}:
      Fail{E.Ext2BadBlockRef{ino, p}}

def Ext2Map.inside(+fs: S.Ext2Fs, +p: Nat) -> Bool:
  Bool.and(Nat.is_le(U32.to_nat(S.Ext2Super.first_data_block(S.Ext2Fs.sb(fs))), p), Nat.is_lt(p, S.Ext2Fs.blocks(fs)))

def Ext2Map.check(+fs: S.Ext2Fs, +ino: Nat, +p: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  Ext2Map.check.pick(Nat.is_eq(p, 0n), Ext2Map.inside(fs, p), ino, p)

def Ext2Map.check_some.pick(inside: Bool, +ino: Nat, +p: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  match inside:
    case True{}:
      Done{Some{p}}
    case False{}:
      Fail{E.Ext2BadBlockRef{ino, p}}

# a block number that has no "hole" value (an extent's): None stays None,
# and a block must be inside the filesystem
def Ext2Map.check_some(+fs: S.Ext2Fs, +ino: Nat, m: Maybe<&2, Nat>) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  match m:
    case None{}:
      Done{None{}}
    case Some{+p}:
      Ext2Map.check_some.pick(Ext2Map.inside(fs, p), ino, p)

# the last check on any answer of a map: a block it names is inside the
# filesystem (the walks check every block number they read already; this
# makes the guarantee hold for every answer, whichever walk gave it)
def Ext2Map.final(+fs: S.Ext2Fs, +ino: Nat, r: Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  match r:
    case Done{m}:
      Ext2Map.check_some(fs, ino, m)
    case Fail{e}:
      Fail{e}

# block number k of a block of block numbers
def Ext2Map.entry(blk: B.Octets, k: Nat) -> Nat:
  F.Ext2Field.nat(blk, Nat.mul(4n, k))

# Where logical block l is: the i_block slot to start from, the number of
# indirect levels below it, and the index within that subtree

type Ext2MapPath is Data:
  Ext2MapPath{slot: Nat, levels: Nat, index: Nat}

def Ext2Map.path.t3(fits: Bool, +c: Nat) -> Maybe<&2, Ext2MapPath>:
  match fits:
    case True{}:
      Some{Ext2MapPath{14n, 3n, c}}
    case False{}:
      None{}

def Ext2Map.path.t2(fits: Bool, +b: Nat, +per: Nat) -> Maybe<&2, Ext2MapPath>:
  match fits:
    case True{}:
      Some{Ext2MapPath{13n, 2n, b}}
    case False{}:
      +c = Nat.sub(b, Nat.mul(per, per))
      Ext2Map.path.t3(Nat.is_lt(c, Nat.mul(per, Nat.mul(per, per))), c)

def Ext2Map.path.t1(fits: Bool, +a: Nat, +per: Nat) -> Maybe<&2, Ext2MapPath>:
  match fits:
    case True{}:
      Some{Ext2MapPath{12n, 1n, a}}
    case False{}:
      +b = Nat.sub(a, per)
      Ext2Map.path.t2(Nat.is_lt(b, Nat.mul(per, per)), b, per)

def Ext2Map.path.t0(direct: Bool, +l: Nat, +per: Nat) -> Maybe<&2, Ext2MapPath>:
  match direct:
    case True{}:
      Some{Ext2MapPath{l, 0n, 0n}}
    case False{}:
      +a = Nat.sub(l, 12n)
      Ext2Map.path.t1(Nat.is_lt(a, per), a, per)

# the path to logical block l, with per block numbers per indirect block;
# None past the triply indirect block's reach
def Ext2Map.path(+l: Nat, +per: Nat) -> Maybe<&2, Ext2MapPath>:
  Ext2Map.path.t0(Nat.is_lt(l, 12n), l, per)

# Walking down: from block number p, levels indirect blocks above the data,
# to entry index of that subtree (per^levels entries)

def Ext2Map.walk.down(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, levels: Nat, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +per: Nat, m: Maybe<&2, Nat>, +index: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  match levels:
    case 0n:
      Done{m}
    case 1n+l:
      match m:
        case None{}:
          Done{None{}}
        case Some{p}:
          +k = l
          +span = Nat.pow(per, k)
          do Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
            blk : B.Octets <- S.Ext2Fs.read_block(~Dv, ~block_size, ~read_block, d, fs, p)
            next : Maybe<&2, Nat> <- Ext2Map.check(fs, ino, Ext2Map.entry(blk, Nat.div(index, span)))
            Ext2Map.walk.down(~Dv, ~block_size, ~read_block, k, d, fs, ino, per, next, Nat.mod(index, span))

def Ext2Map.walk(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +iblock: B.Octets, +per: Nat, path: Maybe<&2, Ext2MapPath>, +l: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  match path:
    case None{}:
      Fail{E.Ext2PastEnd{ino, l}}
    case Some{Ext2MapPath{slot, levels, index}}:
      do Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
        top : Maybe<&2, Nat> <- Ext2Map.check(fs, ino, Ext2Map.entry(iblock, slot))
        Ext2Map.walk.down(~Dv, ~block_size, ~read_block, levels, d, fs, ino, per, top, index)

# the block holding logical block l of the inode numbered ino whose i_block
# is iblock: Some{block}, or None for a hole. Reads at most three indirect
# blocks.
def Ext2Map.map(~Dv: Data, ~block_size: Dv -> Nat, ~read_block: Dv -> Nat -> Result<&2, &2, D.DevError, B.Octets>, +d: Dv, +fs: S.Ext2Fs, +ino: Nat, +iblock: B.Octets, +l: Nat) -> Result<&2, &2, E.Ext2Error, Maybe<&2, Nat>>:
  +per = Nat.div(S.Ext2Fs.block_size(fs), 4n)
  Ext2Map.walk(~Dv, ~block_size, ~read_block, d, fs, ino, iblock, per, Ext2Map.path(l, per), l)
