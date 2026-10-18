# bend-osdev-lz4, compression: the high-compression matcher (LZ4HC), a
# hash-chain search whose depth the level sets.
#
# Written from the LZ4 Block Format Description (lz4_Block_format.md) and the
# published description of LZ4HC's strategy (the LZ4 project's documentation:
# LZ4HC writes ordinary LZ4 blocks, finding its matches through hash chains,
# searched more deeply the higher the level, over levels 3 to 12). No LZ4
# source was read; the depths below are this package's own.
#
# Every position goes into two tables: a head table, keyed by a 15-bit hash
# of the next four bytes, holds the latest position with that hash; a chain
# table of 65536 slots (the LZ4 window), indexed by position, holds for each
# position the one before it with the same hash. At a position the matcher
# walks the chain, newest first, through at most depth candidates within
# 65535 bytes, and keeps the longest match (stopping early at one of nice
# bytes or more). With lazy matching it then looks one position further on:
# if a longer match starts there, the byte here becomes a literal instead.
# Every position, inside matches too, goes into the tables, so later matches
# can reach back to it.
#
# The end-of-block rules are the fast matcher's: a match starts 12 bytes or
# more before the end of the block and ends 5 bytes or more before it.
import Base
import ../bytes/bytes.bend as B
import ./block.bend as K
import ./seq.bend as S

# The parameters

# depth: how many chain entries a search looks at, at most; nice: a match
# this long ends the search; lazy: look one position ahead before taking a
# match
type Lz4HcParams is Data:
  Lz4HcParams{depth: U32, nice: U32, lazy: Bool}

# LZ4HC's documented levels: 3 to 12, 9 by default
def lz4hc_level_min() -> U32:
  3

def lz4hc_level_default() -> U32:
  9

def lz4hc_level_max() -> U32:
  12

def hc.lv.sel(c: Bool, +a: U32, +b: U32) -> U32:
  match c:
    case True{}:
      a
    case False{}:
      b

# a level clamped into 3 to 12
def hc.lv.clamp(+l: U32) -> U32:
  hc.lv.sel(U32.is_lt(l, 3), 3, hc.lv.sel(U32.is_lt(12, l), 12, l))

# depth 2^(level - 1) up to level 10, then 1024 and 4096; nice 2^(level + 3)
# up to level 9, then no limit (65535, the longest a search can find within
# the window); lazy from level 10
def hc.lv.params(+l: U32) -> Lz4HcParams:
  +deep = U32.is_lt(9, l)
  +depth = hc.lv.sel(U32.is_lt(10, l), hc.lv.sel(U32.is_lt(11, l), 4096, 1024), U32.shln(1, U32.to_nat(U32.sub(l, 1))))
  Lz4HcParams{depth, hc.lv.sel(deep, 65535, U32.shln(1, U32.to_nat(U32.add(l, 3)))), deep}

# the parameters of a level (below 3 is 3, above 12 is 12)
def Lz4HcParams.level(+l: U32) -> Lz4HcParams:
  hc.lv.params(hc.lv.clamp(l))

def Lz4HcParams.default() -> Lz4HcParams:
  Lz4HcParams.level(lz4hc_level_default())

# The tables

# a chain slot: the position + 1 it holds (0: empty), the position + 1 of
# the one before it with the same hash (0: none), and the input from there on
type Lz4HcNode is Data:
  Lz4HcNode{pos: U32, prev: U32, suf: List<&2, U32>}

type Lz4HcTabs is Type:
  Lz4HcTabs{head: Array<U32>, chain: Array<Lz4HcNode>}

# 15 bits of a hash of the next four bytes
def hc.hash(xs: List<&2, U32>) -> U32:
  match xs:
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      U32.shrn(U32.mul(U32.or(U32.or(a, U32.shln(b, 8n)), U32.or(U32.shln(c, 16n), U32.shln(d, 24n))), 2654435761), 17n)
    case _:
      0

def hc.ins.at(r: Array<U32> & U32, +h: U32, chain: Array<Lz4HcNode>, +cur: List<&2, U32>, +i: U32) -> Lz4HcTabs:
  (head, +p) = r
  Lz4HcTabs{Array.set(U32, head, h, U32.add(i, 1)), Array.set(Lz4HcNode, chain, U32.and(i, 65535), Lz4HcNode{U32.add(i, 1), p, cur})}

# position i (the input from it on: cur) goes into the tables
def hc.ins(t: Lz4HcTabs, +cur: List<&2, U32>, +i: U32) -> Lz4HcTabs:
  Lz4HcTabs{head, chain} = t
  +h = hc.hash(cur)
  hc.ins.at(Array.get(U32, head, h), h, chain, cur, i)

# n positions from i on go into the tables
def hc.ins_run(n: Nat, t: Lz4HcTabs, +cur: List<&2, U32>, +i: U32) -> Lz4HcTabs:
  match n:
    case 0n:
      t
    case 1n+p:
      match cur:
        case Nil{}:
          t
        case Con{b, rest}:
          hc.ins_run(p, hc.ins(t, Con{b, rest}, i), rest, U32.add(i, 1))

# The search: a walk down the chain, keeping the longest match so far (its
# length and offset); p is the next candidate (position + 1)

type Lz4HcWalk is Type:
  Lz4HcWalkGo{chain: Array<Lz4HcNode>, p: U32, len: Nat, off: U32}
  Lz4HcWalkEnd{chain: Array<Lz4HcNode>, len: Nat, off: U32}

def hc.walk.stop(stop: Bool, chain: Array<Lz4HcNode>, +prev: U32, +l: Nat, +off: U32) -> Lz4HcWalk:
  match stop:
    case True{}:
      Lz4HcWalkEnd{chain, l, off}
    case False{}:
      Lz4HcWalkGo{chain, prev, l, off}

def hc.walk.best(better: Bool, +stop: Bool, chain: Array<Lz4HcNode>, +prev: U32, +bl: Nat, +bo: U32, +l: Nat, +off: U32) -> Lz4HcWalk:
  match better:
    case True{}:
      hc.walk.stop(stop, chain, prev, l, off)
    case False{}:
      Lz4HcWalkGo{chain, prev, bl, bo}

# how long the candidate's match is: 0 if its slot no longer holds it
def hc.walk.len(same: Bool, +suf: List<&2, U32>, +cur: List<&2, U32>, +k: U32) -> Nat:
  match same:
    case True{}:
      S.seq.common(suf, True{}, cur, k, 0n)
    case False{}:
      0n

def hc.walk.node(r: Array<Lz4HcNode> & Lz4HcNode, +p: U32, +cur: List<&2, U32>, +i: U32, +k: U32, +nice: Nat, +bl: Nat, +bo: U32) -> Lz4HcWalk:
  (chain, nd) = r
  match nd:
    case Lz4HcNode{+np, +prev, suf}:
      +l = hc.walk.len(U32.is_eq(np, p), suf, cur, k)
      hc.walk.best(Nat.is_lt(bl, l), Nat.is_le(nice, l), chain, prev, bl, bo, l, U32.sub(U32.add(i, 1), p))

def hc.walk.at(ok: Bool, chain: Array<Lz4HcNode>, +p: U32, +cur: List<&2, U32>, +i: U32, +k: U32, +nice: Nat, +bl: Nat, +bo: U32) -> Lz4HcWalk:
  match ok:
    case True{}:
      hc.walk.node(Array.get(Lz4HcNode, chain, U32.and(U32.sub(p, 1), 65535)), p, cur, i, k, nice, bl, bo)
    case False{}:
      Lz4HcWalkEnd{chain, bl, bo}

# one candidate, if there is one (p is not 0) within the window
def hc.walk.step(chain: Array<Lz4HcNode>, +p: U32, +cur: List<&2, U32>, +i: U32, +k: U32, +nice: Nat, +bl: Nat, +bo: U32) -> Lz4HcWalk:
  hc.walk.at(Bool.and(U32.is_lt(0, p), U32.is_le(U32.sub(U32.add(i, 1), p), 65535)), chain, p, cur, i, k, nice, bl, bo)

# at most n candidates
def hc.walk(n: Nat, w: Lz4HcWalk, +cur: List<&2, U32>, +i: U32, +k: U32, +nice: Nat) -> Lz4HcWalk:
  match n:
    case 0n:
      w
    case 1n+m:
      match w:
        case Lz4HcWalkGo{chain, p, bl, bo}:
          hc.walk(m, hc.walk.step(chain, p, cur, i, k, nice, bl, bo), cur, i, k, nice)
        case Lz4HcWalkEnd{chain, bl, bo}:
          Lz4HcWalkEnd{chain, bl, bo}

# the tables back, with the longest match found (its length, 0 if none, and
# its offset)
type Lz4HcFound is Type:
  Lz4HcFound{tabs: Lz4HcTabs, len: Nat, off: U32}

def hc.search.fin(w: Lz4HcWalk, head: Array<U32>) -> Lz4HcFound:
  match w:
    case Lz4HcWalkGo{chain, p, bl, bo}:
      Lz4HcFound{Lz4HcTabs{head, chain}, bl, bo}
    case Lz4HcWalkEnd{chain, bl, bo}:
      Lz4HcFound{Lz4HcTabs{head, chain}, bl, bo}

def hc.search.at(r: Array<U32> & U32, chain: Array<Lz4HcNode>, +depth: U32, +nice: U32, +cur: List<&2, U32>, +i: U32, +k: U32) -> Lz4HcFound:
  (head, +p) = r
  hc.search.fin(hc.walk(U32.to_nat(depth), Lz4HcWalkGo{chain, p, 0n, 0}, cur, i, k, U32.to_nat(nice)), head)

# the longest match at position i (k bytes at most), among the depth newest
# earlier positions with the same hash
def hc.search(t: Lz4HcTabs, +depth: U32, +nice: U32, +cur: List<&2, U32>, +i: U32, +k: U32) -> Lz4HcFound:
  Lz4HcTabs{head, chain} = t
  hc.search.at(Array.get(U32, head, hc.hash(cur)), chain, depth, nice, cur, i, k)

# The matcher: tables, the input from position i on, the last position a
# match may start at (lim) and the last it may reach (end), the literals
# since the last match (reversed), the output so far (reversed)
type Lz4HcEnc is Type:
  Lz4HcGo{tabs: Lz4HcTabs, cur: List<&2, U32>, i: U32, lim: U32, end: U32, lits: List<&2, U32>, out: List<&2, U32>}
  Lz4HcEnd{out: List<&2, U32>}

# the byte at i joins the literals
def hc.lit(tabs: Lz4HcTabs, +cur: List<&2, U32>, +i: U32, lim: U32, end: U32, lits: List<&2, U32>, out: List<&2, U32>) -> Lz4HcEnc:
  match cur:
    case Nil{}:
      Lz4HcEnd{S.seq.last(K.blk.rev(lits), out)}
    case Con{b, t}:
      Lz4HcGo{tabs, t, U32.add(i, 1), lim, end, Con{b, lits}, out}

# a match of ml bytes at offset off; the positions it covers from i + skip
# on go into the tables (those before are in already)
def hc.emit(tabs: Lz4HcTabs, +skip: Nat, +cur: List<&2, U32>, +i: U32, +ml: Nat, +off: U32, lim: U32, end: U32, +lits: List<&2, U32>, out: List<&2, U32>) -> Lz4HcEnc:
  Lz4HcGo{hc.ins_run(Nat.sub(ml, skip), tabs, B.drop(skip, cur), U32.add(i, U32.from_nat(skip))), B.drop(ml, cur), U32.add(i, U32.from_nat(ml)), lim, end, Nil{}, S.seq.push(K.blk.rev(lits), off, ml, out)}

# lazy matching: a longer match at i + 1 makes the byte at i a literal
def hc.lazy.pick(later: Bool, tabs: Lz4HcTabs, +cur: List<&2, U32>, +i: U32, +ml: Nat, +off: U32, lim: U32, end: U32, lits: List<&2, U32>, out: List<&2, U32>) -> Lz4HcEnc:
  match later:
    case True{}:
      hc.lit(tabs, cur, i, lim, end, lits, out)
    case False{}:
      hc.emit(tabs, 1n, cur, i, ml, off, lim, end, lits, out)

def hc.lazy.cmp(f: Lz4HcFound, +cur: List<&2, U32>, +i: U32, +ml: Nat, +off: U32, lim: U32, end: U32, lits: List<&2, U32>, out: List<&2, U32>) -> Lz4HcEnc:
  Lz4HcFound{tabs, +ml2, off2} = f
  hc.lazy.pick(Nat.is_lt(ml, ml2), tabs, cur, i, ml, off, lim, end, lits, out)

# position i is in the tables; look at i + 1 if a match may start there
def hc.lazy.at(more: Bool, tabs: Lz4HcTabs, +depth: U32, +nice: U32, +cur: List<&2, U32>, +i: U32, +ml: Nat, +off: U32, +lim: U32, +end: U32, lits: List<&2, U32>, out: List<&2, U32>) -> Lz4HcEnc:
  match more:
    case True{}:
      +j = U32.add(i, 1)
      hc.lazy.cmp(hc.search(tabs, depth, nice, B.drop(1n, cur), j, U32.sub(end, j)), cur, i, ml, off, lim, end, lits, out)
    case False{}:
      hc.emit(tabs, 1n, cur, i, ml, off, lim, end, lits, out)

def hc.take(lazy: Bool, tabs: Lz4HcTabs, +depth: U32, +nice: U32, +cur: List<&2, U32>, +i: U32, +ml: Nat, +off: U32, +lim: U32, +end: U32, lits: List<&2, U32>, out: List<&2, U32>) -> Lz4HcEnc:
  match lazy:
    case True{}:
      hc.lazy.at(U32.is_le(U32.add(i, 1), lim), hc.ins(tabs, cur, i), depth, nice, cur, i, ml, off, lim, end, lits, out)
    case False{}:
      hc.emit(tabs, 0n, cur, i, ml, off, lim, end, lits, out)

# a match of 4 bytes or more is taken; otherwise the byte is a literal
def hc.got(ok: Bool, +lazy: Bool, tabs: Lz4HcTabs, +depth: U32, +nice: U32, +cur: List<&2, U32>, +i: U32, +ml: Nat, +off: U32, +lim: U32, +end: U32, lits: List<&2, U32>, out: List<&2, U32>) -> Lz4HcEnc:
  match ok:
    case True{}:
      hc.take(lazy, tabs, depth, nice, cur, i, ml, off, lim, end, lits, out)
    case False{}:
      hc.lit(hc.ins(tabs, cur, i), cur, i, lim, end, lits, out)

def hc.found(f: Lz4HcFound, +lazy: Bool, +depth: U32, +nice: U32, +cur: List<&2, U32>, +i: U32, +lim: U32, +end: U32, lits: List<&2, U32>, out: List<&2, U32>) -> Lz4HcEnc:
  Lz4HcFound{tabs, +ml, +off} = f
  hc.got(Nat.is_le(4n, ml), lazy, tabs, depth, nice, cur, i, ml, off, lim, end, lits, out)

def hc.step.at(go: Bool, p: Lz4HcParams, tabs: Lz4HcTabs, +cur: List<&2, U32>, +i: U32, +lim: U32, +end: U32, lits: List<&2, U32>, out: List<&2, U32>) -> Lz4HcEnc:
  match go:
    case True{}:
      match p:
        case Lz4HcParams{+depth, +nice, lazy}:
          hc.found(hc.search(tabs, depth, nice, cur, i, U32.sub(end, i)), lazy, depth, nice, cur, i, lim, end, lits, out)
    case False{}:
      Lz4HcEnd{S.seq.last(B.rev_onto(lits, cur), out)}

# one position: past the last place a match may start, the rest are literals
def hc.step(p: Lz4HcParams, tabs: Lz4HcTabs, cur: List<&2, U32>, +i: U32, +lim: U32, end: U32, lits: List<&2, U32>, out: List<&2, U32>) -> Lz4HcEnc:
  hc.step.at(U32.is_le(i, lim), p, tabs, cur, i, lim, end, lits, out)

# every step moves on a byte or more, so fuel of the input's length + 1
# reaches the end
def hc.loop(fuel: Nat, st: Lz4HcEnc, +p: Lz4HcParams) -> List<&2, U32>:
  match fuel:
    case 0n:
      match st:
        case Lz4HcGo{tabs, cur, i, lim, end, lits, out}:
          K.blk.rev(S.seq.last(B.rev_onto(lits, cur), out))
        case Lz4HcEnd{out}:
          K.blk.rev(out)
    case 1n+f:
      match st:
        case Lz4HcGo{tabs, cur, i, lim, end, lits, out}:
          hc.loop(f, hc.step(p, tabs, cur, i, lim, end, lits, out), p)
        case Lz4HcEnd{out}:
          K.blk.rev(out)

def hc.start(big: Bool, +p: Lz4HcParams, +dict: List<&2, U32>, +xs: List<&2, U32>, +total: U32) -> List<&2, U32>:
  match big:
    case True{}:
      +all = B.append.fast(dict, xs)
      +base = B.len.fast(dict)
      tabs = hc.ins_run(base, Lz4HcTabs{Array.new(U32, 15n, 0), Array.new(Lz4HcNode, 16n, Lz4HcNode{0, 0, Nil{}})}, all, 0)
      hc.loop(Nat.add(B.len.fast(xs), 1n), Lz4HcGo{tabs, B.drop(base, all), U32.from_nat(base), U32.sub(total, 12), U32.sub(total, 5), Nil{}, Nil{}}, p)
    case False{}:
      K.blk.rev(S.seq.last(xs, Nil{}))

# the block for xs, after the history dict (at most its last 65535 bytes),
# as a byte list
def hc.block(+p: Lz4HcParams, +dict: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, U32>:
  +d = B.drop(Nat.sub(B.len.fast(dict), 65535n), dict)
  +total = U32.from_nat(Nat.add(B.len.fast(d), B.len.fast(xs)))
  hc.start(U32.is_le(13, total), p, d, xs, total)
