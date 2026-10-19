# bend-osdev-deflate: the deflater's matcher, LZ77 with hash chains (RFC 1951,
# section 4, "Compression algorithm details").
#
# It turns the input into tokens, literals and matches (a length of 3 to
# 258 and a distance of 1 to 32768, 3.2.5), which block.bend codes. As
# section 4 describes: "The compressor uses a chained hash table to find
# duplicated strings, using a hash function that operates on 3-byte
# sequences"; it "compares all strings on the XYZ hash chain with the actual
# input data sequence starting at the current point, and selects the longest
# match"; "very long hash chains are arbitrarily truncated at a certain
# length, determined by a run-time parameter"; with "lazy matching", "after a
# match of length N has been found, the compressor searches for a longer
# match starting at the next input byte. If it finds a longer match, it
# truncates the previous match to a length of one (thus producing a single
# literal byte) and then emits the longer match"; and "If speed is most
# important, the compressor inserts new strings in the hash table only when
# no match was found, or when the match is not "too long"."
#
# Each of those is a parameter (DflMatchParams): how many chain entries a
# search looks at; the length that ends a search ("long enough"); the
# length below which a match is held back for a lazy look at the next byte
# (0: never, greedy); the longest match whose positions go into the table.
# The section gives no numbers; the named defaults and the levels below are
# this package's own. Two other strategies: run-length (distance 1 only) and
# Huffman only (no matches).
#
# The tables: a head table of 2^15 slots, keyed by a hash of the next three
# bytes, holding the latest position (+ 1) with that hash; a chain table of
# 32768 slots (the window), indexed by position modulo 32768, holding for
# each position the one before it with the same hash and the input from
# there on, which a candidate's match length is read from.
import Base
import ../bytes/bytes.bend as B

# Tokens

type DflTok is Data:
  DflLit{b: U32}
  DflMatch{len: U32, dist: U32}

# The parameters

type DflMatchParams is Data:
  DflMatchParams{chain: U32, nice: U32, lazy: U32, insert: U32}

type DflStrategy is Data:
  # hash chains, with these parameters
  DflStratChains{p: DflMatchParams}
  # matches at distance 1 only (runs of one byte)
  DflStratRle{}
  # no matches: every byte a literal (the Huffman codes do the work)
  DflStratHuffman{}

# the fast greedy matcher: a short search, no lazy matching, the positions
# of matches longer than 16 bytes not put in the table
def DflMatchParams.fast() -> DflMatchParams:
  DflMatchParams{8, 32, 0, 16}

# the lazier matcher: a long search, a lazy look after every match shorter
# than 32 bytes, every position put in the table
def DflMatchParams.lazy() -> DflMatchParams:
  DflMatchParams{128, 128, 32, 258}

def DflStrategy.default() -> DflStrategy:
  DflStratChains{DflMatchParams.lazy()}

def mt.sel(c: Bool, +a: DflMatchParams, +b: DflMatchParams) -> DflMatchParams:
  match c:
    case True{}:
      a
    case False{}:
      b

# the levels 1 to 9 (above 9 is 9; level 0, storing, is block.bend's): 1 to
# 3 greedy, 4 to 9 lazy, the search longer at each level
def DflMatchParams.level(+l: U32) -> DflMatchParams:
  mt.sel(U32.is_le(l, 1), DflMatchParams{4, 16, 0, 8},
  mt.sel(U32.is_le(l, 2), DflMatchParams.fast(),
  mt.sel(U32.is_le(l, 3), DflMatchParams{32, 64, 0, 64},
  mt.sel(U32.is_le(l, 4), DflMatchParams{16, 32, 8, 258},
  mt.sel(U32.is_le(l, 5), DflMatchParams{32, 64, 16, 258},
  mt.sel(U32.is_le(l, 6), DflMatchParams.lazy(),
  mt.sel(U32.is_le(l, 7), DflMatchParams{256, 192, 64, 258},
  mt.sel(U32.is_le(l, 8), DflMatchParams{1024, 258, 128, 258},
  DflMatchParams{4096, 258, 259, 258}))))))))

# The tables

# a chain slot: the position + 1 it holds (0: empty), the position + 1 of
# the one before it with the same hash (0: none), the input from there on
type DflNode is Data:
  DflNode{pos: U32, prev: U32, suf: List<&2, U32>}

# mask: the chain table's slots - 1; shift: 32 - the head table's key bits
type DflTabs is Type:
  DflTabs{head: Array<U32>, chain: Array<DflNode>, mask: U32, shift: Nat}

# the top 32 - shift bits of a hash of the next three bytes
def mt.hash(xs: List<&2, U32>, +shift: Nat) -> U32:
  match xs:
    case Con{a, Con{b, Con{c, t}}}:
      U32.shrn(U32.mul(U32.or(U32.or(a, U32.shln(b, 8n)), U32.shln(c, 16n)), 2654435761), shift)
    case _:
      0

def mt.ins.at(r: Array<U32> & U32, +h: U32, chain: Array<DflNode>, +mask: U32, +shift: Nat, +cur: List<&2, U32>, +i: U32) -> DflTabs:
  (head, +p) = r
  DflTabs{Array.set(U32, head, h, U32.add(i, 1)), Array.set(DflNode, chain, U32.and(i, mask), DflNode{U32.add(i, 1), p, cur}), mask, shift}

# position i (the input from it on: cur) goes into the tables
def mt.ins(t: DflTabs, +cur: List<&2, U32>, +i: U32) -> DflTabs:
  DflTabs{head, chain, +mask, +shift} = t
  +h = mt.hash(cur, shift)
  mt.ins.at(Array.get(U32, head, h), h, chain, mask, shift, cur, i)

# n positions from i on go into the tables
def mt.ins_run(n: Nat, t: DflTabs, +cur: List<&2, U32>, +i: U32) -> DflTabs:
  match n:
    case 0n:
      t
    case 1n+p:
      match cur:
        case Nil{}:
          t
        case Con{b, rest}:
          mt.ins_run(p, mt.ins(t, Con{b, rest}, i), rest, U32.add(i, 1))

def mt.inc_if(ok: Bool, n: Nat) -> Nat:
  match ok:
    case True{}:
      1n+n
    case False{}:
      n

# how many bytes a and b share from their starts, k at most; live: the
# bytes so far agree
def mt.common(a: List<&2, U32>, live: Bool, b: List<&2, U32>, +k: Nat, n: Nat) -> Nat:
  match a live:
    case Con{x, s} True{}:
      match b:
        case Nil{}:
          n
        case Con{y, t}:
          +ok = Bool.and(Nat.is_lt(0n, k), U32.is_eq(x, y))
          mt.common(s, ok, t, Nat.sub(k, 1n), mt.inc_if(ok, n))
    case _ _:
      n

# The search: a walk down the chain, keeping the longest match so far

type DflWalk is Type:
  DflWalkGo{chain: Array<DflNode>, p: U32, len: Nat, dist: U32}
  DflWalkEnd{chain: Array<DflNode>, len: Nat, dist: U32}

def mt.walk.best(better: Bool, stop: Bool, chain: Array<DflNode>, +prev: U32, +bl: Nat, +bd: U32, +l: Nat, +d: U32) -> DflWalk:
  match better:
    case True{}:
      match stop:
        case True{}:
          DflWalkEnd{chain, l, d}
        case False{}:
          DflWalkGo{chain, prev, l, d}
    case False{}:
      DflWalkGo{chain, prev, bl, bd}

def mt.walk.len(same: Bool, +suf: List<&2, U32>, +cur: List<&2, U32>, +k: Nat) -> Nat:
  match same:
    case True{}:
      mt.common(suf, True{}, cur, k, 0n)
    case False{}:
      0n

def mt.walk.node(r: Array<DflNode> & DflNode, +p: U32, +cur: List<&2, U32>, +i: U32, +k: Nat, +nice: Nat, +bl: Nat, +bd: U32) -> DflWalk:
  (chain, nd) = r
  match nd:
    case DflNode{+np, +prev, suf}:
      +l = mt.walk.len(U32.is_eq(np, p), suf, cur, k)
      mt.walk.best(Nat.is_lt(bl, l), Nat.is_le(nice, l), chain, prev, bl, bd, l, U32.sub(U32.add(i, 1), p))

def mt.walk.at(ok: Bool, chain: Array<DflNode>, +mask: U32, +p: U32, +cur: List<&2, U32>, +i: U32, +k: Nat, +nice: Nat, +bl: Nat, +bd: U32) -> DflWalk:
  match ok:
    case True{}:
      mt.walk.node(Array.get(DflNode, chain, U32.and(U32.sub(p, 1), mask)), p, cur, i, k, nice, bl, bd)
    case False{}:
      DflWalkEnd{chain, bl, bd}

# one candidate, if there is one (p is not 0) within 32768 bytes
def mt.walk.step(chain: Array<DflNode>, +mask: U32, +p: U32, +cur: List<&2, U32>, +i: U32, +k: Nat, +nice: Nat, +bl: Nat, +bd: U32) -> DflWalk:
  mt.walk.at(Bool.and(U32.is_lt(0, p), U32.is_le(U32.sub(U32.add(i, 1), p), 32768)), chain, mask, p, cur, i, k, nice, bl, bd)

# at most n candidates
def mt.walk(n: Nat, w: DflWalk, +mask: U32, +cur: List<&2, U32>, +i: U32, +k: Nat, +nice: Nat) -> DflWalk:
  match n:
    case 0n:
      w
    case 1n+m:
      match w:
        case DflWalkGo{chain, p, bl, bd}:
          mt.walk(m, mt.walk.step(chain, mask, p, cur, i, k, nice, bl, bd), mask, cur, i, k, nice)
        case DflWalkEnd{chain, bl, bd}:
          DflWalkEnd{chain, bl, bd}

# the tables back, with the longest match found (its length, 0 if none,
# and its distance)
type DflFound is Type:
  DflFound{tabs: DflTabs, len: Nat, dist: U32}

def mt.search.fin(w: DflWalk, head: Array<U32>, +mask: U32, +shift: Nat) -> DflFound:
  match w:
    case DflWalkGo{chain, p, bl, bd}:
      DflFound{DflTabs{head, chain, mask, shift}, bl, bd}
    case DflWalkEnd{chain, bl, bd}:
      DflFound{DflTabs{head, chain, mask, shift}, bl, bd}

def mt.search.at(r: Array<U32> & U32, chain: Array<DflNode>, +mask: U32, +shift: Nat, +depth: Nat, +nice: Nat, +cur: List<&2, U32>, +i: U32, +k: Nat) -> DflFound:
  (head, +p) = r
  mt.search.fin(mt.walk(depth, DflWalkGo{chain, p, 0n, 0}, mask, cur, i, k, nice), head, mask, shift)

# the longest match at position i (k bytes at most), among the depth newest
# earlier positions with the same hash
def mt.search(t: DflTabs, +depth: Nat, +nice: Nat, +cur: List<&2, U32>, +i: U32, +k: Nat) -> DflFound:
  DflTabs{head, chain, +mask, +shift} = t
  mt.search.at(Array.get(U32, head, mt.hash(cur, shift)), chain, mask, shift, depth, nice, cur, i, k)

# The matcher

# a parameter set as Nats, once
type DflMp is Data:
  DflMp{chain: Nat, nice: Nat, lazy: Nat, insert: Nat}

def mt.mp(p: DflMatchParams) -> DflMp:
  match p:
    case DflMatchParams{chain, nice, lazy, insert}:
      DflMp{U32.to_nat(chain), Nat.min(U32.to_nat(nice), 258n), U32.to_nat(lazy), U32.to_nat(insert)}

# tabs, the input from position i on (cur, n bytes of it), the tokens so
# far (reversed)
type DflMt is Type:
  DflMtGo{tabs: DflTabs, cur: List<&2, U32>, i: U32, n: Nat, out: List<&2, DflTok>}
  DflMtEnd{out: List<&2, DflTok>}

# the byte at i is a literal (its position already in the tables)
def mt.lit(tabs: DflTabs, cur: List<&2, U32>, +i: U32, n: Nat, out: List<&2, DflTok>) -> DflMt:
  match cur:
    case Nil{}:
      DflMtEnd{out}
    case Con{b, t}:
      DflMtGo{tabs, t, U32.add(i, 1), Nat.sub(n, 1n), Con{DflLit{b}, out}}

# a match of ml bytes at distance d; its positions after i go in if the
# match is not too long (i's own is in already)
def mt.emit(ins: Bool, tabs: DflTabs, +cur: List<&2, U32>, +i: U32, n: Nat, +ml: Nat, +d: U32, out: List<&2, DflTok>) -> DflMt:
  match ins:
    case True{}:
      DflMtGo{mt.ins_run(Nat.sub(ml, 1n), tabs, B.drop(1n, cur), U32.add(i, 1)), B.drop(ml, cur), U32.add(i, U32.from_nat(ml)), Nat.sub(n, ml), Con{DflMatch{U32.from_nat(ml), d}, out}}
    case False{}:
      DflMtGo{tabs, B.drop(ml, cur), U32.add(i, U32.from_nat(ml)), Nat.sub(n, ml), Con{DflMatch{U32.from_nat(ml), d}, out}}

def mt.lazy.pick(later: Bool, +ins: Bool, tabs: DflTabs, +cur: List<&2, U32>, +i: U32, +n: Nat, +ml: Nat, +d: U32, out: List<&2, DflTok>) -> DflMt:
  match later:
    case True{}:
      mt.lit(tabs, cur, i, n, out)
    case False{}:
      mt.emit(ins, tabs, cur, i, n, ml, d, out)

def mt.lazy.cmp(f: DflFound, +ins: Bool, +cur: List<&2, U32>, +i: U32, +n: Nat, +ml: Nat, +d: U32, out: List<&2, DflTok>) -> DflMt:
  DflFound{tabs, +ml2, d2} = f
  mt.lazy.pick(Nat.is_lt(ml, ml2), ins, tabs, cur, i, n, ml, d, out)

# a lazy look at i + 1, if a match may start there
def mt.lazy.at(more: Bool, +ins: Bool, tabs: DflTabs, +mp: DflMp, +cur: List<&2, U32>, +i: U32, +n: Nat, +ml: Nat, +d: U32, out: List<&2, DflTok>) -> DflMt:
  match more:
    case True{}:
      match mp:
        case DflMp{chain, nice, lazy, insert}:
          mt.lazy.cmp(mt.search(tabs, chain, nice, B.drop(1n, cur), U32.add(i, 1), Nat.min(Nat.sub(n, 1n), 258n)), ins, cur, i, n, ml, d, out)
    case False{}:
      mt.emit(ins, tabs, cur, i, n, ml, d, out)

def mt.take(lazy: Bool, +ins: Bool, tabs: DflTabs, +mp: DflMp, +cur: List<&2, U32>, +i: U32, +n: Nat, +ml: Nat, +d: U32, out: List<&2, DflTok>) -> DflMt:
  match lazy:
    case True{}:
      mt.lazy.at(Nat.is_lt(ml, n), ins, tabs, mp, cur, i, n, ml, d, out)
    case False{}:
      mt.emit(ins, tabs, cur, i, n, ml, d, out)

# a match of 3 bytes or more is taken; otherwise the byte is a literal
def mt.got(ok: Bool, tabs: DflTabs, +mp: DflMp, +cur: List<&2, U32>, +i: U32, +n: Nat, +ml: Nat, +d: U32, out: List<&2, DflTok>) -> DflMt:
  match ok:
    case True{}:
      match mp:
        case DflMp{chain, nice, lazy, insert}:
          mt.take(Nat.is_lt(ml, lazy), Nat.is_le(ml, insert), tabs, DflMp{chain, nice, lazy, insert}, cur, i, n, ml, d, out)
    case False{}:
      mt.lit(tabs, cur, i, n, out)

# the search's answer, with position i now put in the tables
def mt.found(f: DflFound, +mp: DflMp, +cur: List<&2, U32>, +i: U32, +n: Nat, out: List<&2, DflTok>) -> DflMt:
  DflFound{tabs, +ml, +d} = f
  mt.got(Nat.is_le(3n, ml), mt.ins(tabs, cur, i), mp, cur, i, n, ml, d, out)

# one position: the longest match among the earlier positions
def mt.step(+mp: DflMp, tabs: DflTabs, +cur: List<&2, U32>, +i: U32, +n: Nat, out: List<&2, DflTok>) -> DflMt:
  match mp:
    case DflMp{chain, nice, lazy, insert}:
      mt.found(mt.search(tabs, chain, nice, cur, i, Nat.min(n, 258n)), DflMp{chain, nice, lazy, insert}, cur, i, n, out)

def mt.loop(fuel: Nat, st: DflMt, +mp: DflMp) -> List<&2, DflTok>:
  match fuel:
    case 0n:
      match st:
        case DflMtGo{tabs, cur, i, n, out}:
          out
        case DflMtEnd{out}:
          out
    case 1n+f:
      match st:
        case DflMtGo{tabs, cur, i, n, out}:
          mt.loop(f, mt.step(mp, tabs, cur, i, n, out), mp)
        case DflMtEnd{out}:
          out

def mt.nsel(c: Bool, +a: Nat, +b: Nat) -> Nat:
  match c:
    case True{}:
      a
    case False{}:
      b

# the key bits d (1 to 15) the tables need for n positions: 2^d >= n, or 15
def mt.bits(fuel: Nat, +n: Nat, +d: Nat, +cap: Nat) -> Nat:
  match fuel:
    case 0n:
      d
    case 1n+f:
      +more = Nat.is_lt(cap, n)
      mt.bits(f, n, mt.nsel(more, 1n+d, d), mt.nsel(more, Nat.add(cap, cap), cap))

# tables sized for n positions (2^15 slots at most: the chain table then
# covers the 32 KB window): small inputs get small tables
def mt.tabs.new(+n: Nat) -> DflTabs:
  +d = mt.bits(14n, n, 1n, 2n)
  DflTabs{Array.new(U32, d, 0), Array.new(DflNode, d, DflNode{0, 0, Nil{}}), U32.sub(U32.shln(1, d), 1), Nat.sub(32n, d)}

# The other strategies

# prev: the input from the byte before cur on (Nil at the very start); n:
# how many bytes cur holds
type DflRle is Data:
  DflRle{prev: List<&2, U32>, cur: List<&2, U32>, n: Nat, out: List<&2, DflTok>}

def mt.rle.pick(ok: Bool, +ml: Nat, +cur: List<&2, U32>, +n: Nat, out: List<&2, DflTok>) -> DflRle:
  match ok:
    case True{}:
      DflRle{B.drop(Nat.sub(ml, 1n), cur), B.drop(ml, cur), Nat.sub(n, ml), Con{DflMatch{U32.from_nat(ml), 1}, out}}
    case False{}:
      match cur:
        case Nil{}:
          DflRle{Nil{}, Nil{}, 0n, out}
        case Con{b, t}:
          DflRle{Con{b, t}, t, Nat.sub(n, 1n), Con{DflLit{b}, out}}

def mt.rle.loop(fuel: Nat, s: DflRle) -> List<&2, DflTok>:
  match fuel:
    case 0n:
      match s:
        case DflRle{prev, cur, n, out}:
          out
    case 1n+f:
      match s:
        case DflRle{prev, +cur, +n, out}:
          +ml = mt.common(prev, True{}, cur, Nat.min(n, 258n), 0n)
          mt.rle.loop(f, mt.rle.pick(Nat.is_le(3n, ml), ml, cur, n, out))

# the byte before xs: hist's last, if any
def mt.rle.prev(hist: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, U32>:
  match hist:
    case Nil{}:
      Nil{}
    case Con{h, +t}:
      B.append.fast(B.drop(B.len.fast(t), Con{h, t}), xs)

def mt.huff(xs: List<&2, U32>, out: List<&2, DflTok>) -> List<&2, DflTok>:
  match xs:
    case Nil{}:
      out
    case Con{b, t}:
      mt.huff(t, Con{DflLit{b}, out})

# The public interface

# the tokens for xs after the history hist (at most its last 32768 bytes
# are reached), reversed (the last token first)
def match_tokens_rev(s: DflStrategy, +hist: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, DflTok>:
  match s:
    case DflStratChains{p}:
      +all = B.append.fast(hist, xs)
      +base = B.len.fast(hist)
      +n = B.len.fast(xs)
      tabs = mt.ins_run(base, mt.tabs.new(Nat.add(base, n)), all, 0)
      mt.loop(1n+n, DflMtGo{tabs, B.drop(base, all), U32.from_nat(base), n, Nil{}}, mt.mp(p))
    case DflStratRle{}:
      +n = B.len.fast(xs)
      mt.rle.loop(1n+n, DflRle{mt.rle.prev(hist, xs), xs, n, Nil{}})
    case DflStratHuffman{}:
      mt.huff(xs, Nil{})

# the tokens for xs after hist, in order
def match_tokens(+s: DflStrategy, +hist: List<&2, U32>, +xs: List<&2, U32>) -> List<&2, DflTok>:
  List.reverse(&2, DflTok, match_tokens_rev(s, hist, xs))
