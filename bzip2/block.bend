# bend-osdev-bzip2: decoding one block (Tsai, "BZip2 Format Specification",
# section 3: the block header, the symbol map, the Huffman tables and their
# selectors, the coded data; section 4: the stages that undo the
# compression, in order: Huffman, MTF and RLE2, the inverse BWT, RLE1).
#
# A block starts with the 48-bit magic 0x314159265359, then its CRC (32
# bits), the randomised bit, origPtr (24 bits), the symbol map (16 bits, then
# 16 for each group marked), the number of tables (3 bits, 2 to 6), the number
# of selectors (15 bits, at least 1), the selectors (each the unary code of
# its move-to-front position: that many 1 bits, then a 0), the tables (a
# 5-bit start length, then for each symbol: 0 ends it, 10 adds one, 11
# subtracts one; every length 1 to 20), and the symbols, each group of 50
# coded with the table its selector names, up to the end-of-block symbol.
# The end of the stream is the 48-bit magic 0x177245385090 and the stream's
# combined CRC.
import Base
import ../bytes/bytes.bend as B
import ./list.bend as L
import ./error.bend as E
import ./bits.bend as K
import ./huffman.bend as H
import ./mtf.bend as M
import ./bwt.bend as W
import ./rle.bend as R

# What a block reads to: the reader after it, its stored CRC and its bytes
# (the RLE1 decoding of its inverse BWT); or the end of the stream and the
# stored combined CRC; or a failure
type Bzip2Blk is Data:
  Bzip2BlkData{r: K.Bzip2Bits, crc: U32, bytes: List<&2, U32>}
  Bzip2BlkEnd{r: K.Bzip2Bits, crc: U32}
  Bzip2BlkBad{e: E.Bzip2Error}

def blk.fail.pick(over: Bool, e: E.Bzip2Error) -> Bzip2Blk:
  match over:
    case True{}:
      Bzip2BlkBad{E.Bzip2Truncated{}}
    case False{}:
      Bzip2BlkBad{e}

# a failure, unless the reader went past the end of the input (then the
# input was cut short)
def blk.fail(+r: K.Bzip2Bits, e: E.Bzip2Error) -> Bzip2Blk:
  blk.fail.pick(K.bits.over(r), e)

# The symbol map

type Bzip2Map is Data:
  Bzip2Map{r: K.Bzip2Bits, acc: List<&2, U32>}

def map.byte(on: Bool, +b: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match on:
    case True{}:
      Con{b, acc}
    case False{}:
      acc

# the 16 bits of a group: byte base + j is used if bit j (from the top) is set
def map.bits(n: Nat, +w: U32, +m: U32, +b: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      map.bits(p, w, U32.shr(m), U32.add(b, 1), map.byte(U32.is_ne(U32.and(w, m), 0), b, acc))

def map.grp.read(g: K.Bzip2Got, +base: U32, acc: List<&2, U32>) -> Bzip2Map:
  match g:
    case K.Bzip2Got{r, w}:
      Bzip2Map{r, map.bits(16n, w, 32768, base, acc)}

def map.grp(on: Bool, r: K.Bzip2Bits, +base: U32, acc: List<&2, U32>) -> Bzip2Map:
  match on:
    case True{}:
      map.grp.read(K.bits.read(16n, r), base, acc)
    case False{}:
      Bzip2Map{r, acc}

def map.go(n: Nat, st: Bzip2Map, +g: U32, +m: U32, +base: U32) -> Bzip2Map:
  match n:
    case 0n:
      st
    case 1n+p:
      match st:
        case Bzip2Map{r, acc}:
          map.go(p, map.grp(U32.is_ne(U32.and(g, m), 0), r, base, acc), g, U32.shr(m), U32.add(base, 16))

# The selectors: each the unary code of a position in a move-to-front list of
# the tables

type Bzip2Sel is Data:
  Bzip2SelGo{r: K.Bzip2Bits, mtf: List<&2, U32>, acc: List<&2, U32>}
  Bzip2SelBad{r: K.Bzip2Bits}

type Bzip2Unary is Data:
  Bzip2UnaryGo{f: K.Bzip2Flag, j: Nat}
  Bzip2UnaryDone{r: K.Bzip2Bits, j: Nat}
  Bzip2UnaryBad{r: K.Bzip2Bits}

def sel.unary.next(ok: Bool, r: K.Bzip2Bits, j: Nat) -> Bzip2Unary:
  match ok:
    case True{}:
      Bzip2UnaryGo{K.bits.flag(r), j}
    case False{}:
      Bzip2UnaryBad{r}

def sel.unary.step(f: K.Bzip2Flag, +j: Nat, +ng: Nat) -> Bzip2Unary:
  match f:
    case K.Bzip2Flag{r, b}:
      match b:
        case False{}:
          Bzip2UnaryDone{r, j}
        case True{}:
          sel.unary.next(Nat.is_lt(1n+j, ng), r, 1n+j)

# 1 bits until a 0: their count, which must stay below ng
def sel.unary(fuel: Nat, u: Bzip2Unary, +ng: Nat) -> Bzip2Unary:
  match fuel:
    case 0n:
      u
    case 1n+f:
      match u:
        case Bzip2UnaryGo{g, j}:
          sel.unary(f, sel.unary.step(g, j, ng), ng)
        case Bzip2UnaryDone{r, j}:
          Bzip2UnaryDone{r, j}
        case Bzip2UnaryBad{r}:
          Bzip2UnaryBad{r}

def sel.taken(m: Maybe<&2, M.Bzip2MtfTake>, r: K.Bzip2Bits, acc: List<&2, U32>) -> Bzip2Sel:
  match m:
    case Some{t}:
      match t:
        case M.Bzip2MtfTake{+x, rest}:
          Bzip2SelGo{r, Con{x, rest}, Con{x, acc}}
    case None{}:
      Bzip2SelBad{r}

def sel.one(u: Bzip2Unary, mtf: List<&2, U32>, acc: List<&2, U32>) -> Bzip2Sel:
  match u:
    case Bzip2UnaryDone{r, j}:
      sel.taken(M.mtf.take(mtf, j), r, acc)
    case Bzip2UnaryGo{g, j}:
      match g:
        case K.Bzip2Flag{r, b}:
          Bzip2SelBad{r}
    case Bzip2UnaryBad{r}:
      Bzip2SelBad{r}

def sel.go(n: Nat, st: Bzip2Sel, +ng: Nat) -> Bzip2Sel:
  match n:
    case 0n:
      st
    case 1n+p:
      match st:
        case Bzip2SelBad{r}:
          Bzip2SelBad{r}
        case Bzip2SelGo{r, mtf, acc}:
          sel.go(p, sel.one(sel.unary(1n+ng, Bzip2UnaryGo{K.bits.flag(r), 0n}, ng), mtf, acc), ng)

# [0, 1, ..., n - 1]
def sel.iota(n: Nat, +i: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{i, sel.iota(p, U32.add(i, 1))}

# The tables: delta-coded code lengths

type Bzip2Len is Data:
  Bzip2LenGo{r: K.Bzip2Bits, curr: U32}
  Bzip2LenDone{r: K.Bzip2Bits, curr: U32}
  Bzip2LenBad{r: K.Bzip2Bits}

def len.ok(+c: U32) -> Bool:
  Bool.and(U32.is_le(1, c), U32.is_le(c, 20))

def len.second(f: K.Bzip2Flag, +curr: U32) -> Bzip2Len:
  match f:
    case K.Bzip2Flag{r, b}:
      match b:
        case False{}:
          Bzip2LenGo{r, U32.add(curr, 1)}
        case True{}:
          Bzip2LenGo{r, U32.sub(curr, 1)}

def len.first(f: K.Bzip2Flag, +curr: U32) -> Bzip2Len:
  match f:
    case K.Bzip2Flag{r, b}:
      match b:
        case False{}:
          Bzip2LenDone{r, curr}
        case True{}:
          len.second(K.bits.flag(r), curr)

def len.step(ok: Bool, r: K.Bzip2Bits, +curr: U32) -> Bzip2Len:
  match ok:
    case True{}:
      len.first(K.bits.flag(r), curr)
    case False{}:
      Bzip2LenBad{r}

# one symbol's length, from the length before (fuel: more than the bits left)
def len.go(fuel: Nat, st: Bzip2Len) -> Bzip2Len:
  match fuel:
    case 0n:
      match st:
        case Bzip2LenGo{r, curr}:
          Bzip2LenBad{r}
        case Bzip2LenDone{r, curr}:
          Bzip2LenDone{r, curr}
        case Bzip2LenBad{r}:
          Bzip2LenBad{r}
    case 1n+f:
      match st:
        case Bzip2LenGo{r, +curr}:
          len.go(f, len.step(len.ok(curr), r, curr))
        case Bzip2LenDone{r, curr}:
          Bzip2LenDone{r, curr}
        case Bzip2LenBad{r}:
          Bzip2LenBad{r}

type Bzip2Lens is Data:
  Bzip2LensGo{r: K.Bzip2Bits, curr: U32, acc: List<&2, U32>}
  Bzip2LensBad{r: K.Bzip2Bits}

def len.fuel(+r: K.Bzip2Bits) -> Nat:
  Nat.add(Nat.mul(8n, K.bits.left(r)), 16n)

def len.next(l: Bzip2Len, acc: List<&2, U32>) -> Bzip2Lens:
  match l:
    case Bzip2LenDone{r, +curr}:
      Bzip2LensGo{r, curr, Con{curr, acc}}
    case Bzip2LenGo{r, curr}:
      Bzip2LensBad{r}
    case Bzip2LenBad{r}:
      Bzip2LensBad{r}

# the lengths of n symbols (reversed)
def len.all(n: Nat, st: Bzip2Lens) -> Bzip2Lens:
  match n:
    case 0n:
      st
    case 1n+p:
      match st:
        case Bzip2LensBad{r}:
          Bzip2LensBad{r}
        case Bzip2LensGo{+r, curr, acc}:
          len.all(p, len.next(len.go(len.fuel(r), Bzip2LenGo{r, curr}), acc))

type Bzip2Tabs is Data:
  Bzip2TabsGo{r: K.Bzip2Bits, acc: List<&2, H.Bzip2Huff>}
  Bzip2TabsBad{r: K.Bzip2Bits}

def tab.fin(l: Bzip2Lens, acc: List<&2, H.Bzip2Huff>) -> Bzip2Tabs:
  match l:
    case Bzip2LensGo{r, curr, ls}:
      Bzip2TabsGo{r, Con{H.huff_tree(L.bz.rev(ls)), acc}}
    case Bzip2LensBad{r}:
      Bzip2TabsBad{r}

def tab.one(g: K.Bzip2Got, +na: Nat, acc: List<&2, H.Bzip2Huff>) -> Bzip2Tabs:
  match g:
    case K.Bzip2Got{r, c}:
      tab.fin(len.all(na, Bzip2LensGo{r, c, Nil{}}), acc)

# ng tables of na symbols each (reversed)
def tab.go(n: Nat, st: Bzip2Tabs, +na: Nat) -> Bzip2Tabs:
  match n:
    case 0n:
      st
    case 1n+p:
      match st:
        case Bzip2TabsBad{r}:
          Bzip2TabsBad{r}
        case Bzip2TabsGo{r, acc}:
          tab.go(p, tab.one(K.bits.read(5n, r), na, acc), na)

def tab.get(m: Maybe<&2, H.Bzip2Huff>) -> H.Bzip2Huff:
  match m:
    case Some{t}:
      t
    case None{}:
      H.Bzip2HufNone{}

# the table of each selector, in order (acc: those so far, reversed)
def tab.pick(sels: List<&2, U32>, +tabs: List<&2, H.Bzip2Huff>, acc: List<&2, H.Bzip2Huff>) -> List<&2, H.Bzip2Huff>:
  match sels:
    case Nil{}:
      List.reverse(&2, H.Bzip2Huff, acc)
    case Con{s, t}:
      tab.pick(t, tabs, Con{tab.get(List.get(&2, H.Bzip2Huff, tabs, U32.to_nat(s))), acc})

# The coded symbols, up to the end of the block

type Bzip2Syms is Data:
  Bzip2SymsGo{r: K.Bzip2Bits, cur: H.Bzip2Huff, left: Nat, tabs: List<&2, H.Bzip2Huff>, acc: List<&2, U32>}
  Bzip2SymsEnd{r: K.Bzip2Bits, acc: List<&2, U32>}
  Bzip2SymsBad{r: K.Bzip2Bits}

def sym.class(end: Bool, bad: Bool, r: K.Bzip2Bits, +v: U32, cur: H.Bzip2Huff, left: Nat, tabs: List<&2, H.Bzip2Huff>, acc: List<&2, U32>) -> Bzip2Syms:
  match end:
    case True{}:
      Bzip2SymsEnd{r, acc}
    case False{}:
      match bad:
        case True{}:
          Bzip2SymsBad{r}
        case False{}:
          Bzip2SymsGo{r, cur, left, tabs, Con{v, acc}}

def sym.got(+eob: U32, g: K.Bzip2Got, +cur: H.Bzip2Huff, left: Nat, tabs: List<&2, H.Bzip2Huff>, acc: List<&2, U32>) -> Bzip2Syms:
  match g:
    case K.Bzip2Got{r, +v}:
      sym.class(U32.is_eq(v, eob), U32.is_eq(v, H.huf.bad()), r, v, cur, left, tabs, acc)

def sym.step(r: K.Bzip2Bits, +cur: H.Bzip2Huff, left: Nat, tabs: List<&2, H.Bzip2Huff>, acc: List<&2, U32>, +eob: U32) -> Bzip2Syms:
  match left:
    case 0n:
      match tabs:
        case Nil{}:
          Bzip2SymsBad{r}
        case Con{+t, rest}:
          sym.got(eob, H.huff_decode(t, r), t, 49n, rest, acc)
    case 1n+l:
      sym.got(eob, H.huff_decode(cur, r), cur, l, tabs, acc)

def sym.go(fuel: Nat, st: Bzip2Syms, +eob: U32) -> Bzip2Syms:
  match fuel:
    case 0n:
      match st:
        case Bzip2SymsGo{r, cur, left, tabs, acc}:
          Bzip2SymsBad{r}
        case Bzip2SymsEnd{r, acc}:
          Bzip2SymsEnd{r, acc}
        case Bzip2SymsBad{r}:
          Bzip2SymsBad{r}
    case 1n+f:
      match st:
        case Bzip2SymsGo{r, +cur, left, tabs, acc}:
          sym.go(f, sym.step(r, cur, left, tabs, acc, eob), eob)
        case Bzip2SymsEnd{r, acc}:
          Bzip2SymsEnd{r, acc}
        case Bzip2SymsBad{r}:
          Bzip2SymsBad{r}

# The stages after the symbols

def blk.rle(m: Maybe<&2, List<&2, U32>>, r: K.Bzip2Bits, crc: U32) -> Bzip2Blk:
  match m:
    case None{}:
      Bzip2BlkBad{E.Bzip2OutputTooLarge{}}
    case Some{acc}:
      Bzip2BlkData{r, crc, L.bz.rev(acc)}

def blk.unbwt(x: Result<&2, &2, E.Bzip2Error, List<&2, U32>>, r: K.Bzip2Bits, crc: U32, room: Nat) -> Bzip2Blk:
  match x:
    case Fail{e}:
      Bzip2BlkBad{e}
    case Done{ys}:
      blk.rle(R.rle1_decode_list(ys, room), r, crc)

def blk.mtf.err(e: E.Bzip2Error) -> E.Bzip2Error:
  match e:
    case E.Bzip2OutputTooLarge{}:
      E.Bzip2BlockTooLarge{}
    case _:
      e

def blk.unmtf(x: Result<&2, &2, E.Bzip2Error, List<&2, U32>>, r: K.Bzip2Bits, crc: U32, +ptr: U32, room: Nat) -> Bzip2Blk:
  match x:
    case Fail{e}:
      Bzip2BlkBad{blk.mtf.err(e)}
    case Done{+ys}:
      blk.unbwt(W.bwt_inverse_list(ys, ptr), r, crc, room)

def blk.syms.end(over: Bool, r: K.Bzip2Bits, x: Result<&2, &2, E.Bzip2Error, List<&2, U32>>, crc: U32, +ptr: U32, room: Nat) -> Bzip2Blk:
  match over:
    case True{}:
      Bzip2BlkBad{E.Bzip2Truncated{}}
    case False{}:
      blk.unmtf(x, r, crc, ptr, room)

def blk.syms(s: Bzip2Syms, +alpha: List<&2, U32>, crc: U32, +ptr: U32, +bmax: Nat, room: Nat) -> Bzip2Blk:
  match s:
    case Bzip2SymsEnd{+r, acc}:
      blk.syms.end(K.bits.over(r), r, M.mtf_decode_list(L.bz.rev(acc), alpha, bmax), crc, ptr, room)
    case Bzip2SymsGo{r, cur, left, tabs, acc}:
      blk.fail(r, E.Bzip2BadHuffmanCode{})
    case Bzip2SymsBad{r}:
      blk.fail(r, E.Bzip2BadHuffmanCode{})

def blk.tabs(t: Bzip2Tabs, +sels: List<&2, U32>, +nsel: Nat, +alpha: List<&2, U32>, +eob: U32, crc: U32, +ptr: U32, +bmax: Nat, room: Nat) -> Bzip2Blk:
  match t:
    case Bzip2TabsBad{r}:
      blk.fail(r, E.Bzip2BadCodeLength{})
    case Bzip2TabsGo{r, acc}:
      blk.syms(sym.go(1n+Nat.mul(nsel, 50n), Bzip2SymsGo{r, H.Bzip2HufNone{}, 0n, tab.pick(sels, List.reverse(&2, H.Bzip2Huff, acc), Nil{}), Nil{}}, eob), alpha, crc, ptr, bmax, room)

def blk.sels(s: Bzip2Sel, +ng: Nat, +nsel: Nat, +alpha: List<&2, U32>, crc: U32, +ptr: U32, +bmax: Nat, room: Nat) -> Bzip2Blk:
  match s:
    case Bzip2SelBad{r}:
      blk.fail(r, E.Bzip2BadSelector{})
    case Bzip2SelGo{r, mtf, acc}:
      +na = {1n+1n+L.bz.len(alpha) : Nat}
      blk.tabs(tab.go(ng, Bzip2TabsGo{r, Nil{}}, na), L.bz.rev(acc), nsel, alpha, U32.from_nat(1n+L.bz.len(alpha)), crc, ptr, bmax, room)

def blk.nsel.ok(ok: Bool, r: K.Bzip2Bits, +ng: Nat, +nsel: Nat, +alpha: List<&2, U32>, crc: U32, +ptr: U32, +bmax: Nat, room: Nat) -> Bzip2Blk:
  match ok:
    case True{}:
      blk.sels(sel.go(nsel, Bzip2SelGo{r, sel.iota(ng, 0), Nil{}}, ng), ng, nsel, alpha, crc, ptr, bmax, room)
    case False{}:
      blk.fail(r, E.Bzip2BadSelectorCount{})

def blk.nsel(g: K.Bzip2Got, +ng: Nat, +alpha: List<&2, U32>, crc: U32, +ptr: U32, +bmax: Nat, room: Nat) -> Bzip2Blk:
  match g:
    case K.Bzip2Got{r, +n}:
      blk.nsel.ok(U32.is_ne(n, 0), r, ng, U32.to_nat(n), alpha, crc, ptr, bmax, room)

def blk.ng.ok(ok: Bool, r: K.Bzip2Bits, +ng: Nat, +alpha: List<&2, U32>, crc: U32, +ptr: U32, +bmax: Nat, room: Nat) -> Bzip2Blk:
  match ok:
    case True{}:
      blk.nsel(K.bits.read(15n, r), ng, alpha, crc, ptr, bmax, room)
    case False{}:
      blk.fail(r, E.Bzip2BadTableCount{})

def blk.ng(g: K.Bzip2Got, +alpha: List<&2, U32>, crc: U32, +ptr: U32, +bmax: Nat, room: Nat) -> Bzip2Blk:
  match g:
    case K.Bzip2Got{r, +n}:
      blk.ng.ok(Bool.and(U32.is_le(2, n), U32.is_le(n, 6)), r, U32.to_nat(n), alpha, crc, ptr, bmax, room)

def blk.map.ok(ok: Bool, r: K.Bzip2Bits, +alpha: List<&2, U32>, crc: U32, +ptr: U32, +bmax: Nat, room: Nat) -> Bzip2Blk:
  match ok:
    case True{}:
      blk.ng(K.bits.read(3n, r), alpha, crc, ptr, bmax, room)
    case False{}:
      blk.fail(r, E.Bzip2BadSymbolMap{})

def blk.map(m: Bzip2Map, crc: U32, +ptr: U32, +bmax: Nat, room: Nat) -> Bzip2Blk:
  match m:
    case Bzip2Map{r, acc}:
      +alpha = L.bz.rev(acc)
      blk.map.ok(Bool.not(List.is_empty(&2, U32, alpha)), r, alpha, crc, ptr, bmax, room)

def blk.groups(g: K.Bzip2Got, crc: U32, +ptr: U32, +bmax: Nat, room: Nat) -> Bzip2Blk:
  match g:
    case K.Bzip2Got{r, +w}:
      blk.map(map.go(16n, Bzip2Map{r, Nil{}}, w, 32768, 0), crc, ptr, bmax, room)

def blk.ptr(g: K.Bzip2Got, crc: U32, +bmax: Nat, room: Nat) -> Bzip2Blk:
  match g:
    case K.Bzip2Got{r, +ptr}:
      blk.groups(K.bits.read(16n, r), crc, ptr, bmax, room)

def blk.rand(f: K.Bzip2Flag, crc: U32, +bmax: Nat, room: Nat) -> Bzip2Blk:
  match f:
    case K.Bzip2Flag{r, b}:
      match b:
        case True{}:
          blk.fail(r, E.Bzip2Randomised{})
        case False{}:
          blk.ptr(K.bits.read(24n, r), crc, bmax, room)

def blk.head.crc(g: K.Bzip2Got, +bmax: Nat, room: Nat) -> Bzip2Blk:
  match g:
    case K.Bzip2Got{r, crc}:
      blk.rand(K.bits.flag(r), crc, bmax, room)

def blk.end.check(over: Bool, r: K.Bzip2Bits, crc: U32) -> Bzip2Blk:
  match over:
    case True{}:
      Bzip2BlkBad{E.Bzip2Truncated{}}
    case False{}:
      Bzip2BlkEnd{r, crc}

def blk.end.crc(g: K.Bzip2Got) -> Bzip2Blk:
  match g:
    case K.Bzip2Got{+r, crc}:
      blk.end.check(K.bits.over(r), r, crc)

def blk.magic.pick(isblk: Bool, isend: Bool, r: K.Bzip2Bits, +bmax: Nat, room: Nat) -> Bzip2Blk:
  match isblk:
    case True{}:
      blk.head.crc(K.bits.read(32n, r), bmax, room)
    case False{}:
      match isend:
        case True{}:
          blk.end.crc(K.bits.read(32n, r))
        case False{}:
          blk.fail(r, E.Bzip2BadBlockMagic{})

def blk.magic.lo(g: K.Bzip2Got, +hi: U32, +bmax: Nat, room: Nat) -> Bzip2Blk:
  match g:
    case K.Bzip2Got{r, +lo}:
      blk.magic.pick(Bool.and(U32.is_eq(hi, 3227993), U32.is_eq(lo, 2511705)), Bool.and(U32.is_eq(hi, 1536581), U32.is_eq(lo, 3690640)), r, bmax, room)

def blk.magic.hi(g: K.Bzip2Got, +bmax: Nat, room: Nat) -> Bzip2Blk:
  match g:
    case K.Bzip2Got{r, hi}:
      blk.magic.lo(K.bits.read(24n, r), hi, bmax, room)

# the next block of a stream (or its end) from r; bmax: the stream's block
# size (the most bytes a block's BWT may hold); room: how many more bytes the
# output may take
def block_read(r: K.Bzip2Bits, +bmax: Nat, room: Nat) -> Bzip2Blk:
  blk.magic.hi(K.bits.read(24n, r), bmax, room)
