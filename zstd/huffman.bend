# bend-osdev-zstd, Huffman coding (RFC 8878, section 4.2): weights, tree
# descriptions, prefix codes, decoding and encoding.
#
# Usable on its own. ZstdHuf.of_weights builds the code from the weights of
# symbols 0 to n - 1 (the weight of symbol n is implied: the one that
# completes the code), as RFC 8878 assigns codes: a symbol of weight w has a
# code of maxbits + 1 - w bits, and codes are given out by weight, lowest
# first, then by symbol. A code is a binary tree (ZstdHufTable): decoding
# walks it bit by bit (bits.bend's bit strings, in reading order) to a leaf.
import Base
import ../bytes/bytes.bend as B
import ./bits.bend as Bi
import ./fse.bend as F

# a prefix code: a tree whose leaves are symbols
type ZsHufTree is Data:
  ZsHufNone{}
  ZsHufLeaf{sym: Nat}
  ZsHufNode{zero: ZsHufTree, one: ZsHufTree}

# each symbol's code (bits), by symbol, for the encoder
type ZsHufCodes is Data:
  ZsHufCNone{}
  ZsHufCLeaf{bits: List<&2, Bool>}
  ZsHufCNode{lo: ZsHufCodes, hi: ZsHufCodes}

# a code: the decoding tree, the codes by symbol, the longest code's length
type ZstdHufTable is Data:
  ZstdHufTable{tree: ZsHufTree, codes: ZsHufCodes, maxbits: Nat}

# a tree description read: the code, and its size in bytes
type ZstdHufRead is Data:
  ZstdHufRead{table: ZstdHufTable, used: Nat}

# The tree

def huf.zero(t: ZsHufTree) -> ZsHufTree:
  match t:
    case ZsHufNode{z, o}:
      z
    case _:
      ZsHufNone{}

def huf.one(t: ZsHufTree) -> ZsHufTree:
  match t:
    case ZsHufNode{z, o}:
      o
    case _:
      ZsHufNone{}

# t with the leaf sym at the end of path
def huf.insert(path: List<&2, Bool>, +t: ZsHufTree, +sym: Nat) -> ZsHufTree:
  match path:
    case Nil{}:
      ZsHufLeaf{sym}
    case Con{b, rest}:
      match b:
        case True{}:
          ZsHufNode{huf.zero(t), huf.insert(rest, huf.one(t), sym)}
        case False{}:
          ZsHufNode{huf.insert(rest, huf.zero(t), sym), huf.one(t)}

# the symbol at the start of bits, and the bits after its code
def ZstdHuf.walk(t: ZsHufTree, bits: List<&2, Bool>) -> Maybe<&2, Bi.ZstdBits>:
  match t:
    case ZsHufNone{}:
      None{}
    case ZsHufLeaf{sym}:
      Some{Bi.ZstdBits{sym, bits}}
    case ZsHufNode{z, o}:
      match bits:
        case Nil{}:
          None{}
        case Con{b, rest}:
          match b:
            case True{}:
              ZstdHuf.walk(o, rest)
            case False{}:
              ZstdHuf.walk(z, rest)

# The codes by symbol: a trie over 8 bits, most significant first

def huf.c.lo(t: ZsHufCodes) -> ZsHufCodes:
  match t:
    case ZsHufCNode{lo, hi}:
      lo
    case _:
      ZsHufCNone{}

def huf.c.hi(t: ZsHufCodes) -> ZsHufCodes:
  match t:
    case ZsHufCNode{lo, hi}:
      hi
    case _:
      ZsHufCNone{}

def huf.c.set(k: Nat, low: Bool, +half: Nat, +s: Nat, +t: ZsHufCodes, +v: List<&2, Bool>) -> ZsHufCodes:
  match k:
    case 0n:
      ZsHufCLeaf{v}
    case 1n+p:
      match low:
        case True{}:
          +h = Nat.div(half, 2n)
          ZsHufCNode{huf.c.set(p, Nat.is_lt(s, h), h, s, huf.c.lo(t), v), huf.c.hi(t)}
        case False{}:
          +h = Nat.div(half, 2n)
          +s2 = Nat.sub(s, half)
          ZsHufCNode{huf.c.lo(t), huf.c.set(p, Nat.is_lt(s2, h), h, s2, huf.c.hi(t), v)}

def huf.c.get(k: Nat, t: ZsHufCodes, low: Bool, +half: Nat, +s: Nat) -> Maybe<&2, List<&2, Bool>>:
  match k:
    case 0n:
      match t:
        case ZsHufCLeaf{v}:
          Some{v}
        case _:
          None{}
    case 1n+p:
      match t:
        case ZsHufCNode{lo, hi}:
          match low:
            case True{}:
              +h = Nat.div(half, 2n)
              huf.c.get(p, lo, Nat.is_lt(s, h), h, s)
            case False{}:
              +h = Nat.div(half, 2n)
              +s2 = Nat.sub(s, half)
              huf.c.get(p, hi, Nat.is_lt(s2, h), h, s2)
        case _:
          None{}

def huf.c.put(+s: Nat, +t: ZsHufCodes, +v: List<&2, Bool>) -> ZsHufCodes:
  huf.c.set(8n, Nat.is_lt(s, 128n), 128n, s, t, v)

# the code of symbol s
def ZstdHuf.code(t: ZstdHufTable, +s: Nat) -> Maybe<&2, List<&2, Bool>>:
  match t:
    case ZstdHufTable{tree, codes, maxbits}:
      huf.c.get(8n, codes, Nat.is_lt(s, 128n), 128n, s)

# Codes from weights (RFC 8878, section 4.2.1)

def huf.total.add(ok: Bool, w: Nat, +a: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      match w:
        case 0n:
          Some{a}
        case 1n+p:
          Some{Nat.add(a, Bi.ZstdBits.pow2(p))}
    case False{}:
      None{}

# the weights' total, sum of 2^(w - 1) over w > 0, if every w is at most 11
def huf.total(ws: List<&2, Nat>, acc: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match ws:
    case Nil{}:
      acc
    case Con{+w, rest}:
      match acc:
        case None{}:
          None{}
        case Some{a}:
          huf.total(rest, huf.total.add(Nat.is_le(w, 11n), w, a))

# a symbol and its code
type ZsHufSym is Data:
  ZsHufSym{sym: Nat, bits: List<&2, Bool>}

# the next code's first index (in a table of 2^maxbits), and the codes so far
type ZsHufAsg is Data:
  ZsHufAsg{start: Nat, acc: List<&2, ZsHufSym>}

def huf.add_code(hit: Bool, +sym: Nat, +w: Nat, +maxbits: Nat, +start: Nat, acc: List<&2, ZsHufSym>) -> List<&2, ZsHufSym>:
  match hit:
    case True{}:
      +nb = Nat.sub(Nat.add(maxbits, 1n), w)
      Con{ZsHufSym{sym, Bi.ZstdBits.of_nat(nb, Nat.div(start, Bi.ZstdBits.pow2(Nat.sub(w, 1n))))}, acc}
    case False{}:
      acc

def huf.next_start(hit: Bool, +start: Nat, +w: Nat) -> Nat:
  match hit:
    case True{}:
      Nat.add(start, Bi.ZstdBits.pow2(Nat.sub(w, 1n)))
    case False{}:
      start

# the codes of the symbols of weight w, in symbol order
def huf.assign.w(ws: List<&2, Nat>, +sym: Nat, +w: Nat, +maxbits: Nat, +start: Nat, acc: List<&2, ZsHufSym>) -> ZsHufAsg:
  match ws:
    case Nil{}:
      ZsHufAsg{start, acc}
    case Con{+x, rest}:
      +hit = Nat.is_eq(x, w)
      huf.assign.w(rest, 1n+sym, w, maxbits, huf.next_start(hit, start, w), huf.add_code(hit, sym, w, maxbits, start, acc))

# weights 1 to maxbits, lowest first
def huf.assign(fuel: Nat, +w: Nat, +ws: List<&2, Nat>, +maxbits: Nat, asg: ZsHufAsg) -> List<&2, ZsHufSym>:
  match fuel:
    case 0n:
      match asg:
        case ZsHufAsg{start, acc}:
          acc
    case 1n+f:
      match asg:
        case ZsHufAsg{start, acc}:
          huf.assign(f, 1n+w, ws, maxbits, huf.assign.w(ws, 0n, w, maxbits, start, acc))

def huf.tree_of(cs: List<&2, ZsHufSym>, t: ZsHufTree, c: ZsHufCodes) -> ZstdHufTable:
  match cs:
    case Nil{}:
      ZstdHufTable{t, c, 0n}
    case Con{ZsHufSym{+sym, +bits}, rest}:
      huf.tree_of(rest, huf.insert(bits, t, sym), huf.c.put(sym, c, bits))

def huf.with_max(t: ZstdHufTable, +maxbits: Nat) -> ZstdHufTable:
  match t:
    case ZstdHufTable{tree, codes, m}:
      ZstdHufTable{tree, codes, maxbits}

# the code of these weights (all of them, the last included)
def ZstdHuf.of_all_weights(+ws: List<&2, Nat>, +maxbits: Nat) -> ZstdHufTable:
  huf.with_max(huf.tree_of(huf.assign(maxbits, 1n, ws, maxbits, ZsHufAsg{0n, Nil{}}), ZsHufNone{}, ZsHufCNone{}), maxbits)

def huf.ow.rest(pow: Bool, +ws: List<&2, Nat>, +maxbits: Nat, +rest: Nat) -> Maybe<&2, ZstdHufTable>:
  match pow:
    case True{}:
      Some{ZstdHuf.of_all_weights(List.append(&2, Nat, ws, [Nat.add(F.ZstdFse.highbit(rest), 1n)]), maxbits)}
    case False{}:
      None{}

def huf.ow.max(ok: Bool, +ws: List<&2, Nat>, +maxbits: Nat, +total: Nat) -> Maybe<&2, ZstdHufTable>:
  match ok:
    case True{}:
      +rest = Nat.sub(Bi.ZstdBits.pow2(maxbits), total)
      huf.ow.rest(Nat.is_eq(Bi.ZstdBits.pow2(F.ZstdFse.highbit(rest)), rest), ws, maxbits, rest)
    case False{}:
      None{}

def huf.ow.total(m: Maybe<&2, Nat>, +ws: List<&2, Nat>) -> Maybe<&2, ZstdHufTable>:
  match m:
    case None{}:
      None{}
    case Some{+total}:
      match total:
        case 0n:
          None{}
        case 1n+p:
          +maxbits = Nat.add(F.ZstdFse.highbit(total), 1n)
          huf.ow.max(Nat.is_le(maxbits, 11n), ws, maxbits, total)

# The public interface: codes

# the code of the weights of symbols 0 to n - 1, the weight of symbol n
# implied; None if a weight passes 11, the weights are all 0, the longest
# code would pass 11 bits, or no weight completes the code
def ZstdHuf.of_weights(+ws: List<&2, Nat>) -> Maybe<&2, ZstdHufTable>:
  huf.ow.total(huf.total(ws, Some{0n}), ws)

def ZstdHuf.tree(t: ZstdHufTable) -> ZsHufTree:
  match t:
    case ZstdHufTable{tree, codes, maxbits}:
      tree

# Decoding

type ZsHufDec is Data:
  ZsHufGo{bits: List<&2, Bool>, acc: List<&2, Nat>}
  ZsHufBad{}

def huf.push(w: Maybe<&2, Bi.ZstdBits>, acc: List<&2, Nat>) -> ZsHufDec:
  match w:
    case None{}:
      ZsHufBad{}
    case Some{Bi.ZstdBits{sym, rest}}:
      ZsHufGo{rest, Con{sym, acc}}

def huf.dec(n: Nat, +t: ZsHufTree, st: ZsHufDec) -> ZsHufDec:
  match n:
    case 0n:
      st
    case 1n+k:
      match st:
        case ZsHufGo{bits, acc}:
          huf.dec(k, t, huf.push(ZstdHuf.walk(t, bits), acc))
        case ZsHufBad{}:
          ZsHufBad{}

# symbols decoded, and the bits after them
type ZstdHufSyms is Data:
  ZstdHufSyms{syms: List<&2, Nat>, rest: List<&2, Bool>}

def huf.dec.out(st: ZsHufDec) -> Maybe<&2, ZstdHufSyms>:
  match st:
    case ZsHufGo{bits, acc}:
      Some{ZstdHufSyms{List.reverse(&2, Nat, acc), bits}}
    case ZsHufBad{}:
      None{}

# n symbols from the start of bits, and the bits after them; None if bits
# run out inside a code
def ZstdHuf.decode(t: ZstdHufTable, bits: List<&2, Bool>, n: Nat) -> Maybe<&2, ZstdHufSyms>:
  huf.dec.out(huf.dec(n, ZstdHuf.tree(t), ZsHufGo{bits, Nil{}}))

def huf.exact(m: Maybe<&2, ZstdHufSyms>) -> Maybe<&2, List<&2, Nat>>:
  match m:
    case None{}:
      None{}
    case Some{ZstdHufSyms{syms, rest}}:
      match rest:
        case Nil{}:
          Some{syms}
        case Con{b, r}:
          None{}

def huf.stream(m: Maybe<&2, List<&2, Bool>>, t: ZstdHufTable, n: Nat) -> Maybe<&2, List<&2, Nat>>:
  match m:
    case None{}:
      None{}
    case Some{bits}:
      huf.exact(ZstdHuf.decode(t, bits, n))

# the n symbols of a Huffman-coded stream (a backward bitstream, xs its
# bytes), which they must use up exactly
def ZstdHuf.decode_stream(t: ZstdHufTable, xs: List<&2, U32>, n: Nat) -> Maybe<&2, List<&2, Nat>>:
  huf.stream(Bi.ZstdBits.backward(xs), t, n)

# Tree descriptions (RFC 8878, section 4.2.1.1)
#
# A header byte h. From 128 up, the weights of h - 127 symbols follow, 4 bits
# each, two to a byte, the first in the high half. Below 128, h bytes follow:
# an FSE table description (accuracy log at most 6) and a backward bitstream
# that two interleaved states decode: state 1 gives a weight, then state 2,
# and so on, each updated after its weight; when an update would need more
# bits than are left, the other state gives the last weight.

def huf.nibbles(xs: List<&2, U32>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      List.reverse(&2, Nat, acc)
    case Con{h, rest}:
      +b = B.byte(h)
      huf.nibbles(rest, Con{U32.to_nat(U32.and(b, 15)), Con{U32.to_nat(U32.shrn(b, 4n)), acc}})

type ZsHufW is Data:
  ZsHufWGo{sa: Nat, sb: Nat, bits: List<&2, Bool>, left: Nat, acc: List<&2, Nat>, count: Nat}
  ZsHufWDone{acc: List<&2, Nat>}
  ZsHufWBad{}

def huf.w.next(r: Maybe<&2, Bi.ZstdBits>, +sb: Nat, +left: Nat, +nb: Nat, acc: List<&2, Nat>, +count: Nat) -> ZsHufW:
  match r:
    case None{}:
      ZsHufWBad{}
    case Some{Bi.ZstdBits{sa2, bits}}:
      ZsHufWGo{sb, sa2, bits, Nat.sub(left, nb), acc, count}

def huf.w.last(full: Bool, +t: F.ZstdFseTable, +sb: Nat, acc: List<&2, Nat>) -> ZsHufW:
  match full:
    case True{}:
      ZsHufWBad{}
    case False{}:
      ZsHufWDone{Con{F.ZstdFse.sym(F.ZstdFse.entry(t, sb)), acc}}

def huf.w.emit(over: Bool, +sym: Nat, e: F.ZstdFseEntry, +nb: Nat, +t: F.ZstdFseTable, +sb: Nat, bits: List<&2, Bool>, +left: Nat, acc: List<&2, Nat>, +count: Nat) -> ZsHufW:
  match over:
    case True{}:
      huf.w.last(Nat.is_le(255n, 1n+count), t, sb, Con{sym, acc})
    case False{}:
      huf.w.next(F.ZstdFse.next(e, bits), sb, left, nb, Con{sym, acc}, 1n+count)

def huf.w.step(full: Bool, +t: F.ZstdFseTable, +sa: Nat, +sb: Nat, bits: List<&2, Bool>, +left: Nat, acc: List<&2, Nat>, +count: Nat) -> ZsHufW:
  match full:
    case True{}:
      ZsHufWBad{}
    case False{}:
      +e = F.ZstdFse.entry(t, sa)
      +nb = F.ZstdFse.nb(e)
      huf.w.emit(Nat.is_lt(left, nb), F.ZstdFse.sym(e), e, nb, t, sb, bits, left, acc, count)

def huf.w.loop(fuel: Nat, +t: F.ZstdFseTable, st: ZsHufW) -> ZsHufW:
  match fuel:
    case 0n:
      ZsHufWBad{}
    case 1n+f:
      match st:
        case ZsHufWGo{sa, sb, bits, left, acc, +count}:
          huf.w.loop(f, t, huf.w.step(Nat.is_le(255n, count), t, sa, sb, bits, left, acc, count))
        case ZsHufWDone{acc}:
          ZsHufWDone{acc}
        case ZsHufWBad{}:
          ZsHufWBad{}

def huf.w.out(st: ZsHufW) -> Maybe<&2, List<&2, Nat>>:
  match st:
    case ZsHufWDone{acc}:
      Some{List.reverse(&2, Nat, acc)}
    case _:
      None{}

def huf.w.init2(r: Maybe<&2, Bi.ZstdBits>, +t: F.ZstdFseTable, +s1: Nat) -> Maybe<&2, List<&2, Nat>>:
  match r:
    case None{}:
      None{}
    case Some{Bi.ZstdBits{s2, +bits}}:
      huf.w.out(huf.w.loop(300n, t, ZsHufWGo{s1, s2, bits, Bi.ZstdBits.len(bits), Nil{}, 0n}))

def huf.w.init1(r: Maybe<&2, Bi.ZstdBits>, +t: F.ZstdFseTable) -> Maybe<&2, List<&2, Nat>>:
  match r:
    case None{}:
      None{}
    case Some{Bi.ZstdBits{s1, bits}}:
      huf.w.init2(Bi.ZstdBits.read(F.ZstdFse.al(t), bits), t, s1)

def huf.w.bits(m: Maybe<&2, List<&2, Bool>>, +t: F.ZstdFseTable) -> Maybe<&2, List<&2, Nat>>:
  match m:
    case None{}:
      None{}
    case Some{bits}:
      huf.w.init1(Bi.ZstdBits.read(F.ZstdFse.al(t), bits), t)

def huf.w.table(m: Maybe<&2, F.ZstdFseTable>, +stream: List<&2, U32>) -> Maybe<&2, List<&2, Nat>>:
  match m:
    case None{}:
      None{}
    case Some{+t}:
      huf.w.bits(Bi.ZstdBits.backward(stream), t)

def huf.w.desc(m: Maybe<&2, F.ZstdFseDesc>, body: List<&2, U32>) -> Maybe<&2, List<&2, Nat>>:
  match m:
    case None{}:
      None{}
    case Some{F.ZstdFseDesc{+al, probs, +used}}:
      huf.w.table(F.ZstdFse.table(al, probs), B.drop(used, body))

# the weights an FSE-coded description's body (h bytes) gives
def ZstdHuf.fse_weights(+body: List<&2, U32>) -> Maybe<&2, List<&2, Nat>>:
  huf.w.desc(F.ZstdFse.read_description(body, 6n, 255n), body)

def huf.rd.table(m: Maybe<&2, ZstdHufTable>, +used: Nat) -> Maybe<&2, ZstdHufRead>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Some{ZstdHufRead{t, used}}

def huf.rd.of(m: Maybe<&2, List<&2, Nat>>, +used: Nat) -> Maybe<&2, ZstdHufRead>:
  match m:
    case None{}:
      None{}
    case Some{+ws}:
      huf.rd.table(ZstdHuf.of_weights(ws), used)

def huf.rd.direct(ok: Bool, +n: Nat, +nbytes: Nat, rest: List<&2, U32>) -> Maybe<&2, ZstdHufRead>:
  match ok:
    case True{}:
      huf.rd.of(Some{List.take(&2, Nat, huf.nibbles(B.take(nbytes, rest), Nil{}), n)}, 1n+nbytes)
    case False{}:
      None{}

def huf.rd.fse(ok: Bool, +h: Nat, rest: List<&2, U32>) -> Maybe<&2, ZstdHufRead>:
  match ok:
    case True{}:
      huf.rd.of(ZstdHuf.fse_weights(B.take(h, rest)), 1n+h)
    case False{}:
      None{}

def huf.rd.head(big: Bool, +h: Nat, +rest: List<&2, U32>) -> Maybe<&2, ZstdHufRead>:
  match big:
    case True{}:
      +n = Nat.sub(h, 127n)
      +nbytes = Nat.div(Nat.add(n, 1n), 2n)
      huf.rd.direct(Nat.is_le(nbytes, B.len.fast(rest)), n, nbytes, rest)
    case False{}:
      huf.rd.fse(Nat.is_le(h, B.len.fast(rest)), h, rest)

# the tree description at the start of xs: the code, and the description's
# size in bytes; None if it is malformed or cut short
def ZstdHuf.read_tree(xs: List<&2, U32>) -> Maybe<&2, ZstdHufRead>:
  match xs:
    case Nil{}:
      None{}
    case Con{h, rest}:
      +hv = U32.to_nat(B.byte(h))
      huf.rd.head(Nat.is_le(128n, hv), hv, rest)

# Encoding: a symbol's code, from the code table by symbol, checked against
# the tree (walking it along the code must end exactly at the symbol's
# leaf), so what the encoder writes decodes back whatever the table holds
# (LAWS.bend)

def huf.enc.ok(w: Maybe<&2, Bi.ZstdBits>, +x: Nat) -> Bool:
  match w:
    case None{}:
      False{}
    case Some{Bi.ZstdBits{y, rest}}:
      match rest:
        case Nil{}:
          Nat.is_eq(y, x)
        case Con{b, r}:
          False{}

def huf.enc.code(ok: Bool, p: List<&2, Bool>) -> Maybe<&2, List<&2, Bool>>:
  match ok:
    case True{}:
      Some{p}
    case False{}:
      None{}

# the checked code of x
def huf.enc.sym(m: Maybe<&2, List<&2, Bool>>, +tree: ZsHufTree, +x: Nat) -> Maybe<&2, List<&2, Bool>>:
  match m:
    case None{}:
      None{}
    case Some{+p}:
      huf.enc.code(huf.enc.ok(ZstdHuf.walk(tree, p), x), p)

def huf.cons(p: Maybe<&2, List<&2, Bool>>, r: Maybe<&2, List<&2, Bool>>) -> Maybe<&2, List<&2, Bool>>:
  match p:
    case None{}:
      None{}
    case Some{a}:
      match r:
        case None{}:
          None{}
        case Some{b}:
          Some{List.append(&2, Bool, a, b)}

# the bits ZstdHuf.decode reads the symbols xs from (each symbol's code, in
# order); None if a symbol has no code
def ZstdHuf.encode(+t: ZstdHufTable, xs: List<&2, Nat>) -> Maybe<&2, List<&2, Bool>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case Con{+x, rest}:
      huf.cons(huf.enc.sym(ZstdHuf.code(t, x), ZstdHuf.tree(t), x), ZstdHuf.encode(t, rest))
