# bend-osdev-deflate: the inflater (RFC 1951): stored, fixed and dynamic
# blocks, with a 32 KB window, one-shot and streaming.
#
# The inflater is a state machine fed one byte at a time, so a stream can
# arrive in pieces of any size: a byte of a stored block is copied whole; any
# other byte is split into its eight bits (bits.bend) and each bit moves the
# machine on: a field gathers its bits, low bit first; a Huffman code walks
# its tree (huffman.bend) one bit per step. The state says what the next bit
# or byte is for.
#
# Each byte's output (literals, and the bytes a match copies out of the
# window) goes to a driver, which keeps the output so far and the room left
# under the caller's maximum, and stops with DeflateOutputTooLarge the moment
# the output would pass it. The machine itself never sees the maximum.
#
# What is refused (RFC 1951 where it says so; where it does not, the choice
# zlib 1.3 makes, found by experiment with Python's zlib module, as a black
# box; ref/gen.py holds the cases):
# * a block type of 11 ("reserved (error)", 3.2.3);
# * a stored block whose NLEN is not the one's complement of LEN (3.2.4);
# * HLIT above 29 (more than 286 literal/length codes) or HDIST above 29
#   (more than 30 distance codes): 3.2.6, "Literal/length values 286-287
#   will never actually occur in the compressed data", "distance codes
#   30-31 will never actually occur"; zlib refuses both;
# * a code length code that is over-subscribed or incomplete;
# * code 16 first ("copy the previous code length", with none before), or a
#   repeat past the HLIT + 257 + HDIST + 1 lengths (3.2.7: "all code lengths
#   form a single sequence");
# * a literal/length code with no code for 256 (every block ends with it,
#   3.2.5), or one that is over-subscribed, or incomplete other than a
#   single code of one bit;
# * a distance code that is over-subscribed, or incomplete other than a
#   single code of one bit (3.2.7: "If only one distance code is used, it is
#   encoded using one bit, not zero bits"); no distance codes at all is
#   allowed ("the data is all literals");
# * bits that match no code, literal/length symbols 286 and 287 and distance
#   symbols 30 and 31 (3.2.6);
# * a distance past the start of the output (and dictionary): 3.2.3, "a
#   distance cannot refer past the beginning of the output stream" (and
#   "the referenced string may overlap the current position": a copy may
#   read what it writes);
# * an input that ends inside the stream.
# Bytes after the final block are not part of the stream: they are handed
# back (the zlib and gzip trailers live there), and ignored or refused as
# the options say.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./bits.bend as K
import ./huffman.bend as H
import ./window.bend as W
import ./eq.bend as Q
import ./codes.bend as C
import ./fixed.bend as X

# The machine's states

# a block's codes
type DflCodes is Data:
  DflCodes{lit: H.DflTree, dist: H.DflTree}

# a dynamic block's header, while the code length code lengths are read:
# left of HCLEN + 4 still to read, the positions (3.2.7's order) they go to,
# the 19 lengths so far
type DflHdr is Data:
  DflHdr{final: Bool, hlit: Nat, hdist: Nat, left: Nat, order: List<&2, Nat>, clens: List<&2, U32>}

# then while the HLIT + 257 + HDIST + 1 code lengths are read: left still to
# read, those read (reversed: the previous one first), the code length code
type DflLens is Data:
  DflLens{final: Bool, hlit: Nat, hdist: Nat, left: Nat, lens: List<&2, U32>, ct: H.DflTree}

# what a field is for
type DflK is Data:
  DflKHead{}
  DflKHlit{final: Bool}
  DflKHdist{final: Bool, hlit: Nat}
  DflKHclen{final: Bool, hlit: Nat, hdist: Nat}
  DflKClen{h: DflHdr}
  DflKRep{l: DflLens, sym: U32}
  DflKLen{final: Bool, codes: DflCodes, sym: U32}
  DflKDist{final: Bool, codes: DflCodes, len: Nat, sym: U32}

# what a Huffman symbol is for
type DflKs is Data:
  DflKsLens{l: DflLens}
  DflKsLit{final: Bool, codes: DflCodes}
  DflKsDist{final: Bool, codes: DflCodes, len: Nat}

type DflSt is Data:
  # a field of left more bits (left at least 1), sh read so far into v
  DflField{left: Nat, sh: Nat, v: U32, k: DflK}
  # a Huffman code, at this node of its tree
  DflSym{node: H.DflTree, k: DflKs}
  # a stored block's header bits are read: the rest of this byte is skipped
  DflAlign{final: Bool}
  # LEN and NLEN, n of their 4 bytes read into v
  DflStoredLen{n: Nat, v: U32, final: Bool}
  # a stored block's bytes, left of them still to copy (at least 1)
  DflStored{left: Nat, final: Bool}
  # after the final block: the bytes after it (reversed)
  DflEnd{rest: List<&2, U32>}
  DflBad{e: E.DeflateError}

# the state, the window, the bytes put out for the current input byte
# (reversed)
type DflCore is Data:
  DflCore{st: DflSt, win: W.DflWin, em: List<&2, U32>}

def inf.bad(e: E.DeflateError, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  DflCore{DflBad{e}, win, em}

# a field of n bits (0 bits: done at once, with the value 0)
def inf.field(n: Nat, k: DflK) -> DflSt:
  DflField{n, 0n, 0, k}

def inf.head() -> DflSt:
  inf.field(3n, DflKHead{})

# Output

def inf.lit.st(final: Bool, codes: DflCodes) -> DflSt:
  match codes:
    case DflCodes{+lit, dist}:
      DflSym{lit, DflKsLit{final, DflCodes{lit, dist}}}

# n bytes, each the one d back (the copy may overlap what it writes); the
# state is set by inf.copy.fin
def inf.copy.go(n: Nat, +d: U32, +win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match n:
    case 0n:
      DflCore{DflEnd{Nil{}}, win, em}
    case 1n+p:
      +v = W.win.get(win, d)
      inf.copy.go(p, d, W.win.put(win, v), Con{v, em})

def inf.copy.fin(c: DflCore, +final: Bool, codes: DflCodes) -> DflCore:
  match c:
    case DflCore{st, win, em}:
      DflCore{inf.lit.st(final, codes), win, em}

def inf.copy.ok(ok: Bool, +n: Nat, +d: U32, +final: Bool, codes: DflCodes, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match ok:
    case True{}:
      inf.copy.fin(inf.copy.go(n, d, win, em), final, codes)
    case False{}:
      inf.bad(E.DeflateDistanceTooFar{}, win, em)

# a match: n bytes from d back, if d does not reach past the start
def inf.copy(+n: Nat, +d: U32, +final: Bool, codes: DflCodes, +win: W.DflWin, em: List<&2, U32>) -> DflCore:
  inf.copy.ok(U32.is_le(d, W.win.count(win)), n, d, final, codes, win, em)

# Dynamic headers (3.2.7)

# where the code length code lengths go, in the order they come
def inf.order() -> List<&2, Nat>:
  [16n, 17n, 18n, 0n, 8n, 7n, 9n, 6n, 10n, 5n, 11n, 4n, 12n, 3n, 13n, 2n, 14n, 1n, 15n]

def inf.zeros(n: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      inf.zeros(p, Con{0, acc})

def inf.lset(xs: List<&2, U32>, i: Nat, +v: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match i:
        case 0n:
          Con{v, t}
        case 1n+p:
          Con{h, inf.lset(t, p, v)}

def inf.lget(xs: List<&2, U32>, i: Nat) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      match i:
        case 0n:
          h
        case 1n+p:
          inf.lget(t, p)

# the code length code is complete, or refused
def inf.clen.ok(k: H.DflKraft) -> Bool:
  match k:
    case H.DflKraftComplete{}:
      True{}
    case _:
      False{}

# a literal/length or distance code: complete or a single one-bit code;
# empty only where allowed (distances)
def inf.code.ok(k: H.DflKraft, empty: Bool) -> Bool:
  match k:
    case H.DflKraftComplete{}:
      True{}
    case H.DflKraftSingle{}:
      True{}
    case H.DflKraftEmpty{}:
      empty
    case H.DflKraftIncomplete{}:
      False{}
    case H.DflKraftOver{}:
      False{}

def inf.lens.dist(ok: Bool, +final: Bool, lit: H.DflTree, +dl: List<&2, U32>, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match ok:
    case True{}:
      DflCore{inf.lit.st(final, DflCodes{lit, H.huff_tree(dl)}), win, em}
    case False{}:
      inf.bad(E.DeflateBadDistCode{}, win, em)

def inf.lens.lit(ok: Bool, +final: Bool, +ll: List<&2, U32>, +dl: List<&2, U32>, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match ok:
    case True{}:
      inf.lens.dist(inf.code.ok(H.huff_kraft(dl), True{}), final, H.huff_tree(ll), dl, win, em)
    case False{}:
      inf.bad(E.DeflateBadLitLenCode{}, win, em)

def inf.lens.end(has: Bool, +final: Bool, +ll: List<&2, U32>, +dl: List<&2, U32>, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match has:
    case True{}:
      inf.lens.lit(inf.code.ok(H.huff_kraft(ll), False{}), final, ll, dl, win, em)
    case False{}:
      inf.bad(E.DeflateNoEndCode{}, win, em)

# all the code lengths are read: the block's codes, checked
def inf.lens.done(+final: Bool, +hlit: Nat, lens: List<&2, U32>, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  +all = List.reverse(&2, U32, lens)
  +ll = List.take(&2, U32, all, hlit)
  inf.lens.end(U32.is_ne(inf.lget(ll, 256n), 0), final, ll, List.drop(&2, U32, all, hlit), win, em)

# after a length: the next, or the codes once all are read
def inf.lens.next(l: DflLens, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match l:
    case DflLens{final, hlit, hdist, +left, lens, +ct}:
      match left:
        case 0n:
          inf.lens.done(final, hlit, lens, win, em)
        case 1n+p:
          DflCore{DflSym{ct, DflKsLens{DflLens{final, hlit, hdist, 1n+p, lens, ct}}}, win, em}

def inf.rep(n: Nat, +v: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      inf.rep(p, v, Con{v, acc})

def inf.lens.add.ok(ok: Bool, +n: Nat, +v: U32, l: DflLens, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match ok:
    case True{}:
      match l:
        case DflLens{final, hlit, hdist, left, lens, ct}:
          inf.lens.next(DflLens{final, hlit, hdist, Nat.sub(left, n), inf.rep(n, v, lens), ct}, win, em)
    case False{}:
      inf.bad(E.DeflateBadRepeat{}, win, em)

def inf.lens.left(l: DflLens) -> Nat:
  match l:
    case DflLens{final, hlit, hdist, left, lens, ct}:
      left

# n more lengths of v (refused past the HLIT + HDIST lengths)
def inf.lens.add(+n: Nat, +v: U32, +l: DflLens, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  inf.lens.add.ok(Nat.is_le(n, inf.lens.left(l)), n, v, l, win, em)

def inf.lens.prev(l: DflLens) -> Maybe<&2, U32>:
  match l:
    case DflLens{final, hlit, hdist, left, lens, ct}:
      List.head(&2, U32, lens)

# the code length code is read: then the lengths
def inf.clens.done(ok: Bool, +final: Bool, +hlit: Nat, +hdist: Nat, +clens: List<&2, U32>, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match ok:
    case True{}:
      +ct = H.huff_tree(clens)
      DflCore{DflSym{ct, DflKsLens{DflLens{final, hlit, hdist, Nat.add(hlit, hdist), Nil{}, ct}}}, win, em}
    case False{}:
      inf.bad(E.DeflateBadCodeLengthCode{}, win, em)

def inf.clen.last(p: Nat, +final: Bool, +hlit: Nat, +hdist: Nat, rest: List<&2, Nat>, +cl: List<&2, U32>, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match p:
    case 0n:
      inf.clens.done(inf.clen.ok(H.huff_kraft(cl)), final, hlit, hdist, cl, win, em)
    case 1n+q:
      DflCore{inf.field(3n, DflKClen{DflHdr{final, hlit, hdist, 1n+q, rest, cl}}), win, em}

def inf.clen.put(h: DflHdr, +v: U32, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match h:
    case DflHdr{final, hlit, hdist, left, order, clens}:
      match left:
        case 0n:
          inf.bad(E.DeflateBadCodeLengthCode{}, win, em)
        case 1n+p:
          match order:
            case Nil{}:
              inf.bad(E.DeflateBadCodeLengthCode{}, win, em)
            case Con{i, rest}:
              inf.clen.last(p, final, hlit, hdist, rest, inf.lset(clens, i, v), win, em)

# A block header's three bits: BFINAL, then BTYPE (3.2.3)

def inf.head.at(+final: Bool, t0: Bool, t1: Bool, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match t0:
    case False{}:
      match t1:
        case False{}:
          DflCore{DflAlign{final}, win, em}
        case True{}:
          DflCore{inf.field(5n, DflKHlit{final}), win, em}
    case True{}:
      match t1:
        case False{}:
          DflCore{inf.lit.st(final, DflCodes{X.fixed.lit(), X.fixed.dist()}), win, em}
        case True{}:
          inf.bad(E.DeflateBadBlockType{}, win, em)

def inf.bit.of(+v: U32, +m: U32) -> Bool:
  U32.is_eq(U32.and(v, m), m)

def inf.hlit(ok: Bool, +final: Bool, +v: U32, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match ok:
    case True{}:
      DflCore{inf.field(5n, DflKHdist{final, Nat.add(U32.to_nat(v), 257n)}), win, em}
    case False{}:
      inf.bad(E.DeflateTooManyCodes{}, win, em)

def inf.hdist(ok: Bool, +final: Bool, +hlit: Nat, +v: U32, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match ok:
    case True{}:
      DflCore{inf.field(4n, DflKHclen{final, hlit, Nat.add(U32.to_nat(v), 1n)}), win, em}
    case False{}:
      inf.bad(E.DeflateTooManyCodes{}, win, em)

def inf.rep.prev(m: Maybe<&2, U32>, +n: Nat, +l: DflLens, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match m:
    case Some{p}:
      inf.lens.add(n, p, l, win, em)
    case None{}:
      inf.bad(E.DeflateBadRepeat{}, win, em)

# the repeat counts of codes 16, 17, 18 (3.2.7)
def inf.rep.add(c16: Bool, c17: Bool, +v: U32, +l: DflLens, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match c16:
    case True{}:
      inf.rep.prev(inf.lens.prev(l), Nat.add(U32.to_nat(v), 3n), l, win, em)
    case False{}:
      match c17:
        case True{}:
          inf.lens.add(Nat.add(U32.to_nat(v), 3n), 0, l, win, em)
        case False{}:
          inf.lens.add(Nat.add(U32.to_nat(v), 11n), 0, l, win, em)

def inf.len.fin(c: DflCore, +final: Bool, codes: DflCodes, +len: Nat) -> DflCore:
  match c:
    case DflCore{st, win, em}:
      match codes:
        case DflCodes{lit, +dist}:
          DflCore{DflSym{dist, DflKsDist{final, DflCodes{lit, dist}, len}}, win, em}

# a field is complete: what it was for
def inf.field.done(k: DflK, +v: U32, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match k:
    case DflKHead{}:
      inf.head.at(inf.bit.of(v, 1), inf.bit.of(v, 2), inf.bit.of(v, 4), win, em)
    case DflKHlit{final}:
      inf.hlit(U32.is_le(v, 29), final, v, win, em)
    case DflKHdist{final, hlit}:
      inf.hdist(U32.is_le(v, 29), final, hlit, v, win, em)
    case DflKHclen{final, hlit, hdist}:
      DflCore{inf.field(3n, DflKClen{DflHdr{final, hlit, hdist, Nat.add(U32.to_nat(v), 4n), inf.order(), inf.zeros(19n, Nil{})}}), win, em}
    case DflKClen{h}:
      inf.clen.put(h, v, win, em)
    case DflKRep{l, +sym}:
      inf.rep.add(U32.is_eq(sym, 16), U32.is_eq(sym, 17), v, l, win, em)
    case DflKLen{final, codes, sym}:
      inf.len.fin(DflCore{DflEnd{Nil{}}, win, em}, final, codes, U32.to_nat(U32.add(C.code_lbase(U32.sub(sym, 257)), v)))
    case DflKDist{final, codes, len, sym}:
      inf.copy(len, U32.add(C.code_dbase(sym), v), final, codes, win, em)

def inf.sym.rep16(m: Maybe<&2, U32>, +l: DflLens, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match m:
    case Some{p}:
      DflCore{inf.field(2n, DflKRep{l, 16}), win, em}
    case None{}:
      inf.bad(E.DeflateBadRepeat{}, win, em)

# a code length symbol (3.2.7): 0-15 a length, 16-18 a repeat (16 needs a
# length before it)
def inf.sym.lens(small: Bool, c16: Bool, c17: Bool, +s: U32, +l: DflLens, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match small:
    case True{}:
      inf.lens.add(1n, s, l, win, em)
    case False{}:
      match c16:
        case True{}:
          inf.sym.rep16(inf.lens.prev(l), l, win, em)
        case False{}:
          match c17:
            case True{}:
              DflCore{inf.field(3n, DflKRep{l, s}), win, em}
            case False{}:
              DflCore{inf.field(7n, DflKRep{l, s}), win, em}

# a length symbol's extra bits, then the distance
def inf.sym.len.at(n: Nat, +final: Bool, codes: DflCodes, +c: U32, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match n:
    case 0n:
      inf.len.fin(DflCore{DflEnd{Nil{}}, win, em}, final, codes, U32.to_nat(C.code_lbase(c)))
    case 1n+p:
      DflCore{inf.field(1n+p, DflKLen{final, codes, U32.add(c, 257)}), win, em}

def inf.sym.len(+final: Bool, codes: DflCodes, +c: U32, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  inf.sym.len.at(C.code_lext(c), final, codes, c, win, em)

# a literal/length symbol (3.2.5): a literal, the end of the block, a length
def inf.sym.lit(lit: Bool, end: Bool, len: Bool, +s: U32, +final: Bool, codes: DflCodes, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match lit:
    case True{}:
      DflCore{inf.lit.st(final, codes), W.win.put(win, s), Con{s, em}}
    case False{}:
      match end:
        case True{}:
          match final:
            case True{}:
              DflCore{DflEnd{Nil{}}, win, em}
            case False{}:
              DflCore{inf.head(), win, em}
        case False{}:
          match len:
            case True{}:
              inf.sym.len(final, codes, U32.sub(s, 257), win, em)
            case False{}:
              inf.bad(E.DeflateBadLitLenSymbol{}, win, em)

def inf.sym.dist.at(n: Nat, +s: U32, +final: Bool, codes: DflCodes, +len: Nat, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match n:
    case 0n:
      inf.copy(len, C.code_dbase(s), final, codes, win, em)
    case 1n+p:
      DflCore{inf.field(1n+p, DflKDist{final, codes, len, s}), win, em}

# a distance symbol (3.2.5): refused at once if even its least distance
# reaches past the start
def inf.sym.dist(ok: Bool, far: Bool, +s: U32, +final: Bool, codes: DflCodes, +len: Nat, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match ok:
    case True{}:
      match far:
        case True{}:
          inf.bad(E.DeflateDistanceTooFar{}, win, em)
        case False{}:
          inf.sym.dist.at(C.code_dext(s), s, final, codes, len, win, em)
    case False{}:
      inf.bad(E.DeflateBadDistSymbol{}, win, em)

# a Huffman symbol is complete: what it was for
def inf.sym.done(k: DflKs, +s: U32, +win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match k:
    case DflKsLens{l}:
      inf.sym.lens(U32.is_lt(s, 16), U32.is_eq(s, 16), U32.is_eq(s, 17), s, l, win, em)
    case DflKsLit{final, codes}:
      inf.sym.lit(U32.is_lt(s, 256), U32.is_eq(s, 256), U32.is_lt(s, 286), s, final, codes, win, em)
    case DflKsDist{final, codes, len}:
      inf.sym.dist(U32.is_lt(s, 30), U32.is_lt(W.win.count(win), C.code_dbase(s)), s, final, codes, len, win, em)

# the failure when the bits match no code
def inf.sym.bad(k: DflKs) -> E.DeflateError:
  match k:
    case DflKsLens{l}:
      E.DeflateBadCodeLengthSymbol{}
    case DflKsLit{final, codes}:
      E.DeflateBadLitLenSymbol{}
    case DflKsDist{final, codes, len}:
      E.DeflateBadDistSymbol{}

# one step down the tree
def inf.sym.step(child: H.DflTree, k: DflKs, win: W.DflWin, em: List<&2, U32>) -> DflCore:
  match child:
    case H.DflHLeaf{s}:
      inf.sym.done(k, s, win, em)
    case H.DflHNil{}:
      inf.bad(inf.sym.bad(k), win, em)
    case H.DflHNode{z, o}:
      DflCore{DflSym{H.DflHNode{z, o}, k}, win, em}

# One bit

def inf.bit(c: DflCore, b: Bool) -> DflCore:
  match c:
    case DflCore{st, win, em}:
      match st:
        case DflField{left, +sh, v, k}:
          match left:
            case 0n:
              inf.field.done(k, K.bits.field(v, sh, b), win, em)
            case 1n+p:
              match p:
                case 0n:
                  inf.field.done(k, K.bits.field(v, sh, b), win, em)
                case 1n+q:
                  DflCore{DflField{1n+q, 1n+sh, K.bits.field(v, sh, b), k}, win, em}
        case DflSym{node, k}:
          match node:
            case H.DflHNode{z, o}:
              match b:
                case True{}:
                  inf.sym.step(o, k, win, em)
                case False{}:
                  inf.sym.step(z, k, win, em)
            case _:
              inf.bad(inf.sym.bad(k), win, em)
        case DflAlign{final}:
          DflCore{DflAlign{final}, win, em}
        case DflStoredLen{n, v, final}:
          DflCore{DflStoredLen{n, v, final}, win, em}
        case DflStored{left, final}:
          DflCore{DflStored{left, final}, win, em}
        case DflEnd{rest}:
          DflCore{DflEnd{rest}, win, em}
        case DflBad{e}:
          DflCore{DflBad{e}, win, em}

# One byte

# a stored block of n bytes, or what follows it when n is 0
def inf.stored.next(n: Nat, final: Bool) -> DflSt:
  match n:
    case 0n:
      match final:
        case True{}:
          DflEnd{Nil{}}
        case False{}:
          inf.head()
    case 1n+p:
      DflStored{1n+p, final}

def inf.stored.len(ok: Bool, +v: U32, +final: Bool) -> DflSt:
  match ok:
    case True{}:
      inf.stored.next(U32.to_nat(U32.and(v, 65535)), final)
    case False{}:
      DflBad{E.DeflateBadStoredLength{}}

# LEN, then NLEN, least significant byte first (3.2.4)
def inf.stored.hdr(n: Nat, +v: U32, +final: Bool) -> DflSt:
  match n:
    case 0n:
      DflStoredLen{1n, v, final}
    case 1n+p:
      match p:
        case 0n:
          DflStoredLen{2n, v, final}
        case 1n+q:
          match q:
            case 0n:
              DflStoredLen{3n, v, final}
            case 1n+r:
              inf.stored.len(Q.eq.u32(U32.shrn(v, 16n), U32.xor(U32.and(v, 65535), 65535)), v, final)

# a byte whose bits are all read: a stored block's header ends at it
def inf.byte.fin(c: DflCore) -> DflCore:
  match c:
    case DflCore{st, win, em}:
      match st:
        case DflAlign{final}:
          DflCore{DflStoredLen{0n, 0, final}, win, em}
        case DflField{left, sh, v, k}:
          DflCore{DflField{left, sh, v, k}, win, em}
        case DflSym{node, k}:
          DflCore{DflSym{node, k}, win, em}
        case DflStoredLen{n, v, final}:
          DflCore{DflStoredLen{n, v, final}, win, em}
        case DflStored{left, final}:
          DflCore{DflStored{left, final}, win, em}
        case DflEnd{rest}:
          DflCore{DflEnd{rest}, win, em}
        case DflBad{e}:
          DflCore{DflBad{e}, win, em}

def inf.bits8(c: DflCore, bb: K.DflByteBits) -> DflCore:
  match bb:
    case K.DflByteBits{b0, b1, b2, b3, b4, b5, b6, b7}:
      inf.byte.fin(inf.bit(inf.bit(inf.bit(inf.bit(inf.bit(inf.bit(inf.bit(inf.bit(c, b0), b1), b2), b3), b4), b5), b6), b7))

# the machine after one more input byte
def inf.byte(c: DflCore, +h: U32) -> DflCore:
  match c:
    case DflCore{st, win, em}:
      match st:
        case DflStoredLen{+n, v, final}:
          DflCore{inf.stored.hdr(n, U32.or(v, U32.shln(B.byte(h), Nat.mul(n, 8n))), final), win, em}
        case DflStored{left, final}:
          match left:
            case 0n:
              DflCore{inf.stored.next(0n, final), W.win.put(win, h), Con{h, em}}
            case 1n+p:
              DflCore{inf.stored.next(p, final), W.win.put(win, h), Con{h, em}}
        case DflEnd{rest}:
          DflCore{DflEnd{Con{h, rest}}, win, em}
        case DflBad{e}:
          DflCore{DflBad{e}, win, em}
        case DflField{left, sh, v, k}:
          inf.bits8(DflCore{DflField{left, sh, v, k}, win, em}, K.bits.of(h))
        case DflSym{node, k}:
          inf.bits8(DflCore{DflSym{node, k}, win, em}, K.bits.of(h))
        case DflAlign{final}:
          inf.bits8(DflCore{DflAlign{final}, win, em}, K.bits.of(h))

# The driver: the output so far (reversed) and the room left under the
# maximum

type DflApp is Data:
  DflAppOk{acc: List<&2, U32>, room: Nat}
  DflAppFull{}

def drv.app.con(+b: U32, r: DflApp) -> DflApp:
  match r:
    case DflAppFull{}:
      DflAppFull{}
    case DflAppOk{acc, room}:
      match room:
        case 0n:
          DflAppFull{}
        case 1n+q:
          DflAppOk{Con{b, acc}, q}

# a byte's output (reversed, as the machine puts it out) onto the output
# so far, one byte of room each
def drv.app(em: List<&2, U32>, acc: List<&2, U32>, room: Nat) -> DflApp:
  match em:
    case Nil{}:
      DflAppOk{acc, room}
    case Con{b, t}:
      drv.app.con(b, drv.app(t, acc, room))

type DflDrv is Data:
  DflRun{core: DflCore, acc: List<&2, U32>, room: Nat}
  DflFull{}

def drv.put(r: DflApp, st: DflSt, win: W.DflWin) -> DflDrv:
  match r:
    case DflAppFull{}:
      DflFull{}
    case DflAppOk{acc, room}:
      DflRun{DflCore{st, win, Nil{}}, acc, room}

def drv.core(c: DflCore, acc: List<&2, U32>, room: Nat) -> DflDrv:
  match c:
    case DflCore{st, win, em}:
      drv.put(drv.app(em, acc, room), st, win)

def drv.byte(d: DflDrv, h: U32) -> DflDrv:
  match d:
    case DflFull{}:
      DflFull{}
    case DflRun{core, acc, room}:
      drv.core(inf.byte(core, h), acc, room)

# the driver after the bytes xs
def drv.go(xs: List<&2, U32>, d: DflDrv) -> DflDrv:
  match xs:
    case Nil{}:
      d
    case Con{h, t}:
      drv.go(t, drv.byte(d, h))

# the machine at the start of a stream, after a window (a dictionary)
def drv.start(win: W.DflWin, room: Nat) -> DflDrv:
  DflRun{DflCore{inf.head(), win, Nil{}}, Nil{}, room}

# a finished stream: its output (reversed) and the bytes after it
type DflRaw is Data:
  DflRaw{acc: List<&2, U32>, rest: List<&2, U32>}

def drv.end(st: DflSt, +acc: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflRaw>:
  match st:
    case DflEnd{rest}:
      Done{DflRaw{acc, B.rev(rest)}}
    case DflBad{e}:
      Fail{e}
    case _:
      Fail{E.DeflateTruncated{}}

def drv.result(d: DflDrv) -> Result<&2, &2, E.DeflateError, DflRaw>:
  match d:
    case DflFull{}:
      Fail{E.DeflateOutputTooLarge{}}
    case DflRun{core, acc, room}:
      match core:
        case DflCore{st, win, em}:
          drv.end(st, acc)

# a raw stream from the list xs, after the window win, with room bytes of
# output at most: its output (reversed) and the bytes after it (for the
# zlib and gzip wrappers)
def inf.run(win: W.DflWin, room: Nat, xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflRaw>:
  drv.result(drv.go(xs, drv.start(win, room)))

# a finished stream's output, and the bytes after it
type DflOutRest is Data:
  DflOutRest{out: B.Octets, rest: List<&2, U32>}

def inf.out(r: Result<&2, &2, E.DeflateError, DflRaw>) -> Result<&2, &2, E.DeflateError, DflOutRest>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{DflRaw{acc, rest}}:
      Done{DflOutRest{B.Octets.of_list(B.rev(acc)), rest}}

# inf.run, its output as Octets
def inf.run.out(win: W.DflWin, room: Nat, xs: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflOutRest>:
  inf.out(inf.run(win, room, xs))

# The public interface

# max: the most output allowed; dict: a preset dictionary the stream may
# refer back into (for zlib, used only when the stream asks for one); ignore:
# whether bytes after the stream are ignored (else DeflateTrailingData)
type InflateOptions is Data:
  InflateOptions{max: U32, dict: B.Octets, ignore: Bool}

# 64 MiB, no dictionary, bytes after the stream ignored (as zlib does)
def InflateOptions.default() -> InflateOptions:
  InflateOptions{67108864, B.Octets.empty(), True{}}

def InflateOptions.max(o: InflateOptions) -> U32:
  match o:
    case InflateOptions{max, dict, ignore}:
      max

def InflateOptions.dict(o: InflateOptions) -> B.Octets:
  match o:
    case InflateOptions{max, dict, ignore}:
      dict

def InflateOptions.ignore(o: InflateOptions) -> Bool:
  match o:
    case InflateOptions{max, dict, ignore}:
      ignore

def InflateOptions.with_dict(o: InflateOptions, +d: B.Octets) -> InflateOptions:
  match o:
    case InflateOptions{max, dict, ignore}:
      InflateOptions{max, d, ignore}

# a stream's output and the input after it
type DflInflated is Data:
  DflInflated{out: B.Octets, rest: B.Octets}

def inf.split.guard(ok: Bool, +out: B.Octets, +rest: List<&2, U32>) -> Result<&2, &2, E.DeflateError, DflInflated>:
  match ok:
    case True{}:
      Done{DflInflated{out, B.Octets.of_list(rest)}}
    case False{}:
      Fail{E.DeflateOutputTooLarge{}}

def inf.split.of(r: Result<&2, &2, E.DeflateError, DflOutRest>, +max: U32) -> Result<&2, &2, E.DeflateError, DflInflated>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{DflOutRest{+out, rest}}:
      inf.split.guard(Nat.is_le(B.Octets.len(out), U32.to_nat(max)), out, rest)

# the raw DEFLATE stream at the start of src: its output, and the bytes
# after it
def inflate_split(opts: InflateOptions, src: B.Octets) -> Result<&2, &2, E.DeflateError, DflInflated>:
  match opts:
    case InflateOptions{+max, dict, ignore}:
      inf.split.of(inf.run.out(W.win.of(B.Octets.to_list(dict)), U32.to_nat(max), B.Octets.to_list(src)), max)

def inf.whole.none(n: Nat, +out: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match n:
    case 0n:
      Done{out}
    case 1n+p:
      Fail{E.DeflateTrailingData{}}

def inf.whole(r: Result<&2, &2, E.DeflateError, DflInflated>, ignore: Bool) -> Result<&2, &2, E.DeflateError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{DflInflated{out, +rest}}:
      match ignore:
        case True{}:
          Done{out}
        case False{}:
          inf.whole.none(B.Octets.len(rest), out)

# the output of the raw DEFLATE stream src, with these options
def inflate_with(+opts: InflateOptions, src: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  inf.whole(inflate_split(opts, src), InflateOptions.ignore(opts))

# the same, with InflateOptions.default()
def inflate(src: B.Octets) -> Result<&2, &2, E.DeflateError, B.Octets>:
  inflate_with(InflateOptions.default(), src)

# Streaming: feed the stream in pieces of any size; each feed answers the
# output those bytes complete

type Inflater is Data:
  Inflater{d: DflDrv, max: U32, ignore: Bool}

type DflFed is Data:
  DflFed{inflater: Inflater, out: B.Octets}

def inflate_start(opts: InflateOptions) -> Inflater:
  match opts:
    case InflateOptions{+max, dict, ignore}:
      Inflater{drv.start(W.win.of(B.Octets.to_list(dict)), U32.to_nat(max)), max, ignore}

def inf.flush(d: DflDrv, +max: U32, +ignore: Bool) -> DflFed:
  match d:
    case DflFull{}:
      DflFed{Inflater{DflFull{}, max, ignore}, B.Octets.empty()}
    case DflRun{core, acc, room}:
      DflFed{Inflater{DflRun{core, Nil{}, room}, max, ignore}, B.Octets.of_list(B.rev(acc))}

def inflate_feed(i: Inflater, o: B.Octets) -> DflFed:
  match i:
    case Inflater{d, max, ignore}:
      inf.flush(drv.go(B.Octets.to_list(o), d), max, ignore)

# whether the final block has ended (the rest of the input is not part of
# the stream)
def inflate_done(i: Inflater) -> Bool:
  match i:
    case Inflater{d, max, ignore}:
      match d:
        case DflRun{core, acc, room}:
          match core:
            case DflCore{st, win, em}:
              match st:
                case DflEnd{rest}:
                  True{}
                case _:
                  False{}
        case DflFull{}:
          False{}

# an inflater after the window win, with room bytes of output at most (the
# wrappers' streaming readers start one per stream)
def inf.start(win: W.DflWin, room: Nat, +max: U32, ignore: Bool) -> Inflater:
  Inflater{drv.start(win, room), max, ignore}

def inf.rest.of(d: DflDrv) -> List<&2, U32>:
  match d:
    case DflRun{core, acc, room}:
      match core:
        case DflCore{st, win, em}:
          match st:
            case DflEnd{rest}:
              B.rev(rest)
            case _:
              Nil{}
    case DflFull{}:
      Nil{}

# the bytes fed after the end of the stream (none before it ends)
def inflate_rest(i: Inflater) -> List<&2, U32>:
  match i:
    case Inflater{d, max, ignore}:
      inf.rest.of(d)

def inf.room.of(d: DflDrv) -> Nat:
  match d:
    case DflRun{core, acc, room}:
      room
    case DflFull{}:
      0n

# how much more output the maximum allows
def inflate_room(i: Inflater) -> Nat:
  match i:
    case Inflater{d, max, ignore}:
      inf.room.of(d)

# the end of the stream: the output not yet handed out and the bytes after
# the stream, or the failure
def inf.finish.of(r: Result<&2, &2, E.DeflateError, DflRaw>) -> Result<&2, &2, E.DeflateError, DflInflated>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{DflRaw{acc, rest}}:
      Done{DflInflated{B.Octets.of_list(B.rev(acc)), B.Octets.of_list(rest)}}

def inflate_finish(i: Inflater) -> Result<&2, &2, E.DeflateError, DflInflated>:
  match i:
    case Inflater{d, max, ignore}:
      inf.finish.of(drv.result(d))
