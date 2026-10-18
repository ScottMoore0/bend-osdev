# bend-osdev-zstd, the literals section of a compressed block (RFC 8878,
# section 3.1.1.3.1): its header, and raw, RLE, Huffman-compressed (one
# stream or four) and treeless literals.
#
# The first byte gives the type (bits 0-1: raw, RLE, compressed, treeless)
# and the size format (bits 2-3). Raw and RLE literals give their size in 5,
# 12 or 20 bits (a header of 1, 2 or 3 bytes); compressed and treeless ones
# give the regenerated and compressed sizes in 10, 10, 14 or 18 bits each
# (3, 3, 4 or 5 bytes), size format 0 meaning one stream and the others
# four. Compressed literals start with a Huffman tree description; treeless
# ones reuse the last tree of the frame.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./bits.bend as Bi
import ./huffman.bend as H

# the literals, the bytes after the section, and the tree to reuse next
type ZstdLiterals is Data:
  ZstdLiterals{lits: List<&2, U32>, rest: List<&2, U32>, tree: Maybe<&2, H.ZstdHufTable>}

def lit.nat(xs: List<&2, U32>, i: Nat) -> Nat:
  U32.to_nat(B.byte(Maybe.default(&2, U32, B.at(xs, i), 0)))

# the fifth header byte (in 5-byte headers), whose bits end the compressed size
def lit.byte4(five: Bool, +xs: List<&2, U32>) -> U32:
  match five:
    case True{}:
      B.byte(Maybe.default(&2, U32, B.at(xs, 4n), 0))
    case False{}:
      0

def lit.u32s(xs: List<&2, Nat>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      B.rev(acc)
    case Con{h, t}:
      lit.u32s(t, Con{U32.from_nat(h), acc})

def lit.rep(n: Nat, +b: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+k:
      lit.rep(k, b, Con{b, acc})

type ZsLitSize is Data:
  ZsLitSize{hl: Nat, regen: Nat}

# the header length and size of raw and RLE literals, by size format
def lit.raw_size(sf: Nat, +b0: Nat, +xs: List<&2, U32>, +n: Nat) -> Result<&2, &2, E.ZstdError, ZsLitSize>:
  match sf:
    case 0n:
      Done{ZsLitSize{1n, Nat.div(b0, 8n)}}
    case 1n+p:
      match p:
        case 0n:
          do Result<&2, &2, E.ZstdError, ZsLitSize>:
            u : Unit <- E.ZstdError.require(Nat.is_le(2n, n), E.ZstdBadLiteralsHeader{})
            return ZsLitSize{2n, Nat.add(Nat.div(b0, 16n), Nat.mul(lit.nat(xs, 1n), 16n))}
        case 1n+q:
          match q:
            case 0n:
              Done{ZsLitSize{1n, Nat.div(b0, 8n)}}
            case 1n+r:
              do Result<&2, &2, E.ZstdError, ZsLitSize>:
                u : Unit <- E.ZstdError.require(Nat.is_le(3n, n), E.ZstdBadLiteralsHeader{})
                return ZsLitSize{3n, Nat.add(Nat.add(Nat.div(b0, 16n), Nat.mul(lit.nat(xs, 1n), 16n)), Nat.mul(lit.nat(xs, 2n), 4096n))}

def lit.rawrle.body(rle: Bool, +hl: Nat, +regen: Nat, +xs: List<&2, U32>, +n: Nat, tree: Maybe<&2, H.ZstdHufTable>) -> Result<&2, &2, E.ZstdError, ZstdLiterals>:
  match rle:
    case False{}:
      do Result<&2, &2, E.ZstdError, ZstdLiterals>:
        u : Unit <- E.ZstdError.require(Nat.is_le(Nat.add(hl, regen), n), E.ZstdBadLiteralsHeader{})
        return ZstdLiterals{B.take.fast(regen, B.drop(hl, xs)), B.drop(Nat.add(hl, regen), xs), tree}
    case True{}:
      do Result<&2, &2, E.ZstdError, ZstdLiterals>:
        u : Unit <- E.ZstdError.require(Nat.is_le(Nat.add(hl, 1n), n), E.ZstdBadLiteralsHeader{})
        return ZstdLiterals{lit.rep(regen, B.byte(Maybe.default(&2, U32, B.at(xs, hl), 0)), Nil{}), B.drop(Nat.add(hl, 1n), xs), tree}

def lit.rawrle(s: ZsLitSize, rle: Bool, +xs: List<&2, U32>, +n: Nat, +block_max: Nat, tree: Maybe<&2, H.ZstdHufTable>) -> Result<&2, &2, E.ZstdError, ZstdLiterals>:
  match s:
    case ZsLitSize{+hl, +regen}:
      do Result<&2, &2, E.ZstdError, ZstdLiterals>:
        u : Unit <- E.ZstdError.require(Nat.is_le(regen, block_max), E.ZstdBadLiteralsHeader{})
        r : ZstdLiterals <- lit.rawrle.body(rle, hl, regen, xs, n, tree)
        return r

# Huffman-coded streams

def lit.one(m: Maybe<&2, List<&2, Nat>>) -> Result<&2, &2, E.ZstdError, List<&2, Nat>>:
  E.ZstdError.need(List<&2, Nat>, m, E.ZstdBadHuffmanStream{})

# four streams: a jump table of three 16-bit sizes, then the streams, the
# first three regenerating (regen + 3) / 4 bytes each and the last the rest
def lit.four(+t: H.ZstdHufTable, +xs: List<&2, U32>, +regen: Nat) -> Result<&2, &2, E.ZstdError, List<&2, Nat>>:
  +m = B.len.fast(xs)
  +s1 = Nat.add(lit.nat(xs, 0n), Nat.mul(lit.nat(xs, 1n), 256n))
  +s2 = Nat.add(lit.nat(xs, 2n), Nat.mul(lit.nat(xs, 3n), 256n))
  +s3 = Nat.add(lit.nat(xs, 4n), Nat.mul(lit.nat(xs, 5n), 256n))
  +seg = Nat.div(Nat.add(regen, 3n), 4n)
  +d1 = B.drop(6n, xs)
  +d2 = B.drop(s1, d1)
  +d3 = B.drop(s2, d2)
  do Result<&2, &2, E.ZstdError, List<&2, Nat>>:
    u1 : Unit <- E.ZstdError.require(Nat.is_le(6n, m), E.ZstdBadHuffmanStream{})
    u2 : Unit <- E.ZstdError.require(Bool.and(Nat.is_le(Nat.add(Nat.add(Nat.add(s1, s2), s3), 6n), m), Nat.is_le(Nat.mul(3n, seg), regen)), E.ZstdBadHuffmanStream{})
    a : List<&2, Nat> <- lit.one(H.ZstdHuf.decode_stream(t, B.take.fast(s1, d1), seg))
    b : List<&2, Nat> <- lit.one(H.ZstdHuf.decode_stream(t, B.take.fast(s2, d2), seg))
    c : List<&2, Nat> <- lit.one(H.ZstdHuf.decode_stream(t, B.take.fast(s3, d3), seg))
    d : List<&2, Nat> <- lit.one(H.ZstdHuf.decode_stream(t, B.drop(s3, d3), Nat.sub(regen, Nat.mul(3n, seg))))
    return List.append(&2, Nat, a, List.append(&2, Nat, b, List.append(&2, Nat, c, d)))

def lit.streams(sf: Nat, +t: H.ZstdHufTable, +xs: List<&2, U32>, +regen: Nat) -> Result<&2, &2, E.ZstdError, List<&2, Nat>>:
  match sf:
    case 0n:
      lit.one(H.ZstdHuf.decode_stream(t, xs, regen))
    case 1n+p:
      do Result<&2, &2, E.ZstdError, List<&2, Nat>>:
        u : Unit <- E.ZstdError.require(Nat.is_le(6n, regen), E.ZstdBadLiteralsHeader{})
        r : List<&2, Nat> <- lit.four(t, xs, regen)
        return r

def lit.tree(fresh: Bool, +body: List<&2, U32>, prev: Maybe<&2, H.ZstdHufTable>) -> Result<&2, &2, E.ZstdError, H.ZstdHufRead>:
  match fresh:
    case True{}:
      E.ZstdError.need(H.ZstdHufRead, H.ZstdHuf.read_tree(body), E.ZstdBadHuffmanTree{})
    case False{}:
      match prev:
        case None{}:
          Fail{E.ZstdNoHuffmanTree{}}
        case Some{t}:
          Done{H.ZstdHufRead{t, 0n}}

def lit.coded.body(r: H.ZstdHufRead, +sf: Nat, +body: List<&2, U32>, +regen: Nat, rest: List<&2, U32>) -> Result<&2, &2, E.ZstdError, ZstdLiterals>:
  match r:
    case H.ZstdHufRead{+t, used}:
      do Result<&2, &2, E.ZstdError, ZstdLiterals>:
        syms : List<&2, Nat> <- lit.streams(sf, t, B.drop(used, body), regen)
        return ZstdLiterals{lit.u32s(syms, Nil{}), rest, Some{t}}

# compressed (fresh: with a tree description) and treeless literals; hl
# and bits by size format
def lit.coded(fresh: Bool, +sf: Nat, +hl: Nat, +bits: Nat, +xs: List<&2, U32>, +n: Nat, +block_max: Nat, prev: Maybe<&2, H.ZstdHufTable>) -> Result<&2, &2, E.ZstdError, ZstdLiterals>:
  +lo = Bi.ZstdBits.u32le(B.take(hl, xs))
  +b4 = lit.byte4(Nat.is_eq(hl, 5n), xs)
  +mask = U32.sub(U32.shln(1, bits), 1)
  +regen = U32.to_nat(U32.and(mask, U32.shrn(lo, 4n)))
  +comp = U32.to_nat(U32.and(mask, U32.or(U32.shrn(lo, Nat.add(4n, bits)), U32.shln(b4, Nat.sub(28n, bits)))))
  +body = B.take.fast(comp, B.drop(hl, xs))
  do Result<&2, &2, E.ZstdError, ZstdLiterals>:
    u1 : Unit <- E.ZstdError.require(Nat.is_le(hl, n), E.ZstdBadLiteralsHeader{})
    u2 : Unit <- E.ZstdError.require(Bool.and(Nat.is_le(regen, block_max), Nat.is_le(Nat.add(hl, comp), n)), E.ZstdBadLiteralsHeader{})
    r : H.ZstdHufRead <- lit.tree(fresh, body, prev)
    out : ZstdLiterals <- lit.coded.body(r, sf, body, regen, B.drop(Nat.add(hl, comp), xs))
    return out

# the header length and the width of each size, by size format
def lit.hl(sf: Nat) -> Nat:
  match sf:
    case 0n:
      3n
    case 1n+p:
      match p:
        case 0n:
          3n
        case 1n+q:
          match q:
            case 0n:
              4n
            case 1n+r:
              5n

def lit.bits(sf: Nat) -> Nat:
  match sf:
    case 0n:
      10n
    case 1n+p:
      match p:
        case 0n:
          10n
        case 1n+q:
          match q:
            case 0n:
              14n
            case 1n+r:
              18n

def lit.kind(k: Nat, +sf: Nat, +b0: Nat, +xs: List<&2, U32>, +n: Nat, +block_max: Nat, tree: Maybe<&2, H.ZstdHufTable>) -> Result<&2, &2, E.ZstdError, ZstdLiterals>:
  match k:
    case 0n:
      do Result<&2, &2, E.ZstdError, ZstdLiterals>:
        s : ZsLitSize <- lit.raw_size(sf, b0, xs, n)
        r : ZstdLiterals <- lit.rawrle(s, False{}, xs, n, block_max, tree)
        return r
    case 1n+p:
      match p:
        case 0n:
          do Result<&2, &2, E.ZstdError, ZstdLiterals>:
            s : ZsLitSize <- lit.raw_size(sf, b0, xs, n)
            r : ZstdLiterals <- lit.rawrle(s, True{}, xs, n, block_max, tree)
            return r
        case 1n+q:
          lit.coded(Nat.is_eq(q, 0n), sf, lit.hl(sf), lit.bits(sf), xs, n, block_max, tree)

# The public interface

# the literals section at the start of xs (the rest of a compressed block):
# the literals, the bytes after the section, and the tree to reuse next;
# block_max bounds the regenerated size, prev is the tree treeless
# literals reuse
def ZstdLit.decode(xs: List<&2, U32>, +block_max: Nat, prev: Maybe<&2, H.ZstdHufTable>) -> Result<&2, &2, E.ZstdError, ZstdLiterals>:
  match xs:
    case Nil{}:
      Fail{E.ZstdBadLiteralsHeader{}}
    case Con{+h, t}:
      +all = {Con{h, t} : List<&2, U32>}
      +b0 = U32.to_nat(B.byte(h))
      lit.kind(Nat.mod(b0, 4n), Nat.mod(Nat.div(b0, 4n), 4n), b0, all, B.len.fast(all), block_max, prev)
