# bend-osdev-lz4, the block format (LZ4 Block Format Description,
# lz4_Block_format.md, from the LZ4 project): the decoder, the simplest
# encoder, and the errors every part of the package answers.
#
# Decompression takes the block and a maximum output size and answers
# Fail{e} for every malformed block: offset 0 or one before the start of the
# output, a block cut short, an output past the maximum, a block that breaks
# the end-of-block rules. It never reads past its input and never writes more
# than the maximum.
import Base
import ../bytes/bytes.bend as B

# Errors (of the block and the frame format alike)

type Lz4Error is Data:
  Lz4Truncated{}
  Lz4BadOffset{}
  Lz4OutputTooLarge{}
  Lz4BadBlockEnd{}
  Lz4BadMagic{}
  Lz4BadVersion{}
  Lz4BadDescriptor{}
  Lz4BadHeaderChecksum{}
  Lz4BlockTooLarge{}
  Lz4BadBlockChecksum{}
  Lz4BadContentSize{}
  Lz4BadContentChecksum{}

def Lz4Error.show(e: Lz4Error) -> String:
  match e:
    case Lz4Truncated{}:
      "Truncated"
    case Lz4BadOffset{}:
      "BadOffset"
    case Lz4OutputTooLarge{}:
      "OutputTooLarge"
    case Lz4BadBlockEnd{}:
      "BadBlockEnd"
    case Lz4BadMagic{}:
      "BadMagic"
    case Lz4BadVersion{}:
      "BadVersion"
    case Lz4BadDescriptor{}:
      "BadDescriptor"
    case Lz4BadHeaderChecksum{}:
      "BadHeaderChecksum"
    case Lz4BlockTooLarge{}:
      "BlockTooLarge"
    case Lz4BadBlockChecksum{}:
      "BadBlockChecksum"
    case Lz4BadContentSize{}:
      "BadContentSize"
    case Lz4BadContentChecksum{}:
      "BadContentChecksum"

# Lists of bytes (the decoder's working form)

# the bytes of xs, masked, pushed one by one onto acc (so acc gets them in
# reverse order): how the decoder grows its output
def blk.push(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      blk.push(t, Con{B.byte(h), acc})

def blk.rev(xs: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, xs)

# The decoder
#
# A block is a run of sequences. Each sequence is a token (literal length in
# the high nibble, match length minus 4 in the low one), more literal-length
# bytes when the nibble is 15 (each 255 adds 255 and goes on; any other byte
# adds itself and ends), the literals, a 16-bit little-endian offset, and more
# match-length bytes when the nibble is 15. The last sequence stops after its
# literals.
#
# The decoder reads one byte at a time. Its output so far is kept reversed
# (the most recent byte first), so the byte at offset o is at index o - 1.

type Lz4St is Data:
  Lz4Tok{}
  Lz4LitExt{n: Nat, m: U32}
  Lz4Lit{n: Nat, total: Nat, m: U32}
  Lz4Off{lo: U32, m: U32}
  Lz4MatExt{off: Nat, n: Nat}
  Lz4Bad{e: Lz4Error}

# st: what the next byte is; acc: the output so far, reversed (after any
# history the block may refer to); room: how many more bytes the output may
# take; last: the length of the last match (0: no match yet)
type Lz4Dec is Data:
  Lz4Dec{st: Lz4St, acc: List<&2, U32>, room: Nat, last: Nat}

# a length byte: 255 (more follow) or the last one, with its value
type Lz4Ext is Data:
  Lz4Full{}
  Lz4Last{v: Nat}

# a block's output, reversed (after the history), and the room left
type Lz4Out is Data:
  Lz4Out{acc: List<&2, U32>, room: Nat}

def blk.bad(e: Lz4Error) -> Lz4Dec:
  Lz4Dec{Lz4Bad{e}, Nil{}, 0n, 0n}

def blk.ext.pick(full: Bool, b: U32) -> Lz4Ext:
  match full:
    case True{}:
      Lz4Full{}
    case False{}:
      Lz4Last{U32.to_nat(b)}

def blk.ext(h: U32) -> Lz4Ext:
  +b = B.byte(h)
  blk.ext.pick(U32.is_eq(b, 255), b)

# a token: 15 literals or more go on in length bytes
def blk.tok.pick(more: Bool, l: U32, m: U32, acc: List<&2, U32>, room: Nat, last: Nat) -> Lz4Dec:
  match more:
    case True{}:
      Lz4Dec{Lz4LitExt{15n, m}, acc, room, last}
    case False{}:
      +n = U32.to_nat(l)
      Lz4Dec{Lz4Lit{n, n, m}, acc, room, last}

def blk.tok(h: U32, acc: List<&2, U32>, room: Nat, last: Nat) -> Lz4Dec:
  +t = B.byte(h)
  +l = U32.shrn(t, 4n)
  blk.tok.pick(U32.is_eq(l, 15), l, U32.and(t, 15), acc, room, last)

def blk.litext(e: Lz4Ext, n: Nat, m: U32, acc: List<&2, U32>, room: Nat, last: Nat) -> Lz4Dec:
  match e:
    case Lz4Full{}:
      Lz4Dec{Lz4LitExt{Nat.add(255n, n), m}, acc, room, last}
    case Lz4Last{v}:
      +t = Nat.add(v, n)
      Lz4Dec{Lz4Lit{t, t, m}, acc, room, last}

# n literals left: copy this one; none left: this byte starts the offset
def blk.lit(n: Nat, room: Nat, total: Nat, m: U32, h: U32, acc: List<&2, U32>, last: Nat) -> Lz4Dec:
  match n:
    case 0n:
      Lz4Dec{Lz4Off{B.byte(h), m}, acc, room, last}
    case 1n+p:
      match room:
        case 0n:
          blk.bad(Lz4OutputTooLarge{})
        case 1n+r:
          Lz4Dec{Lz4Lit{p, total, m}, Con{B.byte(h), acc}, r, last}

# n bytes, each the one o + 1 back; the copy may overlap what it writes
def blk.copy.go(n: Nat, room: Nat, +o: Nat, +acc: List<&2, U32>, +last: Nat) -> Lz4Dec:
  match n:
    case 0n:
      Lz4Dec{Lz4Tok{}, acc, room, last}
    case 1n+p:
      match room:
        case 0n:
          blk.bad(Lz4OutputTooLarge{})
        case 1n+r:
          blk.copy.go(p, r, o, Con{Maybe.default(&2, U32, B.at(acc, o), 0), acc}, last)

def blk.copy.check(ok: Bool, +len: Nat, o: Nat, acc: List<&2, U32>, room: Nat) -> Lz4Dec:
  match ok:
    case True{}:
      blk.copy.go(len, room, o, acc, len)
    case False{}:
      blk.bad(Lz4BadOffset{})

# a match: offset 0, or one before the start of the output, is refused; the
# byte at the offset exists, and the copy only adds bytes, so every later
# byte it reads exists too
def blk.copy(+off: Nat, +len: Nat, +acc: List<&2, U32>, room: Nat) -> Lz4Dec:
  match off:
    case 0n:
      blk.bad(Lz4BadOffset{})
    case 1n+o:
      blk.copy.check(Maybe.is_some(&2, U32, B.at(acc, o)), len, o, acc, room)

def blk.off.pick(more: Bool, +off: Nat, m: U32, acc: List<&2, U32>, room: Nat, last: Nat) -> Lz4Dec:
  match more:
    case True{}:
      Lz4Dec{Lz4MatExt{off, 19n}, acc, room, last}
    case False{}:
      blk.copy(off, Nat.add(U32.to_nat(m), 4n), acc, room)

def blk.off(lo: U32, +m: U32, h: U32, acc: List<&2, U32>, room: Nat, last: Nat) -> Lz4Dec:
  blk.off.pick(U32.is_eq(m, 15), U32.to_nat(U32.or(lo, U32.shln(B.byte(h), 8n))), m, acc, room, last)

def blk.matext(e: Lz4Ext, +off: Nat, n: Nat, acc: List<&2, U32>, room: Nat, last: Nat) -> Lz4Dec:
  match e:
    case Lz4Full{}:
      Lz4Dec{Lz4MatExt{off, Nat.add(255n, n)}, acc, room, last}
    case Lz4Last{v}:
      blk.copy(off, Nat.add(v, n), acc, room)

def blk.step(d: Lz4Dec, h: U32) -> Lz4Dec:
  match d:
    case Lz4Dec{st, acc, room, last}:
      match st:
        case Lz4Tok{}:
          blk.tok(h, acc, room, last)
        case Lz4LitExt{n, m}:
          blk.litext(blk.ext(h), n, m, acc, room, last)
        case Lz4Lit{n, total, m}:
          blk.lit(n, room, total, m, h, acc, last)
        case Lz4Off{lo, m}:
          blk.off(lo, m, h, acc, room, last)
        case Lz4MatExt{off, n}:
          blk.matext(blk.ext(h), off, n, acc, room, last)
        case Lz4Bad{e}:
          blk.bad(e)

def blk.go(xs: List<&2, U32>, d: Lz4Dec) -> Lz4Dec:
  match xs:
    case Nil{}:
      d
    case Con{h, t}:
      blk.go(t, blk.step(d, h))

# End of block: the block stops right after the literals of its last sequence,
# whose token has no match part (low nibble 0). If the block has a match, its
# last 5 bytes are literals and its last match starts at least 12 bytes before
# its end: total literals after it, last its length.
def blk.end.ok(+last: Nat, +total: Nat) -> Bool:
  match last:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(Nat.is_le(5n, total), Nat.is_le(12n, Nat.add(total, last)))

def blk.end.pick(ok: Bool, acc: List<&2, U32>, room: Nat) -> Result<&2, &2, Lz4Error, Lz4Out>:
  match ok:
    case True{}:
      Done{Lz4Out{acc, room}}
    case False{}:
      Fail{Lz4BadBlockEnd{}}

def blk.end.lit(n: Nat, +total: Nat, m: U32, acc: List<&2, U32>, room: Nat, +last: Nat) -> Result<&2, &2, Lz4Error, Lz4Out>:
  match n:
    case 0n:
      blk.end.pick(Bool.and(U32.is_eq(m, 0), blk.end.ok(last, total)), acc, room)
    case 1n+p:
      Fail{Lz4Truncated{}}

def blk.end(d: Lz4Dec) -> Result<&2, &2, Lz4Error, Lz4Out>:
  match d:
    case Lz4Dec{st, acc, room, last}:
      match st:
        case Lz4Lit{n, total, m}:
          blk.end.lit(n, total, m, acc, room, last)
        case Lz4Bad{e}:
          Fail{e}
        case _:
          Fail{Lz4Truncated{}}

# decode the block src after the history hist (reversed), with room bytes
def blk.run(src: List<&2, U32>, hist: List<&2, U32>, room: Nat) -> Result<&2, &2, Lz4Error, Lz4Out>:
  blk.end(blk.go(src, Lz4Dec{Lz4Tok{}, hist, room, 0n}))

def blk.out(+k: Nat, r: Result<&2, &2, Lz4Error, Lz4Out>) -> Result<&2, &2, Lz4Error, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{Lz4Out{acc, room}}:
      Done{B.Octets.of_list(B.drop(k, blk.rev(acc)))}

# The public interface: decoding

# the bytes of the block src, at most max of them
def block_decompress(src: B.Octets, max: Nat) -> Result<&2, &2, Lz4Error, B.Octets>:
  blk.out(0n, blk.run(B.Octets.to_list(src), Nil{}, max))

# the same, for a block that may refer back into dict (the bytes before it:
# a dictionary, or the earlier blocks of a frame); answers the block's bytes
def block_decompress_dict(+dict: B.Octets, src: B.Octets, max: Nat) -> Result<&2, &2, Lz4Error, B.Octets>:
  blk.out(B.Octets.len(dict), blk.run(B.Octets.to_list(src), blk.rev(B.Octets.to_list(dict)), max))

# The encoder
#
# block_literals is the simplest valid block: one sequence, all literals, as
# any LZ4 decoder accepts. A compressor that finds matches joins the package
# as its own file beside this one.

# the last length byte: 254 - d (d counts down the room left in a byte)
def lit.last(d: Nat) -> U32:
  U32.from_nat(Nat.sub(254n, d))

# the length bytes for r more literals after a nibble of 15: a 255 for each
# full 255, then the rest
def lit.ext(r: Nat, d: Nat) -> List<&2, U32>:
  match r:
    case 0n:
      [lit.last(d)]
    case 1n+p:
      match d:
        case 0n:
          Con{255, lit.ext(p, 254n)}
        case 1n+q:
          lit.ext(p, q)

# lit.hK(n): the token and length bytes for K + n literals
def lit.h14(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [224]
    case 1n+p:
      Con{240, lit.ext(p, 254n)}

def lit.h13(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [208]
    case 1n+p:
      lit.h14(p)

def lit.h12(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [192]
    case 1n+p:
      lit.h13(p)

def lit.h11(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [176]
    case 1n+p:
      lit.h12(p)

def lit.h10(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [160]
    case 1n+p:
      lit.h11(p)

def lit.h9(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [144]
    case 1n+p:
      lit.h10(p)

def lit.h8(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [128]
    case 1n+p:
      lit.h9(p)

def lit.h7(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [112]
    case 1n+p:
      lit.h8(p)

def lit.h6(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [96]
    case 1n+p:
      lit.h7(p)

def lit.h5(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [80]
    case 1n+p:
      lit.h6(p)

def lit.h4(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [64]
    case 1n+p:
      lit.h5(p)

def lit.h3(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [48]
    case 1n+p:
      lit.h4(p)

def lit.h2(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [32]
    case 1n+p:
      lit.h3(p)

def lit.h1(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [16]
    case 1n+p:
      lit.h2(p)

def lit.h0(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [0]
    case 1n+p:
      lit.h1(p)

# a block holding the bytes o as literals
def block_literals(+o: B.Octets) -> B.Octets:
  B.Octets.append(B.Octets.of_list(lit.h0(B.Octets.len(o))), o)
