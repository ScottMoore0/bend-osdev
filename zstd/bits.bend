# bend-osdev-zstd, bitstreams (RFC 8878, section 4.1 and the descriptions
# of the Huffman and sequences streams): bit strings, their reading, and
# their packing into bytes.
#
# A bit string is a List<&2, Bool> in the order a decoder reads it. Two
# packings into bytes are used by the format:
#
# * backward bitstreams (Huffman streams, sequences, FSE-coded Huffman
#   weights): written forward, least significant bit first, then an end mark
#   (a 1 bit) and zero padding to a byte; read from the end, starting just
#   below the last byte's highest set bit, each byte from bit 7 down to bit
#   0. A field of n bits is read most significant bit first.
# * forward bitstreams (FSE table descriptions): each byte from bit 0 up to
#   bit 7; a field is read least significant bit first.
import Base
import ../bytes/bytes.bend as B

# A field read: its value and the bits after it
type ZstdBits is Data:
  ZstdBits{value: Nat, rest: List<&2, Bool>}

def ZstdBits.value(r: ZstdBits) -> Nat:
  match r:
    case ZstdBits{v, rest}:
      v

def ZstdBits.rest(r: ZstdBits) -> List<&2, Bool>:
  match r:
    case ZstdBits{v, rest}:
      rest

# 2^n
def ZstdBits.pow2(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      +h = ZstdBits.pow2(p)
      Nat.add(h, h)

def ZstdBits.bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# Reading, most significant bit first

def bits.read.go(n: Nat, bits: List<&2, Bool>, acc: Nat) -> Maybe<&2, ZstdBits>:
  match n:
    case 0n:
      Some{ZstdBits{acc, bits}}
    case 1n+p:
      match bits:
        case Nil{}:
          None{}
        case Con{b, t}:
          +a = acc
          bits.read.go(p, t, Nat.add(Nat.add(a, a), ZstdBits.bit(b)))

# the n-bit field at the start of bits (None if there are fewer bits)
def ZstdBits.read(n: Nat, bits: List<&2, Bool>) -> Maybe<&2, ZstdBits>:
  bits.read.go(n, bits, 0n)

# Reading, least significant bit first (forward bitstreams)

def bits.read_le.go(n: Nat, bits: List<&2, Bool>, +w: Nat, acc: Nat) -> Maybe<&2, ZstdBits>:
  match n:
    case 0n:
      Some{ZstdBits{acc, bits}}
    case 1n+p:
      match bits:
        case Nil{}:
          None{}
        case Con{b, t}:
          bits.read_le.go(p, t, Nat.add(w, w), Nat.add(acc, Nat.mul(ZstdBits.bit(b), w)))

def ZstdBits.read_le(n: Nat, bits: List<&2, Bool>) -> Maybe<&2, ZstdBits>:
  bits.read_le.go(n, bits, 1n, 0n)

# the little-endian U32 of the first four bytes (missing ones are 0), each
# masked to 8 bits
def ZstdBits.u32le(+xs: List<&2, U32>) -> U32:
  +g = {B.append(B.take(4n, xs), [0, 0, 0, 0]) : List<&2, U32>}
  +b0 = B.byte(Maybe.default(&2, U32, B.at(g, 0n), 0))
  +b1 = B.byte(Maybe.default(&2, U32, B.at(g, 1n), 0))
  +b2 = B.byte(Maybe.default(&2, U32, B.at(g, 2n), 0))
  +b3 = B.byte(Maybe.default(&2, U32, B.at(g, 3n), 0))
  U32.or(U32.or(b0, U32.shln(b1, 8n)), U32.or(U32.shln(b2, 16n), U32.shln(b3, 24n)))

# Bytes to bits

def bits.test(+b: U32, k: Nat) -> Bool:
  Bool.not(U32.is_eq(U32.and(U32.shrn(b, k), 1), 0))

# bits 0 to n - 1 of b pushed onto acc, bit 0 first, so that acc starts
# with bit n - 1
def bits.push_msb(n: Nat, +b: U32, +k: Nat, acc: List<&2, Bool>) -> List<&2, Bool>:
  match n:
    case 0n:
      acc
    case 1n+p:
      bits.push_msb(p, b, 1n+k, Con{bits.test(b, k), acc})

# the position of the highest set bit of a nonzero byte: k counts up
# through the bits, best is the last set one seen
def bits.top.pick(set: Bool, k: Nat, best: Nat) -> Nat:
  match set:
    case True{}:
      k
    case False{}:
      best

def bits.top.go(n: Nat, +b: U32, +k: Nat, best: Nat) -> Nat:
  match n:
    case 0n:
      best
    case 1n+p:
      bits.top.go(p, b, 1n+k, bits.top.pick(bits.test(b, k), k, best))

def bits.top(+b: U32) -> Nat:
  bits.top.go(8n, b, 0n, 0n)

# the earlier bytes (in order), each bit 7 first, in front of acc
def bits.back.go(xs: List<&2, U32>, acc: List<&2, Bool>) -> List<&2, Bool>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      bits.back.go(t, bits.push_msb(8n, B.byte(h), 0n, acc))

def bits.back.last(z: Bool, +last: U32, body: List<&2, Bool>) -> Maybe<&2, List<&2, Bool>>:
  match z:
    case True{}:
      None{}
    case False{}:
      Some{bits.push_msb(bits.top(last), last, 0n, body)}

def bits.back.split(r: List<&2, U32>) -> Maybe<&2, List<&2, Bool>>:
  match r:
    case Nil{}:
      None{}
    case Con{+last, earlier}:
      +l = B.byte(last)
      bits.back.last(U32.is_eq(l, 0), l, bits.back.go(B.rev(earlier), Nil{}))

# the bits of a backward bitstream, in reading order; None if it is empty
# or its last byte is 0 (no end mark)
def ZstdBits.backward(xs: List<&2, U32>) -> Maybe<&2, List<&2, Bool>>:
  bits.back.split(B.rev(xs))

# bits 0 to 7 of each byte, in order (a forward bitstream)
def bits.fwd.go(rs: List<&2, U32>, acc: List<&2, Bool>) -> List<&2, Bool>:
  match rs:
    case Nil{}:
      acc
    case Con{h, t}:
      +b = B.byte(h)
      bits.fwd.go(t, Con{bits.test(b, 0n), Con{bits.test(b, 1n), Con{bits.test(b, 2n), Con{bits.test(b, 3n), Con{bits.test(b, 4n), Con{bits.test(b, 5n), Con{bits.test(b, 6n), Con{bits.test(b, 7n), acc}}}}}}}})

def ZstdBits.forward(xs: List<&2, U32>) -> List<&2, Bool>:
  bits.fwd.go(B.rev(xs), Nil{})

# Writing

# n bits of v, most significant first; hi: v has bit n - 1 set (v >= 2^(n-1))
def bits.of_nat.go(+n: Nat, hi: Bool, +v: Nat) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match hi:
        case True{}:
          +v2 = Nat.sub(v, ZstdBits.pow2(p))
          Con{True{}, bits.of_nat.go(p, Nat.is_le(ZstdBits.pow2(Nat.sub(p, 1n)), v2), v2)}
        case False{}:
          Con{False{}, bits.of_nat.go(p, Nat.is_le(ZstdBits.pow2(Nat.sub(p, 1n)), v), v)}

# the n-bit field holding v (v below 2^n), most significant bit first
def ZstdBits.of_nat(+n: Nat, +v: Nat) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      bits.of_nat.go(1n+p, Nat.is_le(ZstdBits.pow2(p), v), v)

# the same, least significant bit first (forward bitstreams)
def ZstdBits.of_nat_le(n: Nat, +v: Nat) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{Nat.is_eq(Nat.mod(v, 2n), 1n), ZstdBits.of_nat_le(p, Nat.div(v, 2n))}

def bits.bv(b: Bool, v: U32) -> U32:
  match b:
    case True{}:
      v
    case False{}:
      0

# bytes of forward bits (least significant first), the last padded with
# zeros; acc: the bytes so far, reversed
def bits.pack.go(bits: List<&2, Bool>, acc: List<&2, U32>) -> List<&2, U32>:
  match bits:
    case Con{b0, Con{b1, Con{b2, Con{b3, Con{b4, Con{b5, Con{b6, Con{b7, t}}}}}}}}:
      +v = U32.or(U32.or(U32.or(bits.bv(b0, 1), bits.bv(b1, 2)), U32.or(bits.bv(b2, 4), bits.bv(b3, 8))), U32.or(U32.or(bits.bv(b4, 16), bits.bv(b5, 32)), U32.or(bits.bv(b6, 64), bits.bv(b7, 128))))
      bits.pack.go(t, Con{v, acc})
    case _:
      B.rev(acc)

# k zero bits after bits
def bits.zeros(k: Nat, acc: List<&2, Bool>) -> List<&2, Bool>:
  match k:
    case 0n:
      acc
    case 1n+p:
      bits.zeros(p, Con{False{}, acc})

def bits.len.go(bits: List<&2, Bool>, n: Nat) -> Nat:
  match bits:
    case Nil{}:
      n
    case Con{h, t}:
      bits.len.go(t, 1n+n)

# the number of bits (tail-recursive)
def ZstdBits.len(bits: List<&2, Bool>) -> Nat:
  bits.len.go(bits, 0n)

# the bytes of a forward bitstream holding bits (zero padded to a byte)
def ZstdBits.pack_forward(+bits: List<&2, Bool>) -> List<&2, U32>:
  +pad = Nat.mod(Nat.sub(8n, Nat.mod(ZstdBits.len(bits), 8n)), 8n)
  bits.pack.go(List.reverse.go(&2, Bool, List.reverse(&2, Bool, bits), bits.zeros(pad, Nil{})), Nil{})

# the bytes of a backward bitstream a reader meets bits in: the bits
# reversed, the end mark, zero padding
def ZstdBits.pack_backward(bits: List<&2, Bool>) -> List<&2, U32>:
  ZstdBits.pack_forward(List.reverse.go(&2, Bool, bits, [True{}]))
