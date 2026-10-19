# bend-osdev-deflate: bits, as DEFLATE packs them (RFC 1951, 3.1.1, "Packing
# into bytes"): "Data elements are packed into bytes in order of increasing
# bit number within the byte, i.e., starting with the least-significant bit
# of the byte"; data elements other than Huffman codes are "packed starting
# with the least-significant bit of the data element"; Huffman codes are
# "packed starting with the most-significant bit of the code".
#
# The reader is incremental: the inflater is handed a byte at a time (so it
# can be fed a stream in pieces), splits it into its eight bits, low bit
# first (bits.of), and gathers each field one bit at a time (bits.field).
# A Huffman code is walked one bit at a time down its tree (huffman.bend), so
# its bits need no reversing.
#
# The writer keeps the whole bytes written (reversed) and the bits of the
# byte being filled; put writes a field low bit first, which is also how a
# Huffman code is written once its bits are stored in the order they are
# sent (huffman.bend's tables keep them so).
import Base
import ../bytes/bytes.bend as B

# The reader

# the eight bits of a byte, the least significant first
type DflByteBits is Data:
  DflByteBits{b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool}

def bits.of(h: U32) -> DflByteBits:
  match h:
    case U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, hi}}}}}}}}}:
      DflByteBits{c0, c1, c2, c3, c4, c5, c6, c7}

# a field read so far (v), with one more bit at position sh
def bits.field(v: U32, sh: Nat, b: Bool) -> U32:
  match b:
    case True{}:
      U32.or(v, U32.shln(1, sh))
    case False{}:
      v

# The writer

# acc: the whole bytes written, reversed; cur: the n bits (0 to 7) of the
# byte being filled, in its low bits
type DflOut is Data:
  DflOut{acc: List<&2, U32>, cur: U32, n: Nat}

def out.new() -> DflOut:
  DflOut{Nil{}, 0, 0n}

# the low k bits of a word
def out.mask(+v: U32, k: Nat) -> U32:
  U32.and(v, U32.sub(U32.shln(1, k), 1))

# whole bytes move from cur to acc while there are 8 bits or more
def out.flush(fuel: Nat, full: Bool, acc: List<&2, U32>, +cur: U32, +m: Nat) -> DflOut:
  match fuel:
    case 0n:
      DflOut{acc, cur, m}
    case 1n+f:
      match full:
        case True{}:
          +m2 = Nat.sub(m, 8n)
          out.flush(f, Nat.is_le(8n, m2), Con{U32.and(cur, 255), acc}, U32.shrn(cur, 8n), m2)
        case False{}:
          DflOut{acc, cur, m}

# the low k bits of v (k at most 24), the least significant first
def out.put(w: DflOut, +v: U32, +k: Nat) -> DflOut:
  match w:
    case DflOut{acc, cur, +n}:
      +m = Nat.add(n, k)
      out.flush(4n, Nat.is_le(8n, m), acc, U32.or(cur, U32.shln(out.mask(v, k), n)), m)

# one bit
def out.bit(w: DflOut, b: Bool) -> DflOut:
  match b:
    case True{}:
      out.put(w, 1, 1n)
    case False{}:
      out.put(w, 0, 1n)

# zero bits up to the next byte boundary
def out.align(w: DflOut) -> DflOut:
  match w:
    case DflOut{acc, cur, n}:
      match n:
        case 0n:
          DflOut{acc, cur, 0n}
        case 1n+p:
          DflOut{Con{U32.and(cur, 255), acc}, 0, 0n}

# whole bytes, at a byte boundary (after out.align)
def out.bytes(w: DflOut, xs: List<&2, U32>) -> DflOut:
  match w:
    case DflOut{acc, cur, n}:
      DflOut{B.rev_onto(xs, acc), cur, n}

# how many bits have been written
def out.bits(w: DflOut) -> Nat:
  match w:
    case DflOut{acc, cur, n}:
      Nat.add(Nat.mul(B.len.fast(acc), 8n), n)

# the bytes written, padded with zero bits to a whole byte
def out.finish.of(w: DflOut) -> List<&2, U32>:
  match w:
    case DflOut{acc, cur, n}:
      B.rev(acc)

def out.finish(w: DflOut) -> List<&2, U32>:
  out.finish.of(out.align(w))

# the whole bytes written so far (in order), and the writer without them
type DflOutTake is Data:
  DflOutTake{bytes: List<&2, U32>, out: DflOut}

def out.take(w: DflOut) -> DflOutTake:
  match w:
    case DflOut{acc, cur, n}:
      DflOutTake{B.rev(acc), DflOut{Nil{}, cur, n}}
