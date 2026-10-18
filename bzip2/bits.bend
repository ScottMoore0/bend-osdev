# bend-osdev-bzip2: bits, most significant first, as the bzip2 format packs
# them (Tsai, "BZip2 Format Specification", section 2: every field and code
# is a run of bits, the high bit of each byte first, with no alignment
# between fields; a stream is padded to a whole byte at its end).
#
# The reader answers 0 for every bit past the end of its input and records
# that it went past (bits.over), so a caller checks once, after a block,
# rather than after every bit.
import Base
import ../bytes/bytes.bend as B
import ./list.bend as L

# rest: the bytes not yet loaded; cur: the byte being read; mask: its next
# bit (128 down to 1; 0 when it is used up); left: how many bytes rest holds;
# over: a read went past the end of the input
type Bzip2Bits is Data:
  Bzip2Bits{rest: List<&2, U32>, cur: U32, mask: U32, left: Nat, over: Bool}

# a reader after a read, and the value read
type Bzip2Got is Data:
  Bzip2Got{bits: Bzip2Bits, v: U32}

def bits.start(+xs: List<&2, U32>) -> Bzip2Bits:
  Bzip2Bits{xs, 0, 0, L.bz.len(xs), False{}}

def bits.b(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

def bits.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# the next byte's high bit
def bits.load(rest: List<&2, U32>, left: Nat, over: Bool) -> Bzip2Got:
  match rest:
    case Nil{}:
      Bzip2Got{Bzip2Bits{Nil{}, 0, 0, 0n, True{}}, 0}
    case Con{h, t}:
      +c = B.byte(h)
      Bzip2Got{Bzip2Bits{t, c, 64, bits.pred(left), over}, U32.shrn(c, 7n)}

def bits.take(empty: Bool, rest: List<&2, U32>, +cur: U32, +mask: U32, left: Nat, over: Bool) -> Bzip2Got:
  match empty:
    case True{}:
      bits.load(rest, left, over)
    case False{}:
      Bzip2Got{Bzip2Bits{rest, cur, U32.shr(mask), left, over}, bits.b(U32.is_ne(U32.and(cur, mask), 0))}

# one bit
def bits.bit(r: Bzip2Bits) -> Bzip2Got:
  match r:
    case Bzip2Bits{rest, +cur, +mask, left, over}:
      bits.take(U32.is_eq(mask, 0), rest, cur, mask, left, over)

# a reader after a one-bit read, and the bit
type Bzip2Flag is Data:
  Bzip2Flag{bits: Bzip2Bits, b: Bool}

def bits.flag.of(g: Bzip2Got) -> Bzip2Flag:
  match g:
    case Bzip2Got{r, v}:
      Bzip2Flag{r, U32.is_eq(v, 1)}

# one bit, as a Bool
def bits.flag(r: Bzip2Bits) -> Bzip2Flag:
  bits.flag.of(bits.bit(r))

def bits.read.add(g: Bzip2Got, v: U32) -> Bzip2Got:
  match g:
    case Bzip2Got{r, x}:
      Bzip2Got{r, U32.or(U32.shl(v), x)}

def bits.read.go(n: Nat, g: Bzip2Got) -> Bzip2Got:
  match n:
    case 0n:
      g
    case 1n+p:
      match g:
        case Bzip2Got{r, v}:
          bits.read.go(p, bits.read.add(bits.bit(r), v))

# n bits (at most 32), the first read the most significant
def bits.read(n: Nat, r: Bzip2Bits) -> Bzip2Got:
  bits.read.go(n, Bzip2Got{r, 0})

# the rest of the current byte skipped: the reader is at a byte boundary
def bits.align(r: Bzip2Bits) -> Bzip2Bits:
  match r:
    case Bzip2Bits{rest, cur, mask, left, over}:
      Bzip2Bits{rest, 0, 0, left, over}

def bits.over(r: Bzip2Bits) -> Bool:
  match r:
    case Bzip2Bits{rest, cur, mask, left, over}:
      over

# how many whole bytes are left to load (an upper bound for loops)
def bits.left(r: Bzip2Bits) -> Nat:
  match r:
    case Bzip2Bits{rest, cur, mask, left, over}:
      left

# the bytes after the current one (meaningful after bits.align)
def bits.rest(r: Bzip2Bits) -> List<&2, U32>:
  match r:
    case Bzip2Bits{rest, cur, mask, left, over}:
      rest

# The writer: acc holds the whole bytes written, reversed; cur the n bits
# (fewer than 8) of the byte being built

type Bzip2Out is Data:
  Bzip2Out{acc: List<&2, U32>, cur: U32, n: Nat}

def out.new() -> Bzip2Out:
  Bzip2Out{Nil{}, 0, 0n}

def out.put(full: Bool, acc: List<&2, U32>, +c: U32, n: Nat) -> Bzip2Out:
  match full:
    case True{}:
      Bzip2Out{Con{c, acc}, 0, 0n}
    case False{}:
      Bzip2Out{acc, c, n}

# one bit (b is 0 or 1)
def out.bit(w: Bzip2Out, b: U32) -> Bzip2Out:
  match w:
    case Bzip2Out{acc, cur, n}:
      +m = {1n+n : Nat}
      out.put(Nat.is_eq(m, 8n), acc, U32.or(U32.shl(cur), b), m)

def out.bits.go(l: Nat, +v: U32, +m: U32, w: Bzip2Out) -> Bzip2Out:
  match l:
    case 0n:
      w
    case 1n+p:
      out.bits.go(p, v, U32.shr(m), out.bit(w, bits.b(U32.is_ne(U32.and(v, m), 0))))

# the low l bits of v (l at most 32), the most significant first
def out.bits(w: Bzip2Out, +l: Nat, v: U32) -> Bzip2Out:
  out.bits.go(l, v, U32.shln(1, Nat.sub(l, 1n)), w)

# the bits written, padded with 0 bits to a whole byte
def out.finish(w: Bzip2Out) -> List<&2, U32>:
  match w:
    case Bzip2Out{acc, cur, n}:
      match n:
        case 0n:
          L.bz.rev(acc)
        case 1n+p:
          L.bz.rev(Con{U32.shln(cur, Nat.sub(8n, 1n+p)), acc})

# the bytes written so far, reversed, and the bits pending (for a writer
# that hands out whole bytes as it goes)
def out.take(w: Bzip2Out) -> List<&2, U32> & Bzip2Out:
  match w:
    case Bzip2Out{acc, cur, n}:
      (acc, Bzip2Out{Nil{}, cur, n})
