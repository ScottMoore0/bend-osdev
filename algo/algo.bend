# bend-osdev-algo: the small algorithms an operating system kernel uses
# everywhere. This file: bit search in a word.
#
# Bit search works on the bits of Base's Word(n) (least significant bit
# first), generic in the width, so that one proof covers U32 and W64:
#
#   popcount   the number of set bits (the kernel's hweight)
#   ffs        1 + the index of the lowest set bit, 0 for zero (the kernel's
#              and C's ffs)
#   fls        1 + the index of the highest set bit, 0 for zero (the
#              kernel's fls)
#   first_set  the index of the lowest set bit, None for zero (__ffs)
#   last_set   the index of the highest set bit, None for zero (__fls)
#   ctz        the number of zero bits below the lowest set bit (the width
#              for zero)
#   clz        the number of zero bits above the highest set bit (the width
#              for zero)
#
# Bitmaps are in bitmap.bend, binary search in bsearch.bend.
import Base
import ../word64/word64.bend as W

# Bits of a word of any width

# bit k (False at or past the width)
def bitw.test(n: Nat, w: Word(n), k: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match w k:
        case WCon{b, t} 0n:
          b
        case WCon{b, t} 1n+j:
          bitw.test(p, t, j)

def bitw.popcount.step(b: Bool, k: Nat) -> Nat:
  match b:
    case True{}:
      1n+k
    case False{}:
      k

def bitw.popcount(n: Nat, w: Word(n)) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match w:
        case WCon{b, t}:
          bitw.popcount.step(b, bitw.popcount(p, t))

# k is ffs of the bits above the lowest one
def bitw.ffs.step(b: Bool, k: Nat) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      match k:
        case 0n:
          0n
        case 1n+j:
          2n+j

def bitw.ffs(n: Nat, w: Word(n)) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match w:
        case WCon{b, t}:
          bitw.ffs.step(b, bitw.ffs(p, t))

# k is fls of the bits above the lowest one
def bitw.fls.step(k: Nat, b: Bool) -> Nat:
  match k:
    case 0n:
      match b:
        case True{}:
          1n
        case False{}:
          0n
    case 1n+j:
      2n+j

def bitw.fls(n: Nat, w: Word(n)) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match w:
        case WCon{b, t}:
          bitw.fls.step(bitw.fls(p, t), b)

def bitw.ctz.step(b: Bool, k: Nat) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n+k

def bitw.ctz(n: Nat, w: Word(n)) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match w:
        case WCon{b, t}:
          bitw.ctz.step(b, bitw.ctz(p, t))

def bitw.clz(+n: Nat, w: Word(n)) -> Nat:
  Nat.sub(n, bitw.fls(n, w))

# a 1-based position (ffs, fls) as a 0-based index
def bitw.index(m: Nat) -> Maybe<&2, Nat>:
  match m:
    case 0n:
      None{}
    case 1n+k:
      Some{k}

# the bits of w, least significant first, in front of rest
def bitw.to_list(n: Nat, w: Word(n), rest: List<&2, Bool>) -> List<&2, Bool>:
  match n:
    case 0n:
      rest
    case 1n+p:
      match w:
        case WCon{b, t}:
          Con{b, bitw.to_list(p, t, rest)}

# U32

def bits32.word(x: U32) -> Word(32n):
  match x:
    case U32{w}:
      w

# bit k of x (False for k >= 32)
def bits32.test(x: U32, k: Nat) -> Bool:
  bitw.test(32n, bits32.word(x), k)

def bits32.popcount(x: U32) -> Nat:
  bitw.popcount(32n, bits32.word(x))

def bits32.ffs(x: U32) -> Nat:
  bitw.ffs(32n, bits32.word(x))

def bits32.fls(x: U32) -> Nat:
  bitw.fls(32n, bits32.word(x))

def bits32.first_set(x: U32) -> Maybe<&2, Nat>:
  bitw.index(bits32.ffs(x))

def bits32.last_set(x: U32) -> Maybe<&2, Nat>:
  bitw.index(bits32.fls(x))

def bits32.ctz(x: U32) -> Nat:
  bitw.ctz(32n, bits32.word(x))

def bits32.clz(x: U32) -> Nat:
  bitw.clz(32n, bits32.word(x))

# W64: the low 32 bits, then the high 32

def bits64.word(+a: W.W64) -> Word(64n):
  W.W64.bits.cat(32n, 32n, bits32.word(W.W64.lo(a)), bits32.word(W.W64.hi(a)))

# bit k of a (False for k >= 64)
def bits64.test(a: W.W64, k: Nat) -> Bool:
  bitw.test(64n, bits64.word(a), k)

def bits64.popcount(a: W.W64) -> Nat:
  bitw.popcount(64n, bits64.word(a))

def bits64.ffs(a: W.W64) -> Nat:
  bitw.ffs(64n, bits64.word(a))

def bits64.fls(a: W.W64) -> Nat:
  bitw.fls(64n, bits64.word(a))

def bits64.first_set(a: W.W64) -> Maybe<&2, Nat>:
  bitw.index(bits64.ffs(a))

def bits64.last_set(a: W.W64) -> Maybe<&2, Nat>:
  bitw.index(bits64.fls(a))

def bits64.ctz(a: W.W64) -> Nat:
  bitw.ctz(64n, bits64.word(a))

def bits64.clz(a: W.W64) -> Nat:
  bitw.clz(64n, bits64.word(a))
