# bend-osdev-word64: unsigned 64-bit words for bend-osdev, wrapping on overflow.
#
# Every bend-osdev package that needs 64 bits uses W64, and only through these
# defs. W64 stores bend-kit-int's U64 today; when Base gains a native U64
# (bendlang/bend#1027), only this file changes. The type is not named U64, so
# that it cannot clash with Base's when it arrives.
import Base
import bend-kit-int@0.2.0.0/int.bend as Int

type W64 is Data:
  W64{v: Int.U64}

def W64.zero() -> W64:
  W64{Int.U64.from_u32(0)}

def W64.one() -> W64:
  W64{Int.U64.from_u32(1)}

def W64.max() -> W64:
  W64{Int.U64.MAX()}

# Conversions

def W64.from_u32(a: U32) -> W64:
  W64{Int.U64.from_u32(a)}

# Splitting a Word(m + n) into its low m and high n bits (bits are stored
# least significant first), and joining them back. Named under W64, not Word,
# so that they cannot clash with Base if it gains Word.lo, Word.hi or Word.cat.
def W64.bits.lo(m: Nat, n: Nat, w: Word(Nat.add(m, n))) -> Word(m):
  match m:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{h, t}:
          WCon{h, W64.bits.lo(p, n, t)}

def W64.bits.hi(m: Nat, n: Nat, w: Word(Nat.add(m, n))) -> Word(n):
  match m:
    case 0n:
      w
    case 1n+p:
      match w:
        case WCon{h, t}:
          W64.bits.hi(p, n, t)

def W64.bits.cat(m: Nat, n: Nat, a: Word(m), b: Word(n)) -> Word(Nat.add(m, n)):
  match m:
    case 0n:
      b
    case 1n+p:
      match a:
        case WCon{h, t}:
          WCon{h, W64.bits.cat(p, n, t, b)}

# the low 32 bits
def W64.lo(a: W64) -> U32:
  match a:
    case W64{Int.U64{w}}:
      U32{W64.bits.lo(32n, 32n, w)}

# the high 32 bits
def W64.hi(a: W64) -> U32:
  match a:
    case W64{Int.U64{w}}:
      U32{W64.bits.hi(32n, 32n, w)}

# the word whose high and low 32 bits are hi and lo
def W64.from_parts(hi: U32, lo: U32) -> W64:
  match hi lo:
    case U32{h} U32{l}:
      W64{Int.U64{W64.bits.cat(32n, 32n, l, h)}}

def W64.to_nat(a: W64) -> Nat:
  match a:
    case W64{x}:
      Int.U64.to_nat(x)

# k mod 2^64
def W64.from_nat(k: Nat) -> W64:
  W64{Int.U64.from_nat(k)}

# Arithmetic, modulo 2^64

def W64.add(a: W64, b: W64) -> W64:
  match a b:
    case W64{x} W64{y}:
      W64{Int.U64.add(x, y)}

def W64.sub(a: W64, b: W64) -> W64:
  match a b:
    case W64{x} W64{y}:
      W64{Int.U64.sub(x, y)}

def W64.mul(a: W64, b: W64) -> W64:
  match a b:
    case W64{x} W64{y}:
      W64{Int.U64.mul(x, y)}

# division and remainder; by zero, as bend-kit-int defines it
def W64.div(a: W64, b: W64) -> W64:
  match a b:
    case W64{x} W64{y}:
      W64{Int.U64.div(x, y)}

def W64.mod(a: W64, b: W64) -> W64:
  match a b:
    case W64{x} W64{y}:
      W64{Int.U64.mod(x, y)}

# Bits

def W64.and(a: W64, b: W64) -> W64:
  match a b:
    case W64{x} W64{y}:
      W64{Int.U64.and(x, y)}

def W64.or(a: W64, b: W64) -> W64:
  match a b:
    case W64{x} W64{y}:
      W64{Int.U64.or(x, y)}

def W64.xor(a: W64, b: W64) -> W64:
  match a b:
    case W64{x} W64{y}:
      W64{Int.U64.xor(x, y)}

def W64.not(a: W64) -> W64:
  match a:
    case W64{x}:
      W64{Int.U64.not(x)}

def W64.shl(a: W64, k: Nat) -> W64:
  match a:
    case W64{x}:
      W64{Int.U64.shl(x, k)}

def W64.shr(a: W64, k: Nat) -> W64:
  match a:
    case W64{x}:
      W64{Int.U64.shr(x, k)}

# Comparisons

def W64.cmp(a: W64, b: W64) -> Cmp:
  match a b:
    case W64{x} W64{y}:
      Int.U64.cmp(x, y)

def W64.is_eq(a: W64, b: W64) -> Bool:
  Cmp.is_eq(W64.cmp(a, b))

def W64.is_lt(a: W64, b: W64) -> Bool:
  Cmp.is_lt(W64.cmp(a, b))

def W64.is_le(a: W64, b: W64) -> Bool:
  Cmp.is_le(W64.cmp(a, b))

def W64.is_gt(a: W64, b: W64) -> Bool:
  Cmp.is_gt(W64.cmp(a, b))

def W64.is_ge(a: W64, b: W64) -> Bool:
  Cmp.is_ge(W64.cmp(a, b))

def W64.is_zero(a: W64) -> Bool:
  W64.is_eq(a, W64.zero())

# Text

def W64.show(a: W64) -> String:
  match a:
    case W64{x}:
      Int.U64.show(x)

# the 16 hex digits, lower case, most significant first
def W64.hex.pick(lt: Bool, d: U32) -> Char:
  match lt:
    case True{}:
      Chr{U32.add(48, d)}
    case False{}:
      Chr{U32.add(87, d)}

def W64.hex.digit(+d: U32) -> Char:
  W64.hex.pick(U32.is_lt(d, 10), d)

def W64.hex.go(n: Nat, +a: W64, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      W64.hex.go(p, W64.shr(a, 4n), SCon{W64.hex.digit(U32.and(W64.lo(a), 15)), acc})

def W64.show_hex(a: W64) -> String:
  W64.hex.go(16n, a, "")
