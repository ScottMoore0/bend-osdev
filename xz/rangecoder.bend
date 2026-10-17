# bend-osdev-xz: the LZMA range decoder, with its adaptive probabilities.
#
# Written from the LZMA specification in the LZMA SDK ("lzma-specification",
# Igor Pavlov, public domain): the range decoder of section "The range
# decoder", bit trees and reverse bit trees, and direct bits.
#
# An XzRd holds the decoder's range and code, the input still to read, the
# probability array (11-bit probabilities, 1024 = one half), and ok, which
# turns False once the decoder sees corruption: the input runs out, the first
# byte is not 0, or the code reaches the range. The caller checks ok (and that
# the code is 0) when the data is meant to end: XzRd.finish.
import Base

type XzRd is Type:
  XzRd{probs: Array<U32>, range: U32, code: U32, input: List<&2, U32>, ok: Bool}

# a decoded bit, and the decoder after it
type XzBit is Type:
  XzBit{rd: XzRd, bit: Bool}

# a decoded value, and the decoder after it
type XzSym is Type:
  XzSym{rd: XzRd, value: U32}

# the probability array: 2^14 slots, each one half
def XzRd.fresh() -> Array<U32>:
  Array.new(U32, 14n, 1024)

def XzRd.bitval(b: Bool) -> U32:
  match b:
    case True{}:
      1
    case False{}:
      0

# Starting: one byte that must be 0, then the code, big-endian
def XzRd.start.go(probs: Array<U32>, input: List<&2, U32>) -> XzRd:
  match input:
    case Con{b0, Con{b1, Con{b2, Con{b3, Con{b4, t}}}}}:
      +code = U32.or(U32.shln(U32.and(b1, 255), 24n), U32.or(U32.shln(U32.and(b2, 255), 16n), U32.or(U32.shln(U32.and(b3, 255), 8n), U32.and(b4, 255))))
      XzRd{probs, 4294967295, code, t, Bool.and(U32.is_eq(U32.and(b0, 255), 0), Bool.not(U32.is_eq(code, 4294967295)))}
    case _:
      XzRd{probs, 4294967295, 0, Nil{}, False{}}

# a range decoder over input, with the probabilities probs
def XzRd.start(probs: Array<U32>, input: List<&2, U32>) -> XzRd:
  XzRd.start.go(probs, input)

# Normalising: below 2^24, the range takes in another byte
def XzRd.norm.go(small: Bool, probs: Array<U32>, +range: U32, +code: U32, input: List<&2, U32>, ok: Bool) -> XzRd:
  match small:
    case False{}:
      XzRd{probs, range, code, input, ok}
    case True{}:
      match input:
        case Nil{}:
          XzRd{probs, U32.shln(range, 8n), U32.shln(code, 8n), Nil{}, False{}}
        case Con{h, t}:
          XzRd{probs, U32.shln(range, 8n), U32.or(U32.shln(code, 8n), U32.and(h, 255)), t, ok}

def XzRd.norm(probs: Array<U32>, +range: U32, +code: U32, input: List<&2, U32>, ok: Bool) -> XzRd:
  XzRd.norm.go(U32.is_lt(range, 16777216), probs, range, code, input, ok)

# One bit with the probability at index i, which adapts towards the bit
def XzRd.bit.pick(zero: Bool, probs: Array<U32>, +i: U32, +p: U32, +bound: U32, +range: U32, +code: U32, input: List<&2, U32>, ok: Bool) -> XzBit:
  match zero:
    case True{}:
      XzBit{XzRd.norm(Array.set(U32, probs, i, U32.add(p, U32.shrn(U32.sub(2048, p), 5n))), bound, code, input, ok), False{}}
    case False{}:
      XzBit{XzRd.norm(Array.set(U32, probs, i, U32.sub(p, U32.shrn(p, 5n))), U32.sub(range, bound), U32.sub(code, bound), input, ok), True{}}

def XzRd.bit.go(pp: Array<U32> & U32, +i: U32, +range: U32, +code: U32, input: List<&2, U32>, ok: Bool) -> XzBit:
  (probs, +p) = pp
  +bound = U32.mul(U32.shrn(range, 11n), p)
  XzRd.bit.pick(U32.is_lt(code, bound), probs, i, p, bound, range, code, input, ok)

def XzRd.bit(d: XzRd, +i: U32) -> XzBit:
  XzRd{probs, +range, +code, input, ok} = d
  XzRd.bit.go(Array.get(U32, probs, i), i, range, code, input, ok)

# Bit trees: r holds the bit decoded with the probability at base + m, and n
# more bits follow; the answer keeps the leading 1
def XzRd.tree.go(n: Nat, r: XzBit, +base: U32, +m: U32) -> XzSym:
  match n:
    case 0n:
      XzBit{rd, b} = r
      XzSym{rd, U32.add(U32.shl(m), XzRd.bitval(b))}
    case 1n+p:
      XzBit{rd, b} = r
      +m2 = U32.add(U32.shl(m), XzRd.bitval(b))
      XzRd.tree.go(p, XzRd.bit(rd, U32.add(base, m2)), base, m2)

def XzRd.minus(r: XzSym, +k: U32) -> XzSym:
  XzSym{rd, v} = r
  XzSym{rd, U32.sub(v, k)}

def XzRd.plus(r: XzSym, +k: U32) -> XzSym:
  XzSym{rd, v} = r
  XzSym{rd, U32.add(v, k)}

# an n-bit value, most significant bit first, from the tree at base
def XzRd.tree(d: XzRd, +base: U32, +n: Nat) -> XzSym:
  match n:
    case 0n:
      XzSym{d, 0}
    case 1n+p:
      XzRd.minus(XzRd.tree.go(p, XzRd.bit(d, U32.add(base, 1)), base, 1), U32.shln(1, 1n+p))

# Reverse bit trees: the same walk, but the first bit is the least significant;
# r's bit is bit k of the value
def XzRd.rev.go(n: Nat, r: XzBit, +base: U32, +m: U32, +k: Nat, +acc: U32) -> XzSym:
  match n:
    case 0n:
      XzBit{rd, b} = r
      XzSym{rd, U32.or(acc, U32.shln(XzRd.bitval(b), k))}
    case 1n+p:
      XzBit{rd, b} = r
      +v = XzRd.bitval(b)
      +m2 = U32.add(U32.shl(m), v)
      XzRd.rev.go(p, XzRd.bit(rd, U32.add(base, m2)), base, m2, 1n+k, U32.or(acc, U32.shln(v, k)))

# an n-bit value, least significant bit first, from the tree at base
def XzRd.rev(d: XzRd, +base: U32, n: Nat) -> XzSym:
  match n:
    case 0n:
      XzSym{d, 0}
    case 1n+p:
      XzRd.rev.go(p, XzRd.bit(d, U32.add(base, 1)), base, 1, 0n, 0)

# Direct bits: n bits of probability one half, most significant first
def XzRd.direct.go(n: Nat, d: XzRd, +acc: U32) -> XzSym:
  match n:
    case 0n:
      XzSym{d, acc}
    case 1n+p:
      XzRd{probs, +range, +code, input, ok} = d
      +r2 = U32.shr(range)
      +c2 = U32.sub(code, r2)
      +t = U32.sub(0, U32.shrn(c2, 31n))
      +c3 = U32.add(c2, U32.and(r2, t))
      XzRd.direct.go(p, XzRd.norm(probs, r2, c3, input, Bool.and(ok, Bool.not(U32.is_eq(c3, r2)))), U32.add(U32.shl(acc), U32.add(t, 1)))

def XzRd.direct(d: XzRd, n: Nat) -> XzSym:
  XzRd.direct.go(n, d, 0)

# The end: the probabilities back, and whether the data ended cleanly (no
# corruption seen, every input byte read, and the code at 0)
def XzRd.finish.go(input: List<&2, U32>, probs: Array<U32>, +code: U32, ok: Bool) -> Array<U32> & Bool:
  match input:
    case Nil{}:
      (probs, Bool.and(ok, U32.is_eq(code, 0)))
    case Con{h, t}:
      (probs, False{})

def XzRd.finish(d: XzRd) -> Array<U32> & Bool:
  XzRd{probs, range, +code, input, ok} = d
  XzRd.finish.go(input, probs, code, ok)
