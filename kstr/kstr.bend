# bend-osdev-kstr: string conversions for kernel-style text. This file:
# strict number parsing, in the manner of the kernel's kstrtox (kstrtouint,
# kstrtoull, kstrtoint, kstrtoll, kstrtobool), as its documentation states:
# the whole string must be the number, with one optional trailing newline;
# a leading '+' (and, for the signed forms, '-'); base 8, 10 or 16, or 0 to
# take it from the prefix ("0x" or "0X" and a hex digit: 16; a leading "0":
# 8; else 10); in base 16 an optional "0x" prefix; at least one digit; and a
# value that does not fit is refused, never wrapped.
#
# The other concerns: format.bend (number formatting, a vsprintf subset),
# hexdump.bend (hex_dump_to_buffer lines) and options.bend (match_token).
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B

type KStrError is Data:
  KStrEmpty{}
  KStrBadChar{pos: Nat}
  KStrRange{}
  KStrBadFormat{pos: Nat}
  KStrMissingArg{}

# A byte, classified once: parsing decides on these constructors only

type KStrTok is Data:
  KTDigit{v: U32}
  KTPlus{}
  KTMinus{}
  KTNewline{}
  KTX{}
  KTOther{c: U32}

def kstr.tok.other(plus: Bool, minus: Bool, nl: Bool, x: Bool, +c: U32) -> KStrTok:
  match plus minus nl x:
    case True{} _ _ _:
      KTPlus{}
    case False{} True{} _ _:
      KTMinus{}
    case False{} False{} True{} _:
      KTNewline{}
    case False{} False{} False{} True{}:
      KTX{}
    case False{} False{} False{} False{}:
      KTOther{c}

# '0'-'9', 'a'-'f' and 'A'-'F' are digits (0 to 15); '+', '-', '\n', 'x'
# and 'X' are their own kind
def kstr.tok.pick(dec: Bool, lo: Bool, up: Bool, +c: U32) -> KStrTok:
  match dec lo up:
    case True{} _ _:
      KTDigit{U32.sub(c, 48)}
    case False{} True{} _:
      KTDigit{U32.sub(c, 87)}
    case False{} False{} True{}:
      KTDigit{U32.sub(c, 55)}
    case False{} False{} False{}:
      kstr.tok.other(U32.is_eq(c, 43), U32.is_eq(c, 45), U32.is_eq(c, 10), Bool.or(U32.is_eq(c, 120), U32.is_eq(c, 88)), c)

def kstr.in(+c: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_le(lo, c), U32.is_le(c, hi))

def KStr.tok(+c: U32) -> KStrTok:
  kstr.tok.pick(kstr.in(c, 48, 57), kstr.in(c, 97, 102), kstr.in(c, 65, 70), c)

def kstr.toks(xs: List<&2, U32>) -> List<&2, KStrTok>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{KStr.tok(h), kstr.toks(t)}

# One trailing newline is dropped
def kstr.strip_nl(ts: List<&2, KStrTok>) -> List<&2, KStrTok>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{KTNewline{}, Nil{}}:
      Nil{}
    case Con{h, t}:
      Con{h, kstr.strip_nl(t)}

# The digits, into a 32-bit accumulator: base 16 and base 8 shift the digit
# in (refusing a value whose top nibble or top three bits are set), other
# bases multiply in 64 bits and refuse past 2^32 - 1

# acc * 16 + d, for d below 16 and acc below 2^28
def kstr.ins4(acc: U32, d: U32) -> U32:
  match acc d:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, r}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{d0, WCon{d1, WCon{d2, WCon{d3, s}}}}}:
      U32{WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

def kstr.ok(fits: Bool, +v: U32) -> Result<&2, &2, KStrError, U32>:
  match fits:
    case True{}:
      Done{v}
    case False{}:
      Fail{KStrRange{}}

def kstr.mul.fin(+p: W.W64) -> Result<&2, &2, KStrError, U32>:
  kstr.ok(U32.is_eq(W.W64.hi(p), 0), W.W64.lo(p))

def kstr.acc.pick(sixteen: Bool, eight: Bool, +base: U32, +acc: U32, +d: U32) -> Result<&2, &2, KStrError, U32>:
  match sixteen eight:
    case True{} _:
      kstr.ok(U32.is_eq(U32.shrn(acc, 28n), 0), kstr.ins4(acc, d))
    case False{} True{}:
      kstr.ok(U32.is_eq(U32.shrn(acc, 29n), 0), U32.or(U32.shln(acc, 3n), d))
    case False{} False{}:
      kstr.mul.fin(W.W64.add(W.W64.mul(W.W64.from_u32(acc), W.W64.from_u32(base)), W.W64.from_u32(d)))

def kstr.step.digit(ok: Bool, +base: U32, +acc: U32, +d: U32, +pos: Nat) -> Result<&2, &2, KStrError, U32>:
  match ok:
    case True{}:
      kstr.acc.pick(U32.is_eq(base, 16), U32.is_eq(base, 8), base, acc, d)
    case False{}:
      Fail{KStrBadChar{pos}}

# one token at position pos into acc
def kstr.step(+base: U32, t: KStrTok, +acc: U32, +pos: Nat) -> Result<&2, &2, KStrError, U32>:
  match t:
    case KTDigit{+d}:
      kstr.step.digit(U32.is_lt(d, base), base, acc, d, pos)
    case o:
      Fail{KStrBadChar{pos}}

def kstr.digits(ts: List<&2, KStrTok>, +base: U32, r: Result<&2, &2, KStrError, U32>, +pos: Nat) -> Result<&2, &2, KStrError, U32>:
  match ts:
    case Nil{}:
      r
    case Con{t, rest}:
      match r:
        case Done{+acc}:
          kstr.digits(rest, base, kstr.step(base, t, acc, pos), 1n+pos)
        case Fail{e}:
          Fail{e}

def kstr.s32.fin(neg: Bool, +v: U32) -> Result<&2, &2, KStrError, U32>:
  match neg:
    case True{}:
      kstr.ok(U32.is_le(v, 2147483648), U32.sub(0, v))
    case False{}:
      kstr.ok(U32.is_le(v, 2147483647), v)

def kstr.s32.res(neg: Bool, r: Result<&2, &2, KStrError, U32>) -> Result<&2, &2, KStrError, U32>:
  match r:
    case Done{+v}:
      kstr.s32.fin(neg, v)
    case Fail{e}:
      Fail{e}

# 64-bit: the same steps on a W64 accumulator

def kstr.ok64(fits: Bool, +v: W.W64) -> Result<&2, &2, KStrError, W.W64>:
  match fits:
    case True{}:
      Done{v}
    case False{}:
      Fail{KStrRange{}}

# acc * base + d, refused past 2^64 - 1: with acc = h 2^32 + l, the product
# is (h base + the top half of l base) 2^32 + the bottom half of l base
def kstr.mul64.fin(+mid: W.W64, +plo: W.W64, +d: U32) -> Result<&2, &2, KStrError, W.W64>:
  +prod = W.W64.from_parts(W.W64.lo(mid), W.W64.lo(plo))
  +sum = W.W64.add(prod, W.W64.from_u32(d))
  kstr.ok64(Bool.and(U32.is_eq(W.W64.hi(mid), 0), W.W64.is_le(prod, sum)), sum)

def kstr.mul64(+acc: W.W64, +base: U32, +d: U32) -> Result<&2, &2, KStrError, W.W64>:
  +plo = W.W64.mul(W.W64.from_u32(W.W64.lo(acc)), W.W64.from_u32(base))
  kstr.mul64.fin(W.W64.add(W.W64.mul(W.W64.from_u32(W.W64.hi(acc)), W.W64.from_u32(base)), W.W64.from_u32(W.W64.hi(plo))), plo, d)

def kstr.step64.digit(ok: Bool, +base: U32, +acc: W.W64, +d: U32, +pos: Nat) -> Result<&2, &2, KStrError, W.W64>:
  match ok:
    case True{}:
      kstr.mul64(acc, base, d)
    case False{}:
      Fail{KStrBadChar{pos}}

def kstr.step64(+base: U32, t: KStrTok, +acc: W.W64, +pos: Nat) -> Result<&2, &2, KStrError, W.W64>:
  match t:
    case KTDigit{+d}:
      kstr.step64.digit(U32.is_lt(d, base), base, acc, d, pos)
    case o:
      Fail{KStrBadChar{pos}}

def kstr.digits64(ts: List<&2, KStrTok>, +base: U32, r: Result<&2, &2, KStrError, W.W64>, +pos: Nat) -> Result<&2, &2, KStrError, W.W64>:
  match ts:
    case Nil{}:
      r
    case Con{t, rest}:
      match r:
        case Done{+acc}:
          kstr.digits64(rest, base, kstr.step64(base, t, acc, pos), 1n+pos)
        case Fail{e}:
          Fail{e}

# The front end: the sign, then the prefix and the base, handing back the
# digits, their base and the position of the first. In base 16 a "0x" is
# skipped; base 0 is decided by the prefix. The second token is looked at
# first, so that an unknown first digit is never inspected when the second
# is not an x.

def kstr.zero(t: KStrTok) -> Bool:
  match t:
    case KTDigit{v}:
      U32.is_eq(v, 0)
    case o:
      False{}

def kstr.hexdigit(t: KStrTok) -> Bool:
  match t:
    case KTDigit{v}:
      True{}
    case o:
      False{}


type KStrDigits is Data:
  KStrDigits{neg: Bool, base: U32, ts: List<&2, KStrTok>, pos: Nat}

def kstr.front.num(+neg: Bool, ts: List<&2, KStrTok>, +base: U32, +pos: Nat) -> Result<&2, &2, KStrError, KStrDigits>:
  match ts:
    case Nil{}:
      Fail{KStrEmpty{}}
    case Con{t, rest}:
      Done{KStrDigits{neg, base, Con{t, rest}, pos}}

def kstr.front.x(z: Bool, +neg: Bool, rest: List<&2, KStrTok>, +pos: Nat) -> Result<&2, &2, KStrError, KStrDigits>:
  match z:
    case True{}:
      kstr.front.num(neg, rest, 16, 2n+pos)
    case False{}:
      Fail{KStrBadChar{1n+pos}}

def kstr.front.hex(+neg: Bool, ts: List<&2, KStrTok>, +pos: Nat) -> Result<&2, &2, KStrError, KStrDigits>:
  match ts:
    case Con{t0, Con{KTX{}, rest}}:
      kstr.front.x(kstr.zero(t0), neg, rest, pos)
    case o:
      kstr.front.num(neg, o, 16, pos)

def kstr.front.auto.pick(x: Bool, z: Bool, +neg: Bool, ts: List<&2, KStrTok>, +pos: Nat) -> Result<&2, &2, KStrError, KStrDigits>:
  match x z:
    case True{} _:
      kstr.front.hex(neg, ts, pos)
    case False{} True{}:
      kstr.front.num(neg, ts, 8, pos)
    case False{} False{}:
      kstr.front.num(neg, ts, 10, pos)

def kstr.front.auto(+neg: Bool, +ts: List<&2, KStrTok>, +pos: Nat) -> Result<&2, &2, KStrError, KStrDigits>:
  match ts:
    case Con{t0, Con{KTX{}, Con{t2, rest}}}:
      kstr.front.auto.pick(Bool.and(kstr.zero(t0), kstr.hexdigit(t2)), kstr.zero(t0), neg, ts, pos)
    case Con{t0, rest}:
      kstr.front.auto.pick(False{}, kstr.zero(t0), neg, ts, pos)
    case o:
      Fail{KStrEmpty{}}

def kstr.front.base(zero: Bool, sixteen: Bool, +neg: Bool, +base: U32, +ts: List<&2, KStrTok>, +pos: Nat) -> Result<&2, &2, KStrError, KStrDigits>:
  match zero sixteen:
    case True{} _:
      kstr.front.auto(neg, ts, pos)
    case False{} True{}:
      kstr.front.hex(neg, ts, pos)
    case False{} False{}:
      kstr.front.num(neg, ts, base, pos)

def kstr.front.sign.minus(minus: Bool, +base: U32, rest: List<&2, KStrTok>) -> Result<&2, &2, KStrError, KStrDigits>:
  match minus:
    case True{}:
      kstr.front.base(U32.is_eq(base, 0), U32.is_eq(base, 16), True{}, base, rest, 1n)
    case False{}:
      Fail{KStrBadChar{0n}}

def kstr.front(+base: U32, ts: List<&2, KStrTok>, minus: Bool) -> Result<&2, &2, KStrError, KStrDigits>:
  match ts:
    case Con{KTPlus{}, rest}:
      kstr.front.base(U32.is_eq(base, 0), U32.is_eq(base, 16), False{}, base, rest, 1n)
    case Con{KTMinus{}, rest}:
      kstr.front.sign.minus(minus, base, rest)
    case o:
      kstr.front.base(U32.is_eq(base, 0), U32.is_eq(base, 16), False{}, base, o, 0n)

def kstr.u32.fin(r: Result<&2, &2, KStrError, KStrDigits>) -> Result<&2, &2, KStrError, U32>:
  match r:
    case Done{d}:
      match d:
        case KStrDigits{neg, +base, ts, pos}:
          kstr.digits(ts, base, Done{0}, pos)
    case Fail{e}:
      Fail{e}

# the bytes o as an unsigned 32-bit number in base (0, 8, 10 or 16; other
# bases from 2 to 16 work too)
def KStr.to_u32(o: B.Octets, +base: U32) -> Result<&2, &2, KStrError, U32>:
  kstr.u32.fin(kstr.front(base, kstr.strip_nl(kstr.toks(B.Octets.to_list(o))), False{}))

def kstr.s32(r: Result<&2, &2, KStrError, KStrDigits>) -> Result<&2, &2, KStrError, U32>:
  match r:
    case Done{d}:
      match d:
        case KStrDigits{neg, +base, ts, pos}:
          kstr.s32.res(neg, kstr.digits(ts, base, Done{0}, pos))
    case Fail{e}:
      Fail{e}

# signed: -2^31 to 2^31 - 1, as two's complement in a U32
def KStr.to_s32(o: B.Octets, +base: U32) -> Result<&2, &2, KStrError, U32>:
  kstr.s32(kstr.front(base, kstr.strip_nl(kstr.toks(B.Octets.to_list(o))), True{}))

def kstr.u64.fin(r: Result<&2, &2, KStrError, KStrDigits>) -> Result<&2, &2, KStrError, W.W64>:
  match r:
    case Done{d}:
      match d:
        case KStrDigits{neg, +base, ts, pos}:
          kstr.digits64(ts, base, Done{W.W64.zero()}, pos)
    case Fail{e}:
      Fail{e}

def KStr.to_u64(o: B.Octets, +base: U32) -> Result<&2, &2, KStrError, W.W64>:
  kstr.u64.fin(kstr.front(base, kstr.strip_nl(kstr.toks(B.Octets.to_list(o))), False{}))

def kstr.s64.fin(neg: Bool, +v: W.W64) -> Result<&2, &2, KStrError, W.W64>:
  match neg:
    case True{}:
      kstr.ok64(W.W64.is_le(v, W.W64.from_parts(2147483648, 0)), W.W64.sub(W.W64.zero(), v))
    case False{}:
      kstr.ok64(W.W64.is_lt(v, W.W64.from_parts(2147483648, 0)), v)

def kstr.s64.res(neg: Bool, r: Result<&2, &2, KStrError, W.W64>) -> Result<&2, &2, KStrError, W.W64>:
  match r:
    case Done{+v}:
      kstr.s64.fin(neg, v)
    case Fail{e}:
      Fail{e}

def kstr.s64(r: Result<&2, &2, KStrError, KStrDigits>) -> Result<&2, &2, KStrError, W.W64>:
  match r:
    case Done{d}:
      match d:
        case KStrDigits{neg, +base, ts, pos}:
          kstr.s64.res(neg, kstr.digits64(ts, base, Done{W.W64.zero()}, pos))
    case Fail{e}:
      Fail{e}

# signed 64-bit, as two's complement in a W64
def KStr.to_s64(o: B.Octets, +base: U32) -> Result<&2, &2, KStrError, W.W64>:
  kstr.s64(kstr.front(base, kstr.strip_nl(kstr.toks(B.Octets.to_list(o))), True{}))

# kstrtobool: "y", "Y", "1", "on" are true; "n", "N", "0", "off" are false
# (only the first one or two bytes are read, as the kernel documents)
def kstr.bool.on2(n: Bool, f: Bool) -> Result<&2, &2, KStrError, Bool>:
  match n f:
    case True{} _:
      Done{True{}}
    case False{} True{}:
      Done{False{}}
    case False{} False{}:
      Fail{KStrBadChar{1n}}

def kstr.bool.on(xs: List<&2, U32>) -> Result<&2, &2, KStrError, Bool>:
  match xs:
    case Con{+c, t}:
      kstr.bool.on2(U32.is_eq(U32.or(c, 32), 110), U32.is_eq(U32.or(c, 32), 102))
    case Nil{}:
      Fail{KStrBadChar{1n}}

def kstr.bool.sel(yes: Bool, no: Bool, o: Bool, t: List<&2, U32>) -> Result<&2, &2, KStrError, Bool>:
  match yes no o:
    case True{} _ _:
      Done{True{}}
    case False{} True{} _:
      Done{False{}}
    case False{} False{} True{}:
      kstr.bool.on(t)
    case False{} False{} False{}:
      Fail{KStrBadChar{0n}}

def kstr.bool.first(+l: U32, t: List<&2, U32>) -> Result<&2, &2, KStrError, Bool>:
  kstr.bool.sel(Bool.or(U32.is_eq(l, 121), U32.is_eq(l, 49)), Bool.or(U32.is_eq(l, 110), U32.is_eq(l, 48)), U32.is_eq(l, 111), t)

def kstr.bool.pick(c: U32, t: List<&2, U32>) -> Result<&2, &2, KStrError, Bool>:
  kstr.bool.first(U32.or(c, 32), t)

def kstr.bool.start(xs: List<&2, U32>) -> Result<&2, &2, KStrError, Bool>:
  match xs:
    case Nil{}:
      Fail{KStrEmpty{}}
    case Con{c, t}:
      kstr.bool.pick(c, t)

def KStr.to_bool(o: B.Octets) -> Result<&2, &2, KStrError, Bool>:
  kstr.bool.start(B.Octets.to_list(o))
