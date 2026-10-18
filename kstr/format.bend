# bend-osdev-kstr, number formatting: the vsprintf conversions %d, %i, %u,
# %x, %X and %o with the flags '-' (left-justify), '0' (pad with zeros), '+'
# and ' ' (the sign of a nonnegative %d), and a field width, as C (ISO C99,
# 7.19.6.1) and the kernel's printf documentation define them; values are
# 64 bits, %d and %i reading them as two's complement. KStr.sprintf reads a
# format string with these conversions and %%; KStr.format formats one value
# by a KFmt record; KStr.hex32 is the fixed form %08x of a U32.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./kstr.bend as K

type KConv is Data:
  KConvD{}
  KConvU{}
  KConvX{}
  KConvXUpper{}
  KConvO{}

type KFmt is Data:
  KFmt{conv: KConv, width: Nat, zero: Bool, left: Bool, plus: Bool, space: Bool}

# a plain conversion: no flags, no width
def KFmt.plain(c: KConv) -> KFmt:
  KFmt{c, 0n, False{}, False{}, False{}, False{}}

# the digit d (below 16) as a byte; upper selects A-F
def kfmt.digit.pick(lt: Bool, upper: Bool, +d: U32) -> U32:
  match lt upper:
    case True{} _:
      U32.add(d, 48)
    case False{} True{}:
      U32.add(d, 55)
    case False{} False{}:
      U32.add(d, 87)

def KStr.hex_digit(+d: U32) -> U32:
  kfmt.digit.pick(U32.is_lt(d, 10), False{}, d)

# a quotient and a remainder
type KFQr is Data:
  KFQr{q: W.W64, r: U32}

def kfmt.qr64(p: W.W64 & W.W64) -> KFQr:
  (q, r) = p
  KFQr{q, W.W64.lo(r)}

# v divided by b, in 32 bits when v fits (the common case, and cheaper)
def kfmt.divmod(small: Bool, +v: W.W64, +b: U32) -> KFQr:
  match small:
    case True{}:
      KFQr{W.W64.from_u32(U32.div(W.W64.lo(v), b)), U32.mod(W.W64.lo(v), b)}
    case False{}:
      kfmt.qr64(W.W64.divmod(v, W.W64.from_u32(b)))

def kfmt.q(p: KFQr) -> W.W64:
  match p:
    case KFQr{q, r}:
      q

def kfmt.r(p: KFQr) -> U32:
  match p:
    case KFQr{q, r}:
      r

# the digits of v in base b (2 to 16), most significant first, onto acc (at
# most 64; stop is "nothing left")
def kfmt.digits(n: Nat, stop: Bool, +v: W.W64, +b: U32, +upper: Bool, acc: List<&2, U32>) -> List<&2, U32>:
  match n stop:
    case _ True{}:
      acc
    case 0n False{}:
      acc
    case 1n+k False{}:
      +qr = kfmt.divmod(U32.is_eq(W.W64.hi(v), 0), v, b)
      +q = kfmt.q(qr)
      +r = kfmt.r(qr)
      kfmt.digits(k, W.W64.is_zero(q), q, b, upper, Con{kfmt.digit.pick(U32.is_lt(r, 10), upper, r), acc})

def kfmt.base(c: KConv) -> U32:
  match c:
    case KConvD{}:
      10
    case KConvU{}:
      10
    case KConvX{}:
      16
    case KConvXUpper{}:
      16
    case KConvO{}:
      8

def kfmt.upper(c: KConv) -> Bool:
  match c:
    case KConvXUpper{}:
      True{}
    case o:
      False{}

def kfmt.signed(c: KConv) -> Bool:
  match c:
    case KConvD{}:
      True{}
    case o:
      False{}

def kfmt.neg(a: W.W64) -> Bool:
  U32.is_eq(U32.shrn(W.W64.hi(a), 31n), 1)

# the sign's bytes, and the magnitude
def kfmt.sign.pick(neg: Bool, +plus: Bool, +space: Bool) -> List<&2, U32>:
  match neg plus space:
    case True{} _ _:
      [45]
    case False{} True{} _:
      [43]
    case False{} False{} True{}:
      [32]
    case False{} False{} False{}:
      Nil{}

def kfmt.mag.pick(neg: Bool, +v: W.W64) -> W.W64:
  match neg:
    case True{}:
      W.W64.sub(W.W64.zero(), v)
    case False{}:
      v

def kfmt.repeat(n: Nat, +c: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+k:
      kfmt.repeat(k, c, Con{c, acc})

def kfmt.pad.pick(left: Bool, zero: Bool, +fill: Nat, +sign: List<&2, U32>, +ds: List<&2, U32>) -> List<&2, U32>:
  match left zero:
    case True{} _:
      B.append(B.append(sign, ds), kfmt.repeat(fill, 32, Nil{}))
    case False{} True{}:
      B.append(sign, kfmt.repeat(fill, 48, ds))
    case False{} False{}:
      kfmt.repeat(fill, 32, B.append(sign, ds))

# pad sign ++ digits to width: spaces after (left), zeros between (zero) or
# spaces before
def kfmt.pad(+width: Nat, zero: Bool, left: Bool, +sign: List<&2, U32>, +ds: List<&2, U32>) -> List<&2, U32>:
  +fill = Nat.sub(width, Nat.add(B.len(sign), B.len(ds)))
  kfmt.pad.pick(left, zero, fill, sign, ds)

def kfmt.list(f: KFmt, +v: W.W64) -> List<&2, U32>:
  match f:
    case KFmt{+conv, width, zero, left, +plus, +space}:
      +neg = Bool.and(kfmt.signed(conv), kfmt.neg(v))
      kfmt.pad(width, zero, left, kfmt.sign.pick(neg, Bool.and(kfmt.signed(conv), plus), Bool.and(kfmt.signed(conv), space)), kfmt.digits(64n, False{}, kfmt.mag.pick(neg, v), kfmt.base(conv), kfmt.upper(conv), Nil{}))

# one 64-bit value by f
def KStr.format(f: KFmt, +v: W.W64) -> B.Octets:
  B.Octets.of_list(kfmt.list(f, v))

# one 32-bit value by f (%d reads it as a signed 32-bit value)
def KStr.format32(f: KFmt, +v: U32) -> B.Octets:
  KStr.format(f, W.W64.from_parts(U32.sub(0, U32.shrn(v, 31n)), v))

# the hex digit of the nibble b3 b2 b1 b0
def KStr.nib(b0: Bool, b1: Bool, b2: Bool, b3: Bool) -> U32:
  KStr.hex_digit(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, Word.zero(28n)}}}}})

# the 8 lower-case hex digits of v (%08x), most significant first
def KStr.hex32(v: U32) -> B.Octets:
  match v:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      B.Octets.of_list([KStr.nib(b28, b29, b30, b31), KStr.nib(b24, b25, b26, b27), KStr.nib(b20, b21, b22, b23), KStr.nib(b16, b17, b18, b19), KStr.nib(b12, b13, b14, b15), KStr.nib(b8, b9, b10, b11), KStr.nib(b4, b5, b6, b7), KStr.nib(b0, b1, b2, b3)])

# sprintf: the format string's bytes, classified once (the meaning of '0'
# and of the digits depends on where they are, so they keep their value)

type KFTok is Data:
  KFPct{}
  KFDash{}
  KFPlus{}
  KFSpace{}
  KFZero{}
  KFDig{d: U32}
  KFConvT{k: KConv}
  KFLit{c: U32}

def kfmt.tok.conv(d: Bool, i: Bool, u: Bool, x: Bool, xx: Bool, o: Bool, +c: U32) -> KFTok:
  match d i u x xx o:
    case True{} _ _ _ _ _:
      KFConvT{KConvD{}}
    case False{} True{} _ _ _ _:
      KFConvT{KConvD{}}
    case False{} False{} True{} _ _ _:
      KFConvT{KConvU{}}
    case False{} False{} False{} True{} _ _:
      KFConvT{KConvX{}}
    case False{} False{} False{} False{} True{} _:
      KFConvT{KConvXUpper{}}
    case False{} False{} False{} False{} False{} True{}:
      KFConvT{KConvO{}}
    case False{} False{} False{} False{} False{} False{}:
      KFLit{c}

def kfmt.tok.pick(pct: Bool, dash: Bool, plus: Bool, space: Bool, zero: Bool, dig: Bool, +c: U32) -> KFTok:
  match pct dash plus space zero dig:
    case True{} _ _ _ _ _:
      KFPct{}
    case False{} True{} _ _ _ _:
      KFDash{}
    case False{} False{} True{} _ _ _:
      KFPlus{}
    case False{} False{} False{} True{} _ _:
      KFSpace{}
    case False{} False{} False{} False{} True{} _:
      KFZero{}
    case False{} False{} False{} False{} False{} True{}:
      KFDig{U32.sub(c, 48)}
    case False{} False{} False{} False{} False{} False{}:
      kfmt.tok.conv(U32.is_eq(c, 100), U32.is_eq(c, 105), U32.is_eq(c, 117), U32.is_eq(c, 120), U32.is_eq(c, 88), U32.is_eq(c, 111), c)

def kfmt.tok(+c: U32) -> KFTok:
  kfmt.tok.pick(U32.is_eq(c, 37), U32.is_eq(c, 45), U32.is_eq(c, 43), U32.is_eq(c, 32), U32.is_eq(c, 48), Bool.and(U32.is_le(49, c), U32.is_le(c, 57)), c)

def kfmt.toks(xs: List<&2, U32>) -> List<&2, KFTok>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{kfmt.tok(h), kfmt.toks(t)}

def kfmt.lit.conv(k: KConv) -> U32:
  match k:
    case KConvD{}:
      100
    case KConvU{}:
      117
    case KConvX{}:
      120
    case KConvXUpper{}:
      88
    case KConvO{}:
      111

# the byte a token came from, when it is text
def kfmt.lit(t: KFTok) -> U32:
  match t:
    case KFPct{}:
      37
    case KFDash{}:
      45
    case KFPlus{}:
      43
    case KFSpace{}:
      32
    case KFZero{}:
      48
    case KFDig{d}:
      U32.add(d, 48)
    case KFConvT{k}:
      kfmt.lit.conv(k)
    case KFLit{c}:
      c

# the arguments left and the output so far (reversed)
type KFSt is Data:
  KFSt{args: List<&2, W.W64>, out: List<&2, U32>}

# where the reader is: in text, or in a conversion with its flags and width
# so far (wd: a digit of the width has been read)
type KFMode is Data:
  KFText{}
  KFSpec{zero: Bool, left: Bool, plus: Bool, space: Bool, width: Nat, wd: Bool, start: Nat}

def kfmt.mode.text(t: KFTok, +pos: Nat) -> KFMode:
  match t:
    case KFPct{}:
      KFSpec{False{}, False{}, False{}, False{}, 0n, False{}, pos}
    case o:
      KFText{}

def kfmt.width(+w: Nat, +d: U32) -> Nat:
  Nat.add(Nat.mul(w, 10n), U32.to_nat(d))

def kfmt.mode.spec(t: KFTok, wd: Bool, z: Bool, l: Bool, p: Bool, s: Bool, +w: Nat, +start: Nat) -> KFMode:
  match t wd:
    case KFDash{} False{}:
      KFSpec{z, True{}, p, s, w, False{}, start}
    case KFPlus{} False{}:
      KFSpec{z, l, True{}, s, w, False{}, start}
    case KFSpace{} False{}:
      KFSpec{z, l, p, True{}, w, False{}, start}
    case KFZero{} False{}:
      KFSpec{True{}, l, p, s, w, False{}, start}
    case KFZero{} True{}:
      KFSpec{z, l, p, s, kfmt.width(w, 0), True{}, start}
    case KFDig{d} _:
      KFSpec{z, l, p, s, kfmt.width(w, d), True{}, start}
    case o _:
      KFText{}

# the next mode after token t
def kfmt.mode(m: KFMode, t: KFTok, +pos: Nat) -> KFMode:
  match m:
    case KFText{}:
      kfmt.mode.text(t, pos)
    case KFSpec{z, l, p, s, +w, wd, start}:
      kfmt.mode.spec(t, wd, z, l, p, s, w, start)

def kfmt.emit(f: KFmt, args: List<&2, W.W64>, acc: List<&2, U32>) -> Result<&2, &2, K.KStrError, KFSt>:
  match args:
    case Nil{}:
      Fail{K.KStrMissingArg{}}
    case Con{+v, rest}:
      Done{KFSt{rest, B.rev_onto(kfmt.list(f, v), acc)}}

def kfmt.out.lit(c: U32, st: KFSt) -> Result<&2, &2, K.KStrError, KFSt>:
  match st:
    case KFSt{args, acc}:
      Done{KFSt{args, Con{c, acc}}}

def kfmt.out.text(t: KFTok, st: KFSt) -> Result<&2, &2, K.KStrError, KFSt>:
  match t:
    case KFPct{}:
      Done{st}
    case o:
      kfmt.out.lit(kfmt.lit(o), st)

def kfmt.out.conv(f: KFmt, st: KFSt) -> Result<&2, &2, K.KStrError, KFSt>:
  match st:
    case KFSt{args, acc}:
      kfmt.emit(f, args, acc)

# a flag after the width, or a byte that is not a conversion, is malformed
def kfmt.out.spec(t: KFTok, wd: Bool, z: Bool, l: Bool, p: Bool, s: Bool, w: Nat, st: KFSt, +pos: Nat) -> Result<&2, &2, K.KStrError, KFSt>:
  match t wd:
    case KFConvT{k} _:
      kfmt.out.conv(KFmt{k, w, z, l, p, s}, st)
    case KFPct{} _:
      kfmt.out.lit(37, st)
    case KFZero{} _:
      Done{st}
    case KFDig{d} _:
      Done{st}
    case KFDash{} False{}:
      Done{st}
    case KFPlus{} False{}:
      Done{st}
    case KFSpace{} False{}:
      Done{st}
    case o _:
      Fail{K.KStrBadFormat{pos}}

# the output and the arguments after token t
def kfmt.out(m: KFMode, t: KFTok, st: KFSt, +pos: Nat) -> Result<&2, &2, K.KStrError, KFSt>:
  match m:
    case KFText{}:
      kfmt.out.text(t, st)
    case KFSpec{z, l, p, s, w, wd, start}:
      kfmt.out.spec(t, wd, z, l, p, s, w, st, pos)

def kfmt.go.fin(st: KFSt) -> Result<&2, &2, K.KStrError, List<&2, U32>>:
  match st:
    case KFSt{args, acc}:
      Done{B.rev(acc)}

def kfmt.go.end(m: KFMode, r: Result<&2, &2, K.KStrError, KFSt>) -> Result<&2, &2, K.KStrError, List<&2, U32>>:
  match m r:
    case KFText{} Done{st}:
      kfmt.go.fin(st)
    case KFSpec{z, l, p, s, w, wd, start} Done{st}:
      Fail{K.KStrBadFormat{start}}
    case _ Fail{e}:
      Fail{e}

def kfmt.go(ts: List<&2, KFTok>, +m: KFMode, r: Result<&2, &2, K.KStrError, KFSt>, +pos: Nat) -> Result<&2, &2, K.KStrError, List<&2, U32>>:
  match ts:
    case Nil{}:
      kfmt.go.end(m, r)
    case Con{+t, rest}:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{st}:
          kfmt.go(rest, kfmt.mode(m, t, pos), kfmt.out(m, t, st, pos), 1n+pos)

def kfmt.sprintf.fin(r: Result<&2, &2, K.KStrError, List<&2, U32>>) -> Result<&2, &2, K.KStrError, B.Octets>:
  match r:
    case Done{xs}:
      Done{B.Octets.of_list(xs)}
    case Fail{e}:
      Fail{e}

# the format string fmt with each conversion replaced by the next argument
# (64-bit values); %% is a percent sign
def KStr.sprintf(fmt: B.Octets, args: List<&2, W.W64>) -> Result<&2, &2, K.KStrError, B.Octets>:
  kfmt.sprintf.fin(kfmt.go(kfmt.toks(B.Octets.to_list(fmt)), KFText{}, Done{KFSt{args, Nil{}}}, 0n))
