# Proof helpers for bend-osdev-crc: the 64-bit engines' steps, for every
# register and polynomial. A W64 is used only through bend-osdev-word64's
# public defs and its parts_of law (a word is its two halves joined): each
# lemma here takes its words apart that way, and word64's defs then work on
# the halves.
#
# word64's one-place shifts join the halves with an OR; the engines are
# restated with clean shifts (c6.shr1, c6.shl1: a U32 shifted with a bit
# entering, built from the bits themselves), which proof_cases64.bend ties to
# word64's. A step of either engine commutes with XOR, so eight steps do
# (c6.r_lin, c6.n_lin). Lemmas are prefixed c6.
import Base
import ../word64/word64.bend as W
import ../word64/LAWS.bend as WL
import ../word64/PROOF.bend as WP
import ./crc.bend as C
import ../array/array.bend as A
import ./proof_word.bend as PW

# A U32 shifted one place with the bit b entering: right (at bit 31) and
# left (at bit 0)

def c6.padb(p: Nat, w: Word(p), b: Bool) -> Word(1n+p):
  match p:
    case 0n:
      WCon{b, WNil{}}
    case 1n+q:
      match w:
        case WCon{h, t}:
          WCon{h, c6.padb(q, t, b)}

def c6.shrc(l: U32, b: Bool) -> U32:
  match l:
    case U32{WCon{l0, lt}}:
      U32{c6.padb(31n, lt, b)}

def c6.shlc(h: U32, b: Bool) -> U32:
  match h:
    case U32{WCon{h0, ht}}:
      U32{WCon{b, Word.shl.put(31n, h0, ht)}}

# OR, reading its second operand first (so that a known second operand
# decides each bit)

def c6.bor(a: Bool, b: Bool) -> Bool:
  match b:
    case False{}:
      a
    case True{}:
      True{}

def c6.wor(n: Nat, a: Word(n), b: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          WCon{c6.bor(ah, bh), c6.wor(p, at, bt)}

def c6.uor(a: U32, b: U32) -> U32:
  match a b:
    case U32{x} U32{y}:
      U32{c6.wor(32n, x, y)}

def c6.bor_eq(+a: Bool, +b: Bool) -> {Bool.or(a, b) == c6.bor(a, b) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def c6.wor_eq(n: Nat, a: Word(n), b: Word(n)) -> {Word.or(n, a, b) == c6.wor(n, a, b) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+ah, at} WCon{+bh, bt}:
          PW.cw.wcon2(p, Bool.or(ah, bh), c6.bor(ah, bh), Word.or(p, at, bt), c6.wor(p, at, bt), c6.bor_eq(ah, bh), c6.wor_eq(p, at, bt))

def c6.or_uor(a: U32, b: U32) -> {U32.or(a, b) == c6.uor(a, b) : U32}:
  match a b:
    case U32{x} U32{y}:
      PW.cw.u32_cong(Word.or(32n, x, y), c6.wor(32n, x, y), c6.wor_eq(32n, x, y))

# The clean shifts move XOR bit for bit

def c6.padb_xor(p: Nat, a: Word(p), b: Word(p), +c: Bool, +d: Bool) -> {c6.padb(p, Word.xor(p, a, b), Bool.xor(c, d)) == Word.xor(1n+p, c6.padb(p, a, c), c6.padb(p, b, d)) : Word(1n+p)}:
  match p:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+q:
      match a b:
        case WCon{+ah, at} WCon{+bh, bt}:
          PW.cw.wcon2(1n+q, Bool.xor(ah, bh), Bool.xor(ah, bh), c6.padb(q, Word.xor(q, at, bt), Bool.xor(c, d)), Word.xor(1n+q, c6.padb(q, at, c), c6.padb(q, bt, d)), {==}, c6.padb_xor(q, at, bt, c, d))

def c6.shrc_xor(x: U32, y: U32, +c: Bool, +d: Bool) -> {c6.shrc(U32.xor(x, y), Bool.xor(c, d)) == U32.xor(c6.shrc(x, c), c6.shrc(y, d)) : U32}:
  match x y:
    case U32{WCon{x0, xt}} U32{WCon{y0, yt}}:
      PW.cw.u32_cong(c6.padb(31n, Word.xor(31n, xt, yt), Bool.xor(c, d)), Word.xor(32n, c6.padb(31n, xt, c), c6.padb(31n, yt, d)), c6.padb_xor(31n, xt, yt, c, d))

def c6.shlc_xor(x: U32, y: U32, +c: Bool, +d: Bool) -> {c6.shlc(U32.xor(x, y), Bool.xor(c, d)) == U32.xor(c6.shlc(x, c), c6.shlc(y, d)) : U32}:
  match x y:
    case U32{WCon{+x0, xt}} U32{WCon{+y0, yt}}:
      PW.cw.u32_cong(WCon{Bool.xor(c, d), Word.shl.put(31n, Bool.xor(x0, y0), Word.xor(31n, xt, yt))}, WCon{Bool.xor(c, d), Word.xor(31n, Word.shl.put(31n, x0, xt), Word.shl.put(31n, y0, yt))}, PW.cw.wcon2(31n, Bool.xor(c, d), Bool.xor(c, d), Word.shl.put(31n, Bool.xor(x0, y0), Word.xor(31n, xt, yt)), Word.xor(31n, Word.shl.put(31n, x0, xt), Word.shl.put(31n, y0, yt)), {==}, PW.cw.put_xor(31n, x0, y0, xt, yt)))

# W64 words through their halves

def c6.fp_cong(-a1: U32, -a2: U32, -b1: U32, -b2: U32, ea: {a1 == a2 : U32}, eb: {b1 == b2 : U32}) -> {W.W64.from_parts(a1, b1) == W.W64.from_parts(a2, b2) : W.W64}:
  %ea : {W.W64.from_parts(a1, b1) == W.W64.from_parts(_, b2) : W.W64}
  %eb : {W.W64.from_parts(a1, b1) == W.W64.from_parts(a1, _) : W.W64}
  {==}

def c6.hi_xor(+x: W.W64, +y: W.W64) -> {W.W64.hi(W.W64.xor(x, y)) == U32.xor(W.W64.hi(x), W.W64.hi(y)) : U32}:
  %WL.parts_of(x) : {W.W64.hi(W.W64.xor(_, y)) == U32.xor(W.W64.hi(_), W.W64.hi(y)) : U32}
  %WL.parts_of(y) : {W.W64.hi(W.W64.xor(W.W64.from_parts(W.W64.hi(x), W.W64.lo(x)), _)) == U32.xor(W.W64.hi(W.W64.from_parts(W.W64.hi(x), W.W64.lo(x))), W.W64.hi(_)) : U32}
  {==}

def c6.lo_xor(+x: W.W64, +y: W.W64) -> {W.W64.lo(W.W64.xor(x, y)) == U32.xor(W.W64.lo(x), W.W64.lo(y)) : U32}:
  %WL.parts_of(x) : {W.W64.lo(W.W64.xor(_, y)) == U32.xor(W.W64.lo(_), W.W64.lo(y)) : U32}
  %WL.parts_of(y) : {W.W64.lo(W.W64.xor(W.W64.from_parts(W.W64.hi(x), W.W64.lo(x)), _)) == U32.xor(W.W64.lo(W.W64.from_parts(W.W64.hi(x), W.W64.lo(x))), W.W64.lo(_)) : U32}
  {==}

def c6.x_assoc(+a: W.W64, +b: W.W64, +c: W.W64) -> {W.W64.xor(W.W64.xor(a, b), c) == W.W64.xor(a, W.W64.xor(b, c)) : W.W64}:
  %WL.parts_of(a) : {W.W64.xor(W.W64.xor(_, b), c) == W.W64.xor(_, W.W64.xor(b, c)) : W.W64}
  %WL.parts_of(b) : {W.W64.xor(W.W64.xor(W.W64.from_parts(W.W64.hi(a), W.W64.lo(a)), _), c) == W.W64.xor(W.W64.from_parts(W.W64.hi(a), W.W64.lo(a)), W.W64.xor(_, c)) : W.W64}
  %WL.parts_of(c) : {W.W64.xor(W.W64.xor(W.W64.from_parts(W.W64.hi(a), W.W64.lo(a)), W.W64.from_parts(W.W64.hi(b), W.W64.lo(b))), _) == W.W64.xor(W.W64.from_parts(W.W64.hi(a), W.W64.lo(a)), W.W64.xor(W.W64.from_parts(W.W64.hi(b), W.W64.lo(b)), _)) : W.W64}
  c6.fp_cong(U32.xor(U32.xor(W.W64.hi(a), W.W64.hi(b)), W.W64.hi(c)), U32.xor(W.W64.hi(a), U32.xor(W.W64.hi(b), W.W64.hi(c))), U32.xor(U32.xor(W.W64.lo(a), W.W64.lo(b)), W.W64.lo(c)), U32.xor(W.W64.lo(a), U32.xor(W.W64.lo(b), W.W64.lo(c))), PW.cw.ux_assoc(W.W64.hi(a), W.W64.hi(b), W.W64.hi(c)), PW.cw.ux_assoc(W.W64.lo(a), W.W64.lo(b), W.W64.lo(c)))

def c6.x_swap(+a: W.W64, +b: W.W64, +c: W.W64) -> {W.W64.xor(W.W64.xor(a, b), c) == W.W64.xor(W.W64.xor(a, c), b) : W.W64}:
  %WL.parts_of(a) : {W.W64.xor(W.W64.xor(_, b), c) == W.W64.xor(W.W64.xor(_, c), b) : W.W64}
  %WL.parts_of(b) : {W.W64.xor(W.W64.xor(W.W64.from_parts(W.W64.hi(a), W.W64.lo(a)), _), c) == W.W64.xor(W.W64.xor(W.W64.from_parts(W.W64.hi(a), W.W64.lo(a)), c), _) : W.W64}
  %WL.parts_of(c) : {W.W64.xor(W.W64.xor(W.W64.from_parts(W.W64.hi(a), W.W64.lo(a)), W.W64.from_parts(W.W64.hi(b), W.W64.lo(b))), _) == W.W64.xor(W.W64.xor(W.W64.from_parts(W.W64.hi(a), W.W64.lo(a)), _), W.W64.from_parts(W.W64.hi(b), W.W64.lo(b))) : W.W64}
  c6.fp_cong(U32.xor(U32.xor(W.W64.hi(a), W.W64.hi(b)), W.W64.hi(c)), U32.xor(U32.xor(W.W64.hi(a), W.W64.hi(c)), W.W64.hi(b)), U32.xor(U32.xor(W.W64.lo(a), W.W64.lo(b)), W.W64.lo(c)), U32.xor(U32.xor(W.W64.lo(a), W.W64.lo(c)), W.W64.lo(b)), PW.cw.x_swap(W.W64.hi(a), W.W64.hi(b), W.W64.hi(c)), PW.cw.x_swap(W.W64.lo(a), W.W64.lo(b), W.W64.lo(c)))

def c6.x_cancel(+a: W.W64, +b: W.W64, +c: W.W64) -> {W.W64.xor(W.W64.xor(a, c), W.W64.xor(b, c)) == W.W64.xor(a, b) : W.W64}:
  %WL.parts_of(a) : {W.W64.xor(W.W64.xor(_, c), W.W64.xor(b, c)) == W.W64.xor(_, b) : W.W64}
  %WL.parts_of(b) : {W.W64.xor(W.W64.xor(W.W64.from_parts(W.W64.hi(a), W.W64.lo(a)), c), W.W64.xor(_, c)) == W.W64.xor(W.W64.from_parts(W.W64.hi(a), W.W64.lo(a)), _) : W.W64}
  %WL.parts_of(c) : {W.W64.xor(W.W64.xor(W.W64.from_parts(W.W64.hi(a), W.W64.lo(a)), _), W.W64.xor(W.W64.from_parts(W.W64.hi(b), W.W64.lo(b)), _)) == W.W64.xor(W.W64.from_parts(W.W64.hi(a), W.W64.lo(a)), W.W64.from_parts(W.W64.hi(b), W.W64.lo(b))) : W.W64}
  c6.fp_cong(U32.xor(U32.xor(W.W64.hi(a), W.W64.hi(c)), U32.xor(W.W64.hi(b), W.W64.hi(c))), U32.xor(W.W64.hi(a), W.W64.hi(b)), U32.xor(U32.xor(W.W64.lo(a), W.W64.lo(c)), U32.xor(W.W64.lo(b), W.W64.lo(c))), U32.xor(W.W64.lo(a), W.W64.lo(b)), PW.cw.x_cancel(W.W64.hi(a), W.W64.hi(b), W.W64.hi(c)), PW.cw.x_cancel(W.W64.lo(a), W.W64.lo(b), W.W64.lo(c)))

# The clean one-place shifts of a W64

def c6.shr1(+c: W.W64) -> W.W64:
  W.W64.from_parts(U32.shr(W.W64.hi(c)), c6.shrc(W.W64.lo(c), PW.cw.odd(W.W64.hi(c))))

def c6.shl1(+c: W.W64) -> W.W64:
  W.W64.from_parts(c6.shlc(W.W64.hi(c), PW.cw.bitk(31n, W.W64.lo(c))), U32.shl(W.W64.lo(c)))

def c6.shr1_xor(+x: W.W64, +y: W.W64) -> {c6.shr1(W.W64.xor(x, y)) == W.W64.xor(c6.shr1(x), c6.shr1(y)) : W.W64}:
  %WL.parts_of(x) : {c6.shr1(W.W64.xor(_, y)) == W.W64.xor(c6.shr1(_), c6.shr1(y)) : W.W64}
  %WL.parts_of(y) : {c6.shr1(W.W64.xor(W.W64.from_parts(W.W64.hi(x), W.W64.lo(x)), _)) == W.W64.xor(c6.shr1(W.W64.from_parts(W.W64.hi(x), W.W64.lo(x))), c6.shr1(_)) : W.W64}
  c6.fp_cong(U32.shr(U32.xor(W.W64.hi(x), W.W64.hi(y))), U32.xor(U32.shr(W.W64.hi(x)), U32.shr(W.W64.hi(y))), c6.shrc(U32.xor(W.W64.lo(x), W.W64.lo(y)), PW.cw.odd(U32.xor(W.W64.hi(x), W.W64.hi(y)))), U32.xor(c6.shrc(W.W64.lo(x), PW.cw.odd(W.W64.hi(x))), c6.shrc(W.W64.lo(y), PW.cw.odd(W.W64.hi(y)))), PW.cw.shr_xor(W.W64.hi(x), W.W64.hi(y)), Equal.trans(U32, c6.shrc(U32.xor(W.W64.lo(x), W.W64.lo(y)), PW.cw.odd(U32.xor(W.W64.hi(x), W.W64.hi(y)))), c6.shrc(U32.xor(W.W64.lo(x), W.W64.lo(y)), Bool.xor(PW.cw.odd(W.W64.hi(x)), PW.cw.odd(W.W64.hi(y)))), U32.xor(c6.shrc(W.W64.lo(x), PW.cw.odd(W.W64.hi(x))), c6.shrc(W.W64.lo(y), PW.cw.odd(W.W64.hi(y)))), Equal.cong(Bool, U32, z => c6.shrc(U32.xor(W.W64.lo(x), W.W64.lo(y)), z), PW.cw.odd(U32.xor(W.W64.hi(x), W.W64.hi(y))), Bool.xor(PW.cw.odd(W.W64.hi(x)), PW.cw.odd(W.W64.hi(y))), PW.cw.odd_xor(W.W64.hi(x), W.W64.hi(y))), c6.shrc_xor(W.W64.lo(x), W.W64.lo(y), PW.cw.odd(W.W64.hi(x)), PW.cw.odd(W.W64.hi(y)))))

def c6.shl1_xor(+x: W.W64, +y: W.W64) -> {c6.shl1(W.W64.xor(x, y)) == W.W64.xor(c6.shl1(x), c6.shl1(y)) : W.W64}:
  %WL.parts_of(x) : {c6.shl1(W.W64.xor(_, y)) == W.W64.xor(c6.shl1(_), c6.shl1(y)) : W.W64}
  %WL.parts_of(y) : {c6.shl1(W.W64.xor(W.W64.from_parts(W.W64.hi(x), W.W64.lo(x)), _)) == W.W64.xor(c6.shl1(W.W64.from_parts(W.W64.hi(x), W.W64.lo(x))), c6.shl1(_)) : W.W64}
  c6.fp_cong(c6.shlc(U32.xor(W.W64.hi(x), W.W64.hi(y)), PW.cw.bitk(31n, U32.xor(W.W64.lo(x), W.W64.lo(y)))), U32.xor(c6.shlc(W.W64.hi(x), PW.cw.bitk(31n, W.W64.lo(x))), c6.shlc(W.W64.hi(y), PW.cw.bitk(31n, W.W64.lo(y)))), U32.shl(U32.xor(W.W64.lo(x), W.W64.lo(y))), U32.xor(U32.shl(W.W64.lo(x)), U32.shl(W.W64.lo(y))), Equal.trans(U32, c6.shlc(U32.xor(W.W64.hi(x), W.W64.hi(y)), PW.cw.bitk(31n, U32.xor(W.W64.lo(x), W.W64.lo(y)))), c6.shlc(U32.xor(W.W64.hi(x), W.W64.hi(y)), Bool.xor(PW.cw.bitk(31n, W.W64.lo(x)), PW.cw.bitk(31n, W.W64.lo(y)))), U32.xor(c6.shlc(W.W64.hi(x), PW.cw.bitk(31n, W.W64.lo(x))), c6.shlc(W.W64.hi(y), PW.cw.bitk(31n, W.W64.lo(y)))), Equal.cong(Bool, U32, z => c6.shlc(U32.xor(W.W64.hi(x), W.W64.hi(y)), z), PW.cw.bitk(31n, U32.xor(W.W64.lo(x), W.W64.lo(y))), Bool.xor(PW.cw.bitk(31n, W.W64.lo(x)), PW.cw.bitk(31n, W.W64.lo(y))), PW.cw.bitk_xor(31n, W.W64.lo(x), W.W64.lo(y))), c6.shlc_xor(W.W64.hi(x), W.W64.hi(y), PW.cw.bitk(31n, W.W64.lo(x)), PW.cw.bitk(31n, W.W64.lo(y)))), PW.cw.shl_xor(W.W64.lo(x), W.W64.lo(y)))

# The engines with the clean shifts

def c6.rpick(b: Bool, +p: W.W64, +c: W.W64) -> W.W64:
  match b:
    case True{}:
      W.W64.xor(c6.shr1(c), p)
    case False{}:
      c6.shr1(c)

def c6.rb(n: Nat, +p: W.W64, +c: W.W64) -> W.W64:
  match n:
    case 0n:
      c
    case 1n+k:
      c6.rb(k, p, c6.rpick(PW.cw.odd(W.W64.lo(c)), p, c))

def c6.npick(b: Bool, +p: W.W64, +c: W.W64) -> W.W64:
  match b:
    case True{}:
      W.W64.xor(c6.shl1(c), p)
    case False{}:
      c6.shl1(c)

def c6.nb(n: Nat, +p: W.W64, +c: W.W64) -> W.W64:
  match n:
    case 0n:
      c
    case 1n+k:
      c6.nb(k, p, c6.npick(PW.cw.bitk(31n, W.W64.hi(c)), p, c))

# one step commutes with XOR, whatever the two choices are
def c6.rpick_lin(bx: Bool, by: Bool, +p: W.W64, +x: W.W64, +y: W.W64) -> {c6.rpick(Bool.xor(bx, by), p, W.W64.xor(x, y)) == W.W64.xor(c6.rpick(bx, p, x), c6.rpick(by, p, y)) : W.W64}:
  match bx by:
    case True{} True{}:
      Equal.trans(W.W64, c6.shr1(W.W64.xor(x, y)), W.W64.xor(c6.shr1(x), c6.shr1(y)), W.W64.xor(W.W64.xor(c6.shr1(x), p), W.W64.xor(c6.shr1(y), p)), c6.shr1_xor(x, y), Equal.sym(W.W64, W.W64.xor(W.W64.xor(c6.shr1(x), p), W.W64.xor(c6.shr1(y), p)), W.W64.xor(c6.shr1(x), c6.shr1(y)), c6.x_cancel(c6.shr1(x), c6.shr1(y), p)))
    case True{} False{}:
      %Equal.sym(W.W64, c6.shr1(W.W64.xor(x, y)), W.W64.xor(c6.shr1(x), c6.shr1(y)), c6.shr1_xor(x, y)) : {W.W64.xor(_, p) == W.W64.xor(W.W64.xor(c6.shr1(x), p), c6.shr1(y)) : W.W64}
      c6.x_swap(c6.shr1(x), c6.shr1(y), p)
    case False{} True{}:
      %Equal.sym(W.W64, c6.shr1(W.W64.xor(x, y)), W.W64.xor(c6.shr1(x), c6.shr1(y)), c6.shr1_xor(x, y)) : {W.W64.xor(_, p) == W.W64.xor(c6.shr1(x), W.W64.xor(c6.shr1(y), p)) : W.W64}
      c6.x_assoc(c6.shr1(x), c6.shr1(y), p)
    case False{} False{}:
      c6.shr1_xor(x, y)

def c6.npick_lin(bx: Bool, by: Bool, +p: W.W64, +x: W.W64, +y: W.W64) -> {c6.npick(Bool.xor(bx, by), p, W.W64.xor(x, y)) == W.W64.xor(c6.npick(bx, p, x), c6.npick(by, p, y)) : W.W64}:
  match bx by:
    case True{} True{}:
      Equal.trans(W.W64, c6.shl1(W.W64.xor(x, y)), W.W64.xor(c6.shl1(x), c6.shl1(y)), W.W64.xor(W.W64.xor(c6.shl1(x), p), W.W64.xor(c6.shl1(y), p)), c6.shl1_xor(x, y), Equal.sym(W.W64, W.W64.xor(W.W64.xor(c6.shl1(x), p), W.W64.xor(c6.shl1(y), p)), W.W64.xor(c6.shl1(x), c6.shl1(y)), c6.x_cancel(c6.shl1(x), c6.shl1(y), p)))
    case True{} False{}:
      %Equal.sym(W.W64, c6.shl1(W.W64.xor(x, y)), W.W64.xor(c6.shl1(x), c6.shl1(y)), c6.shl1_xor(x, y)) : {W.W64.xor(_, p) == W.W64.xor(W.W64.xor(c6.shl1(x), p), c6.shl1(y)) : W.W64}
      c6.x_swap(c6.shl1(x), c6.shl1(y), p)
    case False{} True{}:
      %Equal.sym(W.W64, c6.shl1(W.W64.xor(x, y)), W.W64.xor(c6.shl1(x), c6.shl1(y)), c6.shl1_xor(x, y)) : {W.W64.xor(_, p) == W.W64.xor(c6.shl1(x), W.W64.xor(c6.shl1(y), p)) : W.W64}
      c6.x_assoc(c6.shl1(x), c6.shl1(y), p)
    case False{} False{}:
      c6.shl1_xor(x, y)

# the tests commute with XOR

def c6.rtest_xor(+x: W.W64, +y: W.W64) -> {PW.cw.odd(W.W64.lo(W.W64.xor(x, y))) == Bool.xor(PW.cw.odd(W.W64.lo(x)), PW.cw.odd(W.W64.lo(y))) : Bool}:
  %Equal.sym(U32, W.W64.lo(W.W64.xor(x, y)), U32.xor(W.W64.lo(x), W.W64.lo(y)), c6.lo_xor(x, y)) : {PW.cw.odd(_) == Bool.xor(PW.cw.odd(W.W64.lo(x)), PW.cw.odd(W.W64.lo(y))) : Bool}
  PW.cw.odd_xor(W.W64.lo(x), W.W64.lo(y))

def c6.ntest_xor(+x: W.W64, +y: W.W64) -> {PW.cw.bitk(31n, W.W64.hi(W.W64.xor(x, y))) == Bool.xor(PW.cw.bitk(31n, W.W64.hi(x)), PW.cw.bitk(31n, W.W64.hi(y))) : Bool}:
  %Equal.sym(U32, W.W64.hi(W.W64.xor(x, y)), U32.xor(W.W64.hi(x), W.W64.hi(y)), c6.hi_xor(x, y)) : {PW.cw.bitk(31n, _) == Bool.xor(PW.cw.bitk(31n, W.W64.hi(x)), PW.cw.bitk(31n, W.W64.hi(y))) : Bool}
  PW.cw.bitk_xor(31n, W.W64.hi(x), W.W64.hi(y))

# eight (any number of) steps commute with XOR

def c6.r_lin(n: Nat, +p: W.W64, +x: W.W64, +y: W.W64) -> {c6.rb(n, p, W.W64.xor(x, y)) == W.W64.xor(c6.rb(n, p, x), c6.rb(n, p, y)) : W.W64}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(Bool, PW.cw.odd(W.W64.lo(W.W64.xor(x, y))), Bool.xor(PW.cw.odd(W.W64.lo(x)), PW.cw.odd(W.W64.lo(y))), c6.rtest_xor(x, y)) : {c6.rb(k, p, c6.rpick(_, p, W.W64.xor(x, y))) == W.W64.xor(c6.rb(k, p, c6.rpick(PW.cw.odd(W.W64.lo(x)), p, x)), c6.rb(k, p, c6.rpick(PW.cw.odd(W.W64.lo(y)), p, y))) : W.W64}
      %Equal.sym(W.W64, c6.rpick(Bool.xor(PW.cw.odd(W.W64.lo(x)), PW.cw.odd(W.W64.lo(y))), p, W.W64.xor(x, y)), W.W64.xor(c6.rpick(PW.cw.odd(W.W64.lo(x)), p, x), c6.rpick(PW.cw.odd(W.W64.lo(y)), p, y)), c6.rpick_lin(PW.cw.odd(W.W64.lo(x)), PW.cw.odd(W.W64.lo(y)), p, x, y)) : {c6.rb(k, p, _) == W.W64.xor(c6.rb(k, p, c6.rpick(PW.cw.odd(W.W64.lo(x)), p, x)), c6.rb(k, p, c6.rpick(PW.cw.odd(W.W64.lo(y)), p, y))) : W.W64}
      c6.r_lin(k, p, c6.rpick(PW.cw.odd(W.W64.lo(x)), p, x), c6.rpick(PW.cw.odd(W.W64.lo(y)), p, y))

def c6.n_lin(n: Nat, +p: W.W64, +x: W.W64, +y: W.W64) -> {c6.nb(n, p, W.W64.xor(x, y)) == W.W64.xor(c6.nb(n, p, x), c6.nb(n, p, y)) : W.W64}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(Bool, PW.cw.bitk(31n, W.W64.hi(W.W64.xor(x, y))), Bool.xor(PW.cw.bitk(31n, W.W64.hi(x)), PW.cw.bitk(31n, W.W64.hi(y))), c6.ntest_xor(x, y)) : {c6.nb(k, p, c6.npick(_, p, W.W64.xor(x, y))) == W.W64.xor(c6.nb(k, p, c6.npick(PW.cw.bitk(31n, W.W64.hi(x)), p, x)), c6.nb(k, p, c6.npick(PW.cw.bitk(31n, W.W64.hi(y)), p, y))) : W.W64}
      %Equal.sym(W.W64, c6.npick(Bool.xor(PW.cw.bitk(31n, W.W64.hi(x)), PW.cw.bitk(31n, W.W64.hi(y))), p, W.W64.xor(x, y)), W.W64.xor(c6.npick(PW.cw.bitk(31n, W.W64.hi(x)), p, x), c6.npick(PW.cw.bitk(31n, W.W64.hi(y)), p, y)), c6.npick_lin(PW.cw.bitk(31n, W.W64.hi(x)), PW.cw.bitk(31n, W.W64.hi(y)), p, x, y)) : {c6.nb(k, p, _) == W.W64.xor(c6.nb(k, p, c6.npick(PW.cw.bitk(31n, W.W64.hi(x)), p, x)), c6.nb(k, p, c6.npick(PW.cw.bitk(31n, W.W64.hi(y)), p, y))) : W.W64}
      c6.n_lin(k, p, c6.npick(PW.cw.bitk(31n, W.W64.hi(x)), p, x), c6.npick(PW.cw.bitk(31n, W.W64.hi(y)), p, y))

# The 64-bit tables' entries: entry i is eight steps on the byte i
# (reflected) or on i placed at the top byte (most significant bit first)

type CrcPfEng64 is Data:
  CrcPfR64{p: W.W64}
  CrcPfN64{p: W.W64}

def c6.ev(e: CrcPfEng64, x: U32) -> W.W64:
  match e:
    case CrcPfR64{p}:
      C.r64.bits(8n, p, W.W64.from_u32(x))
    case CrcPfN64{p}:
      C.n64.bits(8n, p, W.W64.from_parts(U32.shln(x, 24n), 0))

# the 64-bit fills' model: the list of slots after n writes from slot k
def c6.fill_model(n: Nat, xs: List<&2, W.W64>, +e: CrcPfEng64, +k: Nat) -> List<&2, W.W64>:
  match n:
    case 0n:
      xs
    case 1n+j:
      c6.fill_model(j, List.set(&2, W.W64, xs, A.Arrays.index(8n, U32.from_nat(k)), c6.ev(e, U32.from_nat(k))), e, 1n+k)

# eight clean shifts
def c6.shr8(+c: W.W64) -> W.W64:
  c6.shr1(c6.shr1(c6.shr1(c6.shr1(c6.shr1(c6.shr1(c6.shr1(c6.shr1(c))))))))

def c6.shl8(+c: W.W64) -> W.W64:
  c6.shl1(c6.shl1(c6.shl1(c6.shl1(c6.shl1(c6.shl1(c6.shl1(c6.shl1(c))))))))
