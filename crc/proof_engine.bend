# Proof helpers for bend-osdev-crc: the bitwise engines' steps, for every
# register and polynomial. A step of either engine is linear (GF(2)-linear:
# it commutes with XOR), so eight steps are; this is what lets a table of
# eight steps on the 256 bytes stand in for the steps themselves
# (proof_fast.bend). Lemmas are prefixed ce.
import Base
import ./crc.bend as C
import ../array/array.bend as A
import ./proof_word.bend as PW

# A word's low byte, by its bits

def ce.lowbyte(x: U32) -> U32:
  match x:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, r}}}}}}}}}:
      U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}}

def ce.mask_low(x: U32) -> {U32.and(255, x) == ce.lowbyte(x) : U32}:
  match x:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, +r}}}}}}}}}:
      %Equal.sym(Word(24n), Word.and(24n, Word.zero(24n), r), Word.zero(24n), PW.cw.wa_zero_l(24n, r)) : {U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, _}}}}}}}}} == U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}} : U32}
      {==}

def ce.low_idem(x: U32) -> {ce.lowbyte(ce.lowbyte(x)) == ce.lowbyte(x) : U32}:
  match x:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, r}}}}}}}}}:
      {==}

# the table index (x & 255) has the low byte 255 & x
def ce.low_and(+x: U32) -> {ce.lowbyte(U32.and(x, 255)) == U32.and(255, x) : U32}:
  %PW.cw.ua_comm(255, x) : {ce.lowbyte(_) == U32.and(255, x) : U32}
  %Equal.sym(U32, U32.and(255, x), ce.lowbyte(x), ce.mask_low(x)) : {ce.lowbyte(_) == U32.and(255, x) : U32}
  %Equal.sym(U32, U32.and(255, x), ce.lowbyte(x), ce.mask_low(x)) : {ce.lowbyte(ce.lowbyte(x)) == _ : U32}
  ce.low_idem(x)

# The reflected engine, with its test of the lowest bit as the bit itself

def ce.rb(n: Nat, +p: U32, +c: U32) -> U32:
  match n:
    case 0n:
      c
    case 1n+k:
      ce.rb(k, p, C.r32.pick(PW.cw.odd(c), p, c))

def ce.r_rb(n: Nat, +p: U32, +c: U32) -> {C.r32.bits(n, p, c) == ce.rb(n, p, c) : U32}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(Bool, U32.is_eq(U32.and(c, 1), 1), PW.cw.odd(c), PW.cw.odd_test(c)) : {C.r32.bits(k, p, C.r32.pick(_, p, c)) == ce.rb(k, p, C.r32.pick(PW.cw.odd(c), p, c)) : U32}
      ce.r_rb(k, p, C.r32.pick(PW.cw.odd(c), p, c))

# one reflected step commutes with XOR
def ce.rpick_lin(x: U32, y: U32, +p: U32) -> {C.r32.pick(PW.cw.odd(U32.xor(x, y)), p, U32.xor(x, y)) == U32.xor(C.r32.pick(PW.cw.odd(x), p, x), C.r32.pick(PW.cw.odd(y), p, y)) : U32}:
  match x y:
    case U32{WCon{True{}, +xt}} U32{WCon{True{}, +yt}}:
      Equal.trans(U32, U32.shr(U32.xor(U32{WCon{True{}, xt}}, U32{WCon{True{}, yt}})), U32.xor(U32.shr(U32{WCon{True{}, xt}}), U32.shr(U32{WCon{True{}, yt}})), U32.xor(U32.xor(U32.shr(U32{WCon{True{}, xt}}), p), U32.xor(U32.shr(U32{WCon{True{}, yt}}), p)), PW.cw.shr_xor(U32{WCon{True{}, xt}}, U32{WCon{True{}, yt}}), Equal.sym(U32, U32.xor(U32.xor(U32.shr(U32{WCon{True{}, xt}}), p), U32.xor(U32.shr(U32{WCon{True{}, yt}}), p)), U32.xor(U32.shr(U32{WCon{True{}, xt}}), U32.shr(U32{WCon{True{}, yt}})), PW.cw.x_cancel(U32.shr(U32{WCon{True{}, xt}}), U32.shr(U32{WCon{True{}, yt}}), p)))
    case U32{WCon{True{}, +xt}} U32{WCon{False{}, +yt}}:
      %Equal.sym(U32, U32.shr(U32.xor(U32{WCon{True{}, xt}}, U32{WCon{False{}, yt}})), U32.xor(U32.shr(U32{WCon{True{}, xt}}), U32.shr(U32{WCon{False{}, yt}})), PW.cw.shr_xor(U32{WCon{True{}, xt}}, U32{WCon{False{}, yt}})) : {U32.xor(_, p) == U32.xor(U32.xor(U32.shr(U32{WCon{True{}, xt}}), p), U32.shr(U32{WCon{False{}, yt}})) : U32}
      PW.cw.x_swap(U32.shr(U32{WCon{True{}, xt}}), U32.shr(U32{WCon{False{}, yt}}), p)
    case U32{WCon{False{}, +xt}} U32{WCon{True{}, +yt}}:
      %Equal.sym(U32, U32.shr(U32.xor(U32{WCon{False{}, xt}}, U32{WCon{True{}, yt}})), U32.xor(U32.shr(U32{WCon{False{}, xt}}), U32.shr(U32{WCon{True{}, yt}})), PW.cw.shr_xor(U32{WCon{False{}, xt}}, U32{WCon{True{}, yt}})) : {U32.xor(_, p) == U32.xor(U32.shr(U32{WCon{False{}, xt}}), U32.xor(U32.shr(U32{WCon{True{}, yt}}), p)) : U32}
      PW.cw.ux_assoc(U32.shr(U32{WCon{False{}, xt}}), U32.shr(U32{WCon{True{}, yt}}), p)
    case U32{WCon{False{}, +xt}} U32{WCon{False{}, +yt}}:
      PW.cw.shr_xor(U32{WCon{False{}, xt}}, U32{WCon{False{}, yt}})

# eight (any number of) reflected steps commute with XOR
def ce.r_lin(n: Nat, +p: U32, +x: U32, +y: U32) -> {ce.rb(n, p, U32.xor(x, y)) == U32.xor(ce.rb(n, p, x), ce.rb(n, p, y)) : U32}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(U32, C.r32.pick(PW.cw.odd(U32.xor(x, y)), p, U32.xor(x, y)), U32.xor(C.r32.pick(PW.cw.odd(x), p, x), C.r32.pick(PW.cw.odd(y), p, y)), ce.rpick_lin(x, y, p)) : {ce.rb(k, p, _) == U32.xor(ce.rb(k, p, C.r32.pick(PW.cw.odd(x), p, x)), ce.rb(k, p, C.r32.pick(PW.cw.odd(y), p, y))) : U32}
      ce.r_lin(k, p, C.r32.pick(PW.cw.odd(x), p, x), C.r32.pick(PW.cw.odd(y), p, y))

# The tables' entries: entry i of a table is an engine's eight steps on the
# byte i (reflected) or on i placed at the top byte (most significant bit
# first). As Data, so that a lemma about every table can take one.

type CrcPfEng is Data:
  CrcPfR{p: U32}
  CrcPfN{p: U32, s: Nat, tb: U32, m: U32}

def ce.ev(e: CrcPfEng, x: U32) -> U32:
  match e:
    case CrcPfR{p}:
      C.r32.bits(8n, p, x)
    case CrcPfN{p, s, tb, m}:
      C.n32.bits(8n, p, tb, m, U32.shln(x, s))

# the table fills' model: the list of slots after n writes from slot k
def ce.fill_model(n: Nat, xs: List<&2, U32>, +e: CrcPfEng, +k: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+j:
      ce.fill_model(j, List.set(&2, U32, xs, A.Arrays.index(8n, U32.from_nat(k)), ce.ev(e, U32.from_nat(k))), e, 1n+k)

# The most-significant-first engine, with its test of the top bit k as the
# bit itself and its mask applied constant first

def ce.npick(b: Bool, +p: U32, +m: U32, x: U32) -> U32:
  match b:
    case True{}:
      U32.and(m, U32.xor(U32.shl(x), p))
    case False{}:
      U32.and(m, U32.shl(x))

def ce.nb(n: Nat, +p: U32, +k: Nat, +m: U32, +c: U32) -> U32:
  match n:
    case 0n:
      c
    case 1n+j:
      ce.nb(j, p, k, m, ce.npick(PW.cw.bitk(k, c), p, m, c))

def ce.pick_np(b: Bool, +p: U32, +m: U32, +x: U32) -> {C.n32.pick(b, p, m, x) == ce.npick(b, p, m, x) : U32}:
  match b:
    case True{}:
      PW.cw.ua_comm(U32.xor(U32.shl(x), p), m)
    case False{}:
      PW.cw.ua_comm(U32.shl(x), m)

# one step commutes with XOR
def ce.npick_lin(bx: Bool, by: Bool, +p: U32, +m: U32, +x: U32, +y: U32) -> {ce.npick(Bool.xor(bx, by), p, m, U32.xor(x, y)) == U32.xor(ce.npick(bx, p, m, x), ce.npick(by, p, m, y)) : U32}:
  match bx by:
    case True{} True{}:
      %PW.cw.ua_xor(m, U32.xor(U32.shl(x), p), U32.xor(U32.shl(y), p)) : {U32.and(m, U32.shl(U32.xor(x, y))) == _ : U32}
      %Equal.sym(U32, U32.xor(U32.xor(U32.shl(x), p), U32.xor(U32.shl(y), p)), U32.xor(U32.shl(x), U32.shl(y)), PW.cw.x_cancel(U32.shl(x), U32.shl(y), p)) : {U32.and(m, U32.shl(U32.xor(x, y))) == U32.and(m, _) : U32}
      %PW.cw.shl_xor(x, y) : {U32.and(m, U32.shl(U32.xor(x, y))) == U32.and(m, _) : U32}
      {==}
    case True{} False{}:
      %Equal.sym(U32, U32.shl(U32.xor(x, y)), U32.xor(U32.shl(x), U32.shl(y)), PW.cw.shl_xor(x, y)) : {U32.and(m, U32.xor(_, p)) == U32.xor(U32.and(m, U32.xor(U32.shl(x), p)), U32.and(m, U32.shl(y))) : U32}
      %Equal.sym(U32, U32.xor(U32.xor(U32.shl(x), U32.shl(y)), p), U32.xor(U32.xor(U32.shl(x), p), U32.shl(y)), PW.cw.x_swap(U32.shl(x), U32.shl(y), p)) : {U32.and(m, _) == U32.xor(U32.and(m, U32.xor(U32.shl(x), p)), U32.and(m, U32.shl(y))) : U32}
      PW.cw.ua_xor(m, U32.xor(U32.shl(x), p), U32.shl(y))
    case False{} True{}:
      %Equal.sym(U32, U32.shl(U32.xor(x, y)), U32.xor(U32.shl(x), U32.shl(y)), PW.cw.shl_xor(x, y)) : {U32.and(m, U32.xor(_, p)) == U32.xor(U32.and(m, U32.shl(x)), U32.and(m, U32.xor(U32.shl(y), p))) : U32}
      %Equal.sym(U32, U32.xor(U32.xor(U32.shl(x), U32.shl(y)), p), U32.xor(U32.shl(x), U32.xor(U32.shl(y), p)), PW.cw.ux_assoc(U32.shl(x), U32.shl(y), p)) : {U32.and(m, _) == U32.xor(U32.and(m, U32.shl(x)), U32.and(m, U32.xor(U32.shl(y), p))) : U32}
      PW.cw.ua_xor(m, U32.shl(x), U32.xor(U32.shl(y), p))
    case False{} False{}:
      %Equal.sym(U32, U32.shl(U32.xor(x, y)), U32.xor(U32.shl(x), U32.shl(y)), PW.cw.shl_xor(x, y)) : {U32.and(m, _) == U32.xor(U32.and(m, U32.shl(x)), U32.and(m, U32.shl(y))) : U32}
      PW.cw.ua_xor(m, U32.shl(x), U32.shl(y))

def ce.n_lin(n: Nat, +p: U32, +k: Nat, +m: U32, +x: U32, +y: U32) -> {ce.nb(n, p, k, m, U32.xor(x, y)) == U32.xor(ce.nb(n, p, k, m, x), ce.nb(n, p, k, m, y)) : U32}:
  match n:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(Bool, PW.cw.bitk(k, U32.xor(x, y)), Bool.xor(PW.cw.bitk(k, x), PW.cw.bitk(k, y)), PW.cw.bitk_xor(k, x, y)) : {ce.nb(j, p, k, m, ce.npick(_, p, m, U32.xor(x, y))) == U32.xor(ce.nb(j, p, k, m, ce.npick(PW.cw.bitk(k, x), p, m, x)), ce.nb(j, p, k, m, ce.npick(PW.cw.bitk(k, y), p, m, y))) : U32}
      %Equal.sym(U32, ce.npick(Bool.xor(PW.cw.bitk(k, x), PW.cw.bitk(k, y)), p, m, U32.xor(x, y)), U32.xor(ce.npick(PW.cw.bitk(k, x), p, m, x), ce.npick(PW.cw.bitk(k, y), p, m, y)), ce.npick_lin(PW.cw.bitk(k, x), PW.cw.bitk(k, y), p, m, x, y)) : {ce.nb(j, p, k, m, _) == U32.xor(ce.nb(j, p, k, m, ce.npick(PW.cw.bitk(k, x), p, m, x)), ce.nb(j, p, k, m, ce.npick(PW.cw.bitk(k, y), p, m, y))) : U32}
      ce.n_lin(j, p, k, m, ce.npick(PW.cw.bitk(k, x), p, m, x), ce.npick(PW.cw.bitk(k, y), p, m, y))

# the engine's result is masked
def ce.npick_mask(b: Bool, +p: U32, +m: U32, +x: U32) -> {U32.and(m, ce.npick(b, p, m, x)) == ce.npick(b, p, m, x) : U32}:
  match b:
    case True{}:
      %PW.cw.ua_assoc(m, m, U32.xor(U32.shl(x), p)) : {_ == U32.and(m, U32.xor(U32.shl(x), p)) : U32}
      %Equal.sym(U32, U32.and(m, m), m, PW.cw.ua_idem(m)) : {U32.and(_, U32.xor(U32.shl(x), p)) == U32.and(m, U32.xor(U32.shl(x), p)) : U32}
      {==}
    case False{}:
      %PW.cw.ua_assoc(m, m, U32.shl(x)) : {_ == U32.and(m, U32.shl(x)) : U32}
      %Equal.sym(U32, U32.and(m, m), m, PW.cw.ua_idem(m)) : {U32.and(_, U32.shl(x)) == U32.and(m, U32.shl(x)) : U32}
      {==}

def ce.nb_mask(j: Nat, +p: U32, +k: Nat, +m: U32, +x: U32) -> {U32.and(m, ce.nb(1n+j, p, k, m, x)) == ce.nb(1n+j, p, k, m, x) : U32}:
  match j:
    case 0n:
      ce.npick_mask(PW.cw.bitk(k, x), p, m, x)
    case 1n+i:
      ce.nb_mask(i, p, k, m, ce.npick(PW.cw.bitk(k, x), p, m, x))

# The most-significant-first byte step, for a width w of 8 to 32 (s = w - 8,
# k = w - 1, m = 2^w - 1, win = 255 << s, the input byte window): the
# register XOR the input byte is the window part B (the table index, in
# place) XOR the rest A, eight steps are linear, and on A (whose window is
# clear) they only shift. eW and eH are those two facts for the register c;
# proof_cases.bend proves them for each width by computation.

def ce.unclear(+win: U32, +c: U32) -> {U32.xor(U32.and(U32.not(win), c), U32.and(win, c)) == c : U32}:
  %PW.cw.ux_clear(win, c) : {U32.xor(_, U32.and(win, c)) == c : U32}
  %Equal.sym(U32, U32.xor(U32.xor(c, U32.and(win, c)), U32.and(win, c)), U32.xor(c, U32.xor(U32.and(win, c), U32.and(win, c))), PW.cw.ux_assoc(c, U32.and(win, c), U32.and(win, c))) : {_ == c : U32}
  %Equal.sym(U32, U32.xor(U32.and(win, c), U32.and(win, c)), 0, PW.cw.ux_self(U32.and(win, c))) : {U32.xor(c, _) == c : U32}
  PW.cw.ux_zero(c)

def ce.core_split(+s: Nat, +win: U32, +c: U32, +h: U32, +eW: {U32.shln(U32.and(255, U32.shrn(c, s)), s) == U32.and(win, c) : U32}) -> {U32.xor(U32.and(U32.not(win), c), U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s)) == U32.xor(c, U32.shln(U32.and(255, h), s)) : U32}:
  %Equal.sym(U32, U32.and(255, U32.xor(U32.shrn(c, s), h)), U32.xor(U32.and(255, U32.shrn(c, s)), U32.and(255, h)), PW.cw.ua_xor(255, U32.shrn(c, s), h)) : {U32.xor(U32.and(U32.not(win), c), U32.shln(_, s)) == U32.xor(c, U32.shln(U32.and(255, h), s)) : U32}
  %Equal.sym(U32, U32.shln(U32.xor(U32.and(255, U32.shrn(c, s)), U32.and(255, h)), s), U32.xor(U32.shln(U32.and(255, U32.shrn(c, s)), s), U32.shln(U32.and(255, h), s)), PW.cw.shln_xor(s, U32.and(255, U32.shrn(c, s)), U32.and(255, h))) : {U32.xor(U32.and(U32.not(win), c), _) == U32.xor(c, U32.shln(U32.and(255, h), s)) : U32}
  %Equal.sym(U32, U32.shln(U32.and(255, U32.shrn(c, s)), s), U32.and(win, c), eW) : {U32.xor(U32.and(U32.not(win), c), U32.xor(_, U32.shln(U32.and(255, h), s))) == U32.xor(c, U32.shln(U32.and(255, h), s)) : U32}
  %PW.cw.ux_assoc(U32.and(U32.not(win), c), U32.and(win, c), U32.shln(U32.and(255, h), s)) : {_ == U32.xor(c, U32.shln(U32.and(255, h), s)) : U32}
  %Equal.sym(U32, U32.xor(U32.and(U32.not(win), c), U32.and(win, c)), c, ce.unclear(win, c)) : {U32.xor(_, U32.shln(U32.and(255, h), s)) == U32.xor(c, U32.shln(U32.and(255, h), s)) : U32}
  {==}

def ce.core_n(+s: Nat, +k: Nat, +m: U32, +win: U32, +c: U32, +h: U32, +p: U32, +eW: {U32.shln(U32.and(255, U32.shrn(c, s)), s) == U32.and(win, c) : U32}, +eH: {ce.nb(8n, p, k, m, U32.and(U32.not(win), c)) == U32.and(m, U32.shln(c, 8n)) : U32}) -> {U32.and(m, U32.xor(U32.shln(c, 8n), ce.nb(8n, p, k, m, U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s)))) == ce.nb(8n, p, k, m, U32.xor(c, U32.shln(U32.and(255, h), s))) : U32}:
  %ce.core_split(s, win, c, h, eW) : {U32.and(m, U32.xor(U32.shln(c, 8n), ce.nb(8n, p, k, m, U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s)))) == ce.nb(8n, p, k, m, _) : U32}
  %Equal.sym(U32, ce.nb(8n, p, k, m, U32.xor(U32.and(U32.not(win), c), U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s))), U32.xor(ce.nb(8n, p, k, m, U32.and(U32.not(win), c)), ce.nb(8n, p, k, m, U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s))), ce.n_lin(8n, p, k, m, U32.and(U32.not(win), c), U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s))) : {U32.and(m, U32.xor(U32.shln(c, 8n), ce.nb(8n, p, k, m, U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s)))) == _ : U32}
  %Equal.sym(U32, ce.nb(8n, p, k, m, U32.and(U32.not(win), c)), U32.and(m, U32.shln(c, 8n)), eH) : {U32.and(m, U32.xor(U32.shln(c, 8n), ce.nb(8n, p, k, m, U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s)))) == U32.xor(_, ce.nb(8n, p, k, m, U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s))) : U32}
  %Equal.sym(U32, U32.and(m, U32.xor(U32.shln(c, 8n), ce.nb(8n, p, k, m, U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s)))), U32.xor(U32.and(m, U32.shln(c, 8n)), U32.and(m, ce.nb(8n, p, k, m, U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s)))), PW.cw.ua_xor(m, U32.shln(c, 8n), ce.nb(8n, p, k, m, U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s)))) : {_ == U32.xor(U32.and(m, U32.shln(c, 8n)), ce.nb(8n, p, k, m, U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s))) : U32}
  %Equal.sym(U32, U32.and(m, ce.nb(8n, p, k, m, U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s))), ce.nb(8n, p, k, m, U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s)), ce.nb_mask(7n, p, k, m, U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s))) : {U32.xor(U32.and(m, U32.shln(c, 8n)), _) == U32.xor(U32.and(m, U32.shln(c, 8n)), ce.nb(8n, p, k, m, U32.shln(U32.and(255, U32.xor(U32.shrn(c, s), h)), s))) : U32}
  {==}

# Widths above 32: the top bit 1 << (w - 1) is shifted out (0), the mask is
# every bit, and so are the input byte bits (s >= 25): eight steps are
# eight shifts, and the byte never reaches the register.

def ce.shlr(n: Nat, x: U32) -> U32:
  match n:
    case 0n:
      x
    case 1n+i:
      ce.shlr(i, U32.shl(x))

def ce.shlr_xor(n: Nat, +a: U32, +b: U32) -> {ce.shlr(n, U32.xor(a, b)) == U32.xor(ce.shlr(n, a), ce.shlr(n, b)) : U32}:
  match n:
    case 0n:
      {==}
    case 1n+i:
      %Equal.sym(U32, U32.shl(U32.xor(a, b)), U32.xor(U32.shl(a), U32.shl(b)), PW.cw.shl_xor(a, b)) : {ce.shlr(i, _) == U32.xor(ce.shlr(i, U32.shl(a)), ce.shlr(i, U32.shl(b))) : U32}
      ce.shlr_xor(i, U32.shl(a), U32.shl(b))

def ce.bit_deg(+j: Nat, +x: U32) -> {PW.cw.bitk(Nat.add(32n, j), x) == False{} : Bool}:
  %Equal.sym(U32, U32.shrn(U32.shrn(x, j), 32n), 0, PW.cw.shr32(U32.shrn(x, j))) : {PW.cw.odd(_) == False{} : Bool}
  {==}

def ce.m_deg(+j: Nat) -> {U32.sub(U32.shln(1, Nat.add(33n, j)), 1) == 4294967295 : U32}:
  %Equal.sym(U32, U32.shln(U32.shln(1, j), 32n), 0, PW.cw.shl32(U32.shln(1, j))) : {U32.sub(U32.shl(_), 1) == 4294967295 : U32}
  {==}

def ce.nb_deg(n: Nat, +p: U32, +j: Nat, +x: U32) -> {ce.nb(n, p, Nat.add(32n, j), 4294967295, x) == ce.shlr(n, x) : U32}:
  match n:
    case 0n:
      {==}
    case 1n+i:
      %Equal.sym(Bool, PW.cw.bitk(Nat.add(32n, j), x), False{}, ce.bit_deg(j, x)) : {ce.nb(i, p, Nat.add(32n, j), 4294967295, ce.npick(_, p, 4294967295, x)) == ce.shlr(i, U32.shl(x)) : U32}
      %Equal.sym(U32, U32.and(4294967295, U32.shl(x)), U32.shl(x), PW.cw.ua_ones_l(U32.shl(x))) : {ce.nb(i, p, Nat.add(32n, j), 4294967295, _) == ce.shlr(i, U32.shl(x)) : U32}
      ce.nb_deg(i, p, j, U32.shl(x))

def ce.shlr_out(+j: Nat, +z: U32) -> {ce.shlr(8n, U32.shln(z, Nat.add(25n, j))) == 0 : U32}:
  %Equal.sym(U32, U32.shln(U32.shln(z, j), 32n), 0, PW.cw.shl32(U32.shln(z, j))) : {U32.shl(_) == 0 : U32}
  {==}

def ce.core_deg(+j: Nat, +c: U32, +h: U32, +p: U32) -> {U32.and(U32.sub(U32.shln(1, Nat.add(33n, j)), 1), U32.xor(U32.shln(c, 8n), ce.nb(8n, p, Nat.add(32n, j), U32.sub(U32.shln(1, Nat.add(33n, j)), 1), U32.shln(U32.and(255, U32.xor(U32.shrn(c, Nat.add(25n, j)), h)), Nat.add(25n, j))))) == ce.nb(8n, p, Nat.add(32n, j), U32.sub(U32.shln(1, Nat.add(33n, j)), 1), U32.xor(c, U32.shln(U32.and(255, h), Nat.add(25n, j)))) : U32}:
  %Equal.sym(U32, U32.sub(U32.shln(1, Nat.add(33n, j)), 1), 4294967295, ce.m_deg(j)) : {U32.and(_, U32.xor(U32.shln(c, 8n), ce.nb(8n, p, Nat.add(32n, j), _, U32.shln(U32.and(255, U32.xor(U32.shrn(c, Nat.add(25n, j)), h)), Nat.add(25n, j))))) == ce.nb(8n, p, Nat.add(32n, j), _, U32.xor(c, U32.shln(U32.and(255, h), Nat.add(25n, j)))) : U32}
  %Equal.sym(U32, U32.and(4294967295, U32.xor(U32.shln(c, 8n), ce.nb(8n, p, Nat.add(32n, j), 4294967295, U32.shln(U32.and(255, U32.xor(U32.shrn(c, Nat.add(25n, j)), h)), Nat.add(25n, j))))), U32.xor(U32.shln(c, 8n), ce.nb(8n, p, Nat.add(32n, j), 4294967295, U32.shln(U32.and(255, U32.xor(U32.shrn(c, Nat.add(25n, j)), h)), Nat.add(25n, j)))), PW.cw.ua_ones_l(U32.xor(U32.shln(c, 8n), ce.nb(8n, p, Nat.add(32n, j), 4294967295, U32.shln(U32.and(255, U32.xor(U32.shrn(c, Nat.add(25n, j)), h)), Nat.add(25n, j)))))) : {_ == ce.nb(8n, p, Nat.add(32n, j), 4294967295, U32.xor(c, U32.shln(U32.and(255, h), Nat.add(25n, j)))) : U32}
  %Equal.sym(U32, ce.nb(8n, p, Nat.add(32n, j), 4294967295, U32.shln(U32.and(255, U32.xor(U32.shrn(c, Nat.add(25n, j)), h)), Nat.add(25n, j))), ce.shlr(8n, U32.shln(U32.and(255, U32.xor(U32.shrn(c, Nat.add(25n, j)), h)), Nat.add(25n, j))), ce.nb_deg(8n, p, j, U32.shln(U32.and(255, U32.xor(U32.shrn(c, Nat.add(25n, j)), h)), Nat.add(25n, j)))) : {U32.xor(U32.shln(c, 8n), _) == ce.nb(8n, p, Nat.add(32n, j), 4294967295, U32.xor(c, U32.shln(U32.and(255, h), Nat.add(25n, j)))) : U32}
  %Equal.sym(U32, ce.shlr(8n, U32.shln(U32.and(255, U32.xor(U32.shrn(c, Nat.add(25n, j)), h)), Nat.add(25n, j))), 0, ce.shlr_out(j, U32.and(255, U32.xor(U32.shrn(c, Nat.add(25n, j)), h)))) : {U32.xor(U32.shln(c, 8n), _) == ce.nb(8n, p, Nat.add(32n, j), 4294967295, U32.xor(c, U32.shln(U32.and(255, h), Nat.add(25n, j)))) : U32}
  %Equal.sym(U32, U32.xor(U32.shln(c, 8n), 0), U32.shln(c, 8n), PW.cw.ux_zero(U32.shln(c, 8n))) : {_ == ce.nb(8n, p, Nat.add(32n, j), 4294967295, U32.xor(c, U32.shln(U32.and(255, h), Nat.add(25n, j)))) : U32}
  %Equal.sym(U32, ce.nb(8n, p, Nat.add(32n, j), 4294967295, U32.xor(c, U32.shln(U32.and(255, h), Nat.add(25n, j)))), ce.shlr(8n, U32.xor(c, U32.shln(U32.and(255, h), Nat.add(25n, j)))), ce.nb_deg(8n, p, j, U32.xor(c, U32.shln(U32.and(255, h), Nat.add(25n, j))))) : {U32.shln(c, 8n) == _ : U32}
  %Equal.sym(U32, ce.shlr(8n, U32.xor(c, U32.shln(U32.and(255, h), Nat.add(25n, j)))), U32.xor(ce.shlr(8n, c), ce.shlr(8n, U32.shln(U32.and(255, h), Nat.add(25n, j)))), ce.shlr_xor(8n, c, U32.shln(U32.and(255, h), Nat.add(25n, j)))) : {U32.shln(c, 8n) == _ : U32}
  %Equal.sym(U32, ce.shlr(8n, U32.shln(U32.and(255, h), Nat.add(25n, j))), 0, ce.shlr_out(j, U32.and(255, h))) : {U32.shln(c, 8n) == U32.xor(ce.shlr(8n, c), _) : U32}
  Equal.sym(U32, U32.xor(ce.shlr(8n, c), 0), U32.shln(c, 8n), PW.cw.ux_zero(ce.shlr(8n, c)))
