import Base
import ../u32/u32.bend as U
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ./word64.bend as W
import ./proof_value.bend as P
import ./proof_shift.bend as PS
import ./LAWS.bend as Laws

def Laws.add_wraps():
  {==}

def Laws.sub_wraps():
  {==}

def Laws.hi_of_parts():
  {==}

def Laws.lo_of_parts():
  {==}

def Laws.shl_crosses_halves():
  {==}

def Laws.shr_crosses_halves():
  {==}

def Laws.mul_of_max_halves():
  {==}

def Laws.show_max():
  {==}

def Laws.show_hex_parts():
  {==}

def Laws.show_hex_zero():
  {==}

def Laws.lo_from_u32(a):
  {==}

def Laws.hi_from_parts(h, l):
  {==}

def Laws.lo_from_parts(h, l):
  {==}

def Laws.parts_of(v):
  match v:
    case W.W64{h, l}:
      {==}

# The value and the order (proof_value.bend: the order of two halves of any
# width, instantiated at 32)

def Laws.to_nat_parts(h, l):
  {==}

def wp.pick_lex(c: Cmp, -al: U32, -bl: U32) -> {W.W64.cmp.pick(c, al, bl) == P.wv.lex(c, U32.cmp(al, bl)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Laws.cmp_value(a, b):
  match a b:
    case W.W64{U32{+ahw}, U32{+alw}} W.W64{U32{+bhw}, U32{+blw}}:
      Equal.trans(Cmp, W.W64.cmp.pick(Word.cmp(32n, ahw, bhw), U32{alw}, U32{blw}), P.wv.lex(Word.cmp(32n, ahw, bhw), Word.cmp(32n, alw, blw)), Nat.cmp(P.wv.V(32n, ahw, alw), P.wv.V(32n, bhw, blw)), wp.pick_lex(Word.cmp(32n, ahw, bhw), U32{alw}, U32{blw}), P.wv.gcmp(32n, ahw, alw, bhw, blw))

def Laws.lt_value(a, b):
  %Laws.cmp_value(a, b) : {Cmp.is_lt(W.W64.cmp(a, b)) == Cmp.is_lt(_) : Bool}
  {==}

def Laws.le_value(a, b):
  %Laws.cmp_value(a, b) : {Cmp.is_le(W.W64.cmp(a, b)) == Cmp.is_le(_) : Bool}
  {==}

def Laws.eq_value(a, b):
  %Laws.cmp_value(a, b) : {Cmp.is_eq(W.W64.cmp(a, b)) == Cmp.is_eq(_) : Bool}
  {==}

def wp.of_halves(p: Word(32n) & Word(32n)) -> W.W64:
  (h, l) = p
  W.W64{U32{h}, U32{l}}

def Laws.value_eq(a, b, e):
  match a b:
    case W.W64{U32{+ahw}, U32{+alw}} W.W64{U32{+bhw}, U32{+blw}}:
      Equal.cong(Word(32n) & Word(32n), W.W64, p => wp.of_halves(p), (ahw, alw), (bhw, blw), P.wv.halves_eq(32n, ahw, alw, bhw, blw, e))

def Laws.cmp_hi_lt(a, b, h):
  match a b:
    case W.W64{ah, al} W.W64{bh, bl}:
      %Equal.sym(Cmp, U32.cmp(ah, bh), LT{}, h) : {W.W64.cmp.pick(_, al, bl) == LT{} : Cmp}
      {==}

def Laws.cmp_hi_gt(a, b, h):
  match a b:
    case W.W64{ah, al} W.W64{bh, bl}:
      %Equal.sym(Cmp, U32.cmp(ah, bh), GT{}, h) : {W.W64.cmp.pick(_, al, bl) == GT{} : Cmp}
      {==}

def Laws.cmp_hi_eq(a, b, h):
  match a b:
    case W.W64{ah, +al} W.W64{bh, +bl}:
      %Equal.sym(Cmp, U32.cmp(ah, bh), EQ{}, h) : {W.W64.cmp.pick(_, al, bl) == U32.cmp(al, bl) : Cmp}
      {==}

# Addition and subtraction: W64.add and W64.sub are proof_value.bend's
# halves at width 32, with the carry or borrow between them

def wp.add_split.fin(-ahw: Word(32n), -alw: Word(32n), -bhw: Word(32n), -blw: Word(32n), cb: Bool) -> {W.W64{U32.add(U32{Word.add(32n, ahw, bhw)}, W.W64.bit(cb)), U32{Word.add(32n, alw, blw)}} == W.W64{U32{Word.add(32n, Word.add(32n, ahw, bhw), P.wv.bitw(32n, cb))}, U32{Word.add(32n, alw, blw)}} : W.W64}:
  match cb:
    case True{}:
      {==}
    case False{}:
      {==}

def wp.add_split.go(+ahw: Word(32n), +alw: Word(32n), +bhw: Word(32n), +blw: Word(32n), cb: Bool, e: {Cmp.is_lt(Word.cmp(32n, Word.add(32n, alw, blw), alw)) == cb : Bool}) -> {W.W64.add(W.W64{U32{ahw}, U32{alw}}, W.W64{U32{bhw}, U32{blw}}) == W.W64{U32{P.wv.addhi(32n, ahw, alw, bhw, blw)}, U32{Word.add(32n, alw, blw)}} : W.W64}:
  %Equal.sym(Bool, Cmp.is_lt(Word.cmp(32n, Word.add(32n, alw, blw), alw)), cb, e) : {W.W64{U32.add(U32{Word.add(32n, ahw, bhw)}, W.W64.bit(_)), U32{Word.add(32n, alw, blw)}} == W.W64{U32{Word.add(32n, Word.add(32n, ahw, bhw), P.wv.bitw(32n, _))}, U32{Word.add(32n, alw, blw)}} : W.W64}
  wp.add_split.fin(ahw, alw, bhw, blw, cb)

def wp.add_split(+ahw: Word(32n), +alw: Word(32n), +bhw: Word(32n), +blw: Word(32n)) -> {W.W64.add(W.W64{U32{ahw}, U32{alw}}, W.W64{U32{bhw}, U32{blw}}) == W.W64{U32{P.wv.addhi(32n, ahw, alw, bhw, blw)}, U32{Word.add(32n, alw, blw)}} : W.W64}:
  wp.add_split.go(ahw, alw, bhw, blw, Cmp.is_lt(Word.cmp(32n, Word.add(32n, alw, blw), alw)), {==})

def wp.sub_split.fin(-ahw: Word(32n), -alw: Word(32n), -bhw: Word(32n), -blw: Word(32n), cb: Bool) -> {W.W64{U32.sub(U32{Word.sub(32n, ahw, bhw)}, W.W64.bit(cb)), U32{Word.sub(32n, alw, blw)}} == W.W64{U32{Word.sub(32n, Word.sub(32n, ahw, bhw), P.wv.bitw(32n, cb))}, U32{Word.sub(32n, alw, blw)}} : W.W64}:
  match cb:
    case True{}:
      {==}
    case False{}:
      {==}

def wp.sub_split.go(+ahw: Word(32n), +alw: Word(32n), +bhw: Word(32n), +blw: Word(32n), cb: Bool, e: {Cmp.is_lt(Word.cmp(32n, alw, blw)) == cb : Bool}) -> {W.W64.sub(W.W64{U32{ahw}, U32{alw}}, W.W64{U32{bhw}, U32{blw}}) == W.W64{U32{P.wv.subhi(32n, ahw, alw, bhw, blw)}, U32{Word.sub(32n, alw, blw)}} : W.W64}:
  %Equal.sym(Bool, Cmp.is_lt(Word.cmp(32n, alw, blw)), cb, e) : {W.W64{U32.sub(U32{Word.sub(32n, ahw, bhw)}, W.W64.bit(_)), U32{Word.sub(32n, alw, blw)}} == W.W64{U32{Word.sub(32n, Word.sub(32n, ahw, bhw), P.wv.bitw(32n, _))}, U32{Word.sub(32n, alw, blw)}} : W.W64}
  wp.sub_split.fin(ahw, alw, bhw, blw, cb)

def wp.sub_split(+ahw: Word(32n), +alw: Word(32n), +bhw: Word(32n), +blw: Word(32n)) -> {W.W64.sub(W.W64{U32{ahw}, U32{alw}}, W.W64{U32{bhw}, U32{blw}}) == W.W64{U32{P.wv.subhi(32n, ahw, alw, bhw, blw)}, U32{Word.sub(32n, alw, blw)}} : W.W64}:
  wp.sub_split.go(ahw, alw, bhw, blw, Cmp.is_lt(Word.cmp(32n, alw, blw)), {==})

def Laws.add_wrap(a, b):
  match a b:
    case W.W64{U32{+ahw}, U32{+alw}} W.W64{U32{+bhw}, U32{+blw}}:
      +x : W.W64 = W.W64{U32{ahw}, U32{alw}}
      +y : W.W64 = W.W64{U32{bhw}, U32{blw}}
      +r : W.W64 = W.W64{U32{P.wv.addhi(32n, ahw, alw, bhw, blw)}, U32{Word.add(32n, alw, blw)}}
      %Equal.sym(W.W64, W.W64.add(x, y), r, wp.add_split(ahw, alw, bhw, blw)) : {Nat.add(W.W64.to_nat(_), U.U32Nat.dbl(64n, U.U32Nat.bit(W.W64.is_lt(_, x)))) == Nat.add(W.W64.to_nat(x), W.W64.to_nat(y)) : Nat}
      %Equal.sym(Bool, W.W64.is_lt(r, x), Nat.is_lt(W.W64.to_nat(r), W.W64.to_nat(x)), Laws.lt_value(r, x)) : {Nat.add(W.W64.to_nat(r), U.U32Nat.dbl(64n, U.U32Nat.bit(_))) == Nat.add(W.W64.to_nat(x), W.W64.to_nat(y)) : Nat}
      P.wv.gadd(32n, ahw, alw, bhw, blw)

def Laws.add_value(a, b, c, h):
  match a b c:
    case W.W64{U32{+ahw}, U32{+alw}} W.W64{U32{+bhw}, U32{+blw}} W.W64{U32{+chw}, U32{+clw}}:
      +x : W.W64 = W.W64{U32{ahw}, U32{alw}}
      +y : W.W64 = W.W64{U32{bhw}, U32{blw}}
      +r : W.W64 = W.W64{U32{P.wv.addhi(32n, ahw, alw, bhw, blw)}, U32{Word.add(32n, alw, blw)}}
      %Equal.sym(W.W64, W.W64.add(x, y), r, wp.add_split(ahw, alw, bhw, blw)) : {W.W64.to_nat(_) == Nat.add(W.W64.to_nat(x), W.W64.to_nat(y)) : Nat}
      P.wv.gadd_nowrap(32n, ahw, alw, bhw, blw, chw, clw, h)

def Laws.sub_wrap(a, b):
  match a b:
    case W.W64{U32{+ahw}, U32{+alw}} W.W64{U32{+bhw}, U32{+blw}}:
      +x : W.W64 = W.W64{U32{ahw}, U32{alw}}
      +y : W.W64 = W.W64{U32{bhw}, U32{blw}}
      +r : W.W64 = W.W64{U32{P.wv.subhi(32n, ahw, alw, bhw, blw)}, U32{Word.sub(32n, alw, blw)}}
      %Equal.sym(W.W64, W.W64.sub(x, y), r, wp.sub_split(ahw, alw, bhw, blw)) : {Nat.add(W.W64.to_nat(_), W.W64.to_nat(y)) == Nat.add(W.W64.to_nat(x), U.U32Nat.dbl(64n, U.U32Nat.bit(W.W64.is_lt(x, y)))) : Nat}
      %Equal.sym(Bool, W.W64.is_lt(x, y), Nat.is_lt(W.W64.to_nat(x), W.W64.to_nat(y)), Laws.lt_value(x, y)) : {Nat.add(W.W64.to_nat(r), W.W64.to_nat(y)) == Nat.add(W.W64.to_nat(x), U.U32Nat.dbl(64n, U.U32Nat.bit(_))) : Nat}
      P.wv.gsub(32n, ahw, alw, bhw, blw)

def Laws.sub_value(a, b, h):
  +s = W.W64.to_nat(W.W64.sub(a, b))
  +av = W.W64.to_nat(a)
  +bv = W.W64.to_nat(b)
  +el = Equal.trans(Bool, W.W64.is_lt(a, b), Nat.is_lt(av, bv), False{}, Laws.lt_value(a, b), P.wn.le_not_lt(bv, av, h))
  +e1 = Equal.trans(Nat, Nat.add(s, bv), Nat.add(av, U.U32Nat.dbl(64n, U.U32Nat.bit(False{}))), av, Equal.trans(Nat, Nat.add(s, bv), Nat.add(av, U.U32Nat.dbl(64n, U.U32Nat.bit(W.W64.is_lt(a, b)))), Nat.add(av, U.U32Nat.dbl(64n, U.U32Nat.bit(False{}))), Laws.sub_wrap(a, b), Equal.cong(Bool, Nat, x => Nat.add(av, U.U32Nat.dbl(64n, U.U32Nat.bit(x))), W.W64.is_lt(a, b), False{}, el)), P.wn.add_zero(av))
  %e1 : {s == Nat.sub(_, bv) : Nat}
  Equal.sym(Nat, Nat.sub(Nat.add(s, bv), bv), s, P.wn.sub_add(s, bv))

# Shifts: U32.shln and U32.shrn are proof_shift.bend's ws.shl and ws.shr at
# width 32; W64.shl and W64.shr are its shifts across two halves

def wq.shln(+w: Word(32n), k: Nat) -> {U32.shln(U32{w}, k) == U32{PS.ws.shl(32n, k, w)} : U32}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      %Equal.sym(U32, U32.shln(U32{w}, p), U32{PS.ws.shl(32n, p, w)}, wq.shln(w, p)) : {U32.shl(_) == U32{PS.ws.shl(32n, 1n+p, w)} : U32}
      {==}

def wq.shrn(+w: Word(32n), k: Nat) -> {U32.shrn(U32{w}, k) == U32{PS.ws.shr(32n, k, w)} : U32}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      %Equal.sym(U32, U32.shrn(U32{w}, p), U32{PS.ws.shr(32n, p, w)}, wq.shrn(w, p)) : {U32.shr(_) == U32{PS.ws.shr(32n, 1n+p, w)} : U32}
      {==}

def wq.shl.go(z: Bool, l32: Bool, l64: Bool, +k: Nat, +hw: Word(32n), +lw: Word(32n), +chw: Word(32n), +clw: Word(32n), ez: {Nat.is_eq(k, 0n) == z : Bool}, e32: {Nat.is_lt(k, 32n) == l32 : Bool}, e64: {Nat.is_lt(k, 64n) == l64 : Bool}, hk: {Nat.is_lt(k, 64n) == True{} : Bool}, +h: {Nat.is_le(U.U32Nat.dbl(k, W.W64.to_nat(W.W64{U32{hw}, U32{lw}})), W.W64.to_nat(W.W64{U32{chw}, U32{clw}})) == True{} : Bool}) -> {W.W64.to_nat(W.W64.shl.pick(z, l32, l64, k, W.W64{U32{hw}, U32{lw}})) == U.U32Nat.dbl(k, W.W64.to_nat(W.W64{U32{hw}, U32{lw}})) : Nat}:
  match z l32 l64:
    case True{} _ _:
      Equal.sym(Nat, U.U32Nat.dbl(k, W.W64.to_nat(W.W64{U32{hw}, U32{lw}})), W.W64.to_nat(W.W64{U32{hw}, U32{lw}}), Equal.cong(Nat, Nat, v => U.U32Nat.dbl(v, W.W64.to_nat(W.W64{U32{hw}, U32{lw}})), k, 0n, PS.ns.eq_zero(k, ez)))
    case False{} True{} _:
      %Equal.sym(U32, U32.shln(U32{hw}, k), U32{PS.ws.shl(32n, k, hw)}, wq.shln(hw, k)) : {W.W64.to_nat(W.W64{U32.or(_, U32.shrn(U32{lw}, Nat.sub(32n, k))), U32.shln(U32{lw}, k)}) == U.U32Nat.dbl(k, W.W64.to_nat(W.W64{U32{hw}, U32{lw}})) : Nat}
      %Equal.sym(U32, U32.shrn(U32{lw}, Nat.sub(32n, k)), U32{PS.ws.shr(32n, Nat.sub(32n, k), lw)}, wq.shrn(lw, Nat.sub(32n, k))) : {W.W64.to_nat(W.W64{U32.or(U32{PS.ws.shl(32n, k, hw)}, _), U32.shln(U32{lw}, k)}) == U.U32Nat.dbl(k, W.W64.to_nat(W.W64{U32{hw}, U32{lw}})) : Nat}
      %Equal.sym(U32, U32.shln(U32{lw}, k), U32{PS.ws.shl(32n, k, lw)}, wq.shln(lw, k)) : {W.W64.to_nat(W.W64{U32.or(U32{PS.ws.shl(32n, k, hw)}, U32{PS.ws.shr(32n, Nat.sub(32n, k), lw)}), _}) == U.U32Nat.dbl(k, W.W64.to_nat(W.W64{U32{hw}, U32{lw}})) : Nat}
      PS.ws.gshl_lo(32n, k, hw, lw, chw, clw, e32, h)
    case False{} False{} True{}:
      %Equal.sym(U32, U32.shln(U32{lw}, Nat.sub(k, 32n)), U32{PS.ws.shl(32n, Nat.sub(k, 32n), lw)}, wq.shln(lw, Nat.sub(k, 32n))) : {W.W64.to_nat(W.W64{_, 0}) == U.U32Nat.dbl(k, W.W64.to_nat(W.W64{U32{hw}, U32{lw}})) : Nat}
      PS.ws.gshl_hi(32n, k, hw, lw, chw, clw, PS.ns.le_of_not_lt(k, 32n, e32), h)
    case False{} False{} False{}:
      Empty.absurd({W.W64.to_nat(W.W64.shl.pick(False{}, False{}, False{}, k, W.W64{U32{hw}, U32{lw}})) == U.U32Nat.dbl(k, W.W64.to_nat(W.W64{U32{hw}, U32{lw}})) : Nat}, P.wn.ft(Equal.trans(Bool, False{}, Nat.is_lt(k, 64n), True{}, Equal.sym(Bool, Nat.is_lt(k, 64n), False{}, e64), hk)))

def Laws.shl_value(a, k, c, hk, h):
  match a c:
    case W.W64{U32{+hw}, U32{+lw}} W.W64{U32{+chw}, U32{+clw}}:
      wq.shl.go(Nat.is_eq(k, 0n), Nat.is_lt(k, 32n), Nat.is_lt(k, 64n), k, hw, lw, chw, clw, {==}, {==}, {==}, hk, h)

def wq.shr_le.go(z: Bool, l32: Bool, l64: Bool, +k: Nat, +hw: Word(32n), +lw: Word(32n), ez: {Nat.is_eq(k, 0n) == z : Bool}, e32: {Nat.is_lt(k, 32n) == l32 : Bool}, e64: {Nat.is_lt(k, 64n) == l64 : Bool}, hk: {Nat.is_lt(k, 64n) == True{} : Bool}) -> {Nat.is_le(U.U32Nat.dbl(k, W.W64.to_nat(W.W64.shr.pick(z, l32, l64, k, W.W64{U32{hw}, U32{lw}}))), W.W64.to_nat(W.W64{U32{hw}, U32{lw}})) == True{} : Bool}:
  match z l32 l64:
    case True{} _ _:
      %Equal.sym(Nat, k, 0n, PS.ns.eq_zero(k, ez)) : {Nat.is_le(U.U32Nat.dbl(_, W.W64.to_nat(W.W64{U32{hw}, U32{lw}})), W.W64.to_nat(W.W64{U32{hw}, U32{lw}})) == True{} : Bool}
      P.wn.le_refl(W.W64.to_nat(W.W64{U32{hw}, U32{lw}}))
    case False{} True{} _:
      %Equal.sym(U32, U32.shrn(U32{hw}, k), U32{PS.ws.shr(32n, k, hw)}, wq.shrn(hw, k)) : {Nat.is_le(U.U32Nat.dbl(k, W.W64.to_nat(W.W64{_, U32.or(U32.shrn(U32{lw}, k), U32.shln(U32{hw}, Nat.sub(32n, k)))})), W.W64.to_nat(W.W64{U32{hw}, U32{lw}})) == True{} : Bool}
      %Equal.sym(U32, U32.shrn(U32{lw}, k), U32{PS.ws.shr(32n, k, lw)}, wq.shrn(lw, k)) : {Nat.is_le(U.U32Nat.dbl(k, W.W64.to_nat(W.W64{U32{PS.ws.shr(32n, k, hw)}, U32.or(_, U32.shln(U32{hw}, Nat.sub(32n, k)))})), W.W64.to_nat(W.W64{U32{hw}, U32{lw}})) == True{} : Bool}
      %Equal.sym(U32, U32.shln(U32{hw}, Nat.sub(32n, k)), U32{PS.ws.shl(32n, Nat.sub(32n, k), hw)}, wq.shln(hw, Nat.sub(32n, k))) : {Nat.is_le(U.U32Nat.dbl(k, W.W64.to_nat(W.W64{U32{PS.ws.shr(32n, k, hw)}, U32.or(U32{PS.ws.shr(32n, k, lw)}, _)})), W.W64.to_nat(W.W64{U32{hw}, U32{lw}})) == True{} : Bool}
      PS.ws.gshr_lo_le(32n, k, hw, lw, e32)
    case False{} False{} True{}:
      %Equal.sym(U32, U32.shrn(U32{hw}, Nat.sub(k, 32n)), U32{PS.ws.shr(32n, Nat.sub(k, 32n), hw)}, wq.shrn(hw, Nat.sub(k, 32n))) : {Nat.is_le(U.U32Nat.dbl(k, W.W64.to_nat(W.W64{0, _})), W.W64.to_nat(W.W64{U32{hw}, U32{lw}})) == True{} : Bool}
      PS.ws.gshr_hi_le(32n, k, hw, lw, PS.ns.le_of_not_lt(k, 32n, e32))
    case False{} False{} False{}:
      Empty.absurd({Nat.is_le(U.U32Nat.dbl(k, W.W64.to_nat(W.W64.shr.pick(False{}, False{}, False{}, k, W.W64{U32{hw}, U32{lw}}))), W.W64.to_nat(W.W64{U32{hw}, U32{lw}})) == True{} : Bool}, P.wn.ft(Equal.trans(Bool, False{}, Nat.is_lt(k, 64n), True{}, Equal.sym(Bool, Nat.is_lt(k, 64n), False{}, e64), hk)))

def Laws.shr_value_le(a, k, hk):
  match a:
    case W.W64{U32{+hw}, U32{+lw}}:
      wq.shr_le.go(Nat.is_eq(k, 0n), Nat.is_lt(k, 32n), Nat.is_lt(k, 64n), k, hw, lw, {==}, {==}, {==}, hk)

def wq.shr_lt.go(z: Bool, l32: Bool, l64: Bool, +k: Nat, +hw: Word(32n), +lw: Word(32n), ez: {Nat.is_eq(k, 0n) == z : Bool}, e32: {Nat.is_lt(k, 32n) == l32 : Bool}, e64: {Nat.is_lt(k, 64n) == l64 : Bool}, hk: {Nat.is_lt(k, 64n) == True{} : Bool}) -> {Nat.is_lt(W.W64.to_nat(W.W64{U32{hw}, U32{lw}}), U.U32Nat.dbl(k, 1n+W.W64.to_nat(W.W64.shr.pick(z, l32, l64, k, W.W64{U32{hw}, U32{lw}})))) == True{} : Bool}:
  match z l32 l64:
    case True{} _ _:
      %Equal.sym(Nat, k, 0n, PS.ns.eq_zero(k, ez)) : {Nat.is_lt(W.W64.to_nat(W.W64{U32{hw}, U32{lw}}), U.U32Nat.dbl(_, 1n+W.W64.to_nat(W.W64{U32{hw}, U32{lw}}))) == True{} : Bool}
      PS.ns.lt_succ_self(W.W64.to_nat(W.W64{U32{hw}, U32{lw}}))
    case False{} True{} _:
      %Equal.sym(U32, U32.shrn(U32{hw}, k), U32{PS.ws.shr(32n, k, hw)}, wq.shrn(hw, k)) : {Nat.is_lt(W.W64.to_nat(W.W64{U32{hw}, U32{lw}}), U.U32Nat.dbl(k, 1n+W.W64.to_nat(W.W64{_, U32.or(U32.shrn(U32{lw}, k), U32.shln(U32{hw}, Nat.sub(32n, k)))}))) == True{} : Bool}
      %Equal.sym(U32, U32.shrn(U32{lw}, k), U32{PS.ws.shr(32n, k, lw)}, wq.shrn(lw, k)) : {Nat.is_lt(W.W64.to_nat(W.W64{U32{hw}, U32{lw}}), U.U32Nat.dbl(k, 1n+W.W64.to_nat(W.W64{U32{PS.ws.shr(32n, k, hw)}, U32.or(_, U32.shln(U32{hw}, Nat.sub(32n, k)))}))) == True{} : Bool}
      %Equal.sym(U32, U32.shln(U32{hw}, Nat.sub(32n, k)), U32{PS.ws.shl(32n, Nat.sub(32n, k), hw)}, wq.shln(hw, Nat.sub(32n, k))) : {Nat.is_lt(W.W64.to_nat(W.W64{U32{hw}, U32{lw}}), U.U32Nat.dbl(k, 1n+W.W64.to_nat(W.W64{U32{PS.ws.shr(32n, k, hw)}, U32.or(U32{PS.ws.shr(32n, k, lw)}, _)}))) == True{} : Bool}
      PS.ws.gshr_lo_lt(32n, k, hw, lw, e32)
    case False{} False{} True{}:
      %Equal.sym(U32, U32.shrn(U32{hw}, Nat.sub(k, 32n)), U32{PS.ws.shr(32n, Nat.sub(k, 32n), hw)}, wq.shrn(hw, Nat.sub(k, 32n))) : {Nat.is_lt(W.W64.to_nat(W.W64{U32{hw}, U32{lw}}), U.U32Nat.dbl(k, 1n+W.W64.to_nat(W.W64{0, _}))) == True{} : Bool}
      PS.ws.gshr_hi_lt(32n, k, hw, lw, PS.ns.le_of_not_lt(k, 32n, e32))
    case False{} False{} False{}:
      Empty.absurd({Nat.is_lt(W.W64.to_nat(W.W64{U32{hw}, U32{lw}}), U.U32Nat.dbl(k, 1n+W.W64.to_nat(W.W64.shr.pick(False{}, False{}, False{}, k, W.W64{U32{hw}, U32{lw}})))) == True{} : Bool}, P.wn.ft(Equal.trans(Bool, False{}, Nat.is_lt(k, 64n), True{}, Equal.sym(Bool, Nat.is_lt(k, 64n), False{}, e64), hk)))

def Laws.shr_value_lt(a, k, hk):
  match a:
    case W.W64{U32{+hw}, U32{+lw}}:
      wq.shr_lt.go(Nat.is_eq(k, 0n), Nat.is_lt(k, 32n), Nat.is_lt(k, 64n), k, hw, lw, {==}, {==}, {==}, hk)

def wq.shlbig.go(z: Bool, l32: Bool, l64: Bool, +k: Nat, -a: W.W64, ez: {Nat.is_eq(k, 0n) == z : Bool}, e32: {Nat.is_lt(k, 32n) == l32 : Bool}, e64: {Nat.is_lt(k, 64n) == l64 : Bool}, +h: {Nat.is_le(64n, k) == True{} : Bool}) -> {W.W64.shl.pick(z, l32, l64, k, a) == W.W64.zero() : W.W64}:
  match z l32 l64:
    case True{} _ _:
      Empty.absurd({a == W.W64.zero() : W.W64}, PS.ns.tf(Equal.trans(Bool, True{}, Nat.is_lt(k, 64n), False{}, Equal.sym(Bool, Nat.is_lt(k, 64n), Nat.is_lt(0n, 64n), Equal.cong(Nat, Bool, v => Nat.is_lt(v, 64n), k, 0n, PS.ns.eq_zero(k, ez))), P.wn.le_not_lt(64n, k, h))))
    case False{} True{} _:
      Empty.absurd({W.W64.shl.pick(False{}, True{}, l64, k, a) == W.W64.zero() : W.W64}, PS.ns.tf(Equal.trans(Bool, True{}, Nat.is_lt(k, 32n), False{}, Equal.sym(Bool, Nat.is_lt(k, 32n), True{}, e32), P.wn.le_not_lt(32n, k, P.wn.le_trans(32n, 64n, k, {==}, h)))))
    case False{} False{} True{}:
      Empty.absurd({W.W64.shl.pick(False{}, False{}, True{}, k, a) == W.W64.zero() : W.W64}, PS.ns.tf(Equal.trans(Bool, True{}, Nat.is_lt(k, 64n), False{}, Equal.sym(Bool, Nat.is_lt(k, 64n), True{}, e64), P.wn.le_not_lt(64n, k, h))))
    case False{} False{} False{}:
      {==}

def Laws.shl_big(a, k, h):
  wq.shlbig.go(Nat.is_eq(k, 0n), Nat.is_lt(k, 32n), Nat.is_lt(k, 64n), k, a, {==}, {==}, {==}, h)

def wq.shrbig.go(z: Bool, l32: Bool, l64: Bool, +k: Nat, -a: W.W64, ez: {Nat.is_eq(k, 0n) == z : Bool}, e32: {Nat.is_lt(k, 32n) == l32 : Bool}, e64: {Nat.is_lt(k, 64n) == l64 : Bool}, +h: {Nat.is_le(64n, k) == True{} : Bool}) -> {W.W64.shr.pick(z, l32, l64, k, a) == W.W64.zero() : W.W64}:
  match z l32 l64:
    case True{} _ _:
      Empty.absurd({a == W.W64.zero() : W.W64}, PS.ns.tf(Equal.trans(Bool, True{}, Nat.is_lt(k, 64n), False{}, Equal.sym(Bool, Nat.is_lt(k, 64n), Nat.is_lt(0n, 64n), Equal.cong(Nat, Bool, v => Nat.is_lt(v, 64n), k, 0n, PS.ns.eq_zero(k, ez))), P.wn.le_not_lt(64n, k, h))))
    case False{} True{} _:
      Empty.absurd({W.W64.shr.pick(False{}, True{}, l64, k, a) == W.W64.zero() : W.W64}, PS.ns.tf(Equal.trans(Bool, True{}, Nat.is_lt(k, 32n), False{}, Equal.sym(Bool, Nat.is_lt(k, 32n), True{}, e32), P.wn.le_not_lt(32n, k, P.wn.le_trans(32n, 64n, k, {==}, h)))))
    case False{} False{} True{}:
      Empty.absurd({W.W64.shr.pick(False{}, False{}, True{}, k, a) == W.W64.zero() : W.W64}, PS.ns.tf(Equal.trans(Bool, True{}, Nat.is_lt(k, 64n), False{}, Equal.sym(Bool, Nat.is_lt(k, 64n), True{}, e64), P.wn.le_not_lt(64n, k, h))))
    case False{} False{} False{}:
      {==}

def Laws.shr_big(a, k, h):
  wq.shrbig.go(Nat.is_eq(k, 0n), Nat.is_lt(k, 32n), Nat.is_lt(k, 64n), k, a, {==}, {==}, {==}, h)
