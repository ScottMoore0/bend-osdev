import Base
import ../u32/u32.bend as U
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ./word64.bend as W
import ./proof_value.bend as P
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
