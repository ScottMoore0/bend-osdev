# Proof helpers for bend-osdev-algo: U32 arithmetic as Nat arithmetic. The
# value (Word.to_nat) of a U32 subtraction, addition, increment and halving
# is the Nat difference, sum, successor and half, when nothing wraps, by
# induction over the bits of Base's Word(n). The Array binary search's index
# arithmetic (lo + (hi - lo) / 2, mid + 1) rests on these; PROOF.bend uses
# them through proof_bsearch.bend.
import Base

# 2^n
def uq.pw(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      Nat.double(uq.pw(p))

# n / 2, rounded down
def uq.half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+q:
          1n+uq.half(q)

# the value of a word's lowest bit and the rest
def uq.bv(b: Bool, x: Nat) -> Nat:
  match b:
    case False{}:
      Nat.double(x)
    case True{}:
      1n+Nat.double(x)

# Contradictions

def uq.bt(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def uq.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : uq.bt(_)
  Unit{}

def uq.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : uq.bt(_)
  Unit{}

# Nat

def uq.succ_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def uq.double_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {Nat.double(a) == Nat.double(b) : Nat}:
  %e : {Nat.double(a) == Nat.double(_) : Nat}
  {==}

def uq.add_zero(x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      uq.succ_cong(Nat.add(p, 0n), p, uq.add_zero(p))

def uq.add_succ(x: Nat, -y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      uq.succ_cong(Nat.add(p, 1n+y), 1n+Nat.add(p, y), uq.add_succ(p, y))

def uq.add_comm(x: Nat, +y: Nat) -> {Nat.add(x, y) == Nat.add(y, x) : Nat}:
  match x:
    case 0n:
      Equal.sym(Nat, Nat.add(y, 0n), y, uq.add_zero(y))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, y), 1n+Nat.add(y, p), Nat.add(y, 1n+p), uq.succ_cong(Nat.add(p, y), Nat.add(y, p), uq.add_comm(p, y)), Equal.sym(Nat, Nat.add(y, 1n+p), 1n+Nat.add(y, p), uq.add_succ(y, p)))

def uq.double_add(x: Nat, -y: Nat) -> {Nat.double(Nat.add(x, y)) == Nat.add(Nat.double(x), Nat.double(y)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      uq.succ_cong(1n+Nat.double(Nat.add(p, y)), 1n+Nat.add(Nat.double(p), Nat.double(y)), uq.succ_cong(Nat.double(Nat.add(p, y)), Nat.add(Nat.double(p), Nat.double(y)), uq.double_add(p, y)))

def uq.sub_add_l(y: Nat, +r: Nat) -> {Nat.sub(Nat.add(y, r), y) == r : Nat}:
  match y:
    case 0n:
      match r:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+q:
      uq.sub_add_l(q, r)

def uq.sub_add(+r: Nat, +y: Nat) -> {Nat.sub(Nat.add(r, y), y) == r : Nat}:
  %uq.add_comm(y, r) : {Nat.sub(_, y) == r : Nat}
  uq.sub_add_l(y, r)

def uq.le_succ(y: Nat, x: Nat) -> {Nat.is_le(1n+y, x) == Nat.is_lt(y, x) : Bool}:
  match y x:
    case 0n 0n:
      {==}
    case 0n 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+q 0n:
      {==}
    case 1n+q 1n+p:
      uq.le_succ(q, p)

def uq.lt_dbl(x: Nat, y: Nat) -> {Nat.is_lt(Nat.double(x), Nat.double(y)) == Nat.is_lt(x, y) : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      uq.lt_dbl(p, q)

def uq.lt_dbl1(x: Nat, y: Nat) -> {Nat.is_lt(1n+Nat.double(x), Nat.double(y)) == Nat.is_lt(x, y) : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      uq.lt_dbl1(p, q)

def uq.lt_rw(-x: Nat, -x2: Nat, -y: Nat, e: {x == x2 : Nat}, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x2, y) == True{} : Bool}:
  %e : {Nat.is_lt(_, y) == True{} : Bool}
  h

# Bounds: every word is below 2^n

def uq.val_lt(n: Nat, w: Word(n)) -> {Nat.is_lt(Word.to_nat(n, w), uq.pw(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{False{}, +t}:
          Equal.trans(Bool, Nat.is_lt(Nat.double(Word.to_nat(p, t)), Nat.double(uq.pw(p))), Nat.is_lt(Word.to_nat(p, t), uq.pw(p)), True{}, uq.lt_dbl(Word.to_nat(p, t), uq.pw(p)), uq.val_lt(p, t))
        case WCon{True{}, +t}:
          Equal.trans(Bool, Nat.is_lt(1n+Nat.double(Word.to_nat(p, t)), Nat.double(uq.pw(p))), Nat.is_lt(Word.to_nat(p, t), uq.pw(p)), True{}, uq.lt_dbl1(Word.to_nat(p, t), uq.pw(p)), uq.val_lt(p, t))

def uq.lt_succ_r(x: Nat, y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x, 1n+y) == True{} : Bool}:
  match x y:
    case 0n _:
      {==}
    case 1n+xp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 1n) == True{} : Bool}, uq.ft(h))
    case 1n+xp 1n+yp:
      uq.lt_succ_r(xp, yp, h)

def uq.le_lt_trans(x: Nat, y: Nat, z: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_lt(y, z) == True{} : Bool}) -> {Nat.is_lt(x, z) == True{} : Bool}:
  match x y z:
    case 0n 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, uq.ft(h2))
    case 0n 0n 1n+zp:
      {==}
    case 0n 1n+yp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, uq.ft(h2))
    case 0n 1n+yp 1n+zp:
      {==}
    case 1n+xp 0n _:
      Empty.absurd({Nat.is_lt(1n+xp, z) == True{} : Bool}, uq.ft(h1))
    case 1n+xp 1n+yp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 0n) == True{} : Bool}, uq.ft(h2))
    case 1n+xp 1n+yp 1n+zp:
      uq.le_lt_trans(xp, yp, zp, h1, h2)

def uq.lt_dbl_self(x: Nat, y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x, Nat.double(y)) == True{} : Bool}:
  match x y:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, uq.ft(h))
    case 0n 1n+yp:
      {==}
    case 1n+xp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 0n) == True{} : Bool}, uq.ft(h))
    case 1n+ +xp 1n+ +yp:
      uq.lt_succ_r(xp, Nat.double(yp), uq.lt_dbl_self(xp, yp, h))

# x < 2^f: x2 < 2^g, for x == x2 and g == 1 + f (stated so that a fixed g,
# such as the search's 33, is never expanded)
def uq.lt_succ_pw(+f: Nat, -g: Nat, eg: {1n+f == g : Nat}, +x: Nat, -x2: Nat, e: {x == x2 : Nat}, h: {Nat.is_lt(x, uq.pw(f)) == True{} : Bool}) -> {Nat.is_lt(x2, uq.pw(g)) == True{} : Bool}:
  %eg : {Nat.is_lt(x2, uq.pw(_)) == True{} : Bool}
  %e : {Nat.is_lt(_, uq.pw(1n+f)) == True{} : Bool}
  uq.lt_dbl_self(x, uq.pw(f), h)

# Comparing the values of words split at their lowest bit

def uq.nc(x: Nat, y: Nat, a: Bool, b: Bool) -> {Nat.cmp(uq.bv(a, x), uq.bv(b, y)) == Word.cmp.fin(a, b, Nat.cmp(x, y)) : Cmp}:
  match x y:
    case 0n 0n:
      match a b:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 0n 1n+q:
      match a b:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+p 0n:
      match a b:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+p 1n+q:
      match a b:
        case False{} False{}:
          uq.nc(p, q, False{}, False{})
        case False{} True{}:
          uq.nc(p, q, False{}, True{})
        case True{} False{}:
          uq.nc(p, q, True{}, False{})
        case True{} True{}:
          uq.nc(p, q, True{}, True{})

# Subtraction: Word.adc with a complemented second operand subtracts

def uq.cb(c: Bool) -> Nat:
  match c:
    case True{}:
      0n
    case False{}:
      1n

def uq.fin_le_ff(c: Cmp) -> {Cmp.is_le(Word.cmp.fin(False{}, False{}, c)) == Cmp.is_le(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def uq.fin_le_tf(c: Cmp) -> {Cmp.is_le(Word.cmp.fin(True{}, False{}, c)) == Cmp.is_lt(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def uq.fin_le_ft(c: Cmp) -> {Cmp.is_le(Word.cmp.fin(False{}, True{}, c)) == Cmp.is_le(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def uq.le_bits(+y: Nat, +x: Nat, +a: Bool, +b: Bool, h: {Nat.is_le(uq.bv(a, y), uq.bv(b, x)) == True{} : Bool}) -> {Cmp.is_le(Word.cmp.fin(a, b, Nat.cmp(y, x))) == True{} : Bool}:
  %uq.nc(y, x, a, b) : {Cmp.is_le(_) == True{} : Bool}
  h

def uq.ha(+y: Nat, +x: Nat, h: {Nat.is_le(uq.bv(False{}, y), uq.bv(False{}, x)) == True{} : Bool}) -> {Nat.is_le(y, x) == True{} : Bool}:
  %uq.fin_le_ff(Nat.cmp(y, x)) : {_ == True{} : Bool}
  uq.le_bits(y, x, False{}, False{}, h)

def uq.hb(+y: Nat, +x: Nat, h: {Nat.is_le(uq.bv(True{}, y), uq.bv(False{}, x)) == True{} : Bool}) -> {Nat.is_le(1n+y, x) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(1n+y, x), Nat.is_lt(y, x), uq.le_succ(y, x)) : {_ == True{} : Bool}
  %uq.fin_le_tf(Nat.cmp(y, x)) : {_ == True{} : Bool}
  uq.le_bits(y, x, True{}, False{}, h)

def uq.hc(+y: Nat, +x: Nat, h: {Nat.is_le(uq.bv(False{}, y), uq.bv(True{}, x)) == True{} : Bool}) -> {Nat.is_le(y, x) == True{} : Bool}:
  %uq.fin_le_ft(Nat.cmp(y, x)) : {_ == True{} : Bool}
  uq.le_bits(y, x, False{}, True{}, h)

def uq.alg2(+r: Nat, +y: Nat) -> {Nat.double(Nat.add(r, 1n+y)) == Nat.add(1n+Nat.double(r), 1n+Nat.double(y)) : Nat}:
  %Equal.sym(Nat, Nat.add(r, 1n+y), 1n+Nat.add(r, y), uq.add_succ(r, y)) : {Nat.double(_) == Nat.add(1n+Nat.double(r), 1n+Nat.double(y)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.double(r), 1n+Nat.double(y)), 1n+Nat.add(Nat.double(r), Nat.double(y)), uq.add_succ(Nat.double(r), Nat.double(y))) : {Nat.double(1n+Nat.add(r, y)) == 1n+_ : Nat}
  uq.succ_cong(1n+Nat.double(Nat.add(r, y)), 1n+Nat.add(Nat.double(r), Nat.double(y)), uq.succ_cong(Nat.double(Nat.add(r, y)), Nat.add(Nat.double(r), Nat.double(y)), uq.double_add(r, y)))

def uq.alg4(+r: Nat, +y: Nat) -> {Nat.double(Nat.add(r, 1n+y)) == Nat.add(Nat.double(r), 2n+Nat.double(y)) : Nat}:
  %Equal.sym(Nat, Nat.add(r, 1n+y), 1n+Nat.add(r, y), uq.add_succ(r, y)) : {Nat.double(_) == Nat.add(Nat.double(r), 2n+Nat.double(y)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.double(r), 2n+Nat.double(y)), 1n+Nat.add(Nat.double(r), 1n+Nat.double(y)), uq.add_succ(Nat.double(r), 1n+Nat.double(y))) : {Nat.double(1n+Nat.add(r, y)) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.double(r), 1n+Nat.double(y)), 1n+Nat.add(Nat.double(r), Nat.double(y)), uq.add_succ(Nat.double(r), Nat.double(y))) : {Nat.double(1n+Nat.add(r, y)) == 1n+_ : Nat}
  uq.succ_cong(1n+Nat.double(Nat.add(r, y)), 1n+Nat.add(Nat.double(r), Nat.double(y)), uq.succ_cong(Nat.double(Nat.add(r, y)), Nat.add(Nat.double(r), Nat.double(y)), uq.double_add(r, y)))

def uq.alg6(+r: Nat, +y: Nat) -> {1n+Nat.double(Nat.add(r, y)) == Nat.add(Nat.double(r), 1n+Nat.double(y)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.double(r), 1n+Nat.double(y)), 1n+Nat.add(Nat.double(r), Nat.double(y)), uq.add_succ(Nat.double(r), Nat.double(y))) : {1n+Nat.double(Nat.add(r, y)) == _ : Nat}
  uq.succ_cong(Nat.double(Nat.add(r, y)), Nat.add(Nat.double(r), Nat.double(y)), uq.double_add(r, y))

# for b <= a (b < a when the carry in c is False):
# a = adc(a, b, True, c) + (1 - c) + b
def uq.sub_w(n: Nat, a: Word(n), b: Word(n), c: Bool, h: {Nat.is_le(Nat.add(uq.cb(c), Word.to_nat(n, b)), Word.to_nat(n, a)) == True{} : Bool}) -> {Word.to_nat(n, a) == Nat.add(Word.to_nat(n, Word.adc(n, a, b, True{}, c)), Nat.add(uq.cb(c), Word.to_nat(n, b))) : Nat}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} True{}:
          {==}
        case WNil{} WNil{} False{}:
          Empty.absurd({0n == 1n : Nat}, uq.ft(h))
    case 1n+ +p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          +r = Word.to_nat(p, Word.adc(p, at, bt, True{}, True{}))
          %Equal.sym(Nat, xv, Nat.add(r, yv), uq.sub_w(p, at, bt, True{}, uq.ha(yv, xv, h))) : {Nat.double(_) == Nat.add(Nat.double(r), Nat.double(yv)) : Nat}
          uq.double_add(r, yv)
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          +r = Word.to_nat(p, Word.adc(p, at, bt, True{}, False{}))
          %Equal.sym(Nat, xv, Nat.add(r, 1n+yv), uq.sub_w(p, at, bt, False{}, uq.hb(yv, xv, h))) : {Nat.double(_) == Nat.add(1n+Nat.double(r), 1n+Nat.double(yv)) : Nat}
          uq.alg2(r, yv)
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          +r = Word.to_nat(p, Word.adc(p, at, bt, True{}, True{}))
          %Equal.sym(Nat, xv, Nat.add(r, yv), uq.sub_w(p, at, bt, True{}, uq.hc(yv, xv, h))) : {1n+Nat.double(_) == 1n+Nat.add(Nat.double(r), Nat.double(yv)) : Nat}
          uq.succ_cong(Nat.double(Nat.add(r, yv)), Nat.add(Nat.double(r), Nat.double(yv)), uq.double_add(r, yv))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          +r = Word.to_nat(p, Word.adc(p, at, bt, True{}, True{}))
          %Equal.sym(Nat, xv, Nat.add(r, yv), uq.sub_w(p, at, bt, True{}, uq.ha(yv, xv, h))) : {1n+Nat.double(_) == Nat.add(Nat.double(r), 1n+Nat.double(yv)) : Nat}
          uq.alg6(r, yv)
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          +r = Word.to_nat(p, Word.adc(p, at, bt, True{}, False{}))
          %Equal.sym(Nat, xv, Nat.add(r, 1n+yv), uq.sub_w(p, at, bt, False{}, uq.hb(yv, xv, h))) : {Nat.double(_) == Nat.add(1n+Nat.double(r), 1n+Nat.double(yv)) : Nat}
          uq.alg2(r, yv)
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          +r = Word.to_nat(p, Word.adc(p, at, bt, True{}, False{}))
          %Equal.sym(Nat, xv, Nat.add(r, 1n+yv), uq.sub_w(p, at, bt, False{}, uq.ha(1n+yv, xv, h))) : {Nat.double(_) == Nat.add(Nat.double(r), 2n+Nat.double(yv)) : Nat}
          uq.alg4(r, yv)
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          +r = Word.to_nat(p, Word.adc(p, at, bt, True{}, True{}))
          %Equal.sym(Nat, xv, Nat.add(r, yv), uq.sub_w(p, at, bt, True{}, uq.ha(yv, xv, h))) : {1n+Nat.double(_) == Nat.add(Nat.double(r), 1n+Nat.double(yv)) : Nat}
          uq.alg6(r, yv)
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          +r = Word.to_nat(p, Word.adc(p, at, bt, True{}, False{}))
          %Equal.sym(Nat, xv, Nat.add(r, 1n+yv), uq.sub_w(p, at, bt, False{}, uq.hb(yv, xv, h))) : {1n+Nat.double(_) == 1n+Nat.add(Nat.double(r), 2n+Nat.double(yv)) : Nat}
          uq.succ_cong(Nat.double(Nat.add(r, 1n+yv)), Nat.add(Nat.double(r), 2n+Nat.double(yv)), uq.alg4(r, yv))

def uq.u32_sub(a: U32, b: U32, h: {Nat.is_le(U32.to_nat(b), U32.to_nat(a)) == True{} : Bool}) -> {U32.to_nat(U32.sub(a, b)) == Nat.sub(U32.to_nat(a), U32.to_nat(b)) : Nat}:
  match a b:
    case U32{+x} U32{+y}:
      +xv = Word.to_nat(32n, x)
      +yv = Word.to_nat(32n, y)
      +r = Word.to_nat(32n, Word.adc(32n, x, y, True{}, True{}))
      %Equal.sym(Nat, xv, Nat.add(r, yv), uq.sub_w(32n, x, y, True{}, h)) : {r == Nat.sub(_, yv) : Nat}
      Equal.sym(Nat, Nat.sub(Nat.add(r, yv), yv), r, uq.sub_add(r, yv))

# Addition, when the sum is below 2^n

def uq.cv(c: Bool) -> Nat:
  match c:
    case True{}:
      1n
    case False{}:
      0n

# the bound for the bits above the lowest, from the bound for the word
def uq.hk0(+s2: Nat, -d: Nat, +q: Nat, e: {Nat.double(s2) == d : Nat}, h: {Nat.is_lt(d, Nat.double(q)) == True{} : Bool}) -> {Nat.is_lt(s2, q) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(s2, q), Nat.is_lt(Nat.double(s2), Nat.double(q)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.double(s2), Nat.double(q)), Nat.is_lt(s2, q), uq.lt_dbl(s2, q)), uq.lt_rw(d, Nat.double(s2), Nat.double(q), Equal.sym(Nat, Nat.double(s2), d, e), h))

def uq.hk1(+s2: Nat, -d: Nat, +q: Nat, e: {Nat.double(s2) == d : Nat}, h: {Nat.is_lt(1n+d, Nat.double(q)) == True{} : Bool}) -> {Nat.is_lt(s2, q) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(s2, q), Nat.is_lt(1n+Nat.double(s2), Nat.double(q)), True{}, Equal.sym(Bool, Nat.is_lt(1n+Nat.double(s2), Nat.double(q)), Nat.is_lt(s2, q), uq.lt_dbl1(s2, q)), uq.lt_rw(1n+d, 1n+Nat.double(s2), Nat.double(q), uq.succ_cong(d, Nat.double(s2), Equal.sym(Nat, Nat.double(s2), d, e)), h))

def uq.hk2(+s2: Nat, -d: Nat, +q: Nat, e: {Nat.double(s2) == d : Nat}, h: {Nat.is_lt(2n+d, Nat.double(q)) == True{} : Bool}) -> {Nat.is_lt(1n+s2, q) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(1n+s2, q), Nat.is_lt(Nat.double(1n+s2), Nat.double(q)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.double(1n+s2), Nat.double(q)), Nat.is_lt(1n+s2, q), uq.lt_dbl(1n+s2, q)), uq.lt_rw(2n+d, 2n+Nat.double(s2), Nat.double(q), uq.succ_cong(1n+d, 1n+Nat.double(s2), uq.succ_cong(d, Nat.double(s2), Equal.sym(Nat, Nat.double(s2), d, e))), h))

def uq.hk3(+s2: Nat, -d: Nat, +q: Nat, e: {Nat.double(s2) == d : Nat}, h: {Nat.is_lt(3n+d, Nat.double(q)) == True{} : Bool}) -> {Nat.is_lt(1n+s2, q) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(1n+s2, q), Nat.is_lt(1n+Nat.double(1n+s2), Nat.double(q)), True{}, Equal.sym(Bool, Nat.is_lt(1n+Nat.double(1n+s2), Nat.double(q)), Nat.is_lt(1n+s2, q), uq.lt_dbl1(1n+s2, q)), uq.lt_rw(3n+d, 3n+Nat.double(s2), Nat.double(q), uq.succ_cong(2n+d, 2n+Nat.double(s2), uq.succ_cong(1n+d, 1n+Nat.double(s2), uq.succ_cong(d, Nat.double(s2), Equal.sym(Nat, Nat.double(s2), d, e)))), h))

# c + a + b < 2^n: adc(a, b, False, c) is c + a + b
def uq.add_w(n: Nat, a: Word(n), b: Word(n), c: Bool, h: {Nat.is_lt(Nat.add(uq.cv(c), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))), uq.pw(n)) == True{} : Bool}) -> {Word.to_nat(n, Word.adc(n, a, b, False{}, c)) == Nat.add(uq.cv(c), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) : Nat}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} False{}:
          {==}
        case WNil{} WNil{} True{}:
          Empty.absurd({0n == 1n : Nat}, uq.ft(h))
    case 1n+ +p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          +xa = Word.to_nat(p, at)
          +xb = Word.to_nat(p, bt)
          +s2 = Nat.add(xa, xb)
          +dd = Nat.add(Nat.double(xa), Nat.double(xb))
          +ih = uq.add_w(p, at, bt, False{}, uq.hk0(s2, dd, uq.pw(p), uq.double_add(xa, xb), h))
          Equal.trans(Nat, Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), Nat.double(s2), dd, uq.double_cong(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), s2, ih), uq.double_add(xa, xb))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          +xa = Word.to_nat(p, at)
          +xb = Word.to_nat(p, bt)
          +s2 = Nat.add(xa, xb)
          +dd = Nat.add(Nat.double(xa), Nat.double(xb))
          +ih = uq.add_w(p, at, bt, False{}, uq.hk1(s2, dd, uq.pw(p), uq.double_add(xa, xb), h))
          uq.succ_cong(Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), dd, Equal.trans(Nat, Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), Nat.double(s2), dd, uq.double_cong(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), s2, ih), uq.double_add(xa, xb)))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          +xa = Word.to_nat(p, at)
          +xb = Word.to_nat(p, bt)
          +s2 = Nat.add(xa, xb)
          +dd = Nat.add(Nat.double(xa), Nat.double(xb))
          +es = uq.add_succ(Nat.double(xa), Nat.double(xb))
          +ih = uq.add_w(p, at, bt, False{}, uq.hk1(s2, dd, uq.pw(p), uq.double_add(xa, xb), uq.lt_rw(Nat.add(Nat.double(xa), 1n+Nat.double(xb)), 1n+dd, Nat.double(uq.pw(p)), es, h)))
          Equal.trans(Nat, 1n+Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), 1n+dd, Nat.add(Nat.double(xa), 1n+Nat.double(xb)), uq.succ_cong(Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), dd, Equal.trans(Nat, Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), Nat.double(s2), dd, uq.double_cong(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), s2, ih), uq.double_add(xa, xb))), Equal.sym(Nat, Nat.add(Nat.double(xa), 1n+Nat.double(xb)), 1n+dd, es))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          +xa = Word.to_nat(p, at)
          +xb = Word.to_nat(p, bt)
          +s2 = Nat.add(xa, xb)
          +dd = Nat.add(Nat.double(xa), Nat.double(xb))
          +es = uq.add_succ(Nat.double(xa), Nat.double(xb))
          +ih = uq.add_w(p, at, bt, True{}, uq.hk2(s2, dd, uq.pw(p), uq.double_add(xa, xb), uq.lt_rw(1n+Nat.add(Nat.double(xa), 1n+Nat.double(xb)), 2n+dd, Nat.double(uq.pw(p)), uq.succ_cong(Nat.add(Nat.double(xa), 1n+Nat.double(xb)), 1n+dd, es), h)))
          +r = Word.to_nat(p, Word.adc(p, at, bt, False{}, True{}))
          Equal.trans(Nat, Nat.double(r), 2n+dd, 1n+Nat.add(Nat.double(xa), 1n+Nat.double(xb)), Equal.trans(Nat, Nat.double(r), 2n+Nat.double(s2), 2n+dd, uq.double_cong(r, 1n+s2, ih), uq.succ_cong(1n+Nat.double(s2), 1n+dd, uq.succ_cong(Nat.double(s2), dd, uq.double_add(xa, xb)))), uq.succ_cong(1n+dd, Nat.add(Nat.double(xa), 1n+Nat.double(xb)), Equal.sym(Nat, Nat.add(Nat.double(xa), 1n+Nat.double(xb)), 1n+dd, es)))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          +xa = Word.to_nat(p, at)
          +xb = Word.to_nat(p, bt)
          +s2 = Nat.add(xa, xb)
          +dd = Nat.add(Nat.double(xa), Nat.double(xb))
          +ih = uq.add_w(p, at, bt, False{}, uq.hk1(s2, dd, uq.pw(p), uq.double_add(xa, xb), h))
          uq.succ_cong(Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), dd, Equal.trans(Nat, Nat.double(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{}))), Nat.double(s2), dd, uq.double_cong(Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), s2, ih), uq.double_add(xa, xb)))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          +xa = Word.to_nat(p, at)
          +xb = Word.to_nat(p, bt)
          +s2 = Nat.add(xa, xb)
          +dd = Nat.add(Nat.double(xa), Nat.double(xb))
          +ih = uq.add_w(p, at, bt, True{}, uq.hk2(s2, dd, uq.pw(p), uq.double_add(xa, xb), h))
          +r = Word.to_nat(p, Word.adc(p, at, bt, False{}, True{}))
          Equal.trans(Nat, Nat.double(r), 2n+Nat.double(s2), 2n+dd, uq.double_cong(r, 1n+s2, ih), uq.succ_cong(1n+Nat.double(s2), 1n+dd, uq.succ_cong(Nat.double(s2), dd, uq.double_add(xa, xb))))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          +xa = Word.to_nat(p, at)
          +xb = Word.to_nat(p, bt)
          +s2 = Nat.add(xa, xb)
          +dd = Nat.add(Nat.double(xa), Nat.double(xb))
          +es = uq.add_succ(Nat.double(xa), Nat.double(xb))
          +ih = uq.add_w(p, at, bt, True{}, uq.hk2(s2, dd, uq.pw(p), uq.double_add(xa, xb), uq.lt_rw(1n+Nat.add(Nat.double(xa), 1n+Nat.double(xb)), 2n+dd, Nat.double(uq.pw(p)), uq.succ_cong(Nat.add(Nat.double(xa), 1n+Nat.double(xb)), 1n+dd, es), h)))
          +r = Word.to_nat(p, Word.adc(p, at, bt, False{}, True{}))
          Equal.trans(Nat, Nat.double(r), 2n+dd, 1n+Nat.add(Nat.double(xa), 1n+Nat.double(xb)), Equal.trans(Nat, Nat.double(r), 2n+Nat.double(s2), 2n+dd, uq.double_cong(r, 1n+s2, ih), uq.succ_cong(1n+Nat.double(s2), 1n+dd, uq.succ_cong(Nat.double(s2), dd, uq.double_add(xa, xb)))), uq.succ_cong(1n+dd, Nat.add(Nat.double(xa), 1n+Nat.double(xb)), Equal.sym(Nat, Nat.add(Nat.double(xa), 1n+Nat.double(xb)), 1n+dd, es)))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          +xa = Word.to_nat(p, at)
          +xb = Word.to_nat(p, bt)
          +s2 = Nat.add(xa, xb)
          +dd = Nat.add(Nat.double(xa), Nat.double(xb))
          +es = uq.add_succ(Nat.double(xa), Nat.double(xb))
          +ih = uq.add_w(p, at, bt, True{}, uq.hk3(s2, dd, uq.pw(p), uq.double_add(xa, xb), uq.lt_rw(2n+Nat.add(Nat.double(xa), 1n+Nat.double(xb)), 3n+dd, Nat.double(uq.pw(p)), uq.succ_cong(1n+Nat.add(Nat.double(xa), 1n+Nat.double(xb)), 2n+dd, uq.succ_cong(Nat.add(Nat.double(xa), 1n+Nat.double(xb)), 1n+dd, es)), h)))
          +r = Word.to_nat(p, Word.adc(p, at, bt, False{}, True{}))
          Equal.trans(Nat, 1n+Nat.double(r), 3n+dd, 2n+Nat.add(Nat.double(xa), 1n+Nat.double(xb)), uq.succ_cong(Nat.double(r), 2n+dd, Equal.trans(Nat, Nat.double(r), 2n+Nat.double(s2), 2n+dd, uq.double_cong(r, 1n+s2, ih), uq.succ_cong(1n+Nat.double(s2), 1n+dd, uq.succ_cong(Nat.double(s2), dd, uq.double_add(xa, xb))))), uq.succ_cong(2n+dd, 1n+Nat.add(Nat.double(xa), 1n+Nat.double(xb)), uq.succ_cong(1n+dd, Nat.add(Nat.double(xa), 1n+Nat.double(xb)), Equal.sym(Nat, Nat.add(Nat.double(xa), 1n+Nat.double(xb)), 1n+dd, es))))

# the bound given by a word's value, so that 2^n is never expanded
def uq.add_wz(+n: Nat, +a: Word(n), +b: Word(n), +c: Bool, +z: Word(n), h: {Nat.is_le(Nat.add(uq.cv(c), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))), Word.to_nat(n, z)) == True{} : Bool}) -> {Word.to_nat(n, Word.adc(n, a, b, False{}, c)) == Nat.add(uq.cv(c), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) : Nat}:
  uq.add_w(n, a, b, c, uq.le_lt_trans(Nat.add(uq.cv(c), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))), Word.to_nat(n, z), uq.pw(n), h, uq.val_lt(n, z)))

# a + b <= c: U32.add(a, b) is a + b
def uq.u32_add(a: U32, b: U32, c: U32, h: {Nat.is_le(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c)) == True{} : Bool}) -> {U32.to_nat(U32.add(a, b)) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}:
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      uq.add_wz(32n, x, y, False{}, z, h)

# Increment, when 1 + w is below 2^n

def uq.inc_w(n: Nat, w: Word(n), h: {Nat.is_lt(1n+Word.to_nat(n, w), uq.pw(n)) == True{} : Bool}) -> {Word.to_nat(n, Word.inc(n, w)) == 1n+Word.to_nat(n, w) : Nat}:
  match n:
    case 0n:
      Empty.absurd({Word.to_nat(0n, Word.inc(0n, w)) == 1n+Word.to_nat(0n, w) : Nat}, uq.ft(h))
    case 1n+ +p:
      match w:
        case WCon{False{}, t}:
          {==}
        case WCon{True{}, +t}:
          +x = Word.to_nat(p, t)
          uq.double_cong(Word.to_nat(p, Word.inc(p, t)), 1n+x, uq.inc_w(p, t, Equal.trans(Bool, Nat.is_lt(1n+x, uq.pw(p)), Nat.is_lt(Nat.double(1n+x), Nat.double(uq.pw(p))), True{}, Equal.sym(Bool, Nat.is_lt(Nat.double(1n+x), Nat.double(uq.pw(p))), Nat.is_lt(1n+x, uq.pw(p)), uq.lt_dbl(1n+x, uq.pw(p))), h)))

def uq.inc_wz(+n: Nat, +w: Word(n), +z: Word(n), h: {Nat.is_le(1n+Word.to_nat(n, w), Word.to_nat(n, z)) == True{} : Bool}) -> {Word.to_nat(n, Word.inc(n, w)) == 1n+Word.to_nat(n, w) : Nat}:
  uq.inc_w(n, w, uq.le_lt_trans(1n+Word.to_nat(n, w), Word.to_nat(n, z), uq.pw(n), h, uq.val_lt(n, z)))

# 1 + a <= c: U32.inc(a) is 1 + a
def uq.u32_inc(a: U32, c: U32, h: {Nat.is_le(1n+U32.to_nat(a), U32.to_nat(c)) == True{} : Bool}) -> {U32.to_nat(U32.inc(a)) == 1n+U32.to_nat(a) : Nat}:
  match a c:
    case U32{+w} U32{+z}:
      uq.inc_wz(32n, w, z, h)

# Halving: a shift right by one bit

def uq.half_dbl(x: Nat) -> {uq.half(Nat.double(x)) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      uq.succ_cong(uq.half(Nat.double(p)), p, uq.half_dbl(p))

def uq.half_dbl1(x: Nat) -> {uq.half(1n+Nat.double(x)) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      uq.succ_cong(uq.half(1n+Nat.double(p)), p, uq.half_dbl1(p))

# padding a word with a zero top bit keeps its value
def uq.pad(p: Nat, t: Word(p)) -> {Word.to_nat(1n+p, Word.shr.pad(p, t)) == Word.to_nat(p, t) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+ +q:
      match t:
        case WCon{False{}, +r}:
          uq.double_cong(Word.to_nat(1n+q, Word.shr.pad(q, r)), Word.to_nat(q, r), uq.pad(q, r))
        case WCon{True{}, +r}:
          uq.succ_cong(Nat.double(Word.to_nat(1n+q, Word.shr.pad(q, r))), Nat.double(Word.to_nat(q, r)), uq.double_cong(Word.to_nat(1n+q, Word.shr.pad(q, r)), Word.to_nat(q, r), uq.pad(q, r)))

def uq.shr_w(n: Nat, w: Word(n)) -> {Word.to_nat(n, Word.shr(n, w)) == uq.half(Word.to_nat(n, w)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{False{}, +t}:
          Equal.trans(Nat, Word.to_nat(1n+p, Word.shr.pad(p, t)), Word.to_nat(p, t), uq.half(Nat.double(Word.to_nat(p, t))), uq.pad(p, t), Equal.sym(Nat, uq.half(Nat.double(Word.to_nat(p, t))), Word.to_nat(p, t), uq.half_dbl(Word.to_nat(p, t))))
        case WCon{True{}, +t}:
          Equal.trans(Nat, Word.to_nat(1n+p, Word.shr.pad(p, t)), Word.to_nat(p, t), uq.half(1n+Nat.double(Word.to_nat(p, t))), uq.pad(p, t), Equal.sym(Nat, uq.half(1n+Nat.double(Word.to_nat(p, t))), Word.to_nat(p, t), uq.half_dbl1(Word.to_nat(p, t))))

def uq.u32_shr(a: U32) -> {U32.to_nat(U32.shr(a)) == uq.half(U32.to_nat(a)) : Nat}:
  match a:
    case U32{w}:
      uq.shr_w(32n, w)
