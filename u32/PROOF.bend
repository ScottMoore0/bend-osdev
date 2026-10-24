# Proofs of bend-osdev-u32's laws: by induction over the bits of Base's
# Word(n), for every width n. The lemmas generalise those bend-osdev-algo
# (proof_u32.bend) and bend-osdev-array (PROOF.bend) proved for their own
# use. Every bound is a word's value or U32Nat.dbl(n, 1n) for a width n
# that is a variable, so no closed power of two is ever computed.
import Base
import ./u32.bend as U
import ./LAWS.bend as Laws

# Contradictions

def un.bt(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def un.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : un.bt(_)
  Unit{}

def un.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : un.bt(_)
  Unit{}

def un.cbt(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Unit
    case o:
      Empty

def un.lt_eq(e: {LT{} == EQ{} : Cmp}) -> Empty:
  %Equal.sym(Cmp, LT{}, EQ{}, e) : un.cbt(_)
  Unit{}

def un.gt_eq(e: {GT{} == EQ{} : Cmp}) -> Empty:
  %Equal.sym(Cmp, GT{}, EQ{}, e) : un.cbt(_)
  Unit{}

# Nat

def un.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def un.succ_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def un.succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, z => un.pred(z), 1n+a, 1n+b, e)

def un.double_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {Nat.double(a) == Nat.double(b) : Nat}:
  %e : {Nat.double(a) == Nat.double(_) : Nat}
  {==}

def un.add_zero(x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      un.succ_cong(Nat.add(p, 0n), p, un.add_zero(p))

def un.add_succ(x: Nat, -y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      un.succ_cong(Nat.add(p, 1n+y), 1n+Nat.add(p, y), un.add_succ(p, y))

def un.add_comm(x: Nat, +y: Nat) -> {Nat.add(x, y) == Nat.add(y, x) : Nat}:
  match x:
    case 0n:
      Equal.sym(Nat, Nat.add(y, 0n), y, un.add_zero(y))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, y), 1n+Nat.add(y, p), Nat.add(y, 1n+p), un.succ_cong(Nat.add(p, y), Nat.add(y, p), un.add_comm(p, y)), Equal.sym(Nat, Nat.add(y, 1n+p), 1n+Nat.add(y, p), un.add_succ(y, p)))

def un.double_add(x: Nat, -y: Nat) -> {Nat.double(Nat.add(x, y)) == Nat.add(Nat.double(x), Nat.double(y)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      un.succ_cong(1n+Nat.double(Nat.add(p, y)), 1n+Nat.add(Nat.double(p), Nat.double(y)), un.succ_cong(Nat.double(Nat.add(p, y)), Nat.add(Nat.double(p), Nat.double(y)), un.double_add(p, y)))

def un.sub_add_l(y: Nat, +r: Nat) -> {Nat.sub(Nat.add(y, r), y) == r : Nat}:
  match y:
    case 0n:
      match r:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+q:
      un.sub_add_l(q, r)

def un.sub_add(+r: Nat, +y: Nat) -> {Nat.sub(Nat.add(r, y), y) == r : Nat}:
  %un.add_comm(y, r) : {Nat.sub(_, y) == r : Nat}
  un.sub_add_l(y, r)

# x + k = y + k: x = y
def un.add_cancel_r(+x: Nat, +y: Nat, k: Nat, e: {Nat.add(x, k) == Nat.add(y, k) : Nat}) -> {x == y : Nat}:
  match k:
    case 0n:
      Equal.trans(Nat, x, Nat.add(x, 0n), y, Equal.sym(Nat, Nat.add(x, 0n), x, un.add_zero(x)), Equal.trans(Nat, Nat.add(x, 0n), Nat.add(y, 0n), y, e, un.add_zero(y)))
    case 1n+q:
      un.add_cancel_r(x, y, q, un.succ_inj(Nat.add(x, q), Nat.add(y, q), Equal.trans(Nat, 1n+Nat.add(x, q), Nat.add(x, 1n+q), 1n+Nat.add(y, q), Equal.sym(Nat, Nat.add(x, 1n+q), 1n+Nat.add(x, q), un.add_succ(x, q)), Equal.trans(Nat, Nat.add(x, 1n+q), Nat.add(y, 1n+q), 1n+Nat.add(y, q), e, un.add_succ(y, q)))))

# Order

def un.lt_rw(-x: Nat, -x2: Nat, -y: Nat, e: {x == x2 : Nat}, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x2, y) == True{} : Bool}:
  %e : {Nat.is_lt(_, y) == True{} : Bool}
  h

def un.lt_rw2(-x: Nat, -y: Nat, -y2: Nat, e: {y == y2 : Nat}, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x, y2) == True{} : Bool}:
  %e : {Nat.is_lt(x, _) == True{} : Bool}
  h

def un.le_succ(y: Nat, x: Nat) -> {Nat.is_le(1n+y, x) == Nat.is_lt(y, x) : Bool}:
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
      un.le_succ(q, p)

def un.lt_dbl(x: Nat, y: Nat) -> {Nat.is_lt(Nat.double(x), Nat.double(y)) == Nat.is_lt(x, y) : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      un.lt_dbl(p, q)

def un.lt_dbl1(x: Nat, y: Nat) -> {Nat.is_lt(1n+Nat.double(x), Nat.double(y)) == Nat.is_lt(x, y) : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      un.lt_dbl1(p, q)

def un.le_dbl(x: Nat, y: Nat) -> {Nat.is_le(Nat.double(x), Nat.double(y)) == Nat.is_le(x, y) : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      un.le_dbl(p, q)

def un.lt_succ_r(x: Nat, y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x, 1n+y) == True{} : Bool}:
  match x y:
    case 0n _:
      {==}
    case 1n+xp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 1n) == True{} : Bool}, un.ft(h))
    case 1n+xp 1n+yp:
      un.lt_succ_r(xp, yp, h)

def un.le_lt_trans(x: Nat, y: Nat, z: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_lt(y, z) == True{} : Bool}) -> {Nat.is_lt(x, z) == True{} : Bool}:
  match x y z:
    case 0n 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, un.ft(h2))
    case 0n 0n 1n+zp:
      {==}
    case 0n 1n+yp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, un.ft(h2))
    case 0n 1n+yp 1n+zp:
      {==}
    case 1n+xp 0n _:
      Empty.absurd({Nat.is_lt(1n+xp, z) == True{} : Bool}, un.ft(h1))
    case 1n+xp 1n+yp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 0n) == True{} : Bool}, un.ft(h2))
    case 1n+xp 1n+yp 1n+zp:
      un.le_lt_trans(xp, yp, zp, h1, h2)

def un.le_trans(x: Nat, y: Nat, z: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_le(y, z) == True{} : Bool}) -> {Nat.is_le(x, z) == True{} : Bool}:
  match x y z:
    case 0n _ _:
      match z:
        case 0n:
          {==}
        case 1n+zp:
          {==}
    case 1n+xp 0n _:
      Empty.absurd({Nat.is_le(1n+xp, z) == True{} : Bool}, un.ft(h1))
    case 1n+xp 1n+yp 0n:
      Empty.absurd({Nat.is_le(1n+xp, 0n) == True{} : Bool}, un.ft(h2))
    case 1n+xp 1n+yp 1n+zp:
      un.le_trans(xp, yp, zp, h1, h2)

def un.le_succ_self(x: Nat) -> {Nat.is_le(x, 1n+x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      un.le_succ_self(p)

def un.le_double(x: Nat) -> {Nat.is_le(x, Nat.double(x)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      un.le_trans(p, Nat.double(p), 1n+Nat.double(p), un.le_double(p), un.le_succ_self(Nat.double(p)))


# A + X < A + Y exactly when X < Y, on either side
def un.lt_add_l(a: Nat, -x: Nat, -y: Nat) -> {Nat.is_lt(Nat.add(a, x), Nat.add(a, y)) == Nat.is_lt(x, y) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      un.lt_add_l(p, x, y)

def un.lt_add_r(+x: Nat, +y: Nat, +a: Nat) -> {Nat.is_lt(Nat.add(x, a), Nat.add(y, a)) == Nat.is_lt(x, y) : Bool}:
  %un.add_comm(a, x) : {Nat.is_lt(_, Nat.add(y, a)) == Nat.is_lt(x, y) : Bool}
  %un.add_comm(a, y) : {Nat.is_lt(Nat.add(a, x), _) == Nat.is_lt(x, y) : Bool}
  un.lt_add_l(a, x, y)

# A + B < A never holds
def un.not_lt_add(a: Nat, b: Nat) -> {Nat.is_lt(Nat.add(a, b), a) == False{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      un.not_lt_add(p, b)

def un.not_lt_add_l(+s: Nat, +b: Nat) -> {Nat.is_lt(Nat.add(s, b), b) == False{} : Bool}:
  %un.add_comm(b, s) : {Nat.is_lt(_, b) == False{} : Bool}
  un.not_lt_add(b, s)

# x + k < k never holds
def un.add_lt_absurd(+s: Nat, +k: Nat, h: {Nat.is_lt(Nat.add(s, k), k) == True{} : Bool}) -> Empty:
  un.ft(Equal.trans(Bool, False{}, Nat.is_lt(Nat.add(s, k), k), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(s, k), k), False{}, un.not_lt_add_l(s, k)), h))

def un.le_not_lt(b: Nat, a: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.is_lt(a, b) == False{} : Bool}:
  match b a:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(0n, 1n+p) == False{} : Bool}, un.ft(h))
    case 1n+p 1n+q:
      un.le_not_lt(p, q, h)

def un.cmp_refl(a: Nat) -> {Nat.cmp(a, a) == EQ{} : Cmp}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      un.cmp_refl(p)

# The Nat functions: x * 2^n, 0 or 1, halving

def Laws.dbl_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      un.double_cong(U.U32Nat.dbl(p, 0n), 0n, Laws.dbl_zero(p))

def Laws.dbl_add(n, x, y):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, Nat.double(U.U32Nat.dbl(p, Nat.add(x, y))), Nat.double(Nat.add(U.U32Nat.dbl(p, x), U.U32Nat.dbl(p, y))), Nat.add(Nat.double(U.U32Nat.dbl(p, x)), Nat.double(U.U32Nat.dbl(p, y))), un.double_cong(U.U32Nat.dbl(p, Nat.add(x, y)), Nat.add(U.U32Nat.dbl(p, x), U.U32Nat.dbl(p, y)), Laws.dbl_add(p, x, y)), un.double_add(U.U32Nat.dbl(p, x), U.U32Nat.dbl(p, y)))

def Laws.dbl_dbl(m, k, x):
  match m:
    case 0n:
      {==}
    case 1n+p:
      un.double_cong(U.U32Nat.dbl(p, U.U32Nat.dbl(k, x)), U.U32Nat.dbl(Nat.add(p, k), x), Laws.dbl_dbl(p, k, x))

def Laws.dbl_lt(n, x, y):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Bool, Nat.is_lt(Nat.double(U.U32Nat.dbl(p, x)), Nat.double(U.U32Nat.dbl(p, y))), Nat.is_lt(U.U32Nat.dbl(p, x), U.U32Nat.dbl(p, y)), Nat.is_lt(x, y), un.lt_dbl(U.U32Nat.dbl(p, x), U.U32Nat.dbl(p, y)), Laws.dbl_lt(p, x, y))

def Laws.dbl_le(n, x, y):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Bool, Nat.is_le(Nat.double(U.U32Nat.dbl(p, x)), Nat.double(U.U32Nat.dbl(p, y))), Nat.is_le(U.U32Nat.dbl(p, x), U.U32Nat.dbl(p, y)), Nat.is_le(x, y), un.le_dbl(U.U32Nat.dbl(p, x), U.U32Nat.dbl(p, y)), Laws.dbl_le(p, x, y))

def Laws.half_double(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      un.succ_cong(U.U32Nat.half(Nat.double(p)), p, Laws.half_double(p))

def Laws.half_double_one(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      un.succ_cong(U.U32Nat.half(1n+Nat.double(p)), p, Laws.half_double_one(p))

# Words: the value of the lowest bit and the rest

def un.bv(b: Bool, x: Nat) -> Nat:
  match b:
    case False{}:
      Nat.double(x)
    case True{}:
      1n+Nat.double(x)

def un.vc(-p: Nat, b: Bool, -t: Word(p)) -> {un.bv(b, Word.to_nat(p, t)) == Word.to_nat(1n+p, WCon{b, t}) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def Laws.word_zero_value(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      un.double_cong(Word.to_nat(p, Word.zero(p)), 0n, Laws.word_zero_value(p))

# Bounds: every word is below 2^n

def Laws.word_value_lt(n, w):
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{False{}, +t}:
          Equal.trans(Bool, Nat.is_lt(Nat.double(Word.to_nat(p, t)), Nat.double(U.U32Nat.dbl(p, 1n))), Nat.is_lt(Word.to_nat(p, t), U.U32Nat.dbl(p, 1n)), True{}, un.lt_dbl(Word.to_nat(p, t), U.U32Nat.dbl(p, 1n)), Laws.word_value_lt(p, t))
        case WCon{True{}, +t}:
          Equal.trans(Bool, Nat.is_lt(1n+Nat.double(Word.to_nat(p, t)), Nat.double(U.U32Nat.dbl(p, 1n))), Nat.is_lt(Word.to_nat(p, t), U.U32Nat.dbl(p, 1n)), True{}, un.lt_dbl1(Word.to_nat(p, t), U.U32Nat.dbl(p, 1n)), Laws.word_value_lt(p, t))

# Comparison: Word.cmp is the order of the values

def un.nc(x: Nat, y: Nat, a: Bool, b: Bool) -> {Nat.cmp(un.bv(a, x), un.bv(b, y)) == Word.cmp.fin(a, b, Nat.cmp(x, y)) : Cmp}:
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
          un.nc(p, q, False{}, False{})
        case False{} True{}:
          un.nc(p, q, False{}, True{})
        case True{} False{}:
          un.nc(p, q, True{}, False{})
        case True{} True{}:
          un.nc(p, q, True{}, True{})

def Laws.word_cmp_value(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          %Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(xv, yv), Laws.word_cmp_value(p, at, bt)) : {Word.cmp.fin(x, y, _) == Nat.cmp(Word.to_nat(1n+p, WCon{x, at}), Word.to_nat(1n+p, WCon{y, bt})) : Cmp}
          %un.vc(p, x, at) : {Word.cmp.fin(x, y, Nat.cmp(xv, yv)) == Nat.cmp(_, Word.to_nat(1n+p, WCon{y, bt})) : Cmp}
          %un.vc(p, y, bt) : {Word.cmp.fin(x, y, Nat.cmp(xv, yv)) == Nat.cmp(un.bv(x, xv), _) : Cmp}
          Equal.sym(Cmp, Nat.cmp(un.bv(x, xv), un.bv(y, yv)), Word.cmp.fin(x, y, Nat.cmp(xv, yv)), un.nc(xv, yv, x, y))

# Equal values: equal words (Word.cmp answers EQ only for equal words)

def un.fin_eq_tail(c: Cmp, -x: Bool, -y: Bool, e: {Word.cmp.fin(x, y, c) == EQ{} : Cmp}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, un.lt_eq(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, un.gt_eq(e))

def un.bool_eq(x: Bool, y: Bool, e: {Bool.cmp(x, y) == EQ{} : Cmp}) -> {x == y : Bool}:
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, un.lt_eq(e))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, un.gt_eq(e))
    case True{} True{}:
      {==}

def un.fin_eq_head(c: Cmp, x: Bool, y: Bool, e: {Word.cmp.fin(x, y, c) == EQ{} : Cmp}) -> {x == y : Bool}:
  match c:
    case LT{}:
      Empty.absurd({x == y : Bool}, un.lt_eq(e))
    case EQ{}:
      un.bool_eq(x, y, e)
    case GT{}:
      Empty.absurd({x == y : Bool}, un.gt_eq(e))

def un.wcon_eq(-p: Nat, -x: Bool, -y: Bool, -s: Word(p), -t: Word(p), e1: {x == y : Bool}, e2: {s == t : Word(p)}) -> {WCon{x, s} == WCon{y, t} : Word(1n+p)}:
  %e1 : {WCon{x, s} == WCon{_, t} : Word(1n+p)}
  %e2 : {WCon{x, s} == WCon{x, _} : Word(1n+p)}
  {==}

def un.word_eq(n: Nat, a: Word(n), b: Word(n), +e: {Word.cmp(n, a, b) == EQ{} : Cmp}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          un.wcon_eq(p, x, y, at, bt, un.fin_eq_head(Word.cmp(p, at, bt), x, y, e), un.word_eq(p, at, bt, un.fin_eq_tail(Word.cmp(p, at, bt), x, y, e)))

def Laws.word_value_eq(n, a, b, e):
  un.word_eq(n, a, b, Equal.trans(Cmp, Word.cmp(n, a, b), Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)), EQ{}, Laws.word_cmp_value(n, a, b), Equal.trans(Cmp, Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)), Nat.cmp(Word.to_nat(n, b), Word.to_nat(n, b)), EQ{}, Equal.cong(Nat, Cmp, v => Nat.cmp(v, Word.to_nat(n, b)), Word.to_nat(n, a), Word.to_nat(n, b), e), un.cmp_refl(Word.to_nat(n, b)))))

# The complement: not(w) + w = 2^n - 1

# 2 + (2N + 2T) = 2 * K, from 1 + (N + T) = K
def un.not_tail(+nv: Nat, +tv: Nat, -k: Nat, ih: {1n+Nat.add(nv, tv) == k : Nat}) -> {2n+Nat.add(Nat.double(nv), Nat.double(tv)) == Nat.double(k) : Nat}:
  Equal.trans(Nat, 2n+Nat.add(Nat.double(nv), Nat.double(tv)), Nat.double(1n+Nat.add(nv, tv)), Nat.double(k), un.succ_cong(1n+Nat.add(Nat.double(nv), Nat.double(tv)), 1n+Nat.double(Nat.add(nv, tv)), un.succ_cong(Nat.add(Nat.double(nv), Nat.double(tv)), Nat.double(Nat.add(nv, tv)), Equal.sym(Nat, Nat.double(Nat.add(nv, tv)), Nat.add(Nat.double(nv), Nat.double(tv)), un.double_add(nv, tv)))), un.double_cong(1n+Nat.add(nv, tv), k, ih))

def Laws.word_not_value(n, w):
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{False{}, +t}:
          un.not_tail(Word.to_nat(p, Word.not(p, t)), Word.to_nat(p, t), U.U32Nat.dbl(p, 1n), Laws.word_not_value(p, t))
        case WCon{True{}, +t}:
          +nv = Word.to_nat(p, Word.not(p, t))
          +tv = Word.to_nat(p, t)
          Equal.trans(Nat, 1n+Nat.add(Nat.double(nv), 1n+Nat.double(tv)), 2n+Nat.add(Nat.double(nv), Nat.double(tv)), Nat.double(U.U32Nat.dbl(p, 1n)), un.succ_cong(Nat.add(Nat.double(nv), 1n+Nat.double(tv)), 1n+Nat.add(Nat.double(nv), Nat.double(tv)), un.add_succ(Nat.double(nv), Nat.double(tv))), un.not_tail(nv, tv, U.U32Nat.dbl(p, 1n), Laws.word_not_value(p, t)))

# Addition with a carry in: the value of Word.adc

# the carry out of Word.adc(n, a, b, False, c)
def un.maj(x: Bool, y: Bool, c: Bool) -> Bool:
  match x:
    case False{}:
      Bool.and(y, c)
    case True{}:
      Bool.or(y, c)

def un.sum(x: Bool, y: Bool, c: Bool) -> Bool:
  match x:
    case False{}:
      Bool.xor(y, c)
    case True{}:
      Bool.not(Bool.xor(y, c))

def un.co(n: Nat, a: Word(n), b: Word(n), c: Bool) -> Bool:
  match n:
    case 0n:
      c
    case 1n+p:
      match a b:
        case WCon{x, at} WCon{y, bt}:
          un.co(p, at, bt, un.maj(x, y, c))

# double R + double D, from R + D
def un.dd(+r: Nat, +d: Nat, +a: Nat, +b: Nat, e: {Nat.add(r, d) == Nat.add(a, b) : Nat}) -> {Nat.add(Nat.double(r), Nat.double(d)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.double(r), Nat.double(d)), Nat.double(Nat.add(r, d)), Nat.add(Nat.double(a), Nat.double(b)), Equal.sym(Nat, Nat.double(Nat.add(r, d)), Nat.add(Nat.double(r), Nat.double(d)), un.double_add(r, d)), Equal.trans(Nat, Nat.double(Nat.add(r, d)), Nat.double(Nat.add(a, b)), Nat.add(Nat.double(a), Nat.double(b)), un.double_cong(Nat.add(r, d), Nat.add(a, b), e), un.double_add(a, b)))

def un.dd1(+r: Nat, +d: Nat, +a: Nat, +b: Nat, e: {Nat.add(r, d) == 1n+Nat.add(a, b) : Nat}) -> {Nat.add(Nat.double(r), Nat.double(d)) == 2n+Nat.add(Nat.double(a), Nat.double(b)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.double(r), Nat.double(d)), Nat.double(Nat.add(r, d)), 2n+Nat.add(Nat.double(a), Nat.double(b)), Equal.sym(Nat, Nat.double(Nat.add(r, d)), Nat.add(Nat.double(r), Nat.double(d)), un.double_add(r, d)), Equal.trans(Nat, Nat.double(Nat.add(r, d)), Nat.double(1n+Nat.add(a, b)), 2n+Nat.add(Nat.double(a), Nat.double(b)), un.double_cong(Nat.add(r, d), 1n+Nat.add(a, b), e), un.succ_cong(1n+Nat.double(Nat.add(a, b)), 1n+Nat.add(Nat.double(a), Nat.double(b)), un.succ_cong(Nat.double(Nat.add(a, b)), Nat.add(Nat.double(a), Nat.double(b)), un.double_add(a, b)))))

# 1 + (2A + (1 + 2B)) = 2 + (2A + 2B)
def un.sh(+a: Nat, +b: Nat) -> {2n+Nat.add(Nat.double(a), Nat.double(b)) == 1n+Nat.add(Nat.double(a), 1n+Nat.double(b)) : Nat}:
  un.succ_cong(1n+Nat.add(Nat.double(a), Nat.double(b)), Nat.add(Nat.double(a), 1n+Nat.double(b)), Equal.sym(Nat, Nat.add(Nat.double(a), 1n+Nat.double(b)), 1n+Nat.add(Nat.double(a), Nat.double(b)), un.add_succ(Nat.double(a), Nat.double(b))))

# one bit position of the adder
def un.cell(x: Bool, y: Bool, c: Bool, +r: Nat, +d: Nat, +a: Nat, +b: Nat, ih: {Nat.add(r, d) == Nat.add(U.U32Nat.bit(un.maj(x, y, c)), Nat.add(a, b)) : Nat}) -> {Nat.add(un.bv(un.sum(x, y, c), r), Nat.double(d)) == Nat.add(U.U32Nat.bit(c), Nat.add(un.bv(x, a), un.bv(y, b))) : Nat}:
  match x y c:
    case False{} False{} False{}:
      un.dd(r, d, a, b, ih)
    case True{} False{} False{}:
      un.succ_cong(Nat.add(Nat.double(r), Nat.double(d)), Nat.add(Nat.double(a), Nat.double(b)), un.dd(r, d, a, b, ih))
    case False{} True{} False{}:
      Equal.trans(Nat, 1n+Nat.add(Nat.double(r), Nat.double(d)), 1n+Nat.add(Nat.double(a), Nat.double(b)), Nat.add(Nat.double(a), 1n+Nat.double(b)), un.succ_cong(Nat.add(Nat.double(r), Nat.double(d)), Nat.add(Nat.double(a), Nat.double(b)), un.dd(r, d, a, b, ih)), Equal.sym(Nat, Nat.add(Nat.double(a), 1n+Nat.double(b)), 1n+Nat.add(Nat.double(a), Nat.double(b)), un.add_succ(Nat.double(a), Nat.double(b))))
    case False{} False{} True{}:
      un.succ_cong(Nat.add(Nat.double(r), Nat.double(d)), Nat.add(Nat.double(a), Nat.double(b)), un.dd(r, d, a, b, ih))
    case True{} True{} False{}:
      Equal.trans(Nat, Nat.add(Nat.double(r), Nat.double(d)), 2n+Nat.add(Nat.double(a), Nat.double(b)), 1n+Nat.add(Nat.double(a), 1n+Nat.double(b)), un.dd1(r, d, a, b, ih), un.sh(a, b))
    case True{} False{} True{}:
      un.dd1(r, d, a, b, ih)
    case False{} True{} True{}:
      Equal.trans(Nat, Nat.add(Nat.double(r), Nat.double(d)), 2n+Nat.add(Nat.double(a), Nat.double(b)), 1n+Nat.add(Nat.double(a), 1n+Nat.double(b)), un.dd1(r, d, a, b, ih), un.sh(a, b))
    case True{} True{} True{}:
      un.succ_cong(Nat.add(Nat.double(r), Nat.double(d)), 1n+Nat.add(Nat.double(a), 1n+Nat.double(b)), Equal.trans(Nat, Nat.add(Nat.double(r), Nat.double(d)), 2n+Nat.add(Nat.double(a), Nat.double(b)), 1n+Nat.add(Nat.double(a), 1n+Nat.double(b)), un.dd1(r, d, a, b, ih), un.sh(a, b)))

# adc(a, b, False, c) + 2^n * carry out = c + a + b
def un.add_v(n: Nat, a: Word(n), b: Word(n), c: Bool) -> {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), U.U32Nat.dbl(n, U.U32Nat.bit(un.co(n, a, b, c)))) == Nat.add(U.U32Nat.bit(c), Nat.add(Word.to_nat(n, a), Word.to_nat(n, b))) : Nat}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} False{}:
          {==}
        case WNil{} WNil{} True{}:
          {==}
    case 1n+ +p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          un.cell(False{}, False{}, False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), U.U32Nat.dbl(p, U.U32Nat.bit(un.co(p, at, bt, False{}))), Word.to_nat(p, at), Word.to_nat(p, bt), un.add_v(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          un.cell(True{}, False{}, False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), U.U32Nat.dbl(p, U.U32Nat.bit(un.co(p, at, bt, False{}))), Word.to_nat(p, at), Word.to_nat(p, bt), un.add_v(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          un.cell(False{}, True{}, False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), U.U32Nat.dbl(p, U.U32Nat.bit(un.co(p, at, bt, False{}))), Word.to_nat(p, at), Word.to_nat(p, bt), un.add_v(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          un.cell(False{}, False{}, True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, False{})), U.U32Nat.dbl(p, U.U32Nat.bit(un.co(p, at, bt, False{}))), Word.to_nat(p, at), Word.to_nat(p, bt), un.add_v(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          un.cell(True{}, True{}, False{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), U.U32Nat.dbl(p, U.U32Nat.bit(un.co(p, at, bt, True{}))), Word.to_nat(p, at), Word.to_nat(p, bt), un.add_v(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          un.cell(True{}, False{}, True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), U.U32Nat.dbl(p, U.U32Nat.bit(un.co(p, at, bt, True{}))), Word.to_nat(p, at), Word.to_nat(p, bt), un.add_v(p, at, bt, True{}))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          un.cell(False{}, True{}, True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), U.U32Nat.dbl(p, U.U32Nat.bit(un.co(p, at, bt, True{}))), Word.to_nat(p, at), Word.to_nat(p, bt), un.add_v(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          un.cell(True{}, True{}, True{}, Word.to_nat(p, Word.adc(p, at, bt, False{}, True{})), U.U32Nat.dbl(p, U.U32Nat.bit(un.co(p, at, bt, True{}))), Word.to_nat(p, at), Word.to_nat(p, bt), un.add_v(p, at, bt, True{}))

# Subtraction is addition of the complement

def un.wcon_cong(-p: Nat, -s: Bool, -x: Word(p), -y: Word(p), e: {x == y : Word(p)}) -> {WCon{s, x} == WCon{s, y} : Word(1n+p)}:
  %e : {WCon{s, x} == WCon{s, _} : Word(1n+p)}
  {==}

def un.adc_not(n: Nat, a: Word(n), b: Word(n), c: Bool) -> {Word.adc(n, a, b, True{}, c) == Word.adc(n, a, Word.not(n, b), False{}, c) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          un.wcon_cong(p, True{}, Word.adc(p, at, bt, True{}, False{}), Word.adc(p, at, Word.not(p, bt), False{}, False{}), un.adc_not(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          un.wcon_cong(p, False{}, Word.adc(p, at, bt, True{}, True{}), Word.adc(p, at, Word.not(p, bt), False{}, True{}), un.adc_not(p, at, bt, True{}))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          un.wcon_cong(p, False{}, Word.adc(p, at, bt, True{}, False{}), Word.adc(p, at, Word.not(p, bt), False{}, False{}), un.adc_not(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          un.wcon_cong(p, True{}, Word.adc(p, at, bt, True{}, False{}), Word.adc(p, at, Word.not(p, bt), False{}, False{}), un.adc_not(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          un.wcon_cong(p, False{}, Word.adc(p, at, bt, True{}, True{}), Word.adc(p, at, Word.not(p, bt), False{}, True{}), un.adc_not(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          un.wcon_cong(p, True{}, Word.adc(p, at, bt, True{}, True{}), Word.adc(p, at, Word.not(p, bt), False{}, True{}), un.adc_not(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          un.wcon_cong(p, True{}, Word.adc(p, at, bt, True{}, False{}), Word.adc(p, at, Word.not(p, bt), False{}, False{}), un.adc_not(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          un.wcon_cong(p, False{}, Word.adc(p, at, bt, True{}, True{}), Word.adc(p, at, Word.not(p, bt), False{}, True{}), un.adc_not(p, at, bt, True{}))

# Carries and borrows, from the values

# s + 2^n * C = A + B with B < 2^n: C is whether s < A
def un.carry(c: Bool, +n: Nat, +s: Nat, +a: Nat, +b: Nat, e: {Nat.add(s, U.U32Nat.dbl(n, U.U32Nat.bit(c))) == Nat.add(a, b) : Nat}, hb: {Nat.is_lt(b, U.U32Nat.dbl(n, 1n)) == True{} : Bool}) -> {Nat.is_lt(s, a) == c : Bool}:
  match c:
    case True{}:
      +k = U.U32Nat.dbl(n, 1n)
      +h1 = Equal.trans(Bool, Nat.is_lt(Nat.add(a, b), Nat.add(a, k)), Nat.is_lt(b, k), True{}, un.lt_add_l(a, b, k), hb)
      +h2 = un.lt_rw(Nat.add(a, b), Nat.add(s, k), Nat.add(a, k), Equal.sym(Nat, Nat.add(s, k), Nat.add(a, b), e), h1)
      Equal.trans(Bool, Nat.is_lt(s, a), Nat.is_lt(Nat.add(s, k), Nat.add(a, k)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(s, k), Nat.add(a, k)), Nat.is_lt(s, a), un.lt_add_r(s, a, k)), h2)
    case False{}:
      +es = Equal.trans(Nat, s, Nat.add(s, 0n), Nat.add(a, b), Equal.sym(Nat, Nat.add(s, 0n), s, un.add_zero(s)), Equal.trans(Nat, Nat.add(s, 0n), Nat.add(s, U.U32Nat.dbl(n, 0n)), Nat.add(a, b), Equal.cong(Nat, Nat, v => Nat.add(s, v), 0n, U.U32Nat.dbl(n, 0n), Equal.sym(Nat, U.U32Nat.dbl(n, 0n), 0n, Laws.dbl_zero(n))), e))
      %Equal.sym(Nat, s, Nat.add(a, b), es) : {Nat.is_lt(_, a) == False{} : Bool}
      un.not_lt_add(a, b)

# s + B = A + 2^n * C with s < 2^n: C is whether A < B
def un.borrow(c: Bool, +n: Nat, +s: Nat, +a: Nat, +b: Nat, e: {Nat.add(s, b) == Nat.add(a, U.U32Nat.dbl(n, U.U32Nat.bit(c))) : Nat}, hs: {Nat.is_lt(s, U.U32Nat.dbl(n, 1n)) == True{} : Bool}) -> {Nat.is_lt(a, b) == c : Bool}:
  match c:
    case True{}:
      +k = U.U32Nat.dbl(n, 1n)
      +h1 = Equal.trans(Bool, Nat.is_lt(Nat.add(s, b), Nat.add(k, b)), Nat.is_lt(s, k), True{}, un.lt_add_r(s, k, b), hs)
      +h2 = un.lt_rw(Nat.add(s, b), Nat.add(a, k), Nat.add(k, b), e, h1)
      +h3 = un.lt_rw2(Nat.add(a, k), Nat.add(k, b), Nat.add(b, k), un.add_comm(k, b), h2)
      Equal.trans(Bool, Nat.is_lt(a, b), Nat.is_lt(Nat.add(a, k), Nat.add(b, k)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(a, k), Nat.add(b, k)), Nat.is_lt(a, b), un.lt_add_r(a, b, k)), h3)
    case False{}:
      +ea = Equal.trans(Nat, Nat.add(s, b), Nat.add(a, U.U32Nat.dbl(n, 0n)), a, e, Equal.trans(Nat, Nat.add(a, U.U32Nat.dbl(n, 0n)), Nat.add(a, 0n), a, Equal.cong(Nat, Nat, v => Nat.add(a, v), U.U32Nat.dbl(n, 0n), 0n, Laws.dbl_zero(n)), un.add_zero(a)))
      %ea : {Nat.is_lt(_, b) == False{} : Bool}
      un.not_lt_add_l(s, b)

# The laws on words

def Laws.word_add_wrap(n, a, b):
  +s = Word.to_nat(n, Word.adc(n, a, b, False{}, False{}))
  +av = Word.to_nat(n, a)
  +bv = Word.to_nat(n, b)
  +c = un.co(n, a, b, False{})
  +ec = un.carry(c, n, s, av, bv, un.add_v(n, a, b, False{}), Laws.word_value_lt(n, b))
  %Equal.sym(Cmp, Word.cmp(n, Word.adc(n, a, b, False{}, False{}), a), Nat.cmp(s, av), Laws.word_cmp_value(n, Word.adc(n, a, b, False{}, False{}), a)) : {Nat.add(s, U.U32Nat.dbl(n, U.U32Nat.bit(Cmp.is_lt(_)))) == Nat.add(av, bv) : Nat}
  %Equal.sym(Bool, Nat.is_lt(s, av), c, ec) : {Nat.add(s, U.U32Nat.dbl(n, U.U32Nat.bit(_))) == Nat.add(av, bv) : Nat}
  un.add_v(n, a, b, False{})

def un.add_nowrap(c: Bool, +n: Nat, +s: Nat, +a: Nat, +b: Nat, +z: Nat, e: {Nat.add(s, U.U32Nat.dbl(n, U.U32Nat.bit(c))) == Nat.add(a, b) : Nat}, h: {Nat.is_le(Nat.add(a, b), z) == True{} : Bool}, hz: {Nat.is_lt(z, U.U32Nat.dbl(n, 1n)) == True{} : Bool}) -> {s == Nat.add(a, b) : Nat}:
  match c:
    case True{}:
      +k = U.U32Nat.dbl(n, 1n)
      Empty.absurd({s == Nat.add(a, b) : Nat}, un.add_lt_absurd(s, k, un.lt_rw(Nat.add(a, b), Nat.add(s, k), k, Equal.sym(Nat, Nat.add(s, k), Nat.add(a, b), e), un.le_lt_trans(Nat.add(a, b), z, k, h, hz))))
    case False{}:
      Equal.trans(Nat, s, Nat.add(s, 0n), Nat.add(a, b), Equal.sym(Nat, Nat.add(s, 0n), s, un.add_zero(s)), Equal.trans(Nat, Nat.add(s, 0n), Nat.add(s, U.U32Nat.dbl(n, 0n)), Nat.add(a, b), Equal.cong(Nat, Nat, v => Nat.add(s, v), 0n, U.U32Nat.dbl(n, 0n), Equal.sym(Nat, U.U32Nat.dbl(n, 0n), 0n, Laws.dbl_zero(n))), e))

def Laws.word_add_value(n, a, b, z, h):
  +s = Word.to_nat(n, Word.adc(n, a, b, False{}, False{}))
  +av = Word.to_nat(n, a)
  +bv = Word.to_nat(n, b)
  un.add_nowrap(un.co(n, a, b, False{}), n, s, av, bv, Word.to_nat(n, z), un.add_v(n, a, b, False{}), h, Laws.word_value_lt(n, z))


# (s + b) + k = (s + k) + b
def un.add_swap(s: Nat, +b: Nat, +k: Nat) -> {Nat.add(Nat.add(s, b), k) == Nat.add(Nat.add(s, k), b) : Nat}:
  match s:
    case 0n:
      un.add_comm(b, k)
    case 1n+p:
      un.succ_cong(Nat.add(Nat.add(p, b), k), Nat.add(Nat.add(p, k), b), un.add_swap(p, b, k))

# (1 + (a + nb)) + b = a + k when 1 + nb + b = k
def un.sub_mid(a: Nat, -nb: Nat, -b: Nat, -k: Nat, en: {1n+Nat.add(nb, b) == k : Nat}) -> {Nat.add(1n+Nat.add(a, nb), b) == Nat.add(a, k) : Nat}:
  match a:
    case 0n:
      en
    case 1n+p:
      un.succ_cong(Nat.add(1n+Nat.add(p, nb), b), Nat.add(p, k), un.sub_mid(p, nb, b, k, en))

# s + B = A + 2^n * C, from adc(a, not b, True) + 2^n * carry = 1 + A + not B
# and 1 + not B + B = 2^n
def un.sub_v(c: Bool, +n: Nat, +s: Nat, +a: Nat, +b: Nat, +nb: Nat, e: {Nat.add(s, U.U32Nat.dbl(n, U.U32Nat.bit(c))) == 1n+Nat.add(a, nb) : Nat}, en: {1n+Nat.add(nb, b) == U.U32Nat.dbl(n, 1n) : Nat}) -> {Nat.add(s, b) == Nat.add(a, U.U32Nat.dbl(n, U.U32Nat.bit(Bool.not(c)))) : Nat}:
  match c:
    case True{}:
      +k = U.U32Nat.dbl(n, 1n)
      +e2 = Equal.trans(Nat, Nat.add(Nat.add(s, b), k), Nat.add(Nat.add(s, k), b), Nat.add(a, k), un.add_swap(s, b, k), Equal.trans(Nat, Nat.add(Nat.add(s, k), b), Nat.add(1n+Nat.add(a, nb), b), Nat.add(a, k), Equal.cong(Nat, Nat, v => Nat.add(v, b), Nat.add(s, k), 1n+Nat.add(a, nb), e), un.sub_mid(a, nb, b, k, en)))
      +e3 = un.add_cancel_r(Nat.add(s, b), a, k, e2)
      Equal.trans(Nat, Nat.add(s, b), a, Nat.add(a, U.U32Nat.dbl(n, 0n)), e3, Equal.trans(Nat, a, Nat.add(a, 0n), Nat.add(a, U.U32Nat.dbl(n, 0n)), Equal.sym(Nat, Nat.add(a, 0n), a, un.add_zero(a)), Equal.cong(Nat, Nat, v => Nat.add(a, v), 0n, U.U32Nat.dbl(n, 0n), Equal.sym(Nat, U.U32Nat.dbl(n, 0n), 0n, Laws.dbl_zero(n)))))
    case False{}:
      +e0 = Equal.trans(Nat, s, Nat.add(s, 0n), 1n+Nat.add(a, nb), Equal.sym(Nat, Nat.add(s, 0n), s, un.add_zero(s)), Equal.trans(Nat, Nat.add(s, 0n), Nat.add(s, U.U32Nat.dbl(n, 0n)), 1n+Nat.add(a, nb), Equal.cong(Nat, Nat, v => Nat.add(s, v), 0n, U.U32Nat.dbl(n, 0n), Equal.sym(Nat, U.U32Nat.dbl(n, 0n), 0n, Laws.dbl_zero(n))), e))
      Equal.trans(Nat, Nat.add(s, b), Nat.add(1n+Nat.add(a, nb), b), Nat.add(a, U.U32Nat.dbl(n, 1n)), Equal.cong(Nat, Nat, v => Nat.add(v, b), s, 1n+Nat.add(a, nb), e0), un.sub_mid(a, nb, b, U.U32Nat.dbl(n, 1n), en))



def Laws.word_sub_wrap(n, a, b):
  +nb = Word.not(n, b)
  +s = Word.to_nat(n, Word.adc(n, a, nb, False{}, True{}))
  +av = Word.to_nat(n, a)
  +bv = Word.to_nat(n, b)
  +nv = Word.to_nat(n, nb)
  +c = un.co(n, a, nb, True{})
  +eb = un.borrow(Bool.not(c), n, s, av, bv, un.sub_v(c, n, s, av, bv, nv, un.add_v(n, a, nb, True{}), Laws.word_not_value(n, b)), Laws.word_value_lt(n, Word.adc(n, a, nb, False{}, True{})))
  %Equal.sym(Word(n), Word.adc(n, a, b, True{}, True{}), Word.adc(n, a, Word.not(n, b), False{}, True{}), un.adc_not(n, a, b, True{})) : {Nat.add(Word.to_nat(n, _), bv) == Nat.add(av, U.U32Nat.dbl(n, U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, a, b))))) : Nat}
  %Equal.sym(Cmp, Word.cmp(n, a, b), Nat.cmp(av, bv), Laws.word_cmp_value(n, a, b)) : {Nat.add(s, bv) == Nat.add(av, U.U32Nat.dbl(n, U.U32Nat.bit(Cmp.is_lt(_)))) : Nat}
  %Equal.sym(Bool, Nat.is_lt(av, bv), Bool.not(c), eb) : {Nat.add(s, bv) == Nat.add(av, U.U32Nat.dbl(n, U.U32Nat.bit(_))) : Nat}
  un.sub_v(c, n, s, av, bv, nv, un.add_v(n, a, nb, True{}), Laws.word_not_value(n, b))

def Laws.word_sub_value(n, a, b, h):
  +s = Word.to_nat(n, Word.sub(n, a, b))
  +av = Word.to_nat(n, a)
  +bv = Word.to_nat(n, b)
  +w = Laws.word_sub_wrap(n, a, b)
  +nl = un.le_not_lt(bv, av, h)
  +el = Equal.trans(Bool, Cmp.is_lt(Word.cmp(n, a, b)), Nat.is_lt(av, bv), False{}, Equal.cong(Cmp, Bool, x => Cmp.is_lt(x), Word.cmp(n, a, b), Nat.cmp(av, bv), Laws.word_cmp_value(n, a, b)), nl)
  +e1 = Equal.trans(Nat, Nat.add(s, bv), Nat.add(av, U.U32Nat.dbl(n, U.U32Nat.bit(False{}))), av, Equal.trans(Nat, Nat.add(s, bv), Nat.add(av, U.U32Nat.dbl(n, U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, a, b))))), Nat.add(av, U.U32Nat.dbl(n, U.U32Nat.bit(False{}))), w, Equal.cong(Bool, Nat, x => Nat.add(av, U.U32Nat.dbl(n, U.U32Nat.bit(x))), Cmp.is_lt(Word.cmp(n, a, b)), False{}, el)), Equal.trans(Nat, Nat.add(av, U.U32Nat.dbl(n, 0n)), Nat.add(av, 0n), av, Equal.cong(Nat, Nat, v => Nat.add(av, v), U.U32Nat.dbl(n, 0n), 0n, Laws.dbl_zero(n)), un.add_zero(av)))
  %e1 : {s == Nat.sub(_, bv) : Nat}
  Equal.sym(Nat, Nat.sub(Nat.add(s, bv), bv), s, un.sub_add(s, bv))

# Increment

def un.inc_w(n: Nat, w: Word(n), h: {Nat.is_lt(1n+Word.to_nat(n, w), U.U32Nat.dbl(n, 1n)) == True{} : Bool}) -> {Word.to_nat(n, Word.inc(n, w)) == 1n+Word.to_nat(n, w) : Nat}:
  match n:
    case 0n:
      Empty.absurd({Word.to_nat(0n, Word.inc(0n, w)) == 1n+Word.to_nat(0n, w) : Nat}, un.ft(h))
    case 1n+ +p:
      match w:
        case WCon{False{}, t}:
          {==}
        case WCon{True{}, +t}:
          +x = Word.to_nat(p, t)
          un.double_cong(Word.to_nat(p, Word.inc(p, t)), 1n+x, un.inc_w(p, t, Equal.trans(Bool, Nat.is_lt(1n+x, U.U32Nat.dbl(p, 1n)), Nat.is_lt(Nat.double(1n+x), Nat.double(U.U32Nat.dbl(p, 1n))), True{}, Equal.sym(Bool, Nat.is_lt(Nat.double(1n+x), Nat.double(U.U32Nat.dbl(p, 1n))), Nat.is_lt(1n+x, U.U32Nat.dbl(p, 1n)), un.lt_dbl(1n+x, U.U32Nat.dbl(p, 1n))), h)))

def Laws.word_inc_value(n, w, z, h):
  un.inc_w(n, w, un.le_lt_trans(1n+Word.to_nat(n, w), Word.to_nat(n, z), U.U32Nat.dbl(n, 1n), h, Laws.word_value_lt(n, z)))

# Shifts left: bits move up by one, a bit c coming in at the bottom

def un.shlput(n: Nat, c: Bool, w: Word(n), h: {Nat.is_lt(Nat.add(U.U32Nat.bit(c), Nat.double(Word.to_nat(n, w))), U.U32Nat.dbl(n, 1n)) == True{} : Bool}) -> {Word.to_nat(n, Word.shl.put(n, c, w)) == Nat.add(U.U32Nat.bit(c), Nat.double(Word.to_nat(n, w))) : Nat}:
  match n:
    case 0n:
      match c w:
        case False{} WNil{}:
          {==}
        case True{} WNil{}:
          Empty.absurd({0n == 1n : Nat}, un.ft(h))
    case 1n+ +p:
      match c w:
        case False{} WCon{False{}, +t}:
          +k = U.U32Nat.dbl(p, 1n)
          +x = Word.to_nat(p, t)
          un.double_cong(Word.to_nat(p, Word.shl.put(p, False{}, t)), Nat.double(x), un.shlput(p, False{}, t, Equal.trans(Bool, Nat.is_lt(Nat.double(x), k), Nat.is_lt(Nat.double(Nat.double(x)), Nat.double(k)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.double(Nat.double(x)), Nat.double(k)), Nat.is_lt(Nat.double(x), k), un.lt_dbl(Nat.double(x), k)), h)))
        case False{} WCon{True{}, +t}:
          +k = U.U32Nat.dbl(p, 1n)
          +x = Word.to_nat(p, t)
          un.double_cong(Word.to_nat(p, Word.shl.put(p, True{}, t)), 1n+Nat.double(x), un.shlput(p, True{}, t, Equal.trans(Bool, Nat.is_lt(1n+Nat.double(x), k), Nat.is_lt(Nat.double(1n+Nat.double(x)), Nat.double(k)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.double(1n+Nat.double(x)), Nat.double(k)), Nat.is_lt(1n+Nat.double(x), k), un.lt_dbl(1n+Nat.double(x), k)), h)))
        case True{} WCon{False{}, +t}:
          +k = U.U32Nat.dbl(p, 1n)
          +x = Word.to_nat(p, t)
          un.succ_cong(Nat.double(Word.to_nat(p, Word.shl.put(p, False{}, t))), Nat.double(Nat.double(x)), un.double_cong(Word.to_nat(p, Word.shl.put(p, False{}, t)), Nat.double(x), un.shlput(p, False{}, t, Equal.trans(Bool, Nat.is_lt(Nat.double(x), k), Nat.is_lt(1n+Nat.double(Nat.double(x)), Nat.double(k)), True{}, Equal.sym(Bool, Nat.is_lt(1n+Nat.double(Nat.double(x)), Nat.double(k)), Nat.is_lt(Nat.double(x), k), un.lt_dbl1(Nat.double(x), k)), h))))
        case True{} WCon{True{}, +t}:
          +k = U.U32Nat.dbl(p, 1n)
          +x = Word.to_nat(p, t)
          un.succ_cong(Nat.double(Word.to_nat(p, Word.shl.put(p, True{}, t))), Nat.double(1n+Nat.double(x)), un.double_cong(Word.to_nat(p, Word.shl.put(p, True{}, t)), 1n+Nat.double(x), un.shlput(p, True{}, t, Equal.trans(Bool, Nat.is_lt(1n+Nat.double(x), k), Nat.is_lt(1n+Nat.double(1n+Nat.double(x)), Nat.double(k)), True{}, Equal.sym(Bool, Nat.is_lt(1n+Nat.double(1n+Nat.double(x)), Nat.double(k)), Nat.is_lt(1n+Nat.double(x), k), un.lt_dbl1(1n+Nat.double(x), k)), h))))

def un.shl_w(n: Nat, w: Word(n), h: {Nat.is_lt(Nat.double(Word.to_nat(n, w)), U.U32Nat.dbl(n, 1n)) == True{} : Bool}) -> {Word.to_nat(n, Word.shl(n, w)) == Nat.double(Word.to_nat(n, w)) : Nat}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+ +p:
      match w:
        case WCon{False{}, +t}:
          +k = U.U32Nat.dbl(p, 1n)
          +x = Word.to_nat(p, t)
          un.double_cong(Word.to_nat(p, Word.shl.put(p, False{}, t)), Nat.double(x), un.shlput(p, False{}, t, Equal.trans(Bool, Nat.is_lt(Nat.double(x), k), Nat.is_lt(Nat.double(Nat.double(x)), Nat.double(k)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.double(Nat.double(x)), Nat.double(k)), Nat.is_lt(Nat.double(x), k), un.lt_dbl(Nat.double(x), k)), h)))
        case WCon{True{}, +t}:
          +k = U.U32Nat.dbl(p, 1n)
          +x = Word.to_nat(p, t)
          un.double_cong(Word.to_nat(p, Word.shl.put(p, True{}, t)), 1n+Nat.double(x), un.shlput(p, True{}, t, Equal.trans(Bool, Nat.is_lt(1n+Nat.double(x), k), Nat.is_lt(Nat.double(1n+Nat.double(x)), Nat.double(k)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.double(1n+Nat.double(x)), Nat.double(k)), Nat.is_lt(1n+Nat.double(x), k), un.lt_dbl(1n+Nat.double(x), k)), h)))

def Laws.word_shl_value(n, w, z, h):
  un.shl_w(n, w, un.le_lt_trans(Nat.double(Word.to_nat(n, w)), Word.to_nat(n, z), U.U32Nat.dbl(n, 1n), h, Laws.word_value_lt(n, z)))

# Shifts right: halving

def un.pad(p: Nat, t: Word(p)) -> {Word.to_nat(1n+p, Word.shr.pad(p, t)) == Word.to_nat(p, t) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+ +q:
      match t:
        case WCon{False{}, +r}:
          un.double_cong(Word.to_nat(1n+q, Word.shr.pad(q, r)), Word.to_nat(q, r), un.pad(q, r))
        case WCon{True{}, +r}:
          un.succ_cong(Nat.double(Word.to_nat(1n+q, Word.shr.pad(q, r))), Nat.double(Word.to_nat(q, r)), un.double_cong(Word.to_nat(1n+q, Word.shr.pad(q, r)), Word.to_nat(q, r), un.pad(q, r)))

def Laws.word_shr_value(n, w):
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{False{}, +t}:
          Equal.trans(Nat, Word.to_nat(1n+p, Word.shr.pad(p, t)), Word.to_nat(p, t), U.U32Nat.half(Nat.double(Word.to_nat(p, t))), un.pad(p, t), Equal.sym(Nat, U.U32Nat.half(Nat.double(Word.to_nat(p, t))), Word.to_nat(p, t), Laws.half_double(Word.to_nat(p, t))))
        case WCon{True{}, +t}:
          Equal.trans(Nat, Word.to_nat(1n+p, Word.shr.pad(p, t)), Word.to_nat(p, t), U.U32Nat.half(1n+Nat.double(Word.to_nat(p, t))), un.pad(p, t), Equal.sym(Nat, U.U32Nat.half(1n+Nat.double(Word.to_nat(p, t))), Word.to_nat(p, t), Laws.half_double_one(Word.to_nat(p, t))))

# U32: the laws on Word(32n)

def Laws.u32_cmp_value(a, b):
  match a b:
    case U32{x} U32{y}:
      Laws.word_cmp_value(32n, x, y)

def Laws.u32_lt_value(a, b):
  %Laws.u32_cmp_value(a, b) : {Cmp.is_lt(U32.cmp(a, b)) == Cmp.is_lt(_) : Bool}
  {==}

def Laws.u32_le_value(a, b):
  %Laws.u32_cmp_value(a, b) : {Cmp.is_le(U32.cmp(a, b)) == Cmp.is_le(_) : Bool}
  {==}

def Laws.u32_eq_value(a, b):
  %Laws.u32_cmp_value(a, b) : {Cmp.is_eq(U32.cmp(a, b)) == Cmp.is_eq(_) : Bool}
  {==}

def un.u32_cong(-x: Word(32n), -y: Word(32n), e: {x == y : Word(32n)}) -> {U32{x} == U32{y} : U32}:
  %e : {U32{x} == U32{_} : U32}
  {==}

def Laws.u32_value_eq(a, b, e):
  match a b:
    case U32{x} U32{y}:
      un.u32_cong(x, y, Laws.word_value_eq(32n, x, y, e))

def Laws.u32_add_wrap(a, b):
  match a b:
    case U32{x} U32{y}:
      Laws.word_add_wrap(32n, x, y)

def Laws.u32_add_value(a, b, c, h):
  match a b c:
    case U32{x} U32{y} U32{z}:
      Laws.word_add_value(32n, x, y, z, h)

def Laws.u32_sub_wrap(a, b):
  match a b:
    case U32{x} U32{y}:
      Laws.word_sub_wrap(32n, x, y)

def Laws.u32_sub_value(a, b, h):
  match a b:
    case U32{x} U32{y}:
      Laws.word_sub_value(32n, x, y, h)

def Laws.u32_inc_value(a, c, h):
  match a c:
    case U32{w} U32{z}:
      Laws.word_inc_value(32n, w, z, h)

def Laws.u32_shl_value(a, c, h):
  match a c:
    case U32{w} U32{z}:
      Laws.word_shl_value(32n, w, z, h)

def Laws.u32_shln_value(a, k, c, h):
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +av = U32.to_nat(a)
      +cv = U32.to_nat(c)
      +ih = Laws.u32_shln_value(a, p, c, un.le_trans(U.U32Nat.dbl(p, av), Nat.double(U.U32Nat.dbl(p, av)), cv, un.le_double(U.U32Nat.dbl(p, av)), h))
      +h2 = Equal.trans(Bool, Nat.is_le(Nat.double(U32.to_nat(U32.shln(a, p))), cv), Nat.is_le(Nat.double(U.U32Nat.dbl(p, av)), cv), True{}, Equal.cong(Nat, Bool, v => Nat.is_le(Nat.double(v), cv), U32.to_nat(U32.shln(a, p)), U.U32Nat.dbl(p, av), ih), h)
      Equal.trans(Nat, U32.to_nat(U32.shl(U32.shln(a, p))), Nat.double(U32.to_nat(U32.shln(a, p))), Nat.double(U.U32Nat.dbl(p, av)), Laws.u32_shl_value(U32.shln(a, p), c, h2), un.double_cong(U32.to_nat(U32.shln(a, p)), U.U32Nat.dbl(p, av), ih))

def Laws.u32_shr_value(a):
  match a:
    case U32{w}:
      Laws.word_shr_value(32n, w)

# Witnesses and vectors

def Laws.u32_wit():
  {==}

def Laws.dbl_vec():
  {==}

# ---- generated by gen/proof.py from here on: do not edit by hand ----

# The Nat library

def Laws.nat_add_zero(x):
  un.add_zero(x)

def Laws.nat_add_succ(x, y):
  un.add_succ(x, y)

def Laws.nat_add_comm(x, y):
  un.add_comm(x, y)

def Laws.nat_add_assoc(x, y, z):
  match x:
    case 0n:
      {==}
    case 1n+p:
      un.succ_cong(Nat.add(Nat.add(p, y), z), Nat.add(p, Nat.add(y, z)), Laws.nat_add_assoc(p, y, z))

def Laws.nat_add_left_comm(x, y, z):
  Equal.trans(Nat, Nat.add(x, Nat.add(y, z)), Nat.add(Nat.add(y, x), z), Nat.add(y, Nat.add(x, z)), Equal.trans(Nat, Nat.add(x, Nat.add(y, z)), Nat.add(Nat.add(x, y), z), Nat.add(Nat.add(y, x), z), Equal.sym(Nat, Nat.add(Nat.add(x, y), z), Nat.add(x, Nat.add(y, z)), Laws.nat_add_assoc(x, y, z)), Equal.cong(Nat, Nat, zz => Nat.add(zz, z), Nat.add(x, y), Nat.add(y, x), Laws.nat_add_comm(x, y))), Laws.nat_add_assoc(y, x, z))

def Laws.nat_add_cancel(k, x, y, e):
  match k:
    case 0n:
      e
    case 1n+p:
      Laws.nat_add_cancel(p, x, y, un.succ_inj(Nat.add(p, x), Nat.add(p, y), e))

def Laws.nat_mul_zero(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      Laws.nat_mul_zero(p)

def Laws.nat_one_mul(x):
  un.add_zero(x)

def Laws.nat_mul_succ(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      un.succ_cong(Nat.add(y, Nat.mul(p, 1n+y)), Nat.add(p, Nat.add(y, Nat.mul(p, y))), Equal.trans(Nat, Nat.add(y, Nat.mul(p, 1n+y)), Nat.add(y, Nat.add(p, Nat.mul(p, y))), Nat.add(p, Nat.add(y, Nat.mul(p, y))), Equal.cong(Nat, Nat, zz => Nat.add(y, zz), Nat.mul(p, 1n+y), Nat.add(p, Nat.mul(p, y)), Laws.nat_mul_succ(p, y)), Laws.nat_add_left_comm(y, p, Nat.mul(p, y))))

def Laws.nat_mul_comm(x, y):
  match x:
    case 0n:
      Equal.sym(Nat, Nat.mul(y, 0n), 0n, Laws.nat_mul_zero(y))
    case 1n+p:
      Equal.trans(Nat, Nat.add(y, Nat.mul(p, y)), Nat.add(y, Nat.mul(y, p)), Nat.mul(y, 1n+p), Equal.cong(Nat, Nat, zz => Nat.add(y, zz), Nat.mul(p, y), Nat.mul(y, p), Laws.nat_mul_comm(p, y)), Equal.sym(Nat, Nat.mul(y, 1n+p), Nat.add(y, Nat.mul(y, p)), Laws.nat_mul_succ(y, p)))

def Laws.nat_add_mul(x, y, z):
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, Nat.add(z, Nat.mul(Nat.add(p, y), z)), Nat.add(z, Nat.add(Nat.mul(p, z), Nat.mul(y, z))), Nat.add(Nat.add(z, Nat.mul(p, z)), Nat.mul(y, z)), Equal.cong(Nat, Nat, zz => Nat.add(z, zz), Nat.mul(Nat.add(p, y), z), Nat.add(Nat.mul(p, z), Nat.mul(y, z)), Laws.nat_add_mul(p, y, z)), Equal.sym(Nat, Nat.add(Nat.add(z, Nat.mul(p, z)), Nat.mul(y, z)), Nat.add(z, Nat.add(Nat.mul(p, z), Nat.mul(y, z))), Laws.nat_add_assoc(z, Nat.mul(p, z), Nat.mul(y, z))))

def Laws.nat_mul_add(x, y, z):
  Equal.trans(Nat, Nat.mul(x, Nat.add(y, z)), Nat.add(Nat.mul(x, y), Nat.mul(z, x)), Nat.add(Nat.mul(x, y), Nat.mul(x, z)), Equal.trans(Nat, Nat.mul(x, Nat.add(y, z)), Nat.add(Nat.mul(y, x), Nat.mul(z, x)), Nat.add(Nat.mul(x, y), Nat.mul(z, x)), Equal.trans(Nat, Nat.mul(x, Nat.add(y, z)), Nat.mul(Nat.add(y, z), x), Nat.add(Nat.mul(y, x), Nat.mul(z, x)), Laws.nat_mul_comm(x, Nat.add(y, z)), Laws.nat_add_mul(y, z, x)), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.mul(z, x)), Nat.mul(y, x), Nat.mul(x, y), Laws.nat_mul_comm(y, x))), Equal.cong(Nat, Nat, zz => Nat.add(Nat.mul(x, y), zz), Nat.mul(z, x), Nat.mul(x, z), Laws.nat_mul_comm(z, x)))

def Laws.nat_mul_assoc(x, y, z):
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, Nat.mul(Nat.add(y, Nat.mul(p, y)), z), Nat.add(Nat.mul(y, z), Nat.mul(Nat.mul(p, y), z)), Nat.add(Nat.mul(y, z), Nat.mul(p, Nat.mul(y, z))), Laws.nat_add_mul(y, Nat.mul(p, y), z), Equal.cong(Nat, Nat, zz => Nat.add(Nat.mul(y, z), zz), Nat.mul(Nat.mul(p, y), z), Nat.mul(p, Nat.mul(y, z)), Laws.nat_mul_assoc(p, y, z)))

def Laws.nat_mul_left_comm(x, y, z):
  Equal.trans(Nat, Nat.mul(x, Nat.mul(y, z)), Nat.mul(Nat.mul(y, x), z), Nat.mul(y, Nat.mul(x, z)), Equal.trans(Nat, Nat.mul(x, Nat.mul(y, z)), Nat.mul(Nat.mul(x, y), z), Nat.mul(Nat.mul(y, x), z), Equal.sym(Nat, Nat.mul(Nat.mul(x, y), z), Nat.mul(x, Nat.mul(y, z)), Laws.nat_mul_assoc(x, y, z)), Equal.cong(Nat, Nat, zz => Nat.mul(zz, z), Nat.mul(x, y), Nat.mul(y, x), Laws.nat_mul_comm(x, y))), Laws.nat_mul_assoc(y, x, z))

def Laws.nat_mul_one(x):
  Equal.trans(Nat, Nat.mul(x, 1n), Nat.mul(1n, x), x, Laws.nat_mul_comm(x, 1n), Laws.nat_one_mul(x))

def Laws.nat_double(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      un.succ_cong(1n+Nat.double(p), Nat.add(p, 1n+p), Equal.trans(Nat, 1n+Nat.double(p), 1n+Nat.add(p, p), Nat.add(p, 1n+p), un.succ_cong(Nat.double(p), Nat.add(p, p), Laws.nat_double(p)), Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), un.add_succ(p, p))))

def Laws.dbl_comm(j, k, x):
  Equal.trans(Nat, U.U32Nat.dbl(j, U.U32Nat.dbl(k, x)), U.U32Nat.dbl(Nat.add(k, j), x), U.U32Nat.dbl(k, U.U32Nat.dbl(j, x)), Equal.trans(Nat, U.U32Nat.dbl(j, U.U32Nat.dbl(k, x)), U.U32Nat.dbl(Nat.add(j, k), x), U.U32Nat.dbl(Nat.add(k, j), x), Laws.dbl_dbl(j, k, x), Equal.cong(Nat, Nat, zz => U.U32Nat.dbl(zz, x), Nat.add(j, k), Nat.add(k, j), Laws.nat_add_comm(j, k))), Equal.sym(Nat, U.U32Nat.dbl(k, U.U32Nat.dbl(j, x)), U.U32Nat.dbl(Nat.add(k, j), x), Laws.dbl_dbl(k, j, x)))

def un.double_mul(+x: Nat, +y: Nat) -> {Nat.mul(Nat.double(x), y) == Nat.double(Nat.mul(x, y)) : Nat}:
  Equal.trans(Nat, Nat.mul(Nat.double(x), y), Nat.add(Nat.mul(x, y), Nat.mul(x, y)), Nat.double(Nat.mul(x, y)), Equal.trans(Nat, Nat.mul(Nat.double(x), y), Nat.mul(Nat.add(x, x), y), Nat.add(Nat.mul(x, y), Nat.mul(x, y)), Equal.cong(Nat, Nat, zz => Nat.mul(zz, y), Nat.double(x), Nat.add(x, x), Laws.nat_double(x)), Laws.nat_add_mul(x, x, y)), Equal.sym(Nat, Nat.double(Nat.mul(x, y)), Nat.add(Nat.mul(x, y), Nat.mul(x, y)), Laws.nat_double(Nat.mul(x, y))))

def Laws.dbl_mul_l(k, x, y):
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, Nat.mul(Nat.double(U.U32Nat.dbl(p, x)), y), Nat.double(Nat.mul(U.U32Nat.dbl(p, x), y)), Nat.double(U.U32Nat.dbl(p, Nat.mul(x, y))), un.double_mul(U.U32Nat.dbl(p, x), y), un.double_cong(Nat.mul(U.U32Nat.dbl(p, x), y), U.U32Nat.dbl(p, Nat.mul(x, y)), Laws.dbl_mul_l(p, x, y)))

def Laws.dbl_mul_r(k, x, y):
  Equal.trans(Nat, Nat.mul(x, U.U32Nat.dbl(k, y)), U.U32Nat.dbl(k, Nat.mul(y, x)), U.U32Nat.dbl(k, Nat.mul(x, y)), Equal.trans(Nat, Nat.mul(x, U.U32Nat.dbl(k, y)), Nat.mul(U.U32Nat.dbl(k, y), x), U.U32Nat.dbl(k, Nat.mul(y, x)), Laws.nat_mul_comm(x, U.U32Nat.dbl(k, y)), Laws.dbl_mul_l(k, y, x)), Equal.cong(Nat, Nat, zz => U.U32Nat.dbl(k, zz), Nat.mul(y, x), Nat.mul(x, y), Laws.nat_mul_comm(y, x)))

def Laws.nat_le_refl(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      Laws.nat_le_refl(p)

def Laws.nat_le_add(x, w):
  match w:
    case 0n:
      Laws.nat_le_refl(x)
    case 1n+v:
      un.le_trans(x, Nat.add(v, x), 1n+Nat.add(v, x), Laws.nat_le_add(x, v), un.le_succ_self(Nat.add(v, x)))

def Laws.nat_lt_add(x, w):
  Equal.trans(Bool, Nat.is_lt(x, Nat.add(w, 1n+x)), Nat.is_le(1n+x, Nat.add(w, 1n+x)), True{}, Equal.sym(Bool, Nat.is_le(1n+x, Nat.add(w, 1n+x)), Nat.is_lt(x, Nat.add(w, 1n+x)), un.le_succ(x, Nat.add(w, 1n+x))), Laws.nat_le_add(1n+x, w))

def Laws.nat_le_witness(x, y, h):
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+yp:
      un.add_zero(1n+yp)
    case 1n+xp 0n:
      Empty.absurd({Nat.add(0n, 1n+xp) == 0n : Nat}, un.ft(h))
    case 1n+xp 1n+yp:
      Equal.trans(Nat, Nat.add(Nat.sub(yp, xp), 1n+xp), 1n+Nat.add(Nat.sub(yp, xp), xp), 1n+yp, un.add_succ(Nat.sub(yp, xp), xp), un.succ_cong(Nat.add(Nat.sub(yp, xp), xp), yp, Laws.nat_le_witness(xp, yp, h)))

def Laws.nat_lt_witness(x, y, h):
  Laws.nat_le_witness(1n+x, y, Equal.trans(Bool, Nat.is_le(1n+x, y), Nat.is_lt(x, y), True{}, un.le_succ(x, y), h))

def un.nz(x: Nat) -> Type:
  match x:
    case 0n:
      Empty
    case 1n+p:
      Unit

def un.sz(-a: Nat, e: {1n+a == 0n : Nat}) -> Empty:
  %e : un.nz(_)
  Unit{}

def Laws.nat_succ_add_absurd(w, x, e):
  match x:
    case 0n:
      un.sz(Nat.add(w, 0n), Equal.trans(Nat, 1n+Nat.add(w, 0n), Nat.add(w, 1n), 0n, Equal.sym(Nat, Nat.add(w, 1n), 1n+Nat.add(w, 0n), un.add_succ(w, 0n)), e))
    case 1n+p:
      Laws.nat_succ_add_absurd(w, p, un.succ_inj(Nat.add(w, 1n+p), p, Equal.trans(Nat, 1n+Nat.add(w, 1n+p), Nat.add(w, 2n+p), 1n+p, Equal.sym(Nat, Nat.add(w, 2n+p), 1n+Nat.add(w, 1n+p), un.add_succ(w, 1n+p)), e)))

def ur.r0(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat) -> {Nat.add(Nat.add(x0, Nat.add(Nat.mul(x1, x2), x3)), 1n+x2) == Nat.add(x0, 1n+Nat.add(Nat.mul(1n+x1, x2), x3)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(Nat.mul(x1, x2), x3)), Nat.add(1n, x2)), Nat.add(x0, Nat.add(Nat.add(Nat.mul(x1, x2), x3), Nat.add(1n, x2))), Laws.nat_add_assoc(x0, Nat.add(Nat.mul(x1, x2), x3), Nat.add(1n, x2))) : {_ == Nat.add(x0, 1n+Nat.add(Nat.mul(1n+x1, x2), x3)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(x1, x2), x3), Nat.add(1n, x2)), Nat.add(Nat.mul(x1, x2), Nat.add(x3, Nat.add(1n, x2))), Laws.nat_add_assoc(Nat.mul(x1, x2), x3, Nat.add(1n, x2))) : {Nat.add(x0, _) == Nat.add(x0, 1n+Nat.add(Nat.mul(1n+x1, x2), x3)) : Nat}
  %Equal.sym(Nat, Nat.add(x3, Nat.add(1n, x2)), Nat.add(1n, Nat.add(x3, x2)), Laws.nat_add_left_comm(x3, 1n, x2)) : {Nat.add(x0, Nat.add(Nat.mul(x1, x2), _)) == Nat.add(x0, 1n+Nat.add(Nat.mul(1n+x1, x2), x3)) : Nat}
  %Equal.sym(Nat, Nat.add(x3, x2), Nat.add(x2, x3), Laws.nat_add_comm(x3, x2)) : {Nat.add(x0, Nat.add(Nat.mul(x1, x2), Nat.add(1n, _))) == Nat.add(x0, 1n+Nat.add(Nat.mul(1n+x1, x2), x3)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x1, x2), Nat.add(1n, Nat.add(x2, x3))), Nat.add(1n, Nat.add(Nat.mul(x1, x2), Nat.add(x2, x3))), Laws.nat_add_left_comm(Nat.mul(x1, x2), 1n, Nat.add(x2, x3))) : {Nat.add(x0, _) == Nat.add(x0, 1n+Nat.add(Nat.mul(1n+x1, x2), x3)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(Nat.mul(x1, x2), Nat.add(x2, x3)))), Nat.add(1n, Nat.add(x0, Nat.add(Nat.mul(x1, x2), Nat.add(x2, x3)))), Laws.nat_add_left_comm(x0, 1n, Nat.add(Nat.mul(x1, x2), Nat.add(x2, x3)))) : {_ == Nat.add(x0, 1n+Nat.add(Nat.mul(1n+x1, x2), x3)) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x0, Nat.add(Nat.mul(x1, x2), Nat.add(x2, x3)))), Nat.add(x0, Nat.add(1n, Nat.add(Nat.mul(x1, x2), Nat.add(x2, x3)))), Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(Nat.mul(x1, x2), Nat.add(x2, x3)))), Nat.add(1n, Nat.add(x0, Nat.add(Nat.mul(x1, x2), Nat.add(x2, x3)))), Laws.nat_add_left_comm(x0, 1n, Nat.add(Nat.mul(x1, x2), Nat.add(x2, x3))))) : {_ == Nat.add(x0, 1n+Nat.add(Nat.mul(1n+x1, x2), x3)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x1, x2), Nat.add(x2, x3)), Nat.add(Nat.add(Nat.mul(x1, x2), x2), x3), Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(x1, x2), x2), x3), Nat.add(Nat.mul(x1, x2), Nat.add(x2, x3)), Laws.nat_add_assoc(Nat.mul(x1, x2), x2, x3))) : {Nat.add(x0, Nat.add(1n, _)) == Nat.add(x0, 1n+Nat.add(Nat.mul(1n+x1, x2), x3)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x1, x2), x2), Nat.add(x2, Nat.mul(x1, x2)), Equal.sym(Nat, Nat.add(x2, Nat.mul(x1, x2)), Nat.add(Nat.mul(x1, x2), x2), Laws.nat_add_comm(x2, Nat.mul(x1, x2)))) : {Nat.add(x0, Nat.add(1n, Nat.add(_, x3))) == Nat.add(x0, 1n+Nat.add(Nat.mul(1n+x1, x2), x3)) : Nat}
  %Equal.sym(Nat, x2, Nat.mul(1n, x2), Equal.sym(Nat, Nat.mul(1n, x2), x2, Laws.nat_one_mul(x2))) : {Nat.add(x0, Nat.add(1n, Nat.add(Nat.add(_, Nat.mul(x1, x2)), x3))) == Nat.add(x0, 1n+Nat.add(Nat.mul(1n+x1, x2), x3)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(1n, x2), Nat.mul(x1, x2)), Nat.mul(Nat.add(1n, x1), x2), Equal.sym(Nat, Nat.mul(Nat.add(1n, x1), x2), Nat.add(Nat.mul(1n, x2), Nat.mul(x1, x2)), Laws.nat_add_mul(1n, x1, x2))) : {Nat.add(x0, Nat.add(1n, Nat.add(_, x3))) == Nat.add(x0, 1n+Nat.add(Nat.mul(1n+x1, x2), x3)) : Nat}
  {==}

def ur.r1(+x0: Nat, +x1: Nat, +x2: Nat) -> {Nat.add(x0, Nat.add(Nat.mul(x1, x0), x2)) == Nat.add(Nat.mul(1n+x1, x0), x2) : Nat}:
  %Equal.sym(Nat, Nat.mul(x1, x0), Nat.mul(x0, x1), Laws.nat_mul_comm(x1, x0)) : {Nat.add(x0, Nat.add(_, x2)) == Nat.add(Nat.mul(1n+x1, x0), x2) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(Nat.mul(x0, x1), x2)), Nat.add(Nat.add(x0, Nat.mul(x0, x1)), x2), Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.mul(x0, x1)), x2), Nat.add(x0, Nat.add(Nat.mul(x0, x1), x2)), Laws.nat_add_assoc(x0, Nat.mul(x0, x1), x2))) : {_ == Nat.add(Nat.mul(1n+x1, x0), x2) : Nat}
  %Equal.sym(Nat, Nat.mul(x0, x1), Nat.mul(x1, x0), Equal.sym(Nat, Nat.mul(x1, x0), Nat.mul(x0, x1), Laws.nat_mul_comm(x1, x0))) : {Nat.add(Nat.add(x0, _), x2) == Nat.add(Nat.mul(1n+x1, x0), x2) : Nat}
  %Equal.sym(Nat, x0, Nat.mul(1n, x0), Equal.sym(Nat, Nat.mul(1n, x0), x0, Laws.nat_one_mul(x0))) : {Nat.add(Nat.add(_, Nat.mul(x1, x0)), x2) == Nat.add(Nat.mul(1n+x1, x0), x2) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(1n, x0), Nat.mul(x1, x0)), Nat.mul(Nat.add(1n, x1), x0), Equal.sym(Nat, Nat.mul(Nat.add(1n, x1), x0), Nat.add(Nat.mul(1n, x0), Nat.mul(x1, x0)), Laws.nat_add_mul(1n, x1, x0))) : {Nat.add(_, x2) == Nat.add(Nat.mul(1n+x1, x0), x2) : Nat}
  {==}

def ur.r2(+x0: Nat, +x1: Nat, +x2: Nat) -> {Nat.add(Nat.mul(1n+x0, x1), x2) == Nat.add(x1, Nat.add(Nat.mul(x0, x1), x2)) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.add(1n, x0), x1), Nat.add(Nat.mul(1n, x1), Nat.mul(x0, x1)), Laws.nat_add_mul(1n, x0, x1)) : {Nat.add(_, x2) == Nat.add(x1, Nat.add(Nat.mul(x0, x1), x2)) : Nat}
  %Equal.sym(Nat, Nat.mul(1n, x1), x1, Laws.nat_one_mul(x1)) : {Nat.add(Nat.add(_, Nat.mul(x0, x1)), x2) == Nat.add(x1, Nat.add(Nat.mul(x0, x1), x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.mul(x0, x1)), Nat.add(Nat.mul(x0, x1), x1), Laws.nat_add_comm(x1, Nat.mul(x0, x1))) : {Nat.add(_, x2) == Nat.add(x1, Nat.add(Nat.mul(x0, x1), x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(x0, x1), x1), x2), Nat.add(Nat.mul(x0, x1), Nat.add(x1, x2)), Laws.nat_add_assoc(Nat.mul(x0, x1), x1, x2)) : {_ == Nat.add(x1, Nat.add(Nat.mul(x0, x1), x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x1), Nat.add(x1, x2)), Nat.add(x1, Nat.add(Nat.mul(x0, x1), x2)), Equal.sym(Nat, Nat.add(x1, Nat.add(Nat.mul(x0, x1), x2)), Nat.add(Nat.mul(x0, x1), Nat.add(x1, x2)), Laws.nat_add_left_comm(x1, Nat.mul(x0, x1), x2))) : {_ == Nat.add(x1, Nat.add(Nat.mul(x0, x1), x2)) : Nat}
  {==}

def un.dmu.s(-s: Nat, -t: Nat, -r1: Nat, -r2: Nat, pr: {s == t : Nat} & {r1 == r2 : Nat}) -> {1n+s == 1n+t : Nat} & {r1 == r2 : Nat}:
  (a, c) = pr
  (un.succ_cong(s, t, a), c)

def un.dmu(+b: Nat, +q1: Nat, +r1: Nat, +q2: Nat, +r2: Nat, e: {Nat.add(Nat.mul(q1, b), r1) == Nat.add(Nat.mul(q2, b), r2) : Nat}, h1: {Nat.is_lt(r1, b) == True{} : Bool}, h2: {Nat.is_lt(r2, b) == True{} : Bool}) -> {q1 == q2 : Nat} & {r1 == r2 : Nat}:
  match q1 q2:
    case 0n 0n:
      ({==}, e)
    case 0n 1n+s:
      Empty.absurd({0n == 1n+s : Nat} & {r1 == r2 : Nat}, Laws.nat_succ_add_absurd(Nat.add(Nat.sub(b, 1n+r1), Nat.add(Nat.mul(s, b), r2)), b, Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(b, 1n+r1), Nat.add(Nat.mul(s, b), r2)), 1n+b), Nat.add(Nat.sub(b, 1n+r1), 1n+r1), b, Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(b, 1n+r1), Nat.add(Nat.mul(s, b), r2)), 1n+b), Nat.add(Nat.sub(b, 1n+r1), 1n+Nat.add(Nat.mul(0n, b), r1)), Nat.add(Nat.sub(b, 1n+r1), 1n+r1), Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(b, 1n+r1), Nat.add(Nat.mul(s, b), r2)), 1n+b), Nat.add(Nat.sub(b, 1n+r1), 1n+Nat.add(Nat.mul(1n+s, b), r2)), Nat.add(Nat.sub(b, 1n+r1), 1n+Nat.add(Nat.mul(0n, b), r1)), ur.r0(Nat.sub(b, 1n+r1), s, b, r2), Equal.cong(Nat, Nat, zz => Nat.add(Nat.sub(b, 1n+r1), 1n+zz), Nat.add(Nat.mul(1n+s, b), r2), Nat.add(Nat.mul(0n, b), r1), Equal.sym(Nat, Nat.add(Nat.mul(0n, b), r1), Nat.add(Nat.mul(1n+s, b), r2), e))), {==}), Laws.nat_lt_witness(r1, b, h1))))
    case 1n+s 1n+t:
      un.dmu.s(s, t, r1, r2, un.dmu(b, s, r1, t, r2, Laws.nat_add_cancel(b, Nat.add(Nat.mul(s, b), r1), Nat.add(Nat.mul(t, b), r2), Equal.trans(Nat, Nat.add(b, Nat.add(Nat.mul(s, b), r1)), Nat.add(Nat.mul(1n+t, b), r2), Nat.add(b, Nat.add(Nat.mul(t, b), r2)), Equal.trans(Nat, Nat.add(b, Nat.add(Nat.mul(s, b), r1)), Nat.add(Nat.mul(1n+s, b), r1), Nat.add(Nat.mul(1n+t, b), r2), ur.r1(b, s, r1), e), ur.r2(t, b, r2))), h1, h2))
    case 1n+s 0n:
      Empty.absurd({1n+s == 0n : Nat} & {r1 == r2 : Nat}, Laws.nat_succ_add_absurd(Nat.add(Nat.sub(b, 1n+r2), Nat.add(Nat.mul(s, b), r1)), b, Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(b, 1n+r2), Nat.add(Nat.mul(s, b), r1)), 1n+b), Nat.add(Nat.sub(b, 1n+r2), 1n+r2), b, Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(b, 1n+r2), Nat.add(Nat.mul(s, b), r1)), 1n+b), Nat.add(Nat.sub(b, 1n+r2), 1n+Nat.add(Nat.mul(0n, b), r2)), Nat.add(Nat.sub(b, 1n+r2), 1n+r2), Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(b, 1n+r2), Nat.add(Nat.mul(s, b), r1)), 1n+b), Nat.add(Nat.sub(b, 1n+r2), 1n+Nat.add(Nat.mul(1n+s, b), r1)), Nat.add(Nat.sub(b, 1n+r2), 1n+Nat.add(Nat.mul(0n, b), r2)), ur.r0(Nat.sub(b, 1n+r2), s, b, r1), Equal.cong(Nat, Nat, zz => Nat.add(Nat.sub(b, 1n+r2), 1n+zz), Nat.add(Nat.mul(1n+s, b), r1), Nat.add(Nat.mul(0n, b), r2), e)), {==}), Laws.nat_lt_witness(r2, b, h2))))

def un.dmu.q(-q1: Nat, -q2: Nat, -r1: Nat, -r2: Nat, pr: {q1 == q2 : Nat} & {r1 == r2 : Nat}) -> {q1 == q2 : Nat}:
  (a, c) = pr
  a

def un.dmu.r(-q1: Nat, -q2: Nat, -r1: Nat, -r2: Nat, pr: {q1 == q2 : Nat} & {r1 == r2 : Nat}) -> {r1 == r2 : Nat}:
  (a, c) = pr
  c

def Laws.nat_div_unique(b, q1, r1, q2, r2, e, h1, h2):
  un.dmu.q(q1, q2, r1, r2, un.dmu(b, q1, r1, q2, r2, e, h1, h2))

def Laws.nat_mod_unique(b, q1, r1, q2, r2, e, h1, h2):
  un.dmu.r(q1, q2, r1, r2, un.dmu(b, q1, r1, q2, r2, e, h1, h2))

def ur.r3(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat, +x4: Nat) -> {Nat.add(Nat.add(x0, Nat.add(x1, Nat.add(x2, U.U32Nat.dbl(x3, x4)))), 1n+U.U32Nat.dbl(x3, 1n)) == Nat.add(x0, 1n+Nat.add(x1, Nat.add(x2, U.U32Nat.dbl(x3, 1n+x4)))) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x1, Nat.add(x2, U.U32Nat.dbl(x3, x4)))), Nat.add(1n, U.U32Nat.dbl(x3, 1n))), Nat.add(x0, Nat.add(Nat.add(x1, Nat.add(x2, U.U32Nat.dbl(x3, x4))), Nat.add(1n, U.U32Nat.dbl(x3, 1n)))), Laws.nat_add_assoc(x0, Nat.add(x1, Nat.add(x2, U.U32Nat.dbl(x3, x4))), Nat.add(1n, U.U32Nat.dbl(x3, 1n)))) : {_ == Nat.add(x0, 1n+Nat.add(x1, Nat.add(x2, U.U32Nat.dbl(x3, 1n+x4)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x1, Nat.add(x2, U.U32Nat.dbl(x3, x4))), Nat.add(1n, U.U32Nat.dbl(x3, 1n))), Nat.add(x1, Nat.add(Nat.add(x2, U.U32Nat.dbl(x3, x4)), Nat.add(1n, U.U32Nat.dbl(x3, 1n)))), Laws.nat_add_assoc(x1, Nat.add(x2, U.U32Nat.dbl(x3, x4)), Nat.add(1n, U.U32Nat.dbl(x3, 1n)))) : {Nat.add(x0, _) == Nat.add(x0, 1n+Nat.add(x1, Nat.add(x2, U.U32Nat.dbl(x3, 1n+x4)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x2, U.U32Nat.dbl(x3, x4)), Nat.add(1n, U.U32Nat.dbl(x3, 1n))), Nat.add(x2, Nat.add(U.U32Nat.dbl(x3, x4), Nat.add(1n, U.U32Nat.dbl(x3, 1n)))), Laws.nat_add_assoc(x2, U.U32Nat.dbl(x3, x4), Nat.add(1n, U.U32Nat.dbl(x3, 1n)))) : {Nat.add(x0, Nat.add(x1, _)) == Nat.add(x0, 1n+Nat.add(x1, Nat.add(x2, U.U32Nat.dbl(x3, 1n+x4)))) : Nat}
  %Equal.sym(Nat, Nat.add(U.U32Nat.dbl(x3, x4), Nat.add(1n, U.U32Nat.dbl(x3, 1n))), Nat.add(1n, Nat.add(U.U32Nat.dbl(x3, x4), U.U32Nat.dbl(x3, 1n))), Laws.nat_add_left_comm(U.U32Nat.dbl(x3, x4), 1n, U.U32Nat.dbl(x3, 1n))) : {Nat.add(x0, Nat.add(x1, Nat.add(x2, _))) == Nat.add(x0, 1n+Nat.add(x1, Nat.add(x2, U.U32Nat.dbl(x3, 1n+x4)))) : Nat}
  %Equal.sym(Nat, Nat.add(U.U32Nat.dbl(x3, x4), U.U32Nat.dbl(x3, 1n)), Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4)), Laws.nat_add_comm(U.U32Nat.dbl(x3, x4), U.U32Nat.dbl(x3, 1n))) : {Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(1n, _)))) == Nat.add(x0, 1n+Nat.add(x1, Nat.add(x2, U.U32Nat.dbl(x3, 1n+x4)))) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(1n, Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4)))), Nat.add(1n, Nat.add(x2, Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4)))), Laws.nat_add_left_comm(x2, 1n, Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4)))) : {Nat.add(x0, Nat.add(x1, _)) == Nat.add(x0, 1n+Nat.add(x1, Nat.add(x2, U.U32Nat.dbl(x3, 1n+x4)))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(1n, Nat.add(x2, Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4))))), Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4))))), Laws.nat_add_left_comm(x1, 1n, Nat.add(x2, Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4))))) : {Nat.add(x0, _) == Nat.add(x0, 1n+Nat.add(x1, Nat.add(x2, U.U32Nat.dbl(x3, 1n+x4)))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4)))))), Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4)))))), Laws.nat_add_left_comm(x0, 1n, Nat.add(x1, Nat.add(x2, Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4)))))) : {_ == Nat.add(x0, 1n+Nat.add(x1, Nat.add(x2, U.U32Nat.dbl(x3, 1n+x4)))) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4)))))), Nat.add(x0, Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4)))))), Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4)))))), Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4)))))), Laws.nat_add_left_comm(x0, 1n, Nat.add(x1, Nat.add(x2, Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4))))))) : {_ == Nat.add(x0, 1n+Nat.add(x1, Nat.add(x2, U.U32Nat.dbl(x3, 1n+x4)))) : Nat}
  %Equal.sym(Nat, Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4)), U.U32Nat.dbl(x3, Nat.add(1n, x4)), Equal.sym(Nat, U.U32Nat.dbl(x3, Nat.add(1n, x4)), Nat.add(U.U32Nat.dbl(x3, 1n), U.U32Nat.dbl(x3, x4)), Laws.dbl_add(x3, 1n, x4))) : {Nat.add(x0, Nat.add(1n, Nat.add(x1, Nat.add(x2, _)))) == Nat.add(x0, 1n+Nat.add(x1, Nat.add(x2, U.U32Nat.dbl(x3, 1n+x4)))) : Nat}
  {==}

def Laws.dbl_nowrap(n, k, r, p, z, e, h, hz):
  match k:
    case 0n:
      Equal.trans(Nat, r, Nat.add(r, U.U32Nat.dbl(n, 0n)), p, Equal.trans(Nat, r, Nat.add(r, 0n), Nat.add(r, U.U32Nat.dbl(n, 0n)), Equal.sym(Nat, Nat.add(r, 0n), r, Laws.nat_add_zero(r)), Equal.cong(Nat, Nat, zz => Nat.add(r, zz), 0n, U.U32Nat.dbl(n, 0n), Equal.sym(Nat, U.U32Nat.dbl(n, 0n), 0n, Laws.dbl_zero(n)))), e)
    case 1n+j:
      Empty.absurd({r == p : Nat}, Laws.nat_succ_add_absurd(Nat.add(Nat.sub(U.U32Nat.dbl(n, 1n), 1n+z), Nat.add(Nat.sub(z, p), Nat.add(r, U.U32Nat.dbl(n, j)))), U.U32Nat.dbl(n, 1n), Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(U.U32Nat.dbl(n, 1n), 1n+z), Nat.add(Nat.sub(z, p), Nat.add(r, U.U32Nat.dbl(n, j)))), 1n+U.U32Nat.dbl(n, 1n)), Nat.add(Nat.sub(U.U32Nat.dbl(n, 1n), 1n+z), 1n+z), U.U32Nat.dbl(n, 1n), Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(U.U32Nat.dbl(n, 1n), 1n+z), Nat.add(Nat.sub(z, p), Nat.add(r, U.U32Nat.dbl(n, j)))), 1n+U.U32Nat.dbl(n, 1n)), Nat.add(Nat.sub(U.U32Nat.dbl(n, 1n), 1n+z), 1n+Nat.add(Nat.sub(z, p), p)), Nat.add(Nat.sub(U.U32Nat.dbl(n, 1n), 1n+z), 1n+z), Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(U.U32Nat.dbl(n, 1n), 1n+z), Nat.add(Nat.sub(z, p), Nat.add(r, U.U32Nat.dbl(n, j)))), 1n+U.U32Nat.dbl(n, 1n)), Nat.add(Nat.sub(U.U32Nat.dbl(n, 1n), 1n+z), 1n+Nat.add(Nat.sub(z, p), Nat.add(r, U.U32Nat.dbl(n, 1n+j)))), Nat.add(Nat.sub(U.U32Nat.dbl(n, 1n), 1n+z), 1n+Nat.add(Nat.sub(z, p), p)), ur.r3(Nat.sub(U.U32Nat.dbl(n, 1n), 1n+z), Nat.sub(z, p), r, n, j), Equal.cong(Nat, Nat, zz => Nat.add(Nat.sub(U.U32Nat.dbl(n, 1n), 1n+z), 1n+Nat.add(Nat.sub(z, p), zz)), Nat.add(r, U.U32Nat.dbl(n, 1n+j)), p, e)), Equal.cong(Nat, Nat, zz => Nat.add(Nat.sub(U.U32Nat.dbl(n, 1n), 1n+z), 1n+zz), Nat.add(Nat.sub(z, p), p), z, Laws.nat_le_witness(p, z, h))), Laws.nat_lt_witness(z, U.U32Nat.dbl(n, 1n), hz))))

# The low bits and the rest

def un.wc(-p: Nat, b: Bool, -t: Word(p)) -> {Word.to_nat(1n+p, WCon{b, t}) == Nat.add(U.U32Nat.bit(b), Nat.double(Word.to_nat(p, t))) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ur.r4(+x0: Nat, +x1: Nat) -> {Nat.add(x0, 2n+Nat.double(x1)) == 2n+Nat.add(x0, Nat.double(x1)) : Nat}:
  %Equal.sym(Nat, Nat.double(x1), Nat.add(x1, x1), Laws.nat_double(x1)) : {Nat.add(x0, Nat.add(1n, Nat.add(1n, _))) == 2n+Nat.add(x0, Nat.double(x1)) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(1n, Nat.add(x1, x1))), Nat.add(Nat.add(1n, 1n), Nat.add(x1, x1)), Equal.sym(Nat, Nat.add(Nat.add(1n, 1n), Nat.add(x1, x1)), Nat.add(1n, Nat.add(1n, Nat.add(x1, x1))), Laws.nat_add_assoc(1n, 1n, Nat.add(x1, x1)))) : {Nat.add(x0, _) == 2n+Nat.add(x0, Nat.double(x1)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(2n, Nat.add(x1, x1))), Nat.add(2n, Nat.add(x0, Nat.add(x1, x1))), Laws.nat_add_left_comm(x0, 2n, Nat.add(x1, x1))) : {_ == 2n+Nat.add(x0, Nat.double(x1)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(1n, 1n), Nat.add(x0, Nat.add(x1, x1))), Nat.add(1n, Nat.add(1n, Nat.add(x0, Nat.add(x1, x1)))), Equal.sym(Nat, Nat.add(1n, Nat.add(1n, Nat.add(x0, Nat.add(x1, x1)))), Nat.add(Nat.add(1n, 1n), Nat.add(x0, Nat.add(x1, x1))), Equal.sym(Nat, Nat.add(Nat.add(1n, 1n), Nat.add(x0, Nat.add(x1, x1))), Nat.add(1n, Nat.add(1n, Nat.add(x0, Nat.add(x1, x1)))), Laws.nat_add_assoc(1n, 1n, Nat.add(x0, Nat.add(x1, x1)))))) : {_ == 2n+Nat.add(x0, Nat.double(x1)) : Nat}
  %Equal.sym(Nat, Nat.add(x1, x1), Nat.double(x1), Equal.sym(Nat, Nat.double(x1), Nat.add(x1, x1), Laws.nat_double(x1))) : {Nat.add(1n, Nat.add(1n, Nat.add(x0, _))) == 2n+Nat.add(x0, Nat.double(x1)) : Nat}
  {==}

def Laws.nat_odd_half(x):
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      match p:
        case 0n:
          {==}
        case 1n+ +q:
          Equal.trans(Nat, Nat.add(U.U32Nat.odd(q), 2n+Nat.double(U.U32Nat.half(q))), 2n+Nat.add(U.U32Nat.odd(q), Nat.double(U.U32Nat.half(q))), 2n+q, ur.r4(U.U32Nat.odd(q), U.U32Nat.half(q)), Equal.cong(Nat, Nat, zz => 2n+zz, Nat.add(U.U32Nat.odd(q), Nat.double(U.U32Nat.half(q))), q, Laws.nat_odd_half(q)))

def Laws.nat_odd_le(x):
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      match p:
        case 0n:
          {==}
        case 1n+ +q:
          Laws.nat_odd_le(q)

def ur.r5(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat) -> {Nat.add(Nat.add(x0, Nat.double(x1)), Nat.double(U.U32Nat.dbl(x2, x3))) == Nat.add(x0, Nat.double(Nat.add(x1, U.U32Nat.dbl(x2, x3)))) : Nat}:
  %Equal.sym(Nat, Nat.double(x1), Nat.add(x1, x1), Laws.nat_double(x1)) : {Nat.add(Nat.add(x0, _), Nat.double(U.U32Nat.dbl(x2, x3))) == Nat.add(x0, Nat.double(Nat.add(x1, U.U32Nat.dbl(x2, x3)))) : Nat}
  %Equal.sym(Nat, Nat.double(U.U32Nat.dbl(x2, x3)), Nat.add(U.U32Nat.dbl(x2, x3), U.U32Nat.dbl(x2, x3)), Laws.nat_double(U.U32Nat.dbl(x2, x3))) : {Nat.add(Nat.add(x0, Nat.add(x1, x1)), _) == Nat.add(x0, Nat.double(Nat.add(x1, U.U32Nat.dbl(x2, x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x1, x1)), Nat.add(U.U32Nat.dbl(x2, x3), U.U32Nat.dbl(x2, x3))), Nat.add(x0, Nat.add(Nat.add(x1, x1), Nat.add(U.U32Nat.dbl(x2, x3), U.U32Nat.dbl(x2, x3)))), Laws.nat_add_assoc(x0, Nat.add(x1, x1), Nat.add(U.U32Nat.dbl(x2, x3), U.U32Nat.dbl(x2, x3)))) : {_ == Nat.add(x0, Nat.double(Nat.add(x1, U.U32Nat.dbl(x2, x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x1, x1), Nat.add(U.U32Nat.dbl(x2, x3), U.U32Nat.dbl(x2, x3))), Nat.add(x1, Nat.add(x1, Nat.add(U.U32Nat.dbl(x2, x3), U.U32Nat.dbl(x2, x3)))), Laws.nat_add_assoc(x1, x1, Nat.add(U.U32Nat.dbl(x2, x3), U.U32Nat.dbl(x2, x3)))) : {Nat.add(x0, _) == Nat.add(x0, Nat.double(Nat.add(x1, U.U32Nat.dbl(x2, x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(U.U32Nat.dbl(x2, x3), U.U32Nat.dbl(x2, x3))), Nat.add(U.U32Nat.dbl(x2, x3), Nat.add(x1, U.U32Nat.dbl(x2, x3))), Equal.sym(Nat, Nat.add(U.U32Nat.dbl(x2, x3), Nat.add(x1, U.U32Nat.dbl(x2, x3))), Nat.add(x1, Nat.add(U.U32Nat.dbl(x2, x3), U.U32Nat.dbl(x2, x3))), Laws.nat_add_left_comm(U.U32Nat.dbl(x2, x3), x1, U.U32Nat.dbl(x2, x3)))) : {Nat.add(x0, Nat.add(x1, _)) == Nat.add(x0, Nat.double(Nat.add(x1, U.U32Nat.dbl(x2, x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(U.U32Nat.dbl(x2, x3), Nat.add(x1, U.U32Nat.dbl(x2, x3)))), Nat.add(Nat.add(x1, U.U32Nat.dbl(x2, x3)), Nat.add(x1, U.U32Nat.dbl(x2, x3))), Equal.sym(Nat, Nat.add(Nat.add(x1, U.U32Nat.dbl(x2, x3)), Nat.add(x1, U.U32Nat.dbl(x2, x3))), Nat.add(x1, Nat.add(U.U32Nat.dbl(x2, x3), Nat.add(x1, U.U32Nat.dbl(x2, x3)))), Laws.nat_add_assoc(x1, U.U32Nat.dbl(x2, x3), Nat.add(x1, U.U32Nat.dbl(x2, x3))))) : {Nat.add(x0, _) == Nat.add(x0, Nat.double(Nat.add(x1, U.U32Nat.dbl(x2, x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x1, U.U32Nat.dbl(x2, x3)), Nat.add(x1, U.U32Nat.dbl(x2, x3))), Nat.double(Nat.add(x1, U.U32Nat.dbl(x2, x3))), Equal.sym(Nat, Nat.double(Nat.add(x1, U.U32Nat.dbl(x2, x3))), Nat.add(Nat.add(x1, U.U32Nat.dbl(x2, x3)), Nat.add(x1, U.U32Nat.dbl(x2, x3))), Laws.nat_double(Nat.add(x1, U.U32Nat.dbl(x2, x3))))) : {Nat.add(x0, _) == Nat.add(x0, Nat.double(Nat.add(x1, U.U32Nat.dbl(x2, x3)))) : Nat}
  {==}

def Laws.low_high(k, x):
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      Equal.trans(Nat, Nat.add(Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.low(j, U.U32Nat.half(x)))), Nat.double(U.U32Nat.dbl(j, U.U32Nat.high(j, U.U32Nat.half(x))))), Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.half(x))), x, Equal.trans(Nat, Nat.add(Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.low(j, U.U32Nat.half(x)))), Nat.double(U.U32Nat.dbl(j, U.U32Nat.high(j, U.U32Nat.half(x))))), Nat.add(U.U32Nat.odd(x), Nat.double(Nat.add(U.U32Nat.low(j, U.U32Nat.half(x)), U.U32Nat.dbl(j, U.U32Nat.high(j, U.U32Nat.half(x)))))), Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.half(x))), ur.r5(U.U32Nat.odd(x), U.U32Nat.low(j, U.U32Nat.half(x)), j, U.U32Nat.high(j, U.U32Nat.half(x))), Equal.cong(Nat, Nat, zz => Nat.add(U.U32Nat.odd(x), Nat.double(zz)), Nat.add(U.U32Nat.low(j, U.U32Nat.half(x)), U.U32Nat.dbl(j, U.U32Nat.high(j, U.U32Nat.half(x)))), U.U32Nat.half(x), Laws.low_high(j, U.U32Nat.half(x)))), Laws.nat_odd_half(x))

def ur.r6(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat) -> {Nat.add(Nat.add(Nat.double(x0), x1), 1n+Nat.add(x2, Nat.double(x3))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}:
  %Equal.sym(Nat, Nat.double(x0), Nat.add(x0, x0), Laws.nat_double(x0)) : {Nat.add(Nat.add(_, x1), 1n+Nat.add(x2, Nat.double(x3))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, x0), x1), Nat.add(x0, Nat.add(x0, x1)), Laws.nat_add_assoc(x0, x0, x1)) : {Nat.add(_, 1n+Nat.add(x2, Nat.double(x3))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.double(x3), Nat.add(x3, x3), Laws.nat_double(x3)) : {Nat.add(Nat.add(x0, Nat.add(x0, x1)), Nat.add(1n, Nat.add(x2, _))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x0, x1)), Nat.add(1n, Nat.add(x2, Nat.add(x3, x3)))), Nat.add(x0, Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(x2, Nat.add(x3, x3))))), Laws.nat_add_assoc(x0, Nat.add(x0, x1), Nat.add(1n, Nat.add(x2, Nat.add(x3, x3))))) : {_ == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(x2, Nat.add(x3, x3)))), Nat.add(x0, Nat.add(x1, Nat.add(1n, Nat.add(x2, Nat.add(x3, x3))))), Laws.nat_add_assoc(x0, x1, Nat.add(1n, Nat.add(x2, Nat.add(x3, x3))))) : {Nat.add(x0, _) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(1n, Nat.add(x2, Nat.add(x3, x3)))), Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(x3, x3)))), Laws.nat_add_left_comm(x1, 1n, Nat.add(x2, Nat.add(x3, x3)))) : {Nat.add(x0, Nat.add(x0, _)) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(x3, x3))))), Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x3, x3))))), Laws.nat_add_left_comm(x0, 1n, Nat.add(x1, Nat.add(x2, Nat.add(x3, x3))))) : {Nat.add(x0, _) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x3, x3)))))), Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x3, x3)))))), Laws.nat_add_left_comm(x0, 1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x3, x3)))))) : {_ == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(x3, x3)), Nat.add(x3, Nat.add(x2, x3)), Equal.sym(Nat, Nat.add(x3, Nat.add(x2, x3)), Nat.add(x2, Nat.add(x3, x3)), Laws.nat_add_left_comm(x3, x2, x3))) : {Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x1, _)))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x3, Nat.add(x2, x3))), Nat.add(x3, Nat.add(x1, Nat.add(x2, x3))), Equal.sym(Nat, Nat.add(x3, Nat.add(x1, Nat.add(x2, x3))), Nat.add(x1, Nat.add(x3, Nat.add(x2, x3))), Laws.nat_add_left_comm(x3, x1, Nat.add(x2, x3)))) : {Nat.add(1n, Nat.add(x0, Nat.add(x0, _))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x2, x3), Nat.add(x3, x2), Equal.sym(Nat, Nat.add(x3, x2), Nat.add(x2, x3), Laws.nat_add_comm(x3, x2))) : {Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x3, Nat.add(x1, _))))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x3, x2)), Nat.add(x3, Nat.add(x1, x2)), Equal.sym(Nat, Nat.add(x3, Nat.add(x1, x2)), Nat.add(x1, Nat.add(x3, x2)), Laws.nat_add_left_comm(x3, x1, x2))) : {Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x3, _)))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x3, Nat.add(x3, Nat.add(x1, x2))), Nat.add(Nat.add(x3, x3), Nat.add(x1, x2)), Equal.sym(Nat, Nat.add(Nat.add(x3, x3), Nat.add(x1, x2)), Nat.add(x3, Nat.add(x3, Nat.add(x1, x2))), Laws.nat_add_assoc(x3, x3, Nat.add(x1, x2)))) : {Nat.add(1n, Nat.add(x0, Nat.add(x0, _))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(Nat.add(x3, x3), Nat.add(x1, x2))), Nat.add(Nat.add(x0, Nat.add(x3, x3)), Nat.add(x1, x2)), Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x3, x3)), Nat.add(x1, x2)), Nat.add(x0, Nat.add(Nat.add(x3, x3), Nat.add(x1, x2))), Laws.nat_add_assoc(x0, Nat.add(x3, x3), Nat.add(x1, x2)))) : {Nat.add(1n, Nat.add(x0, _)) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(Nat.add(x0, Nat.add(x3, x3)), Nat.add(x1, x2))), Nat.add(Nat.add(x0, Nat.add(x0, Nat.add(x3, x3))), Nat.add(x1, x2)), Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x0, Nat.add(x3, x3))), Nat.add(x1, x2)), Nat.add(x0, Nat.add(Nat.add(x0, Nat.add(x3, x3)), Nat.add(x1, x2))), Laws.nat_add_assoc(x0, Nat.add(x0, Nat.add(x3, x3)), Nat.add(x1, x2)))) : {Nat.add(1n, _) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(Nat.add(x0, Nat.add(x0, Nat.add(x3, x3))), Nat.add(x1, x2))), Nat.add(Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x3, x3)))), Nat.add(x1, x2)), Equal.sym(Nat, Nat.add(Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x3, x3)))), Nat.add(x1, x2)), Nat.add(1n, Nat.add(Nat.add(x0, Nat.add(x0, Nat.add(x3, x3))), Nat.add(x1, x2))), Laws.nat_add_assoc(1n, Nat.add(x0, Nat.add(x0, Nat.add(x3, x3))), Nat.add(x1, x2)))) : {_ == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x3, x3)), Nat.add(x3, Nat.add(x0, x3)), Equal.sym(Nat, Nat.add(x3, Nat.add(x0, x3)), Nat.add(x0, Nat.add(x3, x3)), Laws.nat_add_left_comm(x3, x0, x3))) : {Nat.add(Nat.add(1n, Nat.add(x0, _)), Nat.add(x1, x2)) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x3, Nat.add(x0, x3))), Nat.add(Nat.add(x0, x3), Nat.add(x0, x3)), Equal.sym(Nat, Nat.add(Nat.add(x0, x3), Nat.add(x0, x3)), Nat.add(x0, Nat.add(x3, Nat.add(x0, x3))), Laws.nat_add_assoc(x0, x3, Nat.add(x0, x3)))) : {Nat.add(Nat.add(1n, _), Nat.add(x1, x2)) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, x3), Nat.add(x0, x3)), Nat.double(Nat.add(x0, x3)), Equal.sym(Nat, Nat.double(Nat.add(x0, x3)), Nat.add(Nat.add(x0, x3), Nat.add(x0, x3)), Laws.nat_double(Nat.add(x0, x3)))) : {Nat.add(Nat.add(1n, _), Nat.add(x1, x2)) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  {==}

def ur.r7(+x0: Nat, +x1: Nat) -> {Nat.add(1n+Nat.double(Nat.add(x0, x1)), 1n) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}:
  %Equal.sym(Nat, Nat.double(Nat.add(x0, x1)), Nat.add(Nat.add(x0, x1), Nat.add(x0, x1)), Laws.nat_double(Nat.add(x0, x1))) : {Nat.add(Nat.add(1n, _), 1n) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, x1), Nat.add(x0, x1)), Nat.add(x0, Nat.add(x1, Nat.add(x0, x1))), Laws.nat_add_assoc(x0, x1, Nat.add(x0, x1))) : {Nat.add(Nat.add(1n, _), 1n) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x0, x1)), Nat.add(x0, Nat.add(x1, x1)), Laws.nat_add_left_comm(x1, x0, x1)) : {Nat.add(Nat.add(1n, Nat.add(x0, _)), 1n) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x1, x1)))), 1n), Nat.add(1n, Nat.add(Nat.add(x0, Nat.add(x0, Nat.add(x1, x1))), 1n)), Laws.nat_add_assoc(1n, Nat.add(x0, Nat.add(x0, Nat.add(x1, x1))), 1n)) : {_ == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x0, Nat.add(x1, x1))), 1n), Nat.add(x0, Nat.add(Nat.add(x0, Nat.add(x1, x1)), 1n)), Laws.nat_add_assoc(x0, Nat.add(x0, Nat.add(x1, x1)), 1n)) : {Nat.add(1n, _) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x1, x1)), 1n), Nat.add(x0, Nat.add(Nat.add(x1, x1), 1n)), Laws.nat_add_assoc(x0, Nat.add(x1, x1), 1n)) : {Nat.add(1n, Nat.add(x0, _)) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x1, x1), 1n), Nat.add(x1, Nat.add(x1, 1n)), Laws.nat_add_assoc(x1, x1, 1n)) : {Nat.add(1n, Nat.add(x0, Nat.add(x0, _))) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(x1, 1n), Nat.add(1n, x1), Laws.nat_add_comm(x1, 1n)) : {Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x1, _)))) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(1n, x1)), Nat.add(1n, Nat.add(x1, x1)), Laws.nat_add_left_comm(x1, 1n, x1)) : {Nat.add(1n, Nat.add(x0, Nat.add(x0, _))) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(x1, x1))), Nat.add(1n, Nat.add(x0, Nat.add(x1, x1))), Laws.nat_add_left_comm(x0, 1n, Nat.add(x1, x1))) : {Nat.add(1n, Nat.add(x0, _)) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(x0, Nat.add(x1, x1)))), Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x1, x1)))), Laws.nat_add_left_comm(x0, 1n, Nat.add(x0, Nat.add(x1, x1)))) : {Nat.add(1n, _) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x1, x1))))), Nat.add(Nat.add(1n, 1n), Nat.add(x0, Nat.add(x0, Nat.add(x1, x1)))), Equal.sym(Nat, Nat.add(Nat.add(1n, 1n), Nat.add(x0, Nat.add(x0, Nat.add(x1, x1)))), Nat.add(1n, Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x1, x1))))), Laws.nat_add_assoc(1n, 1n, Nat.add(x0, Nat.add(x0, Nat.add(x1, x1)))))) : {_ == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(1n, 1n), Nat.add(x0, Nat.add(x0, Nat.add(x1, x1)))), Nat.add(1n, Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x1, x1))))), Equal.sym(Nat, Nat.add(1n, Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x1, x1))))), Nat.add(Nat.add(1n, 1n), Nat.add(x0, Nat.add(x0, Nat.add(x1, x1)))), Equal.sym(Nat, Nat.add(Nat.add(1n, 1n), Nat.add(x0, Nat.add(x0, Nat.add(x1, x1)))), Nat.add(1n, Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x1, x1))))), Laws.nat_add_assoc(1n, 1n, Nat.add(x0, Nat.add(x0, Nat.add(x1, x1))))))) : {_ == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x1, x1)))), Nat.add(x0, Nat.add(1n, Nat.add(x0, Nat.add(x1, x1)))), Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(x0, Nat.add(x1, x1)))), Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x1, x1)))), Laws.nat_add_left_comm(x0, 1n, Nat.add(x0, Nat.add(x1, x1))))) : {Nat.add(1n, _) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x1, x1)), Nat.add(x1, Nat.add(x0, x1)), Equal.sym(Nat, Nat.add(x1, Nat.add(x0, x1)), Nat.add(x0, Nat.add(x1, x1)), Laws.nat_add_left_comm(x1, x0, x1))) : {Nat.add(1n, Nat.add(x0, Nat.add(1n, _))) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x1, Nat.add(x0, x1))), Nat.add(x1, Nat.add(1n, Nat.add(x0, x1))), Equal.sym(Nat, Nat.add(x1, Nat.add(1n, Nat.add(x0, x1))), Nat.add(1n, Nat.add(x1, Nat.add(x0, x1))), Laws.nat_add_left_comm(x1, 1n, Nat.add(x0, x1)))) : {Nat.add(1n, Nat.add(x0, _)) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x1, Nat.add(1n, Nat.add(x0, x1)))), Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(x0, x1))), Equal.sym(Nat, Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(x0, x1))), Nat.add(x0, Nat.add(x1, Nat.add(1n, Nat.add(x0, x1)))), Laws.nat_add_assoc(x0, x1, Nat.add(1n, Nat.add(x0, x1))))) : {Nat.add(1n, _) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(x0, x1)))), Nat.add(Nat.add(1n, Nat.add(x0, x1)), Nat.add(1n, Nat.add(x0, x1))), Equal.sym(Nat, Nat.add(Nat.add(1n, Nat.add(x0, x1)), Nat.add(1n, Nat.add(x0, x1))), Nat.add(1n, Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(x0, x1)))), Laws.nat_add_assoc(1n, Nat.add(x0, x1), Nat.add(1n, Nat.add(x0, x1))))) : {_ == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x0, x1)), Nat.add(x0, Nat.add(1n, x1)), Equal.sym(Nat, Nat.add(x0, Nat.add(1n, x1)), Nat.add(1n, Nat.add(x0, x1)), Laws.nat_add_left_comm(x0, 1n, x1))) : {Nat.add(Nat.add(1n, Nat.add(x0, x1)), _) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x0, x1)), Nat.add(x0, Nat.add(1n, x1)), Equal.sym(Nat, Nat.add(x0, Nat.add(1n, x1)), Nat.add(1n, Nat.add(x0, x1)), Laws.nat_add_left_comm(x0, 1n, x1))) : {Nat.add(_, Nat.add(x0, 1n+x1)) == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, 1n+x1), Nat.add(x0, 1n+x1)), Nat.double(Nat.add(x0, 1n+x1)), Equal.sym(Nat, Nat.double(Nat.add(x0, 1n+x1)), Nat.add(Nat.add(x0, 1n+x1), Nat.add(x0, 1n+x1)), Laws.nat_double(Nat.add(x0, 1n+x1)))) : {_ == Nat.double(Nat.add(x0, 1n+x1)) : Nat}
  {==}

def Laws.low_lt(k, x):
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      Equal.trans(Bool, Nat.is_lt(Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.low(j, U.U32Nat.half(x)))), Nat.double(U.U32Nat.dbl(j, 1n))), Nat.is_lt(Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.low(j, U.U32Nat.half(x)))), Nat.add(Nat.add(Nat.double(Nat.sub(U.U32Nat.dbl(j, 1n), 1n+U.U32Nat.low(j, U.U32Nat.half(x)))), Nat.sub(1n, U.U32Nat.odd(x))), 1n+Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.low(j, U.U32Nat.half(x)))))), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.low(j, U.U32Nat.half(x)))), Nat.add(Nat.add(Nat.double(Nat.sub(U.U32Nat.dbl(j, 1n), 1n+U.U32Nat.low(j, U.U32Nat.half(x)))), Nat.sub(1n, U.U32Nat.odd(x))), 1n+Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.low(j, U.U32Nat.half(x)))))), Nat.is_lt(Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.low(j, U.U32Nat.half(x)))), Nat.double(U.U32Nat.dbl(j, 1n))), Equal.cong(Nat, Bool, zz => Nat.is_lt(Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.low(j, U.U32Nat.half(x)))), zz), Nat.add(Nat.add(Nat.double(Nat.sub(U.U32Nat.dbl(j, 1n), 1n+U.U32Nat.low(j, U.U32Nat.half(x)))), Nat.sub(1n, U.U32Nat.odd(x))), 1n+Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.low(j, U.U32Nat.half(x))))), Nat.double(U.U32Nat.dbl(j, 1n)), Equal.trans(Nat, Nat.add(Nat.add(Nat.double(Nat.sub(U.U32Nat.dbl(j, 1n), 1n+U.U32Nat.low(j, U.U32Nat.half(x)))), Nat.sub(1n, U.U32Nat.odd(x))), 1n+Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.low(j, U.U32Nat.half(x))))), Nat.double(Nat.add(Nat.sub(U.U32Nat.dbl(j, 1n), 1n+U.U32Nat.low(j, U.U32Nat.half(x))), 1n+U.U32Nat.low(j, U.U32Nat.half(x)))), Nat.double(U.U32Nat.dbl(j, 1n)), Equal.trans(Nat, Nat.add(Nat.add(Nat.double(Nat.sub(U.U32Nat.dbl(j, 1n), 1n+U.U32Nat.low(j, U.U32Nat.half(x)))), Nat.sub(1n, U.U32Nat.odd(x))), 1n+Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.low(j, U.U32Nat.half(x))))), Nat.add(1n+Nat.double(Nat.add(Nat.sub(U.U32Nat.dbl(j, 1n), 1n+U.U32Nat.low(j, U.U32Nat.half(x))), U.U32Nat.low(j, U.U32Nat.half(x)))), 1n), Nat.double(Nat.add(Nat.sub(U.U32Nat.dbl(j, 1n), 1n+U.U32Nat.low(j, U.U32Nat.half(x))), 1n+U.U32Nat.low(j, U.U32Nat.half(x)))), Equal.trans(Nat, Nat.add(Nat.add(Nat.double(Nat.sub(U.U32Nat.dbl(j, 1n), 1n+U.U32Nat.low(j, U.U32Nat.half(x)))), Nat.sub(1n, U.U32Nat.odd(x))), 1n+Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.low(j, U.U32Nat.half(x))))), Nat.add(1n+Nat.double(Nat.add(Nat.sub(U.U32Nat.dbl(j, 1n), 1n+U.U32Nat.low(j, U.U32Nat.half(x))), U.U32Nat.low(j, U.U32Nat.half(x)))), Nat.add(Nat.sub(1n, U.U32Nat.odd(x)), U.U32Nat.odd(x))), Nat.add(1n+Nat.double(Nat.add(Nat.sub(U.U32Nat.dbl(j, 1n), 1n+U.U32Nat.low(j, U.U32Nat.half(x))), U.U32Nat.low(j, U.U32Nat.half(x)))), 1n), ur.r6(Nat.sub(U.U32Nat.dbl(j, 1n), 1n+U.U32Nat.low(j, U.U32Nat.half(x))), Nat.sub(1n, U.U32Nat.odd(x)), U.U32Nat.odd(x), U.U32Nat.low(j, U.U32Nat.half(x))), Equal.cong(Nat, Nat, zz => Nat.add(1n+Nat.double(Nat.add(Nat.sub(U.U32Nat.dbl(j, 1n), 1n+U.U32Nat.low(j, U.U32Nat.half(x))), U.U32Nat.low(j, U.U32Nat.half(x)))), zz), Nat.add(Nat.sub(1n, U.U32Nat.odd(x)), U.U32Nat.odd(x)), 1n, Laws.nat_le_witness(U.U32Nat.odd(x), 1n, Laws.nat_odd_le(x)))), ur.r7(Nat.sub(U.U32Nat.dbl(j, 1n), 1n+U.U32Nat.low(j, U.U32Nat.half(x))), U.U32Nat.low(j, U.U32Nat.half(x)))), Equal.cong(Nat, Nat, zz => Nat.double(zz), Nat.add(Nat.sub(U.U32Nat.dbl(j, 1n), 1n+U.U32Nat.low(j, U.U32Nat.half(x))), 1n+U.U32Nat.low(j, U.U32Nat.half(x))), U.U32Nat.dbl(j, 1n), Laws.nat_lt_witness(U.U32Nat.low(j, U.U32Nat.half(x)), U.U32Nat.dbl(j, 1n), Laws.low_lt(j, U.U32Nat.half(x))))))), Laws.nat_lt_add(Nat.add(U.U32Nat.odd(x), Nat.double(U.U32Nat.low(j, U.U32Nat.half(x)))), Nat.add(Nat.double(Nat.sub(U.U32Nat.dbl(j, 1n), 1n+U.U32Nat.low(j, U.U32Nat.half(x)))), Nat.sub(1n, U.U32Nat.odd(x)))))

def ur.r8(+x0: Nat, +x1: Nat, +x2: Nat) -> {Nat.add(Nat.mul(x0, U.U32Nat.dbl(x1, 1n)), x2) == Nat.add(x2, U.U32Nat.dbl(x1, x0)) : Nat}:
  %Equal.sym(Nat, Nat.mul(x0, U.U32Nat.dbl(x1, 1n)), U.U32Nat.dbl(x1, Nat.mul(x0, 1n)), Laws.dbl_mul_r(x1, x0, 1n)) : {Nat.add(_, x2) == Nat.add(x2, U.U32Nat.dbl(x1, x0)) : Nat}
  %Equal.sym(Nat, Nat.mul(x0, 1n), Nat.mul(1n, x0), Laws.nat_mul_comm(x0, 1n)) : {Nat.add(U.U32Nat.dbl(x1, _), x2) == Nat.add(x2, U.U32Nat.dbl(x1, x0)) : Nat}
  %Equal.sym(Nat, Nat.mul(1n, x0), x0, Laws.nat_one_mul(x0)) : {Nat.add(U.U32Nat.dbl(x1, _), x2) == Nat.add(x2, U.U32Nat.dbl(x1, x0)) : Nat}
  %Equal.sym(Nat, Nat.add(U.U32Nat.dbl(x1, x0), x2), Nat.add(x2, U.U32Nat.dbl(x1, x0)), Laws.nat_add_comm(U.U32Nat.dbl(x1, x0), x2)) : {_ == Nat.add(x2, U.U32Nat.dbl(x1, x0)) : Nat}
  {==}

def ur.r9(+x0: Nat, +x1: Nat, +x2: Nat) -> {Nat.add(x0, U.U32Nat.dbl(x1, x2)) == Nat.add(Nat.mul(x2, U.U32Nat.dbl(x1, 1n)), x0) : Nat}:
  %Equal.sym(Nat, Nat.add(x0, U.U32Nat.dbl(x1, x2)), Nat.add(U.U32Nat.dbl(x1, x2), x0), Equal.sym(Nat, Nat.add(U.U32Nat.dbl(x1, x2), x0), Nat.add(x0, U.U32Nat.dbl(x1, x2)), Laws.nat_add_comm(U.U32Nat.dbl(x1, x2), x0))) : {_ == Nat.add(Nat.mul(x2, U.U32Nat.dbl(x1, 1n)), x0) : Nat}
  %Equal.sym(Nat, x2, Nat.mul(1n, x2), Equal.sym(Nat, Nat.mul(1n, x2), x2, Laws.nat_one_mul(x2))) : {Nat.add(U.U32Nat.dbl(x1, _), x0) == Nat.add(Nat.mul(x2, U.U32Nat.dbl(x1, 1n)), x0) : Nat}
  %Equal.sym(Nat, Nat.mul(1n, x2), Nat.mul(x2, 1n), Equal.sym(Nat, Nat.mul(x2, 1n), Nat.mul(1n, x2), Laws.nat_mul_comm(x2, 1n))) : {Nat.add(U.U32Nat.dbl(x1, _), x0) == Nat.add(Nat.mul(x2, U.U32Nat.dbl(x1, 1n)), x0) : Nat}
  %Equal.sym(Nat, U.U32Nat.dbl(x1, Nat.mul(x2, 1n)), Nat.mul(x2, U.U32Nat.dbl(x1, 1n)), Equal.sym(Nat, Nat.mul(x2, U.U32Nat.dbl(x1, 1n)), U.U32Nat.dbl(x1, Nat.mul(x2, 1n)), Laws.dbl_mul_r(x1, x2, 1n))) : {Nat.add(_, x0) == Nat.add(Nat.mul(x2, U.U32Nat.dbl(x1, 1n)), x0) : Nat}
  {==}

def Laws.low_unique(k, x, r, q, e, h):
  Laws.nat_mod_unique(U.U32Nat.dbl(k, 1n), q, r, U.U32Nat.high(k, x), U.U32Nat.low(k, x), Equal.trans(Nat, Nat.add(Nat.mul(q, U.U32Nat.dbl(k, 1n)), r), Nat.add(U.U32Nat.low(k, x), U.U32Nat.dbl(k, U.U32Nat.high(k, x))), Nat.add(Nat.mul(U.U32Nat.high(k, x), U.U32Nat.dbl(k, 1n)), U.U32Nat.low(k, x)), Equal.trans(Nat, Nat.add(Nat.mul(q, U.U32Nat.dbl(k, 1n)), r), x, Nat.add(U.U32Nat.low(k, x), U.U32Nat.dbl(k, U.U32Nat.high(k, x))), Equal.trans(Nat, Nat.add(Nat.mul(q, U.U32Nat.dbl(k, 1n)), r), Nat.add(r, U.U32Nat.dbl(k, q)), x, ur.r8(q, k, r), e), Equal.sym(Nat, Nat.add(U.U32Nat.low(k, x), U.U32Nat.dbl(k, U.U32Nat.high(k, x))), x, Laws.low_high(k, x))), ur.r9(U.U32Nat.low(k, x), k, U.U32Nat.high(k, x))), h, Laws.low_lt(k, x))

def Laws.high_unique(k, x, r, q, e, h):
  Laws.nat_div_unique(U.U32Nat.dbl(k, 1n), q, r, U.U32Nat.high(k, x), U.U32Nat.low(k, x), Equal.trans(Nat, Nat.add(Nat.mul(q, U.U32Nat.dbl(k, 1n)), r), Nat.add(U.U32Nat.low(k, x), U.U32Nat.dbl(k, U.U32Nat.high(k, x))), Nat.add(Nat.mul(U.U32Nat.high(k, x), U.U32Nat.dbl(k, 1n)), U.U32Nat.low(k, x)), Equal.trans(Nat, Nat.add(Nat.mul(q, U.U32Nat.dbl(k, 1n)), r), x, Nat.add(U.U32Nat.low(k, x), U.U32Nat.dbl(k, U.U32Nat.high(k, x))), Equal.trans(Nat, Nat.add(Nat.mul(q, U.U32Nat.dbl(k, 1n)), r), Nat.add(r, U.U32Nat.dbl(k, q)), x, ur.r8(q, k, r), e), Equal.sym(Nat, Nat.add(U.U32Nat.low(k, x), U.U32Nat.dbl(k, U.U32Nat.high(k, x))), x, Laws.low_high(k, x))), ur.r9(U.U32Nat.low(k, x), k, U.U32Nat.high(k, x))), h, Laws.low_lt(k, x))

def ur.r10(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat) -> {Nat.add(x0, U.U32Nat.dbl(x1, Nat.add(x2, x3))) == Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), U.U32Nat.dbl(x1, x3)) : Nat}:
  %Equal.sym(Nat, U.U32Nat.dbl(x1, Nat.add(x2, x3)), Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, x3)), Laws.dbl_add(x1, x2, x3)) : {Nat.add(x0, _) == Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), U.U32Nat.dbl(x1, x3)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, x3))), Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), U.U32Nat.dbl(x1, x3)), Equal.sym(Nat, Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), U.U32Nat.dbl(x1, x3)), Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, x3))), Laws.nat_add_assoc(x0, U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, x3)))) : {_ == Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), U.U32Nat.dbl(x1, x3)) : Nat}
  {==}

def Laws.low_add_dbl(k, x, q):
  Equal.sym(Nat, U.U32Nat.low(k, x), U.U32Nat.low(k, Nat.add(x, U.U32Nat.dbl(k, q))), Laws.low_unique(k, Nat.add(x, U.U32Nat.dbl(k, q)), U.U32Nat.low(k, x), Nat.add(U.U32Nat.high(k, x), q), Equal.trans(Nat, Nat.add(U.U32Nat.low(k, x), U.U32Nat.dbl(k, Nat.add(U.U32Nat.high(k, x), q))), Nat.add(Nat.add(U.U32Nat.low(k, x), U.U32Nat.dbl(k, U.U32Nat.high(k, x))), U.U32Nat.dbl(k, q)), Nat.add(x, U.U32Nat.dbl(k, q)), ur.r10(U.U32Nat.low(k, x), k, U.U32Nat.high(k, x), q), Equal.cong(Nat, Nat, zz => Nat.add(zz, U.U32Nat.dbl(k, q)), Nat.add(U.U32Nat.low(k, x), U.U32Nat.dbl(k, U.U32Nat.high(k, x))), x, Laws.low_high(k, x))), Laws.low_lt(k, x)))

def ur.r11(+x0: Nat, +x1: Nat) -> {Nat.add(x0, U.U32Nat.dbl(x1, 0n)) == x0 : Nat}:
  %Equal.sym(Nat, U.U32Nat.dbl(x1, 0n), 0n, Laws.dbl_zero(x1)) : {Nat.add(x0, _) == x0 : Nat}
  %Equal.sym(Nat, Nat.add(x0, 0n), x0, Laws.nat_add_zero(x0)) : {_ == x0 : Nat}
  {==}

def Laws.low_small(k, x, h):
  Equal.sym(Nat, x, U.U32Nat.low(k, x), Laws.low_unique(k, x, x, 0n, ur.r11(x, k), h))

def un.low_zero(k: Nat) -> {U.U32Nat.low(k, 0n) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      un.double_cong(U.U32Nat.low(j, 0n), 0n, un.low_zero(j))

# high(k, x / 2) = high(k, x) / 2
def un.high_half(k: Nat, +x: Nat) -> {U.U32Nat.high(k, U.U32Nat.half(x)) == U.U32Nat.half(U.U32Nat.high(k, x)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      un.high_half(j, U.U32Nat.half(x))

def ur.r12(+x0: Nat, +x1: Nat, +x2: Nat) -> {Nat.add(Nat.double(x0), U.U32Nat.dbl(x1, Nat.double(x2))) == Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))) : Nat}:
  %Equal.sym(Nat, Nat.double(x0), Nat.add(x0, x0), Laws.nat_double(x0)) : {Nat.add(_, U.U32Nat.dbl(x1, Nat.double(x2))) == Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))) : Nat}
  %Equal.sym(Nat, Nat.double(x2), Nat.add(x2, x2), Laws.nat_double(x2)) : {Nat.add(Nat.add(x0, x0), U.U32Nat.dbl(x1, _)) == Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))) : Nat}
  %Equal.sym(Nat, U.U32Nat.dbl(x1, Nat.add(x2, x2)), Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, x2)), Laws.dbl_add(x1, x2, x2)) : {Nat.add(Nat.add(x0, x0), _) == Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, x0), Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, x2))), Nat.add(x0, Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, x2)))), Laws.nat_add_assoc(x0, x0, Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, x2)))) : {_ == Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, x2))), Nat.add(U.U32Nat.dbl(x1, x2), Nat.add(x0, U.U32Nat.dbl(x1, x2))), Equal.sym(Nat, Nat.add(U.U32Nat.dbl(x1, x2), Nat.add(x0, U.U32Nat.dbl(x1, x2))), Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, x2))), Laws.nat_add_left_comm(U.U32Nat.dbl(x1, x2), x0, U.U32Nat.dbl(x1, x2)))) : {Nat.add(x0, _) == Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), Nat.add(x0, U.U32Nat.dbl(x1, x2)))), Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), Nat.add(x0, U.U32Nat.dbl(x1, x2))), Equal.sym(Nat, Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), Nat.add(x0, U.U32Nat.dbl(x1, x2))), Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), Nat.add(x0, U.U32Nat.dbl(x1, x2)))), Laws.nat_add_assoc(x0, U.U32Nat.dbl(x1, x2), Nat.add(x0, U.U32Nat.dbl(x1, x2))))) : {_ == Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), Nat.add(x0, U.U32Nat.dbl(x1, x2))), Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))), Equal.sym(Nat, Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))), Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), Nat.add(x0, U.U32Nat.dbl(x1, x2))), Laws.nat_double(Nat.add(x0, U.U32Nat.dbl(x1, x2))))) : {_ == Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))) : Nat}
  {==}

def un.low_double_low(+n: Nat, +y: Nat) -> {U.U32Nat.low(n, Nat.double(U.U32Nat.low(n, y))) == U.U32Nat.low(n, Nat.double(y)) : Nat}:
  Equal.trans(Nat, U.U32Nat.low(n, Nat.double(U.U32Nat.low(n, y))), U.U32Nat.low(n, Nat.add(Nat.double(U.U32Nat.low(n, y)), U.U32Nat.dbl(n, Nat.double(U.U32Nat.high(n, y))))), U.U32Nat.low(n, Nat.double(y)), Equal.sym(Nat, U.U32Nat.low(n, Nat.add(Nat.double(U.U32Nat.low(n, y)), U.U32Nat.dbl(n, Nat.double(U.U32Nat.high(n, y))))), U.U32Nat.low(n, Nat.double(U.U32Nat.low(n, y))), Laws.low_add_dbl(n, Nat.double(U.U32Nat.low(n, y)), Nat.double(U.U32Nat.high(n, y)))), Equal.cong(Nat, Nat, zz => U.U32Nat.low(n, zz), Nat.add(Nat.double(U.U32Nat.low(n, y)), U.U32Nat.dbl(n, Nat.double(U.U32Nat.high(n, y)))), Nat.double(y), Equal.trans(Nat, Nat.add(Nat.double(U.U32Nat.low(n, y)), U.U32Nat.dbl(n, Nat.double(U.U32Nat.high(n, y)))), Nat.double(Nat.add(U.U32Nat.low(n, y), U.U32Nat.dbl(n, U.U32Nat.high(n, y)))), Nat.double(y), ur.r12(U.U32Nat.low(n, y), n, U.U32Nat.high(n, y)), Equal.cong(Nat, Nat, zz => Nat.double(zz), Nat.add(U.U32Nat.low(n, y), U.U32Nat.dbl(n, U.U32Nat.high(n, y))), y, Laws.low_high(n, y)))))

def un.odd_d(v: Nat) -> {U.U32Nat.odd(Nat.double(v)) == 0n : Nat}:
  match v:
    case 0n:
      {==}
    case 1n+ +p:
      un.odd_d(p)

def un.odd_d1(v: Nat) -> {U.U32Nat.odd(1n+Nat.double(v)) == 1n : Nat}:
  match v:
    case 0n:
      {==}
    case 1n+ +p:
      un.odd_d1(p)

def un.odd_bd(b: Bool, +v: Nat) -> {U.U32Nat.odd(Nat.add(U.U32Nat.bit(b), Nat.double(v))) == U.U32Nat.bit(b) : Nat}:
  match b:
    case True{}:
      un.odd_d1(v)
    case False{}:
      un.odd_d(v)

def un.half_bd(b: Bool, +v: Nat) -> {U.U32Nat.half(Nat.add(U.U32Nat.bit(b), Nat.double(v))) == v : Nat}:
  match b:
    case True{}:
      Laws.half_double_one(v)
    case False{}:
      Laws.half_double(v)

# Products: Word.mul is shift and add, one bit of a at a time

def un.topc(n: Nat, c: Bool, w: Word(n)) -> Bool:
  match n:
    case 0n:
      c
    case 1n+ +p:
      match w:
        case WCon{b, t}:
          un.topc(p, b, t)

def un.top(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+ +p:
      match w:
        case WCon{b, t}:
          un.topc(p, b, t)

# a shift left by one bit, c coming in: twice the value plus c, less 2^n for
# the bit going out
def un.putv(n: Nat, +c: Bool, +w: Word(n)) -> {Nat.add(Word.to_nat(n, Word.shl.put(n, c, w)), U.U32Nat.dbl(n, U.U32Nat.bit(un.topc(n, c, w)))) == Nat.add(U.U32Nat.bit(c), Nat.double(Word.to_nat(n, w))) : Nat}:
  match n:
    case 0n:
      Equal.sym(Nat, Nat.add(U.U32Nat.bit(c), 0n), U.U32Nat.bit(c), Laws.nat_add_zero(U.U32Nat.bit(c)))
    case 1n+ +p:
      match w:
        case WCon{+x, +t}:
          Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{c, Word.shl.put(p, x, t)}), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(un.topc(p, x, t))))), Nat.add(U.U32Nat.bit(c), Nat.double(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, t))))), Nat.add(U.U32Nat.bit(c), Nat.double(Word.to_nat(1n+p, WCon{x, t}))), Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{c, Word.shl.put(p, x, t)}), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(un.topc(p, x, t))))), Nat.add(U.U32Nat.bit(c), Nat.double(Nat.add(Word.to_nat(p, Word.shl.put(p, x, t)), U.U32Nat.dbl(p, U.U32Nat.bit(un.topc(p, x, t)))))), Nat.add(U.U32Nat.bit(c), Nat.double(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, t))))), Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{c, Word.shl.put(p, x, t)}), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(un.topc(p, x, t))))), Nat.add(Nat.add(U.U32Nat.bit(c), Nat.double(Word.to_nat(p, Word.shl.put(p, x, t)))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(un.topc(p, x, t))))), Nat.add(U.U32Nat.bit(c), Nat.double(Nat.add(Word.to_nat(p, Word.shl.put(p, x, t)), U.U32Nat.dbl(p, U.U32Nat.bit(un.topc(p, x, t)))))), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(un.topc(p, x, t))))), Word.to_nat(1n+p, WCon{c, Word.shl.put(p, x, t)}), Nat.add(U.U32Nat.bit(c), Nat.double(Word.to_nat(p, Word.shl.put(p, x, t)))), un.wc(p, c, Word.shl.put(p, x, t))), ur.r5(U.U32Nat.bit(c), Word.to_nat(p, Word.shl.put(p, x, t)), p, U.U32Nat.bit(un.topc(p, x, t)))), Equal.cong(Nat, Nat, zz => Nat.add(U.U32Nat.bit(c), Nat.double(zz)), Nat.add(Word.to_nat(p, Word.shl.put(p, x, t)), U.U32Nat.dbl(p, U.U32Nat.bit(un.topc(p, x, t)))), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, t))), un.putv(p, x, t))), Equal.cong(Nat, Nat, zz => Nat.add(U.U32Nat.bit(c), Nat.double(zz)), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, t))), Word.to_nat(1n+p, WCon{x, t}), Equal.sym(Nat, Word.to_nat(1n+p, WCon{x, t}), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, t))), un.wc(p, x, t))))

def ur.r13(+x0: Nat, +x1: Nat, +x2: Nat) -> {Nat.add(Nat.double(x0), Nat.double(U.U32Nat.dbl(x1, x2))) == Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))) : Nat}:
  %Equal.sym(Nat, Nat.double(x0), Nat.add(x0, x0), Laws.nat_double(x0)) : {Nat.add(_, Nat.double(U.U32Nat.dbl(x1, x2))) == Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))) : Nat}
  %Equal.sym(Nat, Nat.double(U.U32Nat.dbl(x1, x2)), Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, x2)), Laws.nat_double(U.U32Nat.dbl(x1, x2))) : {Nat.add(Nat.add(x0, x0), _) == Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, x0), Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, x2))), Nat.add(x0, Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, x2)))), Laws.nat_add_assoc(x0, x0, Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, x2)))) : {_ == Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, x2))), Nat.add(U.U32Nat.dbl(x1, x2), Nat.add(x0, U.U32Nat.dbl(x1, x2))), Equal.sym(Nat, Nat.add(U.U32Nat.dbl(x1, x2), Nat.add(x0, U.U32Nat.dbl(x1, x2))), Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, x2))), Laws.nat_add_left_comm(U.U32Nat.dbl(x1, x2), x0, U.U32Nat.dbl(x1, x2)))) : {Nat.add(x0, _) == Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), Nat.add(x0, U.U32Nat.dbl(x1, x2)))), Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), Nat.add(x0, U.U32Nat.dbl(x1, x2))), Equal.sym(Nat, Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), Nat.add(x0, U.U32Nat.dbl(x1, x2))), Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), Nat.add(x0, U.U32Nat.dbl(x1, x2)))), Laws.nat_add_assoc(x0, U.U32Nat.dbl(x1, x2), Nat.add(x0, U.U32Nat.dbl(x1, x2))))) : {_ == Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), Nat.add(x0, U.U32Nat.dbl(x1, x2))), Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))), Equal.sym(Nat, Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))), Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), Nat.add(x0, U.U32Nat.dbl(x1, x2))), Laws.nat_double(Nat.add(x0, U.U32Nat.dbl(x1, x2))))) : {_ == Nat.double(Nat.add(x0, U.U32Nat.dbl(x1, x2))) : Nat}
  {==}

def un.shlv(n: Nat, +w: Word(n)) -> {Nat.add(Word.to_nat(n, Word.shl(n, w)), U.U32Nat.dbl(n, U.U32Nat.bit(un.top(n, w)))) == Nat.double(Word.to_nat(n, w)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{+x, +t}:
          Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(p, Word.shl.put(p, x, t))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(un.topc(p, x, t))))), Nat.double(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, t)))), Nat.double(Word.to_nat(1n+p, WCon{x, t})), Equal.trans(Nat, Nat.add(Nat.double(Word.to_nat(p, Word.shl.put(p, x, t))), Nat.double(U.U32Nat.dbl(p, U.U32Nat.bit(un.topc(p, x, t))))), Nat.double(Nat.add(Word.to_nat(p, Word.shl.put(p, x, t)), U.U32Nat.dbl(p, U.U32Nat.bit(un.topc(p, x, t))))), Nat.double(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, t)))), ur.r13(Word.to_nat(p, Word.shl.put(p, x, t)), p, U.U32Nat.bit(un.topc(p, x, t))), Equal.cong(Nat, Nat, zz => Nat.double(zz), Nat.add(Word.to_nat(p, Word.shl.put(p, x, t)), U.U32Nat.dbl(p, U.U32Nat.bit(un.topc(p, x, t)))), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, t))), un.putv(p, x, t))), Equal.cong(Nat, Nat, zz => Nat.double(zz), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, t))), Word.to_nat(1n+p, WCon{x, t}), Equal.sym(Nat, Word.to_nat(1n+p, WCon{x, t}), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, t))), un.wc(p, x, t))))

def un.shl_low(+n: Nat, +w: Word(n)) -> {Word.to_nat(n, Word.shl(n, w)) == U.U32Nat.low(n, Nat.double(Word.to_nat(n, w))) : Nat}:
  Laws.low_unique(n, Nat.double(Word.to_nat(n, w)), Word.to_nat(n, Word.shl(n, w)), U.U32Nat.bit(un.top(n, w)), un.shlv(n, w), Laws.word_value_lt(n, Word.shl(n, w)))

def um.k(+n: Nat, m: Nat, a: Word(m), +b: Word(n), +acc: Word(n)) -> Nat:
  match m:
    case 0n:
      0n
    case 1n+ +mp:
      match a:
        case WCon{False{}, +at}:
          Nat.add(um.k(n, mp, at, Word.shl(n, b), acc), Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b))))
        case WCon{True{}, +at}:
          Nat.add(um.k(n, mp, at, Word.shl(n, b), Word.add(n, acc, b)), Nat.add(U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, acc, b), acc))), Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b)))))

def ur.r14(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat, +x4: Nat) -> {Nat.add(x0, U.U32Nat.dbl(x1, Nat.add(x2, Nat.mul(x3, x4)))) == Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), U.U32Nat.dbl(x1, Nat.mul(x3, x4))) : Nat}:
  %Equal.sym(Nat, U.U32Nat.dbl(x1, Nat.add(x2, Nat.mul(x3, x4))), Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, Nat.mul(x3, x4))), Laws.dbl_add(x1, x2, Nat.mul(x3, x4))) : {Nat.add(x0, _) == Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), U.U32Nat.dbl(x1, Nat.mul(x3, x4))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, Nat.mul(x3, x4)))), Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), U.U32Nat.dbl(x1, Nat.mul(x3, x4))), Equal.sym(Nat, Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), U.U32Nat.dbl(x1, Nat.mul(x3, x4))), Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, Nat.mul(x3, x4)))), Laws.nat_add_assoc(x0, U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, Nat.mul(x3, x4))))) : {_ == Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), U.U32Nat.dbl(x1, Nat.mul(x3, x4))) : Nat}
  {==}

def ur.r15(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat, +x4: Nat) -> {Nat.add(Nat.add(x0, Nat.mul(x1, x2)), U.U32Nat.dbl(x3, Nat.mul(x1, x4))) == Nat.add(x0, Nat.mul(x1, Nat.add(x2, U.U32Nat.dbl(x3, x4)))) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.mul(x1, x2)), U.U32Nat.dbl(x3, Nat.mul(x1, x4))), Nat.add(x0, Nat.add(Nat.mul(x1, x2), U.U32Nat.dbl(x3, Nat.mul(x1, x4)))), Laws.nat_add_assoc(x0, Nat.mul(x1, x2), U.U32Nat.dbl(x3, Nat.mul(x1, x4)))) : {_ == Nat.add(x0, Nat.mul(x1, Nat.add(x2, U.U32Nat.dbl(x3, x4)))) : Nat}
  %Equal.sym(Nat, U.U32Nat.dbl(x3, Nat.mul(x1, x4)), Nat.mul(x1, U.U32Nat.dbl(x3, x4)), Equal.sym(Nat, Nat.mul(x1, U.U32Nat.dbl(x3, x4)), U.U32Nat.dbl(x3, Nat.mul(x1, x4)), Laws.dbl_mul_r(x3, x1, x4))) : {Nat.add(x0, Nat.add(Nat.mul(x1, x2), _)) == Nat.add(x0, Nat.mul(x1, Nat.add(x2, U.U32Nat.dbl(x3, x4)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x1, x2), Nat.mul(x1, U.U32Nat.dbl(x3, x4))), Nat.mul(x1, Nat.add(x2, U.U32Nat.dbl(x3, x4))), Equal.sym(Nat, Nat.mul(x1, Nat.add(x2, U.U32Nat.dbl(x3, x4))), Nat.add(Nat.mul(x1, x2), Nat.mul(x1, U.U32Nat.dbl(x3, x4))), Laws.nat_mul_add(x1, x2, U.U32Nat.dbl(x3, x4)))) : {Nat.add(x0, _) == Nat.add(x0, Nat.mul(x1, Nat.add(x2, U.U32Nat.dbl(x3, x4)))) : Nat}
  {==}

def ur.r16(+x0: Nat, +x1: Nat) -> {Nat.mul(x0, Nat.double(x1)) == Nat.mul(Nat.double(x0), x1) : Nat}:
  %Equal.sym(Nat, Nat.double(x1), Nat.add(x1, x1), Laws.nat_double(x1)) : {Nat.mul(x0, _) == Nat.mul(Nat.double(x0), x1) : Nat}
  %Equal.sym(Nat, Nat.mul(x0, Nat.add(x1, x1)), Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1)), Laws.nat_mul_add(x0, x1, x1)) : {_ == Nat.mul(Nat.double(x0), x1) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1)), Nat.mul(Nat.add(x0, x0), x1), Equal.sym(Nat, Nat.mul(Nat.add(x0, x0), x1), Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1)), Laws.nat_add_mul(x0, x0, x1))) : {_ == Nat.mul(Nat.double(x0), x1) : Nat}
  %Equal.sym(Nat, Nat.add(x0, x0), Nat.double(x0), Equal.sym(Nat, Nat.double(x0), Nat.add(x0, x0), Laws.nat_double(x0))) : {Nat.mul(_, x1) == Nat.mul(Nat.double(x0), x1) : Nat}
  {==}

def ur.r17(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat, +x4: Nat, +x5: Nat) -> {Nat.add(x0, U.U32Nat.dbl(x1, Nat.add(x2, Nat.add(x3, Nat.mul(x4, x5))))) == Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), Nat.add(U.U32Nat.dbl(x1, x3), U.U32Nat.dbl(x1, Nat.mul(x4, x5)))) : Nat}:
  %Equal.sym(Nat, U.U32Nat.dbl(x1, Nat.add(x2, Nat.add(x3, Nat.mul(x4, x5)))), Nat.add(U.U32Nat.dbl(x1, x2), U.U32Nat.dbl(x1, Nat.add(x3, Nat.mul(x4, x5)))), Laws.dbl_add(x1, x2, Nat.add(x3, Nat.mul(x4, x5)))) : {Nat.add(x0, _) == Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), Nat.add(U.U32Nat.dbl(x1, x3), U.U32Nat.dbl(x1, Nat.mul(x4, x5)))) : Nat}
  %Equal.sym(Nat, U.U32Nat.dbl(x1, Nat.add(x3, Nat.mul(x4, x5))), Nat.add(U.U32Nat.dbl(x1, x3), U.U32Nat.dbl(x1, Nat.mul(x4, x5))), Laws.dbl_add(x1, x3, Nat.mul(x4, x5))) : {Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), _)) == Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), Nat.add(U.U32Nat.dbl(x1, x3), U.U32Nat.dbl(x1, Nat.mul(x4, x5)))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), Nat.add(U.U32Nat.dbl(x1, x3), U.U32Nat.dbl(x1, Nat.mul(x4, x5))))), Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), Nat.add(U.U32Nat.dbl(x1, x3), U.U32Nat.dbl(x1, Nat.mul(x4, x5)))), Equal.sym(Nat, Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), Nat.add(U.U32Nat.dbl(x1, x3), U.U32Nat.dbl(x1, Nat.mul(x4, x5)))), Nat.add(x0, Nat.add(U.U32Nat.dbl(x1, x2), Nat.add(U.U32Nat.dbl(x1, x3), U.U32Nat.dbl(x1, Nat.mul(x4, x5))))), Laws.nat_add_assoc(x0, U.U32Nat.dbl(x1, x2), Nat.add(U.U32Nat.dbl(x1, x3), U.U32Nat.dbl(x1, Nat.mul(x4, x5)))))) : {_ == Nat.add(Nat.add(x0, U.U32Nat.dbl(x1, x2)), Nat.add(U.U32Nat.dbl(x1, x3), U.U32Nat.dbl(x1, Nat.mul(x4, x5)))) : Nat}
  {==}

def ur.r18(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat, +x4: Nat, +x5: Nat) -> {Nat.add(Nat.add(x0, Nat.mul(x1, x2)), Nat.add(U.U32Nat.dbl(x3, x4), U.U32Nat.dbl(x3, Nat.mul(x1, x5)))) == Nat.add(Nat.add(x0, U.U32Nat.dbl(x3, x4)), Nat.mul(x1, Nat.add(x2, U.U32Nat.dbl(x3, x5)))) : Nat}:
  %Equal.sym(Nat, Nat.add(U.U32Nat.dbl(x3, x4), U.U32Nat.dbl(x3, Nat.mul(x1, x5))), Nat.add(U.U32Nat.dbl(x3, Nat.mul(x1, x5)), U.U32Nat.dbl(x3, x4)), Laws.nat_add_comm(U.U32Nat.dbl(x3, x4), U.U32Nat.dbl(x3, Nat.mul(x1, x5)))) : {Nat.add(Nat.add(x0, Nat.mul(x1, x2)), _) == Nat.add(Nat.add(x0, U.U32Nat.dbl(x3, x4)), Nat.mul(x1, Nat.add(x2, U.U32Nat.dbl(x3, x5)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.mul(x1, x2)), Nat.add(U.U32Nat.dbl(x3, Nat.mul(x1, x5)), U.U32Nat.dbl(x3, x4))), Nat.add(x0, Nat.add(Nat.mul(x1, x2), Nat.add(U.U32Nat.dbl(x3, Nat.mul(x1, x5)), U.U32Nat.dbl(x3, x4)))), Laws.nat_add_assoc(x0, Nat.mul(x1, x2), Nat.add(U.U32Nat.dbl(x3, Nat.mul(x1, x5)), U.U32Nat.dbl(x3, x4)))) : {_ == Nat.add(Nat.add(x0, U.U32Nat.dbl(x3, x4)), Nat.mul(x1, Nat.add(x2, U.U32Nat.dbl(x3, x5)))) : Nat}
  %Equal.sym(Nat, Nat.add(U.U32Nat.dbl(x3, Nat.mul(x1, x5)), U.U32Nat.dbl(x3, x4)), Nat.add(U.U32Nat.dbl(x3, x4), U.U32Nat.dbl(x3, Nat.mul(x1, x5))), Equal.sym(Nat, Nat.add(U.U32Nat.dbl(x3, x4), U.U32Nat.dbl(x3, Nat.mul(x1, x5))), Nat.add(U.U32Nat.dbl(x3, Nat.mul(x1, x5)), U.U32Nat.dbl(x3, x4)), Laws.nat_add_comm(U.U32Nat.dbl(x3, x4), U.U32Nat.dbl(x3, Nat.mul(x1, x5))))) : {Nat.add(x0, Nat.add(Nat.mul(x1, x2), _)) == Nat.add(Nat.add(x0, U.U32Nat.dbl(x3, x4)), Nat.mul(x1, Nat.add(x2, U.U32Nat.dbl(x3, x5)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x1, x2), Nat.add(U.U32Nat.dbl(x3, x4), U.U32Nat.dbl(x3, Nat.mul(x1, x5)))), Nat.add(U.U32Nat.dbl(x3, x4), Nat.add(Nat.mul(x1, x2), U.U32Nat.dbl(x3, Nat.mul(x1, x5)))), Equal.sym(Nat, Nat.add(U.U32Nat.dbl(x3, x4), Nat.add(Nat.mul(x1, x2), U.U32Nat.dbl(x3, Nat.mul(x1, x5)))), Nat.add(Nat.mul(x1, x2), Nat.add(U.U32Nat.dbl(x3, x4), U.U32Nat.dbl(x3, Nat.mul(x1, x5)))), Laws.nat_add_left_comm(U.U32Nat.dbl(x3, x4), Nat.mul(x1, x2), U.U32Nat.dbl(x3, Nat.mul(x1, x5))))) : {Nat.add(x0, _) == Nat.add(Nat.add(x0, U.U32Nat.dbl(x3, x4)), Nat.mul(x1, Nat.add(x2, U.U32Nat.dbl(x3, x5)))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(U.U32Nat.dbl(x3, x4), Nat.add(Nat.mul(x1, x2), U.U32Nat.dbl(x3, Nat.mul(x1, x5))))), Nat.add(Nat.add(x0, U.U32Nat.dbl(x3, x4)), Nat.add(Nat.mul(x1, x2), U.U32Nat.dbl(x3, Nat.mul(x1, x5)))), Equal.sym(Nat, Nat.add(Nat.add(x0, U.U32Nat.dbl(x3, x4)), Nat.add(Nat.mul(x1, x2), U.U32Nat.dbl(x3, Nat.mul(x1, x5)))), Nat.add(x0, Nat.add(U.U32Nat.dbl(x3, x4), Nat.add(Nat.mul(x1, x2), U.U32Nat.dbl(x3, Nat.mul(x1, x5))))), Laws.nat_add_assoc(x0, U.U32Nat.dbl(x3, x4), Nat.add(Nat.mul(x1, x2), U.U32Nat.dbl(x3, Nat.mul(x1, x5)))))) : {_ == Nat.add(Nat.add(x0, U.U32Nat.dbl(x3, x4)), Nat.mul(x1, Nat.add(x2, U.U32Nat.dbl(x3, x5)))) : Nat}
  %Equal.sym(Nat, U.U32Nat.dbl(x3, Nat.mul(x1, x5)), Nat.mul(x1, U.U32Nat.dbl(x3, x5)), Equal.sym(Nat, Nat.mul(x1, U.U32Nat.dbl(x3, x5)), U.U32Nat.dbl(x3, Nat.mul(x1, x5)), Laws.dbl_mul_r(x3, x1, x5))) : {Nat.add(Nat.add(x0, U.U32Nat.dbl(x3, x4)), Nat.add(Nat.mul(x1, x2), _)) == Nat.add(Nat.add(x0, U.U32Nat.dbl(x3, x4)), Nat.mul(x1, Nat.add(x2, U.U32Nat.dbl(x3, x5)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x1, x2), Nat.mul(x1, U.U32Nat.dbl(x3, x5))), Nat.mul(x1, Nat.add(x2, U.U32Nat.dbl(x3, x5))), Equal.sym(Nat, Nat.mul(x1, Nat.add(x2, U.U32Nat.dbl(x3, x5))), Nat.add(Nat.mul(x1, x2), Nat.mul(x1, U.U32Nat.dbl(x3, x5))), Laws.nat_mul_add(x1, x2, U.U32Nat.dbl(x3, x5)))) : {Nat.add(Nat.add(x0, U.U32Nat.dbl(x3, x4)), _) == Nat.add(Nat.add(x0, U.U32Nat.dbl(x3, x4)), Nat.mul(x1, Nat.add(x2, U.U32Nat.dbl(x3, x5)))) : Nat}
  {==}

def ur.r19(+x0: Nat, +x1: Nat, +x2: Nat) -> {Nat.add(Nat.add(x0, x1), Nat.mul(x2, Nat.double(x1))) == Nat.add(x0, Nat.mul(1n+Nat.double(x2), x1)) : Nat}:
  %Equal.sym(Nat, Nat.double(x1), Nat.add(x1, x1), Laws.nat_double(x1)) : {Nat.add(Nat.add(x0, x1), Nat.mul(x2, _)) == Nat.add(x0, Nat.mul(1n+Nat.double(x2), x1)) : Nat}
  %Equal.sym(Nat, Nat.mul(x2, Nat.add(x1, x1)), Nat.add(Nat.mul(x2, x1), Nat.mul(x2, x1)), Laws.nat_mul_add(x2, x1, x1)) : {Nat.add(Nat.add(x0, x1), _) == Nat.add(x0, Nat.mul(1n+Nat.double(x2), x1)) : Nat}
  %Equal.sym(Nat, Nat.mul(x2, x1), Nat.mul(x1, x2), Laws.nat_mul_comm(x2, x1)) : {Nat.add(Nat.add(x0, x1), Nat.add(_, Nat.mul(x2, x1))) == Nat.add(x0, Nat.mul(1n+Nat.double(x2), x1)) : Nat}
  %Equal.sym(Nat, Nat.mul(x2, x1), Nat.mul(x1, x2), Laws.nat_mul_comm(x2, x1)) : {Nat.add(Nat.add(x0, x1), Nat.add(Nat.mul(x1, x2), _)) == Nat.add(x0, Nat.mul(1n+Nat.double(x2), x1)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, x1), Nat.add(Nat.mul(x1, x2), Nat.mul(x1, x2))), Nat.add(x0, Nat.add(x1, Nat.add(Nat.mul(x1, x2), Nat.mul(x1, x2)))), Laws.nat_add_assoc(x0, x1, Nat.add(Nat.mul(x1, x2), Nat.mul(x1, x2)))) : {_ == Nat.add(x0, Nat.mul(1n+Nat.double(x2), x1)) : Nat}
  %Equal.sym(Nat, Nat.mul(x1, x2), Nat.mul(x2, x1), Equal.sym(Nat, Nat.mul(x2, x1), Nat.mul(x1, x2), Laws.nat_mul_comm(x2, x1))) : {Nat.add(x0, Nat.add(x1, Nat.add(Nat.mul(x1, x2), _))) == Nat.add(x0, Nat.mul(1n+Nat.double(x2), x1)) : Nat}
  %Equal.sym(Nat, Nat.mul(x1, x2), Nat.mul(x2, x1), Equal.sym(Nat, Nat.mul(x2, x1), Nat.mul(x1, x2), Laws.nat_mul_comm(x2, x1))) : {Nat.add(x0, Nat.add(x1, Nat.add(_, Nat.mul(x2, x1)))) == Nat.add(x0, Nat.mul(1n+Nat.double(x2), x1)) : Nat}
  %Equal.sym(Nat, x1, Nat.mul(1n, x1), Equal.sym(Nat, Nat.mul(1n, x1), x1, Laws.nat_one_mul(x1))) : {Nat.add(x0, Nat.add(_, Nat.add(Nat.mul(x2, x1), Nat.mul(x2, x1)))) == Nat.add(x0, Nat.mul(1n+Nat.double(x2), x1)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x2, x1), Nat.mul(x2, x1)), Nat.mul(Nat.add(x2, x2), x1), Equal.sym(Nat, Nat.mul(Nat.add(x2, x2), x1), Nat.add(Nat.mul(x2, x1), Nat.mul(x2, x1)), Laws.nat_add_mul(x2, x2, x1))) : {Nat.add(x0, Nat.add(Nat.mul(1n, x1), _)) == Nat.add(x0, Nat.mul(1n+Nat.double(x2), x1)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(1n, x1), Nat.mul(Nat.add(x2, x2), x1)), Nat.mul(Nat.add(1n, Nat.add(x2, x2)), x1), Equal.sym(Nat, Nat.mul(Nat.add(1n, Nat.add(x2, x2)), x1), Nat.add(Nat.mul(1n, x1), Nat.mul(Nat.add(x2, x2), x1)), Laws.nat_add_mul(1n, Nat.add(x2, x2), x1))) : {Nat.add(x0, _) == Nat.add(x0, Nat.mul(1n+Nat.double(x2), x1)) : Nat}
  %Equal.sym(Nat, Nat.add(x2, x2), Nat.double(x2), Equal.sym(Nat, Nat.double(x2), Nat.add(x2, x2), Laws.nat_double(x2))) : {Nat.add(x0, Nat.mul(Nat.add(1n, _), x1)) == Nat.add(x0, Nat.mul(1n+Nat.double(x2), x1)) : Nat}
  {==}

def ur.r20(+x0: Nat, +x1: Nat, +x2: Nat) -> {Nat.add(x0, U.U32Nat.dbl(x1, 0n)) == Nat.add(x0, Nat.mul(0n, x2)) : Nat}:
  %Equal.sym(Nat, U.U32Nat.dbl(x1, 0n), 0n, Laws.dbl_zero(x1)) : {Nat.add(x0, _) == Nat.add(x0, Nat.mul(0n, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, 0n), x0, Laws.nat_add_zero(x0)) : {_ == Nat.add(x0, Nat.mul(0n, x2)) : Nat}
  %Equal.sym(Nat, x0, Nat.add(x0, 0n), Equal.sym(Nat, Nat.add(x0, 0n), x0, Laws.nat_add_zero(x0))) : {_ == Nat.add(x0, Nat.mul(0n, x2)) : Nat}
  {==}

def um.go(+n: Nat, m: Nat, a: Word(m), +b: Word(n), +acc: Word(n)) -> {Nat.add(Word.to_nat(n, Word.mul.go(n, m, a, b, acc)), U.U32Nat.dbl(n, um.k(n, m, a, b, acc))) == Nat.add(Word.to_nat(n, acc), Nat.mul(Word.to_nat(m, a), Word.to_nat(n, b))) : Nat}:
  match m:
    case 0n:
      ur.r20(Word.to_nat(n, acc), n, Word.to_nat(n, b))
    case 1n+ +mp:
      match a:
        case WCon{False{}, +at}:
          Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), acc)), U.U32Nat.dbl(n, Nat.add(um.k(n, mp, at, Word.shl(n, b), acc), Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b)))))), Nat.add(Word.to_nat(n, acc), Nat.mul(Word.to_nat(mp, at), Nat.double(Word.to_nat(n, b)))), Nat.add(Word.to_nat(n, acc), Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(n, b))), Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), acc)), U.U32Nat.dbl(n, Nat.add(um.k(n, mp, at, Word.shl(n, b), acc), Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b)))))), Nat.add(Word.to_nat(n, acc), Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(n, Word.shl(n, b)), U.U32Nat.dbl(n, U.U32Nat.bit(un.top(n, b)))))), Nat.add(Word.to_nat(n, acc), Nat.mul(Word.to_nat(mp, at), Nat.double(Word.to_nat(n, b)))), Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), acc)), U.U32Nat.dbl(n, Nat.add(um.k(n, mp, at, Word.shl(n, b), acc), Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b)))))), Nat.add(Nat.add(Word.to_nat(n, acc), Nat.mul(Word.to_nat(mp, at), Word.to_nat(n, Word.shl(n, b)))), U.U32Nat.dbl(n, Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b))))), Nat.add(Word.to_nat(n, acc), Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(n, Word.shl(n, b)), U.U32Nat.dbl(n, U.U32Nat.bit(un.top(n, b)))))), Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), acc)), U.U32Nat.dbl(n, Nat.add(um.k(n, mp, at, Word.shl(n, b), acc), Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b)))))), Nat.add(Nat.add(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), acc)), U.U32Nat.dbl(n, um.k(n, mp, at, Word.shl(n, b), acc))), U.U32Nat.dbl(n, Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b))))), Nat.add(Nat.add(Word.to_nat(n, acc), Nat.mul(Word.to_nat(mp, at), Word.to_nat(n, Word.shl(n, b)))), U.U32Nat.dbl(n, Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b))))), ur.r14(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), acc)), n, um.k(n, mp, at, Word.shl(n, b), acc), Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b))), Equal.cong(Nat, Nat, zz => Nat.add(zz, U.U32Nat.dbl(n, Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b))))), Nat.add(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), acc)), U.U32Nat.dbl(n, um.k(n, mp, at, Word.shl(n, b), acc))), Nat.add(Word.to_nat(n, acc), Nat.mul(Word.to_nat(mp, at), Word.to_nat(n, Word.shl(n, b)))), um.go(n, mp, at, Word.shl(n, b), acc))), ur.r15(Word.to_nat(n, acc), Word.to_nat(mp, at), Word.to_nat(n, Word.shl(n, b)), n, U.U32Nat.bit(un.top(n, b)))), Equal.cong(Nat, Nat, zz => Nat.add(Word.to_nat(n, acc), Nat.mul(Word.to_nat(mp, at), zz)), Nat.add(Word.to_nat(n, Word.shl(n, b)), U.U32Nat.dbl(n, U.U32Nat.bit(un.top(n, b)))), Nat.double(Word.to_nat(n, b)), un.shlv(n, b))), Equal.cong(Nat, Nat, zz => Nat.add(Word.to_nat(n, acc), zz), Nat.mul(Word.to_nat(mp, at), Nat.double(Word.to_nat(n, b))), Nat.mul(Nat.double(Word.to_nat(mp, at)), Word.to_nat(n, b)), ur.r16(Word.to_nat(mp, at), Word.to_nat(n, b))))
        case WCon{True{}, +at}:
          Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), Word.add(n, acc, b))), U.U32Nat.dbl(n, Nat.add(um.k(n, mp, at, Word.shl(n, b), Word.add(n, acc, b)), Nat.add(U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, acc, b), acc))), Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b))))))), Nat.add(Nat.add(Word.to_nat(n, acc), Word.to_nat(n, b)), Nat.mul(Word.to_nat(mp, at), Nat.double(Word.to_nat(n, b)))), Nat.add(Word.to_nat(n, acc), Nat.mul(1n+Nat.double(Word.to_nat(mp, at)), Word.to_nat(n, b))), Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), Word.add(n, acc, b))), U.U32Nat.dbl(n, Nat.add(um.k(n, mp, at, Word.shl(n, b), Word.add(n, acc, b)), Nat.add(U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, acc, b), acc))), Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b))))))), Nat.add(Nat.add(Word.to_nat(n, acc), Word.to_nat(n, b)), Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(n, Word.shl(n, b)), U.U32Nat.dbl(n, U.U32Nat.bit(un.top(n, b)))))), Nat.add(Nat.add(Word.to_nat(n, acc), Word.to_nat(n, b)), Nat.mul(Word.to_nat(mp, at), Nat.double(Word.to_nat(n, b)))), Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), Word.add(n, acc, b))), U.U32Nat.dbl(n, Nat.add(um.k(n, mp, at, Word.shl(n, b), Word.add(n, acc, b)), Nat.add(U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, acc, b), acc))), Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b))))))), Nat.add(Nat.add(Word.to_nat(n, Word.add(n, acc, b)), U.U32Nat.dbl(n, U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, acc, b), acc))))), Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(n, Word.shl(n, b)), U.U32Nat.dbl(n, U.U32Nat.bit(un.top(n, b)))))), Nat.add(Nat.add(Word.to_nat(n, acc), Word.to_nat(n, b)), Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(n, Word.shl(n, b)), U.U32Nat.dbl(n, U.U32Nat.bit(un.top(n, b)))))), Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), Word.add(n, acc, b))), U.U32Nat.dbl(n, Nat.add(um.k(n, mp, at, Word.shl(n, b), Word.add(n, acc, b)), Nat.add(U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, acc, b), acc))), Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b))))))), Nat.add(Nat.add(Word.to_nat(n, Word.add(n, acc, b)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(n, Word.shl(n, b)))), Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, acc, b), acc)))), U.U32Nat.dbl(n, Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b)))))), Nat.add(Nat.add(Word.to_nat(n, Word.add(n, acc, b)), U.U32Nat.dbl(n, U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, acc, b), acc))))), Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(n, Word.shl(n, b)), U.U32Nat.dbl(n, U.U32Nat.bit(un.top(n, b)))))), Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), Word.add(n, acc, b))), U.U32Nat.dbl(n, Nat.add(um.k(n, mp, at, Word.shl(n, b), Word.add(n, acc, b)), Nat.add(U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, acc, b), acc))), Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b))))))), Nat.add(Nat.add(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), Word.add(n, acc, b))), U.U32Nat.dbl(n, um.k(n, mp, at, Word.shl(n, b), Word.add(n, acc, b)))), Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, acc, b), acc)))), U.U32Nat.dbl(n, Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b)))))), Nat.add(Nat.add(Word.to_nat(n, Word.add(n, acc, b)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(n, Word.shl(n, b)))), Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, acc, b), acc)))), U.U32Nat.dbl(n, Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b)))))), ur.r17(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), Word.add(n, acc, b))), n, um.k(n, mp, at, Word.shl(n, b), Word.add(n, acc, b)), U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, acc, b), acc))), Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b))), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, acc, b), acc)))), U.U32Nat.dbl(n, Nat.mul(Word.to_nat(mp, at), U.U32Nat.bit(un.top(n, b)))))), Nat.add(Word.to_nat(n, Word.mul.go(n, mp, at, Word.shl(n, b), Word.add(n, acc, b))), U.U32Nat.dbl(n, um.k(n, mp, at, Word.shl(n, b), Word.add(n, acc, b)))), Nat.add(Word.to_nat(n, Word.add(n, acc, b)), Nat.mul(Word.to_nat(mp, at), Word.to_nat(n, Word.shl(n, b)))), um.go(n, mp, at, Word.shl(n, b), Word.add(n, acc, b)))), ur.r18(Word.to_nat(n, Word.add(n, acc, b)), Word.to_nat(mp, at), Word.to_nat(n, Word.shl(n, b)), n, U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, acc, b), acc))), U.U32Nat.bit(un.top(n, b)))), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.mul(Word.to_nat(mp, at), Nat.add(Word.to_nat(n, Word.shl(n, b)), U.U32Nat.dbl(n, U.U32Nat.bit(un.top(n, b)))))), Nat.add(Word.to_nat(n, Word.add(n, acc, b)), U.U32Nat.dbl(n, U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, acc, b), acc))))), Nat.add(Word.to_nat(n, acc), Word.to_nat(n, b)), Laws.word_add_wrap(n, acc, b))), Equal.cong(Nat, Nat, zz => Nat.add(Nat.add(Word.to_nat(n, acc), Word.to_nat(n, b)), Nat.mul(Word.to_nat(mp, at), zz)), Nat.add(Word.to_nat(n, Word.shl(n, b)), U.U32Nat.dbl(n, U.U32Nat.bit(un.top(n, b)))), Nat.double(Word.to_nat(n, b)), un.shlv(n, b))), ur.r19(Word.to_nat(n, acc), Word.to_nat(n, b), Word.to_nat(mp, at)))

def um.e(+n: Nat, +a: Word(n), +b: Word(n)) -> {Nat.add(Word.to_nat(n, Word.mul(n, a, b)), U.U32Nat.dbl(n, um.k(n, n, a, b, Word.zero(n)))) == Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b)) : Nat}:
  Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.mul(n, a, b)), U.U32Nat.dbl(n, um.k(n, n, a, b, Word.zero(n)))), Nat.add(0n, Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b))), Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b)), Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.mul(n, a, b)), U.U32Nat.dbl(n, um.k(n, n, a, b, Word.zero(n)))), Nat.add(Word.to_nat(n, Word.zero(n)), Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b))), Nat.add(0n, Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b))), um.go(n, n, a, b, Word.zero(n)), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b))), Word.to_nat(n, Word.zero(n)), 0n, Laws.word_zero_value(n))), {==})

def Laws.word_mul_low(n, a, b):
  Laws.low_unique(n, Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b)), Word.to_nat(n, Word.mul(n, a, b)), um.k(n, n, a, b, Word.zero(n)), um.e(n, a, b), Laws.word_value_lt(n, Word.mul(n, a, b)))

def Laws.word_mul_wrap(n, a, b):
  Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.mul(n, a, b)), U.U32Nat.dbl(n, U.U32Nat.high(n, Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b))))), Nat.add(Word.to_nat(n, Word.mul(n, a, b)), U.U32Nat.dbl(n, um.k(n, n, a, b, Word.zero(n)))), Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b)), Equal.cong(Nat, Nat, zz => Nat.add(Word.to_nat(n, Word.mul(n, a, b)), U.U32Nat.dbl(n, zz)), U.U32Nat.high(n, Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b))), um.k(n, n, a, b, Word.zero(n)), Equal.sym(Nat, um.k(n, n, a, b, Word.zero(n)), U.U32Nat.high(n, Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b))), Laws.high_unique(n, Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b)), Word.to_nat(n, Word.mul(n, a, b)), um.k(n, n, a, b, Word.zero(n)), um.e(n, a, b), Laws.word_value_lt(n, Word.mul(n, a, b))))), um.e(n, a, b))

def Laws.word_mul_value(n, a, b, z, h):
  Laws.dbl_nowrap(n, U.U32Nat.high(n, Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b))), Word.to_nat(n, Word.mul(n, a, b)), Nat.mul(Word.to_nat(n, a), Word.to_nat(n, b)), Word.to_nat(n, z), Laws.word_mul_wrap(n, a, b), h, Laws.word_value_lt(n, z))

def Laws.u32_mul_wrap(a, b):
  match a b:
    case U32{+x} U32{+y}:
      Laws.word_mul_wrap(32n, x, y)

def Laws.u32_mul_low(a, b):
  match a b:
    case U32{+x} U32{+y}:
      Laws.word_mul_low(32n, x, y)

def Laws.u32_mul_value(a, b, c, h):
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      Laws.word_mul_value(32n, x, y, z, h)

# Division: Base's U32.divmod.go, one quotient bit a step, keeps q b + r
# = the bits read so far, with r < b

def ud.q(m: Nat, qr: Word(m) & U32) -> Nat:
  (q, r) = qr
  Word.to_nat(m, q)

def ud.r(m: Nat, qr: Word(m) & U32) -> Nat:
  (q, r) = qr
  U32.to_nat(r)

# Word.shl.out is the bit going out and the shifted word
def un.so(n: Nat, +c: Bool, +w: Word(n)) -> {Word.shl.out(n, c, w) == (un.topc(n, c, w), Word.shl.put(n, c, w)) : Bool & Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{+x, +t}:
          %Equal.sym(Bool & Word(p), Word.shl.out(p, x, t), (un.topc(p, x, t), Word.shl.put(p, x, t)), un.so(p, x, t)) : {Word.shl.out.con(p, c, _) == (un.topc(p, x, t), WCon{c, Word.shl.put(p, x, t)}) : Bool & Word(1n+p)}
          {==}

def un.ge_lt(c: Cmp) -> {Cmp.is_ge(c) == Bool.not(Cmp.is_lt(c)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def un.bit_le(b: Bool) -> {Nat.is_le(U.U32Nat.bit(b), 1n) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# not x < y: y <= x
def un.nlt_le(x: Nat, y: Nat, e: {Nat.is_lt(x, y) == False{} : Bool}) -> {Nat.is_le(y, x) == True{} : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, un.tf(e))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      un.nlt_le(p, q, e)

def ur.r21() -> {Nat.mul(1n, 1n) == 1n : Nat}:
  {==}

def ur.r22() -> {Nat.mul(1n, 0n) == 0n : Nat}:
  %Equal.sym(Nat, Nat.mul(1n, 0n), 0n, Laws.nat_mul_zero(1n)) : {_ == 0n : Nat}
  {==}

def ur.r23() -> {Nat.mul(0n, 1n) == 0n : Nat}:
  {==}

def ur.r24(+x0: Nat, +x1: Nat) -> {x0 == Nat.add(x0, Nat.mul(0n, x1)) : Nat}:
  %Equal.sym(Nat, x0, Nat.add(x0, 0n), Equal.sym(Nat, Nat.add(x0, 0n), x0, Laws.nat_add_zero(x0))) : {_ == Nat.add(x0, Nat.mul(0n, x1)) : Nat}
  {==}

def ur.r25(+x0: Nat, +x1: Nat) -> {Nat.add(x0, U.U32Nat.dbl(x1, Nat.mul(0n, 1n))) == x0 : Nat}:
  %Equal.sym(Nat, U.U32Nat.dbl(x1, 0n), 0n, Laws.dbl_zero(x1)) : {Nat.add(x0, _) == x0 : Nat}
  %Equal.sym(Nat, Nat.add(x0, 0n), x0, Laws.nat_add_zero(x0)) : {_ == x0 : Nat}
  {==}

def ur.r26(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat, +x4: Nat, +x5: Nat) -> {Nat.add(Nat.add(Nat.add(x0, x1), Nat.add(Nat.double(x2), 1n+x3)), 1n+Nat.add(x4, Nat.double(x5))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}:
  %Equal.sym(Nat, Nat.double(x2), Nat.add(x2, x2), Laws.nat_double(x2)) : {Nat.add(Nat.add(Nat.add(x0, x1), Nat.add(_, 1n+x3)), 1n+Nat.add(x4, Nat.double(x5))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x2, x2), Nat.add(1n, x3)), Nat.add(x2, Nat.add(x2, Nat.add(1n, x3))), Laws.nat_add_assoc(x2, x2, Nat.add(1n, x3))) : {Nat.add(Nat.add(Nat.add(x0, x1), _), 1n+Nat.add(x4, Nat.double(x5))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(1n, x3)), Nat.add(1n, Nat.add(x2, x3)), Laws.nat_add_left_comm(x2, 1n, x3)) : {Nat.add(Nat.add(Nat.add(x0, x1), Nat.add(x2, _)), 1n+Nat.add(x4, Nat.double(x5))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(1n, Nat.add(x2, x3))), Nat.add(1n, Nat.add(x2, Nat.add(x2, x3))), Laws.nat_add_left_comm(x2, 1n, Nat.add(x2, x3))) : {Nat.add(Nat.add(Nat.add(x0, x1), _), 1n+Nat.add(x4, Nat.double(x5))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(x2, Nat.add(x2, x3)))), Nat.add(x0, Nat.add(x1, Nat.add(1n, Nat.add(x2, Nat.add(x2, x3))))), Laws.nat_add_assoc(x0, x1, Nat.add(1n, Nat.add(x2, Nat.add(x2, x3))))) : {Nat.add(_, 1n+Nat.add(x4, Nat.double(x5))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(1n, Nat.add(x2, Nat.add(x2, x3)))), Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(x2, x3)))), Laws.nat_add_left_comm(x1, 1n, Nat.add(x2, Nat.add(x2, x3)))) : {Nat.add(Nat.add(x0, _), 1n+Nat.add(x4, Nat.double(x5))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(x2, x3))))), Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, x3))))), Laws.nat_add_left_comm(x0, 1n, Nat.add(x1, Nat.add(x2, Nat.add(x2, x3))))) : {Nat.add(_, 1n+Nat.add(x4, Nat.double(x5))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.double(x5), Nat.add(x5, x5), Laws.nat_double(x5)) : {Nat.add(Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, x3))))), Nat.add(1n, Nat.add(x4, _))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, x3))))), Nat.add(1n, Nat.add(x4, Nat.add(x5, x5)))), Nat.add(1n, Nat.add(Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, x3)))), Nat.add(1n, Nat.add(x4, Nat.add(x5, x5))))), Laws.nat_add_assoc(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, x3)))), Nat.add(1n, Nat.add(x4, Nat.add(x5, x5))))) : {_ == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, x3)))), Nat.add(1n, Nat.add(x4, Nat.add(x5, x5)))), Nat.add(x0, Nat.add(Nat.add(x1, Nat.add(x2, Nat.add(x2, x3))), Nat.add(1n, Nat.add(x4, Nat.add(x5, x5))))), Laws.nat_add_assoc(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, x3))), Nat.add(1n, Nat.add(x4, Nat.add(x5, x5))))) : {Nat.add(1n, _) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x1, Nat.add(x2, Nat.add(x2, x3))), Nat.add(1n, Nat.add(x4, Nat.add(x5, x5)))), Nat.add(x1, Nat.add(Nat.add(x2, Nat.add(x2, x3)), Nat.add(1n, Nat.add(x4, Nat.add(x5, x5))))), Laws.nat_add_assoc(x1, Nat.add(x2, Nat.add(x2, x3)), Nat.add(1n, Nat.add(x4, Nat.add(x5, x5))))) : {Nat.add(1n, Nat.add(x0, _)) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x2, Nat.add(x2, x3)), Nat.add(1n, Nat.add(x4, Nat.add(x5, x5)))), Nat.add(x2, Nat.add(Nat.add(x2, x3), Nat.add(1n, Nat.add(x4, Nat.add(x5, x5))))), Laws.nat_add_assoc(x2, Nat.add(x2, x3), Nat.add(1n, Nat.add(x4, Nat.add(x5, x5))))) : {Nat.add(1n, Nat.add(x0, Nat.add(x1, _))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x2, x3), Nat.add(1n, Nat.add(x4, Nat.add(x5, x5)))), Nat.add(x2, Nat.add(x3, Nat.add(1n, Nat.add(x4, Nat.add(x5, x5))))), Laws.nat_add_assoc(x2, x3, Nat.add(1n, Nat.add(x4, Nat.add(x5, x5))))) : {Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, _)))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x3, Nat.add(1n, Nat.add(x4, Nat.add(x5, x5)))), Nat.add(1n, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5)))), Laws.nat_add_left_comm(x3, 1n, Nat.add(x4, Nat.add(x5, x5)))) : {Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, _))))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(1n, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5))))), Nat.add(1n, Nat.add(x2, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5))))), Laws.nat_add_left_comm(x2, 1n, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5))))) : {Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, _)))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(1n, Nat.add(x2, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5)))))), Nat.add(1n, Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5)))))), Laws.nat_add_left_comm(x2, 1n, Nat.add(x2, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5)))))) : {Nat.add(1n, Nat.add(x0, Nat.add(x1, _))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(1n, Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5))))))), Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5))))))), Laws.nat_add_left_comm(x1, 1n, Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5))))))) : {Nat.add(1n, Nat.add(x0, _)) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5)))))))), Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5)))))))), Laws.nat_add_left_comm(x0, 1n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5)))))))) : {Nat.add(1n, _) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5))))))))), Nat.add(Nat.add(1n, 1n), Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5)))))))), Equal.sym(Nat, Nat.add(Nat.add(1n, 1n), Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5)))))))), Nat.add(1n, Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5))))))))), Laws.nat_add_assoc(1n, 1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x4, Nat.add(x5, x5)))))))))) : {_ == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x4, Nat.add(x5, x5)), Nat.add(x5, Nat.add(x4, x5)), Equal.sym(Nat, Nat.add(x5, Nat.add(x4, x5)), Nat.add(x4, Nat.add(x5, x5)), Laws.nat_add_left_comm(x5, x4, x5))) : {Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, _)))))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x3, Nat.add(x5, Nat.add(x4, x5))), Nat.add(x5, Nat.add(x3, Nat.add(x4, x5))), Equal.sym(Nat, Nat.add(x5, Nat.add(x3, Nat.add(x4, x5))), Nat.add(x3, Nat.add(x5, Nat.add(x4, x5))), Laws.nat_add_left_comm(x5, x3, Nat.add(x4, x5)))) : {Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, _))))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x4, x5), Nat.add(x5, x4), Equal.sym(Nat, Nat.add(x5, x4), Nat.add(x4, x5), Laws.nat_add_comm(x5, x4))) : {Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, Nat.add(x3, _))))))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x3, Nat.add(x5, x4)), Nat.add(x5, Nat.add(x3, x4)), Equal.sym(Nat, Nat.add(x5, Nat.add(x3, x4)), Nat.add(x3, Nat.add(x5, x4)), Laws.nat_add_left_comm(x5, x3, x4))) : {Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, _)))))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x5, Nat.add(x5, Nat.add(x3, x4))), Nat.add(Nat.add(x5, x5), Nat.add(x3, x4)), Equal.sym(Nat, Nat.add(Nat.add(x5, x5), Nat.add(x3, x4)), Nat.add(x5, Nat.add(x5, Nat.add(x3, x4))), Laws.nat_add_assoc(x5, x5, Nat.add(x3, x4)))) : {Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, _))))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(Nat.add(x5, x5), Nat.add(x3, x4))), Nat.add(Nat.add(x2, Nat.add(x5, x5)), Nat.add(x3, x4)), Equal.sym(Nat, Nat.add(Nat.add(x2, Nat.add(x5, x5)), Nat.add(x3, x4)), Nat.add(x2, Nat.add(Nat.add(x5, x5), Nat.add(x3, x4))), Laws.nat_add_assoc(x2, Nat.add(x5, x5), Nat.add(x3, x4)))) : {Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, _)))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(Nat.add(x2, Nat.add(x5, x5)), Nat.add(x3, x4))), Nat.add(Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))), Nat.add(x3, x4)), Equal.sym(Nat, Nat.add(Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))), Nat.add(x3, x4)), Nat.add(x2, Nat.add(Nat.add(x2, Nat.add(x5, x5)), Nat.add(x3, x4))), Laws.nat_add_assoc(x2, Nat.add(x2, Nat.add(x5, x5)), Nat.add(x3, x4)))) : {Nat.add(2n, Nat.add(x0, Nat.add(x1, _))) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))), Nat.add(x3, x4))), Nat.add(Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))), Nat.add(x3, x4)), Equal.sym(Nat, Nat.add(Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))), Nat.add(x3, x4)), Nat.add(x1, Nat.add(Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))), Nat.add(x3, x4))), Laws.nat_add_assoc(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))), Nat.add(x3, x4)))) : {Nat.add(2n, Nat.add(x0, _)) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))), Nat.add(x3, x4))), Nat.add(Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))), Nat.add(x3, x4)), Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))), Nat.add(x3, x4)), Nat.add(x0, Nat.add(Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))), Nat.add(x3, x4))), Laws.nat_add_assoc(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))), Nat.add(x3, x4)))) : {Nat.add(2n, _) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(2n, Nat.add(Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))), Nat.add(x3, x4))), Nat.add(Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))))), Nat.add(x3, x4)), Equal.sym(Nat, Nat.add(Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))))), Nat.add(x3, x4)), Nat.add(2n, Nat.add(Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))), Nat.add(x3, x4))), Laws.nat_add_assoc(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))), Nat.add(x3, x4)))) : {_ == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))))), Nat.add(x0, Nat.add(2n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))))), Equal.sym(Nat, Nat.add(x0, Nat.add(2n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))))), Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))))), Laws.nat_add_left_comm(x0, 2n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))))) : {Nat.add(_, Nat.add(x3, x4)) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(2n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))), Nat.add(x1, Nat.add(2n, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))), Equal.sym(Nat, Nat.add(x1, Nat.add(2n, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))), Nat.add(2n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))), Laws.nat_add_left_comm(x1, 2n, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))))) : {Nat.add(Nat.add(x0, _), Nat.add(x3, x4)) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x1, Nat.add(2n, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))))), Nat.add(Nat.add(x0, x1), Nat.add(2n, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))), Equal.sym(Nat, Nat.add(Nat.add(x0, x1), Nat.add(2n, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))), Nat.add(x0, Nat.add(x1, Nat.add(2n, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))))), Laws.nat_add_assoc(x0, x1, Nat.add(2n, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))))) : {Nat.add(_, Nat.add(x3, x4)) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(1n, 1n), Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))), Nat.add(1n, Nat.add(1n, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))), Equal.sym(Nat, Nat.add(1n, Nat.add(1n, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))), Nat.add(Nat.add(1n, 1n), Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))), Equal.sym(Nat, Nat.add(Nat.add(1n, 1n), Nat.add(x2, Nat.add(x2, Nat.add(x5, x5)))), Nat.add(1n, Nat.add(1n, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))), Laws.nat_add_assoc(1n, 1n, Nat.add(x2, Nat.add(x2, Nat.add(x5, x5))))))) : {Nat.add(Nat.add(Nat.add(x0, x1), _), Nat.add(x3, x4)) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(x5, x5)), Nat.add(x5, Nat.add(x2, x5)), Equal.sym(Nat, Nat.add(x5, Nat.add(x2, x5)), Nat.add(x2, Nat.add(x5, x5)), Laws.nat_add_left_comm(x5, x2, x5))) : {Nat.add(Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(1n, Nat.add(x2, _)))), Nat.add(x3, x4)) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(x5, Nat.add(x2, x5))), Nat.add(Nat.add(x2, x5), Nat.add(x2, x5)), Equal.sym(Nat, Nat.add(Nat.add(x2, x5), Nat.add(x2, x5)), Nat.add(x2, Nat.add(x5, Nat.add(x2, x5))), Laws.nat_add_assoc(x2, x5, Nat.add(x2, x5)))) : {Nat.add(Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(1n, _))), Nat.add(x3, x4)) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x2, x5), Nat.add(x2, x5)), Nat.double(Nat.add(x2, x5)), Equal.sym(Nat, Nat.double(Nat.add(x2, x5)), Nat.add(Nat.add(x2, x5), Nat.add(x2, x5)), Laws.nat_double(Nat.add(x2, x5)))) : {Nat.add(Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(1n, _))), Nat.add(x3, x4)) == Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x5))), Nat.add(x3, x4)) : Nat}
  {==}

def ur.r27(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat) -> {Nat.add(Nat.add(Nat.add(x0, x1), 2n+Nat.double(Nat.add(x2, x3))), 1n) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}:
  %Equal.sym(Nat, Nat.double(Nat.add(x2, x3)), Nat.add(Nat.add(x2, x3), Nat.add(x2, x3)), Laws.nat_double(Nat.add(x2, x3))) : {Nat.add(Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(1n, _))), 1n) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x2, x3), Nat.add(x2, x3)), Nat.add(x2, Nat.add(x3, Nat.add(x2, x3))), Laws.nat_add_assoc(x2, x3, Nat.add(x2, x3))) : {Nat.add(Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(1n, _))), 1n) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x3, Nat.add(x2, x3)), Nat.add(x2, Nat.add(x3, x3)), Laws.nat_add_left_comm(x3, x2, x3)) : {Nat.add(Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(1n, Nat.add(x2, _)))), 1n) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(1n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Nat.add(Nat.add(1n, 1n), Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), Equal.sym(Nat, Nat.add(Nat.add(1n, 1n), Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), Nat.add(1n, Nat.add(1n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Laws.nat_add_assoc(1n, 1n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))) : {Nat.add(Nat.add(Nat.add(x0, x1), _), 1n) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, x1), Nat.add(2n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Nat.add(x0, Nat.add(x1, Nat.add(2n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))), Laws.nat_add_assoc(x0, x1, Nat.add(2n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))) : {Nat.add(_, 1n) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(2n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Nat.add(2n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Laws.nat_add_left_comm(x1, 2n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))) : {Nat.add(Nat.add(x0, _), 1n) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(2n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))), Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))), Laws.nat_add_left_comm(x0, 2n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))) : {Nat.add(_, 1n) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))), 1n), Nat.add(2n, Nat.add(Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), 1n)), Laws.nat_add_assoc(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), 1n)) : {_ == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), 1n), Nat.add(x0, Nat.add(Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), 1n)), Laws.nat_add_assoc(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), 1n)) : {Nat.add(2n, _) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), 1n), Nat.add(x1, Nat.add(Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))), 1n)), Laws.nat_add_assoc(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))), 1n)) : {Nat.add(2n, Nat.add(x0, _)) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))), 1n), Nat.add(x2, Nat.add(Nat.add(x2, Nat.add(x3, x3)), 1n)), Laws.nat_add_assoc(x2, Nat.add(x2, Nat.add(x3, x3)), 1n)) : {Nat.add(2n, Nat.add(x0, Nat.add(x1, _))) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x2, Nat.add(x3, x3)), 1n), Nat.add(x2, Nat.add(Nat.add(x3, x3), 1n)), Laws.nat_add_assoc(x2, Nat.add(x3, x3), 1n)) : {Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, _)))) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x3, x3), 1n), Nat.add(x3, Nat.add(x3, 1n)), Laws.nat_add_assoc(x3, x3, 1n)) : {Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, _))))) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x3, 1n), Nat.add(1n, x3), Laws.nat_add_comm(x3, 1n)) : {Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, _)))))) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x3, Nat.add(1n, x3)), Nat.add(1n, Nat.add(x3, x3)), Laws.nat_add_left_comm(x3, 1n, x3)) : {Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, _))))) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(1n, Nat.add(x3, x3))), Nat.add(1n, Nat.add(x2, Nat.add(x3, x3))), Laws.nat_add_left_comm(x2, 1n, Nat.add(x3, x3))) : {Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, _)))) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(1n, Nat.add(x2, Nat.add(x3, x3)))), Nat.add(1n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), Laws.nat_add_left_comm(x2, 1n, Nat.add(x2, Nat.add(x3, x3)))) : {Nat.add(2n, Nat.add(x0, Nat.add(x1, _))) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(1n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Laws.nat_add_left_comm(x1, 1n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))) : {Nat.add(2n, Nat.add(x0, _)) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))), Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))), Laws.nat_add_left_comm(x0, 1n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))) : {Nat.add(2n, _) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(2n, Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))))), Nat.add(1n, Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))))), Laws.nat_add_left_comm(2n, 1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))))) : {_ == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))))), Nat.add(Nat.add(1n, 2n), Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))), Equal.sym(Nat, Nat.add(Nat.add(1n, 2n), Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))), Nat.add(1n, Nat.add(2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))))), Laws.nat_add_assoc(1n, 2n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))))) : {_ == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(3n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))), Nat.add(x0, Nat.add(3n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))), Equal.sym(Nat, Nat.add(x0, Nat.add(3n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))), Nat.add(3n, Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))), Laws.nat_add_left_comm(x0, 3n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))))) : {_ == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(3n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Nat.add(x1, Nat.add(3n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Equal.sym(Nat, Nat.add(x1, Nat.add(3n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Nat.add(3n, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Laws.nat_add_left_comm(x1, 3n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))) : {Nat.add(x0, _) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x1, Nat.add(3n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))), Nat.add(Nat.add(x0, x1), Nat.add(3n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Equal.sym(Nat, Nat.add(Nat.add(x0, x1), Nat.add(3n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Nat.add(x0, Nat.add(x1, Nat.add(3n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))))), Laws.nat_add_assoc(x0, x1, Nat.add(3n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))))) : {_ == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(1n, 2n), Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), Nat.add(1n, Nat.add(2n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Equal.sym(Nat, Nat.add(1n, Nat.add(2n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Nat.add(Nat.add(1n, 2n), Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), Equal.sym(Nat, Nat.add(Nat.add(1n, 2n), Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), Nat.add(1n, Nat.add(2n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Laws.nat_add_assoc(1n, 2n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))))) : {Nat.add(Nat.add(x0, x1), _) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(1n, 1n), Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), Nat.add(1n, Nat.add(1n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Equal.sym(Nat, Nat.add(1n, Nat.add(1n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Nat.add(Nat.add(1n, 1n), Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), Equal.sym(Nat, Nat.add(Nat.add(1n, 1n), Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), Nat.add(1n, Nat.add(1n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Laws.nat_add_assoc(1n, 1n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))))) : {Nat.add(Nat.add(x0, x1), Nat.add(1n, _)) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), Nat.add(x2, Nat.add(1n, Nat.add(x2, Nat.add(x3, x3)))), Equal.sym(Nat, Nat.add(x2, Nat.add(1n, Nat.add(x2, Nat.add(x3, x3)))), Nat.add(1n, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), Laws.nat_add_left_comm(x2, 1n, Nat.add(x2, Nat.add(x3, x3))))) : {Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(1n, _))) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(x3, x3)), Nat.add(x3, Nat.add(x2, x3)), Equal.sym(Nat, Nat.add(x3, Nat.add(x2, x3)), Nat.add(x2, Nat.add(x3, x3)), Laws.nat_add_left_comm(x3, x2, x3))) : {Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(1n, Nat.add(x2, Nat.add(1n, _))))) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x3, Nat.add(x2, x3))), Nat.add(x3, Nat.add(1n, Nat.add(x2, x3))), Equal.sym(Nat, Nat.add(x3, Nat.add(1n, Nat.add(x2, x3))), Nat.add(1n, Nat.add(x3, Nat.add(x2, x3))), Laws.nat_add_left_comm(x3, 1n, Nat.add(x2, x3)))) : {Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(1n, Nat.add(x2, _)))) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(x3, Nat.add(1n, Nat.add(x2, x3)))), Nat.add(Nat.add(x2, x3), Nat.add(1n, Nat.add(x2, x3))), Equal.sym(Nat, Nat.add(Nat.add(x2, x3), Nat.add(1n, Nat.add(x2, x3))), Nat.add(x2, Nat.add(x3, Nat.add(1n, Nat.add(x2, x3)))), Laws.nat_add_assoc(x2, x3, Nat.add(1n, Nat.add(x2, x3))))) : {Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(1n, _))) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(Nat.add(x2, x3), Nat.add(1n, Nat.add(x2, x3)))), Nat.add(Nat.add(1n, Nat.add(x2, x3)), Nat.add(1n, Nat.add(x2, x3))), Equal.sym(Nat, Nat.add(Nat.add(1n, Nat.add(x2, x3)), Nat.add(1n, Nat.add(x2, x3))), Nat.add(1n, Nat.add(Nat.add(x2, x3), Nat.add(1n, Nat.add(x2, x3)))), Laws.nat_add_assoc(1n, Nat.add(x2, x3), Nat.add(1n, Nat.add(x2, x3))))) : {Nat.add(Nat.add(x0, x1), Nat.add(1n, _)) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x2, x3)), Nat.add(x2, Nat.add(1n, x3)), Equal.sym(Nat, Nat.add(x2, Nat.add(1n, x3)), Nat.add(1n, Nat.add(x2, x3)), Laws.nat_add_left_comm(x2, 1n, x3))) : {Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(Nat.add(1n, Nat.add(x2, x3)), _))) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x2, x3)), Nat.add(x2, Nat.add(1n, x3)), Equal.sym(Nat, Nat.add(x2, Nat.add(1n, x3)), Nat.add(1n, Nat.add(x2, x3)), Laws.nat_add_left_comm(x2, 1n, x3))) : {Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(_, Nat.add(x2, 1n+x3)))) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x2, 1n+x3), Nat.add(x2, 1n+x3)), Nat.double(Nat.add(x2, 1n+x3)), Equal.sym(Nat, Nat.double(Nat.add(x2, 1n+x3)), Nat.add(Nat.add(x2, 1n+x3), Nat.add(x2, 1n+x3)), Laws.nat_double(Nat.add(x2, 1n+x3)))) : {Nat.add(Nat.add(x0, x1), Nat.add(1n, _)) == Nat.add(Nat.add(x0, x1), 1n+Nat.double(Nat.add(x2, 1n+x3))) : Nat}
  {==}

def ur.r28(+x0: Nat, +x1: Nat, +x2: Nat) -> {Nat.add(Nat.add(x0, x1), 1n+Nat.double(x2)) == Nat.add(Nat.add(x0, x2), Nat.add(x1, 1n+x2)) : Nat}:
  %Equal.sym(Nat, Nat.double(x2), Nat.add(x2, x2), Laws.nat_double(x2)) : {Nat.add(Nat.add(x0, x1), Nat.add(1n, _)) == Nat.add(Nat.add(x0, x2), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, x1), Nat.add(1n, Nat.add(x2, x2))), Nat.add(x0, Nat.add(x1, Nat.add(1n, Nat.add(x2, x2)))), Laws.nat_add_assoc(x0, x1, Nat.add(1n, Nat.add(x2, x2)))) : {_ == Nat.add(Nat.add(x0, x2), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(1n, Nat.add(x2, x2))), Nat.add(1n, Nat.add(x1, Nat.add(x2, x2))), Laws.nat_add_left_comm(x1, 1n, Nat.add(x2, x2))) : {Nat.add(x0, _) == Nat.add(Nat.add(x0, x2), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(x1, Nat.add(x2, x2)))), Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, x2)))), Laws.nat_add_left_comm(x0, 1n, Nat.add(x1, Nat.add(x2, x2)))) : {_ == Nat.add(Nat.add(x0, x2), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, x2)))), Nat.add(x0, Nat.add(1n, Nat.add(x1, Nat.add(x2, x2)))), Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(x1, Nat.add(x2, x2)))), Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x2, x2)))), Laws.nat_add_left_comm(x0, 1n, Nat.add(x1, Nat.add(x2, x2))))) : {_ == Nat.add(Nat.add(x0, x2), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x2, x2)), Nat.add(x2, Nat.add(x1, x2)), Equal.sym(Nat, Nat.add(x2, Nat.add(x1, x2)), Nat.add(x1, Nat.add(x2, x2)), Laws.nat_add_left_comm(x2, x1, x2))) : {Nat.add(x0, Nat.add(1n, _)) == Nat.add(Nat.add(x0, x2), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x2, Nat.add(x1, x2))), Nat.add(x2, Nat.add(1n, Nat.add(x1, x2))), Equal.sym(Nat, Nat.add(x2, Nat.add(1n, Nat.add(x1, x2))), Nat.add(1n, Nat.add(x2, Nat.add(x1, x2))), Laws.nat_add_left_comm(x2, 1n, Nat.add(x1, x2)))) : {Nat.add(x0, _) == Nat.add(Nat.add(x0, x2), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x2, Nat.add(1n, Nat.add(x1, x2)))), Nat.add(Nat.add(x0, x2), Nat.add(1n, Nat.add(x1, x2))), Equal.sym(Nat, Nat.add(Nat.add(x0, x2), Nat.add(1n, Nat.add(x1, x2))), Nat.add(x0, Nat.add(x2, Nat.add(1n, Nat.add(x1, x2)))), Laws.nat_add_assoc(x0, x2, Nat.add(1n, Nat.add(x1, x2))))) : {_ == Nat.add(Nat.add(x0, x2), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x1, x2)), Nat.add(x1, Nat.add(1n, x2)), Equal.sym(Nat, Nat.add(x1, Nat.add(1n, x2)), Nat.add(1n, Nat.add(x1, x2)), Laws.nat_add_left_comm(x1, 1n, x2))) : {Nat.add(Nat.add(x0, x2), _) == Nat.add(Nat.add(x0, x2), Nat.add(x1, 1n+x2)) : Nat}
  {==}

def ur.r29(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat) -> {Nat.add(x0, Nat.add(Nat.add(Nat.double(x1), x2), 1n+x3)) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}:
  %Equal.sym(Nat, Nat.double(x1), Nat.add(x1, x1), Laws.nat_double(x1)) : {Nat.add(x0, Nat.add(Nat.add(_, x2), 1n+x3)) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x1, x1), x2), Nat.add(x1, Nat.add(x1, x2)), Laws.nat_add_assoc(x1, x1, x2)) : {Nat.add(x0, Nat.add(_, 1n+x3)) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x1, Nat.add(x1, x2)), Nat.add(1n, x3)), Nat.add(x1, Nat.add(Nat.add(x1, x2), Nat.add(1n, x3))), Laws.nat_add_assoc(x1, Nat.add(x1, x2), Nat.add(1n, x3))) : {Nat.add(x0, _) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x1, x2), Nat.add(1n, x3)), Nat.add(x1, Nat.add(x2, Nat.add(1n, x3))), Laws.nat_add_assoc(x1, x2, Nat.add(1n, x3))) : {Nat.add(x0, Nat.add(x1, _)) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(1n, x3)), Nat.add(1n, Nat.add(x2, x3)), Laws.nat_add_left_comm(x2, 1n, x3)) : {Nat.add(x0, Nat.add(x1, Nat.add(x1, _))) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(1n, Nat.add(x2, x3))), Nat.add(1n, Nat.add(x1, Nat.add(x2, x3))), Laws.nat_add_left_comm(x1, 1n, Nat.add(x2, x3))) : {Nat.add(x0, Nat.add(x1, _)) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(1n, Nat.add(x1, Nat.add(x2, x3)))), Nat.add(1n, Nat.add(x1, Nat.add(x1, Nat.add(x2, x3)))), Laws.nat_add_left_comm(x1, 1n, Nat.add(x1, Nat.add(x2, x3)))) : {Nat.add(x0, _) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(x1, Nat.add(x1, Nat.add(x2, x3))))), Nat.add(1n, Nat.add(x0, Nat.add(x1, Nat.add(x1, Nat.add(x2, x3))))), Laws.nat_add_left_comm(x0, 1n, Nat.add(x1, Nat.add(x1, Nat.add(x2, x3))))) : {_ == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x1, Nat.add(x1, Nat.add(x2, x3)))), Nat.add(x1, Nat.add(x0, Nat.add(x1, Nat.add(x2, x3)))), Equal.sym(Nat, Nat.add(x1, Nat.add(x0, Nat.add(x1, Nat.add(x2, x3)))), Nat.add(x0, Nat.add(x1, Nat.add(x1, Nat.add(x2, x3)))), Laws.nat_add_left_comm(x1, x0, Nat.add(x1, Nat.add(x2, x3))))) : {Nat.add(1n, _) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x1, Nat.add(x2, x3))), Nat.add(x1, Nat.add(x0, Nat.add(x2, x3))), Equal.sym(Nat, Nat.add(x1, Nat.add(x0, Nat.add(x2, x3))), Nat.add(x0, Nat.add(x1, Nat.add(x2, x3))), Laws.nat_add_left_comm(x1, x0, Nat.add(x2, x3)))) : {Nat.add(1n, Nat.add(x1, _)) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x2, x3)), Nat.add(x2, Nat.add(x0, x3)), Equal.sym(Nat, Nat.add(x2, Nat.add(x0, x3)), Nat.add(x0, Nat.add(x2, x3)), Laws.nat_add_left_comm(x2, x0, x3))) : {Nat.add(1n, Nat.add(x1, Nat.add(x1, _))) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x2, Nat.add(x0, x3))), Nat.add(Nat.add(x1, x2), Nat.add(x0, x3)), Equal.sym(Nat, Nat.add(Nat.add(x1, x2), Nat.add(x0, x3)), Nat.add(x1, Nat.add(x2, Nat.add(x0, x3))), Laws.nat_add_assoc(x1, x2, Nat.add(x0, x3)))) : {Nat.add(1n, Nat.add(x1, _)) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(Nat.add(x1, x2), Nat.add(x0, x3))), Nat.add(Nat.add(x1, Nat.add(x1, x2)), Nat.add(x0, x3)), Equal.sym(Nat, Nat.add(Nat.add(x1, Nat.add(x1, x2)), Nat.add(x0, x3)), Nat.add(x1, Nat.add(Nat.add(x1, x2), Nat.add(x0, x3))), Laws.nat_add_assoc(x1, Nat.add(x1, x2), Nat.add(x0, x3)))) : {Nat.add(1n, _) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(Nat.add(x1, Nat.add(x1, x2)), Nat.add(x0, x3))), Nat.add(Nat.add(1n, Nat.add(x1, Nat.add(x1, x2))), Nat.add(x0, x3)), Equal.sym(Nat, Nat.add(Nat.add(1n, Nat.add(x1, Nat.add(x1, x2))), Nat.add(x0, x3)), Nat.add(1n, Nat.add(Nat.add(x1, Nat.add(x1, x2)), Nat.add(x0, x3))), Laws.nat_add_assoc(1n, Nat.add(x1, Nat.add(x1, x2)), Nat.add(x0, x3)))) : {_ == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, x3), Nat.add(x3, x0), Equal.sym(Nat, Nat.add(x3, x0), Nat.add(x0, x3), Laws.nat_add_comm(x3, x0))) : {Nat.add(Nat.add(1n, Nat.add(x1, Nat.add(x1, x2))), _) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, x0, Nat.mul(1n, x0), Equal.sym(Nat, Nat.mul(1n, x0), x0, Laws.nat_one_mul(x0))) : {Nat.add(Nat.add(1n, Nat.add(x1, Nat.add(x1, x2))), Nat.add(x3, _)) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x1, Nat.add(x1, x2))), Nat.add(x1, Nat.add(1n, Nat.add(x1, x2))), Equal.sym(Nat, Nat.add(x1, Nat.add(1n, Nat.add(x1, x2))), Nat.add(1n, Nat.add(x1, Nat.add(x1, x2))), Laws.nat_add_left_comm(x1, 1n, Nat.add(x1, x2)))) : {Nat.add(_, Nat.add(x3, Nat.mul(1n, x0))) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x1, x2)), Nat.add(x1, Nat.add(1n, x2)), Equal.sym(Nat, Nat.add(x1, Nat.add(1n, x2)), Nat.add(1n, Nat.add(x1, x2)), Laws.nat_add_left_comm(x1, 1n, x2))) : {Nat.add(Nat.add(x1, _), Nat.add(x3, Nat.mul(1n, x0))) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x1, Nat.add(1n, x2))), Nat.add(Nat.add(x1, x1), Nat.add(1n, x2)), Equal.sym(Nat, Nat.add(Nat.add(x1, x1), Nat.add(1n, x2)), Nat.add(x1, Nat.add(x1, Nat.add(1n, x2))), Laws.nat_add_assoc(x1, x1, Nat.add(1n, x2)))) : {Nat.add(_, Nat.add(x3, Nat.mul(1n, x0))) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, x1), Nat.double(x1), Equal.sym(Nat, Nat.double(x1), Nat.add(x1, x1), Laws.nat_double(x1))) : {Nat.add(Nat.add(_, 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) == Nat.add(Nat.add(Nat.double(x1), 1n+x2), Nat.add(x3, Nat.mul(1n, x0))) : Nat}
  {==}

def ur.r30(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat) -> {Nat.add(Nat.add(Nat.double(x0), 1n+x1), Nat.add(x2, Nat.double(x3))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}:
  %Equal.sym(Nat, Nat.double(x0), Nat.add(x0, x0), Laws.nat_double(x0)) : {Nat.add(Nat.add(_, 1n+x1), Nat.add(x2, Nat.double(x3))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, x0), Nat.add(1n, x1)), Nat.add(x0, Nat.add(x0, Nat.add(1n, x1))), Laws.nat_add_assoc(x0, x0, Nat.add(1n, x1))) : {Nat.add(_, Nat.add(x2, Nat.double(x3))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(1n, x1)), Nat.add(1n, Nat.add(x0, x1)), Laws.nat_add_left_comm(x0, 1n, x1)) : {Nat.add(Nat.add(x0, _), Nat.add(x2, Nat.double(x3))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(x0, x1))), Nat.add(1n, Nat.add(x0, Nat.add(x0, x1))), Laws.nat_add_left_comm(x0, 1n, Nat.add(x0, x1))) : {Nat.add(_, Nat.add(x2, Nat.double(x3))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.double(x3), Nat.add(x3, x3), Laws.nat_double(x3)) : {Nat.add(Nat.add(1n, Nat.add(x0, Nat.add(x0, x1))), Nat.add(x2, _)) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(1n, Nat.add(x0, Nat.add(x0, x1))), Nat.add(x2, Nat.add(x3, x3))), Nat.add(1n, Nat.add(Nat.add(x0, Nat.add(x0, x1)), Nat.add(x2, Nat.add(x3, x3)))), Laws.nat_add_assoc(1n, Nat.add(x0, Nat.add(x0, x1)), Nat.add(x2, Nat.add(x3, x3)))) : {_ == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x0, x1)), Nat.add(x2, Nat.add(x3, x3))), Nat.add(x0, Nat.add(Nat.add(x0, x1), Nat.add(x2, Nat.add(x3, x3)))), Laws.nat_add_assoc(x0, Nat.add(x0, x1), Nat.add(x2, Nat.add(x3, x3)))) : {Nat.add(1n, _) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, x1), Nat.add(x2, Nat.add(x3, x3))), Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x3, x3)))), Laws.nat_add_assoc(x0, x1, Nat.add(x2, Nat.add(x3, x3)))) : {Nat.add(1n, Nat.add(x0, _)) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(x3, x3)), Nat.add(x3, Nat.add(x2, x3)), Equal.sym(Nat, Nat.add(x3, Nat.add(x2, x3)), Nat.add(x2, Nat.add(x3, x3)), Laws.nat_add_left_comm(x3, x2, x3))) : {Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x1, _)))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x3, Nat.add(x2, x3))), Nat.add(x3, Nat.add(x1, Nat.add(x2, x3))), Equal.sym(Nat, Nat.add(x3, Nat.add(x1, Nat.add(x2, x3))), Nat.add(x1, Nat.add(x3, Nat.add(x2, x3))), Laws.nat_add_left_comm(x3, x1, Nat.add(x2, x3)))) : {Nat.add(1n, Nat.add(x0, Nat.add(x0, _))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x2, x3), Nat.add(x3, x2), Equal.sym(Nat, Nat.add(x3, x2), Nat.add(x2, x3), Laws.nat_add_comm(x3, x2))) : {Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x3, Nat.add(x1, _))))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x3, x2)), Nat.add(x3, Nat.add(x1, x2)), Equal.sym(Nat, Nat.add(x3, Nat.add(x1, x2)), Nat.add(x1, Nat.add(x3, x2)), Laws.nat_add_left_comm(x3, x1, x2))) : {Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x3, _)))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x3, Nat.add(x3, Nat.add(x1, x2))), Nat.add(Nat.add(x3, x3), Nat.add(x1, x2)), Equal.sym(Nat, Nat.add(Nat.add(x3, x3), Nat.add(x1, x2)), Nat.add(x3, Nat.add(x3, Nat.add(x1, x2))), Laws.nat_add_assoc(x3, x3, Nat.add(x1, x2)))) : {Nat.add(1n, Nat.add(x0, Nat.add(x0, _))) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(Nat.add(x3, x3), Nat.add(x1, x2))), Nat.add(Nat.add(x0, Nat.add(x3, x3)), Nat.add(x1, x2)), Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x3, x3)), Nat.add(x1, x2)), Nat.add(x0, Nat.add(Nat.add(x3, x3), Nat.add(x1, x2))), Laws.nat_add_assoc(x0, Nat.add(x3, x3), Nat.add(x1, x2)))) : {Nat.add(1n, Nat.add(x0, _)) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(Nat.add(x0, Nat.add(x3, x3)), Nat.add(x1, x2))), Nat.add(Nat.add(x0, Nat.add(x0, Nat.add(x3, x3))), Nat.add(x1, x2)), Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x0, Nat.add(x3, x3))), Nat.add(x1, x2)), Nat.add(x0, Nat.add(Nat.add(x0, Nat.add(x3, x3)), Nat.add(x1, x2))), Laws.nat_add_assoc(x0, Nat.add(x0, Nat.add(x3, x3)), Nat.add(x1, x2)))) : {Nat.add(1n, _) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(Nat.add(x0, Nat.add(x0, Nat.add(x3, x3))), Nat.add(x1, x2))), Nat.add(Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x3, x3)))), Nat.add(x1, x2)), Equal.sym(Nat, Nat.add(Nat.add(1n, Nat.add(x0, Nat.add(x0, Nat.add(x3, x3)))), Nat.add(x1, x2)), Nat.add(1n, Nat.add(Nat.add(x0, Nat.add(x0, Nat.add(x3, x3))), Nat.add(x1, x2))), Laws.nat_add_assoc(1n, Nat.add(x0, Nat.add(x0, Nat.add(x3, x3))), Nat.add(x1, x2)))) : {_ == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x3, x3)), Nat.add(x3, Nat.add(x0, x3)), Equal.sym(Nat, Nat.add(x3, Nat.add(x0, x3)), Nat.add(x0, Nat.add(x3, x3)), Laws.nat_add_left_comm(x3, x0, x3))) : {Nat.add(Nat.add(1n, Nat.add(x0, _)), Nat.add(x1, x2)) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x3, Nat.add(x0, x3))), Nat.add(Nat.add(x0, x3), Nat.add(x0, x3)), Equal.sym(Nat, Nat.add(Nat.add(x0, x3), Nat.add(x0, x3)), Nat.add(x0, Nat.add(x3, Nat.add(x0, x3))), Laws.nat_add_assoc(x0, x3, Nat.add(x0, x3)))) : {Nat.add(Nat.add(1n, _), Nat.add(x1, x2)) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, x3), Nat.add(x0, x3)), Nat.double(Nat.add(x0, x3)), Equal.sym(Nat, Nat.double(Nat.add(x0, x3)), Nat.add(Nat.add(x0, x3), Nat.add(x0, x3)), Laws.nat_double(Nat.add(x0, x3)))) : {Nat.add(Nat.add(1n, _), Nat.add(x1, x2)) == Nat.add(1n+Nat.double(Nat.add(x0, x3)), Nat.add(x1, x2)) : Nat}
  {==}

def ur.r31(+x0: Nat) -> {Nat.double(x0) == Nat.add(x0, x0) : Nat}:
  %Equal.sym(Nat, Nat.double(x0), Nat.add(x0, x0), Laws.nat_double(x0)) : {_ == Nat.add(x0, x0) : Nat}
  {==}

# r' + g b = 2 r + a, r' < b: the remainder after one step, at a width N
def ud.k(+N: Nat, +S: Nat, +B: Nat, +R: Nat, +A: Nat, +R1: Nat, +T: Bool, +L: Bool, +g: Bool, +eput: {Nat.add(S, U.U32Nat.dbl(N, U.U32Nat.bit(T))) == Nat.add(A, Nat.double(R)) : Nat}, +eL: {Nat.is_lt(S, B) == L : Bool}, +eg: {Bool.or(T, Bool.not(L)) == g : Bool}, +er1: {Nat.add(R1, Nat.mul(U.U32Nat.bit(g), B)) == Nat.add(S, U.U32Nat.dbl(N, Nat.mul(U.U32Nat.bit(g), U.U32Nat.bit(L)))) : Nat}, +hA: {Nat.is_le(A, 1n) == True{} : Bool}, +hR: {Nat.is_lt(R, B) == True{} : Bool}, +hB: {Nat.is_lt(B, U.U32Nat.dbl(N, 1n)) == True{} : Bool}) -> {Nat.add(R1, Nat.mul(U.U32Nat.bit(g), B)) == Nat.add(A, Nat.double(R)) : Nat} & {Nat.is_lt(R1, B) == True{} : Bool}:
  match T L g:
    case True{} True{} True{}:
      (Equal.trans(Nat, Nat.add(R1, Nat.mul(1n, B)), Nat.add(S, U.U32Nat.dbl(N, 1n)), Nat.add(A, Nat.double(R)), Equal.trans(Nat, Nat.add(R1, Nat.mul(1n, B)), Nat.add(S, U.U32Nat.dbl(N, Nat.mul(1n, 1n))), Nat.add(S, U.U32Nat.dbl(N, 1n)), er1, Equal.cong(Nat, Nat, zz => Nat.add(S, U.U32Nat.dbl(N, zz)), Nat.mul(1n, 1n), 1n, ur.r21())), eput), Equal.trans(Bool, Nat.is_lt(R1, B), Nat.is_lt(R1, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1)), True{}, Equal.sym(Bool, Nat.is_lt(R1, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1)), Nat.is_lt(R1, B), Equal.cong(Nat, Bool, zz => Nat.is_lt(R1, zz), Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1), B, Laws.nat_add_cancel(B, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1), B, Equal.trans(Nat, Nat.add(B, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1)), Nat.double(B), Nat.add(B, B), Equal.trans(Nat, Nat.add(B, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1)), Nat.double(Nat.add(Nat.sub(B, 1n+R), 1n+R)), Nat.double(B), Equal.trans(Nat, Nat.add(B, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1)), Nat.add(1n+Nat.double(Nat.add(Nat.sub(B, 1n+R), R)), 1n), Nat.double(Nat.add(Nat.sub(B, 1n+R), 1n+R)), Equal.trans(Nat, Nat.add(B, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1)), Nat.add(1n+Nat.double(Nat.add(Nat.sub(B, 1n+R), R)), Nat.add(Nat.sub(1n, A), A)), Nat.add(1n+Nat.double(Nat.add(Nat.sub(B, 1n+R), R)), 1n), Equal.trans(Nat, Nat.add(B, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1)), Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), 1n+Nat.sub(1n, A)), Nat.add(A, Nat.double(R))), Nat.add(1n+Nat.double(Nat.add(Nat.sub(B, 1n+R), R)), Nat.add(Nat.sub(1n, A), A)), Equal.trans(Nat, Nat.add(B, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1)), Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), 1n+Nat.sub(1n, A)), Nat.add(R1, Nat.mul(1n, B))), Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), 1n+Nat.sub(1n, A)), Nat.add(A, Nat.double(R))), ur.r29(B, Nat.sub(B, 1n+R), Nat.sub(1n, A), R1), Equal.cong(Nat, Nat, zz => Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), 1n+Nat.sub(1n, A)), zz), Nat.add(R1, Nat.mul(1n, B)), Nat.add(A, Nat.double(R)), Equal.trans(Nat, Nat.add(R1, Nat.mul(1n, B)), Nat.add(S, U.U32Nat.dbl(N, 1n)), Nat.add(A, Nat.double(R)), Equal.trans(Nat, Nat.add(R1, Nat.mul(1n, B)), Nat.add(S, U.U32Nat.dbl(N, Nat.mul(1n, 1n))), Nat.add(S, U.U32Nat.dbl(N, 1n)), er1, Equal.cong(Nat, Nat, zz => Nat.add(S, U.U32Nat.dbl(N, zz)), Nat.mul(1n, 1n), 1n, ur.r21())), eput))), ur.r30(Nat.sub(B, 1n+R), Nat.sub(1n, A), A, R)), Equal.cong(Nat, Nat, zz => Nat.add(1n+Nat.double(Nat.add(Nat.sub(B, 1n+R), R)), zz), Nat.add(Nat.sub(1n, A), A), 1n, Laws.nat_le_witness(A, 1n, hA))), ur.r7(Nat.sub(B, 1n+R), R)), Equal.cong(Nat, Nat, zz => Nat.double(zz), Nat.add(Nat.sub(B, 1n+R), 1n+R), B, Laws.nat_lt_witness(R, B, hR))), ur.r31(B))))), Laws.nat_lt_add(R1, Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)))))
    case True{} False{} True{}:
      Empty.absurd({Nat.add(R1, Nat.mul(U.U32Nat.bit(True{}), B)) == Nat.add(A, Nat.double(R)) : Nat} & {Nat.is_lt(R1, B) == True{} : Bool}, Laws.nat_succ_add_absurd(Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), Nat.add(Nat.double(Nat.sub(B, 1n+R)), 1n+Nat.sub(1n, A))), Nat.add(A, Nat.double(R)), Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), Nat.add(Nat.double(Nat.sub(B, 1n+R)), 1n+Nat.sub(1n, A))), 1n+Nat.add(A, Nat.double(R))), Nat.add(S, U.U32Nat.dbl(N, 1n)), Nat.add(A, Nat.double(R)), Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), Nat.add(Nat.double(Nat.sub(B, 1n+R)), 1n+Nat.sub(1n, A))), 1n+Nat.add(A, Nat.double(R))), Nat.add(S, Nat.add(Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B), 1n+B)), Nat.add(S, U.U32Nat.dbl(N, 1n)), Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), Nat.add(Nat.double(Nat.sub(B, 1n+R)), 1n+Nat.sub(1n, A))), 1n+Nat.add(A, Nat.double(R))), Nat.add(Nat.add(Nat.sub(S, B), B), Nat.add(Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B), 1n+B)), Nat.add(S, Nat.add(Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B), 1n+B)), Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), Nat.add(Nat.double(Nat.sub(B, 1n+R)), 1n+Nat.sub(1n, A))), 1n+Nat.add(A, Nat.double(R))), Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), 1n+Nat.double(B)), Nat.add(Nat.add(Nat.sub(S, B), B), Nat.add(Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B), 1n+B)), Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), Nat.add(Nat.double(Nat.sub(B, 1n+R)), 1n+Nat.sub(1n, A))), 1n+Nat.add(A, Nat.double(R))), Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), 1n+Nat.double(Nat.add(Nat.sub(B, 1n+R), 1n+R))), Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), 1n+Nat.double(B)), Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), Nat.add(Nat.double(Nat.sub(B, 1n+R)), 1n+Nat.sub(1n, A))), 1n+Nat.add(A, Nat.double(R))), Nat.add(Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), 2n+Nat.double(Nat.add(Nat.sub(B, 1n+R), R))), 1n), Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), 1n+Nat.double(Nat.add(Nat.sub(B, 1n+R), 1n+R))), Equal.trans(Nat, Nat.add(Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), Nat.add(Nat.double(Nat.sub(B, 1n+R)), 1n+Nat.sub(1n, A))), 1n+Nat.add(A, Nat.double(R))), Nat.add(Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), 2n+Nat.double(Nat.add(Nat.sub(B, 1n+R), R))), Nat.add(Nat.sub(1n, A), A)), Nat.add(Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), 2n+Nat.double(Nat.add(Nat.sub(B, 1n+R), R))), 1n), ur.r26(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B), Nat.sub(B, 1n+R), Nat.sub(1n, A), A, R), Equal.cong(Nat, Nat, zz => Nat.add(Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), 2n+Nat.double(Nat.add(Nat.sub(B, 1n+R), R))), zz), Nat.add(Nat.sub(1n, A), A), 1n, Laws.nat_le_witness(A, 1n, hA))), ur.r27(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B), Nat.sub(B, 1n+R), R)), Equal.cong(Nat, Nat, zz => Nat.add(Nat.add(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B)), 1n+Nat.double(zz)), Nat.add(Nat.sub(B, 1n+R), 1n+R), B, Laws.nat_lt_witness(R, B, hR))), ur.r28(Nat.sub(S, B), Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B), B)), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.add(Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B), 1n+B)), Nat.add(Nat.sub(S, B), B), S, Laws.nat_le_witness(B, S, un.nlt_le(S, B, eL)))), Equal.cong(Nat, Nat, zz => Nat.add(S, zz), Nat.add(Nat.sub(U.U32Nat.dbl(N, 1n), 1n+B), 1n+B), U.U32Nat.dbl(N, 1n), Laws.nat_lt_witness(B, U.U32Nat.dbl(N, 1n), hB))), eput)))
    case False{} False{} True{}:
      (Equal.trans(Nat, Nat.add(R1, Nat.mul(1n, B)), Nat.add(S, U.U32Nat.dbl(N, 0n)), Nat.add(A, Nat.double(R)), Equal.trans(Nat, Nat.add(R1, Nat.mul(1n, B)), Nat.add(S, U.U32Nat.dbl(N, Nat.mul(1n, 0n))), Nat.add(S, U.U32Nat.dbl(N, 0n)), er1, Equal.cong(Nat, Nat, zz => Nat.add(S, U.U32Nat.dbl(N, zz)), Nat.mul(1n, 0n), 0n, ur.r22())), eput), Equal.trans(Bool, Nat.is_lt(R1, B), Nat.is_lt(R1, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1)), True{}, Equal.sym(Bool, Nat.is_lt(R1, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1)), Nat.is_lt(R1, B), Equal.cong(Nat, Bool, zz => Nat.is_lt(R1, zz), Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1), B, Laws.nat_add_cancel(B, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1), B, Equal.trans(Nat, Nat.add(B, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1)), Nat.double(B), Nat.add(B, B), Equal.trans(Nat, Nat.add(B, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1)), Nat.double(Nat.add(Nat.sub(B, 1n+R), 1n+R)), Nat.double(B), Equal.trans(Nat, Nat.add(B, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1)), Nat.add(1n+Nat.double(Nat.add(Nat.sub(B, 1n+R), R)), 1n), Nat.double(Nat.add(Nat.sub(B, 1n+R), 1n+R)), Equal.trans(Nat, Nat.add(B, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1)), Nat.add(1n+Nat.double(Nat.add(Nat.sub(B, 1n+R), R)), Nat.add(Nat.sub(1n, A), A)), Nat.add(1n+Nat.double(Nat.add(Nat.sub(B, 1n+R), R)), 1n), Equal.trans(Nat, Nat.add(B, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1)), Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), 1n+Nat.sub(1n, A)), Nat.add(A, Nat.double(R))), Nat.add(1n+Nat.double(Nat.add(Nat.sub(B, 1n+R), R)), Nat.add(Nat.sub(1n, A), A)), Equal.trans(Nat, Nat.add(B, Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)), 1n+R1)), Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), 1n+Nat.sub(1n, A)), Nat.add(R1, Nat.mul(1n, B))), Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), 1n+Nat.sub(1n, A)), Nat.add(A, Nat.double(R))), ur.r29(B, Nat.sub(B, 1n+R), Nat.sub(1n, A), R1), Equal.cong(Nat, Nat, zz => Nat.add(Nat.add(Nat.double(Nat.sub(B, 1n+R)), 1n+Nat.sub(1n, A)), zz), Nat.add(R1, Nat.mul(1n, B)), Nat.add(A, Nat.double(R)), Equal.trans(Nat, Nat.add(R1, Nat.mul(1n, B)), Nat.add(S, U.U32Nat.dbl(N, 0n)), Nat.add(A, Nat.double(R)), Equal.trans(Nat, Nat.add(R1, Nat.mul(1n, B)), Nat.add(S, U.U32Nat.dbl(N, Nat.mul(1n, 0n))), Nat.add(S, U.U32Nat.dbl(N, 0n)), er1, Equal.cong(Nat, Nat, zz => Nat.add(S, U.U32Nat.dbl(N, zz)), Nat.mul(1n, 0n), 0n, ur.r22())), eput))), ur.r30(Nat.sub(B, 1n+R), Nat.sub(1n, A), A, R)), Equal.cong(Nat, Nat, zz => Nat.add(1n+Nat.double(Nat.add(Nat.sub(B, 1n+R), R)), zz), Nat.add(Nat.sub(1n, A), A), 1n, Laws.nat_le_witness(A, 1n, hA))), ur.r7(Nat.sub(B, 1n+R), R)), Equal.cong(Nat, Nat, zz => Nat.double(zz), Nat.add(Nat.sub(B, 1n+R), 1n+R), B, Laws.nat_lt_witness(R, B, hR))), ur.r31(B))))), Laws.nat_lt_add(R1, Nat.add(Nat.double(Nat.sub(B, 1n+R)), Nat.sub(1n, A)))))
    case False{} True{} False{}:
      (Equal.trans(Nat, Nat.add(R1, Nat.mul(0n, B)), Nat.add(S, U.U32Nat.dbl(N, 0n)), Nat.add(A, Nat.double(R)), Equal.trans(Nat, Nat.add(R1, Nat.mul(0n, B)), Nat.add(S, U.U32Nat.dbl(N, Nat.mul(0n, 1n))), Nat.add(S, U.U32Nat.dbl(N, 0n)), er1, Equal.cong(Nat, Nat, zz => Nat.add(S, U.U32Nat.dbl(N, zz)), Nat.mul(0n, 1n), 0n, ur.r23())), eput), Equal.trans(Bool, Nat.is_lt(R1, B), Nat.is_lt(S, B), True{}, Equal.cong(Nat, Bool, zz => Nat.is_lt(zz, B), R1, S, Equal.trans(Nat, R1, Nat.add(S, U.U32Nat.dbl(N, Nat.mul(0n, 1n))), S, Equal.trans(Nat, R1, Nat.add(R1, Nat.mul(0n, B)), Nat.add(S, U.U32Nat.dbl(N, Nat.mul(0n, 1n))), ur.r24(R1, B), er1), ur.r25(S, N))), eL))
    case True{} _ False{}:
      Empty.absurd({Nat.add(R1, Nat.mul(U.U32Nat.bit(False{}), B)) == Nat.add(A, Nat.double(R)) : Nat} & {Nat.is_lt(R1, B) == True{} : Bool}, un.tf(eg))
    case False{} False{} False{}:
      Empty.absurd({Nat.add(R1, Nat.mul(U.U32Nat.bit(False{}), B)) == Nat.add(A, Nat.double(R)) : Nat} & {Nat.is_lt(R1, B) == True{} : Bool}, un.tf(eg))
    case False{} True{} True{}:
      Empty.absurd({Nat.add(R1, Nat.mul(U.U32Nat.bit(True{}), B)) == Nat.add(A, Nat.double(R)) : Nat} & {Nat.is_lt(R1, B) == True{} : Bool}, un.ft(eg))

def ur.r32(+x0: Nat) -> {Nat.mul(1n, x0) == x0 : Nat}:
  %Equal.sym(Nat, Nat.mul(1n, x0), x0, Laws.nat_one_mul(x0)) : {_ == x0 : Nat}
  {==}

def ur.r33(+x0: Nat) -> {x0 == Nat.mul(1n, x0) : Nat}:
  %Equal.sym(Nat, x0, Nat.mul(1n, x0), Equal.sym(Nat, Nat.mul(1n, x0), x0, Laws.nat_one_mul(x0))) : {_ == Nat.mul(1n, x0) : Nat}
  {==}

def ur.r34(+x0: Nat, +x1: Nat, +x2: Nat) -> {Nat.add(x0, Nat.mul(0n, x1)) == Nat.add(x0, U.U32Nat.dbl(32n, Nat.mul(0n, x2))) : Nat}:
  %Equal.sym(Nat, Nat.add(x0, 0n), x0, Laws.nat_add_zero(x0)) : {_ == Nat.add(x0, U.U32Nat.dbl(32n, Nat.mul(0n, x2))) : Nat}
  %Equal.sym(Nat, x0, Nat.add(x0, 0n), Equal.sym(Nat, Nat.add(x0, 0n), x0, Laws.nat_add_zero(x0))) : {_ == Nat.add(x0, U.U32Nat.dbl(32n, Nat.mul(0n, x2))) : Nat}
  %Equal.sym(Nat, 0n, U.U32Nat.dbl(32n, 0n), Equal.sym(Nat, U.U32Nat.dbl(32n, 0n), 0n, Laws.dbl_zero(32n))) : {Nat.add(x0, _) == Nat.add(x0, U.U32Nat.dbl(32n, Nat.mul(0n, x2))) : Nat}
  {==}

def ur.r35(+x0: Nat, +x1: Nat, +x2: Nat) -> {Nat.add(Nat.mul(1n+Nat.double(x0), x1), x2) == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}:
  %Equal.sym(Nat, Nat.double(x0), Nat.add(x0, x0), Laws.nat_double(x0)) : {Nat.add(Nat.mul(Nat.add(1n, _), x1), x2) == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(1n, Nat.add(x0, x0)), x1), Nat.add(Nat.mul(1n, x1), Nat.mul(Nat.add(x0, x0), x1)), Laws.nat_add_mul(1n, Nat.add(x0, x0), x1)) : {Nat.add(_, x2) == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(x0, x0), x1), Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1)), Laws.nat_add_mul(x0, x0, x1)) : {Nat.add(Nat.add(Nat.mul(1n, x1), _), x2) == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.mul(1n, x1), x1, Laws.nat_one_mul(x1)) : {Nat.add(Nat.add(_, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1))), x2) == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1))), Nat.add(Nat.mul(x0, x1), Nat.add(x1, Nat.mul(x0, x1))), Laws.nat_add_left_comm(x1, Nat.mul(x0, x1), Nat.mul(x0, x1))) : {Nat.add(_, x2) == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.mul(x0, x1)), Nat.add(Nat.mul(x0, x1), x1), Laws.nat_add_comm(x1, Nat.mul(x0, x1))) : {Nat.add(Nat.add(Nat.mul(x0, x1), _), x2) == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x1), x1)), x2), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.add(Nat.mul(x0, x1), x1), x2)), Laws.nat_add_assoc(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x1), x1), x2)) : {_ == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(x0, x1), x1), x2), Nat.add(Nat.mul(x0, x1), Nat.add(x1, x2)), Laws.nat_add_assoc(Nat.mul(x0, x1), x1, x2)) : {Nat.add(Nat.mul(x0, x1), _) == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x1), Nat.add(x1, x2)), Nat.add(x1, Nat.add(Nat.mul(x0, x1), x2)), Equal.sym(Nat, Nat.add(x1, Nat.add(Nat.mul(x0, x1), x2)), Nat.add(Nat.mul(x0, x1), Nat.add(x1, x2)), Laws.nat_add_left_comm(x1, Nat.mul(x0, x1), x2))) : {Nat.add(Nat.mul(x0, x1), _) == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x1), Nat.add(x1, Nat.add(Nat.mul(x0, x1), x2))), Nat.add(x1, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x1), x2))), Equal.sym(Nat, Nat.add(x1, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x1), x2))), Nat.add(Nat.mul(x0, x1), Nat.add(x1, Nat.add(Nat.mul(x0, x1), x2))), Laws.nat_add_left_comm(x1, Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x1), x2)))) : {_ == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x1), x2), Nat.add(x2, Nat.mul(x0, x1)), Equal.sym(Nat, Nat.add(x2, Nat.mul(x0, x1)), Nat.add(Nat.mul(x0, x1), x2), Laws.nat_add_comm(x2, Nat.mul(x0, x1)))) : {Nat.add(x1, Nat.add(Nat.mul(x0, x1), _)) == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x1), Nat.add(x2, Nat.mul(x0, x1))), Nat.add(x2, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1))), Equal.sym(Nat, Nat.add(x2, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1))), Nat.add(Nat.mul(x0, x1), Nat.add(x2, Nat.mul(x0, x1))), Laws.nat_add_left_comm(x2, Nat.mul(x0, x1), Nat.mul(x0, x1)))) : {Nat.add(x1, _) == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x2, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1)))), Nat.add(Nat.add(x1, x2), Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1))), Equal.sym(Nat, Nat.add(Nat.add(x1, x2), Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1))), Nat.add(x1, Nat.add(x2, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1)))), Laws.nat_add_assoc(x1, x2, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1))))) : {_ == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1)), Nat.double(Nat.mul(x0, x1)), Equal.sym(Nat, Nat.double(Nat.mul(x0, x1)), Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1)), Laws.nat_double(Nat.mul(x0, x1)))) : {Nat.add(Nat.add(x1, x2), _) == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, x2), Nat.add(x2, x1), Equal.sym(Nat, Nat.add(x2, x1), Nat.add(x1, x2), Laws.nat_add_comm(x2, x1))) : {Nat.add(_, Nat.double(Nat.mul(x0, x1))) == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, x1, Nat.mul(1n, x1), Equal.sym(Nat, Nat.mul(1n, x1), x1, Laws.nat_one_mul(x1))) : {Nat.add(Nat.add(x2, _), Nat.double(Nat.mul(x0, x1))) == Nat.add(Nat.add(x2, Nat.mul(1n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  {==}

def ur.r36(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat) -> {Nat.add(Nat.add(x0, Nat.double(x1)), Nat.double(Nat.mul(x2, x3))) == Nat.add(x0, Nat.double(Nat.add(Nat.mul(x2, x3), x1))) : Nat}:
  %Equal.sym(Nat, Nat.double(x1), Nat.add(x1, x1), Laws.nat_double(x1)) : {Nat.add(Nat.add(x0, _), Nat.double(Nat.mul(x2, x3))) == Nat.add(x0, Nat.double(Nat.add(Nat.mul(x2, x3), x1))) : Nat}
  %Equal.sym(Nat, Nat.double(Nat.mul(x2, x3)), Nat.add(Nat.mul(x2, x3), Nat.mul(x2, x3)), Laws.nat_double(Nat.mul(x2, x3))) : {Nat.add(Nat.add(x0, Nat.add(x1, x1)), _) == Nat.add(x0, Nat.double(Nat.add(Nat.mul(x2, x3), x1))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x1, x1)), Nat.add(Nat.mul(x2, x3), Nat.mul(x2, x3))), Nat.add(x0, Nat.add(Nat.add(x1, x1), Nat.add(Nat.mul(x2, x3), Nat.mul(x2, x3)))), Laws.nat_add_assoc(x0, Nat.add(x1, x1), Nat.add(Nat.mul(x2, x3), Nat.mul(x2, x3)))) : {_ == Nat.add(x0, Nat.double(Nat.add(Nat.mul(x2, x3), x1))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x1, x1), Nat.add(Nat.mul(x2, x3), Nat.mul(x2, x3))), Nat.add(x1, Nat.add(x1, Nat.add(Nat.mul(x2, x3), Nat.mul(x2, x3)))), Laws.nat_add_assoc(x1, x1, Nat.add(Nat.mul(x2, x3), Nat.mul(x2, x3)))) : {Nat.add(x0, _) == Nat.add(x0, Nat.double(Nat.add(Nat.mul(x2, x3), x1))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(Nat.mul(x2, x3), Nat.mul(x2, x3))), Nat.add(Nat.mul(x2, x3), Nat.add(x1, Nat.mul(x2, x3))), Equal.sym(Nat, Nat.add(Nat.mul(x2, x3), Nat.add(x1, Nat.mul(x2, x3))), Nat.add(x1, Nat.add(Nat.mul(x2, x3), Nat.mul(x2, x3))), Laws.nat_add_left_comm(Nat.mul(x2, x3), x1, Nat.mul(x2, x3)))) : {Nat.add(x0, Nat.add(x1, _)) == Nat.add(x0, Nat.double(Nat.add(Nat.mul(x2, x3), x1))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(Nat.mul(x2, x3), Nat.add(x1, Nat.mul(x2, x3)))), Nat.add(Nat.add(x1, Nat.mul(x2, x3)), Nat.add(x1, Nat.mul(x2, x3))), Equal.sym(Nat, Nat.add(Nat.add(x1, Nat.mul(x2, x3)), Nat.add(x1, Nat.mul(x2, x3))), Nat.add(x1, Nat.add(Nat.mul(x2, x3), Nat.add(x1, Nat.mul(x2, x3)))), Laws.nat_add_assoc(x1, Nat.mul(x2, x3), Nat.add(x1, Nat.mul(x2, x3))))) : {Nat.add(x0, _) == Nat.add(x0, Nat.double(Nat.add(Nat.mul(x2, x3), x1))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.mul(x2, x3)), Nat.add(Nat.mul(x2, x3), x1), Equal.sym(Nat, Nat.add(Nat.mul(x2, x3), x1), Nat.add(x1, Nat.mul(x2, x3)), Laws.nat_add_comm(Nat.mul(x2, x3), x1))) : {Nat.add(x0, Nat.add(Nat.add(x1, Nat.mul(x2, x3)), _)) == Nat.add(x0, Nat.double(Nat.add(Nat.mul(x2, x3), x1))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.mul(x2, x3)), Nat.add(Nat.mul(x2, x3), x1), Equal.sym(Nat, Nat.add(Nat.mul(x2, x3), x1), Nat.add(x1, Nat.mul(x2, x3)), Laws.nat_add_comm(Nat.mul(x2, x3), x1))) : {Nat.add(x0, Nat.add(_, Nat.add(Nat.mul(x2, x3), x1))) == Nat.add(x0, Nat.double(Nat.add(Nat.mul(x2, x3), x1))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(x2, x3), x1), Nat.add(Nat.mul(x2, x3), x1)), Nat.double(Nat.add(Nat.mul(x2, x3), x1)), Equal.sym(Nat, Nat.double(Nat.add(Nat.mul(x2, x3), x1)), Nat.add(Nat.add(Nat.mul(x2, x3), x1), Nat.add(Nat.mul(x2, x3), x1)), Laws.nat_double(Nat.add(Nat.mul(x2, x3), x1)))) : {Nat.add(x0, _) == Nat.add(x0, Nat.double(Nat.add(Nat.mul(x2, x3), x1))) : Nat}
  {==}

def ur.r37(+x0: Nat, +x1: Nat, +x2: Nat) -> {Nat.add(Nat.mul(Nat.double(x0), x1), x2) == Nat.add(Nat.add(x2, Nat.mul(0n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}:
  %Equal.sym(Nat, Nat.double(x0), Nat.add(x0, x0), Laws.nat_double(x0)) : {Nat.add(Nat.mul(_, x1), x2) == Nat.add(Nat.add(x2, Nat.mul(0n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(x0, x0), x1), Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1)), Laws.nat_add_mul(x0, x0, x1)) : {Nat.add(_, x2) == Nat.add(Nat.add(x2, Nat.mul(0n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1)), x2), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x1), x2)), Laws.nat_add_assoc(Nat.mul(x0, x1), Nat.mul(x0, x1), x2)) : {_ == Nat.add(Nat.add(x2, Nat.mul(0n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x1), x2), Nat.add(x2, Nat.mul(x0, x1)), Equal.sym(Nat, Nat.add(x2, Nat.mul(x0, x1)), Nat.add(Nat.mul(x0, x1), x2), Laws.nat_add_comm(x2, Nat.mul(x0, x1)))) : {Nat.add(Nat.mul(x0, x1), _) == Nat.add(Nat.add(x2, Nat.mul(0n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x1), Nat.add(x2, Nat.mul(x0, x1))), Nat.add(x2, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1))), Equal.sym(Nat, Nat.add(x2, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1))), Nat.add(Nat.mul(x0, x1), Nat.add(x2, Nat.mul(x0, x1))), Laws.nat_add_left_comm(x2, Nat.mul(x0, x1), Nat.mul(x0, x1)))) : {_ == Nat.add(Nat.add(x2, Nat.mul(0n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1)), Nat.double(Nat.mul(x0, x1)), Equal.sym(Nat, Nat.double(Nat.mul(x0, x1)), Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x1)), Laws.nat_double(Nat.mul(x0, x1)))) : {Nat.add(x2, _) == Nat.add(Nat.add(x2, Nat.mul(0n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  %Equal.sym(Nat, x2, Nat.add(x2, 0n), Equal.sym(Nat, Nat.add(x2, 0n), x2, Laws.nat_add_zero(x2))) : {Nat.add(_, Nat.double(Nat.mul(x0, x1))) == Nat.add(Nat.add(x2, Nat.mul(0n, x1)), Nat.double(Nat.mul(x0, x1))) : Nat}
  {==}

def ud.fin.t(+p: Nat, +q: Word(p), +bw: Word(32n), +a0: Bool, +rw: Word(32n), +x: Nat, +x2: Nat, +R1: Nat, +ex: {Nat.add(U.U32Nat.bit(a0), Nat.double(x)) == x2 : Nat}, +i1: {Nat.add(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)), Word.to_nat(32n, rw)) == x : Nat}, kp: {Nat.add(R1, Nat.mul(U.U32Nat.bit(True{}), Word.to_nat(32n, bw))) == Nat.add(U.U32Nat.bit(a0), Nat.double(Word.to_nat(32n, rw))) : Nat} & {Nat.is_lt(R1, Word.to_nat(32n, bw)) == True{} : Bool}) -> {Nat.add(Nat.mul(1n+Nat.double(Word.to_nat(p, q)), Word.to_nat(32n, bw)), R1) == x2 : Nat} & {Nat.is_lt(R1, Word.to_nat(32n, bw)) == True{} : Bool}:
  (+k1, +k2) = kp
  (Equal.trans(Nat, Nat.add(Nat.mul(1n+Nat.double(Word.to_nat(p, q)), Word.to_nat(32n, bw)), R1), Nat.add(U.U32Nat.bit(a0), Nat.double(x)), x2, Equal.trans(Nat, Nat.add(Nat.mul(1n+Nat.double(Word.to_nat(p, q)), Word.to_nat(32n, bw)), R1), Nat.add(U.U32Nat.bit(a0), Nat.double(Nat.add(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)), Word.to_nat(32n, rw)))), Nat.add(U.U32Nat.bit(a0), Nat.double(x)), Equal.trans(Nat, Nat.add(Nat.mul(1n+Nat.double(Word.to_nat(p, q)), Word.to_nat(32n, bw)), R1), Nat.add(Nat.add(U.U32Nat.bit(a0), Nat.double(Word.to_nat(32n, rw))), Nat.double(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)))), Nat.add(U.U32Nat.bit(a0), Nat.double(Nat.add(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)), Word.to_nat(32n, rw)))), Equal.trans(Nat, Nat.add(Nat.mul(1n+Nat.double(Word.to_nat(p, q)), Word.to_nat(32n, bw)), R1), Nat.add(Nat.add(R1, Nat.mul(1n, Word.to_nat(32n, bw))), Nat.double(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)))), Nat.add(Nat.add(U.U32Nat.bit(a0), Nat.double(Word.to_nat(32n, rw))), Nat.double(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)))), ur.r35(Word.to_nat(p, q), Word.to_nat(32n, bw), R1), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.double(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)))), Nat.add(R1, Nat.mul(1n, Word.to_nat(32n, bw))), Nat.add(U.U32Nat.bit(a0), Nat.double(Word.to_nat(32n, rw))), k1)), ur.r36(U.U32Nat.bit(a0), Word.to_nat(32n, rw), Word.to_nat(p, q), Word.to_nat(32n, bw))), Equal.cong(Nat, Nat, zz => Nat.add(U.U32Nat.bit(a0), Nat.double(zz)), Nat.add(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)), Word.to_nat(32n, rw)), x, i1)), ex), k2)

def ud.fin.f(+p: Nat, +q: Word(p), +bw: Word(32n), +a0: Bool, +rw: Word(32n), +x: Nat, +x2: Nat, +R1: Nat, +ex: {Nat.add(U.U32Nat.bit(a0), Nat.double(x)) == x2 : Nat}, +i1: {Nat.add(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)), Word.to_nat(32n, rw)) == x : Nat}, kp: {Nat.add(R1, Nat.mul(U.U32Nat.bit(False{}), Word.to_nat(32n, bw))) == Nat.add(U.U32Nat.bit(a0), Nat.double(Word.to_nat(32n, rw))) : Nat} & {Nat.is_lt(R1, Word.to_nat(32n, bw)) == True{} : Bool}) -> {Nat.add(Nat.mul(Nat.double(Word.to_nat(p, q)), Word.to_nat(32n, bw)), R1) == x2 : Nat} & {Nat.is_lt(R1, Word.to_nat(32n, bw)) == True{} : Bool}:
  (+k1, +k2) = kp
  (Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(Word.to_nat(p, q)), Word.to_nat(32n, bw)), R1), Nat.add(U.U32Nat.bit(a0), Nat.double(x)), x2, Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(Word.to_nat(p, q)), Word.to_nat(32n, bw)), R1), Nat.add(U.U32Nat.bit(a0), Nat.double(Nat.add(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)), Word.to_nat(32n, rw)))), Nat.add(U.U32Nat.bit(a0), Nat.double(x)), Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(Word.to_nat(p, q)), Word.to_nat(32n, bw)), R1), Nat.add(Nat.add(U.U32Nat.bit(a0), Nat.double(Word.to_nat(32n, rw))), Nat.double(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)))), Nat.add(U.U32Nat.bit(a0), Nat.double(Nat.add(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)), Word.to_nat(32n, rw)))), Equal.trans(Nat, Nat.add(Nat.mul(Nat.double(Word.to_nat(p, q)), Word.to_nat(32n, bw)), R1), Nat.add(Nat.add(R1, Nat.mul(0n, Word.to_nat(32n, bw))), Nat.double(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)))), Nat.add(Nat.add(U.U32Nat.bit(a0), Nat.double(Word.to_nat(32n, rw))), Nat.double(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)))), ur.r37(Word.to_nat(p, q), Word.to_nat(32n, bw), R1), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.double(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)))), Nat.add(R1, Nat.mul(0n, Word.to_nat(32n, bw))), Nat.add(U.U32Nat.bit(a0), Nat.double(Word.to_nat(32n, rw))), k1)), ur.r36(U.U32Nat.bit(a0), Word.to_nat(32n, rw), Word.to_nat(p, q), Word.to_nat(32n, bw))), Equal.cong(Nat, Nat, zz => Nat.add(U.U32Nat.bit(a0), Nat.double(zz)), Nat.add(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)), Word.to_nat(32n, rw)), x, i1)), ex), k2)

def ud.fin(+p: Nat, +q: Word(p), +s: Word(32n), +bw: Word(32n), +T: Bool, +g: Bool, +a0: Bool, +rw: Word(32n), +x: Nat, +x2: Nat, +eg: {Bool.or(T, U32.is_ge(U32{s}, U32{bw})) == g : Bool}, +eput: {Nat.add(Word.to_nat(32n, s), U.U32Nat.dbl(32n, U.U32Nat.bit(T))) == Nat.add(U.U32Nat.bit(a0), Nat.double(Word.to_nat(32n, rw))) : Nat}, +ex: {Nat.add(U.U32Nat.bit(a0), Nat.double(x)) == x2 : Nat}, +i1: {Nat.add(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)), Word.to_nat(32n, rw)) == x : Nat}, +i2: {Nat.is_lt(Word.to_nat(32n, rw), Word.to_nat(32n, bw)) == True{} : Bool}) -> {Nat.add(Nat.mul(ud.q(1n+p, U32.divmod.go.fin(p, q, U32{s}, U32{bw}, g)), U32.to_nat(U32{bw})), ud.r(1n+p, U32.divmod.go.fin(p, q, U32{s}, U32{bw}, g))) == x2 : Nat} & {Nat.is_lt(ud.r(1n+p, U32.divmod.go.fin(p, q, U32{s}, U32{bw}, g)), U32.to_nat(U32{bw})) == True{} : Bool}:
  match g:
    case True{}:
      ud.fin.t(p, q, bw, a0, rw, x, x2, U32.to_nat(U32.sub(U32{s}, U32{bw})), ex, i1, ud.k(32n, Word.to_nat(32n, s), Word.to_nat(32n, bw), Word.to_nat(32n, rw), U.U32Nat.bit(a0), U32.to_nat(U32.sub(U32{s}, U32{bw})), T, U32.is_lt(U32{s}, U32{bw}), True{}, eput, Equal.sym(Bool, U32.is_lt(U32{s}, U32{bw}), Nat.is_lt(Word.to_nat(32n, s), Word.to_nat(32n, bw)), Laws.u32_lt_value(U32{s}, U32{bw})), Equal.trans(Bool, Bool.or(T, Bool.not(U32.is_lt(U32{s}, U32{bw}))), Bool.or(T, U32.is_ge(U32{s}, U32{bw})), True{}, Equal.cong(Bool, Bool, zz => Bool.or(T, zz), Bool.not(U32.is_lt(U32{s}, U32{bw})), U32.is_ge(U32{s}, U32{bw}), Equal.sym(Bool, U32.is_ge(U32{s}, U32{bw}), Bool.not(U32.is_lt(U32{s}, U32{bw})), un.ge_lt(U32.cmp(U32{s}, U32{bw})))), eg), Equal.trans(Nat, Nat.add(U32.to_nat(U32.sub(U32{s}, U32{bw})), Nat.mul(1n, Word.to_nat(32n, bw))), Nat.add(Word.to_nat(32n, s), U.U32Nat.dbl(32n, U.U32Nat.bit(U32.is_lt(U32{s}, U32{bw})))), Nat.add(Word.to_nat(32n, s), U.U32Nat.dbl(32n, Nat.mul(1n, U.U32Nat.bit(U32.is_lt(U32{s}, U32{bw}))))), Equal.trans(Nat, Nat.add(U32.to_nat(U32.sub(U32{s}, U32{bw})), Nat.mul(1n, Word.to_nat(32n, bw))), Nat.add(U32.to_nat(U32.sub(U32{s}, U32{bw})), Word.to_nat(32n, bw)), Nat.add(Word.to_nat(32n, s), U.U32Nat.dbl(32n, U.U32Nat.bit(U32.is_lt(U32{s}, U32{bw})))), Equal.cong(Nat, Nat, zz => Nat.add(U32.to_nat(U32.sub(U32{s}, U32{bw})), zz), Nat.mul(1n, Word.to_nat(32n, bw)), Word.to_nat(32n, bw), ur.r32(Word.to_nat(32n, bw))), Laws.u32_sub_wrap(U32{s}, U32{bw})), Equal.cong(Nat, Nat, zz => Nat.add(Word.to_nat(32n, s), U.U32Nat.dbl(32n, zz)), U.U32Nat.bit(U32.is_lt(U32{s}, U32{bw})), Nat.mul(1n, U.U32Nat.bit(U32.is_lt(U32{s}, U32{bw}))), ur.r33(U.U32Nat.bit(U32.is_lt(U32{s}, U32{bw}))))), un.bit_le(a0), i2, Laws.word_value_lt(32n, bw)))
    case False{}:
      ud.fin.f(p, q, bw, a0, rw, x, x2, Word.to_nat(32n, s), ex, i1, ud.k(32n, Word.to_nat(32n, s), Word.to_nat(32n, bw), Word.to_nat(32n, rw), U.U32Nat.bit(a0), Word.to_nat(32n, s), T, U32.is_lt(U32{s}, U32{bw}), False{}, eput, Equal.sym(Bool, U32.is_lt(U32{s}, U32{bw}), Nat.is_lt(Word.to_nat(32n, s), Word.to_nat(32n, bw)), Laws.u32_lt_value(U32{s}, U32{bw})), Equal.trans(Bool, Bool.or(T, Bool.not(U32.is_lt(U32{s}, U32{bw}))), Bool.or(T, U32.is_ge(U32{s}, U32{bw})), False{}, Equal.cong(Bool, Bool, zz => Bool.or(T, zz), Bool.not(U32.is_lt(U32{s}, U32{bw})), U32.is_ge(U32{s}, U32{bw}), Equal.sym(Bool, U32.is_ge(U32{s}, U32{bw}), Bool.not(U32.is_lt(U32{s}, U32{bw})), un.ge_lt(U32.cmp(U32{s}, U32{bw})))), eg), ur.r34(Word.to_nat(32n, s), Word.to_nat(32n, bw), U.U32Nat.bit(U32.is_lt(U32{s}, U32{bw}))), un.bit_le(a0), i2, Laws.word_value_lt(32n, bw)))

def ud.step2(+p: Nat, +a0: Bool, +bw: Word(32n), +q: Word(p), +rw: Word(32n), +x: Nat, +x2: Nat, +ex: {Nat.add(U.U32Nat.bit(a0), Nat.double(x)) == x2 : Nat}, +i1: {Nat.add(Nat.mul(Word.to_nat(p, q), Word.to_nat(32n, bw)), Word.to_nat(32n, rw)) == x : Nat}, +i2: {Nat.is_lt(Word.to_nat(32n, rw), Word.to_nat(32n, bw)) == True{} : Bool}) -> {Nat.add(Nat.mul(ud.q(1n+p, U32.divmod.go.shl(p, q, U32{bw}, Word.shl.out(32n, a0, rw))), U32.to_nat(U32{bw})), ud.r(1n+p, U32.divmod.go.shl(p, q, U32{bw}, Word.shl.out(32n, a0, rw)))) == x2 : Nat} & {Nat.is_lt(ud.r(1n+p, U32.divmod.go.shl(p, q, U32{bw}, Word.shl.out(32n, a0, rw))), U32.to_nat(U32{bw})) == True{} : Bool}:
  %Equal.sym(Bool & Word(32n), Word.shl.out(32n, a0, rw), (un.topc(32n, a0, rw), Word.shl.put(32n, a0, rw)), un.so(32n, a0, rw)) : {Nat.add(Nat.mul(ud.q(1n+p, U32.divmod.go.shl(p, q, U32{bw}, _)), U32.to_nat(U32{bw})), ud.r(1n+p, U32.divmod.go.shl(p, q, U32{bw}, _))) == x2 : Nat} & {Nat.is_lt(ud.r(1n+p, U32.divmod.go.shl(p, q, U32{bw}, _)), U32.to_nat(U32{bw})) == True{} : Bool}
  ud.fin(p, q, Word.shl.put(32n, a0, rw), bw, un.topc(32n, a0, rw), Bool.or(un.topc(32n, a0, rw), U32.is_ge(U32{Word.shl.put(32n, a0, rw)}, U32{bw})), a0, rw, x, x2, {==}, un.putv(32n, a0, rw), ex, i1, i2)

def ud.step(+p: Nat, +a0: Bool, +b: U32, qr: Word(p) & U32, +x: Nat, +x2: Nat, +ex: {Nat.add(U.U32Nat.bit(a0), Nat.double(x)) == x2 : Nat}, ih: {Nat.add(Nat.mul(ud.q(p, qr), U32.to_nat(b)), ud.r(p, qr)) == x : Nat} & {Nat.is_lt(ud.r(p, qr), U32.to_nat(b)) == True{} : Bool}) -> {Nat.add(Nat.mul(ud.q(1n+p, U32.divmod.go.rec(p, a0, b, qr)), U32.to_nat(b)), ud.r(1n+p, U32.divmod.go.rec(p, a0, b, qr))) == x2 : Nat} & {Nat.is_lt(ud.r(1n+p, U32.divmod.go.rec(p, a0, b, qr)), U32.to_nat(b)) == True{} : Bool}:
  match b:
    case U32{+bw}:
      match qr:
        case (+q, +r):
          match r:
            case U32{+rw}:
              (+i1, +i2) = ih
              ud.step2(p, a0, bw, q, rw, x, x2, ex, i1, i2)

def ud.go(m: Nat, a: Word(m), +b: U32, +hb: {Nat.is_lt(0n, U32.to_nat(b)) == True{} : Bool}) -> {Nat.add(Nat.mul(ud.q(m, U32.divmod.go(m, a, b)), U32.to_nat(b)), ud.r(m, U32.divmod.go(m, a, b))) == Word.to_nat(m, a) : Nat} & {Nat.is_lt(ud.r(m, U32.divmod.go(m, a, b)), U32.to_nat(b)) == True{} : Bool}:
  match m a:
    case 0n WNil{}:
      ({==}, hb)
    case 1n+ +p WCon{+a0, +hi}:
      ud.step(p, a0, b, U32.divmod.go(p, hi, b), Word.to_nat(p, hi), Word.to_nat(1n+p, WCon{a0, hi}), Equal.sym(Nat, Word.to_nat(1n+p, WCon{a0, hi}), Nat.add(U.U32Nat.bit(a0), Nat.double(Word.to_nat(p, hi))), un.wc(p, a0, hi)), ud.go(p, hi, b, hb))

def ud.dq(G: Word(32n) & U32) -> {U32.to_nat(U32.div.fin(G)) == ud.q(32n, G) : Nat}:
  match G:
    case (q, r):
      {==}

def ud.dr(G: Word(32n) & U32) -> {U32.to_nat(U32.mod.fin(G)) == ud.r(32n, G) : Nat}:
  match G:
    case (q, r):
      {==}

def ud.nz(x: Nat, e: {Nat.is_eq(x, 0n) == False{} : Bool}) -> {Nat.is_lt(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, un.tf(e))
    case 1n+ +p:
      {==}

def ud.hb(+bw: Word(32n), h: {U32.is_zero(U32{bw}) == False{} : Bool}) -> {Nat.is_lt(0n, Word.to_nat(32n, bw)) == True{} : Bool}:
  ud.nz(Word.to_nat(32n, bw), Equal.trans(Bool, Nat.is_eq(Word.to_nat(32n, bw), 0n), U32.is_zero(U32{bw}), False{}, Equal.sym(Bool, U32.is_zero(U32{bw}), Nat.is_eq(Word.to_nat(32n, bw), 0n), Laws.u32_eq_value(U32{bw}, 0)), h))

def ud.dz2(+aw: Word(32n), +bw: Word(32n), G: Word(32n) & U32, iv: {Nat.add(Nat.mul(ud.q(32n, G), U32.to_nat(U32{bw})), ud.r(32n, G)) == Word.to_nat(32n, aw) : Nat} & {Nat.is_lt(ud.r(32n, G), U32.to_nat(U32{bw})) == True{} : Bool}) -> {Nat.add(Nat.mul(U32.to_nat(U32.div.fin(G)), Word.to_nat(32n, bw)), U32.to_nat(U32.mod.fin(G))) == Word.to_nat(32n, aw) : Nat} & {Nat.is_lt(U32.to_nat(U32.mod.fin(G)), Word.to_nat(32n, bw)) == True{} : Bool}:
  match G:
    case (q, r):
      iv

def ud.dz(+aw: Word(32n), +bw: Word(32n), z: Bool, ez: {U32.is_zero(U32{bw}) == z : Bool}, h: {U32.is_zero(U32{bw}) == False{} : Bool}) -> {Nat.add(Nat.mul(U32.to_nat(U32.div.if(aw, U32{bw}, z)), Word.to_nat(32n, bw)), U32.to_nat(U32.mod.if(aw, U32{bw}, z))) == Word.to_nat(32n, aw) : Nat} & {Nat.is_lt(U32.to_nat(U32.mod.if(aw, U32{bw}, z)), Word.to_nat(32n, bw)) == True{} : Bool}:
  match z:
    case True{}:
      Empty.absurd({Nat.add(Nat.mul(U32.to_nat(U32.div.if(aw, U32{bw}, True{})), Word.to_nat(32n, bw)), U32.to_nat(U32.mod.if(aw, U32{bw}, True{}))) == Word.to_nat(32n, aw) : Nat} & {Nat.is_lt(U32.to_nat(U32.mod.if(aw, U32{bw}, True{})), Word.to_nat(32n, bw)) == True{} : Bool}, un.tf(Equal.trans(Bool, True{}, U32.is_zero(U32{bw}), False{}, Equal.sym(Bool, U32.is_zero(U32{bw}), True{}, ez), h)))
    case False{}:
      ud.dz2(aw, bw, U32.divmod.go(32n, aw, U32{bw}), ud.go(32n, aw, U32{bw}, ud.hb(bw, h)))

def ud.p1(-x: Nat, -y: Nat, -c: Nat, -d: Nat, pr: {x == y : Nat} & {Nat.is_lt(c, d) == True{} : Bool}) -> {x == y : Nat}:
  (+a, +b) = pr
  a

def ud.p2(-x: Nat, -y: Nat, -c: Nat, -d: Nat, pr: {x == y : Nat} & {Nat.is_lt(c, d) == True{} : Bool}) -> {Nat.is_lt(c, d) == True{} : Bool}:
  (+a, +b) = pr
  b

def Laws.u32_divmod(a, b, h):
  match a b:
    case U32{+aw} U32{+bw}:
      ud.p1(Nat.add(Nat.mul(U32.to_nat(U32.div.if(aw, U32{bw}, U32.is_zero(U32{bw}))), Word.to_nat(32n, bw)), U32.to_nat(U32.mod.if(aw, U32{bw}, U32.is_zero(U32{bw})))), Word.to_nat(32n, aw), U32.to_nat(U32.mod.if(aw, U32{bw}, U32.is_zero(U32{bw}))), Word.to_nat(32n, bw), ud.dz(aw, bw, U32.is_zero(U32{bw}), {==}, h))

def Laws.u32_mod_lt(a, b, h):
  match a b:
    case U32{+aw} U32{+bw}:
      ud.p2(Nat.add(Nat.mul(U32.to_nat(U32.div.if(aw, U32{bw}, U32.is_zero(U32{bw}))), Word.to_nat(32n, bw)), U32.to_nat(U32.mod.if(aw, U32{bw}, U32.is_zero(U32{bw})))), Word.to_nat(32n, aw), U32.to_nat(U32.mod.if(aw, U32{bw}, U32.is_zero(U32{bw}))), Word.to_nat(32n, bw), ud.dz(aw, bw, U32.is_zero(U32{bw}), {==}, h))

def Laws.u32_div_zero(a):
  match a:
    case U32{+aw}:
      {==}

def Laws.u32_mod_zero(a):
  match a:
    case U32{+aw}:
      {==}

# The bitwise operations

def un.band_comm(x: Bool, y: Bool) -> {Bool.and(x, y) == Bool.and(y, x) : Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def un.bor_comm(x: Bool, y: Bool) -> {Bool.or(x, y) == Bool.or(y, x) : Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def un.bxor_comm(x: Bool, y: Bool) -> {Bool.xor(x, y) == Bool.xor(y, x) : Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def un.bao(x: Bool, y: Bool) -> {Nat.add(U.U32Nat.bit(Bool.and(x, y)), U.U32Nat.bit(Bool.or(x, y))) == Nat.add(U.U32Nat.bit(x), U.U32Nat.bit(y)) : Nat}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def un.bxa(x: Bool, y: Bool) -> {Nat.add(U.U32Nat.bit(Bool.xor(x, y)), Nat.double(U.U32Nat.bit(Bool.and(x, y)))) == Nat.add(U.U32Nat.bit(x), U.U32Nat.bit(y)) : Nat}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def un.band_t(x: Bool) -> {Bool.and(x, True{}) == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def un.band_f(x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def un.bor_f(x: Bool) -> {Bool.or(x, False{}) == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.word_and_comm(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          un.wcon_eq(p, Bool.and(x, y), Bool.and(y, x), Word.and(p, at, bt), Word.and(p, bt, at), un.band_comm(x, y), Laws.word_and_comm(p, at, bt))

def Laws.u32_and_comm(a, b):
  match a b:
    case U32{+x} U32{+y}:
      un.u32_cong(Word.and(32n, x, y), Word.and(32n, y, x), Laws.word_and_comm(32n, x, y))

def Laws.word_or_comm(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          un.wcon_eq(p, Bool.or(x, y), Bool.or(y, x), Word.or(p, at, bt), Word.or(p, bt, at), un.bor_comm(x, y), Laws.word_or_comm(p, at, bt))

def Laws.u32_or_comm(a, b):
  match a b:
    case U32{+x} U32{+y}:
      un.u32_cong(Word.or(32n, x, y), Word.or(32n, y, x), Laws.word_or_comm(32n, x, y))

def Laws.word_xor_comm(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          un.wcon_eq(p, Bool.xor(x, y), Bool.xor(y, x), Word.xor(p, at, bt), Word.xor(p, bt, at), un.bxor_comm(x, y), Laws.word_xor_comm(p, at, bt))

def Laws.u32_xor_comm(a, b):
  match a b:
    case U32{+x} U32{+y}:
      un.u32_cong(Word.xor(32n, x, y), Word.xor(32n, y, x), Laws.word_xor_comm(32n, x, y))

def ur.r38(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat) -> {Nat.add(Nat.add(x0, Nat.double(x1)), Nat.add(x2, Nat.double(x3))) == Nat.add(Nat.add(x0, x2), Nat.double(Nat.add(x1, x3))) : Nat}:
  %Equal.sym(Nat, Nat.double(x1), Nat.add(x1, x1), Laws.nat_double(x1)) : {Nat.add(Nat.add(x0, _), Nat.add(x2, Nat.double(x3))) == Nat.add(Nat.add(x0, x2), Nat.double(Nat.add(x1, x3))) : Nat}
  %Equal.sym(Nat, Nat.double(x3), Nat.add(x3, x3), Laws.nat_double(x3)) : {Nat.add(Nat.add(x0, Nat.add(x1, x1)), Nat.add(x2, _)) == Nat.add(Nat.add(x0, x2), Nat.double(Nat.add(x1, x3))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x1, x1)), Nat.add(x2, Nat.add(x3, x3))), Nat.add(x0, Nat.add(Nat.add(x1, x1), Nat.add(x2, Nat.add(x3, x3)))), Laws.nat_add_assoc(x0, Nat.add(x1, x1), Nat.add(x2, Nat.add(x3, x3)))) : {_ == Nat.add(Nat.add(x0, x2), Nat.double(Nat.add(x1, x3))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x1, x1), Nat.add(x2, Nat.add(x3, x3))), Nat.add(x1, Nat.add(x1, Nat.add(x2, Nat.add(x3, x3)))), Laws.nat_add_assoc(x1, x1, Nat.add(x2, Nat.add(x3, x3)))) : {Nat.add(x0, _) == Nat.add(Nat.add(x0, x2), Nat.double(Nat.add(x1, x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x2, Nat.add(x3, x3))), Nat.add(x2, Nat.add(x1, Nat.add(x3, x3))), Equal.sym(Nat, Nat.add(x2, Nat.add(x1, Nat.add(x3, x3))), Nat.add(x1, Nat.add(x2, Nat.add(x3, x3))), Laws.nat_add_left_comm(x2, x1, Nat.add(x3, x3)))) : {Nat.add(x0, Nat.add(x1, _)) == Nat.add(Nat.add(x0, x2), Nat.double(Nat.add(x1, x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x2, Nat.add(x1, Nat.add(x3, x3)))), Nat.add(x2, Nat.add(x1, Nat.add(x1, Nat.add(x3, x3)))), Equal.sym(Nat, Nat.add(x2, Nat.add(x1, Nat.add(x1, Nat.add(x3, x3)))), Nat.add(x1, Nat.add(x2, Nat.add(x1, Nat.add(x3, x3)))), Laws.nat_add_left_comm(x2, x1, Nat.add(x1, Nat.add(x3, x3))))) : {Nat.add(x0, _) == Nat.add(Nat.add(x0, x2), Nat.double(Nat.add(x1, x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x2, Nat.add(x1, Nat.add(x1, Nat.add(x3, x3))))), Nat.add(Nat.add(x0, x2), Nat.add(x1, Nat.add(x1, Nat.add(x3, x3)))), Equal.sym(Nat, Nat.add(Nat.add(x0, x2), Nat.add(x1, Nat.add(x1, Nat.add(x3, x3)))), Nat.add(x0, Nat.add(x2, Nat.add(x1, Nat.add(x1, Nat.add(x3, x3))))), Laws.nat_add_assoc(x0, x2, Nat.add(x1, Nat.add(x1, Nat.add(x3, x3)))))) : {_ == Nat.add(Nat.add(x0, x2), Nat.double(Nat.add(x1, x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x3, x3)), Nat.add(x3, Nat.add(x1, x3)), Equal.sym(Nat, Nat.add(x3, Nat.add(x1, x3)), Nat.add(x1, Nat.add(x3, x3)), Laws.nat_add_left_comm(x3, x1, x3))) : {Nat.add(Nat.add(x0, x2), Nat.add(x1, _)) == Nat.add(Nat.add(x0, x2), Nat.double(Nat.add(x1, x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x3, Nat.add(x1, x3))), Nat.add(Nat.add(x1, x3), Nat.add(x1, x3)), Equal.sym(Nat, Nat.add(Nat.add(x1, x3), Nat.add(x1, x3)), Nat.add(x1, Nat.add(x3, Nat.add(x1, x3))), Laws.nat_add_assoc(x1, x3, Nat.add(x1, x3)))) : {Nat.add(Nat.add(x0, x2), _) == Nat.add(Nat.add(x0, x2), Nat.double(Nat.add(x1, x3))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x1, x3), Nat.add(x1, x3)), Nat.double(Nat.add(x1, x3)), Equal.sym(Nat, Nat.double(Nat.add(x1, x3)), Nat.add(Nat.add(x1, x3), Nat.add(x1, x3)), Laws.nat_double(Nat.add(x1, x3)))) : {Nat.add(Nat.add(x0, x2), _) == Nat.add(Nat.add(x0, x2), Nat.double(Nat.add(x1, x3))) : Nat}
  {==}

def ur.r39(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat) -> {Nat.add(Nat.add(x0, x1), Nat.double(Nat.add(x2, x3))) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.add(x1, Nat.double(x3))) : Nat}:
  %Equal.sym(Nat, Nat.double(Nat.add(x2, x3)), Nat.add(Nat.add(x2, x3), Nat.add(x2, x3)), Laws.nat_double(Nat.add(x2, x3))) : {Nat.add(Nat.add(x0, x1), _) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.add(x1, Nat.double(x3))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x2, x3), Nat.add(x2, x3)), Nat.add(x2, Nat.add(x3, Nat.add(x2, x3))), Laws.nat_add_assoc(x2, x3, Nat.add(x2, x3))) : {Nat.add(Nat.add(x0, x1), _) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.add(x1, Nat.double(x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x3, Nat.add(x2, x3)), Nat.add(x2, Nat.add(x3, x3)), Laws.nat_add_left_comm(x3, x2, x3)) : {Nat.add(Nat.add(x0, x1), Nat.add(x2, _)) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.add(x1, Nat.double(x3))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, x1), Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), Nat.add(x0, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))), Laws.nat_add_assoc(x0, x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3))))) : {_ == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.add(x1, Nat.double(x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), Nat.add(x2, Nat.add(x1, Nat.add(x2, Nat.add(x3, x3)))), Equal.sym(Nat, Nat.add(x2, Nat.add(x1, Nat.add(x2, Nat.add(x3, x3)))), Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, x3)))), Laws.nat_add_left_comm(x2, x1, Nat.add(x2, Nat.add(x3, x3))))) : {Nat.add(x0, _) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.add(x1, Nat.double(x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x2, Nat.add(x3, x3))), Nat.add(x2, Nat.add(x1, Nat.add(x3, x3))), Equal.sym(Nat, Nat.add(x2, Nat.add(x1, Nat.add(x3, x3))), Nat.add(x1, Nat.add(x2, Nat.add(x3, x3))), Laws.nat_add_left_comm(x2, x1, Nat.add(x3, x3)))) : {Nat.add(x0, Nat.add(x2, _)) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.add(x1, Nat.double(x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(x2, Nat.add(x1, Nat.add(x3, x3)))), Nat.add(Nat.add(x2, x2), Nat.add(x1, Nat.add(x3, x3))), Equal.sym(Nat, Nat.add(Nat.add(x2, x2), Nat.add(x1, Nat.add(x3, x3))), Nat.add(x2, Nat.add(x2, Nat.add(x1, Nat.add(x3, x3)))), Laws.nat_add_assoc(x2, x2, Nat.add(x1, Nat.add(x3, x3))))) : {Nat.add(x0, _) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.add(x1, Nat.double(x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(Nat.add(x2, x2), Nat.add(x1, Nat.add(x3, x3)))), Nat.add(Nat.add(x0, Nat.add(x2, x2)), Nat.add(x1, Nat.add(x3, x3))), Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x2, x2)), Nat.add(x1, Nat.add(x3, x3))), Nat.add(x0, Nat.add(Nat.add(x2, x2), Nat.add(x1, Nat.add(x3, x3)))), Laws.nat_add_assoc(x0, Nat.add(x2, x2), Nat.add(x1, Nat.add(x3, x3))))) : {_ == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.add(x1, Nat.double(x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x3, x3), Nat.double(x3), Equal.sym(Nat, Nat.double(x3), Nat.add(x3, x3), Laws.nat_double(x3))) : {Nat.add(Nat.add(x0, Nat.add(x2, x2)), Nat.add(x1, _)) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.add(x1, Nat.double(x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x2, x2), Nat.double(x2), Equal.sym(Nat, Nat.double(x2), Nat.add(x2, x2), Laws.nat_double(x2))) : {Nat.add(Nat.add(x0, _), Nat.add(x1, Nat.double(x3))) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.add(x1, Nat.double(x3))) : Nat}
  {==}

def Laws.word_and_or(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}), Word.to_nat(1n+p, WCon{Bool.or(x, y), Word.or(p, at, bt)})), Nat.add(Word.to_nat(1n+p, WCon{x, at}), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt)))), Nat.add(Word.to_nat(1n+p, WCon{x, at}), Word.to_nat(1n+p, WCon{y, bt})), Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}), Word.to_nat(1n+p, WCon{Bool.or(x, y), Word.or(p, at, bt)})), Nat.add(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, at))), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt)))), Nat.add(Word.to_nat(1n+p, WCon{x, at}), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt)))), Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}), Word.to_nat(1n+p, WCon{Bool.or(x, y), Word.or(p, at, bt)})), Nat.add(Nat.add(U.U32Nat.bit(x), U.U32Nat.bit(y)), Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)))), Nat.add(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, at))), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt)))), Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}), Word.to_nat(1n+p, WCon{Bool.or(x, y), Word.or(p, at, bt)})), Nat.add(Nat.add(U.U32Nat.bit(Bool.and(x, y)), U.U32Nat.bit(Bool.or(x, y))), Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)))), Nat.add(Nat.add(U.U32Nat.bit(x), U.U32Nat.bit(y)), Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)))), Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}), Word.to_nat(1n+p, WCon{Bool.or(x, y), Word.or(p, at, bt)})), Nat.add(Nat.add(U.U32Nat.bit(Bool.and(x, y)), U.U32Nat.bit(Bool.or(x, y))), Nat.double(Nat.add(Word.to_nat(p, Word.and(p, at, bt)), Word.to_nat(p, Word.or(p, at, bt))))), Nat.add(Nat.add(U.U32Nat.bit(Bool.and(x, y)), U.U32Nat.bit(Bool.or(x, y))), Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)))), Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}), Word.to_nat(1n+p, WCon{Bool.or(x, y), Word.or(p, at, bt)})), Nat.add(Nat.add(U.U32Nat.bit(Bool.and(x, y)), Nat.double(Word.to_nat(p, Word.and(p, at, bt)))), Nat.add(U.U32Nat.bit(Bool.or(x, y)), Nat.double(Word.to_nat(p, Word.or(p, at, bt))))), Nat.add(Nat.add(U.U32Nat.bit(Bool.and(x, y)), U.U32Nat.bit(Bool.or(x, y))), Nat.double(Nat.add(Word.to_nat(p, Word.and(p, at, bt)), Word.to_nat(p, Word.or(p, at, bt))))), Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}), Word.to_nat(1n+p, WCon{Bool.or(x, y), Word.or(p, at, bt)})), Nat.add(Nat.add(U.U32Nat.bit(Bool.and(x, y)), Nat.double(Word.to_nat(p, Word.and(p, at, bt)))), Word.to_nat(1n+p, WCon{Bool.or(x, y), Word.or(p, at, bt)})), Nat.add(Nat.add(U.U32Nat.bit(Bool.and(x, y)), Nat.double(Word.to_nat(p, Word.and(p, at, bt)))), Nat.add(U.U32Nat.bit(Bool.or(x, y)), Nat.double(Word.to_nat(p, Word.or(p, at, bt))))), Equal.cong(Nat, Nat, zz => Nat.add(zz, Word.to_nat(1n+p, WCon{Bool.or(x, y), Word.or(p, at, bt)})), Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}), Nat.add(U.U32Nat.bit(Bool.and(x, y)), Nat.double(Word.to_nat(p, Word.and(p, at, bt)))), un.wc(p, Bool.and(x, y), Word.and(p, at, bt))), Equal.cong(Nat, Nat, zz => Nat.add(Nat.add(U.U32Nat.bit(Bool.and(x, y)), Nat.double(Word.to_nat(p, Word.and(p, at, bt)))), zz), Word.to_nat(1n+p, WCon{Bool.or(x, y), Word.or(p, at, bt)}), Nat.add(U.U32Nat.bit(Bool.or(x, y)), Nat.double(Word.to_nat(p, Word.or(p, at, bt)))), un.wc(p, Bool.or(x, y), Word.or(p, at, bt)))), ur.r38(U.U32Nat.bit(Bool.and(x, y)), Word.to_nat(p, Word.and(p, at, bt)), U.U32Nat.bit(Bool.or(x, y)), Word.to_nat(p, Word.or(p, at, bt)))), Equal.cong(Nat, Nat, zz => Nat.add(Nat.add(U.U32Nat.bit(Bool.and(x, y)), U.U32Nat.bit(Bool.or(x, y))), Nat.double(zz)), Nat.add(Word.to_nat(p, Word.and(p, at, bt)), Word.to_nat(p, Word.or(p, at, bt))), Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)), Laws.word_and_or(p, at, bt))), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)))), Nat.add(U.U32Nat.bit(Bool.and(x, y)), U.U32Nat.bit(Bool.or(x, y))), Nat.add(U.U32Nat.bit(x), U.U32Nat.bit(y)), un.bao(x, y))), ur.r39(U.U32Nat.bit(x), U.U32Nat.bit(y), Word.to_nat(p, at), Word.to_nat(p, bt))), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt)))), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, at))), Word.to_nat(1n+p, WCon{x, at}), Equal.sym(Nat, Word.to_nat(1n+p, WCon{x, at}), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, at))), un.wc(p, x, at)))), Equal.cong(Nat, Nat, zz => Nat.add(Word.to_nat(1n+p, WCon{x, at}), zz), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt))), Word.to_nat(1n+p, WCon{y, bt}), Equal.sym(Nat, Word.to_nat(1n+p, WCon{y, bt}), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt))), un.wc(p, y, bt))))

def ur.r40(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat) -> {Nat.add(Nat.add(x0, Nat.double(x1)), Nat.double(Nat.add(x2, Nat.double(x3)))) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}:
  %Equal.sym(Nat, Nat.double(x1), Nat.add(x1, x1), Laws.nat_double(x1)) : {Nat.add(Nat.add(x0, _), Nat.double(Nat.add(x2, Nat.double(x3)))) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.double(Nat.add(x2, Nat.double(x3))), Nat.add(Nat.add(x2, Nat.double(x3)), Nat.add(x2, Nat.double(x3))), Laws.nat_double(Nat.add(x2, Nat.double(x3)))) : {Nat.add(Nat.add(x0, Nat.add(x1, x1)), _) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.double(x3), Nat.add(x3, x3), Laws.nat_double(x3)) : {Nat.add(Nat.add(x0, Nat.add(x1, x1)), Nat.add(Nat.add(x2, _), Nat.add(x2, Nat.double(x3)))) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.double(x3), Nat.add(x3, x3), Laws.nat_double(x3)) : {Nat.add(Nat.add(x0, Nat.add(x1, x1)), Nat.add(Nat.add(x2, Nat.add(x3, x3)), Nat.add(x2, _))) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x2, Nat.add(x3, x3)), Nat.add(x2, Nat.add(x3, x3))), Nat.add(x2, Nat.add(Nat.add(x3, x3), Nat.add(x2, Nat.add(x3, x3)))), Laws.nat_add_assoc(x2, Nat.add(x3, x3), Nat.add(x2, Nat.add(x3, x3)))) : {Nat.add(Nat.add(x0, Nat.add(x1, x1)), _) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x3, x3), Nat.add(x2, Nat.add(x3, x3))), Nat.add(x3, Nat.add(x3, Nat.add(x2, Nat.add(x3, x3)))), Laws.nat_add_assoc(x3, x3, Nat.add(x2, Nat.add(x3, x3)))) : {Nat.add(Nat.add(x0, Nat.add(x1, x1)), Nat.add(x2, _)) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x3, Nat.add(x2, Nat.add(x3, x3))), Nat.add(x2, Nat.add(x3, Nat.add(x3, x3))), Laws.nat_add_left_comm(x3, x2, Nat.add(x3, x3))) : {Nat.add(Nat.add(x0, Nat.add(x1, x1)), Nat.add(x2, Nat.add(x3, _))) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x3, Nat.add(x2, Nat.add(x3, Nat.add(x3, x3)))), Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))), Laws.nat_add_left_comm(x3, x2, Nat.add(x3, Nat.add(x3, x3)))) : {Nat.add(Nat.add(x0, Nat.add(x1, x1)), Nat.add(x2, _)) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x1, x1)), Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))), Nat.add(x0, Nat.add(Nat.add(x1, x1), Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))))), Laws.nat_add_assoc(x0, Nat.add(x1, x1), Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))))) : {_ == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x1, x1), Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))), Nat.add(x1, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))))), Laws.nat_add_assoc(x1, x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))))) : {Nat.add(x0, _) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))), Nat.add(x2, Nat.add(x1, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))), Equal.sym(Nat, Nat.add(x2, Nat.add(x1, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))), Nat.add(x1, Nat.add(x2, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))), Laws.nat_add_left_comm(x2, x1, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))))) : {Nat.add(x0, Nat.add(x1, _)) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x2, Nat.add(x1, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))))), Nat.add(x2, Nat.add(x1, Nat.add(x1, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))))), Equal.sym(Nat, Nat.add(x2, Nat.add(x1, Nat.add(x1, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))))), Nat.add(x1, Nat.add(x2, Nat.add(x1, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))))), Laws.nat_add_left_comm(x2, x1, Nat.add(x1, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))))) : {Nat.add(x0, _) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))), Nat.add(x2, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))), Equal.sym(Nat, Nat.add(x2, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))), Nat.add(x1, Nat.add(x2, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))), Laws.nat_add_left_comm(x2, x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))) : {Nat.add(x0, Nat.add(x2, Nat.add(x1, _))) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x2, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))), Nat.add(x2, Nat.add(x1, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))), Equal.sym(Nat, Nat.add(x2, Nat.add(x1, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))), Nat.add(x1, Nat.add(x2, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))), Laws.nat_add_left_comm(x2, x1, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))))) : {Nat.add(x0, Nat.add(x2, _)) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(x2, Nat.add(x1, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))))), Nat.add(Nat.add(x2, x2), Nat.add(x1, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))), Equal.sym(Nat, Nat.add(Nat.add(x2, x2), Nat.add(x1, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))), Nat.add(x2, Nat.add(x2, Nat.add(x1, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))))), Laws.nat_add_assoc(x2, x2, Nat.add(x1, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))))) : {Nat.add(x0, _) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(Nat.add(x2, x2), Nat.add(x1, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))))), Nat.add(Nat.add(x0, Nat.add(x2, x2)), Nat.add(x1, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))), Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(x2, x2)), Nat.add(x1, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))), Nat.add(x0, Nat.add(Nat.add(x2, x2), Nat.add(x1, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3))))))), Laws.nat_add_assoc(x0, Nat.add(x2, x2), Nat.add(x1, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))))))) : {_ == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))), Nat.add(x3, Nat.add(x1, Nat.add(x3, Nat.add(x3, x3)))), Equal.sym(Nat, Nat.add(x3, Nat.add(x1, Nat.add(x3, Nat.add(x3, x3)))), Nat.add(x1, Nat.add(x3, Nat.add(x3, Nat.add(x3, x3)))), Laws.nat_add_left_comm(x3, x1, Nat.add(x3, Nat.add(x3, x3))))) : {Nat.add(Nat.add(x0, Nat.add(x2, x2)), Nat.add(x1, _)) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x3, Nat.add(x3, x3))), Nat.add(x3, Nat.add(x1, Nat.add(x3, x3))), Equal.sym(Nat, Nat.add(x3, Nat.add(x1, Nat.add(x3, x3))), Nat.add(x1, Nat.add(x3, Nat.add(x3, x3))), Laws.nat_add_left_comm(x3, x1, Nat.add(x3, x3)))) : {Nat.add(Nat.add(x0, Nat.add(x2, x2)), Nat.add(x1, Nat.add(x3, _))) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x3, Nat.add(x3, Nat.add(x1, Nat.add(x3, x3)))), Nat.add(Nat.add(x3, x3), Nat.add(x1, Nat.add(x3, x3))), Equal.sym(Nat, Nat.add(Nat.add(x3, x3), Nat.add(x1, Nat.add(x3, x3))), Nat.add(x3, Nat.add(x3, Nat.add(x1, Nat.add(x3, x3)))), Laws.nat_add_assoc(x3, x3, Nat.add(x1, Nat.add(x3, x3))))) : {Nat.add(Nat.add(x0, Nat.add(x2, x2)), Nat.add(x1, _)) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(Nat.add(x3, x3), Nat.add(x1, Nat.add(x3, x3)))), Nat.add(Nat.add(x1, Nat.add(x3, x3)), Nat.add(x1, Nat.add(x3, x3))), Equal.sym(Nat, Nat.add(Nat.add(x1, Nat.add(x3, x3)), Nat.add(x1, Nat.add(x3, x3))), Nat.add(x1, Nat.add(Nat.add(x3, x3), Nat.add(x1, Nat.add(x3, x3)))), Laws.nat_add_assoc(x1, Nat.add(x3, x3), Nat.add(x1, Nat.add(x3, x3))))) : {Nat.add(Nat.add(x0, Nat.add(x2, x2)), _) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x3, x3), Nat.double(x3), Equal.sym(Nat, Nat.double(x3), Nat.add(x3, x3), Laws.nat_double(x3))) : {Nat.add(Nat.add(x0, Nat.add(x2, x2)), Nat.add(Nat.add(x1, Nat.add(x3, x3)), Nat.add(x1, _))) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x3, x3), Nat.double(x3), Equal.sym(Nat, Nat.double(x3), Nat.add(x3, x3), Laws.nat_double(x3))) : {Nat.add(Nat.add(x0, Nat.add(x2, x2)), Nat.add(Nat.add(x1, _), Nat.add(x1, Nat.double(x3)))) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x1, Nat.double(x3)), Nat.add(x1, Nat.double(x3))), Nat.double(Nat.add(x1, Nat.double(x3))), Equal.sym(Nat, Nat.double(Nat.add(x1, Nat.double(x3))), Nat.add(Nat.add(x1, Nat.double(x3)), Nat.add(x1, Nat.double(x3))), Laws.nat_double(Nat.add(x1, Nat.double(x3))))) : {Nat.add(Nat.add(x0, Nat.add(x2, x2)), _) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  %Equal.sym(Nat, Nat.add(x2, x2), Nat.double(x2), Equal.sym(Nat, Nat.double(x2), Nat.add(x2, x2), Laws.nat_double(x2))) : {Nat.add(Nat.add(x0, _), Nat.double(Nat.add(x1, Nat.double(x3)))) == Nat.add(Nat.add(x0, Nat.double(x2)), Nat.double(Nat.add(x1, Nat.double(x3)))) : Nat}
  {==}

def Laws.word_xor_and(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{Bool.xor(x, y), Word.xor(p, at, bt)}), Nat.double(Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}))), Nat.add(Word.to_nat(1n+p, WCon{x, at}), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt)))), Nat.add(Word.to_nat(1n+p, WCon{x, at}), Word.to_nat(1n+p, WCon{y, bt})), Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{Bool.xor(x, y), Word.xor(p, at, bt)}), Nat.double(Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}))), Nat.add(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, at))), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt)))), Nat.add(Word.to_nat(1n+p, WCon{x, at}), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt)))), Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{Bool.xor(x, y), Word.xor(p, at, bt)}), Nat.double(Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}))), Nat.add(Nat.add(U.U32Nat.bit(x), U.U32Nat.bit(y)), Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)))), Nat.add(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, at))), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt)))), Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{Bool.xor(x, y), Word.xor(p, at, bt)}), Nat.double(Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}))), Nat.add(Nat.add(U.U32Nat.bit(Bool.xor(x, y)), Nat.double(U.U32Nat.bit(Bool.and(x, y)))), Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)))), Nat.add(Nat.add(U.U32Nat.bit(x), U.U32Nat.bit(y)), Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)))), Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{Bool.xor(x, y), Word.xor(p, at, bt)}), Nat.double(Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}))), Nat.add(Nat.add(U.U32Nat.bit(Bool.xor(x, y)), Nat.double(U.U32Nat.bit(Bool.and(x, y)))), Nat.double(Nat.add(Word.to_nat(p, Word.xor(p, at, bt)), Nat.double(Word.to_nat(p, Word.and(p, at, bt)))))), Nat.add(Nat.add(U.U32Nat.bit(Bool.xor(x, y)), Nat.double(U.U32Nat.bit(Bool.and(x, y)))), Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)))), Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{Bool.xor(x, y), Word.xor(p, at, bt)}), Nat.double(Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}))), Nat.add(Nat.add(U.U32Nat.bit(Bool.xor(x, y)), Nat.double(Word.to_nat(p, Word.xor(p, at, bt)))), Nat.double(Nat.add(U.U32Nat.bit(Bool.and(x, y)), Nat.double(Word.to_nat(p, Word.and(p, at, bt)))))), Nat.add(Nat.add(U.U32Nat.bit(Bool.xor(x, y)), Nat.double(U.U32Nat.bit(Bool.and(x, y)))), Nat.double(Nat.add(Word.to_nat(p, Word.xor(p, at, bt)), Nat.double(Word.to_nat(p, Word.and(p, at, bt)))))), Equal.trans(Nat, Nat.add(Word.to_nat(1n+p, WCon{Bool.xor(x, y), Word.xor(p, at, bt)}), Nat.double(Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}))), Nat.add(Nat.add(U.U32Nat.bit(Bool.xor(x, y)), Nat.double(Word.to_nat(p, Word.xor(p, at, bt)))), Nat.double(Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}))), Nat.add(Nat.add(U.U32Nat.bit(Bool.xor(x, y)), Nat.double(Word.to_nat(p, Word.xor(p, at, bt)))), Nat.double(Nat.add(U.U32Nat.bit(Bool.and(x, y)), Nat.double(Word.to_nat(p, Word.and(p, at, bt)))))), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.double(Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}))), Word.to_nat(1n+p, WCon{Bool.xor(x, y), Word.xor(p, at, bt)}), Nat.add(U.U32Nat.bit(Bool.xor(x, y)), Nat.double(Word.to_nat(p, Word.xor(p, at, bt)))), un.wc(p, Bool.xor(x, y), Word.xor(p, at, bt))), Equal.cong(Nat, Nat, zz => Nat.add(Nat.add(U.U32Nat.bit(Bool.xor(x, y)), Nat.double(Word.to_nat(p, Word.xor(p, at, bt)))), Nat.double(zz)), Word.to_nat(1n+p, WCon{Bool.and(x, y), Word.and(p, at, bt)}), Nat.add(U.U32Nat.bit(Bool.and(x, y)), Nat.double(Word.to_nat(p, Word.and(p, at, bt)))), un.wc(p, Bool.and(x, y), Word.and(p, at, bt)))), ur.r40(U.U32Nat.bit(Bool.xor(x, y)), Word.to_nat(p, Word.xor(p, at, bt)), U.U32Nat.bit(Bool.and(x, y)), Word.to_nat(p, Word.and(p, at, bt)))), Equal.cong(Nat, Nat, zz => Nat.add(Nat.add(U.U32Nat.bit(Bool.xor(x, y)), Nat.double(U.U32Nat.bit(Bool.and(x, y)))), Nat.double(zz)), Nat.add(Word.to_nat(p, Word.xor(p, at, bt)), Nat.double(Word.to_nat(p, Word.and(p, at, bt)))), Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)), Laws.word_xor_and(p, at, bt))), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)))), Nat.add(U.U32Nat.bit(Bool.xor(x, y)), Nat.double(U.U32Nat.bit(Bool.and(x, y)))), Nat.add(U.U32Nat.bit(x), U.U32Nat.bit(y)), un.bxa(x, y))), ur.r39(U.U32Nat.bit(x), U.U32Nat.bit(y), Word.to_nat(p, at), Word.to_nat(p, bt))), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt)))), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, at))), Word.to_nat(1n+p, WCon{x, at}), Equal.sym(Nat, Word.to_nat(1n+p, WCon{x, at}), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, at))), un.wc(p, x, at)))), Equal.cong(Nat, Nat, zz => Nat.add(Word.to_nat(1n+p, WCon{x, at}), zz), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt))), Word.to_nat(1n+p, WCon{y, bt}), Equal.sym(Nat, Word.to_nat(1n+p, WCon{y, bt}), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt))), un.wc(p, y, bt))))

def Laws.u32_and_or(a, b):
  match a b:
    case U32{+x} U32{+y}:
      Laws.word_and_or(32n, x, y)

def Laws.u32_xor_and(a, b):
  match a b:
    case U32{+x} U32{+y}:
      Laws.word_xor_and(32n, x, y)

def un.lt1(x: Nat, h: {Nat.is_lt(x, 1n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      match p:
        case 0n:
          Empty.absurd({1n == 0n : Nat}, un.ft(h))
        case 1n+ +q:
          Empty.absurd({2n+q == 0n : Nat}, un.ft(h))

def un.dz0(v: Nat, e: {Nat.double(v) == 0n : Nat}) -> {v == 0n : Nat}:
  match v:
    case 0n:
      {==}
    case 1n+ +p:
      Empty.absurd({1n+p == 0n : Nat}, un.sz(1n+Nat.double(p), e))

def un.double_inj(a: Nat, b: Nat, e: {Nat.double(a) == Nat.double(b) : Nat}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +q:
      Empty.absurd({0n == 1n+q : Nat}, un.sz(1n+Nat.double(q), Equal.sym(Nat, 0n, 2n+Nat.double(q), e)))
    case 1n+ +p 0n:
      Empty.absurd({1n+p == 0n : Nat}, un.sz(1n+Nat.double(p), e))
    case 1n+ +p 1n+ +q:
      un.succ_cong(p, q, un.double_inj(p, q, un.succ_inj(Nat.double(p), Nat.double(q), un.succ_inj(1n+Nat.double(p), 1n+Nat.double(q), e))))

def un.odd_even(a: Nat, b: Nat, e: {1n+Nat.double(a) == Nat.double(b) : Nat}) -> Empty:
  match a b:
    case 0n 0n:
      un.sz(0n, e)
    case 0n 1n+ +q:
      un.sz(Nat.double(q), Equal.sym(Nat, 0n, 1n+Nat.double(q), un.succ_inj(0n, 1n+Nat.double(q), e)))
    case 1n+ +p 0n:
      un.sz(2n+Nat.double(p), e)
    case 1n+ +p 1n+ +q:
      un.odd_even(p, q, un.succ_inj(1n+Nat.double(p), Nat.double(q), un.succ_inj(2n+Nat.double(p), 1n+Nat.double(q), e)))

def un.lt_half(y: Bool, +v: Nat, +d: Nat, h: {Nat.is_lt(Nat.add(U.U32Nat.bit(y), Nat.double(v)), Nat.double(d)) == True{} : Bool}) -> {Nat.is_lt(v, d) == True{} : Bool}:
  match y:
    case False{}:
      Equal.trans(Bool, Nat.is_lt(v, d), Nat.is_lt(Nat.double(v), Nat.double(d)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.double(v), Nat.double(d)), Nat.is_lt(v, d), un.lt_dbl(v, d)), h)
    case True{}:
      Equal.trans(Bool, Nat.is_lt(v, d), Nat.is_lt(1n+Nat.double(v), Nat.double(d)), True{}, Equal.sym(Bool, Nat.is_lt(1n+Nat.double(v), Nat.double(d)), Nat.is_lt(v, d), un.lt_dbl1(v, d)), h)

def un.or_zero(n: Nat, +a: Word(n), +b: Word(n), hb: {Word.to_nat(n, b) == 0n : Nat}) -> {Word.to_nat(n, Word.or(n, a, b)) == Word.to_nat(n, a) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{True{}, +bt}:
          Empty.absurd({Word.to_nat(1n+p, Word.or(1n+p, WCon{x, at}, WCon{True{}, bt})) == Word.to_nat(1n+p, WCon{x, at}) : Nat}, un.sz(Nat.double(Word.to_nat(p, bt)), hb))
        case WCon{+x, +at} WCon{False{}, +bt}:
          Equal.trans(Nat, Word.to_nat(1n+p, WCon{Bool.or(x, False{}), Word.or(p, at, bt)}), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, at))), Word.to_nat(1n+p, WCon{x, at}), Equal.trans(Nat, Word.to_nat(1n+p, WCon{Bool.or(x, False{}), Word.or(p, at, bt)}), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, Word.or(p, at, bt)))), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, at))), Equal.trans(Nat, Word.to_nat(1n+p, WCon{Bool.or(x, False{}), Word.or(p, at, bt)}), Nat.add(U.U32Nat.bit(Bool.or(x, False{})), Nat.double(Word.to_nat(p, Word.or(p, at, bt)))), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, Word.or(p, at, bt)))), un.wc(p, Bool.or(x, False{}), Word.or(p, at, bt)), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.double(Word.to_nat(p, Word.or(p, at, bt)))), U.U32Nat.bit(Bool.or(x, False{})), U.U32Nat.bit(x), Equal.cong(Bool, Nat, zz => U.U32Nat.bit(zz), Bool.or(x, False{}), x, un.bor_f(x)))), Equal.cong(Nat, Nat, zz => Nat.add(U.U32Nat.bit(x), Nat.double(zz)), Word.to_nat(p, Word.or(p, at, bt)), Word.to_nat(p, at), un.or_zero(p, at, bt, un.dz0(Word.to_nat(p, bt), hb)))), Equal.sym(Nat, Word.to_nat(1n+p, WCon{x, at}), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, at))), un.wc(p, x, at)))

def ur.r41(+x0: Nat, +x1: Nat, +x2: Nat) -> {Nat.add(x0, Nat.double(Nat.add(x1, x2))) == Nat.add(Nat.double(x1), Nat.add(x0, Nat.double(x2))) : Nat}:
  %Equal.sym(Nat, Nat.double(Nat.add(x1, x2)), Nat.add(Nat.add(x1, x2), Nat.add(x1, x2)), Laws.nat_double(Nat.add(x1, x2))) : {Nat.add(x0, _) == Nat.add(Nat.double(x1), Nat.add(x0, Nat.double(x2))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x1, x2), Nat.add(x1, x2)), Nat.add(x1, Nat.add(x2, Nat.add(x1, x2))), Laws.nat_add_assoc(x1, x2, Nat.add(x1, x2))) : {Nat.add(x0, _) == Nat.add(Nat.double(x1), Nat.add(x0, Nat.double(x2))) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(x1, x2)), Nat.add(x1, Nat.add(x2, x2)), Laws.nat_add_left_comm(x2, x1, x2)) : {Nat.add(x0, Nat.add(x1, _)) == Nat.add(Nat.double(x1), Nat.add(x0, Nat.double(x2))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x1, Nat.add(x1, Nat.add(x2, x2)))), Nat.add(x1, Nat.add(x0, Nat.add(x1, Nat.add(x2, x2)))), Equal.sym(Nat, Nat.add(x1, Nat.add(x0, Nat.add(x1, Nat.add(x2, x2)))), Nat.add(x0, Nat.add(x1, Nat.add(x1, Nat.add(x2, x2)))), Laws.nat_add_left_comm(x1, x0, Nat.add(x1, Nat.add(x2, x2))))) : {_ == Nat.add(Nat.double(x1), Nat.add(x0, Nat.double(x2))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x1, Nat.add(x2, x2))), Nat.add(x1, Nat.add(x0, Nat.add(x2, x2))), Equal.sym(Nat, Nat.add(x1, Nat.add(x0, Nat.add(x2, x2))), Nat.add(x0, Nat.add(x1, Nat.add(x2, x2))), Laws.nat_add_left_comm(x1, x0, Nat.add(x2, x2)))) : {Nat.add(x1, _) == Nat.add(Nat.double(x1), Nat.add(x0, Nat.double(x2))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(x1, Nat.add(x0, Nat.add(x2, x2)))), Nat.add(Nat.add(x1, x1), Nat.add(x0, Nat.add(x2, x2))), Equal.sym(Nat, Nat.add(Nat.add(x1, x1), Nat.add(x0, Nat.add(x2, x2))), Nat.add(x1, Nat.add(x1, Nat.add(x0, Nat.add(x2, x2)))), Laws.nat_add_assoc(x1, x1, Nat.add(x0, Nat.add(x2, x2))))) : {_ == Nat.add(Nat.double(x1), Nat.add(x0, Nat.double(x2))) : Nat}
  %Equal.sym(Nat, Nat.add(x2, x2), Nat.double(x2), Equal.sym(Nat, Nat.double(x2), Nat.add(x2, x2), Laws.nat_double(x2))) : {Nat.add(Nat.add(x1, x1), Nat.add(x0, _)) == Nat.add(Nat.double(x1), Nat.add(x0, Nat.double(x2))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, x1), Nat.double(x1), Equal.sym(Nat, Nat.double(x1), Nat.add(x1, x1), Laws.nat_double(x1))) : {Nat.add(_, Nat.add(x0, Nat.double(x2))) == Nat.add(Nat.double(x1), Nat.add(x0, Nat.double(x2))) : Nat}
  {==}

def Laws.word_or_split(n, a, b, k, q, e, h):
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a b:
        case WCon{False{}, +at} WCon{+y, +bt}:
          match k:
            case 0n:
              +hb0 = un.lt1(Word.to_nat(1n+p, WCon{y, bt}), h)
              Equal.trans(Nat, Word.to_nat(1n+p, Word.or(1n+p, WCon{False{}, at}, WCon{y, bt})), Nat.add(Word.to_nat(1n+p, WCon{False{}, at}), 0n), Nat.add(Word.to_nat(1n+p, WCon{False{}, at}), Word.to_nat(1n+p, WCon{y, bt})), Equal.trans(Nat, Word.to_nat(1n+p, Word.or(1n+p, WCon{False{}, at}, WCon{y, bt})), Word.to_nat(1n+p, WCon{False{}, at}), Nat.add(Word.to_nat(1n+p, WCon{False{}, at}), 0n), un.or_zero(1n+p, WCon{False{}, at}, WCon{y, bt}, hb0), Equal.sym(Nat, Nat.add(Word.to_nat(1n+p, WCon{False{}, at}), 0n), Word.to_nat(1n+p, WCon{False{}, at}), Laws.nat_add_zero(Word.to_nat(1n+p, WCon{False{}, at})))), Equal.cong(Nat, Nat, zz => Nat.add(Word.to_nat(1n+p, WCon{False{}, at}), zz), 0n, Word.to_nat(1n+p, WCon{y, bt}), Equal.sym(Nat, Word.to_nat(1n+p, WCon{y, bt}), 0n, hb0)))
            case 1n+ +j:
              Equal.trans(Nat, Word.to_nat(1n+p, WCon{y, Word.or(p, at, bt)}), Nat.add(Nat.double(Word.to_nat(p, at)), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt)))), Nat.add(Nat.double(Word.to_nat(p, at)), Word.to_nat(1n+p, WCon{y, bt})), Equal.trans(Nat, Word.to_nat(1n+p, WCon{y, Word.or(p, at, bt)}), Nat.add(U.U32Nat.bit(y), Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)))), Nat.add(Nat.double(Word.to_nat(p, at)), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt)))), Equal.trans(Nat, Word.to_nat(1n+p, WCon{y, Word.or(p, at, bt)}), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, Word.or(p, at, bt)))), Nat.add(U.U32Nat.bit(y), Nat.double(Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)))), un.wc(p, y, Word.or(p, at, bt)), Equal.cong(Nat, Nat, zz => Nat.add(U.U32Nat.bit(y), Nat.double(zz)), Word.to_nat(p, Word.or(p, at, bt)), Nat.add(Word.to_nat(p, at), Word.to_nat(p, bt)), Laws.word_or_split(p, at, bt, j, q, un.double_inj(Word.to_nat(p, at), U.U32Nat.dbl(j, q), e), un.lt_half(y, Word.to_nat(p, bt), U.U32Nat.dbl(j, 1n), Equal.trans(Bool, Nat.is_lt(Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt))), Nat.double(U.U32Nat.dbl(j, 1n))), Nat.is_lt(Word.to_nat(1n+p, WCon{y, bt}), Nat.double(U.U32Nat.dbl(j, 1n))), True{}, Equal.cong(Nat, Bool, zz => Nat.is_lt(zz, Nat.double(U.U32Nat.dbl(j, 1n))), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt))), Word.to_nat(1n+p, WCon{y, bt}), Equal.sym(Nat, Word.to_nat(1n+p, WCon{y, bt}), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt))), un.wc(p, y, bt))), h))))), ur.r41(U.U32Nat.bit(y), Word.to_nat(p, at), Word.to_nat(p, bt))), Equal.cong(Nat, Nat, zz => Nat.add(Nat.double(Word.to_nat(p, at)), zz), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt))), Word.to_nat(1n+p, WCon{y, bt}), Equal.sym(Nat, Word.to_nat(1n+p, WCon{y, bt}), Nat.add(U.U32Nat.bit(y), Nat.double(Word.to_nat(p, bt))), un.wc(p, y, bt))))
        case WCon{True{}, +at} WCon{+y, +bt}:
          match k:
            case 0n:
              +hb0 = un.lt1(Word.to_nat(1n+p, WCon{y, bt}), h)
              Equal.trans(Nat, Word.to_nat(1n+p, Word.or(1n+p, WCon{True{}, at}, WCon{y, bt})), Nat.add(Word.to_nat(1n+p, WCon{True{}, at}), 0n), Nat.add(Word.to_nat(1n+p, WCon{True{}, at}), Word.to_nat(1n+p, WCon{y, bt})), Equal.trans(Nat, Word.to_nat(1n+p, Word.or(1n+p, WCon{True{}, at}, WCon{y, bt})), Word.to_nat(1n+p, WCon{True{}, at}), Nat.add(Word.to_nat(1n+p, WCon{True{}, at}), 0n), un.or_zero(1n+p, WCon{True{}, at}, WCon{y, bt}, hb0), Equal.sym(Nat, Nat.add(Word.to_nat(1n+p, WCon{True{}, at}), 0n), Word.to_nat(1n+p, WCon{True{}, at}), Laws.nat_add_zero(Word.to_nat(1n+p, WCon{True{}, at})))), Equal.cong(Nat, Nat, zz => Nat.add(Word.to_nat(1n+p, WCon{True{}, at}), zz), 0n, Word.to_nat(1n+p, WCon{y, bt}), Equal.sym(Nat, Word.to_nat(1n+p, WCon{y, bt}), 0n, hb0)))
            case 1n+ +j:
              Empty.absurd({Word.to_nat(1n+p, Word.or(1n+p, WCon{True{}, at}, WCon{y, bt})) == Nat.add(Word.to_nat(1n+p, WCon{True{}, at}), Word.to_nat(1n+p, WCon{y, bt})) : Nat}, un.odd_even(Word.to_nat(p, at), U.U32Nat.dbl(j, q), e))

def Laws.u32_or_split(a, b, k, q, e, h):
  match a b:
    case U32{+x} U32{+y}:
      Laws.word_or_split(32n, x, y, k, q, e, h)

def ur.r42(+x0: Nat) -> {2n+Nat.double(x0) == Nat.double(1n+x0) : Nat}:
  %Equal.sym(Nat, Nat.double(x0), Nat.add(x0, x0), Laws.nat_double(x0)) : {Nat.add(1n, Nat.add(1n, _)) == Nat.double(1n+x0) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(1n, Nat.add(x0, x0))), Nat.add(Nat.add(1n, 1n), Nat.add(x0, x0)), Equal.sym(Nat, Nat.add(Nat.add(1n, 1n), Nat.add(x0, x0)), Nat.add(1n, Nat.add(1n, Nat.add(x0, x0))), Laws.nat_add_assoc(1n, 1n, Nat.add(x0, x0)))) : {_ == Nat.double(1n+x0) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(1n, 1n), Nat.add(x0, x0)), Nat.add(1n, Nat.add(1n, Nat.add(x0, x0))), Equal.sym(Nat, Nat.add(1n, Nat.add(1n, Nat.add(x0, x0))), Nat.add(Nat.add(1n, 1n), Nat.add(x0, x0)), Equal.sym(Nat, Nat.add(Nat.add(1n, 1n), Nat.add(x0, x0)), Nat.add(1n, Nat.add(1n, Nat.add(x0, x0))), Laws.nat_add_assoc(1n, 1n, Nat.add(x0, x0))))) : {_ == Nat.double(1n+x0) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x0, x0)), Nat.add(x0, Nat.add(1n, x0)), Equal.sym(Nat, Nat.add(x0, Nat.add(1n, x0)), Nat.add(1n, Nat.add(x0, x0)), Laws.nat_add_left_comm(x0, 1n, x0))) : {Nat.add(1n, _) == Nat.double(1n+x0) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x0, Nat.add(1n, x0))), Nat.add(Nat.add(1n, x0), Nat.add(1n, x0)), Equal.sym(Nat, Nat.add(Nat.add(1n, x0), Nat.add(1n, x0)), Nat.add(1n, Nat.add(x0, Nat.add(1n, x0))), Laws.nat_add_assoc(1n, x0, Nat.add(1n, x0)))) : {_ == Nat.double(1n+x0) : Nat}
  %Equal.sym(Nat, Nat.add(1n+x0, 1n+x0), Nat.double(1n+x0), Equal.sym(Nat, Nat.double(1n+x0), Nat.add(1n+x0, 1n+x0), Laws.nat_double(1n+x0))) : {_ == Nat.double(1n+x0) : Nat}
  {==}

def Laws.word_mask_value(n, k, h):
  match n:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+ +j:
          Empty.absurd({1n+Word.to_nat(0n, U.U32Word.mask(0n, 1n+j)) == U.U32Nat.dbl(1n+j, 1n) : Nat}, un.ft(h))
    case 1n+ +p:
      match k:
        case 0n:
          un.succ_cong(Word.to_nat(1n+p, Word.zero(1n+p)), 0n, Laws.word_zero_value(1n+p))
        case 1n+ +j:
          Equal.trans(Nat, 2n+Nat.double(Word.to_nat(p, U.U32Word.mask(p, j))), Nat.double(1n+Word.to_nat(p, U.U32Word.mask(p, j))), Nat.double(U.U32Nat.dbl(j, 1n)), ur.r42(Word.to_nat(p, U.U32Word.mask(p, j))), Equal.cong(Nat, Nat, zz => Nat.double(zz), 1n+Word.to_nat(p, U.U32Word.mask(p, j)), U.U32Nat.dbl(j, 1n), Laws.word_mask_value(p, j, h)))

def un.and_zero(n: Nat, +w: Word(n), +m: Word(n), hm: {Word.to_nat(n, m) == 0n : Nat}) -> {Word.to_nat(n, Word.and(n, w, m)) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w m:
        case WCon{+x, +wt} WCon{True{}, +mt}:
          Empty.absurd({Word.to_nat(1n+p, Word.and(1n+p, WCon{x, wt}, WCon{True{}, mt})) == 0n : Nat}, un.sz(Nat.double(Word.to_nat(p, mt)), hm))
        case WCon{+x, +wt} WCon{False{}, +mt}:
          Equal.trans(Nat, Word.to_nat(1n+p, WCon{Bool.and(x, False{}), Word.and(p, wt, mt)}), Nat.add(U.U32Nat.bit(False{}), Nat.double(0n)), 0n, Equal.trans(Nat, Word.to_nat(1n+p, WCon{Bool.and(x, False{}), Word.and(p, wt, mt)}), Nat.add(U.U32Nat.bit(False{}), Nat.double(Word.to_nat(p, Word.and(p, wt, mt)))), Nat.add(U.U32Nat.bit(False{}), Nat.double(0n)), Equal.trans(Nat, Word.to_nat(1n+p, WCon{Bool.and(x, False{}), Word.and(p, wt, mt)}), Nat.add(U.U32Nat.bit(Bool.and(x, False{})), Nat.double(Word.to_nat(p, Word.and(p, wt, mt)))), Nat.add(U.U32Nat.bit(False{}), Nat.double(Word.to_nat(p, Word.and(p, wt, mt)))), un.wc(p, Bool.and(x, False{}), Word.and(p, wt, mt)), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.double(Word.to_nat(p, Word.and(p, wt, mt)))), U.U32Nat.bit(Bool.and(x, False{})), U.U32Nat.bit(False{}), Equal.cong(Bool, Nat, zz => U.U32Nat.bit(zz), Bool.and(x, False{}), False{}, un.band_f(x)))), Equal.cong(Nat, Nat, zz => Nat.add(U.U32Nat.bit(False{}), Nat.double(zz)), Word.to_nat(p, Word.and(p, wt, mt)), 0n, un.and_zero(p, wt, mt, un.dz0(Word.to_nat(p, mt), hm)))), {==})

def Laws.word_and_mask(n, w, m, k, h):
  match n:
    case 0n:
      Equal.sym(Nat, U.U32Nat.low(k, 0n), 0n, un.low_zero(k))
    case 1n+ +p:
      match w m:
        case WCon{+x, +wt} WCon{False{}, +mt}:
          match k:
            case 0n:
              un.and_zero(1n+p, WCon{x, wt}, WCon{False{}, mt}, un.succ_inj(Word.to_nat(1n+p, WCon{False{}, mt}), 0n, h))
            case 1n+ +j:
              Empty.absurd({Word.to_nat(1n+p, Word.and(1n+p, WCon{x, wt}, WCon{False{}, mt})) == U.U32Nat.low(1n+j, Word.to_nat(1n+p, WCon{x, wt})) : Nat}, un.odd_even(Word.to_nat(p, mt), U.U32Nat.dbl(j, 1n), h))
        case WCon{+x, +wt} WCon{True{}, +mt}:
          match k:
            case 0n:
              un.and_zero(1n+p, WCon{x, wt}, WCon{True{}, mt}, un.succ_inj(Word.to_nat(1n+p, WCon{True{}, mt}), 0n, h))
            case 1n+ +j:
              Equal.trans(Nat, Word.to_nat(1n+p, WCon{Bool.and(x, True{}), Word.and(p, wt, mt)}), Nat.add(U.U32Nat.odd(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, wt)))), Nat.double(U.U32Nat.low(j, U.U32Nat.half(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, wt))))))), Nat.add(U.U32Nat.odd(Word.to_nat(1n+p, WCon{x, wt})), Nat.double(U.U32Nat.low(j, U.U32Nat.half(Word.to_nat(1n+p, WCon{x, wt}))))), Equal.trans(Nat, Word.to_nat(1n+p, WCon{Bool.and(x, True{}), Word.and(p, wt, mt)}), Nat.add(U.U32Nat.odd(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, wt)))), Nat.double(U.U32Nat.low(j, Word.to_nat(p, wt)))), Nat.add(U.U32Nat.odd(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, wt)))), Nat.double(U.U32Nat.low(j, U.U32Nat.half(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, wt))))))), Equal.trans(Nat, Word.to_nat(1n+p, WCon{Bool.and(x, True{}), Word.and(p, wt, mt)}), Nat.add(U.U32Nat.bit(x), Nat.double(U.U32Nat.low(j, Word.to_nat(p, wt)))), Nat.add(U.U32Nat.odd(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, wt)))), Nat.double(U.U32Nat.low(j, Word.to_nat(p, wt)))), Equal.trans(Nat, Word.to_nat(1n+p, WCon{Bool.and(x, True{}), Word.and(p, wt, mt)}), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, Word.and(p, wt, mt)))), Nat.add(U.U32Nat.bit(x), Nat.double(U.U32Nat.low(j, Word.to_nat(p, wt)))), Equal.trans(Nat, Word.to_nat(1n+p, WCon{Bool.and(x, True{}), Word.and(p, wt, mt)}), Nat.add(U.U32Nat.bit(Bool.and(x, True{})), Nat.double(Word.to_nat(p, Word.and(p, wt, mt)))), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, Word.and(p, wt, mt)))), un.wc(p, Bool.and(x, True{}), Word.and(p, wt, mt)), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.double(Word.to_nat(p, Word.and(p, wt, mt)))), U.U32Nat.bit(Bool.and(x, True{})), U.U32Nat.bit(x), Equal.cong(Bool, Nat, zz => U.U32Nat.bit(zz), Bool.and(x, True{}), x, un.band_t(x)))), Equal.cong(Nat, Nat, zz => Nat.add(U.U32Nat.bit(x), Nat.double(zz)), Word.to_nat(p, Word.and(p, wt, mt)), U.U32Nat.low(j, Word.to_nat(p, wt)), Laws.word_and_mask(p, wt, mt, j, un.double_inj(1n+Word.to_nat(p, mt), U.U32Nat.dbl(j, 1n), h)))), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.double(U.U32Nat.low(j, Word.to_nat(p, wt)))), U.U32Nat.bit(x), U.U32Nat.odd(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, wt)))), Equal.sym(Nat, U.U32Nat.odd(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, wt)))), U.U32Nat.bit(x), un.odd_bd(x, Word.to_nat(p, wt))))), Equal.cong(Nat, Nat, zz => Nat.add(U.U32Nat.odd(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, wt)))), Nat.double(U.U32Nat.low(j, zz))), Word.to_nat(p, wt), U.U32Nat.half(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, wt)))), Equal.sym(Nat, U.U32Nat.half(Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, wt)))), Word.to_nat(p, wt), un.half_bd(x, Word.to_nat(p, wt))))), Equal.cong(Nat, Nat, zz => Nat.add(U.U32Nat.odd(zz), Nat.double(U.U32Nat.low(j, U.U32Nat.half(zz)))), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, wt))), Word.to_nat(1n+p, WCon{x, wt}), Equal.sym(Nat, Word.to_nat(1n+p, WCon{x, wt}), Nat.add(U.U32Nat.bit(x), Nat.double(Word.to_nat(p, wt))), un.wc(p, x, wt))))

def Laws.u32_and_mask(a, m, k, h):
  match a m:
    case U32{+x} U32{+y}:
      Laws.word_and_mask(32n, x, y, k, h)

def Laws.u32_and_65535(a):
  match a:
    case U32{+x}:
      Laws.word_and_mask(32n, x, U.U32Word.mask(32n, 16n), 16n, Laws.word_mask_value(32n, 16n, {==}))

def ur.r43(+x0: Nat, +x1: Nat) -> {Nat.add(x0, x1) == Nat.add(x1, x0) : Nat}:
  %Equal.sym(Nat, Nat.add(x0, x1), Nat.add(x1, x0), Equal.sym(Nat, Nat.add(x1, x0), Nat.add(x0, x1), Laws.nat_add_comm(x1, x0))) : {_ == Nat.add(x1, x0) : Nat}
  {==}

def un.lts(x: Nat, y: Nat) -> {Nat.is_lt(x, 1n+y) == Nat.is_le(x, y) : Bool}:
  Equal.sym(Bool, Nat.is_le(1n+x, 1n+y), Nat.is_lt(x, 1n+y), un.le_succ(x, 1n+y))

def Laws.word_not_sub(n, w):
  Laws.word_value_eq(n, Word.not(n, w), Word.sub(n, U.U32Word.mask(n, n), w), Laws.nat_add_cancel(Word.to_nat(n, w), Word.to_nat(n, Word.not(n, w)), Word.to_nat(n, Word.sub(n, U.U32Word.mask(n, n), w)), Equal.trans(Nat, Nat.add(Word.to_nat(n, w), Word.to_nat(n, Word.not(n, w))), Nat.add(Word.to_nat(n, Word.sub(n, U.U32Word.mask(n, n), w)), Word.to_nat(n, w)), Nat.add(Word.to_nat(n, w), Word.to_nat(n, Word.sub(n, U.U32Word.mask(n, n), w))), Equal.trans(Nat, Nat.add(Word.to_nat(n, w), Word.to_nat(n, Word.not(n, w))), Word.to_nat(n, U.U32Word.mask(n, n)), Nat.add(Word.to_nat(n, Word.sub(n, U.U32Word.mask(n, n), w)), Word.to_nat(n, w)), Equal.trans(Nat, Nat.add(Word.to_nat(n, w), Word.to_nat(n, Word.not(n, w))), Nat.add(Word.to_nat(n, Word.not(n, w)), Word.to_nat(n, w)), Word.to_nat(n, U.U32Word.mask(n, n)), ur.r43(Word.to_nat(n, w), Word.to_nat(n, Word.not(n, w))), un.succ_inj(Nat.add(Word.to_nat(n, Word.not(n, w)), Word.to_nat(n, w)), Word.to_nat(n, U.U32Word.mask(n, n)), Equal.trans(Nat, 1n+Nat.add(Word.to_nat(n, Word.not(n, w)), Word.to_nat(n, w)), U.U32Nat.dbl(n, 1n), 1n+Word.to_nat(n, U.U32Word.mask(n, n)), Laws.word_not_value(n, w), Equal.sym(Nat, 1n+Word.to_nat(n, U.U32Word.mask(n, n)), U.U32Nat.dbl(n, 1n), Laws.word_mask_value(n, n, Laws.nat_le_refl(n)))))), Equal.sym(Nat, Nat.add(Word.to_nat(n, Word.sub(n, U.U32Word.mask(n, n), w)), Word.to_nat(n, w)), Word.to_nat(n, U.U32Word.mask(n, n)), Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.sub(n, U.U32Word.mask(n, n), w)), Word.to_nat(n, w)), Nat.add(Word.to_nat(n, U.U32Word.mask(n, n)), U.U32Nat.dbl(n, 0n)), Word.to_nat(n, U.U32Word.mask(n, n)), Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.sub(n, U.U32Word.mask(n, n), w)), Word.to_nat(n, w)), Nat.add(Word.to_nat(n, U.U32Word.mask(n, n)), U.U32Nat.dbl(n, U.U32Nat.bit(False{}))), Nat.add(Word.to_nat(n, U.U32Word.mask(n, n)), U.U32Nat.dbl(n, 0n)), Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.sub(n, U.U32Word.mask(n, n), w)), Word.to_nat(n, w)), Nat.add(Word.to_nat(n, U.U32Word.mask(n, n)), U.U32Nat.dbl(n, U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, U.U32Word.mask(n, n), w))))), Nat.add(Word.to_nat(n, U.U32Word.mask(n, n)), U.U32Nat.dbl(n, U.U32Nat.bit(False{}))), Laws.word_sub_wrap(n, U.U32Word.mask(n, n), w), Equal.cong(Nat, Nat, zz => Nat.add(Word.to_nat(n, U.U32Word.mask(n, n)), U.U32Nat.dbl(n, zz)), U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, U.U32Word.mask(n, n), w))), U.U32Nat.bit(False{}), Equal.cong(Bool, Nat, zz => U.U32Nat.bit(zz), Cmp.is_lt(Word.cmp(n, U.U32Word.mask(n, n), w)), False{}, Equal.trans(Bool, Cmp.is_lt(Word.cmp(n, U.U32Word.mask(n, n), w)), Nat.is_lt(Word.to_nat(n, U.U32Word.mask(n, n)), Word.to_nat(n, w)), False{}, Equal.cong(Cmp, Bool, zz => Cmp.is_lt(zz), Word.cmp(n, U.U32Word.mask(n, n), w), Nat.cmp(Word.to_nat(n, U.U32Word.mask(n, n)), Word.to_nat(n, w)), Laws.word_cmp_value(n, U.U32Word.mask(n, n), w)), un.le_not_lt(Word.to_nat(n, w), Word.to_nat(n, U.U32Word.mask(n, n)), Equal.trans(Bool, Nat.is_le(Word.to_nat(n, w), Word.to_nat(n, U.U32Word.mask(n, n))), Nat.is_lt(Word.to_nat(n, w), 1n+Word.to_nat(n, U.U32Word.mask(n, n))), True{}, Equal.sym(Bool, Nat.is_lt(Word.to_nat(n, w), 1n+Word.to_nat(n, U.U32Word.mask(n, n))), Nat.is_le(Word.to_nat(n, w), Word.to_nat(n, U.U32Word.mask(n, n))), un.lts(Word.to_nat(n, w), Word.to_nat(n, U.U32Word.mask(n, n)))), Equal.trans(Bool, Nat.is_lt(Word.to_nat(n, w), 1n+Word.to_nat(n, U.U32Word.mask(n, n))), Nat.is_lt(Word.to_nat(n, w), U.U32Nat.dbl(n, 1n)), True{}, Equal.cong(Nat, Bool, zz => Nat.is_lt(Word.to_nat(n, w), zz), 1n+Word.to_nat(n, U.U32Word.mask(n, n)), U.U32Nat.dbl(n, 1n), Laws.word_mask_value(n, n, Laws.nat_le_refl(n))), Laws.word_value_lt(n, w)))))))), {==}), ur.r11(Word.to_nat(n, U.U32Word.mask(n, n)), n)))), ur.r43(Word.to_nat(n, Word.sub(n, U.U32Word.mask(n, n), w)), Word.to_nat(n, w)))))

def Laws.u32_not_sub(a):
  match a:
    case U32{+x}:
      un.u32_cong(Word.not(32n, x), Word.sub(32n, U.U32Word.mask(32n, 32n), x), Laws.word_not_sub(32n, x))

# Shifts by k bits

def Laws.u32_shrn_value(a, k):
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.trans(Nat, U32.to_nat(U32.shr(U32.shrn(a, p))), U.U32Nat.half(U.U32Nat.high(p, U32.to_nat(a))), U.U32Nat.high(p, U.U32Nat.half(U32.to_nat(a))), Equal.trans(Nat, U32.to_nat(U32.shr(U32.shrn(a, p))), U.U32Nat.half(U32.to_nat(U32.shrn(a, p))), U.U32Nat.half(U.U32Nat.high(p, U32.to_nat(a))), Laws.u32_shr_value(U32.shrn(a, p)), Equal.cong(Nat, Nat, zz => U.U32Nat.half(zz), U32.to_nat(U32.shrn(a, p)), U.U32Nat.high(p, U32.to_nat(a)), Laws.u32_shrn_value(a, p))), Equal.sym(Nat, U.U32Nat.high(p, U.U32Nat.half(U32.to_nat(a))), U.U32Nat.half(U.U32Nat.high(p, U32.to_nat(a))), un.high_half(p, U32.to_nat(a))))

def un.u32_shl_low(+x: U32) -> {U32.to_nat(U32.shl(x)) == U.U32Nat.low(32n, Nat.double(U32.to_nat(x))) : Nat}:
  match x:
    case U32{+v}:
      un.shl_low(32n, v)

def un.u32_low_self(+a: U32) -> {U32.to_nat(a) == U.U32Nat.low(32n, U32.to_nat(a)) : Nat}:
  match a:
    case U32{+w}:
      Equal.sym(Nat, U.U32Nat.low(32n, Word.to_nat(32n, w)), Word.to_nat(32n, w), Laws.low_small(32n, Word.to_nat(32n, w), Laws.word_value_lt(32n, w)))

def Laws.u32_shln_low(a, k):
  match k:
    case 0n:
      un.u32_low_self(a)
    case 1n+ +p:
      Equal.trans(Nat, U32.to_nat(U32.shl(U32.shln(a, p))), U.U32Nat.low(32n, Nat.double(U.U32Nat.low(32n, U.U32Nat.dbl(p, U32.to_nat(a))))), U.U32Nat.low(32n, Nat.double(U.U32Nat.dbl(p, U32.to_nat(a)))), Equal.trans(Nat, U32.to_nat(U32.shl(U32.shln(a, p))), U.U32Nat.low(32n, Nat.double(U32.to_nat(U32.shln(a, p)))), U.U32Nat.low(32n, Nat.double(U.U32Nat.low(32n, U.U32Nat.dbl(p, U32.to_nat(a))))), un.u32_shl_low(U32.shln(a, p)), Equal.cong(Nat, Nat, zz => U.U32Nat.low(32n, Nat.double(zz)), U32.to_nat(U32.shln(a, p)), U.U32Nat.low(32n, U.U32Nat.dbl(p, U32.to_nat(a))), Laws.u32_shln_low(a, p))), un.low_double_low(32n, U.U32Nat.dbl(p, U32.to_nat(a))))

# More of the Nat library

def Laws.low_double(k, x):
  Equal.trans(Nat, Nat.add(U.U32Nat.odd(Nat.double(x)), Nat.double(U.U32Nat.low(k, U.U32Nat.half(Nat.double(x))))), Nat.add(0n, Nat.double(U.U32Nat.low(k, x))), Nat.double(U.U32Nat.low(k, x)), Equal.trans(Nat, Nat.add(U.U32Nat.odd(Nat.double(x)), Nat.double(U.U32Nat.low(k, U.U32Nat.half(Nat.double(x))))), Nat.add(0n, Nat.double(U.U32Nat.low(k, U.U32Nat.half(Nat.double(x))))), Nat.add(0n, Nat.double(U.U32Nat.low(k, x))), Equal.cong(Nat, Nat, zz => Nat.add(zz, Nat.double(U.U32Nat.low(k, U.U32Nat.half(Nat.double(x))))), U.U32Nat.odd(Nat.double(x)), 0n, un.odd_d(x)), Equal.cong(Nat, Nat, zz => Nat.add(0n, Nat.double(U.U32Nat.low(k, zz))), U.U32Nat.half(Nat.double(x)), x, Laws.half_double(x))), {==})

def Laws.high_double(k, x):
  Equal.cong(Nat, Nat, zz => U.U32Nat.high(k, zz), U.U32Nat.half(Nat.double(x)), x, Laws.half_double(x))

def ur.r44(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat) -> {Nat.add(Nat.add(x0, x1), 1n+U.U32Nat.dbl(x2, x3)) == Nat.add(x0, 1n+Nat.add(x1, U.U32Nat.dbl(x2, x3))) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(x0, x1), Nat.add(1n, U.U32Nat.dbl(x2, x3))), Nat.add(x0, Nat.add(x1, Nat.add(1n, U.U32Nat.dbl(x2, x3)))), Laws.nat_add_assoc(x0, x1, Nat.add(1n, U.U32Nat.dbl(x2, x3)))) : {_ == Nat.add(x0, 1n+Nat.add(x1, U.U32Nat.dbl(x2, x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(1n, U.U32Nat.dbl(x2, x3))), Nat.add(1n, Nat.add(x1, U.U32Nat.dbl(x2, x3))), Laws.nat_add_left_comm(x1, 1n, U.U32Nat.dbl(x2, x3))) : {Nat.add(x0, _) == Nat.add(x0, 1n+Nat.add(x1, U.U32Nat.dbl(x2, x3))) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(x1, U.U32Nat.dbl(x2, x3)))), Nat.add(1n, Nat.add(x0, Nat.add(x1, U.U32Nat.dbl(x2, x3)))), Laws.nat_add_left_comm(x0, 1n, Nat.add(x1, U.U32Nat.dbl(x2, x3)))) : {_ == Nat.add(x0, 1n+Nat.add(x1, U.U32Nat.dbl(x2, x3))) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x0, Nat.add(x1, U.U32Nat.dbl(x2, x3)))), Nat.add(x0, Nat.add(1n, Nat.add(x1, U.U32Nat.dbl(x2, x3)))), Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(x1, U.U32Nat.dbl(x2, x3)))), Nat.add(1n, Nat.add(x0, Nat.add(x1, U.U32Nat.dbl(x2, x3)))), Laws.nat_add_left_comm(x0, 1n, Nat.add(x1, U.U32Nat.dbl(x2, x3))))) : {_ == Nat.add(x0, 1n+Nat.add(x1, U.U32Nat.dbl(x2, x3))) : Nat}
  {==}

def Laws.high_lt(k, j, m, x, e, h):
  Equal.trans(Bool, Nat.is_lt(U.U32Nat.high(k, x), U.U32Nat.dbl(j, 1n)), Nat.is_lt(U.U32Nat.dbl(k, U.U32Nat.high(k, x)), U.U32Nat.dbl(k, U.U32Nat.dbl(j, 1n))), True{}, Equal.sym(Bool, Nat.is_lt(U.U32Nat.dbl(k, U.U32Nat.high(k, x)), U.U32Nat.dbl(k, U.U32Nat.dbl(j, 1n))), Nat.is_lt(U.U32Nat.high(k, x), U.U32Nat.dbl(j, 1n)), Laws.dbl_lt(k, U.U32Nat.high(k, x), U.U32Nat.dbl(j, 1n))), Equal.trans(Bool, Nat.is_lt(U.U32Nat.dbl(k, U.U32Nat.high(k, x)), U.U32Nat.dbl(k, U.U32Nat.dbl(j, 1n))), Nat.is_lt(U.U32Nat.dbl(k, U.U32Nat.high(k, x)), Nat.add(Nat.add(Nat.sub(U.U32Nat.dbl(m, 1n), 1n+x), U.U32Nat.low(k, x)), 1n+U.U32Nat.dbl(k, U.U32Nat.high(k, x)))), True{}, Equal.sym(Bool, Nat.is_lt(U.U32Nat.dbl(k, U.U32Nat.high(k, x)), Nat.add(Nat.add(Nat.sub(U.U32Nat.dbl(m, 1n), 1n+x), U.U32Nat.low(k, x)), 1n+U.U32Nat.dbl(k, U.U32Nat.high(k, x)))), Nat.is_lt(U.U32Nat.dbl(k, U.U32Nat.high(k, x)), U.U32Nat.dbl(k, U.U32Nat.dbl(j, 1n))), Equal.cong(Nat, Bool, zz => Nat.is_lt(U.U32Nat.dbl(k, U.U32Nat.high(k, x)), zz), Nat.add(Nat.add(Nat.sub(U.U32Nat.dbl(m, 1n), 1n+x), U.U32Nat.low(k, x)), 1n+U.U32Nat.dbl(k, U.U32Nat.high(k, x))), U.U32Nat.dbl(k, U.U32Nat.dbl(j, 1n)), Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(U.U32Nat.dbl(m, 1n), 1n+x), U.U32Nat.low(k, x)), 1n+U.U32Nat.dbl(k, U.U32Nat.high(k, x))), U.U32Nat.dbl(Nat.add(k, j), 1n), U.U32Nat.dbl(k, U.U32Nat.dbl(j, 1n)), Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(U.U32Nat.dbl(m, 1n), 1n+x), U.U32Nat.low(k, x)), 1n+U.U32Nat.dbl(k, U.U32Nat.high(k, x))), U.U32Nat.dbl(m, 1n), U.U32Nat.dbl(Nat.add(k, j), 1n), Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(U.U32Nat.dbl(m, 1n), 1n+x), U.U32Nat.low(k, x)), 1n+U.U32Nat.dbl(k, U.U32Nat.high(k, x))), Nat.add(Nat.sub(U.U32Nat.dbl(m, 1n), 1n+x), 1n+x), U.U32Nat.dbl(m, 1n), Equal.trans(Nat, Nat.add(Nat.add(Nat.sub(U.U32Nat.dbl(m, 1n), 1n+x), U.U32Nat.low(k, x)), 1n+U.U32Nat.dbl(k, U.U32Nat.high(k, x))), Nat.add(Nat.sub(U.U32Nat.dbl(m, 1n), 1n+x), 1n+Nat.add(U.U32Nat.low(k, x), U.U32Nat.dbl(k, U.U32Nat.high(k, x)))), Nat.add(Nat.sub(U.U32Nat.dbl(m, 1n), 1n+x), 1n+x), ur.r44(Nat.sub(U.U32Nat.dbl(m, 1n), 1n+x), U.U32Nat.low(k, x), k, U.U32Nat.high(k, x)), Equal.cong(Nat, Nat, zz => Nat.add(Nat.sub(U.U32Nat.dbl(m, 1n), 1n+x), 1n+zz), Nat.add(U.U32Nat.low(k, x), U.U32Nat.dbl(k, U.U32Nat.high(k, x))), x, Laws.low_high(k, x))), Laws.nat_lt_witness(x, U.U32Nat.dbl(m, 1n), h)), Equal.cong(Nat, Nat, zz => U.U32Nat.dbl(zz, 1n), m, Nat.add(k, j), Equal.sym(Nat, Nat.add(k, j), m, e))), Equal.sym(Nat, U.U32Nat.dbl(k, U.U32Nat.dbl(j, 1n)), U.U32Nat.dbl(Nat.add(k, j), 1n), Laws.dbl_dbl(k, j, 1n))))), Laws.nat_lt_add(U.U32Nat.dbl(k, U.U32Nat.high(k, x)), Nat.add(Nat.sub(U.U32Nat.dbl(m, 1n), 1n+x), U.U32Nat.low(k, x)))))

def ur.r45(+x0: Nat, +x1: Nat, +x2: Nat, +x3: Nat) -> {Nat.add(Nat.add(Nat.mul(x0, Nat.add(x1, 1n+x2)), Nat.add(x1, Nat.add(x2, Nat.add(Nat.mul(x3, x1), x3)))), 1n+Nat.mul(x3, x2)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}:
  %Equal.sym(Nat, Nat.add(x1, Nat.add(1n, x2)), Nat.add(1n, Nat.add(x1, x2)), Laws.nat_add_left_comm(x1, 1n, x2)) : {Nat.add(Nat.add(Nat.mul(x0, _), Nat.add(x1, Nat.add(x2, Nat.add(Nat.mul(x3, x1), x3)))), 1n+Nat.mul(x3, x2)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.mul(x0, Nat.add(1n, Nat.add(x1, x2))), Nat.add(Nat.mul(x0, 1n), Nat.mul(x0, Nat.add(x1, x2))), Laws.nat_mul_add(x0, 1n, Nat.add(x1, x2))) : {Nat.add(Nat.add(_, Nat.add(x1, Nat.add(x2, Nat.add(Nat.mul(x3, x1), x3)))), 1n+Nat.mul(x3, x2)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.mul(x0, Nat.add(x1, x2)), Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2)), Laws.nat_mul_add(x0, x1, x2)) : {Nat.add(Nat.add(Nat.add(Nat.mul(x0, 1n), _), Nat.add(x1, Nat.add(x2, Nat.add(Nat.mul(x3, x1), x3)))), 1n+Nat.mul(x3, x2)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.mul(x0, 1n), Nat.mul(1n, x0), Laws.nat_mul_comm(x0, 1n)) : {Nat.add(Nat.add(Nat.add(_, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2))), Nat.add(x1, Nat.add(x2, Nat.add(Nat.mul(x3, x1), x3)))), 1n+Nat.mul(x3, x2)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.mul(1n, x0), x0, Laws.nat_one_mul(x0)) : {Nat.add(Nat.add(Nat.add(_, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2))), Nat.add(x1, Nat.add(x2, Nat.add(Nat.mul(x3, x1), x3)))), 1n+Nat.mul(x3, x2)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.mul(x3, x1), Nat.mul(x1, x3), Laws.nat_mul_comm(x3, x1)) : {Nat.add(Nat.add(Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2))), Nat.add(x1, Nat.add(x2, Nat.add(_, x3)))), 1n+Nat.mul(x3, x2)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(Nat.mul(x1, x3), x3)), Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3)), Laws.nat_add_left_comm(x2, Nat.mul(x1, x3), x3)) : {Nat.add(Nat.add(Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2))), Nat.add(x1, _)), 1n+Nat.mul(x3, x2)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2))), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3)))), Nat.add(x0, Nat.add(Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2)), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3))))), Laws.nat_add_assoc(x0, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2)), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3))))) : {Nat.add(_, 1n+Nat.mul(x3, x2)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2)), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3)))), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3))))), Laws.nat_add_assoc(Nat.mul(x0, x1), Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3))))) : {Nat.add(Nat.add(x0, _), 1n+Nat.mul(x3, x2)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.mul(x3, x2), Nat.mul(x2, x3), Laws.nat_mul_comm(x3, x2)) : {Nat.add(Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3)))))), Nat.add(1n, _)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3)))))), Nat.add(1n, Nat.mul(x2, x3))), Nat.add(x0, Nat.add(Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3))))), Nat.add(1n, Nat.mul(x2, x3)))), Laws.nat_add_assoc(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3))))), Nat.add(1n, Nat.mul(x2, x3)))) : {_ == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3))))), Nat.add(1n, Nat.mul(x2, x3))), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3)))), Nat.add(1n, Nat.mul(x2, x3)))), Laws.nat_add_assoc(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3)))), Nat.add(1n, Nat.mul(x2, x3)))) : {Nat.add(x0, _) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3)))), Nat.add(1n, Nat.mul(x2, x3))), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3))), Nat.add(1n, Nat.mul(x2, x3)))), Laws.nat_add_assoc(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3))), Nat.add(1n, Nat.mul(x2, x3)))) : {Nat.add(x0, Nat.add(Nat.mul(x0, x1), _)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3))), Nat.add(1n, Nat.mul(x2, x3))), Nat.add(x1, Nat.add(Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3)), Nat.add(1n, Nat.mul(x2, x3)))), Laws.nat_add_assoc(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3)), Nat.add(1n, Nat.mul(x2, x3)))) : {Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), _))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(x1, x3), Nat.add(x2, x3)), Nat.add(1n, Nat.mul(x2, x3))), Nat.add(Nat.mul(x1, x3), Nat.add(Nat.add(x2, x3), Nat.add(1n, Nat.mul(x2, x3)))), Laws.nat_add_assoc(Nat.mul(x1, x3), Nat.add(x2, x3), Nat.add(1n, Nat.mul(x2, x3)))) : {Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, _)))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x2, x3), Nat.add(1n, Nat.mul(x2, x3))), Nat.add(x2, Nat.add(x3, Nat.add(1n, Nat.mul(x2, x3)))), Laws.nat_add_assoc(x2, x3, Nat.add(1n, Nat.mul(x2, x3)))) : {Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), _))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x3, Nat.add(1n, Nat.mul(x2, x3))), Nat.add(1n, Nat.add(x3, Nat.mul(x2, x3))), Laws.nat_add_left_comm(x3, 1n, Nat.mul(x2, x3))) : {Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, _)))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x3, Nat.mul(x2, x3)), Nat.add(Nat.mul(x2, x3), x3), Laws.nat_add_comm(x3, Nat.mul(x2, x3))) : {Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, Nat.add(1n, _))))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x2, Nat.add(1n, Nat.add(Nat.mul(x2, x3), x3))), Nat.add(1n, Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3))), Laws.nat_add_left_comm(x2, 1n, Nat.add(Nat.mul(x2, x3), x3))) : {Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), _))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x1, x3), Nat.add(1n, Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3)))), Nat.add(1n, Nat.add(Nat.mul(x1, x3), Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3)))), Laws.nat_add_left_comm(Nat.mul(x1, x3), 1n, Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3)))) : {Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, _)))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x1, Nat.add(1n, Nat.add(Nat.mul(x1, x3), Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3))))), Nat.add(1n, Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3))))), Laws.nat_add_left_comm(x1, 1n, Nat.add(Nat.mul(x1, x3), Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3))))) : {Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), _))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x2), Nat.add(1n, Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3)))))), Nat.add(1n, Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3)))))), Laws.nat_add_left_comm(Nat.mul(x0, x2), 1n, Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3)))))) : {Nat.add(x0, Nat.add(Nat.mul(x0, x1), _)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x1), Nat.add(1n, Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3))))))), Nat.add(1n, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3))))))), Laws.nat_add_left_comm(Nat.mul(x0, x1), 1n, Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3))))))) : {Nat.add(x0, _) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(1n, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3)))))))), Nat.add(1n, Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3)))))))), Laws.nat_add_left_comm(x0, 1n, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(Nat.mul(x1, x3), Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3)))))))) : {_ == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x1, x3), Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3))), Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3))), Equal.sym(Nat, Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3))), Nat.add(Nat.mul(x1, x3), Nat.add(x2, Nat.add(Nat.mul(x2, x3), x3))), Laws.nat_add_left_comm(x2, Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3)))) : {Nat.add(1n, Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x1, _))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3))))), Nat.add(x1, Nat.add(Nat.mul(x0, x2), Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3))))), Equal.sym(Nat, Nat.add(x1, Nat.add(Nat.mul(x0, x2), Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3))))), Nat.add(Nat.mul(x0, x2), Nat.add(x1, Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3))))), Laws.nat_add_left_comm(x1, Nat.mul(x0, x2), Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3)))))) : {Nat.add(1n, Nat.add(x0, Nat.add(Nat.mul(x0, x1), _))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x1), Nat.add(x1, Nat.add(Nat.mul(x0, x2), Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3)))))), Nat.add(x1, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3)))))), Equal.sym(Nat, Nat.add(x1, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3)))))), Nat.add(Nat.mul(x0, x1), Nat.add(x1, Nat.add(Nat.mul(x0, x2), Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3)))))), Laws.nat_add_left_comm(x1, Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3))))))) : {Nat.add(1n, Nat.add(x0, _)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x1, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3))))))), Nat.add(x1, Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3))))))), Equal.sym(Nat, Nat.add(x1, Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3))))))), Nat.add(x0, Nat.add(x1, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3))))))), Laws.nat_add_left_comm(x1, x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x2, Nat.add(Nat.mul(x1, x3), Nat.add(Nat.mul(x2, x3), x3)))))))) : {Nat.add(1n, _) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x2, x3), x3), Nat.add(x3, Nat.mul(x2, x3)), Equal.sym(Nat, Nat.add(x3, Nat.mul(x2, x3)), Nat.add(Nat.mul(x2, x3), x3), Laws.nat_add_comm(x3, Nat.mul(x2, x3)))) : {Nat.add(1n, Nat.add(x1, Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x2, Nat.add(Nat.mul(x1, x3), _))))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x1, x3), Nat.add(x3, Nat.mul(x2, x3))), Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3))), Equal.sym(Nat, Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3))), Nat.add(Nat.mul(x1, x3), Nat.add(x3, Nat.mul(x2, x3))), Laws.nat_add_left_comm(x3, Nat.mul(x1, x3), Nat.mul(x2, x3)))) : {Nat.add(1n, Nat.add(x1, Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x2, _)))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x2), Nat.add(x2, Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3))))), Nat.add(x2, Nat.add(Nat.mul(x0, x2), Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3))))), Equal.sym(Nat, Nat.add(x2, Nat.add(Nat.mul(x0, x2), Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3))))), Nat.add(Nat.mul(x0, x2), Nat.add(x2, Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3))))), Laws.nat_add_left_comm(x2, Nat.mul(x0, x2), Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3)))))) : {Nat.add(1n, Nat.add(x1, Nat.add(x0, Nat.add(Nat.mul(x0, x1), _)))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x1), Nat.add(x2, Nat.add(Nat.mul(x0, x2), Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3)))))), Nat.add(x2, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3)))))), Equal.sym(Nat, Nat.add(x2, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3)))))), Nat.add(Nat.mul(x0, x1), Nat.add(x2, Nat.add(Nat.mul(x0, x2), Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3)))))), Laws.nat_add_left_comm(x2, Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3))))))) : {Nat.add(1n, Nat.add(x1, Nat.add(x0, _))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(x0, Nat.add(x2, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3))))))), Nat.add(x2, Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3))))))), Equal.sym(Nat, Nat.add(x2, Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3))))))), Nat.add(x0, Nat.add(x2, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3))))))), Laws.nat_add_left_comm(x2, x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x3, Nat.add(Nat.mul(x1, x3), Nat.mul(x2, x3)))))))) : {Nat.add(1n, Nat.add(x1, _)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.mul(x2, x3), Nat.mul(x3, x2), Equal.sym(Nat, Nat.mul(x3, x2), Nat.mul(x2, x3), Laws.nat_mul_comm(x3, x2))) : {Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x3, Nat.add(Nat.mul(x1, x3), _)))))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.mul(x1, x3), Nat.mul(x3, x1), Equal.sym(Nat, Nat.mul(x3, x1), Nat.mul(x1, x3), Laws.nat_mul_comm(x3, x1))) : {Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(x3, Nat.add(_, Nat.mul(x3, x2))))))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, x3, Nat.mul(1n, x3), Equal.sym(Nat, Nat.mul(1n, x3), x3, Laws.nat_one_mul(x3))) : {Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(_, Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2))))))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.mul(1n, x3), Nat.mul(x3, 1n), Equal.sym(Nat, Nat.mul(x3, 1n), Nat.mul(1n, x3), Laws.nat_mul_comm(x3, 1n))) : {Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(x0, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(_, Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2))))))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, x0, Nat.mul(1n, x0), Equal.sym(Nat, Nat.mul(1n, x0), x0, Laws.nat_one_mul(x0))) : {Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(_, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2))))))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.mul(1n, x0), Nat.mul(x0, 1n), Equal.sym(Nat, Nat.mul(x0, 1n), Nat.mul(1n, x0), Laws.nat_mul_comm(x0, 1n))) : {Nat.add(1n, Nat.add(x1, Nat.add(x2, Nat.add(_, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2))))))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, x2, Nat.mul(1n, x2), Equal.sym(Nat, Nat.mul(1n, x2), x2, Laws.nat_one_mul(x2))) : {Nat.add(1n, Nat.add(x1, Nat.add(_, Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2))))))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, x1, Nat.mul(1n, x1), Equal.sym(Nat, Nat.mul(1n, x1), x1, Laws.nat_one_mul(x1))) : {Nat.add(1n, Nat.add(_, Nat.add(Nat.mul(1n, x2), Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2))))))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(1n, x1), Nat.add(Nat.mul(1n, x2), Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2)))))))), Nat.add(Nat.add(Nat.mul(1n, x1), Nat.mul(1n, x2)), Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2))))))), Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(1n, x1), Nat.mul(1n, x2)), Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2))))))), Nat.add(Nat.mul(1n, x1), Nat.add(Nat.mul(1n, x2), Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2)))))))), Laws.nat_add_assoc(Nat.mul(1n, x1), Nat.mul(1n, x2), Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2))))))))) : {Nat.add(Nat.mul(1n, 1n), _) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(1n, 1n), Nat.add(Nat.add(Nat.mul(1n, x1), Nat.mul(1n, x2)), Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2)))))))), Nat.add(Nat.add(Nat.mul(1n, 1n), Nat.add(Nat.mul(1n, x1), Nat.mul(1n, x2))), Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2))))))), Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(1n, 1n), Nat.add(Nat.mul(1n, x1), Nat.mul(1n, x2))), Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2))))))), Nat.add(Nat.mul(1n, 1n), Nat.add(Nat.add(Nat.mul(1n, x1), Nat.mul(1n, x2)), Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2)))))))), Laws.nat_add_assoc(Nat.mul(1n, 1n), Nat.add(Nat.mul(1n, x1), Nat.mul(1n, x2)), Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2))))))))) : {_ == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2))))), Nat.add(Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2)), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2)))), Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2)), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2)))), Nat.add(Nat.mul(x0, x1), Nat.add(Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2))))), Laws.nat_add_assoc(Nat.mul(x0, x1), Nat.mul(x0, x2), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2)))))) : {Nat.add(Nat.add(Nat.mul(1n, 1n), Nat.add(Nat.mul(1n, x1), Nat.mul(1n, x2))), Nat.add(Nat.mul(x0, 1n), _)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2)), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2))))), Nat.add(Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2))), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2)))), Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2))), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2)))), Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2)), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2))))), Laws.nat_add_assoc(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2)), Nat.add(Nat.mul(x3, 1n), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2)))))) : {Nat.add(Nat.add(Nat.mul(1n, 1n), Nat.add(Nat.mul(1n, x1), Nat.mul(1n, x2))), _) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2)), Nat.mul(x3, Nat.add(x1, x2)), Equal.sym(Nat, Nat.mul(x3, Nat.add(x1, x2)), Nat.add(Nat.mul(x3, x1), Nat.mul(x3, x2)), Laws.nat_mul_add(x3, x1, x2))) : {Nat.add(Nat.add(Nat.mul(1n, 1n), Nat.add(Nat.mul(1n, x1), Nat.mul(1n, x2))), Nat.add(Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2))), Nat.add(Nat.mul(x3, 1n), _))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x3, 1n), Nat.mul(x3, Nat.add(x1, x2))), Nat.mul(x3, Nat.add(1n, Nat.add(x1, x2))), Equal.sym(Nat, Nat.mul(x3, Nat.add(1n, Nat.add(x1, x2))), Nat.add(Nat.mul(x3, 1n), Nat.mul(x3, Nat.add(x1, x2))), Laws.nat_mul_add(x3, 1n, Nat.add(x1, x2)))) : {Nat.add(Nat.add(Nat.mul(1n, 1n), Nat.add(Nat.mul(1n, x1), Nat.mul(1n, x2))), Nat.add(Nat.add(Nat.mul(x0, 1n), Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2))), _)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2)), Nat.mul(x0, Nat.add(x1, x2)), Equal.sym(Nat, Nat.mul(x0, Nat.add(x1, x2)), Nat.add(Nat.mul(x0, x1), Nat.mul(x0, x2)), Laws.nat_mul_add(x0, x1, x2))) : {Nat.add(Nat.add(Nat.mul(1n, 1n), Nat.add(Nat.mul(1n, x1), Nat.mul(1n, x2))), Nat.add(Nat.add(Nat.mul(x0, 1n), _), Nat.mul(x3, Nat.add(1n, Nat.add(x1, x2))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, 1n), Nat.mul(x0, Nat.add(x1, x2))), Nat.mul(x0, Nat.add(1n, Nat.add(x1, x2))), Equal.sym(Nat, Nat.mul(x0, Nat.add(1n, Nat.add(x1, x2))), Nat.add(Nat.mul(x0, 1n), Nat.mul(x0, Nat.add(x1, x2))), Laws.nat_mul_add(x0, 1n, Nat.add(x1, x2)))) : {Nat.add(Nat.add(Nat.mul(1n, 1n), Nat.add(Nat.mul(1n, x1), Nat.mul(1n, x2))), Nat.add(_, Nat.mul(x3, Nat.add(1n, Nat.add(x1, x2))))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(x0, Nat.add(1n, Nat.add(x1, x2))), Nat.mul(x3, Nat.add(1n, Nat.add(x1, x2)))), Nat.mul(Nat.add(x0, x3), Nat.add(1n, Nat.add(x1, x2))), Equal.sym(Nat, Nat.mul(Nat.add(x0, x3), Nat.add(1n, Nat.add(x1, x2))), Nat.add(Nat.mul(x0, Nat.add(1n, Nat.add(x1, x2))), Nat.mul(x3, Nat.add(1n, Nat.add(x1, x2)))), Laws.nat_add_mul(x0, x3, Nat.add(1n, Nat.add(x1, x2))))) : {Nat.add(Nat.add(Nat.mul(1n, 1n), Nat.add(Nat.mul(1n, x1), Nat.mul(1n, x2))), _) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(1n, x1), Nat.mul(1n, x2)), Nat.mul(1n, Nat.add(x1, x2)), Equal.sym(Nat, Nat.mul(1n, Nat.add(x1, x2)), Nat.add(Nat.mul(1n, x1), Nat.mul(1n, x2)), Laws.nat_mul_add(1n, x1, x2))) : {Nat.add(Nat.add(Nat.mul(1n, 1n), _), Nat.mul(Nat.add(x0, x3), Nat.add(1n, Nat.add(x1, x2)))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(1n, 1n), Nat.mul(1n, Nat.add(x1, x2))), Nat.mul(1n, Nat.add(1n, Nat.add(x1, x2))), Equal.sym(Nat, Nat.mul(1n, Nat.add(1n, Nat.add(x1, x2))), Nat.add(Nat.mul(1n, 1n), Nat.mul(1n, Nat.add(x1, x2))), Laws.nat_mul_add(1n, 1n, Nat.add(x1, x2)))) : {Nat.add(_, Nat.mul(Nat.add(x0, x3), Nat.add(1n, Nat.add(x1, x2)))) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.mul(1n, Nat.add(1n, Nat.add(x1, x2))), Nat.mul(Nat.add(x0, x3), Nat.add(1n, Nat.add(x1, x2)))), Nat.mul(Nat.add(1n, Nat.add(x0, x3)), Nat.add(1n, Nat.add(x1, x2))), Equal.sym(Nat, Nat.mul(Nat.add(1n, Nat.add(x0, x3)), Nat.add(1n, Nat.add(x1, x2))), Nat.add(Nat.mul(1n, Nat.add(1n, Nat.add(x1, x2))), Nat.mul(Nat.add(x0, x3), Nat.add(1n, Nat.add(x1, x2)))), Laws.nat_add_mul(1n, Nat.add(x0, x3), Nat.add(1n, Nat.add(x1, x2))))) : {_ == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x1, x2)), Nat.add(x1, Nat.add(1n, x2)), Equal.sym(Nat, Nat.add(x1, Nat.add(1n, x2)), Nat.add(1n, Nat.add(x1, x2)), Laws.nat_add_left_comm(x1, 1n, x2))) : {Nat.mul(Nat.add(1n, Nat.add(x0, x3)), _) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  %Equal.sym(Nat, Nat.add(1n, Nat.add(x0, x3)), Nat.add(x0, Nat.add(1n, x3)), Equal.sym(Nat, Nat.add(x0, Nat.add(1n, x3)), Nat.add(1n, Nat.add(x0, x3)), Laws.nat_add_left_comm(x0, 1n, x3))) : {Nat.mul(_, Nat.add(x1, 1n+x2)) == Nat.mul(Nat.add(x0, 1n+x3), Nat.add(x1, 1n+x2)) : Nat}
  {==}

def Laws.nat_mul_lt(a, b, c, d, h1, h2):
  Equal.trans(Bool, Nat.is_lt(Nat.mul(a, b), Nat.mul(c, d)), Nat.is_lt(Nat.mul(a, b), Nat.add(Nat.add(Nat.mul(Nat.sub(c, 1n+a), Nat.add(Nat.sub(d, 1n+b), 1n+b)), Nat.add(Nat.sub(d, 1n+b), Nat.add(b, Nat.add(Nat.mul(a, Nat.sub(d, 1n+b)), a)))), 1n+Nat.mul(a, b))), True{}, Equal.sym(Bool, Nat.is_lt(Nat.mul(a, b), Nat.add(Nat.add(Nat.mul(Nat.sub(c, 1n+a), Nat.add(Nat.sub(d, 1n+b), 1n+b)), Nat.add(Nat.sub(d, 1n+b), Nat.add(b, Nat.add(Nat.mul(a, Nat.sub(d, 1n+b)), a)))), 1n+Nat.mul(a, b))), Nat.is_lt(Nat.mul(a, b), Nat.mul(c, d)), Equal.cong(Nat, Bool, zz => Nat.is_lt(Nat.mul(a, b), zz), Nat.add(Nat.add(Nat.mul(Nat.sub(c, 1n+a), Nat.add(Nat.sub(d, 1n+b), 1n+b)), Nat.add(Nat.sub(d, 1n+b), Nat.add(b, Nat.add(Nat.mul(a, Nat.sub(d, 1n+b)), a)))), 1n+Nat.mul(a, b)), Nat.mul(c, d), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Nat.sub(c, 1n+a), Nat.add(Nat.sub(d, 1n+b), 1n+b)), Nat.add(Nat.sub(d, 1n+b), Nat.add(b, Nat.add(Nat.mul(a, Nat.sub(d, 1n+b)), a)))), 1n+Nat.mul(a, b)), Nat.mul(c, Nat.add(Nat.sub(d, 1n+b), 1n+b)), Nat.mul(c, d), Equal.trans(Nat, Nat.add(Nat.add(Nat.mul(Nat.sub(c, 1n+a), Nat.add(Nat.sub(d, 1n+b), 1n+b)), Nat.add(Nat.sub(d, 1n+b), Nat.add(b, Nat.add(Nat.mul(a, Nat.sub(d, 1n+b)), a)))), 1n+Nat.mul(a, b)), Nat.mul(Nat.add(Nat.sub(c, 1n+a), 1n+a), Nat.add(Nat.sub(d, 1n+b), 1n+b)), Nat.mul(c, Nat.add(Nat.sub(d, 1n+b), 1n+b)), ur.r45(Nat.sub(c, 1n+a), Nat.sub(d, 1n+b), b, a), Equal.cong(Nat, Nat, zz => Nat.mul(zz, Nat.add(Nat.sub(d, 1n+b), 1n+b)), Nat.add(Nat.sub(c, 1n+a), 1n+a), c, Laws.nat_lt_witness(a, c, h1))), Equal.cong(Nat, Nat, zz => Nat.mul(c, zz), Nat.add(Nat.sub(d, 1n+b), 1n+b), d, Laws.nat_lt_witness(b, d, h2))))), Laws.nat_lt_add(Nat.mul(a, b), Nat.add(Nat.mul(Nat.sub(c, 1n+a), Nat.add(Nat.sub(d, 1n+b), 1n+b)), Nat.add(Nat.sub(d, 1n+b), Nat.add(b, Nat.add(Nat.mul(a, Nat.sub(d, 1n+b)), a))))))

def Laws.nat_le_dbl(k, x):
  match k:
    case 0n:
      Laws.nat_le_refl(x)
    case 1n+ +j:
      un.le_trans(x, U.U32Nat.dbl(j, x), Nat.double(U.U32Nat.dbl(j, x)), Laws.nat_le_dbl(j, x), un.le_double(U.U32Nat.dbl(j, x)))

def Laws.dbl_le_exp(j, k, x, h):
  Equal.trans(Bool, Nat.is_le(U.U32Nat.dbl(j, x), U.U32Nat.dbl(k, x)), Nat.is_le(U.U32Nat.dbl(j, x), U.U32Nat.dbl(Nat.sub(k, j), U.U32Nat.dbl(j, x))), True{}, Equal.sym(Bool, Nat.is_le(U.U32Nat.dbl(j, x), U.U32Nat.dbl(Nat.sub(k, j), U.U32Nat.dbl(j, x))), Nat.is_le(U.U32Nat.dbl(j, x), U.U32Nat.dbl(k, x)), Equal.cong(Nat, Bool, zz => Nat.is_le(U.U32Nat.dbl(j, x), zz), U.U32Nat.dbl(Nat.sub(k, j), U.U32Nat.dbl(j, x)), U.U32Nat.dbl(k, x), Equal.trans(Nat, U.U32Nat.dbl(Nat.sub(k, j), U.U32Nat.dbl(j, x)), U.U32Nat.dbl(Nat.add(Nat.sub(k, j), j), x), U.U32Nat.dbl(k, x), Laws.dbl_dbl(Nat.sub(k, j), j, x), Equal.cong(Nat, Nat, zz => U.U32Nat.dbl(zz, x), Nat.add(Nat.sub(k, j), j), k, Laws.nat_le_witness(j, k, h))))), Laws.nat_le_dbl(Nat.sub(k, j), U.U32Nat.dbl(j, x)))

def Laws.divstep_value(n, s, b, r, a, r1, t, l, g, e, el, eg, er, ha, hr, hb):
  ud.p1(Nat.add(r1, Nat.mul(U.U32Nat.bit(g), b)), Nat.add(a, Nat.double(r)), r1, b, ud.k(n, s, b, r, a, r1, t, l, g, e, el, eg, er, ha, hr, hb))

def Laws.divstep_lt(n, s, b, r, a, r1, t, l, g, e, el, eg, er, ha, hr, hb):
  ud.p2(Nat.add(r1, Nat.mul(U.U32Nat.bit(g), b)), Nat.add(a, Nat.double(r)), r1, b, ud.k(n, s, b, r, a, r1, t, l, g, e, el, eg, er, ha, hr, hb))
