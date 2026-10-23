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
