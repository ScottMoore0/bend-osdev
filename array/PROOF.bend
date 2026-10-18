# Proofs of LAWS.bend. Internal lemmas are prefixed AP.
#
# The method: an array is reflected, once, into a Data tree (AP.Tree) with an
# equation between the tree's array and the array, so that the lemmas can
# mention it as often as they need. On the tree, AP.size, AP.swap_t,
# AP.swap_v and AP.get_v mirror Base's Array.size, Array.swap.go and
# Array.get.go with the same index arithmetic, so Base's code on a built tree
# is the mirror by plain induction. For the list model, the index arithmetic
# is tied to the indices' values: U32's order is its value's order, Word.sub
# subtracts, halving 2^(d+1) gives 2^d, and 2^d - 1 masks the low d bits.
import Base
import ./array.bend as A
import ./LAWS.bend as Laws

def AP.bool_t(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def AP.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : AP.bool_t(_)
  Unit{}

def AP.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : AP.bool_t(_)
  Unit{}

def AP.nat_t(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

# 1 + k is never 0
def AP.sz(-k: Nat, e: {1n+k == 0n : Nat}) -> Empty:
  %Equal.sym(Nat, 1n+k, 0n, e) : AP.nat_t(_)
  Unit{}

def AP.succ_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def AP.double_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {Nat.double(a) == Nat.double(b) : Nat}:
  %e : {Nat.double(a) == Nat.double(_) : Nat}
  {==}

# Nat arithmetic

def AP.add_zero(x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      AP.succ_cong(Nat.add(p, 0n), p, AP.add_zero(p))

def AP.add_succ(x: Nat, -y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      AP.succ_cong(Nat.add(p, 1n+y), 1n+Nat.add(p, y), AP.add_succ(p, y))

def AP.add_comm(x: Nat, +y: Nat) -> {Nat.add(x, y) == Nat.add(y, x) : Nat}:
  match x:
    case 0n:
      Equal.sym(Nat, Nat.add(y, 0n), y, AP.add_zero(y))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, y), 1n+Nat.add(y, p), Nat.add(y, 1n+p), AP.succ_cong(Nat.add(p, y), Nat.add(y, p), AP.add_comm(p, y)), Equal.sym(Nat, Nat.add(y, 1n+p), 1n+Nat.add(y, p), AP.add_succ(y, p)))

def AP.double_add(x: Nat, -y: Nat) -> {Nat.double(Nat.add(x, y)) == Nat.add(Nat.double(x), Nat.double(y)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      AP.succ_cong(1n+Nat.double(Nat.add(p, y)), 1n+Nat.add(Nat.double(p), Nat.double(y)), AP.succ_cong(Nat.double(Nat.add(p, y)), Nat.add(Nat.double(p), Nat.double(y)), AP.double_add(p, y)))

def AP.double_self(+x: Nat) -> {Nat.double(x) == Nat.add(x, x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), AP.add_succ(p, p)) : {2n+Nat.double(p) == 1n+_ : Nat}
      AP.succ_cong(1n+Nat.double(p), 1n+Nat.add(p, p), AP.succ_cong(Nat.double(p), Nat.add(p, p), AP.double_self(p)))

def AP.sub_add_l(y: Nat, +r: Nat) -> {Nat.sub(Nat.add(y, r), y) == r : Nat}:
  match y:
    case 0n:
      match r:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+q:
      AP.sub_add_l(q, r)

def AP.sub_add(+r: Nat, +y: Nat) -> {Nat.sub(Nat.add(r, y), y) == r : Nat}:
  %AP.add_comm(y, r) : {Nat.sub(_, y) == r : Nat}
  AP.sub_add_l(y, r)

def AP.lt_cancel(s: Nat, -r: Nat, -u: Nat) -> {Nat.is_lt(Nat.add(s, r), Nat.add(s, u)) == Nat.is_lt(r, u) : Bool}:
  match s:
    case 0n:
      {==}
    case 1n+q:
      AP.lt_cancel(q, r, u)

def AP.le_succ(y: Nat, x: Nat) -> {Nat.is_le(1n+y, x) == Nat.is_lt(y, x) : Bool}:
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
      AP.le_succ(q, p)

def AP.not_lt_le(x: Nat, y: Nat, e: {Nat.is_lt(x, y) == False{} : Bool}) -> {Nat.is_le(y, x) == True{} : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, AP.tf(e))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      AP.not_lt_le(p, q, e)

def AP.lt_one(x: Nat, e: {Nat.is_lt(x, 1n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          Empty.absurd({1n == 0n : Nat}, AP.ft(e))
        case 1n+q:
          Empty.absurd({2n+q == 0n : Nat}, AP.ft(e))

def AP.double_zero(x: Nat, e: {Nat.double(x) == 0n : Nat}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, AP.sz(1n+Nat.double(p), e))

# the value of a word's lowest bit and the rest: Word.to_nat of WCon{b, t}

def AP.bv(b: Bool, x: Nat) -> Nat:
  match b:
    case False{}:
      Nat.double(x)
    case True{}:
      1n+Nat.double(x)

def AP.nc(x: Nat, y: Nat, a: Bool, b: Bool) -> {Nat.cmp(AP.bv(a, x), AP.bv(b, y)) == Word.cmp.fin(a, b, Nat.cmp(x, y)) : Cmp}:
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
          AP.nc(p, q, False{}, False{})
        case False{} True{}:
          AP.nc(p, q, False{}, True{})
        case True{} False{}:
          AP.nc(p, q, True{}, False{})
        case True{} True{}:
          AP.nc(p, q, True{}, True{})

def AP.vc(-p: Nat, b: Bool, -t: Word(p)) -> {AP.bv(b, Word.to_nat(p, t)) == Word.to_nat(1n+p, WCon{b, t}) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# Word.cmp is the order of the words' values

def AP.cmp_nat(n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          %Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(xv, yv), AP.cmp_nat(p, at, bt)) : {Word.cmp.fin(x, y, _) == Nat.cmp(Word.to_nat(1n+p, WCon{x, at}), Word.to_nat(1n+p, WCon{y, bt})) : Cmp}
          %AP.vc(p, x, at) : {Word.cmp.fin(x, y, Nat.cmp(xv, yv)) == Nat.cmp(_, Word.to_nat(1n+p, WCon{y, bt})) : Cmp}
          %AP.vc(p, y, bt) : {Word.cmp.fin(x, y, Nat.cmp(xv, yv)) == Nat.cmp(AP.bv(x, xv), _) : Cmp}
          Equal.sym(Cmp, Nat.cmp(AP.bv(x, xv), AP.bv(y, yv)), Word.cmp.fin(x, y, Nat.cmp(xv, yv)), AP.nc(xv, yv, x, y))

# U32's order is its value's order

def AP.u32_cmp(a: U32, b: U32) -> {U32.cmp(a, b) == Nat.cmp(U32.to_nat(a), U32.to_nat(b)) : Cmp}:
  match a b:
    case U32{x} U32{y}:
      AP.cmp_nat(32n, x, y)

def AP.u32_lt(+a: U32, +b: U32) -> {U32.is_lt(a, b) == Nat.is_lt(U32.to_nat(a), U32.to_nat(b)) : Bool}:
  %AP.u32_cmp(a, b) : {Cmp.is_lt(U32.cmp(a, b)) == Cmp.is_lt(_) : Bool}
  {==}

def AP.u32_eq(+a: U32, +b: U32) -> {U32.is_eq(a, b) == Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) : Bool}:
  %AP.u32_cmp(a, b) : {Cmp.is_eq(U32.cmp(a, b)) == Cmp.is_eq(_) : Bool}
  {==}

# Subtraction: Word.adc with a complemented second operand subtracts

def AP.cb(c: Bool) -> Nat:
  match c:
    case True{}:
      0n
    case False{}:
      1n

def AP.fin_le_ff(c: Cmp) -> {Cmp.is_le(Word.cmp.fin(False{}, False{}, c)) == Cmp.is_le(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def AP.fin_le_tf(c: Cmp) -> {Cmp.is_le(Word.cmp.fin(True{}, False{}, c)) == Cmp.is_lt(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def AP.fin_le_ft(c: Cmp) -> {Cmp.is_le(Word.cmp.fin(False{}, True{}, c)) == Cmp.is_le(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def AP.fin_lt_xf(b: Bool, c: Cmp) -> {Cmp.is_lt(Word.cmp.fin(b, False{}, c)) == Cmp.is_lt(c) : Bool}:
  match b c:
    case False{} LT{}:
      {==}
    case False{} EQ{}:
      {==}
    case False{} GT{}:
      {==}
    case True{} LT{}:
      {==}
    case True{} EQ{}:
      {==}
    case True{} GT{}:
      {==}

def AP.le_bits(+y: Nat, +x: Nat, +a: Bool, +b: Bool, h: {Nat.is_le(AP.bv(a, y), AP.bv(b, x)) == True{} : Bool}) -> {Cmp.is_le(Word.cmp.fin(a, b, Nat.cmp(y, x))) == True{} : Bool}:
  %AP.nc(y, x, a, b) : {Cmp.is_le(_) == True{} : Bool}
  h

def AP.lt_bits(+y: Nat, +x: Nat, +a: Bool, +b: Bool, h: {Nat.is_lt(AP.bv(a, y), AP.bv(b, x)) == True{} : Bool}) -> {Cmp.is_lt(Word.cmp.fin(a, b, Nat.cmp(y, x))) == True{} : Bool}:
  %AP.nc(y, x, a, b) : {Cmp.is_lt(_) == True{} : Bool}
  h

def AP.ha(+y: Nat, +x: Nat, h: {Nat.is_le(AP.bv(False{}, y), AP.bv(False{}, x)) == True{} : Bool}) -> {Nat.is_le(y, x) == True{} : Bool}:
  %AP.fin_le_ff(Nat.cmp(y, x)) : {_ == True{} : Bool}
  AP.le_bits(y, x, False{}, False{}, h)

def AP.hb(+y: Nat, +x: Nat, h: {Nat.is_le(AP.bv(True{}, y), AP.bv(False{}, x)) == True{} : Bool}) -> {Nat.is_le(1n+y, x) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(1n+y, x), Nat.is_lt(y, x), AP.le_succ(y, x)) : {_ == True{} : Bool}
  %AP.fin_le_tf(Nat.cmp(y, x)) : {_ == True{} : Bool}
  AP.le_bits(y, x, True{}, False{}, h)

def AP.hc(+y: Nat, +x: Nat, h: {Nat.is_le(AP.bv(False{}, y), AP.bv(True{}, x)) == True{} : Bool}) -> {Nat.is_le(y, x) == True{} : Bool}:
  %AP.fin_le_ft(Nat.cmp(y, x)) : {_ == True{} : Bool}
  AP.le_bits(y, x, False{}, True{}, h)

def AP.alg2(+r: Nat, +y: Nat) -> {Nat.double(Nat.add(r, 1n+y)) == Nat.add(1n+Nat.double(r), 1n+Nat.double(y)) : Nat}:
  %Equal.sym(Nat, Nat.add(r, 1n+y), 1n+Nat.add(r, y), AP.add_succ(r, y)) : {Nat.double(_) == Nat.add(1n+Nat.double(r), 1n+Nat.double(y)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.double(r), 1n+Nat.double(y)), 1n+Nat.add(Nat.double(r), Nat.double(y)), AP.add_succ(Nat.double(r), Nat.double(y))) : {Nat.double(1n+Nat.add(r, y)) == 1n+_ : Nat}
  AP.succ_cong(1n+Nat.double(Nat.add(r, y)), 1n+Nat.add(Nat.double(r), Nat.double(y)), AP.succ_cong(Nat.double(Nat.add(r, y)), Nat.add(Nat.double(r), Nat.double(y)), AP.double_add(r, y)))

def AP.alg4(+r: Nat, +y: Nat) -> {Nat.double(Nat.add(r, 1n+y)) == Nat.add(Nat.double(r), 2n+Nat.double(y)) : Nat}:
  %Equal.sym(Nat, Nat.add(r, 1n+y), 1n+Nat.add(r, y), AP.add_succ(r, y)) : {Nat.double(_) == Nat.add(Nat.double(r), 2n+Nat.double(y)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.double(r), 2n+Nat.double(y)), 1n+Nat.add(Nat.double(r), 1n+Nat.double(y)), AP.add_succ(Nat.double(r), 1n+Nat.double(y))) : {Nat.double(1n+Nat.add(r, y)) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.double(r), 1n+Nat.double(y)), 1n+Nat.add(Nat.double(r), Nat.double(y)), AP.add_succ(Nat.double(r), Nat.double(y))) : {Nat.double(1n+Nat.add(r, y)) == 1n+_ : Nat}
  AP.succ_cong(1n+Nat.double(Nat.add(r, y)), 1n+Nat.add(Nat.double(r), Nat.double(y)), AP.succ_cong(Nat.double(Nat.add(r, y)), Nat.add(Nat.double(r), Nat.double(y)), AP.double_add(r, y)))

def AP.alg6(+r: Nat, +y: Nat) -> {1n+Nat.double(Nat.add(r, y)) == Nat.add(Nat.double(r), 1n+Nat.double(y)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.double(r), 1n+Nat.double(y)), 1n+Nat.add(Nat.double(r), Nat.double(y)), AP.add_succ(Nat.double(r), Nat.double(y))) : {1n+Nat.double(Nat.add(r, y)) == _ : Nat}
  AP.succ_cong(Nat.double(Nat.add(r, y)), Nat.add(Nat.double(r), Nat.double(y)), AP.double_add(r, y))

# for b <= a (b < a when the carry in c is False):
# a = adc(a, b, True, c) + (1 - c) + b
def AP.adc(n: Nat, a: Word(n), b: Word(n), c: Bool, h: {Nat.is_le(Nat.add(AP.cb(c), Word.to_nat(n, b)), Word.to_nat(n, a)) == True{} : Bool}) -> {Word.to_nat(n, a) == Nat.add(Word.to_nat(n, Word.adc(n, a, b, True{}, c)), Nat.add(AP.cb(c), Word.to_nat(n, b))) : Nat}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} True{}:
          {==}
        case WNil{} WNil{} False{}:
          Empty.absurd({0n == 1n : Nat}, AP.ft(h))
    case 1n+ +p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          +r = Word.to_nat(p, Word.adc(p, at, bt, True{}, True{}))
          %Equal.sym(Nat, xv, Nat.add(r, yv), AP.adc(p, at, bt, True{}, AP.ha(yv, xv, h))) : {Nat.double(_) == Nat.add(Nat.double(r), Nat.double(yv)) : Nat}
          AP.double_add(r, yv)
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          +r = Word.to_nat(p, Word.adc(p, at, bt, True{}, False{}))
          %Equal.sym(Nat, xv, Nat.add(r, 1n+yv), AP.adc(p, at, bt, False{}, AP.hb(yv, xv, h))) : {Nat.double(_) == Nat.add(1n+Nat.double(r), 1n+Nat.double(yv)) : Nat}
          AP.alg2(r, yv)
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          +r = Word.to_nat(p, Word.adc(p, at, bt, True{}, True{}))
          %Equal.sym(Nat, xv, Nat.add(r, yv), AP.adc(p, at, bt, True{}, AP.hc(yv, xv, h))) : {1n+Nat.double(_) == 1n+Nat.add(Nat.double(r), Nat.double(yv)) : Nat}
          AP.succ_cong(Nat.double(Nat.add(r, yv)), Nat.add(Nat.double(r), Nat.double(yv)), AP.double_add(r, yv))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          +r = Word.to_nat(p, Word.adc(p, at, bt, True{}, True{}))
          %Equal.sym(Nat, xv, Nat.add(r, yv), AP.adc(p, at, bt, True{}, AP.ha(yv, xv, h))) : {1n+Nat.double(_) == Nat.add(Nat.double(r), 1n+Nat.double(yv)) : Nat}
          AP.alg6(r, yv)
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          +r = Word.to_nat(p, Word.adc(p, at, bt, True{}, False{}))
          %Equal.sym(Nat, xv, Nat.add(r, 1n+yv), AP.adc(p, at, bt, False{}, AP.hb(yv, xv, h))) : {Nat.double(_) == Nat.add(1n+Nat.double(r), 1n+Nat.double(yv)) : Nat}
          AP.alg2(r, yv)
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          +r = Word.to_nat(p, Word.adc(p, at, bt, True{}, False{}))
          %Equal.sym(Nat, xv, Nat.add(r, 1n+yv), AP.adc(p, at, bt, False{}, AP.ha(1n+yv, xv, h))) : {Nat.double(_) == Nat.add(Nat.double(r), 2n+Nat.double(yv)) : Nat}
          AP.alg4(r, yv)
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          +r = Word.to_nat(p, Word.adc(p, at, bt, True{}, True{}))
          %Equal.sym(Nat, xv, Nat.add(r, yv), AP.adc(p, at, bt, True{}, AP.ha(yv, xv, h))) : {1n+Nat.double(_) == Nat.add(Nat.double(r), 1n+Nat.double(yv)) : Nat}
          AP.alg6(r, yv)
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          +xv = Word.to_nat(p, at)
          +yv = Word.to_nat(p, bt)
          +r = Word.to_nat(p, Word.adc(p, at, bt, True{}, False{}))
          %Equal.sym(Nat, xv, Nat.add(r, 1n+yv), AP.adc(p, at, bt, False{}, AP.hb(yv, xv, h))) : {1n+Nat.double(_) == 1n+Nat.add(Nat.double(r), 2n+Nat.double(yv)) : Nat}
          AP.succ_cong(Nat.double(Nat.add(r, 1n+yv)), Nat.add(Nat.double(r), 2n+Nat.double(yv)), AP.alg4(r, yv))

def AP.u32_sub(a: U32, b: U32, h: {Nat.is_le(U32.to_nat(b), U32.to_nat(a)) == True{} : Bool}) -> {U32.to_nat(U32.sub(a, b)) == Nat.sub(U32.to_nat(a), U32.to_nat(b)) : Nat}:
  match a b:
    case U32{+x} U32{+y}:
      +xv = Word.to_nat(32n, x)
      +yv = Word.to_nat(32n, y)
      +r = Word.to_nat(32n, Word.adc(32n, x, y, True{}, True{}))
      %Equal.sym(Nat, xv, Nat.add(r, yv), AP.adc(32n, x, y, True{}, h)) : {r == Nat.sub(_, yv) : Nat}
      Equal.sym(Nat, Nat.sub(Nat.add(r, yv), yv), r, AP.sub_add(r, yv))

def AP.wcon_cong(-p: Nat, -b: Bool, -x: Word(p), -y: Word(p), e: {x == y : Word(p)}) -> {WCon{b, x} == WCon{b, y} : Word(1n+p)}:
  %e : {WCon{b, x} == WCon{b, _} : Word(1n+p)}
  {==}

def AP.u32_cong(-x: Word(32n), -y: Word(32n), e: {x == y : Word(32n)}) -> {U32{x} == U32{y} : U32}:
  %e : {U32{x} == U32{_} : U32}
  {==}

# 2^d as a word, and the mask of the low d bits

def AP.pw(n: Nat, d: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+q:
      match d:
        case 0n:
          WCon{True{}, Word.zero(q)}
        case 1n+e:
          WCon{False{}, AP.pw(q, e)}

def AP.lm(n: Nat, d: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+q:
      match d:
        case 0n:
          WCon{False{}, Word.zero(q)}
        case 1n+e:
          WCon{True{}, AP.lm(q, e)}

def AP.spzz(n: Nat) -> {Word.shl.put(n, False{}, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+ +q:
      AP.wcon_cong(q, False{}, Word.shl.put(q, False{}, Word.zero(q)), Word.zero(q), AP.spzz(q))

def AP.spz(n: Nat) -> {Word.shl.put(n, True{}, Word.zero(n)) == AP.pw(n, 0n) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+ +q:
      AP.wcon_cong(q, True{}, Word.shl.put(q, False{}, Word.zero(q)), Word.zero(q), AP.spzz(q))

def AP.sp(n: Nat, d: Nat) -> {Word.shl.put(n, False{}, AP.pw(n, d)) == AP.pw(n, 1n+d) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+ +q:
      match d:
        case 0n:
          AP.wcon_cong(q, False{}, Word.shl.put(q, True{}, Word.zero(q)), AP.pw(q, 0n), AP.spz(q))
        case 1n+ +e:
          AP.wcon_cong(q, False{}, Word.shl.put(q, False{}, AP.pw(q, e)), AP.pw(q, 1n+e), AP.sp(q, e))

def AP.shl_put(n: Nat, w: Word(n)) -> {Word.shl(n, w) == Word.shl.put(n, False{}, w) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+q:
      match w:
        case WCon{b, t}:
          {==}

# shln(1, d) is 2^d
def AP.shln_pw(d: Nat) -> {U32.shln(1, d) == U32{AP.pw(32n, d)} : U32}:
  match d:
    case 0n:
      {==}
    case 1n+ +e:
      %Equal.sym(U32, U32.shln(1, e), U32{AP.pw(32n, e)}, AP.shln_pw(e)) : {U32.shl(_) == U32{AP.pw(32n, 1n+e)} : U32}
      AP.u32_cong(Word.shl(32n, AP.pw(32n, e)), AP.pw(32n, 1n+e), Equal.trans(Word(32n), Word.shl(32n, AP.pw(32n, e)), Word.shl.put(32n, False{}, AP.pw(32n, e)), AP.pw(32n, 1n+e), AP.shl_put(32n, AP.pw(32n, e)), AP.sp(32n, e)))

def AP.padz(n: Nat) -> {Word.shr.pad(n, Word.zero(n)) == Word.zero(1n+n) : Word(1n+n)}:
  match n:
    case 0n:
      {==}
    case 1n+ +q:
      AP.wcon_cong(1n+q, False{}, Word.shr.pad(q, Word.zero(q)), Word.zero(1n+q), AP.padz(q))

def AP.padp(n: Nat, d: Nat, h: {Nat.is_lt(d, n) == True{} : Bool}) -> {Word.shr.pad(n, AP.pw(n, d)) == AP.pw(1n+n, d) : Word(1n+n)}:
  match n:
    case 0n:
      match d:
        case 0n:
          Empty.absurd({Word.shr.pad(0n, AP.pw(0n, 0n)) == AP.pw(1n, 0n) : Word(1n)}, AP.ft(h))
        case 1n+e:
          Empty.absurd({Word.shr.pad(0n, AP.pw(0n, 1n+e)) == AP.pw(1n, 1n+e) : Word(1n)}, AP.ft(h))
    case 1n+ +q:
      match d:
        case 0n:
          AP.wcon_cong(1n+q, True{}, Word.shr.pad(q, Word.zero(q)), Word.zero(1n+q), AP.padz(q))
        case 1n+ +e:
          AP.wcon_cong(1n+q, False{}, Word.shr.pad(q, AP.pw(q, e)), AP.pw(1n+q, e), AP.padp(q, e, h))

def AP.shr_pw(n: Nat, d: Nat, h: {Nat.is_lt(1n+d, n) == True{} : Bool}) -> {Word.shr(n, AP.pw(n, 1n+d)) == AP.pw(n, d) : Word(n)}:
  match n:
    case 0n:
      Empty.absurd({Word.shr(0n, AP.pw(0n, 1n+d)) == AP.pw(0n, d) : Word(0n)}, AP.ft(h))
    case 1n+q:
      AP.padp(q, d, h)

def AP.pw_shln(+d: Nat) -> {U32{AP.pw(32n, d)} == U32.shln(1, d) : U32}:
  Equal.sym(U32, U32.shln(1, d), U32{AP.pw(32n, d)}, AP.shln_pw(d))

# halving 2^(d+1) gives 2^d (below 2^32)
def AP.shr_shln(+d: Nat, h: {Nat.is_lt(1n+d, 32n) == True{} : Bool}) -> {U32.shr(U32.shln(1, 1n+d)) == U32.shln(1, d) : U32}:
  %AP.pw_shln(1n+d) : {U32.shr(_) == U32.shln(1, d) : U32}
  %AP.pw_shln(d) : {U32.shr(U32{AP.pw(32n, 1n+d)}) == _ : U32}
  AP.u32_cong(Word.shr(32n, AP.pw(32n, 1n+d)), AP.pw(32n, d), AP.shr_pw(32n, d, h))

# values

def AP.val_zero(n: Nat) -> {Word.to_nat(n, Word.zero(n)) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +q:
      %Equal.sym(Nat, Word.to_nat(q, Word.zero(q)), 0n, AP.val_zero(q)) : {Nat.double(_) == 0n : Nat}
      {==}

def AP.val_pw(n: Nat, d: Nat, h: {Nat.is_lt(d, n) == True{} : Bool}) -> {Word.to_nat(n, AP.pw(n, d)) == A.Arrays.slots(d) : Nat}:
  match n:
    case 0n:
      match d:
        case 0n:
          Empty.absurd({Word.to_nat(0n, AP.pw(0n, 0n)) == A.Arrays.slots(0n) : Nat}, AP.ft(h))
        case 1n+e:
          Empty.absurd({Word.to_nat(0n, AP.pw(0n, 1n+e)) == A.Arrays.slots(1n+e) : Nat}, AP.ft(h))
    case 1n+ +q:
      match d:
        case 0n:
          %Equal.sym(Nat, Word.to_nat(q, Word.zero(q)), 0n, AP.val_zero(q)) : {1n+Nat.double(_) == 1n : Nat}
          {==}
        case 1n+ +e:
          AP.double_cong(Word.to_nat(q, AP.pw(q, e)), A.Arrays.slots(e), AP.val_pw(q, e, h))

def AP.val_shln(+d: Nat, h: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {U32.to_nat(U32.shln(1, d)) == A.Arrays.slots(d) : Nat}:
  %AP.pw_shln(d) : {U32.to_nat(_) == A.Arrays.slots(d) : Nat}
  AP.val_pw(32n, d, h)

# 2^d - 1 is the mask of the low d bits

def AP.z1(n: Nat) -> {Word.adc(n, Word.zero(n), Word.zero(n), True{}, True{}) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+ +q:
      AP.wcon_cong(q, False{}, Word.adc(q, Word.zero(q), Word.zero(q), True{}, True{}), Word.zero(q), AP.z1(q))

def AP.z2(n: Nat, d: Nat) -> {Word.adc(n, AP.pw(n, d), Word.zero(n), True{}, False{}) == AP.lm(n, d) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+ +q:
      match d:
        case 0n:
          AP.wcon_cong(q, False{}, Word.adc(q, Word.zero(q), Word.zero(q), True{}, True{}), Word.zero(q), AP.z1(q))
        case 1n+ +e:
          AP.wcon_cong(q, True{}, Word.adc(q, AP.pw(q, e), Word.zero(q), True{}, False{}), AP.lm(q, e), AP.z2(q, e))

def AP.sub_one(n: Nat, d: Nat) -> {Word.sub(n, AP.pw(n, d), AP.pw(n, 0n)) == AP.lm(n, d) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+ +q:
      match d:
        case 0n:
          AP.wcon_cong(q, False{}, Word.adc(q, Word.zero(q), Word.zero(q), True{}, True{}), Word.zero(q), AP.z1(q))
        case 1n+ +e:
          AP.wcon_cong(q, True{}, Word.adc(q, AP.pw(q, e), Word.zero(q), True{}, False{}), AP.lm(q, e), AP.z2(q, e))

def AP.mask_lm(+d: Nat) -> {U32.sub(U32.shln(1, d), 1) == U32{AP.lm(32n, d)} : U32}:
  %AP.pw_shln(d) : {U32.sub(_, 1) == U32{AP.lm(32n, d)} : U32}
  AP.u32_cong(Word.sub(32n, AP.pw(32n, d), AP.pw(32n, 0n)), AP.lm(32n, d), AP.sub_one(32n, d))


# A Data mirror of an array, so that lemmas can mention one array many times

type AP.Tree<-T: Data> is Data:
  APLeaf{value: T}
  APNode{xs: AP.Tree<T>, ys: AP.Tree<T>}

def AP.build(-T: Data, t: AP.Tree<T>) -> Array<T>:
  match t:
    case APLeaf{x}:
      ALeaf{x}
    case APNode{xs, ys}:
      ANode{AP.build(T, xs), AP.build(T, ys)}

def AP.reflect.node(-T: Data, -tx: AP.Tree<T>, -ty: AP.Tree<T>, -xs: Array<T>, -ys: Array<T>, ex: {AP.build(T, tx) == xs : Array<T>}, ey: {AP.build(T, ty) == ys : Array<T>}) -> {ANode{AP.build(T, tx), AP.build(T, ty)} == ANode{xs, ys} : Array<T>}:
  %ex : {ANode{AP.build(T, tx), AP.build(T, ty)} == ANode{_, ys} : Array<T>}
  %ey : {ANode{AP.build(T, tx), AP.build(T, ty)} == ANode{AP.build(T, tx), _} : Array<T>}
  {==}

def AP.reflect.join(-T: Data, -xs: Array<T>, -ys: Array<T>, rx: &t: AP.Tree<T> -> {AP.build(T, t) == xs : Array<T>}, ry: &t: AP.Tree<T> -> {AP.build(T, t) == ys : Array<T>}) -> &t: AP.Tree<T> -> {AP.build(T, t) == ANode{xs, ys} : Array<T>}:
  (tx, ex) = rx
  (ty, ey) = ry
  (APNode{tx, ty}, AP.reflect.node(T, tx, ty, xs, ys, ex, ey))

def AP.reflect(-T: Data, a: Array<T>) -> &t: AP.Tree<T> -> {AP.build(T, t) == a : Array<T>}:
  match a:
    case ALeaf{x}:
      (APLeaf{x}, {==})
    case ANode{xs, ys}:
      AP.reflect.join(T, xs, ys, AP.reflect(T, xs), AP.reflect(T, ys))

# Bool facts

def AP.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, AP.ft(e))

def AP.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, AP.ft(e))

# The mirror of Base's array code on the Data tree: the same index
# arithmetic, so each lemma below is a plain induction

def AP.size(-T: Data, t: AP.Tree<T>) -> U32:
  match t:
    case APLeaf{x}:
      1
    case APNode{xs, ys}:
      U32.shl(AP.size(T, xs))

def AP.swap_t(-T: Data, t: AP.Tree<T>, n: U32, +i: U32, v: T, z: Bool) -> AP.Tree<T>:
  match t z:
    case APLeaf{x} _:
      APLeaf{v}
    case APNode{xs, ys} True{}:
      +h = U32.shr(n)
      APNode{AP.swap_t(T, xs, h, i, v, U32.is_lt(i, U32.shr(h))), ys}
    case APNode{xs, ys} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      APNode{xs, AP.swap_t(T, ys, h, j, v, U32.is_lt(j, U32.shr(h)))}

def AP.swap_v(-T: Data, t: AP.Tree<T>, n: U32, +i: U32, v: T, z: Bool) -> T:
  match t z:
    case APLeaf{x} _:
      x
    case APNode{xs, ys} True{}:
      +h = U32.shr(n)
      AP.swap_v(T, xs, h, i, v, U32.is_lt(i, U32.shr(h)))
    case APNode{xs, ys} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      AP.swap_v(T, ys, h, j, v, U32.is_lt(j, U32.shr(h)))

def AP.get_v(-T: Data, t: AP.Tree<T>, n: U32, +i: U32, z: Bool) -> T:
  match t z:
    case APLeaf{x} _:
      x
    case APNode{xs, ys} True{}:
      +h = U32.shr(n)
      AP.get_v(T, xs, h, i, U32.is_lt(i, U32.shr(h)))
    case APNode{xs, ys} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      AP.get_v(T, ys, h, j, U32.is_lt(j, U32.shr(h)))

def AP.mask(+n: U32, i: U32) -> U32:
  U32.and(i, U32.sub(n, 1))

def AP.z(+n: U32, +j: U32) -> Bool:
  U32.is_lt(j, U32.shr(n))

def AP.get_top(-T: Data, +t: AP.Tree<T>, i: U32) -> T:
  +n = AP.size(T, t)
  +j = AP.mask(n, i)
  AP.get_v(T, t, n, j, AP.z(n, j))

def AP.set_top(-T: Data, +t: AP.Tree<T>, i: U32, v: T) -> AP.Tree<T>:
  +n = AP.size(T, t)
  +j = AP.mask(n, i)
  AP.swap_t(T, t, n, j, v, AP.z(n, j))

# Base's code on a built tree is the mirror

def AP.size_eq(-T: Data, t: AP.Tree<T>) -> {Array.size(T, AP.build(T, t)) == (AP.build(T, t), AP.size(T, t)) : Array<T> & U32}:
  match t:
    case APLeaf{x}:
      {==}
    case APNode{xs, ys}:
      %Equal.sym(Array<T> & U32, Array.size(T, AP.build(T, xs)), (AP.build(T, xs), AP.size(T, xs)), AP.size_eq(T, xs)) : {Array.size.node(T, AP.build(T, ys), _) == (ANode{AP.build(T, xs), AP.build(T, ys)}, U32.shl(AP.size(T, xs))) : Array<T> & U32}
      {==}

def AP.swap_eq(-T: Data, t: AP.Tree<T>, n: U32, +i: U32, v: T, z: Bool) -> {Array.swap.go(T, AP.build(T, t), n, i, v, z) == (AP.build(T, AP.swap_t(T, t, n, i, v, z)), AP.swap_v(T, t, n, i, v, z)) : Array<T> & T}:
  match t z:
    case APLeaf{x} _:
      {==}
    case APNode{xs, ys} True{}:
      +h = U32.shr(n)
      +z1 = U32.is_lt(i, U32.shr(h))
      %Equal.sym(Array<T> & T, Array.swap.go(T, AP.build(T, xs), h, i, v, z1), (AP.build(T, AP.swap_t(T, xs, h, i, v, z1)), AP.swap_v(T, xs, h, i, v, z1)), AP.swap_eq(T, xs, h, i, v, z1)) : {Array.swap.lo(T, AP.build(T, ys), _) == (ANode{AP.build(T, AP.swap_t(T, xs, h, i, v, z1)), AP.build(T, ys)}, AP.swap_v(T, xs, h, i, v, z1)) : Array<T> & T}
      {==}
    case APNode{xs, ys} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      +z1 = U32.is_lt(j, U32.shr(h))
      %Equal.sym(Array<T> & T, Array.swap.go(T, AP.build(T, ys), h, j, v, z1), (AP.build(T, AP.swap_t(T, ys, h, j, v, z1)), AP.swap_v(T, ys, h, j, v, z1)), AP.swap_eq(T, ys, h, j, v, z1)) : {Array.swap.hi(T, AP.build(T, xs), _) == (ANode{AP.build(T, xs), AP.build(T, AP.swap_t(T, ys, h, j, v, z1))}, AP.swap_v(T, ys, h, j, v, z1)) : Array<T> & T}
      {==}

def AP.get_eq(-T: Data, t: AP.Tree<T>, n: U32, +i: U32, z: Bool) -> {Array.get.go(T, AP.build(T, t), n, i, z) == (AP.build(T, t), AP.get_v(T, t, n, i, z)) : Array<T> & T}:
  match t z:
    case APLeaf{x} _:
      {==}
    case APNode{xs, ys} True{}:
      +h = U32.shr(n)
      +z1 = U32.is_lt(i, U32.shr(h))
      %Equal.sym(Array<T> & T, Array.get.go(T, AP.build(T, xs), h, i, z1), (AP.build(T, xs), AP.get_v(T, xs, h, i, z1)), AP.get_eq(T, xs, h, i, z1)) : {Array.swap.lo(T, AP.build(T, ys), _) == (ANode{AP.build(T, xs), AP.build(T, ys)}, AP.get_v(T, xs, h, i, z1)) : Array<T> & T}
      {==}
    case APNode{xs, ys} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      +z1 = U32.is_lt(j, U32.shr(h))
      %Equal.sym(Array<T> & T, Array.get.go(T, AP.build(T, ys), h, j, z1), (AP.build(T, ys), AP.get_v(T, ys, h, j, z1)), AP.get_eq(T, ys, h, j, z1)) : {Array.swap.hi(T, AP.build(T, xs), _) == (ANode{AP.build(T, xs), AP.build(T, ys)}, AP.get_v(T, ys, h, j, z1)) : Array<T> & T}
      {==}

def AP.get_top_eq(-T: Data, +t: AP.Tree<T>, +i: U32) -> {Array.get(T, AP.build(T, t), i) == (AP.build(T, t), AP.get_top(T, t, i)) : Array<T> & T}:
  +n = AP.size(T, t)
  +j = AP.mask(n, i)
  %Equal.sym(Array<T> & U32, Array.size(T, AP.build(T, t)), (AP.build(T, t), n), AP.size_eq(T, t)) : {Array.get.at(T, i, _) == (AP.build(T, t), AP.get_top(T, t, i)) : Array<T> & T}
  %Equal.sym(Array<T> & T, Array.get.go(T, AP.build(T, t), n, j, AP.z(n, j)), (AP.build(T, t), AP.get_v(T, t, n, j, AP.z(n, j))), AP.get_eq(T, t, n, j, AP.z(n, j))) : {_ == (AP.build(T, t), AP.get_top(T, t, i)) : Array<T> & T}
  {==}

def AP.set_top_eq(-T: Data, +t: AP.Tree<T>, +i: U32, +v: T) -> {Array.set(T, AP.build(T, t), i, v) == AP.build(T, AP.set_top(T, t, i, v)) : Array<T>}:
  +n = AP.size(T, t)
  +j = AP.mask(n, i)
  %Equal.sym(Array<T> & U32, Array.size(T, AP.build(T, t)), (AP.build(T, t), n), AP.size_eq(T, t)) : {Array.set.fin(T, Array.swap.at(T, i, v, _)) == AP.build(T, AP.set_top(T, t, i, v)) : Array<T>}
  %Equal.sym(Array<T> & T, Array.swap.go(T, AP.build(T, t), n, j, v, AP.z(n, j)), (AP.build(T, AP.swap_t(T, t, n, j, v, AP.z(n, j))), AP.swap_v(T, t, n, j, v, AP.z(n, j))), AP.swap_eq(T, t, n, j, v, AP.z(n, j))) : {Array.set.fin(T, _) == AP.build(T, AP.set_top(T, t, i, v)) : Array<T>}
  {==}

# Shape: a write replaces one leaf and keeps the shape

def AP.swap_size(-T: Data, t: AP.Tree<T>, n: U32, +i: U32, v: T, z: Bool) -> {AP.size(T, AP.swap_t(T, t, n, i, v, z)) == AP.size(T, t) : U32}:
  match t z:
    case APLeaf{x} _:
      {==}
    case APNode{xs, ys} True{}:
      +h = U32.shr(n)
      +z1 = U32.is_lt(i, U32.shr(h))
      %Equal.sym(U32, AP.size(T, AP.swap_t(T, xs, h, i, v, z1)), AP.size(T, xs), AP.swap_size(T, xs, h, i, v, z1)) : {U32.shl(_) == U32.shl(AP.size(T, xs)) : U32}
      {==}
    case APNode{xs, ys} False{}:
      {==}

def AP.get_swap_same(-T: Data, t: AP.Tree<T>, n: U32, +i: U32, +v: T, z: Bool) -> {AP.get_v(T, AP.swap_t(T, t, n, i, v, z), n, i, z) == v : T}:
  match t z:
    case APLeaf{x} _:
      {==}
    case APNode{xs, ys} True{}:
      +h = U32.shr(n)
      AP.get_swap_same(T, xs, h, i, v, U32.is_lt(i, U32.shr(h)))
    case APNode{xs, ys} False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      AP.get_swap_same(T, ys, h, j, v, U32.is_lt(j, U32.shr(h)))

def AP.perf_swap(-T: Data, t: AP.Tree<T>, n: U32, +i: U32, v: T, z: Bool, +d: Nat) -> {A.Arrays.is_perfect(T, d, AP.build(T, AP.swap_t(T, t, n, i, v, z))) == A.Arrays.is_perfect(T, d, AP.build(T, t)) : Bool}:
  match t z:
    case APLeaf{x} _:
      match d:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case APNode{xs, ys} True{}:
      match d:
        case 0n:
          {==}
        case 1n+p:
          +h = U32.shr(n)
          +z1 = U32.is_lt(i, U32.shr(h))
          %Equal.sym(Bool, A.Arrays.is_perfect(T, p, AP.build(T, AP.swap_t(T, xs, h, i, v, z1))), A.Arrays.is_perfect(T, p, AP.build(T, xs)), AP.perf_swap(T, xs, h, i, v, z1, p)) : {Bool.and(_, A.Arrays.is_perfect(T, p, AP.build(T, ys))) == Bool.and(A.Arrays.is_perfect(T, p, AP.build(T, xs)), A.Arrays.is_perfect(T, p, AP.build(T, ys))) : Bool}
          {==}
    case APNode{xs, ys} False{}:
      match d:
        case 0n:
          {==}
        case 1n+p:
          +h = U32.shr(n)
          +j = U32.sub(i, h)
          +z1 = U32.is_lt(j, U32.shr(h))
          %Equal.sym(Bool, A.Arrays.is_perfect(T, p, AP.build(T, AP.swap_t(T, ys, h, j, v, z1))), A.Arrays.is_perfect(T, p, AP.build(T, ys)), AP.perf_swap(T, ys, h, j, v, z1, p)) : {Bool.and(A.Arrays.is_perfect(T, p, AP.build(T, xs)), _) == Bool.and(A.Arrays.is_perfect(T, p, AP.build(T, xs)), A.Arrays.is_perfect(T, p, AP.build(T, ys))) : Bool}
          {==}

def AP.size_perf(-T: Data, +d: Nat, +t: AP.Tree<T>, h: {A.Arrays.is_perfect(T, d, AP.build(T, t)) == True{} : Bool}) -> {AP.size(T, t) == U32.shln(1, d) : U32}:
  match d t:
    case 0n APLeaf{x}:
      {==}
    case 0n APNode{xs, ys}:
      Empty.absurd({AP.size(T, APNode{xs, ys}) == U32.shln(1, 0n) : U32}, AP.ft(h))
    case 1n+p APLeaf{x}:
      Empty.absurd({AP.size(T, APLeaf{x}) == U32.shln(1, 1n+p) : U32}, AP.ft(h))
    case 1n+p APNode{xs, ys}:
      +hx = AP.and_l(A.Arrays.is_perfect(T, p, AP.build(T, xs)), A.Arrays.is_perfect(T, p, AP.build(T, ys)), h)
      %Equal.sym(U32, AP.size(T, xs), U32.shln(1, p), AP.size_perf(T, p, xs, hx)) : {U32.shl(_) == U32.shl(U32.shln(1, p)) : U32}
      {==}

def AP.new_perf(-T: Data, +d: Nat, +v: T) -> {A.Arrays.is_perfect(T, d, Array.new(T, d, v)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Bool, A.Arrays.is_perfect(T, p, Array.new(T, p, v)), True{}, AP.new_perf(T, p, v)) : {Bool.and(_, _) == True{} : Bool}
      {==}

# Reflected forms of the laws for every array

def AP.get_same_array.go(-T: Data, -a: Array<T>, +i: U32, r: &t: AP.Tree<T> -> {AP.build(T, t) == a : Array<T>}) -> {Pair.fst(Array<T>, T, Array.get(T, a, i)) == a : Array<T>}:
  (t, e) = r
  %e : {Pair.fst(Array<T>, T, Array.get(T, _, i)) == _ : Array<T>}
  %Equal.sym(Array<T> & T, Array.get(T, AP.build(T, t), i), (AP.build(T, t), AP.get_top(T, t, i)), AP.get_top_eq(T, t, i)) : {Pair.fst(Array<T>, T, _) == AP.build(T, t) : Array<T>}
  {==}

def AP.get_set_same.go(-T: Data, -a: Array<T>, +i: U32, +v: T, r: &t: AP.Tree<T> -> {AP.build(T, t) == a : Array<T>}) -> {Pair.snd(Array<T>, T, Array.get(T, Array.set(T, a, i, v), i)) == v : T}:
  (+t, e) = r
  +n = AP.size(T, t)
  +j = AP.mask(n, i)
  +t2 = AP.set_top(T, t, i, v)
  %e : {Pair.snd(Array<T>, T, Array.get(T, Array.set(T, _, i, v), i)) == v : T}
  %Equal.sym(Array<T>, Array.set(T, AP.build(T, t), i, v), AP.build(T, t2), AP.set_top_eq(T, t, i, v)) : {Pair.snd(Array<T>, T, Array.get(T, _, i)) == v : T}
  %Equal.sym(Array<T> & T, Array.get(T, AP.build(T, t2), i), (AP.build(T, t2), AP.get_top(T, t2, i)), AP.get_top_eq(T, t2, i)) : {Pair.snd(Array<T>, T, _) == v : T}
  %Equal.sym(U32, AP.size(T, t2), n, AP.swap_size(T, t, n, j, v, AP.z(n, j))) : {AP.get_v(T, t2, _, AP.mask(_, i), AP.z(_, AP.mask(_, i))) == v : T}
  AP.get_swap_same(T, t, n, j, v, AP.z(n, j))

# More Nat order facts

def AP.lt_zero(x: Nat) -> {Nat.is_lt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def AP.lt_succ_l(x: Nat, y: Nat, h: {Nat.is_lt(1n+x, y) == True{} : Bool}) -> {Nat.is_lt(x, y) == True{} : Bool}:
  match x y:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, AP.ft(h))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, AP.ft(h))
    case 1n+p 1n+q:
      AP.lt_succ_l(p, q, h)

def AP.lt_le(x: Nat, y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_le(x, y) == True{} : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, AP.ft(h))
    case 1n+p 1n+q:
      AP.lt_le(p, q, h)

def AP.lt_le_trans(a: Nat, b: Nat, k: Nat, h1: {Nat.is_lt(k, a) == True{} : Bool}, h2: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(k, b) == True{} : Bool}:
  match a b:
    case 0n _:
      Empty.absurd({Nat.is_lt(k, b) == True{} : Bool}, AP.ft(Equal.trans(Bool, False{}, Nat.is_lt(k, 0n), True{}, Equal.sym(Bool, Nat.is_lt(k, 0n), False{}, AP.lt_zero(k)), h1)))
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(k, 0n) == True{} : Bool}, AP.ft(h2))
    case 1n+p 1n+q:
      match k:
        case 0n:
          {==}
        case 1n+r:
          AP.lt_le_trans(p, q, r, h1, h2)

def AP.double_le(+x: Nat, +y: Nat, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.double(x), Nat.double(y)) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(AP.bv(False{}, x), AP.bv(False{}, y)), Word.cmp.fin(False{}, False{}, Nat.cmp(x, y)), AP.nc(x, y, False{}, False{})) : {Cmp.is_le(_) == True{} : Bool}
  %Equal.sym(Bool, Cmp.is_le(Word.cmp.fin(False{}, False{}, Nat.cmp(x, y))), Cmp.is_le(Nat.cmp(x, y)), AP.fin_le_ff(Nat.cmp(x, y))) : {_ == True{} : Bool}
  h

def AP.dpos(x: Nat, e: {Nat.is_lt(0n, x) == True{} : Bool}) -> {Nat.is_le(1n, Nat.double(x)) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, AP.ft(e))
    case 1n+y:
      {==}

def AP.slots_pos(d: Nat) -> {Nat.is_lt(0n, A.Arrays.slots(d)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+ +p:
      AP.lt_le_trans(1n, Nat.double(A.Arrays.slots(p)), 0n, {==}, AP.dpos(A.Arrays.slots(p), AP.slots_pos(p)))

def AP.slots_le(d: Nat, n: Nat, h: {Nat.is_le(d, n) == True{} : Bool}) -> {Nat.is_le(A.Arrays.slots(d), A.Arrays.slots(n)) == True{} : Bool}:
  match d n:
    case 0n 0n:
      {==}
    case 0n 1n+ +q:
      AP.dpos(A.Arrays.slots(q), AP.slots_pos(q))
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(A.Arrays.slots(1n+p), A.Arrays.slots(0n)) == True{} : Bool}, AP.ft(h))
    case 1n+ +p 1n+ +q:
      AP.double_le(A.Arrays.slots(p), A.Arrays.slots(q), AP.slots_le(p, q, h))

# a value below double(s), split at s
def AP.lt_split(+w: Nat, +s: Nat, h: {Nat.is_lt(Nat.add(w, s), Nat.double(s)) == True{} : Bool}) -> {Nat.is_lt(w, s) == True{} : Bool}:
  %AP.lt_cancel(s, w, s) : {_ == True{} : Bool}
  %AP.add_comm(w, s) : {Nat.is_lt(_, Nat.add(s, s)) == True{} : Bool}
  %AP.double_self(s) : {Nat.is_lt(Nat.add(w, s), _) == True{} : Bool}
  h

# Lists

def AP.con_cong(-T: Data, -h: T, -x: List<&2, T>, -y: List<&2, T>, e: {x == y : List<&2, T>}) -> {Con{h, x} == Con{h, y} : List<&2, T>}:
  %e : {Con{h, x} == Con{h, _} : List<&2, T>}
  {==}

def AP.len_app(-T: Data, xs: List<&2, T>, -ys: List<&2, T>) -> {List.length(&2, T, List.append(&2, T, xs, ys)) == Nat.add(List.length(&2, T, xs), List.length(&2, T, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      AP.succ_cong(List.length(&2, T, List.append(&2, T, t, ys)), Nat.add(List.length(&2, T, t), List.length(&2, T, ys)), AP.len_app(T, t, ys))

def AP.get_app_l(-T: Data, xs: List<&2, T>, -ys: List<&2, T>, k: Nat, h: {Nat.is_lt(k, List.length(&2, T, xs)) == True{} : Bool}) -> {List.get(&2, T, List.append(&2, T, xs, ys), k) == List.get(&2, T, xs, k) : Maybe<&2, T>}:
  match xs k:
    case Nil{} _:
      Empty.absurd({List.get(&2, T, List.append(&2, T, Nil{}, ys), k) == List.get(&2, T, Nil{}, k) : Maybe<&2, T>}, AP.ft(Equal.trans(Bool, False{}, Nat.is_lt(k, 0n), True{}, Equal.sym(Bool, Nat.is_lt(k, 0n), False{}, AP.lt_zero(k)), h)))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      AP.get_app_l(T, t, ys, p, h)

def AP.get_app_r(-T: Data, xs: List<&2, T>, -ys: List<&2, T>, -k: Nat) -> {List.get(&2, T, List.append(&2, T, xs, ys), Nat.add(List.length(&2, T, xs), k)) == List.get(&2, T, ys, k) : Maybe<&2, T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      AP.get_app_r(T, t, ys, k)

def AP.set_app_l(-T: Data, xs: List<&2, T>, -ys: List<&2, T>, k: Nat, -v: T, h: {Nat.is_lt(k, List.length(&2, T, xs)) == True{} : Bool}) -> {List.set(&2, T, List.append(&2, T, xs, ys), k, v) == List.append(&2, T, List.set(&2, T, xs, k, v), ys) : List<&2, T>}:
  match xs k:
    case Nil{} _:
      Empty.absurd({List.set(&2, T, List.append(&2, T, Nil{}, ys), k, v) == List.append(&2, T, List.set(&2, T, Nil{}, k, v), ys) : List<&2, T>}, AP.ft(Equal.trans(Bool, False{}, Nat.is_lt(k, 0n), True{}, Equal.sym(Bool, Nat.is_lt(k, 0n), False{}, AP.lt_zero(k)), h)))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      AP.con_cong(T, x, List.set(&2, T, List.append(&2, T, t, ys), p, v), List.append(&2, T, List.set(&2, T, t, p, v), ys), AP.set_app_l(T, t, ys, p, v, h))

def AP.set_app_r(-T: Data, xs: List<&2, T>, -ys: List<&2, T>, -k: Nat, -v: T) -> {List.set(&2, T, List.append(&2, T, xs, ys), Nat.add(List.length(&2, T, xs), k), v) == List.append(&2, T, xs, List.set(&2, T, ys, k, v)) : List<&2, T>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      AP.con_cong(T, x, List.set(&2, T, List.append(&2, T, t, ys), Nat.add(List.length(&2, T, t), k), v), List.append(&2, T, t, List.set(&2, T, ys, k, v)), AP.set_app_r(T, t, ys, k, v))

def AP.get_set_other(-T: Data, xs: List<&2, T>, k1: Nat, k2: Nat, -v: T, h: {Nat.is_eq(k1, k2) == False{} : Bool}) -> {List.get(&2, T, List.set(&2, T, xs, k1, v), k2) == List.get(&2, T, xs, k2) : Maybe<&2, T>}:
  match xs k1 k2:
    case Nil{} _ _:
      {==}
    case Con{x, t} 0n 0n:
      Empty.absurd({List.get(&2, T, List.set(&2, T, Con{x, t}, 0n, v), 0n) == List.get(&2, T, Con{x, t}, 0n) : Maybe<&2, T>}, AP.tf(h))
    case Con{x, t} 0n 1n+q:
      {==}
    case Con{x, t} 1n+p 0n:
      {==}
    case Con{x, t} 1n+p 1n+q:
      AP.get_set_other(T, t, p, q, v, h)

# Masks and words below 2^d

def AP.and_zero(n: Nat, w: Word(n)) -> {Word.and(n, w, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+ +q:
      match w:
        case WCon{False{}, t}:
          AP.wcon_cong(q, False{}, Word.and(q, t, Word.zero(q)), Word.zero(q), AP.and_zero(q, t))
        case WCon{True{}, t}:
          AP.wcon_cong(q, False{}, Word.and(q, t, Word.zero(q)), Word.zero(q), AP.and_zero(q, t))

def AP.val0(n: Nat, w: Word(n), e: {Word.to_nat(n, w) == 0n : Nat}) -> {w == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+ +q:
      match w:
        case WCon{False{}, +t}:
          AP.wcon_cong(q, False{}, t, Word.zero(q), AP.val0(q, t, AP.double_zero(Word.to_nat(q, t), e)))
        case WCon{True{}, +t}:
          Empty.absurd({WCon{True{}, t} == Word.zero(1n+q) : Word(1n+q)}, AP.sz(Nat.double(Word.to_nat(q, t)), e))

def AP.lt_bv_inv(+b: Bool, +x: Nat, +s: Nat, h: {Nat.is_lt(AP.bv(b, x), AP.bv(False{}, s)) == True{} : Bool}) -> {Nat.is_lt(x, s) == True{} : Bool}:
  %AP.fin_lt_xf(b, Nat.cmp(x, s)) : {_ == True{} : Bool}
  AP.lt_bits(x, s, b, False{}, h)

def AP.lt_bv(+b: Bool, +x: Nat, +s: Nat, h: {Nat.is_lt(x, s) == True{} : Bool}) -> {Nat.is_lt(AP.bv(b, x), AP.bv(False{}, s)) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(AP.bv(b, x), AP.bv(False{}, s)), Word.cmp.fin(b, False{}, Nat.cmp(x, s)), AP.nc(x, s, b, False{})) : {Cmp.is_lt(_) == True{} : Bool}
  %Equal.sym(Bool, Cmp.is_lt(Word.cmp.fin(b, False{}, Nat.cmp(x, s))), Cmp.is_lt(Nat.cmp(x, s)), AP.fin_lt_xf(b, Nat.cmp(x, s))) : {_ == True{} : Bool}
  h

# a word masked to its low d bits is below 2^d
def AP.mask_lt(n: Nat, w: Word(n), +d: Nat) -> {Nat.is_lt(Word.to_nat(n, Word.and(n, w, AP.lm(n, d))), A.Arrays.slots(d)) == True{} : Bool}:
  match n:
    case 0n:
      AP.slots_pos(d)
    case 1n+ +q:
      match w d:
        case WCon{False{}, +t} 0n:
          %Equal.sym(Word(q), Word.and(q, t, Word.zero(q)), Word.zero(q), AP.and_zero(q, t)) : {Nat.is_lt(Nat.double(Word.to_nat(q, _)), 1n) == True{} : Bool}
          %Equal.sym(Nat, Word.to_nat(q, Word.zero(q)), 0n, AP.val_zero(q)) : {Nat.is_lt(Nat.double(_), 1n) == True{} : Bool}
          {==}
        case WCon{True{}, +t} 0n:
          %Equal.sym(Word(q), Word.and(q, t, Word.zero(q)), Word.zero(q), AP.and_zero(q, t)) : {Nat.is_lt(Nat.double(Word.to_nat(q, _)), 1n) == True{} : Bool}
          %Equal.sym(Nat, Word.to_nat(q, Word.zero(q)), 0n, AP.val_zero(q)) : {Nat.is_lt(Nat.double(_), 1n) == True{} : Bool}
          {==}
        case WCon{False{}, +t} 1n+ +e:
          AP.lt_bv(False{}, Word.to_nat(q, Word.and(q, t, AP.lm(q, e))), A.Arrays.slots(e), AP.mask_lt(q, t, e))
        case WCon{True{}, +t} 1n+ +e:
          AP.lt_bv(True{}, Word.to_nat(q, Word.and(q, t, AP.lm(q, e))), A.Arrays.slots(e), AP.mask_lt(q, t, e))

# a word below 2^d is unchanged by the mask
def AP.and_id(n: Nat, w: Word(n), +d: Nat, h: {Nat.is_lt(Word.to_nat(n, w), A.Arrays.slots(d)) == True{} : Bool}) -> {Word.and(n, w, AP.lm(n, d)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+ +q:
      match w d:
        case WCon{False{}, +t} 0n:
          +z = AP.val0(q, t, AP.double_zero(Word.to_nat(q, t), AP.lt_one(Nat.double(Word.to_nat(q, t)), h)))
          AP.wcon_cong(q, False{}, Word.and(q, t, Word.zero(q)), t, Equal.trans(Word(q), Word.and(q, t, Word.zero(q)), Word.zero(q), t, AP.and_zero(q, t), Equal.sym(Word(q), t, Word.zero(q), z)))
        case WCon{True{}, +t} 0n:
          Empty.absurd({Word.and(1n+q, WCon{True{}, t}, AP.lm(1n+q, 0n)) == WCon{True{}, t} : Word(1n+q)}, AP.tf(Equal.trans(Bool, True{}, Nat.is_lt(Nat.double(Word.to_nat(q, t)), 0n), False{}, Equal.sym(Bool, Nat.is_lt(Nat.double(Word.to_nat(q, t)), 0n), True{}, h), AP.lt_zero(Nat.double(Word.to_nat(q, t))))))
        case WCon{False{}, +t} 1n+ +e:
          AP.wcon_cong(q, False{}, Word.and(q, t, AP.lm(q, e)), t, AP.and_id(q, t, e, AP.lt_bv_inv(False{}, Word.to_nat(q, t), A.Arrays.slots(e), h)))
        case WCon{True{}, +t} 1n+ +e:
          AP.wcon_cong(q, True{}, Word.and(q, t, AP.lm(q, e)), t, AP.and_id(q, t, e, AP.lt_bv_inv(True{}, Word.to_nat(q, t), A.Arrays.slots(e), h)))

def AP.u32_mask_lt(a: U32, +d: Nat) -> {Nat.is_lt(U32.to_nat(U32.and(a, U32{AP.lm(32n, d)})), A.Arrays.slots(d)) == True{} : Bool}:
  match a:
    case U32{w}:
      AP.mask_lt(32n, w, d)

def AP.u32_and_id(+a: U32, +d: Nat, h: {Nat.is_lt(U32.to_nat(a), A.Arrays.slots(d)) == True{} : Bool}) -> {U32.and(a, U32{AP.lm(32n, d)}) == a : U32}:
  match a:
    case U32{+w}:
      AP.u32_cong(Word.and(32n, w, AP.lm(32n, d)), w, AP.and_id(32n, w, d, h))

# from_nat and to_nat are inverse below 2^32

def AP.inc(n: Nat, w: Word(n), d: Nat, h: {Nat.is_lt(1n+Word.to_nat(n, w), A.Arrays.slots(d)) == True{} : Bool}, hd: {Nat.is_le(d, n) == True{} : Bool}) -> {Word.to_nat(n, Word.inc(n, w)) == 1n+Word.to_nat(n, w) : Nat}:
  match n:
    case 0n:
      match w d:
        case WNil{} 0n:
          Empty.absurd({0n == 1n : Nat}, AP.ft(h))
        case WNil{} 1n+e:
          Empty.absurd({0n == 1n : Nat}, AP.ft(hd))
    case 1n+ +q:
      match w d:
        case WCon{False{}, t} _:
          {==}
        case WCon{True{}, +t} 0n:
          Empty.absurd({Word.to_nat(1n+q, Word.inc(1n+q, WCon{True{}, t})) == 1n+Word.to_nat(1n+q, WCon{True{}, t}) : Nat}, AP.ft(h))
        case WCon{True{}, +t} 1n+ +e:
          +x = Word.to_nat(q, t)
          %Equal.sym(Nat, Word.to_nat(q, Word.inc(q, t)), 1n+x, AP.inc(q, t, e, AP.lt_bv_inv(False{}, 1n+x, A.Arrays.slots(e), h), hd)) : {Nat.double(_) == 2n+Nat.double(x) : Nat}
          {==}

def AP.u32_inc(a: U32, d: Nat, h: {Nat.is_lt(1n+U32.to_nat(a), A.Arrays.slots(d)) == True{} : Bool}, hd: {Nat.is_le(d, 32n) == True{} : Bool}) -> {U32.to_nat(U32.inc(a)) == 1n+U32.to_nat(a) : Nat}:
  match a:
    case U32{w}:
      AP.inc(32n, w, d, h, hd)

def AP.lt_rw(-x: Nat, -y: Nat, -s: Nat, e: {x == y : Nat}, h: {Nat.is_lt(1n+y, s) == True{} : Bool}) -> {Nat.is_lt(1n+x, s) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {Nat.is_lt(1n+_, s) == True{} : Bool}
  h

# from_nat then to_nat is the identity below 2^d, d <= 32
def AP.from_nat(k: Nat, +d: Nat, +h: {Nat.is_lt(k, A.Arrays.slots(d)) == True{} : Bool}, +hd: {Nat.is_le(d, 32n) == True{} : Bool}) -> {U32.to_nat(U32.from_nat(k)) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +ih = AP.from_nat(p, d, AP.lt_succ_l(p, A.Arrays.slots(d), h), hd)
      Equal.trans(Nat, U32.to_nat(U32.inc(U32.from_nat(p))), 1n+U32.to_nat(U32.from_nat(p)), 1n+p, AP.u32_inc(U32.from_nat(p), d, AP.lt_rw(U32.to_nat(U32.from_nat(p)), p, A.Arrays.slots(d), ih, h), hd), AP.succ_cong(U32.to_nat(U32.from_nat(p)), p, ih))

# Reading and writing a perfect tree: the slot is the index's value

def AP.app_cong_l(-T: Data, -x: List<&2, T>, -y: List<&2, T>, -ys: List<&2, T>, e: {x == y : List<&2, T>}) -> {List.append(&2, T, x, ys) == List.append(&2, T, y, ys) : List<&2, T>}:
  %e : {List.append(&2, T, x, ys) == List.append(&2, T, _, ys) : List<&2, T>}
  {==}

def AP.app_cong_r(-T: Data, -xs: List<&2, T>, -x: List<&2, T>, -y: List<&2, T>, e: {x == y : List<&2, T>}) -> {List.append(&2, T, xs, x) == List.append(&2, T, xs, y) : List<&2, T>}:
  %e : {List.append(&2, T, xs, x) == List.append(&2, T, xs, _) : List<&2, T>}
  {==}

def AP.lt_rw_r(-k: Nat, -x: Nat, -y: Nat, e: {x == y : Nat}, h: {Nat.is_lt(k, y) == True{} : Bool}) -> {Nat.is_lt(k, x) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {Nat.is_lt(k, _) == True{} : Bool}
  h

def AP.lt_rw_l(-x: Nat, -y: Nat, -m: Nat, e: {x == y : Nat}, h: {Nat.is_lt(y, m) == True{} : Bool}) -> {Nat.is_lt(x, m) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {Nat.is_lt(_, m) == True{} : Bool}
  h

def AP.lt_split2(+w: Nat, +s: Nat, h: {Nat.is_lt(Nat.add(s, w), Nat.double(s)) == True{} : Bool}) -> {Nat.is_lt(w, s) == True{} : Bool}:
  %AP.lt_cancel(s, w, s) : {_ == True{} : Bool}
  %AP.double_self(s) : {Nat.is_lt(Nat.add(s, w), _) == True{} : Bool}
  h

def AP.eb_fix(+i: U32, +p: Nat, +b: Bool, hd: {Nat.is_lt(1n+p, 32n) == True{} : Bool}, eb: {U32.is_lt(i, U32.shr(U32.shln(1, 1n+p))) == b : Bool}) -> {U32.is_lt(i, U32.shln(1, p)) == b : Bool}:
  %AP.shr_shln(p, hd) : {U32.is_lt(i, _) == b : Bool}
  eb

def AP.lt_true(+i: U32, +p: Nat, hd: {Nat.is_lt(p, 32n) == True{} : Bool}, e: {U32.is_lt(i, U32.shln(1, p)) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(i), A.Arrays.slots(p)) == True{} : Bool}:
  %AP.val_shln(p, hd) : {Nat.is_lt(U32.to_nat(i), _) == True{} : Bool}
  %AP.u32_lt(i, U32.shln(1, p)) : {_ == True{} : Bool}
  e

def AP.lt_false(+i: U32, +p: Nat, hd: {Nat.is_lt(p, 32n) == True{} : Bool}, e: {U32.is_lt(i, U32.shln(1, p)) == False{} : Bool}) -> {Nat.is_lt(U32.to_nat(i), A.Arrays.slots(p)) == False{} : Bool}:
  %AP.val_shln(p, hd) : {Nat.is_lt(U32.to_nat(i), _) == False{} : Bool}
  %AP.u32_lt(i, U32.shln(1, p)) : {_ == False{} : Bool}
  e

def AP.u32_sub_add(a: U32, b: U32, h: {Nat.is_le(U32.to_nat(b), U32.to_nat(a)) == True{} : Bool}) -> {U32.to_nat(a) == Nat.add(U32.to_nat(U32.sub(a, b)), U32.to_nat(b)) : Nat}:
  match a b:
    case U32{x} U32{y}:
      AP.adc(32n, x, y, True{}, h)

def AP.le_rw_l(-x: Nat, -y: Nat, -m: Nat, e: {x == y : Nat}, h: {Nat.is_le(y, m) == True{} : Bool}) -> {Nat.is_le(x, m) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {Nat.is_le(_, m) == True{} : Bool}
  h

# an index at or above 2^p, split into 2^p and the rest
def AP.split(+i: U32, +p: Nat, +hd: {Nat.is_lt(p, 32n) == True{} : Bool}, e: {U32.is_lt(i, U32.shln(1, p)) == False{} : Bool}) -> {Nat.add(A.Arrays.slots(p), U32.to_nat(U32.sub(i, U32.shln(1, p)))) == U32.to_nat(i) : Nat}:
  +s = A.Arrays.slots(p)
  +w = U32.to_nat(U32.sub(i, U32.shln(1, p)))
  +le = AP.le_rw_l(U32.to_nat(U32.shln(1, p)), s, U32.to_nat(i), AP.val_shln(p, hd), AP.not_lt_le(U32.to_nat(i), s, AP.lt_false(i, p, hd, e)))
  %Equal.sym(Nat, U32.to_nat(i), Nat.add(w, U32.to_nat(U32.shln(1, p))), AP.u32_sub_add(i, U32.shln(1, p), le)) : {Nat.add(s, w) == _ : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.shln(1, p)), s, AP.val_shln(p, hd)) : {Nat.add(s, w) == Nat.add(w, _) : Nat}
  AP.add_comm(s, w)

def AP.len_perf(-T: Data, +d: Nat, +t: AP.Tree<T>, +hp: {A.Arrays.is_perfect(T, d, AP.build(T, t)) == True{} : Bool}) -> {List.length(&2, T, A.Arrays.leaves(T, AP.build(T, t))) == A.Arrays.slots(d) : Nat}:
  match d t:
    case 0n APLeaf{x}:
      {==}
    case 0n APNode{xs, ys}:
      Empty.absurd({List.length(&2, T, A.Arrays.leaves(T, AP.build(T, APNode{xs, ys}))) == A.Arrays.slots(0n) : Nat}, AP.ft(hp))
    case 1n+p APLeaf{x}:
      Empty.absurd({List.length(&2, T, A.Arrays.leaves(T, AP.build(T, APLeaf{x}))) == A.Arrays.slots(1n+p) : Nat}, AP.ft(hp))
    case 1n+ +p APNode{xs, ys}:
      +lx = A.Arrays.leaves(T, AP.build(T, xs))
      +ly = A.Arrays.leaves(T, AP.build(T, ys))
      +s = A.Arrays.slots(p)
      +hpx = AP.and_l(A.Arrays.is_perfect(T, p, AP.build(T, xs)), A.Arrays.is_perfect(T, p, AP.build(T, ys)), hp)
      +hpy = AP.and_r(A.Arrays.is_perfect(T, p, AP.build(T, xs)), A.Arrays.is_perfect(T, p, AP.build(T, ys)), hp)
      %Equal.sym(Nat, List.length(&2, T, List.append(&2, T, lx, ly)), Nat.add(List.length(&2, T, lx), List.length(&2, T, ly)), AP.len_app(T, lx, ly)) : {_ == Nat.double(s) : Nat}
      %Equal.sym(Nat, List.length(&2, T, lx), s, AP.len_perf(T, p, xs, hpx)) : {Nat.add(_, List.length(&2, T, ly)) == Nat.double(s) : Nat}
      %Equal.sym(Nat, List.length(&2, T, ly), s, AP.len_perf(T, p, ys, hpy)) : {Nat.add(s, _) == Nat.double(s) : Nat}
      Equal.sym(Nat, Nat.double(s), Nat.add(s, s), AP.double_self(s))

def AP.get_leaves(-T: Data, +d: Nat, +t: AP.Tree<T>, +i: U32, b: Bool, +eb: {U32.is_lt(i, U32.shr(U32.shln(1, d))) == b : Bool}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hp: {A.Arrays.is_perfect(T, d, AP.build(T, t)) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), A.Arrays.slots(d)) == True{} : Bool}) -> {List.get(&2, T, A.Arrays.leaves(T, AP.build(T, t)), U32.to_nat(i)) == Some{AP.get_v(T, t, U32.shln(1, d), i, b)} : Maybe<&2, T>}:
  match d t b:
    case 0n APLeaf{+x} _:
      %Equal.sym(Nat, U32.to_nat(i), 0n, AP.lt_one(U32.to_nat(i), hi)) : {List.get(&2, T, Con{x, Nil{}}, _) == Some{x} : Maybe<&2, T>}
      {==}
    case 0n APNode{xs, ys} _:
      Empty.absurd({List.get(&2, T, A.Arrays.leaves(T, AP.build(T, APNode{xs, ys})), U32.to_nat(i)) == Some{AP.get_v(T, APNode{xs, ys}, U32.shln(1, 0n), i, b)} : Maybe<&2, T>}, AP.ft(hp))
    case 1n+p APLeaf{x} _:
      Empty.absurd({List.get(&2, T, A.Arrays.leaves(T, AP.build(T, APLeaf{x})), U32.to_nat(i)) == Some{AP.get_v(T, APLeaf{x}, U32.shln(1, 1n+p), i, b)} : Maybe<&2, T>}, AP.ft(hp))
    case 1n+ +p APNode{xs, ys} True{}:
      +hd1 = AP.lt_succ_l(p, 32n, hd)
      +s = A.Arrays.slots(p)
      +sh = U32.shln(1, p)
      +lx = A.Arrays.leaves(T, AP.build(T, xs))
      +ly = A.Arrays.leaves(T, AP.build(T, ys))
      +v = U32.to_nat(i)
      +hpx = AP.and_l(A.Arrays.is_perfect(T, p, AP.build(T, xs)), A.Arrays.is_perfect(T, p, AP.build(T, ys)), hp)
      +hi1 = AP.lt_true(i, p, hd1, AP.eb_fix(i, p, True{}, hd, eb))
      +hl = AP.lt_rw_r(v, List.length(&2, T, lx), s, AP.len_perf(T, p, xs, hpx), hi1)
      %Equal.sym(U32, U32.shr(U32.shln(1, 1n+p)), sh, AP.shr_shln(p, hd)) : {List.get(&2, T, List.append(&2, T, lx, ly), v) == Some{AP.get_v(T, xs, _, i, U32.is_lt(i, U32.shr(_)))} : Maybe<&2, T>}
      Equal.trans(Maybe<&2, T>, List.get(&2, T, List.append(&2, T, lx, ly), v), List.get(&2, T, lx, v), Some{AP.get_v(T, xs, sh, i, U32.is_lt(i, U32.shr(sh)))}, AP.get_app_l(T, lx, ly, v, hl), AP.get_leaves(T, p, xs, i, U32.is_lt(i, U32.shr(sh)), {==}, hd1, hpx, hi1))
    case 1n+ +p APNode{xs, ys} False{}:
      +hd1 = AP.lt_succ_l(p, 32n, hd)
      +s = A.Arrays.slots(p)
      +sh = U32.shln(1, p)
      +lx = A.Arrays.leaves(T, AP.build(T, xs))
      +ly = A.Arrays.leaves(T, AP.build(T, ys))
      +j = U32.sub(i, sh)
      +w = U32.to_nat(j)
      +hpx = AP.and_l(A.Arrays.is_perfect(T, p, AP.build(T, xs)), A.Arrays.is_perfect(T, p, AP.build(T, ys)), hp)
      +hpy = AP.and_r(A.Arrays.is_perfect(T, p, AP.build(T, xs)), A.Arrays.is_perfect(T, p, AP.build(T, ys)), hp)
      +hs = AP.split(i, p, hd1, AP.eb_fix(i, p, False{}, hd, eb))
      +hj = AP.lt_split2(w, s, AP.lt_rw_l(Nat.add(s, w), U32.to_nat(i), Nat.double(s), hs, hi))
      %Equal.sym(U32, U32.shr(U32.shln(1, 1n+p)), sh, AP.shr_shln(p, hd)) : {List.get(&2, T, List.append(&2, T, lx, ly), U32.to_nat(i)) == Some{AP.get_v(T, ys, _, U32.sub(i, _), U32.is_lt(U32.sub(i, _), U32.shr(_)))} : Maybe<&2, T>}
      %hs : {List.get(&2, T, List.append(&2, T, lx, ly), _) == Some{AP.get_v(T, ys, sh, j, U32.is_lt(j, U32.shr(sh)))} : Maybe<&2, T>}
      %AP.len_perf(T, p, xs, hpx) : {List.get(&2, T, List.append(&2, T, lx, ly), Nat.add(_, w)) == Some{AP.get_v(T, ys, sh, j, U32.is_lt(j, U32.shr(sh)))} : Maybe<&2, T>}
      Equal.trans(Maybe<&2, T>, List.get(&2, T, List.append(&2, T, lx, ly), Nat.add(List.length(&2, T, lx), w)), List.get(&2, T, ly, w), Some{AP.get_v(T, ys, sh, j, U32.is_lt(j, U32.shr(sh)))}, AP.get_app_r(T, lx, ly, w), AP.get_leaves(T, p, ys, j, U32.is_lt(j, U32.shr(sh)), {==}, hd1, hpy, hj))

def AP.set_leaves(-T: Data, +d: Nat, +t: AP.Tree<T>, +i: U32, +v: T, b: Bool, +eb: {U32.is_lt(i, U32.shr(U32.shln(1, d))) == b : Bool}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hp: {A.Arrays.is_perfect(T, d, AP.build(T, t)) == True{} : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), A.Arrays.slots(d)) == True{} : Bool}) -> {A.Arrays.leaves(T, AP.build(T, AP.swap_t(T, t, U32.shln(1, d), i, v, b))) == List.set(&2, T, A.Arrays.leaves(T, AP.build(T, t)), U32.to_nat(i), v) : List<&2, T>}:
  match d t b:
    case 0n APLeaf{+x} _:
      %Equal.sym(Nat, U32.to_nat(i), 0n, AP.lt_one(U32.to_nat(i), hi)) : {Con{v, Nil{}} == List.set(&2, T, Con{x, Nil{}}, _, v) : List<&2, T>}
      {==}
    case 0n APNode{xs, ys} _:
      Empty.absurd({A.Arrays.leaves(T, AP.build(T, AP.swap_t(T, APNode{xs, ys}, U32.shln(1, 0n), i, v, b))) == List.set(&2, T, A.Arrays.leaves(T, AP.build(T, APNode{xs, ys})), U32.to_nat(i), v) : List<&2, T>}, AP.ft(hp))
    case 1n+p APLeaf{x} _:
      Empty.absurd({A.Arrays.leaves(T, AP.build(T, AP.swap_t(T, APLeaf{x}, U32.shln(1, 1n+p), i, v, b))) == List.set(&2, T, A.Arrays.leaves(T, AP.build(T, APLeaf{x})), U32.to_nat(i), v) : List<&2, T>}, AP.ft(hp))
    case 1n+ +p APNode{xs, ys} True{}:
      +hd1 = AP.lt_succ_l(p, 32n, hd)
      +s = A.Arrays.slots(p)
      +sh = U32.shln(1, p)
      +lx = A.Arrays.leaves(T, AP.build(T, xs))
      +ly = A.Arrays.leaves(T, AP.build(T, ys))
      +k = U32.to_nat(i)
      +z1 = U32.is_lt(i, U32.shr(sh))
      +hpx = AP.and_l(A.Arrays.is_perfect(T, p, AP.build(T, xs)), A.Arrays.is_perfect(T, p, AP.build(T, ys)), hp)
      +hi1 = AP.lt_true(i, p, hd1, AP.eb_fix(i, p, True{}, hd, eb))
      +hl = AP.lt_rw_r(k, List.length(&2, T, lx), s, AP.len_perf(T, p, xs, hpx), hi1)
      %Equal.sym(U32, U32.shr(U32.shln(1, 1n+p)), sh, AP.shr_shln(p, hd)) : {List.append(&2, T, A.Arrays.leaves(T, AP.build(T, AP.swap_t(T, xs, _, i, v, U32.is_lt(i, U32.shr(_))))), ly) == List.set(&2, T, List.append(&2, T, lx, ly), k, v) : List<&2, T>}
      Equal.trans(List<&2, T>, List.append(&2, T, A.Arrays.leaves(T, AP.build(T, AP.swap_t(T, xs, sh, i, v, z1))), ly), List.append(&2, T, List.set(&2, T, lx, k, v), ly), List.set(&2, T, List.append(&2, T, lx, ly), k, v), AP.app_cong_l(T, A.Arrays.leaves(T, AP.build(T, AP.swap_t(T, xs, sh, i, v, z1))), List.set(&2, T, lx, k, v), ly, AP.set_leaves(T, p, xs, i, v, z1, {==}, hd1, hpx, hi1)), Equal.sym(List<&2, T>, List.set(&2, T, List.append(&2, T, lx, ly), k, v), List.append(&2, T, List.set(&2, T, lx, k, v), ly), AP.set_app_l(T, lx, ly, k, v, hl)))
    case 1n+ +p APNode{xs, ys} False{}:
      +hd1 = AP.lt_succ_l(p, 32n, hd)
      +s = A.Arrays.slots(p)
      +sh = U32.shln(1, p)
      +lx = A.Arrays.leaves(T, AP.build(T, xs))
      +ly = A.Arrays.leaves(T, AP.build(T, ys))
      +j = U32.sub(i, sh)
      +w = U32.to_nat(j)
      +z1 = U32.is_lt(j, U32.shr(sh))
      +hpx = AP.and_l(A.Arrays.is_perfect(T, p, AP.build(T, xs)), A.Arrays.is_perfect(T, p, AP.build(T, ys)), hp)
      +hpy = AP.and_r(A.Arrays.is_perfect(T, p, AP.build(T, xs)), A.Arrays.is_perfect(T, p, AP.build(T, ys)), hp)
      +hs = AP.split(i, p, hd1, AP.eb_fix(i, p, False{}, hd, eb))
      +hj = AP.lt_split2(w, s, AP.lt_rw_l(Nat.add(s, w), U32.to_nat(i), Nat.double(s), hs, hi))
      %Equal.sym(U32, U32.shr(U32.shln(1, 1n+p)), sh, AP.shr_shln(p, hd)) : {List.append(&2, T, lx, A.Arrays.leaves(T, AP.build(T, AP.swap_t(T, ys, _, U32.sub(i, _), v, U32.is_lt(U32.sub(i, _), U32.shr(_)))))) == List.set(&2, T, List.append(&2, T, lx, ly), U32.to_nat(i), v) : List<&2, T>}
      %hs : {List.append(&2, T, lx, A.Arrays.leaves(T, AP.build(T, AP.swap_t(T, ys, sh, j, v, z1)))) == List.set(&2, T, List.append(&2, T, lx, ly), _, v) : List<&2, T>}
      %AP.len_perf(T, p, xs, hpx) : {List.append(&2, T, lx, A.Arrays.leaves(T, AP.build(T, AP.swap_t(T, ys, sh, j, v, z1)))) == List.set(&2, T, List.append(&2, T, lx, ly), Nat.add(_, w), v) : List<&2, T>}
      Equal.trans(List<&2, T>, List.append(&2, T, lx, A.Arrays.leaves(T, AP.build(T, AP.swap_t(T, ys, sh, j, v, z1)))), List.append(&2, T, lx, List.set(&2, T, ly, w, v)), List.set(&2, T, List.append(&2, T, lx, ly), Nat.add(List.length(&2, T, lx), w), v), AP.app_cong_r(T, lx, A.Arrays.leaves(T, AP.build(T, AP.swap_t(T, ys, sh, j, v, z1))), List.set(&2, T, ly, w, v), AP.set_leaves(T, p, ys, j, v, z1, {==}, hd1, hpy, hj)), Equal.sym(List<&2, T>, List.set(&2, T, List.append(&2, T, lx, ly), Nat.add(List.length(&2, T, lx), w), v), List.append(&2, T, lx, List.set(&2, T, ly, w, v)), AP.set_app_r(T, lx, ly, w, v)))

# Array.new on the mirror

def AP.tnew(-T: Data, +d: Nat, +v: T) -> AP.Tree<T>:
  match d:
    case 0n:
      APLeaf{v}
    case 1n+p:
      APNode{AP.tnew(T, p, v), AP.tnew(T, p, v)}

def AP.new_eq(-T: Data, +d: Nat, +v: T) -> {Array.new(T, d, v) == AP.build(T, AP.tnew(T, d, v)) : Array<T>}:
  match d:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Array<T>, Array.new(T, p, v), AP.build(T, AP.tnew(T, p, v)), AP.new_eq(T, p, v)) : {ANode{_, _} == ANode{AP.build(T, AP.tnew(T, p, v)), AP.build(T, AP.tnew(T, p, v))} : Array<T>}
      {==}

def AP.get_v_new(-T: Data, +d: Nat, +v: T, n: U32, +i: U32, z: Bool) -> {AP.get_v(T, AP.tnew(T, d, v), n, i, z) == v : T}:
  match d z:
    case 0n _:
      {==}
    case 1n+p True{}:
      +h = U32.shr(n)
      AP.get_v_new(T, p, v, h, i, U32.is_lt(i, U32.shr(h)))
    case 1n+p False{}:
      +h = U32.shr(n)
      +j = U32.sub(i, h)
      AP.get_v_new(T, p, v, h, j, U32.is_lt(j, U32.shr(h)))

def AP.rep_add(-T: Data, a: Nat, -b: Nat, -v: T) -> {List.replicate(T, Nat.add(a, b), v) == List.append(&2, T, List.replicate(T, a, v), List.replicate(T, b, v)) : List<&2, T>}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      AP.con_cong(T, v, List.replicate(T, Nat.add(p, b), v), List.append(&2, T, List.replicate(T, p, v), List.replicate(T, b, v)), AP.rep_add(T, p, b, v))

def AP.unsome(-T: Data, m: Maybe<&2, T>, x: T) -> T:
  match m:
    case Some{y}:
      y
    case None{}:
      x

def AP.some_inj(-T: Data, -x: T, -y: T, e: {Some{x} == Some{y} : Maybe<&2, T>}) -> {x == y : T}:
  Equal.cong(Maybe<&2, T>, T, m => AP.unsome(T, m, x), Some{x}, Some{y}, e)

def AP.perf_rw(-T: Data, -d: Nat, -a: Array<T>, -t: AP.Tree<T>, e: {AP.build(T, t) == a : Array<T>}, h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}) -> {A.Arrays.is_perfect(T, d, AP.build(T, t)) == True{} : Bool}:
  %Equal.sym(Array<T>, AP.build(T, t), a, e) : {A.Arrays.is_perfect(T, d, _) == True{} : Bool}
  h

def AP.index_lt(+d: Nat, +i: U32) -> {Nat.is_lt(A.Arrays.index(d, i), A.Arrays.slots(d)) == True{} : Bool}:
  %Equal.sym(U32, U32.sub(U32.shln(1, d), 1), U32{AP.lm(32n, d)}, AP.mask_lm(d)) : {Nat.is_lt(U32.to_nat(U32.and(i, _)), A.Arrays.slots(d)) == True{} : Bool}
  AP.u32_mask_lt(i, d)

# The tree forms of the model laws

def AP.tree_perf(-T: Data, +d: Nat, +t: AP.Tree<T>, +i: U32, +v: T, h: {A.Arrays.is_perfect(T, d, AP.build(T, t)) == True{} : Bool}) -> {A.Arrays.is_perfect(T, d, AP.build(T, AP.set_top(T, t, i, v))) == True{} : Bool}:
  +n = AP.size(T, t)
  +j = AP.mask(n, i)
  Equal.trans(Bool, A.Arrays.is_perfect(T, d, AP.build(T, AP.swap_t(T, t, n, j, v, AP.z(n, j)))), A.Arrays.is_perfect(T, d, AP.build(T, t)), True{}, AP.perf_swap(T, t, n, j, v, AP.z(n, j), d), h)

def AP.tree_get(-T: Data, +d: Nat, +t: AP.Tree<T>, +hp: {A.Arrays.is_perfect(T, d, AP.build(T, t)) == True{} : Bool}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +i: U32) -> {List.get(&2, T, A.Arrays.leaves(T, AP.build(T, t)), A.Arrays.index(d, i)) == Some{AP.get_top(T, t, i)} : Maybe<&2, T>}:
  +sh = U32.shln(1, d)
  +j = AP.mask(sh, i)
  %Equal.sym(U32, AP.size(T, t), sh, AP.size_perf(T, d, t, hp)) : {List.get(&2, T, A.Arrays.leaves(T, AP.build(T, t)), A.Arrays.index(d, i)) == Some{AP.get_v(T, t, _, AP.mask(_, i), AP.z(_, AP.mask(_, i)))} : Maybe<&2, T>}
  AP.get_leaves(T, d, t, j, AP.z(sh, j), {==}, hd, hp, AP.index_lt(d, i))

def AP.tree_set(-T: Data, +d: Nat, +t: AP.Tree<T>, +hp: {A.Arrays.is_perfect(T, d, AP.build(T, t)) == True{} : Bool}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +i: U32, +v: T) -> {A.Arrays.leaves(T, AP.build(T, AP.set_top(T, t, i, v))) == List.set(&2, T, A.Arrays.leaves(T, AP.build(T, t)), A.Arrays.index(d, i), v) : List<&2, T>}:
  +sh = U32.shln(1, d)
  +j = AP.mask(sh, i)
  %Equal.sym(U32, AP.size(T, t), sh, AP.size_perf(T, d, t, hp)) : {A.Arrays.leaves(T, AP.build(T, AP.swap_t(T, t, _, AP.mask(_, i), v, AP.z(_, AP.mask(_, i))))) == List.set(&2, T, A.Arrays.leaves(T, AP.build(T, t)), A.Arrays.index(d, i), v) : List<&2, T>}
  AP.set_leaves(T, d, t, j, v, AP.z(sh, j), {==}, hd, hp, AP.index_lt(d, i))

# The laws, each through the reflection of its array

def AP.set_keeps_size.go(-T: Data, -a: Array<T>, +i: U32, +v: T, r: &t: AP.Tree<T> -> {AP.build(T, t) == a : Array<T>}) -> {Pair.snd(Array<T>, U32, Array.size(T, Array.set(T, a, i, v))) == Pair.snd(Array<T>, U32, Array.size(T, a)) : U32}:
  (+t, e) = r
  +n = AP.size(T, t)
  +j = AP.mask(n, i)
  +t2 = AP.set_top(T, t, i, v)
  %e : {Pair.snd(Array<T>, U32, Array.size(T, Array.set(T, _, i, v))) == Pair.snd(Array<T>, U32, Array.size(T, _)) : U32}
  %Equal.sym(Array<T>, Array.set(T, AP.build(T, t), i, v), AP.build(T, t2), AP.set_top_eq(T, t, i, v)) : {Pair.snd(Array<T>, U32, Array.size(T, _)) == Pair.snd(Array<T>, U32, Array.size(T, AP.build(T, t))) : U32}
  %Equal.sym(Array<T> & U32, Array.size(T, AP.build(T, t2)), (AP.build(T, t2), AP.size(T, t2)), AP.size_eq(T, t2)) : {Pair.snd(Array<T>, U32, _) == Pair.snd(Array<T>, U32, Array.size(T, AP.build(T, t))) : U32}
  %Equal.sym(Array<T> & U32, Array.size(T, AP.build(T, t)), (AP.build(T, t), n), AP.size_eq(T, t)) : {AP.size(T, t2) == Pair.snd(Array<T>, U32, _) : U32}
  AP.swap_size(T, t, n, j, v, AP.z(n, j))

def AP.get_new.go(-T: Data, +d: Nat, +v: T, +i: U32) -> {Pair.snd(Array<T>, T, Array.get(T, Array.new(T, d, v), i)) == v : T}:
  +t = AP.tnew(T, d, v)
  +n = AP.size(T, t)
  +j = AP.mask(n, i)
  %Equal.sym(Array<T>, Array.new(T, d, v), AP.build(T, t), AP.new_eq(T, d, v)) : {Pair.snd(Array<T>, T, Array.get(T, _, i)) == v : T}
  %Equal.sym(Array<T> & T, Array.get(T, AP.build(T, t), i), (AP.build(T, t), AP.get_top(T, t, i)), AP.get_top_eq(T, t, i)) : {Pair.snd(Array<T>, T, _) == v : T}
  AP.get_v_new(T, d, v, n, j, AP.z(n, j))

def AP.set_perfect.go.body(-T: Data, +d: Nat, -a: Array<T>, h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}, +i: U32, +v: T, +t: AP.Tree<T>, +e: {AP.build(T, t) == a : Array<T>}) -> {A.Arrays.is_perfect(T, d, Array.set(T, a, i, v)) == True{} : Bool}:
  %e : {A.Arrays.is_perfect(T, d, Array.set(T, _, i, v)) == True{} : Bool}
  %Equal.sym(Array<T>, Array.set(T, AP.build(T, t), i, v), AP.build(T, AP.set_top(T, t, i, v)), AP.set_top_eq(T, t, i, v)) : {A.Arrays.is_perfect(T, d, _) == True{} : Bool}
  AP.tree_perf(T, d, t, i, v, AP.perf_rw(T, d, a, t, e, h))

def AP.set_perfect.go(-T: Data, +d: Nat, -a: Array<T>, h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}, +i: U32, +v: T, r: &t: AP.Tree<T> -> {AP.build(T, t) == a : Array<T>}) -> {A.Arrays.is_perfect(T, d, Array.set(T, a, i, v)) == True{} : Bool}:
  (t, e) = r
  AP.set_perfect.go.body(T, d, a, h, i, v, t, e)

def AP.size_perfect.go.body(-T: Data, +d: Nat, -a: Array<T>, h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}, +t: AP.Tree<T>, +e: {AP.build(T, t) == a : Array<T>}) -> {Array.size(T, a) == (a, U32.shln(1, d)) : Array<T> & U32}:
  %e : {Array.size(T, _) == (_, U32.shln(1, d)) : Array<T> & U32}
  %Equal.sym(Array<T> & U32, Array.size(T, AP.build(T, t)), (AP.build(T, t), AP.size(T, t)), AP.size_eq(T, t)) : {_ == (AP.build(T, t), U32.shln(1, d)) : Array<T> & U32}
  %Equal.sym(U32, AP.size(T, t), U32.shln(1, d), AP.size_perf(T, d, t, AP.perf_rw(T, d, a, t, e, h))) : {(AP.build(T, t), _) == (AP.build(T, t), U32.shln(1, d)) : Array<T> & U32}
  {==}

def AP.size_perfect.go(-T: Data, +d: Nat, -a: Array<T>, h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}, r: &t: AP.Tree<T> -> {AP.build(T, t) == a : Array<T>}) -> {Array.size(T, a) == (a, U32.shln(1, d)) : Array<T> & U32}:
  (t, e) = r
  AP.size_perfect.go.body(T, d, a, h, t, e)

def AP.new_leaves.go(-T: Data, +d: Nat, +v: T) -> {A.Arrays.leaves(T, Array.new(T, d, v)) == List.replicate(T, A.Arrays.slots(d), v) : List<&2, T>}:
  match d:
    case 0n:
      {==}
    case 1n+ +p:
      +s = A.Arrays.slots(p)
      %Equal.sym(List<&2, T>, A.Arrays.leaves(T, Array.new(T, p, v)), List.replicate(T, s, v), AP.new_leaves.go(T, p, v)) : {List.append(&2, T, _, _) == List.replicate(T, Nat.double(s), v) : List<&2, T>}
      %Equal.sym(Nat, Nat.double(s), Nat.add(s, s), AP.double_self(s)) : {List.append(&2, T, List.replicate(T, s, v), List.replicate(T, s, v)) == List.replicate(T, _, v) : List<&2, T>}
      Equal.sym(List<&2, T>, List.replicate(T, Nat.add(s, s), v), List.append(&2, T, List.replicate(T, s, v), List.replicate(T, s, v)), AP.rep_add(T, s, s, v))

def AP.model_length.go.body(-T: Data, +d: Nat, -a: Array<T>, h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}, +t: AP.Tree<T>, +e: {AP.build(T, t) == a : Array<T>}) -> {List.length(&2, T, A.Arrays.leaves(T, a)) == A.Arrays.slots(d) : Nat}:
  %e : {List.length(&2, T, A.Arrays.leaves(T, _)) == A.Arrays.slots(d) : Nat}
  AP.len_perf(T, d, t, AP.perf_rw(T, d, a, t, e, h))

def AP.model_length.go(-T: Data, +d: Nat, -a: Array<T>, h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}, r: &t: AP.Tree<T> -> {AP.build(T, t) == a : Array<T>}) -> {List.length(&2, T, A.Arrays.leaves(T, a)) == A.Arrays.slots(d) : Nat}:
  (t, e) = r
  AP.model_length.go.body(T, d, a, h, t, e)

def AP.model_get.go.body(-T: Data, +d: Nat, -a: Array<T>, h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +i: U32, +t: AP.Tree<T>, +e: {AP.build(T, t) == a : Array<T>}) -> {List.get(&2, T, A.Arrays.leaves(T, a), A.Arrays.index(d, i)) == Some{Pair.snd(Array<T>, T, Array.get(T, a, i))} : Maybe<&2, T>}:
  %e : {List.get(&2, T, A.Arrays.leaves(T, _), A.Arrays.index(d, i)) == Some{Pair.snd(Array<T>, T, Array.get(T, _, i))} : Maybe<&2, T>}
  %Equal.sym(Array<T> & T, Array.get(T, AP.build(T, t), i), (AP.build(T, t), AP.get_top(T, t, i)), AP.get_top_eq(T, t, i)) : {List.get(&2, T, A.Arrays.leaves(T, AP.build(T, t)), A.Arrays.index(d, i)) == Some{Pair.snd(Array<T>, T, _)} : Maybe<&2, T>}
  AP.tree_get(T, d, t, AP.perf_rw(T, d, a, t, e, h), hd, i)

def AP.model_get.go(-T: Data, +d: Nat, -a: Array<T>, h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +i: U32, r: &t: AP.Tree<T> -> {AP.build(T, t) == a : Array<T>}) -> {List.get(&2, T, A.Arrays.leaves(T, a), A.Arrays.index(d, i)) == Some{Pair.snd(Array<T>, T, Array.get(T, a, i))} : Maybe<&2, T>}:
  (t, e) = r
  AP.model_get.go.body(T, d, a, h, hd, i, t, e)

def AP.model_set.go.body(-T: Data, +d: Nat, -a: Array<T>, h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +i: U32, +v: T, +t: AP.Tree<T>, +e: {AP.build(T, t) == a : Array<T>}) -> {A.Arrays.leaves(T, Array.set(T, a, i, v)) == List.set(&2, T, A.Arrays.leaves(T, a), A.Arrays.index(d, i), v) : List<&2, T>}:
  %e : {A.Arrays.leaves(T, Array.set(T, _, i, v)) == List.set(&2, T, A.Arrays.leaves(T, _), A.Arrays.index(d, i), v) : List<&2, T>}
  %Equal.sym(Array<T>, Array.set(T, AP.build(T, t), i, v), AP.build(T, AP.set_top(T, t, i, v)), AP.set_top_eq(T, t, i, v)) : {A.Arrays.leaves(T, _) == List.set(&2, T, A.Arrays.leaves(T, AP.build(T, t)), A.Arrays.index(d, i), v) : List<&2, T>}
  AP.tree_set(T, d, t, AP.perf_rw(T, d, a, t, e, h), hd, i, v)

def AP.model_set.go(-T: Data, +d: Nat, -a: Array<T>, h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +i: U32, +v: T, r: &t: AP.Tree<T> -> {AP.build(T, t) == a : Array<T>}) -> {A.Arrays.leaves(T, Array.set(T, a, i, v)) == List.set(&2, T, A.Arrays.leaves(T, a), A.Arrays.index(d, i), v) : List<&2, T>}:
  (t, e) = r
  AP.model_set.go.body(T, d, a, h, hd, i, v, t, e)

def AP.get_set_other.go.body(-T: Data, +d: Nat, -a: Array<T>, h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +i: U32, +j: U32, +v: T, hij: {U32.is_eq(U32.and(i, U32.sub(U32.shln(1, d), 1)), U32.and(j, U32.sub(U32.shln(1, d), 1))) == False{} : Bool}, +t: AP.Tree<T>, +e: {AP.build(T, t) == a : Array<T>}) -> {Pair.snd(Array<T>, T, Array.get(T, Array.set(T, a, i, v), j)) == Pair.snd(Array<T>, T, Array.get(T, a, j)) : T}:
  +hp = AP.perf_rw(T, d, a, t, e, h)
  +t2 = AP.set_top(T, t, i, v)
  +l = A.Arrays.leaves(T, AP.build(T, t))
  +ki = A.Arrays.index(d, i)
  +kj = A.Arrays.index(d, j)
  +m = U32.sub(U32.shln(1, d), 1)
  +hk = Equal.trans(Bool, Nat.is_eq(ki, kj), U32.is_eq(U32.and(i, m), U32.and(j, m)), False{}, Equal.sym(Bool, U32.is_eq(U32.and(i, m), U32.and(j, m)), Nat.is_eq(ki, kj), AP.u32_eq(U32.and(i, m), U32.and(j, m))), hij)
  %e : {Pair.snd(Array<T>, T, Array.get(T, Array.set(T, _, i, v), j)) == Pair.snd(Array<T>, T, Array.get(T, _, j)) : T}
  %Equal.sym(Array<T>, Array.set(T, AP.build(T, t), i, v), AP.build(T, t2), AP.set_top_eq(T, t, i, v)) : {Pair.snd(Array<T>, T, Array.get(T, _, j)) == Pair.snd(Array<T>, T, Array.get(T, AP.build(T, t), j)) : T}
  %Equal.sym(Array<T> & T, Array.get(T, AP.build(T, t2), j), (AP.build(T, t2), AP.get_top(T, t2, j)), AP.get_top_eq(T, t2, j)) : {Pair.snd(Array<T>, T, _) == Pair.snd(Array<T>, T, Array.get(T, AP.build(T, t), j)) : T}
  %Equal.sym(Array<T> & T, Array.get(T, AP.build(T, t), j), (AP.build(T, t), AP.get_top(T, t, j)), AP.get_top_eq(T, t, j)) : {AP.get_top(T, t2, j) == Pair.snd(Array<T>, T, _) : T}
  +e1 = Equal.sym(Maybe<&2, T>, List.get(&2, T, A.Arrays.leaves(T, AP.build(T, t2)), kj), Some{AP.get_top(T, t2, j)}, AP.tree_get(T, d, t2, AP.tree_perf(T, d, t, i, v, hp), hd, j))
  +e2 = Equal.cong(List<&2, T>, Maybe<&2, T>, xs => List.get(&2, T, xs, kj), A.Arrays.leaves(T, AP.build(T, t2)), List.set(&2, T, l, ki, v), AP.tree_set(T, d, t, hp, hd, i, v))
  +e3 = AP.get_set_other(T, l, ki, kj, v, hk)
  +e4 = AP.tree_get(T, d, t, hp, hd, j)
  AP.some_inj(T, AP.get_top(T, t2, j), AP.get_top(T, t, j), Equal.trans(Maybe<&2, T>, Some{AP.get_top(T, t2, j)}, List.get(&2, T, l, kj), Some{AP.get_top(T, t, j)}, Equal.trans(Maybe<&2, T>, Some{AP.get_top(T, t2, j)}, List.get(&2, T, List.set(&2, T, l, ki, v), kj), List.get(&2, T, l, kj), Equal.trans(Maybe<&2, T>, Some{AP.get_top(T, t2, j)}, List.get(&2, T, A.Arrays.leaves(T, AP.build(T, t2)), kj), List.get(&2, T, List.set(&2, T, l, ki, v), kj), e1, e2), e3), e4))

def AP.get_set_other.go(-T: Data, +d: Nat, -a: Array<T>, h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +i: U32, +j: U32, +v: T, hij: {U32.is_eq(U32.and(i, U32.sub(U32.shln(1, d), 1)), U32.and(j, U32.sub(U32.shln(1, d), 1))) == False{} : Bool}, r: &t: AP.Tree<T> -> {AP.build(T, t) == a : Array<T>}) -> {Pair.snd(Array<T>, T, Array.get(T, Array.set(T, a, i, v), j)) == Pair.snd(Array<T>, T, Array.get(T, a, j)) : T}:
  (t, e) = r
  AP.get_set_other.go.body(T, d, a, h, hd, i, j, v, hij, t, e)

def AP.index_of_nat.go(+d: Nat, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +k: Nat, +hk: {Nat.is_lt(k, A.Arrays.slots(d)) == True{} : Bool}) -> {A.Arrays.index(d, U32.from_nat(k)) == k : Nat}:
  +a = U32.from_nat(k)
  +fk = AP.from_nat(k, d, hk, AP.lt_le(d, 32n, hd))
  %Equal.sym(U32, U32.sub(U32.shln(1, d), 1), U32{AP.lm(32n, d)}, AP.mask_lm(d)) : {U32.to_nat(U32.and(a, _)) == k : Nat}
  %Equal.sym(U32, U32.and(a, U32{AP.lm(32n, d)}), a, AP.u32_and_id(a, d, AP.lt_rw_l(U32.to_nat(a), k, A.Arrays.slots(d), fk, hk))) : {U32.to_nat(_) == k : Nat}
  fk


# Arrays built from a Data list

def AP.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def AP.pred_cong(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, n => AP.pred(n), 1n+a, 1n+b, e)

def AP.tof(-T: Data, +d: Nat, +xs: List<&2, T>, +f: T) -> AP.Tree<T>:
  match d:
    case 0n:
      APLeaf{A.Arrays.nth(T, xs, 0n, f)}
    case 1n+p:
      +s = A.Arrays.slots(p)
      APNode{AP.tof(T, p, List.take(&2, T, xs, s), f), AP.tof(T, p, List.drop(&2, T, xs, s), f)}

def AP.of_list_eq(-T: Data, +d: Nat, +xs: List<&2, T>, +f: T) -> {A.Arrays.of_list(T, d, xs, f) == AP.build(T, AP.tof(T, d, xs, f)) : Array<T>}:
  match d:
    case 0n:
      {==}
    case 1n+ +p:
      +s = A.Arrays.slots(p)
      +l = List.take(&2, T, xs, s)
      +r = List.drop(&2, T, xs, s)
      %Equal.sym(Array<T>, A.Arrays.of_list(T, p, l, f), AP.build(T, AP.tof(T, p, l, f)), AP.of_list_eq(T, p, l, f)) : {ANode{_, A.Arrays.of_list(T, p, r, f)} == ANode{AP.build(T, AP.tof(T, p, l, f)), AP.build(T, AP.tof(T, p, r, f))} : Array<T>}
      %Equal.sym(Array<T>, A.Arrays.of_list(T, p, r, f), AP.build(T, AP.tof(T, p, r, f)), AP.of_list_eq(T, p, r, f)) : {ANode{AP.build(T, AP.tof(T, p, l, f)), _} == ANode{AP.build(T, AP.tof(T, p, l, f)), AP.build(T, AP.tof(T, p, r, f))} : Array<T>}
      {==}

def AP.tof_perf(-T: Data, +d: Nat, +xs: List<&2, T>, +f: T) -> {A.Arrays.is_perfect(T, d, AP.build(T, AP.tof(T, d, xs, f))) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+ +p:
      +s = A.Arrays.slots(p)
      +l = List.take(&2, T, xs, s)
      +r = List.drop(&2, T, xs, s)
      %Equal.sym(Bool, A.Arrays.is_perfect(T, p, AP.build(T, AP.tof(T, p, l, f))), True{}, AP.tof_perf(T, p, l, f)) : {Bool.and(_, A.Arrays.is_perfect(T, p, AP.build(T, AP.tof(T, p, r, f)))) == True{} : Bool}
      AP.tof_perf(T, p, r, f)

def AP.take_drop(-T: Data, xs: List<&2, T>, n: Nat) -> {List.append(&2, T, List.take(&2, T, xs, n), List.drop(&2, T, xs, n)) == xs : List<&2, T>}:
  match xs n:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      AP.con_cong(T, x, List.append(&2, T, List.take(&2, T, t, p), List.drop(&2, T, t, p)), t, AP.take_drop(T, t, p))

def AP.take_app(-T: Data, xs: List<&2, T>, ys: List<&2, T>) -> {List.take(&2, T, List.append(&2, T, xs, ys), List.length(&2, T, xs)) == xs : List<&2, T>}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case Con{y, t}:
          {==}
    case Con{x, t}:
      AP.con_cong(T, x, List.take(&2, T, List.append(&2, T, t, ys), List.length(&2, T, t)), t, AP.take_app(T, t, ys))

def AP.drop_app(-T: Data, xs: List<&2, T>, ys: List<&2, T>) -> {List.drop(&2, T, List.append(&2, T, xs, ys), List.length(&2, T, xs)) == ys : List<&2, T>}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case Con{y, t}:
          {==}
    case Con{x, t}:
      AP.drop_app(T, t, ys)

# a list of n + m elements cut after n: n, then m elements
def AP.len_take(-T: Data, xs: List<&2, T>, n: Nat, -m: Nat, h: {List.length(&2, T, xs) == Nat.add(n, m) : Nat}) -> {List.length(&2, T, List.take(&2, T, xs, n)) == n : Nat}:
  match xs n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      Empty.absurd({List.length(&2, T, List.take(&2, T, Nil{}, 1n+p)) == 1n+p : Nat}, AP.sz(Nat.add(p, m), Equal.sym(Nat, 0n, 1n+Nat.add(p, m), h)))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      AP.succ_cong(List.length(&2, T, List.take(&2, T, t, p)), p, AP.len_take(T, t, p, m, AP.pred_cong(List.length(&2, T, t), Nat.add(p, m), h)))

def AP.len_drop(-T: Data, xs: List<&2, T>, n: Nat, -m: Nat, h: {List.length(&2, T, xs) == Nat.add(n, m) : Nat}) -> {List.length(&2, T, List.drop(&2, T, xs, n)) == m : Nat}:
  match xs n:
    case Nil{} 0n:
      h
    case Nil{} 1n+p:
      Empty.absurd({List.length(&2, T, List.drop(&2, T, Nil{}, 1n+p)) == m : Nat}, AP.sz(Nat.add(p, m), Equal.sym(Nat, 0n, 1n+Nat.add(p, m), h)))
    case Con{x, t} 0n:
      h
    case Con{x, t} 1n+p:
      AP.len_drop(T, t, p, m, AP.pred_cong(List.length(&2, T, t), Nat.add(p, m), h))

def AP.one_elem(-T: Data, xs: List<&2, T>, -f: T, h: {List.length(&2, T, xs) == 1n : Nat}) -> {Con{A.Arrays.nth(T, xs, 0n, f), Nil{}} == xs : List<&2, T>}:
  match xs:
    case Nil{}:
      Empty.absurd({Con{A.Arrays.nth(T, Nil{}, 0n, f), Nil{}} == Nil{} : List<&2, T>}, AP.sz(0n, Equal.sym(Nat, 0n, 1n, h)))
    case Con{x, t}:
      match t:
        case Nil{}:
          {==}
        case Con{y, u}:
          Empty.absurd({Con{A.Arrays.nth(T, Con{x, Con{y, u}}, 0n, f), Nil{}} == Con{x, Con{y, u}} : List<&2, T>}, AP.sz(List.length(&2, T, u), AP.pred_cong(1n+List.length(&2, T, u), 0n, h)))

def AP.tof_leaves(-T: Data, +d: Nat, +xs: List<&2, T>, +f: T, +h: {List.length(&2, T, xs) == A.Arrays.slots(d) : Nat}) -> {A.Arrays.leaves(T, AP.build(T, AP.tof(T, d, xs, f))) == xs : List<&2, T>}:
  match d:
    case 0n:
      AP.one_elem(T, xs, f, h)
    case 1n+ +p:
      +s = A.Arrays.slots(p)
      +l = List.take(&2, T, xs, s)
      +r = List.drop(&2, T, xs, s)
      +h2 = Equal.trans(Nat, List.length(&2, T, xs), Nat.double(s), Nat.add(s, s), h, AP.double_self(s))
      %Equal.sym(List<&2, T>, A.Arrays.leaves(T, AP.build(T, AP.tof(T, p, l, f))), l, AP.tof_leaves(T, p, l, f, AP.len_take(T, xs, s, s, h2))) : {List.append(&2, T, _, A.Arrays.leaves(T, AP.build(T, AP.tof(T, p, r, f)))) == xs : List<&2, T>}
      %Equal.sym(List<&2, T>, A.Arrays.leaves(T, AP.build(T, AP.tof(T, p, r, f))), r, AP.tof_leaves(T, p, r, f, AP.len_drop(T, xs, s, s, h2))) : {List.append(&2, T, l, _) == xs : List<&2, T>}
      AP.take_drop(T, xs, s)

# a perfect tree is the tree of its own leaves
def AP.tree_ext(-T: Data, +d: Nat, +t: AP.Tree<T>, +f: T, +hp: {A.Arrays.is_perfect(T, d, AP.build(T, t)) == True{} : Bool}) -> {AP.build(T, t) == AP.build(T, AP.tof(T, d, A.Arrays.leaves(T, AP.build(T, t)), f)) : Array<T>}:
  match d t:
    case 0n APLeaf{x}:
      {==}
    case 0n APNode{xs, ys}:
      Empty.absurd({AP.build(T, APNode{xs, ys}) == AP.build(T, AP.tof(T, 0n, A.Arrays.leaves(T, AP.build(T, APNode{xs, ys})), f)) : Array<T>}, AP.ft(hp))
    case 1n+p APLeaf{x}:
      Empty.absurd({AP.build(T, APLeaf{x}) == AP.build(T, AP.tof(T, 1n+p, A.Arrays.leaves(T, AP.build(T, APLeaf{x})), f)) : Array<T>}, AP.ft(hp))
    case 1n+ +p APNode{xs, ys}:
      +s = A.Arrays.slots(p)
      +lx = A.Arrays.leaves(T, AP.build(T, xs))
      +ly = A.Arrays.leaves(T, AP.build(T, ys))
      +hpx = AP.and_l(A.Arrays.is_perfect(T, p, AP.build(T, xs)), A.Arrays.is_perfect(T, p, AP.build(T, ys)), hp)
      +hpy = AP.and_r(A.Arrays.is_perfect(T, p, AP.build(T, xs)), A.Arrays.is_perfect(T, p, AP.build(T, ys)), hp)
      +hl = AP.len_perf(T, p, xs, hpx)
      %hl : {ANode{AP.build(T, xs), AP.build(T, ys)} == ANode{AP.build(T, AP.tof(T, p, List.take(&2, T, List.append(&2, T, lx, ly), _), f)), AP.build(T, AP.tof(T, p, List.drop(&2, T, List.append(&2, T, lx, ly), _), f))} : Array<T>}
      %Equal.sym(List<&2, T>, List.take(&2, T, List.append(&2, T, lx, ly), List.length(&2, T, lx)), lx, AP.take_app(T, lx, ly)) : {ANode{AP.build(T, xs), AP.build(T, ys)} == ANode{AP.build(T, AP.tof(T, p, _, f)), AP.build(T, AP.tof(T, p, List.drop(&2, T, List.append(&2, T, lx, ly), List.length(&2, T, lx)), f))} : Array<T>}
      %Equal.sym(List<&2, T>, List.drop(&2, T, List.append(&2, T, lx, ly), List.length(&2, T, lx)), ly, AP.drop_app(T, lx, ly)) : {ANode{AP.build(T, xs), AP.build(T, ys)} == ANode{AP.build(T, AP.tof(T, p, lx, f)), AP.build(T, AP.tof(T, p, _, f))} : Array<T>}
      %AP.tree_ext(T, p, xs, f, hpx) : {ANode{AP.build(T, xs), AP.build(T, ys)} == ANode{_, AP.build(T, AP.tof(T, p, ly, f))} : Array<T>}
      %AP.tree_ext(T, p, ys, f, hpy) : {ANode{AP.build(T, xs), AP.build(T, ys)} == ANode{AP.build(T, xs), _} : Array<T>}
      {==}

def AP.nth_get(-T: Data, -xs: List<&2, T>, -k: Nat, -f: T, -g: T, e: {List.get(&2, T, xs, k) == Some{g} : Maybe<&2, T>}) -> {A.Arrays.nth(T, xs, k, f) == g : T}:
  %Equal.sym(Maybe<&2, T>, List.get(&2, T, xs, k), Some{g}, e) : {A.Arrays.nth.or(T, _, f) == g : T}
  {==}

def AP.set_length(-T: Data, xs: List<&2, T>, k: Nat, -v: T) -> {List.length(&2, T, List.set(&2, T, xs, k, v)) == List.length(&2, T, xs) : Nat}:
  match xs k:
    case Nil{} _:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      AP.succ_cong(List.length(&2, T, List.set(&2, T, t, p, v)), List.length(&2, T, t), AP.set_length(T, t, p, v))

def AP.get_set_same(-T: Data, xs: List<&2, T>, k: Nat, -v: T, h: {Nat.is_lt(k, List.length(&2, T, xs)) == True{} : Bool}) -> {List.get(&2, T, List.set(&2, T, xs, k, v), k) == Some{v} : Maybe<&2, T>}:
  match xs k:
    case Nil{} _:
      Empty.absurd({List.get(&2, T, List.set(&2, T, Nil{}, k, v), k) == Some{v} : Maybe<&2, T>}, AP.ft(Equal.trans(Bool, False{}, Nat.is_lt(k, 0n), True{}, Equal.sym(Bool, Nat.is_lt(k, 0n), False{}, AP.lt_zero(k)), h)))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+p:
      AP.get_set_same(T, t, p, v, h)

def AP.get_rep(-T: Data, n: Nat, k: Nat, +v: T, h: {Nat.is_lt(k, n) == True{} : Bool}) -> {List.get(&2, T, List.replicate(T, n, v), k) == Some{v} : Maybe<&2, T>}:
  match n k:
    case 0n _:
      Empty.absurd({List.get(&2, T, List.replicate(T, 0n, v), k) == Some{v} : Maybe<&2, T>}, AP.ft(Equal.trans(Bool, False{}, Nat.is_lt(k, 0n), True{}, Equal.sym(Bool, Nat.is_lt(k, 0n), False{}, AP.lt_zero(k)), h)))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      AP.get_rep(T, p, q, v, h)

def AP.tnew_tof(-T: Data, +d: Nat, +v: T) -> {AP.build(T, AP.tnew(T, d, v)) == AP.build(T, AP.tof(T, d, List.replicate(T, A.Arrays.slots(d), v), v)) : Array<T>}:
  +t = AP.tnew(T, d, v)
  +hp = Equal.trans(Bool, A.Arrays.is_perfect(T, d, AP.build(T, t)), A.Arrays.is_perfect(T, d, Array.new(T, d, v)), True{}, Equal.cong(Array<T>, Bool, a => A.Arrays.is_perfect(T, d, a), AP.build(T, t), Array.new(T, d, v), Equal.sym(Array<T>, Array.new(T, d, v), AP.build(T, t), AP.new_eq(T, d, v))), AP.new_perf(T, d, v))
  +hl = Equal.trans(List<&2, T>, A.Arrays.leaves(T, AP.build(T, t)), A.Arrays.leaves(T, Array.new(T, d, v)), List.replicate(T, A.Arrays.slots(d), v), Equal.cong(Array<T>, List<&2, T>, a => A.Arrays.leaves(T, a), AP.build(T, t), Array.new(T, d, v), Equal.sym(Array<T>, Array.new(T, d, v), AP.build(T, t), AP.new_eq(T, d, v))), AP.new_leaves.go(T, d, v))
  %hl : {AP.build(T, t) == AP.build(T, AP.tof(T, d, _, v)) : Array<T>}
  AP.tree_ext(T, d, t, v, hp)

def AP.reflect_list(-T: Data, +d: Nat, -a: Array<T>, h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}, +f: T, +t: AP.Tree<T>, +e: {AP.build(T, t) == a : Array<T>}) -> &xs: List<&2, T> -> {A.Arrays.of_list(T, d, xs, f) == a : Array<T>} & {List.length(&2, T, xs) == A.Arrays.slots(d) : Nat}:
  +hp = AP.perf_rw(T, d, a, t, e, h)
  +xs = A.Arrays.leaves(T, AP.build(T, t))
  +e1 = Equal.trans(Array<T>, A.Arrays.of_list(T, d, xs, f), AP.build(T, AP.tof(T, d, xs, f)), a, AP.of_list_eq(T, d, xs, f), Equal.trans(Array<T>, AP.build(T, AP.tof(T, d, xs, f)), AP.build(T, t), a, Equal.sym(Array<T>, AP.build(T, t), AP.build(T, AP.tof(T, d, xs, f)), AP.tree_ext(T, d, t, f, hp)), e))
  (xs, (e1, AP.len_perf(T, d, t, hp)))

def AP.ol_sym(-T: Data, +d: Nat, +xs: List<&2, T>, +f: T) -> {AP.build(T, AP.tof(T, d, xs, f)) == A.Arrays.of_list(T, d, xs, f) : Array<T>}:
  Equal.sym(Array<T>, A.Arrays.of_list(T, d, xs, f), AP.build(T, AP.tof(T, d, xs, f)), AP.of_list_eq(T, d, xs, f))

def AP.of_list_get.go(-T: Data, +d: Nat, +xs: List<&2, T>, +f: T, +hl: {List.length(&2, T, xs) == A.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +i: U32) -> {Array.get(T, A.Arrays.of_list(T, d, xs, f), i) == (A.Arrays.of_list(T, d, xs, f), A.Arrays.nth(T, xs, A.Arrays.index(d, i), f)) : Array<T> & T}:
  +t = AP.tof(T, d, xs, f)
  +k = A.Arrays.index(d, i)
  +g = AP.get_top(T, t, i)
  +el = AP.tof_leaves(T, d, xs, f, hl)
  +eg = Equal.trans(Maybe<&2, T>, List.get(&2, T, xs, k), List.get(&2, T, A.Arrays.leaves(T, AP.build(T, t)), k), Some{g}, Equal.cong(List<&2, T>, Maybe<&2, T>, ys => List.get(&2, T, ys, k), xs, A.Arrays.leaves(T, AP.build(T, t)), Equal.sym(List<&2, T>, A.Arrays.leaves(T, AP.build(T, t)), xs, el)), AP.tree_get(T, d, t, AP.tof_perf(T, d, xs, f), hd, i))
  %AP.ol_sym(T, d, xs, f) : {Array.get(T, _, i) == (_, A.Arrays.nth(T, xs, k, f)) : Array<T> & T}
  %Equal.sym(Array<T> & T, Array.get(T, AP.build(T, t), i), (AP.build(T, t), g), AP.get_top_eq(T, t, i)) : {_ == (AP.build(T, t), A.Arrays.nth(T, xs, k, f)) : Array<T> & T}
  %AP.nth_get(T, xs, k, f, g, eg) : {(AP.build(T, t), _) == (AP.build(T, t), A.Arrays.nth(T, xs, k, f)) : Array<T> & T}
  {==}

def AP.of_list_set.go(-T: Data, +d: Nat, +xs: List<&2, T>, +f: T, +hl: {List.length(&2, T, xs) == A.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +i: U32, +v: T) -> {Array.set(T, A.Arrays.of_list(T, d, xs, f), i, v) == A.Arrays.of_list(T, d, List.set(&2, T, xs, A.Arrays.index(d, i), v), f) : Array<T>}:
  +t = AP.tof(T, d, xs, f)
  +k = A.Arrays.index(d, i)
  +t2 = AP.set_top(T, t, i, v)
  +l2 = List.set(&2, T, xs, k, v)
  +el = AP.tof_leaves(T, d, xs, f, hl)
  +hp = AP.tof_perf(T, d, xs, f)
  +el2 = Equal.trans(List<&2, T>, A.Arrays.leaves(T, AP.build(T, t2)), List.set(&2, T, A.Arrays.leaves(T, AP.build(T, t)), k, v), l2, AP.tree_set(T, d, t, hp, hd, i, v), Equal.cong(List<&2, T>, List<&2, T>, ys => List.set(&2, T, ys, k, v), A.Arrays.leaves(T, AP.build(T, t)), xs, el))
  %AP.ol_sym(T, d, xs, f) : {Array.set(T, _, i, v) == A.Arrays.of_list(T, d, l2, f) : Array<T>}
  %Equal.sym(Array<T>, Array.set(T, AP.build(T, t), i, v), AP.build(T, t2), AP.set_top_eq(T, t, i, v)) : {_ == A.Arrays.of_list(T, d, l2, f) : Array<T>}
  %AP.ol_sym(T, d, l2, f) : {AP.build(T, t2) == _ : Array<T>}
  %el2 : {AP.build(T, t2) == AP.build(T, AP.tof(T, d, _, f)) : Array<T>}
  AP.tree_ext(T, d, t2, f, AP.tree_perf(T, d, t, i, v, hp))

def AP.of_list_size.go(-T: Data, +d: Nat, +xs: List<&2, T>, +f: T) -> {Array.size(T, A.Arrays.of_list(T, d, xs, f)) == (A.Arrays.of_list(T, d, xs, f), U32.shln(1, d)) : Array<T> & U32}:
  +t = AP.tof(T, d, xs, f)
  %AP.ol_sym(T, d, xs, f) : {Array.size(T, _) == (_, U32.shln(1, d)) : Array<T> & U32}
  %Equal.sym(Array<T> & U32, Array.size(T, AP.build(T, t)), (AP.build(T, t), AP.size(T, t)), AP.size_eq(T, t)) : {_ == (AP.build(T, t), U32.shln(1, d)) : Array<T> & U32}
  %Equal.sym(U32, AP.size(T, t), U32.shln(1, d), AP.size_perf(T, d, t, AP.tof_perf(T, d, xs, f))) : {(AP.build(T, t), _) == (AP.build(T, t), U32.shln(1, d)) : Array<T> & U32}
  {==}

def AP.reflect.go(-T: Data, +d: Nat, -a: Array<T>, h: {A.Arrays.is_perfect(T, d, a) == True{} : Bool}, +f: T, r: &t: AP.Tree<T> -> {AP.build(T, t) == a : Array<T>}) -> &xs: List<&2, T> -> {A.Arrays.of_list(T, d, xs, f) == a : Array<T>} & {List.length(&2, T, xs) == A.Arrays.slots(d) : Nat}:
  (t, e) = r
  AP.reflect_list(T, d, a, h, f, t, e)

# The laws

def Laws.get_same_array(T, a, i):
  AP.get_same_array.go(T, a, i, AP.reflect(T, a))

def Laws.get_set_same(T, a, i, v):
  AP.get_set_same.go(T, a, i, v, AP.reflect(T, a))

def Laws.set_keeps_size(T, a, i, v):
  AP.set_keeps_size.go(T, a, i, v, AP.reflect(T, a))

def Laws.get_new(T, d, v, i):
  AP.get_new.go(T, d, v, i)

def Laws.new_perfect(T, d, v):
  AP.new_perf(T, d, v)

def Laws.set_perfect(T, d, a, h, i, v):
  AP.set_perfect.go(T, d, a, h, i, v, AP.reflect(T, a))

def Laws.size_perfect(T, d, a, h):
  AP.size_perfect.go(T, d, a, h, AP.reflect(T, a))

def Laws.new_leaves(T, d, v):
  AP.new_leaves.go(T, d, v)

def Laws.model_length(T, d, a, h):
  AP.model_length.go(T, d, a, h, AP.reflect(T, a))

def Laws.model_get(T, d, a, h, hd, i):
  AP.model_get.go(T, d, a, h, hd, i, AP.reflect(T, a))

def Laws.model_set(T, d, a, h, hd, i, v):
  AP.model_set.go(T, d, a, h, hd, i, v, AP.reflect(T, a))

def Laws.get_set_other(T, d, a, h, hd, i, j, v, hij):
  AP.get_set_other.go(T, d, a, h, hd, i, j, v, hij, AP.reflect(T, a))

def Laws.index_below(d, i):
  AP.index_lt(d, i)

def Laws.index_of_nat(d, hd, k, hk):
  AP.index_of_nat.go(d, hd, k, hk)

def Laws.witness_perfect():
  {==}

def Laws.witness_other():
  {==}

def Laws.witness_index():
  {==}

def Laws.vector_wrap():
  {==}

def Laws.vector_leaves():
  {==}

def Laws.vector_index():
  {==}

def Laws.vector_not_perfect():
  {==}

def Laws.of_list_perfect(T, d, xs, f):
  %AP.ol_sym(T, d, xs, f) : {A.Arrays.is_perfect(T, d, _) == True{} : Bool}
  AP.tof_perf(T, d, xs, f)

def Laws.of_list_leaves(T, d, xs, f, hl):
  %AP.ol_sym(T, d, xs, f) : {A.Arrays.leaves(T, _) == xs : List<&2, T>}
  AP.tof_leaves(T, d, xs, f, hl)

def Laws.of_list_size(T, d, xs, f):
  AP.of_list_size.go(T, d, xs, f)

def Laws.of_list_get(T, d, xs, f, hl, hd, i):
  AP.of_list_get.go(T, d, xs, f, hl, hd, i)

def Laws.of_list_set(T, d, xs, f, hl, hd, i, v):
  AP.of_list_set.go(T, d, xs, f, hl, hd, i, v)

def Laws.of_list_new(T, d, v):
  Equal.trans(Array<T>, Array.new(T, d, v), AP.build(T, AP.tnew(T, d, v)), A.Arrays.of_list(T, d, List.replicate(T, A.Arrays.slots(d), v), v), AP.new_eq(T, d, v), Equal.trans(Array<T>, AP.build(T, AP.tnew(T, d, v)), AP.build(T, AP.tof(T, d, List.replicate(T, A.Arrays.slots(d), v), v)), A.Arrays.of_list(T, d, List.replicate(T, A.Arrays.slots(d), v), v), AP.tnew_tof(T, d, v), AP.ol_sym(T, d, List.replicate(T, A.Arrays.slots(d), v), v)))

def Laws.reflect(T, d, a, h, f):
  AP.reflect.go(T, d, a, h, f, AP.reflect(T, a))

def Laws.set_length(T, xs, k, v):
  AP.set_length(T, xs, k, v)

def Laws.nth_set_same(T, xs, k, v, f, h):
  AP.nth_get(T, List.set(&2, T, xs, k, v), k, f, v, AP.get_set_same(T, xs, k, v, h))

def Laws.nth_set_other(T, xs, k, m, v, f, h):
  Equal.cong(Maybe<&2, T>, T, x => A.Arrays.nth.or(T, x, f), List.get(&2, T, List.set(&2, T, xs, k, v), m), List.get(&2, T, xs, m), AP.get_set_other(T, xs, k, m, v, h))

def Laws.nth_replicate(T, n, v, k, f, h):
  AP.nth_get(T, List.replicate(T, n, v), k, f, v, AP.get_rep(T, n, k, v, h))

def Laws.witness_list():
  {==}

def Laws.vector_of_list():
  {==}
