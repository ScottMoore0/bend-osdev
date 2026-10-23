# Proof helpers for bend-osdev-word64: the value of a word and the
# arithmetic on it, for words of two halves of any width n (W64 is n = 32).
#
# A word's value is lo + 2^n * hi (wv.V); W64.to_nat is wv.V at n = 32 by
# computation. Every lemma here is stated for a width n that is a variable,
# so that no closed power of two (2^32, 2^64) is ever computed: such a
# number is a unary Nat in the checkers, and a type holding one cannot be
# compared by computation. The W64 laws (PROOF.bend) instantiate these
# lemmas at n = 32, where every term involved is symbolic.
#
# The arithmetic of each half is bend-osdev-u32's laws on Base's Word(n);
# the lemmas here put the halves together: the carry or borrow between them,
# and the wrap at 2^(2n).
import Base
import ../u32/u32.bend as U
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP

# Contradictions

def wn.bt(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def wn.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : wn.bt(_)
  Unit{}

def wn.cbt(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case o:
      Empty

def wn.eq_lt(e: {EQ{} == LT{} : Cmp}) -> Empty:
  %Equal.sym(Cmp, EQ{}, LT{}, e) : wn.cbt(_)
  Unit{}

def wn.gt_lt(e: {GT{} == LT{} : Cmp}) -> Empty:
  %Equal.sym(Cmp, GT{}, LT{}, e) : wn.cbt(_)
  Unit{}

def wn.ebt(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Unit
    case o:
      Empty

def wn.lt_eq(e: {LT{} == EQ{} : Cmp}) -> Empty:
  %Equal.sym(Cmp, LT{}, EQ{}, e) : wn.ebt(_)
  Unit{}

def wn.gt_eq(e: {GT{} == EQ{} : Cmp}) -> Empty:
  %Equal.sym(Cmp, GT{}, EQ{}, e) : wn.ebt(_)
  Unit{}

# Nat: sums

def wn.succ_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def wn.add_zero(x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      wn.succ_cong(Nat.add(p, 0n), p, wn.add_zero(p))

def wn.add_succ(x: Nat, -y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      wn.succ_cong(Nat.add(p, 1n+y), 1n+Nat.add(p, y), wn.add_succ(p, y))

def wn.add_comm(x: Nat, +y: Nat) -> {Nat.add(x, y) == Nat.add(y, x) : Nat}:
  match x:
    case 0n:
      Equal.sym(Nat, Nat.add(y, 0n), y, wn.add_zero(y))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, y), 1n+Nat.add(y, p), Nat.add(y, 1n+p), wn.succ_cong(Nat.add(p, y), Nat.add(y, p), wn.add_comm(p, y)), Equal.sym(Nat, Nat.add(y, 1n+p), 1n+Nat.add(y, p), wn.add_succ(y, p)))

def wn.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      wn.succ_cong(Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), wn.add_assoc(p, b, c))

# (a + b) + c = (a + c) + b
def wn.add_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, c), b), wn.add_assoc(a, b, c), Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(a, Nat.add(c, b)), Nat.add(Nat.add(a, c), b), Equal.cong(Nat, Nat, v => Nat.add(a, v), Nat.add(b, c), Nat.add(c, b), wn.add_comm(b, c)), Equal.sym(Nat, Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)), wn.add_assoc(a, c, b))))

# (a + b) + (c + d) = (a + c) + (b + d)
def wn.swap_mid(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)), wn.add_assoc(a, b, Nat.add(c, d)), Equal.trans(Nat, Nat.add(a, Nat.add(b, Nat.add(c, d))), Nat.add(a, Nat.add(Nat.add(b, c), d)), Nat.add(Nat.add(a, c), Nat.add(b, d)), Equal.cong(Nat, Nat, v => Nat.add(a, v), Nat.add(b, Nat.add(c, d)), Nat.add(Nat.add(b, c), d), Equal.sym(Nat, Nat.add(Nat.add(b, c), d), Nat.add(b, Nat.add(c, d)), wn.add_assoc(b, c, d))), Equal.trans(Nat, Nat.add(a, Nat.add(Nat.add(b, c), d)), Nat.add(a, Nat.add(Nat.add(c, b), d)), Nat.add(Nat.add(a, c), Nat.add(b, d)), Equal.cong(Nat, Nat, v => Nat.add(a, Nat.add(v, d)), Nat.add(b, c), Nat.add(c, b), wn.add_comm(b, c)), Equal.trans(Nat, Nat.add(a, Nat.add(Nat.add(c, b), d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), Nat.add(Nat.add(a, c), Nat.add(b, d)), Equal.cong(Nat, Nat, v => Nat.add(a, v), Nat.add(Nat.add(c, b), d), Nat.add(c, Nat.add(b, d)), wn.add_assoc(c, b, d)), Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), wn.add_assoc(a, c, Nat.add(b, d)))))))

# a + (b + c) = b + (a + c)
def wn.left_comm(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Nat.add(b, Nat.add(a, c)), Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), wn.add_assoc(a, b, c)), Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(b, a), c), Nat.add(b, Nat.add(a, c)), Equal.cong(Nat, Nat, v => Nat.add(v, c), Nat.add(a, b), Nat.add(b, a), wn.add_comm(a, b)), wn.add_assoc(b, a, c)))

def wn.sub_add_l(y: Nat, +r: Nat) -> {Nat.sub(Nat.add(y, r), y) == r : Nat}:
  match y:
    case 0n:
      match r:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+q:
      wn.sub_add_l(q, r)

def wn.sub_add(+r: Nat, +y: Nat) -> {Nat.sub(Nat.add(r, y), y) == r : Nat}:
  %wn.add_comm(y, r) : {Nat.sub(_, y) == r : Nat}
  wn.sub_add_l(y, r)

# Nat: order

def wn.lt_rw(-x: Nat, -x2: Nat, -y: Nat, e: {x == x2 : Nat}, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x2, y) == True{} : Bool}:
  %e : {Nat.is_lt(_, y) == True{} : Bool}
  h

def wn.lt_rw2(-x: Nat, -y: Nat, -y2: Nat, e: {y == y2 : Nat}, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x, y2) == True{} : Bool}:
  %e : {Nat.is_lt(x, _) == True{} : Bool}
  h

def wn.le_rw(-x: Nat, -x2: Nat, -y: Nat, e: {x == x2 : Nat}, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(x2, y) == True{} : Bool}:
  %e : {Nat.is_le(_, y) == True{} : Bool}
  h

def wn.le_succ(y: Nat, x: Nat) -> {Nat.is_le(1n+y, x) == Nat.is_lt(y, x) : Bool}:
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
      wn.le_succ(q, p)

def wn.le_zero(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def wn.not_lt_zero(x: Nat) -> {False{} == Nat.is_lt(x, 0n) : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def wn.lt_le_trans(x: Nat, y: Nat, z: Nat, h1: {Nat.is_lt(x, y) == True{} : Bool}, h2: {Nat.is_le(y, z) == True{} : Bool}) -> {Nat.is_lt(x, z) == True{} : Bool}:
  match x y z:
    case _ 0n _:
      Empty.absurd({Nat.is_lt(x, z) == True{} : Bool}, wn.ft(Equal.trans(Bool, False{}, Nat.is_lt(x, 0n), True{}, wn.not_lt_zero(x), h1)))
    case 0n 1n+yp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, wn.ft(h2))
    case 0n 1n+yp 1n+zp:
      {==}
    case 1n+xp 1n+yp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 0n) == True{} : Bool}, wn.ft(h2))
    case 1n+xp 1n+yp 1n+zp:
      wn.lt_le_trans(xp, yp, zp, h1, h2)

def wn.le_lt_trans(x: Nat, y: Nat, z: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_lt(y, z) == True{} : Bool}) -> {Nat.is_lt(x, z) == True{} : Bool}:
  match x y z:
    case 0n 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, wn.ft(h2))
    case 0n 0n 1n+zp:
      {==}
    case 0n 1n+yp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, wn.ft(h2))
    case 0n 1n+yp 1n+zp:
      {==}
    case 1n+xp 0n _:
      Empty.absurd({Nat.is_lt(1n+xp, z) == True{} : Bool}, wn.ft(h1))
    case 1n+xp 1n+yp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 0n) == True{} : Bool}, wn.ft(h2))
    case 1n+xp 1n+yp 1n+zp:
      wn.le_lt_trans(xp, yp, zp, h1, h2)

def wn.lt_le(x: Nat, y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_le(x, y) == True{} : Bool}:
  match x y:
    case 0n _:
      wn.le_zero(y)
    case 1n+xp 0n:
      Empty.absurd({Nat.is_le(1n+xp, 0n) == True{} : Bool}, wn.ft(h))
    case 1n+xp 1n+yp:
      wn.lt_le(xp, yp, h)

def wn.le_refl(x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      wn.le_refl(p)

def wn.le_trans(x: Nat, y: Nat, z: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_le(y, z) == True{} : Bool}) -> {Nat.is_le(x, z) == True{} : Bool}:
  match x y z:
    case 0n _ _:
      wn.le_zero(z)
    case 1n+xp 0n _:
      Empty.absurd({Nat.is_le(1n+xp, z) == True{} : Bool}, wn.ft(h1))
    case 1n+xp 1n+yp 0n:
      Empty.absurd({Nat.is_le(1n+xp, 0n) == True{} : Bool}, wn.ft(h2))
    case 1n+xp 1n+yp 1n+zp:
      wn.le_trans(xp, yp, zp, h1, h2)

def wn.le_rw2(-x: Nat, -y: Nat, -y2: Nat, e: {y == y2 : Nat}, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(x, y2) == True{} : Bool}:
  %e : {Nat.is_le(x, _) == True{} : Bool}
  h

def wn.lt_irrefl(x: Nat, h: {Nat.is_lt(x, x) == True{} : Bool}) -> Empty:
  match x:
    case 0n:
      wn.ft(h)
    case 1n+p:
      wn.lt_irrefl(p, h)

# k + x < k + y, k + x <= k + y, cmp(k + x, k + y): as for x and y
def wn.lt_add_l(k: Nat, -x: Nat, -y: Nat) -> {Nat.is_lt(Nat.add(k, x), Nat.add(k, y)) == Nat.is_lt(x, y) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      wn.lt_add_l(p, x, y)

def wn.le_add_l(k: Nat, -x: Nat, -y: Nat) -> {Nat.is_le(Nat.add(k, x), Nat.add(k, y)) == Nat.is_le(x, y) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      wn.le_add_l(p, x, y)

def wn.cmp_add_l(k: Nat, -x: Nat, -y: Nat) -> {Nat.cmp(Nat.add(k, x), Nat.add(k, y)) == Nat.cmp(x, y) : Cmp}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      wn.cmp_add_l(p, x, y)

def wn.lt_add_r(+x: Nat, +y: Nat, +a: Nat) -> {Nat.is_lt(Nat.add(x, a), Nat.add(y, a)) == Nat.is_lt(x, y) : Bool}:
  %wn.add_comm(a, x) : {Nat.is_lt(_, Nat.add(y, a)) == Nat.is_lt(x, y) : Bool}
  %wn.add_comm(a, y) : {Nat.is_lt(Nat.add(a, x), _) == Nat.is_lt(x, y) : Bool}
  wn.lt_add_l(a, x, y)

# x <= x + y and x <= s + x
def wn.le_self_add(x: Nat, +y: Nat) -> {Nat.is_le(x, Nat.add(x, y)) == True{} : Bool}:
  match x:
    case 0n:
      wn.le_zero(y)
    case 1n+p:
      wn.le_self_add(p, y)

def wn.le_add_self(+x: Nat, +s: Nat) -> {Nat.is_le(x, Nat.add(s, x)) == True{} : Bool}:
  %wn.add_comm(x, s) : {Nat.is_le(x, _) == True{} : Bool}
  wn.le_self_add(x, s)

# a < b and c < d: a + c < b + d
def wn.add_lt_mono(+a: Nat, +b: Nat, +c: Nat, +d: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_lt(c, d) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  +s1 = Equal.trans(Bool, Nat.is_lt(Nat.add(a, c), Nat.add(b, c)), Nat.is_lt(a, b), True{}, wn.lt_add_r(a, b, c), h1)
  +s2 = Equal.trans(Bool, Nat.is_le(Nat.add(b, c), Nat.add(b, d)), Nat.is_le(c, d), True{}, wn.le_add_l(b, c, d), wn.lt_le(c, d, h2))
  wn.lt_le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), s1, s2)

# a + b < a never holds, nor s + b < b
def wn.not_lt_add(a: Nat, b: Nat) -> {Nat.is_lt(Nat.add(a, b), a) == False{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      wn.not_lt_add(p, b)

def wn.not_lt_add_l(+s: Nat, +b: Nat) -> {Nat.is_lt(Nat.add(s, b), b) == False{} : Bool}:
  %wn.add_comm(b, s) : {Nat.is_lt(_, b) == False{} : Bool}
  wn.not_lt_add(b, s)

def wn.le_not_lt(b: Nat, a: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.is_lt(a, b) == False{} : Bool}:
  match b a:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(0n, 1n+p) == False{} : Bool}, wn.ft(h))
    case 1n+p 1n+q:
      wn.le_not_lt(p, q, h)

# Nat.cmp from the order

def wn.lt_of(c: Cmp, e: {Cmp.is_lt(c) == True{} : Bool}) -> {c == LT{} : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({EQ{} == LT{} : Cmp}, wn.ft(e))
    case GT{}:
      Empty.absurd({GT{} == LT{} : Cmp}, wn.ft(e))

def wn.cmp_gt(x: Nat, y: Nat, h: {Nat.is_lt(y, x) == True{} : Bool}) -> {Nat.cmp(x, y) == GT{} : Cmp}:
  match x y:
    case 0n 0n:
      Empty.absurd({EQ{} == GT{} : Cmp}, wn.ft(h))
    case 0n 1n+q:
      Empty.absurd({LT{} == GT{} : Cmp}, wn.ft(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      wn.cmp_gt(p, q, h)

def wn.cmp_eq(x: Nat, y: Nat, e: {Nat.cmp(x, y) == EQ{} : Cmp}) -> {x == y : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, wn.lt_eq(e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, wn.gt_eq(e))
    case 1n+p 1n+q:
      wn.succ_cong(p, q, wn.cmp_eq(p, q, e))

def wn.cmp_refl(a: Nat) -> {Nat.cmp(a, a) == EQ{} : Cmp}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      wn.cmp_refl(p)

# The value of a word of two halves

# lo + 2^n * hi
def wv.V(+n: Nat, h: Word(n), l: Word(n)) -> Nat:
  Nat.add(Word.to_nat(n, l), U.U32Nat.dbl(n, Word.to_nat(n, h)))

# x * 2^(2n), the weight of a carry out of the high half
def wv.Q(+n: Nat, x: Nat) -> Nat:
  U.U32Nat.dbl(n, U.U32Nat.dbl(n, x))

# the order of two halves: the high halves, then the low halves
def wv.lex(c: Cmp, d: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      d
    case GT{}:
      GT{}

# a carry as a word: 1 or 0
def wv.bitw(n: Nat, b: Bool) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{b, Word.zero(p)}

def wv.bitw_value(+p: Nat, b: Bool) -> {Word.to_nat(1n+p, wv.bitw(1n+p, b)) == U.U32Nat.bit(b) : Nat}:
  match b:
    case True{}:
      wn.succ_cong(Nat.double(Word.to_nat(p, Word.zero(p))), 0n, Equal.cong(Nat, Nat, v => Nat.double(v), Word.to_nat(p, Word.zero(p)), 0n, UL.word_zero_value(p)))
    case False{}:
      Equal.cong(Nat, Nat, v => Nat.double(v), Word.to_nat(p, Word.zero(p)), 0n, UL.word_zero_value(p))

def wv.q0(+n: Nat) -> {wv.Q(n, 0n) == 0n : Nat}:
  Equal.trans(Nat, U.U32Nat.dbl(n, U.U32Nat.dbl(n, 0n)), U.U32Nat.dbl(n, 0n), 0n, Equal.cong(Nat, Nat, v => U.U32Nat.dbl(n, v), U.U32Nat.dbl(n, 0n), 0n, UL.dbl_zero(n)), UL.dbl_zero(n))

# Q(1 + x) = Q(1) + Q(x)
def wv.qs(+n: Nat, +x: Nat) -> {wv.Q(n, 1n+x) == Nat.add(wv.Q(n, 1n), wv.Q(n, x)) : Nat}:
  Equal.trans(Nat, U.U32Nat.dbl(n, U.U32Nat.dbl(n, 1n+x)), U.U32Nat.dbl(n, Nat.add(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, x))), Nat.add(U.U32Nat.dbl(n, U.U32Nat.dbl(n, 1n)), U.U32Nat.dbl(n, U.U32Nat.dbl(n, x))), Equal.cong(Nat, Nat, v => U.U32Nat.dbl(n, v), U.U32Nat.dbl(n, 1n+x), Nat.add(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, x)), UL.dbl_add(n, 1n, x)), UL.dbl_add(n, U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, x)))

# lo < 2^n and hi < 2^n: lo + 2^n * hi < 2^(2n)
def wv.val_lt2(+n: Nat, +l: Nat, +h: Nat, hl: {Nat.is_lt(l, U.U32Nat.dbl(n, 1n)) == True{} : Bool}, hh: {Nat.is_lt(h, U.U32Nat.dbl(n, 1n)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(l, U.U32Nat.dbl(n, h)), wv.Q(n, 1n)) == True{} : Bool}:
  +k = U.U32Nat.dbl(n, 1n)
  +s1 = Equal.trans(Bool, Nat.is_lt(Nat.add(l, U.U32Nat.dbl(n, h)), Nat.add(k, U.U32Nat.dbl(n, h))), Nat.is_lt(l, k), True{}, wn.lt_add_r(l, k, U.U32Nat.dbl(n, h)), hl)
  +s2 = wn.lt_rw2(Nat.add(l, U.U32Nat.dbl(n, h)), Nat.add(k, U.U32Nat.dbl(n, h)), U.U32Nat.dbl(n, 1n+h), Equal.sym(Nat, U.U32Nat.dbl(n, 1n+h), Nat.add(k, U.U32Nat.dbl(n, h)), UL.dbl_add(n, 1n, h)), s1)
  +s3 = Equal.trans(Bool, Nat.is_le(U.U32Nat.dbl(n, 1n+h), U.U32Nat.dbl(n, k)), Nat.is_le(1n+h, k), True{}, UL.dbl_le(n, 1n+h, k), Equal.trans(Bool, Nat.is_le(1n+h, k), Nat.is_lt(h, k), True{}, wn.le_succ(h, k), hh))
  wn.lt_le_trans(Nat.add(l, U.U32Nat.dbl(n, h)), U.U32Nat.dbl(n, 1n+h), U.U32Nat.dbl(n, k), s2, s3)

# Comparison: the value order is the order of the high halves, then the
# low halves (each half below 2^n)

def wv.ncmp0(+n: Nat, +al: Nat, +bl: Nat) -> {Nat.cmp(Nat.add(al, U.U32Nat.dbl(n, 0n)), Nat.add(bl, U.U32Nat.dbl(n, 0n))) == Nat.cmp(al, bl) : Cmp}:
  %Equal.sym(Nat, U.U32Nat.dbl(n, 0n), 0n, UL.dbl_zero(n)) : {Nat.cmp(Nat.add(al, _), Nat.add(bl, _)) == Nat.cmp(al, bl) : Cmp}
  %Equal.sym(Nat, Nat.add(al, 0n), al, wn.add_zero(al)) : {Nat.cmp(_, Nat.add(bl, 0n)) == Nat.cmp(al, bl) : Cmp}
  %Equal.sym(Nat, Nat.add(bl, 0n), bl, wn.add_zero(bl)) : {Nat.cmp(al, _) == Nat.cmp(al, bl) : Cmp}
  {==}

# al < 2^n <= bl + 2^n * (1 + q)
def wv.nlt(+n: Nat, +al: Nat, +bl: Nat, +q: Nat, hl: {Nat.is_lt(al, U.U32Nat.dbl(n, 1n)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(al, U.U32Nat.dbl(n, 0n)), Nat.add(bl, U.U32Nat.dbl(n, 1n+q))) == True{} : Bool}:
  +k = U.U32Nat.dbl(n, 1n)
  +e0 = Equal.trans(Nat, al, Nat.add(al, 0n), Nat.add(al, U.U32Nat.dbl(n, 0n)), Equal.sym(Nat, Nat.add(al, 0n), al, wn.add_zero(al)), Equal.cong(Nat, Nat, v => Nat.add(al, v), 0n, U.U32Nat.dbl(n, 0n), Equal.sym(Nat, U.U32Nat.dbl(n, 0n), 0n, UL.dbl_zero(n))))
  +s1 = Equal.trans(Bool, Nat.is_le(k, U.U32Nat.dbl(n, 1n+q)), Nat.is_le(1n, 1n+q), True{}, UL.dbl_le(n, 1n, 1n+q), wn.le_zero(q))
  +s2 = wn.lt_le_trans(al, k, U.U32Nat.dbl(n, 1n+q), hl, s1)
  +s3 = wn.lt_le_trans(al, U.U32Nat.dbl(n, 1n+q), Nat.add(bl, U.U32Nat.dbl(n, 1n+q)), s2, wn.le_add_self(U.U32Nat.dbl(n, 1n+q), bl))
  wn.lt_rw(al, Nat.add(al, U.U32Nat.dbl(n, 0n)), Nat.add(bl, U.U32Nat.dbl(n, 1n+q)), e0, s3)

def wv.ncmp(+n: Nat, ah: Nat, bh: Nat, +al: Nat, +bl: Nat, hal: {Nat.is_lt(al, U.U32Nat.dbl(n, 1n)) == True{} : Bool}, hbl: {Nat.is_lt(bl, U.U32Nat.dbl(n, 1n)) == True{} : Bool}) -> {wv.lex(Nat.cmp(ah, bh), Nat.cmp(al, bl)) == Nat.cmp(Nat.add(al, U.U32Nat.dbl(n, ah)), Nat.add(bl, U.U32Nat.dbl(n, bh))) : Cmp}:
  match ah bh:
    case 0n 0n:
      Equal.sym(Cmp, Nat.cmp(Nat.add(al, U.U32Nat.dbl(n, 0n)), Nat.add(bl, U.U32Nat.dbl(n, 0n))), Nat.cmp(al, bl), wv.ncmp0(n, al, bl))
    case 0n 1n+ +q:
      Equal.sym(Cmp, Nat.cmp(Nat.add(al, U.U32Nat.dbl(n, 0n)), Nat.add(bl, U.U32Nat.dbl(n, 1n+q))), LT{}, wn.lt_of(Nat.cmp(Nat.add(al, U.U32Nat.dbl(n, 0n)), Nat.add(bl, U.U32Nat.dbl(n, 1n+q))), wv.nlt(n, al, bl, q, hal)))
    case 1n+ +p 0n:
      Equal.sym(Cmp, Nat.cmp(Nat.add(al, U.U32Nat.dbl(n, 1n+p)), Nat.add(bl, U.U32Nat.dbl(n, 0n))), GT{}, wn.cmp_gt(Nat.add(al, U.U32Nat.dbl(n, 1n+p)), Nat.add(bl, U.U32Nat.dbl(n, 0n)), wv.nlt(n, bl, al, p, hbl)))
    case 1n+ +p 1n+ +q:
      +ea = Equal.trans(Nat, Nat.add(al, U.U32Nat.dbl(n, 1n+p)), Nat.add(al, Nat.add(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, p))), Nat.add(U.U32Nat.dbl(n, 1n), Nat.add(al, U.U32Nat.dbl(n, p))), Equal.cong(Nat, Nat, v => Nat.add(al, v), U.U32Nat.dbl(n, 1n+p), Nat.add(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, p)), UL.dbl_add(n, 1n, p)), wn.left_comm(al, U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, p)))
      +eb = Equal.trans(Nat, Nat.add(bl, U.U32Nat.dbl(n, 1n+q)), Nat.add(bl, Nat.add(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, q))), Nat.add(U.U32Nat.dbl(n, 1n), Nat.add(bl, U.U32Nat.dbl(n, q))), Equal.cong(Nat, Nat, v => Nat.add(bl, v), U.U32Nat.dbl(n, 1n+q), Nat.add(U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, q)), UL.dbl_add(n, 1n, q)), wn.left_comm(bl, U.U32Nat.dbl(n, 1n), U.U32Nat.dbl(n, q)))
      %Equal.sym(Nat, Nat.add(al, U.U32Nat.dbl(n, 1n+p)), Nat.add(U.U32Nat.dbl(n, 1n), Nat.add(al, U.U32Nat.dbl(n, p))), ea) : {wv.lex(Nat.cmp(p, q), Nat.cmp(al, bl)) == Nat.cmp(_, Nat.add(bl, U.U32Nat.dbl(n, 1n+q))) : Cmp}
      %Equal.sym(Nat, Nat.add(bl, U.U32Nat.dbl(n, 1n+q)), Nat.add(U.U32Nat.dbl(n, 1n), Nat.add(bl, U.U32Nat.dbl(n, q))), eb) : {wv.lex(Nat.cmp(p, q), Nat.cmp(al, bl)) == Nat.cmp(Nat.add(U.U32Nat.dbl(n, 1n), Nat.add(al, U.U32Nat.dbl(n, p))), _) : Cmp}
      %Equal.sym(Cmp, Nat.cmp(Nat.add(U.U32Nat.dbl(n, 1n), Nat.add(al, U.U32Nat.dbl(n, p))), Nat.add(U.U32Nat.dbl(n, 1n), Nat.add(bl, U.U32Nat.dbl(n, q)))), Nat.cmp(Nat.add(al, U.U32Nat.dbl(n, p)), Nat.add(bl, U.U32Nat.dbl(n, q))), wn.cmp_add_l(U.U32Nat.dbl(n, 1n), Nat.add(al, U.U32Nat.dbl(n, p)), Nat.add(bl, U.U32Nat.dbl(n, q)))) : {wv.lex(Nat.cmp(p, q), Nat.cmp(al, bl)) == _ : Cmp}
      wv.ncmp(n, p, q, al, bl, hal, hbl)

def wv.gcmp(+n: Nat, +ah: Word(n), +al: Word(n), +bh: Word(n), +bl: Word(n)) -> {wv.lex(Word.cmp(n, ah, bh), Word.cmp(n, al, bl)) == Nat.cmp(wv.V(n, ah, al), wv.V(n, bh, bl)) : Cmp}:
  %Equal.sym(Cmp, Word.cmp(n, ah, bh), Nat.cmp(Word.to_nat(n, ah), Word.to_nat(n, bh)), UL.word_cmp_value(n, ah, bh)) : {wv.lex(_, Word.cmp(n, al, bl)) == Nat.cmp(wv.V(n, ah, al), wv.V(n, bh, bl)) : Cmp}
  %Equal.sym(Cmp, Word.cmp(n, al, bl), Nat.cmp(Word.to_nat(n, al), Word.to_nat(n, bl)), UL.word_cmp_value(n, al, bl)) : {wv.lex(Nat.cmp(Word.to_nat(n, ah), Word.to_nat(n, bh)), _) == Nat.cmp(wv.V(n, ah, al), wv.V(n, bh, bl)) : Cmp}
  wv.ncmp(n, Word.to_nat(n, ah), Word.to_nat(n, bh), Word.to_nat(n, al), Word.to_nat(n, bl), UL.word_value_lt(n, al), UL.word_value_lt(n, bl))

def wv.lex_eq_l(c: Cmp, -d: Cmp, e: {wv.lex(c, d) == EQ{} : Cmp}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, wn.lt_eq(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, wn.gt_eq(e))

def wv.lex_eq_r(c: Cmp, -d: Cmp, e: {wv.lex(c, d) == EQ{} : Cmp}) -> {d == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({d == EQ{} : Cmp}, wn.lt_eq(e))
    case EQ{}:
      e
    case GT{}:
      Empty.absurd({d == EQ{} : Cmp}, wn.gt_eq(e))

# equal values: equal halves
def wv.halves_eq(+n: Nat, +ah: Word(n), +al: Word(n), +bh: Word(n), +bl: Word(n), e: {wv.V(n, ah, al) == wv.V(n, bh, bl) : Nat}) -> {(ah, al) == (bh, bl) : Word(n) & Word(n)}:
  +c = Equal.trans(Cmp, wv.lex(Word.cmp(n, ah, bh), Word.cmp(n, al, bl)), Nat.cmp(wv.V(n, ah, al), wv.V(n, bh, bl)), EQ{}, wv.gcmp(n, ah, al, bh, bl), Equal.trans(Cmp, Nat.cmp(wv.V(n, ah, al), wv.V(n, bh, bl)), Nat.cmp(wv.V(n, bh, bl), wv.V(n, bh, bl)), EQ{}, Equal.cong(Nat, Cmp, v => Nat.cmp(v, wv.V(n, bh, bl)), wv.V(n, ah, al), wv.V(n, bh, bl), e), wn.cmp_refl(wv.V(n, bh, bl))))
  +eh = UL.word_value_eq(n, ah, bh, wn.cmp_eq(Word.to_nat(n, ah), Word.to_nat(n, bh), Equal.trans(Cmp, Nat.cmp(Word.to_nat(n, ah), Word.to_nat(n, bh)), Word.cmp(n, ah, bh), EQ{}, Equal.sym(Cmp, Word.cmp(n, ah, bh), Nat.cmp(Word.to_nat(n, ah), Word.to_nat(n, bh)), UL.word_cmp_value(n, ah, bh)), wv.lex_eq_l(Word.cmp(n, ah, bh), Word.cmp(n, al, bl), c))))
  +el = UL.word_value_eq(n, al, bl, wn.cmp_eq(Word.to_nat(n, al), Word.to_nat(n, bl), Equal.trans(Cmp, Nat.cmp(Word.to_nat(n, al), Word.to_nat(n, bl)), Word.cmp(n, al, bl), EQ{}, Equal.sym(Cmp, Word.cmp(n, al, bl), Nat.cmp(Word.to_nat(n, al), Word.to_nat(n, bl)), UL.word_cmp_value(n, al, bl)), wv.lex_eq_r(Word.cmp(n, ah, bh), Word.cmp(n, al, bl), c))))
  %eh : {(ah, al) == (_, bl) : Word(n) & Word(n)}
  %el : {(ah, al) == (ah, _) : Word(n) & Word(n)}
  {==}

# The carry out of the high half, from the values: s + Q(X) = a + b with
# a, b below Q(1) = 2^(2n) makes X the bit "s < a"; s + b = a + Q(X) with
# s, b below Q(1) makes X the bit "a < b"; with a bound below Q(1) on
# a + b, X is 0.

def wv.q_two(+n: Nat, +y: Nat, +s: Nat, +a: Nat, +b: Nat, ha: {Nat.is_lt(a, wv.Q(n, 1n)) == True{} : Bool}, hb: {Nat.is_lt(b, wv.Q(n, 1n)) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, b), Nat.add(s, wv.Q(n, 2n+y))) == True{} : Bool}:
  +q1 = wv.Q(n, 1n)
  +e2 = Equal.trans(Nat, wv.Q(n, 2n+y), Nat.add(q1, wv.Q(n, 1n+y)), Nat.add(q1, Nat.add(q1, wv.Q(n, y))), wv.qs(n, 1n+y), Equal.cong(Nat, Nat, v => Nat.add(q1, v), wv.Q(n, 1n+y), Nat.add(q1, wv.Q(n, y)), wv.qs(n, y)))
  +s1 = wn.add_lt_mono(a, q1, b, q1, ha, hb)
  +s2 = Equal.trans(Bool, Nat.is_le(Nat.add(q1, q1), Nat.add(q1, Nat.add(q1, wv.Q(n, y)))), Nat.is_le(q1, Nat.add(q1, wv.Q(n, y))), True{}, wn.le_add_l(q1, q1, Nat.add(q1, wv.Q(n, y))), wn.le_self_add(q1, wv.Q(n, y)))
  +s4 = wn.le_trans(Nat.add(q1, q1), Nat.add(q1, Nat.add(q1, wv.Q(n, y))), Nat.add(s, wv.Q(n, 2n+y)), s2, wn.le_trans(Nat.add(q1, Nat.add(q1, wv.Q(n, y))), wv.Q(n, 2n+y), Nat.add(s, wv.Q(n, 2n+y)), wn.le_rw2(Nat.add(q1, Nat.add(q1, wv.Q(n, y))), Nat.add(q1, Nat.add(q1, wv.Q(n, y))), wv.Q(n, 2n+y), Equal.sym(Nat, wv.Q(n, 2n+y), Nat.add(q1, Nat.add(q1, wv.Q(n, y))), e2), wn.le_refl(Nat.add(q1, Nat.add(q1, wv.Q(n, y))))), wn.le_add_self(wv.Q(n, 2n+y), s)))
  wn.lt_le_trans(Nat.add(a, b), Nat.add(q1, q1), Nat.add(s, wv.Q(n, 2n+y)), s1, s4)

def wv.char_add(+n: Nat, x: Nat, +s: Nat, +a: Nat, +b: Nat, e: {Nat.add(s, wv.Q(n, x)) == Nat.add(a, b) : Nat}, ha: {Nat.is_lt(a, wv.Q(n, 1n)) == True{} : Bool}, hb: {Nat.is_lt(b, wv.Q(n, 1n)) == True{} : Bool}) -> {x == U.U32Nat.bit(Nat.is_lt(s, a)) : Nat}:
  match x:
    case 0n:
      +es = Equal.trans(Nat, s, Nat.add(s, 0n), Nat.add(a, b), Equal.sym(Nat, Nat.add(s, 0n), s, wn.add_zero(s)), Equal.trans(Nat, Nat.add(s, 0n), Nat.add(s, wv.Q(n, 0n)), Nat.add(a, b), Equal.cong(Nat, Nat, v => Nat.add(s, v), 0n, wv.Q(n, 0n), Equal.sym(Nat, wv.Q(n, 0n), 0n, wv.q0(n))), e))
      %Equal.sym(Nat, s, Nat.add(a, b), es) : {0n == U.U32Nat.bit(Nat.is_lt(_, a)) : Nat}
      %Equal.sym(Bool, Nat.is_lt(Nat.add(a, b), a), False{}, wn.not_lt_add(a, b)) : {0n == U.U32Nat.bit(_) : Nat}
      {==}
    case 1n+x1:
      match x1:
        case 0n:
          +q1 = wv.Q(n, 1n)
          +h1 = Equal.trans(Bool, Nat.is_lt(Nat.add(a, b), Nat.add(a, q1)), Nat.is_lt(b, q1), True{}, wn.lt_add_l(a, b, q1), hb)
          +h2 = wn.lt_rw(Nat.add(a, b), Nat.add(s, q1), Nat.add(a, q1), Equal.sym(Nat, Nat.add(s, q1), Nat.add(a, b), e), h1)
          +lt = Equal.trans(Bool, Nat.is_lt(s, a), Nat.is_lt(Nat.add(s, q1), Nat.add(a, q1)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(s, q1), Nat.add(a, q1)), Nat.is_lt(s, a), wn.lt_add_r(s, a, q1)), h2)
          %Equal.sym(Bool, Nat.is_lt(s, a), True{}, lt) : {1n == U.U32Nat.bit(_) : Nat}
          {==}
        case 1n+y:
          Empty.absurd({2n+y == U.U32Nat.bit(Nat.is_lt(s, a)) : Nat}, wn.lt_irrefl(Nat.add(a, b), wn.lt_rw2(Nat.add(a, b), Nat.add(s, wv.Q(n, 2n+y)), Nat.add(a, b), e, wv.q_two(n, y, s, a, b, ha, hb))))

def wv.char_sub(+n: Nat, x: Nat, +s: Nat, +a: Nat, +b: Nat, e: {Nat.add(s, b) == Nat.add(a, wv.Q(n, x)) : Nat}, hs: {Nat.is_lt(s, wv.Q(n, 1n)) == True{} : Bool}, hb: {Nat.is_lt(b, wv.Q(n, 1n)) == True{} : Bool}) -> {x == U.U32Nat.bit(Nat.is_lt(a, b)) : Nat}:
  match x:
    case 0n:
      +ea = Equal.trans(Nat, Nat.add(s, b), Nat.add(a, wv.Q(n, 0n)), a, e, Equal.trans(Nat, Nat.add(a, wv.Q(n, 0n)), Nat.add(a, 0n), a, Equal.cong(Nat, Nat, v => Nat.add(a, v), wv.Q(n, 0n), 0n, wv.q0(n)), wn.add_zero(a)))
      %ea : {0n == U.U32Nat.bit(Nat.is_lt(_, b)) : Nat}
      %Equal.sym(Bool, Nat.is_lt(Nat.add(s, b), b), False{}, wn.not_lt_add_l(s, b)) : {0n == U.U32Nat.bit(_) : Nat}
      {==}
    case 1n+x1:
      match x1:
        case 0n:
          +q1 = wv.Q(n, 1n)
          +h1 = Equal.trans(Bool, Nat.is_lt(Nat.add(s, b), Nat.add(q1, b)), Nat.is_lt(s, q1), True{}, wn.lt_add_r(s, q1, b), hs)
          +h2 = wn.lt_rw(Nat.add(s, b), Nat.add(a, q1), Nat.add(q1, b), e, h1)
          +h3 = wn.lt_rw2(Nat.add(a, q1), Nat.add(q1, b), Nat.add(b, q1), wn.add_comm(q1, b), h2)
          +lt = Equal.trans(Bool, Nat.is_lt(a, b), Nat.is_lt(Nat.add(a, q1), Nat.add(b, q1)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(a, q1), Nat.add(b, q1)), Nat.is_lt(a, b), wn.lt_add_r(a, b, q1)), h3)
          %Equal.sym(Bool, Nat.is_lt(a, b), True{}, lt) : {1n == U.U32Nat.bit(_) : Nat}
          {==}
        case 1n+y:
          Empty.absurd({2n+y == U.U32Nat.bit(Nat.is_lt(a, b)) : Nat}, wn.lt_irrefl(Nat.add(s, b), wn.lt_rw2(Nat.add(s, b), Nat.add(a, wv.Q(n, 2n+y)), Nat.add(s, b), Equal.sym(Nat, Nat.add(s, b), Nat.add(a, wv.Q(n, 2n+y)), e), wv.q_two(n, y, a, s, b, hs, hb))))

def wv.nowrap(+n: Nat, x: Nat, +s: Nat, +a: Nat, +b: Nat, +c: Nat, e: {Nat.add(s, wv.Q(n, x)) == Nat.add(a, b) : Nat}, h: {Nat.is_le(Nat.add(a, b), c) == True{} : Bool}, hc: {Nat.is_lt(c, wv.Q(n, 1n)) == True{} : Bool}) -> {s == Nat.add(a, b) : Nat}:
  match x:
    case 0n:
      Equal.trans(Nat, s, Nat.add(s, 0n), Nat.add(a, b), Equal.sym(Nat, Nat.add(s, 0n), s, wn.add_zero(s)), Equal.trans(Nat, Nat.add(s, 0n), Nat.add(s, wv.Q(n, 0n)), Nat.add(a, b), Equal.cong(Nat, Nat, v => Nat.add(s, v), 0n, wv.Q(n, 0n), Equal.sym(Nat, wv.Q(n, 0n), 0n, wv.q0(n))), e))
    case 1n+ +x1:
      +q1 = wv.Q(n, 1n)
      +s1 = wn.le_lt_trans(Nat.add(a, b), c, q1, h, hc)
      +s2 = wn.le_trans(q1, Nat.add(q1, wv.Q(n, x1)), Nat.add(s, wv.Q(n, 1n+x1)), wn.le_self_add(q1, wv.Q(n, x1)), wn.le_rw2(Nat.add(q1, wv.Q(n, x1)), Nat.add(s, Nat.add(q1, wv.Q(n, x1))), Nat.add(s, wv.Q(n, 1n+x1)), Equal.cong(Nat, Nat, v => Nat.add(s, v), Nat.add(q1, wv.Q(n, x1)), wv.Q(n, 1n+x1), Equal.sym(Nat, wv.Q(n, 1n+x1), Nat.add(q1, wv.Q(n, x1)), wv.qs(n, x1))), wn.le_add_self(Nat.add(q1, wv.Q(n, x1)), s)))
      Empty.absurd({s == Nat.add(a, b) : Nat}, wn.lt_irrefl(Nat.add(a, b), wn.lt_rw2(Nat.add(a, b), Nat.add(s, wv.Q(n, 1n+x1)), Nat.add(a, b), e, wn.lt_le_trans(Nat.add(a, b), q1, Nat.add(s, wv.Q(n, 1n+x1)), s1, s2))))

# Addition: the halves with their carries put together

# (l + 2^n h) + 2^n z = l + 2^n (h + z)
def wv.pre(+n: Nat, +l: Nat, +h: Nat, +z: Nat) -> {Nat.add(Nat.add(l, U.U32Nat.dbl(n, h)), U.U32Nat.dbl(n, z)) == Nat.add(l, U.U32Nat.dbl(n, Nat.add(h, z))) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(l, U.U32Nat.dbl(n, h)), U.U32Nat.dbl(n, z)), Nat.add(l, Nat.add(U.U32Nat.dbl(n, h), U.U32Nat.dbl(n, z))), Nat.add(l, U.U32Nat.dbl(n, Nat.add(h, z))), wn.add_assoc(l, U.U32Nat.dbl(n, h), U.U32Nat.dbl(n, z)), Equal.cong(Nat, Nat, v => Nat.add(l, v), Nat.add(U.U32Nat.dbl(n, h), U.U32Nat.dbl(n, z)), U.U32Nat.dbl(n, Nat.add(h, z)), Equal.sym(Nat, U.U32Nat.dbl(n, Nat.add(h, z)), Nat.add(U.U32Nat.dbl(n, h), U.U32Nat.dbl(n, z)), UL.dbl_add(n, h, z))))

def wv.tail(+n: Nat, +cb: Bool, +l: Nat, +y: Nat, +al: Nat, +bl: Nat, +ah: Nat, +bh: Nat, +b1: Nat, e1: {Nat.add(l, U.U32Nat.dbl(n, U.U32Nat.bit(cb))) == Nat.add(al, bl) : Nat}, eb: {b1 == U.U32Nat.bit(cb) : Nat}, ey: {y == Nat.add(Nat.add(ah, bh), b1) : Nat}) -> {Nat.add(l, U.U32Nat.dbl(n, y)) == Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), Nat.add(bl, U.U32Nat.dbl(n, bh))) : Nat}:
  Equal.trans(Nat, Nat.add(l, U.U32Nat.dbl(n, y)), Nat.add(l, U.U32Nat.dbl(n, Nat.add(Nat.add(ah, bh), b1))), Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), Nat.add(bl, U.U32Nat.dbl(n, bh))), Equal.cong(Nat, Nat, v => Nat.add(l, U.U32Nat.dbl(n, v)), y, Nat.add(Nat.add(ah, bh), b1), ey), Equal.trans(Nat, Nat.add(l, U.U32Nat.dbl(n, Nat.add(Nat.add(ah, bh), b1))), Nat.add(l, Nat.add(U.U32Nat.dbl(n, Nat.add(ah, bh)), U.U32Nat.dbl(n, b1))), Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), Nat.add(bl, U.U32Nat.dbl(n, bh))), Equal.cong(Nat, Nat, v => Nat.add(l, v), U.U32Nat.dbl(n, Nat.add(Nat.add(ah, bh), b1)), Nat.add(U.U32Nat.dbl(n, Nat.add(ah, bh)), U.U32Nat.dbl(n, b1)), UL.dbl_add(n, Nat.add(ah, bh), b1)), Equal.trans(Nat, Nat.add(l, Nat.add(U.U32Nat.dbl(n, Nat.add(ah, bh)), U.U32Nat.dbl(n, b1))), Nat.add(l, Nat.add(U.U32Nat.dbl(n, b1), U.U32Nat.dbl(n, Nat.add(ah, bh)))), Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), Nat.add(bl, U.U32Nat.dbl(n, bh))), Equal.cong(Nat, Nat, v => Nat.add(l, v), Nat.add(U.U32Nat.dbl(n, Nat.add(ah, bh)), U.U32Nat.dbl(n, b1)), Nat.add(U.U32Nat.dbl(n, b1), U.U32Nat.dbl(n, Nat.add(ah, bh))), wn.add_comm(U.U32Nat.dbl(n, Nat.add(ah, bh)), U.U32Nat.dbl(n, b1))), Equal.trans(Nat, Nat.add(l, Nat.add(U.U32Nat.dbl(n, b1), U.U32Nat.dbl(n, Nat.add(ah, bh)))), Nat.add(Nat.add(l, U.U32Nat.dbl(n, b1)), U.U32Nat.dbl(n, Nat.add(ah, bh))), Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), Nat.add(bl, U.U32Nat.dbl(n, bh))), Equal.sym(Nat, Nat.add(Nat.add(l, U.U32Nat.dbl(n, b1)), U.U32Nat.dbl(n, Nat.add(ah, bh))), Nat.add(l, Nat.add(U.U32Nat.dbl(n, b1), U.U32Nat.dbl(n, Nat.add(ah, bh)))), wn.add_assoc(l, U.U32Nat.dbl(n, b1), U.U32Nat.dbl(n, Nat.add(ah, bh)))), Equal.trans(Nat, Nat.add(Nat.add(l, U.U32Nat.dbl(n, b1)), U.U32Nat.dbl(n, Nat.add(ah, bh))), Nat.add(Nat.add(l, U.U32Nat.dbl(n, U.U32Nat.bit(cb))), U.U32Nat.dbl(n, Nat.add(ah, bh))), Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), Nat.add(bl, U.U32Nat.dbl(n, bh))), Equal.cong(Nat, Nat, v => Nat.add(Nat.add(l, U.U32Nat.dbl(n, v)), U.U32Nat.dbl(n, Nat.add(ah, bh))), b1, U.U32Nat.bit(cb), eb), Equal.trans(Nat, Nat.add(Nat.add(l, U.U32Nat.dbl(n, U.U32Nat.bit(cb))), U.U32Nat.dbl(n, Nat.add(ah, bh))), Nat.add(Nat.add(al, bl), U.U32Nat.dbl(n, Nat.add(ah, bh))), Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), Nat.add(bl, U.U32Nat.dbl(n, bh))), Equal.cong(Nat, Nat, v => Nat.add(v, U.U32Nat.dbl(n, Nat.add(ah, bh))), Nat.add(l, U.U32Nat.dbl(n, U.U32Nat.bit(cb))), Nat.add(al, bl), e1), Equal.trans(Nat, Nat.add(Nat.add(al, bl), U.U32Nat.dbl(n, Nat.add(ah, bh))), Nat.add(Nat.add(al, bl), Nat.add(U.U32Nat.dbl(n, ah), U.U32Nat.dbl(n, bh))), Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), Nat.add(bl, U.U32Nat.dbl(n, bh))), Equal.cong(Nat, Nat, v => Nat.add(Nat.add(al, bl), v), U.U32Nat.dbl(n, Nat.add(ah, bh)), Nat.add(U.U32Nat.dbl(n, ah), U.U32Nat.dbl(n, bh)), UL.dbl_add(n, ah, bh)), wn.swap_mid(al, bl, U.U32Nat.dbl(n, ah), U.U32Nat.dbl(n, bh)))))))))

def wv.nadd(+n: Nat, +cb: Bool, +c2: Bool, +c3: Bool, +l: Nat, +t: Nat, +h: Nat, +al: Nat, +ah: Nat, +bl: Nat, +bh: Nat, +b1: Nat, e1: {Nat.add(l, U.U32Nat.dbl(n, U.U32Nat.bit(cb))) == Nat.add(al, bl) : Nat}, e2: {Nat.add(t, U.U32Nat.dbl(n, U.U32Nat.bit(c2))) == Nat.add(ah, bh) : Nat}, e3: {Nat.add(h, U.U32Nat.dbl(n, U.U32Nat.bit(c3))) == Nat.add(t, b1) : Nat}, eb: {b1 == U.U32Nat.bit(cb) : Nat}) -> {Nat.add(Nat.add(l, U.U32Nat.dbl(n, h)), wv.Q(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))) == Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), Nat.add(bl, U.U32Nat.dbl(n, bh))) : Nat}:
  +ey = Equal.trans(Nat, Nat.add(h, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), Nat.add(h, Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(c2)), U.U32Nat.dbl(n, U.U32Nat.bit(c3)))), Nat.add(Nat.add(ah, bh), b1), Equal.cong(Nat, Nat, v => Nat.add(h, v), U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3))), Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(c2)), U.U32Nat.dbl(n, U.U32Nat.bit(c3))), UL.dbl_add(n, U.U32Nat.bit(c2), U.U32Nat.bit(c3))), Equal.trans(Nat, Nat.add(h, Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(c2)), U.U32Nat.dbl(n, U.U32Nat.bit(c3)))), Nat.add(h, Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(c3)), U.U32Nat.dbl(n, U.U32Nat.bit(c2)))), Nat.add(Nat.add(ah, bh), b1), Equal.cong(Nat, Nat, v => Nat.add(h, v), Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(c2)), U.U32Nat.dbl(n, U.U32Nat.bit(c3))), Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(c3)), U.U32Nat.dbl(n, U.U32Nat.bit(c2))), wn.add_comm(U.U32Nat.dbl(n, U.U32Nat.bit(c2)), U.U32Nat.dbl(n, U.U32Nat.bit(c3)))), Equal.trans(Nat, Nat.add(h, Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(c3)), U.U32Nat.dbl(n, U.U32Nat.bit(c2)))), Nat.add(Nat.add(h, U.U32Nat.dbl(n, U.U32Nat.bit(c3))), U.U32Nat.dbl(n, U.U32Nat.bit(c2))), Nat.add(Nat.add(ah, bh), b1), Equal.sym(Nat, Nat.add(Nat.add(h, U.U32Nat.dbl(n, U.U32Nat.bit(c3))), U.U32Nat.dbl(n, U.U32Nat.bit(c2))), Nat.add(h, Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(c3)), U.U32Nat.dbl(n, U.U32Nat.bit(c2)))), wn.add_assoc(h, U.U32Nat.dbl(n, U.U32Nat.bit(c3)), U.U32Nat.dbl(n, U.U32Nat.bit(c2)))), Equal.trans(Nat, Nat.add(Nat.add(h, U.U32Nat.dbl(n, U.U32Nat.bit(c3))), U.U32Nat.dbl(n, U.U32Nat.bit(c2))), Nat.add(Nat.add(t, b1), U.U32Nat.dbl(n, U.U32Nat.bit(c2))), Nat.add(Nat.add(ah, bh), b1), Equal.cong(Nat, Nat, v => Nat.add(v, U.U32Nat.dbl(n, U.U32Nat.bit(c2))), Nat.add(h, U.U32Nat.dbl(n, U.U32Nat.bit(c3))), Nat.add(t, b1), e3), Equal.trans(Nat, Nat.add(Nat.add(t, b1), U.U32Nat.dbl(n, U.U32Nat.bit(c2))), Nat.add(Nat.add(t, U.U32Nat.dbl(n, U.U32Nat.bit(c2))), b1), Nat.add(Nat.add(ah, bh), b1), wn.add_swap(t, b1, U.U32Nat.dbl(n, U.U32Nat.bit(c2))), Equal.cong(Nat, Nat, v => Nat.add(v, b1), Nat.add(t, U.U32Nat.dbl(n, U.U32Nat.bit(c2))), Nat.add(ah, bh), e2))))))
  Equal.trans(Nat, Nat.add(Nat.add(l, U.U32Nat.dbl(n, h)), wv.Q(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), Nat.add(l, U.U32Nat.dbl(n, Nat.add(h, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))))), Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), Nat.add(bl, U.U32Nat.dbl(n, bh))), wv.pre(n, l, h, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), wv.tail(n, cb, l, Nat.add(h, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), al, bl, ah, bh, b1, e1, eb, ey))

# Subtraction: the halves with their borrows put together
def wv.nsub(+n: Nat, +cb: Bool, +c2: Bool, +c3: Bool, +l: Nat, +t: Nat, +h: Nat, +al: Nat, +ah: Nat, +bl: Nat, +bh: Nat, +b1: Nat, e1: {Nat.add(l, bl) == Nat.add(al, U.U32Nat.dbl(n, U.U32Nat.bit(cb))) : Nat}, e2: {Nat.add(t, bh) == Nat.add(ah, U.U32Nat.dbl(n, U.U32Nat.bit(c2))) : Nat}, e3: {Nat.add(h, b1) == Nat.add(t, U.U32Nat.dbl(n, U.U32Nat.bit(c3))) : Nat}, eb: {b1 == U.U32Nat.bit(cb) : Nat}) -> {Nat.add(Nat.add(l, U.U32Nat.dbl(n, h)), Nat.add(bl, U.U32Nat.dbl(n, bh))) == Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), wv.Q(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))) : Nat}:
  +ez = Equal.trans(Nat, Nat.add(U.U32Nat.bit(cb), Nat.add(h, bh)), Nat.add(Nat.add(U.U32Nat.bit(cb), h), bh), Nat.add(ah, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), Equal.sym(Nat, Nat.add(Nat.add(U.U32Nat.bit(cb), h), bh), Nat.add(U.U32Nat.bit(cb), Nat.add(h, bh)), wn.add_assoc(U.U32Nat.bit(cb), h, bh)), Equal.trans(Nat, Nat.add(Nat.add(U.U32Nat.bit(cb), h), bh), Nat.add(Nat.add(h, U.U32Nat.bit(cb)), bh), Nat.add(ah, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), Equal.cong(Nat, Nat, v => Nat.add(v, bh), Nat.add(U.U32Nat.bit(cb), h), Nat.add(h, U.U32Nat.bit(cb)), wn.add_comm(U.U32Nat.bit(cb), h)), Equal.trans(Nat, Nat.add(Nat.add(h, U.U32Nat.bit(cb)), bh), Nat.add(Nat.add(h, b1), bh), Nat.add(ah, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), Equal.cong(Nat, Nat, v => Nat.add(Nat.add(h, v), bh), U.U32Nat.bit(cb), b1, Equal.sym(Nat, b1, U.U32Nat.bit(cb), eb)), Equal.trans(Nat, Nat.add(Nat.add(h, b1), bh), Nat.add(Nat.add(t, U.U32Nat.dbl(n, U.U32Nat.bit(c3))), bh), Nat.add(ah, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), Equal.cong(Nat, Nat, v => Nat.add(v, bh), Nat.add(h, b1), Nat.add(t, U.U32Nat.dbl(n, U.U32Nat.bit(c3))), e3), Equal.trans(Nat, Nat.add(Nat.add(t, U.U32Nat.dbl(n, U.U32Nat.bit(c3))), bh), Nat.add(Nat.add(t, bh), U.U32Nat.dbl(n, U.U32Nat.bit(c3))), Nat.add(ah, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), wn.add_swap(t, U.U32Nat.dbl(n, U.U32Nat.bit(c3)), bh), Equal.trans(Nat, Nat.add(Nat.add(t, bh), U.U32Nat.dbl(n, U.U32Nat.bit(c3))), Nat.add(Nat.add(ah, U.U32Nat.dbl(n, U.U32Nat.bit(c2))), U.U32Nat.dbl(n, U.U32Nat.bit(c3))), Nat.add(ah, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), Equal.cong(Nat, Nat, v => Nat.add(v, U.U32Nat.dbl(n, U.U32Nat.bit(c3))), Nat.add(t, bh), Nat.add(ah, U.U32Nat.dbl(n, U.U32Nat.bit(c2))), e2), Equal.trans(Nat, Nat.add(Nat.add(ah, U.U32Nat.dbl(n, U.U32Nat.bit(c2))), U.U32Nat.dbl(n, U.U32Nat.bit(c3))), Nat.add(ah, Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(c2)), U.U32Nat.dbl(n, U.U32Nat.bit(c3)))), Nat.add(ah, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), wn.add_assoc(ah, U.U32Nat.dbl(n, U.U32Nat.bit(c2)), U.U32Nat.dbl(n, U.U32Nat.bit(c3))), Equal.cong(Nat, Nat, v => Nat.add(ah, v), Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(c2)), U.U32Nat.dbl(n, U.U32Nat.bit(c3))), U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3))), Equal.sym(Nat, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3))), Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(c2)), U.U32Nat.dbl(n, U.U32Nat.bit(c3))), UL.dbl_add(n, U.U32Nat.bit(c2), U.U32Nat.bit(c3)))))))))))
  Equal.trans(Nat, Nat.add(Nat.add(l, U.U32Nat.dbl(n, h)), Nat.add(bl, U.U32Nat.dbl(n, bh))), Nat.add(Nat.add(l, bl), Nat.add(U.U32Nat.dbl(n, h), U.U32Nat.dbl(n, bh))), Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), wv.Q(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), wn.swap_mid(l, U.U32Nat.dbl(n, h), bl, U.U32Nat.dbl(n, bh)), Equal.trans(Nat, Nat.add(Nat.add(l, bl), Nat.add(U.U32Nat.dbl(n, h), U.U32Nat.dbl(n, bh))), Nat.add(Nat.add(l, bl), U.U32Nat.dbl(n, Nat.add(h, bh))), Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), wv.Q(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), Equal.cong(Nat, Nat, v => Nat.add(Nat.add(l, bl), v), Nat.add(U.U32Nat.dbl(n, h), U.U32Nat.dbl(n, bh)), U.U32Nat.dbl(n, Nat.add(h, bh)), Equal.sym(Nat, U.U32Nat.dbl(n, Nat.add(h, bh)), Nat.add(U.U32Nat.dbl(n, h), U.U32Nat.dbl(n, bh)), UL.dbl_add(n, h, bh))), Equal.trans(Nat, Nat.add(Nat.add(l, bl), U.U32Nat.dbl(n, Nat.add(h, bh))), Nat.add(Nat.add(al, U.U32Nat.dbl(n, U.U32Nat.bit(cb))), U.U32Nat.dbl(n, Nat.add(h, bh))), Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), wv.Q(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), Equal.cong(Nat, Nat, v => Nat.add(v, U.U32Nat.dbl(n, Nat.add(h, bh))), Nat.add(l, bl), Nat.add(al, U.U32Nat.dbl(n, U.U32Nat.bit(cb))), e1), Equal.trans(Nat, Nat.add(Nat.add(al, U.U32Nat.dbl(n, U.U32Nat.bit(cb))), U.U32Nat.dbl(n, Nat.add(h, bh))), Nat.add(al, Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(cb)), U.U32Nat.dbl(n, Nat.add(h, bh)))), Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), wv.Q(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), wn.add_assoc(al, U.U32Nat.dbl(n, U.U32Nat.bit(cb)), U.U32Nat.dbl(n, Nat.add(h, bh))), Equal.trans(Nat, Nat.add(al, Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(cb)), U.U32Nat.dbl(n, Nat.add(h, bh)))), Nat.add(al, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(cb), Nat.add(h, bh)))), Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), wv.Q(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), Equal.cong(Nat, Nat, v => Nat.add(al, v), Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(cb)), U.U32Nat.dbl(n, Nat.add(h, bh))), U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(cb), Nat.add(h, bh))), Equal.sym(Nat, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(cb), Nat.add(h, bh))), Nat.add(U.U32Nat.dbl(n, U.U32Nat.bit(cb)), U.U32Nat.dbl(n, Nat.add(h, bh))), UL.dbl_add(n, U.U32Nat.bit(cb), Nat.add(h, bh)))), Equal.trans(Nat, Nat.add(al, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(cb), Nat.add(h, bh)))), Nat.add(al, U.U32Nat.dbl(n, Nat.add(ah, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))))), Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), wv.Q(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), Equal.cong(Nat, Nat, v => Nat.add(al, U.U32Nat.dbl(n, v)), Nat.add(U.U32Nat.bit(cb), Nat.add(h, bh)), Nat.add(ah, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), ez), Equal.trans(Nat, Nat.add(al, U.U32Nat.dbl(n, Nat.add(ah, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))))), Nat.add(al, Nat.add(U.U32Nat.dbl(n, ah), U.U32Nat.dbl(n, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))))), Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), wv.Q(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))), Equal.cong(Nat, Nat, v => Nat.add(al, v), U.U32Nat.dbl(n, Nat.add(ah, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3))))), Nat.add(U.U32Nat.dbl(n, ah), U.U32Nat.dbl(n, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3))))), UL.dbl_add(n, ah, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3))))), Equal.sym(Nat, Nat.add(Nat.add(al, U.U32Nat.dbl(n, ah)), U.U32Nat.dbl(n, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3))))), Nat.add(al, Nat.add(U.U32Nat.dbl(n, ah), U.U32Nat.dbl(n, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))))), wn.add_assoc(al, U.U32Nat.dbl(n, ah), U.U32Nat.dbl(n, U.U32Nat.dbl(n, Nat.add(U.U32Nat.bit(c2), U.U32Nat.bit(c3)))))))))))))

# The halves W64.add and W64.sub compute, at width n

def wv.c1add(+n: Nat, +al: Word(n), +bl: Word(n)) -> Bool:
  Cmp.is_lt(Word.cmp(n, Word.add(n, al, bl), al))

def wv.addhi(+n: Nat, +ah: Word(n), +al: Word(n), +bh: Word(n), +bl: Word(n)) -> Word(n):
  Word.add(n, Word.add(n, ah, bh), wv.bitw(n, wv.c1add(n, al, bl)))

def wv.c1sub(+n: Nat, +al: Word(n), +bl: Word(n)) -> Bool:
  Cmp.is_lt(Word.cmp(n, al, bl))

def wv.subhi(+n: Nat, +ah: Word(n), +al: Word(n), +bh: Word(n), +bl: Word(n)) -> Word(n):
  Word.sub(n, Word.sub(n, ah, bh), wv.bitw(n, wv.c1sub(n, al, bl)))

# the value of the sum of two words of two halves, with its carry out
def wv.gadd.go(+n: Nat, +ah: Word(n), +al: Word(n), +bh: Word(n), +bl: Word(n), eb: {Word.to_nat(n, wv.bitw(n, wv.c1add(n, al, bl))) == U.U32Nat.bit(wv.c1add(n, al, bl)) : Nat}) -> {Nat.add(Nat.add(Word.to_nat(n, Word.add(n, al, bl)), U.U32Nat.dbl(n, Word.to_nat(n, wv.addhi(n, ah, al, bh, bl)))), wv.Q(n, Nat.add(U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, ah, bh), ah))), U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, wv.addhi(n, ah, al, bh, bl), Word.add(n, ah, bh))))))) == Nat.add(wv.V(n, ah, al), wv.V(n, bh, bl)) : Nat}:
  +tw = Word.add(n, ah, bh)
  +bw = wv.bitw(n, wv.c1add(n, al, bl))
  wv.nadd(n, wv.c1add(n, al, bl), Cmp.is_lt(Word.cmp(n, tw, ah)), Cmp.is_lt(Word.cmp(n, wv.addhi(n, ah, al, bh, bl), tw)), Word.to_nat(n, Word.add(n, al, bl)), Word.to_nat(n, tw), Word.to_nat(n, wv.addhi(n, ah, al, bh, bl)), Word.to_nat(n, al), Word.to_nat(n, ah), Word.to_nat(n, bl), Word.to_nat(n, bh), Word.to_nat(n, bw), UL.word_add_wrap(n, al, bl), UL.word_add_wrap(n, ah, bh), UL.word_add_wrap(n, tw, bw), eb)

def wv.gadd.sum(+n: Nat, +ah: Word(n), +al: Word(n), +bh: Word(n), +bl: Word(n)) -> {Nat.add(Nat.add(Word.to_nat(n, Word.add(n, al, bl)), U.U32Nat.dbl(n, Word.to_nat(n, wv.addhi(n, ah, al, bh, bl)))), wv.Q(n, Nat.add(U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, ah, bh), ah))), U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, wv.addhi(n, ah, al, bh, bl), Word.add(n, ah, bh))))))) == Nat.add(wv.V(n, ah, al), wv.V(n, bh, bl)) : Nat}:
  match n:
    case 0n:
      match ah al bh bl:
        case WNil{} WNil{} WNil{} WNil{}:
          {==}
    case 1n+ +p:
      wv.gadd.go(1n+p, ah, al, bh, bl, wv.bitw_value(p, wv.c1add(1n+p, al, bl)))

def wv.gsub.go(+n: Nat, +ah: Word(n), +al: Word(n), +bh: Word(n), +bl: Word(n), eb: {Word.to_nat(n, wv.bitw(n, wv.c1sub(n, al, bl))) == U.U32Nat.bit(wv.c1sub(n, al, bl)) : Nat}) -> {Nat.add(Nat.add(Word.to_nat(n, Word.sub(n, al, bl)), U.U32Nat.dbl(n, Word.to_nat(n, wv.subhi(n, ah, al, bh, bl)))), wv.V(n, bh, bl)) == Nat.add(wv.V(n, ah, al), wv.Q(n, Nat.add(U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, ah, bh))), U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.sub(n, ah, bh), wv.bitw(n, wv.c1sub(n, al, bl)))))))) : Nat}:
  +tw = Word.sub(n, ah, bh)
  +bw = wv.bitw(n, wv.c1sub(n, al, bl))
  wv.nsub(n, wv.c1sub(n, al, bl), Cmp.is_lt(Word.cmp(n, ah, bh)), Cmp.is_lt(Word.cmp(n, tw, bw)), Word.to_nat(n, Word.sub(n, al, bl)), Word.to_nat(n, tw), Word.to_nat(n, wv.subhi(n, ah, al, bh, bl)), Word.to_nat(n, al), Word.to_nat(n, ah), Word.to_nat(n, bl), Word.to_nat(n, bh), Word.to_nat(n, bw), UL.word_sub_wrap(n, al, bl), UL.word_sub_wrap(n, ah, bh), UL.word_sub_wrap(n, tw, bw), eb)

def wv.gsub.sum(+n: Nat, +ah: Word(n), +al: Word(n), +bh: Word(n), +bl: Word(n)) -> {Nat.add(Nat.add(Word.to_nat(n, Word.sub(n, al, bl)), U.U32Nat.dbl(n, Word.to_nat(n, wv.subhi(n, ah, al, bh, bl)))), wv.V(n, bh, bl)) == Nat.add(wv.V(n, ah, al), wv.Q(n, Nat.add(U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, ah, bh))), U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.sub(n, ah, bh), wv.bitw(n, wv.c1sub(n, al, bl)))))))) : Nat}:
  match n:
    case 0n:
      match ah al bh bl:
        case WNil{} WNil{} WNil{} WNil{}:
          {==}
    case 1n+ +p:
      wv.gsub.go(1n+p, ah, al, bh, bl, wv.bitw_value(p, wv.c1sub(1n+p, al, bl)))

# W64.add at width n: the sum of the values, less 2^(2n) when it wraps,
# which is when the result is below the first operand
def wv.gadd(+n: Nat, +ah: Word(n), +al: Word(n), +bh: Word(n), +bl: Word(n)) -> {Nat.add(Nat.add(Word.to_nat(n, Word.add(n, al, bl)), U.U32Nat.dbl(n, Word.to_nat(n, wv.addhi(n, ah, al, bh, bl)))), wv.Q(n, U.U32Nat.bit(Nat.is_lt(Nat.add(Word.to_nat(n, Word.add(n, al, bl)), U.U32Nat.dbl(n, Word.to_nat(n, wv.addhi(n, ah, al, bh, bl)))), wv.V(n, ah, al))))) == Nat.add(wv.V(n, ah, al), wv.V(n, bh, bl)) : Nat}:
  +ha = wv.val_lt2(n, Word.to_nat(n, al), Word.to_nat(n, ah), UL.word_value_lt(n, al), UL.word_value_lt(n, ah))
  +hb = wv.val_lt2(n, Word.to_nat(n, bl), Word.to_nat(n, bh), UL.word_value_lt(n, bl), UL.word_value_lt(n, bh))
  +ch = wv.char_add(n, Nat.add(U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, ah, bh), ah))), U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, wv.addhi(n, ah, al, bh, bl), Word.add(n, ah, bh))))), Nat.add(Word.to_nat(n, Word.add(n, al, bl)), U.U32Nat.dbl(n, Word.to_nat(n, wv.addhi(n, ah, al, bh, bl)))), wv.V(n, ah, al), wv.V(n, bh, bl), wv.gadd.sum(n, ah, al, bh, bl), ha, hb)
  %ch : {Nat.add(Nat.add(Word.to_nat(n, Word.add(n, al, bl)), U.U32Nat.dbl(n, Word.to_nat(n, wv.addhi(n, ah, al, bh, bl)))), wv.Q(n, _)) == Nat.add(wv.V(n, ah, al), wv.V(n, bh, bl)) : Nat}
  wv.gadd.sum(n, ah, al, bh, bl)

# with the sum no more than another word's value, nothing wraps
def wv.gadd_nowrap(+n: Nat, +ah: Word(n), +al: Word(n), +bh: Word(n), +bl: Word(n), +ch: Word(n), +cl: Word(n), h: {Nat.is_le(Nat.add(wv.V(n, ah, al), wv.V(n, bh, bl)), wv.V(n, ch, cl)) == True{} : Bool}) -> {Nat.add(Word.to_nat(n, Word.add(n, al, bl)), U.U32Nat.dbl(n, Word.to_nat(n, wv.addhi(n, ah, al, bh, bl)))) == Nat.add(wv.V(n, ah, al), wv.V(n, bh, bl)) : Nat}:
  wv.nowrap(n, Nat.add(U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.add(n, ah, bh), ah))), U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, wv.addhi(n, ah, al, bh, bl), Word.add(n, ah, bh))))), Nat.add(Word.to_nat(n, Word.add(n, al, bl)), U.U32Nat.dbl(n, Word.to_nat(n, wv.addhi(n, ah, al, bh, bl)))), wv.V(n, ah, al), wv.V(n, bh, bl), wv.V(n, ch, cl), wv.gadd.sum(n, ah, al, bh, bl), h, wv.val_lt2(n, Word.to_nat(n, cl), Word.to_nat(n, ch), UL.word_value_lt(n, cl), UL.word_value_lt(n, ch)))

# W64.sub at width n: the difference plus the subtrahend is the minuend,
# plus 2^(2n) when the subtrahend is the larger
def wv.gsub(+n: Nat, +ah: Word(n), +al: Word(n), +bh: Word(n), +bl: Word(n)) -> {Nat.add(Nat.add(Word.to_nat(n, Word.sub(n, al, bl)), U.U32Nat.dbl(n, Word.to_nat(n, wv.subhi(n, ah, al, bh, bl)))), wv.V(n, bh, bl)) == Nat.add(wv.V(n, ah, al), wv.Q(n, U.U32Nat.bit(Nat.is_lt(wv.V(n, ah, al), wv.V(n, bh, bl))))) : Nat}:
  +hs = wv.val_lt2(n, Word.to_nat(n, Word.sub(n, al, bl)), Word.to_nat(n, wv.subhi(n, ah, al, bh, bl)), UL.word_value_lt(n, Word.sub(n, al, bl)), UL.word_value_lt(n, wv.subhi(n, ah, al, bh, bl)))
  +hb = wv.val_lt2(n, Word.to_nat(n, bl), Word.to_nat(n, bh), UL.word_value_lt(n, bl), UL.word_value_lt(n, bh))
  +ch = wv.char_sub(n, Nat.add(U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, ah, bh))), U.U32Nat.bit(Cmp.is_lt(Word.cmp(n, Word.sub(n, ah, bh), wv.bitw(n, wv.c1sub(n, al, bl)))))), Nat.add(Word.to_nat(n, Word.sub(n, al, bl)), U.U32Nat.dbl(n, Word.to_nat(n, wv.subhi(n, ah, al, bh, bl)))), wv.V(n, ah, al), wv.V(n, bh, bl), wv.gsub.sum(n, ah, al, bh, bl), hs, hb)
  %ch : {Nat.add(Nat.add(Word.to_nat(n, Word.sub(n, al, bl)), U.U32Nat.dbl(n, Word.to_nat(n, wv.subhi(n, ah, al, bh, bl)))), wv.V(n, bh, bl)) == Nat.add(wv.V(n, ah, al), wv.Q(n, _)) : Nat}
  wv.gsub.sum(n, ah, al, bh, bl)
