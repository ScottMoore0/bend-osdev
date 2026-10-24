# Lemmas for the Internet checksum's one's complement arithmetic
# (LAWS_sum.bend), written by ref/gen_sum.py: run `python3 ref/gen_sum.py`
# in this directory. They prove no law.
#
# How the proofs go. A 16-bit one's complement sum of t ones is modelled on
# Nat by os.rep(d, t) (d = 2^16 - 1): counting up from 0, a value below d
# steps to its successor and d steps to 1, the end-around carry. Then
# folding early changes nothing (os.rep_fold: rep(rep(x) + y) = rep(x + y))
# and d more ones go once round the cycle (os.rep_period), so every order of
# summing gives the same value. The bridge (os.add_value) shows that
# K.inet_add on two values of at most d computes rep of their sum: the U32
# sum s does not wrap, splits as lo + 2^16 hi with hi 0 or 1 (the mask and
# the shift by 16 read those halves), and lo + hi is rep(s). The sum of a
# byte list is then rep of the plain sum of its 16-bit words (os.fold), and
# the checksum c of a sum S satisfies c + S = d (os.finish_value), so the
# data with c in it sums to rep(S + c) = rep(d) = d.
#
# d is never computed: the lemmas take it as a variable with the facts
# 1 + d = 2^16 (UN.U32Nat.dbl(16n, 1n)) and d = U32.to_nat(65535), and only
# the laws' proofs instantiate it, with the facts proved without expanding
# the number (os.hD, os.hE). A closed 2^16 is a unary Nat in the checkers.
import Base
import ../u32/u32.bend as UN
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./checksum.bend as K

# Contradictions

def os.bt(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def os.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : os.bt(_)
  Unit{}

def os.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : os.bt(_)
  Unit{}

# Nat: successor, addition

def os.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+ +p:
      p

def os.succ_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def os.succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, z => os.pred(z), 1n+a, 1n+b, e)

def os.add_zero(x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      os.succ_cong(Nat.add(p, 0n), p, os.add_zero(p))

def os.add_succ(x: Nat, -y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      os.succ_cong(Nat.add(p, 1n+y), 1n+Nat.add(p, y), os.add_succ(p, y))

def os.add_comm(x: Nat, +y: Nat) -> {Nat.add(x, y) == Nat.add(y, x) : Nat}:
  match x:
    case 0n:
      Equal.sym(Nat, Nat.add(y, 0n), y, os.add_zero(y))
    case 1n+ +p:
      Equal.trans(Nat, 1n+Nat.add(p, y), 1n+Nat.add(y, p), Nat.add(y, 1n+p), os.succ_cong(Nat.add(p, y), Nat.add(y, p), os.add_comm(p, y)), Equal.sym(Nat, Nat.add(y, 1n+p), 1n+Nat.add(y, p), os.add_succ(y, p)))

def os.add_assoc(x: Nat, -y: Nat, -z: Nat) -> {Nat.add(Nat.add(x, y), z) == Nat.add(x, Nat.add(y, z)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      os.succ_cong(Nat.add(Nat.add(p, y), z), Nat.add(p, Nat.add(y, z)), os.add_assoc(p, y, z))

def os.double_add(x: Nat, -y: Nat) -> {Nat.double(Nat.add(x, y)) == Nat.add(Nat.double(x), Nat.double(y)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      os.succ_cong(1n+Nat.double(Nat.add(p, y)), 1n+Nat.add(Nat.double(p), Nat.double(y)), os.succ_cong(Nat.double(Nat.add(p, y)), Nat.add(Nat.double(p), Nat.double(y)), os.double_add(p, y)))

def os.sub_zero(x: Nat) -> {Nat.sub(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      {==}

# (r + y) - y = r
def os.sub_add(+r: Nat, y: Nat) -> {Nat.sub(Nat.add(r, y), y) == r : Nat}:
  match y:
    case 0n:
      %Equal.sym(Nat, Nat.add(r, 0n), r, os.add_zero(r)) : {Nat.sub(_, 0n) == r : Nat}
      os.sub_zero(r)
    case 1n+ +q:
      %Equal.sym(Nat, Nat.add(r, 1n+q), 1n+Nat.add(r, q), os.add_succ(r, q)) : {Nat.sub(_, 1n+q) == r : Nat}
      os.sub_add(r, q)

# Order

def os.le_zero(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      {==}

def os.le_refl(x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      os.le_refl(p)

def os.eq_refl(x: Nat) -> {Nat.is_eq(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      os.eq_refl(p)

# 1 + x <= y: x <= y
def os.le_pred(x: Nat, y: Nat, h: {Nat.is_le(1n+x, y) == True{} : Bool}) -> {Nat.is_le(x, y) == True{} : Bool}:
  match x y:
    case 0n _:
      os.le_zero(y)
    case 1n+ +xp 0n:
      Empty.absurd({Nat.is_le(1n+xp, 0n) == True{} : Bool}, os.ft(h))
    case 1n+ +xp 1n+ +yp:
      os.le_pred(xp, yp, h)

# 1 + x <= y: x is not y
def os.le_succ_ne(x: Nat, y: Nat, h: {Nat.is_le(1n+x, y) == True{} : Bool}) -> {Nat.is_eq(x, y) == False{} : Bool}:
  match x y:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, os.ft(h))
    case 0n 1n+ +yp:
      {==}
    case 1n+ +xp 0n:
      {==}
    case 1n+ +xp 1n+ +yp:
      os.le_succ_ne(xp, yp, h)

# x <= y and x is not y: 1 + x <= y
def os.le_ne_succ(x: Nat, y: Nat, h: {Nat.is_le(x, y) == True{} : Bool}, n: {Nat.is_eq(x, y) == False{} : Bool}) -> {Nat.is_le(1n+x, y) == True{} : Bool}:
  match x y:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, os.tf(n))
    case 0n 1n+ +yp:
      os.le_zero(yp)
    case 1n+ +xp 0n:
      Empty.absurd({Nat.is_le(2n+xp, 0n) == True{} : Bool}, os.ft(h))
    case 1n+ +xp 1n+ +yp:
      os.le_ne_succ(xp, yp, h, n)

def os.le_trans(x: Nat, y: Nat, z: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_le(y, z) == True{} : Bool}) -> {Nat.is_le(x, z) == True{} : Bool}:
  match x y z:
    case 0n _ _:
      os.le_zero(z)
    case 1n+ +xp 0n _:
      Empty.absurd({Nat.is_le(1n+xp, z) == True{} : Bool}, os.ft(h1))
    case 1n+ +xp 1n+ +yp 0n:
      Empty.absurd({Nat.is_le(1n+xp, 0n) == True{} : Bool}, os.ft(h2))
    case 1n+ +xp 1n+ +yp 1n+ +zp:
      os.le_trans(xp, yp, zp, h1, h2)

def os.le_succ_r(x: Nat) -> {Nat.is_le(x, 1n+x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      os.le_succ_r(p)

# x <= x + y... b <= a + b
def os.le_add_l(a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      os.le_refl(b)
    case 1n+ +p:
      os.le_trans(b, Nat.add(p, b), 1n+Nat.add(p, b), os.le_add_l(p, b), os.le_succ_r(Nat.add(p, b)))


# a + b <= c + d when a <= c and b <= d
def os.le_add_mono(a: Nat, +b: Nat, c: Nat, +d: Nat, h1: {Nat.is_le(a, c) == True{} : Bool}, h2: {Nat.is_le(b, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), Nat.add(c, d)) == True{} : Bool}:
  match a c:
    case 0n 0n:
      h2
    case 0n 1n+ +cp:
      os.le_trans(b, d, Nat.add(1n+cp, d), h2, os.le_add_l(1n+cp, d))
    case 1n+ +ap 0n:
      Empty.absurd({Nat.is_le(Nat.add(1n+ap, b), d) == True{} : Bool}, os.ft(h1))
    case 1n+ +ap 1n+ +cp:
      os.le_add_mono(ap, b, cp, d, h1, h2)

# k + a <= k + b is a <= b
def os.le_cancel_l(k: Nat, -a: Nat, -b: Nat) -> {Nat.is_le(Nat.add(k, a), Nat.add(k, b)) == Nat.is_le(a, b) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      os.le_cancel_l(p, a, b)

# 1 + x <= x never holds
def os.succ_le_absurd(x: Nat, h: {Nat.is_le(1n+x, x) == True{} : Bool}) -> Empty:
  match x:
    case 0n:
      os.ft(h)
    case 1n+ +p:
      os.succ_le_absurd(p, h)

def os.lt_zero(x: Nat) -> {Nat.is_lt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      {==}

# x < 1 + y is x <= y
def os.lt_succ(x: Nat, y: Nat) -> {Nat.is_lt(x, 1n+y) == Nat.is_le(x, y) : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+ +yp:
      {==}
    case 1n+ +xp 0n:
      os.lt_zero(xp)
    case 1n+ +xp 1n+ +yp:
      os.lt_succ(xp, yp)

# x <= y is not y < x... is_le(x, y) == False: y < x, as 1 + y <= x
def os.not_le(x: Nat, y: Nat, h: {Nat.is_le(x, y) == False{} : Bool}) -> {Nat.is_le(1n+y, x) == True{} : Bool}:
  match x y:
    case 0n _:
      Empty.absurd({Nat.is_le(1n+y, 0n) == True{} : Bool}, os.tf(Equal.trans(Bool, True{}, Nat.is_le(0n, y), False{}, Equal.sym(Bool, Nat.is_le(0n, y), True{}, os.le_zero(y)), h)))
    case 1n+ +xp 0n:
      os.le_zero(xp)
    case 1n+ +xp 1n+ +yp:
      os.not_le(xp, yp, h)

# X not at most d: X = (1 + (X - (1 + d))) + d
def os.sub_split(X: Nat, d: Nat, h: {Nat.is_le(X, d) == False{} : Bool}) -> {X == Nat.add(1n+Nat.sub(X, 1n+d), d) : Nat}:
  match X d:
    case 0n _:
      Empty.absurd({0n == Nat.add(1n+Nat.sub(0n, 1n+d), d) : Nat}, os.tf(Equal.trans(Bool, True{}, Nat.is_le(0n, d), False{}, Equal.sym(Bool, Nat.is_le(0n, d), True{}, os.le_zero(d)), h)))
    case 1n+ +xp 0n:
      %Equal.sym(Nat, Nat.add(1n+Nat.sub(xp, 0n), 0n), 1n+Nat.sub(xp, 0n), os.add_zero(1n+Nat.sub(xp, 0n))) : {1n+xp == _ : Nat}
      %Equal.sym(Nat, Nat.sub(xp, 0n), xp, os.sub_zero(xp)) : {1n+xp == 1n+_ : Nat}
      {==}
    case 1n+ +xp 1n+ +dp:
      %Equal.sym(Nat, Nat.add(1n+Nat.sub(xp, 1n+dp), 1n+dp), 1n+Nat.add(1n+Nat.sub(xp, 1n+dp), dp), os.add_succ(1n+Nat.sub(xp, 1n+dp), dp)) : {1n+xp == _ : Nat}
      os.succ_cong(xp, Nat.add(1n+Nat.sub(xp, 1n+dp), dp), os.sub_split(xp, dp, h))

# The one's complement model: values 0 .. d (d = 2^16 - 1 for the checksum),
# rep(d, t) the one's complement sum of t ones. Counting up from 0, a value
# below d steps to its successor and d steps to 1 (the end-around carry), so
# 0 is reached only by t = 0 and the values cycle 1 .. d.

def os.next.go(top: Bool, x: Nat) -> Nat:
  match top:
    case True{}:
      1n
    case False{}:
      1n+x

def os.next(d: Nat, +x: Nat) -> Nat:
  os.next.go(Nat.is_eq(x, d), x)

def os.rep(+d: Nat, t: Nat) -> Nat:
  match t:
    case 0n:
      0n
    case 1n+ +p:
      os.next(d, os.rep(d, p))

# k <= d: rep(d, k) = k
def os.rep_small(+d: Nat, k: Nat, +h: {Nat.is_le(k, d) == True{} : Bool}) -> {os.rep(d, k) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      %Equal.sym(Nat, os.rep(d, p), p, os.rep_small(d, p, os.le_pred(p, d, h))) : {os.next(d, _) == 1n+p : Nat}
      %Equal.sym(Bool, Nat.is_eq(p, d), False{}, os.le_succ_ne(p, d, h)) : {os.next.go(_, p) == 1n+p : Nat}
      {==}

def os.next_le.go(b: Bool, +d: Nat, +x: Nat, e: {Nat.is_eq(x, d) == b : Bool}, hx: {Nat.is_le(x, d) == True{} : Bool}, hd: {Nat.is_le(1n, d) == True{} : Bool}) -> {Nat.is_le(os.next.go(b, x), d) == True{} : Bool}:
  match b:
    case True{}:
      hd
    case False{}:
      os.le_ne_succ(x, d, hx, e)

def os.next_le(+d: Nat, +x: Nat, hx: {Nat.is_le(x, d) == True{} : Bool}, hd: {Nat.is_le(1n, d) == True{} : Bool}) -> {Nat.is_le(os.next(d, x), d) == True{} : Bool}:
  os.next_le.go(Nat.is_eq(x, d), d, x, {==}, hx, hd)

# every sum is at most d
def os.rep_le(+d: Nat, t: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}) -> {Nat.is_le(os.rep(d, t), d) == True{} : Bool}:
  match t:
    case 0n:
      os.le_zero(d)
    case 1n+ +p:
      os.next_le(d, os.rep(d, p), os.rep_le(d, p, hd), hd)

# rep(d, rep(d, x) + y) = rep(d, x + y): folding early changes nothing
def os.rep_fold(+d: Nat, +x: Nat, y: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}) -> {os.rep(d, Nat.add(os.rep(d, x), y)) == os.rep(d, Nat.add(x, y)) : Nat}:
  match y:
    case 0n:
      %Equal.sym(Nat, Nat.add(os.rep(d, x), 0n), os.rep(d, x), os.add_zero(os.rep(d, x))) : {os.rep(d, _) == os.rep(d, Nat.add(x, 0n)) : Nat}
      %Equal.sym(Nat, Nat.add(x, 0n), x, os.add_zero(x)) : {os.rep(d, os.rep(d, x)) == os.rep(d, _) : Nat}
      os.rep_small(d, os.rep(d, x), os.rep_le(d, x, hd))
    case 1n+ +q:
      %Equal.sym(Nat, Nat.add(os.rep(d, x), 1n+q), 1n+Nat.add(os.rep(d, x), q), os.add_succ(os.rep(d, x), q)) : {os.rep(d, _) == os.rep(d, Nat.add(x, 1n+q)) : Nat}
      %Equal.sym(Nat, Nat.add(x, 1n+q), 1n+Nat.add(x, q), os.add_succ(x, q)) : {os.rep(d, 1n+Nat.add(os.rep(d, x), q)) == os.rep(d, _) : Nat}
      %Equal.sym(Nat, os.rep(d, Nat.add(os.rep(d, x), q)), os.rep(d, Nat.add(x, q)), os.rep_fold(d, x, q, hd)) : {os.next(d, _) == os.next(d, os.rep(d, Nat.add(x, q))) : Nat}
      {==}

# 1 <= d: rep(d, 1) = 1
def os.rep_one(d: Nat, hd: {Nat.is_le(1n, d) == True{} : Bool}) -> {os.rep(d, 1n) == 1n : Nat}:
  match d:
    case 0n:
      Empty.absurd({os.rep(0n, 1n) == 1n : Nat}, os.ft(hd))
    case 1n+ +p:
      {==}

# rep(d, (1 + y) + d) = rep(d, 1 + y): d more ones go once round the cycle
def os.rep_period1(+d: Nat, y: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}) -> {os.rep(d, Nat.add(1n+y, d)) == os.rep(d, 1n+y) : Nat}:
  match y:
    case 0n:
      %Equal.sym(Nat, os.rep(d, d), d, os.rep_small(d, d, os.le_refl(d))) : {os.next(d, _) == os.rep(d, 1n) : Nat}
      %Equal.sym(Bool, Nat.is_eq(d, d), True{}, os.eq_refl(d)) : {os.next.go(_, d) == os.rep(d, 1n) : Nat}
      Equal.sym(Nat, os.rep(d, 1n), 1n, os.rep_one(d, hd))
    case 1n+ +q:
      %Equal.sym(Nat, os.rep(d, Nat.add(1n+q, d)), os.rep(d, 1n+q), os.rep_period1(d, q, hd)) : {os.next(d, _) == os.next(d, os.rep(d, 1n+q)) : Nat}
      {==}

def os.rep_period(+d: Nat, x: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, hx: {Nat.is_le(1n, x) == True{} : Bool}) -> {os.rep(d, Nat.add(x, d)) == os.rep(d, x) : Nat}:
  match x:
    case 0n:
      Empty.absurd({os.rep(d, Nat.add(0n, d)) == os.rep(d, 0n) : Nat}, os.ft(hx))
    case 1n+ +y:
      os.rep_period1(d, y, hd)

# More order facts

# a <= a + b
def os.le_add_r(a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      os.le_zero(b)
    case 1n+ +p:
      os.le_add_r(p, b)

# x <= y < z: x < z
def os.le_lt(x: Nat, y: Nat, z: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_lt(y, z) == True{} : Bool}) -> {Nat.is_lt(x, z) == True{} : Bool}:
  match x y z:
    case 0n 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, os.ft(h2))
    case 0n 0n 1n+ +zp:
      {==}
    case 0n 1n+ +yp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, os.ft(h2))
    case 0n 1n+ +yp 1n+ +zp:
      {==}
    case 1n+ +xp 0n _:
      Empty.absurd({Nat.is_lt(1n+xp, z) == True{} : Bool}, os.ft(h1))
    case 1n+ +xp 1n+ +yp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 0n) == True{} : Bool}, os.ft(h2))
    case 1n+ +xp 1n+ +yp 1n+ +zp:
      os.le_lt(xp, yp, zp, h1, h2)

# x < 1: x = 0
def os.lt_one(x: Nat, h: {Nat.is_lt(x, 1n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      Empty.absurd({1n+p == 0n : Nat}, os.tf(Equal.trans(Bool, True{}, Nat.is_lt(p, 0n), False{}, Equal.sym(Bool, Nat.is_lt(p, 0n), True{}, h), os.lt_zero(p))))

def os.le_double(x: Nat) -> {Nat.is_le(x, Nat.double(x)) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      os.le_trans(p, Nat.double(p), 1n+Nat.double(p), os.le_double(p), os.le_succ_r(Nat.double(p)))

# x <= x * 2^n
def os.le_dbl(n: Nat, +x: Nat) -> {Nat.is_le(x, UN.U32Nat.dbl(n, x)) == True{} : Bool}:
  match n:
    case 0n:
      os.le_refl(x)
    case 1n+ +p:
      os.le_trans(x, UN.U32Nat.dbl(p, x), Nat.double(UN.U32Nat.dbl(p, x)), os.le_dbl(p, x), os.le_double(UN.U32Nat.dbl(p, x)))

# Words: the value of two halves joined, x = lo + 2^m hi

def os.cat_value(m: Nat, +n: Nat, a: Word(m), +b: Word(n)) -> {Word.to_nat(Nat.add(m, n), W.W64.bits.cat(m, n, a, b)) == Nat.add(Word.to_nat(m, a), UN.U32Nat.dbl(m, Word.to_nat(n, b))) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+ +p:
      match a:
        case WCon{False{}, +t}:
          %Equal.sym(Nat, Word.to_nat(Nat.add(p, n), W.W64.bits.cat(p, n, t, b)), Nat.add(Word.to_nat(p, t), UN.U32Nat.dbl(p, Word.to_nat(n, b))), os.cat_value(p, n, t, b)) : {Nat.double(_) == Nat.add(Nat.double(Word.to_nat(p, t)), Nat.double(UN.U32Nat.dbl(p, Word.to_nat(n, b)))) : Nat}
          os.double_add(Word.to_nat(p, t), UN.U32Nat.dbl(p, Word.to_nat(n, b)))
        case WCon{True{}, +t}:
          %Equal.sym(Nat, Word.to_nat(Nat.add(p, n), W.W64.bits.cat(p, n, t, b)), Nat.add(Word.to_nat(p, t), UN.U32Nat.dbl(p, Word.to_nat(n, b))), os.cat_value(p, n, t, b)) : {1n+Nat.double(_) == 1n+Nat.add(Nat.double(Word.to_nat(p, t)), Nat.double(UN.U32Nat.dbl(p, Word.to_nat(n, b)))) : Nat}
          os.succ_cong(Nat.double(Nat.add(Word.to_nat(p, t), UN.U32Nat.dbl(p, Word.to_nat(n, b)))), Nat.add(Nat.double(Word.to_nat(p, t)), Nat.double(UN.U32Nat.dbl(p, Word.to_nat(n, b)))), os.double_add(Word.to_nat(p, t), UN.U32Nat.dbl(p, Word.to_nat(n, b))))

# a U32 from its low and high 16 bits
def os.mk(a: Word(16n), b: Word(16n)) -> U32:
  U32{W.W64.bits.cat(16n, 16n, a, b)}

def os.lo16(s: U32) -> Word(16n):
  match s:
    case U32{w}:
      W.W64.bits.lo(16n, 16n, w)

def os.hi16(s: U32) -> Word(16n):
  match s:
    case U32{w}:
      W.W64.bits.hi(16n, 16n, w)

def os.ones16() -> Word(16n):
  Word.not(16n, Word.zero(16n))

def os.mk_value(a: Word(16n), b: Word(16n)) -> {U32.to_nat(os.mk(a, b)) == Nat.add(Word.to_nat(16n, a), UN.U32Nat.dbl(16n, Word.to_nat(16n, b))) : Nat}:
  os.cat_value(16n, 16n, a, b)

def os.mk_zero_value(+a: Word(16n)) -> {U32.to_nat(os.mk(a, Word.zero(16n))) == Word.to_nat(16n, a) : Nat}:
  %Equal.sym(Nat, U32.to_nat(os.mk(a, Word.zero(16n))), Nat.add(Word.to_nat(16n, a), UN.U32Nat.dbl(16n, Word.to_nat(16n, Word.zero(16n)))), os.mk_value(a, Word.zero(16n))) : {_ == Word.to_nat(16n, a) : Nat}
  %Equal.sym(Nat, Word.to_nat(16n, Word.zero(16n)), 0n, UL.word_zero_value(16n)) : {Nat.add(Word.to_nat(16n, a), UN.U32Nat.dbl(16n, _)) == Word.to_nat(16n, a) : Nat}
  %Equal.sym(Nat, UN.U32Nat.dbl(16n, 0n), 0n, UL.dbl_zero(16n)) : {Nat.add(Word.to_nat(16n, a), _) == Word.to_nat(16n, a) : Nat}
  os.add_zero(Word.to_nat(16n, a))

def os.and_comm_w(n: Nat, a: Word(n), b: Word(n)) -> {Word.and(n, a, b) == Word.and(n, b, a) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          %os.and_comm_w(p, at, bt) : {WCon{False{}, Word.and(p, at, bt)} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt}:
          %os.and_comm_w(p, at, bt) : {WCon{False{}, Word.and(p, at, bt)} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{False{}, +bt}:
          %os.and_comm_w(p, at, bt) : {WCon{False{}, Word.and(p, at, bt)} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case WCon{True{}, +at} WCon{True{}, +bt}:
          %os.and_comm_w(p, at, bt) : {WCon{True{}, Word.and(p, at, bt)} == WCon{True{}, _} : Word(1n+p)}
          {==}

def os.and_comm(a: U32, b: U32) -> {U32.and(a, b) == U32.and(b, a) : U32}:
  match a b:
    case U32{+x} U32{+y}:
      %os.and_comm_w(32n, x, y) : {U32{Word.and(32n, x, y)} == U32{_} : U32}
      {==}

# Splitting a word into its 16-bit halves (deep patterns, then computation)

def os.split(s: U32) -> {s == os.mk(os.lo16(s), os.hi16(s)) : U32}:
  match s:
    case U32{WCon{s0, WCon{s1, WCon{s2, WCon{s3, WCon{s4, WCon{s5, WCon{s6, WCon{s7, WCon{s8, WCon{s9, WCon{s10, WCon{s11, WCon{s12, WCon{s13, WCon{s14, WCon{s15, WCon{s16, WCon{s17, WCon{s18, WCon{s19, WCon{s20, WCon{s21, WCon{s22, WCon{s23, WCon{s24, WCon{s25, WCon{s26, WCon{s27, WCon{s28, WCon{s29, WCon{s30, WCon{s31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def os.and_mask(s: U32) -> {U32.and(65535, s) == os.mk(os.lo16(s), Word.zero(16n)) : U32}:
  match s:
    case U32{WCon{s0, WCon{s1, WCon{s2, WCon{s3, WCon{s4, WCon{s5, WCon{s6, WCon{s7, WCon{s8, WCon{s9, WCon{s10, WCon{s11, WCon{s12, WCon{s13, WCon{s14, WCon{s15, WCon{s16, WCon{s17, WCon{s18, WCon{s19, WCon{s20, WCon{s21, WCon{s22, WCon{s23, WCon{s24, WCon{s25, WCon{s26, WCon{s27, WCon{s28, WCon{s29, WCon{s30, WCon{s31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def os.shr_mask(s: U32) -> {U32.shrn(s, 16n) == os.mk(os.hi16(s), Word.zero(16n)) : U32}:
  match s:
    case U32{WCon{s0, WCon{s1, WCon{s2, WCon{s3, WCon{s4, WCon{s5, WCon{s6, WCon{s7, WCon{s8, WCon{s9, WCon{s10, WCon{s11, WCon{s12, WCon{s13, WCon{s14, WCon{s15, WCon{s16, WCon{s17, WCon{s18, WCon{s19, WCon{s20, WCon{s21, WCon{s22, WCon{s23, WCon{s24, WCon{s25, WCon{s26, WCon{s27, WCon{s28, WCon{s29, WCon{s30, WCon{s31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# The values of the halves

def os.v_split(+s: U32) -> {U32.to_nat(s) == Nat.add(Word.to_nat(16n, os.lo16(s)), UN.U32Nat.dbl(16n, Word.to_nat(16n, os.hi16(s)))) : Nat}:
  %Equal.sym(U32, s, os.mk(os.lo16(s), os.hi16(s)), os.split(s)) : {U32.to_nat(_) == Nat.add(Word.to_nat(16n, os.lo16(s)), UN.U32Nat.dbl(16n, Word.to_nat(16n, os.hi16(s)))) : Nat}
  os.mk_value(os.lo16(s), os.hi16(s))

def os.v_and(+s: U32) -> {U32.to_nat(U32.and(s, 65535)) == Word.to_nat(16n, os.lo16(s)) : Nat}:
  %os.and_comm(65535, s) : {U32.to_nat(_) == Word.to_nat(16n, os.lo16(s)) : Nat}
  %Equal.sym(U32, U32.and(65535, s), os.mk(os.lo16(s), Word.zero(16n)), os.and_mask(s)) : {U32.to_nat(_) == Word.to_nat(16n, os.lo16(s)) : Nat}
  os.mk_zero_value(os.lo16(s))

def os.v_shr(+s: U32) -> {U32.to_nat(U32.shrn(s, 16n)) == Word.to_nat(16n, os.hi16(s)) : Nat}:
  %Equal.sym(U32, U32.shrn(s, 16n), os.mk(os.hi16(s), Word.zero(16n)), os.shr_mask(s)) : {U32.to_nat(_) == Word.to_nat(16n, os.hi16(s)) : Nat}
  os.mk_zero_value(os.hi16(s))

# The two facts about d = 2^16 - 1, proved without expanding the number

def os.hD() -> {1n+Word.to_nat(16n, Word.not(16n, Word.zero(16n))) == UN.U32Nat.dbl(16n, 1n) : Nat}:
  %os.add_zero(Word.to_nat(16n, Word.not(16n, Word.zero(16n)))) : {1n+_ == UN.U32Nat.dbl(16n, 1n) : Nat}
  %UL.word_zero_value(16n) : {1n+Nat.add(Word.to_nat(16n, Word.not(16n, Word.zero(16n))), _) == UN.U32Nat.dbl(16n, 1n) : Nat}
  UL.word_not_value(16n, Word.zero(16n))

def os.e65535() -> {65535 == os.mk(Word.not(16n, Word.zero(16n)), Word.zero(16n)) : U32}:
  {==}

def os.hE() -> {U32.to_nat(65535) == Word.to_nat(16n, Word.not(16n, Word.zero(16n))) : Nat}:
  %Equal.sym(U32, 65535, os.mk(Word.not(16n, Word.zero(16n)), Word.zero(16n)), os.e65535()) : {U32.to_nat(_) == Word.to_nat(16n, Word.not(16n, Word.zero(16n))) : Nat}
  os.mk_zero_value(Word.not(16n, Word.zero(16n)))

def os.hd() -> {Nat.is_le(1n, Word.to_nat(16n, Word.not(16n, Word.zero(16n)))) == True{} : Bool}:
  {==}

# Bounds: a U32 of at most 65535 is a value of at most d

def os.fit_of(+d: Nat, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, h: {U32.is_le(a, 65535) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(a), d) == True{} : Bool}:
  %hE : {Nat.is_le(U32.to_nat(a), _) == True{} : Bool}
  %UL.u32_le_value(a, 65535) : {_ == True{} : Bool}
  h

def os.fit_to(+d: Nat, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, h: {Nat.is_le(U32.to_nat(a), d) == True{} : Bool}) -> {U32.is_le(a, 65535) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_le(a, 65535), Nat.is_le(U32.to_nat(a), U32.to_nat(65535)), UL.u32_le_value(a, 65535)) : {_ == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(65535), d, hE) : {Nat.is_le(U32.to_nat(a), _) == True{} : Bool}
  h

def os.w16_le(+d: Nat, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +x: Word(16n)) -> {Nat.is_le(Word.to_nat(16n, x), d) == True{} : Bool}:
  %os.lt_succ(Word.to_nat(16n, x), d) : {_ == True{} : Bool}
  %Equal.sym(Nat, 1n+d, UN.U32Nat.dbl(16n, 1n), hD) : {Nat.is_lt(Word.to_nat(16n, x), _) == True{} : Bool}
  UL.word_value_lt(16n, x)

def os.d_lt(+d: Nat, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}) -> {Nat.is_lt(d, UN.U32Nat.dbl(16n, 1n)) == True{} : Bool}:
  %hD : {Nat.is_lt(d, _) == True{} : Bool}
  Equal.trans(Bool, Nat.is_lt(d, 1n+d), Nat.is_le(d, d), True{}, os.lt_succ(d, d), os.le_refl(d))

# L + 2^16 H <= d: H = 0
def os.hi_zero(+d: Nat, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +L: Nat, +H: Nat, +h: {Nat.is_le(Nat.add(L, UN.U32Nat.dbl(16n, H)), d) == True{} : Bool}) -> {H == 0n : Nat}:
  os.lt_one(H, Equal.trans(Bool, Nat.is_lt(H, 1n), Nat.is_lt(UN.U32Nat.dbl(16n, H), UN.U32Nat.dbl(16n, 1n)), True{}, Equal.sym(Bool, Nat.is_lt(UN.U32Nat.dbl(16n, H), UN.U32Nat.dbl(16n, 1n)), Nat.is_lt(H, 1n), UL.dbl_lt(16n, H, 1n)), os.le_lt(UN.U32Nat.dbl(16n, H), d, UN.U32Nat.dbl(16n, 1n), os.le_trans(UN.U32Nat.dbl(16n, H), Nat.add(L, UN.U32Nat.dbl(16n, H)), d, os.le_add_l(L, UN.U32Nat.dbl(16n, H)), h), os.d_lt(d, hD))))

# a value of at most d is the value of its low half
def os.fit_lo(+d: Nat, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +s: U32, +h: {Nat.is_le(U32.to_nat(s), d) == True{} : Bool}) -> {U32.to_nat(s) == Word.to_nat(16n, os.lo16(s)) : Nat}:
  +hz = os.hi_zero(d, hD, Word.to_nat(16n, os.lo16(s)), Word.to_nat(16n, os.hi16(s)), Equal.trans(Bool, Nat.is_le(Nat.add(Word.to_nat(16n, os.lo16(s)), UN.U32Nat.dbl(16n, Word.to_nat(16n, os.hi16(s)))), d), Nat.is_le(U32.to_nat(s), d), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, d), Nat.add(Word.to_nat(16n, os.lo16(s)), UN.U32Nat.dbl(16n, Word.to_nat(16n, os.hi16(s)))), U32.to_nat(s), Equal.sym(Nat, U32.to_nat(s), Nat.add(Word.to_nat(16n, os.lo16(s)), UN.U32Nat.dbl(16n, Word.to_nat(16n, os.hi16(s)))), os.v_split(s))), h))
  %Equal.sym(Nat, U32.to_nat(s), Nat.add(Word.to_nat(16n, os.lo16(s)), UN.U32Nat.dbl(16n, Word.to_nat(16n, os.hi16(s)))), os.v_split(s)) : {_ == Word.to_nat(16n, os.lo16(s)) : Nat}
  %Equal.sym(Nat, Word.to_nat(16n, os.hi16(s)), 0n, hz) : {Nat.add(Word.to_nat(16n, os.lo16(s)), UN.U32Nat.dbl(16n, _)) == Word.to_nat(16n, os.lo16(s)) : Nat}
  %Equal.sym(Nat, UN.U32Nat.dbl(16n, 0n), 0n, UL.dbl_zero(16n)) : {Nat.add(Word.to_nat(16n, os.lo16(s)), _) == Word.to_nat(16n, os.lo16(s)) : Nat}
  os.add_zero(Word.to_nat(16n, os.lo16(s)))

# No wrap: the sum of two values of at most d fits a word

def os.fit65535(+d: Nat, +hE: {U32.to_nat(65535) == d : Nat}) -> {Nat.is_le(U32.to_nat(65535), d) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(65535), d, hE) : {Nat.is_le(_, d) == True{} : Bool}
  os.le_refl(d)

def os.lo65535(+d: Nat, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}) -> {Word.to_nat(16n, os.lo16(65535)) == d : Nat}:
  Equal.trans(Nat, Word.to_nat(16n, os.lo16(65535)), U32.to_nat(65535), d, Equal.sym(Nat, U32.to_nat(65535), Word.to_nat(16n, os.lo16(65535)), os.fit_lo(d, hD, 65535, os.fit65535(d, hE))), hE)

def os.nowrap_bound(+d: Nat, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +b: U32, +ha: {Nat.is_le(U32.to_nat(a), d) == True{} : Bool}, +hb: {Nat.is_le(U32.to_nat(b), d) == True{} : Bool}) -> {Nat.is_le(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(os.mk(os.lo16(65535), os.lo16(65535)))) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(os.mk(os.lo16(65535), os.lo16(65535))), Nat.add(Word.to_nat(16n, os.lo16(65535)), UN.U32Nat.dbl(16n, Word.to_nat(16n, os.lo16(65535)))), os.mk_value(os.lo16(65535), os.lo16(65535))) : {Nat.is_le(Nat.add(U32.to_nat(a), U32.to_nat(b)), _) == True{} : Bool}
  %Equal.sym(Nat, Word.to_nat(16n, os.lo16(65535)), d, os.lo65535(d, hD, hE)) : {Nat.is_le(Nat.add(U32.to_nat(a), U32.to_nat(b)), Nat.add(_, UN.U32Nat.dbl(16n, _))) == True{} : Bool}
  os.le_add_mono(U32.to_nat(a), U32.to_nat(b), d, UN.U32Nat.dbl(16n, d), ha, os.le_trans(U32.to_nat(b), d, UN.U32Nat.dbl(16n, d), hb, os.le_dbl(16n, d)))

def os.nowrap(+d: Nat, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +b: U32, +ha: {Nat.is_le(U32.to_nat(a), d) == True{} : Bool}, +hb: {Nat.is_le(U32.to_nat(b), d) == True{} : Bool}) -> {U32.to_nat(U32.add(a, b)) == Nat.add(U32.to_nat(a), U32.to_nat(b)) : Nat}:
  UL.u32_add_value(a, b, os.mk(os.lo16(65535), os.lo16(65535)), os.nowrap_bound(d, hD, hE, a, b, ha, hb))

# x and y with values X and Y, X + Y <= d: the sum of the values is at most 65535's
def os.sum_bound(+d: Nat, +hE: {U32.to_nat(65535) == d : Nat}, +x: U32, +y: U32, +X: Nat, +Y: Nat, +ex: {U32.to_nat(x) == X : Nat}, +ey: {U32.to_nat(y) == Y : Nat}, +h: {Nat.is_le(Nat.add(X, Y), d) == True{} : Bool}) -> {Nat.is_le(Nat.add(U32.to_nat(x), U32.to_nat(y)), U32.to_nat(65535)) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(65535), d, hE) : {Nat.is_le(Nat.add(U32.to_nat(x), U32.to_nat(y)), _) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(x), X, ex) : {Nat.is_le(Nat.add(_, U32.to_nat(y)), d) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(y), Y, ey) : {Nat.is_le(Nat.add(X, _), d) == True{} : Bool}
  h

def os.le_add0(+L: Nat, +d: Nat, +h: {Nat.is_le(L, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(L, 0n), d) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(L, 0n), L, os.add_zero(L)) : {Nat.is_le(_, d) == True{} : Bool}
  h

def os.le_add1(+L: Nat, +d: Nat, +h: {Nat.is_le(1n+L, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(L, 1n), d) == True{} : Bool}:
  %os.add_comm(1n, L) : {Nat.is_le(_, d) == True{} : Bool}
  h

# 2d < 2^16 + 2^16
def os.two_lt(+d: Nat, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}) -> {Nat.is_lt(Nat.add(d, d), UN.U32Nat.dbl(16n, Nat.add(1n, 1n))) == True{} : Bool}:
  %Equal.sym(Nat, UN.U32Nat.dbl(16n, Nat.add(1n, 1n)), Nat.add(UN.U32Nat.dbl(16n, 1n), UN.U32Nat.dbl(16n, 1n)), UL.dbl_add(16n, 1n, 1n)) : {Nat.is_lt(Nat.add(d, d), _) == True{} : Bool}
  %hD : {Nat.is_lt(Nat.add(d, d), Nat.add(_, _)) == True{} : Bool}
  Equal.trans(Bool, Nat.is_lt(Nat.add(d, d), 1n+Nat.add(d, 1n+d)), Nat.is_le(Nat.add(d, d), Nat.add(d, 1n+d)), True{}, os.lt_succ(Nat.add(d, d), Nat.add(d, 1n+d)), Equal.trans(Bool, Nat.is_le(Nat.add(d, d), Nat.add(d, 1n+d)), Nat.is_le(d, 1n+d), True{}, os.le_cancel_l(d, d, 1n+d), os.le_succ_r(d)))

# X = L + 2^16 H <= 2d: H < 2
def os.two_bound(+d: Nat, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +L: Nat, +H: Nat, +X: Nat, +eS: {X == Nat.add(L, UN.U32Nat.dbl(16n, H)) : Nat}, +hab: {Nat.is_le(X, Nat.add(d, d)) == True{} : Bool}) -> {Nat.is_lt(H, Nat.add(1n, 1n)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(H, Nat.add(1n, 1n)), Nat.is_lt(UN.U32Nat.dbl(16n, H), UN.U32Nat.dbl(16n, Nat.add(1n, 1n))), True{}, Equal.sym(Bool, Nat.is_lt(UN.U32Nat.dbl(16n, H), UN.U32Nat.dbl(16n, Nat.add(1n, 1n))), Nat.is_lt(H, Nat.add(1n, 1n)), UL.dbl_lt(16n, H, Nat.add(1n, 1n))), os.le_lt(UN.U32Nat.dbl(16n, H), Nat.add(d, d), UN.U32Nat.dbl(16n, Nat.add(1n, 1n)), os.le_trans(UN.U32Nat.dbl(16n, H), X, Nat.add(d, d), Equal.trans(Bool, Nat.is_le(UN.U32Nat.dbl(16n, H), X), Nat.is_le(UN.U32Nat.dbl(16n, H), Nat.add(L, UN.U32Nat.dbl(16n, H))), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(UN.U32Nat.dbl(16n, H), z), X, Nat.add(L, UN.U32Nat.dbl(16n, H)), eS), os.le_add_l(L, UN.U32Nat.dbl(16n, H))), hab), os.two_lt(d, hD)))

# X = L + 2^16 <= 2d: 1 + L <= d
def os.h1L(+d: Nat, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +L: Nat, +X: Nat, +eS: {X == Nat.add(L, UN.U32Nat.dbl(16n, 1n)) : Nat}, +hab: {Nat.is_le(X, Nat.add(d, d)) == True{} : Bool}) -> {Nat.is_le(1n+L, d) == True{} : Bool}:
  %os.le_cancel_l(d, 1n+L, d) : {_ == True{} : Bool}
  %Equal.sym(Nat, Nat.add(d, 1n+L), 1n+Nat.add(d, L), os.add_succ(d, L)) : {Nat.is_le(_, Nat.add(d, d)) == True{} : Bool}
  %os.add_comm(L, d) : {Nat.is_le(1n+_, Nat.add(d, d)) == True{} : Bool}
  %os.add_succ(L, d) : {Nat.is_le(_, Nat.add(d, d)) == True{} : Bool}
  %Equal.sym(Nat, 1n+d, UN.U32Nat.dbl(16n, 1n), hD) : {Nat.is_le(Nat.add(L, _), Nat.add(d, d)) == True{} : Bool}
  %eS : {Nat.is_le(_, Nat.add(d, d)) == True{} : Bool}
  hab

# The bridge: inet_add on two values of at most d is rep of their sum. The
# sum s (no wrap) is L + 2^16 H with L <= d and H < 2; the mask reads L and
# the shift H, and inet_add answers L + H.
def os.add_value.go(H: Nat, +d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +b: U32, +L: Nat, +eL: {U32.to_nat(U32.and(U32.add(a, b), 65535)) == L : Nat}, +eH: {U32.to_nat(U32.shrn(U32.add(a, b), 16n)) == H : Nat}, +eS: {Nat.add(U32.to_nat(a), U32.to_nat(b)) == Nat.add(L, UN.U32Nat.dbl(16n, H)) : Nat}, +hL: {Nat.is_le(L, d) == True{} : Bool}, +hab: {Nat.is_le(Nat.add(U32.to_nat(a), U32.to_nat(b)), Nat.add(d, d)) == True{} : Bool}, +hlt: {Nat.is_lt(H, Nat.add(1n, 1n)) == True{} : Bool}) -> {U32.to_nat(K.inet_add(a, b)) == os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))) : Nat}:
  match H:
    case 0n:
      %Equal.sym(Nat, U32.to_nat(U32.add(U32.and(U32.add(a, b), 65535), U32.shrn(U32.add(a, b), 16n))), Nat.add(U32.to_nat(U32.and(U32.add(a, b), 65535)), U32.to_nat(U32.shrn(U32.add(a, b), 16n))), UL.u32_add_value(U32.and(U32.add(a, b), 65535), U32.shrn(U32.add(a, b), 16n), 65535, os.sum_bound(d, hE, U32.and(U32.add(a, b), 65535), U32.shrn(U32.add(a, b), 16n), L, 0n, eL, eH, os.le_add0(L, d, hL)))) : {_ == os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))) : Nat}
      %Equal.sym(Nat, U32.to_nat(U32.and(U32.add(a, b), 65535)), L, eL) : {Nat.add(_, U32.to_nat(U32.shrn(U32.add(a, b), 16n))) == os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))) : Nat}
      %Equal.sym(Nat, U32.to_nat(U32.shrn(U32.add(a, b), 16n)), 0n, eH) : {Nat.add(L, _) == os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))) : Nat}
      %Equal.sym(Nat, Nat.add(U32.to_nat(a), U32.to_nat(b)), Nat.add(L, UN.U32Nat.dbl(16n, 0n)), eS) : {Nat.add(L, 0n) == os.rep(d, _) : Nat}
      %Equal.sym(Nat, UN.U32Nat.dbl(16n, 0n), 0n, UL.dbl_zero(16n)) : {Nat.add(L, 0n) == os.rep(d, Nat.add(L, _)) : Nat}
      %Equal.sym(Nat, Nat.add(L, 0n), L, os.add_zero(L)) : {_ == os.rep(d, _) : Nat}
      Equal.sym(Nat, os.rep(d, L), L, os.rep_small(d, L, hL))
    case 1n+ +H1:
      match H1:
        case 0n:
          +h1 = os.h1L(d, hD, L, Nat.add(U32.to_nat(a), U32.to_nat(b)), eS, hab)
          %Equal.sym(Nat, U32.to_nat(U32.add(U32.and(U32.add(a, b), 65535), U32.shrn(U32.add(a, b), 16n))), Nat.add(U32.to_nat(U32.and(U32.add(a, b), 65535)), U32.to_nat(U32.shrn(U32.add(a, b), 16n))), UL.u32_add_value(U32.and(U32.add(a, b), 65535), U32.shrn(U32.add(a, b), 16n), 65535, os.sum_bound(d, hE, U32.and(U32.add(a, b), 65535), U32.shrn(U32.add(a, b), 16n), L, 1n, eL, eH, os.le_add1(L, d, h1)))) : {_ == os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))) : Nat}
          %Equal.sym(Nat, U32.to_nat(U32.and(U32.add(a, b), 65535)), L, eL) : {Nat.add(_, U32.to_nat(U32.shrn(U32.add(a, b), 16n))) == os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))) : Nat}
          %Equal.sym(Nat, U32.to_nat(U32.shrn(U32.add(a, b), 16n)), 1n, eH) : {Nat.add(L, _) == os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))) : Nat}
          %Equal.sym(Nat, Nat.add(U32.to_nat(a), U32.to_nat(b)), Nat.add(L, UN.U32Nat.dbl(16n, 1n)), eS) : {Nat.add(L, 1n) == os.rep(d, _) : Nat}
          %hD : {Nat.add(L, 1n) == os.rep(d, Nat.add(L, _)) : Nat}
          %Equal.sym(Nat, Nat.add(L, 1n+d), 1n+Nat.add(L, d), os.add_succ(L, d)) : {Nat.add(L, 1n) == os.rep(d, _) : Nat}
          %Equal.sym(Nat, os.rep(d, Nat.add(1n+L, d)), os.rep(d, 1n+L), os.rep_period1(d, L, hd)) : {Nat.add(L, 1n) == _ : Nat}
          %Equal.sym(Nat, os.rep(d, 1n+L), 1n+L, os.rep_small(d, 1n+L, h1)) : {Nat.add(L, 1n) == _ : Nat}
          os.add_comm(L, 1n)
        case 1n+ +h:
          Empty.absurd({U32.to_nat(K.inet_add(a, b)) == os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))) : Nat}, os.ft(Equal.trans(Bool, False{}, Nat.is_lt(h, 0n), True{}, Equal.sym(Bool, Nat.is_lt(h, 0n), False{}, os.lt_zero(h)), hlt)))

def os.add_value(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +b: U32, +ha: {Nat.is_le(U32.to_nat(a), d) == True{} : Bool}, +hb: {Nat.is_le(U32.to_nat(b), d) == True{} : Bool}) -> {U32.to_nat(K.inet_add(a, b)) == os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))) : Nat}:
  +eS = Equal.trans(Nat, Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(U32.add(a, b)), Nat.add(Word.to_nat(16n, os.lo16(U32.add(a, b))), UN.U32Nat.dbl(16n, Word.to_nat(16n, os.hi16(U32.add(a, b))))), Equal.sym(Nat, U32.to_nat(U32.add(a, b)), Nat.add(U32.to_nat(a), U32.to_nat(b)), os.nowrap(d, hD, hE, a, b, ha, hb)), os.v_split(U32.add(a, b)))
  +hab = os.le_add_mono(U32.to_nat(a), U32.to_nat(b), d, d, ha, hb)
  os.add_value.go(Word.to_nat(16n, os.hi16(U32.add(a, b))), d, hd, hD, hE, a, b, Word.to_nat(16n, os.lo16(U32.add(a, b))), os.v_and(U32.add(a, b)), os.v_shr(U32.add(a, b)), eS, os.w16_le(d, hD, os.lo16(U32.add(a, b))), hab, os.two_bound(d, hD, Word.to_nat(16n, os.lo16(U32.add(a, b))), Word.to_nat(16n, os.hi16(U32.add(a, b))), Nat.add(U32.to_nat(a), U32.to_nat(b)), eS, hab))

# inet_add keeps values at most d
def os.add_fits(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +b: U32, +ha: {Nat.is_le(U32.to_nat(a), d) == True{} : Bool}, +hb: {Nat.is_le(U32.to_nat(b), d) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(K.inet_add(a, b)), d) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(K.inet_add(a, b)), os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))), os.add_value(d, hd, hD, hE, a, b, ha, hb)) : {Nat.is_le(_, d) == True{} : Bool}
  os.rep_le(d, Nat.add(U32.to_nat(a), U32.to_nat(b)), hd)

# The sum of a byte list: rep of the plain sum of its 16-bit words

# the plain sum of the 16-bit words of a byte list, an odd final byte padded
def os.ws(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{a, Nil{}}:
      U32.to_nat(K.inet_word(a, 0))
    case Con{a, Con{b, t}}:
      Nat.add(U32.to_nat(K.inet_word(a, b)), os.ws(t))

def os.w8s(a: U32, b: U32) -> Word(16n):
  match a b:
    case U32{x} U32{y}:
      W.W64.bits.cat(8n, 8n, W.W64.bits.lo(8n, 24n, y), W.W64.bits.lo(8n, 24n, x))

def os.word_mk(a: U32, b: U32) -> {K.inet_word(a, b) == os.mk(os.w8s(a, b), Word.zero(16n)) : U32}:
  match a b:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, bh}}}}}}}}}:
      {==}

def os.word_fits(+d: Nat, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +a: U32, +b: U32) -> {Nat.is_le(U32.to_nat(K.inet_word(a, b)), d) == True{} : Bool}:
  %Equal.sym(U32, K.inet_word(a, b), os.mk(os.w8s(a, b), Word.zero(16n)), os.word_mk(a, b)) : {Nat.is_le(U32.to_nat(_), d) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(os.mk(os.w8s(a, b), Word.zero(16n))), Word.to_nat(16n, os.w8s(a, b)), os.mk_zero_value(os.w8s(a, b))) : {Nat.is_le(_, d) == True{} : Bool}
  os.w16_le(d, hD, os.w8s(a, b))

def os.fold(xs: List<&2, U32>, +d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +acc: U32, +h: {Nat.is_le(U32.to_nat(acc), d) == True{} : Bool}) -> {U32.to_nat(K.inet_sum.list(xs, acc)) == os.rep(d, Nat.add(U32.to_nat(acc), os.ws(xs))) : Nat}:
  match xs:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(U32.to_nat(acc), 0n), U32.to_nat(acc), os.add_zero(U32.to_nat(acc))) : {U32.to_nat(acc) == os.rep(d, _) : Nat}
      Equal.sym(Nat, os.rep(d, U32.to_nat(acc)), U32.to_nat(acc), os.rep_small(d, U32.to_nat(acc), h))
    case Con{+a, Nil{}}:
      os.add_value(d, hd, hD, hE, acc, K.inet_word(a, 0), h, os.word_fits(d, hD, a, 0))
    case Con{+a, Con{+b, +t}}:
      %Equal.sym(Nat, U32.to_nat(K.inet_sum.list(t, K.inet_add(acc, K.inet_word(a, b)))), os.rep(d, Nat.add(U32.to_nat(K.inet_add(acc, K.inet_word(a, b))), os.ws(t))), os.fold(t, d, hd, hD, hE, K.inet_add(acc, K.inet_word(a, b)), os.add_fits(d, hd, hD, hE, acc, K.inet_word(a, b), h, os.word_fits(d, hD, a, b)))) : {_ == os.rep(d, Nat.add(U32.to_nat(acc), Nat.add(U32.to_nat(K.inet_word(a, b)), os.ws(t)))) : Nat}
      %Equal.sym(Nat, U32.to_nat(K.inet_add(acc, K.inet_word(a, b))), os.rep(d, Nat.add(U32.to_nat(acc), U32.to_nat(K.inet_word(a, b)))), os.add_value(d, hd, hD, hE, acc, K.inet_word(a, b), h, os.word_fits(d, hD, a, b))) : {os.rep(d, Nat.add(_, os.ws(t))) == os.rep(d, Nat.add(U32.to_nat(acc), Nat.add(U32.to_nat(K.inet_word(a, b)), os.ws(t)))) : Nat}
      %Equal.sym(Nat, os.rep(d, Nat.add(os.rep(d, Nat.add(U32.to_nat(acc), U32.to_nat(K.inet_word(a, b)))), os.ws(t))), os.rep(d, Nat.add(Nat.add(U32.to_nat(acc), U32.to_nat(K.inet_word(a, b))), os.ws(t))), os.rep_fold(d, Nat.add(U32.to_nat(acc), U32.to_nat(K.inet_word(a, b))), os.ws(t), hd)) : {_ == os.rep(d, Nat.add(U32.to_nat(acc), Nat.add(U32.to_nat(K.inet_word(a, b)), os.ws(t)))) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(U32.to_nat(acc), U32.to_nat(K.inet_word(a, b))), os.ws(t)), Nat.add(U32.to_nat(acc), Nat.add(U32.to_nat(K.inet_word(a, b)), os.ws(t))), os.add_assoc(U32.to_nat(acc), U32.to_nat(K.inet_word(a, b)), os.ws(t))) : {os.rep(d, _) == os.rep(d, Nat.add(U32.to_nat(acc), Nat.add(U32.to_nat(K.inet_word(a, b)), os.ws(t)))) : Nat}
      {==}

def os.fold_fits(+xs: List<&2, U32>, +d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +acc: U32, +h: {Nat.is_le(U32.to_nat(acc), d) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(K.inet_sum.list(xs, acc)), d) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(K.inet_sum.list(xs, acc)), os.rep(d, Nat.add(U32.to_nat(acc), os.ws(xs))), os.fold(xs, d, hd, hD, hE, acc, h)) : {Nat.is_le(_, d) == True{} : Bool}
  os.rep_le(d, Nat.add(U32.to_nat(acc), os.ws(xs)), hd)

# the words of xs ++ ys, xs of even length
def os.ws_append(xs: List<&2, U32>, +ys: List<&2, U32>, e: {K.inet_even.list(xs) == True{} : Bool}) -> {os.ws(B.append(xs, ys)) == Nat.add(os.ws(xs), os.ws(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+a, Nil{}}:
      Empty.absurd({os.ws(B.append([a], ys)) == Nat.add(os.ws([a]), os.ws(ys)) : Nat}, os.ft(e))
    case Con{+a, Con{+b, +t}}:
      %Equal.sym(Nat, os.ws(B.append(t, ys)), Nat.add(os.ws(t), os.ws(ys)), os.ws_append(t, ys, e)) : {Nat.add(U32.to_nat(K.inet_word(a, b)), _) == Nat.add(Nat.add(U32.to_nat(K.inet_word(a, b)), os.ws(t)), os.ws(ys)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(U32.to_nat(K.inet_word(a, b)), os.ws(t)), os.ws(ys)), Nat.add(U32.to_nat(K.inet_word(a, b)), Nat.add(os.ws(t), os.ws(ys))), os.add_assoc(U32.to_nat(K.inet_word(a, b)), os.ws(t), os.ws(ys)))

# Even lengths

def os.ev(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match p:
        case 0n:
          False{}
        case 1n+q:
          os.ev(q)

def os.even_len(xs: List<&2, U32>) -> {K.inet_even.list(xs) == os.ev(B.len(xs)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, Nil{}}:
      {==}
    case Con{a, Con{b, t}}:
      os.even_len(t)

def os.ev_double(k: Nat) -> {os.ev(Nat.double(k)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      os.ev_double(p)

# the first 2k bytes of o (if o has them) are an even number
def os.even_take(+o: B.Octets, +k: Nat, +h: {Nat.is_le(Nat.double(k), B.Octets.len(o)) == True{} : Bool}) -> {K.inet_even(B.Octets.take(Nat.double(k), o)) == True{} : Bool}:
  %Equal.sym(Bool, K.inet_even.list(B.Octets.to_list(B.Octets.take(Nat.double(k), o))), os.ev(B.len(B.Octets.to_list(B.Octets.take(Nat.double(k), o)))), os.even_len(B.Octets.to_list(B.Octets.take(Nat.double(k), o)))) : {_ == True{} : Bool}
  %BL.octets_len_list(B.Octets.take(Nat.double(k), o)) : {os.ev(_) == True{} : Bool}
  %Equal.sym(Nat, B.Octets.len(B.Octets.take(Nat.double(k), o)), Nat.double(k), BL.octets_len_take_le(Nat.double(k), o, h)) : {os.ev(_) == True{} : Bool}
  os.ev_double(k)

def os.be16_even.m(v: U32) -> {K.inet_even.list(B.mask(B.be16(v))) == True{} : Bool}:
  match v:
    case U32{x}:
      {==}

def os.be16_even(+v: U32) -> {K.inet_even.list(B.Octets.to_list(B.Octets.be16(v))) == True{} : Bool}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.be16(v))), B.mask(B.be16(v)), BL.octets_to_of(B.be16(v))) : {K.inet_even.list(_) == True{} : Bool}
  os.be16_even.m(v)

# The checksum: the complement of the sum, so c + S = d

def os.finish_mk(t: U32) -> {K.inet_finish(t) == os.mk(Word.not(16n, os.lo16(t)), Word.zero(16n)) : U32}:
  match t:
    case U32{WCon{t0, WCon{t1, WCon{t2, WCon{t3, WCon{t4, WCon{t5, WCon{t6, WCon{t7, WCon{t8, WCon{t9, WCon{t10, WCon{t11, WCon{t12, WCon{t13, WCon{t14, WCon{t15, WCon{t16, WCon{t17, WCon{t18, WCon{t19, WCon{t20, WCon{t21, WCon{t22, WCon{t23, WCon{t24, WCon{t25, WCon{t26, WCon{t27, WCon{t28, WCon{t29, WCon{t30, WCon{t31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def os.finish_fits(+d: Nat, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +t: U32) -> {Nat.is_le(U32.to_nat(K.inet_finish(t)), d) == True{} : Bool}:
  %Equal.sym(U32, K.inet_finish(t), os.mk(Word.not(16n, os.lo16(t)), Word.zero(16n)), os.finish_mk(t)) : {Nat.is_le(U32.to_nat(_), d) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(os.mk(Word.not(16n, os.lo16(t)), Word.zero(16n))), Word.to_nat(16n, Word.not(16n, os.lo16(t))), os.mk_zero_value(Word.not(16n, os.lo16(t)))) : {Nat.is_le(_, d) == True{} : Bool}
  os.w16_le(d, hD, Word.not(16n, os.lo16(t)))

def os.finish_value(+d: Nat, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +t: U32, +h: {Nat.is_le(U32.to_nat(t), d) == True{} : Bool}) -> {Nat.add(U32.to_nat(K.inet_finish(t)), U32.to_nat(t)) == d : Nat}:
  %Equal.sym(U32, K.inet_finish(t), os.mk(Word.not(16n, os.lo16(t)), Word.zero(16n)), os.finish_mk(t)) : {Nat.add(U32.to_nat(_), U32.to_nat(t)) == d : Nat}
  %Equal.sym(Nat, U32.to_nat(os.mk(Word.not(16n, os.lo16(t)), Word.zero(16n))), Word.to_nat(16n, Word.not(16n, os.lo16(t))), os.mk_zero_value(Word.not(16n, os.lo16(t)))) : {Nat.add(_, U32.to_nat(t)) == d : Nat}
  %Equal.sym(Nat, U32.to_nat(t), Word.to_nat(16n, os.lo16(t)), os.fit_lo(d, hD, t, h)) : {Nat.add(Word.to_nat(16n, Word.not(16n, os.lo16(t))), _) == d : Nat}
  os.succ_inj(Nat.add(Word.to_nat(16n, Word.not(16n, os.lo16(t))), Word.to_nat(16n, os.lo16(t))), d, Equal.trans(Nat, 1n+Nat.add(Word.to_nat(16n, Word.not(16n, os.lo16(t))), Word.to_nat(16n, os.lo16(t))), UN.U32Nat.dbl(16n, 1n), 1n+d, UL.word_not_value(16n, os.lo16(t)), Equal.sym(Nat, 1n+d, UN.U32Nat.dbl(16n, 1n), hD)))

# A 16-bit field: its two bytes are one word, the field's value

def os.be16_mask(c: U32) -> {os.ws(B.mask(B.be16(c))) == Nat.add(U32.to_nat(os.mk(os.lo16(c), Word.zero(16n))), 0n) : Nat}:
  match c:
    case U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def os.be16_ws(+d: Nat, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +c: U32, +h: {Nat.is_le(U32.to_nat(c), d) == True{} : Bool}) -> {os.ws(B.Octets.to_list(B.Octets.be16(c))) == U32.to_nat(c) : Nat}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.be16(c))), B.mask(B.be16(c)), BL.octets_to_of(B.be16(c))) : {os.ws(_) == U32.to_nat(c) : Nat}
  %Equal.sym(Nat, os.ws(B.mask(B.be16(c))), Nat.add(U32.to_nat(os.mk(os.lo16(c), Word.zero(16n))), 0n), os.be16_mask(c)) : {_ == U32.to_nat(c) : Nat}
  %Equal.sym(Nat, Nat.add(U32.to_nat(os.mk(os.lo16(c), Word.zero(16n))), 0n), U32.to_nat(os.mk(os.lo16(c), Word.zero(16n))), os.add_zero(U32.to_nat(os.mk(os.lo16(c), Word.zero(16n))))) : {_ == U32.to_nat(c) : Nat}
  %Equal.sym(Nat, U32.to_nat(os.mk(os.lo16(c), Word.zero(16n))), Word.to_nat(16n, os.lo16(c)), os.mk_zero_value(os.lo16(c))) : {_ == U32.to_nat(c) : Nat}
  Equal.sym(Nat, U32.to_nat(c), Word.to_nat(16n, os.lo16(c)), os.fit_lo(d, hD, c, h))

def os.fit0(+d: Nat) -> {Nat.is_le(U32.to_nat(0), d) == True{} : Bool}:
  os.le_zero(d)

def os.be16_ws0(+d: Nat, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}) -> {os.ws(B.Octets.to_list(B.Octets.be16(0))) == 0n : Nat}:
  os.be16_ws(d, hD, 0, os.fit0(d))

# The Internet checksum written into data: the data then sums to d

def os.K3(+pseudo: B.Octets, +o: B.Octets, +off: Nat) -> Nat:
  Nat.add(os.ws(B.Octets.to_list(pseudo)), Nat.add(os.ws(B.Octets.to_list(B.Octets.take(off, o))), os.ws(B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o)))))

def os.rearr(+p: Nat, +t: Nat, +b: Nat, +z: Nat) -> {Nat.add(p, Nat.add(t, Nat.add(b, z))) == Nat.add(Nat.add(p, Nat.add(t, z)), b) : Nat}:
  %os.add_comm(z, b) : {Nat.add(p, Nat.add(t, _)) == Nat.add(Nat.add(p, Nat.add(t, z)), b) : Nat}
  %os.add_assoc(t, z, b) : {Nat.add(p, _) == Nat.add(Nat.add(p, Nat.add(t, z)), b) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(p, Nat.add(t, z)), b), Nat.add(p, Nat.add(Nat.add(t, z), b)), os.add_assoc(p, Nat.add(t, z), b))

# the sum of pseudo ++ o with the 16-bit field at off set to c, pseudo and
# the bytes before off of even length: rep of the words around the field
# plus c's
def os.sum_put(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +pseudo: B.Octets, +o: B.Octets, +off: Nat, +c: U32, +eP: {K.inet_even(pseudo) == True{} : Bool}, +eT: {K.inet_even(B.Octets.take(off, o)) == True{} : Bool}) -> {U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, c)))) == os.rep(d, Nat.add(os.K3(pseudo, o, off), os.ws(B.Octets.to_list(B.Octets.be16(c))))) : Nat}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(pseudo, K.inet_put16(o, off, c))), B.append(B.Octets.to_list(pseudo), B.Octets.to_list(K.inet_put16(o, off, c))), BL.octets_append_list(pseudo, K.inet_put16(o, off, c))) : {U32.to_nat(K.inet_sum.list(_, 0)) == os.rep(d, Nat.add(os.K3(pseudo, o, off), os.ws(B.Octets.to_list(B.Octets.be16(c))))) : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.take(off, o), B.Octets.append(B.Octets.be16(c), B.Octets.drop(Nat.add(off, 2n), o)))), B.append(B.Octets.to_list(B.Octets.take(off, o)), B.Octets.to_list(B.Octets.append(B.Octets.be16(c), B.Octets.drop(Nat.add(off, 2n), o)))), BL.octets_append_list(B.Octets.take(off, o), B.Octets.append(B.Octets.be16(c), B.Octets.drop(Nat.add(off, 2n), o)))) : {U32.to_nat(K.inet_sum.list(B.append(B.Octets.to_list(pseudo), _), 0)) == os.rep(d, Nat.add(os.K3(pseudo, o, off), os.ws(B.Octets.to_list(B.Octets.be16(c))))) : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.be16(c), B.Octets.drop(Nat.add(off, 2n), o))), B.append(B.Octets.to_list(B.Octets.be16(c)), B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o))), BL.octets_append_list(B.Octets.be16(c), B.Octets.drop(Nat.add(off, 2n), o))) : {U32.to_nat(K.inet_sum.list(B.append(B.Octets.to_list(pseudo), B.append(B.Octets.to_list(B.Octets.take(off, o)), _)), 0)) == os.rep(d, Nat.add(os.K3(pseudo, o, off), os.ws(B.Octets.to_list(B.Octets.be16(c))))) : Nat}
  %Equal.sym(Nat, U32.to_nat(K.inet_sum.list(B.append(B.Octets.to_list(pseudo), B.append(B.Octets.to_list(B.Octets.take(off, o)), B.append(B.Octets.to_list(B.Octets.be16(c)), B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o))))), 0)), os.rep(d, Nat.add(U32.to_nat(0), os.ws(B.append(B.Octets.to_list(pseudo), B.append(B.Octets.to_list(B.Octets.take(off, o)), B.append(B.Octets.to_list(B.Octets.be16(c)), B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o)))))))), os.fold(B.append(B.Octets.to_list(pseudo), B.append(B.Octets.to_list(B.Octets.take(off, o)), B.append(B.Octets.to_list(B.Octets.be16(c)), B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o))))), d, hd, hD, hE, 0, os.fit0(d))) : {_ == os.rep(d, Nat.add(os.K3(pseudo, o, off), os.ws(B.Octets.to_list(B.Octets.be16(c))))) : Nat}
  %Equal.sym(Nat, os.ws(B.append(B.Octets.to_list(pseudo), B.append(B.Octets.to_list(B.Octets.take(off, o)), B.append(B.Octets.to_list(B.Octets.be16(c)), B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o)))))), Nat.add(os.ws(B.Octets.to_list(pseudo)), os.ws(B.append(B.Octets.to_list(B.Octets.take(off, o)), B.append(B.Octets.to_list(B.Octets.be16(c)), B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o)))))), os.ws_append(B.Octets.to_list(pseudo), B.append(B.Octets.to_list(B.Octets.take(off, o)), B.append(B.Octets.to_list(B.Octets.be16(c)), B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o)))), eP)) : {os.rep(d, Nat.add(U32.to_nat(0), _)) == os.rep(d, Nat.add(os.K3(pseudo, o, off), os.ws(B.Octets.to_list(B.Octets.be16(c))))) : Nat}
  %Equal.sym(Nat, os.ws(B.append(B.Octets.to_list(B.Octets.take(off, o)), B.append(B.Octets.to_list(B.Octets.be16(c)), B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o))))), Nat.add(os.ws(B.Octets.to_list(B.Octets.take(off, o))), os.ws(B.append(B.Octets.to_list(B.Octets.be16(c)), B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o))))), os.ws_append(B.Octets.to_list(B.Octets.take(off, o)), B.append(B.Octets.to_list(B.Octets.be16(c)), B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o))), eT)) : {os.rep(d, Nat.add(U32.to_nat(0), Nat.add(os.ws(B.Octets.to_list(pseudo)), _))) == os.rep(d, Nat.add(os.K3(pseudo, o, off), os.ws(B.Octets.to_list(B.Octets.be16(c))))) : Nat}
  %Equal.sym(Nat, os.ws(B.append(B.Octets.to_list(B.Octets.be16(c)), B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o)))), Nat.add(os.ws(B.Octets.to_list(B.Octets.be16(c))), os.ws(B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o)))), os.ws_append(B.Octets.to_list(B.Octets.be16(c)), B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o)), os.be16_even(c))) : {os.rep(d, Nat.add(U32.to_nat(0), Nat.add(os.ws(B.Octets.to_list(pseudo)), Nat.add(os.ws(B.Octets.to_list(B.Octets.take(off, o))), _)))) == os.rep(d, Nat.add(os.K3(pseudo, o, off), os.ws(B.Octets.to_list(B.Octets.be16(c))))) : Nat}
  %Equal.sym(Nat, Nat.add(os.ws(B.Octets.to_list(pseudo)), Nat.add(os.ws(B.Octets.to_list(B.Octets.take(off, o))), Nat.add(os.ws(B.Octets.to_list(B.Octets.be16(c))), os.ws(B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o)))))), Nat.add(Nat.add(os.ws(B.Octets.to_list(pseudo)), Nat.add(os.ws(B.Octets.to_list(B.Octets.take(off, o))), os.ws(B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o))))), os.ws(B.Octets.to_list(B.Octets.be16(c)))), os.rearr(os.ws(B.Octets.to_list(pseudo)), os.ws(B.Octets.to_list(B.Octets.take(off, o))), os.ws(B.Octets.to_list(B.Octets.be16(c))), os.ws(B.Octets.to_list(B.Octets.drop(Nat.add(off, 2n), o))))) : {os.rep(d, Nat.add(U32.to_nat(0), _)) == os.rep(d, Nat.add(os.K3(pseudo, o, off), os.ws(B.Octets.to_list(B.Octets.be16(c))))) : Nat}
  {==}

# the field set to 0: rep of the words around it
def os.sum0(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +pseudo: B.Octets, +o: B.Octets, +off: Nat, +eP: {K.inet_even(pseudo) == True{} : Bool}, +eT: {K.inet_even(B.Octets.take(off, o)) == True{} : Bool}) -> {U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))) == os.rep(d, os.K3(pseudo, o, off)) : Nat}:
  %Equal.sym(Nat, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), os.rep(d, Nat.add(os.K3(pseudo, o, off), os.ws(B.Octets.to_list(B.Octets.be16(0))))), os.sum_put(d, hd, hD, hE, pseudo, o, off, 0, eP, eT)) : {_ == os.rep(d, os.K3(pseudo, o, off)) : Nat}
  %Equal.sym(Nat, os.ws(B.Octets.to_list(B.Octets.be16(0))), 0n, os.be16_ws0(d, hD)) : {os.rep(d, Nat.add(os.K3(pseudo, o, off), _)) == os.rep(d, os.K3(pseudo, o, off)) : Nat}
  %Equal.sym(Nat, Nat.add(os.K3(pseudo, o, off), 0n), os.K3(pseudo, o, off), os.add_zero(os.K3(pseudo, o, off))) : {os.rep(d, _) == os.rep(d, os.K3(pseudo, o, off)) : Nat}
  {==}

def os.sum0_fits(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +pseudo: B.Octets, +o: B.Octets, +off: Nat, +eP: {K.inet_even(pseudo) == True{} : Bool}, +eT: {K.inet_even(B.Octets.take(off, o)) == True{} : Bool}) -> {Nat.is_le(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), d) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), os.rep(d, os.K3(pseudo, o, off)), os.sum0(d, hd, hD, hE, pseudo, o, off, eP, eT)) : {Nat.is_le(_, d) == True{} : Bool}
  os.rep_le(d, os.K3(pseudo, o, off), hd)

# x written into the field verifies when the sum with the field 0, plus x,
# is d
def os.verify_put(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +pseudo: B.Octets, +o: B.Octets, +off: Nat, +eP: {K.inet_even(pseudo) == True{} : Bool}, +eT: {K.inet_even(B.Octets.take(off, o)) == True{} : Bool}, +x: U32, +hx: {Nat.is_le(U32.to_nat(x), d) == True{} : Bool}, +ex: {os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), U32.to_nat(x))) == d : Nat}) -> {K.inet_verify(B.Octets.append(pseudo, K.inet_put16(o, off, x))) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, x))), 65535), Nat.is_eq(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, x)))), U32.to_nat(65535)), UL.u32_eq_value(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, x))), 65535)) : {_ == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(65535), d, hE) : {Nat.is_eq(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, x)))), _) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, x)))), os.rep(d, Nat.add(os.K3(pseudo, o, off), os.ws(B.Octets.to_list(B.Octets.be16(x))))), os.sum_put(d, hd, hD, hE, pseudo, o, off, x, eP, eT)) : {Nat.is_eq(_, d) == True{} : Bool}
  %Equal.sym(Nat, os.ws(B.Octets.to_list(B.Octets.be16(x))), U32.to_nat(x), os.be16_ws(d, hD, x, hx)) : {Nat.is_eq(os.rep(d, Nat.add(os.K3(pseudo, o, off), _)), d) == True{} : Bool}
  %os.rep_fold(d, os.K3(pseudo, o, off), U32.to_nat(x), hd) : {Nat.is_eq(_, d) == True{} : Bool}
  %os.sum0(d, hd, hD, hE, pseudo, o, off, eP, eT) : {Nat.is_eq(os.rep(d, Nat.add(_, U32.to_nat(x))), d) == True{} : Bool}
  %Equal.sym(Nat, os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), U32.to_nat(x))), d, ex) : {Nat.is_eq(_, d) == True{} : Bool}
  os.eq_refl(d)

def os.fill_sum(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +pseudo: B.Octets, +o: B.Octets, +off: Nat, +eP: {K.inet_even(pseudo) == True{} : Bool}, +eT: {K.inet_even(B.Octets.take(off, o)) == True{} : Bool}) -> {os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0))))))) == d : Nat}:
  %os.add_comm(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0))))) : {os.rep(d, _) == d : Nat}
  %Equal.sym(Nat, Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0))))), d, os.finish_value(d, hD, K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0))), os.sum0_fits(d, hd, hD, hE, pseudo, o, off, eP, eT))) : {os.rep(d, _) == d : Nat}
  os.rep_small(d, d, os.le_refl(d))

# inet_fill: the data with its checksum written in verifies
def os.fill_verifies(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +pseudo: B.Octets, +o: B.Octets, +off: Nat, +eP: {K.inet_even(pseudo) == True{} : Bool}, +eT: {K.inet_even(B.Octets.take(off, o)) == True{} : Bool}) -> {K.inet_verify(B.Octets.append(pseudo, K.inet_fill(pseudo, o, off))) == True{} : Bool}:
  os.verify_put(d, hd, hD, hE, pseudo, o, off, eP, eT, K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), os.finish_fits(d, hD, K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), os.fill_sum(d, hd, hD, hE, pseudo, o, off, eP, eT))

# the checksum 0 sent as 65535 (UDP): it verifies too, the sum being d
def os.v_eq_zero(x: Nat, +h: {Nat.is_eq(x, 0n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      Empty.absurd({1n+p == 0n : Nat}, os.ft(h))

def os.allones_sum(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +pseudo: B.Octets, +o: B.Octets, +off: Nat, +eP: {K.inet_even(pseudo) == True{} : Bool}, +eT: {K.inet_even(B.Octets.take(off, o)) == True{} : Bool}, +hz: {U32.is_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), 0) == True{} : Bool}) -> {os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), U32.to_nat(65535))) == d : Nat}:
  +vc = os.v_eq_zero(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0))))), Equal.trans(Bool, Nat.is_eq(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0))))), 0n), U32.is_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), 0), True{}, Equal.sym(Bool, U32.is_eq(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), 0), Nat.is_eq(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0))))), U32.to_nat(0)), UL.u32_eq_value(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), 0)), hz))
  +s0 = Equal.trans(Nat, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0))))), d, Equal.sym(Nat, Nat.add(U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0))))), U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), Equal.cong(Nat, Nat, z => Nat.add(z, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0))))), U32.to_nat(K.inet_finish(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0))))), 0n, vc)), os.finish_value(d, hD, K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0))), os.sum0_fits(d, hd, hD, hE, pseudo, o, off, eP, eT)))
  %Equal.sym(Nat, U32.to_nat(65535), d, hE) : {os.rep(d, Nat.add(U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), _)) == d : Nat}
  %Equal.sym(Nat, U32.to_nat(K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))), d, s0) : {os.rep(d, Nat.add(_, d)) == d : Nat}
  %Equal.sym(Nat, os.rep(d, Nat.add(d, d)), os.rep(d, d), os.rep_period(d, d, hd, hd)) : {_ == d : Nat}
  os.rep_small(d, d, os.le_refl(d))

# The algebra, for the laws: every value at most d (written as U32.is_le(x,
# 65535) in the laws)

def os.g_add_bound(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +b: U32, +ha: {U32.is_le(a, 65535) == True{} : Bool}, +hb: {U32.is_le(b, 65535) == True{} : Bool}) -> {U32.is_le(K.inet_add(a, b), 65535) == True{} : Bool}:
  os.fit_to(d, hE, K.inet_add(a, b), os.add_fits(d, hd, hD, hE, a, b, os.fit_of(d, hE, a, ha), os.fit_of(d, hE, b, hb)))

def os.g_add_comm(+a: U32, +b: U32) -> {K.inet_add(a, b) == K.inet_add(b, a) : U32}:
  %U32.add_comm(b, a) : {U32.add(U32.and(_, 65535), U32.shrn(_, 16n)) == K.inet_add(b, a) : U32}
  {==}

def os.g_add_zero(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +ha: {U32.is_le(a, 65535) == True{} : Bool}) -> {K.inet_add(a, 0) == a : U32}:
  UL.u32_value_eq(K.inet_add(a, 0), a, Equal.trans(Nat, U32.to_nat(K.inet_add(a, 0)), os.rep(d, Nat.add(U32.to_nat(a), 0n)), U32.to_nat(a), os.add_value(d, hd, hD, hE, a, 0, os.fit_of(d, hE, a, ha), os.fit0(d)), Equal.trans(Nat, os.rep(d, Nat.add(U32.to_nat(a), 0n)), os.rep(d, U32.to_nat(a)), U32.to_nat(a), Equal.cong(Nat, Nat, z => os.rep(d, z), Nat.add(U32.to_nat(a), 0n), U32.to_nat(a), os.add_zero(U32.to_nat(a))), os.rep_small(d, U32.to_nat(a), os.fit_of(d, hE, a, ha)))))

def os.g_add_assoc.v(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +b: U32, +c: U32, +ha: {Nat.is_le(U32.to_nat(a), d) == True{} : Bool}, +hb: {Nat.is_le(U32.to_nat(b), d) == True{} : Bool}, +hc: {Nat.is_le(U32.to_nat(c), d) == True{} : Bool}) -> {U32.to_nat(K.inet_add(K.inet_add(a, b), c)) == U32.to_nat(K.inet_add(a, K.inet_add(b, c))) : Nat}:
  %Equal.sym(Nat, U32.to_nat(K.inet_add(K.inet_add(a, b), c)), os.rep(d, Nat.add(U32.to_nat(K.inet_add(a, b)), U32.to_nat(c))), os.add_value(d, hd, hD, hE, K.inet_add(a, b), c, os.add_fits(d, hd, hD, hE, a, b, ha, hb), hc)) : {_ == U32.to_nat(K.inet_add(a, K.inet_add(b, c))) : Nat}
  %Equal.sym(Nat, U32.to_nat(K.inet_add(a, b)), os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))), os.add_value(d, hd, hD, hE, a, b, ha, hb)) : {os.rep(d, Nat.add(_, U32.to_nat(c))) == U32.to_nat(K.inet_add(a, K.inet_add(b, c))) : Nat}
  %Equal.sym(Nat, os.rep(d, Nat.add(os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))), U32.to_nat(c))), os.rep(d, Nat.add(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c))), os.rep_fold(d, Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c), hd)) : {_ == U32.to_nat(K.inet_add(a, K.inet_add(b, c))) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(U32.to_nat(a), U32.to_nat(b)), U32.to_nat(c)), Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c))), os.add_assoc(U32.to_nat(a), U32.to_nat(b), U32.to_nat(c))) : {os.rep(d, _) == U32.to_nat(K.inet_add(a, K.inet_add(b, c))) : Nat}
  %Equal.sym(Nat, U32.to_nat(K.inet_add(a, K.inet_add(b, c))), os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(K.inet_add(b, c)))), os.add_value(d, hd, hD, hE, a, K.inet_add(b, c), ha, os.add_fits(d, hd, hD, hE, b, c, hb, hc))) : {os.rep(d, Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c)))) == _ : Nat}
  %Equal.sym(Nat, U32.to_nat(K.inet_add(b, c)), os.rep(d, Nat.add(U32.to_nat(b), U32.to_nat(c))), os.add_value(d, hd, hD, hE, b, c, hb, hc)) : {os.rep(d, Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c)))) == os.rep(d, Nat.add(U32.to_nat(a), _)) : Nat}
  %os.add_comm(os.rep(d, Nat.add(U32.to_nat(b), U32.to_nat(c))), U32.to_nat(a)) : {os.rep(d, Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c)))) == os.rep(d, _) : Nat}
  %Equal.sym(Nat, os.rep(d, Nat.add(os.rep(d, Nat.add(U32.to_nat(b), U32.to_nat(c))), U32.to_nat(a))), os.rep(d, Nat.add(Nat.add(U32.to_nat(b), U32.to_nat(c)), U32.to_nat(a))), os.rep_fold(d, Nat.add(U32.to_nat(b), U32.to_nat(c)), U32.to_nat(a), hd)) : {os.rep(d, Nat.add(U32.to_nat(a), Nat.add(U32.to_nat(b), U32.to_nat(c)))) == _ : Nat}
  %os.add_comm(Nat.add(U32.to_nat(b), U32.to_nat(c)), U32.to_nat(a)) : {os.rep(d, _) == os.rep(d, Nat.add(Nat.add(U32.to_nat(b), U32.to_nat(c)), U32.to_nat(a))) : Nat}
  {==}

def os.g_complement.v(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +ha: {Nat.is_le(U32.to_nat(a), d) == True{} : Bool}) -> {U32.to_nat(K.inet_add(a, K.inet_finish(a))) == U32.to_nat(65535) : Nat}:
  %Equal.sym(Nat, U32.to_nat(K.inet_add(a, K.inet_finish(a))), os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(K.inet_finish(a)))), os.add_value(d, hd, hD, hE, a, K.inet_finish(a), ha, os.finish_fits(d, hD, a))) : {_ == U32.to_nat(65535) : Nat}
  %os.add_comm(U32.to_nat(K.inet_finish(a)), U32.to_nat(a)) : {os.rep(d, _) == U32.to_nat(65535) : Nat}
  %Equal.sym(Nat, Nat.add(U32.to_nat(K.inet_finish(a)), U32.to_nat(a)), d, os.finish_value(d, hD, a, ha)) : {os.rep(d, _) == U32.to_nat(65535) : Nat}
  %Equal.sym(Nat, os.rep(d, d), d, os.rep_small(d, d, os.le_refl(d))) : {_ == U32.to_nat(65535) : Nat}
  Equal.sym(Nat, U32.to_nat(65535), d, hE)

def os.g_finish_bound(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +t: U32) -> {U32.is_le(K.inet_finish(t), 65535) == True{} : Bool}:
  os.fit_to(d, hE, K.inet_finish(t), os.finish_fits(d, hD, t))

def os.g_update_bound(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +acc: U32, +o: B.Octets, +h: {U32.is_le(acc, 65535) == True{} : Bool}) -> {U32.is_le(K.inet_update(acc, o), 65535) == True{} : Bool}:
  os.fit_to(d, hE, K.inet_update(acc, o), os.fold_fits(B.Octets.to_list(o), d, hd, hD, hE, acc, os.fit_of(d, hE, acc, h)))

def os.swap(+x: Nat, +y: Nat, +z: Nat) -> {Nat.add(Nat.add(x, y), z) == Nat.add(Nat.add(x, z), y) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(x, y), z), Nat.add(x, Nat.add(y, z)), os.add_assoc(x, y, z)) : {_ == Nat.add(Nat.add(x, z), y) : Nat}
  %os.add_comm(z, y) : {Nat.add(x, _) == Nat.add(Nat.add(x, z), y) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(x, z), y), Nat.add(x, Nat.add(z, y)), os.add_assoc(x, z, y))

def os.g_update_add.v(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +acc: U32, +w: U32, +o: B.Octets, +ha: {Nat.is_le(U32.to_nat(acc), d) == True{} : Bool}, +hw: {Nat.is_le(U32.to_nat(w), d) == True{} : Bool}) -> {U32.to_nat(K.inet_update(K.inet_add(acc, w), o)) == U32.to_nat(K.inet_add(K.inet_update(acc, o), w)) : Nat}:
  %Equal.sym(Nat, U32.to_nat(K.inet_update(K.inet_add(acc, w), o)), os.rep(d, Nat.add(U32.to_nat(K.inet_add(acc, w)), os.ws(B.Octets.to_list(o)))), os.fold(B.Octets.to_list(o), d, hd, hD, hE, K.inet_add(acc, w), os.add_fits(d, hd, hD, hE, acc, w, ha, hw))) : {_ == U32.to_nat(K.inet_add(K.inet_update(acc, o), w)) : Nat}
  %Equal.sym(Nat, U32.to_nat(K.inet_add(acc, w)), os.rep(d, Nat.add(U32.to_nat(acc), U32.to_nat(w))), os.add_value(d, hd, hD, hE, acc, w, ha, hw)) : {os.rep(d, Nat.add(_, os.ws(B.Octets.to_list(o)))) == U32.to_nat(K.inet_add(K.inet_update(acc, o), w)) : Nat}
  %Equal.sym(Nat, os.rep(d, Nat.add(os.rep(d, Nat.add(U32.to_nat(acc), U32.to_nat(w))), os.ws(B.Octets.to_list(o)))), os.rep(d, Nat.add(Nat.add(U32.to_nat(acc), U32.to_nat(w)), os.ws(B.Octets.to_list(o)))), os.rep_fold(d, Nat.add(U32.to_nat(acc), U32.to_nat(w)), os.ws(B.Octets.to_list(o)), hd)) : {_ == U32.to_nat(K.inet_add(K.inet_update(acc, o), w)) : Nat}
  %Equal.sym(Nat, U32.to_nat(K.inet_add(K.inet_update(acc, o), w)), os.rep(d, Nat.add(U32.to_nat(K.inet_update(acc, o)), U32.to_nat(w))), os.add_value(d, hd, hD, hE, K.inet_update(acc, o), w, os.fold_fits(B.Octets.to_list(o), d, hd, hD, hE, acc, ha), hw)) : {os.rep(d, Nat.add(Nat.add(U32.to_nat(acc), U32.to_nat(w)), os.ws(B.Octets.to_list(o)))) == _ : Nat}
  %Equal.sym(Nat, U32.to_nat(K.inet_update(acc, o)), os.rep(d, Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(o)))), os.fold(B.Octets.to_list(o), d, hd, hD, hE, acc, ha)) : {os.rep(d, Nat.add(Nat.add(U32.to_nat(acc), U32.to_nat(w)), os.ws(B.Octets.to_list(o)))) == os.rep(d, Nat.add(_, U32.to_nat(w))) : Nat}
  %Equal.sym(Nat, os.rep(d, Nat.add(os.rep(d, Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(o)))), U32.to_nat(w))), os.rep(d, Nat.add(Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(o))), U32.to_nat(w))), os.rep_fold(d, Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(o))), U32.to_nat(w), hd)) : {os.rep(d, Nat.add(Nat.add(U32.to_nat(acc), U32.to_nat(w)), os.ws(B.Octets.to_list(o)))) == _ : Nat}
  Equal.cong(Nat, Nat, z => os.rep(d, z), Nat.add(Nat.add(U32.to_nat(acc), U32.to_nat(w)), os.ws(B.Octets.to_list(o))), Nat.add(Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(o))), U32.to_nat(w)), os.swap(U32.to_nat(acc), U32.to_nat(w), os.ws(B.Octets.to_list(o))))

def os.g_update_comm.v(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +acc: U32, +x: B.Octets, +y: B.Octets, +h: {Nat.is_le(U32.to_nat(acc), d) == True{} : Bool}) -> {U32.to_nat(K.inet_update(K.inet_update(acc, x), y)) == U32.to_nat(K.inet_update(K.inet_update(acc, y), x)) : Nat}:
  %Equal.sym(Nat, U32.to_nat(K.inet_update(K.inet_update(acc, x), y)), os.rep(d, Nat.add(U32.to_nat(K.inet_update(acc, x)), os.ws(B.Octets.to_list(y)))), os.fold(B.Octets.to_list(y), d, hd, hD, hE, K.inet_update(acc, x), os.fold_fits(B.Octets.to_list(x), d, hd, hD, hE, acc, h))) : {_ == U32.to_nat(K.inet_update(K.inet_update(acc, y), x)) : Nat}
  %Equal.sym(Nat, U32.to_nat(K.inet_update(acc, x)), os.rep(d, Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(x)))), os.fold(B.Octets.to_list(x), d, hd, hD, hE, acc, h)) : {os.rep(d, Nat.add(_, os.ws(B.Octets.to_list(y)))) == U32.to_nat(K.inet_update(K.inet_update(acc, y), x)) : Nat}
  %Equal.sym(Nat, os.rep(d, Nat.add(os.rep(d, Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(x)))), os.ws(B.Octets.to_list(y)))), os.rep(d, Nat.add(Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(x))), os.ws(B.Octets.to_list(y)))), os.rep_fold(d, Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(x))), os.ws(B.Octets.to_list(y)), hd)) : {_ == U32.to_nat(K.inet_update(K.inet_update(acc, y), x)) : Nat}
  %Equal.sym(Nat, U32.to_nat(K.inet_update(K.inet_update(acc, y), x)), os.rep(d, Nat.add(U32.to_nat(K.inet_update(acc, y)), os.ws(B.Octets.to_list(x)))), os.fold(B.Octets.to_list(x), d, hd, hD, hE, K.inet_update(acc, y), os.fold_fits(B.Octets.to_list(y), d, hd, hD, hE, acc, h))) : {os.rep(d, Nat.add(Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(x))), os.ws(B.Octets.to_list(y)))) == _ : Nat}
  %Equal.sym(Nat, U32.to_nat(K.inet_update(acc, y)), os.rep(d, Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(y)))), os.fold(B.Octets.to_list(y), d, hd, hD, hE, acc, h)) : {os.rep(d, Nat.add(Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(x))), os.ws(B.Octets.to_list(y)))) == os.rep(d, Nat.add(_, os.ws(B.Octets.to_list(x)))) : Nat}
  %Equal.sym(Nat, os.rep(d, Nat.add(os.rep(d, Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(y)))), os.ws(B.Octets.to_list(x)))), os.rep(d, Nat.add(Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(y))), os.ws(B.Octets.to_list(x)))), os.rep_fold(d, Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(y))), os.ws(B.Octets.to_list(x)), hd)) : {os.rep(d, Nat.add(Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(x))), os.ws(B.Octets.to_list(y)))) == _ : Nat}
  Equal.cong(Nat, Nat, z => os.rep(d, z), Nat.add(Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(x))), os.ws(B.Octets.to_list(y))), Nat.add(Nat.add(U32.to_nat(acc), os.ws(B.Octets.to_list(y))), os.ws(B.Octets.to_list(x))), os.swap(U32.to_nat(acc), os.ws(B.Octets.to_list(x)), os.ws(B.Octets.to_list(y))))

def os.g_sum_swap.v(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +x: B.Octets, +y: B.Octets, +ex: {K.inet_even(x) == True{} : Bool}, +ey: {K.inet_even(y) == True{} : Bool}) -> {U32.to_nat(K.inet_sum(B.Octets.append(x, y))) == U32.to_nat(K.inet_sum(B.Octets.append(y, x))) : Nat}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(x, y)), B.append(B.Octets.to_list(x), B.Octets.to_list(y)), BL.octets_append_list(x, y)) : {U32.to_nat(K.inet_sum.list(_, 0)) == U32.to_nat(K.inet_sum(B.Octets.append(y, x))) : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(y, x)), B.append(B.Octets.to_list(y), B.Octets.to_list(x)), BL.octets_append_list(y, x)) : {U32.to_nat(K.inet_sum.list(B.append(B.Octets.to_list(x), B.Octets.to_list(y)), 0)) == U32.to_nat(K.inet_sum.list(_, 0)) : Nat}
  %Equal.sym(Nat, U32.to_nat(K.inet_sum.list(B.append(B.Octets.to_list(x), B.Octets.to_list(y)), 0)), os.rep(d, Nat.add(U32.to_nat(0), os.ws(B.append(B.Octets.to_list(x), B.Octets.to_list(y))))), os.fold(B.append(B.Octets.to_list(x), B.Octets.to_list(y)), d, hd, hD, hE, 0, os.fit0(d))) : {_ == U32.to_nat(K.inet_sum.list(B.append(B.Octets.to_list(y), B.Octets.to_list(x)), 0)) : Nat}
  %Equal.sym(Nat, U32.to_nat(K.inet_sum.list(B.append(B.Octets.to_list(y), B.Octets.to_list(x)), 0)), os.rep(d, Nat.add(U32.to_nat(0), os.ws(B.append(B.Octets.to_list(y), B.Octets.to_list(x))))), os.fold(B.append(B.Octets.to_list(y), B.Octets.to_list(x)), d, hd, hD, hE, 0, os.fit0(d))) : {os.rep(d, Nat.add(U32.to_nat(0), os.ws(B.append(B.Octets.to_list(x), B.Octets.to_list(y))))) == _ : Nat}
  %Equal.sym(Nat, os.ws(B.append(B.Octets.to_list(x), B.Octets.to_list(y))), Nat.add(os.ws(B.Octets.to_list(x)), os.ws(B.Octets.to_list(y))), os.ws_append(B.Octets.to_list(x), B.Octets.to_list(y), ex)) : {os.rep(d, Nat.add(U32.to_nat(0), _)) == os.rep(d, Nat.add(U32.to_nat(0), os.ws(B.append(B.Octets.to_list(y), B.Octets.to_list(x))))) : Nat}
  %Equal.sym(Nat, os.ws(B.append(B.Octets.to_list(y), B.Octets.to_list(x))), Nat.add(os.ws(B.Octets.to_list(y)), os.ws(B.Octets.to_list(x))), os.ws_append(B.Octets.to_list(y), B.Octets.to_list(x), ey)) : {os.rep(d, Nat.add(U32.to_nat(0), Nat.add(os.ws(B.Octets.to_list(x)), os.ws(B.Octets.to_list(y))))) == os.rep(d, Nat.add(U32.to_nat(0), _)) : Nat}
  %os.add_comm(os.ws(B.Octets.to_list(x)), os.ws(B.Octets.to_list(y))) : {os.rep(d, Nat.add(U32.to_nat(0), Nat.add(os.ws(B.Octets.to_list(x)), os.ws(B.Octets.to_list(y))))) == os.rep(d, Nat.add(U32.to_nat(0), _)) : Nat}
  {==}

# The end-around carry: a sum past d comes back round as the sum less d

def os.sum_fits(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +b: U32, +ha: {Nat.is_le(U32.to_nat(a), d) == True{} : Bool}, +hb: {Nat.is_le(U32.to_nat(b), d) == True{} : Bool}, +h: {U32.is_le(U32.add(a, b), 65535) == True{} : Bool}) -> {Nat.is_le(Nat.add(U32.to_nat(a), U32.to_nat(b)), d) == True{} : Bool}:
  %os.nowrap(d, hD, hE, a, b, ha, hb) : {Nat.is_le(_, d) == True{} : Bool}
  os.fit_of(d, hE, U32.add(a, b), h)

def os.sum_not_fits(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +b: U32, +ha: {Nat.is_le(U32.to_nat(a), d) == True{} : Bool}, +hb: {Nat.is_le(U32.to_nat(b), d) == True{} : Bool}, +h: {U32.is_le(U32.add(a, b), 65535) == False{} : Bool}) -> {Nat.is_le(Nat.add(U32.to_nat(a), U32.to_nat(b)), d) == False{} : Bool}:
  %os.nowrap(d, hD, hE, a, b, ha, hb) : {Nat.is_le(_, d) == False{} : Bool}
  %hE : {Nat.is_le(U32.to_nat(U32.add(a, b)), _) == False{} : Bool}
  %UL.u32_le_value(U32.add(a, b), 65535) : {_ == False{} : Bool}
  h

def os.g_no_carry.v(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +b: U32, +ha: {Nat.is_le(U32.to_nat(a), d) == True{} : Bool}, +hb: {Nat.is_le(U32.to_nat(b), d) == True{} : Bool}, +h: {U32.is_le(U32.add(a, b), 65535) == True{} : Bool}) -> {U32.to_nat(K.inet_add(a, b)) == U32.to_nat(U32.add(a, b)) : Nat}:
  %Equal.sym(Nat, U32.to_nat(K.inet_add(a, b)), os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))), os.add_value(d, hd, hD, hE, a, b, ha, hb)) : {_ == U32.to_nat(U32.add(a, b)) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.add(a, b)), Nat.add(U32.to_nat(a), U32.to_nat(b)), os.nowrap(d, hD, hE, a, b, ha, hb)) : {os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))) == _ : Nat}
  os.rep_small(d, Nat.add(U32.to_nat(a), U32.to_nat(b)), os.sum_fits(d, hd, hD, hE, a, b, ha, hb, h))

def os.g_no_carry(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +b: U32, +ha: {U32.is_le(a, 65535) == True{} : Bool}, +hb: {U32.is_le(b, 65535) == True{} : Bool}, +h: {U32.is_le(U32.add(a, b), 65535) == True{} : Bool}) -> {K.inet_add(a, b) == U32.add(a, b) : U32}:
  UL.u32_value_eq(K.inet_add(a, b), U32.add(a, b), os.g_no_carry.v(d, hd, hD, hE, a, b, os.fit_of(d, hE, a, ha), os.fit_of(d, hE, b, hb), h))

def os.end_le(+d: Nat, +j: Nat, +X: Nat, +eX: {X == Nat.add(1n+j, d) : Nat}, +hab: {Nat.is_le(X, Nat.add(d, d)) == True{} : Bool}) -> {Nat.is_le(1n+j, d) == True{} : Bool}:
  %os.le_cancel_l(d, 1n+j, d) : {_ == True{} : Bool}
  %os.add_comm(1n+j, d) : {Nat.is_le(_, Nat.add(d, d)) == True{} : Bool}
  %eX : {Nat.is_le(_, Nat.add(d, d)) == True{} : Bool}
  hab

def os.end_rep(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +X: Nat, +j: Nat, +eX: {X == Nat.add(1n+j, d) : Nat}, +hab: {Nat.is_le(X, Nat.add(d, d)) == True{} : Bool}) -> {os.rep(d, X) == Nat.sub(X, d) : Nat}:
  %Equal.sym(Nat, X, Nat.add(1n+j, d), eX) : {os.rep(d, _) == Nat.sub(_, d) : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.add(1n+j, d), d), 1n+j, os.sub_add(1n+j, d)) : {os.rep(d, Nat.add(1n+j, d)) == _ : Nat}
  %Equal.sym(Nat, os.rep(d, Nat.add(1n+j, d)), os.rep(d, 1n+j), os.rep_period1(d, j, hd)) : {_ == 1n+j : Nat}
  os.rep_small(d, 1n+j, os.end_le(d, j, X, eX, hab))

def os.end_hle(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +b: U32, +ha: {Nat.is_le(U32.to_nat(a), d) == True{} : Bool}, +hb: {Nat.is_le(U32.to_nat(b), d) == True{} : Bool}, +hX: {Nat.is_le(Nat.add(U32.to_nat(a), U32.to_nat(b)), d) == False{} : Bool}) -> {Nat.is_le(U32.to_nat(65535), U32.to_nat(U32.add(a, b))) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(65535), d, hE) : {Nat.is_le(_, U32.to_nat(U32.add(a, b))) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.add(a, b)), Nat.add(U32.to_nat(a), U32.to_nat(b)), os.nowrap(d, hD, hE, a, b, ha, hb)) : {Nat.is_le(d, _) == True{} : Bool}
  os.le_pred(d, Nat.add(U32.to_nat(a), U32.to_nat(b)), os.not_le(Nat.add(U32.to_nat(a), U32.to_nat(b)), d, hX))

def os.g_end_around.v(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +b: U32, +ha: {Nat.is_le(U32.to_nat(a), d) == True{} : Bool}, +hb: {Nat.is_le(U32.to_nat(b), d) == True{} : Bool}, +h: {U32.is_le(U32.add(a, b), 65535) == False{} : Bool}) -> {U32.to_nat(K.inet_add(a, b)) == U32.to_nat(U32.sub(U32.add(a, b), 65535)) : Nat}:
  +hX = os.sum_not_fits(d, hd, hD, hE, a, b, ha, hb, h)
  %Equal.sym(Nat, U32.to_nat(K.inet_add(a, b)), os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))), os.add_value(d, hd, hD, hE, a, b, ha, hb)) : {_ == U32.to_nat(U32.sub(U32.add(a, b), 65535)) : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.sub(U32.add(a, b), 65535)), Nat.sub(U32.to_nat(U32.add(a, b)), U32.to_nat(65535)), UL.u32_sub_value(U32.add(a, b), 65535, os.end_hle(d, hd, hD, hE, a, b, ha, hb, hX))) : {os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))) == _ : Nat}
  %Equal.sym(Nat, U32.to_nat(U32.add(a, b)), Nat.add(U32.to_nat(a), U32.to_nat(b)), os.nowrap(d, hD, hE, a, b, ha, hb)) : {os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))) == Nat.sub(_, U32.to_nat(65535)) : Nat}
  %Equal.sym(Nat, U32.to_nat(65535), d, hE) : {os.rep(d, Nat.add(U32.to_nat(a), U32.to_nat(b))) == Nat.sub(Nat.add(U32.to_nat(a), U32.to_nat(b)), _) : Nat}
  os.end_rep(d, hd, Nat.add(U32.to_nat(a), U32.to_nat(b)), Nat.sub(Nat.add(U32.to_nat(a), U32.to_nat(b)), 1n+d), os.sub_split(Nat.add(U32.to_nat(a), U32.to_nat(b)), d, hX), os.le_add_mono(U32.to_nat(a), U32.to_nat(b), d, d, ha, hb))

def os.g_end_around(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +b: U32, +ha: {U32.is_le(a, 65535) == True{} : Bool}, +hb: {U32.is_le(b, 65535) == True{} : Bool}, +h: {U32.is_le(U32.add(a, b), 65535) == False{} : Bool}) -> {K.inet_add(a, b) == U32.sub(U32.add(a, b), 65535) : U32}:
  UL.u32_value_eq(K.inet_add(a, b), U32.sub(U32.add(a, b), 65535), os.g_end_around.v(d, hd, hD, hE, a, b, os.fit_of(d, hE, a, ha), os.fit_of(d, hE, b, hb), h))

# Lengths: writing a 16-bit field inside the data keeps its length

# x + (y - x) = y, for x <= y
def os.add_sub(x: Nat, y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.add(x, Nat.sub(y, x)) == y : Nat}:
  match x y:
    case 0n _:
      os.sub_zero(y)
    case 1n+ +xp 0n:
      Empty.absurd({Nat.add(1n+xp, Nat.sub(0n, 1n+xp)) == 0n : Nat}, os.ft(h))
    case 1n+ +xp 1n+ +yp:
      os.succ_cong(Nat.add(xp, Nat.sub(yp, xp)), yp, os.add_sub(xp, yp, h))

def os.len_put16(+o: B.Octets, +off: Nat, +x: U32, +h: {Nat.is_le(Nat.add(off, 2n), B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.len(K.inet_put16(o, off, x)) == B.Octets.len(o) : Nat}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(B.Octets.take(off, o), B.Octets.append(B.Octets.be16(x), B.Octets.drop(Nat.add(off, 2n), o)))), Nat.add(B.Octets.len(B.Octets.take(off, o)), B.Octets.len(B.Octets.append(B.Octets.be16(x), B.Octets.drop(Nat.add(off, 2n), o)))), BL.octets_len_append(B.Octets.take(off, o), B.Octets.append(B.Octets.be16(x), B.Octets.drop(Nat.add(off, 2n), o)))) : {_ == B.Octets.len(o) : Nat}
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(B.Octets.be16(x), B.Octets.drop(Nat.add(off, 2n), o))), Nat.add(B.Octets.len(B.Octets.be16(x)), B.Octets.len(B.Octets.drop(Nat.add(off, 2n), o))), BL.octets_len_append(B.Octets.be16(x), B.Octets.drop(Nat.add(off, 2n), o))) : {Nat.add(B.Octets.len(B.Octets.take(off, o)), _) == B.Octets.len(o) : Nat}
  %Equal.sym(Nat, B.Octets.len(B.Octets.take(off, o)), off, BL.octets_len_take_le(off, o, os.le_trans(off, Nat.add(off, 2n), B.Octets.len(o), os.le_add_r(off, 2n), h))) : {Nat.add(_, Nat.add(B.Octets.len(B.Octets.be16(x)), B.Octets.len(B.Octets.drop(Nat.add(off, 2n), o)))) == B.Octets.len(o) : Nat}
  %Equal.sym(Nat, B.Octets.len(B.Octets.be16(x)), 2n, BL.octets_len_be16(x)) : {Nat.add(off, Nat.add(_, B.Octets.len(B.Octets.drop(Nat.add(off, 2n), o)))) == B.Octets.len(o) : Nat}
  %Equal.sym(Nat, B.Octets.len(B.Octets.drop(Nat.add(off, 2n), o)), Nat.sub(B.Octets.len(o), Nat.add(off, 2n)), BL.octets_len_drop(Nat.add(off, 2n), o)) : {Nat.add(off, Nat.add(2n, _)) == B.Octets.len(o) : Nat}
  %os.add_assoc(off, 2n, Nat.sub(B.Octets.len(o), Nat.add(off, 2n))) : {_ == B.Octets.len(o) : Nat}
  os.add_sub(Nat.add(off, 2n), B.Octets.len(o), h)

# a value of at most d is its own low 16 bits
def os.low16_mk(c: U32) -> {B.low16(c) == os.mk(os.lo16(c), Word.zero(16n)) : U32}:
  match c:
    case U32{x}:
      {==}

def os.low16_fit(+d: Nat, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +c: U32, +h: {Nat.is_le(U32.to_nat(c), d) == True{} : Bool}) -> {B.low16(c) == c : U32}:
  UL.u32_value_eq(B.low16(c), c, Equal.trans(Nat, U32.to_nat(B.low16(c)), U32.to_nat(os.mk(os.lo16(c), Word.zero(16n))), U32.to_nat(c), Equal.cong(U32, Nat, z => U32.to_nat(z), B.low16(c), os.mk(os.lo16(c), Word.zero(16n)), os.low16_mk(c)), Equal.trans(Nat, U32.to_nat(os.mk(os.lo16(c), Word.zero(16n))), Word.to_nat(16n, os.lo16(c)), U32.to_nat(c), os.mk_zero_value(os.lo16(c)), Equal.sym(Nat, U32.to_nat(c), Word.to_nat(16n, os.lo16(c)), os.fit_lo(d, hD, c, h)))))

# Lists and Octets: the bytes of data with a 16-bit field written in

def os.mask_append(xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.mask(B.append(xs, ys)) == B.append(B.mask(xs), B.mask(ys)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(List<&2, U32>, B.mask(B.append(t, ys)), B.append(B.mask(t), B.mask(ys)), os.mask_append(t, ys)) : {Con{B.byte(x), _} == Con{B.byte(x), B.append(B.mask(t), B.mask(ys))} : List<&2, U32>}
      {==}

def os.len_mask(xs: List<&2, U32>) -> {B.len(B.mask(xs)) == B.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      os.succ_cong(B.len(B.mask(t)), B.len(t), os.len_mask(t))

def os.len_take(n: Nat, xs: List<&2, U32>, +h: {Nat.is_le(n, B.len(xs)) == True{} : Bool}) -> {B.len(B.take(n, xs)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match xs:
        case Nil{}:
          Empty.absurd({B.len(B.take(1n+p, Nil{})) == 1n+p : Nat}, os.ft(h))
        case Con{x, +t}:
          os.succ_cong(B.len(B.take(p, t)), p, os.len_take(p, t, h))

def os.le_drop(n: Nat, +k: Nat, xs: List<&2, U32>, +h: {Nat.is_le(Nat.add(n, k), B.len(xs)) == True{} : Bool}) -> {Nat.is_le(k, B.len(B.drop(n, xs))) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+ +p:
      match xs:
        case Nil{}:
          Empty.absurd({Nat.is_le(k, B.len(B.drop(1n+p, Nil{}))) == True{} : Bool}, os.ft(h))
        case Con{x, +t}:
          os.le_drop(p, k, t, h)

def os.drop_nil(n: Nat) -> {B.drop(n, Nil{}) == Nil{} : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def os.drop_drop(i: Nat, +j: Nat, xs: List<&2, U32>) -> {B.drop(j, B.drop(i, xs)) == B.drop(Nat.add(i, j), xs) : List<&2, U32>}:
  match i:
    case 0n:
      {==}
    case 1n+ +p:
      match xs:
        case Nil{}:
          os.drop_nil(j)
        case Con{x, +t}:
          os.drop_drop(p, j, t)

def os.of_list_append(+xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.Octets.of_list(B.append(xs, ys)) == B.Octets.append(B.Octets.of_list(xs), B.Octets.of_list(ys)) : B.Octets}:
  %BL.octets_of_to(B.Octets.append(B.Octets.of_list(xs), B.Octets.of_list(ys))) : {B.Octets.of_list(B.append(xs, ys)) == _ : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.of_list(xs), B.Octets.of_list(ys))), B.append(B.Octets.to_list(B.Octets.of_list(xs)), B.Octets.to_list(B.Octets.of_list(ys))), BL.octets_append_list(B.Octets.of_list(xs), B.Octets.of_list(ys))) : {B.Octets.of_list(B.append(xs, ys)) == B.Octets.of_list(_) : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(xs)), B.mask(xs), BL.octets_to_of(xs)) : {B.Octets.of_list(B.append(xs, ys)) == B.Octets.of_list(B.append(_, B.Octets.to_list(B.Octets.of_list(ys)))) : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(ys)), B.mask(ys), BL.octets_to_of(ys)) : {B.Octets.of_list(B.append(xs, ys)) == B.Octets.of_list(B.append(B.mask(xs), _)) : B.Octets}
  %os.mask_append(xs, ys) : {B.Octets.of_list(B.append(xs, ys)) == B.Octets.of_list(_) : B.Octets}
  %BL.octets_to_of(B.append(xs, ys)) : {B.Octets.of_list(B.append(xs, ys)) == B.Octets.of_list(_) : B.Octets}
  Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(B.Octets.of_list(B.append(xs, ys)))), B.Octets.of_list(B.append(xs, ys)), BL.octets_of_list_idempotent(B.append(xs, ys)))

# of_list(L) cut at off and off + 2
def os.cut3(+L: List<&2, U32>, +off: Nat) -> {B.Octets.of_list(L) == B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L))))) : B.Octets}:
  %BL.take_drop(off, L) : {B.Octets.of_list(_) == B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L))))) : B.Octets}
  %BL.take_drop(2n, B.drop(off, L)) : {B.Octets.of_list(B.append(B.take(off, L), _)) == B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L))))) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.of_list(B.append(B.take(off, L), B.append(B.take(2n, B.drop(off, L)), B.drop(2n, B.drop(off, L))))), B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.of_list(B.append(B.take(2n, B.drop(off, L)), B.drop(2n, B.drop(off, L))))), os.of_list_append(B.take(off, L), B.append(B.take(2n, B.drop(off, L)), B.drop(2n, B.drop(off, L))))) : {_ == B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L))))) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.of_list(B.append(B.take(2n, B.drop(off, L)), B.drop(2n, B.drop(off, L)))), B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L)))), os.of_list_append(B.take(2n, B.drop(off, L)), B.drop(2n, B.drop(off, L)))) : {B.Octets.append(B.Octets.of_list(B.take(off, L)), _) == B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L))))) : B.Octets}
  {==}

def os.lenA(+L: List<&2, U32>, +off: Nat, +h: {Nat.is_le(Nat.add(off, 2n), B.len(L)) == True{} : Bool}) -> {B.Octets.len(B.Octets.of_list(B.take(off, L))) == off : Nat}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(B.take(off, L))), B.len(B.take(off, L)), BL.octets_len_of_list(B.take(off, L))) : {_ == off : Nat}
  os.len_take(off, L, os.le_trans(off, Nat.add(off, 2n), B.len(L), os.le_add_r(off, 2n), h))

def os.lenB(+L: List<&2, U32>, +off: Nat, +h: {Nat.is_le(Nat.add(off, 2n), B.len(L)) == True{} : Bool}) -> {B.Octets.len(B.Octets.of_list(B.take(2n, B.drop(off, L)))) == 2n : Nat}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(B.take(2n, B.drop(off, L)))), B.len(B.take(2n, B.drop(off, L))), BL.octets_len_of_list(B.take(2n, B.drop(off, L)))) : {_ == 2n : Nat}
  os.len_take(2n, B.drop(off, L), os.le_drop(off, 2n, L, h))

# the bytes of of_list(L) with v written at off (off + 2 bytes present)
def os.put16_list(+L: List<&2, U32>, +off: Nat, +v: U32, +h: {Nat.is_le(Nat.add(off, 2n), B.len(L)) == True{} : Bool}) -> {B.Octets.to_list(K.inet_put16(B.Octets.of_list(L), off, v)) == B.append(B.mask(B.take(off, L)), B.append(B.mask(B.be16(v)), B.mask(B.drop(Nat.add(off, 2n), L)))) : List<&2, U32>}:
  %Equal.sym(B.Octets, B.Octets.of_list(L), B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L))))), os.cut3(L, off)) : {B.Octets.to_list(K.inet_put16(_, off, v)) == B.append(B.mask(B.take(off, L)), B.append(B.mask(B.be16(v)), B.mask(B.drop(Nat.add(off, 2n), L)))) : List<&2, U32>}
  %os.lenA(L, off, h) : {B.Octets.to_list(B.Octets.append(B.Octets.take(_, B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L)))))), B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(off, 2n), B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L))))))))) == B.append(B.mask(B.take(off, L)), B.append(B.mask(B.be16(v)), B.mask(B.drop(Nat.add(off, 2n), L)))) : List<&2, U32>}
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(B.Octets.of_list(B.take(off, L))), B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L)))))), B.Octets.of_list(B.take(off, L)), BL.octets_take_append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L)))))) : {B.Octets.to_list(B.Octets.append(_, B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(off, 2n), B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L))))))))) == B.append(B.mask(B.take(off, L)), B.append(B.mask(B.be16(v)), B.mask(B.drop(Nat.add(off, 2n), L)))) : List<&2, U32>}
  %os.lenA(L, off, h) : {B.Octets.to_list(B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(_, 2n), B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L))))))))) == B.append(B.mask(B.take(off, L)), B.append(B.mask(B.be16(v)), B.mask(B.drop(Nat.add(off, 2n), L)))) : List<&2, U32>}
  %Equal.sym(B.Octets, B.Octets.drop(Nat.add(B.Octets.len(B.Octets.of_list(B.take(off, L))), 2n), B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L)))))), B.Octets.drop(2n, B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L))))), BL.octets_drop_append_add(B.Octets.of_list(B.take(off, L)), 2n, B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L)))))) : {B.Octets.to_list(B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.be16(v), _))) == B.append(B.mask(B.take(off, L)), B.append(B.mask(B.be16(v)), B.mask(B.drop(Nat.add(off, 2n), L)))) : List<&2, U32>}
  %os.lenB(L, off, h) : {B.Octets.to_list(B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.be16(v), B.Octets.drop(_, B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L)))))))) == B.append(B.mask(B.take(off, L)), B.append(B.mask(B.be16(v)), B.mask(B.drop(Nat.add(off, 2n), L)))) : List<&2, U32>}
  %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(B.Octets.of_list(B.take(2n, B.drop(off, L)))), B.Octets.append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L))))), B.Octets.of_list(B.drop(2n, B.drop(off, L))), BL.octets_drop_append(B.Octets.of_list(B.take(2n, B.drop(off, L))), B.Octets.of_list(B.drop(2n, B.drop(off, L))))) : {B.Octets.to_list(B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.be16(v), _))) == B.append(B.mask(B.take(off, L)), B.append(B.mask(B.be16(v)), B.mask(B.drop(Nat.add(off, 2n), L)))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.be16(v), B.Octets.of_list(B.drop(2n, B.drop(off, L)))))), B.append(B.Octets.to_list(B.Octets.of_list(B.take(off, L))), B.Octets.to_list(B.Octets.append(B.Octets.be16(v), B.Octets.of_list(B.drop(2n, B.drop(off, L)))))), BL.octets_append_list(B.Octets.of_list(B.take(off, L)), B.Octets.append(B.Octets.be16(v), B.Octets.of_list(B.drop(2n, B.drop(off, L)))))) : {_ == B.append(B.mask(B.take(off, L)), B.append(B.mask(B.be16(v)), B.mask(B.drop(Nat.add(off, 2n), L)))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.be16(v), B.Octets.of_list(B.drop(2n, B.drop(off, L))))), B.append(B.Octets.to_list(B.Octets.be16(v)), B.Octets.to_list(B.Octets.of_list(B.drop(2n, B.drop(off, L))))), BL.octets_append_list(B.Octets.be16(v), B.Octets.of_list(B.drop(2n, B.drop(off, L))))) : {B.append(B.Octets.to_list(B.Octets.of_list(B.take(off, L))), _) == B.append(B.mask(B.take(off, L)), B.append(B.mask(B.be16(v)), B.mask(B.drop(Nat.add(off, 2n), L)))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.take(off, L))), B.mask(B.take(off, L)), BL.octets_to_of(B.take(off, L))) : {B.append(_, B.append(B.Octets.to_list(B.Octets.be16(v)), B.Octets.to_list(B.Octets.of_list(B.drop(2n, B.drop(off, L)))))) == B.append(B.mask(B.take(off, L)), B.append(B.mask(B.be16(v)), B.mask(B.drop(Nat.add(off, 2n), L)))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.be16(v))), B.mask(B.be16(v)), BL.octets_to_of(B.be16(v))) : {B.append(B.mask(B.take(off, L)), B.append(_, B.Octets.to_list(B.Octets.of_list(B.drop(2n, B.drop(off, L)))))) == B.append(B.mask(B.take(off, L)), B.append(B.mask(B.be16(v)), B.mask(B.drop(Nat.add(off, 2n), L)))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.drop(2n, B.drop(off, L)))), B.mask(B.drop(2n, B.drop(off, L))), BL.octets_to_of(B.drop(2n, B.drop(off, L)))) : {B.append(B.mask(B.take(off, L)), B.append(B.mask(B.be16(v)), _)) == B.append(B.mask(B.take(off, L)), B.append(B.mask(B.be16(v)), B.mask(B.drop(Nat.add(off, 2n), L)))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.drop(2n, B.drop(off, L)), B.drop(Nat.add(off, 2n), L), os.drop_drop(off, 2n, L)) : {B.append(B.mask(B.take(off, L)), B.append(B.mask(B.be16(v)), B.mask(_))) == B.append(B.mask(B.take(off, L)), B.append(B.mask(B.be16(v)), B.mask(B.drop(Nat.add(off, 2n), L)))) : List<&2, U32>}
  {==}

def os.g_add_assoc(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +b: U32, +c: U32, +ha: {U32.is_le(a, 65535) == True{} : Bool}, +hb: {U32.is_le(b, 65535) == True{} : Bool}, +hc: {U32.is_le(c, 65535) == True{} : Bool}) -> {K.inet_add(K.inet_add(a, b), c) == K.inet_add(a, K.inet_add(b, c)) : U32}:
  UL.u32_value_eq(K.inet_add(K.inet_add(a, b), c), K.inet_add(a, K.inet_add(b, c)), os.g_add_assoc.v(d, hd, hD, hE, a, b, c, os.fit_of(d, hE, a, ha), os.fit_of(d, hE, b, hb), os.fit_of(d, hE, c, hc)))

def os.g_complement(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +a: U32, +ha: {U32.is_le(a, 65535) == True{} : Bool}) -> {K.inet_add(a, K.inet_finish(a)) == 65535 : U32}:
  UL.u32_value_eq(K.inet_add(a, K.inet_finish(a)), 65535, os.g_complement.v(d, hd, hD, hE, a, os.fit_of(d, hE, a, ha)))

def os.g_update_add(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +acc: U32, +w: U32, +o: B.Octets, +ha: {U32.is_le(acc, 65535) == True{} : Bool}, +hw: {U32.is_le(w, 65535) == True{} : Bool}) -> {K.inet_update(K.inet_add(acc, w), o) == K.inet_add(K.inet_update(acc, o), w) : U32}:
  UL.u32_value_eq(K.inet_update(K.inet_add(acc, w), o), K.inet_add(K.inet_update(acc, o), w), os.g_update_add.v(d, hd, hD, hE, acc, w, o, os.fit_of(d, hE, acc, ha), os.fit_of(d, hE, w, hw)))

def os.g_update_comm(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +acc: U32, +x: B.Octets, +y: B.Octets, +h: {U32.is_le(acc, 65535) == True{} : Bool}) -> {K.inet_update(K.inet_update(acc, x), y) == K.inet_update(K.inet_update(acc, y), x) : U32}:
  UL.u32_value_eq(K.inet_update(K.inet_update(acc, x), y), K.inet_update(K.inet_update(acc, y), x), os.g_update_comm.v(d, hd, hD, hE, acc, x, y, os.fit_of(d, hE, acc, h)))

def os.g_sum_swap(+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}, +x: B.Octets, +y: B.Octets, +ex: {K.inet_even(x) == True{} : Bool}, +ey: {K.inet_even(y) == True{} : Bool}) -> {K.inet_sum(B.Octets.append(x, y)) == K.inet_sum(B.Octets.append(y, x)) : U32}:
  UL.u32_value_eq(K.inet_sum(B.Octets.append(x, y)), K.inet_sum(B.Octets.append(y, x)), os.g_sum_swap.v(d, hd, hD, hE, x, y, ex, ey))
