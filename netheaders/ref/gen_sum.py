# Writes netheaders/proof_ones.bend (the lemmas behind LAWS_sum.bend),
# PROOF_sum.bend and PROOF_ipv4.bend; run from netheaders/:
#   python3 ref/gen_sum.py           rewrite the three files
#   python3 ref/gen_sum.py --check   only check that they are up to date The deep patterns are generated; the
# reasoning is in the comments it writes out.
import sys
OUTS = {}
def emit(path, text):
    OUTS[path] = text
P = []
w = P.append
w(r'''# Lemmas for the Internet checksum's one's complement arithmetic
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
''')
w(chr(10))
w(r'''# Contradictions

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
''')
w(r'''
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
''')
def pat32(n):
    return "U32{" + "".join("WCon{%s%d, " % (n, i) for i in range(32)) + "WNil{}" + "}" * 32 + "}"

ONES = "Word.not(16n, Word.zero(16n))"
V = "U32.to_nat"
def v(x): return f"U32.to_nat({x})"
def w16(x): return f"Word.to_nat(16n, {x})"
DBL1 = "UN.U32Nat.dbl(16n, 1n)"
TWO = "Nat.add(1n, 1n)"
D_ARGS = "+d: Nat, +hd: {Nat.is_le(1n, d) == True{} : Bool}, +hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}, +hE: {U32.to_nat(65535) == d : Nat}"
DA = "d, hd, hD, hE"
def fits(x): return "{Nat.is_le(U32.to_nat(%s), d) == True{} : Bool}" % x


va, vb = v("a"), v("b")
AB = "U32.add(a, b)"
AND = f"U32.and({AB}, 65535)"
SHR = f"U32.shrn({AB}, 16n)"
X = f"Nat.add({va}, {vb})"
HD = "+hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}"
HE = "+hE: {U32.to_nat(65535) == d : Nat}"
HDD = "+hd: {Nat.is_le(1n, d) == True{} : Bool}"
def le(x, y): return "{Nat.is_le(%s, %s) == True{} : Bool}" % (x, y)
VX = v("x")
VY = v("y")

HD = "+hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}"
HE = "+hE: {U32.to_nat(65535) == d : Nat}"
HDD = "+hd: {Nat.is_le(1n, d) == True{} : Bool}"
DPAR = f"+d: Nat, {HDD}, {HD}, {HE}"
def le(x, y): return "{Nat.is_le(%s, %s) == True{} : Bool}" % (x, y)
def pat(n, k):
    s = "".join("WCon{%s%d, " % (n, i) for i in range(k))
    tail = "WNil{}" if k == 32 else n + "h"
    return "U32{" + s + tail + "}" * k + "}"
L = "List<&2, U32>"
def tl(x): return f"B.Octets.to_list({x})"
def ws(x): return f"os.ws({x})"
BE = "B.Octets.be16"



# ---- gen_part3.py

w(f"""
# Splitting a word into its 16-bit halves (deep patterns, then computation)

def os.split(s: U32) -> {{s == os.mk(os.lo16(s), os.hi16(s)) : U32}}:
  match s:
    case {pat32("s")}:
      {{==}}

def os.and_mask(s: U32) -> {{U32.and(65535, s) == os.mk(os.lo16(s), Word.zero(16n)) : U32}}:
  match s:
    case {pat32("s")}:
      {{==}}

def os.shr_mask(s: U32) -> {{U32.shrn(s, 16n) == os.mk(os.hi16(s), Word.zero(16n)) : U32}}:
  match s:
    case {pat32("s")}:
      {{==}}

# The values of the halves

def os.v_split(+s: U32) -> {{{v("s")} == Nat.add({w16("os.lo16(s)")}, UN.U32Nat.dbl(16n, {w16("os.hi16(s)")})) : Nat}}:
  %Equal.sym(U32, s, os.mk(os.lo16(s), os.hi16(s)), os.split(s)) : {{U32.to_nat(_) == Nat.add({w16("os.lo16(s)")}, UN.U32Nat.dbl(16n, {w16("os.hi16(s)")})) : Nat}}
  os.mk_value(os.lo16(s), os.hi16(s))

def os.v_and(+s: U32) -> {{{v("U32.and(s, 65535)")} == {w16("os.lo16(s)")} : Nat}}:
  %os.and_comm(65535, s) : {{U32.to_nat(_) == {w16("os.lo16(s)")} : Nat}}
  %Equal.sym(U32, U32.and(65535, s), os.mk(os.lo16(s), Word.zero(16n)), os.and_mask(s)) : {{U32.to_nat(_) == {w16("os.lo16(s)")} : Nat}}
  os.mk_zero_value(os.lo16(s))

def os.v_shr(+s: U32) -> {{{v("U32.shrn(s, 16n)")} == {w16("os.hi16(s)")} : Nat}}:
  %Equal.sym(U32, U32.shrn(s, 16n), os.mk(os.hi16(s), Word.zero(16n)), os.shr_mask(s)) : {{U32.to_nat(_) == {w16("os.hi16(s)")} : Nat}}
  os.mk_zero_value(os.hi16(s))

# The two facts about d = 2^16 - 1, proved without expanding the number

def os.hD() -> {{1n+{w16(ONES)} == {DBL1} : Nat}}:
  %os.add_zero({w16(ONES)}) : {{1n+_ == {DBL1} : Nat}}
  %UL.word_zero_value(16n) : {{1n+Nat.add({w16(ONES)}, _) == {DBL1} : Nat}}
  UL.word_not_value(16n, Word.zero(16n))

def os.e65535() -> {{65535 == os.mk({ONES}, Word.zero(16n)) : U32}}:
  {{==}}

def os.hE() -> {{{v("65535")} == {w16(ONES)} : Nat}}:
  %Equal.sym(U32, 65535, os.mk({ONES}, Word.zero(16n)), os.e65535()) : {{U32.to_nat(_) == {w16(ONES)} : Nat}}
  os.mk_zero_value({ONES})

def os.hd() -> {{Nat.is_le(1n, {w16(ONES)}) == True{{}} : Bool}}:
  {{==}}

# Bounds: a U32 of at most 65535 is a value of at most d

def os.fit_of(+d: Nat, +hE: {{U32.to_nat(65535) == d : Nat}}, +a: U32, h: {{U32.is_le(a, 65535) == True{{}} : Bool}}) -> {fits("a")}:
  %hE : {{Nat.is_le(U32.to_nat(a), _) == True{{}} : Bool}}
  %UL.u32_le_value(a, 65535) : {{_ == True{{}} : Bool}}
  h

def os.fit_to(+d: Nat, +hE: {{U32.to_nat(65535) == d : Nat}}, +a: U32, h: {fits("a")}) -> {{U32.is_le(a, 65535) == True{{}} : Bool}}:
  %Equal.sym(Bool, U32.is_le(a, 65535), Nat.is_le(U32.to_nat(a), U32.to_nat(65535)), UL.u32_le_value(a, 65535)) : {{_ == True{{}} : Bool}}
  %Equal.sym(Nat, U32.to_nat(65535), d, hE) : {{Nat.is_le(U32.to_nat(a), _) == True{{}} : Bool}}
  h

def os.w16_le(+d: Nat, +hD: {{1n+d == {DBL1} : Nat}}, +x: Word(16n)) -> {{Nat.is_le({w16("x")}, d) == True{{}} : Bool}}:
  %os.lt_succ({w16("x")}, d) : {{_ == True{{}} : Bool}}
  %Equal.sym(Nat, 1n+d, {DBL1}, hD) : {{Nat.is_lt({w16("x")}, _) == True{{}} : Bool}}
  UL.word_value_lt(16n, x)

def os.d_lt(+d: Nat, +hD: {{1n+d == {DBL1} : Nat}}) -> {{Nat.is_lt(d, {DBL1}) == True{{}} : Bool}}:
  %hD : {{Nat.is_lt(d, _) == True{{}} : Bool}}
  Equal.trans(Bool, Nat.is_lt(d, 1n+d), Nat.is_le(d, d), True{{}}, os.lt_succ(d, d), os.le_refl(d))

# L + 2^16 H <= d: H = 0
def os.hi_zero(+d: Nat, +hD: {{1n+d == {DBL1} : Nat}}, +L: Nat, +H: Nat, +h: {{Nat.is_le(Nat.add(L, UN.U32Nat.dbl(16n, H)), d) == True{{}} : Bool}}) -> {{H == 0n : Nat}}:
  os.lt_one(H, Equal.trans(Bool, Nat.is_lt(H, 1n), Nat.is_lt(UN.U32Nat.dbl(16n, H), {DBL1}), True{{}}, Equal.sym(Bool, Nat.is_lt(UN.U32Nat.dbl(16n, H), {DBL1}), Nat.is_lt(H, 1n), UL.dbl_lt(16n, H, 1n)), os.le_lt(UN.U32Nat.dbl(16n, H), d, {DBL1}, os.le_trans(UN.U32Nat.dbl(16n, H), Nat.add(L, UN.U32Nat.dbl(16n, H)), d, os.le_add_l(L, UN.U32Nat.dbl(16n, H)), h), os.d_lt(d, hD))))

# a value of at most d is the value of its low half
def os.fit_lo(+d: Nat, +hD: {{1n+d == {DBL1} : Nat}}, +s: U32, +h: {fits("s")}) -> {{{v("s")} == {w16("os.lo16(s)")} : Nat}}:
  +hz = os.hi_zero(d, hD, {w16("os.lo16(s)")}, {w16("os.hi16(s)")}, Equal.trans(Bool, Nat.is_le(Nat.add({w16("os.lo16(s)")}, UN.U32Nat.dbl(16n, {w16("os.hi16(s)")})), d), Nat.is_le({v("s")}, d), True{{}}, Equal.cong(Nat, Bool, z => Nat.is_le(z, d), Nat.add({w16("os.lo16(s)")}, UN.U32Nat.dbl(16n, {w16("os.hi16(s)")})), {v("s")}, Equal.sym(Nat, {v("s")}, Nat.add({w16("os.lo16(s)")}, UN.U32Nat.dbl(16n, {w16("os.hi16(s)")})), os.v_split(s))), h))
  %Equal.sym(Nat, {v("s")}, Nat.add({w16("os.lo16(s)")}, UN.U32Nat.dbl(16n, {w16("os.hi16(s)")})), os.v_split(s)) : {{_ == {w16("os.lo16(s)")} : Nat}}
  %Equal.sym(Nat, {w16("os.hi16(s)")}, 0n, hz) : {{Nat.add({w16("os.lo16(s)")}, UN.U32Nat.dbl(16n, _)) == {w16("os.lo16(s)")} : Nat}}
  %Equal.sym(Nat, UN.U32Nat.dbl(16n, 0n), 0n, UL.dbl_zero(16n)) : {{Nat.add({w16("os.lo16(s)")}, _) == {w16("os.lo16(s)")} : Nat}}
  os.add_zero({w16("os.lo16(s)")})
""")


# ---- gen_part4.py
w(f"""
# No wrap: the sum of two values of at most d fits a word

def os.fit65535(+d: Nat, {HE}) -> {le(v("65535"), "d")}:
  %Equal.sym(Nat, {v("65535")}, d, hE) : {{Nat.is_le(_, d) == True{{}} : Bool}}
  os.le_refl(d)

def os.lo65535(+d: Nat, {HD}, {HE}) -> {{{w16("os.lo16(65535)")} == d : Nat}}:
  Equal.trans(Nat, {w16("os.lo16(65535)")}, {v("65535")}, d, Equal.sym(Nat, {v("65535")}, {w16("os.lo16(65535)")}, os.fit_lo(d, hD, 65535, os.fit65535(d, hE))), hE)

def os.nowrap_bound(+d: Nat, {HD}, {HE}, +a: U32, +b: U32, +ha: {fits("a")}, +hb: {fits("b")}) -> {le(X, v("os.mk(os.lo16(65535), os.lo16(65535))"))}:
  %Equal.sym(Nat, {v("os.mk(os.lo16(65535), os.lo16(65535))")}, Nat.add({w16("os.lo16(65535)")}, UN.U32Nat.dbl(16n, {w16("os.lo16(65535)")})), os.mk_value(os.lo16(65535), os.lo16(65535))) : {{Nat.is_le({X}, _) == True{{}} : Bool}}
  %Equal.sym(Nat, {w16("os.lo16(65535)")}, d, os.lo65535(d, hD, hE)) : {{Nat.is_le({X}, Nat.add(_, UN.U32Nat.dbl(16n, _))) == True{{}} : Bool}}
  os.le_add_mono({va}, {vb}, d, UN.U32Nat.dbl(16n, d), ha, os.le_trans({vb}, d, UN.U32Nat.dbl(16n, d), hb, os.le_dbl(16n, d)))

def os.nowrap(+d: Nat, {HD}, {HE}, +a: U32, +b: U32, +ha: {fits("a")}, +hb: {fits("b")}) -> {{{v(AB)} == {X} : Nat}}:
  UL.u32_add_value(a, b, os.mk(os.lo16(65535), os.lo16(65535)), os.nowrap_bound(d, hD, hE, a, b, ha, hb))

# x and y with values X and Y, X + Y <= d: the sum of the values is at most 65535's
def os.sum_bound(+d: Nat, {HE}, +x: U32, +y: U32, +X: Nat, +Y: Nat, +ex: {{{VX} == X : Nat}}, +ey: {{{VY} == Y : Nat}}, +h: {le("Nat.add(X, Y)", "d")}) -> {le(f"Nat.add({VX}, {VY})", v("65535"))}:
  %Equal.sym(Nat, {v("65535")}, d, hE) : {{Nat.is_le(Nat.add({VX}, {VY}), _) == True{{}} : Bool}}
  %Equal.sym(Nat, {VX}, X, ex) : {{Nat.is_le(Nat.add(_, {VY}), d) == True{{}} : Bool}}
  %Equal.sym(Nat, {VY}, Y, ey) : {{Nat.is_le(Nat.add(X, _), d) == True{{}} : Bool}}
  h

def os.le_add0(+L: Nat, +d: Nat, +h: {le("L", "d")}) -> {le("Nat.add(L, 0n)", "d")}:
  %Equal.sym(Nat, Nat.add(L, 0n), L, os.add_zero(L)) : {{Nat.is_le(_, d) == True{{}} : Bool}}
  h

def os.le_add1(+L: Nat, +d: Nat, +h: {le("1n+L", "d")}) -> {le("Nat.add(L, 1n)", "d")}:
  %os.add_comm(1n, L) : {{Nat.is_le(_, d) == True{{}} : Bool}}
  h

# 2d < 2^16 + 2^16
def os.two_lt(+d: Nat, {HD}) -> {{Nat.is_lt(Nat.add(d, d), UN.U32Nat.dbl(16n, {TWO})) == True{{}} : Bool}}:
  %Equal.sym(Nat, UN.U32Nat.dbl(16n, {TWO}), Nat.add({DBL1}, {DBL1}), UL.dbl_add(16n, 1n, 1n)) : {{Nat.is_lt(Nat.add(d, d), _) == True{{}} : Bool}}
  %hD : {{Nat.is_lt(Nat.add(d, d), Nat.add(_, _)) == True{{}} : Bool}}
  Equal.trans(Bool, Nat.is_lt(Nat.add(d, d), 1n+Nat.add(d, 1n+d)), Nat.is_le(Nat.add(d, d), Nat.add(d, 1n+d)), True{{}}, os.lt_succ(Nat.add(d, d), Nat.add(d, 1n+d)), Equal.trans(Bool, Nat.is_le(Nat.add(d, d), Nat.add(d, 1n+d)), Nat.is_le(d, 1n+d), True{{}}, os.le_cancel_l(d, d, 1n+d), os.le_succ_r(d)))

# X = L + 2^16 H <= 2d: H < 2
def os.two_bound(+d: Nat, {HD}, +L: Nat, +H: Nat, +X: Nat, +eS: {{X == Nat.add(L, UN.U32Nat.dbl(16n, H)) : Nat}}, +hab: {le("X", "Nat.add(d, d)")}) -> {{Nat.is_lt(H, {TWO}) == True{{}} : Bool}}:
  Equal.trans(Bool, Nat.is_lt(H, {TWO}), Nat.is_lt(UN.U32Nat.dbl(16n, H), UN.U32Nat.dbl(16n, {TWO})), True{{}}, Equal.sym(Bool, Nat.is_lt(UN.U32Nat.dbl(16n, H), UN.U32Nat.dbl(16n, {TWO})), Nat.is_lt(H, {TWO}), UL.dbl_lt(16n, H, {TWO})), os.le_lt(UN.U32Nat.dbl(16n, H), Nat.add(d, d), UN.U32Nat.dbl(16n, {TWO}), os.le_trans(UN.U32Nat.dbl(16n, H), X, Nat.add(d, d), Equal.trans(Bool, Nat.is_le(UN.U32Nat.dbl(16n, H), X), Nat.is_le(UN.U32Nat.dbl(16n, H), Nat.add(L, UN.U32Nat.dbl(16n, H))), True{{}}, Equal.cong(Nat, Bool, z => Nat.is_le(UN.U32Nat.dbl(16n, H), z), X, Nat.add(L, UN.U32Nat.dbl(16n, H)), eS), os.le_add_l(L, UN.U32Nat.dbl(16n, H))), hab), os.two_lt(d, hD)))

# X = L + 2^16 <= 2d: 1 + L <= d
def os.h1L(+d: Nat, {HD}, +L: Nat, +X: Nat, +eS: {{X == Nat.add(L, {DBL1}) : Nat}}, +hab: {le("X", "Nat.add(d, d)")}) -> {le("1n+L", "d")}:
  %os.le_cancel_l(d, 1n+L, d) : {{_ == True{{}} : Bool}}
  %Equal.sym(Nat, Nat.add(d, 1n+L), 1n+Nat.add(d, L), os.add_succ(d, L)) : {{Nat.is_le(_, Nat.add(d, d)) == True{{}} : Bool}}
  %os.add_comm(L, d) : {{Nat.is_le(1n+_, Nat.add(d, d)) == True{{}} : Bool}}
  %os.add_succ(L, d) : {{Nat.is_le(_, Nat.add(d, d)) == True{{}} : Bool}}
  %Equal.sym(Nat, 1n+d, {DBL1}, hD) : {{Nat.is_le(Nat.add(L, _), Nat.add(d, d)) == True{{}} : Bool}}
  %eS : {{Nat.is_le(_, Nat.add(d, d)) == True{{}} : Bool}}
  hab

# The bridge: inet_add on two values of at most d is rep of their sum. The
# sum s (no wrap) is L + 2^16 H with L <= d and H < 2; the mask reads L and
# the shift H, and inet_add answers L + H.
def os.add_value.go(H: Nat, +d: Nat, {HDD}, {HD}, {HE}, +a: U32, +b: U32, +L: Nat, +eL: {{{v(AND)} == L : Nat}}, +eH: {{{v(SHR)} == H : Nat}}, +eS: {{{X} == Nat.add(L, UN.U32Nat.dbl(16n, H)) : Nat}}, +hL: {le("L", "d")}, +hab: {le(X, "Nat.add(d, d)")}, +hlt: {{Nat.is_lt(H, {TWO}) == True{{}} : Bool}}) -> {{{v("K.inet_add(a, b)")} == os.rep(d, {X}) : Nat}}:
  match H:
    case 0n:
      %Equal.sym(Nat, {v(f"U32.add({AND}, {SHR})")}, Nat.add({v(AND)}, {v(SHR)}), UL.u32_add_value({AND}, {SHR}, 65535, os.sum_bound(d, hE, {AND}, {SHR}, L, 0n, eL, eH, os.le_add0(L, d, hL)))) : {{_ == os.rep(d, {X}) : Nat}}
      %Equal.sym(Nat, {v(AND)}, L, eL) : {{Nat.add(_, {v(SHR)}) == os.rep(d, {X}) : Nat}}
      %Equal.sym(Nat, {v(SHR)}, 0n, eH) : {{Nat.add(L, _) == os.rep(d, {X}) : Nat}}
      %Equal.sym(Nat, {X}, Nat.add(L, UN.U32Nat.dbl(16n, 0n)), eS) : {{Nat.add(L, 0n) == os.rep(d, _) : Nat}}
      %Equal.sym(Nat, UN.U32Nat.dbl(16n, 0n), 0n, UL.dbl_zero(16n)) : {{Nat.add(L, 0n) == os.rep(d, Nat.add(L, _)) : Nat}}
      %Equal.sym(Nat, Nat.add(L, 0n), L, os.add_zero(L)) : {{_ == os.rep(d, _) : Nat}}
      Equal.sym(Nat, os.rep(d, L), L, os.rep_small(d, L, hL))
    case 1n+ +H1:
      match H1:
        case 0n:
          +h1 = os.h1L(d, hD, L, {X}, eS, hab)
          %Equal.sym(Nat, {v(f"U32.add({AND}, {SHR})")}, Nat.add({v(AND)}, {v(SHR)}), UL.u32_add_value({AND}, {SHR}, 65535, os.sum_bound(d, hE, {AND}, {SHR}, L, 1n, eL, eH, os.le_add1(L, d, h1)))) : {{_ == os.rep(d, {X}) : Nat}}
          %Equal.sym(Nat, {v(AND)}, L, eL) : {{Nat.add(_, {v(SHR)}) == os.rep(d, {X}) : Nat}}
          %Equal.sym(Nat, {v(SHR)}, 1n, eH) : {{Nat.add(L, _) == os.rep(d, {X}) : Nat}}
          %Equal.sym(Nat, {X}, Nat.add(L, {DBL1}), eS) : {{Nat.add(L, 1n) == os.rep(d, _) : Nat}}
          %hD : {{Nat.add(L, 1n) == os.rep(d, Nat.add(L, _)) : Nat}}
          %Equal.sym(Nat, Nat.add(L, 1n+d), 1n+Nat.add(L, d), os.add_succ(L, d)) : {{Nat.add(L, 1n) == os.rep(d, _) : Nat}}
          %Equal.sym(Nat, os.rep(d, Nat.add(1n+L, d)), os.rep(d, 1n+L), os.rep_period1(d, L, hd)) : {{Nat.add(L, 1n) == _ : Nat}}
          %Equal.sym(Nat, os.rep(d, 1n+L), 1n+L, os.rep_small(d, 1n+L, h1)) : {{Nat.add(L, 1n) == _ : Nat}}
          os.add_comm(L, 1n)
        case 1n+ +h:
          Empty.absurd({{{v("K.inet_add(a, b)")} == os.rep(d, {X}) : Nat}}, os.ft(Equal.trans(Bool, False{{}}, Nat.is_lt(h, 0n), True{{}}, Equal.sym(Bool, Nat.is_lt(h, 0n), False{{}}, os.lt_zero(h)), hlt)))

def os.add_value(+d: Nat, {HDD}, {HD}, {HE}, +a: U32, +b: U32, +ha: {fits("a")}, +hb: {fits("b")}) -> {{{v("K.inet_add(a, b)")} == os.rep(d, {X}) : Nat}}:
  +eS = Equal.trans(Nat, {X}, {v(AB)}, Nat.add({w16(f"os.lo16({AB})")}, UN.U32Nat.dbl(16n, {w16(f"os.hi16({AB})")})), Equal.sym(Nat, {v(AB)}, {X}, os.nowrap(d, hD, hE, a, b, ha, hb)), os.v_split({AB}))
  +hab = os.le_add_mono({va}, {vb}, d, d, ha, hb)
  os.add_value.go({w16(f"os.hi16({AB})")}, d, hd, hD, hE, a, b, {w16(f"os.lo16({AB})")}, os.v_and({AB}), os.v_shr({AB}), eS, os.w16_le(d, hD, os.lo16({AB})), hab, os.two_bound(d, hD, {w16(f"os.lo16({AB})")}, {w16(f"os.hi16({AB})")}, {X}, eS, hab))

# inet_add keeps values at most d
def os.add_fits(+d: Nat, {HDD}, {HD}, {HE}, +a: U32, +b: U32, +ha: {fits("a")}, +hb: {fits("b")}) -> {fits("K.inet_add(a, b)")}:
  %Equal.sym(Nat, {v("K.inet_add(a, b)")}, os.rep(d, {X}), os.add_value(d, hd, hD, hE, a, b, ha, hb)) : {{Nat.is_le(_, d) == True{{}} : Bool}}
  os.rep_le(d, {X}, hd)
""")


# ---- gen_part5.py
w(f"""
# The sum of a byte list: rep of the plain sum of its 16-bit words

# the plain sum of the 16-bit words of a byte list, an odd final byte padded
def os.ws(xs: {L}) -> Nat:
  match xs:
    case Nil{{}}:
      0n
    case Con{{a, Nil{{}}}}:
      U32.to_nat(K.inet_word(a, 0))
    case Con{{a, Con{{b, t}}}}:
      Nat.add(U32.to_nat(K.inet_word(a, b)), os.ws(t))

def os.w8s(a: U32, b: U32) -> Word(16n):
  match a b:
    case U32{{x}} U32{{y}}:
      W.W64.bits.cat(8n, 8n, W.W64.bits.lo(8n, 24n, y), W.W64.bits.lo(8n, 24n, x))

def os.word_mk(a: U32, b: U32) -> {{K.inet_word(a, b) == os.mk(os.w8s(a, b), Word.zero(16n)) : U32}}:
  match a b:
    case {pat("a", 8)} {pat("b", 8)}:
      {{==}}

def os.word_fits(+d: Nat, {HD}, +a: U32, +b: U32) -> {fits("K.inet_word(a, b)")}:
  %Equal.sym(U32, K.inet_word(a, b), os.mk(os.w8s(a, b), Word.zero(16n)), os.word_mk(a, b)) : {{Nat.is_le(U32.to_nat(_), d) == True{{}} : Bool}}
  %Equal.sym(Nat, {v("os.mk(os.w8s(a, b), Word.zero(16n))")}, {w16("os.w8s(a, b)")}, os.mk_zero_value(os.w8s(a, b))) : {{Nat.is_le(_, d) == True{{}} : Bool}}
  os.w16_le(d, hD, os.w8s(a, b))

def os.fold(xs: {L}, {DPAR}, +acc: U32, +h: {fits("acc")}) -> {{{v("K.inet_sum.list(xs, acc)")} == os.rep(d, Nat.add({v("acc")}, os.ws(xs))) : Nat}}:
  match xs:
    case Nil{{}}:
      %Equal.sym(Nat, Nat.add({v("acc")}, 0n), {v("acc")}, os.add_zero({v("acc")})) : {{{v("acc")} == os.rep(d, _) : Nat}}
      Equal.sym(Nat, os.rep(d, {v("acc")}), {v("acc")}, os.rep_small(d, {v("acc")}, h))
    case Con{{+a, Nil{{}}}}:
      os.add_value(d, hd, hD, hE, acc, K.inet_word(a, 0), h, os.word_fits(d, hD, a, 0))
    case Con{{+a, Con{{+b, +t}}}}:
      %Equal.sym(Nat, {v("K.inet_sum.list(t, K.inet_add(acc, K.inet_word(a, b)))")}, os.rep(d, Nat.add({v("K.inet_add(acc, K.inet_word(a, b))")}, os.ws(t))), os.fold(t, d, hd, hD, hE, K.inet_add(acc, K.inet_word(a, b)), os.add_fits(d, hd, hD, hE, acc, K.inet_word(a, b), h, os.word_fits(d, hD, a, b)))) : {{_ == os.rep(d, Nat.add({v("acc")}, Nat.add({v("K.inet_word(a, b)")}, os.ws(t)))) : Nat}}
      %Equal.sym(Nat, {v("K.inet_add(acc, K.inet_word(a, b))")}, os.rep(d, Nat.add({v("acc")}, {v("K.inet_word(a, b)")})), os.add_value(d, hd, hD, hE, acc, K.inet_word(a, b), h, os.word_fits(d, hD, a, b))) : {{os.rep(d, Nat.add(_, os.ws(t))) == os.rep(d, Nat.add({v("acc")}, Nat.add({v("K.inet_word(a, b)")}, os.ws(t)))) : Nat}}
      %Equal.sym(Nat, os.rep(d, Nat.add(os.rep(d, Nat.add({v("acc")}, {v("K.inet_word(a, b)")})), os.ws(t))), os.rep(d, Nat.add(Nat.add({v("acc")}, {v("K.inet_word(a, b)")}), os.ws(t))), os.rep_fold(d, Nat.add({v("acc")}, {v("K.inet_word(a, b)")}), os.ws(t), hd)) : {{_ == os.rep(d, Nat.add({v("acc")}, Nat.add({v("K.inet_word(a, b)")}, os.ws(t)))) : Nat}}
      %Equal.sym(Nat, Nat.add(Nat.add({v("acc")}, {v("K.inet_word(a, b)")}), os.ws(t)), Nat.add({v("acc")}, Nat.add({v("K.inet_word(a, b)")}, os.ws(t))), os.add_assoc({v("acc")}, {v("K.inet_word(a, b)")}, os.ws(t))) : {{os.rep(d, _) == os.rep(d, Nat.add({v("acc")}, Nat.add({v("K.inet_word(a, b)")}, os.ws(t)))) : Nat}}
      {{==}}

def os.fold_fits(+xs: {L}, {DPAR}, +acc: U32, +h: {fits("acc")}) -> {fits("K.inet_sum.list(xs, acc)")}:
  %Equal.sym(Nat, {v("K.inet_sum.list(xs, acc)")}, os.rep(d, Nat.add({v("acc")}, os.ws(xs))), os.fold(xs, d, hd, hD, hE, acc, h)) : {{Nat.is_le(_, d) == True{{}} : Bool}}
  os.rep_le(d, Nat.add({v("acc")}, os.ws(xs)), hd)

# the words of xs ++ ys, xs of even length
def os.ws_append(xs: {L}, +ys: {L}, e: {{K.inet_even.list(xs) == True{{}} : Bool}}) -> {{os.ws(B.append(xs, ys)) == Nat.add(os.ws(xs), os.ws(ys)) : Nat}}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+a, Nil{{}}}}:
      Empty.absurd({{os.ws(B.append([a], ys)) == Nat.add(os.ws([a]), os.ws(ys)) : Nat}}, os.ft(e))
    case Con{{+a, Con{{+b, +t}}}}:
      %Equal.sym(Nat, os.ws(B.append(t, ys)), Nat.add(os.ws(t), os.ws(ys)), os.ws_append(t, ys, e)) : {{Nat.add({v("K.inet_word(a, b)")}, _) == Nat.add(Nat.add({v("K.inet_word(a, b)")}, os.ws(t)), os.ws(ys)) : Nat}}
      Equal.sym(Nat, Nat.add(Nat.add({v("K.inet_word(a, b)")}, os.ws(t)), os.ws(ys)), Nat.add({v("K.inet_word(a, b)")}, Nat.add(os.ws(t), os.ws(ys))), os.add_assoc({v("K.inet_word(a, b)")}, os.ws(t), os.ws(ys)))

# Even lengths

def os.ev(n: Nat) -> Bool:
  match n:
    case 0n:
      True{{}}
    case 1n+p:
      match p:
        case 0n:
          False{{}}
        case 1n+q:
          os.ev(q)

def os.even_len(xs: {L}) -> {{K.inet_even.list(xs) == os.ev(B.len(xs)) : Bool}}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{a, Nil{{}}}}:
      {{==}}
    case Con{{a, Con{{b, t}}}}:
      os.even_len(t)

def os.ev_double(k: Nat) -> {{os.ev(Nat.double(k)) == True{{}} : Bool}}:
  match k:
    case 0n:
      {{==}}
    case 1n+ +p:
      os.ev_double(p)

# the first 2k bytes of o (if o has them) are an even number
def os.even_take(+o: B.Octets, +k: Nat, +h: {{Nat.is_le(Nat.double(k), B.Octets.len(o)) == True{{}} : Bool}}) -> {{K.inet_even(B.Octets.take(Nat.double(k), o)) == True{{}} : Bool}}:
  %Equal.sym(Bool, K.inet_even.list({tl("B.Octets.take(Nat.double(k), o)")}), os.ev(B.len({tl("B.Octets.take(Nat.double(k), o)")})), os.even_len({tl("B.Octets.take(Nat.double(k), o)")})) : {{_ == True{{}} : Bool}}
  %BL.octets_len_list(B.Octets.take(Nat.double(k), o)) : {{os.ev(_) == True{{}} : Bool}}
  %Equal.sym(Nat, B.Octets.len(B.Octets.take(Nat.double(k), o)), Nat.double(k), BL.octets_len_take_le(Nat.double(k), o, h)) : {{os.ev(_) == True{{}} : Bool}}
  os.ev_double(k)

def os.be16_even.m(v: U32) -> {{K.inet_even.list(B.mask(B.be16(v))) == True{{}} : Bool}}:
  match v:
    case U32{{x}}:
      {{==}}

def os.be16_even(+v: U32) -> {{K.inet_even.list({tl(BE + "(v)")}) == True{{}} : Bool}}:
  %Equal.sym({L}, {tl("B.Octets.of_list(B.be16(v))")}, B.mask(B.be16(v)), BL.octets_to_of(B.be16(v))) : {{K.inet_even.list(_) == True{{}} : Bool}}
  os.be16_even.m(v)

# The checksum: the complement of the sum, so c + S = d

def os.finish_mk(t: U32) -> {{K.inet_finish(t) == os.mk(Word.not(16n, os.lo16(t)), Word.zero(16n)) : U32}}:
  match t:
    case {pat32("t")}:
      {{==}}

def os.finish_fits(+d: Nat, {HD}, +t: U32) -> {fits("K.inet_finish(t)")}:
  %Equal.sym(U32, K.inet_finish(t), os.mk(Word.not(16n, os.lo16(t)), Word.zero(16n)), os.finish_mk(t)) : {{Nat.is_le(U32.to_nat(_), d) == True{{}} : Bool}}
  %Equal.sym(Nat, {v("os.mk(Word.not(16n, os.lo16(t)), Word.zero(16n))")}, {w16("Word.not(16n, os.lo16(t))")}, os.mk_zero_value(Word.not(16n, os.lo16(t)))) : {{Nat.is_le(_, d) == True{{}} : Bool}}
  os.w16_le(d, hD, Word.not(16n, os.lo16(t)))

def os.finish_value(+d: Nat, {HD}, +t: U32, +h: {fits("t")}) -> {{Nat.add({v("K.inet_finish(t)")}, {v("t")}) == d : Nat}}:
  %Equal.sym(U32, K.inet_finish(t), os.mk(Word.not(16n, os.lo16(t)), Word.zero(16n)), os.finish_mk(t)) : {{Nat.add(U32.to_nat(_), {v("t")}) == d : Nat}}
  %Equal.sym(Nat, {v("os.mk(Word.not(16n, os.lo16(t)), Word.zero(16n))")}, {w16("Word.not(16n, os.lo16(t))")}, os.mk_zero_value(Word.not(16n, os.lo16(t)))) : {{Nat.add(_, {v("t")}) == d : Nat}}
  %Equal.sym(Nat, {v("t")}, {w16("os.lo16(t)")}, os.fit_lo(d, hD, t, h)) : {{Nat.add({w16("Word.not(16n, os.lo16(t))")}, _) == d : Nat}}
  os.succ_inj(Nat.add({w16("Word.not(16n, os.lo16(t))")}, {w16("os.lo16(t)")}), d, Equal.trans(Nat, 1n+Nat.add({w16("Word.not(16n, os.lo16(t))")}, {w16("os.lo16(t)")}), {DBL1}, 1n+d, UL.word_not_value(16n, os.lo16(t)), Equal.sym(Nat, 1n+d, {DBL1}, hD)))

# A 16-bit field: its two bytes are one word, the field's value

def os.be16_mask(c: U32) -> {{os.ws(B.mask(B.be16(c))) == Nat.add({v("os.mk(os.lo16(c), Word.zero(16n))")}, 0n) : Nat}}:
  match c:
    case {pat32("c")}:
      {{==}}

def os.be16_ws(+d: Nat, {HD}, +c: U32, +h: {fits("c")}) -> {{os.ws({tl(BE + "(c)")}) == {v("c")} : Nat}}:
  %Equal.sym({L}, {tl("B.Octets.of_list(B.be16(c))")}, B.mask(B.be16(c)), BL.octets_to_of(B.be16(c))) : {{os.ws(_) == {v("c")} : Nat}}
  %Equal.sym(Nat, os.ws(B.mask(B.be16(c))), Nat.add({v("os.mk(os.lo16(c), Word.zero(16n))")}, 0n), os.be16_mask(c)) : {{_ == {v("c")} : Nat}}
  %Equal.sym(Nat, Nat.add({v("os.mk(os.lo16(c), Word.zero(16n))")}, 0n), {v("os.mk(os.lo16(c), Word.zero(16n))")}, os.add_zero({v("os.mk(os.lo16(c), Word.zero(16n))")})) : {{_ == {v("c")} : Nat}}
  %Equal.sym(Nat, {v("os.mk(os.lo16(c), Word.zero(16n))")}, {w16("os.lo16(c)")}, os.mk_zero_value(os.lo16(c))) : {{_ == {v("c")} : Nat}}
  Equal.sym(Nat, {v("c")}, {w16("os.lo16(c)")}, os.fit_lo(d, hD, c, h))

def os.fit0(+d: Nat) -> {fits("0")}:
  os.le_zero(d)

def os.be16_ws0(+d: Nat, {HD}) -> {{os.ws({tl(BE + "(0)")}) == 0n : Nat}}:
  os.be16_ws(d, hD, 0, os.fit0(d))
""")


# ---- gen_part6.py
HD = "+hD: {1n+d == UN.U32Nat.dbl(16n, 1n) : Nat}"
HE = "+hE: {U32.to_nat(65535) == d : Nat}"
HDD = "+hd: {Nat.is_le(1n, d) == True{} : Bool}"
DPAR = f"+d: Nat, {HDD}, {HD}, {HE}"
L = "List<&2, U32>"
def tl(x): return f"B.Octets.to_list({x})"
def le(x, y): return "{Nat.is_le(%s, %s) == True{} : Bool}" % (x, y)
def u16(x): return "{U32.is_le(%s, 65535) == True{} : Bool}" % x

PL = tl("pseudo")
TT = "B.Octets.take(off, o)"
ZZ = "B.Octets.drop(Nat.add(off, 2n), o)"
TL_ = tl(TT)
ZL = tl(ZZ)
def BL_(c): return tl(f"B.Octets.be16({c})")
K3 = "os.K3(pseudo, o, off)"
def PUT(c): return f"K.inet_put16(o, off, {c})"
def S(c): return f"K.inet_sum(B.Octets.append(pseudo, {PUT(c)}))"
S0 = S("0")
CC = "K.inet_finish(%s)" % S0
EVP = "+eP: {K.inet_even(pseudo) == True{} : Bool}"
EVT = "+eT: {K.inet_even(B.Octets.take(off, o)) == True{} : Bool}"
ARGS = "+pseudo: B.Octets, +o: B.Octets, +off: Nat"

def XS(c): return f"B.append({PL}, B.append({TL_}, B.append({BL_(c)}, {ZL})))"

w(f"""
# The Internet checksum written into data: the data then sums to d

def os.K3({ARGS}) -> Nat:
  Nat.add(os.ws({PL}), Nat.add(os.ws({TL_}), os.ws({ZL})))

def os.rearr(+p: Nat, +t: Nat, +b: Nat, +z: Nat) -> {{Nat.add(p, Nat.add(t, Nat.add(b, z))) == Nat.add(Nat.add(p, Nat.add(t, z)), b) : Nat}}:
  %os.add_comm(z, b) : {{Nat.add(p, Nat.add(t, _)) == Nat.add(Nat.add(p, Nat.add(t, z)), b) : Nat}}
  %os.add_assoc(t, z, b) : {{Nat.add(p, _) == Nat.add(Nat.add(p, Nat.add(t, z)), b) : Nat}}
  Equal.sym(Nat, Nat.add(Nat.add(p, Nat.add(t, z)), b), Nat.add(p, Nat.add(Nat.add(t, z), b)), os.add_assoc(p, Nat.add(t, z), b))

# the sum of pseudo ++ o with the 16-bit field at off set to c, pseudo and
# the bytes before off of even length: rep of the words around the field
# plus c's
def os.sum_put({DPAR}, {ARGS}, +c: U32, {EVP}, {EVT}) -> {{{v(S("c"))} == os.rep(d, Nat.add({K3}, os.ws({BL_("c")}))) : Nat}}:
  %Equal.sym({L}, {tl("B.Octets.append(pseudo, " + PUT("c") + ")")}, B.append({PL}, {tl(PUT("c"))}), BL.octets_append_list(pseudo, {PUT("c")})) : {{U32.to_nat(K.inet_sum.list(_, 0)) == os.rep(d, Nat.add({K3}, os.ws({BL_("c")}))) : Nat}}
  %Equal.sym({L}, {tl("B.Octets.append(" + TT + ", B.Octets.append(B.Octets.be16(c), " + ZZ + "))")}, B.append({TL_}, {tl("B.Octets.append(B.Octets.be16(c), " + ZZ + ")")}), BL.octets_append_list({TT}, B.Octets.append(B.Octets.be16(c), {ZZ}))) : {{U32.to_nat(K.inet_sum.list(B.append({PL}, _), 0)) == os.rep(d, Nat.add({K3}, os.ws({BL_("c")}))) : Nat}}
  %Equal.sym({L}, {tl("B.Octets.append(B.Octets.be16(c), " + ZZ + ")")}, B.append({BL_("c")}, {ZL}), BL.octets_append_list(B.Octets.be16(c), {ZZ})) : {{U32.to_nat(K.inet_sum.list(B.append({PL}, B.append({TL_}, _)), 0)) == os.rep(d, Nat.add({K3}, os.ws({BL_("c")}))) : Nat}}
  %Equal.sym(Nat, U32.to_nat(K.inet_sum.list({XS("c")}, 0)), os.rep(d, Nat.add(U32.to_nat(0), os.ws({XS("c")}))), os.fold({XS("c")}, d, hd, hD, hE, 0, os.fit0(d))) : {{_ == os.rep(d, Nat.add({K3}, os.ws({BL_("c")}))) : Nat}}
  %Equal.sym(Nat, os.ws({XS("c")}), Nat.add(os.ws({PL}), os.ws(B.append({TL_}, B.append({BL_("c")}, {ZL})))), os.ws_append({PL}, B.append({TL_}, B.append({BL_("c")}, {ZL})), eP)) : {{os.rep(d, Nat.add(U32.to_nat(0), _)) == os.rep(d, Nat.add({K3}, os.ws({BL_("c")}))) : Nat}}
  %Equal.sym(Nat, os.ws(B.append({TL_}, B.append({BL_("c")}, {ZL}))), Nat.add(os.ws({TL_}), os.ws(B.append({BL_("c")}, {ZL}))), os.ws_append({TL_}, B.append({BL_("c")}, {ZL}), eT)) : {{os.rep(d, Nat.add(U32.to_nat(0), Nat.add(os.ws({PL}), _))) == os.rep(d, Nat.add({K3}, os.ws({BL_("c")}))) : Nat}}
  %Equal.sym(Nat, os.ws(B.append({BL_("c")}, {ZL})), Nat.add(os.ws({BL_("c")}), os.ws({ZL})), os.ws_append({BL_("c")}, {ZL}, os.be16_even(c))) : {{os.rep(d, Nat.add(U32.to_nat(0), Nat.add(os.ws({PL}), Nat.add(os.ws({TL_}), _)))) == os.rep(d, Nat.add({K3}, os.ws({BL_("c")}))) : Nat}}
  %Equal.sym(Nat, Nat.add(os.ws({PL}), Nat.add(os.ws({TL_}), Nat.add(os.ws({BL_("c")}), os.ws({ZL})))), Nat.add(Nat.add(os.ws({PL}), Nat.add(os.ws({TL_}), os.ws({ZL}))), os.ws({BL_("c")})), os.rearr(os.ws({PL}), os.ws({TL_}), os.ws({BL_("c")}), os.ws({ZL}))) : {{os.rep(d, Nat.add(U32.to_nat(0), _)) == os.rep(d, Nat.add({K3}, os.ws({BL_("c")}))) : Nat}}
  {{==}}

# the field set to 0: rep of the words around it
def os.sum0({DPAR}, {ARGS}, {EVP}, {EVT}) -> {{{v(S0)} == os.rep(d, {K3}) : Nat}}:
  %Equal.sym(Nat, {v(S0)}, os.rep(d, Nat.add({K3}, os.ws({BL_("0")}))), os.sum_put(d, hd, hD, hE, pseudo, o, off, 0, eP, eT)) : {{_ == os.rep(d, {K3}) : Nat}}
  %Equal.sym(Nat, os.ws({BL_("0")}), 0n, os.be16_ws0(d, hD)) : {{os.rep(d, Nat.add({K3}, _)) == os.rep(d, {K3}) : Nat}}
  %Equal.sym(Nat, Nat.add({K3}, 0n), {K3}, os.add_zero({K3})) : {{os.rep(d, _) == os.rep(d, {K3}) : Nat}}
  {{==}}

def os.sum0_fits({DPAR}, {ARGS}, {EVP}, {EVT}) -> {fits(S0)}:
  %Equal.sym(Nat, {v(S0)}, os.rep(d, {K3}), os.sum0(d, hd, hD, hE, pseudo, o, off, eP, eT)) : {{Nat.is_le(_, d) == True{{}} : Bool}}
  os.rep_le(d, {K3}, hd)

# x written into the field verifies when the sum with the field 0, plus x,
# is d
def os.verify_put({DPAR}, {ARGS}, {EVP}, {EVT}, +x: U32, +hx: {fits("x")}, +ex: {{os.rep(d, Nat.add({v(S0)}, {v("x")})) == d : Nat}}) -> {{K.inet_verify(B.Octets.append(pseudo, {PUT("x")})) == True{{}} : Bool}}:
  %Equal.sym(Bool, U32.is_eq({S("x")}, 65535), Nat.is_eq({v(S("x"))}, {v("65535")}), UL.u32_eq_value({S("x")}, 65535)) : {{_ == True{{}} : Bool}}
  %Equal.sym(Nat, {v("65535")}, d, hE) : {{Nat.is_eq({v(S("x"))}, _) == True{{}} : Bool}}
  %Equal.sym(Nat, {v(S("x"))}, os.rep(d, Nat.add({K3}, os.ws({BL_("x")}))), os.sum_put(d, hd, hD, hE, pseudo, o, off, x, eP, eT)) : {{Nat.is_eq(_, d) == True{{}} : Bool}}
  %Equal.sym(Nat, os.ws({BL_("x")}), {v("x")}, os.be16_ws(d, hD, x, hx)) : {{Nat.is_eq(os.rep(d, Nat.add({K3}, _)), d) == True{{}} : Bool}}
  %os.rep_fold(d, {K3}, {v("x")}, hd) : {{Nat.is_eq(_, d) == True{{}} : Bool}}
  %os.sum0(d, hd, hD, hE, pseudo, o, off, eP, eT) : {{Nat.is_eq(os.rep(d, Nat.add(_, {v("x")})), d) == True{{}} : Bool}}
  %Equal.sym(Nat, os.rep(d, Nat.add({v(S0)}, {v("x")})), d, ex) : {{Nat.is_eq(_, d) == True{{}} : Bool}}
  os.eq_refl(d)

def os.fill_sum({DPAR}, {ARGS}, {EVP}, {EVT}) -> {{os.rep(d, Nat.add({v(S0)}, {v(CC)})) == d : Nat}}:
  %os.add_comm({v(CC)}, {v(S0)}) : {{os.rep(d, _) == d : Nat}}
  %Equal.sym(Nat, Nat.add({v(CC)}, {v(S0)}), d, os.finish_value(d, hD, {S0}, os.sum0_fits(d, hd, hD, hE, pseudo, o, off, eP, eT))) : {{os.rep(d, _) == d : Nat}}
  os.rep_small(d, d, os.le_refl(d))

# inet_fill: the data with its checksum written in verifies
def os.fill_verifies({DPAR}, {ARGS}, {EVP}, {EVT}) -> {{K.inet_verify(B.Octets.append(pseudo, K.inet_fill(pseudo, o, off))) == True{{}} : Bool}}:
  os.verify_put(d, hd, hD, hE, pseudo, o, off, eP, eT, {CC}, os.finish_fits(d, hD, {S0}), os.fill_sum(d, hd, hD, hE, pseudo, o, off, eP, eT))

# the checksum 0 sent as 65535 (UDP): it verifies too, the sum being d
def os.v_eq_zero(x: Nat, +h: {{Nat.is_eq(x, 0n) == True{{}} : Bool}}) -> {{x == 0n : Nat}}:
  match x:
    case 0n:
      {{==}}
    case 1n+ +p:
      Empty.absurd({{1n+p == 0n : Nat}}, os.ft(h))

def os.allones_sum({DPAR}, {ARGS}, {EVP}, {EVT}, +hz: {{U32.is_eq({CC}, 0) == True{{}} : Bool}}) -> {{os.rep(d, Nat.add({v(S0)}, {v("65535")})) == d : Nat}}:
  +vc = os.v_eq_zero({v(CC)}, Equal.trans(Bool, Nat.is_eq({v(CC)}, 0n), U32.is_eq({CC}, 0), True{{}}, Equal.sym(Bool, U32.is_eq({CC}, 0), Nat.is_eq({v(CC)}, {v("0")}), UL.u32_eq_value({CC}, 0)), hz))
  +s0 = Equal.trans(Nat, {v(S0)}, Nat.add({v(CC)}, {v(S0)}), d, Equal.sym(Nat, Nat.add({v(CC)}, {v(S0)}), {v(S0)}, Equal.cong(Nat, Nat, z => Nat.add(z, {v(S0)}), {v(CC)}, 0n, vc)), os.finish_value(d, hD, {S0}, os.sum0_fits(d, hd, hD, hE, pseudo, o, off, eP, eT)))
  %Equal.sym(Nat, {v("65535")}, d, hE) : {{os.rep(d, Nat.add({v(S0)}, _)) == d : Nat}}
  %Equal.sym(Nat, {v(S0)}, d, s0) : {{os.rep(d, Nat.add(_, d)) == d : Nat}}
  %Equal.sym(Nat, os.rep(d, Nat.add(d, d)), os.rep(d, d), os.rep_period(d, d, hd, hd)) : {{_ == d : Nat}}
  os.rep_small(d, d, os.le_refl(d))

# The algebra, for the laws: every value at most d (written as U32.is_le(x,
# 65535) in the laws)

def os.g_add_bound({DPAR}, +a: U32, +b: U32, +ha: {u16("a")}, +hb: {u16("b")}) -> {u16("K.inet_add(a, b)")}:
  os.fit_to(d, hE, K.inet_add(a, b), os.add_fits(d, hd, hD, hE, a, b, os.fit_of(d, hE, a, ha), os.fit_of(d, hE, b, hb)))

def os.g_add_comm(+a: U32, +b: U32) -> {{K.inet_add(a, b) == K.inet_add(b, a) : U32}}:
  %U32.add_comm(b, a) : {{U32.add(U32.and(_, 65535), U32.shrn(_, 16n)) == K.inet_add(b, a) : U32}}
  {{==}}

def os.g_add_zero({DPAR}, +a: U32, +ha: {u16("a")}) -> {{K.inet_add(a, 0) == a : U32}}:
  UL.u32_value_eq(K.inet_add(a, 0), a, Equal.trans(Nat, {v("K.inet_add(a, 0)")}, os.rep(d, Nat.add({v("a")}, 0n)), {v("a")}, os.add_value(d, hd, hD, hE, a, 0, os.fit_of(d, hE, a, ha), os.fit0(d)), Equal.trans(Nat, os.rep(d, Nat.add({v("a")}, 0n)), os.rep(d, {v("a")}), {v("a")}, Equal.cong(Nat, Nat, z => os.rep(d, z), Nat.add({v("a")}, 0n), {v("a")}, os.add_zero({v("a")})), os.rep_small(d, {v("a")}, os.fit_of(d, hE, a, ha)))))

def os.g_add_assoc({DPAR}, +a: U32, +b: U32, +c: U32, +ha: {u16("a")}, +hb: {u16("b")}, +hc: {u16("c")}) -> {{K.inet_add(K.inet_add(a, b), c) == K.inet_add(a, K.inet_add(b, c)) : U32}}:
  UL.u32_value_eq(K.inet_add(K.inet_add(a, b), c), K.inet_add(a, K.inet_add(b, c)), os.g_add_assoc.v(d, hd, hD, hE, a, b, c, os.fit_of(d, hE, a, ha), os.fit_of(d, hE, b, hb), os.fit_of(d, hE, c, hc)))
""")
VA, VB, VC = v("a"), v("b"), v("c")
IAB = "K.inet_add(a, b)"
IBC = "K.inet_add(b, c)"
LHS = v(f"K.inet_add({IAB}, c)")
RHS = v(f"K.inet_add(a, {IBC})")
w(f"""
def os.g_add_assoc.v({DPAR}, +a: U32, +b: U32, +c: U32, +ha: {fits("a")}, +hb: {fits("b")}, +hc: {fits("c")}) -> {{{LHS} == {RHS} : Nat}}:
  %Equal.sym(Nat, {LHS}, os.rep(d, Nat.add({v(IAB)}, {VC})), os.add_value(d, hd, hD, hE, {IAB}, c, os.add_fits(d, hd, hD, hE, a, b, ha, hb), hc)) : {{_ == {RHS} : Nat}}
  %Equal.sym(Nat, {v(IAB)}, os.rep(d, Nat.add({VA}, {VB})), os.add_value(d, hd, hD, hE, a, b, ha, hb)) : {{os.rep(d, Nat.add(_, {VC})) == {RHS} : Nat}}
  %Equal.sym(Nat, os.rep(d, Nat.add(os.rep(d, Nat.add({VA}, {VB})), {VC})), os.rep(d, Nat.add(Nat.add({VA}, {VB}), {VC})), os.rep_fold(d, Nat.add({VA}, {VB}), {VC}, hd)) : {{_ == {RHS} : Nat}}
  %Equal.sym(Nat, Nat.add(Nat.add({VA}, {VB}), {VC}), Nat.add({VA}, Nat.add({VB}, {VC})), os.add_assoc({VA}, {VB}, {VC})) : {{os.rep(d, _) == {RHS} : Nat}}
  %Equal.sym(Nat, {RHS}, os.rep(d, Nat.add({VA}, {v(IBC)})), os.add_value(d, hd, hD, hE, a, {IBC}, ha, os.add_fits(d, hd, hD, hE, b, c, hb, hc))) : {{os.rep(d, Nat.add({VA}, Nat.add({VB}, {VC}))) == _ : Nat}}
  %Equal.sym(Nat, {v(IBC)}, os.rep(d, Nat.add({VB}, {VC})), os.add_value(d, hd, hD, hE, b, c, hb, hc)) : {{os.rep(d, Nat.add({VA}, Nat.add({VB}, {VC}))) == os.rep(d, Nat.add({VA}, _)) : Nat}}
  %os.add_comm(os.rep(d, Nat.add({VB}, {VC})), {VA}) : {{os.rep(d, Nat.add({VA}, Nat.add({VB}, {VC}))) == os.rep(d, _) : Nat}}
  %Equal.sym(Nat, os.rep(d, Nat.add(os.rep(d, Nat.add({VB}, {VC})), {VA})), os.rep(d, Nat.add(Nat.add({VB}, {VC}), {VA})), os.rep_fold(d, Nat.add({VB}, {VC}), {VA}, hd)) : {{os.rep(d, Nat.add({VA}, Nat.add({VB}, {VC}))) == _ : Nat}}
  %os.add_comm(Nat.add({VB}, {VC}), {VA}) : {{os.rep(d, _) == os.rep(d, Nat.add(Nat.add({VB}, {VC}), {VA})) : Nat}}
  {{==}}

def os.g_complement({DPAR}, +a: U32, +ha: {u16("a")}) -> {{K.inet_add(a, K.inet_finish(a)) == 65535 : U32}}:
  UL.u32_value_eq(K.inet_add(a, K.inet_finish(a)), 65535, os.g_complement.v(d, hd, hD, hE, a, os.fit_of(d, hE, a, ha)))

def os.g_complement.v({DPAR}, +a: U32, +ha: {fits("a")}) -> {{{v("K.inet_add(a, K.inet_finish(a))")} == {v("65535")} : Nat}}:
  %Equal.sym(Nat, {v("K.inet_add(a, K.inet_finish(a))")}, os.rep(d, Nat.add({VA}, {v("K.inet_finish(a)")})), os.add_value(d, hd, hD, hE, a, K.inet_finish(a), ha, os.finish_fits(d, hD, a))) : {{_ == {v("65535")} : Nat}}
  %os.add_comm({v("K.inet_finish(a)")}, {VA}) : {{os.rep(d, _) == {v("65535")} : Nat}}
  %Equal.sym(Nat, Nat.add({v("K.inet_finish(a)")}, {VA}), d, os.finish_value(d, hD, a, ha)) : {{os.rep(d, _) == {v("65535")} : Nat}}
  %Equal.sym(Nat, os.rep(d, d), d, os.rep_small(d, d, os.le_refl(d))) : {{_ == {v("65535")} : Nat}}
  Equal.sym(Nat, {v("65535")}, d, hE)

def os.g_finish_bound({DPAR}, +t: U32) -> {u16("K.inet_finish(t)")}:
  os.fit_to(d, hE, K.inet_finish(t), os.finish_fits(d, hD, t))

def os.g_update_bound({DPAR}, +acc: U32, +o: B.Octets, +h: {u16("acc")}) -> {u16("K.inet_update(acc, o)")}:
  os.fit_to(d, hE, K.inet_update(acc, o), os.fold_fits({tl("o")}, d, hd, hD, hE, acc, os.fit_of(d, hE, acc, h)))
""")
WO = f"os.ws({tl('o')})"
VAC, VW = v("acc"), v("w")
IAW = "K.inet_add(acc, w)"
UPD = "K.inet_update(acc, o)"
L2 = v(f"K.inet_update({IAW}, o)")
R2 = v(f"K.inet_add({UPD}, w)")
w(f"""
def os.g_update_add({DPAR}, +acc: U32, +w: U32, +o: B.Octets, +ha: {u16("acc")}, +hw: {u16("w")}) -> {{K.inet_update(K.inet_add(acc, w), o) == K.inet_add(K.inet_update(acc, o), w) : U32}}:
  UL.u32_value_eq(K.inet_update(K.inet_add(acc, w), o), K.inet_add(K.inet_update(acc, o), w), os.g_update_add.v(d, hd, hD, hE, acc, w, o, os.fit_of(d, hE, acc, ha), os.fit_of(d, hE, w, hw)))

def os.g_update_add.v({DPAR}, +acc: U32, +w: U32, +o: B.Octets, +ha: {fits("acc")}, +hw: {fits("w")}) -> {{{L2} == {R2} : Nat}}:
  %Equal.sym(Nat, {L2}, os.rep(d, Nat.add({v(IAW)}, {WO})), os.fold({tl("o")}, d, hd, hD, hE, {IAW}, os.add_fits(d, hd, hD, hE, acc, w, ha, hw))) : {{_ == {R2} : Nat}}
  %Equal.sym(Nat, {v(IAW)}, os.rep(d, Nat.add({VAC}, {VW})), os.add_value(d, hd, hD, hE, acc, w, ha, hw)) : {{os.rep(d, Nat.add(_, {WO})) == {R2} : Nat}}
  %Equal.sym(Nat, os.rep(d, Nat.add(os.rep(d, Nat.add({VAC}, {VW})), {WO})), os.rep(d, Nat.add(Nat.add({VAC}, {VW}), {WO})), os.rep_fold(d, Nat.add({VAC}, {VW}), {WO}, hd)) : {{_ == {R2} : Nat}}
  %Equal.sym(Nat, {R2}, os.rep(d, Nat.add({v(UPD)}, {VW})), os.add_value(d, hd, hD, hE, {UPD}, w, os.fold_fits({tl("o")}, d, hd, hD, hE, acc, ha), hw)) : {{os.rep(d, Nat.add(Nat.add({VAC}, {VW}), {WO})) == _ : Nat}}
  %Equal.sym(Nat, {v(UPD)}, os.rep(d, Nat.add({VAC}, {WO})), os.fold({tl("o")}, d, hd, hD, hE, acc, ha)) : {{os.rep(d, Nat.add(Nat.add({VAC}, {VW}), {WO})) == os.rep(d, Nat.add(_, {VW})) : Nat}}
  %Equal.sym(Nat, os.rep(d, Nat.add(os.rep(d, Nat.add({VAC}, {WO})), {VW})), os.rep(d, Nat.add(Nat.add({VAC}, {WO}), {VW})), os.rep_fold(d, Nat.add({VAC}, {WO}), {VW}, hd)) : {{os.rep(d, Nat.add(Nat.add({VAC}, {VW}), {WO})) == _ : Nat}}
  Equal.cong(Nat, Nat, z => os.rep(d, z), Nat.add(Nat.add({VAC}, {VW}), {WO}), Nat.add(Nat.add({VAC}, {WO}), {VW}), os.swap({VAC}, {VW}, {WO}))

def os.swap(+x: Nat, +y: Nat, +z: Nat) -> {{Nat.add(Nat.add(x, y), z) == Nat.add(Nat.add(x, z), y) : Nat}}:
  %Equal.sym(Nat, Nat.add(Nat.add(x, y), z), Nat.add(x, Nat.add(y, z)), os.add_assoc(x, y, z)) : {{_ == Nat.add(Nat.add(x, z), y) : Nat}}
  %os.add_comm(z, y) : {{Nat.add(x, _) == Nat.add(Nat.add(x, z), y) : Nat}}
  Equal.sym(Nat, Nat.add(Nat.add(x, z), y), Nat.add(x, Nat.add(z, y)), os.add_assoc(x, z, y))
""")
WX, WY = f"os.ws({tl('x')})", f"os.ws({tl('y')})"
UX, UY = "K.inet_update(acc, x)", "K.inet_update(acc, y)"
L3 = v(f"K.inet_update({UX}, y)")
R3 = v(f"K.inet_update({UY}, x)")
w(f"""
def os.g_update_comm({DPAR}, +acc: U32, +x: B.Octets, +y: B.Octets, +h: {u16("acc")}) -> {{K.inet_update(K.inet_update(acc, x), y) == K.inet_update(K.inet_update(acc, y), x) : U32}}:
  UL.u32_value_eq(K.inet_update(K.inet_update(acc, x), y), K.inet_update(K.inet_update(acc, y), x), os.g_update_comm.v(d, hd, hD, hE, acc, x, y, os.fit_of(d, hE, acc, h)))

def os.g_update_comm.v({DPAR}, +acc: U32, +x: B.Octets, +y: B.Octets, +h: {fits("acc")}) -> {{{L3} == {R3} : Nat}}:
  %Equal.sym(Nat, {L3}, os.rep(d, Nat.add({v(UX)}, {WY})), os.fold({tl("y")}, d, hd, hD, hE, {UX}, os.fold_fits({tl("x")}, d, hd, hD, hE, acc, h))) : {{_ == {R3} : Nat}}
  %Equal.sym(Nat, {v(UX)}, os.rep(d, Nat.add({VAC}, {WX})), os.fold({tl("x")}, d, hd, hD, hE, acc, h)) : {{os.rep(d, Nat.add(_, {WY})) == {R3} : Nat}}
  %Equal.sym(Nat, os.rep(d, Nat.add(os.rep(d, Nat.add({VAC}, {WX})), {WY})), os.rep(d, Nat.add(Nat.add({VAC}, {WX}), {WY})), os.rep_fold(d, Nat.add({VAC}, {WX}), {WY}, hd)) : {{_ == {R3} : Nat}}
  %Equal.sym(Nat, {R3}, os.rep(d, Nat.add({v(UY)}, {WX})), os.fold({tl("x")}, d, hd, hD, hE, {UY}, os.fold_fits({tl("y")}, d, hd, hD, hE, acc, h))) : {{os.rep(d, Nat.add(Nat.add({VAC}, {WX}), {WY})) == _ : Nat}}
  %Equal.sym(Nat, {v(UY)}, os.rep(d, Nat.add({VAC}, {WY})), os.fold({tl("y")}, d, hd, hD, hE, acc, h)) : {{os.rep(d, Nat.add(Nat.add({VAC}, {WX}), {WY})) == os.rep(d, Nat.add(_, {WX})) : Nat}}
  %Equal.sym(Nat, os.rep(d, Nat.add(os.rep(d, Nat.add({VAC}, {WY})), {WX})), os.rep(d, Nat.add(Nat.add({VAC}, {WY}), {WX})), os.rep_fold(d, Nat.add({VAC}, {WY}), {WX}, hd)) : {{os.rep(d, Nat.add(Nat.add({VAC}, {WX}), {WY})) == _ : Nat}}
  Equal.cong(Nat, Nat, z => os.rep(d, z), Nat.add(Nat.add({VAC}, {WX}), {WY}), Nat.add(Nat.add({VAC}, {WY}), {WX}), os.swap({VAC}, {WX}, {WY}))
""")
SXY = "K.inet_sum(B.Octets.append(x, y))"
SYX = "K.inet_sum(B.Octets.append(y, x))"
w(f"""
def os.g_sum_swap({DPAR}, +x: B.Octets, +y: B.Octets, +ex: {{K.inet_even(x) == True{{}} : Bool}}, +ey: {{K.inet_even(y) == True{{}} : Bool}}) -> {{{SXY} == {SYX} : U32}}:
  UL.u32_value_eq({SXY}, {SYX}, os.g_sum_swap.v(d, hd, hD, hE, x, y, ex, ey))

def os.g_sum_swap.v({DPAR}, +x: B.Octets, +y: B.Octets, +ex: {{K.inet_even(x) == True{{}} : Bool}}, +ey: {{K.inet_even(y) == True{{}} : Bool}}) -> {{{v(SXY)} == {v(SYX)} : Nat}}:
  %Equal.sym({L}, {tl("B.Octets.append(x, y)")}, B.append({tl("x")}, {tl("y")}), BL.octets_append_list(x, y)) : {{U32.to_nat(K.inet_sum.list(_, 0)) == {v(SYX)} : Nat}}
  %Equal.sym({L}, {tl("B.Octets.append(y, x)")}, B.append({tl("y")}, {tl("x")}), BL.octets_append_list(y, x)) : {{U32.to_nat(K.inet_sum.list(B.append({tl("x")}, {tl("y")}), 0)) == U32.to_nat(K.inet_sum.list(_, 0)) : Nat}}
  %Equal.sym(Nat, U32.to_nat(K.inet_sum.list(B.append({tl("x")}, {tl("y")}), 0)), os.rep(d, Nat.add(U32.to_nat(0), os.ws(B.append({tl("x")}, {tl("y")})))), os.fold(B.append({tl("x")}, {tl("y")}), d, hd, hD, hE, 0, os.fit0(d))) : {{_ == U32.to_nat(K.inet_sum.list(B.append({tl("y")}, {tl("x")}), 0)) : Nat}}
  %Equal.sym(Nat, U32.to_nat(K.inet_sum.list(B.append({tl("y")}, {tl("x")}), 0)), os.rep(d, Nat.add(U32.to_nat(0), os.ws(B.append({tl("y")}, {tl("x")})))), os.fold(B.append({tl("y")}, {tl("x")}), d, hd, hD, hE, 0, os.fit0(d))) : {{os.rep(d, Nat.add(U32.to_nat(0), os.ws(B.append({tl("x")}, {tl("y")})))) == _ : Nat}}
  %Equal.sym(Nat, os.ws(B.append({tl("x")}, {tl("y")})), Nat.add({WX}, {WY}), os.ws_append({tl("x")}, {tl("y")}, ex)) : {{os.rep(d, Nat.add(U32.to_nat(0), _)) == os.rep(d, Nat.add(U32.to_nat(0), os.ws(B.append({tl("y")}, {tl("x")})))) : Nat}}
  %Equal.sym(Nat, os.ws(B.append({tl("y")}, {tl("x")})), Nat.add({WY}, {WX}), os.ws_append({tl("y")}, {tl("x")}, ey)) : {{os.rep(d, Nat.add(U32.to_nat(0), Nat.add({WX}, {WY}))) == os.rep(d, Nat.add(U32.to_nat(0), _)) : Nat}}
  %os.add_comm({WX}, {WY}) : {{os.rep(d, Nat.add(U32.to_nat(0), Nat.add({WX}, {WY}))) == os.rep(d, Nat.add(U32.to_nat(0), _)) : Nat}}
  {{==}}
""")


# ---- the end-around carry, lengths
VAB = v("U32.add(a, b)")
XAB = "Nat.add(%s, %s)" % (v("a"), v("b"))
FA = "+ha: {Nat.is_le(U32.to_nat(a), d) == True{} : Bool}"
FB = "+hb: {Nat.is_le(U32.to_nat(b), d) == True{} : Bool}"
w(f"""
# The end-around carry: a sum past d comes back round as the sum less d

def os.sum_fits({DPAR}, +a: U32, +b: U32, {FA}, {FB}, +h: {{U32.is_le(U32.add(a, b), 65535) == True{{}} : Bool}}) -> {{Nat.is_le({XAB}, d) == True{{}} : Bool}}:
  %os.nowrap(d, hD, hE, a, b, ha, hb) : {{Nat.is_le(_, d) == True{{}} : Bool}}
  os.fit_of(d, hE, U32.add(a, b), h)

def os.sum_not_fits({DPAR}, +a: U32, +b: U32, {FA}, {FB}, +h: {{U32.is_le(U32.add(a, b), 65535) == False{{}} : Bool}}) -> {{Nat.is_le({XAB}, d) == False{{}} : Bool}}:
  %os.nowrap(d, hD, hE, a, b, ha, hb) : {{Nat.is_le(_, d) == False{{}} : Bool}}
  %hE : {{Nat.is_le({VAB}, _) == False{{}} : Bool}}
  %UL.u32_le_value(U32.add(a, b), 65535) : {{_ == False{{}} : Bool}}
  h

def os.g_no_carry.v({DPAR}, +a: U32, +b: U32, {FA}, {FB}, +h: {{U32.is_le(U32.add(a, b), 65535) == True{{}} : Bool}}) -> {{{v("K.inet_add(a, b)")} == {VAB} : Nat}}:
  %Equal.sym(Nat, {v("K.inet_add(a, b)")}, os.rep(d, {XAB}), os.add_value(d, hd, hD, hE, a, b, ha, hb)) : {{_ == {VAB} : Nat}}
  %Equal.sym(Nat, {VAB}, {XAB}, os.nowrap(d, hD, hE, a, b, ha, hb)) : {{os.rep(d, {XAB}) == _ : Nat}}
  os.rep_small(d, {XAB}, os.sum_fits(d, hd, hD, hE, a, b, ha, hb, h))

def os.g_no_carry({DPAR}, +a: U32, +b: U32, +ha: {u16("a")}, +hb: {u16("b")}, +h: {{U32.is_le(U32.add(a, b), 65535) == True{{}} : Bool}}) -> {{K.inet_add(a, b) == U32.add(a, b) : U32}}:
  UL.u32_value_eq(K.inet_add(a, b), U32.add(a, b), os.g_no_carry.v(d, hd, hD, hE, a, b, os.fit_of(d, hE, a, ha), os.fit_of(d, hE, b, hb), h))

def os.end_le(+d: Nat, +j: Nat, +X: Nat, +eX: {{X == Nat.add(1n+j, d) : Nat}}, +hab: {{Nat.is_le(X, Nat.add(d, d)) == True{{}} : Bool}}) -> {{Nat.is_le(1n+j, d) == True{{}} : Bool}}:
  %os.le_cancel_l(d, 1n+j, d) : {{_ == True{{}} : Bool}}
  %os.add_comm(1n+j, d) : {{Nat.is_le(_, Nat.add(d, d)) == True{{}} : Bool}}
  %eX : {{Nat.is_le(_, Nat.add(d, d)) == True{{}} : Bool}}
  hab

def os.end_rep(+d: Nat, {HDD}, +X: Nat, +j: Nat, +eX: {{X == Nat.add(1n+j, d) : Nat}}, +hab: {{Nat.is_le(X, Nat.add(d, d)) == True{{}} : Bool}}) -> {{os.rep(d, X) == Nat.sub(X, d) : Nat}}:
  %Equal.sym(Nat, X, Nat.add(1n+j, d), eX) : {{os.rep(d, _) == Nat.sub(_, d) : Nat}}
  %Equal.sym(Nat, Nat.sub(Nat.add(1n+j, d), d), 1n+j, os.sub_add(1n+j, d)) : {{os.rep(d, Nat.add(1n+j, d)) == _ : Nat}}
  %Equal.sym(Nat, os.rep(d, Nat.add(1n+j, d)), os.rep(d, 1n+j), os.rep_period1(d, j, hd)) : {{_ == 1n+j : Nat}}
  os.rep_small(d, 1n+j, os.end_le(d, j, X, eX, hab))

def os.end_hle({DPAR}, +a: U32, +b: U32, {FA}, {FB}, +hX: {{Nat.is_le({XAB}, d) == False{{}} : Bool}}) -> {{Nat.is_le({v("65535")}, {VAB}) == True{{}} : Bool}}:
  %Equal.sym(Nat, {v("65535")}, d, hE) : {{Nat.is_le(_, {VAB}) == True{{}} : Bool}}
  %Equal.sym(Nat, {VAB}, {XAB}, os.nowrap(d, hD, hE, a, b, ha, hb)) : {{Nat.is_le(d, _) == True{{}} : Bool}}
  os.le_pred(d, {XAB}, os.not_le({XAB}, d, hX))

def os.g_end_around.v({DPAR}, +a: U32, +b: U32, {FA}, {FB}, +h: {{U32.is_le(U32.add(a, b), 65535) == False{{}} : Bool}}) -> {{{v("K.inet_add(a, b)")} == {v("U32.sub(U32.add(a, b), 65535)")} : Nat}}:
  +hX = os.sum_not_fits(d, hd, hD, hE, a, b, ha, hb, h)
  %Equal.sym(Nat, {v("K.inet_add(a, b)")}, os.rep(d, {XAB}), os.add_value(d, hd, hD, hE, a, b, ha, hb)) : {{_ == {v("U32.sub(U32.add(a, b), 65535)")} : Nat}}
  %Equal.sym(Nat, {v("U32.sub(U32.add(a, b), 65535)")}, Nat.sub({VAB}, {v("65535")}), UL.u32_sub_value(U32.add(a, b), 65535, os.end_hle(d, hd, hD, hE, a, b, ha, hb, hX))) : {{os.rep(d, {XAB}) == _ : Nat}}
  %Equal.sym(Nat, {VAB}, {XAB}, os.nowrap(d, hD, hE, a, b, ha, hb)) : {{os.rep(d, {XAB}) == Nat.sub(_, {v("65535")}) : Nat}}
  %Equal.sym(Nat, {v("65535")}, d, hE) : {{os.rep(d, {XAB}) == Nat.sub({XAB}, _) : Nat}}
  os.end_rep(d, hd, {XAB}, Nat.sub({XAB}, 1n+d), os.sub_split({XAB}, d, hX), os.le_add_mono({v("a")}, {v("b")}, d, d, ha, hb))

def os.g_end_around({DPAR}, +a: U32, +b: U32, +ha: {u16("a")}, +hb: {u16("b")}, +h: {{U32.is_le(U32.add(a, b), 65535) == False{{}} : Bool}}) -> {{K.inet_add(a, b) == U32.sub(U32.add(a, b), 65535) : U32}}:
  UL.u32_value_eq(K.inet_add(a, b), U32.sub(U32.add(a, b), 65535), os.g_end_around.v(d, hd, hD, hE, a, b, os.fit_of(d, hE, a, ha), os.fit_of(d, hE, b, hb), h))

# Lengths: writing a 16-bit field inside the data keeps its length

# x + (y - x) = y, for x <= y
def os.add_sub(x: Nat, y: Nat, +h: {{Nat.is_le(x, y) == True{{}} : Bool}}) -> {{Nat.add(x, Nat.sub(y, x)) == y : Nat}}:
  match x y:
    case 0n _:
      os.sub_zero(y)
    case 1n+ +xp 0n:
      Empty.absurd({{Nat.add(1n+xp, Nat.sub(0n, 1n+xp)) == 0n : Nat}}, os.ft(h))
    case 1n+ +xp 1n+ +yp:
      os.succ_cong(Nat.add(xp, Nat.sub(yp, xp)), yp, os.add_sub(xp, yp, h))
""")
TK = "B.Octets.take(off, o)"
DR = "B.Octets.drop(Nat.add(off, 2n), o)"
BX = "B.Octets.be16(x)"
LO = "B.Octets.len(o)"
def ln(x): return "B.Octets.len(%s)" % x
REST = "B.Octets.append(%s, %s)" % (BX, DR)
SUBL = "Nat.sub(%s, Nat.add(off, 2n))" % LO
w(f"""
def os.len_put16(+o: B.Octets, +off: Nat, +x: U32, +h: {{Nat.is_le(Nat.add(off, 2n), {LO}) == True{{}} : Bool}}) -> {{{ln("K.inet_put16(o, off, x)")} == {LO} : Nat}}:
  %Equal.sym(Nat, {ln("B.Octets.append(" + TK + ", " + REST + ")")}, Nat.add({ln(TK)}, {ln(REST)}), BL.octets_len_append({TK}, {REST})) : {{_ == {LO} : Nat}}
  %Equal.sym(Nat, {ln(REST)}, Nat.add({ln(BX)}, {ln(DR)}), BL.octets_len_append({BX}, {DR})) : {{Nat.add({ln(TK)}, _) == {LO} : Nat}}
  %Equal.sym(Nat, {ln(TK)}, off, BL.octets_len_take_le(off, o, os.le_trans(off, Nat.add(off, 2n), {LO}, os.le_add_r(off, 2n), h))) : {{Nat.add(_, Nat.add({ln(BX)}, {ln(DR)})) == {LO} : Nat}}
  %Equal.sym(Nat, {ln(BX)}, 2n, BL.octets_len_be16(x)) : {{Nat.add(off, Nat.add(_, {ln(DR)})) == {LO} : Nat}}
  %Equal.sym(Nat, {ln(DR)}, {SUBL}, BL.octets_len_drop(Nat.add(off, 2n), o)) : {{Nat.add(off, Nat.add(2n, _)) == {LO} : Nat}}
  %os.add_assoc(off, 2n, {SUBL}) : {{_ == {LO} : Nat}}
  os.add_sub(Nat.add(off, 2n), {LO}, h)

# a value of at most d is its own low 16 bits
def os.low16_mk(c: U32) -> {{B.low16(c) == os.mk(os.lo16(c), Word.zero(16n)) : U32}}:
  match c:
    case U32{{x}}:
      {{==}}

def os.low16_fit(+d: Nat, {HD}, +c: U32, +h: {fits("c")}) -> {{B.low16(c) == c : U32}}:
  UL.u32_value_eq(B.low16(c), c, Equal.trans(Nat, {v("B.low16(c)")}, {v("os.mk(os.lo16(c), Word.zero(16n))")}, {v("c")}, Equal.cong(U32, Nat, z => U32.to_nat(z), B.low16(c), os.mk(os.lo16(c), Word.zero(16n)), os.low16_mk(c)), Equal.trans(Nat, {v("os.mk(os.lo16(c), Word.zero(16n))")}, {w16("os.lo16(c)")}, {v("c")}, os.mk_zero_value(os.lo16(c)), Equal.sym(Nat, {v("c")}, {w16("os.lo16(c)")}, os.fit_lo(d, hD, c, h)))))
""")

# ---- writing a 16-bit field into bytes given as a list
LL = "List<&2, U32>"
def OL(x): return "B.Octets.of_list(%s)" % x
def TLs(x): return "B.Octets.to_list(%s)" % x
T_ = "B.take(off, L)"
D_ = "B.drop(off, L)"
T2 = "B.take(2n, B.drop(off, L))"
D2 = "B.drop(2n, B.drop(off, L))"
A_ = OL(T_)
BM = OL(T2)
C_ = OL(D2)
XP = f"B.Octets.append({A_}, B.Octets.append({BM}, {C_}))"
RHS = f"B.append(B.mask({T_}), B.append(B.mask(B.be16(v)), B.mask(B.drop(Nat.add(off, 2n), L))))"
w(f"""
# Lists and Octets: the bytes of data with a 16-bit field written in

def os.mask_append(xs: {LL}, +ys: {LL}) -> {{B.mask(B.append(xs, ys)) == B.append(B.mask(xs), B.mask(ys)) : {LL}}}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{+x, +t}}:
      %Equal.sym({LL}, B.mask(B.append(t, ys)), B.append(B.mask(t), B.mask(ys)), os.mask_append(t, ys)) : {{Con{{B.byte(x), _}} == Con{{B.byte(x), B.append(B.mask(t), B.mask(ys))}} : {LL}}}
      {{==}}

def os.len_mask(xs: {LL}) -> {{B.len(B.mask(xs)) == B.len(xs) : Nat}}:
  match xs:
    case Nil{{}}:
      {{==}}
    case Con{{x, +t}}:
      os.succ_cong(B.len(B.mask(t)), B.len(t), os.len_mask(t))

def os.len_take(n: Nat, xs: {LL}, +h: {{Nat.is_le(n, B.len(xs)) == True{{}} : Bool}}) -> {{B.len(B.take(n, xs)) == n : Nat}}:
  match n:
    case 0n:
      {{==}}
    case 1n+ +p:
      match xs:
        case Nil{{}}:
          Empty.absurd({{B.len(B.take(1n+p, Nil{{}})) == 1n+p : Nat}}, os.ft(h))
        case Con{{x, +t}}:
          os.succ_cong(B.len(B.take(p, t)), p, os.len_take(p, t, h))

def os.le_drop(n: Nat, +k: Nat, xs: {LL}, +h: {{Nat.is_le(Nat.add(n, k), B.len(xs)) == True{{}} : Bool}}) -> {{Nat.is_le(k, B.len(B.drop(n, xs))) == True{{}} : Bool}}:
  match n:
    case 0n:
      h
    case 1n+ +p:
      match xs:
        case Nil{{}}:
          Empty.absurd({{Nat.is_le(k, B.len(B.drop(1n+p, Nil{{}}))) == True{{}} : Bool}}, os.ft(h))
        case Con{{x, +t}}:
          os.le_drop(p, k, t, h)

def os.drop_nil(n: Nat) -> {{B.drop(n, Nil{{}}) == Nil{{}} : {LL}}}:
  match n:
    case 0n:
      {{==}}
    case 1n+p:
      {{==}}

def os.drop_drop(i: Nat, +j: Nat, xs: {LL}) -> {{B.drop(j, B.drop(i, xs)) == B.drop(Nat.add(i, j), xs) : {LL}}}:
  match i:
    case 0n:
      {{==}}
    case 1n+ +p:
      match xs:
        case Nil{{}}:
          os.drop_nil(j)
        case Con{{x, +t}}:
          os.drop_drop(p, j, t)

def os.of_list_append(+xs: {LL}, +ys: {LL}) -> {{{OL("B.append(xs, ys)")} == B.Octets.append({OL("xs")}, {OL("ys")}) : B.Octets}}:
  %BL.octets_of_to(B.Octets.append({OL("xs")}, {OL("ys")})) : {{{OL("B.append(xs, ys)")} == _ : B.Octets}}
  %Equal.sym({LL}, {TLs("B.Octets.append(" + OL("xs") + ", " + OL("ys") + ")")}, B.append({TLs(OL("xs"))}, {TLs(OL("ys"))}), BL.octets_append_list({OL("xs")}, {OL("ys")})) : {{{OL("B.append(xs, ys)")} == B.Octets.of_list(_) : B.Octets}}
  %Equal.sym({LL}, {TLs(OL("xs"))}, B.mask(xs), BL.octets_to_of(xs)) : {{{OL("B.append(xs, ys)")} == B.Octets.of_list(B.append(_, {TLs(OL("ys"))})) : B.Octets}}
  %Equal.sym({LL}, {TLs(OL("ys"))}, B.mask(ys), BL.octets_to_of(ys)) : {{{OL("B.append(xs, ys)")} == B.Octets.of_list(B.append(B.mask(xs), _)) : B.Octets}}
  %os.mask_append(xs, ys) : {{{OL("B.append(xs, ys)")} == B.Octets.of_list(_) : B.Octets}}
  %BL.octets_to_of(B.append(xs, ys)) : {{{OL("B.append(xs, ys)")} == B.Octets.of_list(_) : B.Octets}}
  Equal.sym(B.Octets, {OL(TLs(OL("B.append(xs, ys)")))}, {OL("B.append(xs, ys)")}, BL.octets_of_list_idempotent(B.append(xs, ys)))

# of_list(L) cut at off and off + 2
def os.cut3(+L: {LL}, +off: Nat) -> {{{OL("L")} == {XP} : B.Octets}}:
  %BL.take_drop(off, L) : {{B.Octets.of_list(_) == {XP} : B.Octets}}
  %BL.take_drop(2n, {D_}) : {{B.Octets.of_list(B.append({T_}, _)) == {XP} : B.Octets}}
  %Equal.sym(B.Octets, {OL("B.append(" + T_ + ", B.append(" + T2 + ", " + D2 + "))")}, B.Octets.append({A_}, {OL("B.append(" + T2 + ", " + D2 + ")")}), os.of_list_append({T_}, B.append({T2}, {D2}))) : {{_ == {XP} : B.Octets}}
  %Equal.sym(B.Octets, {OL("B.append(" + T2 + ", " + D2 + ")")}, B.Octets.append({BM}, {C_}), os.of_list_append({T2}, {D2})) : {{B.Octets.append({A_}, _) == {XP} : B.Octets}}
  {{==}}

def os.lenA(+L: {LL}, +off: Nat, +h: {{Nat.is_le(Nat.add(off, 2n), B.len(L)) == True{{}} : Bool}}) -> {{B.Octets.len({A_}) == off : Nat}}:
  %Equal.sym(Nat, B.Octets.len({A_}), B.len({T_}), BL.octets_len_of_list({T_})) : {{_ == off : Nat}}
  os.len_take(off, L, os.le_trans(off, Nat.add(off, 2n), B.len(L), os.le_add_r(off, 2n), h))

def os.lenB(+L: {LL}, +off: Nat, +h: {{Nat.is_le(Nat.add(off, 2n), B.len(L)) == True{{}} : Bool}}) -> {{B.Octets.len({BM}) == 2n : Nat}}:
  %Equal.sym(Nat, B.Octets.len({BM}), B.len({T2}), BL.octets_len_of_list({T2})) : {{_ == 2n : Nat}}
  os.len_take(2n, {D_}, os.le_drop(off, 2n, L, h))

# the bytes of of_list(L) with v written at off (off + 2 bytes present)
def os.put16_list(+L: {LL}, +off: Nat, +v: U32, +h: {{Nat.is_le(Nat.add(off, 2n), B.len(L)) == True{{}} : Bool}}) -> {{{TLs("K.inet_put16(" + OL("L") + ", off, v)")} == {RHS} : {LL}}}:
  %Equal.sym(B.Octets, {OL("L")}, {XP}, os.cut3(L, off)) : {{B.Octets.to_list(K.inet_put16(_, off, v)) == {RHS} : {LL}}}
  %os.lenA(L, off, h) : {{B.Octets.to_list(B.Octets.append(B.Octets.take(_, {XP}), B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(off, 2n), {XP})))) == {RHS} : {LL}}}
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len({A_}), {XP}), {A_}, BL.octets_take_append({A_}, B.Octets.append({BM}, {C_}))) : {{B.Octets.to_list(B.Octets.append(_, B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(off, 2n), {XP})))) == {RHS} : {LL}}}
  %os.lenA(L, off, h) : {{B.Octets.to_list(B.Octets.append({A_}, B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(_, 2n), {XP})))) == {RHS} : {LL}}}
  %Equal.sym(B.Octets, B.Octets.drop(Nat.add(B.Octets.len({A_}), 2n), {XP}), B.Octets.drop(2n, B.Octets.append({BM}, {C_})), BL.octets_drop_append_add({A_}, 2n, B.Octets.append({BM}, {C_}))) : {{B.Octets.to_list(B.Octets.append({A_}, B.Octets.append(B.Octets.be16(v), _))) == {RHS} : {LL}}}
  %os.lenB(L, off, h) : {{B.Octets.to_list(B.Octets.append({A_}, B.Octets.append(B.Octets.be16(v), B.Octets.drop(_, B.Octets.append({BM}, {C_}))))) == {RHS} : {LL}}}
  %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len({BM}), B.Octets.append({BM}, {C_})), {C_}, BL.octets_drop_append({BM}, {C_})) : {{B.Octets.to_list(B.Octets.append({A_}, B.Octets.append(B.Octets.be16(v), _))) == {RHS} : {LL}}}
  %Equal.sym({LL}, {TLs("B.Octets.append(" + A_ + ", B.Octets.append(B.Octets.be16(v), " + C_ + "))")}, B.append({TLs(A_)}, {TLs("B.Octets.append(B.Octets.be16(v), " + C_ + ")")}), BL.octets_append_list({A_}, B.Octets.append(B.Octets.be16(v), {C_}))) : {{_ == {RHS} : {LL}}}
  %Equal.sym({LL}, {TLs("B.Octets.append(B.Octets.be16(v), " + C_ + ")")}, B.append({TLs("B.Octets.be16(v)")}, {TLs(C_)}), BL.octets_append_list(B.Octets.be16(v), {C_})) : {{B.append({TLs(A_)}, _) == {RHS} : {LL}}}
  %Equal.sym({LL}, {TLs(A_)}, B.mask({T_}), BL.octets_to_of({T_})) : {{B.append(_, B.append({TLs("B.Octets.be16(v)")}, {TLs(C_)})) == {RHS} : {LL}}}
  %Equal.sym({LL}, {TLs(OL("B.be16(v)"))}, B.mask(B.be16(v)), BL.octets_to_of(B.be16(v))) : {{B.append(B.mask({T_}), B.append(_, {TLs(C_)})) == {RHS} : {LL}}}
  %Equal.sym({LL}, {TLs(C_)}, B.mask({D2}), BL.octets_to_of({D2})) : {{B.append(B.mask({T_}), B.append(B.mask(B.be16(v)), _)) == {RHS} : {LL}}}
  %Equal.sym({LL}, {D2}, B.drop(Nat.add(off, 2n), L), os.drop_drop(off, 2n, L)) : {{B.append(B.mask({T_}), B.append(B.mask(B.be16(v)), B.mask(_))) == {RHS} : {LL}}}
  {{==}}
""")

# ---- appending bytes to a list's bytes
w(f"""
# of_list(X) ++ y is the bytes of the list X ++ to_list(y)
def os.app_of(+X: List<&2, U32>, +y: B.Octets) -> {{B.Octets.append(B.Octets.of_list(X), y) == B.Octets.of_list(B.append(X, B.Octets.to_list(y))) : B.Octets}}:
  %BL.octets_of_to(y) : {{B.Octets.append(B.Octets.of_list(X), _) == B.Octets.of_list(B.append(X, B.Octets.to_list(y))) : B.Octets}}
  Equal.sym(B.Octets, B.Octets.of_list(B.append(X, B.Octets.to_list(y))), B.Octets.append(B.Octets.of_list(X), B.Octets.of_list(B.Octets.to_list(y))), os.of_list_append(X, B.Octets.to_list(y)))

def os.ge_zero(x: Nat) -> {{Cmp.is_ge(Nat.cmp(x, 0n)) == True{{}} : Bool}}:
  match x:
    case 0n:
      {{==}}
    case 1n+p:
      {{==}}
""")

# ---- a field written with its own value; a verified checksum is the computed one
LL = "List<&2, U32>"
w(f"""
# Writing a field's own value back changes nothing

def os.of_mask(+a: {LL}, +b: {LL}, +e: {{B.mask(a) == B.mask(b) : {LL}}}) -> {{B.Octets.of_list(a) == B.Octets.of_list(b) : B.Octets}}:
  %BL.octets_of_list_idempotent(a) : {{_ == B.Octets.of_list(b) : B.Octets}}
  %Equal.sym({LL}, B.Octets.to_list(B.Octets.of_list(a)), B.mask(a), BL.octets_to_of(a)) : {{B.Octets.of_list(_) == B.Octets.of_list(b) : B.Octets}}
  %Equal.sym({LL}, B.mask(a), B.mask(b), e) : {{B.Octets.of_list(_) == B.Octets.of_list(b) : B.Octets}}
  %BL.octets_to_of(b) : {{B.Octets.of_list(_) == B.Octets.of_list(b) : B.Octets}}
  BL.octets_of_list_idempotent(b)

def os.some_get(m: Maybe<&2, U32>, +d: U32) -> U32:
  match m:
    case Some{{x}}:
      x
    case None{{}}:
      d

def os.be16_word(a: U32, b: U32) -> U32:
  U32{{W.W64.bits.cat(16n, 16n, W.W64.bits.cat(8n, 8n, B.bits8(b), B.bits8(a)), Word.zero(16n))}}

def os.be16_ab(a: U32, b: U32) -> {{B.mask(B.be16(os.be16_word(a, b))) == B.mask([a, b]) : {LL}}}:
  match a b:
    case {pat("a", 8)} {pat("b", 8)}:
      {{==}}

# a two-byte list read as a 16-bit field c: its bytes are c's
def os.be16_self.l(ys: {LL}, +c: U32, +eY: {{B.be16.head(ys) == Some{{c}} : Maybe<&2, U32>}}, +eL: {{B.len(ys) == 2n : Nat}}) -> {{B.Octets.of_list(B.be16(c)) == B.Octets.of_list(ys) : B.Octets}}:
  match ys:
    case Nil{{}}:
      Empty.absurd({{B.Octets.of_list(B.be16(c)) == B.Octets.of_list(Nil{{}}) : B.Octets}}, os.ft(Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 2n, 0n, Equal.sym(Nat, 0n, 2n, eL))))
    case Con{{+a, t}}:
      match t:
        case Nil{{}}:
          Empty.absurd({{B.Octets.of_list(B.be16(c)) == B.Octets.of_list([a]) : B.Octets}}, os.ft(Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n), 2n, 1n, Equal.sym(Nat, 1n, 2n, eL))))
        case Con{{+b, t2}}:
          match t2:
            case Nil{{}}:
              %Equal.cong(Maybe<&2, U32>, U32, z => os.some_get(z, c), Some{{os.be16_word(a, b)}}, Some{{c}}, eY) : {{B.Octets.of_list(B.be16(_)) == B.Octets.of_list([a, b]) : B.Octets}}
              os.of_mask(B.be16(os.be16_word(a, b)), [a, b], os.be16_ab(a, b))
            case Con{{+d, +t3}}:
              Empty.absurd({{B.Octets.of_list(B.be16(c)) == B.Octets.of_list(Con{{a, Con{{b, Con{{d, t3}}}}}}) : B.Octets}}, os.ft(Equal.cong(Nat, Bool, z => Nat.is_eq(z, 2n), 3n+B.len(t3), 2n, eL)))

def os.le_sub(off: Nat, +k: Nat, +n: Nat, +h: {{Nat.is_le(Nat.add(off, k), n) == True{{}} : Bool}}) -> {{Nat.is_le(k, Nat.sub(n, off)) == True{{}} : Bool}}:
  match off:
    case 0n:
      Equal.trans(Bool, Nat.is_le(k, Nat.sub(n, 0n)), Nat.is_le(k, n), True{{}}, Equal.cong(Nat, Bool, z => Nat.is_le(k, z), Nat.sub(n, 0n), n, os.sub_zero(n)), h)
    case 1n+ +p:
      match n:
        case 0n:
          Empty.absurd({{Nat.is_le(k, Nat.sub(0n, 1n+p)) == True{{}} : Bool}}, os.ft(h))
        case 1n+ +q:
          os.le_sub(p, k, q, h)

# the 2 bytes at the start of D read as c are c's bytes
def os.be16_self(+D: B.Octets, +c: U32, +hc: {{B.Octets.be16_at(D, 0n) == Some{{c}} : Maybe<&2, U32>}}, +hl: {{Nat.is_le(2n, B.Octets.len(D)) == True{{}} : Bool}}) -> {{B.Octets.be16(c) == B.Octets.take(2n, D) : B.Octets}}:
  %BL.octets_of_to(B.Octets.take(2n, D)) : {{B.Octets.be16(c) == _ : B.Octets}}
  os.be16_self.l(B.Octets.to_list(B.Octets.take(2n, D)), c, Equal.trans(Maybe<&2, U32>, B.be16.head(B.Octets.to_list(B.Octets.take(2n, D))), B.Octets.be16_at(D, 0n), Some{{c}}, Equal.cong(B.Octets, Maybe<&2, U32>, z => B.be16.head(B.Octets.to_list(B.Octets.take(2n, z))), D, B.Octets.drop(0n, D), Equal.sym(B.Octets, B.Octets.drop(0n, D), D, BL.octets_drop_zero(D))), hc), Equal.trans(Nat, B.len(B.Octets.to_list(B.Octets.take(2n, D))), B.Octets.len(B.Octets.take(2n, D)), 2n, Equal.sym(Nat, B.Octets.len(B.Octets.take(2n, D)), B.len(B.Octets.to_list(B.Octets.take(2n, D))), BL.octets_len_list(B.Octets.take(2n, D))), BL.octets_len_take_le(2n, D, hl)))

# writing a field's own value back gives the bytes back
def os.put16_self(+o: B.Octets, +off: Nat, +c: U32, +hc: {{B.Octets.be16_at(o, off) == Some{{c}} : Maybe<&2, U32>}}, +hl: {{Nat.is_le(Nat.add(off, 2n), B.Octets.len(o)) == True{{}} : Bool}}) -> {{K.inet_put16(o, off, c) == o : B.Octets}}:
  %BL.octets_take_drop(off, o) : {{K.inet_put16(o, off, c) == _ : B.Octets}}
  %BL.octets_take_drop(2n, B.Octets.drop(off, o)) : {{K.inet_put16(o, off, c) == B.Octets.append(B.Octets.take(off, o), _) : B.Octets}}
  %Equal.sym(B.Octets, B.Octets.drop(2n, B.Octets.drop(off, o)), B.Octets.drop(Nat.add(off, 2n), o), BL.octets_drop_drop(off, 2n, o)) : {{K.inet_put16(o, off, c) == B.Octets.append(B.Octets.take(off, o), B.Octets.append(B.Octets.take(2n, B.Octets.drop(off, o)), _)) : B.Octets}}
  %os.be16_self(B.Octets.drop(off, o), c, Equal.trans(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.drop(off, o), 0n), B.Octets.be16_at(o, off), Some{{c}}, Equal.trans(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.drop(off, o), 0n), B.Octets.be16_at(o, Nat.add(off, 0n)), B.Octets.be16_at(o, off), BL.octets_be16_at_drop(off, o, 0n), Equal.cong(Nat, Maybe<&2, U32>, z => B.Octets.be16_at(o, z), Nat.add(off, 0n), off, os.add_zero(off))), hc), Equal.trans(Bool, Nat.is_le(2n, B.Octets.len(B.Octets.drop(off, o))), Nat.is_le(2n, Nat.sub(B.Octets.len(o), off)), True{{}}, Equal.cong(Nat, Bool, z => Nat.is_le(2n, z), B.Octets.len(B.Octets.drop(off, o)), Nat.sub(B.Octets.len(o), off), BL.octets_len_drop(off, o)), os.le_sub(off, 2n, B.Octets.len(o), hl))) : {{K.inet_put16(o, off, c) == B.Octets.append(B.Octets.take(off, o), B.Octets.append(_, B.Octets.drop(Nat.add(off, 2n), o))) : B.Octets}}
  {{==}}
""")

# ---- a verified checksum field is the checksum the builder computes
w(f"""
# More Nat facts

def os.nat_eq(x: Nat, y: Nat, +h: {{Nat.is_eq(x, y) == True{{}} : Bool}}) -> {{x == y : Nat}}:
  match x y:
    case 0n 0n:
      {{==}}
    case 0n 1n+q:
      Empty.absurd({{0n == 1n+q : Nat}}, os.ft(h))
    case 1n+p 0n:
      Empty.absurd({{1n+p == 0n : Nat}}, os.ft(h))
    case 1n+ +p 1n+ +q:
      os.succ_cong(p, q, os.nat_eq(p, q, h))

# x <= y and y <= x: x is y
def os.le_antisym(x: Nat, y: Nat, +h1: {{Nat.is_le(x, y) == True{{}} : Bool}}, +h2: {{Nat.is_le(y, x) == True{{}} : Bool}}) -> {{Nat.is_eq(x, y) == True{{}} : Bool}}:
  match x y:
    case 0n 0n:
      {{==}}
    case 0n 1n+q:
      Empty.absurd({{Nat.is_eq(0n, 1n+q) == True{{}} : Bool}}, os.ft(h2))
    case 1n+p 0n:
      Empty.absurd({{Nat.is_eq(1n+p, 0n) == True{{}} : Bool}}, os.ft(h1))
    case 1n+ +p 1n+ +q:
      os.le_antisym(p, q, h1, h2)

def os.add_cancel_r(+x: Nat, +y: Nat, k: Nat, +e: {{Nat.add(x, k) == Nat.add(y, k) : Nat}}) -> {{x == y : Nat}}:
  match k:
    case 0n:
      Equal.trans(Nat, x, Nat.add(x, 0n), y, Equal.sym(Nat, Nat.add(x, 0n), x, os.add_zero(x)), Equal.trans(Nat, Nat.add(x, 0n), Nat.add(y, 0n), y, e, os.add_zero(y)))
    case 1n+ +q:
      os.add_cancel_r(x, y, q, os.succ_inj(Nat.add(x, q), Nat.add(y, q), Equal.trans(Nat, 1n+Nat.add(x, q), Nat.add(x, 1n+q), 1n+Nat.add(y, q), Equal.sym(Nat, Nat.add(x, 1n+q), 1n+Nat.add(x, q), os.add_succ(x, q)), Equal.trans(Nat, Nat.add(x, 1n+q), Nat.add(y, 1n+q), 1n+Nat.add(y, q), e, os.add_succ(y, q)))))

# s + x = 2d with s <= d: d <= x
def os.big_x(+d: Nat, +s: Nat, +x: Nat, +hs: {{Nat.is_le(s, d) == True{{}} : Bool}}, +e: {{Nat.add(s, x) == Nat.add(d, d) : Nat}}) -> {{Nat.is_le(d, x) == True{{}} : Bool}}:
  Equal.trans(Bool, Nat.is_le(d, x), Nat.is_le(Nat.add(d, d), Nat.add(d, x)), True{{}}, Equal.sym(Bool, Nat.is_le(Nat.add(d, d), Nat.add(d, x)), Nat.is_le(d, x), os.le_cancel_l(d, d, x)), Equal.trans(Bool, Nat.is_le(Nat.add(d, d), Nat.add(d, x)), Nat.is_le(Nat.add(s, x), Nat.add(d, x)), True{{}}, Equal.cong(Nat, Bool, z => Nat.is_le(z, Nat.add(d, x)), Nat.add(d, d), Nat.add(s, x), Equal.sym(Nat, Nat.add(s, x), Nat.add(d, d), e)), os.le_add_mono(s, x, d, x, hs, os.le_refl(x))))

# rep(s + x) = d with s, x <= d and x not d: s + x = d
def os.rep_eq_d.go(b: Bool, +d: Nat, +hd: {{Nat.is_le(1n, d) == True{{}} : Bool}}, +s: Nat, +x: Nat, +eb: {{Nat.is_le(Nat.add(s, x), d) == b : Bool}}, +hs: {{Nat.is_le(s, d) == True{{}} : Bool}}, +hx: {{Nat.is_le(x, d) == True{{}} : Bool}}, +hne: {{Nat.is_eq(x, d) == False{{}} : Bool}}, +h: {{os.rep(d, Nat.add(s, x)) == d : Nat}}) -> {{Nat.add(s, x) == d : Nat}}:
  match b:
    case True{{}}:
      Equal.trans(Nat, Nat.add(s, x), os.rep(d, Nat.add(s, x)), d, Equal.sym(Nat, os.rep(d, Nat.add(s, x)), Nat.add(s, x), os.rep_small(d, Nat.add(s, x), eb)), h)
    case False{{}}:
      +j = Nat.sub(Nat.add(s, x), 1n+d)
      +eX = os.sub_split(Nat.add(s, x), d, eb)
      +hab = os.le_add_mono(s, x, d, d, hs, hx)
      +h1 = os.end_le(d, j, Nat.add(s, x), eX, hab)
      +r1 = Equal.trans(Nat, os.rep(d, Nat.add(s, x)), os.rep(d, Nat.add(1n+j, d)), 1n+j, Equal.cong(Nat, Nat, z => os.rep(d, z), Nat.add(s, x), Nat.add(1n+j, d), eX), Equal.trans(Nat, os.rep(d, Nat.add(1n+j, d)), os.rep(d, 1n+j), 1n+j, os.rep_period1(d, j, hd), os.rep_small(d, 1n+j, h1)))
      +ejd = Equal.trans(Nat, 1n+j, os.rep(d, Nat.add(s, x)), d, Equal.sym(Nat, os.rep(d, Nat.add(s, x)), 1n+j, r1), h)
      +e2 = Equal.trans(Nat, Nat.add(s, x), Nat.add(1n+j, d), Nat.add(d, d), eX, Equal.cong(Nat, Nat, z => Nat.add(z, d), 1n+j, d, ejd))
      Empty.absurd({{Nat.add(s, x) == d : Nat}}, os.tf(Equal.trans(Bool, True{{}}, Nat.is_eq(x, d), False{{}}, Equal.sym(Bool, Nat.is_eq(x, d), True{{}}, os.le_antisym(x, d, hx, os.big_x(d, s, x, hs, e2))), hne)))

def os.rep_eq_d(+d: Nat, +hd: {{Nat.is_le(1n, d) == True{{}} : Bool}}, +s: Nat, +x: Nat, +hs: {{Nat.is_le(s, d) == True{{}} : Bool}}, +hx: {{Nat.is_le(x, d) == True{{}} : Bool}}, +hne: {{Nat.is_eq(x, d) == False{{}} : Bool}}, +h: {{os.rep(d, Nat.add(s, x)) == d : Nat}}) -> {{Nat.add(s, x) == d : Nat}}:
  os.rep_eq_d.go(Nat.is_le(Nat.add(s, x), d), d, hd, s, x, {{==}}, hs, hx, hne, h)

# A field read by be16_at is a 16-bit value

def os.mpick(m: Maybe<&2, U32>, t: Type, f: Type) -> Type:
  match m:
    case Some{{x}}:
      t
    case None{{}}:
      f

def os.be16_fits.l(+d: Nat, {HD}, ys: List<&2, U32>, +c: U32, +eY: {{B.be16.head(ys) == Some{{c}} : Maybe<&2, U32>}}) -> {fits("c")}:
  match ys:
    case Nil{{}}:
      %eY : os.mpick(_, {fits("c")}, Unit)
      Unit{{}}
    case Con{{+a, t}}:
      match t:
        case Nil{{}}:
          %eY : os.mpick(_, {fits("c")}, Unit)
          Unit{{}}
        case Con{{+b, +t2}}:
          %Equal.cong(Maybe<&2, U32>, U32, z => os.some_get(z, c), Some{{os.be16_word(a, b)}}, Some{{c}}, eY) : {{Nat.is_le(U32.to_nat(_), d) == True{{}} : Bool}}
          %Equal.sym(Nat, {v("os.mk(W.W64.bits.cat(8n, 8n, B.bits8(b), B.bits8(a)), Word.zero(16n))")}, {w16("W.W64.bits.cat(8n, 8n, B.bits8(b), B.bits8(a))")}, os.mk_zero_value(W.W64.bits.cat(8n, 8n, B.bits8(b), B.bits8(a)))) : {{Nat.is_le(_, d) == True{{}} : Bool}}
          os.w16_le(d, hD, W.W64.bits.cat(8n, 8n, B.bits8(b), B.bits8(a)))

def os.be16_fits(+d: Nat, {HD}, +o: B.Octets, +off: Nat, +c: U32, +hc: {{B.Octets.be16_at(o, off) == Some{{c}} : Maybe<&2, U32>}}) -> {fits("c")}:
  os.be16_fits.l(d, hD, B.Octets.to_list(B.Octets.slice(off, 2n, o)), c, hc)
""")
PUTc = "K.inet_put16(o, off, c)"
Sc = "K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, c)))"
S0_ = "K.inet_sum(B.Octets.append(pseudo, K.inet_put16(o, off, 0)))"
CC_ = f"K.inet_finish({S0_})"
K3_ = "os.K3(pseudo, o, off)"
BEc = "B.Octets.to_list(B.Octets.be16(c))"
VS0 = v(S0_)
w(f"""
# o's field at off verified (pseudo ++ o sums to d): the sum with the field
# 0, plus the field, goes round to d
def os.verified_sum({DPAR}, +pseudo: B.Octets, +o: B.Octets, +off: Nat, +c: U32, +eP: {{K.inet_even(pseudo) == True{{}} : Bool}}, +eT: {{K.inet_even(B.Octets.take(off, o)) == True{{}} : Bool}}, +hc: {{B.Octets.be16_at(o, off) == Some{{c}} : Maybe<&2, U32>}}, +hl: {{Nat.is_le(Nat.add(off, 2n), B.Octets.len(o)) == True{{}} : Bool}}, +hv: {{K.inet_verify(B.Octets.append(pseudo, o)) == True{{}} : Bool}}) -> {{os.rep(d, Nat.add({VS0}, {v("c")})) == d : Nat}}:
  +es = os.put16_self(o, off, c, hc, hl)
  +fc = os.be16_fits(d, hD, o, off, c, hc)
  +f0 = os.sum0_fits(d, hd, hD, hE, pseudo, o, off, eP, eT)
  +hv1 = Equal.trans(Bool, K.inet_verify(B.Octets.append(pseudo, {PUTc})), K.inet_verify(B.Octets.append(pseudo, o)), True{{}}, Equal.cong(B.Octets, Bool, z => K.inet_verify(B.Octets.append(pseudo, z)), {PUTc}, o, es), hv)
  +vS1 = Equal.trans(Nat, {v(Sc)}, {v("65535")}, d, os.nat_eq({v(Sc)}, {v("65535")}, Equal.trans(Bool, Nat.is_eq({v(Sc)}, {v("65535")}), U32.is_eq({Sc}, 65535), True{{}}, Equal.sym(Bool, U32.is_eq({Sc}, 65535), Nat.is_eq({v(Sc)}, {v("65535")}), UL.u32_eq_value({Sc}, 65535)), hv1)), hE)
  +r1 = Equal.trans(Nat, os.rep(d, Nat.add({K3_}, {v("c")})), {v(Sc)}, d, Equal.sym(Nat, {v(Sc)}, os.rep(d, Nat.add({K3_}, {v("c")})), Equal.trans(Nat, {v(Sc)}, os.rep(d, Nat.add({K3_}, os.ws({BEc}))), os.rep(d, Nat.add({K3_}, {v("c")})), os.sum_put(d, hd, hD, hE, pseudo, o, off, c, eP, eT), Equal.cong(Nat, Nat, z => os.rep(d, Nat.add({K3_}, z)), os.ws({BEc}), {v("c")}, os.be16_ws(d, hD, c, fc)))), vS1)
  Equal.trans(Nat, os.rep(d, Nat.add({VS0}, {v("c")})), os.rep(d, Nat.add(os.rep(d, {K3_}), {v("c")})), d, Equal.cong(Nat, Nat, z => os.rep(d, Nat.add(z, {v("c")})), {VS0}, os.rep(d, {K3_}), os.sum0(d, hd, hD, hE, pseudo, o, off, eP, eT)), Equal.trans(Nat, os.rep(d, Nat.add(os.rep(d, {K3_}), {v("c")})), os.rep(d, Nat.add({K3_}, {v("c")})), d, os.rep_fold(d, {K3_}, {v("c")}, hd), r1))

# and the field is not 0xffff: the checksum inet_fill computes is that
# field, so inet_fill gives o back
def os.fill_self({DPAR}, +pseudo: B.Octets, +o: B.Octets, +off: Nat, +c: U32, +eP: {{K.inet_even(pseudo) == True{{}} : Bool}}, +eT: {{K.inet_even(B.Octets.take(off, o)) == True{{}} : Bool}}, +hc: {{B.Octets.be16_at(o, off) == Some{{c}} : Maybe<&2, U32>}}, +hl: {{Nat.is_le(Nat.add(off, 2n), B.Octets.len(o)) == True{{}} : Bool}}, +hv: {{K.inet_verify(B.Octets.append(pseudo, o)) == True{{}} : Bool}}, +hk: {{U32.is_eq(c, 65535) == False{{}} : Bool}}) -> {{K.inet_fill(pseudo, o, off) == o : B.Octets}}:
  +es = os.put16_self(o, off, c, hc, hl)
  +fc = os.be16_fits(d, hD, o, off, c, hc)
  +f0 = os.sum0_fits(d, hd, hD, hE, pseudo, o, off, eP, eT)
  +r2 = os.verified_sum(d, hd, hD, hE, pseudo, o, off, c, eP, eT, hc, hl, hv)
  +hne = Equal.trans(Bool, Nat.is_eq({v("c")}, d), Nat.is_eq({v("c")}, {v("65535")}), False{{}}, Equal.cong(Nat, Bool, z => Nat.is_eq({v("c")}, z), d, {v("65535")}, Equal.sym(Nat, {v("65535")}, d, hE)), Equal.trans(Bool, Nat.is_eq({v("c")}, {v("65535")}), U32.is_eq(c, 65535), False{{}}, Equal.sym(Bool, U32.is_eq(c, 65535), Nat.is_eq({v("c")}, {v("65535")}), UL.u32_eq_value(c, 65535)), hk))
  +e1 = os.rep_eq_d(d, hd, {VS0}, {v("c")}, f0, fc, hne, r2)
  +e3 = Equal.trans(Nat, Nat.add({v(CC_)}, {VS0}), d, Nat.add({v("c")}, {VS0}), os.finish_value(d, hD, {S0_}, f0), Equal.trans(Nat, d, Nat.add({VS0}, {v("c")}), Nat.add({v("c")}, {VS0}), Equal.sym(Nat, Nat.add({VS0}, {v("c")}), d, e1), os.add_comm({VS0}, {v("c")})))
  +e5 = UL.u32_value_eq({CC_}, c, os.add_cancel_r({v(CC_)}, {v("c")}, {VS0}, e3))
  %Equal.sym(U32, {CC_}, c, e5) : {{K.inet_put16(o, off, _) == o : B.Octets}}
  es
""")

# define each lemma before its first use
out = "".join(P)
def cut(s, name):
    a = s.index("\ndef " + name + "(")
    b = s.find("\ndef ", a + 1)
    if b < 0:
        b = len(s)
    return s[:a] + s[b:], s[a:b]
moved = []
for n in ["os.g_add_assoc", "os.g_complement", "os.g_update_add", "os.g_update_comm", "os.g_sum_swap"]:
    out, blk = cut(out, n)
    moved.append(blk)
out, sw = cut(out, "os.swap")
i = out.index("\ndef os.g_update_add.v(")
out = out[:i] + sw + out[i:]
out = out.rstrip() + "\n" + "".join(moved)
emit("proof_ones.bend", out.rstrip() + chr(10))

# ---- PROOF_sum.bend: the laws of LAWS_sum.bend
Q = []
q = Q.append
D = "Word.to_nat(16n, Word.not(16n, Word.zero(16n)))"
DA4 = f"{D}, S.os.hd(), S.os.hD(), S.os.hE()"
def tlq(x): return "B.Octets.to_list(%s)" % x
def lnq(x): return "B.Octets.len(%s)" % x
EMPTY = "B.Octets.empty()"
def pat1(*names): return ", ".join("U32{%s}" % n for n in names)
ADDR = lambda n: "I6.Ipv6Addr{%s}" % pat1(*[n + str(i) for i in range(4)])
q(f"""# Proofs of LAWS_sum.bend, written by ref/gen_sum.py. The one's complement
# lemmas are in proof_ones.bend (see its comments); here they are applied to
# the headers: each checksum is inet_fill (or UDP's variant, which sends a
# computed 0 as 0xffff) at an even offset inside the data, after a
# pseudo-header of even length, and writing the field keeps the data's
# length, so the pseudo-header the verifier builds is the one the builder
# summed. The lemmas take d = 2^16 - 1 as a variable; the laws instantiate
# it with S.os.hd, S.os.hD and S.os.hE.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./netheaders.bend as N
import ./checksum.bend as K
import ./ipv4.bend as I4
import ./ipv6.bend as I6
import ./icmp.bend as C
import ./udp.bend as U
import ./tcp.bend as T
import ./proof_ones.bend as S
import ./LAWS_sum.bend as Laws

# The algebra

def Laws.inet_add_comm(a, b):
  S.os.g_add_comm(a, b)

def Laws.inet_add_bound(a, b, ha, hb):
  S.os.g_add_bound({DA4}, a, b, ha, hb)

def Laws.inet_add_no_carry(a, b, ha, hb, h):
  S.os.g_no_carry({DA4}, a, b, ha, hb, h)

def Laws.inet_add_end_around(a, b, ha, hb, h):
  S.os.g_end_around({DA4}, a, b, ha, hb, h)

def Laws.inet_add_zero(a, ha):
  S.os.g_add_zero({DA4}, a, ha)

def Laws.inet_add_assoc(a, b, c, ha, hb, hc):
  S.os.g_add_assoc({DA4}, a, b, c, ha, hb, hc)

def Laws.inet_add_complement(a, ha):
  S.os.g_complement({DA4}, a, ha)

def Laws.inet_finish_bound(a):
  S.os.g_finish_bound({DA4}, a)

def Laws.inet_update_bound(acc, o, ha):
  S.os.g_update_bound({DA4}, acc, o, ha)

def Laws.inet_update_add(acc, w, o, ha, hw):
  S.os.g_update_add({DA4}, acc, w, o, ha, hw)

def Laws.inet_update_comm(acc, x, y, ha):
  S.os.g_update_comm({DA4}, acc, x, y, ha)

def Laws.inet_sum_swap(x, y, ex, ey):
  S.os.g_sum_swap({DA4}, x, y, ex, ey)

def Laws.inet_fill_verifies(pseudo, o, k, ep, hl):
  S.os.fill_verifies({DA4}, pseudo, o, Nat.double(k), ep, S.os.even_take(o, k, hl))

# Pseudo-headers have even lengths

def h.be32_even_cons(v: U32, +rest: List<&2, U32>) -> {{K.inet_even.list(B.mask(B.append(B.be32(v), rest))) == K.inet_even.list(B.mask(rest)) : Bool}}:
  match v:
    case U32{{x}}:
      {{==}}

def h.pseudo4_even.m(src: U32, dst: U32, +p: U32, +len: U32) -> {{K.inet_even.list(B.mask(B.append(B.be32(src), B.append(B.be32(dst), B.append([0, B.byte(p)], B.be16(len)))))) == True{{}} : Bool}}:
  match src dst:
    case U32{{a}} U32{{b}}:
      S.os.be16_even.m(len)

def h.pseudo4_even(+src: U32, +dst: U32, +p: U32, +len: U32) -> {{K.inet_even(I4.ipv4_pseudo(src, dst, p, len)) == True{{}} : Bool}}:
  %Equal.sym(List<&2, U32>, {tlq("B.Octets.of_list(B.append(B.be32(src), B.append(B.be32(dst), B.append([0, B.byte(p)], B.be16(len)))))")}, B.mask(B.append(B.be32(src), B.append(B.be32(dst), B.append([0, B.byte(p)], B.be16(len))))), BL.octets_to_of(B.append(B.be32(src), B.append(B.be32(dst), B.append([0, B.byte(p)], B.be16(len)))))) : {{K.inet_even.list(_) == True{{}} : Bool}}
  h.pseudo4_even.m(src, dst, p, len)

def h.pseudo6_even.m(src: I6.Ipv6Addr, dst: I6.Ipv6Addr, +len: U32, +n: U32) -> {{K.inet_even.list(B.mask(B.append(I6.Ipv6Addr.list(src), B.append(I6.Ipv6Addr.list(dst), B.append(B.be32(len), [0, 0, 0, B.byte(n)]))))) == True{{}} : Bool}}:
  match src dst:
    case {ADDR("a")} {ADDR("b")}:
      h.be32_even_cons(len, [0, 0, 0, B.byte(n)])

def h.pseudo6_even(+src: I6.Ipv6Addr, +dst: I6.Ipv6Addr, +len: U32, +n: U32) -> {{K.inet_even(I6.ipv6_pseudo(src, dst, len, n)) == True{{}} : Bool}}:
  %Equal.sym(List<&2, U32>, {tlq("B.Octets.of_list(B.append(I6.Ipv6Addr.list(src), B.append(I6.Ipv6Addr.list(dst), B.append(B.be32(len), [0, 0, 0, B.byte(n)]))))")}, B.mask(B.append(I6.Ipv6Addr.list(src), B.append(I6.Ipv6Addr.list(dst), B.append(B.be32(len), [0, 0, 0, B.byte(n)])))), BL.octets_to_of(B.append(I6.Ipv6Addr.list(src), B.append(I6.Ipv6Addr.list(dst), B.append(B.be32(len), [0, 0, 0, B.byte(n)]))))) : {{K.inet_even.list(_) == True{{}} : Bool}}
  h.pseudo6_even.m(src, dst, len, n)
""")
# lengths of built headers followed by data
def lenlaw(name, ty, rest, pat, n, data="data"):
    M = f"B.Octets.append({ty}.build(h), {data})"
    q(f"""
def h.{name}.m(h: {ty}, +{data}: B.Octets) -> {{Nat.is_le({n}n, Nat.add(B.len({ty}.build.list(h)), {lnq(data)})) == True{{}} : Bool}}:
  match h:
    case {pat}:
      S.os.le_zero({rest})

def h.{name}(+h: {ty}, +{data}: B.Octets) -> {{Nat.is_le({n}n, {lnq(M)}) == True{{}} : Bool}}:
  %Equal.sym(Nat, {lnq(M)}, Nat.add({lnq(ty + ".build(h)")}, {lnq(data)}), BL.octets_len_append({ty}.build(h), {data})) : {{Nat.is_le({n}n, _) == True{{}} : Bool}}
  %Equal.sym(Nat, {lnq("B.Octets.of_list(" + ty + ".build.list(h))")}, B.len({ty}.build.list(h)), BL.octets_len_of_list({ty}.build.list(h))) : {{Nat.is_le({n}n, Nat.add(_, {lnq(data)})) == True{{}} : Bool}}
  h.{name}.m(h, {data})
""")
lenlaw("icmp_len", "C.IcmpHeader", "B.Octets.len(data)", "C.IcmpHeader{" + pat1("t", "c", "k", "r") + "}", 8)
lenlaw("udp_len", "U.UdpHeader", "B.Octets.len(payload)", "U.UdpHeader{" + pat1("a", "b", "c", "e") + "}", 8, "payload")
lenlaw("tcp_len", "T.TcpHeader", "Nat.add(B.len(B.Octets.to_list(o)), B.Octets.len(payload))", "T.TcpHeader{" + pat1("a", "b", "sq", "ak", "off", "rs", "fl", "win", "ck", "ur") + ", o}", 20, "payload")

q(f"""
def h.le_trans(+x: Nat, +y: Nat, +z: Nat, +h1: {{Nat.is_le(x, y) == True{{}} : Bool}}, +h2: {{Nat.is_le(y, z) == True{{}} : Bool}}) -> {{Nat.is_le(x, z) == True{{}} : Bool}}:
  S.os.le_trans(x, y, z, h1, h2)

# ICMP

def Laws.icmp_build_verifies(h, data):
  %BL.octets_append_empty_l(K.inet_fill({EMPTY}, B.Octets.append(C.IcmpHeader.build(h), data), 2n)) : {{K.inet_verify(_) == True{{}} : Bool}}
  S.os.fill_verifies({DA4}, {EMPTY}, B.Octets.append(C.IcmpHeader.build(h), data), 2n, {{==}}, S.os.even_take(B.Octets.append(C.IcmpHeader.build(h), data), 1n, h.le_trans(2n, 8n, {lnq("B.Octets.append(C.IcmpHeader.build(h), data)")}, {{==}}, h.icmp_len(h, data))))
""")
# the verifier's pseudo-header has the length the builder used
def keep_len(name, args, M, off, CK, pseudo_of, goal_lhs, n8, lenproof, inner):
    PUT = f"K.inet_put16({M}, {off}, {CK})"
    q(f"""
def {name}({args}) -> {{K.inet_verify(B.Octets.append({pseudo_of("U32.from_nat(" + lnq(goal_lhs) + ")")}, {goal_lhs})) == True{{}} : Bool}}:
  %Equal.sym(Nat, {lnq(PUT)}, {lnq(M)}, S.os.len_put16({M}, {off}, {CK}, h.le_trans(Nat.add({off}, 2n), {n8}, {lnq(M)}, {{==}}, {lenproof}))) : {{K.inet_verify(B.Octets.append({pseudo_of("U32.from_nat(_)")}, {goal_lhs})) == True{{}} : Bool}}
  {inner}
""")

A6 = "+src: I6.Ipv6Addr, +dst: I6.Ipv6Addr"
A4 = "+src: U32, +dst: U32"
# ICMPv6
M6 = "B.Octets.append(C.IcmpHeader.build(h), data)"
P6 = lambda L: f"I6.ipv6_pseudo(src, dst, {L}, 58)"
CK6 = f"K.inet_checksum(B.Octets.append({P6('U32.from_nat(' + lnq(M6) + ')')}, K.inet_put16({M6}, 2n, 0)))"
keep_len("h.icmp6", A6 + ", +h: C.IcmpHeader, +data: B.Octets", M6, "2n", CK6, P6, "C.IcmpHeader.build_ipv6(src, dst, h, data)", "8n", "h.icmp_len(h, data)",
         f"S.os.fill_verifies({DA4}, {P6('U32.from_nat(' + lnq(M6) + ')')}, {M6}, 2n, h.pseudo6_even(src, dst, U32.from_nat({lnq(M6)}), 58), S.os.even_take({M6}, 1n, h.le_trans(2n, 8n, {lnq(M6)}, " + "{==}" + ", h.icmp_len(h, data))))")
q("""
def Laws.icmp6_build_verifies(src, dst, h, data):
  h.icmp6(src, dst, h, data)
""")
# TCP
MT = "B.Octets.append(T.TcpHeader.build(h), payload)"
for fam, AA, P_, ver in [("4", A4, lambda L: f"I4.ipv4_pseudo(src, dst, 6, {L})", "h.pseudo4_even(src, dst, 6, U32.from_nat(%s))"),
                     ("6", A6, lambda L: f"I6.ipv6_pseudo(src, dst, {L}, 6)", "h.pseudo6_even(src, dst, U32.from_nat(%s), 6)")]:
    CKT = f"K.inet_checksum(B.Octets.append({P_('U32.from_nat(' + lnq(MT) + ')')}, K.inet_put16({MT}, 16n, 0)))"
    keep_len(f"h.tcp{fam}", AA + ", +h: T.TcpHeader, +payload: B.Octets", MT, "16n", CKT, P_, f"T.TcpHeader.build_ipv{fam}(src, dst, h, payload)", "20n", "h.tcp_len(h, payload)",
             f"S.os.fill_verifies({DA4}, {P_('U32.from_nat(' + lnq(MT) + ')')}, {MT}, 16n, {ver % lnq(MT)}, S.os.even_take({MT}, 8n, h.le_trans(16n, 20n, {lnq(MT)}, " + "{==}" + ", h.tcp_len(h, payload))))")
    q(f"""
def Laws.tcp_ipv{fam}_build_verifies(src, dst, h, payload):
  h.tcp{fam}(src, dst, h, payload)
""")


# UDP: the checksum written is nonzero(c), 0xffff when the computed c is 0
MU = "B.Octets.append(U.UdpHeader.build(h), payload)"
def S0of(ps, o): return f"K.inet_sum(B.Octets.append({ps}, K.inet_put16({o}, 6n, 0)))"
def CKof(ps, o): return f"K.inet_checksum(B.Octets.append({ps}, K.inet_put16({o}, 6n, 0)))"
EV = "+eP: {K.inet_even(pseudo) == True{} : Bool}, +eT: {K.inet_even(B.Octets.take(6n, o)) == True{} : Bool}"
q(f"""
# the field written by UdpHeader.fill verifies, in both cases of nonzero
def h.udp_nz(z: Bool, +pseudo: B.Octets, +o: B.Octets, {EV}, +ez: {{U32.is_eq({CKof("pseudo", "o")}, 0) == z : Bool}}) -> {{K.inet_verify(B.Octets.append(pseudo, K.inet_put16(o, 6n, U.UdpHeader.nonzero.go(z, {CKof("pseudo", "o")})))) == True{{}} : Bool}}:
  match z:
    case True{{}}:
      S.os.verify_put({DA4}, pseudo, o, 6n, eP, eT, 65535, S.os.fit65535({D}, S.os.hE()), S.os.allones_sum({DA4}, pseudo, o, 6n, eP, eT, ez))
    case False{{}}:
      S.os.verify_put({DA4}, pseudo, o, 6n, eP, eT, K.inet_finish({S0of("pseudo", "o")}), S.os.finish_fits({D}, S.os.hD(), {S0of("pseudo", "o")}), S.os.fill_sum({DA4}, pseudo, o, 6n, eP, eT))

# the field read back: nonzero(c) is never 0
def h.nz_low(z: Bool, +c: U32, +hc: {{Nat.is_le(U32.to_nat(c), {D}) == True{{}} : Bool}}, +ez: {{U32.is_eq(c, 0) == z : Bool}}) -> {{U32.is_eq(B.low16(U.UdpHeader.nonzero.go(z, c)), 0) == False{{}} : Bool}}:
  match z:
    case True{{}}:
      {{==}}
    case False{{}}:
      %Equal.sym(U32, B.low16(c), c, S.os.low16_fit({D}, S.os.hD(), c, hc)) : {{U32.is_eq(_, 0) == False{{}} : Bool}}
      ez

def h.be16_2(+x: U32) -> {{Nat.is_le(Nat.add(0n, 2n), B.Octets.len(B.Octets.be16(x))) == True{{}} : Bool}}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.be16(x)), 2n, BL.octets_len_be16(x)) : {{Nat.is_le(Nat.add(0n, 2n), _) == True{{}} : Bool}}
  {{==}}
""")
TK6 = "B.Octets.take(6n, o)"
DR8 = "B.Octets.drop(Nat.add(6n, 2n), o)"
REST = f"B.Octets.append(B.Octets.be16(x), {DR8})"
q(f"""
# the 16-bit field at offset 6 of o with x written there reads x's low 16 bits
def h.zf(+o: B.Octets, +x: U32, +h8: {{Nat.is_le(8n, B.Octets.len(o)) == True{{}} : Bool}}) -> {{U.UdpHeader.zero_field(B.Octets.be16_at(K.inet_put16(o, 6n, x), 6n)) == U32.is_eq(B.low16(x), 0) : Bool}}:
  %Equal.cong(Nat, Nat, z => Nat.add(z, 0n), B.Octets.len({TK6}), 6n, BL.octets_len_take_le(6n, o, h.le_trans(6n, 8n, B.Octets.len(o), {{==}}, h8))) : {{U.UdpHeader.zero_field(B.Octets.be16_at(B.Octets.append({TK6}, {REST}), _)) == U32.is_eq(B.low16(x), 0) : Bool}}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.append({TK6}, {REST}), Nat.add(B.Octets.len({TK6}), 0n)), B.Octets.be16_at({REST}, 0n), BL.octets_be16_at_append_add({TK6}, {REST}, 0n)) : {{U.UdpHeader.zero_field(_) == U32.is_eq(B.low16(x), 0) : Bool}}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be16_at({REST}, 0n), B.Octets.be16_at(B.Octets.be16(x), 0n), BL.octets_be16_at_append_le(B.Octets.be16(x), {DR8}, 0n, h.be16_2(x))) : {{U.UdpHeader.zero_field(_) == U32.is_eq(B.low16(x), 0) : Bool}}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.be16(x), 0n), Some{{B.low16(x)}}, BL.octets_be16_round_trip(x)) : {{U.UdpHeader.zero_field(_) == U32.is_eq(B.low16(x), 0) : Bool}}
  {{==}}

def h.go_true(z: Bool, +s: Bool, +hs: {{s == True{{}} : Bool}}) -> {{U.UdpHeader.verify.go(z, True{{}}, s) == True{{}} : Bool}}:
  match z:
    case True{{}}:
      {{==}}
    case False{{}}:
      hs

def h.go_false(z: Bool, +s: Bool, +ez: {{z == False{{}} : Bool}}, +hs: {{s == True{{}} : Bool}}) -> {{U.UdpHeader.verify.go(z, False{{}}, s) == True{{}} : Bool}}:
  match z:
    case True{{}}:
      Empty.absurd({{U.UdpHeader.verify.go(True{{}}, False{{}}, s) == True{{}} : Bool}}, S.os.tf(ez))
    case False{{}}:
      hs
""")
A6 = "+src: I6.Ipv6Addr, +dst: I6.Ipv6Addr"
A4 = "+src: U32, +dst: U32"
for fam, AA, P_, ver in [("4", A4, lambda L: f"I4.ipv4_pseudo(src, dst, 17, {L})", "h.pseudo4_even(src, dst, 17, U32.from_nat(%s))"),
                         ("6", A6, lambda L: f"I6.ipv6_pseudo(src, dst, {L}, 17)", "h.pseudo6_even(src, dst, U32.from_nat(%s), 17)")]:
    PS = P_("U32.from_nat(" + lnq(MU) + ")")
    CKU = CKof(PS, MU)
    NZ = f"U.UdpHeader.nonzero({CKU})"
    BUILT = f"U.UdpHeader.build_ipv{fam}(src, dst, h, payload)"
    PUTNZ = f"K.inet_put16({MU}, 6n, {NZ})"
    EP = ver % lnq(MU)
    ET = f"S.os.even_take({MU}, 3n, h.le_trans(6n, 8n, {lnq(MU)}, " + "{==}" + ", h.udp_len(h, payload)))"
    q(f"""
def h.udp{fam}.sum({AA}, +h: U.UdpHeader, +payload: B.Octets) -> {{K.inet_verify(B.Octets.append({P_("U32.from_nat(" + lnq(BUILT) + ")")}, {BUILT})) == True{{}} : Bool}}:
  %Equal.sym(Nat, {lnq(PUTNZ)}, {lnq(MU)}, S.os.len_put16({MU}, 6n, {NZ}, h.le_trans(Nat.add(6n, 2n), 8n, {lnq(MU)}, {{==}}, h.udp_len(h, payload)))) : {{K.inet_verify(B.Octets.append({P_("U32.from_nat(_)")}, {BUILT})) == True{{}} : Bool}}
  h.udp_nz(U32.is_eq({CKU}, 0), {PS}, {MU}, {EP}, {ET}, {{==}})
""")
q(f"""
def Laws.udp_ipv4_build_verifies(src, dst, h, payload):
  h.go_true(U.UdpHeader.zero_field(B.Octets.be16_at(U.UdpHeader.build_ipv4(src, dst, h, payload), 6n)), K.inet_verify(B.Octets.append(I4.ipv4_pseudo(src, dst, 17, U32.from_nat({lnq("U.UdpHeader.build_ipv4(src, dst, h, payload)")})), U.UdpHeader.build_ipv4(src, dst, h, payload))), h.udp4.sum(src, dst, h, payload))
""")
PS6 = f"I6.ipv6_pseudo(src, dst, U32.from_nat({lnq(MU)}), 17)"
CK6U = CKof(PS6, MU)
B6 = "U.UdpHeader.build_ipv6(src, dst, h, payload)"

# ---- the checksum field written by inet_put16 reads back
def OLq(x): return "B.Octets.of_list(%s)" % x
q(f"""
# Writing a 16-bit field

def Laws.inet_put16_len(o, off, v, h):
  S.os.len_put16(o, off, v, h)

def Laws.inet_put16_drop(o, off, v, n, h1, h2):
  %S.os.add_sub(Nat.add(off, 2n), n, h1) : {{B.Octets.drop(_, K.inet_put16(o, off, v)) == B.Octets.drop(n, o) : B.Octets}}
  %Equal.sym(Nat, Nat.add(Nat.add(off, 2n), Nat.sub(n, Nat.add(off, 2n))), Nat.add(off, Nat.add(2n, Nat.sub(n, Nat.add(off, 2n)))), S.os.add_assoc(off, 2n, Nat.sub(n, Nat.add(off, 2n)))) : {{B.Octets.drop(_, K.inet_put16(o, off, v)) == B.Octets.drop(n, o) : B.Octets}}
  %BL.octets_len_take_le(off, o, S.os.le_trans(off, Nat.add(off, 2n), B.Octets.len(o), S.os.le_add_r(off, 2n), h2)) : {{B.Octets.drop(Nat.add(_, Nat.add(2n, Nat.sub(n, Nat.add(off, 2n)))), K.inet_put16(o, off, v)) == B.Octets.drop(n, o) : B.Octets}}
  %Equal.sym(B.Octets, B.Octets.drop(Nat.add(B.Octets.len(B.Octets.take(off, o)), Nat.add(2n, Nat.sub(n, Nat.add(off, 2n)))), B.Octets.append(B.Octets.take(off, o), B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(off, 2n), o)))), B.Octets.drop(Nat.add(2n, Nat.sub(n, Nat.add(off, 2n))), B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(off, 2n), o))), BL.octets_drop_append_add(B.Octets.take(off, o), Nat.add(2n, Nat.sub(n, Nat.add(off, 2n))), B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(off, 2n), o)))) : {{_ == B.Octets.drop(n, o) : B.Octets}}
  %BL.octets_len_be16(v) : {{B.Octets.drop(Nat.add(_, Nat.sub(n, Nat.add(off, 2n))), B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(off, 2n), o))) == B.Octets.drop(n, o) : B.Octets}}
  %Equal.sym(B.Octets, B.Octets.drop(Nat.add(B.Octets.len(B.Octets.be16(v)), Nat.sub(n, Nat.add(off, 2n))), B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(off, 2n), o))), B.Octets.drop(Nat.sub(n, Nat.add(off, 2n)), B.Octets.drop(Nat.add(off, 2n), o)), BL.octets_drop_append_add(B.Octets.be16(v), Nat.sub(n, Nat.add(off, 2n)), B.Octets.drop(Nat.add(off, 2n), o))) : {{_ == B.Octets.drop(n, o) : B.Octets}}
  %Equal.sym(B.Octets, B.Octets.drop(Nat.sub(n, Nat.add(off, 2n)), B.Octets.drop(Nat.add(off, 2n), o)), B.Octets.drop(Nat.add(Nat.add(off, 2n), Nat.sub(n, Nat.add(off, 2n))), o), BL.octets_drop_drop(Nat.add(off, 2n), Nat.sub(n, Nat.add(off, 2n)), o)) : {{_ == B.Octets.drop(n, o) : B.Octets}}
  %Equal.sym(Nat, Nat.add(Nat.add(off, 2n), Nat.sub(n, Nat.add(off, 2n))), n, S.os.add_sub(Nat.add(off, 2n), n, h1)) : {{B.Octets.drop(_, o) == B.Octets.drop(n, o) : B.Octets}}
  {{==}}
""")
# ICMP and UDP headers with the checksum written parse back
def putparse(law, ty, fields, deep, off, nbytes, data):
    names = [f for f, _ in fields]
    H0 = "%s{%s}" % (ty, ", ".join(names))
    HC = "%s{%s}" % (ty, ", ".join("c" if f == "checksum" else f for f in names))
    LP = f"B.append({ty}.build.list({H0}), B.Octets.to_list({data}))"
    RF = f"B.append(B.mask(B.take({off}, {LP})), B.append(B.mask(B.be16(c)), B.mask(B.drop(Nat.add({off}, 2n), {LP}))))"
    RES = f"Result<&2, &2, N.NetError, {ty}>"
    sig_m = ", ".join("%s: U32" % f for f in names) + f", +{data}: B.Octets, c: U32"
    sig = ", ".join("+%s: U32" % f for f in names) + f", +{data}: B.Octets, +c: U32"
    pats = " ".join(pat(f + "_", k) if k else "U32{%s_}" % f for f, k in fields) + " " + pat("c_", 16)
    args = ", ".join(names) + f", {data}, c"
    q(f"""
def h.{law}.m({sig_m}) -> {{{ty}.parse.list({RF}) == Done{{{ty}.norm({HC})}} : {RES}}}:
  match {" ".join(names)} c:
    case {pats}:
      {{==}}

def h.{law}.len.m({", ".join("%s: U32" % f for f in names)}, +{data}: B.Octets) -> {{Nat.is_le(Nat.add({off}, 2n), B.len({LP})) == True{{}} : Bool}}:
  match {" ".join(names)}:
    case {" ".join("U32{%s_}" % f for f in names)}:
      S.os.le_zero({nbytes})

def Laws.{law}({args}):
  %Equal.sym(B.Octets, B.Octets.append({ty}.build({H0}), {data}), {OLq(LP)}, S.os.app_of({ty}.build.list({H0}), {data})) : {{{ty}.parse(K.inet_put16(_, {off}, c)) == Done{{{ty}.norm({HC})}} : {RES}}}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(K.inet_put16({OLq(LP)}, {off}, c)), {RF}, S.os.put16_list({LP}, {off}, c, h.{law}.len.m({", ".join(names)}, {data}))) : {{{ty}.parse.list(_) == Done{{{ty}.norm({HC})}} : {RES}}}
  h.{law}.m({args})
""")
putparse("icmp_put_parse", "C.IcmpHeader", [("msg_type", 8), ("code", 8), ("checksum", 16), ("rest", 32)], None, "2n", "Nat.add(4n, B.len(B.Octets.to_list(data)))", "data")
putparse("udp_put_parse", "U.UdpHeader", [("src_port", 16), ("dst_port", 16), ("length", 16), ("checksum", 0)], None, "6n", "B.len(B.Octets.to_list(payload))", "payload")

# the UDP payload read back
H0U = "U.UdpHeader{src_port, dst_port, length, checksum}"
MUP = f"B.Octets.append(U.UdpHeader.build({H0U}), payload)"
DGU = f"K.inet_put16({MUP}, 6n, c)"
LPL = "B.Octets.len(payload)"
N0 = "U32.to_nat(N.NetField.low(16n, N.NetField.low(16n, length)))"
q(f"""
def h.low_low16(l: U32) -> {{N.NetField.low(16n, N.NetField.low(16n, l)) == N.NetField.low(16n, l) : U32}}:
  match l:
    case {pat("l_", 16)}:
      {{==}}

def h.udp_blen(a: U32, b: U32, l: U32, k: U32) -> {{B.len(U.UdpHeader.build.list(U.UdpHeader{{a, b, l, k}})) == 8n : Nat}}:
  match a b l k:
    case U32{{a_}} U32{{b_}} U32{{l_}} U32{{k_}}:
      {{==}}

def h.udp_len_build(+a: U32, +b: U32, +l: U32, +k: U32) -> {{B.Octets.len(U.UdpHeader.build(U.UdpHeader{{a, b, l, k}})) == 8n : Nat}}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(U.UdpHeader.build.list(U.UdpHeader{{a, b, l, k}}))), B.len(U.UdpHeader.build.list(U.UdpHeader{{a, b, l, k}})), BL.octets_len_of_list(U.UdpHeader.build.list(U.UdpHeader{{a, b, l, k}}))) : {{_ == 8n : Nat}}
  h.udp_blen(a, b, l, k)

def h.udp_dg_len(+src_port: U32, +dst_port: U32, +length: U32, +checksum: U32, +payload: B.Octets, +c: U32) -> {{B.Octets.len({DGU}) == Nat.add(8n, {LPL}) : Nat}}:
  %Equal.sym(Nat, B.Octets.len({DGU}), B.Octets.len({MUP}), S.os.len_put16({MUP}, 6n, c, h.udp_len({H0U}, payload))) : {{_ == Nat.add(8n, {LPL}) : Nat}}
  %Equal.sym(Nat, B.Octets.len({MUP}), Nat.add(B.Octets.len(U.UdpHeader.build({H0U})), {LPL}), BL.octets_len_append(U.UdpHeader.build({H0U}), payload)) : {{_ == Nat.add(8n, {LPL}) : Nat}}
  %Equal.sym(Nat, B.Octets.len(U.UdpHeader.build({H0U})), 8n, h.udp_len_build(src_port, dst_port, length, checksum)) : {{Nat.add(_, {LPL}) == Nat.add(8n, {LPL}) : Nat}}
  {{==}}

def h.udp_drop8(+src_port: U32, +dst_port: U32, +length: U32, +checksum: U32, +payload: B.Octets, +c: U32) -> {{B.Octets.drop(8n, {DGU}) == payload : B.Octets}}:
  %Equal.sym(B.Octets, B.Octets.drop(8n, {DGU}), B.Octets.drop(8n, {MUP}), Laws.inet_put16_drop({MUP}, 6n, c, 8n, {{==}}, h.udp_len({H0U}, payload))) : {{_ == payload : B.Octets}}
  %h.udp_len_build(src_port, dst_port, length, checksum) : {{B.Octets.drop(_, {MUP}) == payload : B.Octets}}
  BL.octets_drop_append(U.UdpHeader.build({H0U}), payload)

def h.sub8(x: Nat) -> {{Nat.sub(Nat.add(8n, x), 8n) == x : Nat}}:
  S.os.sub_zero(x)

def h.ge8(x: Nat) -> {{Nat.is_ge(Nat.add(8n, x), 8n) == True{{}} : Bool}}:
  S.os.ge_zero(x)

def Laws.udp_put_payload(src_port, dst_port, length, checksum, payload, c, hl):
  %Equal.sym(Nat, {N0}, Nat.add(8n, {LPL}), Equal.trans(Nat, {N0}, U32.to_nat(N.NetField.low(16n, length)), Nat.add(8n, {LPL}), Equal.cong(U32, Nat, z => U32.to_nat(z), N.NetField.low(16n, N.NetField.low(16n, length)), N.NetField.low(16n, length), h.low_low16(length)), hl)) : {{U.UdpHeader.payload.go(Nat.is_ge(_, 8n), Nat.sub(_, 8n), {DGU}) == Done{{payload}} : Result<&2, &2, N.NetError, B.Octets>}}
  %Equal.sym(Bool, Nat.is_ge(Nat.add(8n, {LPL}), 8n), True{{}}, h.ge8({LPL})) : {{U.UdpHeader.payload.go(_, Nat.sub(Nat.add(8n, {LPL}), 8n), {DGU}) == Done{{payload}} : Result<&2, &2, N.NetError, B.Octets>}}
  %Equal.sym(Nat, Nat.sub(Nat.add(8n, {LPL}), 8n), {LPL}, h.sub8({LPL})) : {{U.UdpHeader.payload.go(True{{}}, _, {DGU}) == Done{{payload}} : Result<&2, &2, N.NetError, B.Octets>}}
  %Equal.sym(Nat, B.Octets.len({DGU}), Nat.add(8n, {LPL}), h.udp_dg_len(src_port, dst_port, length, checksum, payload, c)) : {{N.net.check(B.Octets, Nat.is_le(Nat.add(8n, {LPL}), _), N.NetTruncated{{}}, B.Octets.slice(8n, {LPL}, {DGU})) == Done{{payload}} : Result<&2, &2, N.NetError, B.Octets>}}
  %Equal.sym(Bool, Nat.is_le(Nat.add(8n, {LPL}), Nat.add(8n, {LPL})), True{{}}, S.os.le_refl(Nat.add(8n, {LPL}))) : {{N.net.check(B.Octets, _, N.NetTruncated{{}}, B.Octets.slice(8n, {LPL}, {DGU})) == Done{{payload}} : Result<&2, &2, N.NetError, B.Octets>}}
  %Equal.sym(B.Octets, B.Octets.drop(8n, {DGU}), payload, h.udp_drop8(src_port, dst_port, length, checksum, payload, c)) : {{Done{{B.Octets.take({LPL}, _)}} == Done{{payload}} : Result<&2, &2, N.NetError, B.Octets>}}
  %Equal.sym(B.Octets, B.Octets.take({LPL}, payload), payload, BL.octets_take_len(payload)) : {{Done{{_}} == Done{{payload}} : Result<&2, &2, N.NetError, B.Octets>}}
  {{==}}
""")

q(f"""
def h.udp6.zero({A6}, +h: U.UdpHeader, +payload: B.Octets) -> {{U.UdpHeader.zero_field(B.Octets.be16_at({B6}, 6n)) == False{{}} : Bool}}:
  Equal.trans(Bool, U.UdpHeader.zero_field(B.Octets.be16_at({B6}, 6n)), U32.is_eq(B.low16(U.UdpHeader.nonzero({CK6U})), 0), False{{}}, h.zf({MU}, U.UdpHeader.nonzero({CK6U}), h.udp_len(h, payload)), h.nz_low(U32.is_eq({CK6U}, 0), K.inet_finish({S0of(PS6, MU)}), S.os.finish_fits({D}, S.os.hD(), {S0of(PS6, MU)}), {{==}}))

def Laws.udp_ipv6_build_verifies(src, dst, h, payload):
  h.go_false(U.UdpHeader.zero_field(B.Octets.be16_at({B6}, 6n)), K.inet_verify(B.Octets.append(I6.ipv6_pseudo(src, dst, U32.from_nat({lnq(B6)}), 17), {B6})), h.udp6.zero(src, dst, h, payload), h.udp6.sum(src, dst, h, payload))

# Satisfiability and the vector

def Laws.inet_sum_sat():
  {{==}}

def Laws.inet_add_vector():
  {{==}}
""")

emit("PROOF_sum.bend", "".join(Q).rstrip() + chr(10))

# ---- PROOF_ipv4.bend: the IPv4 header checksum verifies
R = []
r = R.append
FIELDS = ["ihl", "dscp", "ecn", "tl", "id", "fl", "fo", "ttl", "pr", "ck", "src", "dst"]
def HDR(ckv): return "I4.Ipv4Header{4, ihl, dscp, ecn, tl, id, fl, fo, ttl, pr, %s, src, dst, B.Octets.of_list(options)}" % ckv
def LST(ckv): return "I4.Ipv4Header.build.list(%s)" % HDR(ckv)
def BLD(ckv): return "I4.Ipv4Header.build(%s)" % HDR(ckv)
EMP = "B.Octets.empty()"
CC4 = f"K.inet_checksum(B.Octets.append({EMP}, K.inet_put16({BLD('ck')}, 10n, 0)))"
BC = f"I4.Ipv4Header.build_checksum({HDR('ck')})"
FSIG = ", ".join("+%s: U32" % f for f in FIELDS) + ", +options: List<&2, U32>"
FARGS = ", ".join(FIELDS) + ", options"
def one(n): return "U32{%s}" % n
PATS1 = " ".join(one(f + "_") for f in FIELDS)
def pats_for(deep):
    out = []
    for f in FIELDS:
        if f in deep:
            out.append(pat(f + "_", deep[f]))
        else:
            out.append(one(f + "_"))
    return " ".join(out)
MSIG = ", ".join("%s: U32" % f for f in FIELDS)
MATCH = "match " + " ".join(FIELDS) + ":"
RHSF = f"B.append(B.mask(B.take(10n, {LST('ck')})), B.append(B.mask(B.be16(c)), B.mask(B.drop(Nat.add(10n, 2n), {LST('ck')}))))"
r(f"""# Proof of LAWS_ipv4.bend, written by ref/gen_sum.py. The bytes that
# build_checksum writes are those of the header with its checksum field set
# to the checksum (h4.eq, by computation on the bits of the fields the
# checksum word shares, TTL and protocol, and of the two checksums); so the
# parser reads them back by the round trip (LAWS.bend), the length it reads
# is the bytes' length (h4.len, case by case on the IHL), and the bytes
# verify by inet_fill_verifies (LAWS_sum.bend).
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./netheaders.bend as N
import ./checksum.bend as K
import ./ipv4.bend as I4
import ./LAWS.bend as NL
import ./PROOF.bend as NP
import ./LAWS_sum.bend as SL
import ./PROOF_sum.bend as SP
import ./proof_ones.bend as S
import ./LAWS_ipv4.bend as Laws

# The built bytes, with c written into the checksum field, are the header's
# with checksum c
def h4.eq.list({MSIG}, +options: List<&2, U32>, c: U32) -> {{{RHSF} == B.mask({LST('c')}) : List<&2, U32>}}:
  match {" ".join(FIELDS)} c:
    case {pats_for({"ttl": 8, "pr": 8, "ck": 16})} {pat("c_", 16)}:
      {{==}}

def h4.len.m({MSIG}, +options: List<&2, U32>) -> {{B.len({LST('ck')}) == Nat.add(20n, B.len(B.Octets.to_list(B.Octets.of_list(options)))) : Nat}}:
  {MATCH}
    case {PATS1}:
      {{==}}

def h4.len12.m({MSIG}, +options: List<&2, U32>) -> {{Nat.is_le(Nat.add(10n, 2n), B.len({LST('ck')})) == True{{}} : Bool}}:
  {MATCH}
    case {PATS1}:
      {{==}}

def h4.len10.m({MSIG}, +options: List<&2, U32>) -> {{Nat.is_le(Nat.double(5n), B.len({LST('ck')})) == True{{}} : Bool}}:
  {MATCH}
    case {PATS1}:
      {{==}}

def h4.len10({FSIG}) -> {{Nat.is_le(Nat.double(5n), B.Octets.len({BLD('ck')})) == True{{}} : Bool}}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list({LST('ck')})), B.len({LST('ck')}), BL.octets_len_of_list({LST('ck')})) : {{Nat.is_le(Nat.double(5n), _) == True{{}} : Bool}}
  h4.len10.m({FARGS})

def h4.len12({FSIG}) -> {{Nat.is_le(Nat.add(10n, 2n), B.Octets.len({BLD('ck')})) == True{{}} : Bool}}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list({LST('ck')})), B.len({LST('ck')}), BL.octets_len_of_list({LST('ck')})) : {{Nat.is_le(Nat.add(10n, 2n), _) == True{{}} : Bool}}
  h4.len12.m({FARGS})

def h4.eq({FSIG}, +c: U32) -> {{K.inet_put16({BLD('ck')}, 10n, c) == {BLD('c')} : B.Octets}}:
  %BL.octets_of_to(K.inet_put16({BLD('ck')}, 10n, c)) : {{_ == {BLD('c')} : B.Octets}}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(K.inet_put16(B.Octets.of_list({LST('ck')}), 10n, c)), {RHSF}, S.os.put16_list({LST('ck')}, 10n, c, h4.len12.m({FARGS}))) : {{B.Octets.of_list(_) == {BLD('c')} : B.Octets}}
  %Equal.sym(List<&2, U32>, {RHSF}, B.mask({LST('c')}), h4.eq.list({FARGS}, c)) : {{B.Octets.of_list(_) == {BLD('c')} : B.Octets}}
  %BL.octets_to_of({LST('c')}) : {{B.Octets.of_list(_) == {BLD('c')} : B.Octets}}
  BL.octets_of_list_idempotent({LST('c')})

# the length of the bytes build_checksum writes: 20 bytes and the options
def h4.lenR({FSIG}) -> {{B.Octets.len({BC}) == Nat.add(20n, B.len(options)) : Nat}}:
  %Equal.sym(Nat, B.Octets.len(K.inet_put16({BLD('ck')}, 10n, {CC4})), B.Octets.len({BLD('ck')}), S.os.len_put16({BLD('ck')}, 10n, {CC4}, h4.len12({FARGS}))) : {{_ == Nat.add(20n, B.len(options)) : Nat}}
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list({LST('ck')})), B.len({LST('ck')}), BL.octets_len_of_list({LST('ck')})) : {{_ == Nat.add(20n, B.len(options)) : Nat}}
  %Equal.sym(Nat, B.len({LST('ck')}), Nat.add(20n, B.len(B.Octets.to_list(B.Octets.of_list(options)))), h4.len.m({FARGS})) : {{_ == Nat.add(20n, B.len(options)) : Nat}}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(options)), B.mask(options), BL.octets_to_of(options)) : {{Nat.add(20n, B.len(_)) == Nat.add(20n, B.len(options)) : Nat}}
  %Equal.sym(Nat, B.len(B.mask(options)), B.len(options), S.os.len_mask(options)) : {{Nat.add(20n, _) == Nat.add(20n, B.len(options)) : Nat}}
  {{==}}
""")
# the length the parser reads, case by case on the IHL
LSIG = "ihl: U32, +e1: {U32.is_ge(N.NetField.low(4n, ihl), 5) == True{} : Bool}, " + ", ".join("+%s: U32" % f for f in FIELDS[1:]) + ", +options: List<&2, U32>, +c: U32, +e2: {B.len(options) == Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl))), 20n) : Nat}"
GOAL = f"{{I4.Ipv4Header.length(I4.Ipv4Header.norm({HDR('c')})) == Nat.add(20n, B.len(options)) : Nat}}"
def bits4(v, tail):
    s = "".join("WCon{%s, " % ("True{}" if v >> i & 1 else "False{}") for i in range(4))
    return "U32{" + s + tail + "}" * 4 + "}"
cases = []
for val in range(16):
    if val < 5:
        body = "      Empty.absurd(%s, S.os.ft(e1))" % GOAL
    else:
        body = "      %%Equal.sym(Nat, B.len(options), Nat.sub(Nat.mul(4n, U32.to_nat(N.NetField.low(4n, ihl))), 20n), e2) : {I4.Ipv4Header.length(I4.Ipv4Header.norm(%s)) == Nat.add(20n, _) : Nat}\n      {==}" % HDR("c")
    cases.append("    case %s:\n%s" % (bits4(val, "ih"), body))
r(f"""
def h4.len({LSIG}) -> {GOAL}:
  match ihl:
{chr(10).join(cases)}

def Laws.ipv4_build_verifies(ihl, e1, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, options, e2):
  %Equal.sym(B.Octets, K.inet_put16({BLD('ck')}, 10n, {CC4}), {BLD(CC4)}, h4.eq({FARGS}, {CC4})) : {{I4.Ipv4Header.verify.go(I4.Ipv4Header.parse(_), {BC}) == True{{}} : Bool}}
  %BL.octets_append_empty_r({BLD(CC4)}) : {{I4.Ipv4Header.verify.go(I4.Ipv4Header.parse(_), {BC}) == True{{}} : Bool}}
  %Equal.sym(Result<&2, &2, N.NetError, I4.Ipv4Header>, I4.Ipv4Header.parse(B.Octets.append({BLD(CC4)}, {EMP})), Done{{I4.Ipv4Header.norm({HDR(CC4)})}}, NL.ipv4_round_trip(ihl, e1, dscp, ecn, tl, id, fl, fo, ttl, pr, {CC4}, src, dst, options, e2, {EMP})) : {{I4.Ipv4Header.verify.go(_, {BC}) == True{{}} : Bool}}
  %Equal.sym(Nat, I4.Ipv4Header.length(I4.Ipv4Header.norm({HDR(CC4)})), B.Octets.len({BC}), Equal.trans(Nat, I4.Ipv4Header.length(I4.Ipv4Header.norm({HDR(CC4)})), Nat.add(20n, B.len(options)), B.Octets.len({BC}), h4.len(ihl, e1, dscp, ecn, tl, id, fl, fo, ttl, pr, ck, src, dst, options, {CC4}, e2), Equal.sym(Nat, B.Octets.len({BC}), Nat.add(20n, B.len(options)), h4.lenR({FARGS})))) : {{K.inet_verify(B.Octets.take(_, {BC})) == True{{}} : Bool}}
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len({BC}), {BC}), {BC}, BL.octets_take_len({BC})) : {{K.inet_verify(_) == True{{}} : Bool}}
  %BL.octets_append_empty_l({BC}) : {{K.inet_verify(_) == True{{}} : Bool}}
  SL.inet_fill_verifies({EMP}, {BLD('ck')}, 5n, {{==}}, h4.len10({FARGS}))

def Laws.ipv4_build_verifies_sat():
  {{==}}
""")
emit("PROOF_ipv4.bend", "".join(R).rstrip() + chr(10))

if "--check" in sys.argv[1:]:
    stale = [p for p, t in OUTS.items() if open(p, encoding="utf-8").read() != t]
    if stale:
        print("differ from what ref/gen_sum.py generates: " + " ".join(stale))
        sys.exit(1)
    print("proof_ones.bend, PROOF_sum.bend and PROOF_ipv4.bend are up to date")
else:
    for p, t in OUTS.items():
        with open(p, "w", encoding="utf-8", newline=chr(10)) as f:
            f.write(t)
