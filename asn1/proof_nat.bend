# Proof helpers for bend-osdev-asn1: Nat arithmetic and order, and Base's
# Nat.divmod (a = q * b + r with r < b, and q < a when a >= b >= 2), by
# induction on Base's unary Nat.
import Base
import ../u32/LAWS.bend as UL
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF.bend as UP
import ../u32/PROOF_order.bend as UOP
import ../u32/LAWS_div.bend as UD
import ../u32/PROOF_div.bend as UDP

def an.bt(+b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def an.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : an.bt(_)
  Unit{}

def an.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : an.bt(_)
  Unit{}

def an.and_l(+a: Bool, -b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, an.ft(e))

def an.and_r(+a: Bool, -b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, an.ft(e))

def an.and_i(+a: Bool, -b: Bool, +ea: {a == True{} : Bool}, +eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, an.ft(ea))

def an.not_t(+a: Bool, +e: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, an.ft(e))
    case False{}:
      {==}

# Addition

def an.sub_zero(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def an.sub_add_l(+a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), a) == b : Nat}:
  match a:
    case 0n:
      an.sub_zero(b)
    case 1n+p:
      an.sub_add_l(p, b)

# Order

def an.le_zero(+x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def an.le_succ(+x: Nat) -> {Nat.is_le(x, 1n+x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      an.le_succ(p)

def an.cancel_le(+k: Nat, -a: Nat, -b: Nat) -> {Nat.is_le(Nat.add(k, a), Nat.add(k, b)) == Nat.is_le(a, b) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      an.cancel_le(p, a, b)

# a <= b implies k + a <= k + b
def an.le_add_mono(+k: Nat, +a: Nat, +b: Nat, +e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(k, a), Nat.add(k, b)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(Nat.add(k, a), Nat.add(k, b)), Nat.is_le(a, b), True{}, an.cancel_le(k, a, b), e)

# a <= b implies a + k <= b + k
def an.le_add_mono_r(+k: Nat, +a: Nat, +b: Nat, +e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, k), Nat.add(b, k)) == True{} : Bool}:
  %UL.nat_add_comm(k, a) : {Nat.is_le(_, Nat.add(b, k)) == True{} : Bool}
  %UL.nat_add_comm(k, b) : {Nat.is_le(Nat.add(k, a), _) == True{} : Bool}
  an.le_add_mono(k, a, b, e)

# a <= c and b <= d imply a + b <= c + d
def an.le_add2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: {Nat.is_le(a, c) == True{} : Bool}, +f: {Nat.is_le(b, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), Nat.add(c, d)) == True{} : Bool}:
  UO.nat_le_trans(Nat.add(a, b), Nat.add(c, b), Nat.add(c, d), an.le_add_mono_r(b, a, c, e), an.le_add_mono(c, b, d, f))

def an.lt0(+m: Nat) -> {Nat.is_lt(m, 0n) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

def an.lt_nle(+a: Nat, +b: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_le(0n, a) == False{} : Bool}, an.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, an.lt0(a)), e)))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      an.lt_nle(ap, bp, e)

def an.le_lt_succ(+x: Nat, +k: Nat, +h: {Nat.is_le(x, k) == True{} : Bool}) -> {Nat.is_lt(x, 1n+k) == True{} : Bool}:
  match x k:
    case 0n _:
      {==}
    case 1n+xp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 1n) == True{} : Bool}, an.ft(h))
    case 1n+xp 1n+kp:
      an.le_lt_succ(xp, kp, h)

# x < 1 + k implies x <= k
def an.lt_succ_le(+x: Nat, +k: Nat, +h: {Nat.is_lt(x, 1n+k) == True{} : Bool}) -> {Nat.is_le(x, k) == True{} : Bool}:
  match x k:
    case 0n _:
      an.le_zero(k)
    case 1n+xp 0n:
      Empty.absurd({Nat.is_le(1n+xp, 0n) == True{} : Bool}, an.ft(Equal.trans(Bool, False{}, Nat.is_lt(xp, 0n), True{}, Equal.sym(Bool, Nat.is_lt(xp, 0n), False{}, an.lt0(xp)), h)))
    case 1n+xp 1n+kp:
      an.lt_succ_le(xp, kp, h)

# x < k implies x <= k
def an.lt_le(+x: Nat, +k: Nat, +h: {Nat.is_lt(x, k) == True{} : Bool}) -> {Nat.is_le(x, k) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({Nat.is_le(x, 0n) == True{} : Bool}, an.ft(Equal.trans(Bool, False{}, Nat.is_lt(x, 0n), True{}, Equal.sym(Bool, Nat.is_lt(x, 0n), False{}, an.lt0(x)), h)))
    case 1n+kp:
      UO.nat_le_trans(x, kp, 1n+kp, an.lt_succ_le(x, kp, h), an.le_succ(kp))

# not (b <= a) implies a < b
def an.nle_lt(+a: Nat, +b: Nat, +e: {Nat.is_le(b, a) == False{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, an.tf(Equal.trans(Bool, True{}, Nat.is_le(0n, a), False{}, Equal.sym(Bool, Nat.is_le(0n, a), True{}, an.le_zero(a)), e)))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      an.nle_lt(ap, bp, e)

# Equality

def an.eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      an.eq_refl(p)

def an.eq_sound(+a: Nat, +b: Nat, +e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, an.ft(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, an.ft(e))
    case 1n+ap 1n+bp:
      %an.eq_sound(ap, bp, e) : {1n+ap == 1n+_ : Nat}
      {==}

# a < b implies a != b
def an.lt_ne(+a: Nat, +b: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_eq(a, 0n) == False{} : Bool}, an.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, an.lt0(a)), e)))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      an.lt_ne(ap, bp, e)

# Division: Base's Nat.divmod.go counts n down, m down to the next step of
# the quotient d, and the remainder r up, with m + r the divisor less one

# q <= q * b, for b >= 1
def an.le_mul(+q: Nat, +bp: Nat) -> {Nat.is_le(q, Nat.mul(q, 1n+bp)) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      UO.nat_le_trans(p, Nat.mul(p, 1n+bp), Nat.add(bp, Nat.mul(p, 1n+bp)), an.le_mul(p, bp), UL.nat_le_add(Nat.mul(p, 1n+bp), bp))

# n >= b >= 2 implies n / b < n
def an.div_lt.q(+q: Nat, +r: Nat, +bp: Nat, +n: Nat, +hr: {Nat.add(Nat.mul(q, 2n+bp), r) == n : Nat}, +hn: {Nat.is_le(2n+bp, n) == True{} : Bool}) -> {Nat.is_lt(q, n) == True{} : Bool}:
  match q:
    case 0n:
      %hr : {Nat.is_lt(0n, _) == True{} : Bool}
      UO.nat_lt_le_trans(0n, 2n+bp, r, {==}, Equal.trans(Bool, Nat.is_le(2n+bp, r), Nat.is_le(2n+bp, n), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(2n+bp, z), r, n, hr), hn))
    case 1n+p:
      %hr : {Nat.is_lt(1n+p, _) == True{} : Bool}
      +m = Nat.mul(p, 2n+bp)
      +x = Nat.add(bp, m)
      an.le_lt_succ(p, Nat.add(x, r), UO.nat_le_trans(p, x, Nat.add(x, r), UO.nat_le_trans(p, m, x, an.le_mul(p, 1n+bp), UL.nat_le_add(m, bp)), UO.nat_le_add_r(x, r)))

def an.div_lt(+n: Nat, +bp: Nat, +hn: {Nat.is_le(2n+bp, n) == True{} : Bool}) -> {Nat.is_lt(Nat.div(n, 2n+bp), n) == True{} : Bool}:
  an.div_lt.q(Nat.div(n, 2n+bp), Nat.mod(n, 2n+bp), bp, n, UD.nat_div_mod(n, 1n+bp), hn)
