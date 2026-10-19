# Proof helpers for bend-osdev-oid: Nat arithmetic and order, and Base's
# Nat.divmod (a = q * b + r with r < b, and q < a when a >= b >= 2), by
# induction on Base's unary Nat.
import Base

def on.bt(+b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def on.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : on.bt(_)
  Unit{}

def on.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : on.bt(_)
  Unit{}

def on.and_l(+a: Bool, -b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, on.ft(e))

def on.and_r(+a: Bool, -b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, on.ft(e))

def on.and_i(+a: Bool, -b: Bool, +ea: {a == True{} : Bool}, +eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, on.ft(ea))

def on.not_t(+a: Bool, +e: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, on.ft(e))
    case False{}:
      {==}

# Addition

def on.add_zero(+m: Nat) -> {Nat.add(m, 0n) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      %on.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def on.add_succ(+x: Nat, -y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %on.add_succ(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

def on.add_assoc(+a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %on.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def on.add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, on.add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), on.add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %on.add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def on.sub_zero(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def on.sub_add_l(+a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), a) == b : Nat}:
  match a:
    case 0n:
      on.sub_zero(b)
    case 1n+p:
      on.sub_add_l(p, b)

# Order

def on.le_zero(+x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def on.le_refl(+x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      on.le_refl(p)

def on.le_trans(+a: Nat, +b: Nat, +c: Nat, +e: {Nat.is_le(a, b) == True{} : Bool}, +f: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      on.le_zero(c)
    case 1n+ap 0n _:
      Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, on.ft(e))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, on.ft(f))
    case 1n+ap 1n+bp 1n+cp:
      on.le_trans(ap, bp, cp, e, f)

def on.le_succ(+x: Nat) -> {Nat.is_le(x, 1n+x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      on.le_succ(p)

# x <= x + y
def on.le_add(+x: Nat, +y: Nat) -> {Nat.is_le(x, Nat.add(x, y)) == True{} : Bool}:
  match x:
    case 0n:
      on.le_zero(y)
    case 1n+p:
      on.le_add(p, y)

# y <= x + y
def on.le_add_l(+x: Nat, +y: Nat) -> {Nat.is_le(y, Nat.add(x, y)) == True{} : Bool}:
  match x:
    case 0n:
      on.le_refl(y)
    case 1n+p:
      on.le_trans(y, Nat.add(p, y), 1n+Nat.add(p, y), on.le_add_l(p, y), on.le_succ(Nat.add(p, y)))

def on.cancel_le(+k: Nat, -a: Nat, -b: Nat) -> {Nat.is_le(Nat.add(k, a), Nat.add(k, b)) == Nat.is_le(a, b) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      on.cancel_le(p, a, b)

# a <= b implies k + a <= k + b
def on.le_add_mono(+k: Nat, +a: Nat, +b: Nat, +e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(k, a), Nat.add(k, b)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(Nat.add(k, a), Nat.add(k, b)), Nat.is_le(a, b), True{}, on.cancel_le(k, a, b), e)

# a <= b implies a + k <= b + k
def on.le_add_mono_r(+k: Nat, +a: Nat, +b: Nat, +e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, k), Nat.add(b, k)) == True{} : Bool}:
  %on.add_comm(k, a) : {Nat.is_le(_, Nat.add(b, k)) == True{} : Bool}
  %on.add_comm(k, b) : {Nat.is_le(Nat.add(k, a), _) == True{} : Bool}
  on.le_add_mono(k, a, b, e)

# a <= c and b <= d imply a + b <= c + d
def on.le_add2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: {Nat.is_le(a, c) == True{} : Bool}, +f: {Nat.is_le(b, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), Nat.add(c, d)) == True{} : Bool}:
  on.le_trans(Nat.add(a, b), Nat.add(c, b), Nat.add(c, d), on.le_add_mono_r(b, a, c, e), on.le_add_mono(c, b, d, f))

def on.lt0(+m: Nat) -> {Nat.is_lt(m, 0n) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

def on.lt_nle(+a: Nat, +b: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_le(0n, a) == False{} : Bool}, on.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, on.lt0(a)), e)))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      on.lt_nle(ap, bp, e)

def on.lt_le_trans(+a: Nat, +b: Nat, +c: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}, +f: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ 0n _:
      Empty.absurd({Nat.is_lt(a, c) == True{} : Bool}, on.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, on.lt0(a)), e)))
    case 0n 1n+bp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, on.ft(f))
    case 0n 1n+bp 1n+cp:
      {==}
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, on.ft(f))
    case 1n+ap 1n+bp 1n+cp:
      on.lt_le_trans(ap, bp, cp, e, f)

def on.le_lt_succ(+x: Nat, +k: Nat, +h: {Nat.is_le(x, k) == True{} : Bool}) -> {Nat.is_lt(x, 1n+k) == True{} : Bool}:
  match x k:
    case 0n _:
      {==}
    case 1n+xp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 1n) == True{} : Bool}, on.ft(h))
    case 1n+xp 1n+kp:
      on.le_lt_succ(xp, kp, h)

# x < 1 + k implies x <= k
def on.lt_succ_le(+x: Nat, +k: Nat, +h: {Nat.is_lt(x, 1n+k) == True{} : Bool}) -> {Nat.is_le(x, k) == True{} : Bool}:
  match x k:
    case 0n _:
      on.le_zero(k)
    case 1n+xp 0n:
      Empty.absurd({Nat.is_le(1n+xp, 0n) == True{} : Bool}, on.ft(Equal.trans(Bool, False{}, Nat.is_lt(xp, 0n), True{}, Equal.sym(Bool, Nat.is_lt(xp, 0n), False{}, on.lt0(xp)), h)))
    case 1n+xp 1n+kp:
      on.lt_succ_le(xp, kp, h)

# x < k implies x <= k
def on.lt_le(+x: Nat, +k: Nat, +h: {Nat.is_lt(x, k) == True{} : Bool}) -> {Nat.is_le(x, k) == True{} : Bool}:
  match k:
    case 0n:
      Empty.absurd({Nat.is_le(x, 0n) == True{} : Bool}, on.ft(Equal.trans(Bool, False{}, Nat.is_lt(x, 0n), True{}, Equal.sym(Bool, Nat.is_lt(x, 0n), False{}, on.lt0(x)), h)))
    case 1n+kp:
      on.le_trans(x, kp, 1n+kp, on.lt_succ_le(x, kp, h), on.le_succ(kp))

# not (b <= a) implies a < b
def on.nle_lt(+a: Nat, +b: Nat, +e: {Nat.is_le(b, a) == False{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, on.tf(Equal.trans(Bool, True{}, Nat.is_le(0n, a), False{}, Equal.sym(Bool, Nat.is_le(0n, a), True{}, on.le_zero(a)), e)))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      on.nle_lt(ap, bp, e)

# Equality

def on.eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      on.eq_refl(p)

def on.eq_sound(+a: Nat, +b: Nat, +e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, on.ft(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, on.ft(e))
    case 1n+ap 1n+bp:
      %on.eq_sound(ap, bp, e) : {1n+ap == 1n+_ : Nat}
      {==}

# a < b implies a != b
def on.lt_ne(+a: Nat, +b: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_eq(a, 0n) == False{} : Bool}, on.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, on.lt0(a)), e)))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      on.lt_ne(ap, bp, e)

# Division: Base's Nat.divmod.go counts n down, m down to the next step of
# the quotient d, and the remainder r up, with m + r the divisor less one

def on.dm(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat, +h: {Nat.add(m, r) == bp : Nat}) -> {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r))) == Nat.add(n, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          +ih = on.dm(np, r, 1n+d, 0n, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, on.add_zero(r), h))
          %Equal.sym(Nat, Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n))), Nat.add(np, Nat.add(Nat.mul(1n+d, 1n+bp), 0n)), ih) : {_ == Nat.add(1n+np, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}
          %Equal.sym(Nat, Nat.add(Nat.add(1n+bp, Nat.mul(d, 1n+bp)), 0n), Nat.add(1n+bp, Nat.mul(d, 1n+bp)), on.add_zero(Nat.add(1n+bp, Nat.mul(d, 1n+bp)))) : {Nat.add(np, _) == Nat.add(1n+np, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}
          %h : {Nat.add(np, Nat.add(1n+_, Nat.mul(d, 1n+bp))) == Nat.add(1n+np, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}
          %on.add_comm(r, Nat.mul(d, 1n+bp)) : {Nat.add(np, Nat.add(1n+r, Nat.mul(d, 1n+bp))) == 1n+Nat.add(np, _) : Nat}
          on.add_succ(np, Nat.add(r, Nat.mul(d, 1n+bp)))
        case 1n+mp:
          +ih = on.dm(np, mp, d, 1n+r, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, on.add_succ(mp, r), h))
          %Equal.sym(Nat, Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r))), Nat.add(np, Nat.add(Nat.mul(d, 1n+bp), 1n+r)), ih) : {_ == Nat.add(1n+np, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}
          %Equal.sym(Nat, Nat.add(Nat.mul(d, 1n+bp), 1n+r), 1n+Nat.add(Nat.mul(d, 1n+bp), r), on.add_succ(Nat.mul(d, 1n+bp), r)) : {Nat.add(np, _) == Nat.add(1n+np, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}
          on.add_succ(np, Nat.add(Nat.mul(d, 1n+bp), r))

def on.db(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat, +h: {Nat.add(m, r) == bp : Nat}) -> {Nat.is_le(Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)), bp) == True{} : Bool}:
  match n:
    case 0n:
      %h : {Nat.is_le(r, _) == True{} : Bool}
      on.le_add_l(m, r)
    case 1n+np:
      match m:
        case 0n:
          on.db(np, r, 1n+d, 0n, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, on.add_zero(r), h))
        case 1n+mp:
          on.db(np, mp, d, 1n+r, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, on.add_succ(mp, r), h))

# n = (n / b) * b + n % b, for b = 1 + bp
def on.recon(+n: Nat, +bp: Nat) -> {Nat.add(Nat.mul(Nat.div(n, 1n+bp), 1n+bp), Nat.mod(n, 1n+bp)) == n : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.div(n, 1n+bp), 1n+bp), Nat.mod(n, 1n+bp)), Nat.add(n, Nat.add(Nat.mul(0n, 1n+bp), 0n)), n, on.dm(n, bp, 0n, 0n, bp, on.add_zero(bp)), on.add_zero(n))

# n % b < b
def on.mod_lt(+n: Nat, +bp: Nat) -> {Nat.is_lt(Nat.mod(n, 1n+bp), 1n+bp) == True{} : Bool}:
  on.le_lt_succ(Nat.mod(n, 1n+bp), bp, on.db(n, bp, 0n, 0n, bp, on.add_zero(bp)))

# q <= q * b, for b >= 1
def on.le_mul(+q: Nat, +bp: Nat) -> {Nat.is_le(q, Nat.mul(q, 1n+bp)) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      on.le_trans(p, Nat.mul(p, 1n+bp), Nat.add(bp, Nat.mul(p, 1n+bp)), on.le_mul(p, bp), on.le_add_l(bp, Nat.mul(p, 1n+bp)))

# n >= b >= 2 implies n / b < n
def on.div_lt.q(+q: Nat, +r: Nat, +bp: Nat, +n: Nat, +hr: {Nat.add(Nat.mul(q, 2n+bp), r) == n : Nat}, +hn: {Nat.is_le(2n+bp, n) == True{} : Bool}) -> {Nat.is_lt(q, n) == True{} : Bool}:
  match q:
    case 0n:
      %hr : {Nat.is_lt(0n, _) == True{} : Bool}
      on.lt_le_trans(0n, 2n+bp, r, {==}, Equal.trans(Bool, Nat.is_le(2n+bp, r), Nat.is_le(2n+bp, n), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(2n+bp, z), r, n, hr), hn))
    case 1n+p:
      %hr : {Nat.is_lt(1n+p, _) == True{} : Bool}
      +m = Nat.mul(p, 2n+bp)
      +x = Nat.add(bp, m)
      on.le_lt_succ(p, Nat.add(x, r), on.le_trans(p, x, Nat.add(x, r), on.le_trans(p, m, x, on.le_mul(p, 1n+bp), on.le_add_l(bp, m)), on.le_add(x, r)))

def on.div_lt(+n: Nat, +bp: Nat, +hn: {Nat.is_le(2n+bp, n) == True{} : Bool}) -> {Nat.is_lt(Nat.div(n, 2n+bp), n) == True{} : Bool}:
  on.div_lt.q(Nat.div(n, 2n+bp), Nat.mod(n, 2n+bp), bp, n, on.recon(n, 1n+bp), hn)
