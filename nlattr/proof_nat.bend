# Proof helpers for bend-osdev-nlattr: Nat arithmetic and order, and Base's
# Nat.divmod (a = q * b + r with r < b), by induction on Base's unary Nat.
import Base

def nn.bt(+b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def nn.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : nn.bt(_)
  Unit{}

def nn.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : nn.bt(_)
  Unit{}

def nn.and_l(+a: Bool, -b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, nn.ft(e))

def nn.and_r(+a: Bool, -b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, nn.ft(e))

def nn.and_i(+a: Bool, -b: Bool, +ea: {a == True{} : Bool}, +eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, nn.ft(ea))

# Addition

def nn.add_zero(+m: Nat) -> {Nat.add(m, 0n) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      %nn.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def nn.add_succ(+x: Nat, -y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %nn.add_succ(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

def nn.add_assoc(+a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %nn.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def nn.add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, nn.add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), nn.add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %nn.add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# a + (b + c) = b + (a + c)
def nn.add_lc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  %nn.add_assoc(a, b, c) : {_ == Nat.add(b, Nat.add(a, c)) : Nat}
  %nn.add_assoc(b, a, c) : {Nat.add(Nat.add(a, b), c) == _ : Nat}
  %nn.add_comm(a, b) : {Nat.add(Nat.add(a, b), c) == Nat.add(_, c) : Nat}
  {==}

def nn.sub_zero(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nn.sub_add_l(+a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), a) == b : Nat}:
  match a:
    case 0n:
      nn.sub_zero(b)
    case 1n+p:
      nn.sub_add_l(p, b)

# Order

def nn.le_zero(+x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nn.le_refl(+x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      nn.le_refl(p)

def nn.le_trans(+a: Nat, +b: Nat, +c: Nat, +e: {Nat.is_le(a, b) == True{} : Bool}, +f: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      nn.le_zero(c)
    case 1n+ap 0n _:
      Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, nn.ft(e))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, nn.ft(f))
    case 1n+ap 1n+bp 1n+cp:
      nn.le_trans(ap, bp, cp, e, f)

def nn.le_succ(+x: Nat) -> {Nat.is_le(x, 1n+x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      nn.le_succ(p)

# x <= x + y
def nn.le_add(+x: Nat, +y: Nat) -> {Nat.is_le(x, Nat.add(x, y)) == True{} : Bool}:
  match x:
    case 0n:
      nn.le_zero(y)
    case 1n+p:
      nn.le_add(p, y)

# y <= x + y
def nn.le_add_l(+x: Nat, +y: Nat) -> {Nat.is_le(y, Nat.add(x, y)) == True{} : Bool}:
  match x:
    case 0n:
      nn.le_refl(y)
    case 1n+p:
      nn.le_trans(y, Nat.add(p, y), 1n+Nat.add(p, y), nn.le_add_l(p, y), nn.le_succ(Nat.add(p, y)))

def nn.cancel_le(+k: Nat, -a: Nat, -b: Nat) -> {Nat.is_le(Nat.add(k, a), Nat.add(k, b)) == Nat.is_le(a, b) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      nn.cancel_le(p, a, b)

def nn.lt0(+m: Nat) -> {Nat.is_lt(m, 0n) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nn.lt_nle(+a: Nat, +b: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_le(0n, a) == False{} : Bool}, nn.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, nn.lt0(a)), e)))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      nn.lt_nle(ap, bp, e)

def nn.lt_le_trans(+a: Nat, +b: Nat, +c: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}, +f: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ 0n _:
      Empty.absurd({Nat.is_lt(a, c) == True{} : Bool}, nn.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, nn.lt0(a)), e)))
    case 0n 1n+bp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, nn.ft(f))
    case 0n 1n+bp 1n+cp:
      {==}
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, nn.ft(f))
    case 1n+ap 1n+bp 1n+cp:
      nn.lt_le_trans(ap, bp, cp, e, f)

def nn.le_lt_succ(+x: Nat, +k: Nat, +h: {Nat.is_le(x, k) == True{} : Bool}) -> {Nat.is_lt(x, 1n+k) == True{} : Bool}:
  match x k:
    case 0n _:
      {==}
    case 1n+xp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 1n) == True{} : Bool}, nn.ft(h))
    case 1n+xp 1n+kp:
      nn.le_lt_succ(xp, kp, h)

# Division: Base's Nat.divmod.go counts n down, m down to the next step of
# the quotient d, and the remainder r up, with m + r the divisor less one

def nn.dm(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat, +h: {Nat.add(m, r) == bp : Nat}) -> {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r))) == Nat.add(n, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          +ih = nn.dm(np, r, 1n+d, 0n, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, nn.add_zero(r), h))
          %Equal.sym(Nat, Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n))), Nat.add(np, Nat.add(Nat.mul(1n+d, 1n+bp), 0n)), ih) : {_ == Nat.add(1n+np, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}
          %Equal.sym(Nat, Nat.add(Nat.add(1n+bp, Nat.mul(d, 1n+bp)), 0n), Nat.add(1n+bp, Nat.mul(d, 1n+bp)), nn.add_zero(Nat.add(1n+bp, Nat.mul(d, 1n+bp)))) : {Nat.add(np, _) == Nat.add(1n+np, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}
          %h : {Nat.add(np, Nat.add(1n+_, Nat.mul(d, 1n+bp))) == Nat.add(1n+np, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}
          %nn.add_comm(r, Nat.mul(d, 1n+bp)) : {Nat.add(np, Nat.add(1n+r, Nat.mul(d, 1n+bp))) == 1n+Nat.add(np, _) : Nat}
          nn.add_succ(np, Nat.add(r, Nat.mul(d, 1n+bp)))
        case 1n+mp:
          +ih = nn.dm(np, mp, d, 1n+r, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, nn.add_succ(mp, r), h))
          %Equal.sym(Nat, Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r))), Nat.add(np, Nat.add(Nat.mul(d, 1n+bp), 1n+r)), ih) : {_ == Nat.add(1n+np, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}
          %Equal.sym(Nat, Nat.add(Nat.mul(d, 1n+bp), 1n+r), 1n+Nat.add(Nat.mul(d, 1n+bp), r), nn.add_succ(Nat.mul(d, 1n+bp), r)) : {Nat.add(np, _) == Nat.add(1n+np, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}
          nn.add_succ(np, Nat.add(Nat.mul(d, 1n+bp), r))

def nn.db(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat, +h: {Nat.add(m, r) == bp : Nat}) -> {Nat.is_le(Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)), bp) == True{} : Bool}:
  match n:
    case 0n:
      %h : {Nat.is_le(r, _) == True{} : Bool}
      nn.le_add_l(m, r)
    case 1n+np:
      match m:
        case 0n:
          nn.db(np, r, 1n+d, 0n, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, nn.add_zero(r), h))
        case 1n+mp:
          nn.db(np, mp, d, 1n+r, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, nn.add_succ(mp, r), h))

# n = (n / 256) * 256 + n % 256, and n % 256 < 256
def nn.recon(+n: Nat) -> {Nat.add(Nat.mul(Nat.div(n, 256n), 256n), Nat.mod(n, 256n)) == n : Nat}:
  Equal.trans(Nat, Nat.add(Nat.mul(Nat.div(n, 256n), 256n), Nat.mod(n, 256n)), Nat.add(n, Nat.add(Nat.mul(0n, 256n), 0n)), n, nn.dm(n, 255n, 0n, 0n, 255n, {==}), nn.add_zero(n))

def nn.mod_lt(+n: Nat) -> {Nat.is_lt(Nat.mod(n, 256n), 256n) == True{} : Bool}:
  nn.le_lt_succ(Nat.mod(n, 256n), 255n, nn.db(n, 255n, 0n, 0n, 255n, {==}))
