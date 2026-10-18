# Proof helpers for bend-osdev-genalloc: Nat arithmetic and order, by
# induction on Base's unary Nat.
import Base

# Contradictions and Bool

def nl.bt(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def nl.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : nl.bt(_)
  Unit{}

def nl.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : nl.bt(_)
  Unit{}

def nl.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, nl.ft(e))

def nl.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, nl.ft(e))

def nl.and_i(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, nl.ft(ea))

# a and b false: one of them is false
def nl.and_f(a: Bool, -b: Bool, e: {Bool.and(a, b) == False{} : Bool}, ea: {a == True{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == False{} : Bool}, nl.ft(ea))

# Addition

def nl.add_zero(m: Nat) -> {Nat.add(m, 0n) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      %nl.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def nl.add_succ(x: Nat, -y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %nl.add_succ(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

def nl.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %nl.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def nl.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, nl.add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), nl.add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %nl.add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# (a + b) + (c + d) = (a + c) + (b + d)
def nl.swap4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), nl.add_assoc(a, b, Nat.add(c, d))) : {_ == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), nl.add_assoc(a, c, Nat.add(b, d))) : {Nat.add(a, Nat.add(b, Nat.add(c, d))) == _ : Nat}
  %nl.add_assoc(b, c, d) : {Nat.add(a, _) == Nat.add(a, Nat.add(c, Nat.add(b, d))) : Nat}
  %nl.add_assoc(c, b, d) : {Nat.add(a, Nat.add(Nat.add(b, c), d)) == Nat.add(a, _) : Nat}
  %nl.add_comm(b, c) : {Nat.add(a, Nat.add(Nat.add(b, c), d)) == Nat.add(a, Nat.add(_, d)) : Nat}
  {==}

# Multiplication

def nl.mul_add(a: Nat, -b: Nat, +g: Nat) -> {Nat.mul(Nat.add(a, b), g) == Nat.add(Nat.mul(a, g), Nat.mul(b, g)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(Nat.add(p, b), g), Nat.add(Nat.mul(p, g), Nat.mul(b, g)), nl.mul_add(p, b, g)) : {Nat.add(g, _) == Nat.add(Nat.add(g, Nat.mul(p, g)), Nat.mul(b, g)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(g, Nat.mul(p, g)), Nat.mul(b, g)), Nat.add(g, Nat.add(Nat.mul(p, g), Nat.mul(b, g))), nl.add_assoc(g, Nat.mul(p, g), Nat.mul(b, g)))

# Order

def nl.le_zero(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nl.le_refl(x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      nl.le_refl(p)

def nl.eq_refl(x: Nat) -> {Nat.is_eq(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      nl.eq_refl(p)

def nl.lt0(m: Nat) -> {Nat.is_lt(m, 0n) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nl.le_trans(a: Nat, b: Nat, c: Nat, e: {Nat.is_le(a, b) == True{} : Bool}, f: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      nl.le_zero(c)
    case 1n+ap 0n _:
      Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, nl.ft(e))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, nl.ft(f))
    case 1n+ap 1n+bp 1n+cp:
      nl.le_trans(ap, bp, cp, e, f)

def nl.le_succ(x: Nat) -> {Nat.is_le(x, 1n+x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      nl.le_succ(p)

def nl.lt_le(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_le(a, 0n) == True{} : Bool}, nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, nl.lt0(a)), e)))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      nl.lt_le(ap, bp, e)

def nl.lt_le_trans(a: Nat, b: Nat, c: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}, f: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ 0n _:
      Empty.absurd({Nat.is_lt(a, c) == True{} : Bool}, nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, nl.lt0(a)), e)))
    case 0n 1n+bp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, nl.ft(f))
    case 0n 1n+bp 1n+cp:
      {==}
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, nl.ft(f))
    case 1n+ap 1n+bp 1n+cp:
      nl.lt_le_trans(ap, bp, cp, e, f)

def nl.le_lt_trans(a: Nat, b: Nat, c: Nat, e: {Nat.is_le(a, b) == True{} : Bool}, f: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ _ 0n:
      Empty.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(b, 0n), True{}, Equal.sym(Bool, Nat.is_lt(b, 0n), False{}, nl.lt0(b)), f)))
    case 0n _ 1n+cp:
      {==}
    case 1n+ap 0n 1n+cp:
      Empty.absurd({Nat.is_lt(1n+ap, 1n+cp) == True{} : Bool}, nl.ft(e))
    case 1n+ap 1n+bp 1n+cp:
      nl.le_lt_trans(ap, bp, cp, e, f)

# x <= x + y
def nl.le_add(x: Nat, +y: Nat) -> {Nat.is_le(x, Nat.add(x, y)) == True{} : Bool}:
  match x:
    case 0n:
      nl.le_zero(y)
    case 1n+p:
      nl.le_add(p, y)

# x < x + y when 0 < y
def nl.lt_add(x: Nat, +y: Nat, h: {Nat.is_lt(0n, y) == True{} : Bool}) -> {Nat.is_lt(x, Nat.add(x, y)) == True{} : Bool}:
  match x:
    case 0n:
      h
    case 1n+p:
      nl.lt_add(p, y, h)

# x + a < x + b when a < b
def nl.lt_add_l(x: Nat, -a: Nat, -b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(Nat.add(x, a), Nat.add(x, b)) == True{} : Bool}:
  match x:
    case 0n:
      h
    case 1n+p:
      nl.lt_add_l(p, a, b, h)

# a < b and 0 < g: a * g < b * g
def nl.lt_mul(+a: Nat, +b: Nat, +g: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}, hg: {Nat.is_lt(0n, g) == True{} : Bool}) -> {Nat.is_lt(Nat.mul(a, g), Nat.mul(b, g)) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_lt(Nat.mul(a, g), 0n) == True{} : Bool}, nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, nl.lt0(a)), h)))
    case 0n 1n+bp:
      nl.lt_le_trans(0n, g, Nat.add(g, Nat.mul(bp, g)), hg, nl.le_add(g, Nat.mul(bp, g)))
    case 1n+ap 1n+bp:
      nl.lt_add_l(g, Nat.mul(ap, g), Nat.mul(bp, g), nl.lt_mul(ap, bp, g, h, hg))

def nl.lt_ne(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_eq(a, 0n) == False{} : Bool}, nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, nl.lt0(a)), e)))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      nl.lt_ne(ap, bp, e)

# a <= b: not b < a
def nl.le_nlt(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n +bb:
      nl.lt0(bb)
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(0n, 1n+ap) == False{} : Bool}, nl.ft(e))
    case 1n+ap 1n+bp:
      nl.le_nlt(ap, bp, e)

def nl.eq(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, nl.ft(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, nl.ft(e))
    case 1n+ap 1n+bp:
      %nl.eq(ap, bp, e) : {1n+ap == 1n+_ : Nat}
      {==}

def nl.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nl.sub_self(a: Nat) -> {Nat.sub(a, a) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      nl.sub_self(p)

# c <= d: (1 + d) - c = 1 + (d - c)
def nl.sub_succ(d: Nat, c: Nat, h: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.sub(1n+d, c) == 1n+Nat.sub(d, c) : Nat}:
  match d c:
    case _ 0n:
      %Equal.sym(Nat, Nat.sub(d, 0n), d, nl.sub_zero(d)) : {1n+d == 1n+_ : Nat}
      {==}
    case 0n 1n+cp:
      Empty.absurd({Nat.sub(1n, 1n+cp) == 1n+Nat.sub(0n, 1n+cp) : Nat}, nl.ft(h))
    case 1n+dp 1n+cp:
      nl.sub_succ(dp, cp, h)

def nl.max1(n: Nat) -> {Nat.is_lt(0n, Nat.max(n, 1n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}
