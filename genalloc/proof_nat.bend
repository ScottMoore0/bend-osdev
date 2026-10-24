# Proof helpers for bend-osdev-genalloc: Nat arithmetic and order, by
# induction on Base's unary Nat.
import Base
import ../u32/LAWS.bend as UL
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF.bend as UP
import ../u32/PROOF_order.bend as UOP

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

# (a + b) + (c + d) = (a + c) + (b + d)
def nl.swap4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), UL.nat_add_assoc(a, b, Nat.add(c, d))) : {_ == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), UL.nat_add_assoc(a, c, Nat.add(b, d))) : {Nat.add(a, Nat.add(b, Nat.add(c, d))) == _ : Nat}
  %UL.nat_add_assoc(b, c, d) : {Nat.add(a, _) == Nat.add(a, Nat.add(c, Nat.add(b, d))) : Nat}
  %UL.nat_add_assoc(c, b, d) : {Nat.add(a, Nat.add(Nat.add(b, c), d)) == Nat.add(a, _) : Nat}
  %UL.nat_add_comm(b, c) : {Nat.add(a, Nat.add(Nat.add(b, c), d)) == Nat.add(a, Nat.add(_, d)) : Nat}
  {==}

# Multiplication

# Order

def nl.le_zero(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

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
      UO.nat_lt_le_trans(0n, g, Nat.add(g, Nat.mul(bp, g)), hg, UO.nat_le_add_r(g, Nat.mul(bp, g)))
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
