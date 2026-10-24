# Proofs of LAWS_div.bend, from Base's definition of Nat.divmod: with a
# divisor 1 + bp, Nat.divmod(a, 1 + bp) runs go(a, bp, 0, 0), which counts m
# down and r up (m + r == bp throughout) and d once per full round. The
# lemmas are those bend-osdev-ext2, -iodev and -blockdev proved for their
# own use (PROOF.bend, PROOF_range.bend), now proved here once.
import Base
import ./LAWS.bend as UL
import ./PROOF.bend as UP
import ./LAWS_div.bend as Laws

def ud.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def ud.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def ud.succ_inj(+x: Nat, +y: Nat, e: {1n+x == 1n+y : Nat}) -> {x == y : Nat}:
  Equal.cong(Nat, Nat, ud.pred, 1n+x, 1n+y, e)

# a + r == b + r gives a == b
def ud.add_cancel(+r: Nat, +a: Nat, +b: Nat, e: {Nat.add(a, r) == Nat.add(b, r) : Nat}) -> {a == b : Nat}:
  match r:
    case 0n:
      Equal.trans(Nat, a, Nat.add(b, 0n), b, Equal.trans(Nat, a, Nat.add(a, 0n), Nat.add(b, 0n), Equal.sym(Nat, Nat.add(a, 0n), a, UL.nat_add_zero(a)), e), UL.nat_add_zero(b))
    case 1n+q:
      ud.add_cancel(q, a, b, ud.succ_inj(Nat.add(a, q), Nat.add(b, q), Equal.trans(Nat, 1n+Nat.add(a, q), Nat.add(a, 1n+q), 1n+Nat.add(b, q), Equal.sym(Nat, Nat.add(a, 1n+q), 1n+Nat.add(a, q), UL.nat_add_succ(a, q)), Equal.trans(Nat, Nat.add(a, 1n+q), Nat.add(b, 1n+q), 1n+Nat.add(b, q), e, UL.nat_add_succ(b, q)))))

def ud.bool_disc(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def ud.bool_clash(h: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, h) : ud.bool_disc(_)
  Unit{}

def ud.ex_falso(-A: Type, e: Empty) -> A:
  match e:

def ud.no_lt_one(+np: Nat) -> {Nat.is_lt(1n+np, 1n) == True{} : Bool} -> Empty:
  match np:
    case 0n:
      h => ud.bool_clash(h)
    case 1n+q:
      h => ud.bool_clash(h)

# r < bp + 1 gives (bp - r) + r == bp
def ud.sub_add(+bp: Nat, +r: Nat, h: {Nat.is_lt(r, 1n+bp) == True{} : Bool}) -> {Nat.add(Nat.sub(bp, r), r) == bp : Nat}:
  match bp r:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      ud.ex_falso({Nat.add(Nat.sub(0n, 1n+q), 1n+q) == 0n : Nat}, ud.no_lt_one(q, h))
    case 1n+b 0n:
      UL.nat_add_zero(1n+b)
    case 1n+b 1n+q:
      Equal.trans(Nat, Nat.add(Nat.sub(b, q), 1n+q), 1n+Nat.add(Nat.sub(b, q), q), 1n+b, UL.nat_add_succ(Nat.sub(b, q), q), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.sub(b, q), q), b, ud.sub_add(b, q, h)))

# Division

def ud.dm_lhs(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat) -> Nat:
  Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)))

def ud.dm_sum(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat) -> {Nat.add(m, r) == bp : Nat} -> {ud.dm_lhs(n, m, d, r, bp) == Nat.add(n, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}:
  match n m:
    case 0n _:
      h => {==}
    case 1n+np 0n:
      +h =>
        +dd = Nat.mul(d, 1n+bp)
        +x = Nat.add(Nat.add(bp, dd), 0n)
        %Equal.sym(Nat, r, bp, h) : {ud.dm_lhs(1n+np, 0n, d, r, bp) == 1n+Nat.add(np, Nat.add(dd, _)) : Nat}
        %UL.nat_add_comm(bp, dd) : {ud.dm_lhs(1n+np, 0n, d, r, bp) == 1n+Nat.add(np, _) : Nat}
        %UL.nat_add_zero(Nat.add(bp, dd)) : {ud.dm_lhs(1n+np, 0n, d, r, bp) == 1n+Nat.add(np, _) : Nat}
        %UL.nat_add_succ(np, x) : {ud.dm_lhs(1n+np, 0n, d, r, bp) == _ : Nat}
        ud.dm_sum(np, r, 1n+d, 0n, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, UL.nat_add_zero(r), h))
    case 1n+np 1n+mp:
      h =>
        +dd = Nat.mul(d, 1n+bp)
        %UL.nat_add_succ(np, Nat.add(dd, r)) : {ud.dm_lhs(1n+np, 1n+mp, d, r, bp) == _ : Nat}
        %UL.nat_add_succ(dd, r) : {ud.dm_lhs(1n+np, 1n+mp, d, r, bp) == Nat.add(np, _) : Nat}
        ud.dm_sum(np, mp, d, 1n+r, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, UL.nat_add_succ(mp, r), h))

def ud.div_mod(+k: Nat, +bp: Nat) -> {Nat.add(Nat.mul(Nat.div(k, 1n+bp), 1n+bp), Nat.mod(k, 1n+bp)) == k : Nat}:
  Equal.trans(Nat, ud.dm_lhs(k, bp, 0n, 0n, bp), Nat.add(k, 0n), k, ud.dm_sum(k, bp, 0n, 0n, bp, UL.nat_add_zero(bp)), UL.nat_add_zero(k))

def ud.lt_add(+m: Nat, +r: Nat) -> {Nat.is_lt(r, 1n+Nat.add(m, r)) == True{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(m, 1n+p), 1n+Nat.add(m, p), UL.nat_add_succ(m, p)) : {Nat.is_lt(1n+p, 1n+_) == True{} : Bool}
      ud.lt_add(m, p)

def ud.dm_lt(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat) -> {Nat.add(m, r) == bp : Nat} -> {Nat.is_lt(Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+bp) == True{} : Bool}:
  match n m:
    case 0n _:
      h =>
        %h : {Nat.is_lt(r, 1n+_) == True{} : Bool}
        ud.lt_add(m, r)
    case 1n+np 0n:
      h => ud.dm_lt(np, r, 1n+d, 0n, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, UL.nat_add_zero(r), h))
    case 1n+np 1n+mp:
      h => ud.dm_lt(np, mp, d, 1n+r, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, UL.nat_add_succ(mp, r), h))

def ud.mod_lt(+k: Nat, +bp: Nat) -> {Nat.is_lt(Nat.mod(k, 1n+bp), 1n+bp) == True{} : Bool}:
  ud.dm_lt(k, bp, 0n, 0n, bp, UL.nat_add_zero(bp))

# fewer steps than m left in the round: the remainder grows by n
def ud.dm_small(+n: Nat, +m: Nat, +d: Nat, +r: Nat) -> {Nat.is_lt(n, 1n+m) == True{} : Bool} -> {Nat.divmod.go(n, m, d, r) == (d, Nat.add(n, r)) : Nat & Nat}:
  match n m:
    case 0n _:
      h => {==}
    case 1n+np 0n:
      h => ud.ex_falso({Nat.divmod.go(1n+np, 0n, d, r) == (d, Nat.add(1n+np, r)) : Nat & Nat}, ud.no_lt_one(np, h))
    case 1n+np 1n+mp:
      h =>
        %UL.nat_add_succ(np, r) : {Nat.divmod.go(1n+np, 1n+mp, d, r) == (d, _) : Nat & Nat}
        ud.dm_small(np, mp, d, 1n+r, h)

# finishing a round: m steps, then one more starts the next
def ud.dm_round(+m: Nat, +n: Nat, +d: Nat, +r: Nat) -> {Nat.divmod.go(Nat.add(m, 1n+n), m, d, r) == Nat.divmod.go(n, Nat.add(m, r), 1n+d, 0n) : Nat & Nat}:
  match m:
    case 0n:
      {==}
    case 1n+mp:
      %UL.nat_add_succ(mp, r) : {Nat.divmod.go(Nat.add(1n+mp, 1n+n), 1n+mp, d, r) == Nat.divmod.go(n, _, 1n+d, 0n) : Nat & Nat}
      ud.dm_round(mp, n, d, 1n+r)

def ud.dm_rounds(+g: Nat, +i: Nat, +d: Nat, +bp: Nat) -> {Nat.is_lt(i, 1n+bp) == True{} : Bool} -> {Nat.divmod.go(Nat.add(Nat.mul(g, 1n+bp), i), bp, d, 0n) == (Nat.add(g, d), i) : Nat & Nat}:
  match g:
    case 0n:
      h =>
        %UL.nat_add_zero(i) : {Nat.divmod.go(i, bp, d, 0n) == (d, _) : Nat & Nat}
        ud.dm_small(i, bp, d, 0n, h)
    case 1n+gp:
      h =>
        +gg = Nat.mul(gp, 1n+bp)
        +y = Nat.add(gg, i)
        %Equal.sym(Nat, Nat.add(Nat.add(bp, gg), i), Nat.add(bp, y), UL.nat_add_assoc(bp, gg, i)) : {Nat.divmod.go(1n+_, bp, d, 0n) == (1n+Nat.add(gp, d), i) : Nat & Nat}
        %UL.nat_add_succ(bp, y) : {Nat.divmod.go(_, bp, d, 0n) == (1n+Nat.add(gp, d), i) : Nat & Nat}
        %Equal.sym(Nat & Nat, Nat.divmod.go(Nat.add(bp, 1n+y), bp, d, 0n), Nat.divmod.go(y, Nat.add(bp, 0n), 1n+d, 0n), ud.dm_round(bp, y, d, 0n)) : {_ == (1n+Nat.add(gp, d), i) : Nat & Nat}
        %Equal.sym(Nat, Nat.add(bp, 0n), bp, UL.nat_add_zero(bp)) : {Nat.divmod.go(y, _, 1n+d, 0n) == (1n+Nat.add(gp, d), i) : Nat & Nat}
        %UL.nat_add_succ(gp, d) : {Nat.divmod.go(y, bp, 1n+d, 0n) == (_, i) : Nat & Nat}
        ud.dm_rounds(gp, i, 1n+d, bp, h)

# Rounding up. Nat.sub(1 + bp, 1) is Nat.sub(bp, 0), which is bp by
# ud.sub_zero.

# a + bp == (a + (bp - r)) + r, for r < 1 + bp
def ud.cover_sum(+bp: Nat, +a: Nat, +r: Nat, h: {Nat.is_lt(r, 1n+bp) == True{} : Bool}) -> {Nat.add(a, Nat.sub(bp, 0n)) == Nat.add(Nat.add(a, Nat.sub(bp, r)), r) : Nat}:
  %Equal.sym(Nat, Nat.sub(bp, 0n), bp, ud.sub_zero(bp)) : {Nat.add(a, _) == Nat.add(Nat.add(a, Nat.sub(bp, r)), r) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, Nat.sub(bp, r)), r), Nat.add(a, Nat.add(Nat.sub(bp, r), r)), UL.nat_add_assoc(a, Nat.sub(bp, r), r)) : {Nat.add(a, bp) == _ : Nat}
  %ud.sub_add(bp, r, h) : {Nat.add(a, _) == Nat.add(a, Nat.add(Nat.sub(bp, r), r)) : Nat}
  {==}

def ud.cover(+bp: Nat, +a: Nat) -> {Nat.mul(Nat.div(Nat.add(a, Nat.sub(1n+bp, 1n)), 1n+bp), 1n+bp) == Nat.add(a, Nat.sub(Nat.sub(1n+bp, 1n), Nat.mod(Nat.add(a, Nat.sub(1n+bp, 1n)), 1n+bp))) : Nat}:
  +t = Nat.add(a, Nat.sub(bp, 0n))
  +q = Nat.div(t, 1n+bp)
  +r = Nat.mod(t, 1n+bp)
  %Equal.sym(Nat, Nat.sub(bp, 0n), bp, ud.sub_zero(bp)) : {Nat.mul(q, 1n+bp) == Nat.add(a, Nat.sub(_, r)) : Nat}
  ud.add_cancel(r, Nat.mul(q, 1n+bp), Nat.add(a, Nat.sub(bp, r)), Equal.trans(Nat, Nat.add(Nat.mul(q, 1n+bp), r), t, Nat.add(Nat.add(a, Nat.sub(bp, r)), r), ud.div_mod(t, bp), ud.cover_sum(bp, a, r, ud.mod_lt(t, bp))))

# The laws

def Laws.nat_div_mod(a, bp):
  ud.div_mod(a, bp)

def Laws.nat_mod_lt(a, bp):
  ud.mod_lt(a, bp)

def Laws.nat_divmod_exact(g, i, bp, h):
  %UL.nat_add_zero(g) : {Nat.divmod.go(Nat.add(Nat.mul(g, 1n+bp), i), bp, 0n, 0n) == (_, i) : Nat & Nat}
  ud.dm_rounds(g, i, 0n, bp, h)

def Laws.nat_round_up(bp, a):
  ud.cover(bp, a)
