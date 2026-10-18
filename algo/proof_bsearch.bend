# Proof helpers for bend-osdev-algo: the Array binary search, through
# bend-osdev-array's laws. PROOF.bend uses them for the laws that tie
# bsearch.array_lower_bound and bsearch.array_find to the list reference.
#
# A perfect array is reflected, once, into Arrays.of_list(d, l, 0) for a
# Data list l (array's `reflect`); array's of_list_get then turns each read
# of the search into a literal pair: the same array, and the element of l at
# the masked index. So the search on the array is bq.run, the same halving
# on Data (bq.go), which hands the array back. The value of each index is
# then followed as a Nat (proof_u32.bend): mid is lo + (hi - lo) / 2, and a
# halving at least halves hi - lo.
import Base
import ./bsearch.bend as S
import ../array/array.bend as A
import ../array/LAWS.bend as AL
import ../array/PROOF.bend as APF
import ./proof_u32.bend as U

# Shorthands (they unfold to the defs they name)

def bq.ol(+d: Nat, +l: List<&2, U32>) -> Array<U32>:
  A.Arrays.of_list(U32, d, l, 0)

def bq.mid(+lo: U32, +hi: U32) -> U32:
  U32.add(lo, U32.shr(U32.sub(hi, lo)))

# the element the search reads between lo and hi
def bq.x(+d: Nat, +l: List<&2, U32>, +lo: U32, +hi: U32) -> U32:
  A.Arrays.nth(U32, l, A.Arrays.index(d, bq.mid(lo, hi)), 0)

# the searched prefix, its lower bound, and the range's size and middle as
# Nats
def bq.pre(+l: List<&2, U32>, +n: U32) -> List<&2, U32>:
  List.take(&2, U32, l, U32.to_nat(n))

def bq.lb(+l: List<&2, U32>, +n: U32, +key: U32) -> Nat:
  S.bsearch.lower_bound(List.take(&2, U32, l, U32.to_nat(n)), key)

def bq.s(+lo: U32, +hi: U32) -> Nat:
  Nat.sub(U32.to_nat(hi), U32.to_nat(lo))

def bq.m(+lo: U32, +hi: U32) -> Nat:
  Nat.add(U32.to_nat(lo), U.uq.half(Nat.sub(U32.to_nat(hi), U32.to_nat(lo))))

# The search on Data: one halving of [lo, hi), as bsearch.array.advance

def bq.lo_b(b: Bool, +lo: U32, +mid: U32) -> U32:
  match b:
    case True{}:
      U32.inc(mid)
    case False{}:
      lo

def bq.hi_b(b: Bool, +hi: U32, +mid: U32) -> U32:
  match b:
    case True{}:
      hi
    case False{}:
      mid

def bq.nlo.a(c: Bool, b: Bool, +lo: U32, +mid: U32) -> U32:
  match c:
    case True{}:
      bq.lo_b(b, lo, mid)
    case False{}:
      lo

def bq.nhi.a(c: Bool, b: Bool, +hi: U32, +mid: U32) -> U32:
  match c:
    case True{}:
      bq.hi_b(b, hi, mid)
    case False{}:
      hi

def bq.nlo(+d: Nat, +l: List<&2, U32>, +lo: U32, +hi: U32, +key: U32) -> U32:
  bq.nlo.a(U32.is_lt(lo, hi), U32.is_lt(bq.x(d, l, lo, hi), key), lo, bq.mid(lo, hi))

def bq.nhi(+d: Nat, +l: List<&2, U32>, +lo: U32, +hi: U32, +key: U32) -> U32:
  bq.nhi.a(U32.is_lt(lo, hi), U32.is_lt(bq.x(d, l, lo, hi), key), hi, bq.mid(lo, hi))

# f halvings, then lo
def bq.run(f: Nat, +d: Nat, +l: List<&2, U32>, +lo: U32, +hi: U32, +key: U32) -> U32:
  match f:
    case 0n:
      lo
    case 1n+g:
      bq.run(g, d, l, bq.nlo(d, l, lo, hi, key), bq.nhi(d, l, lo, hi, key), key)

# The search on a reflected array is the search on Data

def bq.pick_eq(b: Bool, -a: Array<U32>, +lo: U32, +hi: U32, +mid: U32) -> {S.bsearch.array.pick(b, a, lo, hi, mid) == S.BsearchState{a, bq.lo_b(b, lo, mid), bq.hi_b(b, hi, mid)} : S.BsearchState}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def bq.step_eq(c: Bool, -a: Array<U32>, +x: U32, +key: U32, +lo: U32, +hi: U32, +mid: U32) -> {S.bsearch.array.step(c, (a, x), key, lo, hi, mid) == S.BsearchState{a, bq.nlo.a(c, U32.is_lt(x, key), lo, mid), bq.nhi.a(c, U32.is_lt(x, key), hi, mid)} : S.BsearchState}:
  match c:
    case True{}:
      bq.pick_eq(U32.is_lt(x, key), a, lo, hi, mid)
    case False{}:
      {==}

def bq.go(f: Nat, +d: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +lo: U32, +hi: U32, +key: U32) -> {S.bsearch.array.go(f, S.BsearchState{bq.ol(d, l), lo, hi}, key) == (bq.ol(d, l), bq.run(f, d, l, lo, hi, key)) : Array<U32> & U32}:
  match f:
    case 0n:
      {==}
    case 1n+ +g:
      -a0 = bq.ol(d, l)
      +mid = bq.mid(lo, hi)
      +x = bq.x(d, l, lo, hi)
      %Equal.sym(Array<U32> & U32, Array.get(U32, a0, mid), (a0, x), AL.of_list_get(U32, d, l, 0, hl, hd, mid)) : {S.bsearch.array.go(g, S.bsearch.array.step(U32.is_lt(lo, hi), _, key, lo, hi, mid), key) == (a0, bq.run(1n+g, d, l, lo, hi, key)) : Array<U32> & U32}
      %Equal.sym(S.BsearchState, S.bsearch.array.step(U32.is_lt(lo, hi), (a0, x), key, lo, hi, mid), S.BsearchState{a0, bq.nlo(d, l, lo, hi, key), bq.nhi(d, l, lo, hi, key)}, bq.step_eq(U32.is_lt(lo, hi), a0, x, key, lo, hi, mid)) : {S.bsearch.array.go(g, _, key) == (a0, bq.run(1n+g, d, l, lo, hi, key)) : Array<U32> & U32}
      bq.go(g, d, l, hl, hd, bq.nlo(d, l, lo, hi, key), bq.nhi(d, l, lo, hi, key), key)

# Contradictions

def bq.bt(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def bq.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : bq.bt(_)
  Unit{}

def bq.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : bq.bt(_)
  Unit{}

def bq.nt(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def bq.sz(-k: Nat, e: {1n+k == 0n : Nat}) -> Empty:
  %Equal.sym(Nat, 1n+k, 0n, e) : bq.nt(_)
  Unit{}

# Nat order

def bq.le_zero(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def bq.le_refl(x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      bq.le_refl(p)

def bq.le_succ_r(x: Nat, y: Nat, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(x, 1n+y) == True{} : Bool}:
  match x y:
    case 0n _:
      {==}
    case 1n+xp 0n:
      Empty.absurd({Nat.is_le(1n+xp, 1n) == True{} : Bool}, bq.ft(h))
    case 1n+xp 1n+yp:
      bq.le_succ_r(xp, yp, h)

def bq.lt_le(x: Nat, y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_le(x, y) == True{} : Bool}:
  match x y:
    case 0n _:
      bq.le_zero(y)
    case 1n+xp 0n:
      Empty.absurd({Nat.is_le(1n+xp, 0n) == True{} : Bool}, bq.ft(h))
    case 1n+xp 1n+yp:
      bq.lt_le(xp, yp, h)

def bq.le_trans(a: Nat, b: Nat, c: Nat, e: {Nat.is_le(a, b) == True{} : Bool}, f: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      bq.le_zero(c)
    case 1n+ap 0n _:
      Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, bq.ft(e))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, bq.ft(f))
    case 1n+ap 1n+bp 1n+cp:
      bq.le_trans(ap, bp, cp, e, f)

def bq.lt_le_trans(a: Nat, b: Nat, c: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}, f: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n _:
      Empty.absurd({Nat.is_lt(0n, c) == True{} : Bool}, bq.ft(e))
    case 0n 1n+bp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, bq.ft(f))
    case 0n 1n+bp 1n+cp:
      {==}
    case 1n+ap 0n _:
      Empty.absurd({Nat.is_lt(1n+ap, c) == True{} : Bool}, bq.ft(e))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, bq.ft(f))
    case 1n+ap 1n+bp 1n+cp:
      bq.lt_le_trans(ap, bp, cp, e, f)

def bq.le_antisym(x: Nat, y: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_le(y, x) == True{} : Bool}) -> {x == y : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+yp:
      Empty.absurd({0n == 1n+yp : Nat}, bq.ft(h2))
    case 1n+xp 0n:
      Empty.absurd({1n+xp == 0n : Nat}, bq.ft(h1))
    case 1n+xp 1n+yp:
      U.uq.succ_cong(xp, yp, bq.le_antisym(xp, yp, h1, h2))

def bq.not_lt(x: Nat, y: Nat, e: {Nat.is_lt(x, y) == False{} : Bool}) -> {Nat.is_le(y, x) == True{} : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+yp:
      Empty.absurd({Nat.is_le(1n+yp, 0n) == True{} : Bool}, bq.tf(e))
    case 1n+xp 0n:
      {==}
    case 1n+xp 1n+yp:
      bq.not_lt(xp, yp, e)

def bq.lt_one(x: Nat, e: {Nat.is_lt(x, 1n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          Empty.absurd({1n == 0n : Nat}, bq.ft(e))
        case 1n+q:
          Empty.absurd({2n+q == 0n : Nat}, bq.ft(e))

def bq.lt_succ_le(x: Nat, y: Nat, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_lt(x, 1n+y) == True{} : Bool}:
  match x y:
    case 0n _:
      {==}
    case 1n+xp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 1n) == True{} : Bool}, bq.ft(h))
    case 1n+xp 1n+yp:
      bq.lt_succ_le(xp, yp, h)

def bq.lt_rw(-x: Nat, -y: Nat, -x2: Nat, -y2: Nat, ex: {x == x2 : Nat}, ey: {y == y2 : Nat}, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x2, y2) == True{} : Bool}:
  %ex : {Nat.is_lt(_, y2) == True{} : Bool}
  %ey : {Nat.is_lt(x, _) == True{} : Bool}
  h

def bq.le_rw(-x: Nat, -y: Nat, -x2: Nat, -y2: Nat, ex: {x == x2 : Nat}, ey: {y == y2 : Nat}, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(x2, y2) == True{} : Bool}:
  %ex : {Nat.is_le(_, y2) == True{} : Bool}
  %ey : {Nat.is_le(x, _) == True{} : Bool}
  h

def bq.lt_cancel(s: Nat, -r: Nat, -u: Nat) -> {Nat.is_lt(Nat.add(s, r), Nat.add(s, u)) == Nat.is_lt(r, u) : Bool}:
  match s:
    case 0n:
      {==}
    case 1n+p:
      bq.lt_cancel(p, r, u)

def bq.pw_pos(f: Nat) -> {Nat.is_lt(0n, U.uq.pw(f)) == True{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n+ +g:
      U.uq.lt_dbl_self(0n, U.uq.pw(g), bq.pw_pos(g))

# Nat arithmetic

def bq.sub_zero(x: Nat) -> {Nat.sub(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def bq.add_sub(d: Nat, s: Nat, e: {Nat.is_le(d, s) == True{} : Bool}) -> {Nat.add(d, Nat.sub(s, d)) == s : Nat}:
  match d s:
    case 0n +ss:
      bq.sub_zero(ss)
    case 1n+dp 0n:
      Empty.absurd({1n+Nat.add(dp, 0n) == 0n : Nat}, bq.ft(e))
    case 1n+ +dp 1n+ +sp:
      U.uq.succ_cong(Nat.add(dp, Nat.sub(sp, dp)), sp, bq.add_sub(dp, sp, e))

def bq.sub_cancel(l: Nat, -s: Nat, -t: Nat) -> {Nat.sub(Nat.add(l, s), Nat.add(l, t)) == Nat.sub(s, t) : Nat}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      bq.sub_cancel(p, s, t)

def bq.sub_pos(l: Nat, h: Nat, e: {Nat.is_lt(l, h) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.sub(h, l)) == True{} : Bool}:
  match l h:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, bq.ft(e))
    case 0n 1n+hp:
      {==}
    case 1n+lp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, bq.ft(e))
    case 1n+lp 1n+hp:
      bq.sub_pos(lp, hp, e)

def bq.sub_le0(h: Nat, l: Nat, e: {Nat.is_le(h, l) == True{} : Bool}) -> {Nat.sub(h, l) == 0n : Nat}:
  match h l:
    case 0n _:
      {==}
    case 1n+hp 0n:
      Empty.absurd({1n+hp == 0n : Nat}, bq.ft(e))
    case 1n+hp 1n+lp:
      bq.sub_le0(hp, lp, e)

def bq.sub0_le(h: Nat, l: Nat, e: {Nat.sub(h, l) == 0n : Nat}) -> {Nat.is_le(h, l) == True{} : Bool}:
  match h l:
    case 0n 0n:
      {==}
    case 0n 1n+lp:
      {==}
    case 1n+hp 0n:
      Empty.absurd({Nat.is_le(1n+hp, 0n) == True{} : Bool}, bq.sz(hp, e))
    case 1n+hp 1n+lp:
      bq.sub0_le(hp, lp, e)

def bq.sub_step(q: Nat, k: Nat) -> {Nat.is_le(Nat.sub(q, k), 1n+Nat.sub(q, 1n+k)) == True{} : Bool}:
  match q k:
    case 0n _:
      {==}
    case 1n+ +qp 0n:
      %Equal.sym(Nat, Nat.sub(qp, 0n), qp, bq.sub_zero(qp)) : {Nat.is_le(1n+qp, 1n+_) == True{} : Bool}
      bq.le_refl(qp)
    case 1n+qp 1n+kp:
      bq.sub_step(qp, kp)

# Halving

def bq.half_le(q: Nat) -> {Nat.is_le(U.uq.half(q), q) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+ +r:
          bq.le_succ_r(U.uq.half(r), r, bq.half_le(r))

def bq.half_lt(s: Nat, h: {Nat.is_lt(0n, s) == True{} : Bool}) -> {Nat.is_lt(U.uq.half(s), s) == True{} : Bool}:
  match s:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, bq.ft(h))
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+ +q:
          bq.lt_succ_le(U.uq.half(q), q, bq.half_le(q))

# s < 2p: s / 2 < p
def bq.half_lt_pw(s: Nat, p: Nat, h: {Nat.is_lt(s, Nat.double(p)) == True{} : Bool}) -> {Nat.is_lt(U.uq.half(s), p) == True{} : Bool}:
  match s:
    case 0n:
      match p:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, bq.ft(h))
        case 1n+pp:
          {==}
    case 1n+sp:
      match sp:
        case 0n:
          match p:
            case 0n:
              Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, bq.ft(h))
            case 1n+pp:
              {==}
        case 1n+q:
          match p:
            case 0n:
              Empty.absurd({Nat.is_lt(1n+U.uq.half(q), 0n) == True{} : Bool}, bq.ft(h))
            case 1n+pp:
              bq.half_lt_pw(q, pp, h)

# s < 2p: s - (1 + s / 2) < p
def bq.hr_lt_pw(s: Nat, p: Nat, h: {Nat.is_lt(s, Nat.double(p)) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(s, 1n+U.uq.half(s)), p) == True{} : Bool}:
  match s:
    case 0n:
      match p:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, bq.ft(h))
        case 1n+pp:
          {==}
    case 1n+sp:
      match sp:
        case 0n:
          match p:
            case 0n:
              Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, bq.ft(h))
            case 1n+pp:
              {==}
        case 1n+ +q:
          match p:
            case 0n:
              Empty.absurd({Nat.is_lt(Nat.sub(q, U.uq.half(q)), 0n) == True{} : Bool}, bq.ft(h))
            case 1n+ +pp:
              U.uq.le_lt_trans(Nat.sub(q, U.uq.half(q)), 1n+Nat.sub(q, 1n+U.uq.half(q)), 1n+pp, bq.sub_step(q, U.uq.half(q)), bq.hr_lt_pw(q, pp, h))

# Lists

def bq.get_take(xs: List<&2, U32>, k: Nat, m: Nat, h: {Nat.is_lt(m, k) == True{} : Bool}) -> {List.get(&2, U32, List.take(&2, U32, xs, k), m) == List.get(&2, U32, xs, m) : Maybe<&2, U32>}:
  match xs k m:
    case Nil{} _ _:
      {==}
    case Con{x, t} 0n 0n:
      Empty.absurd({List.get(&2, U32, List.take(&2, U32, Con{x, t}, 0n), 0n) == List.get(&2, U32, Con{x, t}, 0n) : Maybe<&2, U32>}, bq.ft(h))
    case Con{x, t} 0n 1n+mp:
      Empty.absurd({List.get(&2, U32, List.take(&2, U32, Con{x, t}, 0n), 1n+mp) == List.get(&2, U32, Con{x, t}, 1n+mp) : Maybe<&2, U32>}, bq.ft(h))
    case Con{x, t} 1n+kp 0n:
      {==}
    case Con{x, t} 1n+kp 1n+mp:
      bq.get_take(t, kp, mp, h)

def bq.get_nth(xs: List<&2, U32>, m: Nat, h: {Nat.is_lt(m, List.length(&2, U32, xs)) == True{} : Bool}) -> {List.get(&2, U32, xs, m) == Some{A.Arrays.nth(U32, xs, m, 0)} : Maybe<&2, U32>}:
  match xs m:
    case Nil{} 0n:
      Empty.absurd({None{} == Some{0} : Maybe<&2, U32>}, bq.ft(h))
    case Nil{} 1n+mp:
      Empty.absurd({None{} == Some{0} : Maybe<&2, U32>}, bq.ft(h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+mp:
      bq.get_nth(t, mp, h)

def bq.len_take(xs: List<&2, U32>, k: Nat, h: {Nat.is_le(k, List.length(&2, U32, xs)) == True{} : Bool}) -> {List.length(&2, U32, List.take(&2, U32, xs, k)) == k : Nat}:
  match xs k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+kp:
      Empty.absurd({0n == 1n+kp : Nat}, bq.ft(h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+kp:
      U.uq.succ_cong(List.length(&2, U32, List.take(&2, U32, t, kp)), kp, bq.len_take(t, kp, h))

def bq.get_len(xs: List<&2, U32>) -> {List.get(&2, U32, xs, List.length(&2, U32, xs)) == None{} : Maybe<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      bq.get_len(t)
