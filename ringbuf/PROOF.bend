import Base
import ./ringbuf.bend as R
import ./model.bend as M
import ../array/array.bend as A
import ../array/LAWS.bend as AL
import ../array/PROOF.bend as APF
import ./proof_items.bend as I
import ./LAWS.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF.bend as UP
import ../u32/PROOF_order.bend as UOP

# Contradictions

def absurd.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def absurd.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : absurd.bool(_)
  Unit{}

def absurd.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : absurd.bool(_)
  Unit{}

def bool.contra(-c: Bool, -T: Type, e: {c == True{} : Bool}, f: {c == False{} : Bool}) -> T:
  Empty.absurd(T, absurd.tf(Equal.trans(Bool, True{}, c, False{}, Equal.sym(Bool, c, True{}, e), f)))

# Bool

def bool.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))

def bool.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, absurd.ft(e))

def bool.and_intro(-a: Bool, -b: Bool, e: {a == True{} : Bool}, f: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, e) : {Bool.and(_, b) == True{} : Bool}
  f

# Nat

def nat.le_zero(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nat.le_succ(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 1n) == True{} : Bool}, absurd.ft(e))
    case 1n+ap 1n+bp:
      nat.le_succ(ap, bp, e)

def nat.eq_of(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, absurd.ft(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, absurd.ft(e))
    case 1n+ +ap 1n+ +bp:
      %nat.eq_of(ap, bp, e) : {1n+ap == 1n+_ : Nat}
      {==}

def nat.sub_zero(x: Nat) -> {Nat.sub(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nat.sub_self(x: Nat) -> {Nat.sub(x, x) == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      nat.sub_self(p)

def nat.min_zero_r(x: Nat) -> {Nat.min(x, 0n) == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (1 + i) - u = 1 + (i - u), for u <= i
def nat.sub_succ(i: Nat, u: Nat, e: {Nat.is_le(u, i) == True{} : Bool}) -> {Nat.sub(1n+i, u) == 1n+Nat.sub(i, u) : Nat}:
  match i u:
    case +ii 0n:
      %Equal.sym(Nat, Nat.sub(ii, 0n), ii, nat.sub_zero(ii)) : {1n+ii == 1n+_ : Nat}
      {==}
    case 0n 1n+up:
      Empty.absurd({Nat.sub(1n, 1n+up) == 1n : Nat}, absurd.ft(e))
    case 1n+ip 1n+up:
      nat.sub_succ(ip, up, e)

# d <= s and d != s: 1 + d <= s
def nat.le_ne_succ(d: Nat, s: Nat, e: {Nat.is_le(d, s) == True{} : Bool}, f: {Nat.is_eq(d, s) == False{} : Bool}) -> {Nat.is_le(1n+d, s) == True{} : Bool}:
  match d s:
    case 0n 0n:
      Empty.absurd({False{} == True{} : Bool}, absurd.tf(f))
    case 0n 1n+sp:
      nat.le_zero(sp)
    case 1n+dp 0n:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))
    case 1n+dp 1n+sp:
      nat.le_ne_succ(dp, sp, e, f)

# u < s and 1 + u != s: 1 + u < s
def nat.lt_succ_ne(u: Nat, s: Nat, e: {Nat.is_lt(u, s) == True{} : Bool}, f: {Nat.is_eq(1n+u, s) == False{} : Bool}) -> {Nat.is_lt(1n+u, s) == True{} : Bool}:
  match u s:
    case 0n 0n:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))
    case 1n+up 0n:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))
    case 0n 1n+sp:
      match sp:
        case 0n:
          Empty.absurd({False{} == True{} : Bool}, absurd.tf(f))
        case 1n+q:
          {==}
    case 1n+up 1n+sp:
      nat.lt_succ_ne(up, sp, e, f)

# u <= i and i != u: 1 + u <= i
def nat.le_ne(u: Nat, i: Nat, e: {Nat.is_le(u, i) == True{} : Bool}, f: {Nat.is_eq(i, u) == False{} : Bool}) -> {Nat.is_le(1n+u, i) == True{} : Bool}:
  match u i:
    case 0n 0n:
      Empty.absurd({False{} == True{} : Bool}, absurd.tf(f))
    case 0n 1n+ip:
      nat.le_zero(ip)
    case 1n+up 0n:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))
    case 1n+up 1n+ip:
      nat.le_ne(up, ip, e, f)

def nat.sub_succ_le(i: Nat, u: Nat) -> {Nat.is_le(Nat.sub(i, 1n+u), Nat.sub(i, u)) == True{} : Bool}:
  match i u:
    case 0n _:
      {==}
    case 1n+ +ip 0n:
      %Equal.sym(Nat, Nat.sub(ip, 0n), ip, nat.sub_zero(ip)) : {Nat.is_le(_, 1n+ip) == True{} : Bool}
      nat.le_succ(ip, ip, UL.nat_le_refl(ip))
    case 1n+ip 1n+up:
      nat.sub_succ_le(ip, up)

# 1 + (i - (1 + u)) = i - u, for 1 + u <= i
def nat.sub_succ2(i: Nat, u: Nat, e: {Nat.is_le(1n+u, i) == True{} : Bool}) -> {1n+Nat.sub(i, 1n+u) == Nat.sub(i, u) : Nat}:
  match i u:
    case 0n _:
      Empty.absurd({1n == 0n : Nat}, absurd.ft(e))
    case 1n+ +ip 0n:
      %Equal.sym(Nat, Nat.sub(ip, 0n), ip, nat.sub_zero(ip)) : {1n+_ == 1n+ip : Nat}
      {==}
    case 1n+ip 1n+up:
      nat.sub_succ2(ip, up, e)

def nat.add_sub(d: Nat, s: Nat, e: {Nat.is_le(d, s) == True{} : Bool}) -> {Nat.add(d, Nat.sub(s, d)) == s : Nat}:
  match d s:
    case 0n +ss:
      nat.sub_zero(ss)
    case 1n+dp 0n:
      Empty.absurd({1n+Nat.add(dp, 0n) == 0n : Nat}, absurd.ft(e))
    case 1n+ +dp 1n+ +sp:
      %nat.add_sub(dp, sp, e) : {1n+Nat.add(dp, Nat.sub(sp, dp)) == 1n+_ : Nat}
      {==}

def nat.eq_sub(i: Nat, u: Nat, e: {Nat.is_le(u, i) == True{} : Bool}) -> {Nat.is_eq(i, u) == Nat.is_eq(Nat.sub(i, u), 0n) : Bool}:
  match i u:
    case 0n 0n:
      {==}
    case 0n 1n+up:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))
    case 1n+ip 0n:
      {==}
    case 1n+ip 1n+up:
      nat.eq_sub(ip, up, e)

def nat.eq_sub_rev(d: Nat, s: Nat, e: {Nat.is_le(d, s) == True{} : Bool}) -> {Nat.is_eq(d, s) == Nat.is_eq(Nat.sub(s, d), 0n) : Bool}:
  match d s:
    case 0n 0n:
      {==}
    case 0n 1n+sp:
      {==}
    case 1n+dp 0n:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))
    case 1n+dp 1n+sp:
      nat.eq_sub_rev(dp, sp, e)

# s - d = 1 + (s - (1 + d)), for 1 + d <= s
def nat.sub_pred(s: Nat, d: Nat, e: {Nat.is_le(1n+d, s) == True{} : Bool}) -> {Nat.sub(s, d) == 1n+Nat.sub(s, 1n+d) : Nat}:
  match s d:
    case 0n _:
      Empty.absurd({0n == 1n : Nat}, absurd.ft(e))
    case 1n+ +sp 0n:
      %Equal.sym(Nat, Nat.sub(sp, 0n), sp, nat.sub_zero(sp)) : {1n+sp == 1n+_ : Nat}
      {==}
    case 1n+sp 1n+dp:
      nat.sub_pred(sp, dp, e)

def nat.dbl_pos(x: Nat, e: {Nat.is_lt(0n, x) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.double(x)) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))
    case 1n+k:
      {==}

def nat.size_pos(o: Nat) -> {Nat.is_lt(0n, R.ring.size(o)) == True{} : Bool}:
  match o:
    case 0n:
      {==}
    case 1n+ +p:
      nat.dbl_pos(R.ring.size(p), nat.size_pos(p))

def list.len_snoc(acc: List<&2, U32>, -x: U32) -> {List.length(&2, U32, List.append(&2, U32, acc, Con{x, Nil{}})) == 1n+List.length(&2, U32, acc) : Nat}:
  match acc:
    case Nil{}:
      {==}
    case Con{h, +t}:
      %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, t, Con{x, Nil{}})), 1n+List.length(&2, U32, t), list.len_snoc(t, x)) : {1n+_ == 2n+List.length(&2, U32, t) : Nat}
      {==}

# The invariant: its three parts, and building it

def inv.p1(+o: Nat, +i: Nat, +u: Nat, h: {R.ring.inv(o, i, u) == True{} : Bool}) -> {Nat.is_lt(u, R.ring.size(o)) == True{} : Bool}:
  bool.and_l(Nat.is_lt(u, R.ring.size(o)), Bool.and(Nat.is_le(u, i), Nat.is_le(Nat.sub(i, u), R.ring.size(o))), h)

def inv.p2(+o: Nat, +i: Nat, +u: Nat, h: {R.ring.inv(o, i, u) == True{} : Bool}) -> {Nat.is_le(u, i) == True{} : Bool}:
  bool.and_l(Nat.is_le(u, i), Nat.is_le(Nat.sub(i, u), R.ring.size(o)), bool.and_r(Nat.is_lt(u, R.ring.size(o)), Bool.and(Nat.is_le(u, i), Nat.is_le(Nat.sub(i, u), R.ring.size(o))), h))

def inv.p3(+o: Nat, +i: Nat, +u: Nat, h: {R.ring.inv(o, i, u) == True{} : Bool}) -> {Nat.is_le(Nat.sub(i, u), R.ring.size(o)) == True{} : Bool}:
  bool.and_r(Nat.is_le(u, i), Nat.is_le(Nat.sub(i, u), R.ring.size(o)), bool.and_r(Nat.is_lt(u, R.ring.size(o)), Bool.and(Nat.is_le(u, i), Nat.is_le(Nat.sub(i, u), R.ring.size(o))), h))

def inv.mk(-o: Nat, -i: Nat, -u: Nat, e: {Nat.is_lt(u, R.ring.size(o)) == True{} : Bool}, f: {Nat.is_le(u, i) == True{} : Bool}, g: {Nat.is_le(Nat.sub(i, u), R.ring.size(o)) == True{} : Bool}) -> {R.ring.inv(o, i, u) == True{} : Bool}:
  bool.and_intro(Nat.is_lt(u, R.ring.size(o)), Bool.and(Nat.is_le(u, i), Nat.is_le(Nat.sub(i, u), R.ring.size(o))), e, bool.and_intro(Nat.is_le(u, i), Nat.is_le(Nat.sub(i, u), R.ring.size(o)), f, g))

def inv.push3(+o: Nat, +i: Nat, +u: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ec: {R.ring.full.test(o, i, u) == False{} : Bool}) -> {Nat.is_le(Nat.sub(1n+i, u), R.ring.size(o)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(1n+i, u), 1n+Nat.sub(i, u), nat.sub_succ(i, u, inv.p2(o, i, u, h))) : {Nat.is_le(_, R.ring.size(o)) == True{} : Bool}
  nat.le_ne_succ(Nat.sub(i, u), R.ring.size(o), inv.p3(o, i, u, h), ec)

def inv.push(+o: Nat, +i: Nat, +u: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ec: {R.ring.full.test(o, i, u) == False{} : Bool}) -> {R.ring.inv(o, 1n+i, u) == True{} : Bool}:
  inv.mk(o, 1n+i, u, inv.p1(o, i, u, h), nat.le_succ(u, i, inv.p2(o, i, u, h)), inv.push3(o, i, u, h, ec))

def inv.pop_nowrap(+o: Nat, +i: Nat, +u: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ne: {R.ring.empty.test(i, u) == False{} : Bool}, ew: {Nat.is_eq(1n+u, R.ring.size(o)) == False{} : Bool}) -> {R.ring.inv(o, i, 1n+u) == True{} : Bool}:
  inv.mk(o, i, 1n+u, nat.lt_succ_ne(u, R.ring.size(o), inv.p1(o, i, u, h), ew), nat.le_ne(u, i, inv.p2(o, i, u, h), ne), UO.nat_le_trans(Nat.sub(i, 1n+u), Nat.sub(i, u), R.ring.size(o), nat.sub_succ_le(i, u), inv.p3(o, i, u, h)))

def inv.wrap3(+o: Nat, +i: Nat, +u: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ew: {Nat.is_eq(1n+u, R.ring.size(o)) == True{} : Bool}) -> {Nat.is_le(Nat.sub(Nat.sub(i, R.ring.size(o)), 0n), R.ring.size(o)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.sub(Nat.sub(i, R.ring.size(o)), 0n), Nat.sub(i, R.ring.size(o)), nat.sub_zero(Nat.sub(i, R.ring.size(o)))) : {Nat.is_le(_, R.ring.size(o)) == True{} : Bool}
  %nat.eq_of(1n+u, R.ring.size(o), ew) : {Nat.is_le(Nat.sub(i, _), R.ring.size(o)) == True{} : Bool}
  UO.nat_le_trans(Nat.sub(i, 1n+u), Nat.sub(i, u), R.ring.size(o), nat.sub_succ_le(i, u), inv.p3(o, i, u, h))

def inv.pop_wrap(+o: Nat, +i: Nat, +u: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ew: {Nat.is_eq(1n+u, R.ring.size(o)) == True{} : Bool}) -> {R.ring.inv(o, Nat.sub(i, R.ring.size(o)), 0n) == True{} : Bool}:
  inv.mk(o, Nat.sub(i, R.ring.size(o)), 0n, nat.size_pos(o), nat.le_zero(Nat.sub(i, R.ring.size(o))), inv.wrap3(o, i, u, h, ew))

# the length after a pop, with and without the counters dropping
def len.wrapT(+o: Nat, +i: Nat, +u: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ne: {R.ring.empty.test(i, u) == False{} : Bool}, ew: {Nat.is_eq(1n+u, R.ring.size(o)) == True{} : Bool}) -> {1n+Nat.sub(Nat.sub(i, R.ring.size(o)), 0n) == Nat.sub(i, u) : Nat}:
  %Equal.sym(Nat, Nat.sub(Nat.sub(i, R.ring.size(o)), 0n), Nat.sub(i, R.ring.size(o)), nat.sub_zero(Nat.sub(i, R.ring.size(o)))) : {1n+_ == Nat.sub(i, u) : Nat}
  %nat.eq_of(1n+u, R.ring.size(o), ew) : {1n+Nat.sub(i, _) == Nat.sub(i, u) : Nat}
  nat.sub_succ2(i, u, nat.le_ne(u, i, inv.p2(o, i, u, h), ne))

def len.wrapF(+o: Nat, +i: Nat, +u: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ne: {R.ring.empty.test(i, u) == False{} : Bool}) -> {1n+Nat.sub(i, 1n+u) == Nat.sub(i, u) : Nat}:
  nat.sub_succ2(i, u, nat.le_ne(u, i, inv.p2(o, i, u, h), ne))

# A full ring has no free slot; an empty one, length 0

def avail.full(+o: Nat, +i: Nat, +u: Nat, ec: {R.ring.full.test(o, i, u) == True{} : Bool}) -> {Nat.sub(R.ring.size(o), Nat.sub(i, u)) == 0n : Nat}:
  %Equal.sym(Nat, Nat.sub(i, u), R.ring.size(o), nat.eq_of(Nat.sub(i, u), R.ring.size(o), ec)) : {Nat.sub(R.ring.size(o), _) == 0n : Nat}
  nat.sub_self(R.ring.size(o))

def avail.push(+o: Nat, +i: Nat, +u: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ec: {R.ring.full.test(o, i, u) == False{} : Bool}) -> {Nat.sub(R.ring.size(o), Nat.sub(i, u)) == 1n+Nat.sub(R.ring.size(o), Nat.sub(1n+i, u)) : Nat}:
  %Equal.sym(Nat, Nat.sub(1n+i, u), 1n+Nat.sub(i, u), nat.sub_succ(i, u, inv.p2(o, i, u, h))) : {Nat.sub(R.ring.size(o), Nat.sub(i, u)) == 1n+Nat.sub(R.ring.size(o), _) : Nat}
  nat.sub_pred(R.ring.size(o), Nat.sub(i, u), nat.le_ne_succ(Nat.sub(i, u), R.ring.size(o), inv.p3(o, i, u, h), ec))

def len.empty(+i: Nat, +u: Nat, ec: {R.ring.empty.test(i, u) == True{} : Bool}) -> {Nat.sub(i, u) == 0n : Nat}:
  %nat.eq_of(i, u, ec) : {Nat.sub(i, _) == 0n : Nat}
  nat.sub_self(i)

# Push

def pu.valid(c: Bool, +o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, -x: U32, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ec: {R.ring.full.test(o, i, u) == c : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push.go(c, o, i, u, a, x)))) == True{} : Bool}:
  match c:
    case True{}:
      h
    case False{}:
      inv.push(o, i, u, h, ec)

def pu.full(c: Bool, -o: Nat, -i: Nat, -u: Nat, -a: Array<U32>, -x: U32, ec: {R.ring.full.test(o, i, u) == c : Bool}, e: {R.ring.full.test(o, i, u) == True{} : Bool}) -> {R.ring.push.go(c, o, i, u, a, x) == (R.RingBuf{o, i, u, a}, Fail{R.RingFull{}}) : R.RingBuf & Result<&2, &2, R.RingError, Unit>}:
  match c:
    case True{}:
      {==}
    case False{}:
      bool.contra(R.ring.full.test(o, i, u), {R.ring.push.go(False{}, o, i, u, a, x) == (R.RingBuf{o, i, u, a}, Fail{R.RingFull{}}) : R.RingBuf & Result<&2, &2, R.RingError, Unit>}, e, ec)

def pu.room(c: Bool, -o: Nat, -i: Nat, -u: Nat, -a: Array<U32>, -x: U32, ec: {R.ring.full.test(o, i, u) == c : Bool}, e: {R.ring.full.test(o, i, u) == False{} : Bool}) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push.go(c, o, i, u, a, x)) == Done{Unit{}} : Result<&2, &2, R.RingError, Unit>}:
  match c:
    case True{}:
      bool.contra(R.ring.full.test(o, i, u), {Fail{R.RingFull{}} == Done{Unit{}} : Result<&2, &2, R.RingError, Unit>}, ec, e)
    case False{}:
      {==}

def pu.len(c: Bool, +o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, -x: U32, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ec: {R.ring.full.test(o, i, u) == c : Bool}, e: {R.ring.full.test(o, i, u) == False{} : Bool}) -> {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push.go(c, o, i, u, a, x)))) == 1n+Nat.sub(i, u) : Nat}:
  match c:
    case True{}:
      bool.contra(R.ring.full.test(o, i, u), {Nat.sub(i, u) == 1n+Nat.sub(i, u) : Nat}, ec, e)
    case False{}:
      nat.sub_succ(i, u, inv.p2(o, i, u, h))

# Pop

def po.valid.w(w: Bool, +o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, -x: U32, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ne: {R.ring.empty.test(i, u) == False{} : Bool}, ew: {Nat.is_eq(1n+u, R.ring.size(o)) == w : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.wrap(w, o, i, 1n+u, a, x)))) == True{} : Bool}:
  match w:
    case True{}:
      inv.pop_wrap(o, i, u, h, ew)
    case False{}:
      inv.pop_nowrap(o, i, u, h, ne, ew)

def po.valid.r(+o: Nat, +i: Nat, +u: Nat, ax: Array<U32> & U32, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ne: {R.ring.empty.test(i, u) == False{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.read(o, i, u, ax)))) == True{} : Bool}:
  match ax:
    case (a, x):
      po.valid.w(Nat.is_eq(1n+u, R.ring.size(o)), o, i, u, a, x, h, ne, {==})

def po.valid(c: Bool, +o: Nat, +i: Nat, +u: Nat, a: Array<U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ec: {R.ring.empty.test(i, u) == c : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(c, o, i, u, a)))) == True{} : Bool}:
  match c:
    case True{}:
      h
    case False{}:
      po.valid.r(o, i, u, Array.get(U32, a, U32.from_nat(u)), h, ec)

def po.empty(c: Bool, -o: Nat, -i: Nat, -u: Nat, -a: Array<U32>, ec: {R.ring.empty.test(i, u) == c : Bool}, e: {R.ring.empty.test(i, u) == True{} : Bool}) -> {R.ring.pop.go(c, o, i, u, a) == (R.RingBuf{o, i, u, a}, Fail{R.RingEmpty{}}) : R.RingBuf & Result<&2, &2, R.RingError, U32>}:
  match c:
    case True{}:
      {==}
    case False{}:
      bool.contra(R.ring.empty.test(i, u), {R.ring.pop.go(False{}, o, i, u, a) == (R.RingBuf{o, i, u, a}, Fail{R.RingEmpty{}}) : R.RingBuf & Result<&2, &2, R.RingError, U32>}, e, ec)

def po.done.w(w: Bool, -o: Nat, -i: Nat, -u1: Nat, -a: Array<U32>, -x: U32) -> {Result.is_done(&2, &2, R.RingError, U32, Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.wrap(w, o, i, u1, a, x))) == True{} : Bool}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def po.done.r(+o: Nat, -i: Nat, +u: Nat, ax: Array<U32> & U32) -> {Result.is_done(&2, &2, R.RingError, U32, Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.read(o, i, u, ax))) == True{} : Bool}:
  match ax:
    case (a, x):
      po.done.w(Nat.is_eq(1n+u, R.ring.size(o)), o, i, 1n+u, a, x)

def po.done(c: Bool, +o: Nat, -i: Nat, +u: Nat, a: Array<U32>, ec: {R.ring.empty.test(i, u) == c : Bool}, e: {R.ring.empty.test(i, u) == False{} : Bool}) -> {Result.is_done(&2, &2, R.RingError, U32, Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(c, o, i, u, a))) == True{} : Bool}:
  match c:
    case True{}:
      bool.contra(R.ring.empty.test(i, u), {False{} == True{} : Bool}, ec, e)
    case False{}:
      po.done.r(o, i, u, Array.get(U32, a, U32.from_nat(u)))

def po.len.w(w: Bool, +o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, -x: U32, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ne: {R.ring.empty.test(i, u) == False{} : Bool}, ew: {Nat.is_eq(1n+u, R.ring.size(o)) == w : Bool}) -> {1n+Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.wrap(w, o, i, 1n+u, a, x)))) == Nat.sub(i, u) : Nat}:
  match w:
    case True{}:
      len.wrapT(o, i, u, h, ne, ew)
    case False{}:
      len.wrapF(o, i, u, h, ne)

def po.len.r(+o: Nat, +i: Nat, +u: Nat, ax: Array<U32> & U32, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ne: {R.ring.empty.test(i, u) == False{} : Bool}) -> {1n+Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.read(o, i, u, ax)))) == Nat.sub(i, u) : Nat}:
  match ax:
    case (a, x):
      po.len.w(Nat.is_eq(1n+u, R.ring.size(o)), o, i, u, a, x, h, ne, {==})

def po.len(c: Bool, +o: Nat, +i: Nat, +u: Nat, a: Array<U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ec: {R.ring.empty.test(i, u) == c : Bool}, e: {R.ring.empty.test(i, u) == False{} : Bool}) -> {1n+Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(c, o, i, u, a)))) == Nat.sub(i, u) : Nat}:
  match c:
    case True{}:
      bool.contra(R.ring.empty.test(i, u), {1n+Nat.sub(i, u) == Nat.sub(i, u) : Nat}, ec, e)
    case False{}:
      po.len.r(o, i, u, Array.get(U32, a, U32.from_nat(u)), h, e)

# Peek

def pk.pop.w(w: Bool, -o: Nat, -i: Nat, -u1: Nat, -a: Array<U32>, -x: U32) -> {Done{x} == Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.wrap(w, o, i, u1, a, x)) : Result<&2, &2, R.RingError, U32>}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def pk.pop.r(+o: Nat, -i: Nat, +u: Nat, ax: Array<U32> & U32) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.read(o, i, u, ax)) == Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.read(o, i, u, ax)) : Result<&2, &2, R.RingError, U32>}:
  match ax:
    case (a, x):
      pk.pop.w(Nat.is_eq(1n+u, R.ring.size(o)), o, i, 1n+u, a, x)

def pk.pop(c: Bool, +o: Nat, -i: Nat, +u: Nat, a: Array<U32>) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.go(c, o, i, u, a)) == Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(c, o, i, u, a)) : Result<&2, &2, R.RingError, U32>}:
  match c:
    case True{}:
      {==}
    case False{}:
      pk.pop.r(o, i, u, Array.get(U32, a, U32.from_nat(u)))

def pk.empty(c: Bool, -o: Nat, -i: Nat, -u: Nat, -a: Array<U32>, ec: {R.ring.empty.test(i, u) == c : Bool}, e: {R.ring.empty.test(i, u) == True{} : Bool}) -> {R.ring.peek.go(c, o, i, u, a) == (R.RingBuf{o, i, u, a}, Fail{R.RingEmpty{}}) : R.RingBuf & Result<&2, &2, R.RingError, U32>}:
  match c:
    case True{}:
      {==}
    case False{}:
      bool.contra(R.ring.empty.test(i, u), {R.ring.peek.go(False{}, o, i, u, a) == (R.RingBuf{o, i, u, a}, Fail{R.RingEmpty{}}) : R.RingBuf & Result<&2, &2, R.RingError, U32>}, e, ec)

def pk.valid.r(+o: Nat, +i: Nat, +u: Nat, ax: Array<U32> & U32, h: {R.ring.inv(o, i, u) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.read(o, i, u, ax)))) == True{} : Bool}:
  match ax:
    case (a, x):
      h

def pk.valid(c: Bool, +o: Nat, +i: Nat, +u: Nat, a: Array<U32>, h: {R.ring.inv(o, i, u) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.go(c, o, i, u, a)))) == True{} : Bool}:
  match c:
    case True{}:
      h
    case False{}:
      pk.valid.r(o, i, u, Array.get(U32, a, U32.from_nat(u)), h)

def pk.len.r(+o: Nat, +i: Nat, +u: Nat, ax: Array<U32> & U32) -> {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.read(o, i, u, ax)))) == Nat.sub(i, u) : Nat}:
  match ax:
    case (a, x):
      {==}

def pk.len(c: Bool, +o: Nat, +i: Nat, +u: Nat, a: Array<U32>) -> {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.go(c, o, i, u, a)))) == Nat.sub(i, u) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      pk.len.r(o, i, u, Array.get(U32, a, U32.from_nat(u)))

# Batches: push_list

def bp.count.h(c: Bool, +t: List<&2, U32>, +o: Nat, +i: Nat, +u: Nat, +ec: {R.ring.full.test(o, i, u) == c : Bool}, a: Array<U32>, x: U32, +n: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ih: @i2: Nat -> @a2: Array<U32> -> @n2: Nat -> @h2: {R.ring.inv(o, i2, u) == True{} : Bool} -> {Pair.snd(R.RingBuf, Nat, R.ring.push_list.go(t, (R.RingBuf{o, i2, u, a2}, n2))) == Nat.add(n2, Nat.min(List.length(&2, U32, t), Nat.sub(R.ring.size(o), Nat.sub(i2, u)))) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.push_list.go(t, R.ring.push_list.count(R.ring.push.go(c, o, i, u, a, x), n))) == Nat.add(n, Nat.min(1n+List.length(&2, U32, t), Nat.sub(R.ring.size(o), Nat.sub(i, u)))) : Nat}:
  match c:
    case True{}:
      +lt = List.length(&2, U32, t)
      +av = Nat.sub(R.ring.size(o), Nat.sub(i, u))
      +ez = avail.full(o, i, u, ec)
      %Equal.sym(Nat, av, 0n, ez) : {Pair.snd(R.RingBuf, Nat, R.ring.push_list.go(t, (R.RingBuf{o, i, u, a}, n))) == Nat.add(n, Nat.min(1n+lt, _)) : Nat}
      %Equal.sym(Nat, Pair.snd(R.RingBuf, Nat, R.ring.push_list.go(t, (R.RingBuf{o, i, u, a}, n))), Nat.add(n, Nat.min(lt, av)), ih(i, a, n, h)) : {_ == Nat.add(n, 0n) : Nat}
      %Equal.sym(Nat, av, 0n, ez) : {Nat.add(n, Nat.min(lt, _)) == Nat.add(n, 0n) : Nat}
      %Equal.sym(Nat, Nat.min(lt, 0n), 0n, nat.min_zero_r(lt)) : {Nat.add(n, _) == Nat.add(n, 0n) : Nat}
      {==}
    case False{}:
      +lt = List.length(&2, U32, t)
      +av2 = Nat.sub(R.ring.size(o), Nat.sub(1n+i, u))
      %Equal.sym(Nat, Nat.sub(R.ring.size(o), Nat.sub(i, u)), 1n+av2, avail.push(o, i, u, h, ec)) : {Pair.snd(R.RingBuf, Nat, R.ring.push_list.go(t, (R.RingBuf{o, 1n+i, u, Array.set(U32, a, U32.from_nat(i), x)}, 1n+n))) == Nat.add(n, Nat.min(1n+lt, _)) : Nat}
      %Equal.sym(Nat, Nat.add(n, 1n+Nat.min(lt, av2)), 1n+Nat.add(n, Nat.min(lt, av2)), UL.nat_add_succ(n, Nat.min(lt, av2))) : {Pair.snd(R.RingBuf, Nat, R.ring.push_list.go(t, (R.RingBuf{o, 1n+i, u, Array.set(U32, a, U32.from_nat(i), x)}, 1n+n))) == _ : Nat}
      ih(1n+i, Array.set(U32, a, U32.from_nat(i), x), 1n+n, inv.push(o, i, u, h, ec))

def bp.count(xs: List<&2, U32>, +o: Nat, +i: Nat, +u: Nat, a: Array<U32>, +n: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Nat, R.ring.push_list.go(xs, (R.RingBuf{o, i, u, a}, n))) == Nat.add(n, Nat.min(List.length(&2, U32, xs), Nat.sub(R.ring.size(o), Nat.sub(i, u)))) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, Nat.add(n, 0n), n, UL.nat_add_zero(n))
    case Con{x, +t}:
      bp.count.h(R.ring.full.test(o, i, u), t, o, i, u, {==}, a, x, n, h, i2 => a2 => n2 => h2 => bp.count(t, o, i2, u, a2, n2, h2))

def bp.valid.h(c: Bool, -t: List<&2, U32>, +o: Nat, +i: Nat, +u: Nat, +ec: {R.ring.full.test(o, i, u) == c : Bool}, a: Array<U32>, x: U32, +n: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ih: @i2: Nat -> @a2: Array<U32> -> @n2: Nat -> @h2: {R.ring.inv(o, i2, u) == True{} : Bool} -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(t, (R.RingBuf{o, i2, u, a2}, n2))))) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(t, R.ring.push_list.count(R.ring.push.go(c, o, i, u, a, x), n))))) == True{} : Bool}:
  match c:
    case True{}:
      ih(i, a, n, h)
    case False{}:
      ih(1n+i, Array.set(U32, a, U32.from_nat(i), x), 1n+n, inv.push(o, i, u, h, ec))

def bp.valid(xs: List<&2, U32>, +o: Nat, +i: Nat, +u: Nat, a: Array<U32>, +n: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(xs, (R.RingBuf{o, i, u, a}, n))))) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{x, +t}:
      bp.valid.h(R.ring.full.test(o, i, u), t, o, i, u, {==}, a, x, n, h, i2 => a2 => n2 => h2 => bp.valid(t, o, i2, u, a2, n2, h2))

# Batches: pop_list

def bo.count.w(w: Bool, +k: Nat, +o: Nat, +i: Nat, +u: Nat, +ew: {Nat.is_eq(1n+u, R.ring.size(o)) == w : Bool}, a: Array<U32>, +x: U32, +acc: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ne: {R.ring.empty.test(i, u) == False{} : Bool}, ih: @i2: Nat -> @u2: Nat -> @a2: Array<U32> -> @acc2: List<&2, U32> -> @h2: {R.ring.inv(o, i2, u2) == True{} : Bool} -> {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (R.RingBuf{o, i2, u2, a2}, acc2)))) == Nat.add(List.length(&2, U32, acc2), Nat.min(k, Nat.sub(i2, u2))) : Nat}) -> {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.wrap(w, o, i, 1n+u, a, x), acc)))) == Nat.add(List.length(&2, U32, acc), Nat.min(1n+k, Nat.sub(i, u))) : Nat}:
  match w:
    case True{}:
      +la = List.length(&2, U32, acc)
      +acc2 = List.append(&2, U32, acc, Con{x, Nil{}})
      +l2 = Nat.sub(Nat.sub(i, R.ring.size(o)), 0n)
      %len.wrapT(o, i, u, h, ne, ew) : {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (R.RingBuf{o, Nat.sub(i, R.ring.size(o)), 0n, a}, acc2)))) == Nat.add(la, Nat.min(1n+k, _)) : Nat}
      %Equal.sym(Nat, Nat.add(la, 1n+Nat.min(k, l2)), 1n+Nat.add(la, Nat.min(k, l2)), UL.nat_add_succ(la, Nat.min(k, l2))) : {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (R.RingBuf{o, Nat.sub(i, R.ring.size(o)), 0n, a}, acc2)))) == _ : Nat}
      %list.len_snoc(acc, x) : {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (R.RingBuf{o, Nat.sub(i, R.ring.size(o)), 0n, a}, acc2)))) == Nat.add(_, Nat.min(k, l2)) : Nat}
      ih(Nat.sub(i, R.ring.size(o)), 0n, a, acc2, inv.pop_wrap(o, i, u, h, ew))
    case False{}:
      +la = List.length(&2, U32, acc)
      +acc2 = List.append(&2, U32, acc, Con{x, Nil{}})
      +l2 = Nat.sub(i, 1n+u)
      %len.wrapF(o, i, u, h, ne) : {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (R.RingBuf{o, i, 1n+u, a}, acc2)))) == Nat.add(la, Nat.min(1n+k, _)) : Nat}
      %Equal.sym(Nat, Nat.add(la, 1n+Nat.min(k, l2)), 1n+Nat.add(la, Nat.min(k, l2)), UL.nat_add_succ(la, Nat.min(k, l2))) : {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (R.RingBuf{o, i, 1n+u, a}, acc2)))) == _ : Nat}
      %list.len_snoc(acc, x) : {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (R.RingBuf{o, i, 1n+u, a}, acc2)))) == Nat.add(_, Nat.min(k, l2)) : Nat}
      ih(i, 1n+u, a, acc2, inv.pop_nowrap(o, i, u, h, ne, ew))

def bo.count.r(+k: Nat, +o: Nat, +i: Nat, +u: Nat, ax: Array<U32> & U32, +acc: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ne: {R.ring.empty.test(i, u) == False{} : Bool}, ih: @i2: Nat -> @u2: Nat -> @a2: Array<U32> -> @acc2: List<&2, U32> -> @h2: {R.ring.inv(o, i2, u2) == True{} : Bool} -> {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (R.RingBuf{o, i2, u2, a2}, acc2)))) == Nat.add(List.length(&2, U32, acc2), Nat.min(k, Nat.sub(i2, u2))) : Nat}) -> {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.read(o, i, u, ax), acc)))) == Nat.add(List.length(&2, U32, acc), Nat.min(1n+k, Nat.sub(i, u))) : Nat}:
  match ax:
    case (a, x):
      bo.count.w(Nat.is_eq(1n+u, R.ring.size(o)), k, o, i, u, {==}, a, x, acc, h, ne, ih)

def bo.count.h(c: Bool, +k: Nat, +o: Nat, +i: Nat, +u: Nat, +ec: {R.ring.empty.test(i, u) == c : Bool}, a: Array<U32>, +acc: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ih: @i2: Nat -> @u2: Nat -> @a2: Array<U32> -> @acc2: List<&2, U32> -> @h2: {R.ring.inv(o, i2, u2) == True{} : Bool} -> {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (R.RingBuf{o, i2, u2, a2}, acc2)))) == Nat.add(List.length(&2, U32, acc2), Nat.min(k, Nat.sub(i2, u2))) : Nat}) -> {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.go(c, o, i, u, a), acc)))) == Nat.add(List.length(&2, U32, acc), Nat.min(1n+k, Nat.sub(i, u))) : Nat}:
  match c:
    case True{}:
      +la = List.length(&2, U32, acc)
      +ln = Nat.sub(i, u)
      +ez = len.empty(i, u, ec)
      %Equal.sym(Nat, ln, 0n, ez) : {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (R.RingBuf{o, i, u, a}, acc)))) == Nat.add(la, Nat.min(1n+k, _)) : Nat}
      %Equal.sym(Nat, List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (R.RingBuf{o, i, u, a}, acc)))), Nat.add(la, Nat.min(k, ln)), ih(i, u, a, acc, h)) : {_ == Nat.add(la, 0n) : Nat}
      %Equal.sym(Nat, ln, 0n, ez) : {Nat.add(la, Nat.min(k, _)) == Nat.add(la, 0n) : Nat}
      %Equal.sym(Nat, Nat.min(k, 0n), 0n, nat.min_zero_r(k)) : {Nat.add(la, _) == Nat.add(la, 0n) : Nat}
      {==}
    case False{}:
      bo.count.r(k, o, i, u, Array.get(U32, a, U32.from_nat(u)), acc, h, ec, ih)

def bo.count(n: Nat, +o: Nat, +i: Nat, +u: Nat, a: Array<U32>, +acc: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}) -> {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(n, (R.RingBuf{o, i, u, a}, acc)))) == Nat.add(List.length(&2, U32, acc), Nat.min(n, Nat.sub(i, u))) : Nat}:
  match n:
    case 0n:
      Equal.sym(Nat, Nat.add(List.length(&2, U32, acc), 0n), List.length(&2, U32, acc), UL.nat_add_zero(List.length(&2, U32, acc)))
    case 1n+ +k:
      bo.count.h(R.ring.empty.test(i, u), k, o, i, u, {==}, a, acc, h, i2 => u2 => a2 => acc2 => h2 => bo.count(k, o, i2, u2, a2, acc2, h2))

def bo.valid.w(w: Bool, -k: Nat, +o: Nat, +i: Nat, +u: Nat, +ew: {Nat.is_eq(1n+u, R.ring.size(o)) == w : Bool}, a: Array<U32>, +x: U32, +acc: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ne: {R.ring.empty.test(i, u) == False{} : Bool}, ih: @i2: Nat -> @u2: Nat -> @a2: Array<U32> -> @acc2: List<&2, U32> -> @h2: {R.ring.inv(o, i2, u2) == True{} : Bool} -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (R.RingBuf{o, i2, u2, a2}, acc2))))) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.wrap(w, o, i, 1n+u, a, x), acc))))) == True{} : Bool}:
  match w:
    case True{}:
      ih(Nat.sub(i, R.ring.size(o)), 0n, a, List.append(&2, U32, acc, Con{x, Nil{}}), inv.pop_wrap(o, i, u, h, ew))
    case False{}:
      ih(i, 1n+u, a, List.append(&2, U32, acc, Con{x, Nil{}}), inv.pop_nowrap(o, i, u, h, ne, ew))

def bo.valid.r(-k: Nat, +o: Nat, +i: Nat, +u: Nat, ax: Array<U32> & U32, +acc: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ne: {R.ring.empty.test(i, u) == False{} : Bool}, ih: @i2: Nat -> @u2: Nat -> @a2: Array<U32> -> @acc2: List<&2, U32> -> @h2: {R.ring.inv(o, i2, u2) == True{} : Bool} -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (R.RingBuf{o, i2, u2, a2}, acc2))))) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.read(o, i, u, ax), acc))))) == True{} : Bool}:
  match ax:
    case (a, x):
      bo.valid.w(Nat.is_eq(1n+u, R.ring.size(o)), k, o, i, u, {==}, a, x, acc, h, ne, ih)

def bo.valid.h(c: Bool, -k: Nat, +o: Nat, +i: Nat, +u: Nat, +ec: {R.ring.empty.test(i, u) == c : Bool}, a: Array<U32>, +acc: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, ih: @i2: Nat -> @u2: Nat -> @a2: Array<U32> -> @acc2: List<&2, U32> -> @h2: {R.ring.inv(o, i2, u2) == True{} : Bool} -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (R.RingBuf{o, i2, u2, a2}, acc2))))) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.go(c, o, i, u, a), acc))))) == True{} : Bool}:
  match c:
    case True{}:
      ih(i, u, a, acc, h)
    case False{}:
      bo.valid.r(k, o, i, u, Array.get(U32, a, U32.from_nat(u)), acc, h, ec, ih)

def bo.valid(n: Nat, +o: Nat, +i: Nat, +u: Nat, a: Array<U32>, +acc: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(n, (R.RingBuf{o, i, u, a}, acc))))) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+ +k:
      bo.valid.h(R.ring.empty.test(i, u), k, o, i, u, {==}, a, acc, h, i2 => u2 => a2 => acc2 => h2 => bo.valid(k, o, i2, u2, a2, acc2, h2))

# The laws, on a ring taken apart

def l.new_valid(+o: Nat) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(R.ring.new(o))) == True{} : Bool}:
  inv.mk(o, 0n, 0n, nat.size_pos(o), {==}, nat.le_zero(R.ring.size(o)))

def l.len_le(r: R.RingBuf, h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}) -> {Nat.is_le(Pair.snd(R.RingBuf, Nat, R.ring.len(r)), Pair.snd(R.RingBuf, Nat, R.ring.capacity(r))) == True{} : Bool}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      inv.p3(o, i, u, h)

def l.len_avail(r: R.RingBuf, h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}) -> {Nat.add(Pair.snd(R.RingBuf, Nat, R.ring.len(r)), Pair.snd(R.RingBuf, Nat, R.ring.avail(r))) == Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) : Nat}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      nat.add_sub(Nat.sub(i, u), R.ring.size(o), inv.p3(o, i, u, h))

def l.empty_iff(r: R.RingBuf, h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.is_empty(r)) == Nat.is_eq(Pair.snd(R.RingBuf, Nat, R.ring.len(r)), 0n) : Bool}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      nat.eq_sub(i, u, inv.p2(o, i, u, h))

def l.full_iff(r: R.RingBuf, h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.is_full(r)) == Nat.is_eq(Pair.snd(R.RingBuf, Nat, R.ring.avail(r)), 0n) : Bool}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      nat.eq_sub_rev(Nat.sub(i, u), R.ring.size(o), inv.p3(o, i, u, h))

def l.push_valid(r: R.RingBuf, -x: U32, h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(r, x)))) == True{} : Bool}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      pu.valid(R.ring.full.test(o, i, u), o, i, u, a, x, h, {==})

def l.push_full(r: R.RingBuf, -x: U32, e: {Pair.snd(R.RingBuf, Bool, R.ring.is_full(r)) == True{} : Bool}) -> {R.ring.push(r, x) == (r, Fail{R.RingFull{}}) : R.RingBuf & Result<&2, &2, R.RingError, Unit>}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      pu.full(R.ring.full.test(o, i, u), o, i, u, a, x, {==}, e)

def l.push_room(r: R.RingBuf, -x: U32, e: {Pair.snd(R.RingBuf, Bool, R.ring.is_full(r)) == False{} : Bool}) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(r, x)) == Done{Unit{}} : Result<&2, &2, R.RingError, Unit>}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      pu.room(R.ring.full.test(o, i, u), o, i, u, a, x, {==}, e)

def l.push_len(r: R.RingBuf, -x: U32, h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}, e: {Pair.snd(R.RingBuf, Bool, R.ring.is_full(r)) == False{} : Bool}) -> {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(r, x)))) == 1n+Pair.snd(R.RingBuf, Nat, R.ring.len(r)) : Nat}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      pu.len(R.ring.full.test(o, i, u), o, i, u, a, x, h, {==}, e)

def l.pop_valid(r: R.RingBuf, h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r)))) == True{} : Bool}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      po.valid(R.ring.empty.test(i, u), o, i, u, a, h, {==})

def l.pop_empty(r: R.RingBuf, e: {Pair.snd(R.RingBuf, Bool, R.ring.is_empty(r)) == True{} : Bool}) -> {R.ring.pop(r) == (r, Fail{R.RingEmpty{}}) : R.RingBuf & Result<&2, &2, R.RingError, U32>}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      po.empty(R.ring.empty.test(i, u), o, i, u, a, {==}, e)

def l.pop_done(r: R.RingBuf, e: {Pair.snd(R.RingBuf, Bool, R.ring.is_empty(r)) == False{} : Bool}) -> {Result.is_done(&2, &2, R.RingError, U32, Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r))) == True{} : Bool}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      po.done(R.ring.empty.test(i, u), o, i, u, a, {==}, e)

def l.pop_len(r: R.RingBuf, h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}, e: {Pair.snd(R.RingBuf, Bool, R.ring.is_empty(r)) == False{} : Bool}) -> {1n+Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r)))) == Pair.snd(R.RingBuf, Nat, R.ring.len(r)) : Nat}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      po.len(R.ring.empty.test(i, u), o, i, u, a, h, {==}, e)

def l.peek_is_pop(r: R.RingBuf) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(r)) == Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r)) : Result<&2, &2, R.RingError, U32>}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      pk.pop(R.ring.empty.test(i, u), o, i, u, a)

def l.peek_empty(r: R.RingBuf, e: {Pair.snd(R.RingBuf, Bool, R.ring.is_empty(r)) == True{} : Bool}) -> {R.ring.peek(r) == (r, Fail{R.RingEmpty{}}) : R.RingBuf & Result<&2, &2, R.RingError, U32>}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      pk.empty(R.ring.empty.test(i, u), o, i, u, a, {==}, e)

def l.peek_valid(r: R.RingBuf, h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(r)))) == True{} : Bool}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      pk.valid(R.ring.empty.test(i, u), o, i, u, a, h)

def l.peek_len(r: R.RingBuf) -> {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(r)))) == Pair.snd(R.RingBuf, Nat, R.ring.len(r)) : Nat}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      pk.len(R.ring.empty.test(i, u), o, i, u, a)

def l.push_list_valid(r: R.RingBuf, xs: List<&2, U32>, h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Nat, R.ring.push_list(r, xs)))) == True{} : Bool}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      bp.valid(xs, o, i, u, a, 0n, h)

def l.push_list_count(r: R.RingBuf, xs: List<&2, U32>, h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Nat, R.ring.push_list(r, xs)) == Nat.min(List.length(&2, U32, xs), Pair.snd(R.RingBuf, Nat, R.ring.avail(r))) : Nat}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      bp.count(xs, o, i, u, a, 0n, h)

def l.pop_list_valid(r: R.RingBuf, n: Nat, h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(r, n)))) == True{} : Bool}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      bo.valid(n, o, i, u, a, Nil{}, h)

def l.pop_list_count(r: R.RingBuf, n: Nat, h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}) -> {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list(r, n))) == Nat.min(n, Pair.snd(R.RingBuf, Nat, R.ring.len(r))) : Nat}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      bo.count(n, o, i, u, a, Nil{}, h)

# The laws

def Laws.new_valid(o):
  l.new_valid(o)

def Laws.new_empty(o):
  {==}

def Laws.new_capacity(o):
  {==}

def Laws.len_le_capacity(r, h):
  l.len_le(r, h)

def Laws.len_avail(r, h):
  l.len_avail(r, h)

def Laws.empty_iff(r, h):
  l.empty_iff(r, h)

def Laws.full_iff(r, h):
  l.full_iff(r, h)

def Laws.push_valid(r, x, h):
  l.push_valid(r, x, h)

def Laws.push_full(r, x, e):
  l.push_full(r, x, e)

def Laws.push_room(r, x, e):
  l.push_room(r, x, e)

def Laws.push_len(r, x, h, e):
  l.push_len(r, x, h, e)

def Laws.pop_valid(r, h):
  l.pop_valid(r, h)

def Laws.pop_empty(r, e):
  l.pop_empty(r, e)

def Laws.pop_done(r, e):
  l.pop_done(r, e)

def Laws.pop_len(r, h, e):
  l.pop_len(r, h, e)

def Laws.peek_is_pop(r):
  l.peek_is_pop(r)

def Laws.peek_empty(r, e):
  l.peek_empty(r, e)

def Laws.peek_valid(r, h):
  l.peek_valid(r, h)

def Laws.peek_len(r):
  l.peek_len(r)

def Laws.push_list_valid(r, xs, h):
  l.push_list_valid(r, xs, h)

def Laws.push_list_count(r, xs, h):
  l.push_list_count(r, xs, h)

def Laws.pop_list_valid(r, n, h):
  l.pop_list_valid(r, n, h)

def Laws.pop_list_count(r, n, h):
  l.pop_list_count(r, n, h)

def Laws.fifo_fill(a, b, c, d):
  {==}

def Laws.fifo_wrap(a, b, c, d):
  {==}

def Laws.fifo_wrap8(a, b, c):
  {==}

def Laws.fifo_full(a, b, c, d, e):
  {==}

def Laws.fifo_interleaved(a, b, c):
  {==}

def Laws.vec_default_capacity():
  {==}

def Laws.vec_pop_new():
  {==}

# Lists and Nat, for the model

def nat.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def nat.succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, n => nat.pred(n), 1n+a, 1n+b, e)

def nat.min_le(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({0n == 1n+ap : Nat}, absurd.ft(e))
    case 1n+ +ap 1n+ +bp:
      %nat.min_le(ap, bp, e) : {1n+Nat.min(ap, bp) == 1n+_ : Nat}
      {==}

def nat.min_le_l(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      nat.min_le_l(ap, bp)

def nat.min_le_r(a: Nat, b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n +bb:
      nat.le_zero(bb)
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      nat.min_le_r(ap, bp)

# l <= c and k <= c - l: l + k <= c
def nat.add_le_sub(l: Nat, -k: Nat, c: Nat, e: {Nat.is_le(l, c) == True{} : Bool}, f: {Nat.is_le(k, Nat.sub(c, l)) == True{} : Bool}) -> {Nat.is_le(Nat.add(l, k), c) == True{} : Bool}:
  match l c:
    case 0n +cc:
      %nat.sub_zero(cc) : {Nat.is_le(k, _) == True{} : Bool}
      f
    case 1n+lp 0n:
      Empty.absurd({Nat.is_le(1n+Nat.add(lp, k), 0n) == True{} : Bool}, absurd.ft(e))
    case 1n+lp 1n+cp:
      nat.add_le_sub(lp, k, cp, e, f)

def list.take_all(xs: List<&2, U32>) -> {List.take(&2, U32, xs, List.length(&2, U32, xs)) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %list.take_all(t) : {Con{h, List.take(&2, U32, t, List.length(&2, U32, t))} == Con{h, _} : List<&2, U32>}
      {==}

def list.length_take(xs: List<&2, U32>, n: Nat) -> {List.length(&2, U32, List.take(&2, U32, xs, n)) == Nat.min(n, List.length(&2, U32, xs)) : Nat}:
  match xs n:
    case Nil{} +nn:
      Equal.sym(Nat, Nat.min(nn, 0n), 0n, nat.min_zero_r(nn))
    case Con{h, t} 0n:
      {==}
    case Con{h, +t} 1n+ +p:
      %list.length_take(t, p) : {1n+List.length(&2, U32, List.take(&2, U32, t, p)) == 1n+_ : Nat}
      {==}

def list.length_drop_le(xs: List<&2, U32>, n: Nat) -> {Nat.is_le(List.length(&2, U32, List.drop(&2, U32, xs, n)), List.length(&2, U32, xs)) == True{} : Bool}:
  match xs n:
    case Nil{} _:
      {==}
    case Con{h, +t} 0n:
      UL.nat_le_refl(List.length(&2, U32, t))
    case Con{h, +t} 1n+ +p:
      +lt = List.length(&2, U32, t)
      UO.nat_le_trans(List.length(&2, U32, List.drop(&2, U32, t, p)), lt, 1n+lt, list.length_drop_le(t, p), nat.le_succ(lt, lt, UL.nat_le_refl(lt)))

def list.length_append(a: List<&2, U32>, +b: List<&2, U32>) -> {List.length(&2, U32, List.append(&2, U32, a, b)) == Nat.add(List.length(&2, U32, a), List.length(&2, U32, b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{h, +t}:
      %list.length_append(t, b) : {1n+List.length(&2, U32, List.append(&2, U32, t, b)) == 1n+_ : Nat}
      {==}

# The model

def mo.push_items(c: Bool, -cap: Nat, -items: List<&2, U32>, -x: U32, ec: {Nat.is_eq(List.length(&2, U32, items), cap) == c : Bool}, e: {Nat.is_eq(List.length(&2, U32, items), cap) == False{} : Bool}) -> {M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(c, cap, items, x))) == List.append(&2, U32, items, Con{x, Nil{}}) : List<&2, U32>}:
  match c:
    case True{}:
      bool.contra(Nat.is_eq(List.length(&2, U32, items), cap), {M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(True{}, cap, items, x))) == List.append(&2, U32, items, Con{x, Nil{}}) : List<&2, U32>}, ec, e)
    case False{}:
      {==}

def mo.push_done(c: Bool, -cap: Nat, -items: List<&2, U32>, -x: U32, ec: {Nat.is_eq(List.length(&2, U32, items), cap) == c : Bool}, e: {Nat.is_eq(List.length(&2, U32, items), cap) == False{} : Bool}) -> {Pair.snd(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(c, cap, items, x)) == Done{Unit{}} : Result<&2, &2, R.RingError, Unit>}:
  match c:
    case True{}:
      bool.contra(Nat.is_eq(List.length(&2, U32, items), cap), {Pair.snd(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(True{}, cap, items, x)) == Done{Unit{}} : Result<&2, &2, R.RingError, Unit>}, ec, e)
    case False{}:
      {==}

def mo.push_full(c: Bool, -cap: Nat, -items: List<&2, U32>, -x: U32, ec: {Nat.is_eq(List.length(&2, U32, items), cap) == c : Bool}, e: {Nat.is_eq(List.length(&2, U32, items), cap) == True{} : Bool}) -> {M.model.push.go(c, cap, items, x) == (M.RingModel{cap, items}, Fail{R.RingFull{}}) : M.RingModel & Result<&2, &2, R.RingError, Unit>}:
  match c:
    case True{}:
      {==}
    case False{}:
      bool.contra(Nat.is_eq(List.length(&2, U32, items), cap), {M.model.push.go(False{}, cap, items, x) == (M.RingModel{cap, items}, Fail{R.RingFull{}}) : M.RingModel & Result<&2, &2, R.RingError, Unit>}, e, ec)

def mo.push_valid(c: Bool, +cap: Nat, +items: List<&2, U32>, -x: U32, +h: {Nat.is_le(List.length(&2, U32, items), cap) == True{} : Bool}, ec: {Nat.is_eq(List.length(&2, U32, items), cap) == c : Bool}) -> {M.model.valid(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(c, cap, items, x))) == True{} : Bool}:
  match c:
    case True{}:
      h
    case False{}:
      %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, items, Con{x, Nil{}})), 1n+List.length(&2, U32, items), list.len_snoc(items, x)) : {Nat.is_le(_, cap) == True{} : Bool}
      nat.le_ne_succ(List.length(&2, U32, items), cap, h, ec)

def mo.push_list(m: M.RingModel, +xs: List<&2, U32>, h: {M.model.valid(m) == True{} : Bool}, l: {Nat.is_le(List.length(&2, U32, xs), M.model.avail(m)) == True{} : Bool}) -> {M.model.items(Pair.fst(M.RingModel, Nat, M.model.push_list(m, xs))) == List.append(&2, U32, M.model.items(m), xs) : List<&2, U32>}:
  match m:
    case M.RingModel{+cap, +items}:
      %Equal.sym(Nat, Nat.min(List.length(&2, U32, xs), Nat.sub(cap, List.length(&2, U32, items))), List.length(&2, U32, xs), nat.min_le(List.length(&2, U32, xs), Nat.sub(cap, List.length(&2, U32, items)), l)) : {List.append(&2, U32, items, List.take(&2, U32, xs, _)) == List.append(&2, U32, items, xs) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.take(&2, U32, xs, List.length(&2, U32, xs)), xs, list.take_all(xs)) : {List.append(&2, U32, items, _) == List.append(&2, U32, items, xs) : List<&2, U32>}
      {==}

def mo.push_list_valid(m: M.RingModel, +xs: List<&2, U32>, h: {M.model.valid(m) == True{} : Bool}) -> {M.model.valid(Pair.fst(M.RingModel, Nat, M.model.push_list(m, xs))) == True{} : Bool}:
  match m:
    case M.RingModel{+cap, +items}:
      %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, items, List.take(&2, U32, xs, Nat.min(List.length(&2, U32, xs), Nat.sub(cap, List.length(&2, U32, items)))))), Nat.add(List.length(&2, U32, items), List.length(&2, U32, List.take(&2, U32, xs, Nat.min(List.length(&2, U32, xs), Nat.sub(cap, List.length(&2, U32, items)))))), list.length_append(items, List.take(&2, U32, xs, Nat.min(List.length(&2, U32, xs), Nat.sub(cap, List.length(&2, U32, items)))))) : {Nat.is_le(_, cap) == True{} : Bool}
      %Equal.sym(Nat, List.length(&2, U32, List.take(&2, U32, xs, Nat.min(List.length(&2, U32, xs), Nat.sub(cap, List.length(&2, U32, items))))), Nat.min(Nat.min(List.length(&2, U32, xs), Nat.sub(cap, List.length(&2, U32, items))), List.length(&2, U32, xs)), list.length_take(xs, Nat.min(List.length(&2, U32, xs), Nat.sub(cap, List.length(&2, U32, items))))) : {Nat.is_le(Nat.add(List.length(&2, U32, items), _), cap) == True{} : Bool}
      nat.add_le_sub(List.length(&2, U32, items), Nat.min(Nat.min(List.length(&2, U32, xs), Nat.sub(cap, List.length(&2, U32, items))), List.length(&2, U32, xs)), cap, h, UO.nat_le_trans(Nat.min(Nat.min(List.length(&2, U32, xs), Nat.sub(cap, List.length(&2, U32, items))), List.length(&2, U32, xs)), Nat.min(List.length(&2, U32, xs), Nat.sub(cap, List.length(&2, U32, items))), Nat.sub(cap, List.length(&2, U32, items)), nat.min_le_l(Nat.min(List.length(&2, U32, xs), Nat.sub(cap, List.length(&2, U32, items))), List.length(&2, U32, xs)), nat.min_le_r(List.length(&2, U32, xs), Nat.sub(cap, List.length(&2, U32, items)))))

def mo.pop_list_valid(m: M.RingModel, +n: Nat, h: {M.model.valid(m) == True{} : Bool}) -> {M.model.valid(Pair.fst(M.RingModel, List<&2, U32>, M.model.pop_list(m, n))) == True{} : Bool}:
  match m:
    case M.RingModel{+cap, +items}:
      UO.nat_le_trans(List.length(&2, U32, List.drop(&2, U32, items, n)), List.length(&2, U32, items), cap, list.length_drop_le(items, n), h)

def mo.fifo(m: M.RingModel, +xs: List<&2, U32>, h: {M.model.valid(m) == True{} : Bool}, l: {Nat.is_le(List.length(&2, U32, xs), M.model.avail(m)) == True{} : Bool}) -> {Pair.snd(M.RingModel, List<&2, U32>, M.model.pop_list(Pair.fst(M.RingModel, Nat, M.model.push_list(m, xs)), Nat.add(M.model.len(m), List.length(&2, U32, xs)))) == List.append(&2, U32, M.model.items(m), xs) : List<&2, U32>}:
  match m:
    case M.RingModel{+cap, +items}:
      %Equal.sym(Nat, Nat.min(List.length(&2, U32, xs), Nat.sub(cap, List.length(&2, U32, items))), List.length(&2, U32, xs), nat.min_le(List.length(&2, U32, xs), Nat.sub(cap, List.length(&2, U32, items)), l)) : {List.take(&2, U32, List.append(&2, U32, items, List.take(&2, U32, xs, _)), Nat.add(List.length(&2, U32, items), List.length(&2, U32, xs))) == List.append(&2, U32, items, xs) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.take(&2, U32, xs, List.length(&2, U32, xs)), xs, list.take_all(xs)) : {List.take(&2, U32, List.append(&2, U32, items, _), Nat.add(List.length(&2, U32, items), List.length(&2, U32, xs))) == List.append(&2, U32, items, xs) : List<&2, U32>}
      %list.length_append(items, xs) : {List.take(&2, U32, List.append(&2, U32, items, xs), _) == List.append(&2, U32, items, xs) : List<&2, U32>}
      list.take_all(List.append(&2, U32, items, xs))

# The Array ring against the model

def rl.push(c: Bool, -o: Nat, -i: Nat, -u: Nat, -a: Array<U32>, -x: U32, -cap: Nat, -items: List<&2, U32>) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push.go(c, o, i, u, a, x)) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(c, cap, items, x)) : Result<&2, &2, R.RingError, Unit>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def rl.push_cap(c: Bool, -o: Nat, -i: Nat, -u: Nat, -a: Array<U32>, -x: U32, -items: List<&2, U32>) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push.go(c, o, i, u, a, x)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(c, R.ring.size(o), items, x))) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def rl.push_len(c: Bool, +o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, -x: U32, +items: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +el: {Nat.sub(i, u) == List.length(&2, U32, items) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push.go(c, o, i, u, a, x)))) == M.model.len(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(c, R.ring.size(o), items, x))) : Nat}:
  match c:
    case True{}:
      el
    case False{}:
      %Equal.sym(Nat, Nat.sub(1n+i, u), 1n+Nat.sub(i, u), nat.sub_succ(i, u, inv.p2(o, i, u, h))) : {_ == List.length(&2, U32, List.append(&2, U32, items, Con{x, Nil{}})) : Nat}
      %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, items, Con{x, Nil{}})), 1n+List.length(&2, U32, items), list.len_snoc(items, x)) : {1n+Nat.sub(i, u) == _ : Nat}
      %el : {1n+Nat.sub(i, u) == 1n+_ : Nat}
      {==}

def rl.pop_done(items: List<&2, U32>, +o: Nat, -i: Nat, +u: Nat, a: Array<U32>, -cap: Nat) -> {Result.is_done(&2, &2, R.RingError, U32, Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(Nat.is_eq(List.length(&2, U32, items), 0n), o, i, u, a))) == Result.is_done(&2, &2, R.RingError, U32, Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, items}))) : Bool}:
  match items:
    case Nil{}:
      {==}
    case Con{y, t}:
      po.done.r(o, i, u, Array.get(U32, a, U32.from_nat(u)))

def rl.ne(+o: Nat, +i: Nat, +u: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, -y: U32, -t: List<&2, U32>, el: {Nat.sub(i, u) == List.length(&2, U32, Con{y, t}) : Nat}) -> {R.ring.empty.test(i, u) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(i, u), Nat.is_eq(Nat.sub(i, u), 0n), nat.eq_sub(i, u, inv.p2(o, i, u, h))) : {_ == False{} : Bool}
  %Equal.sym(Nat, Nat.sub(i, u), List.length(&2, U32, Con{y, t}), el) : {Nat.is_eq(_, 0n) == False{} : Bool}
  {==}

def rl.pop_len(items: List<&2, U32>, +o: Nat, +i: Nat, +u: Nat, a: Array<U32>, -cap: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +el: {Nat.sub(i, u) == List.length(&2, U32, items) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(Nat.is_eq(List.length(&2, U32, items), 0n), o, i, u, a)))) == M.model.len(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, items}))) : Nat}:
  match items:
    case Nil{}:
      el
    case Con{y, +t}:
      nat.succ_inj(Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.read(o, i, u, Array.get(U32, a, U32.from_nat(u)))))), List.length(&2, U32, t), Equal.trans(Nat, 1n+Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.read(o, i, u, Array.get(U32, a, U32.from_nat(u)))))), Nat.sub(i, u), 1n+List.length(&2, U32, t), po.len.r(o, i, u, Array.get(U32, a, U32.from_nat(u)), h, rl.ne(o, i, u, h, y, t, el)), el))

def rl.pop_cap.w(w: Bool, -o: Nat, -i: Nat, -u1: Nat, -a: Array<U32>, -x: U32) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.wrap(w, o, i, u1, a, x)))) == R.ring.size(o) : Nat}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def rl.pop_cap.r(+o: Nat, -i: Nat, +u: Nat, ax: Array<U32> & U32) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.read(o, i, u, ax)))) == R.ring.size(o) : Nat}:
  match ax:
    case (a, x):
      rl.pop_cap.w(Nat.is_eq(1n+u, R.ring.size(o)), o, i, 1n+u, a, x)

def rl.pop_cap(c: Bool, +o: Nat, -i: Nat, +u: Nat, a: Array<U32>, items: List<&2, U32>) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(c, o, i, u, a)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{R.ring.size(o), items}))) : Nat}:
  match c items:
    case True{} Nil{}:
      {==}
    case True{} Con{y, t}:
      {==}
    case False{} Nil{}:
      rl.pop_cap.r(o, i, u, Array.get(U32, a, U32.from_nat(u)))
    case False{} Con{y, t}:
      rl.pop_cap.r(o, i, u, Array.get(U32, a, U32.from_nat(u)))

def rel.is_full(r: R.RingBuf, m: M.RingModel, +h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, el: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}) -> {Pair.snd(R.RingBuf, Bool, R.ring.is_full(r)) == M.model.is_full(m) : Bool}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      %ec : {Nat.is_eq(Nat.sub(i, u), R.ring.size(o)) == Nat.is_eq(List.length(&2, U32, items), _) : Bool}
      %el : {Nat.is_eq(Nat.sub(i, u), R.ring.size(o)) == Nat.is_eq(_, R.ring.size(o)) : Bool}
      {==}

def rel.is_empty(r: R.RingBuf, m: M.RingModel, +h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, el: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}) -> {Pair.snd(R.RingBuf, Bool, R.ring.is_empty(r)) == M.model.is_empty(m) : Bool}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      %el : {Nat.is_eq(i, u) == Nat.is_eq(_, 0n) : Bool}
      nat.eq_sub(i, u, inv.p2(o, i, u, h))

def rel.avail(r: R.RingBuf, m: M.RingModel, +h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, el: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.avail(r)) == M.model.avail(m) : Nat}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      %ec : {Nat.sub(R.ring.size(o), Nat.sub(i, u)) == Nat.sub(_, List.length(&2, U32, items)) : Nat}
      %el : {Nat.sub(R.ring.size(o), Nat.sub(i, u)) == Nat.sub(R.ring.size(o), _) : Nat}
      {==}

def rel.push(r: R.RingBuf, m: M.RingModel, -x: U32, +h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, el: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(r, x)) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(m, x)) : Result<&2, &2, R.RingError, Unit>}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      %ec : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push.go(R.ring.full.test(o, i, u), o, i, u, a, x)) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(Nat.is_eq(List.length(&2, U32, items), _), _, items, x)) : Result<&2, &2, R.RingError, Unit>}
      %el : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push.go(R.ring.full.test(o, i, u), o, i, u, a, x)) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(Nat.is_eq(_, R.ring.size(o)), R.ring.size(o), items, x)) : Result<&2, &2, R.RingError, Unit>}
      rl.push(R.ring.full.test(o, i, u), o, i, u, a, x, R.ring.size(o), items)

def rel.push_len(r: R.RingBuf, m: M.RingModel, -x: U32, +h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, +el: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(r, x)))) == M.model.len(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(m, x))) : Nat}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      %ec : {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push.go(R.ring.full.test(o, i, u), o, i, u, a, x)))) == M.model.len(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(Nat.is_eq(List.length(&2, U32, items), _), _, items, x))) : Nat}
      %el : {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push.go(R.ring.full.test(o, i, u), o, i, u, a, x)))) == M.model.len(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(Nat.is_eq(_, R.ring.size(o)), R.ring.size(o), items, x))) : Nat}
      rl.push_len(R.ring.full.test(o, i, u), o, i, u, a, x, items, h, el)

def rel.push_capacity(r: R.RingBuf, m: M.RingModel, -x: U32, +h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, el: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(r, x)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(m, x))) : Nat}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      %ec : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push.go(R.ring.full.test(o, i, u), o, i, u, a, x)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(Nat.is_eq(List.length(&2, U32, items), _), _, items, x))) : Nat}
      %el : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push.go(R.ring.full.test(o, i, u), o, i, u, a, x)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(Nat.is_eq(_, R.ring.size(o)), R.ring.size(o), items, x))) : Nat}
      rl.push_cap(R.ring.full.test(o, i, u), o, i, u, a, x, items)

def rel.pop_done(r: R.RingBuf, m: M.RingModel, +h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, el: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}) -> {Result.is_done(&2, &2, R.RingError, U32, Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r))) == Result.is_done(&2, &2, R.RingError, U32, Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(m))) : Bool}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      %Equal.sym(Bool, Nat.is_eq(i, u), Nat.is_eq(Nat.sub(i, u), 0n), nat.eq_sub(i, u, inv.p2(o, i, u, h))) : {Result.is_done(&2, &2, R.RingError, U32, Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(_, o, i, u, a))) == Result.is_done(&2, &2, R.RingError, U32, Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, items}))) : Bool}
      %Equal.sym(Nat, Nat.sub(i, u), List.length(&2, U32, items), el) : {Result.is_done(&2, &2, R.RingError, U32, Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(Nat.is_eq(_, 0n), o, i, u, a))) == Result.is_done(&2, &2, R.RingError, U32, Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, items}))) : Bool}
      rl.pop_done(items, o, i, u, a, cap)

def rel.pop_len(r: R.RingBuf, m: M.RingModel, +h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, +el: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r)))) == M.model.len(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(m))) : Nat}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      %Equal.sym(Bool, Nat.is_eq(i, u), Nat.is_eq(Nat.sub(i, u), 0n), nat.eq_sub(i, u, inv.p2(o, i, u, h))) : {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(_, o, i, u, a)))) == M.model.len(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, items}))) : Nat}
      %Equal.sym(Nat, Nat.sub(i, u), List.length(&2, U32, items), el) : {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(Nat.is_eq(_, 0n), o, i, u, a)))) == M.model.len(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, items}))) : Nat}
      rl.pop_len(items, o, i, u, a, cap, h, el)

def rel.pop_capacity(r: R.RingBuf, m: M.RingModel, +h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, el: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(m))) : Nat}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      %ec : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(R.ring.empty.test(i, u), o, i, u, a)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{_, items}))) : Nat}
      rl.pop_cap(R.ring.empty.test(i, u), o, i, u, a, items)

def rel.push_list(r: R.RingBuf, m: M.RingModel, +xs: List<&2, U32>, +h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, el: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.push_list(r, xs)) == Pair.snd(M.RingModel, Nat, M.model.push_list(m, xs)) : Nat}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      %Equal.sym(Nat, Pair.snd(R.RingBuf, Nat, R.ring.push_list(R.RingBuf{o, i, u, a}, xs)), Nat.min(List.length(&2, U32, xs), Nat.sub(R.ring.size(o), Nat.sub(i, u))), bp.count(xs, o, i, u, a, 0n, h)) : {_ == Pair.snd(M.RingModel, Nat, M.model.push_list(M.RingModel{cap, items}, xs)) : Nat}
      %ec : {Nat.min(List.length(&2, U32, xs), Nat.sub(R.ring.size(o), Nat.sub(i, u))) == Nat.min(List.length(&2, U32, xs), Nat.sub(_, List.length(&2, U32, items))) : Nat}
      %el : {Nat.min(List.length(&2, U32, xs), Nat.sub(R.ring.size(o), Nat.sub(i, u))) == Nat.min(List.length(&2, U32, xs), Nat.sub(R.ring.size(o), _)) : Nat}
      {==}

def rel.pop_list(r: R.RingBuf, m: M.RingModel, +k: Nat, +h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, el: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}) -> {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list(r, k))) == List.length(&2, U32, Pair.snd(M.RingModel, List<&2, U32>, M.model.pop_list(m, k))) : Nat}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      %Equal.sym(Nat, List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list(R.RingBuf{o, i, u, a}, k))), Nat.min(k, Nat.sub(i, u)), bo.count(k, o, i, u, a, Nil{}, h)) : {_ == List.length(&2, U32, List.take(&2, U32, items, k)) : Nat}
      %Equal.sym(Nat, List.length(&2, U32, List.take(&2, U32, items, k)), Nat.min(k, List.length(&2, U32, items)), list.length_take(items, k)) : {Nat.min(k, Nat.sub(i, u)) == _ : Nat}
      %el : {Nat.min(k, Nat.sub(i, u)) == Nat.min(k, _) : Nat}
      {==}

# The laws: the model

def Laws.model_new_valid(o):
  nat.le_zero(R.ring.size(o))

def Laws.model_new_empty(o):
  {==}

def Laws.model_new_capacity(o):
  {==}

def Laws.model_push_items(m, x, e):
  match m:
    case M.RingModel{+cap, +items}:
      mo.push_items(Nat.is_eq(List.length(&2, U32, items), cap), cap, items, x, {==}, e)

def Laws.model_push_done(m, x, e):
  match m:
    case M.RingModel{+cap, +items}:
      mo.push_done(Nat.is_eq(List.length(&2, U32, items), cap), cap, items, x, {==}, e)

def Laws.model_push_full(m, x, e):
  match m:
    case M.RingModel{+cap, +items}:
      mo.push_full(Nat.is_eq(List.length(&2, U32, items), cap), cap, items, x, {==}, e)

def Laws.model_push_valid(m, x, h):
  match m:
    case M.RingModel{+cap, +items}:
      mo.push_valid(Nat.is_eq(List.length(&2, U32, items), cap), cap, items, x, h, {==})

def Laws.model_pop(m, y, t, e):
  match m:
    case M.RingModel{cap, items}:
      %Equal.sym(List<&2, U32>, items, Con{y, t}, e) : {Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, _})) == Done{y} : Result<&2, &2, R.RingError, U32>}
      {==}

def Laws.model_pop_items(m, y, t, e):
  match m:
    case M.RingModel{cap, items}:
      %Equal.sym(List<&2, U32>, items, Con{y, t}, e) : {M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, _}))) == t : List<&2, U32>}
      {==}

def Laws.model_pop_empty(m, e):
  match m:
    case M.RingModel{cap, items}:
      match items:
        case Nil{}:
          {==}
        case Con{y, t}:
          Empty.absurd({M.model.pop(M.RingModel{cap, Con{y, t}}) == (M.RingModel{cap, Con{y, t}}, Fail{R.RingEmpty{}}) : M.RingModel & Result<&2, &2, R.RingError, U32>}, absurd.ft(e))

def Laws.model_pop_valid(m, h):
  match m:
    case M.RingModel{+cap, items}:
      match items:
        case Nil{}:
          h
        case Con{y, +t}:
          UO.nat_le_trans(List.length(&2, U32, t), 1n+List.length(&2, U32, t), cap, nat.le_succ(List.length(&2, U32, t), List.length(&2, U32, t), UL.nat_le_refl(List.length(&2, U32, t))), h)

def Laws.model_peek_is_pop(m):
  match m:
    case M.RingModel{cap, items}:
      match items:
        case Nil{}:
          {==}
        case Con{y, t}:
          {==}

def Laws.model_peek_keeps(m):
  match m:
    case M.RingModel{cap, items}:
      match items:
        case Nil{}:
          {==}
        case Con{y, t}:
          {==}

def Laws.model_push_list(m, xs, h, l):
  mo.push_list(m, xs, h, l)

def Laws.model_push_list_count(m, xs):
  match m:
    case M.RingModel{cap, items}:
      {==}

def Laws.model_push_list_valid(m, xs, h):
  mo.push_list_valid(m, xs, h)

def Laws.model_pop_list(m, n):
  match m:
    case M.RingModel{cap, items}:
      {==}

def Laws.model_pop_list_items(m, n):
  match m:
    case M.RingModel{cap, items}:
      {==}

def Laws.model_pop_list_valid(m, n, h):
  mo.pop_list_valid(m, n, h)

def Laws.model_fifo(m, xs, h, l):
  mo.fifo(m, xs, h, l)

# The laws: the Array ring against the model

def Laws.rel_is_full(r, m, h, c, n):
  rel.is_full(r, m, h, c, n)

def Laws.rel_is_empty(r, m, h, c, n):
  rel.is_empty(r, m, h, c, n)

def Laws.rel_avail(r, m, h, c, n):
  rel.avail(r, m, h, c, n)

def Laws.rel_push(r, m, x, h, c, n):
  rel.push(r, m, x, h, c, n)

def Laws.rel_push_len(r, m, x, h, c, n):
  rel.push_len(r, m, x, h, c, n)

def Laws.rel_push_capacity(r, m, x, h, c, n):
  rel.push_capacity(r, m, x, h, c, n)

def Laws.rel_pop_done(r, m, h, c, n):
  rel.pop_done(r, m, h, c, n)

def Laws.rel_pop_len(r, m, h, c, n):
  rel.pop_len(r, m, h, c, n)

def Laws.rel_pop_capacity(r, m, h, c, n):
  rel.pop_capacity(r, m, h, c, n)

def Laws.rel_push_list(r, m, xs, h, c, n):
  rel.push_list(r, m, xs, h, c, n)

def Laws.rel_pop_list(r, m, k, h, c, n):
  rel.pop_list(r, m, k, h, c, n)

# Witnesses

def Laws.wit_full():
  {==}

def Laws.wit_not_full():
  {==}

def Laws.wit_not_empty():
  {==}

def Laws.wit_related():
  {==}

def Laws.wit_model():
  {==}

# The Array ring's elements, through bend-osdev-array
# ===================================================
#
# Generated by gen/proof_elems.py; the lemmas on the slots and the view are
# in proof_items.bend. A sound ring's array is reflected once into
# Arrays.of_list(o, l, 0); the ring is then I.ri.rr(o, i, u, l) and its
# elements I.ri.view(i - u, u, o, l). The model with the same capacity and
# elements is RingModel{2^o, that view}.

# Push

def el.push_items(c: Bool, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +x: U32, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ec: {R.ring.full.test(o, i, u) == c : Bool}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push.go(c, o, i, u, I.ri.ol(o, l), x)))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(c, R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l), x))) : List<&2, U32>}:
  match c:
    case True{}:
      I.ri.items_snd(o, i, u, l, hl, hd)
    case False{}:
      %Equal.sym(R.RingBuf & Result<&2, &2, R.RingError, Unit>, R.ring.push.go(False{}, o, i, u, I.ri.ol(o, l), x), (I.ri.rr(o, 1n+i, u, I.ri.set(o, l, i, x)), Done{Unit{}}), I.ri.push_eq(o, i, u, l, x, hl, hd)) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, _))) == List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), Con{x, Nil{}}) : List<&2, U32>}
      Equal.trans(List<&2, U32>, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(I.ri.rr(o, 1n+i, u, I.ri.set(o, l, i, x)))), I.ri.view(Nat.sub(1n+i, u), u, o, I.ri.set(o, l, i, x)), List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), Con{x, Nil{}}), I.ri.items_snd(o, 1n+i, u, I.ri.set(o, l, i, x), I.ri.set_len(o, l, i, x, hl), hd), I.ri.view_push(o, i, u, l, x, hl, hd, inv.p2(o, i, u, h), nat.le_ne_succ(Nat.sub(i, u), R.ring.size(o), inv.p3(o, i, u, h), ec), inv.p1(o, i, u, h)))

def el.push_cap(c: Bool, -o: Nat, -i: Nat, -u: Nat, -l: List<&2, U32>, -x: U32) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push.go(c, o, i, u, I.ri.ol(o, l), x)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(c, R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l), x))) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def el.push_sound(c: Bool, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +x: U32, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ec: {R.ring.full.test(o, i, u) == c : Bool}) -> {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push.go(c, o, i, u, I.ri.ol(o, l), x))) == True{} : Bool}:
  match c:
    case True{}:
      I.ri.sound_of(o, i, u, l, h, hd)
    case False{}:
      %Equal.sym(R.RingBuf & Result<&2, &2, R.RingError, Unit>, R.ring.push.go(False{}, o, i, u, I.ri.ol(o, l), x), (I.ri.rr(o, 1n+i, u, I.ri.set(o, l, i, x)), Done{Unit{}}), I.ri.push_eq(o, i, u, l, x, hl, hd)) : {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, _)) == True{} : Bool}
      I.ri.sound_of(o, 1n+i, u, I.ri.set(o, l, i, x), inv.push(o, i, u, h, ec), hd)

# Pop: the counters on, or dropped by 2^o, read the same slots

def el.wrap_view(+o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ew: {Nat.is_eq(1n+u, R.ring.size(o)) == True{} : Bool}) -> {I.ri.view(Nat.sub(Nat.sub(i, R.ring.size(o)), 0n), 0n, o, l) == I.ri.view(Nat.sub(i, 1n+u), 1n+u, o, l) : List<&2, U32>}:
  %Equal.sym(Nat, 1n+u, R.ring.size(o), nat.eq_of(1n+u, R.ring.size(o), ew)) : {I.ri.view(Nat.sub(Nat.sub(i, R.ring.size(o)), 0n), 0n, o, l) == I.ri.view(Nat.sub(i, _), _, o, l) : List<&2, U32>}
  %Equal.sym(Nat, Nat.sub(Nat.sub(i, R.ring.size(o)), 0n), Nat.sub(i, R.ring.size(o)), nat.sub_zero(Nat.sub(i, R.ring.size(o)))) : {I.ri.view(_, 0n, o, l) == I.ri.view(Nat.sub(i, R.ring.size(o)), R.ring.size(o), o, l) : List<&2, U32>}
  Equal.sym(List<&2, U32>, I.ri.view(Nat.sub(i, R.ring.size(o)), R.ring.size(o), o, l), I.ri.view(Nat.sub(i, R.ring.size(o)), 0n, o, l), I.ri.view_drop(Nat.sub(i, R.ring.size(o)), o, l, hd, I.ri.le_rw(Nat.sub(Nat.sub(i, R.ring.size(o)), 0n), R.ring.size(o), Nat.sub(i, R.ring.size(o)), R.ring.size(o), nat.sub_zero(Nat.sub(i, R.ring.size(o))), {==}, inv.wrap3(o, i, u, h, ew))))

def el.pop_ans(c: Bool, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ec: {R.ring.empty.test(i, u) == c : Bool}) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(c, o, i, u, I.ri.ol(o, l))) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)})) : Result<&2, &2, R.RingError, U32>}:
  match c:
    case True{}:
      %Equal.sym(Nat, Nat.sub(i, u), 0n, len.empty(i, u, ec)) : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(True{}, o, i, u, I.ri.ol(o, l))) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{R.ring.size(o), I.ri.view(_, u, o, l)})) : Result<&2, &2, R.RingError, U32>}
      {==}
    case False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, I.ri.ol(o, l), U32.from_nat(u)), (I.ri.ol(o, l), I.ri.at(o, l, u)), I.ri.get_eq(o, l, hl, hd, u)) : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.read(o, i, u, _)) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)})) : Result<&2, &2, R.RingError, U32>}
      %len.wrapF(o, i, u, h, ec) : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.read(o, i, u, (I.ri.ol(o, l), I.ri.at(o, l, u)))) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{R.ring.size(o), I.ri.view(_, u, o, l)})) : Result<&2, &2, R.RingError, U32>}
      Equal.sym(Result<&2, &2, R.RingError, U32>, Done{I.ri.at(o, l, u)}, Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.wrap(Nat.is_eq(1n+u, R.ring.size(o)), o, i, 1n+u, I.ri.ol(o, l), I.ri.at(o, l, u))), pk.pop.w(Nat.is_eq(1n+u, R.ring.size(o)), o, i, 1n+u, I.ri.ol(o, l), I.ri.at(o, l, u)))

def el.pw_items(w: Bool, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ew: {Nat.is_eq(1n+u, R.ring.size(o)) == w : Bool}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.wrap(w, o, i, 1n+u, I.ri.ol(o, l), I.ri.at(o, l, u))))) == I.ri.view(Nat.sub(i, 1n+u), 1n+u, o, l) : List<&2, U32>}:
  match w:
    case True{}:
      Equal.trans(List<&2, U32>, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(I.ri.rr(o, Nat.sub(i, R.ring.size(o)), 0n, l))), I.ri.view(Nat.sub(Nat.sub(i, R.ring.size(o)), 0n), 0n, o, l), I.ri.view(Nat.sub(i, 1n+u), 1n+u, o, l), I.ri.items_snd(o, Nat.sub(i, R.ring.size(o)), 0n, l, hl, hd), el.wrap_view(o, i, u, l, hd, h, ew))
    case False{}:
      I.ri.items_snd(o, i, 1n+u, l, hl, hd)

def el.pop_items(c: Bool, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ec: {R.ring.empty.test(i, u) == c : Bool}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(c, o, i, u, I.ri.ol(o, l))))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)}))) : List<&2, U32>}:
  match c:
    case True{}:
      %Equal.sym(List<&2, U32>, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(I.ri.rr(o, i, u, l))), I.ri.view(Nat.sub(i, u), u, o, l), I.ri.items_snd(o, i, u, l, hl, hd)) : {_ == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)}))) : List<&2, U32>}
      %Equal.sym(Nat, Nat.sub(i, u), 0n, len.empty(i, u, ec)) : {I.ri.view(_, u, o, l) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{R.ring.size(o), I.ri.view(_, u, o, l)}))) : List<&2, U32>}
      {==}
    case False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, I.ri.ol(o, l), U32.from_nat(u)), (I.ri.ol(o, l), I.ri.at(o, l, u)), I.ri.get_eq(o, l, hl, hd, u)) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.read(o, i, u, _)))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)}))) : List<&2, U32>}
      %len.wrapF(o, i, u, h, ec) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.read(o, i, u, (I.ri.ol(o, l), I.ri.at(o, l, u)))))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{R.ring.size(o), I.ri.view(_, u, o, l)}))) : List<&2, U32>}
      el.pw_items(Nat.is_eq(1n+u, R.ring.size(o)), o, i, u, l, hl, hd, h, {==})

def el.pw_cap(w: Bool, -o: Nat, -i: Nat, -u: Nat, -l: List<&2, U32>) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.wrap(w, o, i, 1n+u, I.ri.ol(o, l), I.ri.at(o, l, u))))) == R.ring.size(o) : Nat}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def el.pop_cap(c: Bool, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ec: {R.ring.empty.test(i, u) == c : Bool}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(c, o, i, u, I.ri.ol(o, l))))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)}))) : Nat}:
  match c:
    case True{}:
      %Equal.sym(Nat, Nat.sub(i, u), 0n, len.empty(i, u, ec)) : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(True{}, o, i, u, I.ri.ol(o, l))))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{R.ring.size(o), I.ri.view(_, u, o, l)}))) : Nat}
      {==}
    case False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, I.ri.ol(o, l), U32.from_nat(u)), (I.ri.ol(o, l), I.ri.at(o, l, u)), I.ri.get_eq(o, l, hl, hd, u)) : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.read(o, i, u, _)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)}))) : Nat}
      %len.wrapF(o, i, u, h, ec) : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.read(o, i, u, (I.ri.ol(o, l), I.ri.at(o, l, u)))))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{R.ring.size(o), I.ri.view(_, u, o, l)}))) : Nat}
      el.pw_cap(Nat.is_eq(1n+u, R.ring.size(o)), o, i, u, l)

def el.pw_sound(w: Bool, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ne: {R.ring.empty.test(i, u) == False{} : Bool}, +ew: {Nat.is_eq(1n+u, R.ring.size(o)) == w : Bool}) -> {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.wrap(w, o, i, 1n+u, I.ri.ol(o, l), I.ri.at(o, l, u)))) == True{} : Bool}:
  match w:
    case True{}:
      I.ri.sound_of(o, Nat.sub(i, R.ring.size(o)), 0n, l, inv.pop_wrap(o, i, u, h, ew), hd)
    case False{}:
      I.ri.sound_of(o, i, 1n+u, l, inv.pop_nowrap(o, i, u, h, ne, ew), hd)

def el.pop_sound(c: Bool, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ec: {R.ring.empty.test(i, u) == c : Bool}) -> {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.go(c, o, i, u, I.ri.ol(o, l)))) == True{} : Bool}:
  match c:
    case True{}:
      I.ri.sound_of(o, i, u, l, h, hd)
    case False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, I.ri.ol(o, l), U32.from_nat(u)), (I.ri.ol(o, l), I.ri.at(o, l, u)), I.ri.get_eq(o, l, hl, hd, u)) : {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop.read(o, i, u, _))) == True{} : Bool}
      el.pw_sound(Nat.is_eq(1n+u, R.ring.size(o)), o, i, u, l, hd, h, ec, {==})

# Peek

def el.peek_ans(c: Bool, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ec: {R.ring.empty.test(i, u) == c : Bool}) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.go(c, o, i, u, I.ri.ol(o, l))) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)})) : Result<&2, &2, R.RingError, U32>}:
  match c:
    case True{}:
      %Equal.sym(Nat, Nat.sub(i, u), 0n, len.empty(i, u, ec)) : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.go(True{}, o, i, u, I.ri.ol(o, l))) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{R.ring.size(o), I.ri.view(_, u, o, l)})) : Result<&2, &2, R.RingError, U32>}
      {==}
    case False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, I.ri.ol(o, l), U32.from_nat(u)), (I.ri.ol(o, l), I.ri.at(o, l, u)), I.ri.get_eq(o, l, hl, hd, u)) : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.read(o, i, u, _)) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)})) : Result<&2, &2, R.RingError, U32>}
      %len.wrapF(o, i, u, h, ec) : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.read(o, i, u, (I.ri.ol(o, l), I.ri.at(o, l, u)))) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{R.ring.size(o), I.ri.view(_, u, o, l)})) : Result<&2, &2, R.RingError, U32>}
      {==}

def el.peek_items(c: Bool, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ec: {R.ring.empty.test(i, u) == c : Bool}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.go(c, o, i, u, I.ri.ol(o, l))))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)}))) : List<&2, U32>}:
  match c:
    case True{}:
      %Equal.sym(List<&2, U32>, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(I.ri.rr(o, i, u, l))), I.ri.view(Nat.sub(i, u), u, o, l), I.ri.items_snd(o, i, u, l, hl, hd)) : {_ == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)}))) : List<&2, U32>}
      %Equal.sym(Nat, Nat.sub(i, u), 0n, len.empty(i, u, ec)) : {I.ri.view(_, u, o, l) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{R.ring.size(o), I.ri.view(_, u, o, l)}))) : List<&2, U32>}
      {==}
    case False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, I.ri.ol(o, l), U32.from_nat(u)), (I.ri.ol(o, l), I.ri.at(o, l, u)), I.ri.get_eq(o, l, hl, hd, u)) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.read(o, i, u, _)))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)}))) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(I.ri.rr(o, i, u, l))), I.ri.view(Nat.sub(i, u), u, o, l), I.ri.items_snd(o, i, u, l, hl, hd)) : {_ == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)}))) : List<&2, U32>}
      %len.wrapF(o, i, u, h, ec) : {I.ri.view(_, u, o, l) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{R.ring.size(o), I.ri.view(_, u, o, l)}))) : List<&2, U32>}
      {==}

def el.peek_cap(c: Bool, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ec: {R.ring.empty.test(i, u) == c : Bool}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.go(c, o, i, u, I.ri.ol(o, l))))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)}))) : Nat}:
  match c:
    case True{}:
      %Equal.sym(Nat, Nat.sub(i, u), 0n, len.empty(i, u, ec)) : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.go(True{}, o, i, u, I.ri.ol(o, l))))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{R.ring.size(o), I.ri.view(_, u, o, l)}))) : Nat}
      {==}
    case False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, I.ri.ol(o, l), U32.from_nat(u)), (I.ri.ol(o, l), I.ri.at(o, l, u)), I.ri.get_eq(o, l, hl, hd, u)) : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.read(o, i, u, _)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)}))) : Nat}
      %len.wrapF(o, i, u, h, ec) : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.read(o, i, u, (I.ri.ol(o, l), I.ri.at(o, l, u)))))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{R.ring.size(o), I.ri.view(_, u, o, l)}))) : Nat}
      {==}

def el.peek_sound(c: Bool, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ec: {R.ring.empty.test(i, u) == c : Bool}) -> {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.go(c, o, i, u, I.ri.ol(o, l)))) == True{} : Bool}:
  match c:
    case True{}:
      I.ri.sound_of(o, i, u, l, h, hd)
    case False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, I.ri.ol(o, l), U32.from_nat(u)), (I.ri.ol(o, l), I.ri.at(o, l, u)), I.ri.get_eq(o, l, hl, hd, u)) : {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek.read(o, i, u, _))) == True{} : Bool}
      I.ri.sound_of(o, i, u, l, h, hd)

# Batches: push_list, by induction on the list

def el.pl_items.h(c: Bool, +t: List<&2, U32>, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +x: U32, +n: Nat, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ec: {R.ring.full.test(o, i, u) == c : Bool}, ih: @i2: Nat -> @l2: List<&2, U32> -> @n2: Nat -> @hl2: {List.length(&2, U32, l2) == A.Arrays.slots(o) : Nat} -> @h2: {R.ring.inv(o, i2, u) == True{} : Bool} -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(t, (I.ri.rr(o, i2, u, l2), n2))))) == List.append(&2, U32, I.ri.view(Nat.sub(i2, u), u, o, l2), List.take(&2, U32, t, Nat.min(List.length(&2, U32, t), Nat.sub(R.ring.size(o), Nat.sub(i2, u))))) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(t, R.ring.push_list.count(R.ring.push.go(c, o, i, u, I.ri.ol(o, l), x), n))))) == List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), List.take(&2, U32, Con{x, t}, Nat.min(1n+List.length(&2, U32, t), Nat.sub(R.ring.size(o), Nat.sub(i, u))))) : List<&2, U32>}:
  match c:
    case True{}:
      +lt = List.length(&2, U32, t)
      +av = Nat.sub(R.ring.size(o), Nat.sub(i, u))
      +ez = avail.full(o, i, u, ec)
      %Equal.sym(Nat, av, 0n, ez) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(t, (I.ri.rr(o, i, u, l), n))))) == List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), List.take(&2, U32, Con{x, t}, Nat.min(1n+lt, _))) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(t, (I.ri.rr(o, i, u, l), n))))), List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), List.take(&2, U32, t, Nat.min(lt, av))), ih(i, l, n, hl, h)) : {_ == List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), Nil{}) : List<&2, U32>}
      %Equal.sym(Nat, av, 0n, ez) : {List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), List.take(&2, U32, t, Nat.min(lt, _))) == List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), Nil{}) : List<&2, U32>}
      %Equal.sym(Nat, Nat.min(lt, 0n), 0n, nat.min_zero_r(lt)) : {List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), List.take(&2, U32, t, _)) == List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), Nil{}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.take(&2, U32, t, 0n), Nil{}, I.ri.take_zero(t)) : {List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), _) == List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), Nil{}) : List<&2, U32>}
      {==}
    case False{}:
      +lt = List.length(&2, U32, t)
      +l2 = I.ri.set(o, l, i, x)
      +av2 = Nat.sub(R.ring.size(o), Nat.sub(1n+i, u))
      +tk = List.take(&2, U32, t, Nat.min(lt, av2))
      %Equal.sym(Nat, Nat.sub(R.ring.size(o), Nat.sub(i, u)), 1n+av2, avail.push(o, i, u, h, ec)) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(t, R.ring.push_list.count(R.ring.push.go(False{}, o, i, u, I.ri.ol(o, l), x), n))))) == List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), List.take(&2, U32, Con{x, t}, Nat.min(1n+lt, _))) : List<&2, U32>}
      %Equal.sym(R.RingBuf & Result<&2, &2, R.RingError, Unit>, R.ring.push.go(False{}, o, i, u, I.ri.ol(o, l), x), (I.ri.rr(o, 1n+i, u, I.ri.set(o, l, i, x)), Done{Unit{}}), I.ri.push_eq(o, i, u, l, x, hl, hd)) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(t, R.ring.push_list.count(_, n))))) == List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), Con{x, tk}) : List<&2, U32>}
      %I.ri.app_snoc(I.ri.view(Nat.sub(i, u), u, o, l), x, tk) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(t, (I.ri.rr(o, 1n+i, u, I.ri.set(o, l, i, x)), 1n+n))))) == _ : List<&2, U32>}
      %I.ri.view_push(o, i, u, l, x, hl, hd, inv.p2(o, i, u, h), nat.le_ne_succ(Nat.sub(i, u), R.ring.size(o), inv.p3(o, i, u, h), ec), inv.p1(o, i, u, h)) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(t, (I.ri.rr(o, 1n+i, u, I.ri.set(o, l, i, x)), 1n+n))))) == List.append(&2, U32, _, tk) : List<&2, U32>}
      ih(1n+i, l2, 1n+n, I.ri.set_len(o, l, i, x, hl), inv.push(o, i, u, h, ec))

def el.pl_items(xs: List<&2, U32>, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +n: Nat, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(xs, (I.ri.rr(o, i, u, l), n))))) == List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), List.take(&2, U32, xs, Nat.min(List.length(&2, U32, xs), Nat.sub(R.ring.size(o), Nat.sub(i, u))))) : List<&2, U32>}:
  match xs:
    case Nil{}:
      Equal.trans(List<&2, U32>, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(I.ri.rr(o, i, u, l))), I.ri.view(Nat.sub(i, u), u, o, l), List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), Nil{}), I.ri.items_snd(o, i, u, l, hl, hd), Equal.sym(List<&2, U32>, List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), Nil{}), I.ri.view(Nat.sub(i, u), u, o, l), I.ri.app_nil(I.ri.view(Nat.sub(i, u), u, o, l))))
    case Con{+x, +t}:
      el.pl_items.h(R.ring.full.test(o, i, u), t, o, i, u, l, x, n, hl, hd, h, {==}, i2 => l2 => n2 => hl2 => h2 => el.pl_items(t, o, i2, u, l2, n2, hl2, hd, h2))

def el.pl_cap.h(c: Bool, -t: List<&2, U32>, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +x: U32, +n: Nat, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ec: {R.ring.full.test(o, i, u) == c : Bool}, ih: @i2: Nat -> @l2: List<&2, U32> -> @n2: Nat -> @hl2: {List.length(&2, U32, l2) == A.Arrays.slots(o) : Nat} -> @h2: {R.ring.inv(o, i2, u) == True{} : Bool} -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(t, (I.ri.rr(o, i2, u, l2), n2))))) == R.ring.size(o) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(t, R.ring.push_list.count(R.ring.push.go(c, o, i, u, I.ri.ol(o, l), x), n))))) == R.ring.size(o) : Nat}:
  match c:
    case True{}:
      ih(i, l, n, hl, h)
    case False{}:
      %Equal.sym(R.RingBuf & Result<&2, &2, R.RingError, Unit>, R.ring.push.go(False{}, o, i, u, I.ri.ol(o, l), x), (I.ri.rr(o, 1n+i, u, I.ri.set(o, l, i, x)), Done{Unit{}}), I.ri.push_eq(o, i, u, l, x, hl, hd)) : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(t, R.ring.push_list.count(_, n))))) == R.ring.size(o) : Nat}
      ih(1n+i, I.ri.set(o, l, i, x), 1n+n, I.ri.set_len(o, l, i, x, hl), inv.push(o, i, u, h, ec))

def el.pl_cap(xs: List<&2, U32>, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +n: Nat, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(xs, (I.ri.rr(o, i, u, l), n))))) == R.ring.size(o) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      el.pl_cap.h(R.ring.full.test(o, i, u), t, o, i, u, l, x, n, hl, hd, h, {==}, i2 => l2 => n2 => hl2 => h2 => el.pl_cap(t, o, i2, u, l2, n2, hl2, hd, h2))

def el.pl_sound.h(c: Bool, -t: List<&2, U32>, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +x: U32, +n: Nat, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ec: {R.ring.full.test(o, i, u) == c : Bool}, ih: @i2: Nat -> @l2: List<&2, U32> -> @n2: Nat -> @hl2: {List.length(&2, U32, l2) == A.Arrays.slots(o) : Nat} -> @h2: {R.ring.inv(o, i2, u) == True{} : Bool} -> {R.ring.sound(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(t, (I.ri.rr(o, i2, u, l2), n2)))) == True{} : Bool}) -> {R.ring.sound(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(t, R.ring.push_list.count(R.ring.push.go(c, o, i, u, I.ri.ol(o, l), x), n)))) == True{} : Bool}:
  match c:
    case True{}:
      ih(i, l, n, hl, h)
    case False{}:
      %Equal.sym(R.RingBuf & Result<&2, &2, R.RingError, Unit>, R.ring.push.go(False{}, o, i, u, I.ri.ol(o, l), x), (I.ri.rr(o, 1n+i, u, I.ri.set(o, l, i, x)), Done{Unit{}}), I.ri.push_eq(o, i, u, l, x, hl, hd)) : {R.ring.sound(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(t, R.ring.push_list.count(_, n)))) == True{} : Bool}
      ih(1n+i, I.ri.set(o, l, i, x), 1n+n, I.ri.set_len(o, l, i, x, hl), inv.push(o, i, u, h, ec))

def el.pl_sound(xs: List<&2, U32>, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +n: Nat, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}) -> {R.ring.sound(Pair.fst(R.RingBuf, Nat, R.ring.push_list.go(xs, (I.ri.rr(o, i, u, l), n)))) == True{} : Bool}:
  match xs:
    case Nil{}:
      I.ri.sound_of(o, i, u, l, h, hd)
    case Con{+x, +t}:
      el.pl_sound.h(R.ring.full.test(o, i, u), t, o, i, u, l, x, n, hl, hd, h, {==}, i2 => l2 => n2 => hl2 => h2 => el.pl_sound(t, o, i2, u, l2, n2, hl2, hd, h2))

# Batches: pop_list, by induction on the count

def el.tk0(+o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, -acc: List<&2, U32>, -k: Nat, ec: {R.ring.empty.test(i, u) == True{} : Bool}) -> {List.append(&2, U32, acc, List.take(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), k)) == List.append(&2, U32, acc, List.take(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), 1n+k)) : List<&2, U32>}:
  %Equal.sym(Nat, Nat.sub(i, u), 0n, len.empty(i, u, ec)) : {List.append(&2, U32, acc, List.take(&2, U32, I.ri.view(_, u, o, l), k)) == List.append(&2, U32, acc, List.take(&2, U32, I.ri.view(_, u, o, l), 1n+k)) : List<&2, U32>}
  {==}

def el.dr0(+o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, -k: Nat, ec: {R.ring.empty.test(i, u) == True{} : Bool}) -> {List.drop(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), k) == List.drop(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), 1n+k) : List<&2, U32>}:
  %Equal.sym(Nat, Nat.sub(i, u), 0n, len.empty(i, u, ec)) : {List.drop(&2, U32, I.ri.view(_, u, o, l), k) == List.drop(&2, U32, I.ri.view(_, u, o, l), 1n+k) : List<&2, U32>}
  {==}

def el.ol_ans.w(w: Bool, +k: Nat, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ne: {R.ring.empty.test(i, u) == False{} : Bool}, +acc: List<&2, U32>, +ew: {Nat.is_eq(1n+u, R.ring.size(o)) == w : Bool}, ih: @i2: Nat -> @u2: Nat -> @acc2: List<&2, U32> -> @h2: {R.ring.inv(o, i2, u2) == True{} : Bool} -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, i2, u2, l), acc2))) == List.append(&2, U32, acc2, List.take(&2, U32, I.ri.view(Nat.sub(i2, u2), u2, o, l), k)) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.wrap(w, o, i, 1n+u, I.ri.ol(o, l), I.ri.at(o, l, u)), acc))) == List.append(&2, U32, acc, Con{I.ri.at(o, l, u), List.take(&2, U32, I.ri.view(Nat.sub(i, 1n+u), 1n+u, o, l), k)}) : List<&2, U32>}:
  match w:
    case True{}:
      %el.wrap_view(o, i, u, l, hd, h, ew) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, Nat.sub(i, R.ring.size(o)), 0n, l), List.append(&2, U32, acc, Con{I.ri.at(o, l, u), Nil{}})))) == List.append(&2, U32, acc, Con{I.ri.at(o, l, u), List.take(&2, U32, _, k)}) : List<&2, U32>}
      %I.ri.app_snoc(acc, I.ri.at(o, l, u), List.take(&2, U32, I.ri.view(Nat.sub(Nat.sub(i, R.ring.size(o)), 0n), 0n, o, l), k)) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, Nat.sub(i, R.ring.size(o)), 0n, l), List.append(&2, U32, acc, Con{I.ri.at(o, l, u), Nil{}})))) == _ : List<&2, U32>}
      ih(Nat.sub(i, R.ring.size(o)), 0n, List.append(&2, U32, acc, Con{I.ri.at(o, l, u), Nil{}}), inv.pop_wrap(o, i, u, h, ew))
    case False{}:
      %I.ri.app_snoc(acc, I.ri.at(o, l, u), List.take(&2, U32, I.ri.view(Nat.sub(i, 1n+u), 1n+u, o, l), k)) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, i, 1n+u, l), List.append(&2, U32, acc, Con{I.ri.at(o, l, u), Nil{}})))) == _ : List<&2, U32>}
      ih(i, 1n+u, List.append(&2, U32, acc, Con{I.ri.at(o, l, u), Nil{}}), inv.pop_nowrap(o, i, u, h, ne, ew))

def el.ol_ans.h(c: Bool, +k: Nat, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +acc: List<&2, U32>, +ec: {R.ring.empty.test(i, u) == c : Bool}, ih: @i2: Nat -> @u2: Nat -> @acc2: List<&2, U32> -> @h2: {R.ring.inv(o, i2, u2) == True{} : Bool} -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, i2, u2, l), acc2))) == List.append(&2, U32, acc2, List.take(&2, U32, I.ri.view(Nat.sub(i2, u2), u2, o, l), k)) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.go(c, o, i, u, I.ri.ol(o, l)), acc))) == List.append(&2, U32, acc, List.take(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), 1n+k)) : List<&2, U32>}:
  match c:
    case True{}:
      Equal.trans(List<&2, U32>, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, i, u, l), acc))), List.append(&2, U32, acc, List.take(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), k)), List.append(&2, U32, acc, List.take(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), 1n+k)), ih(i, u, acc, h), el.tk0(o, i, u, l, acc, k, ec))
    case False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, I.ri.ol(o, l), U32.from_nat(u)), (I.ri.ol(o, l), I.ri.at(o, l, u)), I.ri.get_eq(o, l, hl, hd, u)) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.read(o, i, u, _), acc))) == List.append(&2, U32, acc, List.take(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), 1n+k)) : List<&2, U32>}
      %len.wrapF(o, i, u, h, ec) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.read(o, i, u, (I.ri.ol(o, l), I.ri.at(o, l, u))), acc))) == List.append(&2, U32, acc, List.take(&2, U32, I.ri.view(_, u, o, l), 1n+k)) : List<&2, U32>}
      el.ol_ans.w(Nat.is_eq(1n+u, R.ring.size(o)), k, o, i, u, l, hl, hd, h, ec, acc, {==}, ih)

def el.ol_ans(k: Nat, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +acc: List<&2, U32>) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, i, u, l), acc))) == List.append(&2, U32, acc, List.take(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), k)) : List<&2, U32>}:
  match k:
    case 0n:
      %Equal.sym(List<&2, U32>, List.take(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), 0n), Nil{}, I.ri.take_zero(I.ri.view(Nat.sub(i, u), u, o, l))) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(0n, (I.ri.rr(o, i, u, l), acc))) == List.append(&2, U32, acc, _) : List<&2, U32>}
      Equal.sym(List<&2, U32>, List.append(&2, U32, acc, Nil{}), acc, I.ri.app_nil(acc))
    case 1n+ +p:
      el.ol_ans.h(R.ring.empty.test(i, u), p, o, i, u, l, hl, hd, h, acc, {==}, i2 => u2 => acc2 => h2 => el.ol_ans(p, o, i2, u2, l, hl, hd, h2, acc2))

def el.ol_items.w(w: Bool, +k: Nat, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ne: {R.ring.empty.test(i, u) == False{} : Bool}, +acc: List<&2, U32>, +ew: {Nat.is_eq(1n+u, R.ring.size(o)) == w : Bool}, ih: @i2: Nat -> @u2: Nat -> @acc2: List<&2, U32> -> @h2: {R.ring.inv(o, i2, u2) == True{} : Bool} -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, i2, u2, l), acc2))))) == List.drop(&2, U32, I.ri.view(Nat.sub(i2, u2), u2, o, l), k) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.wrap(w, o, i, 1n+u, I.ri.ol(o, l), I.ri.at(o, l, u)), acc))))) == List.drop(&2, U32, I.ri.view(Nat.sub(i, 1n+u), 1n+u, o, l), k) : List<&2, U32>}:
  match w:
    case True{}:
      %el.wrap_view(o, i, u, l, hd, h, ew) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, Nat.sub(i, R.ring.size(o)), 0n, l), List.append(&2, U32, acc, Con{I.ri.at(o, l, u), Nil{}})))))) == List.drop(&2, U32, _, k) : List<&2, U32>}
      ih(Nat.sub(i, R.ring.size(o)), 0n, List.append(&2, U32, acc, Con{I.ri.at(o, l, u), Nil{}}), inv.pop_wrap(o, i, u, h, ew))
    case False{}:
      ih(i, 1n+u, List.append(&2, U32, acc, Con{I.ri.at(o, l, u), Nil{}}), inv.pop_nowrap(o, i, u, h, ne, ew))

def el.ol_items.h(c: Bool, +k: Nat, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +acc: List<&2, U32>, +ec: {R.ring.empty.test(i, u) == c : Bool}, ih: @i2: Nat -> @u2: Nat -> @acc2: List<&2, U32> -> @h2: {R.ring.inv(o, i2, u2) == True{} : Bool} -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, i2, u2, l), acc2))))) == List.drop(&2, U32, I.ri.view(Nat.sub(i2, u2), u2, o, l), k) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.go(c, o, i, u, I.ri.ol(o, l)), acc))))) == List.drop(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), 1n+k) : List<&2, U32>}:
  match c:
    case True{}:
      Equal.trans(List<&2, U32>, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, i, u, l), acc))))), List.drop(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), k), List.drop(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), 1n+k), ih(i, u, acc, h), el.dr0(o, i, u, l, k, ec))
    case False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, I.ri.ol(o, l), U32.from_nat(u)), (I.ri.ol(o, l), I.ri.at(o, l, u)), I.ri.get_eq(o, l, hl, hd, u)) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.read(o, i, u, _), acc))))) == List.drop(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), 1n+k) : List<&2, U32>}
      %len.wrapF(o, i, u, h, ec) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.read(o, i, u, (I.ri.ol(o, l), I.ri.at(o, l, u))), acc))))) == List.drop(&2, U32, I.ri.view(_, u, o, l), 1n+k) : List<&2, U32>}
      el.ol_items.w(Nat.is_eq(1n+u, R.ring.size(o)), k, o, i, u, l, hl, hd, h, ec, acc, {==}, ih)

def el.ol_items(k: Nat, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +acc: List<&2, U32>) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, i, u, l), acc))))) == List.drop(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), k) : List<&2, U32>}:
  match k:
    case 0n:
      %Equal.sym(List<&2, U32>, List.drop(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), 0n), I.ri.view(Nat.sub(i, u), u, o, l), I.ri.drop_zero(I.ri.view(Nat.sub(i, u), u, o, l))) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(0n, (I.ri.rr(o, i, u, l), acc))))) == _ : List<&2, U32>}
      I.ri.items_snd(o, i, u, l, hl, hd)
    case 1n+ +p:
      el.ol_items.h(R.ring.empty.test(i, u), p, o, i, u, l, hl, hd, h, acc, {==}, i2 => u2 => acc2 => h2 => el.ol_items(p, o, i2, u2, l, hl, hd, h2, acc2))

def el.ol_cap.w(w: Bool, +k: Nat, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ne: {R.ring.empty.test(i, u) == False{} : Bool}, +acc: List<&2, U32>, +ew: {Nat.is_eq(1n+u, R.ring.size(o)) == w : Bool}, ih: @i2: Nat -> @u2: Nat -> @acc2: List<&2, U32> -> @h2: {R.ring.inv(o, i2, u2) == True{} : Bool} -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, i2, u2, l), acc2))))) == R.ring.size(o) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.wrap(w, o, i, 1n+u, I.ri.ol(o, l), I.ri.at(o, l, u)), acc))))) == R.ring.size(o) : Nat}:
  match w:
    case True{}:
      ih(Nat.sub(i, R.ring.size(o)), 0n, List.append(&2, U32, acc, Con{I.ri.at(o, l, u), Nil{}}), inv.pop_wrap(o, i, u, h, ew))
    case False{}:
      ih(i, 1n+u, List.append(&2, U32, acc, Con{I.ri.at(o, l, u), Nil{}}), inv.pop_nowrap(o, i, u, h, ne, ew))

def el.ol_cap.h(c: Bool, +k: Nat, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +acc: List<&2, U32>, +ec: {R.ring.empty.test(i, u) == c : Bool}, ih: @i2: Nat -> @u2: Nat -> @acc2: List<&2, U32> -> @h2: {R.ring.inv(o, i2, u2) == True{} : Bool} -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, i2, u2, l), acc2))))) == R.ring.size(o) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.go(c, o, i, u, I.ri.ol(o, l)), acc))))) == R.ring.size(o) : Nat}:
  match c:
    case True{}:
      ih(i, u, acc, h)
    case False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, I.ri.ol(o, l), U32.from_nat(u)), (I.ri.ol(o, l), I.ri.at(o, l, u)), I.ri.get_eq(o, l, hl, hd, u)) : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.read(o, i, u, _), acc))))) == R.ring.size(o) : Nat}
      el.ol_cap.w(Nat.is_eq(1n+u, R.ring.size(o)), k, o, i, u, l, hl, hd, h, ec, acc, {==}, ih)

def el.ol_cap(k: Nat, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +acc: List<&2, U32>) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, i, u, l), acc))))) == R.ring.size(o) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      el.ol_cap.h(R.ring.empty.test(i, u), p, o, i, u, l, hl, hd, h, acc, {==}, i2 => u2 => acc2 => h2 => el.ol_cap(p, o, i2, u2, l, hl, hd, h2, acc2))

def el.ol_sound.w(w: Bool, +k: Nat, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +ne: {R.ring.empty.test(i, u) == False{} : Bool}, +acc: List<&2, U32>, +ew: {Nat.is_eq(1n+u, R.ring.size(o)) == w : Bool}, ih: @i2: Nat -> @u2: Nat -> @acc2: List<&2, U32> -> @h2: {R.ring.inv(o, i2, u2) == True{} : Bool} -> {R.ring.sound(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, i2, u2, l), acc2)))) == True{} : Bool}) -> {R.ring.sound(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.wrap(w, o, i, 1n+u, I.ri.ol(o, l), I.ri.at(o, l, u)), acc)))) == True{} : Bool}:
  match w:
    case True{}:
      ih(Nat.sub(i, R.ring.size(o)), 0n, List.append(&2, U32, acc, Con{I.ri.at(o, l, u), Nil{}}), inv.pop_wrap(o, i, u, h, ew))
    case False{}:
      ih(i, 1n+u, List.append(&2, U32, acc, Con{I.ri.at(o, l, u), Nil{}}), inv.pop_nowrap(o, i, u, h, ne, ew))

def el.ol_sound.h(c: Bool, +k: Nat, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +acc: List<&2, U32>, +ec: {R.ring.empty.test(i, u) == c : Bool}, ih: @i2: Nat -> @u2: Nat -> @acc2: List<&2, U32> -> @h2: {R.ring.inv(o, i2, u2) == True{} : Bool} -> {R.ring.sound(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, i2, u2, l), acc2)))) == True{} : Bool}) -> {R.ring.sound(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.go(c, o, i, u, I.ri.ol(o, l)), acc)))) == True{} : Bool}:
  match c:
    case True{}:
      ih(i, u, acc, h)
    case False{}:
      %Equal.sym(Array<U32> & U32, Array.get(U32, I.ri.ol(o, l), U32.from_nat(u)), (I.ri.ol(o, l), I.ri.at(o, l, u)), I.ri.get_eq(o, l, hl, hd, u)) : {R.ring.sound(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, R.ring.pop_list.keep(R.ring.pop.read(o, i, u, _), acc)))) == True{} : Bool}
      el.ol_sound.w(Nat.is_eq(1n+u, R.ring.size(o)), k, o, i, u, l, hl, hd, h, ec, acc, {==}, ih)

def el.ol_sound(k: Nat, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +acc: List<&2, U32>) -> {R.ring.sound(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list.go(k, (I.ri.rr(o, i, u, l), acc)))) == True{} : Bool}:
  match k:
    case 0n:
      I.ri.sound_of(o, i, u, l, h, hd)
    case 1n+ +p:
      el.ol_sound.h(R.ring.empty.test(i, u), p, o, i, u, l, hl, hd, h, acc, {==}, i2 => u2 => acc2 => h2 => el.ol_sound(p, o, i2, u2, l, hl, hd, h2, acc2))

# Rings that need no reflection

def el.new_sound(+o: Nat, hd: {Nat.is_lt(o, 32n) == True{} : Bool}) -> {R.ring.sound(R.ring.new(o)) == True{} : Bool}:
  %Equal.sym(Bool, R.ring.inv(o, 0n, 0n), True{}, Laws.new_valid(o)) : {Bool.and(_, Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, Array.new(U32, o, 0)))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_lt(o, 32n), True{}, hd) : {Bool.and(_, A.Arrays.is_perfect(U32, o, Array.new(U32, o, 0))) == True{} : Bool}
  AL.new_perfect(U32, o, 0)

def el.sound_valid(r: R.RingBuf, hs: {R.ring.sound(r) == True{} : Bool}) -> {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)

# The laws, each on its ring taken apart and reflected

def el.l.items_len.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a}))) == Pair.snd(R.RingBuf, Nat, R.ring.len(R.RingBuf{o, i, u, a})) : Nat}:
  %e1 : {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, _}))) == Pair.snd(R.RingBuf, Nat, R.ring.len(R.RingBuf{o, i, u, _})) : Nat}
  %Equal.sym(List<&2, U32>, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(I.ri.rr(o, i, u, l))), I.ri.view(Nat.sub(i, u), u, o, l), I.ri.items_snd(o, i, u, l, hl, hd)) : {List.length(&2, U32, _) == Nat.sub(i, u) : Nat}
  I.ri.view_len(Nat.sub(i, u), u, o, l)

def el.l.items_len.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a}))) == Pair.snd(R.RingBuf, Nat, R.ring.len(R.RingBuf{o, i, u, a})) : Nat}:
  (l, e) = r
  (e1, hl) = e
  el.l.items_len.body(o, i, u, a, h, hd, l, e1, hl)

def el.l.items_len(r: R.RingBuf, +hs: {R.ring.sound(r) == True{} : Bool}) -> {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(r))) == Pair.snd(R.RingBuf, Nat, R.ring.len(r)) : Nat}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.items_len.ref(o, i, u, a, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.items_same.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.fst(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == R.RingBuf{o, i, u, a} : R.RingBuf}:
  %e1 : {Pair.fst(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, _})) == R.RingBuf{o, i, u, _} : R.RingBuf}
  I.ri.items_fst(o, i, u, l, hl, hd)

def el.l.items_same.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.fst(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == R.RingBuf{o, i, u, a} : R.RingBuf}:
  (l, e) = r
  (e1, hl) = e
  el.l.items_same.body(o, i, u, a, h, hd, l, e1, hl)

def el.l.items_same(r: R.RingBuf, +hs: {R.ring.sound(r) == True{} : Bool}) -> {Pair.fst(R.RingBuf, List<&2, U32>, R.ring.items(r)) == r : R.RingBuf}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.items_same.ref(o, i, u, a, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.push_sound.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +x: U32, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(R.RingBuf{o, i, u, a}, x))) == True{} : Bool}:
  %e1 : {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(R.RingBuf{o, i, u, _}, x))) == True{} : Bool}
  el.push_sound(R.ring.full.test(o, i, u), o, i, u, l, x, hl, hd, h, {==})

def el.l.push_sound.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +x: U32, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(R.RingBuf{o, i, u, a}, x))) == True{} : Bool}:
  (l, e) = r
  (e1, hl) = e
  el.l.push_sound.body(o, i, u, a, x, h, hd, l, e1, hl)

def el.l.push_sound(r: R.RingBuf, x: U32, +hs: {R.ring.sound(r) == True{} : Bool}) -> {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(r, x))) == True{} : Bool}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.push_sound.ref(o, i, u, a, x, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.pop_sound.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(R.RingBuf{o, i, u, a}))) == True{} : Bool}:
  %e1 : {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(R.RingBuf{o, i, u, _}))) == True{} : Bool}
  el.pop_sound(R.ring.empty.test(i, u), o, i, u, l, hl, hd, h, {==})

def el.l.pop_sound.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(R.RingBuf{o, i, u, a}))) == True{} : Bool}:
  (l, e) = r
  (e1, hl) = e
  el.l.pop_sound.body(o, i, u, a, h, hd, l, e1, hl)

def el.l.pop_sound(r: R.RingBuf, +hs: {R.ring.sound(r) == True{} : Bool}) -> {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r))) == True{} : Bool}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.pop_sound.ref(o, i, u, a, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.peek_sound.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(R.RingBuf{o, i, u, a}))) == True{} : Bool}:
  %e1 : {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(R.RingBuf{o, i, u, _}))) == True{} : Bool}
  el.peek_sound(R.ring.empty.test(i, u), o, i, u, l, hl, hd, h, {==})

def el.l.peek_sound.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(R.RingBuf{o, i, u, a}))) == True{} : Bool}:
  (l, e) = r
  (e1, hl) = e
  el.l.peek_sound.body(o, i, u, a, h, hd, l, e1, hl)

def el.l.peek_sound(r: R.RingBuf, +hs: {R.ring.sound(r) == True{} : Bool}) -> {R.ring.sound(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(r))) == True{} : Bool}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.peek_sound.ref(o, i, u, a, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.push_list_sound.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +xs: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {R.ring.sound(Pair.fst(R.RingBuf, Nat, R.ring.push_list(R.RingBuf{o, i, u, a}, xs))) == True{} : Bool}:
  %e1 : {R.ring.sound(Pair.fst(R.RingBuf, Nat, R.ring.push_list(R.RingBuf{o, i, u, _}, xs))) == True{} : Bool}
  el.pl_sound(xs, o, i, u, l, 0n, hl, hd, h)

def el.l.push_list_sound.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +xs: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {R.ring.sound(Pair.fst(R.RingBuf, Nat, R.ring.push_list(R.RingBuf{o, i, u, a}, xs))) == True{} : Bool}:
  (l, e) = r
  (e1, hl) = e
  el.l.push_list_sound.body(o, i, u, a, xs, h, hd, l, e1, hl)

def el.l.push_list_sound(r: R.RingBuf, xs: List<&2, U32>, +hs: {R.ring.sound(r) == True{} : Bool}) -> {R.ring.sound(Pair.fst(R.RingBuf, Nat, R.ring.push_list(r, xs))) == True{} : Bool}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.push_list_sound.ref(o, i, u, a, xs, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.pop_list_sound.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +n: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {R.ring.sound(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(R.RingBuf{o, i, u, a}, n))) == True{} : Bool}:
  %e1 : {R.ring.sound(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(R.RingBuf{o, i, u, _}, n))) == True{} : Bool}
  el.ol_sound(n, o, i, u, l, hl, hd, h, Nil{})

def el.l.pop_list_sound.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +n: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {R.ring.sound(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(R.RingBuf{o, i, u, a}, n))) == True{} : Bool}:
  (l, e) = r
  (e1, hl) = e
  el.l.pop_list_sound.body(o, i, u, a, n, h, hd, l, e1, hl)

def el.l.pop_list_sound(r: R.RingBuf, n: Nat, +hs: {R.ring.sound(r) == True{} : Bool}) -> {R.ring.sound(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(r, n))) == True{} : Bool}:
  match r:
    case R.RingBuf{+o, +i, +u, a}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.pop_list_sound.ref(o, i, u, a, n, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.elems_push.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +x: U32, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(R.RingBuf{o, i, u, a}, x)) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.RingModel{cap, items}, x)) : Result<&2, &2, R.RingError, Unit>}:
  %e1 : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(R.RingBuf{o, i, u, _}, x)) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.RingModel{cap, items}, x)) : Result<&2, &2, R.RingError, Unit>}
  %I.ri.ei(o, i, u, a, l, items, hl, hd, e1, ei) : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(I.ri.rr(o, i, u, l), x)) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.RingModel{cap, _}, x)) : Result<&2, &2, R.RingError, Unit>}
  %ec : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(I.ri.rr(o, i, u, l), x)) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.RingModel{_, I.ri.view(Nat.sub(i, u), u, o, l)}, x)) : Result<&2, &2, R.RingError, Unit>}
  Laws.rel_push(I.ri.rr(o, i, u, l), M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)}, x, h, {==}, Equal.sym(Nat, List.length(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l)), Nat.sub(i, u), I.ri.view_len(Nat.sub(i, u), u, o, l)))

def el.l.elems_push.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +x: U32, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(R.RingBuf{o, i, u, a}, x)) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.RingModel{cap, items}, x)) : Result<&2, &2, R.RingError, Unit>}:
  (l, e) = r
  (e1, hl) = e
  el.l.elems_push.body(o, i, u, a, cap, items, x, h, hd, ec, ei, l, e1, hl)

def el.l.elems_push(r: R.RingBuf, m: M.RingModel, x: U32, +hs: {R.ring.sound(r) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(r)) == M.model.items(m) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(r, x)) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(m, x)) : Result<&2, &2, R.RingError, Unit>}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.elems_push.ref(o, i, u, a, cap, items, x, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), ec, ei, AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.elems_push_items.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +x: U32, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(R.RingBuf{o, i, u, a}, x)))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.RingModel{cap, items}, x))) : List<&2, U32>}:
  %e1 : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(R.RingBuf{o, i, u, _}, x)))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.RingModel{cap, items}, x))) : List<&2, U32>}
  %I.ri.ei(o, i, u, a, l, items, hl, hd, e1, ei) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(I.ri.rr(o, i, u, l), x)))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.RingModel{cap, _}, x))) : List<&2, U32>}
  %ec : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(I.ri.rr(o, i, u, l), x)))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.RingModel{_, I.ri.view(Nat.sub(i, u), u, o, l)}, x))) : List<&2, U32>}
  %Equal.sym(Nat, List.length(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l)), Nat.sub(i, u), I.ri.view_len(Nat.sub(i, u), u, o, l)) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(I.ri.rr(o, i, u, l), x)))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(Nat.is_eq(_, R.ring.size(o)), R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l), x))) : List<&2, U32>}
  el.push_items(R.ring.full.test(o, i, u), o, i, u, l, x, hl, hd, h, {==})

def el.l.elems_push_items.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +x: U32, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(R.RingBuf{o, i, u, a}, x)))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.RingModel{cap, items}, x))) : List<&2, U32>}:
  (l, e) = r
  (e1, hl) = e
  el.l.elems_push_items.body(o, i, u, a, cap, items, x, h, hd, ec, ei, l, e1, hl)

def el.l.elems_push_items(r: R.RingBuf, m: M.RingModel, x: U32, +hs: {R.ring.sound(r) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(r)) == M.model.items(m) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(r, x)))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(m, x))) : List<&2, U32>}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.elems_push_items.ref(o, i, u, a, cap, items, x, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), ec, ei, AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.elems_push_capacity.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +x: U32, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(R.RingBuf{o, i, u, a}, x)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.RingModel{cap, items}, x))) : Nat}:
  %e1 : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(R.RingBuf{o, i, u, _}, x)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.RingModel{cap, items}, x))) : Nat}
  %I.ri.ei(o, i, u, a, l, items, hl, hd, e1, ei) : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(I.ri.rr(o, i, u, l), x)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.RingModel{cap, _}, x))) : Nat}
  %ec : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(I.ri.rr(o, i, u, l), x)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.RingModel{_, I.ri.view(Nat.sub(i, u), u, o, l)}, x))) : Nat}
  %Equal.sym(Nat, List.length(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l)), Nat.sub(i, u), I.ri.view_len(Nat.sub(i, u), u, o, l)) : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(I.ri.rr(o, i, u, l), x)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push.go(Nat.is_eq(_, R.ring.size(o)), R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l), x))) : Nat}
  el.push_cap(R.ring.full.test(o, i, u), o, i, u, l, x)

def el.l.elems_push_capacity.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +x: U32, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(R.RingBuf{o, i, u, a}, x)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.RingModel{cap, items}, x))) : Nat}:
  (l, e) = r
  (e1, hl) = e
  el.l.elems_push_capacity.body(o, i, u, a, cap, items, x, h, hd, ec, ei, l, e1, hl)

def el.l.elems_push_capacity(r: R.RingBuf, m: M.RingModel, x: U32, +hs: {R.ring.sound(r) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(r)) == M.model.items(m) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(r, x)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(m, x))) : Nat}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.elems_push_capacity.ref(o, i, u, a, cap, items, x, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), ec, ei, AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.elems_pop.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(R.RingBuf{o, i, u, a})) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, items})) : Result<&2, &2, R.RingError, U32>}:
  %e1 : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(R.RingBuf{o, i, u, _})) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, items})) : Result<&2, &2, R.RingError, U32>}
  %I.ri.ei(o, i, u, a, l, items, hl, hd, e1, ei) : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(I.ri.rr(o, i, u, l))) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, _})) : Result<&2, &2, R.RingError, U32>}
  %ec : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(I.ri.rr(o, i, u, l))) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{_, I.ri.view(Nat.sub(i, u), u, o, l)})) : Result<&2, &2, R.RingError, U32>}
  el.pop_ans(R.ring.empty.test(i, u), o, i, u, l, hl, hd, h, {==})

def el.l.elems_pop.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(R.RingBuf{o, i, u, a})) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, items})) : Result<&2, &2, R.RingError, U32>}:
  (l, e) = r
  (e1, hl) = e
  el.l.elems_pop.body(o, i, u, a, cap, items, h, hd, ec, ei, l, e1, hl)

def el.l.elems_pop(r: R.RingBuf, m: M.RingModel, +hs: {R.ring.sound(r) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(r)) == M.model.items(m) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r)) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(m)) : Result<&2, &2, R.RingError, U32>}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.elems_pop.ref(o, i, u, a, cap, items, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), ec, ei, AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.elems_pop_items.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(R.RingBuf{o, i, u, a})))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, items}))) : List<&2, U32>}:
  %e1 : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(R.RingBuf{o, i, u, _})))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, items}))) : List<&2, U32>}
  %I.ri.ei(o, i, u, a, l, items, hl, hd, e1, ei) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(I.ri.rr(o, i, u, l))))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, _}))) : List<&2, U32>}
  %ec : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(I.ri.rr(o, i, u, l))))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{_, I.ri.view(Nat.sub(i, u), u, o, l)}))) : List<&2, U32>}
  el.pop_items(R.ring.empty.test(i, u), o, i, u, l, hl, hd, h, {==})

def el.l.elems_pop_items.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(R.RingBuf{o, i, u, a})))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, items}))) : List<&2, U32>}:
  (l, e) = r
  (e1, hl) = e
  el.l.elems_pop_items.body(o, i, u, a, cap, items, h, hd, ec, ei, l, e1, hl)

def el.l.elems_pop_items(r: R.RingBuf, m: M.RingModel, +hs: {R.ring.sound(r) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(r)) == M.model.items(m) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r)))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(m))) : List<&2, U32>}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.elems_pop_items.ref(o, i, u, a, cap, items, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), ec, ei, AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.elems_pop_capacity.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(R.RingBuf{o, i, u, a})))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, items}))) : Nat}:
  %e1 : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(R.RingBuf{o, i, u, _})))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, items}))) : Nat}
  %I.ri.ei(o, i, u, a, l, items, hl, hd, e1, ei) : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(I.ri.rr(o, i, u, l))))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, _}))) : Nat}
  %ec : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(I.ri.rr(o, i, u, l))))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{_, I.ri.view(Nat.sub(i, u), u, o, l)}))) : Nat}
  el.pop_cap(R.ring.empty.test(i, u), o, i, u, l, hl, hd, h, {==})

def el.l.elems_pop_capacity.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(R.RingBuf{o, i, u, a})))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(M.RingModel{cap, items}))) : Nat}:
  (l, e) = r
  (e1, hl) = e
  el.l.elems_pop_capacity.body(o, i, u, a, cap, items, h, hd, ec, ei, l, e1, hl)

def el.l.elems_pop_capacity(r: R.RingBuf, m: M.RingModel, +hs: {R.ring.sound(r) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(r)) == M.model.items(m) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(m))) : Nat}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.elems_pop_capacity.ref(o, i, u, a, cap, items, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), ec, ei, AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.elems_peek.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(R.RingBuf{o, i, u, a})) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{cap, items})) : Result<&2, &2, R.RingError, U32>}:
  %e1 : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(R.RingBuf{o, i, u, _})) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{cap, items})) : Result<&2, &2, R.RingError, U32>}
  %I.ri.ei(o, i, u, a, l, items, hl, hd, e1, ei) : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(I.ri.rr(o, i, u, l))) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{cap, _})) : Result<&2, &2, R.RingError, U32>}
  %ec : {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(I.ri.rr(o, i, u, l))) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{_, I.ri.view(Nat.sub(i, u), u, o, l)})) : Result<&2, &2, R.RingError, U32>}
  el.peek_ans(R.ring.empty.test(i, u), o, i, u, l, hl, hd, h, {==})

def el.l.elems_peek.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(R.RingBuf{o, i, u, a})) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{cap, items})) : Result<&2, &2, R.RingError, U32>}:
  (l, e) = r
  (e1, hl) = e
  el.l.elems_peek.body(o, i, u, a, cap, items, h, hd, ec, ei, l, e1, hl)

def el.l.elems_peek(r: R.RingBuf, m: M.RingModel, +hs: {R.ring.sound(r) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(r)) == M.model.items(m) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(r)) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(m)) : Result<&2, &2, R.RingError, U32>}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.elems_peek.ref(o, i, u, a, cap, items, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), ec, ei, AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.elems_peek_items.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(R.RingBuf{o, i, u, a})))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{cap, items}))) : List<&2, U32>}:
  %e1 : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(R.RingBuf{o, i, u, _})))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{cap, items}))) : List<&2, U32>}
  %I.ri.ei(o, i, u, a, l, items, hl, hd, e1, ei) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(I.ri.rr(o, i, u, l))))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{cap, _}))) : List<&2, U32>}
  %ec : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(I.ri.rr(o, i, u, l))))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{_, I.ri.view(Nat.sub(i, u), u, o, l)}))) : List<&2, U32>}
  el.peek_items(R.ring.empty.test(i, u), o, i, u, l, hl, hd, h, {==})

def el.l.elems_peek_items.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(R.RingBuf{o, i, u, a})))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{cap, items}))) : List<&2, U32>}:
  (l, e) = r
  (e1, hl) = e
  el.l.elems_peek_items.body(o, i, u, a, cap, items, h, hd, ec, ei, l, e1, hl)

def el.l.elems_peek_items(r: R.RingBuf, m: M.RingModel, +hs: {R.ring.sound(r) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(r)) == M.model.items(m) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(r)))) == M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(m))) : List<&2, U32>}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.elems_peek_items.ref(o, i, u, a, cap, items, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), ec, ei, AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.elems_peek_capacity.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(R.RingBuf{o, i, u, a})))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{cap, items}))) : Nat}:
  %e1 : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(R.RingBuf{o, i, u, _})))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{cap, items}))) : Nat}
  %I.ri.ei(o, i, u, a, l, items, hl, hd, e1, ei) : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(I.ri.rr(o, i, u, l))))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{cap, _}))) : Nat}
  %ec : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(I.ri.rr(o, i, u, l))))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{_, I.ri.view(Nat.sub(i, u), u, o, l)}))) : Nat}
  el.peek_cap(R.ring.empty.test(i, u), o, i, u, l, hl, hd, h, {==})

def el.l.elems_peek_capacity.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(R.RingBuf{o, i, u, a})))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(M.RingModel{cap, items}))) : Nat}:
  (l, e) = r
  (e1, hl) = e
  el.l.elems_peek_capacity.body(o, i, u, a, cap, items, h, hd, ec, ei, l, e1, hl)

def el.l.elems_peek_capacity(r: R.RingBuf, m: M.RingModel, +hs: {R.ring.sound(r) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(r)) == M.model.items(m) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(r)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(m))) : Nat}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.elems_peek_capacity.ref(o, i, u, a, cap, items, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), ec, ei, AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.elems_push_list.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +xs: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.push_list(R.RingBuf{o, i, u, a}, xs)) == Pair.snd(M.RingModel, Nat, M.model.push_list(M.RingModel{cap, items}, xs)) : Nat}:
  %e1 : {Pair.snd(R.RingBuf, Nat, R.ring.push_list(R.RingBuf{o, i, u, _}, xs)) == Pair.snd(M.RingModel, Nat, M.model.push_list(M.RingModel{cap, items}, xs)) : Nat}
  %I.ri.ei(o, i, u, a, l, items, hl, hd, e1, ei) : {Pair.snd(R.RingBuf, Nat, R.ring.push_list(I.ri.rr(o, i, u, l), xs)) == Pair.snd(M.RingModel, Nat, M.model.push_list(M.RingModel{cap, _}, xs)) : Nat}
  %ec : {Pair.snd(R.RingBuf, Nat, R.ring.push_list(I.ri.rr(o, i, u, l), xs)) == Pair.snd(M.RingModel, Nat, M.model.push_list(M.RingModel{_, I.ri.view(Nat.sub(i, u), u, o, l)}, xs)) : Nat}
  Laws.rel_push_list(I.ri.rr(o, i, u, l), M.RingModel{R.ring.size(o), I.ri.view(Nat.sub(i, u), u, o, l)}, xs, h, {==}, Equal.sym(Nat, List.length(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l)), Nat.sub(i, u), I.ri.view_len(Nat.sub(i, u), u, o, l)))

def el.l.elems_push_list.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +xs: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.push_list(R.RingBuf{o, i, u, a}, xs)) == Pair.snd(M.RingModel, Nat, M.model.push_list(M.RingModel{cap, items}, xs)) : Nat}:
  (l, e) = r
  (e1, hl) = e
  el.l.elems_push_list.body(o, i, u, a, cap, items, xs, h, hd, ec, ei, l, e1, hl)

def el.l.elems_push_list(r: R.RingBuf, m: M.RingModel, xs: List<&2, U32>, +hs: {R.ring.sound(r) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(r)) == M.model.items(m) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, Nat, R.ring.push_list(r, xs)) == Pair.snd(M.RingModel, Nat, M.model.push_list(m, xs)) : Nat}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.elems_push_list.ref(o, i, u, a, cap, items, xs, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), ec, ei, AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.elems_push_list_items.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +xs: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Nat, R.ring.push_list(R.RingBuf{o, i, u, a}, xs)))) == M.model.items(Pair.fst(M.RingModel, Nat, M.model.push_list(M.RingModel{cap, items}, xs))) : List<&2, U32>}:
  %e1 : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Nat, R.ring.push_list(R.RingBuf{o, i, u, _}, xs)))) == M.model.items(Pair.fst(M.RingModel, Nat, M.model.push_list(M.RingModel{cap, items}, xs))) : List<&2, U32>}
  %I.ri.ei(o, i, u, a, l, items, hl, hd, e1, ei) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Nat, R.ring.push_list(I.ri.rr(o, i, u, l), xs)))) == M.model.items(Pair.fst(M.RingModel, Nat, M.model.push_list(M.RingModel{cap, _}, xs))) : List<&2, U32>}
  %ec : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Nat, R.ring.push_list(I.ri.rr(o, i, u, l), xs)))) == M.model.items(Pair.fst(M.RingModel, Nat, M.model.push_list(M.RingModel{_, I.ri.view(Nat.sub(i, u), u, o, l)}, xs))) : List<&2, U32>}
  %Equal.sym(Nat, List.length(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l)), Nat.sub(i, u), I.ri.view_len(Nat.sub(i, u), u, o, l)) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Nat, R.ring.push_list(I.ri.rr(o, i, u, l), xs)))) == List.append(&2, U32, I.ri.view(Nat.sub(i, u), u, o, l), List.take(&2, U32, xs, Nat.min(List.length(&2, U32, xs), Nat.sub(R.ring.size(o), _)))) : List<&2, U32>}
  el.pl_items(xs, o, i, u, l, 0n, hl, hd, h)

def el.l.elems_push_list_items.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +xs: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Nat, R.ring.push_list(R.RingBuf{o, i, u, a}, xs)))) == M.model.items(Pair.fst(M.RingModel, Nat, M.model.push_list(M.RingModel{cap, items}, xs))) : List<&2, U32>}:
  (l, e) = r
  (e1, hl) = e
  el.l.elems_push_list_items.body(o, i, u, a, cap, items, xs, h, hd, ec, ei, l, e1, hl)

def el.l.elems_push_list_items(r: R.RingBuf, m: M.RingModel, xs: List<&2, U32>, +hs: {R.ring.sound(r) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(r)) == M.model.items(m) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, Nat, R.ring.push_list(r, xs)))) == M.model.items(Pair.fst(M.RingModel, Nat, M.model.push_list(m, xs))) : List<&2, U32>}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.elems_push_list_items.ref(o, i, u, a, cap, items, xs, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), ec, ei, AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.elems_push_list_capacity.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +xs: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Nat, R.ring.push_list(R.RingBuf{o, i, u, a}, xs)))) == M.model.capacity(Pair.fst(M.RingModel, Nat, M.model.push_list(M.RingModel{cap, items}, xs))) : Nat}:
  %e1 : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Nat, R.ring.push_list(R.RingBuf{o, i, u, _}, xs)))) == M.model.capacity(Pair.fst(M.RingModel, Nat, M.model.push_list(M.RingModel{cap, items}, xs))) : Nat}
  %I.ri.ei(o, i, u, a, l, items, hl, hd, e1, ei) : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Nat, R.ring.push_list(I.ri.rr(o, i, u, l), xs)))) == M.model.capacity(Pair.fst(M.RingModel, Nat, M.model.push_list(M.RingModel{cap, _}, xs))) : Nat}
  %ec : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Nat, R.ring.push_list(I.ri.rr(o, i, u, l), xs)))) == M.model.capacity(Pair.fst(M.RingModel, Nat, M.model.push_list(M.RingModel{_, I.ri.view(Nat.sub(i, u), u, o, l)}, xs))) : Nat}
  el.pl_cap(xs, o, i, u, l, 0n, hl, hd, h)

def el.l.elems_push_list_capacity.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +xs: List<&2, U32>, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Nat, R.ring.push_list(R.RingBuf{o, i, u, a}, xs)))) == M.model.capacity(Pair.fst(M.RingModel, Nat, M.model.push_list(M.RingModel{cap, items}, xs))) : Nat}:
  (l, e) = r
  (e1, hl) = e
  el.l.elems_push_list_capacity.body(o, i, u, a, cap, items, xs, h, hd, ec, ei, l, e1, hl)

def el.l.elems_push_list_capacity(r: R.RingBuf, m: M.RingModel, xs: List<&2, U32>, +hs: {R.ring.sound(r) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(r)) == M.model.items(m) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Nat, R.ring.push_list(r, xs)))) == M.model.capacity(Pair.fst(M.RingModel, Nat, M.model.push_list(m, xs))) : Nat}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.elems_push_list_capacity.ref(o, i, u, a, cap, items, xs, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), ec, ei, AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.elems_pop_list.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +n: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list(R.RingBuf{o, i, u, a}, n)) == Pair.snd(M.RingModel, List<&2, U32>, M.model.pop_list(M.RingModel{cap, items}, n)) : List<&2, U32>}:
  %e1 : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list(R.RingBuf{o, i, u, _}, n)) == Pair.snd(M.RingModel, List<&2, U32>, M.model.pop_list(M.RingModel{cap, items}, n)) : List<&2, U32>}
  %I.ri.ei(o, i, u, a, l, items, hl, hd, e1, ei) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list(I.ri.rr(o, i, u, l), n)) == Pair.snd(M.RingModel, List<&2, U32>, M.model.pop_list(M.RingModel{cap, _}, n)) : List<&2, U32>}
  %ec : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list(I.ri.rr(o, i, u, l), n)) == Pair.snd(M.RingModel, List<&2, U32>, M.model.pop_list(M.RingModel{_, I.ri.view(Nat.sub(i, u), u, o, l)}, n)) : List<&2, U32>}
  el.ol_ans(n, o, i, u, l, hl, hd, h, Nil{})

def el.l.elems_pop_list.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +n: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list(R.RingBuf{o, i, u, a}, n)) == Pair.snd(M.RingModel, List<&2, U32>, M.model.pop_list(M.RingModel{cap, items}, n)) : List<&2, U32>}:
  (l, e) = r
  (e1, hl) = e
  el.l.elems_pop_list.body(o, i, u, a, cap, items, n, h, hd, ec, ei, l, e1, hl)

def el.l.elems_pop_list(r: R.RingBuf, m: M.RingModel, n: Nat, +hs: {R.ring.sound(r) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(r)) == M.model.items(m) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list(r, n)) == Pair.snd(M.RingModel, List<&2, U32>, M.model.pop_list(m, n)) : List<&2, U32>}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.elems_pop_list.ref(o, i, u, a, cap, items, n, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), ec, ei, AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.elems_pop_list_items.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +n: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(R.RingBuf{o, i, u, a}, n)))) == M.model.items(Pair.fst(M.RingModel, List<&2, U32>, M.model.pop_list(M.RingModel{cap, items}, n))) : List<&2, U32>}:
  %e1 : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(R.RingBuf{o, i, u, _}, n)))) == M.model.items(Pair.fst(M.RingModel, List<&2, U32>, M.model.pop_list(M.RingModel{cap, items}, n))) : List<&2, U32>}
  %I.ri.ei(o, i, u, a, l, items, hl, hd, e1, ei) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(I.ri.rr(o, i, u, l), n)))) == M.model.items(Pair.fst(M.RingModel, List<&2, U32>, M.model.pop_list(M.RingModel{cap, _}, n))) : List<&2, U32>}
  %ec : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(I.ri.rr(o, i, u, l), n)))) == M.model.items(Pair.fst(M.RingModel, List<&2, U32>, M.model.pop_list(M.RingModel{_, I.ri.view(Nat.sub(i, u), u, o, l)}, n))) : List<&2, U32>}
  el.ol_items(n, o, i, u, l, hl, hd, h, Nil{})

def el.l.elems_pop_list_items.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +n: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(R.RingBuf{o, i, u, a}, n)))) == M.model.items(Pair.fst(M.RingModel, List<&2, U32>, M.model.pop_list(M.RingModel{cap, items}, n))) : List<&2, U32>}:
  (l, e) = r
  (e1, hl) = e
  el.l.elems_pop_list_items.body(o, i, u, a, cap, items, n, h, hd, ec, ei, l, e1, hl)

def el.l.elems_pop_list_items(r: R.RingBuf, m: M.RingModel, n: Nat, +hs: {R.ring.sound(r) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(r)) == M.model.items(m) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(r, n)))) == M.model.items(Pair.fst(M.RingModel, List<&2, U32>, M.model.pop_list(m, n))) : List<&2, U32>}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.elems_pop_list_items.ref(o, i, u, a, cap, items, n, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), ec, ei, AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def el.l.elems_pop_list_capacity.body(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +n: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(R.RingBuf{o, i, u, a}, n)))) == M.model.capacity(Pair.fst(M.RingModel, List<&2, U32>, M.model.pop_list(M.RingModel{cap, items}, n))) : Nat}:
  %e1 : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(R.RingBuf{o, i, u, _}, n)))) == M.model.capacity(Pair.fst(M.RingModel, List<&2, U32>, M.model.pop_list(M.RingModel{cap, items}, n))) : Nat}
  %I.ri.ei(o, i, u, a, l, items, hl, hd, e1, ei) : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(I.ri.rr(o, i, u, l), n)))) == M.model.capacity(Pair.fst(M.RingModel, List<&2, U32>, M.model.pop_list(M.RingModel{cap, _}, n))) : Nat}
  %ec : {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(I.ri.rr(o, i, u, l), n)))) == M.model.capacity(Pair.fst(M.RingModel, List<&2, U32>, M.model.pop_list(M.RingModel{_, I.ri.view(Nat.sub(i, u), u, o, l)}, n))) : Nat}
  el.ol_cap(n, o, i, u, l, hl, hd, h, Nil{})

def el.l.elems_pop_list_capacity.ref(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +cap: Nat, -items: List<&2, U32>, +n: Nat, +h: {R.ring.inv(o, i, u) == True{} : Bool}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, ec: {R.ring.size(o) == cap : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(R.RingBuf{o, i, u, a}, n)))) == M.model.capacity(Pair.fst(M.RingModel, List<&2, U32>, M.model.pop_list(M.RingModel{cap, items}, n))) : Nat}:
  (l, e) = r
  (e1, hl) = e
  el.l.elems_pop_list_capacity.body(o, i, u, a, cap, items, n, h, hd, ec, ei, l, e1, hl)

def el.l.elems_pop_list_capacity(r: R.RingBuf, m: M.RingModel, n: Nat, +hs: {R.ring.sound(r) == True{} : Bool}, ec: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(r)) == M.model.items(m) : List<&2, U32>}) -> {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(r, n)))) == M.model.capacity(Pair.fst(M.RingModel, List<&2, U32>, M.model.pop_list(m, n))) : Nat}:
  match r m:
    case R.RingBuf{+o, +i, +u, a} M.RingModel{+cap, +items}:
      +hs1 = bool.and_r(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs)
      el.l.elems_pop_list_capacity.ref(o, i, u, a, cap, items, n, bool.and_l(R.ring.inv(o, i, u), Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a)), hs), bool.and_l(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), ec, ei, AL.reflect(U32, o, a, bool.and_r(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, a), hs1), 0))

def Laws.new_items(o):
  {==}

def Laws.new_sound(o, hd):
  el.new_sound(o, hd)

def Laws.sound_valid(r, hs):
  el.sound_valid(r, hs)

def Laws.items_len(r, hs):
  el.l.items_len(r, hs)

def Laws.items_same(r, hs):
  el.l.items_same(r, hs)

def Laws.push_sound(r, x, hs):
  el.l.push_sound(r, x, hs)

def Laws.pop_sound(r, hs):
  el.l.pop_sound(r, hs)

def Laws.peek_sound(r, hs):
  el.l.peek_sound(r, hs)

def Laws.push_list_sound(r, xs, hs):
  el.l.push_list_sound(r, xs, hs)

def Laws.pop_list_sound(r, n, hs):
  el.l.pop_list_sound(r, n, hs)

def Laws.elems_push(r, m, x, hs, ec, ei):
  el.l.elems_push(r, m, x, hs, ec, ei)

def Laws.elems_push_items(r, m, x, hs, ec, ei):
  el.l.elems_push_items(r, m, x, hs, ec, ei)

def Laws.elems_push_capacity(r, m, x, hs, ec, ei):
  el.l.elems_push_capacity(r, m, x, hs, ec, ei)

def Laws.elems_pop(r, m, hs, ec, ei):
  el.l.elems_pop(r, m, hs, ec, ei)

def Laws.elems_pop_items(r, m, hs, ec, ei):
  el.l.elems_pop_items(r, m, hs, ec, ei)

def Laws.elems_pop_capacity(r, m, hs, ec, ei):
  el.l.elems_pop_capacity(r, m, hs, ec, ei)

def Laws.elems_peek(r, m, hs, ec, ei):
  el.l.elems_peek(r, m, hs, ec, ei)

def Laws.elems_peek_items(r, m, hs, ec, ei):
  el.l.elems_peek_items(r, m, hs, ec, ei)

def Laws.elems_peek_capacity(r, m, hs, ec, ei):
  el.l.elems_peek_capacity(r, m, hs, ec, ei)

def Laws.elems_push_list(r, m, xs, hs, ec, ei):
  el.l.elems_push_list(r, m, xs, hs, ec, ei)

def Laws.elems_push_list_items(r, m, xs, hs, ec, ei):
  el.l.elems_push_list_items(r, m, xs, hs, ec, ei)

def Laws.elems_push_list_capacity(r, m, xs, hs, ec, ei):
  el.l.elems_push_list_capacity(r, m, xs, hs, ec, ei)

def Laws.elems_pop_list(r, m, n, hs, ec, ei):
  el.l.elems_pop_list(r, m, n, hs, ec, ei)

def Laws.elems_pop_list_items(r, m, n, hs, ec, ei):
  el.l.elems_pop_list_items(r, m, n, hs, ec, ei)

def Laws.elems_pop_list_capacity(r, m, n, hs, ec, ei):
  el.l.elems_pop_list_capacity(r, m, n, hs, ec, ei)

def Laws.wit_elems():
  {==}

def Laws.vec_items():
  {==}
