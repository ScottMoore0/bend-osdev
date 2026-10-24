import Base
import ../bytes/bytes.bend as B
import ./alias.bend as L
import ./LAWS_alias.bend as Laws

# Proof of first_tail_least. first_tail is the smallest number from 1 missing
# from the sorted tails of the taken names. Every tail a taken name has is
# one whose name is taken (tail_of checks the name it reads back), sorting
# keeps every element (merge sort: each step moves elements between lists),
# and every number from 1 below the smallest missing one is in the list.

# ---------------------------------------------------------------- logic

def fa.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def fa.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : fa.bool(_)
  Unit{}

def fa.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : fa.bool(_)
  Unit{}

def fa.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, fa.ft(e))

def fa.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, fa.ft(e))

def fa.and_i(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, fa.ft(ea))

def fa.or_t(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def fa.mget(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      x

def fa.some_inj(-x: Nat, -y: Nat, e: {Some{x} == Some{y} : Maybe<&2, Nat>}) -> {x == y : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, m => fa.mget(m), Some{x}, Some{y}, e)

def fa.is_none(m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def fa.ns(-y: Nat, e: {None{} == Some{y} : Maybe<&2, Nat>}) -> Empty:
  %e : fa.is_none(_)
  Unit{}

# ---------------------------------------------------------------- Nat

def fa.is_eqc(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Unit
    case LT{}:
      Empty
    case GT{}:
      Empty

def fa.lt_eq(e: {LT{} == EQ{} : Cmp}) -> Empty:
  %Equal.sym(Cmp, LT{}, EQ{}, e) : fa.is_eqc(_)
  Unit{}

def fa.gt_eq(e: {GT{} == EQ{} : Cmp}) -> Empty:
  %Equal.sym(Cmp, GT{}, EQ{}, e) : fa.is_eqc(_)
  Unit{}

def fa.cmp_eq(a: Nat, b: Nat, e: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, fa.lt_eq(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, fa.gt_eq(e))
    case 1n+ap 1n+bp:
      %fa.cmp_eq(ap, bp, e) : {1n+ap == 1n+_ : Nat}
      {==}

def fa.nat_eq(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, fa.ft(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, fa.ft(e))
    case 1n+ap 1n+bp:
      %fa.nat_eq(ap, bp, e) : {1n+ap == 1n+_ : Nat}
      {==}

def fa.le0(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a <= b < a is impossible
def fa.le_lt(a: Nat, b: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_lt(b, a) == True{} : Bool}) -> Empty:
  match a b:
    case 0n 0n:
      fa.ft(h2)
    case 0n 1n+bp:
      fa.ft(h2)
    case 1n+ap 0n:
      fa.ft(h1)
    case 1n+ap 1n+bp:
      fa.le_lt(ap, bp, h1, h2)

def fa.add_one(e: Nat) -> {Nat.add(e, 1n) == 1n+e : Nat}:
  match e:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n), 1n+p, fa.add_one(p))

# e <= k and e != k: 1 + e <= k
def fa.le_ne(e: Nat, k: Nat, l: {Nat.is_le(e, k) == True{} : Bool}, h: {Nat.is_eq(e, k) == False{} : Bool}) -> {Nat.is_le(1n+e, k) == True{} : Bool}:
  match e k:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, fa.tf(h))
    case 0n 1n+kp:
      fa.le0(kp)
    case 1n+ep 0n:
      Empty.absurd({Nat.is_le(2n+ep, 0n) == True{} : Bool}, fa.ft(l))
    case 1n+ep 1n+kp:
      fa.le_ne(ep, kp, l, h)

# ---------------------------------------------------------------- the property: a number's name is taken

def fa.all(+b: List<&2, U32>, +x: List<&2, U32>, +T: List<&2, B.Octets>, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{n, t}:
      Bool.and(L.FatAlias.taken(L.FatAlias.with_tail(b, x, n), T), fa.all(b, x, T, t))

# ---------------------------------------------------------------- a tail read back names a taken name

def fa.chk(ok: Bool, +b: List<&2, U32>, +x: List<&2, U32>, +s: B.Octets, +n: Nat, -k: Nat, hok: {B.Octets.is_eq(L.FatAlias.with_tail(b, x, n), s) == ok : Bool}, e: {L.FatAlias.tail_of.check(ok, n) == Some{k} : Maybe<&2, Nat>}) -> {B.Octets.is_eq(L.FatAlias.with_tail(b, x, k), s) == True{} : Bool}:
  match ok:
    case True{}:
      %fa.some_inj(n, k, e) : {B.Octets.is_eq(L.FatAlias.with_tail(b, x, _), s) == True{} : Bool}
      hok
    case False{}:
      Empty.absurd({B.Octets.is_eq(L.FatAlias.with_tail(b, x, k), s) == True{} : Bool}, fa.ns(k, e))

def fa.num(m: Maybe<&2, Nat>, +b: List<&2, U32>, +x: List<&2, U32>, +s: B.Octets, -k: Nat, e: {L.FatAlias.tail_of.num(m, b, x, s) == Some{k} : Maybe<&2, Nat>}) -> {B.Octets.is_eq(L.FatAlias.with_tail(b, x, k), s) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({B.Octets.is_eq(L.FatAlias.with_tail(b, x, k), s) == True{} : Bool}, fa.ns(k, e))
    case Some{+n}:
      fa.chk(B.Octets.is_eq(L.FatAlias.with_tail(b, x, n), s), b, x, s, n, k, {==}, e)

def fa.at(m: Maybe<&2, Nat>, +xs: List<&2, U32>, +b: List<&2, U32>, +x: List<&2, U32>, +s: B.Octets, -k: Nat, e: {L.FatAlias.tail_of.at(m, xs, b, x, s) == Some{k} : Maybe<&2, Nat>}) -> {B.Octets.is_eq(L.FatAlias.with_tail(b, x, k), s) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({B.Octets.is_eq(L.FatAlias.with_tail(b, x, k), s) == True{} : Bool}, fa.ns(k, e))
    case Some{i}:
      fa.num(L.FatAlias.digits(B.drop(Nat.add(i, 1n), xs), 0n, False{}), b, x, s, k, e)

def fa.tail_of(+b: List<&2, U32>, +x: List<&2, U32>, +s: B.Octets, -k: Nat, e: {L.FatAlias.tail_of(b, x, s) == Some{k} : Maybe<&2, Nat>}) -> {B.Octets.is_eq(L.FatAlias.with_tail(b, x, k), s) == True{} : Bool}:
  fa.at(L.FatAlias.last_tilde(B.take(8n, B.Octets.to_list(s)), 0n, None{}), B.take(8n, B.Octets.to_list(s)), b, x, s, k, e)

# ---------------------------------------------------------------- the tails of the taken names

# c is taken in a list holding s when c is s
def fa.taken_app(+c: B.Octets, pre: List<&2, B.Octets>, +s: B.Octets, +t: List<&2, B.Octets>, +h: {B.Octets.is_eq(c, s) == True{} : Bool}) -> {L.FatAlias.taken(c, List.append(&2, B.Octets, pre, Con{s, t})) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, B.Octets.is_eq(c, s), True{}, h) : {Bool.or(_, L.FatAlias.taken(c, t)) == True{} : Bool}
      {==}
    case Con{h0, p}:
      %Equal.sym(Bool, L.FatAlias.taken(c, List.append(&2, B.Octets, p, Con{s, t})), True{}, fa.taken_app(c, p, s, t, h)) : {Bool.or(B.Octets.is_eq(c, h0), _) == True{} : Bool}
      fa.or_t(B.Octets.is_eq(c, h0))

def fa.rn(+b: List<&2, U32>, +x: List<&2, U32>, +T: List<&2, B.Octets>, +pre: List<&2, B.Octets>, +s: B.Octets, +t: List<&2, B.Octets>, +n: Nat, hT: {T == List.append(&2, B.Octets, pre, Con{s, t}) : List<&2, B.Octets>}, hs: {B.Octets.is_eq(L.FatAlias.with_tail(b, x, n), s) == True{} : Bool}) -> {L.FatAlias.taken(L.FatAlias.with_tail(b, x, n), T) == True{} : Bool}:
  %Equal.sym(List<&2, B.Octets>, T, List.append(&2, B.Octets, pre, Con{s, t}), hT) : {L.FatAlias.taken(L.FatAlias.with_tail(b, x, n), _) == True{} : Bool}
  fa.taken_app(L.FatAlias.with_tail(b, x, n), pre, s, t, hs)

def fa.put(m: Maybe<&2, Nat>, +b: List<&2, U32>, +x: List<&2, U32>, +T: List<&2, B.Octets>, +pre: List<&2, B.Octets>, +s: B.Octets, +t: List<&2, B.Octets>, +acc: List<&2, Nat>, hm: {L.FatAlias.tail_of(b, x, s) == m : Maybe<&2, Nat>}, +hT: {T == List.append(&2, B.Octets, pre, Con{s, t}) : List<&2, B.Octets>}, +ha: {fa.all(b, x, T, acc) == True{} : Bool}) -> {fa.all(b, x, T, L.FatAlias.tails.put(m, acc)) == True{} : Bool}:
  match m:
    case None{}:
      ha
    case Some{+n}:
      fa.and_i(L.FatAlias.taken(L.FatAlias.with_tail(b, x, n), T), fa.all(b, x, T, acc), fa.rn(b, x, T, pre, s, t, n, hT, fa.tail_of(b, x, s, n, hm)), ha)

def fa.app_assoc(pre: List<&2, B.Octets>, +s: B.Octets, +t: List<&2, B.Octets>) -> {List.append(&2, B.Octets, List.append(&2, B.Octets, pre, Con{s, Nil{}}), t) == List.append(&2, B.Octets, pre, Con{s, t}) : List<&2, B.Octets>}:
  match pre:
    case Nil{}:
      {==}
    case Con{+h, p}:
      Equal.cong(List<&2, B.Octets>, List<&2, B.Octets>, z => Con{h, z}, List.append(&2, B.Octets, List.append(&2, B.Octets, p, Con{s, Nil{}}), t), List.append(&2, B.Octets, p, Con{s, t}), fa.app_assoc(p, s, t))

def fa.tails(xs: List<&2, B.Octets>, +b: List<&2, U32>, +x: List<&2, U32>, +T: List<&2, B.Octets>, +pre: List<&2, B.Octets>, +acc: List<&2, Nat>, +hT: {T == List.append(&2, B.Octets, pre, xs) : List<&2, B.Octets>}, +ha: {fa.all(b, x, T, acc) == True{} : Bool}) -> {fa.all(b, x, T, L.FatAlias.tails(xs, b, x, acc)) == True{} : Bool}:
  match xs:
    case Nil{}:
      ha
    case Con{+s, +t}:
      fa.tails(t, b, x, T, List.append(&2, B.Octets, pre, Con{s, Nil{}}), L.FatAlias.tails.put(L.FatAlias.tail_of(b, x, s), acc), Equal.trans(List<&2, B.Octets>, T, List.append(&2, B.Octets, pre, Con{s, t}), List.append(&2, B.Octets, List.append(&2, B.Octets, pre, Con{s, Nil{}}), t), hT, Equal.sym(List<&2, B.Octets>, List.append(&2, B.Octets, List.append(&2, B.Octets, pre, Con{s, Nil{}}), t), List.append(&2, B.Octets, pre, Con{s, t}), fa.app_assoc(pre, s, t))), fa.put(L.FatAlias.tail_of(b, x, s), b, x, T, pre, s, t, acc, {==}, hT, ha))

# ---------------------------------------------------------------- sorting keeps every element

def fa.app(+b: List<&2, U32>, +x: List<&2, U32>, +T: List<&2, B.Octets>, xs: List<&2, Nat>, +ys: List<&2, Nat>, +hx: {fa.all(b, x, T, xs) == True{} : Bool}, +hy: {fa.all(b, x, T, ys) == True{} : Bool}) -> {fa.all(b, x, T, List.append(&2, Nat, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+n, +t}:
      fa.and_i(L.FatAlias.taken(L.FatAlias.with_tail(b, x, n), T), fa.all(b, x, T, List.append(&2, Nat, t, ys)), fa.and_l(L.FatAlias.taken(L.FatAlias.with_tail(b, x, n), T), fa.all(b, x, T, t), hx), fa.app(b, x, T, t, ys, fa.and_r(L.FatAlias.taken(L.FatAlias.with_tail(b, x, n), T), fa.all(b, x, T, t), hx), hy))

def fa.rgo(+b: List<&2, U32>, +x: List<&2, U32>, +T: List<&2, B.Octets>, xs: List<&2, Nat>, acc: List<&2, Nat>, +hx: {fa.all(b, x, T, xs) == True{} : Bool}, +ha: {fa.all(b, x, T, acc) == True{} : Bool}) -> {fa.all(b, x, T, List.reverse.go(&2, Nat, xs, acc)) == True{} : Bool}:
  match xs:
    case Nil{}:
      ha
    case Con{+n, +t}:
      fa.rgo(b, x, T, t, Con{n, acc}, fa.and_r(L.FatAlias.taken(L.FatAlias.with_tail(b, x, n), T), fa.all(b, x, T, t), hx), fa.and_i(L.FatAlias.taken(L.FatAlias.with_tail(b, x, n), T), fa.all(b, x, T, acc), fa.and_l(L.FatAlias.taken(L.FatAlias.with_tail(b, x, n), T), fa.all(b, x, T, t), hx), ha))

def fa.hdn(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      h

# merging keeps every element (q: whether the heads are in order)
def fa.mgo(+b: List<&2, U32>, +x: List<&2, U32>, +T: List<&2, B.Octets>, fuel: Nat, +acc: List<&2, Nat>, +xs: List<&2, Nat>, +ys: List<&2, Nat>, q: Bool, +hq: {Nat.is_le(fa.hdn(xs), fa.hdn(ys)) == q : Bool}, +h: {Bool.and(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, xs), fa.all(b, x, T, ys))) == True{} : Bool}) -> {fa.all(b, x, T, List.merge.go(~Nat, ~Nat.is_le, fuel, (acc, xs, ys))) == True{} : Bool}:
  match fuel:
    case 0n:
      fa.rgo(b, x, T, acc, List.append(&2, Nat, xs, ys), fa.and_l(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, xs), fa.all(b, x, T, ys)), h), fa.app(b, x, T, xs, ys, fa.and_l(fa.all(b, x, T, xs), fa.all(b, x, T, ys), fa.and_r(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, xs), fa.all(b, x, T, ys)), h)), fa.and_r(fa.all(b, x, T, xs), fa.all(b, x, T, ys), fa.and_r(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, xs), fa.all(b, x, T, ys)), h))))
    case 1n+f:
      match xs ys:
        case Nil{} Nil{}:
          fa.rgo(b, x, T, acc, Nil{}, fa.and_l(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, Nil{}), fa.all(b, x, T, Nil{})), h), {==})
        case Nil{} Con{+m, +yt}:
          fa.rgo(b, x, T, acc, Con{m, yt}, fa.and_l(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, Nil{}), fa.all(b, x, T, Con{m, yt})), h), fa.and_r(fa.all(b, x, T, Nil{}), fa.all(b, x, T, Con{m, yt}), fa.and_r(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, Nil{}), fa.all(b, x, T, Con{m, yt})), h)))
        case Con{+n, +xt} Nil{}:
          fa.rgo(b, x, T, acc, Con{n, xt}, fa.and_l(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Nil{})), h), fa.and_l(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Nil{}), fa.and_r(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Nil{})), h)))
        case Con{+n, +xt} Con{+m, +yt}:
          match q:
            case False{}:
              %Equal.sym(Bool, Nat.is_le(n, m), False{}, hq) : {fa.all(b, x, T, List.merge.go(~Nat, ~Nat.is_le, f, List.merge.step(Nat, acc, n, xt, m, yt, _))) == True{} : Bool}
              fa.mgo(b, x, T, f, Con{m, acc}, Con{n, xt}, yt, Nat.is_le(n, fa.hdn(yt)), {==}, fa.and_i(fa.all(b, x, T, Con{m, acc}), Bool.and(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, yt)), fa.and_i(L.FatAlias.taken(L.FatAlias.with_tail(b, x, m), T), fa.all(b, x, T, acc), fa.and_l(L.FatAlias.taken(L.FatAlias.with_tail(b, x, m), T), fa.all(b, x, T, yt), fa.and_r(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Con{m, yt}), fa.and_r(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Con{m, yt})), h))), fa.and_l(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Con{m, yt})), h)), fa.and_i(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, yt), fa.and_l(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Con{m, yt}), fa.and_r(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Con{m, yt})), h)), fa.and_r(L.FatAlias.taken(L.FatAlias.with_tail(b, x, m), T), fa.all(b, x, T, yt), fa.and_r(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Con{m, yt}), fa.and_r(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Con{m, yt})), h))))))
            case True{}:
              %Equal.sym(Bool, Nat.is_le(n, m), True{}, hq) : {fa.all(b, x, T, List.merge.go(~Nat, ~Nat.is_le, f, List.merge.step(Nat, acc, n, xt, m, yt, _))) == True{} : Bool}
              fa.mgo(b, x, T, f, Con{n, acc}, xt, Con{m, yt}, Nat.is_le(fa.hdn(xt), m), {==}, fa.and_i(fa.all(b, x, T, Con{n, acc}), Bool.and(fa.all(b, x, T, xt), fa.all(b, x, T, Con{m, yt})), fa.and_i(L.FatAlias.taken(L.FatAlias.with_tail(b, x, n), T), fa.all(b, x, T, acc), fa.and_l(L.FatAlias.taken(L.FatAlias.with_tail(b, x, n), T), fa.all(b, x, T, xt), fa.and_l(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Con{m, yt}), fa.and_r(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Con{m, yt})), h))), fa.and_l(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Con{m, yt})), h)), fa.and_i(fa.all(b, x, T, xt), fa.all(b, x, T, Con{m, yt}), fa.and_r(L.FatAlias.taken(L.FatAlias.with_tail(b, x, n), T), fa.all(b, x, T, xt), fa.and_l(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Con{m, yt}), fa.and_r(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Con{m, yt})), h))), fa.and_r(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Con{m, yt}), fa.and_r(fa.all(b, x, T, acc), Bool.and(fa.all(b, x, T, Con{n, xt}), fa.all(b, x, T, Con{m, yt})), h)))))

def fa.allr(+b: List<&2, U32>, +x: List<&2, U32>, +T: List<&2, B.Octets>, rs: List<&2, List<&2, Nat>>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      Bool.and(fa.all(b, x, T, r), fa.allr(b, x, T, t))

def fa.pass(+b: List<&2, U32>, +x: List<&2, U32>, +T: List<&2, B.Octets>, +n: Nat, runs: List<&2, List<&2, Nat>>, +h: {fa.allr(b, x, T, runs) == True{} : Bool}) -> {fa.allr(b, x, T, List.sort.pass(~Nat, ~Nat.is_le, n, runs)) == True{} : Bool}:
  match runs:
    case Nil{}:
      {==}
    case Con{r, Nil{}}:
      h
    case Con{+r1, Con{+r2, +rest}}:
      fa.and_i(fa.all(b, x, T, List.merge.go(~Nat, ~Nat.is_le, n, (Nil{}, r1, r2))), fa.allr(b, x, T, List.sort.pass(~Nat, ~Nat.is_le, n, rest)), fa.mgo(b, x, T, n, Nil{}, r1, r2, Nat.is_le(fa.hdn(r1), fa.hdn(r2)), {==}, fa.and_i(fa.all(b, x, T, r1), fa.all(b, x, T, r2), fa.and_l(fa.all(b, x, T, r1), fa.allr(b, x, T, Con{r2, rest}), h), fa.and_l(fa.all(b, x, T, r2), fa.allr(b, x, T, rest), fa.and_r(fa.all(b, x, T, r1), fa.allr(b, x, T, Con{r2, rest}), h)))), fa.pass(b, x, T, n, rest, fa.and_r(fa.all(b, x, T, r2), fa.allr(b, x, T, rest), fa.and_r(fa.all(b, x, T, r1), fa.allr(b, x, T, Con{r2, rest}), h))))

def fa.concat(+b: List<&2, U32>, +x: List<&2, U32>, +T: List<&2, B.Octets>, rs: List<&2, List<&2, Nat>>, +h: {fa.allr(b, x, T, rs) == True{} : Bool}) -> {fa.all(b, x, T, List.concat(&2, Nat, rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      fa.app(b, x, T, r, List.concat(&2, Nat, t), fa.and_l(fa.all(b, x, T, r), fa.allr(b, x, T, t), h), fa.concat(b, x, T, t, fa.and_r(fa.all(b, x, T, r), fa.allr(b, x, T, t), h)))

def fa.sgo(+b: List<&2, U32>, +x: List<&2, U32>, +T: List<&2, B.Octets>, fuel: Nat, +n: Nat, runs: List<&2, List<&2, Nat>>, +h: {fa.allr(b, x, T, runs) == True{} : Bool}) -> {fa.all(b, x, T, List.sort.go(~Nat, ~Nat.is_le, fuel, n, runs)) == True{} : Bool}:
  match fuel:
    case 0n:
      fa.concat(b, x, T, runs, h)
    case 1n+f:
      match runs:
        case Nil{}:
          {==}
        case Con{r, Nil{}}:
          fa.and_l(fa.all(b, x, T, r), True{}, h)
        case Con{+r1, Con{+r2, +rest}}:
          fa.sgo(b, x, T, f, n, List.sort.pass(~Nat, ~Nat.is_le, n, Con{r1, Con{r2, rest}}), fa.pass(b, x, T, n, Con{r1, Con{r2, rest}}, h))

def fa.runs(+b: List<&2, U32>, +x: List<&2, U32>, +T: List<&2, B.Octets>, xs: List<&2, Nat>, +h: {fa.all(b, x, T, xs) == True{} : Bool}) -> {fa.allr(b, x, T, List.sort.runs(Nat, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      fa.and_i(fa.all(b, x, T, Con{m, Nil{}}), fa.allr(b, x, T, List.sort.runs(Nat, t)), fa.and_i(L.FatAlias.taken(L.FatAlias.with_tail(b, x, m), T), True{}, fa.and_l(L.FatAlias.taken(L.FatAlias.with_tail(b, x, m), T), fa.all(b, x, T, t), h), {==}), fa.runs(b, x, T, t, fa.and_r(L.FatAlias.taken(L.FatAlias.with_tail(b, x, m), T), fa.all(b, x, T, t), h)))

def fa.sort(+b: List<&2, U32>, +x: List<&2, U32>, +T: List<&2, B.Octets>, xs: List<&2, Nat>, +h: {fa.all(b, x, T, xs) == True{} : Bool}) -> {fa.all(b, x, T, List.sort(~Nat, ~Nat.is_le, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      fa.sgo(b, x, T, List.length(&2, Nat, Con{m, t}), List.length(&2, Nat, Con{m, t}), List.sort.runs(Nat, Con{m, t}), fa.runs(b, x, T, Con{m, t}, h))

# ---------------------------------------------------------------- the smallest number missing

# every number from e below mex(xs, e) is in xs, so its name is taken
def fa.mex(+b: List<&2, U32>, +x: List<&2, U32>, +T: List<&2, B.Octets>, xs: List<&2, Nat>, +e: Nat, +k: Nat, c: Cmp, q: Bool, +hc: {Nat.cmp(fa.hdn(xs), e) == c : Cmp}, +hq: {Nat.is_eq(e, k) == q : Bool}, +h: {fa.all(b, x, T, xs) == True{} : Bool}, +hl: {Nat.is_le(e, k) == True{} : Bool}, +hk: {Nat.is_lt(k, L.FatAlias.mex(xs, e)) == True{} : Bool}) -> {L.FatAlias.taken(L.FatAlias.with_tail(b, x, k), T) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({L.FatAlias.taken(L.FatAlias.with_tail(b, x, k), T) == True{} : Bool}, fa.le_lt(e, k, hl, hk))
    case Con{+h0, +t}:
      match c:
        case GT{}:
          Empty.absurd({L.FatAlias.taken(L.FatAlias.with_tail(b, x, k), T) == True{} : Bool}, fa.le_lt(e, k, hl, Equal.trans(Bool, Nat.is_lt(k, L.FatAlias.mex.pick(GT{}, e, L.FatAlias.mex(t, L.FatAlias.mex.next(GT{}, e)))), Nat.is_lt(k, L.FatAlias.mex.pick(Nat.cmp(h0, e), e, L.FatAlias.mex(t, L.FatAlias.mex.next(Nat.cmp(h0, e), e)))), True{}, Equal.cong(Cmp, Bool, z => Nat.is_lt(k, L.FatAlias.mex.pick(z, e, L.FatAlias.mex(t, L.FatAlias.mex.next(z, e)))), GT{}, Nat.cmp(h0, e), Equal.sym(Cmp, Nat.cmp(h0, e), GT{}, hc)), hk)))
        case EQ{}:
          match q:
            case True{}:
              %Equal.trans(Nat, h0, e, k, fa.cmp_eq(h0, e, hc), fa.nat_eq(e, k, hq)) : {L.FatAlias.taken(L.FatAlias.with_tail(b, x, _), T) == True{} : Bool}
              fa.and_l(L.FatAlias.taken(L.FatAlias.with_tail(b, x, h0), T), fa.all(b, x, T, t), h)
            case False{}:
              fa.mex(b, x, T, t, Nat.add(e, 1n), k, Nat.cmp(fa.hdn(t), Nat.add(e, 1n)), Nat.is_eq(Nat.add(e, 1n), k), {==}, {==}, fa.and_r(L.FatAlias.taken(L.FatAlias.with_tail(b, x, h0), T), fa.all(b, x, T, t), h), Equal.trans(Bool, Nat.is_le(Nat.add(e, 1n), k), Nat.is_le(1n+e, k), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, k), Nat.add(e, 1n), 1n+e, fa.add_one(e)), fa.le_ne(e, k, hl, hq)), Equal.trans(Bool, Nat.is_lt(k, L.FatAlias.mex.pick(EQ{}, e, L.FatAlias.mex(t, L.FatAlias.mex.next(EQ{}, e)))), Nat.is_lt(k, L.FatAlias.mex.pick(Nat.cmp(h0, e), e, L.FatAlias.mex(t, L.FatAlias.mex.next(Nat.cmp(h0, e), e)))), True{}, Equal.cong(Cmp, Bool, z => Nat.is_lt(k, L.FatAlias.mex.pick(z, e, L.FatAlias.mex(t, L.FatAlias.mex.next(z, e)))), EQ{}, Nat.cmp(h0, e), Equal.sym(Cmp, Nat.cmp(h0, e), EQ{}, hc)), hk))
        case LT{}:
          fa.mex(b, x, T, t, e, k, Nat.cmp(fa.hdn(t), e), q, {==}, hq, fa.and_r(L.FatAlias.taken(L.FatAlias.with_tail(b, x, h0), T), fa.all(b, x, T, t), h), hl, Equal.trans(Bool, Nat.is_lt(k, L.FatAlias.mex.pick(LT{}, e, L.FatAlias.mex(t, L.FatAlias.mex.next(LT{}, e)))), Nat.is_lt(k, L.FatAlias.mex.pick(Nat.cmp(h0, e), e, L.FatAlias.mex(t, L.FatAlias.mex.next(Nat.cmp(h0, e), e)))), True{}, Equal.cong(Cmp, Bool, z => Nat.is_lt(k, L.FatAlias.mex.pick(z, e, L.FatAlias.mex(t, L.FatAlias.mex.next(z, e)))), LT{}, Nat.cmp(h0, e), Equal.sym(Cmp, Nat.cmp(h0, e), LT{}, hc)), hk))

def Laws.first_tail_least(base, ext, taken, k, h1, h2):
  fa.mex(base, ext, taken, List.sort(~Nat, ~Nat.is_le, L.FatAlias.tails(taken, base, ext, Nil{})), 1n, k, Nat.cmp(fa.hdn(List.sort(~Nat, ~Nat.is_le, L.FatAlias.tails(taken, base, ext, Nil{}))), 1n), Nat.is_eq(1n, k), {==}, {==}, fa.sort(base, ext, taken, L.FatAlias.tails(taken, base, ext, Nil{}), fa.tails(taken, base, ext, taken, Nil{}, Nil{}, {==}, {==})), h1, h2)
