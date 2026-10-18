import Base
import ./ksort.bend as K
import ./spec.bend as S
import ./heapsort.bend as H
import ../array/array.bend as AR
import ../array/LAWS.bend as AL
import ../array/PROOF.bend as APF
import ./proof_heap.bend as HM
import ./LAWS.bend as Laws

# Contradictions and Bool

def kp.bt(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def kp.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : kp.bt(_)
  Unit{}

def kp.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, kp.ft(e))

def kp.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, kp.ft(e))

def kp.and_i(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      Empty.absurd({Bool.and(False{}, b) == True{} : Bool}, kp.ft(ea))

# Nat

def kp.add_zero(m: Nat) -> {Nat.add(m, 0n) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      %kp.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def kp.le_zero(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def kp.le_refl(x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      kp.le_refl(p)

def kp.le_trans(a: Nat, b: Nat, c: Nat, e: {Nat.is_le(a, b) == True{} : Bool}, f: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      kp.le_zero(c)
    case 1n+ap 0n _:
      Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, kp.ft(e))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, kp.ft(f))
    case 1n+ap 1n+bp 1n+cp:
      kp.le_trans(ap, bp, cp, e, f)

def kp.le_succ(x: Nat) -> {Nat.is_le(x, 1n+x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      kp.le_succ(p)

# not a <= b: b < a, as 1 + b <= a
def kp.nle(a: Nat, b: Nat, e: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_le(1n+b, a) == True{} : Bool}:
  match a b:
    case 0n +bb:
      Empty.absurd({Nat.is_le(1n+bb, 0n) == True{} : Bool}, kp.ft(Equal.trans(Bool, False{}, Nat.is_le(0n, bb), True{}, Equal.sym(Bool, Nat.is_le(0n, bb), False{}, e), kp.le_zero(bb))))
    case 1n+ap 0n:
      kp.le_zero(ap)
    case 1n+ap 1n+bp:
      kp.nle(ap, bp, e)

def kp.le_of_lt(+a: Nat, b: Nat, e: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  kp.le_trans(a, 1n+a, b, kp.le_succ(a), e)

# 1 + k <= z: z is not k
def kp.neq(z: Nat, k: Nat, e: {Nat.is_le(1n+k, z) == True{} : Bool}) -> {Nat.is_eq(z, k) == False{} : Bool}:
  match z k:
    case 0n _:
      Empty.absurd({Nat.is_eq(0n, k) == False{} : Bool}, kp.ft(e))
    case 1n+zp 0n:
      {==}
    case 1n+zp 1n+kp2:
      kp.neq(zp, kp2, e)

def kp.eq(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, kp.ft(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, kp.ft(e))
    case 1n+ap 1n+bp:
      %kp.eq(ap, bp, e) : {1n+ap == 1n+_ : Nat}
      {==}

def kp.half_le(+n: Nat) -> {Nat.is_le(K.ksort.half(n), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          kp.le_trans(K.ksort.half(q), q, 1n+q, kp.half_le(q), kp.le_succ(q))

# Lists

def kp.take_len(-A: Data, xs: List<&2, A>, n: Nat) -> {Nat.is_le(List.length(&2, A, List.take(&2, A, xs, n)), n) == True{} : Bool}:
  match xs n:
    case Nil{} m:
      kp.le_zero(m)
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      kp.take_len(A, t, p)

def kp.drop_len(-A: Data, +xs: List<&2, A>, +n: Nat) -> {Nat.is_le(List.length(&2, A, List.drop(&2, A, xs, n)), List.length(&2, A, xs)) == True{} : Bool}:
  match xs n:
    case Nil{} m:
      {==}
    case Con{h, t} 0n:
      kp.le_refl(1n+List.length(&2, A, t))
    case Con{h, +t} 1n+p:
      kp.le_trans(List.length(&2, A, List.drop(&2, A, t, p)), List.length(&2, A, t), 1n+List.length(&2, A, t), kp.drop_len(A, t, p), kp.le_succ(List.length(&2, A, t)))

def kp.append_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %kp.append_nil(A, t) : {Con{h, List.append(&2, A, t, Nil{})} == Con{h, _} : List<&2, A>}
      {==}

def kp.take_drop(-A: Data, xs: List<&2, A>, n: Nat) -> {List.append(&2, A, List.take(&2, A, xs, n), List.drop(&2, A, xs, n)) == xs : List<&2, A>}:
  match xs n:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{+h, +t} 1n+ +p:
      %kp.take_drop(A, t, p) : {Con{h, List.append(&2, A, List.take(&2, A, t, p), List.drop(&2, A, t, p))} == Con{h, _} : List<&2, A>}
      {==}

# Counting: every operation of the sort keeps every predicate's count

def kp.cadd_l(b: Bool, -m: Nat, -n: Nat) -> {Nat.add(S.ksort.count.add(b, m), n) == S.ksort.count.add(b, Nat.add(m, n)) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def kp.cadd_succ(b: Bool, -n: Nat) -> {1n+S.ksort.count.add(b, n) == S.ksort.count.add(b, 1n+n) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def kp.cadd_r(m: Nat, +b: Bool, -n: Nat) -> {Nat.add(m, S.ksort.count.add(b, n)) == S.ksort.count.add(b, Nat.add(m, n)) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, S.ksort.count.add(b, n)), S.ksort.count.add(b, Nat.add(p, n)), kp.cadd_r(p, b, n)) : {1n+_ == S.ksort.count.add(b, 1n+Nat.add(p, n)) : Nat}
      kp.cadd_succ(b, Nat.add(p, n))

def kp.count_go(~A: Data, ~le: A -> A -> Bool, ~f: A -> Bool, +xt: List<&2, A>, +yt: List<&2, A>, c: Bool, +x: A, +y: A) -> {S.ksort.count(~A, ~f, K.ksort.merge.go(~A, ~le, xt, yt, c, x, y)) == Nat.add(S.ksort.count(~A, ~f, Con{x, xt}), S.ksort.count(~A, ~f, Con{y, yt})) : Nat}:
  match xt yt c:
    case Nil{} ys True{}:
      Equal.sym(Nat, Nat.add(S.ksort.count.add(f(x), 0n), S.ksort.count(~A, ~f, Con{y, ys})), S.ksort.count.add(f(x), S.ksort.count(~A, ~f, Con{y, ys})), kp.cadd_l(f(x), 0n, S.ksort.count(~A, ~f, Con{y, ys})))
    case Con{+x2, xt2} ys True{}:
      %Equal.sym(Nat, Nat.add(S.ksort.count.add(f(x), S.ksort.count(~A, ~f, Con{x2, xt2})), S.ksort.count(~A, ~f, Con{y, ys})), S.ksort.count.add(f(x), Nat.add(S.ksort.count(~A, ~f, Con{x2, xt2}), S.ksort.count(~A, ~f, Con{y, ys}))), kp.cadd_l(f(x), S.ksort.count(~A, ~f, Con{x2, xt2}), S.ksort.count(~A, ~f, Con{y, ys}))) : {S.ksort.count.add(f(x), S.ksort.count(~A, ~f, K.ksort.merge.go(~A, ~le, xt2, ys, le(x2, y), x2, y))) == _ : Nat}
      %kp.count_go(~A, ~le, ~f, xt2, ys, le(x2, y), x2, y) : {S.ksort.count.add(f(x), S.ksort.count(~A, ~f, K.ksort.merge.go(~A, ~le, xt2, ys, le(x2, y), x2, y))) == S.ksort.count.add(f(x), _) : Nat}
      {==}
    case xs Nil{} False{}:
      %Equal.sym(Nat, Nat.add(S.ksort.count(~A, ~f, Con{x, xs}), S.ksort.count.add(f(y), 0n)), S.ksort.count.add(f(y), Nat.add(S.ksort.count(~A, ~f, Con{x, xs}), 0n)), kp.cadd_r(S.ksort.count(~A, ~f, Con{x, xs}), f(y), 0n)) : {S.ksort.count.add(f(y), S.ksort.count(~A, ~f, Con{x, xs})) == _ : Nat}
      %Equal.sym(Nat, Nat.add(S.ksort.count(~A, ~f, Con{x, xs}), 0n), S.ksort.count(~A, ~f, Con{x, xs}), kp.add_zero(S.ksort.count(~A, ~f, Con{x, xs}))) : {S.ksort.count.add(f(y), S.ksort.count(~A, ~f, Con{x, xs})) == S.ksort.count.add(f(y), _) : Nat}
      {==}
    case xs Con{+y2, yt2} False{}:
      %Equal.sym(Nat, Nat.add(S.ksort.count(~A, ~f, Con{x, xs}), S.ksort.count.add(f(y), S.ksort.count(~A, ~f, Con{y2, yt2}))), S.ksort.count.add(f(y), Nat.add(S.ksort.count(~A, ~f, Con{x, xs}), S.ksort.count(~A, ~f, Con{y2, yt2}))), kp.cadd_r(S.ksort.count(~A, ~f, Con{x, xs}), f(y), S.ksort.count(~A, ~f, Con{y2, yt2}))) : {S.ksort.count.add(f(y), S.ksort.count(~A, ~f, K.ksort.merge.go(~A, ~le, xs, yt2, le(x, y2), x, y2))) == _ : Nat}
      %kp.count_go(~A, ~le, ~f, xs, yt2, le(x, y2), x, y2) : {S.ksort.count.add(f(y), S.ksort.count(~A, ~f, K.ksort.merge.go(~A, ~le, xs, yt2, le(x, y2), x, y2))) == S.ksort.count.add(f(y), _) : Nat}
      {==}

def kp.count_merge(~A: Data, ~le: A -> A -> Bool, ~f: A -> Bool, +xs: List<&2, A>, +ys: List<&2, A>) -> {S.ksort.count(~A, ~f, K.ksort.merge(~A, ~le, xs, ys)) == Nat.add(S.ksort.count(~A, ~f, xs), S.ksort.count(~A, ~f, ys)) : Nat}:
  match xs ys:
    case Nil{} b:
      {==}
    case Con{+x, +xt} Nil{}:
      Equal.sym(Nat, Nat.add(S.ksort.count(~A, ~f, Con{x, xt}), 0n), S.ksort.count(~A, ~f, Con{x, xt}), kp.add_zero(S.ksort.count(~A, ~f, Con{x, xt})))
    case Con{+x, xt} Con{+y, yt}:
      kp.count_go(~A, ~le, ~f, xt, yt, le(x, y), x, y)

def kp.count_take_drop(~A: Data, ~f: A -> Bool, +xs: List<&2, A>, +n: Nat) -> {Nat.add(S.ksort.count(~A, ~f, List.take(&2, A, xs, n)), S.ksort.count(~A, ~f, List.drop(&2, A, xs, n))) == S.ksort.count(~A, ~f, xs) : Nat}:
  match xs n:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{+h, t} 1n+p:
      %Equal.sym(Nat, Nat.add(S.ksort.count.add(f(h), S.ksort.count(~A, ~f, List.take(&2, A, t, p))), S.ksort.count(~A, ~f, List.drop(&2, A, t, p))), S.ksort.count.add(f(h), Nat.add(S.ksort.count(~A, ~f, List.take(&2, A, t, p)), S.ksort.count(~A, ~f, List.drop(&2, A, t, p)))), kp.cadd_l(f(h), S.ksort.count(~A, ~f, List.take(&2, A, t, p)), S.ksort.count(~A, ~f, List.drop(&2, A, t, p)))) : {_ == S.ksort.count.add(f(h), S.ksort.count(~A, ~f, t)) : Nat}
      %kp.count_take_drop(~A, ~f, t, p) : {S.ksort.count.add(f(h), Nat.add(S.ksort.count(~A, ~f, List.take(&2, A, t, p)), S.ksort.count(~A, ~f, List.drop(&2, A, t, p)))) == S.ksort.count.add(f(h), _) : Nat}
      {==}

def kp.count_msort(~A: Data, ~le: A -> A -> Bool, ~f: A -> Bool, +fuel: Nat, +xs: List<&2, A>) -> {S.ksort.count(~A, ~f, K.ksort.msort(~A, ~le, fuel, xs)) == S.ksort.count(~A, ~f, xs) : Nat}:
  match fuel xs:
    case 0n ys:
      {==}
    case 1n+g Nil{}:
      {==}
    case 1n+g Con{x, Nil{}}:
      {==}
    case 1n+g Con{+x, Con{+y, +t}}:
      %Equal.sym(Nat, S.ksort.count(~A, ~f, K.ksort.merge(~A, ~le, K.ksort.msort(~A, ~le, g, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))), K.ksort.msort(~A, ~le, g, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))))), Nat.add(S.ksort.count(~A, ~f, K.ksort.msort(~A, ~le, g, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))))), S.ksort.count(~A, ~f, K.ksort.msort(~A, ~le, g, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))))), kp.count_merge(~A, ~le, ~f, K.ksort.msort(~A, ~le, g, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))), K.ksort.msort(~A, ~le, g, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))))) : {_ == S.ksort.count(~A, ~f, Con{x, Con{y, t}}) : Nat}
      %Equal.sym(Nat, S.ksort.count(~A, ~f, K.ksort.msort(~A, ~le, g, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))))), S.ksort.count(~A, ~f, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))), kp.count_msort(~A, ~le, ~f, g, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))))) : {Nat.add(_, S.ksort.count(~A, ~f, K.ksort.msort(~A, ~le, g, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))))) == S.ksort.count(~A, ~f, Con{x, Con{y, t}}) : Nat}
      %Equal.sym(Nat, S.ksort.count(~A, ~f, K.ksort.msort(~A, ~le, g, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))))), S.ksort.count(~A, ~f, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))), kp.count_msort(~A, ~le, ~f, g, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))))) : {Nat.add(S.ksort.count(~A, ~f, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))), _) == S.ksort.count(~A, ~f, Con{x, Con{y, t}}) : Nat}
      kp.count_take_drop(~A, ~f, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))

def Laws.list_sort_count(A, le, f, xs):
  kp.count_msort(~A, ~le, ~f, List.length(&2, A, xs), xs)

# the predicate every element satisfies
def kp.yes(-A: Data, x: A) -> Bool:
  True{}

def kp.count_true(~A: Data, xs: List<&2, A>) -> {S.ksort.count(~A, ~(x => kp.yes(A, x)), xs) == List.length(&2, A, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %kp.count_true(~A, t) : {1n+S.ksort.count(~A, ~(x => kp.yes(A, x)), t) == 1n+_ : Nat}
      {==}

def Laws.list_sort_length(A, le, xs):
  Equal.trans(Nat, List.length(&2, A, K.ksort.list_sort(~A, ~le, xs)), S.ksort.count(~A, ~(x => kp.yes(A, x)), K.ksort.list_sort(~A, ~le, xs)), List.length(&2, A, xs), Equal.sym(Nat, S.ksort.count(~A, ~(x => kp.yes(A, x)), K.ksort.list_sort(~A, ~le, xs)), List.length(&2, A, K.ksort.list_sort(~A, ~le, xs)), kp.count_true(~A, K.ksort.list_sort(~A, ~le, xs))), Equal.trans(Nat, S.ksort.count(~A, ~(x => kp.yes(A, x)), K.ksort.list_sort(~A, ~le, xs)), S.ksort.count(~A, ~(x => kp.yes(A, x)), xs), List.length(&2, A, xs), Laws.list_sort_count(~A, ~le, ~(x => kp.yes(A, x)), xs), kp.count_true(~A, xs)))

def Laws.list_sort_by_count(A, key, f, xs):
  Laws.list_sort_count(~A, ~(a => b => Nat.is_le(key(a), key(b))), ~f, xs)

# Sorted, for a sort by key: the merge of sorted lists is sorted

def kp.sorted_go(~A: Data, ~key: A -> Nat, +xt: List<&2, A>, +yt: List<&2, A>, c: Bool, +x: A, +y: A, -z: Nat, +e: {Nat.is_le(key(x), key(y)) == c : Bool}, +hx: {S.ksort.sorted_by.from(~A, ~key, xt, key(x)) == True{} : Bool}, +hy: {S.ksort.sorted_by.from(~A, ~key, yt, key(y)) == True{} : Bool}, hzx: {Nat.is_le(z, key(x)) == True{} : Bool}, hzy: {Nat.is_le(z, key(y)) == True{} : Bool}) -> {S.ksort.sorted_by.from(~A, ~key, K.ksort.merge.go(~A, ~(a => b => Nat.is_le(key(a), key(b))), xt, yt, c, x, y), z) == True{} : Bool}:
  match xt yt c:
    case Nil{} ys True{}:
      %Equal.sym(Bool, Nat.is_le(z, key(x)), True{}, hzx) : {Bool.and(_, S.ksort.sorted_by.from(~A, ~key, Con{y, ys}, key(x))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_le(key(x), key(y)), True{}, e) : {Bool.and(_, S.ksort.sorted_by.from(~A, ~key, ys, key(y))) == True{} : Bool}
      hy
    case Con{+x2, xt2} ys True{}:
      %Equal.sym(Bool, Nat.is_le(z, key(x)), True{}, hzx) : {Bool.and(_, S.ksort.sorted_by.from(~A, ~key, K.ksort.merge.go(~A, ~(a => b => Nat.is_le(key(a), key(b))), xt2, ys, Nat.is_le(key(x2), key(y)), x2, y), key(x))) == True{} : Bool}
      kp.sorted_go(~A, ~key, xt2, ys, Nat.is_le(key(x2), key(y)), x2, y, key(x), {==}, kp.and_r(Nat.is_le(key(x), key(x2)), S.ksort.sorted_by.from(~A, ~key, xt2, key(x2)), hx), hy, kp.and_l(Nat.is_le(key(x), key(x2)), S.ksort.sorted_by.from(~A, ~key, xt2, key(x2)), hx), e)
    case xs Nil{} False{}:
      %Equal.sym(Bool, Nat.is_le(z, key(y)), True{}, hzy) : {Bool.and(_, S.ksort.sorted_by.from(~A, ~key, Con{x, xs}, key(y))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_le(key(y), key(x)), True{}, kp.le_of_lt(key(y), key(x), kp.nle(key(x), key(y), e))) : {Bool.and(_, S.ksort.sorted_by.from(~A, ~key, xs, key(x))) == True{} : Bool}
      hx
    case xs Con{+y2, yt2} False{}:
      %Equal.sym(Bool, Nat.is_le(z, key(y)), True{}, hzy) : {Bool.and(_, S.ksort.sorted_by.from(~A, ~key, K.ksort.merge.go(~A, ~(a => b => Nat.is_le(key(a), key(b))), xs, yt2, Nat.is_le(key(x), key(y2)), x, y2), key(y))) == True{} : Bool}
      kp.sorted_go(~A, ~key, xs, yt2, Nat.is_le(key(x), key(y2)), x, y2, key(y), {==}, hx, kp.and_r(Nat.is_le(key(y), key(y2)), S.ksort.sorted_by.from(~A, ~key, yt2, key(y2)), hy), kp.le_of_lt(key(y), key(x), kp.nle(key(x), key(y), e)), kp.and_l(Nat.is_le(key(y), key(y2)), S.ksort.sorted_by.from(~A, ~key, yt2, key(y2)), hy))

def kp.sorted_merge(~A: Data, ~key: A -> Nat, +xs: List<&2, A>, +ys: List<&2, A>, +hxs: {S.ksort.sorted_by.from(~A, ~key, xs, 0n) == True{} : Bool}, +hys: {S.ksort.sorted_by.from(~A, ~key, ys, 0n) == True{} : Bool}) -> {S.ksort.sorted_by.from(~A, ~key, K.ksort.merge(~A, ~(a => b => Nat.is_le(key(a), key(b))), xs, ys), 0n) == True{} : Bool}:
  match xs ys:
    case Nil{} b:
      hys
    case Con{x, xt} Nil{}:
      hxs
    case Con{+x, +xt} Con{+y, +yt}:
      kp.sorted_go(~A, ~key, xt, yt, Nat.is_le(key(x), key(y)), x, y, 0n, {==}, kp.and_r(Nat.is_le(0n, key(x)), S.ksort.sorted_by.from(~A, ~key, xt, key(x)), hxs), kp.and_r(Nat.is_le(0n, key(y)), S.ksort.sorted_by.from(~A, ~key, yt, key(y)), hys), kp.le_zero(key(x)), kp.le_zero(key(y)))

# The halves of a list of at most 1 + g elements (at least two) have at
# most g each

def kp.bound_take(-A: Data, +x: A, +y: A, +t: List<&2, A>, +g: Nat, h: {Nat.is_le(List.length(&2, A, Con{x, Con{y, t}}), 1n+g) == True{} : Bool}) -> {Nat.is_le(List.length(&2, A, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))), g) == True{} : Bool}:
  kp.le_trans(List.length(&2, A, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))), 1n+K.ksort.half(List.length(&2, A, t)), g, kp.take_len(A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))), kp.le_trans(1n+K.ksort.half(List.length(&2, A, t)), 1n+List.length(&2, A, t), g, kp.half_le(List.length(&2, A, t)), h))

def kp.bound_drop(-A: Data, -x: A, +y: A, +t: List<&2, A>, +g: Nat, h: {Nat.is_le(List.length(&2, A, Con{x, Con{y, t}}), 1n+g) == True{} : Bool}) -> {Nat.is_le(List.length(&2, A, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))), g) == True{} : Bool}:
  kp.le_trans(List.length(&2, A, List.drop(&2, A, Con{y, t}, K.ksort.half(List.length(&2, A, t)))), 1n+List.length(&2, A, t), g, kp.drop_len(A, Con{y, t}, K.ksort.half(List.length(&2, A, t))), h)

def kp.sorted_msort(~A: Data, ~key: A -> Nat, +fuel: Nat, +xs: List<&2, A>, +h: {Nat.is_le(List.length(&2, A, xs), fuel) == True{} : Bool}) -> {S.ksort.sorted_by.from(~A, ~key, K.ksort.msort(~A, ~(a => b => Nat.is_le(key(a), key(b))), fuel, xs), 0n) == True{} : Bool}:
  match fuel xs:
    case 0n Nil{}:
      {==}
    case 0n Con{x, t}:
      Empty.absurd({S.ksort.sorted_by.from(~A, ~key, Con{x, t}, 0n) == True{} : Bool}, kp.ft(h))
    case 1n+g Nil{}:
      {==}
    case 1n+g Con{+x, Nil{}}:
      kp.and_i(Nat.is_le(0n, key(x)), True{}, kp.le_zero(key(x)), {==})
    case 1n+g Con{+x, Con{+y, +t}}:
      kp.sorted_merge(~A, ~key, K.ksort.msort(~A, ~(a => b => Nat.is_le(key(a), key(b))), g, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))), K.ksort.msort(~A, ~(a => b => Nat.is_le(key(a), key(b))), g, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))), kp.sorted_msort(~A, ~key, g, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))), kp.bound_take(A, x, y, t, g, h)), kp.sorted_msort(~A, ~key, g, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))), kp.bound_drop(A, x, y, t, g, h)))

def Laws.list_sort_by_sorted(A, key, xs):
  kp.sorted_msort(~A, ~key, List.length(&2, A, xs), xs, kp.le_refl(List.length(&2, A, xs)))

# Stable, for a sort by key: keeping the elements of one key commutes with
# the merge of sorted lists

def kp.kput_nil(-A: Data, b: Bool, -x: A, -l: List<&2, A>) -> {List.append(&2, A, S.ksort.keep.put(A, b, x, Nil{}), l) == S.ksort.keep.put(A, b, x, l) : List<&2, A>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def kp.kput_app(-A: Data, b: Bool, -x: A, -l: List<&2, A>, -m: List<&2, A>) -> {List.append(&2, A, S.ksort.keep.put(A, b, x, l), m) == S.ksort.keep.put(A, b, x, List.append(&2, A, l, m)) : List<&2, A>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def kp.le_of_eq(+a: Nat, -b: Nat, e: {a == b : Nat}) -> {Nat.is_le(b, a) == True{} : Bool}:
  %e : {Nat.is_le(_, a) == True{} : Bool}
  kp.le_refl(a)

# a list sorted from above k holds no element of key k
def kp.keep_none(~A: Data, ~key: A -> Nat, +l: List<&2, A>, +m: Nat, +k: Nat, +hs: {S.ksort.sorted_by.from(~A, ~key, l, m) == True{} : Bool}, +hl: {Nat.is_le(1n+k, m) == True{} : Bool}) -> {S.ksort.keep(~A, ~key, k, l) == Nil{} : List<&2, A>}:
  match l:
    case Nil{}:
      {==}
    case Con{+z, +t}:
      %Equal.sym(Bool, Nat.is_eq(key(z), k), False{}, kp.neq(key(z), k, kp.le_trans(1n+k, m, key(z), hl, kp.and_l(Nat.is_le(m, key(z)), S.ksort.sorted_by.from(~A, ~key, t, key(z)), hs)))) : {S.ksort.keep.put(A, _, z, S.ksort.keep(~A, ~key, k, t)) == Nil{} : List<&2, A>}
      kp.keep_none(~A, ~key, t, key(z), k, kp.and_r(Nat.is_le(m, key(z)), S.ksort.sorted_by.from(~A, ~key, t, key(z)), hs), kp.le_trans(1n+k, m, key(z), hl, kp.and_l(Nat.is_le(m, key(z)), S.ksort.sorted_by.from(~A, ~key, t, key(z)), hs)))

# key(y) < key(x), x <> xs sorted: when key(y) is k, x <> xs holds no key k
def kp.keep_above(~A: Data, ~key: A -> Nat, +x: A, +xs: List<&2, A>, +y: A, +k: Nat, eb: {Nat.is_eq(key(y), k) == True{} : Bool}, e: {Nat.is_le(key(x), key(y)) == False{} : Bool}, hx: {S.ksort.sorted_by.from(~A, ~key, xs, key(x)) == True{} : Bool}) -> {S.ksort.keep(~A, ~key, k, Con{x, xs}) == Nil{} : List<&2, A>}:
  kp.keep_none(~A, ~key, Con{x, xs}, 1n+key(y), k, kp.and_i(Nat.is_le(1n+key(y), key(x)), S.ksort.sorted_by.from(~A, ~key, xs, key(x)), kp.nle(key(x), key(y), e), hx), kp.le_of_eq(key(y), k, kp.eq(key(y), k, eb)))

def kp.keep_h1(~A: Data, ~key: A -> Nat, b: Bool, +x: A, +xs: List<&2, A>, +y: A, +k: Nat, eb: {Nat.is_eq(key(y), k) == b : Bool}, e: {Nat.is_le(key(x), key(y)) == False{} : Bool}, hx: {S.ksort.sorted_by.from(~A, ~key, xs, key(x)) == True{} : Bool}) -> {S.ksort.keep.put(A, b, y, S.ksort.keep(~A, ~key, k, Con{x, xs})) == List.append(&2, A, S.ksort.keep(~A, ~key, k, Con{x, xs}), S.ksort.keep.put(A, b, y, Nil{})) : List<&2, A>}:
  match b:
    case True{}:
      %Equal.sym(List<&2, A>, S.ksort.keep(~A, ~key, k, Con{x, xs}), Nil{}, kp.keep_above(~A, ~key, x, xs, y, k, eb, e, hx)) : {Con{y, _} == List.append(&2, A, _, Con{y, Nil{}}) : List<&2, A>}
      {==}
    case False{}:
      Equal.sym(List<&2, A>, List.append(&2, A, S.ksort.keep(~A, ~key, k, Con{x, xs}), Nil{}), S.ksort.keep(~A, ~key, k, Con{x, xs}), kp.append_nil(A, S.ksort.keep(~A, ~key, k, Con{x, xs})))

def kp.keep_h2(~A: Data, ~key: A -> Nat, b: Bool, +x: A, +xs: List<&2, A>, +y: A, +k: Nat, -r: List<&2, A>, eb: {Nat.is_eq(key(y), k) == b : Bool}, e: {Nat.is_le(key(x), key(y)) == False{} : Bool}, hx: {S.ksort.sorted_by.from(~A, ~key, xs, key(x)) == True{} : Bool}) -> {S.ksort.keep.put(A, b, y, List.append(&2, A, S.ksort.keep(~A, ~key, k, Con{x, xs}), r)) == List.append(&2, A, S.ksort.keep(~A, ~key, k, Con{x, xs}), S.ksort.keep.put(A, b, y, r)) : List<&2, A>}:
  match b:
    case True{}:
      %Equal.sym(List<&2, A>, S.ksort.keep(~A, ~key, k, Con{x, xs}), Nil{}, kp.keep_above(~A, ~key, x, xs, y, k, eb, e, hx)) : {Con{y, List.append(&2, A, _, r)} == List.append(&2, A, _, Con{y, r}) : List<&2, A>}
      {==}
    case False{}:
      {==}

def kp.keep_go(~A: Data, ~key: A -> Nat, +xt: List<&2, A>, +yt: List<&2, A>, c: Bool, +x: A, +y: A, +k: Nat, +e: {Nat.is_le(key(x), key(y)) == c : Bool}, +hx: {S.ksort.sorted_by.from(~A, ~key, xt, key(x)) == True{} : Bool}, +hy: {S.ksort.sorted_by.from(~A, ~key, yt, key(y)) == True{} : Bool}) -> {S.ksort.keep(~A, ~key, k, K.ksort.merge.go(~A, ~(a => b => Nat.is_le(key(a), key(b))), xt, yt, c, x, y)) == List.append(&2, A, S.ksort.keep(~A, ~key, k, Con{x, xt}), S.ksort.keep(~A, ~key, k, Con{y, yt})) : List<&2, A>}:
  match xt yt c:
    case Nil{} ys True{}:
      Equal.sym(List<&2, A>, List.append(&2, A, S.ksort.keep.put(A, Nat.is_eq(key(x), k), x, Nil{}), S.ksort.keep(~A, ~key, k, Con{y, ys})), S.ksort.keep.put(A, Nat.is_eq(key(x), k), x, S.ksort.keep(~A, ~key, k, Con{y, ys})), kp.kput_nil(A, Nat.is_eq(key(x), k), x, S.ksort.keep(~A, ~key, k, Con{y, ys})))
    case Con{+x2, xt2} ys True{}:
      %Equal.sym(List<&2, A>, List.append(&2, A, S.ksort.keep.put(A, Nat.is_eq(key(x), k), x, S.ksort.keep(~A, ~key, k, Con{x2, xt2})), S.ksort.keep(~A, ~key, k, Con{y, ys})), S.ksort.keep.put(A, Nat.is_eq(key(x), k), x, List.append(&2, A, S.ksort.keep(~A, ~key, k, Con{x2, xt2}), S.ksort.keep(~A, ~key, k, Con{y, ys}))), kp.kput_app(A, Nat.is_eq(key(x), k), x, S.ksort.keep(~A, ~key, k, Con{x2, xt2}), S.ksort.keep(~A, ~key, k, Con{y, ys}))) : {S.ksort.keep.put(A, Nat.is_eq(key(x), k), x, S.ksort.keep(~A, ~key, k, K.ksort.merge.go(~A, ~(a => b => Nat.is_le(key(a), key(b))), xt2, ys, Nat.is_le(key(x2), key(y)), x2, y))) == _ : List<&2, A>}
      %kp.keep_go(~A, ~key, xt2, ys, Nat.is_le(key(x2), key(y)), x2, y, k, {==}, kp.and_r(Nat.is_le(key(x), key(x2)), S.ksort.sorted_by.from(~A, ~key, xt2, key(x2)), hx), hy) : {S.ksort.keep.put(A, Nat.is_eq(key(x), k), x, S.ksort.keep(~A, ~key, k, K.ksort.merge.go(~A, ~(a => b => Nat.is_le(key(a), key(b))), xt2, ys, Nat.is_le(key(x2), key(y)), x2, y))) == S.ksort.keep.put(A, Nat.is_eq(key(x), k), x, _) : List<&2, A>}
      {==}
    case xs Nil{} False{}:
      kp.keep_h1(~A, ~key, Nat.is_eq(key(y), k), x, xs, y, k, {==}, e, hx)
    case xs Con{+y2, yt2} False{}:
      %Equal.sym(List<&2, A>, S.ksort.keep(~A, ~key, k, K.ksort.merge.go(~A, ~(a => b => Nat.is_le(key(a), key(b))), xs, yt2, Nat.is_le(key(x), key(y2)), x, y2)), List.append(&2, A, S.ksort.keep(~A, ~key, k, Con{x, xs}), S.ksort.keep(~A, ~key, k, Con{y2, yt2})), kp.keep_go(~A, ~key, xs, yt2, Nat.is_le(key(x), key(y2)), x, y2, k, {==}, hx, kp.and_r(Nat.is_le(key(y), key(y2)), S.ksort.sorted_by.from(~A, ~key, yt2, key(y2)), hy))) : {S.ksort.keep.put(A, Nat.is_eq(key(y), k), y, _) == List.append(&2, A, S.ksort.keep(~A, ~key, k, Con{x, xs}), S.ksort.keep.put(A, Nat.is_eq(key(y), k), y, S.ksort.keep(~A, ~key, k, Con{y2, yt2}))) : List<&2, A>}
      kp.keep_h2(~A, ~key, Nat.is_eq(key(y), k), x, xs, y, k, S.ksort.keep(~A, ~key, k, Con{y2, yt2}), {==}, e, hx)

def kp.keep_merge(~A: Data, ~key: A -> Nat, +xs: List<&2, A>, +ys: List<&2, A>, +k: Nat, +hxs: {S.ksort.sorted_by.from(~A, ~key, xs, 0n) == True{} : Bool}, +hys: {S.ksort.sorted_by.from(~A, ~key, ys, 0n) == True{} : Bool}) -> {S.ksort.keep(~A, ~key, k, K.ksort.merge(~A, ~(a => b => Nat.is_le(key(a), key(b))), xs, ys)) == List.append(&2, A, S.ksort.keep(~A, ~key, k, xs), S.ksort.keep(~A, ~key, k, ys)) : List<&2, A>}:
  match xs ys:
    case Nil{} b:
      {==}
    case Con{+x, +xt} Nil{}:
      Equal.sym(List<&2, A>, List.append(&2, A, S.ksort.keep(~A, ~key, k, Con{x, xt}), Nil{}), S.ksort.keep(~A, ~key, k, Con{x, xt}), kp.append_nil(A, S.ksort.keep(~A, ~key, k, Con{x, xt})))
    case Con{+x, +xt} Con{+y, +yt}:
      kp.keep_go(~A, ~key, xt, yt, Nat.is_le(key(x), key(y)), x, y, k, {==}, kp.and_r(Nat.is_le(0n, key(x)), S.ksort.sorted_by.from(~A, ~key, xt, key(x)), hxs), kp.and_r(Nat.is_le(0n, key(y)), S.ksort.sorted_by.from(~A, ~key, yt, key(y)), hys))

def kp.keep_app(~A: Data, ~key: A -> Nat, +a: List<&2, A>, +b: List<&2, A>, +k: Nat) -> {S.ksort.keep(~A, ~key, k, List.append(&2, A, a, b)) == List.append(&2, A, S.ksort.keep(~A, ~key, k, a), S.ksort.keep(~A, ~key, k, b)) : List<&2, A>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, A>, List.append(&2, A, S.ksort.keep.put(A, Nat.is_eq(key(h), k), h, S.ksort.keep(~A, ~key, k, t)), S.ksort.keep(~A, ~key, k, b)), S.ksort.keep.put(A, Nat.is_eq(key(h), k), h, List.append(&2, A, S.ksort.keep(~A, ~key, k, t), S.ksort.keep(~A, ~key, k, b))), kp.kput_app(A, Nat.is_eq(key(h), k), h, S.ksort.keep(~A, ~key, k, t), S.ksort.keep(~A, ~key, k, b))) : {S.ksort.keep.put(A, Nat.is_eq(key(h), k), h, S.ksort.keep(~A, ~key, k, List.append(&2, A, t, b))) == _ : List<&2, A>}
      %kp.keep_app(~A, ~key, t, b, k) : {S.ksort.keep.put(A, Nat.is_eq(key(h), k), h, S.ksort.keep(~A, ~key, k, List.append(&2, A, t, b))) == S.ksort.keep.put(A, Nat.is_eq(key(h), k), h, _) : List<&2, A>}
      {==}

def kp.keep_msort(~A: Data, ~key: A -> Nat, +fuel: Nat, +xs: List<&2, A>, +k: Nat, +h: {Nat.is_le(List.length(&2, A, xs), fuel) == True{} : Bool}) -> {S.ksort.keep(~A, ~key, k, K.ksort.msort(~A, ~(a => b => Nat.is_le(key(a), key(b))), fuel, xs)) == S.ksort.keep(~A, ~key, k, xs) : List<&2, A>}:
  match fuel xs:
    case 0n ys:
      {==}
    case 1n+g Nil{}:
      {==}
    case 1n+g Con{x, Nil{}}:
      {==}
    case 1n+g Con{+x, Con{+y, +t}}:
      %Equal.sym(List<&2, A>, S.ksort.keep(~A, ~key, k, K.ksort.merge(~A, ~(a => b => Nat.is_le(key(a), key(b))), K.ksort.msort(~A, ~(a => b => Nat.is_le(key(a), key(b))), g, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))), K.ksort.msort(~A, ~(a => b => Nat.is_le(key(a), key(b))), g, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))))), List.append(&2, A, S.ksort.keep(~A, ~key, k, K.ksort.msort(~A, ~(a => b => Nat.is_le(key(a), key(b))), g, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))))), S.ksort.keep(~A, ~key, k, K.ksort.msort(~A, ~(a => b => Nat.is_le(key(a), key(b))), g, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))))), kp.keep_merge(~A, ~key, K.ksort.msort(~A, ~(a => b => Nat.is_le(key(a), key(b))), g, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))), K.ksort.msort(~A, ~(a => b => Nat.is_le(key(a), key(b))), g, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))), k, kp.sorted_msort(~A, ~key, g, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))), kp.bound_take(A, x, y, t, g, h)), kp.sorted_msort(~A, ~key, g, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))), kp.bound_drop(A, x, y, t, g, h)))) : {_ == S.ksort.keep(~A, ~key, k, Con{x, Con{y, t}}) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ksort.keep(~A, ~key, k, K.ksort.msort(~A, ~(a => b => Nat.is_le(key(a), key(b))), g, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))))), S.ksort.keep(~A, ~key, k, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))), kp.keep_msort(~A, ~key, g, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))), k, kp.bound_take(A, x, y, t, g, h))) : {List.append(&2, A, _, S.ksort.keep(~A, ~key, k, K.ksort.msort(~A, ~(a => b => Nat.is_le(key(a), key(b))), g, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))))) == S.ksort.keep(~A, ~key, k, Con{x, Con{y, t}}) : List<&2, A>}
      %Equal.sym(List<&2, A>, S.ksort.keep(~A, ~key, k, K.ksort.msort(~A, ~(a => b => Nat.is_le(key(a), key(b))), g, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))))), S.ksort.keep(~A, ~key, k, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))), kp.keep_msort(~A, ~key, g, List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))), k, kp.bound_drop(A, x, y, t, g, h))) : {List.append(&2, A, S.ksort.keep(~A, ~key, k, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t)))), _) == S.ksort.keep(~A, ~key, k, Con{x, Con{y, t}}) : List<&2, A>}
      %kp.keep_app(~A, ~key, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))), List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))), k) : {_ == S.ksort.keep(~A, ~key, k, Con{x, Con{y, t}}) : List<&2, A>}
      %kp.take_drop(A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))) : {S.ksort.keep(~A, ~key, k, List.append(&2, A, List.take(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))), List.drop(&2, A, Con{x, Con{y, t}}, 1n+K.ksort.half(List.length(&2, A, t))))) == S.ksort.keep(~A, ~key, k, _) : List<&2, A>}
      {==}

def Laws.list_sort_by_stable(A, key, k, xs):
  kp.keep_msort(~A, ~key, List.length(&2, A, xs), xs, k, kp.le_refl(List.length(&2, A, xs)))

# Vectors

def Laws.vec_list_sort():
  {==}

def Laws.vec_list_sort_desc():
  {==}

def Laws.vec_list_sort_empty():
  {==}

def Laws.vec_list_sort_by_stable():
  {==}

# The Array heapsort: the code on an array built from a list is the model on
# the list (proof_heap.bend), and the model only swaps slots below n

def Laws.heap_sort_count(A, le, f, d, xs, fl, hl, hd, n):
  %Equal.sym(Array<A>, H.ksort.heap_sort(~A, ~le, AR.Arrays.of_list(A, d, xs, fl), n), AR.Arrays.of_list(A, d, HM.hm.sort(~A, ~le, d, fl, xs, n), fl), HM.hm.m_sort(~A, ~le, d, fl, xs, n, hl, hd)) : {S.ksort.count(~A, ~f, AR.Arrays.leaves(A, _)) == S.ksort.count(~A, ~f, xs) : Nat}
  %Equal.sym(List<&2, A>, AR.Arrays.leaves(A, AR.Arrays.of_list(A, d, HM.hm.sort(~A, ~le, d, fl, xs, n), fl)), HM.hm.sort(~A, ~le, d, fl, xs, n), AL.of_list_leaves(A, d, HM.hm.sort(~A, ~le, d, fl, xs, n), fl, HM.hm.l_sort(~A, ~le, d, fl, xs, n, hl))) : {S.ksort.count(~A, ~f, _) == S.ksort.count(~A, ~f, xs) : Nat}
  HM.hm.c_sort(~A, ~le, ~f, d, fl, xs, n, hl)

def Laws.heap_sort_rest(A, le, d, xs, fl, hl, hd, n, k, hk):
  %Equal.sym(Array<A>, H.ksort.heap_sort(~A, ~le, AR.Arrays.of_list(A, d, xs, fl), n), AR.Arrays.of_list(A, d, HM.hm.sort(~A, ~le, d, fl, xs, n), fl), HM.hm.m_sort(~A, ~le, d, fl, xs, n, hl, hd)) : {AR.Arrays.nth(A, AR.Arrays.leaves(A, _), k, fl) == AR.Arrays.nth(A, xs, k, fl) : A}
  %Equal.sym(List<&2, A>, AR.Arrays.leaves(A, AR.Arrays.of_list(A, d, HM.hm.sort(~A, ~le, d, fl, xs, n), fl)), HM.hm.sort(~A, ~le, d, fl, xs, n), AL.of_list_leaves(A, d, HM.hm.sort(~A, ~le, d, fl, xs, n), fl, HM.hm.l_sort(~A, ~le, d, fl, xs, n, hl))) : {AR.Arrays.nth(A, _, k, fl) == AR.Arrays.nth(A, xs, k, fl) : A}
  HM.hm.r_sort(~A, ~le, d, fl, xs, n, k, hk)

def Laws.heap_sort_perfect(A, le, d, xs, fl, hl, hd, n):
  %Equal.sym(Array<A>, H.ksort.heap_sort(~A, ~le, AR.Arrays.of_list(A, d, xs, fl), n), AR.Arrays.of_list(A, d, HM.hm.sort(~A, ~le, d, fl, xs, n), fl), HM.hm.m_sort(~A, ~le, d, fl, xs, n, hl, hd)) : {AR.Arrays.is_perfect(A, d, _) == True{} : Bool}
  AL.of_list_perfect(A, d, HM.hm.sort(~A, ~le, d, fl, xs, n), fl)

def Laws.vec_heap_sort():
  {==}
