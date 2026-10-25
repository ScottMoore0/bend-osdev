# Proof helpers for bend-osdev-ksort's heapsort: a list model of the Array
# code, the proof that the code on an array built from a list is the model
# on that list, and that the model only permutes the list.
#
# The model (hm.*) is the code with each Array.get of slot i replaced by the
# list's element at Arrays.index(d, i) and each Array.set by List.set there,
# as bend-osdev-array's of_list_get and of_list_set say an array built by
# Arrays.of_list(d, xs, fl) behaves. Every change the model makes goes
# through hm.swap, which exchanges two elements, so each predicate counts
# the same elements before and after.
import Base
import ./spec.bend as S
import ./heapsort.bend as H
import ../array/array.bend as AR
import ../array/LAWS.bend as AL
import ../array/PROOF.bend as APF
import ../u32/LAWS.bend as UL
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF.bend as UP
import ../u32/PROOF_order.bend as UOP

# Contradictions

def hm.bt(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def hm.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : hm.bt(_)
  Unit{}

def hm.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : hm.bt(_)
  Unit{}

# The model

type KpHeap<-A: Data> is Data:
  KpHeap{xs: List<&2, A>, n: U32, i: U32, live: Bool}

def hm.get(~A: Data, +d: Nat, xs: List<&2, A>, i: U32, fl: A) -> A:
  AR.Arrays.nth(A, xs, AR.Arrays.index(d, i), fl)

def hm.set(~A: Data, +d: Nat, xs: List<&2, A>, i: U32, v: A) -> List<&2, A>:
  List.set(&2, A, xs, AR.Arrays.index(d, i), v)

def hm.swap.at(~A: Data, ok: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +i: U32, +j: U32) -> List<&2, A>:
  match ok:
    case True{}:
      hm.set(~A, d, hm.set(~A, d, xs, i, hm.get(~A, d, xs, j, fl)), j, hm.get(~A, d, xs, i, fl))
    case False{}:
      xs

def hm.swap(~A: Data, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +i: U32, +j: U32) -> List<&2, A>:
  hm.swap.at(~A, Bool.and(U32.is_lt(i, lim), U32.is_lt(j, lim)), d, fl, xs, i, j)

def hm.decide(~A: Data, stop: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +m: U32) -> KpHeap<A>:
  match stop:
    case True{}:
      KpHeap{xs, n, i, False{}}
    case False{}:
      KpHeap{hm.swap(~A, d, fl, xs, lim, i, m), n, m, True{}}

def hm.cmp(~A: Data, ~le: A -> A -> Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +m: U32) -> KpHeap<A>:
  hm.decide(~A, le(hm.get(~A, d, xs, m, fl), hm.get(~A, d, xs, i, fl)), d, fl, xs, lim, n, i, m)

def hm.pick(~A: Data, ~le: A -> A -> Bool, two: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +c: U32) -> KpHeap<A>:
  match two:
    case True{}:
      hm.cmp(~A, ~le, d, fl, xs, lim, n, i, Bool.pick(U32, le(hm.get(~A, d, xs, c, fl), hm.get(~A, d, xs, U32.inc(c), fl)), U32.inc(c), c))
    case False{}:
      hm.cmp(~A, ~le, d, fl, xs, lim, n, i, c)

def hm.child(~A: Data, ~le: A -> A -> Bool, has: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +c: U32) -> KpHeap<A>:
  match has:
    case True{}:
      hm.pick(~A, ~le, U32.is_lt(U32.inc(c), n), d, fl, xs, lim, n, i, c)
    case False{}:
      KpHeap{xs, n, i, False{}}

def hm.live(~A: Data, ~le: A -> A -> Bool, live: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32) -> KpHeap<A>:
  match live:
    case True{}:
      hm.child(~A, ~le, Bool.and(U32.is_lt(U32.inc(U32.shl(i)), n), U32.is_lt(i, U32.inc(U32.shl(i)))), d, fl, xs, lim, n, i, U32.inc(U32.shl(i)))
    case False{}:
      KpHeap{xs, n, i, False{}}

def hm.step(~A: Data, ~le: A -> A -> Bool, +d: Nat, +fl: A, +lim: U32, st: KpHeap<A>) -> KpHeap<A>:
  match st:
    case KpHeap{+xs, +n, +i, live}:
      hm.live(~A, ~le, live, d, fl, xs, lim, n, i)

def hm.sift(~A: Data, ~le: A -> A -> Bool, fuel: Nat, +d: Nat, +fl: A, +lim: U32, st: KpHeap<A>) -> KpHeap<A>:
  match fuel:
    case 0n:
      st
    case 1n+f:
      hm.sift(~A, ~le, f, d, fl, lim, hm.step(~A, ~le, d, fl, lim, st))

def hm.xs(~A: Data, st: KpHeap<A>) -> List<&2, A>:
  match st:
    case KpHeap{xs, n, i, live}:
      xs

def hm.sift_down(~A: Data, ~le: A -> A -> Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32) -> List<&2, A>:
  hm.xs(~A, hm.sift(~A, ~le, 33n, d, fl, lim, KpHeap{xs, n, i, True{}}))

def hm.build(~A: Data, ~le: A -> A -> Bool, fuel: Nat, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32) -> List<&2, A>:
  match fuel:
    case 0n:
      xs
    case 1n+f:
      hm.build(~A, ~le, f, d, fl, hm.sift_down(~A, ~le, d, fl, xs, lim, n, U32.sub(i, 1)), lim, n, U32.sub(i, 1))

def hm.drain(~A: Data, ~le: A -> A -> Bool, fuel: Nat, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +m: U32) -> List<&2, A>:
  match fuel:
    case 0n:
      xs
    case 1n+f:
      hm.drain(~A, ~le, f, d, fl, hm.sift_down(~A, ~le, d, fl, hm.swap(~A, d, fl, xs, lim, 0, U32.sub(m, 1)), lim, U32.sub(m, 1), 0), lim, U32.sub(m, 1))

def hm.sort(~A: Data, ~le: A -> A -> Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +n: U32) -> List<&2, A>:
  hm.drain(~A, ~le, Nat.sub(U32.to_nat(n), 1n), d, fl, hm.build(~A, ~le, U32.to_nat(U32.shr(n)), d, fl, xs, n, n, U32.shr(n)), n, n)

# the array state of a model state
def hm.emb(~A: Data, +d: Nat, +fl: A, +lim: U32, st: KpHeap<A>) -> H.KsortHeap<A>:
  match st:
    case KpHeap{xs, n, i, live}:
      H.KsortHeap{AR.Arrays.of_list(A, d, xs, fl), lim, n, i, live}

# Counting

def hm.cadd_comm(b1: Bool, b2: Bool, -n: Nat) -> {S.ksort.count.add(b1, S.ksort.count.add(b2, n)) == S.ksort.count.add(b2, S.ksort.count.add(b1, n)) : Nat}:
  match b1 b2:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def hm.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def hm.cadd_inj(b: Bool, -x: Nat, -y: Nat, e: {S.ksort.count.add(b, x) == S.ksort.count.add(b, y) : Nat}) -> {x == y : Nat}:
  match b:
    case True{}:
      Equal.cong(Nat, Nat, n => hm.pred(n), 1n+x, 1n+y, e)
    case False{}:
      e

def hm.lt0(m: Nat) -> {Nat.is_lt(m, 0n) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

# writing v at k < length changes the count by what v and the old element
# count
def hm.count_set(~A: Data, ~f: A -> Bool, +xs: List<&2, A>, +k: Nat, +v: A, +fl: A, hk: {Nat.is_lt(k, List.length(&2, A, xs)) == True{} : Bool}) -> {S.ksort.count.add(f(AR.Arrays.nth(A, xs, k, fl)), S.ksort.count(~A, ~f, List.set(&2, A, xs, k, v))) == S.ksort.count.add(f(v), S.ksort.count(~A, ~f, xs)) : Nat}:
  match xs k:
    case Nil{} +m:
      Empty.absurd({S.ksort.count.add(f(AR.Arrays.nth(A, Nil{}, m, fl)), S.ksort.count(~A, ~f, List.set(&2, A, Nil{}, m, v))) == S.ksort.count.add(f(v), 0n) : Nat}, hm.ft(Equal.trans(Bool, False{}, Nat.is_lt(m, 0n), True{}, Equal.sym(Bool, Nat.is_lt(m, 0n), False{}, hm.lt0(m)), hk)))
    case Con{+h, +t} 0n:
      hm.cadd_comm(f(h), f(v), S.ksort.count(~A, ~f, t))
    case Con{+h, +t} 1n+p:
      %Equal.sym(Nat, S.ksort.count.add(f(AR.Arrays.nth(A, t, p, fl)), S.ksort.count.add(f(h), S.ksort.count(~A, ~f, List.set(&2, A, t, p, v)))), S.ksort.count.add(f(h), S.ksort.count.add(f(AR.Arrays.nth(A, t, p, fl)), S.ksort.count(~A, ~f, List.set(&2, A, t, p, v)))), hm.cadd_comm(f(AR.Arrays.nth(A, t, p, fl)), f(h), S.ksort.count(~A, ~f, List.set(&2, A, t, p, v)))) : {_ == S.ksort.count.add(f(v), S.ksort.count.add(f(h), S.ksort.count(~A, ~f, t))) : Nat}
      %Equal.sym(Nat, S.ksort.count.add(f(AR.Arrays.nth(A, t, p, fl)), S.ksort.count(~A, ~f, List.set(&2, A, t, p, v))), S.ksort.count.add(f(v), S.ksort.count(~A, ~f, t)), hm.count_set(~A, ~f, t, p, v, fl, hk)) : {S.ksort.count.add(f(h), _) == S.ksort.count.add(f(v), S.ksort.count.add(f(h), S.ksort.count(~A, ~f, t))) : Nat}
      hm.cadd_comm(f(h), f(v), S.ksort.count(~A, ~f, t))

def hm.eq(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, hm.ft(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, hm.ft(e))
    case 1n+ap 1n+bp:
      %hm.eq(ap, bp, e) : {1n+ap == 1n+_ : Nat}
      {==}

# a slot index is below the length of a model of 2^d elements
def hm.idx_lt(~A: Data, +d: Nat, +xs: List<&2, A>, +i: U32, hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {Nat.is_lt(AR.Arrays.index(d, i), List.length(&2, A, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, A, xs), AR.Arrays.slots(d), hl) : {Nat.is_lt(AR.Arrays.index(d, i), _) == True{} : Bool}
  AL.index_below(d, i)

# after writing y at p, the element at q is y when it was y before
def hm.nth_swap(~A: Data, b: Bool, +xs: List<&2, A>, +p: Nat, +q: Nat, +fl: A, eb: {Nat.is_eq(p, q) == b : Bool}, hp: {Nat.is_lt(p, List.length(&2, A, xs)) == True{} : Bool}) -> {AR.Arrays.nth(A, List.set(&2, A, xs, p, AR.Arrays.nth(A, xs, q, fl)), q, fl) == AR.Arrays.nth(A, xs, q, fl) : A}:
  match b:
    case True{}:
      %hm.eq(p, q, eb) : {AR.Arrays.nth(A, List.set(&2, A, xs, p, AR.Arrays.nth(A, xs, _, fl)), _, fl) == AR.Arrays.nth(A, xs, _, fl) : A}
      AL.nth_set_same(A, xs, p, AR.Arrays.nth(A, xs, p, fl), fl, hp)
    case False{}:
      AL.nth_set_other(A, xs, p, q, AR.Arrays.nth(A, xs, q, fl), fl, eb)

def hm.c_swap_true(~A: Data, ~f: A -> Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +i: U32, +j: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {S.ksort.count(~A, ~f, hm.swap.at(~A, True{}, d, fl, xs, i, j)) == S.ksort.count(~A, ~f, xs) : Nat}:
  +p = AR.Arrays.index(d, i)
  +q = AR.Arrays.index(d, j)
  +x = AR.Arrays.nth(A, xs, p, fl)
  +y = AR.Arrays.nth(A, xs, q, fl)
  +s1 = List.set(&2, A, xs, p, y)
  +hq1 = Equal.trans(Bool, Nat.is_lt(q, List.length(&2, A, s1)), Nat.is_lt(q, List.length(&2, A, xs)), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(q, z), List.length(&2, A, s1), List.length(&2, A, xs), AL.set_length(A, xs, p, y)), hm.idx_lt(~A, d, xs, j, hl))
  +e1 = hm.count_set(~A, ~f, s1, q, x, fl, hq1)
  +e2 = hm.count_set(~A, ~f, xs, p, y, fl, hm.idx_lt(~A, d, xs, i, hl))
  +e3 = hm.nth_swap(~A, Nat.is_eq(p, q), xs, p, q, fl, {==}, hm.idx_lt(~A, d, xs, i, hl))
  hm.cadd_inj(f(y), S.ksort.count(~A, ~f, List.set(&2, A, s1, q, x)), S.ksort.count(~A, ~f, xs), Equal.trans(Nat, S.ksort.count.add(f(y), S.ksort.count(~A, ~f, List.set(&2, A, s1, q, x))), S.ksort.count.add(f(x), S.ksort.count(~A, ~f, s1)), S.ksort.count.add(f(y), S.ksort.count(~A, ~f, xs)), Equal.trans(Nat, S.ksort.count.add(f(y), S.ksort.count(~A, ~f, List.set(&2, A, s1, q, x))), S.ksort.count.add(f(AR.Arrays.nth(A, s1, q, fl)), S.ksort.count(~A, ~f, List.set(&2, A, s1, q, x))), S.ksort.count.add(f(x), S.ksort.count(~A, ~f, s1)), Equal.cong(A, Nat, z => S.ksort.count.add(f(z), S.ksort.count(~A, ~f, List.set(&2, A, s1, q, x))), y, AR.Arrays.nth(A, s1, q, fl), Equal.sym(A, AR.Arrays.nth(A, s1, q, fl), y, e3)), e1), e2))

def hm.c_swap_at(~A: Data, ~f: A -> Bool, b: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +i: U32, +j: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {S.ksort.count(~A, ~f, hm.swap.at(~A, b, d, fl, xs, i, j)) == S.ksort.count(~A, ~f, xs) : Nat}:
  match b:
    case True{}:
      hm.c_swap_true(~A, ~f, d, fl, xs, i, j, hl)
    case False{}:
      {==}

def hm.c_swap(~A: Data, ~f: A -> Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +i: U32, +j: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {S.ksort.count(~A, ~f, hm.swap(~A, d, fl, xs, lim, i, j)) == S.ksort.count(~A, ~f, xs) : Nat}:
  hm.c_swap_at(~A, ~f, Bool.and(U32.is_lt(i, lim), U32.is_lt(j, lim)), d, fl, xs, i, j, hl)

def hm.c_decide(~A: Data, ~f: A -> Bool, stop: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +m: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {S.ksort.count(~A, ~f, hm.xs(~A, hm.decide(~A, stop, d, fl, xs, lim, n, i, m))) == S.ksort.count(~A, ~f, xs) : Nat}:
  match stop:
    case True{}:
      {==}
    case False{}:
      hm.c_swap(~A, ~f, d, fl, xs, lim, i, m, hl)

def hm.c_cmp(~A: Data, ~le: A -> A -> Bool, ~f: A -> Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +m: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {S.ksort.count(~A, ~f, hm.xs(~A, hm.cmp(~A, ~le, d, fl, xs, lim, n, i, m))) == S.ksort.count(~A, ~f, xs) : Nat}:
  hm.c_decide(~A, ~f, le(hm.get(~A, d, xs, m, fl), hm.get(~A, d, xs, i, fl)), d, fl, xs, lim, n, i, m, hl)

def hm.c_pick(~A: Data, ~le: A -> A -> Bool, ~f: A -> Bool, two: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +c: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {S.ksort.count(~A, ~f, hm.xs(~A, hm.pick(~A, ~le, two, d, fl, xs, lim, n, i, c))) == S.ksort.count(~A, ~f, xs) : Nat}:
  match two:
    case True{}:
      hm.c_cmp(~A, ~le, ~f, d, fl, xs, lim, n, i, Bool.pick(U32, le(hm.get(~A, d, xs, c, fl), hm.get(~A, d, xs, U32.inc(c), fl)), U32.inc(c), c), hl)
    case False{}:
      hm.c_cmp(~A, ~le, ~f, d, fl, xs, lim, n, i, c, hl)

def hm.c_child(~A: Data, ~le: A -> A -> Bool, ~f: A -> Bool, has: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +c: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {S.ksort.count(~A, ~f, hm.xs(~A, hm.child(~A, ~le, has, d, fl, xs, lim, n, i, c))) == S.ksort.count(~A, ~f, xs) : Nat}:
  match has:
    case True{}:
      hm.c_pick(~A, ~le, ~f, U32.is_lt(U32.inc(c), n), d, fl, xs, lim, n, i, c, hl)
    case False{}:
      {==}

def hm.c_live(~A: Data, ~le: A -> A -> Bool, ~f: A -> Bool, live: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {S.ksort.count(~A, ~f, hm.xs(~A, hm.live(~A, ~le, live, d, fl, xs, lim, n, i))) == S.ksort.count(~A, ~f, xs) : Nat}:
  match live:
    case True{}:
      hm.c_child(~A, ~le, ~f, Bool.and(U32.is_lt(U32.inc(U32.shl(i)), n), U32.is_lt(i, U32.inc(U32.shl(i)))), d, fl, xs, lim, n, i, U32.inc(U32.shl(i)), hl)
    case False{}:
      {==}

def hm.c_step(~A: Data, ~le: A -> A -> Bool, ~f: A -> Bool, +d: Nat, +fl: A, +lim: U32, +st: KpHeap<A>, +hl: {List.length(&2, A, hm.xs(~A, st)) == AR.Arrays.slots(d) : Nat}) -> {S.ksort.count(~A, ~f, hm.xs(~A, hm.step(~A, ~le, d, fl, lim, st))) == S.ksort.count(~A, ~f, hm.xs(~A, st)) : Nat}:
  match st:
    case KpHeap{xs, n, i, live}:
      hm.c_live(~A, ~le, ~f, live, d, fl, xs, lim, n, i, hl)

# the predicate every element satisfies counts the length
def hm.yes(~A: Data, x: A) -> Bool:
  True{}

def hm.count_true(~A: Data, xs: List<&2, A>) -> {S.ksort.count(~A, ~(x => hm.yes(~A, x)), xs) == List.length(&2, A, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %hm.count_true(~A, t) : {1n+S.ksort.count(~A, ~(x => hm.yes(~A, x)), t) == 1n+_ : Nat}
      {==}

# lengths follow from counts: two lists every predicate counts alike have
# the same length
def hm.len_of(~A: Data, +xs: List<&2, A>, +ys: List<&2, A>, -L: Nat, e: {S.ksort.count(~A, ~(x => hm.yes(~A, x)), ys) == S.ksort.count(~A, ~(x => hm.yes(~A, x)), xs) : Nat}, hl: {List.length(&2, A, xs) == L : Nat}) -> {List.length(&2, A, ys) == L : Nat}:
  Equal.trans(Nat, List.length(&2, A, ys), S.ksort.count(~A, ~(x => hm.yes(~A, x)), xs), L, Equal.trans(Nat, List.length(&2, A, ys), S.ksort.count(~A, ~(x => hm.yes(~A, x)), ys), S.ksort.count(~A, ~(x => hm.yes(~A, x)), xs), Equal.sym(Nat, S.ksort.count(~A, ~(x => hm.yes(~A, x)), ys), List.length(&2, A, ys), hm.count_true(~A, ys)), e), Equal.trans(Nat, S.ksort.count(~A, ~(x => hm.yes(~A, x)), xs), List.length(&2, A, xs), L, hm.count_true(~A, xs), hl))

def hm.l_step(~A: Data, ~le: A -> A -> Bool, +d: Nat, +fl: A, +lim: U32, +st: KpHeap<A>, +hl: {List.length(&2, A, hm.xs(~A, st)) == AR.Arrays.slots(d) : Nat}) -> {List.length(&2, A, hm.xs(~A, hm.step(~A, ~le, d, fl, lim, st))) == AR.Arrays.slots(d) : Nat}:
  hm.len_of(~A, hm.xs(~A, st), hm.xs(~A, hm.step(~A, ~le, d, fl, lim, st)), AR.Arrays.slots(d), hm.c_step(~A, ~le, ~(x => hm.yes(~A, x)), d, fl, lim, st, hl), hl)

def hm.c_sift(~A: Data, ~le: A -> A -> Bool, ~f: A -> Bool, +fuel: Nat, +d: Nat, +fl: A, +lim: U32, +st: KpHeap<A>, +hl: {List.length(&2, A, hm.xs(~A, st)) == AR.Arrays.slots(d) : Nat}) -> {S.ksort.count(~A, ~f, hm.xs(~A, hm.sift(~A, ~le, fuel, d, fl, lim, st))) == S.ksort.count(~A, ~f, hm.xs(~A, st)) : Nat}:
  match fuel:
    case 0n:
      {==}
    case 1n+g:
      Equal.trans(Nat, S.ksort.count(~A, ~f, hm.xs(~A, hm.sift(~A, ~le, g, d, fl, lim, hm.step(~A, ~le, d, fl, lim, st)))), S.ksort.count(~A, ~f, hm.xs(~A, hm.step(~A, ~le, d, fl, lim, st))), S.ksort.count(~A, ~f, hm.xs(~A, st)), hm.c_sift(~A, ~le, ~f, g, d, fl, lim, hm.step(~A, ~le, d, fl, lim, st), hm.l_step(~A, ~le, d, fl, lim, st, hl)), hm.c_step(~A, ~le, ~f, d, fl, lim, st, hl))

def hm.c_sd(~A: Data, ~le: A -> A -> Bool, ~f: A -> Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {S.ksort.count(~A, ~f, hm.sift_down(~A, ~le, d, fl, xs, lim, n, i)) == S.ksort.count(~A, ~f, xs) : Nat}:
  hm.c_sift(~A, ~le, ~f, 33n, d, fl, lim, KpHeap{xs, n, i, True{}}, hl)

def hm.l_sd(~A: Data, ~le: A -> A -> Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {List.length(&2, A, hm.sift_down(~A, ~le, d, fl, xs, lim, n, i)) == AR.Arrays.slots(d) : Nat}:
  hm.len_of(~A, xs, hm.sift_down(~A, ~le, d, fl, xs, lim, n, i), AR.Arrays.slots(d), hm.c_sd(~A, ~le, ~(x => hm.yes(~A, x)), d, fl, xs, lim, n, i, hl), hl)

def hm.l_swap(~A: Data, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +i: U32, +j: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {List.length(&2, A, hm.swap(~A, d, fl, xs, lim, i, j)) == AR.Arrays.slots(d) : Nat}:
  hm.len_of(~A, xs, hm.swap(~A, d, fl, xs, lim, i, j), AR.Arrays.slots(d), hm.c_swap(~A, ~(x => hm.yes(~A, x)), d, fl, xs, lim, i, j, hl), hl)

def hm.c_build(~A: Data, ~le: A -> A -> Bool, ~f: A -> Bool, fuel: Nat, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {S.ksort.count(~A, ~f, hm.build(~A, ~le, fuel, d, fl, xs, lim, n, i)) == S.ksort.count(~A, ~f, xs) : Nat}:
  match fuel:
    case 0n:
      {==}
    case 1n+g:
      Equal.trans(Nat, S.ksort.count(~A, ~f, hm.build(~A, ~le, g, d, fl, hm.sift_down(~A, ~le, d, fl, xs, lim, n, U32.sub(i, 1)), lim, n, U32.sub(i, 1))), S.ksort.count(~A, ~f, hm.sift_down(~A, ~le, d, fl, xs, lim, n, U32.sub(i, 1))), S.ksort.count(~A, ~f, xs), hm.c_build(~A, ~le, ~f, g, d, fl, hm.sift_down(~A, ~le, d, fl, xs, lim, n, U32.sub(i, 1)), lim, n, U32.sub(i, 1), hm.l_sd(~A, ~le, d, fl, xs, lim, n, U32.sub(i, 1), hl)), hm.c_sd(~A, ~le, ~f, d, fl, xs, lim, n, U32.sub(i, 1), hl))

def hm.l_build(~A: Data, ~le: A -> A -> Bool, +fuel: Nat, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {List.length(&2, A, hm.build(~A, ~le, fuel, d, fl, xs, lim, n, i)) == AR.Arrays.slots(d) : Nat}:
  hm.len_of(~A, xs, hm.build(~A, ~le, fuel, d, fl, xs, lim, n, i), AR.Arrays.slots(d), hm.c_build(~A, ~le, ~(x => hm.yes(~A, x)), fuel, d, fl, xs, lim, n, i, hl), hl)

def hm.c_drain(~A: Data, ~le: A -> A -> Bool, ~f: A -> Bool, fuel: Nat, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +m: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {S.ksort.count(~A, ~f, hm.drain(~A, ~le, fuel, d, fl, xs, lim, m)) == S.ksort.count(~A, ~f, xs) : Nat}:
  match fuel:
    case 0n:
      {==}
    case 1n+g:
      +ys = hm.swap(~A, d, fl, xs, lim, 0, U32.sub(m, 1))
      +hy = hm.l_swap(~A, d, fl, xs, lim, 0, U32.sub(m, 1), hl)
      +zs = hm.sift_down(~A, ~le, d, fl, ys, lim, U32.sub(m, 1), 0)
      Equal.trans(Nat, S.ksort.count(~A, ~f, hm.drain(~A, ~le, g, d, fl, zs, lim, U32.sub(m, 1))), S.ksort.count(~A, ~f, ys), S.ksort.count(~A, ~f, xs), Equal.trans(Nat, S.ksort.count(~A, ~f, hm.drain(~A, ~le, g, d, fl, zs, lim, U32.sub(m, 1))), S.ksort.count(~A, ~f, zs), S.ksort.count(~A, ~f, ys), hm.c_drain(~A, ~le, ~f, g, d, fl, zs, lim, U32.sub(m, 1), hm.l_sd(~A, ~le, d, fl, ys, lim, U32.sub(m, 1), 0, hy)), hm.c_sd(~A, ~le, ~f, d, fl, ys, lim, U32.sub(m, 1), 0, hy)), hm.c_swap(~A, ~f, d, fl, xs, lim, 0, U32.sub(m, 1), hl))

def hm.c_sort(~A: Data, ~le: A -> A -> Bool, ~f: A -> Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +n: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {S.ksort.count(~A, ~f, hm.sort(~A, ~le, d, fl, xs, n)) == S.ksort.count(~A, ~f, xs) : Nat}:
  +ys = hm.build(~A, ~le, U32.to_nat(U32.shr(n)), d, fl, xs, n, n, U32.shr(n))
  Equal.trans(Nat, S.ksort.count(~A, ~f, hm.drain(~A, ~le, Nat.sub(U32.to_nat(n), 1n), d, fl, ys, n, n)), S.ksort.count(~A, ~f, ys), S.ksort.count(~A, ~f, xs), hm.c_drain(~A, ~le, ~f, Nat.sub(U32.to_nat(n), 1n), d, fl, ys, n, n, hm.l_build(~A, ~le, U32.to_nat(U32.shr(n)), d, fl, xs, n, n, U32.shr(n), hl)), hm.c_build(~A, ~le, ~f, U32.to_nat(U32.shr(n)), d, fl, xs, n, n, U32.shr(n), hl))

def hm.l_sort(~A: Data, ~le: A -> A -> Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +n: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}) -> {List.length(&2, A, hm.sort(~A, ~le, d, fl, xs, n)) == AR.Arrays.slots(d) : Nat}:
  hm.len_of(~A, xs, hm.sort(~A, ~le, d, fl, xs, n), AR.Arrays.slots(d), hm.c_sort(~A, ~le, ~(x => hm.yes(~A, x)), d, fl, xs, n, hl), hl)

# The code on an array built from a list is the model on the list

def hm.m_swap_at(~A: Data, ok: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +i: U32, +j: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {H.ksort.heap.swap.at(~A, ok, AR.Arrays.of_list(A, d, xs, fl), i, j) == AR.Arrays.of_list(A, d, hm.swap.at(~A, ok, d, fl, xs, i, j), fl) : Array<A>}:
  match ok:
    case True{}:
      +xi = hm.get(~A, d, xs, i, fl)
      +xj = hm.get(~A, d, xs, j, fl)
      +xs1 = hm.set(~A, d, xs, i, xj)
      %Equal.sym(Array<A> & A, Array.get(A, AR.Arrays.of_list(A, d, xs, fl), i), (AR.Arrays.of_list(A, d, xs, fl), xi), AL.of_list_get(A, d, xs, fl, hl, hd, i)) : {H.ksort.heap.swap.got(~A, _, i, j) == AR.Arrays.of_list(A, d, hm.set(~A, d, xs1, j, xi), fl) : Array<A>}
      %Equal.sym(Array<A> & A, Array.get(A, AR.Arrays.of_list(A, d, xs, fl), j), (AR.Arrays.of_list(A, d, xs, fl), xj), AL.of_list_get(A, d, xs, fl, hl, hd, j)) : {H.ksort.heap.swap.got2(~A, _, i, j, xi) == AR.Arrays.of_list(A, d, hm.set(~A, d, xs1, j, xi), fl) : Array<A>}
      %Equal.sym(Array<A>, Array.set(A, AR.Arrays.of_list(A, d, xs, fl), i, xj), AR.Arrays.of_list(A, d, xs1, fl), AL.of_list_set(A, d, xs, fl, hl, hd, i, xj)) : {Array.set(A, _, j, xi) == AR.Arrays.of_list(A, d, hm.set(~A, d, xs1, j, xi), fl) : Array<A>}
      AL.of_list_set(A, d, xs1, fl, Equal.trans(Nat, List.length(&2, A, xs1), List.length(&2, A, xs), AR.Arrays.slots(d), AL.set_length(A, xs, AR.Arrays.index(d, i), xj), hl), hd, j, xi)
    case False{}:
      {==}

def hm.m_swap(~A: Data, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +i: U32, +j: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {H.ksort.heap.swap(~A, AR.Arrays.of_list(A, d, xs, fl), lim, i, j) == AR.Arrays.of_list(A, d, hm.swap(~A, d, fl, xs, lim, i, j), fl) : Array<A>}:
  hm.m_swap_at(~A, Bool.and(U32.is_lt(i, lim), U32.is_lt(j, lim)), d, fl, xs, i, j, hl, hd)

def hm.m_decide(~A: Data, stop: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +m: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {H.ksort.heap.decide(~A, stop, AR.Arrays.of_list(A, d, xs, fl), lim, n, i, m) == hm.emb(~A, d, fl, lim, hm.decide(~A, stop, d, fl, xs, lim, n, i, m)) : H.KsortHeap<A>}:
  match stop:
    case True{}:
      {==}
    case False{}:
      %hm.m_swap(~A, d, fl, xs, lim, i, m, hl, hd) : {H.KsortHeap{H.ksort.heap.swap(~A, AR.Arrays.of_list(A, d, xs, fl), lim, i, m), lim, n, m, True{}} == H.KsortHeap{_, lim, n, m, True{}} : H.KsortHeap<A>}
      {==}

def hm.m_cmp(~A: Data, ~le: A -> A -> Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +m: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {H.ksort.heap.cmp(~A, ~le, AR.Arrays.of_list(A, d, xs, fl), lim, n, i, m) == hm.emb(~A, d, fl, lim, hm.cmp(~A, ~le, d, fl, xs, lim, n, i, m)) : H.KsortHeap<A>}:
  +xi = hm.get(~A, d, xs, i, fl)
  +xm = hm.get(~A, d, xs, m, fl)
  %Equal.sym(Array<A> & A, Array.get(A, AR.Arrays.of_list(A, d, xs, fl), i), (AR.Arrays.of_list(A, d, xs, fl), xi), AL.of_list_get(A, d, xs, fl, hl, hd, i)) : {H.ksort.heap.cmp.got(~A, ~le, _, lim, n, i, m) == hm.emb(~A, d, fl, lim, hm.cmp(~A, ~le, d, fl, xs, lim, n, i, m)) : H.KsortHeap<A>}
  %Equal.sym(Array<A> & A, Array.get(A, AR.Arrays.of_list(A, d, xs, fl), m), (AR.Arrays.of_list(A, d, xs, fl), xm), AL.of_list_get(A, d, xs, fl, hl, hd, m)) : {H.ksort.heap.cmp.got2(~A, ~le, _, lim, n, i, m, xi) == hm.emb(~A, d, fl, lim, hm.cmp(~A, ~le, d, fl, xs, lim, n, i, m)) : H.KsortHeap<A>}
  hm.m_decide(~A, le(xm, xi), d, fl, xs, lim, n, i, m, hl, hd)

def hm.m_pick(~A: Data, ~le: A -> A -> Bool, two: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +c: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {H.ksort.heap.pick(~A, ~le, two, AR.Arrays.of_list(A, d, xs, fl), lim, n, i, c) == hm.emb(~A, d, fl, lim, hm.pick(~A, ~le, two, d, fl, xs, lim, n, i, c)) : H.KsortHeap<A>}:
  match two:
    case True{}:
      +xc = hm.get(~A, d, xs, c, fl)
      +xd = hm.get(~A, d, xs, U32.inc(c), fl)
      %Equal.sym(Array<A> & A, Array.get(A, AR.Arrays.of_list(A, d, xs, fl), c), (AR.Arrays.of_list(A, d, xs, fl), xc), AL.of_list_get(A, d, xs, fl, hl, hd, c)) : {H.ksort.heap.pick.got(~A, ~le, _, lim, n, i, c, U32.inc(c)) == hm.emb(~A, d, fl, lim, hm.pick(~A, ~le, True{}, d, fl, xs, lim, n, i, c)) : H.KsortHeap<A>}
      %Equal.sym(Array<A> & A, Array.get(A, AR.Arrays.of_list(A, d, xs, fl), U32.inc(c)), (AR.Arrays.of_list(A, d, xs, fl), xd), AL.of_list_get(A, d, xs, fl, hl, hd, U32.inc(c))) : {H.ksort.heap.pick.got2(~A, ~le, _, lim, n, i, c, U32.inc(c), xc) == hm.emb(~A, d, fl, lim, hm.pick(~A, ~le, True{}, d, fl, xs, lim, n, i, c)) : H.KsortHeap<A>}
      hm.m_cmp(~A, ~le, d, fl, xs, lim, n, i, Bool.pick(U32, le(xc, xd), U32.inc(c), c), hl, hd)
    case False{}:
      hm.m_cmp(~A, ~le, d, fl, xs, lim, n, i, c, hl, hd)

def hm.m_child(~A: Data, ~le: A -> A -> Bool, has: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +c: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {H.ksort.heap.child(~A, ~le, has, AR.Arrays.of_list(A, d, xs, fl), lim, n, i, c) == hm.emb(~A, d, fl, lim, hm.child(~A, ~le, has, d, fl, xs, lim, n, i, c)) : H.KsortHeap<A>}:
  match has:
    case True{}:
      hm.m_pick(~A, ~le, U32.is_lt(U32.inc(c), n), d, fl, xs, lim, n, i, c, hl, hd)
    case False{}:
      {==}

def hm.m_live(~A: Data, ~le: A -> A -> Bool, live: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {H.ksort.heap.live(~A, ~le, live, AR.Arrays.of_list(A, d, xs, fl), lim, n, i) == hm.emb(~A, d, fl, lim, hm.live(~A, ~le, live, d, fl, xs, lim, n, i)) : H.KsortHeap<A>}:
  match live:
    case True{}:
      hm.m_child(~A, ~le, Bool.and(U32.is_lt(U32.inc(U32.shl(i)), n), U32.is_lt(i, U32.inc(U32.shl(i)))), d, fl, xs, lim, n, i, U32.inc(U32.shl(i)), hl, hd)
    case False{}:
      {==}

def hm.m_step(~A: Data, ~le: A -> A -> Bool, +d: Nat, +fl: A, +lim: U32, +st: KpHeap<A>, +hl: {List.length(&2, A, hm.xs(~A, st)) == AR.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {H.ksort.heap.step(~A, ~le, hm.emb(~A, d, fl, lim, st)) == hm.emb(~A, d, fl, lim, hm.step(~A, ~le, d, fl, lim, st)) : H.KsortHeap<A>}:
  match st:
    case KpHeap{xs, n, i, live}:
      hm.m_live(~A, ~le, live, d, fl, xs, lim, n, i, hl, hd)

def hm.m_sift(~A: Data, ~le: A -> A -> Bool, +fuel: Nat, +d: Nat, +fl: A, +lim: U32, +st: KpHeap<A>, +hl: {List.length(&2, A, hm.xs(~A, st)) == AR.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {H.ksort.heap.sift(~A, ~le, fuel, hm.emb(~A, d, fl, lim, st)) == hm.emb(~A, d, fl, lim, hm.sift(~A, ~le, fuel, d, fl, lim, st)) : H.KsortHeap<A>}:
  match fuel:
    case 0n:
      {==}
    case 1n+g:
      %Equal.sym(H.KsortHeap<A>, H.ksort.heap.step(~A, ~le, hm.emb(~A, d, fl, lim, st)), hm.emb(~A, d, fl, lim, hm.step(~A, ~le, d, fl, lim, st)), hm.m_step(~A, ~le, d, fl, lim, st, hl, hd)) : {H.ksort.heap.sift(~A, ~le, g, _) == hm.emb(~A, d, fl, lim, hm.sift(~A, ~le, g, d, fl, lim, hm.step(~A, ~le, d, fl, lim, st))) : H.KsortHeap<A>}
      hm.m_sift(~A, ~le, g, d, fl, lim, hm.step(~A, ~le, d, fl, lim, st), hm.l_step(~A, ~le, d, fl, lim, st, hl), hd)

def hm.m_array(~A: Data, +d: Nat, +fl: A, +lim: U32, st: KpHeap<A>) -> {H.ksort.heap.array(~A, hm.emb(~A, d, fl, lim, st)) == AR.Arrays.of_list(A, d, hm.xs(~A, st), fl) : Array<A>}:
  match st:
    case KpHeap{xs, n, i, live}:
      {==}

def hm.m_sd(~A: Data, ~le: A -> A -> Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {H.ksort.heap.sift_down(~A, ~le, AR.Arrays.of_list(A, d, xs, fl), lim, n, i) == AR.Arrays.of_list(A, d, hm.sift_down(~A, ~le, d, fl, xs, lim, n, i), fl) : Array<A>}:
  %Equal.sym(H.KsortHeap<A>, H.ksort.heap.sift(~A, ~le, 33n, hm.emb(~A, d, fl, lim, KpHeap{xs, n, i, True{}})), hm.emb(~A, d, fl, lim, hm.sift(~A, ~le, 33n, d, fl, lim, KpHeap{xs, n, i, True{}})), hm.m_sift(~A, ~le, 33n, d, fl, lim, KpHeap{xs, n, i, True{}}, hl, hd)) : {H.ksort.heap.array(~A, _) == AR.Arrays.of_list(A, d, hm.sift_down(~A, ~le, d, fl, xs, lim, n, i), fl) : Array<A>}
  hm.m_array(~A, d, fl, lim, hm.sift(~A, ~le, 33n, d, fl, lim, KpHeap{xs, n, i, True{}}))

def hm.m_build(~A: Data, ~le: A -> A -> Bool, fuel: Nat, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {H.ksort.heap.build(~A, ~le, fuel, AR.Arrays.of_list(A, d, xs, fl), lim, n, i) == AR.Arrays.of_list(A, d, hm.build(~A, ~le, fuel, d, fl, xs, lim, n, i), fl) : Array<A>}:
  match fuel:
    case 0n:
      {==}
    case 1n+g:
      %Equal.sym(Array<A>, H.ksort.heap.sift_down(~A, ~le, AR.Arrays.of_list(A, d, xs, fl), lim, n, U32.sub(i, 1)), AR.Arrays.of_list(A, d, hm.sift_down(~A, ~le, d, fl, xs, lim, n, U32.sub(i, 1)), fl), hm.m_sd(~A, ~le, d, fl, xs, lim, n, U32.sub(i, 1), hl, hd)) : {H.ksort.heap.build(~A, ~le, g, _, lim, n, U32.sub(i, 1)) == AR.Arrays.of_list(A, d, hm.build(~A, ~le, g, d, fl, hm.sift_down(~A, ~le, d, fl, xs, lim, n, U32.sub(i, 1)), lim, n, U32.sub(i, 1)), fl) : Array<A>}
      hm.m_build(~A, ~le, g, d, fl, hm.sift_down(~A, ~le, d, fl, xs, lim, n, U32.sub(i, 1)), lim, n, U32.sub(i, 1), hm.l_sd(~A, ~le, d, fl, xs, lim, n, U32.sub(i, 1), hl), hd)

def hm.m_drain(~A: Data, ~le: A -> A -> Bool, fuel: Nat, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +m: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {H.ksort.heap.drain(~A, ~le, fuel, AR.Arrays.of_list(A, d, xs, fl), lim, m) == AR.Arrays.of_list(A, d, hm.drain(~A, ~le, fuel, d, fl, xs, lim, m), fl) : Array<A>}:
  match fuel:
    case 0n:
      {==}
    case 1n+g:
      +k = U32.sub(m, 1)
      +ys = hm.swap(~A, d, fl, xs, lim, 0, k)
      +hy = hm.l_swap(~A, d, fl, xs, lim, 0, k, hl)
      +zs = hm.sift_down(~A, ~le, d, fl, ys, lim, k, 0)
      %Equal.sym(Array<A>, H.ksort.heap.swap(~A, AR.Arrays.of_list(A, d, xs, fl), lim, 0, k), AR.Arrays.of_list(A, d, ys, fl), hm.m_swap(~A, d, fl, xs, lim, 0, k, hl, hd)) : {H.ksort.heap.drain(~A, ~le, g, H.ksort.heap.sift_down(~A, ~le, _, lim, k, 0), lim, k) == AR.Arrays.of_list(A, d, hm.drain(~A, ~le, g, d, fl, zs, lim, k), fl) : Array<A>}
      %Equal.sym(Array<A>, H.ksort.heap.sift_down(~A, ~le, AR.Arrays.of_list(A, d, ys, fl), lim, k, 0), AR.Arrays.of_list(A, d, zs, fl), hm.m_sd(~A, ~le, d, fl, ys, lim, k, 0, hy, hd)) : {H.ksort.heap.drain(~A, ~le, g, _, lim, k) == AR.Arrays.of_list(A, d, hm.drain(~A, ~le, g, d, fl, zs, lim, k), fl) : Array<A>}
      hm.m_drain(~A, ~le, g, d, fl, zs, lim, k, hm.l_sd(~A, ~le, d, fl, ys, lim, k, 0, hy), hd)

def hm.m_sort(~A: Data, ~le: A -> A -> Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +n: U32, +hl: {List.length(&2, A, xs) == AR.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}) -> {H.ksort.heap_sort(~A, ~le, AR.Arrays.of_list(A, d, xs, fl), n) == AR.Arrays.of_list(A, d, hm.sort(~A, ~le, d, fl, xs, n), fl) : Array<A>}:
  +ys = hm.build(~A, ~le, U32.to_nat(U32.shr(n)), d, fl, xs, n, n, U32.shr(n))
  %Equal.sym(Array<A>, H.ksort.heap.build(~A, ~le, U32.to_nat(U32.shr(n)), AR.Arrays.of_list(A, d, xs, fl), n, n, U32.shr(n)), AR.Arrays.of_list(A, d, ys, fl), hm.m_build(~A, ~le, U32.to_nat(U32.shr(n)), d, fl, xs, n, n, U32.shr(n), hl, hd)) : {H.ksort.heap.drain(~A, ~le, Nat.sub(U32.to_nat(n), 1n), _, n, n) == AR.Arrays.of_list(A, d, hm.sort(~A, ~le, d, fl, xs, n), fl) : Array<A>}
  hm.m_drain(~A, ~le, Nat.sub(U32.to_nat(n), 1n), d, fl, ys, n, n, hm.l_build(~A, ~le, U32.to_nat(U32.shr(n)), d, fl, xs, n, n, U32.shr(n), hl), hd)

# U32's order is the order of the values (by induction over Base's Word)

# Nat order

def hm.le_zero(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# not a < b: b <= a
def hm.nlt(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case +aa 0n:
      hm.le_zero(aa)
    case 0n 1n+bp:
      Empty.absurd({Nat.is_le(1n+bp, 0n) == True{} : Bool}, hm.tf(e))
    case 1n+ap 1n+bp:
      hm.nlt(ap, bp, e)

def hm.lt_ne(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_eq(a, 0n) == False{} : Bool}, hm.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, hm.lt0(a)), e)))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      hm.lt_ne(ap, bp, e)

def hm.lt_to_le(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_le(a, 0n) == True{} : Bool}, hm.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, hm.lt0(a)), e)))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      hm.lt_to_le(ap, bp, e)

# an index below lim is not a slot k at or past lim
def hm.idx_g(b: Bool, +d: Nat, +i: U32, +lim: U32, +k: Nat, eb: {Nat.is_lt(U32.to_nat(i), AR.Arrays.slots(d)) == b : Bool}, +hi: {Nat.is_lt(U32.to_nat(i), U32.to_nat(lim)) == True{} : Bool}, +hk: {Nat.is_le(U32.to_nat(lim), k) == True{} : Bool}) -> {Nat.is_lt(AR.Arrays.index(d, i), k) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, AR.Arrays.index(d, i), U32.to_nat(i), AL.index_of_u32(d, i, eb)) : {Nat.is_lt(_, k) == True{} : Bool}
      UO.nat_lt_le_trans(U32.to_nat(i), U32.to_nat(lim), k, hi, hk)
    case False{}:
      UO.nat_lt_le_trans(AR.Arrays.index(d, i), U32.to_nat(i), k, UO.nat_lt_le_trans(AR.Arrays.index(d, i), AR.Arrays.slots(d), U32.to_nat(i), AL.index_below(d, i), hm.nlt(U32.to_nat(i), AR.Arrays.slots(d), eb)), hm.lt_to_le(U32.to_nat(i), k, UO.nat_lt_le_trans(U32.to_nat(i), U32.to_nat(lim), k, hi, hk)))

def hm.idx_ne(+d: Nat, +i: U32, +lim: U32, +k: Nat, hi: {U32.is_lt(i, lim) == True{} : Bool}, +hk: {Nat.is_le(U32.to_nat(lim), k) == True{} : Bool}) -> {Nat.is_eq(AR.Arrays.index(d, i), k) == False{} : Bool}:
  hm.lt_ne(AR.Arrays.index(d, i), k, hm.idx_g(Nat.is_lt(U32.to_nat(i), AR.Arrays.slots(d)), d, i, lim, k, {==}, Equal.trans(Bool, Nat.is_lt(U32.to_nat(i), U32.to_nat(lim)), U32.is_lt(i, lim), True{}, Equal.sym(Bool, U32.is_lt(i, lim), Nat.is_lt(U32.to_nat(i), U32.to_nat(lim)), UL.u32_lt_value(i, lim)), hi), hk))

# The slots at or past lim: no step of the model changes them

def hm.r_swap_g(~A: Data, bi: Bool, bj: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +i: U32, +j: U32, +k: Nat, ebi: {U32.is_lt(i, lim) == bi : Bool}, ebj: {U32.is_lt(j, lim) == bj : Bool}, +hk: {Nat.is_le(U32.to_nat(lim), k) == True{} : Bool}) -> {AR.Arrays.nth(A, hm.swap.at(~A, Bool.and(bi, bj), d, fl, xs, i, j), k, fl) == AR.Arrays.nth(A, xs, k, fl) : A}:
  match bi bj:
    case True{} True{}:
      +s1 = hm.set(~A, d, xs, i, hm.get(~A, d, xs, j, fl))
      Equal.trans(A, AR.Arrays.nth(A, hm.set(~A, d, s1, j, hm.get(~A, d, xs, i, fl)), k, fl), AR.Arrays.nth(A, s1, k, fl), AR.Arrays.nth(A, xs, k, fl), AL.nth_set_other(A, s1, AR.Arrays.index(d, j), k, hm.get(~A, d, xs, i, fl), fl, hm.idx_ne(d, j, lim, k, ebj, hk)), AL.nth_set_other(A, xs, AR.Arrays.index(d, i), k, hm.get(~A, d, xs, j, fl), fl, hm.idx_ne(d, i, lim, k, ebi, hk)))
    case True{} False{}:
      {==}
    case False{} _:
      {==}

def hm.r_swap(~A: Data, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +i: U32, +j: U32, +k: Nat, +hk: {Nat.is_le(U32.to_nat(lim), k) == True{} : Bool}) -> {AR.Arrays.nth(A, hm.swap(~A, d, fl, xs, lim, i, j), k, fl) == AR.Arrays.nth(A, xs, k, fl) : A}:
  hm.r_swap_g(~A, U32.is_lt(i, lim), U32.is_lt(j, lim), d, fl, xs, lim, i, j, k, {==}, {==}, hk)

def hm.r_decide(~A: Data, stop: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +m: U32, +k: Nat, +hk: {Nat.is_le(U32.to_nat(lim), k) == True{} : Bool}) -> {AR.Arrays.nth(A, hm.xs(~A, hm.decide(~A, stop, d, fl, xs, lim, n, i, m)), k, fl) == AR.Arrays.nth(A, xs, k, fl) : A}:
  match stop:
    case True{}:
      {==}
    case False{}:
      hm.r_swap(~A, d, fl, xs, lim, i, m, k, hk)

def hm.r_cmp(~A: Data, ~le: A -> A -> Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +m: U32, +k: Nat, +hk: {Nat.is_le(U32.to_nat(lim), k) == True{} : Bool}) -> {AR.Arrays.nth(A, hm.xs(~A, hm.cmp(~A, ~le, d, fl, xs, lim, n, i, m)), k, fl) == AR.Arrays.nth(A, xs, k, fl) : A}:
  hm.r_decide(~A, le(hm.get(~A, d, xs, m, fl), hm.get(~A, d, xs, i, fl)), d, fl, xs, lim, n, i, m, k, hk)

def hm.r_pick(~A: Data, ~le: A -> A -> Bool, two: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +c: U32, +k: Nat, +hk: {Nat.is_le(U32.to_nat(lim), k) == True{} : Bool}) -> {AR.Arrays.nth(A, hm.xs(~A, hm.pick(~A, ~le, two, d, fl, xs, lim, n, i, c)), k, fl) == AR.Arrays.nth(A, xs, k, fl) : A}:
  match two:
    case True{}:
      hm.r_cmp(~A, ~le, d, fl, xs, lim, n, i, Bool.pick(U32, le(hm.get(~A, d, xs, c, fl), hm.get(~A, d, xs, U32.inc(c), fl)), U32.inc(c), c), k, hk)
    case False{}:
      hm.r_cmp(~A, ~le, d, fl, xs, lim, n, i, c, k, hk)

def hm.r_child(~A: Data, ~le: A -> A -> Bool, has: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +c: U32, +k: Nat, +hk: {Nat.is_le(U32.to_nat(lim), k) == True{} : Bool}) -> {AR.Arrays.nth(A, hm.xs(~A, hm.child(~A, ~le, has, d, fl, xs, lim, n, i, c)), k, fl) == AR.Arrays.nth(A, xs, k, fl) : A}:
  match has:
    case True{}:
      hm.r_pick(~A, ~le, U32.is_lt(U32.inc(c), n), d, fl, xs, lim, n, i, c, k, hk)
    case False{}:
      {==}

def hm.r_live(~A: Data, ~le: A -> A -> Bool, live: Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +k: Nat, +hk: {Nat.is_le(U32.to_nat(lim), k) == True{} : Bool}) -> {AR.Arrays.nth(A, hm.xs(~A, hm.live(~A, ~le, live, d, fl, xs, lim, n, i)), k, fl) == AR.Arrays.nth(A, xs, k, fl) : A}:
  match live:
    case True{}:
      hm.r_child(~A, ~le, Bool.and(U32.is_lt(U32.inc(U32.shl(i)), n), U32.is_lt(i, U32.inc(U32.shl(i)))), d, fl, xs, lim, n, i, U32.inc(U32.shl(i)), k, hk)
    case False{}:
      {==}

def hm.r_step(~A: Data, ~le: A -> A -> Bool, +d: Nat, +fl: A, +lim: U32, +st: KpHeap<A>, +k: Nat, +hk: {Nat.is_le(U32.to_nat(lim), k) == True{} : Bool}) -> {AR.Arrays.nth(A, hm.xs(~A, hm.step(~A, ~le, d, fl, lim, st)), k, fl) == AR.Arrays.nth(A, hm.xs(~A, st), k, fl) : A}:
  match st:
    case KpHeap{xs, n, i, live}:
      hm.r_live(~A, ~le, live, d, fl, xs, lim, n, i, k, hk)

def hm.r_sift(~A: Data, ~le: A -> A -> Bool, +fuel: Nat, +d: Nat, +fl: A, +lim: U32, +st: KpHeap<A>, +k: Nat, +hk: {Nat.is_le(U32.to_nat(lim), k) == True{} : Bool}) -> {AR.Arrays.nth(A, hm.xs(~A, hm.sift(~A, ~le, fuel, d, fl, lim, st)), k, fl) == AR.Arrays.nth(A, hm.xs(~A, st), k, fl) : A}:
  match fuel:
    case 0n:
      {==}
    case 1n+g:
      Equal.trans(A, AR.Arrays.nth(A, hm.xs(~A, hm.sift(~A, ~le, g, d, fl, lim, hm.step(~A, ~le, d, fl, lim, st))), k, fl), AR.Arrays.nth(A, hm.xs(~A, hm.step(~A, ~le, d, fl, lim, st)), k, fl), AR.Arrays.nth(A, hm.xs(~A, st), k, fl), hm.r_sift(~A, ~le, g, d, fl, lim, hm.step(~A, ~le, d, fl, lim, st), k, hk), hm.r_step(~A, ~le, d, fl, lim, st, k, hk))

def hm.r_sd(~A: Data, ~le: A -> A -> Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +k: Nat, +hk: {Nat.is_le(U32.to_nat(lim), k) == True{} : Bool}) -> {AR.Arrays.nth(A, hm.sift_down(~A, ~le, d, fl, xs, lim, n, i), k, fl) == AR.Arrays.nth(A, xs, k, fl) : A}:
  hm.r_sift(~A, ~le, 33n, d, fl, lim, KpHeap{xs, n, i, True{}}, k, hk)

def hm.r_build(~A: Data, ~le: A -> A -> Bool, fuel: Nat, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +n: U32, +i: U32, +k: Nat, +hk: {Nat.is_le(U32.to_nat(lim), k) == True{} : Bool}) -> {AR.Arrays.nth(A, hm.build(~A, ~le, fuel, d, fl, xs, lim, n, i), k, fl) == AR.Arrays.nth(A, xs, k, fl) : A}:
  match fuel:
    case 0n:
      {==}
    case 1n+g:
      Equal.trans(A, AR.Arrays.nth(A, hm.build(~A, ~le, g, d, fl, hm.sift_down(~A, ~le, d, fl, xs, lim, n, U32.sub(i, 1)), lim, n, U32.sub(i, 1)), k, fl), AR.Arrays.nth(A, hm.sift_down(~A, ~le, d, fl, xs, lim, n, U32.sub(i, 1)), k, fl), AR.Arrays.nth(A, xs, k, fl), hm.r_build(~A, ~le, g, d, fl, hm.sift_down(~A, ~le, d, fl, xs, lim, n, U32.sub(i, 1)), lim, n, U32.sub(i, 1), k, hk), hm.r_sd(~A, ~le, d, fl, xs, lim, n, U32.sub(i, 1), k, hk))

def hm.r_drain(~A: Data, ~le: A -> A -> Bool, fuel: Nat, +d: Nat, +fl: A, +xs: List<&2, A>, +lim: U32, +m: U32, +k: Nat, +hk: {Nat.is_le(U32.to_nat(lim), k) == True{} : Bool}) -> {AR.Arrays.nth(A, hm.drain(~A, ~le, fuel, d, fl, xs, lim, m), k, fl) == AR.Arrays.nth(A, xs, k, fl) : A}:
  match fuel:
    case 0n:
      {==}
    case 1n+g:
      +ys = hm.swap(~A, d, fl, xs, lim, 0, U32.sub(m, 1))
      +zs = hm.sift_down(~A, ~le, d, fl, ys, lim, U32.sub(m, 1), 0)
      Equal.trans(A, AR.Arrays.nth(A, hm.drain(~A, ~le, g, d, fl, zs, lim, U32.sub(m, 1)), k, fl), AR.Arrays.nth(A, ys, k, fl), AR.Arrays.nth(A, xs, k, fl), Equal.trans(A, AR.Arrays.nth(A, hm.drain(~A, ~le, g, d, fl, zs, lim, U32.sub(m, 1)), k, fl), AR.Arrays.nth(A, zs, k, fl), AR.Arrays.nth(A, ys, k, fl), hm.r_drain(~A, ~le, g, d, fl, zs, lim, U32.sub(m, 1), k, hk), hm.r_sd(~A, ~le, d, fl, ys, lim, U32.sub(m, 1), 0, k, hk)), hm.r_swap(~A, d, fl, xs, lim, 0, U32.sub(m, 1), k, hk))

def hm.r_sort(~A: Data, ~le: A -> A -> Bool, +d: Nat, +fl: A, +xs: List<&2, A>, +n: U32, +k: Nat, +hk: {Nat.is_le(U32.to_nat(n), k) == True{} : Bool}) -> {AR.Arrays.nth(A, hm.sort(~A, ~le, d, fl, xs, n), k, fl) == AR.Arrays.nth(A, xs, k, fl) : A}:
  +ys = hm.build(~A, ~le, U32.to_nat(U32.shr(n)), d, fl, xs, n, n, U32.shr(n))
  Equal.trans(A, AR.Arrays.nth(A, hm.drain(~A, ~le, Nat.sub(U32.to_nat(n), 1n), d, fl, ys, n, n), k, fl), AR.Arrays.nth(A, ys, k, fl), AR.Arrays.nth(A, xs, k, fl), hm.r_drain(~A, ~le, Nat.sub(U32.to_nat(n), 1n), d, fl, ys, n, n, k, hk), hm.r_build(~A, ~le, U32.to_nat(U32.shr(n)), d, fl, xs, n, n, U32.shr(n), k, hk))
