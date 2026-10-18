# Proof helpers for bend-osdev-ringbuf: the Array ring's elements, through
# bend-osdev-array's laws. PROOF.bend uses them for the laws that tie the
# Array ring to the model element by element.
#
# A sound ring's slots are reflected, once, into Arrays.of_list(order, l, 0)
# for a Data list l of 2^order elements (array's `reflect`); array's
# of_list_get and of_list_set then follow every read and write on l alone:
# the element pushed at counter k is ri.at(o, l, k), the slot of the masked
# index Arrays.index(o, k), and a push writes ri.set(o, l, i, x). The
# elements, oldest first, are ri.view(in - out, out, o, l): the slots of the
# counters out to in - 1. A counter between 2^order and 2^(order + 1) wraps
# to its distance from 2^order (array's index_wrap), so the counters of a
# valid ring reach distinct slots: a push at in leaves the view before it
# unchanged, and a pop that drops the counters by 2^order reads on from the
# same slots.
import Base
import ./ringbuf.bend as R
import ../array/array.bend as A
import ../array/LAWS.bend as AL
import ../array/PROOF.bend as APF

# Shorthands (they unfold to the defs they name)

def ri.ol(+o: Nat, +l: List<&2, U32>) -> Array<U32>:
  A.Arrays.of_list(U32, o, l, 0)

def ri.rr(+o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>) -> R.RingBuf:
  R.RingBuf{o, i, u, A.Arrays.of_list(U32, o, l, 0)}

def ri.ix(+o: Nat, k: Nat) -> Nat:
  A.Arrays.index(o, U32.from_nat(k))

# the element at counter k
def ri.at(+o: Nat, +l: List<&2, U32>, k: Nat) -> U32:
  A.Arrays.nth(U32, l, A.Arrays.index(o, U32.from_nat(k)), 0)

# the slots after a push of x at counter i
def ri.set(+o: Nat, +l: List<&2, U32>, i: Nat, x: U32) -> List<&2, U32>:
  List.set(&2, U32, l, A.Arrays.index(o, U32.from_nat(i)), x)

# the elements at the counters k to k + n - 1
def ri.view(n: Nat, +k: Nat, +o: Nat, +l: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{ri.at(o, l, k), ri.view(p, 1n+k, o, l)}

# Contradictions and Bool

def ri.bt(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def ri.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : ri.bt(_)
  Unit{}

def ri.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : ri.bt(_)
  Unit{}

# Nat

def ri.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 0n), p, ri.add_zero(p))

def ri.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 1n+b), 1n+Nat.add(p, b), ri.add_succ(p, b))

def ri.add_comm(x: Nat, +y: Nat) -> {Nat.add(x, y) == Nat.add(y, x) : Nat}:
  match x:
    case 0n:
      Equal.sym(Nat, Nat.add(y, 0n), y, ri.add_zero(y))
    case 1n+ +p:
      Equal.trans(Nat, 1n+Nat.add(p, y), 1n+Nat.add(y, p), Nat.add(y, 1n+p), Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, y), Nat.add(y, p), ri.add_comm(p, y)), Equal.sym(Nat, Nat.add(y, 1n+p), 1n+Nat.add(y, p), ri.add_succ(y, p)))

def ri.double_self(x: Nat) -> {Nat.double(x) == Nat.add(x, x) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.trans(Nat, 2n+Nat.double(p), 2n+Nat.add(p, p), 1n+Nat.add(p, 1n+p), Equal.cong(Nat, Nat, k => 2n+k, Nat.double(p), Nat.add(p, p), ri.double_self(p)), Equal.cong(Nat, Nat, k => 1n+k, 1n+Nat.add(p, p), Nat.add(p, 1n+p), Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), ri.add_succ(p, p))))

def ri.sub_zero(x: Nat) -> {Nat.sub(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (1 + i) - u = 1 + (i - u), for u <= i
def ri.sub_succ(i: Nat, u: Nat, e: {Nat.is_le(u, i) == True{} : Bool}) -> {Nat.sub(1n+i, u) == 1n+Nat.sub(i, u) : Nat}:
  match i u:
    case +ii 0n:
      Equal.cong(Nat, Nat, k => 1n+k, ii, Nat.sub(ii, 0n), Equal.sym(Nat, Nat.sub(ii, 0n), ii, ri.sub_zero(ii)))
    case 0n 1n+up:
      Empty.absurd({Nat.sub(1n, 1n+up) == 1n : Nat}, ri.ft(e))
    case 1n+ip 1n+up:
      ri.sub_succ(ip, up, e)

def ri.add_sub(d: Nat, s: Nat, e: {Nat.is_le(d, s) == True{} : Bool}) -> {Nat.add(d, Nat.sub(s, d)) == s : Nat}:
  match d s:
    case 0n +ss:
      ri.sub_zero(ss)
    case 1n+dp 0n:
      Empty.absurd({1n+Nat.add(dp, 0n) == 0n : Nat}, ri.ft(e))
    case 1n+ +dp 1n+ +sp:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(dp, Nat.sub(sp, dp)), sp, ri.add_sub(dp, sp, e))

def ri.le_refl(x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      ri.le_refl(p)

def ri.lt_succ_r(x: Nat, y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x, 1n+y) == True{} : Bool}:
  match x y:
    case 0n _:
      {==}
    case 1n+xp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 1n) == True{} : Bool}, ri.ft(h))
    case 1n+xp 1n+yp:
      ri.lt_succ_r(xp, yp, h)

def ri.lt_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n _:
      Empty.absurd({Nat.is_lt(0n, c) == True{} : Bool}, ri.ft(h1))
    case 0n 1n+bp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ri.ft(h2))
    case 0n 1n+bp 1n+cp:
      {==}
    case 1n+ap 0n _:
      Empty.absurd({Nat.is_lt(1n+ap, c) == True{} : Bool}, ri.ft(h1))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, ri.ft(h2))
    case 1n+ap 1n+bp 1n+cp:
      ri.lt_trans(ap, bp, cp, h1, h2)

# x < y: x != y
def ri.ne_lt(x: Nat, y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_eq(x, y) == False{} : Bool}:
  match x y:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, ri.ft(h))
    case 0n 1n+yp:
      {==}
    case 1n+xp 0n:
      {==}
    case 1n+xp 1n+yp:
      ri.ne_lt(xp, yp, h)

# y < x: x != y
def ri.ne_gt(x: Nat, y: Nat, h: {Nat.is_lt(y, x) == True{} : Bool}) -> {Nat.is_eq(x, y) == False{} : Bool}:
  match x y:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, ri.ft(h))
    case 0n 1n+yp:
      {==}
    case 1n+xp 0n:
      {==}
    case 1n+xp 1n+yp:
      ri.ne_gt(xp, yp, h)

def ri.not_lt(x: Nat, y: Nat, e: {Nat.is_lt(x, y) == False{} : Bool}) -> {Nat.is_le(y, x) == True{} : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+yp:
      Empty.absurd({Nat.is_le(1n+yp, 0n) == True{} : Bool}, ri.tf(e))
    case 1n+xp 0n:
      {==}
    case 1n+xp 1n+yp:
      ri.not_lt(xp, yp, e)

def ri.le_lt(a: Nat, b: Nat, h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ri.ft(h))
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, ri.ft(h))
    case 1n+ap 1n+bp:
      ri.le_lt(ap, bp, h)

# 1 + (u + p) <= i: u < i
def ri.lt_of_le_add(u: Nat, -p: Nat, i: Nat, h: {Nat.is_le(1n+Nat.add(u, p), i) == True{} : Bool}) -> {Nat.is_lt(u, i) == True{} : Bool}:
  match u i:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ri.ft(h))
    case 0n 1n+ip:
      {==}
    case 1n+up 0n:
      Empty.absurd({Nat.is_lt(1n+up, 0n) == True{} : Bool}, ri.ft(h))
    case 1n+up 1n+ip:
      ri.lt_of_le_add(up, p, ip, h)

def ri.lt_cancel(s: Nat, -r: Nat, -u: Nat) -> {Nat.is_lt(Nat.add(s, r), Nat.add(s, u)) == Nat.is_lt(r, u) : Bool}:
  match s:
    case 0n:
      {==}
    case 1n+p:
      ri.lt_cancel(p, r, u)

# order facts, moved along equations
def ri.lt_rw(-x: Nat, -y: Nat, -x2: Nat, -y2: Nat, ex: {x == x2 : Nat}, ey: {y == y2 : Nat}, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x2, y2) == True{} : Bool}:
  %ex : {Nat.is_lt(_, y2) == True{} : Bool}
  %ey : {Nat.is_lt(x, _) == True{} : Bool}
  h

def ri.le_rw(-x: Nat, -y: Nat, -x2: Nat, -y2: Nat, ex: {x == x2 : Nat}, ey: {y == y2 : Nat}, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(x2, y2) == True{} : Bool}:
  %ex : {Nat.is_le(_, y2) == True{} : Bool}
  %ey : {Nat.is_le(x, _) == True{} : Bool}
  h

# ring.size is Arrays.slots
def ri.size_slots(o: Nat) -> {R.ring.size(o) == A.Arrays.slots(o) : Nat}:
  match o:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => Nat.double(k), R.ring.size(p), A.Arrays.slots(p), ri.size_slots(p))

# Lists

def ri.app_nil(xs: List<&2, U32>) -> {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{h, z}, List.append(&2, U32, t, Nil{}), t, ri.app_nil(t))

def ri.app_snoc(xs: List<&2, U32>, -x: U32, -acc: List<&2, U32>) -> {List.append(&2, U32, List.append(&2, U32, xs, Con{x, Nil{}}), acc) == List.append(&2, U32, xs, Con{x, acc}) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{h, z}, List.append(&2, U32, List.append(&2, U32, t, Con{x, Nil{}}), acc), List.append(&2, U32, t, Con{x, acc}), ri.app_snoc(t, x, acc))

def ri.take_zero(xs: List<&2, U32>) -> {List.take(&2, U32, xs, 0n) == Nil{} : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def ri.drop_zero(xs: List<&2, U32>) -> {List.drop(&2, U32, xs, 0n) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# The view

def ri.view_len(n: Nat, +k: Nat, +o: Nat, +l: List<&2, U32>) -> {List.length(&2, U32, ri.view(n, k, o, l)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, U32, ri.view(p, 1n+k, o, l)), p, ri.view_len(p, 1n+k, o, l))

# the view of 1 + p counters is that of p, then the element at u + p
def ri.view_snoc(p: Nat, +u: Nat, +o: Nat, +l: List<&2, U32>) -> {ri.view(1n+p, u, o, l) == List.append(&2, U32, ri.view(p, u, o, l), Con{ri.at(o, l, Nat.add(u, p)), Nil{}}) : List<&2, U32>}:
  match p:
    case 0n:
      %Equal.sym(Nat, Nat.add(u, 0n), u, ri.add_zero(u)) : {Con{ri.at(o, l, u), Nil{}} == Con{ri.at(o, l, _), Nil{}} : List<&2, U32>}
      {==}
    case 1n+ +q:
      %Equal.sym(Nat, Nat.add(u, 1n+q), 1n+Nat.add(u, q), ri.add_succ(u, q)) : {Con{ri.at(o, l, u), ri.view(1n+q, 1n+u, o, l)} == Con{ri.at(o, l, u), List.append(&2, U32, ri.view(q, 1n+u, o, l), Con{ri.at(o, l, _), Nil{}})} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, ri.view(1n+q, 1n+u, o, l), List.append(&2, U32, ri.view(q, 1n+u, o, l), Con{ri.at(o, l, Nat.add(1n+u, q)), Nil{}}), ri.view_snoc(q, 1n+u, o, l)) : {Con{ri.at(o, l, u), _} == Con{ri.at(o, l, u), List.append(&2, U32, ri.view(q, 1n+u, o, l), Con{ri.at(o, l, 1n+Nat.add(u, q)), Nil{}})} : List<&2, U32>}
      {==}

# Reads and writes of a reflected ring

def ri.get_eq(+o: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +k: Nat) -> {Array.get(U32, ri.ol(o, l), U32.from_nat(k)) == (ri.ol(o, l), ri.at(o, l, k)) : Array<U32> & U32}:
  AL.of_list_get(U32, o, l, 0, hl, hd, U32.from_nat(k))

def ri.set_len(+o: Nat, +l: List<&2, U32>, +i: Nat, +x: U32, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}) -> {List.length(&2, U32, ri.set(o, l, i, x)) == A.Arrays.slots(o) : Nat}:
  Equal.trans(Nat, List.length(&2, U32, ri.set(o, l, i, x)), List.length(&2, U32, l), A.Arrays.slots(o), AL.set_length(U32, l, ri.ix(o, i), x), hl)

# a push that is not refused writes ri.set
def ri.push_eq(+o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +x: U32, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}) -> {R.ring.push.go(False{}, o, i, u, ri.ol(o, l), x) == (ri.rr(o, 1n+i, u, ri.set(o, l, i, x)), Done{Unit{}}) : R.RingBuf & Result<&2, &2, R.RingError, Unit>}:
  %Equal.sym(Array<U32>, Array.set(U32, ri.ol(o, l), U32.from_nat(i), x), ri.ol(o, ri.set(o, l, i, x)), AL.of_list_set(U32, o, l, 0, hl, hd, U32.from_nat(i), x)) : {(R.RingBuf{o, 1n+i, u, _}, Done{Unit{}}) == (ri.rr(o, 1n+i, u, ri.set(o, l, i, x)), Done{Unit{}}) : R.RingBuf & Result<&2, &2, R.RingError, Unit>}
  {==}

# the elements of a reflected ring
def ri.items_go(n: Nat, +o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +acc: List<&2, U32>) -> {R.ring.items.go(n, o, i, u, ri.ol(o, l), acc) == (ri.rr(o, i, u, l), List.append(&2, U32, ri.view(n, u, o, l), acc)) : R.RingBuf & List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      +k = Nat.add(u, p)
      +x = ri.at(o, l, k)
      +v = ri.view(p, u, o, l)
      %Equal.sym(Array<U32> & U32, Array.get(U32, ri.ol(o, l), U32.from_nat(k)), (ri.ol(o, l), x), ri.get_eq(o, l, hl, hd, k)) : {R.ring.items.word(_, a2 => x2 => R.ring.items.go(p, o, i, u, a2, Con{x2, acc})) == (ri.rr(o, i, u, l), List.append(&2, U32, ri.view(1n+p, u, o, l), acc)) : R.RingBuf & List<&2, U32>}
      %Equal.sym(R.RingBuf & List<&2, U32>, R.ring.items.go(p, o, i, u, ri.ol(o, l), Con{x, acc}), (ri.rr(o, i, u, l), List.append(&2, U32, v, Con{x, acc})), ri.items_go(p, o, i, u, l, hl, hd, Con{x, acc})) : {_ == (ri.rr(o, i, u, l), List.append(&2, U32, ri.view(1n+p, u, o, l), acc)) : R.RingBuf & List<&2, U32>}
      %Equal.sym(List<&2, U32>, ri.view(1n+p, u, o, l), List.append(&2, U32, v, Con{x, Nil{}}), ri.view_snoc(p, u, o, l)) : {(ri.rr(o, i, u, l), List.append(&2, U32, v, Con{x, acc})) == (ri.rr(o, i, u, l), List.append(&2, U32, _, acc)) : R.RingBuf & List<&2, U32>}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, v, Con{x, Nil{}}), acc), List.append(&2, U32, v, Con{x, acc}), ri.app_snoc(v, x, acc)) : {(ri.rr(o, i, u, l), List.append(&2, U32, v, Con{x, acc})) == (ri.rr(o, i, u, l), _) : R.RingBuf & List<&2, U32>}
      {==}

def ri.items(+o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}) -> {R.ring.items(ri.rr(o, i, u, l)) == (ri.rr(o, i, u, l), ri.view(Nat.sub(i, u), u, o, l)) : R.RingBuf & List<&2, U32>}:
  %ri.app_nil(ri.view(Nat.sub(i, u), u, o, l)) : {R.ring.items(ri.rr(o, i, u, l)) == (ri.rr(o, i, u, l), _) : R.RingBuf & List<&2, U32>}
  ri.items_go(Nat.sub(i, u), o, i, u, l, hl, hd, Nil{})

def ri.items_snd(+o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(ri.rr(o, i, u, l))) == ri.view(Nat.sub(i, u), u, o, l) : List<&2, U32>}:
  %Equal.sym(R.RingBuf & List<&2, U32>, R.ring.items(ri.rr(o, i, u, l)), (ri.rr(o, i, u, l), ri.view(Nat.sub(i, u), u, o, l)), ri.items(o, i, u, l, hl, hd)) : {Pair.snd(R.RingBuf, List<&2, U32>, _) == ri.view(Nat.sub(i, u), u, o, l) : List<&2, U32>}
  {==}

def ri.items_fst(+o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}) -> {Pair.fst(R.RingBuf, List<&2, U32>, R.ring.items(ri.rr(o, i, u, l))) == ri.rr(o, i, u, l) : R.RingBuf}:
  %Equal.sym(R.RingBuf & List<&2, U32>, R.ring.items(ri.rr(o, i, u, l)), (ri.rr(o, i, u, l), ri.view(Nat.sub(i, u), u, o, l)), ri.items(o, i, u, l, hl, hd)) : {Pair.fst(R.RingBuf, List<&2, U32>, _) == ri.rr(o, i, u, l) : R.RingBuf}
  {==}

# a ring's elements, given about its array, are the view of its reflection
def ri.ei.rw(-o: Nat, -i: Nat, -u: Nat, -a: Array<U32>, -l: List<&2, U32>, -items: List<&2, U32>, e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}) -> {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(ri.rr(o, i, u, l))) == items : List<&2, U32>}:
  %Equal.sym(Array<U32>, A.Arrays.of_list(U32, o, l, 0), a, e1) : {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, _})) == items : List<&2, U32>}
  ei

def ri.ei(+o: Nat, +i: Nat, +u: Nat, -a: Array<U32>, +l: List<&2, U32>, -items: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, e1: {A.Arrays.of_list(U32, o, l, 0) == a : Array<U32>}, ei: {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(R.RingBuf{o, i, u, a})) == items : List<&2, U32>}) -> {ri.view(Nat.sub(i, u), u, o, l) == items : List<&2, U32>}:
  Equal.trans(List<&2, U32>, ri.view(Nat.sub(i, u), u, o, l), Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(ri.rr(o, i, u, l))), items, Equal.sym(List<&2, U32>, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.items(ri.rr(o, i, u, l))), ri.view(Nat.sub(i, u), u, o, l), ri.items_snd(o, i, u, l, hl, hd)), ri.ei.rw(o, i, u, a, l, items, e1, ei))

# a reflected ring with valid counters and an order below 32 is sound
def ri.sound_of(+o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, hinv: {R.ring.inv(o, i, u) == True{} : Bool}, hd: {Nat.is_lt(o, 32n) == True{} : Bool}) -> {R.ring.sound(ri.rr(o, i, u, l)) == True{} : Bool}:
  %Equal.sym(Bool, R.ring.inv(o, i, u), True{}, hinv) : {Bool.and(_, Bool.and(Nat.is_lt(o, 32n), A.Arrays.is_perfect(U32, o, ri.ol(o, l)))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_lt(o, 32n), True{}, hd) : {Bool.and(_, A.Arrays.is_perfect(U32, o, ri.ol(o, l))) == True{} : Bool}
  AL.of_list_perfect(U32, o, l, 0)

# Slots: a counter c below 2^(o + 1) reaches slot c, or c - 2^o past the end

def ri.md(b: Bool, +s: Nat, +c: Nat) -> Nat:
  match b:
    case True{}:
      c
    case False{}:
      Nat.sub(c, s)

def ri.idx_val(+o: Nat, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +c: Nat, b: Bool, +eb: {Nat.is_lt(c, A.Arrays.slots(o)) == b : Bool}, +hc: {Nat.is_lt(c, Nat.double(A.Arrays.slots(o))) == True{} : Bool}) -> {ri.ix(o, c) == ri.md(b, A.Arrays.slots(o), c) : Nat}:
  match b:
    case True{}:
      AL.index_of_nat(o, hd, c, eb)
    case False{}:
      +s = A.Arrays.slots(o)
      +r = Nat.sub(c, s)
      +ec = ri.add_sub(s, c, ri.not_lt(c, s, eb))
      +h2 = ri.lt_rw(c, Nat.double(s), Nat.add(s, r), Nat.add(s, s), Equal.sym(Nat, Nat.add(s, r), c, ec), ri.double_self(s), hc)
      +hr = Equal.trans(Bool, Nat.is_lt(r, s), Nat.is_lt(Nat.add(s, r), Nat.add(s, s)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(s, r), Nat.add(s, s)), Nat.is_lt(r, s), ri.lt_cancel(s, r, s)), h2)
      %ec : {A.Arrays.index(o, U32.from_nat(_)) == Nat.sub(c, s) : Nat}
      AL.index_wrap(o, hd, r, hr)

# counters c < i with i < c + 2^o reach different slots
def ri.md_ne(bi: Bool, bc: Bool, +s: Nat, +c: Nat, +i: Nat, +ebi: {Nat.is_lt(i, s) == bi : Bool}, +ebc: {Nat.is_lt(c, s) == bc : Bool}, +h1: {Nat.is_lt(c, i) == True{} : Bool}, +h2: {Nat.is_lt(i, Nat.add(c, s)) == True{} : Bool}) -> {Nat.is_eq(ri.md(bi, s, i), ri.md(bc, s, c)) == False{} : Bool}:
  match bi bc:
    case True{} True{}:
      ri.ne_gt(i, c, h1)
    case True{} False{}:
      Empty.absurd({Nat.is_eq(i, Nat.sub(c, s)) == False{} : Bool}, ri.tf(Equal.trans(Bool, True{}, Nat.is_lt(c, s), False{}, Equal.sym(Bool, Nat.is_lt(c, s), True{}, ri.lt_trans(c, i, s, h1, ebi)), ebc)))
    case False{} True{}:
      +ip = Nat.sub(i, s)
      +ei = ri.add_sub(s, i, ri.not_lt(i, s, ebi))
      +h2b = ri.lt_rw(i, Nat.add(c, s), Nat.add(s, ip), Nat.add(s, c), Equal.sym(Nat, Nat.add(s, ip), i, ei), ri.add_comm(c, s), h2)
      ri.ne_lt(ip, c, Equal.trans(Bool, Nat.is_lt(ip, c), Nat.is_lt(Nat.add(s, ip), Nat.add(s, c)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(s, ip), Nat.add(s, c)), Nat.is_lt(ip, c), ri.lt_cancel(s, ip, c)), h2b))
    case False{} False{}:
      +ip = Nat.sub(i, s)
      +cp = Nat.sub(c, s)
      +ei = ri.add_sub(s, i, ri.not_lt(i, s, ebi))
      +ec = ri.add_sub(s, c, ri.not_lt(c, s, ebc))
      +h1b = ri.lt_rw(c, i, Nat.add(s, cp), Nat.add(s, ip), Equal.sym(Nat, Nat.add(s, cp), c, ec), Equal.sym(Nat, Nat.add(s, ip), i, ei), h1)
      ri.ne_gt(ip, cp, Equal.trans(Bool, Nat.is_lt(cp, ip), Nat.is_lt(Nat.add(s, cp), Nat.add(s, ip)), True{}, Equal.sym(Bool, Nat.is_lt(Nat.add(s, cp), Nat.add(s, ip)), Nat.is_lt(cp, ip), ri.lt_cancel(s, cp, ip)), h1b))

def ri.idx_ne(+o: Nat, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +c: Nat, +i: Nat, +h1: {Nat.is_lt(c, i) == True{} : Bool}, +h2: {Nat.is_lt(i, Nat.add(c, A.Arrays.slots(o))) == True{} : Bool}, +h3: {Nat.is_lt(i, Nat.double(A.Arrays.slots(o))) == True{} : Bool}) -> {Nat.is_eq(ri.ix(o, i), ri.ix(o, c)) == False{} : Bool}:
  +s = A.Arrays.slots(o)
  +hc = ri.lt_trans(c, i, Nat.double(s), h1, h3)
  %Equal.sym(Nat, ri.ix(o, i), ri.md(Nat.is_lt(i, s), s, i), ri.idx_val(o, hd, i, Nat.is_lt(i, s), {==}, h3)) : {Nat.is_eq(_, ri.ix(o, c)) == False{} : Bool}
  %Equal.sym(Nat, ri.ix(o, c), ri.md(Nat.is_lt(c, s), s, c), ri.idx_val(o, hd, c, Nat.is_lt(c, s), {==}, hc)) : {Nat.is_eq(ri.md(Nat.is_lt(i, s), s, i), _) == False{} : Bool}
  ri.md_ne(Nat.is_lt(i, s), Nat.is_lt(c, s), s, c, i, {==}, {==}, h1, h2)

# a write at counter i leaves the elements at the counters u to u + n - 1,
# all below i, when i - u < 2^o
def ri.view_set(n: Nat, +u: Nat, +o: Nat, +l: List<&2, U32>, +i: Nat, +x: U32, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h1: {Nat.is_le(Nat.add(u, n), i) == True{} : Bool}, +h2: {Nat.is_lt(i, Nat.add(u, A.Arrays.slots(o))) == True{} : Bool}, +h3: {Nat.is_lt(i, Nat.double(A.Arrays.slots(o))) == True{} : Bool}) -> {ri.view(n, u, o, ri.set(o, l, i, x)) == ri.view(n, u, o, l) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      +s = A.Arrays.slots(o)
      +l2 = ri.set(o, l, i, x)
      +h1b = ri.le_rw(Nat.add(u, 1n+p), i, 1n+Nat.add(u, p), i, ri.add_succ(u, p), {==}, h1)
      +hu = ri.lt_of_le_add(u, p, i, h1b)
      +eh = AL.nth_set_other(U32, l, ri.ix(o, i), ri.ix(o, u), x, 0, ri.idx_ne(o, hd, u, i, hu, h2, h3))
      +ih = ri.view_set(p, 1n+u, o, l, i, x, hd, h1b, ri.lt_succ_r(i, Nat.add(u, s), h2), h3)
      %Equal.sym(U32, ri.at(o, l2, u), ri.at(o, l, u), eh) : {Con{_, ri.view(p, 1n+u, o, l2)} == Con{ri.at(o, l, u), ri.view(p, 1n+u, o, l)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, ri.view(p, 1n+u, o, l2), ri.view(p, 1n+u, o, l), ih) : {Con{ri.at(o, l, u), _} == Con{ri.at(o, l, u), ri.view(p, 1n+u, o, l)} : List<&2, U32>}
      {==}

# a push at in, on a ring with room: the elements, then x
def ri.view_push(+o: Nat, +i: Nat, +u: Nat, +l: List<&2, U32>, +x: U32, +hl: {List.length(&2, U32, l) == A.Arrays.slots(o) : Nat}, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +hui: {Nat.is_le(u, i) == True{} : Bool}, +hn: {Nat.is_le(1n+Nat.sub(i, u), R.ring.size(o)) == True{} : Bool}, +hus: {Nat.is_lt(u, R.ring.size(o)) == True{} : Bool}) -> {ri.view(Nat.sub(1n+i, u), u, o, ri.set(o, l, i, x)) == List.append(&2, U32, ri.view(Nat.sub(i, u), u, o, l), Con{x, Nil{}}) : List<&2, U32>}:
  +s = A.Arrays.slots(o)
  +n = Nat.sub(i, u)
  +l2 = ri.set(o, l, i, x)
  +ei = ri.add_sub(u, i, hui)
  +hns = ri.le_lt(n, s, ri.le_rw(1n+n, R.ring.size(o), 1n+n, s, {==}, ri.size_slots(o), hn))
  +hus2 = ri.lt_rw(u, R.ring.size(o), u, s, {==}, ri.size_slots(o), hus)
  +h2 = ri.lt_rw(Nat.add(u, n), Nat.add(u, s), i, Nat.add(u, s), ei, {==}, Equal.trans(Bool, Nat.is_lt(Nat.add(u, n), Nat.add(u, s)), Nat.is_lt(n, s), True{}, ri.lt_cancel(u, n, s), hns))
  +hus3 = ri.lt_rw(Nat.add(s, u), Nat.add(s, s), Nat.add(u, s), Nat.double(s), ri.add_comm(s, u), Equal.sym(Nat, Nat.double(s), Nat.add(s, s), ri.double_self(s)), Equal.trans(Bool, Nat.is_lt(Nat.add(s, u), Nat.add(s, s)), Nat.is_lt(u, s), True{}, ri.lt_cancel(s, u, s), hus2))
  +h3 = ri.lt_trans(i, Nat.add(u, s), Nat.double(s), h2, hus3)
  +h1 = ri.le_rw(i, i, Nat.add(u, n), i, Equal.sym(Nat, Nat.add(u, n), i, ei), {==}, ri.le_refl(i))
  +hlt = ri.lt_rw(ri.ix(o, i), s, ri.ix(o, i), List.length(&2, U32, l), {==}, Equal.sym(Nat, List.length(&2, U32, l), s, hl), AL.index_below(o, U32.from_nat(i)))
  %Equal.sym(Nat, Nat.sub(1n+i, u), 1n+n, ri.sub_succ(i, u, hui)) : {ri.view(_, u, o, l2) == List.append(&2, U32, ri.view(n, u, o, l), Con{x, Nil{}}) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, ri.view(1n+n, u, o, l2), List.append(&2, U32, ri.view(n, u, o, l2), Con{ri.at(o, l2, Nat.add(u, n)), Nil{}}), ri.view_snoc(n, u, o, l2)) : {_ == List.append(&2, U32, ri.view(n, u, o, l), Con{x, Nil{}}) : List<&2, U32>}
  %Equal.sym(Nat, Nat.add(u, n), i, ei) : {List.append(&2, U32, ri.view(n, u, o, l2), Con{ri.at(o, l2, _), Nil{}}) == List.append(&2, U32, ri.view(n, u, o, l), Con{x, Nil{}}) : List<&2, U32>}
  %Equal.sym(U32, ri.at(o, l2, i), x, AL.nth_set_same(U32, l, ri.ix(o, i), x, 0, hlt)) : {List.append(&2, U32, ri.view(n, u, o, l2), Con{_, Nil{}}) == List.append(&2, U32, ri.view(n, u, o, l), Con{x, Nil{}}) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, ri.view(n, u, o, l2), ri.view(n, u, o, l), ri.view_set(n, u, o, l, i, x, hd, h1, h2, h3)) : {List.append(&2, U32, _, Con{x, Nil{}}) == List.append(&2, U32, ri.view(n, u, o, l), Con{x, Nil{}}) : List<&2, U32>}
  {==}

# the counters 2^o + j on read the same slots as j, for j + n <= 2^o
def ri.view_wrap(n: Nat, +j: Nat, +o: Nat, +l: List<&2, U32>, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {Nat.is_le(Nat.add(j, n), A.Arrays.slots(o)) == True{} : Bool}) -> {ri.view(n, Nat.add(A.Arrays.slots(o), j), o, l) == ri.view(n, j, o, l) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      +s = A.Arrays.slots(o)
      +hb = ri.le_rw(Nat.add(j, 1n+p), s, 1n+Nat.add(j, p), s, ri.add_succ(j, p), {==}, h)
      +hj = ri.lt_of_le_add(j, p, s, hb)
      +ih = ri.view_wrap(p, 1n+j, o, l, hd, hb)
      %Equal.sym(Nat, A.Arrays.index(o, U32.from_nat(Nat.add(s, j))), j, AL.index_wrap(o, hd, j, hj)) : {Con{A.Arrays.nth(U32, l, _, 0), ri.view(p, 1n+Nat.add(s, j), o, l)} == Con{ri.at(o, l, j), ri.view(p, 1n+j, o, l)} : List<&2, U32>}
      %Equal.sym(Nat, A.Arrays.index(o, U32.from_nat(j)), j, AL.index_of_nat(o, hd, j, hj)) : {Con{A.Arrays.nth(U32, l, j, 0), ri.view(p, 1n+Nat.add(s, j), o, l)} == Con{A.Arrays.nth(U32, l, _, 0), ri.view(p, 1n+j, o, l)} : List<&2, U32>}
      %ri.add_succ(s, j) : {Con{A.Arrays.nth(U32, l, j, 0), ri.view(p, _, o, l)} == Con{A.Arrays.nth(U32, l, j, 0), ri.view(p, 1n+j, o, l)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, ri.view(p, Nat.add(s, 1n+j), o, l), ri.view(p, 1n+j, o, l), ih) : {Con{A.Arrays.nth(U32, l, j, 0), _} == Con{A.Arrays.nth(U32, l, j, 0), ri.view(p, 1n+j, o, l)} : List<&2, U32>}
      {==}

# after a pop that drops the counters by 2^o: the same elements
def ri.view_drop(+n: Nat, +o: Nat, +l: List<&2, U32>, +hd: {Nat.is_lt(o, 32n) == True{} : Bool}, +h: {Nat.is_le(n, R.ring.size(o)) == True{} : Bool}) -> {ri.view(n, R.ring.size(o), o, l) == ri.view(n, 0n, o, l) : List<&2, U32>}:
  +s = A.Arrays.slots(o)
  %Equal.sym(Nat, R.ring.size(o), s, ri.size_slots(o)) : {ri.view(n, _, o, l) == ri.view(n, 0n, o, l) : List<&2, U32>}
  %ri.add_zero(s) : {ri.view(n, _, o, l) == ri.view(n, 0n, o, l) : List<&2, U32>}
  ri.view_wrap(n, 0n, o, l, hd, ri.le_rw(n, R.ring.size(o), Nat.add(0n, n), s, {==}, ri.size_slots(o), h))
