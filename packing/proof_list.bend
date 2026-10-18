# Proof helpers for bend-osdev-packing: lists. Base's List.reverse, the
# 4-byte swap of view.bend and the reorderings built from them, how bytes'
# mask passes through them, and runs of bits (field.bend).
import Base
import ../bytes/bytes.bend as B
import ./view.bend as V
import ./field.bend as F

def pl.bt(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def pl.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : pl.bt(_)
  Unit{}

def pl.add_zero(m: Nat) -> {Nat.add(m, 0n) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      %pl.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def pl.add_succ(x: Nat, -y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %pl.add_succ(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

# Reversal

def pl.rev_go(-A: Data, xs: List<&2, A>, +acc: List<&2, A>) -> {List.reverse.go(&2, A, List.reverse.go(&2, A, xs, acc), Nil{}) == List.reverse.go(&2, A, acc, xs) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      pl.rev_go(A, t, Con{h, acc})

def pl.rev_rev(-A: Data, +xs: List<&2, A>) -> {List.reverse(&2, A, List.reverse(&2, A, xs)) == xs : List<&2, A>}:
  pl.rev_go(A, xs, Nil{})

def pl.rev_len_go(-A: Data, xs: List<&2, A>, +acc: List<&2, A>) -> {List.length(&2, A, List.reverse.go(&2, A, xs, acc)) == Nat.add(List.length(&2, A, xs), List.length(&2, A, acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %pl.add_succ(List.length(&2, A, t), List.length(&2, A, acc)) : {List.length(&2, A, List.reverse.go(&2, A, t, Con{h, acc})) == _ : Nat}
      pl.rev_len_go(A, t, Con{h, acc})

def pl.rev_len(-A: Data, +xs: List<&2, A>) -> {List.length(&2, A, List.reverse(&2, A, xs)) == List.length(&2, A, xs) : Nat}:
  Equal.trans(Nat, List.length(&2, A, List.reverse(&2, A, xs)), Nat.add(List.length(&2, A, xs), 0n), List.length(&2, A, xs), pl.rev_len_go(A, xs, Nil{}), pl.add_zero(List.length(&2, A, xs)))

def pl.rev_mask_go(xs: List<&2, U32>, +acc: List<&2, U32>) -> {List.reverse.go(&2, U32, B.mask(xs), B.mask(acc)) == B.mask(List.reverse.go(&2, U32, xs, acc)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      pl.rev_mask_go(t, Con{h, acc})

def pl.rev_mask(+xs: List<&2, U32>) -> {List.reverse(&2, U32, B.mask(xs)) == B.mask(List.reverse(&2, U32, xs)) : List<&2, U32>}:
  pl.rev_mask_go(xs, Nil{})

# The 4-byte swap

def pl.le_le(xs: List<&2, U32>) -> {V.packing.le_swap(V.packing.le_swap(xs)) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, Nil{}}:
      {==}
    case Con{a, Con{b, Nil{}}}:
      {==}
    case Con{a, Con{b, Con{c, Nil{}}}}:
      {==}
    case Con{+a, Con{+b, Con{+c, Con{+d, +t}}}}:
      %pl.le_le(t) : {Con{a, Con{b, Con{c, Con{d, V.packing.le_swap(V.packing.le_swap(t))}}}} == Con{a, Con{b, Con{c, Con{d, _}}}} : List<&2, U32>}
      {==}

def pl.le_len(xs: List<&2, U32>) -> {List.length(&2, U32, V.packing.le_swap(xs)) == List.length(&2, U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, Nil{}}:
      {==}
    case Con{a, Con{b, Nil{}}}:
      {==}
    case Con{a, Con{b, Con{c, Nil{}}}}:
      {==}
    case Con{a, Con{b, Con{c, Con{d, +t}}}}:
      %pl.le_len(t) : {4n+List.length(&2, U32, V.packing.le_swap(t)) == 4n+_ : Nat}
      {==}

def pl.le_mask(xs: List<&2, U32>) -> {V.packing.le_swap(B.mask(xs)) == B.mask(V.packing.le_swap(xs)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, Nil{}}:
      {==}
    case Con{a, Con{b, Nil{}}}:
      {==}
    case Con{a, Con{b, Con{c, Nil{}}}}:
      {==}
    case Con{+a, Con{+b, Con{+c, Con{+d, +t}}}}:
      %pl.le_mask(t) : {Con{B.byte(d), Con{B.byte(c), Con{B.byte(b), Con{B.byte(a), V.packing.le_swap(B.mask(t))}}}} == Con{B.byte(d), Con{B.byte(c), Con{B.byte(b), Con{B.byte(a), _}}}} : List<&2, U32>}
      {==}

# The reorderings

def pl.ou(+q: V.PkQuirks, +xs: List<&2, U32>) -> {V.packing.order(q, V.packing.unorder(q, xs)) == xs : List<&2, U32>}:
  match q:
    case V.PkQuirks{m, le, lsw}:
      match le lsw:
        case False{} False{}:
          {==}
        case True{} False{}:
          pl.le_le(xs)
        case False{} True{}:
          %Equal.sym(List<&2, U32>, List.reverse(&2, U32, List.reverse(&2, U32, V.packing.le_swap(xs))), V.packing.le_swap(xs), pl.rev_rev(U32, V.packing.le_swap(xs))) : {V.packing.le_swap(_) == xs : List<&2, U32>}
          pl.le_le(xs)
        case True{} True{}:
          pl.rev_rev(U32, xs)

def pl.order_len(+q: V.PkQuirks, +xs: List<&2, U32>) -> {List.length(&2, U32, V.packing.order(q, xs)) == List.length(&2, U32, xs) : Nat}:
  match q:
    case V.PkQuirks{m, le, lsw}:
      match le lsw:
        case False{} False{}:
          {==}
        case True{} False{}:
          pl.le_len(xs)
        case False{} True{}:
          Equal.trans(Nat, List.length(&2, U32, V.packing.le_swap(List.reverse(&2, U32, xs))), List.length(&2, U32, List.reverse(&2, U32, xs)), List.length(&2, U32, xs), pl.le_len(List.reverse(&2, U32, xs)), pl.rev_len(U32, xs))
        case True{} True{}:
          pl.rev_len(U32, xs)

def pl.unorder_len(+q: V.PkQuirks, +xs: List<&2, U32>) -> {List.length(&2, U32, V.packing.unorder(q, xs)) == List.length(&2, U32, xs) : Nat}:
  match q:
    case V.PkQuirks{m, le, lsw}:
      match le lsw:
        case False{} False{}:
          {==}
        case True{} False{}:
          pl.le_len(xs)
        case False{} True{}:
          Equal.trans(Nat, List.length(&2, U32, List.reverse(&2, U32, V.packing.le_swap(xs))), List.length(&2, U32, V.packing.le_swap(xs)), List.length(&2, U32, xs), pl.rev_len(U32, V.packing.le_swap(xs)), pl.le_len(xs))
        case True{} True{}:
          pl.rev_len(U32, xs)

def pl.order_mask(+q: V.PkQuirks, +xs: List<&2, U32>) -> {V.packing.order(q, B.mask(xs)) == B.mask(V.packing.order(q, xs)) : List<&2, U32>}:
  match q:
    case V.PkQuirks{m, le, lsw}:
      match le lsw:
        case False{} False{}:
          {==}
        case True{} False{}:
          pl.le_mask(xs)
        case False{} True{}:
          %Equal.sym(List<&2, U32>, List.reverse(&2, U32, B.mask(xs)), B.mask(List.reverse(&2, U32, xs)), pl.rev_mask(xs)) : {V.packing.le_swap(_) == B.mask(V.packing.le_swap(List.reverse(&2, U32, xs))) : List<&2, U32>}
          pl.le_mask(List.reverse(&2, U32, xs))
        case True{} True{}:
          pl.rev_mask(xs)

def pl.mask_len(xs: List<&2, U32>) -> {List.length(&2, U32, B.mask(xs)) == List.length(&2, U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, +t}:
      %pl.mask_len(t) : {1n+List.length(&2, U32, B.mask(t)) == 1n+_ : Nat}
      {==}

# Runs of bits

def pl.splice_len(bs: List<&2, Bool>, i: Nat, f: List<&2, Bool>) -> {List.length(&2, Bool, F.packing.splice(bs, i, f)) == List.length(&2, Bool, bs) : Nat}:
  match bs i f:
    case Nil{} _ _:
      {==}
    case Con{b, t} 0n Nil{}:
      {==}
    case Con{b, +t} 0n Con{x, +r}:
      %pl.splice_len(t, 0n, r) : {1n+List.length(&2, Bool, F.packing.splice(t, 0n, r)) == 1n+_ : Nat}
      {==}
    case Con{b, +t} 1n+ +j +g:
      %pl.splice_len(t, j, g) : {1n+List.length(&2, Bool, F.packing.splice(t, j, g)) == 1n+_ : Nat}
      {==}

def pl.or_r(y: Bool, -x: Bool, +h: {x == True{} : Bool}) -> {Bool.or(y, x) == True{} : Bool}:
  match y:
    case True{}:
      {==}
    case False{}:
      h

def pl.drop_splice(bs: List<&2, Bool>, i: Nat, f: List<&2, Bool>) -> {List.drop(&2, Bool, F.packing.splice(bs, i, f), i) == F.packing.splice(List.drop(&2, Bool, bs, i), 0n, f) : List<&2, Bool>}:
  match bs i f:
    case Nil{} _ _:
      {==}
    case Con{b, t} 0n Nil{}:
      {==}
    case Con{b, t} 0n Con{x, r}:
      {==}
    case Con{b, t} 1n+j g:
      pl.drop_splice(t, j, g)

def pl.take_splice(c: List<&2, Bool>, f: List<&2, Bool>, +h: {Nat.is_le(List.length(&2, Bool, f), List.length(&2, Bool, c)) == True{} : Bool}) -> {List.take(&2, Bool, F.packing.splice(c, 0n, f), List.length(&2, Bool, f)) == f : List<&2, Bool>}:
  match c f:
    case Nil{} Nil{}:
      {==}
    case Con{b, t} Nil{}:
      {==}
    case Nil{} Con{x, r}:
      Empty.absurd({Nil{} == Con{x, r} : List<&2, Bool>}, pl.ft(h))
    case Con{b, t} Con{+x, +r}:
      %pl.take_splice(t, r, h) : {Con{x, List.take(&2, Bool, F.packing.splice(t, 0n, r), List.length(&2, Bool, r))} == Con{x, _} : List<&2, Bool>}
      {==}

def pl.drop_len_le(bs: List<&2, Bool>, i: Nat, +n: Nat, +h: {Nat.is_le(Nat.add(i, n), List.length(&2, Bool, bs)) == True{} : Bool}) -> {Nat.is_le(n, List.length(&2, Bool, List.drop(&2, Bool, bs, i))) == True{} : Bool}:
  match bs i:
    case Nil{} 0n:
      h
    case Nil{} 1n+j:
      Empty.absurd({Nat.is_le(n, 0n) == True{} : Bool}, pl.ft(h))
    case Con{b, t} 0n:
      h
    case Con{b, t} 1n+j:
      pl.drop_len_le(t, j, n, h)

# the run just written reads back
def pl.slice_splice(+bs: List<&2, Bool>, +i: Nat, +f: List<&2, Bool>, +h: {Nat.is_le(Nat.add(i, List.length(&2, Bool, f)), List.length(&2, Bool, bs)) == True{} : Bool}) -> {F.packing.slice(F.packing.splice(bs, i, f), i, List.length(&2, Bool, f)) == f : List<&2, Bool>}:
  %Equal.sym(List<&2, Bool>, List.drop(&2, Bool, F.packing.splice(bs, i, f), i), F.packing.splice(List.drop(&2, Bool, bs, i), 0n, f), pl.drop_splice(bs, i, f)) : {List.take(&2, Bool, _, List.length(&2, Bool, f)) == f : List<&2, Bool>}
  pl.take_splice(List.drop(&2, Bool, bs, i), f, pl.drop_len_le(bs, i, List.length(&2, Bool, f), h))

def pl.nth_splice(bs: List<&2, Bool>, i: Nat, f: List<&2, Bool>, k: Nat, +h: {Bool.or(Nat.is_lt(k, i), Nat.is_le(Nat.add(i, List.length(&2, Bool, f)), k)) == True{} : Bool}) -> {F.packing.nth(F.packing.splice(bs, i, f), k) == F.packing.nth(bs, k) : Bool}:
  match bs i f k:
    case Nil{} _ _ _:
      {==}
    case Con{b, t} 0n Nil{} _:
      {==}
    case Con{b, t} 0n Con{x, r} 0n:
      Empty.absurd({x == b : Bool}, pl.ft(h))
    case Con{b, t} 0n Con{x, +r} 1n+ +kk:
      pl.nth_splice(t, 0n, r, kk, pl.or_r(Nat.is_lt(kk, 0n), Nat.is_le(List.length(&2, Bool, r), kk), h))
    case Con{b, t} 1n+j g 0n:
      {==}
    case Con{b, t} 1n+j g 1n+kk:
      pl.nth_splice(t, j, g, kk, h)
