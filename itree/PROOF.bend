# Proofs of LAWS.bend, for the U32 instance (ITree32).
#
# The plan:
# * U32's order: reflexive, EQ only on equal words, antisymmetric and
#   transitive, by induction on the bits of Base's Word.cmp; the order of
#   keys (start, then last) inherits all four.
# * Lists of entries: a sorted list (each key below every later one) splits
#   at any entry e into a sorted part before e, all below e, and a sorted
#   part after e, all above it.
# * The tree's in-order list: a rotation does not change it, so neither does
#   rebalancing; insertion and removal change it as the list model does,
#   by induction on the tree, using only the order facts and the split.
# * Queries: by induction on the tree, against the model's scan. A subtree
#   whose stored maximum is below the query's start holds only entries that
#   end before it (the stored maxima are right, by max_ok); a right subtree
#   whose node starts after the query's end holds only entries that start
#   after it (they are all above the node).
# * The invariant: every node is built by one constructor (ITree.mk) that
#   computes its maximum from its children, so max_ok survives every
#   operation; sortedness survives because the model's insertion and
#   removal keep a list sorted.
import Base
import ./itree.bend as T
import ./model.bend as M
import ./LAWS.bend as Laws
import ../u32/LAWS_order.bend as UO
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

def absurd.is_lt(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case o:
      Empty

def absurd.is_eq(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Unit
    case o:
      Empty

def absurd.is_gt(c: Cmp) -> Type:
  match c:
    case GT{}:
      Unit
    case o:
      Empty

def absurd.gt_lt(e: {GT{} == LT{} : Cmp}) -> Empty:
  %e : absurd.is_gt(_)
  Unit{}

def absurd.lt_eq(e: {LT{} == EQ{} : Cmp}) -> Empty:
  %e : absurd.is_lt(_)
  Unit{}

def absurd.gt_eq(e: {GT{} == EQ{} : Cmp}) -> Empty:
  %e : absurd.is_gt(_)
  Unit{}

def absurd.lt_gt(e: {LT{} == GT{} : Cmp}) -> Empty:
  %e : absurd.is_lt(_)
  Unit{}

def absurd.eq_gt(e: {EQ{} == GT{} : Cmp}) -> Empty:
  %e : absurd.is_eq(_)
  Unit{}

# Bool

def bool.and_l(x: Bool, -y: Bool, e: {Bool.and(x, y) == True{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))

def bool.and_r(x: Bool, -y: Bool, e: {Bool.and(x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      e
    case False{}:
      Empty.absurd({y == True{} : Bool}, absurd.ft(e))

def bool.and_intro(-x: Bool, -y: Bool, ex: {x == True{} : Bool}, ey: {y == True{} : Bool}) -> {Bool.and(x, y) == True{} : Bool}:
  %Equal.sym(Bool, x, True{}, ex) : {Bool.and(_, y) == True{} : Bool}
  ey

def bool.and_assoc(x: Bool, -y: Bool, -z: Bool) -> {Bool.and(Bool.and(x, y), z) == Bool.and(x, Bool.and(y, z)) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def bool.and_false(x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# Cmp

def cmp.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def cmp.lt_of(c: Cmp, e: {Cmp.is_lt(c) == True{} : Bool}) -> {c == LT{} : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({EQ{} == LT{} : Cmp}, absurd.ft(e))
    case GT{}:
      Empty.absurd({GT{} == LT{} : Cmp}, absurd.ft(e))

def cmp.eq_of(c: Cmp, e: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, absurd.ft(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, absurd.ft(e))

def cmp.gt_of(c: Cmp, e: {Cmp.is_gt(c) == True{} : Bool}) -> {c == GT{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == GT{} : Cmp}, absurd.ft(e))
    case EQ{}:
      Empty.absurd({EQ{} == GT{} : Cmp}, absurd.ft(e))
    case GT{}:
      {==}

# not GT, from is_le
def cmp.lt_of_not_ge(c: Cmp, e: {Cmp.is_ge(c) == False{} : Bool}) -> {c == LT{} : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({EQ{} == LT{} : Cmp}, absurd.tf(e))
    case GT{}:
      Empty.absurd({GT{} == LT{} : Cmp}, absurd.tf(e))

def cmp.gt_of_not_le(c: Cmp, e: {Cmp.is_le(c) == False{} : Bool}) -> {c == GT{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == GT{} : Cmp}, absurd.tf(e))
    case EQ{}:
      Empty.absurd({EQ{} == GT{} : Cmp}, absurd.tf(e))
    case GT{}:
      {==}

def cmp.flip_flip(c: Cmp) -> {cmp.flip(cmp.flip(c)) == c : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# Words: Base's order on Word(n), compared from the top bit down

def word.bool_flip(x: Bool, y: Bool) -> {Bool.cmp(y, x) == cmp.flip(Bool.cmp(x, y)) : Cmp}:
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def word.fin_flip(c: Cmp, x: Bool, y: Bool) -> {Word.cmp.fin(y, x, cmp.flip(c)) == cmp.flip(Word.cmp.fin(x, y, c)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      word.bool_flip(x, y)
    case GT{}:
      {==}

def word.flip(n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, b, a) == cmp.flip(Word.cmp(n, a, b)) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          %Equal.sym(Cmp, Word.cmp(p, bt, at), cmp.flip(Word.cmp(p, at, bt)), word.flip(p, at, bt)) : {Word.cmp.fin(y, x, _) == cmp.flip(Word.cmp.fin(x, y, Word.cmp(p, at, bt))) : Cmp}
          word.fin_flip(Word.cmp(p, at, bt), x, y)

# U32

def u32.flip(a: U32, b: U32) -> {U32.cmp(b, a) == cmp.flip(U32.cmp(a, b)) : Cmp}:
  match a b:
    case U32{+x} U32{+y}:
      word.flip(32n, x, y)

def u32.flip_of(+a: U32, +b: U32, c: Cmp, h: {U32.cmp(a, b) == c : Cmp}) -> {U32.cmp(b, a) == cmp.flip(c) : Cmp}:
  %h : {U32.cmp(b, a) == cmp.flip(_) : Cmp}
  u32.flip(a, b)

def u32.le_lt.go(c1: Cmp, +a: U32, +b: U32, +c: U32, e1: {U32.cmp(a, b) == c1 : Cmp}, h1: {Cmp.is_le(c1) == True{} : Bool}, h2: {U32.cmp(b, c) == LT{} : Cmp}) -> {U32.cmp(a, c) == LT{} : Cmp}:
  match c1:
    case LT{}:
      UO.u32_cmp_lt_trans(a, b, c, e1, h2)
    case EQ{}:
      %Equal.sym(U32, a, b, UO.u32_cmp_eq(a, b, e1)) : {U32.cmp(_, c) == LT{} : Cmp}
      h2
    case GT{}:
      Empty.absurd({U32.cmp(a, c) == LT{} : Cmp}, absurd.ft(h1))

# a <= b < c
def u32.le_lt(+a: U32, +b: U32, +c: U32, h1: {Cmp.is_le(U32.cmp(a, b)) == True{} : Bool}, h2: {U32.cmp(b, c) == LT{} : Cmp}) -> {U32.cmp(a, c) == LT{} : Cmp}:
  u32.le_lt.go(U32.cmp(a, b), a, b, c, {==}, h1, h2)

def u32.lt_le.go(c2: Cmp, +a: U32, +b: U32, +c: U32, e2: {U32.cmp(b, c) == c2 : Cmp}, h1: {U32.cmp(a, b) == LT{} : Cmp}, h2: {Cmp.is_le(c2) == True{} : Bool}) -> {U32.cmp(a, c) == LT{} : Cmp}:
  match c2:
    case LT{}:
      UO.u32_cmp_lt_trans(a, b, c, h1, e2)
    case EQ{}:
      %UO.u32_cmp_eq(b, c, e2) : {U32.cmp(a, _) == LT{} : Cmp}
      h1
    case GT{}:
      Empty.absurd({U32.cmp(a, c) == LT{} : Cmp}, absurd.ft(h2))

# a < b <= c
def u32.lt_le(+a: U32, +b: U32, +c: U32, h1: {U32.cmp(a, b) == LT{} : Cmp}, h2: {Cmp.is_le(U32.cmp(b, c)) == True{} : Bool}) -> {U32.cmp(a, c) == LT{} : Cmp}:
  u32.lt_le.go(U32.cmp(b, c), a, b, c, {==}, h1, h2)

def u32.le_le.go(c1: Cmp, +a: U32, +b: U32, +c: U32, e1: {U32.cmp(a, b) == c1 : Cmp}, h1: {Cmp.is_le(c1) == True{} : Bool}, h2: {Cmp.is_le(U32.cmp(b, c)) == True{} : Bool}) -> {Cmp.is_le(U32.cmp(a, c)) == True{} : Bool}:
  match c1:
    case LT{}:
      %Equal.sym(Cmp, U32.cmp(a, c), LT{}, u32.lt_le(a, b, c, e1, h2)) : {Cmp.is_le(_) == True{} : Bool}
      {==}
    case EQ{}:
      %Equal.sym(U32, a, b, UO.u32_cmp_eq(a, b, e1)) : {Cmp.is_le(U32.cmp(_, c)) == True{} : Bool}
      h2
    case GT{}:
      Empty.absurd({Cmp.is_le(U32.cmp(a, c)) == True{} : Bool}, absurd.ft(h1))

# a <= b <= c
def u32.le_le(+a: U32, +b: U32, +c: U32, h1: {Cmp.is_le(U32.cmp(a, b)) == True{} : Bool}, h2: {Cmp.is_le(U32.cmp(b, c)) == True{} : Bool}) -> {Cmp.is_le(U32.cmp(a, c)) == True{} : Bool}:
  u32.le_le.go(U32.cmp(a, b), a, b, c, {==}, h1, h2)

# Keys: (start, last), by start then by last

def kc(+s1: U32, +l1: U32, +s2: U32, +l2: U32) -> Cmp:
  T.ITree.key_cmp(~U32, ~U32.cmp, s1, l1, s2, l2)

def kgo(c: Cmp, +l1: U32, +l2: U32) -> Cmp:
  T.ITree.key_cmp.go(~U32, ~U32.cmp, c, l1, l2)

def kc.refl(+s: U32, +l: U32) -> {kc(s, l, s, l) == EQ{} : Cmp}:
  %Equal.sym(Cmp, U32.cmp(s, s), EQ{}, UO.u32_cmp_refl(s)) : {kgo(_, l, l) == EQ{} : Cmp}
  UO.u32_cmp_refl(l)

def kc.eq_s.go(c: Cmp, +s1: U32, -l1: U32, +s2: U32, -l2: U32, e: {U32.cmp(s1, s2) == c : Cmp}, h: {kgo(c, l1, l2) == EQ{} : Cmp}) -> {s1 == s2 : U32}:
  match c:
    case LT{}:
      Empty.absurd({s1 == s2 : U32}, absurd.lt_eq(h))
    case EQ{}:
      UO.u32_cmp_eq(s1, s2, e)
    case GT{}:
      Empty.absurd({s1 == s2 : U32}, absurd.gt_eq(h))

def kc.eq_s(+s1: U32, +l1: U32, +s2: U32, +l2: U32, h: {kc(s1, l1, s2, l2) == EQ{} : Cmp}) -> {s1 == s2 : U32}:
  kc.eq_s.go(U32.cmp(s1, s2), s1, l1, s2, l2, {==}, h)

def kc.eq_l.go(c: Cmp, +l1: U32, +l2: U32, h: {kgo(c, l1, l2) == EQ{} : Cmp}) -> {l1 == l2 : U32}:
  match c:
    case LT{}:
      Empty.absurd({l1 == l2 : U32}, absurd.lt_eq(h))
    case EQ{}:
      UO.u32_cmp_eq(l1, l2, h)
    case GT{}:
      Empty.absurd({l1 == l2 : U32}, absurd.gt_eq(h))

def kc.eq_l(+s1: U32, +l1: U32, +s2: U32, +l2: U32, h: {kc(s1, l1, s2, l2) == EQ{} : Cmp}) -> {l1 == l2 : U32}:
  kc.eq_l.go(U32.cmp(s1, s2), l1, l2, h)

def kc.flip.go(c: Cmp, +l1: U32, +l2: U32) -> {kgo(cmp.flip(c), l2, l1) == cmp.flip(kgo(c, l1, l2)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      u32.flip(l1, l2)
    case GT{}:
      {==}

def kc.flip(+s1: U32, +l1: U32, +s2: U32, +l2: U32) -> {kc(s2, l2, s1, l1) == cmp.flip(kc(s1, l1, s2, l2)) : Cmp}:
  %Equal.sym(Cmp, U32.cmp(s2, s1), cmp.flip(U32.cmp(s1, s2)), u32.flip(s1, s2)) : {kgo(_, l2, l1) == cmp.flip(kgo(U32.cmp(s1, s2), l1, l2)) : Cmp}
  kc.flip.go(U32.cmp(s1, s2), l1, l2)

def kc.flip_of(+s1: U32, +l1: U32, +s2: U32, +l2: U32, c: Cmp, h: {kc(s1, l1, s2, l2) == c : Cmp}) -> {kc(s2, l2, s1, l1) == cmp.flip(c) : Cmp}:
  %h : {kc(s2, l2, s1, l1) == cmp.flip(_) : Cmp}
  kc.flip(s1, l1, s2, l2)

def kc.lt_trans.go(c1: Cmp, c2: Cmp, +s1: U32, +l1: U32, +s2: U32, +l2: U32, +s3: U32, +l3: U32, e1: {U32.cmp(s1, s2) == c1 : Cmp}, e2: {U32.cmp(s2, s3) == c2 : Cmp}, h1: {kgo(c1, l1, l2) == LT{} : Cmp}, h2: {kgo(c2, l2, l3) == LT{} : Cmp}) -> {kgo(U32.cmp(s1, s3), l1, l3) == LT{} : Cmp}:
  match c1 c2:
    case LT{} LT{}:
      %Equal.sym(Cmp, U32.cmp(s1, s3), LT{}, UO.u32_cmp_lt_trans(s1, s2, s3, e1, e2)) : {kgo(_, l1, l3) == LT{} : Cmp}
      {==}
    case LT{} EQ{}:
      %UO.u32_cmp_eq(s2, s3, e2) : {kgo(U32.cmp(s1, _), l1, l3) == LT{} : Cmp}
      %Equal.sym(Cmp, U32.cmp(s1, s2), LT{}, e1) : {kgo(_, l1, l3) == LT{} : Cmp}
      {==}
    case EQ{} LT{}:
      %Equal.sym(U32, s1, s2, UO.u32_cmp_eq(s1, s2, e1)) : {kgo(U32.cmp(_, s3), l1, l3) == LT{} : Cmp}
      %Equal.sym(Cmp, U32.cmp(s2, s3), LT{}, e2) : {kgo(_, l1, l3) == LT{} : Cmp}
      {==}
    case EQ{} EQ{}:
      %Equal.trans(U32, s1, s2, s3, UO.u32_cmp_eq(s1, s2, e1), UO.u32_cmp_eq(s2, s3, e2)) : {kgo(U32.cmp(s1, _), l1, l3) == LT{} : Cmp}
      %Equal.sym(Cmp, U32.cmp(s1, s1), EQ{}, UO.u32_cmp_refl(s1)) : {kgo(_, l1, l3) == LT{} : Cmp}
      UO.u32_cmp_lt_trans(l1, l2, l3, h1, h2)
    case GT{} c2:
      Empty.absurd({kgo(U32.cmp(s1, s3), l1, l3) == LT{} : Cmp}, absurd.gt_lt(h1))
    case c1 GT{}:
      Empty.absurd({kgo(U32.cmp(s1, s3), l1, l3) == LT{} : Cmp}, absurd.gt_lt(h2))

def kc.lt_trans(+s1: U32, +l1: U32, +s2: U32, +l2: U32, +s3: U32, +l3: U32, h1: {kc(s1, l1, s2, l2) == LT{} : Cmp}, h2: {kc(s2, l2, s3, l3) == LT{} : Cmp}) -> {kc(s1, l1, s3, l3) == LT{} : Cmp}:
  kc.lt_trans.go(U32.cmp(s1, s2), U32.cmp(s2, s3), s1, l1, s2, l2, s3, l3, {==}, {==}, h1, h2)

def kc.gt_trans(+s1: U32, +l1: U32, +s2: U32, +l2: U32, +s3: U32, +l3: U32, h1: {kc(s1, l1, s2, l2) == GT{} : Cmp}, h2: {kc(s2, l2, s3, l3) == GT{} : Cmp}) -> {kc(s1, l1, s3, l3) == GT{} : Cmp}:
  kc.flip_of(s3, l3, s1, l1, LT{}, kc.lt_trans(s3, l3, s2, l2, s1, l1, kc.flip_of(s2, l2, s3, l3, GT{}, h2), kc.flip_of(s1, l1, s2, l2, GT{}, h1)))

def kc.start_le.go(c: Cmp, +l1: U32, +l2: U32, h: {kgo(c, l1, l2) == LT{} : Cmp}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.gt_lt(h))

# a key below another starts no later
def kc.start_le(+s1: U32, +l1: U32, +s2: U32, +l2: U32, h: {kc(s1, l1, s2, l2) == LT{} : Cmp}) -> {Cmp.is_le(U32.cmp(s1, s2)) == True{} : Bool}:
  kc.start_le.go(U32.cmp(s1, s2), l1, l2, h)

# equal keys compare alike
def kc.subst_l(+s1: U32, +l1: U32, +s2: U32, +l2: U32, +s3: U32, +l3: U32, +h: {kc(s1, l1, s2, l2) == EQ{} : Cmp}) -> {kc(s1, l1, s3, l3) == kc(s2, l2, s3, l3) : Cmp}:
  %kc.eq_s(s1, l1, s2, l2, h) : {kc(s1, l1, s3, l3) == kc(_, l2, s3, l3) : Cmp}
  %kc.eq_l(s1, l1, s2, l2, h) : {kc(s1, l1, s3, l3) == kc(s1, _, s3, l3) : Cmp}
  {==}

def kc.ge_gt.go(c: Cmp, +s1: U32, +l1: U32, +s2: U32, +l2: U32, +s3: U32, +l3: U32, +e: {kc(s1, l1, s2, l2) == c : Cmp}, h1: {Cmp.is_lt(c) == False{} : Bool}, h2: {kc(s2, l2, s3, l3) == GT{} : Cmp}) -> {kc(s1, l1, s3, l3) == GT{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({kc(s1, l1, s3, l3) == GT{} : Cmp}, absurd.tf(h1))
    case EQ{}:
      %Equal.sym(Cmp, kc(s1, l1, s3, l3), kc(s2, l2, s3, l3), kc.subst_l(s1, l1, s2, l2, s3, l3, e)) : {_ == GT{} : Cmp}
      h2
    case GT{}:
      kc.gt_trans(s1, l1, s2, l2, s3, l3, e, h2)

# k1 >= k2 > k3
def kc.ge_gt(+s1: U32, +l1: U32, +s2: U32, +l2: U32, +s3: U32, +l3: U32, h1: {Cmp.is_lt(kc(s1, l1, s2, l2)) == False{} : Bool}, h2: {kc(s2, l2, s3, l3) == GT{} : Cmp}) -> {kc(s1, l1, s3, l3) == GT{} : Cmp}:
  kc.ge_gt.go(kc(s1, l1, s2, l2), s1, l1, s2, l2, s3, l3, {==}, h1, h2)

# Shorthands for the U32 instance (they unfold to the package's defs)

def Ent(-V: Data) -> Data:
  T.ITreeEntry<U32, V>

def Es(-V: Data) -> Data:
  List<&2, T.ITreeEntry<U32, V>>

def Tr(-V: Data) -> Data:
  T.ITree<U32, V>

def st(-V: Data, e: Ent(V)) -> U32:
  T.ITreeEntry.start(U32, V, e)

def la(-V: Data, e: Ent(V)) -> U32:
  T.ITreeEntry.last(U32, V, e)

def ec(-V: Data, +s: U32, +l: U32, +e: Ent(V)) -> Cmp:
  T.ITree.entry_cmp(~U32, ~U32.cmp, V, s, l, e)

def app(-V: Data, xs: Es(V), ys: Es(V)) -> Es(V):
  List.append(&2, T.ITreeEntry<U32, V>, xs, ys)

def aft(-V: Data, +s: U32, +l: U32, xs: Es(V)) -> Bool:
  T.ITree.all_after(~U32, ~U32.cmp, V, s, l, xs)

def srt(-V: Data, xs: Es(V)) -> Bool:
  T.ITree.sorted(~U32, ~U32.cmp, V, xs)

def L(-V: Data, t: Tr(V)) -> Es(V):
  T.ITree.to_list(U32, V, t)

def keep(-V: Data, b: Bool, x: Ent(V), r: Es(V)) -> Es(V):
  T.ITree.keep(U32, V, b, x, r)

# every entry of xs comes before the key (s, l)
def bef(-V: Data, xs: Es(V), +s: U32, +l: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +r}:
      Bool.and(Cmp.is_gt(ec(V, s, l, x)), bef(V, r, s, l))

def mins(-V: Data, xs: Es(V), +s: U32, +l: U32, +v: V) -> Es(V):
  M.ITreeModel.insert(~U32, ~U32.cmp, V, xs, s, l, v)

def mrem(-V: Data, xs: Es(V), +s: U32, +l: U32) -> Es(V):
  M.ITreeModel.remove(~U32, ~U32.cmp, V, xs, s, l)

def mlook(-V: Data, xs: Es(V), +s: U32, +l: U32) -> Maybe<&2, V>:
  M.ITreeModel.lookup(~U32, ~U32.cmp, V, xs, s, l)

def orv(-V: Data, m: Maybe<&2, V>, n: Maybe<&2, V>) -> Maybe<&2, V>:
  match m:
    case Some{x}:
      Some{x}
    case None{}:
      n

# Small facts

def bool.rw(-x: Bool, -y: Bool, e: {x == y : Bool}, h: {x == True{} : Bool}) -> {y == True{} : Bool}:
  %e : {_ == True{} : Bool}
  h

def cmp.is_lt_of(-c: Cmp, e: {c == LT{} : Cmp}) -> {Cmp.is_lt(c) == True{} : Bool}:
  %Equal.sym(Cmp, c, LT{}, e) : {Cmp.is_lt(_) == True{} : Bool}
  {==}

def cmp.is_gt_of(-c: Cmp, e: {c == GT{} : Cmp}) -> {Cmp.is_gt(c) == True{} : Bool}:
  %Equal.sym(Cmp, c, GT{}, e) : {Cmp.is_gt(_) == True{} : Bool}
  {==}

def app.assoc(-V: Data, xs: Es(V), +ys: Es(V), +zs: Es(V)) -> {app(V, app(V, xs, ys), zs) == app(V, xs, app(V, ys, zs)) : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %app.assoc(V, r, ys, zs) : {Con{x, app(V, app(V, r, ys), zs)} == Con{x, _} : Es(V)}
      {==}

def app.nil(-V: Data, xs: Es(V)) -> {app(V, xs, Nil{}) == xs : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %app.nil(V, r) : {Con{x, app(V, r, Nil{})} == Con{x, _} : Es(V)}
      {==}

def keep.app(-V: Data, b: Bool, +x: Ent(V), p: Es(V), +q: Es(V)) -> {keep(V, b, x, app(V, p, q)) == app(V, keep(V, b, x, p), q) : Es(V)}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def aft.app(-V: Data, +s: U32, +l: U32, xs: Es(V), +ys: Es(V)) -> {aft(V, s, l, app(V, xs, ys)) == Bool.and(aft(V, s, l, xs), aft(V, s, l, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(Bool, aft(V, s, l, app(V, r, ys)), Bool.and(aft(V, s, l, r), aft(V, s, l, ys)), aft.app(V, s, l, r, ys)) : {Bool.and(Cmp.is_lt(ec(V, s, l, x)), _) == Bool.and(Bool.and(Cmp.is_lt(ec(V, s, l, x)), aft(V, s, l, r)), aft(V, s, l, ys)) : Bool}
      Equal.sym(Bool, Bool.and(Bool.and(Cmp.is_lt(ec(V, s, l, x)), aft(V, s, l, r)), aft(V, s, l, ys)), Bool.and(Cmp.is_lt(ec(V, s, l, x)), Bool.and(aft(V, s, l, r), aft(V, s, l, ys))), bool.and_assoc(Cmp.is_lt(ec(V, s, l, x)), aft(V, s, l, r), aft(V, s, l, ys)))

# Sorted lists

def srt.left(-V: Data, xs: Es(V), +ys: Es(V), h: {srt(V, app(V, xs, ys)) == True{} : Bool}) -> {srt(V, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h = h
      +ha = bool.rw(aft(V, st(V, x), la(V, x), app(V, r, ys)), Bool.and(aft(V, st(V, x), la(V, x), r), aft(V, st(V, x), la(V, x), ys)), aft.app(V, st(V, x), la(V, x), r, ys), bool.and_l(aft(V, st(V, x), la(V, x), app(V, r, ys)), srt(V, app(V, r, ys)), h))
      bool.and_intro(aft(V, st(V, x), la(V, x), r), srt(V, r), bool.and_l(aft(V, st(V, x), la(V, x), r), aft(V, st(V, x), la(V, x), ys), ha), srt.left(V, r, ys, bool.and_r(aft(V, st(V, x), la(V, x), app(V, r, ys)), srt(V, app(V, r, ys)), h)))

def srt.right(-V: Data, xs: Es(V), +ys: Es(V), h: {srt(V, app(V, xs, ys)) == True{} : Bool}) -> {srt(V, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+x, +r}:
      srt.right(V, r, ys, bool.and_r(aft(V, st(V, x), la(V, x), app(V, r, ys)), srt(V, app(V, r, ys)), h))

# the tail of a sorted list headed by e comes after e
def srt.head(-V: Data, +e: Ent(V), +ys: Es(V), h: {srt(V, Con{e, ys}) == True{} : Bool}) -> {aft(V, st(V, e), la(V, e), ys) == True{} : Bool}:
  bool.and_l(aft(V, st(V, e), la(V, e), ys), srt(V, ys), h)

def srt.tail(-V: Data, +e: Ent(V), +ys: Es(V), h: {srt(V, Con{e, ys}) == True{} : Bool}) -> {srt(V, ys) == True{} : Bool}:
  bool.and_r(aft(V, st(V, e), la(V, e), ys), srt(V, ys), h)

# in a sorted list, everything before e comes before it
def srt.bef(-V: Data, xs: Es(V), +e: Ent(V), +ys: Es(V), h: {srt(V, app(V, xs, Con{e, ys})) == True{} : Bool}) -> {bef(V, xs, st(V, e), la(V, e)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h = h
      +ha = bool.rw(aft(V, st(V, x), la(V, x), app(V, r, Con{e, ys})), Bool.and(aft(V, st(V, x), la(V, x), r), aft(V, st(V, x), la(V, x), Con{e, ys})), aft.app(V, st(V, x), la(V, x), r, Con{e, ys}), bool.and_l(aft(V, st(V, x), la(V, x), app(V, r, Con{e, ys})), srt(V, app(V, r, Con{e, ys})), h))
      +hxe = bool.and_r(aft(V, st(V, x), la(V, x), r), aft(V, st(V, x), la(V, x), Con{e, ys}), ha)
      +lt = cmp.lt_of(ec(V, st(V, x), la(V, x), e), bool.and_l(Cmp.is_lt(ec(V, st(V, x), la(V, x), e)), aft(V, st(V, x), la(V, x), ys), hxe))
      bool.and_intro(Cmp.is_gt(ec(V, st(V, e), la(V, e), x)), bef(V, r, st(V, e), la(V, e)), cmp.is_gt_of(ec(V, st(V, e), la(V, e), x), kc.flip_of(st(V, x), la(V, x), st(V, e), la(V, e), LT{}, lt)), srt.bef(V, r, e, ys, bool.and_r(aft(V, st(V, x), la(V, x), app(V, r, Con{e, ys})), srt(V, app(V, r, Con{e, ys})), h)))

# all after k2, and k < k2: all after k
def aft.weaken(-V: Data, +s: U32, +l: U32, +s2: U32, +l2: U32, xs: Es(V), h: {aft(V, s2, l2, xs) == True{} : Bool}, +g: {kc(s, l, s2, l2) == LT{} : Cmp}) -> {aft(V, s, l, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h = h
      +lt = cmp.lt_of(ec(V, s2, l2, x), bool.and_l(Cmp.is_lt(ec(V, s2, l2, x)), aft(V, s2, l2, r), h))
      bool.and_intro(Cmp.is_lt(ec(V, s, l, x)), aft(V, s, l, r), cmp.is_lt_of(ec(V, s, l, x), kc.lt_trans(s, l, s2, l2, st(V, x), la(V, x), g, lt)), aft.weaken(V, s, l, s2, l2, r, bool.and_r(Cmp.is_lt(ec(V, s2, l2, x)), aft(V, s2, l2, r), h), g))

def aft.eqk(-V: Data, +s: U32, +l: U32, +s2: U32, +l2: U32, xs: Es(V), h: {aft(V, s2, l2, xs) == True{} : Bool}, +g: {kc(s, l, s2, l2) == EQ{} : Cmp}) -> {aft(V, s, l, xs) == True{} : Bool}:
  %Equal.sym(U32, s, s2, kc.eq_s(s, l, s2, l2, g)) : {aft(V, _, l, xs) == True{} : Bool}
  %Equal.sym(U32, l, l2, kc.eq_l(s, l, s2, l2, g)) : {aft(V, s2, _, xs) == True{} : Bool}
  h

# all before k2, and k > k2: all before k
def bef.weaken(-V: Data, xs: Es(V), +s: U32, +l: U32, +s2: U32, +l2: U32, h: {bef(V, xs, s2, l2) == True{} : Bool}, +g: {kc(s, l, s2, l2) == GT{} : Cmp}) -> {bef(V, xs, s, l) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h = h
      +gt = cmp.gt_of(ec(V, s2, l2, x), bool.and_l(Cmp.is_gt(ec(V, s2, l2, x)), bef(V, r, s2, l2), h))
      bool.and_intro(Cmp.is_gt(ec(V, s, l, x)), bef(V, r, s, l), cmp.is_gt_of(ec(V, s, l, x), kc.gt_trans(s, l, s2, l2, st(V, x), la(V, x), g, gt)), bef.weaken(V, r, s, l, s2, l2, bool.and_r(Cmp.is_gt(ec(V, s2, l2, x)), bef(V, r, s2, l2), h), g))

def bef.eqk(-V: Data, xs: Es(V), +s: U32, +l: U32, +s2: U32, +l2: U32, h: {bef(V, xs, s2, l2) == True{} : Bool}, +g: {kc(s, l, s2, l2) == EQ{} : Cmp}) -> {bef(V, xs, s, l) == True{} : Bool}:
  %Equal.sym(U32, s, s2, kc.eq_s(s, l, s2, l2, g)) : {bef(V, xs, _, l) == True{} : Bool}
  %Equal.sym(U32, l, l2, kc.eq_l(s, l, s2, l2, g)) : {bef(V, xs, s2, _) == True{} : Bool}
  h

# Tree shape: rotations keep the order of the entries

def rot_r.go.list(dbl: Bool, -V: Data, +ll: Tr(V), +le: Ent(V), lr: Tr(V), +e: Ent(V), +r: Tr(V)) -> {L(V, T.ITree.rot_r.go(~U32, ~U32.cmp, V, dbl, ll, le, lr, e, r)) == app(V, app(V, L(V, ll), Con{le, L(V, lr)}), Con{e, L(V, r)}) : Es(V)}:
  match dbl:
    case False{}:
      Equal.sym(Es(V), app(V, app(V, L(V, ll), Con{le, L(V, lr)}), Con{e, L(V, r)}), app(V, L(V, ll), app(V, Con{le, L(V, lr)}, Con{e, L(V, r)})), app.assoc(V, L(V, ll), Con{le, L(V, lr)}, Con{e, L(V, r)}))
    case True{}:
      match lr:
        case T.ITreeLeaf{}:
          Equal.sym(Es(V), app(V, app(V, L(V, ll), Con{le, Nil{}}), Con{e, L(V, r)}), app(V, L(V, ll), app(V, Con{le, Nil{}}, Con{e, L(V, r)})), app.assoc(V, L(V, ll), Con{le, Nil{}}, Con{e, L(V, r)}))
        case T.ITreeNode{h2, m2, +lrl, +lre, +lrr}:
          %Equal.sym(Es(V), app(V, app(V, L(V, ll), Con{le, L(V, lrl)}), Con{lre, app(V, L(V, lrr), Con{e, L(V, r)})}), app(V, L(V, ll), app(V, Con{le, L(V, lrl)}, Con{lre, app(V, L(V, lrr), Con{e, L(V, r)})})), app.assoc(V, L(V, ll), Con{le, L(V, lrl)}, Con{lre, app(V, L(V, lrr), Con{e, L(V, r)})})) : {_ == app(V, app(V, L(V, ll), Con{le, app(V, L(V, lrl), Con{lre, L(V, lrr)})}), Con{e, L(V, r)}) : Es(V)}
          %Equal.sym(Es(V), app(V, app(V, L(V, ll), Con{le, app(V, L(V, lrl), Con{lre, L(V, lrr)})}), Con{e, L(V, r)}), app(V, L(V, ll), app(V, Con{le, app(V, L(V, lrl), Con{lre, L(V, lrr)})}, Con{e, L(V, r)})), app.assoc(V, L(V, ll), Con{le, app(V, L(V, lrl), Con{lre, L(V, lrr)})}, Con{e, L(V, r)})) : {app(V, L(V, ll), Con{le, app(V, L(V, lrl), Con{lre, app(V, L(V, lrr), Con{e, L(V, r)})})}) == _ : Es(V)}
          %Equal.sym(Es(V), app(V, app(V, L(V, lrl), Con{lre, L(V, lrr)}), Con{e, L(V, r)}), app(V, L(V, lrl), app(V, Con{lre, L(V, lrr)}, Con{e, L(V, r)})), app.assoc(V, L(V, lrl), Con{lre, L(V, lrr)}, Con{e, L(V, r)})) : {app(V, L(V, ll), Con{le, app(V, L(V, lrl), Con{lre, app(V, L(V, lrr), Con{e, L(V, r)})})}) == app(V, L(V, ll), Con{le, _}) : Es(V)}
          {==}

def rot_r.list(-V: Data, l: Tr(V), +e: Ent(V), +r: Tr(V)) -> {L(V, T.ITree.rot_r(~U32, ~U32.cmp, V, l, e, r)) == app(V, L(V, l), Con{e, L(V, r)}) : Es(V)}:
  match l:
    case T.ITreeLeaf{}:
      {==}
    case T.ITreeNode{h, m, +ll, +le, +lr}:
      rot_r.go.list(Nat.is_lt(T.ITree.height(U32, V, ll), T.ITree.height(U32, V, lr)), V, ll, le, lr, e, r)

def rot_l.go.list(dbl: Bool, -V: Data, +l: Tr(V), +e: Ent(V), rl: Tr(V), +re: Ent(V), +rr: Tr(V)) -> {L(V, T.ITree.rot_l.go(~U32, ~U32.cmp, V, dbl, l, e, rl, re, rr)) == app(V, L(V, l), Con{e, app(V, L(V, rl), Con{re, L(V, rr)})}) : Es(V)}:
  match dbl:
    case False{}:
      app.assoc(V, L(V, l), Con{e, L(V, rl)}, Con{re, L(V, rr)})
    case True{}:
      match rl:
        case T.ITreeLeaf{}:
          app.assoc(V, L(V, l), Con{e, Nil{}}, Con{re, L(V, rr)})
        case T.ITreeNode{h2, m2, +rll, +rle, +rlr}:
          %Equal.sym(Es(V), app(V, app(V, L(V, l), Con{e, L(V, rll)}), Con{rle, app(V, L(V, rlr), Con{re, L(V, rr)})}), app(V, L(V, l), app(V, Con{e, L(V, rll)}, Con{rle, app(V, L(V, rlr), Con{re, L(V, rr)})})), app.assoc(V, L(V, l), Con{e, L(V, rll)}, Con{rle, app(V, L(V, rlr), Con{re, L(V, rr)})})) : {_ == app(V, L(V, l), Con{e, app(V, app(V, L(V, rll), Con{rle, L(V, rlr)}), Con{re, L(V, rr)})}) : Es(V)}
          %Equal.sym(Es(V), app(V, app(V, L(V, rll), Con{rle, L(V, rlr)}), Con{re, L(V, rr)}), app(V, L(V, rll), app(V, Con{rle, L(V, rlr)}, Con{re, L(V, rr)})), app.assoc(V, L(V, rll), Con{rle, L(V, rlr)}, Con{re, L(V, rr)})) : {app(V, L(V, l), Con{e, app(V, L(V, rll), Con{rle, app(V, L(V, rlr), Con{re, L(V, rr)})})}) == app(V, L(V, l), Con{e, _}) : Es(V)}
          {==}

def rot_l.list(-V: Data, +l: Tr(V), +e: Ent(V), r: Tr(V)) -> {L(V, T.ITree.rot_l(~U32, ~U32.cmp, V, l, e, r)) == app(V, L(V, l), Con{e, L(V, r)}) : Es(V)}:
  match r:
    case T.ITreeLeaf{}:
      {==}
    case T.ITreeNode{h, m, +rl, +re, +rr}:
      rot_l.go.list(Nat.is_lt(T.ITree.height(U32, V, rr), T.ITree.height(U32, V, rl)), V, l, e, rl, re, rr)

def bal.go.list(lh: Bool, rh: Bool, -V: Data, +l: Tr(V), +e: Ent(V), +r: Tr(V)) -> {L(V, T.ITree.bal.go(~U32, ~U32.cmp, V, lh, rh, l, e, r)) == app(V, L(V, l), Con{e, L(V, r)}) : Es(V)}:
  match lh:
    case True{}:
      rot_r.list(V, l, e, r)
    case False{}:
      match rh:
        case True{}:
          rot_l.list(V, l, e, r)
        case False{}:
          {==}

def bal.list(-V: Data, +l: Tr(V), +e: Ent(V), +r: Tr(V)) -> {L(V, T.ITree.bal(~U32, ~U32.cmp, V, l, e, r)) == app(V, L(V, l), Con{e, L(V, r)}) : Es(V)}:
  bal.go.list(Nat.is_lt(1n+T.ITree.height(U32, V, r), T.ITree.height(U32, V, l)), Nat.is_lt(1n+T.ITree.height(U32, V, l), T.ITree.height(U32, V, r)), V, l, e, r)

def dm.list(-V: Data, t: Tr(V), +e: Ent(V), +r: Tr(V)) -> {Con{T.ITree.min_of(U32, V, t, e), L(V, T.ITree.del_min(~U32, ~U32.cmp, V, t, e, r))} == app(V, L(V, t), Con{e, L(V, r)}) : Es(V)}:
  match t:
    case T.ITreeLeaf{}:
      {==}
    case T.ITreeNode{h, m, +l2, +e2, +r2}:
      %Equal.sym(Es(V), L(V, T.ITree.bal(~U32, ~U32.cmp, V, T.ITree.del_min(~U32, ~U32.cmp, V, l2, e2, r2), e, r)), app(V, L(V, T.ITree.del_min(~U32, ~U32.cmp, V, l2, e2, r2)), Con{e, L(V, r)}), bal.list(V, T.ITree.del_min(~U32, ~U32.cmp, V, l2, e2, r2), e, r)) : {Con{T.ITree.min_of(U32, V, l2, e2), _} == app(V, app(V, L(V, l2), Con{e2, L(V, r2)}), Con{e, L(V, r)}) : Es(V)}
      %Equal.sym(Es(V), Con{T.ITree.min_of(U32, V, l2, e2), L(V, T.ITree.del_min(~U32, ~U32.cmp, V, l2, e2, r2))}, app(V, L(V, l2), Con{e2, L(V, r2)}), dm.list(V, l2, e2, r2)) : {app(V, _, Con{e, L(V, r)}) == app(V, app(V, L(V, l2), Con{e2, L(V, r2)}), Con{e, L(V, r)}) : Es(V)}
      {==}

def merge.list(-V: Data, +l: Tr(V), r: Tr(V)) -> {L(V, T.ITree.merge(~U32, ~U32.cmp, V, l, r)) == app(V, L(V, l), L(V, r)) : Es(V)}:
  match r:
    case T.ITreeLeaf{}:
      Equal.sym(Es(V), app(V, L(V, l), Nil{}), L(V, l), app.nil(V, L(V, l)))
    case T.ITreeNode{h, m, +rl, +re, +rr}:
      %Equal.sym(Es(V), L(V, T.ITree.bal(~U32, ~U32.cmp, V, l, T.ITree.min_of(U32, V, rl, re), T.ITree.del_min(~U32, ~U32.cmp, V, rl, re, rr))), app(V, L(V, l), Con{T.ITree.min_of(U32, V, rl, re), L(V, T.ITree.del_min(~U32, ~U32.cmp, V, rl, re, rr))}), bal.list(V, l, T.ITree.min_of(U32, V, rl, re), T.ITree.del_min(~U32, ~U32.cmp, V, rl, re, rr))) : {_ == app(V, L(V, l), app(V, L(V, rl), Con{re, L(V, rr)})) : Es(V)}
      %Equal.sym(Es(V), Con{T.ITree.min_of(U32, V, rl, re), L(V, T.ITree.del_min(~U32, ~U32.cmp, V, rl, re, rr))}, app(V, L(V, rl), Con{re, L(V, rr)}), dm.list(V, rl, re, rr)) : {app(V, L(V, l), _) == app(V, L(V, l), app(V, L(V, rl), Con{re, L(V, rr)})) : Es(V)}
      {==}

# Insertion: the tree's contents follow the model's

def igo(-V: Data, c: Cmp, x: Ent(V), r: Es(V), n: Ent(V), rec: Es(V)) -> Es(V):
  M.ITreeModel.insert.go(U32, V, c, x, r, n, rec)

def ins.a.go(c: Cmp, -V: Data, +x: Ent(V), +r: Es(V), +e: Ent(V), +ys: Es(V), +s: U32, +l: U32, +v: V, ih: {mins(V, app(V, r, Con{e, ys}), s, l, v) == app(V, mins(V, r, s, l, v), Con{e, ys}) : Es(V)}) -> {igo(V, c, x, app(V, r, Con{e, ys}), T.ITreeEntry{s, l, v}, mins(V, app(V, r, Con{e, ys}), s, l, v)) == app(V, igo(V, c, x, r, T.ITreeEntry{s, l, v}, mins(V, r, s, l, v)), Con{e, ys}) : Es(V)}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      %ih : {Con{x, mins(V, app(V, r, Con{e, ys}), s, l, v)} == Con{x, _} : Es(V)}
      {==}

# inserting a key below e into xs ++ e :: ys inserts it into xs
def ins.a(-V: Data, xs: Es(V), +e: Ent(V), +ys: Es(V), +s: U32, +l: U32, +v: V, +h: {ec(V, s, l, e) == LT{} : Cmp}) -> {mins(V, app(V, xs, Con{e, ys}), s, l, v) == app(V, mins(V, xs, s, l, v), Con{e, ys}) : Es(V)}:
  match xs:
    case Nil{}:
      %Equal.sym(Cmp, ec(V, s, l, e), LT{}, h) : {igo(V, _, e, ys, T.ITreeEntry{s, l, v}, mins(V, ys, s, l, v)) == app(V, mins(V, Nil{}, s, l, v), Con{e, ys}) : Es(V)}
      {==}
    case Con{+x, +r}:
      ins.a.go(ec(V, s, l, x), V, x, r, e, ys, s, l, v, ins.a(V, r, e, ys, s, l, v, h))

# inserting a key above every entry of xs into xs ++ ys inserts it into ys
def ins.b(-V: Data, xs: Es(V), +ys: Es(V), +s: U32, +l: U32, +v: V, h: {bef(V, xs, s, l) == True{} : Bool}) -> {mins(V, app(V, xs, ys), s, l, v) == app(V, xs, mins(V, ys, s, l, v)) : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h = h
      %Equal.sym(Cmp, ec(V, s, l, x), GT{}, cmp.gt_of(ec(V, s, l, x), bool.and_l(Cmp.is_gt(ec(V, s, l, x)), bef(V, r, s, l), h))) : {igo(V, _, x, app(V, r, ys), T.ITreeEntry{s, l, v}, mins(V, app(V, r, ys), s, l, v)) == app(V, Con{x, r}, mins(V, ys, s, l, v)) : Es(V)}
      %ins.b(V, r, ys, s, l, v, bool.and_r(Cmp.is_gt(ec(V, s, l, x)), bef(V, r, s, l), h)) : {Con{x, mins(V, app(V, r, ys), s, l, v)} == Con{x, _} : Es(V)}
      {==}

def tins(-V: Data, +t: Tr(V), +s: U32, +l: U32, +v: V) -> Tr(V):
  T.ITree.ins(~U32, ~U32.cmp, V, t, T.ITree.probe(~U32, ~U32.cmp, V, t, s, l), s, l, v)

def ins.list.node(c: Cmp, -V: Data, +h: Nat, +m: U32, +tl: Tr(V), +e: Ent(V), +tr: Tr(V), +s: U32, +l: U32, +v: V, +ee: {ec(V, s, l, e) == c : Cmp}, +hs: {srt(V, app(V, L(V, tl), Con{e, L(V, tr)})) == True{} : Bool}, ihl: {L(V, tins(V, tl, s, l, v)) == mins(V, L(V, tl), s, l, v) : Es(V)}, ihr: {L(V, tins(V, tr, s, l, v)) == mins(V, L(V, tr), s, l, v) : Es(V)}) -> {L(V, T.ITree.ins(~U32, ~U32.cmp, V, T.ITreeNode{h, m, tl, e, tr}, c, s, l, v)) == mins(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l, v) : Es(V)}:
  match c:
    case LT{}:
      %Equal.sym(Es(V), L(V, T.ITree.bal(~U32, ~U32.cmp, V, tins(V, tl, s, l, v), e, tr)), app(V, L(V, tins(V, tl, s, l, v)), Con{e, L(V, tr)}), bal.list(V, tins(V, tl, s, l, v), e, tr)) : {_ == mins(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l, v) : Es(V)}
      %Equal.sym(Es(V), L(V, tins(V, tl, s, l, v)), mins(V, L(V, tl), s, l, v), ihl) : {app(V, _, Con{e, L(V, tr)}) == mins(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l, v) : Es(V)}
      Equal.sym(Es(V), mins(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l, v), app(V, mins(V, L(V, tl), s, l, v), Con{e, L(V, tr)}), ins.a(V, L(V, tl), e, L(V, tr), s, l, v, ee))
    case EQ{}:
      %Equal.sym(Es(V), mins(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l, v), app(V, L(V, tl), mins(V, Con{e, L(V, tr)}, s, l, v)), ins.b(V, L(V, tl), Con{e, L(V, tr)}, s, l, v, bef.eqk(V, L(V, tl), s, l, st(V, e), la(V, e), srt.bef(V, L(V, tl), e, L(V, tr), hs), ee))) : {app(V, L(V, tl), Con{T.ITreeEntry{s, l, v}, L(V, tr)}) == _ : Es(V)}
      %Equal.sym(Cmp, ec(V, s, l, e), EQ{}, ee) : {app(V, L(V, tl), Con{T.ITreeEntry{s, l, v}, L(V, tr)}) == app(V, L(V, tl), igo(V, _, e, L(V, tr), T.ITreeEntry{s, l, v}, mins(V, L(V, tr), s, l, v))) : Es(V)}
      {==}
    case GT{}:
      %Equal.sym(Es(V), L(V, T.ITree.bal(~U32, ~U32.cmp, V, tl, e, tins(V, tr, s, l, v))), app(V, L(V, tl), Con{e, L(V, tins(V, tr, s, l, v))}), bal.list(V, tl, e, tins(V, tr, s, l, v))) : {_ == mins(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l, v) : Es(V)}
      %Equal.sym(Es(V), L(V, tins(V, tr, s, l, v)), mins(V, L(V, tr), s, l, v), ihr) : {app(V, L(V, tl), Con{e, _}) == mins(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l, v) : Es(V)}
      %Equal.sym(Es(V), mins(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l, v), app(V, L(V, tl), mins(V, Con{e, L(V, tr)}, s, l, v)), ins.b(V, L(V, tl), Con{e, L(V, tr)}, s, l, v, bef.weaken(V, L(V, tl), s, l, st(V, e), la(V, e), srt.bef(V, L(V, tl), e, L(V, tr), hs), ee))) : {app(V, L(V, tl), Con{e, mins(V, L(V, tr), s, l, v)}) == _ : Es(V)}
      %Equal.sym(Cmp, ec(V, s, l, e), GT{}, ee) : {app(V, L(V, tl), Con{e, mins(V, L(V, tr), s, l, v)}) == app(V, L(V, tl), igo(V, _, e, L(V, tr), T.ITreeEntry{s, l, v}, mins(V, L(V, tr), s, l, v))) : Es(V)}
      {==}

def ins.list(-V: Data, t: Tr(V), +s: U32, +l: U32, +v: V, hs: {srt(V, L(V, t)) == True{} : Bool}) -> {L(V, tins(V, t, s, l, v)) == mins(V, L(V, t), s, l, v) : Es(V)}:
  match t:
    case T.ITreeLeaf{}:
      {==}
    case T.ITreeNode{+h, +m, +tl, +e, +tr}:
      +hs = hs
      ins.list.node(ec(V, s, l, e), V, h, m, tl, e, tr, s, l, v, {==}, hs, ins.list(V, tl, s, l, v, srt.left(V, L(V, tl), Con{e, L(V, tr)}, hs)), ins.list(V, tr, s, l, v, srt.tail(V, e, L(V, tr), srt.right(V, L(V, tl), Con{e, L(V, tr)}, hs))))

# Removal

def mrem.app(-V: Data, xs: Es(V), +ys: Es(V), +s: U32, +l: U32) -> {mrem(V, app(V, xs, ys), s, l) == app(V, mrem(V, xs, s, l), mrem(V, ys, s, l)) : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(Es(V), mrem(V, app(V, r, ys), s, l), app(V, mrem(V, r, s, l), mrem(V, ys, s, l)), mrem.app(V, r, ys, s, l)) : {keep(V, Bool.not(Cmp.is_eq(ec(V, s, l, x))), x, _) == app(V, keep(V, Bool.not(Cmp.is_eq(ec(V, s, l, x))), x, mrem(V, r, s, l)), mrem(V, ys, s, l)) : Es(V)}
      keep.app(V, Bool.not(Cmp.is_eq(ec(V, s, l, x))), x, mrem(V, r, s, l), mrem(V, ys, s, l))

def rem.aft(-V: Data, xs: Es(V), +s: U32, +l: U32, h: {aft(V, s, l, xs) == True{} : Bool}) -> {mrem(V, xs, s, l) == xs : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h = h
      %Equal.sym(Cmp, ec(V, s, l, x), LT{}, cmp.lt_of(ec(V, s, l, x), bool.and_l(Cmp.is_lt(ec(V, s, l, x)), aft(V, s, l, r), h))) : {keep(V, Bool.not(Cmp.is_eq(_)), x, mrem(V, r, s, l)) == Con{x, r} : Es(V)}
      %rem.aft(V, r, s, l, bool.and_r(Cmp.is_lt(ec(V, s, l, x)), aft(V, s, l, r), h)) : {Con{x, mrem(V, r, s, l)} == Con{x, _} : Es(V)}
      {==}

def rem.bef(-V: Data, xs: Es(V), +s: U32, +l: U32, h: {bef(V, xs, s, l) == True{} : Bool}) -> {mrem(V, xs, s, l) == xs : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h = h
      %Equal.sym(Cmp, ec(V, s, l, x), GT{}, cmp.gt_of(ec(V, s, l, x), bool.and_l(Cmp.is_gt(ec(V, s, l, x)), bef(V, r, s, l), h))) : {keep(V, Bool.not(Cmp.is_eq(_)), x, mrem(V, r, s, l)) == Con{x, r} : Es(V)}
      %rem.bef(V, r, s, l, bool.and_r(Cmp.is_gt(ec(V, s, l, x)), bef(V, r, s, l), h)) : {Con{x, mrem(V, r, s, l)} == Con{x, _} : Es(V)}
      {==}

def trem(-V: Data, +t: Tr(V), +s: U32, +l: U32) -> Tr(V):
  T.ITree.rem(~U32, ~U32.cmp, V, t, T.ITree.probe(~U32, ~U32.cmp, V, t, s, l), s, l)

def rem.list.node(c: Cmp, -V: Data, +h: Nat, +m: U32, +tl: Tr(V), +e: Ent(V), +tr: Tr(V), +s: U32, +l: U32, +ee: {ec(V, s, l, e) == c : Cmp}, +ha: {aft(V, st(V, e), la(V, e), L(V, tr)) == True{} : Bool}, +hb: {bef(V, L(V, tl), st(V, e), la(V, e)) == True{} : Bool}, ihl: {L(V, trem(V, tl, s, l)) == mrem(V, L(V, tl), s, l) : Es(V)}, ihr: {L(V, trem(V, tr, s, l)) == mrem(V, L(V, tr), s, l) : Es(V)}) -> {L(V, T.ITree.rem(~U32, ~U32.cmp, V, T.ITreeNode{h, m, tl, e, tr}, c, s, l)) == mrem(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l) : Es(V)}:
  match c:
    case LT{}:
      %Equal.sym(Es(V), L(V, T.ITree.bal(~U32, ~U32.cmp, V, trem(V, tl, s, l), e, tr)), app(V, L(V, trem(V, tl, s, l)), Con{e, L(V, tr)}), bal.list(V, trem(V, tl, s, l), e, tr)) : {_ == mrem(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l) : Es(V)}
      %Equal.sym(Es(V), L(V, trem(V, tl, s, l)), mrem(V, L(V, tl), s, l), ihl) : {app(V, _, Con{e, L(V, tr)}) == mrem(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l) : Es(V)}
      %Equal.sym(Es(V), mrem(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l), app(V, mrem(V, L(V, tl), s, l), mrem(V, Con{e, L(V, tr)}, s, l)), mrem.app(V, L(V, tl), Con{e, L(V, tr)}, s, l)) : {app(V, mrem(V, L(V, tl), s, l), Con{e, L(V, tr)}) == _ : Es(V)}
      %Equal.sym(Cmp, ec(V, s, l, e), LT{}, ee) : {app(V, mrem(V, L(V, tl), s, l), Con{e, L(V, tr)}) == app(V, mrem(V, L(V, tl), s, l), keep(V, Bool.not(Cmp.is_eq(_)), e, mrem(V, L(V, tr), s, l))) : Es(V)}
      %Equal.sym(Es(V), mrem(V, L(V, tr), s, l), L(V, tr), rem.aft(V, L(V, tr), s, l, aft.weaken(V, s, l, st(V, e), la(V, e), L(V, tr), ha, ee))) : {app(V, mrem(V, L(V, tl), s, l), Con{e, L(V, tr)}) == app(V, mrem(V, L(V, tl), s, l), Con{e, _}) : Es(V)}
      {==}
    case EQ{}:
      %Equal.sym(Es(V), L(V, T.ITree.merge(~U32, ~U32.cmp, V, tl, tr)), app(V, L(V, tl), L(V, tr)), merge.list(V, tl, tr)) : {_ == mrem(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l) : Es(V)}
      %Equal.sym(Es(V), mrem(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l), app(V, mrem(V, L(V, tl), s, l), mrem(V, Con{e, L(V, tr)}, s, l)), mrem.app(V, L(V, tl), Con{e, L(V, tr)}, s, l)) : {app(V, L(V, tl), L(V, tr)) == _ : Es(V)}
      %Equal.sym(Cmp, ec(V, s, l, e), EQ{}, ee) : {app(V, L(V, tl), L(V, tr)) == app(V, mrem(V, L(V, tl), s, l), keep(V, Bool.not(Cmp.is_eq(_)), e, mrem(V, L(V, tr), s, l))) : Es(V)}
      %Equal.sym(Es(V), mrem(V, L(V, tr), s, l), L(V, tr), rem.aft(V, L(V, tr), s, l, aft.eqk(V, s, l, st(V, e), la(V, e), L(V, tr), ha, ee))) : {app(V, L(V, tl), L(V, tr)) == app(V, mrem(V, L(V, tl), s, l), _) : Es(V)}
      %Equal.sym(Es(V), mrem(V, L(V, tl), s, l), L(V, tl), rem.bef(V, L(V, tl), s, l, bef.eqk(V, L(V, tl), s, l, st(V, e), la(V, e), hb, ee))) : {app(V, L(V, tl), L(V, tr)) == app(V, _, L(V, tr)) : Es(V)}
      {==}
    case GT{}:
      %Equal.sym(Es(V), L(V, T.ITree.bal(~U32, ~U32.cmp, V, tl, e, trem(V, tr, s, l))), app(V, L(V, tl), Con{e, L(V, trem(V, tr, s, l))}), bal.list(V, tl, e, trem(V, tr, s, l))) : {_ == mrem(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l) : Es(V)}
      %Equal.sym(Es(V), L(V, trem(V, tr, s, l)), mrem(V, L(V, tr), s, l), ihr) : {app(V, L(V, tl), Con{e, _}) == mrem(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l) : Es(V)}
      %Equal.sym(Es(V), mrem(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l), app(V, mrem(V, L(V, tl), s, l), mrem(V, Con{e, L(V, tr)}, s, l)), mrem.app(V, L(V, tl), Con{e, L(V, tr)}, s, l)) : {app(V, L(V, tl), Con{e, mrem(V, L(V, tr), s, l)}) == _ : Es(V)}
      %Equal.sym(Cmp, ec(V, s, l, e), GT{}, ee) : {app(V, L(V, tl), Con{e, mrem(V, L(V, tr), s, l)}) == app(V, mrem(V, L(V, tl), s, l), keep(V, Bool.not(Cmp.is_eq(_)), e, mrem(V, L(V, tr), s, l))) : Es(V)}
      %Equal.sym(Es(V), mrem(V, L(V, tl), s, l), L(V, tl), rem.bef(V, L(V, tl), s, l, bef.weaken(V, L(V, tl), s, l, st(V, e), la(V, e), hb, ee))) : {app(V, L(V, tl), Con{e, mrem(V, L(V, tr), s, l)}) == app(V, _, Con{e, mrem(V, L(V, tr), s, l)}) : Es(V)}
      {==}

def rem.list(-V: Data, t: Tr(V), +s: U32, +l: U32, hs: {srt(V, L(V, t)) == True{} : Bool}) -> {L(V, trem(V, t, s, l)) == mrem(V, L(V, t), s, l) : Es(V)}:
  match t:
    case T.ITreeLeaf{}:
      {==}
    case T.ITreeNode{+h, +m, +tl, +e, +tr}:
      +hs = hs
      rem.list.node(ec(V, s, l, e), V, h, m, tl, e, tr, s, l, {==}, srt.head(V, e, L(V, tr), srt.right(V, L(V, tl), Con{e, L(V, tr)}, hs)), srt.bef(V, L(V, tl), e, L(V, tr), hs), rem.list(V, tl, s, l, srt.left(V, L(V, tl), Con{e, L(V, tr)}, hs)), rem.list(V, tr, s, l, srt.tail(V, e, L(V, tr), srt.right(V, L(V, tl), Con{e, L(V, tr)}, hs))))

# Lookup

def lgo(-V: Data, b: Bool, x: Ent(V), rest: Maybe<&2, V>) -> Maybe<&2, V>:
  M.ITreeModel.lookup.go(U32, V, b, x, rest)

def lgo.orv(b: Bool, -V: Data, +x: Ent(V), p: Maybe<&2, V>, +q: Maybe<&2, V>) -> {lgo(V, b, x, orv(V, p, q)) == orv(V, lgo(V, b, x, p), q) : Maybe<&2, V>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def orv.none(-V: Data, m: Maybe<&2, V>) -> {orv(V, m, None{}) == m : Maybe<&2, V>}:
  match m:
    case Some{x}:
      {==}
    case None{}:
      {==}

def mlook.app(-V: Data, xs: Es(V), +ys: Es(V), +s: U32, +l: U32) -> {mlook(V, app(V, xs, ys), s, l) == orv(V, mlook(V, xs, s, l), mlook(V, ys, s, l)) : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(Maybe<&2, V>, mlook(V, app(V, r, ys), s, l), orv(V, mlook(V, r, s, l), mlook(V, ys, s, l)), mlook.app(V, r, ys, s, l)) : {lgo(V, Cmp.is_eq(ec(V, s, l, x)), x, _) == orv(V, lgo(V, Cmp.is_eq(ec(V, s, l, x)), x, mlook(V, r, s, l)), mlook(V, ys, s, l)) : Maybe<&2, V>}
      lgo.orv(Cmp.is_eq(ec(V, s, l, x)), V, x, mlook(V, r, s, l), mlook(V, ys, s, l))

def look.aft(-V: Data, xs: Es(V), +s: U32, +l: U32, h: {aft(V, s, l, xs) == True{} : Bool}) -> {mlook(V, xs, s, l) == None{} : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h = h
      %Equal.sym(Cmp, ec(V, s, l, x), LT{}, cmp.lt_of(ec(V, s, l, x), bool.and_l(Cmp.is_lt(ec(V, s, l, x)), aft(V, s, l, r), h))) : {lgo(V, Cmp.is_eq(_), x, mlook(V, r, s, l)) == None{} : Maybe<&2, V>}
      look.aft(V, r, s, l, bool.and_r(Cmp.is_lt(ec(V, s, l, x)), aft(V, s, l, r), h))

def look.bef(-V: Data, xs: Es(V), +s: U32, +l: U32, h: {bef(V, xs, s, l) == True{} : Bool}) -> {mlook(V, xs, s, l) == None{} : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h = h
      %Equal.sym(Cmp, ec(V, s, l, x), GT{}, cmp.gt_of(ec(V, s, l, x), bool.and_l(Cmp.is_gt(ec(V, s, l, x)), bef(V, r, s, l), h))) : {lgo(V, Cmp.is_eq(_), x, mlook(V, r, s, l)) == None{} : Maybe<&2, V>}
      look.bef(V, r, s, l, bool.and_r(Cmp.is_gt(ec(V, s, l, x)), bef(V, r, s, l), h))

def tfind(-V: Data, +t: Tr(V), +s: U32, +l: U32) -> Maybe<&2, V>:
  T.ITree.find(~U32, ~U32.cmp, V, t, T.ITree.probe(~U32, ~U32.cmp, V, t, s, l), s, l)

def find.list.node(c: Cmp, -V: Data, +h: Nat, +m: U32, +tl: Tr(V), +e: Ent(V), +tr: Tr(V), +s: U32, +l: U32, +ee: {ec(V, s, l, e) == c : Cmp}, +ha: {aft(V, st(V, e), la(V, e), L(V, tr)) == True{} : Bool}, +hb: {bef(V, L(V, tl), st(V, e), la(V, e)) == True{} : Bool}, ihl: {tfind(V, tl, s, l) == mlook(V, L(V, tl), s, l) : Maybe<&2, V>}, ihr: {tfind(V, tr, s, l) == mlook(V, L(V, tr), s, l) : Maybe<&2, V>}) -> {T.ITree.find(~U32, ~U32.cmp, V, T.ITreeNode{h, m, tl, e, tr}, c, s, l) == mlook(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l) : Maybe<&2, V>}:
  match c:
    case LT{}:
      %Equal.sym(Maybe<&2, V>, tfind(V, tl, s, l), mlook(V, L(V, tl), s, l), ihl) : {_ == mlook(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l) : Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, mlook(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l), orv(V, mlook(V, L(V, tl), s, l), mlook(V, Con{e, L(V, tr)}, s, l)), mlook.app(V, L(V, tl), Con{e, L(V, tr)}, s, l)) : {mlook(V, L(V, tl), s, l) == _ : Maybe<&2, V>}
      %Equal.sym(Cmp, ec(V, s, l, e), LT{}, ee) : {mlook(V, L(V, tl), s, l) == orv(V, mlook(V, L(V, tl), s, l), lgo(V, Cmp.is_eq(_), e, mlook(V, L(V, tr), s, l))) : Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, mlook(V, L(V, tr), s, l), None{}, look.aft(V, L(V, tr), s, l, aft.weaken(V, s, l, st(V, e), la(V, e), L(V, tr), ha, ee))) : {mlook(V, L(V, tl), s, l) == orv(V, mlook(V, L(V, tl), s, l), _) : Maybe<&2, V>}
      Equal.sym(Maybe<&2, V>, orv(V, mlook(V, L(V, tl), s, l), None{}), mlook(V, L(V, tl), s, l), orv.none(V, mlook(V, L(V, tl), s, l)))
    case EQ{}:
      %Equal.sym(Maybe<&2, V>, mlook(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l), orv(V, mlook(V, L(V, tl), s, l), mlook(V, Con{e, L(V, tr)}, s, l)), mlook.app(V, L(V, tl), Con{e, L(V, tr)}, s, l)) : {Some{T.ITreeEntry.value(U32, V, e)} == _ : Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, mlook(V, L(V, tl), s, l), None{}, look.bef(V, L(V, tl), s, l, bef.eqk(V, L(V, tl), s, l, st(V, e), la(V, e), hb, ee))) : {Some{T.ITreeEntry.value(U32, V, e)} == orv(V, _, mlook(V, Con{e, L(V, tr)}, s, l)) : Maybe<&2, V>}
      %Equal.sym(Cmp, ec(V, s, l, e), EQ{}, ee) : {Some{T.ITreeEntry.value(U32, V, e)} == lgo(V, Cmp.is_eq(_), e, mlook(V, L(V, tr), s, l)) : Maybe<&2, V>}
      {==}
    case GT{}:
      %Equal.sym(Maybe<&2, V>, tfind(V, tr, s, l), mlook(V, L(V, tr), s, l), ihr) : {_ == mlook(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l) : Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, mlook(V, app(V, L(V, tl), Con{e, L(V, tr)}), s, l), orv(V, mlook(V, L(V, tl), s, l), mlook(V, Con{e, L(V, tr)}, s, l)), mlook.app(V, L(V, tl), Con{e, L(V, tr)}, s, l)) : {mlook(V, L(V, tr), s, l) == _ : Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, mlook(V, L(V, tl), s, l), None{}, look.bef(V, L(V, tl), s, l, bef.weaken(V, L(V, tl), s, l, st(V, e), la(V, e), hb, ee))) : {mlook(V, L(V, tr), s, l) == orv(V, _, mlook(V, Con{e, L(V, tr)}, s, l)) : Maybe<&2, V>}
      %Equal.sym(Cmp, ec(V, s, l, e), GT{}, ee) : {mlook(V, L(V, tr), s, l) == lgo(V, Cmp.is_eq(_), e, mlook(V, L(V, tr), s, l)) : Maybe<&2, V>}
      {==}

def find.list(-V: Data, t: Tr(V), +s: U32, +l: U32, hs: {srt(V, L(V, t)) == True{} : Bool}) -> {tfind(V, t, s, l) == mlook(V, L(V, t), s, l) : Maybe<&2, V>}:
  match t:
    case T.ITreeLeaf{}:
      {==}
    case T.ITreeNode{+h, +m, +tl, +e, +tr}:
      +hs = hs
      find.list.node(ec(V, s, l, e), V, h, m, tl, e, tr, s, l, {==}, srt.head(V, e, L(V, tr), srt.right(V, L(V, tl), Con{e, L(V, tr)}, hs)), srt.bef(V, L(V, tl), e, L(V, tr), hs), find.list(V, tl, s, l, srt.left(V, L(V, tl), Con{e, L(V, tr)}, hs)), find.list(V, tr, s, l, srt.tail(V, e, L(V, tr), srt.right(V, L(V, tl), Con{e, L(V, tr)}, hs))))

# The augmented maximum: pruning by the largest last

def kmax(+a: U32, +b: U32) -> U32:
  T.ITree.kmax(~U32, ~U32.cmp, a, b)

def bnd(-V: Data, t: Tr(V), +x: U32) -> U32:
  T.ITree.bound(~U32, ~U32.cmp, V, t, x)

def mok(-V: Data, t: Tr(V)) -> Bool:
  T.ITree.max_ok(~U32, ~U32.cmp, V, t)

def reaches(-V: Data, t: Tr(V), +a: U32) -> Bool:
  T.ITree.reaches(~U32, ~U32.cmp, V, t, a)

def eov(-V: Data, +e: Ent(V), +a: U32, +b: U32) -> Bool:
  T.ITree.entry_overlaps(~U32, ~U32.cmp, V, e, a, b)

def kmax.ge_l.go(c: Cmp, +a: U32, +b: U32, e: {U32.cmp(a, b) == c : Cmp}) -> {Cmp.is_le(U32.cmp(a, T.ITree.kmax.pick(U32, c, a, b))) == True{} : Bool}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, U32.cmp(a, b), LT{}, e) : {Cmp.is_le(_) == True{} : Bool}
      {==}
    case EQ{}:
      %Equal.sym(Cmp, U32.cmp(a, a), EQ{}, UO.u32_cmp_refl(a)) : {Cmp.is_le(_) == True{} : Bool}
      {==}
    case GT{}:
      %Equal.sym(Cmp, U32.cmp(a, a), EQ{}, UO.u32_cmp_refl(a)) : {Cmp.is_le(_) == True{} : Bool}
      {==}

def kmax.ge_l(+a: U32, +b: U32) -> {Cmp.is_le(U32.cmp(a, kmax(a, b))) == True{} : Bool}:
  kmax.ge_l.go(U32.cmp(a, b), a, b, {==})

def kmax.ge_r.go(c: Cmp, +a: U32, +b: U32, e: {U32.cmp(a, b) == c : Cmp}) -> {Cmp.is_le(U32.cmp(b, T.ITree.kmax.pick(U32, c, a, b))) == True{} : Bool}:
  match c:
    case LT{}:
      %Equal.sym(Cmp, U32.cmp(b, b), EQ{}, UO.u32_cmp_refl(b)) : {Cmp.is_le(_) == True{} : Bool}
      {==}
    case EQ{}:
      %Equal.sym(Cmp, U32.cmp(b, a), EQ{}, u32.flip_of(a, b, EQ{}, e)) : {Cmp.is_le(_) == True{} : Bool}
      {==}
    case GT{}:
      %Equal.sym(Cmp, U32.cmp(b, a), LT{}, u32.flip_of(a, b, GT{}, e)) : {Cmp.is_le(_) == True{} : Bool}
      {==}

def kmax.ge_r(+a: U32, +b: U32) -> {Cmp.is_le(U32.cmp(b, kmax(a, b))) == True{} : Bool}:
  kmax.ge_r.go(U32.cmp(a, b), a, b, {==})

def bnd.ge(-V: Data, t: Tr(V), +x: U32) -> {Cmp.is_le(U32.cmp(x, bnd(V, t, x))) == True{} : Bool}:
  match t:
    case T.ITreeLeaf{}:
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, UO.u32_cmp_refl(x)) : {Cmp.is_le(_) == True{} : Bool}
      {==}
    case T.ITreeNode{h, +m, l, e, r}:
      kmax.ge_r(m, x)

def bnd.below(-V: Data, +t: Tr(V), +x: U32, +a: U32, h: {U32.cmp(bnd(V, t, x), a) == LT{} : Cmp}) -> {U32.cmp(x, a) == LT{} : Cmp}:
  u32.le_lt(x, bnd(V, t, x), a, bnd.ge(V, t, x), h)

def reaches.below(-V: Data, t: Tr(V), +x: U32, +a: U32, h: {U32.cmp(bnd(V, t, x), a) == LT{} : Cmp}) -> {reaches(V, t, a) == False{} : Bool}:
  match t:
    case T.ITreeLeaf{}:
      {==}
    case T.ITreeNode{hh, +m, l, e, r}:
      %Equal.sym(Cmp, U32.cmp(m, a), LT{}, u32.le_lt(m, kmax(m, x), a, kmax.ge_l(m, x), h)) : {Cmp.is_ge(_) == False{} : Bool}
      {==}

# every entry of xs ends before a
def lastlt(-V: Data, xs: Es(V), +a: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +r}:
      Bool.and(Cmp.is_lt(U32.cmp(la(V, x), a)), lastlt(V, r, a))

# every entry of xs starts after b
def stgt(-V: Data, xs: Es(V), +b: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, +r}:
      Bool.and(Cmp.is_gt(U32.cmp(st(V, x), b)), stgt(V, r, b))

def lastlt.app(-V: Data, xs: Es(V), +ys: Es(V), +a: U32) -> {lastlt(V, app(V, xs, ys), a) == Bool.and(lastlt(V, xs, a), lastlt(V, ys, a)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(Bool, lastlt(V, app(V, r, ys), a), Bool.and(lastlt(V, r, a), lastlt(V, ys, a)), lastlt.app(V, r, ys, a)) : {Bool.and(Cmp.is_lt(U32.cmp(la(V, x), a)), _) == Bool.and(Bool.and(Cmp.is_lt(U32.cmp(la(V, x), a)), lastlt(V, r, a)), lastlt(V, ys, a)) : Bool}
      Equal.sym(Bool, Bool.and(Bool.and(Cmp.is_lt(U32.cmp(la(V, x), a)), lastlt(V, r, a)), lastlt(V, ys, a)), Bool.and(Cmp.is_lt(U32.cmp(la(V, x), a)), Bool.and(lastlt(V, r, a), lastlt(V, ys, a))), bool.and_assoc(Cmp.is_lt(U32.cmp(la(V, x), a)), lastlt(V, r, a), lastlt(V, ys, a)))

# a subtree whose largest last is below a holds only entries ending before a
def maxlt(-V: Data, t: Tr(V), +a: U32, hm: {mok(V, t) == True{} : Bool}, h: {reaches(V, t, a) == False{} : Bool}) -> {lastlt(V, L(V, t), a) == True{} : Bool}:
  match t:
    case T.ITreeLeaf{}:
      {==}
    case T.ITreeNode{+hh, +m, +l, +e, +r}:
      +hm = hm
      +meq = UO.u32_cmp_eq(m, bnd(V, l, bnd(V, r, la(V, e))), cmp.eq_of(U32.cmp(m, bnd(V, l, bnd(V, r, la(V, e)))), bool.and_l(Cmp.is_eq(U32.cmp(m, bnd(V, l, bnd(V, r, la(V, e))))), Bool.and(mok(V, l), mok(V, r)), hm)))
      +hmr = bool.and_r(Cmp.is_eq(U32.cmp(m, bnd(V, l, bnd(V, r, la(V, e))))), Bool.and(mok(V, l), mok(V, r)), hm)
      +hlt = cmp.lt_of_not_ge(U32.cmp(m, a), h)
      +hM = Equal.trans(Cmp, U32.cmp(bnd(V, l, bnd(V, r, la(V, e))), a), U32.cmp(m, a), LT{}, Equal.cong(U32, Cmp, w => U32.cmp(w, a), bnd(V, l, bnd(V, r, la(V, e))), m, Equal.sym(U32, m, bnd(V, l, bnd(V, r, la(V, e))), meq)), hlt)
      +hR = bnd.below(V, l, bnd(V, r, la(V, e)), a, hM)
      %Equal.sym(Bool, lastlt(V, app(V, L(V, l), Con{e, L(V, r)}), a), Bool.and(lastlt(V, L(V, l), a), lastlt(V, Con{e, L(V, r)}, a)), lastlt.app(V, L(V, l), Con{e, L(V, r)}, a)) : {_ == True{} : Bool}
      bool.and_intro(lastlt(V, L(V, l), a), lastlt(V, Con{e, L(V, r)}, a), maxlt(V, l, a, bool.and_l(mok(V, l), mok(V, r), hmr), reaches.below(V, l, bnd(V, r, la(V, e)), a, hM)), bool.and_intro(Cmp.is_lt(U32.cmp(la(V, e), a)), lastlt(V, L(V, r), a), cmp.is_lt_of(U32.cmp(la(V, e), a), bnd.below(V, r, la(V, e), a, hR)), maxlt(V, r, a, bool.and_r(mok(V, l), mok(V, r), hmr), reaches.below(V, r, la(V, e), a, hR))))

# a key below every entry of xs, starting after b: every entry starts after b
def aft.stgt(-V: Data, +s: U32, +l: U32, xs: Es(V), +b: U32, h1: {aft(V, s, l, xs) == True{} : Bool}, +h2: {U32.cmp(s, b) == GT{} : Cmp}) -> {stgt(V, xs, b) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h1 = h1
      +kl = cmp.lt_of(ec(V, s, l, x), bool.and_l(Cmp.is_lt(ec(V, s, l, x)), aft(V, s, l, r), h1))
      +bs = u32.lt_le(b, s, st(V, x), u32.flip_of(s, b, GT{}, h2), kc.start_le(s, l, st(V, x), la(V, x), kl))
      bool.and_intro(Cmp.is_gt(U32.cmp(st(V, x), b)), stgt(V, r, b), cmp.is_gt_of(U32.cmp(st(V, x), b), u32.flip_of(b, st(V, x), LT{}, bs)), aft.stgt(V, s, l, r, b, bool.and_r(Cmp.is_lt(ec(V, s, l, x)), aft(V, s, l, r), h1), h2))

# Overlap queries

def mov(-V: Data, xs: Es(V), +a: U32, +b: U32) -> Es(V):
  M.ITreeModel.overlapping(~U32, ~U32.cmp, V, xs, a, b)

def tov(-V: Data, t: Tr(V), go: Bool, +a: U32, +b: U32) -> Es(V):
  T.ITree.ov(~U32, ~U32.cmp, V, t, go, a, b)

def mov.app(-V: Data, xs: Es(V), +ys: Es(V), +a: U32, +b: U32) -> {mov(V, app(V, xs, ys), a, b) == app(V, mov(V, xs, a, b), mov(V, ys, a, b)) : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(Es(V), mov(V, app(V, r, ys), a, b), app(V, mov(V, r, a, b), mov(V, ys, a, b)), mov.app(V, r, ys, a, b)) : {keep(V, eov(V, x, a, b), x, _) == app(V, keep(V, eov(V, x, a, b), x, mov(V, r, a, b)), mov(V, ys, a, b)) : Es(V)}
      keep.app(V, eov(V, x, a, b), x, mov(V, r, a, b), mov(V, ys, a, b))

def lastlt.ov(-V: Data, xs: Es(V), +a: U32, +b: U32, h: {lastlt(V, xs, a) == True{} : Bool}) -> {mov(V, xs, a, b) == Nil{} : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h = h
      %Equal.sym(Cmp, U32.cmp(a, la(V, x)), GT{}, u32.flip_of(la(V, x), a, LT{}, cmp.lt_of(U32.cmp(la(V, x), a), bool.and_l(Cmp.is_lt(U32.cmp(la(V, x), a)), lastlt(V, r, a), h)))) : {keep(V, Bool.and(Cmp.is_le(U32.cmp(st(V, x), b)), Cmp.is_le(_)), x, mov(V, r, a, b)) == Nil{} : Es(V)}
      %Equal.sym(Bool, Bool.and(Cmp.is_le(U32.cmp(st(V, x), b)), False{}), False{}, bool.and_false(Cmp.is_le(U32.cmp(st(V, x), b)))) : {keep(V, _, x, mov(V, r, a, b)) == Nil{} : Es(V)}
      lastlt.ov(V, r, a, b, bool.and_r(Cmp.is_lt(U32.cmp(la(V, x), a)), lastlt(V, r, a), h))

def stgt.ov(-V: Data, xs: Es(V), +a: U32, +b: U32, h: {stgt(V, xs, b) == True{} : Bool}) -> {mov(V, xs, a, b) == Nil{} : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h = h
      %Equal.sym(Cmp, U32.cmp(st(V, x), b), GT{}, cmp.gt_of(U32.cmp(st(V, x), b), bool.and_l(Cmp.is_gt(U32.cmp(st(V, x), b)), stgt(V, r, b), h))) : {keep(V, Bool.and(Cmp.is_le(_), Cmp.is_le(U32.cmp(a, la(V, x)))), x, mov(V, r, a, b)) == Nil{} : Es(V)}
      stgt.ov(V, r, a, b, bool.and_r(Cmp.is_gt(U32.cmp(st(V, x), b)), stgt(V, r, b), h))

def tov.false(-V: Data, t: Tr(V), +a: U32, +b: U32) -> {tov(V, t, False{}, a, b) == Nil{} : Es(V)}:
  match t:
    case T.ITreeLeaf{}:
      {==}
    case T.ITreeNode{h, m, l, e, r}:
      {==}

def ov.right(q: Bool, -V: Data, +tr: Tr(V), +e: Ent(V), +a: U32, +b: U32, eq: {Cmp.is_le(U32.cmp(st(V, e), b)) == q : Bool}, ha: {aft(V, st(V, e), la(V, e), L(V, tr)) == True{} : Bool}, ihr: {tov(V, tr, reaches(V, tr, a), a, b) == mov(V, L(V, tr), a, b) : Es(V)}) -> {tov(V, tr, Bool.and(q, reaches(V, tr, a)), a, b) == mov(V, L(V, tr), a, b) : Es(V)}:
  match q:
    case True{}:
      ihr
    case False{}:
      Equal.trans(Es(V), tov(V, tr, False{}, a, b), Nil{}, mov(V, L(V, tr), a, b), tov.false(V, tr, a, b), Equal.sym(Es(V), mov(V, L(V, tr), a, b), Nil{}, stgt.ov(V, L(V, tr), a, b, aft.stgt(V, st(V, e), la(V, e), L(V, tr), b, ha, cmp.gt_of_not_le(U32.cmp(st(V, e), b), eq)))))

def ov.list.node(g: Bool, -V: Data, +h: Nat, +m: U32, +tl: Tr(V), +e: Ent(V), +tr: Tr(V), +a: U32, +b: U32, eq: {Cmp.is_ge(U32.cmp(m, a)) == g : Bool}, +hm: {mok(V, T.ITreeNode{h, m, tl, e, tr}) == True{} : Bool}, +ha: {aft(V, st(V, e), la(V, e), L(V, tr)) == True{} : Bool}, ihl: {tov(V, tl, reaches(V, tl, a), a, b) == mov(V, L(V, tl), a, b) : Es(V)}, ihr: {tov(V, tr, reaches(V, tr, a), a, b) == mov(V, L(V, tr), a, b) : Es(V)}) -> {tov(V, T.ITreeNode{h, m, tl, e, tr}, g, a, b) == mov(V, app(V, L(V, tl), Con{e, L(V, tr)}), a, b) : Es(V)}:
  match g:
    case False{}:
      Equal.sym(Es(V), mov(V, app(V, L(V, tl), Con{e, L(V, tr)}), a, b), Nil{}, lastlt.ov(V, app(V, L(V, tl), Con{e, L(V, tr)}), a, b, maxlt(V, T.ITreeNode{h, m, tl, e, tr}, a, hm, eq)))
    case True{}:
      %Equal.sym(Es(V), tov(V, tl, reaches(V, tl, a), a, b), mov(V, L(V, tl), a, b), ihl) : {app(V, _, keep(V, eov(V, e, a, b), e, tov(V, tr, T.ITree.go_right(~U32, ~U32.cmp, V, e, tr, a, b), a, b))) == mov(V, app(V, L(V, tl), Con{e, L(V, tr)}), a, b) : Es(V)}
      %Equal.sym(Es(V), tov(V, tr, T.ITree.go_right(~U32, ~U32.cmp, V, e, tr, a, b), a, b), mov(V, L(V, tr), a, b), ov.right(Cmp.is_le(U32.cmp(st(V, e), b)), V, tr, e, a, b, {==}, ha, ihr)) : {app(V, mov(V, L(V, tl), a, b), keep(V, eov(V, e, a, b), e, _)) == mov(V, app(V, L(V, tl), Con{e, L(V, tr)}), a, b) : Es(V)}
      Equal.sym(Es(V), mov(V, app(V, L(V, tl), Con{e, L(V, tr)}), a, b), app(V, mov(V, L(V, tl), a, b), mov(V, Con{e, L(V, tr)}, a, b)), mov.app(V, L(V, tl), Con{e, L(V, tr)}, a, b))

def ov.list(-V: Data, t: Tr(V), +a: U32, +b: U32, hs: {srt(V, L(V, t)) == True{} : Bool}, hm: {mok(V, t) == True{} : Bool}) -> {tov(V, t, reaches(V, t, a), a, b) == mov(V, L(V, t), a, b) : Es(V)}:
  match t:
    case T.ITreeLeaf{}:
      {==}
    case T.ITreeNode{+h, +m, +tl, +e, +tr}:
      +hs = hs
      +hm = hm
      +hmr = bool.and_r(Cmp.is_eq(U32.cmp(m, bnd(V, tl, bnd(V, tr, la(V, e))))), Bool.and(mok(V, tl), mok(V, tr)), hm)
      ov.list.node(Cmp.is_ge(U32.cmp(m, a)), V, h, m, tl, e, tr, a, b, {==}, hm, srt.head(V, e, L(V, tr), srt.right(V, L(V, tl), Con{e, L(V, tr)}, hs)), ov.list(V, tl, a, b, srt.left(V, L(V, tl), Con{e, L(V, tr)}, hs), bool.and_l(mok(V, tl), mok(V, tr), hmr)), ov.list(V, tr, a, b, srt.tail(V, e, L(V, tr), srt.right(V, L(V, tl), Con{e, L(V, tr)}, hs)), bool.and_r(mok(V, tl), mok(V, tr), hmr)))

# The first overlapping entry after a bound

def oe(-V: Data, m: Maybe<&2, Ent(V)>, n: Maybe<&2, Ent(V)>) -> Maybe<&2, Ent(V)>:
  T.ITree.orelse(U32, V, m, n)

def pk(-V: Data, b: Bool, x: Ent(V)) -> Maybe<&2, Ent(V)>:
  T.ITree.pick(U32, V, b, x)

def aftr(-V: Data, lo: T.ITreeBound<U32>, +e: Ent(V)) -> Bool:
  T.ITree.after(~U32, ~U32.cmp, V, lo, e)

def mseek(-V: Data, xs: Es(V), +a: U32, +b: U32, +lo: T.ITreeBound<U32>) -> Maybe<&2, Ent(V)>:
  M.ITreeModel.seek(~U32, ~U32.cmp, V, xs, a, b, lo)

def tseek(-V: Data, t: Tr(V), go: Bool, +a: U32, +b: U32, +lo: T.ITreeBound<U32>, prev: Maybe<&2, Ent(V)>) -> Maybe<&2, Ent(V)>:
  T.ITree.seek(~U32, ~U32.cmp, V, t, go, a, b, lo, prev)

def oe.none(-V: Data, m: Maybe<&2, Ent(V)>) -> {oe(V, m, None{}) == m : Maybe<&2, Ent(V)>}:
  match m:
    case Some{x}:
      {==}
    case None{}:
      {==}

def oe.assoc(-V: Data, m: Maybe<&2, Ent(V)>, +n: Maybe<&2, Ent(V)>, +o: Maybe<&2, Ent(V)>) -> {oe(V, oe(V, m, n), o) == oe(V, m, oe(V, n, o)) : Maybe<&2, Ent(V)>}:
  match m:
    case Some{x}:
      {==}
    case None{}:
      {==}

def mseek.app(-V: Data, xs: Es(V), +ys: Es(V), +a: U32, +b: U32, +lo: T.ITreeBound<U32>) -> {mseek(V, app(V, xs, ys), a, b, lo) == oe(V, mseek(V, xs, a, b, lo), mseek(V, ys, a, b, lo)) : Maybe<&2, Ent(V)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(Maybe<&2, Ent(V)>, mseek(V, app(V, r, ys), a, b, lo), oe(V, mseek(V, r, a, b, lo), mseek(V, ys, a, b, lo)), mseek.app(V, r, ys, a, b, lo)) : {oe(V, pk(V, Bool.and(aftr(V, lo, x), eov(V, x, a, b)), x), _) == oe(V, oe(V, pk(V, Bool.and(aftr(V, lo, x), eov(V, x, a, b)), x), mseek(V, r, a, b, lo)), mseek(V, ys, a, b, lo)) : Maybe<&2, Ent(V)>}
      Equal.sym(Maybe<&2, Ent(V)>, oe(V, oe(V, pk(V, Bool.and(aftr(V, lo, x), eov(V, x, a, b)), x), mseek(V, r, a, b, lo)), mseek(V, ys, a, b, lo)), oe(V, pk(V, Bool.and(aftr(V, lo, x), eov(V, x, a, b)), x), oe(V, mseek(V, r, a, b, lo), mseek(V, ys, a, b, lo))), oe.assoc(V, pk(V, Bool.and(aftr(V, lo, x), eov(V, x, a, b)), x), mseek(V, r, a, b, lo), mseek(V, ys, a, b, lo)))

def lastlt.seek(-V: Data, xs: Es(V), +a: U32, +b: U32, +lo: T.ITreeBound<U32>, h: {lastlt(V, xs, a) == True{} : Bool}) -> {mseek(V, xs, a, b, lo) == None{} : Maybe<&2, Ent(V)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h = h
      %Equal.sym(Cmp, U32.cmp(a, la(V, x)), GT{}, u32.flip_of(la(V, x), a, LT{}, cmp.lt_of(U32.cmp(la(V, x), a), bool.and_l(Cmp.is_lt(U32.cmp(la(V, x), a)), lastlt(V, r, a), h)))) : {oe(V, pk(V, Bool.and(aftr(V, lo, x), Bool.and(Cmp.is_le(U32.cmp(st(V, x), b)), Cmp.is_le(_))), x), mseek(V, r, a, b, lo)) == None{} : Maybe<&2, Ent(V)>}
      %Equal.sym(Bool, Bool.and(Cmp.is_le(U32.cmp(st(V, x), b)), False{}), False{}, bool.and_false(Cmp.is_le(U32.cmp(st(V, x), b)))) : {oe(V, pk(V, Bool.and(aftr(V, lo, x), _), x), mseek(V, r, a, b, lo)) == None{} : Maybe<&2, Ent(V)>}
      %Equal.sym(Bool, Bool.and(aftr(V, lo, x), False{}), False{}, bool.and_false(aftr(V, lo, x))) : {oe(V, pk(V, _, x), mseek(V, r, a, b, lo)) == None{} : Maybe<&2, Ent(V)>}
      lastlt.seek(V, r, a, b, lo, bool.and_r(Cmp.is_lt(U32.cmp(la(V, x), a)), lastlt(V, r, a), h))

def stgt.seek(-V: Data, xs: Es(V), +a: U32, +b: U32, +lo: T.ITreeBound<U32>, h: {stgt(V, xs, b) == True{} : Bool}) -> {mseek(V, xs, a, b, lo) == None{} : Maybe<&2, Ent(V)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h = h
      %Equal.sym(Cmp, U32.cmp(st(V, x), b), GT{}, cmp.gt_of(U32.cmp(st(V, x), b), bool.and_l(Cmp.is_gt(U32.cmp(st(V, x), b)), stgt(V, r, b), h))) : {oe(V, pk(V, Bool.and(aftr(V, lo, x), Bool.and(Cmp.is_le(_), Cmp.is_le(U32.cmp(a, la(V, x))))), x), mseek(V, r, a, b, lo)) == None{} : Maybe<&2, Ent(V)>}
      %Equal.sym(Bool, Bool.and(aftr(V, lo, x), False{}), False{}, bool.and_false(aftr(V, lo, x))) : {oe(V, pk(V, _, x), mseek(V, r, a, b, lo)) == None{} : Maybe<&2, Ent(V)>}
      stgt.seek(V, r, a, b, lo, bool.and_r(Cmp.is_gt(U32.cmp(st(V, x), b)), stgt(V, r, b), h))

# entries before e, with e not after the bound: none is after the bound
def bef.seek.go(-V: Data, xs: Es(V), +s0: U32, +l0: U32, +e: Ent(V), +a: U32, +b: U32, hb: {bef(V, xs, st(V, e), la(V, e)) == True{} : Bool}, +ha: {Cmp.is_lt(ec(V, s0, l0, e)) == False{} : Bool}) -> {mseek(V, xs, a, b, T.ITreeAfter{s0, l0}) == None{} : Maybe<&2, Ent(V)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +hb = hb
      +kg = kc.ge_gt(s0, l0, st(V, e), la(V, e), st(V, x), la(V, x), ha, cmp.gt_of(ec(V, st(V, e), la(V, e), x), bool.and_l(Cmp.is_gt(ec(V, st(V, e), la(V, e), x)), bef(V, r, st(V, e), la(V, e)), hb)))
      %Equal.sym(Cmp, ec(V, s0, l0, x), GT{}, kg) : {oe(V, pk(V, Bool.and(Cmp.is_lt(_), eov(V, x, a, b)), x), mseek(V, r, a, b, T.ITreeAfter{s0, l0})) == None{} : Maybe<&2, Ent(V)>}
      bef.seek.go(V, r, s0, l0, e, a, b, bool.and_r(Cmp.is_gt(ec(V, st(V, e), la(V, e), x)), bef(V, r, st(V, e), la(V, e)), hb), ha)

def bef.seek(lo: T.ITreeBound<U32>, -V: Data, xs: Es(V), +e: Ent(V), +a: U32, +b: U32, hb: {bef(V, xs, st(V, e), la(V, e)) == True{} : Bool}, ha: {aftr(V, lo, e) == False{} : Bool}) -> {mseek(V, xs, a, b, lo) == None{} : Maybe<&2, Ent(V)>}:
  match lo:
    case T.ITreeFromStart{}:
      Empty.absurd({mseek(V, xs, a, b, T.ITreeFromStart{}) == None{} : Maybe<&2, Ent(V)>}, absurd.tf(ha))
    case T.ITreeAfter{+s0, +l0}:
      bef.seek.go(V, xs, s0, l0, e, a, b, hb, ha)

def tseek.false(-V: Data, t: Tr(V), +a: U32, +b: U32, +lo: T.ITreeBound<U32>, +p: Maybe<&2, Ent(V)>) -> {tseek(V, t, False{}, a, b, lo, p) == p : Maybe<&2, Ent(V)>}:
  match t:
    case T.ITreeLeaf{}:
      {==}
    case T.ITreeNode{h, m, l, e, r}:
      {==}

def seek.right(q: Bool, -V: Data, +tr: Tr(V), +e: Ent(V), +a: U32, +b: U32, +lo: T.ITreeBound<U32>, +p: Maybe<&2, Ent(V)>, eq: {Cmp.is_le(U32.cmp(st(V, e), b)) == q : Bool}, ha: {aft(V, st(V, e), la(V, e), L(V, tr)) == True{} : Bool}, ihr: {tseek(V, tr, reaches(V, tr, a), a, b, lo, p) == oe(V, p, mseek(V, L(V, tr), a, b, lo)) : Maybe<&2, Ent(V)>}) -> {tseek(V, tr, Bool.and(q, reaches(V, tr, a)), a, b, lo, p) == oe(V, p, mseek(V, L(V, tr), a, b, lo)) : Maybe<&2, Ent(V)>}:
  match q:
    case True{}:
      ihr
    case False{}:
      %Equal.sym(Maybe<&2, Ent(V)>, tseek(V, tr, False{}, a, b, lo, p), p, tseek.false(V, tr, a, b, lo, p)) : {_ == oe(V, p, mseek(V, L(V, tr), a, b, lo)) : Maybe<&2, Ent(V)>}
      %Equal.sym(Maybe<&2, Ent(V)>, mseek(V, L(V, tr), a, b, lo), None{}, stgt.seek(V, L(V, tr), a, b, lo, aft.stgt(V, st(V, e), la(V, e), L(V, tr), b, ha, cmp.gt_of_not_le(U32.cmp(st(V, e), b), eq)))) : {p == oe(V, p, _) : Maybe<&2, Ent(V)>}
      Equal.sym(Maybe<&2, Ent(V)>, oe(V, p, None{}), p, oe.none(V, p))

def seek.left(w: Bool, -V: Data, +tl: Tr(V), +e: Ent(V), +a: U32, +b: U32, +lo: T.ITreeBound<U32>, eq: {aftr(V, lo, e) == w : Bool}, hb: {bef(V, L(V, tl), st(V, e), la(V, e)) == True{} : Bool}, ihl: {tseek(V, tl, reaches(V, tl, a), a, b, lo, None{}) == mseek(V, L(V, tl), a, b, lo) : Maybe<&2, Ent(V)>}) -> {tseek(V, tl, Bool.and(w, reaches(V, tl, a)), a, b, lo, None{}) == mseek(V, L(V, tl), a, b, lo) : Maybe<&2, Ent(V)>}:
  match w:
    case True{}:
      ihl
    case False{}:
      Equal.trans(Maybe<&2, Ent(V)>, tseek(V, tl, False{}, a, b, lo, None{}), None{}, mseek(V, L(V, tl), a, b, lo), tseek.false(V, tl, a, b, lo, None{}), Equal.sym(Maybe<&2, Ent(V)>, mseek(V, L(V, tl), a, b, lo), None{}, bef.seek(lo, V, L(V, tl), e, a, b, hb, eq)))

def sl.prev(-V: Data, +tl: Tr(V), +e: Ent(V), +a: U32, +b: U32, +lo: T.ITreeBound<U32>) -> Maybe<&2, Ent(V)>:
  oe(V, tseek(V, tl, Bool.and(aftr(V, lo, e), reaches(V, tl, a)), a, b, lo, None{}), pk(V, Bool.and(aftr(V, lo, e), eov(V, e, a, b)), e))

def seek.list.node(g: Bool, -V: Data, +h: Nat, +m: U32, +tl: Tr(V), +e: Ent(V), +tr: Tr(V), +a: U32, +b: U32, +lo: T.ITreeBound<U32>, prev: Maybe<&2, Ent(V)>, eq: {Cmp.is_ge(U32.cmp(m, a)) == g : Bool}, +hm: {mok(V, T.ITreeNode{h, m, tl, e, tr}) == True{} : Bool}, +ha: {aft(V, st(V, e), la(V, e), L(V, tr)) == True{} : Bool}, +hb: {bef(V, L(V, tl), st(V, e), la(V, e)) == True{} : Bool}, ihl: {tseek(V, tl, reaches(V, tl, a), a, b, lo, None{}) == mseek(V, L(V, tl), a, b, lo) : Maybe<&2, Ent(V)>}, ihr: {tseek(V, tr, reaches(V, tr, a), a, b, lo, sl.prev(V, tl, e, a, b, lo)) == oe(V, sl.prev(V, tl, e, a, b, lo), mseek(V, L(V, tr), a, b, lo)) : Maybe<&2, Ent(V)>}) -> {tseek(V, T.ITreeNode{h, m, tl, e, tr}, g, a, b, lo, prev) == oe(V, prev, mseek(V, app(V, L(V, tl), Con{e, L(V, tr)}), a, b, lo)) : Maybe<&2, Ent(V)>}:
  match g:
    case False{}:
      %Equal.sym(Maybe<&2, Ent(V)>, mseek(V, app(V, L(V, tl), Con{e, L(V, tr)}), a, b, lo), None{}, lastlt.seek(V, app(V, L(V, tl), Con{e, L(V, tr)}), a, b, lo, maxlt(V, T.ITreeNode{h, m, tl, e, tr}, a, hm, eq))) : {prev == oe(V, prev, _) : Maybe<&2, Ent(V)>}
      Equal.sym(Maybe<&2, Ent(V)>, oe(V, prev, None{}), prev, oe.none(V, prev))
    case True{}:
      match prev:
        case Some{x}:
          {==}
        case None{}:
          %Equal.sym(Maybe<&2, Ent(V)>, tseek(V, tr, T.ITree.go_right(~U32, ~U32.cmp, V, e, tr, a, b), a, b, lo, sl.prev(V, tl, e, a, b, lo)), oe(V, sl.prev(V, tl, e, a, b, lo), mseek(V, L(V, tr), a, b, lo)), seek.right(Cmp.is_le(U32.cmp(st(V, e), b)), V, tr, e, a, b, lo, sl.prev(V, tl, e, a, b, lo), {==}, ha, ihr)) : {_ == mseek(V, app(V, L(V, tl), Con{e, L(V, tr)}), a, b, lo) : Maybe<&2, Ent(V)>}
          %Equal.sym(Maybe<&2, Ent(V)>, tseek(V, tl, Bool.and(aftr(V, lo, e), reaches(V, tl, a)), a, b, lo, None{}), mseek(V, L(V, tl), a, b, lo), seek.left(aftr(V, lo, e), V, tl, e, a, b, lo, {==}, hb, ihl)) : {oe(V, oe(V, _, pk(V, Bool.and(aftr(V, lo, e), eov(V, e, a, b)), e)), mseek(V, L(V, tr), a, b, lo)) == mseek(V, app(V, L(V, tl), Con{e, L(V, tr)}), a, b, lo) : Maybe<&2, Ent(V)>}
          %Equal.sym(Maybe<&2, Ent(V)>, mseek(V, app(V, L(V, tl), Con{e, L(V, tr)}), a, b, lo), oe(V, mseek(V, L(V, tl), a, b, lo), mseek(V, Con{e, L(V, tr)}, a, b, lo)), mseek.app(V, L(V, tl), Con{e, L(V, tr)}, a, b, lo)) : {oe(V, oe(V, mseek(V, L(V, tl), a, b, lo), pk(V, Bool.and(aftr(V, lo, e), eov(V, e, a, b)), e)), mseek(V, L(V, tr), a, b, lo)) == _ : Maybe<&2, Ent(V)>}
          oe.assoc(V, mseek(V, L(V, tl), a, b, lo), pk(V, Bool.and(aftr(V, lo, e), eov(V, e, a, b)), e), mseek(V, L(V, tr), a, b, lo))

def seek.list(-V: Data, t: Tr(V), +a: U32, +b: U32, +lo: T.ITreeBound<U32>, +prev: Maybe<&2, Ent(V)>, hs: {srt(V, L(V, t)) == True{} : Bool}, hm: {mok(V, t) == True{} : Bool}) -> {tseek(V, t, reaches(V, t, a), a, b, lo, prev) == oe(V, prev, mseek(V, L(V, t), a, b, lo)) : Maybe<&2, Ent(V)>}:
  match t:
    case T.ITreeLeaf{}:
      Equal.sym(Maybe<&2, Ent(V)>, oe(V, prev, None{}), prev, oe.none(V, prev))
    case T.ITreeNode{+h, +m, +tl, +e, +tr}:
      +hs = hs
      +hm = hm
      +hmr = bool.and_r(Cmp.is_eq(U32.cmp(m, bnd(V, tl, bnd(V, tr, la(V, e))))), Bool.and(mok(V, tl), mok(V, tr)), hm)
      seek.list.node(Cmp.is_ge(U32.cmp(m, a)), V, h, m, tl, e, tr, a, b, lo, prev, {==}, hm, srt.head(V, e, L(V, tr), srt.right(V, L(V, tl), Con{e, L(V, tr)}, hs)), srt.bef(V, L(V, tl), e, L(V, tr), hs), seek.list(V, tl, a, b, lo, None{}, srt.left(V, L(V, tl), Con{e, L(V, tr)}, hs), bool.and_l(mok(V, tl), mok(V, tr), hmr)), seek.list(V, tr, a, b, lo, sl.prev(V, tl, e, a, b, lo), srt.tail(V, e, L(V, tr), srt.right(V, L(V, tl), Con{e, L(V, tr)}, hs)), bool.and_r(mok(V, tl), mok(V, tr), hmr)))

# Every operation keeps the stored maxima right

def mk(-V: Data, +l: Tr(V), +e: Ent(V), +r: Tr(V)) -> Tr(V):
  T.ITree.mk(~U32, ~U32.cmp, V, l, e, r)

def mk.mok(-V: Data, +l: Tr(V), +e: Ent(V), +r: Tr(V), +hl: {mok(V, l) == True{} : Bool}, +hr: {mok(V, r) == True{} : Bool}) -> {mok(V, mk(V, l, e, r)) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(bnd(V, l, bnd(V, r, la(V, e))), bnd(V, l, bnd(V, r, la(V, e)))), EQ{}, UO.u32_cmp_refl(bnd(V, l, bnd(V, r, la(V, e))))) : {Bool.and(Cmp.is_eq(_), Bool.and(mok(V, l), mok(V, r))) == True{} : Bool}
  bool.and_intro(mok(V, l), mok(V, r), hl, hr)

def mok.l(-V: Data, +h: Nat, +m: U32, +l: Tr(V), +e: Ent(V), +r: Tr(V), +hm: {mok(V, T.ITreeNode{h, m, l, e, r}) == True{} : Bool}) -> {mok(V, l) == True{} : Bool}:
  bool.and_l(mok(V, l), mok(V, r), bool.and_r(Cmp.is_eq(U32.cmp(m, bnd(V, l, bnd(V, r, la(V, e))))), Bool.and(mok(V, l), mok(V, r)), hm))

def mok.r(-V: Data, +h: Nat, +m: U32, +l: Tr(V), +e: Ent(V), +r: Tr(V), +hm: {mok(V, T.ITreeNode{h, m, l, e, r}) == True{} : Bool}) -> {mok(V, r) == True{} : Bool}:
  bool.and_r(mok(V, l), mok(V, r), bool.and_r(Cmp.is_eq(U32.cmp(m, bnd(V, l, bnd(V, r, la(V, e))))), Bool.and(mok(V, l), mok(V, r)), hm))

def rot_r.go.mok(+dbl: Bool, -V: Data, +ll: Tr(V), +le: Ent(V), +lr: Tr(V), +e: Ent(V), +r: Tr(V), +hll: {mok(V, ll) == True{} : Bool}, +hlr: {mok(V, lr) == True{} : Bool}, +hr: {mok(V, r) == True{} : Bool}) -> {mok(V, T.ITree.rot_r.go(~U32, ~U32.cmp, V, dbl, ll, le, lr, e, r)) == True{} : Bool}:
  match dbl:
    case False{}:
      mk.mok(V, ll, le, mk(V, lr, e, r), hll, mk.mok(V, lr, e, r, hlr, hr))
    case True{}:
      match lr:
        case T.ITreeLeaf{}:
          mk.mok(V, ll, le, mk(V, T.ITreeLeaf{}, e, r), hll, mk.mok(V, T.ITreeLeaf{}, e, r, {==}, hr))
        case T.ITreeNode{+h2, +m2, +lrl, +lre, +lrr}:
          +hlr = hlr
          mk.mok(V, mk(V, ll, le, lrl), lre, mk(V, lrr, e, r), mk.mok(V, ll, le, lrl, hll, mok.l(V, h2, m2, lrl, lre, lrr, hlr)), mk.mok(V, lrr, e, r, mok.r(V, h2, m2, lrl, lre, lrr, hlr), hr))

def rot_r.mok(-V: Data, +l: Tr(V), +e: Ent(V), +r: Tr(V), +hl: {mok(V, l) == True{} : Bool}, +hr: {mok(V, r) == True{} : Bool}) -> {mok(V, T.ITree.rot_r(~U32, ~U32.cmp, V, l, e, r)) == True{} : Bool}:
  match l:
    case T.ITreeLeaf{}:
      mk.mok(V, T.ITreeLeaf{}, e, r, {==}, hr)
    case T.ITreeNode{+h, +m, +ll, +le, +lr}:
      +hl = hl
      rot_r.go.mok(Nat.is_lt(T.ITree.height(U32, V, ll), T.ITree.height(U32, V, lr)), V, ll, le, lr, e, r, mok.l(V, h, m, ll, le, lr, hl), mok.r(V, h, m, ll, le, lr, hl), hr)

def rot_l.go.mok(+dbl: Bool, -V: Data, +l: Tr(V), +e: Ent(V), +rl: Tr(V), +re: Ent(V), +rr: Tr(V), +hl: {mok(V, l) == True{} : Bool}, +hrl: {mok(V, rl) == True{} : Bool}, +hrr: {mok(V, rr) == True{} : Bool}) -> {mok(V, T.ITree.rot_l.go(~U32, ~U32.cmp, V, dbl, l, e, rl, re, rr)) == True{} : Bool}:
  match dbl:
    case False{}:
      mk.mok(V, mk(V, l, e, rl), re, rr, mk.mok(V, l, e, rl, hl, hrl), hrr)
    case True{}:
      match rl:
        case T.ITreeLeaf{}:
          mk.mok(V, mk(V, l, e, T.ITreeLeaf{}), re, rr, mk.mok(V, l, e, T.ITreeLeaf{}, hl, {==}), hrr)
        case T.ITreeNode{+h2, +m2, +rll, +rle, +rlr}:
          +hrl = hrl
          mk.mok(V, mk(V, l, e, rll), rle, mk(V, rlr, re, rr), mk.mok(V, l, e, rll, hl, mok.l(V, h2, m2, rll, rle, rlr, hrl)), mk.mok(V, rlr, re, rr, mok.r(V, h2, m2, rll, rle, rlr, hrl), hrr))

def rot_l.mok(-V: Data, +l: Tr(V), +e: Ent(V), +r: Tr(V), +hl: {mok(V, l) == True{} : Bool}, +hr: {mok(V, r) == True{} : Bool}) -> {mok(V, T.ITree.rot_l(~U32, ~U32.cmp, V, l, e, r)) == True{} : Bool}:
  match r:
    case T.ITreeLeaf{}:
      mk.mok(V, l, e, T.ITreeLeaf{}, hl, {==})
    case T.ITreeNode{+h, +m, +rl, +re, +rr}:
      +hr = hr
      rot_l.go.mok(Nat.is_lt(T.ITree.height(U32, V, rr), T.ITree.height(U32, V, rl)), V, l, e, rl, re, rr, hl, mok.l(V, h, m, rl, re, rr, hr), mok.r(V, h, m, rl, re, rr, hr))

def bal.go.mok(+lh: Bool, +rh: Bool, -V: Data, +l: Tr(V), +e: Ent(V), +r: Tr(V), +hl: {mok(V, l) == True{} : Bool}, +hr: {mok(V, r) == True{} : Bool}) -> {mok(V, T.ITree.bal.go(~U32, ~U32.cmp, V, lh, rh, l, e, r)) == True{} : Bool}:
  match lh:
    case True{}:
      rot_r.mok(V, l, e, r, hl, hr)
    case False{}:
      match rh:
        case True{}:
          rot_l.mok(V, l, e, r, hl, hr)
        case False{}:
          mk.mok(V, l, e, r, hl, hr)

def bal.mok(-V: Data, +l: Tr(V), +e: Ent(V), +r: Tr(V), +hl: {mok(V, l) == True{} : Bool}, +hr: {mok(V, r) == True{} : Bool}) -> {mok(V, T.ITree.bal(~U32, ~U32.cmp, V, l, e, r)) == True{} : Bool}:
  bal.go.mok(Nat.is_lt(1n+T.ITree.height(U32, V, r), T.ITree.height(U32, V, l)), Nat.is_lt(1n+T.ITree.height(U32, V, l), T.ITree.height(U32, V, r)), V, l, e, r, hl, hr)

def ins.mok(-V: Data, +t: Tr(V), +c: Cmp, +s: U32, +l: U32, +v: V, +ht: {mok(V, t) == True{} : Bool}) -> {mok(V, T.ITree.ins(~U32, ~U32.cmp, V, t, c, s, l, v)) == True{} : Bool}:
  match t:
    case T.ITreeLeaf{}:
      mk.mok(V, T.ITreeLeaf{}, T.ITreeEntry{s, l, v}, T.ITreeLeaf{}, {==}, {==})
    case T.ITreeNode{+h, +m, +tl, +e, +tr}:
      match c:
        case LT{}:
          bal.mok(V, tins(V, tl, s, l, v), e, tr, ins.mok(V, tl, T.ITree.probe(~U32, ~U32.cmp, V, tl, s, l), s, l, v, mok.l(V, h, m, tl, e, tr, ht)), mok.r(V, h, m, tl, e, tr, ht))
        case EQ{}:
          mk.mok(V, tl, T.ITreeEntry{s, l, v}, tr, mok.l(V, h, m, tl, e, tr, ht), mok.r(V, h, m, tl, e, tr, ht))
        case GT{}:
          bal.mok(V, tl, e, tins(V, tr, s, l, v), mok.l(V, h, m, tl, e, tr, ht), ins.mok(V, tr, T.ITree.probe(~U32, ~U32.cmp, V, tr, s, l), s, l, v, mok.r(V, h, m, tl, e, tr, ht)))

def dm.mok(-V: Data, +t: Tr(V), +e: Ent(V), +r: Tr(V), +ht: {mok(V, t) == True{} : Bool}, +hr: {mok(V, r) == True{} : Bool}) -> {mok(V, T.ITree.del_min(~U32, ~U32.cmp, V, t, e, r)) == True{} : Bool}:
  match t:
    case T.ITreeLeaf{}:
      hr
    case T.ITreeNode{+h, +m, +l2, +e2, +r2}:
      +ht = ht
      bal.mok(V, T.ITree.del_min(~U32, ~U32.cmp, V, l2, e2, r2), e, r, dm.mok(V, l2, e2, r2, mok.l(V, h, m, l2, e2, r2, ht), mok.r(V, h, m, l2, e2, r2, ht)), hr)

def merge.mok(-V: Data, +l: Tr(V), +r: Tr(V), +hl: {mok(V, l) == True{} : Bool}, +hr: {mok(V, r) == True{} : Bool}) -> {mok(V, T.ITree.merge(~U32, ~U32.cmp, V, l, r)) == True{} : Bool}:
  match r:
    case T.ITreeLeaf{}:
      hl
    case T.ITreeNode{+h, +m, +rl, +re, +rr}:
      +hr = hr
      bal.mok(V, l, T.ITree.min_of(U32, V, rl, re), T.ITree.del_min(~U32, ~U32.cmp, V, rl, re, rr), hl, dm.mok(V, rl, re, rr, mok.l(V, h, m, rl, re, rr, hr), mok.r(V, h, m, rl, re, rr, hr)))

def rem.mok(-V: Data, +t: Tr(V), +c: Cmp, +s: U32, +l: U32, +ht: {mok(V, t) == True{} : Bool}) -> {mok(V, T.ITree.rem(~U32, ~U32.cmp, V, t, c, s, l)) == True{} : Bool}:
  match t:
    case T.ITreeLeaf{}:
      {==}
    case T.ITreeNode{+h, +m, +tl, +e, +tr}:
      match c:
        case LT{}:
          bal.mok(V, trem(V, tl, s, l), e, tr, rem.mok(V, tl, T.ITree.probe(~U32, ~U32.cmp, V, tl, s, l), s, l, mok.l(V, h, m, tl, e, tr, ht)), mok.r(V, h, m, tl, e, tr, ht))
        case EQ{}:
          merge.mok(V, tl, tr, mok.l(V, h, m, tl, e, tr, ht), mok.r(V, h, m, tl, e, tr, ht))
        case GT{}:
          bal.mok(V, tl, e, trem(V, tr, s, l), mok.l(V, h, m, tl, e, tr, ht), rem.mok(V, tr, T.ITree.probe(~U32, ~U32.cmp, V, tr, s, l), s, l, mok.r(V, h, m, tl, e, tr, ht)))

# The model's insertion and removal keep a list sorted

def aft.ins.go(+c: Cmp, -V: Data, +s0: U32, +l0: U32, +x: Ent(V), +r: Es(V), +s: U32, +l: U32, +v: V, +h1: {aft(V, s0, l0, Con{x, r}) == True{} : Bool}, +h2: {kc(s0, l0, s, l) == LT{} : Cmp}, +ih: {aft(V, s0, l0, mins(V, r, s, l, v)) == True{} : Bool}) -> {aft(V, s0, l0, igo(V, c, x, r, T.ITreeEntry{s, l, v}, mins(V, r, s, l, v))) == True{} : Bool}:
  match c:
    case LT{}:
      bool.and_intro(Cmp.is_lt(kc(s0, l0, s, l)), aft(V, s0, l0, Con{x, r}), cmp.is_lt_of(kc(s0, l0, s, l), h2), h1)
    case EQ{}:
      bool.and_intro(Cmp.is_lt(kc(s0, l0, s, l)), aft(V, s0, l0, r), cmp.is_lt_of(kc(s0, l0, s, l), h2), bool.and_r(Cmp.is_lt(ec(V, s0, l0, x)), aft(V, s0, l0, r), h1))
    case GT{}:
      bool.and_intro(Cmp.is_lt(ec(V, s0, l0, x)), aft(V, s0, l0, mins(V, r, s, l, v)), bool.and_l(Cmp.is_lt(ec(V, s0, l0, x)), aft(V, s0, l0, r), h1), ih)

def aft.ins(-V: Data, +s0: U32, +l0: U32, +xs: Es(V), +s: U32, +l: U32, +v: V, +h1: {aft(V, s0, l0, xs) == True{} : Bool}, +h2: {kc(s0, l0, s, l) == LT{} : Cmp}) -> {aft(V, s0, l0, mins(V, xs, s, l, v)) == True{} : Bool}:
  match xs:
    case Nil{}:
      bool.and_intro(Cmp.is_lt(kc(s0, l0, s, l)), True{}, cmp.is_lt_of(kc(s0, l0, s, l), h2), {==})
    case Con{+x, +r}:
      +h1 = h1
      aft.ins.go(ec(V, s, l, x), V, s0, l0, x, r, s, l, v, h1, h2, aft.ins(V, s0, l0, r, s, l, v, bool.and_r(Cmp.is_lt(ec(V, s0, l0, x)), aft(V, s0, l0, r), h1), h2))

def ins.sorted.go(+c: Cmp, -V: Data, +x: Ent(V), +r: Es(V), +s: U32, +l: U32, +v: V, +ee: {ec(V, s, l, x) == c : Cmp}, +h: {srt(V, Con{x, r}) == True{} : Bool}, +ih: {srt(V, mins(V, r, s, l, v)) == True{} : Bool}) -> {srt(V, igo(V, c, x, r, T.ITreeEntry{s, l, v}, mins(V, r, s, l, v))) == True{} : Bool}:
  match c:
    case LT{}:
      bool.and_intro(aft(V, s, l, Con{x, r}), srt(V, Con{x, r}), bool.and_intro(Cmp.is_lt(ec(V, s, l, x)), aft(V, s, l, r), cmp.is_lt_of(ec(V, s, l, x), ee), aft.weaken(V, s, l, st(V, x), la(V, x), r, srt.head(V, x, r, h), ee)), h)
    case EQ{}:
      bool.and_intro(aft(V, s, l, r), srt(V, r), aft.eqk(V, s, l, st(V, x), la(V, x), r, srt.head(V, x, r, h), ee), srt.tail(V, x, r, h))
    case GT{}:
      bool.and_intro(aft(V, st(V, x), la(V, x), mins(V, r, s, l, v)), srt(V, mins(V, r, s, l, v)), aft.ins(V, st(V, x), la(V, x), r, s, l, v, srt.head(V, x, r, h), kc.flip_of(s, l, st(V, x), la(V, x), GT{}, ee)), ih)

def ins.sorted(-V: Data, +xs: Es(V), +s: U32, +l: U32, +v: V, +h: {srt(V, xs) == True{} : Bool}) -> {srt(V, mins(V, xs, s, l, v)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h = h
      ins.sorted.go(ec(V, s, l, x), V, x, r, s, l, v, {==}, h, ins.sorted(V, r, s, l, v, srt.tail(V, x, r, h)))

def aft.rem.go(+b: Bool, -V: Data, +s0: U32, +l0: U32, +x: Ent(V), +r: Es(V), +s: U32, +l: U32, +h1: {aft(V, s0, l0, Con{x, r}) == True{} : Bool}, +ih: {aft(V, s0, l0, mrem(V, r, s, l)) == True{} : Bool}) -> {aft(V, s0, l0, keep(V, b, x, mrem(V, r, s, l))) == True{} : Bool}:
  match b:
    case True{}:
      bool.and_intro(Cmp.is_lt(ec(V, s0, l0, x)), aft(V, s0, l0, mrem(V, r, s, l)), bool.and_l(Cmp.is_lt(ec(V, s0, l0, x)), aft(V, s0, l0, r), h1), ih)
    case False{}:
      ih

def aft.rem(-V: Data, +s0: U32, +l0: U32, +xs: Es(V), +s: U32, +l: U32, +h1: {aft(V, s0, l0, xs) == True{} : Bool}) -> {aft(V, s0, l0, mrem(V, xs, s, l)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h1 = h1
      aft.rem.go(Bool.not(Cmp.is_eq(ec(V, s, l, x))), V, s0, l0, x, r, s, l, h1, aft.rem(V, s0, l0, r, s, l, bool.and_r(Cmp.is_lt(ec(V, s0, l0, x)), aft(V, s0, l0, r), h1)))

def rem.sorted.go(+b: Bool, -V: Data, +x: Ent(V), +r: Es(V), +s: U32, +l: U32, +h: {srt(V, Con{x, r}) == True{} : Bool}, +ih: {srt(V, mrem(V, r, s, l)) == True{} : Bool}) -> {srt(V, keep(V, b, x, mrem(V, r, s, l))) == True{} : Bool}:
  match b:
    case True{}:
      bool.and_intro(aft(V, st(V, x), la(V, x), mrem(V, r, s, l)), srt(V, mrem(V, r, s, l)), aft.rem(V, st(V, x), la(V, x), r, s, l, srt.head(V, x, r, h)), ih)
    case False{}:
      ih

def rem.sorted(-V: Data, +xs: Es(V), +s: U32, +l: U32, +h: {srt(V, xs) == True{} : Bool}) -> {srt(V, mrem(V, xs, s, l)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h = h
      rem.sorted.go(Bool.not(Cmp.is_eq(ec(V, s, l, x))), V, x, r, s, l, h, rem.sorted(V, r, s, l, srt.tail(V, x, r, h)))

# The invariant

def valid(-V: Data, +t: Tr(V)) -> Bool:
  T.ITree.valid(~U32, ~U32.cmp, V, t)

def valid.srt(-V: Data, +t: Tr(V), +h: {valid(V, t) == True{} : Bool}) -> {srt(V, L(V, t)) == True{} : Bool}:
  bool.and_l(srt(V, L(V, t)), mok(V, t), h)

def valid.mok(-V: Data, +t: Tr(V), +h: {valid(V, t) == True{} : Bool}) -> {mok(V, t) == True{} : Bool}:
  bool.and_r(srt(V, L(V, t)), mok(V, t), h)

def ins.valid(-V: Data, +t: Tr(V), +s: U32, +l: U32, +v: V, +h: {valid(V, t) == True{} : Bool}) -> {valid(V, tins(V, t, s, l, v)) == True{} : Bool}:
  %Equal.sym(Es(V), L(V, tins(V, t, s, l, v)), mins(V, L(V, t), s, l, v), ins.list(V, t, s, l, v, valid.srt(V, t, h))) : {Bool.and(srt(V, _), mok(V, tins(V, t, s, l, v))) == True{} : Bool}
  bool.and_intro(srt(V, mins(V, L(V, t), s, l, v)), mok(V, tins(V, t, s, l, v)), ins.sorted(V, L(V, t), s, l, v, valid.srt(V, t, h)), ins.mok(V, t, T.ITree.probe(~U32, ~U32.cmp, V, t, s, l), s, l, v, valid.mok(V, t, h)))

def rem.valid(-V: Data, +t: Tr(V), +s: U32, +l: U32, +h: {valid(V, t) == True{} : Bool}) -> {valid(V, trem(V, t, s, l)) == True{} : Bool}:
  %Equal.sym(Es(V), L(V, trem(V, t, s, l)), mrem(V, L(V, t), s, l), rem.list(V, t, s, l, valid.srt(V, t, h))) : {Bool.and(srt(V, _), mok(V, trem(V, t, s, l))) == True{} : Bool}
  bool.and_intro(srt(V, mrem(V, L(V, t), s, l)), mok(V, trem(V, t, s, l)), rem.sorted(V, L(V, t), s, l, valid.srt(V, t, h)), rem.mok(V, t, T.ITree.probe(~U32, ~U32.cmp, V, t, s, l), s, l, valid.mok(V, t, h)))

def set.valid(+c: Cmp, -V: Data, +t: Tr(V), +s: U32, +l: U32, +v: V, +h: {valid(V, t) == True{} : Bool}) -> {valid(V, T.ITree.set.go(~U32, ~U32.cmp, V, c, t, s, l, v)) == True{} : Bool}:
  match c:
    case LT{}:
      ins.valid(V, t, s, l, v, h)
    case EQ{}:
      ins.valid(V, t, s, l, v, h)
    case GT{}:
      h

def set.list(+c: Cmp, -V: Data, +t: Tr(V), +s: U32, +l: U32, +v: V, +h: {valid(V, t) == True{} : Bool}) -> {L(V, T.ITree.set.go(~U32, ~U32.cmp, V, c, t, s, l, v)) == M.ITreeModel.set.go(~U32, ~U32.cmp, V, c, L(V, t), s, l, v) : Es(V)}:
  match c:
    case LT{}:
      ins.list(V, t, s, l, v, valid.srt(V, t, h))
    case EQ{}:
      ins.list(V, t, s, l, v, valid.srt(V, t, h))
    case GT{}:
      {==}

# After an update: what lookup and the queries find

def mlook.n(-V: Data, +s: U32, +l: U32, +v: V, +rest: Maybe<&2, V>) -> {lgo(V, Cmp.is_eq(ec(V, s, l, T.ITreeEntry{s, l, v})), T.ITreeEntry{s, l, v}, rest) == Some{v} : Maybe<&2, V>}:
  %Equal.sym(Cmp, kc(s, l, s, l), EQ{}, kc.refl(s, l)) : {lgo(V, Cmp.is_eq(_), T.ITreeEntry{s, l, v}, rest) == Some{v} : Maybe<&2, V>}
  {==}

def look.ins.go(c: Cmp, -V: Data, +x: Ent(V), +r: Es(V), +s: U32, +l: U32, +v: V, +ee: {ec(V, s, l, x) == c : Cmp}, ih: {mlook(V, mins(V, r, s, l, v), s, l) == Some{v} : Maybe<&2, V>}) -> {mlook(V, igo(V, c, x, r, T.ITreeEntry{s, l, v}, mins(V, r, s, l, v)), s, l) == Some{v} : Maybe<&2, V>}:
  match c:
    case LT{}:
      mlook.n(V, s, l, v, mlook(V, Con{x, r}, s, l))
    case EQ{}:
      mlook.n(V, s, l, v, mlook(V, r, s, l))
    case GT{}:
      %Equal.sym(Cmp, ec(V, s, l, x), GT{}, ee) : {lgo(V, Cmp.is_eq(_), x, mlook(V, mins(V, r, s, l, v), s, l)) == Some{v} : Maybe<&2, V>}
      ih

def look.ins(-V: Data, xs: Es(V), +s: U32, +l: U32, +v: V) -> {mlook(V, mins(V, xs, s, l, v), s, l) == Some{v} : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      mlook.n(V, s, l, v, None{})
    case Con{+x, +r}:
      look.ins.go(ec(V, s, l, x), V, x, r, s, l, v, {==}, look.ins(V, r, s, l, v))

def found.n(-V: Data, +s: U32, +l: U32, +v: V, +a: U32, +b: U32, +rest: Es(V), hov: {eov(V, T.ITreeEntry{s, l, v}, a, b) == True{} : Bool}) -> {mlook(V, keep(V, eov(V, T.ITreeEntry{s, l, v}, a, b), T.ITreeEntry{s, l, v}, rest), s, l) == Some{v} : Maybe<&2, V>}:
  %Equal.sym(Bool, eov(V, T.ITreeEntry{s, l, v}, a, b), True{}, hov) : {mlook(V, keep(V, _, T.ITreeEntry{s, l, v}, rest), s, l) == Some{v} : Maybe<&2, V>}
  mlook.n(V, s, l, v, mlook(V, rest, s, l))

def found.gt(k: Bool, -V: Data, +x: Ent(V), +rest: Es(V), +s: U32, +l: U32, +v: V, +ee: {ec(V, s, l, x) == GT{} : Cmp}, ih: {mlook(V, rest, s, l) == Some{v} : Maybe<&2, V>}) -> {mlook(V, keep(V, k, x, rest), s, l) == Some{v} : Maybe<&2, V>}:
  match k:
    case True{}:
      %Equal.sym(Cmp, ec(V, s, l, x), GT{}, ee) : {lgo(V, Cmp.is_eq(_), x, mlook(V, rest, s, l)) == Some{v} : Maybe<&2, V>}
      ih
    case False{}:
      ih

def found.ins.go(c: Cmp, -V: Data, +x: Ent(V), +r: Es(V), +s: U32, +l: U32, +v: V, +a: U32, +b: U32, +ee: {ec(V, s, l, x) == c : Cmp}, +hov: {eov(V, T.ITreeEntry{s, l, v}, a, b) == True{} : Bool}, ih: {mlook(V, mov(V, mins(V, r, s, l, v), a, b), s, l) == Some{v} : Maybe<&2, V>}) -> {mlook(V, mov(V, igo(V, c, x, r, T.ITreeEntry{s, l, v}, mins(V, r, s, l, v)), a, b), s, l) == Some{v} : Maybe<&2, V>}:
  match c:
    case LT{}:
      found.n(V, s, l, v, a, b, mov(V, Con{x, r}, a, b), hov)
    case EQ{}:
      found.n(V, s, l, v, a, b, mov(V, r, a, b), hov)
    case GT{}:
      found.gt(eov(V, x, a, b), V, x, mov(V, mins(V, r, s, l, v), a, b), s, l, v, ee, ih)

def found.ins(-V: Data, xs: Es(V), +s: U32, +l: U32, +v: V, +a: U32, +b: U32, +hov: {eov(V, T.ITreeEntry{s, l, v}, a, b) == True{} : Bool}) -> {mlook(V, mov(V, mins(V, xs, s, l, v), a, b), s, l) == Some{v} : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      found.n(V, s, l, v, a, b, Nil{}, hov)
    case Con{+x, +r}:
      found.ins.go(ec(V, s, l, x), V, x, r, s, l, v, a, b, {==}, hov, found.ins(V, r, s, l, v, a, b, hov))

def look.rem.go(bb: Bool, -V: Data, +x: Ent(V), +r: Es(V), +s: U32, +l: U32, eq: {Cmp.is_eq(ec(V, s, l, x)) == bb : Bool}, ih: {mlook(V, mrem(V, r, s, l), s, l) == None{} : Maybe<&2, V>}) -> {mlook(V, keep(V, Bool.not(bb), x, mrem(V, r, s, l)), s, l) == None{} : Maybe<&2, V>}:
  match bb:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, Cmp.is_eq(ec(V, s, l, x)), False{}, eq) : {lgo(V, _, x, mlook(V, mrem(V, r, s, l), s, l)) == None{} : Maybe<&2, V>}
      ih

def look.rem(-V: Data, xs: Es(V), +s: U32, +l: U32) -> {mlook(V, mrem(V, xs, s, l), s, l) == None{} : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      look.rem.go(Cmp.is_eq(ec(V, s, l, x)), V, x, r, s, l, {==}, look.rem(V, r, s, l))

# The largest last: an upper bound of every last, and one of them

def lle(-V: Data, xs: Es(V), +m: U32) -> Bool:
  M.ITreeModel.lasts_le(~U32, ~U32.cmp, V, xs, m)

def hasl(-V: Data, xs: Es(V), +m: U32) -> Bool:
  M.ITreeModel.has_last(~U32, ~U32.cmp, V, xs, m)

def bool.or_l(-x: Bool, -y: Bool, ex: {x == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  %Equal.sym(Bool, x, True{}, ex) : {Bool.or(_, y) == True{} : Bool}
  {==}

def bool.or_r(x: Bool, -y: Bool, ey: {y == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      ey

def bool.or_mono(q: Bool, -y: Bool, -z: Bool, h: {Bool.or(q, y) == True{} : Bool}, f: {y == True{} : Bool} -> {z == True{} : Bool}) -> {Bool.or(q, z) == True{} : Bool}:
  match q:
    case True{}:
      {==}
    case False{}:
      f(h)

def le.subst_l(-a: U32, -b: U32, -c: U32, e: {a == b : U32}, h: {Cmp.is_le(U32.cmp(a, c)) == True{} : Bool}) -> {Cmp.is_le(U32.cmp(b, c)) == True{} : Bool}:
  %e : {Cmp.is_le(U32.cmp(_, c)) == True{} : Bool}
  h

def eq.is_eq(+a: U32, -b: U32, e: {a == b : U32}) -> {Cmp.is_eq(U32.cmp(a, b)) == True{} : Bool}:
  %e : {Cmp.is_eq(U32.cmp(a, _)) == True{} : Bool}
  %Equal.sym(Cmp, U32.cmp(a, a), EQ{}, UO.u32_cmp_refl(a)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def kmax.idem(+m: U32) -> {kmax(m, m) == m : U32}:
  %Equal.sym(Cmp, U32.cmp(m, m), EQ{}, UO.u32_cmp_refl(m)) : {T.ITree.kmax.pick(U32, _, m, m) == m : U32}
  {==}

def lle.app(-V: Data, xs: Es(V), +ys: Es(V), +m: U32, hx: {lle(V, xs, m) == True{} : Bool}, hy: {lle(V, ys, m) == True{} : Bool}) -> {lle(V, app(V, xs, ys), m) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+x, +r}:
      +hx = hx
      bool.and_intro(Cmp.is_le(U32.cmp(la(V, x), m)), lle(V, app(V, r, ys), m), bool.and_l(Cmp.is_le(U32.cmp(la(V, x), m)), lle(V, r, m), hx), lle.app(V, r, ys, m, bool.and_r(Cmp.is_le(U32.cmp(la(V, x), m)), lle(V, r, m), hx), hy))

def lle.weaken(-V: Data, xs: Es(V), +a: U32, +b: U32, h: {lle(V, xs, a) == True{} : Bool}, +g: {Cmp.is_le(U32.cmp(a, b)) == True{} : Bool}) -> {lle(V, xs, b) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +h = h
      bool.and_intro(Cmp.is_le(U32.cmp(la(V, x), b)), lle(V, r, b), u32.le_le(la(V, x), a, b, bool.and_l(Cmp.is_le(U32.cmp(la(V, x), a)), lle(V, r, a), h), g), lle.weaken(V, r, a, b, bool.and_r(Cmp.is_le(U32.cmp(la(V, x), a)), lle(V, r, a), h), g))

def hasl.rw(-V: Data, +xs: Es(V), -a: U32, -b: U32, e: {a == b : U32}, h: {hasl(V, xs, a) == True{} : Bool}) -> {hasl(V, xs, b) == True{} : Bool}:
  %e : {hasl(V, xs, _) == True{} : Bool}
  h

def hasl.app_l(-V: Data, xs: Es(V), +ys: Es(V), +m: U32, h: {hasl(V, xs, m) == True{} : Bool}) -> {hasl(V, app(V, xs, ys), m) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({hasl(V, ys, m) == True{} : Bool}, absurd.ft(h))
    case Con{+x, +r}:
      bool.or_mono(Cmp.is_eq(U32.cmp(la(V, x), m)), hasl(V, r, m), hasl(V, app(V, r, ys), m), h, w => hasl.app_l(V, r, ys, m, w))

def hasl.app_r(-V: Data, xs: Es(V), +ys: Es(V), +m: U32, h: {hasl(V, ys, m) == True{} : Bool}) -> {hasl(V, app(V, xs, ys), m) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+x, +r}:
      bool.or_r(Cmp.is_eq(U32.cmp(la(V, x), m)), hasl(V, app(V, r, ys), m), hasl.app_r(V, r, ys, m, h))

def node.meq(-V: Data, +h: Nat, +m: U32, +l: Tr(V), +e: Ent(V), +r: Tr(V), hm: {mok(V, T.ITreeNode{h, m, l, e, r}) == True{} : Bool}) -> {m == bnd(V, l, bnd(V, r, la(V, e))) : U32}:
  UO.u32_cmp_eq(m, bnd(V, l, bnd(V, r, la(V, e))), cmp.eq_of(U32.cmp(m, bnd(V, l, bnd(V, r, la(V, e)))), bool.and_l(Cmp.is_eq(U32.cmp(m, bnd(V, l, bnd(V, r, la(V, e))))), Bool.and(mok(V, l), mok(V, r)), hm)))

# every last in t is at most the larger of x and t's largest last
def maxle(-V: Data, t: Tr(V), +x: U32, hm: {mok(V, t) == True{} : Bool}) -> {lle(V, L(V, t), bnd(V, t, x)) == True{} : Bool}:
  match t:
    case T.ITreeLeaf{}:
      {==}
    case T.ITreeNode{+h, +m, +l, +e, +r}:
      +hm = hm
      +mb = le.subst_l(m, bnd(V, l, bnd(V, r, la(V, e))), kmax(m, x), node.meq(V, h, m, l, e, r, hm), kmax.ge_l(m, x))
      +xb = u32.le_le(bnd(V, r, la(V, e)), bnd(V, l, bnd(V, r, la(V, e))), kmax(m, x), bnd.ge(V, l, bnd(V, r, la(V, e))), mb)
      lle.app(V, L(V, l), Con{e, L(V, r)}, kmax(m, x), lle.weaken(V, L(V, l), bnd(V, l, bnd(V, r, la(V, e))), kmax(m, x), maxle(V, l, bnd(V, r, la(V, e)), mok.l(V, h, m, l, e, r, hm)), mb), bool.and_intro(Cmp.is_le(U32.cmp(la(V, e), kmax(m, x))), lle(V, L(V, r), kmax(m, x)), u32.le_le(la(V, e), bnd(V, r, la(V, e)), kmax(m, x), bnd.ge(V, r, la(V, e)), xb), lle.weaken(V, L(V, r), bnd(V, r, la(V, e)), kmax(m, x), maxle(V, r, la(V, e), mok.r(V, h, m, l, e, r, hm)), xb)))

def att.mid(-V: Data, +h: Nat, +m: U32, +l: Tr(V), +e: Ent(V), +r: Tr(V), +meq: {m == bnd(V, l, bnd(V, r, la(V, e))) : U32}, il: Either<&2, &2, {bnd(V, l, bnd(V, r, la(V, e))) == bnd(V, r, la(V, e)) : U32}, {hasl(V, L(V, l), bnd(V, l, bnd(V, r, la(V, e)))) == True{} : Bool}>, ir: Either<&2, &2, {bnd(V, r, la(V, e)) == la(V, e) : U32}, {hasl(V, L(V, r), bnd(V, r, la(V, e))) == True{} : Bool}>) -> {hasl(V, app(V, L(V, l), Con{e, L(V, r)}), m) == True{} : Bool}:
  match il:
    case Inr{q}:
      hasl.app_l(V, L(V, l), Con{e, L(V, r)}, m, hasl.rw(V, L(V, l), bnd(V, l, bnd(V, r, la(V, e))), m, Equal.sym(U32, m, bnd(V, l, bnd(V, r, la(V, e))), meq), q))
    case Inl{+p}:
      match ir:
        case Inr{q2}:
          hasl.app_r(V, L(V, l), Con{e, L(V, r)}, m, bool.or_r(Cmp.is_eq(U32.cmp(la(V, e), m)), hasl(V, L(V, r), m), hasl.rw(V, L(V, r), bnd(V, r, la(V, e)), m, Equal.sym(U32, m, bnd(V, r, la(V, e)), Equal.trans(U32, m, bnd(V, l, bnd(V, r, la(V, e))), bnd(V, r, la(V, e)), meq, p)), q2)))
        case Inl{p2}:
          hasl.app_r(V, L(V, l), Con{e, L(V, r)}, m, bool.or_l(Cmp.is_eq(U32.cmp(la(V, e), m)), hasl(V, L(V, r), m), eq.is_eq(la(V, e), m, Equal.sym(U32, m, la(V, e), Equal.trans(U32, m, bnd(V, r, la(V, e)), la(V, e), Equal.trans(U32, m, bnd(V, l, bnd(V, r, la(V, e))), bnd(V, r, la(V, e)), meq, p), p2)))))

def att.top(c: Cmp, -V: Data, +m: U32, +x: U32, -xs: Es(V), hn: {hasl(V, xs, m) == True{} : Bool}) -> Either<&2, &2, {T.ITree.kmax.pick(U32, c, m, x) == x : U32}, {hasl(V, xs, T.ITree.kmax.pick(U32, c, m, x)) == True{} : Bool}>:
  match c:
    case LT{}:
      Inl{{==}}
    case EQ{}:
      Inr{hn}
    case GT{}:
      Inr{hn}

# t's bound on x is x itself, or the last of one of t's entries
def attained(-V: Data, t: Tr(V), +x: U32, hm: {mok(V, t) == True{} : Bool}) -> Either<&2, &2, {bnd(V, t, x) == x : U32}, {hasl(V, L(V, t), bnd(V, t, x)) == True{} : Bool}>:
  match t:
    case T.ITreeLeaf{}:
      Inl{{==}}
    case T.ITreeNode{+h, +m, +l, +e, +r}:
      +hm = hm
      att.top(U32.cmp(m, x), V, m, x, app(V, L(V, l), Con{e, L(V, r)}), att.mid(V, h, m, l, e, r, node.meq(V, h, m, l, e, r, hm), attained(V, l, bnd(V, r, la(V, e)), mok.l(V, h, m, l, e, r, hm)), attained(V, r, la(V, e), mok.r(V, h, m, l, e, r, hm))))

# Maybe

def absurd.isnone(m: Maybe<&2, U32>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{y}:
      Empty

def absurd.issome(m: Maybe<&2, U32>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{y}:
      Unit

def absurd.ns(-m: U32, e: {None{} == Some{m} : Maybe<&2, U32>}) -> Empty:
  %e : absurd.isnone(_)
  Unit{}

def absurd.sn(-m: U32, e: {Some{m} == None{} : Maybe<&2, U32>}) -> Empty:
  %e : absurd.issome(_)
  Unit{}

def maybe.get(m: Maybe<&2, U32>, +d: U32) -> U32:
  match m:
    case None{}:
      d
    case Some{y}:
      y

def some.inj(+a: U32, -b: U32, e: {Some{a} == Some{b} : Maybe<&2, U32>}) -> {a == b : U32}:
  Equal.cong(Maybe<&2, U32>, U32, w => maybe.get(w, a), Some{a}, Some{b}, e)

# The laws

def Laws.valid_empty(V):
  {==}

def Laws.valid_set(V, t, s, l, v, e):
  set.valid(U32.cmp(s, l), V, t, s, l, v, e)

def Laws.valid_remove(V, t, s, l, e):
  rem.valid(V, t, s, l, e)

def Laws.set_contents(V, t, s, l, v, e):
  set.list(U32.cmp(s, l), V, t, s, l, v, e)

def Laws.remove_contents(V, t, s, l, e):
  rem.list(V, t, s, l, valid.srt(V, t, e))

def Laws.set_inverted(V, t, s, l, v, e):
  %Equal.sym(Cmp, U32.cmp(s, l), GT{}, u32.flip_of(l, s, LT{}, cmp.lt_of(U32.cmp(l, s), e))) : {T.ITree.set.go(~U32, ~U32.cmp, V, _, t, s, l, v) == t : T.ITree<U32, V>}
  {==}

def Laws.insert_inverted(V, t, s, l, v, e):
  %Equal.sym(Cmp, U32.cmp(s, l), GT{}, u32.flip_of(l, s, LT{}, cmp.lt_of(U32.cmp(l, s), e))) : {T.ITree.insert.go(~U32, ~U32.cmp, V, _, t, s, l, v) == Fail{T.ITreeInverted{s, l}} : Result<&2, &2, T.ITreeError<U32>, T.ITree<U32, V>>}
  {==}

def insert.set.go(c: Cmp, -V: Data, +t: Tr(V), +s: U32, +l: U32, +v: V, h: {Cmp.is_le(c) == True{} : Bool}) -> {T.ITree.insert.go(~U32, ~U32.cmp, V, c, t, s, l, v) == Done{T.ITree.set.go(~U32, ~U32.cmp, V, c, t, s, l, v)} : Result<&2, &2, T.ITreeError<U32>, T.ITree<U32, V>>}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Fail{T.ITreeInverted{s, l}} == Done{t} : Result<&2, &2, T.ITreeError<U32>, T.ITree<U32, V>>}, absurd.ft(h))

def Laws.insert_set(V, t, s, l, v, e):
  insert.set.go(U32.cmp(s, l), V, t, s, l, v, e)

def Laws.overlapping_spec(V, t, a, b, e):
  ov.list(V, t, a, b, valid.srt(V, t, e), valid.mok(V, t, e))

def Laws.stab_spec(V, t, p, e):
  ov.list(V, t, p, p, valid.srt(V, t, e), valid.mok(V, t, e))

def Laws.first_spec(V, t, a, b, e):
  seek.list(V, t, a, b, T.ITreeFromStart{}, None{}, valid.srt(V, t, e), valid.mok(V, t, e))

def Laws.next_spec(V, t, a, b, s, l, e):
  seek.list(V, t, a, b, T.ITreeAfter{s, l}, None{}, valid.srt(V, t, e), valid.mok(V, t, e))

def Laws.lookup_spec(V, t, s, l, e):
  find.list(V, t, s, l, valid.srt(V, t, e))

def set.lookup.go(c: Cmp, -V: Data, +t: Tr(V), +s: U32, +l: U32, +v: V, h: {Cmp.is_le(c) == True{} : Bool}) -> {mlook(V, M.ITreeModel.set.go(~U32, ~U32.cmp, V, c, L(V, t), s, l, v), s, l) == Some{v} : Maybe<&2, V>}:
  match c:
    case LT{}:
      look.ins(V, L(V, t), s, l, v)
    case EQ{}:
      look.ins(V, L(V, t), s, l, v)
    case GT{}:
      Empty.absurd({mlook(V, L(V, t), s, l) == Some{v} : Maybe<&2, V>}, absurd.ft(h))

def Laws.set_lookup(V, t, s, l, v, e, f):
  %Equal.sym(Maybe<&2, V>, tfind(V, T.ITree32.set(V, t, s, l, v), s, l), mlook(V, L(V, T.ITree32.set(V, t, s, l, v)), s, l), find.list(V, T.ITree32.set(V, t, s, l, v), s, l, valid.srt(V, T.ITree32.set(V, t, s, l, v), set.valid(U32.cmp(s, l), V, t, s, l, v, e)))) : {_ == Some{v} : Maybe<&2, V>}
  %Equal.sym(Es(V), L(V, T.ITree32.set(V, t, s, l, v)), M.ITreeModel.set.go(~U32, ~U32.cmp, V, U32.cmp(s, l), L(V, t), s, l, v), set.list(U32.cmp(s, l), V, t, s, l, v, e)) : {mlook(V, _, s, l) == Some{v} : Maybe<&2, V>}
  set.lookup.go(U32.cmp(s, l), V, t, s, l, v, f)

def set.found.go(c: Cmp, -V: Data, +t: Tr(V), +s: U32, +l: U32, +v: V, +a: U32, +b: U32, h: {Cmp.is_le(c) == True{} : Bool}, g: {eov(V, T.ITreeEntry{s, l, v}, a, b) == True{} : Bool}) -> {mlook(V, mov(V, M.ITreeModel.set.go(~U32, ~U32.cmp, V, c, L(V, t), s, l, v), a, b), s, l) == Some{v} : Maybe<&2, V>}:
  match c:
    case LT{}:
      found.ins(V, L(V, t), s, l, v, a, b, g)
    case EQ{}:
      found.ins(V, L(V, t), s, l, v, a, b, g)
    case GT{}:
      Empty.absurd({mlook(V, mov(V, L(V, t), a, b), s, l) == Some{v} : Maybe<&2, V>}, absurd.ft(h))

def Laws.set_found(V, t, s, l, v, a, b, e, f, g):
  +vu = set.valid(U32.cmp(s, l), V, t, s, l, v, e)
  %Equal.sym(Es(V), tov(V, T.ITree32.set(V, t, s, l, v), reaches(V, T.ITree32.set(V, t, s, l, v), a), a, b), mov(V, L(V, T.ITree32.set(V, t, s, l, v)), a, b), ov.list(V, T.ITree32.set(V, t, s, l, v), a, b, valid.srt(V, T.ITree32.set(V, t, s, l, v), vu), valid.mok(V, T.ITree32.set(V, t, s, l, v), vu))) : {mlook(V, _, s, l) == Some{v} : Maybe<&2, V>}
  %Equal.sym(Es(V), L(V, T.ITree32.set(V, t, s, l, v)), M.ITreeModel.set.go(~U32, ~U32.cmp, V, U32.cmp(s, l), L(V, t), s, l, v), set.list(U32.cmp(s, l), V, t, s, l, v, e)) : {mlook(V, mov(V, _, a, b), s, l) == Some{v} : Maybe<&2, V>}
  set.found.go(U32.cmp(s, l), V, t, s, l, v, a, b, f, g)

def Laws.remove_lookup(V, t, s, l, e):
  %Equal.sym(Maybe<&2, V>, tfind(V, trem(V, t, s, l), s, l), mlook(V, L(V, trem(V, t, s, l)), s, l), find.list(V, trem(V, t, s, l), s, l, valid.srt(V, trem(V, t, s, l), rem.valid(V, t, s, l, e)))) : {_ == None{} : Maybe<&2, V>}
  %Equal.sym(Es(V), L(V, trem(V, t, s, l)), mrem(V, L(V, t), s, l), rem.list(V, t, s, l, valid.srt(V, t, e))) : {mlook(V, _, s, l) == None{} : Maybe<&2, V>}
  look.rem(V, L(V, t), s, l)

def Laws.max_last_upper(V, t, m, e, f):
  match t:
    case T.ITreeLeaf{}:
      Empty.absurd({lle(V, Nil{}, m) == True{} : Bool}, absurd.ns(m, f))
    case T.ITreeNode{+h, +mt, +l, +en, +r}:
      %some.inj(mt, m, f) : {lle(V, L(V, T.ITreeNode{h, mt, l, en, r}), _) == True{} : Bool}
      %kmax.idem(mt) : {lle(V, L(V, T.ITreeNode{h, mt, l, en, r}), _) == True{} : Bool}
      maxle(V, T.ITreeNode{h, mt, l, en, r}, mt, valid.mok(V, T.ITreeNode{h, mt, l, en, r}, e))

def Laws.max_last_attained(V, t, m, e, f):
  match t:
    case T.ITreeLeaf{}:
      Empty.absurd({hasl(V, Nil{}, m) == True{} : Bool}, absurd.ns(m, f))
    case T.ITreeNode{+h, +mt, +l, +en, +r}:
      +mk = valid.mok(V, T.ITreeNode{h, mt, l, en, r}, e)
      %some.inj(mt, m, f) : {hasl(V, L(V, T.ITreeNode{h, mt, l, en, r}), _) == True{} : Bool}
      att.mid(V, h, mt, l, en, r, node.meq(V, h, mt, l, en, r, mk), attained(V, l, bnd(V, r, la(V, en)), mok.l(V, h, mt, l, en, r, mk)), attained(V, r, la(V, en), mok.r(V, h, mt, l, en, r, mk)))

def Laws.max_last_empty(V, t, f):
  match t:
    case T.ITreeLeaf{}:
      {==}
    case T.ITreeNode{h, m, l, en, r}:
      Empty.absurd({L(V, T.ITreeNode{h, m, l, en, r}) == Nil{} : Es(V)}, absurd.sn(m, f))

def Laws.example_valid():
  {==}

def Laws.example_balanced():
  {==}

def Laws.example_contents():
  {==}

def Laws.example_overlapping():
  {==}

def Laws.example_stab():
  {==}

def Laws.example_first():
  {==}

def Laws.example_next():
  {==}

def Laws.example_none():
  {==}

def Laws.example_remove():
  {==}

def Laws.example_lookup():
  {==}

def Laws.example_max_last():
  {==}

def Laws.example_insert_inverted():
  {==}

def Laws.example_in_order():
  {==}

def Laws.example_inverted():
  {==}

def Laws.example_overlaps():
  {==}

def Laws.example_max_last_empty():
  {==}
