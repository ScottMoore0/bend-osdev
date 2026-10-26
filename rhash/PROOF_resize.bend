# The proof that a resize finishes (LAWS_resize.bend), for tables built
# through the interface.
#
# The invariant (rz.inv): the current array is a complete tree of depth
# log, with log at most 31 (RHash.log_limit()); the old array, of depth
# olog <= 31, is either one empty bucket, or the cursor c is below
# 2^olog and the tree is "c of 2^olog buckets taken" (rz.w): a tree of
# depth d with i of its buckets taken is one empty bucket (any i up to
# 2^d), or a leaf at depth 0 with nothing taken, or a node with i < 2^d
# whose halves have ceil(i/2) and floor(i/2) of theirs taken (the cursor
# reads its low bit first, so it alternates between the halves). Taking
# the cursor's bucket (rz.take_w) moves i to i + 1, and a tree with all
# 2^d taken is one empty bucket (rz.done); so 2^olog - c steps empty the
# old array. Inserts and removes only delete from the old array (rz.put_w),
# a resize starts only when the old array is empty, from the complete
# current array, with c = 0 (rz.full_w), and every log is clamped to 31,
# which keeps the cursor's U32 arithmetic exact (rz.next_val).
import Base
import ./rhash.bend as R
import ./LAWS_resize.bend as Laws
import ../u32/u32.bend as U
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF_order.bend as UOP

# ---------------------------------------------------------------- booleans

def rz.bool(+b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def rz.tf(+e: {True{} == False{} : Bool}) -> Empty:
  %e : rz.bool(_)
  Unit{}

def rz.ft(+e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : rz.bool(_)
  Unit{}

def rz.and_l(+a: Bool, -b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, rz.ft(e))

def rz.and_r(+a: Bool, -b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, rz.ft(e))

def rz.and2(+a: Bool, -b: Bool, +ea: {a == True{} : Bool}, +eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def rz.or_r(+a: Bool, -b: Bool, +e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

# ---------------------------------------------------------------- Nat

def rz.lt_irrefl(+n: Nat) -> {Nat.is_lt(n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      rz.lt_irrefl(p)

# i < d gives i + 1 <= d
def rz.lt_le_succ(+i: Nat, +d: Nat, +h: {Nat.is_lt(i, d) == True{} : Bool}) -> {Nat.is_le(1n+i, d) == True{} : Bool}:
  match i d:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, rz.ft(h))
    case 0n 1n+ +e:
      match e:
        case 0n:
          {==}
        case 1n+ +f:
          {==}
    case 1n+ +a 0n:
      Empty.absurd({Nat.is_le(2n+a, 0n) == True{} : Bool}, rz.ft(h))
    case 1n+ +a 1n+ +e:
      rz.lt_le_succ(a, e, h)

# i <= d and not i < d give i = d
def rz.le_lt_eq(+i: Nat, +d: Nat, +h1: {Nat.is_le(i, d) == True{} : Bool}, +h2: {Nat.is_lt(i, d) == False{} : Bool}) -> {i == d : Nat}:
  match i d:
    case 0n 0n:
      {==}
    case 0n 1n+ +e:
      Empty.absurd({0n == 1n+e : Nat}, rz.tf(h2))
    case 1n+ +a 0n:
      Empty.absurd({1n+a == 0n : Nat}, rz.ft(h1))
    case 1n+ +a 1n+ +e:
      Equal.cong(Nat, Nat, z => 1n+z, a, e, rz.le_lt_eq(a, e, h1, h2))

# i < d and d <= i cannot both hold
def rz.lt_not_le(+i: Nat, +d: Nat, +h1: {Nat.is_lt(i, d) == True{} : Bool}, +h2: {Nat.is_le(d, i) == True{} : Bool}) -> Empty:
  match i d:
    case 0n 0n:
      rz.ft(h1)
    case 0n 1n+ +e:
      rz.ft(h2)
    case 1n+ +a 0n:
      rz.ft(h1)
    case 1n+ +a 1n+ +e:
      rz.lt_not_le(a, e, h1, h2)

def rz.lt_succ(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +e:
      {==}
    case 1n+ +x 0n:
      Empty.absurd({Nat.is_lt(1n+x, 1n) == True{} : Bool}, rz.ft(h))
    case 1n+ +x 1n+ +e:
      rz.lt_succ(x, e, h)

def rz.le_dbl(+q: Nat) -> {Nat.is_lt(q, 1n+Nat.double(q)) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+ +r:
      rz.lt_succ(r, 1n+Nat.double(r), rz.le_dbl(r))

def rz.lt_double(+x: Nat, +h: {Nat.is_lt(0n, x) == True{} : Bool}) -> {Nat.is_lt(x, Nat.double(x)) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, rz.ft(h))
    case 1n+ +q:
      rz.le_dbl(q)

def rz.pos_double(+x: Nat, +h: {Nat.is_lt(0n, x) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.double(x)) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, rz.ft(h))
    case 1n+ +q:
      {==}

def rz.pos_pow2(+d: Nat) -> {Nat.is_lt(0n, R.rh.pow2(d)) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+ +e:
      rz.pos_double(R.rh.pow2(e), rz.pos_pow2(e))

def rz.pow2_dbl(+d: Nat) -> {R.rh.pow2(d) == U.U32Nat.dbl(d, 1n) : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+ +e:
      Equal.cong(Nat, Nat, z => Nat.double(z), R.rh.pow2(e), U.U32Nat.dbl(e, 1n), rz.pow2_dbl(e))

def rz.sub_zero(+q: Nat) -> {Nat.sub(q, 0n) == q : Nat}:
  match q:
    case 0n:
      {==}
    case 1n+ +r:
      {==}

def rz.succ_pred(+x: Nat, +h: {Nat.is_lt(0n, x) == True{} : Bool}) -> {1n+Nat.sub(x, 1n) == x : Nat}:
  match x:
    case 0n:
      Empty.absurd({1n == 0n : Nat}, rz.ft(h))
    case 1n+ +q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.sub(q, 0n), q, rz.sub_zero(q))

def rz.le_one(+x: Nat, +h: {Nat.is_lt(0n, x) == True{} : Bool}) -> {Nat.is_le(1n, x) == True{} : Bool}:
  match x:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, rz.ft(h))
    case 1n+ +q:
      match q:
        case 0n:
          {==}
        case 1n+ +r:
          {==}

def rz.add_one(+x: Nat) -> {Nat.add(x, 1n) == 1n+x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+ +q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(q, 1n), 1n+q, rz.add_one(q))

def rz.add_succ(+x: Nat, +y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+ +q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(q, 1n+y), 1n+Nat.add(q, y), rz.add_succ(q, y))

def rz.min_le_r(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +e:
      {==}
    case 1n+ +x 0n:
      {==}
    case 1n+ +x 1n+ +e:
      rz.min_le_r(x, e)

def rz.le_succ(+x: Nat) -> {Nat.is_le(x, 1n+x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+ +q:
      rz.le_succ(q)

def rz.sub_le(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ +x 0n:
      UL.nat_le_refl(1n+x)
    case 1n+ +x 1n+ +e:
      UO.nat_le_trans(Nat.sub(x, e), x, 1n+x, rz.sub_le(x, e), rz.le_succ(x))

def rz.eq0(+d: Nat, +h: {Nat.is_eq(d, 0n) == True{} : Bool}) -> {d == 0n : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+ +e:
      Empty.absurd({1n+e == 0n : Nat}, rz.ft(h))

# ---------------------------------------------------------------- halves

# i even: (i + 1) / 2 = i / 2
def rz.ev_half(+i: Nat, +e: {Nat.is_eq(U.U32Nat.odd(i), 1n) == False{} : Bool}) -> {U.U32Nat.half(1n+i) == U.U32Nat.half(i) : Nat}:
  match i:
    case 0n:
      {==}
    case 1n+ +p:
      match p:
        case 0n:
          Empty.absurd({U.U32Nat.half(2n) == U.U32Nat.half(1n) : Nat}, rz.tf(e))
        case 1n+ +q:
          Equal.cong(Nat, Nat, z => 1n+z, U.U32Nat.half(1n+q), U.U32Nat.half(q), rz.ev_half(q, e))

# i odd: (i + 1) / 2 = i / 2 + 1
def rz.od_half(+i: Nat, +e: {Nat.is_eq(U.U32Nat.odd(i), 1n) == True{} : Bool}) -> {U.U32Nat.half(1n+i) == 1n+U.U32Nat.half(i) : Nat}:
  match i:
    case 0n:
      Empty.absurd({U.U32Nat.half(1n) == 1n : Nat}, rz.ft(e))
    case 1n+ +p:
      match p:
        case 0n:
          {==}
        case 1n+ +q:
          Equal.cong(Nat, Nat, z => 1n+z, U.U32Nat.half(1n+q), 1n+U.U32Nat.half(q), rz.od_half(q, e))

# i < 2 m gives i / 2 < m
def rz.lt_half(+i: Nat, +m: Nat, +h: {Nat.is_lt(i, Nat.double(m)) == True{} : Bool}) -> {Nat.is_lt(U.U32Nat.half(i), m) == True{} : Bool}:
  match i:
    case 0n:
      match m:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, rz.ft(h))
        case 1n+ +n:
          {==}
    case 1n+ +p:
      match p:
        case 0n:
          match m:
            case 0n:
              Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, rz.ft(h))
            case 1n+ +n:
              {==}
        case 1n+ +q:
          match m:
            case 0n:
              Empty.absurd({Nat.is_lt(1n+U.U32Nat.half(q), 0n) == True{} : Bool}, rz.ft(h))
            case 1n+ +n:
              rz.lt_half(q, n, h)

def rz.half_sd(+m: Nat) -> {U.U32Nat.half(1n+Nat.double(m)) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+ +n:
      Equal.cong(Nat, Nat, z => 1n+z, U.U32Nat.half(1n+Nat.double(n)), n, rz.half_sd(n))

# ---------------------------------------------------------------- trees

# t is a complete tree of depth d
def rz.full(~K: Data, ~V: Data, +t: R.RhTree<K, V>, +d: Nat) -> Bool:
  match t:
    case R.RhLeaf{+es}:
      Nat.is_eq(d, 0n)
    case R.RhNode{+lo, +hi}:
      match d:
        case 0n:
          False{}
        case 1n+ +e:
          Bool.and(rz.full(~K, ~V, lo, e), rz.full(~K, ~V, hi, e))

# t, of depth d, has i of its 2^d buckets taken (the module comment)
def rz.w(~K: Data, ~V: Data, +t: R.RhTree<K, V>, +d: Nat, +i: Nat) -> Bool:
  match t:
    case R.RhLeaf{+es}:
      match es:
        case Nil{}:
          Nat.is_le(i, R.rh.pow2(d))
        case Con{+x, +r}:
          Bool.and(Nat.is_eq(d, 0n), Nat.is_eq(i, 0n))
    case R.RhNode{+lo, +hi}:
      match d:
        case 0n:
          False{}
        case 1n+ +e:
          Bool.and(Nat.is_lt(i, R.rh.pow2(1n+e)), Bool.and(rz.w(~K, ~V, lo, e, U.U32Nat.half(1n+i)), rz.w(~K, ~V, hi, e, U.U32Nat.half(i))))

def rz.wtr(~K: Data, ~V: Data, -e: Nat, -x: Nat, -y: Nat, -t: R.RhTree<K, V>, +exy: {x == y : Nat}, +h: {rz.w(~K, ~V, t, e, x) == True{} : Bool}) -> {rz.w(~K, ~V, t, e, y) == True{} : Bool}:
  %exy : {rz.w(~K, ~V, t, e, _) == True{} : Bool}
  h

# all 2^d taken: one empty bucket
def rz.done(~K: Data, ~V: Data, +t: R.RhTree<K, V>, +d: Nat, +h: {rz.w(~K, ~V, t, d, R.rh.pow2(d)) == True{} : Bool}) -> {t == R.RhLeaf{Nil{}} : R.RhTree<K, V>}:
  match t:
    case R.RhLeaf{+es}:
      match es:
        case Nil{}:
          {==}
        case Con{+x, +r}:
          match d:
            case 0n:
              Empty.absurd({R.RhLeaf{Con{x, r}} == R.RhLeaf{Nil{}} : R.RhTree<K, V>}, rz.ft(h))
            case 1n+ +e:
              Empty.absurd({R.RhLeaf{Con{x, r}} == R.RhLeaf{Nil{}} : R.RhTree<K, V>}, rz.ft(h))
    case R.RhNode{+lo, +hi}:
      match d:
        case 0n:
          Empty.absurd({R.RhNode{lo, hi} == R.RhLeaf{Nil{}} : R.RhTree<K, V>}, rz.ft(h))
        case 1n+ +e:
          Empty.absurd({R.RhNode{lo, hi} == R.RhLeaf{Nil{}} : R.RhTree<K, V>}, rz.ft(Equal.trans(Bool, False{}, Nat.is_lt(R.rh.pow2(1n+e), R.rh.pow2(1n+e)), True{}, Equal.sym(Bool, Nat.is_lt(R.rh.pow2(1n+e), R.rh.pow2(1n+e)), False{}, rz.lt_irrefl(R.rh.pow2(1n+e))), rz.and_l(Nat.is_lt(R.rh.pow2(1n+e), R.rh.pow2(1n+e)), Bool.and(rz.w(~K, ~V, lo, e, U.U32Nat.half(1n+R.rh.pow2(1n+e))), rz.w(~K, ~V, hi, e, U.U32Nat.half(R.rh.pow2(1n+e)))), h))))

# a complete tree has none taken
def rz.full_w(~K: Data, ~V: Data, +t: R.RhTree<K, V>, +d: Nat, +h: {rz.full(~K, ~V, t, d) == True{} : Bool}) -> {rz.w(~K, ~V, t, d, 0n) == True{} : Bool}:
  match t:
    case R.RhLeaf{+es}:
      match es:
        case Nil{}:
          match d:
            case 0n:
              {==}
            case 1n+ +e:
              Empty.absurd({rz.w(~K, ~V, R.RhLeaf{Nil{}}, 1n+e, 0n) == True{} : Bool}, rz.ft(h))
        case Con{+x, +r}:
          match d:
            case 0n:
              {==}
            case 1n+ +e:
              Empty.absurd({rz.w(~K, ~V, R.RhLeaf{Con{x, r}}, 1n+e, 0n) == True{} : Bool}, rz.ft(h))
    case R.RhNode{+lo, +hi}:
      match d:
        case 0n:
          Empty.absurd({rz.w(~K, ~V, R.RhNode{lo, hi}, 0n, 0n) == True{} : Bool}, rz.ft(h))
        case 1n+ +e:
          rz.and2(Nat.is_lt(0n, R.rh.pow2(1n+e)), Bool.and(rz.w(~K, ~V, lo, e, 0n), rz.w(~K, ~V, hi, e, 0n)), rz.pos_pow2(1n+e), rz.and2(rz.w(~K, ~V, lo, e, 0n), rz.w(~K, ~V, hi, e, 0n), rz.full_w(~K, ~V, lo, e, rz.and_l(rz.full(~K, ~V, lo, e), rz.full(~K, ~V, hi, e), h)), rz.full_w(~K, ~V, hi, e, rz.and_r(rz.full(~K, ~V, lo, e), rz.full(~K, ~V, hi, e), h))))

def rz.full_full(~K: Data, ~V: Data, +n: Nat) -> {rz.full(~K, ~V, R.RhTree.full(~K, ~V, n), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      rz.and2(rz.full(~K, ~V, R.RhTree.full(~K, ~V, p), p), rz.full(~K, ~V, R.RhTree.full(~K, ~V, p), p), rz.full_full(~K, ~V, p), rz.full_full(~K, ~V, p))

def rz.put_full(~K: Data, ~V: Data, +t: R.RhTree<K, V>, +d: Nat, +p: List<&2, Bool>, +op: R.RhBop<K, V>, +h: {rz.full(~K, ~V, t, d) == True{} : Bool}) -> {rz.full(~K, ~V, R.RhTree.put(~K, ~V, t, p, op), d) == True{} : Bool}:
  match t:
    case R.RhLeaf{+es}:
      h
    case R.RhNode{+lo, +hi}:
      match d:
        case 0n:
          Empty.absurd({rz.full(~K, ~V, R.RhTree.put(~K, ~V, R.RhNode{lo, hi}, p, op), 0n) == True{} : Bool}, rz.ft(h))
        case 1n+ +e:
          match p:
            case Nil{}:
              rz.and2(rz.full(~K, ~V, R.RhTree.put(~K, ~V, lo, Nil{}, op), e), rz.full(~K, ~V, hi, e), rz.put_full(~K, ~V, lo, e, Nil{}, op, rz.and_l(rz.full(~K, ~V, lo, e), rz.full(~K, ~V, hi, e), h)), rz.and_r(rz.full(~K, ~V, lo, e), rz.full(~K, ~V, hi, e), h))
            case Con{+b, +ps}:
              match b:
                case True{}:
                  rz.and2(rz.full(~K, ~V, lo, e), rz.full(~K, ~V, R.RhTree.put(~K, ~V, hi, ps, op), e), rz.and_l(rz.full(~K, ~V, lo, e), rz.full(~K, ~V, hi, e), h), rz.put_full(~K, ~V, hi, e, ps, op, rz.and_r(rz.full(~K, ~V, lo, e), rz.full(~K, ~V, hi, e), h)))
                case False{}:
                  rz.and2(rz.full(~K, ~V, R.RhTree.put(~K, ~V, lo, ps, op), e), rz.full(~K, ~V, hi, e), rz.put_full(~K, ~V, lo, e, ps, op, rz.and_l(rz.full(~K, ~V, lo, e), rz.full(~K, ~V, hi, e), h)), rz.and_r(rz.full(~K, ~V, lo, e), rz.full(~K, ~V, hi, e), h))


def rz.leaf00(~K: Data, ~V: Data, +es: List<&2, R.RhEntry<K, V>>) -> {rz.w(~K, ~V, R.RhLeaf{es}, 0n, 0n) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      {==}

# a node's invariant from its halves'
def rz.pnode(~K: Data, ~V: Data, +e: Nat, +j: Nat, +a: R.RhTree<K, V>, +b: R.RhTree<K, V>, +hl: {Nat.is_lt(j, R.rh.pow2(1n+e)) == True{} : Bool}, +ha: {rz.w(~K, ~V, a, e, U.U32Nat.half(1n+j)) == True{} : Bool}, +hb: {rz.w(~K, ~V, b, e, U.U32Nat.half(j)) == True{} : Bool}) -> {rz.w(~K, ~V, R.RhNode{a, b}, 1n+e, j) == True{} : Bool}:
  rz.and2(Nat.is_lt(j, R.rh.pow2(1n+e)), Bool.and(rz.w(~K, ~V, a, e, U.U32Nat.half(1n+j)), rz.w(~K, ~V, b, e, U.U32Nat.half(j))), hl, rz.and2(rz.w(~K, ~V, a, e, U.U32Nat.half(1n+j)), rz.w(~K, ~V, b, e, U.U32Nat.half(j)), ha, hb))

# a node with j of 2^(e+1) taken, collapsed by prune when both halves are
# empty buckets
def rz.prune_w.go(~K: Data, ~V: Data, +e: Nat, +j: Nat, lt: Bool, +elt: {Nat.is_lt(j, R.rh.pow2(1n+e)) == lt : Bool}, a: R.RhTree<K, V>, b: R.RhTree<K, V>, +hj: {Nat.is_le(j, R.rh.pow2(1n+e)) == True{} : Bool}, +ha: {rz.w(~K, ~V, a, e, U.U32Nat.half(1n+j)) == True{} : Bool}, +hb: {rz.w(~K, ~V, b, e, U.U32Nat.half(j)) == True{} : Bool}) -> {rz.w(~K, ~V, R.rh.prune(~K, ~V, a, b), 1n+e, j) == True{} : Bool}:
  match lt:
    case True{}:
      match a:
        case R.RhLeaf{+x}:
          match x:
            case Nil{}:
              match b:
                case R.RhLeaf{+y}:
                  match y:
                    case Nil{}:
                      hj
                    case Con{+y1, +ys}:
                      rz.pnode(~K, ~V, e, j, R.RhLeaf{Nil{}}, R.RhLeaf{Con{y1, ys}}, elt, ha, hb)
                case R.RhNode{+c, +d}:
                  rz.pnode(~K, ~V, e, j, R.RhLeaf{Nil{}}, R.RhNode{c, d}, elt, ha, hb)
            case Con{+x1, +xs}:
              match b:
                case R.RhLeaf{+y}:
                  rz.pnode(~K, ~V, e, j, R.RhLeaf{Con{x1, xs}}, R.RhLeaf{y}, elt, ha, hb)
                case R.RhNode{+c, +d}:
                  rz.pnode(~K, ~V, e, j, R.RhLeaf{Con{x1, xs}}, R.RhNode{c, d}, elt, ha, hb)
        case R.RhNode{+c, +d}:
          rz.pnode(~K, ~V, e, j, R.RhNode{c, d}, b, elt, ha, hb)
    case False{}:
      +ej = rz.le_lt_eq(j, R.rh.pow2(1n+e), hj, elt)
      +ea = rz.done(~K, ~V, a, e, rz.wtr(~K, ~V, e, U.U32Nat.half(1n+j), R.rh.pow2(e), a, Equal.trans(Nat, U.U32Nat.half(1n+j), U.U32Nat.half(1n+R.rh.pow2(1n+e)), R.rh.pow2(e), Equal.cong(Nat, Nat, z => U.U32Nat.half(1n+z), j, R.rh.pow2(1n+e), ej), rz.half_sd(R.rh.pow2(e))), ha))
      +eb = rz.done(~K, ~V, b, e, rz.wtr(~K, ~V, e, U.U32Nat.half(j), R.rh.pow2(e), b, Equal.trans(Nat, U.U32Nat.half(j), U.U32Nat.half(R.rh.pow2(1n+e)), R.rh.pow2(e), Equal.cong(Nat, Nat, z => U.U32Nat.half(z), j, R.rh.pow2(1n+e), ej), UL.half_double(R.rh.pow2(e))), hb))
      %Equal.sym(Nat, j, R.rh.pow2(1n+e), ej) : {rz.w(~K, ~V, R.rh.prune(~K, ~V, a, b), 1n+e, _) == True{} : Bool}
      %Equal.sym(R.RhTree<K, V>, a, R.RhLeaf{Nil{}}, ea) : {rz.w(~K, ~V, R.rh.prune(~K, ~V, _, b), 1n+e, R.rh.pow2(1n+e)) == True{} : Bool}
      %Equal.sym(R.RhTree<K, V>, b, R.RhLeaf{Nil{}}, eb) : {rz.w(~K, ~V, R.rh.prune(~K, ~V, R.RhLeaf{Nil{}}, _), 1n+e, R.rh.pow2(1n+e)) == True{} : Bool}
      UL.nat_le_refl(R.rh.pow2(1n+e))

def rz.prune_w(~K: Data, ~V: Data, +e: Nat, +j: Nat, +a: R.RhTree<K, V>, +b: R.RhTree<K, V>, +hj: {Nat.is_le(j, R.rh.pow2(1n+e)) == True{} : Bool}, +ha: {rz.w(~K, ~V, a, e, U.U32Nat.half(1n+j)) == True{} : Bool}, +hb: {rz.w(~K, ~V, b, e, U.U32Nat.half(j)) == True{} : Bool}) -> {rz.w(~K, ~V, R.rh.prune(~K, ~V, a, b), 1n+e, j) == True{} : Bool}:
  rz.prune_w.go(~K, ~V, e, j, Nat.is_lt(j, R.rh.pow2(1n+e)), {==}, a, b, hj, ha, hb)

# ---------------------------------------------------------------- taking the cursor's bucket

def rz.rest(~K: Data, ~V: Data, +r: R.RhTake<K, V>) -> R.RhTree<K, V>:
  match r:
    case R.RhTake{+tp, +es, +rest}:
      rest

def rz.rest_lo(~K: Data, ~V: Data, +r: R.RhTake<K, V>, +hi: R.RhTree<K, V>) -> {rz.rest(~K, ~V, R.rh.take.lo(~K, ~V, r, hi)) == R.rh.prune(~K, ~V, rz.rest(~K, ~V, r), hi) : R.RhTree<K, V>}:
  match r:
    case R.RhTake{+tp, +es, +rest}:
      {==}

def rz.rest_hi(~K: Data, ~V: Data, +lo: R.RhTree<K, V>, +r: R.RhTake<K, V>) -> {rz.rest(~K, ~V, R.rh.take.hi(~K, ~V, lo, r)) == R.rh.prune(~K, ~V, lo, rz.rest(~K, ~V, r)) : R.RhTree<K, V>}:
  match r:
    case R.RhTake{+tp, +es, +rest}:
      {==}

# the path to bucket i of 2^d, the low bit first (rh.path on a Nat)
def rz.npath(+d: Nat, +i: Nat) -> List<&2, Bool>:
  match d:
    case 0n:
      Nil{}
    case 1n+ +e:
      Con{Nat.is_eq(U.U32Nat.odd(i), 1n), rz.npath(e, U.U32Nat.half(i))}

# taking bucket i of a tree with i taken leaves i + 1 taken; b is the low
# bit of i
def rz.take_w(~K: Data, ~V: Data, +t: R.RhTree<K, V>, +d: Nat, +i: Nat, b: Bool, +eb: {Nat.is_eq(U.U32Nat.odd(i), 1n) == b : Bool}, +hw: {rz.w(~K, ~V, t, d, i) == True{} : Bool}, +hl: {Nat.is_lt(i, R.rh.pow2(d)) == True{} : Bool}) -> {rz.w(~K, ~V, rz.rest(~K, ~V, R.rh.take(~K, ~V, t, rz.npath(d, i))), d, 1n+i) == True{} : Bool}:
  match t:
    case R.RhLeaf{+es}:
      rz.lt_le_succ(i, R.rh.pow2(d), hl)
    case R.RhNode{+lo, +hi}:
      match d:
        case 0n:
          Empty.absurd({rz.w(~K, ~V, rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, Nil{})), 0n, 1n+i) == True{} : Bool}, rz.ft(hw))
        case 1n+ +e:
          match b:
            case True{}:
              +whi = rz.and_r(rz.w(~K, ~V, lo, e, U.U32Nat.half(1n+i)), rz.w(~K, ~V, hi, e, U.U32Nat.half(i)), rz.and_r(Nat.is_lt(i, R.rh.pow2(1n+e)), Bool.and(rz.w(~K, ~V, lo, e, U.U32Nat.half(1n+i)), rz.w(~K, ~V, hi, e, U.U32Nat.half(i))), hw))
              +wlo = rz.and_l(rz.w(~K, ~V, lo, e, U.U32Nat.half(1n+i)), rz.w(~K, ~V, hi, e, U.U32Nat.half(i)), rz.and_r(Nat.is_lt(i, R.rh.pow2(1n+e)), Bool.and(rz.w(~K, ~V, lo, e, U.U32Nat.half(1n+i)), rz.w(~K, ~V, hi, e, U.U32Nat.half(i))), hw))
              +eh = rz.od_half(i, eb)
              %Equal.sym(Bool, Nat.is_eq(U.U32Nat.odd(i), 1n), True{}, eb) : {rz.w(~K, ~V, rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, Con{_, rz.npath(e, U.U32Nat.half(i))})), 1n+e, 1n+i) == True{} : Bool}
              %Equal.sym(R.RhTree<K, V>, rz.rest(~K, ~V, R.rh.take.hi(~K, ~V, lo, R.rh.take(~K, ~V, hi, rz.npath(e, U.U32Nat.half(i))))), R.rh.prune(~K, ~V, lo, rz.rest(~K, ~V, R.rh.take(~K, ~V, hi, rz.npath(e, U.U32Nat.half(i))))), rz.rest_hi(~K, ~V, lo, R.rh.take(~K, ~V, hi, rz.npath(e, U.U32Nat.half(i))))) : {rz.w(~K, ~V, _, 1n+e, 1n+i) == True{} : Bool}
              rz.prune_w(~K, ~V, e, 1n+i, lo, rz.rest(~K, ~V, R.rh.take(~K, ~V, hi, rz.npath(e, U.U32Nat.half(i)))), rz.lt_le_succ(i, R.rh.pow2(1n+e), hl), rz.wtr(~K, ~V, e, U.U32Nat.half(1n+i), 1n+U.U32Nat.half(i), lo, eh, wlo), rz.wtr(~K, ~V, e, 1n+U.U32Nat.half(i), U.U32Nat.half(1n+i), rz.rest(~K, ~V, R.rh.take(~K, ~V, hi, rz.npath(e, U.U32Nat.half(i)))), Equal.sym(Nat, U.U32Nat.half(1n+i), 1n+U.U32Nat.half(i), eh), rz.take_w(~K, ~V, hi, e, U.U32Nat.half(i), Nat.is_eq(U.U32Nat.odd(U.U32Nat.half(i)), 1n), {==}, whi, rz.lt_half(i, R.rh.pow2(e), hl))))
            case False{}:
              +whi = rz.and_r(rz.w(~K, ~V, lo, e, U.U32Nat.half(1n+i)), rz.w(~K, ~V, hi, e, U.U32Nat.half(i)), rz.and_r(Nat.is_lt(i, R.rh.pow2(1n+e)), Bool.and(rz.w(~K, ~V, lo, e, U.U32Nat.half(1n+i)), rz.w(~K, ~V, hi, e, U.U32Nat.half(i))), hw))
              +wlo = rz.and_l(rz.w(~K, ~V, lo, e, U.U32Nat.half(1n+i)), rz.w(~K, ~V, hi, e, U.U32Nat.half(i)), rz.and_r(Nat.is_lt(i, R.rh.pow2(1n+e)), Bool.and(rz.w(~K, ~V, lo, e, U.U32Nat.half(1n+i)), rz.w(~K, ~V, hi, e, U.U32Nat.half(i))), hw))
              +eh = rz.ev_half(i, eb)
              %Equal.sym(Bool, Nat.is_eq(U.U32Nat.odd(i), 1n), False{}, eb) : {rz.w(~K, ~V, rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, Con{_, rz.npath(e, U.U32Nat.half(i))})), 1n+e, 1n+i) == True{} : Bool}
              %Equal.sym(R.RhTree<K, V>, rz.rest(~K, ~V, R.rh.take.lo(~K, ~V, R.rh.take(~K, ~V, lo, rz.npath(e, U.U32Nat.half(i))), hi)), R.rh.prune(~K, ~V, rz.rest(~K, ~V, R.rh.take(~K, ~V, lo, rz.npath(e, U.U32Nat.half(i)))), hi), rz.rest_lo(~K, ~V, R.rh.take(~K, ~V, lo, rz.npath(e, U.U32Nat.half(i))), hi)) : {rz.w(~K, ~V, _, 1n+e, 1n+i) == True{} : Bool}
              rz.prune_w(~K, ~V, e, 1n+i, rz.rest(~K, ~V, R.rh.take(~K, ~V, lo, rz.npath(e, U.U32Nat.half(i)))), hi, rz.lt_le_succ(i, R.rh.pow2(1n+e), hl), rz.take_w(~K, ~V, lo, e, U.U32Nat.half(i), Nat.is_eq(U.U32Nat.odd(U.U32Nat.half(i)), 1n), {==}, rz.wtr(~K, ~V, e, U.U32Nat.half(1n+i), U.U32Nat.half(i), lo, eh, wlo), rz.lt_half(i, R.rh.pow2(e), hl)), rz.wtr(~K, ~V, e, U.U32Nat.half(i), U.U32Nat.half(1n+i), hi, Equal.sym(Nat, U.U32Nat.half(1n+i), U.U32Nat.half(i), eh), whi))

# the halves' invariants of a node's
def rz.wl(~K: Data, ~V: Data, +lo: R.RhTree<K, V>, +hi: R.RhTree<K, V>, +e: Nat, +i: Nat, +hw: {rz.w(~K, ~V, R.RhNode{lo, hi}, 1n+e, i) == True{} : Bool}) -> {rz.w(~K, ~V, lo, e, U.U32Nat.half(1n+i)) == True{} : Bool}:
  rz.and_l(rz.w(~K, ~V, lo, e, U.U32Nat.half(1n+i)), rz.w(~K, ~V, hi, e, U.U32Nat.half(i)), rz.and_r(Nat.is_lt(i, R.rh.pow2(1n+e)), Bool.and(rz.w(~K, ~V, lo, e, U.U32Nat.half(1n+i)), rz.w(~K, ~V, hi, e, U.U32Nat.half(i))), hw))

def rz.wh(~K: Data, ~V: Data, +lo: R.RhTree<K, V>, +hi: R.RhTree<K, V>, +e: Nat, +i: Nat, +hw: {rz.w(~K, ~V, R.RhNode{lo, hi}, 1n+e, i) == True{} : Bool}) -> {rz.w(~K, ~V, hi, e, U.U32Nat.half(i)) == True{} : Bool}:
  rz.and_r(rz.w(~K, ~V, lo, e, U.U32Nat.half(1n+i)), rz.w(~K, ~V, hi, e, U.U32Nat.half(i)), rz.and_r(Nat.is_lt(i, R.rh.pow2(1n+e)), Bool.and(rz.w(~K, ~V, lo, e, U.U32Nat.half(1n+i)), rz.w(~K, ~V, hi, e, U.U32Nat.half(i))), hw))

def rz.wt(~K: Data, ~V: Data, +lo: R.RhTree<K, V>, +hi: R.RhTree<K, V>, +e: Nat, +i: Nat, +hw: {rz.w(~K, ~V, R.RhNode{lo, hi}, 1n+e, i) == True{} : Bool}) -> {Nat.is_lt(i, R.rh.pow2(1n+e)) == True{} : Bool}:
  rz.and_l(Nat.is_lt(i, R.rh.pow2(1n+e)), Bool.and(rz.w(~K, ~V, lo, e, U.U32Nat.half(1n+i)), rz.w(~K, ~V, hi, e, U.U32Nat.half(i))), hw)

# a delete in the old array keeps the invariant
def rz.put_w(~K: Data, ~V: Data, +t: R.RhTree<K, V>, +d: Nat, +i: Nat, +p: List<&2, Bool>, +kw: List<&2, U32>, +hw: {rz.w(~K, ~V, t, d, i) == True{} : Bool}) -> {rz.w(~K, ~V, R.RhTree.put(~K, ~V, t, p, R.RhBDel{kw}), d, i) == True{} : Bool}:
  match t:
    case R.RhLeaf{+es}:
      match es:
        case Nil{}:
          hw
        case Con{+x, +r}:
          +ed = rz.eq0(d, rz.and_l(Nat.is_eq(d, 0n), Nat.is_eq(i, 0n), hw))
          +ei = rz.eq0(i, rz.and_r(Nat.is_eq(d, 0n), Nat.is_eq(i, 0n), hw))
          %Equal.sym(Nat, d, 0n, ed) : {rz.w(~K, ~V, R.RhLeaf{R.rh.drop(~K, ~V, kw, Con{x, r})}, _, i) == True{} : Bool}
          %Equal.sym(Nat, i, 0n, ei) : {rz.w(~K, ~V, R.RhLeaf{R.rh.drop(~K, ~V, kw, Con{x, r})}, 0n, _) == True{} : Bool}
          rz.leaf00(~K, ~V, R.rh.drop(~K, ~V, kw, Con{x, r}))
    case R.RhNode{+lo, +hi}:
      match d:
        case 0n:
          Empty.absurd({rz.w(~K, ~V, R.RhTree.put(~K, ~V, R.RhNode{lo, hi}, p, R.RhBDel{kw}), 0n, i) == True{} : Bool}, rz.ft(hw))
        case 1n+ +e:
          match p:
            case Nil{}:
              rz.pnode(~K, ~V, e, i, R.RhTree.put(~K, ~V, lo, Nil{}, R.RhBDel{kw}), hi, rz.wt(~K, ~V, lo, hi, e, i, hw), rz.put_w(~K, ~V, lo, e, U.U32Nat.half(1n+i), Nil{}, kw, rz.wl(~K, ~V, lo, hi, e, i, hw)), rz.wh(~K, ~V, lo, hi, e, i, hw))
            case Con{+c, +ps}:
              match c:
                case True{}:
                  rz.pnode(~K, ~V, e, i, lo, R.RhTree.put(~K, ~V, hi, ps, R.RhBDel{kw}), rz.wt(~K, ~V, lo, hi, e, i, hw), rz.wl(~K, ~V, lo, hi, e, i, hw), rz.put_w(~K, ~V, hi, e, U.U32Nat.half(i), ps, kw, rz.wh(~K, ~V, lo, hi, e, i, hw)))
                case False{}:
                  rz.pnode(~K, ~V, e, i, R.RhTree.put(~K, ~V, lo, ps, R.RhBDel{kw}), hi, rz.wt(~K, ~V, lo, hi, e, i, hw), rz.put_w(~K, ~V, lo, e, U.U32Nat.half(1n+i), ps, kw, rz.wl(~K, ~V, lo, hi, e, i, hw)), rz.wh(~K, ~V, lo, hi, e, i, hw))


# ---------------------------------------------------------------- the cursor

# a word's low bit, as rh.path reads it
def rz.bit(+h: U32) -> {U32.is_eq(U32.and(1, h), 1) == Nat.is_eq(U.U32Nat.odd(U32.to_nat(h)), 1n) : Bool}:
  %Equal.sym(Bool, U32.is_eq(U32.and(1, h), 1), Nat.is_eq(U32.to_nat(U32.and(1, h)), U32.to_nat(1)), UL.u32_eq_value(U32.and(1, h), 1)) : {_ == Nat.is_eq(U.U32Nat.odd(U32.to_nat(h)), 1n) : Bool}
  %UL.u32_and_comm(h, 1) : {Nat.is_eq(U32.to_nat(_), U32.to_nat(1)) == Nat.is_eq(U.U32Nat.odd(U32.to_nat(h)), 1n) : Bool}
  %Equal.sym(Nat, U32.to_nat(U32.and(h, 1)), U.U32Nat.low(1n, U32.to_nat(h)), UL.u32_and_mask(h, 1, 1n, {==})) : {Nat.is_eq(_, U32.to_nat(1)) == Nat.is_eq(U.U32Nat.odd(U32.to_nat(h)), 1n) : Bool}
  %Equal.sym(Nat, Nat.add(U.U32Nat.odd(U32.to_nat(h)), 0n), U.U32Nat.odd(U32.to_nat(h)), UL.nat_add_zero(U.U32Nat.odd(U32.to_nat(h)))) : {Nat.is_eq(_, U32.to_nat(1)) == Nat.is_eq(U.U32Nat.odd(U32.to_nat(h)), 1n) : Bool}
  {==}

# rh.path of a word is rz.npath of its value
def rz.path_nat(+d: Nat, +h: U32) -> {R.rh.path(d, h) == rz.npath(d, U32.to_nat(h)) : List<&2, Bool>}:
  match d:
    case 0n:
      {==}
    case 1n+ +e:
      %Equal.sym(Bool, U32.is_eq(U32.and(1, h), 1), Nat.is_eq(U.U32Nat.odd(U32.to_nat(h)), 1n), rz.bit(h)) : {Con{_, R.rh.path(e, U32.shr(h))} == Con{Nat.is_eq(U.U32Nat.odd(U32.to_nat(h)), 1n), rz.npath(e, U.U32Nat.half(U32.to_nat(h)))} : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, R.rh.path(e, U32.shr(h)), rz.npath(e, U32.to_nat(U32.shr(h))), rz.path_nat(e, U32.shr(h))) : {Con{Nat.is_eq(U.U32Nat.odd(U32.to_nat(h)), 1n), _} == Con{Nat.is_eq(U.U32Nat.odd(U32.to_nat(h)), 1n), rz.npath(e, U.U32Nat.half(U32.to_nat(h)))} : List<&2, Bool>}
      %Equal.sym(Nat, U32.to_nat(U32.shr(h)), U.U32Nat.half(U32.to_nat(h)), UL.u32_shr_value(h)) : {Con{Nat.is_eq(U.U32Nat.odd(U32.to_nat(h)), 1n), rz.npath(e, _)} == Con{Nat.is_eq(U.U32Nat.odd(U32.to_nat(h)), 1n), rz.npath(e, U.U32Nat.half(U32.to_nat(h)))} : List<&2, Bool>}
      {==}

# below the wrap, the next cursor is c + 1 (d <= 31: no U32 overflow)
def rz.next_val(+c: U32, +d: Nat, +hd: {Nat.is_le(d, 31n) == True{} : Bool}, +h: {Nat.is_lt(1n+U32.to_nat(c), R.rh.pow2(d)) == True{} : Bool}) -> {U32.to_nat(R.rh.next(c, d)) == 1n+U32.to_nat(c) : Nat}:
  +ep = rz.pow2_dbl(d)
  +pos = Equal.trans(Bool, Nat.is_lt(0n, U.U32Nat.dbl(d, 1n)), Nat.is_lt(0n, R.rh.pow2(d)), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(0n, z), U.U32Nat.dbl(d, 1n), R.rh.pow2(d), Equal.sym(Nat, R.rh.pow2(d), U.U32Nat.dbl(d, 1n), ep)), rz.pos_pow2(d))
  +hD = Equal.trans(Bool, Nat.is_lt(1n+U32.to_nat(c), U.U32Nat.dbl(d, 1n)), Nat.is_lt(1n+U32.to_nat(c), R.rh.pow2(d)), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(1n+U32.to_nat(c), z), U.U32Nat.dbl(d, 1n), R.rh.pow2(d), Equal.sym(Nat, R.rh.pow2(d), U.U32Nat.dbl(d, 1n), ep)), h)
  +hs = UO.nat_lt_le_trans(U.U32Nat.dbl(d, 1n), U.U32Nat.dbl(1n+d, 1n), U.U32Nat.dbl(32n, 1n), rz.lt_double(U.U32Nat.dbl(d, 1n), pos), UL.dbl_le_exp(1n+d, 32n, 1n, hd))
  +es = Equal.trans(Nat, U32.to_nat(U32.shln(1, d)), U.U32Nat.low(32n, U.U32Nat.dbl(d, U32.to_nat(1))), U.U32Nat.dbl(d, 1n), UL.u32_shln_low(1, d), UL.low_small(32n, U.U32Nat.dbl(d, 1n), hs))
  +h1 = Equal.trans(Bool, Nat.is_le(1n, U32.to_nat(U32.shln(1, d))), Nat.is_le(1n, U.U32Nat.dbl(d, 1n)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(1n, z), U32.to_nat(U32.shln(1, d)), U.U32Nat.dbl(d, 1n), es), rz.le_one(U.U32Nat.dbl(d, 1n), pos))
  +em = Equal.trans(Nat, 1n+U32.to_nat(U32.sub(U32.shln(1, d), 1)), 1n+Nat.sub(U32.to_nat(U32.shln(1, d)), U32.to_nat(1)), U.U32Nat.dbl(d, 1n), Equal.cong(Nat, Nat, z => 1n+z, U32.to_nat(U32.sub(U32.shln(1, d), 1)), Nat.sub(U32.to_nat(U32.shln(1, d)), U32.to_nat(1)), UL.u32_sub_value(U32.shln(1, d), 1, h1)), Equal.trans(Nat, 1n+Nat.sub(U32.to_nat(U32.shln(1, d)), 1n), 1n+Nat.sub(U.U32Nat.dbl(d, 1n), 1n), U.U32Nat.dbl(d, 1n), Equal.cong(Nat, Nat, z => 1n+Nat.sub(z, 1n), U32.to_nat(U32.shln(1, d)), U.U32Nat.dbl(d, 1n), es), rz.succ_pred(U.U32Nat.dbl(d, 1n), pos)))
  +hT = UO.nat_lt_trans(1n+U32.to_nat(c), U.U32Nat.dbl(d, 1n), U.U32Nat.dbl(32n, 1n), hD, hs)
  +hz = Equal.trans(Bool, Nat.is_lt(Nat.add(U32.to_nat(c), U32.to_nat(1)), U.U32Nat.dbl(32n, 1n)), Nat.is_lt(1n+U32.to_nat(c), U.U32Nat.dbl(32n, 1n)), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, U.U32Nat.dbl(32n, 1n)), Nat.add(U32.to_nat(c), U32.to_nat(1)), 1n+U32.to_nat(c), rz.add_one(U32.to_nat(c))), hT)
  +ea = Equal.trans(Nat, U32.to_nat(U32.add(c, 1)), Nat.add(U32.to_nat(c), U32.to_nat(1)), 1n+U32.to_nat(c), UL.dbl_nowrap(32n, U.U32Nat.bit(U32.is_lt(U32.add(c, 1), c)), U32.to_nat(U32.add(c, 1)), Nat.add(U32.to_nat(c), U32.to_nat(1)), Nat.add(U32.to_nat(c), U32.to_nat(1)), UL.u32_add_wrap(c, 1), UL.nat_le_refl(Nat.add(U32.to_nat(c), U32.to_nat(1))), hz), rz.add_one(U32.to_nat(c)))
  Equal.trans(Nat, U32.to_nat(U32.and(U32.add(c, 1), U32.sub(U32.shln(1, d), 1))), U.U32Nat.low(d, U32.to_nat(U32.add(c, 1))), 1n+U32.to_nat(c), UL.u32_and_mask(U32.add(c, 1), U32.sub(U32.shln(1, d), 1), d, em), Equal.trans(Nat, U.U32Nat.low(d, U32.to_nat(U32.add(c, 1))), U.U32Nat.low(d, 1n+U32.to_nat(c)), 1n+U32.to_nat(c), Equal.cong(Nat, Nat, z => U.U32Nat.low(d, z), U32.to_nat(U32.add(c, 1)), 1n+U32.to_nat(c), ea), UL.low_small(d, 1n+U32.to_nat(c), hD)))

# ---------------------------------------------------------------- the table's invariant

# the old array: one empty bucket, or c below 2^olog with c taken
def rz.oinv(~K: Data, ~V: Data, +olog: Nat, +c: U32, +ot: R.RhTree<K, V>) -> Bool:
  Bool.or(R.rh.is_empty(~K, ~V, ot), Bool.and(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, ot, olog, U32.to_nat(c))))

def rz.ctab(~K: Data, ~V: Data, +tab: R.RhTab<K, V>) -> Bool:
  match tab:
    case R.RhTab{+log, +seed, +tree}:
      Bool.and(Nat.is_le(log, 31n), rz.full(~K, ~V, tree, log))

def rz.otab(~K: Data, ~V: Data, +c: U32, +tab: R.RhTab<K, V>) -> Bool:
  match tab:
    case R.RhTab{+olog, +seed, +ot}:
      Bool.and(Nat.is_le(olog, 31n), rz.oinv(~K, ~V, olog, c, ot))

def rz.inv(~K: Data, ~V: Data, +t: R.RHash<K, V>) -> Bool:
  match t:
    case R.RHash{+p, +n, +cur, +old, +c}:
      Bool.and(rz.ctab(~K, ~V, cur), rz.otab(~K, ~V, c, old))

def rz.ctab_put(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +cur: R.RhTab<K, V>, +kw: List<&2, U32>, +op: R.RhBop<K, V>, +h: {rz.ctab(~K, ~V, cur) == True{} : Bool}) -> {rz.ctab(~K, ~V, R.RhTab.put(~K, ~V, ~hash, cur, kw, op)) == True{} : Bool}:
  match cur:
    case R.RhTab{+log, +seed, +tree}:
      rz.and2(Nat.is_le(log, 31n), rz.full(~K, ~V, R.RhTree.put(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw), op), log), rz.and_l(Nat.is_le(log, 31n), rz.full(~K, ~V, tree, log), h), rz.put_full(~K, ~V, tree, log, R.RhTab.path(~hash, log, seed, kw), op, rz.and_r(Nat.is_le(log, 31n), rz.full(~K, ~V, tree, log), h)))

def rz.oinv_del.ne(~K: Data, ~V: Data, +olog: Nat, +c: U32, +ot: R.RhTree<K, V>, +p: List<&2, Bool>, +kw: List<&2, U32>, +h: {Bool.and(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, ot, olog, U32.to_nat(c))) == True{} : Bool}) -> {rz.oinv(~K, ~V, olog, c, R.RhTree.put(~K, ~V, ot, p, R.RhBDel{kw})) == True{} : Bool}:
  rz.or_r(R.rh.is_empty(~K, ~V, R.RhTree.put(~K, ~V, ot, p, R.RhBDel{kw})), Bool.and(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, R.RhTree.put(~K, ~V, ot, p, R.RhBDel{kw}), olog, U32.to_nat(c))), rz.and2(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, R.RhTree.put(~K, ~V, ot, p, R.RhBDel{kw}), olog, U32.to_nat(c)), rz.and_l(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, ot, olog, U32.to_nat(c)), h), rz.put_w(~K, ~V, ot, olog, U32.to_nat(c), p, kw, rz.and_r(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, ot, olog, U32.to_nat(c)), h))))

def rz.oinv_del(~K: Data, ~V: Data, +olog: Nat, +c: U32, +ot: R.RhTree<K, V>, +p: List<&2, Bool>, +kw: List<&2, U32>, +h: {rz.oinv(~K, ~V, olog, c, ot) == True{} : Bool}) -> {rz.oinv(~K, ~V, olog, c, R.RhTree.put(~K, ~V, ot, p, R.RhBDel{kw})) == True{} : Bool}:
  match ot:
    case R.RhLeaf{+es}:
      match es:
        case Nil{}:
          {==}
        case Con{+x, +r}:
          rz.oinv_del.ne(~K, ~V, olog, c, R.RhLeaf{Con{x, r}}, p, kw, h)
    case R.RhNode{+lo, +hi}:
      rz.oinv_del.ne(~K, ~V, olog, c, R.RhNode{lo, hi}, p, kw, h)

def rz.otab_del(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +c: U32, +old: R.RhTab<K, V>, +kw: List<&2, U32>, +h: {rz.otab(~K, ~V, c, old) == True{} : Bool}) -> {rz.otab(~K, ~V, c, R.RhTab.put(~K, ~V, ~hash, old, kw, R.RhBDel{kw})) == True{} : Bool}:
  match old:
    case R.RhTab{+olog, +seed, +ot}:
      rz.and2(Nat.is_le(olog, 31n), rz.oinv(~K, ~V, olog, c, R.RhTree.put(~K, ~V, ot, R.RhTab.path(~hash, olog, seed, kw), R.RhBDel{kw})), rz.and_l(Nat.is_le(olog, 31n), rz.oinv(~K, ~V, olog, c, ot), h), rz.oinv_del(~K, ~V, olog, c, ot, R.RhTab.path(~hash, olog, seed, kw), kw, rz.and_r(Nat.is_le(olog, 31n), rz.oinv(~K, ~V, olog, c, ot), h)))

def rz.ins_inv(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +present: Bool, +t: R.RHash<K, V>, +kw: List<&2, U32>, +k: K, +v: V, +h: {rz.inv(~K, ~V, t) == True{} : Bool}) -> {rz.inv(~K, ~V, R.rh.ins(~K, ~V, ~hash, present, t, kw, k, v)) == True{} : Bool}:
  match t:
    case R.RHash{+p, +n, +cur, +old, +c}:
      rz.and2(rz.ctab(~K, ~V, R.RhTab.put(~K, ~V, ~hash, cur, kw, R.RhBIns{R.RhEntry{kw, k, v}})), rz.otab(~K, ~V, c, R.RhTab.put(~K, ~V, ~hash, old, kw, R.RhBDel{kw})), rz.ctab_put(~K, ~V, ~hash, cur, kw, R.RhBIns{R.RhEntry{kw, k, v}}, rz.and_l(rz.ctab(~K, ~V, cur), rz.otab(~K, ~V, c, old), h)), rz.otab_del(~K, ~V, ~hash, c, old, kw, rz.and_r(rz.ctab(~K, ~V, cur), rz.otab(~K, ~V, c, old), h)))

def rz.del_inv(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +present: Bool, +t: R.RHash<K, V>, +kw: List<&2, U32>, +h: {rz.inv(~K, ~V, t) == True{} : Bool}) -> {rz.inv(~K, ~V, R.rh.del(~K, ~V, ~hash, present, t, kw)) == True{} : Bool}:
  match t:
    case R.RHash{+p, +n, +cur, +old, +c}:
      rz.and2(rz.ctab(~K, ~V, R.RhTab.put(~K, ~V, ~hash, cur, kw, R.RhBDel{kw})), rz.otab(~K, ~V, c, R.RhTab.put(~K, ~V, ~hash, old, kw, R.RhBDel{kw})), rz.ctab_put(~K, ~V, ~hash, cur, kw, R.RhBDel{kw}, rz.and_l(rz.ctab(~K, ~V, cur), rz.otab(~K, ~V, c, old), h)), rz.otab_del(~K, ~V, ~hash, c, old, kw, rz.and_r(rz.ctab(~K, ~V, cur), rz.otab(~K, ~V, c, old), h)))

# migration only puts into the current array
def rz.mig1g_ctab(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, vis: Bool, +cur: R.RhTab<K, V>, +e: R.RhEntry<K, V>, +h: {rz.ctab(~K, ~V, cur) == True{} : Bool}) -> {rz.ctab(~K, ~V, R.rh.mig1.go(~K, ~V, ~hash, vis, cur, e)) == True{} : Bool}:
  match vis:
    case True{}:
      match e:
        case R.RhEntry{+w, +k, +v}:
          rz.ctab_put(~K, ~V, ~hash, cur, w, R.RhBApp{R.RhEntry{w, k, v}}, h)
    case False{}:
      h

def rz.mig1_ctab(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +tp: List<&2, Bool>, +olog: Nat, +oseed: U32, +cur: R.RhTab<K, V>, +e: R.RhEntry<K, V>, +h: {rz.ctab(~K, ~V, cur) == True{} : Bool}) -> {rz.ctab(~K, ~V, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, e)) == True{} : Bool}:
  match e:
    case R.RhEntry{+w, +k, +v}:
      rz.mig1g_ctab(~K, ~V, ~hash, R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, w)), cur, R.RhEntry{w, k, v}, h)

def rz.mig_ctab(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +es: List<&2, R.RhEntry<K, V>>, +tp: List<&2, Bool>, +olog: Nat, +oseed: U32, +cur: R.RhTab<K, V>, +h: {rz.ctab(~K, ~V, cur) == True{} : Bool}) -> {rz.ctab(~K, ~V, R.rh.mig(~K, ~V, ~hash, es, tp, olog, oseed, cur)) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case Con{+e, +t}:
      rz.mig_ctab(~K, ~V, ~hash, t, tp, olog, oseed, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, e), rz.mig1_ctab(~K, ~V, ~hash, tp, olog, oseed, cur, e, h))

# a step from c, past c's bucket
def rz.oinv_step.go(~K: Data, ~V: Data, +olog: Nat, +c: U32, +rt: R.RhTree<K, V>, lt: Bool, +elt: {Nat.is_lt(1n+U32.to_nat(c), R.rh.pow2(olog)) == lt : Bool}, +hlog: {Nat.is_le(olog, 31n) == True{} : Bool}, +hl: {Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)) == True{} : Bool}, +tw: {rz.w(~K, ~V, rt, olog, 1n+U32.to_nat(c)) == True{} : Bool}) -> {rz.oinv(~K, ~V, olog, R.rh.next(c, olog), rt) == True{} : Bool}:
  match lt:
    case True{}:
      +en = rz.next_val(c, olog, hlog, elt)
      rz.or_r(R.rh.is_empty(~K, ~V, rt), Bool.and(Nat.is_lt(U32.to_nat(R.rh.next(c, olog)), R.rh.pow2(olog)), rz.w(~K, ~V, rt, olog, U32.to_nat(R.rh.next(c, olog)))), rz.and2(Nat.is_lt(U32.to_nat(R.rh.next(c, olog)), R.rh.pow2(olog)), rz.w(~K, ~V, rt, olog, U32.to_nat(R.rh.next(c, olog))), Equal.trans(Bool, Nat.is_lt(U32.to_nat(R.rh.next(c, olog)), R.rh.pow2(olog)), Nat.is_lt(1n+U32.to_nat(c), R.rh.pow2(olog)), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(z, R.rh.pow2(olog)), U32.to_nat(R.rh.next(c, olog)), 1n+U32.to_nat(c), en), elt), rz.wtr(~K, ~V, olog, 1n+U32.to_nat(c), U32.to_nat(R.rh.next(c, olog)), rt, Equal.sym(Nat, U32.to_nat(R.rh.next(c, olog)), 1n+U32.to_nat(c), en), tw)))
    case False{}:
      +ej = rz.le_lt_eq(1n+U32.to_nat(c), R.rh.pow2(olog), rz.lt_le_succ(U32.to_nat(c), R.rh.pow2(olog), hl), elt)
      +er = rz.done(~K, ~V, rt, olog, rz.wtr(~K, ~V, olog, 1n+U32.to_nat(c), R.rh.pow2(olog), rt, ej, tw))
      %Equal.sym(R.RhTree<K, V>, rt, R.RhLeaf{Nil{}}, er) : {rz.oinv(~K, ~V, olog, R.rh.next(c, olog), _) == True{} : Bool}
      {==}

def rz.oinv_step(~K: Data, ~V: Data, +olog: Nat, +c: U32, +ot: R.RhTree<K, V>, +hlog: {Nat.is_le(olog, 31n) == True{} : Bool}, +h2: {Bool.and(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, ot, olog, U32.to_nat(c))) == True{} : Bool}) -> {rz.oinv(~K, ~V, olog, R.rh.next(c, olog), rz.rest(~K, ~V, R.rh.take(~K, ~V, ot, R.rh.path(olog, c)))) == True{} : Bool}:
  +hl = rz.and_l(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, ot, olog, U32.to_nat(c)), h2)
  +hw = rz.and_r(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, ot, olog, U32.to_nat(c)), h2)
  %Equal.sym(List<&2, Bool>, R.rh.path(olog, c), rz.npath(olog, U32.to_nat(c)), rz.path_nat(olog, c)) : {rz.oinv(~K, ~V, olog, R.rh.next(c, olog), rz.rest(~K, ~V, R.rh.take(~K, ~V, ot, _))) == True{} : Bool}
  rz.oinv_step.go(~K, ~V, olog, c, rz.rest(~K, ~V, R.rh.take(~K, ~V, ot, rz.npath(olog, U32.to_nat(c)))), Nat.is_lt(1n+U32.to_nat(c), R.rh.pow2(olog)), {==}, hlog, hl, rz.take_w(~K, ~V, ot, olog, U32.to_nat(c), Nat.is_eq(U.U32Nat.odd(U32.to_nat(c)), 1n), {==}, hw, hl))

def rz.tp(~K: Data, ~V: Data, +r: R.RhTake<K, V>) -> List<&2, Bool>:
  match r:
    case R.RhTake{+tp, +es, +rest}:
      tp

def rz.es(~K: Data, ~V: Data, +r: R.RhTake<K, V>) -> List<&2, R.RhEntry<K, V>>:
  match r:
    case R.RhTake{+tp, +es, +rest}:
      es

def rz.stake_eta(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +p: R.RhParams, +n: Nat, +cur: R.RhTab<K, V>, +olog: Nat, +oseed: U32, +c: U32, +r: R.RhTake<K, V>) -> {R.rh.step.take(~K, ~V, ~hash, p, n, cur, olog, oseed, c, r) == R.RHash{p, n, R.rh.mig(~K, ~V, ~hash, rz.es(~K, ~V, r), rz.tp(~K, ~V, r), olog, oseed, cur), R.RhTab{olog, oseed, rz.rest(~K, ~V, r)}, R.rh.next(c, olog)} : R.RHash<K, V>}:
  match r:
    case R.RhTake{+tp, +es, +rest}:
      {==}

def rz.stake_inv(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +p: R.RhParams, +n: Nat, +cur: R.RhTab<K, V>, +olog: Nat, +oseed: U32, +c: U32, +r: R.RhTake<K, V>, +hc: {rz.ctab(~K, ~V, cur) == True{} : Bool}, +hlog: {Nat.is_le(olog, 31n) == True{} : Bool}, +hr: {rz.oinv(~K, ~V, olog, R.rh.next(c, olog), rz.rest(~K, ~V, r)) == True{} : Bool}) -> {rz.inv(~K, ~V, R.rh.step.take(~K, ~V, ~hash, p, n, cur, olog, oseed, c, r)) == True{} : Bool}:
  match r:
    case R.RhTake{+tp, +es, +rest}:
      rz.and2(rz.ctab(~K, ~V, R.rh.mig(~K, ~V, ~hash, es, tp, olog, oseed, cur)), rz.otab(~K, ~V, R.rh.next(c, olog), R.RhTab{olog, oseed, rest}), rz.mig_ctab(~K, ~V, ~hash, es, tp, olog, oseed, cur, hc), rz.and2(Nat.is_le(olog, 31n), rz.oinv(~K, ~V, olog, R.rh.next(c, olog), rest), hlog, hr))

# a step past a bucket of a non-empty old array
def rz.step_ne(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +p: R.RhParams, +n: Nat, +cur: R.RhTab<K, V>, +olog: Nat, +oseed: U32, +ot: R.RhTree<K, V>, +c: U32, +hc: {rz.ctab(~K, ~V, cur) == True{} : Bool}, +hlog: {Nat.is_le(olog, 31n) == True{} : Bool}, +h2: {Bool.and(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, ot, olog, U32.to_nat(c))) == True{} : Bool}) -> {rz.inv(~K, ~V, R.rh.step.take(~K, ~V, ~hash, p, n, cur, olog, oseed, c, R.rh.take(~K, ~V, ot, R.rh.path(olog, c)))) == True{} : Bool}:
  rz.stake_inv(~K, ~V, ~hash, p, n, cur, olog, oseed, c, R.rh.take(~K, ~V, ot, R.rh.path(olog, c)), hc, hlog, rz.oinv_step(~K, ~V, olog, c, ot, hlog, h2))

def rz.step_inv(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +t: R.RHash<K, V>, +h: {rz.inv(~K, ~V, t) == True{} : Bool}) -> {rz.inv(~K, ~V, R.rh.step(~K, ~V, ~hash, t)) == True{} : Bool}:
  match t:
    case R.RHash{+p, +n, +cur, +old, +c}:
      match old:
        case R.RhTab{+olog, +oseed, +ot}:
          match ot:
            case R.RhLeaf{+es}:
              match es:
                case Nil{}:
                  h
                case Con{+x, +r}:
                  rz.step_ne(~K, ~V, ~hash, p, n, cur, olog, oseed, R.RhLeaf{Con{x, r}}, c, rz.and_l(rz.ctab(~K, ~V, cur), rz.otab(~K, ~V, c, R.RhTab{olog, oseed, R.RhLeaf{Con{x, r}}}), h), rz.and_l(Nat.is_le(olog, 31n), rz.oinv(~K, ~V, olog, c, R.RhLeaf{Con{x, r}}), rz.and_r(rz.ctab(~K, ~V, cur), rz.otab(~K, ~V, c, R.RhTab{olog, oseed, R.RhLeaf{Con{x, r}}}), h)), rz.and_r(Nat.is_le(olog, 31n), rz.oinv(~K, ~V, olog, c, R.RhLeaf{Con{x, r}}), rz.and_r(rz.ctab(~K, ~V, cur), rz.otab(~K, ~V, c, R.RhTab{olog, oseed, R.RhLeaf{Con{x, r}}}), h)))
            case R.RhNode{+lo, +hi}:
              rz.step_ne(~K, ~V, ~hash, p, n, cur, olog, oseed, R.RhNode{lo, hi}, c, rz.and_l(rz.ctab(~K, ~V, cur), rz.otab(~K, ~V, c, R.RhTab{olog, oseed, R.RhNode{lo, hi}}), h), rz.and_l(Nat.is_le(olog, 31n), rz.oinv(~K, ~V, olog, c, R.RhNode{lo, hi}), rz.and_r(rz.ctab(~K, ~V, cur), rz.otab(~K, ~V, c, R.RhTab{olog, oseed, R.RhNode{lo, hi}}), h)), rz.and_r(Nat.is_le(olog, 31n), rz.oinv(~K, ~V, olog, c, R.RhNode{lo, hi}), rz.and_r(rz.ctab(~K, ~V, cur), rz.otab(~K, ~V, c, R.RhTab{olog, oseed, R.RhNode{lo, hi}}), h)))

def rz.steps_inv(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +k: Nat, +t: R.RHash<K, V>, +h: {rz.inv(~K, ~V, t) == True{} : Bool}) -> {rz.inv(~K, ~V, R.rh.steps(~K, ~V, ~hash, k, t)) == True{} : Bool}:
  match k:
    case 0n:
      h
    case 1n+ +j:
      rz.steps_inv(~K, ~V, ~hash, j, R.rh.step(~K, ~V, ~hash, t), rz.step_inv(~K, ~V, ~hash, t, h))

# a resize starts from an empty old array, with the complete current one
def rz.c2o(~K: Data, ~V: Data, +cur: R.RhTab<K, V>, +h: {rz.ctab(~K, ~V, cur) == True{} : Bool}) -> {rz.otab(~K, ~V, 0, cur) == True{} : Bool}:
  match cur:
    case R.RhTab{+log, +seed, +tree}:
      rz.and2(Nat.is_le(log, 31n), rz.oinv(~K, ~V, log, 0, tree), rz.and_l(Nat.is_le(log, 31n), rz.full(~K, ~V, tree, log), h), rz.or_r(R.rh.is_empty(~K, ~V, tree), Bool.and(Nat.is_lt(0n, R.rh.pow2(log)), rz.w(~K, ~V, tree, log, 0n)), rz.and2(Nat.is_lt(0n, R.rh.pow2(log)), rz.w(~K, ~V, tree, log, 0n), rz.pos_pow2(log), rz.full_w(~K, ~V, tree, log, rz.and_r(Nat.is_le(log, 31n), rz.full(~K, ~V, tree, log), h)))))

def rz.start_go(~K: Data, ~V: Data, b: Bool, +t: R.RHash<K, V>, +l: Nat, +s: U32, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +h: {rz.inv(~K, ~V, t) == True{} : Bool}) -> {rz.inv(~K, ~V, R.rh.start.go(~K, ~V, b, t, l, s)) == True{} : Bool}:
  match b:
    case True{}:
      match t:
        case R.RHash{+p, +n, +cur, +old, +c}:
          rz.and2(rz.ctab(~K, ~V, R.RhTab.empty(~K, ~V, l, s)), rz.otab(~K, ~V, 0, cur), rz.and2(Nat.is_le(l, 31n), rz.full(~K, ~V, R.RhTree.full(~K, ~V, l), l), hl, rz.full_full(~K, ~V, l)), rz.c2o(~K, ~V, cur, rz.and_l(rz.ctab(~K, ~V, cur), rz.otab(~K, ~V, c, old), h)))
    case False{}:
      h

def rz.start_inv(~K: Data, ~V: Data, +t: R.RHash<K, V>, +l: Nat, +s: U32, +hl: {Nat.is_le(l, 31n) == True{} : Bool}, +h: {rz.inv(~K, ~V, t) == True{} : Bool}) -> {rz.inv(~K, ~V, R.rh.start(~K, ~V, t, l, s)) == True{} : Bool}:
  rz.start_go(~K, ~V, R.rh.idle(~K, ~V, t), t, l, s, hl, h)

# the policy asks only for sizes up to 31
def rz.mle(+w: Maybe<&2, Nat>) -> Bool:
  match w:
    case None{}:
      True{}
    case Some{+l}:
      Nat.is_le(l, 31n)

def rz.wgo(+log: Nat, +mx: Nat, +x: Bool, g: Bool, +eg: {Bool.and(Nat.is_lt(log, R.rh.clamp(mx)), x) == g : Bool}, sh: Bool, +hlog: {Nat.is_le(log, 31n) == True{} : Bool}) -> {rz.mle(R.rh.want.go(g, sh, log)) == True{} : Bool}:
  match g:
    case True{}:
      UO.nat_le_trans(1n+log, R.rh.clamp(mx), 31n, rz.lt_le_succ(log, R.rh.clamp(mx), rz.and_l(Nat.is_lt(log, R.rh.clamp(mx)), x, eg)), rz.min_le_r(mx, 31n))
    case False{}:
      match sh:
        case True{}:
          UO.nat_le_trans(Nat.sub(log, 1n), log, 31n, rz.sub_le(log, 1n), hlog)
        case False{}:
          {==}

def rz.want_mle(+p: R.RhParams, +n: Nat, +log: Nat, +hlog: {Nat.is_le(log, 31n) == True{} : Bool}) -> {rz.mle(R.rh.want(p, n, log)) == True{} : Bool}:
  match p:
    case R.RhParams{+gp, +sp, +au, +minl, +maxl, +il, +st, +s0, +ss}:
      rz.wgo(log, maxl, Nat.is_lt(Nat.mul(gp, R.rh.pow2(log)), Nat.mul(n, 100n)), Bool.and(Nat.is_lt(log, R.rh.clamp(maxl)), Nat.is_lt(Nat.mul(gp, R.rh.pow2(log)), Nat.mul(n, 100n))), {==}, Bool.and(au, Bool.and(Nat.is_lt(minl, log), Nat.is_lt(Nat.mul(n, 100n), Nat.mul(sp, R.rh.pow2(log))))), hlog)

def rz.auto_go(~K: Data, ~V: Data, w: Maybe<&2, Nat>, +hw: {rz.mle(w) == True{} : Bool}, +t: R.RHash<K, V>, +s: U32, +h: {rz.inv(~K, ~V, t) == True{} : Bool}) -> {rz.inv(~K, ~V, R.rh.auto.go(~K, ~V, w, t, s)) == True{} : Bool}:
  match w:
    case None{}:
      h
    case Some{+l}:
      rz.start_inv(~K, ~V, t, l, s, hw, h)

def rz.auto_inv(~K: Data, ~V: Data, +t: R.RHash<K, V>, +h: {rz.inv(~K, ~V, t) == True{} : Bool}) -> {rz.inv(~K, ~V, R.rh.auto(~K, ~V, t)) == True{} : Bool}:
  match t:
    case R.RHash{+p, +n, +cur, +old, +c}:
      match cur:
        case R.RhTab{+log, +seed, +tree}:
          rz.auto_go(~K, ~V, R.rh.want(p, n, log), rz.want_mle(p, n, log, rz.and_l(Nat.is_le(log, 31n), rz.full(~K, ~V, tree, log), rz.and_l(rz.ctab(~K, ~V, R.RhTab{log, seed, tree}), rz.otab(~K, ~V, c, old), h))), R.RHash{p, n, R.RhTab{log, seed, tree}, old, c}, U32.add(seed, R.rh.seed_step(p)), h)

def rz.after_inv(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +t: R.RHash<K, V>, +h: {rz.inv(~K, ~V, t) == True{} : Bool}) -> {rz.inv(~K, ~V, R.rh.after(~K, ~V, ~hash, t)) == True{} : Bool}:
  match t:
    case R.RHash{+p, +n, +cur, +old, +c}:
      rz.auto_inv(~K, ~V, R.rh.steps(~K, ~V, ~hash, R.rh.nsteps(p), R.RHash{p, n, cur, old, c}), rz.steps_inv(~K, ~V, ~hash, R.rh.nsteps(p), R.RHash{p, n, cur, old, c}, h))

# ---------------------------------------------------------------- tables built through the interface

def rz.new_inv(~K: Data, ~V: Data, +p: R.RhParams) -> {rz.inv(~K, ~V, R.RHash.new(~K, ~V, p)) == True{} : Bool}:
  match p:
    case R.RhParams{+gp, +sp, +au, +mn, +mx, +il, +st, +s0, +ss}:
      rz.and2(rz.ctab(~K, ~V, R.RhTab.empty(~K, ~V, R.rh.clamp(il), s0)), rz.otab(~K, ~V, 0, R.RhTab{0n, s0, R.RhLeaf{Nil{}}}), rz.and2(Nat.is_le(R.rh.clamp(il), 31n), rz.full(~K, ~V, R.RhTree.full(~K, ~V, R.rh.clamp(il)), R.rh.clamp(il)), rz.min_le_r(il, 31n), rz.full_full(~K, ~V, R.rh.clamp(il))), {==})

def rz.apply_inv(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, +t: R.RHash<K, V>, +op: R.RhOp<K, V>, +h: {rz.inv(~K, ~V, t) == True{} : Bool}) -> {rz.inv(~K, ~V, R.RHash.apply(~K, ~V, ~kenc, ~hash, t, op)) == True{} : Bool}:
  match op:
    case R.RhIns{+k, +v}:
      rz.after_inv(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), k, v), rz.ins_inv(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), k, v, h))
    case R.RhDel{+k}:
      rz.after_inv(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k)), rz.del_inv(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), h))
    case R.RhStep{}:
      rz.step_inv(~K, ~V, ~hash, t, h)
    case R.RhResize{+log, +seed}:
      rz.start_inv(~K, ~V, R.RHash.drain(~K, ~V, ~hash, t), R.rh.clamp(log), seed, rz.min_le_r(log, 31n), rz.steps_inv(~K, ~V, ~hash, R.rh.pow2(R.rh.old_log(~K, ~V, t)), t, h))

def rz.replay_inv(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, +p: R.RhParams, +tr: List<&2, R.RhOp<K, V>>) -> {rz.inv(~K, ~V, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, tr)) == True{} : Bool}:
  match tr:
    case Nil{}:
      rz.new_inv(~K, ~V, p)
    case Con{+op, +older}:
      rz.apply_inv(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), op, rz.replay_inv(~K, ~V, ~kenc, ~hash, p, older))

# ---------------------------------------------------------------- the drain

def rz.steps_empty(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +k: Nat, +p: R.RhParams, +n: Nat, +cur: R.RhTab<K, V>, +olog: Nat, +oseed: U32, +c: U32) -> {R.rh.steps(~K, ~V, ~hash, k, R.RHash{p, n, cur, R.RhTab{olog, oseed, R.RhLeaf{Nil{}}}, c}) == R.RHash{p, n, cur, R.RhTab{olog, oseed, R.RhLeaf{Nil{}}}, c} : R.RHash<K, V>}:
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      rz.steps_empty(~K, ~V, ~hash, j, p, n, cur, olog, oseed, c)

# from c with c taken, k >= 2^olog - c steps empty the old array; b says
# whether c + 1 is below 2^olog
def rz.steps_idle(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +k: Nat, +p: R.RhParams, +n: Nat, +cur: R.RhTab<K, V>, +olog: Nat, +oseed: U32, +ot: R.RhTree<K, V>, +c: U32, b: Bool, +eb: {Nat.is_lt(1n+U32.to_nat(c), R.rh.pow2(olog)) == b : Bool}, +hc: {rz.ctab(~K, ~V, cur) == True{} : Bool}, +hlog: {Nat.is_le(olog, 31n) == True{} : Bool}, +ho: {rz.oinv(~K, ~V, olog, c, ot) == True{} : Bool}, +hk: {Nat.is_le(R.rh.pow2(olog), Nat.add(k, U32.to_nat(c))) == True{} : Bool}) -> {R.rh.idle(~K, ~V, R.rh.steps(~K, ~V, ~hash, k, R.RHash{p, n, cur, R.RhTab{olog, oseed, ot}, c})) == True{} : Bool}:
  match k:
    case 0n:
      match ot:
        case R.RhLeaf{+es}:
          match es:
            case Nil{}:
              {==}
            case Con{+x, +r}:
              Empty.absurd({R.rh.idle(~K, ~V, R.rh.steps(~K, ~V, ~hash, 0n, R.RHash{p, n, cur, R.RhTab{olog, oseed, R.RhLeaf{Con{x, r}}}, c})) == True{} : Bool}, rz.lt_not_le(U32.to_nat(c), R.rh.pow2(olog), rz.and_l(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, R.RhLeaf{Con{x, r}}, olog, U32.to_nat(c)), ho), hk))
        case R.RhNode{+lo, +hi}:
          Empty.absurd({R.rh.idle(~K, ~V, R.rh.steps(~K, ~V, ~hash, 0n, R.RHash{p, n, cur, R.RhTab{olog, oseed, R.RhNode{lo, hi}}, c})) == True{} : Bool}, rz.lt_not_le(U32.to_nat(c), R.rh.pow2(olog), rz.and_l(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, R.RhNode{lo, hi}, olog, U32.to_nat(c)), ho), hk))
    case 1n+ +j:
      match ot:
        case R.RhLeaf{+es}:
          match es:
            case Nil{}:
              %Equal.sym(R.RHash<K, V>, R.rh.steps(~K, ~V, ~hash, 1n+j, R.RHash{p, n, cur, R.RhTab{olog, oseed, R.RhLeaf{Nil{}}}, c}), R.RHash{p, n, cur, R.RhTab{olog, oseed, R.RhLeaf{Nil{}}}, c}, rz.steps_empty(~K, ~V, ~hash, 1n+j, p, n, cur, olog, oseed, c)) : {R.rh.idle(~K, ~V, _) == True{} : Bool}
              {==}
            case Con{+x, +r}:
              match b:
                case True{}:
                  +en = rz.next_val(c, olog, hlog, eb)
                  +hk2 = Equal.trans(Bool, Nat.is_le(R.rh.pow2(olog), Nat.add(j, U32.to_nat(R.rh.next(c, olog)))), Nat.is_le(R.rh.pow2(olog), Nat.add(j, 1n+U32.to_nat(c))), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(R.rh.pow2(olog), Nat.add(j, z)), U32.to_nat(R.rh.next(c, olog)), 1n+U32.to_nat(c), en), Equal.trans(Bool, Nat.is_le(R.rh.pow2(olog), Nat.add(j, 1n+U32.to_nat(c))), Nat.is_le(R.rh.pow2(olog), 1n+Nat.add(j, U32.to_nat(c))), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(R.rh.pow2(olog), z), Nat.add(j, 1n+U32.to_nat(c)), 1n+Nat.add(j, U32.to_nat(c)), rz.add_succ(j, U32.to_nat(c))), hk))
                  %Equal.sym(R.RHash<K, V>, R.rh.step.take(~K, ~V, ~hash, p, n, cur, olog, oseed, c, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), R.RHash{p, n, R.rh.mig(~K, ~V, ~hash, rz.es(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), rz.tp(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), olog, oseed, cur), R.RhTab{olog, oseed, rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c)))}, R.rh.next(c, olog)}, rz.stake_eta(~K, ~V, ~hash, p, n, cur, olog, oseed, c, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c)))) : {R.rh.idle(~K, ~V, R.rh.steps(~K, ~V, ~hash, j, _)) == True{} : Bool}
                  rz.steps_idle(~K, ~V, ~hash, j, p, n, R.rh.mig(~K, ~V, ~hash, rz.es(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), rz.tp(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), olog, oseed, cur), olog, oseed, rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), R.rh.next(c, olog), Nat.is_lt(1n+U32.to_nat(R.rh.next(c, olog)), R.rh.pow2(olog)), {==}, rz.mig_ctab(~K, ~V, ~hash, rz.es(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), rz.tp(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), olog, oseed, cur, hc), hlog, rz.oinv_step(~K, ~V, olog, c, R.RhLeaf{Con{x, r}}, hlog, ho), hk2)
                case False{}:
                  +ej = rz.le_lt_eq(1n+U32.to_nat(c), R.rh.pow2(olog), rz.lt_le_succ(U32.to_nat(c), R.rh.pow2(olog), rz.and_l(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, R.RhLeaf{Con{x, r}}, olog, U32.to_nat(c)), ho)), eb)
                  +tw = rz.take_w(~K, ~V, R.RhLeaf{Con{x, r}}, olog, U32.to_nat(c), Nat.is_eq(U.U32Nat.odd(U32.to_nat(c)), 1n), {==}, rz.and_r(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, R.RhLeaf{Con{x, r}}, olog, U32.to_nat(c)), ho), rz.and_l(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, R.RhLeaf{Con{x, r}}, olog, U32.to_nat(c)), ho))
                  +er1 = rz.done(~K, ~V, rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, rz.npath(olog, U32.to_nat(c)))), olog, rz.wtr(~K, ~V, olog, 1n+U32.to_nat(c), R.rh.pow2(olog), rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, rz.npath(olog, U32.to_nat(c)))), ej, tw))
                  +er = Equal.trans(R.RhTree<K, V>, rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, rz.npath(olog, U32.to_nat(c)))), R.RhLeaf{Nil{}}, Equal.cong(List<&2, Bool>, R.RhTree<K, V>, z => rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, z)), R.rh.path(olog, c), rz.npath(olog, U32.to_nat(c)), rz.path_nat(olog, c)), er1)
                  %Equal.sym(R.RHash<K, V>, R.rh.step.take(~K, ~V, ~hash, p, n, cur, olog, oseed, c, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), R.RHash{p, n, R.rh.mig(~K, ~V, ~hash, rz.es(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), rz.tp(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), olog, oseed, cur), R.RhTab{olog, oseed, rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c)))}, R.rh.next(c, olog)}, rz.stake_eta(~K, ~V, ~hash, p, n, cur, olog, oseed, c, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c)))) : {R.rh.idle(~K, ~V, R.rh.steps(~K, ~V, ~hash, j, _)) == True{} : Bool}
                  %Equal.sym(R.RhTree<K, V>, rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), R.RhLeaf{Nil{}}, er) : {R.rh.idle(~K, ~V, R.rh.steps(~K, ~V, ~hash, j, R.RHash{p, n, R.rh.mig(~K, ~V, ~hash, rz.es(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), rz.tp(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), olog, oseed, cur), R.RhTab{olog, oseed, _}, R.rh.next(c, olog)})) == True{} : Bool}
                  %Equal.sym(R.RHash<K, V>, R.rh.steps(~K, ~V, ~hash, j, R.RHash{p, n, R.rh.mig(~K, ~V, ~hash, rz.es(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), rz.tp(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), olog, oseed, cur), R.RhTab{olog, oseed, R.RhLeaf{Nil{}}}, R.rh.next(c, olog)}), R.RHash{p, n, R.rh.mig(~K, ~V, ~hash, rz.es(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), rz.tp(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), olog, oseed, cur), R.RhTab{olog, oseed, R.RhLeaf{Nil{}}}, R.rh.next(c, olog)}, rz.steps_empty(~K, ~V, ~hash, j, p, n, R.rh.mig(~K, ~V, ~hash, rz.es(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), rz.tp(~K, ~V, R.rh.take(~K, ~V, R.RhLeaf{Con{x, r}}, R.rh.path(olog, c))), olog, oseed, cur), olog, oseed, R.rh.next(c, olog))) : {R.rh.idle(~K, ~V, _) == True{} : Bool}
                  {==}
        case R.RhNode{+lo, +hi}:
          match b:
            case True{}:
              +en = rz.next_val(c, olog, hlog, eb)
              +hk2 = Equal.trans(Bool, Nat.is_le(R.rh.pow2(olog), Nat.add(j, U32.to_nat(R.rh.next(c, olog)))), Nat.is_le(R.rh.pow2(olog), Nat.add(j, 1n+U32.to_nat(c))), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(R.rh.pow2(olog), Nat.add(j, z)), U32.to_nat(R.rh.next(c, olog)), 1n+U32.to_nat(c), en), Equal.trans(Bool, Nat.is_le(R.rh.pow2(olog), Nat.add(j, 1n+U32.to_nat(c))), Nat.is_le(R.rh.pow2(olog), 1n+Nat.add(j, U32.to_nat(c))), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(R.rh.pow2(olog), z), Nat.add(j, 1n+U32.to_nat(c)), 1n+Nat.add(j, U32.to_nat(c)), rz.add_succ(j, U32.to_nat(c))), hk))
              %Equal.sym(R.RHash<K, V>, R.rh.step.take(~K, ~V, ~hash, p, n, cur, olog, oseed, c, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), R.RHash{p, n, R.rh.mig(~K, ~V, ~hash, rz.es(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), rz.tp(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), olog, oseed, cur), R.RhTab{olog, oseed, rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c)))}, R.rh.next(c, olog)}, rz.stake_eta(~K, ~V, ~hash, p, n, cur, olog, oseed, c, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c)))) : {R.rh.idle(~K, ~V, R.rh.steps(~K, ~V, ~hash, j, _)) == True{} : Bool}
              rz.steps_idle(~K, ~V, ~hash, j, p, n, R.rh.mig(~K, ~V, ~hash, rz.es(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), rz.tp(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), olog, oseed, cur), olog, oseed, rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), R.rh.next(c, olog), Nat.is_lt(1n+U32.to_nat(R.rh.next(c, olog)), R.rh.pow2(olog)), {==}, rz.mig_ctab(~K, ~V, ~hash, rz.es(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), rz.tp(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), olog, oseed, cur, hc), hlog, rz.oinv_step(~K, ~V, olog, c, R.RhNode{lo, hi}, hlog, ho), hk2)
            case False{}:
              +ej = rz.le_lt_eq(1n+U32.to_nat(c), R.rh.pow2(olog), rz.lt_le_succ(U32.to_nat(c), R.rh.pow2(olog), rz.and_l(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, R.RhNode{lo, hi}, olog, U32.to_nat(c)), ho)), eb)
              +tw = rz.take_w(~K, ~V, R.RhNode{lo, hi}, olog, U32.to_nat(c), Nat.is_eq(U.U32Nat.odd(U32.to_nat(c)), 1n), {==}, rz.and_r(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, R.RhNode{lo, hi}, olog, U32.to_nat(c)), ho), rz.and_l(Nat.is_lt(U32.to_nat(c), R.rh.pow2(olog)), rz.w(~K, ~V, R.RhNode{lo, hi}, olog, U32.to_nat(c)), ho))
              +er1 = rz.done(~K, ~V, rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, rz.npath(olog, U32.to_nat(c)))), olog, rz.wtr(~K, ~V, olog, 1n+U32.to_nat(c), R.rh.pow2(olog), rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, rz.npath(olog, U32.to_nat(c)))), ej, tw))
              +er = Equal.trans(R.RhTree<K, V>, rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, rz.npath(olog, U32.to_nat(c)))), R.RhLeaf{Nil{}}, Equal.cong(List<&2, Bool>, R.RhTree<K, V>, z => rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, z)), R.rh.path(olog, c), rz.npath(olog, U32.to_nat(c)), rz.path_nat(olog, c)), er1)
              %Equal.sym(R.RHash<K, V>, R.rh.step.take(~K, ~V, ~hash, p, n, cur, olog, oseed, c, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), R.RHash{p, n, R.rh.mig(~K, ~V, ~hash, rz.es(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), rz.tp(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), olog, oseed, cur), R.RhTab{olog, oseed, rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c)))}, R.rh.next(c, olog)}, rz.stake_eta(~K, ~V, ~hash, p, n, cur, olog, oseed, c, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c)))) : {R.rh.idle(~K, ~V, R.rh.steps(~K, ~V, ~hash, j, _)) == True{} : Bool}
              %Equal.sym(R.RhTree<K, V>, rz.rest(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), R.RhLeaf{Nil{}}, er) : {R.rh.idle(~K, ~V, R.rh.steps(~K, ~V, ~hash, j, R.RHash{p, n, R.rh.mig(~K, ~V, ~hash, rz.es(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), rz.tp(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), olog, oseed, cur), R.RhTab{olog, oseed, _}, R.rh.next(c, olog)})) == True{} : Bool}
              %Equal.sym(R.RHash<K, V>, R.rh.steps(~K, ~V, ~hash, j, R.RHash{p, n, R.rh.mig(~K, ~V, ~hash, rz.es(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), rz.tp(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), olog, oseed, cur), R.RhTab{olog, oseed, R.RhLeaf{Nil{}}}, R.rh.next(c, olog)}), R.RHash{p, n, R.rh.mig(~K, ~V, ~hash, rz.es(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), rz.tp(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), olog, oseed, cur), R.RhTab{olog, oseed, R.RhLeaf{Nil{}}}, R.rh.next(c, olog)}, rz.steps_empty(~K, ~V, ~hash, j, p, n, R.rh.mig(~K, ~V, ~hash, rz.es(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), rz.tp(~K, ~V, R.rh.take(~K, ~V, R.RhNode{lo, hi}, R.rh.path(olog, c))), olog, oseed, cur), olog, oseed, R.rh.next(c, olog))) : {R.rh.idle(~K, ~V, _) == True{} : Bool}
              {==}

def rz.drain_idle(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +t: R.RHash<K, V>, +h: {rz.inv(~K, ~V, t) == True{} : Bool}) -> {R.rh.idle(~K, ~V, R.RHash.drain(~K, ~V, ~hash, t)) == True{} : Bool}:
  match t:
    case R.RHash{+p, +n, +cur, +old, +c}:
      match old:
        case R.RhTab{+olog, +oseed, +ot}:
          rz.steps_idle(~K, ~V, ~hash, R.rh.pow2(olog), p, n, cur, olog, oseed, ot, c, Nat.is_lt(1n+U32.to_nat(c), R.rh.pow2(olog)), {==}, rz.and_l(rz.ctab(~K, ~V, cur), rz.otab(~K, ~V, c, R.RhTab{olog, oseed, ot}), h), rz.and_l(Nat.is_le(olog, 31n), rz.oinv(~K, ~V, olog, c, ot), rz.and_r(rz.ctab(~K, ~V, cur), rz.otab(~K, ~V, c, R.RhTab{olog, oseed, ot}), h)), rz.and_r(Nat.is_le(olog, 31n), rz.oinv(~K, ~V, olog, c, ot), rz.and_r(rz.ctab(~K, ~V, cur), rz.otab(~K, ~V, c, R.RhTab{olog, oseed, ot}), h)), UO.nat_le_add_r(R.rh.pow2(olog), U32.to_nat(c)))

# ---------------------------------------------------------------- the law

def Laws.drain_finishes(K, V, kenc, hash, p, tr):
  %Equal.sym(Bool, R.rh.idle(~K, ~V, R.RHash.drain(~K, ~V, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, tr))), True{}, rz.drain_idle(~K, ~V, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, tr), rz.replay_inv(~K, ~V, ~kenc, ~hash, p, tr))) : {Bool.not(_) == False{} : Bool}
  {==}
