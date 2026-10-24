# Proof helpers for bend-osdev-maple: every node but the root stays between
# half full and full (the fill bounds of Maple.balanced), and every
# operation keeps a tree's order.
#
# Notation: o is the tree's order (at least 3), L = half(o + 1) the fewest
# items a node other than the root holds. A full node of height h (fnode)
# is a leaf of L to o entries (h = 0), or a chain of L to o slots whose
# children are full nodes of height h - 1; shape(n, h) is a chain of full
# nodes of height h; a weak node of height h (wn) is a leaf, or a chain of
# full nodes of height h - 1, of any count.
#
# * fit: a weak node of L to 2o items becomes a chain of one or two full
#   nodes (two halves, of half(k) and half(k + 1) items, when it holds
#   k > o); one of at most 2o items, normalised as a root, is a root of 2
#   to o slots or a leaf of at most o entries.
# * Joining two trees merges the shorter's root into the taller's edge at
#   the shorter's height (a full node and at most o more items), and each
#   level on the way back gains at most one slot, so every node fit splits
#   holds o + 1 to 2o items; the root ends with 2 to o slots.
# * Cutting below or above an index joins trees made of the original
#   tree's nodes (a chain of the slots before the path, normalised as a
#   root) and leaves of no more entries than before.
import Base
import ./model.bend as M
import ./node.bend as N
import ./tree.bend as T
import ./maple.bend as X

# Contradictions and Bool

def ab.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def ab.ft(+e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : ab.bool(_)
  Unit{}

def ab.tf(+e: {True{} == False{} : Bool}) -> Empty:
  %e : ab.bool(_)
  Unit{}

def ab.isz(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def ab.succ_zero(-j: Nat, +e: {1n+j == 0n : Nat}) -> Empty:
  %e : ab.isz(_)
  Unit{}

def ab.some(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case Some{x}:
      Unit
    case None{}:
      Empty

def ab.some_none(-A: Data, -x: A, +e: {Some{x} == None{} : Maybe<&2, A>}) -> Empty:
  %e : ab.some(A, _)
  Unit{}

def bo.and_l(x: Bool, -y: Bool, +e: {Bool.and(x, y) == True{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ab.ft(e))

def bo.and_r(x: Bool, -y: Bool, +e: {Bool.and(x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      e
    case False{}:
      Empty.absurd({y == True{} : Bool}, ab.ft(e))

def bo.and_intro(-x: Bool, -y: Bool, +ex: {x == True{} : Bool}, +ey: {y == True{} : Bool}) -> {Bool.and(x, y) == True{} : Bool}:
  %Equal.sym(Bool, x, True{}, ex) : {Bool.and(_, y) == True{} : Bool}
  ey

def bo.or_true_l(x: Bool, -y: Bool, +e: {x == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({y == True{} : Bool}, ab.ft(e))

def bo.or_true_r(x: Bool, -y: Bool, +e: {y == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      e

def bo.or_false_l(x: Bool, -y: Bool, +ex: {x == False{} : Bool}, +e: {Bool.or(x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({y == True{} : Bool}, ab.tf(ex))
    case False{}:
      e

# Nat

def nt.succ_eq(-a: Nat, -b: Nat, +e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def nt.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def nt.succ_inj(-a: Nat, -b: Nat, +e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  %e : {nt.pred(1n+a) == nt.pred(_) : Nat}
  {==}

def nt.eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      nt.eq_refl(p)

def nt.eq_of(+a: Nat, +b: Nat, +e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({0n == 1n+q : Nat}, ab.ft(e))
    case 1n+(+p):
      match b:
        case 0n:
          Empty.absurd({1n+p == 0n : Nat}, ab.ft(e))
        case 1n+(+q):
          nt.succ_eq(p, q, nt.eq_of(p, q, e))

def nt.le_refl(+a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      nt.le_refl(p)

def nt.le_zero(+a: Nat) -> {Nat.is_le(0n, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nt.le_trans(+a: Nat, +b: Nat, +c: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a:
    case 0n:
      nt.le_zero(c)
    case 1n+(+p):
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, ab.ft(h1))
        case 1n+(+q):
          match c:
            case 0n:
              Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, ab.ft(h2))
            case 1n+(+r):
              nt.le_trans(p, q, r, h1, h2)

def nt.le_succ(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, ab.ft(h))
        case 1n+(+q):
          nt.le_succ(p, q, h)

# a <= b, as a rewriting of either side
def nt.le_rw_l(-a: Nat, -b: Nat, -c: Nat, +e: {a == b : Nat}, +h: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Nat.is_le(_, c) == True{} : Bool}
  h

def nt.le_rw_r(-a: Nat, -b: Nat, -c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}, +e: {b == c : Nat}) -> {Nat.is_le(a, c) == True{} : Bool}:
  %e : {Nat.is_le(a, _) == True{} : Bool}
  h

def nt.add_zero(+a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      nt.succ_eq(Nat.add(p, 0n), p, nt.add_zero(p))

def nt.add_succ(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      nt.succ_eq(Nat.add(p, 1n+b), 1n+Nat.add(p, b), nt.add_succ(p, b))

def nt.add_one(+a: Nat) -> {Nat.add(a, 1n) == 1n+a : Nat}:
  Equal.trans(Nat, Nat.add(a, 1n), 1n+Nat.add(a, 0n), 1n+a, nt.add_succ(a, 0n), nt.succ_eq(Nat.add(a, 0n), a, nt.add_zero(a)))

def nt.add_two(+a: Nat) -> {Nat.add(a, 2n) == 2n+a : Nat}:
  Equal.trans(Nat, Nat.add(a, 2n), 1n+Nat.add(a, 1n), 2n+a, nt.add_succ(a, 1n), nt.succ_eq(Nat.add(a, 1n), 1n+a, nt.add_one(a)))

def nt.add_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      nt.succ_eq(Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), nt.add_assoc(p, b, c))

def nt.add_cong_l(-x: Nat, -y: Nat, -z: Nat, +e: {x == y : Nat}) -> {Nat.add(x, z) == Nat.add(y, z) : Nat}:
  %e : {Nat.add(x, z) == Nat.add(_, z) : Nat}
  {==}

def nt.add_cancel(+a: Nat, -b: Nat, -c: Nat, +e: {Nat.add(a, b) == Nat.add(a, c) : Nat}) -> {b == c : Nat}:
  match a:
    case 0n:
      e
    case 1n+(+p):
      nt.add_cancel(p, b, c, nt.succ_inj(Nat.add(p, b), Nat.add(p, c), e))

def nt.add_dbl(+a: Nat) -> {Nat.add(a, a) == Nat.double(a) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      nt.succ_eq(Nat.add(p, 1n+p), 1n+Nat.double(p), Equal.trans(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), 1n+Nat.double(p), nt.add_succ(p, p), nt.succ_eq(Nat.add(p, p), Nat.double(p), nt.add_dbl(p))))

def nt.le_add_r(+a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      nt.le_zero(b)
    case 1n+(+p):
      nt.le_add_r(p, b)

def nt.le_add_l(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      nt.le_refl(b)
    case 1n+(+p):
      nt.le_succ(b, Nat.add(p, b), nt.le_add_l(p, b))

def nt.le_add_mono(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +h1: {Nat.is_le(a, c) == True{} : Bool}, +h2: {Nat.is_le(b, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), Nat.add(c, d)) == True{} : Bool}:
  match a:
    case 0n:
      nt.le_trans(b, d, Nat.add(c, d), h2, nt.le_add_l(c, d))
    case 1n+(+p):
      match c:
        case 0n:
          Empty.absurd({Nat.is_le(Nat.add(1n+p, b), Nat.add(0n, d)) == True{} : Bool}, ab.ft(h1))
        case 1n+(+q):
          nt.le_add_mono(p, b, q, d, h1, h2)

def nt.le_double(+a: Nat) -> {Nat.is_le(a, Nat.double(a)) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      nt.le_succ(p, Nat.double(p), nt.le_double(p))

def nt.succ_le_double(+a: Nat, +h: {Nat.is_le(1n, a) == True{} : Bool}) -> {Nat.is_le(1n+a, Nat.double(a)) == True{} : Bool}:
  match a:
    case 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, ab.ft(h))
    case 1n+(+p):
      nt.le_double(p)

# a < b is a + 1 <= b
def nt.lt_le(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, ab.ft(h))
        case 1n+(+q):
          nt.le_zero(q)
    case 1n+(+p):
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(2n+p, 0n) == True{} : Bool}, ab.ft(h))
        case 1n+(+q):
          nt.lt_le(p, q, h)

def nt.lt_to_le(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  nt.le_trans(a, 1n+a, b, nt.le_succ(a, a, nt.le_refl(a)), nt.lt_le(a, b, h))

# not a < b is b <= a
def nt.not_lt(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, ab.tf(h))
    case 1n+(+p):
      match b:
        case 0n:
          {==}
        case 1n+(+q):
          nt.not_lt(p, q, h)

# not a <= b is b <= a
def nt.le_flip(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(0n, 0n) == True{} : Bool}, ab.tf(h))
        case 1n+q:
          Empty.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, ab.tf(h))
    case 1n+(+p):
      match b:
        case 0n:
          {==}
        case 1n+(+q):
          nt.le_flip(p, q, h)

def nt.sub_add(+a: Nat, +b: Nat, +h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.add(Nat.sub(a, b), b) == a : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          Empty.absurd({Nat.add(0n, 1n+q) == 0n : Nat}, ab.ft(h))
    case 1n+(+p):
      match b:
        case 0n:
          nt.add_zero(1n+p)
        case 1n+(+q):
          Equal.trans(Nat, Nat.add(Nat.sub(p, q), 1n+q), 1n+Nat.add(Nat.sub(p, q), q), 1n+p, nt.add_succ(Nat.sub(p, q), q), nt.succ_eq(Nat.add(Nat.sub(p, q), q), p, nt.sub_add(p, q, h)))

# Halves

def hf(n: Nat) -> Nat:
  N.MapleNode.half(n)

def nt.half_le(+k: Nat) -> {Nat.is_le(hf(k), k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+(+p):
      match p:
        case 0n:
          {==}
        case 1n+(+q):
          nt.le_succ(hf(q), q, nt.half_le(q))

def nt.half_mono(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(hf(a), hf(b)) == True{} : Bool}:
  match a:
    case 0n:
      nt.le_zero(hf(b))
    case 1n+(+p):
      match p:
        case 0n:
          nt.le_zero(hf(b))
        case 1n+(+q):
          match b:
            case 0n:
              Empty.absurd({Nat.is_le(hf(2n+q), 0n) == True{} : Bool}, ab.ft(h))
            case 1n+(+r):
              match r:
                case 0n:
                  Empty.absurd({Nat.is_le(hf(2n+q), 0n) == True{} : Bool}, ab.ft(h))
                case 1n+(+s):
                  nt.half_mono(q, s, h)

# floor(k / 2) + ceil(k / 2) = k
def nt.half_sum(+k: Nat) -> {Nat.add(hf(k), hf(1n+k)) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+(+p):
      match p:
        case 0n:
          {==}
        case 1n+(+q):
          nt.succ_eq(Nat.add(hf(q), 1n+hf(1n+q)), 1n+q, Equal.trans(Nat, Nat.add(hf(q), 1n+hf(1n+q)), 1n+Nat.add(hf(q), hf(1n+q)), 1n+q, nt.add_succ(hf(q), hf(1n+q)), nt.succ_eq(Nat.add(hf(q), hf(1n+q)), q, nt.half_sum(q))))

def nt.half_dbl(+a: Nat) -> {hf(Nat.double(a)) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      nt.succ_eq(hf(Nat.double(p)), p, nt.half_dbl(p))

def nt.half_dbl1(+a: Nat) -> {hf(1n+Nat.double(a)) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      nt.succ_eq(hf(1n+Nat.double(p)), p, nt.half_dbl1(p))

# L = half(o + 1): 2 <= L <= o, for o >= 3
def nt.two_le_L(+o: Nat, +h: {Nat.is_le(3n, o) == True{} : Bool}) -> {Nat.is_le(2n, hf(1n+o)) == True{} : Bool}:
  match o:
    case 0n:
      Empty.absurd({Nat.is_le(2n, hf(1n)) == True{} : Bool}, ab.ft(h))
    case 1n+(+p):
      match p:
        case 0n:
          Empty.absurd({Nat.is_le(2n, hf(2n)) == True{} : Bool}, ab.ft(h))
        case 1n+(+q):
          match q:
            case 0n:
              Empty.absurd({Nat.is_le(2n, hf(3n)) == True{} : Bool}, ab.ft(h))
            case 1n+(+m):
              nt.le_zero(hf(m))

def nt.one_le_L(+o: Nat, +h: {Nat.is_le(3n, o) == True{} : Bool}) -> {Nat.is_le(1n, hf(1n+o)) == True{} : Bool}:
  nt.le_trans(1n, 2n, hf(1n+o), {==}, nt.two_le_L(o, h))

def nt.one_le(+o: Nat, +h: {Nat.is_le(3n, o) == True{} : Bool}) -> {Nat.is_le(1n, o) == True{} : Bool}:
  nt.le_trans(1n, 3n, o, {==}, h)

def nt.two_le(+o: Nat, +h: {Nat.is_le(3n, o) == True{} : Bool}) -> {Nat.is_le(2n, o) == True{} : Bool}:
  nt.le_trans(2n, 3n, o, {==}, h)

# the count after a split: with o < k <= 2o, both halves of k are L to o
def nt.split_a(+o: Nat, +k: Nat, +h1: {Nat.is_lt(o, k) == True{} : Bool}, +h2: {Nat.is_le(k, Nat.double(o)) == True{} : Bool}) -> {Bool.and(Nat.is_le(hf(1n+o), hf(k)), Nat.is_le(hf(k), o)) == True{} : Bool}:
  bo.and_intro(Nat.is_le(hf(1n+o), hf(k)), Nat.is_le(hf(k), o), nt.half_mono(1n+o, k, nt.lt_le(o, k, h1)), nt.le_rw_r(hf(k), hf(Nat.double(o)), o, nt.half_mono(k, Nat.double(o), h2), nt.half_dbl(o)))

def nt.split_b(+o: Nat, +k: Nat, +h1: {Nat.is_lt(o, k) == True{} : Bool}, +h2: {Nat.is_le(k, Nat.double(o)) == True{} : Bool}) -> {Bool.and(Nat.is_le(hf(1n+o), hf(1n+k)), Nat.is_le(hf(1n+k), o)) == True{} : Bool}:
  bo.and_intro(Nat.is_le(hf(1n+o), hf(1n+k)), Nat.is_le(hf(1n+k), o), nt.half_mono(1n+o, 1n+k, nt.lt_to_le(o, k, h1)), nt.le_rw_r(hf(1n+k), hf(1n+Nat.double(o)), o, nt.half_mono(1n+k, 1n+Nat.double(o), h2), nt.half_dbl1(o)))

# the count of a chain that lost a slot and gained one or two: from
# L <= 1 + a <= o and 1 <= b <= 2, L <= a + b <= 2o (and b + a likewise)
def nt.gain_lo(+L: Nat, +a: Nat, +b: Nat, +h1: {Nat.is_le(L, 1n+a) == True{} : Bool}, +h3: {Nat.is_le(1n, b) == True{} : Bool}) -> {Nat.is_le(L, Nat.add(a, b)) == True{} : Bool}:
  nt.le_trans(L, 1n+a, Nat.add(a, b), h1, nt.le_rw_l(1n+a, Nat.add(a, 1n), Nat.add(a, b), Equal.sym(Nat, Nat.add(a, 1n), 1n+a, nt.add_one(a)), nt.le_add_mono(a, 1n, a, b, nt.le_refl(a), h3)))

def nt.gain_hi(+o: Nat, +a: Nat, +b: Nat, +h2: {Nat.is_le(1n+a, o) == True{} : Bool}, +h4: {Nat.is_le(b, 2n) == True{} : Bool}, +h5: {Nat.is_le(1n, o) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), Nat.double(o)) == True{} : Bool}:
  nt.le_trans(Nat.add(a, b), 2n+a, Nat.double(o), nt.le_rw_r(Nat.add(a, b), Nat.add(a, 2n), 2n+a, nt.le_add_mono(a, b, a, 2n, nt.le_refl(a), h4), nt.add_two(a)), nt.le_trans(2n+a, 1n+o, Nat.double(o), h2, nt.succ_le_double(o, h5)))

def nt.gain_lo_l(+L: Nat, +a: Nat, +b: Nat, +h1: {Nat.is_le(L, 1n+a) == True{} : Bool}, +h3: {Nat.is_le(1n, b) == True{} : Bool}) -> {Nat.is_le(L, Nat.add(b, a)) == True{} : Bool}:
  nt.le_trans(L, 1n+a, Nat.add(b, a), h1, nt.le_add_mono(1n, a, b, a, h3, nt.le_refl(a)))

def nt.gain_hi_l(+o: Nat, +a: Nat, +b: Nat, +h2: {Nat.is_le(1n+a, o) == True{} : Bool}, +h4: {Nat.is_le(b, 2n) == True{} : Bool}, +h5: {Nat.is_le(1n, o) == True{} : Bool}) -> {Nat.is_le(Nat.add(b, a), Nat.double(o)) == True{} : Bool}:
  nt.le_trans(Nat.add(b, a), 2n+a, Nat.double(o), nt.le_add_mono(b, a, 2n, a, h4, nt.le_refl(a)), nt.le_trans(2n+a, 1n+o, Nat.double(o), h2, nt.succ_le_double(o, h5)))

# two counts of at most o are at most 2o together
def nt.two_o(+o: Nat, +a: Nat, +b: Nat, +ha: {Nat.is_le(a, o) == True{} : Bool}, +hb: {Nat.is_le(b, o) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, b), Nat.double(o)) == True{} : Bool}:
  nt.le_rw_r(Nat.add(a, b), Nat.add(o, o), Nat.double(o), nt.le_add_mono(a, b, o, o, ha, hb), nt.add_dbl(o))

# Lists of entries

def Es(-V: Data) -> Data:
  List<&2, M.MapleEntry<U32, V>>

def len(-V: Data, xs: Es(V)) -> Nat:
  List.length(&2, M.MapleEntry<U32, V>, xs)

def li.len_append(-V: Data, xs: Es(V), +ys: Es(V)) -> {len(V, List.append(&2, M.MapleEntry<U32, V>, xs, ys)) == Nat.add(len(V, xs), len(V, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      nt.succ_eq(len(V, List.append(&2, M.MapleEntry<U32, V>, r, ys)), Nat.add(len(V, r), len(V, ys)), li.len_append(V, r, ys))

def li.len_take(-V: Data, xs: Es(V), +k: Nat, +h: {Nat.is_le(k, len(V, xs)) == True{} : Bool}) -> {len(V, List.take(&2, M.MapleEntry<U32, V>, xs, k)) == k : Nat}:
  match xs:
    case Nil{}:
      match k:
        case 0n:
          {==}
        case 1n+j:
          Empty.absurd({0n == 1n+j : Nat}, ab.ft(h))
    case Con{x, r}:
      match k:
        case 0n:
          {==}
        case 1n+(+j):
          nt.succ_eq(len(V, List.take(&2, M.MapleEntry<U32, V>, r, j)), j, li.len_take(V, r, j, h))

def li.len_drop(-V: Data, xs: Es(V), +k: Nat, +h: {Nat.is_le(k, len(V, xs)) == True{} : Bool}) -> {Nat.add(k, len(V, List.drop(&2, M.MapleEntry<U32, V>, xs, k))) == len(V, xs) : Nat}:
  match xs:
    case Nil{}:
      match k:
        case 0n:
          {==}
        case 1n+j:
          Empty.absurd({Nat.add(1n+j, 0n) == 0n : Nat}, ab.ft(h))
    case Con{x, r}:
      match k:
        case 0n:
          {==}
        case 1n+(+j):
          nt.succ_eq(Nat.add(j, len(V, List.drop(&2, M.MapleEntry<U32, V>, r, j))), len(V, r), li.len_drop(V, r, j, h))

def li.cut_lo(eb: Bool, sb: Bool, -V: Data, +x: M.MapleEntry<U32, V>, +d: U32, +rest: Es(V), +r: Es(V), +h: {Nat.is_le(len(V, rest), len(V, r)) == True{} : Bool}) -> {Nat.is_le(len(V, M.MapleModel.cut_lo(U32, V, eb, sb, x, d, rest)), 1n+len(V, r)) == True{} : Bool}:
  match eb:
    case True{}:
      h
    case False{}:
      match sb:
        case True{}:
          match x:
            case M.MapleEntry{f, l, v}:
              h
        case False{}:
          nt.le_succ(len(V, rest), len(V, r), h)

def li.len_below(-V: Data, xs: Es(V), +a: U32) -> {Nat.is_le(len(V, M.MapleModel.below(~U32, ~U32.cmp, ~M.MapleKey32.dec, V, xs, a)), len(V, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      li.cut_lo(M.MapleKey.lt(~U32, ~U32.cmp, M.MapleEntry.last(U32, V, x), a), M.MapleKey.lt(~U32, ~U32.cmp, M.MapleEntry.first(U32, V, x), a), V, x, M.MapleKey32.dec(a), M.MapleModel.below(~U32, ~U32.cmp, ~M.MapleKey32.dec, V, r, a), r, li.len_below(V, r, a))

def li.cut_hi(sa: Bool, ea: Bool, -V: Data, +x: M.MapleEntry<U32, V>, +s: U32, +rest: Es(V), +r: Es(V), +h: {Nat.is_le(len(V, rest), len(V, r)) == True{} : Bool}) -> {Nat.is_le(len(V, M.MapleModel.cut_hi(U32, V, sa, ea, x, s, rest)), 1n+len(V, r)) == True{} : Bool}:
  match sa:
    case True{}:
      h
    case False{}:
      match ea:
        case True{}:
          match x:
            case M.MapleEntry{f, l, v}:
              h
        case False{}:
          nt.le_succ(len(V, rest), len(V, r), h)

def li.len_above(-V: Data, xs: Es(V), +b: U32) -> {Nat.is_le(len(V, M.MapleModel.above(~U32, ~U32.cmp, ~M.MapleKey32.inc, V, xs, b)), len(V, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      li.cut_hi(M.MapleKey.lt(~U32, ~U32.cmp, b, M.MapleEntry.first(U32, V, x)), M.MapleKey.lt(~U32, ~U32.cmp, b, M.MapleEntry.last(U32, V, x)), V, x, M.MapleKey32.inc(b), M.MapleModel.above(~U32, ~U32.cmp, ~M.MapleKey32.inc, V, r, b), r, li.len_above(V, r, b))

# Nodes

def Nd(-V: Data) -> Data:
  N.MapleNode<U32, V>

def Tr(-V: Data) -> Data:
  N.MapleTree<U32, V>

def cnt(-V: Data, n: Nd(V)) -> Nat:
  N.MapleNode.count(U32, V, n)

def lk(-V: Data, n: Nd(V)) -> Maybe<&2, U32>:
  N.MapleNode.last_key(U32, V, n)

def shp(-V: Data, n: Nd(V), +h: Nat, +o: Nat) -> Bool:
  N.MapleNode.shape(U32, V, n, h, o)

def fc(+o: Nat, +k: Nat) -> Bool:
  N.MapleNode.fill_ok(o, False{}, 0n, k)

# a full node of height h: a leaf of L to o entries, or a chain of L to o
# full nodes of height h - 1
def fnode(-V: Data, +h: Nat, +c: Nd(V), +o: Nat) -> Bool:
  match h:
    case 0n:
      N.MapleNode.leaf_ok(U32, V, c, o)
    case 1n+g:
      Bool.and(fc(o, cnt(V, c)), shp(V, c, g, o))

# a weak node of height h: a leaf, or a chain of full nodes of height h - 1
def wn(-V: Data, +h: Nat, n: Nd(V), +o: Nat) -> Bool:
  match h:
    case 0n:
      N.MapleNode.is_leaf(U32, V, n)
    case 1n+g:
      shp(V, n, g, o)

def sh.c(-V: Data, +h: Nat, -p: U32, +c: Nd(V), +r: Nd(V), +o: Nat, +e: {shp(V, N.MapleSlot{p, c, r}, h, o) == True{} : Bool}) -> {fnode(V, h, c, o) == True{} : Bool}:
  match h:
    case 0n:
      bo.and_l(N.MapleNode.leaf_ok(U32, V, c, o), shp(V, r, 0n, o), e)
    case 1n+(+g):
      bo.and_intro(fc(o, cnt(V, c)), shp(V, c, g, o), bo.and_l(fc(o, cnt(V, c)), Bool.and(shp(V, c, g, o), shp(V, r, 1n+g, o)), e), bo.and_l(shp(V, c, g, o), shp(V, r, 1n+g, o), bo.and_r(fc(o, cnt(V, c)), Bool.and(shp(V, c, g, o), shp(V, r, 1n+g, o)), e)))

def sh.r(-V: Data, +h: Nat, -p: U32, +c: Nd(V), +r: Nd(V), +o: Nat, +e: {shp(V, N.MapleSlot{p, c, r}, h, o) == True{} : Bool}) -> {shp(V, r, h, o) == True{} : Bool}:
  match h:
    case 0n:
      bo.and_r(N.MapleNode.leaf_ok(U32, V, c, o), shp(V, r, 0n, o), e)
    case 1n+(+g):
      bo.and_r(shp(V, c, g, o), shp(V, r, 1n+g, o), bo.and_r(fc(o, cnt(V, c)), Bool.and(shp(V, c, g, o), shp(V, r, 1n+g, o)), e))

def sh.intro(-V: Data, +h: Nat, -p: U32, +c: Nd(V), +r: Nd(V), +o: Nat, +ec: {fnode(V, h, c, o) == True{} : Bool}, +er: {shp(V, r, h, o) == True{} : Bool}) -> {shp(V, N.MapleSlot{p, c, r}, h, o) == True{} : Bool}:
  match h:
    case 0n:
      bo.and_intro(N.MapleNode.leaf_ok(U32, V, c, o), shp(V, r, 0n, o), ec, er)
    case 1n+(+g):
      bo.and_intro(fc(o, cnt(V, c)), Bool.and(shp(V, c, g, o), shp(V, r, 1n+g, o)), bo.and_l(fc(o, cnt(V, c)), shp(V, c, g, o), ec), bo.and_intro(shp(V, c, g, o), shp(V, r, 1n+g, o), bo.and_r(fc(o, cnt(V, c)), shp(V, c, g, o), ec), er))

def fn.wn(-V: Data, +h: Nat, c: Nd(V), +o: Nat, +e: {fnode(V, h, c, o) == True{} : Bool}) -> {wn(V, h, c, o) == True{} : Bool}:
  match h:
    case 0n:
      match c:
        case N.MapleLeaf{es}:
          {==}
        case N.MapleNil{}:
          Empty.absurd({False{} == True{} : Bool}, ab.ft(e))
        case N.MapleSlot{p, d, r}:
          Empty.absurd({False{} == True{} : Bool}, ab.ft(e))
    case 1n+(+g):
      bo.and_r(fc(o, cnt(V, c)), shp(V, c, g, o), e)

def fn.fc(-V: Data, +h: Nat, c: Nd(V), +o: Nat, +e: {fnode(V, h, c, o) == True{} : Bool}) -> {fc(o, cnt(V, c)) == True{} : Bool}:
  match h:
    case 0n:
      match c:
        case N.MapleLeaf{es}:
          e
        case N.MapleNil{}:
          Empty.absurd({fc(o, 0n) == True{} : Bool}, ab.ft(e))
        case N.MapleSlot{p, d, r}:
          Empty.absurd({fc(o, 1n+cnt(V, r)) == True{} : Bool}, ab.ft(e))
    case 1n+(+g):
      bo.and_l(fc(o, cnt(V, c)), shp(V, c, g, o), e)

def wn.fn(-V: Data, +h: Nat, c: Nd(V), +o: Nat, +w: {wn(V, h, c, o) == True{} : Bool}, +f: {fc(o, cnt(V, c)) == True{} : Bool}) -> {fnode(V, h, c, o) == True{} : Bool}:
  match h:
    case 0n:
      match c:
        case N.MapleLeaf{es}:
          f
        case N.MapleNil{}:
          Empty.absurd({False{} == True{} : Bool}, ab.ft(w))
        case N.MapleSlot{p, d, r}:
          Empty.absurd({False{} == True{} : Bool}, ab.ft(w))
    case 1n+(+g):
      bo.and_intro(fc(o, cnt(V, c)), shp(V, c, g, o), f, w)

# the count bounds of a full node: L <= count <= o
def fc.lo(+o: Nat, +k: Nat, +e: {fc(o, k) == True{} : Bool}) -> {Nat.is_le(hf(1n+o), k) == True{} : Bool}:
  bo.and_l(Nat.is_le(hf(1n+o), k), Nat.is_le(k, o), e)

def fc.hi(+o: Nat, +k: Nat, +e: {fc(o, k) == True{} : Bool}) -> {Nat.is_le(k, o) == True{} : Bool}:
  bo.and_r(Nat.is_le(hf(1n+o), k), Nat.is_le(k, o), e)

def fc.rw(+o: Nat, -x: Nat, -y: Nat, +e: {x == y : Nat}, +f: {fc(o, y) == True{} : Bool}) -> {fc(o, x) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {fc(o, _) == True{} : Bool}
  f

# a node with no last key holds nothing
def ab.or_some(m: Maybe<&2, U32>, -y: U32, +e: {Maybe.or(&2, U32, m, Some{y}) == None{} : Maybe<&2, U32>}) -> Empty:
  match m:
    case None{}:
      ab.some_none(U32, y, e)
    case Some{z}:
      ab.some_none(U32, z, e)

def none.cnt(-V: Data, n: Nd(V), +e: {lk(V, n) == None{} : Maybe<&2, U32>}) -> {cnt(V, n) == 0n : Nat}:
  match n:
    case N.MapleLeaf{es}:
      match es:
        case Nil{}:
          {==}
        case Con{x, r}:
          Empty.absurd({len(V, Con{x, r}) == 0n : Nat}, ab.or_some(M.MapleModel.last_key(U32, V, r), M.MapleEntry.last(U32, V, x), e))
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{p, c, r}:
      Empty.absurd({1n+cnt(V, r) == 0n : Nat}, ab.or_some(lk(V, r), p, e))

def ab.one_zero(k: Nat, +e1: {k == 0n : Nat}, +e2: {Nat.is_le(1n, k) == True{} : Bool}) -> Empty:
  match k:
    case 0n:
      ab.ft(e2)
    case 1n+j:
      ab.succ_zero(j, e1)

# Building chains (cons leaves out an empty child)

def cons(-V: Data, +c: Nd(V), r: Nd(V)) -> Nd(V):
  N.MapleNode.cons(U32, V, c, r)

def shp.cons.go(-V: Data, m: Maybe<&2, U32>, +h: Nat, +c: Nd(V), +r: Nd(V), +o: Nat, +ec: {fnode(V, h, c, o) == True{} : Bool}, +er: {shp(V, r, h, o) == True{} : Bool}) -> {shp(V, N.MapleNode.cons.go(U32, V, m, c, r), h, o) == True{} : Bool}:
  match m:
    case None{}:
      er
    case Some{+p}:
      sh.intro(V, h, p, c, r, o, ec, er)

def shp.cons(-V: Data, +h: Nat, +c: Nd(V), +r: Nd(V), +o: Nat, +ec: {fnode(V, h, c, o) == True{} : Bool}, +er: {shp(V, r, h, o) == True{} : Bool}) -> {shp(V, cons(V, c, r), h, o) == True{} : Bool}:
  shp.cons.go(V, lk(V, c), h, c, r, o, ec, er)

def cnt.cons.go(-V: Data, m: Maybe<&2, U32>, +c: Nd(V), +r: Nd(V), +em: {lk(V, c) == m : Maybe<&2, U32>}, +ec: {Nat.is_le(1n, cnt(V, c)) == True{} : Bool}) -> {cnt(V, N.MapleNode.cons.go(U32, V, m, c, r)) == 1n+cnt(V, r) : Nat}:
  match m:
    case None{}:
      Empty.absurd({cnt(V, r) == 1n+cnt(V, r) : Nat}, ab.one_zero(cnt(V, c), none.cnt(V, c, em), ec))
    case Some{p}:
      {==}

def cnt.cons(-V: Data, +c: Nd(V), +r: Nd(V), +ec: {Nat.is_le(1n, cnt(V, c)) == True{} : Bool}) -> {cnt(V, cons(V, c, r)) == 1n+cnt(V, r) : Nat}:
  cnt.cons.go(V, lk(V, c), c, r, {==}, ec)

# Appending, taking and dropping slots

def app(-V: Data, x: Nd(V), y: Nd(V)) -> Nd(V):
  N.MapleNode.append(U32, V, x, y)

def cnt.append(-V: Data, x: Nd(V), +y: Nd(V), +h: Nat, +o: Nat, +ex: {shp(V, x, h, o) == True{} : Bool}) -> {cnt(V, app(V, x, y)) == Nat.add(cnt(V, x), cnt(V, y)) : Nat}:
  match x:
    case N.MapleLeaf{es}:
      Empty.absurd({cnt(V, app(V, N.MapleLeaf{es}, y)) == Nat.add(len(V, es), cnt(V, y)) : Nat}, ab.ft(ex))
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      nt.succ_eq(cnt(V, app(V, r, y)), Nat.add(cnt(V, r), cnt(V, y)), cnt.append(V, r, y, h, o, sh.r(V, h, p, c, r, o, ex)))

def shp.append(-V: Data, x: Nd(V), +y: Nd(V), +h: Nat, +o: Nat, +ex: {shp(V, x, h, o) == True{} : Bool}, +ey: {shp(V, y, h, o) == True{} : Bool}) -> {shp(V, app(V, x, y), h, o) == True{} : Bool}:
  match x:
    case N.MapleLeaf{es}:
      Empty.absurd({shp(V, app(V, N.MapleLeaf{es}, y), h, o) == True{} : Bool}, ab.ft(ex))
    case N.MapleNil{}:
      ey
    case N.MapleSlot{+p, +c, +r}:
      sh.intro(V, h, p, c, app(V, r, y), o, sh.c(V, h, p, c, r, o, ex), shp.append(V, r, y, h, o, sh.r(V, h, p, c, r, o, ex), ey))

def take(-V: Data, n: Nd(V), k: Nat) -> Nd(V):
  N.MapleNode.take(U32, V, n, k)

def drop(-V: Data, n: Nd(V), k: Nat) -> Nd(V):
  N.MapleNode.drop(U32, V, n, k)

def cnt.take(-V: Data, n: Nd(V), +k: Nat, +ek: {Nat.is_le(k, cnt(V, n)) == True{} : Bool}) -> {cnt(V, take(V, n, k)) == k : Nat}:
  match n:
    case N.MapleLeaf{+es}:
      li.len_take(V, es, k, ek)
    case N.MapleNil{}:
      match k:
        case 0n:
          {==}
        case 1n+j:
          Empty.absurd({0n == 1n+j : Nat}, ab.ft(ek))
    case N.MapleSlot{+p, +c, +r}:
      match k:
        case 0n:
          {==}
        case 1n+(+j):
          nt.succ_eq(cnt(V, take(V, r, j)), j, cnt.take(V, r, j, ek))

def cnt.drop(-V: Data, n: Nd(V), +k: Nat, +ek: {Nat.is_le(k, cnt(V, n)) == True{} : Bool}) -> {Nat.add(k, cnt(V, drop(V, n, k))) == cnt(V, n) : Nat}:
  match n:
    case N.MapleLeaf{+es}:
      li.len_drop(V, es, k, ek)
    case N.MapleNil{}:
      match k:
        case 0n:
          {==}
        case 1n+j:
          Empty.absurd({Nat.add(1n+j, 0n) == 0n : Nat}, ab.ft(ek))
    case N.MapleSlot{+p, +c, +r}:
      match k:
        case 0n:
          {==}
        case 1n+(+j):
          nt.succ_eq(Nat.add(j, cnt(V, drop(V, r, j))), cnt(V, r), cnt.drop(V, r, j, ek))

def shp.take(-V: Data, n: Nd(V), k: Nat, +h: Nat, +o: Nat, +e: {shp(V, n, h, o) == True{} : Bool}) -> {shp(V, take(V, n, k), h, o) == True{} : Bool}:
  match n:
    case N.MapleLeaf{es}:
      Empty.absurd({shp(V, take(V, N.MapleLeaf{es}, k), h, o) == True{} : Bool}, ab.ft(e))
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      match k:
        case 0n:
          {==}
        case 1n+(+j):
          sh.intro(V, h, p, c, take(V, r, j), o, sh.c(V, h, p, c, r, o, e), shp.take(V, r, j, h, o, sh.r(V, h, p, c, r, o, e)))

def shp.drop(-V: Data, n: Nd(V), k: Nat, +h: Nat, +o: Nat, +e: {shp(V, n, h, o) == True{} : Bool}) -> {shp(V, drop(V, n, k), h, o) == True{} : Bool}:
  match n:
    case N.MapleLeaf{es}:
      Empty.absurd({shp(V, drop(V, N.MapleLeaf{es}, k), h, o) == True{} : Bool}, ab.ft(e))
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      match k:
        case 0n:
          e
        case 1n+(+j):
          shp.drop(V, r, j, h, o, sh.r(V, h, p, c, r, o, e))

def wn.take(+h: Nat, -V: Data, n: Nd(V), +k: Nat, +o: Nat, +e: {wn(V, h, n, o) == True{} : Bool}) -> {wn(V, h, take(V, n, k), o) == True{} : Bool}:
  match h:
    case 0n:
      match n:
        case N.MapleLeaf{es}:
          {==}
        case N.MapleNil{}:
          Empty.absurd({False{} == True{} : Bool}, ab.ft(e))
        case N.MapleSlot{p, c, r}:
          Empty.absurd({wn(V, 0n, take(V, N.MapleSlot{p, c, r}, k), o) == True{} : Bool}, ab.ft(e))
    case 1n+(+g):
      shp.take(V, n, k, g, o, e)

def wn.drop(+h: Nat, -V: Data, n: Nd(V), +k: Nat, +o: Nat, +e: {wn(V, h, n, o) == True{} : Bool}) -> {wn(V, h, drop(V, n, k), o) == True{} : Bool}:
  match h:
    case 0n:
      match n:
        case N.MapleLeaf{es}:
          {==}
        case N.MapleNil{}:
          Empty.absurd({False{} == True{} : Bool}, ab.ft(e))
        case N.MapleSlot{p, c, r}:
          Empty.absurd({wn(V, 0n, drop(V, N.MapleSlot{p, c, r}, k), o) == True{} : Bool}, ab.ft(e))
    case 1n+(+g):
      shp.drop(V, n, k, g, o, e)

# Merging two nodes of one height

def mrg(-V: Data, x: Nd(V), y: Nd(V)) -> Nd(V):
  N.MapleNode.merge(U32, V, x, y)

def wn.merge(+h: Nat, -V: Data, x: Nd(V), y: Nd(V), +o: Nat, +ex: {wn(V, h, x, o) == True{} : Bool}, +ey: {wn(V, h, y, o) == True{} : Bool}) -> {wn(V, h, mrg(V, x, y), o) == True{} : Bool}:
  match h:
    case 0n:
      match x:
        case N.MapleLeaf{es}:
          match y:
            case N.MapleLeaf{fs}:
              {==}
            case N.MapleNil{}:
              Empty.absurd({True{} == True{} : Bool}, ab.ft(ey))
            case N.MapleSlot{q, d, s}:
              Empty.absurd({wn(V, 0n, cons(V, N.MapleLeaf{es}, N.MapleSlot{q, d, s}), o) == True{} : Bool}, ab.ft(ey))
        case N.MapleNil{}:
          ey
        case N.MapleSlot{p, c, r}:
          Empty.absurd({wn(V, 0n, app(V, N.MapleSlot{p, c, r}, y), o) == True{} : Bool}, ab.ft(ex))
    case 1n+(+g):
      match x:
        case N.MapleLeaf{es}:
          Empty.absurd({wn(V, 1n+g, mrg(V, N.MapleLeaf{es}, y), o) == True{} : Bool}, ab.ft(ex))
        case N.MapleNil{}:
          ey
        case N.MapleSlot{+p, +c, +r}:
          shp.append(V, N.MapleSlot{p, c, r}, y, g, o, ex, ey)

def cnt.merge(+h: Nat, -V: Data, x: Nd(V), y: Nd(V), +o: Nat, +ex: {wn(V, h, x, o) == True{} : Bool}, +ey: {wn(V, h, y, o) == True{} : Bool}) -> {cnt(V, mrg(V, x, y)) == Nat.add(cnt(V, x), cnt(V, y)) : Nat}:
  match h:
    case 0n:
      match x:
        case N.MapleLeaf{+es}:
          match y:
            case N.MapleLeaf{+fs}:
              li.len_append(V, es, fs)
            case N.MapleNil{}:
              Empty.absurd({len(V, es) == Nat.add(len(V, es), 0n) : Nat}, ab.ft(ey))
            case N.MapleSlot{q, d, s}:
              Empty.absurd({cnt(V, cons(V, N.MapleLeaf{es}, N.MapleSlot{q, d, s})) == Nat.add(len(V, es), 1n+cnt(V, s)) : Nat}, ab.ft(ey))
        case N.MapleNil{}:
          {==}
        case N.MapleSlot{p, c, r}:
          Empty.absurd({cnt(V, app(V, N.MapleSlot{p, c, r}, y)) == Nat.add(1n+cnt(V, r), cnt(V, y)) : Nat}, ab.ft(ex))
    case 1n+(+g):
      match x:
        case N.MapleLeaf{es}:
          Empty.absurd({cnt(V, mrg(V, N.MapleLeaf{es}, y)) == Nat.add(len(V, es), cnt(V, y)) : Nat}, ab.ft(ex))
        case N.MapleNil{}:
          {==}
        case N.MapleSlot{+p, +c, +r}:
          cnt.append(V, N.MapleSlot{p, c, r}, y, g, o, ex)

# The ends of a chain

def shp.init.go(-V: Data, r: Nd(V), +p: U32, +c: Nd(V), +h: Nat, +o: Nat, +e: {shp(V, N.MapleSlot{p, c, r}, h, o) == True{} : Bool}) -> {shp(V, N.MapleNode.init.go(U32, V, r, p, c), h, o) == True{} : Bool}:
  match r:
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+q, +d, +r2}:
      sh.intro(V, h, p, c, N.MapleNode.init.go(U32, V, r2, q, d), o, sh.c(V, h, p, c, N.MapleSlot{q, d, r2}, o, e), shp.init.go(V, r2, q, d, h, o, sh.r(V, h, p, c, N.MapleSlot{q, d, r2}, o, e)))
    case N.MapleLeaf{+es}:
      Empty.absurd({shp(V, N.MapleSlot{p, c, N.MapleNil{}}, h, o) == True{} : Bool}, ab.ft(sh.r(V, h, p, c, N.MapleLeaf{es}, o, e)))

def cnt.init.go(-V: Data, r: Nd(V), +p: U32, +c: Nd(V), +h: Nat, +o: Nat, +e: {shp(V, N.MapleSlot{p, c, r}, h, o) == True{} : Bool}) -> {cnt(V, N.MapleNode.init.go(U32, V, r, p, c)) == cnt(V, r) : Nat}:
  match r:
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+q, +d, +r2}:
      nt.succ_eq(cnt(V, N.MapleNode.init.go(U32, V, r2, q, d)), cnt(V, r2), cnt.init.go(V, r2, q, d, h, o, sh.r(V, h, p, c, N.MapleSlot{q, d, r2}, o, e)))
    case N.MapleLeaf{+es}:
      Empty.absurd({1n == len(V, es) : Nat}, ab.ft(sh.r(V, h, p, c, N.MapleLeaf{es}, o, e)))

def fn.last.go(-V: Data, r: Nd(V), +c: Nd(V), +h: Nat, +o: Nat, +ec: {fnode(V, h, c, o) == True{} : Bool}, +er: {shp(V, r, h, o) == True{} : Bool}) -> {fnode(V, h, N.MapleNode.last.go(U32, V, r, c), o) == True{} : Bool}:
  match r:
    case N.MapleNil{}:
      ec
    case N.MapleSlot{+q, +d, +r2}:
      fn.last.go(V, r2, d, h, o, sh.c(V, h, q, d, r2, o, er), sh.r(V, h, q, d, r2, o, er))
    case N.MapleLeaf{es}:
      Empty.absurd({fnode(V, h, N.MapleLeaf{es}, o) == True{} : Bool}, ab.ft(er))

# Roots

def rs(-V: Data, +o: Nat, t: Tr(V)) -> Bool:
  match t:
    case N.MapleTree{o2, h, +n}:
      Bool.and(Nat.is_eq(o2, o), N.MapleNode.root_shape(U32, V, h, n, o))

# a root, or an empty tree
def rse(-V: Data, +o: Nat, t: Tr(V)) -> Bool:
  match t:
    case N.MapleTree{o2, h, +n}:
      Bool.and(Nat.is_eq(o2, o), Bool.or(N.MapleNode.is_empty(U32, V, n), N.MapleNode.root_shape(U32, V, h, n, o)))

def rse.of(-V: Data, +o: Nat, t: Tr(V), +e: {rs(V, o, t) == True{} : Bool}) -> {rse(V, o, t) == True{} : Bool}:
  match t:
    case N.MapleTree{+o2, +h, +n}:
      bo.and_intro(Nat.is_eq(o2, o), Bool.or(N.MapleNode.is_empty(U32, V, n), N.MapleNode.root_shape(U32, V, h, n, o)), bo.and_l(Nat.is_eq(o2, o), N.MapleNode.root_shape(U32, V, h, n, o), e), bo.or_true_r(N.MapleNode.is_empty(U32, V, n), N.MapleNode.root_shape(U32, V, h, n, o), bo.and_r(Nat.is_eq(o2, o), N.MapleNode.root_shape(U32, V, h, n, o), e)))

def rs.empty(-V: Data, +o: Nat) -> {rs(V, o, T.MapleTree.empty_of(U32, V, o)) == True{} : Bool}:
  bo.and_intro(Nat.is_eq(o, o), N.MapleNode.root_shape(U32, V, 0n, N.MapleLeaf{Nil{}}, o), nt.eq_refl(o), nt.le_zero(o))

def leaf.rs(-V: Data, c: Nd(V), +o: Nat, +lf: {N.MapleNode.leaf_ok(U32, V, c, o) == True{} : Bool}) -> {rs(V, o, N.MapleTree{o, 0n, c}) == True{} : Bool}:
  match c:
    case N.MapleLeaf{+es}:
      bo.and_intro(Nat.is_eq(o, o), N.MapleNode.root_shape(U32, V, 0n, N.MapleLeaf{es}, o), nt.eq_refl(o), bo.and_intro(Nat.is_le(0n, len(V, es)), Nat.is_le(len(V, es), o), nt.le_zero(len(V, es)), fc.hi(o, len(V, es), lf)))
    case N.MapleNil{}:
      Empty.absurd({rs(V, o, N.MapleTree{o, 0n, N.MapleNil{}}) == True{} : Bool}, ab.ft(lf))
    case N.MapleSlot{p, d, r}:
      Empty.absurd({rs(V, o, N.MapleTree{o, 0n, N.MapleSlot{p, d, r}}) == True{} : Bool}, ab.ft(lf))

def norm(-V: Data, h: Nat, n: Nd(V), o: Nat) -> Tr(V):
  T.MapleTree.norm(U32, V, h, n, o)

# a chain of at most o full nodes of height g, normalised, is a root (a
# lone child is pulled up)
def norm.chain(-V: Data, pre: Nd(V), +g: Nat, +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +e: {shp(V, pre, g, o) == True{} : Bool}, +ek: {Nat.is_le(cnt(V, pre), o) == True{} : Bool}) -> {rs(V, o, norm(V, 1n+g, pre, o)) == True{} : Bool}:
  match pre:
    case N.MapleSlot{+p, +c, r}:
      match r:
        case N.MapleNil{}:
          match g:
            case 0n:
              leaf.rs(V, c, o, sh.c(V, 0n, p, c, N.MapleNil{}, o, e))
            case 1n+(+f):
              +fn = sh.c(V, 1n+f, p, c, N.MapleNil{}, o, e)
              norm.chain(V, c, f, o, ho, bo.and_r(fc(o, cnt(V, c)), shp(V, c, f, o), fn), fc.hi(o, cnt(V, c), bo.and_l(fc(o, cnt(V, c)), shp(V, c, f, o), fn)))
        case N.MapleLeaf{+es}:
          Empty.absurd({rs(V, o, norm(V, 1n+g, N.MapleSlot{p, c, N.MapleLeaf{es}}, o)) == True{} : Bool}, ab.ft(sh.r(V, g, p, c, N.MapleLeaf{es}, o, e)))
        case N.MapleSlot{+q, +d, +s}:
          bo.and_intro(Nat.is_eq(o, o), Bool.and(N.MapleNode.fill_ok(o, True{}, 2n, cnt(V, N.MapleSlot{p, c, N.MapleSlot{q, d, s}})), shp(V, N.MapleSlot{p, c, N.MapleSlot{q, d, s}}, g, o)), nt.eq_refl(o), bo.and_intro(N.MapleNode.fill_ok(o, True{}, 2n, cnt(V, N.MapleSlot{p, c, N.MapleSlot{q, d, s}})), shp(V, N.MapleSlot{p, c, N.MapleSlot{q, d, s}}, g, o), bo.and_intro(Nat.is_le(2n, cnt(V, N.MapleSlot{p, c, N.MapleSlot{q, d, s}})), Nat.is_le(cnt(V, N.MapleSlot{p, c, N.MapleSlot{q, d, s}}), o), nt.le_zero(cnt(V, s)), ek), e))
    case N.MapleNil{}:
      rs.empty(V, o)
    case N.MapleLeaf{es}:
      Empty.absurd({rs(V, o, norm(V, 1n+g, N.MapleLeaf{es}, o)) == True{} : Bool}, ab.ft(e))

# a weak node of at most o items, normalised, is a root
def norm.wn(-V: Data, +h: Nat, n: Nd(V), +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +w: {wn(V, h, n, o) == True{} : Bool}, +ek: {Nat.is_le(cnt(V, n), o) == True{} : Bool}) -> {rs(V, o, norm(V, h, n, o)) == True{} : Bool}:
  match h:
    case 0n:
      match n:
        case N.MapleLeaf{+es}:
          bo.and_intro(Nat.is_eq(o, o), N.MapleNode.root_shape(U32, V, 0n, N.MapleLeaf{es}, o), nt.eq_refl(o), bo.and_intro(Nat.is_le(0n, len(V, es)), Nat.is_le(len(V, es), o), nt.le_zero(len(V, es)), ek))
        case N.MapleNil{}:
          Empty.absurd({rs(V, o, N.MapleTree{o, 0n, N.MapleNil{}}) == True{} : Bool}, ab.ft(w))
        case N.MapleSlot{p, d, r}:
          Empty.absurd({rs(V, o, N.MapleTree{o, 0n, N.MapleSlot{p, d, r}}) == True{} : Bool}, ab.ft(w))
    case 1n+(+g):
      norm.chain(V, n, g, o, ho, w, ek)

# Fitting: a node of too many items split in two halves

def fit(-V: Data, +o: Nat, +n: Nd(V)) -> Nd(V):
  N.MapleNode.fit(U32, V, o, n)

def fitok(-V: Data, +h: Nat, +x: Nd(V), +o: Nat) -> Bool:
  Bool.and(shp(V, x, h, o), Bool.and(Nat.is_le(1n, cnt(V, x)), Nat.is_le(cnt(V, x), 2n)))

def c12.one(-k: Nat, +e: {k == 1n : Nat}) -> {Bool.and(Nat.is_le(1n, k), Nat.is_le(k, 2n)) == True{} : Bool}:
  %Equal.sym(Nat, k, 1n, e) : {Bool.and(Nat.is_le(1n, _), Nat.is_le(_, 2n)) == True{} : Bool}
  {==}

def c12.two(-k: Nat, +e: {k == 2n : Nat}) -> {Bool.and(Nat.is_le(1n, k), Nat.is_le(k, 2n)) == True{} : Bool}:
  %Equal.sym(Nat, k, 2n, e) : {Bool.and(Nat.is_le(1n, _), Nat.is_le(_, 2n)) == True{} : Bool}
  {==}

# the halves of a node of k items, o < k <= 2o: half(k) and half(k + 1)
# items, each L to o
def sp.ca(-V: Data, +n: Nd(V)) -> {cnt(V, take(V, n, hf(cnt(V, n)))) == hf(cnt(V, n)) : Nat}:
  cnt.take(V, n, hf(cnt(V, n)), nt.half_le(cnt(V, n)))

def sp.cb(-V: Data, +n: Nd(V)) -> {cnt(V, drop(V, n, hf(cnt(V, n)))) == hf(1n+cnt(V, n)) : Nat}:
  nt.add_cancel(hf(cnt(V, n)), cnt(V, drop(V, n, hf(cnt(V, n)))), hf(1n+cnt(V, n)), Equal.trans(Nat, Nat.add(hf(cnt(V, n)), cnt(V, drop(V, n, hf(cnt(V, n))))), cnt(V, n), Nat.add(hf(cnt(V, n)), hf(1n+cnt(V, n))), cnt.drop(V, n, hf(cnt(V, n)), nt.half_le(cnt(V, n))), Equal.sym(Nat, Nat.add(hf(cnt(V, n)), hf(1n+cnt(V, n))), cnt(V, n), nt.half_sum(cnt(V, n)))))

def sp.fa(-V: Data, +n: Nd(V), +o: Nat, +eo: {Nat.is_lt(o, cnt(V, n)) == True{} : Bool}, +eU: {Nat.is_le(cnt(V, n), Nat.double(o)) == True{} : Bool}) -> {fc(o, cnt(V, take(V, n, hf(cnt(V, n))))) == True{} : Bool}:
  fc.rw(o, cnt(V, take(V, n, hf(cnt(V, n)))), hf(cnt(V, n)), sp.ca(V, n), nt.split_a(o, cnt(V, n), eo, eU))

def sp.fb(-V: Data, +n: Nd(V), +o: Nat, +eo: {Nat.is_lt(o, cnt(V, n)) == True{} : Bool}, +eU: {Nat.is_le(cnt(V, n), Nat.double(o)) == True{} : Bool}) -> {fc(o, cnt(V, drop(V, n, hf(cnt(V, n))))) == True{} : Bool}:
  fc.rw(o, cnt(V, drop(V, n, hf(cnt(V, n)))), hf(1n+cnt(V, n)), sp.cb(V, n), nt.split_b(o, cnt(V, n), eo, eU))

def fc.one(+o: Nat, +k: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +f: {fc(o, k) == True{} : Bool}) -> {Nat.is_le(1n, k) == True{} : Bool}:
  nt.le_trans(1n, hf(1n+o), k, nt.one_le_L(o, ho), fc.lo(o, k, f))

def fit.full.go(over: Bool, -V: Data, +h: Nat, +n: Nd(V), +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +eo: {Nat.is_lt(o, cnt(V, n)) == over : Bool}, +w: {wn(V, h, n, o) == True{} : Bool}, +eL: {Nat.is_le(hf(1n+o), cnt(V, n)) == True{} : Bool}, +eU: {Nat.is_le(cnt(V, n), Nat.double(o)) == True{} : Bool}) -> {fitok(V, h, N.MapleNode.fit.go(U32, V, over, n, hf(cnt(V, n))), o) == True{} : Bool}:
  match over:
    case False{}:
      +fcn = bo.and_intro(Nat.is_le(hf(1n+o), cnt(V, n)), Nat.is_le(cnt(V, n), o), eL, nt.not_lt(o, cnt(V, n), eo))
      bo.and_intro(shp(V, cons(V, n, N.MapleNil{}), h, o), Bool.and(Nat.is_le(1n, cnt(V, cons(V, n, N.MapleNil{}))), Nat.is_le(cnt(V, cons(V, n, N.MapleNil{})), 2n)), shp.cons(V, h, n, N.MapleNil{}, o, wn.fn(V, h, n, o, w, fcn), {==}), c12.one(cnt(V, cons(V, n, N.MapleNil{})), cnt.cons(V, n, N.MapleNil{}, fc.one(o, cnt(V, n), ho, fcn))))
    case True{}:
      +fa = sp.fa(V, n, o, eo, eU)
      +fb = sp.fb(V, n, o, eo, eU)
      bo.and_intro(shp(V, cons(V, take(V, n, hf(cnt(V, n))), cons(V, drop(V, n, hf(cnt(V, n))), N.MapleNil{})), h, o), Bool.and(Nat.is_le(1n, cnt(V, cons(V, take(V, n, hf(cnt(V, n))), cons(V, drop(V, n, hf(cnt(V, n))), N.MapleNil{})))), Nat.is_le(cnt(V, cons(V, take(V, n, hf(cnt(V, n))), cons(V, drop(V, n, hf(cnt(V, n))), N.MapleNil{}))), 2n)), shp.cons(V, h, take(V, n, hf(cnt(V, n))), cons(V, drop(V, n, hf(cnt(V, n))), N.MapleNil{}), o, wn.fn(V, h, take(V, n, hf(cnt(V, n))), o, wn.take(h, V, n, hf(cnt(V, n)), o, w), fa), shp.cons(V, h, drop(V, n, hf(cnt(V, n))), N.MapleNil{}, o, wn.fn(V, h, drop(V, n, hf(cnt(V, n))), o, wn.drop(h, V, n, hf(cnt(V, n)), o, w), fb), {==})), c12.two(cnt(V, cons(V, take(V, n, hf(cnt(V, n))), cons(V, drop(V, n, hf(cnt(V, n))), N.MapleNil{}))), Equal.trans(Nat, cnt(V, cons(V, take(V, n, hf(cnt(V, n))), cons(V, drop(V, n, hf(cnt(V, n))), N.MapleNil{}))), 1n+cnt(V, cons(V, drop(V, n, hf(cnt(V, n))), N.MapleNil{})), 2n, cnt.cons(V, take(V, n, hf(cnt(V, n))), cons(V, drop(V, n, hf(cnt(V, n))), N.MapleNil{}), fc.one(o, cnt(V, take(V, n, hf(cnt(V, n)))), ho, fa)), nt.succ_eq(cnt(V, cons(V, drop(V, n, hf(cnt(V, n))), N.MapleNil{})), 1n, cnt.cons(V, drop(V, n, hf(cnt(V, n))), N.MapleNil{}, fc.one(o, cnt(V, drop(V, n, hf(cnt(V, n)))), ho, fb))))))

# a weak node of L to 2o items fits as a chain of one or two full nodes
def fit.full(-V: Data, +h: Nat, +n: Nd(V), +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +w: {wn(V, h, n, o) == True{} : Bool}, +eL: {Nat.is_le(hf(1n+o), cnt(V, n)) == True{} : Bool}, +eU: {Nat.is_le(cnt(V, n), Nat.double(o)) == True{} : Bool}) -> {fitok(V, h, fit(V, o, n), o) == True{} : Bool}:
  fit.full.go(Nat.is_lt(o, cnt(V, n)), V, h, n, o, ho, {==}, w, eL, eU)

def fit.root.one(m: Maybe<&2, U32>, -V: Data, +h: Nat, +n: Nd(V), +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +w: {wn(V, h, n, o) == True{} : Bool}, +ek: {Nat.is_le(cnt(V, n), o) == True{} : Bool}) -> {rs(V, o, norm(V, 1n+h, N.MapleNode.cons.go(U32, V, m, n, N.MapleNil{}), o)) == True{} : Bool}:
  match m:
    case None{}:
      rs.empty(V, o)
    case Some{p}:
      norm.wn(V, h, n, o, ho, w, ek)

def fit.root.two(m1: Maybe<&2, U32>, m2: Maybe<&2, U32>, -V: Data, +h: Nat, +a: Nd(V), +b: Nd(V), +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +e1: {lk(V, a) == m1 : Maybe<&2, U32>}, +e2: {lk(V, b) == m2 : Maybe<&2, U32>}, +fa: {fnode(V, h, a, o) == True{} : Bool}, +fb: {fnode(V, h, b, o) == True{} : Bool}, +na: {Nat.is_le(1n, cnt(V, a)) == True{} : Bool}, +nb: {Nat.is_le(1n, cnt(V, b)) == True{} : Bool}) -> {rs(V, o, norm(V, 1n+h, N.MapleNode.cons.go(U32, V, m1, a, N.MapleNode.cons.go(U32, V, m2, b, N.MapleNil{})), o)) == True{} : Bool}:
  match m1:
    case None{}:
      Empty.absurd({rs(V, o, norm(V, 1n+h, N.MapleNode.cons.go(U32, V, m2, b, N.MapleNil{}), o)) == True{} : Bool}, ab.one_zero(cnt(V, a), none.cnt(V, a, e1), na))
    case Some{+p1}:
      match m2:
        case None{}:
          Empty.absurd({rs(V, o, norm(V, 1n+h, N.MapleSlot{p1, a, N.MapleNil{}}, o)) == True{} : Bool}, ab.one_zero(cnt(V, b), none.cnt(V, b, e2), nb))
        case Some{+p2}:
          bo.and_intro(Nat.is_eq(o, o), Bool.and(N.MapleNode.fill_ok(o, True{}, 2n, 2n), shp(V, N.MapleSlot{p1, a, N.MapleSlot{p2, b, N.MapleNil{}}}, h, o)), nt.eq_refl(o), bo.and_intro(N.MapleNode.fill_ok(o, True{}, 2n, 2n), shp(V, N.MapleSlot{p1, a, N.MapleSlot{p2, b, N.MapleNil{}}}, h, o), nt.two_le(o, ho), sh.intro(V, h, p1, a, N.MapleSlot{p2, b, N.MapleNil{}}, o, fa, sh.intro(V, h, p2, b, N.MapleNil{}, o, fb, {==}))))

def fit.root.go(over: Bool, -V: Data, +h: Nat, +n: Nd(V), +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +eo: {Nat.is_lt(o, cnt(V, n)) == over : Bool}, +w: {wn(V, h, n, o) == True{} : Bool}, +eU: {Nat.is_le(cnt(V, n), Nat.double(o)) == True{} : Bool}) -> {rs(V, o, norm(V, 1n+h, N.MapleNode.fit.go(U32, V, over, n, hf(cnt(V, n))), o)) == True{} : Bool}:
  match over:
    case False{}:
      fit.root.one(lk(V, n), V, h, n, o, ho, w, nt.not_lt(o, cnt(V, n), eo))
    case True{}:
      +fa = sp.fa(V, n, o, eo, eU)
      +fb = sp.fb(V, n, o, eo, eU)
      fit.root.two(lk(V, take(V, n, hf(cnt(V, n)))), lk(V, drop(V, n, hf(cnt(V, n)))), V, h, take(V, n, hf(cnt(V, n))), drop(V, n, hf(cnt(V, n))), o, ho, {==}, {==}, wn.fn(V, h, take(V, n, hf(cnt(V, n))), o, wn.take(h, V, n, hf(cnt(V, n)), o, w), fa), wn.fn(V, h, drop(V, n, hf(cnt(V, n))), o, wn.drop(h, V, n, hf(cnt(V, n)), o, w), fb), fc.one(o, cnt(V, take(V, n, hf(cnt(V, n)))), ho, fa), fc.one(o, cnt(V, drop(V, n, hf(cnt(V, n)))), ho, fb))

# a weak node of at most 2o items fits, normalised, as a root
def fit.root(-V: Data, +h: Nat, +n: Nd(V), +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +w: {wn(V, h, n, o) == True{} : Bool}, +eU: {Nat.is_le(cnt(V, n), Nat.double(o)) == True{} : Bool}) -> {rs(V, o, norm(V, 1n+h, fit(V, o, n), o)) == True{} : Bool}:
  fit.root.go(Nat.is_lt(o, cnt(V, n)), V, h, n, o, ho, {==}, w, eU)

# Joining

def init.go(-V: Data, r: Nd(V), p: U32, c: Nd(V)) -> Nd(V):
  N.MapleNode.init.go(U32, V, r, p, c)

def last.go(-V: Data, r: Nd(V), c: Nd(V)) -> Nd(V):
  N.MapleNode.last.go(U32, V, r, c)

def jr(-V: Data, d: Nat, +n1: Nd(V), n2: Nd(V), +o: Nat) -> Nd(V):
  T.MapleTree.join_right(U32, V, d, n1, n2, o)

def jl(-V: Data, d: Nat, n1: Nd(V), +n2: Nd(V), +o: Nat) -> Nd(V):
  T.MapleTree.join_left(U32, V, d, n1, n2, o)

def fn.chain_nil(-V: Data, +h: Nat, +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +f: {fnode(V, 1n+h, N.MapleNil{}, o) == True{} : Bool}) -> Empty:
  ab.ft(nt.le_trans(1n, hf(1n+o), 0n, nt.one_le_L(o, ho), fc.lo(o, 0n, bo.and_l(fc(o, 0n), shp(V, N.MapleNil{}, h, o), f))))

# n2 (a weak node of at most o items) merged into the right edge of n1, a
# full node d levels higher: a chain of one or two full nodes
def rs.jr(-V: Data, d: Nat, +h2: Nat, +n1: Nd(V), +n2: Nd(V), +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +f1: {fnode(V, Nat.add(d, h2), n1, o) == True{} : Bool}, +w2: {wn(V, h2, n2, o) == True{} : Bool}, +c2: {Nat.is_le(cnt(V, n2), o) == True{} : Bool}) -> {fitok(V, Nat.add(d, h2), jr(V, d, n1, n2, o), o) == True{} : Bool}:
  match d:
    case 0n:
      +w1 = fn.wn(V, h2, n1, o, f1)
      +fc1 = fn.fc(V, h2, n1, o, f1)
      +cm = cnt.merge(h2, V, n1, n2, o, w1, w2)
      fit.full(V, h2, mrg(V, n1, n2), o, ho, wn.merge(h2, V, n1, n2, o, w1, w2), nt.le_rw_r(hf(1n+o), Nat.add(cnt(V, n1), cnt(V, n2)), cnt(V, mrg(V, n1, n2)), nt.le_trans(hf(1n+o), cnt(V, n1), Nat.add(cnt(V, n1), cnt(V, n2)), fc.lo(o, cnt(V, n1), fc1), nt.le_add_r(cnt(V, n1), cnt(V, n2))), Equal.sym(Nat, cnt(V, mrg(V, n1, n2)), Nat.add(cnt(V, n1), cnt(V, n2)), cm)), nt.le_rw_l(cnt(V, mrg(V, n1, n2)), Nat.add(cnt(V, n1), cnt(V, n2)), Nat.double(o), cm, nt.two_o(o, cnt(V, n1), cnt(V, n2), fc.hi(o, cnt(V, n1), fc1), c2)))
    case 1n+(+e):
      match n1:
        case N.MapleLeaf{es}:
          Empty.absurd({fitok(V, 1n+Nat.add(e, h2), jr(V, 1n+e, N.MapleLeaf{es}, n2, o), o) == True{} : Bool}, ab.ft(bo.and_r(fc(o, len(V, es)), shp(V, N.MapleLeaf{es}, Nat.add(e, h2), o), f1)))
        case N.MapleNil{}:
          Empty.absurd({fitok(V, 1n+Nat.add(e, h2), jr(V, 1n+e, N.MapleNil{}, n2, o), o) == True{} : Bool}, fn.chain_nil(V, Nat.add(e, h2), o, ho, f1))
        case N.MapleSlot{+p, +c, +r}:
          +fc1 = bo.and_l(fc(o, 1n+cnt(V, r)), shp(V, N.MapleSlot{p, c, r}, Nat.add(e, h2), o), f1)
          +sh1 = bo.and_r(fc(o, 1n+cnt(V, r)), shp(V, N.MapleSlot{p, c, r}, Nat.add(e, h2), o), f1)
          +ih = rs.jr(V, e, h2, last.go(V, r, c), n2, o, ho, fn.last.go(V, r, c, Nat.add(e, h2), o, sh.c(V, Nat.add(e, h2), p, c, r, o, sh1), sh.r(V, Nat.add(e, h2), p, c, r, o, sh1)), w2, c2)
          +si = shp.init.go(V, r, p, c, Nat.add(e, h2), o, sh1)
          +sj = bo.and_l(shp(V, jr(V, e, last.go(V, r, c), n2, o), Nat.add(e, h2), o), Bool.and(Nat.is_le(1n, cnt(V, jr(V, e, last.go(V, r, c), n2, o))), Nat.is_le(cnt(V, jr(V, e, last.go(V, r, c), n2, o)), 2n)), ih)
          +cj = bo.and_r(shp(V, jr(V, e, last.go(V, r, c), n2, o), Nat.add(e, h2), o), Bool.and(Nat.is_le(1n, cnt(V, jr(V, e, last.go(V, r, c), n2, o))), Nat.is_le(cnt(V, jr(V, e, last.go(V, r, c), n2, o)), 2n)), ih)
          +cx = Equal.trans(Nat, cnt(V, app(V, init.go(V, r, p, c), jr(V, e, last.go(V, r, c), n2, o))), Nat.add(cnt(V, init.go(V, r, p, c)), cnt(V, jr(V, e, last.go(V, r, c), n2, o))), Nat.add(cnt(V, r), cnt(V, jr(V, e, last.go(V, r, c), n2, o))), cnt.append(V, init.go(V, r, p, c), jr(V, e, last.go(V, r, c), n2, o), Nat.add(e, h2), o, si), nt.add_cong_l(cnt(V, init.go(V, r, p, c)), cnt(V, r), cnt(V, jr(V, e, last.go(V, r, c), n2, o)), cnt.init.go(V, r, p, c, Nat.add(e, h2), o, sh1)))
          fit.full(V, 1n+Nat.add(e, h2), app(V, init.go(V, r, p, c), jr(V, e, last.go(V, r, c), n2, o)), o, ho, shp.append(V, init.go(V, r, p, c), jr(V, e, last.go(V, r, c), n2, o), Nat.add(e, h2), o, si, sj), nt.le_rw_r(hf(1n+o), Nat.add(cnt(V, r), cnt(V, jr(V, e, last.go(V, r, c), n2, o))), cnt(V, app(V, init.go(V, r, p, c), jr(V, e, last.go(V, r, c), n2, o))), nt.gain_lo(hf(1n+o), cnt(V, r), cnt(V, jr(V, e, last.go(V, r, c), n2, o)), fc.lo(o, 1n+cnt(V, r), fc1), bo.and_l(Nat.is_le(1n, cnt(V, jr(V, e, last.go(V, r, c), n2, o))), Nat.is_le(cnt(V, jr(V, e, last.go(V, r, c), n2, o)), 2n), cj)), Equal.sym(Nat, cnt(V, app(V, init.go(V, r, p, c), jr(V, e, last.go(V, r, c), n2, o))), Nat.add(cnt(V, r), cnt(V, jr(V, e, last.go(V, r, c), n2, o))), cx)), nt.le_rw_l(cnt(V, app(V, init.go(V, r, p, c), jr(V, e, last.go(V, r, c), n2, o))), Nat.add(cnt(V, r), cnt(V, jr(V, e, last.go(V, r, c), n2, o))), Nat.double(o), cx, nt.gain_hi(o, cnt(V, r), cnt(V, jr(V, e, last.go(V, r, c), n2, o)), fc.hi(o, 1n+cnt(V, r), fc1), bo.and_r(Nat.is_le(1n, cnt(V, jr(V, e, last.go(V, r, c), n2, o))), Nat.is_le(cnt(V, jr(V, e, last.go(V, r, c), n2, o)), 2n), cj), nt.one_le(o, ho))))

# n1 (a weak node of at most o items) merged into the left edge of n2, a
# full node d levels higher: a chain of one or two full nodes
def rs.jl(-V: Data, d: Nat, +h1: Nat, +n1: Nd(V), +n2: Nd(V), +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +w1: {wn(V, h1, n1, o) == True{} : Bool}, +c1: {Nat.is_le(cnt(V, n1), o) == True{} : Bool}, +f2: {fnode(V, Nat.add(d, h1), n2, o) == True{} : Bool}) -> {fitok(V, Nat.add(d, h1), jl(V, d, n1, n2, o), o) == True{} : Bool}:
  match d:
    case 0n:
      +w2 = fn.wn(V, h1, n2, o, f2)
      +fc2 = fn.fc(V, h1, n2, o, f2)
      +cm = cnt.merge(h1, V, n1, n2, o, w1, w2)
      fit.full(V, h1, mrg(V, n1, n2), o, ho, wn.merge(h1, V, n1, n2, o, w1, w2), nt.le_rw_r(hf(1n+o), Nat.add(cnt(V, n1), cnt(V, n2)), cnt(V, mrg(V, n1, n2)), nt.le_trans(hf(1n+o), cnt(V, n2), Nat.add(cnt(V, n1), cnt(V, n2)), fc.lo(o, cnt(V, n2), fc2), nt.le_add_l(cnt(V, n1), cnt(V, n2))), Equal.sym(Nat, cnt(V, mrg(V, n1, n2)), Nat.add(cnt(V, n1), cnt(V, n2)), cm)), nt.le_rw_l(cnt(V, mrg(V, n1, n2)), Nat.add(cnt(V, n1), cnt(V, n2)), Nat.double(o), cm, nt.two_o(o, cnt(V, n1), cnt(V, n2), c1, fc.hi(o, cnt(V, n2), fc2))))
    case 1n+(+e):
      match n2:
        case N.MapleLeaf{es}:
          Empty.absurd({fitok(V, 1n+Nat.add(e, h1), jl(V, 1n+e, n1, N.MapleLeaf{es}, o), o) == True{} : Bool}, ab.ft(bo.and_r(fc(o, len(V, es)), shp(V, N.MapleLeaf{es}, Nat.add(e, h1), o), f2)))
        case N.MapleNil{}:
          Empty.absurd({fitok(V, 1n+Nat.add(e, h1), jl(V, 1n+e, n1, N.MapleNil{}, o), o) == True{} : Bool}, fn.chain_nil(V, Nat.add(e, h1), o, ho, f2))
        case N.MapleSlot{+p, +c, +r}:
          +fc2 = bo.and_l(fc(o, 1n+cnt(V, r)), shp(V, N.MapleSlot{p, c, r}, Nat.add(e, h1), o), f2)
          +sh2 = bo.and_r(fc(o, 1n+cnt(V, r)), shp(V, N.MapleSlot{p, c, r}, Nat.add(e, h1), o), f2)
          +ih = rs.jl(V, e, h1, n1, c, o, ho, w1, c1, sh.c(V, Nat.add(e, h1), p, c, r, o, sh2))
          +sj = bo.and_l(shp(V, jl(V, e, n1, c, o), Nat.add(e, h1), o), Bool.and(Nat.is_le(1n, cnt(V, jl(V, e, n1, c, o))), Nat.is_le(cnt(V, jl(V, e, n1, c, o)), 2n)), ih)
          +cj = bo.and_r(shp(V, jl(V, e, n1, c, o), Nat.add(e, h1), o), Bool.and(Nat.is_le(1n, cnt(V, jl(V, e, n1, c, o))), Nat.is_le(cnt(V, jl(V, e, n1, c, o)), 2n)), ih)
          +cx = cnt.append(V, jl(V, e, n1, c, o), r, Nat.add(e, h1), o, sj)
          fit.full(V, 1n+Nat.add(e, h1), app(V, jl(V, e, n1, c, o), r), o, ho, shp.append(V, jl(V, e, n1, c, o), r, Nat.add(e, h1), o, sj, sh.r(V, Nat.add(e, h1), p, c, r, o, sh2)), nt.le_rw_r(hf(1n+o), Nat.add(cnt(V, jl(V, e, n1, c, o)), cnt(V, r)), cnt(V, app(V, jl(V, e, n1, c, o), r)), nt.gain_lo_l(hf(1n+o), cnt(V, r), cnt(V, jl(V, e, n1, c, o)), fc.lo(o, 1n+cnt(V, r), fc2), bo.and_l(Nat.is_le(1n, cnt(V, jl(V, e, n1, c, o))), Nat.is_le(cnt(V, jl(V, e, n1, c, o)), 2n), cj)), Equal.sym(Nat, cnt(V, app(V, jl(V, e, n1, c, o), r)), Nat.add(cnt(V, jl(V, e, n1, c, o)), cnt(V, r)), cx)), nt.le_rw_l(cnt(V, app(V, jl(V, e, n1, c, o), r)), Nat.add(cnt(V, jl(V, e, n1, c, o)), cnt(V, r)), Nat.double(o), cx, nt.gain_hi_l(o, cnt(V, r), cnt(V, jl(V, e, n1, c, o)), fc.hi(o, 1n+cnt(V, r), fc2), bo.and_r(Nat.is_le(1n, cnt(V, jl(V, e, n1, c, o))), Nat.is_le(cnt(V, jl(V, e, n1, c, o)), 2n), cj), nt.one_le(o, ho))))

def rsh(-V: Data, h: Nat, +n: Nd(V), +o: Nat) -> Bool:
  N.MapleNode.root_shape(U32, V, h, n, o)

def rs.wn(-V: Data, +h: Nat, +n: Nd(V), +o: Nat, +e: {rsh(V, h, n, o) == True{} : Bool}) -> {wn(V, h, n, o) == True{} : Bool}:
  match h:
    case 0n:
      match n:
        case N.MapleLeaf{es}:
          {==}
        case N.MapleNil{}:
          Empty.absurd({False{} == True{} : Bool}, ab.ft(e))
        case N.MapleSlot{p, c, r}:
          Empty.absurd({False{} == True{} : Bool}, ab.ft(e))
    case 1n+(+g):
      bo.and_r(N.MapleNode.fill_ok(o, True{}, 2n, cnt(V, n)), shp(V, n, g, o), bo.and_r(N.MapleNode.is_chain(U32, V, n), Bool.and(N.MapleNode.fill_ok(o, True{}, 2n, cnt(V, n)), shp(V, n, g, o)), e))

def rs.cnt(-V: Data, +h: Nat, +n: Nd(V), +o: Nat, +e: {rsh(V, h, n, o) == True{} : Bool}) -> {Nat.is_le(cnt(V, n), o) == True{} : Bool}:
  match h:
    case 0n:
      match n:
        case N.MapleLeaf{+es}:
          bo.and_r(Nat.is_le(0n, len(V, es)), Nat.is_le(len(V, es), o), e)
        case N.MapleNil{}:
          Empty.absurd({Nat.is_le(0n, o) == True{} : Bool}, ab.ft(e))
        case N.MapleSlot{p, c, r}:
          Empty.absurd({Nat.is_le(1n+cnt(V, r), o) == True{} : Bool}, ab.ft(e))
    case 1n+(+g):
      bo.and_r(Nat.is_le(2n, cnt(V, n)), Nat.is_le(cnt(V, n), o), bo.and_l(N.MapleNode.fill_ok(o, True{}, 2n, cnt(V, n)), shp(V, n, g, o), bo.and_r(N.MapleNode.is_chain(U32, V, n), Bool.and(N.MapleNode.fill_ok(o, True{}, 2n, cnt(V, n)), shp(V, n, g, o)), e)))

def rsh.rw(-V: Data, -x: Nat, -y: Nat, +n: Nd(V), +o: Nat, +e: {x == y : Nat}, +r: {rsh(V, y, n, o) == True{} : Bool}) -> {rsh(V, x, n, o) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {rsh(V, _, n, o) == True{} : Bool}
  r

# the root n2 merged into the root n1, d levels taller, normalised
def rs.tall_r(-V: Data, d: Nat, +h2: Nat, +n1: Nd(V), +n2: Nd(V), +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +r1: {rsh(V, Nat.add(d, h2), n1, o) == True{} : Bool}, +r2: {rsh(V, h2, n2, o) == True{} : Bool}) -> {rs(V, o, norm(V, 1n+Nat.add(d, h2), jr(V, d, n1, n2, o), o)) == True{} : Bool}:
  match d:
    case 0n:
      +w1 = rs.wn(V, h2, n1, o, r1)
      +w2 = rs.wn(V, h2, n2, o, r2)
      fit.root(V, h2, mrg(V, n1, n2), o, ho, wn.merge(h2, V, n1, n2, o, w1, w2), nt.le_rw_l(cnt(V, mrg(V, n1, n2)), Nat.add(cnt(V, n1), cnt(V, n2)), Nat.double(o), cnt.merge(h2, V, n1, n2, o, w1, w2), nt.two_o(o, cnt(V, n1), cnt(V, n2), rs.cnt(V, h2, n1, o, r1), rs.cnt(V, h2, n2, o, r2))))
    case 1n+(+e):
      match n1:
        case N.MapleLeaf{es}:
          Empty.absurd({rs(V, o, norm(V, 2n+Nat.add(e, h2), jr(V, 1n+e, N.MapleLeaf{es}, n2, o), o)) == True{} : Bool}, ab.ft(r1))
        case N.MapleNil{}:
          Empty.absurd({rs(V, o, norm(V, 2n+Nat.add(e, h2), jr(V, 1n+e, N.MapleNil{}, n2, o), o)) == True{} : Bool}, ab.ft(r1))
        case N.MapleSlot{+p, +c, +r}:
          +fl = bo.and_l(N.MapleNode.fill_ok(o, True{}, 2n, 1n+cnt(V, r)), shp(V, N.MapleSlot{p, c, r}, Nat.add(e, h2), o), r1)
          +sh1 = bo.and_r(N.MapleNode.fill_ok(o, True{}, 2n, 1n+cnt(V, r)), shp(V, N.MapleSlot{p, c, r}, Nat.add(e, h2), o), r1)
          +ih = rs.jr(V, e, h2, last.go(V, r, c), n2, o, ho, fn.last.go(V, r, c, Nat.add(e, h2), o, sh.c(V, Nat.add(e, h2), p, c, r, o, sh1), sh.r(V, Nat.add(e, h2), p, c, r, o, sh1)), rs.wn(V, h2, n2, o, r2), rs.cnt(V, h2, n2, o, r2))
          +si = shp.init.go(V, r, p, c, Nat.add(e, h2), o, sh1)
          +sj = bo.and_l(shp(V, jr(V, e, last.go(V, r, c), n2, o), Nat.add(e, h2), o), Bool.and(Nat.is_le(1n, cnt(V, jr(V, e, last.go(V, r, c), n2, o))), Nat.is_le(cnt(V, jr(V, e, last.go(V, r, c), n2, o)), 2n)), ih)
          +cj = bo.and_r(shp(V, jr(V, e, last.go(V, r, c), n2, o), Nat.add(e, h2), o), Bool.and(Nat.is_le(1n, cnt(V, jr(V, e, last.go(V, r, c), n2, o))), Nat.is_le(cnt(V, jr(V, e, last.go(V, r, c), n2, o)), 2n)), ih)
          +cx = Equal.trans(Nat, cnt(V, app(V, init.go(V, r, p, c), jr(V, e, last.go(V, r, c), n2, o))), Nat.add(cnt(V, init.go(V, r, p, c)), cnt(V, jr(V, e, last.go(V, r, c), n2, o))), Nat.add(cnt(V, r), cnt(V, jr(V, e, last.go(V, r, c), n2, o))), cnt.append(V, init.go(V, r, p, c), jr(V, e, last.go(V, r, c), n2, o), Nat.add(e, h2), o, si), nt.add_cong_l(cnt(V, init.go(V, r, p, c)), cnt(V, r), cnt(V, jr(V, e, last.go(V, r, c), n2, o)), cnt.init.go(V, r, p, c, Nat.add(e, h2), o, sh1)))
          fit.root(V, 1n+Nat.add(e, h2), app(V, init.go(V, r, p, c), jr(V, e, last.go(V, r, c), n2, o)), o, ho, shp.append(V, init.go(V, r, p, c), jr(V, e, last.go(V, r, c), n2, o), Nat.add(e, h2), o, si, sj), nt.le_rw_l(cnt(V, app(V, init.go(V, r, p, c), jr(V, e, last.go(V, r, c), n2, o))), Nat.add(cnt(V, r), cnt(V, jr(V, e, last.go(V, r, c), n2, o))), Nat.double(o), cx, nt.gain_hi(o, cnt(V, r), cnt(V, jr(V, e, last.go(V, r, c), n2, o)), bo.and_r(Nat.is_le(2n, 1n+cnt(V, r)), Nat.is_le(1n+cnt(V, r), o), fl), bo.and_r(Nat.is_le(1n, cnt(V, jr(V, e, last.go(V, r, c), n2, o))), Nat.is_le(cnt(V, jr(V, e, last.go(V, r, c), n2, o)), 2n), cj), nt.one_le(o, ho))))

# the root n1 merged into the root n2, d levels taller, normalised
def rs.tall_l(-V: Data, d: Nat, +h1: Nat, +n1: Nd(V), +n2: Nd(V), +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +r1: {rsh(V, h1, n1, o) == True{} : Bool}, +r2: {rsh(V, Nat.add(d, h1), n2, o) == True{} : Bool}) -> {rs(V, o, norm(V, 1n+Nat.add(d, h1), jl(V, d, n1, n2, o), o)) == True{} : Bool}:
  match d:
    case 0n:
      +w1 = rs.wn(V, h1, n1, o, r1)
      +w2 = rs.wn(V, h1, n2, o, r2)
      fit.root(V, h1, mrg(V, n1, n2), o, ho, wn.merge(h1, V, n1, n2, o, w1, w2), nt.le_rw_l(cnt(V, mrg(V, n1, n2)), Nat.add(cnt(V, n1), cnt(V, n2)), Nat.double(o), cnt.merge(h1, V, n1, n2, o, w1, w2), nt.two_o(o, cnt(V, n1), cnt(V, n2), rs.cnt(V, h1, n1, o, r1), rs.cnt(V, h1, n2, o, r2))))
    case 1n+(+e):
      match n2:
        case N.MapleLeaf{es}:
          Empty.absurd({rs(V, o, norm(V, 2n+Nat.add(e, h1), jl(V, 1n+e, n1, N.MapleLeaf{es}, o), o)) == True{} : Bool}, ab.ft(r2))
        case N.MapleNil{}:
          Empty.absurd({rs(V, o, norm(V, 2n+Nat.add(e, h1), jl(V, 1n+e, n1, N.MapleNil{}, o), o)) == True{} : Bool}, ab.ft(r2))
        case N.MapleSlot{+p, +c, +r}:
          +fl = bo.and_l(N.MapleNode.fill_ok(o, True{}, 2n, 1n+cnt(V, r)), shp(V, N.MapleSlot{p, c, r}, Nat.add(e, h1), o), r2)
          +sh2 = bo.and_r(N.MapleNode.fill_ok(o, True{}, 2n, 1n+cnt(V, r)), shp(V, N.MapleSlot{p, c, r}, Nat.add(e, h1), o), r2)
          +ih = rs.jl(V, e, h1, n1, c, o, ho, rs.wn(V, h1, n1, o, r1), rs.cnt(V, h1, n1, o, r1), sh.c(V, Nat.add(e, h1), p, c, r, o, sh2))
          +sj = bo.and_l(shp(V, jl(V, e, n1, c, o), Nat.add(e, h1), o), Bool.and(Nat.is_le(1n, cnt(V, jl(V, e, n1, c, o))), Nat.is_le(cnt(V, jl(V, e, n1, c, o)), 2n)), ih)
          +cj = bo.and_r(shp(V, jl(V, e, n1, c, o), Nat.add(e, h1), o), Bool.and(Nat.is_le(1n, cnt(V, jl(V, e, n1, c, o))), Nat.is_le(cnt(V, jl(V, e, n1, c, o)), 2n)), ih)
          fit.root(V, 1n+Nat.add(e, h1), app(V, jl(V, e, n1, c, o), r), o, ho, shp.append(V, jl(V, e, n1, c, o), r, Nat.add(e, h1), o, sj, sh.r(V, Nat.add(e, h1), p, c, r, o, sh2)), nt.le_rw_l(cnt(V, app(V, jl(V, e, n1, c, o), r)), Nat.add(cnt(V, jl(V, e, n1, c, o)), cnt(V, r)), Nat.double(o), cnt.append(V, jl(V, e, n1, c, o), r, Nat.add(e, h1), o, sj), nt.gain_hi_l(o, cnt(V, r), cnt(V, jl(V, e, n1, c, o)), bo.and_r(Nat.is_le(2n, 1n+cnt(V, r)), Nat.is_le(1n+cnt(V, r), o), fl), bo.and_r(Nat.is_le(1n, cnt(V, jl(V, e, n1, c, o))), Nat.is_le(cnt(V, jl(V, e, n1, c, o)), 2n), cj), nt.one_le(o, ho))))

def rs.tall(right: Bool, -V: Data, +h1: Nat, +n1: Nd(V), +h2: Nat, +n2: Nd(V), +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +er: {Nat.is_le(h2, h1) == right : Bool}, +r1: {rsh(V, h1, n1, o) == True{} : Bool}, +r2: {rsh(V, h2, n2, o) == True{} : Bool}) -> {rs(V, o, T.MapleTree.join.tall(U32, V, right, h1, n1, h2, n2, o)) == True{} : Bool}:
  match right:
    case True{}:
      +sa = nt.sub_add(h1, h2, er)
      %sa : {rs(V, o, norm(V, 1n+_, jr(V, Nat.sub(h1, h2), n1, n2, o), o)) == True{} : Bool}
      rs.tall_r(V, Nat.sub(h1, h2), h2, n1, n2, o, ho, rsh.rw(V, Nat.add(Nat.sub(h1, h2), h2), h1, n1, o, sa, r1), r2)
    case False{}:
      +sa = nt.sub_add(h2, h1, nt.le_flip(h2, h1, er))
      %sa : {rs(V, o, norm(V, 1n+_, jl(V, Nat.sub(h2, h1), n1, n2, o), o)) == True{} : Bool}
      rs.tall_l(V, Nat.sub(h2, h1), h1, n1, n2, o, ho, r1, rsh.rw(V, Nat.add(Nat.sub(h2, h1), h1), h2, n2, o, sa, r2))

def isem(-V: Data, n: Nd(V)) -> Bool:
  N.MapleNode.is_empty(U32, V, n)

def rs.join.go(e1: Bool, e2: Bool, -V: Data, +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +h1: Nat, +n1: Nd(V), +h2: Nat, +n2: Nd(V), +q1: {isem(V, n1) == e1 : Bool}, +q2: {isem(V, n2) == e2 : Bool}, +a1: {Bool.or(isem(V, n1), rsh(V, h1, n1, o)) == True{} : Bool}, +a2: {rsh(V, h2, n2, o) == True{} : Bool}) -> {rs(V, o, T.MapleTree.join.go(U32, V, e1, e2, o, h1, n1, h2, n2)) == True{} : Bool}:
  match e1:
    case True{}:
      bo.and_intro(Nat.is_eq(o, o), rsh(V, h2, n2, o), nt.eq_refl(o), a2)
    case False{}:
      match e2:
        case True{}:
          bo.and_intro(Nat.is_eq(o, o), rsh(V, h1, n1, o), nt.eq_refl(o), bo.or_false_l(isem(V, n1), rsh(V, h1, n1, o), q1, a1))
        case False{}:
          rs.tall(Nat.is_le(h2, h1), V, h1, n1, h2, n2, o, ho, {==}, bo.or_false_l(isem(V, n1), rsh(V, h1, n1, o), q1, a1), a2)

def join(-V: Data, t1: Tr(V), t2: Tr(V)) -> Tr(V):
  T.MapleTree.join(U32, V, t1, t2)

# a root (or an empty tree) joined with a root, of one order, is a root
def rs.join(-V: Data, t1: Tr(V), t2: Tr(V), +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +a1: {rse(V, o, t1) == True{} : Bool}, +a2: {rs(V, o, t2) == True{} : Bool}) -> {rs(V, o, join(V, t1, t2)) == True{} : Bool}:
  match t1:
    case N.MapleTree{+o1, +h1, +n1}:
      match t2:
        case N.MapleTree{+o2, +h2, +n2}:
          +eo = nt.eq_of(o1, o, bo.and_l(Nat.is_eq(o1, o), Bool.or(isem(V, n1), rsh(V, h1, n1, o)), a1))
          %Equal.sym(Nat, o1, o, eo) : {rs(V, o, T.MapleTree.join.go(U32, V, isem(V, n1), isem(V, n2), _, h1, n1, h2, n2)) == True{} : Bool}
          rs.join.go(isem(V, n1), isem(V, n2), V, o, ho, h1, n1, h2, n2, {==}, {==}, bo.and_r(Nat.is_eq(o1, o), Bool.or(isem(V, n1), rsh(V, h1, n1, o)), a1), bo.and_r(Nat.is_eq(o2, o), rsh(V, h2, n2, o), a2))

# Cutting below and above an index

def pre_ok(-V: Data, +h: Nat, pre: Nd(V), +o: Nat) -> Bool:
  match h:
    case 0n:
      isem(V, pre)
    case 1n+g:
      shp(V, pre, g, o)

def pre_ok.nil(-V: Data, +h: Nat, +o: Nat) -> {pre_ok(V, h, N.MapleNil{}, o) == True{} : Bool}:
  match h:
    case 0n:
      {==}
    case 1n+g:
      {==}

def rse.norm(-V: Data, +h: Nat, +pre: Nd(V), +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +pp: {pre_ok(V, h, pre, o) == True{} : Bool}, +ek: {Nat.is_le(cnt(V, pre), o) == True{} : Bool}) -> {rse(V, o, norm(V, h, pre, o)) == True{} : Bool}:
  match h:
    case 0n:
      bo.and_intro(Nat.is_eq(o, o), Bool.or(isem(V, pre), rsh(V, 0n, pre, o)), nt.eq_refl(o), bo.or_true_l(isem(V, pre), rsh(V, 0n, pre, o), pp))
    case 1n+(+g):
      rse.of(V, o, norm(V, 1n+g, pre, o), norm.chain(V, pre, g, o, ho, pp, ek))

def lo(-V: Data, n: Nd(V), h: Nat, +a: U32, pre: Nd(V), c: Cmp, +o: Nat) -> Tr(V):
  T.MapleTree.lo(~U32, ~U32.cmp, ~M.MapleKey32.dec, V, n, h, a, pre, c, o)

def hi(-V: Data, n: Nd(V), h: Nat, +b: U32, c: Cmp, +o: Nat) -> Tr(V):
  T.MapleTree.hi(~U32, ~U32.cmp, ~M.MapleKey32.inc, V, n, h, b, c, o)

def probe(-V: Data, n: Nd(V), +i: U32) -> Cmp:
  N.MapleNode.probe(~U32, ~U32.cmp, V, n, i)

def below(-V: Data, es: Es(V), +a: U32) -> Es(V):
  M.MapleModel.below(~U32, ~U32.cmp, ~M.MapleKey32.dec, V, es, a)

def above(-V: Data, es: Es(V), +b: U32) -> Es(V):
  M.MapleModel.above(~U32, ~U32.cmp, ~M.MapleKey32.inc, V, es, b)

# the part of n (a weak node of height h) below a, after pre (a chain of
# the slots before it), of at most o slots together, is a root
def rs.lo(-V: Data, n: Nd(V), +h: Nat, +a: U32, +pre: Nd(V), c: Cmp, +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +w: {wn(V, h, n, o) == True{} : Bool}, +pp: {pre_ok(V, h, pre, o) == True{} : Bool}, +ec: {Nat.is_le(Nat.add(cnt(V, pre), cnt(V, n)), o) == True{} : Bool}) -> {rs(V, o, lo(V, n, h, a, pre, c, o)) == True{} : Bool}:
  match n:
    case N.MapleSlot{+p, +ch, +r}:
      match h:
        case 0n:
          Empty.absurd({rs(V, o, lo(V, N.MapleSlot{p, ch, r}, 0n, a, pre, c, o)) == True{} : Bool}, ab.ft(w))
        case 1n+(+g):
          match c:
            case LT{}:
              +cp = cnt.append(V, pre, N.MapleSlot{p, ch, N.MapleNil{}}, g, o, pp)
              rs.lo(V, r, 1n+g, a, app(V, pre, N.MapleSlot{p, ch, N.MapleNil{}}), probe(V, r, a), o, ho, sh.r(V, g, p, ch, r, o, w), shp.append(V, pre, N.MapleSlot{p, ch, N.MapleNil{}}, g, o, pp, sh.intro(V, g, p, ch, N.MapleNil{}, o, sh.c(V, g, p, ch, r, o, w), {==})), nt.le_rw_l(Nat.add(cnt(V, app(V, pre, N.MapleSlot{p, ch, N.MapleNil{}})), cnt(V, r)), Nat.add(Nat.add(cnt(V, pre), 1n), cnt(V, r)), o, nt.add_cong_l(cnt(V, app(V, pre, N.MapleSlot{p, ch, N.MapleNil{}})), Nat.add(cnt(V, pre), 1n), cnt(V, r), cp), nt.le_rw_l(Nat.add(Nat.add(cnt(V, pre), 1n), cnt(V, r)), Nat.add(cnt(V, pre), Nat.add(1n, cnt(V, r))), o, nt.add_assoc(cnt(V, pre), 1n, cnt(V, r)), ec)))
            case EQ{}:
              +fch = sh.c(V, g, p, ch, r, o, w)
              rs.join(V, norm(V, 1n+g, pre, o), lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o), o, ho, rse.of(V, o, norm(V, 1n+g, pre, o), norm.chain(V, pre, g, o, ho, pp, nt.le_trans(cnt(V, pre), Nat.add(cnt(V, pre), 1n+cnt(V, r)), o, nt.le_add_r(cnt(V, pre), 1n+cnt(V, r)), ec))), rs.lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o, ho, fn.wn(V, g, ch, o, fch), pre_ok.nil(V, g, o), fc.hi(o, cnt(V, ch), fn.fc(V, g, ch, o, fch))))
            case GT{}:
              +fch = sh.c(V, g, p, ch, r, o, w)
              rs.join(V, norm(V, 1n+g, pre, o), lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o), o, ho, rse.of(V, o, norm(V, 1n+g, pre, o), norm.chain(V, pre, g, o, ho, pp, nt.le_trans(cnt(V, pre), Nat.add(cnt(V, pre), 1n+cnt(V, r)), o, nt.le_add_r(cnt(V, pre), 1n+cnt(V, r)), ec))), rs.lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o, ho, fn.wn(V, g, ch, o, fch), pre_ok.nil(V, g, o), fc.hi(o, cnt(V, ch), fn.fc(V, g, ch, o, fch))))
    case N.MapleNil{}:
      match h:
        case 0n:
          Empty.absurd({rs(V, o, norm(V, 0n, pre, o)) == True{} : Bool}, ab.ft(w))
        case 1n+(+g):
          norm.chain(V, pre, g, o, ho, pp, nt.le_rw_l(cnt(V, pre), Nat.add(cnt(V, pre), 0n), o, Equal.sym(Nat, Nat.add(cnt(V, pre), 0n), cnt(V, pre), nt.add_zero(cnt(V, pre))), ec))
    case N.MapleLeaf{+es}:
      rs.join(V, norm(V, h, pre, o), N.MapleTree{o, 0n, N.MapleLeaf{below(V, es, a)}}, o, ho, rse.norm(V, h, pre, o, ho, pp, nt.le_trans(cnt(V, pre), Nat.add(cnt(V, pre), len(V, es)), o, nt.le_add_r(cnt(V, pre), len(V, es)), ec)), bo.and_intro(Nat.is_eq(o, o), rsh(V, 0n, N.MapleLeaf{below(V, es, a)}, o), nt.eq_refl(o), bo.and_intro(Nat.is_le(0n, len(V, below(V, es, a))), Nat.is_le(len(V, below(V, es, a)), o), nt.le_zero(len(V, below(V, es, a))), nt.le_trans(len(V, below(V, es, a)), len(V, es), o, li.len_below(V, es, a), nt.le_trans(len(V, es), Nat.add(cnt(V, pre), len(V, es)), o, nt.le_add_l(cnt(V, pre), len(V, es)), ec)))))

# the part of n (a weak node of height h, at most o items) above b is a root
def rs.hi(-V: Data, n: Nd(V), +h: Nat, +b: U32, c: Cmp, +o: Nat, +ho: {Nat.is_le(3n, o) == True{} : Bool}, +w: {wn(V, h, n, o) == True{} : Bool}, +ec: {Nat.is_le(cnt(V, n), o) == True{} : Bool}) -> {rs(V, o, hi(V, n, h, b, c, o)) == True{} : Bool}:
  match n:
    case N.MapleSlot{+p, +ch, +r}:
      match h:
        case 0n:
          Empty.absurd({rs(V, o, hi(V, N.MapleSlot{p, ch, r}, 0n, b, c, o)) == True{} : Bool}, ab.ft(w))
        case 1n+(+g):
          match c:
            case GT{}:
              +ecr = nt.le_trans(cnt(V, r), 1n+cnt(V, r), o, nt.le_succ(cnt(V, r), cnt(V, r), nt.le_refl(cnt(V, r))), ec)
              +fch = sh.c(V, g, p, ch, r, o, w)
              rs.join(V, hi(V, ch, g, b, probe(V, ch, b), o), norm(V, 1n+g, r, o), o, ho, rse.of(V, o, hi(V, ch, g, b, probe(V, ch, b), o), rs.hi(V, ch, g, b, probe(V, ch, b), o, ho, fn.wn(V, g, ch, o, fch), fc.hi(o, cnt(V, ch), fn.fc(V, g, ch, o, fch)))), norm.chain(V, r, g, o, ho, sh.r(V, g, p, ch, r, o, w), ecr))
            case LT{}:
              +ecr = nt.le_trans(cnt(V, r), 1n+cnt(V, r), o, nt.le_succ(cnt(V, r), cnt(V, r), nt.le_refl(cnt(V, r))), ec)
              rs.hi(V, r, 1n+g, b, probe(V, r, b), o, ho, sh.r(V, g, p, ch, r, o, w), ecr)
            case EQ{}:
              +ecr = nt.le_trans(cnt(V, r), 1n+cnt(V, r), o, nt.le_succ(cnt(V, r), cnt(V, r), nt.le_refl(cnt(V, r))), ec)
              rs.hi(V, r, 1n+g, b, probe(V, r, b), o, ho, sh.r(V, g, p, ch, r, o, w), ecr)
    case N.MapleNil{}:
      rs.empty(V, o)
    case N.MapleLeaf{+es}:
      bo.and_intro(Nat.is_eq(o, o), rsh(V, 0n, N.MapleLeaf{above(V, es, b)}, o), nt.eq_refl(o), bo.and_intro(Nat.is_le(0n, len(V, above(V, es, b))), Nat.is_le(len(V, above(V, es, b)), o), nt.le_zero(len(V, above(V, es, b))), nt.le_trans(len(V, above(V, es, b)), len(V, es), o, li.len_above(V, es, b), ec)))

# Storing and erasing

def single(-V: Data, +o: Nat, +a: U32, +b: U32, +v: V) -> Tr(V):
  N.MapleTree{o, 0n, N.MapleLeaf{[M.MapleEntry{a, b, v}]}}

def rs.single(-V: Data, +o: Nat, +a: U32, +b: U32, +v: V, +ho: {Nat.is_le(3n, o) == True{} : Bool}) -> {rs(V, o, single(V, o, a, b, v)) == True{} : Bool}:
  bo.and_intro(Nat.is_eq(o, o), rsh(V, 0n, N.MapleLeaf{[M.MapleEntry{a, b, v}]}, o), nt.eq_refl(o), nt.one_le(o, ho))

def tb(-V: Data, t: Tr(V)) -> Bool:
  X.Maple.balanced(U32, V, t)

def ord(-V: Data, t: Tr(V)) -> Nat:
  X.Maple.order(U32, V, t)

def rs.bal(-V: Data, +o: Nat, t: Tr(V), +e: {rs(V, o, t) == True{} : Bool}) -> {tb(V, t) == True{} : Bool}:
  match t:
    case N.MapleTree{+o2, +h, +n}:
      +eo = nt.eq_of(o2, o, bo.and_l(Nat.is_eq(o2, o), rsh(V, h, n, o), e))
      %Equal.sym(Nat, o2, o, eo) : {rsh(V, h, n, _) == True{} : Bool}
      bo.and_r(Nat.is_eq(o2, o), rsh(V, h, n, o), e)

def tsr.go(-V: Data, ok: Bool, +t: Tr(V), +a: U32, +b: U32, +v: V) -> Tr(V):
  X.Maple.set_range.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, ok, t, a, b, v)

def tcr.go(-V: Data, ok: Bool, +t: Tr(V), +a: U32, +b: U32) -> Tr(V):
  X.Maple.clear_range.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, ok, t, a, b)

def tb.sr.go(ok: Bool, -V: Data, +t: Tr(V), +a: U32, +b: U32, +v: V, +e: {tb(V, t) == True{} : Bool}, +f: {Nat.is_le(3n, ord(V, t)) == True{} : Bool}) -> {tb(V, tsr.go(V, ok, t, a, b, v)) == True{} : Bool}:
  match ok:
    case True{}:
      match t:
        case N.MapleTree{+o, +h, +root}:
          +w = rs.wn(V, h, root, o, e)
          +cr = rs.cnt(V, h, root, o, e)
          +r1 = rs.join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v), o, f, rse.of(V, o, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), rs.lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o, f, w, pre_ok.nil(V, h, o), cr)), rs.single(V, o, a, b, v, f))
          rs.bal(V, o, join(V, join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v)), hi(V, root, h, b, probe(V, root, b), o)), rs.join(V, join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v)), hi(V, root, h, b, probe(V, root, b), o), o, f, rse.of(V, o, join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v)), r1), rs.hi(V, root, h, b, probe(V, root, b), o, f, w, cr)))
    case False{}:
      e

def tb.cr.go(ok: Bool, -V: Data, +t: Tr(V), +a: U32, +b: U32, +e: {tb(V, t) == True{} : Bool}, +f: {Nat.is_le(3n, ord(V, t)) == True{} : Bool}) -> {tb(V, tcr.go(V, ok, t, a, b)) == True{} : Bool}:
  match ok:
    case True{}:
      match t:
        case N.MapleTree{+o, +h, +root}:
          +w = rs.wn(V, h, root, o, e)
          +cr = rs.cnt(V, h, root, o, e)
          rs.bal(V, o, join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), hi(V, root, h, b, probe(V, root, b), o)), rs.join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), hi(V, root, h, b, probe(V, root, b), o), o, f, rse.of(V, o, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), rs.lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o, f, w, pre_ok.nil(V, h, o), cr)), rs.hi(V, root, h, b, probe(V, root, b), o, f, w, cr)))
    case False{}:
      e

def tb.set_range(-V: Data, +t: Tr(V), +a: U32, +b: U32, +v: V, +e: {tb(V, t) == True{} : Bool}, +f: {Nat.is_le(3n, ord(V, t)) == True{} : Bool}) -> {tb(V, X.Maple32.set_range(V, t, a, b, v)) == True{} : Bool}:
  tb.sr.go(M.MapleKey.le(~U32, ~U32.cmp, a, b), V, t, a, b, v, e, f)

def tb.clear_range(-V: Data, +t: Tr(V), +a: U32, +b: U32, +e: {tb(V, t) == True{} : Bool}, +f: {Nat.is_le(3n, ord(V, t)) == True{} : Bool}) -> {tb(V, X.Maple32.clear_range(V, t, a, b)) == True{} : Bool}:
  tb.cr.go(M.MapleKey.le(~U32, ~U32.cmp, a, b), V, t, a, b, e, f)

def tb.erase.go(-V: Data, m: Maybe<&2, M.MapleEntry<U32, V>>, +t: Tr(V), +e: {tb(V, t) == True{} : Bool}, +f: {Nat.is_le(3n, ord(V, t)) == True{} : Bool}) -> {tb(V, X.Maple.erase.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, m, t)) == True{} : Bool}:
  match m:
    case None{}:
      e
    case Some{M.MapleEntry{+fi, +la, +v}}:
      tb.clear_range(V, t, fi, la, e, f)

def tb.erase(-V: Data, +t: Tr(V), +i: U32, +e: {tb(V, t) == True{} : Bool}, +f: {Nat.is_le(3n, ord(V, t)) == True{} : Bool}) -> {tb(V, X.Maple32.erase(V, t, i)) == True{} : Bool}:
  tb.erase.go(V, X.Maple32.lookup(V, t, i), t, e, f)

# The order: every operation keeps it

def ord.norm(-V: Data, h: Nat, n: Nd(V), +o: Nat) -> {ord(V, norm(V, h, n, o)) == o : Nat}:
  match h:
    case 0n:
      {==}
    case 1n+g:
      match n:
        case N.MapleSlot{p, c, r}:
          match r:
            case N.MapleNil{}:
              ord.norm(V, g, c, o)
            case N.MapleLeaf{es}:
              {==}
            case N.MapleSlot{q, d, s}:
              {==}
        case N.MapleNil{}:
          {==}
        case N.MapleLeaf{es}:
          {==}

def ord.tall(right: Bool, -V: Data, +h1: Nat, +n1: Nd(V), +h2: Nat, +n2: Nd(V), +o: Nat) -> {ord(V, T.MapleTree.join.tall(U32, V, right, h1, n1, h2, n2, o)) == o : Nat}:
  match right:
    case True{}:
      ord.norm(V, 1n+h1, jr(V, Nat.sub(h1, h2), n1, n2, o), o)
    case False{}:
      ord.norm(V, 1n+h2, jl(V, Nat.sub(h2, h1), n1, n2, o), o)

def ord.join.go(e1: Bool, e2: Bool, -V: Data, +o: Nat, +h1: Nat, +n1: Nd(V), +h2: Nat, +n2: Nd(V)) -> {ord(V, T.MapleTree.join.go(U32, V, e1, e2, o, h1, n1, h2, n2)) == o : Nat}:
  match e1:
    case True{}:
      {==}
    case False{}:
      match e2:
        case True{}:
          {==}
        case False{}:
          ord.tall(Nat.is_le(h2, h1), V, h1, n1, h2, n2, o)

def ord.join(-V: Data, t1: Tr(V), t2: Tr(V)) -> {ord(V, join(V, t1, t2)) == ord(V, t1) : Nat}:
  match t1:
    case N.MapleTree{+o1, +h1, +n1}:
      match t2:
        case N.MapleTree{o2, +h2, +n2}:
          ord.join.go(isem(V, n1), isem(V, n2), V, o1, h1, n1, h2, n2)

def ord.lo(-V: Data, n: Nd(V), +h: Nat, +a: U32, +pre: Nd(V), c: Cmp, +o: Nat) -> {ord(V, lo(V, n, h, a, pre, c, o)) == o : Nat}:
  match n:
    case N.MapleSlot{+p, +ch, +r}:
      match h:
        case 0n:
          ord.join(V, norm(V, 0n, pre, o), N.MapleTree{o, 0n, N.MapleLeaf{below(V, N.MapleNode.entries(U32, V, N.MapleSlot{p, ch, r}), a)}})
        case 1n+(+g):
          match c:
            case LT{}:
              ord.lo(V, r, 1n+g, a, app(V, pre, N.MapleSlot{p, ch, N.MapleNil{}}), probe(V, r, a), o)
            case EQ{}:
              Equal.trans(Nat, ord(V, join(V, norm(V, 1n+g, pre, o), lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o))), ord(V, norm(V, 1n+g, pre, o)), o, ord.join(V, norm(V, 1n+g, pre, o), lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o)), ord.norm(V, 1n+g, pre, o))
            case GT{}:
              Equal.trans(Nat, ord(V, join(V, norm(V, 1n+g, pre, o), lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o))), ord(V, norm(V, 1n+g, pre, o)), o, ord.join(V, norm(V, 1n+g, pre, o), lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o)), ord.norm(V, 1n+g, pre, o))
    case N.MapleNil{}:
      ord.norm(V, h, pre, o)
    case N.MapleLeaf{+es}:
      Equal.trans(Nat, ord(V, join(V, norm(V, h, pre, o), N.MapleTree{o, 0n, N.MapleLeaf{below(V, es, a)}})), ord(V, norm(V, h, pre, o)), o, ord.join(V, norm(V, h, pre, o), N.MapleTree{o, 0n, N.MapleLeaf{below(V, es, a)}}), ord.norm(V, h, pre, o))

def ord.hi(-V: Data, n: Nd(V), +h: Nat, +b: U32, c: Cmp, +o: Nat) -> {ord(V, hi(V, n, h, b, c, o)) == o : Nat}:
  match n:
    case N.MapleSlot{+p, +ch, +r}:
      match h:
        case 0n:
          {==}
        case 1n+(+g):
          match c:
            case GT{}:
              Equal.trans(Nat, ord(V, join(V, hi(V, ch, g, b, probe(V, ch, b), o), norm(V, 1n+g, r, o))), ord(V, hi(V, ch, g, b, probe(V, ch, b), o)), o, ord.join(V, hi(V, ch, g, b, probe(V, ch, b), o), norm(V, 1n+g, r, o)), ord.hi(V, ch, g, b, probe(V, ch, b), o))
            case LT{}:
              ord.hi(V, r, 1n+g, b, probe(V, r, b), o)
            case EQ{}:
              ord.hi(V, r, 1n+g, b, probe(V, r, b), o)
    case N.MapleNil{}:
      {==}
    case N.MapleLeaf{es}:
      {==}

def ord.sr.go(ok: Bool, -V: Data, +t: Tr(V), +a: U32, +b: U32, +v: V) -> {ord(V, tsr.go(V, ok, t, a, b, v)) == ord(V, t) : Nat}:
  match ok:
    case True{}:
      match t:
        case N.MapleTree{+o, +h, +root}:
          Equal.trans(Nat, ord(V, join(V, join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v)), hi(V, root, h, b, probe(V, root, b), o))), ord(V, join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v))), o, ord.join(V, join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v)), hi(V, root, h, b, probe(V, root, b), o)), Equal.trans(Nat, ord(V, join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v))), ord(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o)), o, ord.join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v)), ord.lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o)))
    case False{}:
      {==}

def ord.cr.go(ok: Bool, -V: Data, +t: Tr(V), +a: U32, +b: U32) -> {ord(V, tcr.go(V, ok, t, a, b)) == ord(V, t) : Nat}:
  match ok:
    case True{}:
      match t:
        case N.MapleTree{+o, +h, +root}:
          Equal.trans(Nat, ord(V, join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), hi(V, root, h, b, probe(V, root, b), o))), ord(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o)), o, ord.join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), hi(V, root, h, b, probe(V, root, b), o)), ord.lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o))
    case False{}:
      {==}

def ord.erase.go(-V: Data, m: Maybe<&2, M.MapleEntry<U32, V>>, +t: Tr(V)) -> {ord(V, X.Maple.erase.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, m, t)) == ord(V, t) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{M.MapleEntry{+fi, +la, +v}}:
      ord.cr.go(M.MapleKey.le(~U32, ~U32.cmp, fi, la), V, t, fi, la)

# The size bound: a balanced tree of height g + 1 holds at least 2 m^(g+1)
# entries, for every m with 2m <= order + 1

def nt.mul_one(+a: Nat) -> {Nat.mul(a, 1n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+(+p):
      nt.succ_eq(Nat.mul(p, 1n), p, nt.mul_one(p))

def nt.pow_one(+m: Nat) -> {Nat.pow(m, 1n) == m : Nat}:
  nt.mul_one(m)

def nt.mul_mono_l(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)) == True{} : Bool}:
  match a:
    case 0n:
      nt.le_zero(Nat.mul(b, c))
    case 1n+(+p):
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(Nat.mul(1n+p, c), 0n) == True{} : Bool}, ab.ft(h))
        case 1n+(+q):
          nt.le_add_mono(c, Nat.mul(p, c), c, Nat.mul(q, c), nt.le_refl(c), nt.mul_mono_l(p, q, c, h))

def nt.m_le_L(+m: Nat, +o: Nat, +h: {Nat.is_le(Nat.double(m), 1n+o) == True{} : Bool}) -> {Nat.is_le(m, hf(1n+o)) == True{} : Bool}:
  nt.le_rw_l(m, hf(Nat.double(m)), hf(1n+o), Equal.sym(Nat, hf(Nat.double(m)), m, nt.half_dbl(m)), nt.half_mono(Nat.double(m), 1n+o, h))

def eo(-V: Data, n: Nd(V), acc: Es(V)) -> Es(V):
  N.MapleNode.entries_onto(U32, V, n, acc)

# p + (k + a) bounds from k + a <= b and p + b <= c
def nt.step(+p: Nat, +k: Nat, +a: Nat, +b: Nat, +c: Nat, +h1: {Nat.is_le(Nat.add(k, a), b) == True{} : Bool}, +h2: {Nat.is_le(Nat.add(p, b), c) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.add(p, k), a), c) == True{} : Bool}:
  nt.le_rw_l(Nat.add(Nat.add(p, k), a), Nat.add(p, Nat.add(k, a)), c, nt.add_assoc(p, k, a), nt.le_trans(Nat.add(p, Nat.add(k, a)), Nat.add(p, b), c, nt.le_add_mono(p, Nat.add(k, a), p, b, nt.le_refl(p), h1), h2))

# a full leaf holds at least m entries
def ents.leaf(-V: Data, c: Nd(V), +acc: Es(V), +m: Nat, +o: Nat, +hm: {Nat.is_le(Nat.double(m), 1n+o) == True{} : Bool}, +lf: {N.MapleNode.leaf_ok(U32, V, c, o) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.pow(m, 1n), len(V, acc)), len(V, eo(V, c, acc))) == True{} : Bool}:
  match c:
    case N.MapleLeaf{+es}:
      nt.le_rw_r(Nat.add(Nat.pow(m, 1n), len(V, acc)), Nat.add(len(V, es), len(V, acc)), len(V, eo(V, N.MapleLeaf{es}, acc)), nt.le_add_mono(Nat.pow(m, 1n), len(V, acc), len(V, es), len(V, acc), nt.le_rw_l(Nat.pow(m, 1n), m, len(V, es), nt.pow_one(m), nt.le_trans(m, hf(1n+o), len(V, es), nt.m_le_L(m, o, hm), fc.lo(o, len(V, es), lf))), nt.le_refl(len(V, acc))), Equal.sym(Nat, len(V, eo(V, N.MapleLeaf{es}, acc)), Nat.add(len(V, es), len(V, acc)), li.len_append(V, es, acc)))
    case N.MapleNil{}:
      Empty.absurd({Nat.is_le(Nat.add(Nat.pow(m, 1n), len(V, acc)), len(V, acc)) == True{} : Bool}, ab.ft(lf))
    case N.MapleSlot{p, d, r}:
      Empty.absurd({Nat.is_le(Nat.add(Nat.pow(m, 1n), len(V, acc)), len(V, eo(V, N.MapleSlot{p, d, r}, acc))) == True{} : Bool}, ab.ft(lf))

# a chain of k full nodes of height g holds at least k m^(g+1) entries
def ents.lo(-V: Data, n: Nd(V), +g: Nat, +acc: Es(V), +m: Nat, +o: Nat, +hm: {Nat.is_le(Nat.double(m), 1n+o) == True{} : Bool}, +e: {shp(V, n, g, o) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.mul(cnt(V, n), Nat.pow(m, 1n+g)), len(V, acc)), len(V, eo(V, n, acc))) == True{} : Bool}:
  match n:
    case N.MapleLeaf{es}:
      Empty.absurd({Nat.is_le(Nat.add(Nat.mul(len(V, es), Nat.pow(m, 1n+g)), len(V, acc)), len(V, eo(V, N.MapleLeaf{es}, acc))) == True{} : Bool}, ab.ft(e))
    case N.MapleNil{}:
      nt.le_refl(len(V, acc))
    case N.MapleSlot{+p, +c, +r}:
      match g:
        case 0n:
          nt.step(Nat.pow(m, 1n), Nat.mul(cnt(V, r), Nat.pow(m, 1n)), len(V, acc), len(V, eo(V, r, acc)), len(V, eo(V, c, eo(V, r, acc))), ents.lo(V, r, 0n, acc, m, o, hm, sh.r(V, 0n, p, c, r, o, e)), ents.leaf(V, c, eo(V, r, acc), m, o, hm, sh.c(V, 0n, p, c, r, o, e)))
        case 1n+(+f):
          +fq = sh.c(V, 1n+f, p, c, r, o, e)
          nt.step(Nat.pow(m, 2n+f), Nat.mul(cnt(V, r), Nat.pow(m, 2n+f)), len(V, acc), len(V, eo(V, r, acc)), len(V, eo(V, c, eo(V, r, acc))), ents.lo(V, r, 1n+f, acc, m, o, hm, sh.r(V, 1n+f, p, c, r, o, e)), nt.le_trans(Nat.add(Nat.pow(m, 2n+f), len(V, eo(V, r, acc))), Nat.add(Nat.mul(cnt(V, c), Nat.pow(m, 1n+f)), len(V, eo(V, r, acc))), len(V, eo(V, c, eo(V, r, acc))), nt.le_add_mono(Nat.pow(m, 2n+f), len(V, eo(V, r, acc)), Nat.mul(cnt(V, c), Nat.pow(m, 1n+f)), len(V, eo(V, r, acc)), nt.mul_mono_l(m, cnt(V, c), Nat.pow(m, 1n+f), nt.le_trans(m, hf(1n+o), cnt(V, c), nt.m_le_L(m, o, hm), fc.lo(o, cnt(V, c), bo.and_l(fc(o, cnt(V, c)), shp(V, c, f, o), fq)))), nt.le_refl(len(V, eo(V, r, acc)))), ents.lo(V, c, f, eo(V, r, acc), m, o, hm, bo.and_r(fc(o, cnt(V, c)), shp(V, c, f, o), fq))))

def tsize(-V: Data, t: Tr(V)) -> Nat:
  X.Maple.size(U32, V, t)

def size.ok(-V: Data, t: Tr(V), +m: Nat, +g: Nat, +e: {tb(V, t) == True{} : Bool}, +f: {Nat.is_le(Nat.double(m), 1n+ord(V, t)) == True{} : Bool}, +h: {X.Maple.height(U32, V, t) == 1n+g : Nat}) -> {Nat.is_le(Nat.mul(2n, Nat.pow(m, 1n+g)), tsize(V, t)) == True{} : Bool}:
  match t:
    case N.MapleTree{+o, +h2, +root}:
      +r1 = rsh.rw(V, 1n+g, h2, root, o, Equal.sym(Nat, h2, 1n+g, h), e)
      +rest = bo.and_r(N.MapleNode.is_chain(U32, V, root), Bool.and(N.MapleNode.fill_ok(o, True{}, 2n, cnt(V, root)), shp(V, root, g, o)), r1)
      +fl = bo.and_l(N.MapleNode.fill_ok(o, True{}, 2n, cnt(V, root)), shp(V, root, g, o), rest)
      nt.le_trans(Nat.mul(2n, Nat.pow(m, 1n+g)), Nat.mul(cnt(V, root), Nat.pow(m, 1n+g)), len(V, eo(V, root, Nil{})), nt.mul_mono_l(2n, cnt(V, root), Nat.pow(m, 1n+g), bo.and_l(Nat.is_le(2n, cnt(V, root)), Nat.is_le(cnt(V, root), o), fl)), nt.le_rw_l(Nat.mul(cnt(V, root), Nat.pow(m, 1n+g)), Nat.add(Nat.mul(cnt(V, root), Nat.pow(m, 1n+g)), 0n), len(V, eo(V, root, Nil{})), Equal.sym(Nat, Nat.add(Nat.mul(cnt(V, root), Nat.pow(m, 1n+g)), 0n), Nat.mul(cnt(V, root), Nat.pow(m, 1n+g)), nt.add_zero(Nat.mul(cnt(V, root), Nat.pow(m, 1n+g)))), ents.lo(V, root, g, Nil{}, m, o, f, bo.and_r(N.MapleNode.fill_ok(o, True{}, 2n, cnt(V, root)), shp(V, root, g, o), rest))))
