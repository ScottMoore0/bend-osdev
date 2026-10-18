import Base
import ../bytes/bytes.bend as B
import ./bits.bend as Bits
import ./mls.bend as M
import ./contexts.bend as C
import ./constraints.bend as K
import ./policy.bend as P
import ./te.bend as T
import ./avc.bend as A
import ./selinux.bend as S
import ./example.bend as X
import ./cil.bend as L
import ./LAWS.bend as Laws

# Witnesses, by computation

def Laws.witness_has():
  {==}

def Laws.witness_subset():
  {==}

def Laws.witness_dom_ab():
  {==}

def Laws.witness_dom_bc():
  {==}

def Laws.witness_dom_ba():
  {==}

def Laws.witness_canonical():
  {==}

def Laws.witness_allowed():
  {==}

def Laws.witness_mls_on():
  {==}

def Laws.witness_not_lenient():
  {==}

def Laws.witness_permissive_mode():
  {==}

def Laws.witness_permissive_types_on():
  {==}

def Laws.witness_permissive_type():
  {==}

def Laws.witness_unconditional():
  {==}

def Laws.witness_neverallow_ok():
  {==}

def Laws.witness_never_covers():
  {==}

def Laws.witness_neverallow_violated():
  {==}

def Laws.witness_transitions_conflict():
  {==}

def Laws.load_refuses_operand_word():
  {==}

def Laws.load_refuses_name_transition_in_booleanif():
  {==}

def Laws.load_refuses_conflicting_transitions():
  {==}

def Laws.load_branch_transitions():
  (Result.default(&2, &2, P.SeError, P.SePolicy, S.Selinux.load(B.Octets.of_string("(class file (read)) (type a_t) (type b_t) (boolean b true) (booleanif b (true (typetransition a_t b_t file a_t)) (false (typetransition a_t b_t file b_t)))")), X.SeExample.policy()), {==})

def Laws.witness_load():
  (Result.default(&2, &2, P.SeError, P.SePolicy, S.Selinux.load(B.Octets.of_string("(class file (read)) (type a_t) (allow a_t a_t (file (read)))")), X.SeExample.policy()), {==})

def Laws.witness_new_type():
  {==}

def Laws.witness_no_rule():
  {==}

def Laws.witness_not_process():
  {==}

def Laws.witness_no_rule_process():
  {==}

def Laws.witness_process():
  {==}

# Contradictions and Bool facts

def SePf.disc(+b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def SePf.ft(+e: {False{} == True{} : Bool}) -> SePf.disc(True{}):
  %e : SePf.disc(_)
  Unit{}

def SePf.disc2(+b: Bool) -> Type:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

def SePf.tf(+e: {True{} == False{} : Bool}) -> SePf.disc2(False{}):
  %e : SePf.disc2(_)
  Unit{}

# anything, from False == True
def SePf.absurd(-T: Type, +e: {False{} == True{} : Bool}) -> T:
  Empty.absurd(T, SePf.ft(e))

def SePf.absurd2(-T: Type, +e: {True{} == False{} : Bool}) -> T:
  Empty.absurd(T, SePf.tf(e))

def SePf.or_false(+x: Bool) -> {Bool.or(x, False{}) == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def SePf.or_false_sym(+x: Bool) -> {x == Bool.or(x, False{}) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def SePf.and_true_sym(+x: Bool) -> {x == Bool.and(x, True{}) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def SePf.and_false(+x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def SePf.or_true(+x: Bool) -> {Bool.or(x, True{}) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def SePf.or_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def SePf.and_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def SePf.and_l(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      SePf.absurd({False{} == True{} : Bool}, h)

def SePf.and_r(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      SePf.absurd({b == True{} : Bool}, h)

def SePf.and_intro(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      SePf.absurd({Bool.and(False{}, b) == True{} : Bool}, ha)

def SePf.or_l(+a: Bool, +b: Bool, +h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      SePf.absurd({Bool.or(False{}, b) == True{} : Bool}, h)

def SePf.or_r(+a: Bool, +b: Bool, +h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# or(a, b) is False: both are
def SePf.nor_l(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      SePf.absurd2({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def SePf.nor_r(+a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      SePf.absurd2({b == False{} : Bool}, h)
    case False{}:
      h

def SePf.nor_intro(+a: Bool, +b: Bool, +ha: {a == False{} : Bool}, +hb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      SePf.absurd2({Bool.or(True{}, b) == False{} : Bool}, ha)
    case False{}:
      hb

# not(x) is True: x is False
def SePf.not_true(+x: Bool, +h: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      SePf.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# x is True and x is False
def SePf.clash(-T: Type, +x: Bool, +h1: {x == True{} : Bool}, +h2: {x == False{} : Bool}) -> T:
  match x:
    case True{}:
      SePf.absurd2(T, h2)
    case False{}:
      SePf.absurd(T, h1)

# Nat facts

def SePf.nat_eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      SePf.nat_eq_refl(p)

def SePf.nat_eq_true(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          SePf.absurd({0n == 1n+q : Nat}, h)
    case 1n+p:
      match b:
        case 0n:
          SePf.absurd({1n+p == 0n : Nat}, h)
        case 1n+q:
          Equal.cong(Nat, Nat, x => 1n+x, p, q, SePf.nat_eq_true(p, q, h))

def SePf.nat_ge_trans(+a: Nat, +b: Nat, +c: Nat, +h1: {Nat.is_ge(a, b) == True{} : Bool}, +h2: {Nat.is_ge(b, c) == True{} : Bool}) -> {Nat.is_ge(a, c) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          h2
        case 1n+q:
          SePf.absurd({Nat.is_ge(0n, c) == True{} : Bool}, h1)
    case 1n+p:
      match b:
        case 0n:
          match c:
            case 0n:
              {==}
            case 1n+r:
              SePf.absurd({Nat.is_ge(1n+p, 1n+r) == True{} : Bool}, h2)
        case 1n+q:
          match c:
            case 0n:
              {==}
            case 1n+r:
              SePf.nat_ge_trans(p, q, r, h1, h2)

def SePf.nat_ge_antisym(+a: Nat, +b: Nat, +h1: {Nat.is_ge(a, b) == True{} : Bool}, +h2: {Nat.is_ge(b, a) == True{} : Bool}) -> {a == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          SePf.absurd({0n == 1n+q : Nat}, h1)
    case 1n+p:
      match b:
        case 0n:
          SePf.absurd({1n+p == 0n : Nat}, h2)
        case 1n+q:
          Equal.cong(Nat, Nat, x => 1n+x, p, q, SePf.nat_ge_antisym(p, q, h1, h2))

# Sets

def Laws.bits_has_or(a, b, k):
  match a:
    case Nil{}:
      {==}
    case Con{x, xs}:
      match b:
        case Nil{}:
          SePf.or_false_sym(Bits.SeBits.has(Con{x, xs}, k))
        case Con{y, ys}:
          match k:
            case 0n:
              {==}
            case 1n+p:
              Laws.bits_has_or(xs, ys, p)

def Laws.bits_has_and(a, b, k):
  match a:
    case Nil{}:
      {==}
    case Con{x, xs}:
      match b:
        case Nil{}:
          match k:
            case 0n:
              Equal.sym(Bool, Bool.and(x, False{}), False{}, SePf.and_false(x))
            case 1n+p:
              Equal.sym(Bool, Bool.and(Bits.SeBits.has(xs, p), False{}), False{}, SePf.and_false(Bits.SeBits.has(xs, p)))
        case Con{y, ys}:
          match k:
            case 0n:
              {==}
            case 1n+p:
              Laws.bits_has_and(xs, ys, p)

def Laws.bits_has_andnot(a, b, k):
  match a:
    case Nil{}:
      {==}
    case Con{x, xs}:
      match b:
        case Nil{}:
          SePf.and_true_sym(Bits.SeBits.has(Con{x, xs}, k))
        case Con{y, ys}:
          match k:
            case 0n:
              {==}
            case 1n+p:
              Laws.bits_has_andnot(xs, ys, p)

def Laws.bits_has_single(i, k):
  match i:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case 1n+q:
      match k:
        case 0n:
          {==}
        case 1n+p:
          Laws.bits_has_single(q, p)

def Laws.bits_has_full(n, k):
  match n:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case 1n+m:
      match k:
        case 0n:
          {==}
        case 1n+p:
          Laws.bits_has_full(m, p)

# norm.put(r, x) holds the same members as x, r
def SePf.put_has(+r: List<&2, Bool>, +x: Bool, +k: Nat) -> {Bits.SeBits.has(Bits.SeBits.norm.put(r, x), k) == Bits.SeBits.has(Con{x, r}, k) : Bool}:
  match r:
    case Nil{}:
      match x:
        case True{}:
          match k:
            case 0n:
              {==}
            case 1n+p:
              {==}
        case False{}:
          match k:
            case 0n:
              {==}
            case 1n+p:
              {==}
    case Con{y, ys}:
      {==}

def SePf.cons_has(+x: Bool, +r: List<&2, Bool>, +xs: List<&2, Bool>, +k: Nat, e: @p: Nat -> {Bits.SeBits.has(r, p) == Bits.SeBits.has(xs, p) : Bool}) -> {Bits.SeBits.has(Con{x, r}, k) == Bits.SeBits.has(Con{x, xs}, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      e(p)

def Laws.bits_has_norm(b, k):
  match b:
    case Nil{}:
      {==}
    case Con{x, xs}:
      Equal.trans(Bool, Bits.SeBits.has(Bits.SeBits.norm.put(Bits.SeBits.norm(xs), x), k), Bits.SeBits.has(Con{x, Bits.SeBits.norm(xs)}, k), Bits.SeBits.has(Con{x, xs}, k), SePf.put_has(Bits.SeBits.norm(xs), x, k), SePf.cons_has(x, Bits.SeBits.norm(xs), xs, k, p => Laws.bits_has_norm(xs, p)))

def SePf.put_norm(+r: List<&2, Bool>, +x: Bool, +h: {Bits.SeBits.is_norm(r) == True{} : Bool}) -> {Bits.SeBits.is_norm(Bits.SeBits.norm.put(r, x)) == True{} : Bool}:
  match r:
    case Nil{}:
      match x:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{y, ys}:
      h

def Laws.bits_norm_canonical(b):
  match b:
    case Nil{}:
      {==}
    case Con{x, xs}:
      SePf.put_norm(Bits.SeBits.norm(xs), x, Laws.bits_norm_canonical(xs))

def Laws.bits_subset_single(k, b):
  match k:
    case 0n:
      match b:
        case Nil{}:
          {==}
        case Con{y, ys}:
          Equal.sym(Bool, y, Bool.and(y, True{}), SePf.and_true_sym(y))
    case 1n+p:
      match b:
        case Nil{}:
          Laws.bits_subset_single(p, Nil{})
        case Con{y, ys}:
          Laws.bits_subset_single(p, ys)

def Laws.bits_any_has(b, k, h):
  match b:
    case Nil{}:
      SePf.absurd({False{} == True{} : Bool}, h)
    case Con{x, xs}:
      match k:
        case 0n:
          SePf.or_l(x, Bits.SeBits.any(xs), h)
        case 1n+p:
          SePf.or_r(x, Bits.SeBits.any(xs), Laws.bits_any_has(xs, p, h))

# a subset of the empty set has no member
def SePf.subset_nil(+a: List<&2, Bool>, +k: Nat, +h1: {Bits.SeBits.subset(a, Nil{}) == True{} : Bool}, +h2: {Bits.SeBits.has(a, k) == True{} : Bool}) -> Empty:
  match a:
    case Nil{}:
      SePf.absurd(Empty, h2)
    case Con{x, xs}:
      match k:
        case 0n:
          SePf.clash(Empty, x, h2, SePf.not_true(x, SePf.and_l(Bool.not(x), Bits.SeBits.subset(xs, Nil{}), h1)))
        case 1n+p:
          SePf.subset_nil(xs, p, SePf.and_r(Bool.not(x), Bits.SeBits.subset(xs, Nil{}), h1), h2)

# not(x) or y, with x
def SePf.imp(+x: Bool, +y: Bool, +h: {Bool.or(Bool.not(x), y) == True{} : Bool}, +hx: {x == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      h
    case False{}:
      SePf.absurd({y == True{} : Bool}, hx)

def Laws.bits_subset_has(a, b, k, h1, h2):
  match a:
    case Nil{}:
      SePf.absurd({Bits.SeBits.has(b, k) == True{} : Bool}, h2)
    case Con{x, xs}:
      match b:
        case Nil{}:
          Empty.absurd({Bits.SeBits.has(Nil{}, k) == True{} : Bool}, SePf.subset_nil(Con{x, xs}, k, h1, h2))
        case Con{y, ys}:
          match k:
            case 0n:
              SePf.imp(x, y, SePf.and_l(Bool.or(Bool.not(x), y), Bits.SeBits.subset(xs, ys), h1), h2)
            case 1n+p:
              Laws.bits_subset_has(xs, ys, p, SePf.and_r(Bool.or(Bool.not(x), y), Bits.SeBits.subset(xs, ys), h1), h2)

# MLS dominance

def SePf.subset_refl(+b: List<&2, Bool>) -> {Bits.SeBits.subset(b, b) == True{} : Bool}:
  match b:
    case Nil{}:
      {==}
    case Con{x, xs}:
      match x:
        case True{}:
          SePf.subset_refl(xs)
        case False{}:
          SePf.subset_refl(xs)

def Laws.dom_refl(l):
  match l:
    case M.SeLevel{s, cats}:
      SePf.and_intro(Nat.is_ge(s, s), Bits.SeBits.subset(cats, cats), Nat.ge_refl(s), SePf.subset_refl(cats))

# a subset of the empty set is a subset of every set
def SePf.subset_nil_any(+a: List<&2, Bool>, +z: List<&2, Bool>, +h: {Bits.SeBits.subset(a, Nil{}) == True{} : Bool}) -> {Bits.SeBits.subset(a, z) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{x, xs}:
      match x:
        case True{}:
          SePf.absurd({Bits.SeBits.subset(Con{True{}, xs}, z) == True{} : Bool}, h)
        case False{}:
          match z:
            case Nil{}:
              h
            case Con{c, zs}:
              SePf.subset_nil_any(xs, zs, h)

def SePf.imp_trans(+a: Bool, +b: Bool, +c: Bool, +h1: {Bool.or(Bool.not(a), b) == True{} : Bool}, +h2: {Bool.or(Bool.not(b), c) == True{} : Bool}) -> {Bool.or(Bool.not(a), c) == True{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      match b:
        case False{}:
          SePf.absurd({Bool.or(False{}, c) == True{} : Bool}, h1)
        case True{}:
          h2

# not(a) or b, and not(b) (and xs a subset of the empty set): a set headed
# by a, a subset of the empty set
def SePf.subset_trans.nil(+a: Bool, +b: Bool, +xs: List<&2, Bool>, +ys: List<&2, Bool>, +h1: {Bits.SeBits.subset(Con{a, xs}, Con{b, ys}) == True{} : Bool}, +h2: {Bits.SeBits.subset(Con{b, ys}, Nil{}) == True{} : Bool}, +hx: {Bits.SeBits.subset(xs, Nil{}) == True{} : Bool}) -> {Bits.SeBits.subset(Con{a, xs}, Nil{}) == True{} : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          SePf.absurd({Bits.SeBits.subset(Con{True{}, xs}, Nil{}) == True{} : Bool}, h2)
        case False{}:
          SePf.absurd({Bits.SeBits.subset(Con{True{}, xs}, Nil{}) == True{} : Bool}, h1)
    case False{}:
      match b:
        case True{}:
          SePf.absurd({Bits.SeBits.subset(Con{False{}, xs}, Nil{}) == True{} : Bool}, h2)
        case False{}:
          hx

def SePf.subset_trans(+x: List<&2, Bool>, +y: List<&2, Bool>, +z: List<&2, Bool>, +h1: {Bits.SeBits.subset(x, y) == True{} : Bool}, +h2: {Bits.SeBits.subset(y, z) == True{} : Bool}) -> {Bits.SeBits.subset(x, z) == True{} : Bool}:
  match x:
    case Nil{}:
      {==}
    case Con{a, xs}:
      match y:
        case Nil{}:
          SePf.subset_nil_any(Con{a, xs}, z, h1)
        case Con{b, ys}:
          match z:
            case Nil{}:
              SePf.subset_trans.nil(a, b, xs, ys, h1, h2, SePf.subset_trans(xs, ys, Nil{}, SePf.and_r(Bool.or(Bool.not(a), b), Bits.SeBits.subset(xs, ys), h1), SePf.and_r(Bool.not(b), Bits.SeBits.subset(ys, Nil{}), h2)))
            case Con{c, zs}:
              SePf.and_intro(Bool.or(Bool.not(a), c), Bits.SeBits.subset(xs, zs), SePf.imp_trans(a, b, c, SePf.and_l(Bool.or(Bool.not(a), b), Bits.SeBits.subset(xs, ys), h1), SePf.and_l(Bool.or(Bool.not(b), c), Bits.SeBits.subset(ys, zs), h2)), SePf.subset_trans(xs, ys, zs, SePf.and_r(Bool.or(Bool.not(a), b), Bits.SeBits.subset(xs, ys), h1), SePf.and_r(Bool.or(Bool.not(b), c), Bits.SeBits.subset(ys, zs), h2)))

def Laws.dom_trans(a, b, c, h1, h2):
  match a:
    case M.SeLevel{sa, ca}:
      match b:
        case M.SeLevel{sb, cb}:
          match c:
            case M.SeLevel{sc, cc}:
              SePf.and_intro(Nat.is_ge(sa, sc), Bits.SeBits.subset(cc, ca), SePf.nat_ge_trans(sa, sb, sc, SePf.and_l(Nat.is_ge(sa, sb), Bits.SeBits.subset(cb, ca), h1), SePf.and_l(Nat.is_ge(sb, sc), Bits.SeBits.subset(cc, cb), h2)), SePf.subset_trans(cc, cb, ca, SePf.and_r(Nat.is_ge(sb, sc), Bits.SeBits.subset(cc, cb), h2), SePf.and_r(Nat.is_ge(sa, sb), Bits.SeBits.subset(cb, ca), h1)))

# a canonical non-empty set has a member, so is no subset of the empty set
def SePf.norm_not_empty(+ys: List<&2, Bool>, +b: Bool, +h: {Bits.SeBits.subset(Con{b, ys}, Nil{}) == True{} : Bool}, +n: {Bits.SeBits.last(ys, b) == True{} : Bool}) -> Empty:
  match ys:
    case Nil{}:
      match b:
        case True{}:
          SePf.absurd(Empty, h)
        case False{}:
          SePf.absurd(Empty, n)
    case Con{c, zs}:
      SePf.norm_not_empty(zs, c, SePf.and_r(Bool.not(b), Bits.SeBits.subset(Con{c, zs}, Nil{}), h), n)

# the tail of a canonical set is canonical
def SePf.norm_tail(+xs: List<&2, Bool>, +a: Bool, +h: {Bits.SeBits.last(xs, a) == True{} : Bool}) -> {Bits.SeBits.is_norm(xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{c, zs}:
      h

def SePf.bool_antisym(+a: Bool, +b: Bool, +h1: {Bool.or(Bool.not(a), b) == True{} : Bool}, +h2: {Bool.or(Bool.not(b), a) == True{} : Bool}) -> {a == b : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          SePf.absurd({True{} == False{} : Bool}, h1)
    case False{}:
      match b:
        case True{}:
          SePf.absurd({False{} == True{} : Bool}, h2)
        case False{}:
          {==}

def SePf.bits_antisym(+x: List<&2, Bool>, +y: List<&2, Bool>, +h1: {Bits.SeBits.subset(x, y) == True{} : Bool}, +h2: {Bits.SeBits.subset(y, x) == True{} : Bool}, +nx: {Bits.SeBits.is_norm(x) == True{} : Bool}, +ny: {Bits.SeBits.is_norm(y) == True{} : Bool}) -> {x == y : List<&2, Bool>}:
  match x:
    case Nil{}:
      match y:
        case Nil{}:
          {==}
        case Con{b, ys}:
          Empty.absurd({Nil{} == Con{b, ys} : List<&2, Bool>}, SePf.norm_not_empty(ys, b, h2, ny))
    case Con{a, xs}:
      match y:
        case Nil{}:
          Empty.absurd({Con{a, xs} == Nil{} : List<&2, Bool>}, SePf.norm_not_empty(xs, a, h1, nx))
        case Con{b, ys}:
          +eh = SePf.bool_antisym(a, b, SePf.and_l(Bool.or(Bool.not(a), b), Bits.SeBits.subset(xs, ys), h1), SePf.and_l(Bool.or(Bool.not(b), a), Bits.SeBits.subset(ys, xs), h2))
          +et = SePf.bits_antisym(xs, ys, SePf.and_r(Bool.or(Bool.not(a), b), Bits.SeBits.subset(xs, ys), h1), SePf.and_r(Bool.or(Bool.not(b), a), Bits.SeBits.subset(ys, xs), h2), SePf.norm_tail(xs, a, nx), SePf.norm_tail(ys, b, ny))
          %eh : {Con{a, xs} == Con{_, ys} : List<&2, Bool>}
          %et : {Con{a, xs} == Con{a, _} : List<&2, Bool>}
          {==}

def Laws.dom_antisym(a, b, h1, h2, ca, cb):
  match a:
    case M.SeLevel{sa, xa}:
      match b:
        case M.SeLevel{sb, xb}:
          +es = SePf.nat_ge_antisym(sa, sb, SePf.and_l(Nat.is_ge(sa, sb), Bits.SeBits.subset(xb, xa), h1), SePf.and_l(Nat.is_ge(sb, sa), Bits.SeBits.subset(xa, xb), h2))
          +ex = SePf.bits_antisym(xa, xb, SePf.and_r(Nat.is_ge(sb, sa), Bits.SeBits.subset(xa, xb), h2), SePf.and_r(Nat.is_ge(sa, sb), Bits.SeBits.subset(xb, xa), h1), ca, cb)
          %es : {M.SeLevel{sa, xa} == M.SeLevel{_, xb} : M.SeLevel}
          %ex : {M.SeLevel{sa, xa} == M.SeLevel{sa, _} : M.SeLevel}
          {==}

def Laws.level_make_canonical(s, cats):
  Laws.bits_norm_canonical(cats)

# Access vectors: the implementation (a fold that unites the permissions of
# matching rules, then takes away what failing constraints name) against
# the specification (some rule in force covers the permission, every
# constraint holds)

def SePf.add_go(+m: Bool, +perms: List<&2, Bool>, +acc: List<&2, Bool>, +k: Nat) -> {Bits.SeBits.has(A.SeAvc.add.go(m, perms, acc), k) == Bool.or(Bits.SeBits.has(acc, k), Bool.and(m, Bits.SeBits.has(perms, k))) : Bool}:
  match m:
    case True{}:
      Laws.bits_has_or(acc, perms, k)
    case False{}:
      SePf.or_false_sym(Bits.SeBits.has(acc, k))

def SePf.collect(+rs: List<&2, P.SeAvRule>, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, +acc: List<&2, Bool>, +k: Nat) -> {Bits.SeBits.has(A.SeAvc.collect(rs, kind, st, tt, c, acc), k) == Bool.or(Bits.SeBits.has(acc, k), T.SeTe.any_covers(rs, kind, st, tt, c, k)) : Bool}:
  match rs:
    case Nil{}:
      SePf.or_false_sym(Bits.SeBits.has(acc, k))
    case Con{+r, t}:
      +a2 = A.SeAvc.add(r, kind, st, tt, c, acc)
      +x = Bits.SeBits.has(acc, k)
      +y = Bool.and(T.SeTe.rule_matches(r, kind, st, tt, c), Bits.SeBits.has(P.SeAvRule.perms(r), k))
      +z = T.SeTe.any_covers(t, kind, st, tt, c, k)
      Equal.trans(Bool, Bits.SeBits.has(A.SeAvc.collect(t, kind, st, tt, c, a2), k), Bool.or(Bits.SeBits.has(a2, k), z), Bool.or(x, Bool.or(y, z)), SePf.collect(t, kind, st, tt, c, a2, k), Equal.trans(Bool, Bool.or(Bits.SeBits.has(a2, k), z), Bool.or(Bool.or(x, y), z), Bool.or(x, Bool.or(y, z)), Equal.cong(Bool, Bool, v => Bool.or(v, z), Bits.SeBits.has(a2, k), Bool.or(x, y), SePf.add_go(T.SeTe.rule_matches(r, kind, st, tt, c), P.SeAvRule.perms(r), acc, k)), SePf.or_assoc(x, y, z)))

def SePf.any_append(+xs: List<&2, P.SeAvRule>, +ys: List<&2, P.SeAvRule>, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, +k: Nat) -> {T.SeTe.any_covers(List.append(&2, P.SeAvRule, xs, ys), kind, st, tt, c, k) == Bool.or(T.SeTe.any_covers(xs, kind, st, tt, c, k), T.SeTe.any_covers(ys, kind, st, tt, c, k)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+r, t}:
      +x = T.SeTe.rule_covers(r, kind, st, tt, c, k)
      +a = T.SeTe.any_covers(t, kind, st, tt, c, k)
      +b = T.SeTe.any_covers(ys, kind, st, tt, c, k)
      Equal.trans(Bool, Bool.or(x, T.SeTe.any_covers(List.append(&2, P.SeAvRule, t, ys), kind, st, tt, c, k)), Bool.or(x, Bool.or(a, b)), Bool.or(Bool.or(x, a), b), Equal.cong(Bool, Bool, v => Bool.or(x, v), T.SeTe.any_covers(List.append(&2, P.SeAvRule, t, ys), kind, st, tt, c, k), Bool.or(a, b), SePf.any_append(t, ys, kind, st, tt, c, k)), Equal.sym(Bool, Bool.or(Bool.or(x, a), b), Bool.or(x, Bool.or(a, b)), SePf.or_assoc(x, a, b)))

def SePf.conds(+cs: List<&2, P.SeCond>, +bs: List<&2, Bool>, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, +acc: List<&2, Bool>, +k: Nat) -> {Bits.SeBits.has(A.SeAvc.collect_conds(cs, bs, kind, st, tt, c, acc), k) == Bool.or(Bits.SeBits.has(acc, k), T.SeTe.any_covers(T.SeTe.cond_av(cs, bs), kind, st, tt, c, k)) : Bool}:
  match cs:
    case Nil{}:
      SePf.or_false_sym(Bits.SeBits.has(acc, k))
    case Con{+cd, t}:
      +br = T.SeTe.branch_av(cd, bs)
      +a2 = A.SeAvc.collect(br, kind, st, tt, c, acc)
      +x = Bits.SeBits.has(acc, k)
      +y = T.SeTe.any_covers(br, kind, st, tt, c, k)
      +z = T.SeTe.any_covers(T.SeTe.cond_av(t, bs), kind, st, tt, c, k)
      +w = T.SeTe.any_covers(List.append(&2, P.SeAvRule, br, T.SeTe.cond_av(t, bs)), kind, st, tt, c, k)
      Equal.trans(Bool, Bits.SeBits.has(A.SeAvc.collect_conds(t, bs, kind, st, tt, c, a2), k), Bool.or(Bits.SeBits.has(a2, k), z), Bool.or(x, w), SePf.conds(t, bs, kind, st, tt, c, a2, k), Equal.trans(Bool, Bool.or(Bits.SeBits.has(a2, k), z), Bool.or(Bool.or(x, y), z), Bool.or(x, w), Equal.cong(Bool, Bool, v => Bool.or(v, z), Bits.SeBits.has(a2, k), Bool.or(x, y), SePf.collect(br, kind, st, tt, c, acc, k)), Equal.trans(Bool, Bool.or(Bool.or(x, y), z), Bool.or(x, Bool.or(y, z)), Bool.or(x, w), SePf.or_assoc(x, y, z), Equal.cong(Bool, Bool, v => Bool.or(x, v), Bool.or(y, z), w, Equal.sym(Bool, w, Bool.or(y, z), SePf.any_append(br, T.SeTe.cond_av(t, bs), kind, st, tt, c, k))))))

# the permissions rules in force give are those a rule in force covers
def SePf.rules(+p: P.SePolicy, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, +k: Nat) -> {Bits.SeBits.has(A.SeAvc.rules_av(p, kind, st, tt, c), k) == T.SeTe.covers(p, kind, st, tt, c, k) : Bool}:
  +cav = T.SeTe.cond_av(P.SePolicy.conds(p), P.SePolicy.state(p))
  +a0 = A.SeAvc.collect(P.SePolicy.av(p), kind, st, tt, c, Nil{})
  +z = T.SeTe.any_covers(cav, kind, st, tt, c, k)
  Equal.trans(Bool, Bits.SeBits.has(A.SeAvc.rules_av(p, kind, st, tt, c), k), Bool.or(Bits.SeBits.has(a0, k), z), T.SeTe.covers(p, kind, st, tt, c, k), SePf.conds(P.SePolicy.conds(p), P.SePolicy.state(p), kind, st, tt, c, a0, k), Equal.trans(Bool, Bool.or(Bits.SeBits.has(a0, k), z), Bool.or(T.SeTe.any_covers(P.SePolicy.av(p), kind, st, tt, c, k), z), T.SeTe.covers(p, kind, st, tt, c, k), Equal.cong(Bool, Bool, v => Bool.or(v, z), Bits.SeBits.has(a0, k), T.SeTe.any_covers(P.SePolicy.av(p), kind, st, tt, c, k), SePf.collect(P.SePolicy.av(p), kind, st, tt, c, Nil{}, k)), Equal.sym(Bool, T.SeTe.covers(p, kind, st, tt, c, k), Bool.or(T.SeTe.any_covers(P.SePolicy.av(p), kind, st, tt, c, k), z), SePf.any_append(P.SePolicy.av(p), cav, kind, st, tt, c, k))))

def SePf.apply_go(+f: Bool, +av: List<&2, Bool>, +perms: List<&2, Bool>, +k: Nat) -> {Bits.SeBits.has(K.SeConstraints.apply.go(f, av, perms), k) == Bool.and(Bits.SeBits.has(av, k), Bool.not(Bool.and(f, Bits.SeBits.has(perms, k)))) : Bool}:
  match f:
    case True{}:
      Laws.bits_has_andnot(av, perms, k)
    case False{}:
      SePf.and_true_sym(Bits.SeBits.has(av, k))

def SePf.bool4(+g: Bool, +q: Bool, +v: Bool, +y: Bool) -> {Bool.not(Bool.and(Bool.and(g, Bool.and(q, Bool.not(v))), y)) == Bool.or(Bool.not(Bool.and(g, Bool.and(q, y))), v) : Bool}:
  match g:
    case False{}:
      {==}
    case True{}:
      match q:
        case False{}:
          {==}
        case True{}:
          match v:
            case True{}:
              match y:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match y:
                case True{}:
                  {==}
                case False{}:
                  {==}

def SePf.apply_one(+con: K.SeConstraint, +on: Bool, +s: C.SeContext, +t: C.SeContext, +c: Nat, +av: List<&2, Bool>, +k: Nat) -> {Bits.SeBits.has(K.SeConstraints.apply.one(con, on, s, t, c, av), k) == Bool.and(Bits.SeBits.has(av, k), K.SeConstraint.holds(con, on, s, t, c, k)) : Bool}:
  match con:
    case K.SeConstraint{m, cls, perms, e}:
      +g = Bool.or(Bool.not(m), on)
      +q = Nat.is_eq(cls, c)
      +v = K.SeCexpr.eval(e, s, t)
      +y = Bits.SeBits.has(perms, k)
      Equal.trans(Bool, Bits.SeBits.has(K.SeConstraints.apply.go(Bool.and(g, Bool.and(q, Bool.not(v))), av, perms), k), Bool.and(Bits.SeBits.has(av, k), Bool.not(Bool.and(Bool.and(g, Bool.and(q, Bool.not(v))), y))), Bool.and(Bits.SeBits.has(av, k), Bool.or(Bool.not(Bool.and(g, Bool.and(q, y))), v)), SePf.apply_go(Bool.and(g, Bool.and(q, Bool.not(v))), av, perms, k), Equal.cong(Bool, Bool, w => Bool.and(Bits.SeBits.has(av, k), w), Bool.not(Bool.and(Bool.and(g, Bool.and(q, Bool.not(v))), y)), Bool.or(Bool.not(Bool.and(g, Bool.and(q, y))), v), SePf.bool4(g, q, v, y)))

def SePf.apply(+cs: List<&2, K.SeConstraint>, +on: Bool, +s: C.SeContext, +t: C.SeContext, +c: Nat, +av: List<&2, Bool>, +k: Nat) -> {Bits.SeBits.has(K.SeConstraints.apply(cs, on, s, t, c, av), k) == Bool.and(Bits.SeBits.has(av, k), K.SeConstraints.permits(cs, on, s, t, c, k)) : Bool}:
  match cs:
    case Nil{}:
      SePf.and_true_sym(Bits.SeBits.has(av, k))
    case Con{+con, rest}:
      +a1 = K.SeConstraints.apply.one(con, on, s, t, c, av)
      +x = Bits.SeBits.has(av, k)
      +y = K.SeConstraint.holds(con, on, s, t, c, k)
      +z = K.SeConstraints.permits(rest, on, s, t, c, k)
      Equal.trans(Bool, Bits.SeBits.has(K.SeConstraints.apply(rest, on, s, t, c, a1), k), Bool.and(Bits.SeBits.has(a1, k), z), Bool.and(x, Bool.and(y, z)), SePf.apply(rest, on, s, t, c, a1, k), Equal.trans(Bool, Bool.and(Bits.SeBits.has(a1, k), z), Bool.and(Bool.and(x, y), z), Bool.and(x, Bool.and(y, z)), Equal.cong(Bool, Bool, w => Bool.and(w, z), Bits.SeBits.has(a1, k), Bool.and(x, y), SePf.apply_one(con, on, s, t, c, av, k)), SePf.and_assoc(x, y, z)))

def Laws.av_allowed_exact(p, s, t, c, k):
  +r = A.SeAvc.rules_av(p, P.SeAllow{}, C.SeContext.typ(s), C.SeContext.typ(t), c)
  +z = K.SeConstraints.permits(P.SePolicy.constraints(p), P.SePolicy.mls(p), s, t, c, k)
  Equal.trans(Bool, Bits.SeBits.has(K.SeConstraints.apply(P.SePolicy.constraints(p), P.SePolicy.mls(p), s, t, c, r), k), Bool.and(Bits.SeBits.has(r, k), z), Bool.and(T.SeTe.covers(p, P.SeAllow{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k), z), SePf.apply(P.SePolicy.constraints(p), P.SePolicy.mls(p), s, t, c, r, k), Equal.cong(Bool, Bool, w => Bool.and(w, z), Bits.SeBits.has(r, k), T.SeTe.covers(p, P.SeAllow{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k), SePf.rules(p, P.SeAllow{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k)))

def Laws.av_auditallow_exact(p, s, t, c, k):
  SePf.rules(p, P.SeAuditallow{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k)

def SePf.and_not_cong(-a: Bool, -a2: Bool, -b: Bool, -b2: Bool, +ea: {a == a2 : Bool}, +eb: {b == b2 : Bool}) -> {Bool.and(a, Bool.not(b)) == Bool.and(a2, Bool.not(b2)) : Bool}:
  %ea : {Bool.and(a, Bool.not(b)) == Bool.and(_, Bool.not(b2)) : Bool}
  %eb : {Bool.and(a, Bool.not(b)) == Bool.and(a, Bool.not(_)) : Bool}
  {==}

def Laws.av_auditdeny_exact(p, s, t, c, k):
  +n = A.SeAvc.nperms(p, c)
  +r = A.SeAvc.rules_av(p, P.SeDontaudit{}, C.SeContext.typ(s), C.SeContext.typ(t), c)
  Equal.trans(Bool, Bits.SeBits.has(Bits.SeBits.andnot(Bits.SeBits.full(n), r), k), Bool.and(Bits.SeBits.has(Bits.SeBits.full(n), k), Bool.not(Bits.SeBits.has(r, k))), Bool.and(Nat.is_lt(k, n), Bool.not(T.SeTe.covers(p, P.SeDontaudit{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k))), Laws.bits_has_andnot(Bits.SeBits.full(n), r, k), SePf.and_not_cong(Bits.SeBits.has(Bits.SeBits.full(n), k), Nat.is_lt(k, n), Bits.SeBits.has(r, k), T.SeTe.covers(p, P.SeDontaudit{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k), Laws.bits_has_full(n, k), SePf.rules(p, P.SeDontaudit{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k)))

# what the allowed vector implies

def Laws.allowed_needs_allow(p, s, t, c, k, h):
  +cov = T.SeTe.covers(p, P.SeAllow{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k)
  +per = K.SeConstraints.permits(P.SePolicy.constraints(p), P.SePolicy.mls(p), s, t, c, k)
  +x = Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(p, s, t, c)), k)
  SePf.and_l(cov, per, Equal.trans(Bool, Bool.and(cov, per), x, True{}, Equal.sym(Bool, x, Bool.and(cov, per), Laws.av_allowed_exact(p, s, t, c, k)), h))

def SePf.permits_of(+p: P.SePolicy, +s: C.SeContext, +t: C.SeContext, +c: Nat, +k: Nat, +h: {Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(p, s, t, c)), k) == True{} : Bool}) -> {K.SeConstraints.permits(P.SePolicy.constraints(p), P.SePolicy.mls(p), s, t, c, k) == True{} : Bool}:
  +cov = T.SeTe.covers(p, P.SeAllow{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k)
  +per = K.SeConstraints.permits(P.SePolicy.constraints(p), P.SePolicy.mls(p), s, t, c, k)
  +x = Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(p, s, t, c)), k)
  SePf.and_r(cov, per, Equal.trans(Bool, Bool.and(cov, per), x, True{}, Equal.sym(Bool, x, Bool.and(cov, per), Laws.av_allowed_exact(p, s, t, c, k)), h))

# a constraint that holds holds as one of its kind
def SePf.holds_kind(+m: Bool, +on: Bool, +want: Bool, +q: Bool, +v: Bool, +h: {Bool.or(Bool.not(Bool.and(Bool.or(Bool.not(m), on), q)), v) == True{} : Bool}, +g: {Bool.or(Bool.not(want), on) == True{} : Bool}) -> {Bool.or(Bool.not(Bool.and(Bool.not(Bool.xor(m, want)), q)), v) == True{} : Bool}:
  match m:
    case True{}:
      match on:
        case True{}:
          match want:
            case True{}:
              match q:
                case True{}:
                  h
                case False{}:
                  {==}
            case False{}:
              {==}
        case False{}:
          match want:
            case True{}:
              SePf.absurd({Bool.or(Bool.not(Bool.and(Bool.not(Bool.xor(True{}, True{})), q)), v) == True{} : Bool}, g)
            case False{}:
              {==}
    case False{}:
      match want:
        case True{}:
          {==}
        case False{}:
          h

def SePf.permits_kind(+cs: List<&2, K.SeConstraint>, +on: Bool, +want: Bool, +s: C.SeContext, +t: C.SeContext, +c: Nat, +k: Nat, +h: {K.SeConstraints.permits(cs, on, s, t, c, k) == True{} : Bool}, +g: {Bool.or(Bool.not(want), on) == True{} : Bool}) -> {K.SeConstraints.permits_kind(cs, want, s, t, c, k) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{con, rest}:
      match con:
        case K.SeConstraint{m, cls, perms, e}:
          +q = Bool.and(Nat.is_eq(cls, c), Bits.SeBits.has(perms, k))
          +v = K.SeCexpr.eval(e, s, t)
          +hd = Bool.or(Bool.not(Bool.and(Bool.or(Bool.not(m), on), q)), v)
          +tl = K.SeConstraints.permits(rest, on, s, t, c, k)
          SePf.and_intro(Bool.or(Bool.not(Bool.and(Bool.not(Bool.xor(m, want)), q)), v), K.SeConstraints.permits_kind(rest, want, s, t, c, k), SePf.holds_kind(m, on, want, q, v, SePf.and_l(hd, tl, h), g), SePf.permits_kind(rest, on, want, s, t, c, k, SePf.and_r(hd, tl, h), g))

def Laws.allowed_needs_constraints(p, s, t, c, k, h):
  SePf.permits_kind(P.SePolicy.constraints(p), P.SePolicy.mls(p), False{}, s, t, c, k, SePf.permits_of(p, s, t, c, k, h), {==})

def Laws.allowed_needs_mls(p, s, t, c, k, m, h):
  SePf.permits_kind(P.SePolicy.constraints(p), P.SePolicy.mls(p), True{}, s, t, c, k, SePf.permits_of(p, s, t, c, k, h), m)

# Decisions

def SePf.decide_enf(+x: Bool, +req: List<&2, Bool>, +avd: A.SeAvd) -> {A.SeDecision.granted(A.SeAvc.decide(x, False{}, req, avd)) == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def SePf.decide_len(+x: Bool, +req: List<&2, Bool>, +avd: A.SeAvd) -> {A.SeDecision.granted(A.SeAvc.decide(x, True{}, req, avd)) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.granted_enforcing(o, p, s, t, c, k, h):
  +avd = A.SeAvc.compute(p, s, t, c)
  +al = A.SeAvd.allowed(avd)
  %Equal.sym(Bool, A.SeAvc.lenient(o, p, s), False{}, h) : {A.SeDecision.granted(A.SeAvc.decide(Bits.SeBits.subset(Bits.SeBits.single(k), al), _, Bits.SeBits.single(k), avd)) == Bits.SeBits.has(al, k) : Bool}
  %Equal.sym(Bool, Bits.SeBits.subset(Bits.SeBits.single(k), al), Bits.SeBits.has(al, k), Laws.bits_subset_single(k, al)) : {A.SeDecision.granted(A.SeAvc.decide(_, False{}, Bits.SeBits.single(k), avd)) == Bits.SeBits.has(al, k) : Bool}
  SePf.decide_enf(Bits.SeBits.has(al, k), Bits.SeBits.single(k), avd)

def SePf.not_of_false(+x: Bool, +h: {x == False{} : Bool}) -> {Bool.not(x) == True{} : Bool}:
  match x:
    case True{}:
      SePf.absurd2({False{} == True{} : Bool}, h)
    case False{}:
      {==}

def Laws.permissive_grants(o, p, s, t, c, req, h):
  +avd = A.SeAvc.compute(p, s, t, c)
  +sub = Bits.SeBits.subset(req, A.SeAvd.allowed(avd))
  +rest = Bool.and(A.SeOptions.permissive_types(o), Bits.SeBits.has(P.SePolicy.permissive(p), C.SeContext.typ(s)))
  +len = SePf.or_l(Bool.not(A.SeOptions.enforcing(o)), rest, SePf.not_of_false(A.SeOptions.enforcing(o), h))
  %Equal.sym(Bool, A.SeAvc.lenient(o, p, s), True{}, len) : {A.SeDecision.granted(A.SeAvc.decide(sub, _, req, avd)) == True{} : Bool}
  SePf.decide_len(sub, req, avd)

def Laws.permissive_type_grants(o, p, s, t, c, req, h1, h2):
  +avd = A.SeAvc.compute(p, s, t, c)
  +sub = Bits.SeBits.subset(req, A.SeAvd.allowed(avd))
  +pt = A.SeOptions.permissive_types(o)
  +hs = Bits.SeBits.has(P.SePolicy.permissive(p), C.SeContext.typ(s))
  +len = SePf.or_r(Bool.not(A.SeOptions.enforcing(o)), Bool.and(pt, hs), SePf.and_intro(pt, hs, h1, h2))
  %Equal.sym(Bool, A.SeAvc.lenient(o, p, s), True{}, len) : {A.SeDecision.granted(A.SeAvc.decide(sub, _, req, avd)) == True{} : Bool}
  SePf.decide_len(sub, req, avd)

# Case analysis on or(x, y) == True
def SePf.or_cases(-R: Type, +x: Bool, +y: Bool, +h: {Bool.or(x, y) == True{} : Bool}, ft: {x == True{} : Bool} -> R, ff: {y == True{} : Bool} -> R) -> R:
  match x:
    case True{}:
      ft({==})
    case False{}:
      ff(h)

def SePf.and_false_l(+a: Bool, +b: Bool, +h: {a == False{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case True{}:
      SePf.absurd2({Bool.and(True{}, b) == False{} : Bool}, h)
    case False{}:
      {==}

# Booleans: the conditional rules in force, when none in either branch
# covers an access, cover nothing

def SePf.pick_none(+b: Bool, +xs: List<&2, P.SeAvRule>, +ys: List<&2, P.SeAvRule>, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, +k: Nat, +hx: {T.SeTe.any_covers(xs, kind, st, tt, c, k) == False{} : Bool}, +hy: {T.SeTe.any_covers(ys, kind, st, tt, c, k) == False{} : Bool}) -> {T.SeTe.any_covers(T.SeTe.pick(List<&2, P.SeAvRule>, b, xs, ys), kind, st, tt, c, k) == False{} : Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# an append covers nothing: neither part does
def SePf.append_none_l(+xs: List<&2, P.SeAvRule>, +ys: List<&2, P.SeAvRule>, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, +k: Nat, +h: {T.SeTe.any_covers(List.append(&2, P.SeAvRule, xs, ys), kind, st, tt, c, k) == False{} : Bool}) -> {T.SeTe.any_covers(xs, kind, st, tt, c, k) == False{} : Bool}:
  +a = T.SeTe.any_covers(xs, kind, st, tt, c, k)
  +b = T.SeTe.any_covers(ys, kind, st, tt, c, k)
  SePf.nor_l(a, b, Equal.trans(Bool, Bool.or(a, b), T.SeTe.any_covers(List.append(&2, P.SeAvRule, xs, ys), kind, st, tt, c, k), False{}, Equal.sym(Bool, T.SeTe.any_covers(List.append(&2, P.SeAvRule, xs, ys), kind, st, tt, c, k), Bool.or(a, b), SePf.any_append(xs, ys, kind, st, tt, c, k)), h))

def SePf.append_none_r(+xs: List<&2, P.SeAvRule>, +ys: List<&2, P.SeAvRule>, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, +k: Nat, +h: {T.SeTe.any_covers(List.append(&2, P.SeAvRule, xs, ys), kind, st, tt, c, k) == False{} : Bool}) -> {T.SeTe.any_covers(ys, kind, st, tt, c, k) == False{} : Bool}:
  +a = T.SeTe.any_covers(xs, kind, st, tt, c, k)
  +b = T.SeTe.any_covers(ys, kind, st, tt, c, k)
  SePf.nor_r(a, b, Equal.trans(Bool, Bool.or(a, b), T.SeTe.any_covers(List.append(&2, P.SeAvRule, xs, ys), kind, st, tt, c, k), False{}, Equal.sym(Bool, T.SeTe.any_covers(List.append(&2, P.SeAvRule, xs, ys), kind, st, tt, c, k), Bool.or(a, b), SePf.any_append(xs, ys, kind, st, tt, c, k)), h))

def SePf.append_none(+xs: List<&2, P.SeAvRule>, +ys: List<&2, P.SeAvRule>, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, +k: Nat, +hx: {T.SeTe.any_covers(xs, kind, st, tt, c, k) == False{} : Bool}, +hy: {T.SeTe.any_covers(ys, kind, st, tt, c, k) == False{} : Bool}) -> {T.SeTe.any_covers(List.append(&2, P.SeAvRule, xs, ys), kind, st, tt, c, k) == False{} : Bool}:
  +a = T.SeTe.any_covers(xs, kind, st, tt, c, k)
  +b = T.SeTe.any_covers(ys, kind, st, tt, c, k)
  Equal.trans(Bool, T.SeTe.any_covers(List.append(&2, P.SeAvRule, xs, ys), kind, st, tt, c, k), Bool.or(a, b), False{}, SePf.any_append(xs, ys, kind, st, tt, c, k), SePf.nor_intro(a, b, hx, hy))

def SePf.cond_none(+cs: List<&2, P.SeCond>, +bs: List<&2, Bool>, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, +k: Nat, +h: {T.SeTe.any_covers(T.SeTe.cond_all_av(cs), kind, st, tt, c, k) == False{} : Bool}) -> {T.SeTe.any_covers(T.SeTe.cond_av(cs, bs), kind, st, tt, c, k) == False{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{cd, t}:
      match cd:
        case P.SeCond{e, tav, tty, fav, fty}:
          +both = List.append(&2, P.SeAvRule, tav, fav)
          +hb = SePf.append_none_l(both, T.SeTe.cond_all_av(t), kind, st, tt, c, k, h)
          +ht = SePf.append_none_r(both, T.SeTe.cond_all_av(t), kind, st, tt, c, k, h)
          SePf.append_none(T.SeTe.pick(List<&2, P.SeAvRule>, P.SeBexpr.eval(e, bs), tav, fav), T.SeTe.cond_av(t, bs), kind, st, tt, c, k, SePf.pick_none(P.SeBexpr.eval(e, bs), tav, fav, kind, st, tt, c, k, SePf.append_none_l(tav, fav, kind, st, tt, c, k, hb), SePf.append_none_r(tav, fav, kind, st, tt, c, k, hb)), SePf.cond_none(t, bs, kind, st, tt, c, k, ht))

# rules in force under any booleans, when no conditional rule covers the
# access: exactly the unconditional ones
def SePf.cov_nc(+avs: List<&2, P.SeAvRule>, +cs: List<&2, P.SeCond>, +bs: List<&2, Bool>, +kind: P.SeAvKind, +st: Nat, +tt: Nat, +c: Nat, +k: Nat, +h: {T.SeTe.any_covers(T.SeTe.cond_all_av(cs), kind, st, tt, c, k) == False{} : Bool}) -> {T.SeTe.any_covers(List.append(&2, P.SeAvRule, avs, T.SeTe.cond_av(cs, bs)), kind, st, tt, c, k) == T.SeTe.any_covers(avs, kind, st, tt, c, k) : Bool}:
  +a = T.SeTe.any_covers(avs, kind, st, tt, c, k)
  +b = T.SeTe.any_covers(T.SeTe.cond_av(cs, bs), kind, st, tt, c, k)
  Equal.trans(Bool, T.SeTe.any_covers(List.append(&2, P.SeAvRule, avs, T.SeTe.cond_av(cs, bs)), kind, st, tt, c, k), Bool.or(a, b), a, SePf.any_append(avs, T.SeTe.cond_av(cs, bs), kind, st, tt, c, k), Equal.trans(Bool, Bool.or(a, b), Bool.or(a, False{}), a, Equal.cong(Bool, Bool, v => Bool.or(a, v), b, False{}, SePf.cond_none(cs, bs, kind, st, tt, c, k, h)), SePf.or_false(a)))

def Laws.bool_only_conditional(p, bs, kind, st, tt, c, k, h):
  match p:
    case P.SePolicy{d, r, m, old}:
      +avs = P.SeRules.av(r)
      +cs = P.SeRules.conds(r)
      Equal.trans(Bool, T.SeTe.any_covers(List.append(&2, P.SeAvRule, avs, T.SeTe.cond_av(cs, bs)), kind, st, tt, c, k), T.SeTe.any_covers(avs, kind, st, tt, c, k), T.SeTe.any_covers(List.append(&2, P.SeAvRule, avs, T.SeTe.cond_av(cs, old)), kind, st, tt, c, k), SePf.cov_nc(avs, cs, bs, kind, st, tt, c, k, h), Equal.sym(Bool, T.SeTe.any_covers(List.append(&2, P.SeAvRule, avs, T.SeTe.cond_av(cs, old)), kind, st, tt, c, k), T.SeTe.any_covers(avs, kind, st, tt, c, k), SePf.cov_nc(avs, cs, old, kind, st, tt, c, k, h)))

def Laws.bool_av_independent(p, bs, s, t, c, k, h):
  match p:
    case P.SePolicy{d, r, m, old}:
      +p0 = {P.SePolicy{d, r, m, old} : P.SePolicy}
      +p1 = {P.SePolicy{d, r, m, bs} : P.SePolicy}
      +per = K.SeConstraints.permits(P.SeRules.constraints(r), m, s, t, c, k)
      +c1 = T.SeTe.covers(p1, P.SeAllow{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k)
      +c0 = T.SeTe.covers(p0, P.SeAllow{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k)
      Equal.trans(Bool, Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(p1, s, t, c)), k), Bool.and(c1, per), Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(p0, s, t, c)), k), Laws.av_allowed_exact(p1, s, t, c, k), Equal.trans(Bool, Bool.and(c1, per), Bool.and(c0, per), Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(p0, s, t, c)), k), Equal.cong(Bool, Bool, v => Bool.and(v, per), c1, c0, Laws.bool_only_conditional(p0, bs, P.SeAllow{}, C.SeContext.typ(s), C.SeContext.typ(t), c, k, h)), Equal.sym(Bool, Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(p0, s, t, c)), k), Bool.and(c0, per), Laws.av_allowed_exact(p0, s, t, c, k))))

# Neverallow: the check finds every conflict

def SePf.cls_eq(+x: Nat, +y: Nat, +c: Nat, +hx: {Nat.is_eq(x, c) == True{} : Bool}, +hy: {Nat.is_eq(y, c) == True{} : Bool}) -> {Nat.is_eq(x, y) == True{} : Bool}:
  +ex = SePf.nat_eq_true(x, c, hx)
  +ey = SePf.nat_eq_true(y, c, hy)
  %Equal.sym(Nat, x, c, ex) : {Nat.is_eq(_, y) == True{} : Bool}
  %Equal.sym(Nat, y, c, ey) : {Nat.is_eq(c, _) == True{} : Bool}
  SePf.nat_eq_refl(c)

# both sets hold i: their intersection is not empty
def SePf.meets(+a: List<&2, Bool>, +b: List<&2, Bool>, +i: Nat, +ha: {Bits.SeBits.has(a, i) == True{} : Bool}, +hb: {Bits.SeBits.has(b, i) == True{} : Bool}) -> {Bits.SeBits.any(Bits.SeBits.and(a, b)) == True{} : Bool}:
  Laws.bits_any_has(Bits.SeBits.and(a, b), i, Equal.trans(Bool, Bits.SeBits.has(Bits.SeBits.and(a, b), i), Bool.and(Bits.SeBits.has(a, i), Bits.SeBits.has(b, i)), True{}, Laws.bits_has_and(a, b, i), SePf.and_intro(Bits.SeBits.has(a, i), Bits.SeBits.has(b, i), ha, hb)))

def SePf.has_and(+a: List<&2, Bool>, +b: List<&2, Bool>, +i: Nat, +ha: {Bits.SeBits.has(a, i) == True{} : Bool}, +hb: {Bits.SeBits.has(b, i) == True{} : Bool}) -> {Bits.SeBits.has(Bits.SeBits.and(a, b), i) == True{} : Bool}:
  Equal.trans(Bool, Bits.SeBits.has(Bits.SeBits.and(a, b), i), Bool.and(Bits.SeBits.has(a, i), Bits.SeBits.has(b, i)), True{}, Laws.bits_has_and(a, b, i), SePf.and_intro(Bits.SeBits.has(a, i), Bits.SeBits.has(b, i), ha, hb))

# s = t moves a membership from t to s
def SePf.move(+b: List<&2, Bool>, +st: Nat, +tt: Nat, +e: {Nat.is_eq(st, tt) == True{} : Bool}, +h: {Bits.SeBits.has(b, tt) == True{} : Bool}) -> {Bits.SeBits.has(b, st) == True{} : Bool}:
  +q = SePf.nat_eq_true(st, tt, e)
  %Equal.sym(Nat, st, tt, q) : {Bits.SeBits.has(b, _) == True{} : Bool}
  h

def SePf.meet.go(+nsrc: List<&2, Bool>, +asrc: List<&2, Bool>, +ntgt: List<&2, Bool>, +atgt: List<&2, Bool>, +nself: Bool, +aself: Bool, +st: Nat, +tt: Nat, +x1: Bool, +x2: Bool, +e1: {Bits.SeBits.has(ntgt, tt) == x1 : Bool}, +e2: {Bits.SeBits.has(atgt, tt) == x2 : Bool}, +tn: {Bool.or(x1, Bool.and(nself, Nat.is_eq(st, tt))) == True{} : Bool}, +ta: {Bool.or(x2, Bool.and(aself, Nat.is_eq(st, tt))) == True{} : Bool}, +sn: {Bits.SeBits.has(nsrc, st) == True{} : Bool}, +sa: {Bits.SeBits.has(asrc, st) == True{} : Bool}) -> {Bool.or(T.SeTe.meet_tt(nsrc, asrc, ntgt, atgt), Bool.or(T.SeTe.meet_ts(nsrc, asrc, ntgt, aself), Bool.or(T.SeTe.meet_st(nsrc, asrc, atgt, nself), T.SeTe.meet_ss(nsrc, asrc, nself, aself)))) == True{} : Bool}:
  match x1:
    case True{}:
      match x2:
        case True{}:
          +s2 = Bits.SeBits.and(nsrc, asrc)
          +hs = SePf.has_and(nsrc, asrc, st, sn, sa)
          +mtt = T.SeTe.meet_tt(nsrc, asrc, ntgt, atgt)
          +mts = T.SeTe.meet_ts(nsrc, asrc, ntgt, aself)
          +mst = T.SeTe.meet_st(nsrc, asrc, atgt, nself)
          +mss = T.SeTe.meet_ss(nsrc, asrc, nself, aself)
          SePf.or_l(mtt, Bool.or(mts, Bool.or(mst, mss)), SePf.and_intro(Bits.SeBits.any(s2), Bits.SeBits.any(Bits.SeBits.and(ntgt, atgt)), SePf.meets(nsrc, asrc, st, sn, sa), SePf.meets(ntgt, atgt, tt, e1, e2)))
        case False{}:
          +s2 = Bits.SeBits.and(nsrc, asrc)
          +hs = SePf.has_and(nsrc, asrc, st, sn, sa)
          +mtt = T.SeTe.meet_tt(nsrc, asrc, ntgt, atgt)
          +mts = T.SeTe.meet_ts(nsrc, asrc, ntgt, aself)
          +mst = T.SeTe.meet_st(nsrc, asrc, atgt, nself)
          +mss = T.SeTe.meet_ss(nsrc, asrc, nself, aself)
          +eq = SePf.and_r(aself, Nat.is_eq(st, tt), ta)
          SePf.or_r(mtt, Bool.or(mts, Bool.or(mst, mss)), SePf.or_l(mts, Bool.or(mst, mss), SePf.and_intro(aself, Bits.SeBits.any(Bits.SeBits.and(s2, ntgt)), SePf.and_l(aself, Nat.is_eq(st, tt), ta), SePf.meets(s2, ntgt, st, hs, SePf.move(ntgt, st, tt, eq, e1)))))
    case False{}:
      match x2:
        case True{}:
          +s2 = Bits.SeBits.and(nsrc, asrc)
          +hs = SePf.has_and(nsrc, asrc, st, sn, sa)
          +mtt = T.SeTe.meet_tt(nsrc, asrc, ntgt, atgt)
          +mts = T.SeTe.meet_ts(nsrc, asrc, ntgt, aself)
          +mst = T.SeTe.meet_st(nsrc, asrc, atgt, nself)
          +mss = T.SeTe.meet_ss(nsrc, asrc, nself, aself)
          +eq = SePf.and_r(nself, Nat.is_eq(st, tt), tn)
          SePf.or_r(mtt, Bool.or(mts, Bool.or(mst, mss)), SePf.or_r(mts, Bool.or(mst, mss), SePf.or_l(mst, mss, SePf.and_intro(nself, Bits.SeBits.any(Bits.SeBits.and(s2, atgt)), SePf.and_l(nself, Nat.is_eq(st, tt), tn), SePf.meets(s2, atgt, st, hs, SePf.move(atgt, st, tt, eq, e2))))))
        case False{}:
          +s2 = Bits.SeBits.and(nsrc, asrc)
          +hs = SePf.has_and(nsrc, asrc, st, sn, sa)
          +mtt = T.SeTe.meet_tt(nsrc, asrc, ntgt, atgt)
          +mts = T.SeTe.meet_ts(nsrc, asrc, ntgt, aself)
          +mst = T.SeTe.meet_st(nsrc, asrc, atgt, nself)
          +mss = T.SeTe.meet_ss(nsrc, asrc, nself, aself)
          SePf.or_r(mtt, Bool.or(mts, Bool.or(mst, mss)), SePf.or_r(mts, Bool.or(mst, mss), SePf.or_r(mst, mss, SePf.and_intro(nself, Bool.and(aself, Bits.SeBits.any(s2)), SePf.and_l(nself, Nat.is_eq(st, tt), tn), SePf.and_intro(aself, Bits.SeBits.any(s2), SePf.and_l(aself, Nat.is_eq(st, tt), ta), Laws.bits_any_has(s2, st, hs))))))

# a neverallow rule and an allow rule that cover the same access conflict
def SePf.conflict_complete(+n: P.SeAvRule, +a: P.SeAvRule, +st: Nat, +tt: Nat, +c: Nat, +k: Nat, +h1: {T.SeTe.rule_covers(n, P.SeNeverallow{}, st, tt, c, k) == True{} : Bool}, +h2: {T.SeTe.rule_covers(a, P.SeAllow{}, st, tt, c, k) == True{} : Bool}) -> {T.SeTe.conflict(n, a) == True{} : Bool}:
  match n:
    case P.SeAvRule{nk, nsrc, ntgt, nself, ncls, nperms}:
      match a:
        case P.SeAvRule{ak, asrc, atgt, aself, acls, aperms}:
          +kn = P.SeAvKind.is_eq(P.SeNeverallow{}, nk)
          +sn = Bits.SeBits.has(nsrc, st)
          +tn = Bool.or(Bits.SeBits.has(ntgt, tt), Bool.and(nself, Nat.is_eq(st, tt)))
          +cn = Nat.is_eq(ncls, c)
          +ka = P.SeAvKind.is_eq(P.SeAllow{}, ak)
          +sa = Bits.SeBits.has(asrc, st)
          +ta = Bool.or(Bits.SeBits.has(atgt, tt), Bool.and(aself, Nat.is_eq(st, tt)))
          +ca = Nat.is_eq(acls, c)
          +mn = SePf.and_l(Bool.and(kn, Bool.and(sn, Bool.and(tn, cn))), Bits.SeBits.has(nperms, k), h1)
          +pn = SePf.and_r(Bool.and(kn, Bool.and(sn, Bool.and(tn, cn))), Bits.SeBits.has(nperms, k), h1)
          +rn1 = SePf.and_r(kn, Bool.and(sn, Bool.and(tn, cn)), mn)
          +rn2 = SePf.and_r(sn, Bool.and(tn, cn), rn1)
          +ma = SePf.and_l(Bool.and(ka, Bool.and(sa, Bool.and(ta, ca))), Bits.SeBits.has(aperms, k), h2)
          +pa = SePf.and_r(Bool.and(ka, Bool.and(sa, Bool.and(ta, ca))), Bits.SeBits.has(aperms, k), h2)
          +ra1 = SePf.and_r(ka, Bool.and(sa, Bool.and(ta, ca)), ma)
          +ra2 = SePf.and_r(sa, Bool.and(ta, ca), ra1)
          +tm = Bool.or(T.SeTe.meet_tt(nsrc, asrc, ntgt, atgt), Bool.or(T.SeTe.meet_ts(nsrc, asrc, ntgt, aself), Bool.or(T.SeTe.meet_st(nsrc, asrc, atgt, nself), T.SeTe.meet_ss(nsrc, asrc, nself, aself))))
          +pm = Bits.SeBits.any(Bits.SeBits.and(nperms, aperms))
          SePf.and_intro(kn, Bool.and(ka, Bool.and(Nat.is_eq(ncls, acls), Bool.and(pm, tm))), SePf.and_l(kn, Bool.and(sn, Bool.and(tn, cn)), mn), SePf.and_intro(ka, Bool.and(Nat.is_eq(ncls, acls), Bool.and(pm, tm)), SePf.and_l(ka, Bool.and(sa, Bool.and(ta, ca)), ma), SePf.and_intro(Nat.is_eq(ncls, acls), Bool.and(pm, tm), SePf.cls_eq(ncls, acls, c, SePf.and_r(tn, cn, rn2), SePf.and_r(ta, ca, ra2)), SePf.and_intro(pm, tm, SePf.meets(nperms, aperms, k, pn, pa), SePf.meet.go(nsrc, asrc, ntgt, atgt, nself, aself, st, tt, Bits.SeBits.has(ntgt, tt), Bits.SeBits.has(atgt, tt), {==}, {==}, SePf.and_l(tn, cn, rn2), SePf.and_l(ta, ca, ra2), SePf.and_l(sn, Bool.and(tn, cn), rn1), SePf.and_l(sa, Bool.and(ta, ca), ra1))))))

def SePf.never_one.cov(+n: P.SeAvRule, +a: P.SeAvRule, +st: Nat, +tt: Nat, +c: Nat, +k: Nat, +x: Bool, +e: {T.SeTe.rule_covers(a, P.SeAllow{}, st, tt, c, k) == x : Bool}, +hn: {T.SeTe.rule_covers(n, P.SeNeverallow{}, st, tt, c, k) == True{} : Bool}, +nc: {T.SeTe.conflict(n, a) == False{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      SePf.clash({True{} == False{} : Bool}, T.SeTe.conflict(n, a), SePf.conflict_complete(n, a, st, tt, c, k, hn, e), nc)
    case False{}:
      {==}

# a rule of another kind covers nothing of this kind
def SePf.cov_kind_false(+kind: P.SeAvKind, +a: P.SeAvRule, +st: Nat, +tt: Nat, +c: Nat, +k: Nat, +e: {P.SeAvKind.is_eq(kind, P.SeAvRule.kind(a)) == False{} : Bool}) -> {T.SeTe.rule_covers(a, kind, st, tt, c, k) == False{} : Bool}:
  match a:
    case P.SeAvRule{rk, src, tgt, self, cls, perms}:
      +rest = Bool.and(Bits.SeBits.has(src, st), Bool.and(Bool.or(Bits.SeBits.has(tgt, tt), Bool.and(self, Nat.is_eq(st, tt))), Nat.is_eq(cls, c)))
      SePf.and_false_l(Bool.and(P.SeAvKind.is_eq(kind, rk), rest), Bits.SeBits.has(perms, k), SePf.and_false_l(P.SeAvKind.is_eq(kind, rk), rest, e))

def SePf.one_step_rest(+b: Bool, +n: P.SeAvRule, +a: P.SeAvRule, +rest: Bool, +hs: {T.SeTe.never_ok_one.step(b, n, a, rest) == True{} : Bool}) -> {rest == True{} : Bool}:
  match b:
    case True{}:
      SePf.and_r(Bool.not(T.SeTe.conflict(n, a)), rest, hs)
    case False{}:
      hs

def SePf.one_step_cov(+n: P.SeAvRule, +a: P.SeAvRule, +st: Nat, +tt: Nat, +c: Nat, +k: Nat, +rest: Bool, +b: Bool, +e: {P.SeAvKind.is_eq(P.SeAllow{}, P.SeAvRule.kind(a)) == b : Bool}, +hs: {T.SeTe.never_ok_one.step(b, n, a, rest) == True{} : Bool}, +hn: {T.SeTe.rule_covers(n, P.SeNeverallow{}, st, tt, c, k) == True{} : Bool}) -> {T.SeTe.rule_covers(a, P.SeAllow{}, st, tt, c, k) == False{} : Bool}:
  match b:
    case True{}:
      +nc = SePf.not_true(T.SeTe.conflict(n, a), SePf.and_l(Bool.not(T.SeTe.conflict(n, a)), rest, hs))
      SePf.never_one.cov(n, a, st, tt, c, k, T.SeTe.rule_covers(a, P.SeAllow{}, st, tt, c, k), {==}, hn, nc)
    case False{}:
      SePf.cov_kind_false(P.SeAllow{}, a, st, tt, c, k, e)

def SePf.never_one(+ars: List<&2, P.SeAvRule>, +n: P.SeAvRule, +st: Nat, +tt: Nat, +c: Nat, +k: Nat, +hok: {T.SeTe.never_ok_one(ars, n) == True{} : Bool}, +hn: {T.SeTe.rule_covers(n, P.SeNeverallow{}, st, tt, c, k) == True{} : Bool}) -> {T.SeTe.any_covers(ars, P.SeAllow{}, st, tt, c, k) == False{} : Bool}:
  match ars:
    case Nil{}:
      {==}
    case Con{a, t}:
      +b = P.SeAvKind.is_eq(P.SeAllow{}, P.SeAvRule.kind(a))
      +rest = T.SeTe.never_ok_one(t, n)
      SePf.nor_intro(T.SeTe.rule_covers(a, P.SeAllow{}, st, tt, c, k), T.SeTe.any_covers(t, P.SeAllow{}, st, tt, c, k), SePf.one_step_cov(n, a, st, tt, c, k, rest, b, {==}, hok, hn), SePf.never_one(t, n, st, tt, c, k, SePf.one_step_rest(b, n, a, rest, hok), hn))

def SePf.all_step_rest(+b: Bool, +n: P.SeAvRule, +ars: List<&2, P.SeAvRule>, +rest: Bool, +hs: {T.SeTe.never_ok.step(b, n, ars, rest) == True{} : Bool}) -> {rest == True{} : Bool}:
  match b:
    case True{}:
      SePf.and_r(T.SeTe.never_ok_one(ars, n), rest, hs)
    case False{}:
      hs

def SePf.all_step_one(+n: P.SeAvRule, +ars: List<&2, P.SeAvRule>, +st: Nat, +tt: Nat, +c: Nat, +k: Nat, +rest: Bool, +b: Bool, +e: {P.SeAvKind.is_eq(P.SeNeverallow{}, P.SeAvRule.kind(n)) == b : Bool}, +hs: {T.SeTe.never_ok.step(b, n, ars, rest) == True{} : Bool}, +hx: {T.SeTe.rule_covers(n, P.SeNeverallow{}, st, tt, c, k) == True{} : Bool}) -> {T.SeTe.never_ok_one(ars, n) == True{} : Bool}:
  match b:
    case True{}:
      SePf.and_l(T.SeTe.never_ok_one(ars, n), rest, hs)
    case False{}:
      SePf.clash({T.SeTe.never_ok_one(ars, n) == True{} : Bool}, T.SeTe.rule_covers(n, P.SeNeverallow{}, st, tt, c, k), hx, SePf.cov_kind_false(P.SeNeverallow{}, n, st, tt, c, k, e))

def SePf.never_all(+ns: List<&2, P.SeAvRule>, +ars: List<&2, P.SeAvRule>, +st: Nat, +tt: Nat, +c: Nat, +k: Nat, +hok: {T.SeTe.never_ok(ns, ars) == True{} : Bool}, +hn: {T.SeTe.any_covers(ns, P.SeNeverallow{}, st, tt, c, k) == True{} : Bool}) -> {T.SeTe.any_covers(ars, P.SeAllow{}, st, tt, c, k) == False{} : Bool}:
  match ns:
    case Nil{}:
      SePf.absurd({T.SeTe.any_covers(ars, P.SeAllow{}, st, tt, c, k) == False{} : Bool}, hn)
    case Con{n, t}:
      +b = P.SeAvKind.is_eq(P.SeNeverallow{}, P.SeAvRule.kind(n))
      +rest = T.SeTe.never_ok(t, ars)
      SePf.or_cases({T.SeTe.any_covers(ars, P.SeAllow{}, st, tt, c, k) == False{} : Bool}, T.SeTe.rule_covers(n, P.SeNeverallow{}, st, tt, c, k), T.SeTe.any_covers(t, P.SeNeverallow{}, st, tt, c, k), hn, +hx => SePf.never_one(ars, n, st, tt, c, k, SePf.all_step_one(n, ars, st, tt, c, k, rest, b, {==}, hok, hx), hx), hy => SePf.never_all(t, ars, st, tt, c, k, SePf.all_step_rest(b, n, ars, rest, hok), hy))

def Laws.neverallow_sound(p, st, tt, c, k, ok, h):
  SePf.never_all(P.SePolicy.av(p), T.SeTe.all_av(p), st, tt, c, k, ok, h)

def Laws.neverallow_never_allowed(p, s, t, c, k, ok, h):
  +st = C.SeContext.typ(s)
  +tt = C.SeContext.typ(t)
  +avs = P.SePolicy.av(p)
  +call = T.SeTe.cond_all_av(P.SePolicy.conds(p))
  +ev = Laws.neverallow_sound(p, st, tt, c, k, ok, h)
  +cov0 = SePf.append_none(avs, T.SeTe.cond_av(P.SePolicy.conds(p), P.SePolicy.state(p)), P.SeAllow{}, st, tt, c, k, SePf.append_none_l(avs, call, P.SeAllow{}, st, tt, c, k, ev), SePf.cond_none(P.SePolicy.conds(p), P.SePolicy.state(p), P.SeAllow{}, st, tt, c, k, SePf.append_none_r(avs, call, P.SeAllow{}, st, tt, c, k, ev)))
  +cov = T.SeTe.covers(p, P.SeAllow{}, st, tt, c, k)
  +per = K.SeConstraints.permits(P.SePolicy.constraints(p), P.SePolicy.mls(p), s, t, c, k)
  Equal.trans(Bool, Bits.SeBits.has(A.SeAvd.allowed(A.SeAvc.compute(p, s, t, c)), k), Bool.and(cov, per), False{}, Laws.av_allowed_exact(p, s, t, c, k), SePf.and_false_l(cov, per, cov0))

# The load-time check

def SePf.rdisc(r: Result<&2, &2, P.SeError, P.SePolicy>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{x}:
      Empty

def SePf.fail_done(-e: P.SeError, -p: P.SePolicy, +h: {Fail{e} == Done{p} : Result<&2, &2, P.SeError, P.SePolicy>}) -> SePf.rdisc(Done{p}):
  %h : SePf.rdisc(_)
  Unit{}

def SePf.vfail(+m: Maybe<&2, P.SeConflict>, -p: P.SePolicy, +h: {S.Selinux.validate.fail(m) == Done{p} : Result<&2, &2, P.SeError, P.SePolicy>}) -> Empty:
  match m:
    case None{}:
      SePf.fail_done(P.SeErrSyntax{"neverallow"}, p, h)
    case Some{c}:
      match c:
        case P.SeConflict{n, a}:
          SePf.fail_done(P.SeErrNeverallow{n, a}, p, h)

def SePf.tfail(+m: Maybe<&2, T.SeTransConflict>, -p: P.SePolicy, +h: {S.Selinux.validate.trans_fail(m) == Done{p} : Result<&2, &2, P.SeError, P.SePolicy>}) -> Empty:
  match m:
    case None{}:
      SePf.fail_done(P.SeErrSyntax{"transition conflict"}, p, h)
    case Some{c}:
      match c:
        case T.SeTyClash{a, b}:
          SePf.fail_done(P.SeErrTypeConflict{a, b}, p, h)
        case T.SeRoleClash{a, b}:
          SePf.fail_done(P.SeErrRoleTransConflict{a, b}, p, h)

# the transition check answers the policy it was given, or fails
def SePf.tsame(+q: P.SePolicy, +p: P.SePolicy, +x: Bool, +h: {S.Selinux.validate.trans(x, q) == Done{p} : Result<&2, &2, P.SeError, P.SePolicy>}) -> {q == p : P.SePolicy}:
  match x:
    case True{}:
      Equal.cong(Result<&2, &2, P.SeError, P.SePolicy>, P.SePolicy, r => Result.default(&2, &2, P.SeError, P.SePolicy, r, q), Done{q}, Done{p}, h)
    case False{}:
      Empty.absurd({q == p : P.SePolicy}, SePf.tfail(T.SeTe.first_trans_conflict(q), p, h))

def SePf.tok(+q: P.SePolicy, +p: P.SePolicy, +x: Bool, +e: {T.SeTe.transitions_ok(q) == x : Bool}, +h: {S.Selinux.validate.trans(x, q) == Done{p} : Result<&2, &2, P.SeError, P.SePolicy>}) -> {T.SeTe.transitions_ok(p) == True{} : Bool}:
  match x:
    case True{}:
      +eq = SePf.tsame(q, p, True{}, h)
      %eq : {T.SeTe.transitions_ok(_) == True{} : Bool}
      e
    case False{}:
      Empty.absurd({T.SeTe.transitions_ok(p) == True{} : Bool}, SePf.tfail(T.SeTe.first_trans_conflict(q), p, h))

def SePf.vgo(+q: P.SePolicy, +p: P.SePolicy, +x: Bool, +e: {T.SeTe.neverallow_ok(q) == x : Bool}, +h: {S.Selinux.validate.go(x, q) == Done{p} : Result<&2, &2, P.SeError, P.SePolicy>}) -> {T.SeTe.neverallow_ok(p) == True{} : Bool}:
  match x:
    case True{}:
      +eq = SePf.tsame(q, p, T.SeTe.transitions_ok(q), h)
      %eq : {T.SeTe.neverallow_ok(_) == True{} : Bool}
      e
    case False{}:
      Empty.absurd({T.SeTe.neverallow_ok(p) == True{} : Bool}, SePf.vfail(T.SeTe.first_conflict(q), p, h))

def SePf.validated(+r: Result<&2, &2, P.SeError, P.SePolicy>, +p: P.SePolicy, +h: {S.Selinux.validated(r) == Done{p} : Result<&2, &2, P.SeError, P.SePolicy>}) -> {T.SeTe.neverallow_ok(p) == True{} : Bool}:
  match r:
    case Fail{e}:
      Empty.absurd({T.SeTe.neverallow_ok(p) == True{} : Bool}, SePf.fail_done(e, p, h))
    case Done{q}:
      SePf.vgo(q, p, T.SeTe.neverallow_ok(q), {==}, h)

def Laws.load_checks_neverallow(o, p, h):
  SePf.validated(L.SeCil.load(o), p, h)

def SePf.vgo_t(+q: P.SePolicy, +p: P.SePolicy, +x: Bool, +h: {S.Selinux.validate.go(x, q) == Done{p} : Result<&2, &2, P.SeError, P.SePolicy>}) -> {T.SeTe.transitions_ok(p) == True{} : Bool}:
  match x:
    case True{}:
      SePf.tok(q, p, T.SeTe.transitions_ok(q), {==}, h)
    case False{}:
      Empty.absurd({T.SeTe.transitions_ok(p) == True{} : Bool}, SePf.vfail(T.SeTe.first_conflict(q), p, h))

def SePf.validated_t(+r: Result<&2, &2, P.SeError, P.SePolicy>, +p: P.SePolicy, +h: {S.Selinux.validated(r) == Done{p} : Result<&2, &2, P.SeError, P.SePolicy>}) -> {T.SeTe.transitions_ok(p) == True{} : Bool}:
  match r:
    case Fail{e}:
      Empty.absurd({T.SeTe.transitions_ok(p) == True{} : Bool}, SePf.fail_done(e, p, h))
    case Done{q}:
      SePf.vgo_t(q, p, T.SeTe.neverallow_ok(q), h)

def Laws.load_checks_transitions(o, p, h):
  SePf.validated_t(L.SeCil.load(o), p, h)

def SePf.vfail_is(+m: Maybe<&2, P.SeConflict>) -> {Result.is_fail(&2, &2, P.SeError, P.SePolicy, S.Selinux.validate.fail(m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{c}:
      match c:
        case P.SeConflict{n, a}:
          {==}

def Laws.validate_refuses(p, h):
  %Equal.sym(Bool, T.SeTe.neverallow_ok(p), False{}, h) : {Result.is_fail(&2, &2, P.SeError, P.SePolicy, S.Selinux.validate.go(_, p)) == True{} : Bool}
  SePf.vfail_is(T.SeTe.first_conflict(p))

def SePf.tfail_is(+m: Maybe<&2, T.SeTransConflict>) -> {Result.is_fail(&2, &2, P.SeError, P.SePolicy, S.Selinux.validate.trans_fail(m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{c}:
      match c:
        case T.SeTyClash{a, b}:
          {==}
        case T.SeRoleClash{a, b}:
          {==}

def SePf.vgo_fails_t(+p: P.SePolicy, +x: Bool, +h: {T.SeTe.transitions_ok(p) == False{} : Bool}) -> {Result.is_fail(&2, &2, P.SeError, P.SePolicy, S.Selinux.validate.go(x, p)) == True{} : Bool}:
  match x:
    case True{}:
      %Equal.sym(Bool, T.SeTe.transitions_ok(p), False{}, h) : {Result.is_fail(&2, &2, P.SeError, P.SePolicy, S.Selinux.validate.trans(_, p)) == True{} : Bool}
      SePf.tfail_is(T.SeTe.first_trans_conflict(p))
    case False{}:
      SePf.vfail_is(T.SeTe.first_conflict(p))

def Laws.validate_refuses_transitions(p, h):
  SePf.vgo_fails_t(p, T.SeTe.neverallow_ok(p), h)

# Transitions

def SePf.mdisc(m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def SePf.none_some(-x: Nat, +h: {None{} == Some{x} : Maybe<&2, Nat>}) -> SePf.mdisc(Some{x}):
  %h : SePf.mdisc(_)
  Unit{}

def SePf.or_sound(-R: Type, +m1: Maybe<&2, Nat>, +m2: Maybe<&2, Nat>, +x: Nat, +h: {Maybe.or(&2, Nat, m1, m2) == Some{x} : Maybe<&2, Nat>}, f1: {m1 == Some{x} : Maybe<&2, Nat>} -> R, f2: {m2 == Some{x} : Maybe<&2, Nat>} -> R) -> R:
  match m1:
    case None{}:
      f2(h)
    case Some{y}:
      f1(h)

def SePf.find_hit(+b: Bool, +tm: Bool, +nm: Bool, +res: Nat, +f: Maybe<&2, Nat>, +x: Nat, +g: Bool, +e: {Bool.and(tm, nm) == b : Bool}, +h: {T.SeTe.find_ty.hit(b, res, f) == Some{x} : Maybe<&2, Nat>}, ih: {f == Some{x} : Maybe<&2, Nat>} -> {g == True{} : Bool}) -> {Bool.or(Bool.and(tm, Nat.is_eq(res, x)), g) == True{} : Bool}:
  match b:
    case True{}:
      +eq = Equal.cong(Maybe<&2, Nat>, Nat, mm => Maybe.default(&2, Nat, mm, res), Some{res}, Some{x}, h)
      +er = Equal.trans(Bool, Nat.is_eq(res, x), Nat.is_eq(x, x), True{}, Equal.cong(Nat, Bool, v => Nat.is_eq(v, x), res, x, eq), SePf.nat_eq_refl(x))
      SePf.or_l(Bool.and(tm, Nat.is_eq(res, x)), g, SePf.and_intro(tm, Nat.is_eq(res, x), SePf.and_l(tm, nm, e), er))
    case False{}:
      SePf.or_r(Bool.and(tm, Nat.is_eq(res, x)), g, ih(h))

def SePf.find_sound(+rs: List<&2, P.SeTyRule>, +kind: P.SeTyKind, +st: Nat, +tt: Nat, +c: Nat, +on: Maybe<&2, String>, +named: Bool, +x: Nat, +h: {T.SeTe.find_ty(rs, kind, st, tt, c, on, named) == Some{x} : Maybe<&2, Nat>}) -> {T.SeTe.ty_gives(rs, kind, st, tt, c, x) == True{} : Bool}:
  match rs:
    case Nil{}:
      Empty.absurd({False{} == True{} : Bool}, SePf.none_some(x, h))
    case Con{r, t}:
      +tm = T.SeTe.ty_matches(r, kind, st, tt, c)
      +nm = T.SeTe.name_ok(P.SeTyRule.name(r), on, named)
      SePf.find_hit(Bool.and(tm, nm), tm, nm, P.SeTyRule.result(r), T.SeTe.find_ty(t, kind, st, tt, c, on, named), x, T.SeTe.ty_gives(t, kind, st, tt, c, x), {==}, h, h2 => SePf.find_sound(t, kind, st, tt, c, on, named, x, h2))

def Laws.new_type_sound(p, kind, st, tt, c, on, x, h):
  +act = T.SeTe.active_ty(p)
  SePf.or_sound({T.SeTe.ty_gives(act, kind, st, tt, c, x) == True{} : Bool}, T.SeTe.find_ty(act, kind, st, tt, c, on, True{}), T.SeTe.find_ty(act, kind, st, tt, c, on, False{}), x, h, h1 => SePf.find_sound(act, kind, st, tt, c, on, True{}, x, h1), h2 => SePf.find_sound(act, kind, st, tt, c, on, False{}, x, h2))

def SePf.create_rule(+b: Bool, +p: P.SePolicy, +s: C.SeContext, +t: C.SeContext, +c: Nat, +on: Maybe<&2, String>, +x: Nat, +h: {T.SeTe.new_type(p, P.SeTyTransition{}, C.SeContext.typ(s), C.SeContext.typ(t), c, on) == Some{x} : Maybe<&2, Nat>}) -> {C.SeContext.typ(A.SeAvc.create.go(b, p, s, t, c, on)) == x : Nat}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, Nat>, T.SeTe.new_type(p, P.SeTyTransition{}, C.SeContext.typ(s), C.SeContext.typ(t), c, on), Some{x}, h) : {Maybe.default(&2, Nat, _, C.SeContext.typ(s)) == x : Nat}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, Nat>, T.SeTe.new_type(p, P.SeTyTransition{}, C.SeContext.typ(s), C.SeContext.typ(t), c, on), Some{x}, h) : {Maybe.default(&2, Nat, _, C.SeContext.typ(t)) == x : Nat}
      {==}

def Laws.create_by_rule(p, s, t, c, on, x, h):
  SePf.create_rule(A.SeAvc.is_process(p, c), p, s, t, c, on, x, h)

def Laws.create_object_default(p, s, t, c, on, hp, h):
  %Equal.sym(Bool, A.SeAvc.is_process(p, c), False{}, hp) : {C.SeContext.typ(A.SeAvc.create.go(_, p, s, t, c, on)) == C.SeContext.typ(t) : Nat}
  %Equal.sym(Maybe<&2, Nat>, T.SeTe.new_type(p, P.SeTyTransition{}, C.SeContext.typ(s), C.SeContext.typ(t), c, on), None{}, h) : {Maybe.default(&2, Nat, _, C.SeContext.typ(t)) == C.SeContext.typ(t) : Nat}
  {==}

def Laws.create_process_default(p, s, t, c, on, hp, h):
  %Equal.sym(Bool, A.SeAvc.is_process(p, c), True{}, hp) : {C.SeContext.typ(A.SeAvc.create.go(_, p, s, t, c, on)) == C.SeContext.typ(s) : Nat}
  %Equal.sym(Maybe<&2, Nat>, T.SeTe.new_type(p, P.SeTyTransition{}, C.SeContext.typ(s), C.SeContext.typ(t), c, on), None{}, h) : {Maybe.default(&2, Nat, _, C.SeContext.typ(s)) == C.SeContext.typ(s) : Nat}
  {==}
