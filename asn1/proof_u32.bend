# Proof helpers for bend-osdev-asn1: Base's U32 equality is reflexive and
# sound (equal comparison means the same word), by induction over the bits
# of Base's Word; and so is the byte-list equality a1.leq.
import Base
import ./number.bend as Nu
import ./proof_nat.bend as AN

def au.fin_refl(b: Bool) -> {Word.cmp.fin(b, b, EQ{}) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def au.cmp_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, au.cmp_refl(p, t)) : {Word.cmp.fin(b, b, _) == EQ{} : Cmp}
          au.fin_refl(b)

def au.is_eq_refl(x: U32) -> {U32.is_eq(x, x) == True{} : Bool}:
  match x:
    case U32{+w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, au.cmp_refl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

def au.cdisc(c: Cmp) -> Type:
  match c:
    case LT{}:
      Empty
    case EQ{}:
      Unit
    case GT{}:
      Empty

def au.bool_cmp(a: Bool, b: Bool, +e: {Cmp.is_eq(Bool.cmp(a, b)) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, AN.an.ft(e))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, AN.an.ft(e))

# a comparison that is EQ after fin: the rest compared EQ and the bits agree
def au.fin_eq(t: Cmp, a: Bool, b: Bool, +e: {Cmp.is_eq(Word.cmp.fin(a, b, t)) == True{} : Bool}) -> {t == EQ{} : Cmp}:
  match t:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, AN.an.ft(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, AN.an.ft(e))

def au.fin_bits(t: Cmp, a: Bool, b: Bool, +e: {Cmp.is_eq(Word.cmp.fin(a, b, t)) == True{} : Bool}) -> {a == b : Bool}:
  match t:
    case LT{}:
      Empty.absurd({a == b : Bool}, AN.an.ft(e))
    case EQ{}:
      au.bool_cmp(a, b, e)
    case GT{}:
      Empty.absurd({a == b : Bool}, AN.an.ft(e))

def au.cmp_sound(n: Nat, x: Word(n), y: Word(n), +e: {Cmp.is_eq(Word.cmp(n, x, y)) == True{} : Bool}) -> {x == y : Word(n)}:
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match x y:
        case WCon{+a, +s} WCon{+b, +t}:
          +ht = au.fin_eq(Word.cmp(p, s, t), a, b, e)
          +hb = au.fin_bits(Word.cmp(p, s, t), a, b, e)
          +hst = au.cmp_sound(p, s, t, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), Word.cmp(p, s, t), EQ{}, ht))
          %hb : {WCon{a, s} == WCon{_, t} : Word(1n+p)}
          %hst : {WCon{a, s} == WCon{a, _} : Word(1n+p)}
          {==}

def au.is_eq_sound(x: U32, y: U32, +e: {U32.is_eq(x, y) == True{} : Bool}) -> {x == y : U32}:
  match x y:
    case U32{+v} U32{+w}:
      %au.cmp_sound(32n, v, w, e) : {U32{v} == U32{_} : U32}
      {==}

# a1.leq is reflexive and sound

def au.leq_refl(xs: List<&2, U32>) -> {Nu.a1.leq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +s}:
      %Equal.sym(Bool, U32.is_eq(a, a), True{}, au.is_eq_refl(a)) : {Bool.and(_, Nu.a1.leq(s, s)) == True{} : Bool}
      au.leq_refl(s)

def au.leq_sound(xs: List<&2, U32>, ys: List<&2, U32>, +e: {Nu.a1.leq(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, U32>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, t}:
      Empty.absurd({Nil{} == Con{b, t} : List<&2, U32>}, AN.an.ft(e))
    case Con{a, s} Nil{}:
      Empty.absurd({Con{a, s} == Nil{} : List<&2, U32>}, AN.an.ft(e))
    case Con{+a, +s} Con{+b, +t}:
      +ha = au.is_eq_sound(a, b, AN.an.and_l(U32.is_eq(a, b), Nu.a1.leq(s, t), e))
      +hs = au.leq_sound(s, t, AN.an.and_r(U32.is_eq(a, b), Nu.a1.leq(s, t), e))
      %ha : {Con{a, s} == Con{_, t} : List<&2, U32>}
      %hs : {Con{a, s} == Con{a, _} : List<&2, U32>}
      {==}
