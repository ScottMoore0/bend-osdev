# Proofs of LAWS_map.bend.
#
# The plan:
# * The key order: ck(c1, c2, c3) says that comparisons c1 (a to b) and
#   c2 (b to c) at or below give c3 (a to c) below when either is below,
#   and equal when both are. It holds for Nat.cmp by induction, so for
#   U32.cmp by bend-osdev-u32's u32_cmp_value, and it passes through the
#   lexicographic step (NftKey.cmp.pick), so it holds for keys by induction
#   on the byte lists. Comparing the other way round flips the comparison,
#   the same way.
# * Lookup: on a list with the invariant, every element before one lies
#   below its low end (mp.before) and every element after it above its high
#   end (mp.below), so it is the only one holding a key it holds.
# * Insertion puts the new element before the first it lies below (lookup
#   reads it first), or after one it lies above, which holds none of its
#   keys, so the two lookups commute (mp.pick_swap). Insertion succeeds
#   only when no element holds a key of the new one (mp.ins_none).
# * A map built from a list: by induction over the insertions, the set's
#   lookup is the first answer of the elements inserted so far (mp.orm).
import Base
import ../bytes/bytes.bend as B
import ../u32/u32.bend as UN
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ./family.bend as F
import ./sets.bend as S
import ./LAWS.bend as NL
import ./PROOF.bend as P
import ./LAWS_map.bend as Laws

# Comparisons

def cm.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

# c1 = cmp(a, b), c2 = cmp(b, c) at or below: c3 = cmp(a, c) as they say
def cm.ck(c1: Cmp, c2: Cmp, c3: Cmp) -> Bool:
  match c1:
    case LT{}:
      match c2:
        case LT{}:
          Cmp.is_lt(c3)
        case EQ{}:
          Cmp.is_lt(c3)
        case GT{}:
          True{}
    case EQ{}:
      match c2:
        case LT{}:
          Cmp.is_lt(c3)
        case EQ{}:
          Cmp.is_eq(c3)
        case GT{}:
          True{}
    case GT{}:
      True{}

def cm.any_lt(c: Cmp) -> {cm.ck(LT{}, c, LT{}) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def cm.any_gt(c: Cmp, -c3: Cmp) -> {cm.ck(c, GT{}, c3) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def cm.lt_lt(c: Cmp) -> {cm.ck(c, LT{}, LT{}) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# the lexicographic step keeps ck
def cm.pick(p1: Cmp, p2: Cmp, p3: Cmp, r1: Cmp, r2: Cmp, r3: Cmp, hp: {cm.ck(p1, p2, p3) == True{} : Bool}, hr: {cm.ck(r1, r2, r3) == True{} : Bool}) -> {cm.ck(S.NftKey.cmp.pick(p1, r1), S.NftKey.cmp.pick(p2, r2), S.NftKey.cmp.pick(p3, r3)) == True{} : Bool}:
  match p1:
    case GT{}:
      {==}
    case LT{}:
      match p2:
        case GT{}:
          {==}
        case LT{}:
          match p3:
            case LT{}:
              {==}
            case EQ{}:
              Empty.absurd({cm.ck(LT{}, LT{}, S.NftKey.cmp.pick(EQ{}, r3)) == True{} : Bool}, P.absurd.ft(hp))
            case GT{}:
              Empty.absurd({cm.ck(LT{}, LT{}, GT{}) == True{} : Bool}, P.absurd.ft(hp))
        case EQ{}:
          match p3:
            case LT{}:
              cm.any_lt(r2)
            case EQ{}:
              Empty.absurd({cm.ck(LT{}, r2, S.NftKey.cmp.pick(EQ{}, r3)) == True{} : Bool}, P.absurd.ft(hp))
            case GT{}:
              Empty.absurd({cm.ck(LT{}, r2, GT{}) == True{} : Bool}, P.absurd.ft(hp))
    case EQ{}:
      match p2:
        case GT{}:
          cm.any_gt(r1, S.NftKey.cmp.pick(p3, r3))
        case LT{}:
          match p3:
            case LT{}:
              cm.lt_lt(r1)
            case EQ{}:
              Empty.absurd({cm.ck(r1, LT{}, S.NftKey.cmp.pick(EQ{}, r3)) == True{} : Bool}, P.absurd.ft(hp))
            case GT{}:
              Empty.absurd({cm.ck(r1, LT{}, GT{}) == True{} : Bool}, P.absurd.ft(hp))
        case EQ{}:
          match p3:
            case EQ{}:
              hr
            case LT{}:
              Empty.absurd({cm.ck(r1, r2, LT{}) == True{} : Bool}, P.absurd.ft(hp))
            case GT{}:
              Empty.absurd({cm.ck(r1, r2, GT{}) == True{} : Bool}, P.absurd.ft(hp))

def cm.pick_flip(c: Cmp, -r: Cmp) -> {S.NftKey.cmp.pick(cm.flip(c), cm.flip(r)) == cm.flip(S.NftKey.cmp.pick(c, r)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def cm.lt_le(c: Cmp, h: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_le(EQ{}) == True{} : Bool}, P.absurd.ft(h))
    case GT{}:
      Empty.absurd({Cmp.is_le(GT{}) == True{} : Bool}, P.absurd.ft(h))

def cm.eq_le(c: Cmp, h: {Cmp.is_eq(c) == True{} : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_le(GT{}) == True{} : Bool}, P.absurd.ft(h))

def cm.le_le(c1: Cmp, c2: Cmp, c3: Cmp, hk: {cm.ck(c1, c2, c3) == True{} : Bool}, h1: {Cmp.is_le(c1) == True{} : Bool}, h2: {Cmp.is_le(c2) == True{} : Bool}) -> {Cmp.is_le(c3) == True{} : Bool}:
  match c1:
    case GT{}:
      Empty.absurd({Cmp.is_le(c3) == True{} : Bool}, P.absurd.ft(h1))
    case LT{}:
      match c2:
        case GT{}:
          Empty.absurd({Cmp.is_le(c3) == True{} : Bool}, P.absurd.ft(h2))
        case LT{}:
          cm.lt_le(c3, hk)
        case EQ{}:
          cm.lt_le(c3, hk)
    case EQ{}:
      match c2:
        case GT{}:
          Empty.absurd({Cmp.is_le(c3) == True{} : Bool}, P.absurd.ft(h2))
        case LT{}:
          cm.lt_le(c3, hk)
        case EQ{}:
          cm.eq_le(c3, hk)

def cm.lt_le3(c1: Cmp, c2: Cmp, -c3: Cmp, hk: {cm.ck(c1, c2, c3) == True{} : Bool}, h1: {Cmp.is_lt(c1) == True{} : Bool}, h2: {Cmp.is_le(c2) == True{} : Bool}) -> {Cmp.is_lt(c3) == True{} : Bool}:
  match c1:
    case LT{}:
      match c2:
        case GT{}:
          Empty.absurd({Cmp.is_lt(c3) == True{} : Bool}, P.absurd.ft(h2))
        case LT{}:
          hk
        case EQ{}:
          hk
    case EQ{}:
      Empty.absurd({Cmp.is_lt(c3) == True{} : Bool}, P.absurd.ft(h1))
    case GT{}:
      Empty.absurd({Cmp.is_lt(c3) == True{} : Bool}, P.absurd.ft(h1))

def cm.le_lt3(c1: Cmp, c2: Cmp, -c3: Cmp, hk: {cm.ck(c1, c2, c3) == True{} : Bool}, h1: {Cmp.is_le(c1) == True{} : Bool}, h2: {Cmp.is_lt(c2) == True{} : Bool}) -> {Cmp.is_lt(c3) == True{} : Bool}:
  match c1:
    case GT{}:
      Empty.absurd({Cmp.is_lt(c3) == True{} : Bool}, P.absurd.ft(h1))
    case LT{}:
      match c2:
        case LT{}:
          hk
        case EQ{}:
          Empty.absurd({Cmp.is_lt(c3) == True{} : Bool}, P.absurd.ft(h2))
        case GT{}:
          Empty.absurd({Cmp.is_lt(c3) == True{} : Bool}, P.absurd.ft(h2))
    case EQ{}:
      match c2:
        case LT{}:
          hk
        case EQ{}:
          Empty.absurd({Cmp.is_lt(c3) == True{} : Bool}, P.absurd.ft(h2))
        case GT{}:
          Empty.absurd({Cmp.is_lt(c3) == True{} : Bool}, P.absurd.ft(h2))

def cm.lt_not_le(c: Cmp, h: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_le(cm.flip(c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({Cmp.is_le(cm.flip(EQ{})) == False{} : Bool}, P.absurd.ft(h))
    case GT{}:
      Empty.absurd({Cmp.is_le(cm.flip(GT{})) == False{} : Bool}, P.absurd.ft(h))

# Nat.cmp, then U32.cmp

def cm.nat_ck(a: Nat, b: Nat, c: Nat) -> {cm.ck(Nat.cmp(a, b), Nat.cmp(b, c), Nat.cmp(a, c)) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+cp:
      {==}
    case 0n 1n+bp 0n:
      {==}
    case 0n 1n+bp 1n+cp:
      cm.any_lt(Nat.cmp(bp, cp))
    case 1n+ap 0n 0n:
      {==}
    case 1n+ap 0n 1n+cp:
      {==}
    case 1n+ap 1n+bp 0n:
      cm.any_gt(Nat.cmp(ap, bp), GT{})
    case 1n+ap 1n+bp 1n+cp:
      cm.nat_ck(ap, bp, cp)

def cm.nat_flip(a: Nat, b: Nat) -> {Nat.cmp(b, a) == cm.flip(Nat.cmp(a, b)) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      cm.nat_flip(ap, bp)

def cm.nat_refl(a: Nat) -> {Nat.cmp(a, a) == EQ{} : Cmp}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      cm.nat_refl(ap)

def cm.u32_ck(+x: U32, +y: U32, +z: U32) -> {cm.ck(U32.cmp(x, y), U32.cmp(y, z), U32.cmp(x, z)) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(x, y), Nat.cmp(U32.to_nat(x), U32.to_nat(y)), UL.u32_cmp_value(x, y)) : {cm.ck(_, U32.cmp(y, z), U32.cmp(x, z)) == True{} : Bool}
  %Equal.sym(Cmp, U32.cmp(y, z), Nat.cmp(U32.to_nat(y), U32.to_nat(z)), UL.u32_cmp_value(y, z)) : {cm.ck(Nat.cmp(U32.to_nat(x), U32.to_nat(y)), _, U32.cmp(x, z)) == True{} : Bool}
  %Equal.sym(Cmp, U32.cmp(x, z), Nat.cmp(U32.to_nat(x), U32.to_nat(z)), UL.u32_cmp_value(x, z)) : {cm.ck(Nat.cmp(U32.to_nat(x), U32.to_nat(y)), Nat.cmp(U32.to_nat(y), U32.to_nat(z)), _) == True{} : Bool}
  cm.nat_ck(U32.to_nat(x), U32.to_nat(y), U32.to_nat(z))

def cm.u32_flip(+x: U32, +y: U32) -> {U32.cmp(y, x) == cm.flip(U32.cmp(x, y)) : Cmp}:
  %Equal.sym(Cmp, U32.cmp(y, x), Nat.cmp(U32.to_nat(y), U32.to_nat(x)), UL.u32_cmp_value(y, x)) : {_ == cm.flip(U32.cmp(x, y)) : Cmp}
  %Equal.sym(Cmp, U32.cmp(x, y), Nat.cmp(U32.to_nat(x), U32.to_nat(y)), UL.u32_cmp_value(x, y)) : {Nat.cmp(U32.to_nat(y), U32.to_nat(x)) == cm.flip(_) : Cmp}
  cm.nat_flip(U32.to_nat(x), U32.to_nat(y))

def cm.u32_refl(+x: U32) -> {U32.cmp(x, x) == EQ{} : Cmp}:
  %Equal.sym(Cmp, U32.cmp(x, x), Nat.cmp(U32.to_nat(x), U32.to_nat(x)), UL.u32_cmp_value(x, x)) : {_ == EQ{} : Cmp}
  cm.nat_refl(U32.to_nat(x))

# Byte lists

def cm.list_ck(a: List<&2, U32>, b: List<&2, U32>, c: List<&2, U32>) -> {cm.ck(S.NftKey.cmp.list(a, b), S.NftKey.cmp.list(b, c), S.NftKey.cmp.list(a, c)) == True{} : Bool}:
  match a b c:
    case Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} Con{z, zs}:
      {==}
    case Nil{} Con{y, ys} Nil{}:
      {==}
    case Nil{} Con{y, ys} Con{z, zs}:
      cm.any_lt(S.NftKey.cmp.pick(U32.cmp(y, z), S.NftKey.cmp.list(ys, zs)))
    case Con{x, xs} Nil{} Nil{}:
      {==}
    case Con{x, xs} Nil{} Con{z, zs}:
      {==}
    case Con{x, xs} Con{y, ys} Nil{}:
      cm.any_gt(S.NftKey.cmp.pick(U32.cmp(x, y), S.NftKey.cmp.list(xs, ys)), GT{})
    case Con{+x, +xs} Con{+y, +ys} Con{+z, +zs}:
      cm.pick(U32.cmp(x, y), U32.cmp(y, z), U32.cmp(x, z), S.NftKey.cmp.list(xs, ys), S.NftKey.cmp.list(ys, zs), S.NftKey.cmp.list(xs, zs), cm.u32_ck(x, y, z), cm.list_ck(xs, ys, zs))

def cm.list_flip(a: List<&2, U32>, b: List<&2, U32>) -> {S.NftKey.cmp.list(b, a) == cm.flip(S.NftKey.cmp.list(a, b)) : Cmp}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      {==}
    case Con{x, xs} Nil{}:
      {==}
    case Con{+x, +xs} Con{+y, +ys}:
      %Equal.sym(Cmp, U32.cmp(y, x), cm.flip(U32.cmp(x, y)), cm.u32_flip(x, y)) : {S.NftKey.cmp.pick(_, S.NftKey.cmp.list(ys, xs)) == cm.flip(S.NftKey.cmp.pick(U32.cmp(x, y), S.NftKey.cmp.list(xs, ys))) : Cmp}
      %Equal.sym(Cmp, S.NftKey.cmp.list(ys, xs), cm.flip(S.NftKey.cmp.list(xs, ys)), cm.list_flip(xs, ys)) : {S.NftKey.cmp.pick(cm.flip(U32.cmp(x, y)), _) == cm.flip(S.NftKey.cmp.pick(U32.cmp(x, y), S.NftKey.cmp.list(xs, ys))) : Cmp}
      cm.pick_flip(U32.cmp(x, y), S.NftKey.cmp.list(xs, ys))

def cm.list_refl(a: List<&2, U32>) -> {S.NftKey.cmp.list(a, a) == EQ{} : Cmp}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +xs}:
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, cm.u32_refl(x)) : {S.NftKey.cmp.pick(_, S.NftKey.cmp.list(xs, xs)) == EQ{} : Cmp}
      cm.list_refl(xs)

# Keys

def ky.ck(+a: B.Octets, +b: B.Octets, +c: B.Octets) -> {cm.ck(S.NftKey.cmp(a, b), S.NftKey.cmp(b, c), S.NftKey.cmp(a, c)) == True{} : Bool}:
  cm.list_ck(B.Octets.to_list(a), B.Octets.to_list(b), B.Octets.to_list(c))

def ky.refl(+a: B.Octets) -> {S.NftKey.le(a, a) == True{} : Bool}:
  %Equal.sym(Cmp, S.NftKey.cmp.list(B.Octets.to_list(a), B.Octets.to_list(a)), EQ{}, cm.list_refl(B.Octets.to_list(a))) : {Cmp.is_le(_) == True{} : Bool}
  {==}

def ky.le_trans(+a: B.Octets, +b: B.Octets, +c: B.Octets, h1: {S.NftKey.le(a, b) == True{} : Bool}, h2: {S.NftKey.le(b, c) == True{} : Bool}) -> {S.NftKey.le(a, c) == True{} : Bool}:
  cm.le_le(S.NftKey.cmp(a, b), S.NftKey.cmp(b, c), S.NftKey.cmp(a, c), ky.ck(a, b, c), h1, h2)

def ky.lt_le(+a: B.Octets, +b: B.Octets, +c: B.Octets, h1: {S.NftKey.lt(a, b) == True{} : Bool}, h2: {S.NftKey.le(b, c) == True{} : Bool}) -> {S.NftKey.lt(a, c) == True{} : Bool}:
  cm.lt_le3(S.NftKey.cmp(a, b), S.NftKey.cmp(b, c), S.NftKey.cmp(a, c), ky.ck(a, b, c), h1, h2)

def ky.le_lt(+a: B.Octets, +b: B.Octets, +c: B.Octets, h1: {S.NftKey.le(a, b) == True{} : Bool}, h2: {S.NftKey.lt(b, c) == True{} : Bool}) -> {S.NftKey.lt(a, c) == True{} : Bool}:
  cm.le_lt3(S.NftKey.cmp(a, b), S.NftKey.cmp(b, c), S.NftKey.cmp(a, c), ky.ck(a, b, c), h1, h2)

def ky.lt_trans(+a: B.Octets, +b: B.Octets, +c: B.Octets, h1: {S.NftKey.lt(a, b) == True{} : Bool}, h2: {S.NftKey.lt(b, c) == True{} : Bool}) -> {S.NftKey.lt(a, c) == True{} : Bool}:
  cm.lt_le3(S.NftKey.cmp(a, b), S.NftKey.cmp(b, c), S.NftKey.cmp(a, c), ky.ck(a, b, c), h1, cm.lt_le(S.NftKey.cmp(b, c), h2))

def ky.lt_not_le(+a: B.Octets, +b: B.Octets, h: {S.NftKey.lt(a, b) == True{} : Bool}) -> {S.NftKey.le(b, a) == False{} : Bool}:
  %Equal.sym(Cmp, S.NftKey.cmp.list(B.Octets.to_list(b), B.Octets.to_list(a)), cm.flip(S.NftKey.cmp.list(B.Octets.to_list(a), B.Octets.to_list(b))), cm.list_flip(B.Octets.to_list(a), B.Octets.to_list(b))) : {Cmp.is_le(_) == False{} : Bool}
  cm.lt_not_le(S.NftKey.cmp.list(B.Octets.to_list(a), B.Octets.to_list(b)), h)

def Laws.key_le_refl(a):
  ky.refl(a)

def Laws.key_le_trans(a, b, c, h1, h2):
  ky.le_trans(a, b, c, h1, h2)

def Laws.key_lt_trans(a, b, c, h1, h2):
  ky.lt_trans(a, b, c, h1, h2)

def Laws.key_lt_le_trans(a, b, c, h1, h2):
  ky.lt_le(a, b, c, h1, h2)

def Laws.key_le_lt_trans(a, b, c, h1, h2):
  ky.le_lt(a, b, c, h1, h2)

def Laws.key_lt_not_le(a, b, h):
  ky.lt_not_le(a, b, h)

# Elements

def el.valid_le(h: S.NftElem, v: {S.NftElem.valid(h) == True{} : Bool}) -> {S.NftKey.le(S.NftElem.lo(h), S.NftElem.hi(h)) == True{} : Bool}:
  match h:
    case S.NftElem{lo, hi, d}:
      v

def el.lo(e: S.NftElem, +x: B.Octets, c: {S.NftElem.contains(e, x) == True{} : Bool}) -> {S.NftKey.le(S.NftElem.lo(e), x) == True{} : Bool}:
  match e:
    case S.NftElem{lo, hi, d}:
      P.bool.and_l(S.NftKey.le(lo, x), S.NftKey.le(x, hi), c)

def el.hi(e: S.NftElem, +x: B.Octets, c: {S.NftElem.contains(e, x) == True{} : Bool}) -> {S.NftKey.le(x, S.NftElem.hi(e)) == True{} : Bool}:
  match e:
    case S.NftElem{lo, hi, d}:
      P.bool.and_r(S.NftKey.le(lo, x), S.NftKey.le(x, hi), c)

def el.and_f(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# x at or below k, k below h's low end: h does not hold x
def el.out_lo(h: S.NftElem, +k: B.Octets, +x: B.Octets, hl: {S.NftKey.lt(k, S.NftElem.lo(h)) == True{} : Bool}, hx: {S.NftKey.le(x, k) == True{} : Bool}) -> {S.NftElem.contains(h, x) == False{} : Bool}:
  match h:
    case S.NftElem{+lo, hi, d}:
      +n = ky.lt_not_le(x, lo, ky.le_lt(x, k, lo, hx, hl))
      %Equal.sym(Bool, S.NftKey.le(lo, x), False{}, n) : {Bool.and(_, S.NftKey.le(x, hi)) == False{} : Bool}
      {==}

# h's high end below k, k at or below x: h does not hold x
def el.out_hi(h: S.NftElem, +k: B.Octets, +x: B.Octets, hl: {S.NftKey.lt(S.NftElem.hi(h), k) == True{} : Bool}, hx: {S.NftKey.le(k, x) == True{} : Bool}) -> {S.NftElem.contains(h, x) == False{} : Bool}:
  match h:
    case S.NftElem{lo, +hi, d}:
      +n = ky.lt_not_le(hi, x, ky.lt_le(hi, k, x, hl, hx))
      %Equal.sym(Bool, S.NftKey.le(x, hi), False{}, n) : {Bool.and(S.NftKey.le(lo, x), _) == False{} : Bool}
      el.and_f(S.NftKey.le(lo, x))

# Lists with the invariant

# a key below the next element's low end is below every later one's
def mp.sep_step(+e: S.NftElem, +h: S.NftElem, t: List<&2, S.NftElem>, hs: {S.NftKey.lt(S.NftElem.hi(e), S.NftElem.lo(h)) == True{} : Bool}, hw: {S.NftSet.wf.go(Con{h, t}) == True{} : Bool}) -> {S.NftSet.sep(e, t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+g, +r}:
      +hw = hw
      +vh = P.bool.and_l(S.NftElem.valid(h), Bool.and(S.NftSet.sep(h, Con{g, r}), S.NftSet.wf.go(Con{g, r})), hw)
      +rest = P.bool.and_r(S.NftElem.valid(h), Bool.and(S.NftSet.sep(h, Con{g, r}), S.NftSet.wf.go(Con{g, r})), hw)
      +sg = P.bool.and_l(S.NftSet.sep(h, Con{g, r}), S.NftSet.wf.go(Con{g, r}), rest)
      ky.lt_trans(S.NftElem.hi(e), S.NftElem.hi(h), S.NftElem.lo(g), ky.lt_le(S.NftElem.hi(e), S.NftElem.lo(h), S.NftElem.hi(h), hs, el.valid_le(h, vh)), sg)

# x at or below e's high end, e below the list: no element holds x
def mp.below(l: List<&2, S.NftElem>, +e: S.NftElem, +x: B.Octets, hs: {S.NftSet.sep(e, l) == True{} : Bool}, hw: {S.NftSet.wf.go(l) == True{} : Bool}, +hx: {S.NftKey.le(x, S.NftElem.hi(e)) == True{} : Bool}) -> {S.NftSet.lookup.go(l, x) == None{} : Maybe<&2, S.NftData>}:
  match l:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +hw = hw
      +hs = hs
      +rest = P.bool.and_r(S.NftElem.valid(h), Bool.and(S.NftSet.sep(h, t), S.NftSet.wf.go(t)), hw)
      +ht = P.bool.and_r(S.NftSet.sep(h, t), S.NftSet.wf.go(t), rest)
      +nh = el.out_lo(h, S.NftElem.hi(e), x, hs, hx)
      +st = mp.sep_step(e, h, t, hs, hw)
      %Equal.sym(Bool, S.NftElem.contains(h, x), False{}, nh) : {S.NftSet.lookup.pick(_, S.NftElem.data(h), S.NftSet.lookup.go(t, x)) == None{} : Maybe<&2, S.NftData>}
      mp.below(t, e, x, st, ht, hx)

# an element before e lies below e's low end
def mp.before(p: List<&2, S.NftElem>, +f: S.NftElem, +e: S.NftElem, +post: List<&2, S.NftElem>, hw: {S.NftSet.wf.go(Con{f, List.append(&2, S.NftElem, p, Con{e, post})}) == True{} : Bool}) -> {S.NftKey.lt(S.NftElem.hi(f), S.NftElem.lo(e)) == True{} : Bool}:
  match p:
    case Nil{}:
      +rest = P.bool.and_r(S.NftElem.valid(f), Bool.and(S.NftSet.sep(f, Con{e, post}), S.NftSet.wf.go(Con{e, post})), hw)
      P.bool.and_l(S.NftSet.sep(f, Con{e, post}), S.NftSet.wf.go(Con{e, post}), rest)
    case Con{+g, +q}:
      +hw = hw
      +rest = P.bool.and_r(S.NftElem.valid(f), Bool.and(S.NftSet.sep(f, Con{g, List.append(&2, S.NftElem, q, Con{e, post})}), S.NftSet.wf.go(Con{g, List.append(&2, S.NftElem, q, Con{e, post})})), hw)
      +sfg = P.bool.and_l(S.NftSet.sep(f, Con{g, List.append(&2, S.NftElem, q, Con{e, post})}), S.NftSet.wf.go(Con{g, List.append(&2, S.NftElem, q, Con{e, post})}), rest)
      +tg = P.bool.and_r(S.NftSet.sep(f, Con{g, List.append(&2, S.NftElem, q, Con{e, post})}), S.NftSet.wf.go(Con{g, List.append(&2, S.NftElem, q, Con{e, post})}), rest)
      +vg = P.bool.and_l(S.NftElem.valid(g), Bool.and(S.NftSet.sep(g, List.append(&2, S.NftElem, q, Con{e, post})), S.NftSet.wf.go(List.append(&2, S.NftElem, q, Con{e, post}))), tg)
      +ih = mp.before(q, g, e, post, tg)
      ky.lt_trans(S.NftElem.hi(f), S.NftElem.hi(g), S.NftElem.lo(e), ky.lt_le(S.NftElem.hi(f), S.NftElem.lo(g), S.NftElem.hi(g), sfg, el.valid_le(g, vg)), ih)

def mp.uniq(pre: List<&2, S.NftElem>, +e: S.NftElem, +post: List<&2, S.NftElem>, +x: B.Octets, hw: {S.NftSet.wf.go(List.append(&2, S.NftElem, pre, Con{e, post})) == True{} : Bool}, +he: {S.NftElem.contains(e, x) == True{} : Bool}) -> {S.NftSet.lookup.go(List.append(&2, S.NftElem, pre, Con{e, post}), x) == Some{S.NftElem.data(e)} : Maybe<&2, S.NftData>}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, S.NftElem.contains(e, x), True{}, he) : {S.NftSet.lookup.pick(_, S.NftElem.data(e), S.NftSet.lookup.go(post, x)) == Some{S.NftElem.data(e)} : Maybe<&2, S.NftData>}
      {==}
    case Con{+f, +p}:
      +hw = hw
      +lt = mp.before(p, f, e, post, hw)
      +nf = el.out_hi(f, S.NftElem.lo(e), x, lt, el.lo(e, x, he))
      +rest = P.bool.and_r(S.NftElem.valid(f), Bool.and(S.NftSet.sep(f, List.append(&2, S.NftElem, p, Con{e, post})), S.NftSet.wf.go(List.append(&2, S.NftElem, p, Con{e, post}))), hw)
      +ht = P.bool.and_r(S.NftSet.sep(f, List.append(&2, S.NftElem, p, Con{e, post})), S.NftSet.wf.go(List.append(&2, S.NftElem, p, Con{e, post})), rest)
      %Equal.sym(Bool, S.NftElem.contains(f, x), False{}, nf) : {S.NftSet.lookup.pick(_, S.NftElem.data(f), S.NftSet.lookup.go(List.append(&2, S.NftElem, p, Con{e, post}), x)) == Some{S.NftElem.data(e)} : Maybe<&2, S.NftData>}
      mp.uniq(p, e, post, x, ht, he)

def mp.wf_tr(-l1: List<&2, S.NftElem>, -l2: List<&2, S.NftElem>, e: {l1 == l2 : List<&2, S.NftElem>}, h: {S.NftSet.wf.go(l1) == True{} : Bool}) -> {S.NftSet.wf.go(l2) == True{} : Bool}:
  %e : {S.NftSet.wf.go(_) == True{} : Bool}
  h

def Laws.map_lookup_unique(s, pre, e, post, x, wf, es, he):
  match s:
    case S.NftSet{l}:
      +es = es
      %Equal.sym(List<&2, S.NftElem>, l, List.append(&2, S.NftElem, pre, Con{e, post}), es) : {S.NftSet.lookup.go(_, x) == Some{S.NftElem.data(e)} : Maybe<&2, S.NftData>}
      mp.uniq(pre, e, post, x, mp.wf_tr(l, List.append(&2, S.NftElem, pre, Con{e, post}), es, wf), he)

# Insertion succeeds only when no element holds a key of the new one

def mp.noov(r: Result<&2, &2, F.NftError, List<&2, S.NftElem>>, es: List<&2, S.NftElem>, +x: B.Octets) -> Type:
  match r:
    case Done{l}:
      {S.NftSet.lookup.go(es, x) == None{} : Maybe<&2, S.NftData>}
    case Fail{err}:
      Unit

def mp.ins_none.pick(b1: Bool, b2: Bool, +e: S.NftElem, +h: S.NftElem, +t: List<&2, S.NftElem>, eq1: {S.NftKey.lt(S.NftElem.hi(e), S.NftElem.lo(h)) == b1 : Bool}, eq2: {S.NftKey.lt(S.NftElem.hi(h), S.NftElem.lo(e)) == b2 : Bool}, r: Result<&2, &2, F.NftError, List<&2, S.NftElem>>, +x: B.Octets, +hw: {S.NftSet.wf.go(Con{h, t}) == True{} : Bool}, +hc: {S.NftElem.contains(e, x) == True{} : Bool}, ih: mp.noov(r, t, x)) -> mp.noov(S.NftSet.ins.pick(b1, b2, e, h, t, r), Con{h, t}, x):
  match b1:
    case True{}:
      mp.below(Con{h, t}, e, x, eq1, hw, el.hi(e, x, hc))
    case False{}:
      match b2:
        case True{}:
          match r:
            case Done{l}:
              +nh = el.out_hi(h, S.NftElem.lo(e), x, eq2, el.lo(e, x, hc))
              %Equal.sym(Bool, S.NftElem.contains(h, x), False{}, nh) : {S.NftSet.lookup.pick(_, S.NftElem.data(h), S.NftSet.lookup.go(t, x)) == None{} : Maybe<&2, S.NftData>}
              ih
            case Fail{err}:
              Unit{}
        case False{}:
          Unit{}

def mp.ins_none(es: List<&2, S.NftElem>, +e: S.NftElem, +x: B.Octets, hw: {S.NftSet.wf.go(es) == True{} : Bool}, +hc: {S.NftElem.contains(e, x) == True{} : Bool}) -> mp.noov(S.NftSet.ins(es, e), es, x):
  match es:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +hw = hw
      +rest = P.bool.and_r(S.NftElem.valid(h), Bool.and(S.NftSet.sep(h, t), S.NftSet.wf.go(t)), hw)
      +ht = P.bool.and_r(S.NftSet.sep(h, t), S.NftSet.wf.go(t), rest)
      mp.ins_none.pick(S.NftKey.lt(S.NftElem.hi(e), S.NftElem.lo(h)), S.NftKey.lt(S.NftElem.hi(h), S.NftElem.lo(e)), e, h, t, {==}, {==}, S.NftSet.ins(t, e), x, hw, hc, mp.ins_none(t, e, x, ht, hc))

def mp.noov_done(r: Result<&2, &2, F.NftError, List<&2, S.NftElem>>, +es: List<&2, S.NftElem>, +x: B.Octets, s1: S.NftSet, ok: {S.NftSet.wrap(r) == Done{s1} : Result<&2, &2, F.NftError, S.NftSet>}, h: mp.noov(r, es, x)) -> {S.NftSet.lookup.go(es, x) == None{} : Maybe<&2, S.NftData>}:
  match r:
    case Done{l}:
      h
    case Fail{err}:
      Empty.absurd({S.NftSet.lookup.go(es, x) == None{} : Maybe<&2, S.NftData>}, P.absurd.fail_done(err, s1, ok))

def mp.noov_go(v: Bool, +es: List<&2, S.NftElem>, +e: S.NftElem, +x: B.Octets, s1: S.NftSet, hw: {S.NftSet.wf.go(es) == True{} : Bool}, +hc: {S.NftElem.contains(e, x) == True{} : Bool}, ok: {S.NftSet.insert.go(v, es, e) == Done{s1} : Result<&2, &2, F.NftError, S.NftSet>}) -> {S.NftSet.lookup.go(es, x) == None{} : Maybe<&2, S.NftData>}:
  match v:
    case False{}:
      Empty.absurd({S.NftSet.lookup.go(es, x) == None{} : Maybe<&2, S.NftData>}, P.absurd.fail_done(F.NftErrBadInterval{}, s1, ok))
    case True{}:
      mp.noov_done(S.NftSet.ins(es, e), es, x, s1, ok, mp.ins_none(es, e, x, hw, hc))

def mp.noov_ins(s0: S.NftSet, +e: S.NftElem, +x: B.Octets, s1: S.NftSet, hw: {S.NftSet.wf(s0) == True{} : Bool}, ok: {S.NftSet.insert(s0, e) == Done{s1} : Result<&2, &2, F.NftError, S.NftSet>}, +hc: {S.NftElem.contains(e, x) == True{} : Bool}) -> {S.NftSet.lookup(s0, x) == None{} : Maybe<&2, S.NftData>}:
  match s0:
    case S.NftSet{es}:
      mp.noov_go(S.NftElem.valid(e), es, e, x, s1, hw, hc, ok)

# Lookup after insertion

def mp.okl(r: Result<&2, &2, F.NftError, List<&2, S.NftElem>>, es: List<&2, S.NftElem>, +e: S.NftElem, +x: B.Octets) -> Type:
  match r:
    case Done{l}:
      {S.NftSet.lookup.go(l, x) == S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), S.NftSet.lookup.go(es, x)) : Maybe<&2, S.NftData>}
    case Fail{err}:
      Unit

# h's high end below e's low end: no key is held by both
def mp.disj(c1: Bool, c2: Bool, +h: S.NftElem, +e: S.NftElem, +x: B.Octets, eq1: {S.NftElem.contains(h, x) == c1 : Bool}, eq2: {S.NftElem.contains(e, x) == c2 : Bool}, hlt: {S.NftKey.lt(S.NftElem.hi(h), S.NftElem.lo(e)) == True{} : Bool}) -> {Bool.and(c1, c2) == False{} : Bool}:
  match c1:
    case False{}:
      {==}
    case True{}:
      match c2:
        case False{}:
          {==}
        case True{}:
          +a = el.hi(h, x, eq1)
          +b = el.lo(e, x, eq2)
          +n = ky.lt_not_le(x, S.NftElem.lo(e), ky.le_lt(x, S.NftElem.hi(h), S.NftElem.lo(e), a, hlt))
          Empty.absurd({Bool.and(True{}, True{}) == False{} : Bool}, P.absurd.ft(Equal.trans(Bool, False{}, S.NftKey.le(S.NftElem.lo(e), x), True{}, Equal.sym(Bool, S.NftKey.le(S.NftElem.lo(e), x), False{}, n), b)))

def mp.pick_swap(a: Bool, b: Bool, -da: S.NftData, -db: S.NftData, -r: Maybe<&2, S.NftData>, h: {Bool.and(a, b) == False{} : Bool}) -> {S.NftSet.lookup.pick(a, da, S.NftSet.lookup.pick(b, db, r)) == S.NftSet.lookup.pick(b, db, S.NftSet.lookup.pick(a, da, r)) : Maybe<&2, S.NftData>}:
  match a:
    case True{}:
      match b:
        case True{}:
          Empty.absurd({S.NftSet.lookup.pick(True{}, da, S.NftSet.lookup.pick(True{}, db, r)) == S.NftSet.lookup.pick(True{}, db, S.NftSet.lookup.pick(True{}, da, r)) : Maybe<&2, S.NftData>}, P.absurd.tf(h))
        case False{}:
          {==}
    case False{}:
      {==}

def mp.ins_lk.pick(b1: Bool, b2: Bool, +e: S.NftElem, +h: S.NftElem, +t: List<&2, S.NftElem>, eq2: {S.NftKey.lt(S.NftElem.hi(h), S.NftElem.lo(e)) == b2 : Bool}, r: Result<&2, &2, F.NftError, List<&2, S.NftElem>>, +x: B.Octets, ih: mp.okl(r, t, e, x)) -> mp.okl(S.NftSet.ins.pick(b1, b2, e, h, t, r), Con{h, t}, e, x):
  match b1:
    case True{}:
      {==}
    case False{}:
      match b2:
        case True{}:
          match r:
            case Done{l}:
              %Equal.sym(Maybe<&2, S.NftData>, S.NftSet.lookup.go(l, x), S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), S.NftSet.lookup.go(t, x)), ih) : {S.NftSet.lookup.pick(S.NftElem.contains(h, x), S.NftElem.data(h), _) == S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), S.NftSet.lookup.pick(S.NftElem.contains(h, x), S.NftElem.data(h), S.NftSet.lookup.go(t, x))) : Maybe<&2, S.NftData>}
              mp.pick_swap(S.NftElem.contains(h, x), S.NftElem.contains(e, x), S.NftElem.data(h), S.NftElem.data(e), S.NftSet.lookup.go(t, x), mp.disj(S.NftElem.contains(h, x), S.NftElem.contains(e, x), h, e, x, {==}, {==}, eq2))
            case Fail{err}:
              Unit{}
        case False{}:
          Unit{}

def mp.ins_lk(es: List<&2, S.NftElem>, +e: S.NftElem, +x: B.Octets) -> mp.okl(S.NftSet.ins(es, e), es, e, x):
  match es:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      mp.ins_lk.pick(S.NftKey.lt(S.NftElem.hi(e), S.NftElem.lo(h)), S.NftKey.lt(S.NftElem.hi(h), S.NftElem.lo(e)), e, h, t, {==}, S.NftSet.ins(t, e), x, mp.ins_lk(t, e, x))

def mp.okl_done(r: Result<&2, &2, F.NftError, List<&2, S.NftElem>>, +es: List<&2, S.NftElem>, +e: S.NftElem, +x: B.Octets, s2: S.NftSet, ok: {S.NftSet.wrap(r) == Done{s2} : Result<&2, &2, F.NftError, S.NftSet>}, h: mp.okl(r, es, e, x)) -> {S.NftSet.lookup(s2, x) == S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), S.NftSet.lookup.go(es, x)) : Maybe<&2, S.NftData>}:
  match r:
    case Done{l}:
      %P.done_inj(S.NftSet{l}, s2, ok) : {S.NftSet.lookup(_, x) == S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), S.NftSet.lookup.go(es, x)) : Maybe<&2, S.NftData>}
      h
    case Fail{err}:
      Empty.absurd({S.NftSet.lookup(s2, x) == S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), S.NftSet.lookup.go(es, x)) : Maybe<&2, S.NftData>}, P.absurd.fail_done(err, s2, ok))

def mp.ins_lk.go(v: Bool, +es: List<&2, S.NftElem>, +e: S.NftElem, +x: B.Octets, s2: S.NftSet, ok: {S.NftSet.insert.go(v, es, e) == Done{s2} : Result<&2, &2, F.NftError, S.NftSet>}) -> {S.NftSet.lookup(s2, x) == S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), S.NftSet.lookup.go(es, x)) : Maybe<&2, S.NftData>}:
  match v:
    case False{}:
      Empty.absurd({S.NftSet.lookup(s2, x) == S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), S.NftSet.lookup.go(es, x)) : Maybe<&2, S.NftData>}, P.absurd.fail_done(F.NftErrBadInterval{}, s2, ok))
    case True{}:
      mp.okl_done(S.NftSet.ins(es, e), es, e, x, s2, ok, mp.ins_lk(es, e, x))

def mp.insert(s: S.NftSet, +e: S.NftElem, +x: B.Octets, s2: S.NftSet, ok: {S.NftSet.insert(s, e) == Done{s2} : Result<&2, &2, F.NftError, S.NftSet>}) -> {S.NftSet.lookup(s2, x) == S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), S.NftSet.lookup(s, x)) : Maybe<&2, S.NftData>}:
  match s:
    case S.NftSet{es}:
      mp.ins_lk.go(S.NftElem.valid(e), es, e, x, s2, ok)

def Laws.map_lookup_insert(s, e, x, s2, ok):
  mp.insert(s, e, x, s2, ok)

# Maps built from a list

# the first answer
def mp.orm(m1: Maybe<&2, S.NftData>, m2: Maybe<&2, S.NftData>) -> Maybe<&2, S.NftData>:
  match m1:
    case Some{d}:
      Some{d}
    case None{}:
      m2

def mp.orm_none(m: Maybe<&2, S.NftData>) -> {mp.orm(m, None{}) == m : Maybe<&2, S.NftData>}:
  match m:
    case Some{d}:
      {==}
    case None{}:
      {==}

def mp.orm_step(m: Maybe<&2, S.NftData>, c: Bool, -d: S.NftData, -r: Maybe<&2, S.NftData>) -> {mp.orm(m, S.NftSet.lookup.pick(c, d, r)) == mp.orm(mp.orm(m, S.NftSet.lookup.pick(c, d, None{})), r) : Maybe<&2, S.NftData>}:
  match m:
    case Some{v}:
      {==}
    case None{}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}

def mp.step(c: Bool, +de: S.NftData, +l0: Maybe<&2, S.NftData>, +m: Maybe<&2, S.NftData>, h: {l0 == m : Maybe<&2, S.NftData>}, nn: {c == True{} : Bool} -> {l0 == None{} : Maybe<&2, S.NftData>}) -> {S.NftSet.lookup.pick(c, de, l0) == mp.orm(m, S.NftSet.lookup.pick(c, de, None{})) : Maybe<&2, S.NftData>}:
  match c:
    case True{}:
      +n = nn({==})
      %Equal.trans(Maybe<&2, S.NftData>, None{}, l0, m, Equal.sym(Maybe<&2, S.NftData>, l0, None{}, n), h) : {Some{de} == mp.orm(_, Some{de}) : Maybe<&2, S.NftData>}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, S.NftData>, l0, m, h) : {_ == mp.orm(m, None{}) : Maybe<&2, S.NftData>}
      Equal.sym(Maybe<&2, S.NftData>, mp.orm(m, None{}), m, mp.orm_none(m))

def mp.okol(r: Result<&2, &2, F.NftError, S.NftSet>, +x: B.Octets, m: Maybe<&2, S.NftData>) -> Type:
  match r:
    case Done{s}:
      {S.NftSet.lookup(s, x) == m : Maybe<&2, S.NftData>}
    case Fail{err}:
      Unit

def mp.add.ins(+s0: S.NftSet, +e: S.NftElem, r2: Result<&2, &2, F.NftError, S.NftSet>, +eq: {S.NftSet.insert(s0, e) == r2 : Result<&2, &2, F.NftError, S.NftSet>}, +x: B.Octets, +m: Maybe<&2, S.NftData>, +hw: {S.NftSet.wf(s0) == True{} : Bool}, +h: {S.NftSet.lookup(s0, x) == m : Maybe<&2, S.NftData>}) -> mp.okol(r2, x, mp.orm(m, S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), None{}))):
  match r2:
    case Done{+s1}:
      Equal.trans(Maybe<&2, S.NftData>, S.NftSet.lookup(s1, x), S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), S.NftSet.lookup(s0, x)), mp.orm(m, S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), None{})), mp.insert(s0, e, x, s1, eq), mp.step(S.NftElem.contains(e, x), S.NftElem.data(e), S.NftSet.lookup(s0, x), m, h, w => mp.noov_ins(s0, e, x, s1, hw, eq, w)))
    case Fail{err}:
      Unit{}

def mp.add(r: Result<&2, &2, F.NftError, S.NftSet>, +e: S.NftElem, +x: B.Octets, +m: Maybe<&2, S.NftData>, hw: {P.okw2(r) == True{} : Bool}, h: mp.okol(r, x, m)) -> mp.okol(S.NftSet.add(r, e), x, mp.orm(m, S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), None{}))):
  match r:
    case Done{+s0}:
      mp.add.ins(s0, e, S.NftSet.insert(s0, e), {==}, x, m, hw, h)
    case Fail{err}:
      Unit{}

def mp.of_list(es: List<&2, S.NftElem>, +r: Result<&2, &2, F.NftError, S.NftSet>, +x: B.Octets, +m: Maybe<&2, S.NftData>, +hw: {P.okw2(r) == True{} : Bool}, h: mp.okol(r, x, m)) -> mp.okol(S.NftSet.of_list.go(es, r), x, mp.orm(m, Laws.list_lookup(es, x))):
  match es:
    case Nil{}:
      %Equal.sym(Maybe<&2, S.NftData>, mp.orm(m, None{}), m, mp.orm_none(m)) : mp.okol(r, x, _)
      h
    case Con{+e, +t}:
      %Equal.sym(Maybe<&2, S.NftData>, mp.orm(m, S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), Laws.list_lookup(t, x))), mp.orm(mp.orm(m, S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), None{})), Laws.list_lookup(t, x)), mp.orm_step(m, S.NftElem.contains(e, x), S.NftElem.data(e), Laws.list_lookup(t, x))) : mp.okol(S.NftSet.of_list.go(t, S.NftSet.add(r, e)), x, _)
      mp.of_list(t, S.NftSet.add(r, e), x, mp.orm(m, S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), None{})), P.add_wf(r, e, hw), mp.add(r, e, x, m, hw, h))

def mp.okol_done(r: Result<&2, &2, F.NftError, S.NftSet>, +s: S.NftSet, +x: B.Octets, +m: Maybe<&2, S.NftData>, ok: {r == Done{s} : Result<&2, &2, F.NftError, S.NftSet>}, h: mp.okol(r, x, m)) -> {S.NftSet.lookup(s, x) == m : Maybe<&2, S.NftData>}:
  match r:
    case Done{s1}:
      %P.done_inj(s1, s, ok) : {S.NftSet.lookup(_, x) == m : Maybe<&2, S.NftData>}
      h
    case Fail{err}:
      Empty.absurd({S.NftSet.lookup(s, x) == m : Maybe<&2, S.NftData>}, P.absurd.fail_done(err, s, ok))

def Laws.map_lookup_of_list(es, s, x, ok):
  mp.okol_done(S.NftSet.of_list(es), s, x, Laws.list_lookup(es, x), ok, mp.of_list(es, Done{S.NftSet.empty()}, x, None{}, {==}, {==}))

# Vectors: by computation

def Laws.map_lookup_vec():
  {==}

def Laws.map_lookup_unique_sat():
  {==}
