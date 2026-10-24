# Proofs of LAWS_expr.bend.
#
# The plan:
# * Payload loads: the load is NftPayload.cut of the base's bytes, so with
#   the base known and the bound decided it is the slice, by rewriting; its
#   byte i is the base's byte at offset + i because a string is its first
#   bytes followed by the rest (bend-osdev-bytes' take_drop), and reading
#   inside the first part, or past it, reads the part (ex.at_take,
#   ex.at_drop, through the list form of Octets).
# * Comparisons: equal keys are equal byte lists (each U32.cmp equal, so
#   each byte equal by bend-osdev-u32's value laws), so equal Octets
#   (octets_of_to); the reverse comparisons flip, by PROOF_map.bend's
#   cm.list_flip; a one-byte key is its byte masked (octets_to_of).
# * Limits: a fresh bucket is full (its credit is its capacity, and a full
#   bucket refills to its capacity, by W64.cmp's value law), so the first
#   packet conforms when the capacity covers its cost. `over` changes only
#   the bit NftBucket.take answers, which every later step passes on
#   unchanged, by induction on the bucket list.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ../word64/word64.bend as W
import ../word64/LAWS.bend as WL
import ../word64/PROOF.bend as WP
import ./sets.bend as S
import ./expr.bend as X
import ./PROOF_map.bend as PM
import ./LAWS_expr.bend as Laws

# Contradictions and Nat

def ex.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def ex.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : ex.bool(_)
  Unit{}

def ex.succ(+a: Nat, +b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  Equal.cong(Nat, Nat, z => 1n+z, a, b, e)

def ex.sub_zero(y: Nat) -> {Nat.sub(y, 0n) == y : Nat}:
  match y:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a + b <= c gives b <= c - a
def ex.le_sub(a: Nat, +b: Nat, c: Nat, h: {Nat.is_le(Nat.add(a, b), c) == True{} : Bool}) -> {Nat.is_le(b, Nat.sub(c, a)) == True{} : Bool}:
  match a c:
    case 0n _:
      %Equal.sym(Nat, Nat.sub(c, 0n), c, ex.sub_zero(c)) : {Nat.is_le(b, _) == True{} : Bool}
      h
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(b, Nat.sub(0n, 1n+ap)) == True{} : Bool}, ex.ft(h))
    case 1n+ap 1n+cp:
      ex.le_sub(ap, b, cp, h)

# a + b <= c gives a <= c
def ex.le_part(a: Nat, -b: Nat, c: Nat, h: {Nat.is_le(Nat.add(a, b), c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a c:
    case 0n 0n:
      {==}
    case 0n 1n+cp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, ex.ft(h))
    case 1n+ap 1n+cp:
      ex.le_part(ap, b, cp, h)

# Byte reads

def ex.lat_app(xs: List<&2, U32>, +ys: List<&2, U32>, i: Nat, h: {Nat.is_lt(i, B.len(xs)) == True{} : Bool}) -> {B.at(B.append(xs, ys), i) == B.at(xs, i) : Maybe<&2, U32>}:
  match xs i:
    case Nil{} 0n:
      Empty.absurd({B.at(B.append(Nil{}, ys), 0n) == B.at(Nil{}, 0n) : Maybe<&2, U32>}, ex.ft(h))
    case Nil{} 1n+ip:
      Empty.absurd({B.at(B.append(Nil{}, ys), 1n+ip) == B.at(Nil{}, 1n+ip) : Maybe<&2, U32>}, ex.ft(h))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+ip:
      ex.lat_app(t, ys, ip, h)

def ex.lt_list(+t: B.Octets, +i: Nat, h: {Nat.is_lt(i, B.Octets.len(t)) == True{} : Bool}) -> {Nat.is_lt(i, B.len(B.Octets.to_list(t))) == True{} : Bool}:
  %BL.octets_len_list(t) : {Nat.is_lt(i, _) == True{} : Bool}
  h

# reading inside the first part of a joined string reads the part
def ex.at_app(+t: B.Octets, +d: B.Octets, +i: Nat, h: {Nat.is_lt(i, B.Octets.len(t)) == True{} : Bool}) -> {B.Octets.at(B.Octets.append(t, d), i) == B.Octets.at(t, i) : Maybe<&2, U32>}:
  +e1 = BL.octets_at_list(B.Octets.append(t, d), i)
  +e2 = Equal.cong(List<&2, U32>, Maybe<&2, U32>, y => B.at(y, i), B.Octets.to_list(B.Octets.append(t, d)), B.append(B.Octets.to_list(t), B.Octets.to_list(d)), BL.octets_append_list(t, d))
  +e3 = ex.lat_app(B.Octets.to_list(t), B.Octets.to_list(d), i, ex.lt_list(t, i, h))
  +e4 = Equal.sym(Maybe<&2, U32>, B.Octets.at(t, i), B.at(B.Octets.to_list(t), i), BL.octets_at_list(t, i))
  Equal.trans(Maybe<&2, U32>, B.Octets.at(B.Octets.append(t, d), i), B.at(B.Octets.to_list(B.Octets.append(t, d)), i), B.Octets.at(t, i), e1, Equal.trans(Maybe<&2, U32>, B.at(B.Octets.to_list(B.Octets.append(t, d)), i), B.at(B.append(B.Octets.to_list(t), B.Octets.to_list(d)), i), B.Octets.at(t, i), e2, Equal.trans(Maybe<&2, U32>, B.at(B.append(B.Octets.to_list(t), B.Octets.to_list(d)), i), B.at(B.Octets.to_list(t), i), B.Octets.at(t, i), e3, e4)))

def ex.at_take(+n: Nat, +x: B.Octets, +i: Nat, h: {Nat.is_lt(i, B.Octets.len(B.Octets.take(n, x))) == True{} : Bool}) -> {B.Octets.at(B.Octets.take(n, x), i) == B.Octets.at(x, i) : Maybe<&2, U32>}:
  +t = B.Octets.take(n, x)
  +d = B.Octets.drop(n, x)
  +e = Equal.cong(B.Octets, Maybe<&2, U32>, y => B.Octets.at(y, i), x, B.Octets.append(t, d), Equal.sym(B.Octets, B.Octets.append(t, d), x, BL.octets_take_drop(n, x)))
  +f = ex.at_app(t, d, i, h)
  Equal.sym(Maybe<&2, U32>, B.Octets.at(x, i), B.Octets.at(t, i), Equal.trans(Maybe<&2, U32>, B.Octets.at(x, i), B.Octets.at(B.Octets.append(t, d), i), B.Octets.at(t, i), e, f))

def ex.at_drop(+off: Nat, +i: Nat, +o: B.Octets, hoff: {Nat.is_le(off, B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.at(B.Octets.drop(off, o), i) == B.Octets.at(o, Nat.add(off, i)) : Maybe<&2, U32>}:
  +t0 = B.Octets.take(off, o)
  +x = B.Octets.drop(off, o)
  +el = BL.octets_len_take_le(off, o, hoff)
  +e1 = Equal.cong(B.Octets, Maybe<&2, U32>, y => B.Octets.at(y, Nat.add(off, i)), o, B.Octets.append(t0, x), Equal.sym(B.Octets, B.Octets.append(t0, x), o, BL.octets_take_drop(off, o)))
  +e2 = Equal.cong(Nat, Maybe<&2, U32>, y => B.Octets.at(B.Octets.append(t0, x), Nat.add(y, i)), off, B.Octets.len(t0), Equal.sym(Nat, B.Octets.len(t0), off, el))
  +e3 = BL.octets_at_append_add(t0, x, i)
  Equal.sym(Maybe<&2, U32>, B.Octets.at(o, Nat.add(off, i)), B.Octets.at(x, i), Equal.trans(Maybe<&2, U32>, B.Octets.at(o, Nat.add(off, i)), B.Octets.at(B.Octets.append(t0, x), Nat.add(off, i)), B.Octets.at(x, i), e1, Equal.trans(Maybe<&2, U32>, B.Octets.at(B.Octets.append(t0, x), Nat.add(off, i)), B.Octets.at(B.Octets.append(t0, x), Nat.add(B.Octets.len(t0), i)), B.Octets.at(x, i), e2, e3)))

def ex.le_drop(+off: Nat, +len: Nat, +o: B.Octets, hf: {Nat.is_le(Nat.add(off, len), B.Octets.len(o)) == True{} : Bool}) -> {Nat.is_le(len, B.Octets.len(B.Octets.drop(off, o))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.drop(off, o)), Nat.sub(B.Octets.len(o), off), BL.octets_len_drop(off, o)) : {Nat.is_le(len, _) == True{} : Bool}
  ex.le_sub(off, len, B.Octets.len(o), hf)

def ex.lt_take(+len: Nat, +x: B.Octets, +i: Nat, hl: {Nat.is_le(len, B.Octets.len(x)) == True{} : Bool}, hi: {Nat.is_lt(i, len) == True{} : Bool}) -> {Nat.is_lt(i, B.Octets.len(B.Octets.take(len, x))) == True{} : Bool}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.take(len, x)), len, BL.octets_len_take_le(len, x, hl)) : {Nat.is_lt(i, _) == True{} : Bool}
  hi

def ex.at_slice(+off: Nat, +len: Nat, +i: Nat, +o: B.Octets, +hf: {Nat.is_le(Nat.add(off, len), B.Octets.len(o)) == True{} : Bool}, hi: {Nat.is_lt(i, len) == True{} : Bool}) -> {B.Octets.at(B.Octets.slice(off, len, o), i) == B.Octets.at(o, Nat.add(off, i)) : Maybe<&2, U32>}:
  +x = B.Octets.drop(off, o)
  +e1 = ex.at_take(len, x, i, ex.lt_take(len, x, i, ex.le_drop(off, len, o, hf), hi))
  +e2 = ex.at_drop(off, i, o, ex.le_part(off, len, B.Octets.len(o), hf))
  Equal.trans(Maybe<&2, U32>, B.Octets.at(B.Octets.take(len, x), i), B.Octets.at(x, i), B.Octets.at(o, Nat.add(off, i)), e1, e2)

# Payload loads

def ex.load(+b: X.NftPayloadBase, +off: Nat, +len: Nat, +sets: List<&2, S.NftNamedSet>, +p: X.NftPacket, +o: B.Octets, h: {X.NftPacket.base(b, p) == Some{o} : Maybe<&2, B.Octets>}, hf: {Nat.is_le(Nat.add(off, len), B.Octets.len(o)) == True{} : Bool}) -> {X.NftSrc.load(X.NftSrcPayload{b, off, len}, sets, p) == Some{B.Octets.slice(off, len, o)} : Maybe<&2, B.Octets>}:
  %Equal.sym(Maybe<&2, B.Octets>, X.NftPacket.base(b, p), Some{o}, h) : {X.NftPayload.slice(_, off, len) == Some{B.Octets.slice(off, len, o)} : Maybe<&2, B.Octets>}
  %Equal.sym(Bool, Nat.is_le(Nat.add(off, len), B.Octets.len(o)), True{}, hf) : {X.NftPayload.cut(_, off, len, o) == Some{B.Octets.slice(off, len, o)} : Maybe<&2, B.Octets>}
  {==}

def Laws.payload_load(b, off, len, sets, p, o, h, hf):
  ex.load(b, off, len, sets, p, o, h, hf)

def Laws.payload_at(b, off, len, i, sets, p, o, h, hf, hi):
  +hf = hf
  %Equal.sym(Maybe<&2, B.Octets>, X.NftSrc.load(X.NftSrcPayload{b, off, len}, sets, p), Some{B.Octets.slice(off, len, o)}, ex.load(b, off, len, sets, p, o, h, hf)) : {Laws.load_at(_, i) == B.Octets.at(o, Nat.add(off, i)) : Maybe<&2, U32>}
  ex.at_slice(off, len, i, o, hf, hi)

def Laws.payload_short(b, off, len, sets, p, o, h, hf):
  %Equal.sym(Maybe<&2, B.Octets>, X.NftPacket.base(b, p), Some{o}, h) : {X.NftPayload.slice(_, off, len) == None{} : Maybe<&2, B.Octets>}
  %Equal.sym(Bool, Nat.is_le(Nat.add(off, len), B.Octets.len(o)), False{}, hf) : {X.NftPayload.cut(_, off, len, o) == None{} : Maybe<&2, B.Octets>}
  {==}

def Laws.payload_no_base(b, off, len, sets, p, h):
  %Equal.sym(Maybe<&2, B.Octets>, X.NftPacket.base(b, p), None{}, h) : {X.NftPayload.slice(_, off, len) == None{} : Maybe<&2, B.Octets>}
  {==}

# Comparisons

def ex.pick_eq_l(c: Cmp, -r: Cmp, h: {Cmp.is_eq(S.NftKey.cmp.pick(c, r)) == True{} : Bool}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case EQ{}:
      {==}
    case LT{}:
      Empty.absurd({Cmp.is_eq(LT{}) == True{} : Bool}, ex.ft(h))
    case GT{}:
      Empty.absurd({Cmp.is_eq(GT{}) == True{} : Bool}, ex.ft(h))

def ex.pick_eq_r(c: Cmp, -r: Cmp, h: {Cmp.is_eq(S.NftKey.cmp.pick(c, r)) == True{} : Bool}) -> {Cmp.is_eq(r) == True{} : Bool}:
  match c:
    case EQ{}:
      h
    case LT{}:
      Empty.absurd({Cmp.is_eq(r) == True{} : Bool}, ex.ft(h))
    case GT{}:
      Empty.absurd({Cmp.is_eq(r) == True{} : Bool}, ex.ft(h))

def ex.nat_eq(a: Nat, b: Nat, h: {Cmp.is_eq(Nat.cmp(a, b)) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, ex.ft(h))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, ex.ft(h))
    case 1n+ +ap 1n+ +bp:
      ex.succ(ap, bp, ex.nat_eq(ap, bp, h))

def ex.u32_eq(+x: U32, +y: U32, h: {Cmp.is_eq(U32.cmp(x, y)) == True{} : Bool}) -> {x == y : U32}:
  +h2 = Equal.trans(Bool, Cmp.is_eq(Nat.cmp(U32.to_nat(x), U32.to_nat(y))), Cmp.is_eq(U32.cmp(x, y)), True{}, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), Nat.cmp(U32.to_nat(x), U32.to_nat(y)), U32.cmp(x, y), Equal.sym(Cmp, U32.cmp(x, y), Nat.cmp(U32.to_nat(x), U32.to_nat(y)), UL.u32_cmp_value(x, y))), h)
  UL.u32_value_eq(x, y, ex.nat_eq(U32.to_nat(x), U32.to_nat(y), h2))

def ex.list_eq(a: List<&2, U32>, b: List<&2, U32>, h: {Cmp.is_eq(S.NftKey.cmp.list(a, b)) == True{} : Bool}) -> {a == b : List<&2, U32>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      Empty.absurd({Nil{} == Con{y, ys} : List<&2, U32>}, ex.ft(h))
    case Con{x, xs} Nil{}:
      Empty.absurd({Con{x, xs} == Nil{} : List<&2, U32>}, ex.ft(h))
    case Con{+x, +xs} Con{+y, +ys}:
      +h = h
      +e1 = ex.u32_eq(x, y, ex.pick_eq_l(U32.cmp(x, y), S.NftKey.cmp.list(xs, ys), h))
      +e2 = ex.list_eq(xs, ys, ex.pick_eq_r(U32.cmp(x, y), S.NftKey.cmp.list(xs, ys), h))
      %Equal.sym(U32, x, y, e1) : {Con{_, xs} == Con{y, ys} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, xs, ys, e2) : {Con{y, _} == Con{y, ys} : List<&2, U32>}
      {==}

def Laws.cmp_eq_holds(v, w, sets, h):
  +el = ex.list_eq(B.Octets.to_list(v), B.Octets.to_list(w), h)
  Equal.trans(B.Octets, v, B.Octets.of_list(B.Octets.to_list(v)), w, Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(v)), v, BL.octets_of_to(v)), Equal.trans(B.Octets, B.Octets.of_list(B.Octets.to_list(v)), B.Octets.of_list(B.Octets.to_list(w)), w, Equal.cong(List<&2, U32>, B.Octets, y => B.Octets.of_list(y), B.Octets.to_list(v), B.Octets.to_list(w), el), BL.octets_of_to(w)))

def Laws.cmp_eq_refl(v, sets):
  %Equal.sym(Cmp, S.NftKey.cmp.list(B.Octets.to_list(v), B.Octets.to_list(v)), EQ{}, PM.cm.list_refl(B.Octets.to_list(v))) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def Laws.cmp_ne(v, w, sets):
  {==}

def Laws.cmp_lt(v, w, sets):
  {==}

def Laws.cmp_le(v, w, sets):
  {==}

def ex.gt_flip(c: Cmp) -> {Cmp.is_gt(c) == Cmp.is_lt(PM.cm.flip(c)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def ex.ge_flip(c: Cmp) -> {Cmp.is_ge(c) == Cmp.is_le(PM.cm.flip(c)) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Laws.cmp_gt(v, w, sets):
  %Equal.sym(Cmp, S.NftKey.cmp.list(B.Octets.to_list(w), B.Octets.to_list(v)), PM.cm.flip(S.NftKey.cmp.list(B.Octets.to_list(v), B.Octets.to_list(w))), PM.cm.list_flip(B.Octets.to_list(v), B.Octets.to_list(w))) : {Cmp.is_gt(S.NftKey.cmp.list(B.Octets.to_list(v), B.Octets.to_list(w))) == Cmp.is_lt(_) : Bool}
  ex.gt_flip(S.NftKey.cmp.list(B.Octets.to_list(v), B.Octets.to_list(w)))

def Laws.cmp_ge(v, w, sets):
  %Equal.sym(Cmp, S.NftKey.cmp.list(B.Octets.to_list(w), B.Octets.to_list(v)), PM.cm.flip(S.NftKey.cmp.list(B.Octets.to_list(v), B.Octets.to_list(w))), PM.cm.list_flip(B.Octets.to_list(v), B.Octets.to_list(w))) : {Cmp.is_ge(S.NftKey.cmp.list(B.Octets.to_list(v), B.Octets.to_list(w))) == Cmp.is_le(_) : Bool}
  ex.ge_flip(S.NftKey.cmp.list(B.Octets.to_list(v), B.Octets.to_list(w)))

def Laws.range_contains(lo, hi, v, sets):
  {==}

def Laws.not_range_contains(lo, hi, v, sets):
  {==}

def ex.not_xor_t(b: Bool) -> {Bool.not(Bool.xor(b, True{})) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ex.not_xor_f(b: Bool) -> {Bool.not(Bool.xor(b, False{})) == Bool.not(b) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.in_set_mem(s, v, sets):
  ex.not_xor_t(S.NftSet.mem(s, v))

def Laws.not_in_set_mem(s, v, sets):
  ex.not_xor_f(S.NftSet.mem(s, v))

def ex.pick_eq(c: Cmp) -> {S.NftKey.cmp.pick(c, EQ{}) == c : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Laws.key_u8_cmp(a, b):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([a])), B.mask([a]), BL.octets_to_of([a])) : {S.NftKey.cmp.list(_, B.Octets.to_list(B.Octets.of_list([b]))) == U32.cmp(B.byte(a), B.byte(b)) : Cmp}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([b])), B.mask([b]), BL.octets_to_of([b])) : {S.NftKey.cmp.list(B.mask([a]), _) == U32.cmp(B.byte(a), B.byte(b)) : Cmp}
  ex.pick_eq(U32.cmp(B.byte(a), B.byte(b)))

# Limits: the first packet

def ex.ge_refl(+a: W.W64) -> {W.W64.is_ge(a, a) == True{} : Bool}:
  %Equal.sym(Cmp, W.W64.cmp(a, a), Nat.cmp(W.W64.to_nat(a), W.W64.to_nat(a)), WL.cmp_value(a, a)) : {Cmp.is_ge(_) == True{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(W.W64.to_nat(a), W.W64.to_nat(a)), EQ{}, PM.cm.nat_refl(W.W64.to_nat(a))) : {Cmp.is_ge(_) == True{} : Bool}
  {==}

def ex.refill_full(+credit: W.W64, +elapsed: W.W64, +rate: U32, +cap: W.W64, h: {W.W64.is_ge(credit, cap) == True{} : Bool}) -> {X.NftBucket.refill(credit, elapsed, rate, cap) == cap : W.W64}:
  %Equal.sym(Bool, W.W64.is_ge(credit, cap), True{}, h) : {X.NftBucket.refill.go(_, U32.is_eq(rate, 0), credit, elapsed, rate, cap) == cap : W.W64}
  {==}

def ex.cap(+rate: U32, +unit: U32, +burst: U32) -> W.W64:
  W.W64.mul(W.W64.from_u32(X.NftBucket.tokens(U32.is_eq(burst, 0), burst, rate)), W.W64.from_u32(unit))

def ex.fresh_step(+rate: U32, +unit: U32, +burst: U32, +bytes: Bool, +over: Bool, +now: W.W64, +len: U32) -> {X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, over}, ex.cap(rate, unit, burst), now, now, len) == X.NftBucket.take(W.W64.is_ge(ex.cap(rate, unit, burst), X.NftBucket.cost(bytes, unit, len)), over, ex.cap(rate, unit, burst), X.NftBucket.cost(bytes, unit, len)) : X.NftBucketStep}:
  +k = ex.cap(rate, unit, burst)
  +c = X.NftBucket.cost(bytes, unit, len)
  +el = X.NftBucket.elapsed(W.W64.is_ge(now, now), now, now)
  Equal.cong(W.W64, X.NftBucketStep, y => X.NftBucket.take(W.W64.is_ge(y, c), over, y, c), X.NftBucket.refill(k, el, rate, k), k, ex.refill_full(k, el, rate, k, ex.ge_refl(k)))

def ex.ok_of(b: Bool, -env: X.NftEnv) -> {Laws.expr_ok(X.NftExprOut.of(b, env)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ex.env_of(b: Bool, +env: X.NftEnv) -> {Laws.expr_env(X.NftExprOut.of(b, env)) == env : X.NftEnv}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ex.take_ok(conf: Bool, +over: Bool, +c: W.W64, +cost: W.W64, +id: U32, +now: W.W64, +p: X.NftPacket, +cs: List<&2, X.NftCounterVal>) -> {Laws.expr_ok(X.NftExpr.limit_go(X.NftLimitOut.hit(X.NftBucket.take(conf, over, c, cost), id, now, Nil{}), p, cs, now)) == Bool.xor(conf, over) : Bool}:
  match conf:
    case True{}:
      ex.ok_of(Bool.xor(True{}, over), X.NftEnv{p, X.NftState{cs, Con{X.NftBucket{id, W.W64.sub(c, cost), now}, Nil{}}}, now})
    case False{}:
      ex.ok_of(Bool.xor(False{}, over), X.NftEnv{p, X.NftState{cs, Con{X.NftBucket{id, c, now}, Nil{}}}, now})

def ex.tok(z: Bool, -burst: U32, -rate: U32) -> {Laws.limit_tokens(z, burst, rate) == X.NftBucket.tokens(z, burst, rate) : U32}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

def ex.cost(bytes: Bool, -unit: U32, -len: U32) -> {Laws.limit_cost(bytes, unit, len) == X.NftBucket.cost(bytes, unit, len) : W.W64}:
  match bytes:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.limit_fresh(id, rate, unit, burst, bytes, over, sets, p, cs, now):
  +len = X.NftPacket.length(p)
  +k = ex.cap(rate, unit, burst)
  +c = X.NftBucket.cost(bytes, unit, len)
  +e1 = Equal.cong(X.NftBucketStep, Bool, y => Laws.expr_ok(X.NftExpr.limit_go(X.NftLimitOut.hit(y, id, now, Nil{}), p, cs, now)), X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, over}, k, now, now, len), X.NftBucket.take(W.W64.is_ge(k, c), over, k, c), ex.fresh_step(rate, unit, burst, bytes, over, now, len))
  +e2 = ex.take_ok(W.W64.is_ge(k, c), over, k, c, id, now, p, cs)
  +ek = Equal.cong(U32, W.W64, y => W.W64.mul(W.W64.from_u32(y), W.W64.from_u32(unit)), X.NftBucket.tokens(U32.is_eq(burst, 0), burst, rate), Laws.limit_tokens(U32.is_eq(burst, 0), burst, rate), Equal.sym(U32, Laws.limit_tokens(U32.is_eq(burst, 0), burst, rate), X.NftBucket.tokens(U32.is_eq(burst, 0), burst, rate), ex.tok(U32.is_eq(burst, 0), burst, rate)))
  +ec = Equal.sym(W.W64, Laws.limit_cost(bytes, unit, len), c, ex.cost(bytes, unit, len))
  +e3 = Equal.cong(W.W64, Bool, y => Bool.xor(W.W64.is_ge(y, c), over), k, Laws.limit_cap(rate, unit, burst), ek)
  +e4 = Equal.cong(W.W64, Bool, y => Bool.xor(W.W64.is_ge(Laws.limit_cap(rate, unit, burst), y), over), c, Laws.limit_cost(bytes, unit, len), ec)
  Equal.trans(Bool, Laws.expr_ok(X.NftExpr.limit_go(X.NftLimitOut.hit(X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, over}, k, now, now, len), id, now, Nil{}), p, cs, now)), Bool.xor(W.W64.is_ge(k, c), over), Bool.xor(W.W64.is_ge(Laws.limit_cap(rate, unit, burst), Laws.limit_cost(bytes, unit, len)), over), Equal.trans(Bool, Laws.expr_ok(X.NftExpr.limit_go(X.NftLimitOut.hit(X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, over}, k, now, now, len), id, now, Nil{}), p, cs, now)), Laws.expr_ok(X.NftExpr.limit_go(X.NftLimitOut.hit(X.NftBucket.take(W.W64.is_ge(k, c), over, k, c), id, now, Nil{}), p, cs, now)), Bool.xor(W.W64.is_ge(k, c), over), e1, e2), Equal.trans(Bool, Bool.xor(W.W64.is_ge(k, c), over), Bool.xor(W.W64.is_ge(Laws.limit_cap(rate, unit, burst), c), over), Bool.xor(W.W64.is_ge(Laws.limit_cap(rate, unit, burst), Laws.limit_cost(bytes, unit, len)), over), e3, e4))

# Limits: over

def ex.flips(s: X.NftBucketStep) -> X.NftBucketStep:
  match s:
    case X.NftBucketStep{m, c}:
      X.NftBucketStep{Bool.not(m), c}

def ex.flipm(o: X.NftLimitOut) -> X.NftLimitOut:
  match o:
    case X.NftLimitOut{m, bs}:
      X.NftLimitOut{Bool.not(m), bs}

def ex.take_flip(conf: Bool, +c: W.W64, +cost: W.W64) -> {X.NftBucket.take(conf, True{}, c, cost) == ex.flips(X.NftBucket.take(conf, False{}, c, cost)) : X.NftBucketStep}:
  match conf:
    case True{}:
      {==}
    case False{}:
      {==}

def ex.step_flip(+rate: U32, +unit: U32, +burst: U32, +bytes: Bool, +credit: W.W64, +last: W.W64, +now: W.W64, +len: U32) -> {X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, True{}}, credit, last, now, len) == ex.flips(X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, False{}}, credit, last, now, len)) : X.NftBucketStep}:
  +k = ex.cap(rate, unit, burst)
  +c = X.NftBucket.refill(credit, X.NftBucket.elapsed(W.W64.is_ge(now, last), now, last), rate, k)
  +cost = X.NftBucket.cost(bytes, unit, len)
  ex.take_flip(W.W64.is_ge(c, cost), c, cost)

def ex.hit_flip(s: X.NftBucketStep, -id: U32, -now: W.W64, -t: List<&2, X.NftBucket>) -> {X.NftLimitOut.hit(ex.flips(s), id, now, t) == ex.flipm(X.NftLimitOut.hit(s, id, now, t)) : X.NftLimitOut}:
  match s:
    case X.NftBucketStep{m, c}:
      {==}

def ex.cons_flip(-b: X.NftBucket, r: X.NftLimitOut) -> {X.NftLimitOut.cons(b, ex.flipm(r)) == ex.flipm(X.NftLimitOut.cons(b, r)) : X.NftLimitOut}:
  match r:
    case X.NftLimitOut{m, bs}:
      {==}

def ex.pick_flip(hit: Bool, +bid: U32, +credit: W.W64, +last: W.W64, +t: List<&2, X.NftBucket>, +rate: U32, +unit: U32, +burst: U32, +bytes: Bool, +now: W.W64, +len: U32, +rt: X.NftLimitOut, +rf: X.NftLimitOut, ih: {rt == ex.flipm(rf) : X.NftLimitOut}) -> {X.NftLimitOut.pick(hit, bid, credit, last, t, X.NftLimitSpec{rate, unit, burst, bytes, True{}}, now, len, rt) == ex.flipm(X.NftLimitOut.pick(hit, bid, credit, last, t, X.NftLimitSpec{rate, unit, burst, bytes, False{}}, now, len, rf)) : X.NftLimitOut}:
  match hit:
    case True{}:
      Equal.trans(X.NftLimitOut, X.NftLimitOut.hit(X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, True{}}, credit, last, now, len), bid, now, t), X.NftLimitOut.hit(ex.flips(X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, False{}}, credit, last, now, len)), bid, now, t), ex.flipm(X.NftLimitOut.hit(X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, False{}}, credit, last, now, len), bid, now, t)), Equal.cong(X.NftBucketStep, X.NftLimitOut, y => X.NftLimitOut.hit(y, bid, now, t), X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, True{}}, credit, last, now, len), ex.flips(X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, False{}}, credit, last, now, len)), ex.step_flip(rate, unit, burst, bytes, credit, last, now, len)), ex.hit_flip(X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, False{}}, credit, last, now, len), bid, now, t))
    case False{}:
      Equal.trans(X.NftLimitOut, X.NftLimitOut.cons(X.NftBucket{bid, credit, last}, rt), X.NftLimitOut.cons(X.NftBucket{bid, credit, last}, ex.flipm(rf)), ex.flipm(X.NftLimitOut.cons(X.NftBucket{bid, credit, last}, rf)), Equal.cong(X.NftLimitOut, X.NftLimitOut, y => X.NftLimitOut.cons(X.NftBucket{bid, credit, last}, y), rt, ex.flipm(rf), ih), ex.cons_flip(X.NftBucket{bid, credit, last}, rf))

def ex.run_flip(bs: List<&2, X.NftBucket>, +id: U32, +rate: U32, +unit: U32, +burst: U32, +bytes: Bool, +now: W.W64, +len: U32) -> {X.NftLimitOut.run(bs, id, X.NftLimitSpec{rate, unit, burst, bytes, True{}}, now, len) == ex.flipm(X.NftLimitOut.run(bs, id, X.NftLimitSpec{rate, unit, burst, bytes, False{}}, now, len)) : X.NftLimitOut}:
  match bs:
    case Nil{}:
      +k = ex.cap(rate, unit, burst)
      Equal.trans(X.NftLimitOut, X.NftLimitOut.hit(X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, True{}}, k, now, now, len), id, now, Nil{}), X.NftLimitOut.hit(ex.flips(X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, False{}}, k, now, now, len)), id, now, Nil{}), ex.flipm(X.NftLimitOut.hit(X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, False{}}, k, now, now, len), id, now, Nil{})), Equal.cong(X.NftBucketStep, X.NftLimitOut, y => X.NftLimitOut.hit(y, id, now, Nil{}), X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, True{}}, k, now, now, len), ex.flips(X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, False{}}, k, now, now, len)), ex.step_flip(rate, unit, burst, bytes, k, now, now, len)), ex.hit_flip(X.NftBucket.step(X.NftLimitSpec{rate, unit, burst, bytes, False{}}, k, now, now, len), id, now, Nil{}))
    case Con{b, +t}:
      match b:
        case X.NftBucket{+bid, +credit, +last}:
          ex.pick_flip(U32.is_eq(bid, id), bid, credit, last, t, rate, unit, burst, bytes, now, len, X.NftLimitOut.run(t, id, X.NftLimitSpec{rate, unit, burst, bytes, True{}}, now, len), X.NftLimitOut.run(t, id, X.NftLimitSpec{rate, unit, burst, bytes, False{}}, now, len), ex.run_flip(t, id, rate, unit, burst, bytes, now, len))

def ex.go_flip(r: X.NftLimitOut, +p: X.NftPacket, +cs: List<&2, X.NftCounterVal>, +now: W.W64) -> {Laws.expr_ok(X.NftExpr.limit_go(ex.flipm(r), p, cs, now)) == Bool.not(Laws.expr_ok(X.NftExpr.limit_go(r, p, cs, now))) : Bool}:
  match r:
    case X.NftLimitOut{+m, +bs}:
      Equal.trans(Bool, Laws.expr_ok(X.NftExprOut.of(Bool.not(m), X.NftEnv{p, X.NftState{cs, bs}, now})), Bool.not(m), Bool.not(Laws.expr_ok(X.NftExprOut.of(m, X.NftEnv{p, X.NftState{cs, bs}, now}))), ex.ok_of(Bool.not(m), X.NftEnv{p, X.NftState{cs, bs}, now}), Equal.cong(Bool, Bool, y => Bool.not(y), m, Laws.expr_ok(X.NftExprOut.of(m, X.NftEnv{p, X.NftState{cs, bs}, now})), Equal.sym(Bool, Laws.expr_ok(X.NftExprOut.of(m, X.NftEnv{p, X.NftState{cs, bs}, now})), m, ex.ok_of(m, X.NftEnv{p, X.NftState{cs, bs}, now}))))

def ex.go_env(r: X.NftLimitOut, +p: X.NftPacket, +cs: List<&2, X.NftCounterVal>, +now: W.W64) -> {Laws.expr_env(X.NftExpr.limit_go(ex.flipm(r), p, cs, now)) == Laws.expr_env(X.NftExpr.limit_go(r, p, cs, now)) : X.NftEnv}:
  match r:
    case X.NftLimitOut{+m, +bs}:
      Equal.trans(X.NftEnv, Laws.expr_env(X.NftExprOut.of(Bool.not(m), X.NftEnv{p, X.NftState{cs, bs}, now})), X.NftEnv{p, X.NftState{cs, bs}, now}, Laws.expr_env(X.NftExprOut.of(m, X.NftEnv{p, X.NftState{cs, bs}, now})), ex.env_of(Bool.not(m), X.NftEnv{p, X.NftState{cs, bs}, now}), Equal.sym(X.NftEnv, Laws.expr_env(X.NftExprOut.of(m, X.NftEnv{p, X.NftState{cs, bs}, now})), X.NftEnv{p, X.NftState{cs, bs}, now}, ex.env_of(m, X.NftEnv{p, X.NftState{cs, bs}, now})))

def Laws.limit_over(id, rate, unit, burst, bytes, sets, env):
  match env:
    case X.NftEnv{+p, st, +now}:
      match st:
        case X.NftState{+cs, +bs}:
          +len = X.NftPacket.length(p)
          Equal.trans(Bool, Laws.expr_ok(X.NftExpr.limit_go(X.NftLimitOut.run(bs, id, X.NftLimitSpec{rate, unit, burst, bytes, True{}}, now, len), p, cs, now)), Laws.expr_ok(X.NftExpr.limit_go(ex.flipm(X.NftLimitOut.run(bs, id, X.NftLimitSpec{rate, unit, burst, bytes, False{}}, now, len)), p, cs, now)), Bool.not(Laws.expr_ok(X.NftExpr.limit_go(X.NftLimitOut.run(bs, id, X.NftLimitSpec{rate, unit, burst, bytes, False{}}, now, len), p, cs, now))), Equal.cong(X.NftLimitOut, Bool, y => Laws.expr_ok(X.NftExpr.limit_go(y, p, cs, now)), X.NftLimitOut.run(bs, id, X.NftLimitSpec{rate, unit, burst, bytes, True{}}, now, len), ex.flipm(X.NftLimitOut.run(bs, id, X.NftLimitSpec{rate, unit, burst, bytes, False{}}, now, len)), ex.run_flip(bs, id, rate, unit, burst, bytes, now, len)), ex.go_flip(X.NftLimitOut.run(bs, id, X.NftLimitSpec{rate, unit, burst, bytes, False{}}, now, len), p, cs, now))

def Laws.limit_over_env(id, rate, unit, burst, bytes, sets, env):
  match env:
    case X.NftEnv{+p, st, +now}:
      match st:
        case X.NftState{+cs, +bs}:
          +len = X.NftPacket.length(p)
          Equal.trans(X.NftEnv, Laws.expr_env(X.NftExpr.limit_go(X.NftLimitOut.run(bs, id, X.NftLimitSpec{rate, unit, burst, bytes, True{}}, now, len), p, cs, now)), Laws.expr_env(X.NftExpr.limit_go(ex.flipm(X.NftLimitOut.run(bs, id, X.NftLimitSpec{rate, unit, burst, bytes, False{}}, now, len)), p, cs, now)), Laws.expr_env(X.NftExpr.limit_go(X.NftLimitOut.run(bs, id, X.NftLimitSpec{rate, unit, burst, bytes, False{}}, now, len), p, cs, now)), Equal.cong(X.NftLimitOut, X.NftEnv, y => Laws.expr_env(X.NftExpr.limit_go(y, p, cs, now)), X.NftLimitOut.run(bs, id, X.NftLimitSpec{rate, unit, burst, bytes, True{}}, now, len), ex.flipm(X.NftLimitOut.run(bs, id, X.NftLimitSpec{rate, unit, burst, bytes, False{}}, now, len)), ex.run_flip(bs, id, rate, unit, burst, bytes, now, len)), ex.go_env(X.NftLimitOut.run(bs, id, X.NftLimitSpec{rate, unit, burst, bytes, False{}}, now, len), p, cs, now))

# Vectors: by computation

def Laws.payload_vec():
  {==}

def Laws.payload_sat():
  {==}

def Laws.cmp_vec():
  {==}

def Laws.limit_vec():
  {==}
