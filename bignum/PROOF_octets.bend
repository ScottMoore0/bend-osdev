# The proofs of LAWS_octets.bend. I2OSP is bn.fit of the limbs' little-endian
# bytes (bn.unpack), OS2IP bn.pack of the reversed bytes. The bytes of the
# valid limbs pack back to them (bo.pu: each limb x below 2^16 is
# low16(x), by bytes' le16_round_trip and low16_mask); packing ignores the
# bits above a byte (bo.pm) and appended zero bytes (bo.pz: their limbs are
# 0); bn.fit's result, padded with zeros, is its input padded with zeros
# (bo.fz), and has k bytes (bo.fl); bn.fit ignores appended zeros (bo.g),
# and the bytes of a list of limbs are those of its normal form with zeros
# appended (bo.u), so equal values (whose normal forms are equal,
# PROOF_mont.bend's by.can) give equal results. The round trip of
# PROOF.bend's octets_round_trip is repeated here (bo.rt) to keep that
# file's exhaustive laws out of this one's imports.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../u32/u32.bend as U
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ./bignum.bend as N
import ./LAWS_limbs.bend as LL
import ./PROOF_limbs.bend as PL
import ./LAWS_mod.bend as LX
import ./PROOF_mod.bend as PX
import ./LAWS_mont.bend as LT
import ./PROOF_mont.bend as PT
import ./LAWS_octets.bend as Laws

# Words, lists and Maybe

# a zero word is 0
def bo.z0(+x: U32, h: {U32.is_zero(x) == True{} : Bool}) -> {x == 0 : U32}:
  UL.u32_value_eq(x, 0, PX.bx.eqt(U32.to_nat(x), 0n, Equal.trans(Bool, Nat.is_eq(U32.to_nat(x), 0n), U32.is_zero(x), True{}, Equal.sym(Bool, U32.is_zero(x), Nat.is_eq(U32.to_nat(x), 0n), UL.u32_eq_value(x, 0)), h)))

def bo.appn(xs: List<&2, U32>) -> {B.append(xs, Nil{}) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, zz => Con{h, zz}, B.append(t, Nil{}), t, bo.appn(t))

def bo.appa(a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> {B.append(B.append(a, b), c) == B.append(a, B.append(b, c)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, zz => Con{h, zz}, B.append(B.append(t, b), c), B.append(t, B.append(b, c)), bo.appa(t, b, c))

def bo.mdisc(m: Maybe<&2, List<&2, U32>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def bo.ns(r: List<&2, U32>, h: {None{} == Some{r} : Maybe<&2, List<&2, U32>>}) -> Empty:
  %h : bo.mdisc(_)
  Unit{}

def bo.odisc(m: Maybe<&2, B.Octets>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def bo.nso(o: B.Octets, h: {None{} == Some{o} : Maybe<&2, B.Octets>}) -> Empty:
  %h : bo.odisc(_)
  Unit{}

def bo.sinj(+a: List<&2, U32>, +b: List<&2, U32>, e: {Some{a} == Some{b} : Maybe<&2, List<&2, U32>>}) -> {a == b : List<&2, U32>}:
  Equal.cong(Maybe<&2, List<&2, U32>>, List<&2, U32>, zz => Maybe.default(&2, List<&2, U32>, zz, a), Some{a}, Some{b}, e)

def bo.sinjo(+a: B.Octets, +b: B.Octets, e: {Some{a} == Some{b} : Maybe<&2, B.Octets>}) -> {a == b : B.Octets}:
  Equal.cong(Maybe<&2, B.Octets>, B.Octets, zz => Maybe.default(&2, B.Octets, zz, a), Some{a}, Some{b}, e)

# Maybe.map(t => Con{y, t}, mm) = Some{r}: mm is Some, and r is y on its
# value
def bo.mi1(mm: Maybe<&2, List<&2, U32>>, +y: U32, +r: List<&2, U32>, h: {Maybe.map(&2, List<&2, U32>, List<&2, U32>, t => Con{y, t}, mm) == Some{r} : Maybe<&2, List<&2, U32>>}) -> {mm == Some{Maybe.default(&2, List<&2, U32>, mm, Nil{})} : Maybe<&2, List<&2, U32>>}:
  match mm:
    case None{}:
      Empty.absurd({None{} == Some{Maybe.default(&2, List<&2, U32>, None{}, Nil{})} : Maybe<&2, List<&2, U32>>}, bo.ns(r, h))
    case Some{+v}:
      {==}

def bo.mi2(mm: Maybe<&2, List<&2, U32>>, +y: U32, +r: List<&2, U32>, h: {Maybe.map(&2, List<&2, U32>, List<&2, U32>, t => Con{y, t}, mm) == Some{r} : Maybe<&2, List<&2, U32>>}) -> {r == Con{y, Maybe.default(&2, List<&2, U32>, mm, Nil{})} : List<&2, U32>}:
  match mm:
    case None{}:
      Empty.absurd({r == Con{y, Maybe.default(&2, List<&2, U32>, None{}, Nil{})} : List<&2, U32>}, bo.ns(r, h))
    case Some{+v}:
      Equal.sym(List<&2, U32>, Con{y, v}, r, bo.sinj(Con{y, v}, r, h))

# the same for I2OSP's map
def bo.oi1(mm: Maybe<&2, List<&2, U32>>, +o: B.Octets, h: {Maybe.map(&2, List<&2, U32>, B.Octets, r => B.Octets.of_list(B.rev(r)), mm) == Some{o} : Maybe<&2, B.Octets>}) -> {mm == Some{Maybe.default(&2, List<&2, U32>, mm, Nil{})} : Maybe<&2, List<&2, U32>>}:
  match mm:
    case None{}:
      Empty.absurd({None{} == Some{Maybe.default(&2, List<&2, U32>, None{}, Nil{})} : Maybe<&2, List<&2, U32>>}, bo.nso(o, h))
    case Some{+v}:
      {==}

def bo.oi2(mm: Maybe<&2, List<&2, U32>>, +o: B.Octets, h: {Maybe.map(&2, List<&2, U32>, B.Octets, r => B.Octets.of_list(B.rev(r)), mm) == Some{o} : Maybe<&2, B.Octets>}) -> {o == B.Octets.of_list(B.rev(Maybe.default(&2, List<&2, U32>, mm, Nil{}))) : B.Octets}:
  match mm:
    case None{}:
      Empty.absurd({o == B.Octets.of_list(B.rev(Maybe.default(&2, List<&2, U32>, None{}, Nil{}))) : B.Octets}, bo.nso(o, h))
    case Some{+v}:
      Equal.sym(B.Octets, B.Octets.of_list(B.rev(v)), o, bo.sinjo(B.Octets.of_list(B.rev(v)), o, h))

# All-zero lists

def bo.az0(i: Nat) -> {N.bn.allz(B.zeros(i)) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+ +j:
      bo.az0(j)

def bo.aza(ys: List<&2, U32>, +i: Nat) -> {N.bn.allz(B.append(ys, B.zeros(i))) == N.bn.allz(ys) : Bool}:
  match ys:
    case Nil{}:
      bo.az0(i)
    case Con{+y, +t}:
      Equal.cong(Bool, Bool, zz => Bool.and(U32.is_zero(y), zz), N.bn.allz(B.append(t, B.zeros(i))), N.bn.allz(t), bo.aza(t, i))

def bo.azz(ys: List<&2, U32>, +h: {N.bn.allz(ys) == True{} : Bool}) -> {ys == B.zeros(B.len(ys)) : List<&2, U32>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      Equal.trans(List<&2, U32>, Con{y, t}, Con{0, t}, Con{0, B.zeros(B.len(t))}, Equal.cong(U32, List<&2, U32>, zz => Con{zz, t}, y, 0, bo.z0(y, PL.bq.and1(U32.is_zero(y), N.bn.allz(t), h))), Equal.cong(List<&2, U32>, List<&2, U32>, zz => Con{0, zz}, t, B.zeros(B.len(t)), bo.azz(t, PL.bq.and2(U32.is_zero(y), N.bn.allz(t), h))))

# bn.fit ignores appended zeros
def bo.g(k: Nat, +ys: List<&2, U32>, +i: Nat) -> {N.bn.fit(k, B.append(ys, B.zeros(i))) == N.bn.fit(k, ys) : Maybe<&2, List<&2, U32>>}:
  match k:
    case 0n:
      Equal.cong(Bool, Maybe<&2, List<&2, U32>>, zz => N.bn.fit.end(zz), N.bn.allz(B.append(ys, B.zeros(i))), N.bn.allz(ys), bo.aza(ys, i))
    case 1n+ +j:
      match ys:
        case Nil{}:
          match i:
            case 0n:
              {==}
            case 1n+ +h:
              Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, List<&2, U32>>, zz => Maybe.map(&2, List<&2, U32>, List<&2, U32>, t => Con{0, t}, zz), N.bn.fit(j, B.zeros(h)), N.bn.fit(j, Nil{}), bo.g(j, Nil{}, h))
        case Con{+y, +t}:
          Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, List<&2, U32>>, zz => Maybe.map(&2, List<&2, U32>, List<&2, U32>, u => Con{y, u}, zz), N.bn.fit(j, B.append(t, B.zeros(i))), N.bn.fit(j, t), bo.g(j, t, i))

# The bytes of limbs are those of their normal form with zeros appended

def bo.u2(+x: U32, +t: List<&2, U32>, r: List<&2, U32>, z: Bool, +er: {N.bn.norm(t) == r : List<&2, U32>}, +ez: {U32.is_zero(x) == z : Bool}, s: Sigma<&1, &1, Nat, jj => {N.bn.unpack(t) == B.append(N.bn.unpack(N.bn.norm(t)), B.zeros(jj)) : List<&2, U32>}>) -> Sigma<&1, &1, Nat, jj => {N.bn.unpack(Con{x, t}) == B.append(N.bn.unpack(N.bn.norm(Con{x, t})), B.zeros(jj)) : List<&2, U32>}>:
  match r:
    case Nil{}:
      match z:
        case True{}:
          (+j, +ej) = s
          (2n+j, Equal.trans(List<&2, U32>, B.append(B.le16(x), N.bn.unpack(t)), B.zeros(2n+j), B.append(N.bn.unpack(N.bn.cons(x, N.bn.norm(t))), B.zeros(2n+j)), Equal.trans(List<&2, U32>, B.append(B.le16(x), N.bn.unpack(t)), B.append(B.le16(0), N.bn.unpack(t)), B.zeros(2n+j), Equal.cong(U32, List<&2, U32>, zz => B.append(B.le16(zz), N.bn.unpack(t)), x, 0, bo.z0(x, ez)), Equal.trans(List<&2, U32>, B.append(B.le16(0), N.bn.unpack(t)), B.append(B.le16(0), B.append(N.bn.unpack(N.bn.norm(t)), B.zeros(j))), B.zeros(2n+j), Equal.cong(List<&2, U32>, List<&2, U32>, zz => B.append(B.le16(0), zz), N.bn.unpack(t), B.append(N.bn.unpack(N.bn.norm(t)), B.zeros(j)), ej), Equal.cong(List<&2, U32>, List<&2, U32>, zz => B.append(B.le16(0), B.append(N.bn.unpack(zz), B.zeros(j))), N.bn.norm(t), Nil{}, er))), Equal.sym(List<&2, U32>, B.append(N.bn.unpack(N.bn.cons(x, N.bn.norm(t))), B.zeros(2n+j)), B.zeros(2n+j), Equal.trans(List<&2, U32>, B.append(N.bn.unpack(N.bn.cons(x, N.bn.norm(t))), B.zeros(2n+j)), B.append(N.bn.unpack(N.bn.lone(U32.is_zero(x), x)), B.zeros(2n+j)), B.zeros(2n+j), Equal.cong(List<&2, U32>, List<&2, U32>, zz => B.append(N.bn.unpack(N.bn.cons(x, zz)), B.zeros(2n+j)), N.bn.norm(t), Nil{}, er), Equal.cong(Bool, List<&2, U32>, zz => B.append(N.bn.unpack(N.bn.lone(zz, x)), B.zeros(2n+j)), U32.is_zero(x), True{}, ez)))))
        case False{}:
          (+j, +ej) = s
          (j, Equal.trans(List<&2, U32>, B.append(B.le16(x), N.bn.unpack(t)), B.append(B.le16(x), B.zeros(j)), B.append(N.bn.unpack(N.bn.cons(x, N.bn.norm(t))), B.zeros(j)), Equal.trans(List<&2, U32>, B.append(B.le16(x), N.bn.unpack(t)), B.append(B.le16(x), B.append(N.bn.unpack(N.bn.norm(t)), B.zeros(j))), B.append(B.le16(x), B.zeros(j)), Equal.cong(List<&2, U32>, List<&2, U32>, zz => B.append(B.le16(x), zz), N.bn.unpack(t), B.append(N.bn.unpack(N.bn.norm(t)), B.zeros(j)), ej), Equal.cong(List<&2, U32>, List<&2, U32>, zz => B.append(B.le16(x), B.append(N.bn.unpack(zz), B.zeros(j))), N.bn.norm(t), Nil{}, er)), Equal.sym(List<&2, U32>, B.append(N.bn.unpack(N.bn.cons(x, N.bn.norm(t))), B.zeros(j)), B.append(B.le16(x), B.zeros(j)), Equal.trans(List<&2, U32>, B.append(N.bn.unpack(N.bn.cons(x, N.bn.norm(t))), B.zeros(j)), B.append(N.bn.unpack(N.bn.lone(U32.is_zero(x), x)), B.zeros(j)), B.append(B.le16(x), B.zeros(j)), Equal.cong(List<&2, U32>, List<&2, U32>, zz => B.append(N.bn.unpack(N.bn.cons(x, zz)), B.zeros(j)), N.bn.norm(t), Nil{}, er), Equal.trans(List<&2, U32>, B.append(N.bn.unpack(N.bn.lone(U32.is_zero(x), x)), B.zeros(j)), B.append(B.append(B.le16(x), Nil{}), B.zeros(j)), B.append(B.le16(x), B.zeros(j)), Equal.cong(Bool, List<&2, U32>, zz => B.append(N.bn.unpack(N.bn.lone(zz, x)), B.zeros(j)), U32.is_zero(x), False{}, ez), Equal.cong(List<&2, U32>, List<&2, U32>, zz => B.append(zz, B.zeros(j)), B.append(B.le16(x), Nil{}), B.le16(x), bo.appn(B.le16(x))))))))
    case Con{+r0, +r1}:
      (+j, +ej) = s
      (j, Equal.trans(List<&2, U32>, B.append(B.le16(x), N.bn.unpack(t)), B.append(B.le16(x), B.append(N.bn.unpack(Con{r0, r1}), B.zeros(j))), B.append(N.bn.unpack(N.bn.cons(x, N.bn.norm(t))), B.zeros(j)), Equal.trans(List<&2, U32>, B.append(B.le16(x), N.bn.unpack(t)), B.append(B.le16(x), B.append(N.bn.unpack(N.bn.norm(t)), B.zeros(j))), B.append(B.le16(x), B.append(N.bn.unpack(Con{r0, r1}), B.zeros(j))), Equal.cong(List<&2, U32>, List<&2, U32>, zz => B.append(B.le16(x), zz), N.bn.unpack(t), B.append(N.bn.unpack(N.bn.norm(t)), B.zeros(j)), ej), Equal.cong(List<&2, U32>, List<&2, U32>, zz => B.append(B.le16(x), B.append(N.bn.unpack(zz), B.zeros(j))), N.bn.norm(t), Con{r0, r1}, er)), Equal.sym(List<&2, U32>, B.append(N.bn.unpack(N.bn.cons(x, N.bn.norm(t))), B.zeros(j)), B.append(B.le16(x), B.append(N.bn.unpack(Con{r0, r1}), B.zeros(j))), Equal.trans(List<&2, U32>, B.append(N.bn.unpack(N.bn.cons(x, N.bn.norm(t))), B.zeros(j)), B.append(B.append(B.le16(x), N.bn.unpack(Con{r0, r1})), B.zeros(j)), B.append(B.le16(x), B.append(N.bn.unpack(Con{r0, r1}), B.zeros(j))), Equal.cong(List<&2, U32>, List<&2, U32>, zz => B.append(N.bn.unpack(N.bn.cons(x, zz)), B.zeros(j)), N.bn.norm(t), Con{r0, r1}, er), bo.appa(B.le16(x), N.bn.unpack(Con{r0, r1}), B.zeros(j))))))

def bo.u(ls: List<&2, U32>) -> Sigma<&1, &1, Nat, jj => {N.bn.unpack(ls) == B.append(N.bn.unpack(N.bn.norm(ls)), B.zeros(jj)) : List<&2, U32>}>:
  match ls:
    case Nil{}:
      (0n, {==})
    case Con{+x, +t}:
      bo.u2(x, t, N.bn.norm(t), U32.is_zero(x), {==}, {==}, bo.u(t))

# valid limbs of equal value give bn.fit equal results
def bo.d2(+l1: List<&2, U32>, +l2: List<&2, U32>, +k: Nat, +en: {N.bn.norm(l1) == N.bn.norm(l2) : List<&2, U32>}, s1: Sigma<&1, &1, Nat, jj => {N.bn.unpack(l1) == B.append(N.bn.unpack(N.bn.norm(l1)), B.zeros(jj)) : List<&2, U32>}>, s2: Sigma<&1, &1, Nat, jj => {N.bn.unpack(l2) == B.append(N.bn.unpack(N.bn.norm(l2)), B.zeros(jj)) : List<&2, U32>}>) -> {N.bn.fit(k, N.bn.unpack(l1)) == N.bn.fit(k, N.bn.unpack(l2)) : Maybe<&2, List<&2, U32>>}:
  (+j1, +e1) = s1
  (+j2, +e2) = s2
  Equal.trans(Maybe<&2, List<&2, U32>>, N.bn.fit(k, N.bn.unpack(l1)), N.bn.fit(k, N.bn.unpack(N.bn.norm(l1))), N.bn.fit(k, N.bn.unpack(l2)), Equal.trans(Maybe<&2, List<&2, U32>>, N.bn.fit(k, N.bn.unpack(l1)), N.bn.fit(k, B.append(N.bn.unpack(N.bn.norm(l1)), B.zeros(j1))), N.bn.fit(k, N.bn.unpack(N.bn.norm(l1))), Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, zz => N.bn.fit(k, zz), N.bn.unpack(l1), B.append(N.bn.unpack(N.bn.norm(l1)), B.zeros(j1)), e1), bo.g(k, N.bn.unpack(N.bn.norm(l1)), j1)), Equal.trans(Maybe<&2, List<&2, U32>>, N.bn.fit(k, N.bn.unpack(N.bn.norm(l1))), N.bn.fit(k, N.bn.unpack(N.bn.norm(l2))), N.bn.fit(k, N.bn.unpack(l2)), Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, zz => N.bn.fit(k, N.bn.unpack(zz)), N.bn.norm(l1), N.bn.norm(l2), en), Equal.sym(Maybe<&2, List<&2, U32>>, N.bn.fit(k, N.bn.unpack(l2)), N.bn.fit(k, N.bn.unpack(N.bn.norm(l2))), Equal.trans(Maybe<&2, List<&2, U32>>, N.bn.fit(k, N.bn.unpack(l2)), N.bn.fit(k, B.append(N.bn.unpack(N.bn.norm(l2)), B.zeros(j2))), N.bn.fit(k, N.bn.unpack(N.bn.norm(l2))), Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, zz => N.bn.fit(k, zz), N.bn.unpack(l2), B.append(N.bn.unpack(N.bn.norm(l2)), B.zeros(j2)), e2), bo.g(k, N.bn.unpack(N.bn.norm(l2)), j2)))))

def bo.d(+l1: List<&2, U32>, +l2: List<&2, U32>, +h1: {LL.bnlaw.ok(l1) == True{} : Bool}, +h2: {LL.bnlaw.ok(l2) == True{} : Bool}, +e: {LL.bnlaw.val(l1) == LL.bnlaw.val(l2) : Nat}, +k: Nat) -> {N.bn.fit(k, N.bn.unpack(l1)) == N.bn.fit(k, N.bn.unpack(l2)) : Maybe<&2, List<&2, U32>>}:
  bo.d2(l1, l2, k, PT.by.can(l1, l2, h1, h2, e), bo.u(l1), bo.u(l2))

# bn.fit's result has k bytes

def bo.fl0(z: Bool, +r: List<&2, U32>, h: {N.bn.fit.end(z) == Some{r} : Maybe<&2, List<&2, U32>>}) -> {B.len(r) == 0n : Nat}:
  match z:
    case True{}:
      Equal.cong(List<&2, U32>, Nat, zz => B.len(zz), r, Nil{}, Equal.sym(List<&2, U32>, Nil{}, r, bo.sinj(Nil{}, r, h)))
    case False{}:
      Empty.absurd({B.len(r) == 0n : Nat}, bo.ns(r, h))

def bo.fl(k: Nat, +ys: List<&2, U32>, +r: List<&2, U32>, +h: {N.bn.fit(k, ys) == Some{r} : Maybe<&2, List<&2, U32>>}) -> {B.len(r) == k : Nat}:
  match k:
    case 0n:
      bo.fl0(N.bn.allz(ys), r, h)
    case 1n+ +j:
      match ys:
        case Nil{}:
          Equal.trans(Nat, B.len(r), B.len(Con{0, Maybe.default(&2, List<&2, U32>, N.bn.fit(j, Nil{}), Nil{})}), 1n+j, Equal.cong(List<&2, U32>, Nat, zz => B.len(zz), r, Con{0, Maybe.default(&2, List<&2, U32>, N.bn.fit(j, Nil{}), Nil{})}, bo.mi2(N.bn.fit(j, Nil{}), 0, r, h)), Equal.cong(Nat, Nat, zz => 1n+zz, B.len(Maybe.default(&2, List<&2, U32>, N.bn.fit(j, Nil{}), Nil{})), j, bo.fl(j, Nil{}, Maybe.default(&2, List<&2, U32>, N.bn.fit(j, Nil{}), Nil{}), bo.mi1(N.bn.fit(j, Nil{}), 0, r, h))))
        case Con{+y, +t}:
          Equal.trans(Nat, B.len(r), B.len(Con{y, Maybe.default(&2, List<&2, U32>, N.bn.fit(j, t), Nil{})}), 1n+j, Equal.cong(List<&2, U32>, Nat, zz => B.len(zz), r, Con{y, Maybe.default(&2, List<&2, U32>, N.bn.fit(j, t), Nil{})}, bo.mi2(N.bn.fit(j, t), y, r, h)), Equal.cong(Nat, Nat, zz => 1n+zz, B.len(Maybe.default(&2, List<&2, U32>, N.bn.fit(j, t), Nil{})), j, bo.fl(j, t, Maybe.default(&2, List<&2, U32>, N.bn.fit(j, t), Nil{}), bo.mi1(N.bn.fit(j, t), y, r, h))))

# bn.fit's result padded with zeros is its input padded with zeros

def bo.fz0(z: Bool, +ys: List<&2, U32>, +r: List<&2, U32>, +ez: {N.bn.allz(ys) == z : Bool}, h: {N.bn.fit.end(z) == Some{r} : Maybe<&2, List<&2, U32>>}) -> Sigma<&1, &1, Nat, ii => Sigma<&1, &1, Nat, jj => {B.append(r, B.zeros(ii)) == B.append(ys, B.zeros(jj)) : List<&2, U32>}>>:
  match z:
    case True{}:
      (B.len(ys), (0n, Equal.trans(List<&2, U32>, B.append(r, B.zeros(B.len(ys))), B.zeros(B.len(ys)), B.append(ys, Nil{}), Equal.cong(List<&2, U32>, List<&2, U32>, zz => B.append(zz, B.zeros(B.len(ys))), r, Nil{}, Equal.sym(List<&2, U32>, Nil{}, r, bo.sinj(Nil{}, r, h))), Equal.trans(List<&2, U32>, B.zeros(B.len(ys)), ys, B.append(ys, Nil{}), Equal.sym(List<&2, U32>, ys, B.zeros(B.len(ys)), bo.azz(ys, ez)), Equal.sym(List<&2, U32>, B.append(ys, Nil{}), ys, bo.appn(ys))))))
    case False{}:
      Empty.absurd(Sigma<&1, &1, Nat, ii => Sigma<&1, &1, Nat, jj => {B.append(r, B.zeros(ii)) == B.append(ys, B.zeros(jj)) : List<&2, U32>}>>, bo.ns(r, h))

def bo.fz1(+r: List<&2, U32>, +R1: List<&2, U32>, +e2: {r == Con{0, R1} : List<&2, U32>}, s: Sigma<&1, &1, Nat, ii => Sigma<&1, &1, Nat, jj => {B.append(R1, B.zeros(ii)) == B.append(Nil{}, B.zeros(jj)) : List<&2, U32>}>>) -> Sigma<&1, &1, Nat, ii => Sigma<&1, &1, Nat, jj => {B.append(r, B.zeros(ii)) == B.append(Nil{}, B.zeros(jj)) : List<&2, U32>}>>:
  (+i, s2) = s
  (+j, +e) = s2
  (i, (1n+j, Equal.trans(List<&2, U32>, B.append(r, B.zeros(i)), B.append(Con{0, R1}, B.zeros(i)), B.zeros(1n+j), Equal.cong(List<&2, U32>, List<&2, U32>, zz => B.append(zz, B.zeros(i)), r, Con{0, R1}, e2), Equal.cong(List<&2, U32>, List<&2, U32>, zz => Con{0, zz}, B.append(R1, B.zeros(i)), B.zeros(j), e))))

def bo.fz2(+y: U32, +t: List<&2, U32>, +r: List<&2, U32>, +R1: List<&2, U32>, +e2: {r == Con{y, R1} : List<&2, U32>}, s: Sigma<&1, &1, Nat, ii => Sigma<&1, &1, Nat, jj => {B.append(R1, B.zeros(ii)) == B.append(t, B.zeros(jj)) : List<&2, U32>}>>) -> Sigma<&1, &1, Nat, ii => Sigma<&1, &1, Nat, jj => {B.append(r, B.zeros(ii)) == B.append(Con{y, t}, B.zeros(jj)) : List<&2, U32>}>>:
  (+i, s2) = s
  (+j, +e) = s2
  (i, (j, Equal.trans(List<&2, U32>, B.append(r, B.zeros(i)), B.append(Con{y, R1}, B.zeros(i)), B.append(Con{y, t}, B.zeros(j)), Equal.cong(List<&2, U32>, List<&2, U32>, zz => B.append(zz, B.zeros(i)), r, Con{y, R1}, e2), Equal.cong(List<&2, U32>, List<&2, U32>, zz => Con{y, zz}, B.append(R1, B.zeros(i)), B.append(t, B.zeros(j)), e))))

def bo.fz(k: Nat, +ys: List<&2, U32>, +r: List<&2, U32>, +h: {N.bn.fit(k, ys) == Some{r} : Maybe<&2, List<&2, U32>>}) -> Sigma<&1, &1, Nat, ii => Sigma<&1, &1, Nat, jj => {B.append(r, B.zeros(ii)) == B.append(ys, B.zeros(jj)) : List<&2, U32>}>>:
  match k:
    case 0n:
      bo.fz0(N.bn.allz(ys), ys, r, {==}, h)
    case 1n+ +j:
      match ys:
        case Nil{}:
          bo.fz1(r, Maybe.default(&2, List<&2, U32>, N.bn.fit(j, Nil{}), Nil{}), bo.mi2(N.bn.fit(j, Nil{}), 0, r, h), bo.fz(j, Nil{}, Maybe.default(&2, List<&2, U32>, N.bn.fit(j, Nil{}), Nil{}), bo.mi1(N.bn.fit(j, Nil{}), 0, r, h)))
        case Con{+y, +t}:
          bo.fz2(y, t, r, Maybe.default(&2, List<&2, U32>, N.bn.fit(j, t), Nil{}), bo.mi2(N.bn.fit(j, t), y, r, h), bo.fz(j, t, Maybe.default(&2, List<&2, U32>, N.bn.fit(j, t), Nil{}), bo.mi1(N.bn.fit(j, t), y, r, h)))

# Packing: the bits above a byte, and appended zero bytes, change nothing;
# the bytes of valid limbs pack back to them; packed limbs are valid

def bo.c1(a: U32, b: U32) -> {B.le16.head([B.byte(a), B.byte(b)]) == B.le16.head([a, b]) : Maybe<&2, U32>}:
  match a b:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, bh}}}}}}}}}:
      {==}

def bo.c1b(a: U32) -> {B.le16.head([B.byte(a), 0]) == B.le16.head([a, 0]) : Maybe<&2, U32>}:
  match a:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}}:
      {==}

def bo.pm(xs: List<&2, U32>) -> {N.bn.pack(B.mask(xs)) == N.bn.pack(xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+a, Nil{}}:
      Equal.cong(Maybe<&2, U32>, List<&2, U32>, zz => Con{Maybe.default(&2, U32, zz, 0), Nil{}}, B.le16.head([B.byte(a), 0]), B.le16.head([a, 0]), bo.c1b(a))
    case Con{+a, Con{+b, +t}}:
      Equal.trans(List<&2, U32>, Con{Maybe.default(&2, U32, B.le16.head([B.byte(a), B.byte(b)]), 0), N.bn.pack(B.mask(t))}, Con{Maybe.default(&2, U32, B.le16.head([a, b]), 0), N.bn.pack(B.mask(t))}, Con{Maybe.default(&2, U32, B.le16.head([a, b]), 0), N.bn.pack(t)}, Equal.cong(Maybe<&2, U32>, List<&2, U32>, zz => Con{Maybe.default(&2, U32, zz, 0), N.bn.pack(B.mask(t))}, B.le16.head([B.byte(a), B.byte(b)]), B.le16.head([a, b]), bo.c1(a, b)), Equal.cong(List<&2, U32>, List<&2, U32>, zz => Con{Maybe.default(&2, U32, B.le16.head([a, b]), 0), zz}, N.bn.pack(B.mask(t)), N.bn.pack(t), bo.pm(t)))

def bo.pz0(i: Nat) -> {LL.bnlaw.val(N.bn.pack(B.zeros(i))) == 0n : Nat}:
  match i:
    case 0n:
      {==}
    case 1n+ +a:
      match a:
        case 0n:
          {==}
        case 1n+ +b:
          Equal.trans(Nat, LL.bnlaw.val(N.bn.pack(B.zeros(2n+b))), Nat.add(U32.to_nat(Maybe.default(&2, U32, B.le16.head([0, 0]), 0)), U.U32Nat.dbl(16n, 0n)), 0n, Equal.cong(Nat, Nat, zz => Nat.add(U32.to_nat(Maybe.default(&2, U32, B.le16.head([0, 0]), 0)), U.U32Nat.dbl(16n, zz)), LL.bnlaw.val(N.bn.pack(B.zeros(b))), 0n, bo.pz0(b)), {==})

def bo.pz(zs: List<&2, U32>, +i: Nat) -> {LL.bnlaw.val(N.bn.pack(B.append(zs, B.zeros(i)))) == LL.bnlaw.val(N.bn.pack(zs)) : Nat}:
  match zs:
    case Nil{}:
      bo.pz0(i)
    case Con{+a, Nil{}}:
      match i:
        case 0n:
          {==}
        case 1n+ +b:
          Equal.cong(Nat, Nat, zz => Nat.add(U32.to_nat(Maybe.default(&2, U32, B.le16.head([a, 0]), 0)), U.U32Nat.dbl(16n, zz)), LL.bnlaw.val(N.bn.pack(B.zeros(b))), 0n, bo.pz0(b))
    case Con{+a, Con{+b, +t}}:
      Equal.cong(Nat, Nat, zz => Nat.add(U32.to_nat(Maybe.default(&2, U32, B.le16.head([a, b]), 0)), U.U32Nat.dbl(16n, zz)), LL.bnlaw.val(N.bn.pack(B.append(t, B.zeros(i)))), LL.bnlaw.val(N.bn.pack(t)), bo.pz(t, i))

# a limb below 2^16 is its own low16
def bo.l16(+x: U32, +hlt: {Nat.is_lt(U32.to_nat(x), U.U32Nat.dbl(16n, 1n)) == True{} : Bool}) -> {B.low16(x) == x : U32}:
  +e1 = UL.u32_value_eq(U32.and(x, 65535), x, Equal.trans(Nat, U32.to_nat(U32.and(x, 65535)), U.U32Nat.low(16n, U32.to_nat(x)), U32.to_nat(x), UL.u32_and_65535(x), UL.low_small(16n, U32.to_nat(x), hlt)))
  Equal.trans(U32, B.low16(x), B.low16(U32.and(x, 65535)), x, Equal.cong(U32, U32, zz => B.low16(zz), x, U32.and(x, 65535), Equal.sym(U32, U32.and(x, 65535), x, e1)), Equal.trans(U32, B.low16(U32.and(x, 65535)), U32.and(x, 65535), x, BL.low16_mask(x), e1))

def bo.pu(ls: List<&2, U32>, +h: {LL.bnlaw.ok(ls) == True{} : Bool}) -> {N.bn.pack(N.bn.unpack(ls)) == ls : List<&2, U32>}:
  match ls:
    case Nil{}:
      {==}
    case Con{x, +t}:
      match x:
        case U32{+w}:
          Equal.trans(List<&2, U32>, Con{Maybe.default(&2, U32, B.le16_at(B.le16(U32{w}), 0n), 0), N.bn.pack(N.bn.unpack(t))}, Con{B.low16(U32{w}), N.bn.pack(N.bn.unpack(t))}, Con{U32{w}, t}, Equal.cong(Maybe<&2, U32>, List<&2, U32>, zz => Con{Maybe.default(&2, U32, zz, 0), N.bn.pack(N.bn.unpack(t))}, B.le16_at(B.le16(U32{w}), 0n), Some{B.low16(U32{w})}, BL.le16_round_trip(U32{w})), Equal.trans(List<&2, U32>, Con{B.low16(U32{w}), N.bn.pack(N.bn.unpack(t))}, Con{U32{w}, N.bn.pack(N.bn.unpack(t))}, Con{U32{w}, t}, Equal.cong(U32, List<&2, U32>, zz => Con{zz, N.bn.pack(N.bn.unpack(t))}, B.low16(U32{w}), U32{w}, bo.l16(N.bn.hd(Con{U32{w}, t}), PX.bx.hdlt(Con{U32{w}, t}, h))), Equal.cong(List<&2, U32>, List<&2, U32>, zz => Con{U32{w}, zz}, N.bn.pack(N.bn.unpack(t)), t, bo.pu(t, PL.bq.and2(U32.is_zero(U32.shrn(U32{w}, 16n)), LL.bnlaw.ok(t), h)))))

def bo.c4(a: U32, b: U32) -> {U32.is_zero(U32.shrn(Maybe.default(&2, U32, B.le16.head([a, b]), 0), 16n)) == True{} : Bool}:
  match a b:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, bh}}}}}}}}}:
      {==}

def bo.c4b(a: U32) -> {U32.is_zero(U32.shrn(Maybe.default(&2, U32, B.le16.head([a, 0]), 0), 16n)) == True{} : Bool}:
  match a:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}}:
      {==}

def bo.pk(xs: List<&2, U32>) -> {LL.bnlaw.ok(N.bn.pack(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+a, Nil{}}:
      Equal.cong(Bool, Bool, zz => Bool.and(zz, True{}), U32.is_zero(U32.shrn(Maybe.default(&2, U32, B.le16.head([a, 0]), 0), 16n)), True{}, bo.c4b(a))
    case Con{+a, Con{+b, +t}}:
      Equal.trans(Bool, Bool.and(U32.is_zero(U32.shrn(Maybe.default(&2, U32, B.le16.head([a, b]), 0), 16n)), LL.bnlaw.ok(N.bn.pack(t))), LL.bnlaw.ok(N.bn.pack(t)), True{}, Equal.cong(Bool, Bool, zz => Bool.and(zz, LL.bnlaw.ok(N.bn.pack(t))), U32.is_zero(U32.shrn(Maybe.default(&2, U32, B.le16.head([a, b]), 0), 16n)), True{}, bo.c4(a, b)), bo.pk(t))

# OS2IP then I2OSP to the bytes' own length (bignum's octets_round_trip,
# PROOF.bend)

def bo.lp2(v: U32, w: U32) -> {B.le16(Maybe.default(&2, U32, B.le16.head([B.byte(v), B.byte(w)]), 0)) == [B.byte(v), B.byte(w)] : List<&2, U32>}:
  match v w:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, bh}}}}}}}}}:
      {==}

def bo.lp1(v: U32) -> {B.le16(Maybe.default(&2, U32, B.le16.head([B.byte(v), 0]), 0)) == [B.byte(v), 0] : List<&2, U32>}:
  match v:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, ah}}}}}}}}}:
      {==}

def bo.fit2(+a: U32, +b: U32, n: Nat, ys: List<&2, U32>, r: List<&2, U32>, h: {N.bn.fit(n, ys) == Some{r} : Maybe<&2, List<&2, U32>>}) -> {N.bn.fit(2n+n, Con{a, Con{b, ys}}) == Some{Con{a, Con{b, r}}} : Maybe<&2, List<&2, U32>>}:
  %Equal.sym(Maybe<&2, List<&2, U32>>, N.bn.fit(n, ys), Some{r}, h) : {Maybe.map(&2, List<&2, U32>, List<&2, U32>, t => Con{a, t}, Maybe.map(&2, List<&2, U32>, List<&2, U32>, t => Con{b, t}, _)) == Some{Con{a, Con{b, r}}} : Maybe<&2, List<&2, U32>>}
  {==}

def bo.fitp(+s: List<&2, U32>) -> {N.bn.fit(B.len(B.mask(s)), N.bn.unpack(N.bn.pack(B.mask(s)))) == Some{B.mask(s)} : Maybe<&2, List<&2, U32>>}:
  match s:
    case Nil{}:
      {==}
    case Con{+v, Nil{}}:
      %Equal.sym(List<&2, U32>, B.le16(Maybe.default(&2, U32, B.le16.head([B.byte(v), 0]), 0)), [B.byte(v), 0], bo.lp1(v)) : {N.bn.fit(1n, B.append(_, Nil{})) == Some{[B.byte(v)]} : Maybe<&2, List<&2, U32>>}
      {==}
    case Con{+v, Con{+w, t}}:
      %Equal.sym(List<&2, U32>, B.le16(Maybe.default(&2, U32, B.le16.head([B.byte(v), B.byte(w)]), 0)), [B.byte(v), B.byte(w)], bo.lp2(v, w)) : {N.bn.fit(2n+B.len(B.mask(t)), B.append(_, N.bn.unpack(N.bn.pack(B.mask(t))))) == Some{Con{B.byte(v), Con{B.byte(w), B.mask(t)}}} : Maybe<&2, List<&2, U32>>}
      bo.fit2(B.byte(v), B.byte(w), B.len(B.mask(t)), N.bn.unpack(N.bn.pack(B.mask(t))), B.mask(t), bo.fitp(t))

def bo.rmg(+xs: List<&2, U32>, +acc: List<&2, U32>) -> {B.rev_onto(B.mask(xs), B.mask(acc)) == B.mask(B.rev_onto(xs, acc)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      bo.rmg(t, Con{h, acc})

def bo.rlg(+xs: List<&2, U32>, +acc: List<&2, U32>) -> {B.len(B.rev_onto(xs, acc)) == Nat.add(B.len(xs), B.len(acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(Nat, B.len(B.rev_onto(t, Con{h, acc})), Nat.add(B.len(t), B.len(Con{h, acc})), bo.rlg(t, Con{h, acc})) : {_ == 1n+Nat.add(B.len(t), B.len(acc)) : Nat}
      UL.nat_add_succ(B.len(t), B.len(acc))

def bo.rl(+xs: List<&2, U32>) -> {B.len(B.rev(xs)) == B.len(xs) : Nat}:
  %Equal.sym(Nat, B.len(B.rev_onto(xs, Nil{})), Nat.add(B.len(xs), B.len(Nil{})), bo.rlg(xs, Nil{})) : {_ == B.len(xs) : Nat}
  UL.nat_add_zero(B.len(xs))

def bo.tlm(+o: B.Octets) -> {B.Octets.to_list(o) == B.mask(B.Octets.to_list(o)) : List<&2, U32>}:
  %BL.octets_to_of(B.Octets.to_list(o)) : {B.Octets.to_list(o) == _ : List<&2, U32>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)) : {B.Octets.to_list(o) == B.Octets.to_list(_) : List<&2, U32>}
  {==}

def bo.rbm(+o: B.Octets) -> {B.mask(B.rev(B.Octets.to_list(o))) == B.rev(B.Octets.to_list(o)) : List<&2, U32>}:
  %bo.rmg(B.Octets.to_list(o), Nil{}) : {_ == B.rev(B.Octets.to_list(o)) : List<&2, U32>}
  %bo.tlm(o) : {B.rev(_) == B.rev(B.Octets.to_list(o)) : List<&2, U32>}
  {==}

def bo.ofit(+o: B.Octets) -> {N.bn.fit(B.Octets.len(o), N.bn.unpack(N.bn.pack(B.rev(B.Octets.to_list(o))))) == Some{B.rev(B.Octets.to_list(o))} : Maybe<&2, List<&2, U32>>}:
  %Equal.sym(Nat, B.Octets.len(o), B.len(B.Octets.to_list(o)), BL.octets_len_list(o)) : {N.bn.fit(_, N.bn.unpack(N.bn.pack(B.rev(B.Octets.to_list(o))))) == Some{B.rev(B.Octets.to_list(o))} : Maybe<&2, List<&2, U32>>}
  %bo.rl(B.Octets.to_list(o)) : {N.bn.fit(_, N.bn.unpack(N.bn.pack(B.rev(B.Octets.to_list(o))))) == Some{B.rev(B.Octets.to_list(o))} : Maybe<&2, List<&2, U32>>}
  %bo.rbm(o) : {N.bn.fit(B.len(_), N.bn.unpack(N.bn.pack(_))) == Some{_} : Maybe<&2, List<&2, U32>>}
  bo.fitp(B.rev(B.Octets.to_list(o)))

def bo.rt(+o: B.Octets) -> {N.BnNat.to_octets(N.BnNat.of_octets(o), B.Octets.len(o)) == Some{o} : Maybe<&2, B.Octets>}:
  %Equal.sym(Maybe<&2, List<&2, U32>>, N.bn.fit(B.Octets.len(o), N.bn.unpack(N.bn.pack(B.rev(B.Octets.to_list(o))))), Some{B.rev(B.Octets.to_list(o))}, bo.ofit(o)) : {Maybe.map(&2, List<&2, U32>, B.Octets, r => B.Octets.of_list(B.rev(r)), _) == Some{o} : Maybe<&2, B.Octets>}
  %Equal.sym(List<&2, U32>, B.rev(B.rev(B.Octets.to_list(o))), B.Octets.to_list(o), BL.rev_rev(B.Octets.to_list(o))) : {Some{B.Octets.of_list(_)} == Some{o} : Maybe<&2, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)) : {Some{_} == Some{o} : Maybe<&2, B.Octets>}
  {==}

# OS2IP of I2OSP's result, from bn.fit's result R0 with zeros
def bo.tv(+ls: List<&2, U32>, +o: B.Octets, +R0: List<&2, U32>, +hok: {LL.bnlaw.ok(ls) == True{} : Bool}, +e2: {o == B.Octets.of_list(B.rev(R0)) : B.Octets}, s: Sigma<&1, &1, Nat, ii => Sigma<&1, &1, Nat, jj => {B.append(R0, B.zeros(ii)) == B.append(N.bn.unpack(ls), B.zeros(jj)) : List<&2, U32>}>>) -> {LL.bnlaw.val(N.bn.pack(B.rev(B.Octets.to_list(o)))) == LL.bnlaw.val(ls) : Nat}:
  (+i, s2) = s
  (+j, +e) = s2
  +a1 = Equal.cong(B.Octets, Nat, zz => LL.bnlaw.val(N.bn.pack(B.rev(B.Octets.to_list(zz)))), o, B.Octets.of_list(B.rev(R0)), e2)
  +a2 = Equal.cong(List<&2, U32>, Nat, zz => LL.bnlaw.val(N.bn.pack(B.rev(zz))), B.Octets.to_list(B.Octets.of_list(B.rev(R0))), B.mask(B.rev(R0)), BL.octets_to_of(B.rev(R0)))
  +a3 = Equal.cong(List<&2, U32>, Nat, zz => LL.bnlaw.val(N.bn.pack(zz)), B.rev(B.mask(B.rev(R0))), B.mask(B.rev(B.rev(R0))), bo.rmg(B.rev(R0), Nil{}))
  +a4 = Equal.cong(List<&2, U32>, Nat, zz => LL.bnlaw.val(N.bn.pack(B.mask(zz))), B.rev(B.rev(R0)), R0, BL.rev_rev(R0))
  +a5 = Equal.cong(List<&2, U32>, Nat, zz => LL.bnlaw.val(zz), N.bn.pack(B.mask(R0)), N.bn.pack(R0), bo.pm(R0))
  +a6 = Equal.sym(Nat, LL.bnlaw.val(N.bn.pack(B.append(R0, B.zeros(i)))), LL.bnlaw.val(N.bn.pack(R0)), bo.pz(R0, i))
  +a7 = Equal.cong(List<&2, U32>, Nat, zz => LL.bnlaw.val(N.bn.pack(zz)), B.append(R0, B.zeros(i)), B.append(N.bn.unpack(ls), B.zeros(j)), e)
  +a8 = bo.pz(N.bn.unpack(ls), j)
  +a9 = Equal.cong(List<&2, U32>, Nat, zz => LL.bnlaw.val(zz), N.bn.pack(N.bn.unpack(ls)), ls, bo.pu(ls, hok))
  Equal.trans(Nat, LL.bnlaw.val(N.bn.pack(B.rev(B.Octets.to_list(o)))), LL.bnlaw.val(N.bn.pack(B.rev(B.Octets.to_list(B.Octets.of_list(B.rev(R0)))))), LL.bnlaw.val(ls), a1, Equal.trans(Nat, LL.bnlaw.val(N.bn.pack(B.rev(B.Octets.to_list(B.Octets.of_list(B.rev(R0)))))), LL.bnlaw.val(N.bn.pack(B.rev(B.mask(B.rev(R0))))), LL.bnlaw.val(ls), a2, Equal.trans(Nat, LL.bnlaw.val(N.bn.pack(B.rev(B.mask(B.rev(R0))))), LL.bnlaw.val(N.bn.pack(B.mask(B.rev(B.rev(R0))))), LL.bnlaw.val(ls), a3, Equal.trans(Nat, LL.bnlaw.val(N.bn.pack(B.mask(B.rev(B.rev(R0))))), LL.bnlaw.val(N.bn.pack(B.mask(R0))), LL.bnlaw.val(ls), a4, Equal.trans(Nat, LL.bnlaw.val(N.bn.pack(B.mask(R0))), LL.bnlaw.val(N.bn.pack(R0)), LL.bnlaw.val(ls), a5, Equal.trans(Nat, LL.bnlaw.val(N.bn.pack(R0)), LL.bnlaw.val(N.bn.pack(B.append(R0, B.zeros(i)))), LL.bnlaw.val(ls), a6, Equal.trans(Nat, LL.bnlaw.val(N.bn.pack(B.append(R0, B.zeros(i)))), LL.bnlaw.val(N.bn.pack(B.append(N.bn.unpack(ls), B.zeros(j)))), LL.bnlaw.val(ls), a7, Equal.trans(Nat, LL.bnlaw.val(N.bn.pack(B.append(N.bn.unpack(ls), B.zeros(j)))), LL.bnlaw.val(N.bn.pack(N.bn.unpack(ls))), LL.bnlaw.val(ls), a8, a9))))))))

# The laws

def Laws.of_octets_valid(o):
  bo.pk(B.rev(B.Octets.to_list(o)))

def Laws.to_octets_len(x, k, o, h):
  match x:
    case N.BnNat{+ls}:
      Equal.trans(Nat, B.Octets.len(o), B.Octets.len(B.Octets.of_list(B.rev(Maybe.default(&2, List<&2, U32>, N.bn.fit(k, N.bn.unpack(ls)), Nil{})))), k, Equal.cong(B.Octets, Nat, zz => B.Octets.len(zz), o, B.Octets.of_list(B.rev(Maybe.default(&2, List<&2, U32>, N.bn.fit(k, N.bn.unpack(ls)), Nil{}))), bo.oi2(N.bn.fit(k, N.bn.unpack(ls)), o, h)), Equal.trans(Nat, B.Octets.len(B.Octets.of_list(B.rev(Maybe.default(&2, List<&2, U32>, N.bn.fit(k, N.bn.unpack(ls)), Nil{})))), B.len(B.rev(Maybe.default(&2, List<&2, U32>, N.bn.fit(k, N.bn.unpack(ls)), Nil{}))), k, BL.octets_len_of_list(B.rev(Maybe.default(&2, List<&2, U32>, N.bn.fit(k, N.bn.unpack(ls)), Nil{}))), Equal.trans(Nat, B.len(B.rev(Maybe.default(&2, List<&2, U32>, N.bn.fit(k, N.bn.unpack(ls)), Nil{}))), B.len(Maybe.default(&2, List<&2, U32>, N.bn.fit(k, N.bn.unpack(ls)), Nil{})), k, bo.rl(Maybe.default(&2, List<&2, U32>, N.bn.fit(k, N.bn.unpack(ls)), Nil{})), bo.fl(k, N.bn.unpack(ls), Maybe.default(&2, List<&2, U32>, N.bn.fit(k, N.bn.unpack(ls)), Nil{}), bo.oi1(N.bn.fit(k, N.bn.unpack(ls)), o, h)))))

def Laws.to_octets_value(x, k, o, hx, h):
  match x:
    case N.BnNat{+ls}:
      bo.tv(ls, o, Maybe.default(&2, List<&2, U32>, N.bn.fit(k, N.bn.unpack(ls)), Nil{}), hx, bo.oi2(N.bn.fit(k, N.bn.unpack(ls)), o, h), bo.fz(k, N.bn.unpack(ls), Maybe.default(&2, List<&2, U32>, N.bn.fit(k, N.bn.unpack(ls)), Nil{}), bo.oi1(N.bn.fit(k, N.bn.unpack(ls)), o, h)))

def Laws.to_octets_eq(x, y, k, hx, hy, e):
  match x y:
    case N.BnNat{+l1} N.BnNat{+l2}:
      Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, B.Octets>, zz => Maybe.map(&2, List<&2, U32>, B.Octets, r => B.Octets.of_list(B.rev(r)), zz), N.bn.fit(k, N.bn.unpack(l1)), N.bn.fit(k, N.bn.unpack(l2)), bo.d(l1, l2, hx, hy, e, k))

def Laws.to_octets_of_value(x, o, hx, e):
  Equal.trans(Maybe<&2, B.Octets>, N.BnNat.to_octets(x, B.Octets.len(o)), N.BnNat.to_octets(N.BnNat.of_octets(o), B.Octets.len(o)), Some{o}, Laws.to_octets_eq(x, N.BnNat.of_octets(o), B.Octets.len(o), hx, Laws.of_octets_valid(o), Equal.sym(Nat, LL.bnlaw.value(N.BnNat.of_octets(o)), LL.bnlaw.value(x), e)), bo.rt(o))
