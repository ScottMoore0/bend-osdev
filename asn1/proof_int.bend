# Proof helpers for bend-osdev-asn1: INTEGER contents read back as the
# integer written. A non-negative integer is written as its big-endian
# digits (number.bend's a1.be) with a 00 in front when the top bit is set;
# a negative one -m as the complement of m - 1's digits with an FF in front
# when the top bit is clear. The digits of a number have no leading zero
# (pi.canon_top), so the contents pass the fewest-octets check, and reading
# them back is Horner's rule (proof_num.bend). Octets are related to their
# values through bend-osdev-u32's value laws (u32_le_value and the like)
# and proof_byte.bend's ab.byte.
import Base
import ../bytes/bytes.bend as B
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./number.bend as Nu
import ./prim.bend as P
import ./proof_nat.bend as AN
import ./proof_list.bend as AL
import ./proof_num.bend as PN
import ./proof_byte.bend as AB

# Tags

# every tag compares equal to itself
def pi.tag_refl(t: T.Asn1Tag) -> {T.Asn1Tag.is_eq(t, t) == True{} : Bool}:
  match t:
    case T.Asn1Tag{+c, +n}:
      AN.an.and_i(T.Asn1Class.is_eq(c, c), Nat.is_eq(n, n), AN.an.eq_refl(T.Asn1Class.rank(c)), AN.an.eq_refl(n))

# a primitive element read with its own tag gives its contents
def pi.prim_as(+t: T.Asn1Tag, +o: B.Octets) -> {P.Asn1.prim_as(t, N.Asn1Prim{t, o}) == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}:
  %Equal.sym(Bool, T.Asn1Tag.is_eq(t, t), True{}, pi.tag_refl(t)) : {P.a1.prim_as.pick(_, o) == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}
  {==}

# Arithmetic

def pi.ne0(+d: Nat, +h: {Nat.is_le(1n, d) == True{} : Bool}) -> {Nat.is_eq(d, 0n) == False{} : Bool}:
  match d:
    case 0n:
      Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, AN.an.ft(h))
    case 1n+p:
      {==}

# not a < b: b <= a
def pi.le_of_nlt(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case _ 0n:
      AN.an.le_zero(a)
    case 0n 1n+bp:
      Empty.absurd({Nat.is_le(1n+bp, 0n) == True{} : Bool}, AN.an.tf(h))
    case 1n+ap 1n+bp:
      pi.le_of_nlt(ap, bp, h)

def pi.sub_le(+a: Nat, +d: Nat) -> {Nat.is_le(Nat.sub(a, d), a) == True{} : Bool}:
  match a d:
    case 0n _:
      {==}
    case 1n+ap 0n:
      AN.an.le_refl(1n+ap)
    case 1n+ap 1n+dp:
      AN.an.le_trans(Nat.sub(ap, dp), ap, 1n+ap, pi.sub_le(ap, dp), AN.an.le_succ(ap))

# d <= a: (1 + a) - d = 1 + (a - d)
def pi.sub_succ(+a: Nat, +d: Nat, +h: {Nat.is_le(d, a) == True{} : Bool}) -> {Nat.sub(1n+a, d) == 1n+Nat.sub(a, d) : Nat}:
  match a d:
    case _ 0n:
      %AN.an.sub_zero(a) : {1n+_ == 1n+Nat.sub(a, 0n) : Nat}
      {==}
    case 0n 1n+dp:
      Empty.absurd({Nat.sub(1n, 1n+dp) == 1n+Nat.sub(0n, 1n+dp) : Nat}, AN.an.ft(h))
    case 1n+ap 1n+dp:
      pi.sub_succ(ap, dp, h)

def pi.sub_self(+a: Nat) -> {Nat.sub(a, a) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pi.sub_self(p)

# d <= a: a - (a - d) = d
def pi.sub_sub(+a: Nat, +d: Nat, +h: {Nat.is_le(d, a) == True{} : Bool}) -> {Nat.sub(a, Nat.sub(a, d)) == d : Nat}:
  match a d:
    case _ 0n:
      %Equal.sym(Nat, Nat.sub(a, 0n), a, AN.an.sub_zero(a)) : {Nat.sub(a, _) == 0n : Nat}
      pi.sub_self(a)
    case 0n 1n+dp:
      Empty.absurd({Nat.sub(0n, Nat.sub(0n, 1n+dp)) == 1n+dp : Nat}, AN.an.ft(h))
    case 1n+ap 1n+dp:
      %Equal.sym(Nat, Nat.sub(1n+ap, Nat.sub(ap, dp)), 1n+Nat.sub(ap, Nat.sub(ap, dp)), pi.sub_succ(ap, Nat.sub(ap, dp), pi.sub_le(ap, dp))) : {_ == 1n+dp : Nat}
      %pi.sub_sub(ap, dp, h) : {1n+Nat.sub(ap, Nat.sub(ap, dp)) == 1n+_ : Nat}
      {==}

# 1 <= d <= a: a - d < a
def pi.sub_lt(+a: Nat, +d: Nat, +h1: {Nat.is_le(1n, d) == True{} : Bool}, +h2: {Nat.is_le(d, a) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(a, d), a) == True{} : Bool}:
  match a d:
    case _ 0n:
      Empty.absurd({Nat.is_lt(Nat.sub(a, 0n), a) == True{} : Bool}, AN.an.ft(h1))
    case 0n 1n+dp:
      Empty.absurd({Nat.is_lt(Nat.sub(0n, 1n+dp), 0n) == True{} : Bool}, AN.an.ft(h2))
    case 1n+ap 1n+dp:
      AN.an.le_lt_succ(Nat.sub(ap, dp), ap, pi.sub_le(ap, dp))

# Octets and their values

def pi.lt256_le(+d: Nat, +hd: {Nat.is_lt(d, 256n) == True{} : Bool}) -> {Nat.is_le(d, 255n) == True{} : Bool}:
  AN.an.lt_succ_le(d, 255n, hd)

def pi.le128(+d: Nat, +hd: {Nat.is_lt(d, 256n) == True{} : Bool}) -> {U32.is_le(128, Nu.a1.b(d)) == Nat.is_le(128n, d) : Bool}:
  %AB.ab.byte(d, hd) : {U32.is_le(128, Nu.a1.b(d)) == Nat.is_le(128n, _) : Bool}
  UL.u32_le_value(128, Nu.a1.b(d))

def pi.lt128(+d: Nat, +hd: {Nat.is_lt(d, 256n) == True{} : Bool}) -> {U32.is_lt(Nu.a1.b(d), 128) == Nat.is_lt(d, 128n) : Bool}:
  %AB.ab.byte(d, hd) : {U32.is_lt(Nu.a1.b(d), 128) == Nat.is_lt(_, 128n) : Bool}
  UL.u32_lt_value(Nu.a1.b(d), 128)

def pi.eq0(+d: Nat, +hd: {Nat.is_lt(d, 256n) == True{} : Bool}) -> {U32.is_eq(Nu.a1.b(d), 0) == Nat.is_eq(d, 0n) : Bool}:
  %AB.ab.byte(d, hd) : {U32.is_eq(Nu.a1.b(d), 0) == Nat.is_eq(_, 0n) : Bool}
  UL.u32_eq_value(Nu.a1.b(d), 0)

def pi.eq255(+d: Nat, +hd: {Nat.is_lt(d, 256n) == True{} : Bool}) -> {U32.is_eq(Nu.a1.b(d), 255) == Nat.is_eq(d, 255n) : Bool}:
  %AB.ab.byte(d, hd) : {U32.is_eq(Nu.a1.b(d), 255) == Nat.is_eq(_, 255n) : Bool}
  UL.u32_eq_value(Nu.a1.b(d), 255)

def pi.sub255_lt(+d: Nat) -> {Nat.is_lt(Nat.sub(255n, d), 256n) == True{} : Bool}:
  AN.an.le_lt_succ(Nat.sub(255n, d), 255n, pi.sub_le(255n, d))

# the complement of an octet d is the octet 255 - d
def pi.comp_b(+d: Nat, +hd: {Nat.is_lt(d, 256n) == True{} : Bool}) -> {U32.sub(255, Nu.a1.b(d)) == Nu.a1.b(Nat.sub(255n, d)) : U32}:
  +hv = AB.ab.byte(d, hd)
  +hle : {Nat.is_le(U32.to_nat(Nu.a1.b(d)), U32.to_nat(255)) == True{} : Bool} = Equal.trans(Bool, Nat.is_le(U32.to_nat(Nu.a1.b(d)), 255n), Nat.is_le(d, 255n), True{}, Equal.cong(Nat, Bool, x => Nat.is_le(x, 255n), U32.to_nat(Nu.a1.b(d)), d, hv), pi.lt256_le(d, hd))
  +e1 = UL.u32_sub_value(255, Nu.a1.b(d), hle)
  +e2 : {U32.to_nat(U32.sub(255, Nu.a1.b(d))) == Nat.sub(255n, d) : Nat} = Equal.trans(Nat, U32.to_nat(U32.sub(255, Nu.a1.b(d))), Nat.sub(255n, U32.to_nat(Nu.a1.b(d))), Nat.sub(255n, d), e1, Equal.cong(Nat, Nat, x => Nat.sub(255n, x), U32.to_nat(Nu.a1.b(d)), d, hv))
  +e3 = AB.ab.byte(Nat.sub(255n, d), pi.sub255_lt(d))
  UL.u32_value_eq(U32.sub(255, Nu.a1.b(d)), Nu.a1.b(Nat.sub(255n, d)), Equal.trans(Nat, U32.to_nat(U32.sub(255, Nu.a1.b(d))), Nat.sub(255n, d), U32.to_nat(Nu.a1.b(Nat.sub(255n, d))), e2, Equal.sym(Nat, U32.to_nat(Nu.a1.b(Nat.sub(255n, d))), Nat.sub(255n, d), e3)))

# Masking

def pi.fix_b(+k: Nat) -> {B.byte(Nu.a1.b(k)) == Nu.a1.b(k) : U32}:
  AL.al.byte_idem(U32.from_nat(k))

def pi.fix_bytes(ds: List<&2, Nat>) -> {B.mask(Nu.a1.bytes_of(ds)) == Nu.a1.bytes_of(ds) : List<&2, U32>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      %Equal.sym(U32, B.byte(Nu.a1.b(d)), Nu.a1.b(d), pi.fix_b(d)) : {Con{_, B.mask(Nu.a1.bytes_of(t))} == Con{Nu.a1.b(d), Nu.a1.bytes_of(t)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(Nu.a1.bytes_of(t)), Nu.a1.bytes_of(t), pi.fix_bytes(t)) : {Con{Nu.a1.b(d), _} == Con{Nu.a1.b(d), Nu.a1.bytes_of(t)} : List<&2, U32>}
      {==}

# a list fixed by masking is its Octets' list, and its length theirs
def pi.to_of(+c: List<&2, U32>, +hf: {B.mask(c) == c : List<&2, U32>}) -> {B.Octets.to_list(B.Octets.of_list(c)) == c : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(c)), B.mask(c), c, AL.al.to_of(c), hf)

def pi.len_of(+c: List<&2, U32>, +hf: {B.mask(c) == c : List<&2, U32>}) -> {B.Octets.len(B.Octets.of_list(c)) == List.length(&2, U32, c) : Nat}:
  %pi.to_of(c, hf) : {B.Octets.len(B.Octets.of_list(c)) == List.length(&2, U32, _) : Nat}
  AL.al.olen(B.Octets.of_list(c))

# Canonical digits: one, or a first that is not zero

def pi.canon(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, Nil{}}:
      True{}
    case Con{d, Con{e, t}}:
      Nat.is_le(1n, d)

def pi.lead(ds: List<&2, Nat>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{d, t}:
      d

def pi.lead_app(xs: List<&2, Nat>, +ys: List<&2, Nat>, +hne: {PN.pn.ne(xs) == True{} : Bool}) -> {pi.lead(List.append(&2, Nat, xs, ys)) == pi.lead(xs) : Nat}:
  match xs:
    case Nil{}:
      Empty.absurd({pi.lead(ys) == 0n : Nat}, AN.an.ft(hne))
    case Con{d, t}:
      {==}

def pi.canon_snoc(xs: List<&2, Nat>, +r: Nat, +hne: {PN.pn.ne(xs) == True{} : Bool}) -> {pi.canon(List.append(&2, Nat, xs, [r])) == Nat.is_le(1n, pi.lead(xs)) : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({pi.canon([r]) == Nat.is_le(1n, 0n) : Bool}, AN.an.ft(hne))
    case Con{+d, t}:
      match t:
        case Nil{}:
          {==}
        case Con{e, u}:
          {==}

# q * b + r = n with r < b <= n: q >= 1
def pi.q_pos(+q: Nat, +r: Nat, +n: Nat, +bp: Nat, +hr: {Nat.add(Nat.mul(q, 1n+bp), r) == n : Nat}, +hrl: {Nat.is_lt(r, 1n+bp) == True{} : Bool}, +hn: {Nat.is_lt(n, 1n+bp) == False{} : Bool}) -> {Nat.is_le(1n, q) == True{} : Bool}:
  match q:
    case 0n:
      +e1 = Equal.cong(Nat, Bool, x => Nat.is_lt(x, 1n+bp), r, n, hr)
      +e2 = Equal.trans(Bool, Nat.is_lt(r, 1n+bp), Nat.is_lt(n, 1n+bp), False{}, e1, hn)
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, AN.an.tf(Equal.trans(Bool, True{}, Nat.is_lt(r, 1n+bp), False{}, Equal.sym(Bool, Nat.is_lt(r, 1n+bp), True{}, hrl), e2)))
    case 1n+p:
      AN.an.le_zero(p)

def pi.div_pos(+n: Nat, +bp: Nat, +hn: {Nat.is_lt(n, 1n+bp) == False{} : Bool}) -> {Nat.is_le(1n, Nat.div(n, 1n+bp)) == True{} : Bool}:
  pi.q_pos(Nat.div(n, 1n+bp), Nat.mod(n, 1n+bp), n, bp, AN.an.recon(n, bp), AN.an.mod_lt(n, bp), hn)

# the first digit of a number of at least 1 is at least 1
def pi.lead_digits(fuel: Nat, lt: Bool, +bp: Nat, +n: Nat, +hl: {Nat.is_lt(n, 1n+bp) == lt : Bool}, +hn: {Nat.is_le(1n, n) == True{} : Bool}) -> {Nat.is_le(1n, pi.lead(Nu.a1.digits.go(fuel, lt, 1n+bp, n))) == True{} : Bool}:
  match fuel lt:
    case _ True{}:
      hn
    case 0n False{}:
      hn
    case 1n+ +f False{}:
      +q = Nat.div(n, 1n+bp)
      %Equal.sym(Nat, pi.lead(List.append(&2, Nat, Nu.a1.digits.go(f, Nat.is_lt(q, 1n+bp), 1n+bp, q), [Nat.mod(n, 1n+bp)])), pi.lead(Nu.a1.digits.go(f, Nat.is_lt(q, 1n+bp), 1n+bp, q)), pi.lead_app(Nu.a1.digits.go(f, Nat.is_lt(q, 1n+bp), 1n+bp, q), [Nat.mod(n, 1n+bp)], PN.pn.digits_ne(f, Nat.is_lt(q, 1n+bp), 1n+bp, q))) : {Nat.is_le(1n, _) == True{} : Bool}
      pi.lead_digits(f, Nat.is_lt(q, 1n+bp), bp, q, {==}, pi.div_pos(n, bp, hl))

# the digits of a number are canonical
def pi.canon_digits(fuel: Nat, lt: Bool, +bp: Nat, +n: Nat, +hl: {Nat.is_lt(n, 1n+bp) == lt : Bool}) -> {pi.canon(Nu.a1.digits.go(fuel, lt, 1n+bp, n)) == True{} : Bool}:
  match fuel lt:
    case _ True{}:
      {==}
    case 0n False{}:
      {==}
    case 1n+ +f False{}:
      +q = Nat.div(n, 1n+bp)
      +xs = Nu.a1.digits.go(f, Nat.is_lt(q, 1n+bp), 1n+bp, q)
      %Equal.sym(Bool, pi.canon(List.append(&2, Nat, xs, [Nat.mod(n, 1n+bp)])), Nat.is_le(1n, pi.lead(xs)), pi.canon_snoc(xs, Nat.mod(n, 1n+bp), PN.pn.digits_ne(f, Nat.is_lt(q, 1n+bp), 1n+bp, q))) : {_ == True{} : Bool}
      pi.lead_digits(f, Nat.is_lt(q, 1n+bp), bp, q, {==}, pi.div_pos(n, bp, hl))

def pi.canon_top(+n: Nat) -> {pi.canon(Nu.a1.digits(256n, n)) == True{} : Bool}:
  pi.canon_digits(n, Nat.is_lt(n, 256n), 255n, n, {==})

# Complemented digits

def pi.cmap(ds: List<&2, Nat>) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      Con{Nat.sub(255n, d), pi.cmap(t)}

def pi.all_cmap(ds: List<&2, Nat>) -> {PN.pn.all_lt(pi.cmap(ds), 256n) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      AN.an.and_i(Nat.is_lt(Nat.sub(255n, d), 256n), PN.pn.all_lt(pi.cmap(t), 256n), pi.sub255_lt(d), pi.all_cmap(t))

def pi.cmap_cmap(ds: List<&2, Nat>, +hall: {PN.pn.all_lt(ds, 256n) == True{} : Bool}) -> {pi.cmap(pi.cmap(ds)) == ds : List<&2, Nat>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      +hd = AN.an.and_l(Nat.is_lt(d, 256n), PN.pn.all_lt(t, 256n), hall)
      +ht = AN.an.and_r(Nat.is_lt(d, 256n), PN.pn.all_lt(t, 256n), hall)
      %pi.sub_sub(255n, d, pi.lt256_le(d, hd)) : {Con{Nat.sub(255n, Nat.sub(255n, d)), pi.cmap(pi.cmap(t))} == Con{_, t} : List<&2, Nat>}
      %pi.cmap_cmap(t, ht) : {Con{Nat.sub(255n, Nat.sub(255n, d)), pi.cmap(pi.cmap(t))} == Con{Nat.sub(255n, Nat.sub(255n, d)), _} : List<&2, Nat>}
      {==}

# the complement of digits' octets is the octets of the complemented digits
def pi.comp_bytes(ds: List<&2, Nat>, +hall: {PN.pn.all_lt(ds, 256n) == True{} : Bool}) -> {P.a1.int.comp(Nu.a1.bytes_of(ds)) == Nu.a1.bytes_of(pi.cmap(ds)) : List<&2, U32>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      +hd = AN.an.and_l(Nat.is_lt(d, 256n), PN.pn.all_lt(t, 256n), hall)
      +ht = AN.an.and_r(Nat.is_lt(d, 256n), PN.pn.all_lt(t, 256n), hall)
      %pi.comp_b(d, hd) : {Con{U32.sub(255, Nu.a1.b(d)), P.a1.int.comp(Nu.a1.bytes_of(t))} == Con{_, Nu.a1.bytes_of(pi.cmap(t))} : List<&2, U32>}
      %pi.comp_bytes(t, ht) : {Con{U32.sub(255, Nu.a1.b(d)), P.a1.int.comp(Nu.a1.bytes_of(t))} == Con{U32.sub(255, Nu.a1.b(d)), _} : List<&2, U32>}
      {==}

# the value read from a negative integer's octets: its digits' value
def pi.neg_val(+ds: List<&2, Nat>, +hall: {PN.pn.all_lt(ds, 256n) == True{} : Bool}) -> {Nu.a1.fold256(P.a1.int.comp(Nu.a1.bytes_of(pi.cmap(ds))), 0n) == Nu.a1.horner(ds, 256n, 0n) : Nat}:
  %Equal.sym(List<&2, U32>, P.a1.int.comp(Nu.a1.bytes_of(pi.cmap(ds))), Nu.a1.bytes_of(pi.cmap(pi.cmap(ds))), pi.comp_bytes(pi.cmap(ds), pi.all_cmap(ds))) : {Nu.a1.fold256(_, 0n) == Nu.a1.horner(ds, 256n, 0n) : Nat}
  %Equal.sym(List<&2, Nat>, pi.cmap(pi.cmap(ds)), ds, pi.cmap_cmap(ds, hall)) : {Nu.a1.fold256(Nu.a1.bytes_of(_), 0n) == Nu.a1.horner(ds, 256n, 0n) : Nat}
  PN.pn.fold_bytes(ds, 0n, hall)

# Reading

# a list fixed by masking, as the contents of an element read as INTEGER
def pi.read_fixed(+c: List<&2, U32>, +hf: {B.mask(c) == c : List<&2, U32>}, +t: T.Asn1Tag, +res: P.Asn1Int, +h: {P.a1.int.of.pick(P.Asn1.int_content_ok(c), c) == Done{res} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}) -> {P.Asn1.get_int_as(t, N.Asn1Prim{t, B.Octets.of_list(c)}) == Done{res} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}:
  %Equal.sym(Result<&2, &2, E.Asn1Error, B.Octets>, P.Asn1.prim_as(t, N.Asn1Prim{t, B.Octets.of_list(c)}), Done{B.Octets.of_list(c)}, pi.prim_as(t, B.Octets.of_list(c))) : {P.a1.int.from(_) == Done{res} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(c)), c, pi.to_of(c, hf)) : {P.a1.int.of.pick(P.Asn1.int_content_ok(_), _) == Done{res} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
  h

def pi.len_fixed(+c: List<&2, U32>, +hf: {B.mask(c) == c : List<&2, U32>}, +hl: {Nat.is_le(B.Octets.len(B.Octets.of_list(c)), 6n) == True{} : Bool}) -> {Nat.is_le(List.length(&2, U32, c), 6n) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(List.length(&2, U32, c), 6n), Nat.is_le(B.Octets.len(B.Octets.of_list(c)), 6n), True{}, Equal.cong(Nat, Bool, x => Nat.is_le(x, 6n), List.length(&2, U32, c), B.Octets.len(B.Octets.of_list(c)), Equal.sym(Nat, B.Octets.len(B.Octets.of_list(c)), List.length(&2, U32, c), pi.len_of(c, hf))), hl)

# Non-negative integers

# a first octet below 128 (and not 00 unless alone): the contents are fine
def pi.ok_lo(+d0: Nat, rest: List<&2, Nat>, +hd: {Nat.is_lt(d0, 128n) == True{} : Bool}, +hcan: {pi.canon(Con{d0, rest}) == True{} : Bool}) -> {P.Asn1.int_content_ok(Nu.a1.bytes_of(Con{d0, rest})) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case Con{+d1, +r2}:
      +h256 = AN.an.lt_le_trans(d0, 128n, 256n, hd, {==})
      +e0 = Equal.trans(Bool, U32.is_eq(Nu.a1.b(d0), 0), Nat.is_eq(d0, 0n), False{}, pi.eq0(d0, h256), pi.ne0(d0, hcan))
      +e1 = Equal.trans(Bool, U32.is_eq(Nu.a1.b(d0), 255), Nat.is_eq(d0, 255n), False{}, pi.eq255(d0, h256), AN.an.lt_ne(d0, 255n, AN.an.lt_le_trans(d0, 128n, 255n, hd, {==})))
      %Equal.sym(Bool, U32.is_eq(Nu.a1.b(d0), 0), False{}, e0) : {Bool.not(Bool.or(Bool.and(_, U32.is_lt(Nu.a1.b(d1), 128)), Bool.and(U32.is_eq(Nu.a1.b(d0), 255), U32.is_le(128, Nu.a1.b(d1))))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(Nu.a1.b(d0), 255), False{}, e1) : {Bool.not(Bool.or(False{}, Bool.and(_, U32.is_le(128, Nu.a1.b(d1))))) == True{} : Bool}
      {==}

def pi.pos_hi(hi: Bool, +d0: Nat, +rest: List<&2, Nat>, +hhi: {U32.is_le(128, Nu.a1.b(d0)) == hi : Bool}, +hcan: {pi.canon(Con{d0, rest}) == True{} : Bool}, +hall: {PN.pn.all_lt(Con{d0, rest}, 256n) == True{} : Bool}, +hlen: {Nat.is_le(List.length(&2, U32, P.a1.int.pad(hi, Nu.a1.bytes_of(Con{d0, rest}))), 6n) == True{} : Bool}) -> {P.a1.int.of.pick(P.Asn1.int_content_ok(P.a1.int.pad(hi, Nu.a1.bytes_of(Con{d0, rest}))), P.a1.int.pad(hi, Nu.a1.bytes_of(Con{d0, rest}))) == Done{P.Asn1Int{False{}, Nu.a1.horner(Con{d0, rest}, 256n, 0n)}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}:
  match hi:
    case True{}:
      +hd = AN.an.and_l(Nat.is_lt(d0, 256n), PN.pn.all_lt(rest, 256n), hall)
      +hge = Equal.trans(Bool, Nat.is_le(128n, d0), U32.is_le(128, Nu.a1.b(d0)), True{}, Equal.sym(Bool, U32.is_le(128, Nu.a1.b(d0)), Nat.is_le(128n, d0), pi.le128(d0, hd)), hhi)
      +elt = Equal.trans(Bool, U32.is_lt(Nu.a1.b(d0), 128), Nat.is_lt(d0, 128n), False{}, pi.lt128(d0, hd), PN.pn.le_nlt(128n, d0, hge))
      %Equal.sym(Bool, U32.is_lt(Nu.a1.b(d0), 128), False{}, elt) : {P.a1.int.of.pick(Bool.not(Bool.or(_, False{})), Con{0, Nu.a1.bytes_of(Con{d0, rest})}) == Done{P.Asn1Int{False{}, Nu.a1.horner(Con{d0, rest}, 256n, 0n)}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
      %Equal.sym(Bool, Nat.is_le(List.length(&2, U32, Con{0, Nu.a1.bytes_of(Con{d0, rest})}), 6n), True{}, hlen) : {P.a1.int.of.small(_, Con{0, Nu.a1.bytes_of(Con{d0, rest})}) == Done{P.Asn1Int{False{}, Nu.a1.horner(Con{d0, rest}, 256n, 0n)}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
      Equal.cong(Nat, Result<&2, &2, E.Asn1Error, P.Asn1Int>, v => Done{P.Asn1Int{False{}, v}}, Nu.a1.fold256(Nu.a1.bytes_of(Con{d0, rest}), 0n), Nu.a1.horner(Con{d0, rest}, 256n, 0n), PN.pn.fold_bytes(Con{d0, rest}, 0n, hall))
    case False{}:
      +hd = AN.an.and_l(Nat.is_lt(d0, 256n), PN.pn.all_lt(rest, 256n), hall)
      +hlt = AN.an.nle_lt(d0, 128n, Equal.trans(Bool, Nat.is_le(128n, d0), U32.is_le(128, Nu.a1.b(d0)), False{}, Equal.sym(Bool, U32.is_le(128, Nu.a1.b(d0)), Nat.is_le(128n, d0), pi.le128(d0, hd)), hhi))
      %Equal.sym(Bool, P.Asn1.int_content_ok(Nu.a1.bytes_of(Con{d0, rest})), True{}, pi.ok_lo(d0, rest, hlt, hcan)) : {P.a1.int.of.pick(_, Nu.a1.bytes_of(Con{d0, rest})) == Done{P.Asn1Int{False{}, Nu.a1.horner(Con{d0, rest}, 256n, 0n)}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
      %Equal.sym(Bool, Nat.is_le(List.length(&2, U32, Nu.a1.bytes_of(Con{d0, rest})), 6n), True{}, hlen) : {P.a1.int.of.small(_, Nu.a1.bytes_of(Con{d0, rest})) == Done{P.Asn1Int{False{}, Nu.a1.horner(Con{d0, rest}, 256n, 0n)}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
      %Equal.sym(Bool, U32.is_le(128, Nu.a1.b(d0)), False{}, hhi) : {Done{P.a1.int.value(_, Nu.a1.bytes_of(Con{d0, rest}))} == Done{P.Asn1Int{False{}, Nu.a1.horner(Con{d0, rest}, 256n, 0n)}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
      Equal.cong(Nat, Result<&2, &2, E.Asn1Error, P.Asn1Int>, v => Done{P.Asn1Int{False{}, v}}, Nu.a1.fold256(Nu.a1.bytes_of(Con{d0, rest}), 0n), Nu.a1.horner(Con{d0, rest}, 256n, 0n), PN.pn.fold_bytes(Con{d0, rest}, 0n, hall))

def pi.pos_ds(ds: List<&2, Nat>, +hall: {PN.pn.all_lt(ds, 256n) == True{} : Bool}, +hcan: {pi.canon(ds) == True{} : Bool}, +hlen: {Nat.is_le(List.length(&2, U32, P.a1.int.pad(U32.is_le(128, P.a1.int.first(Nu.a1.bytes_of(ds))), Nu.a1.bytes_of(ds))), 6n) == True{} : Bool}) -> {P.a1.int.of.pick(P.Asn1.int_content_ok(P.a1.int.pad(U32.is_le(128, P.a1.int.first(Nu.a1.bytes_of(ds))), Nu.a1.bytes_of(ds))), P.a1.int.pad(U32.is_le(128, P.a1.int.first(Nu.a1.bytes_of(ds))), Nu.a1.bytes_of(ds))) == Done{P.Asn1Int{False{}, Nu.a1.horner(ds, 256n, 0n)}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}:
  match ds:
    case Nil{}:
      Empty.absurd({P.a1.int.of.pick(P.Asn1.int_content_ok(P.a1.int.pad(U32.is_le(128, 0), Nil{})), P.a1.int.pad(U32.is_le(128, 0), Nil{})) == Done{P.Asn1Int{False{}, 0n}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}, AN.an.ft(hcan))
    case Con{+d0, +rest}:
      pi.pos_hi(U32.is_le(128, Nu.a1.b(d0)), d0, rest, {==}, hcan, hall, hlen)

def pi.fix_pad(hi: Bool, +ys: List<&2, U32>, +hf: {B.mask(ys) == ys : List<&2, U32>}) -> {B.mask(P.a1.int.pad(hi, ys)) == P.a1.int.pad(hi, ys) : List<&2, U32>}:
  match hi:
    case True{}:
      %Equal.sym(List<&2, U32>, B.mask(ys), ys, hf) : {Con{0, _} == Con{0, ys} : List<&2, U32>}
      {==}
    case False{}:
      hf

# a non-negative integer of six octets or fewer reads back
def pi.pos(+m: Nat, +t: T.Asn1Tag, +hl: {Nat.is_le(B.Octets.len(N.Asn1Node.content(P.Asn1.int_as(t, P.Asn1Int{False{}, m}))), 6n) == True{} : Bool}) -> {P.Asn1.get_int_as(t, P.Asn1.int_as(t, P.Asn1Int{False{}, m})) == Done{P.Asn1Int{False{}, m}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}:
  +ds = Nu.a1.digits(256n, m)
  +c = P.a1.int.nat(m)
  +hf = pi.fix_pad(U32.is_le(128, P.a1.int.first(Nu.a1.bytes_of(ds))), Nu.a1.bytes_of(ds), pi.fix_bytes(ds))
  +hall = PN.pn.digits_lt_top(254n, m)
  %PN.pn.horner_digits_top(255n, m) : {P.Asn1.get_int_as(t, P.Asn1.int_as(t, P.Asn1Int{False{}, m})) == Done{P.Asn1Int{False{}, _}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
  pi.read_fixed(c, hf, t, P.Asn1Int{False{}, Nu.a1.horner(ds, 256n, 0n)}, pi.pos_ds(ds, hall, pi.canon_top(m), pi.len_fixed(c, hf, hl)))

# Negative integers

# a first octet of 128 or more (and not FF unless alone): the contents are
# fine
def pi.ok_neg(+d0: Nat, rest: List<&2, Nat>, +hd: {Nat.is_lt(d0, 256n) == True{} : Bool}, +hge: {Nat.is_le(128n, Nat.sub(255n, d0)) == True{} : Bool}, +hcan: {pi.canon(Con{d0, rest}) == True{} : Bool}) -> {P.Asn1.int_content_ok(Nu.a1.bytes_of(pi.cmap(Con{d0, rest}))) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case Con{+d1, +r2}:
      +c0 = Nat.sub(255n, d0)
      +h256 = pi.sub255_lt(d0)
      +e0 = Equal.trans(Bool, U32.is_eq(Nu.a1.b(c0), 0), Nat.is_eq(c0, 0n), False{}, pi.eq0(c0, h256), pi.ne0(c0, AN.an.le_trans(1n, 128n, c0, {==}, hge)))
      +e1 = Equal.trans(Bool, U32.is_eq(Nu.a1.b(c0), 255), Nat.is_eq(c0, 255n), False{}, pi.eq255(c0, h256), AN.an.lt_ne(c0, 255n, pi.sub_lt(255n, d0, hcan, pi.lt256_le(d0, hd))))
      %Equal.sym(Bool, U32.is_eq(Nu.a1.b(c0), 0), False{}, e0) : {Bool.not(Bool.or(Bool.and(_, U32.is_lt(Nu.a1.b(Nat.sub(255n, d1)), 128)), Bool.and(U32.is_eq(Nu.a1.b(c0), 255), U32.is_le(128, Nu.a1.b(Nat.sub(255n, d1)))))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(Nu.a1.b(c0), 255), False{}, e1) : {Bool.not(Bool.or(False{}, Bool.and(_, U32.is_le(128, Nu.a1.b(Nat.sub(255n, d1)))))) == True{} : Bool}
      {==}

def pi.neg_lo(lo: Bool, +d0: Nat, +rest: List<&2, Nat>, +hlo: {U32.is_lt(Nu.a1.b(Nat.sub(255n, d0)), 128) == lo : Bool}, +hcan: {pi.canon(Con{d0, rest}) == True{} : Bool}, +hall: {PN.pn.all_lt(Con{d0, rest}, 256n) == True{} : Bool}, +hlen: {Nat.is_le(List.length(&2, U32, P.a1.int.npad(lo, Nu.a1.bytes_of(pi.cmap(Con{d0, rest})))), 6n) == True{} : Bool}) -> {P.a1.int.of.pick(P.Asn1.int_content_ok(P.a1.int.npad(lo, Nu.a1.bytes_of(pi.cmap(Con{d0, rest})))), P.a1.int.npad(lo, Nu.a1.bytes_of(pi.cmap(Con{d0, rest})))) == Done{P.Asn1Int{True{}, Nat.add(Nu.a1.horner(Con{d0, rest}, 256n, 0n), 1n)}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}:
  match lo:
    case True{}:
      +c0 = Nat.sub(255n, d0)
      +hlt = Equal.trans(Bool, Nat.is_lt(c0, 128n), U32.is_lt(Nu.a1.b(c0), 128), True{}, Equal.sym(Bool, U32.is_lt(Nu.a1.b(c0), 128), Nat.is_lt(c0, 128n), pi.lt128(c0, pi.sub255_lt(d0))), hlo)
      +ele = Equal.trans(Bool, U32.is_le(128, Nu.a1.b(c0)), Nat.is_le(128n, c0), False{}, pi.le128(c0, pi.sub255_lt(d0)), AN.an.lt_nle(c0, 128n, hlt))
      %Equal.sym(Bool, U32.is_le(128, Nu.a1.b(c0)), False{}, ele) : {P.a1.int.of.pick(Bool.not(_), Con{255, Nu.a1.bytes_of(pi.cmap(Con{d0, rest}))}) == Done{P.Asn1Int{True{}, Nat.add(Nu.a1.horner(Con{d0, rest}, 256n, 0n), 1n)}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
      %Equal.sym(Bool, Nat.is_le(List.length(&2, U32, Con{255, Nu.a1.bytes_of(pi.cmap(Con{d0, rest}))}), 6n), True{}, hlen) : {P.a1.int.of.small(_, Con{255, Nu.a1.bytes_of(pi.cmap(Con{d0, rest}))}) == Done{P.Asn1Int{True{}, Nat.add(Nu.a1.horner(Con{d0, rest}, 256n, 0n), 1n)}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
      Equal.cong(Nat, Result<&2, &2, E.Asn1Error, P.Asn1Int>, v => Done{P.Asn1Int{True{}, Nat.add(v, 1n)}}, Nu.a1.fold256(P.a1.int.comp(Nu.a1.bytes_of(pi.cmap(Con{d0, rest}))), 0n), Nu.a1.horner(Con{d0, rest}, 256n, 0n), pi.neg_val(Con{d0, rest}, hall))
    case False{}:
      +c0 = Nat.sub(255n, d0)
      +hd = AN.an.and_l(Nat.is_lt(d0, 256n), PN.pn.all_lt(rest, 256n), hall)
      +hnlt = Equal.trans(Bool, Nat.is_lt(c0, 128n), U32.is_lt(Nu.a1.b(c0), 128), False{}, Equal.sym(Bool, U32.is_lt(Nu.a1.b(c0), 128), Nat.is_lt(c0, 128n), pi.lt128(c0, pi.sub255_lt(d0))), hlo)
      +hge = pi.le_of_nlt(c0, 128n, hnlt)
      +ele = Equal.trans(Bool, U32.is_le(128, Nu.a1.b(c0)), Nat.is_le(128n, c0), True{}, pi.le128(c0, pi.sub255_lt(d0)), hge)
      %Equal.sym(Bool, P.Asn1.int_content_ok(Nu.a1.bytes_of(pi.cmap(Con{d0, rest}))), True{}, pi.ok_neg(d0, rest, hd, hge, hcan)) : {P.a1.int.of.pick(_, Nu.a1.bytes_of(pi.cmap(Con{d0, rest}))) == Done{P.Asn1Int{True{}, Nat.add(Nu.a1.horner(Con{d0, rest}, 256n, 0n), 1n)}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
      %Equal.sym(Bool, Nat.is_le(List.length(&2, U32, Nu.a1.bytes_of(pi.cmap(Con{d0, rest}))), 6n), True{}, hlen) : {P.a1.int.of.small(_, Nu.a1.bytes_of(pi.cmap(Con{d0, rest}))) == Done{P.Asn1Int{True{}, Nat.add(Nu.a1.horner(Con{d0, rest}, 256n, 0n), 1n)}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
      %Equal.sym(Bool, U32.is_le(128, Nu.a1.b(c0)), True{}, ele) : {Done{P.a1.int.value(_, Nu.a1.bytes_of(pi.cmap(Con{d0, rest})))} == Done{P.Asn1Int{True{}, Nat.add(Nu.a1.horner(Con{d0, rest}, 256n, 0n), 1n)}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
      Equal.cong(Nat, Result<&2, &2, E.Asn1Error, P.Asn1Int>, v => Done{P.Asn1Int{True{}, Nat.add(v, 1n)}}, Nu.a1.fold256(P.a1.int.comp(Nu.a1.bytes_of(pi.cmap(Con{d0, rest}))), 0n), Nu.a1.horner(Con{d0, rest}, 256n, 0n), pi.neg_val(Con{d0, rest}, hall))

def pi.neg_ds(ds: List<&2, Nat>, +hall: {PN.pn.all_lt(ds, 256n) == True{} : Bool}, +hcan: {pi.canon(ds) == True{} : Bool}, +hlen: {Nat.is_le(List.length(&2, U32, P.a1.int.npad(U32.is_lt(P.a1.int.first(Nu.a1.bytes_of(pi.cmap(ds))), 128), Nu.a1.bytes_of(pi.cmap(ds)))), 6n) == True{} : Bool}) -> {P.a1.int.of.pick(P.Asn1.int_content_ok(P.a1.int.npad(U32.is_lt(P.a1.int.first(Nu.a1.bytes_of(pi.cmap(ds))), 128), Nu.a1.bytes_of(pi.cmap(ds)))), P.a1.int.npad(U32.is_lt(P.a1.int.first(Nu.a1.bytes_of(pi.cmap(ds))), 128), Nu.a1.bytes_of(pi.cmap(ds)))) == Done{P.Asn1Int{True{}, Nat.add(Nu.a1.horner(ds, 256n, 0n), 1n)}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}:
  match ds:
    case Nil{}:
      Empty.absurd({P.a1.int.of.pick(P.Asn1.int_content_ok(P.a1.int.npad(U32.is_lt(0, 128), Nil{})), P.a1.int.npad(U32.is_lt(0, 128), Nil{})) == Done{P.Asn1Int{True{}, 1n}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}, AN.an.ft(hcan))
    case Con{+d0, +rest}:
      pi.neg_lo(U32.is_lt(Nu.a1.b(Nat.sub(255n, d0)), 128), d0, rest, {==}, hcan, hall, hlen)

def pi.fix_npad(lo: Bool, +ys: List<&2, U32>, +hf: {B.mask(ys) == ys : List<&2, U32>}) -> {B.mask(P.a1.int.npad(lo, ys)) == P.a1.int.npad(lo, ys) : List<&2, U32>}:
  match lo:
    case True{}:
      %Equal.sym(List<&2, U32>, B.mask(ys), ys, hf) : {Con{255, _} == Con{255, ys} : List<&2, U32>}
      {==}
    case False{}:
      hf

# (m - 0) + 1 = 1 + m
def pi.succ_eq(+m: Nat) -> {Nat.add(Nat.sub(m, 0n), 1n) == 1n+m : Nat}:
  %Equal.sym(Nat, Nat.sub(m, 0n), m, AN.an.sub_zero(m)) : {Nat.add(_, 1n) == 1n+m : Nat}
  %Equal.sym(Nat, Nat.add(m, 1n), 1n+Nat.add(m, 0n), AN.an.add_succ(m, 0n)) : {_ == 1n+m : Nat}
  %Equal.sym(Nat, Nat.add(m, 0n), m, AN.an.add_zero(m)) : {1n+_ == 1n+m : Nat}
  {==}

# the contents as written (the complement of the digits' octets)
def pi.neg_c(+ds: List<&2, Nat>, +hall: {PN.pn.all_lt(ds, 256n) == True{} : Bool}, +hcan: {pi.canon(ds) == True{} : Bool}, +hlen: {Nat.is_le(List.length(&2, U32, P.a1.int.npad(U32.is_lt(P.a1.int.first(Nu.a1.bytes_of(pi.cmap(ds))), 128), Nu.a1.bytes_of(pi.cmap(ds)))), 6n) == True{} : Bool}) -> {P.a1.int.of.pick(P.Asn1.int_content_ok(P.a1.int.npad(U32.is_lt(P.a1.int.first(P.a1.int.comp(Nu.a1.bytes_of(ds))), 128), P.a1.int.comp(Nu.a1.bytes_of(ds)))), P.a1.int.npad(U32.is_lt(P.a1.int.first(P.a1.int.comp(Nu.a1.bytes_of(ds))), 128), P.a1.int.comp(Nu.a1.bytes_of(ds)))) == Done{P.Asn1Int{True{}, Nat.add(Nu.a1.horner(ds, 256n, 0n), 1n)}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}:
  %Equal.sym(List<&2, U32>, P.a1.int.comp(Nu.a1.bytes_of(ds)), Nu.a1.bytes_of(pi.cmap(ds)), pi.comp_bytes(ds, hall)) : {P.a1.int.of.pick(P.Asn1.int_content_ok(P.a1.int.npad(U32.is_lt(P.a1.int.first(_), 128), _)), P.a1.int.npad(U32.is_lt(P.a1.int.first(_), 128), _)) == Done{P.Asn1Int{True{}, Nat.add(Nu.a1.horner(ds, 256n, 0n), 1n)}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
  pi.neg_ds(ds, hall, hcan, hlen)

# -(1 + mp), of six octets or fewer, reads back
def pi.neg(+mp: Nat, +t: T.Asn1Tag, +hl: {Nat.is_le(B.Octets.len(N.Asn1Node.content(P.Asn1.int_as(t, P.Asn1Int{True{}, 1n+mp}))), 6n) == True{} : Bool}) -> {P.Asn1.get_int_as(t, P.Asn1.int_as(t, P.Asn1Int{True{}, 1n+mp})) == Done{P.Asn1Int{True{}, 1n+mp}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}:
  +n = Nat.sub(mp, 0n)
  +ds = Nu.a1.digits(256n, n)
  +hall = PN.pn.digits_lt_top(254n, n)
  +ec = pi.comp_bytes(ds, hall)
  +hf0 = Equal.trans(List<&2, U32>, B.mask(P.a1.int.comp(Nu.a1.bytes_of(ds))), B.mask(Nu.a1.bytes_of(pi.cmap(ds))), P.a1.int.comp(Nu.a1.bytes_of(ds)), Equal.cong(List<&2, U32>, List<&2, U32>, l => B.mask(l), P.a1.int.comp(Nu.a1.bytes_of(ds)), Nu.a1.bytes_of(pi.cmap(ds)), ec), Equal.trans(List<&2, U32>, B.mask(Nu.a1.bytes_of(pi.cmap(ds))), Nu.a1.bytes_of(pi.cmap(ds)), P.a1.int.comp(Nu.a1.bytes_of(ds)), pi.fix_bytes(pi.cmap(ds)), Equal.sym(List<&2, U32>, P.a1.int.comp(Nu.a1.bytes_of(ds)), Nu.a1.bytes_of(pi.cmap(ds)), ec)))
  +c = P.a1.int.neg(1n+mp)
  +hf = pi.fix_npad(U32.is_lt(P.a1.int.first(P.a1.int.comp(Nu.a1.bytes_of(ds))), 128), P.a1.int.comp(Nu.a1.bytes_of(ds)), hf0)
  +hlc = pi.len_fixed(c, hf, hl)
  +hlen = Equal.trans(Bool, Nat.is_le(List.length(&2, U32, P.a1.int.npad(U32.is_lt(P.a1.int.first(Nu.a1.bytes_of(pi.cmap(ds))), 128), Nu.a1.bytes_of(pi.cmap(ds)))), 6n), Nat.is_le(List.length(&2, U32, c), 6n), True{}, Equal.cong(List<&2, U32>, Bool, l => Nat.is_le(List.length(&2, U32, P.a1.int.npad(U32.is_lt(P.a1.int.first(l), 128), l)), 6n), Nu.a1.bytes_of(pi.cmap(ds)), P.a1.int.comp(Nu.a1.bytes_of(ds)), Equal.sym(List<&2, U32>, P.a1.int.comp(Nu.a1.bytes_of(ds)), Nu.a1.bytes_of(pi.cmap(ds)), ec)), hlc)
  +hv = Equal.trans(Nat, Nat.add(Nu.a1.horner(ds, 256n, 0n), 1n), Nat.add(n, 1n), 1n+mp, Equal.cong(Nat, Nat, x => Nat.add(x, 1n), Nu.a1.horner(ds, 256n, 0n), n, PN.pn.horner_digits_top(255n, n)), pi.succ_eq(mp))
  %hv : {P.Asn1.get_int_as(t, P.Asn1.int_as(t, P.Asn1Int{True{}, 1n+mp})) == Done{P.Asn1Int{True{}, _}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}
  pi.read_fixed(c, hf, t, P.Asn1Int{True{}, Nat.add(Nu.a1.horner(ds, 256n, 0n), 1n)}, pi.neg_c(ds, hall, pi.canon_top(n), hlen))

# INTEGER contents of six octets or fewer read back as the integer written
# (other than -0, which is written as 0)
def pi.int_rt(+t: T.Asn1Tag, neg: Bool, +m: Nat, +hz: {Bool.and(neg, Nat.is_eq(m, 0n)) == False{} : Bool}, +hl: {Nat.is_le(B.Octets.len(N.Asn1Node.content(P.Asn1.int_as(t, P.Asn1Int{neg, m}))), 6n) == True{} : Bool}) -> {P.Asn1.get_int_as(t, P.Asn1.int_as(t, P.Asn1Int{neg, m})) == Done{P.Asn1Int{neg, m}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}:
  match neg m:
    case True{} 0n:
      Empty.absurd({P.Asn1.get_int_as(t, P.Asn1.int_as(t, P.Asn1Int{True{}, 0n})) == Done{P.Asn1Int{True{}, 0n}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}, AN.an.tf(hz))
    case True{} 1n+mp:
      pi.neg(mp, t, hl)
    case False{} _:
      pi.pos(m, t, hl)
