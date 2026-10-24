# Proof helpers for bend-osdev-asn1: INTEGER contents the reader accepts
# are the contents the writer writes for the integer read. The reader takes
# contents in the fewest octets (8.3.2); as digits in base 256 they have no
# leading zero, except a 00 before an octet of 128 or more, so the digits of
# their value are those octets again (pc.dh: the digits of Horner's value of
# canonical digits are those digits, as division by 256 is unique), and for
# a negative integer the same holds of the complemented octets, with an FF
# before an octet below 128.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
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
import ./proof_int.bend as PI
import ./proof_clock.bend as PK
import ./proof_strict.bend as PS

# Octets as digits

def pc.vals(xs: List<&2, U32>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{U32.to_nat(x), pc.vals(t)}

def pc.bv_lt(+x: U32, +hx: {B.byte(x) == x : U32}) -> {Nat.is_lt(U32.to_nat(x), 256n) == True{} : Bool}:
  +h1 = Equal.trans(Bool, U32.is_lt(x, 256), U32.is_lt(B.byte(x), 256), True{}, Equal.cong(U32, Bool, y => U32.is_lt(y, 256), x, B.byte(x), Equal.sym(U32, B.byte(x), x, hx)), BL.byte_below_256(x))
  Equal.trans(Bool, Nat.is_lt(U32.to_nat(x), 256n), U32.is_lt(x, 256), True{}, Equal.sym(Bool, U32.is_lt(x, 256), Nat.is_lt(U32.to_nat(x), 256n), UL.u32_lt_value(x, 256)), h1)

def pc.bv_eq(+x: U32, +hx: {B.byte(x) == x : U32}) -> {Nu.a1.b(U32.to_nat(x)) == x : U32}:
  UL.u32_value_eq(Nu.a1.b(U32.to_nat(x)), x, AB.ab.byte(U32.to_nat(x), pc.bv_lt(x, hx)))

def pc.bytes_vals(xs: List<&2, U32>, +hf: {B.mask(xs) == xs : List<&2, U32>}) -> {Nu.a1.bytes_of(pc.vals(xs)) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = PS.sx.cons_fix(x, t, hf)
      +ht = PS.sx.cons_fix_t(x, t, hf)
      %pc.bv_eq(x, hx) : {Con{Nu.a1.b(U32.to_nat(x)), Nu.a1.bytes_of(pc.vals(t))} == Con{_, t} : List<&2, U32>}
      %pc.bytes_vals(t, ht) : {Con{Nu.a1.b(U32.to_nat(x)), Nu.a1.bytes_of(pc.vals(t))} == Con{Nu.a1.b(U32.to_nat(x)), _} : List<&2, U32>}
      {==}

def pc.all_vals(xs: List<&2, U32>, +hf: {B.mask(xs) == xs : List<&2, U32>}) -> {PN.pn.all_lt(pc.vals(xs), 256n) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      AN.an.and_i(Nat.is_lt(U32.to_nat(x), 256n), PN.pn.all_lt(pc.vals(t), 256n), pc.bv_lt(x, PS.sx.cons_fix(x, t, hf)), pc.all_vals(t, PS.sx.cons_fix_t(x, t, hf)))

# The last digit and the ones before it

def pc.init(t: List<&2, Nat>, +d: Nat) -> List<&2, Nat>:
  match t:
    case Nil{}:
      Nil{}
    case Con{e, u}:
      Con{d, pc.init(u, e)}

def pc.last(t: List<&2, Nat>, +d: Nat) -> Nat:
  match t:
    case Nil{}:
      d
    case Con{e, u}:
      pc.last(u, e)

def pc.split(t: List<&2, Nat>, +d: Nat) -> {List.append(&2, Nat, pc.init(t, d), [pc.last(t, d)]) == Con{d, t} : List<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+e, +u}:
      %pc.split(u, e) : {Con{d, List.append(&2, Nat, pc.init(u, e), [pc.last(u, e)])} == Con{d, _} : List<&2, Nat>}
      {==}

def pc.all_init(t: List<&2, Nat>, +d: Nat, +h: {PN.pn.all_lt(Con{d, t}, 256n) == True{} : Bool}) -> {PN.pn.all_lt(pc.init(t, d), 256n) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+e, +u}:
      +h2 = AN.an.and_r(Nat.is_lt(d, 256n), PN.pn.all_lt(Con{e, u}, 256n), h)
      AN.an.and_i(Nat.is_lt(d, 256n), PN.pn.all_lt(pc.init(u, e), 256n), AN.an.and_l(Nat.is_lt(d, 256n), PN.pn.all_lt(Con{e, u}, 256n), h), pc.all_init(u, e, h2))

def pc.last_lt(t: List<&2, Nat>, +d: Nat, +h: {PN.pn.all_lt(Con{d, t}, 256n) == True{} : Bool}) -> {Nat.is_lt(pc.last(t, d), 256n) == True{} : Bool}:
  match t:
    case Nil{}:
      AN.an.and_l(Nat.is_lt(d, 256n), True{}, h)
    case Con{+e, +u}:
      pc.last_lt(u, e, AN.an.and_r(Nat.is_lt(d, 256n), PN.pn.all_lt(Con{e, u}, 256n), h))

# a first digit of at least 1 makes digits canonical
def pc.canon1(+d: Nat, t: List<&2, Nat>, +h: {Nat.is_le(1n, d) == True{} : Bool}) -> {PI.pi.canon(Con{d, t}) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{e, u}:
      h

# Horner's value is at least the value so far
def pc.horner_ge(ds: List<&2, Nat>, +acc: Nat) -> {Nat.is_le(acc, Nu.a1.horner(ds, 256n, acc)) == True{} : Bool}:
  match ds:
    case Nil{}:
      AN.an.le_refl(acc)
    case Con{+x, +t}:
      +a2 = Nat.add(Nat.mul(acc, 256n), x)
      AN.an.le_trans(acc, a2, Nu.a1.horner(t, 256n, a2), AN.an.le_trans(acc, Nat.mul(acc, 256n), a2, AN.an.le_mul(acc, 255n), AN.an.le_add(Nat.mul(acc, 256n), x)), pc.horner_ge(t, a2))

# h >= 1: 256 <= h * 256 + z, and h < h * 256 + z
def pc.ge256(+h: Nat, +z: Nat, +h1: {Nat.is_le(1n, h) == True{} : Bool}) -> {Nat.is_le(256n, Nat.add(Nat.mul(h, 256n), z)) == True{} : Bool}:
  match h:
    case 0n:
      Empty.absurd({Nat.is_le(256n, Nat.add(Nat.mul(0n, 256n), z)) == True{} : Bool}, AN.an.ft(h1))
    case 1n+p:
      AN.an.le_trans(256n, Nat.mul(1n+p, 256n), Nat.add(Nat.mul(1n+p, 256n), z), AN.an.le_add(256n, Nat.mul(p, 256n)), AN.an.le_add(Nat.mul(1n+p, 256n), z))

def pc.gt_self(+h: Nat, +z: Nat, +h1: {Nat.is_le(1n, h) == True{} : Bool}) -> {Nat.is_le(1n+h, Nat.add(Nat.mul(h, 256n), z)) == True{} : Bool}:
  match h:
    case 0n:
      Empty.absurd({Nat.is_le(1n, Nat.add(Nat.mul(0n, 256n), z)) == True{} : Bool}, AN.an.ft(h1))
    case 1n+p:
      +e1 = AN.an.le_add_mono(256n, p, Nat.mul(p, 256n), AN.an.le_mul(p, 255n))
      +e2 = AN.an.le_trans(2n+p, Nat.add(256n, p), Nat.add(256n, Nat.mul(p, 256n)), AN.an.le_add_l(254n, p), e1)
      AN.an.le_trans(2n+p, Nat.mul(1n+p, 256n), Nat.add(Nat.mul(1n+p, 256n), z), e2, AN.an.le_add(Nat.mul(1n+p, 256n), z))

# the digits of the value of canonical digits are those digits
def pc.dh(fuel: Nat, +d: Nat, t: List<&2, Nat>, +hall: {PN.pn.all_lt(Con{d, t}, 256n) == True{} : Bool}, +hcan: {PI.pi.canon(Con{d, t}) == True{} : Bool}, +hf: {Nat.is_le(Nu.a1.horner(Con{d, t}, 256n, 0n), fuel) == True{} : Bool}) -> {Nu.a1.digits.go(fuel, Nat.is_lt(Nu.a1.horner(Con{d, t}, 256n, 0n), 256n), 256n, Nu.a1.horner(Con{d, t}, 256n, 0n)) == Con{d, t} : List<&2, Nat>}:
  match fuel t:
    case _ Nil{}:
      %Equal.sym(Bool, Nat.is_lt(d, 256n), True{}, AN.an.and_l(Nat.is_lt(d, 256n), True{}, hall)) : {Nu.a1.digits.go(fuel, _, 256n, d) == [d] : List<&2, Nat>}
      {==}
    case 0n Con{+e, +u}:
      +hge = pc.ge256(d, e, hcan)
      +hh = AN.an.le_trans(Nat.add(Nat.mul(d, 256n), e), Nu.a1.horner(Con{d, Con{e, u}}, 256n, 0n), 0n, pc.horner_ge(u, Nat.add(Nat.mul(d, 256n), e)), hf)
      Empty.absurd({Nu.a1.digits.go(0n, Nat.is_lt(Nu.a1.horner(Con{d, Con{e, u}}, 256n, 0n), 256n), 256n, Nu.a1.horner(Con{d, Con{e, u}}, 256n, 0n)) == Con{d, Con{e, u}} : List<&2, Nat>}, AN.an.ft(AN.an.le_trans(256n, Nat.add(Nat.mul(d, 256n), e), 0n, hge, hh)))
    case 1n+ +f Con{+e, +u}:
      +p = pc.init(Con{e, u}, d)
      +z = pc.last(Con{e, u}, d)
      +hp = Nu.a1.horner(p, 256n, 0n)
      +hd1 = hcan
      +hz = pc.last_lt(Con{e, u}, d, hall)
      +hpall = pc.all_init(Con{e, u}, d, hall)
      +hp1 = AN.an.le_trans(1n, d, hp, hd1, pc.horner_ge(pc.init(u, e), d))
      +n = Nat.add(Nat.mul(hp, 256n), z)
      +es = pc.split(Con{e, u}, d)
      +eh = PN.pn.horner_snoc(p, 256n, 0n, z)
      +hfn = Equal.trans(Bool, Nat.is_le(n, 1n+f), Nat.is_le(Nu.a1.horner(List.append(&2, Nat, p, [z]), 256n, 0n), 1n+f), True{}, Equal.cong(Nat, Bool, x => Nat.is_le(x, 1n+f), n, Nu.a1.horner(List.append(&2, Nat, p, [z]), 256n, 0n), Equal.sym(Nat, Nu.a1.horner(List.append(&2, Nat, p, [z]), 256n, 0n), n, eh)), Equal.trans(Bool, Nat.is_le(Nu.a1.horner(List.append(&2, Nat, p, [z]), 256n, 0n), 1n+f), Nat.is_le(Nu.a1.horner(Con{d, Con{e, u}}, 256n, 0n), 1n+f), True{}, Equal.cong(List<&2, Nat>, Bool, l => Nat.is_le(Nu.a1.horner(l, 256n, 0n), 1n+f), List.append(&2, Nat, p, [z]), Con{d, Con{e, u}}, es), hf))
      +hpf = AN.an.le_trans(1n+hp, n, 1n+f, pc.gt_self(hp, z, hp1), hfn)
      +ih = pc.dh(f, d, pc.init(u, e), hpall, pc.canon1(d, pc.init(u, e), hd1), hpf)
      %es : {Nu.a1.digits.go(1n+f, Nat.is_lt(Nu.a1.horner(_, 256n, 0n), 256n), 256n, Nu.a1.horner(_, 256n, 0n)) == _ : List<&2, Nat>}
      %Equal.sym(Nat, Nu.a1.horner(List.append(&2, Nat, p, [z]), 256n, 0n), n, eh) : {Nu.a1.digits.go(1n+f, Nat.is_lt(_, 256n), 256n, _) == List.append(&2, Nat, p, [z]) : List<&2, Nat>}
      %Equal.sym(Bool, Nat.is_lt(n, 256n), False{}, PN.pn.le_nlt(256n, n, pc.ge256(hp, z, hp1))) : {Nu.a1.digits.go(1n+f, _, 256n, n) == List.append(&2, Nat, p, [z]) : List<&2, Nat>}
      %Equal.sym(Nat, Nat.div(n, 256n), hp, PK.pk.div_of(hp, z, 255n, hz)) : {List.append(&2, Nat, Nu.a1.digits.go(f, Nat.is_lt(_, 256n), 256n, _), [Nat.mod(n, 256n)]) == List.append(&2, Nat, p, [z]) : List<&2, Nat>}
      %Equal.sym(Nat, Nat.mod(n, 256n), z, PK.pk.mod_of(hp, z, 255n, hz)) : {List.append(&2, Nat, Nu.a1.digits.go(f, Nat.is_lt(hp, 256n), 256n, hp), [_]) == List.append(&2, Nat, p, [z]) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, Nu.a1.digits.go(f, Nat.is_lt(hp, 256n), 256n, hp), p, ih) : {List.append(&2, Nat, _, [z]) == List.append(&2, Nat, p, [z]) : List<&2, Nat>}
      {==}

# the octets of the value of canonical digits are their octets
def pc.be_can(ds: List<&2, Nat>, +hall: {PN.pn.all_lt(ds, 256n) == True{} : Bool}, +hcan: {PI.pi.canon(ds) == True{} : Bool}) -> {Nu.a1.be(Nu.a1.horner(ds, 256n, 0n)) == Nu.a1.bytes_of(ds) : List<&2, U32>}:
  match ds:
    case Nil{}:
      Empty.absurd({Nu.a1.be(0n) == Nil{} : List<&2, U32>}, AN.an.ft(hcan))
    case Con{+d, +t}:
      +m = Nu.a1.horner(Con{d, t}, 256n, 0n)
      Equal.cong(List<&2, Nat>, List<&2, U32>, l => Nu.a1.bytes_of(l), Nu.a1.digits.go(m, Nat.is_lt(m, 256n), 256n, m), Con{d, t}, pc.dh(m, d, t, hall, hcan, AN.an.le_refl(m)))

# Arithmetic

def pc.le_ne_lt(+a: Nat, +b: Nat, +h1: {Nat.is_le(a, b) == True{} : Bool}, +h2: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, AN.an.tf(h2))
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 0n) == True{} : Bool}, AN.an.ft(h1))
    case 1n+ap 1n+bp:
      pc.le_ne_lt(ap, bp, h1, h2)

def pc.sub_pos(+a: Nat, +d: Nat, +h: {Nat.is_lt(d, a) == True{} : Bool}) -> {Nat.is_le(1n, Nat.sub(a, d)) == True{} : Bool}:
  match a d:
    case 0n _:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, AN.an.ft(Equal.trans(Bool, False{}, Nat.is_lt(d, 0n), True{}, Equal.sym(Bool, Nat.is_lt(d, 0n), False{}, AN.an.lt0(d)), h)))
    case 1n+ap 0n:
      AN.an.le_zero(ap)
    case 1n+ap 1n+dp:
      pc.sub_pos(ap, dp, h)

def pc.not_or_f(b: Bool, +h: {Bool.not(Bool.or(b, False{})) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, AN.an.ft(h))
    case False{}:
      {==}

def pc.add1(+f: Nat) -> {Nat.add(f, 1n) == 1n+f : Nat}:
  %Equal.sym(Nat, Nat.add(f, 1n), 1n+Nat.add(f, 0n), AN.an.add_succ(f, 0n)) : {_ == 1n+f : Nat}
  %Equal.sym(Nat, Nat.add(f, 0n), f, AN.an.add_zero(f)) : {1n+_ == 1n+f : Nat}
  {==}

# The writer's contents of the integer of canonical digits

def pc.nat_c(+ds: List<&2, Nat>, +hall: {PN.pn.all_lt(ds, 256n) == True{} : Bool}, +hcan: {PI.pi.canon(ds) == True{} : Bool}, hi: Bool, +hhi: {U32.is_le(128, P.a1.int.first(Nu.a1.bytes_of(ds))) == hi : Bool}) -> {P.a1.int.nat(Nu.a1.horner(ds, 256n, 0n)) == P.a1.int.pad(hi, Nu.a1.bytes_of(ds)) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, Nu.a1.be(Nu.a1.horner(ds, 256n, 0n)), Nu.a1.bytes_of(ds), pc.be_can(ds, hall, hcan)) : {P.a1.int.pad(U32.is_le(128, P.a1.int.first(_)), _) == P.a1.int.pad(hi, Nu.a1.bytes_of(ds)) : List<&2, U32>}
  %Equal.sym(Bool, U32.is_le(128, P.a1.int.first(Nu.a1.bytes_of(ds))), hi, hhi) : {P.a1.int.pad(_, Nu.a1.bytes_of(ds)) == P.a1.int.pad(hi, Nu.a1.bytes_of(ds)) : List<&2, U32>}
  {==}

def pc.neg_c(+ds: List<&2, Nat>, +hall: {PN.pn.all_lt(ds, 256n) == True{} : Bool}, +hcan: {PI.pi.canon(PI.pi.cmap(ds)) == True{} : Bool}, lo: Bool, +hlo: {U32.is_lt(P.a1.int.first(Nu.a1.bytes_of(ds)), 128) == lo : Bool}) -> {P.a1.int.neg(1n+Nu.a1.horner(PI.pi.cmap(ds), 256n, 0n)) == P.a1.int.npad(lo, Nu.a1.bytes_of(ds)) : List<&2, U32>}:
  +h = Nu.a1.horner(PI.pi.cmap(ds), 256n, 0n)
  +hc = PI.pi.all_cmap(ds)
  %Equal.sym(Nat, Nat.sub(h, 0n), h, AN.an.sub_zero(h)) : {P.a1.int.npad(U32.is_lt(P.a1.int.first(P.a1.int.comp(Nu.a1.be(_))), 128), P.a1.int.comp(Nu.a1.be(_))) == P.a1.int.npad(lo, Nu.a1.bytes_of(ds)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, Nu.a1.be(h), Nu.a1.bytes_of(PI.pi.cmap(ds)), pc.be_can(PI.pi.cmap(ds), hc, hcan)) : {P.a1.int.npad(U32.is_lt(P.a1.int.first(P.a1.int.comp(_)), 128), P.a1.int.comp(_)) == P.a1.int.npad(lo, Nu.a1.bytes_of(ds)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, P.a1.int.comp(Nu.a1.bytes_of(PI.pi.cmap(ds))), Nu.a1.bytes_of(PI.pi.cmap(PI.pi.cmap(ds))), PI.pi.comp_bytes(PI.pi.cmap(ds), hc)) : {P.a1.int.npad(U32.is_lt(P.a1.int.first(_), 128), _) == P.a1.int.npad(lo, Nu.a1.bytes_of(ds)) : List<&2, U32>}
  %Equal.sym(List<&2, Nat>, PI.pi.cmap(PI.pi.cmap(ds)), ds, PI.pi.cmap_cmap(ds, hall)) : {P.a1.int.npad(U32.is_lt(P.a1.int.first(Nu.a1.bytes_of(_)), 128), Nu.a1.bytes_of(_)) == P.a1.int.npad(lo, Nu.a1.bytes_of(ds)) : List<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(P.a1.int.first(Nu.a1.bytes_of(ds)), 128), lo, hlo) : {P.a1.int.npad(_, Nu.a1.bytes_of(ds)) == P.a1.int.npad(lo, Nu.a1.bytes_of(ds)) : List<&2, U32>}
  {==}

# Non-negative integers read

def pc.pos_d0(d0: Nat, rest: List<&2, Nat>, +hall: {PN.pn.all_lt(Con{d0, rest}, 256n) == True{} : Bool}, +hn: {U32.is_le(128, Nu.a1.b(d0)) == False{} : Bool}, +hok: {P.Asn1.int_content_ok(Nu.a1.bytes_of(Con{d0, rest})) == True{} : Bool}) -> {P.a1.int.nat(Nu.a1.horner(Con{d0, rest}, 256n, 0n)) == Nu.a1.bytes_of(Con{d0, rest}) : List<&2, U32>}:
  match d0 rest:
    case 0n Nil{}:
      pc.nat_c([0n], hall, {==}, False{}, {==})
    case 0n Con{+d1, +r2}:
      +hr = AN.an.and_r(Nat.is_lt(0n, 256n), PN.pn.all_lt(Con{d1, r2}, 256n), hall)
      +hd1 = AN.an.and_l(Nat.is_lt(d1, 256n), PN.pn.all_lt(r2, 256n), hr)
      +hlt = pc.not_or_f(U32.is_lt(Nu.a1.b(d1), 128), hok)
      +hge = PI.pi.le_of_nlt(d1, 128n, Equal.trans(Bool, Nat.is_lt(d1, 128n), U32.is_lt(Nu.a1.b(d1), 128), False{}, Equal.sym(Bool, U32.is_lt(Nu.a1.b(d1), 128), Nat.is_lt(d1, 128n), PI.pi.lt128(d1, hd1)), hlt))
      +hi = Equal.trans(Bool, U32.is_le(128, Nu.a1.b(d1)), Nat.is_le(128n, d1), True{}, PI.pi.le128(d1, hd1), hge)
      pc.nat_c(Con{d1, r2}, hr, pc.canon1(d1, r2, AN.an.le_trans(1n, 128n, d1, {==}, hge)), True{}, hi)
    case 1n+ +p +rest2:
      pc.nat_c(Con{1n+p, rest2}, hall, pc.canon1(1n+p, rest2, AN.an.le_zero(p)), False{}, hn)

# Negative integers read

def pc.neg_q(q: Bool, +d0: Nat, rest: List<&2, Nat>, +hall: {PN.pn.all_lt(Con{d0, rest}, 256n) == True{} : Bool}, +hge: {Nat.is_le(128n, d0) == True{} : Bool}, +hq: {Nat.is_eq(d0, 255n) == q : Bool}, +hok: {P.Asn1.int_content_ok(Nu.a1.bytes_of(Con{d0, rest})) == True{} : Bool}) -> {P.a1.int.neg(1n+Nu.a1.horner(PI.pi.cmap(Con{d0, rest}), 256n, 0n)) == Nu.a1.bytes_of(Con{d0, rest}) : List<&2, U32>}:
  match q rest:
    case False{} +rest2:
      +hd = AN.an.and_l(Nat.is_lt(d0, 256n), PN.pn.all_lt(rest2, 256n), hall)
      +hlo = Equal.trans(Bool, U32.is_lt(Nu.a1.b(d0), 128), Nat.is_lt(d0, 128n), False{}, PI.pi.lt128(d0, hd), PN.pn.le_nlt(128n, d0, hge))
      +h255 = pc.le_ne_lt(d0, 255n, AN.an.lt_succ_le(d0, 255n, hd), hq)
      pc.neg_c(Con{d0, rest2}, hall, pc.canon1(Nat.sub(255n, d0), PI.pi.cmap(rest2), pc.sub_pos(255n, d0, h255)), False{}, hlo)
    case True{} Nil{}:
      +hd = AN.an.and_l(Nat.is_lt(d0, 256n), True{}, hall)
      +hlo = Equal.trans(Bool, U32.is_lt(Nu.a1.b(d0), 128), Nat.is_lt(d0, 128n), False{}, PI.pi.lt128(d0, hd), PN.pn.le_nlt(128n, d0, hge))
      pc.neg_c([d0], hall, {==}, False{}, hlo)
    case True{} Con{+d1, +r2}:
      +ed = AN.an.eq_sound(d0, 255n, hq)
      +hok2 = Equal.trans(Bool, P.Asn1.int_content_ok(Nu.a1.bytes_of(Con{255n, Con{d1, r2}})), P.Asn1.int_content_ok(Nu.a1.bytes_of(Con{d0, Con{d1, r2}})), True{}, Equal.cong(Nat, Bool, x => P.Asn1.int_content_ok(Nu.a1.bytes_of(Con{x, Con{d1, r2}})), 255n, d0, Equal.sym(Nat, d0, 255n, ed)), hok)
      +hr = AN.an.and_r(Nat.is_lt(d0, 256n), PN.pn.all_lt(Con{d1, r2}, 256n), hall)
      +hd1 = AN.an.and_l(Nat.is_lt(d1, 256n), PN.pn.all_lt(r2, 256n), hr)
      +hle = AN.an.not_t(U32.is_le(128, Nu.a1.b(d1)), hok2)
      +hlt1 = AN.an.nle_lt(d1, 128n, Equal.trans(Bool, Nat.is_le(128n, d1), U32.is_le(128, Nu.a1.b(d1)), False{}, Equal.sym(Bool, U32.is_le(128, Nu.a1.b(d1)), Nat.is_le(128n, d1), PI.pi.le128(d1, hd1)), hle))
      +hlo1 = Equal.trans(Bool, U32.is_lt(Nu.a1.b(d1), 128), Nat.is_lt(d1, 128n), True{}, PI.pi.lt128(d1, hd1), hlt1)
      +hcan = pc.canon1(Nat.sub(255n, d1), PI.pi.cmap(r2), pc.sub_pos(255n, d1, AN.an.lt_le_trans(d1, 128n, 255n, hlt1, {==})))
      %Equal.sym(Nat, d0, 255n, ed) : {P.a1.int.neg(1n+Nu.a1.horner(PI.pi.cmap(Con{_, Con{d1, r2}}), 256n, 0n)) == Nu.a1.bytes_of(Con{_, Con{d1, r2}}) : List<&2, U32>}
      pc.neg_c(Con{d1, r2}, hr, hcan, True{}, hlo1)

# the writer's contents of the integer read from canonical contents
def pc.core_neg(neg: Bool, +d0: Nat, +rest: List<&2, Nat>, +hn: {U32.is_le(128, Nu.a1.b(d0)) == neg : Bool}, +hall: {PN.pn.all_lt(Con{d0, rest}, 256n) == True{} : Bool}, +hok: {P.Asn1.int_content_ok(Nu.a1.bytes_of(Con{d0, rest})) == True{} : Bool}) -> {P.a1.int.content(P.a1.int.value(neg, Nu.a1.bytes_of(Con{d0, rest}))) == Nu.a1.bytes_of(Con{d0, rest}) : List<&2, U32>}:
  match neg:
    case False{}:
      %Equal.sym(Nat, Nu.a1.fold256(Nu.a1.bytes_of(Con{d0, rest}), 0n), Nu.a1.horner(Con{d0, rest}, 256n, 0n), PN.pn.fold_bytes(Con{d0, rest}, 0n, hall)) : {P.a1.int.nat(_) == Nu.a1.bytes_of(Con{d0, rest}) : List<&2, U32>}
      pc.pos_d0(d0, rest, hall, hn, hok)
    case True{}:
      +hd = AN.an.and_l(Nat.is_lt(d0, 256n), PN.pn.all_lt(rest, 256n), hall)
      +hge = Equal.trans(Bool, Nat.is_le(128n, d0), U32.is_le(128, Nu.a1.b(d0)), True{}, Equal.sym(Bool, U32.is_le(128, Nu.a1.b(d0)), Nat.is_le(128n, d0), PI.pi.le128(d0, hd)), hn)
      +f = Nu.a1.fold256(P.a1.int.comp(Nu.a1.bytes_of(Con{d0, rest})), 0n)
      %Equal.sym(Nat, Nat.add(f, 1n), 1n+f, pc.add1(f)) : {P.a1.int.content(P.Asn1Int{True{}, _}) == Nu.a1.bytes_of(Con{d0, rest}) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, P.a1.int.comp(Nu.a1.bytes_of(Con{d0, rest})), Nu.a1.bytes_of(PI.pi.cmap(Con{d0, rest})), PI.pi.comp_bytes(Con{d0, rest}, hall)) : {P.a1.int.neg(1n+Nu.a1.fold256(_, 0n)) == Nu.a1.bytes_of(Con{d0, rest}) : List<&2, U32>}
      %Equal.sym(Nat, Nu.a1.fold256(Nu.a1.bytes_of(PI.pi.cmap(Con{d0, rest})), 0n), Nu.a1.horner(PI.pi.cmap(Con{d0, rest}), 256n, 0n), PN.pn.fold_bytes(PI.pi.cmap(Con{d0, rest}), 0n, PI.pi.all_cmap(Con{d0, rest}))) : {P.a1.int.neg(1n+_) == Nu.a1.bytes_of(Con{d0, rest}) : List<&2, U32>}
      pc.neg_q(Nat.is_eq(d0, 255n), d0, rest, hall, hge, {==}, hok)

def pc.core_ds(ds: List<&2, Nat>, +hall: {PN.pn.all_lt(ds, 256n) == True{} : Bool}, +hok: {P.Asn1.int_content_ok(Nu.a1.bytes_of(ds)) == True{} : Bool}) -> {P.a1.int.content(P.a1.int.value(U32.is_le(128, P.a1.int.first(Nu.a1.bytes_of(ds))), Nu.a1.bytes_of(ds))) == Nu.a1.bytes_of(ds) : List<&2, U32>}:
  match ds:
    case Nil{}:
      Empty.absurd({P.a1.int.content(P.a1.int.value(U32.is_le(128, 0), Nil{})) == Nil{} : List<&2, U32>}, AN.an.ft(hok))
    case Con{+d0, +rest}:
      pc.core_neg(U32.is_le(128, Nu.a1.b(d0)), d0, rest, {==}, hall, hok)

def pc.core(+xs: List<&2, U32>, +hf: {B.mask(xs) == xs : List<&2, U32>}, +hok: {P.Asn1.int_content_ok(xs) == True{} : Bool}) -> {P.a1.int.content(P.a1.int.value(U32.is_le(128, P.a1.int.first(xs)), xs)) == xs : List<&2, U32>}:
  +ds = pc.vals(xs)
  +e = pc.bytes_vals(xs, hf)
  +hok2 = Equal.trans(Bool, P.Asn1.int_content_ok(Nu.a1.bytes_of(ds)), P.Asn1.int_content_ok(xs), True{}, Equal.cong(List<&2, U32>, Bool, l => P.Asn1.int_content_ok(l), Nu.a1.bytes_of(ds), xs, e), hok)
  %e : {P.a1.int.content(P.a1.int.value(U32.is_le(128, P.a1.int.first(_)), _)) == _ : List<&2, U32>}
  pc.core_ds(ds, pc.all_vals(xs, hf), hok2)

# The reader

def pc.small(ok: Bool, +xs: List<&2, U32>, +hf: {B.mask(xs) == xs : List<&2, U32>}, +hok: {P.Asn1.int_content_ok(xs) == True{} : Bool}, -i: P.Asn1Int, +e: {P.a1.int.of.small(ok, xs) == Done{i} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}) -> {P.a1.int.content(i) == xs : List<&2, U32>}:
  match ok:
    case True{}:
      %PS.sx.dd(P.Asn1Int, P.a1.int.value(U32.is_le(128, P.a1.int.first(xs)), xs), i, e) : {P.a1.int.content(_) == xs : List<&2, U32>}
      pc.core(xs, hf, hok)
    case False{}:
      Empty.absurd({P.a1.int.content(i) == xs : List<&2, U32>}, PS.sx.fd(P.Asn1Int, E.Asn1TooLong{}, i, e))

def pc.pick(ok: Bool, +xs: List<&2, U32>, +hf: {B.mask(xs) == xs : List<&2, U32>}, +hok: {P.Asn1.int_content_ok(xs) == ok : Bool}, -i: P.Asn1Int, +e: {P.a1.int.of.pick(ok, xs) == Done{i} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}) -> {P.a1.int.content(i) == xs : List<&2, U32>}:
  match ok:
    case True{}:
      pc.small(Nat.is_le(List.length(&2, U32, xs), Nu.a1.max_octets()), xs, hf, hok, i, e)
    case False{}:
      Empty.absurd({P.a1.int.content(i) == xs : List<&2, U32>}, PS.sx.fd(P.Asn1Int, E.Asn1BadInteger{}, i, e))

def pc.tag(ok: Bool, +t: T.Asn1Tag, +v: T.Asn1Tag, +c: B.Octets, -i: P.Asn1Int, +hok: {T.Asn1Tag.is_eq(t, v) == ok : Bool}, +e: {P.a1.int.from(P.a1.prim_as.pick(ok, c)) == Done{i} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}) -> {P.Asn1.int_as(t, i) == N.Asn1Prim{v, c} : N.Asn1Node}:
  match ok:
    case True{}:
      +xs = B.Octets.to_list(c)
      +et = PS.sx.tag_eq(t, v, hok)
      +ec = pc.pick(P.Asn1.int_content_ok(xs), xs, AL.al.mask_to(c), {==}, i, e)
      %et : {P.Asn1.int_as(t, i) == N.Asn1Prim{_, c} : N.Asn1Node}
      %Equal.sym(List<&2, U32>, P.a1.int.content(i), xs, ec) : {N.Asn1Prim{t, B.Octets.of_list(_)} == N.Asn1Prim{t, c} : N.Asn1Node}
      %AL.al.of_to(c) : {N.Asn1Prim{t, B.Octets.of_list(xs)} == N.Asn1Prim{t, _} : N.Asn1Node}
      {==}
    case False{}:
      Empty.absurd({P.Asn1.int_as(t, i) == N.Asn1Prim{v, c} : N.Asn1Node}, PS.sx.fd(P.Asn1Int, E.Asn1Unexpected{}, i, e))

# an INTEGER element read (with tag t) is the element written for its value
def pc.int_c(+t: T.Asn1Tag, n: N.Asn1Node, -i: P.Asn1Int, +e: {P.Asn1.get_int_as(t, n) == Done{i} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}) -> {P.Asn1.int_as(t, i) == n : N.Asn1Node}:
  match n:
    case N.Asn1Prim{+v, +c}:
      pc.tag(T.Asn1Tag.is_eq(t, v), t, v, c, i, {==}, e)
    case N.Asn1Cons{v, xs}:
      Empty.absurd({P.Asn1.int_as(t, i) == N.Asn1Cons{v, xs} : N.Asn1Node}, PS.sx.fd(P.Asn1Int, E.Asn1Unexpected{}, i, e))

def pc.nat_of(i: P.Asn1Int, -m: Nat, +e: {P.a1.int.nat_of(i) == Done{m} : Result<&2, &2, E.Asn1Error, Nat>}) -> {i == P.Asn1Int{False{}, m} : P.Asn1Int}:
  match i:
    case P.Asn1Int{True{}, k}:
      Empty.absurd({P.Asn1Int{True{}, k} == P.Asn1Int{False{}, m} : P.Asn1Int}, PS.sx.fd(Nat, E.Asn1Negative{}, m, e))
    case P.Asn1Int{False{}, +k}:
      Equal.cong(Nat, P.Asn1Int, x => P.Asn1Int{False{}, x}, k, m, PS.sx.dd(Nat, k, m, e))

def pc.nat_from(res: Result<&2, &2, E.Asn1Error, P.Asn1Int>, -m: Nat, +e: {P.a1.int.nat_from(res) == Done{m} : Result<&2, &2, E.Asn1Error, Nat>}) -> {res == Done{P.Asn1Int{False{}, m}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}:
  match res:
    case Fail{x}:
      Empty.absurd({Fail{x} == Done{P.Asn1Int{False{}, m}} : Result<&2, &2, E.Asn1Error, P.Asn1Int>}, PS.sx.fd(Nat, x, m, e))
    case Done{+i}:
      Equal.cong(P.Asn1Int, Result<&2, &2, E.Asn1Error, P.Asn1Int>, x => Done{x}, i, P.Asn1Int{False{}, m}, pc.nat_of(i, m, e))
