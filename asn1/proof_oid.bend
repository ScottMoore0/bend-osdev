# Proofs for bend-osdev-asn1: OBJECT IDENTIFIER contents read back as the
# arcs written. Each subidentifier's base-128 octets read back as it and
# pass the fewest-octets check (proof_num.bend's pn.r128_b128), and the
# first subidentifier splits back into the first two arcs.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./number.bend as Nu
import ./oidval.bend as O
import ./proof_nat.bend as AN
import ./proof_list.bend as AL
import ./proof_u32.bend as AU
import ./proof_num.bend as PN
import ./proof_enc.bend as PE
import ../u32/LAWS.bend as UL
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF.bend as UP
import ../u32/PROOF_order.bend as UOP

def po.b128_ne(+s: Nat) -> {Nat.is_le(1n, List.length(&2, U32, Nu.a1.b128(s))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, U32, Nu.a1.enc128(Nu.a1.digits(128n, s))), List.length(&2, Nat, Nu.a1.digits(128n, s)), PN.pn.len_enc128(Nu.a1.digits(128n, s))) : {Nat.is_le(1n, _) == True{} : Bool}
  PN.pn.ne_len(Nu.a1.digits(128n, s), PN.pn.digits_ne_top(128n, s))

def po.len_subids(+s: Nat, +rest: List<&2, Nat>) -> {List.length(&2, U32, O.a1.oid.subids(Con{s, rest})) == Nat.add(List.length(&2, U32, Nu.a1.b128(s)), List.length(&2, U32, O.a1.oid.subids(rest))) : Nat}:
  AL.al.app_len(Nu.a1.b128(s), O.a1.oid.subids(rest))

def po.one_ne(+s: Nat, xs: List<&2, U32>, m: Maybe<&2, List<&2, Nat>>, +h: {Nat.is_le(1n, List.length(&2, U32, xs)) == True{} : Bool}) -> {O.a1.oid.one(True{}, s, xs, m) == O.a1.oid.cons(s, m) : Maybe<&2, List<&2, Nat>>}:
  match xs:
    case Nil{}:
      Empty.absurd({O.a1.oid.one(True{}, s, Nil{}, m) == O.a1.oid.cons(s, m) : Maybe<&2, List<&2, Nat>>}, AN.an.ft(h))
    case Con{y, t}:
      {==}

# the subidentifiers' octets read back as them
def po.read(ss: List<&2, Nat>, f: Nat, +hne: {Nat.is_le(1n, List.length(&2, Nat, ss)) == True{} : Bool}, +hf: {Nat.is_le(List.length(&2, U32, O.a1.oid.subids(ss)), f) == True{} : Bool}, +hsm: {O.a1.oid.small(ss) == True{} : Bool}) -> {O.a1.oid.read(f, Nu.a1.r128(O.a1.oid.subids(ss), True{}, Nu.a1.max_octets(), 0n)) == Some{ss} : Maybe<&2, List<&2, Nat>>}:
  match ss:
    case Nil{}:
      Empty.absurd({O.a1.oid.read(f, Nu.a1.r128(O.a1.oid.subids(Nil{}), True{}, Nu.a1.max_octets(), 0n)) == Some{Nil{}} : Maybe<&2, List<&2, Nat>>}, AN.an.ft(hne))
    case Con{+s, +rest}:
      match rest:
        case Nil{}:
          match f:
            case 0n:
              +lb = List.length(&2, U32, Nu.a1.b128(s))
              +lt = List.length(&2, U32, O.a1.oid.subids(Nil{}))
              +hlen = Equal.trans(Bool, Nat.is_le(Nat.add(lb, lt), 0n), Nat.is_le(List.length(&2, U32, O.a1.oid.subids(Con{s, Nil{}})), 0n), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, 0n), Nat.add(lb, lt), List.length(&2, U32, O.a1.oid.subids(Con{s, Nil{}})), Equal.sym(Nat, List.length(&2, U32, O.a1.oid.subids(Con{s, Nil{}})), Nat.add(lb, lt), po.len_subids(s, Nil{}))), hf)
              +h1 = UO.nat_le_trans(1n, lb, 0n, po.b128_ne(s), UO.nat_le_trans(lb, Nat.add(lb, lt), 0n, UO.nat_le_add_r(lb, lt), hlen))
              Empty.absurd({O.a1.oid.read(0n, Nu.a1.r128(O.a1.oid.subids(Con{s, Nil{}}), True{}, Nu.a1.max_octets(), 0n)) == Some{Con{s, Nil{}}} : Maybe<&2, List<&2, Nat>>}, AN.an.ft(h1))
            case 1n+ +g:
              +bs = Nu.a1.b128(s)
              %Equal.sym(Maybe<&2, Nu.A1Num>, Nu.a1.r128(List.append(&2, U32, bs, Nil{}), True{}, Nu.a1.max_octets(), 0n), Some{Nu.A1Num{s, bs, Nil{}}}, PN.pn.r128_b128(s, Nil{}, 6n, AN.an.and_l(Nat.is_le(List.length(&2, U32, Nu.a1.b128(s)), 6n), O.a1.oid.small(Nil{}), hsm))) : {O.a1.oid.read(1n+g, _) == Some{[s]} : Maybe<&2, List<&2, Nat>>}
              %Equal.sym(Bool, Nu.a1.leq(bs, bs), True{}, AU.au.leq_refl(bs)) : {O.a1.oid.one(_, s, Nil{}, O.a1.oid.read(g, Nu.a1.r128(Nil{}, True{}, Nu.a1.max_octets(), 0n))) == Some{[s]} : Maybe<&2, List<&2, Nat>>}
              {==}
        case Con{+s2, +r2}:
          match f:
            case 0n:
              +lb = List.length(&2, U32, Nu.a1.b128(s))
              +lt = List.length(&2, U32, O.a1.oid.subids(Con{s2, r2}))
              +hlen = Equal.trans(Bool, Nat.is_le(Nat.add(lb, lt), 0n), Nat.is_le(List.length(&2, U32, O.a1.oid.subids(Con{s, Con{s2, r2}})), 0n), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, 0n), Nat.add(lb, lt), List.length(&2, U32, O.a1.oid.subids(Con{s, Con{s2, r2}})), Equal.sym(Nat, List.length(&2, U32, O.a1.oid.subids(Con{s, Con{s2, r2}})), Nat.add(lb, lt), po.len_subids(s, Con{s2, r2}))), hf)
              +h1 = UO.nat_le_trans(1n, lb, 0n, po.b128_ne(s), UO.nat_le_trans(lb, Nat.add(lb, lt), 0n, UO.nat_le_add_r(lb, lt), hlen))
              Empty.absurd({O.a1.oid.read(0n, Nu.a1.r128(O.a1.oid.subids(Con{s, Con{s2, r2}}), True{}, Nu.a1.max_octets(), 0n)) == Some{Con{s, Con{s2, r2}}} : Maybe<&2, List<&2, Nat>>}, AN.an.ft(h1))
            case 1n+ +g:
              +rest2 : List<&2, Nat> = Con{s2, r2}
              +bs = Nu.a1.b128(s)
              +tl = O.a1.oid.subids(rest2)
              +lb = List.length(&2, U32, bs)
              +lt = List.length(&2, U32, tl)
              +want : Maybe<&2, List<&2, Nat>> = Some{Con{s, rest2}}
              +hlen = Equal.trans(Bool, Nat.is_le(Nat.add(lb, lt), 1n+g), Nat.is_le(List.length(&2, U32, O.a1.oid.subids(Con{s, rest2})), 1n+g), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, 1n+g), Nat.add(lb, lt), List.length(&2, U32, O.a1.oid.subids(Con{s, rest2})), Equal.sym(Nat, List.length(&2, U32, O.a1.oid.subids(Con{s, rest2})), Nat.add(lb, lt), po.len_subids(s, rest2))), hf)
              +hg = AN.an.lt_succ_le(lt, g, UO.nat_lt_le_trans(lt, Nat.add(lb, lt), 1n+g, PE.pe.lt_plus(lb, lt, lt, po.b128_ne(s), UL.nat_le_refl(lt)), hlen))
              +l2 = List.length(&2, U32, Nu.a1.b128(s2))
              +l3 = List.length(&2, U32, O.a1.oid.subids(r2))
              +htl = Equal.trans(Bool, Nat.is_le(1n, lt), Nat.is_le(1n, Nat.add(l2, l3)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(1n, z), lt, Nat.add(l2, l3), po.len_subids(s2, r2)), UO.nat_le_trans(1n, l2, Nat.add(l2, l3), po.b128_ne(s2), UO.nat_le_add_r(l2, l3)))
              +more = O.a1.oid.read(g, Nu.a1.r128(tl, True{}, Nu.a1.max_octets(), 0n))
              %Equal.sym(Maybe<&2, Nu.A1Num>, Nu.a1.r128(List.append(&2, U32, bs, tl), True{}, Nu.a1.max_octets(), 0n), Some{Nu.A1Num{s, bs, tl}}, PN.pn.r128_b128(s, tl, 6n, AN.an.and_l(Nat.is_le(List.length(&2, U32, Nu.a1.b128(s)), 6n), O.a1.oid.small(rest2), hsm))) : {O.a1.oid.read(1n+g, _) == want : Maybe<&2, List<&2, Nat>>}
              %Equal.sym(Bool, Nu.a1.leq(bs, bs), True{}, AU.au.leq_refl(bs)) : {O.a1.oid.one(_, s, tl, more) == want : Maybe<&2, List<&2, Nat>>}
              %Equal.sym(Maybe<&2, List<&2, Nat>>, O.a1.oid.one(True{}, s, tl, more), O.a1.oid.cons(s, more), po.one_ne(s, tl, more, htl)) : {_ == want : Maybe<&2, List<&2, Nat>>}
              %Equal.sym(Maybe<&2, List<&2, Nat>>, more, Some{rest2}, po.read(rest2, g, AN.an.le_zero(List.length(&2, Nat, r2)), hg, AN.an.and_r(Nat.is_le(List.length(&2, U32, Nu.a1.b128(s)), 6n), O.a1.oid.small(rest2), hsm))) : {O.a1.oid.cons(s, _) == want : Maybe<&2, List<&2, Nat>>}
              {==}

# the subidentifiers' octets are masked
def po.fix_subids(ss: List<&2, Nat>) -> {B.mask(O.a1.oid.subids(ss)) == O.a1.oid.subids(ss) : List<&2, U32>}:
  match ss:
    case Nil{}:
      {==}
    case Con{+s, +rest}:
      AL.al.fixed_app(Nu.a1.b128(s), O.a1.oid.subids(rest), PE.pe.fix_enc128(Nu.a1.digits(128n, s)), po.fix_subids(rest))

# the first subidentifier splits back into the first two arcs
def po.split(x: Nat, +y: Nat, +rest: List<&2, Nat>, +hv: {O.a1.oid.valid2(x, y) == True{} : Bool}) -> {O.a1.oid.arcs(Some{O.a1.oid.to_subids(Con{x, Con{y, rest}})}) == Done{Con{x, Con{y, rest}}} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}:
  match x:
    case 0n:
      %Equal.sym(Bool, Nat.is_lt(y, 40n), True{}, hv) : {Done{O.a1.oid.split2(_, Nat.is_lt(y, 80n), y, rest)} == Done{Con{0n, Con{y, rest}}} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}
      {==}
    case 1n+x1:
      match x1:
        case 0n:
          %Equal.sym(Bool, Nat.is_lt(y, 0n), False{}, AN.an.lt0(y)) : {Done{O.a1.oid.split2(_, Nat.is_lt(y, 40n), Nat.add(40n, y), rest)} == Done{Con{1n, Con{y, rest}}} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}
          %Equal.sym(Bool, Nat.is_lt(y, 40n), True{}, hv) : {Done{O.a1.oid.split2(False{}, _, Nat.add(40n, y), rest)} == Done{Con{1n, Con{y, rest}}} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}
          %Equal.sym(Nat, Nat.sub(Nat.add(40n, y), 40n), y, AN.an.sub_add_l(40n, y)) : {Done{Con{1n, Con{_, rest}}} == Done{Con{1n, Con{y, rest}}} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}
          {==}
        case 1n+x2:
          match x2:
            case 0n:
              %Equal.sym(Bool, Nat.is_lt(y, 0n), False{}, AN.an.lt0(y)) : {Done{O.a1.oid.split2(False{}, _, Nat.add(80n, y), rest)} == Done{Con{2n, Con{y, rest}}} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}
              %Equal.sym(Nat, Nat.sub(Nat.add(80n, y), 80n), y, AN.an.sub_add_l(80n, y)) : {Done{Con{2n, Con{_, rest}}} == Done{Con{2n, Con{y, rest}}} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}
              {==}
            case 1n+x3:
              Empty.absurd({O.a1.oid.arcs(Some{O.a1.oid.to_subids(Con{3n+x3, Con{y, rest}})}) == Done{Con{3n+x3, Con{y, rest}}} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}, AN.an.ft(hv))

def po.disc(r: Result<&2, &2, E.Asn1Error, B.Octets>) -> Type:
  match r:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def po.fd(-x: E.Asn1Error, -y: B.Octets, e: {Fail{x} == Done{y} : Result<&2, &2, E.Asn1Error, B.Octets>}) -> Empty:
  %e : po.disc(_)
  Unit{}

def po.od(r: Result<&2, &2, E.Asn1Error, B.Octets>) -> B.Octets:
  match r:
    case Fail{x}:
      B.Octets.empty()
    case Done{y}:
      y

def po.rt(ok: Bool, arcs: List<&2, Nat>, -o: B.Octets, +hv: {O.Asn1.oid_valid(arcs) == ok : Bool}, +e: {O.a1.oid.content.pick(ok, arcs) == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}) -> {O.Asn1.oid_of_content(o) == Done{arcs} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}:
  match ok:
    case False{}:
      Empty.absurd({O.Asn1.oid_of_content(o) == Done{arcs} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}, po.fd(E.Asn1BadOid{}, o, e))
    case True{}:
      match arcs:
        case Con{+x, Con{+y, +rest}}:
          +ss = O.a1.oid.to_subids(Con{x, Con{y, rest}})
          +hva = AN.an.and_l(O.a1.oid.valid2(x, y), O.a1.oid.small(ss), hv)
          +hsm = AN.an.and_r(O.a1.oid.valid2(x, y), O.a1.oid.small(ss), hv)
          +sb = O.a1.oid.subids(ss)
          %Equal.cong(Result<&2, &2, E.Asn1Error, B.Octets>, B.Octets, z => po.od(z), Done{B.Octets.of_list(sb)}, Done{o}, e) : {O.Asn1.oid_of_content(_) == Done{Con{x, Con{y, rest}}} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}
          %Equal.trans(List<&2, U32>, sb, B.mask(sb), B.Octets.to_list(B.Octets.of_list(sb)), Equal.sym(List<&2, U32>, B.mask(sb), sb, po.fix_subids(ss)), Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(sb)), B.mask(sb), AL.al.to_of(sb))) : {O.a1.oid.arcs(O.a1.oid.read(List.length(&2, U32, _), Nu.a1.r128(_, True{}, Nu.a1.max_octets(), 0n))) == Done{Con{x, Con{y, rest}}} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}
          %Equal.sym(Maybe<&2, List<&2, Nat>>, O.a1.oid.read(List.length(&2, U32, sb), Nu.a1.r128(sb, True{}, Nu.a1.max_octets(), 0n)), Some{ss}, po.read(ss, List.length(&2, U32, sb), AN.an.le_zero(List.length(&2, Nat, rest)), UL.nat_le_refl(List.length(&2, U32, sb)), hsm)) : {O.a1.oid.arcs(_) == Done{Con{x, Con{y, rest}}} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}
          po.split(x, y, rest, hva)
        case Con{x, Nil{}}:
          Empty.absurd({O.Asn1.oid_of_content(o) == Done{Con{x, Nil{}}} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}, AN.an.ft(hv))
        case Nil{}:
          Empty.absurd({O.Asn1.oid_of_content(o) == Done{Nil{}} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}, AN.an.ft(hv))

# OBJECT IDENTIFIER contents read are canonical: the arcs read are written
# back to the same octets

type PoNum is Data:
  PoNum{bytes: List<&2, U32>, ok: Bool}

type PoArcs is Data:
  PoArcs{subids: List<&2, Nat>, ok: Bool}

def po.nb(p: PoNum) -> List<&2, U32>:
  match p:
    case PoNum{b, o}:
      b

def po.no(p: PoNum) -> Bool:
  match p:
    case PoNum{b, o}:
      o

def po.ab(p: PoArcs) -> List<&2, Nat>:
  match p:
    case PoArcs{b, o}:
      b

def po.ao(p: PoArcs) -> Bool:
  match p:
    case PoArcs{b, o}:
      o

def po.pc(+y: U32, p: PoNum) -> PoNum:
  match p:
    case PoNum{b, o}:
      PoNum{Con{y, b}, o}

# what a number read from xs (within k octets) says of xs
def po.mres(m: Maybe<&2, Nu.A1Num>, xs: List<&2, U32>, k: Nat) -> Type:
  match m:
    case None{}:
      Unit
    case Some{Nu.A1Num{v, u, r}}:
      {PoNum{List.append(&2, U32, u, r), Nat.is_le(List.length(&2, U32, u), k)} == PoNum{xs, True{}} : PoNum}

def po.mres_cons(+y: U32, m: Maybe<&2, Nu.A1Num>, +t: List<&2, U32>, +j: Nat, h: po.mres(m, t, j)) -> po.mres(Nu.a1.num_cons(y, m), Con{y, t}, 1n+j):
  match m:
    case None{}:
      Unit{}
    case Some{Nu.A1Num{v, +u, +r}}:
      +h2 : {PoNum{List.append(&2, U32, u, r), Nat.is_le(List.length(&2, U32, u), j)} == PoNum{t, True{}} : PoNum} = h
      Equal.cong(PoNum, PoNum, z => po.pc(y, z), PoNum{List.append(&2, U32, u, r), Nat.is_le(List.length(&2, U32, u), j)}, PoNum{t, True{}}, h2)

def po.r128_m(xs: List<&2, U32>, more: Bool, k: Nat, +acc: Nat) -> po.mres(Nu.a1.r128(xs, more, k, acc), xs, k):
  match xs more k:
    case Nil{} False{} +k2:
      %Equal.sym(Bool, Nat.is_le(0n, k2), True{}, AN.an.le_zero(k2)) : {PoNum{Nil{}, _} == PoNum{Nil{}, True{}} : PoNum}
      {==}
    case Nil{} True{} _:
      Unit{}
    case Con{+y, +t} False{} +k2:
      %Equal.sym(Bool, Nat.is_le(0n, k2), True{}, AN.an.le_zero(k2)) : {PoNum{Con{y, t}, _} == PoNum{Con{y, t}, True{}} : PoNum}
      {==}
    case Con{y, t} True{} 0n:
      Unit{}
    case Con{+y, +t} True{} 1n+ +j:
      +vv = U32.to_nat(y)
      +ge = Nat.is_le(128n, vv)
      +acc2 = Nat.add(Nat.mul(acc, 128n), Nat.sub(vv, Bool.pick(Nat, ge, 128n, 0n)))
      po.mres_cons(y, Nu.a1.r128(t, ge, j, acc2), t, j, po.r128_m(t, ge, j, acc2))

# what subidentifiers read from xs say of xs
def po.rres(m: Maybe<&2, List<&2, Nat>>, xs: List<&2, U32>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{ss}:
      {PoNum{O.a1.oid.subids(ss), O.a1.oid.small(ss)} == PoNum{xs, True{}} : PoNum}

def po.one_m(ok: Bool, +s: Nat, +u: List<&2, U32>, rest: List<&2, U32>, more: Maybe<&2, List<&2, Nat>>, +xs: List<&2, U32>, +hok: {Nu.a1.leq(Nu.a1.b128(s), u) == ok : Bool}, +hm: {PoNum{List.append(&2, U32, u, rest), Nat.is_le(List.length(&2, U32, u), 6n)} == PoNum{xs, True{}} : PoNum}, ih: po.rres(more, rest)) -> po.rres(O.a1.oid.one(ok, s, rest, more), xs):
  match ok rest:
    case False{} _:
      Unit{}
    case True{} Nil{}:
      +eb = AU.au.leq_sound(Nu.a1.b128(s), u, hok)
      +hb = Equal.cong(PoNum, List<&2, U32>, z => po.nb(z), PoNum{List.append(&2, U32, u, Nil{}), Nat.is_le(List.length(&2, U32, u), 6n)}, PoNum{xs, True{}}, hm)
      +ho = Equal.cong(PoNum, Bool, z => po.no(z), PoNum{List.append(&2, U32, u, Nil{}), Nat.is_le(List.length(&2, U32, u), 6n)}, PoNum{xs, True{}}, hm)
      %Equal.sym(List<&2, U32>, Nu.a1.b128(s), u, eb) : {PoNum{List.append(&2, U32, _, Nil{}), Bool.and(Nat.is_le(List.length(&2, U32, _), 6n), True{})} == PoNum{xs, True{}} : PoNum}
      %Equal.sym(List<&2, U32>, List.append(&2, U32, u, Nil{}), xs, hb) : {PoNum{_, Bool.and(Nat.is_le(List.length(&2, U32, u), 6n), True{})} == PoNum{xs, True{}} : PoNum}
      %Equal.sym(Bool, Nat.is_le(List.length(&2, U32, u), 6n), True{}, ho) : {PoNum{xs, Bool.and(_, True{})} == PoNum{xs, True{}} : PoNum}
      {==}
    case True{} Con{+y, +t}:
      match more:
        case None{}:
          Unit{}
        case Some{+ss}:
          +ih2 : {PoNum{O.a1.oid.subids(ss), O.a1.oid.small(ss)} == PoNum{Con{y, t}, True{}} : PoNum} = ih
          +eb = AU.au.leq_sound(Nu.a1.b128(s), u, hok)
          +hb = Equal.cong(PoNum, List<&2, U32>, z => po.nb(z), PoNum{List.append(&2, U32, u, Con{y, t}), Nat.is_le(List.length(&2, U32, u), 6n)}, PoNum{xs, True{}}, hm)
          +ho = Equal.cong(PoNum, Bool, z => po.no(z), PoNum{List.append(&2, U32, u, Con{y, t}), Nat.is_le(List.length(&2, U32, u), 6n)}, PoNum{xs, True{}}, hm)
          +ib = Equal.cong(PoNum, List<&2, U32>, z => po.nb(z), PoNum{O.a1.oid.subids(ss), O.a1.oid.small(ss)}, PoNum{Con{y, t}, True{}}, ih2)
          +io = Equal.cong(PoNum, Bool, z => po.no(z), PoNum{O.a1.oid.subids(ss), O.a1.oid.small(ss)}, PoNum{Con{y, t}, True{}}, ih2)
          %Equal.sym(List<&2, U32>, Nu.a1.b128(s), u, eb) : {PoNum{List.append(&2, U32, _, O.a1.oid.subids(ss)), Bool.and(Nat.is_le(List.length(&2, U32, _), 6n), O.a1.oid.small(ss))} == PoNum{xs, True{}} : PoNum}
          %Equal.sym(List<&2, U32>, O.a1.oid.subids(ss), Con{y, t}, ib) : {PoNum{List.append(&2, U32, u, _), Bool.and(Nat.is_le(List.length(&2, U32, u), 6n), O.a1.oid.small(ss))} == PoNum{xs, True{}} : PoNum}
          %Equal.sym(List<&2, U32>, List.append(&2, U32, u, Con{y, t}), xs, hb) : {PoNum{_, Bool.and(Nat.is_le(List.length(&2, U32, u), 6n), O.a1.oid.small(ss))} == PoNum{xs, True{}} : PoNum}
          %Equal.sym(Bool, Nat.is_le(List.length(&2, U32, u), 6n), True{}, ho) : {PoNum{xs, Bool.and(_, O.a1.oid.small(ss))} == PoNum{xs, True{}} : PoNum}
          %Equal.sym(Bool, O.a1.oid.small(ss), True{}, io) : {PoNum{xs, _} == PoNum{xs, True{}} : PoNum}
          {==}

def po.read_m(f: Nat, m: Maybe<&2, Nu.A1Num>, +xs: List<&2, U32>, hm: po.mres(m, xs, 6n)) -> po.rres(O.a1.oid.read(f, m), xs):
  match f m:
    case _ None{}:
      Unit{}
    case 0n Some{x}:
      Unit{}
    case 1n+ +g Some{Nu.A1Num{+s, +u, +rest}}:
      +hm2 : {PoNum{List.append(&2, U32, u, rest), Nat.is_le(List.length(&2, U32, u), 6n)} == PoNum{xs, True{}} : PoNum} = hm
      +more = O.a1.oid.read(g, Nu.a1.r128(rest, True{}, Nu.a1.max_octets(), 0n))
      po.one_m(Nu.a1.leq(Nu.a1.b128(s), u), s, u, rest, more, xs, {==}, hm2, po.read_m(g, Nu.a1.r128(rest, True{}, Nu.a1.max_octets(), 0n), rest, po.r128_m(rest, True{}, Nu.a1.max_octets(), 0n)))

# a <= b: a + (b - a) == b
def po.add_sub(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.add(a, Nat.sub(b, a)) == b : Nat}:
  match a b:
    case 0n _:
      AN.an.sub_zero(b)
    case 1n+p 0n:
      Empty.absurd({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, AN.an.ft(h))
    case 1n+p 1n+q:
      %po.add_sub(p, q, h) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
      {==}

# b <= s < b + 40 (b = 40): s - 40 < 40
def po.sub_lt(+s: Nat, +h: {Nat.is_lt(s, 80n) == True{} : Bool}, +g: {Nat.is_le(40n, s) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(s, 40n), 40n) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(40n, Nat.sub(s, 40n)), s, po.add_sub(40n, s, g)) : {Nat.is_lt(_, 80n) == True{} : Bool}
  h

def po.le_of_nlt(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(b, a), Bool.not(Nat.is_lt(a, b)), True{}, PN.pn.le_not_lt(b, a), Equal.cong(Bool, Bool, z => Bool.not(z), Nat.is_lt(a, b), False{}, h))

# the first subidentifier's split, folded back, and the arcs' validity
def po.split_ok(lt40: Bool, lt80: Bool, +s: Nat, +rest: List<&2, Nat>, +h40: {Nat.is_lt(s, 40n) == lt40 : Bool}, +h80: {Nat.is_lt(s, 80n) == lt80 : Bool}) -> {PoArcs{O.a1.oid.to_subids(O.a1.oid.split2(lt40, lt80, s, rest)), O.a1.oid.valid(O.a1.oid.split2(lt40, lt80, s, rest))} == PoArcs{Con{s, rest}, True{}} : PoArcs}:
  match lt40 lt80:
    case True{} _:
      %Equal.sym(Bool, Nat.is_lt(s, 40n), True{}, h40) : {PoArcs{Con{s, rest}, _} == PoArcs{Con{s, rest}, True{}} : PoArcs}
      {==}
    case False{} True{}:
      +g = po.le_of_nlt(s, 40n, h40)
      %Equal.sym(Nat, Nat.add(40n, Nat.sub(s, 40n)), s, po.add_sub(40n, s, g)) : {PoArcs{Con{_, rest}, Nat.is_lt(Nat.sub(s, 40n), 40n)} == PoArcs{Con{s, rest}, True{}} : PoArcs}
      %Equal.sym(Bool, Nat.is_lt(Nat.sub(s, 40n), 40n), True{}, po.sub_lt(s, h80, g)) : {PoArcs{Con{s, rest}, _} == PoArcs{Con{s, rest}, True{}} : PoArcs}
      {==}
    case False{} False{}:
      +g = po.le_of_nlt(s, 80n, h80)
      %Equal.sym(Nat, Nat.add(80n, Nat.sub(s, 80n)), s, po.add_sub(80n, s, g)) : {PoArcs{Con{_, rest}, True{}} == PoArcs{Con{s, rest}, True{}} : PoArcs}
      {==}

def po.rdisc(r: Result<&2, &2, E.Asn1Error, List<&2, Nat>>) -> Type:
  match r:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def po.fd2(-x: E.Asn1Error, -y: List<&2, Nat>, e: {Fail{x} == Done{y} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}) -> Empty:
  %e : po.rdisc(_)
  Unit{}

def po.rval(r: Result<&2, &2, E.Asn1Error, List<&2, Nat>>, d: List<&2, Nat>) -> List<&2, Nat>:
  match r:
    case Fail{x}:
      d
    case Done{v}:
      v

def po.canon_m(mr: Maybe<&2, List<&2, Nat>>, +xs: List<&2, U32>, -arcs: List<&2, Nat>, hr: po.rres(mr, xs), +e: {O.a1.oid.arcs(mr) == Done{arcs} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}) -> {O.Asn1.oid_content(arcs) == Done{B.Octets.of_list(xs)} : Result<&2, &2, E.Asn1Error, B.Octets>}:
  match mr:
    case None{}:
      Empty.absurd({O.Asn1.oid_content(arcs) == Done{B.Octets.of_list(xs)} : Result<&2, &2, E.Asn1Error, B.Octets>}, po.fd2(E.Asn1BadOid{}, arcs, e))
    case Some{Nil{}}:
      Empty.absurd({O.Asn1.oid_content(arcs) == Done{B.Octets.of_list(xs)} : Result<&2, &2, E.Asn1Error, B.Octets>}, po.fd2(E.Asn1BadOid{}, arcs, e))
    case Some{Con{+s, +rest}}:
      +hr2 : {PoNum{O.a1.oid.subids(Con{s, rest}), O.a1.oid.small(Con{s, rest})} == PoNum{xs, True{}} : PoNum} = hr
      +a0 = O.a1.oid.split2(Nat.is_lt(s, 40n), Nat.is_lt(s, 80n), s, rest)
      +ea = Equal.cong(Result<&2, &2, E.Asn1Error, List<&2, Nat>>, List<&2, Nat>, z => po.rval(z, a0), Done{a0}, Done{arcs}, e)
      %ea : {O.Asn1.oid_content(_) == Done{B.Octets.of_list(xs)} : Result<&2, &2, E.Asn1Error, B.Octets>}
      +hs = po.split_ok(Nat.is_lt(s, 40n), Nat.is_lt(s, 80n), s, rest, {==}, {==})
      +hsub = Equal.cong(PoArcs, List<&2, Nat>, z => po.ab(z), PoArcs{O.a1.oid.to_subids(a0), O.a1.oid.valid(a0)}, PoArcs{Con{s, rest}, True{}}, hs)
      +hval = Equal.cong(PoArcs, Bool, z => po.ao(z), PoArcs{O.a1.oid.to_subids(a0), O.a1.oid.valid(a0)}, PoArcs{Con{s, rest}, True{}}, hs)
      +hb = Equal.cong(PoNum, List<&2, U32>, z => po.nb(z), PoNum{O.a1.oid.subids(Con{s, rest}), O.a1.oid.small(Con{s, rest})}, PoNum{xs, True{}}, hr2)
      +ho = Equal.cong(PoNum, Bool, z => po.no(z), PoNum{O.a1.oid.subids(Con{s, rest}), O.a1.oid.small(Con{s, rest})}, PoNum{xs, True{}}, hr2)
      %Equal.sym(Bool, O.a1.oid.valid(a0), True{}, hval) : {O.a1.oid.content.pick(Bool.and(_, O.a1.oid.small(O.a1.oid.to_subids(a0))), a0) == Done{B.Octets.of_list(xs)} : Result<&2, &2, E.Asn1Error, B.Octets>}
      %Equal.sym(List<&2, Nat>, O.a1.oid.to_subids(a0), Con{s, rest}, hsub) : {O.a1.oid.content.pick(O.a1.oid.small(_), a0) == Done{B.Octets.of_list(xs)} : Result<&2, &2, E.Asn1Error, B.Octets>}
      %Equal.sym(Bool, O.a1.oid.small(Con{s, rest}), True{}, ho) : {O.a1.oid.content.pick(_, a0) == Done{B.Octets.of_list(xs)} : Result<&2, &2, E.Asn1Error, B.Octets>}
      %Equal.sym(List<&2, Nat>, O.a1.oid.to_subids(a0), Con{s, rest}, hsub) : {Done{B.Octets.of_list(O.a1.oid.subids(_))} == Done{B.Octets.of_list(xs)} : Result<&2, &2, E.Asn1Error, B.Octets>}
      %Equal.sym(List<&2, U32>, O.a1.oid.subids(Con{s, rest}), xs, hb) : {Done{B.Octets.of_list(_)} == Done{B.Octets.of_list(xs)} : Result<&2, &2, E.Asn1Error, B.Octets>}
      {==}

# contents read as arcs are the octets those arcs are written as
def po.canonical(+o: B.Octets, -arcs: List<&2, Nat>, +e: {O.Asn1.oid_of_content(o) == Done{arcs} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}) -> {O.Asn1.oid_content(arcs) == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}:
  +xs = B.Octets.to_list(o)
  +m0 = Nu.a1.r128(xs, True{}, Nu.a1.max_octets(), 0n)
  %AL.al.of_to(o) : {O.Asn1.oid_content(arcs) == Done{_} : Result<&2, &2, E.Asn1Error, B.Octets>}
  po.canon_m(O.a1.oid.read(List.length(&2, U32, xs), m0), xs, arcs, po.read_m(List.length(&2, U32, xs), m0, xs, po.r128_m(xs, True{}, Nu.a1.max_octets(), 0n)), e)
