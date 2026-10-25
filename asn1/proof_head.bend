# Proof helpers for bend-osdev-asn1: the header of an element the encoder
# wrote (identifier octets, then length octets) reads back as the tag, the
# form and the contents octets written, under any rules.
import Base
import ../bytes/bytes.bend as B
import ./number.bend as Nu
import ./tag.bend as T
import ./length.bend as L
import ./rules.bend as R
import ./encode.bend as En
import ./asn1.bend as A
import ./proof_nat.bend as AN
import ./proof_list.bend as AL
import ./proof_u32.bend as AU
import ./proof_byte.bend as AB
import ./proof_num.bend as PN
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF_order.bend as UOP

def ph.idb_low(c: T.Asn1Class, cons: Bool, +n: Nat, +hn: {Nat.is_lt(n, 31n) == True{} : Bool}) -> {T.a1.id_bytes(c, cons, n) == [Nu.a1.b(T.a1.id_octet(c, cons, n))] : List<&2, U32>}:
  %Equal.sym(Bool, Nat.is_lt(n, 31n), True{}, hn) : {T.a1.id_pick(_, c, cons, n) == [Nu.a1.b(T.a1.id_octet(c, cons, n))] : List<&2, U32>}
  {==}

def ph.idb_high(c: T.Asn1Class, cons: Bool, +n: Nat, +hn: {Nat.is_lt(n, 31n) == False{} : Bool}) -> {T.a1.id_bytes(c, cons, n) == Con{Nu.a1.b(T.a1.id_octet(c, cons, 31n)), Nu.a1.b128(n)} : List<&2, U32>}:
  %Equal.sym(Bool, Nat.is_lt(n, 31n), False{}, hn) : {T.a1.id_pick(_, c, cons, n) == Con{Nu.a1.b(T.a1.id_octet(c, cons, 31n)), Nu.a1.b128(n)} : List<&2, U32>}
  {==}

# a low tag number's identifier octet reads back
def ph.id_low(+r: R.Asn1Rules, +c: T.Asn1Class, +cons: Bool, +n: Nat, +rest: List<&2, U32>, +hn: {Nat.is_lt(n, 31n) == True{} : Bool}) -> {A.a1.head0(r, List.append(&2, U32, T.a1.id_bytes(c, cons, n), rest)) == A.a1.head.res(En.a1.is_univ0(c, n), r, c, cons, n, rest) : A.A1Head}:
  +x = Nu.a1.b(T.a1.id_octet(c, cons, n))
  +want : A.A1Head = A.a1.head.res(En.a1.is_univ0(c, n), r, c, cons, n, rest)
  +e1 = ph.idb_low(c, cons, n, hn)
  %Equal.sym(List<&2, U32>, T.a1.id_bytes(c, cons, n), [x], e1) : {A.a1.head0(r, List.append(&2, U32, _, rest)) == want : A.A1Head}
  %Equal.sym(T.A1Id1, T.a1.id1(U32.to_nat(x)), T.A1Id1{c, cons, n}, AB.ab.id1(c, cons, n, UO.nat_lt_le_trans(n, 31n, 32n, hn, {==}))) : {A.a1.head.id(r, _, x, rest) == want : A.A1Head}
  %Equal.sym(Bool, Nat.is_eq(n, 31n), False{}, AN.an.lt_ne(n, 31n, hn)) : {A.a1.head.hi(_, r, c, cons, n, x, rest) == want : A.A1Head}
  %Equal.sym(List<&2, U32>, T.a1.id_bytes(c, cons, n), [x], e1) : {A.a1.head.tag2(Nu.a1.leq(_, [x]), r, c, cons, n, rest) == want : A.A1Head}
  %Equal.sym(Bool, Nu.a1.leq([x], [x]), True{}, AU.au.leq_refl([x])) : {A.a1.head.tag2(_, r, c, cons, n, rest) == want : A.A1Head}
  {==}

# a high tag number's identifier octets read back
def ph.id_high(+r: R.Asn1Rules, +c: T.Asn1Class, +cons: Bool, +n: Nat, +rest: List<&2, U32>, +hn: {Nat.is_lt(n, 31n) == False{} : Bool}, +hk: {Nat.is_le(List.length(&2, U32, Nu.a1.b128(n)), 6n) == True{} : Bool}) -> {A.a1.head0(r, List.append(&2, U32, T.a1.id_bytes(c, cons, n), rest)) == A.a1.head.res(En.a1.is_univ0(c, n), r, c, cons, n, rest) : A.A1Head}:
  +x = Nu.a1.b(T.a1.id_octet(c, cons, 31n))
  +ids : List<&2, U32> = Con{x, Nu.a1.b128(n)}
  +want : A.A1Head = A.a1.head.res(En.a1.is_univ0(c, n), r, c, cons, n, rest)
  +e1 = ph.idb_high(c, cons, n, hn)
  %Equal.sym(List<&2, U32>, T.a1.id_bytes(c, cons, n), ids, e1) : {A.a1.head0(r, List.append(&2, U32, _, rest)) == want : A.A1Head}
  %Equal.sym(T.A1Id1, T.a1.id1(U32.to_nat(x)), T.A1Id1{c, cons, 31n}, AB.ab.id1(c, cons, 31n, {==})) : {A.a1.head.id(r, _, x, List.append(&2, U32, Nu.a1.b128(n), rest)) == want : A.A1Head}
  %Equal.sym(Maybe<&2, Nu.A1Num>, Nu.a1.r128(List.append(&2, U32, Nu.a1.b128(n), rest), True{}, 6n, 0n), Some{Nu.A1Num{n, Nu.a1.b128(n), rest}}, PN.pn.r128_b128(n, rest, 6n, hk)) : {A.a1.head.num(r, c, cons, x, _) == want : A.A1Head}
  %Equal.sym(List<&2, U32>, T.a1.id_bytes(c, cons, n), ids, e1) : {A.a1.head.tag2(Nu.a1.leq(_, ids), r, c, cons, n, rest) == want : A.A1Head}
  %Equal.sym(Bool, Nu.a1.leq(ids, ids), True{}, AU.au.leq_refl(ids)) : {A.a1.head.tag2(_, r, c, cons, n, rest) == want : A.A1Head}
  {==}

def ph.id.go(lt: Bool, +r: R.Asn1Rules, +c: T.Asn1Class, +cons: Bool, +n: Nat, +rest: List<&2, U32>, +hl: {Nat.is_lt(n, 31n) == lt : Bool}, +hid: {T.a1.id_ok(n) == True{} : Bool}) -> {A.a1.head0(r, List.append(&2, U32, T.a1.id_bytes(c, cons, n), rest)) == A.a1.head.res(En.a1.is_univ0(c, n), r, c, cons, n, rest) : A.A1Head}:
  match lt:
    case True{}:
      ph.id_low(r, c, cons, n, rest, hl)
    case False{}:
      ph.id_high(r, c, cons, n, rest, hl, Equal.trans(Bool, Nat.is_le(List.length(&2, U32, Nu.a1.b128(n)), 6n), T.a1.id_ok(n), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, Nat.is_le(List.length(&2, U32, Nu.a1.b128(n)), 6n)), False{}, Nat.is_lt(n, 31n), Equal.sym(Bool, Nat.is_lt(n, 31n), False{}, hl)), hid))

# the identifier octets of any tag read back
def ph.id(+r: R.Asn1Rules, +c: T.Asn1Class, +cons: Bool, +n: Nat, +rest: List<&2, U32>, +hid: {T.a1.id_ok(n) == True{} : Bool}) -> {A.a1.head0(r, List.append(&2, U32, T.a1.id_bytes(c, cons, n), rest)) == A.a1.head.res(En.a1.is_univ0(c, n), r, c, cons, n, rest) : A.A1Head}:
  ph.id.go(Nat.is_lt(n, 31n), r, c, cons, n, rest, {==}, hid)

def ph.when_t(m: Bool) -> {R.a1.when(m, True{}) == True{} : Bool}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

# an element's header, as the encoder writes it, reads back (the contents
# then taken as cs, by a1.head.fit)
def ph.head_tlv(+r: R.Asn1Rules, +c: T.Asn1Class, +cons: Bool, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +hu: {En.a1.is_univ0(c, n) == False{} : Bool}, +hid: {T.a1.id_ok(n) == True{} : Bool}, +hok: {L.a1.len_ok(List.length(&2, U32, cs)) == True{} : Bool}) -> {A.a1.head0(r, En.a1.tlv(c, cons, n, cs, rest)) == A.a1.head.fit(True{}, T.Asn1Tag{c, n}, cons, List.length(&2, U32, cs), List.append(&2, U32, cs, rest)) : A.A1Head}:
  +l = List.length(&2, U32, cs)
  +lb = L.a1.len_bytes(l)
  +t2 = List.append(&2, U32, cs, rest)
  +t1 = List.append(&2, U32, lb, t2)
  +want : A.A1Head = A.a1.head.fit(True{}, T.Asn1Tag{c, n}, cons, l, t2)
  %Equal.sym(A.A1Head, A.a1.head0(r, List.append(&2, U32, T.a1.id_bytes(c, cons, n), t1)), A.a1.head.res(En.a1.is_univ0(c, n), r, c, cons, n, t1), ph.id(r, c, cons, n, t1, hid)) : {_ == want : A.A1Head}
  %Equal.sym(Bool, En.a1.is_univ0(c, n), False{}, hu) : {A.a1.head.res(_, r, c, cons, n, t1) == want : A.A1Head}
  %Equal.sym(L.A1Len, L.a1.len.read(t1), L.A1LDef{l, lb, t2}, PN.pn.len_read(l, t2, hok)) : {A.a1.head.len(r, T.Asn1Tag{c, n}, cons, _) == want : A.A1Head}
  %Equal.sym(Bool, Nu.a1.leq(lb, lb), True{}, AU.au.leq_refl(lb)) : {A.a1.head.min(R.a1.when(R.Asn1Rules.min_length(r), Bool.and(L.a1.len_ok(l), _)), T.Asn1Tag{c, n}, cons, l, t2) == want : A.A1Head}
  %Equal.sym(Bool, L.a1.len_ok(l), True{}, hok) : {A.a1.head.min(R.a1.when(R.Asn1Rules.min_length(r), Bool.and(_, True{})), T.Asn1Tag{c, n}, cons, l, t2) == want : A.A1Head}
  %Equal.sym(Bool, R.a1.when(R.Asn1Rules.min_length(r), True{}), True{}, ph.when_t(R.Asn1Rules.min_length(r))) : {A.a1.head.min(_, T.Asn1Tag{c, n}, cons, l, t2) == want : A.A1Head}
  +hle = Equal.trans(Bool, Nat.is_le(l, List.length(&2, U32, t2)), Nat.is_le(l, Nat.add(l, List.length(&2, U32, rest))), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(l, z), List.length(&2, U32, t2), Nat.add(l, List.length(&2, U32, rest)), AL.al.app_len(cs, rest)), UO.nat_le_add_r(l, List.length(&2, U32, rest)))
  %Equal.sym(Bool, Nat.is_le(l, List.length(&2, U32, t2)), True{}, hle) : {A.a1.head.fit(_, T.Asn1Tag{c, n}, cons, l, t2) == want : A.A1Head}
  {==}

def ph.fit_prim(+t: T.Asn1Tag, +cs: List<&2, U32>, +rest: List<&2, U32>) -> {A.a1.head.fit(True{}, t, False{}, List.length(&2, U32, cs), List.append(&2, U32, cs, rest)) == A.A1HPrim{t, cs, rest} : A.A1Head}:
  %Equal.sym(List<&2, U32>, B.take(List.length(&2, U32, cs), List.append(&2, U32, cs, rest)), cs, AL.al.take_app(cs, rest)) : {A.A1HPrim{t, _, B.drop(List.length(&2, U32, cs), List.append(&2, U32, cs, rest))} == A.A1HPrim{t, cs, rest} : A.A1Head}
  %Equal.sym(List<&2, U32>, B.drop(List.length(&2, U32, cs), List.append(&2, U32, cs, rest)), rest, AL.al.drop_app(cs, rest)) : {A.A1HPrim{t, cs, _} == A.A1HPrim{t, cs, rest} : A.A1Head}
  {==}

def ph.fit_def(+t: T.Asn1Tag, +cs: List<&2, U32>, +rest: List<&2, U32>) -> {A.a1.head.fit(True{}, t, True{}, List.length(&2, U32, cs), List.append(&2, U32, cs, rest)) == A.A1HDef{t, cs, rest} : A.A1Head}:
  %Equal.sym(List<&2, U32>, B.take(List.length(&2, U32, cs), List.append(&2, U32, cs, rest)), cs, AL.al.take_app(cs, rest)) : {A.A1HDef{t, _, B.drop(List.length(&2, U32, cs), List.append(&2, U32, cs, rest))} == A.A1HDef{t, cs, rest} : A.A1Head}
  %Equal.sym(List<&2, U32>, B.drop(List.length(&2, U32, cs), List.append(&2, U32, cs, rest)), rest, AL.al.drop_app(cs, rest)) : {A.A1HDef{t, cs, _} == A.A1HDef{t, cs, rest} : A.A1Head}
  {==}

def ph.head0_prim(+r: R.Asn1Rules, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +hu: {En.a1.is_univ0(c, n) == False{} : Bool}, +hid: {T.a1.id_ok(n) == True{} : Bool}, +hok: {L.a1.len_ok(List.length(&2, U32, cs)) == True{} : Bool}) -> {A.a1.head0(r, En.a1.tlv(c, False{}, n, cs, rest)) == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}:
  Equal.trans(A.A1Head, A.a1.head0(r, En.a1.tlv(c, False{}, n, cs, rest)), A.a1.head.fit(True{}, T.Asn1Tag{c, n}, False{}, List.length(&2, U32, cs), List.append(&2, U32, cs, rest)), A.A1HPrim{T.Asn1Tag{c, n}, cs, rest}, ph.head_tlv(r, c, False{}, n, cs, rest, hu, hid, hok), ph.fit_prim(T.Asn1Tag{c, n}, cs, rest))

def ph.head0_def(+r: R.Asn1Rules, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +hu: {En.a1.is_univ0(c, n) == False{} : Bool}, +hid: {T.a1.id_ok(n) == True{} : Bool}, +hok: {L.a1.len_ok(List.length(&2, U32, cs)) == True{} : Bool}) -> {A.a1.head0(r, En.a1.tlv(c, True{}, n, cs, rest)) == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}:
  Equal.trans(A.A1Head, A.a1.head0(r, En.a1.tlv(c, True{}, n, cs, rest)), A.a1.head.fit(True{}, T.Asn1Tag{c, n}, True{}, List.length(&2, U32, cs), List.append(&2, U32, cs, rest)), A.A1HDef{T.Asn1Tag{c, n}, cs, rest}, ph.head_tlv(r, c, True{}, n, cs, rest, hu, hid, hok), ph.fit_def(T.Asn1Tag{c, n}, cs, rest))

# a header of either form
def ph.mk(cons: Bool, t: T.Asn1Tag, cs: List<&2, U32>, rest: List<&2, U32>) -> A.A1Head:
  match cons:
    case True{}:
      A.A1HDef{t, cs, rest}
    case False{}:
      A.A1HPrim{t, cs, rest}

# The canonical check passes on the encoder's octets

# an element's octets: the octets before its contents, then the contents
def ph.hdr_split(+c: T.Asn1Class, +cons: Bool, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>) -> {En.a1.tlv(c, cons, n, cs, rest) == List.append(&2, U32, A.a1.hdr(c, cons, n, List.length(&2, U32, cs)), List.append(&2, U32, cs, rest)) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, T.a1.id_bytes(c, cons, n), L.a1.len_bytes(List.length(&2, U32, cs))), List.append(&2, U32, cs, rest)), En.a1.tlv(c, cons, n, cs, rest), AL.al.app_assoc(T.a1.id_bytes(c, cons, n), L.a1.len_bytes(List.length(&2, U32, cs)), List.append(&2, U32, cs, rest)))

def ph.canon_ok(+c: T.Asn1Class, +cons: Bool, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +hu: {En.a1.is_univ0(c, n) == False{} : Bool}, +hid: {T.a1.id_ok(n) == True{} : Bool}, +hok: {L.a1.len_ok(List.length(&2, U32, cs)) == True{} : Bool}) -> {A.a1.canon.ok(c, cons, n, List.length(&2, U32, cs), En.a1.tlv(c, cons, n, cs, rest)) == True{} : Bool}:
  +l = List.length(&2, U32, cs)
  +hd = A.a1.hdr(c, cons, n, l)
  +k = List.length(&2, U32, hd)
  +y = List.append(&2, U32, cs, rest)
  +xs = List.append(&2, U32, hd, y)
  %Equal.sym(List<&2, U32>, En.a1.tlv(c, cons, n, cs, rest), xs, ph.hdr_split(c, cons, n, cs, rest)) : {A.a1.canon.ok(c, cons, n, l, _) == True{} : Bool}
  %Equal.sym(List<&2, U32>, B.take(k, xs), hd, AL.al.take_app(hd, y)) : {Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), Bool.and(L.a1.len_ok(l), Bool.and(Nu.a1.leq(hd, _), Nat.is_le(l, List.length(&2, U32, B.drop(k, xs))))))) == True{} : Bool}
  %Equal.sym(List<&2, U32>, B.drop(k, xs), y, AL.al.drop_app(hd, y)) : {Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), Bool.and(L.a1.len_ok(l), Bool.and(Nu.a1.leq(hd, hd), Nat.is_le(l, List.length(&2, U32, _)))))) == True{} : Bool}
  %Equal.sym(Bool, En.a1.is_univ0(c, n), False{}, hu) : {Bool.and(Bool.not(_), Bool.and(T.a1.id_ok(n), Bool.and(L.a1.len_ok(l), Bool.and(Nu.a1.leq(hd, hd), Nat.is_le(l, List.length(&2, U32, y)))))) == True{} : Bool}
  %Equal.sym(Bool, T.a1.id_ok(n), True{}, hid) : {Bool.and(_, Bool.and(L.a1.len_ok(l), Bool.and(Nu.a1.leq(hd, hd), Nat.is_le(l, List.length(&2, U32, y))))) == True{} : Bool}
  %Equal.sym(Bool, L.a1.len_ok(l), True{}, hok) : {Bool.and(_, Bool.and(Nu.a1.leq(hd, hd), Nat.is_le(l, List.length(&2, U32, y)))) == True{} : Bool}
  %Equal.sym(Bool, Nu.a1.leq(hd, hd), True{}, AU.au.leq_refl(hd)) : {Bool.and(_, Nat.is_le(l, List.length(&2, U32, y))) == True{} : Bool}
  %Equal.sym(Nat, List.length(&2, U32, y), Nat.add(l, List.length(&2, U32, rest)), AL.al.app_len(cs, rest)) : {Nat.is_le(l, _) == True{} : Bool}
  UO.nat_le_add_r(l, List.length(&2, U32, rest))

def ph.indef_off_keep(a: Bool, +t: T.Asn1Tag, +cs: List<&2, U32>, +rest: List<&2, U32>, +cons: Bool) -> {A.a1.head.indef_off(a, ph.mk(cons, t, cs, rest)) == ph.mk(cons, t, cs, rest) : A.A1Head}:
  match a cons:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def ph.canon_prim(+c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +hu: {En.a1.is_univ0(c, n) == False{} : Bool}, +hid: {T.a1.id_ok(n) == True{} : Bool}, +hok: {L.a1.len_ok(List.length(&2, U32, cs)) == True{} : Bool}) -> {A.a1.canon(En.a1.tlv(c, False{}, n, cs, rest), A.A1HPrim{T.Asn1Tag{c, n}, cs, rest}) == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}:
  +l = List.length(&2, U32, cs)
  +hd = A.a1.hdr(c, False{}, n, l)
  +k = List.length(&2, U32, hd)
  +y = List.append(&2, U32, cs, rest)
  +x0 = En.a1.tlv(c, False{}, n, cs, rest)
  %Equal.sym(Bool, A.a1.canon.ok(c, False{}, n, l, x0), True{}, ph.canon_ok(c, False{}, n, cs, rest, hu, hid, hok)) : {A.a1.canon.mk(_, T.Asn1Tag{c, n}, False{}, k, l, x0) == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}
  %Equal.sym(List<&2, U32>, x0, List.append(&2, U32, hd, y), ph.hdr_split(c, False{}, n, cs, rest)) : {A.A1HPrim{T.Asn1Tag{c, n}, B.take(l, B.drop(k, _)), B.drop(l, B.drop(k, _))} == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}
  %Equal.sym(List<&2, U32>, B.drop(k, List.append(&2, U32, hd, y)), y, AL.al.drop_app(hd, y)) : {A.A1HPrim{T.Asn1Tag{c, n}, B.take(l, _), B.drop(l, _)} == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}
  %Equal.sym(List<&2, U32>, B.take(l, y), cs, AL.al.take_app(cs, rest)) : {A.A1HPrim{T.Asn1Tag{c, n}, _, B.drop(l, y)} == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}
  %Equal.sym(List<&2, U32>, B.drop(l, y), rest, AL.al.drop_app(cs, rest)) : {A.A1HPrim{T.Asn1Tag{c, n}, cs, _} == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}
  {==}

def ph.fin2_prim(m: Bool, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +hu: {En.a1.is_univ0(c, n) == False{} : Bool}, +hid: {T.a1.id_ok(n) == True{} : Bool}, +hok: {L.a1.len_ok(List.length(&2, U32, cs)) == True{} : Bool}) -> {A.a1.head.fin2(m, En.a1.tlv(c, False{}, n, cs, rest), A.A1HPrim{T.Asn1Tag{c, n}, cs, rest}) == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}:
  match m:
    case True{}:
      ph.canon_prim(c, n, cs, rest, hu, hid, hok)
    case False{}:
      {==}

def ph.fin_prim(+r: R.Asn1Rules, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +hu: {En.a1.is_univ0(c, n) == False{} : Bool}, +hid: {T.a1.id_ok(n) == True{} : Bool}, +hok: {L.a1.len_ok(List.length(&2, U32, cs)) == True{} : Bool}) -> {A.a1.head.fin(r, En.a1.tlv(c, False{}, n, cs, rest), A.a1.head0(r, En.a1.tlv(c, False{}, n, cs, rest))) == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}:
  +x0 = En.a1.tlv(c, False{}, n, cs, rest)
  %Equal.sym(A.A1Head, A.a1.head0(r, x0), A.A1HPrim{T.Asn1Tag{c, n}, cs, rest}, ph.head0_prim(r, c, n, cs, rest, hu, hid, hok)) : {A.a1.head.fin(r, x0, _) == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}
  %Equal.sym(A.A1Head, A.a1.head.indef_off(R.Asn1Rules.indefinite(r), ph.mk(False{}, T.Asn1Tag{c, n}, cs, rest)), ph.mk(False{}, T.Asn1Tag{c, n}, cs, rest), ph.indef_off_keep(R.Asn1Rules.indefinite(r), T.Asn1Tag{c, n}, cs, rest, False{})) : {A.a1.head.fin2(R.Asn1Rules.min_length(r), x0, _) == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}
  ph.fin2_prim(R.Asn1Rules.min_length(r), c, n, cs, rest, hu, hid, hok)

def ph.nend_prim(xs: List<&2, U32>, +t: T.Asn1Tag, +cs: List<&2, U32>, +rest: List<&2, U32>) -> {A.a1.head.nend(xs, A.A1HPrim{t, cs, rest}) == A.A1HPrim{t, cs, rest} : A.A1Head}:
  match xs:
    case Nil{}:
      {==}
    case Con{y, u}:
      {==}

# the header of an element the encoder wrote, under any rules
def ph.head_prim(+r: R.Asn1Rules, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +hu: {En.a1.is_univ0(c, n) == False{} : Bool}, +hid: {T.a1.id_ok(n) == True{} : Bool}, +hok: {L.a1.len_ok(List.length(&2, U32, cs)) == True{} : Bool}) -> {A.a1.head(r, En.a1.tlv(c, False{}, n, cs, rest)) == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}:
  +x0 = En.a1.tlv(c, False{}, n, cs, rest)
  +w : A.A1Head = A.A1HPrim{T.Asn1Tag{c, n}, cs, rest}
  %Equal.sym(A.A1Head, A.a1.head.fin(r, x0, A.a1.head0(r, x0)), w, ph.fin_prim(r, c, n, cs, rest, hu, hid, hok)) : {A.a1.head.nend(x0, _) == w : A.A1Head}
  ph.nend_prim(x0, T.Asn1Tag{c, n}, cs, rest)

def ph.canon_def(+c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +hu: {En.a1.is_univ0(c, n) == False{} : Bool}, +hid: {T.a1.id_ok(n) == True{} : Bool}, +hok: {L.a1.len_ok(List.length(&2, U32, cs)) == True{} : Bool}) -> {A.a1.canon(En.a1.tlv(c, True{}, n, cs, rest), A.A1HDef{T.Asn1Tag{c, n}, cs, rest}) == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}:
  +l = List.length(&2, U32, cs)
  +hd = A.a1.hdr(c, True{}, n, l)
  +k = List.length(&2, U32, hd)
  +y = List.append(&2, U32, cs, rest)
  +x0 = En.a1.tlv(c, True{}, n, cs, rest)
  %Equal.sym(Bool, A.a1.canon.ok(c, True{}, n, l, x0), True{}, ph.canon_ok(c, True{}, n, cs, rest, hu, hid, hok)) : {A.a1.canon.mk(_, T.Asn1Tag{c, n}, True{}, k, l, x0) == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}
  %Equal.sym(List<&2, U32>, x0, List.append(&2, U32, hd, y), ph.hdr_split(c, True{}, n, cs, rest)) : {A.A1HDef{T.Asn1Tag{c, n}, B.take(l, B.drop(k, _)), B.drop(l, B.drop(k, _))} == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}
  %Equal.sym(List<&2, U32>, B.drop(k, List.append(&2, U32, hd, y)), y, AL.al.drop_app(hd, y)) : {A.A1HDef{T.Asn1Tag{c, n}, B.take(l, _), B.drop(l, _)} == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}
  %Equal.sym(List<&2, U32>, B.take(l, y), cs, AL.al.take_app(cs, rest)) : {A.A1HDef{T.Asn1Tag{c, n}, _, B.drop(l, y)} == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}
  %Equal.sym(List<&2, U32>, B.drop(l, y), rest, AL.al.drop_app(cs, rest)) : {A.A1HDef{T.Asn1Tag{c, n}, cs, _} == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}
  {==}

def ph.fin2_def(m: Bool, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +hu: {En.a1.is_univ0(c, n) == False{} : Bool}, +hid: {T.a1.id_ok(n) == True{} : Bool}, +hok: {L.a1.len_ok(List.length(&2, U32, cs)) == True{} : Bool}) -> {A.a1.head.fin2(m, En.a1.tlv(c, True{}, n, cs, rest), A.A1HDef{T.Asn1Tag{c, n}, cs, rest}) == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}:
  match m:
    case True{}:
      ph.canon_def(c, n, cs, rest, hu, hid, hok)
    case False{}:
      {==}

def ph.fin_def(+r: R.Asn1Rules, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +hu: {En.a1.is_univ0(c, n) == False{} : Bool}, +hid: {T.a1.id_ok(n) == True{} : Bool}, +hok: {L.a1.len_ok(List.length(&2, U32, cs)) == True{} : Bool}) -> {A.a1.head.fin(r, En.a1.tlv(c, True{}, n, cs, rest), A.a1.head0(r, En.a1.tlv(c, True{}, n, cs, rest))) == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}:
  +x0 = En.a1.tlv(c, True{}, n, cs, rest)
  %Equal.sym(A.A1Head, A.a1.head0(r, x0), A.A1HDef{T.Asn1Tag{c, n}, cs, rest}, ph.head0_def(r, c, n, cs, rest, hu, hid, hok)) : {A.a1.head.fin(r, x0, _) == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}
  %Equal.sym(A.A1Head, A.a1.head.indef_off(R.Asn1Rules.indefinite(r), ph.mk(True{}, T.Asn1Tag{c, n}, cs, rest)), ph.mk(True{}, T.Asn1Tag{c, n}, cs, rest), ph.indef_off_keep(R.Asn1Rules.indefinite(r), T.Asn1Tag{c, n}, cs, rest, True{})) : {A.a1.head.fin2(R.Asn1Rules.min_length(r), x0, _) == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}
  ph.fin2_def(R.Asn1Rules.min_length(r), c, n, cs, rest, hu, hid, hok)

def ph.nend_def(xs: List<&2, U32>, +t: T.Asn1Tag, +cs: List<&2, U32>, +rest: List<&2, U32>) -> {A.a1.head.nend(xs, A.A1HDef{t, cs, rest}) == A.A1HDef{t, cs, rest} : A.A1Head}:
  match xs:
    case Nil{}:
      {==}
    case Con{y, u}:
      {==}

# the header of an element the encoder wrote, under any rules
def ph.head_def(+r: R.Asn1Rules, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +hu: {En.a1.is_univ0(c, n) == False{} : Bool}, +hid: {T.a1.id_ok(n) == True{} : Bool}, +hok: {L.a1.len_ok(List.length(&2, U32, cs)) == True{} : Bool}) -> {A.a1.head(r, En.a1.tlv(c, True{}, n, cs, rest)) == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}:
  +x0 = En.a1.tlv(c, True{}, n, cs, rest)
  +w : A.A1Head = A.A1HDef{T.Asn1Tag{c, n}, cs, rest}
  %Equal.sym(A.A1Head, A.a1.head.fin(r, x0, A.a1.head0(r, x0)), w, ph.fin_def(r, c, n, cs, rest, hu, hid, hok)) : {A.a1.head.nend(x0, _) == w : A.A1Head}
  ph.nend_def(x0, T.Asn1Tag{c, n}, cs, rest)

def ph.ioff_end(a: Bool) -> {A.a1.head.indef_off(a, A.A1HEnd{}) == A.A1HEnd{} : A.A1Head}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ph.fin2_end(m: Bool) -> {A.a1.head.fin2(m, Nil{}, A.A1HEnd{}) == A.A1HEnd{} : A.A1Head}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

# no octets: the end
def ph.head_nil(+r: R.Asn1Rules) -> {A.a1.head(r, Nil{}) == A.A1HEnd{} : A.A1Head}:
  %Equal.sym(A.A1Head, A.a1.head.indef_off(R.Asn1Rules.indefinite(r), A.A1HEnd{}), A.A1HEnd{}, ph.ioff_end(R.Asn1Rules.indefinite(r))) : {A.a1.head.fin2(R.Asn1Rules.min_length(r), Nil{}, _) == A.A1HEnd{} : A.A1Head}
  ph.fin2_end(R.Asn1Rules.min_length(r))
