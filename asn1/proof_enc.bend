# Proofs for bend-osdev-asn1: decoding what the encoder wrote gives the
# elements back, under any rules they conform to. Element by element: the
# header reads back (proof_head.bend), the contents octets are taken, a
# constructed element's contents decode to its elements (the induction), and
# the rules' checks pass because the value conforms.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ./error.bend as E
import ./number.bend as Nu
import ./tag.bend as T
import ./length.bend as L
import ./node.bend as N
import ./rules.bend as R
import ./encode.bend as En
import ./conform.bend as C
import ./asn1.bend as A
import ./proof_nat.bend as AN
import ./proof_list.bend as AL
import ./proof_u32.bend as AU
import ./proof_num.bend as PN
import ./proof_head.bend as PH

# The encoder's octets are already masked

def pe.fix_b(+k: Nat) -> {B.byte(Nu.a1.b(k)) == Nu.a1.b(k) : U32}:
  AL.al.byte_idem(U32.from_nat(k))

def pe.fix_bytes_of(ds: List<&2, Nat>) -> {B.mask(Nu.a1.bytes_of(ds)) == Nu.a1.bytes_of(ds) : List<&2, U32>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      %Equal.sym(U32, B.byte(Nu.a1.b(d)), Nu.a1.b(d), pe.fix_b(d)) : {Con{_, B.mask(Nu.a1.bytes_of(t))} == Con{Nu.a1.b(d), Nu.a1.bytes_of(t)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(Nu.a1.bytes_of(t)), Nu.a1.bytes_of(t), pe.fix_bytes_of(t)) : {Con{Nu.a1.b(d), _} == Con{Nu.a1.b(d), Nu.a1.bytes_of(t)} : List<&2, U32>}
      {==}

def pe.fix_enc128(ds: List<&2, Nat>) -> {B.mask(Nu.a1.enc128(ds)) == Nu.a1.enc128(ds) : List<&2, U32>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      match t:
        case Nil{}:
          %Equal.sym(U32, B.byte(Nu.a1.b(d)), Nu.a1.b(d), pe.fix_b(d)) : {[_] == [Nu.a1.b(d)] : List<&2, U32>}
          {==}
        case Con{+e, +u}:
          +x = Nu.a1.b(Nat.add(128n, d))
          +rest = Nu.a1.enc128(Con{e, u})
          %Equal.sym(U32, B.byte(x), x, pe.fix_b(Nat.add(128n, d))) : {Con{_, B.mask(rest)} == Con{x, rest} : List<&2, U32>}
          %Equal.sym(List<&2, U32>, B.mask(rest), rest, pe.fix_enc128(Con{e, u})) : {Con{x, _} == Con{x, rest} : List<&2, U32>}
          {==}

def pe.fix_id.go(lt: Bool, +c: T.Asn1Class, +cons: Bool, +n: Nat, +hl: {Nat.is_lt(n, 31n) == lt : Bool}) -> {B.mask(T.a1.id_bytes(c, cons, n)) == T.a1.id_bytes(c, cons, n) : List<&2, U32>}:
  match lt:
    case True{}:
      +x = Nu.a1.b(T.a1.id_octet(c, cons, n))
      %Equal.sym(List<&2, U32>, T.a1.id_bytes(c, cons, n), [x], PH.ph.idb_low(c, cons, n, hl)) : {B.mask(_) == _ : List<&2, U32>}
      %Equal.sym(U32, B.byte(x), x, pe.fix_b(T.a1.id_octet(c, cons, n))) : {[_] == [x] : List<&2, U32>}
      {==}
    case False{}:
      +x = Nu.a1.b(T.a1.id_octet(c, cons, 31n))
      +ids : List<&2, U32> = Con{x, Nu.a1.b128(n)}
      %Equal.sym(List<&2, U32>, T.a1.id_bytes(c, cons, n), ids, PH.ph.idb_high(c, cons, n, hl)) : {B.mask(_) == _ : List<&2, U32>}
      %Equal.sym(U32, B.byte(x), x, pe.fix_b(T.a1.id_octet(c, cons, 31n))) : {Con{_, B.mask(Nu.a1.b128(n))} == ids : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(Nu.a1.b128(n)), Nu.a1.b128(n), pe.fix_enc128(Nu.a1.digits(128n, n))) : {Con{x, _} == ids : List<&2, U32>}
      {==}

def pe.fix_id(+c: T.Asn1Class, +cons: Bool, +n: Nat) -> {B.mask(T.a1.id_bytes(c, cons, n)) == T.a1.id_bytes(c, cons, n) : List<&2, U32>}:
  pe.fix_id.go(Nat.is_lt(n, 31n), c, cons, n, {==})

def pe.fix_len.go(lt: Bool, +n: Nat, +hl: {Nat.is_lt(n, 128n) == lt : Bool}) -> {B.mask(L.a1.len_bytes(n)) == L.a1.len_bytes(n) : List<&2, U32>}:
  match lt:
    case True{}:
      %Equal.sym(List<&2, U32>, L.a1.len_bytes(n), [Nu.a1.b(n)], PN.pn.lb_short(n, hl)) : {B.mask(_) == _ : List<&2, U32>}
      %Equal.sym(U32, B.byte(Nu.a1.b(n)), Nu.a1.b(n), pe.fix_b(n)) : {[_] == [Nu.a1.b(n)] : List<&2, U32>}
      {==}
    case False{}:
      +k = Nat.add(128n, List.length(&2, U32, Nu.a1.be(n)))
      +l1 : List<&2, U32> = Con{Nu.a1.b(k), Nu.a1.be(n)}
      %Equal.sym(List<&2, U32>, L.a1.len_bytes(n), l1, PN.pn.lb_long(n, hl)) : {B.mask(_) == _ : List<&2, U32>}
      %Equal.sym(U32, B.byte(Nu.a1.b(k)), Nu.a1.b(k), pe.fix_b(k)) : {Con{_, B.mask(Nu.a1.be(n))} == l1 : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(Nu.a1.be(n)), Nu.a1.be(n), pe.fix_bytes_of(Nu.a1.digits(256n, n))) : {Con{Nu.a1.b(k), _} == l1 : List<&2, U32>}
      {==}

def pe.fix_len(+n: Nat) -> {B.mask(L.a1.len_bytes(n)) == L.a1.len_bytes(n) : List<&2, U32>}:
  pe.fix_len.go(Nat.is_lt(n, 128n), n, {==})

# masking an element's octets masks only what follows its contents
def pe.mask_tlv(+c: T.Asn1Class, +cons: Bool, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +hcs: {B.mask(cs) == cs : List<&2, U32>}) -> {B.mask(En.a1.tlv(c, cons, n, cs, rest)) == En.a1.tlv(c, cons, n, cs, B.mask(rest)) : List<&2, U32>}:
  +id = T.a1.id_bytes(c, cons, n)
  +lb = L.a1.len_bytes(List.length(&2, U32, cs))
  +want = En.a1.tlv(c, cons, n, cs, B.mask(rest))
  %Equal.sym(List<&2, U32>, B.mask(List.append(&2, U32, id, List.append(&2, U32, lb, List.append(&2, U32, cs, rest)))), List.append(&2, U32, B.mask(id), B.mask(List.append(&2, U32, lb, List.append(&2, U32, cs, rest)))), AL.al.mask_app(id, List.append(&2, U32, lb, List.append(&2, U32, cs, rest)))) : {_ == want : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(List.append(&2, U32, lb, List.append(&2, U32, cs, rest))), List.append(&2, U32, B.mask(lb), B.mask(List.append(&2, U32, cs, rest))), AL.al.mask_app(lb, List.append(&2, U32, cs, rest))) : {List.append(&2, U32, B.mask(id), _) == want : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(List.append(&2, U32, cs, rest)), List.append(&2, U32, B.mask(cs), B.mask(rest)), AL.al.mask_app(cs, rest)) : {List.append(&2, U32, B.mask(id), List.append(&2, U32, B.mask(lb), _)) == want : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(id), id, pe.fix_id(c, cons, n)) : {List.append(&2, U32, _, List.append(&2, U32, B.mask(lb), List.append(&2, U32, B.mask(cs), B.mask(rest)))) == want : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(lb), lb, pe.fix_len(List.length(&2, U32, cs))) : {List.append(&2, U32, id, List.append(&2, U32, _, List.append(&2, U32, B.mask(cs), B.mask(rest)))) == want : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(cs), cs, hcs) : {List.append(&2, U32, id, List.append(&2, U32, lb, List.append(&2, U32, _, B.mask(rest)))) == want : List<&2, U32>}
  {==}

# masking the encoder's octets changes nothing but the tail
def pe.mask_enc(ns: List<&2, N.Asn1Node>, +tail: List<&2, U32>) -> {B.mask(En.a1.enc_list(ns, tail)) == En.a1.enc_list(ns, B.mask(tail)) : List<&2, U32>}:
  match ns:
    case Nil{}:
      {==}
    case Con{N.Asn1Prim{T.Asn1Tag{+c, +n}, +o}, +rest}:
      +cs = B.Octets.to_list(o)
      %Equal.sym(List<&2, U32>, B.mask(En.a1.tlv(c, False{}, n, cs, En.a1.enc_list(rest, tail))), En.a1.tlv(c, False{}, n, cs, B.mask(En.a1.enc_list(rest, tail))), pe.mask_tlv(c, False{}, n, cs, En.a1.enc_list(rest, tail), AL.al.mask_to(o))) : {_ == En.a1.tlv(c, False{}, n, cs, En.a1.enc_list(rest, B.mask(tail))) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(En.a1.enc_list(rest, tail)), En.a1.enc_list(rest, B.mask(tail)), pe.mask_enc(rest, tail)) : {En.a1.tlv(c, False{}, n, cs, _) == En.a1.tlv(c, False{}, n, cs, En.a1.enc_list(rest, B.mask(tail))) : List<&2, U32>}
      {==}
    case Con{N.Asn1Cons{T.Asn1Tag{+c, +n}, +xs}, +rest}:
      +cs = En.a1.enc_list(xs, Nil{})
      %Equal.sym(List<&2, U32>, B.mask(En.a1.tlv(c, True{}, n, cs, En.a1.enc_list(rest, tail))), En.a1.tlv(c, True{}, n, cs, B.mask(En.a1.enc_list(rest, tail))), pe.mask_tlv(c, True{}, n, cs, En.a1.enc_list(rest, tail), pe.mask_enc(xs, Nil{}))) : {_ == En.a1.tlv(c, True{}, n, cs, En.a1.enc_list(rest, B.mask(tail))) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.mask(En.a1.enc_list(rest, tail)), En.a1.enc_list(rest, B.mask(tail)), pe.mask_enc(rest, tail)) : {En.a1.tlv(c, True{}, n, cs, _) == En.a1.tlv(c, True{}, n, cs, En.a1.enc_list(rest, B.mask(tail))) : List<&2, U32>}
      {==}

# Inverting the encoder's error check

def pe.mdisc(m: Maybe<&2, E.Asn1Error>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def pe.sn(-x: E.Asn1Error, e: {Some{x} == None{} : Maybe<&2, E.Asn1Error>}) -> Empty:
  %e : pe.mdisc(_)
  Unit{}

def pe.first_l(a: Maybe<&2, E.Asn1Error>, -b: Maybe<&2, E.Asn1Error>, +h: {En.a1.first(a, b) == None{} : Maybe<&2, E.Asn1Error>}) -> {a == None{} : Maybe<&2, E.Asn1Error>}:
  match a:
    case None{}:
      {==}
    case Some{e}:
      Empty.absurd({Some{e} == None{} : Maybe<&2, E.Asn1Error>}, pe.sn(e, h))

def pe.first_r(a: Maybe<&2, E.Asn1Error>, -b: Maybe<&2, E.Asn1Error>, +h: {En.a1.first(a, b) == None{} : Maybe<&2, E.Asn1Error>}) -> {b == None{} : Maybe<&2, E.Asn1Error>}:
  match a:
    case None{}:
      h
    case Some{e}:
      Empty.absurd({b == None{} : Maybe<&2, E.Asn1Error>}, pe.sn(e, h))


def pe.u0(u0: Bool, -idok: Bool, -ok: Bool, +h: {En.a1.node_err.pick(u0, idok, ok) == None{} : Maybe<&2, E.Asn1Error>}) -> {u0 == False{} : Bool}:
  match u0:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, pe.sn(E.Asn1ReservedTag{}, h))
    case False{}:
      {==}

def pe.idk(u0: Bool, idok: Bool, -ok: Bool, +h: {En.a1.node_err.pick(u0, idok, ok) == None{} : Maybe<&2, E.Asn1Error>}) -> {idok == True{} : Bool}:
  match u0 idok:
    case True{} _:
      Empty.absurd({idok == True{} : Bool}, pe.sn(E.Asn1ReservedTag{}, h))
    case False{} True{}:
      {==}
    case False{} False{}:
      Empty.absurd({False{} == True{} : Bool}, pe.sn(E.Asn1BadTag{}, h))

def pe.lok(u0: Bool, idok: Bool, ok: Bool, +h: {En.a1.node_err.pick(u0, idok, ok) == None{} : Maybe<&2, E.Asn1Error>}) -> {ok == True{} : Bool}:
  match u0 idok ok:
    case True{} _ _:
      Empty.absurd({ok == True{} : Bool}, pe.sn(E.Asn1ReservedTag{}, h))
    case False{} False{} _:
      Empty.absurd({ok == True{} : Bool}, pe.sn(E.Asn1BadTag{}, h))
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      Empty.absurd({False{} == True{} : Bool}, pe.sn(E.Asn1TooLong{}, h))

# Lengths: an element's octets are longer than its contents and than what
# follows it

def pe.id_ne.go(lt: Bool, +c: T.Asn1Class, +cons: Bool, +n: Nat, +hl: {Nat.is_lt(n, 31n) == lt : Bool}) -> {Nat.is_le(1n, List.length(&2, U32, T.a1.id_bytes(c, cons, n))) == True{} : Bool}:
  match lt:
    case True{}:
      %Equal.sym(List<&2, U32>, T.a1.id_bytes(c, cons, n), [Nu.a1.b(T.a1.id_octet(c, cons, n))], PH.ph.idb_low(c, cons, n, hl)) : {Nat.is_le(1n, List.length(&2, U32, _)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(List<&2, U32>, T.a1.id_bytes(c, cons, n), Con{Nu.a1.b(T.a1.id_octet(c, cons, 31n)), Nu.a1.b128(n)}, PH.ph.idb_high(c, cons, n, hl)) : {Nat.is_le(1n, List.length(&2, U32, _)) == True{} : Bool}
      AN.an.le_zero(List.length(&2, U32, Nu.a1.b128(n)))

def pe.id_ne(+c: T.Asn1Class, +cons: Bool, +n: Nat) -> {Nat.is_le(1n, List.length(&2, U32, T.a1.id_bytes(c, cons, n))) == True{} : Bool}:
  pe.id_ne.go(Nat.is_lt(n, 31n), c, cons, n, {==})

def pe.lt_plus(+a: Nat, +x: Nat, +y: Nat, +ha: {Nat.is_le(1n, a) == True{} : Bool}, +hx: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_lt(x, Nat.add(a, y)) == True{} : Bool}:
  match a:
    case 0n:
      Empty.absurd({Nat.is_lt(x, Nat.add(0n, y)) == True{} : Bool}, AN.an.ft(ha))
    case 1n+q:
      AN.an.le_lt_succ(x, Nat.add(q, y), AN.an.le_trans(x, y, Nat.add(q, y), hx, AN.an.le_add_l(q, y)))

# the length of an element's octets
def pe.len_tlv(+c: T.Asn1Class, +cons: Bool, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>) -> {List.length(&2, U32, En.a1.tlv(c, cons, n, cs, rest)) == Nat.add(List.length(&2, U32, T.a1.id_bytes(c, cons, n)), Nat.add(List.length(&2, U32, L.a1.len_bytes(List.length(&2, U32, cs))), Nat.add(List.length(&2, U32, cs), List.length(&2, U32, rest)))) : Nat}:
  +id = T.a1.id_bytes(c, cons, n)
  +lb = L.a1.len_bytes(List.length(&2, U32, cs))
  +lcr = Nat.add(List.length(&2, U32, cs), List.length(&2, U32, rest))
  +want = Nat.add(List.length(&2, U32, id), Nat.add(List.length(&2, U32, lb), lcr))
  %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, id, List.append(&2, U32, lb, List.append(&2, U32, cs, rest)))), Nat.add(List.length(&2, U32, id), List.length(&2, U32, List.append(&2, U32, lb, List.append(&2, U32, cs, rest)))), AL.al.app_len(id, List.append(&2, U32, lb, List.append(&2, U32, cs, rest)))) : {_ == want : Nat}
  %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, lb, List.append(&2, U32, cs, rest))), Nat.add(List.length(&2, U32, lb), List.length(&2, U32, List.append(&2, U32, cs, rest))), AL.al.app_len(lb, List.append(&2, U32, cs, rest))) : {Nat.add(List.length(&2, U32, id), _) == want : Nat}
  %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, cs, rest)), lcr, AL.al.app_len(cs, rest)) : {Nat.add(List.length(&2, U32, id), Nat.add(List.length(&2, U32, lb), _)) == want : Nat}
  {==}

def pe.lt_tlv_rest(+c: T.Asn1Class, +cons: Bool, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>) -> {Nat.is_lt(List.length(&2, U32, rest), List.length(&2, U32, En.a1.tlv(c, cons, n, cs, rest))) == True{} : Bool}:
  +lc = List.length(&2, U32, cs)
  +lr = List.length(&2, U32, rest)
  +ll = List.length(&2, U32, L.a1.len_bytes(lc))
  %Equal.sym(Nat, List.length(&2, U32, En.a1.tlv(c, cons, n, cs, rest)), Nat.add(List.length(&2, U32, T.a1.id_bytes(c, cons, n)), Nat.add(ll, Nat.add(lc, lr))), pe.len_tlv(c, cons, n, cs, rest)) : {Nat.is_lt(lr, _) == True{} : Bool}
  pe.lt_plus(List.length(&2, U32, T.a1.id_bytes(c, cons, n)), lr, Nat.add(ll, Nat.add(lc, lr)), pe.id_ne(c, cons, n), AN.an.le_trans(lr, Nat.add(lc, lr), Nat.add(ll, Nat.add(lc, lr)), AN.an.le_add_l(lc, lr), AN.an.le_add_l(ll, Nat.add(lc, lr))))

def pe.lt_tlv_cs(+c: T.Asn1Class, +cons: Bool, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>) -> {Nat.is_lt(List.length(&2, U32, cs), List.length(&2, U32, En.a1.tlv(c, cons, n, cs, rest))) == True{} : Bool}:
  +lc = List.length(&2, U32, cs)
  +lr = List.length(&2, U32, rest)
  +ll = List.length(&2, U32, L.a1.len_bytes(lc))
  %Equal.sym(Nat, List.length(&2, U32, En.a1.tlv(c, cons, n, cs, rest)), Nat.add(List.length(&2, U32, T.a1.id_bytes(c, cons, n)), Nat.add(ll, Nat.add(lc, lr))), pe.len_tlv(c, cons, n, cs, rest)) : {Nat.is_lt(lc, _) == True{} : Bool}
  pe.lt_plus(List.length(&2, U32, T.a1.id_bytes(c, cons, n)), lc, Nat.add(ll, Nat.add(lc, lr)), pe.id_ne(c, cons, n), AN.an.le_trans(lc, Nat.add(lc, lr), Nat.add(ll, Nat.add(lc, lr)), AN.an.le_add(lc, lr), AN.an.le_add_l(ll, Nat.add(lc, lr))))

# fuel above an element's octets is fuel above what is inside it
def pe.fuel_in(+x: Nat, +len: Nat, +g: Nat, +hx: {Nat.is_lt(x, len) == True{} : Bool}, +hf: {Nat.is_lt(len, 1n+g) == True{} : Bool}) -> {Nat.is_lt(x, g) == True{} : Bool}:
  AN.an.lt_le_trans(x, len, g, hx, AN.an.lt_succ_le(len, g, hf))

def pe.no_fuel(+x: Nat, +hf: {Nat.is_lt(x, 0n) == True{} : Bool}) -> Empty:
  AN.an.ft(Equal.trans(Bool, False{}, Nat.is_lt(x, 0n), True{}, Equal.sym(Bool, Nat.is_lt(x, 0n), False{}, AN.an.lt0(x)), hf))

# Decoding the encoder's octets of elements ns, to the end of the input,
# gives ns back (the induction runs over the elements and their contents)
def pe.all(ns: List<&2, N.Asn1Node>, f: Nat, +r: R.Asn1Rules, +herr: {En.a1.enc_err(ns) == None{} : Maybe<&2, E.Asn1Error>}, +hconf: {C.a1.conf_list(ns, r) == True{} : Bool}, +hf: {Nat.is_lt(List.length(&2, U32, En.a1.enc_list(ns, Nil{})), f) == True{} : Bool}) -> {A.a1.dec(f, r, A.A1All{}, A.a1.head(r, En.a1.enc_list(ns, Nil{}))) == Done{A.A1Out{ns, Nil{}}} : Result<&2, &2, E.Asn1Error, A.A1Out>}:
  match ns:
    case Nil{}:
      match f:
        case 0n:
          Empty.absurd({A.a1.dec(0n, r, A.A1All{}, A.a1.head(r, En.a1.enc_list(Nil{}, Nil{}))) == Done{A.A1Out{Nil{}, Nil{}}} : Result<&2, &2, E.Asn1Error, A.A1Out>}, pe.no_fuel(0n, hf))
        case 1n+g:
          %Equal.sym(A.A1Head, A.a1.head(r, Nil{}), A.A1HEnd{}, PH.ph.head_nil(r)) : {A.a1.dec(1n+g, r, A.A1All{}, _) == Done{A.A1Out{Nil{}, Nil{}}} : Result<&2, &2, E.Asn1Error, A.A1Out>}
          {==}
    case Con{N.Asn1Prim{T.Asn1Tag{+c, +n}, +o}, +rest}:
      match f:
        case 0n:
          Empty.absurd({A.a1.dec(0n, r, A.A1All{}, A.a1.head(r, En.a1.enc_list(Con{N.Asn1Prim{T.Asn1Tag{c, n}, o}, rest}, Nil{}))) == Done{A.A1Out{Con{N.Asn1Prim{T.Asn1Tag{c, n}, o}, rest}, Nil{}}} : Result<&2, &2, E.Asn1Error, A.A1Out>}, pe.no_fuel(List.length(&2, U32, En.a1.enc_list(Con{N.Asn1Prim{T.Asn1Tag{c, n}, o}, rest}, Nil{})), hf))
        case 1n+ +g:
          +cs = B.Octets.to_list(o)
          +t : T.Asn1Tag = T.Asn1Tag{c, n}
          +er = En.a1.enc_list(rest, Nil{})
          +x : N.Asn1Node = N.Asn1Prim{t, o}
          +ne = En.a1.node_err(c, n, B.Octets.len(o))
          +he1 = pe.first_l(ne, En.a1.enc_err(rest), herr)
          +he2 = pe.first_r(ne, En.a1.enc_err(rest), herr)
          +hu = pe.u0(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(B.Octets.len(o)), he1)
          +hok0 = pe.lok(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(B.Octets.len(o)), he1)
          +hid = pe.idk(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(B.Octets.len(o)), he1)
          +hok = Equal.trans(Bool, L.a1.len_ok(List.length(&2, U32, cs)), L.a1.len_ok(B.Octets.len(o)), True{}, Equal.cong(Nat, Bool, z => L.a1.len_ok(z), List.length(&2, U32, cs), B.Octets.len(o), Equal.sym(Nat, B.Octets.len(o), List.length(&2, U32, cs), AL.al.olen(o))), hok0)
          +hform = AN.an.and_l(R.a1.form_ok(r, t, False{}), C.a1.conf_list(rest, r), hconf)
          +hrest = AN.an.and_r(R.a1.form_ok(r, t, False{}), C.a1.conf_list(rest, r), hconf)
          +ih = pe.all(rest, g, r, he2, hrest, pe.fuel_in(List.length(&2, U32, er), List.length(&2, U32, En.a1.tlv(c, False{}, n, cs, er)), g, pe.lt_tlv_rest(c, False{}, n, cs, er), hf))
          +want : Result<&2, &2, E.Asn1Error, A.A1Out> = Done{A.A1Out{Con{x, rest}, Nil{}}}
          %Equal.sym(A.A1Head, A.a1.head(r, En.a1.tlv(c, False{}, n, cs, er)), A.A1HPrim{t, cs, er}, PH.ph.head_prim(r, c, n, cs, er, hu, hid, hok)) : {A.a1.dec(1n+g, r, A.A1All{}, _) == want : Result<&2, &2, E.Asn1Error, A.A1Out>}
          %Equal.sym(B.Octets, B.Octets.of_list(cs), o, AL.al.of_to(o)) : {A.a1.more(A.a1.mk_prim(r, t, _), A.a1.dec(g, r, A.A1All{}, A.a1.head(r, er))) == want : Result<&2, &2, E.Asn1Error, A.A1Out>}
          %Equal.sym(Bool, R.a1.form_ok(r, t, False{}), True{}, hform) : {A.a1.more(A.a1.mk_prim.pick(_, t, o), A.a1.dec(g, r, A.A1All{}, A.a1.head(r, er))) == want : Result<&2, &2, E.Asn1Error, A.A1Out>}
          %Equal.sym(Result<&2, &2, E.Asn1Error, A.A1Out>, A.a1.dec(g, r, A.A1All{}, A.a1.head(r, er)), Done{A.A1Out{rest, Nil{}}}, ih) : {A.a1.more(Done{x}, _) == want : Result<&2, &2, E.Asn1Error, A.A1Out>}
          {==}
    case Con{N.Asn1Cons{T.Asn1Tag{+c, +n}, +xs}, +rest}:
      match f:
        case 0n:
          Empty.absurd({A.a1.dec(0n, r, A.A1All{}, A.a1.head(r, En.a1.enc_list(Con{N.Asn1Cons{T.Asn1Tag{c, n}, xs}, rest}, Nil{}))) == Done{A.A1Out{Con{N.Asn1Cons{T.Asn1Tag{c, n}, xs}, rest}, Nil{}}} : Result<&2, &2, E.Asn1Error, A.A1Out>}, pe.no_fuel(List.length(&2, U32, En.a1.enc_list(Con{N.Asn1Cons{T.Asn1Tag{c, n}, xs}, rest}, Nil{})), hf))
        case 1n+ +g:
          +cs = En.a1.enc_list(xs, Nil{})
          +t : T.Asn1Tag = T.Asn1Tag{c, n}
          +er = En.a1.enc_list(rest, Nil{})
          +x : N.Asn1Node = N.Asn1Cons{t, xs}
          +ne = En.a1.node_err(c, n, List.length(&2, U32, cs))
          +e23 = En.a1.first(En.a1.enc_err(xs), En.a1.enc_err(rest))
          +he1 = pe.first_l(ne, e23, herr)
          +he23 = pe.first_r(ne, e23, herr)
          +he2 = pe.first_l(En.a1.enc_err(xs), En.a1.enc_err(rest), he23)
          +he3 = pe.first_r(En.a1.enc_err(xs), En.a1.enc_err(rest), he23)
          +hu = pe.u0(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)), he1)
          +hok = pe.lok(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)), he1)
          +hid = pe.idk(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)), he1)
          +c34 = Bool.and(C.a1.conf_list(xs, r), C.a1.conf_list(rest, r))
          +c234 = Bool.and(C.a1.set_ok(r, t, xs), c34)
          +hform = AN.an.and_l(R.a1.form_ok(r, t, True{}), c234, hconf)
          +h234 = AN.an.and_r(R.a1.form_ok(r, t, True{}), c234, hconf)
          +hset = AN.an.and_l(C.a1.set_ok(r, t, xs), c34, h234)
          +h34 = AN.an.and_r(C.a1.set_ok(r, t, xs), c34, h234)
          +hxs = AN.an.and_l(C.a1.conf_list(xs, r), C.a1.conf_list(rest, r), h34)
          +hrest = AN.an.and_r(C.a1.conf_list(xs, r), C.a1.conf_list(rest, r), h34)
          +lt = List.length(&2, U32, En.a1.tlv(c, True{}, n, cs, er))
          +ihx = pe.all(xs, g, r, he2, hxs, pe.fuel_in(List.length(&2, U32, cs), lt, g, pe.lt_tlv_cs(c, True{}, n, cs, er), hf))
          +ihr = pe.all(rest, g, r, he3, hrest, pe.fuel_in(List.length(&2, U32, er), lt, g, pe.lt_tlv_rest(c, True{}, n, cs, er), hf))
          +want : Result<&2, &2, E.Asn1Error, A.A1Out> = Done{A.A1Out{Con{x, rest}, Nil{}}}
          %Equal.sym(A.A1Head, A.a1.head(r, En.a1.tlv(c, True{}, n, cs, er)), A.A1HDef{t, cs, er}, PH.ph.head_def(r, c, n, cs, er, hu, hid, hok)) : {A.a1.dec(1n+g, r, A.A1All{}, _) == want : Result<&2, &2, E.Asn1Error, A.A1Out>}
          %Equal.sym(Result<&2, &2, E.Asn1Error, A.A1Out>, A.a1.dec(g, r, A.A1All{}, A.a1.head(r, cs)), Done{A.A1Out{xs, Nil{}}}, ihx) : {A.a1.more(A.a1.mk_cons(r, t, _), A.a1.dec(g, r, A.A1All{}, A.a1.head(r, er))) == want : Result<&2, &2, E.Asn1Error, A.A1Out>}
          %Equal.sym(Bool, R.a1.form_ok(r, t, True{}), True{}, hform) : {A.a1.more(A.a1.mk_cons.form(_, r, t, xs), A.a1.dec(g, r, A.A1All{}, A.a1.head(r, er))) == want : Result<&2, &2, E.Asn1Error, A.A1Out>}
          %Equal.sym(Bool, C.a1.set_ok(r, t, xs), True{}, hset) : {A.a1.more(A.a1.mk_cons.set(_, t, xs), A.a1.dec(g, r, A.A1All{}, A.a1.head(r, er))) == want : Result<&2, &2, E.Asn1Error, A.A1Out>}
          %Equal.sym(Result<&2, &2, E.Asn1Error, A.A1Out>, A.a1.dec(g, r, A.A1All{}, A.a1.head(r, er)), Done{A.A1Out{rest, Nil{}}}, ihr) : {A.a1.more(Done{x}, _) == want : Result<&2, &2, E.Asn1Error, A.A1Out>}
          {==}

# decoding one element the encoder wrote gives it back
def pe.one(x0: N.Asn1Node, f: Nat, +r: R.Asn1Rules, +herr: {En.a1.enc_err([x0]) == None{} : Maybe<&2, E.Asn1Error>}, +hconf: {C.a1.conf_list([x0], r) == True{} : Bool}, +hf: {Nat.is_lt(List.length(&2, U32, En.a1.enc_list([x0], Nil{})), f) == True{} : Bool}) -> {A.a1.dec(f, r, A.A1One{}, A.a1.head(r, En.a1.enc_list([x0], Nil{}))) == Done{A.A1Out{[x0], Nil{}}} : Result<&2, &2, E.Asn1Error, A.A1Out>}:
  match x0:
    case N.Asn1Prim{T.Asn1Tag{+c, +n}, +o}:
      match f:
        case 0n:
          Empty.absurd({A.a1.dec(0n, r, A.A1One{}, A.a1.head(r, En.a1.enc_list([N.Asn1Prim{T.Asn1Tag{c, n}, o}], Nil{}))) == Done{A.A1Out{[N.Asn1Prim{T.Asn1Tag{c, n}, o}], Nil{}}} : Result<&2, &2, E.Asn1Error, A.A1Out>}, pe.no_fuel(List.length(&2, U32, En.a1.enc_list([N.Asn1Prim{T.Asn1Tag{c, n}, o}], Nil{})), hf))
        case 1n+ +g:
          +cs = B.Octets.to_list(o)
          +t : T.Asn1Tag = T.Asn1Tag{c, n}
          +x : N.Asn1Node = N.Asn1Prim{t, o}
          +ne = En.a1.node_err(c, n, B.Octets.len(o))
          +he1 = pe.first_l(ne, None{}, herr)
          +hu = pe.u0(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(B.Octets.len(o)), he1)
          +hok0 = pe.lok(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(B.Octets.len(o)), he1)
          +hid = pe.idk(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(B.Octets.len(o)), he1)
          +hok = Equal.trans(Bool, L.a1.len_ok(List.length(&2, U32, cs)), L.a1.len_ok(B.Octets.len(o)), True{}, Equal.cong(Nat, Bool, z => L.a1.len_ok(z), List.length(&2, U32, cs), B.Octets.len(o), Equal.sym(Nat, B.Octets.len(o), List.length(&2, U32, cs), AL.al.olen(o))), hok0)
          +hform = AN.an.and_l(R.a1.form_ok(r, t, False{}), True{}, hconf)
          +want : Result<&2, &2, E.Asn1Error, A.A1Out> = Done{A.A1Out{[x], Nil{}}}
          %Equal.sym(A.A1Head, A.a1.head(r, En.a1.tlv(c, False{}, n, cs, Nil{})), A.A1HPrim{t, cs, Nil{}}, PH.ph.head_prim(r, c, n, cs, Nil{}, hu, hid, hok)) : {A.a1.dec(1n+g, r, A.A1One{}, _) == want : Result<&2, &2, E.Asn1Error, A.A1Out>}
          %Equal.sym(B.Octets, B.Octets.of_list(cs), o, AL.al.of_to(o)) : {A.a1.one(A.a1.mk_prim(r, t, _), Nil{}) == want : Result<&2, &2, E.Asn1Error, A.A1Out>}
          %Equal.sym(Bool, R.a1.form_ok(r, t, False{}), True{}, hform) : {A.a1.one(A.a1.mk_prim.pick(_, t, o), Nil{}) == want : Result<&2, &2, E.Asn1Error, A.A1Out>}
          {==}
    case N.Asn1Cons{T.Asn1Tag{+c, +n}, +xs}:
      match f:
        case 0n:
          Empty.absurd({A.a1.dec(0n, r, A.A1One{}, A.a1.head(r, En.a1.enc_list([N.Asn1Cons{T.Asn1Tag{c, n}, xs}], Nil{}))) == Done{A.A1Out{[N.Asn1Cons{T.Asn1Tag{c, n}, xs}], Nil{}}} : Result<&2, &2, E.Asn1Error, A.A1Out>}, pe.no_fuel(List.length(&2, U32, En.a1.enc_list([N.Asn1Cons{T.Asn1Tag{c, n}, xs}], Nil{})), hf))
        case 1n+ +g:
          +cs = En.a1.enc_list(xs, Nil{})
          +t : T.Asn1Tag = T.Asn1Tag{c, n}
          +x : N.Asn1Node = N.Asn1Cons{t, xs}
          +ne = En.a1.node_err(c, n, List.length(&2, U32, cs))
          +e23 = En.a1.first(En.a1.enc_err(xs), None{})
          +he1 = pe.first_l(ne, e23, herr)
          +he23 = pe.first_r(ne, e23, herr)
          +he2 = pe.first_l(En.a1.enc_err(xs), None{}, he23)
          +hu = pe.u0(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)), he1)
          +hok = pe.lok(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)), he1)
          +hid = pe.idk(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)), he1)
          +c34 = Bool.and(C.a1.conf_list(xs, r), True{})
          +c234 = Bool.and(C.a1.set_ok(r, t, xs), c34)
          +hform = AN.an.and_l(R.a1.form_ok(r, t, True{}), c234, hconf)
          +h234 = AN.an.and_r(R.a1.form_ok(r, t, True{}), c234, hconf)
          +hset = AN.an.and_l(C.a1.set_ok(r, t, xs), c34, h234)
          +h34 = AN.an.and_r(C.a1.set_ok(r, t, xs), c34, h234)
          +hxs = AN.an.and_l(C.a1.conf_list(xs, r), True{}, h34)
          +ihx = pe.all(xs, g, r, he2, hxs, pe.fuel_in(List.length(&2, U32, cs), List.length(&2, U32, En.a1.tlv(c, True{}, n, cs, Nil{})), g, pe.lt_tlv_cs(c, True{}, n, cs, Nil{}), hf))
          +want : Result<&2, &2, E.Asn1Error, A.A1Out> = Done{A.A1Out{[x], Nil{}}}
          %Equal.sym(A.A1Head, A.a1.head(r, En.a1.tlv(c, True{}, n, cs, Nil{})), A.A1HDef{t, cs, Nil{}}, PH.ph.head_def(r, c, n, cs, Nil{}, hu, hid, hok)) : {A.a1.dec(1n+g, r, A.A1One{}, _) == want : Result<&2, &2, E.Asn1Error, A.A1Out>}
          %Equal.sym(Result<&2, &2, E.Asn1Error, A.A1Out>, A.a1.dec(g, r, A.A1All{}, A.a1.head(r, cs)), Done{A.A1Out{xs, Nil{}}}, ihx) : {A.a1.one(A.a1.mk_cons(r, t, _), Nil{}) == want : Result<&2, &2, E.Asn1Error, A.A1Out>}
          %Equal.sym(Bool, R.a1.form_ok(r, t, True{}), True{}, hform) : {A.a1.one(A.a1.mk_cons.form(_, r, t, xs), Nil{}) == want : Result<&2, &2, E.Asn1Error, A.A1Out>}
          %Equal.sym(Bool, C.a1.set_ok(r, t, xs), True{}, hset) : {A.a1.one(A.a1.mk_cons.set(_, t, xs), Nil{}) == want : Result<&2, &2, E.Asn1Error, A.A1Out>}
          {==}

def pe.odisc(r: Result<&2, &2, E.Asn1Error, B.Octets>) -> Type:
  match r:
    case Fail{x}:
      Empty
    case Done{y}:
      Unit

def pe.fd(-x: E.Asn1Error, -y: B.Octets, e: {Fail{x} == Done{y} : Result<&2, &2, E.Asn1Error, B.Octets>}) -> Empty:
  %Equal.sym(Result<&2, &2, E.Asn1Error, B.Octets>, Fail{x}, Done{y}, e) : pe.odisc(_)
  Unit{}

def pe.od(r: Result<&2, &2, E.Asn1Error, B.Octets>) -> B.Octets:
  match r:
    case Fail{x}:
      B.Octets.empty()
    case Done{y}:
      y

# decode after encode
def pe.de(m: Maybe<&2, E.Asn1Error>, +r: R.Asn1Rules, +x0: N.Asn1Node, -b: B.Octets, +em: {En.a1.enc_err([x0]) == m : Maybe<&2, E.Asn1Error>}, +e: {En.a1.encode.go(m, [x0]) == Done{b} : Result<&2, &2, E.Asn1Error, B.Octets>}, +hc: {C.a1.conf_list([x0], r) == True{} : Bool}) -> {A.Asn1.decode(r, b) == Done{x0} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}:
  match m:
    case None{}:
      +ee = En.a1.enc_list([x0], Nil{})
      %Equal.cong(Result<&2, &2, E.Asn1Error, B.Octets>, B.Octets, z => pe.od(z), Done{B.Octets.of_list(ee)}, Done{b}, e) : {A.Asn1.decode(r, _) == Done{x0} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}
      %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(ee)), B.mask(ee), AL.al.to_of(ee)) : {A.a1.top(r, A.a1.run(r, A.A1One{}, _)) == Done{x0} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}
      %Equal.sym(List<&2, U32>, B.mask(ee), ee, pe.mask_enc([x0], Nil{})) : {A.a1.top(r, A.a1.run(r, A.A1One{}, _)) == Done{x0} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}
      +lee = List.length(&2, U32, ee)
      %Equal.sym(Result<&2, &2, E.Asn1Error, A.A1Out>, A.a1.dec(1n+lee, r, A.A1One{}, A.a1.head(r, ee)), Done{A.A1Out{[x0], Nil{}}}, pe.one(x0, 1n+lee, r, em, hc, AN.an.le_lt_succ(lee, lee, AN.an.le_refl(lee)))) : {A.a1.top(r, _) == Done{x0} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}
      {==}
    case Some{x}:
      Empty.absurd({A.Asn1.decode(r, b) == Done{x0} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}, pe.fd(x, b, e))
