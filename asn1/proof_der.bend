# Proofs for bend-osdev-asn1: under DER's length checks, the octets an
# element was read from are its encoding (pd.read_der: law read_der), as
# proof_canon.bend shows the element and the octets after it encode back to
# the input, and a read of one element answers one element (pd.sg); and
# re-tagging a constructed element changes only its identifier octets
# (pd.retag: law encode_retag).
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ./error.bend as E
import ./tag.bend as T
import ./number.bend as Nu
import ./length.bend as L
import ./node.bend as N
import ./rules.bend as R
import ./encode.bend as En
import ./asn1.bend as A
import ./proof_nat.bend as AN
import ./proof_list.bend as AL
import ./proof_canon.bend as PC
import ./proof_oct.bend as OA
import ./proof_split.bend as PS

# A read of one element answers one element

def pd.sg(res: Result<&2, &2, E.Asn1Error, A.A1Out>) -> Type:
  match res:
    case Fail{e}:
      Unit
    case Done{A.A1Out{Nil{}, r}}:
      Empty
    case Done{A.A1Out{Con{x, Nil{}}, r}}:
      Unit
    case Done{A.A1Out{Con{x, Con{y, t}}, r}}:
      Empty

def pd.sg_one(n: Result<&2, &2, E.Asn1Error, N.Asn1Node>, rest: List<&2, U32>) -> pd.sg(A.a1.one(n, rest)):
  match n:
    case Fail{e}:
      Unit{}
    case Done{x}:
      Unit{}

def pd.sg_dec(f: Nat, +r: R.Asn1Rules, h: A.A1Head) -> pd.sg(A.a1.dec(f, r, A.A1One{}, h)):
  match f:
    case 0n:
      Unit{}
    case 1n+ +g:
      match h:
        case A.A1HEnd{}:
          Unit{}
        case A.A1HEoc{rest}:
          Unit{}
        case A.A1HErr{e}:
          Unit{}
        case A.A1HPrim{+t, +cs, +rest}:
          pd.sg_one(A.a1.mk_prim(r, t, B.Octets.of_list(cs)), rest)
        case A.A1HDef{+t, +cs, +rest}:
          pd.sg_one(A.a1.mk_cons(r, t, A.a1.dec(g, r, A.A1All{}, A.a1.head(r, cs))), rest)
        case A.A1HIndef{+t, +rest}:
          +inner = A.a1.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest))
          pd.sg_one(A.a1.mk_cons(r, t, inner), A.a1.out_rest(inner))

# An element's encoding, then other octets

def pd.tlv_app(+c: T.Asn1Class, +cons: Bool, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>) -> {En.a1.tlv(c, cons, n, cs, rest) == List.append(&2, U32, En.a1.tlv(c, cons, n, cs, Nil{}), rest) : List<&2, U32>}:
  +id = T.a1.id_bytes(c, cons, n)
  +lb = L.a1.len_bytes(List.length(&2, U32, cs))
  %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, id, List.append(&2, U32, lb, List.append(&2, U32, cs, Nil{}))), rest), List.append(&2, U32, id, List.append(&2, U32, List.append(&2, U32, lb, List.append(&2, U32, cs, Nil{})), rest)), AL.al.app_assoc(id, List.append(&2, U32, lb, List.append(&2, U32, cs, Nil{})), rest)) : {En.a1.tlv(c, cons, n, cs, rest) == _ : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, lb, List.append(&2, U32, cs, Nil{})), rest), List.append(&2, U32, lb, List.append(&2, U32, List.append(&2, U32, cs, Nil{}), rest)), AL.al.app_assoc(lb, List.append(&2, U32, cs, Nil{}), rest)) : {En.a1.tlv(c, cons, n, cs, rest) == List.append(&2, U32, id, _) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.append(&2, U32, cs, Nil{}), cs, AL.al.app_nil(cs)) : {En.a1.tlv(c, cons, n, cs, rest) == List.append(&2, U32, id, List.append(&2, U32, lb, List.append(&2, U32, _, rest))) : List<&2, U32>}
  {==}

def pd.enc_app(n: N.Asn1Node, +rest: List<&2, U32>) -> {En.a1.enc_list([n], rest) == List.append(&2, U32, En.a1.enc_list([n], Nil{}), rest) : List<&2, U32>}:
  match n:
    case N.Asn1Prim{T.Asn1Tag{+c, +k}, +o}:
      pd.tlv_app(c, False{}, k, B.Octets.to_list(o), rest)
    case N.Asn1Cons{T.Asn1Tag{+c, +k}, +xs}:
      pd.tlv_app(c, True{}, k, En.a1.enc_list(xs, Nil{}), rest)

def pd.rd_tlv(z: Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>) -> A.Asn1Tlv:
  match z:
    case Fail{x}:
      A.Asn1Tlv{N.Asn1Prim{T.Asn1Tag.null(), B.Octets.empty()}, B.Octets.empty()}
    case Done{A.Asn1TlvRead{t, rest}}:
      t

def pd.der_fin(+n: N.Asn1Node, +xs: List<&2, U32>, +r2: List<&2, U32>, +henc: {En.a1.enc_list([n], r2) == xs : List<&2, U32>}, +herr: {En.a1.enc_err([n]) == None{} : Maybe<&2, E.Asn1Error>}) -> {En.Asn1.encode(n) == Done{B.Octets.of_list(B.take(Nat.sub(List.length(&2, U32, xs), List.length(&2, U32, r2)), xs))} : Result<&2, &2, E.Asn1Error, B.Octets>}:
  +ee = En.a1.enc_list([n], Nil{})
  %henc : {En.Asn1.encode(n) == Done{B.Octets.of_list(B.take(Nat.sub(List.length(&2, U32, _), List.length(&2, U32, r2)), _))} : Result<&2, &2, E.Asn1Error, B.Octets>}
  %Equal.sym(List<&2, U32>, En.a1.enc_list([n], r2), List.append(&2, U32, ee, r2), pd.enc_app(n, r2)) : {En.Asn1.encode(n) == Done{B.Octets.of_list(B.take(Nat.sub(List.length(&2, U32, _), List.length(&2, U32, r2)), _))} : Result<&2, &2, E.Asn1Error, B.Octets>}
  %Equal.sym(List<&2, U32>, B.take(Nat.sub(List.length(&2, U32, List.append(&2, U32, ee, r2)), List.length(&2, U32, r2)), List.append(&2, U32, ee, r2)), ee, PS.ps.used(ee, r2)) : {En.Asn1.encode(n) == Done{B.Octets.of_list(_)} : Result<&2, &2, E.Asn1Error, B.Octets>}
  %Equal.sym(Maybe<&2, E.Asn1Error>, En.a1.enc_err([n]), None{}, herr) : {En.a1.encode.go(_, [n]) == Done{B.Octets.of_list(ee)} : Result<&2, &2, E.Asn1Error, B.Octets>}
  {==}

def pd.tlvder(+xs: List<&2, U32>, res: Result<&2, &2, E.Asn1Error, A.A1Out>, hsg: pd.sg(res), hg: PC.pc.goodO(res, xs), +x: A.Asn1Tlv, +rest: B.Octets, +e: {A.a1.tlv.out(xs, res) == Done{A.Asn1TlvRead{x, rest}} : Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>}) -> {En.Asn1.encode(A.Asn1Tlv.node(x)) == Done{A.Asn1Tlv.raw(x)} : Result<&2, &2, E.Asn1Error, B.Octets>}:
  match res:
    case Fail{er}:
      Empty.absurd({En.Asn1.encode(A.Asn1Tlv.node(x)) == Done{A.Asn1Tlv.raw(x)} : Result<&2, &2, E.Asn1Error, B.Octets>}, PS.ps.rfd(er, A.Asn1TlvRead{x, rest}, e))
    case Done{A.A1Out{Nil{}, r2}}:
      Empty.absurd({En.Asn1.encode(A.Asn1Tlv.node(x)) == Done{A.Asn1Tlv.raw(x)} : Result<&2, &2, E.Asn1Error, B.Octets>}, hsg)
    case Done{A.A1Out{Con{n, Con{y, t}}, r2}}:
      Empty.absurd({En.Asn1.encode(A.Asn1Tlv.node(x)) == Done{A.Asn1Tlv.raw(x)} : Result<&2, &2, E.Asn1Error, B.Octets>}, hsg)
    case Done{A.A1Out{Con{+n, Nil{}}, +r2}}:
      +z = A.a1.tlv.out(xs, Done{A.A1Out{[n], r2}})
      +ex = Equal.cong(Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>, A.Asn1Tlv, q => pd.rd_tlv(q), z, Done{A.Asn1TlvRead{x, rest}}, e)
      %ex : {En.Asn1.encode(A.Asn1Tlv.node(_)) == Done{A.Asn1Tlv.raw(_)} : Result<&2, &2, E.Asn1Error, B.Octets>}
      +ee = En.a1.enc_list([n], r2)
      +hg2 : {PC.PcPk{ee, En.a1.enc_err([n])} == PC.PcPk{xs, None{}} : PC.PcPk} = hg
      +henc = Equal.cong(PC.PcPk, List<&2, U32>, q => PC.pc.pb(q), PC.PcPk{ee, En.a1.enc_err([n])}, PC.PcPk{xs, None{}}, hg2)
      +herr = Equal.cong(PC.PcPk, Maybe<&2, E.Asn1Error>, q => PC.pc.pe(q), PC.PcPk{ee, En.a1.enc_err([n])}, PC.PcPk{xs, None{}}, hg2)
      pd.der_fin(n, xs, r2, henc, herr)

# law read_der
def pd.read_der(+r: R.Asn1Rules, +hm: {R.Asn1Rules.min_length(r) == True{} : Bool}, +hi: {R.Asn1Rules.indefinite(r) == False{} : Bool}, +b: B.Octets, +x: A.Asn1Tlv, +rest: B.Octets, +e: {A.Asn1.read(r, b) == Done{A.Asn1TlvRead{x, rest}} : Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>}) -> {En.Asn1.encode(A.Asn1Tlv.node(x)) == Done{A.Asn1Tlv.raw(x)} : Result<&2, &2, E.Asn1Error, B.Octets>}:
  +xs = B.Octets.to_list(b)
  +f = Nat.add(1n, List.length(&2, U32, xs))
  pd.tlvder(xs, A.a1.run(r, A.A1One{}, xs), pd.sg_dec(f, r, A.a1.head(r, xs)), PC.pc.dec_one(f, r, A.a1.head(r, xs), xs, {==}, AL.al.mask_to(b), hm, hi), x, rest, e)

# Re-tagging a constructed element

def pd.mdisc(m: Maybe<&2, E.Asn1Error>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{y}:
      Unit

def pd.mfd(-x: E.Asn1Error, e: {Some{x} == None{} : Maybe<&2, E.Asn1Error>}) -> Empty:
  %e : pd.mdisc(_)
  Unit{}

def pd.odisc(z: Result<&2, &2, E.Asn1Error, B.Octets>) -> Type:
  match z:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def pd.ofd(-x: E.Asn1Error, -y: B.Octets, e: {Fail{x} == Done{y} : Result<&2, &2, E.Asn1Error, B.Octets>}) -> Empty:
  %e : pd.odisc(_)
  Unit{}

def pd.oval(z: Result<&2, &2, E.Asn1Error, B.Octets>) -> B.Octets:
  match z:
    case Fail{x}:
      B.Octets.empty()
    case Done{v}:
      v

def pd.first_l(a: Maybe<&2, E.Asn1Error>, +b: Maybe<&2, E.Asn1Error>, +h: {En.a1.first(a, b) == None{} : Maybe<&2, E.Asn1Error>}) -> {a == None{} : Maybe<&2, E.Asn1Error>}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, E.Asn1Error>}, pd.mfd(x, h))

def pd.first_r(a: Maybe<&2, E.Asn1Error>, +b: Maybe<&2, E.Asn1Error>, +h: {En.a1.first(a, b) == None{} : Maybe<&2, E.Asn1Error>}) -> {b == None{} : Maybe<&2, E.Asn1Error>}:
  match a:
    case None{}:
      h
    case Some{x}:
      Empty.absurd({b == None{} : Maybe<&2, E.Asn1Error>}, pd.mfd(x, h))

def pd.pick_ok(u0: Bool, idok: Bool, ok: Bool, +h: {En.a1.node_err.pick(u0, idok, ok) == None{} : Maybe<&2, E.Asn1Error>}) -> {ok == True{} : Bool}:
  match u0 idok ok:
    case True{} _ _:
      Empty.absurd({ok == True{} : Bool}, pd.mfd(E.Asn1ReservedTag{}, h))
    case False{} False{} _:
      Empty.absurd({ok == True{} : Bool}, pd.mfd(E.Asn1BadTag{}, h))
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      Empty.absurd({False{} == True{} : Bool}, pd.mfd(E.Asn1TooLong{}, h))

# a tag other than [UNIVERSAL 0] is not reserved
def pd.u0(c: T.Asn1Class, +n: Nat, +hr: {T.Asn1Tag.is_eq(T.Asn1Tag{c, n}, T.Asn1Tag.universal(0n)) == False{} : Bool}) -> {En.a1.is_univ0(c, n) == False{} : Bool}:
  match c:
    case T.Asn1Universal{}:
      hr
    case T.Asn1Application{}:
      {==}
    case T.Asn1Context{}:
      {==}
    case T.Asn1Private{}:
      {==}

def pd.err_u(+c2: T.Asn1Class, +n2: Nat, +ns: List<&2, N.Asn1Node>, +hlen: {L.a1.len_ok(List.length(&2, U32, En.a1.enc_list(ns, Nil{}))) == True{} : Bool}, +hns: {En.a1.enc_err(ns) == None{} : Maybe<&2, E.Asn1Error>}, +hu: {Nat.is_lt(n2, 31n) == True{} : Bool}, +hr0: {En.a1.is_univ0(c2, n2) == False{} : Bool}) -> {En.a1.enc_err([N.Asn1Cons{T.Asn1Tag{c2, n2}, ns}]) == None{} : Maybe<&2, E.Asn1Error>}:
  +lv = List.length(&2, U32, En.a1.enc_list(ns, Nil{}))
  %Equal.sym(Bool, En.a1.is_univ0(c2, n2), False{}, hr0) : {En.a1.first(En.a1.node_err.pick(_, T.a1.id_ok(n2), L.a1.len_ok(lv)), En.a1.first(En.a1.enc_err(ns), None{})) == None{} : Maybe<&2, E.Asn1Error>}
  %Equal.sym(Bool, Nat.is_lt(n2, 31n), True{}, hu) : {En.a1.first(En.a1.node_err.pick(False{}, Bool.or(_, Nat.is_le(List.length(&2, U32, Nu.a1.b128(n2)), Nu.a1.max_octets())), L.a1.len_ok(lv)), En.a1.first(En.a1.enc_err(ns), None{})) == None{} : Maybe<&2, E.Asn1Error>}
  %Equal.sym(Bool, L.a1.len_ok(lv), True{}, hlen) : {En.a1.first(En.a1.node_err.pick(False{}, True{}, _), En.a1.first(En.a1.enc_err(ns), None{})) == None{} : Maybe<&2, E.Asn1Error>}
  %Equal.sym(Maybe<&2, E.Asn1Error>, En.a1.enc_err(ns), None{}, hns) : {En.a1.first(None{}, En.a1.first(_, None{})) == None{} : Maybe<&2, E.Asn1Error>}
  {==}

def pd.e2(+c2: T.Asn1Class, +n2: Nat, +ns: List<&2, N.Asn1Node>, +herr: {En.a1.enc_err([N.Asn1Cons{T.Asn1Tag{c2, n2}, ns}]) == None{} : Maybe<&2, E.Asn1Error>}) -> {En.Asn1.encode(N.Asn1Cons{T.Asn1Tag{c2, n2}, ns}) == Done{B.Octets.append(En.Asn1.identifier(T.Asn1Tag{c2, n2}, True{}), B.Octets.of_list(List.append(&2, U32, L.a1.len_bytes(List.length(&2, U32, En.a1.enc_list(ns, Nil{}))), List.append(&2, U32, En.a1.enc_list(ns, Nil{}), Nil{}))))} : Result<&2, &2, E.Asn1Error, B.Octets>}:
  +id2 = T.a1.id_bytes(c2, True{}, n2)
  +rest = List.append(&2, U32, L.a1.len_bytes(List.length(&2, U32, En.a1.enc_list(ns, Nil{}))), List.append(&2, U32, En.a1.enc_list(ns, Nil{}), Nil{}))
  %Equal.sym(Maybe<&2, E.Asn1Error>, En.a1.enc_err([N.Asn1Cons{T.Asn1Tag{c2, n2}, ns}]), None{}, herr) : {En.a1.encode.go(_, [N.Asn1Cons{T.Asn1Tag{c2, n2}, ns}]) == Done{B.Octets.append(B.Octets.of_list(id2), B.Octets.of_list(rest))} : Result<&2, &2, E.Asn1Error, B.Octets>}
  Equal.cong(B.Octets, Result<&2, &2, E.Asn1Error, B.Octets>, q => Done{q}, B.Octets.of_list(List.append(&2, U32, id2, rest)), B.Octets.append(B.Octets.of_list(id2), B.Octets.of_list(rest)), OA.oa.of_app(id2, rest))

def pd.retag_none(+c: T.Asn1Class, +n: Nat, +c2: T.Asn1Class, +n2: Nat, +ns: List<&2, N.Asn1Node>, +o: B.Octets, +hm: {En.a1.enc_err([N.Asn1Cons{T.Asn1Tag{c, n}, ns}]) == None{} : Maybe<&2, E.Asn1Error>}, +e: {Done{B.Octets.of_list(En.a1.enc_list([N.Asn1Cons{T.Asn1Tag{c, n}, ns}], Nil{}))} == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}, +hu: {Nat.is_lt(n2, 31n) == True{} : Bool}, +hr0: {En.a1.is_univ0(c2, n2) == False{} : Bool}) -> Sigma<&1, &1, B.Octets, l => {o == B.Octets.append(En.Asn1.identifier(T.Asn1Tag{c, n}, True{}), l) : B.Octets} & {En.Asn1.encode(N.Asn1Cons{T.Asn1Tag{c2, n2}, ns}) == Done{B.Octets.append(En.Asn1.identifier(T.Asn1Tag{c2, n2}, True{}), l)} : Result<&2, &2, E.Asn1Error, B.Octets>}>:
  +cs = En.a1.enc_list(ns, Nil{})
  +lv = List.length(&2, U32, cs)
  +id = T.a1.id_bytes(c, True{}, n)
  +rest = List.append(&2, U32, L.a1.len_bytes(lv), List.append(&2, U32, cs, Nil{}))
  +ha = pd.first_l(En.a1.node_err(c, n, lv), En.a1.first(En.a1.enc_err(ns), None{}), hm)
  +hb = pd.first_r(En.a1.node_err(c, n, lv), En.a1.first(En.a1.enc_err(ns), None{}), hm)
  +hns = pd.first_l(En.a1.enc_err(ns), None{}, hb)
  +hlen = pd.pick_ok(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(lv), ha)
  +eo = Equal.cong(Result<&2, &2, E.Asn1Error, B.Octets>, B.Octets, q => pd.oval(q), Done{B.Octets.of_list(List.append(&2, U32, id, rest))}, Done{o}, e)
  +e1 = Equal.trans(B.Octets, o, B.Octets.of_list(List.append(&2, U32, id, rest)), B.Octets.append(B.Octets.of_list(id), B.Octets.of_list(rest)), Equal.sym(B.Octets, B.Octets.of_list(List.append(&2, U32, id, rest)), o, eo), OA.oa.of_app(id, rest))
  (B.Octets.of_list(rest), (e1, pd.e2(c2, n2, ns, pd.err_u(c2, n2, ns, hlen, hns, hu, hr0))))

def pd.retag(m: Maybe<&2, E.Asn1Error>, +c: T.Asn1Class, +n: Nat, +c2: T.Asn1Class, +n2: Nat, +ns: List<&2, N.Asn1Node>, +o: B.Octets, +hm: {En.a1.enc_err([N.Asn1Cons{T.Asn1Tag{c, n}, ns}]) == m : Maybe<&2, E.Asn1Error>}, +e: {En.a1.encode.go(m, [N.Asn1Cons{T.Asn1Tag{c, n}, ns}]) == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}, +hu: {Nat.is_lt(n2, 31n) == True{} : Bool}, +hr0: {En.a1.is_univ0(c2, n2) == False{} : Bool}) -> Sigma<&1, &1, B.Octets, l => {o == B.Octets.append(En.Asn1.identifier(T.Asn1Tag{c, n}, True{}), l) : B.Octets} & {En.Asn1.encode(N.Asn1Cons{T.Asn1Tag{c2, n2}, ns}) == Done{B.Octets.append(En.Asn1.identifier(T.Asn1Tag{c2, n2}, True{}), l)} : Result<&2, &2, E.Asn1Error, B.Octets>}>:
  match m:
    case Some{x}:
      Empty.absurd(Sigma<&1, &1, B.Octets, l => {o == B.Octets.append(En.Asn1.identifier(T.Asn1Tag{c, n}, True{}), l) : B.Octets} & {En.Asn1.encode(N.Asn1Cons{T.Asn1Tag{c2, n2}, ns}) == Done{B.Octets.append(En.Asn1.identifier(T.Asn1Tag{c2, n2}, True{}), l)} : Result<&2, &2, E.Asn1Error, B.Octets>}>, pd.ofd(x, o, e))
    case None{}:
      pd.retag_none(c, n, c2, n2, ns, o, hm, e, hu, hr0)
