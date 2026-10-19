# Proofs for bend-osdev-asn1: DER encoding is unique. Under rules with the
# minimal-length check (which makes a1.head end in the canonical check,
# a1.canon) and without the indefinite form, a header read from octets xs
# says xs is the encoder's octets for the tag, form, contents and rest read
# (pc.head_prim, pc.head_def); so, by induction on the decoder's fuel, the
# elements decoded from xs encode back to xs (pc.dec_all, pc.dec_one), and
# can be encoded (no error).
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
import ./proof_within.bend as PW

# What a header says of its octets: they are the encoder's, and the element
# can be encoded
type PcHd is Data:
  PcHd{bytes: List<&2, U32>, ok: Bool}

def pc.hdb(h: PcHd) -> List<&2, U32>:
  match h:
    case PcHd{b, o}:
      b

def pc.hdo(h: PcHd) -> Bool:
  match h:
    case PcHd{b, o}:
      o

# What a decode says: one element (or more) and the octets after them encode
# back to the input, without error
type PcPk is Data:
  PcPk{bytes: List<&2, U32>, err: Maybe<&2, E.Asn1Error>}

type PcPk3 is Data:
  PcPk3{bytes: List<&2, U32>, err: Maybe<&2, E.Asn1Error>, rest: List<&2, U32>}

def pc.pb(p: PcPk) -> List<&2, U32>:
  match p:
    case PcPk{b, e}:
      b

def pc.pe(p: PcPk) -> Maybe<&2, E.Asn1Error>:
  match p:
    case PcPk{b, e}:
      e

def pc.p3b(p: PcPk3) -> List<&2, U32>:
  match p:
    case PcPk3{b, e, r}:
      b

def pc.p3e(p: PcPk3) -> Maybe<&2, E.Asn1Error>:
  match p:
    case PcPk3{b, e, r}:
      e

def pc.p3r(p: PcPk3) -> List<&2, U32>:
  match p:
    case PcPk3{b, e, r}:
      r

def pc.goodO(res: Result<&2, &2, E.Asn1Error, A.A1Out>, xs: List<&2, U32>) -> Type:
  match res:
    case Fail{e}:
      Unit
    case Done{A.A1Out{ns, rest}}:
      {PcPk{En.a1.enc_list(ns, rest), En.a1.enc_err(ns)} == PcPk{xs, None{}} : PcPk}

def pc.goodA(res: Result<&2, &2, E.Asn1Error, A.A1Out>, xs: List<&2, U32>) -> Type:
  match res:
    case Fail{e}:
      Unit
    case Done{A.A1Out{ns, rest}}:
      {PcPk3{En.a1.enc_list(ns, Nil{}), En.a1.enc_err(ns), rest} == PcPk3{xs, None{}, Nil{}} : PcPk3}

# Discriminating headers

def pc.notP(h: A.A1Head) -> Type:
  match h:
    case A.A1HPrim{t, cs, rest}:
      Empty
    case A.A1HDef{t, cs, rest}:
      Unit
    case A.A1HEnd{}:
      Unit
    case A.A1HEoc{rest}:
      Unit
    case A.A1HErr{e}:
      Unit
    case A.A1HIndef{t, rest}:
      Unit

def pc.notD(h: A.A1Head) -> Type:
  match h:
    case A.A1HPrim{t, cs, rest}:
      Unit
    case A.A1HDef{t, cs, rest}:
      Empty
    case A.A1HEnd{}:
      Unit
    case A.A1HEoc{rest}:
      Unit
    case A.A1HErr{e}:
      Unit
    case A.A1HIndef{t, rest}:
      Unit

def pc.notE(h: A.A1Head) -> Type:
  match h:
    case A.A1HPrim{t, cs, rest}:
      Unit
    case A.A1HDef{t, cs, rest}:
      Unit
    case A.A1HEnd{}:
      Empty
    case A.A1HEoc{rest}:
      Unit
    case A.A1HErr{e}:
      Unit
    case A.A1HIndef{t, rest}:
      Unit

def pc.notI(h: A.A1Head) -> Type:
  match h:
    case A.A1HPrim{t, cs, rest}:
      Unit
    case A.A1HDef{t, cs, rest}:
      Unit
    case A.A1HEnd{}:
      Unit
    case A.A1HEoc{rest}:
      Unit
    case A.A1HErr{e}:
      Unit
    case A.A1HIndef{t, rest}:
      Empty

def pc.htag(h: A.A1Head) -> T.Asn1Tag:
  match h:
    case A.A1HPrim{t, cs, rest}:
      t
    case A.A1HDef{t, cs, rest}:
      t
    case A.A1HEnd{}:
      T.Asn1Tag{T.Asn1Universal{}, 0n}
    case A.A1HEoc{rest}:
      T.Asn1Tag{T.Asn1Universal{}, 0n}
    case A.A1HErr{e}:
      T.Asn1Tag{T.Asn1Universal{}, 0n}
    case A.A1HIndef{t, rest}:
      t

def pc.hcs(h: A.A1Head) -> List<&2, U32>:
  match h:
    case A.A1HPrim{t, cs, rest}:
      cs
    case A.A1HDef{t, cs, rest}:
      cs
    case A.A1HEnd{}:
      Nil{}
    case A.A1HEoc{rest}:
      Nil{}
    case A.A1HErr{e}:
      Nil{}
    case A.A1HIndef{t, rest}:
      Nil{}

def pc.hrest(h: A.A1Head) -> List<&2, U32>:
  match h:
    case A.A1HPrim{t, cs, rest}:
      rest
    case A.A1HDef{t, cs, rest}:
      rest
    case A.A1HEnd{}:
      Nil{}
    case A.A1HEoc{rest}:
      rest
    case A.A1HErr{e}:
      Nil{}
    case A.A1HIndef{t, rest}:
      rest

def pc.tcls(t: T.Asn1Tag) -> T.Asn1Class:
  match t:
    case T.Asn1Tag{c, n}:
      c

def pc.tnum(t: T.Asn1Tag) -> Nat:
  match t:
    case T.Asn1Tag{c, n}:
      n

def pc.err_nprim(-er: E.Asn1Error, -c: T.Asn1Class, -n: Nat, -cs: List<&2, U32>, -rest: List<&2, U32>, e: {A.A1HErr{er} == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> Empty:
  %e : pc.notP(_)
  Unit{}

def pc.end_nprim(-c: T.Asn1Class, -n: Nat, -cs: List<&2, U32>, -rest: List<&2, U32>, e: {A.A1HEnd{} == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> Empty:
  %e : pc.notP(_)
  Unit{}

def pc.eoc_nprim(-r0: List<&2, U32>, -c: T.Asn1Class, -n: Nat, -cs: List<&2, U32>, -rest: List<&2, U32>, e: {A.A1HEoc{r0} == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> Empty:
  %e : pc.notP(_)
  Unit{}

def pc.ind_nprim(-t0: T.Asn1Tag, -r0: List<&2, U32>, -c: T.Asn1Class, -n: Nat, -cs: List<&2, U32>, -rest: List<&2, U32>, e: {A.A1HIndef{t0, r0} == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> Empty:
  %e : pc.notP(_)
  Unit{}

def pc.oth_nprim(-t0: T.Asn1Tag, -cs0: List<&2, U32>, -r0: List<&2, U32>, -c: T.Asn1Class, -n: Nat, -cs: List<&2, U32>, -rest: List<&2, U32>, e: {A.A1HDef{t0, cs0, r0} == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> Empty:
  %e : pc.notP(_)
  Unit{}

def pc.err_ndef(-er: E.Asn1Error, -c: T.Asn1Class, -n: Nat, -cs: List<&2, U32>, -rest: List<&2, U32>, e: {A.A1HErr{er} == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> Empty:
  %e : pc.notD(_)
  Unit{}

def pc.end_ndef(-c: T.Asn1Class, -n: Nat, -cs: List<&2, U32>, -rest: List<&2, U32>, e: {A.A1HEnd{} == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> Empty:
  %e : pc.notD(_)
  Unit{}

def pc.eoc_ndef(-r0: List<&2, U32>, -c: T.Asn1Class, -n: Nat, -cs: List<&2, U32>, -rest: List<&2, U32>, e: {A.A1HEoc{r0} == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> Empty:
  %e : pc.notD(_)
  Unit{}

def pc.ind_ndef(-t0: T.Asn1Tag, -r0: List<&2, U32>, -c: T.Asn1Class, -n: Nat, -cs: List<&2, U32>, -rest: List<&2, U32>, e: {A.A1HIndef{t0, r0} == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> Empty:
  %e : pc.notD(_)
  Unit{}

def pc.oth_ndef(-t0: T.Asn1Tag, -cs0: List<&2, U32>, -r0: List<&2, U32>, -c: T.Asn1Class, -n: Nat, -cs: List<&2, U32>, -rest: List<&2, U32>, e: {A.A1HPrim{t0, cs0, r0} == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> Empty:
  %e : pc.notD(_)
  Unit{}

# the canonical check passed: the octets are the encoder's
def pc.cmk_prim(ok: Bool, +c0: T.Asn1Class, +n0: Nat, +l: Nat, +xs: List<&2, U32>, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +eok: {A.a1.canon.ok(c0, False{}, n0, l, xs) == ok : Bool}, +e: {A.a1.canon.mk(ok, T.Asn1Tag{c0, n0}, False{}, List.length(&2, U32, A.a1.hdr(c0, False{}, n0, l)), l, xs) == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> {PcHd{En.a1.tlv(c, False{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}:
  match ok:
    case False{}:
      Empty.absurd({PcHd{En.a1.tlv(c, False{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}, pc.err_nprim(E.Asn1NonMinimalLength{}, c, n, cs, rest, e))
    case True{}:
      +id = T.a1.id_bytes(c0, False{}, n0)
      +lb = L.a1.len_bytes(l)
      +hd = A.a1.hdr(c0, False{}, n0, l)
      +k = List.length(&2, U32, hd)
      +d = B.drop(k, xs)
      +cs0 = B.take(l, d)
      +r0 = B.drop(l, d)
      +h0 : A.A1Head = A.A1HPrim{T.Asn1Tag{c0, n0}, cs0, r0}
      +hw : A.A1Head = A.A1HPrim{T.Asn1Tag{c, n}, cs, rest}
      +etag = Equal.cong(A.A1Head, T.Asn1Tag, z => pc.htag(z), h0, hw, e)
      +ec = Equal.cong(T.Asn1Tag, T.Asn1Class, z => pc.tcls(z), T.Asn1Tag{c0, n0}, T.Asn1Tag{c, n}, etag)
      +en = Equal.cong(T.Asn1Tag, Nat, z => pc.tnum(z), T.Asn1Tag{c0, n0}, T.Asn1Tag{c, n}, etag)
      +ecs = Equal.cong(A.A1Head, List<&2, U32>, z => pc.hcs(z), h0, hw, e)
      +er = Equal.cong(A.A1Head, List<&2, U32>, z => pc.hrest(z), h0, hw, e)
      %ec : {PcHd{En.a1.tlv(_, False{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(_, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}
      %en : {PcHd{En.a1.tlv(c0, False{}, _, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c0, _)), Bool.and(T.a1.id_ok(_), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}
      %ecs : {PcHd{En.a1.tlv(c0, False{}, n0, _, rest), Bool.and(Bool.not(En.a1.is_univ0(c0, n0)), Bool.and(T.a1.id_ok(n0), L.a1.len_ok(List.length(&2, U32, _))))} == PcHd{xs, True{}} : PcHd}
      %er : {PcHd{En.a1.tlv(c0, False{}, n0, cs0, _), Bool.and(Bool.not(En.a1.is_univ0(c0, n0)), Bool.and(T.a1.id_ok(n0), L.a1.len_ok(List.length(&2, U32, cs0))))} == PcHd{xs, True{}} : PcHd}
      +a1 = Bool.not(En.a1.is_univ0(c0, n0))
      +a0 = T.a1.id_ok(n0)
      +a2 = L.a1.len_ok(l)
      +a3 = Nu.a1.leq(hd, B.take(k, xs))
      +a4 = Nat.is_le(l, List.length(&2, U32, d))
      +f1 = AN.an.and_l(a1, Bool.and(a0, Bool.and(a2, Bool.and(a3, a4))), eok)
      +f0234 = AN.an.and_r(a1, Bool.and(a0, Bool.and(a2, Bool.and(a3, a4))), eok)
      +f0 = AN.an.and_l(a0, Bool.and(a2, Bool.and(a3, a4)), f0234)
      +f234 = AN.an.and_r(a0, Bool.and(a2, Bool.and(a3, a4)), f0234)
      +f2 = AN.an.and_l(a2, Bool.and(a3, a4), f234)
      +f34 = AN.an.and_r(a2, Bool.and(a3, a4), f234)
      +f3 = AN.an.and_l(a3, a4, f34)
      +f4 = AN.an.and_r(a3, a4, f34)
      +x1 = List.append(&2, U32, cs0, r0)
      %Equal.sym(Nat, List.length(&2, U32, cs0), l, AL.al.len_take(l, d, f4)) : {PcHd{List.append(&2, U32, id, List.append(&2, U32, L.a1.len_bytes(_), x1)), Bool.and(a1, Bool.and(a0, L.a1.len_ok(_)))} == PcHd{xs, True{}} : PcHd}
      %Equal.sym(Bool, a1, True{}, f1) : {PcHd{List.append(&2, U32, id, List.append(&2, U32, lb, x1)), Bool.and(_, Bool.and(a0, a2))} == PcHd{xs, True{}} : PcHd}
      %Equal.sym(Bool, a0, True{}, f0) : {PcHd{List.append(&2, U32, id, List.append(&2, U32, lb, x1)), Bool.and(_, a2)} == PcHd{xs, True{}} : PcHd}
      %Equal.sym(Bool, a2, True{}, f2) : {PcHd{List.append(&2, U32, id, List.append(&2, U32, lb, x1)), _} == PcHd{xs, True{}} : PcHd}
      %AL.al.take_drop(k, xs) : {PcHd{List.append(&2, U32, id, List.append(&2, U32, lb, x1)), True{}} == PcHd{_, True{}} : PcHd}
      %AU.au.leq_sound(hd, B.take(k, xs), f3) : {PcHd{List.append(&2, U32, id, List.append(&2, U32, lb, x1)), True{}} == PcHd{List.append(&2, U32, _, d), True{}} : PcHd}
      %AL.al.take_drop(l, d) : {PcHd{List.append(&2, U32, id, List.append(&2, U32, lb, x1)), True{}} == PcHd{List.append(&2, U32, hd, _), True{}} : PcHd}
      %AL.al.app_assoc(id, lb, x1) : {PcHd{_, True{}} == PcHd{List.append(&2, U32, hd, x1), True{}} : PcHd}
      {==}

def pc.cmkx_prim(ok: Bool, +c0: T.Asn1Class, +n0: Nat, +k: Nat, +l: Nat, +xs: List<&2, U32>, -c: T.Asn1Class, -n: Nat, -cs: List<&2, U32>, -rest: List<&2, U32>, +e: {A.a1.canon.mk(ok, T.Asn1Tag{c0, n0}, True{}, k, l, xs) == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> Empty:
  match ok:
    case False{}:
      pc.err_nprim(E.Asn1NonMinimalLength{}, c, n, cs, rest, e)
    case True{}:
      pc.oth_nprim(T.Asn1Tag{c0, n0}, B.take(l, B.drop(k, xs)), B.drop(l, B.drop(k, xs)), c, n, cs, rest, e)

# a header that passed the canonical check
def pc.canon_prim(+xs: List<&2, U32>, h: A.A1Head, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +e: {A.a1.canon(xs, h) == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> {PcHd{En.a1.tlv(c, False{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}:
  match h:
    case A.A1HPrim{T.Asn1Tag{+c0, +n0}, +cs0, r0}:
      +l = List.length(&2, U32, cs0)
      pc.cmk_prim(A.a1.canon.ok(c0, False{}, n0, l, xs), c0, n0, l, xs, c, n, cs, rest, {==}, e)
    case A.A1HDef{T.Asn1Tag{+c0, +n0}, +cs0, r0}:
      +l = List.length(&2, U32, cs0)
      Empty.absurd({PcHd{En.a1.tlv(c, False{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}, pc.cmkx_prim(A.a1.canon.ok(c0, True{}, n0, l, xs), c0, n0, List.length(&2, U32, A.a1.hdr(c0, True{}, n0, l)), l, xs, c, n, cs, rest, e))
    case A.A1HEnd{}:
      Empty.absurd({PcHd{En.a1.tlv(c, False{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}, pc.end_nprim(c, n, cs, rest, e))
    case A.A1HEoc{r0}:
      Empty.absurd({PcHd{En.a1.tlv(c, False{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}, pc.eoc_nprim(r0, c, n, cs, rest, e))
    case A.A1HErr{er}:
      Empty.absurd({PcHd{En.a1.tlv(c, False{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}, pc.err_nprim(er, c, n, cs, rest, e))
    case A.A1HIndef{t0, r0}:
      Empty.absurd({PcHd{En.a1.tlv(c, False{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}, pc.ind_nprim(t0, r0, c, n, cs, rest, e))

def pc.nend_prim(xs: List<&2, U32>, h: A.A1Head, -c: T.Asn1Class, -n: Nat, -cs: List<&2, U32>, -rest: List<&2, U32>, +e: {A.a1.head.nend(xs, h) == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> {h == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}:
  match xs:
    case Nil{}:
      e
    case Con{y, t}:
      match h:
        case A.A1HEnd{}:
          Empty.absurd({A.A1HEnd{} == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}, pc.err_nprim(E.Asn1Truncated{}, c, n, cs, rest, e))
        case A.A1HEoc{r0}:
          e
        case A.A1HErr{er}:
          e
        case A.A1HPrim{u, cs0, r0}:
          e
        case A.A1HDef{u, cs0, r0}:
          e
        case A.A1HIndef{u, r0}:
          e

# under the minimal-length rule, a header read says its octets are the
# encoder's octets
def pc.head_prim(+r: R.Asn1Rules, +xs: List<&2, U32>, +hm: {R.Asn1Rules.min_length(r) == True{} : Bool}, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +e: {A.a1.head(r, xs) == A.A1HPrim{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> {PcHd{En.a1.tlv(c, False{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}:
  +h1 = A.a1.head.indef_off(R.Asn1Rules.indefinite(r), A.a1.head0(r, xs))
  +e2 = pc.nend_prim(xs, A.a1.head.fin(r, xs, A.a1.head0(r, xs)), c, n, cs, rest, e)
  +e3 = Equal.trans(A.A1Head, A.a1.canon(xs, h1), A.a1.head.fin2(R.Asn1Rules.min_length(r), xs, h1), A.A1HPrim{T.Asn1Tag{c, n}, cs, rest}, Equal.cong(Bool, A.A1Head, z => A.a1.head.fin2(z, xs, h1), True{}, R.Asn1Rules.min_length(r), Equal.sym(Bool, R.Asn1Rules.min_length(r), True{}, hm)), e2)
  pc.canon_prim(xs, h1, c, n, cs, rest, e3)

# the canonical check passed: the octets are the encoder's
def pc.cmk_def(ok: Bool, +c0: T.Asn1Class, +n0: Nat, +l: Nat, +xs: List<&2, U32>, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +eok: {A.a1.canon.ok(c0, True{}, n0, l, xs) == ok : Bool}, +e: {A.a1.canon.mk(ok, T.Asn1Tag{c0, n0}, True{}, List.length(&2, U32, A.a1.hdr(c0, True{}, n0, l)), l, xs) == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> {PcHd{En.a1.tlv(c, True{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}:
  match ok:
    case False{}:
      Empty.absurd({PcHd{En.a1.tlv(c, True{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}, pc.err_ndef(E.Asn1NonMinimalLength{}, c, n, cs, rest, e))
    case True{}:
      +id = T.a1.id_bytes(c0, True{}, n0)
      +lb = L.a1.len_bytes(l)
      +hd = A.a1.hdr(c0, True{}, n0, l)
      +k = List.length(&2, U32, hd)
      +d = B.drop(k, xs)
      +cs0 = B.take(l, d)
      +r0 = B.drop(l, d)
      +h0 : A.A1Head = A.A1HDef{T.Asn1Tag{c0, n0}, cs0, r0}
      +hw : A.A1Head = A.A1HDef{T.Asn1Tag{c, n}, cs, rest}
      +etag = Equal.cong(A.A1Head, T.Asn1Tag, z => pc.htag(z), h0, hw, e)
      +ec = Equal.cong(T.Asn1Tag, T.Asn1Class, z => pc.tcls(z), T.Asn1Tag{c0, n0}, T.Asn1Tag{c, n}, etag)
      +en = Equal.cong(T.Asn1Tag, Nat, z => pc.tnum(z), T.Asn1Tag{c0, n0}, T.Asn1Tag{c, n}, etag)
      +ecs = Equal.cong(A.A1Head, List<&2, U32>, z => pc.hcs(z), h0, hw, e)
      +er = Equal.cong(A.A1Head, List<&2, U32>, z => pc.hrest(z), h0, hw, e)
      %ec : {PcHd{En.a1.tlv(_, True{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(_, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}
      %en : {PcHd{En.a1.tlv(c0, True{}, _, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c0, _)), Bool.and(T.a1.id_ok(_), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}
      %ecs : {PcHd{En.a1.tlv(c0, True{}, n0, _, rest), Bool.and(Bool.not(En.a1.is_univ0(c0, n0)), Bool.and(T.a1.id_ok(n0), L.a1.len_ok(List.length(&2, U32, _))))} == PcHd{xs, True{}} : PcHd}
      %er : {PcHd{En.a1.tlv(c0, True{}, n0, cs0, _), Bool.and(Bool.not(En.a1.is_univ0(c0, n0)), Bool.and(T.a1.id_ok(n0), L.a1.len_ok(List.length(&2, U32, cs0))))} == PcHd{xs, True{}} : PcHd}
      +a1 = Bool.not(En.a1.is_univ0(c0, n0))
      +a0 = T.a1.id_ok(n0)
      +a2 = L.a1.len_ok(l)
      +a3 = Nu.a1.leq(hd, B.take(k, xs))
      +a4 = Nat.is_le(l, List.length(&2, U32, d))
      +f1 = AN.an.and_l(a1, Bool.and(a0, Bool.and(a2, Bool.and(a3, a4))), eok)
      +f0234 = AN.an.and_r(a1, Bool.and(a0, Bool.and(a2, Bool.and(a3, a4))), eok)
      +f0 = AN.an.and_l(a0, Bool.and(a2, Bool.and(a3, a4)), f0234)
      +f234 = AN.an.and_r(a0, Bool.and(a2, Bool.and(a3, a4)), f0234)
      +f2 = AN.an.and_l(a2, Bool.and(a3, a4), f234)
      +f34 = AN.an.and_r(a2, Bool.and(a3, a4), f234)
      +f3 = AN.an.and_l(a3, a4, f34)
      +f4 = AN.an.and_r(a3, a4, f34)
      +x1 = List.append(&2, U32, cs0, r0)
      %Equal.sym(Nat, List.length(&2, U32, cs0), l, AL.al.len_take(l, d, f4)) : {PcHd{List.append(&2, U32, id, List.append(&2, U32, L.a1.len_bytes(_), x1)), Bool.and(a1, Bool.and(a0, L.a1.len_ok(_)))} == PcHd{xs, True{}} : PcHd}
      %Equal.sym(Bool, a1, True{}, f1) : {PcHd{List.append(&2, U32, id, List.append(&2, U32, lb, x1)), Bool.and(_, Bool.and(a0, a2))} == PcHd{xs, True{}} : PcHd}
      %Equal.sym(Bool, a0, True{}, f0) : {PcHd{List.append(&2, U32, id, List.append(&2, U32, lb, x1)), Bool.and(_, a2)} == PcHd{xs, True{}} : PcHd}
      %Equal.sym(Bool, a2, True{}, f2) : {PcHd{List.append(&2, U32, id, List.append(&2, U32, lb, x1)), _} == PcHd{xs, True{}} : PcHd}
      %AL.al.take_drop(k, xs) : {PcHd{List.append(&2, U32, id, List.append(&2, U32, lb, x1)), True{}} == PcHd{_, True{}} : PcHd}
      %AU.au.leq_sound(hd, B.take(k, xs), f3) : {PcHd{List.append(&2, U32, id, List.append(&2, U32, lb, x1)), True{}} == PcHd{List.append(&2, U32, _, d), True{}} : PcHd}
      %AL.al.take_drop(l, d) : {PcHd{List.append(&2, U32, id, List.append(&2, U32, lb, x1)), True{}} == PcHd{List.append(&2, U32, hd, _), True{}} : PcHd}
      %AL.al.app_assoc(id, lb, x1) : {PcHd{_, True{}} == PcHd{List.append(&2, U32, hd, x1), True{}} : PcHd}
      {==}

def pc.cmkx_def(ok: Bool, +c0: T.Asn1Class, +n0: Nat, +k: Nat, +l: Nat, +xs: List<&2, U32>, -c: T.Asn1Class, -n: Nat, -cs: List<&2, U32>, -rest: List<&2, U32>, +e: {A.a1.canon.mk(ok, T.Asn1Tag{c0, n0}, False{}, k, l, xs) == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> Empty:
  match ok:
    case False{}:
      pc.err_ndef(E.Asn1NonMinimalLength{}, c, n, cs, rest, e)
    case True{}:
      pc.oth_ndef(T.Asn1Tag{c0, n0}, B.take(l, B.drop(k, xs)), B.drop(l, B.drop(k, xs)), c, n, cs, rest, e)

# a header that passed the canonical check
def pc.canon_def(+xs: List<&2, U32>, h: A.A1Head, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +e: {A.a1.canon(xs, h) == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> {PcHd{En.a1.tlv(c, True{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}:
  match h:
    case A.A1HPrim{T.Asn1Tag{+c0, +n0}, +cs0, r0}:
      +l = List.length(&2, U32, cs0)
      Empty.absurd({PcHd{En.a1.tlv(c, True{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}, pc.cmkx_def(A.a1.canon.ok(c0, False{}, n0, l, xs), c0, n0, List.length(&2, U32, A.a1.hdr(c0, False{}, n0, l)), l, xs, c, n, cs, rest, e))
    case A.A1HDef{T.Asn1Tag{+c0, +n0}, +cs0, r0}:
      +l = List.length(&2, U32, cs0)
      pc.cmk_def(A.a1.canon.ok(c0, True{}, n0, l, xs), c0, n0, l, xs, c, n, cs, rest, {==}, e)
    case A.A1HEnd{}:
      Empty.absurd({PcHd{En.a1.tlv(c, True{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}, pc.end_ndef(c, n, cs, rest, e))
    case A.A1HEoc{r0}:
      Empty.absurd({PcHd{En.a1.tlv(c, True{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}, pc.eoc_ndef(r0, c, n, cs, rest, e))
    case A.A1HErr{er}:
      Empty.absurd({PcHd{En.a1.tlv(c, True{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}, pc.err_ndef(er, c, n, cs, rest, e))
    case A.A1HIndef{t0, r0}:
      Empty.absurd({PcHd{En.a1.tlv(c, True{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}, pc.ind_ndef(t0, r0, c, n, cs, rest, e))

def pc.nend_def(xs: List<&2, U32>, h: A.A1Head, -c: T.Asn1Class, -n: Nat, -cs: List<&2, U32>, -rest: List<&2, U32>, +e: {A.a1.head.nend(xs, h) == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> {h == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}:
  match xs:
    case Nil{}:
      e
    case Con{y, t}:
      match h:
        case A.A1HEnd{}:
          Empty.absurd({A.A1HEnd{} == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}, pc.err_ndef(E.Asn1Truncated{}, c, n, cs, rest, e))
        case A.A1HEoc{r0}:
          e
        case A.A1HErr{er}:
          e
        case A.A1HPrim{u, cs0, r0}:
          e
        case A.A1HDef{u, cs0, r0}:
          e
        case A.A1HIndef{u, r0}:
          e

# under the minimal-length rule, a header read says its octets are the
# encoder's octets
def pc.head_def(+r: R.Asn1Rules, +xs: List<&2, U32>, +hm: {R.Asn1Rules.min_length(r) == True{} : Bool}, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +e: {A.a1.head(r, xs) == A.A1HDef{T.Asn1Tag{c, n}, cs, rest} : A.A1Head}) -> {PcHd{En.a1.tlv(c, True{}, n, cs, rest), Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))} == PcHd{xs, True{}} : PcHd}:
  +h1 = A.a1.head.indef_off(R.Asn1Rules.indefinite(r), A.a1.head0(r, xs))
  +e2 = pc.nend_def(xs, A.a1.head.fin(r, xs, A.a1.head0(r, xs)), c, n, cs, rest, e)
  +e3 = Equal.trans(A.A1Head, A.a1.canon(xs, h1), A.a1.head.fin2(R.Asn1Rules.min_length(r), xs, h1), A.A1HDef{T.Asn1Tag{c, n}, cs, rest}, Equal.cong(Bool, A.A1Head, z => A.a1.head.fin2(z, xs, h1), True{}, R.Asn1Rules.min_length(r), Equal.sym(Bool, R.Asn1Rules.min_length(r), True{}, hm)), e2)
  pc.canon_def(xs, h1, c, n, cs, rest, e3)

# Headers that are not the end, or not indefinite

def pc.nend_ne(+y: U32, +t: List<&2, U32>, h: A.A1Head, +e: {A.a1.head.nend(Con{y, t}, h) == A.A1HEnd{} : A.A1Head}) -> Empty:
  match h:
    case A.A1HEnd{}:
      %e : pc.notE(_)
      Unit{}
    case A.A1HEoc{r0}:
      %e : pc.notE(_)
      Unit{}
    case A.A1HErr{er}:
      %e : pc.notE(_)
      Unit{}
    case A.A1HPrim{u, cs, r0}:
      %e : pc.notE(_)
      Unit{}
    case A.A1HDef{u, cs, r0}:
      %e : pc.notE(_)
      Unit{}
    case A.A1HIndef{u, r0}:
      %e : pc.notE(_)
      Unit{}

# the end of the input is read only from no octets
def pc.end_inv(+r: R.Asn1Rules, xs: List<&2, U32>, +e: {A.a1.head(r, xs) == A.A1HEnd{} : A.A1Head}) -> {Nil{} == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      Empty.absurd({Nil{} == Con{y, t} : List<&2, U32>}, pc.nend_ne(y, t, A.a1.head.fin(r, Con{y, t}, A.a1.head0(r, Con{y, t})), e))

def pc.ni(h: A.A1Head) -> Bool:
  match h:
    case A.A1HIndef{t, rest}:
      False{}
    case A.A1HEnd{}:
      True{}
    case A.A1HEoc{rest}:
      True{}
    case A.A1HErr{e}:
      True{}
    case A.A1HPrim{t, cs, rest}:
      True{}
    case A.A1HDef{t, cs, rest}:
      True{}

def pc.ioff_ni(h: A.A1Head) -> {pc.ni(A.a1.head.indef_off(False{}, h)) == True{} : Bool}:
  match h:
    case A.A1HIndef{t, rest}:
      {==}
    case A.A1HEnd{}:
      {==}
    case A.A1HEoc{rest}:
      {==}
    case A.A1HErr{e}:
      {==}
    case A.A1HPrim{t, cs, rest}:
      {==}
    case A.A1HDef{t, cs, rest}:
      {==}

def pc.cmk_ni(ok: Bool, +t: T.Asn1Tag, cons: Bool, +k: Nat, +l: Nat, +xs: List<&2, U32>) -> {pc.ni(A.a1.canon.mk(ok, t, cons, k, l, xs)) == True{} : Bool}:
  match ok cons:
    case False{} _:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def pc.canon_ni(+xs: List<&2, U32>, h: A.A1Head, +hn: {pc.ni(h) == True{} : Bool}) -> {pc.ni(A.a1.canon(xs, h)) == True{} : Bool}:
  match h:
    case A.A1HPrim{T.Asn1Tag{+c, +n}, +cs, rest}:
      +l = List.length(&2, U32, cs)
      pc.cmk_ni(A.a1.canon.ok(c, False{}, n, l, xs), T.Asn1Tag{c, n}, False{}, List.length(&2, U32, A.a1.hdr(c, False{}, n, l)), l, xs)
    case A.A1HDef{T.Asn1Tag{+c, +n}, +cs, rest}:
      +l = List.length(&2, U32, cs)
      pc.cmk_ni(A.a1.canon.ok(c, True{}, n, l, xs), T.Asn1Tag{c, n}, True{}, List.length(&2, U32, A.a1.hdr(c, True{}, n, l)), l, xs)
    case A.A1HEnd{}:
      {==}
    case A.A1HEoc{rest}:
      {==}
    case A.A1HErr{e}:
      {==}
    case A.A1HIndef{t, rest}:
      hn

def pc.fin2_ni(m: Bool, +xs: List<&2, U32>, h: A.A1Head, +hn: {pc.ni(h) == True{} : Bool}) -> {pc.ni(A.a1.head.fin2(m, xs, h)) == True{} : Bool}:
  match m:
    case True{}:
      pc.canon_ni(xs, h, hn)
    case False{}:
      hn

def pc.nend_ni(xs: List<&2, U32>, h: A.A1Head, +hn: {pc.ni(h) == True{} : Bool}) -> {pc.ni(A.a1.head.nend(xs, h)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hn
    case Con{y, t}:
      match h:
        case A.A1HIndef{u, rest}:
          hn
        case A.A1HEnd{}:
          {==}
        case A.A1HEoc{rest}:
          {==}
        case A.A1HErr{e}:
          {==}
        case A.A1HPrim{u, cs, rest}:
          {==}
        case A.A1HDef{u, cs, rest}:
          {==}

# without the indefinite form, no header is indefinite
def pc.head_ni(+r: R.Asn1Rules, +xs: List<&2, U32>, +hi: {R.Asn1Rules.indefinite(r) == False{} : Bool}) -> {pc.ni(A.a1.head(r, xs)) == True{} : Bool}:
  +h0 = A.a1.head0(r, xs)
  +hf = Equal.trans(Bool, pc.ni(A.a1.head.fin2(R.Asn1Rules.min_length(r), xs, A.a1.head.indef_off(R.Asn1Rules.indefinite(r), h0))), pc.ni(A.a1.head.fin2(R.Asn1Rules.min_length(r), xs, A.a1.head.indef_off(False{}, h0))), True{}, Equal.cong(Bool, Bool, z => pc.ni(A.a1.head.fin2(R.Asn1Rules.min_length(r), xs, A.a1.head.indef_off(z, h0))), R.Asn1Rules.indefinite(r), False{}, hi), pc.fin2_ni(R.Asn1Rules.min_length(r), xs, A.a1.head.indef_off(False{}, h0), pc.ioff_ni(h0)))
  pc.nend_ni(xs, A.a1.head.fin(r, xs, h0), hf)

def pc.head_indef(+r: R.Asn1Rules, +xs: List<&2, U32>, +hi: {R.Asn1Rules.indefinite(r) == False{} : Bool}, -t: T.Asn1Tag, -rest: List<&2, U32>, +e: {A.a1.head(r, xs) == A.A1HIndef{t, rest} : A.A1Head}) -> Empty:
  AN.an.ft(Equal.trans(Bool, False{}, pc.ni(A.a1.head(r, xs)), True{}, Equal.sym(Bool, pc.ni(A.a1.head(r, xs)), False{}, Equal.cong(A.A1Head, Bool, z => pc.ni(z), A.a1.head(r, xs), A.A1HIndef{t, rest}, e)), pc.head_ni(r, xs, hi)))

# The contents and the rest of an element read are masked, as its input was

def pc.fix_cs(+c: T.Asn1Class, +cons: Bool, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +xs: List<&2, U32>, +hx: {En.a1.tlv(c, cons, n, cs, rest) == xs : List<&2, U32>}, +hmask: {B.mask(xs) == xs : List<&2, U32>}) -> {B.mask(cs) == cs : List<&2, U32>}:
  +x0 = En.a1.tlv(c, cons, n, cs, rest)
  +id = T.a1.id_bytes(c, cons, n)
  +lb = L.a1.len_bytes(List.length(&2, U32, cs))
  +y = List.append(&2, U32, cs, rest)
  +h0 = Equal.trans(List<&2, U32>, B.mask(x0), B.mask(xs), x0, Equal.cong(List<&2, U32>, List<&2, U32>, z => B.mask(z), x0, xs, hx), Equal.trans(List<&2, U32>, B.mask(xs), xs, x0, hmask, Equal.sym(List<&2, U32>, x0, xs, hx)))
  AL.al.fixed_l(cs, rest, AL.al.fixed_r(lb, y, AL.al.fixed_r(id, List.append(&2, U32, lb, y), h0)))

def pc.fix_rest(+c: T.Asn1Class, +cons: Bool, +n: Nat, +cs: List<&2, U32>, +rest: List<&2, U32>, +xs: List<&2, U32>, +hx: {En.a1.tlv(c, cons, n, cs, rest) == xs : List<&2, U32>}, +hmask: {B.mask(xs) == xs : List<&2, U32>}) -> {B.mask(rest) == rest : List<&2, U32>}:
  +x0 = En.a1.tlv(c, cons, n, cs, rest)
  +id = T.a1.id_bytes(c, cons, n)
  +lb = L.a1.len_bytes(List.length(&2, U32, cs))
  +y = List.append(&2, U32, cs, rest)
  +h0 = Equal.trans(List<&2, U32>, B.mask(x0), B.mask(xs), x0, Equal.cong(List<&2, U32>, List<&2, U32>, z => B.mask(z), x0, xs, hx), Equal.trans(List<&2, U32>, B.mask(xs), xs, x0, hmask, Equal.sym(List<&2, U32>, x0, xs, hx)))
  AL.al.fixed_r(cs, rest, AL.al.fixed_r(lb, y, AL.al.fixed_r(id, List.append(&2, U32, lb, y), h0)))


# One primitive element, then the elements after it

def pc.moreA_prim(ok: Bool, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest1: List<&2, U32>, +xs: List<&2, U32>, b: Result<&2, &2, E.Asn1Error, A.A1Out>, +hx: {En.a1.tlv(c, False{}, n, cs, rest1) == xs : List<&2, U32>}, +hb: {Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)))) == True{} : Bool}, +hmc: {B.mask(cs) == cs : List<&2, U32>}, hg: pc.goodA(b, rest1)) -> pc.goodA(A.a1.more(A.a1.mk_prim.pick(ok, T.Asn1Tag{c, n}, B.Octets.of_list(cs)), b), xs):
  match ok b:
    case False{} _:
      Unit{}
    case True{} Fail{e}:
      Unit{}
    case True{} Done{A.A1Out{+ns, +r2}}:
      +o = B.Octets.of_list(cs)
      +er = En.a1.enc_list(ns, Nil{})
      +ee = En.a1.enc_err(ns)
      +pk : PcPk3 = PcPk3{er, ee, r2}
      +hg2 : {pk == PcPk3{rest1, None{}, Nil{}} : PcPk3} = hg
      +want : PcPk3 = PcPk3{xs, None{}, Nil{}}
  +hu = AN.an.not_t(En.a1.is_univ0(c, n), AN.an.and_l(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), hb))
  +hb2 = AN.an.and_r(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), hb)
  +hid = AN.an.and_l(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)), hb2)
  +hl = AN.an.and_r(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)), hb2)
      +gb = Equal.cong(PcPk3, List<&2, U32>, z => pc.p3b(z), pk, PcPk3{rest1, None{}, Nil{}}, hg2)
      +ge = Equal.cong(PcPk3, Maybe<&2, E.Asn1Error>, z => pc.p3e(z), pk, PcPk3{rest1, None{}, Nil{}}, hg2)
      +gr = Equal.cong(PcPk3, List<&2, U32>, z => pc.p3r(z), pk, PcPk3{rest1, None{}, Nil{}}, hg2)
      +eto = Equal.trans(List<&2, U32>, cs, B.mask(cs), B.Octets.to_list(o), Equal.sym(List<&2, U32>, B.mask(cs), cs, hmc), Equal.sym(List<&2, U32>, B.Octets.to_list(o), B.mask(cs), AL.al.to_of(cs)))
      %eto : {PcPk3{En.a1.tlv(c, False{}, n, _, er), En.a1.first(En.a1.node_err.pick(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(B.Octets.len(o))), ee), r2} == want : PcPk3}
      %Equal.sym(Nat, B.Octets.len(o), List.length(&2, U32, cs), PW.pw.olen_of(cs)) : {PcPk3{En.a1.tlv(c, False{}, n, cs, er), En.a1.first(En.a1.node_err.pick(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(_)), ee), r2} == want : PcPk3}
      %Equal.sym(List<&2, U32>, er, rest1, gb) : {PcPk3{En.a1.tlv(c, False{}, n, cs, _), En.a1.first(En.a1.node_err.pick(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), ee), r2} == want : PcPk3}
      %Equal.sym(Maybe<&2, E.Asn1Error>, ee, None{}, ge) : {PcPk3{En.a1.tlv(c, False{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), _), r2} == want : PcPk3}
      %Equal.sym(List<&2, U32>, r2, Nil{}, gr) : {PcPk3{En.a1.tlv(c, False{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), None{}), _} == want : PcPk3}
      %Equal.sym(Bool, En.a1.is_univ0(c, n), False{}, hu) : {PcPk3{En.a1.tlv(c, False{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(_, T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), None{}), Nil{}} == want : PcPk3}
      %Equal.sym(Bool, T.a1.id_ok(n), True{}, hid) : {PcPk3{En.a1.tlv(c, False{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(False{}, _, L.a1.len_ok(List.length(&2, U32, cs))), None{}), Nil{}} == want : PcPk3}
      %Equal.sym(Bool, L.a1.len_ok(List.length(&2, U32, cs)), True{}, hl) : {PcPk3{En.a1.tlv(c, False{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(False{}, True{}, _), None{}), Nil{}} == want : PcPk3}
      %Equal.sym(List<&2, U32>, En.a1.tlv(c, False{}, n, cs, rest1), xs, hx) : {PcPk3{_, None{}, Nil{}} == want : PcPk3}
      {==}

def pc.oneO_prim(ok: Bool, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest1: List<&2, U32>, +xs: List<&2, U32>, +hx: {En.a1.tlv(c, False{}, n, cs, rest1) == xs : List<&2, U32>}, +hb: {Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)))) == True{} : Bool}, +hmc: {B.mask(cs) == cs : List<&2, U32>}) -> pc.goodO(A.a1.one(A.a1.mk_prim.pick(ok, T.Asn1Tag{c, n}, B.Octets.of_list(cs)), rest1), xs):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      +o = B.Octets.of_list(cs)
      +want : PcPk = PcPk{xs, None{}}
  +hu = AN.an.not_t(En.a1.is_univ0(c, n), AN.an.and_l(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), hb))
  +hb2 = AN.an.and_r(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), hb)
  +hid = AN.an.and_l(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)), hb2)
  +hl = AN.an.and_r(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)), hb2)
      +eto = Equal.trans(List<&2, U32>, cs, B.mask(cs), B.Octets.to_list(o), Equal.sym(List<&2, U32>, B.mask(cs), cs, hmc), Equal.sym(List<&2, U32>, B.Octets.to_list(o), B.mask(cs), AL.al.to_of(cs)))
      %eto : {PcPk{En.a1.tlv(c, False{}, n, _, rest1), En.a1.first(En.a1.node_err.pick(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(B.Octets.len(o))), None{})} == want : PcPk}
      %Equal.sym(Nat, B.Octets.len(o), List.length(&2, U32, cs), PW.pw.olen_of(cs)) : {PcPk{En.a1.tlv(c, False{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(_)), None{})} == want : PcPk}
      %Equal.sym(Bool, En.a1.is_univ0(c, n), False{}, hu) : {PcPk{En.a1.tlv(c, False{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(_, T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), None{})} == want : PcPk}
      %Equal.sym(Bool, T.a1.id_ok(n), True{}, hid) : {PcPk{En.a1.tlv(c, False{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(False{}, _, L.a1.len_ok(List.length(&2, U32, cs))), None{})} == want : PcPk}
      %Equal.sym(Bool, L.a1.len_ok(List.length(&2, U32, cs)), True{}, hl) : {PcPk{En.a1.tlv(c, False{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(False{}, True{}, _), None{})} == want : PcPk}
      %Equal.sym(List<&2, U32>, En.a1.tlv(c, False{}, n, cs, rest1), xs, hx) : {PcPk{_, None{}} == want : PcPk}
      {==}


# One constructed element, then the elements after it

def pc.moreA_set(f2: Bool, +c: T.Asn1Class, +n: Nat, +items: List<&2, N.Asn1Node>, +cs: List<&2, U32>, +rest1: List<&2, U32>, +xs: List<&2, U32>, b: Result<&2, &2, E.Asn1Error, A.A1Out>, +hx: {En.a1.tlv(c, True{}, n, cs, rest1) == xs : List<&2, U32>}, +hb: {Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)))) == True{} : Bool}, +hencs: {En.a1.enc_list(items, Nil{}) == cs : List<&2, U32>}, +herr: {En.a1.enc_err(items) == None{} : Maybe<&2, E.Asn1Error>}, hg: pc.goodA(b, rest1)) -> pc.goodA(A.a1.more(A.a1.mk_cons.set(f2, T.Asn1Tag{c, n}, items), b), xs):
  match f2 b:
    case False{} _:
      Unit{}
    case True{} Fail{e}:
      Unit{}
    case True{} Done{A.A1Out{+ns, +r3}}:
      +ei = En.a1.enc_list(items, Nil{})
      +er = En.a1.enc_list(ns, Nil{})
      +ee = En.a1.enc_err(ns)
      +pk : PcPk3 = PcPk3{er, ee, r3}
      +hg2 : {pk == PcPk3{rest1, None{}, Nil{}} : PcPk3} = hg
      +want : PcPk3 = PcPk3{xs, None{}, Nil{}}
  +hu = AN.an.not_t(En.a1.is_univ0(c, n), AN.an.and_l(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), hb))
  +hb2 = AN.an.and_r(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), hb)
  +hid = AN.an.and_l(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)), hb2)
  +hl = AN.an.and_r(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)), hb2)
      +gb = Equal.cong(PcPk3, List<&2, U32>, z => pc.p3b(z), pk, PcPk3{rest1, None{}, Nil{}}, hg2)
      +ge = Equal.cong(PcPk3, Maybe<&2, E.Asn1Error>, z => pc.p3e(z), pk, PcPk3{rest1, None{}, Nil{}}, hg2)
      +gr = Equal.cong(PcPk3, List<&2, U32>, z => pc.p3r(z), pk, PcPk3{rest1, None{}, Nil{}}, hg2)
      %Equal.sym(List<&2, U32>, ei, cs, hencs) : {PcPk3{En.a1.tlv(c, True{}, n, _, er), En.a1.first(En.a1.node_err.pick(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, _))), En.a1.first(En.a1.enc_err(items), ee)), r3} == want : PcPk3}
      %Equal.sym(List<&2, U32>, er, rest1, gb) : {PcPk3{En.a1.tlv(c, True{}, n, cs, _), En.a1.first(En.a1.node_err.pick(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), En.a1.first(En.a1.enc_err(items), ee)), r3} == want : PcPk3}
      %Equal.sym(Maybe<&2, E.Asn1Error>, En.a1.enc_err(items), None{}, herr) : {PcPk3{En.a1.tlv(c, True{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), En.a1.first(_, ee)), r3} == want : PcPk3}
      %Equal.sym(Maybe<&2, E.Asn1Error>, ee, None{}, ge) : {PcPk3{En.a1.tlv(c, True{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), En.a1.first(None{}, _)), r3} == want : PcPk3}
      %Equal.sym(List<&2, U32>, r3, Nil{}, gr) : {PcPk3{En.a1.tlv(c, True{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), None{}), _} == want : PcPk3}
      %Equal.sym(Bool, En.a1.is_univ0(c, n), False{}, hu) : {PcPk3{En.a1.tlv(c, True{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(_, T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), None{}), Nil{}} == want : PcPk3}
      %Equal.sym(Bool, T.a1.id_ok(n), True{}, hid) : {PcPk3{En.a1.tlv(c, True{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(False{}, _, L.a1.len_ok(List.length(&2, U32, cs))), None{}), Nil{}} == want : PcPk3}
      %Equal.sym(Bool, L.a1.len_ok(List.length(&2, U32, cs)), True{}, hl) : {PcPk3{En.a1.tlv(c, True{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(False{}, True{}, _), None{}), Nil{}} == want : PcPk3}
      %Equal.sym(List<&2, U32>, En.a1.tlv(c, True{}, n, cs, rest1), xs, hx) : {PcPk3{_, None{}, Nil{}} == want : PcPk3}
      {==}

def pc.moreA_form(f1: Bool, +r: R.Asn1Rules, +c: T.Asn1Class, +n: Nat, +items: List<&2, N.Asn1Node>, +cs: List<&2, U32>, +rest1: List<&2, U32>, +xs: List<&2, U32>, b: Result<&2, &2, E.Asn1Error, A.A1Out>, +hx: {En.a1.tlv(c, True{}, n, cs, rest1) == xs : List<&2, U32>}, +hb: {Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)))) == True{} : Bool}, +hencs: {En.a1.enc_list(items, Nil{}) == cs : List<&2, U32>}, +herr: {En.a1.enc_err(items) == None{} : Maybe<&2, E.Asn1Error>}, hg: pc.goodA(b, rest1)) -> pc.goodA(A.a1.more(A.a1.mk_cons.form(f1, r, T.Asn1Tag{c, n}, items), b), xs):
  match f1:
    case False{}:
      Unit{}
    case True{}:
      pc.moreA_set(C.a1.set_ok(r, T.Asn1Tag{c, n}, items), c, n, items, cs, rest1, xs, b, hx, hb, hencs, herr, hg)

def pc.moreA_cons(+r: R.Asn1Rules, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest1: List<&2, U32>, +xs: List<&2, U32>, inner: Result<&2, &2, E.Asn1Error, A.A1Out>, b: Result<&2, &2, E.Asn1Error, A.A1Out>, +hx: {En.a1.tlv(c, True{}, n, cs, rest1) == xs : List<&2, U32>}, +hb: {Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)))) == True{} : Bool}, hin: pc.goodA(inner, cs), hg: pc.goodA(b, rest1)) -> pc.goodA(A.a1.more(A.a1.mk_cons(r, T.Asn1Tag{c, n}, inner), b), xs):
  match inner:
    case Fail{e}:
      Unit{}
    case Done{A.A1Out{+items, +r2}}:
      +pk : PcPk3 = PcPk3{En.a1.enc_list(items, Nil{}), En.a1.enc_err(items), r2}
      +hin2 : {pk == PcPk3{cs, None{}, Nil{}} : PcPk3} = hin
      +hencs = Equal.cong(PcPk3, List<&2, U32>, z => pc.p3b(z), pk, PcPk3{cs, None{}, Nil{}}, hin2)
      +herr = Equal.cong(PcPk3, Maybe<&2, E.Asn1Error>, z => pc.p3e(z), pk, PcPk3{cs, None{}, Nil{}}, hin2)
      pc.moreA_form(R.a1.form_ok(r, T.Asn1Tag{c, n}, True{}), r, c, n, items, cs, rest1, xs, b, hx, hb, hencs, herr, hg)

def pc.oneO_set(f2: Bool, +c: T.Asn1Class, +n: Nat, +items: List<&2, N.Asn1Node>, +cs: List<&2, U32>, +rest1: List<&2, U32>, +xs: List<&2, U32>, +hx: {En.a1.tlv(c, True{}, n, cs, rest1) == xs : List<&2, U32>}, +hb: {Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)))) == True{} : Bool}, +hencs: {En.a1.enc_list(items, Nil{}) == cs : List<&2, U32>}, +herr: {En.a1.enc_err(items) == None{} : Maybe<&2, E.Asn1Error>}) -> pc.goodO(A.a1.one(A.a1.mk_cons.set(f2, T.Asn1Tag{c, n}, items), rest1), xs):
  match f2:
    case False{}:
      Unit{}
    case True{}:
      +ei = En.a1.enc_list(items, Nil{})
      +want : PcPk = PcPk{xs, None{}}
  +hu = AN.an.not_t(En.a1.is_univ0(c, n), AN.an.and_l(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), hb))
  +hb2 = AN.an.and_r(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), hb)
  +hid = AN.an.and_l(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)), hb2)
  +hl = AN.an.and_r(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)), hb2)
      %Equal.sym(List<&2, U32>, ei, cs, hencs) : {PcPk{En.a1.tlv(c, True{}, n, _, rest1), En.a1.first(En.a1.node_err.pick(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, _))), En.a1.first(En.a1.enc_err(items), None{}))} == want : PcPk}
      %Equal.sym(Maybe<&2, E.Asn1Error>, En.a1.enc_err(items), None{}, herr) : {PcPk{En.a1.tlv(c, True{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(En.a1.is_univ0(c, n), T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), En.a1.first(_, None{}))} == want : PcPk}
      %Equal.sym(Bool, En.a1.is_univ0(c, n), False{}, hu) : {PcPk{En.a1.tlv(c, True{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(_, T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))), None{})} == want : PcPk}
      %Equal.sym(Bool, T.a1.id_ok(n), True{}, hid) : {PcPk{En.a1.tlv(c, True{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(False{}, _, L.a1.len_ok(List.length(&2, U32, cs))), None{})} == want : PcPk}
      %Equal.sym(Bool, L.a1.len_ok(List.length(&2, U32, cs)), True{}, hl) : {PcPk{En.a1.tlv(c, True{}, n, cs, rest1), En.a1.first(En.a1.node_err.pick(False{}, True{}, _), None{})} == want : PcPk}
      %Equal.sym(List<&2, U32>, En.a1.tlv(c, True{}, n, cs, rest1), xs, hx) : {PcPk{_, None{}} == want : PcPk}
      {==}

def pc.oneO_form(f1: Bool, +r: R.Asn1Rules, +c: T.Asn1Class, +n: Nat, +items: List<&2, N.Asn1Node>, +cs: List<&2, U32>, +rest1: List<&2, U32>, +xs: List<&2, U32>, +hx: {En.a1.tlv(c, True{}, n, cs, rest1) == xs : List<&2, U32>}, +hb: {Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)))) == True{} : Bool}, +hencs: {En.a1.enc_list(items, Nil{}) == cs : List<&2, U32>}, +herr: {En.a1.enc_err(items) == None{} : Maybe<&2, E.Asn1Error>}) -> pc.goodO(A.a1.one(A.a1.mk_cons.form(f1, r, T.Asn1Tag{c, n}, items), rest1), xs):
  match f1:
    case False{}:
      Unit{}
    case True{}:
      pc.oneO_set(C.a1.set_ok(r, T.Asn1Tag{c, n}, items), c, n, items, cs, rest1, xs, hx, hb, hencs, herr)

def pc.oneO_cons(+r: R.Asn1Rules, +c: T.Asn1Class, +n: Nat, +cs: List<&2, U32>, +rest1: List<&2, U32>, +xs: List<&2, U32>, inner: Result<&2, &2, E.Asn1Error, A.A1Out>, +hx: {En.a1.tlv(c, True{}, n, cs, rest1) == xs : List<&2, U32>}, +hb: {Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs)))) == True{} : Bool}, hin: pc.goodA(inner, cs)) -> pc.goodO(A.a1.one(A.a1.mk_cons(r, T.Asn1Tag{c, n}, inner), rest1), xs):
  match inner:
    case Fail{e}:
      Unit{}
    case Done{A.A1Out{+items, +r2}}:
      +pk : PcPk3 = PcPk3{En.a1.enc_list(items, Nil{}), En.a1.enc_err(items), r2}
      +hin2 : {pk == PcPk3{cs, None{}, Nil{}} : PcPk3} = hin
      +hencs = Equal.cong(PcPk3, List<&2, U32>, z => pc.p3b(z), pk, PcPk3{cs, None{}, Nil{}}, hin2)
      +herr = Equal.cong(PcPk3, Maybe<&2, E.Asn1Error>, z => pc.p3e(z), pk, PcPk3{cs, None{}, Nil{}}, hin2)
      pc.oneO_form(R.a1.form_ok(r, T.Asn1Tag{c, n}, True{}), r, c, n, items, cs, rest1, xs, hx, hb, hencs, herr)


# Decoding octets to their end: the elements encode back to the octets
def pc.dec_all(f: Nat, +r: R.Asn1Rules, h: A.A1Head, +xs: List<&2, U32>, +eh: {A.a1.head(r, xs) == h : A.A1Head}, +hmask: {B.mask(xs) == xs : List<&2, U32>}, +hm: {R.Asn1Rules.min_length(r) == True{} : Bool}, +hi: {R.Asn1Rules.indefinite(r) == False{} : Bool}) -> pc.goodA(A.a1.dec(f, r, A.A1All{}, h), xs):
  match f:
    case 0n:
      Unit{}
    case 1n+ +g:
      match h:
        case A.A1HEnd{}:
          %pc.end_inv(r, xs, eh) : {PcPk3{Nil{}, None{}, Nil{}} == PcPk3{_, None{}, Nil{}} : PcPk3}
          {==}
        case A.A1HEoc{rest}:
          Unit{}
        case A.A1HErr{e}:
          Unit{}
        case A.A1HIndef{t, rest}:
          Empty.absurd(pc.goodA(A.a1.dec(1n+g, r, A.A1All{}, A.A1HIndef{t, rest}), xs), pc.head_indef(r, xs, hi, t, rest, eh))
        case A.A1HPrim{T.Asn1Tag{+c, +n}, +cs, +rest1}:
              +hd = pc.head_prim(r, xs, hm, c, n, cs, rest1, eh)
              +x0 = En.a1.tlv(c, False{}, n, cs, rest1)
              +hx = Equal.cong(PcHd, List<&2, U32>, z => pc.hdb(z), PcHd{x0, Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))}, PcHd{xs, True{}}, hd)
              +hb = Equal.cong(PcHd, Bool, z => pc.hdo(z), PcHd{x0, Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))}, PcHd{xs, True{}}, hd)
              +hmc = pc.fix_cs(c, False{}, n, cs, rest1, xs, hx, hmask)
              +hmr = pc.fix_rest(c, False{}, n, cs, rest1, xs, hx, hmask)
              +b = A.a1.dec(g, r, A.A1All{}, A.a1.head(r, rest1))
              pc.moreA_prim(R.a1.form_ok(r, T.Asn1Tag{c, n}, False{}), c, n, cs, rest1, xs, b, hx, hb, hmc, pc.dec_all(g, r, A.a1.head(r, rest1), rest1, {==}, hmr, hm, hi))
        case A.A1HDef{T.Asn1Tag{+c, +n}, +cs, +rest1}:
              +hd = pc.head_def(r, xs, hm, c, n, cs, rest1, eh)
              +x0 = En.a1.tlv(c, True{}, n, cs, rest1)
              +hx = Equal.cong(PcHd, List<&2, U32>, z => pc.hdb(z), PcHd{x0, Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))}, PcHd{xs, True{}}, hd)
              +hb = Equal.cong(PcHd, Bool, z => pc.hdo(z), PcHd{x0, Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))}, PcHd{xs, True{}}, hd)
              +hmc = pc.fix_cs(c, True{}, n, cs, rest1, xs, hx, hmask)
              +hmr = pc.fix_rest(c, True{}, n, cs, rest1, xs, hx, hmask)
              +inner = A.a1.dec(g, r, A.A1All{}, A.a1.head(r, cs))
              +b = A.a1.dec(g, r, A.A1All{}, A.a1.head(r, rest1))
              pc.moreA_cons(r, c, n, cs, rest1, xs, inner, b, hx, hb, pc.dec_all(g, r, A.a1.head(r, cs), cs, {==}, hmc, hm, hi), pc.dec_all(g, r, A.a1.head(r, rest1), rest1, {==}, hmr, hm, hi))

# Decoding one element: it, and the octets after it, encode back to the
# octets
def pc.dec_one(f: Nat, +r: R.Asn1Rules, h: A.A1Head, +xs: List<&2, U32>, +eh: {A.a1.head(r, xs) == h : A.A1Head}, +hmask: {B.mask(xs) == xs : List<&2, U32>}, +hm: {R.Asn1Rules.min_length(r) == True{} : Bool}, +hi: {R.Asn1Rules.indefinite(r) == False{} : Bool}) -> pc.goodO(A.a1.dec(f, r, A.A1One{}, h), xs):
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
        case A.A1HIndef{t, rest}:
          Empty.absurd(pc.goodO(A.a1.dec(1n+g, r, A.A1One{}, A.A1HIndef{t, rest}), xs), pc.head_indef(r, xs, hi, t, rest, eh))
        case A.A1HPrim{T.Asn1Tag{+c, +n}, +cs, +rest1}:
              +hd = pc.head_prim(r, xs, hm, c, n, cs, rest1, eh)
              +x0 = En.a1.tlv(c, False{}, n, cs, rest1)
              +hx = Equal.cong(PcHd, List<&2, U32>, z => pc.hdb(z), PcHd{x0, Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))}, PcHd{xs, True{}}, hd)
              +hb = Equal.cong(PcHd, Bool, z => pc.hdo(z), PcHd{x0, Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))}, PcHd{xs, True{}}, hd)
              +hmc = pc.fix_cs(c, False{}, n, cs, rest1, xs, hx, hmask)
              +hmr = pc.fix_rest(c, False{}, n, cs, rest1, xs, hx, hmask)
              pc.oneO_prim(R.a1.form_ok(r, T.Asn1Tag{c, n}, False{}), c, n, cs, rest1, xs, hx, hb, hmc)
        case A.A1HDef{T.Asn1Tag{+c, +n}, +cs, +rest1}:
              +hd = pc.head_def(r, xs, hm, c, n, cs, rest1, eh)
              +x0 = En.a1.tlv(c, True{}, n, cs, rest1)
              +hx = Equal.cong(PcHd, List<&2, U32>, z => pc.hdb(z), PcHd{x0, Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))}, PcHd{xs, True{}}, hd)
              +hb = Equal.cong(PcHd, Bool, z => pc.hdo(z), PcHd{x0, Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), L.a1.len_ok(List.length(&2, U32, cs))))}, PcHd{xs, True{}}, hd)
              +hmc = pc.fix_cs(c, True{}, n, cs, rest1, xs, hx, hmask)
              +hmr = pc.fix_rest(c, True{}, n, cs, rest1, xs, hx, hmask)
              +inner = A.a1.dec(g, r, A.A1All{}, A.a1.head(r, cs))
              pc.oneO_cons(r, c, n, cs, rest1, xs, inner, hx, hb, pc.dec_all(g, r, A.a1.head(r, cs), cs, {==}, hmc, hm, hi))


# Decoding octets to one element with nothing after it

def pc.ndisc(r: Result<&2, &2, E.Asn1Error, N.Asn1Node>) -> Type:
  match r:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def pc.fd(-x: E.Asn1Error, -y: N.Asn1Node, e: {Fail{x} == Done{y} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}) -> Empty:
  %e : pc.ndisc(_)
  Unit{}

def pc.dval(z: Result<&2, &2, E.Asn1Error, N.Asn1Node>, d: N.Asn1Node) -> N.Asn1Node:
  match z:
    case Fail{x}:
      d
    case Done{v}:
      v

def pc.top_good(+r: R.Asn1Rules, res: Result<&2, &2, E.Asn1Error, A.A1Out>, -n: N.Asn1Node, +xs: List<&2, U32>, +ht: {R.Asn1Rules.trailing(r) == False{} : Bool}, hg: pc.goodO(res, xs), +e: {A.a1.top(r, res) == Done{n} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}) -> {PcPk{En.a1.enc_list([n], Nil{}), En.a1.enc_err([n])} == PcPk{xs, None{}} : PcPk}:
  match res:
    case Fail{x}:
      Empty.absurd({PcPk{En.a1.enc_list([n], Nil{}), En.a1.enc_err([n])} == PcPk{xs, None{}} : PcPk}, pc.fd(x, n, e))
    case Done{A.A1Out{Nil{}, rest}}:
      Empty.absurd({PcPk{En.a1.enc_list([n], Nil{}), En.a1.enc_err([n])} == PcPk{xs, None{}} : PcPk}, pc.fd(E.Asn1Truncated{}, n, e))
    case Done{A.A1Out{Con{m, Con{m2, ms}}, rest}}:
      Empty.absurd({PcPk{En.a1.enc_list([n], Nil{}), En.a1.enc_err([n])} == PcPk{xs, None{}} : PcPk}, pc.fd(E.Asn1Truncated{}, n, e))
    case Done{A.A1Out{Con{+m, Nil{}}, Nil{}}}:
      %Equal.cong(Result<&2, &2, E.Asn1Error, N.Asn1Node>, N.Asn1Node, z => pc.dval(z, m), Done{m}, Done{n}, e) : {PcPk{En.a1.enc_list([_], Nil{}), En.a1.enc_err([_])} == PcPk{xs, None{}} : PcPk}
      hg
    case Done{A.A1Out{Con{+m, Nil{}}, Con{y, t}}}:
      +e2 = Equal.trans(Result<&2, &2, E.Asn1Error, N.Asn1Node>, A.a1.top.end(False{}, m), A.a1.top.end(R.Asn1Rules.trailing(r), m), Done{n}, Equal.cong(Bool, Result<&2, &2, E.Asn1Error, N.Asn1Node>, z => A.a1.top.end(z, m), False{}, R.Asn1Rules.trailing(r), Equal.sym(Bool, R.Asn1Rules.trailing(r), False{}, ht)), e)
      Empty.absurd({PcPk{En.a1.enc_list([n], Nil{}), En.a1.enc_err([n])} == PcPk{xs, None{}} : PcPk}, pc.fd(E.Asn1Trailing{}, n, e2))

# encode after decode
def pc.ed(+r: R.Asn1Rules, +hm: {R.Asn1Rules.min_length(r) == True{} : Bool}, +hi: {R.Asn1Rules.indefinite(r) == False{} : Bool}, +ht: {R.Asn1Rules.trailing(r) == False{} : Bool}, +b: B.Octets, +n: N.Asn1Node, +e: {A.Asn1.decode(r, b) == Done{n} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}) -> {En.Asn1.encode(n) == Done{b} : Result<&2, &2, E.Asn1Error, B.Octets>}:
  +xs = B.Octets.to_list(b)
  +res = A.a1.run(r, A.A1One{}, xs)
  +pk = pc.top_good(r, res, n, xs, ht, pc.dec_one(Nat.add(1n, List.length(&2, U32, xs)), r, A.a1.head(r, xs), xs, {==}, AL.al.mask_to(b), hm, hi), e)
  +ee = En.a1.enc_list([n], Nil{})
  +henc = Equal.cong(PcPk, List<&2, U32>, z => pc.pb(z), PcPk{ee, En.a1.enc_err([n])}, PcPk{xs, None{}}, pk)
  +herr = Equal.cong(PcPk, Maybe<&2, E.Asn1Error>, z => pc.pe(z), PcPk{ee, En.a1.enc_err([n])}, PcPk{xs, None{}}, pk)
  %Equal.sym(Maybe<&2, E.Asn1Error>, En.a1.enc_err([n]), None{}, herr) : {En.a1.encode.go(_, [n]) == Done{b} : Result<&2, &2, E.Asn1Error, B.Octets>}
  %Equal.sym(List<&2, U32>, ee, xs, henc) : {Done{B.Octets.of_list(_)} == Done{b} : Result<&2, &2, E.Asn1Error, B.Octets>}
  %AL.al.of_to(b) : {Done{B.Octets.of_list(xs)} == Done{_} : Result<&2, &2, E.Asn1Error, B.Octets>}
  {==}
