# Proofs of bend-osdev-asn1's laws. The lemmas are in the proof_*.bend
# files: proof_enc.bend (decoding what the encoder wrote), proof_head.bend
# (headers), proof_num.bend (numbers in octets), proof_byte.bend (generated:
# single octets), proof_split.bend (the octets kept per element),
# proof_der.bend (those octets under DER, re-tagging), proof_match.bend
# (schema matches), proof_oct.bend (Octets joined and cut),
# proof_u32.bend, proof_list.bend and proof_nat.bend.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./rules.bend as R
import ./encode.bend as En
import ./conform.bend as C
import ./asn1.bend as A
import ./proof_enc.bend as PE
import ./proof_within.bend as PW
import ./proof_canon.bend as PC
import ./proof_oid.bend as PO
import ./proof_split.bend as PS
import ./proof_der.bend as PD
import ./proof_match.bend as PM
import ./schema.bend as Sc
import ./oidval.bend as O
import ./LAWS.bend as Laws

def Laws.decode_encode(r, n, b, e, hc):
  PE.pe.de(En.a1.enc_err([n]), r, n, b, {==}, e, hc)

# the forms check of a primitive BIT STRING or OCTET STRING passes whether
# or not the rules check forms
def pf.when_true(on: Bool) -> {R.a1.when(on, True{}) == True{} : Bool}:
  match on:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.bit_string_conforms(r, c):
  %Equal.sym(Bool, R.a1.when(R.Asn1Rules.forms(r), True{}), True{}, pf.when_true(R.Asn1Rules.forms(r))) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def Laws.octet_string_conforms(r, c):
  %Equal.sym(Bool, R.a1.when(R.Asn1Rules.forms(r), True{}), True{}, pf.when_true(R.Asn1Rules.forms(r))) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def Laws.encode_decode(r, hm, hi, ht, b, n, e):
  PC.pc.ed(r, hm, hi, ht, b, n, e)

def Laws.der_unique(b, n, e):
  PC.pc.ed(R.Asn1Rules.der(), {==}, {==}, {==}, b, n, e)

def Laws.decode_within(r, b, n, e):
  +xs = B.Octets.to_list(b)
  %PW.pw.blen(b) : {Nat.is_le(N.Asn1.span(n), _) == True{} : Bool}
  PW.pw.top_inv(r, A.a1.run(r, A.A1One{}, xs), n, List.length(&2, U32, xs), PW.pw.run(r, A.A1One{}, xs), e)

def Laws.prefix_within(r, b, n, rest, e):
  +xs = B.Octets.to_list(b)
  %PW.pw.blen(b) : {Nat.is_le(Nat.add(N.Asn1.span(n), B.Octets.len(rest)), _) == True{} : Bool}
  PW.pw.read_inv(A.a1.run(r, A.A1One{}, xs), n, rest, List.length(&2, U32, xs), PW.pw.run(r, A.A1One{}, xs), e)

def Laws.all_within(r, b, ns, e):
  +xs = B.Octets.to_list(b)
  %PW.pw.blen(b) : {Nat.is_le(N.Asn1.spans(ns), _) == True{} : Bool}
  PW.pw.all_inv(A.a1.run(r, A.A1All{}, xs), ns, List.length(&2, U32, xs), PW.pw.run(r, A.A1All{}, xs), e)

def Laws.oid_round_trip(arcs, o, e):
  PO.po.rt(O.Asn1.oid_valid(arcs), arcs, o, {==}, e)

def Laws.oid_canonical(o, arcs, e):
  PO.po.canonical(o, arcs, e)

def Laws.read_split(r, b, x, rest, e):
  PS.ps.read(r, b, x, rest, e)

def Laws.read_all_split(r, b, xs, e):
  PS.ps.read_all(r, b, xs, e)

def Laws.contents_within(r, x):
  PS.ps.contents(r, x)

def Laws.items_split(r, x, xs, e):
  PS.ps.items(r, x, xs, e)

def Laws.read_der(r, hm, hi, b, x, rest, e):
  PD.pd.read_der(r, hm, hi, b, x, rest, e)

def Laws.encode_retag(t, u, ns, o, hu, hr, e):
  match t u:
    case T.Asn1Tag{+c, +n} T.Asn1Tag{+c2, +n2}:
      PD.pd.retag(En.a1.enc_err([N.Asn1Cons{T.Asn1Tag{c, n}, ns}]), c, n, c2, n2, ns, o, {==}, e, hu, PD.pd.u0(c2, n2, hr))

def Laws.match_tlv_tlv(r, s, x, m, e):
  PM.pm.tlvtlv(r, s, x, m, e)

def Laws.match_tlv_within(r, s, x, m, p, q, e):
  PM.pm.tlv_within(r, s, x, m, p, q, e)

def Laws.match_split(r, s, b, m, e):
  PM.pm.msplit(r, s, b, m, PM.pm.mread(r, s, b, m, e))

def Laws.match_whole(r, ht, s, b, m, e):
  PM.pm.mwhole(r, ht, s, b, m, PM.pm.mread(r, s, b, m, e))

def Laws.match_within(r, s, b, m, p, q, e):
  PM.pm.mwithin(r, s, b, m, p, q, PM.pm.mread(r, s, b, m, e))

def Laws.match_input(r, s, b, m, p, e):
  PM.pm.minput(r, s, b, m, p, e)

def Laws.match_der(r, hm, hi, s, b, m, e):
  PM.pm.mder(r, hm, hi, s, b, m, PM.pm.mread(r, s, b, m, e))

def Laws.match_of_node(r, t, item, set, b, m, e):
  PM.pm.mof(r, t, item, set, b, m, PM.pm.mread(r, Sc.Asn1SOf{t, item, set}, b, m, e))

def Laws.follow_nil(m):
  {==}

def Laws.follow_at(m, i, p):
  {==}

def Laws.follow_inner(m, p):
  {==}

def Laws.at_items(m, pre, x, post, h):
  %Equal.sym(List<&2, Sc.Asn1Match>, Sc.Asn1Match.items(m), List.append(&2, Sc.Asn1Match, pre, Con{x, post}), h) : {Sc.a1.s.nth(_, List.length(&2, Sc.Asn1Match, pre)) == x : Sc.Asn1Match}
  PM.pm.nth_app(pre, x, post)

def Laws.vec_sequence():
  {==}

def Laws.vec_tagging():
  {==}

def Laws.vec_oid():
  {==}

def Laws.vec_length():
  {==}

def Laws.vec_indefinite():
  {==}

def Laws.vec_identifier():
  {==}
