# Proofs of bend-osdev-x509's extension laws (LAWS_ext.bend): an extension's
# value octets decode back to the element written (asn1's decode_encode:
# a primitive BIT STRING or OCTET STRING conforms to every rules), and the
# typed reader reads that element back as the value (asn1's
# bits_round_trip, octets_round_trip).
import Base
import ../bytes/bytes.bend as B
import ../asn1/error.bend as AE
import ../asn1/tag.bend as AT
import ../asn1/node.bend as AN
import ../asn1/rules.bend as AR
import ../asn1/conform.bend as AC
import ../asn1/asn1.bend as A
import ../asn1/prim.bend as AP
import ../asn1/bits.bend as ABi
import ../asn1/LAWS.bend as AL1
import ../asn1/PROOF.bend as AP1
import ../asn1/LAWS_typed.bend as ALT
import ../asn1/PROOF_typed.bend as APT
import ./error.bend as XE
import ./rules.bend as XR
import ./ext.bend as XX
import ./extval.bend as XV
import ./LAWS_ext.bend as Laws

def px.when_true(on: Bool) -> {AR.a1.when(on, True{}) == True{} : Bool}:
  match on:
    case True{}:
      {==}
    case False{}:
      {==}

# a primitive element of a universal type that may be primitive conforms to
# every rules (BIT STRING 3, OCTET STRING 4)
def px.conf3(+rr: AR.Asn1Rules, +c: B.Octets) -> {AC.Asn1.conforms(rr, AN.Asn1Prim{AT.Asn1Tag.bit_string(), c}) == True{} : Bool}:
  %Equal.sym(Bool, AR.a1.when(AR.Asn1Rules.forms(rr), True{}), True{}, px.when_true(AR.Asn1Rules.forms(rr))) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def px.conf4(+rr: AR.Asn1Rules, +c: B.Octets) -> {AC.Asn1.conforms(rr, AN.Asn1Prim{AT.Asn1Tag.octet_string(), c}) == True{} : Bool}:
  %Equal.sym(Bool, AR.a1.when(AR.Asn1Rules.forms(rr), True{}), True{}, px.when_true(AR.Asn1Rules.forms(rr))) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

# an extension's value that decodes to n
def px.node(+r: XR.X509Rules, +e: XX.X509Ext, +n: AN.Asn1Node, +hd: {A.Asn1.decode(XR.X509Rules.asn1(r), XX.X509Ext.value(e)) == Done{n} : Result<&2, &2, AE.Asn1Error, AN.Asn1Node>}) -> {XV.x5.v.node(r, e) == Done{n} : Result<&2, &2, XE.X509Error, AN.Asn1Node>}:
  %Equal.sym(Result<&2, &2, AE.Asn1Error, AN.Asn1Node>, A.Asn1.decode(XR.X509Rules.asn1(r), XX.X509Ext.value(e)), Done{n}, hd) : {XE.x5.or(AN.Asn1Node, _, XV.x5.v.bad(e)) == Done{n} : Result<&2, &2, XE.X509Error, AN.Asn1Node>}
  {==}

def Laws.key_usage_round_trip(r, id, crit, raw, u, o, hok, hc, v, he):
  +rr = XR.X509Rules.asn1(r)
  +e : XX.X509Ext = XX.X509Ext{id, crit, v, raw}
  +n = ABi.Asn1.bits(ABi.Asn1Bits{u, o})
  +hn = px.node(r, e, n, AL1.decode_encode(rr, n, v, he, px.conf3(rr, B.Octets.cons(U32.from_nat(u), o))))
  +hb = ALT.bits_round_trip(rr, AT.Asn1Tag.bit_string(), u, o, hok, hc)
  %Equal.sym(Result<&2, &2, XE.X509Error, AN.Asn1Node>, XV.x5.v.node(r, e), Done{n}, hn) : {XV.x5.v.then(AN.Asn1Node, ABi.Asn1Bits, _, m => XE.x5.or(ABi.Asn1Bits, ABi.Asn1.get_bits(rr, m), XV.x5.v.bad(e))) == Done{ABi.Asn1Bits{u, o}} : Result<&2, &2, XE.X509Error, ABi.Asn1Bits>}
  %Equal.sym(Result<&2, &2, AE.Asn1Error, ABi.Asn1Bits>, ABi.Asn1.get_bits(rr, n), Done{ABi.Asn1Bits{u, o}}, hb) : {XE.x5.or(ABi.Asn1Bits, _, XV.x5.v.bad(e)) == Done{ABi.Asn1Bits{u, o}} : Result<&2, &2, XE.X509Error, ABi.Asn1Bits>}
  {==}

def Laws.subject_key_id_round_trip(r, id, crit, raw, o, v, he):
  +rr = XR.X509Rules.asn1(r)
  +e : XX.X509Ext = XX.X509Ext{id, crit, v, raw}
  +n = AP.Asn1.octets(o)
  +hn = px.node(r, e, n, AL1.decode_encode(rr, n, v, he, px.conf4(rr, o)))
  +hb = ALT.octets_round_trip(rr, AT.Asn1Tag.octet_string(), o)
  %Equal.sym(Result<&2, &2, XE.X509Error, AN.Asn1Node>, XV.x5.v.node(r, e), Done{n}, hn) : {XV.x5.v.then(AN.Asn1Node, B.Octets, _, m => XE.x5.or(B.Octets, AP.Asn1.get_octets(rr, m), XV.x5.v.bad(e))) == Done{o} : Result<&2, &2, XE.X509Error, B.Octets>}
  %Equal.sym(Result<&2, &2, AE.Asn1Error, B.Octets>, AP.Asn1.get_octets(rr, n), Done{o}, hb) : {XE.x5.or(B.Octets, _, XV.x5.v.bad(e)) == Done{o} : Result<&2, &2, XE.X509Error, B.Octets>}
  {==}
