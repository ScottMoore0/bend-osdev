# Proofs of bend-osdev-pkcs's laws. The lemmas are in proof_pkcs.bend and
# proof_octets.bend (the octets kept, through asn1's match laws); the
# signature law rests on crypto's sign_verify_bytes_if.
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ../crypto/sign.bend as Sg
import ../crypto/LAWS.bend as CL
import ../crypto/PROOF.bend as CP
import ./signer.bend as PG
import ./pkcs.bend as P
import ./signed.bend as PS
import ./p8.bend as P8
import ./proof_pkcs.bend as PP
import ./proof_octets.bend as PQ
import ./LAWS.bend as Laws

def Laws.cms_parsed_conforms(r, b, s, e):
  PP.pp.finish(P.pk.parse0(r, b), r, s, e)

def Laws.p8_parsed_conforms(r, b, k, e):
  PP.pp.kfinish(P8.pk.p8.parse0(r, b), r, k, e)

def Laws.signed_without_attrs(g, c, h):
  %Equal.sym(Maybe<&2, PG.CmsAttrs>, PG.CmsSigner.signed_attrs(g), None{}, h) : {PS.pk.signed.msg(_, c) == c : B.Octets}
  {==}

def Laws.verify_signed_if(SK, PK, public, pk_of, pk_to, sign, verify, sk, g, c, hf, ha, hs):
  %Equal.sym(B.Octets, PG.CmsSigner.signature(g), sign(sk, PS.Cms.signed_message(g, c)), hs) : {Sg.CrSign.verify_bytes(~PK, ~pk_of, ~verify, pk_to(public(sk)), PS.Cms.signed_message(g, c), _) == True{} : Bool}
  CL.sign_verify_bytes_if(SK, PK, public, pk_of, pk_to, sign, verify, sk, PS.Cms.signed_message(g, c), hf, ha)

def Laws.find_attr_type(xs, id, a, e):
  PP.pp.find(xs, id, a, e)

def Laws.vec_set_tagged():
  {==}

def Laws.signed_data_slice(r, b, s, e):
  PQ.pq.sd_slice(r, b, s, PQ.pq.parsed(r, b, s, e))

def Laws.signed_attrs_slice(r, b, s, pre, g, post, a, e, hg, ha):
  PQ.pq.sa_slice(r, b, s, pre, g, post, a, hg, ha, PQ.pq.parsed(r, b, s, e))

def Laws.certificate_slice(r, b, s, pre, o, post, e, hc):
  PQ.pq.cert_slice(r, b, s, pre, o, post, hc, PQ.pq.parsed(r, b, s, e))

def Laws.signed_attrs_der(r, b, s, pre, g, post, a, c, e, hg, ha, hd):
  PQ.pq.der1(g, c, a, ha, PQ.pq.der_match(r, b, s, pre, g, post, a, e, hg, ha, hd))
