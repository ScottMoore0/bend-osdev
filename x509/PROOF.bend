# Proofs of bend-osdev-x509's laws. The lemmas are in proof_x509.bend and
# proof_octets.bend (the octets kept, through asn1's match laws); the
# signature law rests on crypto's sign_verify_bytes_if and the name laws on
# bytes' octets_is_eq_refl.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../crypto/crypto.bend as Cr
import ../crypto/sign.bend as Sg
import ../crypto/LAWS.bend as CL
import ../crypto/PROOF.bend as CP
import ./namecmp.bend as XC
import ./x509.bend as X
import ./verify.bend as XV
import ./proof_x509.bend as XP
import ./proof_octets.bend as XO
import ./LAWS.bend as Laws

def Laws.parsed_conforms(r, b, c, e):
  XP.xp.finish(X.x5.parse0(r, b), r, c, e)

def Laws.verify_signed_if(SK, PK, public, pk_of, pk_to, sign, verify, sk, c, hf, ha, hs):
  %Equal.sym(B.Octets, X.X509Cert.signature_octets(c), sign(sk, X.X509Cert.tbs_raw(c)), hs) : {Sg.CrSign.verify_bytes(~PK, ~pk_of, ~verify, pk_to(public(sk)), X.X509Cert.tbs_raw(c), _) == True{} : Bool}
  CL.sign_verify_bytes_if(SK, PK, public, pk_of, pk_to, sign, verify, sk, X.X509Cert.tbs_raw(c), hf, ha)

def Laws.name_match_refl(r, n):
  BL.octets_is_eq_refl(XC.X509Name.key(r, n))

def Laws.name_match_binary(a, b):
  {==}

def Laws.find_ext_id(es, id, x, e):
  XP.xp.find(es, id, x, e)

def Laws.vec_name_rfc5280():
  {==}

def Laws.cert_split(r, b, c, e):
  XO.xq.split(r, b, c, XO.xq.parsed(r, b, c, e))

def Laws.cert_whole(r, ht, b, c, e):
  XO.xq.whole(r, ht, b, c, XO.xq.parsed(r, b, c, e))

def Laws.tbs_slice(r, b, c, e):
  XO.xq.tbs_slice(r, b, c, XO.xq.parsed(r, b, c, e))

def Laws.tbs_within(r, b, c, e):
  XO.xq.tbs_within(r, b, c, XO.xq.parsed(r, b, c, e))

def Laws.sig_alg_within(r, b, c, e):
  XO.xq.sig_alg_within(r, b, c, XO.xq.parsed(r, b, c, e))

def Laws.issuer_within(r, b, c, e):
  XO.xq.issuer_within(r, b, c, XO.xq.parsed(r, b, c, e))

def Laws.subject_within(r, b, c, e):
  XO.xq.subject_within(r, b, c, XO.xq.parsed(r, b, c, e))

def Laws.spki_within(r, b, c, e):
  XO.xq.spki_within(r, b, c, XO.xq.parsed(r, b, c, e))

def Laws.tbs_alg_within(r, b, c, e):
  XO.xq.tbs_alg_within(r, b, c, XO.xq.parsed(r, b, c, e))

def Laws.ext_within(r, b, c, pre, x, post, h, e):
  XO.xq.ext_within(r, b, c, pre, x, post, h, XO.xq.parsed(r, b, c, e))
