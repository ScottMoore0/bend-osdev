# The proof of LAWS_rsa.bend: rsa's pkcs1_sign_verify says verifying the
# signature RsaPkcs1.sign makes is true wherever it makes one, so, where it
# does (hs), the instance's signature (the made one) verifies: that is
# LAWS.bend's hypothesis ha, and its rsa_pkcs1_verify_bytes_if (crypto's
# sign_verify_bytes_if) does the rest.
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../bignum/LAWS_limbs.bend as LL
import ../bignum/LAWS_fermat.bend as LF
import ../rsa/rsa.bend as RR
import ../rsa/keys.bend as RK
import ../rsa/pkcs1.bend as RP
import ../rsa/LAWS_sign.bend as RS
import ../rsa/PROOF_sign.bend as RSP
import ../crypto/crypto.bend as Cr
import ../crypto/sign.bend as Sg
import ../crypto/LAWS_pk.bend as CK
import ../crypto/PROOF_pk.bend as CKP
import ./rsa.bend as PR
import ./LAWS_rsa.bend as Laws

def pkr.bool(+b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def pkr.ft(+e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : pkr.bool(_)
  Unit{}

# where r is a made signature, the instance's signature (r, or empty bytes)
# verifies, given that verifying r's signature is true wherever r makes one
def pkr.made(~digest: B.Octets -> B.Octets, ~prefix: B.Octets, +sk: RR.RsaPrivate, +m: B.Octets, +r: Result<&2, &2, RR.RsaError, B.Octets>, +h1: {Result.map(&2, &2, RR.RsaError, B.Octets, Bool, x => RP.RsaPkcs1.verify(~digest, prefix, RR.Rsa.public(sk), m, x), r) == Result.map(&2, &2, RR.RsaError, B.Octets, Bool, x => True{}, r) : Result<&2, &2, RR.RsaError, Bool>}, +hs: {Result.is_done(&2, &2, RR.RsaError, B.Octets, r) == True{} : Bool}) -> {RP.RsaPkcs1.verify(~digest, prefix, RR.Rsa.public(sk), m, Result.default(&2, &2, RR.RsaError, B.Octets, r, B.Octets.empty())) == True{} : Bool}:
  match r:
    case Fail{+x}:
      Empty.absurd({RP.RsaPkcs1.verify(~digest, prefix, RR.Rsa.public(sk), m, Result.default(&2, &2, RR.RsaError, B.Octets, Fail{x}, B.Octets.empty())) == True{} : Bool}, pkr.ft(hs))
    case Done{+s}:
      Equal.cong(Result<&2, &2, RR.RsaError, Bool>, Bool, z => Result.default(&2, &2, RR.RsaError, Bool, z, False{}), Done{RP.RsaPkcs1.verify(~digest, prefix, RR.Rsa.public(sk), m, s)}, Done{True{}}, h1)

def Laws.rsa_pkcs1_verify_bytes(digest, prefix, n, e, d, p, q, sk, m, hk, hn, he, hd, hp, hq, pp, pq, hs, hf):
  CK.sign_verify_bytes_if(~RR.RsaPrivate, ~RR.RsaPublic, ~RR.Rsa.public, ~PR.PkRsa.pk_of, ~RK.RsaKeys.public_to, ~PR.PkRsa.pkcs1_sign(~digest, ~prefix), ~PR.PkRsa.pkcs1_verify(~digest, ~prefix), sk, m, hf, pkr.made(~digest, ~prefix, sk, m, RP.RsaPkcs1.sign(~digest, prefix, sk, m), RS.pkcs1_sign_verify(~digest, prefix, n, e, d, p, q, sk, m, hk, hn, he, hd, hp, hq, pp, pq), hs))
