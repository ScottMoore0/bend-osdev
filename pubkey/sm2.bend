# SM2 signatures (the sm2 package) as an instance of the signature
# interface (crypto's sign.bend), over a curve (~prm, EcCurves.sm2() the usual one),
# a hash (~digest, SM3 the usual one), its HMAC for the deterministic k
# (~mac) and the signer's identity (~id):
#   ~N.BnNat, ~E.EcPoint, ~PkSm2.secret(~prm), ~PkEcdh.public(~prm),
#   ~PkEcdh.pk_of(~prm), ~PkEcdh.pk_to(~prm),
#   ~PkSm2.sign(~prm, ~digest, ~mac, ~id), ~PkSm2.verify(~prm, ~digest, ~id)
# Keys are ECDH's forms (ecc.bend), except that a private key is in
# [1, n - 2]; a signature is r || s, each n's length. The interface's sign
# is deterministic (sm2's Sm2.sign_det, RFC 6979's construction: not part
# of SM2, which asks for a random k; a verifier cannot tell). The named
# instance is SM2 with SM3 on SM2's curve for the identity
# "1234567812345678" (PkSm2.sm3_sign and _verify; any other identity is a
# template argument).
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../ecc/ecc.bend as E
import ../ecc/curves.bend as EC
import ../ecc/ecdsa.bend as S
import ../sm2/sm2.bend as M
import ../crypto/crypto.bend as Cr
import ./pubkey.bend as Pk

def PkSm2.err(e: M.Sm2Error) -> Cr.CrError:
  match e:
    case M.Sm2BadNonce{}:
      Cr.CrBadKey{}
    case M.Sm2BadPrivateKey{}:
      Cr.CrBadKey{}
    case M.Sm2IdTooLong{}:
      Cr.CrTooLong{0n}

def PkSm2.secret(~prm: E.EcParams, o: B.Octets) -> Result<&2, &2, Cr.CrError, N.BnNat>:
  Cr.CrError.lift(~M.Sm2Error, ~N.BnNat, ~PkSm2.err, M.Sm2.private_of(E.EcCurve.of(prm), o))

def PkSm2.sig(+c: E.EcCurve, r: Result<&2, &2, M.Sm2Error, S.EcSig>) -> B.Octets:
  match r:
    case Fail{e}:
      B.Octets.empty()
    case Done{s}:
      S.EcDsa.sig_to(c, s)

def PkSm2.sign(~prm: E.EcParams, ~digest: B.Octets -> B.Octets, ~mac: B.Octets -> B.Octets -> B.Octets, ~id: B.Octets, d: N.BnNat, m: B.Octets) -> B.Octets:
  +c = E.EcCurve.of(prm)
  PkSm2.sig(c, M.Sm2.sign_det(~digest, ~mac, c, d, id, m))

def PkSm2.check(~digest: B.Octets -> B.Octets, ~id: B.Octets, +c: E.EcCurve, q: E.EcPoint, m: B.Octets, s: Maybe<&2, S.EcSig>) -> Bool:
  match s:
    case None{}:
      False{}
    case Some{sig}:
      M.Sm2.verify(~digest, c, q, id, m, sig)

def PkSm2.verify(~prm: E.EcParams, ~digest: B.Octets -> B.Octets, ~id: B.Octets, q: E.EcPoint, m: B.Octets, s: B.Octets) -> Bool:
  +c = E.EcCurve.of(prm)
  PkSm2.check(~digest, ~id, c, q, m, S.EcDsa.sig_of(c, s))

def PkSm2.default_id() -> B.Octets:
  B.Octets.of_string("1234567812345678")

def PkSm2.sm3_sign(d: N.BnNat, m: B.Octets) -> B.Octets:
  PkSm2.sign(~EC.EcCurves.sm2(), ~M.Sm2.sm3, ~Pk.PkHmac.raw(~64n, ~M.Sm2.sm3), ~PkSm2.default_id(), d, m)

def PkSm2.sm3_verify(q: E.EcPoint, m: B.Octets, s: B.Octets) -> Bool:
  PkSm2.verify(~EC.EcCurves.sm2(), ~M.Sm2.sm3, ~PkSm2.default_id(), q, m, s)
