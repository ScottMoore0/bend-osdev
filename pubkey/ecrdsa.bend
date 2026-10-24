# GOST R 34.10-2012 signatures (the ecrdsa package, RFC 7091) as an
# instance of the signature interface (crypto's sign.bend), over a curve (~prm, such
# as EcCurves.gost_cp_a()), a hash (~digest, Streebog-256 for 256-bit
# curves) and its HMAC for the deterministic k (~mac):
#   ~N.BnNat, ~E.EcPoint, ~PkEcrdsa.secret(~prm), ~PkEcdh.public(~prm),
#   ~PkEcrdsa.pk_of(~prm), ~PkEcrdsa.pk_to(~prm),
#   ~PkEcrdsa.sign(~prm, ~digest, ~mac), ~PkEcrdsa.verify(~prm, ~digest)
# A private key's bytes are the big-endian d in [1, q - 1]; public keys and
# signatures travel in RFC 4491's forms (x then y little-endian; s then r
# big-endian). The interface's sign is deterministic (ecrdsa's
# Ecrdsa.sign_det, RFC 6979's construction: not part of GOST R 34.10-2012,
# which asks for a random k; a verifier cannot tell). The named instance is
# CryptoPro-A with Streebog-256 (PkEcrdsa.cp_a_streebog256_sign and
# _verify).
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../ecc/ecc.bend as E
import ../ecc/curves.bend as EC
import ../ecc/ecdsa.bend as S
import ../ecrdsa/ecrdsa.bend as G
import ../crypto/crypto.bend as Cr
import ./pubkey.bend as Pk

def PkEcrdsa.err(e: G.EcrdsaError) -> Cr.CrError:
  match e:
    case G.EcrdsaBadNonce{}:
      Cr.CrBadKey{}
    case G.EcrdsaBadPrivateKey{}:
      Cr.CrBadKey{}
    case G.EcrdsaBadPublicKey{}:
      Cr.CrBadPublicKey{}

def PkEcrdsa.secret(~prm: E.EcParams, o: B.Octets) -> Result<&2, &2, Cr.CrError, N.BnNat>:
  Cr.CrError.lift(~G.EcrdsaError, ~N.BnNat, ~PkEcrdsa.err, G.Ecrdsa.private_of(E.EcCurve.of(prm), o))

# a public key from RFC 4491's form on the curve (ecrdsa's Ecrdsa.public_of)
def PkEcrdsa.public_of(~prm: E.EcParams, o: B.Octets) -> Result<&2, &2, G.EcrdsaError, E.EcPoint>:
  G.Ecrdsa.public_of(E.EcCurve.of(prm), o)

def PkEcrdsa.pk_of(~prm: E.EcParams, o: B.Octets) -> Result<&2, &2, Cr.CrError, E.EcPoint>:
  Cr.CrError.lift(~G.EcrdsaError, ~E.EcPoint, ~PkEcrdsa.err, PkEcrdsa.public_of(~prm, o))

def PkEcrdsa.pk_to(~prm: E.EcParams, p: E.EcPoint) -> B.Octets:
  G.Ecrdsa.public_to(E.EcCurve.of(prm), p)

def PkEcrdsa.sig(+c: E.EcCurve, r: Result<&2, &2, G.EcrdsaError, S.EcSig>) -> B.Octets:
  match r:
    case Fail{e}:
      B.Octets.empty()
    case Done{s}:
      G.Ecrdsa.sig_to(c, s)

def PkEcrdsa.sign(~prm: E.EcParams, ~digest: B.Octets -> B.Octets, ~mac: B.Octets -> B.Octets -> B.Octets, d: N.BnNat, m: B.Octets) -> B.Octets:
  +c = E.EcCurve.of(prm)
  PkEcrdsa.sig(c, G.Ecrdsa.sign_det(~digest, ~mac, c, d, m))

def PkEcrdsa.verify(~prm: E.EcParams, ~digest: B.Octets -> B.Octets, q: E.EcPoint, m: B.Octets, s: B.Octets) -> Bool:
  G.Ecrdsa.verify_bytes(~digest, E.EcCurve.of(prm), q, m, s)

def PkEcrdsa.cp_a_streebog256_sign(d: N.BnNat, m: B.Octets) -> B.Octets:
  PkEcrdsa.sign(~EC.EcCurves.gost_cp_a(), ~G.Ecrdsa.streebog256, ~Pk.PkHmac.raw(~64n, ~G.Ecrdsa.streebog256), d, m)

def PkEcrdsa.cp_a_streebog256_verify(q: E.EcPoint, m: B.Octets, s: B.Octets) -> Bool:
  PkEcrdsa.verify(~EC.EcCurves.gost_cp_a(), ~G.Ecrdsa.streebog256, q, m, s)
