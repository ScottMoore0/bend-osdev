# The ecc package as instances of the interfaces, over any curve (~prm:
# EcParams, such as EcCurves.p256() of ecc/curves.bend):
#
# ECDH (SP 800-56A) as a key agreement (crypto's kex.bend):
#   ~N.BnNat, ~E.EcPoint, ~PkEcdh.secret(~prm), ~PkEcdh.public(~prm),
#   ~PkEcdh.pk_of(~prm), ~PkEcdh.pk_to(~prm), ~PkEcdh.shared(~prm)
# ECDSA (FIPS 186-5) as a signature (crypto's sign.bend), over a hash (~digest) and
# its HMAC for RFC 6979's deterministic k (~mac: raw key, data -> tag;
# PkHmac.raw(~bsize, ~digest) is HMAC over any hash, crypto's hmac.bend):
#   ~N.BnNat, ~E.EcPoint, ~PkEcdh.secret(~prm), ~PkEcdh.public(~prm),
#   ~PkEcdh.pk_of(~prm), ~PkEcdh.pk_to(~prm),
#   ~PkEcdsa.sign(~prm, ~digest, ~mac), ~PkEcdsa.verify(~prm, ~digest)
# A private key's bytes are the big-endian d in [1, n - 1]; a public key's
# are SEC 1's uncompressed form, partially validated by pk_of and in full
# by ECDH's shared; a signature's are r || s, each n's length. The named
# instance is ECDSA over P-256 with SHA-256 (PkEcdsa.p256_sha256_sign and
# _verify).
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../ecc/ecc.bend as E
import ../ecc/curves.bend as EC
import ../ecc/ecdh.bend as D
import ../ecc/ecdsa.bend as S
import ../crypto/crypto.bend as Cr
import ../crypto/inst_sha2.bend as SH
import ./pubkey.bend as Pk

# ecc's errors onto CrError
def PkEcc.err(e: E.EcError) -> Cr.CrError:
  match e:
    case E.EcBadPoint{}:
      Cr.CrBadPublicKey{}
    case E.EcInfinity{}:
      Cr.CrBadPublicKey{}
    case E.EcBadEncoding{}:
      Cr.CrBadPublicKey{}
    case E.EcBadPrivateKey{}:
      Cr.CrBadKey{}
    case E.EcBadNonce{}:
      Cr.CrBadKey{}

def PkEcdh.secret(~prm: E.EcParams, o: B.Octets) -> Result<&2, &2, Cr.CrError, N.BnNat>:
  Cr.CrError.lift(~E.EcError, ~N.BnNat, ~PkEcc.err, D.EcDh.private_of(E.EcCurve.of(prm), o))

def PkEcdh.public(~prm: E.EcParams, d: N.BnNat) -> E.EcPoint:
  D.EcDh.public(E.EcCurve.of(prm), d)

# a point from SEC 1's uncompressed form on the curve (ecc's EcCurve.point_of)
def PkEcdh.point_of(~prm: E.EcParams, o: B.Octets) -> Result<&2, &2, E.EcError, E.EcPoint>:
  E.EcCurve.point_of(E.EcCurve.of(prm), o)

def PkEcdh.pk_of(~prm: E.EcParams, o: B.Octets) -> Result<&2, &2, Cr.CrError, E.EcPoint>:
  Cr.CrError.lift(~E.EcError, ~E.EcPoint, ~PkEcc.err, PkEcdh.point_of(~prm, o))

def PkEcdh.pk_to(~prm: E.EcParams, p: E.EcPoint) -> B.Octets:
  E.EcCurve.point_to(E.EcCurve.of(prm), p)

def PkEcdh.shared(~prm: E.EcParams, d: N.BnNat, q: E.EcPoint) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Cr.CrError.lift(~E.EcError, ~B.Octets, ~PkEcc.err, D.EcDh.agree(E.EcCurve.of(prm), d, q))

def PkEcdsa.sig(+c: E.EcCurve, r: Result<&2, &2, E.EcError, S.EcSig>) -> B.Octets:
  match r:
    case Fail{e}:
      B.Octets.empty()
    case Done{s}:
      S.EcDsa.sig_to(c, s)

# deterministic ECDSA (RFC 6979), the signature's bytes (empty if it cannot
# be made)
def PkEcdsa.sign(~prm: E.EcParams, ~digest: B.Octets -> B.Octets, ~mac: B.Octets -> B.Octets -> B.Octets, d: N.BnNat, m: B.Octets) -> B.Octets:
  +c = E.EcCurve.of(prm)
  PkEcdsa.sig(c, S.EcDsa.sign_det(~digest, ~mac, c, d, m))

def PkEcdsa.verify(~prm: E.EcParams, ~digest: B.Octets -> B.Octets, q: E.EcPoint, m: B.Octets, s: B.Octets) -> Bool:
  S.EcDsa.verify_bytes(~digest, E.EcCurve.of(prm), q, m, s)

# the named instance: ECDSA over P-256 with SHA-256
def PkEcdsa.p256_sha256_sign(d: N.BnNat, m: B.Octets) -> B.Octets:
  PkEcdsa.sign(~EC.EcCurves.p256(), ~SH.CrSha2.sha256, ~Pk.PkHmac.raw(~64n, ~SH.CrSha2.sha256), d, m)

def PkEcdsa.p256_sha256_verify(q: E.EcPoint, m: B.Octets, s: B.Octets) -> Bool:
  PkEcdsa.verify(~EC.EcCurves.p256(), ~SH.CrSha2.sha256, q, m, s)
