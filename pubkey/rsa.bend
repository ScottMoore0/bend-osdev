# RSA (the rsa package, RFC 8017) as instances of the signature interface
# (crypto's sign.bend): RSASSA-PKCS1-v1_5 and RSASSA-PSS over any hash, with the
# keys in the rsa package's raw byte form (rsa/keys.bend).
#
# RSASSA-PKCS1-v1_5 over a hash (~digest) with its DigestInfo prefix
# (~prefix, rsa/pkcs1.bend's RsaDigestInfo.*):
#   ~R.RsaPrivate, ~R.RsaPublic, ~PkRsa.secret, ~R.Rsa.public, ~PkRsa.pk_of,
#   ~K.RsaKeys.public_to, ~PkRsa.pkcs1_sign(~digest, ~prefix),
#   ~PkRsa.pkcs1_verify(~digest, ~prefix)
# RSASSA-PSS over a hash with MGF1 over the same hash and a salt of ~slen
# bytes: the same with ~PkRsa.pss_sign(~digest, ~slen) and
# ~PkRsa.pss_verify(~digest, ~slen). The interface's sign is deterministic,
# so its PSS salt is derived (PkRsa.pss_salt: MGF1 over the hash of the
# private key's form and the message, the first slen bytes); RFC 8017's
# verification accepts any salt of the expected length, and rsa's own
# RsaPss.sign takes a random salt from the caller. A signature that cannot
# be made (a modulus too short for the encoding) is empty, which every
# verifier refuses.
#
# The named instances over SHA-256 are PkRsa.pkcs1_sha256_sign and
# _verify, and PkRsa.pss_sha256_sign and _verify (32-byte salts).
import Base
import ../bytes/bytes.bend as B
import ../rsa/rsa.bend as R
import ../rsa/keys.bend as K
import ../rsa/mgf1.bend as G
import ../rsa/pkcs1.bend as P
import ../rsa/pss.bend as S
import ../crypto/crypto.bend as Cr
import ../crypto/inst_sha2.bend as SH

# rsa's errors onto CrError
def PkRsa.err(e: R.RsaError) -> Cr.CrError:
  match e:
    case R.RsaMessageTooLong{}:
      Cr.CrTooLong{0n}
    case R.RsaDecryptionError{}:
      Cr.CrBadPadding{}
    case R.RsaEncodingError{}:
      Cr.CrBadOutputLength{0n}
    case R.RsaOutOfRange{}:
      Cr.CrBadPadding{}
    case R.RsaIntegerTooLarge{}:
      Cr.CrBadPadding{}
    case R.RsaBadKey{}:
      Cr.CrBadKey{}
    case R.RsaBadFormat{}:
      Cr.CrBadKey{}
    case R.RsaNoPrime{}:
      Cr.CrBadKey{}

def PkRsa.err_pk(e: R.RsaError) -> Cr.CrError:
  Cr.CrBadPublicKey{}

# a private key from its form (CrBadKey)
def PkRsa.secret(o: B.Octets) -> Result<&2, &2, Cr.CrError, R.RsaPrivate>:
  Cr.CrError.lift(~R.RsaError, ~R.RsaPrivate, ~PkRsa.err, K.RsaKeys.private_of(o))

# a public key from its form (CrBadPublicKey)
def PkRsa.pk_of(o: B.Octets) -> Result<&2, &2, Cr.CrError, R.RsaPublic>:
  Cr.CrError.lift(~R.RsaError, ~R.RsaPublic, ~PkRsa.err_pk, K.RsaKeys.public_of(o))

# RSASSA-PKCS1-v1_5 signature (empty if it cannot be made)
def PkRsa.pkcs1_sign(~digest: B.Octets -> B.Octets, ~prefix: B.Octets, sk: R.RsaPrivate, m: B.Octets) -> B.Octets:
  Result.default(&2, &2, R.RsaError, B.Octets, P.RsaPkcs1.sign(~digest, prefix, sk, m), B.Octets.empty())

def PkRsa.pkcs1_verify(~digest: B.Octets -> B.Octets, ~prefix: B.Octets, pk: R.RsaPublic, m: B.Octets, s: B.Octets) -> Bool:
  P.RsaPkcs1.verify(~digest, prefix, pk, m, s)

# the derived PSS salt: the first slen bytes of MGF1(Hash(form(sk) || M))
def PkRsa.pss_salt(~digest: B.Octets -> B.Octets, ~slen: Nat, sk: R.RsaPrivate, m: B.Octets) -> B.Octets:
  G.RsaMgf1.mask(~digest, digest(B.Octets.append(K.RsaKeys.private_to(sk), m)), slen)

# RSASSA-PSS signature with the derived salt (empty if it cannot be made)
def PkRsa.pss_sign(~digest: B.Octets -> B.Octets, ~slen: Nat, +sk: R.RsaPrivate, +m: B.Octets) -> B.Octets:
  Result.default(&2, &2, R.RsaError, B.Octets, S.RsaPss.sign(~digest, ~G.RsaMgf1.mask(~digest), sk, m, PkRsa.pss_salt(~digest, ~slen, sk, m)), B.Octets.empty())

def PkRsa.pss_verify(~digest: B.Octets -> B.Octets, ~slen: Nat, pk: R.RsaPublic, m: B.Octets, s: B.Octets) -> Bool:
  S.RsaPss.verify(~digest, ~G.RsaMgf1.mask(~digest), pk, m, s, slen)

# the named instances over SHA-256
def PkRsa.pkcs1_sha256_sign(sk: R.RsaPrivate, m: B.Octets) -> B.Octets:
  PkRsa.pkcs1_sign(~SH.CrSha2.sha256, ~P.RsaDigestInfo.sha256(), sk, m)

def PkRsa.pkcs1_sha256_verify(pk: R.RsaPublic, m: B.Octets, s: B.Octets) -> Bool:
  PkRsa.pkcs1_verify(~SH.CrSha2.sha256, ~P.RsaDigestInfo.sha256(), pk, m, s)

def PkRsa.pss_sha256_sign(sk: R.RsaPrivate, m: B.Octets) -> B.Octets:
  PkRsa.pss_sign(~SH.CrSha2.sha256, ~32n, sk, m)

def PkRsa.pss_sha256_verify(pk: R.RsaPublic, m: B.Octets, s: B.Octets) -> Bool:
  PkRsa.pss_verify(~SH.CrSha2.sha256, ~32n, pk, m, s)
