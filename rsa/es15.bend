# EME-PKCS1-v1_5 and RSAES-PKCS1-v1_5 (RFC 8017, section 7.2):
#   EM = 0x00 || 0x02 || PS || 0x00 || M,
# PS at least eight nonzero random bytes, k - mLen - 3 of them. PS is a
# parameter: the caller's random bytes, of exactly that length and with no
# zero byte. RFC 8017 recommends OAEP for new applications; this scheme is
# here for compatibility, and its decryption answers one error for every
# failure (section 7.2.2, Note).
#
# Decoding reads EM's bytes as a list: two leading bytes 0x00 0x02, then PS
# up to the first zero byte, at least eight bytes long, then M. LAWS.bend's
# es15_round_trip proves that it undoes the encoding.
import Base
import ../bytes/bytes.bend as B
import ./rsa.bend as R
import ./octets.bend as O

def rsa.es15.enc(fits: Bool, good: Bool, m: B.Octets, ps: B.Octets) -> Result<&2, &2, R.RsaError, B.Octets>:
  match fits good:
    case False{} _:
      Fail{R.RsaMessageTooLong{}}
    case True{} False{}:
      Fail{R.RsaEncodingError{}}
    case True{} True{}:
      Done{B.Octets.append(B.Octets.of_list([0, 2]), B.Octets.append(ps, B.Octets.append(B.Octets.of_list([0]), m)))}

# EME-PKCS1-v1_5 encoding of M to k bytes with the padding string PS:
# RsaMessageTooLong when mLen > k - 11, RsaEncodingError for a PS of the
# wrong length (k - mLen - 3, at least 8) or with a zero byte
def RsaEs15.encode(+m: B.Octets, +ps: B.Octets, +k: Nat) -> Result<&2, &2, R.RsaError, B.Octets>:
  rsa.es15.enc(Nat.is_le(Nat.add(B.Octets.len(m), 11n), k), Bool.and(Bool.and(Nat.is_eq(Nat.add(B.Octets.len(ps), Nat.add(B.Octets.len(m), 3n)), k), Nat.is_le(8n, B.Octets.len(ps))), O.RsaOct.no_zero(ps)), m, ps)

def rsa.es15.zero.go(z: Bool, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match z:
    case True{}:
      Some{0n}
    case False{}:
      Maybe.map(&2, Nat, Nat, i => 1n+i, rest)

# the index of the first zero byte
def rsa.es15.zero(xs: List<&2, U32>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, t}:
      rsa.es15.zero.go(U32.is_zero(x), rsa.es15.zero(t))

def rsa.es15.dec.len(long: Bool, +i: Nat, t: List<&2, U32>) -> Result<&2, &2, R.RsaError, B.Octets>:
  match long:
    case True{}:
      Done{B.Octets.of_list(B.drop(Nat.add(i, 1n), t))}
    case False{}:
      Fail{R.RsaDecryptionError{}}

def rsa.es15.dec.msg(z: Maybe<&2, Nat>, t: List<&2, U32>) -> Result<&2, &2, R.RsaError, B.Octets>:
  match z:
    case None{}:
      Fail{R.RsaDecryptionError{}}
    case Some{+i}:
      rsa.es15.dec.len(Nat.is_le(8n, i), i, t)

def rsa.es15.dec.head(ok: Bool, +t: List<&2, U32>) -> Result<&2, &2, R.RsaError, B.Octets>:
  match ok:
    case True{}:
      rsa.es15.dec.msg(rsa.es15.zero(t), t)
    case False{}:
      Fail{R.RsaDecryptionError{}}

def rsa.es15.dec(xs: List<&2, U32>) -> Result<&2, &2, R.RsaError, B.Octets>:
  match xs:
    case Con{a, Con{b, t}}:
      rsa.es15.dec.head(Bool.and(U32.is_zero(a), U32.is_eq(b, 2)), t)
    case _:
      Fail{R.RsaDecryptionError{}}

# EME-PKCS1-v1_5 decoding of EM: M, or RsaDecryptionError
def RsaEs15.decode(em: B.Octets) -> Result<&2, &2, R.RsaError, B.Octets>:
  rsa.es15.dec(B.Octets.to_list(em))

# RSAES-PKCS1-V1_5-ENCRYPT((n, e), M) (section 7.2.1) with the padding
# string PS
def RsaEs15.encrypt(+pk: R.RsaPublic, m: B.Octets, ps: B.Octets) -> Result<&2, &2, R.RsaError, B.Octets>:
  Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, RsaEs15.encode(m, ps, R.Rsa.k(pk)), em => R.Rsa.ep_octets(pk, em))

def rsa.es15.dec2(r: Result<&2, &2, R.RsaError, B.Octets>) -> Result<&2, &2, R.RsaError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{R.RsaDecryptionError{}}
    case Done{em}:
      RsaEs15.decode(em)

# RSAES-PKCS1-V1_5-DECRYPT(K, C) (section 7.2.2): RsaDecryptionError for a
# modulus shorter than 11 bytes, a C of another length than the modulus's,
# a representative out of range, or a bad encoding
def RsaEs15.decrypt(+sk: R.RsaPrivate, c: B.Octets) -> Result<&2, &2, R.RsaError, B.Octets>:
  Result.bind(&2, &2, R.RsaError, Unit, B.Octets, R.RsaError.check(Nat.is_le(11n, R.Rsa.k_of(sk)), R.RsaDecryptionError{}), u => rsa.es15.dec2(R.Rsa.dp_octets(sk, c)))
