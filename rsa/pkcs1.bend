# EMSA-PKCS1-v1_5 (RFC 8017, section 9.2) and RSASSA-PKCS1-v1_5 (section
# 8.2), over any hash (~digest, one-shot) and its DigestInfo prefix:
#   EM = 0x00 || 0x01 || PS || 0x00 || T,  T = prefix || Hash(M),
# PS at least eight bytes of 0xff. The prefixes of section 9.2, Note 1, are
# named below; any other hash brings its own (the DER of its DigestInfo up
# to the digest).
import Base
import ../bytes/bytes.bend as B
import ./rsa.bend as R
import ./octets.bend as O

# The DER encodings of DigestInfo before the digest (RFC 8017, section 9.2,
# Note 1)
def RsaDigestInfo.md2() -> B.Octets:
  B.Octets.of_list([48, 32, 48, 12, 6, 8, 42, 134, 72, 134, 247, 13, 2, 2, 5, 0, 4, 16])

def RsaDigestInfo.md5() -> B.Octets:
  B.Octets.of_list([48, 32, 48, 12, 6, 8, 42, 134, 72, 134, 247, 13, 2, 5, 5, 0, 4, 16])

def RsaDigestInfo.sha1() -> B.Octets:
  B.Octets.of_list([48, 33, 48, 9, 6, 5, 43, 14, 3, 2, 26, 5, 0, 4, 20])

def RsaDigestInfo.sha224() -> B.Octets:
  B.Octets.of_list([48, 45, 48, 13, 6, 9, 96, 134, 72, 1, 101, 3, 4, 2, 4, 5, 0, 4, 28])

def RsaDigestInfo.sha256() -> B.Octets:
  B.Octets.of_list([48, 49, 48, 13, 6, 9, 96, 134, 72, 1, 101, 3, 4, 2, 1, 5, 0, 4, 32])

def RsaDigestInfo.sha384() -> B.Octets:
  B.Octets.of_list([48, 65, 48, 13, 6, 9, 96, 134, 72, 1, 101, 3, 4, 2, 2, 5, 0, 4, 48])

def RsaDigestInfo.sha512() -> B.Octets:
  B.Octets.of_list([48, 81, 48, 13, 6, 9, 96, 134, 72, 1, 101, 3, 4, 2, 3, 5, 0, 4, 64])

def RsaDigestInfo.sha512_224() -> B.Octets:
  B.Octets.of_list([48, 45, 48, 13, 6, 9, 96, 134, 72, 1, 101, 3, 4, 2, 5, 5, 0, 4, 28])

def RsaDigestInfo.sha512_256() -> B.Octets:
  B.Octets.of_list([48, 49, 48, 13, 6, 9, 96, 134, 72, 1, 101, 3, 4, 2, 6, 5, 0, 4, 32])

def rsa.emsa15.build(+t: B.Octets, +emlen: Nat) -> B.Octets:
  B.Octets.append(B.Octets.of_list([0, 1]), B.Octets.append(O.RsaOct.rep(Nat.sub(emlen, Nat.add(B.Octets.len(t), 3n)), 255), B.Octets.append(B.Octets.of_list([0]), t)))

# EMSA-PKCS1-v1_5-ENCODE(M, emLen): RsaEncodingError ("intended encoded
# message length too short") when emLen < tLen + 11
def RsaPkcs1.encode(~digest: B.Octets -> B.Octets, prefix: B.Octets, m: B.Octets, +emlen: Nat) -> Result<&2, &2, R.RsaError, B.Octets>:
  +t = B.Octets.append(prefix, digest(m))
  Result.map(&2, &2, R.RsaError, Unit, B.Octets, u => rsa.emsa15.build(t, emlen), R.RsaError.check(Nat.is_le(Nat.add(B.Octets.len(t), 11n), emlen), R.RsaEncodingError{}))

# RSASSA-PKCS1-V1_5-SIGN(K, M) (section 8.2.1): the k-byte signature
def RsaPkcs1.sign(~digest: B.Octets -> B.Octets, prefix: B.Octets, +sk: R.RsaPrivate, m: B.Octets) -> Result<&2, &2, R.RsaError, B.Octets>:
  Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, RsaPkcs1.encode(~digest, prefix, m, R.Rsa.k_of(sk)), em => R.Rsa.dp_octets(sk, em))

def rsa.pkcs1.cmp(r: Result<&2, &2, R.RsaError, B.Octets>, em: B.Octets) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{em2}:
      B.Octets.is_eq(em, em2)

def rsa.pkcs1.check(~digest: B.Octets -> B.Octets, r: Result<&2, &2, R.RsaError, B.Octets>, prefix: B.Octets, m: B.Octets, +k: Nat) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{em}:
      rsa.pkcs1.cmp(RsaPkcs1.encode(~digest, prefix, m, k), em)

# RSASSA-PKCS1-V1_5-VERIFY((n, e), M, S) (section 8.2.2): whether S is a
# valid signature of M ("invalid signature" for every failure: a length
# other than k, a representative out of range, an encoding that differs)
def RsaPkcs1.verify(~digest: B.Octets -> B.Octets, prefix: B.Octets, +pk: R.RsaPublic, m: B.Octets, s: B.Octets) -> Bool:
  rsa.pkcs1.check(~digest, R.Rsa.ep_octets(pk, s), prefix, m, R.Rsa.k(pk))
