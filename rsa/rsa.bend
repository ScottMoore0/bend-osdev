# bend-osdev-rsa: RSA (RFC 8017, PKCS #1 v2.2).
#
# This file holds the keys and the four primitives of RFC 8017 section 5:
# RSAEP and RSAVP1 (m^e mod n), RSADP and RSASP1 (c^d mod n, with the
# Chinese remainder theorem from p, q, dP, dQ and qInv: section 5.1.2,
# step 2.b), on numbers and on octet strings of the modulus's length
# (OS2IP and I2OSP, section 4). The encodings (EMSA-PKCS1-v1_5, EMSA-PSS,
# EME-OAEP, EME-PKCS1-v1_5), the schemes built from them, key generation
# and the keys' byte forms are in their own files (README.md, "Files").
#
# Keys are plain integers (BnNat): reading them from DER (RFC 8017
# Appendix A.1) is an extension point, left to an ASN.1 package.
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../bignum/modular.bend as Md

# Every failure (the errors RFC 8017 names, and the keys' own)
type RsaError is Data:
  RsaMessageTooLong{}
  RsaDecryptionError{}
  RsaEncodingError{}
  RsaOutOfRange{}
  RsaIntegerTooLarge{}
  RsaBadKey{}
  RsaBadFormat{}
  RsaNoPrime{}

# A public key (n, e) (open)
type RsaPublic is Data:
  RsaPublic{n: N.BnNat, e: N.BnNat}

# A private key in RFC 8017's second form, with n, e and d of the first
# (open): n = p q, d e = 1 mod lcm(p - 1, q - 1), dP = d mod (p - 1),
# dQ = d mod (q - 1), qInv = q^-1 mod p
type RsaPrivate is Data:
  RsaPrivate{n: N.BnNat, e: N.BnNat, d: N.BnNat, p: N.BnNat, q: N.BnNat, dp: N.BnNat, dq: N.BnNat, qinv: N.BnNat}

def RsaError.check(ok: Bool, e: RsaError) -> Result<&2, &2, RsaError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

# the public key of a private key
def Rsa.public(sk: RsaPrivate) -> RsaPublic:
  match sk:
    case RsaPrivate{n, e, d, p, q, dp, dq, qinv}:
      RsaPublic{n, e}

# the modulus's length in bytes (RFC 8017's k)
def Rsa.k(pk: RsaPublic) -> Nat:
  match pk:
    case RsaPublic{n, e}:
      N.BnNat.byte_len(n)

def Rsa.k_of(sk: RsaPrivate) -> Nat:
  match sk:
    case RsaPrivate{n, e, d, p, q, dp, dq, qinv}:
      N.BnNat.byte_len(n)

# the modulus's length in bits
def Rsa.mod_bits(pk: RsaPublic) -> Nat:
  match pk:
    case RsaPublic{n, e}:
      N.BnNat.bit_len(n)

def rsa.three() -> N.BnNat:
  N.BnNat.of_u32(3)

# A public key, checked as RFC 8017 section 3.1 asks: n odd and above 3,
# e odd and in [3, n - 1] (RsaBadKey otherwise)
def Rsa.public_of(+n: N.BnNat, +e: N.BnNat) -> Result<&2, &2, RsaError, RsaPublic>:
  +ok = Bool.and(Bool.and(N.BnNat.is_odd(n), N.BnNat.is_lt(rsa.three(), n)), Bool.and(N.BnNat.is_odd(e), Bool.and(N.BnNat.is_le(rsa.three(), e), N.BnNat.is_lt(e, n))))
  Result.map(&2, &2, RsaError, Unit, RsaPublic, u => RsaPublic{n, e}, RsaError.check(ok, RsaBadKey{}))

def rsa.minus1(+x: N.BnNat) -> N.BnNat:
  N.BnNat.sub(x, N.BnNat.one())

def rsa.crt(+n: N.BnNat, +e: N.BnNat, +d: N.BnNat, +p: N.BnNat, +q: N.BnNat, qi: Maybe<&2, N.BnNat>) -> Result<&2, &2, RsaError, RsaPrivate>:
  match qi:
    case None{}:
      Fail{RsaBadKey{}}
    case Some{qinv}:
      Done{RsaPrivate{n, e, d, p, q, N.BnNat.mod(d, rsa.minus1(p)), N.BnNat.mod(d, rsa.minus1(q)), qinv}}

# A private key from n, e, d, p and q: its CRT values computed, and checked:
# n = p q, p and q above 1, e odd and in [3, n - 1], and d e = 1 modulo
# p - 1 and modulo q - 1 (RsaBadKey otherwise)
def Rsa.private_of(+n: N.BnNat, +e: N.BnNat, +d: N.BnNat, +p: N.BnNat, +q: N.BnNat) -> Result<&2, &2, RsaError, RsaPrivate>:
  +one = N.BnNat.one()
  +ok = Bool.and(Bool.and(N.BnNat.is_eq(N.BnNat.mul(p, q), n), Bool.and(N.BnNat.is_lt(one, p), N.BnNat.is_lt(one, q))), Bool.and(N.BnNat.is_eq(Md.BnMod.mul(d, e, rsa.minus1(p)), N.BnNat.mod(one, rsa.minus1(p))), N.BnNat.is_eq(Md.BnMod.mul(d, e, rsa.minus1(q)), N.BnNat.mod(one, rsa.minus1(q)))))
  Result.bind(&2, &2, RsaError, RsaPublic, RsaPrivate, Rsa.public_of(n, e), pk => Result.bind(&2, &2, RsaError, Unit, RsaPrivate, RsaError.check(ok, RsaBadKey{}), u => rsa.crt(n, e, d, p, q, Md.BnMod.inv(q, p))))

def rsa.of_d(+n: N.BnNat, +e: N.BnNat, +p: N.BnNat, +q: N.BnNat, di: Maybe<&2, N.BnNat>) -> Result<&2, &2, RsaError, RsaPrivate>:
  match di:
    case None{}:
      Fail{RsaBadKey{}}
    case Some{d}:
      Rsa.private_of(n, e, d, p, q)

# A private key from the primes p and q and the public exponent e, with
# d = e^-1 mod lcm(p - 1, q - 1) (FIPS 186-5, Appendix A.1.1); RsaBadKey
# when e has no inverse
def Rsa.private_of_primes(+p: N.BnNat, +q: N.BnNat, +e: N.BnNat) -> Result<&2, &2, RsaError, RsaPrivate>:
  rsa.of_d(N.BnNat.mul(p, q), e, p, q, Md.BnMod.inv(e, Md.BnMod.lcm(rsa.minus1(p), rsa.minus1(q))))

# RSAEP (section 5.1.1) and RSAVP1 (5.2.2): m^e mod n, for m < n
# (RsaOutOfRange otherwise)
def Rsa.ep(pk: RsaPublic, +m: N.BnNat) -> Result<&2, &2, RsaError, N.BnNat>:
  match pk:
    case RsaPublic{+n, e}:
      Result.map(&2, &2, RsaError, Unit, N.BnNat, u => Md.BnMod.exp(m, e, n), RsaError.check(N.BnNat.is_lt(m, n), RsaOutOfRange{}))

def Rsa.vp1(+pk: RsaPublic, +s: N.BnNat) -> Result<&2, &2, RsaError, N.BnNat>:
  Rsa.ep(pk, s)

# c^d mod n by the Chinese remainder theorem (section 5.1.2, step 2.b):
# m1 = c^dP mod p, m2 = c^dQ mod q, h = (m1 - m2) qInv mod p, m = m2 + q h
def rsa.crt_exp(+c: N.BnNat, +p: N.BnNat, +q: N.BnNat, dp: N.BnNat, dq: N.BnNat, qinv: N.BnNat) -> N.BnNat:
  +m1 = Md.BnMod.exp(c, dp, p)
  +m2 = Md.BnMod.exp(c, dq, q)
  N.BnNat.add(m2, N.BnNat.mul(q, Md.BnMod.mul(Md.BnMod.sub(m1, m2, p), qinv, p)))

# RSADP (section 5.1.2) and RSASP1 (5.2.1), by the CRT, for c < n
# (RsaOutOfRange otherwise)
def Rsa.dp(sk: RsaPrivate, +c: N.BnNat) -> Result<&2, &2, RsaError, N.BnNat>:
  match sk:
    case RsaPrivate{n, e, d, p, q, dp, dq, qinv}:
      Result.map(&2, &2, RsaError, Unit, N.BnNat, u => rsa.crt_exp(c, p, q, dp, dq, qinv), RsaError.check(N.BnNat.is_lt(c, n), RsaOutOfRange{}))

def Rsa.sp1(+sk: RsaPrivate, +m: N.BnNat) -> Result<&2, &2, RsaError, N.BnNat>:
  Rsa.dp(sk, m)

# RSADP in the first form (n, d): c^d mod n, without the CRT (the
# reference the CRT form is tested against)
def Rsa.dp_plain(sk: RsaPrivate, +c: N.BnNat) -> Result<&2, &2, RsaError, N.BnNat>:
  match sk:
    case RsaPrivate{+n, e, d, p, q, dp, dq, qinv}:
      Result.map(&2, &2, RsaError, Unit, N.BnNat, u => Md.BnMod.exp(c, d, n), RsaError.check(N.BnNat.is_lt(c, n), RsaOutOfRange{}))

def rsa.i2osp.go(m: Maybe<&2, B.Octets>) -> Result<&2, &2, RsaError, B.Octets>:
  match m:
    case None{}:
      Fail{RsaIntegerTooLarge{}}
    case Some{o}:
      Done{o}

# I2OSP to k bytes, as a Result (RsaIntegerTooLarge)
def Rsa.i2osp(+x: N.BnNat, +k: Nat) -> Result<&2, &2, RsaError, B.Octets>:
  rsa.i2osp.go(N.BnNat.to_octets(x, k))

# The primitives on octet strings of the modulus's length k: OS2IP, the
# primitive, I2OSP to k bytes. A string of another length is refused
# (RsaOutOfRange)
def Rsa.ep_octets(+pk: RsaPublic, +m: B.Octets) -> Result<&2, &2, RsaError, B.Octets>:
  +k = Rsa.k(pk)
  Result.bind(&2, &2, RsaError, Unit, B.Octets, RsaError.check(Nat.is_eq(B.Octets.len(m), k), RsaOutOfRange{}), u => Result.bind(&2, &2, RsaError, N.BnNat, B.Octets, Rsa.ep(pk, N.BnNat.of_octets(m)), x => Rsa.i2osp(x, k)))

def Rsa.dp_octets(+sk: RsaPrivate, +c: B.Octets) -> Result<&2, &2, RsaError, B.Octets>:
  +k = Rsa.k_of(sk)
  Result.bind(&2, &2, RsaError, Unit, B.Octets, RsaError.check(Nat.is_eq(B.Octets.len(c), k), RsaOutOfRange{}), u => Result.bind(&2, &2, RsaError, N.BnNat, B.Octets, Rsa.dp(sk, N.BnNat.of_octets(c)), x => Rsa.i2osp(x, k)))
