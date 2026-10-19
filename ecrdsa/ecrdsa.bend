# bend-osdev-ecrdsa: GOST R 34.10-2012 digital signatures (EC-RDSA), as
# RFC 7091 ("GOST R 34.10-2012: Digital Signature Algorithm", V. Dolmatov
# and A. Degtyarev, 2013) sets it out, sections 6.1 (generation) and 6.2
# (verification), over any curve of the ecc package (RFC 4357's CryptoPro
# parameter sets are named there) and any hash (~digest; Streebog-256 and
# Streebog-512 from the hashes package, the named defaults):
#   e = alpha mod q, alpha the integer whose binary representation is the
#       hash vector h (e = 1 if that is 0),
#   sign: C = k P, r = x_C mod q != 0, s = (r d + k e) mod q != 0,
#   verify: 0 < r < q, 0 < s < q, v = e^-1 mod q, z1 = s v mod q,
#       z2 = -r v mod q, C = z1 P + z2 Q, accept iff x_C mod q = r.
# A hash vector's components are numbered from the right (RFC 6986, section
# 4.2), and the hashes package outputs them from component 0: alpha is the
# digest's bytes read least significant first.
#
# Keys and signatures travel as RFC 4491 ("Using the GOST R 34.10-94,
# GOST R 34.10-2001, and GOST R 34.11-94 Algorithms with the Internet X.509
# Public Key Infrastructure", 2006) carries them: a public key as x then y,
# each little-endian, the field's length (section 2.3.2); a signature as s
# then r, each big-endian, q's length (section 2.2.2).
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../bignum/modular.bend as Md
import ../ecc/ecc.bend as E
import ../ecc/ecdsa.bend as S
import ../ecc/rfc6979.bend as R
import ../hashes/streebog.bend as Stb

# Every failure
type EcrdsaError is Data:
  EcrdsaBadNonce{}
  EcrdsaBadPrivateKey{}
  EcrdsaBadPublicKey{}

def EcrdsaError.check(ok: Bool, e: EcrdsaError) -> Result<&2, &2, EcrdsaError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

# Streebog-256 and Streebog-512 (RFC 6986, the hashes package), the named
# defaults for 256- and 512-bit curves
def Ecrdsa.streebog256(o: B.Octets) -> B.Octets:
  Stb.HsStreebog.digest256(o)

def Ecrdsa.streebog512(o: B.Octets) -> B.Octets:
  Stb.HsStreebog.digest512(o)

def ecrdsa.one_if_zero(z: Bool, +e: N.BnNat) -> N.BnNat:
  match z:
    case True{}:
      N.BnNat.one()
    case False{}:
      e

# e from a hash value h (section 6.1, step 2)
def Ecrdsa.e(+c: E.EcCurve, h: B.Octets) -> N.BnNat:
  +e = N.BnNat.mod(N.BnNat.of_octets(B.Octets.of_list(B.rev(B.Octets.to_list(h)))), E.EcCurve.n(c))
  ecrdsa.one_if_zero(N.BnNat.is_zero(e), e)

# the public key Q = d P
def Ecrdsa.public(+c: E.EcCurve, +d: N.BnNat) -> E.EcPoint:
  E.EcCurve.base_mul(c, d)

def ecrdsa.in_range(+x: N.BnNat, +n: N.BnNat) -> Bool:
  Bool.and(Bool.not(N.BnNat.is_zero(x)), N.BnNat.is_lt(x, n))

# A private key from big-endian bytes (EcrdsaBadPrivateKey outside
# [1, q - 1])
def Ecrdsa.private_of(+c: E.EcCurve, o: B.Octets) -> Result<&2, &2, EcrdsaError, N.BnNat>:
  +d = N.BnNat.of_octets(o)
  Result.map(&2, &2, EcrdsaError, Unit, N.BnNat, u => d, EcrdsaError.check(ecrdsa.in_range(d, E.EcCurve.n(c)), EcrdsaBadPrivateKey{}))

def ecrdsa.sig(+r: N.BnNat, +s: N.BnNat) -> Result<&2, &2, EcrdsaError, S.EcSig>:
  Result.map(&2, &2, EcrdsaError, Unit, S.EcSig, u => S.EcSig{r, s}, EcrdsaError.check(Bool.and(Bool.not(N.BnNat.is_zero(r)), Bool.not(N.BnNat.is_zero(s))), EcrdsaBadNonce{}))

def ecrdsa.sign.go(+c: E.EcCurve, d: N.BnNat, +e: N.BnNat, +k: N.BnNat) -> Result<&2, &2, EcrdsaError, S.EcSig>:
  +q = E.EcCurve.n(c)
  +r = N.BnNat.mod(E.EcPoint.x(E.EcCurve.base_mul(c, k)), q)
  ecrdsa.sig(r, Md.BnMod.add(Md.BnMod.mul(r, d, q), Md.BnMod.mul(k, e, q), q))

# The signature for e under the private key d with the per-message secret
# k (section 6.1, steps 3 to 6): EcrdsaBadNonce for k outside (0, q), or
# when r or s is 0 (the caller takes another k)
def Ecrdsa.sign_e(+c: E.EcCurve, d: N.BnNat, +e: N.BnNat, +k: N.BnNat) -> Result<&2, &2, EcrdsaError, S.EcSig>:
  Result.bind(&2, &2, EcrdsaError, Unit, S.EcSig, EcrdsaError.check(ecrdsa.in_range(k, E.EcCurve.n(c)), EcrdsaBadNonce{}), u => ecrdsa.sign.go(c, d, e, k))

def ecrdsa.verify.go(+c: E.EcCurve, q: E.EcPoint, +e: N.BnNat, +r: N.BnNat, s: N.BnNat) -> Bool:
  +n = E.EcCurve.n(c)
  +v = Maybe.default(&2, N.BnNat, Md.BnMod.inv(e, n), N.BnNat.zero())
  +z1 = Md.BnMod.mul(s, v, n)
  +z2 = Md.BnMod.sub(N.BnNat.zero(), Md.BnMod.mul(r, v, n), n)
  +p = E.EcCurve.mul2(c, z1, E.EcCurve.generator(c), z2, q)
  Bool.and(Bool.not(E.EcPoint.is_inf(p)), N.BnNat.is_eq(N.BnNat.mod(E.EcPoint.x(p), n), r))

# whether sig is a valid signature for e under the public key Q (section
# 6.2)
def Ecrdsa.verify_e(+c: E.EcCurve, q: E.EcPoint, +e: N.BnNat, sig: S.EcSig) -> Bool:
  match sig:
    case S.EcSig{+r, +s}:
      +n = E.EcCurve.n(c)
      Bool.and(Bool.and(ecrdsa.in_range(r, n), ecrdsa.in_range(s, n)), ecrdsa.verify.go(c, q, e, r, s))

# The signature of M with the per-message secret k
def Ecrdsa.sign(~digest: B.Octets -> B.Octets, +c: E.EcCurve, d: N.BnNat, m: B.Octets, +k: N.BnNat) -> Result<&2, &2, EcrdsaError, S.EcSig>:
  Ecrdsa.sign_e(c, d, Ecrdsa.e(c, digest(m)), k)

# The same with a deterministic k: RFC 6979's construction over the HMAC
# ~mac, from d and the hash value (not part of GOST R 34.10-2012, which asks
# for a random k; verification cannot tell the difference)
def Ecrdsa.sign_det(~digest: B.Octets -> B.Octets, ~mac: B.Octets -> B.Octets -> B.Octets, +c: E.EcCurve, +d: N.BnNat, m: B.Octets) -> Result<&2, &2, EcrdsaError, S.EcSig>:
  +h = digest(m)
  Ecrdsa.sign_e(c, d, Ecrdsa.e(c, h), R.EcRfc6979.k(~mac, E.EcCurve.n(c), d, h))

# whether sig is a valid signature of M under Q
def Ecrdsa.verify(~digest: B.Octets -> B.Octets, +c: E.EcCurve, q: E.EcPoint, m: B.Octets, sig: S.EcSig) -> Bool:
  Ecrdsa.verify_e(c, q, Ecrdsa.e(c, digest(m)), sig)

def ecrdsa.be(+x: N.BnNat, +l: Nat) -> B.Octets:
  Maybe.default(&2, B.Octets, N.BnNat.to_octets(x, l), B.Octets.zeros(l))

def ecrdsa.le(+x: N.BnNat, +l: Nat) -> B.Octets:
  B.Octets.of_list(B.rev(B.Octets.to_list(ecrdsa.be(x, l))))

def ecrdsa.of_le(o: B.Octets) -> N.BnNat:
  N.BnNat.of_octets(B.Octets.of_list(B.rev(B.Octets.to_list(o))))

# A signature's bytes (RFC 4491, 2.2.2): s then r, big-endian, q's length
def Ecrdsa.sig_to(+c: E.EcCurve, sig: S.EcSig) -> B.Octets:
  match sig:
    case S.EcSig{r, s}:
      +l = E.EcCurve.order_len(c)
      B.Octets.append(ecrdsa.be(s, l), ecrdsa.be(r, l))

def ecrdsa.sig_of.go(ok: Bool, +l: Nat, +o: B.Octets) -> Maybe<&2, S.EcSig>:
  match ok:
    case True{}:
      Some{S.EcSig{N.BnNat.of_octets(B.Octets.drop(l, o)), N.BnNat.of_octets(B.Octets.take(l, o))}}
    case False{}:
      None{}

# A signature from its bytes (None for another length than twice q's)
def Ecrdsa.sig_of(+c: E.EcCurve, +o: B.Octets) -> Maybe<&2, S.EcSig>:
  +l = E.EcCurve.order_len(c)
  ecrdsa.sig_of.go(Nat.is_eq(B.Octets.len(o), Nat.mul(2n, l)), l, o)

# A public key's bytes (RFC 4491, 2.3.2): x then y, little-endian, the
# field's length
def Ecrdsa.public_to(+c: E.EcCurve, +q: E.EcPoint) -> B.Octets:
  +l = E.EcCurve.field_len(c)
  B.Octets.append(ecrdsa.le(E.EcPoint.x(q), l), ecrdsa.le(E.EcPoint.y(q), l))

def ecrdsa.pk.go(ok: Bool, +c: E.EcCurve, +o: B.Octets) -> Result<&2, &2, EcrdsaError, E.EcPoint>:
  match ok:
    case False{}:
      Fail{EcrdsaBadPublicKey{}}
    case True{}:
      +l = E.EcCurve.field_len(c)
      +p = {E.EcAff{ecrdsa.of_le(B.Octets.take(l, o)), ecrdsa.of_le(B.Octets.drop(l, o))} : E.EcPoint}
      Result.map(&2, &2, EcrdsaError, Unit, E.EcPoint, u => p, EcrdsaError.check(E.EcCurve.on_curve(c, p), EcrdsaBadPublicKey{}))

# A public key from its bytes: twice the field's length, and a point of the
# curve (EcrdsaBadPublicKey otherwise)
def Ecrdsa.public_of(+c: E.EcCurve, +o: B.Octets) -> Result<&2, &2, EcrdsaError, E.EcPoint>:
  ecrdsa.pk.go(Nat.is_eq(B.Octets.len(o), Nat.mul(2n, E.EcCurve.field_len(c))), c, o)

def ecrdsa.verify_bytes.go(~digest: B.Octets -> B.Octets, +c: E.EcCurve, q: E.EcPoint, m: B.Octets, s: Maybe<&2, S.EcSig>) -> Bool:
  match s:
    case None{}:
      False{}
    case Some{sig}:
      Ecrdsa.verify(~digest, c, q, m, sig)

# whether the bytes (RFC 4491's form) are a valid signature of M under Q
def Ecrdsa.verify_bytes(~digest: B.Octets -> B.Octets, +c: E.EcCurve, q: E.EcPoint, m: B.Octets, +s: B.Octets) -> Bool:
  ecrdsa.verify_bytes.go(~digest, c, q, m, Ecrdsa.sig_of(c, s))
