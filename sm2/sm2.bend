# bend-osdev-sm2: the SM2 digital signature algorithm (GB/T 32918.2-2016,
# as the IETF draft draft-shen-sm2-ecdsa-02, "SM2 Digital Signature
# Algorithm", S. Shen and X. Lee, 2014, sets it out), over any curve of the
# ecc package (SM2's recommended curve by default) and any hash (~digest;
# SM3, the sm3 package's, the named default):
#   Z_A = H(ENTL_A || ID_A || a || b || x_G || y_G || x_A || y_A),
#   e = H(Z_A || M) as an integer,
#   sign: (x1, y1) = k G, r = (e + x1) mod n (refused if r = 0 or r + k = n),
#         s = (1 + d_A)^-1 (k - r d_A) mod n (refused if s = 0),
#   verify: r, s in [1, n - 1], t = (r + s) mod n != 0,
#         (x1, y1) = s G + t P_A, accept iff (e + x1) mod n = r.
# ENTL_A is ID_A's length in bits as two big-endian bytes; a, b and the
# coordinates are big-endian, the field's length. The per-message secret k
# is a parameter (random, from the caller), or, for a deterministic signer
# (pubkey's signature instance), RFC 6979's construction over
# an HMAC with e in place of the message hash (Sm2.sign_det: not part of
# the SM2 standard, which asks for a random k; verification cannot tell the
# difference).
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../bignum/modular.bend as Md
import ../ecc/ecc.bend as E
import ../ecc/ecdsa.bend as S
import ../ecc/rfc6979.bend as R
import ../sm3/sm3.bend as Sm3

# Every failure
type Sm2Error is Data:
  Sm2BadNonce{}
  Sm2BadPrivateKey{}
  Sm2IdTooLong{}

def Sm2Error.check(ok: Bool, e: Sm2Error) -> Result<&2, &2, Sm2Error, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

# SM3, the named default hash (GB/T 32905, the sm3 package)
def Sm2.sm3(o: B.Octets) -> B.Octets:
  Sm3.HsSm3.digest(o)

def sm2.fe(+c: E.EcCurve, x: N.BnNat) -> B.Octets:
  +l = E.EcCurve.field_len(c)
  Maybe.default(&2, B.Octets, N.BnNat.to_octets(x, l), B.Octets.zeros(l))

# whether ID_A's length in bits fits ENTL_A's two bytes
def Sm2.id_ok(+id: B.Octets) -> Bool:
  Nat.is_lt(Nat.mul(8n, B.Octets.len(id)), 65536n)

# Z_A, the hash of the signer's identity and key with the curve
def Sm2.za(~digest: B.Octets -> B.Octets, +c: E.EcCurve, +id: B.Octets, +pk: E.EcPoint) -> B.Octets:
  +prm = E.EcCurve.params(c)
  +g = E.EcCurve.generator(c)
  +entl = B.Octets.be16(U32.from_nat(Nat.mul(8n, B.Octets.len(id))))
  digest(B.Octets.concat([entl, id, sm2.fe(c, E.EcParams.a(prm)), sm2.fe(c, E.EcParams.b(prm)), sm2.fe(c, E.EcPoint.x(g)), sm2.fe(c, E.EcPoint.y(g)), sm2.fe(c, E.EcPoint.x(pk)), sm2.fe(c, E.EcPoint.y(pk))]))

# e = H(Z_A || M) as an integer
def Sm2.e(~digest: B.Octets -> B.Octets, +c: E.EcCurve, +id: B.Octets, +pk: E.EcPoint, m: B.Octets) -> N.BnNat:
  N.BnNat.of_octets(digest(B.Octets.append(Sm2.za(~digest, c, id, pk), m)))

# the public key d G
def Sm2.public(+c: E.EcCurve, +d: N.BnNat) -> E.EcPoint:
  E.EcCurve.base_mul(c, d)

# whether d is a private key: 1 <= d <= n - 2 (so that 1 + d is invertible)
def Sm2.private_ok(+c: E.EcCurve, +d: N.BnNat) -> Bool:
  Bool.and(Bool.not(N.BnNat.is_zero(d)), N.BnNat.is_lt(N.BnNat.add(d, N.BnNat.one()), E.EcCurve.n(c)))

# A private key from big-endian bytes (Sm2BadPrivateKey outside
# [1, n - 2])
def Sm2.private_of(+c: E.EcCurve, o: B.Octets) -> Result<&2, &2, Sm2Error, N.BnNat>:
  +d = N.BnNat.of_octets(o)
  Result.map(&2, &2, Sm2Error, Unit, N.BnNat, u => d, Sm2Error.check(Sm2.private_ok(c, d), Sm2BadPrivateKey{}))

def sm2.sig(+r: N.BnNat, +s: N.BnNat, +k: N.BnNat, +n: N.BnNat) -> Result<&2, &2, Sm2Error, S.EcSig>:
  +ok = Bool.and(Bool.and(Bool.not(N.BnNat.is_zero(r)), Bool.not(N.BnNat.is_eq(N.BnNat.add(r, k), n))), Bool.not(N.BnNat.is_zero(s)))
  Result.map(&2, &2, Sm2Error, Unit, S.EcSig, u => S.EcSig{r, s}, Sm2Error.check(ok, Sm2BadNonce{}))

def sm2.sign.go(+c: E.EcCurve, +d: N.BnNat, +e: N.BnNat, +k: N.BnNat) -> Result<&2, &2, Sm2Error, S.EcSig>:
  +n = E.EcCurve.n(c)
  +r = Md.BnMod.add(e, E.EcPoint.x(E.EcCurve.base_mul(c, k)), n)
  +inv = Maybe.default(&2, N.BnNat, Md.BnMod.inv(N.BnNat.add(d, N.BnNat.one()), n), N.BnNat.zero())
  sm2.sig(r, Md.BnMod.mul(inv, Md.BnMod.sub(k, Md.BnMod.mul(r, d, n), n), n), k, n)

# The signature for e under the private key d with the per-message secret
# k (Sm2BadNonce for k outside [1, n - 1], or when r = 0, r + k = n or
# s = 0: the caller takes another k)
def Sm2.sign_e(+c: E.EcCurve, +d: N.BnNat, +e: N.BnNat, +k: N.BnNat) -> Result<&2, &2, Sm2Error, S.EcSig>:
  +n = E.EcCurve.n(c)
  Result.bind(&2, &2, Sm2Error, Unit, S.EcSig, Sm2Error.check(Bool.and(Bool.not(N.BnNat.is_zero(k)), N.BnNat.is_lt(k, n)), Sm2BadNonce{}), u => sm2.sign.go(c, d, e, k))

def sm2.verify.go(+c: E.EcCurve, +pk: E.EcPoint, +e: N.BnNat, +r: N.BnNat, +s: N.BnNat) -> Bool:
  +n = E.EcCurve.n(c)
  +t = Md.BnMod.add(r, s, n)
  +p = E.EcCurve.mul2(c, s, E.EcCurve.generator(c), t, pk)
  Bool.and(Bool.and(Bool.not(N.BnNat.is_zero(t)), Bool.not(E.EcPoint.is_inf(p))), N.BnNat.is_eq(Md.BnMod.add(e, E.EcPoint.x(p), n), r))

def sm2.in_range(+x: N.BnNat, +n: N.BnNat) -> Bool:
  Bool.and(Bool.not(N.BnNat.is_zero(x)), N.BnNat.is_lt(x, n))

# whether sig is a valid signature for e under the public key P_A
def Sm2.verify_e(+c: E.EcCurve, +pk: E.EcPoint, +e: N.BnNat, sig: S.EcSig) -> Bool:
  match sig:
    case S.EcSig{+r, +s}:
      +n = E.EcCurve.n(c)
      Bool.and(Bool.and(sm2.in_range(r, n), sm2.in_range(s, n)), sm2.verify.go(c, pk, e, r, s))

# The signature of M by the signer with identity ID_A and private key d
# (public key d G), with the per-message secret k (Sm2IdTooLong for an ID
# of 8192 bytes or more)
def Sm2.sign(~digest: B.Octets -> B.Octets, +c: E.EcCurve, +d: N.BnNat, +id: B.Octets, m: B.Octets, +k: N.BnNat) -> Result<&2, &2, Sm2Error, S.EcSig>:
  Result.bind(&2, &2, Sm2Error, Unit, S.EcSig, Sm2Error.check(Sm2.id_ok(id), Sm2IdTooLong{}), u => Sm2.sign_e(c, d, Sm2.e(~digest, c, id, Sm2.public(c, d), m), k))

# The same with a deterministic k: RFC 6979's construction over the HMAC
# ~mac, from d and e's bytes
def Sm2.sign_det(~digest: B.Octets -> B.Octets, ~mac: B.Octets -> B.Octets -> B.Octets, +c: E.EcCurve, +d: N.BnNat, +id: B.Octets, m: B.Octets) -> Result<&2, &2, Sm2Error, S.EcSig>:
  +e = Sm2.e(~digest, c, id, Sm2.public(c, d), m)
  +n = E.EcCurve.n(c)
  +eo = Maybe.default(&2, B.Octets, N.BnNat.to_octets(e, E.EcCurve.order_len(c)), B.Octets.empty())
  Result.bind(&2, &2, Sm2Error, Unit, S.EcSig, Sm2Error.check(Sm2.id_ok(id), Sm2IdTooLong{}), u => Sm2.sign_e(c, d, e, R.EcRfc6979.k(~mac, n, d, eo)))

# whether sig is a valid signature of M by the signer with identity ID_A and
# public key P_A
def Sm2.verify(~digest: B.Octets -> B.Octets, +c: E.EcCurve, +pk: E.EcPoint, +id: B.Octets, m: B.Octets, sig: S.EcSig) -> Bool:
  Bool.and(Sm2.id_ok(id), Sm2.verify_e(c, pk, Sm2.e(~digest, c, id, pk, m), sig))
