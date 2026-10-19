# ECDSA (FIPS 186-5, "Digital Signature Standard (DSS)", 2023, section 6.4:
# 6.4.1 signature generation, 6.4.2 verification), over any curve of this
# package and any hash (~digest, one-shot):
#   e = the leftmost min(len(n), hashlen) bits of H = Hash(M),
#   sign: R = k G, r = x_R mod n, s = k^-1 (e + r d) mod n,
#   verify: r, s in [1, n - 1], u = e s^-1, v = r s^-1 mod n,
#           R1 = u G + v Q not the point at infinity, x_R1 mod n = r.
# The per-message secret k is a parameter (a random k from the caller, as
# FIPS 186-5 6.3.1 asks), or RFC 6979's deterministic k (rfc6979.bend)
# through sign_det. A signature travels as r || s, each n's length
# (the IEEE P1363 form); DER (an ASN.1 SEQUENCE of two INTEGERs) is an
# extension point.
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../bignum/modular.bend as Md
import ./ecc.bend as E
import ./rfc6979.bend as R

# A signature (open)
type EcSig is Data:
  EcSig{r: N.BnNat, s: N.BnNat}

# e from a hash value (section 6.4.1, step 2): its leftmost len(n) bits when
# it is longer
def EcDsa.hash_int(+c: E.EcCurve, +h: B.Octets) -> N.BnNat:
  N.BnNat.shr(N.BnNat.of_octets(h), Nat.sub(Nat.mul(8n, B.Octets.len(h)), N.BnNat.bit_len(E.EcCurve.n(c))))

def ecdsa.in_range(+x: N.BnNat, +n: N.BnNat) -> Bool:
  Bool.and(Bool.not(N.BnNat.is_zero(x)), N.BnNat.is_lt(x, n))

def ecdsa.sig(+r: N.BnNat, +s: N.BnNat) -> Result<&2, &2, E.EcError, EcSig>:
  Result.map(&2, &2, E.EcError, Unit, EcSig, u => EcSig{r, s}, E.EcError.check(Bool.and(Bool.not(N.BnNat.is_zero(r)), Bool.not(N.BnNat.is_zero(s))), E.EcBadNonce{}))

def ecdsa.sign.go(+c: E.EcCurve, d: N.BnNat, +e: N.BnNat, +k: N.BnNat) -> Result<&2, &2, E.EcError, EcSig>:
  +n = E.EcCurve.n(c)
  +r = N.BnNat.mod(E.EcPoint.x(E.EcCurve.base_mul(c, k)), n)
  +kinv = Maybe.default(&2, N.BnNat, Md.BnMod.inv(k, n), N.BnNat.zero())
  ecdsa.sig(r, Md.BnMod.mul(kinv, Md.BnMod.add(e, Md.BnMod.mul(r, d, n), n), n))

# The signature of the hash value h under the private key d with the
# per-message secret k (section 6.4.1, steps 2 to 12): EcBadNonce for a k
# outside [1, n - 1], or when r or s is 0 (the caller takes another k)
def EcDsa.sign_hash(+c: E.EcCurve, d: N.BnNat, +h: B.Octets, +k: N.BnNat) -> Result<&2, &2, E.EcError, EcSig>:
  Result.bind(&2, &2, E.EcError, Unit, EcSig, E.EcError.check(ecdsa.in_range(k, E.EcCurve.n(c)), E.EcBadNonce{}), u => ecdsa.sign.go(c, d, EcDsa.hash_int(c, h), k))

def ecdsa.verify.go(+c: E.EcCurve, q: E.EcPoint, +e: N.BnNat, +r: N.BnNat, s: N.BnNat) -> Bool:
  +n = E.EcCurve.n(c)
  +w = Maybe.default(&2, N.BnNat, Md.BnMod.inv(s, n), N.BnNat.zero())
  +p = E.EcCurve.mul2(c, Md.BnMod.mul(e, w, n), E.EcCurve.generator(c), Md.BnMod.mul(r, w, n), q)
  Bool.and(Bool.not(E.EcPoint.is_inf(p)), N.BnNat.is_eq(N.BnNat.mod(E.EcPoint.x(p), n), r))

# Whether sig is a valid signature of the hash value h under the public key
# Q (section 6.4.2)
def EcDsa.verify_hash(+c: E.EcCurve, q: E.EcPoint, +h: B.Octets, sig: EcSig) -> Bool:
  match sig:
    case EcSig{+r, +s}:
      +n = E.EcCurve.n(c)
      Bool.and(Bool.and(ecdsa.in_range(r, n), ecdsa.in_range(s, n)), ecdsa.verify.go(c, q, EcDsa.hash_int(c, h), r, s))

# the signature of M with the per-message secret k
def EcDsa.sign(~digest: B.Octets -> B.Octets, +c: E.EcCurve, d: N.BnNat, m: B.Octets, +k: N.BnNat) -> Result<&2, &2, E.EcError, EcSig>:
  EcDsa.sign_hash(c, d, digest(m), k)

# deterministic ECDSA: the signature of M with RFC 6979's k, over the HMAC
# ~mac of the same hash
def EcDsa.sign_det(~digest: B.Octets -> B.Octets, ~mac: B.Octets -> B.Octets -> B.Octets, +c: E.EcCurve, +d: N.BnNat, m: B.Octets) -> Result<&2, &2, E.EcError, EcSig>:
  +h = digest(m)
  EcDsa.sign_hash(c, d, h, R.EcRfc6979.k(~mac, E.EcCurve.n(c), d, h))

# whether sig is a valid signature of M under Q
def EcDsa.verify(~digest: B.Octets -> B.Octets, +c: E.EcCurve, q: E.EcPoint, m: B.Octets, sig: EcSig) -> Bool:
  EcDsa.verify_hash(c, q, digest(m), sig)

def ecdsa.int(+x: N.BnNat, +l: Nat) -> B.Octets:
  Maybe.default(&2, B.Octets, N.BnNat.to_octets(x, l), B.Octets.zeros(l))

# A signature's bytes: r || s, each n's length
def EcDsa.sig_to(+c: E.EcCurve, sig: EcSig) -> B.Octets:
  match sig:
    case EcSig{r, s}:
      +l = E.EcCurve.order_len(c)
      B.Octets.append(ecdsa.int(r, l), ecdsa.int(s, l))

def ecdsa.sig_of.go(ok: Bool, +l: Nat, +o: B.Octets) -> Maybe<&2, EcSig>:
  match ok:
    case True{}:
      Some{EcSig{N.BnNat.of_octets(B.Octets.take(l, o)), N.BnNat.of_octets(B.Octets.drop(l, o))}}
    case False{}:
      None{}

# A signature from r || s (None for another length than twice n's)
def EcDsa.sig_of(+c: E.EcCurve, +o: B.Octets) -> Maybe<&2, EcSig>:
  +l = E.EcCurve.order_len(c)
  ecdsa.sig_of.go(Nat.is_eq(B.Octets.len(o), Nat.mul(2n, l)), l, o)

def ecdsa.verify_bytes.go(~digest: B.Octets -> B.Octets, +c: E.EcCurve, q: E.EcPoint, m: B.Octets, s: Maybe<&2, EcSig>) -> Bool:
  match s:
    case None{}:
      False{}
    case Some{sig}:
      EcDsa.verify(~digest, c, q, m, sig)

# whether the bytes r || s are a valid signature of M under Q
def EcDsa.verify_bytes(~digest: B.Octets -> B.Octets, +c: E.EcCurve, q: E.EcPoint, m: B.Octets, +s: B.Octets) -> Bool:
  ecdsa.verify_bytes.go(~digest, c, q, m, EcDsa.sig_of(c, s))
