# ECDH (NIST SP 800-56A Rev. 3): key pairs (section 5.6.1.2: a private key
# d in [1, n - 1], from extra random bits as in 5.6.1.2.1), and the ECC CDH
# primitive (section 5.7.1.2): P = h d Q, refused if P is the point at
# infinity, and Z = x_P as bytes of the field's length (Appendix C.2). Peer
# keys are validated in full (5.6.2.3.3) by EcDh.agree.
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ./ecc.bend as E

# whether d is a private key of the curve: 1 <= d <= n - 1
def EcDh.private_ok(+c: E.EcCurve, +d: N.BnNat) -> Bool:
  Bool.and(Bool.not(N.BnNat.is_zero(d)), N.BnNat.is_lt(d, E.EcCurve.n(c)))

# A private key from big-endian bytes (EcBadPrivateKey outside [1, n - 1])
def EcDh.private_of(+c: E.EcCurve, o: B.Octets) -> Result<&2, &2, E.EcError, N.BnNat>:
  +d = N.BnNat.of_octets(o)
  Result.map(&2, &2, E.EcError, Unit, N.BnNat, u => d, E.EcError.check(EcDh.private_ok(c, d), E.EcBadPrivateKey{}))

# A private key's bytes: big-endian, n's length
def EcDh.private_to(+c: E.EcCurve, d: N.BnNat) -> B.Octets:
  +l = E.EcCurve.order_len(c)
  Maybe.default(&2, B.Octets, N.BnNat.to_octets(d, l), B.Octets.zeros(l))

# Key-pair generation using extra random bits (SP 800-56A 5.6.1.2.1, and
# FIPS 186-5 Appendix A.2.1): from c, the integer of len(n) + 64 random bits
# (the caller's bytes), d = (c mod (n - 1)) + 1
def EcDh.private_from_bits(+c: E.EcCurve, bits: B.Octets) -> N.BnNat:
  N.BnNat.add(N.BnNat.mod(N.BnNat.of_octets(bits), N.BnNat.sub(E.EcCurve.n(c), N.BnNat.one())), N.BnNat.one())

# the public key d G
def EcDh.public(+c: E.EcCurve, +d: N.BnNat) -> E.EcPoint:
  E.EcCurve.base_mul(c, d)

def ecdh.z(+c: E.EcCurve, p: E.EcPoint) -> Result<&2, &2, E.EcError, B.Octets>:
  match p:
    case E.EcInf{}:
      Fail{E.EcInfinity{}}
    case E.EcAff{x, y}:
      +l = E.EcCurve.field_len(c)
      Done{Maybe.default(&2, B.Octets, N.BnNat.to_octets(x, l), B.Octets.zeros(l))}

# The ECC CDH primitive (section 5.7.1.2): Z, the x coordinate of h d Q
# (EcInfinity when that is the point at infinity)
def EcDh.primitive(+c: E.EcCurve, d: N.BnNat, q: E.EcPoint) -> Result<&2, &2, E.EcError, B.Octets>:
  ecdh.z(c, E.EcCurve.mul(c, N.BnNat.mul(E.EcCurve.h(c), d), q))

# The shared secret with a peer's public key, validated in full first
# (EcBadPoint), then the primitive
def EcDh.agree(+c: E.EcCurve, d: N.BnNat, +q: E.EcPoint) -> Result<&2, &2, E.EcError, B.Octets>:
  Result.bind(&2, &2, E.EcError, Unit, B.Octets, E.EcError.check(E.EcCurve.validate(c, q), E.EcBadPoint{}), u => EcDh.primitive(c, d, q))
