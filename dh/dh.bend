# bend-osdev-dh: finite-field Diffie-Hellman (NIST SP 800-56A Rev. 3,
# "Recommendation for Pair-Wise Key-Establishment Schemes Using Discrete
# Logarithm Cryptography", 2018): key pairs (section 5.6.1.1), public-key
# validation (5.6.2.3.1 full, 5.6.2.3.2 partial, and the Legendre-symbol
# form footnote 22 allows for safe-prime groups), and the FFC DH primitive
# (5.7.1.1). The named groups (RFC 7919's ffdhe and RFC 3526's MODP) are in
# groups.bend.
#
# A group is (p, q, g): every value is a BnNat. Public keys travel as
# big-endian bytes of p's length (SP 800-56A, Appendix C.1).
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../bignum/modular.bend as Md
import ../bignum/jacobi.bend as J

# Every failure
type DhError is Data:
  DhBadPrivateKey{}
  DhBadPublicKey{}
  DhBadSharedSecret{}
  DhBadLength{}

# A group (open): the prime p, the generator g, and q, the order of g's
# subgroup ((p - 1) / 2 for a safe prime)
type DhGroup is Data:
  DhGroup{p: N.BnNat, g: N.BnNat, q: N.BnNat}

def DhError.check(ok: Bool, e: DhError) -> Result<&2, &2, DhError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

def DhGroup.p(grp: DhGroup) -> N.BnNat:
  match grp:
    case DhGroup{p, g, q}:
      p

def DhGroup.q(grp: DhGroup) -> N.BnNat:
  match grp:
    case DhGroup{p, g, q}:
      q

# the length of p in bytes (of public keys and shared secrets)
def DhGroup.len(grp: DhGroup) -> Nat:
  N.BnNat.byte_len(DhGroup.p(grp))

# whether x is a private key of the group: 1 <= x <= q - 1 (section 5.6.1.1)
def Dh.private_ok(grp: DhGroup, +x: N.BnNat) -> Bool:
  Bool.and(Bool.not(N.BnNat.is_zero(x)), N.BnNat.is_lt(x, DhGroup.q(grp)))

# A private key from big-endian bytes (DhBadPrivateKey outside [1, q - 1])
def Dh.private_of(+grp: DhGroup, o: B.Octets) -> Result<&2, &2, DhError, N.BnNat>:
  +x = N.BnNat.of_octets(o)
  Result.map(&2, &2, DhError, Unit, N.BnNat, u => x, DhError.check(Dh.private_ok(grp, x), DhBadPrivateKey{}))

def dh.min(lt: Bool, a: N.BnNat, b: N.BnNat) -> N.BnNat:
  match lt:
    case True{}:
      a
    case False{}:
      b

# Key-pair generation using extra random bits (section 5.6.1.1.3, steps 4
# to 6): from c, the integer of N + 64 random bits (the caller's bytes),
# x = (c mod (M - 1)) + 1 with M = min(2^N, q)
def Dh.private_from_bits(grp: DhGroup, c: B.Octets, +nbits: Nat) -> N.BnNat:
  +q = DhGroup.q(grp)
  +m2 = N.BnNat.shl(N.BnNat.one(), nbits)
  +m = dh.min(N.BnNat.is_lt(m2, q), m2, q)
  N.BnNat.add(N.BnNat.mod(N.BnNat.of_octets(c), N.BnNat.sub(m, N.BnNat.one())), N.BnNat.one())

# the public key g^x mod p
def Dh.public(grp: DhGroup, x: N.BnNat) -> N.BnNat:
  match grp:
    case DhGroup{p, g, q}:
      Md.BnMod.exp(g, x, p)

# 2 <= y <= p - 2 (partial validation, section 5.6.2.3.2; RFC 7919 section
# 5.1's check)
def Dh.check_partial(grp: DhGroup, +y: N.BnNat) -> Bool:
  match grp:
    case DhGroup{+p, g, q}:
      Bool.and(N.BnNat.is_le(N.BnNat.of_u32(2), y), N.BnNat.is_le(y, N.BnNat.sub(p, N.BnNat.of_u32(2))))

# full validation (section 5.6.2.3.1): the range, and y^q mod p = 1
def Dh.check_full(+grp: DhGroup, +y: N.BnNat) -> Bool:
  match grp:
    case DhGroup{+p, g, +q}:
      Bool.and(Dh.check_partial(DhGroup{p, g, q}, y), N.BnNat.is_eq(Md.BnMod.exp(y, q, p), N.BnNat.one()))

def dh.plus(j: Maybe<&2, J.BnJacobi>) -> Bool:
  match j:
    case Some{J.BnJacPlus{}}:
      True{}
    case _:
      False{}

# full validation for a safe-prime group (q = (p - 1) / 2): the range, and
# y a quadratic residue modulo p, by the Legendre symbol (section 5.6.2.3.1,
# footnote 22: for a safe-prime group, y^q mod p = 1 exactly then)
def Dh.check_safe(+grp: DhGroup, +y: N.BnNat) -> Bool:
  match grp:
    case DhGroup{+p, g, q}:
      Bool.and(Dh.check_partial(DhGroup{p, g, q}, y), dh.plus(J.BnNat.jacobi(y, p)))

def dh.prim(+grp: DhGroup, +z: N.BnNat) -> Result<&2, &2, DhError, B.Octets>:
  +ok = Bool.and(N.BnNat.is_lt(N.BnNat.one(), z), Bool.not(N.BnNat.is_eq(z, N.BnNat.sub(DhGroup.p(grp), N.BnNat.one()))))
  Result.map(&2, &2, DhError, Unit, B.Octets, u => Maybe.default(&2, B.Octets, N.BnNat.to_octets(z, DhGroup.len(grp)), B.Octets.empty()), DhError.check(ok, DhBadSharedSecret{}))

# The FFC DH primitive (section 5.7.1.1): z = y^x mod p, refused when
# z <= 1 or z = p - 1 (DhBadSharedSecret); Z is z as bytes of p's length
def Dh.primitive(+grp: DhGroup, x: N.BnNat, y: N.BnNat) -> Result<&2, &2, DhError, B.Octets>:
  dh.prim(grp, Md.BnMod.exp(y, x, DhGroup.p(grp)))

# The shared secret with a peer's public key, validated in full first
# (DhBadPublicKey), then the primitive
def Dh.agree(+grp: DhGroup, x: N.BnNat, +y: N.BnNat) -> Result<&2, &2, DhError, B.Octets>:
  Result.bind(&2, &2, DhError, Unit, B.Octets, DhError.check(Dh.check_full(grp, y), DhBadPublicKey{}), u => Dh.primitive(grp, x, y))

# The same, validated by the Legendre symbol (for a safe-prime group only)
def Dh.agree_safe(+grp: DhGroup, x: N.BnNat, +y: N.BnNat) -> Result<&2, &2, DhError, B.Octets>:
  Result.bind(&2, &2, DhError, Unit, B.Octets, DhError.check(Dh.check_safe(grp, y), DhBadPublicKey{}), u => Dh.primitive(grp, x, y))

# A public key's bytes: big-endian, p's length (empty if y does not fit)
def Dh.public_to(grp: DhGroup, y: N.BnNat) -> B.Octets:
  Maybe.default(&2, B.Octets, N.BnNat.to_octets(y, DhGroup.len(grp)), B.Octets.empty())

def dh.pk.go(lenok: Bool, inrange: Bool, +o: B.Octets) -> Result<&2, &2, DhError, N.BnNat>:
  match lenok inrange:
    case False{} _:
      Fail{DhBadLength{}}
    case True{} False{}:
      Fail{DhBadPublicKey{}}
    case True{} True{}:
      Done{N.BnNat.of_octets(o)}

# A public key from its bytes: exactly p's length (DhBadLength), and in
# [2, p - 2] (DhBadPublicKey: partial validation; Dh.agree validates in
# full)
def Dh.public_of(+grp: DhGroup, +o: B.Octets) -> Result<&2, &2, DhError, N.BnNat>:
  dh.pk.go(Nat.is_eq(B.Octets.len(o), DhGroup.len(grp)), Dh.check_partial(grp, N.BnNat.of_octets(o)), o)
