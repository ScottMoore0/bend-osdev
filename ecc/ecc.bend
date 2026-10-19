# bend-osdev-ecc: elliptic curves y^2 = x^3 + a x + b over a prime field
# GF(p), generic over the curve's domain parameters (p, a, b, G, n, h).
#
# Points are affine (EcPoint: the point at infinity, or (x, y) as ordinary
# integers below p) at the interface. Inside, a point is in Jacobian
# coordinates (x = X / Z^2, y = Y / Z^3; Z = 0 for the point at infinity)
# with every coordinate in Montgomery form (bignum's mont.bend), and points
# are doubled and added by the Explicit-Formulas Database's dbl-2007-bl and
# add-2007-bl (D. J. Bernstein, T. Lange, "Jacobian coordinates for short
# Weierstrass curves", hyperelliptic.org/EFD/g1p/auto-shortw-jacobian.html),
# with the cases those formulas exclude (an input at infinity, P + P,
# P + (-P)) taken first. Scalars multiply by double-and-add over the
# scalar's bits, most significant first; u P + v Q by Shamir's trick (the
# two scalars' bits together, with P + Q precomputed).
#
# Public-key validation is NIST SP 800-56A Rev. 3's (section 5.6.2.3.3 full,
# 5.6.2.3.4 partial). Points travel in SEC 1's uncompressed form (0x04, X,
# Y, each coordinate the field's length; README.md cites it). The named
# curves are in curves.bend; ECDH in ecdh.bend; ECDSA in ecdsa.bend.
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../bignum/mont.bend as Mt

# Every failure
type EcError is Data:
  EcBadPoint{}
  EcInfinity{}
  EcBadEncoding{}
  EcBadPrivateKey{}
  EcBadNonce{}

# A curve's domain parameters (open): the field's prime p, the coefficients
# a and b (below p), the base point G = (gx, gy), its prime order n, and the
# cofactor h
type EcParams is Data:
  EcParams{p: N.BnNat, a: N.BnNat, b: N.BnNat, gx: N.BnNat, gy: N.BnNat, n: N.BnNat, h: N.BnNat}

# A point (open): the point at infinity, or affine coordinates below p
type EcPoint is Data:
  EcInf{}
  EcAff{x: N.BnNat, y: N.BnNat}

# A curve ready for arithmetic (opaque): its parameters, the Montgomery
# context of p, a and b in Montgomery form, and the byte lengths of p and n
type EcCurve is Data:
  EcCurve{prm: EcParams, fp: Mt.BnMont, am: N.BnNat, bm: N.BnNat, flen: Nat, nlen: Nat}

# A point in Jacobian coordinates, in Montgomery form (internal)
type EcJac is Data:
  EcJac{x: N.BnNat, y: N.BnNat, z: N.BnNat}

def EcError.check(ok: Bool, e: EcError) -> Result<&2, &2, EcError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

# ---------------------------------------------------------------- the curve

# The curve of the parameters p, a, b, G, n, h. p and n must be odd primes
# (as every named curve's are; EcCurve.check tests a curve's parameters)
def EcCurve.of(+prm: EcParams) -> EcCurve:
  match prm:
    case EcParams{+p, a, b, gx, gy, +n, h}:
      +fp = Mt.BnMont.of_odd(p)
      EcCurve{prm, fp, Mt.BnMont.to(fp, a), Mt.BnMont.to(fp, b), N.BnNat.byte_len(p), N.BnNat.byte_len(n)}

def EcCurve.params(c: EcCurve) -> EcParams:
  match c:
    case EcCurve{prm, fp, am, bm, flen, nlen}:
      prm

def EcParams.p(prm: EcParams) -> N.BnNat:
  match prm:
    case EcParams{p, a, b, gx, gy, n, h}:
      p

def EcParams.n(prm: EcParams) -> N.BnNat:
  match prm:
    case EcParams{p, a, b, gx, gy, n, h}:
      n

def EcParams.h(prm: EcParams) -> N.BnNat:
  match prm:
    case EcParams{p, a, b, gx, gy, n, h}:
      h

def EcParams.a(prm: EcParams) -> N.BnNat:
  match prm:
    case EcParams{p, a, b, gx, gy, n, h}:
      a

def EcParams.b(prm: EcParams) -> N.BnNat:
  match prm:
    case EcParams{p, a, b, gx, gy, n, h}:
      b

# the field's prime p
def EcCurve.p(c: EcCurve) -> N.BnNat:
  EcParams.p(EcCurve.params(c))

# the base point's order n
def EcCurve.n(c: EcCurve) -> N.BnNat:
  EcParams.n(EcCurve.params(c))

# the cofactor h
def EcCurve.h(c: EcCurve) -> N.BnNat:
  EcParams.h(EcCurve.params(c))

# the base point G
def EcCurve.generator(c: EcCurve) -> EcPoint:
  match c:
    case EcCurve{EcParams{p, a, b, gx, gy, n, h}, fp, am, bm, flen, nlen}:
      EcAff{gx, gy}

# the length of p in bytes (of a coordinate)
def EcCurve.field_len(c: EcCurve) -> Nat:
  match c:
    case EcCurve{prm, fp, am, bm, flen, nlen}:
      flen

# the length of n in bytes (of a scalar)
def EcCurve.order_len(c: EcCurve) -> Nat:
  match c:
    case EcCurve{prm, fp, am, bm, flen, nlen}:
      nlen

def EcCurve.field(c: EcCurve) -> Mt.BnMont:
  match c:
    case EcCurve{prm, fp, am, bm, flen, nlen}:
      fp

def EcCurve.am(c: EcCurve) -> N.BnNat:
  match c:
    case EcCurve{prm, fp, am, bm, flen, nlen}:
      am

def EcCurve.bm(c: EcCurve) -> N.BnNat:
  match c:
    case EcCurve{prm, fp, am, bm, flen, nlen}:
      bm

# ---------------------------------------------------------------- field

def ec.fm(+f: Mt.BnMont, a: N.BnNat, b: N.BnNat) -> N.BnNat:
  Mt.BnMont.mul(f, a, b)

def ec.fq(+f: Mt.BnMont, a: N.BnNat) -> N.BnNat:
  Mt.BnMont.sqr(f, a)

def ec.fa(+f: Mt.BnMont, a: N.BnNat, b: N.BnNat) -> N.BnNat:
  Mt.BnMont.add(f, a, b)

def ec.fs(+f: Mt.BnMont, a: N.BnNat, b: N.BnNat) -> N.BnNat:
  Mt.BnMont.sub(f, a, b)

def ec.f2(+f: Mt.BnMont, +a: N.BnNat) -> N.BnNat:
  Mt.BnMont.add(f, a, a)

# ---------------------------------------------------------------- Jacobian

def ec.inf(+f: Mt.BnMont) -> EcJac:
  EcJac{Mt.BnMont.one(f), Mt.BnMont.one(f), N.BnNat.zero()}

# dbl-2007-bl: XX = X1^2, YY = Y1^2, YYYY = YY^2, ZZ = Z1^2,
# S = 2((X1 + YY)^2 - XX - YYYY), M = 3 XX + a ZZ^2, T = M^2 - 2 S,
# X3 = T, Y3 = M (S - T) - 8 YYYY, Z3 = (Y1 + Z1)^2 - YY - ZZ
# (a point at infinity, Z1 = 0, gives Z3 = 0 again)
def ec.dbl(+f: Mt.BnMont, +am: N.BnNat, j: EcJac) -> EcJac:
  match j:
    case EcJac{+x1, +y1, +z1}:
      +xx = ec.fq(f, x1)
      +yy = ec.fq(f, y1)
      +yyyy = ec.fq(f, yy)
      +zz = ec.fq(f, z1)
      +s = ec.f2(f, ec.fs(f, ec.fs(f, ec.fq(f, ec.fa(f, x1, yy)), xx), yyyy))
      +m = ec.fa(f, ec.fa(f, ec.f2(f, xx), xx), ec.fm(f, am, ec.fq(f, zz)))
      +t = ec.fs(f, ec.fq(f, m), ec.f2(f, s))
      EcJac{t, ec.fs(f, ec.fm(f, m, ec.fs(f, s, t)), ec.f2(f, ec.f2(f, ec.f2(f, yyyy)))), ec.fs(f, ec.fs(f, ec.fq(f, ec.fa(f, y1, z1)), yy), zz)}

# add-2007-bl, for P1 != +-P2 (H != 0): I = (2 H)^2, J = H I, r = 2 (S2 - S1),
# V = U1 I, X3 = r^2 - J - 2 V, Y3 = r (V - X3) - 2 S1 J,
# Z3 = ((Z1 + Z2)^2 - Z1Z1 - Z2Z2) H
def ec.add.gen(+f: Mt.BnMont, +u1: N.BnNat, +s1: N.BnNat, +h: N.BnNat, +rr: N.BnNat, z1: N.BnNat, z2: N.BnNat, z1z1: N.BnNat, z2z2: N.BnNat) -> EcJac:
  +i = ec.fq(f, ec.f2(f, h))
  +j = ec.fm(f, h, i)
  +r = ec.f2(f, rr)
  +v = ec.fm(f, u1, i)
  +x3 = ec.fs(f, ec.fs(f, ec.fq(f, r), j), ec.f2(f, v))
  EcJac{x3, ec.fs(f, ec.fm(f, r, ec.fs(f, v, x3)), ec.f2(f, ec.fm(f, s1, j))), ec.fm(f, ec.fs(f, ec.fs(f, ec.fq(f, ec.fa(f, z1, z2)), z1z1), z2z2), h)}

# H = U2 - U1 and S2 - S1 zero or not: P1 = P2 (double), P1 = -P2 (the
# point at infinity), or the general case
def ec.add.h(hz: Bool, rz: Bool, +f: Mt.BnMont, +am: N.BnNat, +p1: EcJac, +u1: N.BnNat, +s1: N.BnNat, +h: N.BnNat, +rr: N.BnNat, z1: N.BnNat, z2: N.BnNat, z1z1: N.BnNat, z2z2: N.BnNat) -> EcJac:
  match hz rz:
    case True{} True{}:
      ec.dbl(f, am, p1)
    case True{} False{}:
      ec.inf(f)
    case False{} _:
      ec.add.gen(f, u1, s1, h, rr, z1, z2, z1z1, z2z2)

# Z1Z1 = Z1^2, Z2Z2 = Z2^2, U1 = X1 Z2Z2, U2 = X2 Z1Z1, S1 = Y1 Z2 Z2Z2,
# S2 = Y2 Z1 Z1Z1
def ec.add.both(+f: Mt.BnMont, +am: N.BnNat, +x1: N.BnNat, +y1: N.BnNat, +z1: N.BnNat, x2: N.BnNat, y2: N.BnNat, +z2: N.BnNat) -> EcJac:
  +z1z1 = ec.fq(f, z1)
  +z2z2 = ec.fq(f, z2)
  +u1 = ec.fm(f, x1, z2z2)
  +s1 = ec.fm(f, ec.fm(f, y1, z2), z2z2)
  +h = ec.fs(f, ec.fm(f, x2, z1z1), u1)
  +rr = ec.fs(f, ec.fm(f, ec.fm(f, y2, z1), z1z1), s1)
  ec.add.h(N.BnNat.is_zero(h), N.BnNat.is_zero(rr), f, am, EcJac{x1, y1, z1}, u1, s1, h, rr, z1, z2, z1z1, z2z2)

def ec.add.pts(+f: Mt.BnMont, +am: N.BnNat, p1: EcJac, p2: EcJac) -> EcJac:
  match p1 p2:
    case EcJac{x1, y1, z1} EcJac{x2, y2, z2}:
      ec.add.both(f, am, x1, y1, z1, x2, y2, z2)

def ec.add.z(z1: Bool, z2: Bool, +f: Mt.BnMont, +am: N.BnNat, p1: EcJac, p2: EcJac) -> EcJac:
  match z1 z2:
    case True{} _:
      p2
    case False{} True{}:
      p1
    case False{} False{}:
      ec.add.pts(f, am, p1, p2)

def EcJac.z(j: EcJac) -> N.BnNat:
  match j:
    case EcJac{x, y, z}:
      z

# P1 + P2
def ec.add(+f: Mt.BnMont, +am: N.BnNat, +p1: EcJac, +p2: EcJac) -> EcJac:
  ec.add.z(N.BnNat.is_zero(EcJac.z(p1)), N.BnNat.is_zero(EcJac.z(p2)), f, am, p1, p2)

def ec.to_jac(+f: Mt.BnMont, p: EcPoint) -> EcJac:
  match p:
    case EcInf{}:
      ec.inf(f)
    case EcAff{x, y}:
      EcJac{Mt.BnMont.to(f, x), Mt.BnMont.to(f, y), Mt.BnMont.one(f)}

def ec.to_aff.fin(+f: Mt.BnMont, +p: N.BnNat, j: EcJac) -> EcPoint:
  match j:
    case EcJac{x, y, z}:
      +zi = Mt.BnMont.exp(f, z, N.BnNat.sub(p, N.BnNat.of_u32(2)))
      +zi2 = ec.fq(f, zi)
      EcAff{Mt.BnMont.of(f, ec.fm(f, x, zi2)), Mt.BnMont.of(f, ec.fm(f, y, ec.fm(f, zi2, zi)))}

def ec.to_aff.go(inf: Bool, +f: Mt.BnMont, +p: N.BnNat, j: EcJac) -> EcPoint:
  match inf:
    case True{}:
      EcInf{}
    case False{}:
      ec.to_aff.fin(f, p, j)

# x = X / Z^2, y = Y / Z^3, with 1 / Z = Z^(p - 2) (Fermat)
def ec.to_aff(+f: Mt.BnMont, +p: N.BnNat, +j: EcJac) -> EcPoint:
  ec.to_aff.go(N.BnNat.is_zero(EcJac.z(j)), f, p, j)

def ec.pick(set: Bool, +f: Mt.BnMont, +am: N.BnNat, +acc: EcJac, +q: EcJac) -> EcJac:
  match set:
    case True{}:
      ec.add(f, am, acc, q)
    case False{}:
      acc

# k P from bit i - 1 of k down: double, and add P where the bit is set
def ec.mul.go(+i: Nat, +f: Mt.BnMont, +am: N.BnNat, +k: N.BnNat, +pj: EcJac, acc: EcJac) -> EcJac:
  match i:
    case 0n:
      acc
    case 1n+b:
      ec.mul.go(b, f, am, k, pj, ec.pick(N.BnNat.bit(k, b), f, am, ec.dbl(f, am, acc), pj))

def ec.pick2(bu: Bool, bv: Bool, +f: Mt.BnMont, +am: N.BnNat, +acc: EcJac, +pj: EcJac, +qj: EcJac, +pq: EcJac) -> EcJac:
  match bu bv:
    case True{} True{}:
      ec.add(f, am, acc, pq)
    case True{} False{}:
      ec.add(f, am, acc, pj)
    case False{} True{}:
      ec.add(f, am, acc, qj)
    case False{} False{}:
      acc

# u P + v Q from bit i - 1 down (Shamir's trick)
def ec.mul2.go(+i: Nat, +f: Mt.BnMont, +am: N.BnNat, +u: N.BnNat, +v: N.BnNat, +pj: EcJac, +qj: EcJac, +pq: EcJac, acc: EcJac) -> EcJac:
  match i:
    case 0n:
      acc
    case 1n+b:
      ec.mul2.go(b, f, am, u, v, pj, qj, pq, ec.pick2(N.BnNat.bit(u, b), N.BnNat.bit(v, b), f, am, ec.dbl(f, am, acc), pj, qj, pq))

def ec.mul.jac(+c: EcCurve, +k: N.BnNat, p: EcPoint) -> EcJac:
  +f = EcCurve.field(c)
  ec.mul.go(N.BnNat.bit_len(k), f, EcCurve.am(c), k, ec.to_jac(f, p), ec.inf(f))

# ---------------------------------------------------------------- points

# P + Q
def EcCurve.add(+c: EcCurve, p: EcPoint, q: EcPoint) -> EcPoint:
  +f = EcCurve.field(c)
  ec.to_aff(f, EcCurve.p(c), ec.add(f, EcCurve.am(c), ec.to_jac(f, p), ec.to_jac(f, q)))

# 2 P
def EcCurve.dbl(+c: EcCurve, p: EcPoint) -> EcPoint:
  +f = EcCurve.field(c)
  ec.to_aff(f, EcCurve.p(c), ec.dbl(f, EcCurve.am(c), ec.to_jac(f, p)))

# -P
def EcCurve.neg(+c: EcCurve, p: EcPoint) -> EcPoint:
  match p:
    case EcInf{}:
      EcInf{}
    case EcAff{x, +y}:
      EcAff{x, N.BnNat.mod(N.BnNat.sub(EcCurve.p(c), y), EcCurve.p(c))}

# k P, for any k (0 P and n P are the point at infinity)
def EcCurve.mul(+c: EcCurve, +k: N.BnNat, p: EcPoint) -> EcPoint:
  ec.to_aff(EcCurve.field(c), EcCurve.p(c), ec.mul.jac(c, k, p))

# k G
def EcCurve.base_mul(+c: EcCurve, +k: N.BnNat) -> EcPoint:
  EcCurve.mul(c, k, EcCurve.generator(c))

# u P + v Q
def EcCurve.mul2(+c: EcCurve, +u: N.BnNat, p: EcPoint, +v: N.BnNat, q: EcPoint) -> EcPoint:
  +f = EcCurve.field(c)
  +am = EcCurve.am(c)
  +pj = ec.to_jac(f, p)
  +qj = ec.to_jac(f, q)
  +bits = Nat.max(N.BnNat.bit_len(u), N.BnNat.bit_len(v))
  ec.to_aff(f, EcCurve.p(c), ec.mul2.go(bits, f, am, u, v, pj, qj, ec.add(f, am, pj, qj), ec.inf(f)))

def EcPoint.is_inf(p: EcPoint) -> Bool:
  match p:
    case EcInf{}:
      True{}
    case EcAff{x, y}:
      False{}

# equality by value
def EcPoint.is_eq(p: EcPoint, q: EcPoint) -> Bool:
  match p q:
    case EcInf{} EcInf{}:
      True{}
    case EcAff{x1, y1} EcAff{x2, y2}:
      Bool.and(N.BnNat.is_eq(x1, x2), N.BnNat.is_eq(y1, y2))
    case _ _:
      False{}

# the x coordinate (0 for the point at infinity)
def EcPoint.x(p: EcPoint) -> N.BnNat:
  match p:
    case EcInf{}:
      N.BnNat.zero()
    case EcAff{x, y}:
      x

def EcPoint.y(p: EcPoint) -> N.BnNat:
  match p:
    case EcInf{}:
      N.BnNat.zero()
    case EcAff{x, y}:
      y

def ec.on.aff(+c: EcCurve, +x: N.BnNat, +y: N.BnNat) -> Bool:
  +f = EcCurve.field(c)
  +p = EcCurve.p(c)
  +xm = Mt.BnMont.to(f, x)
  +rhs = ec.fa(f, ec.fa(f, ec.fm(f, ec.fq(f, xm), xm), ec.fm(f, EcCurve.am(c), xm)), EcCurve.bm(c))
  Bool.and(Bool.and(N.BnNat.is_lt(x, p), N.BnNat.is_lt(y, p)), N.BnNat.is_eq(ec.fq(f, Mt.BnMont.to(f, y)), rhs))

# whether P is a finite point of the curve: coordinates in [0, p - 1] and
# y^2 = x^3 + a x + b mod p (SP 800-56A, 5.6.2.3.4 steps 1 to 3: partial
# validation)
def EcCurve.on_curve(+c: EcCurve, p: EcPoint) -> Bool:
  match p:
    case EcInf{}:
      False{}
    case EcAff{x, y}:
      ec.on.aff(c, x, y)

# full validation (SP 800-56A, 5.6.2.3.3): on the curve, and n P is the
# point at infinity
def EcCurve.validate(+c: EcCurve, +p: EcPoint) -> Bool:
  Bool.and(EcCurve.on_curve(c, p), N.BnNat.is_zero(EcJac.z(ec.mul.jac(c, EcCurve.n(c), p))))

# Whether the parameters make a curve this package can use: p and n odd and
# above 3, a and b below p, 4 a^3 + 27 b^2 != 0 mod p, G on the curve and
# n G the point at infinity (the primality of p and n is not tested here:
# bignum's BnPrime does that)
def EcCurve.check(+c: EcCurve) -> Bool:
  +prm = EcCurve.params(c)
  +p = EcParams.p(prm)
  +n = EcParams.n(prm)
  +f = EcCurve.field(c)
  +am = EcCurve.am(c)
  +bm = EcCurve.bm(c)
  +three = N.BnNat.of_u32(3)
  +disc = ec.fa(f, ec.fm(f, Mt.BnMont.to(f, N.BnNat.of_u32(4)), ec.fm(f, ec.fq(f, am), am)), ec.fm(f, Mt.BnMont.to(f, N.BnNat.of_u32(27)), ec.fq(f, bm)))
  +odd = Bool.and(Bool.and(N.BnNat.is_odd(p), N.BnNat.is_lt(three, p)), Bool.and(N.BnNat.is_odd(n), N.BnNat.is_lt(three, n)))
  +small = Bool.and(N.BnNat.is_lt(EcParams.a(prm), p), N.BnNat.is_lt(EcParams.b(prm), p))
  Bool.and(Bool.and(odd, small), Bool.and(Bool.not(N.BnNat.is_zero(disc)), EcCurve.validate(c, EcCurve.generator(c))))

# ---------------------------------------------------------------- bytes

def ec.coord(+x: N.BnNat, +len: Nat) -> B.Octets:
  Maybe.default(&2, B.Octets, N.BnNat.to_octets(x, len), B.Octets.zeros(len))

# A point's bytes, SEC 1's uncompressed form: 0x04, then x and y, each the
# field's length (the point at infinity is the single byte 0x00)
def EcCurve.point_to(+c: EcCurve, p: EcPoint) -> B.Octets:
  match p:
    case EcInf{}:
      B.Octets.of_list([0])
    case EcAff{x, y}:
      +l = EcCurve.field_len(c)
      B.Octets.append(B.Octets.of_list([4]), B.Octets.append(ec.coord(x, l), ec.coord(y, l)))

def ec.pt.go(form: Bool, oncurve: Bool, +x: N.BnNat, +y: N.BnNat) -> Result<&2, &2, EcError, EcPoint>:
  match form oncurve:
    case False{} _:
      Fail{EcBadEncoding{}}
    case True{} False{}:
      Fail{EcBadPoint{}}
    case True{} True{}:
      Done{EcAff{x, y}}

# A point from SEC 1's uncompressed form: EcBadEncoding for another length
# or first byte, EcBadPoint for coordinates not below p or not on the curve
# (partial validation; EcCurve.validate validates in full)
def EcCurve.point_of(+c: EcCurve, +o: B.Octets) -> Result<&2, &2, EcError, EcPoint>:
  +l = EcCurve.field_len(c)
  +r = B.Octets.drop(1n, o)
  +xs = B.Octets.take(l, r)
  +ys = B.Octets.drop(l, r)
  +x = N.BnNat.of_octets(xs)
  +y = N.BnNat.of_octets(ys)
  ec.pt.go(Bool.and(B.Octets.is_eq(B.Octets.take(1n, o), B.Octets.of_list([4])), Bool.and(Nat.is_eq(B.Octets.len(xs), l), Nat.is_eq(B.Octets.len(ys), l))), ec.on.aff(c, x, y), x, y)
