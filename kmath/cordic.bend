# bend-osdev-kmath, CORDIC sine and cosine in fixed point (Volder, "The
# CORDIC Trigonometric Computing Technique", IRE Trans. Electronic Computers,
# 1959; Walther, "A unified algorithm for elementary functions", 1971).
#
# An angle is a binary angle: a U32 where 2^32 is the full turn (2^30 is
# 90 degrees), so angles wrap as U32 arithmetic does. The results are signed
# Q1.30 fixed point in U32 (two's complement, 2^30 = 1.0). Angles in the
# second and third quadrants are turned by 180 degrees first (and the results
# negated), leaving |angle| <= 90 degrees, inside CORDIC's range of
# convergence (about 99.9 degrees). Then 30 rotations by +-atan(2^-i), from
# the gain-compensated start (K, 0).
#
# Error bound (documented and tested, not proved): |cos - cos(angle) * 2^30|
# and |sin - sin(angle) * 2^30| are at most 64, that is 2^-24. The 30 steps
# leave an angle residual below atan(2^-29), and each step truncates its two
# shifts; ref/run.sh checks 4,000 angles against Python's math.cos and
# math.sin, and an exact model of these steps gives at most 18.3 over
# 200,000 random angles.
import Base
import ../word64/word64.bend as W
import ./cordic_table.bend as CT

type KCordic is Data:
  KCordic{cos: U32, sin: U32}

# v >> i keeping the sign
def kcordic.sra(+v: U32, i: Nat) -> U32:
  +s = U32.sub(0, U32.shrn(v, 31n))
  U32.xor(U32.shrn(U32.xor(v, s), i), s)

# -v if s is all ones, v if s is 0
def kcordic.cneg(+v: U32, +s: U32) -> U32:
  U32.sub(U32.xor(v, s), s)

def kcordic.go(ts: List<&2, U32>, +i: Nat, +x: U32, +y: U32, +z: U32) -> KCordic:
  match ts:
    case Nil{}:
      KCordic{x, y}
    case Con{a, rest}:
      +s = U32.sub(0, U32.shrn(z, 31n))
      kcordic.go(rest, 1n+i, U32.sub(x, kcordic.cneg(kcordic.sra(y, i), s)), U32.add(y, kcordic.cneg(kcordic.sra(x, i), s)), U32.sub(z, kcordic.cneg(a, s)))

def kcordic.turn(r: KCordic, +s: U32) -> KCordic:
  match r:
    case KCordic{c, n}:
      KCordic{kcordic.cneg(c, s), kcordic.cneg(n, s)}

# cos and sin of a binary angle, in Q1.30; quadrants II and III (top bits
# 01 and 10) are turned by 180 degrees
def KMath.cordic(+angle: U32) -> KCordic:
  +q = U32.shrn(angle, 30n)
  +s = U32.sub(0, U32.and(U32.xor(q, U32.shr(q)), 1))
  kcordic.turn(kcordic.go(CT.KCordic.atans(), 0n, CT.KCordic.gain(), 0, U32.add(angle, U32.and(s, 2147483648))), s)

def KCordic.cos(r: KCordic) -> U32:
  match r:
    case KCordic{c, n}:
      c

def KCordic.sin(r: KCordic) -> U32:
  match r:
    case KCordic{c, n}:
      n

# the binary angle of a signed number of degrees: deg * 2^32 / 360, rounded
# to nearest (and wrapping, as angles do)
def KMath.angle_of_degrees(+deg: U32) -> U32:
  +s = U32.sub(0, U32.shrn(deg, 31n))
  +mag = W.W64.from_parts(kcordic.cneg(deg, s), 180)
  kcordic.cneg(W.W64.lo(W.W64.div(mag, W.W64.from_u32(360))), s)
