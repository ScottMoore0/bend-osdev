import Base
import ../word64/word64.bend as W
import ./kmath.bend as K
import ./isqrt.bend as S
import ./div64.bend as D
import ./reciprocal.bend as R
import ./rational.bend as Q
import ./cordic.bend as C
import ./prime.bend as P

def u(x: U32) -> String:
  U32.show(x)

def n(x: Nat) -> String:
  Nat.show(x)

def b(x: Bool) -> String:
  Bool.show(x)

def rat(r: Q.KRational) -> String:
  match r:
    case Q.KRational{p, q}:
      U32.show(p) ++ "/" ++ U32.show(q)

def cs(r: C.KCordic) -> String:
  match r:
    case C.KCordic{c, s}:
      U32.show(c) ++ " " ++ U32.show(s)

def dv(r: D.KDiv64) -> String:
  match r:
    case D.KDiv64{q, r}:
      W.W64.show(q) ++ " " ++ U32.show(r)

def pr(p: W.W64 & W.W64) -> String:
  (q, r) = p
  W.W64.show(q) ++ " " ++ W.W64.show(r)

def rc.count(ok: Bool, bad: Nat) -> Nat:
  match ok:
    case True{}:
      bad
    case False{}:
      1n+bad

# reciprocal_divide against U32.div for every d from 1 to 2^16 and a few a
# per d, and for every a below 2^20 with a few d: the number of mismatches
def rc.d(fuel: Nat, +d: U32, bad: Nat) -> Nat:
  match fuel:
    case 0n:
      bad
    case 1n+k:
      +r = R.KRecip.of(d)
      +a1 = U32.mul(d, 2654435761)
      +a2 = U32.sub(0, d)
      +ok = Bool.and(U32.is_eq(R.KRecip.divide(a1, r), U32.div(a1, d)), Bool.and(U32.is_eq(R.KRecip.divide(a2, r), U32.div(a2, d)), U32.is_eq(R.KRecip.divide(4294967295, r), U32.div(4294967295, d))))
      rc.d(k, U32.add(d, 1), rc.count(ok, bad))

def rc.a(fuel: Nat, +a: U32, +r3: R.KRecip, +r7: R.KRecip, +rx: R.KRecip, bad: Nat) -> Nat:
  match fuel:
    case 0n:
      bad
    case 1n+k:
      +ok = Bool.and(U32.is_eq(R.KRecip.divide(a, r3), U32.div(a, 3)), Bool.and(U32.is_eq(R.KRecip.divide(a, r7), U32.div(a, 7)), U32.is_eq(R.KRecip.divide(a, rx), U32.div(a, 641))))
      rc.a(k, U32.add(a, 4093), r3, r7, rx, rc.count(ok, bad))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(n(K.KMath.gcd(1071n, 462n)))
    IO.print(n(K.KMath.lcm(4n, 6n)))
    IO.print(n(K.KMath.pow(3n, 13)))
    IO.print(u(K.KMath.pow32(3, 100)))
    IO.print(u(K.KMath.gcd32(4294967295, 65535)))
    IO.print(u(S.KMath.isqrt(4294967295)))
    IO.print(u(S.KMath.isqrt(1000000)))
    IO.print(u(S.KMath.isqrt64(W.W64.max())))
    IO.print(u(S.KMath.isqrt64(W.W64.from_parts(1, 0))))
    IO.print(dv(D.KMath.div_u64_rem(W.W64.max(), 10)))
    IO.print(pr(D.KMath.div64_u64_rem(W.W64.max(), W.W64.from_parts(1, 7))))
    IO.print(W.W64.show_hex(D.KMath.div64_s64(W.W64.sub(W.W64.zero(), W.W64.from_u32(7)), W.W64.from_u32(2))))
    IO.print(dv(D.KMath.div_s64_rem(W.W64.sub(W.W64.zero(), W.W64.from_u32(7)), 2)))
    IO.print(W.W64.show(D.KMath.div64_u64_round_up(W.W64.from_u32(7), W.W64.from_u32(2))))
    IO.print(u(R.KRecip.divide(4294967295, R.KRecip.of(3))))
    IO.print(n(rc.d(65536n, 1, 0n)))
    IO.print(n(rc.a(262144n, 0, R.KRecip.of(3), R.KRecip.of(7), R.KRecip.of(641), 0n)))
    IO.print(rat(Q.KMath.rational_best(314159265, 100000000, 1000, 1000)))
    IO.print(rat(Q.KMath.rational_best(1, 3, 10, 10)))
    IO.print(rat(Q.KMath.rational_best(1000, 1, 10, 10)))
    IO.print(cs(C.KMath.cordic(0)))
    IO.print(cs(C.KMath.cordic(1073741824)))
    IO.print(cs(C.KMath.cordic(C.KMath.angle_of_degrees(30))))
    IO.print(cs(C.KMath.cordic(C.KMath.angle_of_degrees(4294967146))))
    IO.print(b(P.KMath.is_prime(4294967291)))
    IO.print(b(P.KMath.is_prime(4294967295)))
    IO.print(u(P.KMath.next_prime(100)))
    IO.print(u(P.KMath.next_prime(4294967290)))
    IO.print(u(P.KMath.next_prime(4294967291)))

#|21
#|12
#|1594323
#|3476558801
#|65535
#|65535
#|1000
#|4294967295
#|65536
#|1844674407370955161 5
#|4294967289 48
#|fffffffffffffffd
#|18446744073709551613 4294967295
#|4
#|1431655765
#|0
#|0
#|355/113
#|1/3
#|10/1
#|1073741828 6
#|4294967293 1073741828
#|929887699 536870915
#|3365079597 3758096381
#|True
#|False
#|101
#|4294967291
#|0
