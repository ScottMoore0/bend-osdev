import Base
import ../bytes/bytes.bend as B
import ./bignum.bend as N
import ./modular.bend as Md
import ./mont.bend as Mt
import ./prime.bend as Pr
import ./jacobi.bend as J

def h(s: String) -> N.BnNat:
  Maybe.default(&2, N.BnNat, N.BnNat.of_hex(s), N.BnNat.zero())

def x(n: N.BnNat) -> String:
  N.BnNat.hex(n)

def bs(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def mo(m: Maybe<&2, B.Octets>) -> String:
  match m:
    case None{}:
      "none"
    case Some{o}:
      B.Octets.hex(o)

def mn(m: Maybe<&2, N.BnNat>) -> String:
  match m:
    case None{}:
      "none"
    case Some{v}:
      x(v)

def js(m: Maybe<&2, J.BnJacobi>) -> String:
  match m:
    case Some{J.BnJacZero{}}:
      "0"
    case Some{J.BnJacPlus{}}:
      "1"
    case Some{J.BnJacMinus{}}:
      "-1"
    case None{}:
      "none"

def mersenne(e: Nat) -> N.BnNat:
  N.BnNat.sub(N.BnNat.shl(N.BnNat.one(), e), N.BnNat.one())

def bases() -> List<&2, N.BnNat>:
  [N.BnNat.of_u32(2), N.BnNat.of_u32(3), N.BnNat.of_u32(5), N.BnNat.of_u32(7)]

# a 2048-bit odd modulus: 2^2048 - 1 - 12345 * 2^1024
def big() -> N.BnNat:
  N.BnNat.sub(mersenne(2048n), N.BnNat.mul(N.BnNat.of_u32(12345), N.BnNat.shl(N.BnNat.one(), 1024n)))

def main() -> IO(Unit):
  +a = h("123456789abcdef123456789abcdef123456789abcdef123456789abcdef123456789abcdef123456789abcdef123456789abcdef123456789abcdef123456789abcdef123456789abcdef")
  +p127 = mersenne(127n)
  +p521 = mersenne(521n)
  +n = big()
  do IO<Unit>:
    IO.print("os2ip " ++ x(N.BnNat.of_octets(B.Octets.of_list([0, 1, 2, 255]))))
    IO.print("i2osp " ++ mo(N.BnNat.to_octets(h("102ff"), 5n)) ++ " " ++ mo(N.BnNat.to_octets(h("102ff"), 2n)))
    IO.print("square " ++ x(N.BnNat.mul(a, a)))
    IO.print("mod " ++ x(N.BnNat.mod(a, p127)))
    IO.print("modexp " ++ x(Md.BnMod.exp(a, N.BnNat.of_u32(65537), p521)))
    IO.print("inverse " ++ mn(Md.BnMod.inv(N.BnNat.of_u32(3), p127)))
    IO.print("fermat-2048 " ++ x(N.BnNat.shr(Md.BnMod.exp(N.BnNat.of_u32(7), N.BnNat.sub(n, N.BnNat.one()), n), 1888n)))
    IO.print("quotient " ++ x(N.BnNat.shr(N.BnNat.div(N.BnNat.shl(N.BnNat.one(), 4096n), N.BnNat.add(N.BnNat.shl(N.BnNat.one(), 2048n), N.BnNat.of_u32(12345))), 1856n)))
    IO.print("prime 2^127-1 " ++ bs(Pr.BnPrime.is_probable(p127, bases())) ++ ", 2^521-1 " ++ bs(Pr.BnPrime.is_probable(p521, bases())) ++ ", 2^128+1 " ++ bs(Pr.BnPrime.is_probable(N.BnNat.add(N.BnNat.shl(N.BnNat.one(), 128n), N.BnNat.one()), bases())))
    IO.print("jacobi " ++ js(J.BnNat.jacobi(N.BnNat.of_u32(1001), N.BnNat.of_u32(9907))) ++ " " ++ js(J.BnNat.jacobi(N.BnNat.of_u32(19), N.BnNat.of_u32(45))) ++ " " ++ js(J.BnNat.jacobi(N.BnNat.of_u32(5), N.BnNat.of_u32(8))))
    IO.print("gcd " ++ x(Md.BnMod.gcd(N.BnNat.of_u32(1071), N.BnNat.of_u32(462))))
#|os2ip 102ff
#|i2osp 00000102ff none
#|square 14b66dc33f6acdccf4ee417717abc989e75a6ba38aab6447fd0bfd59a9a2ff18471407aa88fb9b0bd6839ba77c744933bc6bca6692ee1aa109dda555e97a2064cfea442a41296b901fa32f353e3186b5348627aa5bb328324975c00d44de5114a890574ce8a1f04b9c4adc5835ecf4caf9043e1e1bae4dc2d5ab6b8d88d4ed61b12f53956c4fe9607a7ee524b50fca5e20890f2a521
#|mod 786848089abcdf0021415f79abcdf00
#|modexp a00c62a8f4a0dacd3815e2c2462d86533790612fdc00a4743a04d97356b4faf5d406266171e3a5394a1f6eea876616c783ed8b9a8cea9ced4595ab4f5bcc1bb6c9
#|inverse 55555555555555555555555555555555
#|fermat-2048 cac5196193d0bc9d4f688f810e5e9f02c288f190
#|quotient ffffffffffffffffffffffffffffffffffffffffffffffff
#|prime 2^127-1 yes, 2^521-1 yes, 2^128+1 no
#|jacobi -1 1 none
#|gcd 15
