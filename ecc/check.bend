import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ./ecc.bend as E
import ./curves.bend as C
import ./ecdh.bend as D
import ./ecdsa.bend as S
import ./rfc6979.bend as R
import bend-collections-laws-crypto@1.0.0.0/src/crypto/hash.bend as Hc

def sha256(o: B.Octets) -> B.Octets:
  B.Octets.of_list(Hc.sha256(B.Octets.to_list(o)))

def xorc(xs: List<&2, U32>, +c: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{U32.xor(x, c), xorc(t, c)}

# HMAC-SHA-256 (RFC 2104) for keys of at most 64 bytes, for RFC 6979
def hmac.go(+k: B.Octets, m: B.Octets) -> B.Octets:
  +k0 = B.Octets.to_list(B.Octets.append(k, B.Octets.zeros(Nat.sub(64n, B.Octets.len(k)))))
  sha256(B.Octets.append(B.Octets.of_list(xorc(k0, 92)), sha256(B.Octets.append(B.Octets.of_list(xorc(k0, 54)), m))))

def hmac(k: B.Octets, m: B.Octets) -> B.Octets:
  hmac.go(k, m)

def h(s: String) -> N.BnNat:
  Maybe.default(&2, N.BnNat, N.BnNat.of_hex(s), N.BnNat.zero())

def bs(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def rs(r: Result<&2, &2, E.EcError, S.EcSig>) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{S.EcSig{r, s}}:
      N.BnNat.hex(r) ++ " " ++ N.BnNat.hex(s)

def ro(r: Result<&2, &2, E.EcError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{o}:
      B.Octets.hex(o)

def chk(p: E.EcParams) -> String:
  bs(E.EcCurve.check(E.EcCurve.of(p)))

def rfc6979_x() -> N.BnNat:
  h("c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721")

def main() -> IO(Unit):
  +c = E.EcCurve.of(C.EcCurves.p256())
  +q = D.EcDh.public(c, rfc6979_x())
  +d1 = h("1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f1f")
  +d2 = h("2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e2e")
  +sample = B.Octets.of_string("sample")
  +test = B.Octets.of_string("test")
  do IO<Unit>:
    IO.print("check p192 " ++ chk(C.EcCurves.p192()) ++ " p224 " ++ chk(C.EcCurves.p224()) ++ " p256 " ++ chk(C.EcCurves.p256()) ++ " p384 " ++ chk(C.EcCurves.p384()) ++ " p521 " ++ chk(C.EcCurves.p521()))
    IO.print("check sm2 " ++ chk(C.EcCurves.sm2()) ++ " gost a " ++ chk(C.EcCurves.gost_cp_a()) ++ " b " ++ chk(C.EcCurves.gost_cp_b()) ++ " c " ++ chk(C.EcCurves.gost_cp_c()) ++ " example " ++ chk(C.EcCurves.gost_example()))
    IO.print("public " ++ B.Octets.hex(E.EcCurve.point_to(c, q)))
    IO.print("k sample " ++ N.BnNat.hex(R.EcRfc6979.k(~hmac, E.EcCurve.n(c), rfc6979_x(), sha256(sample))))
    IO.print("sign sample " ++ rs(S.EcDsa.sign_det(~sha256, ~hmac, c, rfc6979_x(), sample)))
    IO.print("k test " ++ N.BnNat.hex(R.EcRfc6979.k(~hmac, E.EcCurve.n(c), rfc6979_x(), sha256(test))))
    IO.print("sign test " ++ rs(S.EcDsa.sign_det(~sha256, ~hmac, c, rfc6979_x(), test)))
    IO.print("verify " ++ bs(S.EcDsa.verify_bytes(~sha256, c, q, sample, B.Octets.append(B.Octets.of_list([239, 212, 139, 42, 172, 182, 168, 253, 17, 64, 221, 156, 212, 94, 129, 214, 157, 44, 135, 123, 86, 170, 249, 145, 195, 77, 14, 168, 78, 175, 55, 22]), B.Octets.of_list([247, 203, 28, 148, 45, 101, 124, 65, 212, 54, 199, 161, 182, 226, 159, 101, 243, 233, 0, 219, 185, 175, 244, 6, 77, 196, 171, 47, 132, 58, 205, 168])))) ++ " " ++ bs(S.EcDsa.verify_bytes(~sha256, c, q, test, B.Octets.zeros(64n))))
    IO.print("ecdh " ++ ro(D.EcDh.agree(c, d1, D.EcDh.public(c, d2))) ++ " " ++ ro(D.EcDh.agree(c, d2, D.EcDh.public(c, d1))))
    IO.print("order " ++ bs(E.EcPoint.is_inf(E.EcCurve.base_mul(c, E.EcCurve.n(c)))) ++ " refused " ++ ro(D.EcDh.agree(c, d1, E.EcAff{N.BnNat.one(), N.BnNat.one()})))
#|check p192 yes p224 yes p256 yes p384 yes p521 yes
#|check sm2 yes gost a yes b yes c yes example yes
#|public 0460fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb67903fe1008b8bc99a41ae9e95628bc64f2f1b20c2d7e9f5177a3c294d4462299
#|k sample a6e3c57dd01abe90086538398355dd4c3b17aa873382b0f24d6129493d8aad60
#|sign sample efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716 f7cb1c942d657c41d436c7a1b6e29f65f3e900dbb9aff4064dc4ab2f843acda8
#|k test d16b6ae827f17175e040871a1c7ec3500192c4c92677336ec2537acaee0008e0
#|sign test f1abb023518351cd71d881567b1ea663ed3efcf6c5132b354f28d3b0b7d38367 19f4113742a2b14bd25926b49c649155f267e60d3814b4c0cc84250e46f0083
#|verify yes no
#|ecdh 8ff9d3b60959e96d66f6099897f6a9ef3c905352d6deb18885c22cdcc693b073 8ff9d3b60959e96d66f6099897f6a9ef3c905352d6deb18885c22cdcc693b073
#|order yes refused fail
