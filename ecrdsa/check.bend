import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../ecc/ecc.bend as E
import ../ecc/curves.bend as C
import ../ecc/ecdsa.bend as S
import ./ecrdsa.bend as G

def h(s: String) -> N.BnNat:
  Maybe.default(&2, N.BnNat, N.BnNat.of_hex(s), N.BnNat.zero())

def bs(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def rs(r: Result<&2, &2, G.EcrdsaError, S.EcSig>) -> String:
  match r:
    case Fail{G.EcrdsaBadNonce{}}:
      "bad-nonce"
    case Fail{G.EcrdsaBadPrivateKey{}}:
      "bad-private"
    case Fail{G.EcrdsaBadPublicKey{}}:
      "bad-public"
    case Done{S.EcSig{r, s}}:
      N.BnNat.hex(r) ++ " " ++ N.BnNat.hex(s)

def pt(p: E.EcPoint) -> String:
  match p:
    case E.EcInf{}:
      "inf"
    case E.EcAff{x, y}:
      N.BnNat.hex(x) ++ " " ++ N.BnNat.hex(y)

def rp(r: Result<&2, &2, G.EcrdsaError, E.EcPoint>) -> String:
  match r:
    case Fail{e}:
      "bad-public"
    case Done{p}:
      pt(p)

def xorc(xs: List<&2, U32>, +c: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{U32.xor(x, c), xorc(t, c)}

def hmac.go(+k: B.Octets, m: B.Octets) -> B.Octets:
  +k0 = B.Octets.to_list(B.Octets.append(k, B.Octets.zeros(Nat.sub(64n, B.Octets.len(k)))))
  G.Ecrdsa.streebog256(B.Octets.append(B.Octets.of_list(xorc(k0, 92)), G.Ecrdsa.streebog256(B.Octets.append(B.Octets.of_list(xorc(k0, 54)), m))))

# HMAC over Streebog-256 (RFC 2104, a 64-byte block) for keys of at most 64
# bytes
def hmac(k: B.Octets, m: B.Octets) -> B.Octets:
  hmac.go(k, m)

def okv(r: Result<&2, &2, G.EcrdsaError, S.EcSig>, +c: E.EcCurve, q: E.EcPoint, m: B.Octets) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{s}:
      bs(G.Ecrdsa.verify_bytes(~G.Ecrdsa.streebog256, c, q, m, G.Ecrdsa.sig_to(c, s)))

def main() -> IO(Unit):
  +c = E.EcCurve.of(C.EcCurves.gost_example())
  +d = h("7a929ade789bb9be10ed359dd39a72c11b60961f49397eee1d19ce9891ec3b28")
  +q = G.Ecrdsa.public(c, d)
  +e = h("2dfbc1b372d89a1188c09c52e0eec61fce52032ab1022e8e67ece6672b043ee5")
  +k = h("77105c9b20bcd3122823c8cf6fcc7b956de33814e95b7fe64fed924594dceab3")
  +ca = E.EcCurve.of(C.EcCurves.gost_cp_a())
  +da = h("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef")
  +qa = G.Ecrdsa.public(ca, da)
  +msg = B.Octets.of_string("GOST R 34.10-2012")
  do IO<Unit>:
    IO.print("public " ++ pt(q))
    IO.print("sign " ++ rs(G.Ecrdsa.sign_e(c, d, e, k)))
    IO.print("verify " ++ bs(G.Ecrdsa.verify_e(c, q, e, S.EcSig{h("41aa28d2f1ab148280cd9ed56feda41974053554a42767b83ad043fd39dc0493"), h("1456c64ba4642a1653c235a98a60249bcd6d3f746b631df928014f6c5bf9c40")})) ++ " " ++ bs(G.Ecrdsa.verify_e(c, q, e, S.EcSig{h("41aa28d2f1ab148280cd9ed56feda41974053554a42767b83ad043fd39dc0494"), h("1456c64ba4642a1653c235a98a60249bcd6d3f746b631df928014f6c5bf9c40")})))
    IO.print("cryptopro-a, streebog-256, deterministic " ++ okv(G.Ecrdsa.sign_det(~G.Ecrdsa.streebog256, ~hmac, ca, da, msg), ca, qa, msg))
    IO.print("public form " ++ rp(G.Ecrdsa.public_of(ca, G.Ecrdsa.public_to(ca, qa))) ++ " / " ++ pt(qa))
    IO.print("refused " ++ rp(G.Ecrdsa.public_of(ca, B.Octets.zeros(64n))) ++ " " ++ rs(G.Ecrdsa.sign_e(c, d, e, N.BnNat.zero())))
#|public 7f2b49e270db6d90d8595bec458b50c58585ba1d4e9b788f6689dbd8e56fd80b 26f1b489d6701dd185c8413a977b3cbbaf64d1c593d26627dffb101a87ff77da
#|sign 41aa28d2f1ab148280cd9ed56feda41974053554a42767b83ad043fd39dc0493 1456c64ba4642a1653c235a98a60249bcd6d3f746b631df928014f6c5bf9c40
#|verify yes no
#|cryptopro-a, streebog-256, deterministic yes
#|public form 27c5dbdfd29e417fff68b1d000c13d6118ebd6c7c5f88fcefb715e5d72e5e8f8 25c27dba270e21eee9d553fe267c8dbcdce100e60782287461ad03996e52c352 / 27c5dbdfd29e417fff68b1d000c13d6118ebd6c7c5f88fcefb715e5d72e5e8f8 25c27dba270e21eee9d553fe267c8dbcdce100e60782287461ad03996e52c352
#|refused bad-public bad-nonce
