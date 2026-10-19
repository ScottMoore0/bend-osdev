import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../ecc/ecc.bend as E
import ../ecc/curves.bend as C
import ../ecc/ecdsa.bend as S
import ./sm2.bend as M

def h(s: String) -> N.BnNat:
  Maybe.default(&2, N.BnNat, N.BnNat.of_hex(s), N.BnNat.zero())

def bs(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def rs(r: Result<&2, &2, M.Sm2Error, S.EcSig>) -> String:
  match r:
    case Fail{M.Sm2BadNonce{}}:
      "bad-nonce"
    case Fail{M.Sm2BadPrivateKey{}}:
      "bad-private"
    case Fail{M.Sm2IdTooLong{}}:
      "id-too-long"
    case Done{S.EcSig{r, s}}:
      N.BnNat.hex(r) ++ " " ++ N.BnNat.hex(s)

def pt(p: E.EcPoint) -> String:
  match p:
    case E.EcInf{}:
      "inf"
    case E.EcAff{x, y}:
      N.BnNat.hex(x) ++ " " ++ N.BnNat.hex(y)

def okv(r: Result<&2, &2, M.Sm2Error, S.EcSig>, c: E.EcCurve, q: E.EcPoint, id: B.Octets, m: B.Octets) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{s}:
      bs(M.Sm2.verify(~M.Sm2.sm3, c, q, id, m, s))

def xorc(xs: List<&2, U32>, +c: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{U32.xor(x, c), xorc(t, c)}

def hmac.go(+k: B.Octets, m: B.Octets) -> B.Octets:
  +k0 = B.Octets.to_list(B.Octets.append(k, B.Octets.zeros(Nat.sub(64n, B.Octets.len(k)))))
  M.Sm2.sm3(B.Octets.append(B.Octets.of_list(xorc(k0, 92)), M.Sm2.sm3(B.Octets.append(B.Octets.of_list(xorc(k0, 54)), m))))

# HMAC-SM3 (RFC 2104) for keys of at most 64 bytes
def hmac(k: B.Octets, m: B.Octets) -> B.Octets:
  hmac.go(k, m)

# draft-shen-sm2-ecdsa-02, Appendix A.2: the example's private key
def da() -> N.BnNat:
  h("128b2fa8bd433c6c068c8d803dff79792a519a55171b1b650c23661d15897263")

def ida() -> B.Octets:
  B.Octets.of_string("ALICE123@YAHOO.COM")

def main() -> IO(Unit):
  +c = E.EcCurve.of(C.EcCurves.sm2_example())
  +pa = M.Sm2.public(c, da())
  +msg = B.Octets.of_string("message digest")
  +k = h("6cb28d99385c175c94f94e934817663fc176d925dd72b727260dbaae1fb2f96f")
  +c2 = E.EcCurve.of(C.EcCurves.sm2())
  +d2 = h("3945208f7b2144b13f36e38ac6d39f95889393692860b51a42fb81ef4df7c5b8")
  +q2 = M.Sm2.public(c2, d2)
  do IO<Unit>:
    IO.print("public " ++ pt(pa))
    IO.print("za " ++ B.Octets.hex(M.Sm2.za(~M.Sm2.sm3, c, ida(), pa)))
    IO.print("e " ++ N.BnNat.hex(M.Sm2.e(~M.Sm2.sm3, c, ida(), pa, msg)))
    IO.print("sign " ++ rs(M.Sm2.sign(~M.Sm2.sm3, c, da(), ida(), msg, k)))
    IO.print("verify " ++ bs(M.Sm2.verify(~M.Sm2.sm3, c, pa, ida(), msg, S.EcSig{h("40f1ec59f793d9f49e09dcef49130d4194f79fb1eed2caa55bacdb49c4e755d1"), h("6fc6dac32c5d5cf10c77dfb20f7c2eb667a457872fb09ec56327a67ec7deebe7")})) ++ " " ++ bs(M.Sm2.verify(~M.Sm2.sm3, c, pa, ida(), B.Octets.of_string("message digesT"), S.EcSig{h("40f1ec59f793d9f49e09dcef49130d4194f79fb1eed2caa55bacdb49c4e755d1"), h("6fc6dac32c5d5cf10c77dfb20f7c2eb667a457872fb09ec56327a67ec7deebe7")})))
    IO.print("deterministic on sm2's curve " ++ okv(M.Sm2.sign_det(~M.Sm2.sm3, ~hmac, c2, d2, ida(), msg), c2, q2, ida(), msg))
    IO.print("refusals " ++ rs(M.Sm2.sign(~M.Sm2.sm3, c, da(), ida(), msg, N.BnNat.zero())) ++ " " ++ rs(M.Sm2.sign(~M.Sm2.sm3, c, da(), B.Octets.zeros(8192n), msg, k)))
#|public ae4c7798aa0f119471bee11825be46202bb79e2a5844495e97c04ff4df2548a 7c0240f88f1cd4e16352a73c17b7f16f07353e53a176d684a9fe0c6bb798e857
#|za f4a38489e32b45b6f876e3ac2168ca392362dc8f23459c1d1146fc3dbfb7bc9a
#|e b524f552cd82b8b028476e005c377fb19a87e6fc682d48bb5d42e3d9b9effe76
#|sign 40f1ec59f793d9f49e09dcef49130d4194f79fb1eed2caa55bacdb49c4e755d1 6fc6dac32c5d5cf10c77dfb20f7c2eb667a457872fb09ec56327a67ec7deebe7
#|verify yes no
#|deterministic on sm2's curve yes
#|refusals bad-nonce id-too-long
