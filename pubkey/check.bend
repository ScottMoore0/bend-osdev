import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../ecc/ecc.bend as E
import ../ecc/curves.bend as EC
import ../dh/dh.bend as D
import ../dh/groups.bend as DG
import ../rsa/rsa.bend as R
import ../rsa/keys.bend as K
import ../crypto/crypto.bend as Cr
import ../crypto/sign.bend as Sg
import ../crypto/kex.bend as Kx
import ./rsa.bend as PR
import ./dh.bend as PD
import ./ecc.bend as PE
import ./sm2.bend as PS
import ./ecrdsa.bend as PG

# Every instance through crypto's interfaces: keys from bytes, a signature
# checked from the public key's bytes (CrSign.verify_bytes), agreement from
# the peer's bytes (CrKex.agree)

def h(s: String) -> N.BnNat:
  Maybe.default(&2, N.BnNat, N.BnNat.of_hex(s), N.BnNat.zero())

# a number's big-endian bytes, of length l
def be(s: String, +l: Nat) -> B.Octets:
  Result.default(&2, &2, R.RsaError, B.Octets, R.Rsa.i2osp(h(s), l), B.Octets.empty())

def bs(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def ro(r: Result<&2, &2, Cr.CrError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "refused"
    case Done{o}:
      B.Octets.hex(o)

def same.go(x: B.Octets, b: Result<&2, &2, Cr.CrError, B.Octets>) -> String:
  match b:
    case Fail{e}:
      "refused"
    case Done{y}:
      bs(B.Octets.is_eq(x, y))

def same(a: Result<&2, &2, Cr.CrError, B.Octets>, b: Result<&2, &2, Cr.CrError, B.Octets>) -> String:
  match a:
    case Fail{e}:
      "refused"
    case Done{x}:
      same.go(x, b)

def nat(r: Result<&2, &2, Cr.CrError, N.BnNat>) -> N.BnNat:
  Result.default(&2, &2, Cr.CrError, N.BnNat, r, N.BnNat.zero())

# ECDSA over P-256 with SHA-256: RFC 6979 A.2.5's key x and message
# "sample"; the signature is r || s of that section
def ecdsa() -> String:
  +d = nat(PE.PkEcdh.secret(~EC.EcCurves.p256(), be("c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721", 32n)))
  +pk = PE.PkEcdh.pk_to(~EC.EcCurves.p256(), PE.PkEcdh.public(~EC.EcCurves.p256(), d))
  +m = B.Octets.of_string("sample")
  +s = PE.PkEcdsa.p256_sha256_sign(d, m)
  B.Octets.hex(s) ++ " " ++ bs(Sg.CrSign.verify_bytes(~E.EcPoint, ~PE.PkEcdh.pk_of(~EC.EcCurves.p256()), ~PE.PkEcdsa.p256_sha256_verify, pk, m, s)) ++ " " ++ bs(Sg.CrSign.verify_bytes(~E.EcPoint, ~PE.PkEcdh.pk_of(~EC.EcCurves.p256()), ~PE.PkEcdsa.p256_sha256_verify, pk, B.Octets.of_string("samplf"), s)) ++ " " ++ bs(Sg.CrSign.verify_bytes(~E.EcPoint, ~PE.PkEcdh.pk_of(~EC.EcCurves.p256()), ~PE.PkEcdsa.p256_sha256_verify, B.Octets.zeros(65n), m, s))

# SM2 with SM3 on SM2's curve, identity "1234567812345678"
def sm2() -> String:
  +d = nat(PS.PkSm2.secret(~EC.EcCurves.sm2(), be("3945208f7b2144b13f36e38ac6d39f95889393692860b51a42fb81ef4df7c5b8", 32n)))
  +pk = PE.PkEcdh.pk_to(~EC.EcCurves.sm2(), PE.PkEcdh.public(~EC.EcCurves.sm2(), d))
  +m = B.Octets.of_string("message digest")
  +s = PS.PkSm2.sm3_sign(d, m)
  Nat.show(B.Octets.len(s)) ++ " bytes " ++ bs(Sg.CrSign.verify_bytes(~E.EcPoint, ~PE.PkEcdh.pk_of(~EC.EcCurves.sm2()), ~PS.PkSm2.sm3_verify, pk, m, s)) ++ " " ++ bs(Sg.CrSign.verify_bytes(~E.EcPoint, ~PE.PkEcdh.pk_of(~EC.EcCurves.sm2()), ~PS.PkSm2.sm3_verify, pk, B.Octets.of_string("message digesT"), s))

# GOST R 34.10-2012 on CryptoPro-A with Streebog-256
def ecrdsa() -> String:
  +d = nat(PG.PkEcrdsa.secret(~EC.EcCurves.gost_cp_a(), be("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef", 32n)))
  +pk = PG.PkEcrdsa.pk_to(~EC.EcCurves.gost_cp_a(), PE.PkEcdh.public(~EC.EcCurves.gost_cp_a(), d))
  +m = B.Octets.of_string("GOST R 34.10-2012")
  +s = PG.PkEcrdsa.cp_a_streebog256_sign(d, m)
  Nat.show(B.Octets.len(s)) ++ " bytes " ++ bs(Sg.CrSign.verify_bytes(~E.EcPoint, ~PG.PkEcrdsa.pk_of(~EC.EcCurves.gost_cp_a()), ~PG.PkEcrdsa.cp_a_streebog256_verify, pk, m, s)) ++ " " ++ bs(Sg.CrSign.verify_bytes(~E.EcPoint, ~PG.PkEcrdsa.pk_of(~EC.EcCurves.gost_cp_a()), ~PG.PkEcrdsa.cp_a_streebog256_verify, pk, B.Octets.of_string("GOST R 34.10-2013"), s))

# an RSA-2048 key made by Python's cryptography (rsa/check.bend's), and
# cryptography's RSASSA-PKCS1-v1_5 and RSASSA-PSS signatures of "abc" over
# SHA-256
def rsa_key() -> B.Octets:
  K.RsaKeys.private_to(Result.default(&2, &2, R.RsaError, R.RsaPrivate, R.Rsa.private_of(h("bebc4488b9017a5755bb005e5602d69bf6d9b6a053d0651506108c24944d9085c9eb9b6119fd851fccff9933ec2cb891c7c43ad378202f7b574adb47d6bc9105d340c0380ac2cd76bed6ac4832b4905998f986bd5e5c405ea155bed99adb15f48df25eb8401d3bdf78a869d50d249cf5ac63cb022441ed589552123181032b5b57be10d5aaa136900bb16372842d95f93be5d919bfda1b4c7aafa2647ac38878a2debaefa956fa8d1a4dea1ddae9dd05c75ddad277f27dc4469af2cf91b411bd3d56d144ad92419bc57a7fbacdb5d28e72f71cafbdb598d6b79238a4c648b919e2badea3774ffc3536f0ee84012b12ef9df258eb69fc37cca7c54a25a9f7d9ff"), h("10001"), h("4b39473240fcd33a54866f0bc59252ffa9e88d7d47f0fd9cc00a90aaf08e72bc413999cb3f0bdc900132a1427817df2727893dc61f2f5a6aa3afd331cf000996298df501654514f18b2c713ffc377862cdd14391b6005e26b42c741bb0564d9f68c8391123c023d7ebe747ee0dc3eddf7a80d514e025dc2cbe9f62ab817d35809e07285c1d2259ce45f75a28b680e223c7c1f416a03ca071e0aa29ae656b8d4a3e229b3686102fa33a6d3b64136a7aac67085980372e941d45891ad19a7146e7314e0875c49038ebee903191b6bce5d6cc91a9c1236f4bcd6bab60796e19cdb42c15766ec1dddf42332668ada9033d4677efa6d1417b92a98b7e0ea4eea7ee99"), h("fcc0b70c32ef9edf13afa2206255624b198c73694b59c70db0dae3b5e8b5607d9459c17da623265ba9dccc54bcc16462621f0170a7253ec0b033445a0a12e7f2162a39fda6ac7fb33928895215029622475ebfbb125aca92865ecb922944760807edfc0cb197106d9b2e08fb9f076896d58c250680251b582507897ad1a26995"), h("c12f950ae4313639b6321159192ea1ac1d5c297e88933851d5639ce982c5f4a86dffecb4fbcbfbdb35e6ee7302b28edae7227f5349f9841bdde439ed272be1a2951765d399b37f5e6d0a6be57c11ab4bbaae1490f09007a2bc3b4251319c511d4e6b1f89e74d53ef1f8396d24da0d32f89e4215304a22ba5b96d74baeabf5843")), R.RsaPrivate{N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero()}))

def rsa_pkcs1_sig() -> B.Octets:
  be("51fc053325e6001fc437194ce89ac04f6767eea708944e61122709e43267b953cf9e0f96714c25434af8dda3aa3c7b6bf48f81d8c48ca62db3ece751a37a54973dba81392ca8f8815bf51c92e5a6966e0c5a3432f6c86ef8f4dfefee24716da30b930b8d75f73c5ab1d32d93f8c85973f294f89b5018647dd3b76a69fc2a42f715acbcd4855e31f36ce900b8463c313acdb29cab0c3f36d30688c9a30be0cab0b822d3764e37fdcd10daa169fb08cde8e4d9f9572dda29a5dec68c23a0e37dccd0d4d3f1f9f99e5c98bc573dfd15098a803f9ff0c463a3b4569a553251614793bde28ddef2b8744aaaac43620233427979105339cf213c796fccd30b7062bf5c", 256n)

def rsa_pss_sig() -> B.Octets:
  be("54eb6cbb515cb5d304176918cbb5e12172fb5ef17cf296075c26e5de5b3cb752e709f1ab95856e60f9200990a69d553934afc8c7e65d857d28dae370a6d2afde702c12c4d163f4872a03cc554080a5d5698993f05b9cba5fc3ae6e064565033aa0555b3f0176ae0f04dde85cd855898120b7769e5e2f026d9b5beb27ab8fc5f842f59aeb8c2aacac9bec9d683cf8685c2e5725a148054ab967475626ac2ab5cb8128f8abff25145868ce71f7152cc1e4c2b6413c3e3842f85af28fd099c07403b7c3529ab9a6c3fdb01534f0e6d60e69658a1cdb442430bba17f806fa2054cd77fb2ad3e532828b9ecc3093945734681b0c5cca925a1319ddf0cb2cdce8d84e9", 256n)

def rsa.go(r: Result<&2, &2, Cr.CrError, R.RsaPrivate>) -> String:
  match r:
    case Fail{e}:
      "refused"
    case Done{+sk}:
      +pk = K.RsaKeys.public_to(R.Rsa.public(sk))
      +m = B.Octets.of_string("abc")
      +s1 = PR.PkRsa.pkcs1_sha256_sign(sk, m)
      +s2 = PR.PkRsa.pss_sha256_sign(sk, m)
      "pkcs1 " ++ bs(B.Octets.is_eq(s1, rsa_pkcs1_sig())) ++ " " ++ bs(Sg.CrSign.verify_bytes(~R.RsaPublic, ~PR.PkRsa.pk_of, ~PR.PkRsa.pkcs1_sha256_verify, pk, m, s1)) ++ " " ++ bs(Sg.CrSign.verify_bytes(~R.RsaPublic, ~PR.PkRsa.pk_of, ~PR.PkRsa.pkcs1_sha256_verify, pk, B.Octets.of_string("abd"), s1)) ++ ", pss " ++ bs(Sg.CrSign.verify_bytes(~R.RsaPublic, ~PR.PkRsa.pk_of, ~PR.PkRsa.pss_sha256_verify, pk, m, s2)) ++ " " ++ bs(Sg.CrSign.verify_bytes(~R.RsaPublic, ~PR.PkRsa.pk_of, ~PR.PkRsa.pss_sha256_verify, pk, m, rsa_pss_sig())) ++ " " ++ bs(Sg.CrSign.verify_bytes(~R.RsaPublic, ~PR.PkRsa.pk_of, ~PR.PkRsa.pss_sha256_verify, pk, B.Octets.of_string("abd"), s2))

def rsa() -> String:
  rsa.go(PR.PkRsa.secret(rsa_key()))

# ECDH over P-256: both parties from each other's bytes
def ecdh() -> String:
  +a = be("c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721", 32n)
  +b = be("0f0e0d0c0b0a090807060504030201000102030405060708090a0b0c0d0e0f10", 32n)
  +pa = PE.PkEcdh.pk_to(~EC.EcCurves.p256(), PE.PkEcdh.public(~EC.EcCurves.p256(), nat(PE.PkEcdh.secret(~EC.EcCurves.p256(), a))))
  +pb = PE.PkEcdh.pk_to(~EC.EcCurves.p256(), PE.PkEcdh.public(~EC.EcCurves.p256(), nat(PE.PkEcdh.secret(~EC.EcCurves.p256(), b))))
  +z = Kx.CrKex.agree(~N.BnNat, ~E.EcPoint, ~PE.PkEcdh.secret(~EC.EcCurves.p256()), ~PE.PkEcdh.pk_of(~EC.EcCurves.p256()), ~PE.PkEcdh.shared(~EC.EcCurves.p256()), a, pb)
  same(z, Kx.CrKex.agree(~N.BnNat, ~E.EcPoint, ~PE.PkEcdh.secret(~EC.EcCurves.p256()), ~PE.PkEcdh.pk_of(~EC.EcCurves.p256()), ~PE.PkEcdh.shared(~EC.EcCurves.p256()), b, pa)) ++ " " ++ ro(Kx.CrKex.agree(~N.BnNat, ~E.EcPoint, ~PE.PkEcdh.secret(~EC.EcCurves.p256()), ~PE.PkEcdh.pk_of(~EC.EcCurves.p256()), ~PE.PkEcdh.shared(~EC.EcCurves.p256()), a, B.Octets.zeros(65n))) ++ " " ++ ro(Kx.CrKex.agree(~N.BnNat, ~E.EcPoint, ~PE.PkEcdh.secret(~EC.EcCurves.p256()), ~PE.PkEcdh.pk_of(~EC.EcCurves.p256()), ~PE.PkEcdh.shared(~EC.EcCurves.p256()), B.Octets.zeros(32n), pb))

# Diffie-Hellman over FFDHE-2048: both parties from each other's bytes
def dh() -> String:
  +a = be("c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721", 32n)
  +b = be("0f0e0d0c0b0a090807060504030201000102030405060708090a0b0c0d0e0f10", 32n)
  +pa = PD.PkDh.pk_to(~DG.DhGroups.ffdhe2048(), PD.PkDh.public(~DG.DhGroups.ffdhe2048(), nat(PD.PkDh.secret(~DG.DhGroups.ffdhe2048(), a))))
  +pb = PD.PkDh.pk_to(~DG.DhGroups.ffdhe2048(), PD.PkDh.public(~DG.DhGroups.ffdhe2048(), nat(PD.PkDh.secret(~DG.DhGroups.ffdhe2048(), b))))
  +z = Kx.CrKex.agree(~N.BnNat, ~N.BnNat, ~PD.PkDh.secret(~DG.DhGroups.ffdhe2048()), ~PD.PkDh.pk_of(~DG.DhGroups.ffdhe2048()), ~PD.PkDh.shared(~DG.DhGroups.ffdhe2048()), a, pb)
  Nat.show(B.Octets.len(pa)) ++ "-byte keys " ++ same(z, Kx.CrKex.agree(~N.BnNat, ~N.BnNat, ~PD.PkDh.secret(~DG.DhGroups.ffdhe2048()), ~PD.PkDh.pk_of(~DG.DhGroups.ffdhe2048()), ~PD.PkDh.shared(~DG.DhGroups.ffdhe2048()), b, pa)) ++ " " ++ ro(Kx.CrKex.agree(~N.BnNat, ~N.BnNat, ~PD.PkDh.secret(~DG.DhGroups.ffdhe2048()), ~PD.PkDh.pk_of(~DG.DhGroups.ffdhe2048()), ~PD.PkDh.shared(~DG.DhGroups.ffdhe2048()), a, be("1", 256n)))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("ecdsa p-256 sha-256 " ++ ecdsa())
    IO.print("sm2 sm3 " ++ sm2())
    IO.print("ec-rdsa cryptopro-a streebog-256 " ++ ecrdsa())
    IO.print("rsa-2048 sha-256 " ++ rsa())
    IO.print("ecdh p-256 " ++ ecdh())
    IO.print("dh ffdhe2048 " ++ dh())
#|ecdsa p-256 sha-256 efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716f7cb1c942d657c41d436c7a1b6e29f65f3e900dbb9aff4064dc4ab2f843acda8 yes no no
#|sm2 sm3 64 bytes yes no
#|ec-rdsa cryptopro-a streebog-256 64 bytes yes no
#|rsa-2048 sha-256 pkcs1 yes yes no, pss yes yes no
#|ecdh p-256 yes refused refused
#|dh ffdhe2048 256-byte keys yes refused
