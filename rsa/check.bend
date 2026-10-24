import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ./rsa.bend as R
import ./mgf1.bend as M
import ./pkcs1.bend as P
import ./pss.bend as S
import ./oaep.bend as O
import ./es15.bend as E
import ./keys.bend as K
import bend-collections-laws-crypto@1.0.0.0/src/crypto/hash.bend as Hc

# An RSA-2048 key (e = 65537) made by Python's cryptography for this file,
# and its RSASSA-PKCS1-v1_5 and RSASSA-PSS (MGF1-SHA-256, 32-byte salt)
# signatures of "abc" over SHA-256, made by cryptography

def sha256(o: B.Octets) -> B.Octets:
  B.Octets.of_list(Hc.sha256(B.Octets.to_list(o)))

def h(s: String) -> N.BnNat:
  Maybe.default(&2, N.BnNat, N.BnNat.of_hex(s), N.BnNat.zero())

def ob(s: String) -> B.Octets:
  Result.default(&2, &2, R.RsaError, B.Octets, R.Rsa.i2osp(h(s), 256n), B.Octets.empty())

def bs(b: Bool) -> String:
  match b:
    case True{}:
      "yes"
    case False{}:
      "no"

def err(e: R.RsaError) -> String:
  match e:
    case R.RsaMessageTooLong{}:
      "too-long"
    case R.RsaDecryptionError{}:
      "decryption-error"
    case R.RsaEncodingError{}:
      "encoding-error"
    case R.RsaOutOfRange{}:
      "out-of-range"
    case R.RsaIntegerTooLarge{}:
      "too-large"
    case R.RsaBadKey{}:
      "bad-key"
    case R.RsaBadFormat{}:
      "bad-format"
    case R.RsaNoPrime{}:
      "no-prime"

def ro(r: Result<&2, &2, R.RsaError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{o}:
      B.Octets.to_string(o)

def eqo(r: Result<&2, &2, R.RsaError, B.Octets>, +o: B.Octets) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{x}:
      bs(B.Octets.is_eq(x, o))

def rn(r: Result<&2, &2, R.RsaError, N.BnNat>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{x}:
      N.BnNat.hex(x)

# a public key form read: n and e in hex and whether the form written for
# the key is the form read, or the error
def kf.go(r: Result<&2, &2, R.RsaError, R.RsaPublic>, +o: B.Octets) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{pk}:
      match pk:
        case R.RsaPublic{+n, +e}:
          N.BnNat.hex(n) ++ "," ++ N.BnNat.hex(e) ++ " " ++ bs(B.Octets.is_eq(K.RsaKeys.public_to(R.RsaPublic{n, e}), o))

def kf(xs: List<&2, U32>) -> String:
  +o = B.Octets.of_list(xs)
  kf.go(K.RsaKeys.public_of(o), o)

# a private key form read: whether the form written for the key is the form
# read, or the error
def kfp.go(r: Result<&2, &2, R.RsaError, R.RsaPrivate>, +o: B.Octets) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{sk}:
      bs(B.Octets.is_eq(K.RsaKeys.private_to(sk), o))

def kfp(xs: List<&2, U32>) -> String:
  +o = B.Octets.of_list(xs)
  kfp.go(K.RsaKeys.private_of(o), o)

def key() -> R.RsaPrivate:
  Result.default(&2, &2, R.RsaError, R.RsaPrivate, R.Rsa.private_of(h("bebc4488b9017a5755bb005e5602d69bf6d9b6a053d0651506108c24944d9085c9eb9b6119fd851fccff9933ec2cb891c7c43ad378202f7b574adb47d6bc9105d340c0380ac2cd76bed6ac4832b4905998f986bd5e5c405ea155bed99adb15f48df25eb8401d3bdf78a869d50d249cf5ac63cb022441ed589552123181032b5b57be10d5aaa136900bb16372842d95f93be5d919bfda1b4c7aafa2647ac38878a2debaefa956fa8d1a4dea1ddae9dd05c75ddad277f27dc4469af2cf91b411bd3d56d144ad92419bc57a7fbacdb5d28e72f71cafbdb598d6b79238a4c648b919e2badea3774ffc3536f0ee84012b12ef9df258eb69fc37cca7c54a25a9f7d9ff"), h("10001"), h("4b39473240fcd33a54866f0bc59252ffa9e88d7d47f0fd9cc00a90aaf08e72bc413999cb3f0bdc900132a1427817df2727893dc61f2f5a6aa3afd331cf000996298df501654514f18b2c713ffc377862cdd14391b6005e26b42c741bb0564d9f68c8391123c023d7ebe747ee0dc3eddf7a80d514e025dc2cbe9f62ab817d35809e07285c1d2259ce45f75a28b680e223c7c1f416a03ca071e0aa29ae656b8d4a3e229b3686102fa33a6d3b64136a7aac67085980372e941d45891ad19a7146e7314e0875c49038ebee903191b6bce5d6cc91a9c1236f4bcd6bab60796e19cdb42c15766ec1dddf42332668ada9033d4677efa6d1417b92a98b7e0ea4eea7ee99"), h("fcc0b70c32ef9edf13afa2206255624b198c73694b59c70db0dae3b5e8b5607d9459c17da623265ba9dccc54bcc16462621f0170a7253ec0b033445a0a12e7f2162a39fda6ac7fb33928895215029622475ebfbb125aca92865ecb922944760807edfc0cb197106d9b2e08fb9f076896d58c250680251b582507897ad1a26995"), h("c12f950ae4313639b6321159192ea1ac1d5c297e88933851d5639ce982c5f4a86dffecb4fbcbfbdb35e6ee7302b28edae7227f5349f9841bdde439ed272be1a2951765d399b37f5e6d0a6be57c11ab4bbaae1490f09007a2bc3b4251319c511d4e6b1f89e74d53ef1f8396d24da0d32f89e4215304a22ba5b96d74baeabf5843")), R.RsaPrivate{N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero(), N.BnNat.zero()})

def sig_pkcs1() -> B.Octets:
  ob("51fc053325e6001fc437194ce89ac04f6767eea708944e61122709e43267b953cf9e0f96714c25434af8dda3aa3c7b6bf48f81d8c48ca62db3ece751a37a54973dba81392ca8f8815bf51c92e5a6966e0c5a3432f6c86ef8f4dfefee24716da30b930b8d75f73c5ab1d32d93f8c85973f294f89b5018647dd3b76a69fc2a42f715acbcd4855e31f36ce900b8463c313acdb29cab0c3f36d30688c9a30be0cab0b822d3764e37fdcd10daa169fb08cde8e4d9f9572dda29a5dec68c23a0e37dccd0d4d3f1f9f99e5c98bc573dfd15098a803f9ff0c463a3b4569a553251614793bde28ddef2b8744aaaac43620233427979105339cf213c796fccd30b7062bf5c")

def sig_pss() -> B.Octets:
  ob("54eb6cbb515cb5d304176918cbb5e12172fb5ef17cf296075c26e5de5b3cb752e709f1ab95856e60f9200990a69d553934afc8c7e65d857d28dae370a6d2afde702c12c4d163f4872a03cc554080a5d5698993f05b9cba5fc3ae6e064565033aa0555b3f0176ae0f04dde85cd855898120b7769e5e2f026d9b5beb27ab8fc5f842f59aeb8c2aacac9bec9d683cf8685c2e5725a148054ab967475626ac2ab5cb8128f8abff25145868ce71f7152cc1e4c2b6413c3e3842f85af28fd099c07403b7c3529ab9a6c3fdb01534f0e6d60e69658a1cdb442430bba17f806fa2054cd77fb2ad3e532828b9ecc3093945734681b0c5cca925a1319ddf0cb2cdce8d84e9")

def pkv(r: Result<&2, &2, R.RsaError, R.RsaPublic>, m: B.Octets, s: B.Octets) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{pk}:
      bs(P.RsaPkcs1.verify(~sha256, P.RsaDigestInfo.sha256(), pk, m, s))

def main() -> IO(Unit):
  +sk = key()
  +pk = R.Rsa.public(sk)
  +m = B.Octets.of_string("abc")
  +salt = B.Octets.of_list([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32])
  +seed = sha256(B.Octets.of_string("seed"))
  +ps = B.Octets.of_list([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250])
  +c = h("1234567890abcdef")
  do IO<Unit>:
    IO.print("modulus bits " ++ Nat.show(R.Rsa.mod_bits(pk)) ++ ", k " ++ Nat.show(R.Rsa.k(pk)))
    IO.print("pkcs1 sign is cryptography's " ++ eqo(P.RsaPkcs1.sign(~sha256, P.RsaDigestInfo.sha256(), sk, m), sig_pkcs1()))
    IO.print("pkcs1 verify " ++ bs(P.RsaPkcs1.verify(~sha256, P.RsaDigestInfo.sha256(), pk, m, sig_pkcs1())) ++ " " ++ bs(P.RsaPkcs1.verify(~sha256, P.RsaDigestInfo.sha256(), pk, B.Octets.of_string("abd"), sig_pkcs1())))
    IO.print("pss verify cryptography's " ++ bs(S.RsaPss.verify(~sha256, ~M.RsaMgf1.mask(~sha256), pk, m, sig_pss(), 32n)) ++ " " ++ bs(S.RsaPss.verify(~sha256, ~M.RsaMgf1.mask(~sha256), pk, B.Octets.of_string("abd"), sig_pss(), 32n)))
    IO.print("pss own " ++ bs(Result.default(&2, &2, R.RsaError, Bool, Result.map(&2, &2, R.RsaError, B.Octets, Bool, s => S.RsaPss.verify(~sha256, ~M.RsaMgf1.mask(~sha256), pk, m, s, 32n), S.RsaPss.sign(~sha256, ~M.RsaMgf1.mask(~sha256), sk, m, salt)), False{})))
    IO.print("oaep " ++ ro(Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, O.RsaOaep.encrypt(~sha256, ~M.RsaMgf1.mask(~sha256), pk, B.Octets.empty(), m, seed), x => O.RsaOaep.decrypt(~sha256, ~M.RsaMgf1.mask(~sha256), sk, B.Octets.empty(), x))))
    IO.print("pkcs1 v1.5 encryption " ++ ro(Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, E.RsaEs15.encrypt(pk, m, ps), x => E.RsaEs15.decrypt(sk, x))))
    IO.print("crt " ++ rn(R.Rsa.dp(sk, c)) ++ " plain " ++ rn(R.Rsa.dp_plain(sk, c)))
    IO.print("key form " ++ bs(B.Octets.is_eq(K.RsaKeys.private_to(Result.default(&2, &2, R.RsaError, R.RsaPrivate, K.RsaKeys.private_of(K.RsaKeys.private_to(sk)), key())), K.RsaKeys.private_to(sk))) ++ " " ++ pkv(K.RsaKeys.public_of(K.RsaKeys.public_to(pk)), m, sig_pkcs1()))
    IO.print("short forms: " ++ kf([0, 0, 0, 1, 197, 0, 0, 0, 1, 3]) ++ "; leading zero in n " ++ kf([0, 0, 0, 2, 0, 197, 0, 0, 0, 1, 3]) ++ ", in e " ++ kf([0, 0, 0, 1, 197, 0, 0, 0, 2, 0, 3]) ++ "; n = 0 as no bytes " ++ kf([0, 0, 0, 0, 0, 0, 0, 1, 3]) ++ ", as a byte " ++ kf([0, 0, 0, 1, 0, 0, 0, 0, 1, 3]))
    IO.print("private short form " ++ kfp([0, 0, 0, 1, 55, 0, 0, 0, 1, 3, 0, 0, 0, 1, 7, 0, 0, 0, 1, 5, 0, 0, 0, 1, 11]) ++ ", leading zero in d " ++ kfp([0, 0, 0, 1, 55, 0, 0, 0, 1, 3, 0, 0, 0, 2, 0, 7, 0, 0, 0, 1, 5, 0, 0, 0, 1, 11]))
    IO.print("refused " ++ ro(R.Rsa.dp_octets(sk, B.Octets.zeros(257n))) ++ " " ++ eqo(P.RsaPkcs1.sign(~sha256, P.RsaDigestInfo.sha256(), sk, m), B.Octets.empty()))
#|modulus bits 2048, k 256
#|pkcs1 sign is cryptography's yes
#|pkcs1 verify yes no
#|pss verify cryptography's yes no
#|pss own yes
#|oaep abc
#|pkcs1 v1.5 encryption abc
#|crt 8cc913ef5a06ee5b8cb1d53b7e4e704ea7efd317d00428e6de7e62f8bd0ffdec6781ef3cd4575adf71968de27ff0e12866e91305b6b36dc39992593005be23f0ee42e81b5f98bfd2cb3f7dc82cc6d6ef68ee33115bcce2f1d34b6033a053c9f0a170e75e42db969cac9719867e7826729eb8a82d9c2d10af37ca06563714030d3f054cfc481f96438945090f0d06f79d405e1f004f3ef38cfe97deb3a7da3585185c6ca3c4d1b125d14ff9af925c3642e5bf33d37977049b5b4ef932708bf658316ee5ee8df037ea62a70b8f629eaf20a193e86d7ad4531bf340a601785b6ebeee37e74396487a94a4a9469b862c765b40c2c70bd2940231b60cfe071223a0cf plain 8cc913ef5a06ee5b8cb1d53b7e4e704ea7efd317d00428e6de7e62f8bd0ffdec6781ef3cd4575adf71968de27ff0e12866e91305b6b36dc39992593005be23f0ee42e81b5f98bfd2cb3f7dc82cc6d6ef68ee33115bcce2f1d34b6033a053c9f0a170e75e42db969cac9719867e7826729eb8a82d9c2d10af37ca06563714030d3f054cfc481f96438945090f0d06f79d405e1f004f3ef38cfe97deb3a7da3585185c6ca3c4d1b125d14ff9af925c3642e5bf33d37977049b5b4ef932708bf658316ee5ee8df037ea62a70b8f629eaf20a193e86d7ad4531bf340a601785b6ebeee37e74396487a94a4a9469b862c765b40c2c70bd2940231b60cfe071223a0cf
#|key form yes yes
#|short forms: c5,3 yes; leading zero in n bad-format, in e bad-format; n = 0 as no bytes bad-key, as a byte bad-format
#|private short form yes, leading zero in d bad-format
#|refused out-of-range no
