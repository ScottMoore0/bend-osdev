# The RSASSA-PKCS1-v1_5 instance's sign-then-verify from public-key bytes,
# for every hash, DigestInfo prefix, key rsa accepts and message, with no
# hypothesis on the scheme: rsa's pkcs1_sign_verify (LAWS_sign.bend) gives
# what LAWS.bend's rsa_pkcs1_verify_bytes_if takes as its hypothesis ha.
#
# The key is one Rsa.private_of accepts (hk), from valid integers whose p
# and q are prime (rsa's laws need both; private_of does not test
# primality), the signature is made (hs: signing refuses only where the
# message's encoding does not fit the key, and this instance then signs with
# empty bytes), and the public key survives its bytes (hf, as in LAWS.bend).
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../bignum/LAWS_limbs.bend as LL
import ../bignum/LAWS_fermat.bend as LF
import ../rsa/rsa.bend as RR
import ../rsa/keys.bend as RK
import ../rsa/pkcs1.bend as RP
import ../crypto/crypto.bend as Cr
import ../crypto/sign.bend as Sg
import ./rsa.bend as PR

law rsa_pkcs1_verify_bytes:
  for ~digest: B.Octets -> B.Octets
  for ~prefix: B.Octets
  for +n: N.BnNat
  for +e: N.BnNat
  for +d: N.BnNat
  for +p: N.BnNat
  for +q: N.BnNat
  for +sk: RR.RsaPrivate
  for +m: B.Octets
  for +hk: {RR.Rsa.private_of(n, e, d, p, q) == Done{sk} : Result<&2, &2, RR.RsaError, RR.RsaPrivate>}
  for +hn: {LL.bnlaw.valid(n) == True{} : Bool}
  for +he: {LL.bnlaw.valid(e) == True{} : Bool}
  for +hd: {LL.bnlaw.valid(d) == True{} : Bool}
  for +hp: {LL.bnlaw.valid(p) == True{} : Bool}
  for +hq: {LL.bnlaw.valid(q) == True{} : Bool}
  for +pp: {LF.bnlaw.prime(LL.bnlaw.value(p)) == True{} : Bool}
  for +pq: {LF.bnlaw.prime(LL.bnlaw.value(q)) == True{} : Bool}
  for +hs: {Result.is_done(&2, &2, RR.RsaError, B.Octets, RP.RsaPkcs1.sign(~digest, prefix, sk, m)) == True{} : Bool}
  for +hf: {PR.PkRsa.pk_of(RK.RsaKeys.public_to(RR.Rsa.public(sk))) == Done{RR.Rsa.public(sk)} : Result<&2, &2, Cr.CrError, RR.RsaPublic>}
  {Sg.CrSign.verify_bytes(~RR.RsaPublic, ~PR.PkRsa.pk_of, ~PR.PkRsa.pkcs1_verify(~digest, ~prefix), RK.RsaKeys.public_to(RR.Rsa.public(sk)), m, PR.PkRsa.pkcs1_sign(~digest, ~prefix, sk, m)) == True{} : Bool}
