# RSASSA-PSS's sign-then-verify law, for every key Rsa.private_of accepts
# whose p and q are primes (as in LAWS_prim.bend): every signature verifies,
# for every mask generation function, message and salt, and every hash whose
# digest of M' is as long as its digest of M (every hash of a fixed length:
# hd, as in LAWS.bend's pss_round_trip); where signing refuses, both sides
# refuse alike. From LAWS_prim.bend's number theory, bignum's octet-string
# laws and LAWS.bend's pss_round_trip. Proved in PROOF_pss.bend.
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../bignum/LAWS_limbs.bend as LL
import ../bignum/LAWS_fermat.bend as LF
import ./rsa.bend as R
import ./pss.bend as PS

law pss_sign_verify:
  for ~digest: B.Octets -> B.Octets
  for ~mgf: B.Octets -> Nat -> B.Octets
  for +n: N.BnNat
  for +e: N.BnNat
  for +d: N.BnNat
  for +p: N.BnNat
  for +q: N.BnNat
  for +sk: R.RsaPrivate
  for +m: B.Octets
  for +salt: B.Octets
  for +hdg: {B.Octets.len(digest(B.Octets.append(B.Octets.zeros(8n), B.Octets.append(digest(m), salt)))) == B.Octets.len(digest(m)) : Nat}
  for +hk: {R.Rsa.private_of(n, e, d, p, q) == Done{sk} : Result<&2, &2, R.RsaError, R.RsaPrivate>}
  for +hn: {LL.bnlaw.valid(n) == True{} : Bool}
  for +he: {LL.bnlaw.valid(e) == True{} : Bool}
  for +hd: {LL.bnlaw.valid(d) == True{} : Bool}
  for +hp: {LL.bnlaw.valid(p) == True{} : Bool}
  for +hq: {LL.bnlaw.valid(q) == True{} : Bool}
  for +pp: {LF.bnlaw.prime(LL.bnlaw.value(p)) == True{} : Bool}
  for +pq: {LF.bnlaw.prime(LL.bnlaw.value(q)) == True{} : Bool}
  {Result.map(&2, &2, R.RsaError, B.Octets, Bool, x => PS.RsaPss.verify(~digest, ~mgf, R.Rsa.public(sk), m, x, B.Octets.len(salt)), PS.RsaPss.sign(~digest, ~mgf, sk, m, salt)) == Result.map(&2, &2, R.RsaError, B.Octets, Bool, x => True{}, PS.RsaPss.sign(~digest, ~mgf, sk, m, salt)) : Result<&2, &2, R.RsaError, Bool>}
