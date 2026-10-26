# rsa's laws of the primitives on octet strings and of RSASSA-PKCS1-v1_5,
# for every key Rsa.private_of accepts whose p and q are primes (as in
# LAWS_prim.bend): RSAVP1 undoes RSASP1 and RSADP undoes RSAEP on octet
# strings of the modulus's length (Rsa.ep_octets and Rsa.dp_octets: OS2IP,
# the primitive, I2OSP), wherever the first succeeds; and so an
# RSASSA-PKCS1-v1_5 signature verifies, for every hash, DigestInfo prefix
# and message, wherever signing succeeds (with no hypothesis on the
# primitives: pkcs1_sign_verify_if's hs and hv hold for such keys). From
# LAWS_prim.bend's number theory (bignum's LAWS_rsa.bend) and bignum's
# octet-string laws (LAWS_octets.bend: I2OSP's bytes read back as the value,
# and I2OSP depends only on it). Proved in PROOF_sign.bend.
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../bignum/LAWS_limbs.bend as LL
import ../bignum/LAWS_fermat.bend as LF
import ./rsa.bend as R
import ./pkcs1.bend as P

# RSAVP1 after RSASP1 on octet strings (RSAEP after RSADP): wherever
# Rsa.dp_octets gives s, Rsa.ep_octets gives the input back
law ep_dp_octets:
  for +n: N.BnNat
  for +e: N.BnNat
  for +d: N.BnNat
  for +p: N.BnNat
  for +q: N.BnNat
  for +sk: R.RsaPrivate
  for +o: B.Octets
  for +hk: {R.Rsa.private_of(n, e, d, p, q) == Done{sk} : Result<&2, &2, R.RsaError, R.RsaPrivate>}
  for +hn: {LL.bnlaw.valid(n) == True{} : Bool}
  for +he: {LL.bnlaw.valid(e) == True{} : Bool}
  for +hd: {LL.bnlaw.valid(d) == True{} : Bool}
  for +hp: {LL.bnlaw.valid(p) == True{} : Bool}
  for +hq: {LL.bnlaw.valid(q) == True{} : Bool}
  for +pp: {LF.bnlaw.prime(LL.bnlaw.value(p)) == True{} : Bool}
  for +pq: {LF.bnlaw.prime(LL.bnlaw.value(q)) == True{} : Bool}
  {Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, R.Rsa.dp_octets(sk, o), s => R.Rsa.ep_octets(R.Rsa.public(sk), s)) == Result.map(&2, &2, R.RsaError, B.Octets, B.Octets, s => o, R.Rsa.dp_octets(sk, o)) : Result<&2, &2, R.RsaError, B.Octets>}

# RSADP after RSAEP on octet strings
law dp_ep_octets:
  for +n: N.BnNat
  for +e: N.BnNat
  for +d: N.BnNat
  for +p: N.BnNat
  for +q: N.BnNat
  for +sk: R.RsaPrivate
  for +o: B.Octets
  for +hk: {R.Rsa.private_of(n, e, d, p, q) == Done{sk} : Result<&2, &2, R.RsaError, R.RsaPrivate>}
  for +hn: {LL.bnlaw.valid(n) == True{} : Bool}
  for +he: {LL.bnlaw.valid(e) == True{} : Bool}
  for +hd: {LL.bnlaw.valid(d) == True{} : Bool}
  for +hp: {LL.bnlaw.valid(p) == True{} : Bool}
  for +hq: {LL.bnlaw.valid(q) == True{} : Bool}
  for +pp: {LF.bnlaw.prime(LL.bnlaw.value(p)) == True{} : Bool}
  for +pq: {LF.bnlaw.prime(LL.bnlaw.value(q)) == True{} : Bool}
  {Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, R.Rsa.ep_octets(R.Rsa.public(sk), o), c => R.Rsa.dp_octets(sk, c)) == Result.map(&2, &2, R.RsaError, B.Octets, B.Octets, c => o, R.Rsa.ep_octets(R.Rsa.public(sk), o)) : Result<&2, &2, R.RsaError, B.Octets>}

# RSASSA-PKCS1-v1_5: every signature verifies, for every hash, prefix and
# message (where signing refuses, both sides refuse alike)
law pkcs1_sign_verify:
  for ~digest: B.Octets -> B.Octets
  for +prefix: B.Octets
  for +n: N.BnNat
  for +e: N.BnNat
  for +d: N.BnNat
  for +p: N.BnNat
  for +q: N.BnNat
  for +sk: R.RsaPrivate
  for +m: B.Octets
  for +hk: {R.Rsa.private_of(n, e, d, p, q) == Done{sk} : Result<&2, &2, R.RsaError, R.RsaPrivate>}
  for +hn: {LL.bnlaw.valid(n) == True{} : Bool}
  for +he: {LL.bnlaw.valid(e) == True{} : Bool}
  for +hd: {LL.bnlaw.valid(d) == True{} : Bool}
  for +hp: {LL.bnlaw.valid(p) == True{} : Bool}
  for +hq: {LL.bnlaw.valid(q) == True{} : Bool}
  for +pp: {LF.bnlaw.prime(LL.bnlaw.value(p)) == True{} : Bool}
  for +pq: {LF.bnlaw.prime(LL.bnlaw.value(q)) == True{} : Bool}
  {Result.map(&2, &2, R.RsaError, B.Octets, Bool, x => P.RsaPkcs1.verify(~digest, prefix, R.Rsa.public(sk), m, x), P.RsaPkcs1.sign(~digest, prefix, sk, m)) == Result.map(&2, &2, R.RsaError, B.Octets, Bool, x => True{}, P.RsaPkcs1.sign(~digest, prefix, sk, m)) : Result<&2, &2, R.RsaError, Bool>}
