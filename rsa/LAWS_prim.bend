# rsa's laws of the primitives, for every key Rsa.private_of accepts whose
# p and q are primes: RSAVP1 undoes RSASP1 and RSADP undoes RSAEP, with
# RSADP (and RSASP1) by the Chinese remainder theorem from the key's dP, dQ
# and qInv (RFC 8017, 5.1.2 step 2.b) and in the first form (n, d), and the
# two forms of RSADP agree; for every message representative below n. The
# integers are bignum's (valid: every number bignum's public defs make is,
# bignum's LAWS_limbs.bend), and primality is bignum's bnlaw.prime of their
# values (Rsa.private_of does not test it; key generation's Miller-Rabin
# does). The number theory is bignum's LAWS_rsa.bend: rsa_nat, rsa_nat_rev
# and crt_exp_nat, from the checks Rsa.private_of makes (n = p q odd, d e = 1
# modulo p - 1 and q - 1, q qInv = 1 mod p). Proved in PROOF_prim.bend.
import Base
import ../bignum/bignum.bend as N
import ../bignum/LAWS_limbs.bend as LL
import ../bignum/LAWS_fermat.bend as LF
import ./rsa.bend as R

# RSAVP1(RSASP1(m)) = m, RSASP1 by the CRT
law vp1_sp1:
  for +n: N.BnNat
  for +e: N.BnNat
  for +d: N.BnNat
  for +p: N.BnNat
  for +q: N.BnNat
  for +sk: R.RsaPrivate
  for +m: N.BnNat
  for +hk: {R.Rsa.private_of(n, e, d, p, q) == Done{sk} : Result<&2, &2, R.RsaError, R.RsaPrivate>}
  for +hn: {LL.bnlaw.valid(n) == True{} : Bool}
  for +he: {LL.bnlaw.valid(e) == True{} : Bool}
  for +hd: {LL.bnlaw.valid(d) == True{} : Bool}
  for +hp: {LL.bnlaw.valid(p) == True{} : Bool}
  for +hq: {LL.bnlaw.valid(q) == True{} : Bool}
  for +pp: {LF.bnlaw.prime(LL.bnlaw.value(p)) == True{} : Bool}
  for +pq: {LF.bnlaw.prime(LL.bnlaw.value(q)) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hlt: {N.BnNat.is_lt(m, n) == True{} : Bool}
  {Result.map(&2, &2, R.RsaError, N.BnNat, Nat, x => LL.bnlaw.value(x), Result.bind(&2, &2, R.RsaError, N.BnNat, N.BnNat, R.Rsa.sp1(sk, m), s => R.Rsa.vp1(R.Rsa.public(sk), s))) == Done{LL.bnlaw.value(m)} : Result<&2, &2, R.RsaError, Nat>}

# RSADP(RSAEP(m)) = m, RSADP by the CRT
law dp_ep:
  for +n: N.BnNat
  for +e: N.BnNat
  for +d: N.BnNat
  for +p: N.BnNat
  for +q: N.BnNat
  for +sk: R.RsaPrivate
  for +m: N.BnNat
  for +hk: {R.Rsa.private_of(n, e, d, p, q) == Done{sk} : Result<&2, &2, R.RsaError, R.RsaPrivate>}
  for +hn: {LL.bnlaw.valid(n) == True{} : Bool}
  for +he: {LL.bnlaw.valid(e) == True{} : Bool}
  for +hd: {LL.bnlaw.valid(d) == True{} : Bool}
  for +hp: {LL.bnlaw.valid(p) == True{} : Bool}
  for +hq: {LL.bnlaw.valid(q) == True{} : Bool}
  for +pp: {LF.bnlaw.prime(LL.bnlaw.value(p)) == True{} : Bool}
  for +pq: {LF.bnlaw.prime(LL.bnlaw.value(q)) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hlt: {N.BnNat.is_lt(m, n) == True{} : Bool}
  {Result.map(&2, &2, R.RsaError, N.BnNat, Nat, x => LL.bnlaw.value(x), Result.bind(&2, &2, R.RsaError, N.BnNat, N.BnNat, R.Rsa.ep(R.Rsa.public(sk), m), c => R.Rsa.dp(sk, c))) == Done{LL.bnlaw.value(m)} : Result<&2, &2, R.RsaError, Nat>}

# the same in the first form (n, d): RSAEP(RSADP(m)) = m and RSADP(RSAEP(m))
# = m
law ep_dp_plain:
  for +n: N.BnNat
  for +e: N.BnNat
  for +d: N.BnNat
  for +p: N.BnNat
  for +q: N.BnNat
  for +sk: R.RsaPrivate
  for +m: N.BnNat
  for +hk: {R.Rsa.private_of(n, e, d, p, q) == Done{sk} : Result<&2, &2, R.RsaError, R.RsaPrivate>}
  for +hn: {LL.bnlaw.valid(n) == True{} : Bool}
  for +he: {LL.bnlaw.valid(e) == True{} : Bool}
  for +hd: {LL.bnlaw.valid(d) == True{} : Bool}
  for +hp: {LL.bnlaw.valid(p) == True{} : Bool}
  for +hq: {LL.bnlaw.valid(q) == True{} : Bool}
  for +pp: {LF.bnlaw.prime(LL.bnlaw.value(p)) == True{} : Bool}
  for +pq: {LF.bnlaw.prime(LL.bnlaw.value(q)) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hlt: {N.BnNat.is_lt(m, n) == True{} : Bool}
  {Result.map(&2, &2, R.RsaError, N.BnNat, Nat, x => LL.bnlaw.value(x), Result.bind(&2, &2, R.RsaError, N.BnNat, N.BnNat, R.Rsa.dp_plain(sk, m), s => R.Rsa.ep(R.Rsa.public(sk), s))) == Done{LL.bnlaw.value(m)} : Result<&2, &2, R.RsaError, Nat>}

law dp_plain_ep:
  for +n: N.BnNat
  for +e: N.BnNat
  for +d: N.BnNat
  for +p: N.BnNat
  for +q: N.BnNat
  for +sk: R.RsaPrivate
  for +m: N.BnNat
  for +hk: {R.Rsa.private_of(n, e, d, p, q) == Done{sk} : Result<&2, &2, R.RsaError, R.RsaPrivate>}
  for +hn: {LL.bnlaw.valid(n) == True{} : Bool}
  for +he: {LL.bnlaw.valid(e) == True{} : Bool}
  for +hd: {LL.bnlaw.valid(d) == True{} : Bool}
  for +hp: {LL.bnlaw.valid(p) == True{} : Bool}
  for +hq: {LL.bnlaw.valid(q) == True{} : Bool}
  for +pp: {LF.bnlaw.prime(LL.bnlaw.value(p)) == True{} : Bool}
  for +pq: {LF.bnlaw.prime(LL.bnlaw.value(q)) == True{} : Bool}
  for +hm: {LL.bnlaw.valid(m) == True{} : Bool}
  for +hlt: {N.BnNat.is_lt(m, n) == True{} : Bool}
  {Result.map(&2, &2, R.RsaError, N.BnNat, Nat, x => LL.bnlaw.value(x), Result.bind(&2, &2, R.RsaError, N.BnNat, N.BnNat, R.Rsa.ep(R.Rsa.public(sk), m), c => R.Rsa.dp_plain(sk, c))) == Done{LL.bnlaw.value(m)} : Result<&2, &2, R.RsaError, Nat>}

# RSADP by the CRT has the value of the first form, c^d mod n
law dp_crt_plain:
  for +n: N.BnNat
  for +e: N.BnNat
  for +d: N.BnNat
  for +p: N.BnNat
  for +q: N.BnNat
  for +sk: R.RsaPrivate
  for +c: N.BnNat
  for +hk: {R.Rsa.private_of(n, e, d, p, q) == Done{sk} : Result<&2, &2, R.RsaError, R.RsaPrivate>}
  for +hn: {LL.bnlaw.valid(n) == True{} : Bool}
  for +he: {LL.bnlaw.valid(e) == True{} : Bool}
  for +hd: {LL.bnlaw.valid(d) == True{} : Bool}
  for +hp: {LL.bnlaw.valid(p) == True{} : Bool}
  for +hq: {LL.bnlaw.valid(q) == True{} : Bool}
  for +pp: {LF.bnlaw.prime(LL.bnlaw.value(p)) == True{} : Bool}
  for +pq: {LF.bnlaw.prime(LL.bnlaw.value(q)) == True{} : Bool}
  for +hc: {LL.bnlaw.valid(c) == True{} : Bool}
  for +hlt: {N.BnNat.is_lt(c, n) == True{} : Bool}
  {Result.map(&2, &2, R.RsaError, N.BnNat, Nat, x => LL.bnlaw.value(x), R.Rsa.dp(sk, c)) == Result.map(&2, &2, R.RsaError, N.BnNat, Nat, x => LL.bnlaw.value(x), R.Rsa.dp_plain(sk, c)) : Result<&2, &2, R.RsaError, Nat>}
