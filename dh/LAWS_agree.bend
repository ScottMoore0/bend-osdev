# dh's agreement law, for every group and pair of keys: the two parties
# compute the same shared secret, (g^y)^x = (g^x)^y mod p, unconditionally
# (LAWS.bend's agree_if takes that equation as a hypothesis). Proved in
# PROOF_agree.bend from bignum's exp_exp_comm (bignum/LAWS_mont.bend).
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ../bignum/LAWS_limbs.bend as NL
import ./dh.bend as D

# For a group (p, g, q) whose p is valid, odd and above 1 (every safe prime
# is), a valid g, and valid private keys x and y: the primitive on the
# peer's public key gives the same result on both sides (the same bytes,
# or the same refusal)
law agree:
  for +p: N.BnNat
  for +g: N.BnNat
  for +q: N.BnNat
  for +x: N.BnNat
  for +y: N.BnNat
  for +hp: {NL.bnlaw.valid(p) == True{} : Bool}
  for +hpo: {N.BnNat.is_odd(p) == True{} : Bool}
  for +hp1: {Nat.is_lt(1n, NL.bnlaw.value(p)) == True{} : Bool}
  for +hg: {NL.bnlaw.valid(g) == True{} : Bool}
  for +hx: {NL.bnlaw.valid(x) == True{} : Bool}
  for +hy: {NL.bnlaw.valid(y) == True{} : Bool}
  {D.Dh.primitive(D.DhGroup{p, g, q}, x, D.Dh.public(D.DhGroup{p, g, q}, y)) == D.Dh.primitive(D.DhGroup{p, g, q}, y, D.Dh.public(D.DhGroup{p, g, q}, x)) : Result<&2, &2, D.DhError, B.Octets>}
