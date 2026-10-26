# bend-osdev-bignum's octet-string laws, for every input: OS2IP
# (BnNat.of_octets) makes a valid number; I2OSP (BnNat.to_octets) to k
# bytes gives k bytes, which OS2IP reads back as the number's value; I2OSP
# depends only on the value (zero limbs on top change nothing); and so I2OSP
# of a number gives back every byte string whose OS2IP has its value, at
# that string's length. With bignum's octets_round_trip (LAWS.bend) these
# are what RSA's octet-string primitives need (rsa's LAWS_octets.bend).
# Proved in PROOF_octets.bend.
import Base
import ../bytes/bytes.bend as B
import ./bignum.bend as N
import ./LAWS_limbs.bend as LL

law of_octets_valid:
  for +o: B.Octets
  {LL.bnlaw.valid(N.BnNat.of_octets(o)) == True{} : Bool}

law to_octets_len:
  for +x: N.BnNat
  for +k: Nat
  for +o: B.Octets
  for +h: {N.BnNat.to_octets(x, k) == Some{o} : Maybe<&2, B.Octets>}
  {B.Octets.len(o) == k : Nat}

law to_octets_value:
  for +x: N.BnNat
  for +k: Nat
  for +o: B.Octets
  for +hx: {LL.bnlaw.valid(x) == True{} : Bool}
  for +h: {N.BnNat.to_octets(x, k) == Some{o} : Maybe<&2, B.Octets>}
  {LL.bnlaw.value(N.BnNat.of_octets(o)) == LL.bnlaw.value(x) : Nat}

law to_octets_eq:
  for +x: N.BnNat
  for +y: N.BnNat
  for +k: Nat
  for +hx: {LL.bnlaw.valid(x) == True{} : Bool}
  for +hy: {LL.bnlaw.valid(y) == True{} : Bool}
  for +e: {LL.bnlaw.value(x) == LL.bnlaw.value(y) : Nat}
  {N.BnNat.to_octets(x, k) == N.BnNat.to_octets(y, k) : Maybe<&2, B.Octets>}

law to_octets_of_value:
  for +x: N.BnNat
  for +o: B.Octets
  for +hx: {LL.bnlaw.valid(x) == True{} : Bool}
  for +e: {LL.bnlaw.value(N.BnNat.of_octets(o)) == LL.bnlaw.value(x) : Nat}
  {N.BnNat.to_octets(x, B.Octets.len(o)) == Some{o} : Maybe<&2, B.Octets>}
