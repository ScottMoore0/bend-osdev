# Fermat's little theorem, on Nat, for every input: for a prime p and every
# a, a^p = a (mod p). Primality is stated plainly: p >= 2 and no d with
# 2 <= d < p divides p (bnlaw.prime). Proved in PROOF_fermat.bend (by the
# binomial theorem: p divides C(p, k) for 0 < k < p, so (a + 1)^p = a^p + 1
# (mod p), and induction on a).
import Base

# whether no d among d0, d0 + 1, ..., d0 + k - 1 divides p
def bnlaw.nodiv(k: Nat, +p: Nat, +d0: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+j:
      Bool.and(Bool.not(Nat.is_eq(Nat.mod(p, d0), 0n)), bnlaw.nodiv(j, p, 1n+d0))

# p is prime: p >= 2, and no d with 2 <= d < p divides p
def bnlaw.prime(+p: Nat) -> Bool:
  Bool.and(Nat.is_lt(1n, p), bnlaw.nodiv(Nat.sub(p, 2n), p, 2n))

law fermat:
  for +p: Nat
  for +a: Nat
  for hp: {bnlaw.prime(p) == True{} : Bool}
  {Nat.mod(Nat.pow(a, p), p) == Nat.mod(a, p) : Nat}

# the predicate on small values
law prime_vector:
  {[bnlaw.prime(2n), bnlaw.prime(7n), bnlaw.prime(9n), bnlaw.prime(1n), bnlaw.prime(0n)] == [True{}, True{}, False{}, False{}, False{}] : List<&2, Bool>}
