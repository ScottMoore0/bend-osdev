# The KDF interface's length and prefix laws for HKDF (hkdf.bend), over every
# hash whose digest has its digest size: in a pair of their own
# (CONVENTIONS.md, Laws), their proofs resting on bytes' laws only.
#
# HKDF's output is T(1) .. T(N) cut to the length asked for, N the ceiling
# of len / dsize, each T(i) an HMAC tag, so how long it is depends on how
# long the hash's digests are. The laws take that property of the hash as
# the hypothesis hd on lists of inputs, as cipher-modes' laws take a
# cipher's (README.md, "How the laws are stated"): for every list of byte
# strings, each one's digest has dsize bytes. A hash whose digest has dsize
# bytes for every input (its length law) gives it for every list by
# induction.
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr
import ./hkdf.bend as Hk

# the length of each input's digest, and n for each input
def crhk.dlens(~digest: B.Octets -> B.Octets, xs: List<&2, B.Octets>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{B.Octets.len(digest(x)), crhk.dlens(~digest, t)}

def crhk.reps(+n: Nat, xs: List<&2, B.Octets>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{n, crhk.reps(n, t)}

# length: a derivation that succeeds gives exactly the length asked for,
# for every hash with hd, input keying material, salt, context and length
law hkdf_length:
  for ~bsize: Nat
  for ~dsize: Nat
  for ~digest: B.Octets -> B.Octets
  for hd: @xs: List<&2, B.Octets> -> {crhk.dlens(~digest, xs) == crhk.reps(dsize, xs) : List<&2, Nat>}
  for +ikm: B.Octets
  for +salt: B.Octets
  for +info: B.Octets
  for +n: Nat
  {Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => B.Octets.len(o), Hk.CrHkdf.derive(~bsize, ~dsize, ~digest, ikm, salt, info, n)) == Result.map(&2, &2, Cr.CrError, B.Octets, Nat, o => n, Hk.CrHkdf.derive(~bsize, ~dsize, ~digest, ikm, salt, info, n)) : Result<&2, &2, Cr.CrError, Nat>}

# prefix: when a derivation of n + j bytes succeeds, the derivation of n
# bytes from the same inputs succeeds and is its first n bytes
law hkdf_prefix:
  for ~bsize: Nat
  for ~dsize: Nat
  for ~digest: B.Octets -> B.Octets
  for hd: @xs: List<&2, B.Octets> -> {crhk.dlens(~digest, xs) == crhk.reps(dsize, xs) : List<&2, Nat>}
  for +ikm: B.Octets
  for +salt: B.Octets
  for +info: B.Octets
  for +n: Nat
  for +j: Nat
  {Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, o => B.Octets.take(n, o), Hk.CrHkdf.derive(~bsize, ~dsize, ~digest, ikm, salt, info, Nat.add(n, j))) == Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Hk.CrHkdf.derive(~bsize, ~dsize, ~digest, ikm, salt, info, Nat.add(n, j)), o => Hk.CrHkdf.derive(~bsize, ~dsize, ~digest, ikm, salt, info, n)) : Result<&2, &2, Cr.CrError, B.Octets>}
