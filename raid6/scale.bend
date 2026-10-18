# bend-osdev-raid6, scaling a block: every byte of a block multiplied by
# the same element of GF(2^8) (H. Peter Anvin, "The mathematics of RAID-6",
# section 2: a constant, "same value across every data byte", times a
# vector). The field is a parameter (bend-osdev-gf's Gf8Field).
#
# The work is done on the block's byte list, tail-recursively, so blocks of
# any length run on both of Bend's lanes; r6.scale.list is the structural
# form the proofs reason about, and PROOF.bend proves the two equal.
import Base
import ../bytes/bytes.bend as B
import ../gf/gf.bend as G

# c * x for every byte x (internal, structural)
def r6.scale.list(+f: G.Gf8Field, +c: U32, xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{G.Gf8.mul(f, c, x), r6.scale.list(f, c, t)}

# the same, tail-recursive, the result kept reversed in acc (internal)
def r6.scale.go(xs: List<&2, U32>, +f: G.Gf8Field, +c: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      B.rev_onto(acc, Nil{})
    case Con{x, t}:
      r6.scale.go(t, f, c, Con{G.Gf8.mul(f, c, x), acc})

# every byte of b multiplied by c in the field f
def Raid6.scale(+f: G.Gf8Field, +c: U32, b: B.Octets) -> B.Octets:
  B.Octets.of_list(r6.scale.go(B.Octets.to_list(b), f, c, Nil{}))
