# bend-osdev-kitbytes: an adapter between bend-osdev's Octets and bend-kit's
# Bytes (bend-kit-bytes, an array-backed buffer packed four bytes to a word).
#
# The core bend-osdev packages never depend on bend-kit's types; a program
# that uses both converts at its edges, here.
import Base
import ../bytes/bytes.bend as B
import bend-kit-bytes@0.3.2.0/bytes.bend as KB

def of_octets.go(xs: List<&2, U32>, b: KB.Bytes, +i: U32) -> KB.Bytes:
  match xs:
    case Nil{}:
      b
    case Con{h, t}:
      of_octets.go(t, KB.set(b, i, h), U32.add(i, 1))

# a bend-kit buffer holding the bytes of o
def of_octets(o: B.Octets) -> KB.Bytes:
  +xs = B.Octets.to_list(o)
  of_octets.go(xs, KB.new(U32.from_nat(B.len(xs))), 0)

def to_octets.byte(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{v}:
      v
    case None{}:
      0

def to_octets.push(r: KB.Bytes & Maybe<&2, U32>, acc: List<&2, U32>) -> KB.Bytes & List<&2, U32>:
  (b, m) = r
  (b, Con{to_octets.byte(m), acc})

# reads bytes k-1 down to 0, so the list is built front first
def to_octets.go(+k: Nat, r: KB.Bytes & List<&2, U32>) -> KB.Bytes & List<&2, U32>:
  match k:
    case 0n:
      r
    case 1n+p:
      (b, acc) = r
      to_octets.go(p, to_octets.push(KB.get(b, U32.from_nat(p)), acc))

def to_octets.fin(r: KB.Bytes & List<&2, U32>) -> KB.Bytes & B.Octets:
  (b, xs) = r
  (b, B.Octets.of_list(xs))

def to_octets.start(r: KB.Bytes & U32) -> KB.Bytes & B.Octets:
  (b, n) = r
  to_octets.fin(to_octets.go(U32.to_nat(n), (b, Nil{})))

# the bytes of a bend-kit buffer, handed back beside the buffer (it is affine)
def to_octets(b: KB.Bytes) -> KB.Bytes & B.Octets:
  to_octets.start(KB.length(b))

# convert there and back, dropping the buffer: the identity, by the laws
def round_trip.fin(r: KB.Bytes & B.Octets) -> B.Octets:
  (b, o) = r
  o

def round_trip(o: B.Octets) -> B.Octets:
  round_trip.fin(to_octets(of_octets(o)))
