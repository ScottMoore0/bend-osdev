# Where the search for a short name's numeric tail starts: FatAlias.first_tail
# (alias.bend), the smallest n from 1 that no taken name has as its tail.
# Every tail below it is taken, for every basis name (base and extension)
# and every list of taken names; FatAlias.make's search for a free tail
# starts there and goes up one at a time to the first free one, so the tail
# it chooses is the smallest free one.
import Base
import ../bytes/bytes.bend as B
import ./alias.bend as L

law first_tail_least:
  for +base: List<&2, U32>
  for +ext: List<&2, U32>
  for +taken: List<&2, B.Octets>
  for +k: Nat
  for h1: {Nat.is_le(1n, k) == True{} : Bool}
  for h2: {Nat.is_lt(k, L.FatAlias.first_tail(base, ext, taken)) == True{} : Bool}
  {L.FatAlias.taken(L.FatAlias.with_tail(base, ext, k), taken) == True{} : Bool}
