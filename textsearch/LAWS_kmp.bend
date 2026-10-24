# Properties of Knuth-Morris-Pratt, for every input:
#
# * kmp_ref: KMP finds exactly what the reference finds (naive.bend's
#   ts.naive.ends: the pattern tried at every offset), for every pattern
#   (exactly or ignoring case) and every text;
# * kmp_search_ref: so does KMP fed the text in any chunks, for every
#   chunking.
#
# The proofs (PROOF_kmp.bend) rest on a theory of borders: the set of the
# pattern's prefixes that a text read so far ends with is, after reading
# the pattern's own first k bytes, the set of borders of those k bytes; the
# prefix table names the longest proper one, so following the table from
# the current prefix visits exactly the borders, and KMP's state, one
# number, stands for the whole set.
import Base
import ./textsearch.bend as T
import ./kmp.bend as K
import ./naive.bend as V

law kmp_ref:
  for +icase: Bool
  for +p: List<&2, U32>
  for xs: List<&2, U32>
  {K.ts.kmp.ends(icase, p, xs) == V.ts.naive.ends(icase, p, xs) : List<&2, Nat>}

law kmp_search_ref:
  for +icase: Bool
  for +p: List<&2, U32>
  for cs: List<&2, List<&2, U32>>
  {K.ts.kmp.search(icase, p, cs) == V.ts.naive.ends(icase, p, T.ts.concat(cs)) : List<&2, Nat>}
