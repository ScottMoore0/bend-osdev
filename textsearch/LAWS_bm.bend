# Properties of Boyer-Moore, for every input:
#
# * bm_ref: Boyer-Moore, with either shift rule (Horspool's bad-character
#   rule, or the default: the larger of it and the strong good-suffix
#   shift), finds exactly what the reference finds (naive.bend's
#   ts.naive.ends), for every pattern, exactly or ignoring case, and every
#   text;
# * bm_split: Boyer-Moore fed the text in any chunks (keeping the last
#   m - 1 bytes between them) finds exactly what it finds in the text
#   whole, for every chunking; bm_search_ref: so it finds what the
#   reference finds.
#
# The proofs (PROOF_bm.bend) show every shift safe: no window it skips
# holds the pattern. Horspool's, because the byte under the pattern's last
# position does not occur at the pattern positions it skips over; the
# good-suffix shift, because each skipped shift either misaligns the
# matched suffix with the pattern or puts the same byte under the
# mismatch; after a match, because each skipped shift is not a period.
import Base
import ./textsearch.bend as T
import ./bm.bend as M
import ./naive.bend as V

law bm_ref:
  for +icase: Bool
  for +rule: M.TsBmRule
  for +p: List<&2, U32>
  for +xs: List<&2, U32>
  {M.ts.bm.ends(icase, rule, p, xs) == V.ts.naive.ends(icase, p, xs) : List<&2, Nat>}

law bm_split:
  for +icase: Bool
  for +rule: M.TsBmRule
  for +p: List<&2, U32>
  for +cs: List<&2, List<&2, U32>>
  {M.ts.bm.search(icase, rule, p, cs) == M.ts.bm.ends(icase, rule, p, T.ts.concat(cs)) : List<&2, Nat>}

law bm_search_ref:
  for +icase: Bool
  for +rule: M.TsBmRule
  for +p: List<&2, U32>
  for +cs: List<&2, List<&2, U32>>
  {M.ts.bm.search(icase, rule, p, cs) == V.ts.naive.ends(icase, p, T.ts.concat(cs)) : List<&2, Nat>}
