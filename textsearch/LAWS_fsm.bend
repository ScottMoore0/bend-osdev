# Properties of the token automaton, for every input:
#
# * fsm_ref: the automaton (the set of token positions reached, moved a
#   byte at a time) finds exactly what the backtracking reference finds
#   (fsm.bend's ts.fsm.naive: every offset where some non-empty run of
#   bytes ending there matches the tokens), for every token pattern and
#   every text;
# * fsm_search_ref: so does the automaton fed the text in any chunks, for
#   every chunking.
#
# The proofs (PROOF_fsm.bend) follow apparmor's glob_run: what a set of
# positions accepts is some active position's tokens matching the rest
# exactly, and each pass of the step (closing over optional tokens,
# reading a byte) is shown to take one such meaning to the next.
import Base
import ./textsearch.bend as T
import ./fsm.bend as F

law fsm_ref:
  for +tks: List<&2, F.TsToken>
  for +xs: List<&2, U32>
  {F.ts.fsm.ends(tks, xs) == F.ts.fsm.naive(tks, xs) : List<&2, Nat>}

law fsm_search_ref:
  for +tks: List<&2, F.TsToken>
  for +cs: List<&2, List<&2, U32>>
  {F.ts.fsm.search(tks, cs) == F.ts.fsm.naive(tks, T.ts.concat(cs)) : List<&2, Nat>}
