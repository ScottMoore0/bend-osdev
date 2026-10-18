# Properties:
#
# * for every byte automaton (every state type and step), feeding a text in
#   any chunks finds the same matches as feeding it whole: auto_append for
#   one cut, auto_split for any list of chunks; so for KMP and the token
#   automaton (kmp_split, fsm_split), for every pattern and text;
# * bounded exhaustive agreement: over a two-letter alphabet, KMP and both
#   Boyer-Moore rules find exactly what the reference finds, for every short
#   pattern and text (exactly, and ignoring case over a and A), the text
#   whole, one byte per chunk, or cut in two anywhere (small_plain,
#   small_plain3, small_icase); and the token automaton finds what its
#   reference finds, for short token patterns and texts (small_tokens,
#   small_tokens2).
#
# Vectors: KMP, Boyer-Moore and the token automaton on small texts.
import Base
import ./textsearch.bend as T
import ./auto.bend as A
import ./kmp.bend as K
import ./bm.bend as M
import ./fsm.bend as F
import ./spec.bend as SP

# Byte automata

law auto_append:
  for ~S: Data
  for ~step: S -> U32 -> S & Bool
  for s: S
  for +pos: Nat
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  {A.ts.auto.feed(~S, ~step, s, pos, List.append(&2, U32, xs, ys)) == A.ts.auto.then(~S, ~step, A.ts.auto.feed(~S, ~step, s, pos, xs), Nat.add(pos, List.length(&2, U32, xs)), ys) : S & List<&2, Nat>}

law auto_split:
  for ~S: Data
  for ~step: S -> U32 -> S & Bool
  for s: S
  for +pos: Nat
  for cs: List<&2, List<&2, U32>>
  {A.ts.auto.run(~S, ~step, s, pos, cs) == A.ts.auto.ends(~S, ~step, s, pos, T.ts.concat(cs)) : List<&2, Nat>}

law kmp_split:
  for +icase: Bool
  for +p: List<&2, U32>
  for cs: List<&2, List<&2, U32>>
  {K.ts.kmp.search(icase, p, cs) == K.ts.kmp.ends(icase, p, T.ts.concat(cs)) : List<&2, Nat>}

law fsm_split:
  for +tks: List<&2, F.TsToken>
  for cs: List<&2, List<&2, U32>>
  {F.ts.fsm.search(tks, cs) == F.ts.fsm.ends(tks, T.ts.concat(cs)) : List<&2, Nat>}

# Bounded exhaustive agreement with the references (the checker bounds the
# work of one law, so each covers a slice; check.bend runs far larger bounds)

# every pattern of 1 or 2 bytes, every text of up to 4
law small_plain:
  {SP.ts.spec.plain(False{}, SP.ts.spec.upto(2n, [0, 1], 1n), SP.ts.spec.upto(5n, [0, 1], 0n)) == True{} : Bool}

# every pattern of 3 bytes starting with 0 (those starting with 1 are the
# same up to renaming the bytes), every text of 4
law small_plain3:
  {SP.ts.spec.plain(False{}, SP.ts.spec.prepend(0, SP.ts.spec.words([0, 1], 2n)), SP.ts.spec.words([0, 1], 4n)) == True{} : Bool}

# ignoring case: every pattern of 1 or 2 bytes of A and a, every text of up
# to 3
law small_icase:
  {SP.ts.spec.plain(True{}, SP.ts.spec.upto(2n, [65, 97], 1n), SP.ts.spec.upto(4n, [65, 97], 0n)) == True{} : Bool}

# every single token (byte 0, byte 1 or any byte; once, perhaps, any number,
# one or more), every text of up to 4
law small_tokens:
  {SP.ts.spec.tokens(SP.ts.spec.ones(SP.ts.spec.toks([F.TsIs{0}, F.TsIs{1}, F.TsAnyByte{}])), SP.ts.spec.upto(5n, [0, 1], 0n)) == True{} : Bool}

# two tokens: byte 0 or any byte, then byte 1, in every count; every text of
# up to 3
law small_tokens2:
  {SP.ts.spec.tokens(SP.ts.spec.pairs(SP.ts.spec.toks([F.TsIs{0}, F.TsAnyByte{}]), SP.ts.spec.toks([F.TsIs{1}])), SP.ts.spec.upto(4n, [0, 1], 0n)) == True{} : Bool}

# Vectors

law vec_kmp:
  {K.ts.kmp.search(False{}, [1, 2, 1], [[0, 1, 2], [1, 2], [1, 0]]) == [4n, 6n] : List<&2, Nat>}

law vec_bm:
  {(M.ts.bm.search(False{}, M.TsGoodSuffix{}, [1, 2, 1], [[0, 1, 2], [1, 2], [1, 0]]), M.ts.bm.search(True{}, M.TsHorspool{}, [65, 98], [[97], [66, 97, 98]])) == ([4n, 6n], [2n, 4n]) : List<&2, Nat> & List<&2, Nat>}

law vec_fsm:
  {F.ts.fsm.search([F.TsToken{F.TsIs{1}, F.TsOne{}}, F.TsToken{F.TsRange{5, 9}, F.TsPlus{}}], [[1, 5], [6, 1], [9, 1]]) == [2n, 3n, 5n] : List<&2, Nat>}
