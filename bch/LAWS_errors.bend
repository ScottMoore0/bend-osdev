# The (15,7) code (Bch.bch15_7, t = 2): every pattern of at most two
# flipped bits is corrected, for every message of 7 bits. Properties, for
# every input:
#   * a codeword with any bits flipped (at any positions) has the
#     syndromes of the zero word with the same bits flipped;
#   * so the decoder treats a codeword with bits flipped as it treats the
#     flips alone: whenever the zero word with those bits flipped decodes
#     to the zero message, every codeword with them flipped decodes to its
#     own message;
#   * every received word that is a codeword with any two of its bits
#     flipped (two errors, or none when the two indexes are equal; an
#     index past the end flips nothing) decodes to the message.
import Base
import ./code.bend as C
import ./encode.bend as E
import ./syndrome.bend as S
import ./bch.bend as D

law small15_syndromes_shift:
  for +m: List<&2, Bool>
  for +n7: {List.length(&2, Bool, m) == 7n : Nat}
  for +ps: List<&2, U32>
  {S.Bch.syndromes(C.Bch.bch15_7(), D.Bch.flip(ps, E.Bch.codeword(C.Bch.bch15_7(), m))) == S.Bch.syndromes(C.Bch.bch15_7(), D.Bch.flip(ps, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}])) : List<&2, U32>}

law small15_decode_shift:
  for +m: List<&2, Bool>
  for +n7: {List.length(&2, Bool, m) == 7n : Nat}
  for +ps: List<&2, U32>
  for zero: {D.Bch.decode_bits(C.Bch.bch15_7(), D.Bch.flip(ps, [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}])) == Done{[False{}, False{}, False{}, False{}, False{}, False{}, False{}]} : Result<&2, &2, E.BchError, List<&2, Bool>>}
  {D.Bch.decode_bits(C.Bch.bch15_7(), D.Bch.flip(ps, E.Bch.codeword(C.Bch.bch15_7(), m))) == Done{m} : Result<&2, &2, E.BchError, List<&2, Bool>>}

law small15_two_errors:
  for +m: List<&2, Bool>
  for +n7: {List.length(&2, Bool, m) == 7n : Nat}
  for +i: Nat
  for +j: Nat
  {D.Bch.decode_bits(C.Bch.bch15_7(), D.Bch.flip_at(D.Bch.flip_at(E.Bch.codeword(C.Bch.bch15_7(), m), i), j)) == Done{m} : Result<&2, &2, E.BchError, List<&2, Bool>>}
