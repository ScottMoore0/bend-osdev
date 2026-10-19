# Properties, for every input:
#   * every code: encoding at most n - deg(g) data bits gives their
#     codeword, which begins with the data bits (systematic encoding);
#   * the (7,4) code (Bch.bch7_4, t = 1), for every message of up to 4
#     bits (shortened or not): its codeword's syndromes are zero, and the
#     codeword decodes to the message with any one bit flipped, or none;
#   * the (15,7) code (Bch.bch15_7, t = 2), for every message of up to 7
#     bits: its codeword's syndromes are zero, and the codeword decodes to
#     the message.
# Vectors: the generators of the small codes (Ho's (15,7) and (15,5)
# generators, "BCH Codes", section 2), Ho's decoding example (section 4),
# the NAND codes' parity sizes, the bit orders, and the refusals.
import Base
import ../bytes/bytes.bend as B
import ../gf/gfm.bend as M
import ./code.bend as C
import ./bits.bend as T
import ./encode.bend as E
import ./syndrome.bend as S
import ./bch.bend as D

# Every code

law encode_short:
  for +c: C.BchCode
  for +m: List<&2, Bool>
  for short: {Nat.is_le(Nat.add(List.length(&2, Bool, m), C.Bch.parity_bits(c)), U32.to_nat(C.Bch.n(c))) == True{} : Bool}
  {E.Bch.encode_bits(c, m) == Done{E.Bch.codeword(c, m)} : Result<&2, &2, E.BchError, List<&2, Bool>>}

law codeword_message:
  for +c: C.BchCode
  for +m: List<&2, Bool>
  {List.take(&2, Bool, E.Bch.codeword(c, m), List.length(&2, Bool, m)) == m : List<&2, Bool>}

# The (7,4) code, t = 1

law small7_syndromes:
  for m: List<&2, Bool>
  for short: {Nat.is_le(List.length(&2, Bool, m), 4n) == True{} : Bool}
  {S.Bch.syndromes(C.Bch.bch7_4(), E.Bch.codeword(C.Bch.bch7_4(), m)) == [0, 0] : List<&2, U32>}

law small7_roundtrip:
  for +m: List<&2, Bool>
  for short: {Nat.is_le(List.length(&2, Bool, m), 4n) == True{} : Bool}
  for some: {Nat.is_lt(0n, List.length(&2, Bool, m)) == True{} : Bool}
  {D.Bch.decode_bits(C.Bch.bch7_4(), E.Bch.codeword(C.Bch.bch7_4(), m)) == Done{m} : Result<&2, &2, E.BchError, List<&2, Bool>>}

# any one of the codeword's m + 3 bits flipped
law small7_error:
  for +m: List<&2, Bool>
  for i: Nat
  for short: {Nat.is_le(List.length(&2, Bool, m), 4n) == True{} : Bool}
  for some: {Nat.is_lt(0n, List.length(&2, Bool, m)) == True{} : Bool}
  for inside: {Nat.is_lt(i, Nat.add(List.length(&2, Bool, m), 3n)) == True{} : Bool}
  {D.Bch.decode_bits(C.Bch.bch7_4(), D.Bch.flip_at(E.Bch.codeword(C.Bch.bch7_4(), m), i)) == Done{m} : Result<&2, &2, E.BchError, List<&2, Bool>>}

# The (15,7) code, t = 2

law small15_syndromes:
  for m: List<&2, Bool>
  for short: {Nat.is_le(List.length(&2, Bool, m), 7n) == True{} : Bool}
  {S.Bch.syndromes(C.Bch.bch15_7(), E.Bch.codeword(C.Bch.bch15_7(), m)) == [0, 0, 0, 0] : List<&2, U32>}

law small15_roundtrip:
  for +m: List<&2, Bool>
  for short: {Nat.is_le(List.length(&2, Bool, m), 7n) == True{} : Bool}
  for some: {Nat.is_lt(0n, List.length(&2, Bool, m)) == True{} : Bool}
  {D.Bch.decode_bits(C.Bch.bch15_7(), E.Bch.codeword(C.Bch.bch15_7(), m)) == Done{m} : Result<&2, &2, E.BchError, List<&2, Bool>>}

# Vectors

# g(X) = 1 + X + X^3
law v_generator7_4:
  {C.Bch.generator(C.Bch.bch7_4()) == [True{}, True{}, False{}, True{}] : List<&2, Bool>}

# Ho, section 2: Q(x) = (1 + x + x^4)(1 + x + x^2 + x^3 + x^4)
# = 1 + x^4 + x^6 + x^7 + x^8
law v_generator15_7:
  {C.Bch.generator(C.Bch.bch15_7()) == [True{}, False{}, False{}, False{}, True{}, False{}, True{}, True{}, True{}] : List<&2, Bool>}

# Ho, section 2: Q(x) = (1 + x + x^4)(1 + x + x^2 + x^3 + x^4)(1 + x + x^2)
# = 1 + x + x^2 + x^4 + x^5 + x^8 + x^10
law v_generator15_5:
  {C.Bch.generator(C.Bch.bch15_5()) == [True{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}, True{}, False{}, True{}] : List<&2, Bool>}

# Ho, section 4: 101000110110010 received (lowest power first there,
# highest first here), errors at x^2 and x^5, 100001110110010 corrected
law v_ho_correct:
  {D.Bch.correct(C.Bch.bch15_5(), [False{}, True{}, False{}, False{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, True{}, False{}, True{}]) == Done{D.BchFixed{[False{}, True{}, False{}, False{}, True{}, True{}, False{}, True{}, True{}, True{}, False{}, False{}, False{}, False{}, True{}], 2n}} : Result<&2, &2, E.BchError, D.BchFixed>}

# three errors are too many for the (15,7) code (here detected)
law v_three_errors:
  {D.Bch.decode_bits(C.Bch.bch15_7(), [True{}, True{}, False{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Fail{E.BchUncorrectable{}} : Result<&2, &2, E.BchError, List<&2, Bool>>}

# 13 t parity bits for the NAND codes
law v_nand_t4_bits:
  {C.Bch.parity_bits(C.Bch.nand_t4()) == 52n : Nat}

law v_nand_t8_bits:
  {C.Bch.parity_bits(C.Bch.nand_t8()) == 104n : Nat}

law v_bits_msb:
  {T.Bch.bits_of(T.BchMsbFirst{}, B.Octets.of_list([165, 1])) == [True{}, False{}, True{}, False{}, False{}, True{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}, True{}] : List<&2, Bool>}

law v_bits_lsb:
  {T.Bch.bits_of(T.BchLsbFirst{}, B.Octets.of_list([165, 1])) == [True{}, False{}, True{}, False{}, False{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] : List<&2, Bool>}

# the last byte padded with zero bits
law v_octets_msb:
  {T.Bch.octets_of(T.BchMsbFirst{}, [True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, True{}, True{}]) == B.Octets.of_list([176, 192]) : B.Octets}

law v_octets_lsb:
  {T.Bch.octets_of(T.BchLsbFirst{}, [True{}, False{}, True{}, True{}, False{}, False{}, False{}, False{}, True{}, True{}]) == B.Octets.of_list([13, 3]) : B.Octets}

# refusals: more data bits than n - deg(g), and a word no longer than deg(g)
law v_too_long:
  {E.Bch.encode_bits(C.Bch.bch15_7(), [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Fail{E.BchBadLength{8n}} : Result<&2, &2, E.BchError, List<&2, Bool>>}

law v_too_short:
  {D.Bch.decode_bits(C.Bch.bch15_7(), [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}]) == Fail{E.BchBadLength{8n}} : Result<&2, &2, E.BchError, List<&2, Bool>>}
