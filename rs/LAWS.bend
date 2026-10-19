# Properties, for every input:
#   * every code: encoding a message of at most k symbols gives its
#     codeword, which begins with the message (systematic encoding);
#   * the GF(4) code with 2 parity symbols (Rs.small4, t = 1), for every
#     message: its codeword's syndromes are zero, it decodes to the
#     message, and so does it with any one symbol changed to anything (one
#     error) or with any one symbol erased and changed to anything;
#   * the GF(8) code with 4 parity symbols (Rs.small8, t = 2): syndromes
#     and parity are linear (the syndromes of a sum of words are the sums
#     of their syndromes; the same for parity and messages), for words and
#     messages of every length; every codeword's syndromes are zero, for
#     every message of up to k = 3 symbols; and every codeword decodes to
#     its message.
#   * RsGf.inv is the inverse: a a^-1 = 1 for every nonzero element of GF(8)
#     and GF(16).
# Vectors: Geisel's (15,9) example throughout (NASA TM-102162: the
# generator, section 3.3.1; the codeword, 3.3.2; the syndromes, 4.2.1;
# sigma(X), 4.3.1.1; the Chien search, 4.4.1; the decoded word, 4.6; the
# erasure example, chapter 5); Massey's figure 2 (1969); codewords of the
# named 8-bit codes from an independent model (ref/gen.py); and
# Rs.check's refusals.
import Base
import ../gf/gfm.bend as M
import ./poly.bend as P
import ./arith.bend as A
import ./code.bend as C
import ./encode.bend as E
import ./syndrome.bend as Sy
import ./bm.bend as Bm
import ./chien.bend as Ch
import ./rs.bend as D

# Every code

law encode_short:
  for +c: C.RsCode
  for +m: List<&2, U32>
  for short: {Nat.is_le(List.length(&2, U32, m), U32.to_nat(C.Rs.k(c))) == True{} : Bool}
  {E.Rs.encode(c, m) == Done{E.Rs.codeword(c, m)} : Result<&2, &2, E.RsError, List<&2, U32>>}

law codeword_message:
  for +c: C.RsCode
  for +m: List<&2, U32>
  {List.take(&2, U32, E.Rs.codeword(c, m), List.length(&2, U32, m)) == E.Rs.mask(c, m) : List<&2, U32>}

# GF(4), t = 1

law small4_syndromes:
  for +a: U32
  {Sy.Rs.syndromes(C.Rs.small4(), E.Rs.codeword(C.Rs.small4(), [a])) == [0, 0] : List<&2, U32>}

law small4_roundtrip:
  for +a: U32
  {D.Rs.decode(C.Rs.small4(), E.Rs.codeword(C.Rs.small4(), [a]), Nil{}) == Done{E.Rs.mask(C.Rs.small4(), [a])} : Result<&2, &2, E.RsError, List<&2, U32>>}

law small4_error:
  for +a: U32
  for +i: Nat
  for +v: U32
  {D.Rs.decode(C.Rs.small4(), D.Rs.inject(E.Rs.codeword(C.Rs.small4(), [a]), i, v), Nil{}) == Done{E.Rs.mask(C.Rs.small4(), [a])} : Result<&2, &2, E.RsError, List<&2, U32>>}

law small4_erasure:
  for +a: U32
  for +i: Nat
  for +v: U32
  for hi: {Nat.is_lt(i, 3n) == True{} : Bool}
  {D.Rs.decode(C.Rs.small4(), D.Rs.inject(E.Rs.codeword(C.Rs.small4(), [a]), i, v), [i]) == Done{E.Rs.mask(C.Rs.small4(), [a])} : Result<&2, &2, E.RsError, List<&2, U32>>}

# GF(8), t = 2

law small8_syndromes_linear:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +same: {List.length(&2, U32, a) == List.length(&2, U32, b) : Nat}
  {Sy.Rs.syndromes(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), a, b)) == P.RsPoly.add(C.Rs.gf8(), Sy.Rs.syndromes(C.Rs.small8(), a), Sy.Rs.syndromes(C.Rs.small8(), b)) : List<&2, U32>}

law small8_parity_linear:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +same: {List.length(&2, U32, a) == List.length(&2, U32, b) : Nat}
  {E.Rs.parity(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), a, b)) == P.RsPoly.add(C.Rs.gf8(), E.Rs.parity(C.Rs.small8(), a), E.Rs.parity(C.Rs.small8(), b)) : List<&2, U32>}

law small8_codeword_syndromes:
  for +m: List<&2, U32>
  for +short: {Nat.is_le(List.length(&2, U32, m), 3n) == True{} : Bool}
  {Sy.Rs.syndromes(C.Rs.small8(), E.Rs.codeword(C.Rs.small8(), m)) == [0, 0, 0, 0] : List<&2, U32>}

law small8_roundtrip:
  for +m: List<&2, U32>
  for +short: {Nat.is_le(List.length(&2, U32, m), 3n) == True{} : Bool}
  for +some: {Nat.is_lt(0n, List.length(&2, U32, m)) == True{} : Bool}
  {D.Rs.decode(C.Rs.small8(), E.Rs.codeword(C.Rs.small8(), m), Nil{}) == Done{E.Rs.mask(C.Rs.small8(), m)} : Result<&2, &2, E.RsError, List<&2, U32>>}

# The inverse: a a^-1 = 1 for every nonzero element of GF(8) and GF(16)

law inv_gf8:
  for +a: U32
  for nz: {U32.is_eq(M.Gfm.elt(C.Rs.gf8(), a), 0) == False{} : Bool}
  {M.Gfm.mul(C.Rs.gf8(), a, A.RsGf.inv(C.Rs.gf8(), a)) == 1 : U32}

law inv_gf16:
  for +a: U32
  for nz: {U32.is_eq(M.Gfm.elt(M.Gfm.gf16(), a), 0) == False{} : Bool}
  {M.Gfm.mul(M.Gfm.gf16(), a, A.RsGf.inv(M.Gfm.gf16(), a)) == 1 : U32}

# agrees with gf's own vector for Gfm.inv in GF(2^13): 1234^-1 = 2297
law v_inv_bch13:
  {A.RsGf.inv(M.Gfm.bch13(), 1234) == 2297 : U32}

# Vectors: Geisel's (15,9) example

# g(X) = X^6 + a^10 X^5 + a^14 X^4 + a^4 X^3 + a^6 X^2 + a^9 X + a^6
law v_generator:
  {C.Rs.generator(C.Rs.geisel15_9()) == [12, 10, 12, 3, 9, 7, 1] : List<&2, U32>}

# M(X) = a^11 X; C(X) = a^11 X^7 + a^8 X^5 + a^10 X^4 + a^4 X^3 + a^14 X^2 + a^8 X + a^12
law v_encode:
  {E.Rs.encode(C.Rs.geisel15_9(), [0, 0, 0, 0, 0, 0, 0, 14, 0]) == Done{[0, 0, 0, 0, 0, 0, 0, 14, 0, 5, 7, 3, 9, 5, 15]} : Result<&2, &2, E.RsError, List<&2, U32>>}

# R(X) = X^8 + C(X) + (a^3 + a^14) X^2: S1..S6 = 1, 1, a^5, 1, 0, a^10
law v_syndromes:
  {Sy.Rs.syndromes(C.Rs.geisel15_9(), [0, 0, 0, 0, 0, 0, 1, 14, 0, 5, 7, 3, 8, 5, 15]) == [1, 1, 6, 1, 0, 7] : List<&2, U32>}

# sigma(X) = a^10 X^2 + X + 1
law v_bm:
  {Bm.RsBm.lfsr(M.Gfm.gf16(), [1, 1, 6, 1, 0, 7]) == Bm.RsLfsr{[1, 1, 7], 2n} : Bm.RsLfsr}

# the roots of sigma_r: z = a^2 and a^8, so errors at X^2 and X^8
law v_chien:
  {Ch.RsChien.roots(M.Gfm.gf16(), [1, 1, 7], C.Rs.beta_inv(C.Rs.geisel15_9()), 15) == [2, 8] : List<&2, U32>}

law v_correct:
  {D.Rs.correct(C.Rs.geisel15_9(), [0, 0, 0, 0, 0, 0, 1, 14, 0, 5, 7, 3, 8, 5, 15], Nil{}) == Done{D.RsFixed{[0, 0, 0, 0, 0, 0, 0, 14, 0, 5, 7, 3, 9, 5, 15], 2n}} : Result<&2, &2, E.RsError, D.RsFixed>}

# chapter 5: errors at X^8 and X, erasures at X^7 and X^2 (indexes 7 and 12)
law v_erasures:
  {D.Rs.correct(C.Rs.geisel15_9(), [0, 0, 0, 0, 0, 0, 1, 11, 0, 5, 7, 3, 8, 10, 15], [7n, 12n]) == Done{D.RsFixed{[0, 0, 0, 0, 0, 0, 0, 14, 0, 5, 7, 3, 9, 5, 15], 4n}} : Result<&2, &2, E.RsError, D.RsFixed>}

# the same four symbols in error without the erasures: more than t = 3
law v_too_many:
  {D.Rs.decode(C.Rs.geisel15_9(), [0, 0, 0, 0, 0, 0, 1, 11, 0, 5, 7, 3, 8, 10, 15], Nil{}) == Fail{E.RsUncorrectable{}} : Result<&2, &2, E.RsError, List<&2, U32>>}

# Massey (1969), figure 2: the sequence 1, 0, 1, 0, 0 needs L = 3, C(D) = 1
law v_massey:
  {Bm.RsBm.lfsr(M.Gfm.gf16(), [1, 0, 1, 0, 0]) == Bm.RsLfsr{[1], 3n} : Bm.RsLfsr}

# The named 8-bit codes (ref/gen.py's model): the parity of "RS"
law v_rs8_p16:
  {E.Rs.parity(C.Rs.rs8_p16(), [82, 83]) == [124, 76, 86, 57, 4, 98, 71, 248, 211, 157, 123, 86, 118, 44, 111, 209] : List<&2, U32>}

law v_ccsds_e8:
  {E.Rs.parity(C.Rs.ccsds_e8(), [82, 83]) == [87, 55, 204, 151, 107, 46, 24, 125, 81, 170, 82, 255, 46, 4, 226, 189] : List<&2, U32>}

# Refusals
law v_check_short:
  {D.Rs.check(C.Rs.small8(), 4n, Nil{}) == Some{E.RsBadLength{4n}} : Maybe<&2, E.RsError>}

law v_check_long:
  {D.Rs.check(C.Rs.small8(), 8n, Nil{}) == Some{E.RsBadLength{8n}} : Maybe<&2, E.RsError>}

law v_check_erasures:
  {D.Rs.check(C.Rs.small8(), 7n, [0n, 1n, 2n, 3n, 4n]) == Some{E.RsTooManyErasures{5n}} : Maybe<&2, E.RsError>}

law v_check_outside:
  {D.Rs.check(C.Rs.small8(), 7n, [7n]) == Some{E.RsBadErasure{7n}} : Maybe<&2, E.RsError>}

law v_check_twice:
  {D.Rs.check(C.Rs.small8(), 7n, [2n, 2n]) == Some{E.RsBadErasure{2n}} : Maybe<&2, E.RsError>}
