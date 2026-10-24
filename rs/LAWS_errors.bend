# The GF(8) code with 4 parity symbols (Rs.small8, t = 2): every pattern
# of at most two symbol errors is corrected, for every message of k = 3
# symbols. Properties, for every input:
#   * a codeword plus any word e of its length has e's syndromes, for
#     every message of up to 3 symbols;
#   * so the decoder treats a codeword plus e as it treats e: whenever e
#     alone (a received word of 7 symbols) decodes to the zero message,
#     every codeword plus e decodes to its own message;
#   * every received word that is a codeword with any two of its symbols
#     changed by any values (two errors, one, or none: the indexes may be
#     equal, a value may be zero, and an index past the end changes
#     nothing) decodes to the message.
import Base
import ./poly.bend as P
import ./code.bend as C
import ./encode.bend as E
import ./syndrome.bend as Sy
import ./rs.bend as D

law small8_syndromes_shift:
  for +m: List<&2, U32>
  for +short: {Nat.is_le(List.length(&2, U32, m), 3n) == True{} : Bool}
  for +e: List<&2, U32>
  for +same: {List.length(&2, U32, e) == Nat.add(List.length(&2, U32, m), 4n) : Nat}
  {Sy.Rs.syndromes(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), E.Rs.codeword(C.Rs.small8(), m), e)) == Sy.Rs.syndromes(C.Rs.small8(), e) : List<&2, U32>}

law small8_decode_shift:
  for +a: U32
  for +b: U32
  for +d: U32
  for +e: List<&2, U32>
  for +n7: {List.length(&2, U32, e) == 7n : Nat}
  for zero: {D.Rs.decode(C.Rs.small8(), e, Nil{}) == Done{[0, 0, 0]} : Result<&2, &2, E.RsError, List<&2, U32>>}
  {D.Rs.decode(C.Rs.small8(), P.RsPoly.add(C.Rs.gf8(), E.Rs.codeword(C.Rs.small8(), [a, b, d]), e), Nil{}) == Done{E.Rs.mask(C.Rs.small8(), [a, b, d])} : Result<&2, &2, E.RsError, List<&2, U32>>}

law small8_two_errors:
  for +a: U32
  for +b: U32
  for +d: U32
  for +i: Nat
  for +u: U32
  for +j: Nat
  for +v: U32
  {D.Rs.decode(C.Rs.small8(), D.Rs.inject(D.Rs.inject(E.Rs.codeword(C.Rs.small8(), [a, b, d]), i, u), j, v), Nil{}) == Done{E.Rs.mask(C.Rs.small8(), [a, b, d])} : Result<&2, &2, E.RsError, List<&2, U32>>}
