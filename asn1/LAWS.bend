# Laws of bend-osdev-asn1, for every input:
#
# * decode_encode: an element the encoder writes decodes back to itself,
#   under any rules it conforms to (every value conforms to BER's);
# * encode_decode: under rules with DER's length checks and without the
#   indefinite form or trailing octets, an element decoded from bytes is
#   encoded back to exactly those bytes: DER encoding is unique;
# * decode_within, prefix_within, all_within: a decode that succeeds reads
#   nothing past its buffer: the octets its elements need (two per element
#   for the identifier and length, and the primitive contents) fit in the
#   buffer, beside any octets left after it;
# * oid_round_trip, oid_canonical: OBJECT IDENTIFIER contents read back as
#   the arcs written, and arcs read are written back as the same contents.
#
# Vectors: ITU-T X.690 (02/2021)'s own examples.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./rules.bend as R
import ./encode.bend as En
import ./conform.bend as C
import ./asn1.bend as A
import ./oidval.bend as O
import ./length.bend as L
import ./number.bend as Nu

law decode_encode:
  for +r: R.Asn1Rules
  for +n: N.Asn1Node
  for +b: B.Octets
  for +e: {En.Asn1.encode(n) == Done{b} : Result<&2, &2, E.Asn1Error, B.Octets>}
  for +hc: {C.Asn1.conforms(r, n) == True{} : Bool}
  {A.Asn1.decode(r, b) == Done{n} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}

law encode_decode:
  for +r: R.Asn1Rules
  for +hm: {R.Asn1Rules.min_length(r) == True{} : Bool}
  for +hi: {R.Asn1Rules.indefinite(r) == False{} : Bool}
  for +ht: {R.Asn1Rules.trailing(r) == False{} : Bool}
  for +b: B.Octets
  for +n: N.Asn1Node
  for +e: {A.Asn1.decode(r, b) == Done{n} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}
  {En.Asn1.encode(n) == Done{b} : Result<&2, &2, E.Asn1Error, B.Octets>}

law der_unique:
  for +b: B.Octets
  for +n: N.Asn1Node
  for +e: {A.Asn1.decode(R.Asn1Rules.der(), b) == Done{n} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}
  {En.Asn1.encode(n) == Done{b} : Result<&2, &2, E.Asn1Error, B.Octets>}

law decode_within:
  for +r: R.Asn1Rules
  for +b: B.Octets
  for +n: N.Asn1Node
  for +e: {A.Asn1.decode(r, b) == Done{n} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}
  {Nat.is_le(N.Asn1.span(n), B.Octets.len(b)) == True{} : Bool}

law prefix_within:
  for +r: R.Asn1Rules
  for +b: B.Octets
  for +n: N.Asn1Node
  for +rest: B.Octets
  for +e: {A.Asn1.decode_prefix(r, b) == Done{A.Asn1Read{n, rest}} : Result<&2, &2, E.Asn1Error, A.Asn1Read>}
  {Nat.is_le(Nat.add(N.Asn1.span(n), B.Octets.len(rest)), B.Octets.len(b)) == True{} : Bool}

law all_within:
  for +r: R.Asn1Rules
  for +b: B.Octets
  for +ns: List<&2, N.Asn1Node>
  for +e: {A.Asn1.decode_all(r, b) == Done{ns} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}
  {Nat.is_le(N.Asn1.spans(ns), B.Octets.len(b)) == True{} : Bool}

law oid_round_trip:
  for +arcs: List<&2, Nat>
  for +o: B.Octets
  for +e: {O.Asn1.oid_content(arcs) == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}
  {O.Asn1.oid_of_content(o) == Done{arcs} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}

law oid_canonical:
  for +o: B.Octets
  for +arcs: List<&2, Nat>
  for +e: {O.Asn1.oid_of_content(o) == Done{arcs} : Result<&2, &2, E.Asn1Error, List<&2, Nat>>}
  {O.Asn1.oid_content(arcs) == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}

# Vectors: ITU-T X.690 (02/2021)'s examples

# 8.9.3: SEQUENCE {name IA5String "Smith", ok BOOLEAN TRUE}
law vec_sequence:
  {En.Asn1.encode(N.Asn1Cons{T.Asn1Tag.sequence(), [N.Asn1Prim{T.Asn1Tag.ia5_string(), B.Octets.of_list([83, 109, 105, 116, 104])}, N.Asn1Prim{T.Asn1Tag.boolean(), B.Octets.of_list([255])}]}) == Done{B.Octets.of_list([48, 10, 22, 5, 83, 109, 105, 116, 104, 1, 1, 255])} : Result<&2, &2, E.Asn1Error, B.Octets>}

# 8.14.4: Type3 ::= [2] Type2, Type2 ::= [APPLICATION 3] IMPLICIT VisibleString, "Jones"
law vec_tagging:
  {A.Asn1.decode(R.Asn1Rules.der(), B.Octets.of_list([162, 7, 67, 5, 74, 111, 110, 101, 115])) == Done{N.Asn1Cons{T.Asn1Tag.context(2n), [N.Asn1Prim{T.Asn1Tag{T.Asn1Application{}, 3n}, B.Octets.of_list([74, 111, 110, 101, 115])}]}} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}

# 8.19.5: {2 999 3}
law vec_oid:
  {O.Asn1.oid_content([2n, 999n, 3n]) == Done{B.Octets.of_list([136, 55, 3])} : Result<&2, &2, E.Asn1Error, B.Octets>}

# 8.1.3.5: L = 201 in the long form, 81 C9
law vec_length:
  {L.a1.len_bytes(201n) == [Nu.a1.b(129n), Nu.a1.b(201n)] : List<&2, U32>}

# 8.1.3.6, 8.1.5: the indefinite form, accepted by BER and refused by DER
law vec_indefinite:
  {(A.Asn1.decode(R.Asn1Rules.ber(), B.Octets.of_list([48, 128, 5, 0, 0, 0])), A.Asn1.decode(R.Asn1Rules.der(), B.Octets.of_list([48, 128, 5, 0, 0, 0]))) == (Done{N.Asn1Cons{T.Asn1Tag.sequence(), [N.Asn1Prim{T.Asn1Tag.null(), B.Octets.empty()}]}}, Fail{E.Asn1Indefinite{}}) : Result<&2, &2, E.Asn1Error, N.Asn1Node> & Result<&2, &2, E.Asn1Error, N.Asn1Node>}
