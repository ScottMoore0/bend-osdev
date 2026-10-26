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
#   the arcs written, and arcs read are written back as the same contents;
# * read_split, read_all_split: the octets kept for each element read are
#   the input's own, in order: an element's octets then the octets after
#   it are the input, and the elements of a run join back to it;
#   contents_within: an element's contents octets are a slice of its
#   octets; items_split: the elements inside a constructed element join to
#   its contents octets; read_der: under DER's length checks, an element's
#   octets are its DER encoding (its identifier, length and contents
#   octets as X.690 writes them);
# * encode_retag: re-tagging a constructed element changes only its
#   identifier octets;
# * match_tlv_tlv, match_split, match_whole, match_tlv_within, match_within,
#   match_input: a schema match holds the element read, and every match
#   reached inside it by Asn1Match.follow keeps octets that are a slice of
#   the octets of the match it was reached from, so of the input;
#   match_der: under DER's length checks, a match's octets are the DER
#   encoding of its element; match_of_node: a SEQUENCE OF or SET OF match
#   is of a constructed element of its tag; follow_nil, follow_at,
#   follow_inner, at_items: what Asn1Match.follow and Asn1Match.at reach.
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
import ./schema.bend as Sc

law decode_encode:
  for +r: R.Asn1Rules
  for +n: N.Asn1Node
  for +b: B.Octets
  for +e: {En.Asn1.encode(n) == Done{b} : Result<&2, &2, E.Asn1Error, B.Octets>}
  for +hc: {C.Asn1.conforms(r, n) == True{} : Bool}
  {A.Asn1.decode(r, b) == Done{n} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}

# a primitive BIT STRING or OCTET STRING conforms to every rules, so
# decode_encode applies to it under any rules
law bit_string_conforms:
  for +r: R.Asn1Rules
  for +c: B.Octets
  {C.Asn1.conforms(r, N.Asn1Prim{T.Asn1Tag.bit_string(), c}) == True{} : Bool}

law octet_string_conforms:
  for +r: R.Asn1Rules
  for +c: B.Octets
  {C.Asn1.conforms(r, N.Asn1Prim{T.Asn1Tag.octet_string(), c}) == True{} : Bool}

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

# The octets kept for each element: the input's own

law read_split:
  for +r: R.Asn1Rules
  for +b: B.Octets
  for +x: A.Asn1Tlv
  for +rest: B.Octets
  for +e: {A.Asn1.read(r, b) == Done{A.Asn1TlvRead{x, rest}} : Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>}
  {B.Octets.append(A.Asn1Tlv.raw(x), rest) == b : B.Octets}

law read_all_split:
  for +r: R.Asn1Rules
  for +b: B.Octets
  for +xs: List<&2, A.Asn1Tlv>
  for +e: {A.Asn1.read_all(r, b) == Done{xs} : Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>}
  {B.Octets.concat(A.Asn1.raws(xs)) == b : B.Octets}

law contents_within:
  for +r: R.Asn1Rules
  for +x: A.Asn1Tlv
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {A.Asn1Tlv.raw(x) == B.Octets.append(u, B.Octets.append(A.Asn1.contents(r, x), v)) : B.Octets}>>

law items_split:
  for +r: R.Asn1Rules
  for +x: A.Asn1Tlv
  for +xs: List<&2, A.Asn1Tlv>
  for +e: {A.Asn1.items(r, x) == Done{xs} : Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>}
  {B.Octets.concat(A.Asn1.raws(xs)) == A.Asn1.contents(r, x) : B.Octets}

law read_der:
  for +r: R.Asn1Rules
  for +hm: {R.Asn1Rules.min_length(r) == True{} : Bool}
  for +hi: {R.Asn1Rules.indefinite(r) == False{} : Bool}
  for +b: B.Octets
  for +x: A.Asn1Tlv
  for +rest: B.Octets
  for +e: {A.Asn1.read(r, b) == Done{A.Asn1TlvRead{x, rest}} : Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>}
  {En.Asn1.encode(A.Asn1Tlv.node(x)) == Done{A.Asn1Tlv.raw(x)} : Result<&2, &2, E.Asn1Error, B.Octets>}

law encode_retag:
  for +t: T.Asn1Tag
  for +u: T.Asn1Tag
  for +ns: List<&2, N.Asn1Node>
  for +o: B.Octets
  for +hu: {Nat.is_lt(T.Asn1Tag.num(u), 31n) == True{} : Bool}
  for +hr: {T.Asn1Tag.is_eq(u, T.Asn1Tag.universal(0n)) == False{} : Bool}
  for +e: {En.Asn1.encode(N.Asn1Cons{t, ns}) == Done{o} : Result<&2, &2, E.Asn1Error, B.Octets>}
  Sigma<&1, &1, B.Octets, l => {o == B.Octets.append(En.Asn1.identifier(t, True{}), l) : B.Octets} & {En.Asn1.encode(N.Asn1Cons{u, ns}) == Done{B.Octets.append(En.Asn1.identifier(u, True{}), l)} : Result<&2, &2, E.Asn1Error, B.Octets>}>

# Schema matches: the element read, and slices of it

law match_tlv_tlv:
  for +r: R.Asn1Rules
  for +s: Sc.Asn1Schema
  for +x: A.Asn1Tlv
  for +m: Sc.Asn1Match
  for +e: {Sc.Asn1.match_tlv(r, s, x) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}
  {Sc.Asn1Match.tlv(m) == Some{x} : Maybe<&2, A.Asn1Tlv>}

law match_tlv_within:
  for +r: R.Asn1Rules
  for +s: Sc.Asn1Schema
  for +x: A.Asn1Tlv
  for +m: Sc.Asn1Match
  for +p: List<&2, Sc.Asn1Step>
  for +q: List<&2, Sc.Asn1Step>
  for +e: {Sc.Asn1.match_tlv(r, s, x) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {Sc.Asn1Match.raw(Sc.Asn1Match.follow(m, p)) == B.Octets.append(u, B.Octets.append(Sc.Asn1Match.raw(Sc.Asn1Match.follow(m, List.append(&2, Sc.Asn1Step, p, q))), v)) : B.Octets}>>

law match_split:
  for +r: R.Asn1Rules
  for +s: Sc.Asn1Schema
  for +b: B.Octets
  for +m: Sc.Asn1Match
  for +e: {Sc.Asn1.match(r, s, b) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}
  Sigma<&1, &1, B.Octets, rest => {B.Octets.append(Sc.Asn1Match.raw(m), rest) == b : B.Octets}>

law match_whole:
  for +r: R.Asn1Rules
  for +ht: {R.Asn1Rules.trailing(r) == False{} : Bool}
  for +s: Sc.Asn1Schema
  for +b: B.Octets
  for +m: Sc.Asn1Match
  for +e: {Sc.Asn1.match(r, s, b) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}
  {Sc.Asn1Match.raw(m) == b : B.Octets}

law match_within:
  for +r: R.Asn1Rules
  for +s: Sc.Asn1Schema
  for +b: B.Octets
  for +m: Sc.Asn1Match
  for +p: List<&2, Sc.Asn1Step>
  for +q: List<&2, Sc.Asn1Step>
  for +e: {Sc.Asn1.match(r, s, b) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {Sc.Asn1Match.raw(Sc.Asn1Match.follow(m, p)) == B.Octets.append(u, B.Octets.append(Sc.Asn1Match.raw(Sc.Asn1Match.follow(m, List.append(&2, Sc.Asn1Step, p, q))), v)) : B.Octets}>>

law match_input:
  for +r: R.Asn1Rules
  for +s: Sc.Asn1Schema
  for +b: B.Octets
  for +m: Sc.Asn1Match
  for +p: List<&2, Sc.Asn1Step>
  for +e: {Sc.Asn1.match(r, s, b) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}
  Sigma<&1, &1, B.Octets, u => Sigma<&1, &1, B.Octets, v => {b == B.Octets.append(u, B.Octets.append(Sc.Asn1Match.raw(Sc.Asn1Match.follow(m, p)), v)) : B.Octets}>>

law match_der:
  for +r: R.Asn1Rules
  for +hm: {R.Asn1Rules.min_length(r) == True{} : Bool}
  for +hi: {R.Asn1Rules.indefinite(r) == False{} : Bool}
  for +s: Sc.Asn1Schema
  for +b: B.Octets
  for +m: Sc.Asn1Match
  for +e: {Sc.Asn1.match(r, s, b) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}
  Sigma<&1, &1, N.Asn1Node, n => {Sc.Asn1Match.node(m) == Some{n} : Maybe<&2, N.Asn1Node>} & {En.Asn1.encode(n) == Done{Sc.Asn1Match.raw(m)} : Result<&2, &2, E.Asn1Error, B.Octets>}>

law match_of_node:
  for +r: R.Asn1Rules
  for +t: T.Asn1Tag
  for +item: Sc.Asn1Schema
  for +set: Bool
  for +b: B.Octets
  for +m: Sc.Asn1Match
  for +e: {Sc.Asn1.match(r, Sc.Asn1SOf{t, item, set}, b) == Done{m} : Result<&2, &2, E.Asn1Error, Sc.Asn1Match>}
  Sigma<&1, &1, List<&2, N.Asn1Node>, ns => {Sc.Asn1Match.node(m) == Some{N.Asn1Cons{t, ns}} : Maybe<&2, N.Asn1Node>}>

law follow_nil:
  for +m: Sc.Asn1Match
  {Sc.Asn1Match.follow(m, Nil{}) == m : Sc.Asn1Match}

law follow_at:
  for +m: Sc.Asn1Match
  for +i: Nat
  for +p: List<&2, Sc.Asn1Step>
  {Sc.Asn1Match.follow(m, Con{Sc.Asn1StepAt{i}, p}) == Sc.Asn1Match.follow(Sc.Asn1Match.at(m, i), p) : Sc.Asn1Match}

law follow_inner:
  for +m: Sc.Asn1Match
  for +p: List<&2, Sc.Asn1Step>
  {Sc.Asn1Match.follow(m, Con{Sc.Asn1StepInner{}, p}) == Sc.Asn1Match.follow(Sc.Asn1Match.inner(m), p) : Sc.Asn1Match}

law at_items:
  for +m: Sc.Asn1Match
  for +pre: List<&2, Sc.Asn1Match>
  for +x: Sc.Asn1Match
  for +post: List<&2, Sc.Asn1Match>
  for +h: {Sc.Asn1Match.items(m) == List.append(&2, Sc.Asn1Match, pre, Con{x, post}) : List<&2, Sc.Asn1Match>}
  {Sc.Asn1Match.at(m, List.length(&2, Sc.Asn1Match, pre)) == x : Sc.Asn1Match}

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

# 8.1.2.2, 8.1.2.5: [0] IMPLICIT constructed is A0, SET (constructed) 31
law vec_identifier:
  {(En.Asn1.identifier(T.Asn1Tag.context(0n), True{}), En.Asn1.identifier(T.Asn1Tag.set(), True{})) == (B.Octets.of_list([160]), B.Octets.of_list([49])) : B.Octets & B.Octets}
