# The key order and map lookup, for every input:
# * the key order (NftKey.le, NftKey.lt: bytes compared most significant
#   first, a proper prefix first) is reflexive and transitive, and a key
#   below another is not at or above it;
# * on a set with the invariant (sorted, disjoint intervals), the element
#   holding a key is the only one: lookup gives its data;
# * inserting an element: lookup gives its data for the keys it holds, and
#   what it gave before for the others;
# * a map built from a list of elements answers as the list does: the data
#   of the first element of the list holding the key (the list model).
#
# A pair of its own (PROOF_map.bend): the proofs rest on LAWS.bend's set
# laws and bend-osdev-u32's comparison law.
import Base
import ../bytes/bytes.bend as B
import ./family.bend as F
import ./sets.bend as S

# the data of the first element of es holding x: a map as a list
def list_lookup(es: List<&2, S.NftElem>, +x: B.Octets) -> Maybe<&2, S.NftData>:
  match es:
    case Nil{}:
      None{}
    case Con{+e, t}:
      S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), list_lookup(t, x))

# The key order

law key_le_refl:
  for +a: B.Octets
  {S.NftKey.le(a, a) == True{} : Bool}

law key_le_trans:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  for h1: {S.NftKey.le(a, b) == True{} : Bool}
  for h2: {S.NftKey.le(b, c) == True{} : Bool}
  {S.NftKey.le(a, c) == True{} : Bool}

law key_lt_trans:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  for h1: {S.NftKey.lt(a, b) == True{} : Bool}
  for h2: {S.NftKey.lt(b, c) == True{} : Bool}
  {S.NftKey.lt(a, c) == True{} : Bool}

law key_lt_le_trans:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  for h1: {S.NftKey.lt(a, b) == True{} : Bool}
  for h2: {S.NftKey.le(b, c) == True{} : Bool}
  {S.NftKey.lt(a, c) == True{} : Bool}

law key_le_lt_trans:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  for h1: {S.NftKey.le(a, b) == True{} : Bool}
  for h2: {S.NftKey.lt(b, c) == True{} : Bool}
  {S.NftKey.lt(a, c) == True{} : Bool}

law key_lt_not_le:
  for +a: B.Octets
  for +b: B.Octets
  for h: {S.NftKey.lt(a, b) == True{} : Bool}
  {S.NftKey.le(b, a) == False{} : Bool}

# Maps

# on a set with the invariant, the element holding x is the one lookup finds
law map_lookup_unique:
  for +s: S.NftSet
  for +pre: List<&2, S.NftElem>
  for +e: S.NftElem
  for +post: List<&2, S.NftElem>
  for +x: B.Octets
  for wf: {S.NftSet.wf(s) == True{} : Bool}
  for es: {S.NftSet.elements(s) == List.append(&2, S.NftElem, pre, Con{e, post}) : List<&2, S.NftElem>}
  for he: {S.NftElem.contains(e, x) == True{} : Bool}
  {S.NftSet.lookup(s, x) == Some{S.NftElem.data(e)} : Maybe<&2, S.NftData>}

law map_lookup_insert:
  for +s: S.NftSet
  for +e: S.NftElem
  for +x: B.Octets
  for +s2: S.NftSet
  for ok: {S.NftSet.insert(s, e) == Done{s2} : Result<&2, &2, F.NftError, S.NftSet>}
  {S.NftSet.lookup(s2, x) == S.NftSet.lookup.pick(S.NftElem.contains(e, x), S.NftElem.data(e), S.NftSet.lookup(s, x)) : Maybe<&2, S.NftData>}

law map_lookup_of_list:
  for +es: List<&2, S.NftElem>
  for +s: S.NftSet
  for +x: B.Octets
  for ok: {S.NftSet.of_list(es) == Done{s} : Result<&2, &2, F.NftError, S.NftSet>}
  {S.NftSet.lookup(s, x) == list_lookup(es, x) : Maybe<&2, S.NftData>}

# Vectors: a map of two intervals, looked up inside one and between them
law map_lookup_vec:
  {(S.NftSet.of_list([S.NftElem.to(S.NftElem.range(S.NftKey.u8(10), S.NftKey.u8(20)), S.NftDataValue{S.NftKey.u8(1)}), S.NftElem.to(S.NftElem.range(S.NftKey.u8(30), S.NftKey.u8(40)), S.NftDataValue{S.NftKey.u8(2)})]), list_lookup([S.NftElem.to(S.NftElem.range(S.NftKey.u8(10), S.NftKey.u8(20)), S.NftDataValue{S.NftKey.u8(1)}), S.NftElem.to(S.NftElem.range(S.NftKey.u8(30), S.NftKey.u8(40)), S.NftDataValue{S.NftKey.u8(2)})], S.NftKey.u8(35)), list_lookup([S.NftElem.to(S.NftElem.range(S.NftKey.u8(10), S.NftKey.u8(20)), S.NftDataValue{S.NftKey.u8(1)})], S.NftKey.u8(25))) == (Done{S.NftSet{[S.NftElem{S.NftKey.u8(10), S.NftKey.u8(20), S.NftDataValue{S.NftKey.u8(1)}}, S.NftElem{S.NftKey.u8(30), S.NftKey.u8(40), S.NftDataValue{S.NftKey.u8(2)}}]}}, Some{S.NftDataValue{S.NftKey.u8(2)}}, None{}) : Result<&2, &2, F.NftError, S.NftSet> & Maybe<&2, S.NftData> & Maybe<&2, S.NftData>}

# the hypotheses of map_lookup_unique hold: a one-element set holding 15
law map_lookup_unique_sat:
  {(S.NftSet.wf(S.NftSet{[S.NftElem.range(S.NftKey.u8(10), S.NftKey.u8(20))]}), S.NftElem.contains(S.NftElem.range(S.NftKey.u8(10), S.NftKey.u8(20)), S.NftKey.u8(15))) == (True{}, True{}) : Bool & Bool}
