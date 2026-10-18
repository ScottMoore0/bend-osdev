# Every field writer and its reader agree, for every value; a byte is always
# below 256; and a byte string split anywhere joins back to itself. The
# vectors fix the byte orders, the hex text, and what a short input reads.
import Base
import ../word64/word64.bend as W
import ./bytes.bend as B

# Properties, for every input

law le16_round_trip:
  for v: U32
  {B.le16_at(B.le16(v), 0n) == Some{B.low16(v)} : Maybe<&2, U32>}

law be16_round_trip:
  for v: U32
  {B.be16_at(B.be16(v), 0n) == Some{B.low16(v)} : Maybe<&2, U32>}

law le32_round_trip:
  for v: U32
  {B.le32_at(B.le32(v), 0n) == Some{v} : Maybe<&2, U32>}

law be32_round_trip:
  for v: U32
  {B.be32_at(B.be32(v), 0n) == Some{v} : Maybe<&2, U32>}

law le64_round_trip:
  for +v: W.W64
  {B.le64_at(B.le64(v), 0n) == Some{v} : Maybe<&2, W.W64>}

law be64_round_trip:
  for +v: W.W64
  {B.be64_at(B.be64(v), 0n) == Some{v} : Maybe<&2, W.W64>}

law byte_below_256:
  for b: U32
  {U32.is_lt(B.byte(b), 256) == True{} : Bool}

law take_drop:
  for n: Nat
  for xs: List<&2, U32>
  {B.append(B.take(n, xs), B.drop(n, xs)) == xs : List<&2, U32>}

# Vectors (0x12345678 = 305419896)

law be32_order:
  {B.be32(305419896) == [18, 52, 86, 120] : List<&2, U32>}

law le32_order:
  {B.le32(305419896) == [120, 86, 52, 18] : List<&2, U32>}

law be64_order:
  {B.be64(W.W64.from_parts(16909060, 84281096)) == [1, 2, 3, 4, 5, 6, 7, 8] : List<&2, U32>}

law le16_at_offset:
  {B.le16_at([9, 52, 18], 1n) == Some{4660} : Maybe<&2, U32>}

law short_input:
  {B.le16_at([1, 2, 3], 2n) == None{} : Maybe<&2, U32>}

law at_end:
  {B.at([7, 8], 2n) == None{} : Maybe<&2, U32>}

law masks_elements:
  {B.at([7, 264], 1n) == Some{8} : Maybe<&2, U32>}

law hex_text:
  {B.hex(B.of_string("Bend")) == "42656e64" : String}

# The Octets interface: the same round trips, and slicing, on Octets

law octets_le16_round_trip:
  for v: U32
  {B.Octets.le16_at(B.Octets.le16(v), 0n) == Some{B.low16(v)} : Maybe<&2, U32>}

law octets_be16_round_trip:
  for v: U32
  {B.Octets.be16_at(B.Octets.be16(v), 0n) == Some{B.low16(v)} : Maybe<&2, U32>}

law octets_le32_round_trip:
  for v: U32
  {B.Octets.le32_at(B.Octets.le32(v), 0n) == Some{v} : Maybe<&2, U32>}

law octets_be32_round_trip:
  for v: U32
  {B.Octets.be32_at(B.Octets.be32(v), 0n) == Some{v} : Maybe<&2, U32>}

law octets_le64_round_trip:
  for +v: W.W64
  {B.Octets.le64_at(B.Octets.le64(v), 0n) == Some{v} : Maybe<&2, W.W64>}

law octets_be64_round_trip:
  for +v: W.W64
  {B.Octets.be64_at(B.Octets.be64(v), 0n) == Some{v} : Maybe<&2, W.W64>}

law octets_take_drop:
  for n: Nat
  for o: B.Octets
  {B.Octets.append(B.Octets.take(n, o), B.Octets.drop(n, o)) == o : B.Octets}

# of_list masks once: converting a byte string to a list and back changes nothing
law octets_of_list_idempotent:
  for xs: List<&2, U32>
  {B.Octets.of_list(B.Octets.to_list(B.Octets.of_list(xs))) == B.Octets.of_list(xs) : B.Octets}

law octets_is_eq_refl:
  for o: B.Octets
  {B.Octets.is_eq(o, o) == True{} : Bool}

law octets_masks:
  {B.Octets.hex(B.Octets.of_list([255, 256, 257])) == "ff0001" : String}

law octets_slice:
  {B.Octets.to_string(B.Octets.slice(2n, 3n, B.Octets.of_string("bend-osdev"))) == "nd-" : String}

# The interface laws other packages' proofs rely on: how Octets relates to
# lists, without depending on how Octets stores its bytes

law octets_append_list:
  for a: B.Octets
  for b: B.Octets
  {B.Octets.to_list(B.Octets.append(a, b)) == B.append(B.Octets.to_list(a), B.Octets.to_list(b)) : List<&2, U32>}

# every Octets is a valid byte string: to a list and back changes nothing
law octets_of_to:
  for o: B.Octets
  {B.Octets.of_list(B.Octets.to_list(o)) == o : B.Octets}

# a list becomes Octets by masking each element to its low 8 bits
law octets_to_of:
  for xs: List<&2, U32>
  {B.Octets.to_list(B.Octets.of_list(xs)) == B.mask(xs) : List<&2, U32>}

law octets_zeros_list:
  for n: Nat
  {B.Octets.to_list(B.Octets.zeros(n)) == B.zeros(n) : List<&2, U32>}

law octets_cons_list:
  for b: U32
  for o: B.Octets
  {B.Octets.to_list(B.Octets.cons(b, o)) == Con{B.byte(b), B.Octets.to_list(o)} : List<&2, U32>}

law octets_len_list:
  for o: B.Octets
  {B.Octets.len(o) == B.len(B.Octets.to_list(o)) : Nat}

# a joined string splits back exactly where it was joined
law octets_take_append:
  for +a: B.Octets
  for b: B.Octets
  {B.Octets.take(B.Octets.len(a), B.Octets.append(a, b)) == a : B.Octets}

law octets_drop_append:
  for a: B.Octets
  for +b: B.Octets
  {B.Octets.drop(B.Octets.len(a), B.Octets.append(a, b)) == b : B.Octets}

law octets_split_at_append:
  for +a: B.Octets
  for +b: B.Octets
  {B.Octets.split_at(B.Octets.len(a), B.Octets.append(a, b)) == Some{B.OctetsSplit{a, b}} : Maybe<&2, B.OctetsSplit>}

law octets_split_short:
  {B.Octets.split_at(4n, B.Octets.of_string("abc")) == None{} : Maybe<&2, B.OctetsSplit>}

law octets_split_text:
  {B.Octets.split_at(2n, B.Octets.of_string("abc")) == Some{B.OctetsSplit{B.Octets.of_string("ab"), B.Octets.of_string("c")}} : Maybe<&2, B.OctetsSplit>}

# The tail-recursive list layer: each fast form equals its structural form,
# for every input (stated structural == fast, the direction rewrites use, so
# that `%BL.len_fast(xs) : {... _ ...}` turns a fast form back into the one
# the other laws are about)

law len_fast:
  for xs: List<&2, U32>
  {B.len(xs) == B.len.fast(xs) : Nat}

law take_fast:
  for n: Nat
  for xs: List<&2, U32>
  {B.take(n, xs) == B.take.fast(n, xs) : List<&2, U32>}

law append_fast:
  for xs: List<&2, U32>
  for ys: List<&2, U32>
  {B.append(xs, ys) == B.append.fast(xs, ys) : List<&2, U32>}

law zeros_fast:
  for n: Nat
  {B.zeros(n) == B.zeros.fast(n) : List<&2, U32>}

law mask_fast:
  for xs: List<&2, U32>
  {B.mask(xs) == B.mask.fast(xs) : List<&2, U32>}

law of_string_fast:
  for s: String
  {B.of_string(s) == B.of_string.fast(s) : List<&2, U32>}

law to_string_fast:
  for xs: List<&2, U32>
  {B.to_string(xs) == B.to_string.fast(xs) : String}

law hex_fast:
  for xs: List<&2, U32>
  {B.hex(xs) == B.hex.fast(xs) : String}

law list_eq_fast:
  for xs: List<&2, U32>
  for ys: List<&2, U32>
  {B.list_eq(xs, ys) == B.list_eq.fast(xs, ys) : Bool}

law rev_rev:
  for xs: List<&2, U32>
  {B.rev(B.rev(xs)) == xs : List<&2, U32>}

# Octets' text and hex are the list layer's, and concat joins in order

law octets_hex_list:
  for o: B.Octets
  {B.Octets.hex(o) == B.hex(B.Octets.to_list(o)) : String}

law octets_to_string_list:
  for o: B.Octets
  {B.Octets.to_string(o) == B.to_string(B.Octets.to_list(o)) : String}

law octets_concat_nil:
  {B.Octets.concat(Nil{}) == B.Octets.empty() : B.Octets}

law octets_concat_cons:
  for h: B.Octets
  for t: List<&2, B.Octets>
  {B.Octets.concat(Con{h, t}) == B.Octets.append(h, B.Octets.concat(t)) : B.Octets}
