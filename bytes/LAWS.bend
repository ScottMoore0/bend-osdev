# DRAFT: not yet reviewed by the maintainer
#
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
