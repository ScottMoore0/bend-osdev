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

# Reading at an offset: lengths, take and drop at offsets, and what a byte
# or a field read inside joined, cut or sliced bytes gives (for dependents'
# proofs: a field at offset i of a ++ b is read from a when it ends inside
# a, and at i of b when it starts at len(a) + i)

law octets_len_append:
  for +a: B.Octets
  for +b: B.Octets
  {B.Octets.len(B.Octets.append(a, b)) == Nat.add(B.Octets.len(a), B.Octets.len(b)) : Nat}

law octets_len_take:
  for +n: Nat
  for +o: B.Octets
  {B.Octets.len(B.Octets.take(n, o)) == Nat.min(n, B.Octets.len(o)) : Nat}

law octets_len_take_le:
  for +n: Nat
  for +o: B.Octets
  for h: {Nat.is_le(n, B.Octets.len(o)) == True{} : Bool}
  {B.Octets.len(B.Octets.take(n, o)) == n : Nat}

law octets_len_drop:
  for +n: Nat
  for +o: B.Octets
  {B.Octets.len(B.Octets.drop(n, o)) == Nat.sub(B.Octets.len(o), n) : Nat}

law octets_len_slice:
  for +i: Nat
  for +n: Nat
  for +o: B.Octets
  {B.Octets.len(B.Octets.slice(i, n, o)) == Nat.min(n, Nat.sub(B.Octets.len(o), i)) : Nat}

law octets_len_slice_le:
  for +i: Nat
  for +n: Nat
  for +o: B.Octets
  for h: {Nat.is_le(Nat.add(i, n), B.Octets.len(o)) == True{} : Bool}
  {B.Octets.len(B.Octets.slice(i, n, o)) == n : Nat}

law octets_len_zeros:
  for +n: Nat
  {B.Octets.len(B.Octets.zeros(n)) == n : Nat}

law octets_len_of_list:
  for +xs: List<&2, U32>
  {B.Octets.len(B.Octets.of_list(xs)) == B.len(xs) : Nat}

law octets_append_assoc:
  for +a: B.Octets
  for +b: B.Octets
  for +c: B.Octets
  {B.Octets.append(B.Octets.append(a, b), c) == B.Octets.append(a, B.Octets.append(b, c)) : B.Octets}

law octets_append_empty_l:
  for +o: B.Octets
  {B.Octets.append(B.Octets.empty(), o) == o : B.Octets}

law octets_append_empty_r:
  for +o: B.Octets
  {B.Octets.append(o, B.Octets.empty()) == o : B.Octets}

law octets_drop_zero:
  for +o: B.Octets
  {B.Octets.drop(0n, o) == o : B.Octets}

law octets_take_len:
  for +o: B.Octets
  {B.Octets.take(B.Octets.len(o), o) == o : B.Octets}

# take and drop composed

law octets_drop_drop:
  for +j: Nat
  for +i: Nat
  for +o: B.Octets
  {B.Octets.drop(i, B.Octets.drop(j, o)) == B.Octets.drop(Nat.add(j, i), o) : B.Octets}

law octets_take_take:
  for +i: Nat
  for +j: Nat
  for +o: B.Octets
  {B.Octets.take(i, B.Octets.take(j, o)) == B.Octets.take(Nat.min(i, j), o) : B.Octets}

law octets_take_drop_comm:
  for +i: Nat
  for +j: Nat
  for +o: B.Octets
  {B.Octets.take(i, B.Octets.drop(j, o)) == B.Octets.drop(j, B.Octets.take(Nat.add(j, i), o)) : B.Octets}

law octets_drop_take_comm:
  for +i: Nat
  for +j: Nat
  for +o: B.Octets
  {B.Octets.drop(i, B.Octets.take(j, o)) == B.Octets.take(Nat.sub(j, i), B.Octets.drop(i, o)) : B.Octets}

# take and drop at offsets inside joined bytes

law octets_take_append_le:
  for +n: Nat
  for +a: B.Octets
  for +b: B.Octets
  for h: {Nat.is_le(n, B.Octets.len(a)) == True{} : Bool}
  {B.Octets.take(n, B.Octets.append(a, b)) == B.Octets.take(n, a) : B.Octets}

law octets_take_append_add:
  for +a: B.Octets
  for +n: Nat
  for +b: B.Octets
  {B.Octets.take(Nat.add(B.Octets.len(a), n), B.Octets.append(a, b)) == B.Octets.append(a, B.Octets.take(n, b)) : B.Octets}

law octets_drop_append_le:
  for +n: Nat
  for +a: B.Octets
  for +b: B.Octets
  for h: {Nat.is_le(n, B.Octets.len(a)) == True{} : Bool}
  {B.Octets.drop(n, B.Octets.append(a, b)) == B.Octets.append(B.Octets.drop(n, a), b) : B.Octets}

law octets_drop_append_add:
  for +a: B.Octets
  for +n: Nat
  for +b: B.Octets
  {B.Octets.drop(Nat.add(B.Octets.len(a), n), B.Octets.append(a, b)) == B.Octets.drop(n, b) : B.Octets}

# slices

law octets_slice_append_add:
  for +a: B.Octets
  for +i: Nat
  for +n: Nat
  for +b: B.Octets
  {B.Octets.slice(Nat.add(B.Octets.len(a), i), n, B.Octets.append(a, b)) == B.Octets.slice(i, n, b) : B.Octets}

law octets_slice_append_le:
  for +i: Nat
  for +n: Nat
  for +a: B.Octets
  for +b: B.Octets
  for h: {Nat.is_le(Nat.add(i, n), B.Octets.len(a)) == True{} : Bool}
  {B.Octets.slice(i, n, B.Octets.append(a, b)) == B.Octets.slice(i, n, a) : B.Octets}

law octets_slice_drop:
  for +j: Nat
  for +i: Nat
  for +n: Nat
  for +o: B.Octets
  {B.Octets.slice(i, n, B.Octets.drop(j, o)) == B.Octets.slice(Nat.add(j, i), n, o) : B.Octets}

law octets_slice_take:
  for +m: Nat
  for +i: Nat
  for +n: Nat
  for +o: B.Octets
  for h: {Nat.is_le(Nat.add(i, n), m) == True{} : Bool}
  {B.Octets.slice(i, n, B.Octets.take(m, o)) == B.Octets.slice(i, n, o) : B.Octets}

# a byte at an offset

law octets_at_list:
  for +o: B.Octets
  for +i: Nat
  {B.Octets.at(o, i) == B.at(B.Octets.to_list(o), i) : Maybe<&2, U32>}

law octets_at_append_add:
  for +a: B.Octets
  for +b: B.Octets
  for +i: Nat
  {B.Octets.at(B.Octets.append(a, b), Nat.add(B.Octets.len(a), i)) == B.Octets.at(b, i) : Maybe<&2, U32>}

law octets_at_append_lt:
  for +a: B.Octets
  for +b: B.Octets
  for +i: Nat
  for h: {Nat.is_lt(i, B.Octets.len(a)) == True{} : Bool}
  {B.Octets.at(B.Octets.append(a, b), i) == B.Octets.at(a, i) : Maybe<&2, U32>}

law octets_at_drop:
  for +j: Nat
  for +o: B.Octets
  for +i: Nat
  {B.Octets.at(B.Octets.drop(j, o), i) == B.Octets.at(o, Nat.add(j, i)) : Maybe<&2, U32>}

law octets_at_take:
  for +n: Nat
  for +o: B.Octets
  for +i: Nat
  for h: {Nat.is_lt(i, n) == True{} : Bool}
  {B.Octets.at(B.Octets.take(n, o), i) == B.Octets.at(o, i) : Maybe<&2, U32>}

# the list layer's at

law at_append_add:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +i: Nat
  {B.at(B.append(a, b), Nat.add(B.len(a), i)) == B.at(b, i) : Maybe<&2, U32>}

law at_append_lt:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +i: Nat
  for h: {Nat.is_lt(i, B.len(a)) == True{} : Bool}
  {B.at(B.append(a, b), i) == B.at(a, i) : Maybe<&2, U32>}

law at_drop:
  for +j: Nat
  for +xs: List<&2, U32>
  for +i: Nat
  {B.at(B.drop(j, xs), i) == B.at(xs, Nat.add(j, i)) : Maybe<&2, U32>}

law at_take:
  for +n: Nat
  for +xs: List<&2, U32>
  for +i: Nat
  for h: {Nat.is_lt(i, n) == True{} : Bool}
  {B.at(B.take(n, xs), i) == B.at(xs, i) : Maybe<&2, U32>}

# the fields' widths, and each field read at an offset: inside joined bytes
# (past the first part, or ending inside it), and inside cut bytes

law octets_len_le16:
  for +v: U32
  {B.Octets.len(B.Octets.le16(v)) == 2n : Nat}

law octets_len_be16:
  for +v: U32
  {B.Octets.len(B.Octets.be16(v)) == 2n : Nat}

law octets_len_le32:
  for +v: U32
  {B.Octets.len(B.Octets.le32(v)) == 4n : Nat}

law octets_len_be32:
  for +v: U32
  {B.Octets.len(B.Octets.be32(v)) == 4n : Nat}

law octets_len_le64:
  for +v: W.W64
  {B.Octets.len(B.Octets.le64(v)) == 8n : Nat}

law octets_len_be64:
  for +v: W.W64
  {B.Octets.len(B.Octets.be64(v)) == 8n : Nat}

law octets_le16_at_append_add:
  for +a: B.Octets
  for +b: B.Octets
  for +i: Nat
  {B.Octets.le16_at(B.Octets.append(a, b), Nat.add(B.Octets.len(a), i)) == B.Octets.le16_at(b, i) : Maybe<&2, U32>}

law octets_le16_at_append_le:
  for +a: B.Octets
  for +b: B.Octets
  for +i: Nat
  for h: {Nat.is_le(Nat.add(i, 2n), B.Octets.len(a)) == True{} : Bool}
  {B.Octets.le16_at(B.Octets.append(a, b), i) == B.Octets.le16_at(a, i) : Maybe<&2, U32>}

law octets_le16_at_drop:
  for +j: Nat
  for +o: B.Octets
  for +i: Nat
  {B.Octets.le16_at(B.Octets.drop(j, o), i) == B.Octets.le16_at(o, Nat.add(j, i)) : Maybe<&2, U32>}

law octets_le16_at_take:
  for +n: Nat
  for +o: B.Octets
  for +i: Nat
  for h: {Nat.is_le(Nat.add(i, 2n), n) == True{} : Bool}
  {B.Octets.le16_at(B.Octets.take(n, o), i) == B.Octets.le16_at(o, i) : Maybe<&2, U32>}

law octets_be16_at_append_add:
  for +a: B.Octets
  for +b: B.Octets
  for +i: Nat
  {B.Octets.be16_at(B.Octets.append(a, b), Nat.add(B.Octets.len(a), i)) == B.Octets.be16_at(b, i) : Maybe<&2, U32>}

law octets_be16_at_append_le:
  for +a: B.Octets
  for +b: B.Octets
  for +i: Nat
  for h: {Nat.is_le(Nat.add(i, 2n), B.Octets.len(a)) == True{} : Bool}
  {B.Octets.be16_at(B.Octets.append(a, b), i) == B.Octets.be16_at(a, i) : Maybe<&2, U32>}

law octets_be16_at_drop:
  for +j: Nat
  for +o: B.Octets
  for +i: Nat
  {B.Octets.be16_at(B.Octets.drop(j, o), i) == B.Octets.be16_at(o, Nat.add(j, i)) : Maybe<&2, U32>}

law octets_be16_at_take:
  for +n: Nat
  for +o: B.Octets
  for +i: Nat
  for h: {Nat.is_le(Nat.add(i, 2n), n) == True{} : Bool}
  {B.Octets.be16_at(B.Octets.take(n, o), i) == B.Octets.be16_at(o, i) : Maybe<&2, U32>}

law octets_le32_at_append_add:
  for +a: B.Octets
  for +b: B.Octets
  for +i: Nat
  {B.Octets.le32_at(B.Octets.append(a, b), Nat.add(B.Octets.len(a), i)) == B.Octets.le32_at(b, i) : Maybe<&2, U32>}

law octets_le32_at_append_le:
  for +a: B.Octets
  for +b: B.Octets
  for +i: Nat
  for h: {Nat.is_le(Nat.add(i, 4n), B.Octets.len(a)) == True{} : Bool}
  {B.Octets.le32_at(B.Octets.append(a, b), i) == B.Octets.le32_at(a, i) : Maybe<&2, U32>}

law octets_le32_at_drop:
  for +j: Nat
  for +o: B.Octets
  for +i: Nat
  {B.Octets.le32_at(B.Octets.drop(j, o), i) == B.Octets.le32_at(o, Nat.add(j, i)) : Maybe<&2, U32>}

law octets_le32_at_take:
  for +n: Nat
  for +o: B.Octets
  for +i: Nat
  for h: {Nat.is_le(Nat.add(i, 4n), n) == True{} : Bool}
  {B.Octets.le32_at(B.Octets.take(n, o), i) == B.Octets.le32_at(o, i) : Maybe<&2, U32>}

law octets_be32_at_append_add:
  for +a: B.Octets
  for +b: B.Octets
  for +i: Nat
  {B.Octets.be32_at(B.Octets.append(a, b), Nat.add(B.Octets.len(a), i)) == B.Octets.be32_at(b, i) : Maybe<&2, U32>}

law octets_be32_at_append_le:
  for +a: B.Octets
  for +b: B.Octets
  for +i: Nat
  for h: {Nat.is_le(Nat.add(i, 4n), B.Octets.len(a)) == True{} : Bool}
  {B.Octets.be32_at(B.Octets.append(a, b), i) == B.Octets.be32_at(a, i) : Maybe<&2, U32>}

law octets_be32_at_drop:
  for +j: Nat
  for +o: B.Octets
  for +i: Nat
  {B.Octets.be32_at(B.Octets.drop(j, o), i) == B.Octets.be32_at(o, Nat.add(j, i)) : Maybe<&2, U32>}

law octets_be32_at_take:
  for +n: Nat
  for +o: B.Octets
  for +i: Nat
  for h: {Nat.is_le(Nat.add(i, 4n), n) == True{} : Bool}
  {B.Octets.be32_at(B.Octets.take(n, o), i) == B.Octets.be32_at(o, i) : Maybe<&2, U32>}

law octets_le64_at_append_add:
  for +a: B.Octets
  for +b: B.Octets
  for +i: Nat
  {B.Octets.le64_at(B.Octets.append(a, b), Nat.add(B.Octets.len(a), i)) == B.Octets.le64_at(b, i) : Maybe<&2, W.W64>}

law octets_le64_at_append_le:
  for +a: B.Octets
  for +b: B.Octets
  for +i: Nat
  for h: {Nat.is_le(Nat.add(i, 8n), B.Octets.len(a)) == True{} : Bool}
  {B.Octets.le64_at(B.Octets.append(a, b), i) == B.Octets.le64_at(a, i) : Maybe<&2, W.W64>}

law octets_le64_at_drop:
  for +j: Nat
  for +o: B.Octets
  for +i: Nat
  {B.Octets.le64_at(B.Octets.drop(j, o), i) == B.Octets.le64_at(o, Nat.add(j, i)) : Maybe<&2, W.W64>}

law octets_le64_at_take:
  for +n: Nat
  for +o: B.Octets
  for +i: Nat
  for h: {Nat.is_le(Nat.add(i, 8n), n) == True{} : Bool}
  {B.Octets.le64_at(B.Octets.take(n, o), i) == B.Octets.le64_at(o, i) : Maybe<&2, W.W64>}

law octets_be64_at_append_add:
  for +a: B.Octets
  for +b: B.Octets
  for +i: Nat
  {B.Octets.be64_at(B.Octets.append(a, b), Nat.add(B.Octets.len(a), i)) == B.Octets.be64_at(b, i) : Maybe<&2, W.W64>}

law octets_be64_at_append_le:
  for +a: B.Octets
  for +b: B.Octets
  for +i: Nat
  for h: {Nat.is_le(Nat.add(i, 8n), B.Octets.len(a)) == True{} : Bool}
  {B.Octets.be64_at(B.Octets.append(a, b), i) == B.Octets.be64_at(a, i) : Maybe<&2, W.W64>}

law octets_be64_at_drop:
  for +j: Nat
  for +o: B.Octets
  for +i: Nat
  {B.Octets.be64_at(B.Octets.drop(j, o), i) == B.Octets.be64_at(o, Nat.add(j, i)) : Maybe<&2, W.W64>}

law octets_be64_at_take:
  for +n: Nat
  for +o: B.Octets
  for +i: Nat
  for h: {Nat.is_le(Nat.add(i, 8n), n) == True{} : Bool}
  {B.Octets.be64_at(B.Octets.take(n, o), i) == B.Octets.be64_at(o, i) : Maybe<&2, W.W64>}

# a value already masked to 16 bits is its own low16 (so a 16-bit field
# written from such a value reads back as that value)

law low16_mask:
  for +v: U32
  {B.low16(U32.and(v, 65535)) == U32.and(v, 65535) : U32}
