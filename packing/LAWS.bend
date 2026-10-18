# Properties, for every quirk setting, buffer, field and value:
#
# * the view of a buffer as bits and back are inverse: a list of 8n bits
#   made into bytes and viewed again is itself; viewing ignores everything
#   but each element's low 8 bits; the view has 8 bits per byte;
# * unpacking a field just packed gives the value packed (or, masked, its
#   low bits);
# * packing changes no bit outside the field, and keeps the buffer's
#   length.
#
# Vectors: fields under each quirk, and the errors.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./view.bend as V
import ./field.bend as F
import ./packing.bend as P

# The view

law view_unview:
  for +q: V.PkQuirks
  for +bs: List<&2, Bool>
  for +n: Nat
  for +h: {List.length(&2, Bool, bs) == Nat.mul(n, 8n) : Nat}
  {V.packing.view(q, V.packing.unview(q, bs)) == bs : List<&2, Bool>}

law view_mask:
  for +q: V.PkQuirks
  for +xs: List<&2, U32>
  {V.packing.view(q, B.mask(xs)) == V.packing.view(q, xs) : List<&2, Bool>}

law view_len:
  for +q: V.PkQuirks
  for +xs: List<&2, U32>
  {List.length(&2, Bool, V.packing.view(q, xs)) == Nat.mul(List.length(&2, U32, xs), 8n) : Nat}

law unview_len:
  for +q: V.PkQuirks
  for +bs: List<&2, Bool>
  for +n: Nat
  for +h: {List.length(&2, Bool, bs) == Nat.mul(n, 8n) : Nat}
  {List.length(&2, U32, V.packing.unview(q, bs)) == n : Nat}

# Values

law value_bits:
  for +v: W.W64
  {F.packing.bits_w64(F.packing.w64_bits(v)) == v : W.W64}

# Packing and unpacking

law unpack_pack:
  for +q: V.PkQuirks
  for +buf: B.Octets
  for +start: Nat
  for +end: Nat
  for +v: W.W64
  for +b: B.Octets
  for +e: {P.packing.pack(q, buf, start, end, v) == Done{b} : Result<&2, &2, P.PkError, B.Octets>}
  {P.packing.unpack(q, b, start, end) == Done{v} : Result<&2, &2, P.PkError, W.W64>}

law unpack_pack_masked:
  for +q: V.PkQuirks
  for +buf: B.Octets
  for +start: Nat
  for +end: Nat
  for +v: W.W64
  for +b: B.Octets
  for +e: {P.packing.pack_masked(q, buf, start, end, v) == Done{b} : Result<&2, &2, P.PkError, B.Octets>}
  {P.packing.unpack(q, b, start, end) == Done{F.packing.low(v, P.packing.width(start, end))} : Result<&2, &2, P.PkError, W.W64>}

law pack_rest:
  for +q: V.PkQuirks
  for +buf: B.Octets
  for +start: Nat
  for +end: Nat
  for +v: W.W64
  for +b: B.Octets
  for +e: {P.packing.pack(q, buf, start, end, v) == Done{b} : Result<&2, &2, P.PkError, B.Octets>}
  for +k: Nat
  for +h: {Bool.or(Nat.is_lt(k, end), Nat.is_lt(start, k)) == True{} : Bool}
  {P.packing.bit(q, b, k) == P.packing.bit(q, buf, k) : Bool}

law pack_masked_rest:
  for +q: V.PkQuirks
  for +buf: B.Octets
  for +start: Nat
  for +end: Nat
  for +v: W.W64
  for +b: B.Octets
  for +e: {P.packing.pack_masked(q, buf, start, end, v) == Done{b} : Result<&2, &2, P.PkError, B.Octets>}
  for +k: Nat
  for +h: {Bool.or(Nat.is_lt(k, end), Nat.is_lt(start, k)) == True{} : Bool}
  {P.packing.bit(q, b, k) == P.packing.bit(q, buf, k) : Bool}

law pack_len:
  for +q: V.PkQuirks
  for +buf: B.Octets
  for +start: Nat
  for +end: Nat
  for +v: W.W64
  for +b: B.Octets
  for +e: {P.packing.pack(q, buf, start, end, v) == Done{b} : Result<&2, &2, P.PkError, B.Octets>}
  {B.Octets.len(b) == B.Octets.len(buf) : Nat}

# Vectors

law vec_plain:
  {P.packing.pack(V.packing.quirks_none(), B.Octets.zeros(4n), 15n, 8n, W.W64.from_u32(171)) == Done{B.Octets.of_list([0, 0, 171, 0])} : Result<&2, &2, P.PkError, B.Octets>}

law vec_little_endian:
  {P.packing.pack(V.PkQuirks{False{}, True{}, False{}}, B.Octets.zeros(4n), 15n, 8n, W.W64.from_u32(171)) == Done{B.Octets.of_list([0, 171, 0, 0])} : Result<&2, &2, P.PkError, B.Octets>}

law vec_msb_right:
  {P.packing.pack(V.PkQuirks{True{}, False{}, False{}}, B.Octets.zeros(4n), 7n, 0n, W.W64.from_u32(1)) == Done{B.Octets.of_list([0, 0, 0, 128])} : Result<&2, &2, P.PkError, B.Octets>}

law vec_lsw32_first:
  {P.packing.pack(V.PkQuirks{False{}, False{}, True{}}, B.Octets.zeros(8n), 7n, 0n, W.W64.from_u32(5)) == Done{B.Octets.of_list([0, 0, 0, 5, 0, 0, 0, 0])} : Result<&2, &2, P.PkError, B.Octets>}

law vec_unpack:
  {P.packing.unpack(V.packing.quirks_none(), B.Octets.of_list([18, 52, 86, 120]), 19n, 4n) == Done{W.W64.from_u32(17767)} : Result<&2, &2, P.PkError, W.W64>}

law vec_errors:
  {(P.packing.unpack(V.packing.quirks_none(), B.Octets.zeros(4n), 3n, 5n), P.packing.unpack(V.packing.quirks_none(), B.Octets.zeros(4n), 32n, 0n), P.packing.unpack(V.PkQuirks{False{}, True{}, False{}}, B.Octets.zeros(6n), 7n, 0n), P.packing.pack(V.packing.quirks_none(), B.Octets.zeros(4n), 7n, 0n, W.W64.from_u32(300))) == (Fail{P.PkBadRange{}}, Fail{P.PkOutOfBuffer{}}, Fail{P.PkBadLength{}}, Fail{P.PkOverflow{}}) : Result<&2, &2, P.PkError, W.W64> & Result<&2, &2, P.PkError, W.W64> & Result<&2, &2, P.PkError, W.W64> & Result<&2, &2, P.PkError, B.Octets>}
