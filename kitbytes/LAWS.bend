# Vectors: converting to bend-kit's Bytes and back gives the same Octets, and
# a buffer bend-kit built itself converts to the bytes it holds. A proof for
# every input would have to reason about bend-kit's array internals, which
# bend-osdev does not do; these are vectors only.
import Base
import ../bytes/bytes.bend as B
import bend-kit-bytes@0.3.2.0/bytes.bend as KB
import ./kitbytes.bend as K

def second(r: KB.Bytes & B.Octets) -> B.Octets:
  (b, o) = r
  o

law round_trip_text:
  {K.round_trip(B.Octets.of_string("bend-osdev")) == B.Octets.of_string("bend-osdev") : B.Octets}

law round_trip_bytes:
  {K.round_trip(B.Octets.of_list([0, 1, 127, 128, 254, 255])) == B.Octets.of_list([0, 1, 127, 128, 254, 255]) : B.Octets}

law round_trip_empty:
  {K.round_trip(B.Octets.empty()) == B.Octets.empty() : B.Octets}

law from_kit:
  {second(K.to_octets(KB.from_string("kernel"))) == B.Octets.of_string("kernel") : B.Octets}
