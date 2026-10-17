# The Internet checksum (RFC 1071): the 16-bit one's complement of the one's
# complement sum of the data's 16-bit big-endian words, an odd final byte
# padded with a zero byte. IPv4, ICMP, ICMPv6, UDP and TCP use it.
#
# The sum can be computed in pieces: inet_start, then inet_update with each
# piece (every piece but the last of an even length, so that the 16-bit
# words line up), then inet_finish. inet_checksum does the three in a row.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B

# the 16-bit word of two bytes, the first most significant
def inet_word(a: U32, b: U32) -> U32:
  match a b:
    case U32{x} U32{y}:
      U32{W.W64.bits.cat(8n, 24n, W.W64.bits.lo(8n, 24n, y), W.W64.bits.cat(8n, 16n, W.W64.bits.lo(8n, 24n, x), Word.zero(16n)))}

# one's complement addition of two 16-bit values: add, then fold the carry
# back in (the end-around carry)
def inet_add(acc: U32, w: U32) -> U32:
  +s = U32.add(acc, w)
  U32.add(U32.and(s, 65535), U32.shrn(s, 16n))

def inet_sum.list(xs: List<&2, U32>, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{a, Nil{}}:
      inet_add(acc, inet_word(a, 0))
    case Con{a, Con{b, t}}:
      inet_sum.list(t, inet_add(acc, inet_word(a, b)))

def inet_even.list(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{a, Nil{}}:
      False{}
    case Con{a, Con{b, t}}:
      inet_even.list(t)

# The sum, in pieces

# the sum of no data
def inet_start() -> U32:
  0

# the 16-bit sum acc with the words of o added (an odd final byte padded)
def inet_update(acc: U32, o: B.Octets) -> U32:
  inet_sum.list(B.Octets.to_list(o), acc)

# the checksum of data whose sum is acc: its one's complement
def inet_finish(acc: U32) -> U32:
  U32.and(65535, U32.not(acc))

# whether o has an even number of bytes: whether more data may follow it in
# the same sum
def inet_even(o: B.Octets) -> Bool:
  inet_even.list(B.Octets.to_list(o))

# One shot

# the one's complement sum of o
def inet_sum(o: B.Octets) -> U32:
  inet_update(inet_start(), o)

# the checksum of o
def inet_checksum(o: B.Octets) -> U32:
  inet_finish(inet_sum(o))

# whether data that includes its checksum verifies: its sum is all ones
def inet_verify(o: B.Octets) -> Bool:
  U32.is_eq(inet_sum(o), 65535)

# Writing a checksum

# o with the 16-bit big-endian field at offset off replaced by v
def inet_put16(+o: B.Octets, +off: Nat, v: U32) -> B.Octets:
  B.Octets.append(B.Octets.take(off, o), B.Octets.append(B.Octets.be16(v), B.Octets.drop(Nat.add(off, 2n), o)))

# o with the checksum of pseudo ++ o written into its 16-bit field at offset
# off (whatever the field held counts as zero); pseudo is the pseudo-header
# the checksum also covers, or empty
def inet_fill(pseudo: B.Octets, +o: B.Octets, +off: Nat) -> B.Octets:
  inet_put16(o, off, inet_checksum(B.Octets.append(pseudo, inet_put16(o, off, 0))))
