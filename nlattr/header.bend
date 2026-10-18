# bend-osdev-nlattr, the attribute header: two 16-bit fields (nla_len, the
# header and payload length; nla_type, the type and two flags) in host byte
# order, and the 4-byte alignment between attributes (RFC 3549 and the
# kernel's netlink documentation).
import Base

# the byte order of the header's 16-bit fields (the host's)
type NlOrder is Data:
  NlLittle{}
  NlBig{}

# the size of the header, and the alignment of attributes
def nla.hdrlen() -> Nat:
  4n

# the largest nla_len (a 16-bit field)
def nla.maxlen() -> Nat:
  65535n

# the largest type number (14 bits; the top two bits are flags)
def nla.maxtype() -> Nat:
  16383n

# the number of type values (types are 0 to 16383)
def nla.ntypes() -> Nat:
  16384n

# the flag values in the type field (NLA_F_NESTED = 32768,
# NLA_F_NET_BYTEORDER = 16384)
def nla.f_nested() -> Nat:
  Nat.add(16384n, 16384n)

def nla.f_netorder() -> Nat:
  16384n

# the zero bytes after an attribute of n bytes, up to the next multiple of 4
def nla.pad(n: Nat) -> Nat:
  Nat.mod(Nat.sub(4n, Nat.mod(n, 4n)), 4n)

# n rounded up to a multiple of 4 (NLA_ALIGN)
def nla.align(+n: Nat) -> Nat:
  Nat.add(n, nla.pad(n))

# the byte of a value below 256
def nla.byte(n: Nat) -> U32:
  U32.from_nat(n)

# whether n fits a 16-bit field: its high byte is below 256
def nla.fits16(+n: Nat) -> Bool:
  Nat.is_lt(Nat.div(n, 256n), 256n)

# a 16-bit field's two bytes, in buffer order
def nla.u16_bytes(o: NlOrder, +n: Nat, rest: List<&2, U32>) -> List<&2, U32>:
  match o:
    case NlLittle{}:
      Con{nla.byte(Nat.mod(n, 256n)), Con{nla.byte(Nat.div(n, 256n)), rest}}
    case NlBig{}:
      Con{nla.byte(Nat.div(n, 256n)), Con{nla.byte(Nat.mod(n, 256n)), rest}}

# a 16-bit field's value, from its two bytes in buffer order
def nla.u16_value(o: NlOrder, a: U32, b: U32) -> Nat:
  match o:
    case NlLittle{}:
      Nat.add(Nat.mul(U32.to_nat(b), 256n), U32.to_nat(a))
    case NlBig{}:
      Nat.add(Nat.mul(U32.to_nat(a), 256n), U32.to_nat(b))

# the type field's value: the type and its flags (NLA_F_NESTED, bit 15;
# NLA_F_NET_BYTEORDER, bit 14)
def nla.type_field(+t: Nat, nested: Bool, netorder: Bool) -> Nat:
  Nat.add(Bool.pick(Nat, nested, nla.f_nested(), 0n), Nat.add(Bool.pick(Nat, netorder, nla.f_netorder(), 0n), t))

# the high byte of the type field: the flags in its top two bits, the type's
# high 6 bits below them
def nla.type_hi(+t: Nat, nested: Bool, netorder: Bool) -> Nat:
  Nat.add(Bool.pick(Nat, nested, 128n, 0n), Nat.add(Bool.pick(Nat, netorder, 64n, 0n), Nat.div(t, 256n)))

# the type field's two bytes, in buffer order
def nla.type_bytes(o: NlOrder, +t: Nat, nested: Bool, netorder: Bool, rest: List<&2, U32>) -> List<&2, U32>:
  match o:
    case NlLittle{}:
      Con{nla.byte(Nat.mod(t, 256n)), Con{nla.byte(nla.type_hi(t, nested, netorder)), rest}}
    case NlBig{}:
      Con{nla.byte(nla.type_hi(t, nested, netorder)), Con{nla.byte(Nat.mod(t, 256n)), rest}}

# a type is below 16384: its high byte is below 64
def nla.type_ok(+t: Nat) -> Bool:
  Nat.is_lt(Nat.div(t, 256n), 64n)

def nla.has.go(+f: Nat, +flag: Nat, ge: Bool) -> Nat & Bool:
  match ge:
    case True{}:
      (Nat.sub(f, flag), True{})
    case False{}:
      (f, False{})

# a value with one flag bit taken off: the rest, and whether it was set
def nla.has(+f: Nat, +flag: Nat) -> Nat & Bool:
  nla.has.go(f, flag, Nat.is_le(flag, f))
