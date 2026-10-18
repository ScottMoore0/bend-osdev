# bend-osdev-nlattr: netlink attributes (RFC 3549 and the kernel's netlink
# documentation): type-length-value records with a 4-byte header and 4-byte
# alignment, nested attributes, and the NLA_F_NESTED and
# NLA_F_NET_BYTEORDER flags. Building, parsing (here), and validation
# against a policy (policy.bend).
#
# An attribute is NlAttr{type, nested, netorder, payload}: the 14-bit type,
# the two flags, and the payload bytes. A nested attribute's payload is
# itself a run of attributes: build it with nla.build and parse it with
# nla.parse.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./header.bend as H

type NlAttr is Data:
  NlAttr{kind: Nat, nested: Bool, netorder: Bool, payload: B.Octets}

type NlError is Data:
  NlBadType{kind: Nat}
  NlTooLong{kind: Nat}
  NlBadLength{}
  NlTrailing{}
  NlUnknown{kind: Nat}
  NlTooShort{kind: Nat}
  NlTooLarge{kind: Nat}
  NlNoNul{kind: Nat}
  NlNotFlag{kind: Nat}
  NlNoNestedFlag{kind: Nat}
  NlTooDeep{}

# How to parse: the header's byte order, and whether bytes left after the
# last attribute (fewer than a header) are an error
type NlOpts is Data:
  NlOpts{order: H.NlOrder, strict: Bool}

# the usual choices: the host's order (little-endian here), strict
def nla.opts_default() -> NlOpts:
  NlOpts{H.NlLittle{}, True{}}

def nla.opts_liberal(o: H.NlOrder) -> NlOpts:
  NlOpts{o, False{}}

def nla.opts.order(p: NlOpts) -> H.NlOrder:
  match p:
    case NlOpts{o, s}:
      o

def nla.opts.strict(p: NlOpts) -> Bool:
  match p:
    case NlOpts{o, s}:
      s

def nla.attr(+t: Nat, p: B.Octets) -> NlAttr:
  NlAttr{t, False{}, False{}, p}

# a nested attribute whose payload is inner, already built (nla_nest_start
# with NLA_F_NESTED, the kernel's default for new code)
def nla.nest(+t: Nat, inner: B.Octets) -> NlAttr:
  NlAttr{t, True{}, False{}, inner}

def nla.type(a: NlAttr) -> Nat:
  match a:
    case NlAttr{t, nd, nb, p}:
      t

def nla.payload(a: NlAttr) -> B.Octets:
  match a:
    case NlAttr{t, nd, nb, p}:
      p

def nla.is_nested(a: NlAttr) -> Bool:
  match a:
    case NlAttr{t, nd, nb, p}:
      nd

# Building

def nla.len_of(a: NlAttr) -> Nat:
  match a:
    case NlAttr{t, nd, nb, p}:
      Nat.add(H.nla.hdrlen(), B.Octets.len(p))

# an attribute can be built: its type is below 16384, and its length fits
# 16 bits
def nla.ok(+a: NlAttr) -> Bool:
  Bool.and(H.nla.type_ok(nla.type(a)), H.nla.fits16(nla.len_of(a)))

def nla.err.pick(ok: Bool, +t: Nat) -> NlError:
  match ok:
    case True{}:
      NlTooLong{t}
    case False{}:
      NlBadType{t}

# why an attribute cannot be built
def nla.err(+a: NlAttr) -> NlError:
  nla.err.pick(H.nla.type_ok(nla.type(a)), nla.type(a))

# an attribute's bytes before rest: header, payload, zero padding
def nla.enc(+o: H.NlOrder, a: NlAttr, rest: List<&2, U32>) -> List<&2, U32>:
  match a:
    case NlAttr{+t, nd, nb, p}:
      +ps = B.Octets.to_list(p)
      +n = Nat.add(H.nla.hdrlen(), List.length(&2, U32, ps))
      H.nla.u16_bytes(o, n, H.nla.type_bytes(o, t, nd, nb, List.append(&2, U32, ps, List.append(&2, U32, B.zeros(H.nla.pad(n)), rest))))

def nla.enc_all(+o: H.NlOrder, as: List<&2, NlAttr>) -> List<&2, U32>:
  match as:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      nla.enc(o, a, nla.enc_all(o, t))

def nla.first_err.pick(ok: Bool, +a: NlAttr, r: Maybe<&2, NlError>) -> Maybe<&2, NlError>:
  match ok:
    case True{}:
      r
    case False{}:
      Some{nla.err(a)}

# the error of the first attribute that cannot be built
def nla.first_err(as: List<&2, NlAttr>) -> Maybe<&2, NlError>:
  match as:
    case Nil{}:
      None{}
    case Con{+a, t}:
      nla.first_err.pick(nla.ok(a), a, nla.first_err(t))

def nla.build.go(m: Maybe<&2, NlError>, +o: H.NlOrder, as: List<&2, NlAttr>) -> Result<&2, &2, NlError, B.Octets>:
  match m:
    case None{}:
      Done{B.Octets.of_list(nla.enc_all(o, as))}
    case Some{e}:
      Fail{e}

# the attributes one after another, each padded to 4 bytes with zeros
# (nla_put for each); NlBadType for a type above 14 bits, NlTooLong for a
# payload that does not fit nla_len
def nla.build(+o: H.NlOrder, +as: List<&2, NlAttr>) -> Result<&2, &2, NlError, B.Octets>:
  nla.build.go(nla.first_err(as), o, as)

# one attribute's bytes
def nla.put(+o: H.NlOrder, a: NlAttr) -> Result<&2, &2, NlError, B.Octets>:
  nla.build(o, [a])

# Parsing

def nla.parse.cons(a: NlAttr, r: Result<&2, &2, NlError, List<&2, NlAttr>>) -> Result<&2, &2, NlError, List<&2, NlAttr>>:
  Result.map(&2, &2, NlError, List<&2, NlAttr>, List<&2, NlAttr>, as => Con{a, as}, r)

def nla.parse.attr2(r: Nat & Bool, nd: Bool, +lo: Nat, p: List<&2, U32>) -> NlAttr:
  (h, nb) = r
  NlAttr{Nat.add(Nat.mul(h, 256n), lo), nd, nb, B.Octets.of_list(p)}

def nla.parse.attr1(r: Nat & Bool, +lo: Nat, p: List<&2, U32>) -> NlAttr:
  (h, nd) = r
  nla.parse.attr2(H.nla.has(h, 64n), nd, lo, p)

# the attribute of the type field's high and low bytes and payload p
def nla.parse.attr(hi: U32, lo: U32, p: List<&2, U32>) -> NlAttr:
  nla.parse.attr1(H.nla.has(U32.to_nat(hi), 128n), U32.to_nat(lo), p)

# the type field's high and low bytes, from its bytes in buffer order
def nla.parse.attr_o(o: H.NlOrder, a: U32, b: U32, p: List<&2, U32>) -> NlAttr:
  match o:
    case H.NlLittle{}:
      nla.parse.attr(b, a, p)
    case H.NlBig{}:
      nla.parse.attr(a, b, p)

# the bytes after the n of an attribute and its padding (fewer padding
# bytes are accepted at the end, as the kernel does)
def nla.parse.rest(+n: Nat, rest: List<&2, U32>) -> List<&2, U32>:
  List.drop(&2, U32, List.drop(&2, U32, rest, Nat.sub(n, H.nla.hdrlen())), H.nla.pad(n))

def nla.parse.short(strict: Bool) -> Result<&2, &2, NlError, List<&2, NlAttr>>:
  match strict:
    case True{}:
      Fail{NlTrailing{}}
    case False{}:
      Done{Nil{}}

def nla.parse.check(ok: Bool, +o: H.NlOrder, b2: U32, b3: U32, +n: Nat, rest: List<&2, U32>, r: Result<&2, &2, NlError, List<&2, NlAttr>>) -> Result<&2, &2, NlError, List<&2, NlAttr>>:
  match ok:
    case True{}:
      nla.parse.cons(nla.parse.attr_o(o, b2, b3, List.take(&2, U32, rest, Nat.sub(n, H.nla.hdrlen()))), r)
    case False{}:
      Fail{NlBadLength{}}

# fuel bounds the attributes (each takes 4 bytes or more): the length
# of the bytes is enough
def nla.parse.go(fuel: Nat, +p: NlOpts, xs: List<&2, U32>) -> Result<&2, &2, NlError, List<&2, NlAttr>>:
  match fuel xs:
    case _ Nil{}:
      Done{Nil{}}
    case 0n Con{x, t}:
      nla.parse.short(nla.opts.strict(p))
    case 1n+f Con{+b0, Con{+b1, Con{+b2, Con{+b3, +rest}}}}:
      +o = nla.opts.order(p)
      +n = H.nla.u16_value(o, b0, b1)
      nla.parse.check(Bool.and(Nat.is_le(H.nla.hdrlen(), n), Nat.is_le(Nat.sub(n, H.nla.hdrlen()), List.length(&2, U32, rest))), o, b2, b3, n, rest, nla.parse.go(f, p, nla.parse.rest(n, rest)))
    case 1n+f Con{x, t}:
      nla.parse.short(nla.opts.strict(p))

# the attributes of buf, in order; NlBadLength for an nla_len below 4 or past
# the end, NlTrailing (when strict) for bytes left that are not a header
def nla.parse(+p: NlOpts, buf: B.Octets) -> Result<&2, &2, NlError, List<&2, NlAttr>>:
  +xs = B.Octets.to_list(buf)
  nla.parse.go(List.length(&2, U32, xs), p, xs)

# Reading attributes

def nla.find.pick(hit: Bool, a: NlAttr, r: Maybe<&2, NlAttr>) -> Maybe<&2, NlAttr>:
  match hit:
    case True{}:
      Some{a}
    case False{}:
      r

# the first attribute of type t (nla_find)
def nla.find(as: List<&2, NlAttr>, +t: Nat) -> Maybe<&2, NlAttr>:
  match as:
    case Nil{}:
      None{}
    case Con{+a, r}:
      nla.find.pick(Nat.is_eq(nla.type(a), t), a, nla.find(r, t))

# the byte order of an attribute's integer payload: network order when
# NLA_F_NET_BYTEORDER is set, else the host's
def nla.big(o: H.NlOrder, nb: Bool) -> Bool:
  match o nb:
    case _ True{}:
      True{}
    case H.NlBig{} False{}:
      True{}
    case H.NlLittle{} False{}:
      False{}

def nla.get_u8(a: NlAttr) -> Maybe<&2, U32>:
  match a:
    case NlAttr{t, nd, nb, p}:
      B.Octets.at(p, 0n)

def nla.get_u16.at(big: Bool, p: B.Octets) -> Maybe<&2, U32>:
  match big:
    case True{}:
      B.Octets.be16_at(p, 0n)
    case False{}:
      B.Octets.le16_at(p, 0n)

def nla.get_u16(o: H.NlOrder, a: NlAttr) -> Maybe<&2, U32>:
  match a:
    case NlAttr{t, nd, nb, p}:
      nla.get_u16.at(nla.big(o, nb), p)

def nla.get_u32.at(big: Bool, p: B.Octets) -> Maybe<&2, U32>:
  match big:
    case True{}:
      B.Octets.be32_at(p, 0n)
    case False{}:
      B.Octets.le32_at(p, 0n)

def nla.get_u32(o: H.NlOrder, a: NlAttr) -> Maybe<&2, U32>:
  match a:
    case NlAttr{t, nd, nb, p}:
      nla.get_u32.at(nla.big(o, nb), p)

def nla.get_u64.at(big: Bool, p: B.Octets) -> Maybe<&2, W.W64>:
  match big:
    case True{}:
      B.Octets.be64_at(p, 0n)
    case False{}:
      B.Octets.le64_at(p, 0n)

def nla.get_u64(o: H.NlOrder, a: NlAttr) -> Maybe<&2, W.W64>:
  match a:
    case NlAttr{t, nd, nb, p}:
      nla.get_u64.at(nla.big(o, nb), p)

# Making attributes

def nla.u8(+t: Nat, v: U32) -> NlAttr:
  nla.attr(t, B.Octets.of_list([v]))

def nla.u16(o: H.NlOrder, +t: Nat, v: U32) -> NlAttr:
  match o:
    case H.NlLittle{}:
      nla.attr(t, B.Octets.le16(v))
    case H.NlBig{}:
      nla.attr(t, B.Octets.be16(v))

def nla.u32(o: H.NlOrder, +t: Nat, v: U32) -> NlAttr:
  match o:
    case H.NlLittle{}:
      nla.attr(t, B.Octets.le32(v))
    case H.NlBig{}:
      nla.attr(t, B.Octets.be32(v))

# a 32-bit value in network order, flagged NLA_F_NET_BYTEORDER
def nla.u32_be(+t: Nat, v: U32) -> NlAttr:
  NlAttr{t, False{}, True{}, B.Octets.be32(v)}

def nla.u64(o: H.NlOrder, +t: Nat, +v: W.W64) -> NlAttr:
  match o:
    case H.NlLittle{}:
      nla.attr(t, B.Octets.le64(v))
    case H.NlBig{}:
      nla.attr(t, B.Octets.be64(v))

# a string with its terminating NUL (nla_put_string)
def nla.string(+t: Nat, s: String) -> NlAttr:
  nla.attr(t, B.Octets.append(B.Octets.of_string(s), B.Octets.zeros(1n)))

# a flag: no payload (nla_put_flag)
def nla.flag(+t: Nat) -> NlAttr:
  nla.attr(t, B.Octets.empty())

# the bytes the attributes' headers and payloads take (their padding not
# counted)
def nla.span(as: List<&2, NlAttr>) -> Nat:
  match as:
    case Nil{}:
      0n
    case Con{a, t}:
      Nat.add(nla.len_of(a), nla.span(t))
