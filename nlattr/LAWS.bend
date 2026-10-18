# Properties, for every byte order, list of attributes and buffer:
#
# * parsing what build made gives the attributes back (strict or liberal);
# * an attribute's alignment padding is zero bytes, and a built attribute
#   is a whole number of 4-byte words;
# * a parse that succeeds, with or without a policy, reads nothing past the
#   buffer: the attributes' headers and payloads fit in it; and a parse
#   with a policy answers what the plain parse answers.
#
# Vectors: building and parsing small attributes, and the errors.
import Base
import ../bytes/bytes.bend as B
import ./header.bend as H
import ./nlattr.bend as N
import ./policy.bend as P

law parse_build:
  for +o: H.NlOrder
  for +s: Bool
  for +as: List<&2, N.NlAttr>
  for +b: B.Octets
  for +e: {N.nla.build(o, as) == Done{b} : Result<&2, &2, N.NlError, B.Octets>}
  {N.nla.parse(N.NlOpts{o, s}, b) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}

law pad_zero:
  for +o: H.NlOrder
  for +a: N.NlAttr
  for +b: B.Octets
  for +e: {N.nla.put(o, a) == Done{b} : Result<&2, &2, N.NlError, B.Octets>}
  {B.Octets.drop(N.nla.len_of(a), b) == B.Octets.zeros(H.nla.pad(N.nla.len_of(a))) : B.Octets}

law put_len:
  for +o: H.NlOrder
  for +a: N.NlAttr
  for +b: B.Octets
  for +e: {N.nla.put(o, a) == Done{b} : Result<&2, &2, N.NlError, B.Octets>}
  {B.Octets.len(b) == H.nla.align(N.nla.len_of(a)) : Nat}

law parse_within:
  for +p: N.NlOpts
  for +buf: B.Octets
  for +as: List<&2, N.NlAttr>
  for +e: {N.nla.parse(p, buf) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
  {Nat.is_le(N.nla.span(as), B.Octets.len(buf)) == True{} : Bool}

law parse_policy_parse:
  for +c: P.NlCheck
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +buf: B.Octets
  for +as: List<&2, N.NlAttr>
  for +e: {P.nla.parse_policy(c, set, pol, buf) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
  {N.nla.parse(P.nla.check.parse(c), buf) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}

law parse_policy_within:
  for +c: P.NlCheck
  for +set: List<&2, P.NlPolicy>
  for +pol: Nat
  for +buf: B.Octets
  for +as: List<&2, N.NlAttr>
  for +e: {P.nla.parse_policy(c, set, pol, buf) == Done{as} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
  {Nat.is_le(N.nla.span(as), B.Octets.len(buf)) == True{} : Bool}

# Vectors

law vec_u32:
  {N.nla.put(H.NlLittle{}, N.nla.u32(H.NlLittle{}, 4n, 1500)) == Done{B.Octets.of_list([8, 0, 4, 0, 220, 5, 0, 0])} : Result<&2, &2, N.NlError, B.Octets>}

law vec_string:
  {N.nla.put(H.NlLittle{}, N.nla.string(3n, "lo")) == Done{B.Octets.of_list([7, 0, 3, 0, 108, 111, 0, 0])} : Result<&2, &2, N.NlError, B.Octets>}

law vec_flags:
  {N.nla.put(H.NlBig{}, N.NlAttr{2n, True{}, True{}, B.Octets.empty()}) == Done{B.Octets.of_list([0, 4, 192, 2])} : Result<&2, &2, N.NlError, B.Octets>}

law vec_parse:
  {N.nla.parse(N.nla.opts_default(), B.Octets.of_list([6, 0, 1, 0, 7, 7, 0, 0, 4, 0, 2, 128])) == Done{[N.NlAttr{1n, False{}, False{}, B.Octets.of_list([7, 7])}, N.NlAttr{2n, True{}, False{}, B.Octets.empty()}]} : Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}

# (a type past 14 bits, NlBadType, is a large number: check.bend shows it)
law vec_errors:
  {(N.nla.parse(N.nla.opts_default(), B.Octets.of_list([3, 0, 1, 0])), N.nla.parse(N.nla.opts_default(), B.Octets.of_list([4, 0, 1, 0, 9]))) == (Fail{N.NlBadLength{}}, Fail{N.NlTrailing{}}) : Result<&2, &2, N.NlError, List<&2, N.NlAttr>> & Result<&2, &2, N.NlError, List<&2, N.NlAttr>>}
