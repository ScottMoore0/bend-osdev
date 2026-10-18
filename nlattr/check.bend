import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./header.bend as H
import ./nlattr.bend as N
import ./policy.bend as P

def err(e: N.NlError) -> String:
  match e:
    case N.NlBadType{t}:
      "NlBadType " ++ Nat.show(t)
    case N.NlTooLong{t}:
      "NlTooLong " ++ Nat.show(t)
    case N.NlBadLength{}:
      "NlBadLength"
    case N.NlTrailing{}:
      "NlTrailing"
    case N.NlUnknown{t}:
      "NlUnknown " ++ Nat.show(t)
    case N.NlTooShort{t}:
      "NlTooShort " ++ Nat.show(t)
    case N.NlTooLarge{t}:
      "NlTooLarge " ++ Nat.show(t)
    case N.NlNoNul{t}:
      "NlNoNul " ++ Nat.show(t)
    case N.NlNotFlag{t}:
      "NlNotFlag " ++ Nat.show(t)
    case N.NlNoNestedFlag{t}:
      "NlNoNestedFlag " ++ Nat.show(t)
    case N.NlTooDeep{}:
      "NlTooDeep"

def show_o(r: Result<&2, &2, N.NlError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.hex(o)
    case Fail{e}:
      err(e)

def show_a(a: N.NlAttr) -> String:
  match a:
    case N.NlAttr{t, nd, nb, p}:
      Nat.show(t) ++ Bool.pick(String, nd, "N", "") ++ Bool.pick(String, nb, "B", "") ++ ":" ++ B.Octets.hex(p)

def show_as(as: List<&2, N.NlAttr>) -> String:
  match as:
    case Nil{}:
      "-"
    case Con{a, Nil{}}:
      show_a(a)
    case Con{a, t}:
      show_a(a) ++ " " ++ show_as(t)

def show_p(r: Result<&2, &2, N.NlError, List<&2, N.NlAttr>>) -> String:
  match r:
    case Done{as}:
      show_as(as)
    case Fail{e}:
      err(e)

def show_m(m: Maybe<&2, U32>) -> String:
  match m:
    case None{}:
      "none"
    case Some{v}:
      U32.show(v)

def built(r: Result<&2, &2, N.NlError, B.Octets>) -> B.Octets:
  match r:
    case Done{o}:
      o
    case Fail{e}:
      B.Octets.empty()

def le() -> H.NlOrder:
  H.NlLittle{}

# IFLA_IFNAME-like string, a u32, a flag, a nested pair, a network-order u32
def attrs() -> List<&2, N.NlAttr>:
  [N.nla.string(3n, "eth0"), N.nla.u32(le(), 4n, 1500), N.nla.flag(7n), N.nla.nest(18n, built(N.nla.build(le(), [N.nla.u8(1n, 5), N.nla.u16(le(), 2n, 513)]))), N.nla.u32_be(9n, 16909060)]

def buf() -> B.Octets:
  built(N.nla.build(le(), attrs()))

# policy 0: the top level; policy 1: the nested attribute's
def set() -> List<&2, P.NlPolicy>:
  [P.NlPolicy{[P.NlReject{}, P.NlReject{}, P.NlReject{}, P.NlNulString{15n}, P.NlU32{}, P.NlReject{}, P.NlReject{}, P.NlFlag{}, P.NlReject{}, P.NlU32{}, P.NlReject{}, P.NlReject{}, P.NlReject{}, P.NlReject{}, P.NlReject{}, P.NlReject{}, P.NlReject{}, P.NlReject{}, P.NlNested{1n}]}, P.NlPolicy{[P.NlReject{}, P.NlU8{}, P.NlU16{}]}]

def ok_set() -> List<&2, P.NlPolicy>:
  set()

def first_u32(r: Result<&2, &2, N.NlError, List<&2, N.NlAttr>>, +t: Nat) -> String:
  match r:
    case Done{as}:
      show_m(Maybe.bind(&2, N.NlAttr, U32, N.nla.find(as, t), a => N.nla.get_u32(H.NlLittle{}, a)))
    case Fail{e}:
      err(e)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(B.Octets.hex(buf()))
    IO.print(show_p(N.nla.parse(N.nla.opts_default(), buf())))
    IO.print(first_u32(N.nla.parse(N.nla.opts_default(), buf()), 4n))
    IO.print(first_u32(N.nla.parse(N.nla.opts_default(), buf()), 9n))
    IO.print(show_p(P.nla.parse_policy(P.nla.check_default(), set(), 0n, buf())))
    IO.print(show_p(P.nla.parse_policy(P.nla.check_default(), [P.NlPolicy{[P.NlReject{}, P.NlReject{}, P.NlReject{}, P.NlNulString{2n}]}], 0n, buf())))
    IO.print(show_p(P.nla.parse_policy(P.nla.check_liberal(le()), [P.NlPolicy{[P.NlReject{}, P.NlReject{}, P.NlReject{}, P.NlString{0n}, P.NlU16{}]}], 0n, buf())))
    IO.print(show_p(P.nla.parse_policy(P.nla.check_default(), [P.NlPolicy{[P.NlReject{}, P.NlReject{}, P.NlReject{}, P.NlString{0n}, P.NlU16{}]}], 0n, buf())))
    IO.print(show_p(N.nla.parse(N.nla.opts_default(), B.Octets.of_list([8, 0, 1, 0, 1, 2, 3, 4, 9]))))
    IO.print(show_p(N.nla.parse(N.nla.opts_liberal(le()), B.Octets.of_list([8, 0, 1, 0, 1, 2, 3, 4, 9]))))
    IO.print(show_p(N.nla.parse(N.nla.opts_default(), B.Octets.of_list([12, 0, 1, 0, 1, 2, 3, 4]))))
    IO.print(show_p(N.nla.parse(N.nla.opts_default(), B.Octets.of_list([3, 0, 1, 0]))))
    IO.print(show_p(N.nla.parse(N.nla.opts_default(), B.Octets.of_list([6, 0, 1, 0, 7, 7]))))
    IO.print(show_o(N.nla.build(le(), [N.nla.flag(16384n)])))
    IO.print(show_o(N.nla.build(H.NlBig{}, [N.nla.u8(258n, 255)])))

#|09000300657468300000000008000400dc0500000400070014001280050001000500000006000200010200000800094001020304
#|3:6574683000 4:dc050000 7: 18N:05000100050000000600020001020000 9B:01020304
#|1500
#|16909060
#|3:6574683000 4:dc050000 7: 18N:05000100050000000600020001020000 9B:01020304
#|NlTooLarge 3
#|3:6574683000 4:dc050000 7: 18N:05000100050000000600020001020000 9B:01020304
#|NlTooLarge 4
#|NlTrailing
#|1:01020304
#|NlBadLength
#|NlBadLength
#|1:0707
#|NlBadType 16384
#|00050102ff000000
