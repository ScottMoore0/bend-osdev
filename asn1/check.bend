import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./rules.bend as R
import ./encode.bend as En
import ./conform.bend as C
import ./asn1.bend as A
import ./prim.bend as P
import ./bits.bend as Bi
import ./oidval.bend as O
import ./string.bend as S
import ./time.bend as Ti
import ./build.bend as Bu
import ./schema.bend as Sc

# Hex input

def hexd(+c: Char) -> U32:
  +x = Char.to_u32(c)
  Bool.pick(U32, U32.is_lt(x, 58), U32.sub(x, 48), Bool.pick(U32, U32.is_lt(x, 71), U32.sub(x, 55), U32.sub(x, 87)))

def unhex(s: String) -> List<&2, U32>:
  match s:
    case SCon{a, SCon{b, t}}:
      Con{U32.add(U32.mul(hexd(a), 16), hexd(b)), unhex(t)}
    case _:
      Nil{}

def hx(s: String) -> B.Octets:
  B.Octets.of_list(unhex(s))

# Showing

def cls(c: T.Asn1Class) -> String:
  match c:
    case T.Asn1Universal{}:
      "U"
    case T.Asn1Application{}:
      "A"
    case T.Asn1Context{}:
      "C"
    case T.Asn1Private{}:
      "P"

def show_list(ns: List<&2, N.Asn1Node>) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{N.Asn1Prim{T.Asn1Tag{c, n}, o}, Nil{}}:
      cls(c) ++ Nat.show(n) ++ ":" ++ B.Octets.hex(o)
    case Con{N.Asn1Prim{T.Asn1Tag{c, n}, o}, rest}:
      cls(c) ++ Nat.show(n) ++ ":" ++ B.Octets.hex(o) ++ " " ++ show_list(rest)
    case Con{N.Asn1Cons{T.Asn1Tag{c, n}, xs}, Nil{}}:
      cls(c) ++ Nat.show(n) ++ "{" ++ show_list(xs) ++ "}"
    case Con{N.Asn1Cons{T.Asn1Tag{c, n}, xs}, rest}:
      cls(c) ++ Nat.show(n) ++ "{" ++ show_list(xs) ++ "} " ++ show_list(rest)

def err(e: E.Asn1Error) -> String:
  E.Asn1Error.name(e)

def show_n(r: Result<&2, &2, E.Asn1Error, N.Asn1Node>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{n}:
      show_list([n])

def show_o(r: Result<&2, &2, E.Asn1Error, B.Octets>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{o}:
      B.Octets.hex(o)

def enc_n(n: N.Asn1Node) -> String:
  show_o(En.Asn1.encode(n))

# decode, show, and encode again
def t(+r: R.Asn1Rules, +s: String) -> String:
  +res = A.Asn1.decode(r, hx(s))
  s ++ " => " ++ show_n(res) ++ " | " ++ show_o(Result.bind(&2, &2, E.Asn1Error, N.Asn1Node, B.Octets, res, n => En.Asn1.encode(n)))

def der() -> R.Asn1Rules:
  R.Asn1Rules.der()

def ber() -> R.Asn1Rules:
  R.Asn1Rules.ber()

def nat_list(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, Nil{}}:
      Nat.show(x)
    case Con{x, t}:
      Nat.show(x) ++ "." ++ nat_list(t)

def show_arcs(r: Result<&2, &2, E.Asn1Error, List<&2, Nat>>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{xs}:
      nat_list(xs)

def show_int(r: Result<&2, &2, E.Asn1Error, P.Asn1Int>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{P.Asn1Int{neg, m}}:
      Bool.pick(String, neg, "-", "") ++ Nat.show(m)

def show_bool(r: Result<&2, &2, E.Asn1Error, Bool>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{b}:
      Bool.show(b)

def show_bits(r: Result<&2, &2, E.Asn1Error, Bi.Asn1Bits>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{Bi.Asn1Bits{u, o}}:
      Nat.show(u) ++ "/" ++ B.Octets.hex(o)

def show_str(r: Result<&2, &2, E.Asn1Error, S.Asn1Str>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{s}:
      "\"" ++ S.Asn1Str.text(s) ++ "\""

def show_time(r: Result<&2, &2, E.Asn1Error, Ti.Asn1Time>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{t}:
      Ti.Asn1Time.show(t)

def node_of(r: Result<&2, &2, E.Asn1Error, N.Asn1Node>) -> N.Asn1Node:
  Result.default(&2, &2, E.Asn1Error, N.Asn1Node, r, Bu.Asn1.seq(Nil{}))

def dec(s: String) -> N.Asn1Node:
  node_of(A.Asn1.decode(ber(), hx(s)))

def int_rt(i: P.Asn1Int) -> String:
  +n = P.Asn1.int(i)
  enc_n(n) ++ " " ++ show_int(P.Asn1.get_int(n))

# Schema: SEQUENCE { a INTEGER, b [0] EXPLICIT BOOLEAN OPTIONAL,
#   c [1] IMPLICIT OCTET STRING OPTIONAL, d SET OF OBJECT IDENTIFIER,
#   e CHOICE { IA5String, UTF8String } }
def sch() -> Sc.Asn1Schema:
  Sc.Asn1S.seq([Sc.Asn1S.elem(T.Asn1Tag.integer()), Sc.Asn1S.opt(Sc.Asn1S.explicit(0n, Sc.Asn1S.elem(T.Asn1Tag.boolean()))), Sc.Asn1S.opt(Sc.Asn1S.ctx(1n)), Sc.Asn1S.set_of(Sc.Asn1S.elem(T.Asn1Tag.oid())), Sc.Asn1SChoice{[Sc.Asn1S.elem(T.Asn1Tag.ia5_string()), Sc.Asn1S.elem(T.Asn1Tag.utf8_string())]}])

def sep(rest: List<&2, Sc.Asn1Match>) -> String:
  match rest:
    case Nil{}:
      ""
    case Con{m, t}:
      " "

# matches as text (fuel bounds the nesting)
def show_ms(f: Nat, ms: List<&2, Sc.Asn1Match>) -> String:
  match f ms:
    case 0n _:
      "..."
    case _ Nil{}:
      ""
    case 1n+ +g Con{Sc.Asn1MElem{x}, +rest}:
      "E(" ++ B.Octets.hex(A.Asn1Tlv.raw(x)) ++ ")" ++ sep(rest) ++ show_ms(g, rest)
    case 1n+ +g Con{Sc.Asn1MSeq{x, ms2}, +rest}:
      "S[" ++ show_ms(g, ms2) ++ "]" ++ sep(rest) ++ show_ms(g, rest)
    case 1n+ +g Con{Sc.Asn1MChoice{i, x}, +rest}:
      "C" ++ Nat.show(i) ++ ":" ++ show_ms(g, [x]) ++ sep(rest) ++ show_ms(g, rest)
    case 1n+ +g Con{Sc.Asn1MExplicit{x, y}, +rest}:
      "X:" ++ show_ms(g, [y]) ++ sep(rest) ++ show_ms(g, rest)
    case 1n+ +g Con{Sc.Asn1MAbsent{}, +rest}:
      "-" ++ sep(rest) ++ show_ms(g, rest)
    case 1n+ +g Con{Sc.Asn1MDefault{v}, +rest}:
      "D" ++ sep(rest) ++ show_ms(g, rest)

def show_m(m: Sc.Asn1Match) -> String:
  show_ms(100n, [m])

def show_match(r: Result<&2, &2, E.Asn1Error, Sc.Asn1Match>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{m}:
      show_m(m)

def big() -> N.Asn1Node:
  Bu.Asn1.seq([P.Asn1.octets(B.Octets.zeros(300n)), N.Asn1Prim{T.Asn1Tag{T.Asn1Private{}, 70000n}, hx("ab")}, Bu.Asn1.explicit(31n, P.Asn1.null())])

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("X.690 examples")
    IO.print(t(der(), "300a1605536d6974680101ff"))
    IO.print(show_arcs(O.Asn1.get_oid(dec("0603883703"))))
    IO.print(show_o(Result.bind(&2, &2, E.Asn1Error, N.Asn1Node, B.Octets, O.Asn1.oid([2n, 999n, 3n]), n => En.Asn1.encode(n))))
    IO.print(t(der(), "1a054a6f6e6573"))
    IO.print(t(der(), "43054a6f6e6573"))
    IO.print(t(der(), "a20743054a6f6e6573"))
    IO.print(t(der(), "670743054a6f6e6573"))
    IO.print(t(der(), "82054a6f6e6573"))
    IO.print(show_bits(Bi.Asn1.get_bits(der(), dec("0307040a3b5f291cd0"))))
    IO.print(show_bits(Bi.Asn1.get_bits(ber(), dec("23800303000a3b0305045f291cd00000"))))
    IO.print(show_bits(Bi.Asn1.get_bits(der(), dec("23800303000a3b0305045f291cd00000"))))
    IO.print(B.Octets.hex(B.Octets.take(4n, Result.default(&2, &2, E.Asn1Error, B.Octets, En.Asn1.encode(P.Asn1.octets(B.Octets.zeros(201n))), B.Octets.empty()))))
    IO.print(show_bool(P.Asn1.get_bool(der(), dec("0101ff"))))
    IO.print(show_n(A.Asn1.decode(der(), hx("0500"))))
    IO.print("Tags and lengths")
    IO.print(t(der(), "1f1f00"))
    IO.print(t(der(), "1f1e00"))
    IO.print(t(der(), "1f801f00"))
    IO.print(t(der(), "5f81480100"))
    IO.print(t(der(), "df8f2c00"))
    IO.print(t(der(), "0481800000"))
    IO.print(t(ber(), "048100"))
    IO.print(t(der(), "048100"))
    IO.print(t(der(), "04ff00"))
    IO.print(t(der(), "0482000100"))
    IO.print(enc_n(big()))
    IO.print(Bool.show(String.eq(show_n(A.Asn1.decode(der(), Result.default(&2, &2, E.Asn1Error, B.Octets, En.Asn1.encode(big()), B.Octets.empty()))), show_list([big()]))))
    IO.print("BER and DER")
    IO.print(t(ber(), "3080020101040100" ++ "0000"))
    IO.print(t(der(), "3080020101040100" ++ "0000"))
    IO.print(t(ber(), "0480"))
    IO.print(t(ber(), "308002010100"))
    IO.print(t(ber(), "2480040161040162000"))
    IO.print(t(ber(), "24800401610401620000"))
    IO.print(t(der(), "24060401610401620000"))
    IO.print(t(ber(), "21030101ff"))
    IO.print(t(ber(), "2003050100"))
    IO.print(t(ber(), "1003020101"))
    IO.print(t(der(), "3106020102020101"))
    IO.print(t(ber(), "3106020102020101"))
    IO.print(t(der(), "3106020101020102"))
    IO.print(t(der(), "0000"))
    IO.print(t(der(), "2000"))
    IO.print(t(der(), "020101ff"))
    IO.print(t(R.Asn1Rules.with_trailing(der(), True{}), "020101ff"))
    IO.print(t(der(), "0203"))
    IO.print(t(der(), "30030201"))
    IO.print(t(der(), "3004020101"))
    IO.print(show_o(En.Asn1.encode(N.Asn1Prim{T.Asn1Tag.universal(0n), B.Octets.empty()})))
    IO.print(Bool.show(C.Asn1.conforms(der(), Bu.Asn1.set([P.Asn1.int_nat(2n), P.Asn1.int_nat(1n)]))) ++ " " ++ Bool.show(C.Asn1.conforms(der(), Bu.Asn1.set_of([P.Asn1.int_nat(2n), P.Asn1.int_nat(1n)]))) ++ " " ++ enc_n(Bu.Asn1.set_of([P.Asn1.int_nat(2n), P.Asn1.int_nat(1n)])))
    IO.print("INTEGER")
    IO.print(int_rt(P.Asn1Int{False{}, 0n}))
    IO.print(int_rt(P.Asn1Int{False{}, 127n}))
    IO.print(int_rt(P.Asn1Int{False{}, 128n}))
    IO.print(int_rt(P.Asn1Int{False{}, 256n}))
    IO.print(int_rt(P.Asn1Int{True{}, 1n}))
    IO.print(int_rt(P.Asn1Int{True{}, 128n}))
    IO.print(int_rt(P.Asn1Int{True{}, 129n}))
    IO.print(int_rt(P.Asn1Int{True{}, 65536n}))
    IO.print(int_rt(P.Asn1Int{False{}, Nat.add(Nat.mul(65535n, 4294967295n), 9n)}))
    IO.print(show_int(P.Asn1.get_int(dec("020701000000000000"))) ++ " " ++ show_o(P.Asn1.get_int_bytes(dec("020701000000000000"))) ++ " " ++ show_o(P.Asn1.get_uint_bytes(dec("02080080000000000001"))) ++ " " ++ enc_n(P.Asn1.uint(hx("000080"))) ++ " " ++ enc_n(P.Asn1.uint(B.Octets.empty())) ++ " " ++ show_o(P.Asn1.get_uint_bytes(dec("0201ff"))))
    IO.print(show_int(P.Asn1.get_int(dec("02020001"))))
    IO.print(show_int(P.Asn1.get_int(dec("0202ff80"))))
    IO.print(show_int(P.Asn1.get_int(dec("0200"))))
    IO.print(show_o(Result.map(&2, &2, E.Asn1Error, Nat, B.Octets, n => B.Octets.of_string(Nat.show(n)), P.Asn1.get_nat(dec("0201ff")))))
    IO.print("BOOLEAN NULL OCTET STRING")
    IO.print(show_bool(P.Asn1.get_bool(der(), dec("010100"))) ++ " " ++ show_bool(P.Asn1.get_bool(der(), dec("010101"))) ++ " " ++ show_bool(P.Asn1.get_bool(ber(), dec("010101"))) ++ " " ++ show_bool(P.Asn1.get_bool(der(), dec("01020000"))))
    IO.print(Bool.show(P.Asn1.is_null(dec("0500"))) ++ " " ++ Bool.show(P.Asn1.is_null(dec("050100"))))
    IO.print(show_o(P.Asn1.get_octets(ber(), dec("24800401610401620000"))) ++ " " ++ show_o(P.Asn1.get_octets(der(), dec("2406040161040162"))))
    IO.print("BIT STRING")
    IO.print(show_bits(Bi.Asn1.get_bits(der(), dec("030206c0"))) ++ " " ++ show_bits(Bi.Asn1.get_bits(der(), dec("030206c1"))) ++ " " ++ show_bits(Bi.Asn1.get_bits(ber(), dec("030206c1"))) ++ " " ++ show_bits(Bi.Asn1.get_bits(der(), dec("030100"))) ++ " " ++ show_bits(Bi.Asn1.get_bits(der(), dec("030101"))) ++ " " ++ show_bits(Bi.Asn1.get_bits(der(), dec("030208ff"))))
    IO.print(Bool.show(Bi.Asn1Bits.bit(Bi.Asn1Bits{6n, hx("a0")}, 0n)) ++ Bool.show(Bi.Asn1Bits.bit(Bi.Asn1Bits{6n, hx("a0")}, 1n)) ++ Bool.show(Bi.Asn1Bits.bit(Bi.Asn1Bits{6n, hx("a0")}, 2n)) ++ " " ++ Nat.show(Bi.Asn1Bits.len(Bi.Asn1Bits{6n, hx("a0")})))
    IO.print("OBJECT IDENTIFIER")
    IO.print(show_arcs(O.Asn1.get_oid(dec("06092a864886f70d01010b"))))
    IO.print(show_arcs(O.Asn1.get_oid(dec("0603550403"))))
    IO.print(show_arcs(O.Asn1.get_oid(dec("060100"))))
    IO.print(show_arcs(O.Asn1.get_oid(dec("0600"))))
    IO.print(show_arcs(O.Asn1.get_oid(dec("06022a86"))))
    IO.print(show_arcs(O.Asn1.get_oid(dec("0603808001"))))
    IO.print(show_o(O.Asn1.oid_content([3n, 1n])) ++ " " ++ show_o(O.Asn1.oid_content([1n, 40n])) ++ " " ++ show_o(O.Asn1.oid_content([2n, 100n, 3n])) ++ " " ++ show_o(O.Asn1.oid_content([1n])))
    IO.print(show_arcs(O.Asn1.get_oid(dec("0606883781e8e82d"))) ++ " " ++ show_arcs(O.Asn1.get_oid(dec("060a698a8a8a8a8a8a8a8a01"))) ++ " " ++ show_n(O.Asn1.oid([2n, 25n, Nat.mul(1048576n, 4194304n)])))
    IO.print("Strings")
    IO.print(show_str(S.Asn1.get_string(der(), dec("0c0668c3a96c6c6f"))) ++ " " ++ show_str(S.Asn1.get_string(der(), dec("0c02c0af"))) ++ " " ++ show_str(S.Asn1.get_string(der(), dec("0c03eda080"))) ++ " " ++ show_str(S.Asn1.get_string(der(), dec("0c04f4908080"))))
    IO.print(show_str(S.Asn1.get_string(der(), dec("13024162"))) ++ " " ++ show_str(S.Asn1.get_string(der(), dec("1302412a"))) ++ " " ++ show_str(S.Asn1.get_string(der(), dec("16024140"))) ++ " " ++ show_str(S.Asn1.get_string(der(), dec("160141"))) ++ " " ++ show_str(S.Asn1.get_string(der(), dec("160180"))))
    IO.print(show_str(S.Asn1.get_string(der(), dec("1e0400410042"))) ++ " " ++ show_str(S.Asn1.get_string(der(), dec("1c0400000041"))) ++ " " ++ show_str(S.Asn1.get_string(der(), dec("12023132"))) ++ " " ++ show_str(S.Asn1.get_string(der(), dec("120331322e"))))
    IO.print(enc_n(S.Asn1.utf8(S.Asn1.points_text([104, 233, 8364, 128512]))) ++ " " ++ show_n(S.Asn1.text_string(S.Asn1Printable{}, "Ab 1")) ++ " " ++ show_n(S.Asn1.text_string(S.Asn1Printable{}, "a@b")))
    IO.print("Times")
    IO.print(show_time(Ti.Asn1.get_time(der(), Ti.Asn1.utc_pivot(), dec("170d3439313233313233353935395a"))) ++ " " ++ show_time(Ti.Asn1.get_time(der(), Ti.Asn1.utc_pivot(), dec("170d3530303130313030303030305a"))))
    IO.print(show_time(Ti.Asn1.get_time(der(), Ti.Asn1.utc_pivot(), dec("170b393230353231303030305a"))) ++ " " ++ show_time(Ti.Asn1.get_time(ber(), Ti.Asn1.utc_pivot(), dec("170b393230353231303030305a"))) ++ " " ++ show_time(Ti.Asn1.get_time(ber(), Ti.Asn1.utc_pivot(), dec("17113832303130323037303030302d30353030"))))
    IO.print(show_time(Ti.Asn1.get_time(der(), Ti.Asn1.utc_pivot(), dec("180f32303530303130313030303030305a"))) ++ " " ++ show_time(Ti.Asn1.get_time(der(), Ti.Asn1.utc_pivot(), dec("181131393932303732323133323130302e335a"))) ++ " " ++ show_time(Ti.Asn1.get_time(der(), Ti.Asn1.utc_pivot(), dec("181231393932303732323133323130302e33305a"))))
    IO.print(show_time(Ti.Asn1.get_time(ber(), Ti.Asn1.utc_pivot(), dec("181231393835313130363231303632372e343536"))) ++ " " ++ show_time(Ti.Asn1.get_time(ber(), Ti.Asn1.utc_pivot(), dec("181531393835313130363231303632372e332d30353030"))) ++ " " ++ show_time(Ti.Asn1.get_time(der(), Ti.Asn1.utc_pivot(), dec("180f32303233303232393030303030305a"))) ++ " " ++ show_time(Ti.Asn1.get_time(der(), Ti.Asn1.utc_pivot(), dec("180f32303234303232393030303030305a"))))
    IO.print(show_time(Ti.Asn1.get_time(ber(), Ti.Asn1.utc_pivot(), dec("181132303230303130313132303030302c355a"))) ++ " " ++ show_time(Ti.Asn1.get_time(der(), Ti.Asn1.utc_pivot(), dec("181132303230303130313132303030302c355a"))) ++ " " ++ show_time(Ti.Asn1.get_time(ber(), Ti.Asn1.utc_pivot(), dec("180a32303230303130313132"))) ++ " " ++ show_time(Ti.Asn1.get_time(ber(), Ti.Asn1.utc_pivot(), dec("180f3230323030313031313233302b3031"))) ++ " " ++ show_time(Ti.Asn1.get_time(der(), Ti.Asn1.utc_pivot(), dec("170d3230303233303030303030305a"))) ++ " " ++ show_time(Ti.Asn1.get_time(der(), Ti.Asn1.utc_pivot(), dec("170d3230313233313234363030305a"))))
    IO.print(enc_n(Ti.Asn1.utc_time(Ti.Asn1Time{2049n, 12n, 31n, 23n, 59n, 59n, Nil{}, Ti.Asn1Zulu{}})) ++ " " ++ enc_n(Ti.Asn1.gen_time(Ti.Asn1Time{1992n, 7n, 22n, 13n, 21n, 0n, [3n, 0n], Ti.Asn1Zulu{}})))
    IO.print("Schema")
    IO.print(show_match(Sc.Asn1.match(der(), sch(), hx("3017020105a0030101ff8102010231060601000601281601" ++ "61"))))
    IO.print(show_match(Sc.Asn1.match(der(), sch(), hx("300b0201053103060100" ++ "0c0161"))))
    IO.print(show_match(Sc.Asn1.match(der(), sch(), hx("300b0201053103060100" ++ "040161"))))
    IO.print(show_match(Sc.Asn1.match(der(), sch(), hx("300d02010531030601000c01610500"))))
    IO.print(show_match(Sc.Asn1.match(der(), sch(), hx("30080201053103060100"))))
    IO.print(show_match(Sc.Asn1.match(der(), sch(), hx("300e0201053106060128060100160161"))))
    IO.print(show_match(Sc.Asn1.match(der(), Sc.Asn1S.seq([Sc.Asn1SDefault{Sc.Asn1S.elem(T.Asn1Tag.integer()), P.Asn1.int_nat(1n)}]), hx("3003020101"))))
    IO.print(show_match(Sc.Asn1.match(ber(), Sc.Asn1S.seq([Sc.Asn1SDefault{Sc.Asn1S.elem(T.Asn1Tag.integer()), P.Asn1.int_nat(1n)}]), hx("3003020101"))))
    IO.print(show_match(Sc.Asn1.match(der(), Sc.Asn1S.seq([Sc.Asn1SDefault{Sc.Asn1S.elem(T.Asn1Tag.integer()), P.Asn1.int_nat(1n)}]), hx("3000"))))
    IO.print(show_match(Sc.Asn1.match(ber(), Sc.Asn1S.seq([Sc.Asn1S.any(), Sc.Asn1S.any()]), hx("30800201010500" ++ "0000"))))

#|X.690 examples
#|300a1605536d6974680101ff => U16{U22:536d697468 U1:ff} | 300a1605536d6974680101ff
#|2.999.3
#|0603883703
#|1a054a6f6e6573 => U26:4a6f6e6573 | 1a054a6f6e6573
#|43054a6f6e6573 => A3:4a6f6e6573 | 43054a6f6e6573
#|a20743054a6f6e6573 => C2{A3:4a6f6e6573} | a20743054a6f6e6573
#|670743054a6f6e6573 => A7{A3:4a6f6e6573} | 670743054a6f6e6573
#|82054a6f6e6573 => C2:4a6f6e6573 | 82054a6f6e6573
#|4/0a3b5f291cd0
#|4/0a3b5f291cd0
#|Asn1BadForm
#|0481c900
#|True
#|U5:
#|Tags and lengths
#|1f1f00 => U31: | 1f1f00
#|1f1e00 => Asn1BadTag | Asn1BadTag
#|1f801f00 => Asn1BadTag | Asn1BadTag
#|5f81480100 => A200:00 | 5f81480100
#|df8f2c00 => P1964: | df8f2c00
#|0481800000 => Asn1Truncated | Asn1Truncated
#|048100 => U4: | 0400
#|048100 => Asn1NonMinimalLength | Asn1NonMinimalLength
#|04ff00 => Asn1BadLength | Asn1BadLength
#|0482000100 => Asn1NonMinimalLength | Asn1NonMinimalLength
#|3082013b0482012c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000df84a27001abbf1f020500
#|True
#|BER and DER
#|30800201010401000000 => U16{U2:01 U4:00} | 3006020101040100
#|30800201010401000000 => Asn1Indefinite | Asn1Indefinite
#|0480 => Asn1PrimIndefinite | Asn1PrimIndefinite
#|308002010100 => Asn1Truncated | Asn1Truncated
#|2480040161040162000 => Asn1Truncated | Asn1Truncated
#|24800401610401620000 => U4{U4:61 U4:62} | 2406040161040162
#|24060401610401620000 => Asn1BadForm | Asn1BadForm
#|21030101ff => Asn1BadForm | Asn1BadForm
#|2003050100 => Asn1ReservedTag | Asn1ReservedTag
#|1003020101 => Asn1BadForm | Asn1BadForm
#|3106020102020101 => Asn1SetOrder | Asn1SetOrder
#|3106020102020101 => U17{U2:02 U2:01} | 3106020102020101
#|3106020101020102 => U17{U2:01 U2:02} | 3106020101020102
#|0000 => Asn1BadEoc | Asn1BadEoc
#|2000 => Asn1ReservedTag | Asn1ReservedTag
#|020101ff => Asn1Trailing | Asn1Trailing
#|020101ff => U2:01 | 020101
#|0203 => Asn1Truncated | Asn1Truncated
#|30030201 => Asn1Truncated | Asn1Truncated
#|3004020101 => Asn1Truncated | Asn1Truncated
#|Asn1ReservedTag
#|False True 3106020101020102
#|INTEGER
#|020100 0
#|02017f 127
#|02020080 128
#|02020100 256
#|0201ff -1
#|020180 -128
#|0202ff7f -129
#|0203ff0000 -65536
#|020700fffeffff000a Asn1TooLong
#|Asn1TooLong 01000000000000 80000000000001 02020080 020100 Asn1Negative
#|Asn1BadInteger
#|Asn1BadInteger
#|Asn1BadInteger
#|Asn1Negative
#|BOOLEAN NULL OCTET STRING
#|False Asn1BadValue True Asn1BadValue
#|True False
#|6162 Asn1BadForm
#|BIT STRING
#|6/c0 Asn1BadBits 6/c1 0/ Asn1BadBits Asn1BadBits
#|TrueFalseFalse 2
#|OBJECT IDENTIFIER
#|1.2.840.113549.1.1.11
#|2.5.4.3
#|0.0
#|Asn1BadOid
#|Asn1BadOid
#|Asn1BadOid
#|Asn1BadOid Asn1BadOid 813403 Asn1BadOid
#|2.999.3814445 Asn1BadOid Asn1BadOid
#|Strings
#|"héllo" Asn1BadString Asn1BadString Asn1BadString
#|"Ab" Asn1BadString "A@" "A" Asn1BadString
#|"AB" "A" "12" Asn1BadString
#|0c0a68c3a9e282acf09f9880 U19:41622031 Asn1BadString
#|Times
#|2049-12-31T23:59:59Z 1950-01-01T00:00:00Z
#|Asn1BadTime 1992-05-21T00:00:00Z 1982-01-02T07:00:00-05:00
#|2050-01-01T00:00:00Z 1992-07-22T13:21:00.3Z Asn1BadTime
#|1985-11-06T21:06:27.456 1985-11-06T21:06:27.3-05:00 Asn1BadTime 2024-02-29T00:00:00Z
#|2020-01-01T12:00:00.5Z Asn1BadTime 2020-01-01T12:00:00 2020-01-01T12:30:00+01:00 Asn1BadTime Asn1BadTime
#|170d3439313233313233353935395a 181131393932303732323133323130302e335a
#|Schema
#|S[E(020105) X:E(0101ff) E(81020102) S[E(060100) E(060128)] C0:E(160161)]
#|S[E(020105) - - S[E(060100)] C1:E(0c0161)]
#|Asn1SchemaMismatch
#|Asn1SchemaExtra
#|Asn1SchemaMissing
#|Asn1SetOrder
#|Asn1SchemaDefault
#|S[E(020101)]
#|S[D]
#|S[E(020101) E(0500)]
