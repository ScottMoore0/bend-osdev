import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./kstr.bend as K
import ./format.bend as F
import ./hexdump.bend as H
import ./options.bend as O

def err(e: K.KStrError) -> String:
  match e:
    case K.KStrEmpty{}:
      "empty"
    case K.KStrBadChar{p}:
      "bad char " ++ Nat.show(p)
    case K.KStrRange{}:
      "range"
    case K.KStrBadFormat{p}:
      "bad format " ++ Nat.show(p)
    case K.KStrMissingArg{}:
      "missing arg"

def r32(r: Result<&2, &2, K.KStrError, U32>) -> String:
  match r:
    case Done{v}:
      U32.show(v)
    case Fail{e}:
      err(e)

def margs(xs: List<&2, B.Octets>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      " [" ++ B.Octets.to_string(h) ++ "]" ++ margs(t)

def mres(m: Maybe<&2, O.KStrMatch>) -> String:
  match m:
    case None{}:
      "none"
    case Some{k}:
      match k:
        case O.KStrMatch{t, args}:
          U32.show(t) ++ margs(args)

def table() -> List<&2, O.KStrPattern>:
  [O.KStrPattern{1, B.Octets.of_string("size=%u")}, O.KStrPattern{2, B.Octets.of_string("mode=%o")}, O.KStrPattern{3, B.Octets.of_string("uid=%d")}, O.KStrPattern{4, B.Octets.of_string("name=%s")}, O.KStrPattern{5, B.Octets.of_string("ro")}]

def sres(r: Result<&2, &2, K.KStrError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.to_string(o)
    case Fail{e}:
      err(e)

def lines(xs: List<&2, B.Octets>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      B.Octets.to_string(h) ++ "|" ++ lines(t)

def s(x: String) -> B.Octets:
  B.Octets.of_string(x)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(r32(K.KStr.to_u32(s("0x1f"), 0)))
    IO.print(r32(K.KStr.to_u32(s("017"), 0)))
    IO.print(r32(K.KStr.to_u32(s("17\n"), 10)))
    IO.print(r32(K.KStr.to_u32(s("4294967295"), 10)))
    IO.print(r32(K.KStr.to_u32(s("4294967296"), 10)))
    IO.print(r32(K.KStr.to_u32(s("12a"), 10)))
    IO.print(r32(K.KStr.to_u32(s(""), 10)))
    IO.print(r32(K.KStr.to_u32(s("+5"), 10)))
    IO.print(r32(K.KStr.to_u32(s("-5"), 10)))
    IO.print(r32(K.KStr.to_s32(s("-2147483648"), 10)))
    IO.print(r32(K.KStr.to_s32(s("2147483648"), 10)))
    IO.print(r32(K.KStr.to_u32(s("ffffffff"), 16)))
    IO.print(r32(K.KStr.to_u32(s("100000000"), 16)))
    IO.print(B.Octets.to_string(F.KStr.hex32(3735928559)))
    IO.print(B.Octets.to_string(F.KStr.format(F.KFmt{F.KConvD{}, 5n, False{}, False{}, False{}, False{}}, W.W64.sub(W.W64.zero(), W.W64.from_u32(42)))))
    IO.print(B.Octets.to_string(F.KStr.format(F.KFmt{F.KConvD{}, 5n, True{}, False{}, False{}, False{}}, W.W64.sub(W.W64.zero(), W.W64.from_u32(42)))))
    IO.print(sres(F.KStr.sprintf(s("[%5d|%-5u|%05x|%+d|% d|%o|%X|%%|%08x]"), [W.W64.sub(W.W64.zero(), W.W64.from_u32(42)), W.W64.from_u32(7), W.W64.from_u32(255), W.W64.from_u32(3), W.W64.from_u32(4), W.W64.from_u32(8), W.W64.from_u32(48879), W.W64.from_u32(3735928559)])))
    IO.print(sres(F.KStr.sprintf(s("%d %d"), [W.W64.one()])))
    IO.print(sres(F.KStr.sprintf(s("%5"), [W.W64.one()])))
    IO.print(B.Octets.to_string(H.KStr.hex_dump_line(H.KDump.default(), s("@ABCDEFGHIJKLMNO"))))
    IO.print(B.Octets.to_string(H.KStr.hex_dump_line(H.KDump{16n, 4n, True{}, True{}}, s("@ABCDEFGHIJKLMNO"))))
    IO.print(B.Octets.to_string(H.KStr.hex_dump_line(H.KDump.default(), B.Octets.of_list([97, 98, 99, 10]))))
    IO.print(lines(H.KStr.hex_dump(H.KDump.default(), H.KDumpOffset{}, s("0123456789abcdefXYZ"))))
    IO.print(mres(O.KStr.match_token(s("size=4096"), table())))
    IO.print(mres(O.KStr.match_token(s("mode=0755"), table())))
    IO.print(mres(O.KStr.match_token(s("uid=-3"), table())))
    IO.print(mres(O.KStr.match_token(s("name=foo,bar"), table())))
    IO.print(mres(O.KStr.match_token(s("ro"), table())))
    IO.print(mres(O.KStr.match_token(s("size=x"), table())))
    IO.print(lines(O.KStr.split_options(s(",size=1,,ro,"))))

#|31
#|15
#|17
#|4294967295
#|range
#|bad char 2
#|empty
#|5
#|bad char 0
#|2147483648
#|range
#|4294967295
#|range
#|deadbeef
#|  -42
#|-0042
#|[  -42|7    |000ff|+3| 4|10|BEEF|%|deadbeef]
#|missing arg
#|bad format 0
#|40 41 42 43 44 45 46 47 48 49 4a 4b 4c 4d 4e 4f  @ABCDEFGHIJKLMNO
#|43424140 47464544 4b4a4948 4f4e4d4c  @ABCDEFGHIJKLMNO
#|61 62 63 0a                                      abc.
#|00000000: 30 31 32 33 34 35 36 37 38 39 61 62 63 64 65 66  0123456789abcdef|00000010: 58 59 5a                                         XYZ|
#|1 [4096]
#|2 [0755]
#|3 [-3]
#|4 [foo,bar]
#|5
#|none
#|size=1|ro|
