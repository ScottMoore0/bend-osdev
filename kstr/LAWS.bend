# Properties, for every input:
#  * parse after format gives the value back: for every U32 v, its eight hex
#    digits (KStr.hex32, the %08x form) parse in base 16 to v.
#
# Vectors: kstrtox's rules (the prefix in base 0, a trailing newline, '+',
# a refused '-' and a refused overflow, the bounds of the signed form), the
# vsprintf subset (width, zero-padding, left-justifying, the sign flags, the
# conversions, %%, a missing argument), the hex_dump_to_buffer example from
# the kernel's documentation and its groups of 4, print_hex_dump's offsets,
# and match_token on a table of options.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./kstr.bend as K
import ./format.bend as F
import ./hexdump.bend as H
import ./options.bend as O

law hex32_round_trip:
  for +v: U32
  {K.KStr.to_u32(F.KStr.hex32(v), 16) == Done{v} : Result<&2, &2, K.KStrError, U32>}

# kstrtox

law v_base0:
  {[K.KStr.to_u32(B.Octets.of_string("0x1f"), 0), K.KStr.to_u32(B.Octets.of_string("017"), 0), K.KStr.to_u32(B.Octets.of_string("0"), 0), K.KStr.to_u32(B.Octets.of_string("19"), 0)] == [Done{31}, Done{15}, Done{0}, Done{19}] : List<&2, Result<&2, &2, K.KStrError, U32>>}

law v_newline:
  {[K.KStr.to_u32(B.Octets.of_string("17\n"), 10), K.KStr.to_u32(B.Octets.of_string("17\n\n"), 10)] == [Done{17}, Fail{K.KStrBadChar{2n}}] : List<&2, Result<&2, &2, K.KStrError, U32>>}

law v_sign:
  {[K.KStr.to_u32(B.Octets.of_string("+5"), 10), K.KStr.to_u32(B.Octets.of_string("-5"), 10), K.KStr.to_s32(B.Octets.of_string("-5"), 10)] == [Done{5}, Fail{K.KStrBadChar{0n}}, Done{4294967291}] : List<&2, Result<&2, &2, K.KStrError, U32>>}

law v_errors:
  {[K.KStr.to_u32(B.Octets.of_string(""), 10), K.KStr.to_u32(B.Octets.of_string("12a"), 10), K.KStr.to_u32(B.Octets.of_string("0x"), 16), K.KStr.to_u32(B.Octets.of_string("8"), 8)] == [Fail{K.KStrEmpty{}}, Fail{K.KStrBadChar{2n}}, Fail{K.KStrEmpty{}}, Fail{K.KStrBadChar{0n}}] : List<&2, Result<&2, &2, K.KStrError, U32>>}

law v_range:
  {[K.KStr.to_u32(B.Octets.of_string("ffffffff"), 16), K.KStr.to_u32(B.Octets.of_string("100000000"), 16), K.KStr.to_u32(B.Octets.of_string("37777777777"), 8), K.KStr.to_u32(B.Octets.of_string("40000000000"), 8)] == [Done{4294967295}, Fail{K.KStrRange{}}, Done{4294967295}, Fail{K.KStrRange{}}] : List<&2, Result<&2, &2, K.KStrError, U32>>}

law v_signed_bounds:
  {[K.KStr.to_s32(B.Octets.of_string("-2147483648"), 10), K.KStr.to_s32(B.Octets.of_string("2147483647"), 10), K.KStr.to_s32(B.Octets.of_string("2147483648"), 10)] == [Done{2147483648}, Done{2147483647}, Fail{K.KStrRange{}}] : List<&2, Result<&2, &2, K.KStrError, U32>>}

law v_u64:
  {K.KStr.to_u64(B.Octets.of_string("0xffffffffffffffff"), 0) == Done{W.W64.max()} : Result<&2, &2, K.KStrError, W.W64>}

law v_bool:
  {[K.KStr.to_bool(B.Octets.of_string("y")), K.KStr.to_bool(B.Octets.of_string("0")), K.KStr.to_bool(B.Octets.of_string("on")), K.KStr.to_bool(B.Octets.of_string("off"))] == [Done{True{}}, Done{False{}}, Done{True{}}, Done{False{}}] : List<&2, Result<&2, &2, K.KStrError, Bool>>}

# vsprintf: "[%5d|%-5u|%05x|%+d|% d|%o|%X|%%]" of -42, 7, 255, 3, 4, 8, 0xbeef

law v_sprintf:
  {F.KStr.sprintf(B.Octets.of_string("[%5d|%-5u|%05x|%+d|% d|%o|%X|%%]"), [W.W64.sub(W.W64.zero(), W.W64.from_u32(42)), W.W64.from_u32(7), W.W64.from_u32(255), W.W64.from_u32(3), W.W64.from_u32(4), W.W64.from_u32(8), W.W64.from_u32(48879)]) == Done{B.Octets.of_string("[  -42|7    |000ff|+3| 4|10|BEEF|%]")} : Result<&2, &2, K.KStrError, B.Octets>}

law v_sprintf_zero_sign:
  {F.KStr.format(F.KFmt{F.KConvD{}, 5n, True{}, False{}, False{}, False{}}, W.W64.sub(W.W64.zero(), W.W64.from_u32(42))) == B.Octets.of_string("-0042") : B.Octets}

law v_sprintf_errors:
  {[F.KStr.sprintf(B.Octets.of_string("%d %d"), [W.W64.one()]), F.KStr.sprintf(B.Octets.of_string("%5"), [W.W64.one()]), F.KStr.sprintf(B.Octets.of_string("%q"), [W.W64.one()])] == [Fail{K.KStrMissingArg{}}, Fail{K.KStrBadFormat{0n}}, Fail{K.KStrBadFormat{1n}}] : List<&2, Result<&2, &2, K.KStrError, B.Octets>>}

law v_hex32:
  {F.KStr.hex32(3735928559) == B.Octets.of_string("deadbeef") : B.Octets}

# hex dumps: the kernel documentation's example, groups of 4 (little-endian),
# a short line, and print_hex_dump's offsets

law v_hexdump_doc:
  {H.KStr.hex_dump_line(H.KDump.default(), B.Octets.of_string("@ABCDEFGHIJKLMNO")) == B.Octets.of_string("40 41 42 43 44 45 46 47 48 49 4a 4b 4c 4d 4e 4f  @ABCDEFGHIJKLMNO") : B.Octets}

law v_hexdump_groups:
  {H.KStr.hex_dump_line(H.KDump{16n, 4n, True{}, True{}}, B.Octets.of_string("@ABCDEFGHIJKLMNO")) == B.Octets.of_string("43424140 47464544 4b4a4948 4f4e4d4c  @ABCDEFGHIJKLMNO") : B.Octets}

law v_hexdump_short:
  {H.KStr.hex_dump_line(H.KDump.default(), B.Octets.of_list([97, 98, 99, 10])) == B.Octets.of_string("61 62 63 0a                                      abc.") : B.Octets}

law v_hexdump_offsets:
  {H.KStr.hex_dump(H.KDump{16n, 1n, False{}, True{}}, H.KDumpOffset{}, B.Octets.of_string("0123456789abcdefXY")) == [B.Octets.of_string("00000000: 30 31 32 33 34 35 36 37 38 39 61 62 63 64 65 66"), B.Octets.of_string("00000010: 58 59")] : List<&2, B.Octets>}

# match_token

law v_match_token:
  {[O.KStr.match_token(B.Octets.of_string("size=4096"), [O.KStrPattern{1, B.Octets.of_string("size=%u")}, O.KStrPattern{2, B.Octets.of_string("ro")}]), O.KStr.match_token(B.Octets.of_string("ro"), [O.KStrPattern{1, B.Octets.of_string("size=%u")}, O.KStrPattern{2, B.Octets.of_string("ro")}]), O.KStr.match_token(B.Octets.of_string("size=x"), [O.KStrPattern{1, B.Octets.of_string("size=%u")}, O.KStrPattern{2, B.Octets.of_string("ro")}])] == [Some{O.KStrMatch{1, [B.Octets.of_string("4096")]}}, Some{O.KStrMatch{2, []}}, None{}] : List<&2, Maybe<&2, O.KStrMatch>>}

law v_match_signed:
  {O.KStr.match_one(O.KStrPattern{3, B.Octets.of_string("uid=%d,gid=%x")}, B.Octets.of_string("uid=-3,gid=ff")) == Some{O.KStrMatch{3, [B.Octets.of_string("-3"), B.Octets.of_string("ff")]}} : Maybe<&2, O.KStrMatch>}

law v_split_options:
  {O.KStr.split_options(B.Octets.of_string(",size=1,,ro,")) == [B.Octets.of_string("size=1"), B.Octets.of_string("ro")] : List<&2, B.Octets>}
