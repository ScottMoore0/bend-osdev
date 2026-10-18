# Properties, for every input: the header, the reservation block, the
# structure block's tokens and the typed property values each read back as
# written; the lexer can be fed in pieces; and parsing a blob that Fdt.build
# wrote gives back the tree, the reservations and the boot CPU, for every
# tree it can hold. A blob whose first four bytes are not the magic is
# refused, whatever follows.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./header.bend as H
import ./rsvmap.bend as R
import ./structure.bend as S
import ./tree.bend as T
import ./props.bend as P
import ./path.bend as Pa
import ./fdt.bend as F
import ./example.bend as X

# The header

law header_round_trip:
  for +h: H.FdtHeader
  {H.FdtHeader.decode(H.FdtHeader.encode(h)) == Done{h} : Result<&2, &2, E.FdtError, H.FdtHeader>}

law bad_magic:
  for +opts: F.FdtOptions
  for +m: U32
  for +ne: {U32.is_eq(m, H.FdtHeader.magic_value()) == False{} : Bool}
  for +rest: B.Octets
  {F.Fdt.parse(opts, B.Octets.append(B.Octets.be32(m), rest)) == Fail{E.FdtBadMagic{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# Property values

law u32_round_trip:
  for +v: U32
  {P.FdtProp.u32(P.FdtProp.of_u32(v)) == Done{v} : Result<&2, &2, E.FdtError, U32>}

law u64_round_trip:
  for +v: W.W64
  {P.FdtProp.u64(P.FdtProp.of_u64(v)) == Done{v} : Result<&2, &2, E.FdtError, W.W64>}

law string_round_trip:
  for +s: B.Octets
  for +ok: {P.FdtProp.string_ok(s) == True{} : Bool}
  {P.FdtProp.string(P.FdtProp.of_string(s)) == Done{s} : Result<&2, &2, E.FdtError, B.Octets>}

# The reservation block

law rsv_round_trip:
  for +rs: List<&2, R.FdtRsv>
  for +ok: {R.FdtRsv.valid_all(rs) == True{} : Bool}
  {R.FdtRsv.decode(R.FdtRsv.encode(rs)) == Done{rs} : Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>}

# The structure block

law lexer_streaming:
  for +st: S.FdtLexer
  for +a: B.Octets
  for +b: B.Octets
  {S.FdtLexer.feed(S.FdtLexer.feed(st, a), b) == S.FdtLexer.feed(st, B.Octets.append(a, b)) : S.FdtLexer}

law tokens_round_trip:
  for +ts: List<&2, S.FdtToken>
  for +ok: {S.FdtToken.valid_all(ts) == True{} : Bool}
  {S.FdtToken.decode_all(S.FdtToken.encode_all(ts)) == Done{ts} : Result<&2, &2, E.FdtError, List<&2, S.FdtToken>>}

# The tree: its tokens and strings block build it back, whatever the rules

law tree_round_trip:
  for +rules: T.FdtTreeRules
  for +root: T.FdtNode
  for +ok: {T.FdtNode.flat_ok(root) == True{} : Bool}
  {T.FdtNode.of_flat(rules, T.FdtNode.to_tokens(root)) == Done{root} : Result<&2, &2, E.FdtError, T.FdtNode>}

# The blob: parsing what Fdt.build wrote gives back the version, the boot
# CPU, the reservations and the tree, for every tree and reservation list it
# can hold (Fdt.buildable), whatever the options

law parse_build:
  for +opts: F.FdtOptions
  for +root: T.FdtNode
  for +rsv: List<&2, R.FdtRsv>
  for +boot: U32
  for +ok: {F.Fdt.buildable(root, rsv) == True{} : Bool}
  {F.Fdt.parse(opts, F.Fdt.build(root, rsv, boot)) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# More property values

law strings_round_trip:
  for +ss: List<&2, B.Octets>
  for +ok: {P.FdtProp.strings_ok(ss) == True{} : Bool}
  {P.FdtProp.strings(P.FdtProp.of_strings(ss)) == Done{ss} : Result<&2, &2, E.FdtError, List<&2, B.Octets>>}

law cells_round_trip:
  for +cs: List<&2, U32>
  {P.FdtProp.cells(P.FdtProp.of_cells(cs)) == Done{cs} : Result<&2, &2, E.FdtError, List<&2, U32>>}

# Lookups, for every tree

# a node's first property is found by its name
law prop_head:
  for +nm: B.Octets
  for +k: B.Octets
  for +v: B.Octets
  for +ps: List<&2, T.FdtProp>
  for +cs: List<&2, T.FdtNode>
  {Pa.FdtNode.prop(T.FdtNode{nm, Con{T.FdtProp{k, v}, ps}, cs}, k) == Some{v} : Maybe<&2, B.Octets>}

# a node's first child is found by its name
law child_head:
  for +nm: B.Octets
  for +ps: List<&2, T.FdtProp>
  for +k: B.Octets
  for +kps: List<&2, T.FdtProp>
  for +kcs: List<&2, T.FdtNode>
  for +cs: List<&2, T.FdtNode>
  {Pa.FdtNode.child(T.FdtNode{nm, ps, Con{T.FdtNode{k, kps, kcs}, cs}}, k) == Some{T.FdtNode{k, kps, kcs}} : Maybe<&2, T.FdtNode>}

law find_root:
  for +root: T.FdtNode
  {Pa.FdtNode.find(root, "/") == Some{root} : Maybe<&2, T.FdtNode>}

# The hypotheses above are satisfiable, so no law is vacuous

law bad_magic_example:
  {U32.is_eq(0, H.FdtHeader.magic_value()) == False{} : Bool}

law string_ok_example:
  {P.FdtProp.string_ok(B.Octets.of_string("fsl,mpc8572ds")) == True{} : Bool}

law strings_ok_example:
  {P.FdtProp.strings_ok([B.Octets.of_string("ns16550"), B.Octets.empty()]) == True{} : Bool}

law rsv_valid_example:
  {R.FdtRsv.valid_all(X.FdtExample.rsv()) == True{} : Bool}

law tokens_valid_example:
  {S.FdtToken.valid_all([S.FdtTokBegin{B.Octets.empty()}, S.FdtTokProp{0, P.FdtProp.of_u32(1)}, S.FdtTokNop{}, S.FdtTokEnd{}]) == True{} : Bool}

law flat_ok_example:
  {T.FdtNode.flat_ok(X.FdtExample.tree()) == True{} : Bool}

law buildable_example:
  {F.Fdt.buildable(X.FdtExample.tree(), X.FdtExample.rsv()) == True{} : Bool}

# Vectors: property values (0x20000000 = 536870912)

law u32_vector:
  {P.FdtProp.u32(B.Octets.of_list([32, 0, 0, 0])) == Done{536870912} : Result<&2, &2, E.FdtError, U32>}

law u32_short:
  {P.FdtProp.u32(B.Octets.of_list([1, 2, 3])) == Fail{E.FdtBadLength{}} : Result<&2, &2, E.FdtError, U32>}

law u64_vector:
  {P.FdtProp.u64(B.Octets.of_list([0, 0, 0, 1, 0, 0, 0, 2])) == Done{W.W64.from_parts(1, 2)} : Result<&2, &2, E.FdtError, W.W64>}

law text_vector:
  {P.FdtProp.text(P.FdtProp.of_text("root=/dev/sda2")) == Done{"root=/dev/sda2"} : Result<&2, &2, E.FdtError, String>}

law string_no_nul:
  {P.FdtProp.string(B.Octets.of_string("ab")) == Fail{E.FdtBadString{}} : Result<&2, &2, E.FdtError, B.Octets>}

law string_inner_nul:
  {P.FdtProp.string(B.Octets.of_list([97, 0, 98, 0])) == Fail{E.FdtBadString{}} : Result<&2, &2, E.FdtError, B.Octets>}

law strings_vector:
  {P.FdtProp.strings(B.Octets.of_list([97, 0, 0, 98, 99, 0])) == Done{[B.Octets.of_string("a"), B.Octets.empty(), B.Octets.of_string("bc")]} : Result<&2, &2, E.FdtError, List<&2, B.Octets>>}

law strings_unterminated:
  {P.FdtProp.strings(B.Octets.of_list([97, 0, 98])) == Fail{E.FdtBadString{}} : Result<&2, &2, E.FdtError, List<&2, B.Octets>>}

law cells_bad_length:
  {P.FdtProp.cells(B.Octets.of_list([0, 0, 0, 1, 2])) == Fail{E.FdtBadLength{}} : Result<&2, &2, E.FdtError, List<&2, U32>>}

# two cells of address, two of size
law reg_vector:
  {P.FdtProp.reg(2n, 2n, P.FdtProp.of_cells([0, 4096, 1, 0])) == Done{[P.FdtReg{W.W64.from_parts(0, 4096), W.W64.from_parts(1, 0)}]} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}

law reg_bad_cells:
  {P.FdtProp.reg(3n, 1n, P.FdtProp.of_cells([0, 0, 0, 0])) == Fail{E.FdtBadCells{}} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}

law reg_bad_length:
  {P.FdtProp.reg(1n, 1n, P.FdtProp.of_cells([0, 0, 0])) == Fail{E.FdtBadLength{}} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}

# Vectors: lookups in the sample tree

law find_cpu:
  {Pa.FdtNode.find_prop(X.FdtExample.tree(), "/cpus/cpu@1", "reg") == Some{P.FdtProp.of_u32(1)} : Maybe<&2, B.Octets>}

# a name without its unit address finds the first match
law find_cpu_base:
  {Pa.FdtNode.find_prop(X.FdtExample.tree(), "/cpus/cpu", "reg") == Some{P.FdtProp.of_u32(0)} : Maybe<&2, B.Octets>}

law find_alias:
  {Pa.FdtNode.find_prop(X.FdtExample.tree(), "serial0", "compatible") == Some{P.FdtProp.of_text("ns16550")} : Maybe<&2, B.Octets>}

law find_missing:
  {Pa.FdtNode.find(X.FdtExample.tree(), "/cpus/cpu@2") == None{} : Maybe<&2, T.FdtNode>}

law find_bootargs:
  {Pa.FdtNode.find_prop(X.FdtExample.tree(), "/chosen", "bootargs") == Some{P.FdtProp.of_text("root=/dev/sda2")} : Maybe<&2, B.Octets>}

# 0xfe001000 = 4261416960; the root has one address cell and one size cell
law find_reg_uart:
  {Pa.FdtNode.find_reg(X.FdtExample.tree(), "/uart@fe001000") == Some{Done{[P.FdtReg{W.W64.from_u32(4261416960), W.W64.from_u32(256)}]}} : Maybe<&2, Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>>}

# /cpus has one address cell and no size cells
law find_reg_cpu:
  {Pa.FdtNode.find_reg(X.FdtExample.tree(), "/cpus/cpu@1") == Some{Done{[P.FdtReg{W.W64.from_u32(1), W.W64.zero()}]}} : Maybe<&2, Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>>}

law address_cells_default:
  {Pa.FdtNode.address_cells(T.FdtNode{B.Octets.empty(), [], []}) == 2n : Nat}

law size_cells_default:
  {Pa.FdtNode.size_cells(T.FdtNode{B.Octets.empty(), [], []}) == 1n : Nat}

law find_phandle:
  {Pa.FdtNode.find_phandle(T.FdtNode{B.Octets.empty(), [], [T.FdtNode{B.Octets.of_string("dev"), [T.FdtProp{B.Octets.of_string("interrupt-parent"), P.FdtProp.of_u32(1)}], []}, T.FdtNode{B.Octets.of_string("pic"), [T.FdtProp{B.Octets.of_string("phandle"), P.FdtProp.of_u32(1)}], []}]}, 1) == Some{T.FdtNode{B.Octets.of_string("pic"), [T.FdtProp{B.Octets.of_string("phandle"), P.FdtProp.of_u32(1)}], []}} : Maybe<&2, T.FdtNode>}

# Vectors: blobs. The sample tree's bytes were computed by ref/gen.py's
# writer and checked with dtc; the malformed blobs are a small tree's blob
# (root with "a" = "x", child "n") with one change each, and the error is
# the one ref/gen.py's reader gives.

law empty_blob:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.empty()) == Fail{E.FdtTooShort{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

law zero_magic:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.zeros(64n)) == Fail{E.FdtBadMagic{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# the sample tree, written with the simple strings block
law example_build:
  {B.Octets.hex(F.Fdt.build(X.FdtExample.tree(), X.FdtExample.rsv(), 0)) == "d00dfeed00000331000000480000025400000028000000110000001000000000000000dd0000020c00000000100000000000000000010000000000000000000000000000000000000000000100000000000000030000000e0000000066736c2c6d7063383537326473000000000000030000000e0000000666736c2c6d7063383537326473000000000000030000000400000011000000010000000300000004000000200000000100000001637075730000000000000003000000040000002c0000000100000003000000040000003b000000000000000163707540300000000000000300000004000000476370750000000003000000040000005300000000000000030000000400000057312c804000000003000000040000006a312c80400000000200000001637075403100000000000003000000040000007a637075000000000300000004000000860000000100000003000000040000008a312c804000000003000000040000009d312c80400000000200000002000000016d656d6f72794030000000000000000300000007000000ad6d656d6f727900000000000300000008000000b900000000200000000000000200000001756172744066653030313030300000000000000300000008000000bd6e733136353530000000000300000008000000c8fe00100000000100000000020000000163686f73656e0000000000030000000f000000cc726f6f743d2f6465762f7364613200000000000200000001616c696173657300000000030000000f000000d52f7561727440666530303130303000000000000200000002000000096d6f64656c00636f6d70617469626c650023616464726573732d63656c6c73002373697a652d63656c6c730023616464726573732d63656c6c73002373697a652d63656c6c73006465766963655f74797065007265670074696d65626173652d6672657175656e637900636c6f636b2d6672657175656e6379006465766963655f74797065007265670074696d65626173652d6672657175656e637900636c6f636b2d6672657175656e6379006465766963655f747970650072656700636f6d70617469626c650072656700626f6f74617267730073657269616c3000" : String}

# the same tree with each name once: the 708 bytes dtc 1.7.0 writes for its
# source (ref/gen.py checks this for random trees too)
law example_dtc:
  {B.Octets.hex(F.Fdt.build_with(T.FdtStringsDedup{}, X.FdtExample.tree(), X.FdtExample.rsv(), 0)) == "d00dfeed000002c4000000480000025400000028000000110000001000000000000000700000020c00000000100000000000000000010000000000000000000000000000000000000000000100000000000000030000000e0000000066736c2c6d7063383537326473000000000000030000000e0000000666736c2c6d70633835373264730000000000000300000004000000110000000100000003000000040000002000000001000000016370757300000000000000030000000400000011000000010000000300000004000000200000000000000001637075403000000000000003000000040000002c637075000000000300000004000000380000000000000003000000040000003c312c804000000003000000040000004f312c80400000000200000001637075403100000000000003000000040000002c637075000000000300000004000000380000000100000003000000040000003c312c804000000003000000040000004f312c80400000000200000002000000016d656d6f727940300000000000000003000000070000002c6d656d6f7279000000000003000000080000003800000000200000000000000200000001756172744066653030313030300000000000000300000008000000066e73313635353000000000030000000800000038fe00100000000100000000020000000163686f73656e0000000000030000000f0000005f726f6f743d2f6465762f7364613200000000000200000001616c696173657300000000030000000f000000682f7561727440666530303130303000000000000200000002000000096d6f64656c00636f6d70617469626c650023616464726573732d63656c6c73002373697a652d63656c6c73006465766963655f74797065007265670074696d65626173652d6672657175656e637900636c6f636b2d6672657175656e637900626f6f74617267730073657269616c3000" : String}

# dtc's blob for the sample source reads as the sample tree
law example_parse_dtc:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237, 0, 0, 2, 196, 0, 0, 0, 72, 0, 0, 2, 84, 0, 0, 0, 40, 0, 0, 0, 17, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 112, 0, 0, 2, 12, 0, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 14, 0, 0, 0, 0, 102, 115, 108, 44, 109, 112, 99, 56, 53, 55, 50, 100, 115, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 14, 0, 0, 0, 6, 102, 115, 108, 44, 109, 112, 99, 56, 53, 55, 50, 100, 115, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 32, 0, 0, 0, 1, 0, 0, 0, 1, 99, 112, 117, 115, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 17, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 1, 99, 112, 117, 64, 48, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 44, 99, 112, 117, 0, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 56, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 60, 49, 44, 128, 64, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 79, 49, 44, 128, 64, 0, 0, 0, 2, 0, 0, 0, 1, 99, 112, 117, 64, 49, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 44, 99, 112, 117, 0, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 56, 0, 0, 0, 1, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 60, 49, 44, 128, 64, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 79, 49, 44, 128, 64, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 1, 109, 101, 109, 111, 114, 121, 64, 48, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 7, 0, 0, 0, 44, 109, 101, 109, 111, 114, 121, 0, 0, 0, 0, 0, 3, 0, 0, 0, 8, 0, 0, 0, 56, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 117, 97, 114, 116, 64, 102, 101, 48, 48, 49, 48, 48, 48, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 8, 0, 0, 0, 6, 110, 115, 49, 54, 53, 53, 48, 0, 0, 0, 0, 3, 0, 0, 0, 8, 0, 0, 0, 56, 254, 0, 16, 0, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 1, 99, 104, 111, 115, 101, 110, 0, 0, 0, 0, 0, 3, 0, 0, 0, 15, 0, 0, 0, 95, 114, 111, 111, 116, 61, 47, 100, 101, 118, 47, 115, 100, 97, 50, 0, 0, 0, 0, 0, 2, 0, 0, 0, 1, 97, 108, 105, 97, 115, 101, 115, 0, 0, 0, 0, 3, 0, 0, 0, 15, 0, 0, 0, 104, 47, 117, 97, 114, 116, 64, 102, 101, 48, 48, 49, 48, 48, 48, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 9, 109, 111, 100, 101, 108, 0, 99, 111, 109, 112, 97, 116, 105, 98, 108, 101, 0, 35, 97, 100, 100, 114, 101, 115, 115, 45, 99, 101, 108, 108, 115, 0, 35, 115, 105, 122, 101, 45, 99, 101, 108, 108, 115, 0, 100, 101, 118, 105, 99, 101, 95, 116, 121, 112, 101, 0, 114, 101, 103, 0, 116, 105, 109, 101, 98, 97, 115, 101, 45, 102, 114, 101, 113, 117, 101, 110, 99, 121, 0, 99, 108, 111, 99, 107, 45, 102, 114, 101, 113, 117, 101, 110, 99, 121, 0, 98, 111, 111, 116, 97, 114, 103, 115, 0, 115, 101, 114, 105, 97, 108, 48, 0])) == Done{F.FdtBlob{17, 0, X.FdtExample.rsv(), X.FdtExample.tree()}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# a magic and nothing else (error too_short)
law reject_short:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237])) == Fail{E.FdtTooShort{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# version 18 (error bad_version)
law reject_version:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 102, 0, 0, 0, 56, 0, 0, 0, 100, 0, 0, 0, 40, 0, 0, 0, 18, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Fail{E.FdtBadVersion{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# version 16 when only 17 is accepted (error bad_version)
law reject_v16_only17:
  {F.Fdt.parse(F.FdtOptions{H.FdtV17Only{}, T.FdtTreeRules.default()}, B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 102, 0, 0, 0, 56, 0, 0, 0, 100, 0, 0, 0, 40, 0, 0, 0, 16, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Fail{E.FdtBadVersion{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# last_comp_version 18 (error bad_last_comp)
law reject_last_comp:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 102, 0, 0, 0, 56, 0, 0, 0, 100, 0, 0, 0, 40, 0, 0, 0, 17, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Fail{E.FdtBadLastComp{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# totalsize one past the blob (error bad_total_size)
law reject_total_size:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 103, 0, 0, 0, 56, 0, 0, 0, 100, 0, 0, 0, 40, 0, 0, 0, 17, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Fail{E.FdtBadTotalSize{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# off_mem_rsvmap not 8-aligned (error bad_rsvmap)
law reject_rsvmap:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 102, 0, 0, 0, 56, 0, 0, 0, 100, 0, 0, 0, 44, 0, 0, 0, 17, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Fail{E.FdtBadRsvmap{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# off_dt_struct not 4-aligned (error bad_struct)
law reject_struct:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 102, 0, 0, 0, 58, 0, 0, 0, 100, 0, 0, 0, 40, 0, 0, 0, 17, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Fail{E.FdtBadStruct{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# the strings block one byte past totalsize (error bad_strings)
law reject_strings:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 102, 0, 0, 0, 56, 0, 0, 0, 100, 0, 0, 0, 40, 0, 0, 0, 17, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Fail{E.FdtBadStrings{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# the reservation block read from the structure block, which holds no 0, 0 entry (error rsv_unterminated)
law reject_rsv_unterminated:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 102, 0, 0, 0, 56, 0, 0, 0, 100, 0, 0, 0, 56, 0, 0, 0, 17, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Fail{E.FdtRsvUnterminated{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# the root's FDT_BEGIN_NODE replaced by tag 5 (error bad_token 5)
law reject_token:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 102, 0, 0, 0, 56, 0, 0, 0, 100, 0, 0, 0, 40, 0, 0, 0, 17, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Fail{E.FdtBadToken{5}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# size_dt_struct four bytes short: no FDT_END (error truncated)
law reject_truncated:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 102, 0, 0, 0, 56, 0, 0, 0, 100, 0, 0, 0, 40, 0, 0, 0, 17, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 40, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Fail{E.FdtTruncated{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# size_dt_struct two bytes long: bytes after FDT_END (error after_end)
law reject_after_end:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 102, 0, 0, 0, 56, 0, 0, 0, 100, 0, 0, 0, 40, 0, 0, 0, 17, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 46, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Fail{E.FdtAfterEnd{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# the root's FDT_END_NODE replaced by FDT_NOP (error unbalanced)
law reject_unbalanced:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 102, 0, 0, 0, 56, 0, 0, 0, 100, 0, 0, 0, 40, 0, 0, 0, 17, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 9, 97, 0])) == Fail{E.FdtUnbalanced{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# a structure block of FDT_END alone (error no_root)
law reject_no_root:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 102, 0, 0, 0, 56, 0, 0, 0, 100, 0, 0, 0, 40, 0, 0, 0, 17, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Fail{E.FdtNoRoot{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# the property moved after the child (error prop_after_node)
law reject_prop_after_node:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 102, 0, 0, 0, 56, 0, 0, 0, 100, 0, 0, 0, 40, 0, 0, 0, 17, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Fail{E.FdtPropAfterNode{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# the same, with properties after children allowed (ok 17)
law lenient_prop_after_node:
  {F.Fdt.parse(F.FdtOptions{H.FdtV16V17{}, T.FdtTreeRules{True{}, False{}}}, B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 102, 0, 0, 0, 56, 0, 0, 0, 100, 0, 0, 0, 40, 0, 0, 0, 17, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Done{F.FdtBlob{17, 0, [], T.FdtNode{B.Octets.empty(), [T.FdtProp{B.Octets.of_string("a"), P.FdtProp.of_text("x")}], [T.FdtNode{B.Octets.of_string("n"), [], []}]}}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# a nameoff past the strings block (error bad_nameoff)
law reject_nameoff:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 102, 0, 0, 0, 56, 0, 0, 0, 100, 0, 0, 0, 40, 0, 0, 0, 17, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 44, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 100, 120, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Fail{E.FdtBadNameOff{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# a blob with FDT_NOPs, when the options refuse them (error nop_refused)
law reject_nop:
  {F.Fdt.parse(F.FdtOptions{H.FdtV16V17{}, T.FdtTreeRules{False{}, True{}}}, B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 106, 0, 0, 0, 56, 0, 0, 0, 104, 0, 0, 0, 40, 0, 0, 0, 17, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Fail{E.FdtNopRefused{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}

# the same blob, by default (ok 17)
law accept_nop:
  {F.Fdt.parse(F.FdtOptions.default(), B.Octets.of_list([208, 13, 254, 237, 0, 0, 0, 106, 0, 0, 0, 56, 0, 0, 0, 104, 0, 0, 0, 40, 0, 0, 0, 17, 0, 0, 0, 16, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 48, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 2, 0, 0, 0, 0, 120, 0, 0, 0, 0, 0, 0, 1, 110, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 9, 97, 0])) == Done{F.FdtBlob{17, 0, [], T.FdtNode{B.Octets.empty(), [T.FdtProp{B.Octets.of_string("a"), P.FdtProp.of_text("x")}], [T.FdtNode{B.Octets.of_string("n"), [], []}]}}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
