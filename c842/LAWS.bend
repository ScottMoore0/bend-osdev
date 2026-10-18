# Properties, for every input:
# * packing: a stream's bytes unpack to its bits, then zero bits;
# * the literal stream decodes back to its bytes whenever the maximum holds
#   them, and is exactly the documented worst case long (69 bits a chunk);
# * what the compressor writes decodes back to its input, with any options,
#   and is no longer than the worst case;
# * the decoder never answers more than its maximum, ignores whatever
#   follows a valid stream, and answers the same fed in any pieces;
# * a stream that opens with code 26 or 31, with RPT (no 8 bytes to repeat)
#   or with short data of count 0 is refused, whatever follows.
#
# Vectors: the paper's example (Z8, RPT(63): 512 zero bytes in 16 bits),
# Linux's streams for chosen inputs (ref/OBSERVATIONS.md), each template of
# the patent's Figure 3 as Linux decodes it, each failure, the CRC's check
# value, the worst case.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./format.bend as F
import ./crc.bend as K
import ./decode.bend as D
import ./match.bend as M
import ./encode.bend as C
import ./c842.bend as L

# Properties, for every input

# a stream's bytes unpack to its bits, then the zero bits that fill its last
# 8-byte word
law pack_round_trip:
  for +bs: List<&2, Bool>
  {F.c842.unpack(F.c842.pack(bs)) == F.c842.fmt.cat(bs, F.c842.fmt.zeros(F.c842.pack.fill(bs))) : List<&2, Bool>}

law literals_round_trip:
  for +o: B.Octets
  for +k: Nat
  {D.c842.decompress(C.c842.literals(o), Nat.add(B.Octets.len(o), k)) == Done{o} : Result<&2, &2, E.C842Error, B.Octets>}

law compress_round_trip:
  for +opts: C.C842CompressOptions
  for +o: B.Octets
  {D.c842.decompress(C.c842.compress_with(opts, o), B.Octets.len(o)) == Done{o} : Result<&2, &2, E.C842Error, B.Octets>}

# the literal stream is the documented worst case: 69 bits for each chunk,
# the tail's short data, the end and its CRC (before padding)
law literal_bits_worst:
  for +o: B.Octets
  {List.length(&2, Bool, C.c842.literal_bits(o)) == F.c842.worst_bits(B.Octets.len(o)) : Nat}

# the compressor's stream is no longer than that
law compress_within_worst:
  for +opts: C.C842CompressOptions
  for +o: B.Octets
  {Nat.is_le(List.length(&2, Bool, C.c842.compress_bits(opts, o)), F.c842.worst_bits(B.Octets.len(o))) == True{} : Bool}

# and its bytes are those bits, packed
law compress_packs:
  for +opts: C.C842CompressOptions
  for +o: B.Octets
  {C.c842.compress_with(opts, o) == F.c842.pack(C.c842.compress_bits(opts, o)) : B.Octets}

# a valid stream followed by anything decodes as the stream alone (Linux
# ignores what follows the CRC: ref/OBSERVATIONS.md, E2)
law trailing_ignored:
  for +s: B.Octets
  for +t: B.Octets
  for +max: Nat
  for +o: B.Octets
  for e: {D.c842.decompress(s, max) == Done{o} : Result<&2, &2, E.C842Error, B.Octets>}
  {D.c842.decompress(B.Octets.append(s, t), max) == Done{o} : Result<&2, &2, E.C842Error, B.Octets>}

# Linux's stream for 8 zero bytes (Z8, the end, CRC 0): the hypothesis can
# hold
law trailing_ignored_witness:
  exs o: B.Octets
  {D.c842.decompress(B.Octets.of_list([231, 128, 0, 0, 0, 0, 0, 0]), 8n) == Done{o} : Result<&2, &2, E.C842Error, B.Octets>}

def C842Laws.join(ps: List<&2, B.Octets>) -> B.Octets:
  match ps:
    case Nil{}:
      B.Octets.empty()
    case Con{p, t}:
      B.Octets.append(p, C842Laws.join(t))

# the reader, fed a stream in any pieces, answers what decompress answers for
# the pieces joined
law reader_pieces:
  for +max: Nat
  for +ps: List<&2, B.Octets>
  {D.c842.reader_decompress(max, ps) == D.c842.decompress(C842Laws.join(ps), max) : Result<&2, &2, E.C842Error, B.Octets>}

# A stream that cannot start: its first code is 26 or 31 (invalid), RPT
# (nothing to repeat) or short data with count 0, whatever follows. lo's low
# 3 bits fill the rest of the first byte.

law code26_rejected:
  for +lo: U32
  for +rest: B.Octets
  for +max: Nat
  {D.c842.decompress(B.Octets.cons(U32.or(208, U32.and(7, lo)), rest), max) == Fail{E.C842BadTemplate{}} : Result<&2, &2, E.C842Error, B.Octets>}

law code31_rejected:
  for +lo: U32
  for +rest: B.Octets
  for +max: Nat
  {D.c842.decompress(B.Octets.cons(U32.or(248, U32.and(7, lo)), rest), max) == Fail{E.C842BadTemplate{}} : Result<&2, &2, E.C842Error, B.Octets>}

# RPT's 6-bit field takes lo's 3 bits and the second byte's top 3
law repeat_first_rejected:
  for +lo: U32
  for +b: U32
  for +rest: B.Octets
  for +max: Nat
  {D.c842.decompress(B.Octets.cons(U32.or(216, U32.and(7, lo)), B.Octets.cons(b, rest)), max) == Fail{E.C842BadRepeat{}} : Result<&2, &2, E.C842Error, B.Octets>}

# 11101 000: short data, count 0
law short_zero_rejected:
  for +rest: B.Octets
  for +max: Nat
  {D.c842.decompress(B.Octets.cons(232, rest), max) == Fail{E.C842BadShort{}} : Result<&2, &2, E.C842Error, B.Octets>}

# The decoder never answers more than its maximum
law output_within_max:
  for +src: B.Octets
  for +max: Nat
  {Nat.is_le(B.Octets.len(Result.default(&2, &2, E.C842Error, B.Octets, D.c842.decompress(src, max), B.Octets.empty())), max) == True{} : Bool}

# Vectors (generated by gen/vectors.py)

# the paper's example, Z8 then RPT(63): 512 zero bytes in 5 + 5 + 6 bits
# (RPT's field holds 62: 63 more chunks; E1); then the end, CRC 0
law paper_z8_rpt63:
  {D.c842.decompress(B.Octets.of_list([230, 254, 240, 0, 0, 0, 0, 0]), 512n) == Done{B.Octets.zeros(512n)} : Result<&2, &2, E.C842Error, B.Octets>}

# those two codes are 16 bits
law paper_z8_rpt63_bits:
  {List.length(&2, Bool, F.c842.serialise([F.C842Zero{}, F.C842Repeat{62}])) == 16n : Nat}

# P8 and its 8-bit pointer: 13 bits for 8 bytes
law paper_p8_bits:
  {List.length(&2, Bool, F.c842.fmt.token(F.C842Chunk{25, [F.C842Ptr{0}]})) == 13n : Nat}

# the paper's P4_P2_LL: a 4-byte pointer, a 2-byte pointer, a literal
# (the patent's state 22)
law paper_p4_p2_ll:
  {F.c842.template(22) == Some{[F.C842P4{}, F.C842P2{}, F.C842LL{}]} : Maybe<&2, List<&2, F.C842Kind>>}

# the most a chunk takes: 69 bits (a template and four literals)
law paper_max_69:
  {List.length(&2, Bool, F.c842.fmt.token(F.C842Chunk{0, [F.C842Lit{1, 2}, F.C842Lit{3, 4}, F.C842Lit{5, 6}, F.C842Lit{7, 8}]})) == 69n : Nat}

# 26 templates (the patent's Figure 3, states 0 to 25)
law templates_26:
  {List.length(&2, List<&2, F.C842Kind>, F.c842.templates()) == 26n : Nat}

# Linux's streams (E1). 01 02 ... 08: template 0, the end, CRC 0x7D0F3681
law linux_ramp8:
  {L.compress(B.Octets.of_list([1, 2, 3, 4, 5, 6, 7, 8])) == B.Octets.of_list([0, 8, 16, 24, 32, 40, 48, 56, 71, 159, 67, 205, 160, 64, 0, 0]) : B.Octets}

# one byte: short data
law linux_ramp1:
  {L.compress(B.Octets.of_list([1])) == B.Octets.of_list([233, 1, 240, 38, 8, 237, 184, 0]) : B.Octets}

# nine bytes: a chunk, then short data
law linux_ramp9:
  {L.compress(B.Octets.of_list([1, 2, 3, 4, 5, 6, 7, 8, 9])) == B.Octets.of_list([0, 8, 16, 24, 32, 40, 48, 56, 71, 72, 79, 191, 33, 186, 142, 192]) : B.Octets}

# eight zero bytes: Z8
law linux_zeros8:
  {L.compress(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0])) == B.Octets.of_list([231, 128, 0, 0, 0, 0, 0, 0]) : B.Octets}

# 24 zero bytes: Z8, RPT(1)
law linux_zeros24:
  {L.compress(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) == B.Octets.of_list([230, 193, 240, 0, 0, 0, 0, 0]) : B.Octets}

# a chunk twice: RPT(0)
law linux_repeat:
  {L.compress(B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 65, 66, 67, 68, 69, 70, 71, 72])) == B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 70, 192, 241, 116, 204, 202, 112, 0]) : B.Octets}

# a 4-byte phrase seen before: template 20 (P4 LL LL), index 0
law linux_p4_ll_ll:
  {L.compress(B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 65, 66, 67, 68, 119, 120, 121, 122])) == B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 69, 0, 14, 239, 15, 47, 94, 33, 43, 10, 64, 0, 0, 0, 0, 0]) : B.Octets}

# both halves seen: template 24 (P4 P4), indices 1 and 0
law linux_p4_p4:
  {L.compress(B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 69, 70, 71, 72, 65, 66, 67, 68])) == B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 70, 0, 32, 15, 61, 160, 223, 201, 128, 0, 0, 0, 0, 0, 0, 0]) : B.Octets}

# 2-byte phrases: template 11 (P2 LL LL P2), indices 0 and 3
law linux_p2:
  {L.compress(B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 65, 66, 119, 120, 121, 122, 71, 72])) == B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 66, 192, 29, 222, 30, 94, 128, 253, 148, 148, 171, 30, 0, 0, 0, 0]) : B.Octets}

# a chunk seen two chunks back: template 25 (P8), index 0
law linux_p8:
  {L.compress(B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 65, 66, 67, 68, 69, 70, 71, 72])) == B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 50, 1, 233, 22, 69, 187, 144]) : B.Octets}

# Linux's decoder (E2): each template after ABCDEFGH and abcdefgh as
# literals. template 0 (LL LL LL LL)
law linux_template0:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 0, 162, 164, 164, 166, 166, 168, 168, 171, 227, 147, 10, 136, 176, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 81, 82, 82, 83, 83, 84, 84, 85])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 1 (LL LL LL P2)
law linux_template1:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 2, 162, 164, 164, 166, 166, 168, 15, 233, 237, 107, 18, 224, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 81, 82, 82, 83, 83, 84, 103, 104])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 2 (LL LL P2 LL)
law linux_template2:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 4, 162, 164, 164, 166, 6, 168, 171, 234, 111, 205, 119, 144, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 81, 82, 82, 83, 71, 72, 84, 85])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 3 (LL LL P2 P2)
law linux_template3:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 6, 162, 164, 164, 166, 6, 15, 224, 17, 172, 237, 192, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 81, 82, 82, 83, 71, 72, 103, 104])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 4 (LL LL P4)
law linux_template4:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 8, 162, 164, 164, 166, 3, 243, 55, 85, 249, 240, 0, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 81, 82, 82, 83, 101, 102, 103, 104])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 5 (LL P2 LL LL)
law linux_template5:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 10, 162, 164, 12, 166, 168, 168, 171, 228, 250, 82, 42, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 81, 82, 101, 102, 83, 84, 84, 85])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 6 (LL P2 LL P2)
law linux_template6:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 12, 162, 164, 12, 166, 168, 15, 238, 132, 51, 176, 80, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 81, 82, 101, 102, 83, 84, 103, 104])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 7 (LL P2 P2 LL)
law linux_template7:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 14, 162, 164, 12, 6, 168, 171, 237, 6, 149, 213, 32, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 81, 82, 101, 102, 71, 72, 84, 85])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 8 (LL P2 P2 P2)
law linux_template8:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 16, 162, 164, 12, 6, 15, 231, 120, 244, 79, 112, 0, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 81, 82, 101, 102, 71, 72, 103, 104])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 9 (LL P2 P4)
law linux_template9:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 18, 162, 164, 12, 3, 240, 131, 249, 168, 168, 0, 0, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 81, 82, 101, 102, 101, 102, 103, 104])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 10 (P2 LL LL LL)
law linux_template10:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 20, 2, 164, 166, 166, 168, 168, 171, 230, 46, 178, 204, 144, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 67, 68, 82, 83, 83, 84, 84, 85])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 11 (P2 LL LL P2)
law linux_template11:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 22, 2, 164, 166, 166, 168, 15, 236, 80, 211, 86, 192, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 67, 68, 82, 83, 83, 84, 103, 104])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 12 (P2 LL P2 LL)
law linux_template12:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 24, 2, 164, 166, 6, 168, 171, 239, 210, 117, 51, 176, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 67, 68, 82, 83, 71, 72, 84, 85])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 13 (P2 LL P2 P2)
law linux_template13:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 26, 2, 164, 166, 6, 15, 229, 172, 20, 169, 224, 0, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 67, 68, 82, 83, 71, 72, 103, 104])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 14 (P2 LL P4)
law linux_template14:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 28, 2, 164, 166, 3, 241, 233, 137, 219, 224, 0, 0, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 67, 68, 82, 83, 101, 102, 103, 104])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 15 (P2 P2 LL LL)
law linux_template15:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 30, 2, 12, 166, 168, 168, 171, 225, 71, 234, 110, 32, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 67, 68, 101, 102, 83, 84, 84, 85])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 16 (P2 P2 LL P2)
law linux_template16:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 32, 2, 12, 166, 168, 15, 235, 57, 139, 244, 112, 0, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 67, 68, 101, 102, 83, 84, 103, 104])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 17 (P2 P2 P2 LL)
law linux_template17:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 34, 2, 12, 6, 168, 171, 232, 187, 45, 145, 0, 0, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 67, 68, 101, 102, 71, 72, 84, 85])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 18 (P2 P2 P2 P2)
law linux_template18:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 36, 2, 12, 6, 15, 226, 197, 76, 11, 80, 0, 0, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 67, 68, 101, 102, 71, 72, 103, 104])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 19 (P2 P2 P4)
law linux_template19:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 38, 2, 12, 3, 242, 93, 37, 138, 184, 0, 0, 0, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 67, 68, 101, 102, 101, 102, 103, 104])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 20 (P4 LL LL)
law linux_template20:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 40, 3, 82, 83, 83, 84, 247, 125, 247, 114, 40, 0, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 101, 102, 103, 104, 82, 83, 83, 84])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 21 (P4 LL P2)
law linux_template21:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 42, 3, 82, 83, 3, 246, 30, 176, 167, 88, 0, 0, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 101, 102, 103, 104, 82, 83, 71, 72])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 22 (P4 P2 LL)
law linux_template22:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 44, 3, 6, 83, 84, 246, 119, 33, 235, 184, 0, 0, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 101, 102, 103, 104, 101, 102, 83, 84])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 23 (P4 P2 P2)
law linux_template23:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 46, 3, 6, 3, 247, 20, 102, 62, 200, 0, 0, 0, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 101, 102, 103, 104, 101, 102, 71, 72])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 24 (P4 P4)
law linux_template24:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 48, 3, 0, 248, 205, 192, 71, 32, 0, 0, 0, 0, 0, 0, 0]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 101, 102, 103, 104, 69, 70, 71, 72])} : Result<&2, &2, E.C842Error, B.Octets>}

# template 25 (P8)
law linux_template25:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 50, 3, 224, 70, 178, 81, 96]), 24n) == Done{B.Octets.of_list([65, 66, 67, 68, 69, 70, 71, 72, 97, 98, 99, 100, 101, 102, 103, 104, 97, 98, 99, 100, 101, 102, 103, 104])} : Result<&2, &2, E.C842Error, B.Octets>}

# a flipped CRC bit: EINVAL
law linux_bad_crc:
  {D.c842.decompress(B.Octets.of_list([0, 8, 16, 24, 32, 40, 48, 56, 71, 159, 66, 205, 160, 64, 0, 0]), 100n) == Fail{E.C842BadCrc{}} : Result<&2, &2, E.C842Error, B.Octets>}

# cut inside the CRC: EOVERFLOW
law linux_cut:
  {D.c842.decompress(B.Octets.of_list([0, 8, 16, 24, 32, 40, 48, 56, 71, 159, 67, 205]), 100n) == Fail{E.C842Truncated{}} : Result<&2, &2, E.C842Error, B.Octets>}

# 16 bytes into 15: ENOSPC
law linux_no_room:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 64, 24, 88, 152, 217, 25, 89, 153, 218, 61, 119, 45, 207, 194, 0, 0]), 15n) == Fail{E.C842OutputTooLarge{}} : Result<&2, &2, E.C842Error, B.Octets>}

# bytes after the stream are ignored
law linux_trailing:
  {D.c842.decompress(B.Octets.of_list([0, 8, 16, 24, 32, 40, 48, 56, 71, 159, 67, 205, 160, 64, 0, 0, 5, 6]), 100n) == Done{B.Octets.of_list([1, 2, 3, 4, 5, 6, 7, 8])} : Result<&2, &2, E.C842Error, B.Octets>}

# P8 index 1 after one chunk: nothing written there yet, EINVAL
law linux_unwritten:
  {D.c842.decompress(B.Octets.of_list([2, 10, 18, 26, 34, 42, 50, 58, 70, 64, 124, 93, 51, 50, 156, 0]), 100n) == Fail{E.C842BadPointer{}} : Result<&2, &2, E.C842Error, B.Octets>}

# short data before a chunk: accepted, the output carries on
law linux_short_mid:
  {D.c842.decompress(B.Octets.of_list([235, 97, 98, 99, 2, 10, 18, 26, 34, 42, 50, 58, 71, 179, 39, 216, 162, 192, 0, 0, 0, 0, 0, 0]), 100n) == Done{B.Octets.of_list([97, 98, 99, 65, 66, 67, 68, 69, 70, 71, 72])} : Result<&2, &2, E.C842Error, B.Octets>}

# RPT after 3 bytes, which Linux reads before its buffer (E8): refused
law repeat_after_short:
  {D.c842.decompress(B.Octets.of_list([235, 97, 98, 99, 216, 30, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), 100n) == Fail{E.C842BadRepeat{}} : Result<&2, &2, E.C842Error, B.Octets>}

# the CRC's check value (of 123456789): 0x89A1897F
law crc_check:
  {K.c842.crc(B.Octets.of_string("123456789")) == 2309065087 : U32}

# the worst case for 8 bytes: 106 bits
law worst_8:
  {F.c842.worst_bits(8n) == 106n : Nat}

# for 64 bytes: 589 bits, in 80 bytes (Linux wrote 80 for 64 random bytes, E1)
law worst_64:
  {F.c842.worst_bytes(64n) == 80n : Nat}

# the format's parser: one byte is short data, then the end
law tokens_short:
  {F.c842.tokens(B.Octets.of_list([233, 1, 240, 38, 8, 237, 184, 0])) == Done{[F.C842Short{[1]}, F.C842End{79764919}]} : Result<&2, &2, E.C842Error, List<&2, F.C842Token>>}

