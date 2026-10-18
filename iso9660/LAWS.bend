# Properties, for every input:
#   * both-endian fields: a 32-bit field written and read back gives the
#     value; a 16-bit one gives its low 16 bits; trusting one half reads
#     that half whatever the other holds; and halves that differ are
#     refused when both are checked (with a witness that such halves exist);
#   * the 7-byte directory date: every date reads back as stored (each
#     field to 8 bits), and every 7 bytes read and written again are the
#     same 7 bytes;
#   * the 17-byte volume date: every date whose fields fit their digits
#     (year below 10000, the others below 100) reads back, its offset to
#     8 bits (with a witness);
#   * UCS-2 (Joliet) names: every text reads back, each code to 16 bits;
#   * directory records: every record of the stated class (a non-empty
#     identifier, a length below 256) reads back as stored, whatever bytes
#     follow it (with a witness);
#   * reading only what is needed: the records of a directory are the same
#     on a device fenced to the directory's own blocks; a step of a file
#     stream is the same on a device fenced to the one block it is at; and
#     the end of a stream reads nothing.
#
# Vectors: records, Rock Ridge entries and a date from an image genisoimage
# wrote; Joliet levels, identifiers, SUSP areas good and bad, Rock Ridge
# link text, a short or malformed record, a bad date, block counts.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as BD
import ./fields.bend as F
import ./joliet.bend as J
import ./dirrec.bend as R
import ./susp.bend as S
import ./rockridge.bend as RR
import ./dir.bend as DR
import ./file.bend as FL
import ./fence.bend as FN

# Both-endian fields

law both32_round_trip:
  for v: U32
  {F.Iso.both32_decode(F.IsoEndianCheck{}, F.Iso.both32_encode(v), 0n) == Done{v} : Result<&2, &2, F.IsoError, U32>}

law both16_round_trip:
  for v: U32
  {F.Iso.both16_decode(F.IsoEndianCheck{}, F.Iso.both16_encode(v), 0n) == Done{B.low16(v)} : Result<&2, &2, F.IsoError, U32>}

law both32_trust_little:
  for lo: U32
  for hi: U32
  {F.Iso.both32_decode(F.IsoEndianLittle{}, F.Iso.both32_encode_pair(lo, hi), 0n) == Done{lo} : Result<&2, &2, F.IsoError, U32>}

law both32_trust_big:
  for lo: U32
  for hi: U32
  {F.Iso.both32_decode(F.IsoEndianBig{}, F.Iso.both32_encode_pair(lo, hi), 0n) == Done{hi} : Result<&2, &2, F.IsoError, U32>}

law both32_mismatch:
  for lo: U32
  for hi: U32
  for h: {U32.is_eq(lo, hi) == False{} : Bool}
  {F.Iso.both32_decode(F.IsoEndianCheck{}, F.Iso.both32_encode_pair(lo, hi), 0n) == Fail{F.IsoBothEndianMismatch{0n}} : Result<&2, &2, F.IsoError, U32>}

law both32_mismatch_witness:
  {U32.is_eq(1, 2) == False{} : Bool}

law both16_mismatch:
  for lo: U32
  for hi: U32
  for h: {U32.is_eq(B.low16(lo), B.low16(hi)) == False{} : Bool}
  {F.Iso.both16_decode(F.IsoEndianCheck{}, F.Iso.both16_encode_pair(lo, hi), 0n) == Fail{F.IsoBothEndianMismatch{0n}} : Result<&2, &2, F.IsoError, U32>}

law both16_mismatch_witness:
  {U32.is_eq(B.low16(1), B.low16(2)) == False{} : Bool}

# Dates

law dir_date_round_trip:
  for d: F.IsoDirDate
  {F.IsoDirDate.decode(F.IsoDirDate.encode(d)) == Done{F.IsoDirDate.norm(d)} : Result<&2, &2, F.IsoError, F.IsoDirDate>}

law dir_date_bytes:
  for +a0: U32
  for +a1: U32
  for +a2: U32
  for +a3: U32
  for +a4: U32
  for +a5: U32
  for +a6: U32
  {Result.map(&2, &2, F.IsoError, F.IsoDirDate, B.Octets, F.IsoDirDate.encode, F.IsoDirDate.decode(B.Octets.of_list([a0, a1, a2, a3, a4, a5, a6]))) == Done{B.Octets.of_list([a0, a1, a2, a3, a4, a5, a6])} : Result<&2, &2, F.IsoError, B.Octets>}

law vol_date_round_trip:
  for d: F.IsoVolDate
  for h: {F.IsoVolDate.fits(d) == True{} : Bool}
  {F.IsoVolDate.decode(F.IsoVolDate.encode(d)) == Done{F.IsoVolDate.norm(d)} : Result<&2, &2, F.IsoError, F.IsoVolDate>}

law vol_date_witness:
  {F.IsoVolDate.fits(F.IsoVolDate{9999n, 12n, 31n, 23n, 59n, 59n, 99n, 208}) == True{} : Bool}

# Joliet names

law ucs2_round_trip:
  for +s: String
  {J.Iso.ucs2_decode(J.Iso.ucs2_encode(s)) == Done{J.Iso.ucs2_norm(s)} : Result<&2, &2, F.IsoError, String>}

# Directory records

law dirrec_round_trip:
  for r: R.IsoDirRec
  for rest: B.Octets
  for h: {R.IsoDirRec.fits(r) == True{} : Bool}
  {R.IsoDirRec.decode(F.IsoEndianCheck{}, B.Octets.append(R.IsoDirRec.encode(r), rest)) == Done{R.IsoDirRec.norm(r)} : Result<&2, &2, F.IsoError, R.IsoDirRec>}

law dirrec_witness:
  {R.IsoDirRec.fits(R.IsoDirRec{0, 19, 2048, F.IsoDirDate{126, 10, 17, 12, 0, 0, 4}, 2, 0, 0, 1, B.Octets.of_string("DIR"), B.Octets.of_list([78, 77, 8, 1, 0, 100, 105, 114])}) == True{} : Bool}

# Reading only what is needed

law dir_records_fenced:
  for +d: BD.MemDev
  for +mode: F.IsoEndian
  for +ext: U32
  for +size: U32
  {DR.Iso.dir_records(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, d, mode, ext, size) == DR.Iso.dir_records(~FN.IsoFence, ~FN.IsoFence.block_size, ~FN.IsoFence.read_block, FN.IsoFence{d, U32.to_nat(ext), R.Iso.blocks(size)}, mode, ext, size) : Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>}

law stream_step_fenced:
  for +d: BD.MemDev
  for +b: U32
  for +s: U32
  for +t: List<&2, DR.IsoExtent>
  for +i: Nat
  for +left: U32
  {FL.Iso.file_next(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, d, FL.IsoCursor{Con{DR.IsoExtent{b, s}, t}, i, left}) == FL.Iso.file_next(~FN.IsoFence, ~FN.IsoFence.block_size, ~FN.IsoFence.read_block, FN.IsoFence{d, Nat.add(U32.to_nat(b), i), 1n}, FL.IsoCursor{Con{DR.IsoExtent{b, s}, t}, i, left}) : Result<&2, &2, F.IsoError, FL.IsoChunk>}

law stream_end_reads_nothing:
  for d: FN.IsoFence
  for i: Nat
  for left: U32
  {FL.Iso.file_next(~FN.IsoFence, ~FN.IsoFence.block_size, ~FN.IsoFence.read_block, d, FL.IsoCursor{Nil{}, i, left}) == Done{FL.IsoChunkEnd{}} : Result<&2, &2, F.IsoError, FL.IsoChunk>}

# Vectors from an image genisoimage wrote (-R -J): the root directory's
# record in the primary descriptor, a file's record with its Rock Ridge
# entries (RR, NM, PX of RRIP 1.10, TF), and the creation date

law gi_root_record:
  {R.IsoDirRec.decode(F.IsoEndianCheck{}, B.Octets.of_list([34, 0, 28, 0, 0, 0, 0, 0, 0, 28, 0, 8, 0, 0, 0, 0, 8, 0, 126, 10, 17, 20, 45, 23, 4, 2, 0, 0, 1, 0, 0, 1, 1, 0])) == Done{R.IsoDirRec{0, 28, 2048, F.IsoDirDate{126, 10, 17, 20, 45, 23, 4}, 2, 0, 0, 1, B.Octets.of_list([0]), B.Octets.empty()}} : Result<&2, &2, F.IsoError, R.IsoDirRec>}

law gi_file_record:
  {Result.map(&2, &2, F.IsoError, R.IsoDirRec, Nat, R.IsoDirRec.length, R.IsoDirRec.decode(F.IsoEndianCheck{}, B.Octets.of_list([126, 0, 44, 0, 0, 0, 0, 0, 0, 44, 12, 0, 0, 0, 0, 0, 0, 12, 126, 10, 17, 20, 45, 23, 4, 0, 0, 0, 1, 0, 0, 1, 11, 72, 69, 76, 76, 79, 46, 84, 88, 84, 59, 49, 82, 82, 5, 1, 137, 78, 77, 14, 1, 0, 104, 101, 108, 108, 111, 46, 116, 120, 116, 80, 88, 36, 1, 164, 129, 0, 0, 0, 0, 129, 164, 1, 0, 0, 0, 0, 0, 0, 1, 232, 3, 0, 0, 0, 0, 3, 232, 232, 3, 0, 0, 0, 0, 3, 232, 84, 70, 26, 1, 14, 126, 10, 17, 20, 45, 23, 4, 126, 10, 17, 20, 45, 23, 4, 126, 10, 17, 20, 45, 23, 4, 0]))) == Done{126n} : Result<&2, &2, F.IsoError, Nat>}

law gi_file_rr_name:
  {Result.map(&2, &2, F.IsoError, RR.IsoRr, Maybe<&2, String>, RR.IsoRr.name_of, Result.bind(&2, &2, F.IsoError, List<&2, S.IsoSuspEntry>, RR.IsoRr, S.Iso.susp_parse(B.Octets.of_list([82, 82, 5, 1, 137, 78, 77, 14, 1, 0, 104, 101, 108, 108, 111, 46, 116, 120, 116, 80, 88, 36, 1, 164, 129, 0, 0, 0, 0, 129, 164, 1, 0, 0, 0, 0, 0, 0, 1, 232, 3, 0, 0, 0, 0, 3, 232, 232, 3, 0, 0, 0, 0, 3, 232, 84, 70, 26, 1, 14, 126, 10, 17, 20, 45, 23, 4, 126, 10, 17, 20, 45, 23, 4, 126, 10, 17, 20, 45, 23, 4, 0])), es => RR.Iso.rr_of(F.IsoEndianCheck{}, es))) == Done{Some{"hello.txt"}} : Result<&2, &2, F.IsoError, Maybe<&2, String>>}

law gi_creation_date:
  {F.IsoVolDate.decode(B.Octets.of_list([50, 48, 50, 54, 49, 48, 49, 55, 50, 48, 52, 53, 50, 51, 48, 48, 4])) == Done{F.IsoVolDate{2026n, 10n, 17n, 20n, 45n, 23n, 0n, 4}} : Result<&2, &2, F.IsoError, F.IsoVolDate>}

# Vectors

law joliet_level_3:
  {J.Iso.joliet_level(B.Octets.of_list([37, 47, 69])) == 3n : Nat}

law joliet_level_1:
  {J.Iso.joliet_level(B.Octets.of_list([37, 47, 64])) == 1n : Nat}

law joliet_level_none:
  {J.Iso.joliet_level(B.Octets.zeros(32n)) == 0n : Nat}

law text_trims_spaces:
  {F.Iso.text(B.Octets.of_string("CDROM   ")) == "CDROM" : String}

law ucs2_text:
  {J.Iso.ucs2_decode(B.Octets.of_list([0, 104, 0, 105, 0, 59, 0, 49])) == Done{"hi;1"} : Result<&2, &2, F.IsoError, String>}

law ucs2_odd_refused:
  {J.Iso.ucs2_decode(B.Octets.of_list([0, 104, 0])) == Fail{F.IsoBadJolietName{}} : Result<&2, &2, F.IsoError, String>}

law susp_two_entries:
  {Result.map(&2, &2, F.IsoError, List<&2, S.IsoSuspEntry>, Nat, es => List.length(&2, S.IsoSuspEntry, es), S.Iso.susp_parse(B.Octets.of_list([78, 77, 6, 1, 0, 120, 82, 69, 4, 1]))) == Done{2n} : Result<&2, &2, F.IsoError, Nat>}

law susp_stops_at_st:
  {Result.map(&2, &2, F.IsoError, List<&2, S.IsoSuspEntry>, Nat, es => List.length(&2, S.IsoSuspEntry, es), S.Iso.susp_parse(B.Octets.of_list([82, 69, 4, 1, 83, 84, 4, 1, 82, 69, 4, 1]))) == Done{1n} : Result<&2, &2, F.IsoError, Nat>}

law susp_short_length_refused:
  {S.Iso.susp_parse(B.Octets.of_list([78, 77, 3, 1, 0, 120])) == Fail{F.IsoBadSusp{}} : Result<&2, &2, F.IsoError, List<&2, S.IsoSuspEntry>>}

law susp_past_area_refused:
  {S.Iso.susp_parse(B.Octets.of_list([78, 77, 9, 1, 0, 120])) == Fail{F.IsoBadSusp{}} : Result<&2, &2, F.IsoError, List<&2, S.IsoSuspEntry>>}

law sp_skip:
  {S.Iso.susp_sp(B.Octets.of_list([83, 80, 7, 1, 190, 239, 0])) == Some{0n} : Maybe<&2, Nat>}

law rr_link_root:
  {RR.Iso.rr_link_text([RR.IsoSlComp{8, Nil{}}, RR.IsoSlComp{0, [117, 115, 114]}, RR.IsoSlComp{0, [98, 105, 110]}]) == "/usr/bin" : String}

law rr_link_continued:
  {RR.Iso.rr_link_text([RR.IsoSlComp{4, Nil{}}, RR.IsoSlComp{1, [108, 111]}, RR.IsoSlComp{0, [110, 103]}]) == "../long" : String}

law rr_name_from_nm:
  {Result.map(&2, &2, F.IsoError, RR.IsoRr, Maybe<&2, String>, RR.IsoRr.name_of, RR.Iso.rr_of(F.IsoEndianCheck{}, [S.IsoSuspEntry{78, 77, 1, B.Octets.of_list([1, 108, 111])}, S.IsoSuspEntry{78, 77, 1, B.Octets.of_list([0, 110, 103])}])) == Done{Some{"long"}} : Result<&2, &2, F.IsoError, Maybe<&2, String>>}

law rr_px_short_refused:
  {Result.map(&2, &2, F.IsoError, RR.IsoRr, Maybe<&2, String>, RR.IsoRr.name_of, RR.Iso.rr_of(F.IsoEndianCheck{}, [S.IsoSuspEntry{80, 88, 1, B.Octets.zeros(8n)}])) == Fail{F.IsoBadRrip{"PX"}} : Result<&2, &2, F.IsoError, Maybe<&2, String>>}

law dirrec_no_identifier:
  {R.IsoDirRec.decode(F.IsoEndianCheck{}, B.Octets.append(B.Octets.of_list([34, 0]), B.Octets.zeros(32n))) == Fail{F.IsoBadIdentifierLength{0n}} : Result<&2, &2, F.IsoError, R.IsoDirRec>}

law dirrec_truncated:
  {R.IsoDirRec.decode(F.IsoEndianCheck{}, B.Octets.zeros(20n)) == Fail{F.IsoTruncated{}} : Result<&2, &2, F.IsoError, R.IsoDirRec>}

law vol_date_bad_digit:
  {F.IsoVolDate.decode(B.Octets.of_string("20261017x23456780")) == Fail{F.IsoBadDate{}} : Result<&2, &2, F.IsoError, F.IsoVolDate>}

law blocks_round_up:
  {R.Iso.blocks(2049) == 2n : Nat}

law blocks_exact:
  {R.Iso.blocks(4096) == 2n : Nat}
