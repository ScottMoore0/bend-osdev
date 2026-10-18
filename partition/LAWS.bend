# Properties, for every input:
#   * MBR: parsing a built sector gives the table back, for every boot code
#     and table, as stored (Mbr.norm: status and type to 8 bits, CHS fields
#     to 8, 6 and 10 bits);
#   * GPT: a built header block carries a valid header CRC, and parsing it
#     gives the header back with that CRC (GptHeader.seal); an entry reads
#     back as written, its name as the 36 code units stored (GptEntry.norm);
#     the entries CRC of Gpt.build is the CRC-32 of the encoded entries.
#
# Vectors: sectors written by sgdisk (a GPT disk of 8192 blocks with two
# partitions) and sfdisk (an MBR disk with two partitions), their parsed
# fields and CRCs, rebuilding them byte for byte, the protective MBR, the
# standard layout, UTF-16 names, and malformed input.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ../crc/crc.bend as C
import ../uuid/uuid.bend as U
import ./mbr.bend as M
import ./gpt.bend as G
import ./partition.bend as P

# Properties, for every input

law mbr_round_trip:
  for +boot: B.Octets
  for +m: M.Mbr
  {M.Mbr.parse(M.Mbr.build(boot, m)) == Done{M.Mbr.norm(m)} : Result<&2, &2, M.MbrError, M.Mbr>}

law gpt_header_crc:
  for +h: G.GptHeader
  {G.Gpt.header_crc_ok(G.Gpt.build_header(h)) == True{} : Bool}

law gpt_header_round_trip:
  for +h: G.GptHeader
  {G.Gpt.parse_header(G.Gpt.build_header(h)) == Done{G.GptHeader.seal(h)} : Result<&2, &2, G.GptError, G.GptHeader>}

law gpt_entry_round_trip:
  for +e: G.GptEntry
  {G.GptEntry.decode(G.GptEntry.encode(e)) == Done{G.GptEntry.norm(e)} : Result<&2, &2, G.GptError, G.GptEntry>}

law gpt_build_entries_crc:
  for +h: G.GptHeader
  for +es: List<&2, G.GptEntry>
  {Result.map(&2, &2, G.GptError, G.GptHeader, U32, G.GptHeader.entries_crc, G.Gpt.parse_header(G.Gpt.build(h, es))) == Done{C.crc32(G.Gpt.entries_encode(es))} : Result<&2, &2, G.GptError, U32>}

# Vectors: the GPT header sgdisk wrote (header CRC 0xC6D3AB7D, entries CRC
# 0x92969633)

law sgdisk_header:
  {G.Gpt.validate_header(B.Octets.append(B.Octets.of_list([69, 70, 73, 32, 80, 65, 82, 84, 0, 0, 1, 0, 92, 0, 0, 0, 125, 171, 211, 198, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 255, 31, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 222, 31, 0, 0, 0, 0, 0, 0, 27, 48, 32, 148, 177, 137, 179, 64, 170, 235, 143, 149, 202, 132, 158, 228, 2, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 128, 0, 0, 0, 51, 150, 150, 146]), B.Octets.zeros(420n))) == Done{G.GptHeader{65536, 92, 3335760765, W.W64.from_u32(1), W.W64.from_u32(8191), W.W64.from_u32(34), W.W64.from_u32(8158), U.Uuid.make(148, 32, 48, 27, 137, 177, 64, 179, 170, 235, 143, 149, 202, 132, 158, 228), W.W64.from_u32(2), 128, 128, 2459342387}} : Result<&2, &2, G.GptError, G.GptHeader>}

law sgdisk_header_crc:
  {G.Gpt.header_crc(B.Octets.append(B.Octets.of_list([69, 70, 73, 32, 80, 65, 82, 84, 0, 0, 1, 0, 92, 0, 0, 0, 125, 171, 211, 198, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 255, 31, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 222, 31, 0, 0, 0, 0, 0, 0, 27, 48, 32, 148, 177, 137, 179, 64, 170, 235, 143, 149, 202, 132, 158, 228, 2, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 128, 0, 0, 0, 51, 150, 150, 146]), B.Octets.zeros(420n))) == 3335760765 : U32}

law sgdisk_header_rebuilt:
  {G.Gpt.build_header(G.GptHeader{65536, 92, 3335760765, W.W64.from_u32(1), W.W64.from_u32(8191), W.W64.from_u32(34), W.W64.from_u32(8158), U.Uuid.make(148, 32, 48, 27, 137, 177, 64, 179, 170, 235, 143, 149, 202, 132, 158, 228), W.W64.from_u32(2), 128, 128, 2459342387}) == B.Octets.append(B.Octets.of_list([69, 70, 73, 32, 80, 65, 82, 84, 0, 0, 1, 0, 92, 0, 0, 0, 125, 171, 211, 198, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 255, 31, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 222, 31, 0, 0, 0, 0, 0, 0, 27, 48, 32, 148, 177, 137, 179, 64, 170, 235, 143, 149, 202, 132, 158, 228, 2, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 128, 0, 0, 0, 51, 150, 150, 146]), B.Octets.zeros(420n)) : B.Octets}

law sgdisk_header_corrupt:
  {G.Gpt.validate_header(B.Octets.append(B.Octets.of_list([69, 70, 73, 32, 80, 65, 82, 84, 0, 0, 1, 0, 92, 0, 0, 0, 125, 171, 211, 198, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 255, 31, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 222, 31, 0, 0, 0, 0, 0, 0, 27, 48, 32, 148, 177, 137, 179, 64, 170, 235, 143, 149, 202, 132, 158, 228, 2, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 128, 0, 0, 0, 51, 150, 150, 146]), B.Octets.zeros(420n))) == Fail{G.GptBadHeaderCrc{}} : Result<&2, &2, G.GptError, G.GptHeader>}

law sgdisk_standard_layout:
  {G.GptHeader.standard(G.GptLayout.standard(), W.W64.from_u32(8192), U.Uuid.make(148, 32, 48, 27, 137, 177, 64, 179, 170, 235, 143, 149, 202, 132, 158, 228)) == G.GptHeader{65536, 92, 0, W.W64.from_u32(1), W.W64.from_u32(8191), W.W64.from_u32(34), W.W64.from_u32(8158), U.Uuid.make(148, 32, 48, 27, 137, 177, 64, 179, 170, 235, 143, 149, 202, 132, 158, 228), W.W64.from_u32(2), 128, 128, 0} : G.GptHeader}

# Vectors: its first entry, the EFI System Partition

law sgdisk_entry:
  {G.GptEntry.decode(B.Octets.of_list([40, 115, 42, 193, 31, 248, 210, 17, 186, 75, 0, 160, 201, 62, 201, 59, 86, 136, 248, 239, 76, 47, 115, 66, 174, 200, 39, 193, 68, 231, 165, 150, 0, 8, 0, 0, 0, 0, 0, 0, 255, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 0, 70, 0, 73, 0, 32, 0, 115, 0, 121, 0, 115, 0, 116, 0, 101, 0, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) == Done{G.GptEntry.norm(G.GptEntry{U.Uuid.make(193, 42, 115, 40, 248, 31, 17, 210, 186, 75, 0, 160, 201, 62, 201, 59), U.Uuid.make(239, 248, 136, 86, 47, 76, 66, 115, 174, 200, 39, 193, 68, 231, 165, 150), W.W64.from_u32(2048), W.W64.from_u32(4095), W.W64.zero(), G.Gpt.name_units("EFI system")})} : Result<&2, &2, G.GptError, G.GptEntry>}

law sgdisk_entry_rebuilt:
  {G.GptEntry.encode(G.GptEntry.norm(G.GptEntry{U.Uuid.make(193, 42, 115, 40, 248, 31, 17, 210, 186, 75, 0, 160, 201, 62, 201, 59), U.Uuid.make(239, 248, 136, 86, 47, 76, 66, 115, 174, 200, 39, 193, 68, 231, 165, 150), W.W64.from_u32(2048), W.W64.from_u32(4095), W.W64.zero(), G.Gpt.name_units("EFI system")})) == B.Octets.of_list([40, 115, 42, 193, 31, 248, 210, 17, 186, 75, 0, 160, 201, 62, 201, 59, 86, 136, 248, 239, 76, 47, 115, 66, 174, 200, 39, 193, 68, 231, 165, 150, 0, 8, 0, 0, 0, 0, 0, 0, 255, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 0, 70, 0, 73, 0, 32, 0, 115, 0, 121, 0, 115, 0, 116, 0, 101, 0, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) : B.Octets}

law sgdisk_entry_name:
  {Result.map(&2, &2, G.GptError, G.GptEntry, String, G.GptEntry.name_text, G.GptEntry.decode(B.Octets.of_list([40, 115, 42, 193, 31, 248, 210, 17, 186, 75, 0, 160, 201, 62, 201, 59, 86, 136, 248, 239, 76, 47, 115, 66, 174, 200, 39, 193, 68, 231, 165, 150, 0, 8, 0, 0, 0, 0, 0, 0, 255, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 0, 70, 0, 73, 0, 32, 0, 115, 0, 121, 0, 115, 0, 116, 0, 101, 0, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) == Done{"EFI system"} : Result<&2, &2, G.GptError, String>}

# Vectors: UTF-16 names (U+1F600 is the surrogate pair 0xD83D 0xDE00)

law name_surrogates:
  {G.Gpt.name_units(SCon{'a', SCon{Chr{128512}, SNil{}}}) == [97, 55357, 56832] : List<&2, U32>}

law name_text_surrogates:
  {G.GptEntry.name_text(G.GptEntry{U.Uuid.nil(), U.Uuid.nil(), W.W64.zero(), W.W64.zero(), W.W64.zero(), [97, 55357, 56832, 0, 98]}) == SCon{'a', SCon{Chr{128512}, SNil{}}} : String}

# Vectors: the protective MBR sgdisk wrote, and the MBR sfdisk wrote

law sgdisk_protective_mbr:
  {M.Mbr.build(B.Octets.empty(), M.Mbr.protective(W.W64.from_u32(8191))) == B.Octets.append(B.Octets.zeros(440n), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 238, 130, 2, 0, 1, 0, 0, 0, 255, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 170])) : B.Octets}

law sfdisk_mbr:
  {M.Mbr.parse(B.Octets.append(B.Octets.zeros(440n), B.Octets.of_list([120, 86, 52, 18, 0, 0, 128, 32, 33, 0, 131, 48, 48, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 48, 49, 0, 12, 65, 1, 0, 0, 12, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 170]))) == Done{M.Mbr{305419896, M.MbrEntry{128, M.MbrChs{32, 33, 0}, 131, M.MbrChs{48, 48, 0}, 2048, 1024}, M.MbrEntry{0, M.MbrChs{48, 49, 0}, 12, M.MbrChs{65, 1, 0}, 3072, 1024}, M.MbrEntry.empty(), M.MbrEntry.empty()}} : Result<&2, &2, M.MbrError, M.Mbr>}

law sfdisk_mbr_rebuilt:
  {M.Mbr.build(B.Octets.zeros(440n), M.Mbr{305419896, M.MbrEntry{128, M.MbrChs{32, 33, 0}, 131, M.MbrChs{48, 48, 0}, 2048, 1024}, M.MbrEntry{0, M.MbrChs{48, 49, 0}, 12, M.MbrChs{65, 1, 0}, 3072, 1024}, M.MbrEntry.empty(), M.MbrEntry.empty()}) == B.Octets.append(B.Octets.zeros(440n), B.Octets.of_list([120, 86, 52, 18, 0, 0, 128, 32, 33, 0, 131, 48, 48, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 48, 49, 0, 12, 65, 1, 0, 0, 12, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 170])) : B.Octets}

law chs_of_lba:
  {M.MbrChs.of_lba(M.MbrGeometry.standard(), 4095) == M.MbrChs{65, 1, 0} : M.MbrChs}

law chs_of_lba_too_far:
  {M.MbrChs.of_lba(M.MbrGeometry.standard(), 16450560) == M.MbrChs{255, 63, 1023} : M.MbrChs}

# Vectors: telling the schemes apart

law detect_gpt:
  {P.PartitionScheme.show(P.Partition.detect(B.Octets.append(B.Octets.zeros(440n), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 238, 130, 2, 0, 1, 0, 0, 0, 255, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 170])), B.Octets.append(B.Octets.of_list([69, 70, 73, 32, 80, 65, 82, 84, 0, 0, 1, 0, 92, 0, 0, 0, 125, 171, 211, 198, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 255, 31, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 222, 31, 0, 0, 0, 0, 0, 0, 27, 48, 32, 148, 177, 137, 179, 64, 170, 235, 143, 149, 202, 132, 158, 228, 2, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 128, 0, 0, 0, 51, 150, 150, 146]), B.Octets.zeros(420n)))) == "gpt" : String}

law detect_mbr:
  {P.PartitionScheme.show(P.Partition.detect(B.Octets.append(B.Octets.zeros(440n), B.Octets.of_list([120, 86, 52, 18, 0, 0, 128, 32, 33, 0, 131, 48, 48, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 48, 49, 0, 12, 65, 1, 0, 0, 12, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 170])), B.Octets.append(B.Octets.of_list([69, 70, 73, 32, 80, 65, 82, 84, 0, 0, 1, 0, 92, 0, 0, 0, 125, 171, 211, 198, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 255, 31, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 222, 31, 0, 0, 0, 0, 0, 0, 27, 48, 32, 148, 177, 137, 179, 64, 170, 235, 143, 149, 202, 132, 158, 228, 2, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 128, 0, 0, 0, 51, 150, 150, 146]), B.Octets.zeros(420n)))) == "mbr" : String}

law detect_bad_gpt:
  {P.PartitionScheme.show(P.Partition.detect(B.Octets.append(B.Octets.zeros(440n), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 238, 130, 2, 0, 1, 0, 0, 0, 255, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 170])), B.Octets.append(B.Octets.of_list([69, 70, 73, 32, 80, 65, 82, 84, 0, 0, 1, 0, 92, 0, 0, 0, 125, 171, 211, 198, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 255, 31, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 222, 31, 0, 0, 0, 0, 0, 0, 27, 48, 32, 148, 177, 137, 179, 64, 170, 235, 143, 149, 202, 132, 158, 228, 2, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 128, 0, 0, 0, 51, 150, 150, 146]), B.Octets.zeros(420n)))) == "bad gpt: bad header CRC" : String}

law detect_none:
  {P.PartitionScheme.show(P.Partition.detect(B.Octets.zeros(512n), B.Octets.zeros(512n))) == "none" : String}

# Vectors: malformed input

law mbr_no_signature:
  {M.Mbr.parse(B.Octets.zeros(512n)) == Fail{M.MbrBadSignature{}} : Result<&2, &2, M.MbrError, M.Mbr>}

law mbr_too_short:
  {M.Mbr.parse(B.Octets.zeros(500n)) == Fail{M.MbrTooShort{}} : Result<&2, &2, M.MbrError, M.Mbr>}

law gpt_no_signature:
  {G.Gpt.parse_header(B.Octets.zeros(512n)) == Fail{G.GptBadSignature{}} : Result<&2, &2, G.GptError, G.GptHeader>}

law gpt_too_short:
  {G.Gpt.parse_header(B.Octets.of_string("EFI PART")) == Fail{G.GptTooShort{}} : Result<&2, &2, G.GptError, G.GptHeader>}
