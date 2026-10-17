#!/usr/bin/env python3
"""Writes partition/LAWS.bend from the sectors in sectors.txt (dumped from
images made by sgdisk and sfdisk; see LAWS.bend). Run from anywhere:
python3 partition/gen/genlaws.py, then genproof.py."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
PKG = os.path.dirname(HERE)
import uuid
v = {}
for line in open(os.path.join(HERE, "sectors.txt"), encoding="utf-8"):
    k, rest = line.split(" ", 1); v[k] = rest.strip()
def make(s):
    return "U.Uuid.make(" + ", ".join(str(b) for b in uuid.UUID(s).bytes) + ")"
HDR = "B.Octets.append(B.Octets.of_list(%s), B.Octets.zeros(420n))" % v["HDR"]
hb = eval(v["HDR"]); hb[100 - 100 + 30] ^= 1  # flip a bit of the alternate LBA
BAD = "B.Octets.append(B.Octets.of_list(%s), B.Octets.zeros(420n))" % str(hb)
E0 = "B.Octets.of_list(%s)" % v["E0"]
PMBR = "B.Octets.append(B.Octets.zeros(440n), B.Octets.of_list(%s))" % v["PMBR"]
MBR = "B.Octets.append(B.Octets.zeros(440n), B.Octets.of_list(%s))" % v["MBR"]
RH = "Result<&2, &2, G.GptError, G.GptHeader>"
RE = "Result<&2, &2, G.GptError, G.GptEntry>"
RM = "Result<&2, &2, M.MbrError, M.Mbr>"
W = lambda n: "W.W64.from_u32(%d)" % n
DISK = make("9420301B-89B1-40B3-AAEB-8F95CA849EE4")
HDRV = "G.GptHeader{65536, 92, 3335760765, %s, %s, %s, %s, %s, %s, 128, 128, 2459342387}" % (W(1), W(8191), W(34), W(8158), DISK, W(2))
ENT0 = "G.GptEntry.norm(G.GptEntry{%s, %s, %s, %s, W.W64.zero(), G.Gpt.name_units(\"EFI system\")})" % (make("C12A7328-F81F-11D2-BA4B-00A0C93EC93B"), make("EFF88856-2F4C-4273-AEC8-27C144E7A596"), W(2048), W(4095))
ENTRY = lambda n: "M.MbrEntry{%d, M.MbrChs{%d, %d, %d}, %d, M.MbrChs{%d, %d, %d}, %d, %d}" % n
EMPTY = "M.MbrEntry.empty()"
MBRV = "M.Mbr{305419896, %s, %s, %s, %s}" % (ENTRY((128, 32, 33, 0, 131, 48, 48, 0, 2048, 1024)), ENTRY((0, 48, 49, 0, 12, 65, 1, 0, 3072, 1024)), EMPTY, EMPTY)
out = '''# DRAFT: not yet reviewed by the maintainer
#
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
  {M.Mbr.parse(M.Mbr.build(boot, m)) == Done{M.Mbr.norm(m)} : %(RM)s}

law gpt_header_crc:
  for +h: G.GptHeader
  {G.Gpt.header_crc_ok(G.Gpt.build_header(h)) == True{} : Bool}

law gpt_header_round_trip:
  for +h: G.GptHeader
  {G.Gpt.parse_header(G.Gpt.build_header(h)) == Done{G.GptHeader.seal(h)} : %(RH)s}

law gpt_entry_round_trip:
  for +e: G.GptEntry
  {G.GptEntry.decode(G.GptEntry.encode(e)) == Done{G.GptEntry.norm(e)} : %(RE)s}

law gpt_build_entries_crc:
  for +h: G.GptHeader
  for +es: List<&2, G.GptEntry>
  {Result.map(&2, &2, G.GptError, G.GptHeader, U32, G.GptHeader.entries_crc, G.Gpt.parse_header(G.Gpt.build(h, es))) == Done{C.crc32(G.Gpt.entries_encode(es))} : Result<&2, &2, G.GptError, U32>}

# Vectors: the GPT header sgdisk wrote (header CRC 0xC6D3AB7D, entries CRC
# 0x92969633)

law sgdisk_header:
  {G.Gpt.validate_header(%(HDR)s) == Done{%(HDRV)s} : %(RH)s}

law sgdisk_header_crc:
  {G.Gpt.header_crc(%(HDR)s) == 3335760765 : U32}

law sgdisk_header_rebuilt:
  {G.Gpt.build_header(%(HDRV)s) == %(HDR)s : B.Octets}

law sgdisk_header_corrupt:
  {G.Gpt.validate_header(%(BAD)s) == Fail{G.GptBadHeaderCrc{}} : %(RH)s}

law sgdisk_standard_layout:
  {G.GptHeader.standard(G.GptLayout.standard(), W.W64.from_u32(8192), %(DISK)s) == G.GptHeader{65536, 92, 0, %(W1)s, %(W8191)s, %(W34)s, %(W8158)s, %(DISK)s, %(W2)s, 128, 128, 0} : G.GptHeader}

# Vectors: its first entry, the EFI System Partition

law sgdisk_entry:
  {G.GptEntry.decode(%(E0)s) == Done{%(ENT0)s} : %(RE)s}

law sgdisk_entry_rebuilt:
  {G.GptEntry.encode(%(ENT0)s) == %(E0)s : B.Octets}

law sgdisk_entry_name:
  {Result.map(&2, &2, G.GptError, G.GptEntry, String, G.GptEntry.name_text, G.GptEntry.decode(%(E0)s)) == Done{"EFI system"} : Result<&2, &2, G.GptError, String>}

# Vectors: UTF-16 names (U+1F600 is the surrogate pair 0xD83D 0xDE00)

law name_surrogates:
  {G.Gpt.name_units(SCon{'a', SCon{Chr{128512}, SNil{}}}) == [97, 55357, 56832] : List<&2, U32>}

law name_text_surrogates:
  {G.GptEntry.name_text(G.GptEntry{U.Uuid.nil(), U.Uuid.nil(), W.W64.zero(), W.W64.zero(), W.W64.zero(), [97, 55357, 56832, 0, 98]}) == SCon{'a', SCon{Chr{128512}, SNil{}}} : String}

# Vectors: the protective MBR sgdisk wrote, and the MBR sfdisk wrote

law sgdisk_protective_mbr:
  {M.Mbr.build(B.Octets.empty(), M.Mbr.protective(W.W64.from_u32(8191))) == %(PMBR)s : B.Octets}

law sfdisk_mbr:
  {M.Mbr.parse(%(MBR)s) == Done{%(MBRV)s} : %(RM)s}

law sfdisk_mbr_rebuilt:
  {M.Mbr.build(B.Octets.zeros(440n), %(MBRV)s) == %(MBR)s : B.Octets}

law chs_of_lba:
  {M.MbrChs.of_lba(M.MbrGeometry.standard(), 4095) == M.MbrChs{65, 1, 0} : M.MbrChs}

law chs_of_lba_too_far:
  {M.MbrChs.of_lba(M.MbrGeometry.standard(), 16450560) == M.MbrChs{255, 63, 1023} : M.MbrChs}

# Vectors: telling the schemes apart

law detect_gpt:
  {P.PartitionScheme.show(P.Partition.detect(%(PMBR)s, %(HDR)s)) == "gpt" : String}

law detect_mbr:
  {P.PartitionScheme.show(P.Partition.detect(%(MBR)s, %(HDR)s)) == "mbr" : String}

law detect_bad_gpt:
  {P.PartitionScheme.show(P.Partition.detect(%(PMBR)s, %(BAD)s)) == "bad gpt: bad header CRC" : String}

law detect_none:
  {P.PartitionScheme.show(P.Partition.detect(B.Octets.zeros(512n), B.Octets.zeros(512n))) == "none" : String}

# Vectors: malformed input

law mbr_no_signature:
  {M.Mbr.parse(B.Octets.zeros(512n)) == Fail{M.MbrBadSignature{}} : %(RM)s}

law mbr_too_short:
  {M.Mbr.parse(B.Octets.zeros(500n)) == Fail{M.MbrTooShort{}} : %(RM)s}

law gpt_no_signature:
  {G.Gpt.parse_header(B.Octets.zeros(512n)) == Fail{G.GptBadSignature{}} : %(RH)s}

law gpt_too_short:
  {G.Gpt.parse_header(B.Octets.of_string("EFI PART")) == Fail{G.GptTooShort{}} : %(RH)s}
''' % dict(RM=RM, RH=RH, RE=RE, HDR=HDR, HDRV=HDRV, BAD=BAD, DISK=DISK, E0=E0, ENT0=ENT0, PMBR=PMBR, MBR=MBR, MBRV=MBRV, W1=W(1), W8191=W(8191), W34=W(34), W8158=W(8158), W2=W(2))
open(os.path.join(PKG, "LAWS.bend"), "w", encoding="utf-8", newline="\n").write(out)
