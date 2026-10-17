# DRAFT: not yet reviewed by the maintainer
#
# Properties, for every input:
#
# * Each writer and its reader agree, in both classes and both byte orders:
#   reading the bytes written for an ELF header, a program header, a section
#   header or a symbol, followed by any bytes at all, gives back the structure
#   as the file stores it (normal: bytes masked to 8 bits, 16-bit fields to 16,
#   and in ELF32 the addresses, offsets and sizes to 32).
# * The same for whole tables: reading n entries from the bytes of a table of
#   n program headers, section headers or symbols gives back every entry.
# * The header reader rejects anything without the magic number (with
#   ElfBadMagic), anything shorter than 52 bytes (the smallest header), and
#   every header with its last byte cut off (with ElfTruncated).
#
# Vectors: the header of a real x86-64 executable (gcc, -nostdlib -static) and
# of an ELF32 big-endian file written by hand from the gABI; a bad class, data
# encoding and version, and the version accepted when not checked; the section
# count held in section 0 (e_shnum 0); a table that runs past the end of the
# file; strings in a string table; st_info's binding and type; and a whole
# file built with the writers, read back, its sections found by name.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./fields.bend as F
import ./header.bend as H
import ./sections.bend as S
import ./segments.bend as P
import ./symbols.bend as Y
import ./elf.bend as E

# Round trips

law header_round_trip:
  for h: H.ElfHeader
  for rest: B.Octets
  {H.ElfHeader.parse(B.Octets.append(H.ElfHeader.write(h), rest)) == Done{H.ElfHeader.normal(h)} : Result<&2, &2, F.ElfError, H.ElfHeader>}

law phdr_round_trip:
  for is64: Bool
  for big: Bool
  for p: P.ElfPhdr
  for rest: B.Octets
  {P.ElfPhdr.parse(is64, big, B.Octets.append(P.ElfPhdr.write(is64, big, p), rest)) == Done{P.ElfPhdr.normal(is64, p)} : Result<&2, &2, F.ElfError, P.ElfPhdr>}

law shdr_round_trip:
  for is64: Bool
  for big: Bool
  for s: S.ElfShdr
  for rest: B.Octets
  {S.ElfShdr.parse(is64, big, B.Octets.append(S.ElfShdr.write(is64, big, s), rest)) == Done{S.ElfShdr.normal(is64, s)} : Result<&2, &2, F.ElfError, S.ElfShdr>}

law sym_round_trip:
  for is64: Bool
  for big: Bool
  for s: Y.ElfSym
  for rest: B.Octets
  {Y.ElfSym.parse(is64, big, B.Octets.append(Y.ElfSym.write(is64, big, s), rest)) == Done{Y.ElfSym.normal(is64, s)} : Result<&2, &2, F.ElfError, Y.ElfSym>}

# Tables, with entries packed (the step is the entry's size)

law phdr_table_round_trip:
  for is64: Bool
  for big: Bool
  for ps: List<&2, P.ElfPhdr>
  {P.ElfPhdr.read_table(is64, big, List.length(&2, P.ElfPhdr, ps), U32.to_nat(P.ElfPhdr.size(is64)), P.ElfPhdr.write_table(is64, big, ps)) == Done{P.ElfPhdr.normal_table(is64, ps)} : Result<&2, &2, F.ElfError, List<&2, P.ElfPhdr>>}

law shdr_table_round_trip:
  for is64: Bool
  for big: Bool
  for ss: List<&2, S.ElfShdr>
  {S.ElfShdr.read_table(is64, big, List.length(&2, S.ElfShdr, ss), U32.to_nat(S.ElfShdr.size(is64)), S.ElfShdr.write_table(is64, big, ss)) == Done{S.ElfShdr.normal_table(is64, ss)} : Result<&2, &2, F.ElfError, List<&2, S.ElfShdr>>}

law sym_table_round_trip:
  for is64: Bool
  for big: Bool
  for ss: List<&2, Y.ElfSym>
  {Y.ElfSym.read_table(is64, big, List.length(&2, Y.ElfSym, ss), U32.to_nat(Y.ElfSym.size(is64)), Y.ElfSym.write_table(is64, big, ss)) == Done{Y.ElfSym.normal_table(is64, ss)} : Result<&2, &2, F.ElfError, List<&2, Y.ElfSym>>}

# Rejection

law rejects_bad_magic:
  for o: B.Octets
  for e: {H.ElfHeader.has_magic(o) == False{} : Bool}
  {H.ElfHeader.parse(o) == Fail{F.ElfBadMagic{}} : Result<&2, &2, F.ElfError, H.ElfHeader>}

law rejects_short:
  for xs: List<&2, U32>
  for e: {Nat.is_lt(List.length(&2, U32, xs), 52n) == True{} : Bool}
  {Result.is_fail(&2, &2, F.ElfError, H.ElfHeader, H.ElfHeader.parse(B.Octets.of_list(xs))) == True{} : Bool}

law header_truncated:
  for h: H.ElfHeader
  {H.ElfHeader.parse(B.Octets.take(Nat.sub(U32.to_nat(H.ElfHeader.size(H.ElfHeader.is64(h))), 1n), H.ElfHeader.write(h))) == Fail{F.ElfTruncated{}} : Result<&2, &2, F.ElfError, H.ElfHeader>}

# Vectors

# the first 64 bytes of a gcc -nostdlib -static executable for x86-64:
# ET_EXEC, EM_X86_64, entry 0x401000, 6 program headers at 64, 9 sections at
# 8560, names in section 8
law vector_x86_64:
  {H.ElfHeader.parse(B.Octets.of_list([127, 69, 76, 70, 2, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 62, 0, 1, 0, 0, 0, 0, 16, 64, 0, 0, 0, 0, 0, 64, 0, 0, 0, 0, 0, 0, 0, 112, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 64, 0, 56, 0, 6, 0, 64, 0, 9, 0, 8, 0])) == Done{H.ElfHeader{True{}, False{}, 0, 0, 2, 62, 1, W.W64.from_parts(0, 4198400), W.W64.from_parts(0, 64), W.W64.from_parts(0, 8560), 0, 64, 56, 6, 64, 9, 8}} : Result<&2, &2, F.ElfError, H.ElfHeader>}

# an ELF32 big-endian header for PowerPC (EM_PPC = 20): ET_EXEC, entry
# 0x10000074, one program header at 52, no sections
law vector_ppc32_big_endian:
  {H.ElfHeader.parse(B.Octets.of_list([127, 69, 76, 70, 1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 20, 0, 0, 0, 1, 16, 0, 0, 116, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 0, 32, 0, 1, 0, 40, 0, 0, 0, 0])) == Done{H.ElfHeader{False{}, True{}, 0, 0, 2, 20, 1, W.W64.from_parts(0, 268435572), W.W64.from_parts(0, 52), W.W64.zero(), 0, 52, 32, 1, 40, 0, 0}} : Result<&2, &2, F.ElfError, H.ElfHeader>}

# the same header with EI_CLASS 3, EI_DATA 0, EI_VERSION 2: none is in the gABI
law rejects_bad_class:
  {H.ElfHeader.parse(B.Octets.of_list([127, 69, 76, 70, 3, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 20, 0, 0, 0, 1, 16, 0, 0, 116, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 0, 32, 0, 1, 0, 40, 0, 0, 0, 0])) == Fail{F.ElfBadClass{}} : Result<&2, &2, F.ElfError, H.ElfHeader>}

law rejects_bad_data:
  {H.ElfHeader.parse(B.Octets.of_list([127, 69, 76, 70, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 20, 0, 0, 0, 1, 16, 0, 0, 116, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 0, 32, 0, 1, 0, 40, 0, 0, 0, 0])) == Fail{F.ElfBadData{}} : Result<&2, &2, F.ElfError, H.ElfHeader>}

law rejects_bad_version:
  {H.ElfHeader.parse(B.Octets.of_list([127, 69, 76, 70, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 20, 0, 0, 0, 1, 16, 0, 0, 116, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 0, 32, 0, 1, 0, 40, 0, 0, 0, 0])) == Fail{F.ElfBadVersion{}} : Result<&2, &2, F.ElfError, H.ElfHeader>}

# unless the version is not checked
law version_unchecked:
  {H.ElfHeader.parse_with(H.ElfOptions{False{}}, B.Octets.of_list([127, 69, 76, 70, 1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 20, 0, 0, 0, 1, 16, 0, 0, 116, 0, 0, 0, 52, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 0, 32, 0, 1, 0, 40, 0, 0, 0, 0])) == Done{H.ElfHeader{False{}, True{}, 0, 0, 2, 20, 1, W.W64.from_parts(0, 268435572), W.W64.from_parts(0, 52), W.W64.zero(), 0, 52, 32, 1, 40, 0, 0}} : Result<&2, &2, F.ElfError, H.ElfHeader>}

# an ELF64 header with e_shnum 0 and section headers at 64: the count, 300,
# is section 0's sh_size
law extended_shnum:
  {S.ElfShdr.count(B.Octets.append(H.ElfHeader.write(H.ElfHeader{True{}, False{}, 0, 0, 1, 62, 1, W.W64.zero(), W.W64.zero(), W.W64.from_parts(0, 64), 0, 64, 0, 0, 64, 0, 0}), S.ElfShdr.write(True{}, False{}, S.ElfShdr{0, 0, W.W64.zero(), W.W64.zero(), W.W64.zero(), W.W64.from_parts(0, 300), 0, 0, W.W64.zero(), W.W64.zero()})), H.ElfHeader{True{}, False{}, 0, 0, 1, 62, 1, W.W64.zero(), W.W64.zero(), W.W64.from_parts(0, 64), 0, 64, 0, 0, 64, 0, 0}) == Done{300} : Result<&2, &2, F.ElfError, U32>}

# one program header at offset 64 of a 64-byte file runs past its end
law phdrs_past_end:
  {P.ElfPhdr.all(H.ElfHeader.write(H.ElfHeader{True{}, False{}, 0, 0, 2, 62, 1, W.W64.zero(), W.W64.from_parts(0, 64), W.W64.zero(), 0, 64, 56, 1, 64, 0, 0}), H.ElfHeader{True{}, False{}, 0, 0, 2, 62, 1, W.W64.zero(), W.W64.from_parts(0, 64), W.W64.zero(), 0, 64, 56, 1, 64, 0, 0}) == Fail{F.ElfTruncated{}} : Result<&2, &2, F.ElfError, List<&2, P.ElfPhdr>>}

# "\0.text\0.data\0": the names at 1 and 7, the empty name at 0; none past
# the end, nor where the NUL is missing
law string_text:
  {S.ElfShdr.string(B.Octets.of_list([0, 46, 116, 101, 120, 116, 0, 46, 100, 97, 116, 97, 0]), 1) == Done{B.Octets.of_string(".text")} : Result<&2, &2, F.ElfError, B.Octets>}

law string_data:
  {S.ElfShdr.string(B.Octets.of_list([0, 46, 116, 101, 120, 116, 0, 46, 100, 97, 116, 97, 0]), 7) == Done{B.Octets.of_string(".data")} : Result<&2, &2, F.ElfError, B.Octets>}

law string_empty:
  {S.ElfShdr.string(B.Octets.of_list([0, 46, 116, 101, 120, 116, 0]), 0) == Done{B.Octets.empty()} : Result<&2, &2, F.ElfError, B.Octets>}

law string_past_end:
  {S.ElfShdr.string(B.Octets.of_list([0, 46, 116, 101, 120, 116, 0]), 8) == Fail{F.ElfBadString{}} : Result<&2, &2, F.ElfError, B.Octets>}

law string_unterminated:
  {S.ElfShdr.string(B.Octets.of_list([0, 46, 116, 101, 120, 116]), 1) == Fail{F.ElfBadString{}} : Result<&2, &2, F.ElfError, B.Octets>}

# STB_GLOBAL (1) and STT_FUNC (2) make st_info 0x12; st_info 0x22 is
# STB_WEAK, STT_FUNC, and st_other 2 is STV_HIDDEN
law sym_info:
  {Y.ElfSym.info(1, 2) == 18 : U32}

law sym_bind_type:
  {(Y.ElfSym.bind(Y.ElfSym{0, W.W64.zero(), W.W64.zero(), 34, 2, 0}), Y.ElfSym.type(Y.ElfSym{0, W.W64.zero(), W.W64.zero(), 34, 2, 0}), Y.ElfSym.visibility(Y.ElfSym{0, W.W64.zero(), W.W64.zero(), 34, 2, 0})) == (2, 2, 2) : U32 & U32 & U32}

# A whole ELF32 big-endian file built with the writers: the header, then the
# section-name string table "\0.shstrtab\0.text\0" (17 bytes at 52), then
# three section headers at 72 (SHT_NULL; .shstrtab, SHT_STRTAB; .text,
# SHT_PROGBITS, 4 bytes at 52). Read back, ".text" is section 2.
law whole_file:
  {Maybe.map(&2, S.ElfShdr, U32, S.ElfShdr.sh_type, Result.default(&2, &2, F.ElfError, Maybe<&2, S.ElfShdr>, Result.map(&2, &2, F.ElfError, E.ElfFile, Maybe<&2, S.ElfShdr>, f => E.ElfFile.find_section(f, B.Octets.of_string(".text")), E.ElfFile.read(B.Octets.concat([H.ElfHeader.write(H.ElfHeader{False{}, True{}, 0, 0, 1, 20, 1, W.W64.zero(), W.W64.zero(), W.W64.from_parts(0, 72), 0, 52, 0, 0, 40, 3, 1}), B.Octets.of_list([0, 46, 115, 104, 115, 116, 114, 116, 97, 98, 0, 46, 116, 101, 120, 116, 0, 0, 0, 0]), S.ElfShdr.write_table(False{}, True{}, [S.ElfShdr{0, 0, W.W64.zero(), W.W64.zero(), W.W64.zero(), W.W64.zero(), 0, 0, W.W64.zero(), W.W64.zero()}, S.ElfShdr{1, 3, W.W64.zero(), W.W64.zero(), W.W64.from_parts(0, 52), W.W64.from_parts(0, 17), 0, 0, W.W64.one(), W.W64.zero()}, S.ElfShdr{11, 1, W.W64.from_parts(0, 6), W.W64.zero(), W.W64.from_parts(0, 52), W.W64.from_parts(0, 4), 0, 0, W.W64.one(), W.W64.zero()}])]))), None{})) == Some{1} : Maybe<&2, U32>}
