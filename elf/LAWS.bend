# Properties, for every input:
#
# * Each writer and its reader agree, in both classes and both byte orders:
#   reading the bytes written for an ELF header, a program header, a section
#   header, a symbol, a relocation (with or without an addend), a dynamic
#   section entry or a symbol version entry (versym, verdef, verdaux, verneed,
#   vernaux), followed by any bytes at all, gives back the structure as the
#   file stores it (normal: bytes masked to 8 bits, 16-bit fields to 16, in
#   ELF32 the addresses, offsets and sizes to 32, and ELF32 addends
#   sign-extended).
# * The same for whole tables: reading n entries from the bytes of a table of
#   n of them gives back every entry.
# * A note whose sizes are its name's and descriptor's lengths is read back
#   from its bytes, with either alignment; so is a list of them.
# * The header reader rejects anything without the magic number (with
#   ElfBadMagic), anything shorter than 52 bytes (the smallest header), and
#   every header with its last byte cut off (with ElfTruncated).
# * A string table's index answers what the reference lookup answers, for
#   every table and offset, and so do symbol and section names through it.
# * Every named dynamic tag's code is read back as its name; ELF64_R_INFO's
#   symbol and type come back out of r_info.
#
# Vectors: the header of a real x86-64 executable (gcc, -nostdlib -static) and
# of an ELF32 big-endian file written by hand from the gABI; a bad class, data
# encoding and version, and the version accepted when not checked; the section
# count held in section 0 (e_shnum 0); a table that runs past the end of the
# file; strings in a string table, directly and indexed; st_info's binding and
# type; a whole file built with the writers, read back, its sections found by
# name; ELF32_R_INFO and a negative ELF32 addend; DT_NEEDED and the end of the
# dynamic array; packed version definition and need chains, written and read
# back; a hidden version index; a build ID note; an 8-byte-aligned GNU
# property note. Each law with a hypothesis has a witness that the hypothesis
# can hold.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./fields.bend as F
import ./header.bend as H
import ./sections.bend as S
import ./segments.bend as P
import ./symbols.bend as Y
import ./strtab.bend as T
import ./relocs.bend as R
import ./dynamic.bend as D
import ./notes.bend as N
import ./versions.bend as V
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

# Witnesses: each hypothesis above can hold

law rejects_bad_magic_witness:
  {H.ElfHeader.has_magic(B.Octets.of_string("ELF")) == False{} : Bool}

law rejects_short_witness:
  {Nat.is_lt(List.length(&2, U32, [127, 69, 76, 70]), 52n) == True{} : Bool}

# String tables, indexed: the index answers what the reference lookup
# (ElfShdr.string, a walk of the table to the offset) answers, for every table
# and every offset; so do the names looked up through it

law strtab_string:
  for strtab: B.Octets
  for i: U32
  {T.ElfStrtab.string(T.ElfStrtab.of(strtab), i) == S.ElfShdr.string(strtab, i) : Result<&2, &2, F.ElfError, B.Octets>}

law sym_name_indexed:
  for strtab: B.Octets
  for s: Y.ElfSym
  {Y.ElfSym.name_in(T.ElfStrtab.of(strtab), s) == Y.ElfSym.name(strtab, s) : Result<&2, &2, F.ElfError, B.Octets>}

law shdr_name_indexed:
  for names: B.Octets
  for s: S.ElfShdr
  {S.ElfShdr.name_in(T.ElfStrtab.of(names), s) == S.ElfShdr.name(names, s) : Result<&2, &2, F.ElfError, B.Octets>}

# "\0.text\0.data\0": ".data" at 7, "data" at 8 (inside a string), nothing at
# 13 (the end)
law strtab_vector:
  {(T.ElfStrtab.string(T.ElfStrtab.of(B.Octets.of_list([0, 46, 116, 101, 120, 116, 0, 46, 100, 97, 116, 97, 0])), 7), T.ElfStrtab.string(T.ElfStrtab.of(B.Octets.of_list([0, 46, 116, 101, 120, 116, 0, 46, 100, 97, 116, 97, 0])), 8), T.ElfStrtab.string(T.ElfStrtab.of(B.Octets.of_list([0, 46, 116, 101, 120, 116, 0, 46, 100, 97, 116, 97, 0])), 13)) == (Done{B.Octets.of_string(".data")}, Done{B.Octets.of_string("data")}, Fail{F.ElfBadString{}}) : Result<&2, &2, F.ElfError, B.Octets> & Result<&2, &2, F.ElfError, B.Octets> & Result<&2, &2, F.ElfError, B.Octets>}

# Relocations: each entry and each table, with and without addends, in both
# classes and byte orders

law rel_round_trip:
  for is64: Bool
  for big: Bool
  for rela: Bool
  for r: R.ElfReloc
  for rest: B.Octets
  {R.ElfReloc.parse(is64, big, rela, B.Octets.append(R.ElfReloc.write(is64, big, rela, r), rest)) == Done{R.ElfReloc.normal(is64, rela, r)} : Result<&2, &2, F.ElfError, R.ElfReloc>}

law rel_table_round_trip:
  for is64: Bool
  for big: Bool
  for rela: Bool
  for rs: List<&2, R.ElfReloc>
  {R.ElfReloc.read_table(is64, big, rela, List.length(&2, R.ElfReloc, rs), U32.to_nat(R.ElfReloc.size(is64, rela)), R.ElfReloc.write_table(is64, big, rela, rs)) == Done{R.ElfReloc.normal_table(is64, rela, rs)} : Result<&2, &2, F.ElfError, List<&2, R.ElfReloc>>}

# ELF64_R_INFO's symbol and type come back out of r_info, for every symbol
# and type
law rel_info64:
  for sym: U32
  for kind: U32
  {(R.ElfReloc.sym(True{}, R.ElfReloc{W.W64.zero(), R.ElfReloc.info(True{}, sym, kind), W.W64.zero()}), R.ElfReloc.type(True{}, R.ElfReloc{W.W64.zero(), R.ElfReloc.info(True{}, sym, kind), W.W64.zero()})) == (sym, kind) : U32 & U32}

# ELF32_R_INFO(4, R_386_GLOB_DAT = 6) is 0x406 (a gcc -m32 shared object's
# .rel.dyn)
law rel_info32:
  {(R.ElfReloc.info(False{}, 4, 6), R.ElfReloc.sym(False{}, R.ElfReloc{W.W64.zero(), W.W64.from_parts(0, 1030), W.W64.zero()}), R.ElfReloc.type(False{}, R.ElfReloc{W.W64.zero(), W.W64.from_parts(0, 1030), W.W64.zero()})) == (W.W64.from_parts(0, 1030), 4, 6) : W.W64 & U32 & U32}

# an Elf32_Rela, little-endian: r_offset 16, r_info 0x102, r_addend -4,
# sign-extended
law rela32_negative_addend:
  {R.ElfReloc.parse(False{}, False{}, True{}, B.Octets.of_list([16, 0, 0, 0, 2, 1, 0, 0, 252, 255, 255, 255])) == Done{R.ElfReloc{W.W64.from_parts(0, 16), W.W64.from_parts(0, 258), W.W64.from_parts(4294967295, 4294967292)}} : Result<&2, &2, F.ElfError, R.ElfReloc>}

# The dynamic section: each entry and each table

law dyn_round_trip:
  for is64: Bool
  for big: Bool
  for d: D.ElfDyn
  for rest: B.Octets
  {D.ElfDyn.parse(is64, big, B.Octets.append(D.ElfDyn.write(is64, big, d), rest)) == Done{D.ElfDyn.normal(is64, d)} : Result<&2, &2, F.ElfError, D.ElfDyn>}

law dyn_table_round_trip:
  for is64: Bool
  for big: Bool
  for ds: List<&2, D.ElfDyn>
  {D.ElfDyn.read_table(is64, big, List.length(&2, D.ElfDyn, ds), U32.to_nat(D.ElfDyn.size(is64)), D.ElfDyn.write_table(is64, big, ds)) == Done{D.ElfDyn.normal_table(is64, ds)} : Result<&2, &2, F.ElfError, List<&2, D.ElfDyn>>}

# every named tag's code is read back as that name
law dyn_tag_code:
  for k: D.ElfDynTag
  {D.ElfDynTag.of_code(D.ElfDynTag.code(k)) == Some{k} : Maybe<&2, D.ElfDynTag>}

# DT_NEEDED at 1 of "\0libc.so.6\0", then DT_NULL, then padding: two entries
# until the end, the first named and pointing to "libc.so.6"
law dyn_needed:
  {(List.length(&2, D.ElfDyn, D.ElfDyn.until_null([D.ElfDyn{W.W64.one(), W.W64.one()}, D.ElfDyn{W.W64.zero(), W.W64.zero()}, D.ElfDyn{W.W64.zero(), W.W64.zero()}])), D.ElfDyn.tag(D.ElfDyn{W.W64.one(), W.W64.one()}), D.ElfDyn.string(T.ElfStrtab.of(B.Octets.of_list([0, 108, 105, 98, 99, 46, 115, 111, 46, 54, 0])), D.ElfDyn{W.W64.one(), W.W64.one()})) == (2n, Some{D.ElfDtNeeded{}}, Done{B.Octets.of_string("libc.so.6")}) : Nat & Maybe<&2, D.ElfDynTag> & Result<&2, &2, F.ElfError, B.Octets>}

# an unnamed tag (DT_LOPROC, 0x70000000) has no name
law dyn_tag_unnamed:
  {D.ElfDyn.tag(D.ElfDyn{W.W64.from_parts(0, 1879048192), W.W64.zero()}) == None{} : Maybe<&2, D.ElfDynTag>}

# Symbol versions: each entry, in both byte orders, and each table

law versym_round_trip:
  for big: Bool
  for v: V.ElfVersym
  for rest: B.Octets
  {V.ElfVersym.parse(big, B.Octets.append(V.ElfVersym.write(big, v), rest)) == Done{V.ElfVersym.normal(v)} : Result<&2, &2, F.ElfError, V.ElfVersym>}

law versym_table_round_trip:
  for big: Bool
  for vs: List<&2, V.ElfVersym>
  {V.ElfVersym.read_table(big, List.length(&2, V.ElfVersym, vs), U32.to_nat(V.ElfVersym.size()), V.ElfVersym.write_table(big, vs)) == Done{V.ElfVersym.normal_table(vs)} : Result<&2, &2, F.ElfError, List<&2, V.ElfVersym>>}

law verdef_round_trip:
  for big: Bool
  for d: V.ElfVerdef
  for rest: B.Octets
  {V.ElfVerdef.parse(big, B.Octets.append(V.ElfVerdef.write(big, d), rest)) == Done{V.ElfVerdef.normal(d)} : Result<&2, &2, F.ElfError, V.ElfVerdef>}

law verdef_table_round_trip:
  for big: Bool
  for ds: List<&2, V.ElfVerdef>
  {V.ElfVerdef.read_table(big, List.length(&2, V.ElfVerdef, ds), U32.to_nat(V.ElfVerdef.size()), V.ElfVerdef.write_table(big, ds)) == Done{V.ElfVerdef.normal_table(ds)} : Result<&2, &2, F.ElfError, List<&2, V.ElfVerdef>>}

law verdaux_round_trip:
  for big: Bool
  for a: V.ElfVerdaux
  for rest: B.Octets
  {V.ElfVerdaux.parse(big, B.Octets.append(V.ElfVerdaux.write(big, a), rest)) == Done{V.ElfVerdaux.normal(a)} : Result<&2, &2, F.ElfError, V.ElfVerdaux>}

law verdaux_table_round_trip:
  for big: Bool
  for as: List<&2, V.ElfVerdaux>
  {V.ElfVerdaux.read_table(big, List.length(&2, V.ElfVerdaux, as), U32.to_nat(V.ElfVerdaux.size()), V.ElfVerdaux.write_table(big, as)) == Done{V.ElfVerdaux.normal_table(as)} : Result<&2, &2, F.ElfError, List<&2, V.ElfVerdaux>>}

law verneed_round_trip:
  for big: Bool
  for n: V.ElfVerneed
  for rest: B.Octets
  {V.ElfVerneed.parse(big, B.Octets.append(V.ElfVerneed.write(big, n), rest)) == Done{V.ElfVerneed.normal(n)} : Result<&2, &2, F.ElfError, V.ElfVerneed>}

law verneed_table_round_trip:
  for big: Bool
  for ns: List<&2, V.ElfVerneed>
  {V.ElfVerneed.read_table(big, List.length(&2, V.ElfVerneed, ns), U32.to_nat(V.ElfVerneed.size()), V.ElfVerneed.write_table(big, ns)) == Done{V.ElfVerneed.normal_table(ns)} : Result<&2, &2, F.ElfError, List<&2, V.ElfVerneed>>}

law vernaux_round_trip:
  for big: Bool
  for a: V.ElfVernaux
  for rest: B.Octets
  {V.ElfVernaux.parse(big, B.Octets.append(V.ElfVernaux.write(big, a), rest)) == Done{V.ElfVernaux.normal(a)} : Result<&2, &2, F.ElfError, V.ElfVernaux>}

law vernaux_table_round_trip:
  for big: Bool
  for as: List<&2, V.ElfVernaux>
  {V.ElfVernaux.read_table(big, List.length(&2, V.ElfVernaux, as), U32.to_nat(V.ElfVernaux.size()), V.ElfVernaux.write_table(big, as)) == Done{V.ElfVernaux.normal_table(as)} : Result<&2, &2, F.ElfError, List<&2, V.ElfVernaux>>}

# a packed chain of two definitions (the file's own, "libx.so" at 1; VERS_1
# at 9, with VERS_0 at 16 as its parent), written and read back
law verdef_chain:
  {V.ElfVerdef.chain(False{}, 2, V.ElfVerdef.write_chain(False{}, V.ElfVerdef.pack([V.ElfVerdefEntry{V.ElfVerdef{1, 1, 1, 0, 7574943, 0, 0}, [V.ElfVerdaux{1, 0}]}, V.ElfVerdefEntry{V.ElfVerdef{1, 0, 2, 0, 95058209, 0, 0}, [V.ElfVerdaux{9, 0}, V.ElfVerdaux{16, 0}]}]))) == Done{[V.ElfVerdefEntry{V.ElfVerdef{1, 1, 1, 1, 7574943, 20, 28}, [V.ElfVerdaux{1, 0}]}, V.ElfVerdefEntry{V.ElfVerdef{1, 0, 2, 2, 95058209, 20, 0}, [V.ElfVerdaux{9, 8}, V.ElfVerdaux{16, 0}]}]} : Result<&2, &2, F.ElfError, List<&2, V.ElfVerdefEntry>>}

# a packed chain of one needed file ("libc.so.6" at 1) with two versions,
# big-endian, written and read back
law verneed_chain:
  {V.ElfVerneed.chain(True{}, 1, V.ElfVerneed.write_chain(True{}, V.ElfVerneed.pack([V.ElfVerneedEntry{V.ElfVerneed{1, 0, 1, 0, 0}, [V.ElfVernaux{157882997, 0, 3, 11, 0}, V.ElfVernaux{110530996, 0, 2, 23, 0}]}]))) == Done{[V.ElfVerneedEntry{V.ElfVerneed{1, 2, 1, 16, 0}, [V.ElfVernaux{157882997, 0, 3, 11, 16}, V.ElfVernaux{110530996, 0, 2, 23, 0}]}]} : Result<&2, &2, F.ElfError, List<&2, V.ElfVerneedEntry>>}

# a hidden symbol of version 2 (0x8002)
law versym_hidden:
  {(V.ElfVersym.index(V.ElfVersym{32770}), V.ElfVersym.hidden(V.ElfVersym{32770})) == (2, True{}) : U32 & Bool}

# Notes: a note whose sizes are its name's and descriptor's lengths is read
# back from its bytes, followed by any bytes, with either alignment and byte
# order; so is a list of such notes, one after another

law note_round_trip:
  for big: Bool
  for al: N.ElfNoteAlign
  for namesz: U32
  for descsz: U32
  for t: U32
  for name: B.Octets
  for desc: B.Octets
  for rest: B.Octets
  for e1: {B.Octets.len(name) == U32.to_nat(namesz) : Nat}
  for e2: {B.Octets.len(desc) == U32.to_nat(descsz) : Nat}
  {N.ElfNote.parse(big, al, B.Octets.append(N.ElfNote.write(big, al, N.ElfNote{namesz, descsz, t, name, desc}), rest)) == Done{N.ElfNote{namesz, descsz, t, name, desc}} : Result<&2, &2, F.ElfError, N.ElfNote>}

law note_round_trip_witness:
  {(B.Octets.len(B.Octets.of_string("GNU")), B.Octets.len(B.Octets.of_list([1, 2]))) == (U32.to_nat(3), U32.to_nat(2)) : Nat & Nat}

law notes_round_trip:
  for big: Bool
  for al: N.ElfNoteAlign
  for ns: List<&2, N.ElfNote>
  for e: {N.ElfNote.all_sized(ns) == True{} : Bool}
  {N.ElfNote.read_all(big, al, N.ElfNote.write_all(big, al, ns)) == Done{ns} : Result<&2, &2, F.ElfError, List<&2, N.ElfNote>>}

law notes_round_trip_witness:
  {N.ElfNote.all_sized([N.ElfNote.make(3, B.Octets.of_string("GNU"), B.Octets.of_list([222, 173, 190, 239])), N.ElfNote.make(1, B.Octets.empty(), B.Octets.empty())]) == True{} : Bool}

# a GNU build ID note, made, written with 4-byte alignment, read back: its
# descriptor is the build ID
law note_build_id:
  {Result.map(&2, &2, F.ElfError, List<&2, N.ElfNote>, Maybe<&2, B.Octets>, ns => N.ElfNote.find_build_id(ns), N.ElfNote.read_all(False{}, N.ElfAlign4{}, N.ElfNote.write_all(False{}, N.ElfAlign4{}, [N.ElfNote.make(1, B.Octets.of_string("GNU"), B.Octets.of_list([0, 0, 0, 0])), N.ElfNote.make(3, B.Octets.of_string("GNU"), B.Octets.of_list([222, 173, 190, 239]))]))) == Done{Some{B.Octets.of_list([222, 173, 190, 239])}} : Result<&2, &2, F.ElfError, Maybe<&2, B.Octets>>}

# a GNU property note (NT_GNU_PROPERTY_TYPE_0 = 5) of a gcc x86-64
# executable, aligned to 8: the descriptor starts at 16, not 12 + 4
law note_align8:
  {N.ElfNote.read_all(False{}, N.ElfNoteAlign.of(W.W64.from_parts(0, 8)), B.Octets.of_list([4, 0, 0, 0, 16, 0, 0, 0, 5, 0, 0, 0, 71, 78, 85, 0, 2, 0, 0, 192, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0])) == Done{[N.ElfNote{4, 16, 5, B.Octets.of_list([71, 78, 85, 0]), B.Octets.of_list([2, 0, 0, 192, 4, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0])}]} : Result<&2, &2, F.ElfError, List<&2, N.ElfNote>>}
