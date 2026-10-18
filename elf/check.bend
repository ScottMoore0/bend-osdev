import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./fields.bend as F
import ./header.bend as H
import ./sections.bend as S
import ./segments.bend as P
import ./symbols.bend as Y
import ./elf.bend as E
import ./relocs.bend as R
import ./dynamic.bend as DY
import ./notes.bend as N
import ./versions.bend as V
import ./ref/dump.bend as D

def w(v: U32) -> W.W64:
  W.W64.from_parts(0, v)

# A small file built with the writers, in either class and byte order: the
# header; at hs the section names "\0.shstrtab\0.symtab\0.strtab\0" (27
# bytes, padded to 32); at hs + 32 the symbol names "\0main\0data\0" (11,
# padded to 16); at hs + 48 three symbols; then four section headers.
def build(+is64: Bool, +big: Bool) -> B.Octets:
  +hs = H.ElfHeader.size(is64)
  +ys = Y.ElfSym.size(is64)
  +symtab = U32.add(hs, 48)
  +shoff = U32.add(symtab, U32.mul(3, ys))
  h = {H.ElfHeader{is64, big, 0, 0, 1, 62, 1, W.W64.zero(), W.W64.zero(), w(shoff), 0, hs, 0, 0, S.ElfShdr.size(is64), 4, 1} : H.ElfHeader}
  names = B.Octets.of_list([0, 46, 115, 104, 115, 116, 114, 116, 97, 98, 0, 46, 115, 121, 109, 116, 97, 98, 0, 46, 115, 116, 114, 116, 97, 98, 0])
  strs = B.Octets.of_list([0, 109, 97, 105, 110, 0, 100, 97, 116, 97, 0])
  syms = Y.ElfSym.write_table(is64, big, {[Y.ElfSym{0, W.W64.zero(), W.W64.zero(), 0, 0, 0}, Y.ElfSym{1, w(4198400), w(12), Y.ElfSym.info(1, 2), 0, 65521}, Y.ElfSym{6, w(4202496), w(4), Y.ElfSym.info(2, 1), 2, 65521}] : List<&2, Y.ElfSym>})
  shdrs = S.ElfShdr.write_table(is64, big, {[S.ElfShdr{0, 0, W.W64.zero(), W.W64.zero(), W.W64.zero(), W.W64.zero(), 0, 0, W.W64.zero(), W.W64.zero()}, S.ElfShdr{1, 3, W.W64.zero(), W.W64.zero(), w(hs), w(27), 0, 0, W.W64.one(), W.W64.zero()}, S.ElfShdr{11, 2, W.W64.zero(), W.W64.zero(), w(symtab), w(U32.mul(3, ys)), 3, 1, w(8), w(ys)}, S.ElfShdr{19, 3, W.W64.zero(), W.W64.zero(), w(U32.add(hs, 32)), w(11), 0, 0, W.W64.one(), W.W64.zero()}] : List<&2, S.ElfShdr>})
  B.Octets.concat({[H.ElfHeader.write(h), names, B.Octets.zeros(5n), strs, B.Octets.zeros(5n), syms, shdrs] : List<&2, B.Octets>})

# A larger file, as a regression test for long inputs: the same layout, little-
# endian ELF64, with n + 1 symbols (the null one, then n named "main" with
# values n down to 1), a symbol table of 24 * (n + 1) bytes
def big.syms(n: Nat, +i: U32, acc: List<&2, Y.ElfSym>) -> List<&2, Y.ElfSym>:
  match n:
    case 0n:
      acc
    case 1n+p:
      big.syms(p, U32.add(i, 1), Con{Y.ElfSym{1, w(i), w(4), Y.ElfSym.info(1, 2), 0, 65521}, acc})

def build_big(+n: U32) -> B.Octets:
  +symtab = {112 : U32}
  +size = U32.mul(U32.add(n, 1), 24)
  +shoff = U32.add(symtab, size)
  h = {H.ElfHeader{True{}, False{}, 0, 0, 1, 62, 1, W.W64.zero(), W.W64.zero(), w(shoff), 0, 64, 0, 0, 64, 4, 1} : H.ElfHeader}
  names = B.Octets.of_list([0, 46, 115, 104, 115, 116, 114, 116, 97, 98, 0, 46, 115, 121, 109, 116, 97, 98, 0, 46, 115, 116, 114, 116, 97, 98, 0])
  strs = B.Octets.of_list([0, 109, 97, 105, 110, 0, 100, 97, 116, 97, 0])
  syms = Y.ElfSym.write_table(True{}, False{}, Con{Y.ElfSym{0, W.W64.zero(), W.W64.zero(), 0, 0, 0}, big.syms(U32.to_nat(n), 1, Nil{})})
  shdrs = S.ElfShdr.write_table(True{}, False{}, {[S.ElfShdr{0, 0, W.W64.zero(), W.W64.zero(), W.W64.zero(), W.W64.zero(), 0, 0, W.W64.zero(), W.W64.zero()}, S.ElfShdr{1, 3, W.W64.zero(), W.W64.zero(), w(64), w(27), 0, 0, W.W64.one(), W.W64.zero()}, S.ElfShdr{11, 2, W.W64.zero(), W.W64.zero(), w(symtab), w(size), 3, 1, w(8), w(24)}, S.ElfShdr{19, 3, W.W64.zero(), W.W64.zero(), w(96), w(11), 0, 0, W.W64.one(), W.W64.zero()}] : List<&2, S.ElfShdr>})
  B.Octets.concat({[H.ElfHeader.write(h), names, B.Octets.zeros(5n), strs, B.Octets.zeros(5n), syms, shdrs] : List<&2, B.Octets>})

# the number of symbols, the sum of their values, and the last one's name
def big.tally(ys: List<&2, Y.ElfSym>, +strtab: B.Octets, n: Nat, sum: U32, last: String) -> String:
  match ys:
    case Nil{}:
      Nat.show(n) ++ " symbols, values sum " ++ U32.show(sum) ++ ", last " ++ last
    case Con{+y, t}:
      big.tally(t, strtab, 1n+n, U32.add(sum, W.W64.lo(Y.ElfSym.st_value(y))), D.show_name(Y.ElfSym.name(strtab, y)))

def big.show_syms(r: Result<&2, &2, F.ElfError, List<&2, Y.ElfSym>>, t: Result<&2, &2, F.ElfError, B.Octets>) -> String:
  match r t:
    case Done{ys} Done{strtab}:
      big.tally(ys, strtab, 0n, 0, "none")
    case _ _:
      "error"

def big.show_tab(+o: B.Octets, +f: E.ElfFile, m: Maybe<&2, S.ElfShdr>) -> String:
  match m:
    case Some{+s}:
      big.show_syms(E.ElfFile.symbols(o, f, s), E.ElfFile.strtab(o, f, s))
    case None{}:
      "no .symtab"

def big.show(r: Result<&2, &2, F.ElfError, E.ElfFile>, +o: B.Octets) -> String:
  match r:
    case Done{+f}:
      big.show_tab(o, f, E.ElfFile.find_section(f, B.Octets.of_string(".symtab")))
    case Fail{e}:
      "error " ++ D.err(e)

def show_found(m: Maybe<&2, S.ElfShdr>) -> String:
  match m:
    case Some{s}:
      "found, sh_type " ++ U32.show(S.ElfShdr.sh_type(s))
    case None{}:
      "not found"

def show_file(r: Result<&2, &2, F.ElfError, E.ElfFile>) -> String:
  match r:
    case Done{+f}:
      ".symtab " ++ show_found(E.ElfFile.find_section(f, B.Octets.of_string(".symtab"))) ++ "; .text " ++ show_found(E.ElfFile.find_section(f, B.Octets.of_string(".text")))
    case Fail{e}:
      "error " ++ D.err(e)

# A file with the later concerns' sections, built with their writers, in
# either class and byte order: after the header, each padded to 8 bytes, the
# section names, the dynamic strings "\0libc.so.6\0VERS_1\0libx.so\0
# GLIBC_2.2.5\0", relocations with addends, a dynamic section, a build ID
# note, .gnu.version, .gnu.version_d and .gnu.version_r; then the section
# headers.
def ext.len(o: B.Octets) -> U32:
  U32.from_nat(B.Octets.len(o))

def ext.pad8(+o: B.Octets) -> B.Octets:
  B.Octets.append(o, B.Octets.zeros(U32.to_nat(U32.and(7, U32.sub(0, ext.len(o))))))

def ext.sh(name: U32, kind: U32, +off: U32, o: B.Octets, link: U32, info: U32, align: U32, entsize: U32) -> S.ElfShdr:
  S.ElfShdr{name, kind, w(2), W.W64.zero(), w(off), w(ext.len(o)), link, info, w(align), w(entsize)}

def build_ext(+is64: Bool, +big: Bool) -> B.Octets:
  +names = B.Octets.of_list([0, 46, 115, 104, 115, 116, 114, 116, 97, 98, 0, 46, 100, 121, 110, 115, 116, 114, 0, 46, 114, 101, 108, 97, 46, 116, 101, 120, 116, 0, 46, 100, 121, 110, 97, 109, 105, 99, 0, 46, 110, 111, 116, 101, 46, 103, 110, 117, 46, 98, 117, 105, 108, 100, 45, 105, 100, 0, 46, 103, 110, 117, 46, 118, 101, 114, 115, 105, 111, 110, 0, 46, 103, 110, 117, 46, 118, 101, 114, 115, 105, 111, 110, 95, 100, 0, 46, 103, 110, 117, 46, 118, 101, 114, 115, 105, 111, 110, 95, 114, 0])
  +dynstr = B.Octets.of_list([0, 108, 105, 98, 99, 46, 115, 111, 46, 54, 0, 86, 69, 82, 83, 95, 49, 0, 108, 105, 98, 120, 46, 115, 111, 0, 71, 76, 73, 66, 67, 95, 50, 46, 50, 46, 53, 0])
  +rela = R.ElfReloc.write_table(is64, big, True{}, {[R.ElfReloc{w(16), R.ElfReloc.info(is64, 1, 2), W.W64.from_parts(4294967295, 4294967288)}, R.ElfReloc{w(32), R.ElfReloc.info(is64, 0, 8), w(4096)}] : List<&2, R.ElfReloc>})
  +dyn = DY.ElfDyn.write_table(is64, big, {[DY.ElfDyn{W.W64.one(), W.W64.one()}, DY.ElfDyn{w(14), w(18)}, DY.ElfDyn{w(1879048189), w(2)}, DY.ElfDyn{w(1879048192), w(5)}, DY.ElfDyn{W.W64.zero(), W.W64.zero()}, DY.ElfDyn{W.W64.zero(), W.W64.zero()}] : List<&2, DY.ElfDyn>})
  +note = N.ElfNote.write_all(big, N.ElfNoteAlign.default(), [N.ElfNote.make(3, B.Octets.of_string("GNU"), B.Octets.of_list([222, 173, 190, 239, 1, 2, 3]))])
  +versym = V.ElfVersym.write_table(big, {[V.ElfVersym{0}, V.ElfVersym{1}, V.ElfVersym{2}, V.ElfVersym{32771}] : List<&2, V.ElfVersym>})
  +verdef = V.ElfVerdef.write_chain(big, V.ElfVerdef.pack([V.ElfVerdefEntry{V.ElfVerdef{1, 1, 1, 0, 7574943, 0, 0}, [V.ElfVerdaux{18, 0}]}, V.ElfVerdefEntry{V.ElfVerdef{1, 0, 2, 0, 95058209, 0, 0}, [V.ElfVerdaux{11, 0}]}]))
  +verneed = V.ElfVerneed.write_chain(big, V.ElfVerneed.pack([V.ElfVerneedEntry{V.ElfVerneed{1, 0, 1, 0, 0}, [V.ElfVernaux{157882997, 0, 3, 26, 0}]}]))
  +hs = H.ElfHeader.size(is64)
  +o1 = hs
  +o2 = U32.add(o1, ext.len(ext.pad8(names)))
  +o3 = U32.add(o2, ext.len(ext.pad8(dynstr)))
  +o4 = U32.add(o3, ext.len(ext.pad8(rela)))
  +o5 = U32.add(o4, ext.len(ext.pad8(dyn)))
  +o6 = U32.add(o5, ext.len(ext.pad8(note)))
  +o7 = U32.add(o6, ext.len(ext.pad8(versym)))
  +o8 = U32.add(o7, ext.len(ext.pad8(verdef)))
  +shoff = U32.add(o8, ext.len(ext.pad8(verneed)))
  h = {H.ElfHeader{is64, big, 0, 0, 3, 62, 1, W.W64.zero(), W.W64.zero(), w(shoff), 0, hs, 0, 0, S.ElfShdr.size(is64), 9, 1} : H.ElfHeader}
  shdrs = S.ElfShdr.write_table(is64, big, {[S.ElfShdr{0, 0, W.W64.zero(), W.W64.zero(), W.W64.zero(), W.W64.zero(), 0, 0, W.W64.zero(), W.W64.zero()}, ext.sh(1, 3, o1, names, 0, 0, 1, 0), ext.sh(11, 3, o2, dynstr, 0, 0, 1, 0), ext.sh(19, 4, o3, rela, 0, 0, 8, R.ElfReloc.size(is64, True{})), ext.sh(30, 6, o4, dyn, 2, 0, 8, DY.ElfDyn.size(is64)), ext.sh(39, 7, o5, note, 0, 0, 4, 0), ext.sh(58, 1879048191, o6, versym, 0, 0, 2, 2), ext.sh(71, 1879048189, o7, verdef, 2, 2, 4, 0), ext.sh(86, 1879048190, o8, verneed, 2, 1, 4, 0)] : List<&2, S.ElfShdr>})
  B.Octets.concat({[H.ElfHeader.write(h), ext.pad8(names), ext.pad8(dynstr), ext.pad8(rela), ext.pad8(dyn), ext.pad8(note), ext.pad8(versym), ext.pad8(verdef), ext.pad8(verneed), shdrs] : List<&2, B.Octets>})

def main() -> IO(Unit):
  +big = build_big(3000)
  do IO<Unit>:
    D.dump(build(True{}, False{}))
    D.dump(build(False{}, True{}))
    IO.print(show_file(E.ElfFile.read(build(True{}, True{}))))
    IO.print(B.Octets.hex(P.ElfPhdr.write(False{}, True{}, P.ElfPhdr{1, 5, w(4096), w(268435456), w(268435456), w(116), w(116), w(65536)})))
    D.dump(B.Octets.of_string("not an ELF file"))
    D.dump(B.Octets.take(60n, build(True{}, False{})))
    D.dump(B.Octets.take(150n, build(False{}, False{})))
    IO.print(big.show(E.ElfFile.read(big), big))
    D.dump(build_ext(True{}, False{}))
    D.dump(build_ext(False{}, True{}))

#|header class=64 data=le osabi=0 abiversion=0 type=1 machine=62 version=1 entry=0000000000000000 phoff=0000000000000000 shoff=00000000000000b8 flags=0 ehsize=64 phentsize=0 phnum=0 shentsize=64 shnum=4 shstrndx=1
#|counts phnum=0 shnum=4 shstrndx=1
#|sh 0 name='' type=0 flags=0000000000000000 addr=0000000000000000 offset=0000000000000000 size=0000000000000000 link=0 info=0 align=0000000000000000 entsize=0000000000000000
#|sh 1 name='.shstrtab' type=3 flags=0000000000000000 addr=0000000000000000 offset=0000000000000040 size=000000000000001b link=0 info=0 align=0000000000000001 entsize=0000000000000000
#|sh 2 name='.symtab' type=2 flags=0000000000000000 addr=0000000000000000 offset=0000000000000070 size=0000000000000048 link=3 info=1 align=0000000000000008 entsize=0000000000000018
#|sh 3 name='.strtab' type=3 flags=0000000000000000 addr=0000000000000000 offset=0000000000000060 size=000000000000000b link=0 info=0 align=0000000000000001 entsize=0000000000000000
#|sym .symtab 0 name='' value=0000000000000000 size=0000000000000000 bind=0 type=0 other=0 shndx=0
#|sym .symtab 1 name='main' value=0000000000401000 size=000000000000000c bind=1 type=2 other=0 shndx=65521
#|sym .symtab 2 name='data' value=0000000000402000 size=0000000000000004 bind=2 type=1 other=2 shndx=65521
#|header class=32 data=be osabi=0 abiversion=0 type=1 machine=62 version=1 entry=0000000000000000 phoff=0000000000000000 shoff=0000000000000094 flags=0 ehsize=52 phentsize=0 phnum=0 shentsize=40 shnum=4 shstrndx=1
#|counts phnum=0 shnum=4 shstrndx=1
#|sh 0 name='' type=0 flags=0000000000000000 addr=0000000000000000 offset=0000000000000000 size=0000000000000000 link=0 info=0 align=0000000000000000 entsize=0000000000000000
#|sh 1 name='.shstrtab' type=3 flags=0000000000000000 addr=0000000000000000 offset=0000000000000034 size=000000000000001b link=0 info=0 align=0000000000000001 entsize=0000000000000000
#|sh 2 name='.symtab' type=2 flags=0000000000000000 addr=0000000000000000 offset=0000000000000064 size=0000000000000030 link=3 info=1 align=0000000000000008 entsize=0000000000000010
#|sh 3 name='.strtab' type=3 flags=0000000000000000 addr=0000000000000000 offset=0000000000000054 size=000000000000000b link=0 info=0 align=0000000000000001 entsize=0000000000000000
#|sym .symtab 0 name='' value=0000000000000000 size=0000000000000000 bind=0 type=0 other=0 shndx=0
#|sym .symtab 1 name='main' value=0000000000401000 size=000000000000000c bind=1 type=2 other=0 shndx=65521
#|sym .symtab 2 name='data' value=0000000000402000 size=0000000000000004 bind=2 type=1 other=2 shndx=65521
#|.symtab found, sh_type 2; .text not found
#|0000000100001000100000001000000000000074000000740000000500010000
#|error bad-magic
#|error truncated
#|header class=32 data=le osabi=0 abiversion=0 type=1 machine=62 version=1 entry=0000000000000000 phoff=0000000000000000 shoff=0000000000000094 flags=0 ehsize=52 phentsize=0 phnum=0 shentsize=40 shnum=4 shstrndx=1
#|counts phnum=0 shnum=4 shstrndx=1
#|shdrs error truncated
#|3001 symbols, values sum 4501500, last 'main'
#|header class=64 data=le osabi=0 abiversion=0 type=3 machine=62 version=1 entry=0000000000000000 phoff=0000000000000000 shoff=00000000000001d8 flags=0 ehsize=64 phentsize=0 phnum=0 shentsize=64 shnum=9 shstrndx=1
#|counts phnum=0 shnum=9 shstrndx=1
#|sh 0 name='' type=0 flags=0000000000000000 addr=0000000000000000 offset=0000000000000000 size=0000000000000000 link=0 info=0 align=0000000000000000 entsize=0000000000000000
#|sh 1 name='.shstrtab' type=3 flags=0000000000000002 addr=0000000000000000 offset=0000000000000040 size=0000000000000065 link=0 info=0 align=0000000000000001 entsize=0000000000000000
#|sh 2 name='.dynstr' type=3 flags=0000000000000002 addr=0000000000000000 offset=00000000000000a8 size=0000000000000026 link=0 info=0 align=0000000000000001 entsize=0000000000000000
#|sh 3 name='.rela.text' type=4 flags=0000000000000002 addr=0000000000000000 offset=00000000000000d0 size=0000000000000030 link=0 info=0 align=0000000000000008 entsize=0000000000000018
#|sh 4 name='.dynamic' type=6 flags=0000000000000002 addr=0000000000000000 offset=0000000000000100 size=0000000000000060 link=2 info=0 align=0000000000000008 entsize=0000000000000010
#|sh 5 name='.note.gnu.build-id' type=7 flags=0000000000000002 addr=0000000000000000 offset=0000000000000160 size=0000000000000018 link=0 info=0 align=0000000000000004 entsize=0000000000000000
#|sh 6 name='.gnu.version' type=1879048191 flags=0000000000000002 addr=0000000000000000 offset=0000000000000178 size=0000000000000008 link=0 info=0 align=0000000000000002 entsize=0000000000000002
#|sh 7 name='.gnu.version_d' type=1879048189 flags=0000000000000002 addr=0000000000000000 offset=0000000000000180 size=0000000000000038 link=2 info=2 align=0000000000000004 entsize=0000000000000000
#|sh 8 name='.gnu.version_r' type=1879048190 flags=0000000000000002 addr=0000000000000000 offset=00000000000001b8 size=0000000000000020 link=2 info=1 align=0000000000000004 entsize=0000000000000000
#|rel .rela.text 0 offset=0000000000000010 info=0000000100000002 sym=1 type=2 addend=fffffffffffffff8
#|rel .rela.text 1 offset=0000000000000020 info=0000000000000008 sym=0 type=8 addend=0000000000001000
#|dyns .dynamic entries=6
#|dyn .dynamic 0 tag=0000000000000001 val=0000000000000001 name=DT_NEEDED str='libc.so.6'
#|dyn .dynamic 1 tag=000000000000000e val=0000000000000012 name=DT_SONAME str='libx.so'
#|dyn .dynamic 2 tag=000000006ffffffd val=0000000000000002 name=DT_VERDEFNUM str=-
#|dyn .dynamic 3 tag=0000000070000000 val=0000000000000005 name=? str=-
#|dyn .dynamic 4 tag=0000000000000000 val=0000000000000000 name=DT_NULL str=-
#|note .note.gnu.build-id 0 namesz=4 descsz=7 type=3 owner=[GNU] desc=deadbeef010203 buildid=deadbeef010203
#|versym .gnu.version 0 index=0 hidden=0
#|versym .gnu.version 1 index=1 hidden=0
#|versym .gnu.version 2 index=2 hidden=0
#|versym .gnu.version 3 index=3 hidden=1
#|verdef .gnu.version_d 0 version=1 flags=1 ndx=1 cnt=1 hash=7574943 aux=20 next=28
#|verdaux .gnu.version_d 0 0 name='libx.so' next=0
#|verdef .gnu.version_d 1 version=1 flags=0 ndx=2 cnt=1 hash=95058209 aux=20 next=0
#|verdaux .gnu.version_d 1 0 name='VERS_1' next=0
#|verneed .gnu.version_r 0 version=1 cnt=1 file='libc.so.6' aux=16 next=0
#|vernaux .gnu.version_r 0 0 hash=157882997 flags=0 other=3 name='GLIBC_2.2.5' next=0
#|header class=32 data=be osabi=0 abiversion=0 type=3 machine=62 version=1 entry=0000000000000000 phoff=0000000000000000 shoff=0000000000000184 flags=0 ehsize=52 phentsize=0 phnum=0 shentsize=40 shnum=9 shstrndx=1
#|counts phnum=0 shnum=9 shstrndx=1
#|sh 0 name='' type=0 flags=0000000000000000 addr=0000000000000000 offset=0000000000000000 size=0000000000000000 link=0 info=0 align=0000000000000000 entsize=0000000000000000
#|sh 1 name='.shstrtab' type=3 flags=0000000000000002 addr=0000000000000000 offset=0000000000000034 size=0000000000000065 link=0 info=0 align=0000000000000001 entsize=0000000000000000
#|sh 2 name='.dynstr' type=3 flags=0000000000000002 addr=0000000000000000 offset=000000000000009c size=0000000000000026 link=0 info=0 align=0000000000000001 entsize=0000000000000000
#|sh 3 name='.rela.text' type=4 flags=0000000000000002 addr=0000000000000000 offset=00000000000000c4 size=0000000000000018 link=0 info=0 align=0000000000000008 entsize=000000000000000c
#|sh 4 name='.dynamic' type=6 flags=0000000000000002 addr=0000000000000000 offset=00000000000000dc size=0000000000000030 link=2 info=0 align=0000000000000008 entsize=0000000000000008
#|sh 5 name='.note.gnu.build-id' type=7 flags=0000000000000002 addr=0000000000000000 offset=000000000000010c size=0000000000000018 link=0 info=0 align=0000000000000004 entsize=0000000000000000
#|sh 6 name='.gnu.version' type=1879048191 flags=0000000000000002 addr=0000000000000000 offset=0000000000000124 size=0000000000000008 link=0 info=0 align=0000000000000002 entsize=0000000000000002
#|sh 7 name='.gnu.version_d' type=1879048189 flags=0000000000000002 addr=0000000000000000 offset=000000000000012c size=0000000000000038 link=2 info=2 align=0000000000000004 entsize=0000000000000000
#|sh 8 name='.gnu.version_r' type=1879048190 flags=0000000000000002 addr=0000000000000000 offset=0000000000000164 size=0000000000000020 link=2 info=1 align=0000000000000004 entsize=0000000000000000
#|rel .rela.text 0 offset=0000000000000010 info=0000000000000102 sym=1 type=2 addend=fffffffffffffff8
#|rel .rela.text 1 offset=0000000000000020 info=0000000000000008 sym=0 type=8 addend=0000000000001000
#|dyns .dynamic entries=6
#|dyn .dynamic 0 tag=0000000000000001 val=0000000000000001 name=DT_NEEDED str='libc.so.6'
#|dyn .dynamic 1 tag=000000000000000e val=0000000000000012 name=DT_SONAME str='libx.so'
#|dyn .dynamic 2 tag=000000006ffffffd val=0000000000000002 name=DT_VERDEFNUM str=-
#|dyn .dynamic 3 tag=0000000070000000 val=0000000000000005 name=? str=-
#|dyn .dynamic 4 tag=0000000000000000 val=0000000000000000 name=DT_NULL str=-
#|note .note.gnu.build-id 0 namesz=4 descsz=7 type=3 owner=[GNU] desc=deadbeef010203 buildid=deadbeef010203
#|versym .gnu.version 0 index=0 hidden=0
#|versym .gnu.version 1 index=1 hidden=0
#|versym .gnu.version 2 index=2 hidden=0
#|versym .gnu.version 3 index=3 hidden=1
#|verdef .gnu.version_d 0 version=1 flags=1 ndx=1 cnt=1 hash=7574943 aux=20 next=28
#|verdaux .gnu.version_d 0 0 name='libx.so' next=0
#|verdef .gnu.version_d 1 version=1 flags=0 ndx=2 cnt=1 hash=95058209 aux=20 next=0
#|verdaux .gnu.version_d 1 0 name='VERS_1' next=0
#|verneed .gnu.version_r 0 version=1 cnt=1 file='libc.so.6' aux=16 next=0
#|vernaux .gnu.version_r 0 0 hash=157882997 flags=0 other=3 name='GLIBC_2.2.5' next=0
