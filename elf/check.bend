import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./fields.bend as F
import ./header.bend as H
import ./sections.bend as S
import ./segments.bend as P
import ./symbols.bend as Y
import ./elf.bend as E
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
