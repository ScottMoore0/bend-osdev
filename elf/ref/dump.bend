# The dump the differential test compares: every field of every structure of
# a file, one line each, in the format ref/gen.py writes from readelf and from
# its own reader.
import Base
import ../../word64/word64.bend as W
import ../../bytes/bytes.bend as B
import ../fields.bend as F
import ../header.bend as H
import ../sections.bend as S
import ../segments.bend as P
import ../symbols.bend as Y

def err(e: F.ElfError) -> String:
  match e:
    case F.ElfTruncated{}:
      "truncated"
    case F.ElfBadMagic{}:
      "bad-magic"
    case F.ElfBadClass{}:
      "bad-class"
    case F.ElfBadData{}:
      "bad-data"
    case F.ElfBadVersion{}:
      "bad-version"
    case F.ElfOffsetOutOfRange{}:
      "offset-out-of-range"
    case F.ElfBadEntrySize{}:
      "bad-entry-size"
    case F.ElfBadIndex{}:
      "bad-index"
    case F.ElfBadString{}:
      "bad-string"
    case F.ElfNoSectionTable{}:
      "no-section-table"

def x(v: W.W64) -> String:
  W.W64.show_hex(v)

def n(v: U32) -> String:
  U32.show(v)

def yes(b: Bool, t: String, f: String) -> String:
  match b:
    case True{}:
      t
    case False{}:
      f

def show_header(h: H.ElfHeader) -> String:
  match h:
    case H.ElfHeader{is64, big, osabi, abiv, t, m, v, entry, phoff, shoff, flags, ehsize, phentsize, phnum, shentsize, shnum, shstrndx}:
      "header class=" ++ yes(is64, "64", "32") ++ " data=" ++ yes(big, "be", "le") ++ " osabi=" ++ n(osabi) ++ " abiversion=" ++ n(abiv) ++ " type=" ++ n(t) ++ " machine=" ++ n(m) ++ " version=" ++ n(v) ++ " entry=" ++ x(entry) ++ " phoff=" ++ x(phoff) ++ " shoff=" ++ x(shoff) ++ " flags=" ++ n(flags) ++ " ehsize=" ++ n(ehsize) ++ " phentsize=" ++ n(phentsize) ++ " phnum=" ++ n(phnum) ++ " shentsize=" ++ n(shentsize) ++ " shnum=" ++ n(shnum) ++ " shstrndx=" ++ n(shstrndx)

def show_phdr(i: U32, p: P.ElfPhdr) -> String:
  match p:
    case P.ElfPhdr{t, fl, off, va, pa, fs, ms, al}:
      "ph " ++ n(i) ++ " type=" ++ n(t) ++ " flags=" ++ n(fl) ++ " offset=" ++ x(off) ++ " vaddr=" ++ x(va) ++ " paddr=" ++ x(pa) ++ " filesz=" ++ x(fs) ++ " memsz=" ++ x(ms) ++ " align=" ++ x(al)

def show_name(r: Result<&2, &2, F.ElfError, B.Octets>) -> String:
  match r:
    case Done{o}:
      "'" ++ B.Octets.to_string(o) ++ "'"
    case Fail{e}:
      "!" ++ err(e)

def show_shdr(i: U32, +names: B.Octets, +s: S.ElfShdr) -> String:
  match s:
    case S.ElfShdr{nm, t, fl, ad, off, sz, lk, inf, al, es}:
      "sh " ++ n(i) ++ " name=" ++ show_name(S.ElfShdr.name(names, s)) ++ " type=" ++ n(t) ++ " flags=" ++ x(fl) ++ " addr=" ++ x(ad) ++ " offset=" ++ x(off) ++ " size=" ++ x(sz) ++ " link=" ++ n(lk) ++ " info=" ++ n(inf) ++ " align=" ++ x(al) ++ " entsize=" ++ x(es)

def show_sym(sec: String, i: U32, +strtab: B.Octets, +s: Y.ElfSym) -> String:
  match s:
    case Y.ElfSym{nm, v, sz, info, other, ndx}:
      "sym " ++ sec ++ " " ++ n(i) ++ " name=" ++ show_name(Y.ElfSym.name(strtab, s)) ++ " value=" ++ x(v) ++ " size=" ++ x(sz) ++ " bind=" ++ n(Y.ElfSym.bind(s)) ++ " type=" ++ n(Y.ElfSym.type(s)) ++ " other=" ++ n(other) ++ " shndx=" ++ n(ndx)

def print_phdrs(ps: List<&2, P.ElfPhdr>, +i: U32) -> IO(Unit):
  match ps:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{p, t}:
      do IO<Unit>:
        IO.print(show_phdr(i, p))
        print_phdrs(t, U32.add(i, 1))

def print_shdrs(ss: List<&2, S.ElfShdr>, +names: B.Octets, +i: U32) -> IO(Unit):
  match ss:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{s, t}:
      do IO<Unit>:
        IO.print(show_shdr(i, names, s))
        print_shdrs(t, names, U32.add(i, 1))

def print_syms(ys: List<&2, Y.ElfSym>, +sec: String, +strtab: B.Octets, +i: U32) -> IO(Unit):
  match ys:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{y, t}:
      do IO<Unit>:
        IO.print(show_sym(sec, i, strtab, y))
        print_syms(t, sec, strtab, U32.add(i, 1))

def print_syms.r(r: Result<&2, &2, F.ElfError, List<&2, Y.ElfSym>>, +sec: String, +strtab: B.Octets) -> IO(Unit):
  match r:
    case Done{ys}:
      print_syms(ys, sec, strtab, 0)
    case Fail{e}:
      IO.print("syms " ++ sec ++ " error " ++ err(e))

def name_text(r: Result<&2, &2, F.ElfError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.to_string(o)
    case Fail{e}:
      "?"

def strtab_or_empty(r: Result<&2, &2, F.ElfError, B.Octets>) -> B.Octets:
  match r:
    case Done{o}:
      o
    case Fail{e}:
      B.Octets.empty()

def print_symtab.go(yes_symtab: Bool, +o: B.Octets, +h: H.ElfHeader, +ss: List<&2, S.ElfShdr>, +names: B.Octets, +s: S.ElfShdr) -> IO(Unit):
  match yes_symtab:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      +sec = name_text(S.ElfShdr.name(names, s))
      +strtab = strtab_or_empty(S.ElfShdr.bytes_at(o, ss, S.ElfShdr.sh_link(s)))
      print_syms.r(Y.ElfSym.all(o, h, s), sec, strtab)

def is_symtab(+t: U32) -> Bool:
  Bool.or(U32.is_eq(t, 2), U32.is_eq(t, 11))

def print_symtabs(ss: List<&2, S.ElfShdr>, +o: B.Octets, +h: H.ElfHeader, +all: List<&2, S.ElfShdr>, +names: B.Octets) -> IO(Unit):
  match ss:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+s, t}:
      do IO<Unit>:
        print_symtab.go(is_symtab(S.ElfShdr.sh_type(s)), o, h, all, names, s)
        print_symtabs(t, o, h, all, names)

def names_of(+o: B.Octets, +h: H.ElfHeader, ss: List<&2, S.ElfShdr>) -> B.Octets:
  strtab_or_empty(S.ElfShdr.shstrtab(o, h, ss))

def dump_sections.go(r: Result<&2, &2, F.ElfError, List<&2, S.ElfShdr>>, +o: B.Octets, +h: H.ElfHeader) -> IO(Unit):
  match r:
    case Done{+ss}:
      +names = names_of(o, h, ss)
      do IO<Unit>:
        print_shdrs(ss, names, 0)
        print_symtabs(ss, o, h, ss, names)
    case Fail{e}:
      IO.print("shdrs error " ++ err(e))

def dump_counts(c: Result<&2, &2, F.ElfError, U32>) -> String:
  match c:
    case Done{v}:
      n(v)
    case Fail{e}:
      err(e)

def dump_sections(+o: B.Octets, +h: H.ElfHeader) -> IO(Unit):
  dump_sections.go(S.ElfShdr.all(o, h), o, h)

def dump_phdrs(r: Result<&2, &2, F.ElfError, List<&2, P.ElfPhdr>>) -> IO(Unit):
  match r:
    case Done{ps}:
      print_phdrs(ps, 0)
    case Fail{e}:
      IO.print("phdrs error " ++ err(e))

def dump.go(r: Result<&2, &2, F.ElfError, H.ElfHeader>, +o: B.Octets) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("error " ++ err(e))
    case Done{+h}:
      do IO<Unit>:
        IO.print(show_header(h))
        IO.print("counts phnum=" ++ dump_counts(S.ElfShdr.phnum(o, h)) ++ " shnum=" ++ dump_counts(S.ElfShdr.count(o, h)) ++ " shstrndx=" ++ dump_counts(S.ElfShdr.shstrndx(o, h)))
        dump_phdrs(P.ElfPhdr.all(o, h))
        dump_sections(o, h)

def dump(+o: B.Octets) -> IO(Unit):
  dump.go(H.ElfHeader.parse(o), o)

def dump_read.r(r: Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Unit):
  match r:
    case Done{xs}:
      dump(B.Octets.of_list(xs))
    case Fail{e}:
      IO.print("error unreadable")

def dump_read(p: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Unit):
  (f, r) = p
  do IO<Unit>:
    File.close(f)
    dump_read.r(r)

# read the file at path (up to 1 MiB) and dump it, after a line naming it
def dump_file(label: String, path: String) -> IO(Unit):
  do IO<Unit>:
    IO.print("file " ++ label)
    f : File <- IO.try(File, File.open(path, "r"))
    p : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 1048576)
    dump_read(p)

# dump each (label, path) in turn
def dump_files(fs: List<(String & String)>) -> IO(Unit):
  match fs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{(label, path), t}:
      do IO<Unit>:
        dump_file(label, path)
        dump_files(t)
