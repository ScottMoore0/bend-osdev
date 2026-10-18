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
import ../strtab.bend as T
import ../relocs.bend as R
import ../dynamic.bend as D
import ../notes.bend as N
import ../versions.bend as V

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
    case F.ElfBadSectionType{}:
      "bad-section-type"

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

def show_shdr(i: U32, +names: T.ElfStrtab, +s: S.ElfShdr) -> String:
  match s:
    case S.ElfShdr{nm, t, fl, ad, off, sz, lk, inf, al, es}:
      "sh " ++ n(i) ++ " name=" ++ show_name(S.ElfShdr.name_in(names, s)) ++ " type=" ++ n(t) ++ " flags=" ++ x(fl) ++ " addr=" ++ x(ad) ++ " offset=" ++ x(off) ++ " size=" ++ x(sz) ++ " link=" ++ n(lk) ++ " info=" ++ n(inf) ++ " align=" ++ x(al) ++ " entsize=" ++ x(es)

def show_sym(sec: String, i: U32, +strtab: T.ElfStrtab, +s: Y.ElfSym) -> String:
  match s:
    case Y.ElfSym{nm, v, sz, info, other, ndx}:
      "sym " ++ sec ++ " " ++ n(i) ++ " name=" ++ show_name(Y.ElfSym.name_in(strtab, s)) ++ " value=" ++ x(v) ++ " size=" ++ x(sz) ++ " bind=" ++ n(Y.ElfSym.bind(s)) ++ " type=" ++ n(Y.ElfSym.type(s)) ++ " other=" ++ n(other) ++ " shndx=" ++ n(ndx)

def print_phdrs(ps: List<&2, P.ElfPhdr>, +i: U32) -> IO(Unit):
  match ps:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{p, t}:
      do IO<Unit>:
        IO.print(show_phdr(i, p))
        print_phdrs(t, U32.add(i, 1))

def print_shdrs(ss: List<&2, S.ElfShdr>, +names: T.ElfStrtab, +i: U32) -> IO(Unit):
  match ss:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{s, t}:
      do IO<Unit>:
        IO.print(show_shdr(i, names, s))
        print_shdrs(t, names, U32.add(i, 1))

def print_syms(ys: List<&2, Y.ElfSym>, +sec: String, +strtab: T.ElfStrtab, +i: U32) -> IO(Unit):
  match ys:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{y, t}:
      do IO<Unit>:
        IO.print(show_sym(sec, i, strtab, y))
        print_syms(t, sec, strtab, U32.add(i, 1))

def print_syms.r(r: Result<&2, &2, F.ElfError, List<&2, Y.ElfSym>>, +sec: String, +strtab: T.ElfStrtab) -> IO(Unit):
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

def print_symtab.go(yes_symtab: Bool, +o: B.Octets, +h: H.ElfHeader, +ss: List<&2, S.ElfShdr>, +names: T.ElfStrtab, +s: S.ElfShdr) -> IO(Unit):
  match yes_symtab:
    case False{}:
      IO.pure(Unit, Unit{})
    case True{}:
      +sec = name_text(S.ElfShdr.name_in(names, s))
      +strtab = T.ElfStrtab.of(strtab_or_empty(S.ElfShdr.bytes_at(o, ss, S.ElfShdr.sh_link(s))))
      print_syms.r(Y.ElfSym.all(o, h, s), sec, strtab)

def is_symtab(+t: U32) -> Bool:
  Bool.or(U32.is_eq(t, 2), U32.is_eq(t, 11))

def print_symtabs(ss: List<&2, S.ElfShdr>, +o: B.Octets, +h: H.ElfHeader, +all: List<&2, S.ElfShdr>, +names: T.ElfStrtab) -> IO(Unit):
  match ss:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+s, t}:
      do IO<Unit>:
        print_symtab.go(is_symtab(S.ElfShdr.sh_type(s)), o, h, all, names, s)
        print_symtabs(t, o, h, all, names)

# Relocations, dynamic sections, notes and symbol versions

def b01(b: Bool) -> String:
  yes(b, "1", "0")

def str_ix(+o: B.Octets, +ss: List<&2, S.ElfShdr>, i: U32) -> T.ElfStrtab:
  T.ElfStrtab.of(strtab_or_empty(S.ElfShdr.bytes_at(o, ss, i)))

def show_rel(sec: String, i: U32, +is64: Bool, +r: R.ElfReloc) -> String:
  "rel " ++ sec ++ " " ++ n(i) ++ " offset=" ++ x(R.ElfReloc.r_offset(r)) ++ " info=" ++ x(R.ElfReloc.r_info(r)) ++ " sym=" ++ n(R.ElfReloc.sym(is64, r)) ++ " type=" ++ n(R.ElfReloc.type(is64, r)) ++ " addend=" ++ x(R.ElfReloc.r_addend(r))

def print_rels(rs: List<&2, R.ElfReloc>, +sec: String, +is64: Bool, +i: U32) -> IO(Unit):
  match rs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{r, t}:
      do IO<Unit>:
        IO.print(show_rel(sec, i, is64, r))
        print_rels(t, sec, is64, U32.add(i, 1))

def print_rels.r(r: Result<&2, &2, F.ElfError, List<&2, R.ElfReloc>>, +sec: String, +is64: Bool) -> IO(Unit):
  match r:
    case Done{rs}:
      print_rels(rs, sec, is64, 0)
    case Fail{e}:
      IO.print("rels " ++ sec ++ " error " ++ err(e))

def tag_name(m: Maybe<&2, D.ElfDynTag>) -> String:
  match m:
    case Some{k}:
      D.ElfDynTag.name(k)
    case None{}:
      "?"

# the string of DT_NEEDED (1), DT_SONAME (14), DT_RPATH (15), DT_RUNPATH (29)
def dyn_str.go(hit: Bool, +strtab: T.ElfStrtab, +d: D.ElfDyn) -> String:
  match hit:
    case True{}:
      show_name(D.ElfDyn.string(strtab, d))
    case False{}:
      "-"

def dyn_str(+strtab: T.ElfStrtab, +d: D.ElfDyn) -> String:
  +t = W.W64.lo(D.ElfDyn.d_tag(d))
  +small = U32.is_eq(W.W64.hi(D.ElfDyn.d_tag(d)), 0)
  dyn_str.go(Bool.and(small, Bool.or(Bool.or(U32.is_eq(t, 1), U32.is_eq(t, 14)), Bool.or(U32.is_eq(t, 15), U32.is_eq(t, 29)))), strtab, d)

def print_dyns(ds: List<&2, D.ElfDyn>, +sec: String, +strtab: T.ElfStrtab, +i: U32) -> IO(Unit):
  match ds:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+d, t}:
      do IO<Unit>:
        IO.print("dyn " ++ sec ++ " " ++ n(i) ++ " tag=" ++ x(D.ElfDyn.d_tag(d)) ++ " val=" ++ x(D.ElfDyn.d_val(d)) ++ " name=" ++ tag_name(D.ElfDyn.tag(d)) ++ " str=" ++ dyn_str(strtab, d))
        print_dyns(t, sec, strtab, U32.add(i, 1))

def print_dyns.r(r: Result<&2, &2, F.ElfError, List<&2, D.ElfDyn>>, +sec: String, +strtab: T.ElfStrtab) -> IO(Unit):
  match r:
    case Done{+ds}:
      do IO<Unit>:
        IO.print("dyns " ++ sec ++ " entries=" ++ Nat.show(List.length(&2, D.ElfDyn, ds)))
        print_dyns(D.ElfDyn.until_null(ds), sec, strtab, 0)
    case Fail{e}:
      IO.print("dyns " ++ sec ++ " error " ++ err(e))

def show_build_id(m: Maybe<&2, B.Octets>) -> String:
  match m:
    case Some{o}:
      B.Octets.hex(o)
    case None{}:
      "-"

def show_note(kind: String, i: U32, +nt: N.ElfNote) -> String:
  kind ++ " " ++ n(i) ++ " namesz=" ++ n(N.ElfNote.n_namesz(nt)) ++ " descsz=" ++ n(N.ElfNote.n_descsz(nt)) ++ " type=" ++ n(N.ElfNote.n_type(nt)) ++ " owner=[" ++ B.Octets.to_string(N.ElfNote.owner(nt)) ++ "] desc=" ++ B.Octets.hex(N.ElfNote.desc(nt)) ++ " buildid=" ++ show_build_id(N.ElfNote.build_id(nt))

def print_notes(ns: List<&2, N.ElfNote>, +kind: String, +i: U32) -> IO(Unit):
  match ns:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{nt, t}:
      do IO<Unit>:
        IO.print(show_note(kind, i, nt))
        print_notes(t, kind, U32.add(i, 1))

def print_notes.r(r: Result<&2, &2, F.ElfError, List<&2, N.ElfNote>>, +kind: String) -> IO(Unit):
  match r:
    case Done{ns}:
      print_notes(ns, kind, 0)
    case Fail{e}:
      IO.print(kind ++ " error " ++ err(e))

def print_versyms(vs: List<&2, V.ElfVersym>, +sec: String, +i: U32) -> IO(Unit):
  match vs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+v, t}:
      do IO<Unit>:
        IO.print("versym " ++ sec ++ " " ++ n(i) ++ " index=" ++ n(V.ElfVersym.index(v)) ++ " hidden=" ++ b01(V.ElfVersym.hidden(v)))
        print_versyms(t, sec, U32.add(i, 1))

def print_versyms.r(r: Result<&2, &2, F.ElfError, List<&2, V.ElfVersym>>, +sec: String) -> IO(Unit):
  match r:
    case Done{vs}:
      print_versyms(vs, sec, 0)
    case Fail{e}:
      IO.print("versyms " ++ sec ++ " error " ++ err(e))

def print_verdauxs(as: List<&2, V.ElfVerdaux>, +head: String, +strtab: T.ElfStrtab, +j: U32) -> IO(Unit):
  match as:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+a, t}:
      do IO<Unit>:
        IO.print("verdaux " ++ head ++ " " ++ n(j) ++ " name=" ++ show_name(T.ElfStrtab.string(strtab, V.ElfVerdaux.vda_name(a))) ++ " next=" ++ n(V.ElfVerdaux.vda_next(a)))
        print_verdauxs(t, head, strtab, U32.add(j, 1))

def print_verdefs(es: List<&2, V.ElfVerdefEntry>, +sec: String, +strtab: T.ElfStrtab, +i: U32) -> IO(Unit):
  match es:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{V.ElfVerdefEntry{V.ElfVerdef{ver, fl, ndx, cnt, hash, aux, next}, as}, t}:
      do IO<Unit>:
        IO.print("verdef " ++ sec ++ " " ++ n(i) ++ " version=" ++ n(ver) ++ " flags=" ++ n(fl) ++ " ndx=" ++ n(ndx) ++ " cnt=" ++ n(cnt) ++ " hash=" ++ n(hash) ++ " aux=" ++ n(aux) ++ " next=" ++ n(next))
        print_verdauxs(as, sec ++ " " ++ n(i), strtab, 0)
        print_verdefs(t, sec, strtab, U32.add(i, 1))

def print_verdefs.r(r: Result<&2, &2, F.ElfError, List<&2, V.ElfVerdefEntry>>, +sec: String, +strtab: T.ElfStrtab) -> IO(Unit):
  match r:
    case Done{es}:
      print_verdefs(es, sec, strtab, 0)
    case Fail{e}:
      IO.print("verdefs " ++ sec ++ " error " ++ err(e))

def print_vernauxs(as: List<&2, V.ElfVernaux>, +head: String, +strtab: T.ElfStrtab, +j: U32) -> IO(Unit):
  match as:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{V.ElfVernaux{hash, fl, other, nm, next}, t}:
      do IO<Unit>:
        IO.print("vernaux " ++ head ++ " " ++ n(j) ++ " hash=" ++ n(hash) ++ " flags=" ++ n(fl) ++ " other=" ++ n(other) ++ " name=" ++ show_name(T.ElfStrtab.string(strtab, nm)) ++ " next=" ++ n(next))
        print_vernauxs(t, head, strtab, U32.add(j, 1))

def print_verneeds(es: List<&2, V.ElfVerneedEntry>, +sec: String, +strtab: T.ElfStrtab, +i: U32) -> IO(Unit):
  match es:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{V.ElfVerneedEntry{V.ElfVerneed{ver, cnt, file, aux, next}, as}, t}:
      do IO<Unit>:
        IO.print("verneed " ++ sec ++ " " ++ n(i) ++ " version=" ++ n(ver) ++ " cnt=" ++ n(cnt) ++ " file=" ++ show_name(T.ElfStrtab.string(strtab, file)) ++ " aux=" ++ n(aux) ++ " next=" ++ n(next))
        print_vernauxs(as, sec ++ " " ++ n(i), strtab, 0)
        print_verneeds(t, sec, strtab, U32.add(i, 1))

def print_verneeds.r(r: Result<&2, &2, F.ElfError, List<&2, V.ElfVerneedEntry>>, +sec: String, +strtab: T.ElfStrtab) -> IO(Unit):
  match r:
    case Done{es}:
      print_verneeds(es, sec, strtab, 0)
    case Fail{e}:
      IO.print("verneeds " ++ sec ++ " error " ++ err(e))

# each kind of section, if s is one
def extra.rel(hit: Bool, +o: B.Octets, +h: H.ElfHeader, +sec: String, +s: S.ElfShdr) -> IO(Unit):
  match hit:
    case True{}:
      print_rels.r(R.ElfReloc.all(o, h, s), sec, H.ElfHeader.is64(h))
    case False{}:
      IO.pure(Unit, Unit{})

def extra.dyn(hit: Bool, +o: B.Octets, +h: H.ElfHeader, +ss: List<&2, S.ElfShdr>, +sec: String, +s: S.ElfShdr) -> IO(Unit):
  match hit:
    case True{}:
      print_dyns.r(D.ElfDyn.all(o, h, s), sec, str_ix(o, ss, S.ElfShdr.sh_link(s)))
    case False{}:
      IO.pure(Unit, Unit{})

def extra.note(hit: Bool, +o: B.Octets, +h: H.ElfHeader, +sec: String, +s: S.ElfShdr) -> IO(Unit):
  match hit:
    case True{}:
      print_notes.r(N.ElfNote.all(o, h, s), "note " ++ sec)
    case False{}:
      IO.pure(Unit, Unit{})

def extra.versym(hit: Bool, +o: B.Octets, +h: H.ElfHeader, +sec: String, +s: S.ElfShdr) -> IO(Unit):
  match hit:
    case True{}:
      print_versyms.r(V.ElfVersym.all(o, h, s), sec)
    case False{}:
      IO.pure(Unit, Unit{})

def extra.verdef(hit: Bool, +o: B.Octets, +h: H.ElfHeader, +ss: List<&2, S.ElfShdr>, +sec: String, +s: S.ElfShdr) -> IO(Unit):
  match hit:
    case True{}:
      print_verdefs.r(V.ElfVerdef.all(o, h, s), sec, str_ix(o, ss, S.ElfShdr.sh_link(s)))
    case False{}:
      IO.pure(Unit, Unit{})

def extra.verneed(hit: Bool, +o: B.Octets, +h: H.ElfHeader, +ss: List<&2, S.ElfShdr>, +sec: String, +s: S.ElfShdr) -> IO(Unit):
  match hit:
    case True{}:
      print_verneeds.r(V.ElfVerneed.all(o, h, s), sec, str_ix(o, ss, S.ElfShdr.sh_link(s)))
    case False{}:
      IO.pure(Unit, Unit{})

def print_extras(ss: List<&2, S.ElfShdr>, +o: B.Octets, +h: H.ElfHeader, +all: List<&2, S.ElfShdr>, +names: T.ElfStrtab) -> IO(Unit):
  match ss:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+s, t}:
      +sec = name_text(S.ElfShdr.name_in(names, s))
      do IO<Unit>:
        extra.rel(R.ElfReloc.is_section(s), o, h, sec, s)
        extra.dyn(D.ElfDyn.is_section(s), o, h, all, sec, s)
        extra.note(N.ElfNote.is_section(s), o, h, sec, s)
        extra.versym(V.ElfVersym.is_section(s), o, h, sec, s)
        extra.verdef(V.ElfVerdef.is_section(s), o, h, all, sec, s)
        extra.verneed(V.ElfVerneed.is_section(s), o, h, all, sec, s)
        print_extras(t, o, h, all, names)

def pnote.go(hit: Bool, +o: B.Octets, +h: H.ElfHeader, +i: U32, +p: P.ElfPhdr) -> IO(Unit):
  match hit:
    case True{}:
      print_notes.r(N.ElfNote.segment(o, h, p), "pnote " ++ n(i))
    case False{}:
      IO.pure(Unit, Unit{})

def print_pnotes(ps: List<&2, P.ElfPhdr>, +o: B.Octets, +h: H.ElfHeader, +i: U32) -> IO(Unit):
  match ps:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+p, t}:
      do IO<Unit>:
        pnote.go(N.ElfNote.is_segment(p), o, h, i, p)
        print_pnotes(t, o, h, U32.add(i, 1))

def print_pnotes.r(r: Result<&2, &2, F.ElfError, List<&2, P.ElfPhdr>>, +o: B.Octets, +h: H.ElfHeader) -> IO(Unit):
  match r:
    case Done{ps}:
      print_pnotes(ps, o, h, 0)
    case Fail{e}:
      IO.pure(Unit, Unit{})

def names_of(+o: B.Octets, +h: H.ElfHeader, ss: List<&2, S.ElfShdr>) -> T.ElfStrtab:
  T.ElfStrtab.of(strtab_or_empty(S.ElfShdr.shstrtab(o, h, ss)))

def dump_sections.go(r: Result<&2, &2, F.ElfError, List<&2, S.ElfShdr>>, +o: B.Octets, +h: H.ElfHeader) -> IO(Unit):
  match r:
    case Done{+ss}:
      +names = names_of(o, h, ss)
      do IO<Unit>:
        print_shdrs(ss, names, 0)
        print_symtabs(ss, o, h, ss, names)
        print_extras(ss, o, h, ss, names)
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
        print_pnotes.r(P.ElfPhdr.all(o, h), o, h)
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
