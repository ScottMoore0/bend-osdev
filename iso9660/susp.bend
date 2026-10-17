# bend-osdev-iso9660, susp.bend: the System Use Sharing Protocol (IEEE
# P1281, "SUSP", version 1.12, 1994). The system use area of a directory
# record holds entries: a two-byte signature, a length byte (counting the
# four header bytes), a version byte, then data. The entries used here:
#   SP  (the first entry of the root's "\0" record): check bytes 0xBE 0xEF
#       and LEN_SKP, the bytes to skip at the start of every system use area
#   CE  a continuation area: block, offset and length (both-endian 32 each),
#       read after the entries of the current area
#   ER  an extension reference: identifier, descriptor and source
#   ST  the end of the entries; PD padding (skipped)
# A zero byte where a signature would start, or fewer than four bytes left,
# ends an area (writers pad).
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as BD
import ./fields.bend as F

type IsoSuspEntry is Data:
  IsoSuspEntry{sig1: U32, sig2: U32, version: U32, data: B.Octets}

# a continuation area: its block, the offset in it and the length
type IsoCe is Data:
  IsoCe{block: U32, offset: U32, length: U32}

# an extension reference
type IsoEr is Data:
  IsoEr{id: String, descriptor: String, source: String, version: U32}

def IsoSuspEntry.sig(e: IsoSuspEntry) -> String:
  match e:
    case IsoSuspEntry{a, b, v, d}:
      B.to_string([a, b])

def IsoSuspEntry.is(e: IsoSuspEntry, +a: U32, +b: U32) -> Bool:
  match e:
    case IsoSuspEntry{x, y, v, d}:
      Bool.and(U32.is_eq(x, a), U32.is_eq(y, b))

def IsoSuspEntry.data_of(e: IsoSuspEntry) -> B.Octets:
  match e:
    case IsoSuspEntry{x, y, v, d}:
      d

# Parsing one area

def iso.susp.got(ok: Bool, s1: U32, s2: U32, v: U32, d: List<&2, U32>, rest: Result<&2, &2, F.IsoError, List<&2, IsoSuspEntry>>) -> Result<&2, &2, F.IsoError, List<&2, IsoSuspEntry>>:
  match ok:
    case True{}:
      Result.map(&2, &2, F.IsoError, List<&2, IsoSuspEntry>, List<&2, IsoSuspEntry>, es => Con{IsoSuspEntry{s1, s2, v, B.Octets.of_list(d)}, es}, rest)
    case False{}:
      Fail{F.IsoBadSusp{}}

def iso.susp.kind.go(end: Bool, short: Bool) -> Nat:
  match end short:
    case True{} _:
      0n
    case False{} True{}:
      1n
    case False{} False{}:
      2n

# what an entry header says: 0 the area ends, 1 a bad length, 2 an entry
def iso.susp.kind(+s1: U32, +s2: U32, +l: U32) -> Nat:
  iso.susp.kind.go(Bool.or(U32.is_eq(s1, 0), Bool.and(U32.is_eq(s1, 83), U32.is_eq(s2, 84))), U32.is_lt(l, 4))

def iso.susp.step(k: Nat, s1: U32, s2: U32, v: U32, +n: Nat, rest: List<&2, U32>, next: Result<&2, &2, F.IsoError, List<&2, IsoSuspEntry>>) -> Result<&2, &2, F.IsoError, List<&2, IsoSuspEntry>>:
  match k:
    case 0n:
      Done{Nil{}}
    case 1n:
      Fail{F.IsoBadSusp{}}
    case _:
      +d = B.take(n, rest)
      iso.susp.got(Nat.is_eq(B.len(d), n), s1, s2, v, d, next)

# the entries of an area, at most fuel of them
def iso.susp.list(fuel: Nat, xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, List<&2, IsoSuspEntry>>:
  match fuel:
    case 0n:
      Done{Nil{}}
    case 1n+f:
      match xs:
        case Con{+s1, Con{+s2, Con{+l, Con{v, +rest}}}}:
          +n = Nat.sub(U32.to_nat(l), 4n)
          iso.susp.step(iso.susp.kind(s1, s2, l), s1, s2, v, n, rest, iso.susp.list(f, B.drop(n, rest)))
        case _:
          Done{Nil{}}

# the entries of one system use area (no continuation followed)
def Iso.susp_parse(o: B.Octets) -> Result<&2, &2, F.IsoError, List<&2, IsoSuspEntry>>:
  +xs = B.Octets.to_list(o)
  iso.susp.list(B.len(xs), xs)

# Particular entries

def iso.susp.sp.check(ok: Bool, skip: U32) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{U32.to_nat(skip)}
    case False{}:
      None{}

def iso.susp.sp(xs: List<&2, U32>) -> Maybe<&2, Nat>:
  match xs:
    case Con{a, Con{b, Con{l, Con{v, Con{c1, Con{c2, Con{skip, t}}}}}}}:
      iso.susp.sp.check(Bool.and(Bool.and(U32.is_eq(a, 83), U32.is_eq(b, 80)), Bool.and(U32.is_eq(c1, 190), U32.is_eq(c2, 239))), skip)
    case _:
      None{}

# LEN_SKP, when the area starts with an SP entry (the root's "\0" record)
def Iso.susp_sp(o: B.Octets) -> Maybe<&2, Nat>:
  iso.susp.sp(B.Octets.to_list(o))

def iso.susp.ce.go(+mode: F.IsoEndian, +xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, IsoCe>:
  do Result<&2, &2, F.IsoError, IsoCe>:
    b : U32 <- F.iso.both32.list(mode, xs, 4n)
    o : U32 <- F.iso.both32.list(mode, B.drop(8n, xs), 12n)
    l : U32 <- F.iso.both32.list(mode, B.drop(16n, xs), 20n)
    return IsoCe{b, o, l}

def iso.susp.ce.fix(r: Result<&2, &2, F.IsoError, IsoCe>) -> Result<&2, &2, F.IsoError, IsoCe>:
  match r:
    case Fail{F.IsoTruncated{}}:
      Fail{F.IsoBadContinuation{}}
    case _:
      r

# a CE entry's fields
def IsoSuspEntry.ce(mode: F.IsoEndian, e: IsoSuspEntry) -> Result<&2, &2, F.IsoError, IsoCe>:
  iso.susp.ce.fix(iso.susp.ce.go(mode, B.Octets.to_list(IsoSuspEntry.data_of(e))))

def iso.susp.er.fin(ok: Bool, e: IsoEr) -> Result<&2, &2, F.IsoError, IsoEr>:
  match ok:
    case True{}:
      Done{e}
    case False{}:
      Fail{F.IsoBadSusp{}}

def iso.susp.er.go(xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, IsoEr>:
  match xs:
    case Con{+li, Con{+ld, Con{+ls, Con{v, +t}}}}:
      +ni = U32.to_nat(li)
      +nd = U32.to_nat(ld)
      +ns = U32.to_nat(ls)
      iso.susp.er.fin(Nat.is_le(Nat.add(ni, Nat.add(nd, ns)), B.len(t)), IsoEr{B.to_string(B.take(ni, t)), B.to_string(B.take(nd, B.drop(ni, t))), B.to_string(B.take(ns, B.drop(Nat.add(ni, nd), t))), v})
    case _:
      Fail{F.IsoBadSusp{}}

# an ER entry's fields
def IsoSuspEntry.er(e: IsoSuspEntry) -> Result<&2, &2, F.IsoError, IsoEr>:
  iso.susp.er.go(B.Octets.to_list(IsoSuspEntry.data_of(e)))

# Following continuation areas

def iso.susp.find_ce.pick(hit: Bool, mode: F.IsoEndian, e: IsoSuspEntry, rest: Result<&2, &2, F.IsoError, Maybe<&2, IsoCe>>) -> Result<&2, &2, F.IsoError, Maybe<&2, IsoCe>>:
  match hit:
    case True{}:
      Result.map(&2, &2, F.IsoError, IsoCe, Maybe<&2, IsoCe>, c => Some{c}, IsoSuspEntry.ce(mode, e))
    case False{}:
      rest

def iso.susp.find_ce(+mode: F.IsoEndian, es: List<&2, IsoSuspEntry>) -> Result<&2, &2, F.IsoError, Maybe<&2, IsoCe>>:
  match es:
    case Nil{}:
      Done{None{}}
    case Con{+e, t}:
      iso.susp.find_ce.pick(IsoSuspEntry.is(e, 67, 69), mode, e, iso.susp.find_ce(mode, t))

def iso.susp.area(ok: Bool, +off: Nat, +len: Nat, o: B.Octets) -> Result<&2, &2, F.IsoError, List<&2, U32>>:
  match ok:
    case True{}:
      Done{B.take(len, B.drop(off, B.Octets.to_list(o)))}
    case False{}:
      Fail{F.IsoBadContinuation{}}

def iso.susp.follow(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, d: D, m: Maybe<&2, IsoCe>) -> Result<&2, &2, F.IsoError, List<&2, U32>>:
  match m:
    case None{}:
      Done{Nil{}}
    case Some{IsoCe{b, o, l}}:
      +off = U32.to_nat(o)
      +len = U32.to_nat(l)
      do Result<&2, &2, F.IsoError, List<&2, U32>>:
        blk : B.Octets <- F.iso.read_sector(~D, ~read_block, d, U32.to_nat(b))
        iso.susp.area(Nat.is_le(Nat.add(off, len), 2048n), off, len, blk)

def iso.susp.last(ce: Result<&2, &2, F.IsoError, Maybe<&2, IsoCe>>, es: List<&2, IsoSuspEntry>) -> Result<&2, &2, F.IsoError, List<&2, IsoSuspEntry>>:
  match ce:
    case Done{None{}}:
      Done{es}
    case Done{Some{c}}:
      Fail{F.IsoContinuationLimit{}}
    case Fail{e}:
      Fail{e}

def iso.susp.parse.list(+xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, List<&2, IsoSuspEntry>>:
  iso.susp.list(B.len(xs), xs)

# the entries of an area and of the continuation areas it leads to, at most
# fuel continuations deep
def iso.susp.chase(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, fuel: Nat, +d: D, +mode: F.IsoEndian, xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, List<&2, IsoSuspEntry>>:
  match fuel:
    case 0n:
      do Result<&2, &2, F.IsoError, List<&2, IsoSuspEntry>>:
        +es : List<&2, IsoSuspEntry> <- iso.susp.parse.list(xs)
        iso.susp.last(iso.susp.find_ce(mode, es), es)
    case 1n+f:
      do Result<&2, &2, F.IsoError, List<&2, IsoSuspEntry>>:
        +es : List<&2, IsoSuspEntry> <- iso.susp.parse.list(xs)
        c : Maybe<&2, IsoCe> <- iso.susp.find_ce(mode, es)
        nx : List<&2, U32> <- iso.susp.follow(~D, ~read_block, d, c)
        more : List<&2, IsoSuspEntry> <- iso.susp.chase(~D, ~read_block, f, d, mode, nx)
        return List.append(&2, IsoSuspEntry, es, more)

# the entries of a record's system use area after skipping skip bytes (the
# SP entry's LEN_SKP), with every continuation area, at most fuel deep
def Iso.susp_entries(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, d: D, mode: F.IsoEndian, fuel: Nat, skip: Nat, area: B.Octets) -> Result<&2, &2, F.IsoError, List<&2, IsoSuspEntry>>:
  iso.susp.chase(~D, ~read_block, fuel, d, mode, B.drop(skip, B.Octets.to_list(area)))
