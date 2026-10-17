# bend-osdev-iso9660, dir.bend: walking directories (ECMA-119, 4th edition,
# 6.8 and 9.1). A directory is an extent of whole logical sectors; each
# sector holds directory records from its start, and a zero byte where a
# record would start ends that sector's records (records never cross a
# sector boundary). The walk reads the directory's own sectors and nothing
# else (a law); turning records into named entries may also read SUSP
# continuation areas (Rock Ridge) and, for a relocated directory, the
# first sector of the directory its CL entry points to.
#
# Entries are named by the volume's naming (volume.bend): the file
# identifier (plain), its UCS-2 form (Joliet) or the Rock Ridge NM name.
# A file of several extents (the multi-extent flag on every record but its
# last) is one entry with every extent.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../blockdev/blockdev.bend as BD
import ./fields.bend as F
import ./joliet.bend as J
import ./dirrec.bend as R
import ./susp.bend as S
import ./rockridge.bend as RR
import ./volume.bend as V

# The records of a directory

def iso.dir.zero(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      U32.is_eq(h, 0)

# the records of a sector, from xs (the sector's bytes from a record on);
# end: xs is empty or starts with a zero byte
def iso.dir.sector(fuel: Nat, end: Bool, +mode: F.IsoEndian, +xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>:
  match fuel:
    case 0n:
      Done{Nil{}}
    case 1n+f:
      match end:
        case True{}:
          Done{Nil{}}
        case False{}:
          do Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>:
            +r : R.IsoDirRec <- R.iso.dirrec.list(mode, xs)
            +ys : List<&2, U32> = B.drop(R.IsoDirRec.length(r), xs)
            rest : List<&2, R.IsoDirRec> <- iso.dir.sector(f, iso.dir.zero(ys), mode, ys)
            return Con{r, rest}

# the records of one sector of a directory, of which left bytes remain
def iso.dir.records(+mode: F.IsoEndian, +left: Nat, blk: B.Octets) -> Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>:
  +xs = B.take(left, B.Octets.to_list(blk))
  iso.dir.sector(61n, iso.dir.zero(xs), mode, xs)

# one sector's records (rr) in front of the rest's
def iso.dir.walk.join(rr: Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>, rest: Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>) -> Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>:
  match rr rest:
    case Fail{e} _:
      Fail{e}
    case Done{recs} Fail{e}:
      Fail{e}
    case Done{recs} Done{more}:
      Done{List.append(&2, R.IsoDirRec, recs, more)}

def iso.dir.walk.step(r: Result<&2, &2, F.IsoError, B.Octets>, +mode: F.IsoEndian, +left: Nat, rest: Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>) -> Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{blk}:
      iso.dir.walk.join(iso.dir.records(mode, left, blk), rest)

# The reference walk, structural: the records of the k sectors of a
# directory from its sector i on (left: the bytes of the directory from
# sector i on); it reads blocks ext + i to ext + i + k - 1 and no others.
# It recurses once per sector; iso.dir.walk below is the same as a loop
# (PROOF.bend proves the two equal for every input).
def iso.dir.walk.ref(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, k: Nat, +d: D, +mode: F.IsoEndian, +ext: Nat, +left: Nat, +i: Nat) -> Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>:
  match k:
    case 0n:
      Done{Nil{}}
    case 1n+p:
      iso.dir.walk.step(F.iso.read_sector(~D, ~read_block, d, Nat.add(ext, i)), mode, left, iso.dir.walk.ref(~D, ~read_block, p, d, mode, ext, Nat.sub(left, 2048n), 1n+i))

def iso.dir.rev(xs: List<&2, R.IsoDirRec>, acc: List<&2, R.IsoDirRec>) -> List<&2, R.IsoDirRec>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      iso.dir.rev(t, Con{h, acc})

def iso.dir.walk.push(rr: Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>, acc: List<&2, R.IsoDirRec>) -> Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>:
  match rr:
    case Fail{e}:
      Fail{e}
    case Done{recs}:
      Done{iso.dir.rev(recs, acc)}

# one sector's records, reversed onto the records so far (latest first)
def iso.dir.walk.add(r: Result<&2, &2, F.IsoError, B.Octets>, +mode: F.IsoEndian, +left: Nat, acc: List<&2, R.IsoDirRec>) -> Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{blk}:
      iso.dir.walk.push(iso.dir.records(mode, left, blk), acc)

def iso.dir.walk.fin(acc: Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>) -> Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>:
  match acc:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      Done{iso.dir.rev(a, Nil{})}

# the walk as a loop: acc holds the records of the sectors before sector i
# (latest first), or the first error; it reads what the reference reads
def iso.dir.walk(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, k: Nat, +d: D, +mode: F.IsoEndian, +ext: Nat, +left: Nat, +i: Nat, acc: Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>) -> Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>:
  match k:
    case 0n:
      iso.dir.walk.fin(acc)
    case 1n+p:
      match acc:
        case Fail{e}:
          Fail{e}
        case Done{a}:
          iso.dir.walk(~D, ~read_block, p, d, mode, ext, Nat.sub(left, 2048n), 1n+i, iso.dir.walk.add(F.iso.read_sector(~D, ~read_block, d, Nat.add(ext, i)), mode, left, a))

# every record of the directory whose extent starts at block ext and is
# size bytes long, "\0" and "\1" included, in order
def Iso.dir_records(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, d: D, mode: F.IsoEndian, ext: U32, +size: U32) -> Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>:
  iso.dir.walk(~D, ~read_block, R.Iso.blocks(size), d, mode, U32.to_nat(ext), U32.to_nat(size), 0n, Done{Nil{}})

# Entries

# an extent of a file: its first block (after any extended attribute
# record) and its length in bytes
type IsoExtent is Data:
  IsoExtent{block: U32, size: U32}

# a directory entry: its name, whether it is a directory, its size (every
# extent's together), its extents, its (last) record, and what its Rock
# Ridge entries say (Rock Ridge naming only)
type IsoEntry is Data:
  IsoEntry{name: String, is_dir: Bool, size: W.W64, extents: List<&2, IsoExtent>, rec: R.IsoDirRec, rr: Maybe<&2, RR.IsoRr>}

def IsoEntry.name_of(e: IsoEntry) -> String:
  match e:
    case IsoEntry{n, d, s, x, r, rr}:
      n

def IsoEntry.is_dir_of(e: IsoEntry) -> Bool:
  match e:
    case IsoEntry{n, d, s, x, r, rr}:
      d

def IsoEntry.size_of(e: IsoEntry) -> W.W64:
  match e:
    case IsoEntry{n, d, s, x, r, rr}:
      s

def IsoEntry.extents_of(e: IsoEntry) -> List<&2, IsoExtent>:
  match e:
    case IsoEntry{n, d, s, x, r, rr}:
      x

def IsoEntry.rec_of(e: IsoEntry) -> R.IsoDirRec:
  match e:
    case IsoEntry{n, d, s, x, r, rr}:
      r

def IsoEntry.rr_of(e: IsoEntry) -> Maybe<&2, RR.IsoRr>:
  match e:
    case IsoEntry{n, d, s, x, r, rr}:
      rr

# the symbolic link's target (Rock Ridge SL), if the entry is one
def IsoEntry.link(e: IsoEntry) -> Maybe<&2, String>:
  match e:
    case IsoEntry{n, d, s, x, r, Some{RR.IsoRr{px, nm, link, ts, dev, cl, pl, re}}}:
      link
    case IsoEntry{n, d, s, x, r, None{}}:
      None{}

def iso.extent.of(r: R.IsoDirRec) -> IsoExtent:
  match r:
    case R.IsoDirRec{ea, ex, sz, dt, fl, us, gp, vs, id, su}:
      IsoExtent{U32.add(ex, ea), sz}

def iso.extent.total.go(xs: List<&2, IsoExtent>, acc: W.W64) -> W.W64:
  match xs:
    case Nil{}:
      acc
    case Con{IsoExtent{b, s}, t}:
      iso.extent.total.go(t, W.W64.add(acc, W.W64.from_u32(s)))

# the sum of the extents' sizes (a loop: a file may have many extents)
def iso.extent.total(xs: List<&2, IsoExtent>) -> W.W64:
  iso.extent.total.go(xs, W.W64.zero())

def iso.extent.rev(xs: List<&2, IsoExtent>, acc: List<&2, IsoExtent>) -> List<&2, IsoExtent>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      iso.extent.rev(t, Con{h, acc})

# the entry of a directory record
def iso.entry.make(name: String, +r: R.IsoDirRec, +exts: List<&2, IsoExtent>, rr: Maybe<&2, RR.IsoRr>) -> IsoEntry:
  IsoEntry{name, R.IsoDirRec.is_dir(r), iso.extent.total(exts), exts, r, rr}

# the root directory of a volume
def Iso.root(v: V.IsoVolume) -> IsoEntry:
  match v:
    case V.IsoVolume{o, n, p, +root, j, k, b, ds}:
      iso.entry.make("", root, [iso.extent.of(root)], None{})

def iso.name.ver.cut(ok: Bool, +k: Nat, r: String, s: String) -> String:
  match ok:
    case True{}:
      String.reverse(String.drop(r, 1n+k))
    case False{}:
      s

def iso.name.digits.go(dig: Bool, n: Nat) -> Nat:
  match dig:
    case True{}:
      1n+n
    case False{}:
      0n

# Names

# the part of s before its last ';' when only digits follow it (a version)
# the number of digits at the start of r
def iso.name.digits(r: String) -> Nat:
  match r:
    case SNil{}:
      0n
    case SCon{+c, t}:
      iso.name.digits.go(Char.is_digit(c), iso.name.digits(t))

def iso.name.semi(m: Maybe<&2, Char>) -> Bool:
  match m:
    case Some{c}:
      Char.is_eq(c, ';')
    case None{}:
      False{}

def iso.name.version(+s: String) -> String:
  +r = String.reverse(s)
  +k = iso.name.digits(r)
  iso.name.ver.cut(Bool.and(Bool.not(Nat.is_eq(k, 0n)), iso.name.semi(String.get(r, k))), k, r, s)

def iso.name.dot.pick(dot: Bool, c: Char, t: String) -> String:
  match dot:
    case True{}:
      t
    case False{}:
      SCon{c, t}

def iso.name.dot.go(r: String) -> String:
  match r:
    case SCon{Chr{+c}, t}:
      iso.name.dot.pick(U32.is_eq(c, 46), Chr{c}, t)
    case SNil{}:
      SNil{}

# a plain identifier without a trailing '.' (a file with no extension)
def iso.name.dot(s: String) -> String:
  String.reverse(iso.name.dot.go(String.reverse(s)))

def iso.name.strip.dot(plain: Bool, s: String) -> String:
  match plain:
    case True{}:
      iso.name.dot(s)
    case False{}:
      s

def iso.name.strip(strip: Bool, +plain: Bool, s: String) -> String:
  match strip:
    case True{}:
      iso.name.strip.dot(plain, iso.name.version(s))
    case False{}:
      s

def iso.name.plain(+strip: Bool, r: R.IsoDirRec) -> String:
  iso.name.strip(strip, True{}, B.Octets.to_string(R.IsoDirRec.ident_of(r)))

def iso.name.joliet(+strip: Bool, r: R.IsoDirRec) -> Result<&2, &2, F.IsoError, String>:
  Result.map(&2, &2, F.IsoError, String, String, s => iso.name.strip(strip, False{}, s), J.Iso.ucs2_decode(R.IsoDirRec.ident_of(r)))

def iso.name.rr(+strip: Bool, r: R.IsoDirRec, rr: RR.IsoRr) -> String:
  match rr:
    case RR.IsoRr{px, Some{n}, l, ts, dv, cl, pl, re}:
      n
    case RR.IsoRr{px, None{}, l, ts, dv, cl, pl, re}:
      iso.name.plain(strip, r)

# Rock Ridge relocation (RRIP 4.1.5): a CL entry stands for the directory at
# its location; that directory's own RE entry hides it where it was moved to

def iso.rr.child(rr: RR.IsoRr) -> Maybe<&2, U32>:
  match rr:
    case RR.IsoRr{px, n, l, ts, dv, cl, pl, re}:
      cl

def iso.rr.relocated(rr: RR.IsoRr) -> Bool:
  match rr:
    case RR.IsoRr{px, n, l, ts, dv, cl, pl, re}:
      re

def iso.dir.cl.entry(name: String, r: R.IsoDirRec, rr: RR.IsoRr, self: R.IsoDirRec) -> IsoEntry:
  +ex = iso.extent.of(self)
  IsoEntry{name, True{}, iso.extent.total([ex]), [ex], r, Some{rr}}

# the entry for a CL record: the directory at the CL location, whose "\0"
# record gives its extent
def iso.dir.cl(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, d: D, mode: F.IsoEndian, follow: Bool, cl: Maybe<&2, U32>, name: String, +r: R.IsoDirRec, +rr: RR.IsoRr, exts: List<&2, IsoExtent>) -> Result<&2, &2, F.IsoError, Maybe<&2, IsoEntry>>:
  match follow cl:
    case True{} Some{loc}:
      do Result<&2, &2, F.IsoError, Maybe<&2, IsoEntry>>:
        blk : B.Octets <- F.iso.read_sector(~D, ~read_block, d, U32.to_nat(loc))
        self : R.IsoDirRec <- R.IsoDirRec.decode(mode, blk)
        return Some{iso.dir.cl.entry(name, r, rr, self)}
    case _ _:
      Done{Some{iso.entry.make(name, r, exts, Some{rr})}}

def iso.dir.rr.hide(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, hide: Bool, d: D, mode: F.IsoEndian, +follow: Bool, +strip: Bool, +r: R.IsoDirRec, +rr: RR.IsoRr, exts: List<&2, IsoExtent>) -> Result<&2, &2, F.IsoError, Maybe<&2, IsoEntry>>:
  match hide:
    case True{}:
      Done{None{}}
    case False{}:
      iso.dir.cl(~D, ~read_block, d, mode, follow, iso.rr.child(rr), iso.name.rr(strip, r, rr), r, rr, exts)

def iso.dir.rr(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, +d: D, +mode: F.IsoEndian, +fuel: Nat, +skip: Nat, +follow: Bool, +strip: Bool, +r: R.IsoDirRec, exts: List<&2, IsoExtent>) -> Result<&2, &2, F.IsoError, Maybe<&2, IsoEntry>>:
  do Result<&2, &2, F.IsoError, Maybe<&2, IsoEntry>>:
    es : List<&2, S.IsoSuspEntry> <- S.Iso.susp_entries(~D, ~read_block, d, mode, fuel, skip, R.IsoDirRec.system_use_of(r))
    +rr : RR.IsoRr <- RR.Iso.rr_of(mode, es)
    iso.dir.rr.hide(~D, ~read_block, Bool.and(follow, iso.rr.relocated(rr)), d, mode, follow, strip, r, rr, exts)

def iso.dir.entry.go(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, naming: V.IsoNaming, d: D, +mode: F.IsoEndian, fuel: Nat, skip: Nat, follow: Bool, +strip: Bool, +r: R.IsoDirRec, exts: List<&2, IsoExtent>) -> Result<&2, &2, F.IsoError, Maybe<&2, IsoEntry>>:
  match naming:
    case V.IsoNamingRockRidge{}:
      iso.dir.rr(~D, ~read_block, d, mode, fuel, skip, follow, strip, r, exts)
    case V.IsoNamingJoliet{}:
      Result.map(&2, &2, F.IsoError, String, Maybe<&2, IsoEntry>, n => Some{iso.entry.make(n, r, exts, None{})}, iso.name.joliet(strip, r))
    case _:
      Done{Some{iso.entry.make(iso.name.plain(strip, r), r, exts, None{})}}

# the entry of the last record of a file (exts: all its extents)
def iso.dir.entry(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, v: V.IsoVolume, d: D, +r: R.IsoDirRec, exts: List<&2, IsoExtent>) -> Result<&2, &2, F.IsoError, Maybe<&2, IsoEntry>>:
  match v:
    case V.IsoVolume{V.IsoOptions{nm, e, strip, follow, md, mc, mx}, naming, p, root, j, skip, b, ds}:
      iso.dir.entry.go(~D, ~read_block, naming, d, e, mc, skip, follow, strip, r, exts)

def iso.dir.kind.go(dot: Bool, multi: Bool) -> Nat:
  match dot multi:
    case True{} _:
      0n
    case False{} True{}:
      1n
    case False{} False{}:
      2n

# what a record is to the listing: 0 "\0" or "\1" (skipped), 1 part of a
# multi-extent file (more records follow), 2 a file's last record
def iso.dir.kind(+r: R.IsoDirRec) -> Nat:
  iso.dir.kind.go(Bool.or(R.IsoDirRec.is_self(r), R.IsoDirRec.is_parent(r)), R.IsoDirRec.is_multi_extent(r))

# the entry of a file's last record (pending: the extents of the records
# before it, latest first)
def iso.dir.one(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, k: Nat, v: V.IsoVolume, d: D, +r: R.IsoDirRec, pending: List<&2, IsoExtent>) -> Result<&2, &2, F.IsoError, Maybe<&2, IsoEntry>>:
  match k:
    case 2n:
      iso.dir.entry(~D, ~read_block, v, d, r, iso.extent.rev(Con{iso.extent.of(r), pending}, Nil{}))
    case _:
      Done{None{}}

# the extents pending after a record (latest first)
def iso.dir.pending(k: Nat, +r: R.IsoDirRec, pending: List<&2, IsoExtent>) -> List<&2, IsoExtent>:
  match k:
    case 1n:
      Con{iso.extent.of(r), pending}
    case 0n:
      pending
    case _:
      Nil{}

def iso.dir.keep(m: Maybe<&2, IsoEntry>, acc: List<&2, IsoEntry>) -> List<&2, IsoEntry>:
  match m:
    case Some{e}:
      Con{e, acc}
    case None{}:
      acc

def iso.entry.rev(xs: List<&2, IsoEntry>, acc: List<&2, IsoEntry>) -> List<&2, IsoEntry>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      iso.entry.rev(t, Con{h, acc})

# the entries of the records rs, as a loop: m is the entry of the record
# before them (or the first error), acc the entries so far (latest first)
def iso.dir.entries(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, rs: List<&2, R.IsoDirRec>, +v: V.IsoVolume, +d: D, +pending: List<&2, IsoExtent>, m: Result<&2, &2, F.IsoError, Maybe<&2, IsoEntry>>, acc: List<&2, IsoEntry>) -> Result<&2, &2, F.IsoError, List<&2, IsoEntry>>:
  match rs m:
    case _ Fail{e}:
      Fail{e}
    case Nil{} Done{x}:
      Done{iso.entry.rev(iso.dir.keep(x, acc), Nil{})}
    case Con{+r, t} Done{x}:
      +k = iso.dir.kind(r)
      iso.dir.entries(~D, ~read_block, t, v, d, iso.dir.pending(k, r, pending), iso.dir.one(~D, ~read_block, k, v, d, r, pending), iso.dir.keep(x, acc))

def iso.dir.is_dir(ok: Bool, +name: String, r: Result<&2, &2, F.IsoError, List<&2, IsoEntry>>) -> Result<&2, &2, F.IsoError, List<&2, IsoEntry>>:
  match ok:
    case True{}:
      r
    case False{}:
      Fail{F.IsoNotDirectory{name}}

def iso.dir.mode(v: V.IsoVolume) -> F.IsoEndian:
  match v:
    case V.IsoVolume{V.IsoOptions{nm, e, strip, follow, md, mc, mx}, naming, p, root, j, skip, b, ds}:
      e

def iso.dir.space(v: V.IsoVolume) -> Nat:
  U32.to_nat(V.IsoPvd.space_size_of(V.IsoVolume.pvd_of(v)))

def iso.dir.inside(ok: Bool, +blk: U32, r: Result<&2, &2, F.IsoError, List<&2, IsoEntry>>) -> Result<&2, &2, F.IsoError, List<&2, IsoEntry>>:
  match ok:
    case True{}:
      r
    case False{}:
      Fail{F.IsoExtentOutOfRange{blk}}

# the entries of a directory, "\0" and "\1" left out; a directory whose
# extent runs past the volume space is refused
def Iso.list(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, +d: D, +v: V.IsoVolume, dir: IsoEntry) -> Result<&2, &2, F.IsoError, List<&2, IsoEntry>>:
  match dir:
    case IsoEntry{+name, isd, s, Con{IsoExtent{+blk, +sz}, more}, r, rr}:
      iso.dir.is_dir(isd, name, iso.dir.inside(Nat.is_le(Nat.add(U32.to_nat(blk), R.Iso.blocks(sz)), iso.dir.space(v)), blk, Result.bind(&2, &2, F.IsoError, List<&2, R.IsoDirRec>, List<&2, IsoEntry>, Iso.dir_records(~D, ~block_size, ~read_block, d, iso.dir.mode(v), blk, sz), rs => iso.dir.entries(~D, ~read_block, rs, v, d, Nil{}, Done{None{}}, Nil{}))))
    case IsoEntry{+name, isd, s, Nil{}, r, rr}:
      Fail{F.IsoNotDirectory{name}}

# Finding a path

def iso.find.hit(hit: Bool, e: IsoEntry) -> Maybe<&2, IsoEntry>:
  match hit:
    case True{}:
      Some{e}
    case False{}:
      None{}

# the first of es named name (found: the entry before es, if it was)
def iso.find.in(es: List<&2, IsoEntry>, +name: String, found: Maybe<&2, IsoEntry>) -> Result<&2, &2, F.IsoError, IsoEntry>:
  match es found:
    case _ Some{e}:
      Done{e}
    case Nil{} None{}:
      Fail{F.IsoNotFound{name}}
    case Con{+e, t} None{}:
      iso.find.in(t, name, iso.find.hit(String.eq(IsoEntry.name_of(e), name), e))

def iso.find.go(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, cs: List<&2, String>, +d: D, +v: V.IsoVolume, cur: IsoEntry) -> Result<&2, &2, F.IsoError, IsoEntry>:
  match cs:
    case Nil{}:
      Done{cur}
    case Con{+c, t}:
      do Result<&2, &2, F.IsoError, IsoEntry>:
        es : List<&2, IsoEntry> <- Iso.list(~D, ~block_size, ~read_block, d, v, cur)
        next : IsoEntry <- iso.find.in(es, c, None{})
        iso.find.go(~D, ~block_size, ~read_block, t, d, v, next)

def iso.find.parts(s: String) -> List<&2, String>:
  List.filter(~String, ~(x => Bool.not(String.is_empty(x))), String.split(s, '/'))

def iso.find.deep(ok: Bool, r: Result<&2, &2, F.IsoError, IsoEntry>) -> Result<&2, &2, F.IsoError, IsoEntry>:
  match ok:
    case True{}:
      r
    case False{}:
      Fail{F.IsoDepthLimit{}}

def iso.find.max(v: V.IsoVolume) -> Nat:
  match v:
    case V.IsoVolume{V.IsoOptions{nm, e, strip, follow, md, mc, mx}, naming, p, root, j, skip, b, ds}:
      mx

# the entry at a path ("/" separated, from the root; "" or "/" is the root);
# symbolic links are not followed
def Iso.find(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, +d: D, +v: V.IsoVolume, path: String) -> Result<&2, &2, F.IsoError, IsoEntry>:
  +cs = iso.find.parts(path)
  iso.find.deep(Nat.is_le(List.length(&2, String, cs), iso.find.max(v)), iso.find.go(~D, ~block_size, ~read_block, cs, d, v, Iso.root(v)))

# the entries of the directory at a path
def Iso.list_path(~D: Data, ~block_size: D -> Nat, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, +d: D, +v: V.IsoVolume, path: String) -> Result<&2, &2, F.IsoError, List<&2, IsoEntry>>:
  Result.bind(&2, &2, F.IsoError, IsoEntry, List<&2, IsoEntry>, Iso.find(~D, ~block_size, ~read_block, d, v, path), e => Iso.list(~D, ~block_size, ~read_block, d, v, e))
