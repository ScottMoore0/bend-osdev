# bend-osdev-iso9660, rockridge.bend: the Rock Ridge Interchange Protocol
# (IEEE P1282, "RRIP", version 1.12, 1994), carried in SUSP entries
# (susp.bend). The entries read here:
#   PX  POSIX file attributes: mode, links, uid, gid (both-endian 32 each),
#       and in RRIP 1.12 the file serial number
#   PN  a device's number (high and low, both-endian 32)
#   SL  a symbolic link: a flags byte (bit 0: continues in the next SL), then
#       component records (flags: bit 0 continues in the next component,
#       1 ".", 2 "..", 3 the root; a length; the bytes)
#   NM  an alternate name: a flags byte (bit 0 continues in the next NM,
#       1 ".", 2 ".."), then bytes
#   CL  child link: where a relocated directory really is (both-endian 32)
#   PL  parent link: the real parent of a relocated directory
#   RE  this directory was relocated (its real place has a CL entry)
#   TF  time stamps: a flags byte (bits 0 to 6: creation, modify, access,
#       attributes, backup, expiration, effective; bit 7: 17-byte form),
#       then a 7- or 17-byte date for each bit set, in that order
# RRIP's identifier in an ER entry is "RRIP_1991A" (1.10 and 1.12), or
# "IEEE_P1282" / "IEEE_1282" (later drafts).
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ./fields.bend as F
import ./susp.bend as S

type IsoPx is Data:
  IsoPx{mode: U32, links: U32, uid: U32, gid: U32, serial: Maybe<&2, U32>}

type IsoPn is Data:
  IsoPn{high: U32, low: U32}

# a time stamp: which one (0 creation, 1 modify, 2 access, 3 attributes,
# 4 backup, 5 expiration, 6 effective), whether it is in the 17-byte form,
# and its bytes
type IsoRrStamp is Data:
  IsoRrStamp{kind: Nat, long: Bool, raw: B.Octets}

# a symbolic link component: its flags and bytes
type IsoSlComp is Data:
  IsoSlComp{flags: U32, text: List<&2, U32>}

# what the Rock Ridge entries of a record say
type IsoRr is Data:
  IsoRr{px: Maybe<&2, IsoPx>, name: Maybe<&2, String>, link: Maybe<&2, String>, stamps: List<&2, IsoRrStamp>, dev: Maybe<&2, IsoPn>, child: Maybe<&2, U32>, parent: Maybe<&2, U32>, relocated: Bool}

# the accumulator while reading entries: name bytes and link components
type IsoRrAcc is Data:
  IsoRrAcc{px: Maybe<&2, IsoPx>, name: Maybe<&2, List<&2, U32>>, link: Maybe<&2, List<&2, IsoSlComp>>, stamps: List<&2, IsoRrStamp>, dev: Maybe<&2, IsoPn>, child: Maybe<&2, U32>, parent: Maybe<&2, U32>, relocated: Bool}

def IsoRr.empty() -> IsoRr:
  IsoRr{None{}, None{}, None{}, Nil{}, None{}, None{}, None{}, False{}}

def iso.rr.acc0() -> IsoRrAcc:
  IsoRrAcc{None{}, None{}, None{}, Nil{}, None{}, None{}, None{}, False{}}

def iso.rr.bad(-A: Data, sig: String, r: Result<&2, &2, F.IsoError, A>) -> Result<&2, &2, F.IsoError, A>:
  match r:
    case Fail{F.IsoTruncated{}}:
      Fail{F.IsoBadRrip{sig}}
    case _:
      r

# PX

def iso.rr.serial(r: Result<&2, &2, F.IsoError, U32>) -> Maybe<&2, U32>:
  match r:
    case Done{v}:
      Some{v}
    case Fail{e}:
      None{}

def iso.rr.px(+mode: F.IsoEndian, +xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, IsoPx>:
  do Result<&2, &2, F.IsoError, IsoPx>:
    m : U32 <- F.iso.both32.list(mode, xs, 4n)
    l : U32 <- F.iso.both32.list(mode, B.drop(8n, xs), 12n)
    u : U32 <- F.iso.both32.list(mode, B.drop(16n, xs), 20n)
    g : U32 <- F.iso.both32.list(mode, B.drop(24n, xs), 28n)
    return IsoPx{m, l, u, g, iso.rr.serial(F.iso.both32.list(mode, B.drop(32n, xs), 36n))}

def iso.rr.pn(+mode: F.IsoEndian, +xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, IsoPn>:
  do Result<&2, &2, F.IsoError, IsoPn>:
    h : U32 <- F.iso.both32.list(mode, xs, 4n)
    l : U32 <- F.iso.both32.list(mode, B.drop(8n, xs), 12n)
    return IsoPn{h, l}

def iso.rr.tf.adv(set: Bool, size: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match set:
    case True{}:
      B.drop(size, xs)
    case False{}:
      xs

def iso.rr.tf.keep(ok: Bool, s: IsoRrStamp, rest: Result<&2, &2, F.IsoError, List<&2, IsoRrStamp>>) -> Result<&2, &2, F.IsoError, List<&2, IsoRrStamp>>:
  match ok:
    case True{}:
      Result.map(&2, &2, F.IsoError, List<&2, IsoRrStamp>, List<&2, IsoRrStamp>, t => Con{s, t}, rest)
    case False{}:
      Fail{F.IsoBadRrip{"TF"}}

def iso.rr.tf.pick(set: Bool, +bit: Nat, long: Bool, +size: Nat, xs: List<&2, U32>, rest: Result<&2, &2, F.IsoError, List<&2, IsoRrStamp>>) -> Result<&2, &2, F.IsoError, List<&2, IsoRrStamp>>:
  match set:
    case True{}:
      +raw = B.take(size, xs)
      iso.rr.tf.keep(Nat.is_eq(B.len(raw), size), IsoRrStamp{bit, long, B.Octets.of_list(raw)}, rest)
    case False{}:
      rest

# TF: one stamp for each of the seven bits set, in order

def iso.rr.tf.go(k: Nat, +bit: Nat, +flags: U32, +long: Bool, +size: Nat, xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, List<&2, IsoRrStamp>>:
  match k:
    case 0n:
      Done{Nil{}}
    case 1n+p:
      +set = Bool.not(U32.is_eq(U32.and(flags, U32.shln(1, bit)), 0))
      +ys = xs
      iso.rr.tf.pick(set, bit, long, size, ys, iso.rr.tf.go(p, 1n+bit, flags, long, size, iso.rr.tf.adv(set, size, ys)))

def iso.rr.tf.size(long: Bool) -> Nat:
  match long:
    case True{}:
      17n
    case False{}:
      7n

def iso.rr.tf(xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, List<&2, IsoRrStamp>>:
  match xs:
    case Con{+flags, t}:
      +long = Bool.not(U32.is_eq(U32.and(flags, 128), 0))
      iso.rr.tf.go(7n, 0n, flags, long, iso.rr.tf.size(long), t)
    case Nil{}:
      Fail{F.IsoBadRrip{"TF"}}

def iso.rr.sl.keep(ok: Bool, c: IsoSlComp, rest: Result<&2, &2, F.IsoError, List<&2, IsoSlComp>>) -> Result<&2, &2, F.IsoError, List<&2, IsoSlComp>>:
  match ok:
    case True{}:
      Result.map(&2, &2, F.IsoError, List<&2, IsoSlComp>, List<&2, IsoSlComp>, t => Con{c, t}, rest)
    case False{}:
      Fail{F.IsoBadRrip{"SL"}}

# SL: the component records of one entry

def iso.rr.sl.comps(fuel: Nat, xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, List<&2, IsoSlComp>>:
  match fuel:
    case 0n:
      Done{Nil{}}
    case 1n+f:
      match xs:
        case Nil{}:
          Done{Nil{}}
        case Con{fl, Con{+l, +t}}:
          +n = U32.to_nat(l)
          +txt = B.take(n, t)
          iso.rr.sl.keep(Nat.is_eq(B.len(txt), n), IsoSlComp{fl, txt}, iso.rr.sl.comps(f, B.drop(n, t)))
        case Con{fl, Nil{}}:
          Fail{F.IsoBadRrip{"SL"}}

def iso.rr.sl(xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, List<&2, IsoSlComp>>:
  match xs:
    case Con{flags, +t}:
      iso.rr.sl.comps(B.len(t), t)
    case Nil{}:
      Fail{F.IsoBadRrip{"SL"}}

def iso.bit8(+fl: U32, m: U32) -> Bool:
  Bool.not(U32.is_eq(U32.and(m, fl), 0))

def iso.rr.sl.sep(sep: Bool) -> String:
  match sep:
    case True{}:
      "/"
    case False{}:
      ""

def iso.rr.sl.one(root: Bool, cur: Bool, par: Bool, sep: Bool, txt: List<&2, U32>) -> String:
  match root cur par:
    case True{} _ _:
      "/"
    case False{} True{} _:
      iso.rr.sl.sep(sep) ++ "."
    case False{} False{} True{}:
      iso.rr.sl.sep(sep) ++ ".."
    case False{} False{} False{}:
      iso.rr.sl.sep(sep) ++ B.to_string(txt)

# the text of a link from its components: "/" for the root, "." and "..",
# components joined with "/" unless a component continues in the next
def iso.rr.sl.text(cs: List<&2, IsoSlComp>, sep: Bool) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{IsoSlComp{+fl, txt}, t}:
      iso.rr.sl.one(iso.bit8(fl, 8), iso.bit8(fl, 2), iso.bit8(fl, 4), sep, txt) ++ iso.rr.sl.text(t, Bool.and(Bool.not(iso.bit8(fl, 8)), Bool.not(iso.bit8(fl, 1))))

# a link's text from its components
def Iso.rr_link_text(cs: List<&2, IsoSlComp>) -> String:
  iso.rr.sl.text(cs, False{})

def iso.rr.nm.pick(cur: Bool, par: Bool, t: List<&2, U32>) -> Result<&2, &2, F.IsoError, List<&2, U32>>:
  match cur par:
    case True{} _:
      Done{[46]}
    case False{} True{}:
      Done{[46, 46]}
    case False{} False{}:
      Done{t}

# NM: the name's bytes ("." and ".." for the flags that say so)

def iso.rr.nm(xs: List<&2, U32>) -> Result<&2, &2, F.IsoError, List<&2, U32>>:
  match xs:
    case Con{+fl, t}:
      iso.rr.nm.pick(iso.bit8(fl, 2), iso.bit8(fl, 4), t)
    case Nil{}:
      Fail{F.IsoBadRrip{"NM"}}

# Folding the entries of a record into what they say

def iso.rr.join(-A: Data, m: Maybe<&2, List<&2, A>>, more: List<&2, A>) -> Maybe<&2, List<&2, A>>:
  match m:
    case None{}:
      Some{more}
    case Some{xs}:
      Some{List.append(&2, A, xs, more)}

def iso.rr.set_px(a: IsoRrAcc, r: Result<&2, &2, F.IsoError, IsoPx>) -> Result<&2, &2, F.IsoError, IsoRrAcc>:
  match a r:
    case IsoRrAcc{p, n, l, s, d, c, pa, re} Done{x}:
      Done{IsoRrAcc{Some{x}, n, l, s, d, c, pa, re}}
    case _ Fail{e}:
      Fail{e}

def iso.rr.set_pn(a: IsoRrAcc, r: Result<&2, &2, F.IsoError, IsoPn>) -> Result<&2, &2, F.IsoError, IsoRrAcc>:
  match a r:
    case IsoRrAcc{p, n, l, s, d, c, pa, re} Done{x}:
      Done{IsoRrAcc{p, n, l, s, Some{x}, c, pa, re}}
    case _ Fail{e}:
      Fail{e}

def iso.rr.add_nm(a: IsoRrAcc, r: Result<&2, &2, F.IsoError, List<&2, U32>>) -> Result<&2, &2, F.IsoError, IsoRrAcc>:
  match a r:
    case IsoRrAcc{p, n, l, s, d, c, pa, re} Done{x}:
      Done{IsoRrAcc{p, iso.rr.join(U32, n, x), l, s, d, c, pa, re}}
    case _ Fail{e}:
      Fail{e}

def iso.rr.add_sl(a: IsoRrAcc, r: Result<&2, &2, F.IsoError, List<&2, IsoSlComp>>) -> Result<&2, &2, F.IsoError, IsoRrAcc>:
  match a r:
    case IsoRrAcc{p, n, l, s, d, c, pa, re} Done{x}:
      Done{IsoRrAcc{p, n, iso.rr.join(IsoSlComp, l, x), s, d, c, pa, re}}
    case _ Fail{e}:
      Fail{e}

def iso.rr.add_tf(a: IsoRrAcc, r: Result<&2, &2, F.IsoError, List<&2, IsoRrStamp>>) -> Result<&2, &2, F.IsoError, IsoRrAcc>:
  match a r:
    case IsoRrAcc{p, n, l, s, d, c, pa, re} Done{x}:
      Done{IsoRrAcc{p, n, l, List.append(&2, IsoRrStamp, s, x), d, c, pa, re}}
    case _ Fail{e}:
      Fail{e}

def iso.rr.set_cl(a: IsoRrAcc, r: Result<&2, &2, F.IsoError, U32>) -> Result<&2, &2, F.IsoError, IsoRrAcc>:
  match a r:
    case IsoRrAcc{p, n, l, s, d, c, pa, re} Done{x}:
      Done{IsoRrAcc{p, n, l, s, d, Some{x}, pa, re}}
    case _ Fail{e}:
      Fail{e}

def iso.rr.set_pl(a: IsoRrAcc, r: Result<&2, &2, F.IsoError, U32>) -> Result<&2, &2, F.IsoError, IsoRrAcc>:
  match a r:
    case IsoRrAcc{p, n, l, s, d, c, pa, re} Done{x}:
      Done{IsoRrAcc{p, n, l, s, d, c, Some{x}, re}}
    case _ Fail{e}:
      Fail{e}

def iso.rr.set_re(a: IsoRrAcc) -> Result<&2, &2, F.IsoError, IsoRrAcc>:
  match a:
    case IsoRrAcc{p, n, l, s, d, c, pa, re}:
      Done{IsoRrAcc{p, n, l, s, d, c, pa, True{}}}

# the signature of an entry, as a number (first byte * 256 + second)
def iso.rr.code(e: S.IsoSuspEntry) -> U32:
  match e:
    case S.IsoSuspEntry{a, b, v, d}:
      U32.add(U32.shln(a, 8n), b)

def iso.rr.which.go(px: Bool, pn: Bool, sl: Bool, nm: Bool, cl: Bool, pl: Bool, re: Bool, tf: Bool) -> Nat:
  match px pn sl nm cl pl re tf:
    case True{} _ _ _ _ _ _ _:
      1n
    case False{} True{} _ _ _ _ _ _:
      2n
    case False{} False{} True{} _ _ _ _ _:
      3n
    case False{} False{} False{} True{} _ _ _ _:
      4n
    case False{} False{} False{} False{} True{} _ _ _:
      5n
    case False{} False{} False{} False{} False{} True{} _ _:
      6n
    case False{} False{} False{} False{} False{} False{} True{} _:
      7n
    case False{} False{} False{} False{} False{} False{} False{} True{}:
      8n
    case False{} False{} False{} False{} False{} False{} False{} False{}:
      0n

# 1 PX, 2 PN, 3 SL, 4 NM, 5 CL, 6 PL, 7 RE, 8 TF, 0 anything else
def iso.rr.which(+c: U32) -> Nat:
  iso.rr.which.go(U32.is_eq(c, 20568), U32.is_eq(c, 20558), U32.is_eq(c, 21324), U32.is_eq(c, 20045), U32.is_eq(c, 17228), U32.is_eq(c, 20556), U32.is_eq(c, 21061), U32.is_eq(c, 21574))

def iso.rr.dispatch.go(k: Nat, +mode: F.IsoEndian, +xs: List<&2, U32>, a: IsoRrAcc) -> Result<&2, &2, F.IsoError, IsoRrAcc>:
  match k:
    case 1n:
      iso.rr.set_px(a, iso.rr.bad(IsoPx, "PX", iso.rr.px(mode, xs)))
    case 2n:
      iso.rr.set_pn(a, iso.rr.bad(IsoPn, "PN", iso.rr.pn(mode, xs)))
    case 3n:
      iso.rr.add_sl(a, iso.rr.sl(xs))
    case 4n:
      iso.rr.add_nm(a, iso.rr.nm(xs))
    case 5n:
      iso.rr.set_cl(a, iso.rr.bad(U32, "CL", F.iso.both32.list(mode, xs, 4n)))
    case 6n:
      iso.rr.set_pl(a, iso.rr.bad(U32, "PL", F.iso.both32.list(mode, xs, 4n)))
    case 7n:
      iso.rr.set_re(a)
    case 8n:
      iso.rr.add_tf(a, iso.rr.tf(xs))
    case _:
      Done{a}

def iso.rr.dispatch(+mode: F.IsoEndian, +code: U32, +xs: List<&2, U32>, a: IsoRrAcc) -> Result<&2, &2, F.IsoError, IsoRrAcc>:
  iso.rr.dispatch.go(iso.rr.which(code), mode, xs, a)

def iso.rr.add(+mode: F.IsoEndian, +e: S.IsoSuspEntry, a: IsoRrAcc) -> Result<&2, &2, F.IsoError, IsoRrAcc>:
  iso.rr.dispatch(mode, iso.rr.code(e), B.Octets.to_list(S.IsoSuspEntry.data_of(e)), a)

def iso.rr.fold(+mode: F.IsoEndian, es: List<&2, S.IsoSuspEntry>, r: Result<&2, &2, F.IsoError, IsoRrAcc>) -> Result<&2, &2, F.IsoError, IsoRrAcc>:
  match es:
    case Nil{}:
      r
    case Con{e, t}:
      iso.rr.fold(mode, t, Result.bind(&2, &2, F.IsoError, IsoRrAcc, IsoRrAcc, r, a => iso.rr.add(mode, e, a)))

def iso.rr.text(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, String>:
  match m:
    case Some{xs}:
      Some{B.to_string(xs)}
    case None{}:
      None{}

def iso.rr.link(m: Maybe<&2, List<&2, IsoSlComp>>) -> Maybe<&2, String>:
  match m:
    case Some{cs}:
      Some{Iso.rr_link_text(cs)}
    case None{}:
      None{}

def iso.rr.finish(a: IsoRrAcc) -> IsoRr:
  match a:
    case IsoRrAcc{p, n, l, s, d, c, pa, re}:
      IsoRr{p, iso.rr.text(n), iso.rr.link(l), s, d, c, pa, re}

# what a record's SUSP entries (continuations included) say in Rock Ridge
def Iso.rr_of(mode: F.IsoEndian, es: List<&2, S.IsoSuspEntry>) -> Result<&2, &2, F.IsoError, IsoRr>:
  Result.map(&2, &2, F.IsoError, IsoRrAcc, IsoRr, iso.rr.finish, iso.rr.fold(mode, es, Done{iso.rr.acc0()}))

# Telling whether a volume has Rock Ridge, from the entries of its root's
# "\0" record: an ER entry with an RRIP identifier, or an RR or PX entry

def iso.rr.er_is_rrip(r: Result<&2, &2, F.IsoError, S.IsoEr>) -> Bool:
  match r:
    case Done{S.IsoEr{+id, d, s, v}}:
      Bool.or(String.eq(id, "RRIP_1991A"), Bool.or(String.eq(id, "IEEE_P1282"), String.eq(id, "IEEE_1282")))
    case Fail{e}:
      False{}

def iso.rr.marks.er(er: Bool, e: S.IsoSuspEntry) -> Bool:
  match er:
    case True{}:
      iso.rr.er_is_rrip(S.IsoSuspEntry.er(e))
    case False{}:
      False{}

def iso.rr.marks(+e: S.IsoSuspEntry) -> Bool:
  Bool.or(S.IsoSuspEntry.is(e, 82, 82), Bool.or(S.IsoSuspEntry.is(e, 80, 88), iso.rr.marks.er(S.IsoSuspEntry.is(e, 69, 82), e)))

def Iso.rr_present(es: List<&2, S.IsoSuspEntry>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{e, t}:
      Bool.or(iso.rr.marks(e), Iso.rr_present(t))

# the file type bits of a PX mode (S_IFMT)
def IsoPx.is_dir(p: IsoPx) -> Bool:
  match p:
    case IsoPx{m, l, u, g, s}:
      U32.is_eq(U32.and(61440, m), 16384)

def IsoPx.is_link(p: IsoPx) -> Bool:
  match p:
    case IsoPx{m, l, u, g, s}:
      U32.is_eq(U32.and(61440, m), 40960)

def IsoRr.name_of(r: IsoRr) -> Maybe<&2, String>:
  match r:
    case IsoRr{px, n, l, s, d, c, pa, re}:
      n

def IsoRr.link_of(r: IsoRr) -> Maybe<&2, String>:
  match r:
    case IsoRr{px, n, l, s, d, c, pa, re}:
      l
