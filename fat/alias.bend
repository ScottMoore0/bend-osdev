# bend-osdev-fat, alias.bend: names for new directory entries. Checking a
# long name, and the short name (an 8.3 alias with a numeric tail when it
# needs one) and long-name entries stored for it.
#
# Microsoft, "FAT: General Overview of On-Disk Format" (version 1.03, 2000),
# section 6.1 (the characters a short name may hold) and section 7 (long
# names: their characters; leading and trailing spaces and trailing periods
# are ignored; the basis-name generation algorithm and the numeric-tail
# generation algorithm).
#
# The basis name of a long name: its characters upper-cased (ASCII letters);
# a character a short name cannot hold (or outside ASCII: no OEM code page
# is assumed) replaced by '_', which makes the conversion lossy; every space
# and the leading periods removed; then up to 8 characters before the first
# period as the base, and up to 3 after the last period as the extension.
# The basis name is the short name as it is when the conversion was not
# lossy, the long name is itself a valid 8.3 name, and no entry of the
# directory has that short name. Otherwise "~n" goes at the end of the base
# (the base cut so it stays within 8 characters), with n the smallest from 1
# that gives a short name no entry has.
#
# A long-name entry run (dirent.bend's FatLfn.build) is stored unless the
# short name alone shows the name: the name is its own 8.3 form in upper
# case, or (FatWOptions.nt_case) its base and its extension are each all in
# one case, which Windows NT's DIR_NTRes flags record.
#
# The public interface is listed in README.md; everything else is internal.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./bpb.bend as P
import ./dirent.bend as R

# Checking a long name

# a character a long name may hold: not a control character, and none of
# " * / : < > ? \ |
def FatAlias.long_char(+c: U32) -> Bool:
  Bool.and(U32.is_ge(c, 32), Bool.not(P.Fat.u32_in(c, [34, 42, 47, 58, 60, 62, 63, 92, 124])))

def FatAlias.all_long(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(FatAlias.long_char(h), FatAlias.all_long(t))

def FatAlias.keep(keep: Bool, h: U32, r: List<&2, U32>) -> List<&2, U32>:
  match keep:
    case True{}:
      Con{h, r}
    case False{}:
      r

# xs without its leading characters equal to a or b (started: once one
# that is neither has been seen)
def FatAlias.drop_lead(xs: List<&2, U32>, +a: U32, +b: U32, started: Bool) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      +go = Bool.or(started, Bool.not(Bool.or(U32.is_eq(h, a), U32.is_eq(h, b))))
      FatAlias.keep(go, h, FatAlias.drop_lead(t, a, b, go))

def FatAlias.rev(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      FatAlias.rev(t, Con{h, acc})

# a name as it is stored: its leading spaces, and its trailing spaces and
# periods, removed (section 7: they are ignored)
def FatAlias.trim(xs: List<&2, U32>) -> List<&2, U32>:
  FatAlias.rev(FatAlias.drop_lead(FatAlias.rev(FatAlias.drop_lead(xs, 32, 32, False{}), Nil{}), 32, 46, False{}), Nil{})

def FatAlias.check.go(ok: Bool, xs: List<&2, U32>) -> Result<&2, &2, E.FatError, List<&2, U32>>:
  match ok:
    case True{}:
      Done{xs}
    case False{}:
      Fail{E.FatBadName{}}

def FatAlias.codes(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      Con{Char.to_u32(c), FatAlias.codes(t)}

def FatAlias.text(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      SCon{Char.from_u32(h), FatAlias.text(t)}

# a path component as the name stored for it (trimmed), or FatBadName: empty
# once trimmed, a character a long name cannot hold, or more than 255 UCS-2
# units
def FatAlias.check(s: String) -> Result<&2, &2, E.FatError, String>:
  +xs = FatAlias.trim(FatAlias.codes(s))
  +n = B.len(R.FatName.units(FatAlias.text(xs)))
  Result.map(&2, &2, E.FatError, List<&2, U32>, String, FatAlias.text, FatAlias.check.go(Bool.and(Bool.and(Nat.is_lt(0n, n), Nat.is_le(n, 255n)), FatAlias.all_long(xs)), xs))

# The basis name

# a character of the basis name, and whether it was lossy: '.' and ' ' kept
# (the steps after use them), others upper-cased, and '_' for one a short
# name cannot hold
type FatBasisChar is Data:
  FatBasisChar{c: U32, lossy: Bool}

def FatAlias.oem.pick(keep: Bool, +u: U32) -> FatBasisChar:
  match keep:
    case True{}:
      FatBasisChar{u, False{}}
    case False{}:
      FatBasisChar{95, True{}}

def FatAlias.oem(+c: U32) -> FatBasisChar:
  +u = R.FatName.upper(c)
  FatAlias.oem.pick(Bool.or(Bool.or(U32.is_eq(u, 32), U32.is_eq(u, 46)), R.FatName.short_char(u)), u)

type FatBasis is Data:
  FatBasis{base: List<&2, U32>, ext: List<&2, U32>, lossy: Bool}

def FatBasisChar.c(b: FatBasisChar) -> U32:
  match b:
    case FatBasisChar{c, l}:
      c

def FatBasisChar.lossy(b: FatBasisChar) -> Bool:
  match b:
    case FatBasisChar{c, l}:
      l

# the characters converted (reversed onto acc), and whether any was lossy
def FatAlias.convert(xs: List<&2, U32>, acc: List<&2, U32>, lossy: Bool) -> FatBasis:
  match xs:
    case Nil{}:
      FatBasis{FatAlias.rev(acc, Nil{}), Nil{}, lossy}
    case Con{h, t}:
      +b = FatAlias.oem(h)
      FatAlias.convert(t, Con{FatBasisChar.c(b), acc}, Bool.or(lossy, FatBasisChar.lossy(b)))

# xs without the characters equal to a
def FatAlias.without(xs: List<&2, U32>, +a: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      FatAlias.keep(Bool.not(U32.is_eq(h, a)), h, FatAlias.without(t, a))

def FatAlias.cut_at(dot: Bool, h: U32, r: List<&2, U32>) -> List<&2, U32>:
  match dot:
    case True{}:
      Nil{}
    case False{}:
      Con{h, r}

# the characters before the first period
def FatAlias.before_dot(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      FatAlias.cut_at(U32.is_eq(h, 46), h, FatAlias.before_dot(t))

def FatAlias.after_dot.fin(seen: Bool, cur: List<&2, U32>) -> List<&2, U32>:
  match seen:
    case True{}:
      FatAlias.rev(cur, Nil{})
    case False{}:
      Nil{}

def FatAlias.after_dot.cur(dot: Bool, h: U32, cur: List<&2, U32>) -> List<&2, U32>:
  match dot:
    case True{}:
      Nil{}
    case False{}:
      Con{h, cur}

# the characters after the last period (none when there is no period; cur:
# those after the last period so far, reversed)
def FatAlias.after_dot(xs: List<&2, U32>, cur: List<&2, U32>, seen: Bool) -> List<&2, U32>:
  match xs:
    case Nil{}:
      FatAlias.after_dot.fin(seen, cur)
    case Con{+h, t}:
      +dot = U32.is_eq(h, 46)
      FatAlias.after_dot(t, FatAlias.after_dot.cur(dot, h, cur), Bool.or(seen, dot))

def FatAlias.basis.fin(b: FatBasis) -> FatBasis:
  match b:
    case FatBasis{+cs, e, lossy}:
      +s = FatAlias.drop_lead(FatAlias.without(cs, 32), 46, 46, False{})
      FatBasis{B.take(8n, FatAlias.before_dot(s)), B.take(3n, FatAlias.after_dot(s, Nil{}, False{})), lossy}

# the basis name of a long name (its code points): a base of at most 8 and
# an extension of at most 3 characters, and whether it was lossy
def FatAlias.basis(xs: List<&2, U32>) -> FatBasis:
  FatAlias.basis.fin(FatAlias.convert(xs, Nil{}, False{}))

# The numeric tail

def FatAlias.taken(+s: B.Octets, xs: List<&2, B.Octets>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(B.Octets.is_eq(s, h), FatAlias.taken(s, t))

# the 11 bytes of a base and an extension, each padded with spaces
def FatAlias.name11(base: List<&2, U32>, ext: List<&2, U32>) -> B.Octets:
  B.Octets.of_list(B.append(P.Fat.fit(8n, 32, base), P.Fat.fit(3n, 32, ext)))

# the short name with tail "~n": the base cut so the whole stays within 8
def FatAlias.with_tail(+base: List<&2, U32>, +ext: List<&2, U32>, +n: Nat) -> B.Octets:
  +tail = {Con{126, FatAlias.codes(Nat.show(n))} : List<&2, U32>}
  FatAlias.name11(B.append(B.take(Nat.sub(8n, B.len(tail)), base), tail), ext)

# the first tail from n on whose name is not taken, in at most fuel tries
def FatAlias.tail.go(fuel: Nat, +base: List<&2, U32>, +ext: List<&2, U32>, +taken: List<&2, B.Octets>, +n: Nat, +cand: B.Octets, used: Bool) -> Result<&2, &2, E.FatError, B.Octets>:
  match fuel used:
    case _ False{}:
      Done{cand}
    case 0n True{}:
      Fail{E.FatNoAlias{}}
    case 1n+f True{}:
      +n2 = Nat.add(n, 1n)
      +c2 = FatAlias.with_tail(base, ext, n2)
      FatAlias.tail.go(f, base, ext, taken, n2, c2, FatAlias.taken(c2, taken))

# Where the search starts: the smallest n from 1 that no taken name's tail
# is (a taken name counts when it is exactly the name with that tail), so a
# directory of many names with one basis costs one pass over its names, not
# one a tail tried

def FatAlias.last_tilde.pick(t: Bool, +i: Nat, at: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match t:
    case True{}:
      Some{i}
    case False{}:
      at

# the position of the last '~' in xs
def FatAlias.last_tilde(xs: List<&2, U32>, +i: Nat, at: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      at
    case Con{+h, t}:
      FatAlias.last_tilde(t, Nat.add(i, 1n), FatAlias.last_tilde.pick(U32.is_eq(h, 126), i, at))

def FatAlias.digits.end(any: Bool, +acc: Nat) -> Maybe<&2, Nat>:
  match any:
    case True{}:
      Some{acc}
    case False{}:
      None{}

def FatAlias.digits.stop(digit: Bool, space: Bool, any: Bool, +acc: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match digit space:
    case True{} _:
      rest
    case False{} True{}:
      FatAlias.digits.end(any, acc)
    case False{} False{}:
      None{}

# the number the digits of xs give, up to a space or their end (None for
# anything else, or no digit)
def FatAlias.digits(xs: List<&2, U32>, +acc: Nat, any: Bool) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      FatAlias.digits.end(any, acc)
    case Con{+h, t}:
      +digit = Bool.and(U32.is_ge(h, 48), U32.is_le(h, 57))
      FatAlias.digits.stop(digit, U32.is_eq(h, 32), any, acc, FatAlias.digits(t, Nat.add(Nat.mul(acc, 10n), U32.to_nat(U32.sub(h, 48))), True{}))

def FatAlias.tail_of.check(ok: Bool, +n: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{n}
    case False{}:
      None{}

def FatAlias.tail_of.num(m: Maybe<&2, Nat>, +base: List<&2, U32>, +ext: List<&2, U32>, +s: B.Octets) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{+n}:
      FatAlias.tail_of.check(B.Octets.is_eq(FatAlias.with_tail(base, ext, n), s), n)

def FatAlias.tail_of.at(m: Maybe<&2, Nat>, +xs: List<&2, U32>, +base: List<&2, U32>, +ext: List<&2, U32>, +s: B.Octets) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{i}:
      FatAlias.tail_of.num(FatAlias.digits(B.drop(Nat.add(i, 1n), xs), 0n, False{}), base, ext, s)

# n when s is the short name with tail ~n
def FatAlias.tail_of(+base: List<&2, U32>, +ext: List<&2, U32>, +s: B.Octets) -> Maybe<&2, Nat>:
  +xs = B.take(8n, B.Octets.to_list(s))
  FatAlias.tail_of.at(FatAlias.last_tilde(xs, 0n, None{}), xs, base, ext, s)

def FatAlias.tails.put(m: Maybe<&2, Nat>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case None{}:
      acc
    case Some{n}:
      Con{n, acc}

# the tails the taken names have
def FatAlias.tails(xs: List<&2, B.Octets>, +base: List<&2, U32>, +ext: List<&2, U32>, acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case Con{+s, t}:
      FatAlias.tails(t, base, ext, FatAlias.tails.put(FatAlias.tail_of(base, ext, s), acc))

def FatAlias.mex.pick(c: Cmp, +e: Nat, rest: Nat) -> Nat:
  match c:
    case EQ{}:
      rest
    case LT{}:
      rest
    case GT{}:
      e

def FatAlias.mex.next(c: Cmp, +e: Nat) -> Nat:
  match c:
    case EQ{}:
      Nat.add(e, 1n)
    case _:
      e

# the smallest number from e on missing from a sorted list
def FatAlias.mex(xs: List<&2, Nat>, +e: Nat) -> Nat:
  match xs:
    case Nil{}:
      e
    case Con{+h, t}:
      +c = Nat.cmp(h, e)
      FatAlias.mex.pick(c, e, FatAlias.mex(t, FatAlias.mex.next(c, e)))

def FatAlias.first_tail(+base: List<&2, U32>, +ext: List<&2, U32>, +taken: List<&2, B.Octets>) -> Nat:
  FatAlias.mex(List.sort(~Nat, ~Nat.is_le, FatAlias.tails(taken, base, ext, Nil{})), 1n)

# the first tail whose name is not taken (the search from first_tail on, so
# a name it misses is still checked)
def FatAlias.tail(+base: List<&2, U32>, +ext: List<&2, U32>, +taken: List<&2, B.Octets>) -> Result<&2, &2, E.FatError, B.Octets>:
  +n = FatAlias.first_tail(base, ext, taken)
  +c = FatAlias.with_tail(base, ext, n)
  FatAlias.tail.go(999998n, base, ext, taken, n, c, FatAlias.taken(c, taken))

# What is stored for a new name: its short name, its DIR_NTRes case flags,
# and its long name's UCS-2 units (none when the short name alone shows it)
type FatAlias is Data:
  FatAlias{short: B.Octets, nt: U32, long: List<&2, U32>}

def FatAlias.short(a: FatAlias) -> B.Octets:
  match a:
    case FatAlias{s, nt, l}:
      s

def FatAlias.nt(a: FatAlias) -> U32:
  match a:
    case FatAlias{s, nt, l}:
      nt

def FatAlias.long(a: FatAlias) -> List<&2, U32>:
  match a:
    case FatAlias{s, nt, l}:
      l

# Case: whether a part has upper-case or lower-case ASCII letters

def FatAlias.has_lower(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+h, t}:
      Bool.or(Bool.and(U32.is_ge(h, 97), U32.is_le(h, 122)), FatAlias.has_lower(t))

def FatAlias.has_upper(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+h, t}:
      Bool.or(Bool.and(U32.is_ge(h, 65), U32.is_le(h, 90)), FatAlias.has_upper(t))

# the base and extension of a valid 8.3 name (the text before and after its
# one period)
def FatAlias.split83(+xs: List<&2, U32>) -> FatBasis:
  FatBasis{FatAlias.before_dot(xs), FatAlias.after_dot(xs, Nil{}, False{}), False{}}

def FatAlias.flag(+part: List<&2, U32>, +bit: U32) -> U32:
  U32.mul(Bool.to_u32(FatAlias.has_lower(part)), bit)

def FatAlias.mixed(+part: List<&2, U32>) -> Bool:
  Bool.and(FatAlias.has_lower(part), FatAlias.has_upper(part))

def FatAlias.case.nt(mixed: Bool, flags: U32) -> Maybe<&2, U32>:
  match mixed:
    case True{}:
      None{}
    case False{}:
      Some{flags}

# the case flags for a name its 8.3 form shows (nt_case: lower-case parts
# flagged), or None when a long name must be stored
def FatAlias.case.pick(nt_case: Bool, +b: List<&2, U32>, +e: List<&2, U32>) -> Maybe<&2, U32>:
  match nt_case:
    case True{}:
      FatAlias.case.nt(Bool.or(FatAlias.mixed(b), FatAlias.mixed(e)), U32.or(FatAlias.flag(b, 8), FatAlias.flag(e, 16)))
    case False{}:
      FatAlias.case.nt(Bool.or(FatAlias.has_lower(b), FatAlias.has_lower(e)), 0)

def FatAlias.case(nt_case: Bool, p: FatBasis) -> Maybe<&2, U32>:
  match p:
    case FatBasis{b, e, l}:
      FatAlias.case.pick(nt_case, b, e)

def FatAlias.tailed.go(p: FatBasis, +taken: List<&2, B.Octets>, long: List<&2, U32>) -> Result<&2, &2, E.FatError, FatAlias>:
  match p:
    case FatBasis{+b, +e, l}:
      do Result<&2, &2, E.FatError, FatAlias>:
        s : B.Octets <- FatAlias.tail(b, e, taken)
        return FatAlias{s, 0, long}

# a short name with a numeric tail, and the long name
def FatAlias.tailed(+xs: List<&2, U32>, +taken: List<&2, B.Octets>) -> Result<&2, &2, E.FatError, FatAlias>:
  FatAlias.tailed.go(FatAlias.basis(xs), taken, R.FatName.units(FatAlias.text(xs)))

def FatAlias.fits.case(m: Maybe<&2, U32>, +s: B.Octets, long: List<&2, U32>) -> FatAlias:
  match m:
    case None{}:
      FatAlias{s, 0, long}
    case Some{flags}:
      FatAlias{s, flags, Nil{}}

def FatAlias.fits(used: Bool, +nt_case: Bool, +xs: List<&2, U32>, +s: B.Octets, +taken: List<&2, B.Octets>) -> Result<&2, &2, E.FatError, FatAlias>:
  match used:
    case True{}:
      FatAlias.tailed(xs, taken)
    case False{}:
      Done{FatAlias.fits.case(FatAlias.case(nt_case, FatAlias.split83(xs)), s, R.FatName.units(FatAlias.text(xs)))}

def FatAlias.make.go(m: Maybe<&2, B.Octets>, +nt_case: Bool, +xs: List<&2, U32>, +taken: List<&2, B.Octets>) -> Result<&2, &2, E.FatError, FatAlias>:
  match m:
    case None{}:
      FatAlias.tailed(xs, taken)
    case Some{+s}:
      FatAlias.fits(FatAlias.taken(s, taken), nt_case, xs, s, taken)

# what to store for a new entry named name (a name FatAlias.check gave) in
# a directory whose entries have the short names taken: its own 8.3 form
# when it is one and no entry has it, else the basis name with the first
# numeric tail no entry has; a long name unless the short name shows it
def FatAlias.make(+nt_case: Bool, +name: String, +taken: List<&2, B.Octets>) -> Result<&2, &2, E.FatError, FatAlias>:
  FatAlias.make.go(R.FatName.short_of(name), nt_case, FatAlias.codes(name), taken)
