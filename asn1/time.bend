# bend-osdev-asn1, UTCTime and GeneralizedTime (ITU-T X.680 (02/2021)
# clauses 47 and 46; their DER forms, X.690 (02/2021) 11.8 and 11.7).
#
# UTCTime: YYMMDDhhmm, optionally ss, then Z or +hhmm / -hhmm (X.680 47.3).
# GeneralizedTime: YYYYMMDDhh, optionally mm and then ss, a fraction of a
# second after a full stop or comma, then Z, +hh[mm] / -hh[mm], or nothing
# (local time) (X.680 46.3; this reader takes fractions only after the
# seconds, not of an hour or minute). Under the values rule (DER) both must
# end in Z and keep their seconds (11.7.1, 11.7.2, 11.8.1, 11.8.2), and a
# GeneralizedTime fraction uses a full stop and ends in a non-zero digit
# (11.7.3, 11.7.4). Dates must exist in the Gregorian calendar; hours are 0 to
# 23, minutes and seconds 0 to 59.
#
# A UTCTime holds two digits of its year; the century is a parameter
# (pivot: years below it are 20YY, the others 19YY). Asn1.utc_pivot() is
# 50, RFC 5280 4.1.2.5.1's rule.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./rules.bend as R
import ./prim.bend as P

type Asn1Zone is Data:
  Asn1Zulu{}
  Asn1LocalTime{}
  Asn1Offset{negative: Bool, hours: Nat, minutes: Nat}

# year (four digits), month, day, hour, minute, second, the fraction's
# digits, and the zone
type Asn1Time is Data:
  Asn1Time{year: Nat, month: Nat, day: Nat, hour: Nat, minute: Nat, second: Nat, frac: List<&2, Nat>, zone: Asn1Zone}

type A1TNums is Data:
  A1TNums{vals: List<&2, Nat>, rest: List<&2, U32>}

# A GeneralizedTime read so far: the date and hour, the minute and second
# (if present), the fraction's digits, the rest, and whether the form is
# right so far
type A1Gen is Data:
  A1Gen{f: List<&2, Nat>, mi: Nat, s: Nat, has_mi: Bool, has_s: Bool, frac: List<&2, Nat>, rest: List<&2, U32>, ok: Bool}

def Asn1.utc_pivot() -> Nat:
  50n

# Digits

def a1.t.dig(+x: U32) -> Bool:
  Bool.and(U32.is_le(48, x), U32.is_le(x, 57))

def a1.t.val(x: U32) -> Nat:
  U32.to_nat(U32.sub(x, 48))

def a1.t.done(ok: Bool, acc: List<&2, Nat>, xs: List<&2, U32>) -> Maybe<&2, A1TNums>:
  match ok:
    case True{}:
      Some{A1TNums{List.reverse(&2, Nat, acc), xs}}
    case False{}:
      None{}

# k two-digit numbers
def a1.t.nums(k: Nat, xs: List<&2, U32>, ok: Bool, acc: List<&2, Nat>) -> Maybe<&2, A1TNums>:
  match k xs:
    case 0n _:
      a1.t.done(ok, acc, xs)
    case 1n+j Con{+a, Con{+b, t}}:
      a1.t.nums(j, t, Bool.and(ok, Bool.and(a1.t.dig(a), a1.t.dig(b))), Con{Nat.add(Nat.mul(a1.t.val(a), 10n), a1.t.val(b)), acc})
    case 1n+j _:
      None{}

# whether xs starts with two digits
def a1.t.two(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{+a, Con{+b, t}}:
      Bool.and(a1.t.dig(a), a1.t.dig(b))
    case _:
      False{}

# Calendar

def a1.t.leap(+y: Nat) -> Bool:
  Bool.or(Bool.and(Nat.is_eq(Nat.mod(y, 4n), 0n), Bool.not(Nat.is_eq(Nat.mod(y, 100n), 0n))), Nat.is_eq(Nat.mod(y, 400n), 0n))

def a1.t.mdays(+y: Nat, m: Nat) -> Nat:
  match m:
    case 2n:
      Bool.pick(Nat, a1.t.leap(y), 29n, 28n)
    case 4n:
      30n
    case 6n:
      30n
    case 9n:
      30n
    case 11n:
      30n
    case _:
      31n

def a1.t.in(+v: Nat, lo: Nat, hi: Nat) -> Bool:
  Bool.and(Nat.is_le(lo, v), Nat.is_le(v, hi))

def a1.t.zone_ok(z: Asn1Zone) -> Bool:
  match z:
    case Asn1Offset{n, +h, +m}:
      Bool.and(Nat.is_lt(h, 24n), Nat.is_lt(m, 60n))
    case _:
      True{}

# a date and time of day that exist
def Asn1Time.valid(t: Asn1Time) -> Bool:
  match t:
    case Asn1Time{+y, +mo, +d, +h, +mi, +s, f, z}:
      Bool.and(a1.t.in(mo, 1n, 12n), Bool.and(a1.t.in(d, 1n, a1.t.mdays(y, mo)), Bool.and(Nat.is_lt(h, 24n), Bool.and(Nat.is_lt(mi, 60n), Bool.and(Nat.is_lt(s, 60n), a1.t.zone_ok(z))))))

def a1.t.days.go(+early: Bool, +y: Nat, +m: Nat, d: Nat) -> Nat:
  +y2 = Bool.pick(Nat, early, Nat.sub(y, 1n), y)
  +m2 = Bool.pick(Nat, early, Nat.add(m, 12n), m)
  Nat.add(Nat.add(Nat.mul(y2, 365n), Nat.add(Nat.sub(Nat.div(y2, 4n), Nat.div(y2, 100n)), Nat.div(y2, 400n))), Nat.add(Nat.div(Nat.add(Nat.mul(Nat.sub(m2, 3n), 153n), 2n), 5n), d))

# days from 0000-03-01 (with the year shifted 400 on, so the count stays
# a natural number): 365 a year, the leap days, and the months from March
def a1.t.days(+y: Nat, +m: Nat, d: Nat) -> Nat:
  a1.t.days.go(Nat.is_le(m, 2n), Nat.add(y, 400n), m, d)

def a1.t.shift(z: Asn1Zone, +secs: Nat) -> Nat:
  match z:
    case Asn1Offset{True{}, h, m}:
      Nat.add(Nat.add(secs, 86400n), Nat.mul(Nat.add(Nat.mul(h, 60n), m), 60n))
    case Asn1Offset{False{}, h, m}:
      Nat.sub(Nat.add(secs, 86400n), Nat.mul(Nat.add(Nat.mul(h, 60n), m), 60n))
    case _:
      Nat.add(secs, 86400n)

# the time as seconds in UTC (offsets applied; a local time taken as UTC),
# from an epoch before year 0
def Asn1Time.seconds(t: Asn1Time) -> Nat:
  match t:
    case Asn1Time{+y, +mo, d, h, mi, s, f, z}:
      a1.t.shift(z, Nat.add(Nat.mul(Nat.add(Nat.mul(Nat.add(Nat.mul(a1.t.days(y, mo, d), 24n), h), 60n), mi), 60n), s))

def a1.t.fcmp2(c: Cmp, rest: Cmp) -> Cmp:
  match c:
    case EQ{}:
      rest
    case LT{}:
      LT{}
    case GT{}:
      GT{}

# Zones

def a1.t.fcmp(f1: List<&2, Nat>, f2: List<&2, Nat>) -> Cmp:
  match f1 f2:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{b, t}:
      a1.t.fcmp(Nil{}, t)
    case Con{a, s} Nil{}:
      a1.t.fcmp(s, Nil{})
    case Con{+a, s} Con{+b, t}:
      a1.t.fcmp2(Nat.cmp(a, b), a1.t.fcmp(s, t))

def a1.t.cmp2(c: Cmp, f1: List<&2, Nat>, f2: List<&2, Nat>) -> Cmp:
  match c:
    case EQ{}:
      a1.t.fcmp(f1, f2)
    case LT{}:
      LT{}
    case GT{}:
      GT{}

# order of two times (fractions of a second compared digit by digit)
def Asn1Time.cmp(a: Asn1Time, b: Asn1Time) -> Cmp:
  match a b:
    case Asn1Time{y1, mo1, d1, h1, mi1, s1, +f1, z1} Asn1Time{y2, mo2, d2, h2, mi2, s2, +f2, z2}:
      a1.t.cmp2(Nat.cmp(Asn1Time.seconds(Asn1Time{y1, mo1, d1, h1, mi1, s1, f1, z1}), Asn1Time.seconds(Asn1Time{y2, mo2, d2, h2, mi2, s2, f2, z2})), f1, f2)

def a1.t.sign.pick(plus: Bool, minus: Bool) -> Maybe<&2, Bool>:
  match plus minus:
    case True{} _:
      Some{False{}}
    case False{} True{}:
      Some{True{}}
    case False{} False{}:
      None{}

def a1.t.sign(+x: U32) -> Maybe<&2, Bool>:
  a1.t.sign.pick(U32.is_eq(x, 43), U32.is_eq(x, 45))

def a1.t.off(s: Maybe<&2, Bool>, m: Maybe<&2, A1TNums>) -> Maybe<&2, Asn1Zone>:
  match s m:
    case Some{neg} Some{A1TNums{[h, mi], Nil{}}}:
      Some{Asn1Offset{neg, h, mi}}
    case Some{neg} Some{A1TNums{[h], Nil{}}}:
      Some{Asn1Offset{neg, h, 0n}}
    case _ _:
      None{}

# the zone at the end: Z, +hhmm / -hhmm (or +hh / -hh when hh_only), or
# (when local is allowed) nothing
def a1.t.zone(xs: List<&2, U32>, +local: Bool, +hh_only: Bool) -> Maybe<&2, Asn1Zone>:
  match xs:
    case Nil{}:
      Bool.pick(Maybe<&2, Asn1Zone>, local, Some{Asn1LocalTime{}}, None{})
    case Con{+x, Nil{}}:
      Bool.pick(Maybe<&2, Asn1Zone>, U32.is_eq(x, 90), Some{Asn1Zulu{}}, None{})
    case Con{+x, Con{a, Con{b, Nil{}}}}:
      Bool.pick(Maybe<&2, Asn1Zone>, hh_only, a1.t.off(a1.t.sign(x), a1.t.nums(1n, [a, b], True{}, Nil{})), None{})
    case Con{+x, t}:
      a1.t.off(a1.t.sign(x), a1.t.nums(2n, t, True{}, Nil{}))

def a1.t.zulu(z: Asn1Zone) -> Bool:
  match z:
    case Asn1Zulu{}:
      True{}
    case _:
      False{}

def a1.t.check2(ok: Bool, t: Asn1Time) -> Result<&2, &2, E.Asn1Error, Asn1Time>:
  match ok:
    case True{}:
      Done{t}
    case False{}:
      Fail{E.Asn1BadTime{}}

def Asn1Time.zone(t: Asn1Time) -> Asn1Zone:
  match t:
    case Asn1Time{y, mo, d, h, mi, s, f, z}:
      z

# UTCTime

def a1.t.check(+der: Bool, mt: Maybe<&2, Asn1Time>) -> Result<&2, &2, E.Asn1Error, Asn1Time>:
  match mt:
    case None{}:
      Fail{E.Asn1BadTime{}}
    case Some{+t}:
      a1.t.check2(Bool.and(Asn1Time.valid(t), R.a1.when(der, a1.t.zulu(Asn1Time.zone(t)))), t)

def a1.utc.year(+yy: Nat, +pivot: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(yy, pivot), Nat.add(2000n, yy), Nat.add(1900n, yy))

def a1.utc.zone(+pivot: Nat, f: List<&2, Nat>, +s: Nat, m: Maybe<&2, Asn1Zone>) -> Maybe<&2, Asn1Time>:
  match f m:
    case [yy, mo, d, h, mi] Some{z}:
      Some{Asn1Time{a1.utc.year(yy, pivot), mo, d, h, mi, s, Nil{}, z}}
    case _ _:
      None{}

def a1.utc.sec(two: Bool, +der: Bool, +pivot: Nat, f: List<&2, Nat>, rest: List<&2, U32>) -> Maybe<&2, Asn1Time>:
  match two rest:
    case True{} Con{+a, Con{+b, t}}:
      a1.utc.zone(pivot, f, Nat.add(Nat.mul(a1.t.val(a), 10n), a1.t.val(b)), a1.t.zone(t, False{}, False{}))
    case _ _:
      Bool.pick(Maybe<&2, Asn1Time>, der, None{}, a1.utc.zone(pivot, f, 0n, a1.t.zone(rest, False{}, False{})))

def a1.utc.parse(m: Maybe<&2, A1TNums>, +der: Bool, +pivot: Nat) -> Maybe<&2, Asn1Time>:
  match m:
    case None{}:
      None{}
    case Some{A1TNums{f, +rest}}:
      a1.utc.sec(a1.t.two(rest), der, pivot, f, rest)

# a UTCTime's characters as a time (the century from pivot)
def Asn1.utc_of_content(+r: R.Asn1Rules, +pivot: Nat, o: B.Octets) -> Result<&2, &2, E.Asn1Error, Asn1Time>:
  +der = R.Asn1Rules.values(r)
  a1.t.check(der, a1.utc.parse(a1.t.nums(5n, B.Octets.to_list(o), True{}, Nil{}), der, pivot))

# GeneralizedTime

def a1.t.head_dig(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      a1.t.dig(x)

# a run of digits (d: whether the first is one), and the rest
def a1.gen.run(xs: List<&2, U32>, d: Bool, acc: List<&2, Nat>) -> A1TNums:
  match xs d:
    case Nil{} _:
      A1TNums{List.reverse(&2, Nat, acc), Nil{}}
    case Con{x, t} False{}:
      A1TNums{List.reverse(&2, Nat, acc), Con{x, t}}
    case Con{+x, +t} True{}:
      a1.gen.run(t, a1.t.head_dig(t), Con{a1.t.val(x), acc})

def a1.gen.start(m: Maybe<&2, A1TNums>) -> A1Gen:
  match m:
    case None{}:
      A1Gen{Nil{}, 0n, 0n, False{}, False{}, Nil{}, Nil{}, False{}}
    case Some{A1TNums{f, rest}}:
      A1Gen{f, 0n, 0n, False{}, False{}, Nil{}, rest, True{}}

def a1.gen.two.go(two: Bool, g: A1Gen) -> A1Gen:
  match two g:
    case True{} A1Gen{f, mi, s, False{}, hs, fr, Con{+a, Con{+b, t}}, ok}:
      A1Gen{f, Nat.add(Nat.mul(a1.t.val(a), 10n), a1.t.val(b)), s, True{}, hs, fr, t, ok}
    case True{} A1Gen{f, mi, s, True{}, False{}, fr, Con{+a, Con{+b, t}}, ok}:
      A1Gen{f, mi, Nat.add(Nat.mul(a1.t.val(a), 10n), a1.t.val(b)), True{}, True{}, fr, t, ok}
    case _ g2:
      g2

# the next two digits, as the minute or then the second, if present
def a1.gen.two(g: A1Gen) -> A1Gen:
  match g:
    case A1Gen{f, mi, s, hm, hs, fr, +rest, ok}:
      a1.gen.two.go(a1.t.two(rest), A1Gen{f, mi, s, hm, hs, fr, rest, ok})

def a1.gen.dec_sign(+x: U32, +der: Bool) -> Bool:
  Bool.or(U32.is_eq(x, 46), Bool.and(Bool.not(der), U32.is_eq(x, 44)))

def a1.gen.frac.put(r: A1TNums, g: A1Gen) -> A1Gen:
  match r g:
    case A1TNums{+ds, rest} A1Gen{f, mi, s, hm, hs, fr, t, ok}:
      A1Gen{f, mi, s, hm, hs, ds, rest, Bool.and(ok, Bool.not(List.is_empty(&2, Nat, ds)))}

def a1.gen.frac.go(sign: Bool, g: A1Gen) -> A1Gen:
  match sign g:
    case True{} A1Gen{f, mi, s, hm, hs, fr, Con{x, +t}, ok}:
      a1.gen.frac.put(a1.gen.run(t, a1.t.head_dig(t), Nil{}), A1Gen{f, mi, s, hm, hs, fr, t, ok})
    case _ g2:
      g2

# a fraction of a second, after the seconds
def a1.gen.frac(+der: Bool, g: A1Gen) -> A1Gen:
  match g:
    case A1Gen{f, mi, s, hm, True{}, fr, Con{+x, +t}, ok}:
      a1.gen.frac.go(a1.gen.dec_sign(x, der), A1Gen{f, mi, s, hm, True{}, fr, Con{x, t}, ok})
    case g2:
      g2

def a1.gen.last0(ds: List<&2, Nat>, last: Nat) -> Bool:
  match ds:
    case Nil{}:
      Nat.is_eq(last, 0n)
    case Con{d, t}:
      a1.gen.last0(t, d)

# DER: minutes and seconds present, no trailing zero in the fraction
def a1.gen.der_ok(g: A1Gen) -> Bool:
  match g:
    case A1Gen{f, mi, s, hm, hs, +fr, rest, ok}:
      Bool.and(hm, Bool.and(hs, Bool.or(List.is_empty(&2, Nat, fr), Bool.not(a1.gen.last0(fr, 0n)))))

def a1.gen.mk(ok: Bool, y: Nat, mo: Nat, d: Nat, h: Nat, mi: Nat, s: Nat, fr: List<&2, Nat>, z: Maybe<&2, Asn1Zone>) -> Maybe<&2, Asn1Time>:
  match ok z:
    case True{} Some{zz}:
      Some{Asn1Time{y, mo, d, h, mi, s, fr, zz}}
    case _ _:
      None{}

def a1.gen.finish(+der: Bool, +g: A1Gen) -> Maybe<&2, Asn1Time>:
  match g:
    case A1Gen{[y1, y2, mo, d, h], mi, s, hm, hs, fr, rest, True{}}:
      a1.gen.mk(R.a1.when(der, a1.gen.der_ok(g)), Nat.add(Nat.mul(y1, 100n), y2), mo, d, h, mi, s, fr, a1.t.zone(rest, Bool.not(der), True{}))
    case _:
      None{}

# a GeneralizedTime's characters as a time
def Asn1.gen_of_content(+r: R.Asn1Rules, o: B.Octets) -> Result<&2, &2, E.Asn1Error, Asn1Time>:
  +der = R.Asn1Rules.values(r)
  a1.t.check(der, a1.gen.finish(der, a1.gen.frac(der, a1.gen.two(a1.gen.two(a1.gen.start(a1.t.nums(5n, B.Octets.to_list(o), True{}, Nil{})))))))

# Elements

def a1.t.from(r: Result<&2, &2, E.Asn1Error, B.Octets>, +rr: R.Asn1Rules, +pivot: Nat, utc: Bool) -> Result<&2, &2, E.Asn1Error, Asn1Time>:
  match r utc:
    case Fail{e} _:
      Fail{e}
    case Done{o} True{}:
      Asn1.utc_of_content(rr, pivot, o)
    case Done{o} False{}:
      Asn1.gen_of_content(rr, o)

# a UTCTime element's time
def Asn1.get_utc_time(+r: R.Asn1Rules, +pivot: Nat, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Asn1Time>:
  a1.t.from(P.a1.string_value(R.Asn1Rules.prim_strings(r), T.Asn1Tag.utc_time(), T.Asn1Tag.utc_time(), n), r, pivot, True{})

# a GeneralizedTime element's time
def Asn1.get_gen_time(+r: R.Asn1Rules, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Asn1Time>:
  a1.t.from(P.a1.string_value(R.Asn1Rules.prim_strings(r), T.Asn1Tag.generalized_time(), T.Asn1Tag.generalized_time(), n), r, 50n, False{})

def a1.t.either(utc: Bool, +r: R.Asn1Rules, +pivot: Nat, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Asn1Time>:
  match utc:
    case True{}:
      Asn1.get_utc_time(r, pivot, n)
    case False{}:
      Asn1.get_gen_time(r, n)

# a UTCTime or GeneralizedTime element's time (X.509's Time)
def Asn1.get_time(+r: R.Asn1Rules, +pivot: Nat, +n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, Asn1Time>:
  a1.t.either(T.Asn1Tag.is_eq(N.Asn1Node.tag(n), T.Asn1Tag.utc_time()), r, pivot, n)

# Writing (the DER forms: seconds kept, Z, no trailing fraction zeros)

def a1.t.d2(+v: Nat) -> List<&2, U32>:
  [U32.from_nat(Nat.add(48n, Nat.div(v, 10n))), U32.from_nat(Nat.add(48n, Nat.mod(v, 10n)))]

def a1.t.ds(ds: List<&2, Nat>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      Con{U32.from_nat(Nat.add(48n, d)), a1.t.ds(t)}

def a1.t.drop0(ds: List<&2, Nat>) -> List<&2, Nat>:
  match ds:
    case Con{0n, t}:
      a1.t.drop0(t)
    case t:
      t

def a1.t.trim(ds: List<&2, Nat>) -> List<&2, Nat>:
  List.reverse(&2, Nat, a1.t.drop0(List.reverse(&2, Nat, ds)))

def a1.t.fracs.go(fr: List<&2, Nat>) -> List<&2, U32>:
  match fr:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      Con{46, a1.t.ds(Con{d, t})}

def a1.t.fracs(fr: List<&2, Nat>) -> List<&2, U32>:
  a1.t.fracs.go(a1.t.trim(fr))

def a1.t.app(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, ys)

# a time as a UTCTime element: YYMMDDHHMMSSZ (the year's last two digits)
def Asn1.utc_time(t: Asn1Time) -> N.Asn1Node:
  match t:
    case Asn1Time{+y, mo, d, h, mi, s, f, z}:
      N.Asn1Prim{T.Asn1Tag.utc_time(), B.Octets.of_list(a1.t.app(a1.t.d2(Nat.mod(y, 100n)), a1.t.app(a1.t.d2(mo), a1.t.app(a1.t.d2(d), a1.t.app(a1.t.d2(h), a1.t.app(a1.t.d2(mi), a1.t.app(a1.t.d2(s), [90])))))))}

# a time as a GeneralizedTime element: YYYYMMDDHHMMSS[.f]Z
def Asn1.gen_time(t: Asn1Time) -> N.Asn1Node:
  match t:
    case Asn1Time{+y, mo, d, h, mi, s, f, z}:
      N.Asn1Prim{T.Asn1Tag.generalized_time(), B.Octets.of_list(a1.t.app(a1.t.d2(Nat.div(y, 100n)), a1.t.app(a1.t.d2(Nat.mod(y, 100n)), a1.t.app(a1.t.d2(mo), a1.t.app(a1.t.d2(d), a1.t.app(a1.t.d2(h), a1.t.app(a1.t.d2(mi), a1.t.app(a1.t.d2(s), a1.t.app(a1.t.fracs(f), [90])))))))))}

def a1.t.show2(+v: Nat) -> String:
  B.Octets.to_string(B.Octets.of_list(a1.t.d2(v)))

def a1.t.show_zone(z: Asn1Zone) -> String:
  match z:
    case Asn1Zulu{}:
      "Z"
    case Asn1LocalTime{}:
      ""
    case Asn1Offset{n, +h, +m}:
      Bool.pick(String, n, "-", "+") ++ a1.t.show2(h) ++ ":" ++ a1.t.show2(m)

# a time as text: YYYY-MM-DDTHH:MM:SS[.f] and Z, +HH:MM / -HH:MM, or nothing
def Asn1Time.show(t: Asn1Time) -> String:
  match t:
    case Asn1Time{+y, +mo, +d, +h, +mi, +s, f, z}:
      a1.t.show2(Nat.div(y, 100n)) ++ a1.t.show2(Nat.mod(y, 100n)) ++ "-" ++ a1.t.show2(mo) ++ "-" ++ a1.t.show2(d) ++ "T" ++ a1.t.show2(h) ++ ":" ++ a1.t.show2(mi) ++ ":" ++ a1.t.show2(s) ++ B.Octets.to_string(B.Octets.of_list(a1.t.fracs.go(f))) ++ a1.t.show_zone(z)
