# Proof helpers for bend-osdev-asn1: UTCTime and GeneralizedTime contents
# read back as the time written. The writer puts down each field as two
# digits (proof_d2.bend: each reads back as the field, for values below
# 100, which every field of a valid time is); the reader takes five
# two-digit numbers, then the seconds, then Z. The year's digits are its
# remainder and quotient by 100 (pk.div_of, pk.mod_of: division's result is
# unique), so a GeneralizedTime's century and year, and a UTCTime's year
# from its century rule, come back.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./rules.bend as R
import ./time.bend as Ti
import ./proof_nat.bend as AN
import ./proof_u32.bend as AU
import ./proof_int.bend as PI
import ./proof_prims.bend as PP
import ./proof_d2.bend as PK

# Arithmetic: division's result is unique

def pk.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def pk.add_cancel(+k: Nat, +x: Nat, +y: Nat, +e: {Nat.add(k, x) == Nat.add(k, y) : Nat}) -> {x == y : Nat}:
  match k:
    case 0n:
      e
    case 1n+kp:
      pk.add_cancel(kp, x, y, Equal.cong(Nat, Nat, n => pk.pred(n), 1n+Nat.add(kp, x), 1n+Nat.add(kp, y), e))

# x = b + y + z with x < b is impossible
def pk.no_lt(+x: Nat, +b: Nat, +y: Nat, +z: Nat, +h: {Nat.is_lt(x, b) == True{} : Bool}, +e: {x == Nat.add(Nat.add(b, y), z) : Nat}) -> Empty:
  +hle = AN.an.le_trans(b, Nat.add(b, y), Nat.add(Nat.add(b, y), z), AN.an.le_add(b, y), AN.an.le_add(Nat.add(b, y), z))
  +hle2 = Equal.trans(Bool, Nat.is_le(b, x), Nat.is_le(b, Nat.add(Nat.add(b, y), z)), True{}, Equal.cong(Nat, Bool, w => Nat.is_le(b, w), x, Nat.add(Nat.add(b, y), z), e), hle)
  AN.an.ft(Equal.trans(Bool, False{}, Nat.is_le(b, x), True{}, Equal.sym(Bool, Nat.is_le(b, x), False{}, AN.an.lt_nle(x, b, h)), hle2))

# q1 b + r1 = q2 b + r2 with r1, r2 < b: q1 = q2
def pk.dm_q(+q1: Nat, +q2: Nat, +r1: Nat, +r2: Nat, +bp: Nat, +h1: {Nat.is_lt(r1, 1n+bp) == True{} : Bool}, +h2: {Nat.is_lt(r2, 1n+bp) == True{} : Bool}, +e: {Nat.add(Nat.mul(q1, 1n+bp), r1) == Nat.add(Nat.mul(q2, 1n+bp), r2) : Nat}) -> {q1 == q2 : Nat}:
  match q1 q2:
    case 0n 0n:
      {==}
    case 0n 1n+p:
      Empty.absurd({0n == 1n+p : Nat}, pk.no_lt(r1, 1n+bp, Nat.mul(p, 1n+bp), r2, h1, e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, pk.no_lt(r2, 1n+bp, Nat.mul(p, 1n+bp), r1, h2, Equal.sym(Nat, Nat.add(Nat.add(1n+bp, Nat.mul(p, 1n+bp)), r1), r2, e)))
    case 1n+p 1n+pp:
      +e1 = Equal.trans(Nat, Nat.add(1n+bp, Nat.add(Nat.mul(p, 1n+bp), r1)), Nat.add(Nat.add(1n+bp, Nat.mul(p, 1n+bp)), r1), Nat.add(1n+bp, Nat.add(Nat.mul(pp, 1n+bp), r2)), Equal.sym(Nat, Nat.add(Nat.add(1n+bp, Nat.mul(p, 1n+bp)), r1), Nat.add(1n+bp, Nat.add(Nat.mul(p, 1n+bp), r1)), AN.an.add_assoc(1n+bp, Nat.mul(p, 1n+bp), r1)), Equal.trans(Nat, Nat.add(Nat.add(1n+bp, Nat.mul(p, 1n+bp)), r1), Nat.add(Nat.add(1n+bp, Nat.mul(pp, 1n+bp)), r2), Nat.add(1n+bp, Nat.add(Nat.mul(pp, 1n+bp), r2)), e, AN.an.add_assoc(1n+bp, Nat.mul(pp, 1n+bp), r2)))
      +e2 = pk.add_cancel(1n+bp, Nat.add(Nat.mul(p, 1n+bp), r1), Nat.add(Nat.mul(pp, 1n+bp), r2), e1)
      Equal.cong(Nat, Nat, n => 1n+n, p, pp, pk.dm_q(p, pp, r1, r2, bp, h1, h2, e2))

def pk.div_of(+q: Nat, +r: Nat, +bp: Nat, +hr: {Nat.is_lt(r, 1n+bp) == True{} : Bool}) -> {Nat.div(Nat.add(Nat.mul(q, 1n+bp), r), 1n+bp) == q : Nat}:
  +n = Nat.add(Nat.mul(q, 1n+bp), r)
  pk.dm_q(Nat.div(n, 1n+bp), q, Nat.mod(n, 1n+bp), r, bp, AN.an.mod_lt(n, bp), hr, AN.an.recon(n, bp))

def pk.mod_of(+q: Nat, +r: Nat, +bp: Nat, +hr: {Nat.is_lt(r, 1n+bp) == True{} : Bool}) -> {Nat.mod(Nat.add(Nat.mul(q, 1n+bp), r), 1n+bp) == r : Nat}:
  +n = Nat.add(Nat.mul(q, 1n+bp), r)
  +e = Equal.trans(Nat, Nat.add(Nat.mul(q, 1n+bp), Nat.mod(n, 1n+bp)), Nat.add(Nat.mul(Nat.div(n, 1n+bp), 1n+bp), Nat.mod(n, 1n+bp)), Nat.add(Nat.mul(q, 1n+bp), r), Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(x, 1n+bp), Nat.mod(n, 1n+bp)), q, Nat.div(n, 1n+bp), Equal.sym(Nat, Nat.div(n, 1n+bp), q, pk.div_of(q, r, bp, hr))), AN.an.recon(n, bp))
  pk.add_cancel(Nat.mul(q, 1n+bp), Nat.mod(n, 1n+bp), r, e)

# Order

def pk.lt_of_le(+x: Nat, +c: Nat, +k: Nat, +h: {Nat.is_le(x, c) == True{} : Bool}, +hc: {Nat.is_le(1n+c, k) == True{} : Bool}) -> {Nat.is_lt(x, k) == True{} : Bool}:
  AN.an.lt_le_trans(x, 1n+c, k, AN.an.le_lt_succ(x, c, h), hc)

def pk.lt_lt(+x: Nat, +c: Nat, +k: Nat, +h: {Nat.is_lt(x, c) == True{} : Bool}, +hc: {Nat.is_le(c, k) == True{} : Bool}) -> {Nat.is_lt(x, k) == True{} : Bool}:
  AN.an.lt_le_trans(x, c, k, h, hc)

def pk.mdays_le.feb(lp: Bool) -> {Nat.is_le(Bool.pick(Nat, lp, 29n, 28n), 31n) == True{} : Bool}:
  match lp:
    case True{}:
      {==}
    case False{}:
      {==}

# no month has more than 31 days
def pk.mdays_le(+y: Nat, m: Nat) -> {Nat.is_le(Ti.a1.t.mdays(y, m), 31n) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      pk.mdays_le.feb(Ti.a1.t.leap(y))
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n+k:
      {==}

# the fields of a valid time are below 100
type PkF is Data:
  PkF{mo: Bool, d: Bool, h: Bool, mi: Bool, s: Bool}

def pk.f100(+mo: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat) -> PkF:
  PkF{Nat.is_lt(mo, 100n), Nat.is_lt(d, 100n), Nat.is_lt(h, 100n), Nat.is_lt(mi, 100n), Nat.is_lt(s, 100n)}

def pk.fields(+y: Nat, +mo: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat, +f: List<&2, Nat>, +z: Ti.Asn1Zone, +hv: {Ti.Asn1Time.valid(Ti.Asn1Time{y, mo, d, h, mi, s, f, z}) == True{} : Bool}) -> {pk.f100(mo, d, h, mi, s) == PkF{True{}, True{}, True{}, True{}, True{}} : PkF}:
  +c1 = Ti.a1.t.in(mo, 1n, 12n)
  +r1 = Bool.and(Ti.a1.t.in(d, 1n, Ti.a1.t.mdays(y, mo)), Bool.and(Nat.is_lt(h, 24n), Bool.and(Nat.is_lt(mi, 60n), Bool.and(Nat.is_lt(s, 60n), Ti.a1.t.zone_ok(z)))))
  +hmo = AN.an.and_r(Nat.is_le(1n, mo), Nat.is_le(mo, 12n), AN.an.and_l(c1, r1, hv))
  +h1 = AN.an.and_r(c1, r1, hv)
  +c2 = Ti.a1.t.in(d, 1n, Ti.a1.t.mdays(y, mo))
  +r2 = Bool.and(Nat.is_lt(h, 24n), Bool.and(Nat.is_lt(mi, 60n), Bool.and(Nat.is_lt(s, 60n), Ti.a1.t.zone_ok(z))))
  +hd = AN.an.le_trans(d, Ti.a1.t.mdays(y, mo), 31n, AN.an.and_r(Nat.is_le(1n, d), Nat.is_le(d, Ti.a1.t.mdays(y, mo)), AN.an.and_l(c2, r2, h1)), pk.mdays_le(y, mo))
  +h2 = AN.an.and_r(c2, r2, h1)
  +r3 = Bool.and(Nat.is_lt(mi, 60n), Bool.and(Nat.is_lt(s, 60n), Ti.a1.t.zone_ok(z)))
  +hh = AN.an.and_l(Nat.is_lt(h, 24n), r3, h2)
  +h3 = AN.an.and_r(Nat.is_lt(h, 24n), r3, h2)
  +r4 = Bool.and(Nat.is_lt(s, 60n), Ti.a1.t.zone_ok(z))
  +hmi = AN.an.and_l(Nat.is_lt(mi, 60n), r4, h3)
  +hs = AN.an.and_l(Nat.is_lt(s, 60n), Ti.a1.t.zone_ok(z), AN.an.and_r(Nat.is_lt(mi, 60n), r4, h3))
  %Equal.sym(Bool, Nat.is_lt(mo, 100n), True{}, pk.lt_of_le(mo, 12n, 100n, hmo, {==})) : {PkF{_, Nat.is_lt(d, 100n), Nat.is_lt(h, 100n), Nat.is_lt(mi, 100n), Nat.is_lt(s, 100n)} == PkF{True{}, True{}, True{}, True{}, True{}} : PkF}
  %Equal.sym(Bool, Nat.is_lt(d, 100n), True{}, pk.lt_of_le(d, 31n, 100n, hd, {==})) : {PkF{True{}, _, Nat.is_lt(h, 100n), Nat.is_lt(mi, 100n), Nat.is_lt(s, 100n)} == PkF{True{}, True{}, True{}, True{}, True{}} : PkF}
  %Equal.sym(Bool, Nat.is_lt(h, 100n), True{}, pk.lt_lt(h, 24n, 100n, hh, {==})) : {PkF{True{}, True{}, _, Nat.is_lt(mi, 100n), Nat.is_lt(s, 100n)} == PkF{True{}, True{}, True{}, True{}, True{}} : PkF}
  %Equal.sym(Bool, Nat.is_lt(mi, 100n), True{}, pk.lt_lt(mi, 60n, 100n, hmi, {==})) : {PkF{True{}, True{}, True{}, _, Nat.is_lt(s, 100n)} == PkF{True{}, True{}, True{}, True{}, True{}} : PkF}
  %Equal.sym(Bool, Nat.is_lt(s, 100n), True{}, pk.lt_lt(s, 60n, 100n, hs, {==})) : {PkF{True{}, True{}, True{}, True{}, _} == PkF{True{}, True{}, True{}, True{}, True{}} : PkF}
  {==}

def pk.fmo(p: PkF) -> Bool:
  match p:
    case PkF{a, b, c, d, e}:
      a

def pk.fd(p: PkF) -> Bool:
  match p:
    case PkF{a, b, c, d, e}:
      b

def pk.fh(p: PkF) -> Bool:
  match p:
    case PkF{a, b, c, d, e}:
      c

def pk.fmi(p: PkF) -> Bool:
  match p:
    case PkF{a, b, c, d, e}:
      d

def pk.fs(p: PkF) -> Bool:
  match p:
    case PkF{a, b, c, d, e}:
      e

# Two digits

def pk.p_da(p: PK.PkD2) -> Bool:
  match p:
    case PK.PkD2{a, b, c, d, e}:
      a

def pk.p_db(p: PK.PkD2) -> Bool:
  match p:
    case PK.PkD2{a, b, c, d, e}:
      b

def pk.p_ma(p: PK.PkD2) -> Bool:
  match p:
    case PK.PkD2{a, b, c, d, e}:
      c

def pk.p_mb(p: PK.PkD2) -> Bool:
  match p:
    case PK.PkD2{a, b, c, d, e}:
      d

def pk.p_v(p: PK.PkD2) -> Nat:
  match p:
    case PK.PkD2{a, b, c, d, e}:
      e

def pk.ca(+v: Nat) -> U32:
  U32.from_nat(Nat.add(48n, Nat.div(v, 10n)))

def pk.cb(+v: Nat) -> U32:
  U32.from_nat(Nat.add(48n, Nat.mod(v, 10n)))

def pk.da(+v: Nat, +lt: {Nat.is_lt(v, 100n) == True{} : Bool}) -> {Ti.a1.t.dig(pk.ca(v)) == True{} : Bool}:
  Equal.cong(PK.PkD2, Bool, p => pk.p_da(p), PK.pk.d2f(v), PK.PkD2{True{}, True{}, True{}, True{}, v}, PK.pk.d2(v, lt))

def pk.db(+v: Nat, +lt: {Nat.is_lt(v, 100n) == True{} : Bool}) -> {Ti.a1.t.dig(pk.cb(v)) == True{} : Bool}:
  Equal.cong(PK.PkD2, Bool, p => pk.p_db(p), PK.pk.d2f(v), PK.PkD2{True{}, True{}, True{}, True{}, v}, PK.pk.d2(v, lt))

def pk.ma(+v: Nat, +lt: {Nat.is_lt(v, 100n) == True{} : Bool}) -> {B.byte(pk.ca(v)) == pk.ca(v) : U32}:
  AU.au.is_eq_sound(B.byte(pk.ca(v)), pk.ca(v), Equal.cong(PK.PkD2, Bool, p => pk.p_ma(p), PK.pk.d2f(v), PK.PkD2{True{}, True{}, True{}, True{}, v}, PK.pk.d2(v, lt)))

def pk.mb(+v: Nat, +lt: {Nat.is_lt(v, 100n) == True{} : Bool}) -> {B.byte(pk.cb(v)) == pk.cb(v) : U32}:
  AU.au.is_eq_sound(B.byte(pk.cb(v)), pk.cb(v), Equal.cong(PK.PkD2, Bool, p => pk.p_mb(p), PK.pk.d2f(v), PK.PkD2{True{}, True{}, True{}, True{}, v}, PK.pk.d2(v, lt)))

def pk.val(+v: Nat, +lt: {Nat.is_lt(v, 100n) == True{} : Bool}) -> {Nat.add(Nat.mul(Ti.a1.t.val(pk.ca(v)), 10n), Ti.a1.t.val(pk.cb(v))) == v : Nat}:
  Equal.cong(PK.PkD2, Nat, p => pk.p_v(p), PK.pk.d2f(v), PK.PkD2{True{}, True{}, True{}, True{}, v}, PK.pk.d2(v, lt))

# two digits of v, then t, as octets
def pk.fix_d2(+v: Nat, +lt: {Nat.is_lt(v, 100n) == True{} : Bool}, +t: List<&2, U32>, +ht: {B.mask(t) == t : List<&2, U32>}) -> {B.mask(List.append(&2, U32, Ti.a1.t.d2(v), t)) == List.append(&2, U32, Ti.a1.t.d2(v), t) : List<&2, U32>}:
  %Equal.sym(U32, B.byte(pk.ca(v)), pk.ca(v), pk.ma(v, lt)) : {Con{_, Con{B.byte(pk.cb(v)), B.mask(t)}} == Con{pk.ca(v), Con{pk.cb(v), t}} : List<&2, U32>}
  %Equal.sym(U32, B.byte(pk.cb(v)), pk.cb(v), pk.mb(v, lt)) : {Con{pk.ca(v), Con{_, B.mask(t)}} == Con{pk.ca(v), Con{pk.cb(v), t}} : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(t), t, ht) : {Con{pk.ca(v), Con{pk.cb(v), _}} == Con{pk.ca(v), Con{pk.cb(v), t}} : List<&2, U32>}
  {==}

# reading a two-digit number
def pk.nums(+v: Nat, +lt: {Nat.is_lt(v, 100n) == True{} : Bool}, +j: Nat, +t: List<&2, U32>, +acc: List<&2, Nat>) -> {Ti.a1.t.nums(1n+j, List.append(&2, U32, Ti.a1.t.d2(v), t), True{}, acc) == Ti.a1.t.nums(j, t, True{}, Con{v, acc}) : Maybe<&2, Ti.A1TNums>}:
  %Equal.sym(Bool, Ti.a1.t.dig(pk.ca(v)), True{}, pk.da(v, lt)) : {Ti.a1.t.nums(j, t, Bool.and(_, Ti.a1.t.dig(pk.cb(v))), Con{Nat.add(Nat.mul(Ti.a1.t.val(pk.ca(v)), 10n), Ti.a1.t.val(pk.cb(v))), acc}) == Ti.a1.t.nums(j, t, True{}, Con{v, acc}) : Maybe<&2, Ti.A1TNums>}
  %Equal.sym(Bool, Ti.a1.t.dig(pk.cb(v)), True{}, pk.db(v, lt)) : {Ti.a1.t.nums(j, t, _, Con{Nat.add(Nat.mul(Ti.a1.t.val(pk.ca(v)), 10n), Ti.a1.t.val(pk.cb(v))), acc}) == Ti.a1.t.nums(j, t, True{}, Con{v, acc}) : Maybe<&2, Ti.A1TNums>}
  %Equal.sym(Nat, Nat.add(Nat.mul(Ti.a1.t.val(pk.ca(v)), 10n), Ti.a1.t.val(pk.cb(v))), v, pk.val(v, lt)) : {Ti.a1.t.nums(j, t, True{}, Con{_, acc}) == Ti.a1.t.nums(j, t, True{}, Con{v, acc}) : Maybe<&2, Ti.A1TNums>}
  {==}

def pk.two(+v: Nat, +lt: {Nat.is_lt(v, 100n) == True{} : Bool}, +t: List<&2, U32>) -> {Ti.a1.t.two(List.append(&2, U32, Ti.a1.t.d2(v), t)) == True{} : Bool}:
  %Equal.sym(Bool, Ti.a1.t.dig(pk.ca(v)), True{}, pk.da(v, lt)) : {Bool.and(_, Ti.a1.t.dig(pk.cb(v))) == True{} : Bool}
  pk.db(v, lt)

def pk.and_false(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pk.lmo(+y: Nat, +mo: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat, +f: List<&2, Nat>, +z: Ti.Asn1Zone, +hv: {Ti.Asn1Time.valid(Ti.Asn1Time{y, mo, d, h, mi, s, f, z}) == True{} : Bool}) -> {Nat.is_lt(mo, 100n) == True{} : Bool}:
  Equal.cong(PkF, Bool, p => pk.fmo(p), pk.f100(mo, d, h, mi, s), PkF{True{}, True{}, True{}, True{}, True{}}, pk.fields(y, mo, d, h, mi, s, f, z, hv))

def pk.ld(+y: Nat, +mo: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat, +f: List<&2, Nat>, +z: Ti.Asn1Zone, +hv: {Ti.Asn1Time.valid(Ti.Asn1Time{y, mo, d, h, mi, s, f, z}) == True{} : Bool}) -> {Nat.is_lt(d, 100n) == True{} : Bool}:
  Equal.cong(PkF, Bool, p => pk.fd(p), pk.f100(mo, d, h, mi, s), PkF{True{}, True{}, True{}, True{}, True{}}, pk.fields(y, mo, d, h, mi, s, f, z, hv))

def pk.lh(+y: Nat, +mo: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat, +f: List<&2, Nat>, +z: Ti.Asn1Zone, +hv: {Ti.Asn1Time.valid(Ti.Asn1Time{y, mo, d, h, mi, s, f, z}) == True{} : Bool}) -> {Nat.is_lt(h, 100n) == True{} : Bool}:
  Equal.cong(PkF, Bool, p => pk.fh(p), pk.f100(mo, d, h, mi, s), PkF{True{}, True{}, True{}, True{}, True{}}, pk.fields(y, mo, d, h, mi, s, f, z, hv))

def pk.lmi(+y: Nat, +mo: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat, +f: List<&2, Nat>, +z: Ti.Asn1Zone, +hv: {Ti.Asn1Time.valid(Ti.Asn1Time{y, mo, d, h, mi, s, f, z}) == True{} : Bool}) -> {Nat.is_lt(mi, 100n) == True{} : Bool}:
  Equal.cong(PkF, Bool, p => pk.fmi(p), pk.f100(mo, d, h, mi, s), PkF{True{}, True{}, True{}, True{}, True{}}, pk.fields(y, mo, d, h, mi, s, f, z, hv))

def pk.ls(+y: Nat, +mo: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat, +f: List<&2, Nat>, +z: Ti.Asn1Zone, +hv: {Ti.Asn1Time.valid(Ti.Asn1Time{y, mo, d, h, mi, s, f, z}) == True{} : Bool}) -> {Nat.is_lt(s, 100n) == True{} : Bool}:
  Equal.cong(PkF, Bool, p => pk.fs(p), pk.f100(mo, d, h, mi, s), PkF{True{}, True{}, True{}, True{}, True{}}, pk.fields(y, mo, d, h, mi, s, f, z, hv))

# UTCTime

# the characters the writer puts down, for a year's last two digits yy
def pk.utc_c(+yy: Nat, +mo: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat) -> List<&2, U32>:
  Ti.a1.t.app(Ti.a1.t.d2(yy), Ti.a1.t.app(Ti.a1.t.d2(mo), Ti.a1.t.app(Ti.a1.t.d2(d), Ti.a1.t.app(Ti.a1.t.d2(h), Ti.a1.t.app(Ti.a1.t.d2(mi), Ti.a1.t.app(Ti.a1.t.d2(s), [90]))))))

def pk.utc_read(+r: R.Asn1Rules, +pivot: Nat, +yy: Nat, +mo: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat, +hyy: {Nat.is_lt(yy, 100n) == True{} : Bool}, +hv: {Ti.Asn1Time.valid(Ti.Asn1Time{Ti.a1.utc.year(yy, pivot), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}) == True{} : Bool}) -> {Ti.Asn1.get_utc_time(r, pivot, N.Asn1Prim{T.Asn1Tag.utc_time(), B.Octets.of_list(pk.utc_c(yy, mo, d, h, mi, s))}) == Done{Ti.Asn1Time{Ti.a1.utc.year(yy, pivot), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}:
  +y = Ti.a1.utc.year(yy, pivot)
  +lmo = pk.lmo(y, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}, hv)
  +ld = pk.ld(y, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}, hv)
  +lh = pk.lh(y, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}, hv)
  +lmi = pk.lmi(y, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}, hv)
  +ls = pk.ls(y, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}, hv)
  +der = R.Asn1Rules.values(r)
  +r5 = Ti.a1.t.app(Ti.a1.t.d2(s), [90])
  +r4 = Ti.a1.t.app(Ti.a1.t.d2(mi), r5)
  +r3 = Ti.a1.t.app(Ti.a1.t.d2(h), r4)
  +r2 = Ti.a1.t.app(Ti.a1.t.d2(d), r3)
  +r1 = Ti.a1.t.app(Ti.a1.t.d2(mo), r2)
  +c = Ti.a1.t.app(Ti.a1.t.d2(yy), r1)
  +hf = pk.fix_d2(yy, hyy, r1, pk.fix_d2(mo, lmo, r2, pk.fix_d2(d, ld, r3, pk.fix_d2(h, lh, r4, pk.fix_d2(mi, lmi, r5, pk.fix_d2(s, ls, [90], {==}))))))
  +t : Ti.Asn1Time = Ti.Asn1Time{y, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(c)), c, PI.pi.to_of(c, hf)) : {Ti.a1.t.check(der, Ti.a1.utc.parse(Ti.a1.t.nums(5n, _, True{}, Nil{}), der, pivot)) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Maybe<&2, Ti.A1TNums>, Ti.a1.t.nums(5n, c, True{}, Nil{}), Ti.a1.t.nums(4n, r1, True{}, [yy]), pk.nums(yy, hyy, 4n, r1, Nil{})) : {Ti.a1.t.check(der, Ti.a1.utc.parse(_, der, pivot)) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Maybe<&2, Ti.A1TNums>, Ti.a1.t.nums(4n, r1, True{}, [yy]), Ti.a1.t.nums(3n, r2, True{}, [mo, yy]), pk.nums(mo, lmo, 3n, r2, [yy])) : {Ti.a1.t.check(der, Ti.a1.utc.parse(_, der, pivot)) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Maybe<&2, Ti.A1TNums>, Ti.a1.t.nums(3n, r2, True{}, [mo, yy]), Ti.a1.t.nums(2n, r3, True{}, [d, mo, yy]), pk.nums(d, ld, 2n, r3, [mo, yy])) : {Ti.a1.t.check(der, Ti.a1.utc.parse(_, der, pivot)) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Maybe<&2, Ti.A1TNums>, Ti.a1.t.nums(2n, r3, True{}, [d, mo, yy]), Ti.a1.t.nums(1n, r4, True{}, [h, d, mo, yy]), pk.nums(h, lh, 1n, r4, [d, mo, yy])) : {Ti.a1.t.check(der, Ti.a1.utc.parse(_, der, pivot)) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Maybe<&2, Ti.A1TNums>, Ti.a1.t.nums(1n, r4, True{}, [h, d, mo, yy]), Ti.a1.t.nums(0n, r5, True{}, [mi, h, d, mo, yy]), pk.nums(mi, lmi, 0n, r5, [h, d, mo, yy])) : {Ti.a1.t.check(der, Ti.a1.utc.parse(_, der, pivot)) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Bool, Ti.a1.t.two(r5), True{}, pk.two(s, ls, [90])) : {Ti.a1.t.check(der, Ti.a1.utc.sec(_, der, pivot, [yy, mo, d, h, mi], r5)) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Nat, Nat.add(Nat.mul(Ti.a1.t.val(pk.ca(s)), 10n), Ti.a1.t.val(pk.cb(s))), s, pk.val(s, ls)) : {Ti.a1.t.check(der, Some{Ti.Asn1Time{y, mo, d, h, mi, _, Nil{}, Ti.Asn1Zulu{}}}) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Bool, Ti.Asn1Time.valid(t), True{}, hv) : {Ti.a1.t.check2(Bool.and(_, R.a1.when(der, True{})), t) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Bool, R.a1.when(der, True{}), True{}, PP.pp.when_true(der)) : {Ti.a1.t.check2(_, t) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  {==}

# a year's last two digits, from the year a UTCTime's two digits stand for
def pk.mod_year(lt: Bool, +yy: Nat, +hyy: {Nat.is_lt(yy, 100n) == True{} : Bool}) -> {Nat.mod(Bool.pick(Nat, lt, Nat.add(2000n, yy), Nat.add(1900n, yy)), 100n) == yy : Nat}:
  match lt:
    case True{}:
      pk.mod_of(20n, yy, 99n, hyy)
    case False{}:
      pk.mod_of(19n, yy, 99n, hyy)

def pk.utc_rt(+r: R.Asn1Rules, +pivot: Nat, +yy: Nat, +mo: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat, +hyy: {Nat.is_lt(yy, 100n) == True{} : Bool}, +hv: {Ti.Asn1Time.valid(Ti.Asn1Time{Ti.a1.utc.year(yy, pivot), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}) == True{} : Bool}) -> {Ti.Asn1.get_utc_time(r, pivot, Ti.Asn1.utc_time(Ti.Asn1Time{Ti.a1.utc.year(yy, pivot), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}})) == Done{Ti.Asn1Time{Ti.a1.utc.year(yy, pivot), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}:
  +y = Ti.a1.utc.year(yy, pivot)
  +y2 = Nat.mod(y, 100n)
  +ey = Equal.cong(Nat, Nat, x => Ti.a1.utc.year(x, pivot), y2, yy, pk.mod_year(Nat.is_lt(yy, pivot), yy, hyy))
  +hv2 = Equal.trans(Bool, Ti.Asn1Time.valid(Ti.Asn1Time{Ti.a1.utc.year(y2, pivot), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}), Ti.Asn1Time.valid(Ti.Asn1Time{y, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}), True{}, Equal.cong(Nat, Bool, x => Ti.Asn1Time.valid(Ti.Asn1Time{x, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}), Ti.a1.utc.year(y2, pivot), y, ey), hv)
  %ey : {Ti.Asn1.get_utc_time(r, pivot, Ti.Asn1.utc_time(Ti.Asn1Time{y, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}})) == Done{Ti.Asn1Time{_, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  pk.utc_read(r, pivot, y2, mo, d, h, mi, s, AN.an.mod_lt(y, 99n), hv2)

# GeneralizedTime

def pk.gen_c(+c1: Nat, +c2: Nat, +mo: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat) -> List<&2, U32>:
  Ti.a1.t.app(Ti.a1.t.d2(c1), Ti.a1.t.app(Ti.a1.t.d2(c2), Ti.a1.t.app(Ti.a1.t.d2(mo), Ti.a1.t.app(Ti.a1.t.d2(d), Ti.a1.t.app(Ti.a1.t.d2(h), Ti.a1.t.app(Ti.a1.t.d2(mi), Ti.a1.t.app(Ti.a1.t.d2(s), Ti.a1.t.app(Ti.a1.t.fracs(Nil{}), [90]))))))))

def pk.gtwo1(+f: List<&2, Nat>, +mi: Nat, +lmi: {Nat.is_lt(mi, 100n) == True{} : Bool}, +rest: List<&2, U32>) -> {Ti.a1.gen.two(Ti.A1Gen{f, 0n, 0n, False{}, False{}, Nil{}, Ti.a1.t.app(Ti.a1.t.d2(mi), rest), True{}}) == Ti.A1Gen{f, mi, 0n, True{}, False{}, Nil{}, rest, True{}} : Ti.A1Gen}:
  %Equal.sym(Bool, Ti.a1.t.two(Ti.a1.t.app(Ti.a1.t.d2(mi), rest)), True{}, pk.two(mi, lmi, rest)) : {Ti.a1.gen.two.go(_, Ti.A1Gen{f, 0n, 0n, False{}, False{}, Nil{}, Ti.a1.t.app(Ti.a1.t.d2(mi), rest), True{}}) == Ti.A1Gen{f, mi, 0n, True{}, False{}, Nil{}, rest, True{}} : Ti.A1Gen}
  %Equal.sym(Nat, Nat.add(Nat.mul(Ti.a1.t.val(pk.ca(mi)), 10n), Ti.a1.t.val(pk.cb(mi))), mi, pk.val(mi, lmi)) : {Ti.A1Gen{f, _, 0n, True{}, False{}, Nil{}, rest, True{}} == Ti.A1Gen{f, mi, 0n, True{}, False{}, Nil{}, rest, True{}} : Ti.A1Gen}
  {==}

def pk.gtwo2(+f: List<&2, Nat>, +mi: Nat, +s: Nat, +ls: {Nat.is_lt(s, 100n) == True{} : Bool}, +rest: List<&2, U32>) -> {Ti.a1.gen.two(Ti.A1Gen{f, mi, 0n, True{}, False{}, Nil{}, Ti.a1.t.app(Ti.a1.t.d2(s), rest), True{}}) == Ti.A1Gen{f, mi, s, True{}, True{}, Nil{}, rest, True{}} : Ti.A1Gen}:
  %Equal.sym(Bool, Ti.a1.t.two(Ti.a1.t.app(Ti.a1.t.d2(s), rest)), True{}, pk.two(s, ls, rest)) : {Ti.a1.gen.two.go(_, Ti.A1Gen{f, mi, 0n, True{}, False{}, Nil{}, Ti.a1.t.app(Ti.a1.t.d2(s), rest), True{}}) == Ti.A1Gen{f, mi, s, True{}, True{}, Nil{}, rest, True{}} : Ti.A1Gen}
  %Equal.sym(Nat, Nat.add(Nat.mul(Ti.a1.t.val(pk.ca(s)), 10n), Ti.a1.t.val(pk.cb(s))), s, pk.val(s, ls)) : {Ti.A1Gen{f, mi, _, True{}, True{}, Nil{}, rest, True{}} == Ti.A1Gen{f, mi, s, True{}, True{}, Nil{}, rest, True{}} : Ti.A1Gen}
  {==}

def pk.gen_read(+r: R.Asn1Rules, +c1: Nat, +c2: Nat, +mo: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat, +hc1: {Nat.is_lt(c1, 100n) == True{} : Bool}, +hc2: {Nat.is_lt(c2, 100n) == True{} : Bool}, +hv: {Ti.Asn1Time.valid(Ti.Asn1Time{Nat.add(Nat.mul(c1, 100n), c2), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}) == True{} : Bool}) -> {Ti.Asn1.get_gen_time(r, N.Asn1Prim{T.Asn1Tag.generalized_time(), B.Octets.of_list(pk.gen_c(c1, c2, mo, d, h, mi, s))}) == Done{Ti.Asn1Time{Nat.add(Nat.mul(c1, 100n), c2), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}:
  +y = Nat.add(Nat.mul(c1, 100n), c2)
  +lmo = pk.lmo(y, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}, hv)
  +ld = pk.ld(y, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}, hv)
  +lh = pk.lh(y, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}, hv)
  +lmi = pk.lmi(y, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}, hv)
  +ls = pk.ls(y, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}, hv)
  +der = R.Asn1Rules.values(r)
  +r6 = Ti.a1.t.app(Ti.a1.t.d2(s), [90])
  +r5 = Ti.a1.t.app(Ti.a1.t.d2(mi), r6)
  +r4 = Ti.a1.t.app(Ti.a1.t.d2(h), r5)
  +r3 = Ti.a1.t.app(Ti.a1.t.d2(d), r4)
  +r2 = Ti.a1.t.app(Ti.a1.t.d2(mo), r3)
  +r1 = Ti.a1.t.app(Ti.a1.t.d2(c2), r2)
  +c = Ti.a1.t.app(Ti.a1.t.d2(c1), r1)
  +hf = pk.fix_d2(c1, hc1, r1, pk.fix_d2(c2, hc2, r2, pk.fix_d2(mo, lmo, r3, pk.fix_d2(d, ld, r4, pk.fix_d2(h, lh, r5, pk.fix_d2(mi, lmi, r6, pk.fix_d2(s, ls, [90], {==})))))))
  +t : Ti.Asn1Time = Ti.Asn1Time{y, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}
  +f : List<&2, Nat> = [c1, c2, mo, d, h]
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(c)), c, PI.pi.to_of(c, hf)) : {Ti.a1.t.check(der, Ti.a1.gen.finish(der, Ti.a1.gen.frac(der, Ti.a1.gen.two(Ti.a1.gen.two(Ti.a1.gen.start(Ti.a1.t.nums(5n, _, True{}, Nil{}))))))) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Maybe<&2, Ti.A1TNums>, Ti.a1.t.nums(5n, c, True{}, Nil{}), Ti.a1.t.nums(4n, r1, True{}, [c1]), pk.nums(c1, hc1, 4n, r1, Nil{})) : {Ti.a1.t.check(der, Ti.a1.gen.finish(der, Ti.a1.gen.frac(der, Ti.a1.gen.two(Ti.a1.gen.two(Ti.a1.gen.start(_)))))) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Maybe<&2, Ti.A1TNums>, Ti.a1.t.nums(4n, r1, True{}, [c1]), Ti.a1.t.nums(3n, r2, True{}, [c2, c1]), pk.nums(c2, hc2, 3n, r2, [c1])) : {Ti.a1.t.check(der, Ti.a1.gen.finish(der, Ti.a1.gen.frac(der, Ti.a1.gen.two(Ti.a1.gen.two(Ti.a1.gen.start(_)))))) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Maybe<&2, Ti.A1TNums>, Ti.a1.t.nums(3n, r2, True{}, [c2, c1]), Ti.a1.t.nums(2n, r3, True{}, [mo, c2, c1]), pk.nums(mo, lmo, 2n, r3, [c2, c1])) : {Ti.a1.t.check(der, Ti.a1.gen.finish(der, Ti.a1.gen.frac(der, Ti.a1.gen.two(Ti.a1.gen.two(Ti.a1.gen.start(_)))))) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Maybe<&2, Ti.A1TNums>, Ti.a1.t.nums(2n, r3, True{}, [mo, c2, c1]), Ti.a1.t.nums(1n, r4, True{}, [d, mo, c2, c1]), pk.nums(d, ld, 1n, r4, [mo, c2, c1])) : {Ti.a1.t.check(der, Ti.a1.gen.finish(der, Ti.a1.gen.frac(der, Ti.a1.gen.two(Ti.a1.gen.two(Ti.a1.gen.start(_)))))) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Maybe<&2, Ti.A1TNums>, Ti.a1.t.nums(1n, r4, True{}, [d, mo, c2, c1]), Ti.a1.t.nums(0n, r5, True{}, [h, d, mo, c2, c1]), pk.nums(h, lh, 0n, r5, [d, mo, c2, c1])) : {Ti.a1.t.check(der, Ti.a1.gen.finish(der, Ti.a1.gen.frac(der, Ti.a1.gen.two(Ti.a1.gen.two(Ti.a1.gen.start(_)))))) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Ti.A1Gen, Ti.a1.gen.two(Ti.A1Gen{f, 0n, 0n, False{}, False{}, Nil{}, r5, True{}}), Ti.A1Gen{f, mi, 0n, True{}, False{}, Nil{}, r6, True{}}, pk.gtwo1(f, mi, lmi, r6)) : {Ti.a1.t.check(der, Ti.a1.gen.finish(der, Ti.a1.gen.frac(der, Ti.a1.gen.two(_)))) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Ti.A1Gen, Ti.a1.gen.two(Ti.A1Gen{f, mi, 0n, True{}, False{}, Nil{}, r6, True{}}), Ti.A1Gen{f, mi, s, True{}, True{}, Nil{}, [90], True{}}, pk.gtwo2(f, mi, s, ls, [90])) : {Ti.a1.t.check(der, Ti.a1.gen.finish(der, Ti.a1.gen.frac(der, _))) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Bool, Bool.and(Bool.not(der), False{}), False{}, pk.and_false(Bool.not(der))) : {Ti.a1.t.check(der, Ti.a1.gen.finish(der, Ti.a1.gen.frac.go(_, Ti.A1Gen{f, mi, s, True{}, True{}, Nil{}, [90], True{}}))) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Bool, R.a1.when(der, True{}), True{}, PP.pp.when_true(der)) : {Ti.a1.t.check(der, Ti.a1.gen.mk(_, y, mo, d, h, mi, s, Nil{}, Some{Ti.Asn1Zulu{}})) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Bool, Ti.Asn1Time.valid(t), True{}, hv) : {Ti.a1.t.check2(Bool.and(_, R.a1.when(der, True{})), t) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  %Equal.sym(Bool, R.a1.when(der, True{}), True{}, PP.pp.when_true(der)) : {Ti.a1.t.check2(_, t) == Done{t} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  {==}

def pk.gen_rt(+r: R.Asn1Rules, +cc: Nat, +yy: Nat, +mo: Nat, +d: Nat, +h: Nat, +mi: Nat, +s: Nat, +hcc: {Nat.is_lt(cc, 100n) == True{} : Bool}, +hyy: {Nat.is_lt(yy, 100n) == True{} : Bool}, +hv: {Ti.Asn1Time.valid(Ti.Asn1Time{Nat.add(Nat.mul(cc, 100n), yy), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}) == True{} : Bool}) -> {Ti.Asn1.get_gen_time(r, Ti.Asn1.gen_time(Ti.Asn1Time{Nat.add(Nat.mul(cc, 100n), yy), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}})) == Done{Ti.Asn1Time{Nat.add(Nat.mul(cc, 100n), yy), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}:
  +y = Nat.add(Nat.mul(cc, 100n), yy)
  +c1 = Nat.div(y, 100n)
  +c2 = Nat.mod(y, 100n)
  +er = AN.an.recon(y, 99n)
  +hc1 = Equal.trans(Bool, Nat.is_lt(c1, 100n), Nat.is_lt(cc, 100n), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(x, 100n), c1, cc, pk.div_of(cc, yy, 99n, hyy)), hcc)
  +hv2 = Equal.trans(Bool, Ti.Asn1Time.valid(Ti.Asn1Time{Nat.add(Nat.mul(c1, 100n), c2), mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}), Ti.Asn1Time.valid(Ti.Asn1Time{y, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}), True{}, Equal.cong(Nat, Bool, x => Ti.Asn1Time.valid(Ti.Asn1Time{x, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}), Nat.add(Nat.mul(c1, 100n), c2), y, er), hv)
  %er : {Ti.Asn1.get_gen_time(r, Ti.Asn1.gen_time(Ti.Asn1Time{y, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}})) == Done{Ti.Asn1Time{_, mo, d, h, mi, s, Nil{}, Ti.Asn1Zulu{}}} : Result<&2, &2, E.Asn1Error, Ti.Asn1Time>}
  pk.gen_read(r, c1, c2, mo, d, h, mi, s, hc1, AN.an.mod_lt(y, 99n), hv2)
