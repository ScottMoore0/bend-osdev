# Proofs of bend-osdev-asn1's typed laws (LAWS_typed.bend). The lemmas are
# in proof_int.bend (INTEGER), proof_prims.bend (BOOLEAN, NULL, OCTET
# STRING, BIT STRING, character strings, constructed values and tags),
# proof_clock.bend (UTCTime and GeneralizedTime) and proof_d2.bend
# (generated: the two digits of each number below 100), proof_strict.bend,
# proof_intc.bend and proof_tstrict.bend (what the readers accept), and
# proof_chars.bend (generated: each octet against the character tables).
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./rules.bend as R
import ./prim.bend as P
import ./bits.bend as Bi
import ./string.bend as S
import ./time.bend as Ti
import ./build.bend as Bu
import ./proof_int.bend as PI
import ./proof_prims.bend as PP
import ./proof_clock.bend as PK
import ./proof_strict.bend as PS
import ./proof_intc.bend as PC
import ./proof_tstrict.bend as PD
import ./proof_chars.bend as PCH
import ./proof_list.bend as AL
import ./LAWS_typed.bend as Laws

# the law's statement of a bit string's last octet is the reader's
def pt.last_eq(xs: List<&2, U32>, +acc: U32) -> {Bi.a1.bits.last(xs, acc) == Laws.asn1law.last(xs, acc) : U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      pt.last_eq(t, x)

def pt.clear_eq(+u: Nat, +o: B.Octets) -> {Bi.a1.bits.clear(u, o) == Laws.asn1law.bits_clear(u, o) : Bool}:
  %pt.last_eq(B.Octets.to_list(o), 0) : {Bi.a1.bits.clear(u, o) == U32.is_eq(U32.and(_, U32.sub(U32.shln(1, u), 1)), 0) : Bool}
  {==}

def Laws.bool_round_trip(r, b):
  PP.pp.bool_rt(r, b)

def Laws.null_round_trip():
  {==}

def Laws.octets_round_trip(r, t, o):
  PP.pp.octets_rt(r, t, o)

def Laws.int_round_trip(t, neg, m, hz, hl):
  PI.pi.int_rt(t, neg, m, hz, hl)

def Laws.enum_round_trip(neg, m, hz, hl):
  PI.pi.int_rt(T.Asn1Tag.enumerated(), neg, m, hz, hl)

def Laws.nat_round_trip(n, hl):
  %Equal.sym(Result<&2, &2, E.Asn1Error, P.Asn1Int>, P.Asn1.get_int_as(T.Asn1Tag.integer(), P.Asn1.int_as(T.Asn1Tag.integer(), P.Asn1Int{False{}, n})), Done{P.Asn1Int{False{}, n}}, PI.pi.int_rt(T.Asn1Tag.integer(), False{}, n, {==}, hl)) : {P.a1.int.nat_from(_) == Done{n} : Result<&2, &2, E.Asn1Error, Nat>}
  {==}

def Laws.bits_round_trip(r, t, u, o, hok, hc):
  PP.pp.bits_rt(r, t, u, o, hok, Equal.trans(Bool, Bi.a1.bits.clear(u, o), Laws.asn1law.bits_clear(u, o), True{}, pt.clear_eq(u, o), hc))

def Laws.bits_ber_round_trip(r, hv, t, u, o, hok):
  PP.pp.bits_ber(r, hv, t, u, o, hok)

def Laws.bits_octets_round_trip(r, t, o):
  PP.pp.bits_whole(r, t, o)

def Laws.string_round_trip(r, k, o, hv):
  PP.pp.str_rt(r, k, o, hv)

def Laws.string_implicit_round_trip(r, t, k, o, hv):
  PP.pp.str_as_rt(r, t, k, o, hv)

def Laws.utc_round_trip(r, pivot, yy, mo, d, h, mi, s, hyy, hv):
  PK.pk.utc_rt(r, pivot, yy, mo, d, h, mi, s, hyy, hv)

def Laws.gen_round_trip(r, cc, yy, mo, d, h, mi, s, hcc, hyy, hv):
  PK.pk.gen_rt(r, cc, yy, mo, d, h, mi, s, hcc, hyy, hv)

def Laws.time_utc_round_trip(r, pivot, yy, mo, d, h, mi, s, hyy, hv):
  PK.pk.utc_rt(r, pivot, yy, mo, d, h, mi, s, hyy, hv)

def Laws.time_gen_round_trip(r, pivot, cc, yy, mo, d, h, mi, s, hcc, hyy, hv):
  PK.pk.gen_rt(r, cc, yy, mo, d, h, mi, s, hcc, hyy, hv)

def Laws.seq_round_trip(xs):
  {==}

def Laws.set_round_trip(xs):
  {==}

def Laws.cons_round_trip(t, xs):
  PP.pp.cons_rt(t, xs)

def Laws.explicit_round_trip(n, x):
  PP.pp.explicit_rt(n, x)

def Laws.implicit_round_trip(t, u, x):
  PP.pp.untag_rt(t, u, x)

def Laws.implicit_tag(t, x):
  PP.pp.has_tag(t, x)

def Laws.bool_canonical(r, hv, n, b, e):
  PS.sx.bool_c(r, hv, n, b, e)

def Laws.null_canonical(n, u, e):
  PS.sx.null_c(n, u, e)

def Laws.octets_canonical(r, hp, t, n, o, e):
  PS.sx.octets_c(r, hp, t, n, o, e)

def Laws.bits_canonical(r, hp, t, n, b, e):
  PS.sx.bits_c(r, hp, t, n, b, e)

def Laws.string_canonical(r, hp, n, s, e):
  PS.sx.str_read_c(S.Asn1StrKind.of_tag(N.Asn1Node.tag(n)), r, hp, n, s, e)

def Laws.string_implicit_canonical(r, hp, t, k, n, s, e):
  PS.sx.str_got_c(r, hp, t, k, n, P.a1.string_value(R.Asn1Rules.prim_strings(r), t, S.Asn1StrKind.tag(k), n), {==}, s, e)

def Laws.string_valid(r, n, s, e):
  PS.sx.str_read_v(S.Asn1StrKind.of_tag(N.Asn1Node.tag(n)), r, n, s, e)

def Laws.string_implicit_valid(r, t, k, n, s, e):
  PS.sx.str_got_v(k, P.a1.string_value(R.Asn1Rules.prim_strings(r), t, S.Asn1StrKind.tag(k), n), s, e)

def Laws.cons_canonical(t, n, xs, e):
  PS.sx.cons_c(t, n, xs, e)

def Laws.seq_canonical(n, xs, e):
  PS.sx.cons_c(T.Asn1Tag.sequence(), n, xs, e)

def Laws.set_canonical(n, xs, e):
  PS.sx.cons_c(T.Asn1Tag.set(), n, xs, e)

def Laws.explicit_canonical(k, n, x, e):
  PS.sx.explicit_c(k, n, x, e)

def Laws.utc_valid(r, pivot, n, t, e):
  PS.sx.valid_of(R.Asn1Rules.values(r), t, PS.sx.from(P.a1.string_value(R.Asn1Rules.prim_strings(r), T.Asn1Tag.utc_time(), T.Asn1Tag.utc_time(), n), r, pivot, True{}, t, e))

def Laws.gen_valid(r, n, t, e):
  PS.sx.valid_of(R.Asn1Rules.values(r), t, PS.sx.from(P.a1.string_value(R.Asn1Rules.prim_strings(r), T.Asn1Tag.generalized_time(), T.Asn1Tag.generalized_time(), n), r, 50n, False{}, t, e))

def Laws.time_valid(r, pivot, n, t, e):
  PS.sx.valid_of(R.Asn1Rules.values(r), t, PS.sx.time(r, pivot, n, t, e))

def Laws.utc_zulu(r, hv, pivot, n, t, e):
  PS.sx.zulu_of(t, PS.sx.der_facts(r, hv, t, PS.sx.from(P.a1.string_value(R.Asn1Rules.prim_strings(r), T.Asn1Tag.utc_time(), T.Asn1Tag.utc_time(), n), r, pivot, True{}, t, e)))

def Laws.gen_zulu(r, hv, n, t, e):
  PS.sx.zulu_of(t, PS.sx.der_facts(r, hv, t, PS.sx.from(P.a1.string_value(R.Asn1Rules.prim_strings(r), T.Asn1Tag.generalized_time(), T.Asn1Tag.generalized_time(), n), r, 50n, False{}, t, e)))

def Laws.time_zulu(r, hv, pivot, n, t, e):
  PS.sx.zulu_of(t, PS.sx.der_facts(r, hv, t, PS.sx.time(r, pivot, n, t, e)))

def Laws.int_canonical(t, n, i, e):
  PC.pc.int_c(t, n, i, e)

def Laws.enum_canonical(n, i, e):
  PC.pc.int_c(T.Asn1Tag.enumerated(), n, i, e)

def Laws.nat_canonical(n, m, e):
  PC.pc.int_c(T.Asn1Tag.integer(), n, P.Asn1Int{False{}, m}, PC.pc.nat_from(P.Asn1.get_int(n), m, e))

def Laws.utc_canonical(r, hv, hp, pivot, n, t, e):
  PD.pd.utc_top(P.a1.string_value(R.Asn1Rules.prim_strings(r), T.Asn1Tag.utc_time(), T.Asn1Tag.utc_time(), n), r, hv, hp, pivot, n, t, {==}, e)

def Laws.gen_canonical(r, hv, hp, n, y, mo, d, h, mi, s, z, e):
  PD.pd.gen_top(P.a1.string_value(R.Asn1Rules.prim_strings(r), T.Asn1Tag.generalized_time(), T.Asn1Tag.generalized_time(), n), r, hv, hp, n, Ti.Asn1Time{y, mo, d, h, mi, s, Nil{}, z}, {==}, {==}, e)

# The character tables

def pt.comb(p: PCH.PcCh, q: PCH.PcCh) -> PCH.PcCh:
  match p q:
    case PCH.PcCh{a, b, c, d} PCH.PcCh{e, f, g, h}:
      PCH.PcCh{Bool.and(a, e), Bool.and(b, f), Bool.and(c, g), Bool.and(d, h)}

def pt.recl(+xs: List<&2, U32>) -> PCH.PcCh:
  PCH.PcCh{S.a1.all_in(xs, S.Asn1Numeric{}), S.a1.all_in(xs, S.Asn1Printable{}), S.a1.all_in(xs, S.Asn1Ia5{}), S.a1.all_in(xs, S.Asn1Visible{})}

def pt.recr(+xs: List<&2, U32>) -> PCH.PcCh:
  PCH.PcCh{Laws.asn1law.all_of(xs, Laws.asn1law.numeric_chars()), Laws.asn1law.all_of(xs, Laws.asn1law.printable_chars()), Laws.asn1law.all_of(xs, Laws.asn1law.ia5_chars()), Laws.asn1law.all_of(xs, Laws.asn1law.visible_chars())}

# octets: each check of all of them is membership of the table for all
def pt.rec(xs: List<&2, U32>, +hf: {B.mask(xs) == xs : List<&2, U32>}) -> {pt.recl(xs) == pt.recr(xs) : PCH.PcCh}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +hx = PS.sx.cons_fix(x, t, hf)
      +ht = PS.sx.cons_fix_t(x, t, hf)
      +eo = Equal.trans(PCH.PcCh, PCH.pc.chk(x), PCH.pc.chk(B.byte(x)), PCH.pc.tbl(x), Equal.cong(U32, PCH.PcCh, y => PCH.pc.chk(y), x, B.byte(x), Equal.sym(U32, B.byte(x), x, hx)), Equal.trans(PCH.PcCh, PCH.pc.chk(B.byte(x)), PCH.pc.tbl(B.byte(x)), PCH.pc.tbl(x), PCH.pc.oct(x), Equal.cong(U32, PCH.PcCh, y => PCH.pc.tbl(y), B.byte(x), x, hx)))
      %Equal.sym(PCH.PcCh, PCH.pc.chk(x), PCH.pc.tbl(x), eo) : {pt.comb(_, pt.recl(t)) == pt.comb(PCH.pc.tbl(x), pt.recr(t)) : PCH.PcCh}
      %Equal.sym(PCH.PcCh, pt.recl(t), pt.recr(t), pt.rec(t, ht)) : {pt.comb(PCH.pc.tbl(x), _) == pt.comb(PCH.pc.tbl(x), pt.recr(t)) : PCH.PcCh}
      {==}

def pt.some_ok(b: Bool, +xs: List<&2, U32>) -> {Maybe.is_some(&2, List<&2, U32>, S.a1.ok_chars(b, xs)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pt.pn(p: PCH.PcCh) -> Bool:
  match p:
    case PCH.PcCh{a, b, c, d}:
      a

def pt.pp(p: PCH.PcCh) -> Bool:
  match p:
    case PCH.PcCh{a, b, c, d}:
      b

def pt.pi(p: PCH.PcCh) -> Bool:
  match p:
    case PCH.PcCh{a, b, c, d}:
      c

def pt.pv(p: PCH.PcCh) -> Bool:
  match p:
    case PCH.PcCh{a, b, c, d}:
      d

def Laws.numeric_chars(o):
  +xs = B.Octets.to_list(o)
  Equal.trans(Bool, Maybe.is_some(&2, List<&2, U32>, S.a1.ok_chars(S.a1.all_in(xs, S.Asn1Numeric{}), xs)), S.a1.all_in(xs, S.Asn1Numeric{}), Laws.asn1law.all_of(xs, Laws.asn1law.numeric_chars()), pt.some_ok(S.a1.all_in(xs, S.Asn1Numeric{}), xs), Equal.cong(PCH.PcCh, Bool, p => pt.pn(p), pt.recl(xs), pt.recr(xs), pt.rec(xs, AL.al.mask_to(o))))

def Laws.printable_chars(o):
  +xs = B.Octets.to_list(o)
  Equal.trans(Bool, Maybe.is_some(&2, List<&2, U32>, S.a1.ok_chars(S.a1.all_in(xs, S.Asn1Printable{}), xs)), S.a1.all_in(xs, S.Asn1Printable{}), Laws.asn1law.all_of(xs, Laws.asn1law.printable_chars()), pt.some_ok(S.a1.all_in(xs, S.Asn1Printable{}), xs), Equal.cong(PCH.PcCh, Bool, p => pt.pp(p), pt.recl(xs), pt.recr(xs), pt.rec(xs, AL.al.mask_to(o))))

def Laws.ia5_chars(o):
  +xs = B.Octets.to_list(o)
  Equal.trans(Bool, Maybe.is_some(&2, List<&2, U32>, S.a1.ok_chars(S.a1.all_in(xs, S.Asn1Ia5{}), xs)), S.a1.all_in(xs, S.Asn1Ia5{}), Laws.asn1law.all_of(xs, Laws.asn1law.ia5_chars()), pt.some_ok(S.a1.all_in(xs, S.Asn1Ia5{}), xs), Equal.cong(PCH.PcCh, Bool, p => pt.pi(p), pt.recl(xs), pt.recr(xs), pt.rec(xs, AL.al.mask_to(o))))

def Laws.visible_chars(o):
  +xs = B.Octets.to_list(o)
  Equal.trans(Bool, Maybe.is_some(&2, List<&2, U32>, S.a1.ok_chars(S.a1.all_in(xs, S.Asn1Visible{}), xs)), S.a1.all_in(xs, S.Asn1Visible{}), Laws.asn1law.all_of(xs, Laws.asn1law.visible_chars()), pt.some_ok(S.a1.all_in(xs, S.Asn1Visible{}), xs), Equal.cong(PCH.PcCh, Bool, p => pt.pv(p), pt.recl(xs), pt.recr(xs), pt.rec(xs, AL.al.mask_to(o))))

def Laws.teletex_chars(o):
  {==}
