# Proofs for bend-osdev-asn1: the decoder never reads past its buffer. A
# header takes at least its identifier and length octets and leaves its
# contents and what follows inside the input (pw.head_le); so each element's
# span (two octets, and its primitive contents) fits in what it was read
# from, with the octets left after it (pw.dec), by induction on the decoder's
# fuel. Bounds are stated as Bool functions (pw.rb, pw.nb, pw.mb, pw.lb) so
# that a failed decode satisfies them trivially.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ./error.bend as E
import ./number.bend as Nu
import ./tag.bend as T
import ./length.bend as L
import ./node.bend as N
import ./rules.bend as R
import ./encode.bend as En
import ./conform.bend as C
import ./asn1.bend as A
import ./proof_nat.bend as AN
import ./proof_list.bend as AL
import ./proof_u32.bend as AU
import ./proof_enc.bend as PE
import ./proof_num.bend as PN
import ../u32/LAWS.bend as UL
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF.bend as UP
import ../u32/PROOF_order.bend as UOP

def pw.len(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

# the octets a header accounts for: identifier and length (two at least),
# contents, and what follows
def pw.hlen(h: A.A1Head) -> Nat:
  match h:
    case A.A1HEnd{}:
      0n
    case A.A1HEoc{rest}:
      Nat.add(2n, List.length(&2, U32, rest))
    case A.A1HErr{e}:
      0n
    case A.A1HPrim{t, cs, rest}:
      Nat.add(2n, Nat.add(List.length(&2, U32, cs), List.length(&2, U32, rest)))
    case A.A1HDef{t, cs, rest}:
      Nat.add(2n, Nat.add(List.length(&2, U32, cs), List.length(&2, U32, rest)))
    case A.A1HIndef{t, rest}:
      Nat.add(2n, List.length(&2, U32, rest))

# a decoder result's elements and leftover octets fit in k octets
def pw.rb(res: Result<&2, &2, E.Asn1Error, A.A1Out>, +k: Nat) -> Bool:
  match res:
    case Fail{e}:
      True{}
    case Done{A.A1Out{ns, rest}}:
      Nat.is_le(Nat.add(N.a1.span_list(ns), List.length(&2, U32, rest)), k)

# an element result fits in k octets
def pw.nb(res: Result<&2, &2, E.Asn1Error, N.Asn1Node>, +k: Nat) -> Bool:
  match res:
    case Fail{e}:
      True{}
    case Done{x}:
      Nat.is_le(N.a1.span_list([x]), k)

# a number read from t leaves no more than t
def pw.mb(m: Maybe<&2, Nu.A1Num>, t: List<&2, U32>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Nu.A1Num{v, u, rest}}:
      Nat.is_le(List.length(&2, U32, rest), List.length(&2, U32, t))

# length octets read from xs leave less than xs
def pw.lb(l: L.A1Len, xs: List<&2, U32>) -> Bool:
  match l:
    case L.A1LDef{n, u, rest}:
      Nat.is_lt(List.length(&2, U32, rest), List.length(&2, U32, xs))
    case L.A1LIndef{rest}:
      Nat.is_lt(List.length(&2, U32, rest), List.length(&2, U32, xs))
    case L.A1LErr{e}:
      True{}

def pw.le_succ_mono(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  UO.nat_le_trans(a, b, 1n+b, h, AN.an.le_succ(b))

# Spans

def pw.span_cons(x: N.Asn1Node, +ns: List<&2, N.Asn1Node>) -> {N.a1.span_list(Con{x, ns}) == Nat.add(N.a1.span_list([x]), N.a1.span_list(ns)) : Nat}:
  match x:
    case N.Asn1Prim{t, +c}:
      %Equal.sym(Nat, Nat.add(B.Octets.len(c), 0n), B.Octets.len(c), UL.nat_add_zero(B.Octets.len(c))) : {Nat.add(2n, Nat.add(B.Octets.len(c), N.a1.span_list(ns))) == Nat.add(Nat.add(2n, _), N.a1.span_list(ns)) : Nat}
      {==}
    case N.Asn1Cons{t, +xs}:
      %Equal.sym(Nat, Nat.add(N.a1.span_list(xs), 0n), N.a1.span_list(xs), UL.nat_add_zero(N.a1.span_list(xs))) : {Nat.add(2n, Nat.add(N.a1.span_list(xs), N.a1.span_list(ns))) == Nat.add(Nat.add(2n, _), N.a1.span_list(ns)) : Nat}
      {==}

def pw.rb_mono(res: Result<&2, &2, E.Asn1Error, A.A1Out>, +k: Nat, +k2: Nat, +hk: {Nat.is_le(k, k2) == True{} : Bool}, +h: {pw.rb(res, k) == True{} : Bool}) -> {pw.rb(res, k2) == True{} : Bool}:
  match res:
    case Fail{e}:
      {==}
    case Done{A.A1Out{+ns, +rest}}:
      UO.nat_le_trans(Nat.add(N.a1.span_list(ns), List.length(&2, U32, rest)), k, k2, h, hk)

def pw.rb_more(a: Result<&2, &2, E.Asn1Error, N.Asn1Node>, b: Result<&2, &2, E.Asn1Error, A.A1Out>, +k1: Nat, +k2: Nat, +ha: {pw.nb(a, k1) == True{} : Bool}, +hb: {pw.rb(b, k2) == True{} : Bool}) -> {pw.rb(A.a1.more(a, b), Nat.add(k1, k2)) == True{} : Bool}:
  match a b:
    case Fail{e} _:
      {==}
    case Done{x} Fail{e}:
      {==}
    case Done{+x} Done{A.A1Out{+ns, +rest}}:
      +sx = N.a1.span_list([x])
      +sn = N.a1.span_list(ns)
      +lr = List.length(&2, U32, rest)
      %Equal.sym(Nat, N.a1.span_list(Con{x, ns}), Nat.add(sx, sn), pw.span_cons(x, ns)) : {Nat.is_le(Nat.add(_, lr), Nat.add(k1, k2)) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(Nat.add(sx, sn), lr), Nat.add(sx, Nat.add(sn, lr)), UL.nat_add_assoc(sx, sn, lr)) : {Nat.is_le(_, Nat.add(k1, k2)) == True{} : Bool}
      AN.an.le_add2(sx, Nat.add(sn, lr), k1, k2, ha, hb)

def pw.rb_one(a: Result<&2, &2, E.Asn1Error, N.Asn1Node>, +rest: List<&2, U32>, +k1: Nat, +ha: {pw.nb(a, k1) == True{} : Bool}) -> {pw.rb(A.a1.one(a, rest), Nat.add(k1, List.length(&2, U32, rest))) == True{} : Bool}:
  match a:
    case Fail{e}:
      {==}
    case Done{+x}:
      AN.an.le_add_mono_r(List.length(&2, U32, rest), N.a1.span_list([x]), k1, ha)

# element results

def pw.nb_pick(ok: Bool, +t: T.Asn1Tag, +o: B.Octets) -> {pw.nb(A.a1.mk_prim.pick(ok, t, o), N.a1.span_list([N.Asn1Prim{t, o}])) == True{} : Bool}:
  match ok:
    case True{}:
      UL.nat_le_refl(N.a1.span_list([N.Asn1Prim{t, o}]))
    case False{}:
      {==}

def pw.nb_prim(+r: R.Asn1Rules, +t: T.Asn1Tag, +o: B.Octets) -> {pw.nb(A.a1.mk_prim(r, t, o), N.a1.span_list([N.Asn1Prim{t, o}])) == True{} : Bool}:
  pw.nb_pick(R.a1.form_ok(r, t, False{}), t, o)

def pw.nb_set(ok: Bool, +t: T.Asn1Tag, +xs: List<&2, N.Asn1Node>, +k: Nat, +hk: {Nat.is_le(N.a1.span_list(xs), k) == True{} : Bool}) -> {pw.nb(A.a1.mk_cons.set(ok, t, xs), Nat.add(2n, k)) == True{} : Bool}:
  match ok:
    case True{}:
      %Equal.sym(Nat, Nat.add(N.a1.span_list(xs), 0n), N.a1.span_list(xs), UL.nat_add_zero(N.a1.span_list(xs))) : {Nat.is_le(Nat.add(2n, _), Nat.add(2n, k)) == True{} : Bool}
      hk
    case False{}:
      {==}

def pw.nb_form(ok: Bool, +r: R.Asn1Rules, +t: T.Asn1Tag, +xs: List<&2, N.Asn1Node>, +k: Nat, +hk: {Nat.is_le(N.a1.span_list(xs), k) == True{} : Bool}) -> {pw.nb(A.a1.mk_cons.form(ok, r, t, xs), Nat.add(2n, k)) == True{} : Bool}:
  match ok:
    case True{}:
      pw.nb_set(C.a1.set_ok(r, t, xs), t, xs, k, hk)
    case False{}:
      {==}

def pw.nb_cons(+r: R.Asn1Rules, +t: T.Asn1Tag, inner: Result<&2, &2, E.Asn1Error, A.A1Out>, +k: Nat, +h: {pw.rb(inner, k) == True{} : Bool}) -> {pw.nb(A.a1.mk_cons(r, t, inner), Nat.add(2n, k)) == True{} : Bool}:
  match inner:
    case Fail{e}:
      {==}
    case Done{A.A1Out{+xs, +rest}}:
      +sx = N.a1.span_list(xs)
      pw.nb_form(R.a1.form_ok(r, t, True{}), r, t, xs, k, UO.nat_le_trans(sx, Nat.add(sx, List.length(&2, U32, rest)), k, UO.nat_le_add_r(sx, List.length(&2, U32, rest)), h))

# an indefinite constructed element: its contents, and what follows its
# end-of-contents octets, fit in what follows its header
def pw.indef_one(+r: R.Asn1Rules, +t: T.Asn1Tag, inner: Result<&2, &2, E.Asn1Error, A.A1Out>, +k: Nat, +h: {pw.rb(inner, k) == True{} : Bool}) -> {pw.rb(A.a1.one(A.a1.mk_cons(r, t, inner), A.a1.out_rest(inner)), Nat.add(2n, k)) == True{} : Bool}:
  match inner:
    case Fail{e}:
      {==}
    case Done{A.A1Out{+xs, +r2}}:
      +sx = N.a1.span_list(xs)
      +l2 = List.length(&2, U32, r2)
      +hn = pw.nb_form(R.a1.form_ok(r, t, True{}), r, t, xs, sx, UL.nat_le_refl(sx))
      +ho = pw.rb_one(A.a1.mk_cons.form(R.a1.form_ok(r, t, True{}), r, t, xs), r2, Nat.add(2n, sx), hn)
      pw.rb_mono(A.a1.one(A.a1.mk_cons.form(R.a1.form_ok(r, t, True{}), r, t, xs), r2), Nat.add(Nat.add(2n, sx), l2), Nat.add(2n, k), h, ho)

def pw.indef_more(+r: R.Asn1Rules, +t: T.Asn1Tag, +mode: A.A1Mode, +g: Nat, inner: Result<&2, &2, E.Asn1Error, A.A1Out>, +k: Nat, +h: {pw.rb(inner, k) == True{} : Bool}, ih: @ys: List<&2, U32> -> {pw.rb(A.a1.dec(g, r, mode, A.a1.head(r, ys)), List.length(&2, U32, ys)) == True{} : Bool}) -> {pw.rb(A.a1.more(A.a1.mk_cons(r, t, inner), A.a1.dec(g, r, mode, A.a1.head(r, A.a1.out_rest(inner)))), Nat.add(2n, k)) == True{} : Bool}:
  match inner:
    case Fail{e}:
      {==}
    case Done{A.A1Out{+xs, +r2}}:
      +sx = N.a1.span_list(xs)
      +l2 = List.length(&2, U32, r2)
      +hn = pw.nb_form(R.a1.form_ok(r, t, True{}), r, t, xs, sx, UL.nat_le_refl(sx))
      +hm = pw.rb_more(A.a1.mk_cons.form(R.a1.form_ok(r, t, True{}), r, t, xs), A.a1.dec(g, r, mode, A.a1.head(r, r2)), Nat.add(2n, sx), l2, hn, ih(r2))
      pw.rb_mono(A.a1.more(A.a1.mk_cons.form(R.a1.form_ok(r, t, True{}), r, t, xs), A.a1.dec(g, r, mode, A.a1.head(r, r2))), Nat.add(Nat.add(2n, sx), l2), Nat.add(2n, k), h, hm)

# Lists

def pw.drop_le(k: Nat, xs: List<&2, U32>) -> {Nat.is_le(List.length(&2, U32, B.drop(k, xs)), List.length(&2, U32, xs)) == True{} : Bool}:
  match k xs:
    case 0n _:
      UL.nat_le_refl(List.length(&2, U32, xs))
    case 1n+j Nil{}:
      {==}
    case 1n+ +j Con{b, +t}:
      pw.le_succ_mono(List.length(&2, U32, B.drop(j, t)), List.length(&2, U32, t), pw.drop_le(j, t))

def pw.take_drop_len(+n: Nat, +xs: List<&2, U32>) -> {Nat.add(List.length(&2, U32, B.take(n, xs)), List.length(&2, U32, B.drop(n, xs))) == List.length(&2, U32, xs) : Nat}:
  Equal.trans(Nat, Nat.add(List.length(&2, U32, B.take(n, xs)), List.length(&2, U32, B.drop(n, xs))), List.length(&2, U32, List.append(&2, U32, B.take(n, xs), B.drop(n, xs))), List.length(&2, U32, xs), Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, B.take(n, xs), B.drop(n, xs))), Nat.add(List.length(&2, U32, B.take(n, xs)), List.length(&2, U32, B.drop(n, xs))), AL.al.app_len(B.take(n, xs), B.drop(n, xs))), Equal.cong(List<&2, U32>, Nat, z => List.length(&2, U32, z), List.append(&2, U32, B.take(n, xs), B.drop(n, xs)), xs, BL.take_drop(n, xs)))

def pw.lt_le_succ(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_le(1n+a, 0n) == True{} : Bool}, AN.an.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, AN.an.lt0(a)), h)))
    case 0n 1n+q:
      AN.an.le_zero(q)
    case 1n+p 1n+q:
      pw.lt_le_succ(p, q, h)

# Numbers and lengths read leave no more than they were read from

def pw.mb_cons(+x: U32, m: Maybe<&2, Nu.A1Num>, +u: List<&2, U32>, +h: {pw.mb(m, u) == True{} : Bool}) -> {pw.mb(Nu.a1.num_cons(x, m), Con{x, u}) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{Nu.A1Num{v, w, +rest}}:
      pw.le_succ_mono(List.length(&2, U32, rest), List.length(&2, U32, u), h)

def pw.r128_mb(t: List<&2, U32>, more: Bool, k: Nat, +acc: Nat) -> {pw.mb(Nu.a1.r128(t, more, k, acc), t) == True{} : Bool}:
  match t more k:
    case Nil{} False{} _:
      {==}
    case Nil{} True{} _:
      {==}
    case Con{x, +u} False{} _:
      UL.nat_le_refl(1n+List.length(&2, U32, u))
    case Con{x, u} True{} 0n:
      {==}
    case Con{+x, +u} True{} 1n+ +j:
      +v = U32.to_nat(x)
      +ge = Nat.is_le(128n, v)
      +acc2 = Nat.add(Nat.mul(acc, 128n), Nat.sub(v, Bool.pick(Nat, ge, 128n, 0n)))
      pw.mb_cons(x, Nu.a1.r128(u, ge, j, acc2), u, pw.r128_mb(u, ge, j, acc2))

def pw.rbe_pick(ok: Bool, +k: Nat, +xs: List<&2, U32>) -> {pw.mb(Nu.a1.rbe.pick(ok, k, xs), xs) == True{} : Bool}:
  match ok:
    case True{}:
      pw.drop_le(k, xs)
    case False{}:
      {==}

def pw.lbytes(+y: U32, m: Maybe<&2, Nu.A1Num>, +t: List<&2, U32>, +h: {pw.mb(m, t) == True{} : Bool}) -> {pw.lb(L.a1.len.bytes(y, m), Con{y, t}) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{Nu.A1Num{n, u, +r2}}:
      AN.an.le_lt_succ(List.length(&2, U32, r2), List.length(&2, U32, t), h)

def pw.lmany(big: Bool, +k: Nat, +y: U32, +t: List<&2, U32>) -> {pw.lb(L.a1.len.many(big, k, y, t), Con{y, t}) == True{} : Bool}:
  match big:
    case True{}:
      {==}
    case False{}:
      pw.lbytes(y, Nu.a1.rbe(k, t), t, pw.rbe_pick(Nat.is_le(k, List.length(&2, U32, t)), k, t))

def pw.lres(is127: Bool, +k: Nat, +y: U32, +t: List<&2, U32>) -> {pw.lb(L.a1.len.reserved(is127, k, y, t), Con{y, t}) == True{} : Bool}:
  match is127:
    case True{}:
      {==}
    case False{}:
      pw.lmany(Nat.is_lt(Nu.a1.max_octets(), k), k, y, t)

def pw.llong(+k: Nat, +y: U32, +t: List<&2, U32>) -> {pw.lb(L.a1.len.long(k, y, t), Con{y, t}) == True{} : Bool}:
  match k:
    case 0n:
      AN.an.le_lt_succ(List.length(&2, U32, t), List.length(&2, U32, t), UL.nat_le_refl(List.length(&2, U32, t)))
    case 1n+j:
      pw.lres(Nat.is_eq(1n+j, 127n), 1n+j, y, t)

def pw.lfirst(lt: Bool, +v: Nat, +y: U32, +t: List<&2, U32>) -> {pw.lb(L.a1.len.first(lt, v, y, t), Con{y, t}) == True{} : Bool}:
  match lt:
    case True{}:
      AN.an.le_lt_succ(List.length(&2, U32, t), List.length(&2, U32, t), UL.nat_le_refl(List.length(&2, U32, t)))
    case False{}:
      pw.llong(Nat.sub(v, 128n), y, t)

def pw.lread(xs: List<&2, U32>) -> {pw.lb(L.a1.len.read(xs), xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      pw.lfirst(Nat.is_lt(U32.to_nat(y), 128n), U32.to_nat(y), y, t)

# Headers: identifier and length octets, then contents and the rest

def pw.fit(ok: Bool, +t: T.Asn1Tag, cons: Bool, +n: Nat, +rest: List<&2, U32>) -> {Nat.is_le(pw.hlen(A.a1.head.fit(ok, t, cons, n, rest)), Nat.add(2n, List.length(&2, U32, rest))) == True{} : Bool}:
  match ok cons:
    case False{} _:
      AN.an.le_zero(Nat.add(2n, List.length(&2, U32, rest)))
    case True{} False{}:
      %Equal.sym(Nat, Nat.add(List.length(&2, U32, B.take(n, rest)), List.length(&2, U32, B.drop(n, rest))), List.length(&2, U32, rest), pw.take_drop_len(n, rest)) : {Nat.is_le(Nat.add(2n, _), Nat.add(2n, List.length(&2, U32, rest))) == True{} : Bool}
      UL.nat_le_refl(List.length(&2, U32, rest))
    case True{} True{}:
      %Equal.sym(Nat, Nat.add(List.length(&2, U32, B.take(n, rest)), List.length(&2, U32, B.drop(n, rest))), List.length(&2, U32, rest), pw.take_drop_len(n, rest)) : {Nat.is_le(Nat.add(2n, _), Nat.add(2n, List.length(&2, U32, rest))) == True{} : Bool}
      UL.nat_le_refl(List.length(&2, U32, rest))

def pw.min(ok: Bool, +t: T.Asn1Tag, +cons: Bool, +n: Nat, +rest: List<&2, U32>) -> {Nat.is_le(pw.hlen(A.a1.head.min(ok, t, cons, n, rest)), Nat.add(2n, List.length(&2, U32, rest))) == True{} : Bool}:
  match ok:
    case True{}:
      pw.fit(Nat.is_le(n, List.length(&2, U32, rest)), t, cons, n, rest)
    case False{}:
      AN.an.le_zero(Nat.add(2n, List.length(&2, U32, rest)))

def pw.indef(allowed: Bool, cons: Bool, +t: T.Asn1Tag, +rest: List<&2, U32>) -> {Nat.is_le(pw.hlen(A.a1.head.indef(allowed, cons, t, rest)), Nat.add(2n, List.length(&2, U32, rest))) == True{} : Bool}:
  match allowed cons:
    case False{} _:
      AN.an.le_zero(Nat.add(2n, List.length(&2, U32, rest)))
    case True{} False{}:
      AN.an.le_zero(Nat.add(2n, List.length(&2, U32, rest)))
    case True{} True{}:
      UL.nat_le_refl(Nat.add(2n, List.length(&2, U32, rest)))

def pw.hl_len(+r: R.Asn1Rules, +t: T.Asn1Tag, +cons: Bool, l: L.A1Len, +xs: List<&2, U32>, +hl: {pw.lb(l, xs) == True{} : Bool}) -> {Nat.is_le(pw.hlen(A.a1.head.len(r, t, cons, l)), Nat.add(1n, List.length(&2, U32, xs))) == True{} : Bool}:
  match l:
    case L.A1LErr{e}:
      AN.an.le_zero(Nat.add(1n, List.length(&2, U32, xs)))
    case L.A1LIndef{+rest}:
      UO.nat_le_trans(pw.hlen(A.a1.head.indef(R.Asn1Rules.indefinite(r), cons, t, rest)), Nat.add(2n, List.length(&2, U32, rest)), Nat.add(1n, List.length(&2, U32, xs)), pw.indef(R.Asn1Rules.indefinite(r), cons, t, rest), pw.lt_le_succ(List.length(&2, U32, rest), List.length(&2, U32, xs), hl))
    case L.A1LDef{+n, +u, +rest}:
      +ok = R.a1.when(R.Asn1Rules.min_length(r), Bool.and(L.a1.len_ok(n), Nu.a1.leq(L.a1.len_bytes(n), u)))
      UO.nat_le_trans(pw.hlen(A.a1.head.min(ok, t, cons, n, rest)), Nat.add(2n, List.length(&2, U32, rest)), Nat.add(1n, List.length(&2, U32, xs)), pw.min(ok, t, cons, n, rest), pw.lt_le_succ(List.length(&2, U32, rest), List.length(&2, U32, xs), hl))

def pw.eoc2(z: Bool, +t: List<&2, U32>) -> {Nat.is_le(pw.hlen(A.a1.head.eoc2(z, t)), Nat.add(2n, List.length(&2, U32, t))) == True{} : Bool}:
  match z:
    case True{}:
      UL.nat_le_refl(Nat.add(2n, List.length(&2, U32, t)))
    case False{}:
      AN.an.le_zero(Nat.add(2n, List.length(&2, U32, t)))

def pw.eoc(rest: List<&2, U32>) -> {Nat.is_le(pw.hlen(A.a1.head.eoc(rest)), Nat.add(1n, List.length(&2, U32, rest))) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      pw.eoc2(Nat.is_eq(U32.to_nat(y), 0n), t)

def pw.res(u0: Bool, +r: R.Asn1Rules, +c: T.Asn1Class, cons: Bool, +n: Nat, +rest: List<&2, U32>) -> {Nat.is_le(pw.hlen(A.a1.head.res(u0, r, c, cons, n, rest)), Nat.add(1n, List.length(&2, U32, rest))) == True{} : Bool}:
  match u0 cons:
    case True{} False{}:
      pw.eoc(rest)
    case True{} True{}:
      AN.an.le_zero(Nat.add(1n, List.length(&2, U32, rest)))
    case False{} False{}:
      pw.hl_len(r, T.Asn1Tag{c, n}, False{}, L.a1.len.read(rest), rest, pw.lread(rest))
    case False{} True{}:
      pw.hl_len(r, T.Asn1Tag{c, n}, True{}, L.a1.len.read(rest), rest, pw.lread(rest))

def pw.tag2(ok: Bool, +r: R.Asn1Rules, +c: T.Asn1Class, +cons: Bool, +n: Nat, +rest: List<&2, U32>) -> {Nat.is_le(pw.hlen(A.a1.head.tag2(ok, r, c, cons, n, rest)), Nat.add(1n, List.length(&2, U32, rest))) == True{} : Bool}:
  match ok:
    case True{}:
      pw.res(En.a1.is_univ0(c, n), r, c, cons, n, rest)
    case False{}:
      AN.an.le_zero(Nat.add(1n, List.length(&2, U32, rest)))

def pw.num(+r: R.Asn1Rules, +c: T.Asn1Class, +cons: Bool, +x: U32, m: Maybe<&2, Nu.A1Num>, +t: List<&2, U32>, +hm: {pw.mb(m, t) == True{} : Bool}) -> {Nat.is_le(pw.hlen(A.a1.head.num(r, c, cons, x, m)), Nat.add(1n, List.length(&2, U32, t))) == True{} : Bool}:
  match m:
    case None{}:
      AN.an.le_zero(Nat.add(1n, List.length(&2, U32, t)))
    case Some{Nu.A1Num{+n, +u, +rest}}:
      +ids : List<&2, U32> = Con{x, u}
      UO.nat_le_trans(pw.hlen(A.a1.head.tag(r, c, cons, n, ids, rest)), Nat.add(1n, List.length(&2, U32, rest)), Nat.add(1n, List.length(&2, U32, t)), pw.tag2(Nu.a1.leq(T.a1.id_bytes(c, cons, n), ids), r, c, cons, n, rest), hm)

def pw.hi(hi: Bool, +r: R.Asn1Rules, +c: T.Asn1Class, +cons: Bool, +low: Nat, +x: U32, +t: List<&2, U32>) -> {Nat.is_le(pw.hlen(A.a1.head.hi(hi, r, c, cons, low, x, t)), Nat.add(1n, List.length(&2, U32, t))) == True{} : Bool}:
  match hi:
    case True{}:
      pw.num(r, c, cons, x, Nu.a1.r128(t, True{}, Nu.a1.max_octets(), 0n), t, pw.r128_mb(t, True{}, Nu.a1.max_octets(), 0n))
    case False{}:
      pw.tag2(Nu.a1.leq(T.a1.id_bytes(c, cons, low), [x]), r, c, cons, low, t)

def pw.id(+r: R.Asn1Rules, i: T.A1Id1, +x: U32, +t: List<&2, U32>) -> {Nat.is_le(pw.hlen(A.a1.head.id(r, i, x, t)), Nat.add(1n, List.length(&2, U32, t))) == True{} : Bool}:
  match i:
    case T.A1Id1{+c, +cons, +low}:
      pw.hi(Nat.is_eq(low, 31n), r, c, cons, low, x, t)

# a header fits in the octets it was read from
def pw.head0_le(+r: R.Asn1Rules, xs: List<&2, U32>) -> {Nat.is_le(pw.hlen(A.a1.head0(r, xs)), List.length(&2, U32, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      pw.id(r, T.a1.id1(U32.to_nat(x)), x, t)

# The final checks keep a header within its octets

def pw.imp(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      True{}

def pw.imp_i(a: Bool, -b: Bool, h: @e: {a == True{} : Bool} -> {b == True{} : Bool}) -> {pw.imp(a, b) == True{} : Bool}:
  match a:
    case True{}:
      h({==})
    case False{}:
      {==}

def pw.lb_ne.go(lt: Bool, +n: Nat, +hl: {Nat.is_lt(n, 128n) == lt : Bool}) -> {Nat.is_le(1n, List.length(&2, U32, L.a1.len_bytes(n))) == True{} : Bool}:
  match lt:
    case True{}:
      %Equal.sym(List<&2, U32>, L.a1.len_bytes(n), [Nu.a1.b(n)], PN.pn.lb_short(n, hl)) : {Nat.is_le(1n, List.length(&2, U32, _)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(List<&2, U32>, L.a1.len_bytes(n), Con{Nu.a1.b(Nat.add(128n, List.length(&2, U32, Nu.a1.be(n)))), Nu.a1.be(n)}, PN.pn.lb_long(n, hl)) : {Nat.is_le(1n, List.length(&2, U32, _)) == True{} : Bool}
      AN.an.le_zero(List.length(&2, U32, Nu.a1.be(n)))

def pw.lb_ne(+n: Nat) -> {Nat.is_le(1n, List.length(&2, U32, L.a1.len_bytes(n))) == True{} : Bool}:
  pw.lb_ne.go(Nat.is_lt(n, 128n), n, {==})

# the octets before the contents are at least two
def pw.hdr2(+c: T.Asn1Class, +cons: Bool, +n: Nat, +l: Nat) -> {Nat.is_le(2n, List.length(&2, U32, A.a1.hdr(c, cons, n, l))) == True{} : Bool}:
  +id = T.a1.id_bytes(c, cons, n)
  +lb = L.a1.len_bytes(l)
  %Equal.sym(Nat, List.length(&2, U32, List.append(&2, U32, id, lb)), Nat.add(List.length(&2, U32, id), List.length(&2, U32, lb)), AL.al.app_len(id, lb)) : {Nat.is_le(2n, _) == True{} : Bool}
  AN.an.le_add2(1n, 1n, List.length(&2, U32, id), List.length(&2, U32, lb), PE.pe.id_ne(c, cons, n), pw.lb_ne(l))

# when the canonical check passes, the contents start two octets in or more
def pw.cbound(+c: T.Asn1Class, +cons: Bool, +n: Nat, +l: Nat, +xs: List<&2, U32>, +e: {A.a1.canon.ok(c, cons, n, l, xs) == True{} : Bool}) -> {Nat.is_le(Nat.add(2n, List.length(&2, U32, B.drop(List.length(&2, U32, A.a1.hdr(c, cons, n, l)), xs))), List.length(&2, U32, xs)) == True{} : Bool}:
  +hd = A.a1.hdr(c, cons, n, l)
  +k = List.length(&2, U32, hd)
  +ld = List.length(&2, U32, B.drop(k, xs))
  +a1 = Bool.not(En.a1.is_univ0(c, n))
  +a0 = T.a1.id_ok(n)
  +a2 = L.a1.len_ok(l)
  +a3 = Nu.a1.leq(hd, B.take(k, xs))
  +a4 = Nat.is_le(l, ld)
  +e1 = AN.an.and_r(a1, Bool.and(a0, Bool.and(a2, Bool.and(a3, a4))), e)
  +e2 = AN.an.and_r(a0, Bool.and(a2, Bool.and(a3, a4)), e1)
  +e3 = AN.an.and_r(a2, Bool.and(a3, a4), e2)
  +eq = AU.au.leq_sound(hd, B.take(k, xs), AN.an.and_l(a3, a4, e3))
  +ht = Equal.cong(List<&2, U32>, Nat, z => List.length(&2, U32, z), hd, B.take(k, xs), eq)
  %pw.take_drop_len(k, xs) : {Nat.is_le(Nat.add(2n, ld), _) == True{} : Bool}
  %ht : {Nat.is_le(Nat.add(2n, ld), Nat.add(_, ld)) == True{} : Bool}
  AN.an.le_add_mono_r(ld, 2n, k, pw.hdr2(c, cons, n, l))

def pw.cmk(ok: Bool, +t: T.Asn1Tag, cons: Bool, +k: Nat, +l: Nat, +xs: List<&2, U32>, +hb: {pw.imp(ok, Nat.is_le(Nat.add(2n, List.length(&2, U32, B.drop(k, xs))), List.length(&2, U32, xs))) == True{} : Bool}) -> {Nat.is_le(pw.hlen(A.a1.canon.mk(ok, t, cons, k, l, xs)), List.length(&2, U32, xs)) == True{} : Bool}:
  match ok cons:
    case False{} _:
      AN.an.le_zero(List.length(&2, U32, xs))
    case True{} False{}:
      +d = B.drop(k, xs)
      %Equal.sym(Nat, Nat.add(List.length(&2, U32, B.take(l, d)), List.length(&2, U32, B.drop(l, d))), List.length(&2, U32, d), pw.take_drop_len(l, d)) : {Nat.is_le(Nat.add(2n, _), List.length(&2, U32, xs)) == True{} : Bool}
      hb
    case True{} True{}:
      +d = B.drop(k, xs)
      %Equal.sym(Nat, Nat.add(List.length(&2, U32, B.take(l, d)), List.length(&2, U32, B.drop(l, d))), List.length(&2, U32, d), pw.take_drop_len(l, d)) : {Nat.is_le(Nat.add(2n, _), List.length(&2, U32, xs)) == True{} : Bool}
      hb

def pw.canon_le(+xs: List<&2, U32>, h: A.A1Head, +hh: {Nat.is_le(pw.hlen(h), List.length(&2, U32, xs)) == True{} : Bool}) -> {Nat.is_le(pw.hlen(A.a1.canon(xs, h)), List.length(&2, U32, xs)) == True{} : Bool}:
  match h:
    case A.A1HPrim{T.Asn1Tag{+c, +n}, +cs, rest}:
      +l = List.length(&2, U32, cs)
      +k = List.length(&2, U32, A.a1.hdr(c, False{}, n, l))
      +ok = A.a1.canon.ok(c, False{}, n, l, xs)
      pw.cmk(ok, T.Asn1Tag{c, n}, False{}, k, l, xs, pw.imp_i(ok, Nat.is_le(Nat.add(2n, List.length(&2, U32, B.drop(k, xs))), List.length(&2, U32, xs)), e => pw.cbound(c, False{}, n, l, xs, e)))
    case A.A1HDef{T.Asn1Tag{+c, +n}, +cs, rest}:
      +l = List.length(&2, U32, cs)
      +k = List.length(&2, U32, A.a1.hdr(c, True{}, n, l))
      +ok = A.a1.canon.ok(c, True{}, n, l, xs)
      pw.cmk(ok, T.Asn1Tag{c, n}, True{}, k, l, xs, pw.imp_i(ok, Nat.is_le(Nat.add(2n, List.length(&2, U32, B.drop(k, xs))), List.length(&2, U32, xs)), e => pw.cbound(c, True{}, n, l, xs, e)))
    case A.A1HEnd{}:
      hh
    case A.A1HEoc{rest}:
      hh
    case A.A1HErr{e}:
      hh
    case A.A1HIndef{t, rest}:
      hh

def pw.ioff(a: Bool, h: A.A1Head, +xs: List<&2, U32>, +hh: {Nat.is_le(pw.hlen(h), List.length(&2, U32, xs)) == True{} : Bool}) -> {Nat.is_le(pw.hlen(A.a1.head.indef_off(a, h)), List.length(&2, U32, xs)) == True{} : Bool}:
  match a:
    case True{}:
      hh
    case False{}:
      match h:
        case A.A1HIndef{t, rest}:
          AN.an.le_zero(List.length(&2, U32, xs))
        case A.A1HEnd{}:
          hh
        case A.A1HEoc{rest}:
          hh
        case A.A1HErr{e}:
          hh
        case A.A1HPrim{t, cs, rest}:
          hh
        case A.A1HDef{t, cs, rest}:
          hh

def pw.fin2(m: Bool, +xs: List<&2, U32>, h: A.A1Head, +hh: {Nat.is_le(pw.hlen(h), List.length(&2, U32, xs)) == True{} : Bool}) -> {Nat.is_le(pw.hlen(A.a1.head.fin2(m, xs, h)), List.length(&2, U32, xs)) == True{} : Bool}:
  match m:
    case True{}:
      pw.canon_le(xs, h, hh)
    case False{}:
      hh

def pw.nend(xs: List<&2, U32>, h: A.A1Head, +hh: {Nat.is_le(pw.hlen(h), List.length(&2, U32, xs)) == True{} : Bool}) -> {Nat.is_le(pw.hlen(A.a1.head.nend(xs, h)), List.length(&2, U32, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hh
    case Con{y, +t}:
      match h:
        case A.A1HEnd{}:
          AN.an.le_zero(1n+List.length(&2, U32, t))
        case A.A1HEoc{rest}:
          hh
        case A.A1HErr{e}:
          hh
        case A.A1HPrim{u, cs, rest}:
          hh
        case A.A1HDef{u, cs, rest}:
          hh
        case A.A1HIndef{u, rest}:
          hh

def pw.head_le(+r: R.Asn1Rules, +xs: List<&2, U32>) -> {Nat.is_le(pw.hlen(A.a1.head(r, xs)), List.length(&2, U32, xs)) == True{} : Bool}:
  +h1 = A.a1.head.indef_off(R.Asn1Rules.indefinite(r), A.a1.head0(r, xs))
  +h2 = A.a1.head.fin(r, xs, A.a1.head0(r, xs))
  pw.nend(xs, h2, pw.fin2(R.Asn1Rules.min_length(r), xs, h1, pw.ioff(R.Asn1Rules.indefinite(r), A.a1.head0(r, xs), xs, pw.head0_le(r, xs))))

# Elements

def pw.olen_of(+cs: List<&2, U32>) -> {B.Octets.len(B.Octets.of_list(cs)) == List.length(&2, U32, cs) : Nat}:
  Equal.trans(Nat, B.Octets.len(B.Octets.of_list(cs)), List.length(&2, U32, B.Octets.to_list(B.Octets.of_list(cs))), List.length(&2, U32, cs), BL.octets_len_list(B.Octets.of_list(cs)), Equal.trans(Nat, List.length(&2, U32, B.Octets.to_list(B.Octets.of_list(cs))), List.length(&2, U32, B.mask(cs)), List.length(&2, U32, cs), Equal.cong(List<&2, U32>, Nat, z => List.length(&2, U32, z), B.Octets.to_list(B.Octets.of_list(cs)), B.mask(cs), BL.octets_to_of(cs)), AL.al.mask_len(cs)))

# a primitive element's span and what follows it fit where its header said
def pw.prim_le(+t: T.Asn1Tag, +cs: List<&2, U32>, +rest: List<&2, U32>, +xs: List<&2, U32>, +hh: {Nat.is_le(Nat.add(2n, Nat.add(List.length(&2, U32, cs), List.length(&2, U32, rest))), List.length(&2, U32, xs)) == True{} : Bool}) -> {Nat.is_le(Nat.add(N.a1.span_list([N.Asn1Prim{t, B.Octets.of_list(cs)}]), List.length(&2, U32, rest)), List.length(&2, U32, xs)) == True{} : Bool}:
  +lo = B.Octets.len(B.Octets.of_list(cs))
  %Equal.sym(Nat, Nat.add(lo, 0n), lo, UL.nat_add_zero(lo)) : {Nat.is_le(Nat.add(Nat.add(2n, _), List.length(&2, U32, rest)), List.length(&2, U32, xs)) == True{} : Bool}
  %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(cs)), List.length(&2, U32, cs), pw.olen_of(cs)) : {Nat.is_le(Nat.add(Nat.add(2n, _), List.length(&2, U32, rest)), List.length(&2, U32, xs)) == True{} : Bool}
  hh

def pw.eoc_le(+rest: List<&2, U32>, +xs: List<&2, U32>, +hh: {Nat.is_le(Nat.add(2n, List.length(&2, U32, rest)), List.length(&2, U32, xs)) == True{} : Bool}) -> {Nat.is_le(List.length(&2, U32, rest), List.length(&2, U32, xs)) == True{} : Bool}:
  UO.nat_le_trans(List.length(&2, U32, rest), Nat.add(2n, List.length(&2, U32, rest)), List.length(&2, U32, xs), UL.nat_le_add(List.length(&2, U32, rest), 2n), hh)

# whatever the decoder answers from a header within xs fits in xs
def pw.dec(f: Nat, +r: R.Asn1Rules, mode: A.A1Mode, h: A.A1Head, +xs: List<&2, U32>, +hh: {Nat.is_le(pw.hlen(h), List.length(&2, U32, xs)) == True{} : Bool}) -> {pw.rb(A.a1.dec(f, r, mode, h), List.length(&2, U32, xs)) == True{} : Bool}:
  match f:
    case 0n:
      {==}
    case 1n+ +g:
      match mode:
        case A.A1One{}:
          match h:
            case A.A1HEnd{}:
              {==}
            case A.A1HEoc{rest}:
              {==}
            case A.A1HErr{e}:
              {==}
            case A.A1HPrim{+t, +cs, +rest}:
              +o = B.Octets.of_list(cs)
              +sp = N.a1.span_list([N.Asn1Prim{t, o}])
              pw.rb_mono(A.a1.one(A.a1.mk_prim(r, t, o), rest), Nat.add(sp, List.length(&2, U32, rest)), List.length(&2, U32, xs), pw.prim_le(t, cs, rest, xs, hh), pw.rb_one(A.a1.mk_prim(r, t, o), rest, sp, pw.nb_prim(r, t, o)))
            case A.A1HDef{+t, +cs, +rest}:
              +inner = A.a1.dec(g, r, A.A1All{}, A.a1.head(r, cs))
              +ih = pw.dec(g, r, A.A1All{}, A.a1.head(r, cs), cs, pw.head_le(r, cs))
              +lc = List.length(&2, U32, cs)
              pw.rb_mono(A.a1.one(A.a1.mk_cons(r, t, inner), rest), Nat.add(Nat.add(2n, lc), List.length(&2, U32, rest)), List.length(&2, U32, xs), hh, pw.rb_one(A.a1.mk_cons(r, t, inner), rest, Nat.add(2n, lc), pw.nb_cons(r, t, inner, lc, ih)))
            case A.A1HIndef{+t, +rest}:
              +inner = A.a1.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest))
              +ih = pw.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest), rest, pw.head_le(r, rest))
              pw.rb_mono(A.a1.one(A.a1.mk_cons(r, t, inner), A.a1.out_rest(inner)), Nat.add(2n, List.length(&2, U32, rest)), List.length(&2, U32, xs), hh, pw.indef_one(r, t, inner, List.length(&2, U32, rest), ih))
        case A.A1All{}:
          match h:
            case A.A1HEnd{}:
              AN.an.le_zero(List.length(&2, U32, xs))
            case A.A1HEoc{rest}:
              {==}
            case A.A1HErr{e}:
              {==}
            case A.A1HPrim{+t, +cs, +rest}:
              +o = B.Octets.of_list(cs)
              +sp = N.a1.span_list([N.Asn1Prim{t, o}])
              +cont = A.a1.dec(g, r, A.A1All{}, A.a1.head(r, rest))
              +ihr = pw.dec(g, r, A.A1All{}, A.a1.head(r, rest), rest, pw.head_le(r, rest))
              pw.rb_mono(A.a1.more(A.a1.mk_prim(r, t, o), cont), Nat.add(sp, List.length(&2, U32, rest)), List.length(&2, U32, xs), pw.prim_le(t, cs, rest, xs, hh), pw.rb_more(A.a1.mk_prim(r, t, o), cont, sp, List.length(&2, U32, rest), pw.nb_prim(r, t, o), ihr))
            case A.A1HDef{+t, +cs, +rest}:
              +inner = A.a1.dec(g, r, A.A1All{}, A.a1.head(r, cs))
              +ih = pw.dec(g, r, A.A1All{}, A.a1.head(r, cs), cs, pw.head_le(r, cs))
              +cont = A.a1.dec(g, r, A.A1All{}, A.a1.head(r, rest))
              +ihr = pw.dec(g, r, A.A1All{}, A.a1.head(r, rest), rest, pw.head_le(r, rest))
              +lc = List.length(&2, U32, cs)
              pw.rb_mono(A.a1.more(A.a1.mk_cons(r, t, inner), cont), Nat.add(Nat.add(2n, lc), List.length(&2, U32, rest)), List.length(&2, U32, xs), hh, pw.rb_more(A.a1.mk_cons(r, t, inner), cont, Nat.add(2n, lc), List.length(&2, U32, rest), pw.nb_cons(r, t, inner, lc, ih), ihr))
            case A.A1HIndef{+t, +rest}:
              +inner = A.a1.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest))
              +ih = pw.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest), rest, pw.head_le(r, rest))
              pw.rb_mono(A.a1.more(A.a1.mk_cons(r, t, inner), A.a1.dec(g, r, A.A1All{}, A.a1.head(r, A.a1.out_rest(inner)))), Nat.add(2n, List.length(&2, U32, rest)), List.length(&2, U32, xs), hh, pw.indef_more(r, t, A.A1All{}, g, inner, List.length(&2, U32, rest), ih, +ys => pw.dec(g, r, A.A1All{}, A.a1.head(r, ys), ys, pw.head_le(r, ys))))
        case A.A1Eoc{}:
          match h:
            case A.A1HEnd{}:
              {==}
            case A.A1HEoc{+rest}:
              pw.eoc_le(rest, xs, hh)
            case A.A1HErr{e}:
              {==}
            case A.A1HPrim{+t, +cs, +rest}:
              +o = B.Octets.of_list(cs)
              +sp = N.a1.span_list([N.Asn1Prim{t, o}])
              +cont = A.a1.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest))
              +ihr = pw.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest), rest, pw.head_le(r, rest))
              pw.rb_mono(A.a1.more(A.a1.mk_prim(r, t, o), cont), Nat.add(sp, List.length(&2, U32, rest)), List.length(&2, U32, xs), pw.prim_le(t, cs, rest, xs, hh), pw.rb_more(A.a1.mk_prim(r, t, o), cont, sp, List.length(&2, U32, rest), pw.nb_prim(r, t, o), ihr))
            case A.A1HDef{+t, +cs, +rest}:
              +inner = A.a1.dec(g, r, A.A1All{}, A.a1.head(r, cs))
              +ih = pw.dec(g, r, A.A1All{}, A.a1.head(r, cs), cs, pw.head_le(r, cs))
              +cont = A.a1.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest))
              +ihr = pw.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest), rest, pw.head_le(r, rest))
              +lc = List.length(&2, U32, cs)
              pw.rb_mono(A.a1.more(A.a1.mk_cons(r, t, inner), cont), Nat.add(Nat.add(2n, lc), List.length(&2, U32, rest)), List.length(&2, U32, xs), hh, pw.rb_more(A.a1.mk_cons(r, t, inner), cont, Nat.add(2n, lc), List.length(&2, U32, rest), pw.nb_cons(r, t, inner, lc, ih), ihr))
            case A.A1HIndef{+t, +rest}:
              +inner = A.a1.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest))
              +ih = pw.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest), rest, pw.head_le(r, rest))
              pw.rb_mono(A.a1.more(A.a1.mk_cons(r, t, inner), A.a1.dec(g, r, A.A1Eoc{}, A.a1.head(r, A.a1.out_rest(inner)))), Nat.add(2n, List.length(&2, U32, rest)), List.length(&2, U32, xs), hh, pw.indef_more(r, t, A.A1Eoc{}, g, inner, List.length(&2, U32, rest), ih, +ys => pw.dec(g, r, A.A1Eoc{}, A.a1.head(r, ys), ys, pw.head_le(r, ys))))

# the decoder from the start of xs
def pw.run(+r: R.Asn1Rules, mode: A.A1Mode, +xs: List<&2, U32>) -> {pw.rb(A.a1.run(r, mode, xs), List.length(&2, U32, xs)) == True{} : Bool}:
  pw.dec(Nat.add(1n, List.length(&2, U32, xs)), r, mode, A.a1.head(r, xs), xs, pw.head_le(r, xs))

# From the decoder's answer to the public decoders'

def pw.rdisc(r: Result<&2, &2, E.Asn1Error, N.Asn1Node>) -> Type:
  match r:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def pw.fd(-x: E.Asn1Error, -y: N.Asn1Node, e: {Fail{x} == Done{y} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}) -> Empty:
  %e : pw.rdisc(_)
  Unit{}

def pw.dval(z: Result<&2, &2, E.Asn1Error, N.Asn1Node>, d: N.Asn1Node) -> N.Asn1Node:
  match z:
    case Fail{x}:
      d
    case Done{v}:
      v

def pw.end_inv(ok: Bool, +m: N.Asn1Node, -n: N.Asn1Node, +e: {A.a1.top.end(ok, m) == Done{n} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}) -> {m == n : N.Asn1Node}:
  match ok:
    case True{}:
      Equal.cong(Result<&2, &2, E.Asn1Error, N.Asn1Node>, N.Asn1Node, z => pw.dval(z, m), Done{m}, Done{n}, e)
    case False{}:
      Empty.absurd({m == n : N.Asn1Node}, pw.fd(E.Asn1Trailing{}, n, e))

def pw.top_inv(+r: R.Asn1Rules, res: Result<&2, &2, E.Asn1Error, A.A1Out>, -n: N.Asn1Node, +k: Nat, +hrb: {pw.rb(res, k) == True{} : Bool}, +e: {A.a1.top(r, res) == Done{n} : Result<&2, &2, E.Asn1Error, N.Asn1Node>}) -> {Nat.is_le(N.a1.span_list([n]), k) == True{} : Bool}:
  match res:
    case Fail{x}:
      Empty.absurd({Nat.is_le(N.a1.span_list([n]), k) == True{} : Bool}, pw.fd(x, n, e))
    case Done{A.A1Out{Nil{}, rest}}:
      Empty.absurd({Nat.is_le(N.a1.span_list([n]), k) == True{} : Bool}, pw.fd(E.Asn1Truncated{}, n, e))
    case Done{A.A1Out{Con{m, Con{m2, ms}}, rest}}:
      Empty.absurd({Nat.is_le(N.a1.span_list([n]), k) == True{} : Bool}, pw.fd(E.Asn1Truncated{}, n, e))
    case Done{A.A1Out{Con{+m, Nil{}}, Nil{}}}:
      %Equal.cong(Result<&2, &2, E.Asn1Error, N.Asn1Node>, N.Asn1Node, z => pw.dval(z, m), Done{m}, Done{n}, e) : {Nat.is_le(N.a1.span_list([_]), k) == True{} : Bool}
      %UL.nat_add_zero(N.a1.span_list([m])) : {Nat.is_le(_, k) == True{} : Bool}
      hrb
    case Done{A.A1Out{Con{+m, Nil{}}, Con{y, +t}}}:
      %pw.end_inv(R.Asn1Rules.trailing(r), m, n, e) : {Nat.is_le(N.a1.span_list([_]), k) == True{} : Bool}
      UO.nat_le_trans(N.a1.span_list([m]), Nat.add(N.a1.span_list([m]), 1n+List.length(&2, U32, t)), k, UO.nat_le_add_r(N.a1.span_list([m]), 1n+List.length(&2, U32, t)), hrb)

def pw.prdisc(r: Result<&2, &2, E.Asn1Error, A.Asn1Read>) -> Type:
  match r:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def pw.pfd(-x: E.Asn1Error, -y: A.Asn1Read, e: {Fail{x} == Done{y} : Result<&2, &2, E.Asn1Error, A.Asn1Read>}) -> Empty:
  %e : pw.prdisc(_)
  Unit{}

def pw.read_node(z: Result<&2, &2, E.Asn1Error, A.Asn1Read>, d: N.Asn1Node) -> N.Asn1Node:
  match z:
    case Fail{x}:
      d
    case Done{A.Asn1Read{v, o}}:
      v

def pw.read_rest(z: Result<&2, &2, E.Asn1Error, A.Asn1Read>) -> B.Octets:
  match z:
    case Fail{x}:
      B.Octets.empty()
    case Done{A.Asn1Read{v, o}}:
      o

def pw.read_inv(res: Result<&2, &2, E.Asn1Error, A.A1Out>, -n: N.Asn1Node, -rest: B.Octets, +k: Nat, +hrb: {pw.rb(res, k) == True{} : Bool}, +e: {A.a1.read.out(res) == Done{A.Asn1Read{n, rest}} : Result<&2, &2, E.Asn1Error, A.Asn1Read>}) -> {Nat.is_le(Nat.add(N.a1.span_list([n]), B.Octets.len(rest)), k) == True{} : Bool}:
  match res:
    case Fail{x}:
      Empty.absurd({Nat.is_le(Nat.add(N.a1.span_list([n]), B.Octets.len(rest)), k) == True{} : Bool}, pw.pfd(x, A.Asn1Read{n, rest}, e))
    case Done{A.A1Out{Nil{}, rl}}:
      Empty.absurd({Nat.is_le(Nat.add(N.a1.span_list([n]), B.Octets.len(rest)), k) == True{} : Bool}, pw.pfd(E.Asn1Truncated{}, A.Asn1Read{n, rest}, e))
    case Done{A.A1Out{Con{+m, +ms}, +rl}}:
      +got : Result<&2, &2, E.Asn1Error, A.Asn1Read> = Done{A.Asn1Read{m, B.Octets.of_list(rl)}}
      %Equal.cong(Result<&2, &2, E.Asn1Error, A.Asn1Read>, N.Asn1Node, z => pw.read_node(z, m), got, Done{A.Asn1Read{n, rest}}, e) : {Nat.is_le(Nat.add(N.a1.span_list([_]), B.Octets.len(rest)), k) == True{} : Bool}
      %Equal.cong(Result<&2, &2, E.Asn1Error, A.Asn1Read>, B.Octets, z => pw.read_rest(z), got, Done{A.Asn1Read{n, rest}}, e) : {Nat.is_le(Nat.add(N.a1.span_list([m]), B.Octets.len(_)), k) == True{} : Bool}
      %Equal.sym(Nat, B.Octets.len(B.Octets.of_list(rl)), List.length(&2, U32, rl), pw.olen_of(rl)) : {Nat.is_le(Nat.add(N.a1.span_list([m]), _), k) == True{} : Bool}
      +sm = N.a1.span_list([m])
      +ss = N.a1.span_list(ms)
      +lr = List.length(&2, U32, rl)
      +h1 = Equal.trans(Bool, Nat.is_le(Nat.add(Nat.add(sm, ss), lr), k), Nat.is_le(Nat.add(N.a1.span_list(Con{m, ms}), lr), k), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(Nat.add(z, lr), k), Nat.add(sm, ss), N.a1.span_list(Con{m, ms}), Equal.sym(Nat, N.a1.span_list(Con{m, ms}), Nat.add(sm, ss), pw.span_cons(m, ms))), hrb)
      UO.nat_le_trans(Nat.add(sm, lr), Nat.add(Nat.add(sm, ss), lr), k, AN.an.le_add_mono_r(lr, sm, Nat.add(sm, ss), UO.nat_le_add_r(sm, ss)), h1)

def pw.ardisc(r: Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>) -> Type:
  match r:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def pw.afd(-x: E.Asn1Error, -y: List<&2, N.Asn1Node>, e: {Fail{x} == Done{y} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}) -> Empty:
  %e : pw.ardisc(_)
  Unit{}

def pw.aval(z: Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>, d: List<&2, N.Asn1Node>) -> List<&2, N.Asn1Node>:
  match z:
    case Fail{x}:
      d
    case Done{v}:
      v

def pw.all_inv(res: Result<&2, &2, E.Asn1Error, A.A1Out>, -ns: List<&2, N.Asn1Node>, +k: Nat, +hrb: {pw.rb(res, k) == True{} : Bool}, +e: {A.a1.all.out(res) == Done{ns} : Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>}) -> {Nat.is_le(N.a1.span_list(ns), k) == True{} : Bool}:
  match res:
    case Fail{x}:
      Empty.absurd({Nat.is_le(N.a1.span_list(ns), k) == True{} : Bool}, pw.afd(x, ns, e))
    case Done{A.A1Out{+ms, +rl}}:
      %Equal.cong(Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>, List<&2, N.Asn1Node>, z => pw.aval(z, ms), Done{ms}, Done{ns}, e) : {Nat.is_le(N.a1.span_list(_), k) == True{} : Bool}
      UO.nat_le_trans(N.a1.span_list(ms), Nat.add(N.a1.span_list(ms), List.length(&2, U32, rl)), k, UO.nat_le_add_r(N.a1.span_list(ms), List.length(&2, U32, rl)), hrb)

def pw.blen(+b: B.Octets) -> {List.length(&2, U32, B.Octets.to_list(b)) == B.Octets.len(b) : Nat}:
  Equal.sym(Nat, B.Octets.len(b), List.length(&2, U32, B.Octets.to_list(b)), BL.octets_len_list(b))
