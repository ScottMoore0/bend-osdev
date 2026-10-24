# Proofs for bend-osdev-asn1: the decoder only splits its input. Every
# reader of a header (identifier octets, length octets, the canonical check)
# leaves its contents and what follows as the input's last octets (ps.hs),
# and the decoder leaves, after the elements it read, the input's last
# octets (ps.dec, by induction on the fuel), so an element read is the
# input's first octets and the rest the remaining ones (ps.read: law
# read_split), the elements of a run join back to the input (ps.go: law
# read_all_split), and the contents octets Asn1.contents answers are a
# slice of an element's octets (ps.contents: law contents_within), as
# every header is read only from octets it then cuts.
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
import ./asn1.bend as A
import ./proof_nat.bend as AN
import ./proof_list.bend as AL
import ./proof_oct.bend as OA
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP

# ys is a suffix of xs: the octets after some others
def ps.suf(ys: List<&2, U32>, xs: List<&2, U32>) -> Type:
  Sigma<&1, &1, List<&2, U32>, p => {List.append(&2, U32, p, ys) == xs : List<&2, U32>}>

def ps.refl(+xs: List<&2, U32>) -> ps.suf(xs, xs):
  (Nil{}, {==})

def ps.nil(+xs: List<&2, U32>) -> ps.suf(Nil{}, xs):
  (xs, AL.al.app_nil(xs))

def ps.app(+p: List<&2, U32>, +ys: List<&2, U32>) -> ps.suf(ys, List.append(&2, U32, p, ys)):
  (p, {==})

def ps.cons(+x: U32, +ys: List<&2, U32>, +t: List<&2, U32>, h: ps.suf(ys, t)) -> ps.suf(ys, Con{x, t}):
  (+p, +e) = h
  (Con{x, p}, Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{x, z}, List.append(&2, U32, p, ys), t, e))

def ps.trans.e(+p1: List<&2, U32>, +p2: List<&2, U32>, +zs: List<&2, U32>, +ys: List<&2, U32>, +xs: List<&2, U32>, +e1: {List.append(&2, U32, p1, zs) == ys : List<&2, U32>}, +e2: {List.append(&2, U32, p2, ys) == xs : List<&2, U32>}) -> {List.append(&2, U32, List.append(&2, U32, p2, p1), zs) == xs : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, List.append(&2, U32, List.append(&2, U32, p2, p1), zs), List.append(&2, U32, p2, List.append(&2, U32, p1, zs)), AL.al.app_assoc(p2, p1, zs)) : {_ == xs : List<&2, U32>}
  %Equal.sym(List<&2, U32>, List.append(&2, U32, p1, zs), ys, e1) : {List.append(&2, U32, p2, _) == xs : List<&2, U32>}
  e2

def ps.trans(+zs: List<&2, U32>, +ys: List<&2, U32>, +xs: List<&2, U32>, h1: ps.suf(zs, ys), h2: ps.suf(ys, xs)) -> ps.suf(zs, xs):
  (+p1, +e1) = h1
  (+p2, +e2) = h2
  (List.append(&2, U32, p2, p1), ps.trans.e(p1, p2, zs, ys, xs, e1, e2))

def ps.drop(+k: Nat, +xs: List<&2, U32>) -> ps.suf(B.drop(k, xs), xs):
  (B.take(k, xs), BL.take_drop(k, xs))

# a cut of a suffix, joined back
def ps.td(+n: Nat, +rest: List<&2, U32>, +xs: List<&2, U32>, h: ps.suf(rest, xs)) -> ps.suf(List.append(&2, U32, B.take(n, rest), B.drop(n, rest)), xs):
  %Equal.sym(List<&2, U32>, B.append(B.take(n, rest), B.drop(n, rest)), rest, BL.take_drop(n, rest)) : ps.suf(_, xs)
  h

# Numbers and lengths read leave the last octets

def ps.mb(m: Maybe<&2, Nu.A1Num>, t: List<&2, U32>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{Nu.A1Num{v, u, rest}}:
      ps.suf(rest, t)

def ps.lb(l: L.A1Len, xs: List<&2, U32>) -> Type:
  match l:
    case L.A1LDef{n, u, rest}:
      ps.suf(rest, xs)
    case L.A1LIndef{rest}:
      ps.suf(rest, xs)
    case L.A1LErr{e}:
      Unit

def ps.num_cons(+x: U32, m: Maybe<&2, Nu.A1Num>, +u: List<&2, U32>, h: ps.mb(m, u)) -> ps.mb(Nu.a1.num_cons(x, m), Con{x, u}):
  match m:
    case None{}:
      Unit{}
    case Some{Nu.A1Num{v, w, +rest}}:
      ps.cons(x, rest, u, h)

def ps.r128(t: List<&2, U32>, more: Bool, k: Nat, +acc: Nat) -> ps.mb(Nu.a1.r128(t, more, k, acc), t):
  match t more k:
    case Nil{} False{} _:
      ps.refl(Nil{})
    case Nil{} True{} _:
      Unit{}
    case Con{+x, +u} False{} _:
      ps.refl(Con{x, u})
    case Con{x, u} True{} 0n:
      Unit{}
    case Con{+x, +u} True{} 1n+ +j:
      +v = U32.to_nat(x)
      +ge = Nat.is_le(128n, v)
      +acc2 = Nat.add(Nat.mul(acc, 128n), Nat.sub(v, Bool.pick(Nat, ge, 128n, 0n)))
      ps.num_cons(x, Nu.a1.r128(u, ge, j, acc2), u, ps.r128(u, ge, j, acc2))

def ps.rbe_pick(ok: Bool, +k: Nat, +xs: List<&2, U32>) -> ps.mb(Nu.a1.rbe.pick(ok, k, xs), xs):
  match ok:
    case True{}:
      ps.drop(k, xs)
    case False{}:
      Unit{}

def ps.lbytes(+y: U32, m: Maybe<&2, Nu.A1Num>, +t: List<&2, U32>, h: ps.mb(m, t)) -> ps.lb(L.a1.len.bytes(y, m), Con{y, t}):
  match m:
    case None{}:
      Unit{}
    case Some{Nu.A1Num{n, u, +r2}}:
      ps.cons(y, r2, t, h)

def ps.lmany(big: Bool, +k: Nat, +y: U32, +t: List<&2, U32>) -> ps.lb(L.a1.len.many(big, k, y, t), Con{y, t}):
  match big:
    case True{}:
      Unit{}
    case False{}:
      ps.lbytes(y, Nu.a1.rbe(k, t), t, ps.rbe_pick(Nat.is_le(k, List.length(&2, U32, t)), k, t))

def ps.lres(is127: Bool, +k: Nat, +y: U32, +t: List<&2, U32>) -> ps.lb(L.a1.len.reserved(is127, k, y, t), Con{y, t}):
  match is127:
    case True{}:
      Unit{}
    case False{}:
      ps.lmany(Nat.is_lt(Nu.a1.max_octets(), k), k, y, t)

def ps.llong(+k: Nat, +y: U32, +t: List<&2, U32>) -> ps.lb(L.a1.len.long(k, y, t), Con{y, t}):
  match k:
    case 0n:
      ps.cons(y, t, t, ps.refl(t))
    case 1n+j:
      ps.lres(Nat.is_eq(1n+j, 127n), 1n+j, y, t)

def ps.lfirst(lt: Bool, +v: Nat, +y: U32, +t: List<&2, U32>) -> ps.lb(L.a1.len.first(lt, v, y, t), Con{y, t}):
  match lt:
    case True{}:
      ps.cons(y, t, t, ps.refl(t))
    case False{}:
      ps.llong(Nat.sub(v, 128n), y, t)

def ps.lread(xs: List<&2, U32>) -> ps.lb(L.a1.len.read(xs), xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+y, +t}:
      ps.lfirst(Nat.is_lt(U32.to_nat(y), 128n), U32.to_nat(y), y, t)

# Headers: what a header leaves (its contents and what follows, or what
# follows its identifier and length octets) is the input's last octets

def ps.hs(h: A.A1Head, xs: List<&2, U32>) -> Type:
  match h:
    case A.A1HEnd{}:
      Unit
    case A.A1HEoc{rest}:
      ps.suf(rest, xs)
    case A.A1HErr{e}:
      Unit
    case A.A1HPrim{t, cs, rest}:
      ps.suf(List.append(&2, U32, cs, rest), xs)
    case A.A1HDef{t, cs, rest}:
      ps.suf(List.append(&2, U32, cs, rest), xs)
    case A.A1HIndef{t, rest}:
      ps.suf(rest, xs)

# a header read from a suffix of xs leaves a suffix of xs
def ps.hlift(h: A.A1Head, +ys: List<&2, U32>, +xs: List<&2, U32>, hh: ps.hs(h, ys), hy: ps.suf(ys, xs)) -> ps.hs(h, xs):
  match h:
    case A.A1HEnd{}:
      Unit{}
    case A.A1HEoc{+rest}:
      ps.trans(rest, ys, xs, hh, hy)
    case A.A1HErr{e}:
      Unit{}
    case A.A1HPrim{t, +cs, +rest}:
      ps.trans(List.append(&2, U32, cs, rest), ys, xs, hh, hy)
    case A.A1HDef{t, +cs, +rest}:
      ps.trans(List.append(&2, U32, cs, rest), ys, xs, hh, hy)
    case A.A1HIndef{t, +rest}:
      ps.trans(rest, ys, xs, hh, hy)

def ps.fit(ok: Bool, +t: T.Asn1Tag, cons: Bool, +n: Nat, +rest: List<&2, U32>) -> ps.hs(A.a1.head.fit(ok, t, cons, n, rest), rest):
  match ok cons:
    case False{} _:
      Unit{}
    case True{} False{}:
      ps.td(n, rest, rest, ps.refl(rest))
    case True{} True{}:
      ps.td(n, rest, rest, ps.refl(rest))

def ps.min(ok: Bool, +t: T.Asn1Tag, +cons: Bool, +n: Nat, +rest: List<&2, U32>) -> ps.hs(A.a1.head.min(ok, t, cons, n, rest), rest):
  match ok:
    case True{}:
      ps.fit(Nat.is_le(n, List.length(&2, U32, rest)), t, cons, n, rest)
    case False{}:
      Unit{}

def ps.indef(allowed: Bool, cons: Bool, +t: T.Asn1Tag, +rest: List<&2, U32>) -> ps.hs(A.a1.head.indef(allowed, cons, t, rest), rest):
  match allowed cons:
    case False{} _:
      Unit{}
    case True{} False{}:
      Unit{}
    case True{} True{}:
      ps.refl(rest)

def ps.hl_len(+r: R.Asn1Rules, +t: T.Asn1Tag, +cons: Bool, l: L.A1Len, +xs: List<&2, U32>, hl: ps.lb(l, xs)) -> ps.hs(A.a1.head.len(r, t, cons, l), xs):
  match l:
    case L.A1LErr{e}:
      Unit{}
    case L.A1LIndef{+rest}:
      ps.hlift(A.a1.head.indef(R.Asn1Rules.indefinite(r), cons, t, rest), rest, xs, ps.indef(R.Asn1Rules.indefinite(r), cons, t, rest), hl)
    case L.A1LDef{+n, +u, +rest}:
      +ok = R.a1.when(R.Asn1Rules.min_length(r), Bool.and(L.a1.len_ok(n), Nu.a1.leq(L.a1.len_bytes(n), u)))
      ps.hlift(A.a1.head.min(ok, t, cons, n, rest), rest, xs, ps.min(ok, t, cons, n, rest), hl)

def ps.eoc2(z: Bool, +t: List<&2, U32>) -> ps.hs(A.a1.head.eoc2(z, t), t):
  match z:
    case True{}:
      ps.refl(t)
    case False{}:
      Unit{}

def ps.eoc(rest: List<&2, U32>) -> ps.hs(A.a1.head.eoc(rest), rest):
  match rest:
    case Nil{}:
      Unit{}
    case Con{+y, +t}:
      +z = Nat.is_eq(U32.to_nat(y), 0n)
      ps.hlift(A.a1.head.eoc2(z, t), t, Con{y, t}, ps.eoc2(z, t), ps.cons(y, t, t, ps.refl(t)))

def ps.res(u0: Bool, +r: R.Asn1Rules, +c: T.Asn1Class, cons: Bool, +n: Nat, +rest: List<&2, U32>) -> ps.hs(A.a1.head.res(u0, r, c, cons, n, rest), rest):
  match u0 cons:
    case True{} False{}:
      ps.eoc(rest)
    case True{} True{}:
      Unit{}
    case False{} False{}:
      ps.hl_len(r, T.Asn1Tag{c, n}, False{}, L.a1.len.read(rest), rest, ps.lread(rest))
    case False{} True{}:
      ps.hl_len(r, T.Asn1Tag{c, n}, True{}, L.a1.len.read(rest), rest, ps.lread(rest))

def ps.tag2(ok: Bool, +r: R.Asn1Rules, +c: T.Asn1Class, +cons: Bool, +n: Nat, +rest: List<&2, U32>) -> ps.hs(A.a1.head.tag2(ok, r, c, cons, n, rest), rest):
  match ok:
    case True{}:
      ps.res(En.a1.is_univ0(c, n), r, c, cons, n, rest)
    case False{}:
      Unit{}

def ps.num(+r: R.Asn1Rules, +c: T.Asn1Class, +cons: Bool, +x: U32, m: Maybe<&2, Nu.A1Num>, +t: List<&2, U32>, hm: ps.mb(m, t)) -> ps.hs(A.a1.head.num(r, c, cons, x, m), t):
  match m:
    case None{}:
      Unit{}
    case Some{Nu.A1Num{+n, +u, +rest}}:
      +ids : List<&2, U32> = Con{x, u}
      ps.hlift(A.a1.head.tag(r, c, cons, n, ids, rest), rest, t, ps.tag2(Nu.a1.leq(T.a1.id_bytes(c, cons, n), ids), r, c, cons, n, rest), hm)

def ps.hi(hi: Bool, +r: R.Asn1Rules, +c: T.Asn1Class, +cons: Bool, +low: Nat, +x: U32, +t: List<&2, U32>) -> ps.hs(A.a1.head.hi(hi, r, c, cons, low, x, t), t):
  match hi:
    case True{}:
      ps.num(r, c, cons, x, Nu.a1.r128(t, True{}, Nu.a1.max_octets(), 0n), t, ps.r128(t, True{}, Nu.a1.max_octets(), 0n))
    case False{}:
      ps.tag2(Nu.a1.leq(T.a1.id_bytes(c, cons, low), [x]), r, c, cons, low, t)

def ps.id(+r: R.Asn1Rules, i: T.A1Id1, +x: U32, +t: List<&2, U32>) -> ps.hs(A.a1.head.id(r, i, x, t), t):
  match i:
    case T.A1Id1{+c, +cons, +low}:
      ps.hi(Nat.is_eq(low, 31n), r, c, cons, low, x, t)

def ps.head0(+r: R.Asn1Rules, xs: List<&2, U32>) -> ps.hs(A.a1.head0(r, xs), xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +t}:
      +i = T.a1.id1(U32.to_nat(x))
      ps.hlift(A.a1.head.id(r, i, x, t), t, Con{x, t}, ps.id(r, i, x, t), ps.cons(x, t, t, ps.refl(t)))

# The final checks cut the input again, or pass the header on

def ps.cmk(ok: Bool, +t: T.Asn1Tag, cons: Bool, +k: Nat, +l: Nat, +xs: List<&2, U32>) -> ps.hs(A.a1.canon.mk(ok, t, cons, k, l, xs), xs):
  match ok cons:
    case False{} _:
      Unit{}
    case True{} False{}:
      ps.td(l, B.drop(k, xs), xs, ps.drop(k, xs))
    case True{} True{}:
      ps.td(l, B.drop(k, xs), xs, ps.drop(k, xs))

def ps.canon(+xs: List<&2, U32>, h: A.A1Head, hh: ps.hs(h, xs)) -> ps.hs(A.a1.canon(xs, h), xs):
  match h:
    case A.A1HPrim{T.Asn1Tag{+c, +n}, +cs, rest}:
      +l = List.length(&2, U32, cs)
      ps.cmk(A.a1.canon.ok(c, False{}, n, l, xs), T.Asn1Tag{c, n}, False{}, List.length(&2, U32, A.a1.hdr(c, False{}, n, l)), l, xs)
    case A.A1HDef{T.Asn1Tag{+c, +n}, +cs, rest}:
      +l = List.length(&2, U32, cs)
      ps.cmk(A.a1.canon.ok(c, True{}, n, l, xs), T.Asn1Tag{c, n}, True{}, List.length(&2, U32, A.a1.hdr(c, True{}, n, l)), l, xs)
    case A.A1HEnd{}:
      hh
    case A.A1HEoc{rest}:
      hh
    case A.A1HErr{e}:
      hh
    case A.A1HIndef{t, rest}:
      hh

def ps.ioff(a: Bool, h: A.A1Head, +xs: List<&2, U32>, hh: ps.hs(h, xs)) -> ps.hs(A.a1.head.indef_off(a, h), xs):
  match a:
    case True{}:
      hh
    case False{}:
      match h:
        case A.A1HIndef{t, rest}:
          Unit{}
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

def ps.fin2(m: Bool, +xs: List<&2, U32>, h: A.A1Head, hh: ps.hs(h, xs)) -> ps.hs(A.a1.head.fin2(m, xs, h), xs):
  match m:
    case True{}:
      ps.canon(xs, h, hh)
    case False{}:
      hh

def ps.nend(xs: List<&2, U32>, h: A.A1Head, hh: ps.hs(h, xs)) -> ps.hs(A.a1.head.nend(xs, h), xs):
  match xs:
    case Nil{}:
      hh
    case Con{y, t}:
      match h:
        case A.A1HEnd{}:
          Unit{}
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

# every header leaves the input's last octets
def ps.head(+r: R.Asn1Rules, +xs: List<&2, U32>) -> ps.hs(A.a1.head(r, xs), xs):
  +h0 = A.a1.head0(r, xs)
  +h1 = A.a1.head.indef_off(R.Asn1Rules.indefinite(r), h0)
  +h2 = A.a1.head.fin2(R.Asn1Rules.min_length(r), xs, h1)
  ps.nend(xs, h2, ps.fin2(R.Asn1Rules.min_length(r), xs, h1, ps.ioff(R.Asn1Rules.indefinite(r), h0, xs, ps.head0(r, xs))))

# The decoder: what it leaves after the elements it read is the input's
# last octets

def ps.rs(res: Result<&2, &2, E.Asn1Error, A.A1Out>, xs: List<&2, U32>) -> Type:
  match res:
    case Fail{e}:
      Unit
    case Done{A.A1Out{ns, rest}}:
      ps.suf(rest, xs)

def ps.one(n: Result<&2, &2, E.Asn1Error, N.Asn1Node>, +rest: List<&2, U32>, +xs: List<&2, U32>, h: ps.suf(rest, xs)) -> ps.rs(A.a1.one(n, rest), xs):
  match n:
    case Fail{e}:
      Unit{}
    case Done{x}:
      h

def ps.more(n: Result<&2, &2, E.Asn1Error, N.Asn1Node>, b: Result<&2, &2, E.Asn1Error, A.A1Out>, +ys: List<&2, U32>, +xs: List<&2, U32>, hb: ps.rs(b, ys), hy: ps.suf(ys, xs)) -> ps.rs(A.a1.more(n, b), xs):
  match n b:
    case Fail{e} _:
      Unit{}
    case Done{x} Fail{e}:
      Unit{}
    case Done{x} Done{A.A1Out{ns, +rest}}:
      ps.trans(rest, ys, xs, hb, hy)

def ps.orest(inner: Result<&2, &2, E.Asn1Error, A.A1Out>, +ys: List<&2, U32>, +xs: List<&2, U32>, hi: ps.rs(inner, ys), hy: ps.suf(ys, xs)) -> ps.suf(A.a1.out_rest(inner), xs):
  match inner:
    case Fail{e}:
      ps.nil(xs)
    case Done{A.A1Out{ns, +rest}}:
      ps.trans(rest, ys, xs, hi, hy)

def ps.after(+cs: List<&2, U32>, +rest: List<&2, U32>, +xs: List<&2, U32>, hh: ps.suf(List.append(&2, U32, cs, rest), xs)) -> ps.suf(rest, xs):
  ps.trans(rest, List.append(&2, U32, cs, rest), xs, ps.app(cs, rest), hh)

def ps.dec(f: Nat, +r: R.Asn1Rules, mode: A.A1Mode, h: A.A1Head, +xs: List<&2, U32>, hh: ps.hs(h, xs)) -> ps.rs(A.a1.dec(f, r, mode, h), xs):
  match f:
    case 0n:
      Unit{}
    case 1n+ +g:
      match mode:
        case A.A1One{}:
          match h:
            case A.A1HEnd{}:
              Unit{}
            case A.A1HEoc{rest}:
              Unit{}
            case A.A1HErr{e}:
              Unit{}
            case A.A1HPrim{+t, +cs, +rest}:
              ps.one(A.a1.mk_prim(r, t, B.Octets.of_list(cs)), rest, xs, ps.after(cs, rest, xs, hh))
            case A.A1HDef{+t, +cs, +rest}:
              ps.one(A.a1.mk_cons(r, t, A.a1.dec(g, r, A.A1All{}, A.a1.head(r, cs))), rest, xs, ps.after(cs, rest, xs, hh))
            case A.A1HIndef{+t, +rest}:
              +inner = A.a1.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest))
              ps.one(A.a1.mk_cons(r, t, inner), A.a1.out_rest(inner), xs, ps.orest(inner, rest, xs, ps.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest), rest, ps.head(r, rest)), hh))
        case A.A1All{}:
          match h:
            case A.A1HEnd{}:
              ps.nil(xs)
            case A.A1HEoc{rest}:
              Unit{}
            case A.A1HErr{e}:
              Unit{}
            case A.A1HPrim{+t, +cs, +rest}:
              ps.more(A.a1.mk_prim(r, t, B.Octets.of_list(cs)), A.a1.dec(g, r, A.A1All{}, A.a1.head(r, rest)), rest, xs, ps.dec(g, r, A.A1All{}, A.a1.head(r, rest), rest, ps.head(r, rest)), ps.after(cs, rest, xs, hh))
            case A.A1HDef{+t, +cs, +rest}:
              ps.more(A.a1.mk_cons(r, t, A.a1.dec(g, r, A.A1All{}, A.a1.head(r, cs))), A.a1.dec(g, r, A.A1All{}, A.a1.head(r, rest)), rest, xs, ps.dec(g, r, A.A1All{}, A.a1.head(r, rest), rest, ps.head(r, rest)), ps.after(cs, rest, xs, hh))
            case A.A1HIndef{+t, +rest}:
              +inner = A.a1.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest))
              +ys = A.a1.out_rest(inner)
              ps.more(A.a1.mk_cons(r, t, inner), A.a1.dec(g, r, A.A1All{}, A.a1.head(r, ys)), ys, xs, ps.dec(g, r, A.A1All{}, A.a1.head(r, ys), ys, ps.head(r, ys)), ps.orest(inner, rest, xs, ps.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest), rest, ps.head(r, rest)), hh))
        case A.A1Eoc{}:
          match h:
            case A.A1HEnd{}:
              Unit{}
            case A.A1HEoc{rest}:
              hh
            case A.A1HErr{e}:
              Unit{}
            case A.A1HPrim{+t, +cs, +rest}:
              ps.more(A.a1.mk_prim(r, t, B.Octets.of_list(cs)), A.a1.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest)), rest, xs, ps.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest), rest, ps.head(r, rest)), ps.after(cs, rest, xs, hh))
            case A.A1HDef{+t, +cs, +rest}:
              ps.more(A.a1.mk_cons(r, t, A.a1.dec(g, r, A.A1All{}, A.a1.head(r, cs))), A.a1.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest)), rest, xs, ps.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest), rest, ps.head(r, rest)), ps.after(cs, rest, xs, hh))
            case A.A1HIndef{+t, +rest}:
              +inner = A.a1.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest))
              +ys = A.a1.out_rest(inner)
              ps.more(A.a1.mk_cons(r, t, inner), A.a1.dec(g, r, A.A1Eoc{}, A.a1.head(r, ys)), ys, xs, ps.dec(g, r, A.A1Eoc{}, A.a1.head(r, ys), ys, ps.head(r, ys)), ps.orest(inner, rest, xs, ps.dec(g, r, A.A1Eoc{}, A.a1.head(r, rest), rest, ps.head(r, rest)), hh))

def ps.run(+r: R.Asn1Rules, mode: A.A1Mode, +xs: List<&2, U32>) -> ps.rs(A.a1.run(r, mode, xs), xs):
  ps.dec(Nat.add(1n, List.length(&2, U32, xs)), r, mode, A.a1.head(r, xs), xs, ps.head(r, xs))

# One element read: its octets, then the rest, are the input

def ps.rdisc(z: Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>) -> Type:
  match z:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def ps.rfd(-x: E.Asn1Error, -y: A.Asn1TlvRead, e: {Fail{x} == Done{y} : Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>}) -> Empty:
  %e : ps.rdisc(_)
  Unit{}

def ps.rd_raw(z: Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>) -> B.Octets:
  match z:
    case Fail{x}:
      B.Octets.empty()
    case Done{A.Asn1TlvRead{t, rest}}:
      A.Asn1Tlv.raw(t)

def ps.rd_rest(z: Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>) -> B.Octets:
  match z:
    case Fail{x}:
      B.Octets.empty()
    case Done{A.Asn1TlvRead{t, rest}}:
      rest

# the octets used are those in front of the rest
def ps.used(+p: List<&2, U32>, +rest: List<&2, U32>) -> {B.take(Nat.sub(List.length(&2, U32, List.append(&2, U32, p, rest)), List.length(&2, U32, rest)), List.append(&2, U32, p, rest)) == p : List<&2, U32>}:
  +lp = List.length(&2, U32, p)
  +lr = List.length(&2, U32, rest)
  +pr = List.append(&2, U32, p, rest)
  %Equal.sym(Nat, List.length(&2, U32, pr), Nat.add(lp, lr), AL.al.app_len(p, rest)) : {B.take(Nat.sub(_, lr), pr) == p : List<&2, U32>}
  %UL.nat_add_comm(lr, lp) : {B.take(Nat.sub(_, lr), pr) == p : List<&2, U32>}
  %Equal.sym(Nat, Nat.sub(Nat.add(lr, lp), lr), lp, AN.an.sub_add_l(lr, lp)) : {B.take(_, pr) == p : List<&2, U32>}
  AL.al.take_app(p, rest)

def ps.split_eq(+p: List<&2, U32>, +rest: List<&2, U32>) -> {B.Octets.append(B.Octets.of_list(B.take(Nat.sub(List.length(&2, U32, List.append(&2, U32, p, rest)), List.length(&2, U32, rest)), List.append(&2, U32, p, rest))), B.Octets.of_list(rest)) == B.Octets.of_list(List.append(&2, U32, p, rest)) : B.Octets}:
  %Equal.sym(List<&2, U32>, B.take(Nat.sub(List.length(&2, U32, List.append(&2, U32, p, rest)), List.length(&2, U32, rest)), List.append(&2, U32, p, rest)), p, ps.used(p, rest)) : {B.Octets.append(B.Octets.of_list(_), B.Octets.of_list(rest)) == B.Octets.of_list(List.append(&2, U32, p, rest)) : B.Octets}
  Equal.sym(B.Octets, B.Octets.of_list(List.append(&2, U32, p, rest)), B.Octets.append(B.Octets.of_list(p), B.Octets.of_list(rest)), OA.oa.of_app(p, rest))

def ps.split_suf(+xs: List<&2, U32>, +rest: List<&2, U32>, h: ps.suf(rest, xs)) -> {B.Octets.append(B.Octets.of_list(B.take(Nat.sub(List.length(&2, U32, xs), List.length(&2, U32, rest)), xs)), B.Octets.of_list(rest)) == B.Octets.of_list(xs) : B.Octets}:
  (+p, +e) = h
  %e : {B.Octets.append(B.Octets.of_list(B.take(Nat.sub(List.length(&2, U32, _), List.length(&2, U32, rest)), _)), B.Octets.of_list(rest)) == B.Octets.of_list(_) : B.Octets}
  ps.split_eq(p, rest)

def ps.tlv(+xs: List<&2, U32>, res: Result<&2, &2, E.Asn1Error, A.A1Out>, hr: ps.rs(res, xs), +x: A.Asn1Tlv, +rest: B.Octets, +e: {A.a1.tlv.out(xs, res) == Done{A.Asn1TlvRead{x, rest}} : Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>}) -> {B.Octets.append(A.Asn1Tlv.raw(x), rest) == B.Octets.of_list(xs) : B.Octets}:
  match res:
    case Fail{er}:
      Empty.absurd({B.Octets.append(A.Asn1Tlv.raw(x), rest) == B.Octets.of_list(xs) : B.Octets}, ps.rfd(er, A.Asn1TlvRead{x, rest}, e))
    case Done{A.A1Out{Nil{}, r2}}:
      Empty.absurd({B.Octets.append(A.Asn1Tlv.raw(x), rest) == B.Octets.of_list(xs) : B.Octets}, ps.rfd(E.Asn1Truncated{}, A.Asn1TlvRead{x, rest}, e))
    case Done{A.A1Out{Con{+n, +ns}, +r2}}:
      +z = A.a1.tlv.out(xs, Done{A.A1Out{Con{n, ns}, r2}})
      +er = Equal.cong(Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>, B.Octets, q => ps.rd_raw(q), z, Done{A.Asn1TlvRead{x, rest}}, e)
      +es = Equal.cong(Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>, B.Octets, q => ps.rd_rest(q), z, Done{A.Asn1TlvRead{x, rest}}, e)
      %er : {B.Octets.append(_, rest) == B.Octets.of_list(xs) : B.Octets}
      %es : {B.Octets.append(ps.rd_raw(z), _) == B.Octets.of_list(xs) : B.Octets}
      ps.split_suf(xs, r2, hr)

# law read_split
def ps.read(+r: R.Asn1Rules, +b: B.Octets, +x: A.Asn1Tlv, +rest: B.Octets, +e: {A.Asn1.read(r, b) == Done{A.Asn1TlvRead{x, rest}} : Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>}) -> {B.Octets.append(A.Asn1Tlv.raw(x), rest) == b : B.Octets}:
  +xs = B.Octets.to_list(b)
  %BL.octets_of_to(b) : {B.Octets.append(A.Asn1Tlv.raw(x), rest) == _ : B.Octets}
  ps.tlv(xs, A.a1.run(r, A.A1One{}, xs), ps.run(r, A.A1One{}, xs), x, rest, e)

# A run of elements: their octets, in order, are the input

def ps.st(s: A.A1Step, b: B.Octets) -> Type:
  match s:
    case A.A1StepEnd{}:
      {B.Octets.empty() == b : B.Octets}
    case A.A1StepErr{e}:
      Unit
    case A.A1StepOne{x, rest}:
      {B.Octets.append(A.Asn1Tlv.raw(x), rest) == b : B.Octets}

def ps.stepof(res: Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>, +r: R.Asn1Rules, +b: B.Octets, +eq: {A.Asn1.read(r, b) == res : Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>}) -> ps.st(A.a1.step.of(res), b):
  match res:
    case Fail{e}:
      Unit{}
    case Done{A.Asn1TlvRead{+x, +rest}}:
      ps.read(r, b, x, rest, eq)

def ps.pick(xs: List<&2, U32>, +r: R.Asn1Rules, +b: B.Octets, +ex: {B.Octets.to_list(b) == xs : List<&2, U32>}) -> ps.st(A.a1.step.pick(xs, r, b), b):
  match xs:
    case Nil{}:
      OA.oa.ext(B.Octets.empty(), b, Equal.trans(List<&2, U32>, B.Octets.to_list(B.Octets.empty()), Nil{}, B.Octets.to_list(b), OA.oa.empty_list(), Equal.sym(List<&2, U32>, B.Octets.to_list(b), Nil{}, ex)))
    case Con{y, t}:
      ps.stepof(A.Asn1.read(r, b), r, b, {==})

def ps.step(+r: R.Asn1Rules, +b: B.Octets) -> ps.st(A.a1.step(r, b), b):
  ps.pick(B.Octets.to_list(b), r, b, {==})

def ps.ldisc(z: Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>) -> Type:
  match z:
    case Fail{x}:
      Unit
    case Done{y}:
      Empty

def ps.lfd(-x: E.Asn1Error, -y: List<&2, A.Asn1Tlv>, e: {Fail{x} == Done{y} : Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>}) -> Empty:
  %e : ps.ldisc(_)
  Unit{}

def ps.lval(z: Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>) -> List<&2, A.Asn1Tlv>:
  match z:
    case Fail{x}:
      Nil{}
    case Done{v}:
      v

def ps.go2(+x: A.Asn1Tlv, res2: Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>, +rest: B.Octets, +b: B.Octets, +hx: {B.Octets.append(A.Asn1Tlv.raw(x), rest) == b : B.Octets}, ih: @ys: List<&2, A.Asn1Tlv> -> @e2: {res2 == Done{ys} : Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>} -> {B.Octets.concat(A.Asn1.raws(ys)) == rest : B.Octets}, +xs: List<&2, A.Asn1Tlv>, +e: {A.a1.reads.cons(x, res2) == Done{xs} : Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>}) -> {B.Octets.concat(A.Asn1.raws(xs)) == b : B.Octets}:
  match res2:
    case Fail{er}:
      Empty.absurd({B.Octets.concat(A.Asn1.raws(xs)) == b : B.Octets}, ps.lfd(er, xs, e))
    case Done{+ys}:
      +hxs = Equal.cong(Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>, List<&2, A.Asn1Tlv>, q => ps.lval(q), Done{Con{x, ys}}, Done{xs}, e)
      %hxs : {B.Octets.concat(A.Asn1.raws(_)) == b : B.Octets}
      %Equal.sym(B.Octets, B.Octets.concat(Con{A.Asn1Tlv.raw(x), A.Asn1.raws(ys)}), B.Octets.append(A.Asn1Tlv.raw(x), B.Octets.concat(A.Asn1.raws(ys))), BL.octets_concat_cons(A.Asn1Tlv.raw(x), A.Asn1.raws(ys))) : {_ == b : B.Octets}
      %Equal.sym(B.Octets, B.Octets.concat(A.Asn1.raws(ys)), rest, ih(ys, {==})) : {B.Octets.append(A.Asn1Tlv.raw(x), _) == b : B.Octets}
      hx

def ps.go(f: Nat, +r: R.Asn1Rules, s: A.A1Step, +b: B.Octets, hs: ps.st(s, b), +xs: List<&2, A.Asn1Tlv>, +e: {A.a1.reads.go(f, r, s) == Done{xs} : Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>}) -> {B.Octets.concat(A.Asn1.raws(xs)) == b : B.Octets}:
  match f s:
    case _ A.A1StepEnd{}:
      +hxs = Equal.cong(Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>, List<&2, A.Asn1Tlv>, q => ps.lval(q), Done{Nil{}}, Done{xs}, e)
      %hxs : {B.Octets.concat(A.Asn1.raws(_)) == b : B.Octets}
      %Equal.sym(B.Octets, B.Octets.concat(Nil{}), B.Octets.empty(), BL.octets_concat_nil()) : {_ == b : B.Octets}
      hs
    case _ A.A1StepErr{er}:
      Empty.absurd({B.Octets.concat(A.Asn1.raws(xs)) == b : B.Octets}, ps.lfd(er, xs, e))
    case 0n A.A1StepOne{x, rest}:
      Empty.absurd({B.Octets.concat(A.Asn1.raws(xs)) == b : B.Octets}, ps.lfd(E.Asn1Exhausted{}, xs, e))
    case 1n+ +g A.A1StepOne{+x, +rest}:
      ps.go2(x, A.a1.reads.go(g, r, A.a1.step(r, rest)), rest, b, hs, +ys => +e2 => ps.go(g, r, A.a1.step(r, rest), rest, ps.step(r, rest), ys, e2), xs, e)

# law read_all_split
def ps.read_all(+r: R.Asn1Rules, +b: B.Octets, +xs: List<&2, A.Asn1Tlv>, +e: {A.Asn1.read_all(r, b) == Done{xs} : Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>}) -> {B.Octets.concat(A.Asn1.raws(xs)) == b : B.Octets}:
  ps.go(Nat.add(1n, B.Octets.len(b)), r, A.a1.step(r, b), b, ps.step(r, b), xs, e)

# law items_split
def ps.items(+r: R.Asn1Rules, +x: A.Asn1Tlv, +xs: List<&2, A.Asn1Tlv>, +e: {A.Asn1.items(r, x) == Done{xs} : Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>}) -> {B.Octets.concat(A.Asn1.raws(xs)) == A.Asn1.contents(r, x) : B.Octets}:
  ps.read_all(r, A.Asn1.contents(r, x), xs, e)

# The contents octets: a slice of what a header was read from

def ps.cof_split(+cs: List<&2, U32>, +rest: List<&2, U32>, +zs: List<&2, U32>, h: ps.suf(List.append(&2, U32, cs, rest), zs)) -> OA.oa.sl(B.Octets.of_list(cs), B.Octets.of_list(zs)):
  (+p, +e) = h
  %e : OA.oa.sl(B.Octets.of_list(cs), B.Octets.of_list(_))
  %Equal.sym(B.Octets, B.Octets.of_list(List.append(&2, U32, p, List.append(&2, U32, cs, rest))), B.Octets.append(B.Octets.of_list(p), B.Octets.of_list(List.append(&2, U32, cs, rest))), OA.oa.of_app(p, List.append(&2, U32, cs, rest))) : OA.oa.sl(B.Octets.of_list(cs), _)
  %Equal.sym(B.Octets, B.Octets.of_list(List.append(&2, U32, cs, rest)), B.Octets.append(B.Octets.of_list(cs), B.Octets.of_list(rest)), OA.oa.of_app(cs, rest)) : OA.oa.sl(B.Octets.of_list(cs), B.Octets.append(B.Octets.of_list(p), _))
  OA.oa.sl_mid(B.Octets.of_list(p), B.Octets.of_list(cs), B.Octets.of_list(rest))

def ps.cof(h: A.A1Head, +zs: List<&2, U32>, hh: ps.hs(h, zs)) -> OA.oa.sl(B.Octets.of_list(A.a1.content.of(h)), B.Octets.of_list(zs)):
  match h:
    case A.A1HPrim{t, +cs, +rest}:
      ps.cof_split(cs, rest, zs, hh)
    case A.A1HDef{t, +cs, +rest}:
      ps.cof_split(cs, rest, zs, hh)
    case A.A1HIndef{t, +rest}:
      +k = Nat.sub(List.length(&2, U32, rest), 2n)
      ps.cof_split(B.take(k, rest), B.drop(k, rest), zs, ps.td(k, rest, zs, hh))
    case A.A1HEnd{}:
      ps.cof_split(Nil{}, zs, zs, ps.refl(zs))
    case A.A1HEoc{rest}:
      ps.cof_split(Nil{}, zs, zs, ps.refl(zs))
    case A.A1HErr{e}:
      ps.cof_split(Nil{}, zs, zs, ps.refl(zs))

# law contents_within
def ps.contents(+r: R.Asn1Rules, x: A.Asn1Tlv) -> OA.oa.sl(A.Asn1.contents(r, x), A.Asn1Tlv.raw(x)):
  match x:
    case A.Asn1Tlv{n, +raw}:
      +zs = B.Octets.to_list(raw)
      %BL.octets_of_to(raw) : OA.oa.sl(B.Octets.of_list(A.a1.content.of(A.a1.head(r, zs))), _)
      ps.cof(A.a1.head(r, zs), zs, ps.head(r, zs))
