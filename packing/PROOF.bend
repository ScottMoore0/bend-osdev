import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../word64/LAWS.bend as WL
import ../word64/PROOF.bend as WP
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./view.bend as V
import ./field.bend as F
import ./packing.bend as P
import ./proof_list.bend as PL
import ./proof_view.bend as PV
import ./proof_val.bend as PW
import ./LAWS.bend as Laws

def Laws.view_unview(q, bs, n, h):
  match q:
    case V.PkQuirks{+m, +le, +lsw}:
      +by = V.packing.bytes_of(m, bs)
      +r = List.reverse(&2, U32, by)
      %Equal.sym(List<&2, U32>, V.packing.order(V.PkQuirks{m, le, lsw}, V.packing.unorder(V.PkQuirks{m, le, lsw}, r)), r, PL.pl.ou(V.PkQuirks{m, le, lsw}, r)) : {V.packing.bits_of(m, List.reverse(&2, U32, _)) == bs : List<&2, Bool>}
      %Equal.sym(List<&2, U32>, List.reverse(&2, U32, r), by, PL.pl.rev_rev(U32, by)) : {V.packing.bits_of(m, _) == bs : List<&2, Bool>}
      PV.pv.bits_bytes(n, bs, m, h)

def Laws.view_mask(q, xs):
  match q:
    case V.PkQuirks{+m, +le, +lsw}:
      +qq = {V.PkQuirks{m, le, lsw} : V.PkQuirks}
      %Equal.sym(List<&2, U32>, V.packing.order(qq, B.mask(xs)), B.mask(V.packing.order(qq, xs)), PL.pl.order_mask(qq, xs)) : {V.packing.bits_of(m, List.reverse(&2, U32, _)) == V.packing.bits_of(m, List.reverse(&2, U32, V.packing.order(qq, xs))) : List<&2, Bool>}
      %Equal.sym(List<&2, U32>, List.reverse(&2, U32, B.mask(V.packing.order(qq, xs))), B.mask(List.reverse(&2, U32, V.packing.order(qq, xs))), PL.pl.rev_mask(V.packing.order(qq, xs))) : {V.packing.bits_of(m, _) == V.packing.bits_of(m, List.reverse(&2, U32, V.packing.order(qq, xs))) : List<&2, Bool>}
      PV.pv.bits_mask(m, List.reverse(&2, U32, V.packing.order(qq, xs)))

def Laws.view_len(q, xs):
  match q:
    case V.PkQuirks{+m, +le, +lsw}:
      +qq = {V.PkQuirks{m, le, lsw} : V.PkQuirks}
      %Equal.sym(Nat, List.length(&2, Bool, V.packing.bits_of(m, List.reverse(&2, U32, V.packing.order(qq, xs)))), Nat.mul(List.length(&2, U32, List.reverse(&2, U32, V.packing.order(qq, xs))), 8n), PV.pv.len_bits(m, List.reverse(&2, U32, V.packing.order(qq, xs)))) : {_ == Nat.mul(List.length(&2, U32, xs), 8n) : Nat}
      %Equal.sym(Nat, List.length(&2, U32, List.reverse(&2, U32, V.packing.order(qq, xs))), List.length(&2, U32, V.packing.order(qq, xs)), PL.pl.rev_len(U32, V.packing.order(qq, xs))) : {Nat.mul(_, 8n) == Nat.mul(List.length(&2, U32, xs), 8n) : Nat}
      %Equal.sym(Nat, List.length(&2, U32, V.packing.order(qq, xs)), List.length(&2, U32, xs), PL.pl.order_len(qq, xs)) : {Nat.mul(_, 8n) == Nat.mul(List.length(&2, U32, xs), 8n) : Nat}
      {==}

def Laws.unview_len(q, bs, n, h):
  match q:
    case V.PkQuirks{+m, +le, +lsw}:
      +qq = {V.PkQuirks{m, le, lsw} : V.PkQuirks}
      %Equal.sym(Nat, List.length(&2, U32, V.packing.unorder(qq, List.reverse(&2, U32, V.packing.bytes_of(m, bs)))), List.length(&2, U32, List.reverse(&2, U32, V.packing.bytes_of(m, bs))), PL.pl.unorder_len(qq, List.reverse(&2, U32, V.packing.bytes_of(m, bs)))) : {_ == n : Nat}
      %Equal.sym(Nat, List.length(&2, U32, List.reverse(&2, U32, V.packing.bytes_of(m, bs))), List.length(&2, U32, V.packing.bytes_of(m, bs)), PL.pl.rev_len(U32, V.packing.bytes_of(m, bs))) : {_ == n : Nat}
      PV.pv.len_bytes(n, bs, m, h)

def Laws.value_bits(v):
  PW.pw.val(v)

# Nat

def pk.le_succ(x: Nat) -> {Nat.is_le(x, 1n+x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      pk.le_succ(p)

def pk.le_zero(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pk.le_trans(a: Nat, b: Nat, c: Nat, +e: {Nat.is_le(a, b) == True{} : Bool}, +f: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      pk.le_zero(c)
    case 1n+ap 0n _:
      Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, PL.pl.ft(e))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, PL.pl.ft(f))
    case 1n+ap 1n+bp 1n+cp:
      pk.le_trans(ap, bp, cp, e, f)

def pk.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : PL.pl.bt(_)
  Unit{}

def pk.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# not a < b: b <= a
def pk.nlt(a: Nat, b: Nat, +e: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case +aa 0n:
      pk.le_zero(aa)
    case 0n 1n+bp:
      Empty.absurd({Nat.is_le(1n+bp, 0n) == True{} : Bool}, pk.tf(e))
    case 1n+ap 1n+bp:
      pk.nlt(ap, bp, e)

# not a <= b: 1 + b <= a
def pk.nle(a: Nat, b: Nat, +e: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_le(1n+b, a) == True{} : Bool}:
  match a b:
    case 0n +bb:
      Empty.absurd({Nat.is_le(1n+bb, 0n) == True{} : Bool}, PL.pl.ft(Equal.trans(Bool, False{}, Nat.is_le(0n, bb), True{}, Equal.sym(Bool, Nat.is_le(0n, bb), False{}, e), pk.le_zero(bb))))
    case 1n+ap 0n:
      pk.le_zero(ap)
    case 1n+ap 1n+bp:
      pk.nle(ap, bp, e)

def pk.le_succ_lt(s: Nat, k: Nat) -> {Nat.is_le(1n+s, k) == Nat.is_lt(s, k) : Bool}:
  match s k:
    case _ 0n:
      {==}
    case 0n 1n+kp:
      pk.le_zero(kp)
    case 1n+sp 1n+kp:
      pk.le_succ_lt(sp, kp)

# e <= t: e + (t - e) = t
def pk.add_sub(e: Nat, t: Nat, +h: {Nat.is_le(e, t) == True{} : Bool}) -> {Nat.add(e, Nat.sub(t, e)) == t : Nat}:
  match e t:
    case 0n +tt:
      pk.sub_zero(tt)
    case 1n+ep 0n:
      Empty.absurd({Nat.add(1n+ep, 0n) == 0n : Nat}, PL.pl.ft(h))
    case 1n+ep 1n+tp:
      %pk.add_sub(ep, tp, h) : {1n+Nat.add(ep, Nat.sub(tp, ep)) == 1n+_ : Nat}
      {==}

# What a passing check says about the field

def pk.mdisc(m: Maybe<&2, P.PkError>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def pk.sn(-x: P.PkError, e: {Some{x} == None{} : Maybe<&2, P.PkError>}) -> Empty:
  %e : pk.mdisc(_)
  Unit{}

def pk.c_range(b: Bool, +q: V.PkQuirks, +l: Nat, +s: Nat, +e: Nat, +h: {P.packing.check.range(b, q, l, s, e) == None{} : Maybe<&2, P.PkError>}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, pk.sn(P.PkBadRange{}, h))
    case False{}:
      {==}

def pk.c_wide(b: Bool, +q: V.PkQuirks, +l: Nat, +s: Nat, +h: {P.packing.check.wide(b, q, l, s) == None{} : Maybe<&2, P.PkError>}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, pk.sn(P.PkTooWide{}, h))
    case False{}:
      {==}

def pk.c_buf(b: Bool, +q: V.PkQuirks, +l: Nat, +h: {P.packing.check.buf(b, q, l) == None{} : Maybe<&2, P.PkError>}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, pk.sn(P.PkOutOfBuffer{}, h))
    case False{}:
      {==}

def pk.r1(+q: V.PkQuirks, +l: Nat, +s: Nat, +e: Nat, +h: {P.packing.check(q, l, s, e) == None{} : Maybe<&2, P.PkError>}) -> {Nat.is_lt(s, e) == False{} : Bool}:
  pk.c_range(Nat.is_lt(s, e), q, l, s, e, h)

def pk.h2(+q: V.PkQuirks, +l: Nat, +s: Nat, +e: Nat, +h: {P.packing.check(q, l, s, e) == None{} : Maybe<&2, P.PkError>}) -> {P.packing.check.wide(Nat.is_lt(64n, P.packing.width(s, e)), q, l, s) == None{} : Maybe<&2, P.PkError>}:
  %pk.r1(q, l, s, e, h) : {P.packing.check.range(_, q, l, s, e) == None{} : Maybe<&2, P.PkError>}
  h

def pk.r2(+q: V.PkQuirks, +l: Nat, +s: Nat, +e: Nat, +h: {P.packing.check(q, l, s, e) == None{} : Maybe<&2, P.PkError>}) -> {Nat.is_lt(64n, P.packing.width(s, e)) == False{} : Bool}:
  pk.c_wide(Nat.is_lt(64n, P.packing.width(s, e)), q, l, s, pk.h2(q, l, s, e, h))

def pk.h3(+q: V.PkQuirks, +l: Nat, +s: Nat, +e: Nat, +h: {P.packing.check(q, l, s, e) == None{} : Maybe<&2, P.PkError>}) -> {P.packing.check.buf(Nat.is_le(Nat.mul(l, 8n), s), q, l) == None{} : Maybe<&2, P.PkError>}:
  %pk.r2(q, l, s, e, h) : {P.packing.check.wide(_, q, l, s) == None{} : Maybe<&2, P.PkError>}
  pk.h2(q, l, s, e, h)

def pk.r3(+q: V.PkQuirks, +l: Nat, +s: Nat, +e: Nat, +h: {P.packing.check(q, l, s, e) == None{} : Maybe<&2, P.PkError>}) -> {Nat.is_le(Nat.mul(l, 8n), s) == False{} : Bool}:
  pk.c_buf(Nat.is_le(Nat.mul(l, 8n), s), q, l, pk.h3(q, l, s, e, h))

def pk.fit_eq(-e: Nat, -s: Nat, -lf: Nat, -lv: Nat, -m8: Nat, ha: {Nat.add(e, lf) == 1n+s : Nat}, hv: {lv == m8 : Nat}) -> {Nat.is_le(Nat.add(e, lf), lv) == Nat.is_le(1n+s, m8) : Bool}:
  %Equal.sym(Nat, Nat.add(e, lf), 1n+s, ha) : {Nat.is_le(_, lv) == Nat.is_le(1n+s, m8) : Bool}
  %Equal.sym(Nat, lv, m8, hv) : {Nat.is_le(1n+s, _) == Nat.is_le(1n+s, m8) : Bool}
  {==}

# The field's bits: w of them, ending at bit start

def pk.len_f(+v: W.W64, +w: Nat, +hw: {Nat.is_le(w, 64n) == True{} : Bool}) -> {List.length(&2, Bool, List.take(&2, Bool, F.packing.w64_bits(v), w)) == w : Nat}:
  PW.pw.take_len(F.packing.w64_bits(v), w, Equal.trans(Bool, Nat.is_le(w, List.length(&2, Bool, F.packing.w64_bits(v))), Nat.is_le(w, 64n), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(w, z), List.length(&2, Bool, F.packing.w64_bits(v)), 64n, PW.pw.bits_len(v)), hw))

def pk.end_f(+q: V.PkQuirks, +l: Nat, +s: Nat, +e: Nat, +v: W.W64, +h: {P.packing.check(q, l, s, e) == None{} : Maybe<&2, P.PkError>}) -> {Nat.add(e, List.length(&2, Bool, List.take(&2, Bool, F.packing.w64_bits(v), P.packing.width(s, e)))) == 1n+s : Nat}:
  +w = P.packing.width(s, e)
  +les = pk.nlt(s, e, pk.r1(q, l, s, e, h))
  Equal.trans(Nat, Nat.add(e, List.length(&2, Bool, List.take(&2, Bool, F.packing.w64_bits(v), w))), Nat.add(e, w), 1n+s, Equal.cong(Nat, Nat, z => Nat.add(e, z), List.length(&2, Bool, List.take(&2, Bool, F.packing.w64_bits(v), w)), w, pk.len_f(v, w, pk.nlt(64n, w, pk.r2(q, l, s, e, h)))), pk.add_sub(e, 1n+s, pk.le_trans(e, s, 1n+s, les, pk.le_succ(s))))

# the view of the buffer after a put, and its length

def pk.sp_len(+q: V.PkQuirks, +xs: List<&2, U32>, +e: Nat, +f: List<&2, Bool>) -> {List.length(&2, Bool, F.packing.splice(V.packing.view(q, xs), e, f)) == Nat.mul(List.length(&2, U32, xs), 8n) : Nat}:
  Equal.trans(Nat, List.length(&2, Bool, F.packing.splice(V.packing.view(q, xs), e, f)), List.length(&2, Bool, V.packing.view(q, xs)), Nat.mul(List.length(&2, U32, xs), 8n), PL.pl.splice_len(V.packing.view(q, xs), e, f), Laws.view_len(q, xs))

def pk.put_view(+q: V.PkQuirks, +xs: List<&2, U32>, +e: Nat, +f: List<&2, Bool>) -> {V.packing.view(q, B.Octets.to_list(B.Octets.of_list(V.packing.unview(q, F.packing.splice(V.packing.view(q, xs), e, f))))) == F.packing.splice(V.packing.view(q, xs), e, f) : List<&2, Bool>}:
  +sp = F.packing.splice(V.packing.view(q, xs), e, f)
  +u = V.packing.unview(q, sp)
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(u)), B.mask(u), BL.octets_to_of(u)) : {V.packing.view(q, _) == sp : List<&2, Bool>}
  %Equal.sym(List<&2, Bool>, V.packing.view(q, B.mask(u)), V.packing.view(q, u), Laws.view_mask(q, u)) : {_ == sp : List<&2, Bool>}
  Laws.view_unview(q, sp, List.length(&2, U32, xs), pk.sp_len(q, xs, e, f))

def pk.put_len(+q: V.PkQuirks, +xs: List<&2, U32>, +e: Nat, +f: List<&2, Bool>) -> {List.length(&2, U32, B.Octets.to_list(B.Octets.of_list(V.packing.unview(q, F.packing.splice(V.packing.view(q, xs), e, f))))) == List.length(&2, U32, xs) : Nat}:
  +sp = F.packing.splice(V.packing.view(q, xs), e, f)
  +u = V.packing.unview(q, sp)
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(u)), B.mask(u), BL.octets_to_of(u)) : {List.length(&2, U32, _) == List.length(&2, U32, xs) : Nat}
  Equal.trans(Nat, List.length(&2, U32, B.mask(u)), List.length(&2, U32, u), List.length(&2, U32, xs), PL.pl.mask_len(u), Laws.unview_len(q, sp, List.length(&2, U32, xs), pk.sp_len(q, xs, e, f)))

# unpacking after a put reads the bits put

def pk.core(+q: V.PkQuirks, +xs: List<&2, U32>, +s: Nat, +e: Nat, +v: W.W64, +hc: {P.packing.check(q, List.length(&2, U32, xs), s, e) == None{} : Maybe<&2, P.PkError>}) -> {P.packing.unpack(q, P.packing.put(q, xs, e, P.packing.width(s, e), v), s, e) == Done{F.packing.bits_w64(List.take(&2, Bool, F.packing.w64_bits(v), P.packing.width(s, e)))} : Result<&2, &2, P.PkError, W.W64>}:
  +w = P.packing.width(s, e)
  +f = List.take(&2, Bool, F.packing.w64_bits(v), w)
  +vw = V.packing.view(q, xs)
  +sp = F.packing.splice(vw, e, f)
  +ys = B.Octets.to_list(B.Octets.of_list(V.packing.unview(q, sp)))
  %Equal.sym(Nat, List.length(&2, U32, ys), List.length(&2, U32, xs), pk.put_len(q, xs, e, f)) : {P.packing.unpack.go(P.packing.check(q, _, s, e), q, ys, e, w) == Done{F.packing.bits_w64(f)} : Result<&2, &2, P.PkError, W.W64>}
  %Equal.sym(Maybe<&2, P.PkError>, P.packing.check(q, List.length(&2, U32, xs), s, e), None{}, hc) : {P.packing.unpack.go(_, q, ys, e, w) == Done{F.packing.bits_w64(f)} : Result<&2, &2, P.PkError, W.W64>}
  %Equal.sym(List<&2, Bool>, V.packing.view(q, ys), sp, pk.put_view(q, xs, e, f)) : {Done{F.packing.bits_w64(F.packing.slice(_, e, w))} == Done{F.packing.bits_w64(f)} : Result<&2, &2, P.PkError, W.W64>}
  %pk.len_f(v, w, pk.nlt(64n, w, pk.r2(q, List.length(&2, U32, xs), s, e, hc))) : {Done{F.packing.bits_w64(F.packing.slice(sp, e, _))} == Done{F.packing.bits_w64(f)} : Result<&2, &2, P.PkError, W.W64>}
  +fit = Equal.trans(Bool, Nat.is_le(Nat.add(e, List.length(&2, Bool, f)), List.length(&2, Bool, vw)), Nat.is_le(1n+s, Nat.mul(List.length(&2, U32, xs), 8n)), True{}, pk.fit_eq(e, s, List.length(&2, Bool, f), List.length(&2, Bool, vw), Nat.mul(List.length(&2, U32, xs), 8n), pk.end_f(q, List.length(&2, U32, xs), s, e, v, hc), Laws.view_len(q, xs)), pk.nle(Nat.mul(List.length(&2, U32, xs), 8n), s, pk.r3(q, List.length(&2, U32, xs), s, e, hc)))
  %Equal.sym(List<&2, Bool>, F.packing.slice(sp, e, List.length(&2, Bool, f)), f, PL.pl.slice_splice(vw, e, f, fit)) : {Done{F.packing.bits_w64(_)} == Done{F.packing.bits_w64(f)} : Result<&2, &2, P.PkError, W.W64>}
  {==}

# What pack answers when it answers Done

def pk.od(r: Result<&2, &2, P.PkError, B.Octets>) -> B.Octets:
  match r:
    case Fail{x}:
      B.Octets.empty()
    case Done{o}:
      o

def pk.rd(r: Result<&2, &2, P.PkError, B.Octets>) -> Type:
  match r:
    case Fail{x}:
      Empty
    case Done{o}:
      Unit

def pk.fd(-x: P.PkError, -y: B.Octets, e: {Fail{x} == Done{y} : Result<&2, &2, P.PkError, B.Octets>}) -> Empty:
  %Equal.sym(Result<&2, &2, P.PkError, B.Octets>, Fail{x}, Done{y}, e) : pk.rd(_)
  Unit{}

def pk.i_up(m: Maybe<&2, P.PkError>, ok: Bool, +q: V.PkQuirks, +xs: List<&2, U32>, +s: Nat, +e: Nat, +v: W.W64, -b: B.Octets, +em: {P.packing.check(q, List.length(&2, U32, xs), s, e) == m : Maybe<&2, P.PkError>}, +eok: {F.packing.fits(v, P.packing.width(s, e)) == ok : Bool}, +h: {P.packing.pack.go(m, ok, q, xs, e, P.packing.width(s, e), v) == Done{b} : Result<&2, &2, P.PkError, B.Octets>}) -> {P.packing.unpack(q, b, s, e) == Done{v} : Result<&2, &2, P.PkError, W.W64>}:
  match m ok:
    case None{} True{}:
      +w = P.packing.width(s, e)
      %Equal.cong(Result<&2, &2, P.PkError, B.Octets>, B.Octets, z => pk.od(z), Done{P.packing.put(q, xs, e, w, v)}, Done{b}, h) : {P.packing.unpack(q, _, s, e) == Done{v} : Result<&2, &2, P.PkError, W.W64>}
      %Equal.sym(Result<&2, &2, P.PkError, W.W64>, P.packing.unpack(q, P.packing.put(q, xs, e, w, v), s, e), Done{F.packing.bits_w64(List.take(&2, Bool, F.packing.w64_bits(v), w))}, pk.core(q, xs, s, e, v, em)) : {_ == Done{v} : Result<&2, &2, P.PkError, W.W64>}
      %Equal.sym(W.W64, F.packing.bits_w64(List.take(&2, Bool, F.packing.w64_bits(v), w)), v, PW.pw.fits_low(v, w, eok)) : {Done{_} == Done{v} : Result<&2, &2, P.PkError, W.W64>}
      {==}
    case None{} False{}:
      Empty.absurd({P.packing.unpack(q, b, s, e) == Done{v} : Result<&2, &2, P.PkError, W.W64>}, pk.fd(P.PkOverflow{}, b, h))
    case Some{x} _:
      Empty.absurd({P.packing.unpack(q, b, s, e) == Done{v} : Result<&2, &2, P.PkError, W.W64>}, pk.fd(x, b, h))

def Laws.unpack_pack(q, buf, start, end, v, b, e):
  pk.i_up(P.packing.check(q, List.length(&2, U32, B.Octets.to_list(buf)), start, end), F.packing.fits(v, P.packing.width(start, end)), q, B.Octets.to_list(buf), start, end, v, b, {==}, {==}, e)

def pk.i_upm(m: Maybe<&2, P.PkError>, +q: V.PkQuirks, +xs: List<&2, U32>, +s: Nat, +e: Nat, +v: W.W64, -b: B.Octets, +em: {P.packing.check(q, List.length(&2, U32, xs), s, e) == m : Maybe<&2, P.PkError>}, +h: {P.packing.pack.go(m, True{}, q, xs, e, P.packing.width(s, e), v) == Done{b} : Result<&2, &2, P.PkError, B.Octets>}) -> {P.packing.unpack(q, b, s, e) == Done{F.packing.low(v, P.packing.width(s, e))} : Result<&2, &2, P.PkError, W.W64>}:
  match m:
    case None{}:
      %Equal.cong(Result<&2, &2, P.PkError, B.Octets>, B.Octets, z => pk.od(z), Done{P.packing.put(q, xs, e, P.packing.width(s, e), v)}, Done{b}, h) : {P.packing.unpack(q, _, s, e) == Done{F.packing.low(v, P.packing.width(s, e))} : Result<&2, &2, P.PkError, W.W64>}
      pk.core(q, xs, s, e, v, em)
    case Some{x}:
      Empty.absurd({P.packing.unpack(q, b, s, e) == Done{F.packing.low(v, P.packing.width(s, e))} : Result<&2, &2, P.PkError, W.W64>}, pk.fd(x, b, h))

def Laws.unpack_pack_masked(q, buf, start, end, v, b, e):
  pk.i_upm(P.packing.check(q, List.length(&2, U32, B.Octets.to_list(buf)), start, end), q, B.Octets.to_list(buf), start, end, v, b, {==}, e)

# Bits outside the field

def pk.hk_of(-e: Nat, +s: Nat, +k: Nat, -lf: Nat, ha: {Nat.add(e, lf) == 1n+s : Nat}, h: {Bool.or(Nat.is_lt(k, e), Nat.is_lt(s, k)) == True{} : Bool}) -> {Bool.or(Nat.is_lt(k, e), Nat.is_le(Nat.add(e, lf), k)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(e, lf), 1n+s, ha) : {Bool.or(Nat.is_lt(k, e), Nat.is_le(_, k)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(1n+s, k), Nat.is_lt(s, k), pk.le_succ_lt(s, k)) : {Bool.or(Nat.is_lt(k, e), _) == True{} : Bool}
  h

def pk.core_rest(+q: V.PkQuirks, +xs: List<&2, U32>, +s: Nat, +e: Nat, +v: W.W64, +k: Nat, +hc: {P.packing.check(q, List.length(&2, U32, xs), s, e) == None{} : Maybe<&2, P.PkError>}, +hk: {Bool.or(Nat.is_lt(k, e), Nat.is_lt(s, k)) == True{} : Bool}) -> {P.packing.bit(q, P.packing.put(q, xs, e, P.packing.width(s, e), v), k) == F.packing.nth(V.packing.view(q, xs), k) : Bool}:
  +f = List.take(&2, Bool, F.packing.w64_bits(v), P.packing.width(s, e))
  +vw = V.packing.view(q, xs)
  %Equal.sym(List<&2, Bool>, V.packing.view(q, B.Octets.to_list(B.Octets.of_list(V.packing.unview(q, F.packing.splice(vw, e, f))))), F.packing.splice(vw, e, f), pk.put_view(q, xs, e, f)) : {F.packing.nth(_, k) == F.packing.nth(vw, k) : Bool}
  PL.pl.nth_splice(vw, e, f, k, pk.hk_of(e, s, k, List.length(&2, Bool, f), pk.end_f(q, List.length(&2, U32, xs), s, e, v, hc), hk))

def pk.i_rest(m: Maybe<&2, P.PkError>, ok: Bool, +q: V.PkQuirks, +xs: List<&2, U32>, +s: Nat, +e: Nat, +v: W.W64, -b: B.Octets, +k: Nat, +hk: {Bool.or(Nat.is_lt(k, e), Nat.is_lt(s, k)) == True{} : Bool}, +em: {P.packing.check(q, List.length(&2, U32, xs), s, e) == m : Maybe<&2, P.PkError>}, +h: {P.packing.pack.go(m, ok, q, xs, e, P.packing.width(s, e), v) == Done{b} : Result<&2, &2, P.PkError, B.Octets>}) -> {P.packing.bit(q, b, k) == F.packing.nth(V.packing.view(q, xs), k) : Bool}:
  match m ok:
    case None{} True{}:
      %Equal.cong(Result<&2, &2, P.PkError, B.Octets>, B.Octets, z => pk.od(z), Done{P.packing.put(q, xs, e, P.packing.width(s, e), v)}, Done{b}, h) : {P.packing.bit(q, _, k) == F.packing.nth(V.packing.view(q, xs), k) : Bool}
      pk.core_rest(q, xs, s, e, v, k, em, hk)
    case None{} False{}:
      Empty.absurd({P.packing.bit(q, b, k) == F.packing.nth(V.packing.view(q, xs), k) : Bool}, pk.fd(P.PkOverflow{}, b, h))
    case Some{x} _:
      Empty.absurd({P.packing.bit(q, b, k) == F.packing.nth(V.packing.view(q, xs), k) : Bool}, pk.fd(x, b, h))

def Laws.pack_rest(q, buf, start, end, v, b, e, k, h):
  pk.i_rest(P.packing.check(q, List.length(&2, U32, B.Octets.to_list(buf)), start, end), F.packing.fits(v, P.packing.width(start, end)), q, B.Octets.to_list(buf), start, end, v, b, k, h, {==}, e)

def Laws.pack_masked_rest(q, buf, start, end, v, b, e, k, h):
  pk.i_rest(P.packing.check(q, List.length(&2, U32, B.Octets.to_list(buf)), start, end), True{}, q, B.Octets.to_list(buf), start, end, v, b, k, h, {==}, e)

# The length

def pk.i_len(m: Maybe<&2, P.PkError>, ok: Bool, +q: V.PkQuirks, +xs: List<&2, U32>, +s: Nat, +e: Nat, +v: W.W64, -b: B.Octets, +h: {P.packing.pack.go(m, ok, q, xs, e, P.packing.width(s, e), v) == Done{b} : Result<&2, &2, P.PkError, B.Octets>}) -> {B.Octets.len(b) == List.length(&2, U32, xs) : Nat}:
  match m ok:
    case None{} True{}:
      +f = List.take(&2, Bool, F.packing.w64_bits(v), P.packing.width(s, e))
      %Equal.cong(Result<&2, &2, P.PkError, B.Octets>, B.Octets, z => pk.od(z), Done{P.packing.put(q, xs, e, P.packing.width(s, e), v)}, Done{b}, h) : {B.Octets.len(_) == List.length(&2, U32, xs) : Nat}
      Equal.trans(Nat, B.Octets.len(P.packing.put(q, xs, e, P.packing.width(s, e), v)), List.length(&2, U32, B.Octets.to_list(P.packing.put(q, xs, e, P.packing.width(s, e), v))), List.length(&2, U32, xs), BL.octets_len_list(P.packing.put(q, xs, e, P.packing.width(s, e), v)), pk.put_len(q, xs, e, f))
    case None{} False{}:
      Empty.absurd({B.Octets.len(b) == List.length(&2, U32, xs) : Nat}, pk.fd(P.PkOverflow{}, b, h))
    case Some{x} _:
      Empty.absurd({B.Octets.len(b) == List.length(&2, U32, xs) : Nat}, pk.fd(x, b, h))

def Laws.pack_len(q, buf, start, end, v, b, e):
  Equal.trans(Nat, B.Octets.len(b), List.length(&2, U32, B.Octets.to_list(buf)), B.Octets.len(buf), pk.i_len(P.packing.check(q, List.length(&2, U32, B.Octets.to_list(buf)), start, end), F.packing.fits(v, P.packing.width(start, end)), q, B.Octets.to_list(buf), start, end, v, b, e), Equal.sym(Nat, B.Octets.len(buf), B.len(B.Octets.to_list(buf)), BL.octets_len_list(buf)))

# Vectors

def Laws.vec_plain():
  {==}

def Laws.vec_little_endian():
  {==}

def Laws.vec_msb_right():
  {==}

def Laws.vec_lsw32_first():
  {==}

def Laws.vec_unpack():
  {==}

def Laws.vec_errors():
  {==}
