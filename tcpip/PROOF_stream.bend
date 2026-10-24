# Proofs of LAWS_stream.bend.
#
# The plan: say that t is a prefix of z when t == take(len(t), z). Then
# * take(m, z) is a prefix of z (st.pf_take); dropping k bytes from a
#   prefix of z gives a prefix of drop(k, z) (st.pf_drop); and a prefix t
#   of z followed by a prefix of drop(len(t), z) is a prefix of z
#   (st.pf_join): the reassembly lemma, from bend-osdev-bytes' laws of
#   take, drop and append;
# * a held piece RcvSeg{at, d} is the stream's when d is a prefix of
#   drop(at, str); delivering it from next n >= at gives drop(n - at, d), a
#   prefix of drop(at + (n - at), str) = drop(n, str), and the rest is
#   delivered from n + its length, so by induction on the held list what is
#   delivered is a prefix of drop(n, str) (st.pull_data);
# * insertion and delivery only move, keep, drop or choose between pieces,
#   so the held pieces stay the stream's (st.ins_ok, st.pull_held).
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./rcvq.bend as Q
import ./LAWS_stream.bend as Laws

# Nat

def st.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def st.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : st.bool(_)
  Unit{}

def st.sub_zero(y: Nat) -> {Nat.sub(y, 0n) == y : Nat}:
  match y:
    case 0n:
      {==}
    case 1n+p:
      {==}

def st.succ(+a: Nat, +b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  Equal.cong(Nat, Nat, z => 1n+z, a, b, e)

# x + (y - x) = y, for x <= y
def st.add_sub(x: Nat, y: Nat, +h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.add(x, Nat.sub(y, x)) == y : Nat}:
  match x y:
    case 0n _:
      st.sub_zero(y)
    case 1n+ +xp 0n:
      Empty.absurd({Nat.add(1n+xp, Nat.sub(0n, 1n+xp)) == 0n : Nat}, st.ft(h))
    case 1n+ +xp 1n+ +yp:
      st.succ(Nat.add(xp, Nat.sub(yp, xp)), yp, st.add_sub(xp, yp, h))

def st.minmin(m: Nat, z: Nat) -> {Nat.min(Nat.min(m, z), m) == Nat.min(m, z) : Nat}:
  match m z:
    case 0n _:
      {==}
    case 1n+mp 0n:
      {==}
    case 1n+ +mp 1n+ +zp:
      st.succ(Nat.min(Nat.min(mp, zp), mp), Nat.min(mp, zp), st.minmin(mp, zp))

def st.minlen(+x: Nat, +m: Nat, +z: Nat, +e: {x == Nat.min(m, z) : Nat}) -> {Nat.min(x, m) == x : Nat}:
  Equal.trans(Nat, Nat.min(x, m), Nat.min(Nat.min(m, z), m), x, Equal.cong(Nat, Nat, y => Nat.min(y, m), x, Nat.min(m, z), e), Equal.trans(Nat, Nat.min(Nat.min(m, z), m), Nat.min(m, z), x, st.minmin(m, z), Equal.sym(Nat, x, Nat.min(m, z), e)))

# Prefixes: t is a prefix of z when t == take(len(t), z)

def st.take0(+o: B.Octets) -> {B.Octets.take(0n, o) == B.Octets.empty() : B.Octets}:
  Equal.trans(B.Octets, B.Octets.take(0n, o), B.Octets.take(0n, B.Octets.append(B.Octets.empty(), o)), B.Octets.empty(), Equal.cong(B.Octets, B.Octets, y => B.Octets.take(0n, y), o, B.Octets.append(B.Octets.empty(), o), Equal.sym(B.Octets, B.Octets.append(B.Octets.empty(), o), o, BL.octets_append_empty_l(o))), BL.octets_take_append(B.Octets.empty(), o))

def st.pf_take(+m: Nat, +z: B.Octets) -> {B.Octets.take(m, z) == B.Octets.take(B.Octets.len(B.Octets.take(m, z)), z) : B.Octets}:
  +t = B.Octets.take(m, z)
  +l = B.Octets.len(t)
  +e1 = Equal.sym(B.Octets, B.Octets.take(l, t), t, BL.octets_take_len(t))
  +e2 = BL.octets_take_take(l, m, z)
  +e3 = st.minlen(l, m, B.Octets.len(z), BL.octets_len_take(m, z))
  +e4 = Equal.cong(Nat, B.Octets, y => B.Octets.take(y, z), Nat.min(l, m), l, e3)
  Equal.trans(B.Octets, t, B.Octets.take(l, t), B.Octets.take(l, z), e1, Equal.trans(B.Octets, B.Octets.take(l, t), B.Octets.take(Nat.min(l, m), z), B.Octets.take(l, z), e2, e4))

def st.pf_drop(+k: Nat, +t: B.Octets, +z: B.Octets, h: {t == B.Octets.take(B.Octets.len(t), z) : B.Octets}) -> {B.Octets.drop(k, t) == B.Octets.take(B.Octets.len(B.Octets.drop(k, t)), B.Octets.drop(k, z)) : B.Octets}:
  +z2 = B.Octets.drop(k, z)
  +m = Nat.sub(B.Octets.len(t), k)
  +e1 = Equal.cong(B.Octets, B.Octets, y => B.Octets.drop(k, y), t, B.Octets.take(B.Octets.len(t), z), h)
  +e2 = BL.octets_drop_take_comm(k, B.Octets.len(t), z)
  +e12 = Equal.trans(B.Octets, B.Octets.drop(k, t), B.Octets.drop(k, B.Octets.take(B.Octets.len(t), z)), B.Octets.take(m, z2), e1, e2)
  +e3 = st.pf_take(m, z2)
  +e4 = Equal.cong(B.Octets, B.Octets, y => B.Octets.take(B.Octets.len(y), z2), B.Octets.take(m, z2), B.Octets.drop(k, t), Equal.sym(B.Octets, B.Octets.drop(k, t), B.Octets.take(m, z2), e12))
  Equal.trans(B.Octets, B.Octets.drop(k, t), B.Octets.take(m, z2), B.Octets.take(B.Octets.len(B.Octets.drop(k, t)), z2), e12, Equal.trans(B.Octets, B.Octets.take(m, z2), B.Octets.take(B.Octets.len(B.Octets.take(m, z2)), z2), B.Octets.take(B.Octets.len(B.Octets.drop(k, t)), z2), e3, e4))

# the reassembly lemma: a prefix t of x, then a prefix of what follows it
def st.pf_join(+t: B.Octets, +r: B.Octets, +x: B.Octets, +ht: {t == B.Octets.take(B.Octets.len(t), x) : B.Octets}, hr: {r == B.Octets.take(B.Octets.len(r), B.Octets.drop(B.Octets.len(t), x)) : B.Octets}) -> {B.Octets.append(t, r) == B.Octets.take(B.Octets.len(B.Octets.append(t, r)), x) : B.Octets}:
  +dd = B.Octets.drop(B.Octets.len(t), x)
  +n = Nat.add(B.Octets.len(t), B.Octets.len(r))
  +eX = Equal.trans(B.Octets, B.Octets.append(t, dd), B.Octets.append(B.Octets.take(B.Octets.len(t), x), dd), x, Equal.cong(B.Octets, B.Octets, y => B.Octets.append(y, dd), t, B.Octets.take(B.Octets.len(t), x), ht), BL.octets_take_drop(B.Octets.len(t), x))
  +eA = Equal.cong(B.Octets, B.Octets, y => B.Octets.append(t, y), r, B.Octets.take(B.Octets.len(r), dd), hr)
  +eB = Equal.sym(B.Octets, B.Octets.take(n, B.Octets.append(t, dd)), B.Octets.append(t, B.Octets.take(B.Octets.len(r), dd)), BL.octets_take_append_add(t, B.Octets.len(r), dd))
  +eC = Equal.cong(B.Octets, B.Octets, y => B.Octets.take(n, y), B.Octets.append(t, dd), x, eX)
  +eD = Equal.cong(Nat, B.Octets, y => B.Octets.take(y, x), n, B.Octets.len(B.Octets.append(t, r)), Equal.sym(Nat, B.Octets.len(B.Octets.append(t, r)), n, BL.octets_len_append(t, r)))
  Equal.trans(B.Octets, B.Octets.append(t, r), B.Octets.append(t, B.Octets.take(B.Octets.len(r), dd)), B.Octets.take(B.Octets.len(B.Octets.append(t, r)), x), eA, Equal.trans(B.Octets, B.Octets.append(t, B.Octets.take(B.Octets.len(r), dd)), B.Octets.take(n, B.Octets.append(t, dd)), B.Octets.take(B.Octets.len(B.Octets.append(t, r)), x), eB, Equal.trans(B.Octets, B.Octets.take(n, B.Octets.append(t, dd)), B.Octets.take(n, x), B.Octets.take(B.Octets.len(B.Octets.append(t, r)), x), eC, eD)))

# Pieces of the stream

def st.hd(xs: List<&2, Q.RcvSeg>, dflt: Q.RcvSeg) -> Q.RcvSeg:
  match xs:
    case Nil{}:
      dflt
    case Con{h, t}:
      h

def st.tl(xs: List<&2, Q.RcvSeg>) -> List<&2, Q.RcvSeg>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def st.dat(s: Q.RcvSeg) -> B.Octets:
  match s:
    case Q.RcvSeg{a, d}:
      d

def st.split_hd(+s: Q.RcvSeg, +t: List<&2, Q.RcvSeg>, +str: B.Octets, h: {Laws.stream_segs(Con{s, t}, str) == Con{s, t} : List<&2, Q.RcvSeg>}) -> {Laws.stream_seg(s, str) == s : Q.RcvSeg}:
  Equal.cong(List<&2, Q.RcvSeg>, Q.RcvSeg, y => st.hd(y, s), Laws.stream_segs(Con{s, t}, str), Con{s, t}, h)

def st.split_tl(+s: Q.RcvSeg, +t: List<&2, Q.RcvSeg>, +str: B.Octets, h: {Laws.stream_segs(Con{s, t}, str) == Con{s, t} : List<&2, Q.RcvSeg>}) -> {Laws.stream_segs(t, str) == t : List<&2, Q.RcvSeg>}:
  Equal.cong(List<&2, Q.RcvSeg>, List<&2, Q.RcvSeg>, y => st.tl(y), Laws.stream_segs(Con{s, t}, str), Con{s, t}, h)

def st.cons_ok(+s: Q.RcvSeg, +t: List<&2, Q.RcvSeg>, +str: B.Octets, hs: {Laws.stream_seg(s, str) == s : Q.RcvSeg}, ht: {Laws.stream_segs(t, str) == t : List<&2, Q.RcvSeg>}) -> {Laws.stream_segs(Con{s, t}, str) == Con{s, t} : List<&2, Q.RcvSeg>}:
  %Equal.sym(Q.RcvSeg, Laws.stream_seg(s, str), s, hs) : {Con{_, Laws.stream_segs(t, str)} == Con{s, t} : List<&2, Q.RcvSeg>}
  %Equal.sym(List<&2, Q.RcvSeg>, Laws.stream_segs(t, str), t, ht) : {Con{s, _} == Con{s, t} : List<&2, Q.RcvSeg>}
  {==}

def st.seg_new(+at: Nat, +d: B.Octets, +str: B.Octets, hd: {B.Octets.slice(at, B.Octets.len(d), str) == d : B.Octets}) -> {Laws.stream_seg(Q.RcvSeg{at, d}, str) == Q.RcvSeg{at, d} : Q.RcvSeg}:
  Equal.cong(B.Octets, Q.RcvSeg, y => Q.RcvSeg{at, y}, B.Octets.slice(at, B.Octets.len(d), str), d, hd)

def st.longer_ok(nl: Bool, +s: Q.RcvSeg, +h: Q.RcvSeg, +str: B.Octets, hs: {Laws.stream_seg(s, str) == s : Q.RcvSeg}, hh: {Laws.stream_seg(h, str) == h : Q.RcvSeg}) -> {Laws.stream_seg(Q.RcvQ.longer(nl, s, h), str) == Q.RcvQ.longer(nl, s, h) : Q.RcvSeg}:
  match nl:
    case True{}:
      hs
    case False{}:
      hh

def st.same_ok(s: Q.RcvSeg, h: Q.RcvSeg, +str: B.Octets, hs: {Laws.stream_seg(s, str) == s : Q.RcvSeg}, hh: {Laws.stream_seg(h, str) == h : Q.RcvSeg}) -> {Laws.stream_seg(Q.RcvQ.same(s, h), str) == Q.RcvQ.same(s, h) : Q.RcvSeg}:
  match s h:
    case Q.RcvSeg{a, +sd} Q.RcvSeg{b, +hd}:
      st.longer_ok(Nat.is_lt(B.Octets.len(hd), B.Octets.len(sd)), Q.RcvSeg{a, sd}, Q.RcvSeg{b, hd}, str, hs, hh)

# insertion keeps the pieces the stream's
def st.ins_ok(xs: List<&2, Q.RcvSeg>, +s: Q.RcvSeg, +at: Nat, c: Cmp, +str: B.Octets, +hx: {Laws.stream_segs(xs, str) == xs : List<&2, Q.RcvSeg>}, +hs: {Laws.stream_seg(s, str) == s : Q.RcvSeg}) -> {Laws.stream_segs(Q.RcvQ.ins(xs, s, at, c), str) == Q.RcvQ.ins(xs, s, at, c) : List<&2, Q.RcvSeg>}:
  match xs:
    case Nil{}:
      st.cons_ok(s, Nil{}, str, hs, {==})
    case Con{+h, +t}:
      match c:
        case LT{}:
          st.cons_ok(s, Con{h, t}, str, hs, hx)
        case EQ{}:
          st.cons_ok(Q.RcvQ.same(s, h), t, str, st.same_ok(s, h, str, hs, st.split_hd(h, t, str, hx)), st.split_tl(h, t, str, hx))
        case GT{}:
          st.cons_ok(h, Q.RcvQ.ins(t, s, at, Q.RcvQ.head_cmp(at, t)), str, st.split_hd(h, t, str, hx), st.ins_ok(t, s, at, Q.RcvQ.head_cmp(at, t), str, st.split_tl(h, t, str, hx), hs))

def st.admit_ok(ok: Bool, +xs: List<&2, Q.RcvSeg>, +s: Q.RcvSeg, +at: Nat, +str: B.Octets, hx: {Laws.stream_segs(xs, str) == xs : List<&2, Q.RcvSeg>}, hs: {Laws.stream_seg(s, str) == s : Q.RcvSeg}) -> {Laws.stream_segs(Q.RcvQ.admit(ok, xs, s, at), str) == Q.RcvQ.admit(ok, xs, s, at) : List<&2, Q.RcvSeg>}:
  match ok:
    case True{}:
      st.ins_ok(xs, s, at, Q.RcvQ.head_cmp(at, xs), str, hx, hs)
    case False{}:
      hx

# Delivery

def st.cons_data(f: B.Octets, o: Q.RcvOut) -> {Q.RcvOut.data(Q.RcvOut.cons(f, o)) == B.Octets.append(f, Q.RcvOut.data(o)) : B.Octets}:
  match o:
    case Q.RcvOut{n, h, d}:
      {==}

def st.cons_held(f: B.Octets, o: Q.RcvOut) -> {Laws.out_held(Q.RcvOut.cons(f, o)) == Laws.out_held(o) : List<&2, Q.RcvSeg>}:
  match o:
    case Q.RcvOut{n, h, d}:
      {==}

def st.tr_ok(+a: List<&2, Q.RcvSeg>, +b: List<&2, Q.RcvSeg>, +str: B.Octets, +e: {a == b : List<&2, Q.RcvSeg>}, h: {Laws.stream_segs(b, str) == b : List<&2, Q.RcvSeg>}) -> {Laws.stream_segs(a, str) == a : List<&2, Q.RcvSeg>}:
  Equal.trans(List<&2, Q.RcvSeg>, Laws.stream_segs(a, str), Laws.stream_segs(b, str), a, Equal.cong(List<&2, Q.RcvSeg>, List<&2, Q.RcvSeg>, y => Laws.stream_segs(y, str), a, b, e), Equal.trans(List<&2, Q.RcvSeg>, Laws.stream_segs(b, str), b, a, h, Equal.sym(List<&2, Q.RcvSeg>, a, b, e)))

def st.pull_held(xs: List<&2, Q.RcvSeg>, +n: Nat, r: Bool, +str: B.Octets, hx: {Laws.stream_segs(xs, str) == xs : List<&2, Q.RcvSeg>}) -> {Laws.stream_segs(Laws.out_held(Q.RcvQ.pull(xs, n, r)), str) == Laws.out_held(Q.RcvQ.pull(xs, n, r)) : List<&2, Q.RcvSeg>}:
  match xs:
    case Nil{}:
      {==}
    case Con{Q.RcvSeg{+at, +d}, +t}:
      match r:
        case False{}:
          hx
        case True{}:
          +f = B.Octets.drop(Nat.sub(n, at), d)
          +n2 = Nat.add(n, B.Octets.len(f))
          +o = Q.RcvQ.pull(t, n2, Q.RcvQ.ready(t, n2))
          st.tr_ok(Laws.out_held(Q.RcvOut.cons(f, o)), Laws.out_held(o), str, st.cons_held(f, o), st.pull_held(t, n2, Q.RcvQ.ready(t, n2), str, st.split_tl(Q.RcvSeg{at, d}, t, str, hx)))

# what is delivered from the held pieces is a prefix of the stream from n
def st.pull_data(xs: List<&2, Q.RcvSeg>, +n: Nat, r: Bool, er: {Q.RcvQ.ready(xs, n) == r : Bool}, +str: B.Octets, hx: {Laws.stream_segs(xs, str) == xs : List<&2, Q.RcvSeg>}) -> {Q.RcvOut.data(Q.RcvQ.pull(xs, n, r)) == B.Octets.take(B.Octets.len(Q.RcvOut.data(Q.RcvQ.pull(xs, n, r))), B.Octets.drop(n, str)) : B.Octets}:
  match xs:
    case Nil{}:
      Equal.sym(B.Octets, B.Octets.take(0n, B.Octets.drop(n, str)), B.Octets.empty(), st.take0(B.Octets.drop(n, str)))
    case Con{Q.RcvSeg{+at, +d}, +t}:
      match r:
        case False{}:
          Equal.sym(B.Octets, B.Octets.take(0n, B.Octets.drop(n, str)), B.Octets.empty(), st.take0(B.Octets.drop(n, str)))
        case True{}:
          +hx = hx
          +hs = st.split_hd(Q.RcvSeg{at, d}, t, str, hx)
          +ht = st.split_tl(Q.RcvSeg{at, d}, t, str, hx)
          +hdd = Equal.cong(Q.RcvSeg, B.Octets, y => st.dat(y), Laws.stream_seg(Q.RcvSeg{at, d}, str), Q.RcvSeg{at, d}, hs)
          +k = Nat.sub(n, at)
          +f = B.Octets.drop(k, d)
          +n2 = Nat.add(n, B.Octets.len(f))
          +o = Q.RcvQ.pull(t, n2, Q.RcvQ.ready(t, n2))
          +rr = Q.RcvOut.data(o)
          +z = B.Octets.drop(n, str)
          +pd = st.pf_drop(k, d, B.Octets.drop(at, str), Equal.sym(B.Octets, B.Octets.slice(at, B.Octets.len(d), str), d, hdd))
          +edn = Equal.trans(B.Octets, B.Octets.drop(k, B.Octets.drop(at, str)), B.Octets.drop(Nat.add(at, k), str), z, BL.octets_drop_drop(at, k, str), Equal.cong(Nat, B.Octets, y => B.Octets.drop(y, str), Nat.add(at, k), n, st.add_sub(at, n, er)))
          +pf2 = Equal.trans(B.Octets, f, B.Octets.take(B.Octets.len(f), B.Octets.drop(k, B.Octets.drop(at, str))), B.Octets.take(B.Octets.len(f), z), pd, Equal.cong(B.Octets, B.Octets, y => B.Octets.take(B.Octets.len(f), y), B.Octets.drop(k, B.Octets.drop(at, str)), z, edn))
          +ih = st.pull_data(t, n2, Q.RcvQ.ready(t, n2), {==}, str, ht)
          +ih2 = Equal.trans(B.Octets, rr, B.Octets.take(B.Octets.len(rr), B.Octets.drop(n2, str)), B.Octets.take(B.Octets.len(rr), B.Octets.drop(B.Octets.len(f), z)), ih, Equal.cong(B.Octets, B.Octets, y => B.Octets.take(B.Octets.len(rr), y), B.Octets.drop(n2, str), B.Octets.drop(B.Octets.len(f), z), Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(f), z), B.Octets.drop(n2, str), BL.octets_drop_drop(n, B.Octets.len(f), str))))
          +j = st.pf_join(f, rr, z, pf2, ih2)
          +ec = st.cons_data(f, o)
          Equal.trans(B.Octets, Q.RcvOut.data(Q.RcvOut.cons(f, o)), B.Octets.append(f, rr), B.Octets.take(B.Octets.len(Q.RcvOut.data(Q.RcvOut.cons(f, o))), z), ec, Equal.trans(B.Octets, B.Octets.append(f, rr), B.Octets.take(B.Octets.len(B.Octets.append(f, rr)), z), B.Octets.take(B.Octets.len(Q.RcvOut.data(Q.RcvOut.cons(f, o))), z), j, Equal.cong(B.Octets, B.Octets, y => B.Octets.take(B.Octets.len(y), z), B.Octets.append(f, rr), Q.RcvOut.data(Q.RcvOut.cons(f, o)), Equal.sym(B.Octets, Q.RcvOut.data(Q.RcvOut.cons(f, o)), B.Octets.append(f, rr), ec))))

# The laws

def Laws.rcvq_stream(limit, n, held, rel, d, str, hq, hd):
  +at = Nat.add(n, rel)
  +ok = Bool.and(Nat.is_gt(B.Octets.len(d), 0n), Bool.or(Nat.is_eq(rel, 0n), Nat.is_lt(Q.RcvQ.held.count(held, 0n), limit)))
  +xs = Q.RcvQ.admit(ok, held, Q.RcvSeg{at, d}, at)
  +hx = st.admit_ok(ok, held, Q.RcvSeg{at, d}, at, str, hq, st.seg_new(at, d, str, hd))
  Equal.sym(B.Octets, Q.RcvOut.data(Q.RcvQ.pull(xs, n, Q.RcvQ.ready(xs, n))), B.Octets.take(B.Octets.len(Q.RcvOut.data(Q.RcvQ.pull(xs, n, Q.RcvQ.ready(xs, n)))), B.Octets.drop(n, str)), st.pull_data(xs, n, Q.RcvQ.ready(xs, n), {==}, str, hx))

def Laws.rcvq_stream_held(limit, n, held, rel, d, str, hq, hd):
  +at = Nat.add(n, rel)
  +ok = Bool.and(Nat.is_gt(B.Octets.len(d), 0n), Bool.or(Nat.is_eq(rel, 0n), Nat.is_lt(Q.RcvQ.held.count(held, 0n), limit)))
  +xs = Q.RcvQ.admit(ok, held, Q.RcvSeg{at, d}, at)
  st.pull_held(xs, n, Q.RcvQ.ready(xs, n), str, st.admit_ok(ok, held, Q.RcvSeg{at, d}, at, str, hq, st.seg_new(at, d, str, hd)))

# Vectors: by computation

def Laws.rcvq_stream_vec():
  {==}

def Laws.rcvq_stream_sat():
  {==}
