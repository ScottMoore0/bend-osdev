import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../word64/word64.bend as W
import ./sample.bend as Sm
import ./stuck.bend as Sk
import ./health.bend as Ht
import ./jitter.bend as J
import ./LAWS.bend as Laws

# ---------------------------------------------------------------- logic

def ab.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def ab.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : ab.bool(_)
  Unit{}

def ab.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : ab.bool(_)
  Unit{}

def or_true_r(f: Bool) -> {Bool.or(f, True{}) == True{} : Bool}:
  match f:
    case True{}:
      {==}
    case False{}:
      {==}

def and_false_r(y: Bool) -> {Bool.and(y, False{}) == False{} : Bool}:
  match y:
    case True{}:
      {==}
    case False{}:
      {==}

# ---------------------------------------------------------------- samples

def bool_cmp_self(b: Bool) -> {Word.cmp.fin(b, b, EQ{}) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def word_cmp_self(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{+b, t}:
          Equal.trans(Cmp, Word.cmp.fin(b, b, Word.cmp(p, t, t)), Word.cmp.fin(b, b, EQ{}), EQ{},
            Equal.cong(Cmp, Cmp, x => Word.cmp.fin(b, b, x), Word.cmp(p, t, t), EQ{}, word_cmp_self(p, t)),
            bool_cmp_self(b))

def u32_eq_self(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{+w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, word_cmp_self(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# every sample equals itself
def sample_eq_self(+t: W.W64) -> {Sm.JitSample.eq(t, t) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(W.W64.lo(t), W.W64.lo(t)), True{}, u32_eq_self(W.W64.lo(t))) : {Bool.and(_, U32.is_eq(W.W64.hi(t), W.W64.hi(t))) == True{} : Bool}
  u32_eq_self(W.W64.hi(t))

# ---------------------------------------------------------------- Nat

def nat.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, nat.add_zero(p))

def nat.add_succ(m: Nat, +b: Nat) -> {Nat.add(m, 1n+b) == 1n+Nat.add(m, b) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+ +q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(q, 1n+b), 1n+Nat.add(q, b), nat.add_succ(q, b))

def nat.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      nat.le_refl(p)

def nat.le_succ(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 1n) == True{} : Bool}, ab.ft(e))
    case 1n+ap 1n+bp:
      nat.le_succ(ap, bp, e)

def nat.le_add(+c: Nat, +a: Nat, d: Nat, h: {Nat.is_le(c, a) == True{} : Bool}) -> {Nat.is_le(c, Nat.add(d, a)) == True{} : Bool}:
  match d:
    case 0n:
      h
    case 1n+ +q:
      nat.le_succ(c, Nat.add(q, a), nat.le_add(c, a, q, h))

def nat.succ_not_le(n: Nat) -> {Nat.is_le(1n+n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      nat.succ_not_le(p)

def nat.le_false.go(+c: Nat, +a: Nat, +d: Nat, b: Bool, eb: {Nat.is_le(c, a) == b : Bool}, h: {Nat.is_le(c, Nat.add(d, a)) == False{} : Bool}) -> {Nat.is_le(c, a) == False{} : Bool}:
  match b:
    case False{}:
      eb
    case True{}:
      Empty.absurd({Nat.is_le(c, a) == False{} : Bool}, ab.tf(Equal.trans(Bool, True{}, Nat.is_le(c, Nat.add(d, a)), False{}, Equal.sym(Bool, Nat.is_le(c, Nat.add(d, a)), True{}, nat.le_add(c, a, d, eb)), h)))

# c <= a fails when c <= d + a fails
def nat.le_false(+c: Nat, +a: Nat, +d: Nat, h: {Nat.is_le(c, Nat.add(d, a)) == False{} : Bool}) -> {Nat.is_le(c, a) == False{} : Bool}:
  nat.le_false.go(c, a, d, Nat.is_le(c, a), {==}, h)

# a < w when 1 + d + a <= w
def nat.lt_of_le(a: Nat, +d: Nat, w: Nat, h: {Nat.is_le(1n+Nat.add(d, a), w) == True{} : Bool}) -> {Nat.is_lt(a, w) == True{} : Bool}:
  match a:
    case 0n:
      match w:
        case 0n:
          Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ab.ft(h))
        case 1n+ +v:
          {==}
    case 1n+ +q:
      match w:
        case 0n:
          Empty.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, ab.ft(h))
        case 1n+ +v:
          nat.lt_of_le(q, d, v, Equal.trans(Bool, Nat.is_le(1n+Nat.add(d, q), v), Nat.is_le(1n+Nat.add(d, 1n+q), 1n+v), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(1n+z, 1n+v), 1n+Nat.add(d, q), Nat.add(d, 1n+q), Equal.sym(Nat, Nat.add(d, 1n+q), 1n+Nat.add(d, q), nat.add_succ(d, q))), h))

# 2 + k <= 1 + (k + 1)
def h_cut(+k: Nat) -> {Nat.is_le(2n+k, 1n+Nat.add(k, 1n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(k, 1n), 1n+Nat.add(k, 0n), nat.add_succ(k, 0n)) : {Nat.is_le(2n+k, 1n+_) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(k, 0n), k, nat.add_zero(k)) : {Nat.is_le(2n+k, 2n+_) == True{} : Bool}
  nat.le_refl(2n+k)

# not 2 + k <= k + 1
def h_below(+k: Nat) -> {Nat.is_le(2n+k, Nat.add(k, 1n)) == False{} : Bool}:
  %Equal.sym(Nat, Nat.add(k, 1n), 1n+Nat.add(k, 0n), nat.add_succ(k, 0n)) : {Nat.is_le(2n+k, _) == False{} : Bool}
  %Equal.sym(Nat, Nat.add(k, 0n), k, nat.add_zero(k)) : {Nat.is_le(2n+k, 1n+_) == False{} : Bool}
  nat.succ_not_le(1n+k)

# ---------------------------------------------------------------- the stuck test

def Laws.stuck_zero(s):
  match s:
    case Sk.JitStuckState{p, p2}:
      {==}

def sr.go(+t: W.W64, -q: W.W64, z: Bool, ez: {W.W64.is_zero(t) == z : Bool}) -> {Bool.or(W.W64.is_zero(t), Bool.or(Sm.JitSample.eq(t, t), Sm.JitSample.eq(W.W64.sub(t, t), q))) == True{} : Bool}:
  match z:
    case True{}:
      %Equal.sym(Bool, W.W64.is_zero(t), True{}, ez) : {Bool.or(_, Bool.or(Sm.JitSample.eq(t, t), Sm.JitSample.eq(W.W64.sub(t, t), q))) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, W.W64.is_zero(t), False{}, ez) : {Bool.or(_, Bool.or(Sm.JitSample.eq(t, t), Sm.JitSample.eq(W.W64.sub(t, t), q))) == True{} : Bool}
      %Equal.sym(Bool, Sm.JitSample.eq(t, t), True{}, sample_eq_self(t)) : {Bool.or(_, Sm.JitSample.eq(W.W64.sub(t, t), q)) == True{} : Bool}
      {==}

# the stuck test after t, on t again
def stuck_rep(s: Sk.JitStuckState, +t: W.W64) -> {Sk.JitStuck.is_stuck(Sk.JitStuck.next(s, t), t) == True{} : Bool}:
  match s:
    case Sk.JitStuckState{p, p2}:
      sr.go(t, W.W64.sub(t, p), W.W64.is_zero(t), {==})

def Laws.stuck_repeat(s, t):
  stuck_rep(s, t)

def Laws.stuck_vec_second():
  {==}

def Laws.stuck_vec_moving():
  {==}

# ---------------------------------------------------------------- the Repetition Count Test

# 1 + m more copies of the repeated sample, with c <= 1 + m + b, fail
def rctA(m: Nat, +x: W.W64, +b: Nat, f: Bool, +c: Nat, h: {Nat.is_le(c, 1n+Nat.add(m, b)) == True{} : Bool}) -> {Ht.JitRct.failed(Ht.jit.rct.run(List.replicate(W.W64, 1n+m, x), c, Ht.JitRct{x, b, True{}, f})) == True{} : Bool}:
  match m:
    case 0n:
      %Equal.sym(Bool, Sm.JitSample.eq(x, x), True{}, sample_eq_self(x)) : {Ht.JitRct.failed(Ht.jit.rct.same(_, c, x, b, f, x)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_le(c, 1n+b), True{}, h) : {Bool.or(f, _) == True{} : Bool}
      or_true_r(f)
    case 1n+ +q:
      %Equal.sym(Bool, Sm.JitSample.eq(x, x), True{}, sample_eq_self(x)) : {Ht.JitRct.failed(Ht.jit.rct.run(List.replicate(W.W64, 1n+q, x), c, Ht.jit.rct.same(_, c, x, b, f, x))) == True{} : Bool}
      rctA(q, x, 1n+b, Bool.or(f, Nat.is_le(c, 1n+b)), c, Equal.trans(Bool, Nat.is_le(c, 1n+Nat.add(q, 1n+b)), Nat.is_le(c, 2n+Nat.add(q, b)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(c, 1n+z), Nat.add(q, 1n+b), 1n+Nat.add(q, b), nat.add_succ(q, b)), h))

# m more copies, with not c <= m + b, do not fail
def rctB(m: Nat, +x: W.W64, +b: Nat, +c: Nat, h: {Nat.is_le(c, Nat.add(m, b)) == False{} : Bool}) -> {Ht.JitRct.failed(Ht.jit.rct.run(List.replicate(W.W64, m, x), c, Ht.JitRct{x, b, True{}, False{}})) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+ +q:
      +h2 = Equal.trans(Bool, Nat.is_le(c, Nat.add(q, 1n+b)), Nat.is_le(c, 1n+Nat.add(q, b)), False{}, Equal.cong(Nat, Bool, z => Nat.is_le(c, z), Nat.add(q, 1n+b), 1n+Nat.add(q, b), nat.add_succ(q, b)), h)
      %Equal.sym(Bool, Sm.JitSample.eq(x, x), True{}, sample_eq_self(x)) : {Ht.JitRct.failed(Ht.jit.rct.run(List.replicate(W.W64, q, x), c, Ht.jit.rct.same(_, c, x, b, False{}, x))) == False{} : Bool}
      %Equal.sym(Bool, Nat.is_le(c, 1n+b), False{}, nat.le_false(c, 1n+b, q, h2)) : {Ht.JitRct.failed(Ht.jit.rct.run(List.replicate(W.W64, q, x), c, Ht.JitRct{x, 1n+b, True{}, _})) == False{} : Bool}
      rctB(q, x, 1n+b, c, h2)

def Laws.rct_trips(x, k):
  rctA(k, x, 1n, False{}, 2n+k, h_cut(k))

def Laws.rct_below_cutoff(x, k):
  rctB(k, x, 1n, 2n+k, h_below(k))

def rl.go(+c: Nat, +a: W.W64, +b: Nat, +f: Bool, +x: W.W64, e: Bool, +ee: {Sm.JitSample.eq(x, a) == e : Bool}, h: {f == True{} : Bool}) -> {Ht.JitRct.failed(Ht.jit.rct.same(Sm.JitSample.eq(x, a), c, a, b, f, x)) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(Bool, Sm.JitSample.eq(x, a), True{}, ee) : {Ht.JitRct.failed(Ht.jit.rct.same(_, c, a, b, f, x)) == True{} : Bool}
      %Equal.sym(Bool, f, True{}, h) : {Bool.or(_, Nat.is_le(c, 1n+b)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Sm.JitSample.eq(x, a), False{}, ee) : {Ht.JitRct.failed(Ht.jit.rct.same(_, c, a, b, f, x)) == True{} : Bool}
      h

# a failed RCT stays failed
def rlatch(+c: Nat, r: Ht.JitRct, +x: W.W64, h: {Ht.JitRct.failed(r) == True{} : Bool}) -> {Ht.JitRct.failed(Ht.JitRct.feed(c, r, x)) == True{} : Bool}:
  match r:
    case Ht.JitRct{+a, +b, s, +f}:
      match s:
        case False{}:
          h
        case True{}:
          rl.go(c, a, b, f, x, Sm.JitSample.eq(x, a), {==}, h)

def Laws.rct_latch(c, r, x, h):
  rlatch(c, r, x, h)

# ---------------------------------------------------------------- the Adaptive Proportion Test

# 1 + m more copies of the window's first sample, with c <= 1 + m + b and
# 1 + m + b <= w, fail
def aptA(m: Nat, +x: W.W64, +b: Nat, f: Bool, +c: Nat, +w: Nat, h1: {Nat.is_le(c, 1n+Nat.add(m, b)) == True{} : Bool}, h2: {Nat.is_le(1n+Nat.add(m, b), w) == True{} : Bool}) -> {Ht.JitApt.failed(Ht.jit.apt.run(List.replicate(W.W64, 1n+m, x), w, c, Ht.JitApt{x, b, b, True{}, f})) == True{} : Bool}:
  match m:
    case 0n:
      %Equal.sym(Bool, Sm.JitSample.eq(x, x), True{}, sample_eq_self(x)) : {Ht.JitApt.failed(Ht.jit.apt.same(_, w, c, x, b, 1n+b, f)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_le(c, 1n+b), True{}, h1) : {Bool.or(f, _) == True{} : Bool}
      or_true_r(f)
    case 1n+ +q:
      +h2b = Equal.trans(Bool, Nat.is_le(1n+Nat.add(q, 1n+b), w), Nat.is_le(2n+Nat.add(q, b), w), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(1n+z, w), Nat.add(q, 1n+b), 1n+Nat.add(q, b), nat.add_succ(q, b)), h2)
      %Equal.sym(Bool, Sm.JitSample.eq(x, x), True{}, sample_eq_self(x)) : {Ht.JitApt.failed(Ht.jit.apt.run(List.replicate(W.W64, 1n+q, x), w, c, Ht.jit.apt.same(_, w, c, x, b, 1n+b, f))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_lt(1n+b, w), True{}, nat.lt_of_le(1n+b, q, w, h2b)) : {Ht.JitApt.failed(Ht.jit.apt.run(List.replicate(W.W64, 1n+q, x), w, c, Ht.JitApt{x, 1n+b, 1n+b, _, Bool.or(f, Nat.is_le(c, 1n+b))})) == True{} : Bool}
      aptA(q, x, 1n+b, Bool.or(f, Nat.is_le(c, 1n+b)), c, w, Equal.trans(Bool, Nat.is_le(c, 1n+Nat.add(q, 1n+b)), Nat.is_le(c, 2n+Nat.add(q, b)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(c, 1n+z), Nat.add(q, 1n+b), 1n+Nat.add(q, b), nat.add_succ(q, b)), h1), h2b)

def Laws.apt_trips(x, k, w, h):
  +hw = Equal.trans(Bool, Nat.is_le(1n+Nat.add(k, 1n), w), Nat.is_le(2n+k, w), True{}, Equal.trans(Bool, Nat.is_le(1n+Nat.add(k, 1n), w), Nat.is_le(2n+Nat.add(k, 0n), w), Nat.is_le(2n+k, w), Equal.cong(Nat, Bool, z => Nat.is_le(1n+z, w), Nat.add(k, 1n), 1n+Nat.add(k, 0n), nat.add_succ(k, 0n)), Equal.cong(Nat, Bool, z => Nat.is_le(2n+z, w), Nat.add(k, 0n), k, nat.add_zero(k))), h)
  %Equal.sym(Bool, Nat.is_lt(1n, w), True{}, nat.lt_of_le(1n, k, w, hw)) : {Ht.JitApt.failed(Ht.jit.apt.run(List.replicate(W.W64, 1n+k, x), w, 2n+k, Ht.JitApt{x, 1n, 1n, _, False{}})) == True{} : Bool}
  aptA(k, x, 1n, False{}, 2n+k, w, h_cut(k), hw)

def al.go(+w: Nat, +c: Nat, +a: W.W64, +b: Nat, +i: Nat, +f: Bool, +x: W.W64, e: Bool, +ee: {Sm.JitSample.eq(x, a) == e : Bool}, h: {f == True{} : Bool}) -> {Ht.JitApt.failed(Ht.jit.apt.same(Sm.JitSample.eq(x, a), w, c, a, b, 1n+i, f)) == True{} : Bool}:
  match e:
    case True{}:
      %Equal.sym(Bool, Sm.JitSample.eq(x, a), True{}, ee) : {Ht.JitApt.failed(Ht.jit.apt.same(_, w, c, a, b, 1n+i, f)) == True{} : Bool}
      %Equal.sym(Bool, f, True{}, h) : {Bool.or(_, Nat.is_le(c, 1n+b)) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Sm.JitSample.eq(x, a), False{}, ee) : {Ht.JitApt.failed(Ht.jit.apt.same(_, w, c, a, b, 1n+i, f)) == True{} : Bool}
      h

# a failed APT stays failed
def alatch(+w: Nat, +c: Nat, t: Ht.JitApt, +x: W.W64, h: {Ht.JitApt.failed(t) == True{} : Bool}) -> {Ht.JitApt.failed(Ht.JitApt.feed(w, c, t, x)) == True{} : Bool}:
  match t:
    case Ht.JitApt{+a, +b, +i, o, +f}:
      match o:
        case False{}:
          h
        case True{}:
          al.go(w, c, a, b, i, f, x, Sm.JitSample.eq(x, a), {==}, h)

def Laws.apt_latch(w, c, t, x, h):
  alatch(w, c, t, x, h)

def Laws.apt_vec_window():
  {==}

def Laws.apt_vec_restart():
  {==}

# ---------------------------------------------------------------- the generator

def aa(~H: Data, ~bsize: Nat, ~update: H -> B.Octets -> H, ~digest: B.Octets -> B.Octets, a: List<&2, W.W64>, +b: List<&2, W.W64>, +p: J.JitParams, st: J.JitState<H>) -> {J.jit.absorb_all(~H, ~bsize, ~update, ~digest, b, p, J.jit.absorb_all(~H, ~bsize, ~update, ~digest, a, p, st)) == J.jit.absorb_all(~H, ~bsize, ~update, ~digest, List.append(&2, W.W64, a, b), p, st) : J.JitState<H>}:
  match a:
    case Nil{}:
      {==}
    case Con{d, t}:
      aa(~H, ~bsize, ~update, ~digest, t, b, p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d))

def Laws.absorb_all_append(H, bsize, update, digest, p, st, a, b):
  aa(~H, ~bsize, ~update, ~digest, a, b, p, st)

def af.go(+p: J.JitParams, +r: Ht.JitRct, +a: Ht.JitApt, +d: W.W64, fr: Bool, efr: {Ht.JitRct.failed(r) == fr : Bool}, h: {Bool.or(Ht.JitRct.failed(r), Ht.JitApt.failed(a)) == True{} : Bool}) -> {Bool.or(Ht.JitRct.failed(Ht.JitRct.feed(J.JitParams.rct_cutoff(p), r, d)), Ht.JitApt.failed(Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), a, d))) == True{} : Bool}:
  match fr:
    case True{}:
      %Equal.sym(Bool, Ht.JitRct.failed(Ht.JitRct.feed(J.JitParams.rct_cutoff(p), r, d)), True{}, rlatch(J.JitParams.rct_cutoff(p), r, d, efr)) : {Bool.or(_, Ht.JitApt.failed(Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), a, d))) == True{} : Bool}
      {==}
    case False{}:
      +ha = Equal.trans(Bool, Ht.JitApt.failed(a), Bool.or(Ht.JitRct.failed(r), Ht.JitApt.failed(a)), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, Ht.JitApt.failed(a)), False{}, Ht.JitRct.failed(r), Equal.sym(Bool, Ht.JitRct.failed(r), False{}, efr)), h)
      %Equal.sym(Bool, Ht.JitApt.failed(Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), a, d)), True{}, alatch(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), a, d, ha)) : {Bool.or(Ht.JitRct.failed(Ht.JitRct.feed(J.JitParams.rct_cutoff(p), r, d)), _) == True{} : Bool}
      or_true_r(Ht.JitRct.failed(Ht.JitRct.feed(J.JitParams.rct_cutoff(p), r, d)))

def Laws.absorb_failed(H, bsize, update, digest, p, st, d, h):
  match st:
    case J.JitState{pool, s, +r, +a, c, dis}:
      af.go(p, r, a, d, Ht.JitRct.failed(r), {==}, h)

# after a delta, the same delta again does not count
def cnt_again(~H: Data, ~bsize: Nat, ~update: H -> B.Octets -> H, ~digest: B.Octets -> B.Octets, +p: J.JitParams, st: J.JitState<H>, +d: W.W64) -> {J.Jitter.count(~H, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d), d)) == J.Jitter.count(~H, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d)) : Nat}:
  match st:
    case J.JitState{pool, +s, r, a, +c, dis}:
      %Equal.sym(Bool, Sk.JitStuck.is_stuck(Sk.JitStuck.next(s, d), d), True{}, stuck_rep(s, d)) : {J.jit.count(_, J.jit.count(Sk.JitStuck.is_stuck(s, d), c)) == J.jit.count(Sk.JitStuck.is_stuck(s, d), c) : Nat}
      {==}

# after a delta, repeating it any number of times does not change the count
def cnt_rep(~H: Data, ~bsize: Nat, ~update: H -> B.Octets -> H, ~digest: B.Octets -> B.Octets, m: Nat, +p: J.JitParams, +st: J.JitState<H>, +d: W.W64) -> {J.Jitter.count(~H, J.jit.absorb_all(~H, ~bsize, ~update, ~digest, List.replicate(W.W64, m, d), p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d))) == J.Jitter.count(~H, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d)) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+ +q:
      Equal.trans(Nat, J.Jitter.count(~H, J.jit.absorb_all(~H, ~bsize, ~update, ~digest, List.replicate(W.W64, q, d), p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d), d))), J.Jitter.count(~H, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d), d)), J.Jitter.count(~H, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d)), cnt_rep(~H, ~bsize, ~update, ~digest, q, p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d), d), cnt_again(~H, ~bsize, ~update, ~digest, p, st, d))

# a block needs two or more counted deltas: none and one are too few
def few(n: Nat, h: {Nat.is_lt(1n, n) == True{} : Bool}, b: Bool) -> {Nat.is_le(n, J.jit.count(b, 0n)) == False{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({Nat.is_le(0n, J.jit.count(b, 0n)) == False{} : Bool}, ab.ft(h))
    case 1n+ +n1:
      match n1:
        case 0n:
          Empty.absurd({Nat.is_le(1n, J.jit.count(b, 0n)) == False{} : Bool}, ab.ft(h))
        case 1n+ +q:
          match b:
            case True{}:
              {==}
            case False{}:
              {==}

def Laws.stuck_source(H, bsize, init, update, digest, p, h, d, n):
  match n:
    case 0n:
      few(J.JitParams.need(p), h, True{})
    case 1n+ +m:
      %Equal.sym(Nat, J.Jitter.count(~H, J.jit.absorb_all(~H, ~bsize, ~update, ~digest, List.replicate(W.W64, m, d), p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.Jitter.init(~H, ~init, p), d))), J.Jitter.count(~H, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.Jitter.init(~H, ~init, p), d)), cnt_rep(~H, ~bsize, ~update, ~digest, m, p, J.Jitter.init(~H, ~init, p), d)) : {Bool.and(Bool.not(J.Jitter.failed(~H, J.jit.absorb_all(~H, ~bsize, ~update, ~digest, List.replicate(W.W64, m, d), p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.Jitter.init(~H, ~init, p), d)))), Nat.is_le(J.JitParams.need(p), _)) == False{} : Bool}
      %Equal.sym(Bool, Nat.is_le(J.JitParams.need(p), J.jit.count(Sk.JitStuck.is_stuck(Sk.JitStuck.new(), d), 0n)), False{}, few(J.JitParams.need(p), h, Sk.JitStuck.is_stuck(Sk.JitStuck.new(), d))) : {Bool.and(Bool.not(J.Jitter.failed(~H, J.jit.absorb_all(~H, ~bsize, ~update, ~digest, List.replicate(W.W64, m, d), p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.Jitter.init(~H, ~init, p), d)))), _) == False{} : Bool}
      and_false_r(Bool.not(J.Jitter.failed(~H, J.jit.absorb_all(~H, ~bsize, ~update, ~digest, List.replicate(W.W64, m, d), p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.Jitter.init(~H, ~init, p), d)))))

def Laws.block_refused(H, init, update, final, p, st, h):
  %Equal.sym(Bool, J.Jitter.can_block(~H, p, st), False{}, h) : {J.jit.block.go(~H, ~init, ~update, ~final, _, p, st) == Fail{J.Jitter.why(~H, p, st)} : Result<&2, &2, J.JitError, J.JitBlock<H>>}
  {==}

def Laws.read_failed(H, bsize, init, update, final, digest, p, st, ds, n, h):
  match ds:
    case Nil{}:
      %Equal.sym(Bool, J.Jitter.failed(~H, st), True{}, h) : {J.jit.end(~H, False{}, _, p, st, B.Octets.empty(), 1n+n) == Fail{J.Jitter.why(~H, p, st)} : Result<&2, &2, J.JitError, J.JitOut<H>>}
      {==}
    case Con{+d, +rest}:
      %Equal.sym(Bool, J.Jitter.failed(~H, st), True{}, h) : {J.jit.go(~H, ~bsize, ~init, ~update, ~final, ~digest, Con{d, rest}, False{}, _, p, st, B.Octets.empty(), 1n+n) == Fail{J.Jitter.why(~H, p, st)} : Result<&2, &2, J.JitError, J.JitOut<H>>}
      {==}

# ---------------------------------------------------------------- the length of what is read

def mask_len(xs: List<&2, U32>) -> {B.len(B.mask(xs)) == B.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %mask_len(t) : {B.len(B.mask(Con{h, t})) == 1n+_ : Nat}
      {==}

def pad_len(n: Nat, xs: List<&2, U32>) -> {B.len(J.jit.pad(n, xs)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      match xs:
        case Nil{}:
          Equal.cong(Nat, Nat, z => 1n+z, B.len(J.jit.pad(m, Nil{})), m, pad_len(m, Nil{}))
        case Con{x, t}:
          Equal.cong(Nat, Nat, z => 1n+z, B.len(J.jit.pad(m, t)), m, pad_len(m, t))

def fit_len(+n: Nat, +acc: B.Octets) -> {B.Octets.len(J.jit.fit(n, acc)) == n : Nat}:
  +l = J.jit.pad(n, B.Octets.to_list(acc))
  Equal.trans(Nat, B.Octets.len(B.Octets.of_list(l)), B.len(B.Octets.to_list(B.Octets.of_list(l))), n, BL.octets_len_list(B.Octets.of_list(l)), Equal.trans(Nat, B.len(B.Octets.to_list(B.Octets.of_list(l))), B.len(B.mask(l)), n, Equal.cong(List<&2, U32>, Nat, z => B.len(z), B.Octets.to_list(B.Octets.of_list(l)), B.mask(l), BL.octets_to_of(l)), Equal.trans(Nat, B.len(B.mask(l)), B.len(l), n, mask_len(l), pad_len(n, B.Octets.to_list(acc)))))

def gl(~H: Data, ~bsize: Nat, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, ~digest: B.Octets -> B.Octets, ds: List<&2, W.W64>, done: Bool, failed: Bool, +p: J.JitParams, +st: J.JitState<H>, +acc: B.Octets, +n: Nat) -> {Result.map(&2, &2, J.JitError, J.JitOut<H>, Nat, o => B.Octets.len(J.JitOut.out(~H, o)), J.jit.go(~H, ~bsize, ~init, ~update, ~final, ~digest, ds, done, failed, p, st, acc, n)) == Result.map(&2, &2, J.JitError, J.JitOut<H>, Nat, o => n, J.jit.go(~H, ~bsize, ~init, ~update, ~final, ~digest, ds, done, failed, p, st, acc, n)) : Result<&2, &2, J.JitError, Nat>}:
  match ds:
    case Nil{}:
      match done:
        case True{}:
          Equal.cong(Nat, Result<&2, &2, J.JitError, Nat>, z => Done{z}, B.Octets.len(J.jit.fit(n, acc)), n, fit_len(n, acc))
        case False{}:
          match failed:
            case True{}:
              {==}
            case False{}:
              {==}
    case Con{+d, +rest}:
      match done:
        case True{}:
          Equal.cong(Nat, Result<&2, &2, J.JitError, Nat>, z => Done{z}, B.Octets.len(J.jit.fit(n, acc)), n, fit_len(n, acc))
        case False{}:
          match failed:
            case True{}:
              {==}
            case False{}:
              +r = J.jit.emit(~H, ~init, ~update, ~final, J.Jitter.can_block(~H, p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d)), J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d), acc)
              gl(~H, ~bsize, ~init, ~update, ~final, ~digest, rest, Nat.is_le(n, B.Octets.len(J.JitAcc.acc(~H, r))), J.Jitter.failed(~H, J.JitAcc.state(~H, r)), p, J.JitAcc.state(~H, r), J.JitAcc.acc(~H, r), n)

def Laws.read_length(H, bsize, init, update, final, digest, p, st, ds, n):
  gl(~H, ~bsize, ~init, ~update, ~final, ~digest, ds, Nat.is_le(n, 0n), J.Jitter.failed(~H, st), p, st, B.Octets.empty(), n)

def Laws.params_default():
  {==}

def Laws.need_default():
  {==}
