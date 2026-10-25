import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./sample.bend as Sm
import ./stuck.bend as Sk
import ./health.bend as Ht
import ./jitter.bend as J
import ./LAWS_constant.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF.bend as UP
import ../u32/PROOF_order.bend as UOP

# ---------------------------------------------------------------- logic

def nat.lt0(m: Nat) -> {Nat.is_lt(m, 0n) == False{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

def ab.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def ab.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : ab.bool(_)
  Unit{}

def ab.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : ab.bool(_)
  Unit{}

def and_false_r(y: Bool) -> {Bool.and(y, False{}) == False{} : Bool}:
  match y:
    case True{}:
      {==}
    case False{}:
      {==}

# ---------------------------------------------------------------- samples

def u32_eq_self(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{+w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, UO.word_cmp_refl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# every sample equals itself
def sample_eq_self(+t: W.W64) -> {Sm.JitSample.eq(t, t) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(W.W64.lo(t), W.W64.lo(t)), True{}, u32_eq_self(W.W64.lo(t))) : {Bool.and(_, U32.is_eq(W.W64.hi(t), W.W64.hi(t))) == True{} : Bool}
  u32_eq_self(W.W64.hi(t))

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

# ---------------------------------------------------------------- Nat

# not a <= b: b < a
def nat.nle_lt(a: Nat, b: Nat, h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ab.tf(h))
    case 0n 1n+bp:
      Empty.absurd({Nat.is_lt(1n+bp, 0n) == True{} : Bool}, ab.tf(h))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      nat.nle_lt(ap, bp, h)

# a < b: not b <= a
def nat.lt_nle(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_le(0n, a) == False{} : Bool}, ab.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, nat.lt0(a)), h)))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      nat.lt_nle(ap, bp, h)

# a <= b < a is impossible
def nat.le_lt(a: Nat, b: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_lt(b, a) == True{} : Bool}) -> Empty:
  match a b:
    case 0n 0n:
      ab.ft(h2)
    case 0n 1n+bp:
      ab.ft(h2)
    case 1n+ap 0n:
      ab.ft(h1)
    case 1n+ap 1n+bp:
      nat.le_lt(ap, bp, h1, h2)

# 2 <= r: 1 < r
def nat.lt1(r: Nat, h: {Nat.is_le(2n, r) == True{} : Bool}) -> {Nat.is_lt(1n, r) == True{} : Bool}:
  match r:
    case 0n:
      Empty.absurd({Nat.is_lt(1n, 0n) == True{} : Bool}, ab.ft(h))
    case 1n+r1:
      match r1:
        case 0n:
          Empty.absurd({Nat.is_lt(1n, 1n) == True{} : Bool}, ab.ft(h))
        case 1n+r2:
          {==}

# 2 <= r <= 0 is impossible
def nat.le2_0(r: Nat, h: {Nat.is_le(2n, r) == True{} : Bool}, k: {Nat.is_le(r, 0n) == True{} : Bool}) -> Empty:
  match r:
    case 0n:
      ab.ft(h)
    case 1n+q:
      ab.ft(k)

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

# ---------------------------------------------------------------- the tests on a repeated delta

# a repeated delta below the RCT's cutoff: the run grows, no failure
def rct_step(+c: Nat, +d: W.W64, +b: Nat, hf: {Nat.is_le(c, 1n+b) == False{} : Bool}) -> {Ht.JitRct.feed(c, Ht.JitRct{d, b, True{}, False{}}, d) == Ht.JitRct{d, 1n+b, True{}, False{}} : Ht.JitRct}:
  %Equal.sym(Bool, Sm.JitSample.eq(d, d), True{}, sample_eq_self(d)) : {Ht.jit.rct.same(_, c, d, b, False{}, d) == Ht.JitRct{d, 1n+b, True{}, False{}} : Ht.JitRct}
  %Equal.sym(Bool, Nat.is_le(c, 1n+b), False{}, hf) : {Ht.JitRct{d, 1n+b, True{}, Bool.or(False{}, _)} == Ht.JitRct{d, 1n+b, True{}, False{}} : Ht.JitRct}
  {==}

# a repeated delta at the RCT's cutoff: failure
def rct_trip(+c: Nat, +d: W.W64, +b: Nat, ht: {Nat.is_le(c, 1n+b) == True{} : Bool}) -> {Ht.JitRct.failed(Ht.JitRct.feed(c, Ht.JitRct{d, b, True{}, False{}}, d)) == True{} : Bool}:
  %Equal.sym(Bool, Sm.JitSample.eq(d, d), True{}, sample_eq_self(d)) : {Ht.JitRct.failed(Ht.jit.rct.same(_, c, d, b, False{}, d)) == True{} : Bool}
  ht

# a repeated delta in an open APT window, below its cutoff
def apt_step(+aw: Nat, +c: Nat, +d: W.W64, +b: Nat, ho: {Nat.is_lt(1n+b, aw) == True{} : Bool}, hf: {Nat.is_le(c, 1n+b) == False{} : Bool}) -> {Ht.JitApt.feed(aw, c, Ht.JitApt{d, b, b, True{}, False{}}, d) == Ht.JitApt{d, 1n+b, 1n+b, True{}, False{}} : Ht.JitApt}:
  %Equal.sym(Bool, Sm.JitSample.eq(d, d), True{}, sample_eq_self(d)) : {Ht.jit.apt.same(_, aw, c, d, b, 1n+b, False{}) == Ht.JitApt{d, 1n+b, 1n+b, True{}, False{}} : Ht.JitApt}
  %Equal.sym(Bool, Nat.is_lt(1n+b, aw), True{}, ho) : {Ht.JitApt{d, 1n+b, 1n+b, _, Bool.or(False{}, Nat.is_le(c, 1n+b))} == Ht.JitApt{d, 1n+b, 1n+b, True{}, False{}} : Ht.JitApt}
  %Equal.sym(Bool, Nat.is_le(c, 1n+b), False{}, hf) : {Ht.JitApt{d, 1n+b, 1n+b, True{}, Bool.or(False{}, _)} == Ht.JitApt{d, 1n+b, 1n+b, True{}, False{}} : Ht.JitApt}
  {==}

# ---------------------------------------------------------------- the read loop

# a delta that counts towards no block: no block is taken
def cb_false(~H: Data, ~bsize: Nat, ~update: H -> B.Octets -> H, ~digest: B.Octets -> B.Octets, +p: J.JitParams, +pool: H, +s: Sk.JitStuckState, +r: Ht.JitRct, +a: Ht.JitApt, +c: Nat, +dis: Nat, +d: W.W64, hc: {Nat.is_le(J.JitParams.need(p), J.jit.count(Sk.JitStuck.is_stuck(s, d), c)) == False{} : Bool}) -> {J.Jitter.can_block(~H, p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.JitState{pool, s, r, a, c, dis}, d)) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(J.JitParams.need(p), J.jit.count(Sk.JitStuck.is_stuck(s, d), c)), False{}, hc) : {Bool.and(Bool.not(J.Jitter.failed(~H, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.JitState{pool, s, r, a, c, dis}, d))), _) == False{} : Bool}
  and_false_r(Bool.not(J.Jitter.failed(~H, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.JitState{pool, s, r, a, c, dis}, d))))

# one step of the read loop when no block can be taken
def step(~H: Data, ~bsize: Nat, ~update: H -> B.Octets -> H, ~digest: B.Octets -> B.Octets, ~take: H -> J.JitTaken<H>, +p: J.JitParams, +st: J.JitState<H>, +d: W.W64, +rest: List<&2, W.W64>, +acc: B.Octets, +n: Nat, hcb: {J.Jitter.can_block(~H, p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d)) == False{} : Bool}) -> {J.jit.go(~H, ~bsize, ~update, ~digest, ~take, Con{d, rest}, False{}, False{}, p, st, acc, n) == J.jit.go(~H, ~bsize, ~update, ~digest, ~take, rest, Nat.is_le(n, B.Octets.len(acc)), J.Jitter.failed(~H, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d)), p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d), acc, n) : Result<&2, &2, J.JitError, J.JitOut<H>>}:
  %Equal.sym(Bool, J.Jitter.can_block(~H, p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d)), False{}, hcb) : {J.jit.go(~H, ~bsize, ~update, ~digest, ~take, rest, Nat.is_le(n, B.Octets.len(J.JitAcc.acc(~H, J.jit.emit(~H, ~take, _, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d), acc)))), J.Jitter.failed(~H, J.JitAcc.state(~H, J.jit.emit(~H, ~take, _, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d), acc))), p, J.JitAcc.state(~H, J.jit.emit(~H, ~take, _, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d), acc)), J.JitAcc.acc(~H, J.jit.emit(~H, ~take, _, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d), acc)), n) == J.jit.go(~H, ~bsize, ~update, ~digest, ~take, rest, Nat.is_le(n, B.Octets.len(acc)), J.Jitter.failed(~H, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d)), p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, st, d), acc, n) : Result<&2, &2, J.JitError, J.JitOut<H>>}
  {==}

# a failed generator stops the read loop with the reason
def fl(~H: Data, ~bsize: Nat, ~update: H -> B.Octets -> H, ~digest: B.Octets -> B.Octets, ~take: H -> J.JitTaken<H>, +p: J.JitParams, +st: J.JitState<H>, ds: List<&2, W.W64>, +acc: B.Octets, +n: Nat, h: {J.Jitter.failed(~H, st) == True{} : Bool}) -> {J.jit.go(~H, ~bsize, ~update, ~digest, ~take, ds, False{}, J.Jitter.failed(~H, st), p, st, acc, n) == Fail{J.Jitter.why(~H, p, st)} : Result<&2, &2, J.JitError, J.JitOut<H>>}:
  match ds:
    case Nil{}:
      %Equal.sym(Bool, J.Jitter.failed(~H, st), True{}, h) : {J.jit.go(~H, ~bsize, ~update, ~digest, ~take, Nil{}, False{}, _, p, st, acc, n) == Fail{J.Jitter.why(~H, p, st)} : Result<&2, &2, J.JitError, J.JitOut<H>>}
      {==}
    case Con{+x, +t}:
      %Equal.sym(Bool, J.Jitter.failed(~H, st), True{}, h) : {J.jit.go(~H, ~bsize, ~update, ~digest, ~take, Con{x, t}, False{}, _, p, st, acc, n) == Fail{J.Jitter.why(~H, p, st)} : Result<&2, &2, J.JitError, J.JitOut<H>>}
      {==}

# The loop: after b copies of d (b below the RCT's cutoff), with the RCT
# and the APT counting b copies and nothing failed, and d stuck, m more
# copies (enough to reach the cutoff) make the read fail with the RCT
def loop(~H: Data, ~bsize: Nat, ~update: H -> B.Octets -> H, ~digest: B.Octets -> B.Octets, ~take: H -> J.JitTaken<H>, m: Nat, +p: J.JitParams, +pool: H, +s: Sk.JitStuckState, +c: Nat, +dis: Nat, +d: W.W64, +b: Nat, +n: Nat, t: Bool, +ht: {Nat.is_le(J.JitParams.rct_cutoff(p), 1n+b) == t : Bool}, +hk: {Sk.JitStuck.is_stuck(s, d) == True{} : Bool}, +hc: {Nat.is_le(J.JitParams.need(p), c) == False{} : Bool}, +hb: {Nat.is_lt(b, J.JitParams.rct_cutoff(p)) == True{} : Bool}, +hm: {Nat.is_le(J.JitParams.rct_cutoff(p), Nat.add(b, m)) == True{} : Bool}, +hw: {Nat.is_le(J.JitParams.rct_cutoff(p), J.JitParams.apt_window(p)) == True{} : Bool}, +ha: {Nat.is_le(J.JitParams.rct_cutoff(p), J.JitParams.apt_cutoff(p)) == True{} : Bool}) -> {J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, m, d), False{}, J.Jitter.failed(~H, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}), p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, B.Octets.empty(), 1n+n) == Fail{J.JitRctFailure{}} : Result<&2, &2, J.JitError, J.JitOut<H>>}:
  match m:
    case 0n:
      Empty.absurd({J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, 0n, d), False{}, J.Jitter.failed(~H, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}), p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, B.Octets.empty(), 1n+n) == Fail{J.JitRctFailure{}} : Result<&2, &2, J.JitError, J.JitOut<H>>}, nat.le_lt(J.JitParams.rct_cutoff(p), b, Equal.trans(Bool, Nat.is_le(J.JitParams.rct_cutoff(p), b), Nat.is_le(J.JitParams.rct_cutoff(p), Nat.add(b, 0n)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(J.JitParams.rct_cutoff(p), z), b, Nat.add(b, 0n), Equal.sym(Nat, Nat.add(b, 0n), b, UL.nat_add_zero(b))), hm), hb))
    case 1n+ +q:
      match t:
        case True{}:
          Equal.trans(Result<&2, &2, J.JitError, J.JitOut<H>>, J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, 1n+q, d), False{}, J.Jitter.failed(~H, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}), p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, B.Octets.empty(), 1n+n), J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, q, d), Nat.is_le(1n+n, B.Octets.len(B.Octets.empty())), J.Jitter.failed(~H, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, d)), p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, d), B.Octets.empty(), 1n+n), Fail{J.JitRctFailure{}}, step(~H, ~bsize, ~update, ~digest, ~take, p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, d, List.replicate(W.W64, q, d), B.Octets.empty(), 1n+n, cb_false(~H, ~bsize, ~update, ~digest, p, pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis, d, Equal.trans(Bool, Nat.is_le(J.JitParams.need(p), J.jit.count(Sk.JitStuck.is_stuck(s, d), c)), Nat.is_le(J.JitParams.need(p), J.jit.count(True{}, c)), False{}, Equal.cong(Bool, Bool, z => Nat.is_le(J.JitParams.need(p), J.jit.count(z, c)), Sk.JitStuck.is_stuck(s, d), True{}, hk), hc))), Equal.trans(Result<&2, &2, J.JitError, J.JitOut<H>>, J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, q, d), Nat.is_le(1n+n, B.Octets.len(B.Octets.empty())), J.Jitter.failed(~H, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, d)), p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, d), B.Octets.empty(), 1n+n), Fail{J.Jitter.why(~H, p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, d))}, Fail{J.JitRctFailure{}}, fl(~H, ~bsize, ~update, ~digest, ~take, p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, d), List.replicate(W.W64, q, d), B.Octets.empty(), 1n+n, Equal.trans(Bool, J.Jitter.failed(~H, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, d)), Bool.or(True{}, Ht.JitApt.failed(Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d))), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, Ht.JitApt.failed(Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d))), Ht.JitRct.failed(Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d)), True{}, rct_trip(J.JitParams.rct_cutoff(p), d, b, ht)), {==})), Equal.cong(J.JitError, Result<&2, &2, J.JitError, J.JitOut<H>>, z => Fail{z}, J.Jitter.why(~H, p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, d)), J.JitRctFailure{}, Equal.trans(J.JitError, J.Jitter.why(~H, p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, d)), J.jit.why.go(True{}, Ht.JitApt.failed(Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d)), J.jit.count(Sk.JitStuck.is_stuck(s, d), c), J.JitParams.need(p)), J.JitRctFailure{}, Equal.cong(Bool, J.JitError, z => J.jit.why.go(z, Ht.JitApt.failed(Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d)), J.jit.count(Sk.JitStuck.is_stuck(s, d), c), J.JitParams.need(p)), Ht.JitRct.failed(Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d)), True{}, rct_trip(J.JitParams.rct_cutoff(p), d, b, ht)), {==}))))
        case False{}:
          Equal.trans(Result<&2, &2, J.JitError, J.JitOut<H>>, J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, 1n+q, d), False{}, J.Jitter.failed(~H, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}), p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, B.Octets.empty(), 1n+n), J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, q, d), Nat.is_le(1n+n, B.Octets.len(B.Octets.empty())), J.Jitter.failed(~H, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, d)), p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, d), B.Octets.empty(), 1n+n), Fail{J.JitRctFailure{}}, step(~H, ~bsize, ~update, ~digest, ~take, p, J.JitState{pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis}, d, List.replicate(W.W64, q, d), B.Octets.empty(), 1n+n, cb_false(~H, ~bsize, ~update, ~digest, p, pool, s, Ht.JitRct{d, b, True{}, False{}}, Ht.JitApt{d, b, b, True{}, False{}}, c, dis, d, Equal.trans(Bool, Nat.is_le(J.JitParams.need(p), J.jit.count(Sk.JitStuck.is_stuck(s, d), c)), Nat.is_le(J.JitParams.need(p), J.jit.count(True{}, c)), False{}, Equal.cong(Bool, Bool, z => Nat.is_le(J.JitParams.need(p), J.jit.count(z, c)), Sk.JitStuck.is_stuck(s, d), True{}, hk), hc))), Equal.trans(Result<&2, &2, J.JitError, J.JitOut<H>>, J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, q, d), False{}, J.Jitter.failed(~H, J.JitState{update(pool, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d)))), Sk.JitStuck.next(s, d), Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d), J.jit.count(Sk.JitStuck.is_stuck(s, d), c), dis}), p, J.JitState{update(pool, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d)))), Sk.JitStuck.next(s, d), Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d), J.jit.count(Sk.JitStuck.is_stuck(s, d), c), dis}, B.Octets.empty(), 1n+n), J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, q, d), False{}, J.Jitter.failed(~H, J.JitState{update(pool, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d)))), Sk.JitStuck.next(s, d), Ht.JitRct{d, 1n+b, True{}, False{}}, Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d), J.jit.count(Sk.JitStuck.is_stuck(s, d), c), dis}), p, J.JitState{update(pool, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d)))), Sk.JitStuck.next(s, d), Ht.JitRct{d, 1n+b, True{}, False{}}, Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d), J.jit.count(Sk.JitStuck.is_stuck(s, d), c), dis}, B.Octets.empty(), 1n+n), Fail{J.JitRctFailure{}}, Equal.cong(Ht.JitRct, Result<&2, &2, J.JitError, J.JitOut<H>>, x => J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, q, d), False{}, J.Jitter.failed(~H, J.JitState{update(pool, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d)))), Sk.JitStuck.next(s, d), x, Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d), J.jit.count(Sk.JitStuck.is_stuck(s, d), c), dis}), p, J.JitState{update(pool, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d)))), Sk.JitStuck.next(s, d), x, Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d), J.jit.count(Sk.JitStuck.is_stuck(s, d), c), dis}, B.Octets.empty(), 1n+n), Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d), Ht.JitRct{d, 1n+b, True{}, False{}}, rct_step(J.JitParams.rct_cutoff(p), d, b, ht)), Equal.trans(Result<&2, &2, J.JitError, J.JitOut<H>>, J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, q, d), False{}, J.Jitter.failed(~H, J.JitState{update(pool, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d)))), Sk.JitStuck.next(s, d), Ht.JitRct{d, 1n+b, True{}, False{}}, Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d), J.jit.count(Sk.JitStuck.is_stuck(s, d), c), dis}), p, J.JitState{update(pool, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d)))), Sk.JitStuck.next(s, d), Ht.JitRct{d, 1n+b, True{}, False{}}, Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d), J.jit.count(Sk.JitStuck.is_stuck(s, d), c), dis}, B.Octets.empty(), 1n+n), J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, q, d), False{}, J.Jitter.failed(~H, J.JitState{update(pool, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d)))), Sk.JitStuck.next(s, d), Ht.JitRct{d, 1n+b, True{}, False{}}, Ht.JitApt{d, 1n+b, 1n+b, True{}, False{}}, J.jit.count(Sk.JitStuck.is_stuck(s, d), c), dis}), p, J.JitState{update(pool, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d)))), Sk.JitStuck.next(s, d), Ht.JitRct{d, 1n+b, True{}, False{}}, Ht.JitApt{d, 1n+b, 1n+b, True{}, False{}}, J.jit.count(Sk.JitStuck.is_stuck(s, d), c), dis}, B.Octets.empty(), 1n+n), Fail{J.JitRctFailure{}}, Equal.cong(Ht.JitApt, Result<&2, &2, J.JitError, J.JitOut<H>>, y => J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, q, d), False{}, J.Jitter.failed(~H, J.JitState{update(pool, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d)))), Sk.JitStuck.next(s, d), Ht.JitRct{d, 1n+b, True{}, False{}}, y, J.jit.count(Sk.JitStuck.is_stuck(s, d), c), dis}), p, J.JitState{update(pool, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d)))), Sk.JitStuck.next(s, d), Ht.JitRct{d, 1n+b, True{}, False{}}, y, J.jit.count(Sk.JitStuck.is_stuck(s, d), c), dis}, B.Octets.empty(), 1n+n), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d), Ht.JitApt{d, 1n+b, 1n+b, True{}, False{}}, apt_step(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), d, b, UO.nat_lt_le_trans(1n+b, J.JitParams.rct_cutoff(p), J.JitParams.apt_window(p), nat.nle_lt(J.JitParams.rct_cutoff(p), 1n+b, ht), hw), nat.lt_nle(1n+b, J.JitParams.apt_cutoff(p), UO.nat_lt_le_trans(1n+b, J.JitParams.rct_cutoff(p), J.JitParams.apt_cutoff(p), nat.nle_lt(J.JitParams.rct_cutoff(p), 1n+b, ht), ha)))), loop(~H, ~bsize, ~update, ~digest, ~take, q, p, update(pool, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct{d, b, True{}, False{}}, d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt{d, b, b, True{}, False{}}, d)))), Sk.JitStuck.next(s, d), J.jit.count(Sk.JitStuck.is_stuck(s, d), c), dis, d, 1n+b, n, Nat.is_le(J.JitParams.rct_cutoff(p), 2n+b), {==}, stuck_rep(s, d), Equal.trans(Bool, Nat.is_le(J.JitParams.need(p), J.jit.count(Sk.JitStuck.is_stuck(s, d), c)), Nat.is_le(J.JitParams.need(p), J.jit.count(True{}, c)), False{}, Equal.cong(Bool, Bool, z => Nat.is_le(J.JitParams.need(p), J.jit.count(z, c)), Sk.JitStuck.is_stuck(s, d), True{}, hk), hc), nat.nle_lt(J.JitParams.rct_cutoff(p), 1n+b, ht), Equal.trans(Bool, Nat.is_le(J.JitParams.rct_cutoff(p), 1n+Nat.add(b, q)), Nat.is_le(J.JitParams.rct_cutoff(p), Nat.add(b, 1n+q)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(J.JitParams.rct_cutoff(p), z), 1n+Nat.add(b, q), Nat.add(b, 1n+q), Equal.sym(Nat, Nat.add(b, 1n+q), 1n+Nat.add(b, q), UL.nat_add_succ(b, q))), hm), hw, ha))))

# the APT's first sample opens a window of at least two
def apt_first(+aw: Nat, +c: Nat, +d: W.W64, ho: {Nat.is_lt(1n, aw) == True{} : Bool}) -> {Ht.JitApt.feed(aw, c, Ht.JitApt.new(), d) == Ht.JitApt{d, 1n, 1n, True{}, False{}} : Ht.JitApt}:
  %Equal.sym(Bool, Nat.is_lt(1n, aw), True{}, ho) : {Ht.JitApt{d, 1n, 1n, _, False{}} == Ht.JitApt{d, 1n, 1n, True{}, False{}} : Ht.JitApt}
  {==}

# A new generator given m copies of d, m at least the RCT's cutoff
def gen(~H: Data, ~bsize: Nat, ~init: H, ~update: H -> B.Octets -> H, ~digest: B.Octets -> B.Octets, ~take: H -> J.JitTaken<H>, +p: J.JitParams, +d: W.W64, m: Nat, +n: Nat, +h1: {Nat.is_lt(1n, J.JitParams.need(p)) == True{} : Bool}, +h2: {Nat.is_le(2n, J.JitParams.rct_cutoff(p)) == True{} : Bool}, +h3: {Nat.is_le(J.JitParams.rct_cutoff(p), J.JitParams.apt_window(p)) == True{} : Bool}, +h4: {Nat.is_le(J.JitParams.rct_cutoff(p), J.JitParams.apt_cutoff(p)) == True{} : Bool}, +h5: {Nat.is_le(J.JitParams.rct_cutoff(p), m) == True{} : Bool}) -> {J.JitCore.generate(~H, ~bsize, ~init, ~update, ~digest, ~take, p, List.replicate(W.W64, m, d), 1n+n) == Fail{J.JitRctFailure{}} : Result<&2, &2, J.JitError, J.JitOut<H>>}:
  match m:
    case 0n:
      Empty.absurd({J.JitCore.generate(~H, ~bsize, ~init, ~update, ~digest, ~take, p, List.replicate(W.W64, 0n, d), 1n+n) == Fail{J.JitRctFailure{}} : Result<&2, &2, J.JitError, J.JitOut<H>>}, nat.le2_0(J.JitParams.rct_cutoff(p), h2, h5))
    case 1n+ +q:
      Equal.trans(Result<&2, &2, J.JitError, J.JitOut<H>>, J.JitCore.generate(~H, ~bsize, ~init, ~update, ~digest, ~take, p, List.replicate(W.W64, 1n+q, d), 1n+n), J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, q, d), Nat.is_le(1n+n, B.Octets.len(B.Octets.empty())), J.Jitter.failed(~H, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.Jitter.init(~H, ~init, p), d)), p, J.Jitter.absorb(~H, ~bsize, ~update, ~digest, p, J.Jitter.init(~H, ~init, p), d), B.Octets.empty(), 1n+n), Fail{J.JitRctFailure{}}, step(~H, ~bsize, ~update, ~digest, ~take, p, J.Jitter.init(~H, ~init, p), d, List.replicate(W.W64, q, d), B.Octets.empty(), 1n+n, cb_false(~H, ~bsize, ~update, ~digest, p, init, Sk.JitStuck.new(), Ht.JitRct.new(), Ht.JitApt.new(), 0n, J.JitParams.prime(p), d, few(J.JitParams.need(p), h1, Sk.JitStuck.is_stuck(Sk.JitStuck.new(), d)))), Equal.trans(Result<&2, &2, J.JitError, J.JitOut<H>>, J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, q, d), False{}, J.Jitter.failed(~H, J.JitState{update(init, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct.new(), d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt.new(), d)))), Sk.JitStuck.next(Sk.JitStuck.new(), d), Ht.JitRct{d, 1n, True{}, False{}}, Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt.new(), d), J.jit.count(Sk.JitStuck.is_stuck(Sk.JitStuck.new(), d), 0n), J.JitParams.prime(p)}), p, J.JitState{update(init, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct.new(), d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt.new(), d)))), Sk.JitStuck.next(Sk.JitStuck.new(), d), Ht.JitRct{d, 1n, True{}, False{}}, Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt.new(), d), J.jit.count(Sk.JitStuck.is_stuck(Sk.JitStuck.new(), d), 0n), J.JitParams.prime(p)}, B.Octets.empty(), 1n+n), J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, q, d), False{}, J.Jitter.failed(~H, J.JitState{update(init, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct.new(), d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt.new(), d)))), Sk.JitStuck.next(Sk.JitStuck.new(), d), Ht.JitRct{d, 1n, True{}, False{}}, Ht.JitApt{d, 1n, 1n, True{}, False{}}, J.jit.count(Sk.JitStuck.is_stuck(Sk.JitStuck.new(), d), 0n), J.JitParams.prime(p)}), p, J.JitState{update(init, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct.new(), d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt.new(), d)))), Sk.JitStuck.next(Sk.JitStuck.new(), d), Ht.JitRct{d, 1n, True{}, False{}}, Ht.JitApt{d, 1n, 1n, True{}, False{}}, J.jit.count(Sk.JitStuck.is_stuck(Sk.JitStuck.new(), d), 0n), J.JitParams.prime(p)}, B.Octets.empty(), 1n+n), Fail{J.JitRctFailure{}}, Equal.cong(Ht.JitApt, Result<&2, &2, J.JitError, J.JitOut<H>>, y => J.jit.go(~H, ~bsize, ~update, ~digest, ~take, List.replicate(W.W64, q, d), False{}, J.Jitter.failed(~H, J.JitState{update(init, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct.new(), d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt.new(), d)))), Sk.JitStuck.next(Sk.JitStuck.new(), d), Ht.JitRct{d, 1n, True{}, False{}}, y, J.jit.count(Sk.JitStuck.is_stuck(Sk.JitStuck.new(), d), 0n), J.JitParams.prime(p)}), p, J.JitState{update(init, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct.new(), d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt.new(), d)))), Sk.JitStuck.next(Sk.JitStuck.new(), d), Ht.JitRct{d, 1n, True{}, False{}}, y, J.jit.count(Sk.JitStuck.is_stuck(Sk.JitStuck.new(), d), 0n), J.JitParams.prime(p)}, B.Octets.empty(), 1n+n), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt.new(), d), Ht.JitApt{d, 1n, 1n, True{}, False{}}, apt_first(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), d, UO.nat_lt_le_trans(1n, J.JitParams.rct_cutoff(p), J.JitParams.apt_window(p), nat.lt1(J.JitParams.rct_cutoff(p), h2), h3))), loop(~H, ~bsize, ~update, ~digest, ~take, q, p, update(init, J.jit.buf(~bsize, ~digest, p, d, J.jit.aux(p, Ht.JitRct.feed(J.JitParams.rct_cutoff(p), Ht.JitRct.new(), d), Ht.JitApt.feed(J.JitParams.apt_window(p), J.JitParams.apt_cutoff(p), Ht.JitApt.new(), d)))), Sk.JitStuck.next(Sk.JitStuck.new(), d), J.jit.count(Sk.JitStuck.is_stuck(Sk.JitStuck.new(), d), 0n), J.JitParams.prime(p), d, 1n, n, Nat.is_le(J.JitParams.rct_cutoff(p), 2n), {==}, stuck_rep(Sk.JitStuck.new(), d), few(J.JitParams.need(p), h1, Sk.JitStuck.is_stuck(Sk.JitStuck.new(), d)), nat.lt1(J.JitParams.rct_cutoff(p), h2), h5, h3, h4)))

# ---------------------------------------------------------------- the laws

def Laws.core_constant_fails(H, bsize, init, update, digest, take, p, d, m, n, h1, h2, h3, h4, h5):
  gen(~H, ~bsize, ~init, ~update, ~digest, ~take, p, d, m, n, h1, h2, h3, h4, h5)

def Laws.constant_fails(H, bsize, init, update, final, digest, p, d, m, n, h1, h2, h3, h4, h5):
  gen(~H, ~bsize, ~init, ~update, ~digest, ~J.JitCond.hash(~H, ~init, ~update, ~final), p, d, m, n, h1, h2, h3, h4, h5)

def Laws.constant_fails_default(H, bsize, init, update, final, digest, d, m, n, h):
  gen(~H, ~bsize, ~init, ~update, ~digest, ~J.JitCond.hash(~H, ~init, ~update, ~final), J.JitParams.default(), d, m, n, {==}, {==}, {==}, {==}, h)
