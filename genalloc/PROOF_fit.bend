import Base
import ./bits.bend as Bits
import ./genalloc.bend as G
import ./fit.bend as F
import ./proof_nat.bend as N
import ./proof_bits.bend as PB
import ./LAWS_fit.bend as Laws

# Maybe

def pf.is_none(m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

def pf.ns(-k: Nat, e: {None{} == Some{k} : Maybe<&2, Nat>}) -> Empty:
  %e : pf.is_none(_)
  Unit{}

def pf.sn(-k: Nat, e: {Some{k} == None{} : Maybe<&2, Nat>}) -> Empty:
  %Equal.sym(Maybe<&2, Nat>, Some{k}, None{}, e) : pf.is_none(_)
  Unit{}

def pf.get(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      x

def pf.some_inj(-x: Nat, -y: Nat, e: {Some{x} == Some{y} : Maybe<&2, Nat>}) -> {x == y : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, m => pf.get(m), Some{x}, Some{y}, e)

# Order

def pf.le_ne(s: Nat, j: Nat, l: {Nat.is_le(s, j) == True{} : Bool}, h: {Nat.is_eq(s, j) == False{} : Bool}) -> {Nat.is_le(1n+s, j) == True{} : Bool}:
  match s j:
    case 0n 0n:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, N.nl.tf(h))
    case 0n 1n+jp:
      N.nl.le_zero(jp)
    case 1n+sp 0n:
      Empty.absurd({Nat.is_le(2n+sp, 0n) == True{} : Bool}, N.nl.ft(l))
    case 1n+sp 1n+jp:
      pf.le_ne(sp, jp, l, h)

def pf.nle_succ(s: Nat) -> {Nat.is_le(1n+s, s) == False{} : Bool}:
  match s:
    case 0n:
      {==}
    case 1n+p:
      pf.nle_succ(p)

def pf.and_false(x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# x mod 1 is 0

def pf.dm1(x: Nat, d: Nat) -> {Pair.snd(Nat, Nat, Nat.divmod.go(x, 0n, d, 0n)) == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      pf.dm1(p, 1n+d)

def pf.mod1(x: Nat) -> {Nat.mod(x, 1n) == 0n : Nat}:
  pf.dm1(x, 0n)

# with no offset and an alignment of 1, a candidate is a free run
def pf.cand1(+full: List<&2, Bool>, +j: Nat, +n: Nat, +g: Nat) -> {F.genpool.fit.cand(full, j, n, 0n, g, 1n) == Bits.genpool.bits.run_free(full, j, n) : Bool}:
  %Equal.sym(Nat, Nat.mod(Nat.mul(j, g), 1n), 0n, pf.mod1(Nat.mul(j, g))) : {Bool.and(Nat.is_eq(_, 0n), Bits.genpool.bits.run_free(full, j, n)) == Bits.genpool.bits.run_free(full, j, n) : Bool}
  {==}

# no run of n >= 1 granules starts past the end
def pf.rf_past(u: List<&2, Bool>, j: Nat, +n: Nat, hn: {Nat.is_lt(0n, n) == True{} : Bool}, hj: {Nat.is_le(j, List.length(&2, Bool, u)) == False{} : Bool}) -> {Bits.genpool.bits.run_free(u, j, n) == False{} : Bool}:
  match u j:
    case Nil{} _:
      match n:
        case 0n:
          Empty.absurd({Bits.genpool.bits.run_free(Nil{}, j, 0n) == False{} : Bool}, N.nl.ft(hn))
        case 1n+m:
          {==}
    case Con{b, t} 0n:
      Empty.absurd({Bits.genpool.bits.run_free(Con{b, t}, 0n, n) == False{} : Bool}, N.nl.tf(hj))
    case Con{b, t} 1n+i:
      pf.rf_past(t, i, n, hn, hj)

# The scan behind the first fits: genpool.fit.scan(rest, ok, ...) tries the
# candidates s, s + 1, ..., s + length(rest), and ok is whether s is one

# what it answers is a candidate
def pf.scan_some(rest: List<&2, Bool>, ok: Bool, +full: List<&2, Bool>, +n: Nat, +s: Nat, +off: Nat, +g: Nat, +a: Nat, -k: Nat, hok: {F.genpool.fit.cand(full, s, n, off, g, a) == ok : Bool}, e: {F.genpool.fit.scan(rest, ok, full, n, s, off, g, a) == Some{k} : Maybe<&2, Nat>}) -> {F.genpool.fit.cand(full, k, n, off, g, a) == True{} : Bool}:
  match rest ok:
    case r True{}:
      %pf.some_inj(s, k, e) : {F.genpool.fit.cand(full, _, n, off, g, a) == True{} : Bool}
      hok
    case Nil{} False{}:
      Empty.absurd({F.genpool.fit.cand(full, k, n, off, g, a) == True{} : Bool}, pf.ns(k, e))
    case Con{b, t} False{}:
      pf.scan_some(t, F.genpool.fit.cand(full, 1n+s, n, off, g, a), full, n, 1n+s, off, g, a, k, {==}, e)

# no candidate lies between s and what it answers (c: whether j is s)
def pf.scan_low(rest: List<&2, Bool>, ok: Bool, +full: List<&2, Bool>, +n: Nat, +s: Nat, +off: Nat, +g: Nat, +a: Nat, +k: Nat, +j: Nat, c: Bool, hc: {Nat.is_eq(s, j) == c : Bool}, hok: {F.genpool.fit.cand(full, s, n, off, g, a) == ok : Bool}, e: {F.genpool.fit.scan(rest, ok, full, n, s, off, g, a) == Some{k} : Maybe<&2, Nat>}, l: {Nat.is_le(s, j) == True{} : Bool}, m: {Nat.is_lt(j, k) == True{} : Bool}) -> {F.genpool.fit.cand(full, j, n, off, g, a) == False{} : Bool}:
  match rest ok:
    case r True{}:
      Empty.absurd({F.genpool.fit.cand(full, j, n, off, g, a) == False{} : Bool}, N.nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(j, s), True{}, Equal.sym(Bool, Nat.is_lt(j, s), False{}, N.nl.le_nlt(s, j, l)), Equal.trans(Bool, Nat.is_lt(j, s), Nat.is_lt(j, k), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(j, x), s, k, pf.some_inj(s, k, e)), m))))
    case Nil{} False{}:
      Empty.absurd({F.genpool.fit.cand(full, j, n, off, g, a) == False{} : Bool}, pf.ns(k, e))
    case Con{b, t} False{}:
      match c:
        case True{}:
          %N.nl.eq(s, j, hc) : {F.genpool.fit.cand(full, _, n, off, g, a) == False{} : Bool}
          hok
        case False{}:
          pf.scan_low(t, F.genpool.fit.cand(full, 1n+s, n, off, g, a), full, n, 1n+s, off, g, a, k, j, Nat.is_eq(1n+s, j), {==}, {==}, e, pf.le_ne(s, j, l, hc), m)

# when it answers None, no candidate lies from s to s + length(rest)
def pf.scan_none(rest: List<&2, Bool>, ok: Bool, +full: List<&2, Bool>, +n: Nat, +s: Nat, +off: Nat, +g: Nat, +a: Nat, +j: Nat, c: Bool, hc: {Nat.is_eq(s, j) == c : Bool}, hok: {F.genpool.fit.cand(full, s, n, off, g, a) == ok : Bool}, e: {F.genpool.fit.scan(rest, ok, full, n, s, off, g, a) == None{} : Maybe<&2, Nat>}, l: {Nat.is_le(s, j) == True{} : Bool}, m: {Nat.is_le(j, Nat.add(s, List.length(&2, Bool, rest))) == True{} : Bool}) -> {F.genpool.fit.cand(full, j, n, off, g, a) == False{} : Bool}:
  match rest ok:
    case r True{}:
      Empty.absurd({F.genpool.fit.cand(full, j, n, off, g, a) == False{} : Bool}, pf.sn(s, e))
    case Nil{} False{}:
      match c:
        case True{}:
          %N.nl.eq(s, j, hc) : {F.genpool.fit.cand(full, _, n, off, g, a) == False{} : Bool}
          hok
        case False{}:
          Empty.absurd({F.genpool.fit.cand(full, j, n, off, g, a) == False{} : Bool}, N.nl.ft(Equal.trans(Bool, False{}, Nat.is_le(1n+s, s), True{}, Equal.sym(Bool, Nat.is_le(1n+s, s), False{}, pf.nle_succ(s)), N.nl.le_trans(1n+s, j, s, pf.le_ne(s, j, l, hc), Equal.trans(Bool, Nat.is_le(j, s), Nat.is_le(j, Nat.add(s, 0n)), True{}, Equal.cong(Nat, Bool, x => Nat.is_le(j, x), s, Nat.add(s, 0n), Equal.sym(Nat, Nat.add(s, 0n), s, N.nl.add_zero(s))), m)))))
    case Con{b, +t} False{}:
      match c:
        case True{}:
          %N.nl.eq(s, j, hc) : {F.genpool.fit.cand(full, _, n, off, g, a) == False{} : Bool}
          hok
        case False{}:
          pf.scan_none(t, F.genpool.fit.cand(full, 1n+s, n, off, g, a), full, n, 1n+s, off, g, a, j, Nat.is_eq(1n+s, j), {==}, {==}, e, pf.le_ne(s, j, l, hc), Equal.trans(Bool, Nat.is_le(j, 1n+Nat.add(s, List.length(&2, Bool, t))), Nat.is_le(j, Nat.add(s, 1n+List.length(&2, Bool, t))), True{}, Equal.cong(Nat, Bool, x => Nat.is_le(j, x), 1n+Nat.add(s, List.length(&2, Bool, t)), Nat.add(s, 1n+List.length(&2, Bool, t)), Equal.sym(Nat, Nat.add(s, 1n+List.length(&2, Bool, t)), 1n+Nat.add(s, List.length(&2, Bool, t)), N.nl.add_succ(s, List.length(&2, Bool, t)))), m))

# First fit

def pf.first_none(q: Bool, +bits: List<&2, Bool>, +n: Nat, +g: Nat, +j: Nat, hq: {Nat.is_le(j, List.length(&2, Bool, bits)) == q : Bool}, e: {F.genpool.fit.scan(bits, F.genpool.fit.cand(bits, 0n, n, 0n, g, 1n), bits, n, 0n, 0n, g, 1n) == None{} : Maybe<&2, Nat>}, hn: {Nat.is_lt(0n, n) == True{} : Bool}) -> {Bits.genpool.bits.run_free(bits, j, n) == False{} : Bool}:
  match q:
    case True{}:
      Equal.trans(Bool, Bits.genpool.bits.run_free(bits, j, n), F.genpool.fit.cand(bits, j, n, 0n, g, 1n), False{}, Equal.sym(Bool, F.genpool.fit.cand(bits, j, n, 0n, g, 1n), Bits.genpool.bits.run_free(bits, j, n), pf.cand1(bits, j, n, g)), pf.scan_none(bits, F.genpool.fit.cand(bits, 0n, n, 0n, g, 1n), bits, n, 0n, 0n, g, 1n, j, Nat.is_eq(0n, j), {==}, {==}, e, N.nl.le_zero(j), hq))
    case False{}:
      pf.rf_past(bits, j, n, hn, hq)

def Laws.first_fit_free(d, bits, n, base, g, s, e):
  Equal.trans(Bool, Bits.genpool.bits.run_free(bits, s, n), F.genpool.fit.cand(bits, s, n, 0n, g, 1n), True{}, Equal.sym(Bool, F.genpool.fit.cand(bits, s, n, 0n, g, 1n), Bits.genpool.bits.run_free(bits, s, n), pf.cand1(bits, s, n, g)), pf.scan_some(bits, F.genpool.fit.cand(bits, 0n, n, 0n, g, 1n), bits, n, 0n, 0n, g, 1n, s, {==}, e))

def Laws.first_fit_lowest(d, bits, n, base, g, s, j, e, h):
  Equal.trans(Bool, Bits.genpool.bits.run_free(bits, j, n), F.genpool.fit.cand(bits, j, n, 0n, g, 1n), False{}, Equal.sym(Bool, F.genpool.fit.cand(bits, j, n, 0n, g, 1n), Bits.genpool.bits.run_free(bits, j, n), pf.cand1(bits, j, n, g)), pf.scan_low(bits, F.genpool.fit.cand(bits, 0n, n, 0n, g, 1n), bits, n, 0n, 0n, g, 1n, s, j, Nat.is_eq(0n, j), {==}, {==}, e, N.nl.le_zero(j), h))

def Laws.first_fit_none(d, bits, n, base, g, j, e, hn):
  pf.first_none(Nat.is_le(j, List.length(&2, Bool, bits)), bits, n, g, j, {==}, e, hn)

# First fit with an alignment

def pf.align_none(q: Bool, +al: Nat, +bits: List<&2, Bool>, +n: Nat, +base: Nat, +g: Nat, +j: Nat, hq: {Nat.is_le(j, List.length(&2, Bool, bits)) == q : Bool}, e: {F.genpool.fit.scan(bits, F.genpool.fit.cand(bits, 0n, n, base, g, Nat.max(al, 1n)), bits, n, 0n, base, g, Nat.max(al, 1n)) == None{} : Maybe<&2, Nat>}, hn: {Nat.is_lt(0n, n) == True{} : Bool}) -> {F.genpool.fit.cand(bits, j, n, base, g, Nat.max(al, 1n)) == False{} : Bool}:
  match q:
    case True{}:
      pf.scan_none(bits, F.genpool.fit.cand(bits, 0n, n, base, g, Nat.max(al, 1n)), bits, n, 0n, base, g, Nat.max(al, 1n), j, Nat.is_eq(0n, j), {==}, {==}, e, N.nl.le_zero(j), hq)
    case False{}:
      %Equal.sym(Bool, Bits.genpool.bits.run_free(bits, j, n), False{}, pf.rf_past(bits, j, n, hn, hq)) : {Bool.and(Nat.is_eq(Nat.mod(Nat.add(base, Nat.mul(j, g)), Nat.max(al, 1n)), 0n), _) == False{} : Bool}
      pf.and_false(Nat.is_eq(Nat.mod(Nat.add(base, Nat.mul(j, g)), Nat.max(al, 1n)), 0n))

def Laws.first_fit_align_free(al, bits, n, base, g, s, e):
  pf.scan_some(bits, F.genpool.fit.cand(bits, 0n, n, base, g, Nat.max(al, 1n)), bits, n, 0n, base, g, Nat.max(al, 1n), s, {==}, e)

def Laws.first_fit_align_lowest(al, bits, n, base, g, s, j, e, h):
  pf.scan_low(bits, F.genpool.fit.cand(bits, 0n, n, base, g, Nat.max(al, 1n)), bits, n, 0n, base, g, Nat.max(al, 1n), s, j, Nat.is_eq(0n, j), {==}, {==}, e, N.nl.le_zero(j), h)

def Laws.first_fit_align_none(al, bits, n, base, g, j, e, hn):
  pf.align_none(Nat.is_le(j, List.length(&2, Bool, bits)), al, bits, n, base, g, j, {==}, e, hn)

# First fit with the order alignment

def Laws.first_fit_order_align_free(d, bits, n, base, g, s, e):
  N.nl.and_r(Nat.is_eq(Nat.mod(Nat.add(0n, Nat.mul(s, g)), Nat.max(Nat.mul(F.genpool.fit.pow2(n), g), 1n)), 0n), Bits.genpool.bits.run_free(bits, s, n), pf.scan_some(bits, F.genpool.fit.cand(bits, 0n, n, 0n, g, Nat.max(Nat.mul(F.genpool.fit.pow2(n), g), 1n)), bits, n, 0n, 0n, g, Nat.max(Nat.mul(F.genpool.fit.pow2(n), g), 1n), s, {==}, e))

# The fixed offset

def pf.fx_at(ok: Bool, +s0: Nat, -s: Nat, e: {F.genpool.fit.fixed.at(ok, s0) == Some{s} : Maybe<&2, Nat>}) -> {s == s0 : Nat}:
  match ok:
    case True{}:
      pf.some_inj(s, s0, Equal.sym(Maybe<&2, Nat>, Some{s0}, Some{s}, e))
    case False{}:
      Empty.absurd({s == s0 : Nat}, pf.ns(s, e))

def pf.fx_ok(ok: Bool, -s0: Nat, -s: Nat, e: {F.genpool.fit.fixed.at(ok, s0) == Some{s} : Maybe<&2, Nat>}) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, pf.ns(s, e))

def pf.fx_none(ok: Bool, -s0: Nat, e: {F.genpool.fit.fixed.at(ok, s0) == None{} : Maybe<&2, Nat>}) -> {ok == False{} : Bool}:
  match ok:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, pf.sn(s0, e))
    case False{}:
      {==}

def Laws.fixed_offset_at(off, bits, n, base, g, s, e):
  pf.fx_at(Bool.and(Nat.is_eq(Nat.mod(off, g), 0n), Bits.genpool.bits.run_free(bits, Nat.div(off, g), n)), Nat.div(off, g), s, e)

def Laws.fixed_offset_free(off, bits, n, base, g, s, e):
  pf.fx_ok(Bool.and(Nat.is_eq(Nat.mod(off, g), 0n), Bits.genpool.bits.run_free(bits, Nat.div(off, g), n)), Nat.div(off, g), s, e)

def Laws.fixed_offset_none(off, bits, n, base, g, e):
  pf.fx_none(Bool.and(Nat.is_eq(Nat.mod(off, g), 0n), Bits.genpool.bits.run_free(bits, Nat.div(off, g), n)), Nat.div(off, g), e)

def Laws.fixed_offset_no_data(bits, n, base, g):
  {==}

def Laws.fixed_offset_align_data(a, bits, n, base, g):
  {==}

# ---------------------------------------------------------------- best fit
#
# runs(bits) lists the maximal free runs (sound, complete, in order of
# start); best.go picks, among the runs long enough, the shortest, the first
# of those on ties. The scan's invariant: from the current run's start the
# bits are len free ones followed by the rest still to scan.

# Nat

def bf.nle(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case _ 0n:
      N.nl.le_zero(a)
    case 0n 1n+bp:
      Empty.absurd({Nat.is_le(1n+bp, 0n) == True{} : Bool}, N.nl.tf(h))
    case 1n+ap 1n+bp:
      bf.nle(ap, bp, h)

def bf.lt_nle(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_le(0n, a) == False{} : Bool}, N.nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, N.nl.lt0(a)), h)))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      bf.lt_nle(ap, bp, h)

def bf.antisym(a: Nat, b: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, a) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, N.nl.ft(h2))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, N.nl.ft(h1))
    case 1n+ap 1n+bp:
      %bf.antisym(ap, bp, h1, h2) : {1n+ap == 1n+_ : Nat}
      {==}

def bf.le_s_lt(p: Nat, i: Nat, h: {Nat.is_le(1n+p, i) == True{} : Bool}) -> {Nat.is_lt(p, i) == True{} : Bool}:
  match p i:
    case _ 0n:
      Empty.absurd({Nat.is_lt(p, 0n) == True{} : Bool}, N.nl.ft(h))
    case 0n 1n+ip:
      {==}
    case 1n+pp 1n+ip:
      bf.le_s_lt(pp, ip, h)

def bf.lt_s_le(a: Nat, p: Nat, h: {Nat.is_lt(a, 1n+p) == True{} : Bool}) -> {Nat.is_le(a, p) == True{} : Bool}:
  match a p:
    case 0n _:
      N.nl.le_zero(p)
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, N.nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(ap, 0n), True{}, Equal.sym(Bool, Nat.is_lt(ap, 0n), False{}, N.nl.lt0(ap)), h)))
    case 1n+ap 1n+pp:
      bf.lt_s_le(ap, pp, h)

def bf.lt_s(i: Nat, j: Nat, h: {Nat.is_lt(i, j) == True{} : Bool}) -> {Nat.is_le(1n+i, j) == True{} : Bool}:
  match i j:
    case _ 0n:
      Empty.absurd({Nat.is_le(1n+i, 0n) == True{} : Bool}, N.nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(i, 0n), True{}, Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, N.nl.lt0(i)), h)))
    case 0n 1n+jp:
      N.nl.le_zero(jp)
    case 1n+ip 1n+jp:
      bf.lt_s(ip, jp, h)

def bf.lt_next(i: Nat, s: Nat, h1: {Nat.is_lt(i, s) == True{} : Bool}, h2: {Nat.is_eq(s, 1n+i) == False{} : Bool}) -> {Nat.is_lt(1n+i, s) == True{} : Bool}:
  match i s:
    case _ 0n:
      Empty.absurd({Nat.is_lt(1n+i, 0n) == True{} : Bool}, N.nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(i, 0n), True{}, Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, N.nl.lt0(i)), h1)))
    case 0n 1n+sp:
      match sp:
        case 0n:
          Empty.absurd({Nat.is_lt(1n, 1n) == True{} : Bool}, N.nl.tf(h2))
        case 1n+sq:
          {==}
    case 1n+ip 1n+sp:
      bf.lt_next(ip, sp, h1, h2)

def bf.lt_le0(l: Nat, h1: {Nat.is_lt(0n, l) == True{} : Bool}, h2: {Nat.is_le(l, 0n) == True{} : Bool}) -> Empty:
  match l:
    case 0n:
      N.nl.ft(h1)
    case 1n+p:
      N.nl.ft(h2)

def bf.lt_irr(x: Nat) -> {Nat.is_lt(x, x) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      bf.lt_irr(p)

def bf.lt_succ(x: Nat) -> {Nat.is_lt(x, 1n+x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      bf.lt_succ(p)

def bf.le_add_l(j: Nat, +n: Nat) -> {Nat.is_le(n, Nat.add(j, n)) == True{} : Bool}:
  match j:
    case 0n:
      N.nl.le_refl(n)
    case 1n+ +p:
      N.nl.le_trans(n, Nat.add(p, n), 1n+Nat.add(p, n), bf.le_add_l(p, n), N.nl.le_succ(Nat.add(p, n)))

# st <= j and j + n <= st + ln: n <= ln
def bf.cancel(st: Nat, j: Nat, +n: Nat, +ln: Nat, h1: {Nat.is_le(st, j) == True{} : Bool}, h2: {Nat.is_le(Nat.add(j, n), Nat.add(st, ln)) == True{} : Bool}) -> {Nat.is_le(n, ln) == True{} : Bool}:
  match st j:
    case 0n +jj:
      N.nl.le_trans(n, Nat.add(jj, n), ln, bf.le_add_l(jj, n), h2)
    case 1n+sp 0n:
      Empty.absurd({Nat.is_le(n, ln) == True{} : Bool}, N.nl.ft(h1))
    case 1n+sp 1n+jp:
      bf.cancel(sp, jp, n, ln, h1, h2)

def bf.or_t(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Bool lists

def bf.lhd(v: List<&2, Bool>) -> Bool:
  match v:
    case Nil{}:
      False{}
    case Con{b, t}:
      b

def bf.ltl(v: List<&2, Bool>) -> List<&2, Bool>:
  match v:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      t

def bf.is_nil(v: List<&2, Bool>) -> Type:
  match v:
    case Nil{}:
      Unit
    case Con{b, t}:
      Empty

def bf.nc(-b: Bool, -t: List<&2, Bool>, e: {Nil{} == Con{b, t} : List<&2, Bool>}) -> Empty:
  %e : bf.is_nil(_)
  Unit{}

def bf.drop0(v: List<&2, Bool>) -> {List.drop(&2, Bool, v, 0n) == v : List<&2, Bool>}:
  match v:
    case Nil{}:
      {==}
    case Con{b, t}:
      {==}

def bf.app_rep_cons(ln: Nat, +t: List<&2, Bool>) -> {List.append(&2, Bool, List.replicate(Bool, ln, False{}), Con{False{}, t}) == Con{False{}, List.append(&2, Bool, List.replicate(Bool, ln, False{}), t)} : List<&2, Bool>}:
  match ln:
    case 0n:
      {==}
    case 1n+k:
      Equal.cong(List<&2, Bool>, List<&2, Bool>, z => Con{False{}, z}, List.append(&2, Bool, List.replicate(Bool, k, False{}), Con{False{}, t}), Con{False{}, List.append(&2, Bool, List.replicate(Bool, k, False{}), t)}, bf.app_rep_cons(k, t))

def bf.fp_rep(ln: Nat, +rest: List<&2, Bool>) -> {Bits.genpool.bits.free_prefix(List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest), ln) == True{} : Bool}:
  match ln:
    case 0n:
      match rest:
        case Nil{}:
          {==}
        case Con{b, t}:
          {==}
    case 1n+k:
      bf.fp_rep(k, rest)

def bf.drop_rep(ln: Nat, +rest: List<&2, Bool>) -> {List.drop(&2, Bool, List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest), ln) == rest : List<&2, Bool>}:
  match ln:
    case 0n:
      bf.drop0(rest)
    case 1n+k:
      bf.drop_rep(k, rest)

def bf.drop_drop(v: List<&2, Bool>, a: Nat, +b: Nat) -> {List.drop(&2, Bool, List.drop(&2, Bool, v, a), b) == List.drop(&2, Bool, v, Nat.add(a, b)) : List<&2, Bool>}:
  match v a:
    case Nil{} _:
      {==}
    case Con{x, u} 0n:
      {==}
    case Con{x, u} 1n+ap:
      bf.drop_drop(u, ap, b)

def bf.drop_succ(v: List<&2, Bool>, i: Nat, -b: Bool, -t: List<&2, Bool>, h: {List.drop(&2, Bool, v, i) == Con{b, t} : List<&2, Bool>}) -> {List.drop(&2, Bool, v, 1n+i) == t : List<&2, Bool>}:
  match v i:
    case Nil{} _:
      Empty.absurd({List.drop(&2, Bool, Nil{}, 1n+i) == t : List<&2, Bool>}, bf.nc(b, t, h))
    case Con{x, +u} 0n:
      Equal.trans(List<&2, Bool>, List.drop(&2, Bool, u, 0n), u, t, bf.drop0(u), Equal.cong(List<&2, Bool>, List<&2, Bool>, z => bf.ltl(z), Con{x, u}, Con{b, t}, h))
    case Con{x, u} 1n+k:
      bf.drop_succ(u, k, b, t, h)

def bf.drop_get(v: List<&2, Bool>, i: Nat, -b: Bool, -t: List<&2, Bool>, h: {List.drop(&2, Bool, v, i) == Con{b, t} : List<&2, Bool>}) -> {Bits.genpool.bits.get(v, i) == b : Bool}:
  match v i:
    case Nil{} _:
      Empty.absurd({Bits.genpool.bits.get(Nil{}, i) == b : Bool}, bf.nc(b, t, h))
    case Con{x, u} 0n:
      Equal.cong(List<&2, Bool>, Bool, z => bf.lhd(z), Con{x, u}, Con{b, t}, h)
    case Con{x, u} 1n+k:
      bf.drop_get(u, k, b, t, h)

def bf.drop_nil(v: List<&2, Bool>, i: Nat, h: {List.drop(&2, Bool, v, i) == Nil{} : List<&2, Bool>}) -> {Nat.is_le(List.length(&2, Bool, v), i) == True{} : Bool}:
  match v i:
    case Nil{} _:
      N.nl.le_zero(i)
    case Con{x, u} 0n:
      Empty.absurd({Nat.is_le(1n+List.length(&2, Bool, u), 0n) == True{} : Bool}, bf.nc(x, u, Equal.sym(List<&2, Bool>, Con{x, u}, Nil{}, h)))
    case Con{x, u} 1n+k:
      bf.drop_nil(u, k, h)

def bf.get_rep(ln: Nat, +rest: List<&2, Bool>, k: Nat, h: {Nat.is_lt(k, ln) == True{} : Bool}) -> {Bits.genpool.bits.get(List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest), k) == False{} : Bool}:
  match ln k:
    case 0n _:
      Empty.absurd({Bits.genpool.bits.get(rest, k) == False{} : Bool}, N.nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(k, 0n), True{}, Equal.sym(Bool, Nat.is_lt(k, 0n), False{}, N.nl.lt0(k)), h)))
    case 1n+lp 0n:
      {==}
    case 1n+lp 1n+kp:
      bf.get_rep(lp, rest, kp, h)

# the bits from st on are ln free ones and rest: rest is what is left after i
def bf.da(+bits: List<&2, Bool>, +st: Nat, +ln: Nat, +rest: List<&2, Bool>, +i: Nat, +q: {List.drop(&2, Bool, bits, st) == List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest) : List<&2, Bool>}, +hi: {i == Nat.add(st, ln) : Nat}) -> {List.drop(&2, Bool, bits, i) == rest : List<&2, Bool>}:
  Equal.trans(List<&2, Bool>, List.drop(&2, Bool, bits, i), List.drop(&2, Bool, bits, Nat.add(st, ln)), rest, Equal.cong(Nat, List<&2, Bool>, z => List.drop(&2, Bool, bits, z), i, Nat.add(st, ln), hi), Equal.trans(List<&2, Bool>, List.drop(&2, Bool, bits, Nat.add(st, ln)), List.drop(&2, Bool, List.drop(&2, Bool, bits, st), ln), rest, Equal.sym(List<&2, Bool>, List.drop(&2, Bool, List.drop(&2, Bool, bits, st), ln), List.drop(&2, Bool, bits, Nat.add(st, ln)), bf.drop_drop(bits, st, ln)), Equal.trans(List<&2, Bool>, List.drop(&2, Bool, List.drop(&2, Bool, bits, st), ln), List.drop(&2, Bool, List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest), ln), rest, Equal.cong(List<&2, Bool>, List<&2, Bool>, z => List.drop(&2, Bool, z, ln), List.drop(&2, Bool, bits, st), List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest), q), bf.drop_rep(ln, rest))))

# and so the bits from st to st + ln - 1 are free
def bf.freep(v: List<&2, Bool>, st: Nat, p: Nat, +ln: Nat, +rest: List<&2, Bool>, q: {List.drop(&2, Bool, v, st) == List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest) : List<&2, Bool>}, h1: {Nat.is_le(st, p) == True{} : Bool}, h2: {Nat.is_lt(p, Nat.add(st, ln)) == True{} : Bool}) -> {Bits.genpool.bits.get(v, p) == False{} : Bool}:
  match v st p:
    case Nil{} _ _:
      {==}
    case Con{+x, +u} 0n +pp:
      Equal.trans(Bool, Bits.genpool.bits.get(Con{x, u}, pp), Bits.genpool.bits.get(List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest), pp), False{}, Equal.cong(List<&2, Bool>, Bool, z => Bits.genpool.bits.get(z, pp), Con{x, u}, List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest), q), bf.get_rep(ln, rest, pp, h2))
    case Con{x, u} 1n+sp 0n:
      Empty.absurd({Bits.genpool.bits.get(Con{x, u}, 0n) == False{} : Bool}, N.nl.ft(h1))
    case Con{x, u} 1n+sp 1n+pp:
      bf.freep(u, sp, pp, ln, rest, q, h1, h2)

def bf.fp_prefix(v: List<&2, Bool>, l: Nat, n: Nat, +h: {Bits.genpool.bits.free_prefix(v, l) == True{} : Bool}, hn: {Nat.is_le(n, l) == True{} : Bool}) -> {Bits.genpool.bits.free_prefix(v, n) == True{} : Bool}:
  match v l n:
    case Nil{} _ 0n:
      {==}
    case Nil{} 0n 1n+np:
      Empty.absurd({Bits.genpool.bits.free_prefix(Nil{}, 1n+np) == True{} : Bool}, N.nl.ft(hn))
    case Nil{} 1n+lp 1n+np:
      Empty.absurd({Bits.genpool.bits.free_prefix(Nil{}, 1n+np) == True{} : Bool}, N.nl.ft(h))
    case Con{b, t} _ 0n:
      {==}
    case Con{b, t} 0n 1n+np:
      Empty.absurd({Bits.genpool.bits.free_prefix(Con{b, t}, 1n+np) == True{} : Bool}, N.nl.ft(hn))
    case Con{+b, +t} 1n+lp 1n+np:
      N.nl.and_i(Bool.not(b), Bits.genpool.bits.free_prefix(t, np), N.nl.and_l(Bool.not(b), Bits.genpool.bits.free_prefix(t, lp), h), bf.fp_prefix(t, lp, np, N.nl.and_r(Bool.not(b), Bits.genpool.bits.free_prefix(t, lp), h), hn))

# The ends of a run

def bf.right_le(+bits: List<&2, Bool>, +e: Nat, h: {Nat.is_le(List.length(&2, Bool, bits), e) == True{} : Bool}) -> {Laws.bf.right(bits, e) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(List.length(&2, Bool, bits), e), True{}, h) : {Bool.or(_, Bits.genpool.bits.get(bits, e)) == True{} : Bool}
  {==}

def bf.right_get(+bits: List<&2, Bool>, +e: Nat, h: {Bits.genpool.bits.get(bits, e) == True{} : Bool}) -> {Laws.bf.right(bits, e) == True{} : Bool}:
  %Equal.sym(Bool, Bits.genpool.bits.get(bits, e), True{}, h) : {Bool.or(Nat.is_le(List.length(&2, Bool, bits), e), _) == True{} : Bool}
  bf.or_t(Nat.is_le(List.length(&2, Bool, bits), e))

def bf.right_f(+bits: List<&2, Bool>, +e: Nat, h1: {Nat.is_le(List.length(&2, Bool, bits), e) == False{} : Bool}, h2: {Bits.genpool.bits.get(bits, e) == False{} : Bool}) -> {Laws.bf.right(bits, e) == False{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(List.length(&2, Bool, bits), e), False{}, h1) : {Bool.or(_, Bits.genpool.bits.get(bits, e)) == False{} : Bool}
  h2

def bf.nle_lt(a: Nat, b: Nat, h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, N.nl.tf(h))
    case 0n 1n+bp:
      Empty.absurd({Nat.is_lt(1n+bp, 0n) == True{} : Bool}, N.nl.tf(h))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      bf.nle_lt(ap, bp, h)

def bf.u.go(q: Bool, +bits: List<&2, Bool>, +s: Nat, +a: Nat, +b: Nat, +hq: {Nat.is_le(a, b) == q : Bool}, +ha: {Bits.genpool.bits.run_free(bits, s, a) == True{} : Bool}, +hpos: {Nat.is_lt(0n, a) == True{} : Bool}, hr: {Laws.bf.right(bits, Nat.add(s, b)) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match q:
    case True{}:
      hq
    case False{}:
      Empty.absurd({Nat.is_le(a, b) == True{} : Bool}, N.nl.ft(Equal.trans(Bool, False{}, Laws.bf.right(bits, Nat.add(s, b)), True{}, Equal.sym(Bool, Laws.bf.right(bits, Nat.add(s, b)), False{}, bf.right_f(bits, Nat.add(s, b), bf.lt_nle(Nat.add(s, b), List.length(&2, Bool, bits), N.nl.lt_le_trans(Nat.add(s, b), Nat.add(s, a), List.length(&2, Bool, bits), N.nl.lt_add_l(s, b, a, bf.nle_lt(a, b, hq)), PB.pb.rf_len(bits, s, a, hpos, ha))), PB.pb.rf_get(bits, s, a, Nat.add(s, b), ha, N.nl.le_add(s, b), N.nl.lt_add_l(s, b, a, bf.nle_lt(a, b, hq))))), hr)))

# a run of a free granules from s ends no sooner than any end of it
def bf.u(+bits: List<&2, Bool>, +s: Nat, +a: Nat, +b: Nat, +ha: {Bits.genpool.bits.run_free(bits, s, a) == True{} : Bool}, +hpos: {Nat.is_lt(0n, a) == True{} : Bool}, hr: {Laws.bf.right(bits, Nat.add(s, b)) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  bf.u.go(Nat.is_le(a, b), bits, s, a, b, {==}, ha, hpos, hr)

# Lists of runs

def bf.allmax(+bits: List<&2, Bool>, rs: List<&2, F.GpRun>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{+r, t}:
      Bool.and(Laws.bf.maximal(bits, F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)), bf.allmax(bits, t))

def bf.memr(rs: List<&2, F.GpRun>, +s: Nat, +l: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{+r, t}:
      Bool.or(Bool.and(Nat.is_eq(F.genpool.fit.run_start(r), s), Nat.is_eq(F.genpool.fit.run_len(r), l)), bf.memr(t, s, l))

def bf.srt(rs: List<&2, F.GpRun>, +lb: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{+r, t}:
      Bool.and(Nat.is_le(lb, F.genpool.fit.run_start(r)), bf.srt(t, 1n+F.genpool.fit.run_start(r)))

def bf.anyfit(rs: List<&2, F.GpRun>, +n: Nat) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case Con{+r, t}:
      Bool.or(Nat.is_le(n, F.genpool.fit.run_len(r)), bf.anyfit(t, n))

def bf.hdr(rs: List<&2, F.GpRun>) -> F.GpRun:
  match rs:
    case Nil{}:
      F.GpRun{0n, 0n}
    case Con{r, t}:
      r

def bf.close_mem(+st: Nat, +ln: Nat, +x: List<&2, F.GpRun>, +s: Nat, +l: Nat, h: {bf.memr(x, s, l) == True{} : Bool}) -> {bf.memr(F.genpool.fit.runs.close(st, ln, x), s, l) == True{} : Bool}:
  match ln:
    case 0n:
      h
    case 1n+k:
      %Equal.sym(Bool, bf.memr(x, s, l), True{}, h) : {Bool.or(Bool.and(Nat.is_eq(st, s), Nat.is_eq(1n+k, l)), _) == True{} : Bool}
      bf.or_t(Bool.and(Nat.is_eq(st, s), Nat.is_eq(1n+k, l)))

def bf.close_any(+st: Nat, +ln: Nat, +x: List<&2, F.GpRun>, +n: Nat, h: {bf.anyfit(x, n) == True{} : Bool}) -> {bf.anyfit(F.genpool.fit.runs.close(st, ln, x), n) == True{} : Bool}:
  match ln:
    case 0n:
      h
    case 1n+k:
      %Equal.sym(Bool, bf.anyfit(x, n), True{}, h) : {Bool.or(Nat.is_le(n, 1n+k), _) == True{} : Bool}
      bf.or_t(Nat.is_le(n, 1n+k))

def bf.mem_head(+st: Nat, +ln: Nat, +x: List<&2, F.GpRun>, +l: Nat, h: {ln == l : Nat}) -> {bf.memr(Con{F.GpRun{st, ln}, x}, st, l) == True{} : Bool}:
  %h : {bf.memr(Con{F.GpRun{st, ln}, x}, st, _) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(st, st), True{}, N.nl.eq_refl(st)) : {Bool.or(Bool.and(_, Nat.is_eq(ln, ln)), bf.memr(x, st, ln)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(ln, ln), True{}, N.nl.eq_refl(ln)) : {Bool.or(_, bf.memr(x, st, ln)) == True{} : Bool}
  {==}

def bf.any_head(+st: Nat, +ln: Nat, +x: List<&2, F.GpRun>, +n: Nat, h: {Nat.is_le(n, ln) == True{} : Bool}) -> {bf.anyfit(Con{F.GpRun{st, ln}, x}, n) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(n, ln), True{}, h) : {Bool.or(_, bf.anyfit(x, n)) == True{} : Bool}
  {==}

def bf.afit_len(+st: Nat, +ln: Nat, +x: List<&2, F.GpRun>, +n: Nat, hn: {Nat.is_lt(0n, n) == True{} : Bool}, h: {Nat.is_le(n, ln) == True{} : Bool}) -> {bf.anyfit(F.genpool.fit.runs.close(st, ln, x), n) == True{} : Bool}:
  match ln:
    case 0n:
      Empty.absurd({bf.anyfit(x, n) == True{} : Bool}, bf.lt_le0(n, hn, h))
    case 1n+ +k:
      bf.any_head(st, 1n+k, x, n, h)

def bf.eq_comm(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      bf.eq_comm(ap, bp)

def bf.mem_all.go(+bits: List<&2, Bool>, rs: List<&2, F.GpRun>, +s: Nat, +l: Nat, hb: Bool, +hh: {Bool.and(Nat.is_eq(F.genpool.fit.run_start(bf.hdr(rs)), s), Nat.is_eq(F.genpool.fit.run_len(bf.hdr(rs)), l)) == hb : Bool}, +h: {bf.allmax(bits, rs) == True{} : Bool}, +hm: {bf.memr(rs, s, l) == True{} : Bool}) -> {Laws.bf.maximal(bits, s, l) == True{} : Bool}:
  match rs:
    case Nil{}:
      Empty.absurd({Laws.bf.maximal(bits, s, l) == True{} : Bool}, N.nl.ft(hm))
    case Con{+r, +t}:
      match hb:
        case True{}:
          %N.nl.eq(F.genpool.fit.run_start(r), s, N.nl.and_l(Nat.is_eq(F.genpool.fit.run_start(r), s), Nat.is_eq(F.genpool.fit.run_len(r), l), hh)) : {Laws.bf.maximal(bits, _, l) == True{} : Bool}
          %N.nl.eq(F.genpool.fit.run_len(r), l, N.nl.and_r(Nat.is_eq(F.genpool.fit.run_start(r), s), Nat.is_eq(F.genpool.fit.run_len(r), l), hh)) : {Laws.bf.maximal(bits, F.genpool.fit.run_start(r), _) == True{} : Bool}
          N.nl.and_l(Laws.bf.maximal(bits, F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)), bf.allmax(bits, t), h)
        case False{}:
          bf.mem_all.go(bits, t, s, l, Bool.and(Nat.is_eq(F.genpool.fit.run_start(bf.hdr(t)), s), Nat.is_eq(F.genpool.fit.run_len(bf.hdr(t)), l)), {==}, N.nl.and_r(Laws.bf.maximal(bits, F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)), bf.allmax(bits, t), h), Equal.trans(Bool, bf.memr(t, s, l), Bool.or(Bool.and(Nat.is_eq(F.genpool.fit.run_start(r), s), Nat.is_eq(F.genpool.fit.run_len(r), l)), bf.memr(t, s, l)), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, bf.memr(t, s, l)), False{}, Bool.and(Nat.is_eq(F.genpool.fit.run_start(r), s), Nat.is_eq(F.genpool.fit.run_len(r), l)), Equal.sym(Bool, Bool.and(Nat.is_eq(F.genpool.fit.run_start(r), s), Nat.is_eq(F.genpool.fit.run_len(r), l)), False{}, hh)), hm))

# a run of a list of maximal runs is maximal
def bf.mem_all(+bits: List<&2, Bool>, +rs: List<&2, F.GpRun>, +s: Nat, +l: Nat, +h: {bf.allmax(bits, rs) == True{} : Bool}, +hm: {bf.memr(rs, s, l) == True{} : Bool}) -> {Laws.bf.maximal(bits, s, l) == True{} : Bool}:
  bf.mem_all.go(bits, rs, s, l, Bool.and(Nat.is_eq(F.genpool.fit.run_start(bf.hdr(rs)), s), Nat.is_eq(F.genpool.fit.run_len(bf.hdr(rs)), l)), {==}, h, hm)

# The scan

def bf.q_false(+bits: List<&2, Bool>, +st: Nat, +ln: Nat, +t: List<&2, Bool>, +q: {List.drop(&2, Bool, bits, st) == List.append(&2, Bool, List.replicate(Bool, ln, False{}), Con{False{}, t}) : List<&2, Bool>}) -> {List.drop(&2, Bool, bits, st) == List.append(&2, Bool, List.replicate(Bool, 1n+ln, False{}), t) : List<&2, Bool>}:
  Equal.trans(List<&2, Bool>, List.drop(&2, Bool, bits, st), List.append(&2, Bool, List.replicate(Bool, ln, False{}), Con{False{}, t}), List.append(&2, Bool, List.replicate(Bool, 1n+ln, False{}), t), q, bf.app_rep_cons(ln, t))

def bf.hi_succ(+i: Nat, +st: Nat, +ln: Nat, +hi: {i == Nat.add(st, ln) : Nat}) -> {1n+i == Nat.add(st, 1n+ln) : Nat}:
  Equal.trans(Nat, 1n+i, 1n+Nat.add(st, ln), Nat.add(st, 1n+ln), Equal.cong(Nat, Nat, z => 1n+z, i, Nat.add(st, ln), hi), Equal.sym(Nat, Nat.add(st, 1n+ln), 1n+Nat.add(st, ln), N.nl.add_succ(st, ln)))

def bf.hi_zero(+i: Nat) -> {1n+i == Nat.add(1n+i, 0n) : Nat}:
  Equal.sym(Nat, Nat.add(1n+i, 0n), 1n+i, N.nl.add_zero(1n+i))

def bf.rf_q(+bits: List<&2, Bool>, +st: Nat, +ln: Nat, +rest: List<&2, Bool>, +q: {List.drop(&2, Bool, bits, st) == List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest) : List<&2, Bool>}) -> {Bits.genpool.bits.run_free(bits, st, ln) == True{} : Bool}:
  Equal.trans(Bool, Bits.genpool.bits.free_prefix(List.drop(&2, Bool, bits, st), ln), Bits.genpool.bits.free_prefix(List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest), ln), True{}, Equal.cong(List<&2, Bool>, Bool, z => Bits.genpool.bits.free_prefix(z, ln), List.drop(&2, Bool, bits, st), List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest), q), bf.fp_rep(ln, rest))

# the run so far ends at the end of the bits
def bf.end_nil(+bits: List<&2, Bool>, +st: Nat, +ln: Nat, +i: Nat, +q: {List.drop(&2, Bool, bits, st) == List.append(&2, Bool, List.replicate(Bool, ln, False{}), Nil{}) : List<&2, Bool>}, +hi: {i == Nat.add(st, ln) : Nat}) -> {Laws.bf.right(bits, Nat.add(st, ln)) == True{} : Bool}:
  bf.right_le(bits, Nat.add(st, ln), Equal.trans(Bool, Nat.is_le(List.length(&2, Bool, bits), Nat.add(st, ln)), Nat.is_le(List.length(&2, Bool, bits), i), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(List.length(&2, Bool, bits), z), Nat.add(st, ln), i, Equal.sym(Nat, i, Nat.add(st, ln), hi)), bf.drop_nil(bits, i, bf.da(bits, st, ln, Nil{}, i, q, hi))))

# the run so far ends at an allocated granule
def bf.end_used(+bits: List<&2, Bool>, +st: Nat, +ln: Nat, +t: List<&2, Bool>, +i: Nat, +q: {List.drop(&2, Bool, bits, st) == List.append(&2, Bool, List.replicate(Bool, ln, False{}), Con{True{}, t}) : List<&2, Bool>}, +hi: {i == Nat.add(st, ln) : Nat}) -> {Laws.bf.right(bits, Nat.add(st, ln)) == True{} : Bool}:
  bf.right_get(bits, Nat.add(st, ln), Equal.trans(Bool, Bits.genpool.bits.get(bits, Nat.add(st, ln)), Bits.genpool.bits.get(bits, i), True{}, Equal.cong(Nat, Bool, z => Bits.genpool.bits.get(bits, z), Nat.add(st, ln), i, Equal.sym(Nat, i, Nat.add(st, ln), hi)), bf.drop_get(bits, i, True{}, t, bf.da(bits, st, ln, Con{True{}, t}, i, q, hi))))

def bf.max_of(+bits: List<&2, Bool>, +st: Nat, +k: Nat, +rest: List<&2, Bool>, +q: {List.drop(&2, Bool, bits, st) == List.append(&2, Bool, List.replicate(Bool, 1n+k, False{}), rest) : List<&2, Bool>}, +hl: {Laws.bf.left(bits, st) == True{} : Bool}, +hr: {Laws.bf.right(bits, Nat.add(st, 1n+k)) == True{} : Bool}) -> {Laws.bf.maximal(bits, st, 1n+k) == True{} : Bool}:
  N.nl.and_i(Nat.is_lt(0n, 1n+k), Bool.and(Bits.genpool.bits.run_free(bits, st, 1n+k), Bool.and(Laws.bf.left(bits, st), Laws.bf.right(bits, Nat.add(st, 1n+k)))), {==}, N.nl.and_i(Bits.genpool.bits.run_free(bits, st, 1n+k), Bool.and(Laws.bf.left(bits, st), Laws.bf.right(bits, Nat.add(st, 1n+k))), bf.rf_q(bits, st, 1n+k, rest, q), N.nl.and_i(Laws.bf.left(bits, st), Laws.bf.right(bits, Nat.add(st, 1n+k)), hl, hr)))

# every run the scan lists is maximal
def bf.sound(+bits: List<&2, Bool>, rest: List<&2, Bool>, +i: Nat, +st: Nat, +ln: Nat, +q: {List.drop(&2, Bool, bits, st) == List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest) : List<&2, Bool>}, +hi: {i == Nat.add(st, ln) : Nat}, +hl: {Laws.bf.left(bits, st) == True{} : Bool}) -> {bf.allmax(bits, F.genpool.fit.runs.go(rest, i, st, ln)) == True{} : Bool}:
  match rest:
    case Nil{}:
      match ln:
        case 0n:
          {==}
        case 1n+ +k:
          N.nl.and_i(Laws.bf.maximal(bits, st, 1n+k), True{}, bf.max_of(bits, st, k, Nil{}, q, hl, bf.end_nil(bits, st, 1n+k, i, q, hi)), {==})
    case Con{b, +t}:
      match b:
        case False{}:
          bf.sound(bits, t, 1n+i, st, 1n+ln, bf.q_false(bits, st, ln, t, q), bf.hi_succ(i, st, ln, hi), hl)
        case True{}:
          match ln:
            case 0n:
              bf.sound(bits, t, 1n+i, 1n+i, 0n, bf.drop_succ(bits, i, True{}, t, bf.da(bits, st, 0n, Con{True{}, t}, i, q, hi)), bf.hi_zero(i), bf.drop_get(bits, i, True{}, t, bf.da(bits, st, 0n, Con{True{}, t}, i, q, hi)))
            case 1n+ +k:
              N.nl.and_i(Laws.bf.maximal(bits, st, 1n+k), bf.allmax(bits, F.genpool.fit.runs.go(t, 1n+i, 1n+i, 0n)), bf.max_of(bits, st, k, Con{True{}, t}, q, hl, bf.end_used(bits, st, 1n+k, t, i, q, hi)), bf.sound(bits, t, 1n+i, 1n+i, 0n, bf.drop_succ(bits, i, True{}, t, bf.da(bits, st, 1n+k, Con{True{}, t}, i, q, hi)), bf.hi_zero(i), bf.drop_get(bits, i, True{}, t, bf.da(bits, st, 1n+k, Con{True{}, t}, i, q, hi))))

def bf.st_i(+i: Nat, +st: Nat, +ln: Nat, +hi: {i == Nat.add(st, ln) : Nat}) -> {Nat.is_le(st, i) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(st, i), Nat.is_le(st, Nat.add(st, ln)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(st, z), i, Nat.add(st, ln), hi), N.nl.le_add(st, ln))

# the scan lists its runs in order of start, from st on
def bf.sorted(rest: List<&2, Bool>, +i: Nat, +st: Nat, +ln: Nat, +lb: Nat, +hi: {i == Nat.add(st, ln) : Nat}, +hlb: {Nat.is_le(lb, st) == True{} : Bool}) -> {bf.srt(F.genpool.fit.runs.go(rest, i, st, ln), lb) == True{} : Bool}:
  match rest:
    case Nil{}:
      match ln:
        case 0n:
          {==}
        case 1n+k:
          N.nl.and_i(Nat.is_le(lb, st), True{}, hlb, {==})
    case Con{b, +t}:
      match b:
        case False{}:
          bf.sorted(t, 1n+i, st, 1n+ln, lb, bf.hi_succ(i, st, ln, hi), hlb)
        case True{}:
          match ln:
            case 0n:
              bf.sorted(t, 1n+i, 1n+i, 0n, lb, bf.hi_zero(i), N.nl.le_trans(lb, st, 1n+i, hlb, N.nl.le_trans(st, i, 1n+i, bf.st_i(i, st, 0n, hi), N.nl.le_succ(i))))
            case 1n+ +k:
              N.nl.and_i(Nat.is_le(lb, st), bf.srt(F.genpool.fit.runs.go(t, 1n+i, 1n+i, 0n), 1n+st), hlb, bf.sorted(t, 1n+i, 1n+i, 0n, 1n+st, bf.hi_zero(i), bf.st_i(i, st, 1n+k, hi)))

def bf.mx_pos(+bits: List<&2, Bool>, +s: Nat, +l: Nat, h: {Laws.bf.maximal(bits, s, l) == True{} : Bool}) -> {Nat.is_lt(0n, l) == True{} : Bool}:
  N.nl.and_l(Nat.is_lt(0n, l), Bool.and(Bits.genpool.bits.run_free(bits, s, l), Bool.and(Laws.bf.left(bits, s), Laws.bf.right(bits, Nat.add(s, l)))), h)

def bf.mx_rf(+bits: List<&2, Bool>, +s: Nat, +l: Nat, h: {Laws.bf.maximal(bits, s, l) == True{} : Bool}) -> {Bits.genpool.bits.run_free(bits, s, l) == True{} : Bool}:
  N.nl.and_l(Bits.genpool.bits.run_free(bits, s, l), Bool.and(Laws.bf.left(bits, s), Laws.bf.right(bits, Nat.add(s, l))), N.nl.and_r(Nat.is_lt(0n, l), Bool.and(Bits.genpool.bits.run_free(bits, s, l), Bool.and(Laws.bf.left(bits, s), Laws.bf.right(bits, Nat.add(s, l)))), h))

def bf.mx_left(+bits: List<&2, Bool>, +s: Nat, +l: Nat, h: {Laws.bf.maximal(bits, s, l) == True{} : Bool}) -> {Laws.bf.left(bits, s) == True{} : Bool}:
  N.nl.and_l(Laws.bf.left(bits, s), Laws.bf.right(bits, Nat.add(s, l)), N.nl.and_r(Bits.genpool.bits.run_free(bits, s, l), Bool.and(Laws.bf.left(bits, s), Laws.bf.right(bits, Nat.add(s, l))), N.nl.and_r(Nat.is_lt(0n, l), Bool.and(Bits.genpool.bits.run_free(bits, s, l), Bool.and(Laws.bf.left(bits, s), Laws.bf.right(bits, Nat.add(s, l)))), h)))

def bf.mx_right(+bits: List<&2, Bool>, +s: Nat, +l: Nat, h: {Laws.bf.maximal(bits, s, l) == True{} : Bool}) -> {Laws.bf.right(bits, Nat.add(s, l)) == True{} : Bool}:
  N.nl.and_r(Laws.bf.left(bits, s), Laws.bf.right(bits, Nat.add(s, l)), N.nl.and_r(Bits.genpool.bits.run_free(bits, s, l), Bool.and(Laws.bf.left(bits, s), Laws.bf.right(bits, Nat.add(s, l))), N.nl.and_r(Nat.is_lt(0n, l), Bool.and(Bits.genpool.bits.run_free(bits, s, l), Bool.and(Laws.bf.left(bits, s), Laws.bf.right(bits, Nat.add(s, l)))), h)))

# the maximal run at st has the length the scan finds for it
def bf.same_len(+bits: List<&2, Bool>, +st: Nat, +k: Nat, +l: Nat, +rest: List<&2, Bool>, +q: {List.drop(&2, Bool, bits, st) == List.append(&2, Bool, List.replicate(Bool, 1n+k, False{}), rest) : List<&2, Bool>}, +hr: {Laws.bf.right(bits, Nat.add(st, 1n+k)) == True{} : Bool}, +hm: {Laws.bf.maximal(bits, st, l) == True{} : Bool}) -> {1n+k == l : Nat}:
  bf.antisym(1n+k, l, bf.u(bits, st, 1n+k, l, bf.rf_q(bits, st, 1n+k, rest, q), {==}, bf.mx_right(bits, st, l, hm)), bf.u(bits, st, l, 1n+k, bf.mx_rf(bits, st, l, hm), bf.mx_pos(bits, st, l, hm), hr))

# a maximal run at the start of the run being scanned is listed
def bf.cpl_a(+bits: List<&2, Bool>, rest: List<&2, Bool>, +i: Nat, +st: Nat, +ln: Nat, +l: Nat, +q: {List.drop(&2, Bool, bits, st) == List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest) : List<&2, Bool>}, +hi: {i == Nat.add(st, ln) : Nat}, +hm: {Laws.bf.maximal(bits, st, l) == True{} : Bool}) -> {bf.memr(F.genpool.fit.runs.go(rest, i, st, ln), st, l) == True{} : Bool}:
  match rest:
    case Nil{}:
      match ln:
        case 0n:
          Empty.absurd({bf.memr(Nil{}, st, l) == True{} : Bool}, bf.lt_le0(l, bf.mx_pos(bits, st, l, hm), bf.u(bits, st, l, 0n, bf.mx_rf(bits, st, l, hm), bf.mx_pos(bits, st, l, hm), bf.end_nil(bits, st, 0n, i, q, hi))))
        case 1n+ +k:
          bf.mem_head(st, 1n+k, Nil{}, l, bf.same_len(bits, st, k, l, Nil{}, q, bf.end_nil(bits, st, 1n+k, i, q, hi), hm))
    case Con{b, +t}:
      match b:
        case False{}:
          bf.cpl_a(bits, t, 1n+i, st, 1n+ln, l, bf.q_false(bits, st, ln, t, q), bf.hi_succ(i, st, ln, hi), hm)
        case True{}:
          match ln:
            case 0n:
              Empty.absurd({bf.memr(F.genpool.fit.runs.go(t, 1n+i, 1n+i, 0n), st, l) == True{} : Bool}, bf.lt_le0(l, bf.mx_pos(bits, st, l, hm), bf.u(bits, st, l, 0n, bf.mx_rf(bits, st, l, hm), bf.mx_pos(bits, st, l, hm), bf.end_used(bits, st, 0n, t, i, q, hi))))
            case 1n+ +k:
              bf.mem_head(st, 1n+k, F.genpool.fit.runs.go(t, 1n+i, 1n+i, 0n), l, bf.same_len(bits, st, k, l, Con{True{}, t}, q, bf.end_used(bits, st, 1n+k, t, i, q, hi), hm))

# no maximal run starts inside the run being scanned
def bf.inside(+bits: List<&2, Bool>, +st: Nat, +ln: Nat, +rest: List<&2, Bool>, +i: Nat, s: Nat, +q: {List.drop(&2, Bool, bits, st) == List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest) : List<&2, Bool>}, +hi: {i == Nat.add(st, ln) : Nat}, hs: {Nat.is_lt(st, s) == True{} : Bool}, hsi: {Nat.is_le(s, i) == True{} : Bool}, hleft: {Laws.bf.left(bits, s) == True{} : Bool}) -> Empty:
  match s:
    case 0n:
      N.nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(st, 0n), True{}, Equal.sym(Bool, Nat.is_lt(st, 0n), False{}, N.nl.lt0(st)), hs))
    case 1n+ +p:
      N.nl.ft(Equal.trans(Bool, False{}, Bits.genpool.bits.get(bits, p), True{}, Equal.sym(Bool, Bits.genpool.bits.get(bits, p), False{}, bf.freep(bits, st, p, ln, rest, q, bf.lt_s_le(st, p, hs), Equal.trans(Bool, Nat.is_lt(p, Nat.add(st, ln)), Nat.is_lt(p, i), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(p, z), Nat.add(st, ln), i, Equal.sym(Nat, i, Nat.add(st, ln), hi)), bf.le_s_lt(p, i, hsi)))), hleft))

# a maximal run after the start of the run being scanned is listed
def bf.cpl_b(+bits: List<&2, Bool>, rest: List<&2, Bool>, +i: Nat, +st: Nat, +ln: Nat, +s: Nat, +l: Nat, +q: {List.drop(&2, Bool, bits, st) == List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest) : List<&2, Bool>}, +hi: {i == Nat.add(st, ln) : Nat}, +hm: {Laws.bf.maximal(bits, s, l) == True{} : Bool}, +hs: {Nat.is_lt(st, s) == True{} : Bool}, q1: Bool, +hq1: {Nat.is_lt(i, s) == q1 : Bool}, q2: Bool, +hq2: {Nat.is_eq(s, 1n+i) == q2 : Bool}) -> {bf.memr(F.genpool.fit.runs.go(rest, i, st, ln), s, l) == True{} : Bool}:
  match rest:
    case Nil{}:
      Empty.absurd({bf.memr(F.genpool.fit.runs.go(Nil{}, i, st, ln), s, l) == True{} : Bool}, bf.inside(bits, st, ln, Nil{}, i, s, q, hi, hs, N.nl.lt_le(s, i, N.nl.lt_le_trans(s, Nat.add(s, l), i, N.nl.lt_add(s, l, bf.mx_pos(bits, s, l, hm)), N.nl.le_trans(Nat.add(s, l), List.length(&2, Bool, bits), i, PB.pb.rf_len(bits, s, l, bf.mx_pos(bits, s, l, hm), bf.mx_rf(bits, s, l, hm)), bf.drop_nil(bits, i, bf.da(bits, st, ln, Nil{}, i, q, hi))))), bf.mx_left(bits, s, l, hm)))
    case Con{b, +t}:
      match b:
        case False{}:
          bf.cpl_b(bits, t, 1n+i, st, 1n+ln, s, l, bf.q_false(bits, st, ln, t, q), bf.hi_succ(i, st, ln, hi), hm, hs, Nat.is_lt(1n+i, s), {==}, Nat.is_eq(s, 2n+i), {==})
        case True{}:
          match q1:
            case False{}:
              Empty.absurd({bf.memr(F.genpool.fit.runs.go(Con{True{}, t}, i, st, ln), s, l) == True{} : Bool}, bf.inside(bits, st, ln, Con{True{}, t}, i, s, q, hi, hs, bf.nle(i, s, hq1), bf.mx_left(bits, s, l, hm)))
            case True{}:
              match q2:
                case True{}:
                  %N.nl.eq(1n+i, s, Equal.trans(Bool, Nat.is_eq(1n+i, s), Nat.is_eq(s, 1n+i), True{}, bf.eq_comm(1n+i, s), hq2)) : {bf.memr(F.genpool.fit.runs.go(Con{True{}, t}, i, st, ln), _, l) == True{} : Bool}
                  bf.close_mem(st, ln, F.genpool.fit.runs.go(t, 1n+i, 1n+i, 0n), 1n+i, l, bf.cpl_a(bits, t, 1n+i, 1n+i, 0n, l, bf.drop_succ(bits, i, True{}, t, bf.da(bits, st, ln, Con{True{}, t}, i, q, hi)), bf.hi_zero(i), Equal.trans(Bool, Laws.bf.maximal(bits, 1n+i, l), Laws.bf.maximal(bits, s, l), True{}, Equal.cong(Nat, Bool, z => Laws.bf.maximal(bits, z, l), 1n+i, s, N.nl.eq(1n+i, s, Equal.trans(Bool, Nat.is_eq(1n+i, s), Nat.is_eq(s, 1n+i), True{}, bf.eq_comm(1n+i, s), hq2))), hm)))
                case False{}:
                  bf.close_mem(st, ln, F.genpool.fit.runs.go(t, 1n+i, 1n+i, 0n), s, l, bf.cpl_b(bits, t, 1n+i, 1n+i, 0n, s, l, bf.drop_succ(bits, i, True{}, t, bf.da(bits, st, ln, Con{True{}, t}, i, q, hi)), bf.hi_zero(i), hm, bf.lt_next(i, s, hq1, hq2), Nat.is_lt(1n+i, s), {==}, Nat.is_eq(s, 2n+i), {==}))

# every maximal run is listed
def bf.cpl(+bits: List<&2, Bool>, s: Nat, +l: Nat, +hm: {Laws.bf.maximal(bits, s, l) == True{} : Bool}) -> {bf.memr(F.genpool.fit.runs(bits), s, l) == True{} : Bool}:
  match s:
    case 0n:
      bf.cpl_a(bits, bits, 0n, 0n, 0n, l, bf.drop0(bits), {==}, hm)
    case 1n+ +p:
      bf.cpl_b(bits, bits, 0n, 0n, 0n, 1n+p, l, bf.drop0(bits), {==}, hm, {==}, Nat.is_lt(0n, 1n+p), {==}, Nat.is_eq(1n+p, 1n), {==})

def bf.afit_hit(c: Bool, +bits: List<&2, Bool>, +st: Nat, +ln: Nat, +t: List<&2, Bool>, +i: Nat, +n: Nat, +j: Nat, +q: {List.drop(&2, Bool, bits, st) == List.append(&2, Bool, List.replicate(Bool, ln, False{}), Con{True{}, t}) : List<&2, Bool>}, +hi: {i == Nat.add(st, ln) : Nat}, +hj: {Nat.is_le(st, j) == True{} : Bool}, +hr: {Bits.genpool.bits.run_free(bits, j, n) == True{} : Bool}, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +hji: {Nat.is_le(j, i) == True{} : Bool}, +hc: {Nat.is_lt(i, Nat.add(j, n)) == c : Bool}) -> {bf.anyfit(F.genpool.fit.runs.go(Con{True{}, t}, i, st, ln), n) == True{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({bf.anyfit(F.genpool.fit.runs.go(Con{True{}, t}, i, st, ln), n) == True{} : Bool}, N.nl.ft(Equal.trans(Bool, False{}, Bits.genpool.bits.get(bits, i), True{}, Equal.sym(Bool, Bits.genpool.bits.get(bits, i), False{}, PB.pb.rf_get(bits, j, n, i, hr, hji, hc)), bf.drop_get(bits, i, True{}, t, bf.da(bits, st, ln, Con{True{}, t}, i, q, hi)))))
    case False{}:
      bf.afit_len(st, ln, F.genpool.fit.runs.go(t, 1n+i, 1n+i, 0n), n, hn, bf.cancel(st, j, n, ln, hj, Equal.trans(Bool, Nat.is_le(Nat.add(j, n), Nat.add(st, ln)), Nat.is_le(Nat.add(j, n), i), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(Nat.add(j, n), z), Nat.add(st, ln), i, Equal.sym(Nat, i, Nat.add(st, ln), hi)), bf.nle(i, Nat.add(j, n), hc))))

# a free run of n >= 1 granules lies in a run the scan lists, of n or more
def bf.afit(+bits: List<&2, Bool>, rest: List<&2, Bool>, +i: Nat, +st: Nat, +ln: Nat, +n: Nat, +j: Nat, +q: {List.drop(&2, Bool, bits, st) == List.append(&2, Bool, List.replicate(Bool, ln, False{}), rest) : List<&2, Bool>}, +hi: {i == Nat.add(st, ln) : Nat}, +hj: {Nat.is_le(st, j) == True{} : Bool}, +hr: {Bits.genpool.bits.run_free(bits, j, n) == True{} : Bool}, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, c: Bool, +hc: {Nat.is_le(j, i) == c : Bool}) -> {bf.anyfit(F.genpool.fit.runs.go(rest, i, st, ln), n) == True{} : Bool}:
  match rest:
    case Nil{}:
      bf.afit_len(st, ln, Nil{}, n, hn, bf.cancel(st, j, n, ln, hj, N.nl.le_trans(Nat.add(j, n), List.length(&2, Bool, bits), Nat.add(st, ln), PB.pb.rf_len(bits, j, n, hn, hr), Equal.trans(Bool, Nat.is_le(List.length(&2, Bool, bits), Nat.add(st, ln)), Nat.is_le(List.length(&2, Bool, bits), i), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(List.length(&2, Bool, bits), z), Nat.add(st, ln), i, Equal.sym(Nat, i, Nat.add(st, ln), hi)), bf.drop_nil(bits, i, bf.da(bits, st, ln, Nil{}, i, q, hi))))))
    case Con{b, +t}:
      match b:
        case False{}:
          bf.afit(bits, t, 1n+i, st, 1n+ln, n, j, bf.q_false(bits, st, ln, t, q), bf.hi_succ(i, st, ln, hi), hj, hr, hn, Nat.is_le(j, 1n+i), {==})
        case True{}:
          match c:
            case True{}:
              bf.afit_hit(Nat.is_lt(i, Nat.add(j, n)), bits, st, ln, t, i, n, j, q, hi, hj, hr, hn, hc, {==})
            case False{}:
              bf.close_any(st, ln, F.genpool.fit.runs.go(t, 1n+i, 1n+i, 0n), n, bf.afit(bits, t, 1n+i, 1n+i, 0n, n, j, bf.drop_succ(bits, i, True{}, t, bf.da(bits, st, ln, Con{True{}, t}, i, q, hi)), bf.hi_zero(i), bf.lt_s(i, j, bf.nle_lt(j, i, hc)), hr, hn, Nat.is_le(j, 1n+i), {==}))

# Choosing the best

def bf.imp(+rb: F.GpRun, +a: F.GpRun) -> Bool:
  Bool.or(Bool.and(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(a)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(a))), Nat.is_lt(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(a)))

def bf.resimp(res: Maybe<&2, F.GpRun>, +a: F.GpRun) -> Bool:
  match res:
    case None{}:
      False{}
    case Some{rb}:
      bf.imp(rb, a)

def bf.imp_refl(a: F.GpRun) -> {bf.imp(a, a) == True{} : Bool}:
  match a:
    case F.GpRun{+s, +l}:
      %Equal.sym(Bool, Nat.is_eq(s, s), True{}, N.nl.eq_refl(s)) : {Bool.or(Bool.and(_, Nat.is_eq(l, l)), Nat.is_lt(l, l)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(l, l), True{}, N.nl.eq_refl(l)) : {Bool.or(_, Nat.is_lt(l, l)) == True{} : Bool}
      {==}

def bf.imp_lt.go(c: Bool, +rb: F.GpRun, +r: F.GpRun, +a: F.GpRun, +hc: {Bool.and(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(r)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r))) == c : Bool}, +h: {bf.imp(rb, r) == True{} : Bool}, +hlt: {Nat.is_lt(F.genpool.fit.run_len(r), F.genpool.fit.run_len(a)) == True{} : Bool}) -> {Nat.is_lt(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(a)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Nat, F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r), N.nl.eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r), N.nl.and_r(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(r)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r)), hc))) : {Nat.is_lt(_, F.genpool.fit.run_len(a)) == True{} : Bool}
      hlt
    case False{}:
      N.nl.lt_le_trans(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r), F.genpool.fit.run_len(a), Equal.trans(Bool, Nat.is_lt(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r)), bf.imp(rb, r), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, Nat.is_lt(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r))), False{}, Bool.and(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(r)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r))), Equal.sym(Bool, Bool.and(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(r)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r))), False{}, hc)), h), N.nl.lt_le(F.genpool.fit.run_len(r), F.genpool.fit.run_len(a), hlt))

def bf.resimp_lt(res: Maybe<&2, F.GpRun>, +r: F.GpRun, +a: F.GpRun, h: {bf.resimp(res, r) == True{} : Bool}, +hlt: {Nat.is_lt(F.genpool.fit.run_len(r), F.genpool.fit.run_len(a)) == True{} : Bool}) -> {bf.resimp(res, a) == True{} : Bool}:
  match res:
    case None{}:
      Empty.absurd({False{} == True{} : Bool}, N.nl.ft(h))
    case Some{+rb}:
      %Equal.sym(Bool, Nat.is_lt(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(a)), True{}, bf.imp_lt.go(Bool.and(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(r)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r))), rb, r, a, {==}, h, hlt)) : {Bool.or(Bool.and(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(a)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(a))), _) == True{} : Bool}
      bf.or_t(Bool.and(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(a)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(a))))

# what best.go answers improves on what it starts from
def bf.bg1(rs: List<&2, F.GpRun>, +n: Nat, a: F.GpRun, fits: Bool, +hf: {Nat.is_le(n, F.genpool.fit.run_len(bf.hdr(rs))) == fits : Bool}, lt: Bool, +hl: {Nat.is_lt(F.genpool.fit.run_len(bf.hdr(rs)), F.genpool.fit.run_len(a)) == lt : Bool}) -> {bf.resimp(F.genpool.fit.best.go(rs, n, Some{a}), a) == True{} : Bool}:
  match rs:
    case Nil{}:
      bf.imp_refl(a)
    case Con{+r, +t}:
      match a:
        case F.GpRun{+s, +l}:
          match fits:
            case False{}:
              %Equal.sym(Bool, Nat.is_le(n, F.genpool.fit.run_len(r)), False{}, hf) : {bf.resimp(F.genpool.fit.best.go(t, n, F.genpool.fit.better(_, r, Some{F.GpRun{s, l}})), F.GpRun{s, l}) == True{} : Bool}
              bf.bg1(t, n, F.GpRun{s, l}, Nat.is_le(n, F.genpool.fit.run_len(bf.hdr(t))), {==}, Nat.is_lt(F.genpool.fit.run_len(bf.hdr(t)), l), {==})
            case True{}:
              match lt:
                case True{}:
                  %Equal.sym(Bool, Nat.is_le(n, F.genpool.fit.run_len(r)), True{}, hf) : {bf.resimp(F.genpool.fit.best.go(t, n, F.genpool.fit.better(_, r, Some{F.GpRun{s, l}})), F.GpRun{s, l}) == True{} : Bool}
                  %Equal.sym(Bool, Nat.is_lt(F.genpool.fit.run_len(r), l), True{}, hl) : {bf.resimp(F.genpool.fit.best.go(t, n, Bool.pick(Maybe<&2, F.GpRun>, _, Some{r}, Some{F.GpRun{s, l}})), F.GpRun{s, l}) == True{} : Bool}
                  bf.resimp_lt(F.genpool.fit.best.go(t, n, Some{r}), r, F.GpRun{s, l}, bf.bg1(t, n, r, Nat.is_le(n, F.genpool.fit.run_len(bf.hdr(t))), {==}, Nat.is_lt(F.genpool.fit.run_len(bf.hdr(t)), F.genpool.fit.run_len(r)), {==}), hl)
                case False{}:
                  %Equal.sym(Bool, Nat.is_le(n, F.genpool.fit.run_len(r)), True{}, hf) : {bf.resimp(F.genpool.fit.best.go(t, n, F.genpool.fit.better(_, r, Some{F.GpRun{s, l}})), F.GpRun{s, l}) == True{} : Bool}
                  %Equal.sym(Bool, Nat.is_lt(F.genpool.fit.run_len(r), l), False{}, hl) : {bf.resimp(F.genpool.fit.best.go(t, n, Bool.pick(Maybe<&2, F.GpRun>, _, Some{r}, Some{F.GpRun{s, l}})), F.GpRun{s, l}) == True{} : Bool}
                  bf.bg1(t, n, F.GpRun{s, l}, Nat.is_le(n, F.genpool.fit.run_len(bf.hdr(t))), {==}, Nat.is_lt(F.genpool.fit.run_len(bf.hdr(t)), l), {==})

def bf.bg1s(+rs: List<&2, F.GpRun>, +n: Nat, +a: F.GpRun) -> {bf.resimp(F.genpool.fit.best.go(rs, n, Some{a}), a) == True{} : Bool}:
  bf.bg1(rs, n, a, Nat.is_le(n, F.genpool.fit.run_len(bf.hdr(rs))), {==}, Nat.is_lt(F.genpool.fit.run_len(bf.hdr(rs)), F.genpool.fit.run_len(a)), {==})

# what best.go answers is at least as good as every run it saw

def bf.good(+n: Nat, +rb: F.GpRun, +s2: Nat, +l2: Nat) -> Bool:
  Bool.or(Bool.not(Nat.is_le(n, l2)), Bool.and(Nat.is_le(F.genpool.fit.run_len(rb), l2), Bool.or(Bool.not(Nat.is_lt(s2, F.genpool.fit.run_start(rb))), Nat.is_lt(F.genpool.fit.run_len(rb), l2))))

def bf.resgood(+n: Nat, res: Maybe<&2, F.GpRun>, +s2: Nat, +l2: Nat) -> Bool:
  match res:
    case None{}:
      Bool.not(Nat.is_le(n, l2))
    case Some{rb}:
      bf.good(n, rb, s2, l2)

def bf.accb(acc: Maybe<&2, F.GpRun>, +lb: Nat) -> Bool:
  match acc:
    case None{}:
      True{}
    case Some{a}:
      Nat.is_lt(F.genpool.fit.run_start(a), lb)

def bf.good_and(+n: Nat, +rb: F.GpRun, +s2: Nat, +l2: Nat, h1: {Nat.is_le(F.genpool.fit.run_len(rb), l2) == True{} : Bool}, h2: {Bool.or(Bool.not(Nat.is_lt(s2, F.genpool.fit.run_start(rb))), Nat.is_lt(F.genpool.fit.run_len(rb), l2)) == True{} : Bool}) -> {bf.good(n, rb, s2, l2) == True{} : Bool}:
  %Equal.sym(Bool, Bool.and(Nat.is_le(F.genpool.fit.run_len(rb), l2), Bool.or(Bool.not(Nat.is_lt(s2, F.genpool.fit.run_start(rb))), Nat.is_lt(F.genpool.fit.run_len(rb), l2))), True{}, N.nl.and_i(Nat.is_le(F.genpool.fit.run_len(rb), l2), Bool.or(Bool.not(Nat.is_lt(s2, F.genpool.fit.run_start(rb))), Nat.is_lt(F.genpool.fit.run_len(rb), l2)), h1, h2)) : {Bool.or(Bool.not(Nat.is_le(n, l2)), _) == True{} : Bool}
  bf.or_t(Bool.not(Nat.is_le(n, l2)))

def bf.rg_nofit(+n: Nat, res: Maybe<&2, F.GpRun>, +s2: Nat, +l2: Nat, +h: {Nat.is_le(n, l2) == False{} : Bool}) -> {bf.resgood(n, res, s2, l2) == True{} : Bool}:
  match res:
    case None{}:
      %Equal.sym(Bool, Nat.is_le(n, l2), False{}, h) : {Bool.not(_) == True{} : Bool}
      {==}
    case Some{+rb}:
      %Equal.sym(Bool, Nat.is_le(n, l2), False{}, h) : {Bool.or(Bool.not(_), Bool.and(Nat.is_le(F.genpool.fit.run_len(rb), l2), Bool.or(Bool.not(Nat.is_lt(s2, F.genpool.fit.run_start(rb))), Nat.is_lt(F.genpool.fit.run_len(rb), l2)))) == True{} : Bool}
      {==}

def bf.not_f(+b: Bool, h: {b == False{} : Bool}) -> {Bool.or(Bool.not(b), b) == True{} : Bool}:
  %Equal.sym(Bool, b, False{}, h) : {Bool.or(Bool.not(_), _) == True{} : Bool}
  {==}

def bf.or_l(+a: Bool, +b: Bool, h: {Bool.not(a) == True{} : Bool}) -> {Bool.or(Bool.not(a), b) == True{} : Bool}:
  %Equal.sym(Bool, Bool.not(a), True{}, h) : {Bool.or(_, b) == True{} : Bool}
  {==}

def bf.not_ft(+a: Bool, h: {a == False{} : Bool}) -> {Bool.not(a) == True{} : Bool}:
  %Equal.sym(Bool, a, False{}, h) : {Bool.not(_) == True{} : Bool}
  {==}

def bf.or_r(+a: Bool, +b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, b, True{}, h) : {Bool.or(a, _) == True{} : Bool}
  bf.or_t(a)

def bf.imp_r(+rb: F.GpRun, +r: F.GpRun, +hc: {Bool.and(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(r)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r))) == False{} : Bool}, +h: {bf.imp(rb, r) == True{} : Bool}) -> {Nat.is_lt(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r)) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r)), bf.imp(rb, r), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, Nat.is_lt(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r))), False{}, Bool.and(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(r)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r))), Equal.sym(Bool, Bool.and(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(r)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r))), False{}, hc)), h)

# the run itself, or one improving on it
def bf.g_self.go(c: Bool, +n: Nat, +rb: F.GpRun, +r: F.GpRun, +hc: {Bool.and(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(r)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r))) == c : Bool}, +h: {bf.imp(rb, r) == True{} : Bool}) -> {bf.good(n, rb, F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)) == True{} : Bool}:
  match c:
    case True{}:
      bf.good_and(n, rb, F.genpool.fit.run_start(r), F.genpool.fit.run_len(r), Equal.trans(Bool, Nat.is_le(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r)), Nat.is_le(F.genpool.fit.run_len(r), F.genpool.fit.run_len(r)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, F.genpool.fit.run_len(r)), F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r), N.nl.eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r), N.nl.and_r(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(r)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r)), hc))), N.nl.le_refl(F.genpool.fit.run_len(r))), bf.or_l(Nat.is_lt(F.genpool.fit.run_start(r), F.genpool.fit.run_start(rb)), Nat.is_lt(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r)), bf.not_ft(Nat.is_lt(F.genpool.fit.run_start(r), F.genpool.fit.run_start(rb)), Equal.trans(Bool, Nat.is_lt(F.genpool.fit.run_start(r), F.genpool.fit.run_start(rb)), Nat.is_lt(F.genpool.fit.run_start(r), F.genpool.fit.run_start(r)), False{}, Equal.cong(Nat, Bool, z => Nat.is_lt(F.genpool.fit.run_start(r), z), F.genpool.fit.run_start(rb), F.genpool.fit.run_start(r), N.nl.eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(r), N.nl.and_l(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(r)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r)), hc))), bf.lt_irr(F.genpool.fit.run_start(r))))))
    case False{}:
      bf.good_and(n, rb, F.genpool.fit.run_start(r), F.genpool.fit.run_len(r), N.nl.lt_le(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r), bf.imp_r(rb, r, hc, h)), bf.or_r(Bool.not(Nat.is_lt(F.genpool.fit.run_start(r), F.genpool.fit.run_start(rb))), Nat.is_lt(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r)), bf.imp_r(rb, r, hc, h)))

def bf.rg_imp(res: Maybe<&2, F.GpRun>, +n: Nat, +r: F.GpRun, h: {bf.resimp(res, r) == True{} : Bool}) -> {bf.resgood(n, res, F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)) == True{} : Bool}:
  match res:
    case None{}:
      Empty.absurd({Bool.not(Nat.is_le(n, F.genpool.fit.run_len(r))) == True{} : Bool}, N.nl.ft(h))
    case Some{+rb}:
      bf.g_self.go(Bool.and(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(r)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r))), n, rb, r, {==}, h)

# an earlier run kept: it is no longer than r and starts before it
def bf.g_kept.go(c: Bool, +n: Nat, +rb: F.GpRun, +a: F.GpRun, +r: F.GpRun, +hc: {Bool.and(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(a)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(a))) == c : Bool}, +h: {bf.imp(rb, a) == True{} : Bool}, +hle: {Nat.is_le(F.genpool.fit.run_len(a), F.genpool.fit.run_len(r)) == True{} : Bool}, +hst: {Nat.is_lt(F.genpool.fit.run_start(a), F.genpool.fit.run_start(r)) == True{} : Bool}) -> {bf.good(n, rb, F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)) == True{} : Bool}:
  match c:
    case True{}:
      bf.good_and(n, rb, F.genpool.fit.run_start(r), F.genpool.fit.run_len(r), Equal.trans(Bool, Nat.is_le(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r)), Nat.is_le(F.genpool.fit.run_len(a), F.genpool.fit.run_len(r)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, F.genpool.fit.run_len(r)), F.genpool.fit.run_len(rb), F.genpool.fit.run_len(a), N.nl.eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(a), N.nl.and_r(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(a)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(a)), hc))), hle), bf.or_l(Nat.is_lt(F.genpool.fit.run_start(r), F.genpool.fit.run_start(rb)), Nat.is_lt(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r)), bf.not_ft(Nat.is_lt(F.genpool.fit.run_start(r), F.genpool.fit.run_start(rb)), Equal.trans(Bool, Nat.is_lt(F.genpool.fit.run_start(r), F.genpool.fit.run_start(rb)), Nat.is_lt(F.genpool.fit.run_start(r), F.genpool.fit.run_start(a)), False{}, Equal.cong(Nat, Bool, z => Nat.is_lt(F.genpool.fit.run_start(r), z), F.genpool.fit.run_start(rb), F.genpool.fit.run_start(a), N.nl.eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(a), N.nl.and_l(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(a)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(a)), hc))), N.nl.le_nlt(F.genpool.fit.run_start(a), F.genpool.fit.run_start(r), N.nl.lt_le(F.genpool.fit.run_start(a), F.genpool.fit.run_start(r), hst))))))
    case False{}:
      bf.good_and(n, rb, F.genpool.fit.run_start(r), F.genpool.fit.run_len(r), N.nl.lt_le(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r), N.nl.lt_le_trans(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(a), F.genpool.fit.run_len(r), bf.imp_r(rb, a, hc, h), hle)), bf.or_r(Bool.not(Nat.is_lt(F.genpool.fit.run_start(r), F.genpool.fit.run_start(rb))), Nat.is_lt(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(r)), N.nl.lt_le_trans(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(a), F.genpool.fit.run_len(r), bf.imp_r(rb, a, hc, h), hle)))

def bf.rg_kept(res: Maybe<&2, F.GpRun>, +n: Nat, +a: F.GpRun, +r: F.GpRun, h: {bf.resimp(res, a) == True{} : Bool}, +hle: {Nat.is_le(F.genpool.fit.run_len(a), F.genpool.fit.run_len(r)) == True{} : Bool}, +hst: {Nat.is_lt(F.genpool.fit.run_start(a), F.genpool.fit.run_start(r)) == True{} : Bool}) -> {bf.resgood(n, res, F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)) == True{} : Bool}:
  match res:
    case None{}:
      Empty.absurd({Bool.not(Nat.is_le(n, F.genpool.fit.run_len(r))) == True{} : Bool}, N.nl.ft(h))
    case Some{+rb}:
      bf.g_kept.go(Bool.and(Nat.is_eq(F.genpool.fit.run_start(rb), F.genpool.fit.run_start(a)), Nat.is_eq(F.genpool.fit.run_len(rb), F.genpool.fit.run_len(a))), n, rb, a, r, {==}, h, hle, hst)

def bf.lt_s1(+a: Nat, +lb: Nat, +x: Nat, h1: {Nat.is_lt(a, lb) == True{} : Bool}, h2: {Nat.is_le(lb, x) == True{} : Bool}) -> {Nat.is_lt(a, 1n+x) == True{} : Bool}:
  N.nl.lt_le_trans(a, lb, 1n+x, h1, N.nl.le_trans(lb, x, 1n+x, h2, N.nl.le_succ(x)))

def bf.pick_accb(c: Bool, +r: F.GpRun, +a: F.GpRun, +lb: Nat, +ha: {Nat.is_lt(F.genpool.fit.run_start(a), lb) == True{} : Bool}, +hlb: {Nat.is_le(lb, F.genpool.fit.run_start(r)) == True{} : Bool}) -> {bf.accb(Bool.pick(Maybe<&2, F.GpRun>, c, Some{r}, Some{a}), 1n+F.genpool.fit.run_start(r)) == True{} : Bool}:
  match c:
    case True{}:
      bf.lt_succ(F.genpool.fit.run_start(r))
    case False{}:
      bf.lt_s1(F.genpool.fit.run_start(a), lb, F.genpool.fit.run_start(r), ha, hlb)

# the run kept after r starts before the next one
def bf.ab(fits: Bool, +r: F.GpRun, acc: Maybe<&2, F.GpRun>, +lb: Nat, +hacc: {bf.accb(acc, lb) == True{} : Bool}, +hlb: {Nat.is_le(lb, F.genpool.fit.run_start(r)) == True{} : Bool}) -> {bf.accb(F.genpool.fit.better(fits, r, acc), 1n+F.genpool.fit.run_start(r)) == True{} : Bool}:
  match fits:
    case False{}:
      match acc:
        case None{}:
          {==}
        case Some{+a}:
          bf.lt_s1(F.genpool.fit.run_start(a), lb, F.genpool.fit.run_start(r), hacc, hlb)
    case True{}:
      match acc:
        case None{}:
          bf.lt_succ(F.genpool.fit.run_start(r))
        case Some{a}:
          match a:
            case F.GpRun{+s, +l}:
              bf.pick_accb(Nat.is_lt(F.genpool.fit.run_len(r), l), r, F.GpRun{s, l}, lb, hacc, hlb)

def bf.hit2(lt: Bool, +n: Nat, +r: F.GpRun, +t: List<&2, F.GpRun>, +s: Nat, +l: Nat, +lb: Nat, +hlt: {Nat.is_lt(F.genpool.fit.run_len(r), l) == lt : Bool}, +hacc: {Nat.is_lt(s, lb) == True{} : Bool}, +hlb: {Nat.is_le(lb, F.genpool.fit.run_start(r)) == True{} : Bool}) -> {bf.resgood(n, F.genpool.fit.best.go(t, n, Bool.pick(Maybe<&2, F.GpRun>, Nat.is_lt(F.genpool.fit.run_len(r), l), Some{r}, Some{F.GpRun{s, l}})), F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)) == True{} : Bool}:
  match lt:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(F.genpool.fit.run_len(r), l), True{}, hlt) : {bf.resgood(n, F.genpool.fit.best.go(t, n, Bool.pick(Maybe<&2, F.GpRun>, _, Some{r}, Some{F.GpRun{s, l}})), F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)) == True{} : Bool}
      bf.rg_imp(F.genpool.fit.best.go(t, n, Some{r}), n, r, bf.bg1s(t, n, r))
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(F.genpool.fit.run_len(r), l), False{}, hlt) : {bf.resgood(n, F.genpool.fit.best.go(t, n, Bool.pick(Maybe<&2, F.GpRun>, _, Some{r}, Some{F.GpRun{s, l}})), F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)) == True{} : Bool}
      bf.rg_kept(F.genpool.fit.best.go(t, n, Some{F.GpRun{s, l}}), n, F.GpRun{s, l}, r, bf.bg1s(t, n, F.GpRun{s, l}), bf.nle(F.genpool.fit.run_len(r), l, hlt), N.nl.lt_le_trans(s, lb, F.genpool.fit.run_start(r), hacc, hlb))

# the run r itself, as best.go meets it
def bf.hit(fits: Bool, +n: Nat, +r: F.GpRun, +t: List<&2, F.GpRun>, acc: Maybe<&2, F.GpRun>, +lb: Nat, +hf: {Nat.is_le(n, F.genpool.fit.run_len(r)) == fits : Bool}, +hacc: {bf.accb(acc, lb) == True{} : Bool}, +hlb: {Nat.is_le(lb, F.genpool.fit.run_start(r)) == True{} : Bool}) -> {bf.resgood(n, F.genpool.fit.best.go(t, n, F.genpool.fit.better(Nat.is_le(n, F.genpool.fit.run_len(r)), r, acc)), F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)) == True{} : Bool}:
  match fits:
    case False{}:
      %Equal.sym(Bool, Nat.is_le(n, F.genpool.fit.run_len(r)), False{}, hf) : {bf.resgood(n, F.genpool.fit.best.go(t, n, F.genpool.fit.better(_, r, acc)), F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)) == True{} : Bool}
      bf.rg_nofit(n, F.genpool.fit.best.go(t, n, acc), F.genpool.fit.run_start(r), F.genpool.fit.run_len(r), hf)
    case True{}:
      match acc:
        case None{}:
          %Equal.sym(Bool, Nat.is_le(n, F.genpool.fit.run_len(r)), True{}, hf) : {bf.resgood(n, F.genpool.fit.best.go(t, n, F.genpool.fit.better(_, r, None{})), F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)) == True{} : Bool}
          bf.rg_imp(F.genpool.fit.best.go(t, n, Some{r}), n, r, bf.bg1s(t, n, r))
        case Some{a}:
          match a:
            case F.GpRun{+s, +l}:
              %Equal.sym(Bool, Nat.is_le(n, F.genpool.fit.run_len(r)), True{}, hf) : {bf.resgood(n, F.genpool.fit.best.go(t, n, F.genpool.fit.better(_, r, Some{F.GpRun{s, l}})), F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)) == True{} : Bool}
              bf.hit2(Nat.is_lt(F.genpool.fit.run_len(r), l), n, r, t, s, l, lb, {==}, hacc, hlb)

# every run of a sorted list is no better than what best.go answers
def bf.bg2(rs: List<&2, F.GpRun>, +n: Nat, +acc: Maybe<&2, F.GpRun>, +lb: Nat, +s2: Nat, +l2: Nat, hb: Bool, +hh: {Bool.and(Nat.is_eq(F.genpool.fit.run_start(bf.hdr(rs)), s2), Nat.is_eq(F.genpool.fit.run_len(bf.hdr(rs)), l2)) == hb : Bool}, +hs: {bf.srt(rs, lb) == True{} : Bool}, +hacc: {bf.accb(acc, lb) == True{} : Bool}, +hm: {bf.memr(rs, s2, l2) == True{} : Bool}) -> {bf.resgood(n, F.genpool.fit.best.go(rs, n, acc), s2, l2) == True{} : Bool}:
  match rs:
    case Nil{}:
      Empty.absurd({bf.resgood(n, acc, s2, l2) == True{} : Bool}, N.nl.ft(hm))
    case Con{+r, +t}:
      match hb:
        case True{}:
          %N.nl.eq(F.genpool.fit.run_start(r), s2, N.nl.and_l(Nat.is_eq(F.genpool.fit.run_start(r), s2), Nat.is_eq(F.genpool.fit.run_len(r), l2), hh)) : {bf.resgood(n, F.genpool.fit.best.go(Con{r, t}, n, acc), _, l2) == True{} : Bool}
          %N.nl.eq(F.genpool.fit.run_len(r), l2, N.nl.and_r(Nat.is_eq(F.genpool.fit.run_start(r), s2), Nat.is_eq(F.genpool.fit.run_len(r), l2), hh)) : {bf.resgood(n, F.genpool.fit.best.go(Con{r, t}, n, acc), F.genpool.fit.run_start(r), _) == True{} : Bool}
          bf.hit(Nat.is_le(n, F.genpool.fit.run_len(r)), n, r, t, acc, lb, {==}, hacc, N.nl.and_l(Nat.is_le(lb, F.genpool.fit.run_start(r)), bf.srt(t, 1n+F.genpool.fit.run_start(r)), hs))
        case False{}:
          bf.bg2(t, n, F.genpool.fit.better(Nat.is_le(n, F.genpool.fit.run_len(r)), r, acc), 1n+F.genpool.fit.run_start(r), s2, l2, Bool.and(Nat.is_eq(F.genpool.fit.run_start(bf.hdr(t)), s2), Nat.is_eq(F.genpool.fit.run_len(bf.hdr(t)), l2)), {==}, N.nl.and_r(Nat.is_le(lb, F.genpool.fit.run_start(r)), bf.srt(t, 1n+F.genpool.fit.run_start(r)), hs), bf.ab(Nat.is_le(n, F.genpool.fit.run_len(r)), r, acc, lb, hacc, N.nl.and_l(Nat.is_le(lb, F.genpool.fit.run_start(r)), bf.srt(t, 1n+F.genpool.fit.run_start(r)), hs)), Equal.trans(Bool, bf.memr(t, s2, l2), Bool.or(Bool.and(Nat.is_eq(F.genpool.fit.run_start(r), s2), Nat.is_eq(F.genpool.fit.run_len(r), l2)), bf.memr(t, s2, l2)), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, bf.memr(t, s2, l2)), False{}, Bool.and(Nat.is_eq(F.genpool.fit.run_start(r), s2), Nat.is_eq(F.genpool.fit.run_len(r), l2)), Equal.sym(Bool, Bool.and(Nat.is_eq(F.genpool.fit.run_start(r), s2), Nat.is_eq(F.genpool.fit.run_len(r), l2)), False{}, hh)), hm))

# best.go answers something when a run fits

def bf.issome(m: Maybe<&2, F.GpRun>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def bf.imp_some(res: Maybe<&2, F.GpRun>, +a: F.GpRun, h: {bf.resimp(res, a) == True{} : Bool}) -> {bf.issome(res) == True{} : Bool}:
  match res:
    case None{}:
      h
    case Some{x}:
      {==}

def bf.bs_pick(c: Bool, +r: F.GpRun, +a: F.GpRun, +t: List<&2, F.GpRun>, +n: Nat) -> {bf.issome(F.genpool.fit.best.go(t, n, Bool.pick(Maybe<&2, F.GpRun>, c, Some{r}, Some{a}))) == True{} : Bool}:
  match c:
    case True{}:
      bf.imp_some(F.genpool.fit.best.go(t, n, Some{r}), r, bf.bg1s(t, n, r))
    case False{}:
      bf.imp_some(F.genpool.fit.best.go(t, n, Some{a}), a, bf.bg1s(t, n, a))

def bf.bs2(rs: List<&2, F.GpRun>, +n: Nat, fits: Bool, +hf: {Nat.is_le(n, F.genpool.fit.run_len(bf.hdr(rs))) == fits : Bool}, acc: Maybe<&2, F.GpRun>, +h: {bf.anyfit(rs, n) == True{} : Bool}) -> {bf.issome(F.genpool.fit.best.go(rs, n, acc)) == True{} : Bool}:
  match rs:
    case Nil{}:
      Empty.absurd({bf.issome(acc) == True{} : Bool}, N.nl.ft(h))
    case Con{+r, +t}:
      match fits:
        case True{}:
          match acc:
            case None{}:
              %Equal.sym(Bool, Nat.is_le(n, F.genpool.fit.run_len(r)), True{}, hf) : {bf.issome(F.genpool.fit.best.go(t, n, F.genpool.fit.better(_, r, None{}))) == True{} : Bool}
              bf.imp_some(F.genpool.fit.best.go(t, n, Some{r}), r, bf.bg1s(t, n, r))
            case Some{a}:
              match a:
                case F.GpRun{+s, +l}:
                  %Equal.sym(Bool, Nat.is_le(n, F.genpool.fit.run_len(r)), True{}, hf) : {bf.issome(F.genpool.fit.best.go(t, n, F.genpool.fit.better(_, r, Some{F.GpRun{s, l}}))) == True{} : Bool}
                  bf.bs_pick(Nat.is_lt(F.genpool.fit.run_len(r), l), r, F.GpRun{s, l}, t, n)
        case False{}:
          %Equal.sym(Bool, Nat.is_le(n, F.genpool.fit.run_len(r)), False{}, hf) : {bf.issome(F.genpool.fit.best.go(t, n, F.genpool.fit.better(_, r, acc))) == True{} : Bool}
          bf.bs2(t, n, Nat.is_le(n, F.genpool.fit.run_len(bf.hdr(t))), {==}, acc, Equal.trans(Bool, bf.anyfit(t, n), Bool.or(Nat.is_le(n, F.genpool.fit.run_len(r)), bf.anyfit(t, n)), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, bf.anyfit(t, n)), False{}, Nat.is_le(n, F.genpool.fit.run_len(r)), Equal.sym(Bool, Nat.is_le(n, F.genpool.fit.run_len(r)), False{}, hf)), h))

# what best.go answers is a run of the list that fits

def bf.pfit(+full: List<&2, F.GpRun>, +n: Nat, m: Maybe<&2, F.GpRun>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+a}:
      Bool.and(bf.memr(full, F.genpool.fit.run_start(a), F.genpool.fit.run_len(a)), Nat.is_le(n, F.genpool.fit.run_len(a)))

def bf.mem_app(pre: List<&2, F.GpRun>, +r: F.GpRun, +t: List<&2, F.GpRun>) -> {bf.memr(List.append(&2, F.GpRun, pre, Con{r, t}), F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(F.genpool.fit.run_start(r), F.genpool.fit.run_start(r)), True{}, N.nl.eq_refl(F.genpool.fit.run_start(r))) : {Bool.or(Bool.and(_, Nat.is_eq(F.genpool.fit.run_len(r), F.genpool.fit.run_len(r))), bf.memr(t, F.genpool.fit.run_start(r), F.genpool.fit.run_len(r))) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(F.genpool.fit.run_len(r), F.genpool.fit.run_len(r)), True{}, N.nl.eq_refl(F.genpool.fit.run_len(r))) : {Bool.or(_, bf.memr(t, F.genpool.fit.run_start(r), F.genpool.fit.run_len(r))) == True{} : Bool}
      {==}
    case Con{+h, p}:
      %Equal.sym(Bool, bf.memr(List.append(&2, F.GpRun, p, Con{r, t}), F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)), True{}, bf.mem_app(p, r, t)) : {Bool.or(Bool.and(Nat.is_eq(F.genpool.fit.run_start(h), F.genpool.fit.run_start(r)), Nat.is_eq(F.genpool.fit.run_len(h), F.genpool.fit.run_len(r))), _) == True{} : Bool}
      bf.or_t(Bool.and(Nat.is_eq(F.genpool.fit.run_start(h), F.genpool.fit.run_start(r)), Nat.is_eq(F.genpool.fit.run_len(h), F.genpool.fit.run_len(r))))

def bf.rapp(pre: List<&2, F.GpRun>, +r: F.GpRun, +t: List<&2, F.GpRun>) -> {List.append(&2, F.GpRun, List.append(&2, F.GpRun, pre, Con{r, Nil{}}), t) == List.append(&2, F.GpRun, pre, Con{r, t}) : List<&2, F.GpRun>}:
  match pre:
    case Nil{}:
      {==}
    case Con{+h, p}:
      Equal.cong(List<&2, F.GpRun>, List<&2, F.GpRun>, z => Con{h, z}, List.append(&2, F.GpRun, List.append(&2, F.GpRun, p, Con{r, Nil{}}), t), List.append(&2, F.GpRun, p, Con{r, t}), bf.rapp(p, r, t))

def bf.p_new(+full: List<&2, F.GpRun>, +n: Nat, +pre: List<&2, F.GpRun>, +r: F.GpRun, +t: List<&2, F.GpRun>, +hfull: {full == List.append(&2, F.GpRun, pre, Con{r, t}) : List<&2, F.GpRun>}, +hf: {Nat.is_le(n, F.genpool.fit.run_len(r)) == True{} : Bool}) -> {bf.pfit(full, n, Some{r}) == True{} : Bool}:
  N.nl.and_i(bf.memr(full, F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)), Nat.is_le(n, F.genpool.fit.run_len(r)), Equal.trans(Bool, bf.memr(full, F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)), bf.memr(List.append(&2, F.GpRun, pre, Con{r, t}), F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)), True{}, Equal.cong(List<&2, F.GpRun>, Bool, z => bf.memr(z, F.genpool.fit.run_start(r), F.genpool.fit.run_len(r)), full, List.append(&2, F.GpRun, pre, Con{r, t}), hfull), bf.mem_app(pre, r, t)), hf)

def bf.p_pick(c: Bool, +full: List<&2, F.GpRun>, +n: Nat, +pre: List<&2, F.GpRun>, +r: F.GpRun, +t: List<&2, F.GpRun>, +a: F.GpRun, +hfull: {full == List.append(&2, F.GpRun, pre, Con{r, t}) : List<&2, F.GpRun>}, +hf: {Nat.is_le(n, F.genpool.fit.run_len(r)) == True{} : Bool}, +hp: {bf.pfit(full, n, Some{a}) == True{} : Bool}) -> {bf.pfit(full, n, Bool.pick(Maybe<&2, F.GpRun>, c, Some{r}, Some{a})) == True{} : Bool}:
  match c:
    case True{}:
      bf.p_new(full, n, pre, r, t, hfull, hf)
    case False{}:
      hp

def bf.p_better(fits: Bool, +full: List<&2, F.GpRun>, +n: Nat, +pre: List<&2, F.GpRun>, +r: F.GpRun, +t: List<&2, F.GpRun>, acc: Maybe<&2, F.GpRun>, +hfull: {full == List.append(&2, F.GpRun, pre, Con{r, t}) : List<&2, F.GpRun>}, +hf: {Nat.is_le(n, F.genpool.fit.run_len(r)) == fits : Bool}, +hp: {bf.pfit(full, n, acc) == True{} : Bool}) -> {bf.pfit(full, n, F.genpool.fit.better(Nat.is_le(n, F.genpool.fit.run_len(r)), r, acc)) == True{} : Bool}:
  match fits:
    case False{}:
      %Equal.sym(Bool, Nat.is_le(n, F.genpool.fit.run_len(r)), False{}, hf) : {bf.pfit(full, n, F.genpool.fit.better(_, r, acc)) == True{} : Bool}
      hp
    case True{}:
      match acc:
        case None{}:
          %Equal.sym(Bool, Nat.is_le(n, F.genpool.fit.run_len(r)), True{}, hf) : {bf.pfit(full, n, F.genpool.fit.better(_, r, None{})) == True{} : Bool}
          bf.p_new(full, n, pre, r, t, hfull, hf)
        case Some{a}:
          match a:
            case F.GpRun{+s, +l}:
              %Equal.sym(Bool, Nat.is_le(n, F.genpool.fit.run_len(r)), True{}, hf) : {bf.pfit(full, n, F.genpool.fit.better(_, r, Some{F.GpRun{s, l}})) == True{} : Bool}
              bf.p_pick(Nat.is_lt(F.genpool.fit.run_len(r), l), full, n, pre, r, t, F.GpRun{s, l}, hfull, hf, hp)

def bf.inres(+full: List<&2, F.GpRun>, rs: List<&2, F.GpRun>, +n: Nat, +acc: Maybe<&2, F.GpRun>, +pre: List<&2, F.GpRun>, +hfull: {full == List.append(&2, F.GpRun, pre, rs) : List<&2, F.GpRun>}, +hp: {bf.pfit(full, n, acc) == True{} : Bool}) -> {bf.pfit(full, n, F.genpool.fit.best.go(rs, n, acc)) == True{} : Bool}:
  match rs:
    case Nil{}:
      hp
    case Con{+r, +t}:
      bf.inres(full, t, n, F.genpool.fit.better(Nat.is_le(n, F.genpool.fit.run_len(r)), r, acc), List.append(&2, F.GpRun, pre, Con{r, Nil{}}), Equal.trans(List<&2, F.GpRun>, full, List.append(&2, F.GpRun, pre, Con{r, t}), List.append(&2, F.GpRun, List.append(&2, F.GpRun, pre, Con{r, Nil{}}), t), hfull, Equal.sym(List<&2, F.GpRun>, List.append(&2, F.GpRun, List.append(&2, F.GpRun, pre, Con{r, Nil{}}), t), List.append(&2, F.GpRun, pre, Con{r, t}), bf.rapp(pre, r, t))), bf.p_better(Nat.is_le(n, F.genpool.fit.run_len(r)), full, n, pre, r, t, acc, hfull, {==}, hp))

# ---------------------------------------------------------------- the laws of best fit

def bf.res(+bits: List<&2, Bool>, +n: Nat) -> Maybe<&2, F.GpRun>:
  F.genpool.fit.best.go(F.genpool.fit.runs(bits), n, None{})

def bf.pfit_of(+bits: List<&2, Bool>, +n: Nat, +rb: F.GpRun, +hm: {bf.res(bits, n) == Some{rb} : Maybe<&2, F.GpRun>}) -> {bf.pfit(F.genpool.fit.runs(bits), n, Some{rb}) == True{} : Bool}:
  Equal.trans(Bool, bf.pfit(F.genpool.fit.runs(bits), n, Some{rb}), bf.pfit(F.genpool.fit.runs(bits), n, bf.res(bits, n)), True{}, Equal.cong(Maybe<&2, F.GpRun>, Bool, z => bf.pfit(F.genpool.fit.runs(bits), n, z), Some{rb}, bf.res(bits, n), Equal.sym(Maybe<&2, F.GpRun>, bf.res(bits, n), Some{rb}, hm)), bf.inres(F.genpool.fit.runs(bits), F.genpool.fit.runs(bits), n, None{}, Nil{}, {==}, {==}))

# the run best fit answers, from what it answers
def bf.chosen(+bits: List<&2, Bool>, +n: Nat, +rb: F.GpRun, +hm: {bf.res(bits, n) == Some{rb} : Maybe<&2, F.GpRun>}) -> {Laws.bf.maximal(bits, F.genpool.fit.run_start(rb), F.genpool.fit.run_len(rb)) == True{} : Bool}:
  bf.mem_all(bits, F.genpool.fit.runs(bits), F.genpool.fit.run_start(rb), F.genpool.fit.run_len(rb), bf.sound(bits, bits, 0n, 0n, 0n, bf.drop0(bits), {==}, {==}), N.nl.and_l(bf.memr(F.genpool.fit.runs(bits), F.genpool.fit.run_start(rb), F.genpool.fit.run_len(rb)), Nat.is_le(n, F.genpool.fit.run_len(rb)), bf.pfit_of(bits, n, rb, hm)))

def bf.good_le(+n: Nat, +rb: F.GpRun, +s2: Nat, +l2: Nat, +h: {bf.good(n, rb, s2, l2) == True{} : Bool}, +h3: {Nat.is_le(n, l2) == True{} : Bool}) -> {Bool.and(Nat.is_le(F.genpool.fit.run_len(rb), l2), Bool.or(Bool.not(Nat.is_lt(s2, F.genpool.fit.run_start(rb))), Nat.is_lt(F.genpool.fit.run_len(rb), l2))) == True{} : Bool}:
  Equal.trans(Bool, Bool.or(Bool.not(True{}), Bool.and(Nat.is_le(F.genpool.fit.run_len(rb), l2), Bool.or(Bool.not(Nat.is_lt(s2, F.genpool.fit.run_start(rb))), Nat.is_lt(F.genpool.fit.run_len(rb), l2)))), bf.good(n, rb, s2, l2), True{}, Equal.cong(Bool, Bool, z => Bool.or(Bool.not(z), Bool.and(Nat.is_le(F.genpool.fit.run_len(rb), l2), Bool.or(Bool.not(Nat.is_lt(s2, F.genpool.fit.run_start(rb))), Nat.is_lt(F.genpool.fit.run_len(rb), l2)))), True{}, Nat.is_le(n, l2), Equal.sym(Bool, Nat.is_le(n, l2), True{}, h3)), h)

def bf.good_lt(+n: Nat, +rb: F.GpRun, +s2: Nat, +l2: Nat, +h: {bf.good(n, rb, s2, l2) == True{} : Bool}, +h3: {Nat.is_le(n, l2) == True{} : Bool}, +h4: {Nat.is_lt(s2, F.genpool.fit.run_start(rb)) == True{} : Bool}) -> {Nat.is_lt(F.genpool.fit.run_len(rb), l2) == True{} : Bool}:
  Equal.trans(Bool, Bool.or(Bool.not(True{}), Nat.is_lt(F.genpool.fit.run_len(rb), l2)), Bool.or(Bool.not(Nat.is_lt(s2, F.genpool.fit.run_start(rb))), Nat.is_lt(F.genpool.fit.run_len(rb), l2)), True{}, Equal.cong(Bool, Bool, z => Bool.or(Bool.not(z), Nat.is_lt(F.genpool.fit.run_len(rb), l2)), True{}, Nat.is_lt(s2, F.genpool.fit.run_start(rb)), Equal.sym(Bool, Nat.is_lt(s2, F.genpool.fit.run_start(rb)), True{}, h4)), N.nl.and_r(Nat.is_le(F.genpool.fit.run_len(rb), l2), Bool.or(Bool.not(Nat.is_lt(s2, F.genpool.fit.run_start(rb))), Nat.is_lt(F.genpool.fit.run_len(rb), l2)), bf.good_le(n, rb, s2, l2, h, h3)))

def bf.good_of(+bits: List<&2, Bool>, +n: Nat, +rb: F.GpRun, +s2: Nat, +l2: Nat, +hm: {bf.res(bits, n) == Some{rb} : Maybe<&2, F.GpRun>}, +h2: {Laws.bf.maximal(bits, s2, l2) == True{} : Bool}) -> {bf.good(n, rb, s2, l2) == True{} : Bool}:
  Equal.trans(Bool, bf.resgood(n, Some{rb}, s2, l2), bf.resgood(n, bf.res(bits, n), s2, l2), True{}, Equal.cong(Maybe<&2, F.GpRun>, Bool, z => bf.resgood(n, z, s2, l2), Some{rb}, bf.res(bits, n), Equal.sym(Maybe<&2, F.GpRun>, bf.res(bits, n), Some{rb}, hm)), bf.bg2(F.genpool.fit.runs(bits), n, None{}, 0n, s2, l2, Bool.and(Nat.is_eq(F.genpool.fit.run_start(bf.hdr(F.genpool.fit.runs(bits))), s2), Nat.is_eq(F.genpool.fit.run_len(bf.hdr(F.genpool.fit.runs(bits))), l2)), {==}, bf.sorted(bits, 0n, 0n, 0n, 0n, {==}, N.nl.le_zero(0n)), {==}, bf.cpl(bits, s2, l2, h2)))

def bf.h1_at(+bits: List<&2, Bool>, +rb: F.GpRun, +s: Nat, +l: Nat, +es: {F.genpool.fit.run_start(rb) == s : Nat}, +h1: {Laws.bf.maximal(bits, s, l) == True{} : Bool}) -> {Laws.bf.maximal(bits, F.genpool.fit.run_start(rb), l) == True{} : Bool}:
  Equal.trans(Bool, Laws.bf.maximal(bits, F.genpool.fit.run_start(rb), l), Laws.bf.maximal(bits, s, l), True{}, Equal.cong(Nat, Bool, z => Laws.bf.maximal(bits, z, l), F.genpool.fit.run_start(rb), s, es), h1)

# a maximal run at the start of the chosen one is the chosen one
def bf.len_of(+bits: List<&2, Bool>, +n: Nat, +rb: F.GpRun, +s: Nat, +l: Nat, +hm: {bf.res(bits, n) == Some{rb} : Maybe<&2, F.GpRun>}, +es: {F.genpool.fit.run_start(rb) == s : Nat}, +h1: {Laws.bf.maximal(bits, s, l) == True{} : Bool}) -> {F.genpool.fit.run_len(rb) == l : Nat}:
  bf.antisym(F.genpool.fit.run_len(rb), l, bf.u(bits, F.genpool.fit.run_start(rb), F.genpool.fit.run_len(rb), l, bf.mx_rf(bits, F.genpool.fit.run_start(rb), F.genpool.fit.run_len(rb), bf.chosen(bits, n, rb, hm)), bf.mx_pos(bits, F.genpool.fit.run_start(rb), F.genpool.fit.run_len(rb), bf.chosen(bits, n, rb, hm)), bf.mx_right(bits, F.genpool.fit.run_start(rb), l, bf.h1_at(bits, rb, s, l, es, h1))), bf.u(bits, F.genpool.fit.run_start(rb), l, F.genpool.fit.run_len(rb), bf.mx_rf(bits, F.genpool.fit.run_start(rb), l, bf.h1_at(bits, rb, s, l, es, h1)), bf.mx_pos(bits, F.genpool.fit.run_start(rb), l, bf.h1_at(bits, rb, s, l, es, h1)), bf.mx_right(bits, F.genpool.fit.run_start(rb), F.genpool.fit.run_len(rb), bf.chosen(bits, n, rb, hm))))

def bf.lfree(m: Maybe<&2, F.GpRun>, +bits: List<&2, Bool>, +n: Nat, +s: Nat, +hm: {bf.res(bits, n) == m : Maybe<&2, F.GpRun>}, e: {Maybe.map(&2, F.GpRun, Nat, r => F.genpool.fit.run_start(r), m) == Some{s} : Maybe<&2, Nat>}) -> {Bits.genpool.bits.run_free(bits, s, n) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Bits.genpool.bits.run_free(bits, s, n) == True{} : Bool}, pf.ns(s, e))
    case Some{+rb}:
      %pf.some_inj(F.genpool.fit.run_start(rb), s, e) : {Bits.genpool.bits.run_free(bits, _, n) == True{} : Bool}
      bf.fp_prefix(List.drop(&2, Bool, bits, F.genpool.fit.run_start(rb)), F.genpool.fit.run_len(rb), n, bf.mx_rf(bits, F.genpool.fit.run_start(rb), F.genpool.fit.run_len(rb), bf.chosen(bits, n, rb, hm)), N.nl.and_r(bf.memr(F.genpool.fit.runs(bits), F.genpool.fit.run_start(rb), F.genpool.fit.run_len(rb)), Nat.is_le(n, F.genpool.fit.run_len(rb)), bf.pfit_of(bits, n, rb, hm)))

def bf.lstart(m: Maybe<&2, F.GpRun>, +bits: List<&2, Bool>, +n: Nat, +s: Nat, +hm: {bf.res(bits, n) == m : Maybe<&2, F.GpRun>}, e: {Maybe.map(&2, F.GpRun, Nat, r => F.genpool.fit.run_start(r), m) == Some{s} : Maybe<&2, Nat>}) -> {Laws.bf.left(bits, s) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Laws.bf.left(bits, s) == True{} : Bool}, pf.ns(s, e))
    case Some{+rb}:
      %pf.some_inj(F.genpool.fit.run_start(rb), s, e) : {Laws.bf.left(bits, _) == True{} : Bool}
      bf.mx_left(bits, F.genpool.fit.run_start(rb), F.genpool.fit.run_len(rb), bf.chosen(bits, n, rb, hm))

def bf.lshort(m: Maybe<&2, F.GpRun>, +bits: List<&2, Bool>, +n: Nat, +s: Nat, +l: Nat, +s2: Nat, +l2: Nat, +hm: {bf.res(bits, n) == m : Maybe<&2, F.GpRun>}, +e: {Maybe.map(&2, F.GpRun, Nat, r => F.genpool.fit.run_start(r), m) == Some{s} : Maybe<&2, Nat>}, +h1: {Laws.bf.maximal(bits, s, l) == True{} : Bool}, +h2: {Laws.bf.maximal(bits, s2, l2) == True{} : Bool}, +h3: {Nat.is_le(n, l2) == True{} : Bool}) -> {Nat.is_le(l, l2) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Nat.is_le(l, l2) == True{} : Bool}, pf.ns(s, e))
    case Some{+rb}:
      %bf.len_of(bits, n, rb, s, l, hm, pf.some_inj(F.genpool.fit.run_start(rb), s, e), h1) : {Nat.is_le(_, l2) == True{} : Bool}
      N.nl.and_l(Nat.is_le(F.genpool.fit.run_len(rb), l2), Bool.or(Bool.not(Nat.is_lt(s2, F.genpool.fit.run_start(rb))), Nat.is_lt(F.genpool.fit.run_len(rb), l2)), bf.good_le(n, rb, s2, l2, bf.good_of(bits, n, rb, s2, l2, hm, h2), h3))

def bf.lfirst(m: Maybe<&2, F.GpRun>, +bits: List<&2, Bool>, +n: Nat, +s: Nat, +l: Nat, +s2: Nat, +l2: Nat, +hm: {bf.res(bits, n) == m : Maybe<&2, F.GpRun>}, +e: {Maybe.map(&2, F.GpRun, Nat, r => F.genpool.fit.run_start(r), m) == Some{s} : Maybe<&2, Nat>}, +h1: {Laws.bf.maximal(bits, s, l) == True{} : Bool}, +h2: {Laws.bf.maximal(bits, s2, l2) == True{} : Bool}, +h3: {Nat.is_le(n, l2) == True{} : Bool}, +h4: {Nat.is_lt(s2, s) == True{} : Bool}) -> {Nat.is_lt(l, l2) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({Nat.is_lt(l, l2) == True{} : Bool}, pf.ns(s, e))
    case Some{+rb}:
      %bf.len_of(bits, n, rb, s, l, hm, pf.some_inj(F.genpool.fit.run_start(rb), s, e), h1) : {Nat.is_lt(_, l2) == True{} : Bool}
      bf.good_lt(n, rb, s2, l2, bf.good_of(bits, n, rb, s2, l2, hm, h2), h3, Equal.trans(Bool, Nat.is_lt(s2, F.genpool.fit.run_start(rb)), Nat.is_lt(s2, s), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(s2, z), F.genpool.fit.run_start(rb), s, pf.some_inj(F.genpool.fit.run_start(rb), s, e)), h4))

def bf.lnone(m: Maybe<&2, F.GpRun>, +bits: List<&2, Bool>, +n: Nat, +j: Nat, b: Bool, +hm: {bf.res(bits, n) == m : Maybe<&2, F.GpRun>}, +hb: {Bits.genpool.bits.run_free(bits, j, n) == b : Bool}, e: {Maybe.map(&2, F.GpRun, Nat, r => F.genpool.fit.run_start(r), m) == None{} : Maybe<&2, Nat>}, +hn: {Nat.is_lt(0n, n) == True{} : Bool}) -> {Bits.genpool.bits.run_free(bits, j, n) == False{} : Bool}:
  match m:
    case Some{rb}:
      Empty.absurd({Bits.genpool.bits.run_free(bits, j, n) == False{} : Bool}, pf.sn(F.genpool.fit.run_start(rb), e))
    case None{}:
      match b:
        case False{}:
          hb
        case True{}:
          Empty.absurd({Bits.genpool.bits.run_free(bits, j, n) == False{} : Bool}, N.nl.ft(Equal.trans(Bool, bf.issome(None{}), bf.issome(bf.res(bits, n)), True{}, Equal.cong(Maybe<&2, F.GpRun>, Bool, z => bf.issome(z), None{}, bf.res(bits, n), Equal.sym(Maybe<&2, F.GpRun>, bf.res(bits, n), None{}, hm)), bf.bs2(F.genpool.fit.runs(bits), n, Nat.is_le(n, F.genpool.fit.run_len(bf.hdr(F.genpool.fit.runs(bits)))), {==}, None{}, bf.afit(bits, bits, 0n, 0n, 0n, n, j, bf.drop0(bits), {==}, N.nl.le_zero(j), hb, hn, Nat.is_le(j, 0n), {==})))))

def Laws.best_fit_free(d, bits, n, base, g, s, e):
  bf.lfree(bf.res(bits, n), bits, n, s, {==}, e)

def Laws.best_fit_starts(d, bits, n, base, g, s, e):
  bf.lstart(bf.res(bits, n), bits, n, s, {==}, e)

def Laws.best_fit_shortest(d, bits, n, base, g, s, l, s2, l2, e, h1, h2, h3):
  bf.lshort(bf.res(bits, n), bits, n, s, l, s2, l2, {==}, e, h1, h2, h3)

def Laws.best_fit_first(d, bits, n, base, g, s, l, s2, l2, e, h1, h2, h3, h4):
  bf.lfirst(bf.res(bits, n), bits, n, s, l, s2, l2, {==}, e, h1, h2, h3, h4)

def Laws.best_fit_none(d, bits, n, base, g, j, e, hn):
  bf.lnone(bf.res(bits, n), bits, n, j, Bits.genpool.bits.run_free(bits, j, n), {==}, {==}, e, hn)
