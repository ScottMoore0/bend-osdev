import Base
import ./bits.bend as Bits
import ./genalloc.bend as G
import ./fit.bend as F
import ./proof_nat.bend as N
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
