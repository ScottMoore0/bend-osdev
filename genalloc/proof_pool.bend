# Proof helpers for bend-osdev-genalloc: what a plan of the fit algorithm
# guarantees once the pool has checked it, how marking a run changes the
# chunks, and how genpool.free finds the chunk of an address.
import Base
import ./bits.bend as Bits
import ./genalloc.bend as G
import ./proof_nat.bend as N
import ./proof_bits.bend as PB
import ../u32/LAWS.bend as UL
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF.bend as UP
import ../u32/PROOF_order.bend as UOP

# A checked plan: chunk k holds address b and a free run of n at s

def pp.valid_at(cs: List<&2, G.GpChunk>, k: Nat, +s: Nat, +b: Nat, +n: Nat) -> Bool:
  match cs k:
    case Nil{} _:
      False{}
    case Con{+h, t} 0n:
      Bool.and(Nat.is_eq(G.genpool.chunk.addr(h), b), Bits.genpool.bits.run_free(G.genpool.chunk.used(h), s, n))
    case Con{h, t} 1n+i:
      pp.valid_at(t, i, s, b, n)

# a plan result is a failure, or a checked plan at index off or later
def pp.okp(cs: List<&2, G.GpChunk>, +off: Nat, +n: Nat, r: Result<&2, &2, G.GpError, G.GpPlan>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{G.GpPlan{+c, +s, +b}}:
      Bool.and(Nat.is_le(off, c), pp.valid_at(cs, Nat.sub(c, off), s, b, n))

def pp.shift(+x: G.GpChunk, +l: List<&2, G.GpChunk>, +c: Nat, +n: Nat, r: Result<&2, &2, G.GpError, G.GpPlan>, +h: {pp.okp(l, 1n+c, n, r) == True{} : Bool}) -> {pp.okp(Con{x, l}, c, n, r) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{G.GpPlan{c2, +s, +b}}:
      match c2:
        case 0n:
          Empty.absurd({pp.okp(Con{x, l}, c, n, Done{G.GpPlan{0n, s, b}}) == True{} : Bool}, N.nl.ft(N.nl.and_l(Nat.is_le(1n+c, 0n), pp.valid_at(l, Nat.sub(0n, 1n+c), s, b, n), h)))
        case 1n+ +d:
          +hle = N.nl.and_l(Nat.is_le(c, d), pp.valid_at(l, Nat.sub(d, c), s, b, n), h)
          %Equal.sym(Nat, Nat.sub(1n+d, c), 1n+Nat.sub(d, c), N.nl.sub_succ(d, c, hle)) : {Bool.and(Nat.is_le(c, 1n+d), pp.valid_at(Con{x, l}, _, s, b, n)) == True{} : Bool}
          N.nl.and_i(Nat.is_le(c, 1n+d), pp.valid_at(l, Nat.sub(d, c), s, b, n), UO.nat_le_trans(c, d, 1n+d, hle, N.nl.le_succ(d)), N.nl.and_r(Nat.is_le(c, d), pp.valid_at(l, Nat.sub(d, c), s, b, n), h))

def pp.pc(ok: Bool, +ch: G.GpChunk, +r: List<&2, G.GpChunk>, +c: Nat, +s: Nat, +n: Nat, +eok: {Bits.genpool.bits.run_free(G.genpool.chunk.used(ch), s, n) == ok : Bool}) -> {pp.okp(Con{ch, r}, c, n, G.genpool.plan.check(ok, c, s, G.genpool.chunk.addr(ch))) == True{} : Bool}:
  match ok:
    case True{}:
      %Equal.sym(Nat, Nat.sub(c, c), 0n, N.nl.sub_self(c)) : {Bool.and(Nat.is_le(c, c), pp.valid_at(Con{ch, r}, _, s, G.genpool.chunk.addr(ch), n)) == True{} : Bool}
      N.nl.and_i(Nat.is_le(c, c), pp.valid_at(Con{ch, r}, 0n, s, G.genpool.chunk.addr(ch), n), UL.nat_le_refl(c), N.nl.and_i(Nat.is_eq(G.genpool.chunk.addr(ch), G.genpool.chunk.addr(ch)), Bits.genpool.bits.run_free(G.genpool.chunk.used(ch), s, n), N.nl.eq_refl(G.genpool.chunk.addr(ch)), eok))
    case False{}:
      {==}

def pp.plan_go(~fit: G.GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>, +rest: List<&2, G.GpChunk>, m: Maybe<&2, Nat>, +ch: G.GpChunk, +n: Nat, +data: G.GpFitData, +g: Nat, +c: Nat) -> {pp.okp(Con{ch, rest}, c, n, G.genpool.plan.go(~fit, rest, m, ch, n, data, g, c)) == True{} : Bool}:
  match rest m:
    case +r Some{+s}:
      pp.pc(Bits.genpool.bits.run_free(G.genpool.chunk.used(ch), s, n), ch, r, c, s, n, {==})
    case Nil{} None{}:
      {==}
    case Con{+h, +t} None{}:
      pp.shift(ch, Con{h, t}, c, n, G.genpool.plan.go(~fit, t, fit(data, G.genpool.chunk.used(h), n, G.genpool.chunk.addr(h), g), h, n, data, g, 1n+c), pp.plan_go(~fit, t, fit(data, G.genpool.chunk.used(h), n, G.genpool.chunk.addr(h), g), h, n, data, g, 1n+c))

def pp.plan(~fit: G.GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>, +cs: List<&2, G.GpChunk>, +n: Nat, +data: G.GpFitData, +g: Nat) -> {pp.okp(cs, 0n, n, G.genpool.plan(~fit, cs, n, data, g)) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      pp.plan_go(~fit, t, fit(data, G.genpool.chunk.used(h), n, G.genpool.chunk.addr(h), g), h, n, data, g, 0n)

def pp.va_of(+cs: List<&2, G.GpChunk>, +c: Nat, +s: Nat, +b: Nat, +n: Nat, +h: {pp.okp(cs, 0n, n, Done{G.GpPlan{c, s, b}}) == True{} : Bool}) -> {pp.valid_at(cs, c, s, b, n) == True{} : Bool}:
  %N.nl.sub_zero(c) : {pp.valid_at(cs, _, s, b, n) == True{} : Bool}
  N.nl.and_r(Nat.is_le(0n, c), pp.valid_at(cs, Nat.sub(c, 0n), s, b, n), h)

# What a checked plan says about its chunk

def pp.va_len(cs: List<&2, G.GpChunk>, k: Nat, +s: Nat, +b: Nat, +n: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +hv: {pp.valid_at(cs, k, s, b, n) == True{} : Bool}) -> {Nat.is_le(Nat.add(s, n), Maybe.default(&2, Nat, Maybe.map(&2, G.GpChunk, Nat, h => List.length(&2, Bool, G.genpool.chunk.used(h)), List.get(&2, G.GpChunk, cs, k)), 0n)) == True{} : Bool}:
  match cs k:
    case Nil{} _:
      Empty.absurd({Nat.is_le(Nat.add(s, n), 0n) == True{} : Bool}, N.nl.ft(hv))
    case Con{+h, t} 0n:
      PB.pb.rf_len(G.genpool.chunk.used(h), s, n, hn, N.nl.and_r(Nat.is_eq(G.genpool.chunk.addr(h), b), Bits.genpool.bits.run_free(G.genpool.chunk.used(h), s, n), hv))
    case Con{h, t} 1n+i:
      pp.va_len(t, i, s, b, n, hn, hv)

def pp.va_addr(cs: List<&2, G.GpChunk>, k: Nat, +s: Nat, +b: Nat, +n: Nat, +hv: {pp.valid_at(cs, k, s, b, n) == True{} : Bool}) -> {Maybe.default(&2, Nat, Maybe.map(&2, G.GpChunk, Nat, h => G.genpool.chunk.addr(h), List.get(&2, G.GpChunk, cs, k)), 0n) == b : Nat}:
  match cs k:
    case Nil{} _:
      Empty.absurd({0n == b : Nat}, N.nl.ft(hv))
    case Con{+h, t} 0n:
      N.nl.eq(G.genpool.chunk.addr(h), b, N.nl.and_l(Nat.is_eq(G.genpool.chunk.addr(h), b), Bits.genpool.bits.run_free(G.genpool.chunk.used(h), s, n), hv))
    case Con{h, t} 1n+i:
      pp.va_addr(t, i, s, b, n, hv)

def pp.va_free(cs: List<&2, G.GpChunk>, k: Nat, +s: Nat, +b: Nat, +n: Nat, +j: Nat, +hv: {pp.valid_at(cs, k, s, b, n) == True{} : Bool}, +l: {Nat.is_le(s, j) == True{} : Bool}, +m: {Nat.is_lt(j, Nat.add(s, n)) == True{} : Bool}) -> {G.genpool.used_at.go(List.get(&2, G.GpChunk, cs, k), j) == False{} : Bool}:
  match cs k:
    case Nil{} _:
      {==}
    case Con{+h, t} 0n:
      PB.pb.rf_get(G.genpool.chunk.used(h), s, n, j, N.nl.and_r(Nat.is_eq(G.genpool.chunk.addr(h), b), Bits.genpool.bits.run_free(G.genpool.chunk.used(h), s, n), hv), l, m)
    case Con{h, t} 1n+i:
      pp.va_free(t, i, s, b, n, j, hv, l, m)

# Marking a run

def pp.mark_in(cs: List<&2, G.GpChunk>, k: Nat, +s: Nat, +b: Nat, +n: Nat, +j: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +hv: {pp.valid_at(cs, k, s, b, n) == True{} : Bool}, +l: {Nat.is_le(s, j) == True{} : Bool}, +m: {Nat.is_lt(j, Nat.add(s, n)) == True{} : Bool}) -> {G.genpool.used_at.go(List.get(&2, G.GpChunk, G.genpool.mark(cs, k, s, n, True{}), k), j) == True{} : Bool}:
  match cs k:
    case Nil{} _:
      Empty.absurd({False{} == True{} : Bool}, N.nl.ft(hv))
    case Con{G.GpChunk{+a, +u}, t} 0n:
      +hr = N.nl.and_r(Nat.is_eq(a, b), Bits.genpool.bits.run_free(u, s, n), hv)
      PB.pb.fill_get_in(u, s, n, j, True{}, l, m, UO.nat_lt_le_trans(j, Nat.add(s, n), List.length(&2, Bool, u), m, PB.pb.rf_len(u, s, n, hn, hr)))
    case Con{h, t} 1n+i:
      pp.mark_in(t, i, s, b, n, j, hn, hv, l, m)

def pp.mark_out(cs: List<&2, G.GpChunk>, k: Nat, c2: Nat, +s: Nat, +n: Nat, +v: Bool, +j: Nat, +o: {Bool.and(Nat.is_eq(c2, k), Bool.and(Nat.is_le(s, j), Nat.is_lt(j, Nat.add(s, n)))) == False{} : Bool}) -> {G.genpool.used_at.go(List.get(&2, G.GpChunk, G.genpool.mark(cs, k, s, n, v), c2), j) == G.genpool.used_at.go(List.get(&2, G.GpChunk, cs, c2), j) : Bool}:
  match cs k c2:
    case Nil{} _ _:
      {==}
    case Con{G.GpChunk{a, +u}, t} 0n 0n:
      PB.pb.fill_get_out(u, s, n, j, v, o)
    case Con{G.GpChunk{a, u}, t} 0n 1n+d:
      {==}
    case Con{h, t} 1n+i 0n:
      {==}
    case Con{h, t} 1n+i 1n+d:
      pp.mark_out(t, i, d, s, n, v, j, o)

def pp.mark_blank(cs: List<&2, G.GpChunk>, k: Nat, +s: Nat, +n: Nat, +v: Bool) -> {G.genpool.blank.go(G.genpool.mark(cs, k, s, n, v)) == G.genpool.blank.go(cs) : List<&2, G.GpChunk>}:
  match cs k:
    case Nil{} _:
      {==}
    case Con{G.GpChunk{+a, +u}, +t} 0n:
      %Equal.sym(Nat, List.length(&2, Bool, Bits.genpool.bits.fill(u, s, n, v)), List.length(&2, Bool, u), PB.pb.fill_len(u, s, n, v)) : {Con{G.GpChunk{a, List.replicate(Bool, _, False{})}, G.genpool.blank.go(t)} == Con{G.GpChunk{a, List.replicate(Bool, List.length(&2, Bool, u), False{})}, G.genpool.blank.go(t)} : List<&2, G.GpChunk>}
      {==}
    case Con{G.GpChunk{+a, +u}, +t} 1n+ +i:
      %pp.mark_blank(t, i, s, n, v) : {Con{G.GpChunk{a, List.replicate(Bool, List.length(&2, Bool, u), False{})}, G.genpool.blank.go(G.genpool.mark(t, i, s, n, v))} == Con{G.GpChunk{a, List.replicate(Bool, List.length(&2, Bool, u), False{})}, _} : List<&2, G.GpChunk>}
      {==}

# the free granules after marking a free run of n as allocated: n fewer
def pp.cf_fp(v: List<&2, Bool>, n: Nat, +h: {Bits.genpool.bits.free_prefix(v, n) == True{} : Bool}) -> {Nat.add(Bits.genpool.bits.count_free(Bits.genpool.bits.fill_prefix(v, n, True{})), n) == Bits.genpool.bits.count_free(v) : Nat}:
  match v n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+m:
      Empty.absurd({Nat.add(0n, 1n+m) == 0n : Nat}, N.nl.ft(h))
    case Con{+b, +t} 0n:
      UL.nat_add_zero(Bits.genpool.bits.count_free(Con{b, t}))
    case Con{+b, +t} 1n+ +m:
      %Equal.sym(Bool, b, False{}, PB.pb.not_t(b, N.nl.and_l(Bool.not(b), Bits.genpool.bits.free_prefix(t, m), h))) : {Nat.add(Bits.genpool.bits.count_free(Bits.genpool.bits.fill_prefix(t, m, True{})), 1n+m) == Bits.genpool.bits.count_free(Con{_, t}) : Nat}
      %Equal.sym(Nat, Nat.add(Bits.genpool.bits.count_free(Bits.genpool.bits.fill_prefix(t, m, True{})), 1n+m), 1n+Nat.add(Bits.genpool.bits.count_free(Bits.genpool.bits.fill_prefix(t, m, True{})), m), UL.nat_add_succ(Bits.genpool.bits.count_free(Bits.genpool.bits.fill_prefix(t, m, True{})), m)) : {_ == 1n+Bits.genpool.bits.count_free(t) : Nat}
      %pp.cf_fp(t, m, N.nl.and_r(Bool.not(b), Bits.genpool.bits.free_prefix(t, m), h)) : {1n+Nat.add(Bits.genpool.bits.count_free(Bits.genpool.bits.fill_prefix(t, m, True{})), m) == 1n+_ : Nat}
      {==}

def pp.cf_fill(u: List<&2, Bool>, s: Nat, +n: Nat, +h: {Bits.genpool.bits.run_free(u, s, n) == True{} : Bool}) -> {Nat.add(Bits.genpool.bits.count_free(Bits.genpool.bits.fill(u, s, n, True{})), n) == Bits.genpool.bits.count_free(u) : Nat}:
  match u s:
    case Nil{} _:
      pp.cf_fp(Nil{}, n, h)
    case Con{+b, +t} 0n:
      pp.cf_fp(Con{b, t}, n, h)
    case Con{True{}, t} 1n+i:
      pp.cf_fill(t, i, n, h)
    case Con{False{}, t} 1n+i:
      %pp.cf_fill(t, i, n, h) : {1n+Nat.add(Bits.genpool.bits.count_free(Bits.genpool.bits.fill(t, i, n, True{})), n) == 1n+_ : Nat}
      {==}

# (x + y) + n = (x + n) + y
def pp.add_rc(+x: Nat, +y: Nat, +n: Nat) -> {Nat.add(Nat.add(x, y), n) == Nat.add(Nat.add(x, n), y) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(x, y), n), Nat.add(x, Nat.add(y, n)), UL.nat_add_assoc(x, y, n)) : {_ == Nat.add(Nat.add(x, n), y) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(x, n), y), Nat.add(x, Nat.add(n, y)), UL.nat_add_assoc(x, n, y)) : {Nat.add(x, Nat.add(y, n)) == _ : Nat}
  %UL.nat_add_comm(y, n) : {Nat.add(x, Nat.add(y, n)) == Nat.add(x, _) : Nat}
  {==}

def pp.cf_mark(cs: List<&2, G.GpChunk>, k: Nat, +s: Nat, +b: Nat, +n: Nat, +hv: {pp.valid_at(cs, k, s, b, n) == True{} : Bool}) -> {Nat.add(G.genpool.count_free.go(G.genpool.mark(cs, k, s, n, True{})), n) == G.genpool.count_free.go(cs) : Nat}:
  match cs k:
    case Nil{} _:
      Empty.absurd({Nat.add(0n, n) == 0n : Nat}, N.nl.ft(hv))
    case Con{G.GpChunk{+a, +u}, +t} 0n:
      +f = Bits.genpool.bits.count_free(Bits.genpool.bits.fill(u, s, n, True{}))
      %Equal.sym(Nat, Nat.add(Nat.add(f, G.genpool.count_free.go(t)), n), Nat.add(Nat.add(f, n), G.genpool.count_free.go(t)), pp.add_rc(f, G.genpool.count_free.go(t), n)) : {_ == Nat.add(Bits.genpool.bits.count_free(u), G.genpool.count_free.go(t)) : Nat}
      %pp.cf_fill(u, s, n, N.nl.and_r(Nat.is_eq(a, b), Bits.genpool.bits.run_free(u, s, n), hv)) : {Nat.add(Nat.add(f, n), G.genpool.count_free.go(t)) == Nat.add(_, G.genpool.count_free.go(t)) : Nat}
      {==}
    case Con{+h, +t} 1n+ +i:
      +f = Bits.genpool.bits.count_free(G.genpool.chunk.used(h))
      %Equal.sym(Nat, Nat.add(Nat.add(f, G.genpool.count_free.go(G.genpool.mark(t, i, s, n, True{}))), n), Nat.add(f, Nat.add(G.genpool.count_free.go(G.genpool.mark(t, i, s, n, True{})), n)), UL.nat_add_assoc(f, G.genpool.count_free.go(G.genpool.mark(t, i, s, n, True{})), n)) : {_ == Nat.add(f, G.genpool.count_free.go(t)) : Nat}
      %pp.cf_mark(t, i, s, b, n, hv) : {Nat.add(f, Nat.add(G.genpool.count_free.go(G.genpool.mark(t, i, s, n, True{})), n)) == Nat.add(f, _) : Nat}
      {==}

# Finding the chunk of an address

def pp.inside_at(cs: List<&2, G.GpChunk>, k: Nat, +a: Nat, +g: Nat) -> Bool:
  match cs k:
    case Nil{} _:
      False{}
    case Con{+h, t} 0n:
      G.genpool.inside(h, a, g)
    case Con{h, t} 1n+i:
      pp.inside_at(t, i, a, g)

# the address of granule s of a checked plan's chunk lies in that chunk
def pp.va_inside(cs: List<&2, G.GpChunk>, k: Nat, +s: Nat, +b: Nat, +n: Nat, +g: Nat, +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +hv: {pp.valid_at(cs, k, s, b, n) == True{} : Bool}) -> {pp.inside_at(cs, k, Nat.add(b, Nat.mul(s, g)), g) == True{} : Bool}:
  match cs k:
    case Nil{} _:
      Empty.absurd({False{} == True{} : Bool}, N.nl.ft(hv))
    case Con{G.GpChunk{+a0, +u}, t} 0n:
      +hr = N.nl.and_r(Nat.is_eq(a0, b), Bits.genpool.bits.run_free(u, s, n), hv)
      +hs = UO.nat_lt_le_trans(s, Nat.add(s, n), List.length(&2, Bool, u), N.nl.lt_add(s, n, hn), PB.pb.rf_len(u, s, n, hn, hr))
      %N.nl.eq(a0, b, N.nl.and_l(Nat.is_eq(a0, b), Bits.genpool.bits.run_free(u, s, n), hv)) : {G.genpool.inside(G.GpChunk{a0, u}, Nat.add(_, Nat.mul(s, g)), g) == True{} : Bool}
      N.nl.and_i(Nat.is_le(a0, Nat.add(a0, Nat.mul(s, g))), Nat.is_lt(Nat.add(a0, Nat.mul(s, g)), Nat.add(a0, Nat.mul(List.length(&2, Bool, u), g))), UO.nat_le_add_r(a0, Nat.mul(s, g)), N.nl.lt_add_l(a0, Nat.mul(s, g), Nat.mul(List.length(&2, Bool, u), g), N.nl.lt_mul(s, List.length(&2, Bool, u), g, hs, hg)))
    case Con{h, t} 1n+i:
      pp.va_inside(t, i, s, b, n, g, hg, hn, hv)

def pp.and_ff(x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def pp.lt_nle(a: Nat, b: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case _ 0n:
      Empty.absurd({Nat.is_le(0n, a) == False{} : Bool}, N.nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(a, 0n), True{}, Equal.sym(Bool, Nat.is_lt(a, 0n), False{}, N.nl.lt0(a)), e)))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      pp.lt_nle(ap, bp, e)

# a in [b2, e2), which [b, e) is apart from: a is not in [b, e)
def pp.apart1(x: Bool, +b: Nat, +e: Nat, +b2: Nat, +e2: Nat, +a: Nat, +ex: {Nat.is_le(e, b2) == x : Bool}, +ap: {Bool.or(x, Nat.is_le(e2, b)) == True{} : Bool}, +hl: {Nat.is_le(b2, a) == True{} : Bool}, +hr: {Nat.is_lt(a, e2) == True{} : Bool}) -> {Bool.and(Nat.is_le(b, a), Nat.is_lt(a, e)) == False{} : Bool}:
  match x:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(a, e), False{}, N.nl.le_nlt(e, a, UO.nat_le_trans(e, b2, a, ex, hl))) : {Bool.and(Nat.is_le(b, a), _) == False{} : Bool}
      pp.and_ff(Nat.is_le(b, a))
    case False{}:
      %Equal.sym(Bool, Nat.is_le(b, a), False{}, pp.lt_nle(a, b, UO.nat_lt_le_trans(a, e2, b, hr, ap))) : {Bool.and(_, Nat.is_lt(a, e)) == False{} : Bool}
      {==}

def pp.apart_out(+b: Nat, +e: Nat, cs: List<&2, G.GpChunk>, k: Nat, +a: Nat, +g: Nat, +hap: {G.genpool.apart_all(b, e, cs, g) == True{} : Bool}, +hin: {pp.inside_at(cs, k, a, g) == True{} : Bool}) -> {Bool.and(Nat.is_le(b, a), Nat.is_lt(a, e)) == False{} : Bool}:
  match cs k:
    case Nil{} _:
      Empty.absurd({Bool.and(Nat.is_le(b, a), Nat.is_lt(a, e)) == False{} : Bool}, N.nl.ft(hin))
    case Con{+h, +t} 0n:
      +b2 = G.genpool.chunk.addr(h)
      +e2 = G.genpool.chunk.end(h, g)
      pp.apart1(Nat.is_le(e, b2), b, e, b2, e2, a, {==}, N.nl.and_l(G.genpool.apart(b, e, b2, e2), G.genpool.apart_all(b, e, t, g), hap), N.nl.and_l(Nat.is_le(b2, a), Nat.is_lt(a, e2), hin), N.nl.and_r(Nat.is_le(b2, a), Nat.is_lt(a, e2), hin))
    case Con{+h, +t} 1n+i:
      pp.apart_out(b, e, t, i, a, g, N.nl.and_r(G.genpool.apart(b, e, G.genpool.chunk.addr(h), G.genpool.chunk.end(h, g)), G.genpool.apart_all(b, e, t, g), hap), hin)

# on disjoint chunks, the first chunk holding an address is the one that
# holds it
def pp.locate_hit(cs: List<&2, G.GpChunk>, k: Nat, +a: Nat, +g: Nat, +i: Nat, +hd: {G.genpool.disjoint.go(cs, g) == True{} : Bool}, +hin: {pp.inside_at(cs, k, a, g) == True{} : Bool}) -> {G.genpool.locate(cs, a, g, i) == Some{Nat.add(k, i)} : Maybe<&2, Nat>}:
  match cs k:
    case Nil{} _:
      Empty.absurd({None{} == Some{Nat.add(k, i)} : Maybe<&2, Nat>}, N.nl.ft(hin))
    case Con{+h, +t} 0n:
      %Equal.sym(Bool, G.genpool.inside(h, a, g), True{}, hin) : {G.genpool.locate.pick(_, i, G.genpool.locate(t, a, g, 1n+i)) == Some{i} : Maybe<&2, Nat>}
      {==}
    case Con{+h, +t} 1n+ +j:
      +out = pp.apart_out(G.genpool.chunk.addr(h), G.genpool.chunk.end(h, g), t, j, a, g, N.nl.and_l(G.genpool.apart_all(G.genpool.chunk.addr(h), G.genpool.chunk.end(h, g), t, g), G.genpool.disjoint.go(t, g), hd), hin)
      %Equal.sym(Bool, G.genpool.inside(h, a, g), False{}, out) : {G.genpool.locate.pick(_, i, G.genpool.locate(t, a, g, 1n+i)) == Some{1n+Nat.add(j, i)} : Maybe<&2, Nat>}
      Equal.trans(Maybe<&2, Nat>, G.genpool.locate(t, a, g, 1n+i), Some{Nat.add(j, 1n+i)}, Some{1n+Nat.add(j, i)}, pp.locate_hit(t, j, a, g, 1n+i, N.nl.and_r(G.genpool.apart_all(G.genpool.chunk.addr(h), G.genpool.chunk.end(h, g), t, g), G.genpool.disjoint.go(t, g), hd), hin), Equal.cong(Nat, Maybe<&2, Nat>, z => Some{z}, Nat.add(j, 1n+i), 1n+Nat.add(j, i), UL.nat_add_succ(j, i)))

# marking a run changes no chunk's address or length
def pp.locate_mark(cs: List<&2, G.GpChunk>, k: Nat, +s: Nat, +n: Nat, +v: Bool, +a: Nat, +g: Nat, +i: Nat) -> {G.genpool.locate(G.genpool.mark(cs, k, s, n, v), a, g, i) == G.genpool.locate(cs, a, g, i) : Maybe<&2, Nat>}:
  match cs k:
    case Nil{} _:
      {==}
    case Con{G.GpChunk{+a0, +u}, +t} 0n:
      %Equal.sym(Nat, List.length(&2, Bool, Bits.genpool.bits.fill(u, s, n, v)), List.length(&2, Bool, u), PB.pb.fill_len(u, s, n, v)) : {G.genpool.locate.pick(Bool.and(Nat.is_le(a0, a), Nat.is_lt(a, Nat.add(a0, Nat.mul(_, g)))), i, G.genpool.locate(t, a, g, 1n+i)) == G.genpool.locate(Con{G.GpChunk{a0, u}, t}, a, g, i) : Maybe<&2, Nat>}
      {==}
    case Con{+h, +t} 1n+ +j:
      %pp.locate_mark(t, j, s, n, v, a, g, 1n+i) : {G.genpool.locate.pick(G.genpool.inside(h, a, g), i, G.genpool.locate(G.genpool.mark(t, j, s, n, v), a, g, 1n+i)) == G.genpool.locate.pick(G.genpool.inside(h, a, g), i, _) : Maybe<&2, Nat>}
      {==}

# Freeing what a checked plan marked gives the chunks back

def pp.free_mark(cs: List<&2, G.GpChunk>, k: Nat, +s: Nat, +b: Nat, +n: Nat, +g: Nat, +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +hv: {pp.valid_at(cs, k, s, b, n) == True{} : Bool}) -> {G.genpool.free.at(G.genpool.mark(cs, k, s, n, True{}), k, Nat.add(b, Nat.mul(s, g)), n, g) == Done{cs} : Result<&2, &2, G.GpError, List<&2, G.GpChunk>>}:
  match cs k:
    case Nil{} _:
      Empty.absurd({Fail{G.GpNotInPool{}} == Done{Nil{}} : Result<&2, &2, G.GpError, List<&2, G.GpChunk>>}, N.nl.ft(hv))
    case Con{G.GpChunk{+a0, +u}, +t} 0n:
      +hr = N.nl.and_r(Nat.is_eq(a0, b), Bits.genpool.bits.run_free(u, s, n), hv)
      %N.nl.eq(a0, b, N.nl.and_l(Nat.is_eq(a0, b), Bits.genpool.bits.run_free(u, s, n), hv)) : {G.genpool.free.chunk(a0, G.genpool.free.walk(Bits.genpool.bits.fill(u, s, n, True{}), Nat.is_eq(a0, Nat.add(_, Nat.mul(s, g))), Nat.is_lt(Nat.add(_, Nat.mul(s, g)), a0), a0, Nat.add(_, Nat.mul(s, g)), g, n), t) == Done{Con{G.GpChunk{a0, u}, t}} : Result<&2, &2, G.GpError, List<&2, G.GpChunk>>}
      %Equal.sym(Result<&2, &2, G.GpError, List<&2, Bool>>, G.genpool.free.walk(Bits.genpool.bits.fill(u, s, n, True{}), Nat.is_eq(a0, Nat.add(a0, Nat.mul(s, g))), Nat.is_lt(Nat.add(a0, Nat.mul(s, g)), a0), a0, Nat.add(a0, Nat.mul(s, g)), g, n), Done{u}, PB.pb.free_fill(u, s, a0, g, n, hg, hn, hr)) : {G.genpool.free.chunk(a0, _, t) == Done{Con{G.GpChunk{a0, u}, t}} : Result<&2, &2, G.GpError, List<&2, G.GpChunk>>}
      {==}
    case Con{+h, +t} 1n+ +j:
      %Equal.sym(Result<&2, &2, G.GpError, List<&2, G.GpChunk>>, G.genpool.free.at(G.genpool.mark(t, j, s, n, True{}), j, Nat.add(b, Nat.mul(s, g)), n, g), Done{t}, pp.free_mark(t, j, s, b, n, g, hg, hn, hv)) : {G.genpool.free.ccons(h, _) == Done{Con{h, t}} : Result<&2, &2, G.GpError, List<&2, G.GpChunk>>}
      {==}
