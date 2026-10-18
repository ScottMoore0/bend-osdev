import Base
import ./bits.bend as Bits
import ./genalloc.bend as G
import ./fit.bend as F
import ./proof_nat.bend as N
import ./proof_bits.bend as PB
import ./proof_pool.bend as PP
import ./LAWS.bend as Laws

# Sizes: each granule is free or allocated

def gl.count_bits(+u: List<&2, Bool>) -> {Nat.add(Bits.genpool.bits.count_free(u), Bits.genpool.bits.count_used(u)) == List.length(&2, Bool, u) : Nat}:
  match u:
    case Nil{}:
      {==}
    case Con{True{}, t}:
      %Equal.sym(Nat, Nat.add(Bits.genpool.bits.count_free(t), 1n+Bits.genpool.bits.count_used(t)), 1n+Nat.add(Bits.genpool.bits.count_free(t), Bits.genpool.bits.count_used(t)), N.nl.add_succ(Bits.genpool.bits.count_free(t), Bits.genpool.bits.count_used(t))) : {_ == 1n+List.length(&2, Bool, t) : Nat}
      %gl.count_bits(t) : {1n+Nat.add(Bits.genpool.bits.count_free(t), Bits.genpool.bits.count_used(t)) == 1n+_ : Nat}
      {==}
    case Con{False{}, t}:
      %gl.count_bits(t) : {1n+Nat.add(Bits.genpool.bits.count_free(t), Bits.genpool.bits.count_used(t)) == 1n+_ : Nat}
      {==}

def gl.count_go(+cs: List<&2, G.GpChunk>) -> {Nat.add(G.genpool.count_free.go(cs), G.genpool.count_used.go(cs)) == G.genpool.count.go(cs) : Nat}:
  match cs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +f1 = Bits.genpool.bits.count_free(G.genpool.chunk.used(h))
      +u1 = Bits.genpool.bits.count_used(G.genpool.chunk.used(h))
      %Equal.sym(Nat, Nat.add(Nat.add(f1, G.genpool.count_free.go(t)), Nat.add(u1, G.genpool.count_used.go(t))), Nat.add(Nat.add(f1, u1), Nat.add(G.genpool.count_free.go(t), G.genpool.count_used.go(t))), N.nl.swap4(f1, G.genpool.count_free.go(t), u1, G.genpool.count_used.go(t))) : {_ == G.genpool.count.go(Con{h, t}) : Nat}
      %gl.count_bits(G.genpool.chunk.used(h)) : {Nat.add(Nat.add(f1, u1), Nat.add(G.genpool.count_free.go(t), G.genpool.count_used.go(t))) == Nat.add(_, G.genpool.count.go(t)) : Nat}
      %gl.count_go(t) : {Nat.add(Nat.add(f1, u1), Nat.add(G.genpool.count_free.go(t), G.genpool.count_used.go(t))) == Nat.add(Nat.add(f1, u1), _) : Nat}
      {==}

def Laws.avail_size(p):
  match p:
    case G.GpPool{o, +g, +cs}:
      %N.nl.mul_add(G.genpool.count_free.go(cs), G.genpool.count_used.go(cs), g) : {_ == Nat.mul(G.genpool.count.go(cs), g) : Nat}
      %gl.count_go(cs) : {Nat.mul(Nat.add(G.genpool.count_free.go(cs), G.genpool.count_used.go(cs)), g) == Nat.mul(_, g) : Nat}
      {==}

# Allocation: what a Done answer says

def gl.rdisc(r: Result<&2, &2, G.GpError, G.GpAlloc>) -> Type:
  match r:
    case Fail{x}:
      Empty
    case Done{y}:
      Unit

def gl.fd(-x: G.GpError, -y: G.GpAlloc, e: {Fail{x} == Done{y} : Result<&2, &2, G.GpError, G.GpAlloc>}) -> Empty:
  %Equal.sym(Result<&2, &2, G.GpError, G.GpAlloc>, Fail{x}, Done{y}, e) : gl.rdisc(_)
  Unit{}

def gl.pdisc(r: Result<&2, &2, G.GpError, G.GpPool>) -> Type:
  match r:
    case Fail{x}:
      Empty
    case Done{y}:
      Unit

def gl.pfd(-x: G.GpError, -y: G.GpPool, e: {Fail{x} == Done{y} : Result<&2, &2, G.GpError, G.GpPool>}) -> Empty:
  %Equal.sym(Result<&2, &2, G.GpError, G.GpPool>, Fail{x}, Done{y}, e) : gl.pdisc(_)
  Unit{}

def gl.fq(r: Result<&2, &2, G.GpError, G.GpAlloc>) -> G.GpPool:
  match r:
    case Fail{x}:
      G.GpPool{0n, 0n, Nil{}}
    case Done{G.GpAlloc{q, a, c, s, n}}:
      q

def gl.fa(r: Result<&2, &2, G.GpError, G.GpAlloc>) -> Nat:
  match r:
    case Fail{x}:
      0n
    case Done{G.GpAlloc{q, a, c, s, n}}:
      a

def gl.fc(r: Result<&2, &2, G.GpError, G.GpAlloc>) -> Nat:
  match r:
    case Fail{x}:
      0n
    case Done{G.GpAlloc{q, a, c, s, n}}:
      c

def gl.fs(r: Result<&2, &2, G.GpError, G.GpAlloc>) -> Nat:
  match r:
    case Fail{x}:
      0n
    case Done{G.GpAlloc{q, a, c, s, n}}:
      s

def gl.fn(r: Result<&2, &2, G.GpError, G.GpAlloc>) -> Nat:
  match r:
    case Fail{x}:
      0n
    case Done{G.GpAlloc{q, a, c, s, n}}:
      n

def gl.fp(r: Result<&2, &2, G.GpError, G.GpPool>) -> G.GpPool:
  match r:
    case Fail{x}:
      G.GpPool{0n, 0n, Nil{}}
    case Done{q}:
      q

def gl.h_inside(r: Result<&2, &2, G.GpError, G.GpPlan>, +o: Nat, +g: Nat, +cs: List<&2, G.GpChunk>, +n0: Nat, -q: G.GpPool, -a: Nat, +c: Nat, +s: Nat, +n: Nat, +e: {G.genpool.alloc.apply(r, o, g, cs, n0) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}, +hr: {PP.pp.okp(cs, 0n, n0, r) == True{} : Bool}, +hn0: {Nat.is_lt(0n, n0) == True{} : Bool}) -> {Bool.and(Nat.is_lt(0n, n), Nat.is_le(Nat.add(s, n), G.genpool.chunk_granules(G.GpPool{o, g, cs}, c))) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({Bool.and(Nat.is_lt(0n, n), Nat.is_le(Nat.add(s, n), G.genpool.chunk_granules(G.GpPool{o, g, cs}, c))) == True{} : Bool}, gl.fd(x, G.GpAlloc{q, a, c, s, n}, e))
    case Done{G.GpPlan{+c1, +s1, +b1}}:
      +hv = PP.pp.va_of(cs, c1, s1, b1, n0, hr)
      %Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fc(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e) : {Bool.and(Nat.is_lt(0n, n), Nat.is_le(Nat.add(s, n), G.genpool.chunk_granules(G.GpPool{o, g, cs}, _))) == True{} : Bool}
      %Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fs(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e) : {Bool.and(Nat.is_lt(0n, n), Nat.is_le(Nat.add(_, n), G.genpool.chunk_granules(G.GpPool{o, g, cs}, c1))) == True{} : Bool}
      %Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fn(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e) : {Bool.and(Nat.is_lt(0n, _), Nat.is_le(Nat.add(s1, _), G.genpool.chunk_granules(G.GpPool{o, g, cs}, c1))) == True{} : Bool}
      N.nl.and_i(Nat.is_lt(0n, n0), Nat.is_le(Nat.add(s1, n0), G.genpool.chunk_granules(G.GpPool{o, g, cs}, c1)), hn0, PP.pp.va_len(cs, c1, s1, b1, n0, hn0, hv))

def Laws.alloc_inside(fit, p, size, data, q, a, c, s, n, e):
  match p size:
    case G.GpPool{o, g, cs} 0n:
      Empty.absurd({Bool.and(Nat.is_lt(0n, n), Nat.is_le(Nat.add(s, n), G.genpool.chunk_granules(G.GpPool{o, g, cs}, c))) == True{} : Bool}, gl.fd(G.GpBadSize{}, G.GpAlloc{q, a, c, s, n}, e))
    case G.GpPool{+o, +g, +cs} 1n+ +k:
      gl.h_inside(G.genpool.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), o, g, cs, G.genpool.granules_for(1n+k, g), q, a, c, s, n, e, PP.pp.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), N.nl.max1(Nat.div(Nat.add(1n+k, Nat.sub(g, 1n)), g)))

# moving hypotheses across the equalities an allocation gives

def gl.tr_le(-x: Nat, -y: Nat, -j: Nat, e: {x == y : Nat}, h: {Nat.is_le(y, j) == True{} : Bool}) -> {Nat.is_le(x, j) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {Nat.is_le(_, j) == True{} : Bool}
  h

def gl.tr_lt(-j: Nat, -x1: Nat, -x: Nat, -y1: Nat, -y: Nat, ex: {x1 == x : Nat}, ey: {y1 == y : Nat}, h: {Nat.is_lt(j, Nat.add(x, y)) == True{} : Bool}) -> {Nat.is_lt(j, Nat.add(x1, y1)) == True{} : Bool}:
  %Equal.sym(Nat, x1, x, ex) : {Nat.is_lt(j, Nat.add(_, y1)) == True{} : Bool}
  %Equal.sym(Nat, y1, y, ey) : {Nat.is_lt(j, Nat.add(x, _)) == True{} : Bool}
  h

def gl.tr_o(-c2: Nat, -j: Nat, -c1: Nat, -c: Nat, -s1: Nat, -s: Nat, -n1: Nat, -n: Nat, ec: {c1 == c : Nat}, es: {s1 == s : Nat}, en: {n1 == n : Nat}, h: {Bool.and(Nat.is_eq(c2, c), Bool.and(Nat.is_le(s, j), Nat.is_lt(j, Nat.add(s, n)))) == False{} : Bool}) -> {Bool.and(Nat.is_eq(c2, c1), Bool.and(Nat.is_le(s1, j), Nat.is_lt(j, Nat.add(s1, n1)))) == False{} : Bool}:
  %Equal.sym(Nat, c1, c, ec) : {Bool.and(Nat.is_eq(c2, _), Bool.and(Nat.is_le(s1, j), Nat.is_lt(j, Nat.add(s1, n1)))) == False{} : Bool}
  %Equal.sym(Nat, s1, s, es) : {Bool.and(Nat.is_eq(c2, c), Bool.and(Nat.is_le(_, j), Nat.is_lt(j, Nat.add(_, n1)))) == False{} : Bool}
  %Equal.sym(Nat, n1, n, en) : {Bool.and(Nat.is_eq(c2, c), Bool.and(Nat.is_le(s, j), Nat.is_lt(j, Nat.add(s, _)))) == False{} : Bool}
  h

def gl.h_addr(r: Result<&2, &2, G.GpError, G.GpPlan>, +o: Nat, +g: Nat, +cs: List<&2, G.GpChunk>, +n0: Nat, -q: G.GpPool, -a: Nat, +c: Nat, +s: Nat, -n: Nat, +e: {G.genpool.alloc.apply(r, o, g, cs, n0) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}, +hr: {PP.pp.okp(cs, 0n, n0, r) == True{} : Bool}, +hn0: {Nat.is_lt(0n, n0) == True{} : Bool}) -> {a == Nat.add(G.genpool.chunk_addr(G.GpPool{o, g, cs}, c), Nat.mul(s, G.genpool.granule(G.GpPool{o, g, cs}))) : Nat}:
  match r:
    case Fail{x}:
      Empty.absurd({a == Nat.add(G.genpool.chunk_addr(G.GpPool{o, g, cs}, c), Nat.mul(s, G.genpool.granule(G.GpPool{o, g, cs}))) : Nat}, gl.fd(x, G.GpAlloc{q, a, c, s, n}, e))
    case Done{G.GpPlan{+c1, +s1, +b1}}:
      +hv = PP.pp.va_of(cs, c1, s1, b1, n0, hr)
      %Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fa(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e) : {_ == Nat.add(G.genpool.chunk_addr(G.GpPool{o, g, cs}, c), Nat.mul(s, g)) : Nat}
      %Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fc(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e) : {Nat.add(b1, Nat.mul(s1, g)) == Nat.add(G.genpool.chunk_addr(G.GpPool{o, g, cs}, _), Nat.mul(s, g)) : Nat}
      %Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fs(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e) : {Nat.add(b1, Nat.mul(s1, g)) == Nat.add(G.genpool.chunk_addr(G.GpPool{o, g, cs}, c1), Nat.mul(_, g)) : Nat}
      %Equal.sym(Nat, G.genpool.chunk_addr(G.GpPool{o, g, cs}, c1), b1, PP.pp.va_addr(cs, c1, s1, b1, n0, hv)) : {Nat.add(b1, Nat.mul(s1, g)) == Nat.add(_, Nat.mul(s1, g)) : Nat}
      {==}

def Laws.alloc_addr(fit, p, size, data, q, a, c, s, n, e):
  match p size:
    case G.GpPool{o, g, cs} 0n:
      Empty.absurd({a == Nat.add(G.genpool.chunk_addr(G.GpPool{o, g, cs}, c), Nat.mul(s, G.genpool.granule(G.GpPool{o, g, cs}))) : Nat}, gl.fd(G.GpBadSize{}, G.GpAlloc{q, a, c, s, n}, e))
    case G.GpPool{+o, +g, +cs} 1n+ +k:
      gl.h_addr(G.genpool.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), o, g, cs, G.genpool.granules_for(1n+k, g), q, a, c, s, n, e, PP.pp.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), N.nl.max1(Nat.div(Nat.add(1n+k, Nat.sub(g, 1n)), g)))

def gl.h_was_free(r: Result<&2, &2, G.GpError, G.GpPlan>, +o: Nat, +g: Nat, +cs: List<&2, G.GpChunk>, +n0: Nat, -q: G.GpPool, -a: Nat, +c: Nat, +s: Nat, +n: Nat, +j: Nat, +e: {G.genpool.alloc.apply(r, o, g, cs, n0) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}, +hr: {PP.pp.okp(cs, 0n, n0, r) == True{} : Bool}, +hn0: {Nat.is_lt(0n, n0) == True{} : Bool}, +l: {Nat.is_le(s, j) == True{} : Bool}, +m: {Nat.is_lt(j, Nat.add(s, n)) == True{} : Bool}) -> {G.genpool.used_at(G.GpPool{o, g, cs}, c, j) == False{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({G.genpool.used_at(G.GpPool{o, g, cs}, c, j) == False{} : Bool}, gl.fd(x, G.GpAlloc{q, a, c, s, n}, e))
    case Done{G.GpPlan{+c1, +s1, +b1}}:
      +hv = PP.pp.va_of(cs, c1, s1, b1, n0, hr)
      %Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fc(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e) : {G.genpool.used_at(G.GpPool{o, g, cs}, _, j) == False{} : Bool}
      PP.pp.va_free(cs, c1, s1, b1, n0, j, hv, gl.tr_le(s1, s, j, Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fs(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e), l), gl.tr_lt(j, s1, s, n0, n, Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fs(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e), Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fn(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e), m))

def Laws.alloc_was_free(fit, p, size, data, q, a, c, s, n, j, e, l, m):
  match p size:
    case G.GpPool{o, g, cs} 0n:
      Empty.absurd({G.genpool.used_at(G.GpPool{o, g, cs}, c, j) == False{} : Bool}, gl.fd(G.GpBadSize{}, G.GpAlloc{q, a, c, s, n}, e))
    case G.GpPool{+o, +g, +cs} 1n+ +k:
      gl.h_was_free(G.genpool.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), o, g, cs, G.genpool.granules_for(1n+k, g), q, a, c, s, n, j, e, PP.pp.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), N.nl.max1(Nat.div(Nat.add(1n+k, Nat.sub(g, 1n)), g)), l, m)

def gl.h_in_use(r: Result<&2, &2, G.GpError, G.GpPlan>, +o: Nat, +g: Nat, +cs: List<&2, G.GpChunk>, +n0: Nat, +q: G.GpPool, -a: Nat, +c: Nat, +s: Nat, +n: Nat, +j: Nat, +e: {G.genpool.alloc.apply(r, o, g, cs, n0) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}, +hr: {PP.pp.okp(cs, 0n, n0, r) == True{} : Bool}, +hn0: {Nat.is_lt(0n, n0) == True{} : Bool}, +l: {Nat.is_le(s, j) == True{} : Bool}, +m: {Nat.is_lt(j, Nat.add(s, n)) == True{} : Bool}) -> {G.genpool.used_at(q, c, j) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({G.genpool.used_at(q, c, j) == True{} : Bool}, gl.fd(x, G.GpAlloc{q, a, c, s, n}, e))
    case Done{G.GpPlan{+c1, +s1, +b1}}:
      +hv = PP.pp.va_of(cs, c1, s1, b1, n0, hr)
      %Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, G.GpPool, z => gl.fq(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e) : {G.genpool.used_at(_, c, j) == True{} : Bool}
      %Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fc(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e) : {G.genpool.used_at(G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, _, j) == True{} : Bool}
      PP.pp.mark_in(cs, c1, s1, b1, n0, j, hn0, hv, gl.tr_le(s1, s, j, Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fs(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e), l), gl.tr_lt(j, s1, s, n0, n, Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fs(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e), Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fn(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e), m))

def Laws.alloc_in_use(fit, p, size, data, q, a, c, s, n, j, e, l, m):
  match p size:
    case G.GpPool{o, g, cs} 0n:
      Empty.absurd({G.genpool.used_at(q, c, j) == True{} : Bool}, gl.fd(G.GpBadSize{}, G.GpAlloc{q, a, c, s, n}, e))
    case G.GpPool{+o, +g, +cs} 1n+ +k:
      gl.h_in_use(G.genpool.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), o, g, cs, G.genpool.granules_for(1n+k, g), q, a, c, s, n, j, e, PP.pp.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), N.nl.max1(Nat.div(Nat.add(1n+k, Nat.sub(g, 1n)), g)), l, m)

def gl.h_others(r: Result<&2, &2, G.GpError, G.GpPlan>, +o: Nat, +g: Nat, +cs: List<&2, G.GpChunk>, +n0: Nat, +q: G.GpPool, -a: Nat, +c: Nat, +s: Nat, +n: Nat, +c2: Nat, +j: Nat, +e: {G.genpool.alloc.apply(r, o, g, cs, n0) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}, +hr: {PP.pp.okp(cs, 0n, n0, r) == True{} : Bool}, +hn0: {Nat.is_lt(0n, n0) == True{} : Bool}, +ho: {Bool.and(Nat.is_eq(c2, c), Bool.and(Nat.is_le(s, j), Nat.is_lt(j, Nat.add(s, n)))) == False{} : Bool}) -> {G.genpool.used_at(q, c2, j) == G.genpool.used_at(G.GpPool{o, g, cs}, c2, j) : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({G.genpool.used_at(q, c2, j) == G.genpool.used_at(G.GpPool{o, g, cs}, c2, j) : Bool}, gl.fd(x, G.GpAlloc{q, a, c, s, n}, e))
    case Done{G.GpPlan{+c1, +s1, +b1}}:
      +hv = PP.pp.va_of(cs, c1, s1, b1, n0, hr)
      %Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, G.GpPool, z => gl.fq(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e) : {G.genpool.used_at(_, c2, j) == G.genpool.used_at(G.GpPool{o, g, cs}, c2, j) : Bool}
      PP.pp.mark_out(cs, c1, c2, s1, n0, True{}, j, gl.tr_o(c2, j, c1, c, s1, s, n0, n, Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fc(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e), Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fs(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e), Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fn(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e), ho))

def Laws.alloc_others(fit, p, size, data, q, a, c, s, n, c2, j, e, ho):
  match p size:
    case G.GpPool{o, g, cs} 0n:
      Empty.absurd({G.genpool.used_at(q, c2, j) == G.genpool.used_at(G.GpPool{o, g, cs}, c2, j) : Bool}, gl.fd(G.GpBadSize{}, G.GpAlloc{q, a, c, s, n}, e))
    case G.GpPool{+o, +g, +cs} 1n+ +k:
      gl.h_others(G.genpool.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), o, g, cs, G.genpool.granules_for(1n+k, g), q, a, c, s, n, c2, j, e, PP.pp.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), N.nl.max1(Nat.div(Nat.add(1n+k, Nat.sub(g, 1n)), g)), ho)

def gl.h_blank(r: Result<&2, &2, G.GpError, G.GpPlan>, +o: Nat, +g: Nat, +cs: List<&2, G.GpChunk>, +n0: Nat, +q: G.GpPool, -a: Nat, -c: Nat, -s: Nat, -n: Nat, +e: {G.genpool.alloc.apply(r, o, g, cs, n0) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}, +hr: {PP.pp.okp(cs, 0n, n0, r) == True{} : Bool}, +hn0: {Nat.is_lt(0n, n0) == True{} : Bool}) -> {G.genpool.blank(q) == G.genpool.blank(G.GpPool{o, g, cs}) : G.GpPool}:
  match r:
    case Fail{x}:
      Empty.absurd({G.genpool.blank(q) == G.genpool.blank(G.GpPool{o, g, cs}) : G.GpPool}, gl.fd(x, G.GpAlloc{q, a, c, s, n}, e))
    case Done{G.GpPlan{+c1, +s1, +b1}}:
      +hv = PP.pp.va_of(cs, c1, s1, b1, n0, hr)
      %Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, G.GpPool, z => gl.fq(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e) : {G.genpool.blank(_) == G.genpool.blank(G.GpPool{o, g, cs}) : G.GpPool}
      %PP.pp.mark_blank(cs, c1, s1, n0, True{}) : {G.GpPool{o, g, G.genpool.blank.go(G.genpool.mark(cs, c1, s1, n0, True{}))} == G.GpPool{o, g, _} : G.GpPool}
      {==}

def Laws.alloc_blank(fit, p, size, data, q, a, c, s, n, e):
  match p size:
    case G.GpPool{o, g, cs} 0n:
      Empty.absurd({G.genpool.blank(q) == G.genpool.blank(G.GpPool{o, g, cs}) : G.GpPool}, gl.fd(G.GpBadSize{}, G.GpAlloc{q, a, c, s, n}, e))
    case G.GpPool{+o, +g, +cs} 1n+ +k:
      gl.h_blank(G.genpool.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), o, g, cs, G.genpool.granules_for(1n+k, g), q, a, c, s, n, e, PP.pp.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), N.nl.max1(Nat.div(Nat.add(1n+k, Nat.sub(g, 1n)), g)))

def gl.h_avail(r: Result<&2, &2, G.GpError, G.GpPlan>, +o: Nat, +g: Nat, +cs: List<&2, G.GpChunk>, +n0: Nat, +q: G.GpPool, -a: Nat, -c: Nat, -s: Nat, +n: Nat, +e: {G.genpool.alloc.apply(r, o, g, cs, n0) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}, +hr: {PP.pp.okp(cs, 0n, n0, r) == True{} : Bool}, +hn0: {Nat.is_lt(0n, n0) == True{} : Bool}) -> {Nat.add(G.genpool.avail(q), Nat.mul(n, G.genpool.granule(G.GpPool{o, g, cs}))) == G.genpool.avail(G.GpPool{o, g, cs}) : Nat}:
  match r:
    case Fail{x}:
      Empty.absurd({Nat.add(G.genpool.avail(q), Nat.mul(n, G.genpool.granule(G.GpPool{o, g, cs}))) == G.genpool.avail(G.GpPool{o, g, cs}) : Nat}, gl.fd(x, G.GpAlloc{q, a, c, s, n}, e))
    case Done{G.GpPlan{+c1, +s1, +b1}}:
      +hv = PP.pp.va_of(cs, c1, s1, b1, n0, hr)
      %Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, G.GpPool, z => gl.fq(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e) : {Nat.add(G.genpool.avail(_), Nat.mul(n, g)) == Nat.mul(G.genpool.count_free.go(cs), g) : Nat}
      %Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fn(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e) : {Nat.add(Nat.mul(G.genpool.count_free.go(G.genpool.mark(cs, c1, s1, n0, True{})), g), Nat.mul(_, g)) == Nat.mul(G.genpool.count_free.go(cs), g) : Nat}
      %N.nl.mul_add(G.genpool.count_free.go(G.genpool.mark(cs, c1, s1, n0, True{})), n0, g) : {_ == Nat.mul(G.genpool.count_free.go(cs), g) : Nat}
      %PP.pp.cf_mark(cs, c1, s1, b1, n0, hv) : {Nat.mul(Nat.add(G.genpool.count_free.go(G.genpool.mark(cs, c1, s1, n0, True{})), n0), g) == Nat.mul(_, g) : Nat}
      {==}

def Laws.alloc_avail(fit, p, size, data, q, a, c, s, n, e):
  match p size:
    case G.GpPool{o, g, cs} 0n:
      Empty.absurd({Nat.add(G.genpool.avail(q), Nat.mul(n, G.genpool.granule(G.GpPool{o, g, cs}))) == G.genpool.avail(G.GpPool{o, g, cs}) : Nat}, gl.fd(G.GpBadSize{}, G.GpAlloc{q, a, c, s, n}, e))
    case G.GpPool{+o, +g, +cs} 1n+ +k:
      gl.h_avail(G.genpool.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), o, g, cs, G.genpool.granules_for(1n+k, g), q, a, c, s, n, e, PP.pp.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), N.nl.max1(Nat.div(Nat.add(1n+k, Nat.sub(g, 1n)), g)))


# Marking keeps every chunk's address and length, so the chunks stay apart

def gl.aa_mark(+b: Nat, +e: Nat, cs: List<&2, G.GpChunk>, k: Nat, +s: Nat, +n: Nat, +v: Bool, +g: Nat) -> {G.genpool.apart_all(b, e, G.genpool.mark(cs, k, s, n, v), g) == G.genpool.apart_all(b, e, cs, g) : Bool}:
  match cs k:
    case Nil{} _:
      {==}
    case Con{G.GpChunk{+a0, +u}, +t} 0n:
      %Equal.sym(Nat, List.length(&2, Bool, Bits.genpool.bits.fill(u, s, n, v)), List.length(&2, Bool, u), PB.pb.fill_len(u, s, n, v)) : {Bool.and(G.genpool.apart(b, e, a0, Nat.add(a0, Nat.mul(_, g))), G.genpool.apart_all(b, e, t, g)) == G.genpool.apart_all(b, e, Con{G.GpChunk{a0, u}, t}, g) : Bool}
      {==}
    case Con{+h, +t} 1n+ +j:
      %gl.aa_mark(b, e, t, j, s, n, v, g) : {Bool.and(G.genpool.apart(b, e, G.genpool.chunk.addr(h), G.genpool.chunk.end(h, g)), G.genpool.apart_all(b, e, G.genpool.mark(t, j, s, n, v), g)) == Bool.and(G.genpool.apart(b, e, G.genpool.chunk.addr(h), G.genpool.chunk.end(h, g)), _) : Bool}
      {==}

def gl.disj_mark(cs: List<&2, G.GpChunk>, k: Nat, +s: Nat, +n: Nat, +v: Bool, +g: Nat) -> {G.genpool.disjoint.go(G.genpool.mark(cs, k, s, n, v), g) == G.genpool.disjoint.go(cs, g) : Bool}:
  match cs k:
    case Nil{} _:
      {==}
    case Con{G.GpChunk{+a0, +u}, +t} 0n:
      %Equal.sym(Nat, List.length(&2, Bool, Bits.genpool.bits.fill(u, s, n, v)), List.length(&2, Bool, u), PB.pb.fill_len(u, s, n, v)) : {Bool.and(G.genpool.apart_all(a0, Nat.add(a0, Nat.mul(_, g)), t, g), G.genpool.disjoint.go(t, g)) == G.genpool.disjoint.go(Con{G.GpChunk{a0, u}, t}, g) : Bool}
      {==}
    case Con{+h, +t} 1n+ +j:
      %gl.aa_mark(G.genpool.chunk.addr(h), G.genpool.chunk.end(h, g), t, j, s, n, v, g) : {Bool.and(G.genpool.apart_all(G.genpool.chunk.addr(h), G.genpool.chunk.end(h, g), G.genpool.mark(t, j, s, n, v), g), G.genpool.disjoint.go(G.genpool.mark(t, j, s, n, v), g)) == Bool.and(_, G.genpool.disjoint.go(t, g)) : Bool}
      %gl.disj_mark(t, j, s, n, v, g) : {Bool.and(G.genpool.apart_all(G.genpool.chunk.addr(h), G.genpool.chunk.end(h, g), G.genpool.mark(t, j, s, n, v), g), G.genpool.disjoint.go(G.genpool.mark(t, j, s, n, v), g)) == Bool.and(G.genpool.apart_all(G.genpool.chunk.addr(h), G.genpool.chunk.end(h, g), G.genpool.mark(t, j, s, n, v), g), _) : Bool}
      {==}

def gl.h_free(r: Result<&2, &2, G.GpError, G.GpPlan>, +o: Nat, +g: Nat, +cs: List<&2, G.GpChunk>, +k: Nat, +q: G.GpPool, +a: Nat, -c: Nat, -s: Nat, -n: Nat, +e: {G.genpool.alloc.apply(r, o, g, cs, G.genpool.granules_for(1n+k, g)) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}, +hr: {PP.pp.okp(cs, 0n, G.genpool.granules_for(1n+k, g), r) == True{} : Bool}, +hn0: {Nat.is_lt(0n, G.genpool.granules_for(1n+k, g)) == True{} : Bool}, +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +hd: {G.genpool.disjoint.go(cs, g) == True{} : Bool}) -> {G.genpool.free(q, a, 1n+k) == Done{G.GpPool{o, g, cs}} : Result<&2, &2, G.GpError, G.GpPool>}:
  match r:
    case Fail{x}:
      Empty.absurd({G.genpool.free(q, a, 1n+k) == Done{G.GpPool{o, g, cs}} : Result<&2, &2, G.GpError, G.GpPool>}, gl.fd(x, G.GpAlloc{q, a, c, s, n}, e))
    case Done{G.GpPlan{+c1, +s1, +b1}}:
      +n0 = G.genpool.granules_for(1n+k, g)
      +hv = PP.pp.va_of(cs, c1, s1, b1, n0, hr)
      %Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, G.GpPool, z => gl.fq(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e) : {G.genpool.free(_, a, 1n+k) == Done{G.GpPool{o, g, cs}} : Result<&2, &2, G.GpError, G.GpPool>}
      %Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, Nat, z => gl.fa(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e) : {G.genpool.free(G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, _, 1n+k) == Done{G.GpPool{o, g, cs}} : Result<&2, &2, G.GpError, G.GpPool>}
      %Equal.sym(Maybe<&2, Nat>, G.genpool.locate(G.genpool.mark(cs, c1, s1, n0, True{}), Nat.add(b1, Nat.mul(s1, g)), g, 0n), Some{c1}, Equal.trans(Maybe<&2, Nat>, G.genpool.locate(G.genpool.mark(cs, c1, s1, n0, True{}), Nat.add(b1, Nat.mul(s1, g)), g, 0n), G.genpool.locate(cs, Nat.add(b1, Nat.mul(s1, g)), g, 0n), Some{c1}, PP.pp.locate_mark(cs, c1, s1, n0, True{}, Nat.add(b1, Nat.mul(s1, g)), g, 0n), Equal.trans(Maybe<&2, Nat>, G.genpool.locate(cs, Nat.add(b1, Nat.mul(s1, g)), g, 0n), Some{Nat.add(c1, 0n)}, Some{c1}, PP.pp.locate_hit(cs, c1, Nat.add(b1, Nat.mul(s1, g)), g, 0n, hd, PP.pp.va_inside(cs, c1, s1, b1, n0, g, hg, hn0, hv)), Equal.cong(Nat, Maybe<&2, Nat>, z => Some{z}, Nat.add(c1, 0n), c1, N.nl.add_zero(c1))))) : {G.genpool.free.found(_, G.genpool.mark(cs, c1, s1, n0, True{}), Nat.add(b1, Nat.mul(s1, g)), n0, o, g) == Done{G.GpPool{o, g, cs}} : Result<&2, &2, G.GpError, G.GpPool>}
      %Equal.sym(Result<&2, &2, G.GpError, List<&2, G.GpChunk>>, G.genpool.free.at(G.genpool.mark(cs, c1, s1, n0, True{}), c1, Nat.add(b1, Nat.mul(s1, g)), n0, g), Done{cs}, PP.pp.free_mark(cs, c1, s1, b1, n0, g, hg, hn0, hv)) : {G.genpool.free.pool(_, o, g) == Done{G.GpPool{o, g, cs}} : Result<&2, &2, G.GpError, G.GpPool>}
      {==}

def Laws.free_alloc(fit, p, size, data, q, a, c, s, n, hv, e):
  match p size:
    case G.GpPool{o, g, cs} 0n:
      Empty.absurd({G.genpool.free(q, a, 0n) == Done{G.GpPool{o, g, cs}} : Result<&2, &2, G.GpError, G.GpPool>}, gl.fd(G.GpBadSize{}, G.GpAlloc{q, a, c, s, n}, e))
    case G.GpPool{+o, +g, +cs} 1n+ +k:
      gl.h_free(G.genpool.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), o, g, cs, k, q, a, c, s, n, e, PP.pp.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), N.nl.max1(Nat.div(Nat.add(1n+k, Nat.sub(g, 1n)), g)), N.nl.and_l(Nat.is_lt(0n, g), G.genpool.disjoint.go(cs, g), hv), N.nl.and_r(Nat.is_lt(0n, g), G.genpool.disjoint.go(cs, g), hv))

def Laws.realloc(fit, p, size, data, q, a, c, s, n, hv, e):
  %Equal.sym(Result<&2, &2, G.GpError, G.GpPool>, G.genpool.free(q, a, size), Done{p}, Laws.free_alloc(~fit, p, size, data, q, a, c, s, n, hv, e)) : {G.genpool.alloc(~fit, G.genpool.pool(_, q), size, data) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}
  e

def gl.h_valid(r: Result<&2, &2, G.GpError, G.GpPlan>, +o: Nat, +g: Nat, +cs: List<&2, G.GpChunk>, +n0: Nat, +q: G.GpPool, -a: Nat, -c: Nat, -s: Nat, -n: Nat, +e: {G.genpool.alloc.apply(r, o, g, cs, n0) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}, +hvp: {G.genpool.valid(G.GpPool{o, g, cs}) == True{} : Bool}) -> {G.genpool.valid(q) == True{} : Bool}:
  match r:
    case Fail{x}:
      Empty.absurd({G.genpool.valid(q) == True{} : Bool}, gl.fd(x, G.GpAlloc{q, a, c, s, n}, e))
    case Done{G.GpPlan{+c1, +s1, +b1}}:
      %Equal.cong(Result<&2, &2, G.GpError, G.GpAlloc>, G.GpPool, z => gl.fq(z), Done{G.GpAlloc{G.GpPool{o, g, G.genpool.mark(cs, c1, s1, n0, True{})}, Nat.add(b1, Nat.mul(s1, g)), c1, s1, n0}}, Done{G.GpAlloc{q, a, c, s, n}}, e) : {G.genpool.valid(_) == True{} : Bool}
      %Equal.sym(Bool, G.genpool.disjoint.go(G.genpool.mark(cs, c1, s1, n0, True{}), g), G.genpool.disjoint.go(cs, g), gl.disj_mark(cs, c1, s1, n0, True{}, g)) : {Bool.and(Nat.is_lt(0n, g), _) == True{} : Bool}
      hvp

def Laws.alloc_valid(fit, p, size, data, q, a, c, s, n, hv, e):
  match p size:
    case G.GpPool{o, g, cs} 0n:
      Empty.absurd({G.genpool.valid(q) == True{} : Bool}, gl.fd(G.GpBadSize{}, G.GpAlloc{q, a, c, s, n}, e))
    case G.GpPool{+o, +g, +cs} 1n+ +k:
      gl.h_valid(G.genpool.plan(~fit, cs, G.genpool.granules_for(1n+k, g), data, g), o, g, cs, G.genpool.granules_for(1n+k, g), q, a, c, s, n, e, hv)

# A new pool is valid, and adding a chunk apart from the others keeps it so

def gl.pow_pos(+k: Nat) -> {Nat.is_lt(0n, Nat.pow(2n, k)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      N.nl.lt_le_trans(0n, Nat.pow(2n, j), Nat.add(Nat.pow(2n, j), Nat.mul(1n, Nat.pow(2n, j))), gl.pow_pos(j), N.nl.le_add(Nat.pow(2n, j), Nat.mul(1n, Nat.pow(2n, j))))

def Laws.new_valid(order):
  N.nl.and_i(Nat.is_lt(0n, Nat.pow(2n, order)), True{}, gl.pow_pos(order), {==})

def gl.or_comm(+x: Bool, +y: Bool) -> {Bool.or(x, y) == Bool.or(y, x) : Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def gl.aa_app(+b: Nat, +e: Nat, t: List<&2, G.GpChunk>, +x: G.GpChunk, +g: Nat, +h1: {G.genpool.apart_all(b, e, t, g) == True{} : Bool}, +h2: {G.genpool.apart(b, e, G.genpool.chunk.addr(x), G.genpool.chunk.end(x, g)) == True{} : Bool}) -> {G.genpool.apart_all(b, e, List.append(&2, G.GpChunk, t, [x]), g) == True{} : Bool}:
  match t:
    case Nil{}:
      N.nl.and_i(G.genpool.apart(b, e, G.genpool.chunk.addr(x), G.genpool.chunk.end(x, g)), True{}, h2, {==})
    case Con{+h, +r}:
      N.nl.and_i(G.genpool.apart(b, e, G.genpool.chunk.addr(h), G.genpool.chunk.end(h, g)), G.genpool.apart_all(b, e, List.append(&2, G.GpChunk, r, [x]), g), N.nl.and_l(G.genpool.apart(b, e, G.genpool.chunk.addr(h), G.genpool.chunk.end(h, g)), G.genpool.apart_all(b, e, r, g), h1), gl.aa_app(b, e, r, x, g, N.nl.and_r(G.genpool.apart(b, e, G.genpool.chunk.addr(h), G.genpool.chunk.end(h, g)), G.genpool.apart_all(b, e, r, g), h1), h2))

def gl.disj_app(cs: List<&2, G.GpChunk>, +x: G.GpChunk, +g: Nat, +hd: {G.genpool.disjoint.go(cs, g) == True{} : Bool}, +ha: {G.genpool.apart_all(G.genpool.chunk.addr(x), G.genpool.chunk.end(x, g), cs, g) == True{} : Bool}) -> {G.genpool.disjoint.go(List.append(&2, G.GpChunk, cs, [x]), g) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +bh = G.genpool.chunk.addr(h)
      +eh = G.genpool.chunk.end(h, g)
      +bx = G.genpool.chunk.addr(x)
      +ex = G.genpool.chunk.end(x, g)
      +hx = N.nl.and_l(G.genpool.apart(bx, ex, bh, eh), G.genpool.apart_all(bx, ex, t, g), ha)
      +hsym = Equal.trans(Bool, G.genpool.apart(bh, eh, bx, ex), G.genpool.apart(bx, ex, bh, eh), True{}, gl.or_comm(Nat.is_le(eh, bx), Nat.is_le(ex, bh)), hx)
      N.nl.and_i(G.genpool.apart_all(bh, eh, List.append(&2, G.GpChunk, t, [x]), g), G.genpool.disjoint.go(List.append(&2, G.GpChunk, t, [x]), g), gl.aa_app(bh, eh, t, x, g, N.nl.and_l(G.genpool.apart_all(bh, eh, t, g), G.genpool.disjoint.go(t, g), hd), hsym), gl.disj_app(t, x, g, N.nl.and_r(G.genpool.apart_all(bh, eh, t, g), G.genpool.disjoint.go(t, g), hd), N.nl.and_r(G.genpool.apart(bx, ex, bh, eh), G.genpool.apart_all(bx, ex, t, g), ha)))

def gl.rep_len(+n: Nat) -> {List.length(&2, Bool, List.replicate(Bool, n, False{})) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      %gl.rep_len(m) : {1n+List.length(&2, Bool, List.replicate(Bool, m, False{})) == 1n+_ : Nat}
      {==}

def gl.h_add2(ok: Bool, +o: Nat, +g: Nat, +cs: List<&2, G.GpChunk>, +addr: Nat, +m: Nat, -q: G.GpPool, +eok: {G.genpool.apart_all(addr, Nat.add(addr, Nat.mul(1n+m, g)), cs, g) == ok : Bool}, +e: {G.genpool.add.check(ok, o, g, cs, addr, 1n+m) == Done{q} : Result<&2, &2, G.GpError, G.GpPool>}, +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +hd: {G.genpool.disjoint.go(cs, g) == True{} : Bool}) -> {G.genpool.valid(q) == True{} : Bool}:
  match ok:
    case True{}:
      +x = {G.GpChunk{addr, List.replicate(Bool, 1n+m, False{})} : G.GpChunk}
      %Equal.cong(Result<&2, &2, G.GpError, G.GpPool>, G.GpPool, z => gl.fp(z), Done{G.GpPool{o, g, List.append(&2, G.GpChunk, cs, [x])}}, Done{q}, e) : {G.genpool.valid(_) == True{} : Bool}
      +ha = Equal.trans(Bool, G.genpool.apart_all(addr, G.genpool.chunk.end(x, g), cs, g), G.genpool.apart_all(addr, Nat.add(addr, Nat.mul(1n+m, g)), cs, g), True{}, Equal.cong(Nat, Bool, z => G.genpool.apart_all(addr, Nat.add(addr, Nat.mul(z, g)), cs, g), List.length(&2, Bool, List.replicate(Bool, 1n+m, False{})), 1n+m, gl.rep_len(1n+m)), eok)
      N.nl.and_i(Nat.is_lt(0n, g), G.genpool.disjoint.go(List.append(&2, G.GpChunk, cs, [x]), g), hg, gl.disj_app(cs, x, g, hd, ha))
    case False{}:
      Empty.absurd({G.genpool.valid(q) == True{} : Bool}, gl.pfd(G.GpOverlap{}, q, e))

def gl.h_add(+nn: Nat, +o: Nat, +g: Nat, +cs: List<&2, G.GpChunk>, +addr: Nat, -q: G.GpPool, +e: {G.genpool.add.go(nn, o, g, cs, addr) == Done{q} : Result<&2, &2, G.GpError, G.GpPool>}, +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +hd: {G.genpool.disjoint.go(cs, g) == True{} : Bool}) -> {G.genpool.valid(q) == True{} : Bool}:
  match nn:
    case 0n:
      Empty.absurd({G.genpool.valid(q) == True{} : Bool}, gl.pfd(G.GpBadSize{}, q, e))
    case 1n+ +m:
      gl.h_add2(G.genpool.apart_all(addr, Nat.add(addr, Nat.mul(1n+m, g)), cs, g), o, g, cs, addr, m, q, {==}, e, hg, hd)

def Laws.add_valid(p, addr, size, q, hv, e):
  match p:
    case G.GpPool{+o, +g, +cs}:
      gl.h_add(Nat.div(size, g), o, g, cs, addr, q, e, N.nl.and_l(Nat.is_lt(0n, g), G.genpool.disjoint.go(cs, g), hv), N.nl.and_r(Nat.is_lt(0n, g), G.genpool.disjoint.go(cs, g), hv))

# Vectors

def Laws.vec_first():
  {==}

def Laws.vec_align():
  {==}

def Laws.vec_overlap():
  {==}

# Freeing keeps every chunk's address and length, so the pool stays valid

def gl.wres(r: Result<&2, &2, G.GpError, List<&2, Bool>>, d: List<&2, Bool>) -> List<&2, Bool>:
  match r:
    case Fail{x}:
      d
    case Done{bs}:
      bs

def gl.cres(r: Result<&2, &2, G.GpError, List<&2, G.GpChunk>>, d: List<&2, G.GpChunk>) -> List<&2, G.GpChunk>:
  match r:
    case Fail{x}:
      d
    case Done{cs}:
      cs

def gl.wl_clear(ok: Bool, +bs: List<&2, Bool>, +n: Nat) -> {List.length(&2, Bool, gl.wres(G.genpool.free.clear(ok, bs, n), bs)) == List.length(&2, Bool, bs) : Nat}:
  match ok:
    case True{}:
      PB.pb.fp_len_keep(bs, n, False{})
    case False{}:
      {==}

def gl.wl_cons(+b: Bool, w: Result<&2, &2, G.GpError, List<&2, Bool>>, +t: List<&2, Bool>, +h: {List.length(&2, Bool, gl.wres(w, t)) == List.length(&2, Bool, t) : Nat}) -> {List.length(&2, Bool, gl.wres(G.genpool.free.cons(b, w), Con{b, t})) == 1n+List.length(&2, Bool, t) : Nat}:
  match w:
    case Fail{x}:
      {==}
    case Done{bs}:
      %h : {1n+List.length(&2, Bool, bs) == 1n+_ : Nat}
      {==}

def gl.walk_len(+bits: List<&2, Bool>, +hit: Bool, +past: Bool, +x: Nat, +a: Nat, +g: Nat, +n: Nat) -> {List.length(&2, Bool, gl.wres(G.genpool.free.walk(bits, hit, past, x, a, g, n), bits)) == List.length(&2, Bool, bits) : Nat}:
  match bits hit past:
    case Nil{} True{} _:
      gl.wl_clear(Bits.genpool.bits.used_prefix(Nil{}, n), Nil{}, n)
    case Con{+b, +t} True{} _:
      gl.wl_clear(Bits.genpool.bits.used_prefix(Con{b, t}, n), Con{b, t}, n)
    case Nil{} False{} _:
      {==}
    case Con{b, t} False{} True{}:
      {==}
    case Con{+b, +t} False{} False{}:
      gl.wl_cons(b, G.genpool.free.walk(t, Nat.is_eq(Nat.add(x, g), a), Nat.is_lt(a, Nat.add(x, g)), Nat.add(x, g), a, g, n), t, gl.walk_len(t, Nat.is_eq(Nat.add(x, g), a), Nat.is_lt(a, Nat.add(x, g)), Nat.add(x, g), a, g, n))

def gl.fc_blank(+a0: Nat, w: Result<&2, &2, G.GpError, List<&2, Bool>>, +u: List<&2, Bool>, +t: List<&2, G.GpChunk>, +h: {List.length(&2, Bool, gl.wres(w, u)) == List.length(&2, Bool, u) : Nat}) -> {G.genpool.blank.go(gl.cres(G.genpool.free.chunk(a0, w, t), Con{G.GpChunk{a0, u}, t})) == G.genpool.blank.go(Con{G.GpChunk{a0, u}, t}) : List<&2, G.GpChunk>}:
  match w:
    case Fail{x}:
      {==}
    case Done{bs}:
      %h : {Con{G.GpChunk{a0, List.replicate(Bool, List.length(&2, Bool, bs), False{})}, G.genpool.blank.go(t)} == Con{G.GpChunk{a0, List.replicate(Bool, _, False{})}, G.genpool.blank.go(t)} : List<&2, G.GpChunk>}
      {==}

def gl.cc_blank(+h: G.GpChunk, r: Result<&2, &2, G.GpError, List<&2, G.GpChunk>>, +t: List<&2, G.GpChunk>, +ih: {G.genpool.blank.go(gl.cres(r, t)) == G.genpool.blank.go(t) : List<&2, G.GpChunk>}) -> {G.genpool.blank.go(gl.cres(G.genpool.free.ccons(h, r), Con{h, t})) == G.genpool.blank.go(Con{h, t}) : List<&2, G.GpChunk>}:
  match h r:
    case _ Fail{x}:
      {==}
    case G.GpChunk{+a, +u} Done{cs}:
      %ih : {Con{G.GpChunk{a, List.replicate(Bool, List.length(&2, Bool, u), False{})}, G.genpool.blank.go(cs)} == Con{G.GpChunk{a, List.replicate(Bool, List.length(&2, Bool, u), False{})}, _} : List<&2, G.GpChunk>}
      {==}

def gl.fa_blank(+cs: List<&2, G.GpChunk>, +c: Nat, +a: Nat, +n: Nat, +g: Nat) -> {G.genpool.blank.go(gl.cres(G.genpool.free.at(cs, c, a, n, g), cs)) == G.genpool.blank.go(cs) : List<&2, G.GpChunk>}:
  match cs c:
    case Nil{} _:
      {==}
    case Con{G.GpChunk{+a0, +u}, +t} 0n:
      gl.fc_blank(a0, G.genpool.free.walk(u, Nat.is_eq(a0, a), Nat.is_lt(a, a0), a0, a, g, n), u, t, gl.walk_len(u, Nat.is_eq(a0, a), Nat.is_lt(a, a0), a0, a, g, n))
    case Con{+h, +t} 1n+ +i:
      gl.cc_blank(h, G.genpool.free.at(t, i, a, n, g), t, gl.fa_blank(t, i, a, n, g))

def gl.fp_blank(r: Result<&2, &2, G.GpError, List<&2, G.GpChunk>>, +o: Nat, +g: Nat, +cs: List<&2, G.GpChunk>, +ih: {G.genpool.blank.go(gl.cres(r, cs)) == G.genpool.blank.go(cs) : List<&2, G.GpChunk>}) -> {G.genpool.blank(G.genpool.pool(G.genpool.free.pool(r, o, g), G.GpPool{o, g, cs})) == G.genpool.blank(G.GpPool{o, g, cs}) : G.GpPool}:
  match r:
    case Fail{x}:
      {==}
    case Done{c2}:
      %ih : {G.GpPool{o, g, G.genpool.blank.go(c2)} == G.GpPool{o, g, _} : G.GpPool}
      {==}

def gl.ff_blank(+m: Maybe<&2, Nat>, +o: Nat, +g: Nat, +cs: List<&2, G.GpChunk>, +a: Nat, +n: Nat) -> {G.genpool.blank(G.genpool.pool(G.genpool.free.found(m, cs, a, n, o, g), G.GpPool{o, g, cs})) == G.genpool.blank(G.GpPool{o, g, cs}) : G.GpPool}:
  match m:
    case None{}:
      {==}
    case Some{c}:
      gl.fp_blank(G.genpool.free.at(cs, c, a, n, g), o, g, cs, gl.fa_blank(cs, c, a, n, g))

def gl.free_blank(+p: G.GpPool, +a: Nat, +size: Nat) -> {G.genpool.blank(G.genpool.pool(G.genpool.free(p, a, size), p)) == G.genpool.blank(p) : G.GpPool}:
  match p size:
    case G.GpPool{o, g, cs} 0n:
      {==}
    case G.GpPool{+o, +g, +cs} 1n+k:
      gl.ff_blank(G.genpool.locate(cs, a, g, 0n), o, g, cs, a, G.genpool.granules_for(1n+k, g))

def gl.aa_blank(+b: Nat, +e: Nat, cs: List<&2, G.GpChunk>, +g: Nat) -> {G.genpool.apart_all(b, e, G.genpool.blank.go(cs), g) == G.genpool.apart_all(b, e, cs, g) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{G.GpChunk{+a0, +u}, +t}:
      %Equal.sym(Nat, List.length(&2, Bool, List.replicate(Bool, List.length(&2, Bool, u), False{})), List.length(&2, Bool, u), gl.rep_len(List.length(&2, Bool, u))) : {Bool.and(G.genpool.apart(b, e, a0, Nat.add(a0, Nat.mul(_, g))), G.genpool.apart_all(b, e, G.genpool.blank.go(t), g)) == Bool.and(G.genpool.apart(b, e, a0, Nat.add(a0, Nat.mul(List.length(&2, Bool, u), g))), G.genpool.apart_all(b, e, t, g)) : Bool}
      %gl.aa_blank(b, e, t, g) : {Bool.and(G.genpool.apart(b, e, a0, Nat.add(a0, Nat.mul(List.length(&2, Bool, u), g))), G.genpool.apart_all(b, e, G.genpool.blank.go(t), g)) == Bool.and(G.genpool.apart(b, e, a0, Nat.add(a0, Nat.mul(List.length(&2, Bool, u), g))), _) : Bool}
      {==}

def gl.dj_blank(cs: List<&2, G.GpChunk>, +g: Nat) -> {G.genpool.disjoint.go(G.genpool.blank.go(cs), g) == G.genpool.disjoint.go(cs, g) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{G.GpChunk{+a0, +u}, +t}:
      %Equal.sym(Nat, List.length(&2, Bool, List.replicate(Bool, List.length(&2, Bool, u), False{})), List.length(&2, Bool, u), gl.rep_len(List.length(&2, Bool, u))) : {Bool.and(G.genpool.apart_all(a0, Nat.add(a0, Nat.mul(_, g)), G.genpool.blank.go(t), g), G.genpool.disjoint.go(G.genpool.blank.go(t), g)) == Bool.and(G.genpool.apart_all(a0, Nat.add(a0, Nat.mul(List.length(&2, Bool, u), g)), t, g), G.genpool.disjoint.go(t, g)) : Bool}
      %gl.aa_blank(a0, Nat.add(a0, Nat.mul(List.length(&2, Bool, u), g)), t, g) : {Bool.and(G.genpool.apart_all(a0, Nat.add(a0, Nat.mul(List.length(&2, Bool, u), g)), G.genpool.blank.go(t), g), G.genpool.disjoint.go(G.genpool.blank.go(t), g)) == Bool.and(_, G.genpool.disjoint.go(t, g)) : Bool}
      %gl.dj_blank(t, g) : {Bool.and(G.genpool.apart_all(a0, Nat.add(a0, Nat.mul(List.length(&2, Bool, u), g)), G.genpool.blank.go(t), g), G.genpool.disjoint.go(G.genpool.blank.go(t), g)) == Bool.and(G.genpool.apart_all(a0, Nat.add(a0, Nat.mul(List.length(&2, Bool, u), g)), G.genpool.blank.go(t), g), _) : Bool}
      {==}

def gl.vb(p: G.GpPool) -> {G.genpool.valid(G.genpool.blank(p)) == G.genpool.valid(p) : Bool}:
  match p:
    case G.GpPool{+o, +g, +cs}:
      %gl.dj_blank(cs, g) : {Bool.and(Nat.is_lt(0n, g), G.genpool.disjoint.go(G.genpool.blank.go(cs), g)) == Bool.and(Nat.is_lt(0n, g), _) : Bool}
      {==}

def Laws.free_valid(p, addr, size, q, hv, e):
  %e : {G.genpool.valid(G.genpool.pool(_, p)) == True{} : Bool}
  +x = G.genpool.pool(G.genpool.free(p, addr, size), p)
  Equal.trans(Bool, G.genpool.valid(x), G.genpool.valid(G.genpool.blank(x)), True{}, Equal.sym(Bool, G.genpool.valid(G.genpool.blank(x)), G.genpool.valid(x), gl.vb(x)), Equal.trans(Bool, G.genpool.valid(G.genpool.blank(x)), G.genpool.valid(G.genpool.blank(p)), True{}, Equal.cong(G.GpPool, Bool, z => G.genpool.valid(z), G.genpool.blank(x), G.genpool.blank(p), gl.free_blank(p, addr, size)), Equal.trans(Bool, G.genpool.valid(G.genpool.blank(p)), G.genpool.valid(p), True{}, gl.vb(p), hv)))
