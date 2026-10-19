# Proof helpers for bend-osdev-genalloc: granule bitmaps (bits.bend), and
# the walk of genpool.free along a chunk's bits.
import Base
import ./bits.bend as Bits
import ./genalloc.bend as G
import ./proof_nat.bend as N

def pb.not_t(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, N.nl.ft(e))

def pb.fp_nil(n: Nat, hn: {Nat.is_lt(0n, n) == True{} : Bool}, h: {Bits.genpool.bits.free_prefix(Nil{}, n) == True{} : Bool}) -> Empty:
  match n:
    case 0n:
      N.nl.ft(hn)
    case 1n+m:
      N.nl.ft(h)

def pb.up_nil(n: Nat, hn: {Nat.is_lt(0n, n) == True{} : Bool}, h: {Bits.genpool.bits.used_prefix(Nil{}, n) == True{} : Bool}) -> Empty:
  match n:
    case 0n:
      N.nl.ft(hn)
    case 1n+m:
      N.nl.ft(h)

# a free run lies inside the bits
def pb.fp_len(v: List<&2, Bool>, n: Nat, h: {Bits.genpool.bits.free_prefix(v, n) == True{} : Bool}) -> {Nat.is_le(n, List.length(&2, Bool, v)) == True{} : Bool}:
  match v n:
    case _ 0n:
      {==}
    case Nil{} 1n+m:
      Empty.absurd({Nat.is_le(1n+m, 0n) == True{} : Bool}, N.nl.ft(h))
    case Con{+b, t} 1n+m:
      pb.fp_len(t, m, N.nl.and_r(Bool.not(b), Bits.genpool.bits.free_prefix(t, m), h))

def pb.rf_len(u: List<&2, Bool>, s: Nat, +n: Nat, hn: {Nat.is_lt(0n, n) == True{} : Bool}, h: {Bits.genpool.bits.run_free(u, s, n) == True{} : Bool}) -> {Nat.is_le(Nat.add(s, n), List.length(&2, Bool, u)) == True{} : Bool}:
  match u s:
    case Nil{} +i:
      Empty.absurd({Nat.is_le(Nat.add(i, n), 0n) == True{} : Bool}, pb.fp_nil(n, hn, h))
    case Con{+b, +t} 0n:
      pb.fp_len(Con{b, t}, n, h)
    case Con{b, t} 1n+i:
      pb.rf_len(t, i, n, hn, h)

# the granules of a free run are free
def pb.fp_get(v: List<&2, Bool>, n: Nat, j: Nat, h: {Bits.genpool.bits.free_prefix(v, n) == True{} : Bool}, m: {Nat.is_lt(j, n) == True{} : Bool}) -> {Bits.genpool.bits.get(v, j) == False{} : Bool}:
  match v n j:
    case Nil{} _ _:
      {==}
    case Con{b, t} 0n +jj:
      Empty.absurd({Bits.genpool.bits.get(Con{b, t}, jj) == False{} : Bool}, N.nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(jj, 0n), True{}, Equal.sym(Bool, Nat.is_lt(jj, 0n), False{}, N.nl.lt0(jj)), m)))
    case Con{+b, t} 1n+k 0n:
      pb.not_t(b, N.nl.and_l(Bool.not(b), Bits.genpool.bits.free_prefix(t, k), h))
    case Con{+b, t} 1n+k 1n+jj:
      pb.fp_get(t, k, jj, N.nl.and_r(Bool.not(b), Bits.genpool.bits.free_prefix(t, k), h), m)

def pb.rf_get(u: List<&2, Bool>, s: Nat, +n: Nat, j: Nat, h: {Bits.genpool.bits.run_free(u, s, n) == True{} : Bool}, l: {Nat.is_le(s, j) == True{} : Bool}, m: {Nat.is_lt(j, Nat.add(s, n)) == True{} : Bool}) -> {Bits.genpool.bits.get(u, j) == False{} : Bool}:
  match u s j:
    case Nil{} _ _:
      {==}
    case Con{+b, +t} 0n jj:
      pb.fp_get(Con{b, t}, n, jj, h, m)
    case Con{b, t} 1n+i 0n:
      Empty.absurd({Bits.genpool.bits.get(Con{b, t}, 0n) == False{} : Bool}, N.nl.ft(l))
    case Con{b, t} 1n+i 1n+jj:
      pb.rf_get(t, i, n, jj, h, l, m)

# Filling

def pb.fp_len_keep(v: List<&2, Bool>, n: Nat, +w: Bool) -> {List.length(&2, Bool, Bits.genpool.bits.fill_prefix(v, n, w)) == List.length(&2, Bool, v) : Nat}:
  match v n:
    case Nil{} _:
      {==}
    case Con{b, t} 0n:
      {==}
    case Con{b, +t} 1n+m:
      %pb.fp_len_keep(t, m, w) : {1n+List.length(&2, Bool, Bits.genpool.bits.fill_prefix(t, m, w)) == 1n+_ : Nat}
      {==}

def pb.fill_len(u: List<&2, Bool>, s: Nat, +n: Nat, +w: Bool) -> {List.length(&2, Bool, Bits.genpool.bits.fill(u, s, n, w)) == List.length(&2, Bool, u) : Nat}:
  match u s:
    case Nil{} _:
      {==}
    case Con{+b, +t} 0n:
      pb.fp_len_keep(Con{b, t}, n, w)
    case Con{b, +t} 1n+i:
      %pb.fill_len(t, i, n, w) : {1n+List.length(&2, Bool, Bits.genpool.bits.fill(t, i, n, w)) == 1n+_ : Nat}
      {==}

def pb.fp_get_in(v: List<&2, Bool>, n: Nat, j: Nat, +w: Bool, m: {Nat.is_lt(j, n) == True{} : Bool}, hl: {Nat.is_lt(j, List.length(&2, Bool, v)) == True{} : Bool}) -> {Bits.genpool.bits.get(Bits.genpool.bits.fill_prefix(v, n, w), j) == w : Bool}:
  match v n j:
    case Nil{} _ +jj:
      Empty.absurd({Bits.genpool.bits.get(Bits.genpool.bits.fill_prefix(Nil{}, n, w), jj) == w : Bool}, N.nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(jj, 0n), True{}, Equal.sym(Bool, Nat.is_lt(jj, 0n), False{}, N.nl.lt0(jj)), hl)))
    case Con{b, t} 0n +jj:
      Empty.absurd({Bits.genpool.bits.get(Con{b, t}, jj) == w : Bool}, N.nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(jj, 0n), True{}, Equal.sym(Bool, Nat.is_lt(jj, 0n), False{}, N.nl.lt0(jj)), m)))
    case Con{b, t} 1n+k 0n:
      {==}
    case Con{b, t} 1n+k 1n+jj:
      pb.fp_get_in(t, k, jj, w, m, hl)

def pb.fill_get_in(u: List<&2, Bool>, s: Nat, +n: Nat, j: Nat, +w: Bool, l: {Nat.is_le(s, j) == True{} : Bool}, m: {Nat.is_lt(j, Nat.add(s, n)) == True{} : Bool}, hl: {Nat.is_lt(j, List.length(&2, Bool, u)) == True{} : Bool}) -> {Bits.genpool.bits.get(Bits.genpool.bits.fill(u, s, n, w), j) == w : Bool}:
  match u s j:
    case Nil{} _ +jj:
      Empty.absurd({Bits.genpool.bits.get(Nil{}, jj) == w : Bool}, N.nl.ft(Equal.trans(Bool, False{}, Nat.is_lt(jj, 0n), True{}, Equal.sym(Bool, Nat.is_lt(jj, 0n), False{}, N.nl.lt0(jj)), hl)))
    case Con{+b, +t} 0n jj:
      pb.fp_get_in(Con{b, t}, n, jj, w, m, hl)
    case Con{b, t} 1n+i 0n:
      Empty.absurd({Bits.genpool.bits.get(Con{b, Bits.genpool.bits.fill(t, i, n, w)}, 0n) == w : Bool}, N.nl.ft(l))
    case Con{b, t} 1n+i 1n+jj:
      pb.fill_get_in(t, i, n, jj, w, l, m, hl)

def pb.fp_get_out(v: List<&2, Bool>, n: Nat, j: Nat, +w: Bool, o: {Nat.is_lt(j, n) == False{} : Bool}) -> {Bits.genpool.bits.get(Bits.genpool.bits.fill_prefix(v, n, w), j) == Bits.genpool.bits.get(v, j) : Bool}:
  match v n j:
    case Nil{} _ _:
      {==}
    case Con{b, t} 0n _:
      {==}
    case Con{b, t} 1n+k 0n:
      Empty.absurd({w == b : Bool}, N.nl.tf(o))
    case Con{b, t} 1n+k 1n+jj:
      pb.fp_get_out(t, k, jj, w, o)

def pb.fill_get_out(u: List<&2, Bool>, s: Nat, +n: Nat, j: Nat, +w: Bool, o: {Bool.and(Nat.is_le(s, j), Nat.is_lt(j, Nat.add(s, n))) == False{} : Bool}) -> {Bits.genpool.bits.get(Bits.genpool.bits.fill(u, s, n, w), j) == Bits.genpool.bits.get(u, j) : Bool}:
  match u s j:
    case Nil{} _ _:
      {==}
    case Con{+b, +t} 0n +jj:
      pb.fp_get_out(Con{b, t}, n, jj, w, N.nl.and_f(Nat.is_le(0n, jj), Nat.is_lt(jj, n), o, N.nl.le_zero(jj)))
    case Con{b, t} 1n+i 0n:
      {==}
    case Con{b, t} 1n+i 1n+jj:
      pb.fill_get_out(t, i, n, jj, w, o)

# Freeing a filled run

def pb.take_fill(u: List<&2, Bool>, s: Nat, n: Nat, +w: Bool) -> {List.take(&2, Bool, Bits.genpool.bits.fill(u, s, n, w), s) == List.take(&2, Bool, u, s) : List<&2, Bool>}:
  match u s n:
    case Nil{} _ _:
      {==}
    case Con{b, t} 0n 0n:
      {==}
    case Con{b, t} 0n 1n+m:
      {==}
    case Con{+b, +t} 1n+ +i +k:
      %pb.take_fill(t, i, k, w) : {Con{b, List.take(&2, Bool, Bits.genpool.bits.fill(t, i, k, w), i)} == Con{b, _} : List<&2, Bool>}
      {==}

def pb.drop_fill(u: List<&2, Bool>, s: Nat, n: Nat, +w: Bool) -> {List.drop(&2, Bool, Bits.genpool.bits.fill(u, s, n, w), s) == Bits.genpool.bits.fill_prefix(List.drop(&2, Bool, u, s), n, w) : List<&2, Bool>}:
  match u s n:
    case Nil{} _ _:
      {==}
    case Con{b, t} 0n 0n:
      {==}
    case Con{b, t} 0n 1n+m:
      {==}
    case Con{b, t} 1n+i k:
      pb.drop_fill(t, i, k, w)

def pb.up_fill(v: List<&2, Bool>, n: Nat, hl: {Nat.is_le(n, List.length(&2, Bool, v)) == True{} : Bool}) -> {Bits.genpool.bits.used_prefix(Bits.genpool.bits.fill_prefix(v, n, True{}), n) == True{} : Bool}:
  match v n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+m:
      Empty.absurd({Bits.genpool.bits.used_prefix(Nil{}, 1n+m) == True{} : Bool}, N.nl.ft(hl))
    case Con{b, t} 0n:
      {==}
    case Con{b, t} 1n+m:
      pb.up_fill(t, m, hl)

def pb.fill_back(v: List<&2, Bool>, n: Nat, +h: {Bits.genpool.bits.free_prefix(v, n) == True{} : Bool}) -> {Bits.genpool.bits.fill_prefix(Bits.genpool.bits.fill_prefix(v, n, True{}), n, False{}) == v : List<&2, Bool>}:
  match v n:
    case Nil{} _:
      {==}
    case Con{b, t} 0n:
      {==}
    case Con{+b, +t} 1n+ +m:
      %Equal.sym(Bool, b, False{}, pb.not_t(b, N.nl.and_l(Bool.not(b), Bits.genpool.bits.free_prefix(t, m), h))) : {Con{False{}, Bits.genpool.bits.fill_prefix(Bits.genpool.bits.fill_prefix(t, m, True{}), m, False{})} == Con{_, t} : List<&2, Bool>}
      %pb.fill_back(t, m, N.nl.and_r(Bool.not(b), Bits.genpool.bits.free_prefix(t, m), h)) : {Con{False{}, Bits.genpool.bits.fill_prefix(Bits.genpool.bits.fill_prefix(t, m, True{}), m, False{})} == Con{False{}, _} : List<&2, Bool>}
      {==}

def pb.take_drop(u: List<&2, Bool>, s: Nat) -> {List.append(&2, Bool, List.take(&2, Bool, u, s), List.drop(&2, Bool, u, s)) == u : List<&2, Bool>}:
  match u s:
    case Nil{} _:
      {==}
    case Con{b, t} 0n:
      {==}
    case Con{+b, +t} 1n+ +i:
      %pb.take_drop(t, i) : {Con{b, List.append(&2, Bool, List.take(&2, Bool, t, i), List.drop(&2, Bool, t, i))} == Con{b, _} : List<&2, Bool>}
      {==}

# The walk of genpool.free: from address x, the granule at x + s * g is
# found after s steps, and the n granules there are freed
def pb.walk(bits: List<&2, Bool>, s: Nat, +x: Nat, +g: Nat, +n: Nat, +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, hu: {Bits.genpool.bits.used_prefix(List.drop(&2, Bool, bits, s), n) == True{} : Bool}) -> {G.genpool.free.walk(bits, Nat.is_eq(x, Nat.add(x, Nat.mul(s, g))), Nat.is_lt(Nat.add(x, Nat.mul(s, g)), x), x, Nat.add(x, Nat.mul(s, g)), g, n) == Done{List.append(&2, Bool, List.take(&2, Bool, bits, s), Bits.genpool.bits.fill_prefix(List.drop(&2, Bool, bits, s), n, False{}))} : Result<&2, &2, G.GpError, List<&2, Bool>>}:
  match bits s:
    case Nil{} 0n:
      %Equal.sym(Nat, Nat.add(x, 0n), x, N.nl.add_zero(x)) : {G.genpool.free.walk(Nil{}, Nat.is_eq(x, _), Nat.is_lt(_, x), x, _, g, n) == Done{Bits.genpool.bits.fill_prefix(Nil{}, n, False{})} : Result<&2, &2, G.GpError, List<&2, Bool>>}
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, N.nl.eq_refl(x)) : {G.genpool.free.walk(Nil{}, _, Nat.is_lt(x, x), x, x, g, n) == Done{Bits.genpool.bits.fill_prefix(Nil{}, n, False{})} : Result<&2, &2, G.GpError, List<&2, Bool>>}
      %Equal.sym(Bool, Bits.genpool.bits.used_prefix(Nil{}, n), True{}, hu) : {G.genpool.free.clear(_, Nil{}, n) == Done{Bits.genpool.bits.fill_prefix(Nil{}, n, False{})} : Result<&2, &2, G.GpError, List<&2, Bool>>}
      {==}
    case Con{+b, +t} 0n:
      %Equal.sym(Nat, Nat.add(x, 0n), x, N.nl.add_zero(x)) : {G.genpool.free.walk(Con{b, t}, Nat.is_eq(x, _), Nat.is_lt(_, x), x, _, g, n) == Done{Bits.genpool.bits.fill_prefix(Con{b, t}, n, False{})} : Result<&2, &2, G.GpError, List<&2, Bool>>}
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, N.nl.eq_refl(x)) : {G.genpool.free.walk(Con{b, t}, _, Nat.is_lt(x, x), x, x, g, n) == Done{Bits.genpool.bits.fill_prefix(Con{b, t}, n, False{})} : Result<&2, &2, G.GpError, List<&2, Bool>>}
      %Equal.sym(Bool, Bits.genpool.bits.used_prefix(Con{b, t}, n), True{}, hu) : {G.genpool.free.clear(_, Con{b, t}, n) == Done{Bits.genpool.bits.fill_prefix(Con{b, t}, n, False{})} : Result<&2, &2, G.GpError, List<&2, Bool>>}
      {==}
    case Nil{} 1n+i:
      Empty.absurd({G.genpool.free.walk(Nil{}, Nat.is_eq(x, Nat.add(x, Nat.mul(1n+i, g))), Nat.is_lt(Nat.add(x, Nat.mul(1n+i, g)), x), x, Nat.add(x, Nat.mul(1n+i, g)), g, n) == Done{Bits.genpool.bits.fill_prefix(Nil{}, n, False{})} : Result<&2, &2, G.GpError, List<&2, Bool>>}, pb.up_nil(n, hn, hu))
    case Con{+b, +t} 1n+ +i:
      +m = Nat.mul(i, g)
      +a = Nat.add(x, Nat.add(g, m))
      +y = Nat.add(x, g)
      +pos = N.nl.lt_le_trans(0n, g, Nat.add(g, m), hg, N.nl.le_add(g, m))
      %Equal.sym(Bool, Nat.is_eq(x, a), False{}, N.nl.lt_ne(x, a, N.nl.lt_add(x, Nat.add(g, m), pos))) : {G.genpool.free.walk(Con{b, t}, _, Nat.is_lt(a, x), x, a, g, n) == Done{Con{b, List.append(&2, Bool, List.take(&2, Bool, t, i), Bits.genpool.bits.fill_prefix(List.drop(&2, Bool, t, i), n, False{}))}} : Result<&2, &2, G.GpError, List<&2, Bool>>}
      %Equal.sym(Bool, Nat.is_lt(a, x), False{}, N.nl.le_nlt(x, a, N.nl.le_add(x, Nat.add(g, m)))) : {G.genpool.free.walk(Con{b, t}, False{}, _, x, a, g, n) == Done{Con{b, List.append(&2, Bool, List.take(&2, Bool, t, i), Bits.genpool.bits.fill_prefix(List.drop(&2, Bool, t, i), n, False{}))}} : Result<&2, &2, G.GpError, List<&2, Bool>>}
      %N.nl.add_assoc(x, g, m) : {G.genpool.free.cons(b, G.genpool.free.walk(t, Nat.is_eq(y, _), Nat.is_lt(_, y), y, _, g, n)) == Done{Con{b, List.append(&2, Bool, List.take(&2, Bool, t, i), Bits.genpool.bits.fill_prefix(List.drop(&2, Bool, t, i), n, False{}))}} : Result<&2, &2, G.GpError, List<&2, Bool>>}
      %Equal.sym(Result<&2, &2, G.GpError, List<&2, Bool>>, G.genpool.free.walk(t, Nat.is_eq(y, Nat.add(y, m)), Nat.is_lt(Nat.add(y, m), y), y, Nat.add(y, m), g, n), Done{List.append(&2, Bool, List.take(&2, Bool, t, i), Bits.genpool.bits.fill_prefix(List.drop(&2, Bool, t, i), n, False{}))}, pb.walk(t, i, y, g, n, hg, hn, hu)) : {G.genpool.free.cons(b, _) == Done{Con{b, List.append(&2, Bool, List.take(&2, Bool, t, i), Bits.genpool.bits.fill_prefix(List.drop(&2, Bool, t, i), n, False{}))}} : Result<&2, &2, G.GpError, List<&2, Bool>>}
      {==}

# freeing a run just filled gives the bits back
def pb.free_fill(+u: List<&2, Bool>, +s: Nat, +x: Nat, +g: Nat, +n: Nat, +hg: {Nat.is_lt(0n, g) == True{} : Bool}, +hn: {Nat.is_lt(0n, n) == True{} : Bool}, +h: {Bits.genpool.bits.run_free(u, s, n) == True{} : Bool}) -> {G.genpool.free.walk(Bits.genpool.bits.fill(u, s, n, True{}), Nat.is_eq(x, Nat.add(x, Nat.mul(s, g))), Nat.is_lt(Nat.add(x, Nat.mul(s, g)), x), x, Nat.add(x, Nat.mul(s, g)), g, n) == Done{u} : Result<&2, &2, G.GpError, List<&2, Bool>>}:
  +f = Bits.genpool.bits.fill(u, s, n, True{})
  +d = List.drop(&2, Bool, u, s)
  +hu = Equal.trans(Bool, Bits.genpool.bits.used_prefix(List.drop(&2, Bool, f, s), n), Bits.genpool.bits.used_prefix(Bits.genpool.bits.fill_prefix(d, n, True{}), n), True{}, Equal.cong(List<&2, Bool>, Bool, z => Bits.genpool.bits.used_prefix(z, n), List.drop(&2, Bool, f, s), Bits.genpool.bits.fill_prefix(d, n, True{}), pb.drop_fill(u, s, n, True{})), pb.up_fill(d, n, pb.fp_len(d, n, h)))
  %Equal.sym(Result<&2, &2, G.GpError, List<&2, Bool>>, G.genpool.free.walk(f, Nat.is_eq(x, Nat.add(x, Nat.mul(s, g))), Nat.is_lt(Nat.add(x, Nat.mul(s, g)), x), x, Nat.add(x, Nat.mul(s, g)), g, n), Done{List.append(&2, Bool, List.take(&2, Bool, f, s), Bits.genpool.bits.fill_prefix(List.drop(&2, Bool, f, s), n, False{}))}, pb.walk(f, s, x, g, n, hg, hn, hu)) : {_ == Done{u} : Result<&2, &2, G.GpError, List<&2, Bool>>}
  %Equal.sym(List<&2, Bool>, List.take(&2, Bool, f, s), List.take(&2, Bool, u, s), pb.take_fill(u, s, n, True{})) : {Done{List.append(&2, Bool, _, Bits.genpool.bits.fill_prefix(List.drop(&2, Bool, f, s), n, False{}))} == Done{u} : Result<&2, &2, G.GpError, List<&2, Bool>>}
  %Equal.sym(List<&2, Bool>, List.drop(&2, Bool, f, s), Bits.genpool.bits.fill_prefix(d, n, True{}), pb.drop_fill(u, s, n, True{})) : {Done{List.append(&2, Bool, List.take(&2, Bool, u, s), Bits.genpool.bits.fill_prefix(_, n, False{}))} == Done{u} : Result<&2, &2, G.GpError, List<&2, Bool>>}
  %Equal.sym(List<&2, Bool>, Bits.genpool.bits.fill_prefix(Bits.genpool.bits.fill_prefix(d, n, True{}), n, False{}), d, pb.fill_back(d, n, h)) : {Done{List.append(&2, Bool, List.take(&2, Bool, u, s), _)} == Done{u} : Result<&2, &2, G.GpError, List<&2, Bool>>}
  %Equal.sym(List<&2, Bool>, List.append(&2, Bool, List.take(&2, Bool, u, s), d), u, pb.take_drop(u, s)) : {Done{_} == Done{u} : Result<&2, &2, G.GpError, List<&2, Bool>>}
  {==}
