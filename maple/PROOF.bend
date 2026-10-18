# Proofs of LAWS.bend, for the U32 instance (Maple32).
#
# The plan (the lemmas are in the proof_*.bend files):
# * proof_order.bend: U32's order (reflexive, antisymmetric, transitive),
#   its successor and predecessor (U32.inc, U32.sub(a, 1)), and that adding
#   d is monotone when it does not wrap (through the value of a word as a
#   Nat), all by induction on the bits of Base's Word.
# * proof_lists.bend: the list model. Cutting below a keeps every index under
#   a and clears the rest, cutting above b the same above b, so set_range and
#   clear_range load as the laws say, for every list; on an ordered list
#   (wf) they keep it ordered; find, next, prev and the gap search behave as
#   their scans say on appends and on lists wholly on one side of an index.
#   The gap search: every answer is within bounds and its run is free, and a
#   free run within bounds is found, at or below its start.
# * proof_level.bend: every leaf stays at depth height: cons leaves out
#   empty children, so joins, cuts, stores and erases keep chains of nodes
#   of one height.
# * proof_trees.bend: the tree. Every restructuring keeps the contents in
#   order; every node built by MapleNode.cons has the right pivot; in a tree
#   with right pivots and ordered contents, a child below an index holds
#   only entries ending before it and the slots after a child only entries
#   starting after its pivot, so lo and hi cut as the model cuts, and every
#   lookup and the gap search answer what the model's scan answers.
import Base
import ./model.bend as M
import ./node.bend as N
import ./maple.bend as T
import ./gap.bend as G
import ./proof_order.bend as O
import ./proof_lists.bend as P
import ./proof_trees.bend as R
import ./proof_level.bend as LV
import ./LAWS.bend as Laws

# Small helpers

def ab.res(r: Result<&2, &2, M.MapleError<U32>, U32>) -> Type:
  match r:
    case Done{s}:
      Unit
    case Fail{e}:
      Empty

def ab.fail_done(-x: M.MapleError<U32>, -s: U32, +e: {Fail{x} == Done{s} : Result<&2, &2, M.MapleError<U32>, U32>}) -> Empty:
  %Equal.sym(Result<&2, &2, M.MapleError<U32>, U32>, Fail{x}, Done{s}, e) : ab.res(_)
  Unit{}

def ga.done(r: Result<&2, &2, M.MapleError<U32>, U32>, -s: U32, g: P.GA(s, r)) -> {Result.is_done(&2, &2, M.MapleError<U32>, U32, r) == True{} : Bool}:
  match r:
    case Done{x}:
      {==}
    case Fail{e}:
      Empty.absurd({False{} == True{} : Bool}, g)

def wfrw(-V: Data, -xs: P.Es(V), -ys: P.Es(V), +e: {xs == ys : P.Es(V)}, +h: {P.wf(V, xs) == True{} : Bool}) -> {P.wf(V, ys) == True{} : Bool}:
  %e : {P.wf(V, _) == True{} : Bool}
  h

# entries(t) == xs, as a fact about the contents
def ent(-V: Data, +t: R.Tr(V), -xs: P.Es(V), +f: {T.Maple32.entries(V, t) == xs : P.Es(V)}) -> {R.TL(V, t) == xs : P.Es(V)}:
  Equal.trans(P.Es(V), R.TL(V, t), T.Maple32.entries(V, t), xs, Equal.sym(P.Es(V), T.Maple32.entries(V, t), R.TL(V, t), R.tr.entries(V, t)), f)

# The invariant

def Laws.valid_empty(V):
  {==}

def Laws.valid_empty_with(V, o):
  {==}

def Laws.valid_set_range(V, t, a, b, v, e):
  R.tr.valid_set_range(V, t, a, b, v, e)

def Laws.valid_clear_range(V, t, a, b, e):
  R.tr.valid_clear_range(V, t, a, b, e)

def Laws.valid_erase(V, t, i, e):
  R.tr.valid_erase(V, t, i, e)

def Laws.valid_disjoint(V, t, e):
  %Equal.sym(P.Es(V), T.Maple32.entries(V, t), R.TL(V, t), R.tr.entries(V, t)) : {P.wf(V, _) == True{} : Bool}
  R.tr.valid_wf(V, t, e)

def Laws.leveled_empty(V):
  {==}

def Laws.leveled_empty_with(V, o):
  {==}

def Laws.leveled_set_range(V, t, a, b, v, e):
  LV.tl.set_range(V, t, a, b, v, e)

def Laws.leveled_clear_range(V, t, a, b, e):
  LV.tl.clear_range(V, t, a, b, e)

def Laws.leveled_erase(V, t, i, e):
  LV.tl.erase(V, t, i, e)

# The contents

def Laws.set_range_entries(V, t, a, b, v, e):
  %Equal.sym(P.Es(V), T.Maple32.entries(V, T.Maple32.set_range(V, t, a, b, v)), R.TL(V, T.Maple32.set_range(V, t, a, b, v)), R.tr.entries(V, T.Maple32.set_range(V, t, a, b, v))) : {_ == P.msr(V, T.Maple32.entries(V, t), a, b, v) : P.Es(V)}
  %Equal.sym(P.Es(V), T.Maple32.entries(V, t), R.TL(V, t), R.tr.entries(V, t)) : {R.TL(V, T.Maple32.set_range(V, t, a, b, v)) == P.msr(V, _, a, b, v) : P.Es(V)}
  R.tr.set_range(V, t, a, b, v, e)

def Laws.clear_range_entries(V, t, a, b, e):
  %Equal.sym(P.Es(V), T.Maple32.entries(V, T.Maple32.clear_range(V, t, a, b)), R.TL(V, T.Maple32.clear_range(V, t, a, b)), R.tr.entries(V, T.Maple32.clear_range(V, t, a, b))) : {_ == P.mcr(V, T.Maple32.entries(V, t), a, b) : P.Es(V)}
  %Equal.sym(P.Es(V), T.Maple32.entries(V, t), R.TL(V, t), R.tr.entries(V, t)) : {R.TL(V, T.Maple32.clear_range(V, t, a, b)) == P.mcr(V, _, a, b) : P.Es(V)}
  R.tr.clear_range(V, t, a, b, e)

def Laws.set_range_inverted(V, t, a, b, v, e):
  %Equal.sym(Bool, O.ule(a, b), False{}, O.u.lt_not_le(b, a, e)) : {R.tsr.go(V, _, t, a, b, v) == t : R.Tr(V)}
  {==}

def Laws.clear_range_inverted(V, t, a, b, e):
  %Equal.sym(Bool, O.ule(a, b), False{}, O.u.lt_not_le(b, a, e)) : {R.tcr.go(V, _, t, a, b) == t : R.Tr(V)}
  {==}

def Laws.store_range_inverted(V, t, a, b, v, e):
  %Equal.sym(Bool, O.ule(a, b), False{}, O.u.lt_not_le(b, a, e)) : {T.Maple.store_range.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, _, t, a, b, v) == Fail{M.MapleInverted{a, b}} : Result<&2, &2, M.MapleError<U32>, R.Tr(V)>}
  {==}

def Laws.store_range_ok(V, t, a, b, v, e):
  %Equal.sym(Bool, O.ule(a, b), True{}, e) : {T.Maple.store_range.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, _, t, a, b, v) == Done{T.Maple32.set_range(V, t, a, b, v)} : Result<&2, &2, M.MapleError<U32>, R.Tr(V)>}
  {==}

def Laws.store_single(V, t, i, v):
  {==}

# The lookups

def Laws.load_spec(V, t, i, e):
  %Equal.sym(P.Es(V), T.Maple32.entries(V, t), R.TL(V, t), R.tr.entries(V, t)) : {T.Maple32.load(V, t, i) == P.mload(V, _, i) : Maybe<&2, V>}
  R.tr.load(V, t, i, e)

def Laws.lookup_spec(V, t, i, e):
  %Equal.sym(P.Es(V), T.Maple32.entries(V, t), R.TL(V, t), R.tr.entries(V, t)) : {T.Maple32.lookup(V, t, i) == P.mlookup(V, _, i) : Maybe<&2, P.Ent(V)>}
  R.tr.lookup(V, t, i, e)

def Laws.find_spec(V, t, i, e):
  %Equal.sym(P.Es(V), T.Maple32.entries(V, t), R.TL(V, t), R.tr.entries(V, t)) : {T.Maple32.find(V, t, i) == P.mfind(V, _, i) : Maybe<&2, P.Ent(V)>}
  R.tr.find(V, t, i, e)

def Laws.next_spec(V, t, i, e):
  %Equal.sym(P.Es(V), T.Maple32.entries(V, t), R.TL(V, t), R.tr.entries(V, t)) : {T.Maple32.next(V, t, i) == P.mnext(V, _, i) : Maybe<&2, P.Ent(V)>}
  R.tr.next(V, t, i, e)

def Laws.prev_spec(V, t, i, e):
  %Equal.sym(P.Es(V), T.Maple32.entries(V, t), R.TL(V, t), R.tr.entries(V, t)) : {T.Maple32.prev(V, t, i) == P.mprev(V, _, i) : Maybe<&2, P.Ent(V)>}
  R.tr.prev(V, t, i, e)

def Laws.empty_area_spec(V, t, min, max, size, e):
  %Equal.sym(P.Es(V), T.Maple32.entries(V, t), R.TL(V, t), R.tr.entries(V, t)) : {G.Maple32.empty_area(V, t, min, max, size) == M.MapleModel32.empty_area(V, _, min, max, size) : Result<&2, &2, M.MapleError<U32>, U32>}
  R.tr.empty_area(V, t, min, max, size, e)

# After an update

def sr.m(-V: Data, +t: R.Tr(V), +a: U32, +b: U32, +v: V, +e: {T.Maple32.valid(V, t) == True{} : Bool}) -> {R.TL(V, T.Maple32.set_range(V, t, a, b, v)) == P.msr(V, R.TL(V, t), a, b, v) : P.Es(V)}:
  R.tr.set_range(V, t, a, b, v, e)

def cr.m(-V: Data, +t: R.Tr(V), +a: U32, +b: U32, +e: {T.Maple32.valid(V, t) == True{} : Bool}) -> {R.TL(V, T.Maple32.clear_range(V, t, a, b)) == P.mcr(V, R.TL(V, t), a, b) : P.Es(V)}:
  R.tr.clear_range(V, t, a, b, e)

def Laws.set_range_load_in(V, t, a, b, v, i, e, f, g):
  %Equal.sym(Maybe<&2, V>, T.Maple32.load(V, T.Maple32.set_range(V, t, a, b, v), i), P.mload(V, R.TL(V, T.Maple32.set_range(V, t, a, b, v)), i), R.tr.load(V, T.Maple32.set_range(V, t, a, b, v), i, R.tr.valid_set_range(V, t, a, b, v, e))) : {_ == Some{v} : Maybe<&2, V>}
  %Equal.sym(P.Es(V), R.TL(V, T.Maple32.set_range(V, t, a, b, v)), P.msr(V, R.TL(V, t), a, b, v), sr.m(V, t, a, b, v, e)) : {P.mload(V, _, i) == Some{v} : Maybe<&2, V>}
  P.set_load_in(V, R.TL(V, t), a, b, v, i, f, g)

def Laws.set_range_load_out(V, t, a, b, v, i, e, f):
  %Equal.sym(Maybe<&2, V>, T.Maple32.load(V, T.Maple32.set_range(V, t, a, b, v), i), P.mload(V, R.TL(V, T.Maple32.set_range(V, t, a, b, v)), i), R.tr.load(V, T.Maple32.set_range(V, t, a, b, v), i, R.tr.valid_set_range(V, t, a, b, v, e))) : {_ == T.Maple32.load(V, t, i) : Maybe<&2, V>}
  %Equal.sym(Maybe<&2, V>, T.Maple32.load(V, t, i), P.mload(V, R.TL(V, t), i), R.tr.load(V, t, i, e)) : {P.mload(V, R.TL(V, T.Maple32.set_range(V, t, a, b, v)), i) == _ : Maybe<&2, V>}
  %Equal.sym(P.Es(V), R.TL(V, T.Maple32.set_range(V, t, a, b, v)), P.msr(V, R.TL(V, t), a, b, v), sr.m(V, t, a, b, v, e)) : {P.mload(V, _, i) == P.mload(V, R.TL(V, t), i) : Maybe<&2, V>}
  P.set_load_out(V, R.TL(V, t), a, b, v, i, f)

def Laws.clear_range_load_in(V, t, a, b, i, e, f, g):
  %Equal.sym(Maybe<&2, V>, T.Maple32.load(V, T.Maple32.clear_range(V, t, a, b), i), P.mload(V, R.TL(V, T.Maple32.clear_range(V, t, a, b)), i), R.tr.load(V, T.Maple32.clear_range(V, t, a, b), i, R.tr.valid_clear_range(V, t, a, b, e))) : {_ == None{} : Maybe<&2, V>}
  %Equal.sym(P.Es(V), R.TL(V, T.Maple32.clear_range(V, t, a, b)), P.mcr(V, R.TL(V, t), a, b), cr.m(V, t, a, b, e)) : {P.mload(V, _, i) == None{} : Maybe<&2, V>}
  P.clear_load_in(V, R.TL(V, t), a, b, i, f, g)

def Laws.clear_range_load_out(V, t, a, b, i, e, f):
  %Equal.sym(Maybe<&2, V>, T.Maple32.load(V, T.Maple32.clear_range(V, t, a, b), i), P.mload(V, R.TL(V, T.Maple32.clear_range(V, t, a, b)), i), R.tr.load(V, T.Maple32.clear_range(V, t, a, b), i, R.tr.valid_clear_range(V, t, a, b, e))) : {_ == T.Maple32.load(V, t, i) : Maybe<&2, V>}
  %Equal.sym(Maybe<&2, V>, T.Maple32.load(V, t, i), P.mload(V, R.TL(V, t), i), R.tr.load(V, t, i, e)) : {P.mload(V, R.TL(V, T.Maple32.clear_range(V, t, a, b)), i) == _ : Maybe<&2, V>}
  %Equal.sym(P.Es(V), R.TL(V, T.Maple32.clear_range(V, t, a, b)), P.mcr(V, R.TL(V, t), a, b), cr.m(V, t, a, b, e)) : {P.mload(V, _, i) == P.mload(V, R.TL(V, t), i) : Maybe<&2, V>}
  P.clear_load_out(V, R.TL(V, t), a, b, i, f)

def lh.pick(b: Bool, -V: Data, +y: P.Ent(V), +x: P.Ent(V), +i: U32, +eb: {P.holds(V, y, i) == b : Bool}, +f: {P.pk(V, b, y, None{}) == Some{x} : Maybe<&2, P.Ent(V)>}) -> {P.holds(V, x, i) == True{} : Bool}:
  match b:
    case True{}:
      %P.some.inj(P.Ent(V), y, x, f) : {P.holds(V, _, i) == True{} : Bool}
      eb
    case False{}:
      Empty.absurd({P.holds(V, x, i) == True{} : Bool}, O.ab.none_some(P.Ent(V), x, f))

def lh.go(-V: Data, m: Maybe<&2, P.Ent(V)>, +i: U32, +x: P.Ent(V), +f: {R.lgo(V, m, i) == Some{x} : Maybe<&2, P.Ent(V)>}) -> {P.holds(V, x, i) == True{} : Bool}:
  match m:
    case None{}:
      Empty.absurd({P.holds(V, x, i) == True{} : Bool}, O.ab.none_some(P.Ent(V), x, f))
    case Some{+y}:
      lh.pick(P.holds(V, y, i), V, y, x, i, {==}, f)

def Laws.lookup_holds(V, t, i, x, f):
  lh.go(V, T.Maple32.find(V, t, i), i, x, f)

def Laws.erase_load_in(V, t, i, x, j, e, f, g):
  match x:
    case M.MapleEntry{+a, +b, +v}:
      %Equal.sym(Maybe<&2, P.Ent(V)>, T.Maple32.lookup(V, t, i), Some{M.MapleEntry{a, b, v}}, f) : {T.Maple32.load(V, T.Maple.erase.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, _, t), j) == None{} : Maybe<&2, V>}
      Laws.clear_range_load_in(V, t, a, b, j, e, O.bo.and_l(O.ule(a, j), O.ule(j, b), g), O.bo.and_r(O.ule(a, j), O.ule(j, b), g))

def Laws.erase_load_out(V, t, i, x, j, e, f, g):
  match x:
    case M.MapleEntry{+a, +b, +v}:
      %Equal.sym(Maybe<&2, P.Ent(V)>, T.Maple32.lookup(V, t, i), Some{M.MapleEntry{a, b, v}}, f) : {T.Maple32.load(V, T.Maple.erase.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, _, t), j) == T.Maple32.load(V, t, j) : Maybe<&2, V>}
      Laws.clear_range_load_out(V, t, a, b, j, e, g)

def Laws.erase_absent(V, t, i, f):
  %Equal.sym(Maybe<&2, P.Ent(V)>, T.Maple32.lookup(V, t, i), None{}, f) : {T.Maple.erase.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, _, t) == t : R.Tr(V)}
  {==}

# Iteration

def Laws.find_first(V, t, x, ys, e, f):
  %Equal.sym(Maybe<&2, P.Ent(V)>, T.Maple32.find(V, t, 0), P.mfind(V, R.TL(V, t), 0), R.tr.find(V, t, 0, e)) : {_ == Some{x} : Maybe<&2, P.Ent(V)>}
  %Equal.sym(P.Es(V), R.TL(V, t), Con{x, ys}, ent(V, t, Con{x, ys}, f)) : {P.mfind(V, _, 0) == Some{x} : Maybe<&2, P.Ent(V)>}
  P.it.find_first(V, x, ys)

def Laws.next_after(V, t, xs, x, y, ys, e, f):
  +ft = ent(V, t, P.app(V, xs, Con{x, Con{y, ys}}), f)
  %Equal.sym(Maybe<&2, P.Ent(V)>, T.Maple32.next(V, t, P.lst(V, x)), P.mnext(V, R.TL(V, t), P.lst(V, x)), R.tr.next(V, t, P.lst(V, x), e)) : {_ == Some{y} : Maybe<&2, P.Ent(V)>}
  %Equal.sym(P.Es(V), R.TL(V, t), P.app(V, xs, Con{x, Con{y, ys}}), ft) : {P.mnext(V, _, P.lst(V, x)) == Some{y} : Maybe<&2, P.Ent(V)>}
  P.it.next_after(V, xs, x, y, ys, wfrw(V, R.TL(V, t), P.app(V, xs, Con{x, Con{y, ys}}), ft, R.tr.valid_wf(V, t, e)))

def Laws.next_none(V, t, xs, x, e, f):
  +ft = ent(V, t, P.app(V, xs, Con{x, Nil{}}), f)
  %Equal.sym(Maybe<&2, P.Ent(V)>, T.Maple32.next(V, t, P.lst(V, x)), P.mnext(V, R.TL(V, t), P.lst(V, x)), R.tr.next(V, t, P.lst(V, x), e)) : {_ == None{} : Maybe<&2, P.Ent(V)>}
  %Equal.sym(P.Es(V), R.TL(V, t), P.app(V, xs, Con{x, Nil{}}), ft) : {P.mnext(V, _, P.lst(V, x)) == None{} : Maybe<&2, P.Ent(V)>}
  P.it.next_none(V, xs, x, wfrw(V, R.TL(V, t), P.app(V, xs, Con{x, Nil{}}), ft, R.tr.valid_wf(V, t, e)))

def Laws.prev_before(V, t, xs, x, y, ys, e, f):
  +ft = ent(V, t, P.app(V, xs, Con{x, Con{y, ys}}), f)
  %Equal.sym(Maybe<&2, P.Ent(V)>, T.Maple32.prev(V, t, P.fst(V, y)), P.mprev(V, R.TL(V, t), P.fst(V, y)), R.tr.prev(V, t, P.fst(V, y), e)) : {_ == Some{x} : Maybe<&2, P.Ent(V)>}
  %Equal.sym(P.Es(V), R.TL(V, t), P.app(V, xs, Con{x, Con{y, ys}}), ft) : {P.mprev(V, _, P.fst(V, y)) == Some{x} : Maybe<&2, P.Ent(V)>}
  P.it.prev_before(V, xs, x, y, ys, wfrw(V, R.TL(V, t), P.app(V, xs, Con{x, Con{y, ys}}), ft, R.tr.valid_wf(V, t, e)))

# The gap search

def Laws.empty_area_zero(V, t, min, max):
  match t:
    case N.MapleTree{o, h, r}:
      {==}

def Laws.empty_area_inverted(V, t, min, max, size, f, g):
  match t:
    case N.MapleTree{o, h, +n}:
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(size, 0)), False{}, f) : {G.Maple.empty_area.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, ~M.MapleKey32.add, V, _, O.ult(max, min), n, min, max, size) == Fail{M.MapleBadRange{min, max}} : Result<&2, &2, M.MapleError<U32>, U32>}
      %Equal.sym(Bool, O.ult(max, min), True{}, g) : {G.Maple.empty_area.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, ~M.MapleKey32.add, V, False{}, _, n, min, max, size) == Fail{M.MapleBadRange{min, max}} : Result<&2, &2, M.MapleError<U32>, U32>}
      {==}

def mea(-V: Data, zs: Bool, inv: Bool, xs: P.Es(V), +min: U32, +max: U32, +size: U32) -> Result<&2, &2, M.MapleError<U32>, U32>:
  M.MapleModel.empty_area.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, ~M.MapleKey32.add, V, zs, inv, xs, min, max, size)

# the tree answers what the model answers
def ea.m(-V: Data, +t: R.Tr(V), +min: U32, +max: U32, +size: U32, -s: U32, +e: {T.Maple32.valid(V, t) == True{} : Bool}, +f: {G.Maple32.empty_area(V, t, min, max, size) == Done{s} : Result<&2, &2, M.MapleError<U32>, U32>}) -> {M.MapleModel32.empty_area(V, R.TL(V, t), min, max, size) == Done{s} : Result<&2, &2, M.MapleError<U32>, U32>}:
  Equal.trans(Result<&2, &2, M.MapleError<U32>, U32>, M.MapleModel32.empty_area(V, R.TL(V, t), min, max, size), G.Maple32.empty_area(V, t, min, max, size), Done{s}, Equal.sym(Result<&2, &2, M.MapleError<U32>, U32>, G.Maple32.empty_area(V, t, min, max, size), M.MapleModel32.empty_area(V, R.TL(V, t), min, max, size), R.tr.empty_area(V, t, min, max, size, e)), f)

def eb.go(zs: Bool, inv: Bool, -V: Data, +xs: P.Es(V), +min: U32, +max: U32, +size: U32, +s: U32, +f: {mea(V, zs, inv, xs, min, max, size) == Done{s} : Result<&2, &2, M.MapleError<U32>, U32>}) -> P.GB(min, U32.sub(size, 1), max, Done{s}):
  match zs:
    case True{}:
      Empty.absurd(P.GB(min, U32.sub(size, 1), max, Done{s}), ab.fail_done(M.MapleBadSize{}, s, f))
    case False{}:
      match inv:
        case True{}:
          Empty.absurd(P.GB(min, U32.sub(size, 1), max, Done{s}), ab.fail_done(M.MapleBadRange{min, max}, s, f))
        case False{}:
          %f : P.GB(min, U32.sub(size, 1), max, _)
          P.gbound(V, xs, min, U32.sub(size, 1), max)

def Laws.empty_area_bounds(V, t, min, max, size, s, e, f):
  eb.go(Cmp.is_eq(U32.cmp(size, 0)), O.ult(max, min), V, R.TL(V, t), min, max, size, s, ea.m(V, t, min, max, size, s, e, f))

def ef.go(zs: Bool, inv: Bool, -V: Data, +xs: P.Es(V), +min: U32, +max: U32, +size: U32, +s: U32, +w: {P.wf(V, xs) == True{} : Bool}, +f: {mea(V, zs, inv, xs, min, max, size) == Done{s} : Result<&2, &2, M.MapleError<U32>, U32>}) -> P.GF(V, xs, U32.sub(size, 1), Done{s}):
  match zs:
    case True{}:
      Empty.absurd(P.GF(V, xs, U32.sub(size, 1), Done{s}), ab.fail_done(M.MapleBadSize{}, s, f))
    case False{}:
      match inv:
        case True{}:
          Empty.absurd(P.GF(V, xs, U32.sub(size, 1), Done{s}), ab.fail_done(M.MapleBadRange{min, max}, s, f))
        case False{}:
          %f : P.GF(V, xs, U32.sub(size, 1), _)
          P.gfree(V, xs, min, U32.sub(size, 1), max, w)

def Laws.empty_area_free(V, t, min, max, size, s, i, e, f, g, h):
  Equal.trans(Maybe<&2, V>, T.Maple32.load(V, t, i), P.mload(V, R.TL(V, t), i), None{}, R.tr.load(V, t, i, e), ef.go(Cmp.is_eq(U32.cmp(size, 0)), O.ult(max, min), V, R.TL(V, t), min, max, size, s, R.tr.valid_wf(V, t, e), ea.m(V, t, min, max, size, s, e, f))(i)(g)(h))

# a free run in the tree is a free run in the model
def free.m(-V: Data, +t: R.Tr(V), +s: U32, +d: U32, +e: {T.Maple32.valid(V, t) == True{} : Bool}, h: @i:U32 -> {O.ule(s, i) == True{} : Bool} -> {O.ule(i, U32.add(s, d)) == True{} : Bool} -> {T.Maple32.load(V, t, i) == None{} : Maybe<&2, V>}) -> P.Free(V, R.TL(V, t), s, d):
  +i => +h1 => +h2 => Equal.trans(Maybe<&2, V>, P.mload(V, R.TL(V, t), i), T.Maple32.load(V, t, i), None{}, Equal.sym(Maybe<&2, V>, T.Maple32.load(V, t, i), P.mload(V, R.TL(V, t), i), R.tr.load(V, t, i, e)), h(i)(h1)(h2))

def ed.go(zs: Bool, inv: Bool, -V: Data, +xs: P.Es(V), +min: U32, +max: U32, +size: U32, +s: U32, +ez: {zs == False{} : Bool}, +ei: {O.ult(max, min) == inv : Bool}, +w: {P.wf(V, xs) == True{} : Bool}, +g: P.HB(min, s, U32.sub(size, 1), max), hm: P.Free(V, xs, s, U32.sub(size, 1))) -> {Result.is_done(&2, &2, M.MapleError<U32>, U32, mea(V, zs, inv, xs, min, max, size)) == True{} : Bool}:
  match zs:
    case True{}:
      Empty.absurd({False{} == True{} : Bool}, O.ab.tf(ez))
    case False{}:
      match inv:
        case True{}:
          +rest = O.bo.and_r(O.ule(min, s), Bool.and(O.ule(s, U32.add(s, U32.sub(size, 1))), O.ule(U32.add(s, U32.sub(size, 1)), max)), g)
          +smax = O.u.le_trans(s, U32.add(s, U32.sub(size, 1)), max, O.bo.and_l(O.ule(s, U32.add(s, U32.sub(size, 1))), O.ule(U32.add(s, U32.sub(size, 1)), max), rest), O.bo.and_r(O.ule(s, U32.add(s, U32.sub(size, 1))), O.ule(U32.add(s, U32.sub(size, 1)), max), rest))
          Empty.absurd({False{} == True{} : Bool}, O.u.lt_le_absurd(max, min, ei, O.u.le_trans(min, s, max, O.bo.and_l(O.ule(min, s), Bool.and(O.ule(s, U32.add(s, U32.sub(size, 1))), O.ule(U32.add(s, U32.sub(size, 1)), max)), g), smax)))
        case False{}:
          ga.done(P.GR(V, xs, min, U32.sub(size, 1), max), s, P.gcomplete(V, xs, min, s, U32.sub(size, 1), max, w, g, hm))

def Laws.empty_area_found(V, t, min, max, size, s, e, f, g, h):
  %Equal.sym(Result<&2, &2, M.MapleError<U32>, U32>, G.Maple32.empty_area(V, t, min, max, size), M.MapleModel32.empty_area(V, R.TL(V, t), min, max, size), R.tr.empty_area(V, t, min, max, size, e)) : {Result.is_done(&2, &2, M.MapleError<U32>, U32, _) == True{} : Bool}
  ed.go(Cmp.is_eq(U32.cmp(size, 0)), O.ult(max, min), V, R.TL(V, t), min, max, size, s, f, {==}, R.tr.valid_wf(V, t, e), g, free.m(V, t, s, U32.sub(size, 1), e, h))

def el.go(zs: Bool, inv: Bool, -V: Data, +xs: P.Es(V), +min: U32, +max: U32, +size: U32, +r: U32, +s: U32, +w: {P.wf(V, xs) == True{} : Bool}, +f: {mea(V, zs, inv, xs, min, max, size) == Done{r} : Result<&2, &2, M.MapleError<U32>, U32>}, +g: P.HB(min, s, U32.sub(size, 1), max), hm: P.Free(V, xs, s, U32.sub(size, 1))) -> P.GA(s, Done{r}):
  match zs:
    case True{}:
      Empty.absurd(P.GA(s, Done{r}), ab.fail_done(M.MapleBadSize{}, r, f))
    case False{}:
      match inv:
        case True{}:
          Empty.absurd(P.GA(s, Done{r}), ab.fail_done(M.MapleBadRange{min, max}, r, f))
        case False{}:
          %f : P.GA(s, _)
          P.gcomplete(V, xs, min, s, U32.sub(size, 1), max, w, g, hm)

def Laws.empty_area_lowest(V, t, min, max, size, r, s, e, f, g, h):
  el.go(Cmp.is_eq(U32.cmp(size, 0)), O.ult(max, min), V, R.TL(V, t), min, max, size, r, s, R.tr.valid_wf(V, t, e), ea.m(V, t, min, max, size, r, e, f), g, free.m(V, t, s, U32.sub(size, 1), e, h))

# Vectors

def Laws.example_entries():
  {==}

def Laws.example_valid():
  {==}

def Laws.example_balanced():
  {==}

def Laws.example_split():
  {==}

def Laws.example_load():
  {==}

def Laws.example_clear():
  {==}

def Laws.example_erase():
  {==}

def Laws.example_lookup():
  {==}

def Laws.example_lookup_none():
  {==}

def Laws.example_next():
  {==}

def Laws.example_prev():
  {==}

def Laws.example_gap():
  {==}

def Laws.example_gap_busy():
  {==}

def Laws.example_store_inverted():
  {==}

def Laws.example_deep():
  {==}

def Laws.example_in_range():
  {==}

def Laws.example_out_of_range():
  {==}

def Laws.example_inverted():
  {==}

def Laws.example_split_entries():
  {==}

def Laws.example_last_entry():
  {==}

def Laws.example_gap_empty():
  {==}

def Laws.example_holds():
  {==}

def Laws.example_size():
  {==}

def Laws.example_free_run(i, f, g):
  {==}

def Laws.example_free_run_bounds():
  {==}
