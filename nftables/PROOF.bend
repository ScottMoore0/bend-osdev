# Proofs of LAWS.bend.
#
# The plan:
# * Sets: insertion walks the sorted elements and puts the new one before
#   the first it lies below, after one it lies above, or refuses it. So the
#   new list's membership is the old one's or the new element's (a reordered
#   "or"), and the invariant holds because each neighbour relation the new
#   list has is one the insertion tested or one the old list had. Results
#   are carried through Result by small checking functions (okm, okw) that
#   are True on Fail.
# * Depth: every step of a chain's evaluation keeps its depth, except a
#   jump or goto, which takes the maximum with one more than the callee's;
#   the callee runs with one level less fuel, so by induction on the fuel
#   and the rules the depth stays within the fuel.
# * Drop: a drop makes the evaluation's state Done, and Done passes through
#   every later rule and base chain unchanged.
# * No rules: a base chain with no rules returns at once, so its policy
#   decides; the base chains are collected by insertion in priority order,
#   which keeps "every chain has no rules" and "some policy drops", and the
#   latter is the model's scan of the tables.
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ./family.bend as F
import ./verdict.bend as V
import ./sets.bend as S
import ./expr.bend as X
import ./chains.bend as C
import ./eval.bend as E
import ./nftables.bend as N
import ./LAWS.bend as Laws

# Contradictions

def absurd.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def absurd.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : absurd.bool(_)
  Unit{}

def absurd.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : absurd.bool(_)
  Unit{}

def absurd.res(r: Result<&2, &2, F.NftError, S.NftSet>) -> Type:
  match r:
    case Done{x}:
      Empty
    case Fail{e}:
      Unit

def absurd.fail_done(-err: F.NftError, -s: S.NftSet, e: {Fail{err} == Done{s} : Result<&2, &2, F.NftError, S.NftSet>}) -> Empty:
  %e : absurd.res(_)
  Unit{}

def unwrap(r: Result<&2, &2, F.NftError, S.NftSet>) -> S.NftSet:
  match r:
    case Done{x}:
      x
    case Fail{e}:
      S.NftSet.empty()

def done_inj(-a: S.NftSet, -b: S.NftSet, e: {Done{a} == Done{b} : Result<&2, &2, F.NftError, S.NftSet>}) -> {a == b : S.NftSet}:
  Equal.cong(Result<&2, &2, F.NftError, S.NftSet>, S.NftSet, r => unwrap(r), Done{a}, Done{b}, e)

# Bool

def bool.and_l(x: Bool, -y: Bool, e: {Bool.and(x, y) == True{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))

def bool.and_r(x: Bool, -y: Bool, e: {Bool.and(x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      e
    case False{}:
      Empty.absurd({y == True{} : Bool}, absurd.ft(e))

def bool.and_intro(-x: Bool, -y: Bool, ex: {x == True{} : Bool}, ey: {y == True{} : Bool}) -> {Bool.and(x, y) == True{} : Bool}:
  %Equal.sym(Bool, x, True{}, ex) : {Bool.and(_, y) == True{} : Bool}
  ey

def bool.or_false(x: Bool) -> {Bool.or(x, False{}) == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def bool.or_swap(x: Bool, y: Bool, -z: Bool) -> {Bool.or(x, Bool.or(y, z)) == Bool.or(y, Bool.or(x, z)) : Bool}:
  match x:
    case True{}:
      match y:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

# or(b, or(a, c)) == or(or(a, b), c)
def bool.or_rot(a: Bool, b: Bool, -c: Bool) -> {Bool.or(b, Bool.or(a, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def beq(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

def beq.refl(a: Bool) -> {beq(a, a) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def beq.eq(a: Bool, b: Bool, e: {beq(a, b) == True{} : Bool}) -> {a == b : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          Empty.absurd({True{} == False{} : Bool}, absurd.ft(e))
    case False{}:
      match b:
        case True{}:
          Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))
        case False{}:
          {==}

# Sets: membership after insertion

def okm(r: Result<&2, &2, F.NftError, List<&2, S.NftElem>>, +x: B.Octets, want: Bool) -> Bool:
  match r:
    case Done{l}:
      beq(S.NftSet.mem.go(l, x), want)
    case Fail{e}:
      True{}

def ins_mem.pick(b1: Bool, b2: Bool, +e: S.NftElem, +h: S.NftElem, +t: List<&2, S.NftElem>, r: Result<&2, &2, F.NftError, List<&2, S.NftElem>>, +x: B.Octets, ih: {okm(r, x, Bool.or(S.NftElem.contains(e, x), S.NftSet.mem.go(t, x))) == True{} : Bool}) -> {okm(S.NftSet.ins.pick(b1, b2, e, h, t, r), x, Bool.or(S.NftElem.contains(e, x), Bool.or(S.NftElem.contains(h, x), S.NftSet.mem.go(t, x)))) == True{} : Bool}:
  match b1:
    case True{}:
      beq.refl(Bool.or(S.NftElem.contains(e, x), Bool.or(S.NftElem.contains(h, x), S.NftSet.mem.go(t, x))))
    case False{}:
      match b2:
        case True{}:
          match r:
            case Done{l}:
              +me = beq.eq(S.NftSet.mem.go(l, x), Bool.or(S.NftElem.contains(e, x), S.NftSet.mem.go(t, x)), ih)
              %Equal.sym(Bool, S.NftSet.mem.go(l, x), Bool.or(S.NftElem.contains(e, x), S.NftSet.mem.go(t, x)), me) : {beq(Bool.or(S.NftElem.contains(h, x), _), Bool.or(S.NftElem.contains(e, x), Bool.or(S.NftElem.contains(h, x), S.NftSet.mem.go(t, x)))) == True{} : Bool}
              %Equal.sym(Bool, Bool.or(S.NftElem.contains(h, x), Bool.or(S.NftElem.contains(e, x), S.NftSet.mem.go(t, x))), Bool.or(S.NftElem.contains(e, x), Bool.or(S.NftElem.contains(h, x), S.NftSet.mem.go(t, x))), bool.or_swap(S.NftElem.contains(h, x), S.NftElem.contains(e, x), S.NftSet.mem.go(t, x))) : {beq(_, Bool.or(S.NftElem.contains(e, x), Bool.or(S.NftElem.contains(h, x), S.NftSet.mem.go(t, x)))) == True{} : Bool}
              beq.refl(Bool.or(S.NftElem.contains(e, x), Bool.or(S.NftElem.contains(h, x), S.NftSet.mem.go(t, x))))
            case Fail{err}:
              {==}
        case False{}:
          {==}

def ins_mem(es: List<&2, S.NftElem>, +e: S.NftElem, +x: B.Octets) -> {okm(S.NftSet.ins(es, e), x, Bool.or(S.NftElem.contains(e, x), S.NftSet.mem.go(es, x))) == True{} : Bool}:
  match es:
    case Nil{}:
      beq.refl(Bool.or(S.NftElem.contains(e, x), False{}))
    case Con{+h, +t}:
      ins_mem.pick(S.NftKey.lt(S.NftElem.hi(e), S.NftElem.lo(h)), S.NftKey.lt(S.NftElem.hi(h), S.NftElem.lo(e)), e, h, t, S.NftSet.ins(t, e), x, ins_mem(t, e, x))

def mem_done(r: Result<&2, &2, F.NftError, List<&2, S.NftElem>>, +x: B.Octets, +w: Bool, s2: S.NftSet, ok: {S.NftSet.wrap(r) == Done{s2} : Result<&2, &2, F.NftError, S.NftSet>}, h: {okm(r, x, w) == True{} : Bool}) -> {S.NftSet.mem(s2, x) == w : Bool}:
  match r:
    case Done{l}:
      %done_inj(S.NftSet{l}, s2, ok) : {S.NftSet.mem(_, x) == w : Bool}
      beq.eq(S.NftSet.mem.go(l, x), w, h)
    case Fail{err}:
      Empty.absurd({S.NftSet.mem(s2, x) == w : Bool}, absurd.fail_done(err, s2, ok))

def insert_go_mem(v: Bool, +es: List<&2, S.NftElem>, +e: S.NftElem, +x: B.Octets, s2: S.NftSet, ok: {S.NftSet.insert.go(v, es, e) == Done{s2} : Result<&2, &2, F.NftError, S.NftSet>}) -> {S.NftSet.mem(s2, x) == Bool.or(S.NftElem.contains(e, x), S.NftSet.mem.go(es, x)) : Bool}:
  match v:
    case False{}:
      Empty.absurd({S.NftSet.mem(s2, x) == Bool.or(S.NftElem.contains(e, x), S.NftSet.mem.go(es, x)) : Bool}, absurd.fail_done(F.NftErrBadInterval{}, s2, ok))
    case True{}:
      mem_done(S.NftSet.ins(es, e), x, Bool.or(S.NftElem.contains(e, x), S.NftSet.mem.go(es, x)), s2, ok, ins_mem(es, e, x))

def Laws.set_mem_insert(s, e, x, s2, ok):
  match s:
    case S.NftSet{es}:
      insert_go_mem(S.NftElem.valid(e), es, e, x, s2, ok)

# Sets: the invariant after insertion

def okw(r: Result<&2, &2, F.NftError, List<&2, S.NftElem>>) -> Bool:
  match r:
    case Done{l}:
      S.NftSet.wf.go(l)
    case Fail{e}:
      True{}

def oks(a: S.NftElem, r: Result<&2, &2, F.NftError, List<&2, S.NftElem>>) -> Bool:
  match r:
    case Done{l}:
      S.NftSet.sep(a, l)
    case Fail{e}:
      True{}

def ins_sep.pick(b1: Bool, b2: Bool, +a: S.NftElem, +e: S.NftElem, +h: S.NftElem, +t: List<&2, S.NftElem>, r: Result<&2, &2, F.NftError, List<&2, S.NftElem>>, hs: {S.NftKey.lt(S.NftElem.hi(a), S.NftElem.lo(h)) == True{} : Bool}, ha: {S.NftKey.lt(S.NftElem.hi(a), S.NftElem.lo(e)) == True{} : Bool}) -> {oks(a, S.NftSet.ins.pick(b1, b2, e, h, t, r)) == True{} : Bool}:
  match b1:
    case True{}:
      ha
    case False{}:
      match b2:
        case True{}:
          match r:
            case Done{l}:
              hs
            case Fail{err}:
              {==}
        case False{}:
          {==}

def ins_sep(es: List<&2, S.NftElem>, +a: S.NftElem, +e: S.NftElem, hs: {S.NftSet.sep(a, es) == True{} : Bool}, ha: {S.NftKey.lt(S.NftElem.hi(a), S.NftElem.lo(e)) == True{} : Bool}) -> {oks(a, S.NftSet.ins(es, e)) == True{} : Bool}:
  match es:
    case Nil{}:
      ha
    case Con{+h, +t}:
      ins_sep.pick(S.NftKey.lt(S.NftElem.hi(e), S.NftElem.lo(h)), S.NftKey.lt(S.NftElem.hi(h), S.NftElem.lo(e)), a, e, h, t, S.NftSet.ins(t, e), hs, ha)

def ins_wf.pick(b1: Bool, b2: Bool, +e: S.NftElem, +h: S.NftElem, +t: List<&2, S.NftElem>, eq1: {S.NftKey.lt(S.NftElem.hi(e), S.NftElem.lo(h)) == b1 : Bool}, eq2: {S.NftKey.lt(S.NftElem.hi(h), S.NftElem.lo(e)) == b2 : Bool}, r: Result<&2, &2, F.NftError, List<&2, S.NftElem>>, hv: {S.NftElem.valid(e) == True{} : Bool}, +hw: {S.NftSet.wf.go(Con{h, t}) == True{} : Bool}, sp: {S.NftKey.lt(S.NftElem.hi(h), S.NftElem.lo(e)) == True{} : Bool} -> {oks(h, r) == True{} : Bool}, ih: {okw(r) == True{} : Bool}) -> {okw(S.NftSet.ins.pick(b1, b2, e, h, t, r)) == True{} : Bool}:
  match b1:
    case True{}:
      bool.and_intro(S.NftElem.valid(e), Bool.and(S.NftKey.lt(S.NftElem.hi(e), S.NftElem.lo(h)), S.NftSet.wf.go(Con{h, t})), hv, bool.and_intro(S.NftKey.lt(S.NftElem.hi(e), S.NftElem.lo(h)), S.NftSet.wf.go(Con{h, t}), eq1, hw))
    case False{}:
      match b2:
        case True{}:
          match r:
            case Done{l}:
              +vh = bool.and_l(S.NftElem.valid(h), Bool.and(S.NftSet.sep(h, t), S.NftSet.wf.go(t)), hw)
              bool.and_intro(S.NftElem.valid(h), Bool.and(S.NftSet.sep(h, l), S.NftSet.wf.go(l)), vh, bool.and_intro(S.NftSet.sep(h, l), S.NftSet.wf.go(l), sp(eq2), ih))
            case Fail{err}:
              {==}
        case False{}:
          {==}

def ins_wf(es: List<&2, S.NftElem>, +e: S.NftElem, +hv: {S.NftElem.valid(e) == True{} : Bool}, hw: {S.NftSet.wf.go(es) == True{} : Bool}) -> {okw(S.NftSet.ins(es, e)) == True{} : Bool}:
  match es:
    case Nil{}:
      %Equal.sym(Bool, S.NftElem.valid(e), True{}, hv) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case Con{+h, +t}:
      +hw = hw
      +rest = bool.and_r(S.NftElem.valid(h), Bool.and(S.NftSet.sep(h, t), S.NftSet.wf.go(t)), hw)
      +hs = bool.and_l(S.NftSet.sep(h, t), S.NftSet.wf.go(t), rest)
      +ht = bool.and_r(S.NftSet.sep(h, t), S.NftSet.wf.go(t), rest)
      ins_wf.pick(S.NftKey.lt(S.NftElem.hi(e), S.NftElem.lo(h)), S.NftKey.lt(S.NftElem.hi(h), S.NftElem.lo(e)), e, h, t, {==}, {==}, S.NftSet.ins(t, e), hv, hw, k => ins_sep(t, h, e, hs, k), ins_wf(t, e, hv, ht))

def wf_done(r: Result<&2, &2, F.NftError, List<&2, S.NftElem>>, s2: S.NftSet, ok: {S.NftSet.wrap(r) == Done{s2} : Result<&2, &2, F.NftError, S.NftSet>}, h: {okw(r) == True{} : Bool}) -> {S.NftSet.wf(s2) == True{} : Bool}:
  match r:
    case Done{l}:
      %done_inj(S.NftSet{l}, s2, ok) : {S.NftSet.wf(_) == True{} : Bool}
      h
    case Fail{err}:
      Empty.absurd({S.NftSet.wf(s2) == True{} : Bool}, absurd.fail_done(err, s2, ok))

def insert_go_wf(v: Bool, +e: S.NftElem, eqv: {S.NftElem.valid(e) == v : Bool}, +es: List<&2, S.NftElem>, s2: S.NftSet, hw: {S.NftSet.wf.go(es) == True{} : Bool}, ok: {S.NftSet.insert.go(v, es, e) == Done{s2} : Result<&2, &2, F.NftError, S.NftSet>}) -> {S.NftSet.wf(s2) == True{} : Bool}:
  match v:
    case False{}:
      Empty.absurd({S.NftSet.wf(s2) == True{} : Bool}, absurd.fail_done(F.NftErrBadInterval{}, s2, ok))
    case True{}:
      wf_done(S.NftSet.ins(es, e), s2, ok, ins_wf(es, e, eqv, hw))

def Laws.set_wf_insert(s, e, s2, wf, ok):
  match s:
    case S.NftSet{es}:
      insert_go_wf(S.NftElem.valid(e), e, {==}, es, s2, wf, ok)

# Maps: lookup finds an element exactly when the key is in

def lookup_mem.pick(b: Bool, -d: S.NftData, -rest: Maybe<&2, S.NftData>, -m: Bool, ih: {Laws.is_some(rest) == m : Bool}) -> {Laws.is_some(S.NftSet.lookup.pick(b, d, rest)) == Bool.or(b, m) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def lookup_mem(es: List<&2, S.NftElem>, +x: B.Octets) -> {Laws.is_some(S.NftSet.lookup.go(es, x)) == S.NftSet.mem.go(es, x) : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      lookup_mem.pick(S.NftElem.contains(e, x), S.NftElem.data(e), S.NftSet.lookup.go(t, x), S.NftSet.mem.go(t, x), lookup_mem(t, x))

def Laws.map_lookup_mem(s, x):
  match s:
    case S.NftSet{es}:
      lookup_mem(es, x)

# Sets built from a list

def okm2(r: Result<&2, &2, F.NftError, S.NftSet>, +x: B.Octets, want: Bool) -> Bool:
  match r:
    case Done{s}:
      beq(S.NftSet.mem(s, x), want)
    case Fail{e}:
      True{}

def add_mem.ins(+s0: S.NftSet, +e: S.NftElem, r2: Result<&2, &2, F.NftError, S.NftSet>, eq: {S.NftSet.insert(s0, e) == r2 : Result<&2, &2, F.NftError, S.NftSet>}, +x: B.Octets, +w: Bool, h: {beq(S.NftSet.mem(s0, x), w) == True{} : Bool}) -> {okm2(r2, x, Bool.or(S.NftElem.contains(e, x), w)) == True{} : Bool}:
  match r2:
    case Done{s2}:
      +mi = Laws.set_mem_insert(s0, e, x, s2, eq)
      +mw = beq.eq(S.NftSet.mem(s0, x), w, h)
      %Equal.sym(Bool, S.NftSet.mem(s2, x), Bool.or(S.NftElem.contains(e, x), S.NftSet.mem(s0, x)), mi) : {beq(_, Bool.or(S.NftElem.contains(e, x), w)) == True{} : Bool}
      %Equal.sym(Bool, S.NftSet.mem(s0, x), w, mw) : {beq(Bool.or(S.NftElem.contains(e, x), _), Bool.or(S.NftElem.contains(e, x), w)) == True{} : Bool}
      beq.refl(Bool.or(S.NftElem.contains(e, x), w))
    case Fail{err}:
      {==}

def add_mem(r: Result<&2, &2, F.NftError, S.NftSet>, +e: S.NftElem, +x: B.Octets, +w: Bool, h: {okm2(r, x, w) == True{} : Bool}) -> {okm2(S.NftSet.add(r, e), x, Bool.or(S.NftElem.contains(e, x), w)) == True{} : Bool}:
  match r:
    case Done{+s0}:
      add_mem.ins(s0, e, S.NftSet.insert(s0, e), {==}, x, w, h)
    case Fail{err}:
      {==}

def of_list_mem(es: List<&2, S.NftElem>, +r: Result<&2, &2, F.NftError, S.NftSet>, +x: B.Octets, +w: Bool, h: {okm2(r, x, w) == True{} : Bool}) -> {okm2(S.NftSet.of_list.go(es, r), x, Bool.or(Laws.list_mem(es, x), w)) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case Con{+e, +t}:
      %bool.or_rot(S.NftElem.contains(e, x), Laws.list_mem(t, x), w) : {okm2(S.NftSet.of_list.go(t, S.NftSet.add(r, e)), x, _) == True{} : Bool}
      of_list_mem(t, S.NftSet.add(r, e), x, Bool.or(S.NftElem.contains(e, x), w), add_mem(r, e, x, w, h))

def okm2_done(r: Result<&2, &2, F.NftError, S.NftSet>, s: S.NftSet, +x: B.Octets, +w: Bool, ok: {r == Done{s} : Result<&2, &2, F.NftError, S.NftSet>}, h: {okm2(r, x, w) == True{} : Bool}) -> {S.NftSet.mem(s, x) == w : Bool}:
  match r:
    case Done{s1}:
      %done_inj(s1, s, ok) : {S.NftSet.mem(_, x) == w : Bool}
      beq.eq(S.NftSet.mem(s1, x), w, h)
    case Fail{err}:
      Empty.absurd({S.NftSet.mem(s, x) == w : Bool}, absurd.fail_done(err, s, ok))

def Laws.set_mem_of_list(es, s, x, ok):
  +m = okm2_done(S.NftSet.of_list(es), s, x, Bool.or(Laws.list_mem(es, x), False{}), ok, of_list_mem(es, Done{S.NftSet.empty()}, x, False{}, {==}))
  Equal.trans(Bool, S.NftSet.mem(s, x), Bool.or(Laws.list_mem(es, x), False{}), Laws.list_mem(es, x), m, bool.or_false(Laws.list_mem(es, x)))

def okw2(r: Result<&2, &2, F.NftError, S.NftSet>) -> Bool:
  match r:
    case Done{s}:
      S.NftSet.wf(s)
    case Fail{e}:
      True{}

def add_wf.ins(+s0: S.NftSet, +e: S.NftElem, r2: Result<&2, &2, F.NftError, S.NftSet>, eq: {S.NftSet.insert(s0, e) == r2 : Result<&2, &2, F.NftError, S.NftSet>}, h: {S.NftSet.wf(s0) == True{} : Bool}) -> {okw2(r2) == True{} : Bool}:
  match r2:
    case Done{s2}:
      Laws.set_wf_insert(s0, e, s2, h, eq)
    case Fail{err}:
      {==}

def add_wf(r: Result<&2, &2, F.NftError, S.NftSet>, +e: S.NftElem, h: {okw2(r) == True{} : Bool}) -> {okw2(S.NftSet.add(r, e)) == True{} : Bool}:
  match r:
    case Done{+s0}:
      add_wf.ins(s0, e, S.NftSet.insert(s0, e), {==}, h)
    case Fail{err}:
      {==}

def of_list_wf(es: List<&2, S.NftElem>, +r: Result<&2, &2, F.NftError, S.NftSet>, h: {okw2(r) == True{} : Bool}) -> {okw2(S.NftSet.of_list.go(es, r)) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case Con{+e, +t}:
      of_list_wf(t, S.NftSet.add(r, e), add_wf(r, e, h))

def okw2_done(r: Result<&2, &2, F.NftError, S.NftSet>, s: S.NftSet, ok: {r == Done{s} : Result<&2, &2, F.NftError, S.NftSet>}, h: {okw2(r) == True{} : Bool}) -> {S.NftSet.wf(s) == True{} : Bool}:
  match r:
    case Done{s1}:
      %done_inj(s1, s, ok) : {S.NftSet.wf(_) == True{} : Bool}
      h
    case Fail{err}:
      Empty.absurd({S.NftSet.wf(s) == True{} : Bool}, absurd.fail_done(err, s, ok))

def Laws.set_wf_of_list(es, s, ok):
  okw2_done(S.NftSet.of_list(es), s, ok, of_list_wf(es, Done{S.NftSet.empty()}, {==}))

# Nat

def nat.le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nat.max_le(a: Nat, b: Nat, c: Nat, ha: {Nat.is_le(a, c) == True{} : Bool}, hb: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(Nat.max(a, b), c) == True{} : Bool}:
  match a b:
    case 0n _:
      hb
    case 1n+ap 0n:
      ha
    case 1n+ap 1n+bp:
      match c:
        case 0n:
          Empty.absurd({Nat.is_le(Nat.max(1n+ap, 1n+bp), 0n) == True{} : Bool}, absurd.ft(ha))
        case 1n+cp:
          nat.max_le(ap, bp, cp, ha, hb)

# Depth: each step keeps the depth within the bound

def le.of_rule(o: X.NftRuleOut, -d: Nat, -n: Nat, h: {Nat.is_le(d, n) == True{} : Bool}) -> {Nat.is_le(E.NftRun.depth(E.NftRun.of_rule(o, d)), n) == True{} : Bool}:
  match o:
    case X.NftRuleNext{env}:
      h
    case X.NftRuleVerdict{v, env}:
      h

def le.step(r: X.NftRule, +sets: List<&2, S.NftNamedSet>, a: E.NftRun, -n: Nat, h: {Nat.is_le(E.NftRun.depth(a), n) == True{} : Bool}) -> {Nat.is_le(E.NftRun.depth(E.NftRun.step(r, sets, a)), n) == True{} : Bool}:
  match a:
    case E.NftRun{p, env, d}:
      match p:
        case E.NftPendNext{}:
          le.of_rule(X.NftRule.eval(r, sets, env), d, n, h)
        case E.NftPendJump{c}:
          h
        case E.NftPendGoto{c}:
          h
        case E.NftPendDone{x}:
          h

def le.fin(a: E.NftRun, -n: Nat, h: {Nat.is_le(E.NftRun.depth(a), n) == True{} : Bool}) -> {Nat.is_le(E.NftRun.depth(E.NftRun.fin(a)), n) == True{} : Bool}:
  match a:
    case E.NftRun{p, env, d}:
      match p:
        case E.NftPendNext{}:
          h
        case E.NftPendJump{c}:
          h
        case E.NftPendGoto{c}:
          h
        case E.NftPendDone{x}:
          h

def le.cut(a: E.NftRun, -opts: E.NftOptions, -n: Nat, h: {Nat.is_le(E.NftRun.depth(a), n) == True{} : Bool}) -> {Nat.is_le(E.NftRun.depth(E.NftRun.cut(a, opts)), n) == True{} : Bool}:
  match a:
    case E.NftRun{p, env, d}:
      match p:
        case E.NftPendNext{}:
          h
        case E.NftPendJump{c}:
          h
        case E.NftPendGoto{c}:
          h
        case E.NftPendDone{x}:
          h

def le.join.go(r: E.NftChainRes, -env: X.NftEnv, -dd: Nat, -n: Nat, h: {Nat.is_le(dd, n) == True{} : Bool}) -> {Nat.is_le(E.NftRun.depth(E.NftRun.join.go(r, env, dd)), n) == True{} : Bool}:
  match r:
    case E.NftChainReturn{}:
      h
    case E.NftChainStop{f}:
      h

def le.join(found: Bool, +callee: E.NftRun, +d: Nat, -opts: E.NftOptions, -env: X.NftEnv, +q: Nat, hd: {Nat.is_le(d, 1n+q) == True{} : Bool}, hc: {Nat.is_le(E.NftRun.depth(callee), q) == True{} : Bool}) -> {Nat.is_le(E.NftRun.depth(E.NftRun.join(found, callee, d, opts, env)), 1n+q) == True{} : Bool}:
  match found:
    case False{}:
      hd
    case True{}:
      le.join.go(E.NftRun.result(callee), E.NftRun.env(callee), Nat.max(d, 1n+E.NftRun.depth(callee)), 1n+q, nat.max_le(d, 1n+E.NftRun.depth(callee), 1n+q, hd, hc))

def le.goto(found: Bool, +callee: E.NftRun, +d: Nat, -opts: E.NftOptions, -env: X.NftEnv, +q: Nat, hd: {Nat.is_le(d, 1n+q) == True{} : Bool}, hc: {Nat.is_le(E.NftRun.depth(callee), q) == True{} : Bool}) -> {Nat.is_le(E.NftRun.depth(E.NftRun.goto(found, callee, d, opts, env)), 1n+q) == True{} : Bool}:
  match found:
    case False{}:
      hd
    case True{}:
      nat.max_le(d, 1n+E.NftRun.depth(callee), 1n+q, hd, hc)

def dep.run(+fuel: Nat, rules: List<&2, X.NftRule>, +tbl: C.NftTable, +opts: E.NftOptions, +a: E.NftRun, h: {Nat.is_le(E.NftRun.depth(a), fuel) == True{} : Bool}) -> {Nat.is_le(E.NftRun.depth(E.NftRun.run(fuel, rules, tbl, opts, a)), fuel) == True{} : Bool}:
  match fuel:
    case 0n:
      match rules:
        case Nil{}:
          le.fin(E.NftRun.cut(a, opts), 0n, le.cut(a, opts, 0n, h))
        case Con{+r, rest}:
          dep.run(fuel, rest, tbl, opts, E.NftRun.step(r, C.NftTable.sets(tbl), E.NftRun.cut(a, opts)), le.step(r, C.NftTable.sets(tbl), E.NftRun.cut(a, opts), 0n, le.cut(a, opts, 0n, h)))
    case 1n+q:
      match rules:
        case Nil{}:
          match a:
            case E.NftRun{p, +env, +d}:
              match p:
                case E.NftPendNext{}:
                  h
                case E.NftPendDone{x}:
                  h
                case E.NftPendJump{+c}:
                  +callee = E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env, 0n})
                  le.fin(E.NftRun.join(C.NftTable.has_chain(tbl, c), callee, d, opts, env), 1n+q, le.join(C.NftTable.has_chain(tbl, c), callee, d, opts, env, q, h, dep.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env, 0n}, nat.le0(q))))
                case E.NftPendGoto{+c}:
                  +callee = E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env, 0n})
                  le.goto(C.NftTable.has_chain(tbl, c), callee, d, opts, env, q, h, dep.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env, 0n}, nat.le0(q)))
        case Con{+r, rest}:
          match a:
            case E.NftRun{p, +env, +d}:
              match p:
                case E.NftPendNext{}:
                  dep.run(fuel, rest, tbl, opts, E.NftRun.of_rule(X.NftRule.eval(r, C.NftTable.sets(tbl), env), d), le.of_rule(X.NftRule.eval(r, C.NftTable.sets(tbl), env), d, 1n+q, h))
                case E.NftPendDone{x}:
                  h
                case E.NftPendJump{+c}:
                  +callee = E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env, 0n})
                  +j = E.NftRun.join(C.NftTable.has_chain(tbl, c), callee, d, opts, env)
                  dep.run(fuel, rest, tbl, opts, E.NftRun.step(r, C.NftTable.sets(tbl), j), le.step(r, C.NftTable.sets(tbl), j, 1n+q, le.join(C.NftTable.has_chain(tbl, c), callee, d, opts, env, q, h, dep.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env, 0n}, nat.le0(q)))))
                case E.NftPendGoto{+c}:
                  +callee = E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env, 0n})
                  le.goto(C.NftTable.has_chain(tbl, c), callee, d, opts, env, q, h, dep.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env, 0n}, nat.le0(q)))

def Laws.chain_depth_bound(opts, fuel, tbl, rules, env):
  dep.run(fuel, rules, tbl, opts, E.NftRun{E.NftPendNext{}, env, 0n}, nat.le0(fuel))

def le.out(r: E.NftChainRes, pol: V.NftPolicy, -env: X.NftEnv, -d: Nat, -n: Nat, h: {Nat.is_le(d, n) == True{} : Bool}) -> {Nat.is_le(E.NftOut.depth(E.NftBase.out(r, pol, env, d)), n) == True{} : Bool}:
  match r:
    case E.NftChainReturn{}:
      match pol:
        case V.NftPolicyAccept{}:
          h
        case V.NftPolicyDrop{}:
          h
    case E.NftChainStop{f}:
      match f:
        case V.NftFinalAccept{}:
          h
        case V.NftFinalDrop{}:
          h
        case V.NftFinalReject{w}:
          h
        case V.NftFinalQueue{k, b}:
          h

def le.base(+opts: E.NftOptions, h: C.NftHooked, +env: X.NftEnv) -> {Nat.is_le(E.NftOut.depth(E.Nft.run_base(opts, h, env)), E.NftOptions.max_depth(opts)) == True{} : Bool}:
  match h:
    case C.NftHooked{+tbl, +rules, prio, pol}:
      +r = E.Nft.run_chain(opts, E.NftOptions.max_depth(opts), tbl, rules, env)
      le.out(E.NftRun.result(r), pol, E.NftRun.env(r), E.NftRun.depth(r), E.NftOptions.max_depth(opts), Laws.chain_depth_bound(opts, E.NftOptions.max_depth(opts), tbl, rules, env))

def le.hook(hs: List<&2, C.NftHooked>, +opts: E.NftOptions, acc: E.NftOut, h: {Nat.is_le(E.NftOut.depth(acc), E.NftOptions.max_depth(opts)) == True{} : Bool}) -> {Nat.is_le(E.NftOut.depth(E.NftHookRun.go(hs, opts, acc)), E.NftOptions.max_depth(opts)) == True{} : Bool}:
  match hs:
    case Nil{}:
      h
    case Con{+x, t}:
      match acc:
        case E.NftOut{f, +env, +d}:
          match f:
            case None{}:
              le.hook(t, opts, E.NftHookRun.combine(E.Nft.run_base(opts, x, env), d), nat.max_le(d, E.NftOut.depth(E.Nft.run_base(opts, x, env)), E.NftOptions.max_depth(opts), h, le.base(opts, x, env)))
            case Some{y}:
              h

def le.result(o: E.NftOut, -n: Nat, h: {Nat.is_le(E.NftOut.depth(o), n) == True{} : Bool}) -> {Nat.is_le(N.NftResult.depth(N.NftResult.of(o)), n) == True{} : Bool}:
  match o:
    case E.NftOut{f, env, d}:
      match env:
        case X.NftEnv{p, s, w}:
          h

def Laws.eval_depth_bound(opts, rs, proto, hook, now, pkt, st):
  +hs = C.NftRuleset.base_chains(rs, proto, hook)
  +env = {X.NftEnv{pkt, st, now} : X.NftEnv}
  le.result(E.Nft.run_hook(opts, hs, env), E.NftOptions.max_depth(opts), le.hook(hs, opts, E.NftOut{None{}, env, 0n}, nat.le0(E.NftOptions.max_depth(opts))))

# Drop: Done passes through every later rule

def DROP() -> E.NftChainRes:
  E.NftChainStop{V.NftFinalDrop{}}

def res(+fuel: Nat, rules: List<&2, X.NftRule>, +tbl: C.NftTable, +opts: E.NftOptions, a: E.NftRun) -> E.NftChainRes:
  E.NftRun.result(E.NftRun.run(fuel, rules, tbl, opts, a))

def done.run(+fuel: Nat, rules: List<&2, X.NftRule>, +tbl: C.NftTable, +opts: E.NftOptions, +x: E.NftChainRes, +env: X.NftEnv, +d: Nat) -> {E.NftRun.run(fuel, rules, tbl, opts, E.NftRun{E.NftPendDone{x}, env, d}) == E.NftRun{E.NftPendDone{x}, env, d} : E.NftRun}:
  match fuel:
    case 0n:
      match rules:
        case Nil{}:
          {==}
        case Con{r, rest}:
          done.run(fuel, rest, tbl, opts, x, env, d)
    case 1n+q:
      match rules:
        case Nil{}:
          {==}
        case Con{r, rest}:
          {==}

def done.res(+fuel: Nat, rules: List<&2, X.NftRule>, +tbl: C.NftTable, +opts: E.NftOptions, +x: E.NftChainRes, +env: X.NftEnv, +d: Nat) -> {res(fuel, rules, tbl, opts, E.NftRun{E.NftPendDone{x}, env, d}) == x : E.NftChainRes}:
  %Equal.sym(E.NftRun, E.NftRun.run(fuel, rules, tbl, opts, E.NftRun{E.NftPendDone{x}, env, d}), E.NftRun{E.NftPendDone{x}, env, d}, done.run(fuel, rules, tbl, opts, x, env, d)) : {E.NftRun.result(_) == x : E.NftChainRes}
  {==}

def Laws.drop_rule_final(opts, fuel, tbl, r, rest, env, env2, drops):
  match fuel:
    case 0n:
      %Equal.sym(X.NftRuleOut, X.NftRule.eval(r, C.NftTable.sets(tbl), env), X.NftRuleVerdict{V.NftDrop{}, env2}, drops) : {res(0n, rest, tbl, opts, E.NftRun.of_rule(_, 0n)) == DROP() : E.NftChainRes}
      done.res(0n, rest, tbl, opts, DROP(), env2, 0n)
    case 1n+q:
      %Equal.sym(X.NftRuleOut, X.NftRule.eval(r, C.NftTable.sets(tbl), env), X.NftRuleVerdict{V.NftDrop{}, env2}, drops) : {res(1n+q, rest, tbl, opts, E.NftRun.of_rule(_, 0n)) == DROP() : E.NftChainRes}
      done.res(1n+q, rest, tbl, opts, DROP(), env2, 0n)

# after a jump to chain c, which exists and drops
def jd.join(+tbl: C.NftTable, +c: String, +callee: E.NftRun, +d: Nat, +opts: E.NftOptions, env: X.NftEnv, found: {C.NftTable.has_chain(tbl, c) == True{} : Bool}, hd: {E.NftRun.result(callee) == DROP() : E.NftChainRes}) -> {E.NftRun.join(C.NftTable.has_chain(tbl, c), callee, d, opts, env) == E.NftRun{E.NftPendDone{DROP()}, E.NftRun.env(callee), Nat.max(d, 1n+E.NftRun.depth(callee))} : E.NftRun}:
  %Equal.sym(Bool, C.NftTable.has_chain(tbl, c), True{}, found) : {E.NftRun.join(_, callee, d, opts, env) == E.NftRun{E.NftPendDone{DROP()}, E.NftRun.env(callee), Nat.max(d, 1n+E.NftRun.depth(callee))} : E.NftRun}
  %Equal.sym(E.NftChainRes, E.NftRun.result(callee), DROP(), hd) : {E.NftRun.join.go(_, E.NftRun.env(callee), Nat.max(d, 1n+E.NftRun.depth(callee))) == E.NftRun{E.NftPendDone{DROP()}, E.NftRun.env(callee), Nat.max(d, 1n+E.NftRun.depth(callee))} : E.NftRun}
  {==}

def jd.after(+q: Nat, rest: List<&2, X.NftRule>, +tbl: C.NftTable, +opts: E.NftOptions, +c: String, +env2: X.NftEnv, +found: {C.NftTable.has_chain(tbl, c) == True{} : Bool}, +drops: {E.NftRun.result(E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env2, 0n})) == DROP() : E.NftChainRes}) -> {res(1n+q, rest, tbl, opts, E.NftRun{E.NftPendJump{c}, env2, 0n}) == DROP() : E.NftChainRes}:
  match rest:
    case Nil{}:
      +callee = E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env2, 0n})
      %Equal.sym(E.NftRun, E.NftRun.join(C.NftTable.has_chain(tbl, c), callee, 0n, opts, env2), E.NftRun{E.NftPendDone{DROP()}, E.NftRun.env(callee), Nat.max(0n, 1n+E.NftRun.depth(callee))}, jd.join(tbl, c, callee, 0n, opts, env2, found, drops)) : {E.NftRun.result(E.NftRun.fin(_)) == DROP() : E.NftChainRes}
      {==}
    case Con{r2, rest2}:
      +callee = E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env2, 0n})
      %Equal.sym(E.NftRun, E.NftRun.join(C.NftTable.has_chain(tbl, c), callee, 0n, opts, env2), E.NftRun{E.NftPendDone{DROP()}, E.NftRun.env(callee), Nat.max(0n, 1n+E.NftRun.depth(callee))}, jd.join(tbl, c, callee, 0n, opts, env2, found, drops)) : {res(1n+q, rest2, tbl, opts, E.NftRun.step(r2, C.NftTable.sets(tbl), _)) == DROP() : E.NftChainRes}
      done.res(1n+q, rest2, tbl, opts, DROP(), E.NftRun.env(callee), Nat.max(0n, 1n+E.NftRun.depth(callee)))

def Laws.drop_through_jump(opts, q, tbl, r, rest, env, c, env2, jumps, found, drops):
  %Equal.sym(X.NftRuleOut, X.NftRule.eval(r, C.NftTable.sets(tbl), env), X.NftRuleVerdict{V.NftJump{c}, env2}, jumps) : {res(1n+q, rest, tbl, opts, E.NftRun.of_rule(_, 0n)) == DROP() : E.NftChainRes}
  jd.after(q, rest, tbl, opts, c, env2, found, drops)

# goto: the gone-to chain's result and packet are the chain's

def go.after(+q: Nat, rest: List<&2, X.NftRule>, +tbl: C.NftTable, +opts: E.NftOptions, +c: String, +env2: X.NftEnv, +found: {C.NftTable.has_chain(tbl, c) == True{} : Bool}) -> {E.NftRun.run(1n+q, rest, tbl, opts, E.NftRun{E.NftPendGoto{c}, env2, 0n}) == E.NftRun.goto(True{}, E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env2, 0n}), 0n, opts, env2) : E.NftRun}:
  match rest:
    case Nil{}:
      %Equal.sym(Bool, C.NftTable.has_chain(tbl, c), True{}, found) : {E.NftRun.goto(_, E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env2, 0n}), 0n, opts, env2) == E.NftRun.goto(True{}, E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env2, 0n}), 0n, opts, env2) : E.NftRun}
      {==}
    case Con{r2, rest2}:
      %Equal.sym(Bool, C.NftTable.has_chain(tbl, c), True{}, found) : {E.NftRun.goto(_, E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env2, 0n}), 0n, opts, env2) == E.NftRun.goto(True{}, E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env2, 0n}), 0n, opts, env2) : E.NftRun}
      {==}

def go.chain(+opts: E.NftOptions, +q: Nat, +tbl: C.NftTable, r: X.NftRule, rest: List<&2, X.NftRule>, env: X.NftEnv, +c: String, +env2: X.NftEnv, goes: {X.NftRule.eval(r, C.NftTable.sets(tbl), env) == X.NftRuleVerdict{V.NftGoto{c}, env2} : X.NftRuleOut}, +found: {C.NftTable.has_chain(tbl, c) == True{} : Bool}) -> {E.Nft.run_chain(opts, 1n+q, tbl, Con{r, rest}, env) == E.NftRun.goto(True{}, E.Nft.run_chain(opts, q, tbl, C.NftTable.rules(tbl, c), env2), 0n, opts, env2) : E.NftRun}:
  %Equal.sym(X.NftRuleOut, X.NftRule.eval(r, C.NftTable.sets(tbl), env), X.NftRuleVerdict{V.NftGoto{c}, env2}, goes) : {E.NftRun.run(1n+q, rest, tbl, opts, E.NftRun.of_rule(_, 0n)) == E.NftRun.goto(True{}, E.Nft.run_chain(opts, q, tbl, C.NftTable.rules(tbl, c), env2), 0n, opts, env2) : E.NftRun}
  go.after(q, rest, tbl, opts, c, env2, found)

def Laws.drop_through_goto(opts, q, tbl, r, rest, env, c, env2, goes, found, drops):
  %Equal.sym(E.NftRun, E.Nft.run_chain(opts, 1n+q, tbl, Con{r, rest}, env), E.NftRun.goto(True{}, E.Nft.run_chain(opts, q, tbl, C.NftTable.rules(tbl, c), env2), 0n, opts, env2), go.chain(opts, q, tbl, r, rest, env, c, env2, goes, found)) : {E.NftRun.result(_) == DROP() : E.NftChainRes}
  drops

def Laws.goto_result(opts, q, tbl, r, rest, env, c, env2, goes, found):
  %Equal.sym(E.NftRun, E.Nft.run_chain(opts, 1n+q, tbl, Con{r, rest}, env), E.NftRun.goto(True{}, E.Nft.run_chain(opts, q, tbl, C.NftTable.rules(tbl, c), env2), 0n, opts, env2), go.chain(opts, q, tbl, r, rest, env, c, env2, goes, found)) : {E.NftRun.result(_) == E.NftRun.result(E.Nft.run_chain(opts, q, tbl, C.NftTable.rules(tbl, c), env2)) : E.NftChainRes}
  {==}

def Laws.goto_returns(opts, q, tbl, r, rest, env, c, env2, goes, found):
  %Equal.sym(E.NftRun, E.Nft.run_chain(opts, 1n+q, tbl, Con{r, rest}, env), E.NftRun.goto(True{}, E.Nft.run_chain(opts, q, tbl, C.NftTable.rules(tbl, c), env2), 0n, opts, env2), go.chain(opts, q, tbl, r, rest, env, c, env2, goes, found)) : {E.NftRun.env(_) == E.NftRun.env(E.Nft.run_chain(opts, q, tbl, C.NftTable.rules(tbl, c), env2)) : X.NftEnv}
  {==}

# Drop ends the hook

def hk.absorb(hs: List<&2, C.NftHooked>, +opts: E.NftOptions, +x: V.NftFinal, +env: X.NftEnv, +d: Nat) -> {E.NftHookRun.go(hs, opts, E.NftOut{Some{x}, env, d}) == E.NftOut{Some{x}, env, d} : E.NftOut}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def Laws.drop_ends_hook(opts, h, rest, env, drops):
  +o = E.Nft.run_base(opts, h, env)
  %Equal.sym(Maybe<&2, V.NftFinal>, E.NftOut.final(o), Some{V.NftFinalDrop{}}, drops) : {E.NftHookRun.go(rest, opts, E.NftOut{_, E.NftOut.env(o), Nat.max(0n, E.NftOut.depth(o))}) == E.NftOut{Some{V.NftFinalDrop{}}, E.NftOut.env(o), E.NftOut.depth(o)} : E.NftOut}
  hk.absorb(rest, opts, V.NftFinalDrop{}, E.NftOut.env(o), E.NftOut.depth(o))

# No rules: every base chain returns at once, and its policy decides

def hk.empty(h: C.NftHooked) -> Bool:
  match h:
    case C.NftHooked{t, rs, p, pol}:
      match rs:
        case Nil{}:
          True{}
        case Con{r, rr}:
          False{}

def hk.all_empty(hs: List<&2, C.NftHooked>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(hk.empty(h), hk.all_empty(t))

def hk.drops(h: C.NftHooked) -> Bool:
  match h:
    case C.NftHooked{t, rs, p, pol}:
      Bool.not(V.NftPolicy.accepts(pol))

def hk.any_drop(hs: List<&2, C.NftHooked>) -> Bool:
  match hs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(hk.drops(h), hk.any_drop(t))

def hk.out(b: Bool, env: X.NftEnv) -> E.NftOut:
  match b:
    case True{}:
      E.NftOut{Some{V.NftFinalDrop{}}, env, 0n}
    case False{}:
      E.NftOut{None{}, env, 0n}

def run_nil(+fuel: Nat, +tbl: C.NftTable, +opts: E.NftOptions, +env: X.NftEnv) -> {E.NftRun.run(fuel, Nil{}, tbl, opts, E.NftRun{E.NftPendNext{}, env, 0n}) == E.NftRun{E.NftPendDone{E.NftChainReturn{}}, env, 0n} : E.NftRun}:
  match fuel:
    case 0n:
      {==}
    case 1n+q:
      {==}

def hk.run(hs: List<&2, C.NftHooked>, +opts: E.NftOptions, +env: X.NftEnv, h: {hk.all_empty(hs) == True{} : Bool}) -> {E.NftHookRun.go(hs, opts, E.NftOut{None{}, env, 0n}) == hk.out(hk.any_drop(hs), env) : E.NftOut}:
  match hs:
    case Nil{}:
      {==}
    case Con{x, t}:
      match x:
        case C.NftHooked{+tbl, rs, prio, pol}:
          match rs:
            case Con{r, rr}:
              Empty.absurd({E.NftHookRun.go(Con{C.NftHooked{tbl, Con{r, rr}, prio, pol}, t}, opts, E.NftOut{None{}, env, 0n}) == hk.out(hk.any_drop(Con{C.NftHooked{tbl, Con{r, rr}, prio, pol}, t}), env) : E.NftOut}, absurd.ft(h))
            case Nil{}:
              match pol:
                case V.NftPolicyAccept{}:
                  %Equal.sym(E.NftRun, E.NftRun.run(E.NftOptions.max_depth(opts), Nil{}, tbl, opts, E.NftRun{E.NftPendNext{}, env, 0n}), E.NftRun{E.NftPendDone{E.NftChainReturn{}}, env, 0n}, run_nil(E.NftOptions.max_depth(opts), tbl, opts, env)) : {E.NftHookRun.go(t, opts, E.NftHookRun.combine(E.NftBase.of_run(_, V.NftPolicyAccept{}), 0n)) == hk.out(hk.any_drop(t), env) : E.NftOut}
                  hk.run(t, opts, env, h)
                case V.NftPolicyDrop{}:
                  %Equal.sym(E.NftRun, E.NftRun.run(E.NftOptions.max_depth(opts), Nil{}, tbl, opts, E.NftRun{E.NftPendNext{}, env, 0n}), E.NftRun{E.NftPendDone{E.NftChainReturn{}}, env, 0n}, run_nil(E.NftOptions.max_depth(opts), tbl, opts, env)) : {E.NftHookRun.go(t, opts, E.NftHookRun.combine(E.NftBase.of_run(_, V.NftPolicyDrop{}), 0n)) == hk.out(True{}, env) : E.NftOut}
                  hk.absorb(t, opts, V.NftFinalDrop{}, env, 0n)

# insertion in priority order keeps "no rules" and "some policy drops"

def hk.ins_nil.pick(b: Bool, -x: C.NftHooked, +hd: C.NftHooked, -tl: List<&2, C.NftHooked>, -r: List<&2, C.NftHooked>, hx: {hk.empty(x) == True{} : Bool}, +h: {hk.all_empty(Con{hd, tl}) == True{} : Bool}, ih: {hk.all_empty(r) == True{} : Bool}) -> {hk.all_empty(C.NftHooked.ins.pick(b, x, hd, tl, r)) == True{} : Bool}:
  match b:
    case True{}:
      bool.and_intro(hk.empty(x), hk.all_empty(Con{hd, tl}), hx, h)
    case False{}:
      bool.and_intro(hk.empty(hd), hk.all_empty(r), bool.and_l(hk.empty(hd), hk.all_empty(tl), h), ih)

def hk.ins_nil(acc: List<&2, C.NftHooked>, +x: C.NftHooked, +hx: {hk.empty(x) == True{} : Bool}, h: {hk.all_empty(acc) == True{} : Bool}) -> {hk.all_empty(C.NftHooked.ins(acc, x)) == True{} : Bool}:
  match acc:
    case Nil{}:
      bool.and_intro(hk.empty(x), True{}, hx, {==})
    case Con{+hd, +tl}:
      +h = h
      hk.ins_nil.pick(F.NftPrio.lt(C.NftHooked.prio(x), C.NftHooked.prio(hd)), x, hd, tl, C.NftHooked.ins(tl, x), hx, h, hk.ins_nil(tl, x, hx, bool.and_r(hk.empty(hd), hk.all_empty(tl), h)))

def hk.ins_drop.pick(b: Bool, +x: C.NftHooked, +hd: C.NftHooked, +tl: List<&2, C.NftHooked>, +r: List<&2, C.NftHooked>, ih: {hk.any_drop(r) == Bool.or(hk.drops(x), hk.any_drop(tl)) : Bool}) -> {hk.any_drop(C.NftHooked.ins.pick(b, x, hd, tl, r)) == Bool.or(hk.drops(x), Bool.or(hk.drops(hd), hk.any_drop(tl))) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, hk.any_drop(r), Bool.or(hk.drops(x), hk.any_drop(tl)), ih) : {Bool.or(hk.drops(hd), _) == Bool.or(hk.drops(x), Bool.or(hk.drops(hd), hk.any_drop(tl))) : Bool}
      bool.or_swap(hk.drops(hd), hk.drops(x), hk.any_drop(tl))

def hk.ins_drop(acc: List<&2, C.NftHooked>, +x: C.NftHooked) -> {hk.any_drop(C.NftHooked.ins(acc, x)) == Bool.or(hk.drops(x), hk.any_drop(acc)) : Bool}:
  match acc:
    case Nil{}:
      {==}
    case Con{+hd, +tl}:
      hk.ins_drop.pick(F.NftPrio.lt(C.NftHooked.prio(x), C.NftHooked.prio(hd)), x, hd, tl, C.NftHooked.ins(tl, x), hk.ins_drop(tl, x))

# the collected base chains of a rule set without rules

def hk.offer_go_empty(at: Bool, +t: C.NftTable, +p: U32, +pol: V.NftPolicy, +acc: List<&2, C.NftHooked>, h: {hk.all_empty(acc) == True{} : Bool}) -> {hk.all_empty(C.NftChain.offer.go(at, t, Nil{}, p, pol, acc)) == True{} : Bool}:
  match at:
    case True{}:
      hk.ins_nil(acc, C.NftHooked{t, Nil{}, p, pol}, {==}, h)
    case False{}:
      h

def hk.offer_empty(-n: String, b: Maybe<&2, C.NftBaseSpec>, +t: C.NftTable, +hook: F.NftHook, +acc: List<&2, C.NftHooked>, h: {hk.all_empty(acc) == True{} : Bool}) -> {hk.all_empty(C.NftChain.offer(C.NftChain{n, b, Nil{}}, t, hook, acc)) == True{} : Bool}:
  match b:
    case None{}:
      h
    case Some{spec}:
      match spec:
        case C.NftBaseSpec{hh, p, pol}:
          hk.offer_go_empty(F.NftHook.is_eq(hh, hook), t, p, pol, acc, h)

def hk.chains_empty(cs: List<&2, C.NftChain>, +t: C.NftTable, +hook: F.NftHook, +acc: List<&2, C.NftHooked>, h: {hk.all_empty(acc) == True{} : Bool}) -> {hk.all_empty(C.NftChains.collect(C.NftChains.strip(cs), t, hook, acc)) == True{} : Bool}:
  match cs:
    case Nil{}:
      h
    case Con{c, rest}:
      match c:
        case C.NftChain{+n, +b, rs}:
          hk.chains_empty(rest, t, hook, C.NftChain.offer(C.NftChain{n, b, Nil{}}, t, hook, acc), hk.offer_empty(n, b, t, hook, acc, h))

def hk.toffer_empty(sees: Bool, +n: String, +f: F.NftFamily, +cs: List<&2, C.NftChain>, +ss: List<&2, S.NftNamedSet>, +hook: F.NftHook, +acc: List<&2, C.NftHooked>, h: {hk.all_empty(acc) == True{} : Bool}) -> {hk.all_empty(C.NftTable.offer(sees, C.NftTable{n, f, C.NftChains.strip(cs), ss}, hook, acc)) == True{} : Bool}:
  match sees:
    case True{}:
      hk.chains_empty(cs, C.NftTable{n, f, C.NftChains.strip(cs), ss}, hook, acc, h)
    case False{}:
      h

def hk.tables_empty(ts: List<&2, C.NftTable>, +proto: F.NftProto, +hook: F.NftHook, +acc: List<&2, C.NftHooked>, h: {hk.all_empty(acc) == True{} : Bool}) -> {hk.all_empty(C.NftTables.collect(C.NftTables.strip(ts), proto, hook, acc)) == True{} : Bool}:
  match ts:
    case Nil{}:
      h
    case Con{t, rest}:
      match t:
        case C.NftTable{+n, +f, +cs, +ss}:
          hk.tables_empty(rest, proto, hook, C.NftTable.offer(F.NftFamily.sees(f, proto), C.NftTable{n, f, C.NftChains.strip(cs), ss}, hook, acc), hk.toffer_empty(F.NftFamily.sees(f, proto), n, f, cs, ss, hook, acc, h))

def hk.offer_go_drop(at: Bool, +t: C.NftTable, +p: U32, +pol: V.NftPolicy, +acc: List<&2, C.NftHooked>) -> {hk.any_drop(C.NftChain.offer.go(at, t, Nil{}, p, pol, acc)) == Bool.or(Bool.and(at, Bool.not(V.NftPolicy.accepts(pol))), hk.any_drop(acc)) : Bool}:
  match at:
    case True{}:
      hk.ins_drop(acc, C.NftHooked{t, Nil{}, p, pol})
    case False{}:
      {==}

def hk.offer_drop(-n: String, b: Maybe<&2, C.NftBaseSpec>, -rs: List<&2, X.NftRule>, +t: C.NftTable, +hook: F.NftHook, +acc: List<&2, C.NftHooked>) -> {hk.any_drop(C.NftChain.offer(C.NftChain{n, b, Nil{}}, t, hook, acc)) == Bool.or(Laws.model.chain(C.NftChain{n, b, rs}, hook), hk.any_drop(acc)) : Bool}:
  match b:
    case None{}:
      {==}
    case Some{spec}:
      match spec:
        case C.NftBaseSpec{hh, p, pol}:
          hk.offer_go_drop(F.NftHook.is_eq(hh, hook), t, p, pol, acc)

def hk.chains_drop(cs: List<&2, C.NftChain>, +t: C.NftTable, +hook: F.NftHook, +acc: List<&2, C.NftHooked>) -> {hk.any_drop(C.NftChains.collect(C.NftChains.strip(cs), t, hook, acc)) == Bool.or(Laws.model.chains(cs, hook), hk.any_drop(acc)) : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{c, +rest}:
      match c:
        case C.NftChain{+n, +b, +rs}:
          +acc2 = C.NftChain.offer(C.NftChain{n, b, Nil{}}, t, hook, acc)
          +mc = Laws.model.chain(C.NftChain{n, b, rs}, hook)
          +mr = Laws.model.chains(rest, hook)
          +ih = hk.chains_drop(rest, t, hook, acc2)
          +step = Equal.cong(Bool, Bool, v => Bool.or(mr, v), hk.any_drop(acc2), Bool.or(mc, hk.any_drop(acc)), hk.offer_drop(n, b, rs, t, hook, acc))
          Equal.trans(Bool, hk.any_drop(C.NftChains.collect(C.NftChains.strip(rest), t, hook, acc2)), Bool.or(mr, Bool.or(mc, hk.any_drop(acc))), Bool.or(Bool.or(mc, mr), hk.any_drop(acc)), Equal.trans(Bool, hk.any_drop(C.NftChains.collect(C.NftChains.strip(rest), t, hook, acc2)), Bool.or(mr, hk.any_drop(acc2)), Bool.or(mr, Bool.or(mc, hk.any_drop(acc))), ih, step), bool.or_rot(mc, mr, hk.any_drop(acc)))

def hk.toffer_drop(sees: Bool, +n: String, +f: F.NftFamily, +cs: List<&2, C.NftChain>, +ss: List<&2, S.NftNamedSet>, +hook: F.NftHook, +acc: List<&2, C.NftHooked>) -> {hk.any_drop(C.NftTable.offer(sees, C.NftTable{n, f, C.NftChains.strip(cs), ss}, hook, acc)) == Bool.or(Bool.and(sees, Laws.model.chains(cs, hook)), hk.any_drop(acc)) : Bool}:
  match sees:
    case True{}:
      hk.chains_drop(cs, C.NftTable{n, f, C.NftChains.strip(cs), ss}, hook, acc)
    case False{}:
      {==}

def hk.tables_drop(ts: List<&2, C.NftTable>, +proto: F.NftProto, +hook: F.NftHook, +acc: List<&2, C.NftHooked>) -> {hk.any_drop(C.NftTables.collect(C.NftTables.strip(ts), proto, hook, acc)) == Bool.or(Laws.model.tables(ts, proto, hook), hk.any_drop(acc)) : Bool}:
  match ts:
    case Nil{}:
      {==}
    case Con{t, +rest}:
      match t:
        case C.NftTable{+n, +f, +cs, +ss}:
          +acc2 = C.NftTable.offer(F.NftFamily.sees(f, proto), C.NftTable{n, f, C.NftChains.strip(cs), ss}, hook, acc)
          +mt = Bool.and(F.NftFamily.sees(f, proto), Laws.model.chains(cs, hook))
          +mr = Laws.model.tables(rest, proto, hook)
          +ih = hk.tables_drop(rest, proto, hook, acc2)
          +step = Equal.cong(Bool, Bool, v => Bool.or(mr, v), hk.any_drop(acc2), Bool.or(mt, hk.any_drop(acc)), hk.toffer_drop(F.NftFamily.sees(f, proto), n, f, cs, ss, hook, acc))
          Equal.trans(Bool, hk.any_drop(C.NftTables.collect(C.NftTables.strip(rest), proto, hook, acc2)), Bool.or(mr, Bool.or(mt, hk.any_drop(acc))), Bool.or(Bool.or(mt, mr), hk.any_drop(acc)), Equal.trans(Bool, hk.any_drop(C.NftTables.collect(C.NftTables.strip(rest), proto, hook, acc2)), Bool.or(mr, hk.any_drop(acc2)), Bool.or(mr, Bool.or(mt, hk.any_drop(acc))), ih, step), bool.or_rot(mt, mr, hk.any_drop(acc)))

def hk.final(b: Bool, -pkt: X.NftPacket, -st: X.NftState, -now: W.W64) -> {N.NftResult.of(hk.out(b, X.NftEnv{pkt, st, now})) == N.NftResult{Laws.model.final(b), pkt, st, 0n} : N.NftResult}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.no_rules_policy(opts, rs, proto, hook, now, pkt, st):
  match rs:
    case C.NftRuleset{+ts}:
      +env = {X.NftEnv{pkt, st, now} : X.NftEnv}
      +hs = C.NftTables.collect(C.NftTables.strip(ts), proto, hook, Nil{})
      +mt = Laws.model.tables(ts, proto, hook)
      +run = hk.run(hs, opts, env, hk.tables_empty(ts, proto, hook, Nil{}, {==}))
      +drop = Equal.trans(Bool, hk.any_drop(hs), Bool.or(mt, False{}), mt, hk.tables_drop(ts, proto, hook, Nil{}), bool.or_false(mt))
      %Equal.sym(E.NftOut, E.NftHookRun.go(hs, opts, E.NftOut{None{}, env, 0n}), hk.out(hk.any_drop(hs), env), run) : {N.NftResult.of(_) == N.NftResult{Laws.model.final(mt), pkt, st, 0n} : N.NftResult}
      %Equal.sym(Bool, hk.any_drop(hs), mt, drop) : {N.NftResult.of(hk.out(_, env)) == N.NftResult{Laws.model.final(mt), pkt, st, 0n} : N.NftResult}
      hk.final(mt, pkt, st, now)


# Jump: the result and packet of an evaluation do not depend on the depth
# it starts from

def pend_of(a: E.NftRun) -> E.NftPend:
  match a:
    case E.NftRun{p, e, d}:
      p

def jpend(x: E.NftChainRes) -> E.NftPend:
  match x:
    case E.NftChainReturn{}:
      E.NftPendNext{}
    case E.NftChainStop{f}:
      E.NftPendDone{E.NftChainStop{f}}

def form.join_go(x: E.NftChainRes, +en: X.NftEnv, +dd: Nat) -> {E.NftRun.join.go(x, en, dd) == E.NftRun{jpend(x), en, dd} : E.NftRun}:
  match x:
    case E.NftChainReturn{}:
      {==}
    case E.NftChainStop{f}:
      {==}

def jp(b: Bool, +cl: E.NftRun, +opts: E.NftOptions) -> E.NftPend:
  match b:
    case False{}:
      E.NftPendDone{E.NftChainStop{E.NftOptions.missing_final(opts)}}
    case True{}:
      jpend(E.NftRun.result(cl))

def je(b: Bool, +cl: E.NftRun, e: X.NftEnv) -> X.NftEnv:
  match b:
    case False{}:
      e
    case True{}:
      E.NftRun.env(cl)

def jdep(b: Bool, +cl: E.NftRun, +d: Nat) -> Nat:
  match b:
    case False{}:
      d
    case True{}:
      Nat.max(d, 1n+E.NftRun.depth(cl))

def form.join(b: Bool, +cl: E.NftRun, +d: Nat, +opts: E.NftOptions, +e: X.NftEnv) -> {E.NftRun.join(b, cl, d, opts, e) == E.NftRun{jp(b, cl, opts), je(b, cl, e), jdep(b, cl, d)} : E.NftRun}:
  match b:
    case False{}:
      {==}
    case True{}:
      form.join_go(E.NftRun.result(cl), E.NftRun.env(cl), Nat.max(d, 1n+E.NftRun.depth(cl)))

def spend(r: X.NftRule, +sets: List<&2, S.NftNamedSet>, p: E.NftPend, +e: X.NftEnv) -> E.NftPend:
  match p:
    case E.NftPendNext{}:
      pend_of(E.NftRun.of_rule(X.NftRule.eval(r, sets, e), 0n))
    case E.NftPendJump{c}:
      E.NftPendJump{c}
    case E.NftPendGoto{c}:
      E.NftPendGoto{c}
    case E.NftPendDone{x}:
      E.NftPendDone{x}

def senv(r: X.NftRule, +sets: List<&2, S.NftNamedSet>, p: E.NftPend, +e: X.NftEnv) -> X.NftEnv:
  match p:
    case E.NftPendNext{}:
      E.NftRun.env(E.NftRun.of_rule(X.NftRule.eval(r, sets, e), 0n))
    case E.NftPendJump{c}:
      e
    case E.NftPendGoto{c}:
      e
    case E.NftPendDone{x}:
      e

def form.of_rule(o: X.NftRuleOut, +d: Nat) -> {E.NftRun.of_rule(o, d) == E.NftRun{pend_of(E.NftRun.of_rule(o, 0n)), E.NftRun.env(E.NftRun.of_rule(o, 0n)), d} : E.NftRun}:
  match o:
    case X.NftRuleNext{env}:
      {==}
    case X.NftRuleVerdict{v, env}:
      {==}

def form.step(r: X.NftRule, +sets: List<&2, S.NftNamedSet>, p: E.NftPend, +e: X.NftEnv, +d: Nat) -> {E.NftRun.step(r, sets, E.NftRun{p, e, d}) == E.NftRun{spend(r, sets, p, e), senv(r, sets, p, e), d} : E.NftRun}:
  match p:
    case E.NftPendNext{}:
      form.of_rule(X.NftRule.eval(r, sets, e), d)
    case E.NftPendJump{c}:
      {==}
    case E.NftPendGoto{c}:
      {==}
    case E.NftPendDone{x}:
      {==}

def vfin.go(x: E.NftChainRes, -en: X.NftEnv, -dd1: Nat, -dd2: Nat) -> {Laws.view(E.NftRun.fin(E.NftRun.join.go(x, en, dd1))) == Laws.view(E.NftRun.fin(E.NftRun.join.go(x, en, dd2))) : E.NftChainRes & X.NftEnv}:
  match x:
    case E.NftChainReturn{}:
      {==}
    case E.NftChainStop{f}:
      {==}

def vfin(b: Bool, +cl: E.NftRun, +d1: Nat, +d2: Nat, -opts: E.NftOptions, -e: X.NftEnv) -> {Laws.view(E.NftRun.fin(E.NftRun.join(b, cl, d1, opts, e))) == Laws.view(E.NftRun.fin(E.NftRun.join(b, cl, d2, opts, e))) : E.NftChainRes & X.NftEnv}:
  match b:
    case False{}:
      {==}
    case True{}:
      vfin.go(E.NftRun.result(cl), E.NftRun.env(cl), Nat.max(d1, 1n+E.NftRun.depth(cl)), Nat.max(d2, 1n+E.NftRun.depth(cl)))

def vgoto(b: Bool, -cl: E.NftRun, -d1: Nat, -d2: Nat, -opts: E.NftOptions, -e: X.NftEnv) -> {Laws.view(E.NftRun.goto(b, cl, d1, opts, e)) == Laws.view(E.NftRun.goto(b, cl, d2, opts, e)) : E.NftChainRes & X.NftEnv}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def vrun.cong(+fuel: Nat, +rules: List<&2, X.NftRule>, +tbl: C.NftTable, +opts: E.NftOptions, -a: E.NftRun, -b: E.NftRun, e: {a == b : E.NftRun}) -> {Laws.view(E.NftRun.run(fuel, rules, tbl, opts, a)) == Laws.view(E.NftRun.run(fuel, rules, tbl, opts, b)) : E.NftChainRes & X.NftEnv}:
  %e : {Laws.view(E.NftRun.run(fuel, rules, tbl, opts, a)) == Laws.view(E.NftRun.run(fuel, rules, tbl, opts, _)) : E.NftChainRes & X.NftEnv}
  {==}

def id.lift(+fuel: Nat, +rules: List<&2, X.NftRule>, +tbl: C.NftTable, +opts: E.NftOptions, +a1: E.NftRun, +b1: E.NftRun, +a2: E.NftRun, +b2: E.NftRun, e1: {a1 == b1 : E.NftRun}, e2: {a2 == b2 : E.NftRun}, ih: {Laws.view(E.NftRun.run(fuel, rules, tbl, opts, b1)) == Laws.view(E.NftRun.run(fuel, rules, tbl, opts, b2)) : E.NftChainRes & X.NftEnv}) -> {Laws.view(E.NftRun.run(fuel, rules, tbl, opts, a1)) == Laws.view(E.NftRun.run(fuel, rules, tbl, opts, a2)) : E.NftChainRes & X.NftEnv}:
  Equal.trans(E.NftChainRes & X.NftEnv, Laws.view(E.NftRun.run(fuel, rules, tbl, opts, a1)), Laws.view(E.NftRun.run(fuel, rules, tbl, opts, b1)), Laws.view(E.NftRun.run(fuel, rules, tbl, opts, a2)), vrun.cong(fuel, rules, tbl, opts, a1, b1, e1), Equal.trans(E.NftChainRes & X.NftEnv, Laws.view(E.NftRun.run(fuel, rules, tbl, opts, b1)), Laws.view(E.NftRun.run(fuel, rules, tbl, opts, b2)), Laws.view(E.NftRun.run(fuel, rules, tbl, opts, a2)), ih, Equal.sym(E.NftChainRes & X.NftEnv, Laws.view(E.NftRun.run(fuel, rules, tbl, opts, a2)), Laws.view(E.NftRun.run(fuel, rules, tbl, opts, b2)), vrun.cong(fuel, rules, tbl, opts, a2, b2, e2))))

# step after join, as one record
def form.step_join(r: X.NftRule, +sets: List<&2, S.NftNamedSet>, +b: Bool, +cl: E.NftRun, +d: Nat, +opts: E.NftOptions, +e: X.NftEnv) -> {E.NftRun.step(r, sets, E.NftRun.join(b, cl, d, opts, e)) == E.NftRun{spend(r, sets, jp(b, cl, opts), je(b, cl, e)), senv(r, sets, jp(b, cl, opts), je(b, cl, e)), jdep(b, cl, d)} : E.NftRun}:
  Equal.trans(E.NftRun, E.NftRun.step(r, sets, E.NftRun.join(b, cl, d, opts, e)), E.NftRun.step(r, sets, E.NftRun{jp(b, cl, opts), je(b, cl, e), jdep(b, cl, d)}), E.NftRun{spend(r, sets, jp(b, cl, opts), je(b, cl, e)), senv(r, sets, jp(b, cl, opts), je(b, cl, e)), jdep(b, cl, d)}, Equal.cong(E.NftRun, E.NftRun, v => E.NftRun.step(r, sets, v), E.NftRun.join(b, cl, d, opts, e), E.NftRun{jp(b, cl, opts), je(b, cl, e), jdep(b, cl, d)}, form.join(b, cl, d, opts, e)), form.step(r, sets, jp(b, cl, opts), je(b, cl, e), jdep(b, cl, d)))

def id.run(+fuel: Nat, +rules: List<&2, X.NftRule>, +tbl: C.NftTable, +opts: E.NftOptions, p: E.NftPend, +e: X.NftEnv, +d1: Nat, +d2: Nat) -> {Laws.view(E.NftRun.run(fuel, rules, tbl, opts, E.NftRun{p, e, d1})) == Laws.view(E.NftRun.run(fuel, rules, tbl, opts, E.NftRun{p, e, d2})) : E.NftChainRes & X.NftEnv}:
  match fuel:
    case 0n:
      match rules:
        case Nil{}:
          match p:
            case E.NftPendNext{}:
              {==}
            case E.NftPendJump{c}:
              {==}
            case E.NftPendGoto{c}:
              {==}
            case E.NftPendDone{x}:
              {==}
        case Con{+r, +rest}:
          match p:
            case E.NftPendNext{}:
              +sets = C.NftTable.sets(tbl)
              id.lift(fuel, rest, tbl, opts, E.NftRun.step(r, sets, E.NftRun{E.NftPendNext{}, e, d1}), E.NftRun{spend(r, sets, E.NftPendNext{}, e), senv(r, sets, E.NftPendNext{}, e), d1}, E.NftRun.step(r, sets, E.NftRun{E.NftPendNext{}, e, d2}), E.NftRun{spend(r, sets, E.NftPendNext{}, e), senv(r, sets, E.NftPendNext{}, e), d2}, form.step(r, sets, E.NftPendNext{}, e, d1), form.step(r, sets, E.NftPendNext{}, e, d2), id.run(fuel, rest, tbl, opts, spend(r, sets, E.NftPendNext{}, e), senv(r, sets, E.NftPendNext{}, e), d1, d2))
            case E.NftPendJump{c}:
              id.run(fuel, rest, tbl, opts, E.NftPendDone{E.NftChainStop{E.NftOptions.depth_final(opts)}}, e, d1, d2)
            case E.NftPendGoto{c}:
              id.run(fuel, rest, tbl, opts, E.NftPendDone{E.NftChainStop{E.NftOptions.depth_final(opts)}}, e, d1, d2)
            case E.NftPendDone{+x}:
              id.run(fuel, rest, tbl, opts, E.NftPendDone{x}, e, d1, d2)
    case 1n+q:
      match rules:
        case Nil{}:
          match p:
            case E.NftPendNext{}:
              {==}
            case E.NftPendDone{x}:
              {==}
            case E.NftPendJump{+c}:
              vfin(C.NftTable.has_chain(tbl, c), E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, e, 0n}), d1, d2, opts, e)
            case E.NftPendGoto{+c}:
              vgoto(C.NftTable.has_chain(tbl, c), E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, e, 0n}), d1, d2, opts, e)
        case Con{+r, +rest}:
          match p:
            case E.NftPendNext{}:
              +o = X.NftRule.eval(r, C.NftTable.sets(tbl), e)
              id.lift(fuel, rest, tbl, opts, E.NftRun.of_rule(o, d1), E.NftRun{pend_of(E.NftRun.of_rule(o, 0n)), E.NftRun.env(E.NftRun.of_rule(o, 0n)), d1}, E.NftRun.of_rule(o, d2), E.NftRun{pend_of(E.NftRun.of_rule(o, 0n)), E.NftRun.env(E.NftRun.of_rule(o, 0n)), d2}, form.of_rule(o, d1), form.of_rule(o, d2), id.run(fuel, rest, tbl, opts, pend_of(E.NftRun.of_rule(o, 0n)), E.NftRun.env(E.NftRun.of_rule(o, 0n)), d1, d2))
            case E.NftPendDone{x}:
              {==}
            case E.NftPendJump{+c}:
              +sets = C.NftTable.sets(tbl)
              +b = C.NftTable.has_chain(tbl, c)
              +cl = E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, e, 0n})
              id.lift(fuel, rest, tbl, opts, E.NftRun.step(r, sets, E.NftRun.join(b, cl, d1, opts, e)), E.NftRun{spend(r, sets, jp(b, cl, opts), je(b, cl, e)), senv(r, sets, jp(b, cl, opts), je(b, cl, e)), jdep(b, cl, d1)}, E.NftRun.step(r, sets, E.NftRun.join(b, cl, d2, opts, e)), E.NftRun{spend(r, sets, jp(b, cl, opts), je(b, cl, e)), senv(r, sets, jp(b, cl, opts), je(b, cl, e)), jdep(b, cl, d2)}, form.step_join(r, sets, b, cl, d1, opts, e), form.step_join(r, sets, b, cl, d2, opts, e), id.run(fuel, rest, tbl, opts, spend(r, sets, jp(b, cl, opts), je(b, cl, e)), senv(r, sets, jp(b, cl, opts), je(b, cl, e)), jdep(b, cl, d1), jdep(b, cl, d2)))
            case E.NftPendGoto{+c}:
              vgoto(C.NftTable.has_chain(tbl, c), E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, e, 0n}), d1, d2, opts, e)

# after a jump to chain c, which exists and returns
def jr.join(+tbl: C.NftTable, +c: String, +callee: E.NftRun, +d: Nat, +opts: E.NftOptions, env: X.NftEnv, found: {C.NftTable.has_chain(tbl, c) == True{} : Bool}, hr: {E.NftRun.result(callee) == E.NftChainReturn{} : E.NftChainRes}) -> {E.NftRun.join(C.NftTable.has_chain(tbl, c), callee, d, opts, env) == E.NftRun{E.NftPendNext{}, E.NftRun.env(callee), Nat.max(d, 1n+E.NftRun.depth(callee))} : E.NftRun}:
  %Equal.sym(Bool, C.NftTable.has_chain(tbl, c), True{}, found) : {E.NftRun.join(_, callee, d, opts, env) == E.NftRun{E.NftPendNext{}, E.NftRun.env(callee), Nat.max(d, 1n+E.NftRun.depth(callee))} : E.NftRun}
  %Equal.sym(E.NftChainRes, E.NftRun.result(callee), E.NftChainReturn{}, hr) : {E.NftRun.join.go(_, E.NftRun.env(callee), Nat.max(d, 1n+E.NftRun.depth(callee))) == E.NftRun{E.NftPendNext{}, E.NftRun.env(callee), Nat.max(d, 1n+E.NftRun.depth(callee))} : E.NftRun}
  {==}

def jr.after(+q: Nat, rest: List<&2, X.NftRule>, +tbl: C.NftTable, +opts: E.NftOptions, +c: String, +env2: X.NftEnv, +found: {C.NftTable.has_chain(tbl, c) == True{} : Bool}, +ret: {E.NftRun.result(E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env2, 0n})) == E.NftChainReturn{} : E.NftChainRes}) -> {Laws.view(E.NftRun.run(1n+q, rest, tbl, opts, E.NftRun{E.NftPendJump{c}, env2, 0n})) == Laws.view(E.Nft.run_chain(opts, 1n+q, tbl, rest, E.NftRun.env(E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env2, 0n})))) : E.NftChainRes & X.NftEnv}:
  match rest:
    case Nil{}:
      +callee = E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env2, 0n})
      %Equal.sym(E.NftRun, E.NftRun.join(C.NftTable.has_chain(tbl, c), callee, 0n, opts, env2), E.NftRun{E.NftPendNext{}, E.NftRun.env(callee), Nat.max(0n, 1n+E.NftRun.depth(callee))}, jr.join(tbl, c, callee, 0n, opts, env2, found, ret)) : {Laws.view(E.NftRun.fin(_)) == Laws.view(E.Nft.run_chain(opts, 1n+q, tbl, Nil{}, E.NftRun.env(callee))) : E.NftChainRes & X.NftEnv}
      {==}
    case Con{+r2, +rest2}:
      +callee = E.NftRun.run(q, C.NftTable.rules(tbl, c), tbl, opts, E.NftRun{E.NftPendNext{}, env2, 0n})
      +sets = C.NftTable.sets(tbl)
      +dd = Nat.max(0n, 1n+E.NftRun.depth(callee))
      +o = X.NftRule.eval(r2, sets, E.NftRun.env(callee))
      %Equal.sym(E.NftRun, E.NftRun.join(C.NftTable.has_chain(tbl, c), callee, 0n, opts, env2), E.NftRun{E.NftPendNext{}, E.NftRun.env(callee), dd}, jr.join(tbl, c, callee, 0n, opts, env2, found, ret)) : {Laws.view(E.NftRun.run(1n+q, rest2, tbl, opts, E.NftRun.step(r2, sets, _))) == Laws.view(E.Nft.run_chain(opts, 1n+q, tbl, Con{r2, rest2}, E.NftRun.env(callee))) : E.NftChainRes & X.NftEnv}
      id.lift(1n+q, rest2, tbl, opts, E.NftRun.of_rule(o, dd), E.NftRun{pend_of(E.NftRun.of_rule(o, 0n)), E.NftRun.env(E.NftRun.of_rule(o, 0n)), dd}, E.NftRun.of_rule(o, 0n), E.NftRun{pend_of(E.NftRun.of_rule(o, 0n)), E.NftRun.env(E.NftRun.of_rule(o, 0n)), 0n}, form.of_rule(o, dd), form.of_rule(o, 0n), id.run(1n+q, rest2, tbl, opts, pend_of(E.NftRun.of_rule(o, 0n)), E.NftRun.env(E.NftRun.of_rule(o, 0n)), dd, 0n))

def Laws.jump_returns(opts, q, tbl, r, rest, env, c, env2, jumps, found, returns):
  %Equal.sym(X.NftRuleOut, X.NftRule.eval(r, C.NftTable.sets(tbl), env), X.NftRuleVerdict{V.NftJump{c}, env2}, jumps) : {Laws.view(E.NftRun.run(1n+q, rest, tbl, opts, E.NftRun.of_rule(_, 0n))) == Laws.view(E.Nft.run_chain(opts, 1n+q, tbl, rest, E.NftRun.env(E.Nft.run_chain(opts, q, tbl, C.NftTable.rules(tbl, c), env2)))) : E.NftChainRes & X.NftEnv}
  jr.after(q, rest, tbl, opts, c, env2, found, returns)

# Vectors and witnesses: by computation

def Laws.set_empty_wf():
  {==}

def Laws.vec_depth_limit():
  {==}

def Laws.vec_jump_return():
  {==}

def Laws.vec_goto_return():
  {==}

def Laws.vec_accept_passes_on():
  {==}

def Laws.vec_queue():
  {==}

def Laws.vec_overlap():
  {==}

def Laws.vec_bad_interval():
  {==}

def Laws.witness_drops():
  {==}

def Laws.witness_jumps():
  {==}

def Laws.witness_found():
  {==}

def Laws.witness_callee_drops():
  {==}

def Laws.witness_goes():
  {==}

def Laws.witness_base_drops():
  {==}

def Laws.witness_of_list():
  {==}

def Laws.witness_wf():
  {==}

def Laws.witness_insert():
  {==}

def Laws.witness_callee_returns():
  {==}

def Laws.witness_jumps_r():
  {==}

def Laws.witness_found_r():
  {==}
