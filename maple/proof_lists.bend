# Proof helpers for bend-osdev-maple: the list model (model.bend), for U32
# indices. Lists of entries: appends, the order invariant (wf), and how each
# scan of the model behaves on an append, on a list below or above an
# index, and on the parts set_range and clear_range build.
import Base
import ./model.bend as M
import ./proof_order.bend as O

# Shorthands for the U32 instance (they unfold to the package's defs)

def Ent(-V: Data) -> Data:
  M.MapleEntry<U32, V>

def Es(-V: Data) -> Data:
  List<&2, M.MapleEntry<U32, V>>

def fst(-V: Data, e: Ent(V)) -> U32:
  M.MapleEntry.first(U32, V, e)

def lst(-V: Data, e: Ent(V)) -> U32:
  M.MapleEntry.last(U32, V, e)

def val(-V: Data, e: Ent(V)) -> V:
  M.MapleEntry.value(U32, V, e)

def app(-V: Data, xs: Es(V), ys: Es(V)) -> Es(V):
  M.MapleModel.append(U32, V, xs, ys)

def wf(-V: Data, xs: Es(V)) -> Bool:
  M.MapleModel.wf(~U32, ~U32.cmp, V, xs)

def aft(-V: Data, +k: U32, xs: Es(V)) -> Bool:
  M.MapleModel.after(~U32, ~U32.cmp, V, k, xs)

def holds(-V: Data, +e: Ent(V), +i: U32) -> Bool:
  M.MapleEntry.holds(~U32, ~U32.cmp, V, e, i)

def lkey(-V: Data, xs: Es(V)) -> Maybe<&2, U32>:
  M.MapleModel.last_key(U32, V, xs)

def mload(-V: Data, xs: Es(V), +i: U32) -> Maybe<&2, V>:
  M.MapleModel.load(~U32, ~U32.cmp, V, xs, i)

def mlookup(-V: Data, xs: Es(V), +i: U32) -> Maybe<&2, Ent(V)>:
  M.MapleModel.lookup(~U32, ~U32.cmp, V, xs, i)

def mfind(-V: Data, xs: Es(V), +i: U32) -> Maybe<&2, Ent(V)>:
  M.MapleModel.find(~U32, ~U32.cmp, V, xs, i)

def mnext(-V: Data, xs: Es(V), +i: U32) -> Maybe<&2, Ent(V)>:
  M.MapleModel.next(~U32, ~U32.cmp, V, xs, i)

def mprev(-V: Data, xs: Es(V), +i: U32) -> Maybe<&2, Ent(V)>:
  M.MapleModel.prev(~U32, ~U32.cmp, V, xs, i)

def below(-V: Data, xs: Es(V), +a: U32) -> Es(V):
  M.MapleModel.below(~U32, ~U32.cmp, ~M.MapleKey32.dec, V, xs, a)

def above(-V: Data, xs: Es(V), +b: U32) -> Es(V):
  M.MapleModel.above(~U32, ~U32.cmp, ~M.MapleKey32.inc, V, xs, b)

def later(-V: Data, m: Maybe<&2, Ent(V)>, n: Maybe<&2, Ent(V)>) -> Maybe<&2, Ent(V)>:
  M.MapleModel.later(U32, V, m, n)

def orv(-V: Data, m: Maybe<&2, V>, n: Maybe<&2, V>) -> Maybe<&2, V>:
  Maybe.or(&2, V, m, n)

# every entry of xs ends at or before p
def lasts_le(-V: Data, xs: Es(V), +p: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, r}:
      Bool.and(O.ule(lst(V, x), p), lasts_le(V, r, p))

# every entry of xs ends before a
def lasts_lt(-V: Data, xs: Es(V), +a: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, r}:
      Bool.and(O.ult(lst(V, x), a), lasts_lt(V, r, a))

# every entry of xs starts at or after a
def firsts_ge(-V: Data, xs: Es(V), +a: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, r}:
      Bool.and(O.ule(a, fst(V, x)), firsts_ge(V, r, a))

# the last entry
def elast(-V: Data, xs: Es(V)) -> Maybe<&2, Ent(V)>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, r}:
      later(V, elast(V, r), Some{x})

# Appends

def app.assoc(-V: Data, xs: Es(V), +ys: Es(V), +zs: Es(V)) -> {app(V, app(V, xs, ys), zs) == app(V, xs, app(V, ys, zs)) : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %app.assoc(V, r, ys, zs) : {Con{x, app(V, app(V, r, ys), zs)} == Con{x, _} : Es(V)}
      {==}

def app.nil(-V: Data, xs: Es(V)) -> {app(V, xs, Nil{}) == xs : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %app.nil(V, r) : {Con{x, app(V, r, Nil{})} == Con{x, _} : Es(V)}
      {==}

# Small Bool facts about entries

# the parts of the hypotheses wf gives for a list headed by x
def wf.le(-V: Data, +x: Ent(V), +r: Es(V), +h: {wf(V, Con{x, r}) == True{} : Bool}) -> {O.ule(fst(V, x), lst(V, x)) == True{} : Bool}:
  O.bo.and_l(O.ule(fst(V, x), lst(V, x)), Bool.and(aft(V, lst(V, x), r), wf(V, r)), h)

def wf.aft(-V: Data, +x: Ent(V), +r: Es(V), +h: {wf(V, Con{x, r}) == True{} : Bool}) -> {aft(V, lst(V, x), r) == True{} : Bool}:
  O.bo.and_l(aft(V, lst(V, x), r), wf(V, r), O.bo.and_r(O.ule(fst(V, x), lst(V, x)), Bool.and(aft(V, lst(V, x), r), wf(V, r)), h))

def wf.tail(-V: Data, +x: Ent(V), +r: Es(V), +h: {wf(V, Con{x, r}) == True{} : Bool}) -> {wf(V, r) == True{} : Bool}:
  O.bo.and_r(aft(V, lst(V, x), r), wf(V, r), O.bo.and_r(O.ule(fst(V, x), lst(V, x)), Bool.and(aft(V, lst(V, x), r), wf(V, r)), h))

def wf.intro(-V: Data, +x: Ent(V), +r: Es(V), +a: {O.ule(fst(V, x), lst(V, x)) == True{} : Bool}, +b: {aft(V, lst(V, x), r) == True{} : Bool}, +c: {wf(V, r) == True{} : Bool}) -> {wf(V, Con{x, r}) == True{} : Bool}:
  O.bo.and_intro(O.ule(fst(V, x), lst(V, x)), Bool.and(aft(V, lst(V, x), r), wf(V, r)), a, O.bo.and_intro(aft(V, lst(V, x), r), wf(V, r), b, c))

def aft.head(-V: Data, +k: U32, +x: Ent(V), +r: Es(V), +h: {aft(V, k, Con{x, r}) == True{} : Bool}) -> {O.ult(k, fst(V, x)) == True{} : Bool}:
  O.bo.and_l(O.ult(k, fst(V, x)), aft(V, k, r), h)

def aft.tail(-V: Data, +k: U32, +x: Ent(V), +r: Es(V), +h: {aft(V, k, Con{x, r}) == True{} : Bool}) -> {aft(V, k, r) == True{} : Bool}:
  O.bo.and_r(O.ult(k, fst(V, x)), aft(V, k, r), h)

def aft.app_l(-V: Data, +k: U32, xs: Es(V), +ys: Es(V), +h: {aft(V, k, app(V, xs, ys)) == True{} : Bool}) -> {aft(V, k, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      O.bo.and_intro(O.ult(k, fst(V, x)), aft(V, k, r), aft.head(V, k, x, app(V, r, ys), h), aft.app_l(V, k, r, ys, aft.tail(V, k, x, app(V, r, ys), h)))

def aft.app_r(-V: Data, +k: U32, xs: Es(V), +ys: Es(V), +h: {aft(V, k, app(V, xs, ys)) == True{} : Bool}) -> {aft(V, k, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+x, +r}:
      aft.app_r(V, k, r, ys, aft.tail(V, k, x, app(V, r, ys), h))

def aft.app_intro(-V: Data, +k: U32, xs: Es(V), +ys: Es(V), +hx: {aft(V, k, xs) == True{} : Bool}, +hy: {aft(V, k, ys) == True{} : Bool}) -> {aft(V, k, app(V, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+x, +r}:
      O.bo.and_intro(O.ult(k, fst(V, x)), aft(V, k, app(V, r, ys)), aft.head(V, k, x, r, hx), aft.app_intro(V, k, r, ys, aft.tail(V, k, x, r, hx), hy))

# all after k2 and k <= k2: all after k
def aft.weaken(-V: Data, +k: U32, +k2: U32, xs: Es(V), +g: {O.ule(k, k2) == True{} : Bool}, +h: {aft(V, k2, xs) == True{} : Bool}) -> {aft(V, k, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      O.bo.and_intro(O.ult(k, fst(V, x)), aft(V, k, r), O.u.le_lt(k, k2, fst(V, x), g, aft.head(V, k2, x, r, h)), aft.weaken(V, k, k2, r, g, aft.tail(V, k2, x, r, h)))

# all starting at or after a, and k < a: all after k
def aft.of_ge(-V: Data, +k: U32, +a: U32, xs: Es(V), +g: {O.ult(k, a) == True{} : Bool}, +h: {firsts_ge(V, xs, a) == True{} : Bool}) -> {aft(V, k, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      O.bo.and_intro(O.ult(k, fst(V, x)), aft(V, k, r), O.u.lt_le(k, a, fst(V, x), g, O.bo.and_l(O.ule(a, fst(V, x)), firsts_ge(V, r, a), h)), aft.of_ge(V, k, a, r, g, O.bo.and_r(O.ule(a, fst(V, x)), firsts_ge(V, r, a), h)))

# all after k, and a <= k: all start at or after a
def ge.of_aft(-V: Data, +a: U32, +k: U32, xs: Es(V), +g: {O.ule(a, k) == True{} : Bool}, +h: {aft(V, k, xs) == True{} : Bool}) -> {firsts_ge(V, xs, a) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      O.bo.and_intro(O.ule(a, fst(V, x)), firsts_ge(V, r, a), O.u.le_of_lt(a, fst(V, x), O.u.le_lt(a, k, fst(V, x), g, aft.head(V, k, x, r, h))), ge.of_aft(V, a, k, r, g, aft.tail(V, k, x, r, h)))

def wf.app_l(-V: Data, xs: Es(V), +ys: Es(V), +h: {wf(V, app(V, xs, ys)) == True{} : Bool}) -> {wf(V, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      wf.intro(V, x, r, wf.le(V, x, app(V, r, ys), h), aft.app_l(V, lst(V, x), r, ys, wf.aft(V, x, app(V, r, ys), h)), wf.app_l(V, r, ys, wf.tail(V, x, app(V, r, ys), h)))

def wf.app_r(-V: Data, xs: Es(V), +ys: Es(V), +h: {wf(V, app(V, xs, ys)) == True{} : Bool}) -> {wf(V, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case Con{+x, +r}:
      wf.app_r(V, r, ys, wf.tail(V, x, app(V, r, ys), h))

# xs before a, ys from a on, each in order: xs ++ ys in order
def wf.app_intro(-V: Data, xs: Es(V), +ys: Es(V), +a: U32, +hx: {wf(V, xs) == True{} : Bool}, +hy: {wf(V, ys) == True{} : Bool}, +lx: {lasts_lt(V, xs, a) == True{} : Bool}, +gy: {firsts_ge(V, ys, a) == True{} : Bool}) -> {wf(V, app(V, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+x, +r}:
      +lx = lx
      wf.intro(V, x, app(V, r, ys), wf.le(V, x, r, hx), aft.app_intro(V, lst(V, x), r, ys, wf.aft(V, x, r, hx), aft.of_ge(V, lst(V, x), a, ys, O.bo.and_l(O.ult(lst(V, x), a), lasts_lt(V, r, a), lx), gy)), wf.app_intro(V, r, ys, a, wf.tail(V, x, r, hx), hy, O.bo.and_r(O.ult(lst(V, x), a), lasts_lt(V, r, a), lx), gy))

# Picking: pick_value (for values) and pick (for entries)

def pv(-V: Data, b: Bool, x: V, rest: Maybe<&2, V>) -> Maybe<&2, V>:
  M.MapleModel.pick_value(V, b, x, rest)

def pk(-V: Data, b: Bool, x: Ent(V), rest: Maybe<&2, Ent(V)>) -> Maybe<&2, Ent(V)>:
  M.MapleModel.pick(U32, V, b, x, rest)

def bo.and_true_r(x: Bool, -y: Bool, +ey: {y == True{} : Bool}) -> {Bool.and(x, y) == x : Bool}:
  match x:
    case True{}:
      ey
    case False{}:
      {==}

def bo.and_true_l(x: Bool, -y: Bool, +ex: {x == True{} : Bool}) -> {Bool.and(x, y) == y : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == y : Bool}, O.ab.ft(ex))

def pv.false(-V: Data, b: Bool, -x: V, -m: Maybe<&2, V>, +e: {b == False{} : Bool}) -> {pv(V, b, x, m) == m : Maybe<&2, V>}:
  match b:
    case True{}:
      Empty.absurd({Some{x} == m : Maybe<&2, V>}, O.ab.tf(e))
    case False{}:
      {==}

def pv.true(-V: Data, b: Bool, -x: V, -m: Maybe<&2, V>, +e: {b == True{} : Bool}) -> {pv(V, b, x, m) == Some{x} : Maybe<&2, V>}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({m == Some{x} : Maybe<&2, V>}, O.ab.ft(e))

def pv.cong(-V: Data, -b1: Bool, -b2: Bool, -x: V, -m1: Maybe<&2, V>, -m2: Maybe<&2, V>, +eb: {b1 == b2 : Bool}, +em: {m1 == m2 : Maybe<&2, V>}) -> {pv(V, b1, x, m1) == pv(V, b2, x, m2) : Maybe<&2, V>}:
  %eb : {pv(V, b1, x, m1) == pv(V, _, x, m2) : Maybe<&2, V>}
  %em : {pv(V, b1, x, m1) == pv(V, b1, x, _) : Maybe<&2, V>}
  {==}

def pv.or(-V: Data, b: Bool, -x: V, -m: Maybe<&2, V>, -n: Maybe<&2, V>) -> {orv(V, pv(V, b, x, m), n) == pv(V, b, x, orv(V, m, n)) : Maybe<&2, V>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def orv.none(-V: Data, m: Maybe<&2, V>) -> {orv(V, m, None{}) == m : Maybe<&2, V>}:
  match m:
    case Some{x}:
      {==}
    case None{}:
      {==}

def pk.false(-V: Data, b: Bool, -x: Ent(V), -m: Maybe<&2, Ent(V)>, +e: {b == False{} : Bool}) -> {pk(V, b, x, m) == m : Maybe<&2, Ent(V)>}:
  match b:
    case True{}:
      Empty.absurd({Some{x} == m : Maybe<&2, Ent(V)>}, O.ab.tf(e))
    case False{}:
      {==}

def pk.true(-V: Data, b: Bool, -x: Ent(V), -m: Maybe<&2, Ent(V)>, +e: {b == True{} : Bool}) -> {pk(V, b, x, m) == Some{x} : Maybe<&2, Ent(V)>}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({m == Some{x} : Maybe<&2, Ent(V)>}, O.ab.ft(e))

def pk.cong(-V: Data, -b: Bool, -x: Ent(V), -m1: Maybe<&2, Ent(V)>, -m2: Maybe<&2, Ent(V)>, +em: {m1 == m2 : Maybe<&2, Ent(V)>}) -> {pk(V, b, x, m1) == pk(V, b, x, m2) : Maybe<&2, Ent(V)>}:
  %em : {pk(V, b, x, m1) == pk(V, b, x, _) : Maybe<&2, Ent(V)>}
  {==}

def pk.later(-V: Data, b: Bool, -x: Ent(V), -m: Maybe<&2, Ent(V)>, -n: Maybe<&2, Ent(V)>) -> {later(V, pk(V, b, x, m), n) == pk(V, b, x, later(V, m, n)) : Maybe<&2, Ent(V)>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def later.none(-V: Data, m: Maybe<&2, Ent(V)>) -> {later(V, m, None{}) == m : Maybe<&2, Ent(V)>}:
  match m:
    case Some{x}:
      {==}
    case None{}:
      {==}

def later.assoc(-V: Data, a: Maybe<&2, Ent(V)>, -b: Maybe<&2, Ent(V)>, -c: Maybe<&2, Ent(V)>) -> {later(V, later(V, a, b), c) == later(V, a, later(V, b, c)) : Maybe<&2, Ent(V)>}:
  match a:
    case Some{x}:
      {==}
    case None{}:
      {==}

def later.cong_l(-V: Data, -a1: Maybe<&2, Ent(V)>, -a2: Maybe<&2, Ent(V)>, -b: Maybe<&2, Ent(V)>, +e: {a1 == a2 : Maybe<&2, Ent(V)>}) -> {later(V, a1, b) == later(V, a2, b) : Maybe<&2, Ent(V)>}:
  %e : {later(V, a1, b) == later(V, _, b) : Maybe<&2, Ent(V)>}
  {==}

def later.cong_r(-V: Data, -a: Maybe<&2, Ent(V)>, -b1: Maybe<&2, Ent(V)>, -b2: Maybe<&2, Ent(V)>, +e: {b1 == b2 : Maybe<&2, Ent(V)>}) -> {later(V, a, b1) == later(V, a, b2) : Maybe<&2, Ent(V)>}:
  %e : {later(V, a, b1) == later(V, a, _) : Maybe<&2, Ent(V)>}
  {==}

# a later choice that is something wins
def later.some(-V: Data, -x: Ent(V), -n: Maybe<&2, Ent(V)>) -> {later(V, Some{x}, n) == Some{x} : Maybe<&2, Ent(V)>}:
  {==}

# Scans over an append

def mload.app(-V: Data, xs: Es(V), +ys: Es(V), +i: U32) -> {mload(V, app(V, xs, ys), i) == orv(V, mload(V, xs, i), mload(V, ys, i)) : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(Maybe<&2, V>, pv(V, holds(V, x, i), val(V, x), mload(V, app(V, r, ys), i)), pv(V, holds(V, x, i), val(V, x), orv(V, mload(V, r, i), mload(V, ys, i))), orv(V, pv(V, holds(V, x, i), val(V, x), mload(V, r, i)), mload(V, ys, i)), pv.cong(V, holds(V, x, i), holds(V, x, i), val(V, x), mload(V, app(V, r, ys), i), orv(V, mload(V, r, i), mload(V, ys, i)), {==}, mload.app(V, r, ys, i)), Equal.sym(Maybe<&2, V>, orv(V, pv(V, holds(V, x, i), val(V, x), mload(V, r, i)), mload(V, ys, i)), pv(V, holds(V, x, i), val(V, x), orv(V, mload(V, r, i), mload(V, ys, i))), pv.or(V, holds(V, x, i), val(V, x), mload(V, r, i), mload(V, ys, i))))

def mfind.app(-V: Data, xs: Es(V), +ys: Es(V), +i: U32) -> {mfind(V, app(V, xs, ys), i) == later(V, mfind(V, xs, i), mfind(V, ys, i)) : Maybe<&2, Ent(V)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(Maybe<&2, Ent(V)>, pk(V, O.ule(i, lst(V, x)), x, mfind(V, app(V, r, ys), i)), pk(V, O.ule(i, lst(V, x)), x, later(V, mfind(V, r, i), mfind(V, ys, i))), later(V, pk(V, O.ule(i, lst(V, x)), x, mfind(V, r, i)), mfind(V, ys, i)), pk.cong(V, O.ule(i, lst(V, x)), x, mfind(V, app(V, r, ys), i), later(V, mfind(V, r, i), mfind(V, ys, i)), mfind.app(V, r, ys, i)), Equal.sym(Maybe<&2, Ent(V)>, later(V, pk(V, O.ule(i, lst(V, x)), x, mfind(V, r, i)), mfind(V, ys, i)), pk(V, O.ule(i, lst(V, x)), x, later(V, mfind(V, r, i), mfind(V, ys, i))), pk.later(V, O.ule(i, lst(V, x)), x, mfind(V, r, i), mfind(V, ys, i))))

def mnext.app(-V: Data, xs: Es(V), +ys: Es(V), +i: U32) -> {mnext(V, app(V, xs, ys), i) == later(V, mnext(V, xs, i), mnext(V, ys, i)) : Maybe<&2, Ent(V)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(Maybe<&2, Ent(V)>, pk(V, O.ult(i, fst(V, x)), x, mnext(V, app(V, r, ys), i)), pk(V, O.ult(i, fst(V, x)), x, later(V, mnext(V, r, i), mnext(V, ys, i))), later(V, pk(V, O.ult(i, fst(V, x)), x, mnext(V, r, i)), mnext(V, ys, i)), pk.cong(V, O.ult(i, fst(V, x)), x, mnext(V, app(V, r, ys), i), later(V, mnext(V, r, i), mnext(V, ys, i)), mnext.app(V, r, ys, i)), Equal.sym(Maybe<&2, Ent(V)>, later(V, pk(V, O.ult(i, fst(V, x)), x, mnext(V, r, i)), mnext(V, ys, i)), pk(V, O.ult(i, fst(V, x)), x, later(V, mnext(V, r, i), mnext(V, ys, i))), pk.later(V, O.ult(i, fst(V, x)), x, mnext(V, r, i), mnext(V, ys, i))))

# prev keeps the later candidate: prev(xs ++ ys) is prev(ys), else prev(xs)
def mprev.app(-V: Data, xs: Es(V), +ys: Es(V), +i: U32) -> {mprev(V, app(V, xs, ys), i) == later(V, mprev(V, ys, i), mprev(V, xs, i)) : Maybe<&2, Ent(V)>}:
  match xs:
    case Nil{}:
      Equal.sym(Maybe<&2, Ent(V)>, later(V, mprev(V, ys, i), None{}), mprev(V, ys, i), later.none(V, mprev(V, ys, i)))
    case Con{+x, +r}:
      Equal.trans(Maybe<&2, Ent(V)>, later(V, mprev(V, app(V, r, ys), i), pk(V, O.ult(lst(V, x), i), x, None{})), later(V, later(V, mprev(V, ys, i), mprev(V, r, i)), pk(V, O.ult(lst(V, x), i), x, None{})), later(V, mprev(V, ys, i), later(V, mprev(V, r, i), pk(V, O.ult(lst(V, x), i), x, None{}))), later.cong_l(V, mprev(V, app(V, r, ys), i), later(V, mprev(V, ys, i), mprev(V, r, i)), pk(V, O.ult(lst(V, x), i), x, None{}), mprev.app(V, r, ys, i)), later.assoc(V, mprev(V, ys, i), mprev(V, r, i), pk(V, O.ult(lst(V, x), i), x, None{})))

def gscan(-V: Data, xs: Es(V), st: M.MapleGap<U32>, +d: U32, +max: U32) -> M.MapleGap<U32>:
  M.MapleModel.gap_scan(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.add, V, xs, st, d, max)

def gscan.app(-V: Data, xs: Es(V), +ys: Es(V), st: M.MapleGap<U32>, +d: U32, +max: U32) -> {gscan(V, app(V, xs, ys), st, d, max) == gscan(V, ys, gscan(V, xs, st, d, max), d, max) : M.MapleGap<U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      gscan.app(V, r, ys, M.MapleModel.gap_step(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.add, V, st, x, d, max), d, max)

# Scans that find nothing

# every entry ends at or before p < i: none holds i
def mload.none_le(-V: Data, xs: Es(V), +p: U32, +i: U32, +h: {lasts_le(V, xs, p) == True{} : Bool}, +g: {O.ult(p, i) == True{} : Bool}) -> {mload(V, xs, i) == None{} : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(Maybe<&2, V>, pv(V, holds(V, x, i), val(V, x), mload(V, r, i)), mload(V, r, i), None{}, pv.false(V, holds(V, x, i), val(V, x), mload(V, r, i), O.bo.and_false_r(O.ule(fst(V, x), i), O.ule(i, lst(V, x)), O.u.lt_not_le(lst(V, x), i, O.u.le_lt(lst(V, x), p, i, O.bo.and_l(O.ule(lst(V, x), p), lasts_le(V, r, p), h), g)))), mload.none_le(V, r, p, i, O.bo.and_r(O.ule(lst(V, x), p), lasts_le(V, r, p), h), g))

# every entry starts after k >= i: none holds i
def mload.none_aft(-V: Data, xs: Es(V), +k: U32, +i: U32, +h: {aft(V, k, xs) == True{} : Bool}, +g: {O.ule(i, k) == True{} : Bool}) -> {mload(V, xs, i) == None{} : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(Maybe<&2, V>, pv(V, holds(V, x, i), val(V, x), mload(V, r, i)), mload(V, r, i), None{}, pv.false(V, holds(V, x, i), val(V, x), mload(V, r, i), O.bo.and_false_l(O.ule(fst(V, x), i), O.ule(i, lst(V, x)), O.u.lt_not_le(i, fst(V, x), O.u.le_lt(i, k, fst(V, x), g, aft.head(V, k, x, r, h))))), mload.none_aft(V, r, k, i, aft.tail(V, k, x, r, h), g))

# Cutting below a and above b: what each index loads

def cutlo(-V: Data, eb: Bool, sb: Bool, x: Ent(V), d: U32, rest: Es(V)) -> Es(V):
  M.MapleModel.cut_lo(U32, V, eb, sb, x, d, rest)

def cuthi(-V: Data, sa: Bool, ea: Bool, x: Ent(V), s: U32, rest: Es(V)) -> Es(V):
  M.MapleModel.cut_hi(U32, V, sa, ea, x, s, rest)

def hs(-V: Data, +f: U32, +l: U32, +v: V, +i: U32) -> Bool:
  holds(V, M.MapleEntry{f, l, v}, i)

def lbl.go(-V: Data, eb: Bool, sb: Bool, +f: U32, +l: U32, +v: V, +r: Es(V), +a: U32, +i: U32, +e1: {O.ult(l, a) == eb : Bool}, +e2: {O.ult(f, a) == sb : Bool}, +h: {O.ult(i, a) == True{} : Bool}, +ih: {mload(V, below(V, r, a), i) == mload(V, r, i) : Maybe<&2, V>}) -> {mload(V, cutlo(V, eb, sb, M.MapleEntry{f, l, v}, U32.sub(a, 1), below(V, r, a)), i) == pv(V, hs(V, f, l, v, i), v, mload(V, r, i)) : Maybe<&2, V>}:
  match eb:
    case True{}:
      pv.cong(V, hs(V, f, l, v, i), hs(V, f, l, v, i), v, mload(V, below(V, r, a), i), mload(V, r, i), {==}, ih)
    case False{}:
      match sb:
        case True{}:
          pv.cong(V, hs(V, f, U32.sub(a, 1), v, i), hs(V, f, l, v, i), v, mload(V, below(V, r, a), i), mload(V, r, i), Equal.trans(Bool, Bool.and(O.ule(f, i), O.ule(i, U32.sub(a, 1))), O.ule(f, i), Bool.and(O.ule(f, i), O.ule(i, l)), bo.and_true_r(O.ule(f, i), O.ule(i, U32.sub(a, 1)), O.u.dec_le(i, a, h)), Equal.sym(Bool, Bool.and(O.ule(f, i), O.ule(i, l)), O.ule(f, i), bo.and_true_r(O.ule(f, i), O.ule(i, l), O.u.le_of_lt(i, l, O.u.lt_le(i, a, l, h, O.u.not_lt(l, a, e1)))))), ih)
        case False{}:
          Equal.trans(Maybe<&2, V>, mload(V, below(V, r, a), i), mload(V, r, i), pv(V, hs(V, f, l, v, i), v, mload(V, r, i)), ih, Equal.sym(Maybe<&2, V>, pv(V, hs(V, f, l, v, i), v, mload(V, r, i)), mload(V, r, i), pv.false(V, hs(V, f, l, v, i), v, mload(V, r, i), O.bo.and_false_l(O.ule(f, i), O.ule(i, l), O.u.lt_not_le(i, f, O.u.lt_le(i, a, f, h, O.u.not_lt(f, a, e2)))))))

# below a, an index under a loads as before
def load_below_lt(-V: Data, xs: Es(V), +a: U32, +i: U32, +h: {O.ult(i, a) == True{} : Bool}) -> {mload(V, below(V, xs, a), i) == mload(V, xs, i) : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{M.MapleEntry{+f, +l, +v}, +r}:
      lbl.go(V, O.ult(l, a), O.ult(f, a), f, l, v, r, a, i, {==}, {==}, h, load_below_lt(V, r, a, i, h))

def lbg.go(-V: Data, eb: Bool, sb: Bool, +f: U32, +l: U32, +v: V, +r: Es(V), +a: U32, +i: U32, +e1: {O.ult(l, a) == eb : Bool}, +e2: {O.ult(f, a) == sb : Bool}, +h: {O.ule(a, i) == True{} : Bool}, +ih: {mload(V, below(V, r, a), i) == None{} : Maybe<&2, V>}) -> {mload(V, cutlo(V, eb, sb, M.MapleEntry{f, l, v}, U32.sub(a, 1), below(V, r, a)), i) == None{} : Maybe<&2, V>}:
  match eb:
    case True{}:
      Equal.trans(Maybe<&2, V>, pv(V, hs(V, f, l, v, i), v, mload(V, below(V, r, a), i)), mload(V, below(V, r, a), i), None{}, pv.false(V, hs(V, f, l, v, i), v, mload(V, below(V, r, a), i), O.bo.and_false_r(O.ule(f, i), O.ule(i, l), O.u.lt_not_le(l, i, O.u.lt_le(l, a, i, e1, h)))), ih)
    case False{}:
      match sb:
        case True{}:
          Equal.trans(Maybe<&2, V>, pv(V, hs(V, f, U32.sub(a, 1), v, i), v, mload(V, below(V, r, a), i)), mload(V, below(V, r, a), i), None{}, pv.false(V, hs(V, f, U32.sub(a, 1), v, i), v, mload(V, below(V, r, a), i), O.bo.and_false_r(O.ule(f, i), O.ule(i, U32.sub(a, 1)), O.u.lt_not_le(U32.sub(a, 1), i, O.u.lt_le(U32.sub(a, 1), a, i, O.u.dec_lt(f, a, e2), h)))), ih)
        case False{}:
          ih

# below a, an index from a on loads nothing
def load_below_ge(-V: Data, xs: Es(V), +a: U32, +i: U32, +h: {O.ule(a, i) == True{} : Bool}) -> {mload(V, below(V, xs, a), i) == None{} : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{M.MapleEntry{+f, +l, +v}, +r}:
      lbg.go(V, O.ult(l, a), O.ult(f, a), f, l, v, r, a, i, {==}, {==}, h, load_below_ge(V, r, a, i, h))

def lag.go(-V: Data, sa: Bool, ea: Bool, +f: U32, +l: U32, +v: V, +r: Es(V), +b: U32, +i: U32, +e1: {O.ult(b, f) == sa : Bool}, +e2: {O.ult(b, l) == ea : Bool}, +h: {O.ult(b, i) == True{} : Bool}, +ih: {mload(V, above(V, r, b), i) == mload(V, r, i) : Maybe<&2, V>}) -> {mload(V, cuthi(V, sa, ea, M.MapleEntry{f, l, v}, U32.inc(b), above(V, r, b)), i) == pv(V, hs(V, f, l, v, i), v, mload(V, r, i)) : Maybe<&2, V>}:
  match sa:
    case True{}:
      pv.cong(V, hs(V, f, l, v, i), hs(V, f, l, v, i), v, mload(V, above(V, r, b), i), mload(V, r, i), {==}, ih)
    case False{}:
      match ea:
        case True{}:
          pv.cong(V, hs(V, U32.inc(b), l, v, i), hs(V, f, l, v, i), v, mload(V, above(V, r, b), i), mload(V, r, i), Equal.trans(Bool, Bool.and(O.ule(U32.inc(b), i), O.ule(i, l)), O.ule(i, l), Bool.and(O.ule(f, i), O.ule(i, l)), bo.and_true_l(O.ule(U32.inc(b), i), O.ule(i, l), O.u.inc_le(b, i, h)), Equal.sym(Bool, Bool.and(O.ule(f, i), O.ule(i, l)), O.ule(i, l), bo.and_true_l(O.ule(f, i), O.ule(i, l), O.u.le_of_lt(f, i, O.u.le_lt(f, b, i, O.u.not_lt(b, f, e1), h))))), ih)
        case False{}:
          Equal.trans(Maybe<&2, V>, mload(V, above(V, r, b), i), mload(V, r, i), pv(V, hs(V, f, l, v, i), v, mload(V, r, i)), ih, Equal.sym(Maybe<&2, V>, pv(V, hs(V, f, l, v, i), v, mload(V, r, i)), mload(V, r, i), pv.false(V, hs(V, f, l, v, i), v, mload(V, r, i), O.bo.and_false_r(O.ule(f, i), O.ule(i, l), O.u.lt_not_le(l, i, O.u.le_lt(l, b, i, O.u.not_lt(b, l, e2), h))))))

# above b, an index over b loads as before
def load_above_gt(-V: Data, xs: Es(V), +b: U32, +i: U32, +h: {O.ult(b, i) == True{} : Bool}) -> {mload(V, above(V, xs, b), i) == mload(V, xs, i) : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{M.MapleEntry{+f, +l, +v}, +r}:
      lag.go(V, O.ult(b, f), O.ult(b, l), f, l, v, r, b, i, {==}, {==}, h, load_above_gt(V, r, b, i, h))

def lal.go(-V: Data, sa: Bool, ea: Bool, +f: U32, +l: U32, +v: V, +r: Es(V), +b: U32, +i: U32, +e1: {O.ult(b, f) == sa : Bool}, +e2: {O.ult(b, l) == ea : Bool}, +h: {O.ule(i, b) == True{} : Bool}, +ih: {mload(V, above(V, r, b), i) == None{} : Maybe<&2, V>}) -> {mload(V, cuthi(V, sa, ea, M.MapleEntry{f, l, v}, U32.inc(b), above(V, r, b)), i) == None{} : Maybe<&2, V>}:
  match sa:
    case True{}:
      Equal.trans(Maybe<&2, V>, pv(V, hs(V, f, l, v, i), v, mload(V, above(V, r, b), i)), mload(V, above(V, r, b), i), None{}, pv.false(V, hs(V, f, l, v, i), v, mload(V, above(V, r, b), i), O.bo.and_false_l(O.ule(f, i), O.ule(i, l), O.u.lt_not_le(i, f, O.u.le_lt(i, b, f, h, e1)))), ih)
    case False{}:
      match ea:
        case True{}:
          Equal.trans(Maybe<&2, V>, pv(V, hs(V, U32.inc(b), l, v, i), v, mload(V, above(V, r, b), i)), mload(V, above(V, r, b), i), None{}, pv.false(V, hs(V, U32.inc(b), l, v, i), v, mload(V, above(V, r, b), i), O.bo.and_false_l(O.ule(U32.inc(b), i), O.ule(i, l), O.u.lt_not_le(i, U32.inc(b), O.u.le_lt(i, b, U32.inc(b), h, O.u.inc_gt(b, l, e2))))), ih)
        case False{}:
          ih

# above b, an index at or below b loads nothing
def load_above_le(-V: Data, xs: Es(V), +b: U32, +i: U32, +h: {O.ule(i, b) == True{} : Bool}) -> {mload(V, above(V, xs, b), i) == None{} : Maybe<&2, V>}:
  match xs:
    case Nil{}:
      {==}
    case Con{M.MapleEntry{+f, +l, +v}, +r}:
      lal.go(V, O.ult(b, f), O.ult(b, l), f, l, v, r, b, i, {==}, {==}, h, load_above_le(V, r, b, i, h))

# set_range and clear_range, on the model: what each index loads

def msr(-V: Data, +xs: Es(V), +a: U32, +b: U32, v: V) -> Es(V):
  M.MapleModel.set_range(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, xs, a, b, v)

def msr.go(-V: Data, ok: Bool, +xs: Es(V), +a: U32, +b: U32, v: V) -> Es(V):
  M.MapleModel.set_range.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, ok, xs, a, b, v)

def mcr(-V: Data, +xs: Es(V), +a: U32, +b: U32) -> Es(V):
  M.MapleModel.clear_range(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, xs, a, b)

def mcr.go(-V: Data, ok: Bool, +xs: Es(V), +a: U32, +b: U32) -> Es(V):
  M.MapleModel.clear_range.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, ok, xs, a, b)

def sli.go(-V: Data, ok: Bool, +xs: Es(V), +a: U32, +b: U32, +v: V, +i: U32, +e: {O.ule(a, b) == ok : Bool}, +f: {O.ule(a, i) == True{} : Bool}, +g: {O.ule(i, b) == True{} : Bool}) -> {mload(V, msr.go(V, ok, xs, a, b, v), i) == Some{v} : Maybe<&2, V>}:
  match ok:
    case True{}:
      %Equal.sym(Maybe<&2, V>, mload(V, app(V, below(V, xs, a), Con{M.MapleEntry{a, b, v}, above(V, xs, b)}), i), orv(V, mload(V, below(V, xs, a), i), mload(V, Con{M.MapleEntry{a, b, v}, above(V, xs, b)}, i)), mload.app(V, below(V, xs, a), Con{M.MapleEntry{a, b, v}, above(V, xs, b)}, i)) : {_ == Some{v} : Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, mload(V, below(V, xs, a), i), None{}, load_below_ge(V, xs, a, i, f)) : {orv(V, _, mload(V, Con{M.MapleEntry{a, b, v}, above(V, xs, b)}, i)) == Some{v} : Maybe<&2, V>}
      pv.true(V, hs(V, a, b, v, i), v, mload(V, above(V, xs, b), i), O.bo.and_intro(O.ule(a, i), O.ule(i, b), f, g))
    case False{}:
      Empty.absurd({mload(V, xs, i) == Some{v} : Maybe<&2, V>}, O.bo.not_true(O.ule(a, b), O.u.le_trans(a, i, b, f, g), e))

# after set_range(a, b, v), an index of [a, b] loads v
def set_load_in(-V: Data, +xs: Es(V), +a: U32, +b: U32, +v: V, +i: U32, +f: {O.ule(a, i) == True{} : Bool}, +g: {O.ule(i, b) == True{} : Bool}) -> {mload(V, msr(V, xs, a, b, v), i) == Some{v} : Maybe<&2, V>}:
  sli.go(V, O.ule(a, b), xs, a, b, v, i, {==}, f, g)

def slo.lt(-V: Data, +xs: Es(V), +a: U32, +b: U32, +v: V, +i: U32, +ok: {O.ule(a, b) == True{} : Bool}, +lt: {O.ult(i, a) == True{} : Bool}, +nf: {O.ule(a, i) == False{} : Bool}) -> {mload(V, app(V, below(V, xs, a), Con{M.MapleEntry{a, b, v}, above(V, xs, b)}), i) == mload(V, xs, i) : Maybe<&2, V>}:
  %Equal.sym(Maybe<&2, V>, mload(V, app(V, below(V, xs, a), Con{M.MapleEntry{a, b, v}, above(V, xs, b)}), i), orv(V, mload(V, below(V, xs, a), i), mload(V, Con{M.MapleEntry{a, b, v}, above(V, xs, b)}, i)), mload.app(V, below(V, xs, a), Con{M.MapleEntry{a, b, v}, above(V, xs, b)}, i)) : {_ == mload(V, xs, i) : Maybe<&2, V>}
  %Equal.sym(Maybe<&2, V>, mload(V, below(V, xs, a), i), mload(V, xs, i), load_below_lt(V, xs, a, i, lt)) : {orv(V, _, mload(V, Con{M.MapleEntry{a, b, v}, above(V, xs, b)}, i)) == mload(V, xs, i) : Maybe<&2, V>}
  %Equal.sym(Maybe<&2, V>, pv(V, hs(V, a, b, v, i), v, mload(V, above(V, xs, b), i)), mload(V, above(V, xs, b), i), pv.false(V, hs(V, a, b, v, i), v, mload(V, above(V, xs, b), i), O.bo.and_false_l(O.ule(a, i), O.ule(i, b), nf))) : {orv(V, mload(V, xs, i), _) == mload(V, xs, i) : Maybe<&2, V>}
  %Equal.sym(Maybe<&2, V>, mload(V, above(V, xs, b), i), None{}, load_above_le(V, xs, b, i, O.u.le_of_lt(i, b, O.u.lt_le(i, a, b, lt, ok)))) : {orv(V, mload(V, xs, i), _) == mload(V, xs, i) : Maybe<&2, V>}
  orv.none(V, mload(V, xs, i))

def slo.gt(-V: Data, +xs: Es(V), +a: U32, +b: U32, +v: V, +i: U32, +ai: {O.ule(a, i) == True{} : Bool}, +gt: {O.ult(b, i) == True{} : Bool}, +nh: {hs(V, a, b, v, i) == False{} : Bool}) -> {mload(V, app(V, below(V, xs, a), Con{M.MapleEntry{a, b, v}, above(V, xs, b)}), i) == mload(V, xs, i) : Maybe<&2, V>}:
  %Equal.sym(Maybe<&2, V>, mload(V, app(V, below(V, xs, a), Con{M.MapleEntry{a, b, v}, above(V, xs, b)}), i), orv(V, mload(V, below(V, xs, a), i), mload(V, Con{M.MapleEntry{a, b, v}, above(V, xs, b)}, i)), mload.app(V, below(V, xs, a), Con{M.MapleEntry{a, b, v}, above(V, xs, b)}, i)) : {_ == mload(V, xs, i) : Maybe<&2, V>}
  %Equal.sym(Maybe<&2, V>, mload(V, below(V, xs, a), i), None{}, load_below_ge(V, xs, a, i, ai)) : {orv(V, _, mload(V, Con{M.MapleEntry{a, b, v}, above(V, xs, b)}, i)) == mload(V, xs, i) : Maybe<&2, V>}
  %Equal.sym(Maybe<&2, V>, pv(V, hs(V, a, b, v, i), v, mload(V, above(V, xs, b), i)), mload(V, above(V, xs, b), i), pv.false(V, hs(V, a, b, v, i), v, mload(V, above(V, xs, b), i), nh)) : {orv(V, None{}, _) == mload(V, xs, i) : Maybe<&2, V>}
  load_above_gt(V, xs, b, i, gt)

def slo.ai(-V: Data, c: Bool, +xs: Es(V), +a: U32, +b: U32, +v: V, +i: U32, +ok: {O.ule(a, b) == True{} : Bool}, +e: {O.ule(a, i) == c : Bool}, +f: {Bool.and(O.ule(a, i), O.ule(i, b)) == False{} : Bool}) -> {mload(V, app(V, below(V, xs, a), Con{M.MapleEntry{a, b, v}, above(V, xs, b)}), i) == mload(V, xs, i) : Maybe<&2, V>}:
  match c:
    case False{}:
      slo.lt(V, xs, a, b, v, i, ok, O.u.not_le(a, i, e), e)
    case True{}:
      slo.gt(V, xs, a, b, v, i, e, O.u.not_le(i, b, O.bo.and_false_rest(O.ule(a, i), O.ule(i, b), f, e)), f)

def slo.go(-V: Data, ok: Bool, +xs: Es(V), +a: U32, +b: U32, +v: V, +i: U32, +e: {O.ule(a, b) == ok : Bool}, +f: {Bool.and(O.ule(a, i), O.ule(i, b)) == False{} : Bool}) -> {mload(V, msr.go(V, ok, xs, a, b, v), i) == mload(V, xs, i) : Maybe<&2, V>}:
  match ok:
    case True{}:
      slo.ai(V, O.ule(a, i), xs, a, b, v, i, e, {==}, f)
    case False{}:
      {==}

# after set_range(a, b, v), an index outside [a, b] loads as before
def set_load_out(-V: Data, +xs: Es(V), +a: U32, +b: U32, +v: V, +i: U32, +f: {Bool.and(O.ule(a, i), O.ule(i, b)) == False{} : Bool}) -> {mload(V, msr(V, xs, a, b, v), i) == mload(V, xs, i) : Maybe<&2, V>}:
  slo.go(V, O.ule(a, b), xs, a, b, v, i, {==}, f)

def cli.go(-V: Data, ok: Bool, +xs: Es(V), +a: U32, +b: U32, +i: U32, +e: {O.ule(a, b) == ok : Bool}, +f: {O.ule(a, i) == True{} : Bool}, +g: {O.ule(i, b) == True{} : Bool}) -> {mload(V, mcr.go(V, ok, xs, a, b), i) == None{} : Maybe<&2, V>}:
  match ok:
    case True{}:
      %Equal.sym(Maybe<&2, V>, mload(V, app(V, below(V, xs, a), above(V, xs, b)), i), orv(V, mload(V, below(V, xs, a), i), mload(V, above(V, xs, b), i)), mload.app(V, below(V, xs, a), above(V, xs, b), i)) : {_ == None{} : Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, mload(V, below(V, xs, a), i), None{}, load_below_ge(V, xs, a, i, f)) : {orv(V, _, mload(V, above(V, xs, b), i)) == None{} : Maybe<&2, V>}
      load_above_le(V, xs, b, i, g)
    case False{}:
      Empty.absurd({mload(V, xs, i) == None{} : Maybe<&2, V>}, O.bo.not_true(O.ule(a, b), O.u.le_trans(a, i, b, f, g), e))

# after clear_range(a, b), an index of [a, b] loads nothing
def clear_load_in(-V: Data, +xs: Es(V), +a: U32, +b: U32, +i: U32, +f: {O.ule(a, i) == True{} : Bool}, +g: {O.ule(i, b) == True{} : Bool}) -> {mload(V, mcr(V, xs, a, b), i) == None{} : Maybe<&2, V>}:
  cli.go(V, O.ule(a, b), xs, a, b, i, {==}, f, g)

def clo.ai(-V: Data, c: Bool, +xs: Es(V), +a: U32, +b: U32, +i: U32, +ok: {O.ule(a, b) == True{} : Bool}, +e: {O.ule(a, i) == c : Bool}, +f: {Bool.and(O.ule(a, i), O.ule(i, b)) == False{} : Bool}) -> {mload(V, app(V, below(V, xs, a), above(V, xs, b)), i) == mload(V, xs, i) : Maybe<&2, V>}:
  match c:
    case False{}:
      %Equal.sym(Maybe<&2, V>, mload(V, app(V, below(V, xs, a), above(V, xs, b)), i), orv(V, mload(V, below(V, xs, a), i), mload(V, above(V, xs, b), i)), mload.app(V, below(V, xs, a), above(V, xs, b), i)) : {_ == mload(V, xs, i) : Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, mload(V, below(V, xs, a), i), mload(V, xs, i), load_below_lt(V, xs, a, i, O.u.not_le(a, i, e))) : {orv(V, _, mload(V, above(V, xs, b), i)) == mload(V, xs, i) : Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, mload(V, above(V, xs, b), i), None{}, load_above_le(V, xs, b, i, O.u.le_of_lt(i, b, O.u.lt_le(i, a, b, O.u.not_le(a, i, e), ok)))) : {orv(V, mload(V, xs, i), _) == mload(V, xs, i) : Maybe<&2, V>}
      orv.none(V, mload(V, xs, i))
    case True{}:
      %Equal.sym(Maybe<&2, V>, mload(V, app(V, below(V, xs, a), above(V, xs, b)), i), orv(V, mload(V, below(V, xs, a), i), mload(V, above(V, xs, b), i)), mload.app(V, below(V, xs, a), above(V, xs, b), i)) : {_ == mload(V, xs, i) : Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, mload(V, below(V, xs, a), i), None{}, load_below_ge(V, xs, a, i, e)) : {orv(V, _, mload(V, above(V, xs, b), i)) == mload(V, xs, i) : Maybe<&2, V>}
      load_above_gt(V, xs, b, i, O.u.not_le(i, b, O.bo.and_false_rest(O.ule(a, i), O.ule(i, b), f, e)))

def clo.go(-V: Data, ok: Bool, +xs: Es(V), +a: U32, +b: U32, +i: U32, +e: {O.ule(a, b) == ok : Bool}, +f: {Bool.and(O.ule(a, i), O.ule(i, b)) == False{} : Bool}) -> {mload(V, mcr.go(V, ok, xs, a, b), i) == mload(V, xs, i) : Maybe<&2, V>}:
  match ok:
    case True{}:
      clo.ai(V, O.ule(a, i), xs, a, b, i, e, {==}, f)
    case False{}:
      {==}

# after clear_range(a, b), an index outside [a, b] loads as before
def clear_load_out(-V: Data, +xs: Es(V), +a: U32, +b: U32, +i: U32, +f: {Bool.and(O.ule(a, i), O.ule(i, b)) == False{} : Bool}) -> {mload(V, mcr(V, xs, a, b), i) == mload(V, xs, i) : Maybe<&2, V>}:
  clo.go(V, O.ule(a, b), xs, a, b, i, {==}, f)

# The invariant through cutting

def abl.go(-V: Data, eb: Bool, sb: Bool, +f: U32, +l: U32, +v: V, +r: Es(V), +k: U32, +a: U32, +h1: {O.ult(k, f) == True{} : Bool}, +ih: {aft(V, k, below(V, r, a)) == True{} : Bool}) -> {aft(V, k, cutlo(V, eb, sb, M.MapleEntry{f, l, v}, U32.sub(a, 1), below(V, r, a))) == True{} : Bool}:
  match eb:
    case True{}:
      O.bo.and_intro(O.ult(k, f), aft(V, k, below(V, r, a)), h1, ih)
    case False{}:
      match sb:
        case True{}:
          O.bo.and_intro(O.ult(k, f), aft(V, k, below(V, r, a)), h1, ih)
        case False{}:
          ih

# cutting below a keeps every entry after k
def aft.below(-V: Data, +k: U32, xs: Es(V), +a: U32, +h: {aft(V, k, xs) == True{} : Bool}) -> {aft(V, k, below(V, xs, a)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{M.MapleEntry{+f, +l, +v}, +r}:
      abl.go(V, O.ult(l, a), O.ult(f, a), f, l, v, r, k, a, aft.head(V, k, M.MapleEntry{f, l, v}, r, h), aft.below(V, k, r, a, aft.tail(V, k, M.MapleEntry{f, l, v}, r, h)))

def aab.go(-V: Data, sa: Bool, ea: Bool, +f: U32, +l: U32, +v: V, +r: Es(V), +k: U32, +b: U32, +e1: {O.ult(b, f) == sa : Bool}, +e2: {O.ult(b, l) == ea : Bool}, +h1: {O.ult(k, f) == True{} : Bool}, +ih: {aft(V, k, above(V, r, b)) == True{} : Bool}) -> {aft(V, k, cuthi(V, sa, ea, M.MapleEntry{f, l, v}, U32.inc(b), above(V, r, b))) == True{} : Bool}:
  match sa:
    case True{}:
      O.bo.and_intro(O.ult(k, f), aft(V, k, above(V, r, b)), h1, ih)
    case False{}:
      match ea:
        case True{}:
          O.bo.and_intro(O.ult(k, U32.inc(b)), aft(V, k, above(V, r, b)), O.u.lt_trans(k, b, U32.inc(b), O.u.lt_le(k, f, b, h1, O.u.not_lt(b, f, e1)), O.u.inc_gt(b, l, e2)), ih)
        case False{}:
          ih

# cutting above b keeps every entry after k
def aft.above(-V: Data, +k: U32, xs: Es(V), +b: U32, +h: {aft(V, k, xs) == True{} : Bool}) -> {aft(V, k, above(V, xs, b)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{M.MapleEntry{+f, +l, +v}, +r}:
      aab.go(V, O.ult(b, f), O.ult(b, l), f, l, v, r, k, b, {==}, {==}, aft.head(V, k, M.MapleEntry{f, l, v}, r, h), aft.above(V, k, r, b, aft.tail(V, k, M.MapleEntry{f, l, v}, r, h)))

def lbt.go(-V: Data, eb: Bool, sb: Bool, +f: U32, +l: U32, +v: V, +r: Es(V), +a: U32, +e1: {O.ult(l, a) == eb : Bool}, +e2: {O.ult(f, a) == sb : Bool}, +ih: {lasts_lt(V, below(V, r, a), a) == True{} : Bool}) -> {lasts_lt(V, cutlo(V, eb, sb, M.MapleEntry{f, l, v}, U32.sub(a, 1), below(V, r, a)), a) == True{} : Bool}:
  match eb:
    case True{}:
      O.bo.and_intro(O.ult(l, a), lasts_lt(V, below(V, r, a), a), e1, ih)
    case False{}:
      match sb:
        case True{}:
          O.bo.and_intro(O.ult(U32.sub(a, 1), a), lasts_lt(V, below(V, r, a), a), O.u.dec_lt(f, a, e2), ih)
        case False{}:
          ih

# below a, everything ends before a
def lasts.below(-V: Data, xs: Es(V), +a: U32) -> {lasts_lt(V, below(V, xs, a), a) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{M.MapleEntry{+f, +l, +v}, +r}:
      lbt.go(V, O.ult(l, a), O.ult(f, a), f, l, v, r, a, {==}, {==}, lasts.below(V, r, a))

def fat.go(-V: Data, sa: Bool, ea: Bool, +f: U32, +l: U32, +v: V, +r: Es(V), +b: U32, +e1: {O.ult(b, f) == sa : Bool}, +e2: {O.ult(b, l) == ea : Bool}, +ih: {aft(V, b, above(V, r, b)) == True{} : Bool}) -> {aft(V, b, cuthi(V, sa, ea, M.MapleEntry{f, l, v}, U32.inc(b), above(V, r, b))) == True{} : Bool}:
  match sa:
    case True{}:
      O.bo.and_intro(O.ult(b, f), aft(V, b, above(V, r, b)), e1, ih)
    case False{}:
      match ea:
        case True{}:
          O.bo.and_intro(O.ult(b, U32.inc(b)), aft(V, b, above(V, r, b)), O.u.inc_gt(b, l, e2), ih)
        case False{}:
          ih

# above b, everything starts after b
def firsts.above(-V: Data, xs: Es(V), +b: U32) -> {aft(V, b, above(V, xs, b)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{M.MapleEntry{+f, +l, +v}, +r}:
      fat.go(V, O.ult(b, f), O.ult(b, l), f, l, v, r, b, {==}, {==}, firsts.above(V, r, b))

def bnil.go(-V: Data, eb: Bool, sb: Bool, +f: U32, +l: U32, +v: V, +r: Es(V), +a: U32, +e1: {O.ult(l, a) == eb : Bool}, +e2: {O.ult(f, a) == sb : Bool}, +n1: {O.ult(l, a) == False{} : Bool}, +n2: {O.ult(f, a) == False{} : Bool}, +ih: {below(V, r, a) == Nil{} : Es(V)}) -> {cutlo(V, eb, sb, M.MapleEntry{f, l, v}, U32.sub(a, 1), below(V, r, a)) == Nil{} : Es(V)}:
  match eb:
    case True{}:
      Empty.absurd({Con{M.MapleEntry{f, l, v}, below(V, r, a)} == Nil{} : Es(V)}, O.bo.not_true(O.ult(l, a), e1, n1))
    case False{}:
      match sb:
        case True{}:
          Empty.absurd({Con{M.MapleEntry{f, U32.sub(a, 1), v}, below(V, r, a)} == Nil{} : Es(V)}, O.bo.not_true(O.ult(f, a), e2, n2))
        case False{}:
          ih

# an ordered list after k >= a has nothing below a
def below.nil(-V: Data, xs: Es(V), +k: U32, +a: U32, +w: {wf(V, xs) == True{} : Bool}, +h: {aft(V, k, xs) == True{} : Bool}, +g: {O.ule(a, k) == True{} : Bool}) -> {below(V, xs, a) == Nil{} : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{M.MapleEntry{+f, +l, +v}, +r}:
      +af = O.u.le_lt(a, k, f, g, aft.head(V, k, M.MapleEntry{f, l, v}, r, h))
      bnil.go(V, O.ult(l, a), O.ult(f, a), f, l, v, r, a, {==}, {==}, O.u.le_not_lt(a, l, O.u.le_of_lt(a, l, O.u.lt_le(a, f, l, af, wf.le(V, M.MapleEntry{f, l, v}, r, w)))), O.u.le_not_lt(a, f, O.u.le_of_lt(a, f, af)), below.nil(V, r, k, a, wf.tail(V, M.MapleEntry{f, l, v}, r, w), aft.tail(V, k, M.MapleEntry{f, l, v}, r, h), g))

def wbl.go(-V: Data, eb: Bool, sb: Bool, +f: U32, +l: U32, +v: V, +r: Es(V), +a: U32, +e1: {O.ult(l, a) == eb : Bool}, +e2: {O.ult(f, a) == sb : Bool}, +w: {wf(V, Con{M.MapleEntry{f, l, v}, r}) == True{} : Bool}, +ih: {wf(V, below(V, r, a)) == True{} : Bool}) -> {wf(V, cutlo(V, eb, sb, M.MapleEntry{f, l, v}, U32.sub(a, 1), below(V, r, a))) == True{} : Bool}:
  match eb:
    case True{}:
      wf.intro(V, M.MapleEntry{f, l, v}, below(V, r, a), wf.le(V, M.MapleEntry{f, l, v}, r, w), aft.below(V, l, r, a, wf.aft(V, M.MapleEntry{f, l, v}, r, w)), ih)
    case False{}:
      match sb:
        case True{}:
          %Equal.sym(Es(V), below(V, r, a), Nil{}, below.nil(V, r, l, a, wf.tail(V, M.MapleEntry{f, l, v}, r, w), wf.aft(V, M.MapleEntry{f, l, v}, r, w), O.u.not_lt(l, a, e1))) : {wf(V, Con{M.MapleEntry{f, U32.sub(a, 1), v}, _}) == True{} : Bool}
          O.bo.and_intro(O.ule(f, U32.sub(a, 1)), Bool.and(True{}, True{}), O.u.dec_le(f, a, e2), {==})
        case False{}:
          ih

def wf.below(-V: Data, xs: Es(V), +a: U32, +w: {wf(V, xs) == True{} : Bool}) -> {wf(V, below(V, xs, a)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{M.MapleEntry{+f, +l, +v}, +r}:
      wbl.go(V, O.ult(l, a), O.ult(f, a), f, l, v, r, a, {==}, {==}, w, wf.below(V, r, a, wf.tail(V, M.MapleEntry{f, l, v}, r, w)))

def wab.go(-V: Data, sa: Bool, ea: Bool, +f: U32, +l: U32, +v: V, +r: Es(V), +b: U32, +e1: {O.ult(b, f) == sa : Bool}, +e2: {O.ult(b, l) == ea : Bool}, +w: {wf(V, Con{M.MapleEntry{f, l, v}, r}) == True{} : Bool}, +ih: {wf(V, above(V, r, b)) == True{} : Bool}) -> {wf(V, cuthi(V, sa, ea, M.MapleEntry{f, l, v}, U32.inc(b), above(V, r, b))) == True{} : Bool}:
  match sa:
    case True{}:
      wf.intro(V, M.MapleEntry{f, l, v}, above(V, r, b), wf.le(V, M.MapleEntry{f, l, v}, r, w), aft.above(V, l, r, b, wf.aft(V, M.MapleEntry{f, l, v}, r, w)), ih)
    case False{}:
      match ea:
        case True{}:
          wf.intro(V, M.MapleEntry{U32.inc(b), l, v}, above(V, r, b), O.u.inc_le(b, l, e2), aft.above(V, l, r, b, wf.aft(V, M.MapleEntry{f, l, v}, r, w)), ih)
        case False{}:
          ih

def wf.above(-V: Data, xs: Es(V), +b: U32, +w: {wf(V, xs) == True{} : Bool}) -> {wf(V, above(V, xs, b)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{M.MapleEntry{+f, +l, +v}, +r}:
      wab.go(V, O.ult(b, f), O.ult(b, l), f, l, v, r, b, {==}, {==}, w, wf.above(V, r, b, wf.tail(V, M.MapleEntry{f, l, v}, r, w)))

def wsr.go(-V: Data, ok: Bool, +xs: Es(V), +a: U32, +b: U32, +v: V, +e: {O.ule(a, b) == ok : Bool}, +w: {wf(V, xs) == True{} : Bool}) -> {wf(V, msr.go(V, ok, xs, a, b, v)) == True{} : Bool}:
  match ok:
    case True{}:
      wf.app_intro(V, below(V, xs, a), Con{M.MapleEntry{a, b, v}, above(V, xs, b)}, a, wf.below(V, xs, a, w), wf.intro(V, M.MapleEntry{a, b, v}, above(V, xs, b), e, firsts.above(V, xs, b), wf.above(V, xs, b, w)), lasts.below(V, xs, a), O.bo.and_intro(O.ule(a, a), firsts_ge(V, above(V, xs, b), a), O.u.le_refl(a), ge.of_aft(V, a, b, above(V, xs, b), e, firsts.above(V, xs, b))))
    case False{}:
      w

# set_range keeps the model in order
def wf.set_range(-V: Data, +xs: Es(V), +a: U32, +b: U32, +v: V, +w: {wf(V, xs) == True{} : Bool}) -> {wf(V, msr(V, xs, a, b, v)) == True{} : Bool}:
  wsr.go(V, O.ule(a, b), xs, a, b, v, {==}, w)

def wcr.go(-V: Data, ok: Bool, +xs: Es(V), +a: U32, +b: U32, +e: {O.ule(a, b) == ok : Bool}, +w: {wf(V, xs) == True{} : Bool}) -> {wf(V, mcr.go(V, ok, xs, a, b)) == True{} : Bool}:
  match ok:
    case True{}:
      wf.app_intro(V, below(V, xs, a), above(V, xs, b), a, wf.below(V, xs, a, w), wf.above(V, xs, b, w), lasts.below(V, xs, a), ge.of_aft(V, a, b, above(V, xs, b), e, firsts.above(V, xs, b)))
    case False{}:
      w

# clear_range keeps the model in order
def wf.clear_range(-V: Data, +xs: Es(V), +a: U32, +b: U32, +w: {wf(V, xs) == True{} : Bool}) -> {wf(V, mcr(V, xs, a, b)) == True{} : Bool}:
  wcr.go(V, O.ule(a, b), xs, a, b, {==}, w)

# The last key

def some.inj(-A: Data, -a: A, -b: A, +e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => Maybe.default(&2, A, m, a), Some{a}, Some{b}, e)

def or_some.none(-A: Data, m: Maybe<&2, A>, -z: A, +e: {Maybe.or(&2, A, m, Some{z}) == None{} : Maybe<&2, A>}) -> Empty:
  match m:
    case Some{y}:
      O.ab.some_none(A, y, e)
    case None{}:
      O.ab.some_none(A, z, e)

def lkey.none_nil(-V: Data, xs: Es(V), +e: {lkey(V, xs) == None{} : Maybe<&2, U32>}) -> {xs == Nil{} : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      Empty.absurd({Con{x, r} == Nil{} : Es(V)}, or_some.none(U32, lkey(V, r), lst(V, x), e))

# the last key of x :: r, once the last key of r is known to be m
def lkey.step(-V: Data, -m: Maybe<&2, U32>, +x: Ent(V), -r: Es(V), -p: U32, +em: {lkey(V, r) == m : Maybe<&2, U32>}, +e: {lkey(V, Con{x, r}) == Some{p} : Maybe<&2, U32>}) -> {Maybe.or(&2, U32, m, Some{lst(V, x)}) == Some{p} : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, Maybe.or(&2, U32, m, Some{lst(V, x)}), Maybe.or(&2, U32, lkey(V, r), Some{lst(V, x)}), Some{p}, Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, n => Maybe.or(&2, U32, n, Some{lst(V, x)}), m, lkey(V, r), Equal.sym(Maybe<&2, U32>, lkey(V, r), m, em)), e)

# k before the start of a nonempty ordered list whose entries end by p: k < p
def aft.lt_key(-V: Data, +k: U32, r: Es(V), +p: U32, -q: U32, +h1: {aft(V, k, r) == True{} : Bool}, +h2: {lasts_le(V, r, p) == True{} : Bool}, +w: {wf(V, r) == True{} : Bool}, +em: {lkey(V, r) == Some{q} : Maybe<&2, U32>}) -> {O.ult(k, p) == True{} : Bool}:
  match r:
    case Nil{}:
      Empty.absurd({O.ult(k, p) == True{} : Bool}, O.ab.none_some(U32, q, em))
    case Con{+y, +r2}:
      O.u.lt_le(k, fst(V, y), p, aft.head(V, k, y, r2, h1), O.u.le_trans(fst(V, y), lst(V, y), p, wf.le(V, y, r2, w), O.bo.and_l(O.ule(lst(V, y), p), lasts_le(V, r2, p), h2)))

def lle.go(-V: Data, m: Maybe<&2, U32>, +x: Ent(V), +r: Es(V), +p: U32, +w: {wf(V, Con{x, r}) == True{} : Bool}, +em: {lkey(V, r) == m : Maybe<&2, U32>}, +e: {Maybe.or(&2, U32, m, Some{lst(V, x)}) == Some{p} : Maybe<&2, U32>}, ih: {lkey(V, r) == Some{p} : Maybe<&2, U32>} -> {lasts_le(V, r, p) == True{} : Bool}) -> {lasts_le(V, Con{x, r}, p) == True{} : Bool}:
  match m:
    case None{}:
      %Equal.sym(Es(V), r, Nil{}, lkey.none_nil(V, r, em)) : {lasts_le(V, Con{x, _}, p) == True{} : Bool}
      %some.inj(U32, lst(V, x), p, e) : {Bool.and(O.ule(lst(V, x), _), True{}) == True{} : Bool}
      O.bo.and_intro(O.ule(lst(V, x), lst(V, x)), True{}, O.u.le_refl(lst(V, x)), {==})
    case Some{+q}:
      +ep = Equal.trans(Maybe<&2, U32>, lkey(V, r), Some{q}, Some{p}, em, Equal.cong(U32, Maybe<&2, U32>, z => Some{z}, q, p, some.inj(U32, q, p, e)))
      +lr = ih(ep)
      O.bo.and_intro(O.ule(lst(V, x), p), lasts_le(V, r, p), O.u.le_of_lt(lst(V, x), p, aft.lt_key(V, lst(V, x), r, p, p, wf.aft(V, x, r, w), lr, wf.tail(V, x, r, w), ep)), lr)

# an ordered list whose last key is p: every entry ends by p
def lasts.of_key(-V: Data, xs: Es(V), +p: U32, +w: {wf(V, xs) == True{} : Bool}, +e: {lkey(V, xs) == Some{p} : Maybe<&2, U32>}) -> {lasts_le(V, xs, p) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({True{} == True{} : Bool}, O.ab.none_some(U32, p, e))
    case Con{+x, +r}:
      lle.go(V, lkey(V, r), x, r, p, w, {==}, lkey.step(V, lkey(V, r), x, r, p, {==}, e), em => lasts.of_key(V, r, p, wf.tail(V, x, r, w), em))

def aak.go(-V: Data, m: Maybe<&2, U32>, +x: Ent(V), +r: Es(V), +ys: Es(V), +p: U32, +w: {wf(V, Con{x, app(V, r, ys)}) == True{} : Bool}, +em: {lkey(V, r) == m : Maybe<&2, U32>}, +e: {Maybe.or(&2, U32, m, Some{lst(V, x)}) == Some{p} : Maybe<&2, U32>}, ih: {lkey(V, r) == Some{p} : Maybe<&2, U32>} -> {aft(V, p, ys) == True{} : Bool}) -> {aft(V, p, ys) == True{} : Bool}:
  match m:
    case None{}:
      %some.inj(U32, lst(V, x), p, e) : {aft(V, _, ys) == True{} : Bool}
      aft.app_r(V, lst(V, x), r, ys, wf.aft(V, x, app(V, r, ys), w))
    case Some{+q}:
      ih(Equal.trans(Maybe<&2, U32>, lkey(V, r), Some{q}, Some{p}, em, Equal.cong(U32, Maybe<&2, U32>, z => Some{z}, q, p, some.inj(U32, q, p, e))))

# in an ordered xs ++ ys, ys starts after the last key of xs
def aft.of_key(-V: Data, xs: Es(V), +ys: Es(V), +p: U32, +w: {wf(V, app(V, xs, ys)) == True{} : Bool}, +e: {lkey(V, xs) == Some{p} : Maybe<&2, U32>}) -> {aft(V, p, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      Empty.absurd({aft(V, p, ys) == True{} : Bool}, O.ab.none_some(U32, p, e))
    case Con{+x, +r}:
      aak.go(V, lkey(V, r), x, r, ys, p, w, {==}, lkey.step(V, lkey(V, r), x, r, p, {==}, e), em => aft.of_key(V, r, ys, p, wf.tail(V, x, app(V, r, ys), w), em))

def lasts.lt_of_le(-V: Data, xs: Es(V), +p: U32, +i: U32, +h: {lasts_le(V, xs, p) == True{} : Bool}, +g: {O.ult(p, i) == True{} : Bool}) -> {lasts_lt(V, xs, i) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      O.bo.and_intro(O.ult(lst(V, x), i), lasts_lt(V, r, i), O.u.le_lt(lst(V, x), p, i, O.bo.and_l(O.ule(lst(V, x), p), lasts_le(V, r, p), h), g), lasts.lt_of_le(V, r, p, i, O.bo.and_r(O.ule(lst(V, x), p), lasts_le(V, r, p), h), g))

# Find, next and prev on lists that end before or start after the index

def mfind.none_le(-V: Data, xs: Es(V), +p: U32, +i: U32, +h: {lasts_le(V, xs, p) == True{} : Bool}, +g: {O.ult(p, i) == True{} : Bool}) -> {mfind(V, xs, i) == None{} : Maybe<&2, Ent(V)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(Maybe<&2, Ent(V)>, pk(V, O.ule(i, lst(V, x)), x, mfind(V, r, i)), mfind(V, r, i), None{}, pk.false(V, O.ule(i, lst(V, x)), x, mfind(V, r, i), O.u.lt_not_le(lst(V, x), i, O.u.le_lt(lst(V, x), p, i, O.bo.and_l(O.ule(lst(V, x), p), lasts_le(V, r, p), h), g))), mfind.none_le(V, r, p, i, O.bo.and_r(O.ule(lst(V, x), p), lasts_le(V, r, p), h), g))

def mfind.head(-V: Data, ys: Es(V), +k: U32, +i: U32, +h: {aft(V, k, ys) == True{} : Bool}, +w: {wf(V, ys) == True{} : Bool}, +g: {O.ule(i, k) == True{} : Bool}) -> {mfind(V, ys, i) == List.head(&2, Ent(V), ys) : Maybe<&2, Ent(V)>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      pk.true(V, O.ule(i, lst(V, y)), y, mfind(V, r, i), O.u.le_of_lt(i, lst(V, y), O.u.lt_le(i, fst(V, y), lst(V, y), O.u.le_lt(i, k, fst(V, y), g, aft.head(V, k, y, r, h)), wf.le(V, y, r, w))))

def mnext.none_le(-V: Data, xs: Es(V), +p: U32, +i: U32, +h: {lasts_le(V, xs, p) == True{} : Bool}, +w: {wf(V, xs) == True{} : Bool}, +g: {O.ule(p, i) == True{} : Bool}) -> {mnext(V, xs, i) == None{} : Maybe<&2, Ent(V)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(Maybe<&2, Ent(V)>, pk(V, O.ult(i, fst(V, x)), x, mnext(V, r, i)), mnext(V, r, i), None{}, pk.false(V, O.ult(i, fst(V, x)), x, mnext(V, r, i), O.u.le_not_lt(fst(V, x), i, O.u.le_trans(fst(V, x), p, i, O.u.le_trans(fst(V, x), lst(V, x), p, wf.le(V, x, r, w), O.bo.and_l(O.ule(lst(V, x), p), lasts_le(V, r, p), h)), g))), mnext.none_le(V, r, p, i, O.bo.and_r(O.ule(lst(V, x), p), lasts_le(V, r, p), h), wf.tail(V, x, r, w), g))

def mnext.head(-V: Data, ys: Es(V), +k: U32, +i: U32, +h: {aft(V, k, ys) == True{} : Bool}, +g: {O.ule(i, k) == True{} : Bool}) -> {mnext(V, ys, i) == List.head(&2, Ent(V), ys) : Maybe<&2, Ent(V)>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      pk.true(V, O.ult(i, fst(V, y)), y, mnext(V, r, i), O.u.le_lt(i, k, fst(V, y), g, aft.head(V, k, y, r, h)))

# every entry ends before i: prev is the last entry
def mprev.all(-V: Data, xs: Es(V), +i: U32, +h: {lasts_lt(V, xs, i) == True{} : Bool}) -> {mprev(V, xs, i) == elast(V, xs) : Maybe<&2, Ent(V)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(Maybe<&2, Ent(V)>, later(V, mprev(V, r, i), pk(V, O.ult(lst(V, x), i), x, None{})), later(V, elast(V, r), pk(V, O.ult(lst(V, x), i), x, None{})), later(V, elast(V, r), Some{x}), later.cong_l(V, mprev(V, r, i), elast(V, r), pk(V, O.ult(lst(V, x), i), x, None{}), mprev.all(V, r, i, O.bo.and_r(O.ult(lst(V, x), i), lasts_lt(V, r, i), h))), later.cong_r(V, elast(V, r), pk(V, O.ult(lst(V, x), i), x, None{}), Some{x}, pk.true(V, O.ult(lst(V, x), i), x, None{}, O.bo.and_l(O.ult(lst(V, x), i), lasts_lt(V, r, i), h))))

def mprev.none_aft(-V: Data, ys: Es(V), +k: U32, +i: U32, +h: {aft(V, k, ys) == True{} : Bool}, +w: {wf(V, ys) == True{} : Bool}, +g: {O.ule(i, k) == True{} : Bool}) -> {mprev(V, ys, i) == None{} : Maybe<&2, Ent(V)>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      Equal.trans(Maybe<&2, Ent(V)>, later(V, mprev(V, r, i), pk(V, O.ult(lst(V, y), i), y, None{})), later(V, None{}, pk(V, O.ult(lst(V, y), i), y, None{})), None{}, later.cong_l(V, mprev(V, r, i), None{}, pk(V, O.ult(lst(V, y), i), y, None{}), mprev.none_aft(V, r, k, i, aft.tail(V, k, y, r, h), wf.tail(V, y, r, w), g)), pk.false(V, O.ult(lst(V, y), i), y, None{}, O.u.le_not_lt(i, lst(V, y), O.u.le_of_lt(i, lst(V, y), O.u.lt_le(i, fst(V, y), lst(V, y), O.u.le_lt(i, k, fst(V, y), g, aft.head(V, k, y, r, h)), wf.le(V, y, r, w))))))

def later.some_r(-V: Data, m: Maybe<&2, Ent(V)>, -x: Ent(V), -n: Maybe<&2, Ent(V)>) -> {later(V, later(V, m, Some{x}), n) == later(V, m, Some{x}) : Maybe<&2, Ent(V)>}:
  match m:
    case Some{y}:
      {==}
    case None{}:
      {==}

def elast.absorb(-V: Data, r: Es(V), -n: Maybe<&2, Ent(V)>, -q: U32, +em: {lkey(V, r) == Some{q} : Maybe<&2, U32>}) -> {later(V, elast(V, r), n) == elast(V, r) : Maybe<&2, Ent(V)>}:
  match r:
    case Nil{}:
      Empty.absurd({later(V, None{}, n) == None{} : Maybe<&2, Ent(V)>}, O.ab.none_some(U32, q, em))
    case Con{+y, +r2}:
      later.some_r(V, elast(V, r2), y, n)

def mfk.go(-V: Data, m: Maybe<&2, U32>, +x: Ent(V), +r: Es(V), +k: U32, +w: {wf(V, Con{x, r}) == True{} : Bool}, +em: {lkey(V, r) == m : Maybe<&2, U32>}, +e: {Maybe.or(&2, U32, m, Some{lst(V, x)}) == Some{k} : Maybe<&2, U32>}, ih: {lkey(V, r) == Some{k} : Maybe<&2, U32>} -> {mfind(V, r, k) == elast(V, r) : Maybe<&2, Ent(V)>}) -> {mfind(V, Con{x, r}, k) == elast(V, Con{x, r}) : Maybe<&2, Ent(V)>}:
  match m:
    case None{}:
      %Equal.sym(Es(V), r, Nil{}, lkey.none_nil(V, r, em)) : {mfind(V, Con{x, _}, k) == elast(V, Con{x, _}) : Maybe<&2, Ent(V)>}
      %some.inj(U32, lst(V, x), k, e) : {pk(V, O.ule(_, lst(V, x)), x, None{}) == Some{x} : Maybe<&2, Ent(V)>}
      pk.true(V, O.ule(lst(V, x), lst(V, x)), x, None{}, O.u.le_refl(lst(V, x)))
    case Some{+q}:
      +ek = Equal.trans(Maybe<&2, U32>, lkey(V, r), Some{q}, Some{k}, em, Equal.cong(U32, Maybe<&2, U32>, z => Some{z}, q, k, some.inj(U32, q, k, e)))
      +lr = lasts.of_key(V, r, k, wf.tail(V, x, r, w), ek)
      +f = Equal.trans(Maybe<&2, Ent(V)>, pk(V, O.ule(k, lst(V, x)), x, mfind(V, r, k)), mfind(V, r, k), elast(V, r), pk.false(V, O.ule(k, lst(V, x)), x, mfind(V, r, k), O.u.lt_not_le(lst(V, x), k, aft.lt_key(V, lst(V, x), r, k, k, wf.aft(V, x, r, w), lr, wf.tail(V, x, r, w), ek))), ih(ek))
      Equal.trans(Maybe<&2, Ent(V)>, mfind(V, Con{x, r}, k), elast(V, r), later(V, elast(V, r), Some{x}), f, Equal.sym(Maybe<&2, Ent(V)>, later(V, elast(V, r), Some{x}), elast(V, r), elast.absorb(V, r, Some{x}, k, ek)))

# in an ordered list, the first entry ending at or after the last key is the last entry
def mfind.last(-V: Data, xs: Es(V), +k: U32, +w: {wf(V, xs) == True{} : Bool}, +e: {lkey(V, xs) == Some{k} : Maybe<&2, U32>}) -> {mfind(V, xs, k) == elast(V, xs) : Maybe<&2, Ent(V)>}:
  match xs:
    case Nil{}:
      Empty.absurd({None{} == None{} : Maybe<&2, Ent(V)>}, O.ab.none_some(U32, k, e))
    case Con{+x, +r}:
      mfk.go(V, lkey(V, r), x, r, k, w, {==}, lkey.step(V, lkey(V, r), x, r, k, {==}, e), em => mfind.last(V, r, k, wf.tail(V, x, r, w), em))

# Iteration on the model

def it.find_first(-V: Data, +x: Ent(V), +ys: Es(V)) -> {mfind(V, Con{x, ys}, 0) == Some{x} : Maybe<&2, Ent(V)>}:
  pk.true(V, O.ule(0, lst(V, x)), x, mfind(V, ys, 0), O.u.zero_le(lst(V, x)))

# z before x in an ordered list: next(last of x) does not pick z
def it.before(-V: Data, +z: Ent(V), +x: Ent(V), +rs: Es(V), +ts: Es(V), +w: {wf(V, Con{z, app(V, rs, Con{x, ts})}) == True{} : Bool}, +wx: {wf(V, Con{x, ts}) == True{} : Bool}) -> {O.ult(lst(V, x), fst(V, z)) == False{} : Bool}:
  O.u.le_not_lt(fst(V, z), lst(V, x), O.u.le_of_lt(fst(V, z), lst(V, x), O.u.le_lt(fst(V, z), lst(V, z), lst(V, x), wf.le(V, z, app(V, rs, Con{x, ts}), w), O.u.lt_le(lst(V, z), fst(V, x), lst(V, x), aft.head(V, lst(V, z), x, ts, aft.app_r(V, lst(V, z), rs, Con{x, ts}, wf.aft(V, z, app(V, rs, Con{x, ts}), w))), wf.le(V, x, ts, wx)))))

def it.next_after(-V: Data, xs: Es(V), +x: Ent(V), +y: Ent(V), +ys: Es(V), +w: {wf(V, app(V, xs, Con{x, Con{y, ys}})) == True{} : Bool}) -> {mnext(V, app(V, xs, Con{x, Con{y, ys}}), lst(V, x)) == Some{y} : Maybe<&2, Ent(V)>}:
  match xs:
    case Nil{}:
      Equal.trans(Maybe<&2, Ent(V)>, pk(V, O.ult(lst(V, x), fst(V, x)), x, mnext(V, Con{y, ys}, lst(V, x))), mnext(V, Con{y, ys}, lst(V, x)), Some{y}, pk.false(V, O.ult(lst(V, x), fst(V, x)), x, mnext(V, Con{y, ys}, lst(V, x)), O.u.le_not_lt(fst(V, x), lst(V, x), wf.le(V, x, Con{y, ys}, w))), pk.true(V, O.ult(lst(V, x), fst(V, y)), y, mnext(V, ys, lst(V, x)), aft.head(V, lst(V, x), y, ys, wf.aft(V, x, Con{y, ys}, w))))
    case Con{+z, +rs}:
      Equal.trans(Maybe<&2, Ent(V)>, pk(V, O.ult(lst(V, x), fst(V, z)), z, mnext(V, app(V, rs, Con{x, Con{y, ys}}), lst(V, x))), mnext(V, app(V, rs, Con{x, Con{y, ys}}), lst(V, x)), Some{y}, pk.false(V, O.ult(lst(V, x), fst(V, z)), z, mnext(V, app(V, rs, Con{x, Con{y, ys}}), lst(V, x)), it.before(V, z, x, rs, Con{y, ys}, w, wf.app_r(V, rs, Con{x, Con{y, ys}}, wf.tail(V, z, app(V, rs, Con{x, Con{y, ys}}), w)))), it.next_after(V, rs, x, y, ys, wf.tail(V, z, app(V, rs, Con{x, Con{y, ys}}), w)))

def it.next_none(-V: Data, xs: Es(V), +x: Ent(V), +w: {wf(V, app(V, xs, Con{x, Nil{}})) == True{} : Bool}) -> {mnext(V, app(V, xs, Con{x, Nil{}}), lst(V, x)) == None{} : Maybe<&2, Ent(V)>}:
  match xs:
    case Nil{}:
      pk.false(V, O.ult(lst(V, x), fst(V, x)), x, None{}, O.u.le_not_lt(fst(V, x), lst(V, x), wf.le(V, x, Nil{}, w)))
    case Con{+z, +rs}:
      Equal.trans(Maybe<&2, Ent(V)>, pk(V, O.ult(lst(V, x), fst(V, z)), z, mnext(V, app(V, rs, Con{x, Nil{}}), lst(V, x))), mnext(V, app(V, rs, Con{x, Nil{}}), lst(V, x)), None{}, pk.false(V, O.ult(lst(V, x), fst(V, z)), z, mnext(V, app(V, rs, Con{x, Nil{}}), lst(V, x)), it.before(V, z, x, rs, Nil{}, w, wf.app_r(V, rs, Con{x, Nil{}}, wf.tail(V, z, app(V, rs, Con{x, Nil{}}), w)))), it.next_none(V, rs, x, wf.tail(V, z, app(V, rs, Con{x, Nil{}}), w)))

def it.prev_pair(-V: Data, +x: Ent(V), +y: Ent(V), +ys: Es(V), +w: {wf(V, Con{x, Con{y, ys}}) == True{} : Bool}) -> {mprev(V, Con{x, Con{y, ys}}, fst(V, y)) == Some{x} : Maybe<&2, Ent(V)>}:
  +wy = wf.tail(V, x, Con{y, ys}, w)
  +py = Equal.trans(Maybe<&2, Ent(V)>, mprev(V, Con{y, ys}, fst(V, y)), later(V, None{}, pk(V, O.ult(lst(V, y), fst(V, y)), y, None{})), None{}, later.cong_l(V, mprev(V, ys, fst(V, y)), None{}, pk(V, O.ult(lst(V, y), fst(V, y)), y, None{}), mprev.none_aft(V, ys, lst(V, y), fst(V, y), wf.aft(V, y, ys, wy), wf.tail(V, y, ys, wy), wf.le(V, y, ys, wy))), pk.false(V, O.ult(lst(V, y), fst(V, y)), y, None{}, O.u.le_not_lt(fst(V, y), lst(V, y), wf.le(V, y, ys, wy))))
  Equal.trans(Maybe<&2, Ent(V)>, mprev(V, Con{x, Con{y, ys}}, fst(V, y)), later(V, None{}, pk(V, O.ult(lst(V, x), fst(V, y)), x, None{})), Some{x}, later.cong_l(V, mprev(V, Con{y, ys}, fst(V, y)), None{}, pk(V, O.ult(lst(V, x), fst(V, y)), x, None{}), py), pk.true(V, O.ult(lst(V, x), fst(V, y)), x, None{}, aft.head(V, lst(V, x), y, ys, wf.aft(V, x, Con{y, ys}, w))))

def it.prev_before(-V: Data, +xs: Es(V), +x: Ent(V), +y: Ent(V), +ys: Es(V), +w: {wf(V, app(V, xs, Con{x, Con{y, ys}})) == True{} : Bool}) -> {mprev(V, app(V, xs, Con{x, Con{y, ys}}), fst(V, y)) == Some{x} : Maybe<&2, Ent(V)>}:
  Equal.trans(Maybe<&2, Ent(V)>, mprev(V, app(V, xs, Con{x, Con{y, ys}}), fst(V, y)), later(V, Some{x}, mprev(V, xs, fst(V, y))), Some{x}, Equal.trans(Maybe<&2, Ent(V)>, mprev(V, app(V, xs, Con{x, Con{y, ys}}), fst(V, y)), later(V, mprev(V, Con{x, Con{y, ys}}, fst(V, y)), mprev(V, xs, fst(V, y))), later(V, Some{x}, mprev(V, xs, fst(V, y))), mprev.app(V, xs, Con{x, Con{y, ys}}, fst(V, y)), later.cong_l(V, mprev(V, Con{x, Con{y, ys}}, fst(V, y)), Some{x}, mprev(V, xs, fst(V, y)), it.prev_pair(V, x, y, ys, wf.app_r(V, xs, Con{x, Con{y, ys}}, w)))), {==})

# Gap scans: a found or failed search stays so; entries before the cursor
# change nothing

def gscan.found(-V: Data, xs: Es(V), +s: U32, +d: U32, +max: U32) -> {gscan(V, xs, M.MapleGapFound{s}, d, max) == M.MapleGapFound{s} : M.MapleGap<U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      gscan.found(V, r, s, d, max)

def gscan.busy(-V: Data, xs: Es(V), +d: U32, +max: U32) -> {gscan(V, xs, M.MapleGapBusy{}, d, max) == M.MapleGapBusy{} : M.MapleGap<U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      gscan.busy(V, r, d, max)

def gentry(-V: Data, before: Bool, +x: Ent(V), +cur: U32, +d: U32, +max: U32) -> M.MapleGap<U32>:
  M.MapleModel.gap_entry(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.add, V, before, x, cur, d, max)

def gentry.before(-V: Data, b: Bool, -x: Ent(V), -cur: U32, -d: U32, -max: U32, +e: {b == True{} : Bool}) -> {gentry(V, b, x, cur, d, max) == M.MapleGapScan{cur} : M.MapleGap<U32>}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({gentry(V, False{}, x, cur, d, max) == M.MapleGapScan{cur} : M.MapleGap<U32>}, O.ab.ft(e))

def gscan.skip(-V: Data, xs: Es(V), +cur: U32, +d: U32, +max: U32, +h: {lasts_lt(V, xs, cur) == True{} : Bool}) -> {gscan(V, xs, M.MapleGapScan{cur}, d, max) == M.MapleGapScan{cur} : M.MapleGap<U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(M.MapleGap<U32>, gscan(V, r, gentry(V, O.ult(lst(V, x), cur), x, cur, d, max), d, max), gscan(V, r, M.MapleGapScan{cur}, d, max), M.MapleGapScan{cur}, Equal.cong(M.MapleGap<U32>, M.MapleGap<U32>, st => gscan(V, r, st, d, max), gentry(V, O.ult(lst(V, x), cur), x, cur, d, max), M.MapleGapScan{cur}, gentry.before(V, O.ult(lst(V, x), cur), x, cur, d, max, O.bo.and_l(O.ult(lst(V, x), cur), lasts_lt(V, r, cur), h))), gscan.skip(V, r, cur, d, max, O.bo.and_r(O.ult(lst(V, x), cur), lasts_lt(V, r, cur), h)))

# The gap search on the model. With d = size - 1, the run from s ends at
# s + d. GR is the search's answer from the cursor cur.

def gend(st: M.MapleGap<U32>, +d: U32, +max: U32) -> Result<&2, &2, M.MapleError<U32>, U32>:
  M.MapleModel.gap_end(~U32, ~U32.cmp, ~M.MapleKey32.add, st, d, max)

def GR(-V: Data, xs: Es(V), +cur: U32, +d: U32, +max: U32) -> Result<&2, &2, M.MapleError<U32>, U32>:
  gend(gscan(V, xs, M.MapleGapScan{cur}, d, max), d, max)

def gendgo(c: Bool, cur: U32) -> Result<&2, &2, M.MapleError<U32>, U32>:
  M.MapleModel.gap_end.go(U32, c, cur)

# the run from cur fits below max (and does not wrap)
def gfit(+cur: U32, +d: U32, +max: U32) -> Bool:
  Bool.and(O.ule(cur, U32.add(cur, d)), O.ule(U32.add(cur, d), max))

# ... and ends before fx
def gfit2(+cur: U32, +d: U32, +max: U32, +fx: U32) -> Bool:
  Bool.and(O.ule(cur, U32.add(cur, d)), Bool.and(O.ult(U32.add(cur, d), fx), O.ule(U32.add(cur, d), max)))

def gtry(c: Bool, +cur: U32, +lx: U32, +max: U32) -> M.MapleGap<U32>:
  M.MapleModel.gap_try(~U32, ~U32.cmp, ~M.MapleKey32.inc, c, cur, lx, max)

def gmove(c: Bool, +lx: U32) -> M.MapleGap<U32>:
  M.MapleModel.gap_move(~U32, ~M.MapleKey32.inc, c, lx)

# the run from s holds nothing
def Free(-V: Data, +xs: Es(V), +s: U32, +d: U32) -> Type:
  @i:U32 -> {O.ule(s, i) == True{} : Bool} -> {O.ule(i, U32.add(s, d)) == True{} : Bool} -> {mload(V, xs, i) == None{} : Maybe<&2, V>}

# the run from s starts at or after cur, does not wrap, and ends by max
def HB(+cur: U32, +s: U32, +d: U32, +max: U32) -> Data:
  {Bool.and(O.ule(cur, s), Bool.and(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max))) == True{} : Bool}

# an answer s has HB(cur, s, d, max)
def GB(+cur: U32, +d: U32, +max: U32, r: Result<&2, &2, M.MapleError<U32>, U32>) -> Data:
  match r:
    case Done{+s}:
      HB(cur, s, d, max)
    case Fail{e}:
      Unit

# an answer s has a free run
def GF(-V: Data, +xs: Es(V), +d: U32, r: Result<&2, &2, M.MapleError<U32>, U32>) -> Type:
  match r:
    case Done{+s}:
      Free(V, xs, s, d)
    case Fail{e}:
      Unit

# there is an answer, at or below t
def GA(+t: U32, r: Result<&2, &2, M.MapleError<U32>, U32>) -> Data:
  match r:
    case Done{s}:
      {O.ule(s, t) == True{} : Bool}
    case Fail{e}:
      Empty

# The bounds of an answer

def gb.end(c: Bool, +cur: U32, +d: U32, +max: U32, +e: {gfit(cur, d, max) == c : Bool}) -> GB(cur, d, max, gendgo(c, cur)):
  match c:
    case True{}:
      O.bo.and_intro(O.ule(cur, cur), gfit(cur, d, max), O.u.le_refl(cur), e)
    case False{}:
      Unit{}

def gb.weak(r: Result<&2, &2, M.MapleError<U32>, U32>, +c1: U32, +c2: U32, +d: U32, +max: U32, +h: {O.ule(c1, c2) == True{} : Bool}, +g: GB(c2, d, max, r)) -> GB(c1, d, max, r):
  match r:
    case Done{+s}:
      O.bo.and_intro(O.ule(c1, s), Bool.and(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max)), O.u.le_trans(c1, c2, s, h, O.bo.and_l(O.ule(c2, s), Bool.and(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max)), g)), O.bo.and_r(O.ule(c2, s), Bool.and(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max)), g))
    case Fail{e}:
      Unit{}

def gb.found(+cur: U32, +d: U32, +max: U32, +fx: U32, +e: {gfit2(cur, d, max, fx) == True{} : Bool}) -> HB(cur, cur, d, max):
  O.bo.and_intro(O.ule(cur, cur), gfit(cur, d, max), O.u.le_refl(cur), O.bo.and_intro(O.ule(cur, U32.add(cur, d)), O.ule(U32.add(cur, d), max), O.bo.and_l(O.ule(cur, U32.add(cur, d)), Bool.and(O.ult(U32.add(cur, d), fx), O.ule(U32.add(cur, d), max)), e), O.bo.and_r(O.ult(U32.add(cur, d), fx), O.ule(U32.add(cur, d), max), O.bo.and_r(O.ule(cur, U32.add(cur, d)), Bool.and(O.ult(U32.add(cur, d), fx), O.ule(U32.add(cur, d), max)), e))))

def gb.move(c3: Bool, -V: Data, +r: Es(V), +cur: U32, +lx: U32, +d: U32, +max: U32, +e3: {O.ult(lx, max) == c3 : Bool}, +hc: {O.ule(cur, lx) == True{} : Bool}, +ih: GB(U32.inc(lx), d, max, GR(V, r, U32.inc(lx), d, max))) -> GB(cur, d, max, gend(gscan(V, r, gmove(c3, lx), d, max), d, max)):
  match c3:
    case True{}:
      gb.weak(GR(V, r, U32.inc(lx), d, max), cur, U32.inc(lx), d, max, O.u.le_of_lt(cur, U32.inc(lx), O.u.le_lt(cur, lx, U32.inc(lx), hc, O.u.inc_gt(lx, max, e3))), ih)
    case False{}:
      %Equal.sym(M.MapleGap<U32>, gscan(V, r, M.MapleGapBusy{}, d, max), M.MapleGapBusy{}, gscan.busy(V, r, d, max)) : GB(cur, d, max, gend(_, d, max))
      Unit{}

def gb.try(c2: Bool, -V: Data, +r: Es(V), +cur: U32, +lx: U32, +fx: U32, +d: U32, +max: U32, +e2: {gfit2(cur, d, max, fx) == c2 : Bool}, +hc: {O.ule(cur, lx) == True{} : Bool}, +ih: GB(U32.inc(lx), d, max, GR(V, r, U32.inc(lx), d, max))) -> GB(cur, d, max, gend(gscan(V, r, gtry(c2, cur, lx, max), d, max), d, max)):
  match c2:
    case True{}:
      %Equal.sym(M.MapleGap<U32>, gscan(V, r, M.MapleGapFound{cur}, d, max), M.MapleGapFound{cur}, gscan.found(V, r, cur, d, max)) : GB(cur, d, max, gend(_, d, max))
      gb.found(cur, d, max, fx, e2)
    case False{}:
      gb.move(O.ult(lx, max), V, r, cur, lx, d, max, {==}, hc, ih)

def gb.step(before: Bool, -V: Data, +x: Ent(V), +r: Es(V), +cur: U32, +d: U32, +max: U32, +e0: {O.ult(lst(V, x), cur) == before : Bool}, +ihc: GB(cur, d, max, GR(V, r, cur, d, max)), +ihn: GB(U32.inc(lst(V, x)), d, max, GR(V, r, U32.inc(lst(V, x)), d, max))) -> GB(cur, d, max, gend(gscan(V, r, gentry(V, before, x, cur, d, max), d, max), d, max)):
  match before:
    case True{}:
      ihc
    case False{}:
      gb.try(gfit2(cur, d, max, fst(V, x)), V, r, cur, lst(V, x), fst(V, x), d, max, {==}, O.u.not_lt(lst(V, x), cur, e0), ihn)

# every answer lies within the bounds
def gbound(-V: Data, xs: Es(V), +cur: U32, +d: U32, +max: U32) -> GB(cur, d, max, GR(V, xs, cur, d, max)):
  match xs:
    case Nil{}:
      gb.end(gfit(cur, d, max), cur, d, max, {==})
    case Con{+x, +r}:
      gb.step(O.ult(lst(V, x), cur), V, x, r, cur, d, max, {==}, gbound(V, r, cur, d, max), gbound(V, r, U32.inc(lst(V, x)), d, max))

# The run of an answer is free

def gf.end(c: Bool, -V: Data, +cur: U32, +d: U32) -> GF(V, Nil{}, d, gendgo(c, cur)):
  match c:
    case True{}:
      +i => +h1 => +h2 => {==}
    case False{}:
      Unit{}

def gf.ext(-V: Data, r: Result<&2, &2, M.MapleError<U32>, U32>, +x: Ent(V), +xs: Es(V), +d: U32, +max: U32, +c: U32, +lt: {O.ult(lst(V, x), c) == True{} : Bool}, +gb: GB(c, d, max, r), gf: GF(V, xs, d, r)) -> GF(V, Con{x, xs}, d, r):
  match r:
    case Done{+s}:
      +i => +h1 => +h2 => Equal.trans(Maybe<&2, V>, pv(V, holds(V, x, i), val(V, x), mload(V, xs, i)), mload(V, xs, i), None{}, pv.false(V, holds(V, x, i), val(V, x), mload(V, xs, i), O.bo.and_false_r(O.ule(fst(V, x), i), O.ule(i, lst(V, x)), O.u.lt_not_le(lst(V, x), i, O.u.lt_le(lst(V, x), c, i, lt, O.u.le_trans(c, s, i, O.bo.and_l(O.ule(c, s), Bool.and(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max)), gb), h1))))), gf(i)(h1)(h2))
    case Fail{e}:
      Unit{}

def gf.found.at(-V: Data, +x: Ent(V), +r: Es(V), +cur: U32, +d: U32, +max: U32, +i: U32, +w: {wf(V, Con{x, r}) == True{} : Bool}, +e2: {gfit2(cur, d, max, fst(V, x)) == True{} : Bool}, +h2: {O.ule(i, U32.add(cur, d)) == True{} : Bool}) -> {mload(V, Con{x, r}, i) == None{} : Maybe<&2, V>}:
  +ltf = O.u.le_lt(i, U32.add(cur, d), fst(V, x), h2, O.bo.and_l(O.ult(U32.add(cur, d), fst(V, x)), O.ule(U32.add(cur, d), max), O.bo.and_r(O.ule(cur, U32.add(cur, d)), Bool.and(O.ult(U32.add(cur, d), fst(V, x)), O.ule(U32.add(cur, d), max)), e2)))
  Equal.trans(Maybe<&2, V>, pv(V, holds(V, x, i), val(V, x), mload(V, r, i)), mload(V, r, i), None{}, pv.false(V, holds(V, x, i), val(V, x), mload(V, r, i), O.bo.and_false_l(O.ule(fst(V, x), i), O.ule(i, lst(V, x)), O.u.lt_not_le(i, fst(V, x), ltf))), mload.none_aft(V, r, lst(V, x), i, wf.aft(V, x, r, w), O.u.le_of_lt(i, lst(V, x), O.u.lt_le(i, fst(V, x), lst(V, x), ltf, wf.le(V, x, r, w)))))

def gf.found(-V: Data, +x: Ent(V), +r: Es(V), +cur: U32, +d: U32, +max: U32, +w: {wf(V, Con{x, r}) == True{} : Bool}, +e2: {gfit2(cur, d, max, fst(V, x)) == True{} : Bool}) -> Free(V, Con{x, r}, cur, d):
  +i => +h1 => +h2 => gf.found.at(V, x, r, cur, d, max, i, w, e2, h2)

def gf.move(c3: Bool, -V: Data, +x: Ent(V), +r: Es(V), +d: U32, +max: U32, +e3: {O.ult(lst(V, x), max) == c3 : Bool}, +gbn: GB(U32.inc(lst(V, x)), d, max, GR(V, r, U32.inc(lst(V, x)), d, max)), gfn: GF(V, r, d, GR(V, r, U32.inc(lst(V, x)), d, max))) -> GF(V, Con{x, r}, d, gend(gscan(V, r, gmove(c3, lst(V, x)), d, max), d, max)):
  match c3:
    case True{}:
      gf.ext(V, GR(V, r, U32.inc(lst(V, x)), d, max), x, r, d, max, U32.inc(lst(V, x)), O.u.inc_gt(lst(V, x), max, e3), gbn, gfn)
    case False{}:
      %Equal.sym(M.MapleGap<U32>, gscan(V, r, M.MapleGapBusy{}, d, max), M.MapleGapBusy{}, gscan.busy(V, r, d, max)) : GF(V, Con{x, r}, d, gend(_, d, max))
      Unit{}

def gf.try(c2: Bool, -V: Data, +x: Ent(V), +r: Es(V), +cur: U32, +d: U32, +max: U32, +w: {wf(V, Con{x, r}) == True{} : Bool}, +e2: {gfit2(cur, d, max, fst(V, x)) == c2 : Bool}, +gbn: GB(U32.inc(lst(V, x)), d, max, GR(V, r, U32.inc(lst(V, x)), d, max)), gfn: GF(V, r, d, GR(V, r, U32.inc(lst(V, x)), d, max))) -> GF(V, Con{x, r}, d, gend(gscan(V, r, gtry(c2, cur, lst(V, x), max), d, max), d, max)):
  match c2:
    case True{}:
      %Equal.sym(M.MapleGap<U32>, gscan(V, r, M.MapleGapFound{cur}, d, max), M.MapleGapFound{cur}, gscan.found(V, r, cur, d, max)) : GF(V, Con{x, r}, d, gend(_, d, max))
      gf.found(V, x, r, cur, d, max, w, e2)
    case False{}:
      gf.move(O.ult(lst(V, x), max), V, x, r, d, max, {==}, gbn, gfn)

def gf.step(before: Bool, -V: Data, +x: Ent(V), +r: Es(V), +cur: U32, +d: U32, +max: U32, +w: {wf(V, Con{x, r}) == True{} : Bool}, +e0: {O.ult(lst(V, x), cur) == before : Bool}, +gbc: GB(cur, d, max, GR(V, r, cur, d, max)), gfc: GF(V, r, d, GR(V, r, cur, d, max)), +gbn: GB(U32.inc(lst(V, x)), d, max, GR(V, r, U32.inc(lst(V, x)), d, max)), gfn: GF(V, r, d, GR(V, r, U32.inc(lst(V, x)), d, max))) -> GF(V, Con{x, r}, d, gend(gscan(V, r, gentry(V, before, x, cur, d, max), d, max), d, max)):
  match before:
    case True{}:
      gf.ext(V, GR(V, r, cur, d, max), x, r, d, max, cur, e0, gbc, gfc)
    case False{}:
      gf.try(gfit2(cur, d, max, fst(V, x)), V, x, r, cur, d, max, w, {==}, gbn, gfn)

# in an ordered list, the run of every answer is free
def gfree(-V: Data, xs: Es(V), +cur: U32, +d: U32, +max: U32, +w: {wf(V, xs) == True{} : Bool}) -> GF(V, xs, d, GR(V, xs, cur, d, max)):
  match xs:
    case Nil{}:
      gf.end(gfit(cur, d, max), V, cur, d)
    case Con{+x, +r}:
      +wt = wf.tail(V, x, r, w)
      gf.step(O.ult(lst(V, x), cur), V, x, r, cur, d, max, w, {==}, gbound(V, r, cur, d, max), gfree(V, r, cur, d, max, wt), gbound(V, r, U32.inc(lst(V, x)), d, max), gfree(V, r, U32.inc(lst(V, x)), d, max, wt))

# A free run is found: the answer is at or below its start

def gc.fits(+cur: U32, +s: U32, +d: U32, +max: U32, +hb: HB(cur, s, d, max)) -> {gfit(cur, d, max) == True{} : Bool}:
  +am = O.u.am(cur, s, d, O.bo.and_l(O.ule(cur, s), Bool.and(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max)), hb), O.bo.and_l(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max), O.bo.and_r(O.ule(cur, s), Bool.and(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max)), hb)))
  O.bo.and_intro(O.ule(cur, U32.add(cur, d)), O.ule(U32.add(cur, d), max), O.bo.and_l(O.ule(cur, U32.add(cur, d)), O.ule(U32.add(cur, d), U32.add(s, d)), am), O.u.le_trans(U32.add(cur, d), U32.add(s, d), max, O.bo.and_r(O.ule(cur, U32.add(cur, d)), O.ule(U32.add(cur, d), U32.add(s, d)), am), O.bo.and_r(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max), O.bo.and_r(O.ule(cur, s), Bool.and(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max)), hb))))

def gc.fits2(+cur: U32, +s: U32, +d: U32, +max: U32, +fx: U32, +hb: HB(cur, s, d, max), +e: {O.ult(U32.add(s, d), fx) == True{} : Bool}) -> {gfit2(cur, d, max, fx) == True{} : Bool}:
  +am = O.u.am(cur, s, d, O.bo.and_l(O.ule(cur, s), Bool.and(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max)), hb), O.bo.and_l(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max), O.bo.and_r(O.ule(cur, s), Bool.and(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max)), hb)))
  +fit = gc.fits(cur, s, d, max, hb)
  O.bo.and_intro(O.ule(cur, U32.add(cur, d)), Bool.and(O.ult(U32.add(cur, d), fx), O.ule(U32.add(cur, d), max)), O.bo.and_l(O.ule(cur, U32.add(cur, d)), O.ule(U32.add(cur, d), max), fit), O.bo.and_intro(O.ult(U32.add(cur, d), fx), O.ule(U32.add(cur, d), max), O.u.le_lt(U32.add(cur, d), U32.add(s, d), fx, O.bo.and_r(O.ule(cur, U32.add(cur, d)), O.ule(U32.add(cur, d), U32.add(s, d)), am), e), O.bo.and_r(O.ule(cur, U32.add(cur, d)), O.ule(U32.add(cur, d), max), fit)))

def gc.end(c: Bool, +cur: U32, +s: U32, +d: U32, +max: U32, +e: {gfit(cur, d, max) == c : Bool}, +hb: HB(cur, s, d, max)) -> GA(s, gendgo(c, cur)):
  match c:
    case True{}:
      O.bo.and_l(O.ule(cur, s), Bool.and(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max)), hb)
    case False{}:
      O.bo.not_true(gfit(cur, d, max), gc.fits(cur, s, d, max, hb), e)

def pv.none_rest(-V: Data, b: Bool, -x: V, -m: Maybe<&2, V>, +e: {pv(V, b, x, m) == None{} : Maybe<&2, V>}) -> {m == None{} : Maybe<&2, V>}:
  match b:
    case True{}:
      Empty.absurd({m == None{} : Maybe<&2, V>}, O.ab.some_none(V, x, e))
    case False{}:
      e

def free.tail(-V: Data, +x: Ent(V), +r: Es(V), +s: U32, +d: U32, hf: Free(V, Con{x, r}, s, d)) -> Free(V, r, s, d):
  +i => +h1 => +h2 => pv.none_rest(V, holds(V, x, i), val(V, x), mload(V, r, i), hf(i)(h1)(h2))

# an index x holds is not free
def held(-V: Data, +x: Ent(V), +r: Es(V), +i: U32, +h: {holds(V, x, i) == True{} : Bool}, +f: {mload(V, Con{x, r}, i) == None{} : Maybe<&2, V>}) -> Empty:
  O.ab.some_none(V, val(V, x), Equal.trans(Maybe<&2, V>, Some{val(V, x)}, pv(V, holds(V, x, i), val(V, x), mload(V, r, i)), None{}, Equal.sym(Maybe<&2, V>, pv(V, holds(V, x, i), val(V, x), mload(V, r, i)), Some{val(V, x)}, pv.true(V, holds(V, x, i), val(V, x), mload(V, r, i), h)), f))

def gc.c6(c6: Bool, -V: Data, +x: Ent(V), +r: Es(V), +cur: U32, +s: U32, +d: U32, +max: U32, +w: {wf(V, Con{x, r}) == True{} : Bool}, +e6: {O.ult(U32.add(s, d), fst(V, x)) == c6 : Bool}, +e5: {O.ult(s, fst(V, x)) == True{} : Bool}, +e2: {gfit2(cur, d, max, fst(V, x)) == False{} : Bool}, +hb: HB(cur, s, d, max), hf: Free(V, Con{x, r}, s, d)) -> Empty:
  match c6:
    case True{}:
      O.bo.not_true(gfit2(cur, d, max, fst(V, x)), gc.fits2(cur, s, d, max, fst(V, x), hb, e6), e2)
    case False{}:
      held(V, x, r, fst(V, x), O.bo.and_intro(O.ule(fst(V, x), fst(V, x)), O.ule(fst(V, x), lst(V, x)), O.u.le_refl(fst(V, x)), wf.le(V, x, r, w)), hf(fst(V, x))(O.u.le_of_lt(s, fst(V, x), e5))(O.u.not_lt(U32.add(s, d), fst(V, x), e6)))

def gc.c5(c5: Bool, -V: Data, +x: Ent(V), +r: Es(V), +cur: U32, +s: U32, +d: U32, +max: U32, +w: {wf(V, Con{x, r}) == True{} : Bool}, +e5: {O.ult(s, fst(V, x)) == c5 : Bool}, +e4: {O.ult(lst(V, x), s) == False{} : Bool}, +e2: {gfit2(cur, d, max, fst(V, x)) == False{} : Bool}, +hb: HB(cur, s, d, max), hf: Free(V, Con{x, r}, s, d)) -> Empty:
  match c5:
    case True{}:
      gc.c6(O.ult(U32.add(s, d), fst(V, x)), V, x, r, cur, s, d, max, w, {==}, e5, e2, hb, hf)
    case False{}:
      held(V, x, r, s, O.bo.and_intro(O.ule(fst(V, x), s), O.ule(s, lst(V, x)), O.u.not_lt(s, fst(V, x), e5), O.u.not_lt(lst(V, x), s, e4)), hf(s)(O.u.le_refl(s))(O.bo.and_l(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max), O.bo.and_r(O.ule(cur, s), Bool.and(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max)), hb))))

def gc.move(c3: Bool, -V: Data, +x: Ent(V), +r: Es(V), +s: U32, +d: U32, +max: U32, +e3: {O.ult(lst(V, x), max) == c3 : Bool}, +t: {O.ult(lst(V, x), max) == True{} : Bool}, +hb: HB(U32.inc(lst(V, x)), s, d, max), hf: Free(V, Con{x, r}, s, d), ihn: HB(U32.inc(lst(V, x)), s, d, max) -> Free(V, r, s, d) -> GA(s, GR(V, r, U32.inc(lst(V, x)), d, max))) -> GA(s, gend(gscan(V, r, gmove(c3, lst(V, x)), d, max), d, max)):
  match c3:
    case True{}:
      ihn(hb)(free.tail(V, x, r, s, d, hf))
    case False{}:
      Empty.absurd(GA(s, gend(gscan(V, r, M.MapleGapBusy{}, d, max), d, max)), O.ab.tf(Equal.trans(Bool, True{}, O.ult(lst(V, x), max), False{}, Equal.sym(Bool, O.ult(lst(V, x), max), True{}, t), e3)))

def gc.dec(c4: Bool, -V: Data, +x: Ent(V), +r: Es(V), +cur: U32, +s: U32, +d: U32, +max: U32, +w: {wf(V, Con{x, r}) == True{} : Bool}, +e4: {O.ult(lst(V, x), s) == c4 : Bool}, +e2: {gfit2(cur, d, max, fst(V, x)) == False{} : Bool}, +hb: HB(cur, s, d, max), hf: Free(V, Con{x, r}, s, d), ihn: HB(U32.inc(lst(V, x)), s, d, max) -> Free(V, r, s, d) -> GA(s, GR(V, r, U32.inc(lst(V, x)), d, max))) -> GA(s, gend(gscan(V, r, gmove(O.ult(lst(V, x), max), lst(V, x)), d, max), d, max)):
  match c4:
    case True{}:
      +rest = O.bo.and_r(O.ule(cur, s), Bool.and(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max)), hb)
      +smax = O.u.le_trans(s, U32.add(s, d), max, O.bo.and_l(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max), rest), O.bo.and_r(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max), rest))
      gc.move(O.ult(lst(V, x), max), V, x, r, s, d, max, {==}, O.u.lt_le(lst(V, x), s, max, e4, smax), O.bo.and_intro(O.ule(U32.inc(lst(V, x)), s), Bool.and(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max)), O.u.inc_le(lst(V, x), s, e4), rest), hf, ihn)
    case False{}:
      Empty.absurd(GA(s, gend(gscan(V, r, gmove(O.ult(lst(V, x), max), lst(V, x)), d, max), d, max)), gc.c5(O.ult(s, fst(V, x)), V, x, r, cur, s, d, max, w, {==}, e4, e2, hb, hf))

def gc.try(c2: Bool, -V: Data, +x: Ent(V), +r: Es(V), +cur: U32, +s: U32, +d: U32, +max: U32, +w: {wf(V, Con{x, r}) == True{} : Bool}, +e2: {gfit2(cur, d, max, fst(V, x)) == c2 : Bool}, +hb: HB(cur, s, d, max), hf: Free(V, Con{x, r}, s, d), ihn: HB(U32.inc(lst(V, x)), s, d, max) -> Free(V, r, s, d) -> GA(s, GR(V, r, U32.inc(lst(V, x)), d, max))) -> GA(s, gend(gscan(V, r, gtry(c2, cur, lst(V, x), max), d, max), d, max)):
  match c2:
    case True{}:
      %Equal.sym(M.MapleGap<U32>, gscan(V, r, M.MapleGapFound{cur}, d, max), M.MapleGapFound{cur}, gscan.found(V, r, cur, d, max)) : GA(s, gend(_, d, max))
      O.bo.and_l(O.ule(cur, s), Bool.and(O.ule(s, U32.add(s, d)), O.ule(U32.add(s, d), max)), hb)
    case False{}:
      gc.dec(O.ult(lst(V, x), s), V, x, r, cur, s, d, max, w, {==}, e2, hb, hf, ihn)

def gc.step(before: Bool, -V: Data, +x: Ent(V), +r: Es(V), +cur: U32, +s: U32, +d: U32, +max: U32, +w: {wf(V, Con{x, r}) == True{} : Bool}, +e0: {O.ult(lst(V, x), cur) == before : Bool}, +hb: HB(cur, s, d, max), hf: Free(V, Con{x, r}, s, d), ihc: Free(V, r, s, d) -> GA(s, GR(V, r, cur, d, max)), ihn: HB(U32.inc(lst(V, x)), s, d, max) -> Free(V, r, s, d) -> GA(s, GR(V, r, U32.inc(lst(V, x)), d, max))) -> GA(s, gend(gscan(V, r, gentry(V, before, x, cur, d, max), d, max), d, max)):
  match before:
    case True{}:
      ihc(free.tail(V, x, r, s, d, hf))
    case False{}:
      gc.try(gfit2(cur, d, max, fst(V, x)), V, x, r, cur, s, d, max, w, {==}, hb, hf, ihn)

# in an ordered list, a free run from s (cur <= s, within max) means the
# search answers, at or below s
def gcomplete(-V: Data, xs: Es(V), +cur: U32, +s: U32, +d: U32, +max: U32, +w: {wf(V, xs) == True{} : Bool}, +hb: HB(cur, s, d, max), hf: Free(V, xs, s, d)) -> GA(s, GR(V, xs, cur, d, max)):
  match xs:
    case Nil{}:
      gc.end(gfit(cur, d, max), cur, s, d, max, {==}, hb)
    case Con{+x, +r}:
      +wt = wf.tail(V, x, r, w)
      gc.step(O.ult(lst(V, x), cur), V, x, r, cur, s, d, max, w, {==}, hb, hf, f => gcomplete(V, r, cur, s, d, max, wt, hb, f), h => f => gcomplete(V, r, U32.inc(lst(V, x)), s, d, max, wt, h, f))

# Cutting an append, and cutting lists that lie wholly on one side

def cutlo.app(-V: Data, eb: Bool, sb: Bool, x: Ent(V), -d: U32, -rest: Es(V), -ys: Es(V)) -> {app(V, cutlo(V, eb, sb, x, d, rest), ys) == cutlo(V, eb, sb, x, d, app(V, rest, ys)) : Es(V)}:
  match eb:
    case True{}:
      {==}
    case False{}:
      match sb:
        case True{}:
          match x:
            case M.MapleEntry{f, l, v}:
              {==}
        case False{}:
          {==}

def cuthi.app(-V: Data, sa: Bool, ea: Bool, x: Ent(V), -s: U32, -rest: Es(V), -ys: Es(V)) -> {app(V, cuthi(V, sa, ea, x, s, rest), ys) == cuthi(V, sa, ea, x, s, app(V, rest, ys)) : Es(V)}:
  match sa:
    case True{}:
      {==}
    case False{}:
      match ea:
        case True{}:
          match x:
            case M.MapleEntry{f, l, v}:
              {==}
        case False{}:
          {==}

def below.app(-V: Data, xs: Es(V), +ys: Es(V), +a: U32) -> {below(V, app(V, xs, ys), a) == app(V, below(V, xs, a), below(V, ys, a)) : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(Es(V), cutlo(V, O.ult(lst(V, x), a), O.ult(fst(V, x), a), x, U32.sub(a, 1), below(V, app(V, r, ys), a)), cutlo(V, O.ult(lst(V, x), a), O.ult(fst(V, x), a), x, U32.sub(a, 1), app(V, below(V, r, a), below(V, ys, a))), app(V, cutlo(V, O.ult(lst(V, x), a), O.ult(fst(V, x), a), x, U32.sub(a, 1), below(V, r, a)), below(V, ys, a)), Equal.cong(Es(V), Es(V), q => cutlo(V, O.ult(lst(V, x), a), O.ult(fst(V, x), a), x, U32.sub(a, 1), q), below(V, app(V, r, ys), a), app(V, below(V, r, a), below(V, ys, a)), below.app(V, r, ys, a)), Equal.sym(Es(V), app(V, cutlo(V, O.ult(lst(V, x), a), O.ult(fst(V, x), a), x, U32.sub(a, 1), below(V, r, a)), below(V, ys, a)), cutlo(V, O.ult(lst(V, x), a), O.ult(fst(V, x), a), x, U32.sub(a, 1), app(V, below(V, r, a), below(V, ys, a))), cutlo.app(V, O.ult(lst(V, x), a), O.ult(fst(V, x), a), x, U32.sub(a, 1), below(V, r, a), below(V, ys, a))))

def above.app(-V: Data, xs: Es(V), +ys: Es(V), +b: U32) -> {above(V, app(V, xs, ys), b) == app(V, above(V, xs, b), above(V, ys, b)) : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(Es(V), cuthi(V, O.ult(b, fst(V, x)), O.ult(b, lst(V, x)), x, U32.inc(b), above(V, app(V, r, ys), b)), cuthi(V, O.ult(b, fst(V, x)), O.ult(b, lst(V, x)), x, U32.inc(b), app(V, above(V, r, b), above(V, ys, b))), app(V, cuthi(V, O.ult(b, fst(V, x)), O.ult(b, lst(V, x)), x, U32.inc(b), above(V, r, b)), above(V, ys, b)), Equal.cong(Es(V), Es(V), q => cuthi(V, O.ult(b, fst(V, x)), O.ult(b, lst(V, x)), x, U32.inc(b), q), above(V, app(V, r, ys), b), app(V, above(V, r, b), above(V, ys, b)), above.app(V, r, ys, b)), Equal.sym(Es(V), app(V, cuthi(V, O.ult(b, fst(V, x)), O.ult(b, lst(V, x)), x, U32.inc(b), above(V, r, b)), above(V, ys, b)), cuthi(V, O.ult(b, fst(V, x)), O.ult(b, lst(V, x)), x, U32.inc(b), app(V, above(V, r, b), above(V, ys, b))), cuthi.app(V, O.ult(b, fst(V, x)), O.ult(b, lst(V, x)), x, U32.inc(b), above(V, r, b), above(V, ys, b))))

def cutlo.true(-V: Data, eb: Bool, -sb: Bool, -x: Ent(V), -d: U32, -rest: Es(V), +e: {eb == True{} : Bool}) -> {cutlo(V, eb, sb, x, d, rest) == Con{x, rest} : Es(V)}:
  match eb:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({cutlo(V, False{}, sb, x, d, rest) == Con{x, rest} : Es(V)}, O.ab.ft(e))

def cuthi.true(-V: Data, sa: Bool, -ea: Bool, -x: Ent(V), -s: U32, -rest: Es(V), +e: {sa == True{} : Bool}) -> {cuthi(V, sa, ea, x, s, rest) == Con{x, rest} : Es(V)}:
  match sa:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({cuthi(V, False{}, ea, x, s, rest) == Con{x, rest} : Es(V)}, O.ab.ft(e))

def cuthi.ff(-V: Data, sa: Bool, ea: Bool, -x: Ent(V), -s: U32, -rest: Es(V), +e1: {sa == False{} : Bool}, +e2: {ea == False{} : Bool}) -> {cuthi(V, sa, ea, x, s, rest) == rest : Es(V)}:
  match sa:
    case True{}:
      Empty.absurd({Con{x, rest} == rest : Es(V)}, O.ab.tf(e1))
    case False{}:
      match ea:
        case True{}:
          Empty.absurd({cuthi(V, False{}, True{}, x, s, rest) == rest : Es(V)}, O.ab.tf(e2))
        case False{}:
          {==}

# everything ends by p < a: nothing is cut below a
def below.all(-V: Data, xs: Es(V), +p: U32, +a: U32, +h: {lasts_le(V, xs, p) == True{} : Bool}, +g: {O.ult(p, a) == True{} : Bool}) -> {below(V, xs, a) == xs : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(Es(V), cutlo(V, O.ult(lst(V, x), a), O.ult(fst(V, x), a), x, U32.sub(a, 1), below(V, r, a)), Con{x, below(V, r, a)}, Con{x, r}, cutlo.true(V, O.ult(lst(V, x), a), O.ult(fst(V, x), a), x, U32.sub(a, 1), below(V, r, a), O.u.le_lt(lst(V, x), p, a, O.bo.and_l(O.ule(lst(V, x), p), lasts_le(V, r, p), h), g)), Equal.cong(Es(V), Es(V), q => Con{x, q}, below(V, r, a), r, below.all(V, r, p, a, O.bo.and_r(O.ule(lst(V, x), p), lasts_le(V, r, p), h), g)))

# everything starts after b: nothing is cut above b
def above.all(-V: Data, xs: Es(V), +b: U32, +h: {aft(V, b, xs) == True{} : Bool}) -> {above(V, xs, b) == xs : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(Es(V), cuthi(V, O.ult(b, fst(V, x)), O.ult(b, lst(V, x)), x, U32.inc(b), above(V, r, b)), Con{x, above(V, r, b)}, Con{x, r}, cuthi.true(V, O.ult(b, fst(V, x)), O.ult(b, lst(V, x)), x, U32.inc(b), above(V, r, b), aft.head(V, b, x, r, h)), Equal.cong(Es(V), Es(V), q => Con{x, q}, above(V, r, b), r, above.all(V, r, b, aft.tail(V, b, x, r, h))))

# an ordered list ending by p <= b has nothing above b
def above.nil(-V: Data, xs: Es(V), +p: U32, +b: U32, +h: {lasts_le(V, xs, p) == True{} : Bool}, +w: {wf(V, xs) == True{} : Bool}, +g: {O.ule(p, b) == True{} : Bool}) -> {above(V, xs, b) == Nil{} : Es(V)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +lb = O.u.le_trans(lst(V, x), p, b, O.bo.and_l(O.ule(lst(V, x), p), lasts_le(V, r, p), h), g)
      Equal.trans(Es(V), cuthi(V, O.ult(b, fst(V, x)), O.ult(b, lst(V, x)), x, U32.inc(b), above(V, r, b)), above(V, r, b), Nil{}, cuthi.ff(V, O.ult(b, fst(V, x)), O.ult(b, lst(V, x)), x, U32.inc(b), above(V, r, b), O.u.le_not_lt(fst(V, x), b, O.u.le_trans(fst(V, x), lst(V, x), b, wf.le(V, x, r, w), lb)), O.u.le_not_lt(lst(V, x), b, lb)), above.nil(V, r, p, b, O.bo.and_r(O.ule(lst(V, x), p), lasts_le(V, r, p), h), wf.tail(V, x, r, w), g))

def mor.none(-A: Data, m: Maybe<&2, A>) -> {Maybe.or(&2, A, m, None{}) == m : Maybe<&2, A>}:
  match m:
    case Some{x}:
      {==}
    case None{}:
      {==}

def mor.assoc(-A: Data, a: Maybe<&2, A>, -b: Maybe<&2, A>, -c: Maybe<&2, A>) -> {Maybe.or(&2, A, Maybe.or(&2, A, a, b), c) == Maybe.or(&2, A, a, Maybe.or(&2, A, b, c)) : Maybe<&2, A>}:
  match a:
    case Some{x}:
      {==}
    case None{}:
      {==}

# the last key of xs ++ ys is that of ys, else that of xs
def lkey.app(-V: Data, xs: Es(V), +ys: Es(V)) -> {lkey(V, app(V, xs, ys)) == Maybe.or(&2, U32, lkey(V, ys), lkey(V, xs)) : Maybe<&2, U32>}:
  match xs:
    case Nil{}:
      Equal.sym(Maybe<&2, U32>, Maybe.or(&2, U32, lkey(V, ys), None{}), lkey(V, ys), mor.none(U32, lkey(V, ys)))
    case Con{+x, +r}:
      Equal.trans(Maybe<&2, U32>, Maybe.or(&2, U32, lkey(V, app(V, r, ys)), Some{lst(V, x)}), Maybe.or(&2, U32, Maybe.or(&2, U32, lkey(V, ys), lkey(V, r)), Some{lst(V, x)}), Maybe.or(&2, U32, lkey(V, ys), Maybe.or(&2, U32, lkey(V, r), Some{lst(V, x)})), Equal.cong(Maybe<&2, U32>, Maybe<&2, U32>, m => Maybe.or(&2, U32, m, Some{lst(V, x)}), lkey(V, app(V, r, ys)), Maybe.or(&2, U32, lkey(V, ys), lkey(V, r)), lkey.app(V, r, ys)), mor.assoc(U32, lkey(V, ys), lkey(V, r), Some{lst(V, x)}))
