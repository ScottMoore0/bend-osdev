import Base
import ../word64/word64.bend as W
import ./timer.bend as T
import ./store.bend as S
import ./sorted.bend as SL
import ./timerqueue.bend as Q
import ./proof_order.bend as O
import ./LAWS.bend as Laws

# Every timer of a list at or after y

def tq.all_ge(+y: T.TqTimer, xs: List<&2, T.TqTimer>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{z, r}:
      Bool.and(T.TqTimer.le(y, z), tq.all_ge(y, r))

# Sorted lists

def ls.tail(+y: T.TqTimer, t: List<&2, T.TqTimer>, +h: {T.TqTimer.sorted(Con{y, t}) == True{} : Bool}) -> {T.TqTimer.sorted(t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      O.bo.and_r(T.TqTimer.le(y, z), T.TqTimer.sorted(Con{z, r}), h)

def ls.ge_trans(t: List<&2, T.TqTimer>, +y: T.TqTimer, +z: T.TqTimer, +h: {T.TqTimer.le(y, z) == True{} : Bool}, +g: {tq.all_ge(z, t) == True{} : Bool}) -> {tq.all_ge(y, t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+w, +r}:
      O.bo.and_intro(T.TqTimer.le(y, w), tq.all_ge(y, r), O.kt.le_trans(y, z, w, h, O.bo.and_l(T.TqTimer.le(z, w), tq.all_ge(z, r), g)), ls.ge_trans(r, y, z, h, O.bo.and_r(T.TqTimer.le(z, w), tq.all_ge(z, r), g)))

def ls.all(t: List<&2, T.TqTimer>, +y: T.TqTimer, +h: {T.TqTimer.sorted(Con{y, t}) == True{} : Bool}) -> {tq.all_ge(y, t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      O.bo.and_intro(T.TqTimer.le(y, z), tq.all_ge(y, r), O.bo.and_l(T.TqTimer.le(y, z), T.TqTimer.sorted(Con{z, r}), h), ls.ge_trans(r, y, z, O.bo.and_l(T.TqTimer.le(y, z), T.TqTimer.sorted(Con{z, r}), h), ls.all(r, z, O.bo.and_r(T.TqTimer.le(y, z), T.TqTimer.sorted(Con{z, r}), h))))

def ls.cons(r: List<&2, T.TqTimer>, +y: T.TqTimer, +g: {tq.all_ge(y, r) == True{} : Bool}, +s: {T.TqTimer.sorted(r) == True{} : Bool}) -> {T.TqTimer.sorted(Con{y, r}) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case Con{+z, +r2}:
      O.bo.and_intro(T.TqTimer.le(y, z), T.TqTimer.sorted(Con{z, r2}), O.bo.and_l(T.TqTimer.le(y, z), tq.all_ge(y, r2), g), s)

# Insertion keeps a list sorted

def ins.put(b: Bool, +x: T.TqTimer, +y: T.TqTimer, +z: T.TqTimer, +r: List<&2, T.TqTimer>, +eb: {T.TqTimer.lt(x, z) == b : Bool}, +hy: {T.TqTimer.le(y, x) == True{} : Bool}, +hs: {T.TqTimer.sorted(Con{y, Con{z, r}}) == True{} : Bool}, ih: {T.TqTimer.le(z, x) == True{} : Bool} -> {T.TqTimer.sorted(Con{z, SL.TqSorted.insert(r, x)}) == True{} : Bool}) -> {T.TqTimer.sorted(Con{y, SL.TqSorted.insert.put(b, x, z, SL.TqSorted.insert(r, x), r)}) == True{} : Bool}:
  match b:
    case True{}:
      O.bo.and_intro(T.TqTimer.le(y, x), T.TqTimer.sorted(Con{x, Con{z, r}}), hy, O.bo.and_intro(T.TqTimer.le(x, z), T.TqTimer.sorted(Con{z, r}), O.kt.lt_le(x, z, eb), O.bo.and_r(T.TqTimer.le(y, z), T.TqTimer.sorted(Con{z, r}), hs)))
    case False{}:
      O.bo.and_intro(T.TqTimer.le(y, z), T.TqTimer.sorted(Con{z, SL.TqSorted.insert(r, x)}), O.bo.and_l(T.TqTimer.le(y, z), T.TqTimer.sorted(Con{z, r}), hs), ih(O.kt.not_lt(x, z, eb)))

def ins.head(t: List<&2, T.TqTimer>, +y: T.TqTimer, +x: T.TqTimer, +hy: {T.TqTimer.le(y, x) == True{} : Bool}, +hs: {T.TqTimer.sorted(Con{y, t}) == True{} : Bool}) -> {T.TqTimer.sorted(Con{y, SL.TqSorted.insert(t, x)}) == True{} : Bool}:
  match t:
    case Nil{}:
      O.bo.and_intro(T.TqTimer.le(y, x), True{}, hy, {==})
    case Con{+z, +r}:
      ins.put(T.TqTimer.lt(x, z), x, y, z, r, {==}, hy, hs, u => ins.head(r, z, x, u, O.bo.and_r(T.TqTimer.le(y, z), T.TqTimer.sorted(Con{z, r}), hs)))

def ins.top(b: Bool, +x: T.TqTimer, +y: T.TqTimer, +t: List<&2, T.TqTimer>, +eb: {T.TqTimer.lt(x, y) == b : Bool}, +h: {T.TqTimer.sorted(Con{y, t}) == True{} : Bool}) -> {T.TqTimer.sorted(SL.TqSorted.insert.put(b, x, y, SL.TqSorted.insert(t, x), t)) == True{} : Bool}:
  match b:
    case True{}:
      O.bo.and_intro(T.TqTimer.le(x, y), T.TqTimer.sorted(Con{y, t}), O.kt.lt_le(x, y, eb), h)
    case False{}:
      ins.head(t, y, x, O.kt.not_lt(x, y, eb), h)

def ins.sorted(xs: List<&2, T.TqTimer>, +x: T.TqTimer, +h: {T.TqTimer.sorted(xs) == True{} : Bool}) -> {T.TqTimer.sorted(SL.TqSorted.insert(xs, x)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      ins.top(T.TqTimer.lt(x, y), x, y, t, {==}, h)

# Removal keeps a list sorted

def ge.rput(b: Bool, +y: T.TqTimer, +z: T.TqTimer, +rest: List<&2, T.TqTimer>, +g1: {T.TqTimer.le(y, z) == True{} : Bool}, +g2: {tq.all_ge(y, rest) == True{} : Bool}) -> {tq.all_ge(y, SL.TqSorted.remove.put(b, z, rest)) == True{} : Bool}:
  match b:
    case True{}:
      g2
    case False{}:
      O.bo.and_intro(T.TqTimer.le(y, z), tq.all_ge(y, rest), g1, g2)

def ls.ge_remove(t: List<&2, T.TqTimer>, +y: T.TqTimer, +x: T.TqTimer, +g: {tq.all_ge(y, t) == True{} : Bool}) -> {tq.all_ge(y, SL.TqSorted.remove(t, x)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      ge.rput(T.TqTimer.is_eq(z, x), y, z, SL.TqSorted.remove(r, x), O.bo.and_l(T.TqTimer.le(y, z), tq.all_ge(y, r), g), ls.ge_remove(r, y, x, O.bo.and_r(T.TqTimer.le(y, z), tq.all_ge(y, r), g)))

def rem.put(b: Bool, +y: T.TqTimer, +rest: List<&2, T.TqTimer>, +g: {tq.all_ge(y, rest) == True{} : Bool}, +s: {T.TqTimer.sorted(rest) == True{} : Bool}) -> {T.TqTimer.sorted(SL.TqSorted.remove.put(b, y, rest)) == True{} : Bool}:
  match b:
    case True{}:
      s
    case False{}:
      ls.cons(rest, y, g, s)

def rem.sorted(xs: List<&2, T.TqTimer>, +x: T.TqTimer, +h: {T.TqTimer.sorted(xs) == True{} : Bool}) -> {T.TqTimer.sorted(SL.TqSorted.remove(xs, x)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      rem.put(T.TqTimer.is_eq(y, x), y, SL.TqSorted.remove(t, x), ls.ge_remove(t, y, x, ls.all(t, y, h)), rem.sorted(t, x, ls.tail(y, t, h)))

# Ids stay below the next one

def ids.succ(xs: List<&2, T.TqTimer>, +n: Nat, +h: {T.TqTimer.ids_below(n, xs) == True{} : Bool}) -> {T.TqTimer.ids_below(1n+n, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      O.bo.and_intro(Nat.is_lt(T.TqTimer.id(z), 1n+n), T.TqTimer.ids_below(1n+n, r), O.n.lt_succ(T.TqTimer.id(z), n, O.bo.and_l(Nat.is_lt(T.TqTimer.id(z), n), T.TqTimer.ids_below(n, r), h)), ids.succ(r, n, O.bo.and_r(Nat.is_lt(T.TqTimer.id(z), n), T.TqTimer.ids_below(n, r), h)))

def ids.put(b: Bool, +x: T.TqTimer, +y: T.TqTimer, +t: List<&2, T.TqTimer>, +n: Nat, +hx: {Nat.is_lt(T.TqTimer.id(x), n) == True{} : Bool}, +h: {T.TqTimer.ids_below(n, Con{y, t}) == True{} : Bool}, +ih: {T.TqTimer.ids_below(n, SL.TqSorted.insert(t, x)) == True{} : Bool}) -> {T.TqTimer.ids_below(n, SL.TqSorted.insert.put(b, x, y, SL.TqSorted.insert(t, x), t)) == True{} : Bool}:
  match b:
    case True{}:
      O.bo.and_intro(Nat.is_lt(T.TqTimer.id(x), n), T.TqTimer.ids_below(n, Con{y, t}), hx, h)
    case False{}:
      O.bo.and_intro(Nat.is_lt(T.TqTimer.id(y), n), T.TqTimer.ids_below(n, SL.TqSorted.insert(t, x)), O.bo.and_l(Nat.is_lt(T.TqTimer.id(y), n), T.TqTimer.ids_below(n, t), h), ih)

def ids.ins(xs: List<&2, T.TqTimer>, +x: T.TqTimer, +n: Nat, +hx: {Nat.is_lt(T.TqTimer.id(x), n) == True{} : Bool}, +h: {T.TqTimer.ids_below(n, xs) == True{} : Bool}) -> {T.TqTimer.ids_below(n, SL.TqSorted.insert(xs, x)) == True{} : Bool}:
  match xs:
    case Nil{}:
      O.bo.and_intro(Nat.is_lt(T.TqTimer.id(x), n), True{}, hx, {==})
    case Con{+y, +t}:
      ids.put(T.TqTimer.lt(x, y), x, y, t, n, hx, h, ids.ins(t, x, n, hx, O.bo.and_r(Nat.is_lt(T.TqTimer.id(y), n), T.TqTimer.ids_below(n, t), h)))

def ids.rput(b: Bool, +y: T.TqTimer, +rest: List<&2, T.TqTimer>, +n: Nat, +hy: {Nat.is_lt(T.TqTimer.id(y), n) == True{} : Bool}, +ih: {T.TqTimer.ids_below(n, rest) == True{} : Bool}) -> {T.TqTimer.ids_below(n, SL.TqSorted.remove.put(b, y, rest)) == True{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      O.bo.and_intro(Nat.is_lt(T.TqTimer.id(y), n), T.TqTimer.ids_below(n, rest), hy, ih)

def ids.rem(xs: List<&2, T.TqTimer>, +x: T.TqTimer, +n: Nat, +h: {T.TqTimer.ids_below(n, xs) == True{} : Bool}) -> {T.TqTimer.ids_below(n, SL.TqSorted.remove(xs, x)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      ids.rput(T.TqTimer.is_eq(y, x), y, SL.TqSorted.remove(t, x), n, O.bo.and_l(Nat.is_lt(T.TqTimer.id(y), n), T.TqTimer.ids_below(n, t), h), ids.rem(t, x, n, O.bo.and_r(Nat.is_lt(T.TqTimer.id(y), n), T.TqTimer.ids_below(n, t), h)))

# Membership

def mem.put(b: Bool, +x: T.TqTimer, +z: T.TqTimer, +t: List<&2, T.TqTimer>, +y: T.TqTimer, +ih: {T.TqTimer.member(SL.TqSorted.insert(t, x), y) == Bool.or(T.TqTimer.is_eq(x, y), T.TqTimer.member(t, y)) : Bool}) -> {T.TqTimer.member(SL.TqSorted.insert.put(b, x, z, SL.TqSorted.insert(t, x), t), y) == Bool.or(T.TqTimer.is_eq(x, y), T.TqTimer.member(Con{z, t}, y)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, T.TqTimer.member(SL.TqSorted.insert(t, x), y), Bool.or(T.TqTimer.is_eq(x, y), T.TqTimer.member(t, y)), ih) : {Bool.or(T.TqTimer.is_eq(z, y), _) == Bool.or(T.TqTimer.is_eq(x, y), Bool.or(T.TqTimer.is_eq(z, y), T.TqTimer.member(t, y))) : Bool}
      O.bo.or_swap(T.TqTimer.is_eq(z, y), T.TqTimer.is_eq(x, y), T.TqTimer.member(t, y))

def mem.ins(xs: List<&2, T.TqTimer>, +x: T.TqTimer, +y: T.TqTimer) -> {T.TqTimer.member(SL.TqSorted.insert(xs, x), y) == Bool.or(T.TqTimer.is_eq(x, y), T.TqTimer.member(xs, y)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+z, +t}:
      mem.put(T.TqTimer.lt(x, z), x, z, t, y, mem.ins(t, x, y))

def mg.put(b: Bool, +y: T.TqTimer, +rest: List<&2, T.TqTimer>, +x: T.TqTimer, +eb: {T.TqTimer.is_eq(y, x) == b : Bool}, +ih: {T.TqTimer.member(rest, x) == False{} : Bool}) -> {T.TqTimer.member(SL.TqSorted.remove.put(b, y, rest), x) == False{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, T.TqTimer.is_eq(y, x), False{}, eb) : {Bool.or(_, T.TqTimer.member(rest, x)) == False{} : Bool}
      %Equal.sym(Bool, T.TqTimer.member(rest, x), False{}, ih) : {Bool.or(False{}, _) == False{} : Bool}
      {==}

def mem.gone(xs: List<&2, T.TqTimer>, +x: T.TqTimer) -> {T.TqTimer.member(SL.TqSorted.remove(xs, x), x) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      mg.put(T.TqTimer.is_eq(y, x), y, SL.TqSorted.remove(t, x), x, {==}, mem.gone(t, x))

def mo.put(b: Bool, +z: T.TqTimer, +x: T.TqTimer, +y: T.TqTimer, +t: List<&2, T.TqTimer>, +eb: {T.TqTimer.is_eq(z, x) == b : Bool}, +d: {T.TqTimer.is_eq(x, y) == False{} : Bool}, +ih: {T.TqTimer.member(SL.TqSorted.remove(t, x), y) == T.TqTimer.member(t, y) : Bool}) -> {T.TqTimer.member(SL.TqSorted.remove.put(b, z, SL.TqSorted.remove(t, x)), y) == T.TqTimer.member(Con{z, t}, y) : Bool}:
  match b:
    case True{}:
      %Equal.sym(T.TqTimer, z, x, O.kt.eq(z, x, eb)) : {T.TqTimer.member(SL.TqSorted.remove(t, x), y) == Bool.or(T.TqTimer.is_eq(_, y), T.TqTimer.member(t, y)) : Bool}
      %Equal.sym(Bool, T.TqTimer.is_eq(x, y), False{}, d) : {T.TqTimer.member(SL.TqSorted.remove(t, x), y) == Bool.or(_, T.TqTimer.member(t, y)) : Bool}
      ih
    case False{}:
      %Equal.sym(Bool, T.TqTimer.member(SL.TqSorted.remove(t, x), y), T.TqTimer.member(t, y), ih) : {Bool.or(T.TqTimer.is_eq(z, y), _) == Bool.or(T.TqTimer.is_eq(z, y), T.TqTimer.member(t, y)) : Bool}
      {==}

def mem.other(xs: List<&2, T.TqTimer>, +x: T.TqTimer, +y: T.TqTimer, +d: {T.TqTimer.is_eq(x, y) == False{} : Bool}) -> {T.TqTimer.member(SL.TqSorted.remove(xs, x), y) == T.TqTimer.member(xs, y) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+z, +t}:
      mo.put(T.TqTimer.is_eq(z, x), z, x, y, t, {==}, d, mem.other(t, x, y, d))

def mem.fresh(xs: List<&2, T.TqTimer>, +n: Nat, +e: W.W64, +h: {T.TqTimer.ids_below(n, xs) == True{} : Bool}) -> {T.TqTimer.member(xs, T.TqTimer{e, n}) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{T.TqTimer{+ez, +iz}, +r}:
      %Equal.sym(Bool, T.TqTimer.is_eq(T.TqTimer{ez, iz}, T.TqTimer{e, n}), False{}, O.kt.fresh(ez, iz, e, n, O.bo.and_l(Nat.is_lt(iz, n), T.TqTimer.ids_below(n, r), h))) : {Bool.or(_, T.TqTimer.member(r, T.TqTimer{e, n})) == False{} : Bool}
      %Equal.sym(Bool, T.TqTimer.member(r, T.TqTimer{e, n}), False{}, mem.fresh(r, n, e, O.bo.and_r(Nat.is_lt(iz, n), T.TqTimer.ids_below(n, r), h))) : {Bool.or(False{}, _) == False{} : Bool}
      {==}

def mem.app(a: List<&2, T.TqTimer>, +b: List<&2, T.TqTimer>, +x: T.TqTimer) -> {T.TqTimer.member(List.append(&2, T.TqTimer, a, b), x) == Bool.or(T.TqTimer.member(a, x), T.TqTimer.member(b, x)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      %Equal.sym(Bool, T.TqTimer.member(List.append(&2, T.TqTimer, r, b), x), Bool.or(T.TqTimer.member(r, x), T.TqTimer.member(b, x)), mem.app(r, b, x)) : {Bool.or(T.TqTimer.is_eq(y, x), _) == Bool.or(Bool.or(T.TqTimer.is_eq(y, x), T.TqTimer.member(r, x)), T.TqTimer.member(b, x)) : Bool}
      O.bo.or_assoc(T.TqTimer.is_eq(y, x), T.TqTimer.member(r, x), T.TqTimer.member(b, x))

# The expiry loop on a sorted list: each lemma by whether the first timer
# is due

def ex.app.case(d: Bool, +x: T.TqTimer, +t: List<&2, T.TqTimer>, +now: W.W64, +ih: {List.append(&2, T.TqTimer, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), t, now)), Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), t, now))) == t : List<&2, T.TqTimer>}) -> {List.append(&2, T.TqTimer, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.go(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), 1n+List.length(&2, T.TqTimer, t), Some{x}, d, Con{x, t}, now)), Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.go(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), 1n+List.length(&2, T.TqTimer, t), Some{x}, d, Con{x, t}, now))) == Con{x, t} : List<&2, T.TqTimer>}:
  match d:
    case True{}:
      %Equal.sym(List<&2, T.TqTimer>, List.append(&2, T.TqTimer, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), t, now)), Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), t, now))), t, ih) : {Con{x, _} == Con{x, t} : List<&2, T.TqTimer>}
      {==}
    case False{}:
      {==}

def ex.app(l: List<&2, T.TqTimer>, +now: W.W64) -> {List.append(&2, T.TqTimer, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), l, now)), Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), l, now))) == l : List<&2, T.TqTimer>}:
  match l:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      ex.app.case(T.TqTime.le(T.TqTimer.expiry(x), now), x, t, now, ex.app(t, now))

def ex.due.case(d: Bool, +x: T.TqTimer, +t: List<&2, T.TqTimer>, +now: W.W64, +ed: {T.TqTime.le(T.TqTimer.expiry(x), now) == d : Bool}, +ih: {T.TqTimer.all_due(now, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), t, now))) == True{} : Bool}) -> {T.TqTimer.all_due(now, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.go(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), 1n+List.length(&2, T.TqTimer, t), Some{x}, d, Con{x, t}, now))) == True{} : Bool}:
  match d:
    case True{}:
      O.bo.and_intro(T.TqTime.le(T.TqTimer.expiry(x), now), T.TqTimer.all_due(now, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), t, now))), ed, ih)
    case False{}:
      {==}

def ex.due(l: List<&2, T.TqTimer>, +now: W.W64) -> {T.TqTimer.all_due(now, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), l, now))) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      ex.due.case(T.TqTime.le(T.TqTimer.expiry(x), now), x, t, now, {==}, ex.due(t, now))

def ex.ge.case(d: Bool, +y: T.TqTimer, +x: T.TqTimer, +t: List<&2, T.TqTimer>, +now: W.W64, +g1: {T.TqTimer.le(y, x) == True{} : Bool}, +ih: {tq.all_ge(y, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), t, now))) == True{} : Bool}) -> {tq.all_ge(y, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.go(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), 1n+List.length(&2, T.TqTimer, t), Some{x}, d, Con{x, t}, now))) == True{} : Bool}:
  match d:
    case True{}:
      O.bo.and_intro(T.TqTimer.le(y, x), tq.all_ge(y, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), t, now))), g1, ih)
    case False{}:
      {==}

def ex.ge(t: List<&2, T.TqTimer>, +y: T.TqTimer, +now: W.W64, +g: {tq.all_ge(y, t) == True{} : Bool}) -> {tq.all_ge(y, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), t, now))) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      ex.ge.case(T.TqTime.le(T.TqTimer.expiry(x), now), y, x, r, now, O.bo.and_l(T.TqTimer.le(y, x), tq.all_ge(y, r), g), ex.ge(r, y, now, O.bo.and_r(T.TqTimer.le(y, x), tq.all_ge(y, r), g)))

def ex.sorted.case(d: Bool, +x: T.TqTimer, +t: List<&2, T.TqTimer>, +now: W.W64, +h: {T.TqTimer.sorted(Con{x, t}) == True{} : Bool}, +ih: {T.TqTimer.sorted(Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), t, now))) == True{} : Bool}) -> {T.TqTimer.sorted(Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.go(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), 1n+List.length(&2, T.TqTimer, t), Some{x}, d, Con{x, t}, now))) == True{} : Bool}:
  match d:
    case True{}:
      ls.cons(Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), t, now)), x, ex.ge(t, x, now, ls.all(t, x, h)), ih)
    case False{}:
      {==}

def ex.sorted(l: List<&2, T.TqTimer>, +now: W.W64, +h: {T.TqTimer.sorted(l) == True{} : Bool}) -> {T.TqTimer.sorted(Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), l, now))) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      ex.sorted.case(T.TqTime.le(T.TqTimer.expiry(x), now), x, t, now, h, ex.sorted(t, now, ls.tail(x, t, h)))

def ex.later_ge(t: List<&2, T.TqTimer>, +x: T.TqTimer, +now: W.W64, +hx: {T.TqTime.lt(now, T.TqTimer.expiry(x)) == True{} : Bool}, +g: {tq.all_ge(x, t) == True{} : Bool}) -> {T.TqTimer.all_later(now, t) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+z, +r}:
      O.bo.and_intro(T.TqTime.lt(now, T.TqTimer.expiry(z)), T.TqTimer.all_later(now, r), O.tm.lt_le(now, T.TqTimer.expiry(x), T.TqTimer.expiry(z), hx, O.kt.le_time(x, z, O.bo.and_l(T.TqTimer.le(x, z), tq.all_ge(x, r), g))), ex.later_ge(r, x, now, hx, O.bo.and_r(T.TqTimer.le(x, z), tq.all_ge(x, r), g)))

def ex.later.case(d: Bool, +x: T.TqTimer, +t: List<&2, T.TqTimer>, +now: W.W64, +ed: {T.TqTime.le(T.TqTimer.expiry(x), now) == d : Bool}, +h: {T.TqTimer.sorted(Con{x, t}) == True{} : Bool}, +ih: {T.TqTimer.all_later(now, Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), t, now))) == True{} : Bool}) -> {T.TqTimer.all_later(now, Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.go(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), 1n+List.length(&2, T.TqTimer, t), Some{x}, d, Con{x, t}, now))) == True{} : Bool}:
  match d:
    case True{}:
      ih
    case False{}:
      O.bo.and_intro(T.TqTime.lt(now, T.TqTimer.expiry(x)), T.TqTimer.all_later(now, t), O.tm.not_le(T.TqTimer.expiry(x), now, ed), ex.later_ge(t, x, now, O.tm.not_le(T.TqTimer.expiry(x), now, ed), ls.all(t, x, h)))

def ex.later(l: List<&2, T.TqTimer>, +now: W.W64, +h: {T.TqTimer.sorted(l) == True{} : Bool}) -> {T.TqTimer.all_later(now, Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), l, now))) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      ex.later.case(T.TqTime.le(T.TqTimer.expiry(x), now), x, t, now, {==}, h, ex.later(t, now, ls.tail(x, t, h)))

def ex.st_sorted.case(d: Bool, +x: T.TqTimer, +t: List<&2, T.TqTimer>, +now: W.W64, +h: {T.TqTimer.sorted(Con{x, t}) == True{} : Bool}, +ih: {T.TqTimer.sorted(Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), t, now))) == True{} : Bool}) -> {T.TqTimer.sorted(Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.go(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), 1n+List.length(&2, T.TqTimer, t), Some{x}, d, Con{x, t}, now))) == True{} : Bool}:
  match d:
    case True{}:
      ih
    case False{}:
      h

def ex.st_sorted(l: List<&2, T.TqTimer>, +now: W.W64, +h: {T.TqTimer.sorted(l) == True{} : Bool}) -> {T.TqTimer.sorted(Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), l, now))) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      ex.st_sorted.case(T.TqTime.le(T.TqTimer.expiry(x), now), x, t, now, h, ex.st_sorted(t, now, ls.tail(x, t, h)))

def ex.st_ids.case(d: Bool, +x: T.TqTimer, +t: List<&2, T.TqTimer>, +now: W.W64, +n: Nat, +h: {T.TqTimer.ids_below(n, Con{x, t}) == True{} : Bool}, +ih: {T.TqTimer.ids_below(n, Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), t, now))) == True{} : Bool}) -> {T.TqTimer.ids_below(n, Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.go(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), 1n+List.length(&2, T.TqTimer, t), Some{x}, d, Con{x, t}, now))) == True{} : Bool}:
  match d:
    case True{}:
      ih
    case False{}:
      h

def ex.st_ids(l: List<&2, T.TqTimer>, +now: W.W64, +n: Nat, +h: {T.TqTimer.ids_below(n, l) == True{} : Bool}) -> {T.TqTimer.ids_below(n, Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), l, now))) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      ex.st_ids.case(T.TqTime.le(T.TqTimer.expiry(x), now), x, t, now, n, h, ex.st_ids(t, now, n, O.bo.and_r(Nat.is_lt(T.TqTimer.id(x), n), T.TqTimer.ids_below(n, t), h)))

def never.mem(+q: List<&2, T.TqTimer>, +now: W.W64, +x: T.TqTimer, +c: {T.TqTimer.member(q, x) == False{} : Bool}) -> {T.TqTimer.member(List.append(&2, T.TqTimer, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now)), Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now))), x) == False{} : Bool}:
  %Equal.sym(List<&2, T.TqTimer>, List.append(&2, T.TqTimer, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now)), Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now))), q, ex.app(q, now)) : {T.TqTimer.member(_, x) == False{} : Bool}
  c

def next.from(r: List<&2, T.TqTimer>, +x: T.TqTimer, +g: {tq.all_ge(x, r) == True{} : Bool}) -> {T.TqTimer.all_from(T.TqTimer.expiry(x), r) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case Con{+z, +r2}:
      O.bo.and_intro(T.TqTime.le(T.TqTimer.expiry(x), T.TqTimer.expiry(z)), T.TqTimer.all_from(T.TqTimer.expiry(x), r2), O.kt.le_time(x, z, O.bo.and_l(T.TqTimer.le(x, z), tq.all_ge(x, r2), g)), next.from(r2, x, O.bo.and_r(T.TqTimer.le(x, z), tq.all_ge(x, r2), g)))

# The laws

def Laws.tq_new_valid():
  {==}

def Laws.tq_add_valid(tq, e, v):
  match tq:
    case Q.TimerQueue{+q, +n}:
      O.bo.and_intro(T.TqTimer.sorted(SL.TqSorted.insert(q, T.TqTimer{e, n})), T.TqTimer.ids_below(1n+n, SL.TqSorted.insert(q, T.TqTimer{e, n})), ins.sorted(q, T.TqTimer{e, n}, O.bo.and_l(T.TqTimer.sorted(q), T.TqTimer.ids_below(n, q), v)), ids.ins(q, T.TqTimer{e, n}, 1n+n, O.n.lt_self_succ(n), ids.succ(q, n, O.bo.and_r(T.TqTimer.sorted(q), T.TqTimer.ids_below(n, q), v))))

def Laws.tq_delete_valid(tq, x, v):
  match tq:
    case Q.TimerQueue{+q, +n}:
      O.bo.and_intro(T.TqTimer.sorted(SL.TqSorted.remove(q, x)), T.TqTimer.ids_below(n, SL.TqSorted.remove(q, x)), rem.sorted(q, x, O.bo.and_l(T.TqTimer.sorted(q), T.TqTimer.ids_below(n, q), v)), ids.rem(q, x, n, O.bo.and_r(T.TqTimer.sorted(q), T.TqTimer.ids_below(n, q), v)))

def Laws.tq_expire_valid(tq, now, v):
  match tq:
    case Q.TimerQueue{+q, +n}:
      O.bo.and_intro(T.TqTimer.sorted(Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now))), T.TqTimer.ids_below(n, Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now))), ex.st_sorted(q, now, O.bo.and_l(T.TqTimer.sorted(q), T.TqTimer.ids_below(n, q), v)), ex.st_ids(q, now, n, O.bo.and_r(T.TqTimer.sorted(q), T.TqTimer.ids_below(n, q), v)))

def Laws.tq_sorted(tq, v):
  match tq:
    case Q.TimerQueue{+q, +n}:
      O.bo.and_l(T.TqTimer.sorted(q), T.TqTimer.ids_below(n, q), v)

def Laws.tq_new_empty():
  {==}

def Laws.tq_add_timer(tq, e):
  match tq:
    case Q.TimerQueue{q, +n}:
      {==}

def Laws.tq_add_contains(tq, e):
  match tq:
    case Q.TimerQueue{+q, +n}:
      %Equal.sym(Bool, T.TqTimer.member(SL.TqSorted.insert(q, T.TqTimer{e, n}), T.TqTimer{e, n}), Bool.or(T.TqTimer.is_eq(T.TqTimer{e, n}, T.TqTimer{e, n}), T.TqTimer.member(q, T.TqTimer{e, n})), mem.ins(q, T.TqTimer{e, n}, T.TqTimer{e, n})) : {_ == True{} : Bool}
      %Equal.sym(Bool, T.TqTimer.is_eq(T.TqTimer{e, n}, T.TqTimer{e, n}), True{}, O.kt.refl(T.TqTimer{e, n})) : {Bool.or(_, T.TqTimer.member(q, T.TqTimer{e, n})) == True{} : Bool}
      {==}

def Laws.tq_add_fresh(tq, e, v):
  match tq:
    case Q.TimerQueue{+q, +n}:
      mem.fresh(q, n, e, O.bo.and_r(T.TqTimer.sorted(q), T.TqTimer.ids_below(n, q), v))

def Laws.tq_add_others(tq, e, x, i):
  match tq x:
    case Q.TimerQueue{+q, +n} T.TqTimer{+ex, +ix}:
      %Equal.sym(Bool, T.TqTimer.member(SL.TqSorted.insert(q, T.TqTimer{e, n}), T.TqTimer{ex, ix}), Bool.or(T.TqTimer.is_eq(T.TqTimer{e, n}, T.TqTimer{ex, ix}), T.TqTimer.member(q, T.TqTimer{ex, ix})), mem.ins(q, T.TqTimer{e, n}, T.TqTimer{ex, ix})) : {_ == T.TqTimer.member(q, T.TqTimer{ex, ix}) : Bool}
      %Equal.sym(Bool, T.TqTimer.is_eq(T.TqTimer{e, n}, T.TqTimer{ex, ix}), False{}, O.kt.fresh2(e, n, ex, ix, i)) : {Bool.or(_, T.TqTimer.member(q, T.TqTimer{ex, ix})) == T.TqTimer.member(q, T.TqTimer{ex, ix}) : Bool}
      {==}

def Laws.tq_delete_gone(tq, x):
  match tq:
    case Q.TimerQueue{+q, n}:
      mem.gone(q, x)

def Laws.tq_delete_others(tq, x, y, d):
  match tq:
    case Q.TimerQueue{+q, n}:
      mem.other(q, x, y, d)

def Laws.tq_next_first(tq):
  match tq:
    case Q.TimerQueue{Nil{}, n}:
      {==}
    case Q.TimerQueue{Con{x, r}, n}:
      {==}

def Laws.tq_next_min(tq, t, v, h):
  match tq:
    case Q.TimerQueue{Nil{}, n}:
      Empty.absurd({T.TqTimer.all_from(t, Nil{}) == True{} : Bool}, O.ab.none_some(W.W64, t, h))
    case Q.TimerQueue{Con{T.TqTimer{+e, +i}, +r}, +n}:
      %Equal.cong(Maybe<&2, W.W64>, W.W64, m => Maybe.default(&2, W.W64, m, e), Some{e}, Some{t}, h) : {T.TqTimer.all_from(_, Con{T.TqTimer{e, i}, r}) == True{} : Bool}
      O.bo.and_intro(T.TqTime.le(e, e), T.TqTimer.all_from(e, r), O.tm.le_refl(e), next.from(r, T.TqTimer{e, i}, ls.all(r, T.TqTimer{e, i}, O.bo.and_l(T.TqTimer.sorted(Con{T.TqTimer{e, i}, r}), T.TqTimer.ids_below(n, Con{T.TqTimer{e, i}, r}), v))))

def Laws.tq_expire_split(tq, now):
  match tq:
    case Q.TimerQueue{+q, n}:
      ex.app(q, now)

def Laws.tq_expire_due(tq, now):
  match tq:
    case Q.TimerQueue{+q, n}:
      ex.due(q, now)

def Laws.tq_expire_sorted(tq, now, v):
  match tq:
    case Q.TimerQueue{+q, +n}:
      ex.sorted(q, now, O.bo.and_l(T.TqTimer.sorted(q), T.TqTimer.ids_below(n, q), v))

def Laws.tq_expire_later(tq, now, v):
  match tq:
    case Q.TimerQueue{+q, +n}:
      ex.later(q, now, O.bo.and_l(T.TqTimer.sorted(q), T.TqTimer.ids_below(n, q), v))

def Laws.tq_expire_never(tq, now, x, c):
  match tq:
    case Q.TimerQueue{+q, n}:
      O.bo.or_false_pair(T.TqTimer.member(Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now)), x), T.TqTimer.member(Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now)), x), Equal.trans(Bool, Bool.or(T.TqTimer.member(Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now)), x), T.TqTimer.member(Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now)), x)), T.TqTimer.member(List.append(&2, T.TqTimer, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now)), Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now))), x), False{}, Equal.sym(Bool, T.TqTimer.member(List.append(&2, T.TqTimer, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now)), Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now))), x), Bool.or(T.TqTimer.member(Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now)), x), T.TqTimer.member(Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now)), x)), mem.app(Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now)), Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), q, now)), x)), never.mem(q, now, x, c)))

def or.false_l(a: Bool, -b: Bool, +e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, O.ab.tf(e))
    case False{}:
      {==}

def Laws.tq_deleted_never_fires(tq, now, x):
  match tq:
    case Q.TimerQueue{+q, n}:
      or.false_l(T.TqTimer.member(Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), SL.TqSorted.remove(q, x), now)), x), T.TqTimer.member(Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), SL.TqSorted.remove(q, x), now)), x), Equal.trans(Bool, Bool.or(T.TqTimer.member(Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), SL.TqSorted.remove(q, x), now)), x), T.TqTimer.member(Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), SL.TqSorted.remove(q, x), now)), x)), T.TqTimer.member(List.append(&2, T.TqTimer, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), SL.TqSorted.remove(q, x), now)), Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), SL.TqSorted.remove(q, x), now))), x), False{}, Equal.sym(Bool, T.TqTimer.member(List.append(&2, T.TqTimer, Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), SL.TqSorted.remove(q, x), now)), Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), SL.TqSorted.remove(q, x), now))), x), Bool.or(T.TqTimer.member(Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), SL.TqSorted.remove(q, x), now)), x), T.TqTimer.member(Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), SL.TqSorted.remove(q, x), now)), x)), mem.app(Q.TqSplit.fired(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), SL.TqSorted.remove(q, x), now)), Q.TqSplit.store(List<&2, T.TqTimer>, Q.TimerQueue.expire.split(~List<&2, T.TqTimer>, ~SL.TqSorted.store(), SL.TqSorted.remove(q, x), now)), x)), never.mem(SL.TqSorted.remove(q, x), now, x, mem.gone(q, x))))

def Laws.tq_issued_add(tq, e, x, i):
  match tq:
    case Q.TimerQueue{q, +n}:
      %Equal.sym(Bool, Nat.is_lt(T.TqTimer.id(x), 1n+n), True{}, O.n.lt_succ(T.TqTimer.id(x), n, i)) : {(_, Nat.is_lt(n, 1n+n)) == (True{}, True{}) : Bool & Bool}
      %Equal.sym(Bool, Nat.is_lt(n, 1n+n), True{}, O.n.lt_self_succ(n)) : {(True{}, _) == (True{}, True{}) : Bool & Bool}
      {==}

def Laws.tq_issued_delete(tq, x):
  match tq:
    case Q.TimerQueue{q, n}:
      {==}

def Laws.tq_issued_expire(tq, now):
  match tq:
    case Q.TimerQueue{q, n}:
      {==}

def Laws.tq_time_cmp(a, b):
  O.tm.w64(a, b)

def Laws.tq_vec():
  {==}

def Laws.tq_wit():
  {==}
