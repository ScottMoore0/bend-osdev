# bend-osdev-textsearch, lemmas the proof files share: Bool algebra,
# absurdities, U32 and Nat equality, Nat order, lists, the reference with
# case folded out, and the byte-automaton adapter (auto.bend) unfolded a
# byte at a time and over chunks. No law is proved here.
import Base
import ./textsearch.bend as T
import ./auto.bend as A
import ./naive.bend as V

# Absurdities

def tsl.disc(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def tsl.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : tsl.disc(_)
  Unit{}

# from False == True, anything
def tsl.absurd(-X: Type, -x: X, -y: X, +e: {False{} == True{} : Bool}) -> {x == y : X}:
  Empty.absurd({x == y : X}, tsl.ft(e))

def tsl.absurd_tf(-X: Type, -x: X, -y: X, +e: {True{} == False{} : Bool}) -> {x == y : X}:
  Empty.absurd({x == y : X}, tsl.ft(Equal.sym(Bool, True{}, False{}, e)))

# Bool algebra

def tsl.and_true_r(+a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def tsl.and_false_r(+a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def tsl.or_false_r(+a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def tsl.and_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def tsl.or_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# a and b is True: a is True, and b is True
def tsl.and_l(+a: Bool, -b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      tsl.absurd(Bool, False{}, True{}, e)

def tsl.and_r(+a: Bool, +b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      tsl.absurd(Bool, b, True{}, e)

# U32: is_eq is equality

def tsl.bool_cmp_self(+b: Bool) -> {Bool.cmp(b, b) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tsl.word_cmp_self(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+b, t}:
          Equal.trans(Cmp, Word.cmp.fin(b, b, Word.cmp(p, t, t)), Word.cmp.fin(b, b, EQ{}), EQ{}, Equal.cong(Cmp, Cmp, x => Word.cmp.fin(b, b, x), Word.cmp(p, t, t), EQ{}, tsl.word_cmp_self(p, t)), tsl.bool_cmp_self(b))

def tsl.u32_refl(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{+w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, tsl.word_cmp_self(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

def tsl.word_eq_tail(c: Cmp, x: Bool, y: Bool, e: {Cmp.is_eq(Word.cmp.fin(x, y, c)) == True{} : Bool}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, tsl.ft(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, tsl.ft(e))

def tsl.word_eq_head(c: Cmp, x: Bool, y: Bool, e: {Cmp.is_eq(Word.cmp.fin(x, y, c)) == True{} : Bool}) -> {x == y : Bool}:
  match c:
    case LT{}:
      Empty.absurd({x == y : Bool}, tsl.ft(e))
    case EQ{}:
      match x y:
        case True{} True{}:
          {==}
        case False{} False{}:
          {==}
        case True{} False{}:
          Empty.absurd({True{} == False{} : Bool}, tsl.ft(e))
        case False{} True{}:
          Empty.absurd({False{} == True{} : Bool}, tsl.ft(e))
    case GT{}:
      Empty.absurd({x == y : Bool}, tsl.ft(e))

def tsl.word_eq(n: Nat, a: Word(n), b: Word(n), e: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          +e2 = e
          %tsl.word_eq(p, at, bt, tsl.word_eq_tail(Word.cmp(p, at, bt), x, y, e2)) : {WCon{x, at} == WCon{y, _} : Word(1n+p)}
          %tsl.word_eq_head(Word.cmp(p, at, bt), x, y, e2) : {WCon{x, at} == WCon{_, at} : Word(1n+p)}
          {==}

# is_eq(a, b) is True: a is b
def tsl.u32_eq(a: U32, b: U32, e: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+wa} U32{+wb}:
      %tsl.word_eq(32n, wa, wb, e) : {U32{wa} == U32{_} : U32}
      {==}

# Nat

def tsl.add_zero(+m: Nat) -> {Nat.add(m, 0n) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      %tsl.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def tsl.add_succ(+x: Nat, -y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %tsl.add_succ(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

def tsl.add_one(+a: Nat) -> {Nat.add(a, 1n) == 1n+a : Nat}:
  Equal.trans(Nat, Nat.add(a, 1n), 1n+Nat.add(a, 0n), 1n+a, tsl.add_succ(a, 0n), Equal.cong(Nat, Nat, n => 1n+n, Nat.add(a, 0n), a, tsl.add_zero(a)))

def tsl.lt_succ(+a: Nat) -> {Nat.is_lt(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      tsl.lt_succ(p)

def tsl.lt_zero(+x: Nat) -> {Nat.is_lt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# x < 0 is never True
def tsl.lt_zero_abs(-X: Type, -u: X, -v: X, +x: Nat, +h: {Nat.is_lt(x, 0n) == True{} : Bool}) -> {u == v : X}:
  tsl.absurd(X, u, v, Equal.trans(Bool, False{}, Nat.is_lt(x, 0n), True{}, Equal.sym(Bool, Nat.is_lt(x, 0n), False{}, tsl.lt_zero(x)), h))

# a < b and b < c + 1: a < c
def tsl.lt_le_trans(+a: Nat, +b: Nat, +c: Nat, +h1: {Nat.is_lt(a, b) == True{} : Bool}, +h2: {Nat.is_lt(b, 1n+c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          tsl.absurd(Bool, Nat.is_lt(0n, c), True{}, h1)
        case 1n+bp:
          match c:
            case 0n:
              tsl.lt_zero_abs(Bool, Nat.is_lt(0n, 0n), True{}, bp, h2)
            case 1n+cp:
              {==}
    case 1n+ap:
      match b:
        case 0n:
          tsl.absurd(Bool, Nat.is_lt(1n+ap, c), True{}, h1)
        case 1n+bp:
          match c:
            case 0n:
              tsl.lt_zero_abs(Bool, Nat.is_lt(1n+ap, 0n), True{}, bp, h2)
            case 1n+cp:
              tsl.lt_le_trans(ap, bp, cp, h1, h2)

# a < n: a < n + 1
def tsl.lt_weak(+a: Nat, +n: Nat, +h: {Nat.is_lt(a, n) == True{} : Bool}) -> {Nat.is_lt(a, 1n+n) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      match n:
        case 0n:
          tsl.absurd(Bool, Nat.is_lt(1n+ap, 1n), True{}, h)
        case 1n+np:
          tsl.lt_weak(ap, np, h)

# a < a + 1 + l
def tsl.lt_add(+a: Nat, +l: Nat) -> {Nat.is_lt(a, Nat.add(a, 1n+l)) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      tsl.lt_add(ap, l)

def tsl.sub_zero(+a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      {==}

# a < b + 1, and a is not b: a < b
def tsl.lt_succ_ne(+a: Nat, +b: Nat, +h1: {Nat.is_lt(a, 1n+b) == True{} : Bool}, +h2: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      tsl.absurd_tf(Bool, Nat.is_lt(0n, 0n), True{}, h2)
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      tsl.lt_zero_abs(Bool, Nat.is_lt(1n+ap, 0n), True{}, ap, h1)
    case 1n+ap 1n+bp:
      tsl.lt_succ_ne(ap, bp, h1, h2)

# a < b + 1, and not a < b: a is b
def tsl.lt_succ_eq(+a: Nat, +b: Nat, +h1: {Nat.is_lt(a, 1n+b) == True{} : Bool}, +h2: {Nat.is_lt(a, b) == False{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      tsl.absurd_tf(Nat, 0n, 1n+bp, h2)
    case 1n+ap 0n:
      tsl.lt_zero_abs(Nat, 1n+ap, 0n, ap, h1)
    case 1n+ap 1n+bp:
      %tsl.lt_succ_eq(ap, bp, h1, h2) : {1n+ap == 1n+_ : Nat}
      {==}

# is_eq(a, b) is True: a is b
def tsl.nat_eq(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      tsl.absurd(Nat, 0n, 1n+q, h)
    case 1n+p 0n:
      tsl.absurd(Nat, 1n+p, 0n, h)
    case 1n+p 1n+q:
      %tsl.nat_eq(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

def tsl.nat_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      tsl.nat_refl(p)

# Lists

def tsl.app_nil(xs: List<&2, Nat>) -> {List.append(&2, Nat, xs, Nil{}) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %tsl.app_nil(t) : {Con{h, List.append(&2, Nat, t, Nil{})} == Con{h, _} : List<&2, Nat>}
      {==}

def tsl.app_assoc(xs: List<&2, Nat>, +ys: List<&2, Nat>, +zs: List<&2, Nat>) -> {List.append(&2, Nat, List.append(&2, Nat, xs, ys), zs) == List.append(&2, Nat, xs, List.append(&2, Nat, ys, zs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %tsl.app_assoc(t, ys, zs) : {Con{h, List.append(&2, Nat, List.append(&2, Nat, t, ys), zs)} == Con{h, _} : List<&2, Nat>}
      {==}

def tsl.take0(xs: List<&2, U32>) -> {List.take(&2, U32, xs, 0n) == Nil{} : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      {==}

# a hit, then more ends
def tsl.hit_app(+h: Bool, +e: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {List.append(&2, Nat, V.ts.naive.hit(h, e, xs), ys) == V.ts.naive.hit(h, e, List.append(&2, Nat, xs, ys)) : List<&2, Nat>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

# the length of the folded bytes
def tsl.fold_len(+icase: Bool, xs: List<&2, U32>) -> {List.length(&2, U32, T.ts.fold_all(icase, xs)) == List.length(&2, U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{c, t}:
      %tsl.fold_len(icase, t) : {1n+List.length(&2, U32, T.ts.fold_all(icase, t)) == 1n+_ : Nat}
      {==}

# The reference with case folded out: ignoring case is comparing the folded
# pattern with the folded text exactly

def tsl.at_fold(+icase: Bool, p: List<&2, U32>, xs: List<&2, U32>) -> {V.ts.naive.at(icase, p, xs) == V.ts.naive.at(False{}, T.ts.fold_all(icase, p), T.ts.fold_all(icase, xs)) : Bool}:
  match p xs:
    case Nil{} _:
      {==}
    case Con{a, pt} Nil{}:
      {==}
    case Con{+a, pt} Con{+b, xt}:
      %tsl.at_fold(icase, pt, xt) : {Bool.and(U32.is_eq(T.ts.fold(icase, a), T.ts.fold(icase, b)), V.ts.naive.at(icase, pt, xt)) == Bool.and(U32.is_eq(T.ts.fold(icase, a), T.ts.fold(icase, b)), _) : Bool}
      {==}

def tsl.go_fold(+icase: Bool, +p: List<&2, U32>, +m: Nat, xs: List<&2, U32>, +pos: Nat) -> {V.ts.naive.go(icase, p, m, xs, pos) == V.ts.naive.go(False{}, T.ts.fold_all(icase, p), m, T.ts.fold_all(icase, xs), pos) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      %tsl.at_fold(icase, p, Con{c, t}) : {V.ts.naive.hit(V.ts.naive.at(icase, p, Con{c, t}), Nat.add(pos, m), V.ts.naive.go(icase, p, m, t, 1n+pos)) == V.ts.naive.hit(_, Nat.add(pos, m), V.ts.naive.go(False{}, T.ts.fold_all(icase, p), m, T.ts.fold_all(icase, t), 1n+pos)) : List<&2, Nat>}
      %tsl.go_fold(icase, p, m, t, 1n+pos) : {V.ts.naive.hit(V.ts.naive.at(icase, p, Con{c, t}), Nat.add(pos, m), V.ts.naive.go(icase, p, m, t, 1n+pos)) == V.ts.naive.hit(V.ts.naive.at(icase, p, Con{c, t}), Nat.add(pos, m), _) : List<&2, Nat>}
      {==}

# The byte-automaton adapter

# a hit, then the outcome r
def tsl.cons_snd(~S: Data, h: Bool, +e: Nat, r: S & List<&2, Nat>) -> {A.ts.auto.snd(~S, A.ts.auto.cons(~S, h, e, r)) == A.ts.auto.hit(h, e, A.ts.auto.snd(~S, r)) : List<&2, Nat>}:
  match r:
    case (s, ms):
      {==}

# a pending step, then ys: the pending hit, then ys fed from its state
def tsl.go_snd(~S: Data, ~step: S -> U32 -> S & Bool, ys: List<&2, U32>, +pos: Nat, +s: S, +h: Bool) -> {A.ts.auto.snd(~S, A.ts.auto.go(~S, ~step, ys, pos, (s, h))) == A.ts.auto.hit(h, pos, A.ts.auto.snd(~S, A.ts.auto.feed(~S, ~step, s, pos, ys))) : List<&2, Nat>}:
  match ys:
    case Nil{}:
      {==}
    case Con{c, t}:
      tsl.cons_snd(~S, h, pos, A.ts.auto.go(~S, ~step, t, 1n+pos, step(s, c)))

# The adapter over chunks (as PROOF.bend proves auto_split)

# a hit and then more matches: the hit first
def tsl.cons_pre(~S: Data, h: Bool, +e: Nat, r: S & List<&2, Nat>) -> {A.ts.auto.cons(~S, h, e, r) == A.ts.auto.pre(~S, A.ts.auto.hit(h, e, Nil{}), r) : S & List<&2, Nat>}:
  match h:
    case True{}:
      match r:
        case (s, ms):
          {==}
    case False{}:
      match r:
        case (s, ms):
          {==}

def tsl.cons_pre2(~S: Data, h: Bool, +e: Nat, -m1: List<&2, Nat>, r: S & List<&2, Nat>) -> {A.ts.auto.cons(~S, h, e, A.ts.auto.pre(~S, m1, r)) == A.ts.auto.pre(~S, A.ts.auto.hit(h, e, m1), r) : S & List<&2, Nat>}:
  match h:
    case True{}:
      match r:
        case (s, m2):
          {==}
    case False{}:
      match r:
        case (s, m2):
          {==}

def tsl.cons_then(~S: Data, ~step: S -> U32 -> S & Bool, h: Bool, +e: Nat, x: S & List<&2, Nat>, +p: Nat, +ys: List<&2, U32>) -> {A.ts.auto.cons(~S, h, e, A.ts.auto.then(~S, ~step, x, p, ys)) == A.ts.auto.then(~S, ~step, A.ts.auto.cons(~S, h, e, x), p, ys) : S & List<&2, Nat>}:
  match x:
    case (s1, m1):
      tsl.cons_pre2(~S, h, e, m1, A.ts.auto.feed(~S, ~step, s1, p, ys))

def tsl.pre_nil(~S: Data, r: S & List<&2, Nat>) -> {A.ts.auto.pre(~S, Nil{}, r) == r : S & List<&2, Nat>}:
  match r:
    case (s, m):
      {==}

# a pending step, then ys: the pending hit, then ys fed from its state
def tsl.go_nil(~S: Data, ~step: S -> U32 -> S & Bool, ys: List<&2, U32>, +pos: Nat, +s: S, +h: Bool) -> {A.ts.auto.go(~S, ~step, ys, pos, (s, h)) == A.ts.auto.pre(~S, A.ts.auto.hit(h, pos, Nil{}), A.ts.auto.feed(~S, ~step, s, pos, ys)) : S & List<&2, Nat>}:
  match ys:
    case Nil{}:
      match h:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{c, t}:
      tsl.cons_pre(~S, h, pos, A.ts.auto.go(~S, ~step, t, 1n+pos, step(s, c)))

# the pending step commutes with appending
def tsl.go_app(~S: Data, ~step: S -> U32 -> S & Bool, xs: List<&2, U32>, +ys: List<&2, U32>, +pos: Nat, r: S & Bool) -> {A.ts.auto.go(~S, ~step, List.append(&2, U32, xs, ys), pos, r) == A.ts.auto.then(~S, ~step, A.ts.auto.go(~S, ~step, xs, pos, r), Nat.add(pos, List.length(&2, U32, xs)), ys) : S & List<&2, Nat>}:
  match xs:
    case Nil{}:
      match r:
        case (+s, +h):
          %Equal.sym(Nat, Nat.add(pos, 0n), pos, tsl.add_zero(pos)) : {A.ts.auto.go(~S, ~step, ys, pos, (s, h)) == A.ts.auto.then(~S, ~step, (s, A.ts.auto.hit(h, pos, Nil{})), _, ys) : S & List<&2, Nat>}
          tsl.go_nil(~S, ~step, ys, pos, s, h)
    case Con{+c, +t}:
      match r:
        case (+s, +h):
          %Equal.sym(S & List<&2, Nat>, A.ts.auto.go(~S, ~step, List.append(&2, U32, t, ys), 1n+pos, step(s, c)), A.ts.auto.then(~S, ~step, A.ts.auto.go(~S, ~step, t, 1n+pos, step(s, c)), Nat.add(1n+pos, List.length(&2, U32, t)), ys), tsl.go_app(~S, ~step, t, ys, 1n+pos, step(s, c))) : {A.ts.auto.cons(~S, h, pos, _) == A.ts.auto.then(~S, ~step, A.ts.auto.cons(~S, h, pos, A.ts.auto.go(~S, ~step, t, 1n+pos, step(s, c))), Nat.add(pos, 1n+List.length(&2, U32, t)), ys) : S & List<&2, Nat>}
          %Equal.sym(Nat, Nat.add(pos, 1n+List.length(&2, U32, t)), 1n+Nat.add(pos, List.length(&2, U32, t)), tsl.add_succ(pos, List.length(&2, U32, t))) : {A.ts.auto.cons(~S, h, pos, A.ts.auto.then(~S, ~step, A.ts.auto.go(~S, ~step, t, 1n+pos, step(s, c)), 1n+Nat.add(pos, List.length(&2, U32, t)), ys)) == A.ts.auto.then(~S, ~step, A.ts.auto.cons(~S, h, pos, A.ts.auto.go(~S, ~step, t, 1n+pos, step(s, c))), _, ys) : S & List<&2, Nat>}
          tsl.cons_then(~S, ~step, h, pos, A.ts.auto.go(~S, ~step, t, 1n+pos, step(s, c)), 1n+Nat.add(pos, List.length(&2, U32, t)), ys)

# feeding xs ++ ys: xs, then ys from where xs ended
def tsl.feed_app(~S: Data, ~step: S -> U32 -> S & Bool, +s: S, +pos: Nat, xs: List<&2, U32>, +ys: List<&2, U32>) -> {A.ts.auto.feed(~S, ~step, s, pos, List.append(&2, U32, xs, ys)) == A.ts.auto.then(~S, ~step, A.ts.auto.feed(~S, ~step, s, pos, xs), Nat.add(pos, List.length(&2, U32, xs)), ys) : S & List<&2, Nat>}:
  match xs:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(pos, 0n), pos, tsl.add_zero(pos)) : {A.ts.auto.feed(~S, ~step, s, pos, ys) == A.ts.auto.then(~S, ~step, (s, Nil{}), _, ys) : S & List<&2, Nat>}
      Equal.sym(S & List<&2, Nat>, A.ts.auto.pre(~S, Nil{}, A.ts.auto.feed(~S, ~step, s, pos, ys)), A.ts.auto.feed(~S, ~step, s, pos, ys), tsl.pre_nil(~S, A.ts.auto.feed(~S, ~step, s, pos, ys)))
    case Con{+c, +t}:
      %Equal.sym(Nat, Nat.add(pos, 1n+List.length(&2, U32, t)), 1n+Nat.add(pos, List.length(&2, U32, t)), tsl.add_succ(pos, List.length(&2, U32, t))) : {A.ts.auto.go(~S, ~step, List.append(&2, U32, t, ys), 1n+pos, step(s, c)) == A.ts.auto.then(~S, ~step, A.ts.auto.go(~S, ~step, t, 1n+pos, step(s, c)), _, ys) : S & List<&2, Nat>}
      tsl.go_app(~S, ~step, t, ys, 1n+pos, step(s, c))

# Any chunks: the matches of the bytes of all of them

def tsl.snd_pre(~S: Data, -m1: List<&2, Nat>, r: S & List<&2, Nat>) -> {A.ts.auto.snd(~S, A.ts.auto.pre(~S, m1, r)) == List.append(&2, Nat, m1, A.ts.auto.snd(~S, r)) : List<&2, Nat>}:
  match r:
    case (s, m2):
      {==}

def tsl.split_k(~S: Data, ~step: S -> U32 -> S & Bool, r: S & List<&2, Nat>, +t: List<&2, List<&2, U32>>, +p: Nat, +m0: List<&2, Nat>, ih: @s1:S -> @m1:List<&2, Nat> -> {T.ts.run.go(~S, ~(s1 => p => xs => A.ts.auto.feed(~S, ~step, s1, p, xs)), t, p, (s1, m1)) == List.append(&2, Nat, m1, A.ts.auto.snd(~S, A.ts.auto.feed(~S, ~step, s1, p, T.ts.concat(t)))) : List<&2, Nat>}) -> {List.append(&2, Nat, m0, T.ts.run.go(~S, ~(s1 => p => xs => A.ts.auto.feed(~S, ~step, s1, p, xs)), t, p, r)) == List.append(&2, Nat, m0, A.ts.auto.snd(~S, A.ts.auto.then(~S, ~step, r, p, T.ts.concat(t)))) : List<&2, Nat>}:
  match r:
    case (+s1, +m1):
      %Equal.sym(List<&2, Nat>, A.ts.auto.snd(~S, A.ts.auto.pre(~S, m1, A.ts.auto.feed(~S, ~step, s1, p, T.ts.concat(t)))), List.append(&2, Nat, m1, A.ts.auto.snd(~S, A.ts.auto.feed(~S, ~step, s1, p, T.ts.concat(t)))), tsl.snd_pre(~S, m1, A.ts.auto.feed(~S, ~step, s1, p, T.ts.concat(t)))) : {List.append(&2, Nat, m0, T.ts.run.go(~S, ~(s1 => p => xs => A.ts.auto.feed(~S, ~step, s1, p, xs)), t, p, (s1, m1))) == List.append(&2, Nat, m0, _) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, T.ts.run.go(~S, ~(s1 => p => xs => A.ts.auto.feed(~S, ~step, s1, p, xs)), t, p, (s1, m1)), List.append(&2, Nat, m1, A.ts.auto.snd(~S, A.ts.auto.feed(~S, ~step, s1, p, T.ts.concat(t)))), ih(s1, m1)) : {List.append(&2, Nat, m0, _) == List.append(&2, Nat, m0, List.append(&2, Nat, m1, A.ts.auto.snd(~S, A.ts.auto.feed(~S, ~step, s1, p, T.ts.concat(t))))) : List<&2, Nat>}
      {==}

def tsl.split(~S: Data, ~step: S -> U32 -> S & Bool, cs: List<&2, List<&2, U32>>, +pos: Nat, +s: S, +m0: List<&2, Nat>) -> {T.ts.run.go(~S, ~(s1 => p => xs => A.ts.auto.feed(~S, ~step, s1, p, xs)), cs, pos, (s, m0)) == List.append(&2, Nat, m0, A.ts.auto.snd(~S, A.ts.auto.feed(~S, ~step, s, pos, T.ts.concat(cs)))) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      Equal.sym(List<&2, Nat>, List.append(&2, Nat, m0, Nil{}), m0, tsl.app_nil(m0))
    case Con{+c, +t}:
      +p = Nat.add(pos, List.length(&2, U32, c))
      %Equal.sym(S & List<&2, Nat>, A.ts.auto.feed(~S, ~step, s, pos, List.append(&2, U32, c, T.ts.concat(t))), A.ts.auto.then(~S, ~step, A.ts.auto.feed(~S, ~step, s, pos, c), p, T.ts.concat(t)), tsl.feed_app(~S, ~step, s, pos, c, T.ts.concat(t))) : {List.append(&2, Nat, m0, T.ts.run.go(~S, ~(s1 => p => xs => A.ts.auto.feed(~S, ~step, s1, p, xs)), t, p, A.ts.auto.feed(~S, ~step, s, pos, c))) == List.append(&2, Nat, m0, A.ts.auto.snd(~S, _)) : List<&2, Nat>}
      tsl.split_k(~S, ~step, A.ts.auto.feed(~S, ~step, s, pos, c), t, p, m0, s1 => m1 => tsl.split(~S, ~step, t, p, s1, m1))


# Nat: subtraction and order

def tsl.sub_self(+a: Nat) -> {Nat.sub(a, a) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      tsl.sub_self(p)

# b <= a: (a + 1) - b is (a - b) + 1
def tsl.sub_succ_le(+a: Nat, +b: Nat, +h: {Nat.is_lt(b, 1n+a) == True{} : Bool}) -> {Nat.sub(1n+a, b) == 1n+Nat.sub(a, b) : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          tsl.lt_zero_abs(Nat, Nat.sub(1n, 1n+bp), 1n+Nat.sub(0n, 1n+bp), bp, h)
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          tsl.sub_succ_le(ap, bp, h)

# a <= b: a + (b - a) is b
def tsl.add_sub(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, 1n+b) == True{} : Bool}) -> {Nat.add(a, Nat.sub(b, a)) == b : Nat}:
  match a:
    case 0n:
      tsl.sub_zero(b)
    case 1n+ap:
      match b:
        case 0n:
          tsl.lt_zero_abs(Nat, Nat.add(1n+ap, Nat.sub(0n, 1n+ap)), 0n, ap, h)
        case 1n+bp:
          %tsl.add_sub(ap, bp, h) : {1n+Nat.add(ap, Nat.sub(bp, ap)) == 1n+_ : Nat}
          {==}

# a - b <= a
def tsl.sub_le(+a: Nat, +b: Nat) -> {Nat.is_lt(Nat.sub(a, b), 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ap:
      match b:
        case 0n:
          tsl.lt_succ(ap)
        case 1n+bp:
          tsl.lt_weak(Nat.sub(ap, bp), 1n+ap, tsl.sub_le(ap, bp))

def tsl.lt_irrefl(+a: Nat) -> {Nat.is_lt(a, a) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      tsl.lt_irrefl(p)

def tsl.lt_trans(+a: Nat, +b: Nat, +c: Nat, +h1: {Nat.is_lt(a, b) == True{} : Bool}, +h2: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  tsl.lt_le_trans(a, b, c, h1, tsl.lt_weak(b, c, h2))

# a < b: a is not b
def tsl.lt_ne(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          tsl.absurd(Bool, True{}, False{}, h)
        case 1n+bp:
          {==}
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          tsl.lt_ne(ap, bp, h)

# not a < b, and a is not b: b < a
def tsl.nlt_ne(+a: Nat, +b: Nat, +h1: {Nat.is_lt(a, b) == False{} : Bool}, +h2: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          tsl.absurd_tf(Bool, Nat.is_lt(0n, 0n), True{}, h2)
        case 1n+bp:
          tsl.absurd_tf(Bool, Nat.is_lt(1n+bp, 0n), True{}, h1)
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          tsl.nlt_ne(ap, bp, h1, h2)

# not a < b: b < a + 1
def tsl.nlt_le(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_lt(b, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          tsl.absurd_tf(Bool, Nat.is_lt(1n+bp, 1n), True{}, h)
    case 1n+ap:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          tsl.nlt_le(ap, bp, h)

# a < b + 1: not b < a
def tsl.le_nlt(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, 1n+b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a:
    case 0n:
      tsl.lt_zero(b)
    case 1n+ap:
      match b:
        case 0n:
          tsl.lt_zero_abs(Bool, Nat.is_lt(0n, 1n+ap), False{}, ap, h)
        case 1n+bp:
          tsl.le_nlt(ap, bp, h)

def tsl.max_zero(+y: Nat) -> {Nat.max(y, 0n) == y : Nat}:
  match y:
    case 0n:
      {==}
    case 1n+p:
      {==}

# m > 0: (m - 1) + 1 is m
def tsl.succ_pred(+m: Nat, +h: {Nat.is_lt(0n, m) == True{} : Bool}) -> {1n+Nat.sub(m, 1n) == m : Nat}:
  match m:
    case 0n:
      tsl.absurd(Nat, 1n, 0n, h)
    case 1n+ +k:
      %Equal.sym(Nat, Nat.sub(k, 0n), k, tsl.sub_zero(k)) : {1n+_ == 1n+k : Nat}
      {==}

# j <= a: a - (a - j) is j
def tsl.sub_sub(+a: Nat, +j: Nat, +h: {Nat.is_lt(j, 1n+a) == True{} : Bool}) -> {Nat.sub(a, Nat.sub(a, j)) == j : Nat}:
  match a:
    case 0n:
      match j:
        case 0n:
          {==}
        case 1n+ +i:
          tsl.lt_zero_abs(Nat, 0n, 1n+i, i, h)
    case 1n+ +k:
      match j:
        case 0n:
          tsl.sub_self(k)
        case 1n+ +i:
          %Equal.sym(Nat, Nat.sub(1n+k, Nat.sub(k, i)), 1n+Nat.sub(k, Nat.sub(k, i)), tsl.sub_succ_le(k, Nat.sub(k, i), tsl.sub_le(k, i))) : {_ == 1n+i : Nat}
          %Equal.sym(Nat, Nat.sub(k, Nat.sub(k, i)), i, tsl.sub_sub(k, i, h)) : {1n+_ == 1n+i : Nat}
          {==}

# 0 < i <= a: a - i < a
def tsl.sub_lt(+a: Nat, +i: Nat, +h1: {Nat.is_lt(0n, i) == True{} : Bool}, +h2: {Nat.is_lt(i, 1n+a) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(a, i), a) == True{} : Bool}:
  match a:
    case 0n:
      match i:
        case 0n:
          tsl.absurd(Bool, Nat.is_lt(0n, 0n), True{}, h1)
        case 1n+ +j:
          tsl.lt_zero_abs(Bool, Nat.is_lt(0n, 0n), True{}, j, h2)
    case 1n+ +k:
      match i:
        case 0n:
          tsl.absurd(Bool, Nat.is_lt(1n+k, 1n+k), True{}, h1)
        case 1n+ +j:
          tsl.sub_le(k, j)

# b1 <= b2: a - b2 <= a - b1
def tsl.sub_mono(+b1: Nat, +b2: Nat, +a: Nat, +h: {Nat.is_lt(b1, 1n+b2) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(a, b2), 1n+Nat.sub(a, b1)) == True{} : Bool}:
  match b1:
    case 0n:
      %Equal.sym(Nat, Nat.sub(a, 0n), a, tsl.sub_zero(a)) : {Nat.is_lt(Nat.sub(a, b2), 1n+_) == True{} : Bool}
      tsl.sub_le(a, b2)
    case 1n+ +c1:
      match b2:
        case 0n:
          tsl.lt_zero_abs(Bool, Nat.is_lt(Nat.sub(a, 0n), 1n+Nat.sub(a, 1n+c1)), True{}, c1, h)
        case 1n+ +c2:
          match a:
            case 0n:
              {==}
            case 1n+ +k:
              tsl.sub_mono(c1, c2, k, h)

# a < b: not b <= a
def tsl.lt_nle(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(b, 1n+a) == False{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          tsl.absurd(Bool, True{}, False{}, h)
        case 1n+ +j:
          tsl.lt_zero(j)
    case 1n+ +k:
      match b:
        case 0n:
          tsl.absurd(Bool, True{}, False{}, h)
        case 1n+ +j:
          tsl.lt_nle(k, j, h)

# a + b < c: a < c
def tsl.lt_add_l(+a: Nat, +b: Nat, +c: Nat, +h: {Nat.is_lt(Nat.add(a, b), c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a:
    case 0n:
      match c:
        case 0n:
          tsl.lt_zero_abs(Bool, False{}, True{}, b, h)
        case 1n+ +k:
          {==}
    case 1n+ +j:
      match c:
        case 0n:
          tsl.absurd(Bool, False{}, True{}, h)
        case 1n+ +k:
          tsl.lt_add_l(j, b, k, h)
