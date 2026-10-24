# Proofs of bend-osdev-textsearch's laws. The automaton laws go by induction
# on the bytes: the adapter's pending step (auto.bend's ts.auto.go) commutes
# with appending more bytes. The bounded laws and the vectors are closed
# computations.
import Base
import ./textsearch.bend as T
import ./auto.bend as A
import ./kmp.bend as K
import ./fsm.bend as F
import ./LAWS.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP

# Nat and lists

def pr.app_nil(xs: List<&2, Nat>) -> {List.append(&2, Nat, xs, Nil{}) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %pr.app_nil(t) : {Con{h, List.append(&2, Nat, t, Nil{})} == Con{h, _} : List<&2, Nat>}
      {==}

# The adapter's pieces

# a hit and then more matches: the hit first
def pr.cons_pre(~S: Data, h: Bool, +e: Nat, r: S & List<&2, Nat>) -> {A.ts.auto.cons(~S, h, e, r) == A.ts.auto.pre(~S, A.ts.auto.hit(h, e, Nil{}), r) : S & List<&2, Nat>}:
  match h:
    case True{}:
      match r:
        case (s, ms):
          {==}
    case False{}:
      match r:
        case (s, ms):
          {==}

def pr.cons_pre2(~S: Data, h: Bool, +e: Nat, -m1: List<&2, Nat>, r: S & List<&2, Nat>) -> {A.ts.auto.cons(~S, h, e, A.ts.auto.pre(~S, m1, r)) == A.ts.auto.pre(~S, A.ts.auto.hit(h, e, m1), r) : S & List<&2, Nat>}:
  match h:
    case True{}:
      match r:
        case (s, m2):
          {==}
    case False{}:
      match r:
        case (s, m2):
          {==}

def pr.cons_then(~S: Data, ~step: S -> U32 -> S & Bool, h: Bool, +e: Nat, x: S & List<&2, Nat>, +p: Nat, +ys: List<&2, U32>) -> {A.ts.auto.cons(~S, h, e, A.ts.auto.then(~S, ~step, x, p, ys)) == A.ts.auto.then(~S, ~step, A.ts.auto.cons(~S, h, e, x), p, ys) : S & List<&2, Nat>}:
  match x:
    case (s1, m1):
      pr.cons_pre2(~S, h, e, m1, A.ts.auto.feed(~S, ~step, s1, p, ys))

def pr.pre_nil(~S: Data, r: S & List<&2, Nat>) -> {A.ts.auto.pre(~S, Nil{}, r) == r : S & List<&2, Nat>}:
  match r:
    case (s, m):
      {==}

# a pending step, then ys: the pending hit, then ys fed from its state
def pr.go_nil(~S: Data, ~step: S -> U32 -> S & Bool, ys: List<&2, U32>, +pos: Nat, +s: S, +h: Bool) -> {A.ts.auto.go(~S, ~step, ys, pos, (s, h)) == A.ts.auto.pre(~S, A.ts.auto.hit(h, pos, Nil{}), A.ts.auto.feed(~S, ~step, s, pos, ys)) : S & List<&2, Nat>}:
  match ys:
    case Nil{}:
      match h:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{c, t}:
      pr.cons_pre(~S, h, pos, A.ts.auto.go(~S, ~step, t, 1n+pos, step(s, c)))

# the pending step commutes with appending
def pr.go_app(~S: Data, ~step: S -> U32 -> S & Bool, xs: List<&2, U32>, +ys: List<&2, U32>, +pos: Nat, r: S & Bool) -> {A.ts.auto.go(~S, ~step, List.append(&2, U32, xs, ys), pos, r) == A.ts.auto.then(~S, ~step, A.ts.auto.go(~S, ~step, xs, pos, r), Nat.add(pos, List.length(&2, U32, xs)), ys) : S & List<&2, Nat>}:
  match xs:
    case Nil{}:
      match r:
        case (+s, +h):
          %Equal.sym(Nat, Nat.add(pos, 0n), pos, UL.nat_add_zero(pos)) : {A.ts.auto.go(~S, ~step, ys, pos, (s, h)) == A.ts.auto.then(~S, ~step, (s, A.ts.auto.hit(h, pos, Nil{})), _, ys) : S & List<&2, Nat>}
          pr.go_nil(~S, ~step, ys, pos, s, h)
    case Con{+c, +t}:
      match r:
        case (+s, +h):
          %Equal.sym(S & List<&2, Nat>, A.ts.auto.go(~S, ~step, List.append(&2, U32, t, ys), 1n+pos, step(s, c)), A.ts.auto.then(~S, ~step, A.ts.auto.go(~S, ~step, t, 1n+pos, step(s, c)), Nat.add(1n+pos, List.length(&2, U32, t)), ys), pr.go_app(~S, ~step, t, ys, 1n+pos, step(s, c))) : {A.ts.auto.cons(~S, h, pos, _) == A.ts.auto.then(~S, ~step, A.ts.auto.cons(~S, h, pos, A.ts.auto.go(~S, ~step, t, 1n+pos, step(s, c))), Nat.add(pos, 1n+List.length(&2, U32, t)), ys) : S & List<&2, Nat>}
          %Equal.sym(Nat, Nat.add(pos, 1n+List.length(&2, U32, t)), 1n+Nat.add(pos, List.length(&2, U32, t)), UL.nat_add_succ(pos, List.length(&2, U32, t))) : {A.ts.auto.cons(~S, h, pos, A.ts.auto.then(~S, ~step, A.ts.auto.go(~S, ~step, t, 1n+pos, step(s, c)), 1n+Nat.add(pos, List.length(&2, U32, t)), ys)) == A.ts.auto.then(~S, ~step, A.ts.auto.cons(~S, h, pos, A.ts.auto.go(~S, ~step, t, 1n+pos, step(s, c))), _, ys) : S & List<&2, Nat>}
          pr.cons_then(~S, ~step, h, pos, A.ts.auto.go(~S, ~step, t, 1n+pos, step(s, c)), 1n+Nat.add(pos, List.length(&2, U32, t)), ys)

# feeding xs ++ ys: xs, then ys from where xs ended
def pr.feed_app(~S: Data, ~step: S -> U32 -> S & Bool, +s: S, +pos: Nat, xs: List<&2, U32>, +ys: List<&2, U32>) -> {A.ts.auto.feed(~S, ~step, s, pos, List.append(&2, U32, xs, ys)) == A.ts.auto.then(~S, ~step, A.ts.auto.feed(~S, ~step, s, pos, xs), Nat.add(pos, List.length(&2, U32, xs)), ys) : S & List<&2, Nat>}:
  match xs:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(pos, 0n), pos, UL.nat_add_zero(pos)) : {A.ts.auto.feed(~S, ~step, s, pos, ys) == A.ts.auto.then(~S, ~step, (s, Nil{}), _, ys) : S & List<&2, Nat>}
      Equal.sym(S & List<&2, Nat>, A.ts.auto.pre(~S, Nil{}, A.ts.auto.feed(~S, ~step, s, pos, ys)), A.ts.auto.feed(~S, ~step, s, pos, ys), pr.pre_nil(~S, A.ts.auto.feed(~S, ~step, s, pos, ys)))
    case Con{+c, +t}:
      %Equal.sym(Nat, Nat.add(pos, 1n+List.length(&2, U32, t)), 1n+Nat.add(pos, List.length(&2, U32, t)), UL.nat_add_succ(pos, List.length(&2, U32, t))) : {A.ts.auto.go(~S, ~step, List.append(&2, U32, t, ys), 1n+pos, step(s, c)) == A.ts.auto.then(~S, ~step, A.ts.auto.go(~S, ~step, t, 1n+pos, step(s, c)), _, ys) : S & List<&2, Nat>}
      pr.go_app(~S, ~step, t, ys, 1n+pos, step(s, c))

def Laws.auto_append(S, step, s, pos, xs, ys):
  pr.feed_app(~S, ~step, s, pos, xs, ys)

# Any chunks: the matches of the bytes of all of them

def pr.snd_pre(~S: Data, -m1: List<&2, Nat>, r: S & List<&2, Nat>) -> {A.ts.auto.snd(~S, A.ts.auto.pre(~S, m1, r)) == List.append(&2, Nat, m1, A.ts.auto.snd(~S, r)) : List<&2, Nat>}:
  match r:
    case (s, m2):
      {==}

def pr.split_k(~S: Data, ~step: S -> U32 -> S & Bool, r: S & List<&2, Nat>, +t: List<&2, List<&2, U32>>, +p: Nat, +m0: List<&2, Nat>, ih: @s1:S -> @m1:List<&2, Nat> -> {T.ts.run.go(~S, ~(s1 => p => xs => A.ts.auto.feed(~S, ~step, s1, p, xs)), t, p, (s1, m1)) == List.append(&2, Nat, m1, A.ts.auto.snd(~S, A.ts.auto.feed(~S, ~step, s1, p, T.ts.concat(t)))) : List<&2, Nat>}) -> {List.append(&2, Nat, m0, T.ts.run.go(~S, ~(s1 => p => xs => A.ts.auto.feed(~S, ~step, s1, p, xs)), t, p, r)) == List.append(&2, Nat, m0, A.ts.auto.snd(~S, A.ts.auto.then(~S, ~step, r, p, T.ts.concat(t)))) : List<&2, Nat>}:
  match r:
    case (+s1, +m1):
      %Equal.sym(List<&2, Nat>, A.ts.auto.snd(~S, A.ts.auto.pre(~S, m1, A.ts.auto.feed(~S, ~step, s1, p, T.ts.concat(t)))), List.append(&2, Nat, m1, A.ts.auto.snd(~S, A.ts.auto.feed(~S, ~step, s1, p, T.ts.concat(t)))), pr.snd_pre(~S, m1, A.ts.auto.feed(~S, ~step, s1, p, T.ts.concat(t)))) : {List.append(&2, Nat, m0, T.ts.run.go(~S, ~(s1 => p => xs => A.ts.auto.feed(~S, ~step, s1, p, xs)), t, p, (s1, m1))) == List.append(&2, Nat, m0, _) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, T.ts.run.go(~S, ~(s1 => p => xs => A.ts.auto.feed(~S, ~step, s1, p, xs)), t, p, (s1, m1)), List.append(&2, Nat, m1, A.ts.auto.snd(~S, A.ts.auto.feed(~S, ~step, s1, p, T.ts.concat(t)))), ih(s1, m1)) : {List.append(&2, Nat, m0, _) == List.append(&2, Nat, m0, List.append(&2, Nat, m1, A.ts.auto.snd(~S, A.ts.auto.feed(~S, ~step, s1, p, T.ts.concat(t))))) : List<&2, Nat>}
      {==}

def pr.split(~S: Data, ~step: S -> U32 -> S & Bool, cs: List<&2, List<&2, U32>>, +pos: Nat, +s: S, +m0: List<&2, Nat>) -> {T.ts.run.go(~S, ~(s1 => p => xs => A.ts.auto.feed(~S, ~step, s1, p, xs)), cs, pos, (s, m0)) == List.append(&2, Nat, m0, A.ts.auto.snd(~S, A.ts.auto.feed(~S, ~step, s, pos, T.ts.concat(cs)))) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      Equal.sym(List<&2, Nat>, List.append(&2, Nat, m0, Nil{}), m0, pr.app_nil(m0))
    case Con{+c, +t}:
      +p = Nat.add(pos, List.length(&2, U32, c))
      %Equal.sym(S & List<&2, Nat>, A.ts.auto.feed(~S, ~step, s, pos, List.append(&2, U32, c, T.ts.concat(t))), A.ts.auto.then(~S, ~step, A.ts.auto.feed(~S, ~step, s, pos, c), p, T.ts.concat(t)), pr.feed_app(~S, ~step, s, pos, c, T.ts.concat(t))) : {List.append(&2, Nat, m0, T.ts.run.go(~S, ~(s1 => p => xs => A.ts.auto.feed(~S, ~step, s1, p, xs)), t, p, A.ts.auto.feed(~S, ~step, s, pos, c))) == List.append(&2, Nat, m0, A.ts.auto.snd(~S, _)) : List<&2, Nat>}
      pr.split_k(~S, ~step, A.ts.auto.feed(~S, ~step, s, pos, c), t, p, m0, s1 => m1 => pr.split(~S, ~step, t, p, s1, m1))

def Laws.auto_split(S, step, s, pos, cs):
  pr.split(~S, ~step, cs, pos, s, Nil{})

def Laws.kmp_split(icase, p, cs):
  pr.split(~K.TsKmp, ~K.ts.kmp.step, cs, 0n, K.ts.kmp.start(icase, p), Nil{})

def Laws.fsm_split(tks, cs):
  pr.split(~F.TsFsm, ~F.ts.fsm.step, cs, 0n, F.ts.fsm.start(tks), Nil{})

# The bounded laws and the vectors: closed computations

def Laws.small_plain():
  {==}

def Laws.small_plain3():
  {==}

def Laws.small_icase():
  {==}

def Laws.small_tokens():
  {==}

def Laws.small_tokens2():
  {==}

def Laws.vec_kmp():
  {==}

def Laws.vec_bm():
  {==}

def Laws.vec_fsm():
  {==}
