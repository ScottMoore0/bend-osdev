# Proof helpers for bend-osdev-maple: every leaf stays at the same depth.
#
# A node of height 0 is a leaf, one of height h + 1 a chain whose children
# have height h (level). A strong node (Maple.leveled.go) is also nonempty
# when it is a chain; a weak one (wn) may be the empty chain. MapleNode.cons
# leaves out empty children, so a chain built by it has only strong
# children. Joining two trees at their own heights, cutting a tree, and so
# storing and erasing keep every leaf at depth height.
import Base
import ./model.bend as M
import ./node.bend as N
import ./tree.bend as T
import ./maple.bend as X
import ./proof_order.bend as O

def Nd(-V: Data) -> Data:
  N.MapleNode<U32, V>

def Tr(-V: Data) -> Data:
  N.MapleTree<U32, V>

def lv(-V: Data, n: Nd(V), +h: Nat) -> Bool:
  N.MapleNode.level(U32, V, n, h)

def isleaf(-V: Data, n: Nd(V)) -> Bool:
  N.MapleNode.is_leaf(U32, V, n)

def ischain(-V: Data, n: Nd(V)) -> Bool:
  N.MapleNode.is_chain(U32, V, n)

# a strong node of height h
def sn(-V: Data, +h: Nat, +n: Nd(V)) -> Bool:
  X.Maple.leveled.go(U32, V, h, n)

# a weak node of height h
def wn(-V: Data, +h: Nat, n: Nd(V)) -> Bool:
  match h:
    case 0n:
      isleaf(V, n)
    case 1n+g:
      lv(V, n, g)

def tl(-V: Data, t: Tr(V)) -> Bool:
  X.Maple.leveled(U32, V, t)

def troot(-V: Data, t: Tr(V)) -> Nd(V):
  match t:
    case N.MapleTree{o, h, n}:
      n

# a leveled tree, or an empty one
def tle(-V: Data, +t: Tr(V)) -> Bool:
  Bool.or(N.MapleNode.is_empty(U32, V, troot(V, t)), tl(V, t))

def or_true_r(x: Bool, -y: Bool, +e: {y == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      e

def sw(-V: Data, +h: Nat, +n: Nd(V), +s: {sn(V, h, n) == True{} : Bool}) -> {wn(V, h, n) == True{} : Bool}:
  match h:
    case 0n:
      s
    case 1n+g:
      O.bo.and_r(ischain(V, n), lv(V, n, g), s)

# the parts of a leveled chain
def lv.c(-V: Data, +h: Nat, +p: U32, +c: Nd(V), +r: Nd(V), +e: {lv(V, N.MapleSlot{p, c, r}, h) == True{} : Bool}) -> {sn(V, h, c) == True{} : Bool}:
  match h:
    case 0n:
      O.bo.and_l(isleaf(V, c), lv(V, r, 0n), e)
    case 1n+(+g):
      O.bo.and_intro(ischain(V, c), lv(V, c, g), O.bo.and_l(ischain(V, c), Bool.and(lv(V, c, g), lv(V, r, 1n+g)), e), O.bo.and_l(lv(V, c, g), lv(V, r, 1n+g), O.bo.and_r(ischain(V, c), Bool.and(lv(V, c, g), lv(V, r, 1n+g)), e)))

def lv.r(-V: Data, +h: Nat, +p: U32, +c: Nd(V), +r: Nd(V), +e: {lv(V, N.MapleSlot{p, c, r}, h) == True{} : Bool}) -> {lv(V, r, h) == True{} : Bool}:
  match h:
    case 0n:
      O.bo.and_r(isleaf(V, c), lv(V, r, 0n), e)
    case 1n+(+g):
      O.bo.and_r(lv(V, c, g), lv(V, r, 1n+g), O.bo.and_r(ischain(V, c), Bool.and(lv(V, c, g), lv(V, r, 1n+g)), e))

def lv.intro(-V: Data, +h: Nat, +p: U32, +c: Nd(V), +r: Nd(V), +ec: {sn(V, h, c) == True{} : Bool}, +er: {lv(V, r, h) == True{} : Bool}) -> {lv(V, N.MapleSlot{p, c, r}, h) == True{} : Bool}:
  match h:
    case 0n:
      O.bo.and_intro(isleaf(V, c), lv(V, r, 0n), ec, er)
    case 1n+(+g):
      O.bo.and_intro(ischain(V, c), Bool.and(lv(V, c, g), lv(V, r, 1n+g)), O.bo.and_l(ischain(V, c), lv(V, c, g), ec), O.bo.and_intro(lv(V, c, g), lv(V, r, 1n+g), O.bo.and_r(ischain(V, c), lv(V, c, g), ec), er))

# a leveled chain with a last key is nonempty
def chain.of(-V: Data, c: Nd(V), +g: Nat, -p: U32, +e: {lv(V, c, g) == True{} : Bool}, +em: {N.MapleNode.last_key(U32, V, c) == Some{p} : Maybe<&2, U32>}) -> {ischain(V, c) == True{} : Bool}:
  match c:
    case N.MapleSlot{q, d, r}:
      {==}
    case N.MapleNil{}:
      Empty.absurd({False{} == True{} : Bool}, O.ab.none_some(U32, p, em))
    case N.MapleLeaf{es}:
      Empty.absurd({False{} == True{} : Bool}, O.ab.ft(e))

def weak.strong(-V: Data, +h: Nat, +c: Nd(V), -p: U32, +w: {wn(V, h, c) == True{} : Bool}, +em: {N.MapleNode.last_key(U32, V, c) == Some{p} : Maybe<&2, U32>}) -> {sn(V, h, c) == True{} : Bool}:
  match h:
    case 0n:
      w
    case 1n+(+g):
      O.bo.and_intro(ischain(V, c), lv(V, c, g), chain.of(V, c, g, p, w, em), w)

def lv.cons.go(-V: Data, m: Maybe<&2, U32>, +h: Nat, +c: Nd(V), +r: Nd(V), +em: {N.MapleNode.last_key(U32, V, c) == m : Maybe<&2, U32>}, +w: {wn(V, h, c) == True{} : Bool}, +er: {lv(V, r, h) == True{} : Bool}) -> {lv(V, N.MapleNode.cons.go(U32, V, m, c, r), h) == True{} : Bool}:
  match m:
    case None{}:
      er
    case Some{+p}:
      lv.intro(V, h, p, c, r, weak.strong(V, h, c, p, w, em), er)

def lv.cons(-V: Data, +h: Nat, +c: Nd(V), +r: Nd(V), +w: {wn(V, h, c) == True{} : Bool}, +er: {lv(V, r, h) == True{} : Bool}) -> {lv(V, N.MapleNode.cons(U32, V, c, r), h) == True{} : Bool}:
  lv.cons.go(V, N.MapleNode.last_key(U32, V, c), h, c, r, {==}, w, er)

def lv.append(-V: Data, x: Nd(V), +y: Nd(V), +h: Nat, +ex: {lv(V, x, h) == True{} : Bool}, +ey: {lv(V, y, h) == True{} : Bool}) -> {lv(V, N.MapleNode.append(U32, V, x, y), h) == True{} : Bool}:
  match x:
    case N.MapleLeaf{es}:
      Empty.absurd({lv(V, N.MapleNode.append(U32, V, N.MapleLeaf{es}, y), h) == True{} : Bool}, O.ab.ft(ex))
    case N.MapleNil{}:
      ey
    case N.MapleSlot{+p, +c, +r}:
      lv.intro(V, h, p, c, N.MapleNode.append(U32, V, r, y), lv.c(V, h, p, c, r, ex), lv.append(V, r, y, h, lv.r(V, h, p, c, r, ex), ey))

def lv.take(-V: Data, n: Nd(V), k: Nat, +h: Nat, +e: {lv(V, n, h) == True{} : Bool}) -> {lv(V, N.MapleNode.take(U32, V, n, k), h) == True{} : Bool}:
  match n:
    case N.MapleLeaf{es}:
      Empty.absurd({False{} == True{} : Bool}, O.ab.ft(e))
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      match k:
        case 0n:
          {==}
        case 1n+(+j):
          lv.intro(V, h, p, c, N.MapleNode.take(U32, V, r, j), lv.c(V, h, p, c, r, e), lv.take(V, r, j, h, lv.r(V, h, p, c, r, e)))

def lv.drop(-V: Data, n: Nd(V), k: Nat, +h: Nat, +e: {lv(V, n, h) == True{} : Bool}) -> {lv(V, N.MapleNode.drop(U32, V, n, k), h) == True{} : Bool}:
  match n:
    case N.MapleLeaf{es}:
      Empty.absurd({False{} == True{} : Bool}, O.ab.ft(e))
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      match k:
        case 0n:
          e
        case 1n+(+j):
          lv.drop(V, r, j, h, lv.r(V, h, p, c, r, e))

def wn.take(+h: Nat, -V: Data, n: Nd(V), +k: Nat, +e: {wn(V, h, n) == True{} : Bool}) -> {wn(V, h, N.MapleNode.take(U32, V, n, k)) == True{} : Bool}:
  match h:
    case 0n:
      match n:
        case N.MapleLeaf{es}:
          {==}
        case N.MapleNil{}:
          Empty.absurd({False{} == True{} : Bool}, O.ab.ft(e))
        case N.MapleSlot{p, c, r}:
          Empty.absurd({isleaf(V, N.MapleNode.take(U32, V, N.MapleSlot{p, c, r}, k)) == True{} : Bool}, O.ab.ft(e))
    case 1n+(+g):
      lv.take(V, n, k, g, e)

def wn.drop(+h: Nat, -V: Data, n: Nd(V), +k: Nat, +e: {wn(V, h, n) == True{} : Bool}) -> {wn(V, h, N.MapleNode.drop(U32, V, n, k)) == True{} : Bool}:
  match h:
    case 0n:
      match n:
        case N.MapleLeaf{es}:
          {==}
        case N.MapleNil{}:
          Empty.absurd({False{} == True{} : Bool}, O.ab.ft(e))
        case N.MapleSlot{p, c, r}:
          Empty.absurd({isleaf(V, N.MapleNode.drop(U32, V, N.MapleSlot{p, c, r}, k)) == True{} : Bool}, O.ab.ft(e))
    case 1n+(+g):
      lv.drop(V, n, k, g, e)

def wn.merge(+h: Nat, -V: Data, x: Nd(V), y: Nd(V), +ex: {wn(V, h, x) == True{} : Bool}, +ey: {wn(V, h, y) == True{} : Bool}) -> {wn(V, h, N.MapleNode.merge(U32, V, x, y)) == True{} : Bool}:
  match h:
    case 0n:
      match x:
        case N.MapleLeaf{es}:
          match y:
            case N.MapleLeaf{fs}:
              {==}
            case N.MapleNil{}:
              Empty.absurd({True{} == True{} : Bool}, O.ab.ft(ey))
            case N.MapleSlot{q, d, s}:
              Empty.absurd({wn(V, 0n, N.MapleNode.cons(U32, V, N.MapleLeaf{es}, N.MapleSlot{q, d, s})) == True{} : Bool}, O.ab.ft(ey))
        case N.MapleNil{}:
          ey
        case N.MapleSlot{p, c, r}:
          Empty.absurd({wn(V, 0n, N.MapleNode.append(U32, V, N.MapleSlot{p, c, r}, y)) == True{} : Bool}, O.ab.ft(ex))
    case 1n+(+g):
      match x:
        case N.MapleLeaf{es}:
          Empty.absurd({wn(V, 1n+g, N.MapleNode.merge(U32, V, N.MapleLeaf{es}, y)) == True{} : Bool}, O.ab.ft(ex))
        case N.MapleNil{}:
          ey
        case N.MapleSlot{+p, +c, +r}:
          lv.append(V, N.MapleSlot{p, c, r}, y, g, ex, ey)

def lv.fit.go(-V: Data, over: Bool, +h: Nat, +n: Nd(V), +k: Nat, +w: {wn(V, h, n) == True{} : Bool}) -> {lv(V, N.MapleNode.fit.go(U32, V, over, n, k), h) == True{} : Bool}:
  match over:
    case False{}:
      lv.cons(V, h, n, N.MapleNil{}, w, {==})
    case True{}:
      lv.cons(V, h, N.MapleNode.take(U32, V, n, k), N.MapleNode.cons(U32, V, N.MapleNode.drop(U32, V, n, k), N.MapleNil{}), wn.take(h, V, n, k, w), lv.cons(V, h, N.MapleNode.drop(U32, V, n, k), N.MapleNil{}, wn.drop(h, V, n, k, w), {==}))

# fit turns a node of height h into a chain of nodes of height h
def lv.fit(-V: Data, +h: Nat, +o: Nat, +n: Nd(V), +w: {wn(V, h, n) == True{} : Bool}) -> {lv(V, N.MapleNode.fit(U32, V, o, n), h) == True{} : Bool}:
  lv.fit.go(V, Nat.is_lt(o, N.MapleNode.count(U32, V, n)), h, n, N.MapleNode.half(N.MapleNode.count(U32, V, n)), w)

def lv.init.go(-V: Data, n: Nd(V), +p: U32, +c: Nd(V), +h: Nat, +e: {lv(V, N.MapleSlot{p, c, n}, h) == True{} : Bool}) -> {lv(V, N.MapleNode.init.go(U32, V, n, p, c), h) == True{} : Bool}:
  match n:
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+q, +d, +r}:
      lv.intro(V, h, p, c, N.MapleNode.init.go(U32, V, r, q, d), lv.c(V, h, p, c, N.MapleSlot{q, d, r}, e), lv.init.go(V, r, q, d, h, lv.r(V, h, p, c, N.MapleSlot{q, d, r}, e)))
    case N.MapleLeaf{+es}:
      lv.intro(V, h, p, c, N.MapleNil{}, lv.c(V, h, p, c, N.MapleLeaf{es}, e), {==})

def lv.init(-V: Data, n: Nd(V), +h: Nat, +e: {lv(V, n, h) == True{} : Bool}) -> {lv(V, N.MapleNode.init(U32, V, n), h) == True{} : Bool}:
  match n:
    case N.MapleLeaf{es}:
      {==}
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      lv.init.go(V, r, p, c, h, e)

def sn.last.go(-V: Data, n: Nd(V), +c: Nd(V), +h: Nat, +ec: {sn(V, h, c) == True{} : Bool}, +en: {lv(V, n, h) == True{} : Bool}) -> {sn(V, h, N.MapleNode.last.go(U32, V, n, c)) == True{} : Bool}:
  match n:
    case N.MapleNil{}:
      ec
    case N.MapleSlot{+q, +d, +r}:
      sn.last.go(V, r, d, h, lv.c(V, h, q, d, r, en), lv.r(V, h, q, d, r, en))
    case N.MapleLeaf{es}:
      Empty.absurd({sn(V, h, N.MapleLeaf{es}) == True{} : Bool}, O.ab.ft(en))

# the last child of a nonempty leveled chain is a strong node
def sn.last(-V: Data, n: Nd(V), +h: Nat, +ec: {ischain(V, n) == True{} : Bool}, +e: {lv(V, n, h) == True{} : Bool}) -> {sn(V, h, N.MapleNode.last(U32, V, n)) == True{} : Bool}:
  match n:
    case N.MapleLeaf{es}:
      Empty.absurd({sn(V, h, N.MapleLeaf{es}) == True{} : Bool}, O.ab.ft(ec))
    case N.MapleNil{}:
      Empty.absurd({sn(V, h, N.MapleNil{}) == True{} : Bool}, O.ab.ft(ec))
    case N.MapleSlot{+p, +c, +r}:
      sn.last.go(V, r, c, h, lv.c(V, h, p, c, r, e), lv.r(V, h, p, c, r, e))

def sn.first(-V: Data, n: Nd(V), +h: Nat, +ec: {ischain(V, n) == True{} : Bool}, +e: {lv(V, n, h) == True{} : Bool}) -> {sn(V, h, N.MapleNode.first(U32, V, n)) == True{} : Bool}:
  match n:
    case N.MapleLeaf{es}:
      Empty.absurd({sn(V, h, N.MapleLeaf{es}) == True{} : Bool}, O.ab.ft(ec))
    case N.MapleNil{}:
      Empty.absurd({sn(V, h, N.MapleNil{}) == True{} : Bool}, O.ab.ft(ec))
    case N.MapleSlot{+p, +c, +r}:
      lv.c(V, h, p, c, r, e)

def lv.tail(-V: Data, n: Nd(V), +h: Nat, +e: {lv(V, n, h) == True{} : Bool}) -> {lv(V, N.MapleNode.tail(U32, V, n), h) == True{} : Bool}:
  match n:
    case N.MapleLeaf{es}:
      {==}
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      lv.r(V, h, p, c, r, e)

# joining at the right edge: a strong n1 of height d + h2 and a weak n2 of
# height h2 make a chain of nodes of height d + h2
def lv.jr(-V: Data, d: Nat, +h2: Nat, +n1: Nd(V), +n2: Nd(V), +o: Nat, +s1: {sn(V, Nat.add(d, h2), n1) == True{} : Bool}, +w2: {wn(V, h2, n2) == True{} : Bool}) -> {lv(V, T.MapleTree.join_right(U32, V, d, n1, n2, o), Nat.add(d, h2)) == True{} : Bool}:
  match d:
    case 0n:
      lv.fit(V, h2, o, N.MapleNode.merge(U32, V, n1, n2), wn.merge(h2, V, n1, n2, sw(V, h2, n1, s1), w2))
    case 1n+(+e):
      +ch = O.bo.and_l(ischain(V, n1), lv(V, n1, Nat.add(e, h2)), s1)
      +l1 = O.bo.and_r(ischain(V, n1), lv(V, n1, Nat.add(e, h2)), s1)
      lv.fit(V, 1n+Nat.add(e, h2), o, N.MapleNode.append(U32, V, N.MapleNode.init(U32, V, n1), T.MapleTree.join_right(U32, V, e, N.MapleNode.last(U32, V, n1), n2, o)), lv.append(V, N.MapleNode.init(U32, V, n1), T.MapleTree.join_right(U32, V, e, N.MapleNode.last(U32, V, n1), n2, o), Nat.add(e, h2), lv.init(V, n1, Nat.add(e, h2), l1), lv.jr(V, e, h2, N.MapleNode.last(U32, V, n1), n2, o, sn.last(V, n1, Nat.add(e, h2), ch, l1), w2)))

def lv.jl(-V: Data, d: Nat, +h1: Nat, +n1: Nd(V), +n2: Nd(V), +o: Nat, +w1: {wn(V, h1, n1) == True{} : Bool}, +s2: {sn(V, Nat.add(d, h1), n2) == True{} : Bool}) -> {lv(V, T.MapleTree.join_left(U32, V, d, n1, n2, o), Nat.add(d, h1)) == True{} : Bool}:
  match d:
    case 0n:
      lv.fit(V, h1, o, N.MapleNode.merge(U32, V, n1, n2), wn.merge(h1, V, n1, n2, w1, sw(V, h1, n2, s2)))
    case 1n+(+e):
      +ch = O.bo.and_l(ischain(V, n2), lv(V, n2, Nat.add(e, h1)), s2)
      +l2 = O.bo.and_r(ischain(V, n2), lv(V, n2, Nat.add(e, h1)), s2)
      lv.fit(V, 1n+Nat.add(e, h1), o, N.MapleNode.append(U32, V, T.MapleTree.join_left(U32, V, e, n1, N.MapleNode.first(U32, V, n2), o), N.MapleNode.tail(U32, V, n2)), lv.append(V, T.MapleTree.join_left(U32, V, e, n1, N.MapleNode.first(U32, V, n2), o), N.MapleNode.tail(U32, V, n2), Nat.add(e, h1), lv.jl(V, e, h1, n1, N.MapleNode.first(U32, V, n2), o, w1, sn.first(V, n2, Nat.add(e, h1), ch, l2)), lv.tail(V, n2, Nat.add(e, h1), l2)))

# a strong node of height h is a leveled tree once normalised
def tl.norm_sn(-V: Data, h: Nat, n: Nd(V), +o: Nat, +s: {sn(V, h, n) == True{} : Bool}) -> {tl(V, T.MapleTree.norm(U32, V, h, n, o)) == True{} : Bool}:
  match h:
    case 0n:
      s
    case 1n+(+g):
      match n:
        case N.MapleSlot{+p, +c, r}:
          match r:
            case N.MapleNil{}:
              tl.norm_sn(V, g, c, o, lv.c(V, g, p, c, N.MapleNil{}, O.bo.and_r(ischain(V, N.MapleSlot{p, c, N.MapleNil{}}), lv(V, N.MapleSlot{p, c, N.MapleNil{}}, g), s)))
            case N.MapleLeaf{es}:
              s
            case N.MapleSlot{q, d, t}:
              s
        case N.MapleNil{}:
          {==}
        case N.MapleLeaf{es}:
          Empty.absurd({tl(V, N.MapleTree{o, 1n+g, N.MapleLeaf{es}}) == True{} : Bool}, O.ab.ft(s))

# a chain of nodes of height h is a leveled tree of height h + 1, normalised
def tl.norm(-V: Data, +h: Nat, c: Nd(V), +o: Nat, +e: {lv(V, c, h) == True{} : Bool}) -> {tl(V, T.MapleTree.norm(U32, V, 1n+h, c, o)) == True{} : Bool}:
  match c:
    case N.MapleSlot{+p, +ch, r}:
      match r:
        case N.MapleNil{}:
          tl.norm_sn(V, h, ch, o, lv.c(V, h, p, ch, N.MapleNil{}, e))
        case N.MapleLeaf{es}:
          e
        case N.MapleSlot{q, d, t}:
          e
    case N.MapleNil{}:
      {==}
    case N.MapleLeaf{es}:
      Empty.absurd({tl(V, N.MapleTree{o, 1n+h, N.MapleLeaf{es}}) == True{} : Bool}, O.ab.ft(e))

# Heights: the taller tree's height is the shorter's plus their difference

def nt.sub_add(a: Nat, b: Nat, +e: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.add(Nat.sub(a, b), b) == a : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.add(0n, 1n+q) == 0n : Nat}, O.ab.ft(e))
    case 1n+p 0n:
      O.nt.add_zero(1n+p)
    case 1n+(+p) 1n+(+q):
      %Equal.sym(Nat, Nat.add(Nat.sub(p, q), 1n+q), 1n+Nat.add(Nat.sub(p, q), q), O.nt.add_succ(Nat.sub(p, q), q)) : {_ == 1n+p : Nat}
      %nt.sub_add(p, q, e) : {1n+Nat.add(Nat.sub(p, q), q) == 1n+_ : Nat}
      {==}

def nt.le_flip(+a: Nat, +b: Nat, +e: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(b, a), O.cm.flip(Nat.cmp(a, b)), O.nt.flip(a, b)) : {Cmp.is_le(_) == True{} : Bool}
  O.cm.le_of_lt(O.cm.flip(Nat.cmp(a, b)), O.cm.lt_flip(Nat.cmp(a, b), e))

def sn.rw(-V: Data, -x: Nat, -y: Nat, +n: Nd(V), +e: {x == y : Nat}, +s: {sn(V, y, n) == True{} : Bool}) -> {sn(V, x, n) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {sn(V, _, n) == True{} : Bool}
  s

def lv.rw(-V: Data, -x: Nat, -y: Nat, +n: Nd(V), +e: {x == y : Nat}, +s: {lv(V, n, x) == True{} : Bool}) -> {lv(V, n, y) == True{} : Bool}:
  %e : {lv(V, n, _) == True{} : Bool}
  s

# Joining keeps every leaf at depth height

def tlj.tall(right: Bool, -V: Data, +h1: Nat, +n1: Nd(V), +h2: Nat, +n2: Nd(V), +o: Nat, +s1: {sn(V, h1, n1) == True{} : Bool}, +s2: {sn(V, h2, n2) == True{} : Bool}, +er: {Nat.is_le(h2, h1) == right : Bool}) -> {tl(V, T.MapleTree.join.tall(U32, V, right, h1, n1, h2, n2, o)) == True{} : Bool}:
  match right:
    case True{}:
      +sa = nt.sub_add(h1, h2, er)
      tl.norm(V, h1, T.MapleTree.join_right(U32, V, Nat.sub(h1, h2), n1, n2, o), o, lv.rw(V, Nat.add(Nat.sub(h1, h2), h2), h1, T.MapleTree.join_right(U32, V, Nat.sub(h1, h2), n1, n2, o), sa, lv.jr(V, Nat.sub(h1, h2), h2, n1, n2, o, sn.rw(V, Nat.add(Nat.sub(h1, h2), h2), h1, n1, sa, s1), sw(V, h2, n2, s2))))
    case False{}:
      +sa = nt.sub_add(h2, h1, nt.le_flip(h2, h1, er))
      tl.norm(V, h2, T.MapleTree.join_left(U32, V, Nat.sub(h2, h1), n1, n2, o), o, lv.rw(V, Nat.add(Nat.sub(h2, h1), h1), h2, T.MapleTree.join_left(U32, V, Nat.sub(h2, h1), n1, n2, o), sa, lv.jl(V, Nat.sub(h2, h1), h1, n1, n2, o, sw(V, h1, n1, s1), sn.rw(V, Nat.add(Nat.sub(h2, h1), h1), h2, n2, sa, s2))))

def or_false_l(x: Bool, -y: Bool, +ex: {x == False{} : Bool}, +e: {Bool.or(x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      Empty.absurd({y == True{} : Bool}, O.ab.tf(ex))
    case False{}:
      e

def or_true_l(x: Bool, -y: Bool, +e: {x == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({y == True{} : Bool}, O.ab.ft(e))

def tlj.go(e1: Bool, e2: Bool, -V: Data, +o: Nat, +h1: Nat, +n1: Nd(V), +h2: Nat, +n2: Nd(V), +q1: {N.MapleNode.is_empty(U32, V, n1) == e1 : Bool}, +q2: {N.MapleNode.is_empty(U32, V, n2) == e2 : Bool}, +a1: {Bool.or(N.MapleNode.is_empty(U32, V, n1), sn(V, h1, n1)) == True{} : Bool}, +a2: {sn(V, h2, n2) == True{} : Bool}) -> {tl(V, T.MapleTree.join.go(U32, V, e1, e2, o, h1, n1, h2, n2)) == True{} : Bool}:
  match e1:
    case True{}:
      a2
    case False{}:
      match e2:
        case True{}:
          or_false_l(N.MapleNode.is_empty(U32, V, n1), sn(V, h1, n1), q1, a1)
        case False{}:
          tlj.tall(Nat.is_le(h2, h1), V, h1, n1, h2, n2, o, or_false_l(N.MapleNode.is_empty(U32, V, n1), sn(V, h1, n1), q1, a1), a2, {==})

# a leveled (or empty) tree joined with a leveled tree is leveled
def tl.join(-V: Data, t1: Tr(V), t2: Tr(V), +a1: {tle(V, t1) == True{} : Bool}, +a2: {tl(V, t2) == True{} : Bool}) -> {tl(V, T.MapleTree.join(U32, V, t1, t2)) == True{} : Bool}:
  match t1:
    case N.MapleTree{+o1, +h1, +n1}:
      match t2:
        case N.MapleTree{+o2, +h2, +n2}:
          tlj.go(N.MapleNode.is_empty(U32, V, n1), N.MapleNode.is_empty(U32, V, n2), V, o1, h1, n1, h2, n2, {==}, {==}, a1, a2)

# Cutting keeps every leaf at depth height

def pre_ok(-V: Data, h: Nat, pre: Nd(V)) -> Bool:
  match h:
    case 0n:
      N.MapleNode.is_empty(U32, V, pre)
    case 1n+g:
      lv(V, pre, g)

def pre_ok.nil(-V: Data, h: Nat) -> {pre_ok(V, h, N.MapleNil{}) == True{} : Bool}:
  match h:
    case 0n:
      {==}
    case 1n+g:
      {==}

def tle.norm(-V: Data, h: Nat, +pre: Nd(V), +o: Nat, +pp: {pre_ok(V, h, pre) == True{} : Bool}) -> {tle(V, T.MapleTree.norm(U32, V, h, pre, o)) == True{} : Bool}:
  match h:
    case 0n:
      or_true_l(N.MapleNode.is_empty(U32, V, pre), isleaf(V, pre), pp)
    case 1n+(+g):
      or_true_r(N.MapleNode.is_empty(U32, V, troot(V, T.MapleTree.norm(U32, V, 1n+g, pre, o))), tl(V, T.MapleTree.norm(U32, V, 1n+g, pre, o)), tl.norm(V, g, pre, o, pp))

def tle.of(-V: Data, +t: Tr(V), +e: {tl(V, t) == True{} : Bool}) -> {tle(V, t) == True{} : Bool}:
  or_true_r(N.MapleNode.is_empty(U32, V, troot(V, t)), tl(V, t), e)

def lo(-V: Data, n: Nd(V), h: Nat, +a: U32, pre: Nd(V), c: Cmp, +o: Nat) -> Tr(V):
  T.MapleTree.lo(~U32, ~U32.cmp, ~M.MapleKey32.dec, V, n, h, a, pre, c, o)

def hi(-V: Data, n: Nd(V), h: Nat, +b: U32, c: Cmp, +o: Nat) -> Tr(V):
  T.MapleTree.hi(~U32, ~U32.cmp, ~M.MapleKey32.inc, V, n, h, b, c, o)

def probe(-V: Data, n: Nd(V), +i: U32) -> Cmp:
  N.MapleNode.probe(~U32, ~U32.cmp, V, n, i)

def tl.lo(-V: Data, n: Nd(V), +h: Nat, +a: U32, +pre: Nd(V), c: Cmp, +o: Nat, +w: {wn(V, h, n) == True{} : Bool}, +pp: {pre_ok(V, h, pre) == True{} : Bool}) -> {tl(V, lo(V, n, h, a, pre, c, o)) == True{} : Bool}:
  match n:
    case N.MapleSlot{+p, +ch, +r}:
      match h:
        case 0n:
          Empty.absurd({tl(V, lo(V, N.MapleSlot{p, ch, r}, 0n, a, pre, c, o)) == True{} : Bool}, O.ab.ft(w))
        case 1n+(+g):
          match c:
            case LT{}:
              tl.lo(V, r, 1n+g, a, N.MapleNode.append(U32, V, pre, N.MapleSlot{p, ch, N.MapleNil{}}), probe(V, r, a), o, lv.r(V, g, p, ch, r, w), lv.append(V, pre, N.MapleSlot{p, ch, N.MapleNil{}}, g, pp, lv.intro(V, g, p, ch, N.MapleNil{}, lv.c(V, g, p, ch, r, w), {==})))
            case EQ{}:
              tl.join(V, T.MapleTree.norm(U32, V, 1n+g, pre, o), lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o), tle.norm(V, 1n+g, pre, o, pp), tl.lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o, sw(V, g, ch, lv.c(V, g, p, ch, r, w)), pre_ok.nil(V, g)))
            case GT{}:
              tl.join(V, T.MapleTree.norm(U32, V, 1n+g, pre, o), lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o), tle.norm(V, 1n+g, pre, o, pp), tl.lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o, sw(V, g, ch, lv.c(V, g, p, ch, r, w)), pre_ok.nil(V, g)))
    case N.MapleNil{}:
      match h:
        case 0n:
          Empty.absurd({isleaf(V, pre) == True{} : Bool}, O.ab.ft(w))
        case 1n+(+g):
          tl.norm(V, g, pre, o, pp)
    case N.MapleLeaf{+es}:
      tl.join(V, T.MapleTree.norm(U32, V, h, pre, o), N.MapleTree{o, 0n, N.MapleLeaf{M.MapleModel.below(~U32, ~U32.cmp, ~M.MapleKey32.dec, V, es, a)}}, tle.norm(V, h, pre, o, pp), {==})

def tl.hi(-V: Data, n: Nd(V), +h: Nat, +b: U32, c: Cmp, +o: Nat, +w: {wn(V, h, n) == True{} : Bool}) -> {tl(V, hi(V, n, h, b, c, o)) == True{} : Bool}:
  match n:
    case N.MapleSlot{+p, +ch, +r}:
      match h:
        case 0n:
          {==}
        case 1n+(+g):
          match c:
            case GT{}:
              tl.join(V, hi(V, ch, g, b, probe(V, ch, b), o), T.MapleTree.norm(U32, V, 1n+g, r, o), tle.of(V, hi(V, ch, g, b, probe(V, ch, b), o), tl.hi(V, ch, g, b, probe(V, ch, b), o, sw(V, g, ch, lv.c(V, g, p, ch, r, w)))), tl.norm(V, g, r, o, lv.r(V, g, p, ch, r, w)))
            case LT{}:
              tl.hi(V, r, 1n+g, b, probe(V, r, b), o, lv.r(V, g, p, ch, r, w))
            case EQ{}:
              tl.hi(V, r, 1n+g, b, probe(V, r, b), o, lv.r(V, g, p, ch, r, w))
    case N.MapleNil{}:
      {==}
    case N.MapleLeaf{es}:
      {==}

# Storing and erasing keep every leaf at depth height

def tsr.go(-V: Data, ok: Bool, +t: Tr(V), +a: U32, +b: U32, +v: V) -> Tr(V):
  X.Maple.set_range.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, ok, t, a, b, v)

def tcr.go(-V: Data, ok: Bool, +t: Tr(V), +a: U32, +b: U32) -> Tr(V):
  X.Maple.clear_range.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, ok, t, a, b)

def single(-V: Data, +o: Nat, +a: U32, +b: U32, +v: V) -> Tr(V):
  N.MapleTree{o, 0n, N.MapleLeaf{[M.MapleEntry{a, b, v}]}}

def tlsr.go(ok: Bool, -V: Data, +t: Tr(V), +a: U32, +b: U32, +v: V, +e: {tl(V, t) == True{} : Bool}) -> {tl(V, tsr.go(V, ok, t, a, b, v)) == True{} : Bool}:
  match ok:
    case True{}:
      match t:
        case N.MapleTree{+o, +h, +root}:
          tl.join(V, T.MapleTree.join(U32, V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v)), hi(V, root, h, b, probe(V, root, b), o), tle.of(V, T.MapleTree.join(U32, V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v)), tl.join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v), tle.of(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), tl.lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o, sw(V, h, root, e), pre_ok.nil(V, h))), {==})), tl.hi(V, root, h, b, probe(V, root, b), o, sw(V, h, root, e)))
    case False{}:
      e

def tlcr.go(ok: Bool, -V: Data, +t: Tr(V), +a: U32, +b: U32, +e: {tl(V, t) == True{} : Bool}) -> {tl(V, tcr.go(V, ok, t, a, b)) == True{} : Bool}:
  match ok:
    case True{}:
      match t:
        case N.MapleTree{+o, +h, +root}:
          tl.join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), hi(V, root, h, b, probe(V, root, b), o), tle.of(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), tl.lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o, sw(V, h, root, e), pre_ok.nil(V, h))), tl.hi(V, root, h, b, probe(V, root, b), o, sw(V, h, root, e)))
    case False{}:
      e

def tl.set_range(-V: Data, +t: Tr(V), +a: U32, +b: U32, +v: V, +e: {tl(V, t) == True{} : Bool}) -> {tl(V, X.Maple32.set_range(V, t, a, b, v)) == True{} : Bool}:
  tlsr.go(O.ule(a, b), V, t, a, b, v, e)

def tl.clear_range(-V: Data, +t: Tr(V), +a: U32, +b: U32, +e: {tl(V, t) == True{} : Bool}) -> {tl(V, X.Maple32.clear_range(V, t, a, b)) == True{} : Bool}:
  tlcr.go(O.ule(a, b), V, t, a, b, e)

def tl.erase.go(-V: Data, m: Maybe<&2, M.MapleEntry<U32, V>>, +t: Tr(V), +e: {tl(V, t) == True{} : Bool}) -> {tl(V, X.Maple.erase.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, m, t)) == True{} : Bool}:
  match m:
    case None{}:
      e
    case Some{M.MapleEntry{+f, +l, +v}}:
      tl.clear_range(V, t, f, l, e)

def tl.erase(-V: Data, +t: Tr(V), +i: U32, +e: {tl(V, t) == True{} : Bool}) -> {tl(V, X.Maple32.erase(V, t, i)) == True{} : Bool}:
  tl.erase.go(V, X.Maple32.lookup(V, t, i), t, e)
