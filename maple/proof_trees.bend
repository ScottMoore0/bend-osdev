# Proof helpers for bend-osdev-maple: the B-tree (node.bend, tree.bend) and
# the public operations (maple.bend, gap.bend), for U32 indices, held to the
# list model.
#
# * Every restructuring (cons, append, take/drop, merge, fit, the ends of a
#   chain, norm, join) keeps the contents in order, for every node; each
#   keeps the pivots right when its inputs' are.
# * The pivot of a slot is its child's last index, so in an ordered tree a
#   child whose pivot is below an index holds only entries ending before it,
#   and the children after a slot hold only entries starting after its
#   pivot: from these, cutting (lo, hi) and every lookup follow the model.
import Base
import ./model.bend as M
import ./node.bend as N
import ./tree.bend as T
import ./maple.bend as X
import ./gap.bend as G
import ./proof_order.bend as O
import ./proof_lists.bend as P
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF_order.bend as UOP

# Shorthands for the U32 instance

def Nd(-V: Data) -> Data:
  N.MapleNode<U32, V>

def Tr(-V: Data) -> Data:
  N.MapleTree<U32, V>

def L(-V: Data, n: Nd(V)) -> P.Es(V):
  N.MapleNode.entries(U32, V, n)

def TL(-V: Data, t: Tr(V)) -> P.Es(V):
  T.MapleTree.entries(U32, V, t)

def pok(-V: Data, n: Nd(V)) -> Bool:
  N.MapleNode.pivots_ok(~U32, ~U32.cmp, V, n)

def nlk(-V: Data, n: Nd(V)) -> Maybe<&2, U32>:
  N.MapleNode.last_key(U32, V, n)

def tpok(-V: Data, t: Tr(V)) -> Bool:
  match t:
    case N.MapleTree{o, h, n}:
      pok(V, n)

# Contents through restructuring

def nd.none_empty(-V: Data, n: Nd(V), +e: {nlk(V, n) == None{} : Maybe<&2, U32>}) -> {L(V, n) == Nil{} : P.Es(V)}:
  match n:
    case N.MapleLeaf{es}:
      P.lkey.none_nil(V, es, e)
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{p, c, r}:
      Empty.absurd({P.app(V, L(V, c), L(V, r)) == Nil{} : P.Es(V)}, P.or_some.none(U32, nlk(V, r), p, e))

def nd.cons.go(-V: Data, m: Maybe<&2, U32>, +c: Nd(V), +r: Nd(V), +e: {nlk(V, c) == m : Maybe<&2, U32>}) -> {L(V, N.MapleNode.cons.go(U32, V, m, c, r)) == P.app(V, L(V, c), L(V, r)) : P.Es(V)}:
  match m:
    case None{}:
      %Equal.sym(P.Es(V), L(V, c), Nil{}, nd.none_empty(V, c, e)) : {L(V, r) == P.app(V, _, L(V, r)) : P.Es(V)}
      {==}
    case Some{p}:
      {==}

def nd.cons(-V: Data, +c: Nd(V), +r: Nd(V)) -> {L(V, N.MapleNode.cons(U32, V, c, r)) == P.app(V, L(V, c), L(V, r)) : P.Es(V)}:
  nd.cons.go(V, nlk(V, c), c, r, {==})

def nd.append(-V: Data, x: Nd(V), +y: Nd(V)) -> {L(V, N.MapleNode.append(U32, V, x, y)) == P.app(V, L(V, x), L(V, y)) : P.Es(V)}:
  match x:
    case N.MapleLeaf{+es}:
      nd.cons(V, N.MapleLeaf{es}, y)
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      %Equal.sym(P.Es(V), L(V, N.MapleNode.append(U32, V, r, y)), P.app(V, L(V, r), L(V, y)), nd.append(V, r, y)) : {P.app(V, L(V, c), _) == P.app(V, P.app(V, L(V, c), L(V, r)), L(V, y)) : P.Es(V)}
      Equal.sym(P.Es(V), P.app(V, P.app(V, L(V, c), L(V, r)), L(V, y)), P.app(V, L(V, c), P.app(V, L(V, r), L(V, y))), P.app.assoc(V, L(V, c), L(V, r), L(V, y)))

def list.take_drop(-V: Data, xs: P.Es(V), k: Nat) -> {P.app(V, List.take(&2, P.Ent(V), xs, k), List.drop(&2, P.Ent(V), xs, k)) == xs : P.Es(V)}:
  match xs k:
    case Nil{} k:
      {==}
    case Con{+h, +t} 0n:
      {==}
    case Con{+h, +t} 1n+(+j):
      %list.take_drop(V, t, j) : {Con{h, P.app(V, List.take(&2, P.Ent(V), t, j), List.drop(&2, P.Ent(V), t, j))} == Con{h, _} : P.Es(V)}
      {==}

def nd.take_drop(-V: Data, n: Nd(V), k: Nat) -> {P.app(V, L(V, N.MapleNode.take(U32, V, n, k)), L(V, N.MapleNode.drop(U32, V, n, k))) == L(V, n) : P.Es(V)}:
  match n:
    case N.MapleLeaf{+es}:
      list.take_drop(V, es, k)
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      match k:
        case 0n:
          {==}
        case 1n+(+j):
          %Equal.sym(P.Es(V), P.app(V, P.app(V, L(V, c), L(V, N.MapleNode.take(U32, V, r, j))), L(V, N.MapleNode.drop(U32, V, r, j))), P.app(V, L(V, c), P.app(V, L(V, N.MapleNode.take(U32, V, r, j)), L(V, N.MapleNode.drop(U32, V, r, j)))), P.app.assoc(V, L(V, c), L(V, N.MapleNode.take(U32, V, r, j)), L(V, N.MapleNode.drop(U32, V, r, j)))) : {_ == P.app(V, L(V, c), L(V, r)) : P.Es(V)}
          %Equal.sym(P.Es(V), P.app(V, L(V, N.MapleNode.take(U32, V, r, j)), L(V, N.MapleNode.drop(U32, V, r, j))), L(V, r), nd.take_drop(V, r, j)) : {P.app(V, L(V, c), _) == P.app(V, L(V, c), L(V, r)) : P.Es(V)}
          {==}

def nd.merge(-V: Data, x: Nd(V), y: Nd(V)) -> {L(V, N.MapleNode.merge(U32, V, x, y)) == P.app(V, L(V, x), L(V, y)) : P.Es(V)}:
  match x:
    case N.MapleLeaf{+es}:
      match y:
        case N.MapleLeaf{fs}:
          {==}
        case N.MapleNil{}:
          Equal.sym(P.Es(V), P.app(V, es, Nil{}), es, P.app.nil(V, es))
        case N.MapleSlot{+q, +d, +s}:
          nd.cons(V, N.MapleLeaf{es}, N.MapleSlot{q, d, s})
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      nd.append(V, N.MapleSlot{p, c, r}, y)

def nd.fit.go(-V: Data, over: Bool, +n: Nd(V), +k: Nat) -> {L(V, N.MapleNode.fit.go(U32, V, over, n, k)) == L(V, n) : P.Es(V)}:
  match over:
    case False{}:
      %Equal.sym(P.Es(V), L(V, N.MapleNode.cons(U32, V, n, N.MapleNil{})), P.app(V, L(V, n), Nil{}), nd.cons(V, n, N.MapleNil{})) : {_ == L(V, n) : P.Es(V)}
      P.app.nil(V, L(V, n))
    case True{}:
      %Equal.sym(P.Es(V), L(V, N.MapleNode.cons(U32, V, N.MapleNode.take(U32, V, n, k), N.MapleNode.cons(U32, V, N.MapleNode.drop(U32, V, n, k), N.MapleNil{}))), P.app(V, L(V, N.MapleNode.take(U32, V, n, k)), L(V, N.MapleNode.cons(U32, V, N.MapleNode.drop(U32, V, n, k), N.MapleNil{}))), nd.cons(V, N.MapleNode.take(U32, V, n, k), N.MapleNode.cons(U32, V, N.MapleNode.drop(U32, V, n, k), N.MapleNil{}))) : {_ == L(V, n) : P.Es(V)}
      %Equal.sym(P.Es(V), L(V, N.MapleNode.cons(U32, V, N.MapleNode.drop(U32, V, n, k), N.MapleNil{})), P.app(V, L(V, N.MapleNode.drop(U32, V, n, k)), Nil{}), nd.cons(V, N.MapleNode.drop(U32, V, n, k), N.MapleNil{})) : {P.app(V, L(V, N.MapleNode.take(U32, V, n, k)), _) == L(V, n) : P.Es(V)}
      %Equal.sym(P.Es(V), P.app(V, L(V, N.MapleNode.drop(U32, V, n, k)), Nil{}), L(V, N.MapleNode.drop(U32, V, n, k)), P.app.nil(V, L(V, N.MapleNode.drop(U32, V, n, k)))) : {P.app(V, L(V, N.MapleNode.take(U32, V, n, k)), _) == L(V, n) : P.Es(V)}
      nd.take_drop(V, n, k)

def nd.fit(-V: Data, +o: Nat, +n: Nd(V)) -> {L(V, N.MapleNode.fit(U32, V, o, n)) == L(V, n) : P.Es(V)}:
  nd.fit.go(V, Nat.is_lt(o, N.MapleNode.count(U32, V, n)), n, N.MapleNode.half(N.MapleNode.count(U32, V, n)))

def nd.ends.go(-V: Data, n: Nd(V), +p: U32, +c: Nd(V)) -> {P.app(V, L(V, N.MapleNode.init.go(U32, V, n, p, c)), L(V, N.MapleNode.last.go(U32, V, n, c))) == P.app(V, L(V, c), L(V, n)) : P.Es(V)}:
  match n:
    case N.MapleNil{}:
      Equal.sym(P.Es(V), P.app(V, L(V, c), Nil{}), L(V, c), P.app.nil(V, L(V, c)))
    case N.MapleSlot{+q, +d, +r}:
      %Equal.sym(P.Es(V), P.app(V, P.app(V, L(V, c), L(V, N.MapleNode.init.go(U32, V, r, q, d))), L(V, N.MapleNode.last.go(U32, V, r, d))), P.app(V, L(V, c), P.app(V, L(V, N.MapleNode.init.go(U32, V, r, q, d)), L(V, N.MapleNode.last.go(U32, V, r, d)))), P.app.assoc(V, L(V, c), L(V, N.MapleNode.init.go(U32, V, r, q, d)), L(V, N.MapleNode.last.go(U32, V, r, d)))) : {_ == P.app(V, L(V, c), P.app(V, L(V, d), L(V, r))) : P.Es(V)}
      %Equal.sym(P.Es(V), P.app(V, L(V, N.MapleNode.init.go(U32, V, r, q, d)), L(V, N.MapleNode.last.go(U32, V, r, d))), P.app(V, L(V, d), L(V, r)), nd.ends.go(V, r, q, d)) : {P.app(V, L(V, c), _) == P.app(V, L(V, c), P.app(V, L(V, d), L(V, r))) : P.Es(V)}
      {==}
    case N.MapleLeaf{+es}:
      %Equal.sym(P.Es(V), P.app(V, L(V, c), Nil{}), L(V, c), P.app.nil(V, L(V, c))) : {P.app(V, _, es) == P.app(V, L(V, c), es) : P.Es(V)}
      {==}

# a chain is its init, then its last child
def nd.ends(-V: Data, n: Nd(V)) -> {P.app(V, L(V, N.MapleNode.init(U32, V, n)), L(V, N.MapleNode.last(U32, V, n))) == L(V, n) : P.Es(V)}:
  match n:
    case N.MapleLeaf{es}:
      {==}
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      nd.ends.go(V, r, p, c)

# a chain is its first child, then its tail
def nd.heads(-V: Data, n: Nd(V)) -> {P.app(V, L(V, N.MapleNode.first(U32, V, n)), L(V, N.MapleNode.tail(U32, V, n))) == L(V, n) : P.Es(V)}:
  match n:
    case N.MapleLeaf{es}:
      P.app.nil(V, es)
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{p, c, r}:
      {==}

def tr.norm(-V: Data, h: Nat, n: Nd(V), +o: Nat) -> {TL(V, T.MapleTree.norm(U32, V, h, n, o)) == L(V, n) : P.Es(V)}:
  match h:
    case 0n:
      {==}
    case 1n+(+g):
      match n:
        case N.MapleSlot{p, +c, r}:
          match r:
            case N.MapleNil{}:
              Equal.trans(P.Es(V), TL(V, T.MapleTree.norm(U32, V, g, c, o)), L(V, c), P.app(V, L(V, c), Nil{}), tr.norm(V, g, c, o), Equal.sym(P.Es(V), P.app(V, L(V, c), Nil{}), L(V, c), P.app.nil(V, L(V, c))))
            case N.MapleLeaf{es}:
              {==}
            case N.MapleSlot{q, d, s}:
              {==}
        case N.MapleNil{}:
          {==}
        case N.MapleLeaf{es}:
          {==}

def tr.join_right(-V: Data, d: Nat, +n1: Nd(V), +n2: Nd(V), +o: Nat) -> {L(V, T.MapleTree.join_right(U32, V, d, n1, n2, o)) == P.app(V, L(V, n1), L(V, n2)) : P.Es(V)}:
  match d:
    case 0n:
      Equal.trans(P.Es(V), L(V, N.MapleNode.fit(U32, V, o, N.MapleNode.merge(U32, V, n1, n2))), L(V, N.MapleNode.merge(U32, V, n1, n2)), P.app(V, L(V, n1), L(V, n2)), nd.fit(V, o, N.MapleNode.merge(U32, V, n1, n2)), nd.merge(V, n1, n2))
    case 1n+(+e):
      %Equal.sym(P.Es(V), L(V, N.MapleNode.fit(U32, V, o, N.MapleNode.append(U32, V, N.MapleNode.init(U32, V, n1), T.MapleTree.join_right(U32, V, e, N.MapleNode.last(U32, V, n1), n2, o)))), L(V, N.MapleNode.append(U32, V, N.MapleNode.init(U32, V, n1), T.MapleTree.join_right(U32, V, e, N.MapleNode.last(U32, V, n1), n2, o))), nd.fit(V, o, N.MapleNode.append(U32, V, N.MapleNode.init(U32, V, n1), T.MapleTree.join_right(U32, V, e, N.MapleNode.last(U32, V, n1), n2, o)))) : {_ == P.app(V, L(V, n1), L(V, n2)) : P.Es(V)}
      %Equal.sym(P.Es(V), L(V, N.MapleNode.append(U32, V, N.MapleNode.init(U32, V, n1), T.MapleTree.join_right(U32, V, e, N.MapleNode.last(U32, V, n1), n2, o))), P.app(V, L(V, N.MapleNode.init(U32, V, n1)), L(V, T.MapleTree.join_right(U32, V, e, N.MapleNode.last(U32, V, n1), n2, o))), nd.append(V, N.MapleNode.init(U32, V, n1), T.MapleTree.join_right(U32, V, e, N.MapleNode.last(U32, V, n1), n2, o))) : {_ == P.app(V, L(V, n1), L(V, n2)) : P.Es(V)}
      %Equal.sym(P.Es(V), L(V, T.MapleTree.join_right(U32, V, e, N.MapleNode.last(U32, V, n1), n2, o)), P.app(V, L(V, N.MapleNode.last(U32, V, n1)), L(V, n2)), tr.join_right(V, e, N.MapleNode.last(U32, V, n1), n2, o)) : {P.app(V, L(V, N.MapleNode.init(U32, V, n1)), _) == P.app(V, L(V, n1), L(V, n2)) : P.Es(V)}
      %P.app.assoc(V, L(V, N.MapleNode.init(U32, V, n1)), L(V, N.MapleNode.last(U32, V, n1)), L(V, n2)) : {_ == P.app(V, L(V, n1), L(V, n2)) : P.Es(V)}
      %Equal.sym(P.Es(V), P.app(V, L(V, N.MapleNode.init(U32, V, n1)), L(V, N.MapleNode.last(U32, V, n1))), L(V, n1), nd.ends(V, n1)) : {P.app(V, _, L(V, n2)) == P.app(V, L(V, n1), L(V, n2)) : P.Es(V)}
      {==}

def tr.join_left(-V: Data, d: Nat, +n1: Nd(V), +n2: Nd(V), +o: Nat) -> {L(V, T.MapleTree.join_left(U32, V, d, n1, n2, o)) == P.app(V, L(V, n1), L(V, n2)) : P.Es(V)}:
  match d:
    case 0n:
      Equal.trans(P.Es(V), L(V, N.MapleNode.fit(U32, V, o, N.MapleNode.merge(U32, V, n1, n2))), L(V, N.MapleNode.merge(U32, V, n1, n2)), P.app(V, L(V, n1), L(V, n2)), nd.fit(V, o, N.MapleNode.merge(U32, V, n1, n2)), nd.merge(V, n1, n2))
    case 1n+(+e):
      %Equal.sym(P.Es(V), L(V, N.MapleNode.fit(U32, V, o, N.MapleNode.append(U32, V, T.MapleTree.join_left(U32, V, e, n1, N.MapleNode.first(U32, V, n2), o), N.MapleNode.tail(U32, V, n2)))), L(V, N.MapleNode.append(U32, V, T.MapleTree.join_left(U32, V, e, n1, N.MapleNode.first(U32, V, n2), o), N.MapleNode.tail(U32, V, n2))), nd.fit(V, o, N.MapleNode.append(U32, V, T.MapleTree.join_left(U32, V, e, n1, N.MapleNode.first(U32, V, n2), o), N.MapleNode.tail(U32, V, n2)))) : {_ == P.app(V, L(V, n1), L(V, n2)) : P.Es(V)}
      %Equal.sym(P.Es(V), L(V, N.MapleNode.append(U32, V, T.MapleTree.join_left(U32, V, e, n1, N.MapleNode.first(U32, V, n2), o), N.MapleNode.tail(U32, V, n2))), P.app(V, L(V, T.MapleTree.join_left(U32, V, e, n1, N.MapleNode.first(U32, V, n2), o)), L(V, N.MapleNode.tail(U32, V, n2))), nd.append(V, T.MapleTree.join_left(U32, V, e, n1, N.MapleNode.first(U32, V, n2), o), N.MapleNode.tail(U32, V, n2))) : {_ == P.app(V, L(V, n1), L(V, n2)) : P.Es(V)}
      %Equal.sym(P.Es(V), L(V, T.MapleTree.join_left(U32, V, e, n1, N.MapleNode.first(U32, V, n2), o)), P.app(V, L(V, n1), L(V, N.MapleNode.first(U32, V, n2))), tr.join_left(V, e, n1, N.MapleNode.first(U32, V, n2), o)) : {P.app(V, _, L(V, N.MapleNode.tail(U32, V, n2))) == P.app(V, L(V, n1), L(V, n2)) : P.Es(V)}
      %Equal.sym(P.Es(V), P.app(V, P.app(V, L(V, n1), L(V, N.MapleNode.first(U32, V, n2))), L(V, N.MapleNode.tail(U32, V, n2))), P.app(V, L(V, n1), P.app(V, L(V, N.MapleNode.first(U32, V, n2)), L(V, N.MapleNode.tail(U32, V, n2)))), P.app.assoc(V, L(V, n1), L(V, N.MapleNode.first(U32, V, n2)), L(V, N.MapleNode.tail(U32, V, n2)))) : {_ == P.app(V, L(V, n1), L(V, n2)) : P.Es(V)}
      %Equal.sym(P.Es(V), P.app(V, L(V, N.MapleNode.first(U32, V, n2)), L(V, N.MapleNode.tail(U32, V, n2))), L(V, n2), nd.heads(V, n2)) : {P.app(V, L(V, n1), _) == P.app(V, L(V, n1), L(V, n2)) : P.Es(V)}
      {==}


def nd.empty.go(-V: Data, m: Maybe<&2, U32>, n: Nd(V), +em: {nlk(V, n) == m : Maybe<&2, U32>}, +e: {Maybe.is_none(&2, U32, m) == True{} : Bool}) -> {L(V, n) == Nil{} : P.Es(V)}:
  match m:
    case None{}:
      nd.none_empty(V, n, em)
    case Some{p}:
      Empty.absurd({L(V, n) == Nil{} : P.Es(V)}, O.ab.ft(e))

def nd.empty_of(-V: Data, +n: Nd(V), +e: {N.MapleNode.is_empty(U32, V, n) == True{} : Bool}) -> {L(V, n) == Nil{} : P.Es(V)}:
  nd.empty.go(V, nlk(V, n), n, {==}, e)

def tr.join.tall(right: Bool, -V: Data, +h1: Nat, +n1: Nd(V), +h2: Nat, +n2: Nd(V), +o: Nat) -> {TL(V, T.MapleTree.join.tall(U32, V, right, h1, n1, h2, n2, o)) == P.app(V, L(V, n1), L(V, n2)) : P.Es(V)}:
  match right:
    case True{}:
      Equal.trans(P.Es(V), TL(V, T.MapleTree.norm(U32, V, 1n+h1, T.MapleTree.join_right(U32, V, Nat.sub(h1, h2), n1, n2, o), o)), L(V, T.MapleTree.join_right(U32, V, Nat.sub(h1, h2), n1, n2, o)), P.app(V, L(V, n1), L(V, n2)), tr.norm(V, 1n+h1, T.MapleTree.join_right(U32, V, Nat.sub(h1, h2), n1, n2, o), o), tr.join_right(V, Nat.sub(h1, h2), n1, n2, o))
    case False{}:
      Equal.trans(P.Es(V), TL(V, T.MapleTree.norm(U32, V, 1n+h2, T.MapleTree.join_left(U32, V, Nat.sub(h2, h1), n1, n2, o), o)), L(V, T.MapleTree.join_left(U32, V, Nat.sub(h2, h1), n1, n2, o)), P.app(V, L(V, n1), L(V, n2)), tr.norm(V, 1n+h2, T.MapleTree.join_left(U32, V, Nat.sub(h2, h1), n1, n2, o), o), tr.join_left(V, Nat.sub(h2, h1), n1, n2, o))

def tr.join.go(e1: Bool, e2: Bool, -V: Data, +o: Nat, +h1: Nat, +n1: Nd(V), +h2: Nat, +n2: Nd(V), +q1: {N.MapleNode.is_empty(U32, V, n1) == e1 : Bool}, +q2: {N.MapleNode.is_empty(U32, V, n2) == e2 : Bool}) -> {TL(V, T.MapleTree.join.go(U32, V, e1, e2, o, h1, n1, h2, n2)) == P.app(V, L(V, n1), L(V, n2)) : P.Es(V)}:
  match e1:
    case True{}:
      %Equal.sym(P.Es(V), L(V, n1), Nil{}, nd.empty_of(V, n1, q1)) : {L(V, n2) == P.app(V, _, L(V, n2)) : P.Es(V)}
      {==}
    case False{}:
      match e2:
        case True{}:
          %Equal.sym(P.Es(V), L(V, n2), Nil{}, nd.empty_of(V, n2, q2)) : {L(V, n1) == P.app(V, L(V, n1), _) : P.Es(V)}
          Equal.sym(P.Es(V), P.app(V, L(V, n1), Nil{}), L(V, n1), P.app.nil(V, L(V, n1)))
        case False{}:
          tr.join.tall(Nat.is_le(h2, h1), V, h1, n1, h2, n2, o)

# the entries of join(t1, t2) are those of t1, then those of t2
def tr.join(-V: Data, t1: Tr(V), t2: Tr(V)) -> {TL(V, T.MapleTree.join(U32, V, t1, t2)) == P.app(V, TL(V, t1), TL(V, t2)) : P.Es(V)}:
  match t1:
    case N.MapleTree{+o1, +h1, +n1}:
      match t2:
        case N.MapleTree{+o2, +h2, +n2}:
          tr.join.go(N.MapleNode.is_empty(U32, V, n1), N.MapleNode.is_empty(U32, V, n2), V, o1, h1, n1, h2, n2, {==}, {==})

# Pivots through restructuring

def kis(+m: Maybe<&2, U32>, +p: U32) -> Bool:
  N.MapleNode.key_is(~U32, ~U32.cmp, m, p)

def kis.some(m: Maybe<&2, U32>, +p: U32, +e: {kis(m, p) == True{} : Bool}) -> {m == Some{p} : Maybe<&2, U32>}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{p} : Maybe<&2, U32>}, O.ab.ft(e))
    case Some{+k}:
      Equal.cong(U32, Maybe<&2, U32>, z => Some{z}, k, p, UO.u32_cmp_eq(k, p, O.cm.eq_of(U32.cmp(k, p), e)))

def kis.refl(+p: U32) -> {kis(Some{p}, p) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(p, p), EQ{}, UO.u32_cmp_refl(p)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def pk.k(-V: Data, +p: U32, +c: Nd(V), +r: Nd(V), +h: {pok(V, N.MapleSlot{p, c, r}) == True{} : Bool}) -> {kis(nlk(V, c), p) == True{} : Bool}:
  O.bo.and_l(kis(nlk(V, c), p), Bool.and(pok(V, c), pok(V, r)), h)

def pk.c(-V: Data, +p: U32, +c: Nd(V), +r: Nd(V), +h: {pok(V, N.MapleSlot{p, c, r}) == True{} : Bool}) -> {pok(V, c) == True{} : Bool}:
  O.bo.and_l(pok(V, c), pok(V, r), O.bo.and_r(kis(nlk(V, c), p), Bool.and(pok(V, c), pok(V, r)), h))

def pk.r(-V: Data, +p: U32, +c: Nd(V), +r: Nd(V), +h: {pok(V, N.MapleSlot{p, c, r}) == True{} : Bool}) -> {pok(V, r) == True{} : Bool}:
  O.bo.and_r(pok(V, c), pok(V, r), O.bo.and_r(kis(nlk(V, c), p), Bool.and(pok(V, c), pok(V, r)), h))

def pk.intro(-V: Data, +p: U32, +c: Nd(V), +r: Nd(V), +k: {kis(nlk(V, c), p) == True{} : Bool}, +hc: {pok(V, c) == True{} : Bool}, +hr: {pok(V, r) == True{} : Bool}) -> {pok(V, N.MapleSlot{p, c, r}) == True{} : Bool}:
  O.bo.and_intro(kis(nlk(V, c), p), Bool.and(pok(V, c), pok(V, r)), k, O.bo.and_intro(pok(V, c), pok(V, r), hc, hr))

# the child's last key is the pivot
def pk.key(-V: Data, +p: U32, +c: Nd(V), +r: Nd(V), +h: {pok(V, N.MapleSlot{p, c, r}) == True{} : Bool}) -> {nlk(V, c) == Some{p} : Maybe<&2, U32>}:
  kis.some(nlk(V, c), p, pk.k(V, p, c, r, h))

def pok.key_rw(-V: Data, +c: Nd(V), +p: U32, +em: {nlk(V, c) == Some{p} : Maybe<&2, U32>}) -> {kis(nlk(V, c), p) == True{} : Bool}:
  %Equal.sym(Maybe<&2, U32>, nlk(V, c), Some{p}, em) : {kis(_, p) == True{} : Bool}
  kis.refl(p)

def pok.cons.go(-V: Data, m: Maybe<&2, U32>, +c: Nd(V), +r: Nd(V), +em: {nlk(V, c) == m : Maybe<&2, U32>}, +hc: {pok(V, c) == True{} : Bool}, +hr: {pok(V, r) == True{} : Bool}) -> {pok(V, N.MapleNode.cons.go(U32, V, m, c, r)) == True{} : Bool}:
  match m:
    case None{}:
      hr
    case Some{+p}:
      pk.intro(V, p, c, r, pok.key_rw(V, c, p, em), hc, hr)

def pok.cons(-V: Data, +c: Nd(V), +r: Nd(V), +hc: {pok(V, c) == True{} : Bool}, +hr: {pok(V, r) == True{} : Bool}) -> {pok(V, N.MapleNode.cons(U32, V, c, r)) == True{} : Bool}:
  pok.cons.go(V, nlk(V, c), c, r, {==}, hc, hr)

def pok.append(-V: Data, x: Nd(V), +y: Nd(V), +hx: {pok(V, x) == True{} : Bool}, +hy: {pok(V, y) == True{} : Bool}) -> {pok(V, N.MapleNode.append(U32, V, x, y)) == True{} : Bool}:
  match x:
    case N.MapleLeaf{+es}:
      pok.cons(V, N.MapleLeaf{es}, y, {==}, hy)
    case N.MapleNil{}:
      hy
    case N.MapleSlot{+p, +c, +r}:
      pk.intro(V, p, c, N.MapleNode.append(U32, V, r, y), pk.k(V, p, c, r, hx), pk.c(V, p, c, r, hx), pok.append(V, r, y, pk.r(V, p, c, r, hx), hy))

def pok.take(-V: Data, n: Nd(V), k: Nat, +h: {pok(V, n) == True{} : Bool}) -> {pok(V, N.MapleNode.take(U32, V, n, k)) == True{} : Bool}:
  match n:
    case N.MapleLeaf{es}:
      {==}
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      match k:
        case 0n:
          {==}
        case 1n+(+j):
          pk.intro(V, p, c, N.MapleNode.take(U32, V, r, j), pk.k(V, p, c, r, h), pk.c(V, p, c, r, h), pok.take(V, r, j, pk.r(V, p, c, r, h)))

def pok.drop(-V: Data, n: Nd(V), k: Nat, +h: {pok(V, n) == True{} : Bool}) -> {pok(V, N.MapleNode.drop(U32, V, n, k)) == True{} : Bool}:
  match n:
    case N.MapleLeaf{es}:
      {==}
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      match k:
        case 0n:
          h
        case 1n+(+j):
          pok.drop(V, r, j, pk.r(V, p, c, r, h))

def pok.merge(-V: Data, x: Nd(V), y: Nd(V), +hx: {pok(V, x) == True{} : Bool}, +hy: {pok(V, y) == True{} : Bool}) -> {pok(V, N.MapleNode.merge(U32, V, x, y)) == True{} : Bool}:
  match x:
    case N.MapleLeaf{+es}:
      match y:
        case N.MapleLeaf{fs}:
          {==}
        case N.MapleNil{}:
          {==}
        case N.MapleSlot{+q, +d, +s}:
          pok.cons(V, N.MapleLeaf{es}, N.MapleSlot{q, d, s}, {==}, hy)
    case N.MapleNil{}:
      hy
    case N.MapleSlot{+p, +c, +r}:
      pok.append(V, N.MapleSlot{p, c, r}, y, hx, hy)

def pok.fit.go(-V: Data, over: Bool, +n: Nd(V), +k: Nat, +h: {pok(V, n) == True{} : Bool}) -> {pok(V, N.MapleNode.fit.go(U32, V, over, n, k)) == True{} : Bool}:
  match over:
    case False{}:
      pok.cons(V, n, N.MapleNil{}, h, {==})
    case True{}:
      pok.cons(V, N.MapleNode.take(U32, V, n, k), N.MapleNode.cons(U32, V, N.MapleNode.drop(U32, V, n, k), N.MapleNil{}), pok.take(V, n, k, h), pok.cons(V, N.MapleNode.drop(U32, V, n, k), N.MapleNil{}, pok.drop(V, n, k, h), {==}))

def pok.fit(-V: Data, +o: Nat, +n: Nd(V), +h: {pok(V, n) == True{} : Bool}) -> {pok(V, N.MapleNode.fit(U32, V, o, n)) == True{} : Bool}:
  pok.fit.go(V, Nat.is_lt(o, N.MapleNode.count(U32, V, n)), n, N.MapleNode.half(N.MapleNode.count(U32, V, n)), h)

def pok.init.go(-V: Data, n: Nd(V), +p: U32, +c: Nd(V), +h: {pok(V, N.MapleSlot{p, c, n}) == True{} : Bool}) -> {pok(V, N.MapleNode.init.go(U32, V, n, p, c)) == True{} : Bool}:
  match n:
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+q, +d, +r}:
      pk.intro(V, p, c, N.MapleNode.init.go(U32, V, r, q, d), pk.k(V, p, c, N.MapleSlot{q, d, r}, h), pk.c(V, p, c, N.MapleSlot{q, d, r}, h), pok.init.go(V, r, q, d, pk.r(V, p, c, N.MapleSlot{q, d, r}, h)))
    case N.MapleLeaf{+es}:
      pk.intro(V, p, c, N.MapleNil{}, pk.k(V, p, c, N.MapleLeaf{es}, h), pk.c(V, p, c, N.MapleLeaf{es}, h), {==})

def pok.last.go(-V: Data, n: Nd(V), +c: Nd(V), +hc: {pok(V, c) == True{} : Bool}, +hn: {pok(V, n) == True{} : Bool}) -> {pok(V, N.MapleNode.last.go(U32, V, n, c)) == True{} : Bool}:
  match n:
    case N.MapleNil{}:
      hc
    case N.MapleSlot{+q, +d, +r}:
      pok.last.go(V, r, d, pk.c(V, q, d, r, hn), pk.r(V, q, d, r, hn))
    case N.MapleLeaf{es}:
      {==}

def pok.init(-V: Data, n: Nd(V), +h: {pok(V, n) == True{} : Bool}) -> {pok(V, N.MapleNode.init(U32, V, n)) == True{} : Bool}:
  match n:
    case N.MapleLeaf{es}:
      {==}
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      pok.init.go(V, r, p, c, h)

def pok.last(-V: Data, n: Nd(V), +h: {pok(V, n) == True{} : Bool}) -> {pok(V, N.MapleNode.last(U32, V, n)) == True{} : Bool}:
  match n:
    case N.MapleLeaf{es}:
      {==}
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      pok.last.go(V, r, c, pk.c(V, p, c, r, h), pk.r(V, p, c, r, h))

def pok.first(-V: Data, n: Nd(V), +h: {pok(V, n) == True{} : Bool}) -> {pok(V, N.MapleNode.first(U32, V, n)) == True{} : Bool}:
  match n:
    case N.MapleLeaf{es}:
      {==}
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      pk.c(V, p, c, r, h)

def pok.tail(-V: Data, n: Nd(V), +h: {pok(V, n) == True{} : Bool}) -> {pok(V, N.MapleNode.tail(U32, V, n)) == True{} : Bool}:
  match n:
    case N.MapleLeaf{es}:
      {==}
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      pk.r(V, p, c, r, h)

def tpok.norm(-V: Data, h: Nat, n: Nd(V), +o: Nat, +hn: {pok(V, n) == True{} : Bool}) -> {tpok(V, T.MapleTree.norm(U32, V, h, n, o)) == True{} : Bool}:
  match h:
    case 0n:
      hn
    case 1n+(+g):
      match n:
        case N.MapleSlot{+p, +c, r}:
          match r:
            case N.MapleNil{}:
              tpok.norm(V, g, c, o, pk.c(V, p, c, N.MapleNil{}, hn))
            case N.MapleLeaf{es}:
              hn
            case N.MapleSlot{q, d, s}:
              hn
        case N.MapleNil{}:
          {==}
        case N.MapleLeaf{es}:
          {==}

def pok.join_right(-V: Data, d: Nat, +n1: Nd(V), +n2: Nd(V), +o: Nat, +h1: {pok(V, n1) == True{} : Bool}, +h2: {pok(V, n2) == True{} : Bool}) -> {pok(V, T.MapleTree.join_right(U32, V, d, n1, n2, o)) == True{} : Bool}:
  match d:
    case 0n:
      pok.fit(V, o, N.MapleNode.merge(U32, V, n1, n2), pok.merge(V, n1, n2, h1, h2))
    case 1n+(+e):
      pok.fit(V, o, N.MapleNode.append(U32, V, N.MapleNode.init(U32, V, n1), T.MapleTree.join_right(U32, V, e, N.MapleNode.last(U32, V, n1), n2, o)), pok.append(V, N.MapleNode.init(U32, V, n1), T.MapleTree.join_right(U32, V, e, N.MapleNode.last(U32, V, n1), n2, o), pok.init(V, n1, h1), pok.join_right(V, e, N.MapleNode.last(U32, V, n1), n2, o, pok.last(V, n1, h1), h2)))

def pok.join_left(-V: Data, d: Nat, +n1: Nd(V), +n2: Nd(V), +o: Nat, +h1: {pok(V, n1) == True{} : Bool}, +h2: {pok(V, n2) == True{} : Bool}) -> {pok(V, T.MapleTree.join_left(U32, V, d, n1, n2, o)) == True{} : Bool}:
  match d:
    case 0n:
      pok.fit(V, o, N.MapleNode.merge(U32, V, n1, n2), pok.merge(V, n1, n2, h1, h2))
    case 1n+(+e):
      pok.fit(V, o, N.MapleNode.append(U32, V, T.MapleTree.join_left(U32, V, e, n1, N.MapleNode.first(U32, V, n2), o), N.MapleNode.tail(U32, V, n2)), pok.append(V, T.MapleTree.join_left(U32, V, e, n1, N.MapleNode.first(U32, V, n2), o), N.MapleNode.tail(U32, V, n2), pok.join_left(V, e, n1, N.MapleNode.first(U32, V, n2), o, h1, pok.first(V, n2, h2)), pok.tail(V, n2, h2)))

def tpok.join.tall(right: Bool, -V: Data, +h1: Nat, +n1: Nd(V), +h2: Nat, +n2: Nd(V), +o: Nat, +p1: {pok(V, n1) == True{} : Bool}, +p2: {pok(V, n2) == True{} : Bool}) -> {tpok(V, T.MapleTree.join.tall(U32, V, right, h1, n1, h2, n2, o)) == True{} : Bool}:
  match right:
    case True{}:
      tpok.norm(V, 1n+h1, T.MapleTree.join_right(U32, V, Nat.sub(h1, h2), n1, n2, o), o, pok.join_right(V, Nat.sub(h1, h2), n1, n2, o, p1, p2))
    case False{}:
      tpok.norm(V, 1n+h2, T.MapleTree.join_left(U32, V, Nat.sub(h2, h1), n1, n2, o), o, pok.join_left(V, Nat.sub(h2, h1), n1, n2, o, p1, p2))

def tpok.join.go(e1: Bool, e2: Bool, -V: Data, +o: Nat, +h1: Nat, +n1: Nd(V), +h2: Nat, +n2: Nd(V), +p1: {pok(V, n1) == True{} : Bool}, +p2: {pok(V, n2) == True{} : Bool}) -> {tpok(V, T.MapleTree.join.go(U32, V, e1, e2, o, h1, n1, h2, n2)) == True{} : Bool}:
  match e1:
    case True{}:
      p2
    case False{}:
      match e2:
        case True{}:
          p1
        case False{}:
          tpok.join.tall(Nat.is_le(h2, h1), V, h1, n1, h2, n2, o, p1, p2)

def tpok.join(-V: Data, t1: Tr(V), t2: Tr(V), +p1: {tpok(V, t1) == True{} : Bool}, +p2: {tpok(V, t2) == True{} : Bool}) -> {tpok(V, T.MapleTree.join(U32, V, t1, t2)) == True{} : Bool}:
  match t1:
    case N.MapleTree{+o1, +h1, +n1}:
      match t2:
        case N.MapleTree{+o2, +h2, +n2}:
          tpok.join.go(N.MapleNode.is_empty(U32, V, n1), N.MapleNode.is_empty(U32, V, n2), V, o1, h1, n1, h2, n2, p1, p2)

# The pivots and the contents: a node's last key is its contents' last key

def nlk.L(-V: Data, n: Nd(V), +h: {pok(V, n) == True{} : Bool}) -> {nlk(V, n) == P.lkey(V, L(V, n)) : Maybe<&2, U32>}:
  match n:
    case N.MapleLeaf{es}:
      {==}
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      +ckey = Equal.trans(Maybe<&2, U32>, P.lkey(V, L(V, c)), nlk(V, c), Some{p}, Equal.sym(Maybe<&2, U32>, nlk(V, c), P.lkey(V, L(V, c)), nlk.L(V, c, pk.c(V, p, c, r, h))), pk.key(V, p, c, r, h))
      %Equal.sym(Maybe<&2, U32>, P.lkey(V, P.app(V, L(V, c), L(V, r))), Maybe.or(&2, U32, P.lkey(V, L(V, r)), P.lkey(V, L(V, c))), P.lkey.app(V, L(V, c), L(V, r))) : {Maybe.or(&2, U32, nlk(V, r), Some{p}) == _ : Maybe<&2, U32>}
      %Equal.sym(Maybe<&2, U32>, P.lkey(V, L(V, c)), Some{p}, ckey) : {Maybe.or(&2, U32, nlk(V, r), Some{p}) == Maybe.or(&2, U32, P.lkey(V, L(V, r)), _) : Maybe<&2, U32>}
      %Equal.sym(Maybe<&2, U32>, nlk(V, r), P.lkey(V, L(V, r)), nlk.L(V, r, pk.r(V, p, c, r, h))) : {Maybe.or(&2, U32, _, Some{p}) == Maybe.or(&2, U32, P.lkey(V, L(V, r)), Some{p}) : Maybe<&2, U32>}
      {==}

# the contents of the child of a slot end at its pivot ...
def ch.key(-V: Data, +p: U32, +c: Nd(V), +r: Nd(V), +h: {pok(V, N.MapleSlot{p, c, r}) == True{} : Bool}) -> {P.lkey(V, L(V, c)) == Some{p} : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, P.lkey(V, L(V, c)), nlk(V, c), Some{p}, Equal.sym(Maybe<&2, U32>, nlk(V, c), P.lkey(V, L(V, c)), nlk.L(V, c, pk.c(V, p, c, r, h))), pk.key(V, p, c, r, h))

def ch.lasts(-V: Data, +p: U32, +c: Nd(V), +r: Nd(V), +w: {P.wf(V, P.app(V, L(V, c), L(V, r))) == True{} : Bool}, +h: {pok(V, N.MapleSlot{p, c, r}) == True{} : Bool}) -> {P.lasts_le(V, L(V, c), p) == True{} : Bool}:
  P.lasts.of_key(V, L(V, c), p, P.wf.app_l(V, L(V, c), L(V, r), w), ch.key(V, p, c, r, h))

# ... and the rest starts after it
def ch.aft(-V: Data, +p: U32, +c: Nd(V), +r: Nd(V), +w: {P.wf(V, P.app(V, L(V, c), L(V, r))) == True{} : Bool}, +h: {pok(V, N.MapleSlot{p, c, r}) == True{} : Bool}) -> {P.aft(V, p, L(V, r)) == True{} : Bool}:
  P.aft.of_key(V, L(V, c), L(V, r), p, w, ch.key(V, p, c, r, h))

def cmp.not_lt_eq(+a: U32, +b: U32, +e: {U32.cmp(a, b) == EQ{} : Cmp}) -> {O.ult(a, b) == False{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, b), EQ{}, e) : {Cmp.is_lt(_) == False{} : Bool}
  {==}

def cmp.not_lt_gt(+a: U32, +b: U32, +e: {U32.cmp(a, b) == GT{} : Cmp}) -> {O.ult(a, b) == False{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, b), GT{}, e) : {Cmp.is_lt(_) == False{} : Bool}
  {==}

def cmp.lt_lt(+a: U32, +b: U32, +e: {U32.cmp(a, b) == LT{} : Cmp}) -> {O.ult(a, b) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, b), LT{}, e) : {Cmp.is_lt(_) == True{} : Bool}
  {==}

def cmp.le_lt(+a: U32, +b: U32, +e: {U32.cmp(a, b) == LT{} : Cmp}) -> {O.ule(a, b) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, b), LT{}, e) : {Cmp.is_le(_) == True{} : Bool}
  {==}

def cmp.le_eq(+a: U32, +b: U32, +e: {U32.cmp(a, b) == EQ{} : Cmp}) -> {O.ule(a, b) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, b), EQ{}, e) : {Cmp.is_le(_) == True{} : Bool}
  {==}

def cmp.not_le_gt(+a: U32, +b: U32, +e: {U32.cmp(a, b) == GT{} : Cmp}) -> {O.ule(a, b) == False{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, b), GT{}, e) : {Cmp.is_le(_) == False{} : Bool}
  {==}

def cmp.gt_le(+a: U32, +b: U32, +e: {U32.cmp(a, b) == GT{} : Cmp}) -> {O.ule(b, a) == True{} : Bool}:
  UO.u32_lt_le(b, a, UO.u32_not_le(a, b, cmp.not_le_gt(a, b, e)))

def lo(-V: Data, n: Nd(V), h: Nat, +a: U32, pre: Nd(V), c: Cmp, +o: Nat) -> Tr(V):
  T.MapleTree.lo(~U32, ~U32.cmp, ~M.MapleKey32.dec, V, n, h, a, pre, c, o)

def hi(-V: Data, n: Nd(V), h: Nat, +b: U32, c: Cmp, +o: Nat) -> Tr(V):
  T.MapleTree.hi(~U32, ~U32.cmp, ~M.MapleKey32.inc, V, n, h, b, c, o)

def probe(-V: Data, n: Nd(V), +i: U32) -> Cmp:
  N.MapleNode.probe(~U32, ~U32.cmp, V, n, i)

# cutting below a: the rest of the slot (from the pivot on) is dropped
def tr.lo.ge(-V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +g: Nat, +a: U32, +pre: Nd(V), +o: Nat, +w: {P.wf(V, P.app(V, L(V, ch), L(V, r))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +ge: {O.ule(a, p) == True{} : Bool}, +ihc: {TL(V, lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o)) == P.below(V, L(V, ch), a) : P.Es(V)}) -> {TL(V, T.MapleTree.join(U32, V, T.MapleTree.norm(U32, V, 1n+g, pre, o), lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o))) == P.app(V, L(V, pre), P.below(V, P.app(V, L(V, ch), L(V, r)), a)) : P.Es(V)}:
  %Equal.sym(P.Es(V), TL(V, T.MapleTree.join(U32, V, T.MapleTree.norm(U32, V, 1n+g, pre, o), lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o))), P.app(V, TL(V, T.MapleTree.norm(U32, V, 1n+g, pre, o)), TL(V, lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o))), tr.join(V, T.MapleTree.norm(U32, V, 1n+g, pre, o), lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o))) : {_ == P.app(V, L(V, pre), P.below(V, P.app(V, L(V, ch), L(V, r)), a)) : P.Es(V)}
  %Equal.sym(P.Es(V), TL(V, T.MapleTree.norm(U32, V, 1n+g, pre, o)), L(V, pre), tr.norm(V, 1n+g, pre, o)) : {P.app(V, _, TL(V, lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o))) == P.app(V, L(V, pre), P.below(V, P.app(V, L(V, ch), L(V, r)), a)) : P.Es(V)}
  %Equal.sym(P.Es(V), TL(V, lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o)), P.below(V, L(V, ch), a), ihc) : {P.app(V, L(V, pre), _) == P.app(V, L(V, pre), P.below(V, P.app(V, L(V, ch), L(V, r)), a)) : P.Es(V)}
  %Equal.sym(P.Es(V), P.below(V, P.app(V, L(V, ch), L(V, r)), a), P.app(V, P.below(V, L(V, ch), a), P.below(V, L(V, r), a)), P.below.app(V, L(V, ch), L(V, r), a)) : {P.app(V, L(V, pre), P.below(V, L(V, ch), a)) == P.app(V, L(V, pre), _) : P.Es(V)}
  %Equal.sym(P.Es(V), P.below(V, L(V, r), a), Nil{}, P.below.nil(V, L(V, r), p, a, P.wf.app_r(V, L(V, ch), L(V, r), w), ch.aft(V, p, ch, r, w, hp), ge)) : {P.app(V, L(V, pre), P.below(V, L(V, ch), a)) == P.app(V, L(V, pre), P.app(V, P.below(V, L(V, ch), a), _)) : P.Es(V)}
  %Equal.sym(P.Es(V), P.app(V, P.below(V, L(V, ch), a), Nil{}), P.below(V, L(V, ch), a), P.app.nil(V, P.below(V, L(V, ch), a))) : {P.app(V, L(V, pre), P.below(V, L(V, ch), a)) == P.app(V, L(V, pre), _) : P.Es(V)}
  {==}

# cutting below a: a child whose pivot is below a is kept whole
def tr.lo.lt(-V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +g: Nat, +a: U32, +pre: Nd(V), +o: Nat, +w: {P.wf(V, P.app(V, L(V, ch), L(V, r))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +lt: {O.ult(p, a) == True{} : Bool}, +ihr: {TL(V, lo(V, r, 1n+g, a, N.MapleNode.append(U32, V, pre, N.MapleSlot{p, ch, N.MapleNil{}}), probe(V, r, a), o)) == P.app(V, L(V, N.MapleNode.append(U32, V, pre, N.MapleSlot{p, ch, N.MapleNil{}})), P.below(V, L(V, r), a)) : P.Es(V)}) -> {TL(V, lo(V, r, 1n+g, a, N.MapleNode.append(U32, V, pre, N.MapleSlot{p, ch, N.MapleNil{}}), probe(V, r, a), o)) == P.app(V, L(V, pre), P.below(V, P.app(V, L(V, ch), L(V, r)), a)) : P.Es(V)}:
  %Equal.sym(P.Es(V), TL(V, lo(V, r, 1n+g, a, N.MapleNode.append(U32, V, pre, N.MapleSlot{p, ch, N.MapleNil{}}), probe(V, r, a), o)), P.app(V, L(V, N.MapleNode.append(U32, V, pre, N.MapleSlot{p, ch, N.MapleNil{}})), P.below(V, L(V, r), a)), ihr) : {_ == P.app(V, L(V, pre), P.below(V, P.app(V, L(V, ch), L(V, r)), a)) : P.Es(V)}
  %Equal.sym(P.Es(V), L(V, N.MapleNode.append(U32, V, pre, N.MapleSlot{p, ch, N.MapleNil{}})), P.app(V, L(V, pre), P.app(V, L(V, ch), Nil{})), nd.append(V, pre, N.MapleSlot{p, ch, N.MapleNil{}})) : {P.app(V, _, P.below(V, L(V, r), a)) == P.app(V, L(V, pre), P.below(V, P.app(V, L(V, ch), L(V, r)), a)) : P.Es(V)}
  %Equal.sym(P.Es(V), P.app(V, L(V, ch), Nil{}), L(V, ch), P.app.nil(V, L(V, ch))) : {P.app(V, P.app(V, L(V, pre), _), P.below(V, L(V, r), a)) == P.app(V, L(V, pre), P.below(V, P.app(V, L(V, ch), L(V, r)), a)) : P.Es(V)}
  %Equal.sym(P.Es(V), P.app(V, P.app(V, L(V, pre), L(V, ch)), P.below(V, L(V, r), a)), P.app(V, L(V, pre), P.app(V, L(V, ch), P.below(V, L(V, r), a))), P.app.assoc(V, L(V, pre), L(V, ch), P.below(V, L(V, r), a))) : {_ == P.app(V, L(V, pre), P.below(V, P.app(V, L(V, ch), L(V, r)), a)) : P.Es(V)}
  %Equal.sym(P.Es(V), P.below(V, P.app(V, L(V, ch), L(V, r)), a), P.app(V, P.below(V, L(V, ch), a), P.below(V, L(V, r), a)), P.below.app(V, L(V, ch), L(V, r), a)) : {P.app(V, L(V, pre), P.app(V, L(V, ch), P.below(V, L(V, r), a))) == P.app(V, L(V, pre), _) : P.Es(V)}
  %Equal.sym(P.Es(V), P.below(V, L(V, ch), a), L(V, ch), P.below.all(V, L(V, ch), p, a, ch.lasts(V, p, ch, r, w, hp), lt)) : {P.app(V, L(V, pre), P.app(V, L(V, ch), P.below(V, L(V, r), a))) == P.app(V, L(V, pre), P.app(V, _, P.below(V, L(V, r), a))) : P.Es(V)}
  {==}

def tr.lo.slot(c: Cmp, -V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +g: Nat, +a: U32, +pre: Nd(V), +o: Nat, +e: {U32.cmp(p, a) == c : Cmp}, +w: {P.wf(V, P.app(V, L(V, ch), L(V, r))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +ihr: {TL(V, lo(V, r, 1n+g, a, N.MapleNode.append(U32, V, pre, N.MapleSlot{p, ch, N.MapleNil{}}), probe(V, r, a), o)) == P.app(V, L(V, N.MapleNode.append(U32, V, pre, N.MapleSlot{p, ch, N.MapleNil{}})), P.below(V, L(V, r), a)) : P.Es(V)}, +ihc: {TL(V, lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o)) == P.below(V, L(V, ch), a) : P.Es(V)}) -> {TL(V, lo(V, N.MapleSlot{p, ch, r}, 1n+g, a, pre, c, o)) == P.app(V, L(V, pre), P.below(V, P.app(V, L(V, ch), L(V, r)), a)) : P.Es(V)}:
  match c:
    case LT{}:
      tr.lo.lt(V, p, ch, r, g, a, pre, o, w, hp, cmp.lt_lt(p, a, e), ihr)
    case EQ{}:
      tr.lo.ge(V, p, ch, r, g, a, pre, o, w, hp, UO.u32_not_lt(p, a, cmp.not_lt_eq(p, a, e)), ihc)
    case GT{}:
      tr.lo.ge(V, p, ch, r, g, a, pre, o, w, hp, UO.u32_not_lt(p, a, cmp.not_lt_gt(p, a, e)), ihc)

# cutting below a: pre, then every entry cut to its part below a
def tr.lo(-V: Data, n: Nd(V), +h: Nat, +a: U32, +pre: Nd(V), +o: Nat, +w: {P.wf(V, L(V, n)) == True{} : Bool}, +hp: {pok(V, n) == True{} : Bool}) -> {TL(V, lo(V, n, h, a, pre, probe(V, n, a), o)) == P.app(V, L(V, pre), P.below(V, L(V, n), a)) : P.Es(V)}:
  match n:
    case N.MapleSlot{+p, +ch, +r}:
      match h:
        case 0n:
          tr.join(V, T.MapleTree.norm(U32, V, 0n, pre, o), N.MapleTree{o, 0n, N.MapleLeaf{P.below(V, L(V, N.MapleSlot{p, ch, r}), a)}})
        case 1n+(+g):
          tr.lo.slot(U32.cmp(p, a), V, p, ch, r, g, a, pre, o, {==}, w, hp, tr.lo(V, r, 1n+g, a, N.MapleNode.append(U32, V, pre, N.MapleSlot{p, ch, N.MapleNil{}}), o, P.wf.app_r(V, L(V, ch), L(V, r), w), pk.r(V, p, ch, r, hp)), tr.lo(V, ch, g, a, N.MapleNil{}, o, P.wf.app_l(V, L(V, ch), L(V, r), w), pk.c(V, p, ch, r, hp)))
    case N.MapleNil{}:
      Equal.trans(P.Es(V), TL(V, T.MapleTree.norm(U32, V, h, pre, o)), L(V, pre), P.app(V, L(V, pre), Nil{}), tr.norm(V, h, pre, o), Equal.sym(P.Es(V), P.app(V, L(V, pre), Nil{}), L(V, pre), P.app.nil(V, L(V, pre))))
    case N.MapleLeaf{+es}:
      %Equal.sym(P.Es(V), TL(V, T.MapleTree.join(U32, V, T.MapleTree.norm(U32, V, h, pre, o), N.MapleTree{o, 0n, N.MapleLeaf{P.below(V, es, a)}})), P.app(V, TL(V, T.MapleTree.norm(U32, V, h, pre, o)), P.below(V, es, a)), tr.join(V, T.MapleTree.norm(U32, V, h, pre, o), N.MapleTree{o, 0n, N.MapleLeaf{P.below(V, es, a)}})) : {_ == P.app(V, L(V, pre), P.below(V, es, a)) : P.Es(V)}
      %Equal.sym(P.Es(V), TL(V, T.MapleTree.norm(U32, V, h, pre, o)), L(V, pre), tr.norm(V, h, pre, o)) : {P.app(V, _, P.below(V, es, a)) == P.app(V, L(V, pre), P.below(V, es, a)) : P.Es(V)}
      {==}

# cutting above b: a child whose pivot is above b is cut, and the rest kept
def tr.hi.gt(-V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +g: Nat, +b: U32, +o: Nat, +w: {P.wf(V, P.app(V, L(V, ch), L(V, r))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +gt: {O.ule(b, p) == True{} : Bool}, +ihc: {TL(V, hi(V, ch, g, b, probe(V, ch, b), o)) == P.above(V, L(V, ch), b) : P.Es(V)}) -> {TL(V, T.MapleTree.join(U32, V, hi(V, ch, g, b, probe(V, ch, b), o), T.MapleTree.norm(U32, V, 1n+g, r, o))) == P.above(V, P.app(V, L(V, ch), L(V, r)), b) : P.Es(V)}:
  %Equal.sym(P.Es(V), TL(V, T.MapleTree.join(U32, V, hi(V, ch, g, b, probe(V, ch, b), o), T.MapleTree.norm(U32, V, 1n+g, r, o))), P.app(V, TL(V, hi(V, ch, g, b, probe(V, ch, b), o)), TL(V, T.MapleTree.norm(U32, V, 1n+g, r, o))), tr.join(V, hi(V, ch, g, b, probe(V, ch, b), o), T.MapleTree.norm(U32, V, 1n+g, r, o))) : {_ == P.above(V, P.app(V, L(V, ch), L(V, r)), b) : P.Es(V)}
  %Equal.sym(P.Es(V), TL(V, hi(V, ch, g, b, probe(V, ch, b), o)), P.above(V, L(V, ch), b), ihc) : {P.app(V, _, TL(V, T.MapleTree.norm(U32, V, 1n+g, r, o))) == P.above(V, P.app(V, L(V, ch), L(V, r)), b) : P.Es(V)}
  %Equal.sym(P.Es(V), TL(V, T.MapleTree.norm(U32, V, 1n+g, r, o)), L(V, r), tr.norm(V, 1n+g, r, o)) : {P.app(V, P.above(V, L(V, ch), b), _) == P.above(V, P.app(V, L(V, ch), L(V, r)), b) : P.Es(V)}
  %Equal.sym(P.Es(V), P.above(V, P.app(V, L(V, ch), L(V, r)), b), P.app(V, P.above(V, L(V, ch), b), P.above(V, L(V, r), b)), P.above.app(V, L(V, ch), L(V, r), b)) : {P.app(V, P.above(V, L(V, ch), b), L(V, r)) == _ : P.Es(V)}
  %Equal.sym(P.Es(V), P.above(V, L(V, r), b), L(V, r), P.above.all(V, L(V, r), b, P.aft.weaken(V, b, p, L(V, r), gt, ch.aft(V, p, ch, r, w, hp)))) : {P.app(V, P.above(V, L(V, ch), b), L(V, r)) == P.app(V, P.above(V, L(V, ch), b), _) : P.Es(V)}
  {==}

# cutting above b: a child whose pivot is at most b is dropped
def tr.hi.le(-V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +g: Nat, +b: U32, +o: Nat, +w: {P.wf(V, P.app(V, L(V, ch), L(V, r))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +le: {O.ule(p, b) == True{} : Bool}, +ihr: {TL(V, hi(V, r, 1n+g, b, probe(V, r, b), o)) == P.above(V, L(V, r), b) : P.Es(V)}) -> {TL(V, hi(V, r, 1n+g, b, probe(V, r, b), o)) == P.above(V, P.app(V, L(V, ch), L(V, r)), b) : P.Es(V)}:
  %Equal.sym(P.Es(V), P.above(V, P.app(V, L(V, ch), L(V, r)), b), P.app(V, P.above(V, L(V, ch), b), P.above(V, L(V, r), b)), P.above.app(V, L(V, ch), L(V, r), b)) : {TL(V, hi(V, r, 1n+g, b, probe(V, r, b), o)) == _ : P.Es(V)}
  %Equal.sym(P.Es(V), P.above(V, L(V, ch), b), Nil{}, P.above.nil(V, L(V, ch), p, b, ch.lasts(V, p, ch, r, w, hp), P.wf.app_l(V, L(V, ch), L(V, r), w), le)) : {TL(V, hi(V, r, 1n+g, b, probe(V, r, b), o)) == P.app(V, _, P.above(V, L(V, r), b)) : P.Es(V)}
  ihr

def tr.hi.slot(c: Cmp, -V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +g: Nat, +b: U32, +o: Nat, +e: {U32.cmp(p, b) == c : Cmp}, +w: {P.wf(V, P.app(V, L(V, ch), L(V, r))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +ihc: {TL(V, hi(V, ch, g, b, probe(V, ch, b), o)) == P.above(V, L(V, ch), b) : P.Es(V)}, +ihr: {TL(V, hi(V, r, 1n+g, b, probe(V, r, b), o)) == P.above(V, L(V, r), b) : P.Es(V)}) -> {TL(V, hi(V, N.MapleSlot{p, ch, r}, 1n+g, b, c, o)) == P.above(V, P.app(V, L(V, ch), L(V, r)), b) : P.Es(V)}:
  match c:
    case GT{}:
      tr.hi.gt(V, p, ch, r, g, b, o, w, hp, cmp.gt_le(p, b, e), ihc)
    case LT{}:
      tr.hi.le(V, p, ch, r, g, b, o, w, hp, cmp.le_lt(p, b, e), ihr)
    case EQ{}:
      tr.hi.le(V, p, ch, r, g, b, o, w, hp, cmp.le_eq(p, b, e), ihr)

# cutting above b: every entry cut to its part above b
def tr.hi(-V: Data, n: Nd(V), +h: Nat, +b: U32, +o: Nat, +w: {P.wf(V, L(V, n)) == True{} : Bool}, +hp: {pok(V, n) == True{} : Bool}) -> {TL(V, hi(V, n, h, b, probe(V, n, b), o)) == P.above(V, L(V, n), b) : P.Es(V)}:
  match n:
    case N.MapleSlot{+p, +ch, +r}:
      match h:
        case 0n:
          {==}
        case 1n+(+g):
          tr.hi.slot(U32.cmp(p, b), V, p, ch, r, g, b, o, {==}, w, hp, tr.hi(V, ch, g, b, o, P.wf.app_l(V, L(V, ch), L(V, r), w), pk.c(V, p, ch, r, hp)), tr.hi(V, r, 1n+g, b, o, P.wf.app_r(V, L(V, ch), L(V, r), w), pk.r(V, p, ch, r, hp)))
    case N.MapleNil{}:
      {==}
    case N.MapleLeaf{es}:
      {==}

# the pivots of what lo and hi build are right
def tpok.lo(-V: Data, n: Nd(V), +h: Nat, +a: U32, +pre: Nd(V), c: Cmp, +o: Nat, +hn: {pok(V, n) == True{} : Bool}, +hpre: {pok(V, pre) == True{} : Bool}) -> {tpok(V, lo(V, n, h, a, pre, c, o)) == True{} : Bool}:
  match n:
    case N.MapleSlot{+p, +ch, +r}:
      match h:
        case 0n:
          tpok.join(V, T.MapleTree.norm(U32, V, 0n, pre, o), N.MapleTree{o, 0n, N.MapleLeaf{P.below(V, L(V, N.MapleSlot{p, ch, r}), a)}}, tpok.norm(V, 0n, pre, o, hpre), {==})
        case 1n+(+g):
          match c:
            case LT{}:
              tpok.lo(V, r, 1n+g, a, N.MapleNode.append(U32, V, pre, N.MapleSlot{p, ch, N.MapleNil{}}), probe(V, r, a), o, pk.r(V, p, ch, r, hn), pok.append(V, pre, N.MapleSlot{p, ch, N.MapleNil{}}, hpre, pk.intro(V, p, ch, N.MapleNil{}, pk.k(V, p, ch, r, hn), pk.c(V, p, ch, r, hn), {==})))
            case EQ{}:
              tpok.join(V, T.MapleTree.norm(U32, V, 1n+g, pre, o), lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o), tpok.norm(V, 1n+g, pre, o, hpre), tpok.lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o, pk.c(V, p, ch, r, hn), {==}))
            case GT{}:
              tpok.join(V, T.MapleTree.norm(U32, V, 1n+g, pre, o), lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o), tpok.norm(V, 1n+g, pre, o, hpre), tpok.lo(V, ch, g, a, N.MapleNil{}, probe(V, ch, a), o, pk.c(V, p, ch, r, hn), {==}))
    case N.MapleNil{}:
      tpok.norm(V, h, pre, o, hpre)
    case N.MapleLeaf{+es}:
      tpok.join(V, T.MapleTree.norm(U32, V, h, pre, o), N.MapleTree{o, 0n, N.MapleLeaf{P.below(V, es, a)}}, tpok.norm(V, h, pre, o, hpre), {==})

def tpok.hi(-V: Data, n: Nd(V), +h: Nat, +b: U32, c: Cmp, +o: Nat, +hn: {pok(V, n) == True{} : Bool}) -> {tpok(V, hi(V, n, h, b, c, o)) == True{} : Bool}:
  match n:
    case N.MapleSlot{+p, +ch, +r}:
      match h:
        case 0n:
          {==}
        case 1n+(+g):
          match c:
            case GT{}:
              tpok.join(V, hi(V, ch, g, b, probe(V, ch, b), o), T.MapleTree.norm(U32, V, 1n+g, r, o), tpok.hi(V, ch, g, b, probe(V, ch, b), o, pk.c(V, p, ch, r, hn)), tpok.norm(V, 1n+g, r, o, pk.r(V, p, ch, r, hn)))
            case LT{}:
              tpok.hi(V, r, 1n+g, b, probe(V, r, b), o, pk.r(V, p, ch, r, hn))
            case EQ{}:
              tpok.hi(V, r, 1n+g, b, probe(V, r, b), o, pk.r(V, p, ch, r, hn))
    case N.MapleNil{}:
      {==}
    case N.MapleLeaf{es}:
      {==}

# The public operations

def nd.onto(-V: Data, n: Nd(V), +acc: P.Es(V)) -> {N.MapleNode.entries_onto(U32, V, n, acc) == P.app(V, L(V, n), acc) : P.Es(V)}:
  match n:
    case N.MapleLeaf{es}:
      {==}
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      Equal.trans(P.Es(V), N.MapleNode.entries_onto(U32, V, c, N.MapleNode.entries_onto(U32, V, r, acc)), P.app(V, L(V, c), N.MapleNode.entries_onto(U32, V, r, acc)), P.app(V, P.app(V, L(V, c), L(V, r)), acc), nd.onto(V, c, N.MapleNode.entries_onto(U32, V, r, acc)), Equal.trans(P.Es(V), P.app(V, L(V, c), N.MapleNode.entries_onto(U32, V, r, acc)), P.app(V, L(V, c), P.app(V, L(V, r), acc)), P.app(V, P.app(V, L(V, c), L(V, r)), acc), Equal.cong(P.Es(V), P.Es(V), q => P.app(V, L(V, c), q), N.MapleNode.entries_onto(U32, V, r, acc), P.app(V, L(V, r), acc), nd.onto(V, r, acc)), Equal.sym(P.Es(V), P.app(V, P.app(V, L(V, c), L(V, r)), acc), P.app(V, L(V, c), P.app(V, L(V, r), acc)), P.app.assoc(V, L(V, c), L(V, r), acc))))

# entries (the interface's) are the contents
def tr.entries(-V: Data, t: Tr(V)) -> {X.Maple32.entries(V, t) == TL(V, t) : P.Es(V)}:
  match t:
    case N.MapleTree{o, h, +n}:
      Equal.trans(P.Es(V), N.MapleNode.entries_onto(U32, V, n, Nil{}), P.app(V, L(V, n), Nil{}), L(V, n), nd.onto(V, n, Nil{}), P.app.nil(V, L(V, n)))

def tr.valid(-V: Data, t: Tr(V)) -> {X.Maple32.valid(V, t) == Bool.and(P.wf(V, TL(V, t)), tpok(V, t)) : Bool}:
  match t:
    case N.MapleTree{o, h, n}:
      {==}

def tr.valid_wf(-V: Data, +t: Tr(V), +e: {X.Maple32.valid(V, t) == True{} : Bool}) -> {P.wf(V, TL(V, t)) == True{} : Bool}:
  O.bo.and_l(P.wf(V, TL(V, t)), tpok(V, t), Equal.trans(Bool, Bool.and(P.wf(V, TL(V, t)), tpok(V, t)), X.Maple32.valid(V, t), True{}, Equal.sym(Bool, X.Maple32.valid(V, t), Bool.and(P.wf(V, TL(V, t)), tpok(V, t)), tr.valid(V, t)), e))

def tr.valid_pok(-V: Data, +t: Tr(V), +e: {X.Maple32.valid(V, t) == True{} : Bool}) -> {tpok(V, t) == True{} : Bool}:
  O.bo.and_r(P.wf(V, TL(V, t)), tpok(V, t), Equal.trans(Bool, Bool.and(P.wf(V, TL(V, t)), tpok(V, t)), X.Maple32.valid(V, t), True{}, Equal.sym(Bool, X.Maple32.valid(V, t), Bool.and(P.wf(V, TL(V, t)), tpok(V, t)), tr.valid(V, t)), e))

def tr.valid_intro(-V: Data, +t: Tr(V), +w: {P.wf(V, TL(V, t)) == True{} : Bool}, +hp: {tpok(V, t) == True{} : Bool}) -> {X.Maple32.valid(V, t) == True{} : Bool}:
  %Equal.sym(Bool, X.Maple32.valid(V, t), Bool.and(P.wf(V, TL(V, t)), tpok(V, t)), tr.valid(V, t)) : {_ == True{} : Bool}
  O.bo.and_intro(P.wf(V, TL(V, t)), tpok(V, t), w, hp)

def tsr.go(-V: Data, ok: Bool, +t: Tr(V), +a: U32, +b: U32, +v: V) -> Tr(V):
  X.Maple.set_range.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, ok, t, a, b, v)

def tcr.go(-V: Data, ok: Bool, +t: Tr(V), +a: U32, +b: U32) -> Tr(V):
  X.Maple.clear_range.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, ok, t, a, b)

def single(-V: Data, +o: Nat, +a: U32, +b: U32, +v: V) -> Tr(V):
  N.MapleTree{o, 0n, N.MapleLeaf{[M.MapleEntry{a, b, v}]}}

def tr.sr.true(-V: Data, +o: Nat, +h: Nat, +root: Nd(V), +a: U32, +b: U32, +v: V, +w: {P.wf(V, L(V, root)) == True{} : Bool}, +hp: {pok(V, root) == True{} : Bool}) -> {TL(V, T.MapleTree.join(U32, V, T.MapleTree.join(U32, V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v)), hi(V, root, h, b, probe(V, root, b), o))) == P.app(V, P.below(V, L(V, root), a), Con{M.MapleEntry{a, b, v}, P.above(V, L(V, root), b)}) : P.Es(V)}:
  %Equal.sym(P.Es(V), TL(V, T.MapleTree.join(U32, V, T.MapleTree.join(U32, V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v)), hi(V, root, h, b, probe(V, root, b), o))), P.app(V, TL(V, T.MapleTree.join(U32, V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v))), TL(V, hi(V, root, h, b, probe(V, root, b), o))), tr.join(V, T.MapleTree.join(U32, V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v)), hi(V, root, h, b, probe(V, root, b), o))) : {_ == P.app(V, P.below(V, L(V, root), a), Con{M.MapleEntry{a, b, v}, P.above(V, L(V, root), b)}) : P.Es(V)}
  %Equal.sym(P.Es(V), TL(V, T.MapleTree.join(U32, V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v))), P.app(V, TL(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o)), TL(V, single(V, o, a, b, v))), tr.join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v))) : {P.app(V, _, TL(V, hi(V, root, h, b, probe(V, root, b), o))) == P.app(V, P.below(V, L(V, root), a), Con{M.MapleEntry{a, b, v}, P.above(V, L(V, root), b)}) : P.Es(V)}
  %Equal.sym(P.Es(V), TL(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o)), P.below(V, L(V, root), a), tr.lo(V, root, h, a, N.MapleNil{}, o, w, hp)) : {P.app(V, P.app(V, _, Con{M.MapleEntry{a, b, v}, Nil{}}), TL(V, hi(V, root, h, b, probe(V, root, b), o))) == P.app(V, P.below(V, L(V, root), a), Con{M.MapleEntry{a, b, v}, P.above(V, L(V, root), b)}) : P.Es(V)}
  %Equal.sym(P.Es(V), TL(V, hi(V, root, h, b, probe(V, root, b), o)), P.above(V, L(V, root), b), tr.hi(V, root, h, b, o, w, hp)) : {P.app(V, P.app(V, P.below(V, L(V, root), a), Con{M.MapleEntry{a, b, v}, Nil{}}), _) == P.app(V, P.below(V, L(V, root), a), Con{M.MapleEntry{a, b, v}, P.above(V, L(V, root), b)}) : P.Es(V)}
  P.app.assoc(V, P.below(V, L(V, root), a), Con{M.MapleEntry{a, b, v}, Nil{}}, P.above(V, L(V, root), b))

def tr.sr.go(ok: Bool, -V: Data, +t: Tr(V), +a: U32, +b: U32, +v: V, +w: {P.wf(V, TL(V, t)) == True{} : Bool}, +hp: {tpok(V, t) == True{} : Bool}) -> {TL(V, tsr.go(V, ok, t, a, b, v)) == P.msr.go(V, ok, TL(V, t), a, b, v) : P.Es(V)}:
  match ok:
    case True{}:
      match t:
        case N.MapleTree{+o, +h, +root}:
          tr.sr.true(V, o, h, root, a, b, v, w, hp)
    case False{}:
      {==}

def tr.cr.true(-V: Data, +o: Nat, +h: Nat, +root: Nd(V), +a: U32, +b: U32, +w: {P.wf(V, L(V, root)) == True{} : Bool}, +hp: {pok(V, root) == True{} : Bool}) -> {TL(V, T.MapleTree.join(U32, V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), hi(V, root, h, b, probe(V, root, b), o))) == P.app(V, P.below(V, L(V, root), a), P.above(V, L(V, root), b)) : P.Es(V)}:
  %Equal.sym(P.Es(V), TL(V, T.MapleTree.join(U32, V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), hi(V, root, h, b, probe(V, root, b), o))), P.app(V, TL(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o)), TL(V, hi(V, root, h, b, probe(V, root, b), o))), tr.join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), hi(V, root, h, b, probe(V, root, b), o))) : {_ == P.app(V, P.below(V, L(V, root), a), P.above(V, L(V, root), b)) : P.Es(V)}
  %Equal.sym(P.Es(V), TL(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o)), P.below(V, L(V, root), a), tr.lo(V, root, h, a, N.MapleNil{}, o, w, hp)) : {P.app(V, _, TL(V, hi(V, root, h, b, probe(V, root, b), o))) == P.app(V, P.below(V, L(V, root), a), P.above(V, L(V, root), b)) : P.Es(V)}
  %Equal.sym(P.Es(V), TL(V, hi(V, root, h, b, probe(V, root, b), o)), P.above(V, L(V, root), b), tr.hi(V, root, h, b, o, w, hp)) : {P.app(V, P.below(V, L(V, root), a), _) == P.app(V, P.below(V, L(V, root), a), P.above(V, L(V, root), b)) : P.Es(V)}
  {==}

def tr.cr.go(ok: Bool, -V: Data, +t: Tr(V), +a: U32, +b: U32, +w: {P.wf(V, TL(V, t)) == True{} : Bool}, +hp: {tpok(V, t) == True{} : Bool}) -> {TL(V, tcr.go(V, ok, t, a, b)) == P.mcr.go(V, ok, TL(V, t), a, b) : P.Es(V)}:
  match ok:
    case True{}:
      match t:
        case N.MapleTree{+o, +h, +root}:
          tr.cr.true(V, o, h, root, a, b, w, hp)
    case False{}:
      {==}

def tpok.sr.go(ok: Bool, -V: Data, +t: Tr(V), +a: U32, +b: U32, +v: V, +hp: {tpok(V, t) == True{} : Bool}) -> {tpok(V, tsr.go(V, ok, t, a, b, v)) == True{} : Bool}:
  match ok:
    case True{}:
      match t:
        case N.MapleTree{+o, +h, +root}:
          tpok.join(V, T.MapleTree.join(U32, V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v)), hi(V, root, h, b, probe(V, root, b), o), tpok.join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), single(V, o, a, b, v), tpok.lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o, hp, {==}), {==}), tpok.hi(V, root, h, b, probe(V, root, b), o, hp))
    case False{}:
      hp

def tpok.cr.go(ok: Bool, -V: Data, +t: Tr(V), +a: U32, +b: U32, +hp: {tpok(V, t) == True{} : Bool}) -> {tpok(V, tcr.go(V, ok, t, a, b)) == True{} : Bool}:
  match ok:
    case True{}:
      match t:
        case N.MapleTree{+o, +h, +root}:
          tpok.join(V, lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o), hi(V, root, h, b, probe(V, root, b), o), tpok.lo(V, root, h, a, N.MapleNil{}, probe(V, root, a), o, hp, {==}), tpok.hi(V, root, h, b, probe(V, root, b), o, hp))
    case False{}:
      hp

# set_range and clear_range, on a valid tree: contents and validity
def tr.set_range(-V: Data, +t: Tr(V), +a: U32, +b: U32, +v: V, +e: {X.Maple32.valid(V, t) == True{} : Bool}) -> {TL(V, X.Maple32.set_range(V, t, a, b, v)) == P.msr(V, TL(V, t), a, b, v) : P.Es(V)}:
  tr.sr.go(O.ule(a, b), V, t, a, b, v, tr.valid_wf(V, t, e), tr.valid_pok(V, t, e))

def tr.clear_range(-V: Data, +t: Tr(V), +a: U32, +b: U32, +e: {X.Maple32.valid(V, t) == True{} : Bool}) -> {TL(V, X.Maple32.clear_range(V, t, a, b)) == P.mcr(V, TL(V, t), a, b) : P.Es(V)}:
  tr.cr.go(O.ule(a, b), V, t, a, b, tr.valid_wf(V, t, e), tr.valid_pok(V, t, e))

def wf.rw(-V: Data, -xs: P.Es(V), -ys: P.Es(V), +e: {xs == ys : P.Es(V)}, +h: {P.wf(V, ys) == True{} : Bool}) -> {P.wf(V, xs) == True{} : Bool}:
  %Equal.sym(P.Es(V), xs, ys, e) : {P.wf(V, _) == True{} : Bool}
  h

def tr.valid_set_range(-V: Data, +t: Tr(V), +a: U32, +b: U32, +v: V, +e: {X.Maple32.valid(V, t) == True{} : Bool}) -> {X.Maple32.valid(V, X.Maple32.set_range(V, t, a, b, v)) == True{} : Bool}:
  tr.valid_intro(V, X.Maple32.set_range(V, t, a, b, v), wf.rw(V, TL(V, X.Maple32.set_range(V, t, a, b, v)), P.msr(V, TL(V, t), a, b, v), tr.set_range(V, t, a, b, v, e), P.wf.set_range(V, TL(V, t), a, b, v, tr.valid_wf(V, t, e))), tpok.sr.go(O.ule(a, b), V, t, a, b, v, tr.valid_pok(V, t, e)))

def tr.valid_clear_range(-V: Data, +t: Tr(V), +a: U32, +b: U32, +e: {X.Maple32.valid(V, t) == True{} : Bool}) -> {X.Maple32.valid(V, X.Maple32.clear_range(V, t, a, b)) == True{} : Bool}:
  tr.valid_intro(V, X.Maple32.clear_range(V, t, a, b), wf.rw(V, TL(V, X.Maple32.clear_range(V, t, a, b)), P.mcr(V, TL(V, t), a, b), tr.clear_range(V, t, a, b, e), P.wf.clear_range(V, TL(V, t), a, b, tr.valid_wf(V, t, e))), tpok.cr.go(O.ule(a, b), V, t, a, b, tr.valid_pok(V, t, e)))

# Lookups follow the model

def nload(-V: Data, +n: Nd(V), +i: U32) -> Maybe<&2, V>:
  N.MapleNode.load(~U32, ~U32.cmp, V, n, i, probe(V, n, i))

def nfind(-V: Data, +n: Nd(V), +i: U32) -> Maybe<&2, P.Ent(V)>:
  N.MapleNode.find(~U32, ~U32.cmp, V, n, i, probe(V, n, i))

def nnext(-V: Data, +n: Nd(V), +i: U32) -> Maybe<&2, P.Ent(V)>:
  N.MapleNode.next(~U32, ~U32.cmp, V, n, i, probe(V, n, i))

def nprev(-V: Data, +n: Nd(V), +i: U32, sib: Nd(V)) -> Maybe<&2, P.Ent(V)>:
  N.MapleNode.prev(~U32, ~U32.cmp, V, n, i, probe(V, n, i), sib)

# below the pivot: the rest holds nothing at i
def nd.load.ge(-V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +i: U32, +w: {P.wf(V, P.app(V, L(V, ch), L(V, r))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +ge: {O.ule(i, p) == True{} : Bool}, +ihc: {nload(V, ch, i) == P.mload(V, L(V, ch), i) : Maybe<&2, V>}) -> {nload(V, ch, i) == P.mload(V, P.app(V, L(V, ch), L(V, r)), i) : Maybe<&2, V>}:
  %Equal.sym(Maybe<&2, V>, P.mload(V, P.app(V, L(V, ch), L(V, r)), i), P.orv(V, P.mload(V, L(V, ch), i), P.mload(V, L(V, r), i)), P.mload.app(V, L(V, ch), L(V, r), i)) : {nload(V, ch, i) == _ : Maybe<&2, V>}
  %Equal.sym(Maybe<&2, V>, P.mload(V, L(V, r), i), None{}, P.mload.none_aft(V, L(V, r), p, i, ch.aft(V, p, ch, r, w, hp), ge)) : {nload(V, ch, i) == P.orv(V, P.mload(V, L(V, ch), i), _) : Maybe<&2, V>}
  %Equal.sym(Maybe<&2, V>, P.orv(V, P.mload(V, L(V, ch), i), None{}), P.mload(V, L(V, ch), i), P.orv.none(V, P.mload(V, L(V, ch), i))) : {nload(V, ch, i) == _ : Maybe<&2, V>}
  ihc

# above the pivot: the child holds nothing at i
def nd.load.lt(-V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +i: U32, +w: {P.wf(V, P.app(V, L(V, ch), L(V, r))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +lt: {O.ult(p, i) == True{} : Bool}, +ihr: {nload(V, r, i) == P.mload(V, L(V, r), i) : Maybe<&2, V>}) -> {nload(V, r, i) == P.mload(V, P.app(V, L(V, ch), L(V, r)), i) : Maybe<&2, V>}:
  %Equal.sym(Maybe<&2, V>, P.mload(V, P.app(V, L(V, ch), L(V, r)), i), P.orv(V, P.mload(V, L(V, ch), i), P.mload(V, L(V, r), i)), P.mload.app(V, L(V, ch), L(V, r), i)) : {nload(V, r, i) == _ : Maybe<&2, V>}
  %Equal.sym(Maybe<&2, V>, P.mload(V, L(V, ch), i), None{}, P.mload.none_le(V, L(V, ch), p, i, ch.lasts(V, p, ch, r, w, hp), lt)) : {nload(V, r, i) == P.orv(V, _, P.mload(V, L(V, r), i)) : Maybe<&2, V>}
  ihr

def nd.load.slot(c: Cmp, -V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +i: U32, +e: {U32.cmp(p, i) == c : Cmp}, +w: {P.wf(V, P.app(V, L(V, ch), L(V, r))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +ihc: {nload(V, ch, i) == P.mload(V, L(V, ch), i) : Maybe<&2, V>}, +ihr: {nload(V, r, i) == P.mload(V, L(V, r), i) : Maybe<&2, V>}) -> {N.MapleNode.load(~U32, ~U32.cmp, V, N.MapleSlot{p, ch, r}, i, c) == P.mload(V, P.app(V, L(V, ch), L(V, r)), i) : Maybe<&2, V>}:
  match c:
    case LT{}:
      nd.load.lt(V, p, ch, r, i, w, hp, cmp.lt_lt(p, i, e), ihr)
    case EQ{}:
      nd.load.ge(V, p, ch, r, i, w, hp, UO.u32_not_lt(p, i, cmp.not_lt_eq(p, i, e)), ihc)
    case GT{}:
      nd.load.ge(V, p, ch, r, i, w, hp, UO.u32_not_lt(p, i, cmp.not_lt_gt(p, i, e)), ihc)

def nd.load(-V: Data, n: Nd(V), +i: U32, +w: {P.wf(V, L(V, n)) == True{} : Bool}, +hp: {pok(V, n) == True{} : Bool}) -> {nload(V, n, i) == P.mload(V, L(V, n), i) : Maybe<&2, V>}:
  match n:
    case N.MapleLeaf{es}:
      {==}
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +ch, +r}:
      nd.load.slot(U32.cmp(p, i), V, p, ch, r, i, {==}, w, hp, nd.load(V, ch, i, P.wf.app_l(V, L(V, ch), L(V, r), w), pk.c(V, p, ch, r, hp)), nd.load(V, r, i, P.wf.app_r(V, L(V, ch), L(V, r), w), pk.r(V, p, ch, r, hp)))

def head.app(-V: Data, xs: P.Es(V), -ys: P.Es(V), -q: U32, +e: {P.lkey(V, xs) == Some{q} : Maybe<&2, U32>}) -> {List.head(&2, P.Ent(V), P.app(V, xs, ys)) == List.head(&2, P.Ent(V), xs) : Maybe<&2, P.Ent(V)>}:
  match xs:
    case Nil{}:
      Empty.absurd({List.head(&2, P.Ent(V), ys) == None{} : Maybe<&2, P.Ent(V)>}, O.ab.none_some(U32, q, e))
    case Con{x, r}:
      {==}

def nd.first_entry(-V: Data, n: Nd(V), +hp: {pok(V, n) == True{} : Bool}) -> {N.MapleNode.first_entry(U32, V, n) == List.head(&2, P.Ent(V), L(V, n)) : Maybe<&2, P.Ent(V)>}:
  match n:
    case N.MapleLeaf{es}:
      {==}
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +c, +r}:
      Equal.trans(Maybe<&2, P.Ent(V)>, N.MapleNode.first_entry(U32, V, c), List.head(&2, P.Ent(V), L(V, c)), List.head(&2, P.Ent(V), P.app(V, L(V, c), L(V, r))), nd.first_entry(V, c, pk.c(V, p, c, r, hp)), Equal.sym(Maybe<&2, P.Ent(V)>, List.head(&2, P.Ent(V), P.app(V, L(V, c), L(V, r))), List.head(&2, P.Ent(V), L(V, c)), head.app(V, L(V, c), L(V, r), p, ch.key(V, p, c, r, hp))))

def nd.find.ge(-V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +i: U32, +w: {P.wf(V, P.app(V, L(V, ch), L(V, r))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +ge: {O.ule(i, p) == True{} : Bool}, +ihc: {nfind(V, ch, i) == P.mfind(V, L(V, ch), i) : Maybe<&2, P.Ent(V)>}) -> {P.later(V, nfind(V, ch, i), N.MapleNode.first_entry(U32, V, r)) == P.mfind(V, P.app(V, L(V, ch), L(V, r)), i) : Maybe<&2, P.Ent(V)>}:
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mfind(V, P.app(V, L(V, ch), L(V, r)), i), P.later(V, P.mfind(V, L(V, ch), i), P.mfind(V, L(V, r), i)), P.mfind.app(V, L(V, ch), L(V, r), i)) : {P.later(V, nfind(V, ch, i), N.MapleNode.first_entry(U32, V, r)) == _ : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mfind(V, L(V, r), i), List.head(&2, P.Ent(V), L(V, r)), P.mfind.head(V, L(V, r), p, i, ch.aft(V, p, ch, r, w, hp), P.wf.app_r(V, L(V, ch), L(V, r), w), ge)) : {P.later(V, nfind(V, ch, i), N.MapleNode.first_entry(U32, V, r)) == P.later(V, P.mfind(V, L(V, ch), i), _) : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, N.MapleNode.first_entry(U32, V, r), List.head(&2, P.Ent(V), L(V, r)), nd.first_entry(V, r, pk.r(V, p, ch, r, hp))) : {P.later(V, nfind(V, ch, i), _) == P.later(V, P.mfind(V, L(V, ch), i), List.head(&2, P.Ent(V), L(V, r))) : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, nfind(V, ch, i), P.mfind(V, L(V, ch), i), ihc) : {P.later(V, _, List.head(&2, P.Ent(V), L(V, r))) == P.later(V, P.mfind(V, L(V, ch), i), List.head(&2, P.Ent(V), L(V, r))) : Maybe<&2, P.Ent(V)>}
  {==}

def nd.find.lt(-V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +i: U32, +w: {P.wf(V, P.app(V, L(V, ch), L(V, r))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +lt: {O.ult(p, i) == True{} : Bool}, +ihr: {nfind(V, r, i) == P.mfind(V, L(V, r), i) : Maybe<&2, P.Ent(V)>}) -> {nfind(V, r, i) == P.mfind(V, P.app(V, L(V, ch), L(V, r)), i) : Maybe<&2, P.Ent(V)>}:
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mfind(V, P.app(V, L(V, ch), L(V, r)), i), P.later(V, P.mfind(V, L(V, ch), i), P.mfind(V, L(V, r), i)), P.mfind.app(V, L(V, ch), L(V, r), i)) : {nfind(V, r, i) == _ : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mfind(V, L(V, ch), i), None{}, P.mfind.none_le(V, L(V, ch), p, i, ch.lasts(V, p, ch, r, w, hp), lt)) : {nfind(V, r, i) == P.later(V, _, P.mfind(V, L(V, r), i)) : Maybe<&2, P.Ent(V)>}
  ihr

def nd.find.slot(c: Cmp, -V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +i: U32, +e: {U32.cmp(p, i) == c : Cmp}, +w: {P.wf(V, P.app(V, L(V, ch), L(V, r))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +ihc: {nfind(V, ch, i) == P.mfind(V, L(V, ch), i) : Maybe<&2, P.Ent(V)>}, +ihr: {nfind(V, r, i) == P.mfind(V, L(V, r), i) : Maybe<&2, P.Ent(V)>}) -> {N.MapleNode.find(~U32, ~U32.cmp, V, N.MapleSlot{p, ch, r}, i, c) == P.mfind(V, P.app(V, L(V, ch), L(V, r)), i) : Maybe<&2, P.Ent(V)>}:
  match c:
    case LT{}:
      nd.find.lt(V, p, ch, r, i, w, hp, cmp.lt_lt(p, i, e), ihr)
    case EQ{}:
      nd.find.ge(V, p, ch, r, i, w, hp, UO.u32_not_lt(p, i, cmp.not_lt_eq(p, i, e)), ihc)
    case GT{}:
      nd.find.ge(V, p, ch, r, i, w, hp, UO.u32_not_lt(p, i, cmp.not_lt_gt(p, i, e)), ihc)

def nd.find(-V: Data, n: Nd(V), +i: U32, +w: {P.wf(V, L(V, n)) == True{} : Bool}, +hp: {pok(V, n) == True{} : Bool}) -> {nfind(V, n, i) == P.mfind(V, L(V, n), i) : Maybe<&2, P.Ent(V)>}:
  match n:
    case N.MapleLeaf{es}:
      {==}
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +ch, +r}:
      nd.find.slot(U32.cmp(p, i), V, p, ch, r, i, {==}, w, hp, nd.find(V, ch, i, P.wf.app_l(V, L(V, ch), L(V, r), w), pk.c(V, p, ch, r, hp)), nd.find(V, r, i, P.wf.app_r(V, L(V, ch), L(V, r), w), pk.r(V, p, ch, r, hp)))

def nd.next.gt(-V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +i: U32, +w: {P.wf(V, P.app(V, L(V, ch), L(V, r))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +ge: {O.ule(i, p) == True{} : Bool}, +ihc: {nnext(V, ch, i) == P.mnext(V, L(V, ch), i) : Maybe<&2, P.Ent(V)>}) -> {P.later(V, nnext(V, ch, i), N.MapleNode.first_entry(U32, V, r)) == P.mnext(V, P.app(V, L(V, ch), L(V, r)), i) : Maybe<&2, P.Ent(V)>}:
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mnext(V, P.app(V, L(V, ch), L(V, r)), i), P.later(V, P.mnext(V, L(V, ch), i), P.mnext(V, L(V, r), i)), P.mnext.app(V, L(V, ch), L(V, r), i)) : {P.later(V, nnext(V, ch, i), N.MapleNode.first_entry(U32, V, r)) == _ : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mnext(V, L(V, r), i), List.head(&2, P.Ent(V), L(V, r)), P.mnext.head(V, L(V, r), p, i, ch.aft(V, p, ch, r, w, hp), ge)) : {P.later(V, nnext(V, ch, i), N.MapleNode.first_entry(U32, V, r)) == P.later(V, P.mnext(V, L(V, ch), i), _) : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, N.MapleNode.first_entry(U32, V, r), List.head(&2, P.Ent(V), L(V, r)), nd.first_entry(V, r, pk.r(V, p, ch, r, hp))) : {P.later(V, nnext(V, ch, i), _) == P.later(V, P.mnext(V, L(V, ch), i), List.head(&2, P.Ent(V), L(V, r))) : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, nnext(V, ch, i), P.mnext(V, L(V, ch), i), ihc) : {P.later(V, _, List.head(&2, P.Ent(V), L(V, r))) == P.later(V, P.mnext(V, L(V, ch), i), List.head(&2, P.Ent(V), L(V, r))) : Maybe<&2, P.Ent(V)>}
  {==}

def nd.next.le(-V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +i: U32, +w: {P.wf(V, P.app(V, L(V, ch), L(V, r))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +le: {O.ule(p, i) == True{} : Bool}, +ihr: {nnext(V, r, i) == P.mnext(V, L(V, r), i) : Maybe<&2, P.Ent(V)>}) -> {nnext(V, r, i) == P.mnext(V, P.app(V, L(V, ch), L(V, r)), i) : Maybe<&2, P.Ent(V)>}:
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mnext(V, P.app(V, L(V, ch), L(V, r)), i), P.later(V, P.mnext(V, L(V, ch), i), P.mnext(V, L(V, r), i)), P.mnext.app(V, L(V, ch), L(V, r), i)) : {nnext(V, r, i) == _ : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mnext(V, L(V, ch), i), None{}, P.mnext.none_le(V, L(V, ch), p, i, ch.lasts(V, p, ch, r, w, hp), P.wf.app_l(V, L(V, ch), L(V, r), w), le)) : {nnext(V, r, i) == P.later(V, _, P.mnext(V, L(V, r), i)) : Maybe<&2, P.Ent(V)>}
  ihr

def nd.next.slot(c: Cmp, -V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +i: U32, +e: {U32.cmp(p, i) == c : Cmp}, +w: {P.wf(V, P.app(V, L(V, ch), L(V, r))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +ihc: {nnext(V, ch, i) == P.mnext(V, L(V, ch), i) : Maybe<&2, P.Ent(V)>}, +ihr: {nnext(V, r, i) == P.mnext(V, L(V, r), i) : Maybe<&2, P.Ent(V)>}) -> {N.MapleNode.next(~U32, ~U32.cmp, V, N.MapleSlot{p, ch, r}, i, c) == P.mnext(V, P.app(V, L(V, ch), L(V, r)), i) : Maybe<&2, P.Ent(V)>}:
  match c:
    case GT{}:
      nd.next.gt(V, p, ch, r, i, w, hp, cmp.gt_le(p, i, e), ihc)
    case LT{}:
      nd.next.le(V, p, ch, r, i, w, hp, cmp.le_lt(p, i, e), ihr)
    case EQ{}:
      nd.next.le(V, p, ch, r, i, w, hp, cmp.le_eq(p, i, e), ihr)

def nd.next(-V: Data, n: Nd(V), +i: U32, +w: {P.wf(V, L(V, n)) == True{} : Bool}, +hp: {pok(V, n) == True{} : Bool}) -> {nnext(V, n, i) == P.mnext(V, L(V, n), i) : Maybe<&2, P.Ent(V)>}:
  match n:
    case N.MapleLeaf{es}:
      {==}
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +ch, +r}:
      nd.next.slot(U32.cmp(p, i), V, p, ch, r, i, {==}, w, hp, nd.next(V, ch, i, P.wf.app_l(V, L(V, ch), L(V, r), w), pk.c(V, p, ch, r, hp)), nd.next(V, r, i, P.wf.app_r(V, L(V, ch), L(V, r), w), pk.r(V, p, ch, r, hp)))

# the last entry of a node is the last of its contents
def nd.last_entry.go(-V: Data, m: Maybe<&2, U32>, +n: Nd(V), +em: {nlk(V, n) == m : Maybe<&2, U32>}, +w: {P.wf(V, L(V, n)) == True{} : Bool}, +hp: {pok(V, n) == True{} : Bool}) -> {N.MapleNode.last_entry.go(~U32, ~U32.cmp, V, n, m) == P.elast(V, L(V, n)) : Maybe<&2, P.Ent(V)>}:
  match m:
    case None{}:
      %Equal.sym(P.Es(V), L(V, n), Nil{}, nd.none_empty(V, n, em)) : {None{} == P.elast(V, _) : Maybe<&2, P.Ent(V)>}
      {==}
    case Some{+k}:
      Equal.trans(Maybe<&2, P.Ent(V)>, nfind(V, n, k), P.mfind(V, L(V, n), k), P.elast(V, L(V, n)), nd.find(V, n, k, w, hp), P.mfind.last(V, L(V, n), k, w, Equal.trans(Maybe<&2, U32>, P.lkey(V, L(V, n)), nlk(V, n), Some{k}, Equal.sym(Maybe<&2, U32>, nlk(V, n), P.lkey(V, L(V, n)), nlk.L(V, n, hp)), em)))

def nd.last_entry(-V: Data, +n: Nd(V), +w: {P.wf(V, L(V, n)) == True{} : Bool}, +hp: {pok(V, n) == True{} : Bool}) -> {N.MapleNode.last_entry(~U32, ~U32.cmp, V, n) == P.elast(V, L(V, n)) : Maybe<&2, P.Ent(V)>}:
  nd.last_entry.go(V, nlk(V, n), n, {==}, w, hp)

# prev: the last entry ending before i in sib ++ n

def later3(-V: Data, a: Maybe<&2, P.Ent(V)>, +b: Maybe<&2, P.Ent(V)>, -y: P.Ent(V), -n: Maybe<&2, P.Ent(V)>) -> {P.later(V, P.later(V, a, P.later(V, b, Some{y})), n) == P.later(V, a, P.later(V, b, Some{y})) : Maybe<&2, P.Ent(V)>}:
  match a:
    case Some{x}:
      {==}
    case None{}:
      P.later.some_r(V, b, y, n)

def prev.absorb.go(-V: Data, xs: P.Es(V), +rs: P.Es(V), -n: Maybe<&2, P.Ent(V)>, +i: U32, -q: U32, +e: {P.lkey(V, xs) == Some{q} : Maybe<&2, U32>}) -> {P.later(V, P.later(V, P.mprev(V, rs, i), P.elast(V, xs)), n) == P.later(V, P.mprev(V, rs, i), P.elast(V, xs)) : Maybe<&2, P.Ent(V)>}:
  match xs:
    case Nil{}:
      Empty.absurd({P.later(V, P.later(V, P.mprev(V, rs, i), None{}), n) == P.later(V, P.mprev(V, rs, i), None{}) : Maybe<&2, P.Ent(V)>}, O.ab.none_some(U32, q, e))
    case Con{y, ys}:
      later3(V, P.mprev(V, rs, i), P.elast(V, ys), y, n)

# a nonempty xs ending before i: prev over xs ++ rs is never None, so a
# later fallback n is not used
def prev.absorb(-V: Data, +xs: P.Es(V), +rs: P.Es(V), -n: Maybe<&2, P.Ent(V)>, +i: U32, -q: U32, +e: {P.lkey(V, xs) == Some{q} : Maybe<&2, U32>}, +h: {P.lasts_lt(V, xs, i) == True{} : Bool}) -> {P.later(V, P.mprev(V, P.app(V, xs, rs), i), n) == P.mprev(V, P.app(V, xs, rs), i) : Maybe<&2, P.Ent(V)>}:
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mprev(V, P.app(V, xs, rs), i), P.later(V, P.mprev(V, rs, i), P.mprev(V, xs, i)), P.mprev.app(V, xs, rs, i)) : {P.later(V, _, n) == _ : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mprev(V, xs, i), P.elast(V, xs), P.mprev.all(V, xs, i, h)) : {P.later(V, P.later(V, P.mprev(V, rs, i), _), n) == P.later(V, P.mprev(V, rs, i), _) : Maybe<&2, P.Ent(V)>}
  prev.absorb.go(V, xs, rs, n, i, q, e)

def nd.prev.leaf(-V: Data, +es: P.Es(V), +sib: Nd(V), +i: U32, +w: {P.wf(V, L(V, sib)) == True{} : Bool}, +hs: {pok(V, sib) == True{} : Bool}, +ls: {P.lasts_lt(V, L(V, sib), i) == True{} : Bool}) -> {P.later(V, P.mprev(V, es, i), N.MapleNode.last_entry(~U32, ~U32.cmp, V, sib)) == P.mprev(V, P.app(V, L(V, sib), es), i) : Maybe<&2, P.Ent(V)>}:
  %Equal.sym(Maybe<&2, P.Ent(V)>, N.MapleNode.last_entry(~U32, ~U32.cmp, V, sib), P.elast(V, L(V, sib)), nd.last_entry(V, sib, w, hs)) : {P.later(V, P.mprev(V, es, i), _) == P.mprev(V, P.app(V, L(V, sib), es), i) : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mprev(V, P.app(V, L(V, sib), es), i), P.later(V, P.mprev(V, es, i), P.mprev(V, L(V, sib), i)), P.mprev.app(V, L(V, sib), es, i)) : {P.later(V, P.mprev(V, es, i), P.elast(V, L(V, sib))) == _ : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mprev(V, L(V, sib), i), P.elast(V, L(V, sib)), P.mprev.all(V, L(V, sib), i, ls)) : {P.later(V, P.mprev(V, es, i), P.elast(V, L(V, sib))) == P.later(V, P.mprev(V, es, i), _) : Maybe<&2, P.Ent(V)>}
  {==}

def nd.prev.nil(-V: Data, +sib: Nd(V), +i: U32, +w: {P.wf(V, L(V, sib)) == True{} : Bool}, +hs: {pok(V, sib) == True{} : Bool}, +ls: {P.lasts_lt(V, L(V, sib), i) == True{} : Bool}) -> {N.MapleNode.last_entry(~U32, ~U32.cmp, V, sib) == P.mprev(V, P.app(V, L(V, sib), Nil{}), i) : Maybe<&2, P.Ent(V)>}:
  %Equal.sym(P.Es(V), P.app(V, L(V, sib), Nil{}), L(V, sib), P.app.nil(V, L(V, sib))) : {N.MapleNode.last_entry(~U32, ~U32.cmp, V, sib) == P.mprev(V, _, i) : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mprev(V, L(V, sib), i), P.elast(V, L(V, sib)), P.mprev.all(V, L(V, sib), i, ls)) : {N.MapleNode.last_entry(~U32, ~U32.cmp, V, sib) == _ : Maybe<&2, P.Ent(V)>}
  nd.last_entry(V, sib, w, hs)

def nd.prev.lt(-V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +i: U32, +sib: Nd(V), +w: {P.wf(V, P.app(V, L(V, sib), P.app(V, L(V, ch), L(V, r)))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +lt: {O.ult(p, i) == True{} : Bool}, ihr: {P.lasts_lt(V, L(V, ch), i) == True{} : Bool} -> {nprev(V, r, i, ch) == P.mprev(V, P.app(V, L(V, ch), L(V, r)), i) : Maybe<&2, P.Ent(V)>}) -> {nprev(V, r, i, ch) == P.mprev(V, P.app(V, L(V, sib), P.app(V, L(V, ch), L(V, r))), i) : Maybe<&2, P.Ent(V)>}:
  +wc = P.wf.app_r(V, L(V, sib), P.app(V, L(V, ch), L(V, r)), w)
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mprev(V, P.app(V, L(V, sib), P.app(V, L(V, ch), L(V, r))), i), P.later(V, P.mprev(V, P.app(V, L(V, ch), L(V, r)), i), P.mprev(V, L(V, sib), i)), P.mprev.app(V, L(V, sib), P.app(V, L(V, ch), L(V, r)), i)) : {nprev(V, r, i, ch) == _ : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.later(V, P.mprev(V, P.app(V, L(V, ch), L(V, r)), i), P.mprev(V, L(V, sib), i)), P.mprev(V, P.app(V, L(V, ch), L(V, r)), i), prev.absorb(V, L(V, ch), L(V, r), P.mprev(V, L(V, sib), i), i, p, ch.key(V, p, ch, r, hp), P.lasts.lt_of_le(V, L(V, ch), p, i, ch.lasts(V, p, ch, r, wc, hp), lt))) : {nprev(V, r, i, ch) == _ : Maybe<&2, P.Ent(V)>}
  ihr(P.lasts.lt_of_le(V, L(V, ch), p, i, ch.lasts(V, p, ch, r, wc, hp), lt))

def nd.prev.ge(-V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +i: U32, +sib: Nd(V), +w: {P.wf(V, P.app(V, L(V, sib), P.app(V, L(V, ch), L(V, r)))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +hs: {pok(V, sib) == True{} : Bool}, +ls: {P.lasts_lt(V, L(V, sib), i) == True{} : Bool}, +ge: {O.ule(i, p) == True{} : Bool}, +ihc: {nprev(V, ch, i, N.MapleNil{}) == P.mprev(V, L(V, ch), i) : Maybe<&2, P.Ent(V)>}) -> {P.later(V, nprev(V, ch, i, N.MapleNil{}), N.MapleNode.last_entry(~U32, ~U32.cmp, V, sib)) == P.mprev(V, P.app(V, L(V, sib), P.app(V, L(V, ch), L(V, r))), i) : Maybe<&2, P.Ent(V)>}:
  +wc = P.wf.app_r(V, L(V, sib), P.app(V, L(V, ch), L(V, r)), w)
  %Equal.sym(Maybe<&2, P.Ent(V)>, N.MapleNode.last_entry(~U32, ~U32.cmp, V, sib), P.elast(V, L(V, sib)), nd.last_entry(V, sib, P.wf.app_l(V, L(V, sib), P.app(V, L(V, ch), L(V, r)), w), hs)) : {P.later(V, nprev(V, ch, i, N.MapleNil{}), _) == P.mprev(V, P.app(V, L(V, sib), P.app(V, L(V, ch), L(V, r))), i) : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, nprev(V, ch, i, N.MapleNil{}), P.mprev(V, L(V, ch), i), ihc) : {P.later(V, _, P.elast(V, L(V, sib))) == P.mprev(V, P.app(V, L(V, sib), P.app(V, L(V, ch), L(V, r))), i) : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mprev(V, P.app(V, L(V, sib), P.app(V, L(V, ch), L(V, r))), i), P.later(V, P.mprev(V, P.app(V, L(V, ch), L(V, r)), i), P.mprev(V, L(V, sib), i)), P.mprev.app(V, L(V, sib), P.app(V, L(V, ch), L(V, r)), i)) : {P.later(V, P.mprev(V, L(V, ch), i), P.elast(V, L(V, sib))) == _ : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mprev(V, P.app(V, L(V, ch), L(V, r)), i), P.later(V, P.mprev(V, L(V, r), i), P.mprev(V, L(V, ch), i)), P.mprev.app(V, L(V, ch), L(V, r), i)) : {P.later(V, P.mprev(V, L(V, ch), i), P.elast(V, L(V, sib))) == P.later(V, _, P.mprev(V, L(V, sib), i)) : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mprev(V, L(V, r), i), None{}, P.mprev.none_aft(V, L(V, r), p, i, ch.aft(V, p, ch, r, wc, hp), P.wf.app_r(V, L(V, ch), L(V, r), wc), ge)) : {P.later(V, P.mprev(V, L(V, ch), i), P.elast(V, L(V, sib))) == P.later(V, P.later(V, _, P.mprev(V, L(V, ch), i)), P.mprev(V, L(V, sib), i)) : Maybe<&2, P.Ent(V)>}
  %Equal.sym(Maybe<&2, P.Ent(V)>, P.mprev(V, L(V, sib), i), P.elast(V, L(V, sib)), P.mprev.all(V, L(V, sib), i, ls)) : {P.later(V, P.mprev(V, L(V, ch), i), P.elast(V, L(V, sib))) == P.later(V, P.later(V, None{}, P.mprev(V, L(V, ch), i)), _) : Maybe<&2, P.Ent(V)>}
  {==}

def nd.prev.slot(c: Cmp, -V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +i: U32, +sib: Nd(V), +e: {U32.cmp(p, i) == c : Cmp}, +w: {P.wf(V, P.app(V, L(V, sib), P.app(V, L(V, ch), L(V, r)))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +hs: {pok(V, sib) == True{} : Bool}, +ls: {P.lasts_lt(V, L(V, sib), i) == True{} : Bool}, +ihc: {nprev(V, ch, i, N.MapleNil{}) == P.mprev(V, L(V, ch), i) : Maybe<&2, P.Ent(V)>}, ihr: {P.lasts_lt(V, L(V, ch), i) == True{} : Bool} -> {nprev(V, r, i, ch) == P.mprev(V, P.app(V, L(V, ch), L(V, r)), i) : Maybe<&2, P.Ent(V)>}) -> {N.MapleNode.prev(~U32, ~U32.cmp, V, N.MapleSlot{p, ch, r}, i, c, sib) == P.mprev(V, P.app(V, L(V, sib), P.app(V, L(V, ch), L(V, r))), i) : Maybe<&2, P.Ent(V)>}:
  match c:
    case LT{}:
      nd.prev.lt(V, p, ch, r, i, sib, w, hp, cmp.lt_lt(p, i, e), ihr)
    case EQ{}:
      nd.prev.ge(V, p, ch, r, i, sib, w, hp, hs, ls, UO.u32_not_lt(p, i, cmp.not_lt_eq(p, i, e)), ihc)
    case GT{}:
      nd.prev.ge(V, p, ch, r, i, sib, w, hp, hs, ls, UO.u32_not_lt(p, i, cmp.not_lt_gt(p, i, e)), ihc)

def nd.prev(-V: Data, n: Nd(V), +i: U32, +sib: Nd(V), +w: {P.wf(V, P.app(V, L(V, sib), L(V, n))) == True{} : Bool}, +hn: {pok(V, n) == True{} : Bool}, +hs: {pok(V, sib) == True{} : Bool}, +ls: {P.lasts_lt(V, L(V, sib), i) == True{} : Bool}) -> {nprev(V, n, i, sib) == P.mprev(V, P.app(V, L(V, sib), L(V, n)), i) : Maybe<&2, P.Ent(V)>}:
  match n:
    case N.MapleLeaf{+es}:
      nd.prev.leaf(V, es, sib, i, P.wf.app_l(V, L(V, sib), es, w), hs, ls)
    case N.MapleNil{}:
      nd.prev.nil(V, sib, i, P.wf.app_l(V, L(V, sib), Nil{}, w), hs, ls)
    case N.MapleSlot{+p, +ch, +r}:
      +wc = P.wf.app_r(V, L(V, sib), P.app(V, L(V, ch), L(V, r)), w)
      nd.prev.slot(U32.cmp(p, i), V, p, ch, r, i, sib, {==}, w, hn, hs, ls, nd.prev(V, ch, i, N.MapleNil{}, P.wf.app_l(V, L(V, ch), L(V, r), wc), pk.c(V, p, ch, r, hn), {==}, {==}), h => nd.prev(V, r, i, ch, wc, pk.r(V, p, ch, r, hn), pk.c(V, p, ch, r, hn), h))

# Lookups on a valid tree

def vw(-V: Data, +n: Nd(V), +e: {Bool.and(P.wf(V, L(V, n)), pok(V, n)) == True{} : Bool}) -> {P.wf(V, L(V, n)) == True{} : Bool}:
  O.bo.and_l(P.wf(V, L(V, n)), pok(V, n), e)

def vp(-V: Data, +n: Nd(V), +e: {Bool.and(P.wf(V, L(V, n)), pok(V, n)) == True{} : Bool}) -> {pok(V, n) == True{} : Bool}:
  O.bo.and_r(P.wf(V, L(V, n)), pok(V, n), e)

def tr.load(-V: Data, t: Tr(V), +i: U32, +e: {X.Maple32.valid(V, t) == True{} : Bool}) -> {X.Maple32.load(V, t, i) == P.mload(V, TL(V, t), i) : Maybe<&2, V>}:
  match t:
    case N.MapleTree{o, h, +n}:
      nd.load(V, n, i, vw(V, n, e), vp(V, n, e))

def tr.find(-V: Data, t: Tr(V), +i: U32, +e: {X.Maple32.valid(V, t) == True{} : Bool}) -> {X.Maple32.find(V, t, i) == P.mfind(V, TL(V, t), i) : Maybe<&2, P.Ent(V)>}:
  match t:
    case N.MapleTree{o, h, +n}:
      nd.find(V, n, i, vw(V, n, e), vp(V, n, e))

def tr.next(-V: Data, t: Tr(V), +i: U32, +e: {X.Maple32.valid(V, t) == True{} : Bool}) -> {X.Maple32.next(V, t, i) == P.mnext(V, TL(V, t), i) : Maybe<&2, P.Ent(V)>}:
  match t:
    case N.MapleTree{o, h, +n}:
      nd.next(V, n, i, vw(V, n, e), vp(V, n, e))

def tr.prev(-V: Data, t: Tr(V), +i: U32, +e: {X.Maple32.valid(V, t) == True{} : Bool}) -> {X.Maple32.prev(V, t, i) == P.mprev(V, TL(V, t), i) : Maybe<&2, P.Ent(V)>}:
  match t:
    case N.MapleTree{o, h, +n}:
      nd.prev(V, n, i, N.MapleNil{}, vw(V, n, e), vp(V, n, e), {==}, {==})

def lgo(-V: Data, m: Maybe<&2, P.Ent(V)>, +i: U32) -> Maybe<&2, P.Ent(V)>:
  X.Maple.lookup.go(~U32, ~U32.cmp, V, m, i)

def mlookup.none_aft(-V: Data, xs: P.Es(V), +k: U32, +i: U32, +h: {P.aft(V, k, xs) == True{} : Bool}, +g: {O.ule(i, k) == True{} : Bool}) -> {P.mlookup(V, xs, i) == None{} : Maybe<&2, P.Ent(V)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Equal.trans(Maybe<&2, P.Ent(V)>, P.pk(V, P.holds(V, x, i), x, P.mlookup(V, r, i)), P.mlookup(V, r, i), None{}, P.pk.false(V, P.holds(V, x, i), x, P.mlookup(V, r, i), O.bo.and_false_l(O.ule(P.fst(V, x), i), O.ule(i, P.lst(V, x)), UO.u32_lt_not_le(i, P.fst(V, x), UO.u32_le_lt_trans(i, k, P.fst(V, x), g, P.aft.head(V, k, x, r, h))))), mlookup.none_aft(V, r, k, i, P.aft.tail(V, k, x, r, h), g))

def lf.go(c: Bool, -V: Data, +x: P.Ent(V), +r: P.Es(V), +i: U32, +e: {O.ule(i, P.lst(V, x)) == c : Bool}, +w: {P.wf(V, Con{x, r}) == True{} : Bool}, +ih: {lgo(V, P.mfind(V, r, i), i) == P.mlookup(V, r, i) : Maybe<&2, P.Ent(V)>}) -> {lgo(V, P.pk(V, c, x, P.mfind(V, r, i)), i) == P.pk(V, P.holds(V, x, i), x, P.mlookup(V, r, i)) : Maybe<&2, P.Ent(V)>}:
  match c:
    case True{}:
      P.pk.cong(V, P.holds(V, x, i), x, None{}, P.mlookup(V, r, i), Equal.sym(Maybe<&2, P.Ent(V)>, P.mlookup(V, r, i), None{}, mlookup.none_aft(V, r, P.lst(V, x), i, P.wf.aft(V, x, r, w), e)))
    case False{}:
      Equal.trans(Maybe<&2, P.Ent(V)>, lgo(V, P.mfind(V, r, i), i), P.mlookup(V, r, i), P.pk(V, P.holds(V, x, i), x, P.mlookup(V, r, i)), ih, Equal.sym(Maybe<&2, P.Ent(V)>, P.pk(V, P.holds(V, x, i), x, P.mlookup(V, r, i)), P.mlookup(V, r, i), P.pk.false(V, P.holds(V, x, i), x, P.mlookup(V, r, i), O.bo.and_false_r(O.ule(P.fst(V, x), i), O.ule(i, P.lst(V, x)), e))))

# lookup is find, kept if it holds the index
def lf(-V: Data, xs: P.Es(V), +i: U32, +w: {P.wf(V, xs) == True{} : Bool}) -> {lgo(V, P.mfind(V, xs, i), i) == P.mlookup(V, xs, i) : Maybe<&2, P.Ent(V)>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      lf.go(O.ule(i, P.lst(V, x)), V, x, r, i, {==}, w, lf(V, r, i, P.wf.tail(V, x, r, w)))

def tr.lookup(-V: Data, +t: Tr(V), +i: U32, +e: {X.Maple32.valid(V, t) == True{} : Bool}) -> {X.Maple32.lookup(V, t, i) == P.mlookup(V, TL(V, t), i) : Maybe<&2, P.Ent(V)>}:
  %Equal.sym(Maybe<&2, P.Ent(V)>, X.Maple32.find(V, t, i), P.mfind(V, TL(V, t), i), tr.find(V, t, i, e)) : {lgo(V, _, i) == P.mlookup(V, TL(V, t), i) : Maybe<&2, P.Ent(V)>}
  lf(V, TL(V, t), i, tr.valid_wf(V, t, e))

# erase keeps a tree valid
def tr.valid_erase.go(-V: Data, m: Maybe<&2, P.Ent(V)>, +t: Tr(V), +e: {X.Maple32.valid(V, t) == True{} : Bool}) -> {X.Maple32.valid(V, X.Maple.erase.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, V, m, t)) == True{} : Bool}:
  match m:
    case None{}:
      e
    case Some{M.MapleEntry{+f, +l, +v}}:
      tr.valid_clear_range(V, t, f, l, e)

def tr.valid_erase(-V: Data, +t: Tr(V), +i: U32, +e: {X.Maple32.valid(V, t) == True{} : Bool}) -> {X.Maple32.valid(V, X.Maple32.erase(V, t, i)) == True{} : Bool}:
  tr.valid_erase.go(V, X.Maple32.lookup(V, t, i), t, e)

# The gap search follows the model

def gnode(-V: Data, +n: Nd(V), +st: M.MapleGap<U32>, +d: U32, +max: U32) -> M.MapleGap<U32>:
  G.MapleGap.node(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.add, V, n, st, G.MapleGap.probe(~U32, ~U32.cmp, V, n, st), d, max)

def gn.slot(c: Cmp, -V: Data, +p: U32, +ch: Nd(V), +r: Nd(V), +cur: U32, +d: U32, +max: U32, +e: {U32.cmp(p, cur) == c : Cmp}, +w: {P.wf(V, P.app(V, L(V, ch), L(V, r))) == True{} : Bool}, +hp: {pok(V, N.MapleSlot{p, ch, r}) == True{} : Bool}, +ihc: {gnode(V, ch, M.MapleGapScan{cur}, d, max) == P.gscan(V, L(V, ch), M.MapleGapScan{cur}, d, max) : M.MapleGap<U32>}, +ihr1: {gnode(V, r, M.MapleGapScan{cur}, d, max) == P.gscan(V, L(V, r), M.MapleGapScan{cur}, d, max) : M.MapleGap<U32>}, +ihr2: {gnode(V, r, gnode(V, ch, M.MapleGapScan{cur}, d, max), d, max) == P.gscan(V, L(V, r), gnode(V, ch, M.MapleGapScan{cur}, d, max), d, max) : M.MapleGap<U32>}) -> {G.MapleGap.node(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.add, V, N.MapleSlot{p, ch, r}, M.MapleGapScan{cur}, c, d, max) == P.gscan(V, P.app(V, L(V, ch), L(V, r)), M.MapleGapScan{cur}, d, max) : M.MapleGap<U32>}:
  match c:
    case LT{}:
      %Equal.sym(M.MapleGap<U32>, P.gscan(V, P.app(V, L(V, ch), L(V, r)), M.MapleGapScan{cur}, d, max), P.gscan(V, L(V, r), P.gscan(V, L(V, ch), M.MapleGapScan{cur}, d, max), d, max), P.gscan.app(V, L(V, ch), L(V, r), M.MapleGapScan{cur}, d, max)) : {gnode(V, r, M.MapleGapScan{cur}, d, max) == _ : M.MapleGap<U32>}
      %Equal.sym(M.MapleGap<U32>, P.gscan(V, L(V, ch), M.MapleGapScan{cur}, d, max), M.MapleGapScan{cur}, P.gscan.skip(V, L(V, ch), cur, d, max, P.lasts.lt_of_le(V, L(V, ch), p, cur, ch.lasts(V, p, ch, r, w, hp), cmp.lt_lt(p, cur, e)))) : {gnode(V, r, M.MapleGapScan{cur}, d, max) == P.gscan(V, L(V, r), _, d, max) : M.MapleGap<U32>}
      ihr1
    case EQ{}:
      %Equal.sym(M.MapleGap<U32>, P.gscan(V, P.app(V, L(V, ch), L(V, r)), M.MapleGapScan{cur}, d, max), P.gscan(V, L(V, r), P.gscan(V, L(V, ch), M.MapleGapScan{cur}, d, max), d, max), P.gscan.app(V, L(V, ch), L(V, r), M.MapleGapScan{cur}, d, max)) : {gnode(V, r, gnode(V, ch, M.MapleGapScan{cur}, d, max), d, max) == _ : M.MapleGap<U32>}
      %ihc : {gnode(V, r, gnode(V, ch, M.MapleGapScan{cur}, d, max), d, max) == P.gscan(V, L(V, r), _, d, max) : M.MapleGap<U32>}
      ihr2
    case GT{}:
      %Equal.sym(M.MapleGap<U32>, P.gscan(V, P.app(V, L(V, ch), L(V, r)), M.MapleGapScan{cur}, d, max), P.gscan(V, L(V, r), P.gscan(V, L(V, ch), M.MapleGapScan{cur}, d, max), d, max), P.gscan.app(V, L(V, ch), L(V, r), M.MapleGapScan{cur}, d, max)) : {gnode(V, r, gnode(V, ch, M.MapleGapScan{cur}, d, max), d, max) == _ : M.MapleGap<U32>}
      %ihc : {gnode(V, r, gnode(V, ch, M.MapleGapScan{cur}, d, max), d, max) == P.gscan(V, L(V, r), _, d, max) : M.MapleGap<U32>}
      ihr2

def gn(-V: Data, n: Nd(V), +st: M.MapleGap<U32>, +d: U32, +max: U32, +w: {P.wf(V, L(V, n)) == True{} : Bool}, +hp: {pok(V, n) == True{} : Bool}) -> {gnode(V, n, st, d, max) == P.gscan(V, L(V, n), st, d, max) : M.MapleGap<U32>}:
  match n:
    case N.MapleLeaf{es}:
      {==}
    case N.MapleNil{}:
      {==}
    case N.MapleSlot{+p, +ch, +r}:
      match st:
        case M.MapleGapScan{+cur}:
          +wc = P.wf.app_l(V, L(V, ch), L(V, r), w)
          +wr = P.wf.app_r(V, L(V, ch), L(V, r), w)
          gn.slot(U32.cmp(p, cur), V, p, ch, r, cur, d, max, {==}, w, hp, gn(V, ch, M.MapleGapScan{cur}, d, max, wc, pk.c(V, p, ch, r, hp)), gn(V, r, M.MapleGapScan{cur}, d, max, wr, pk.r(V, p, ch, r, hp)), gn(V, r, gnode(V, ch, M.MapleGapScan{cur}, d, max), d, max, wr, pk.r(V, p, ch, r, hp)))
        case M.MapleGapFound{+s}:
          Equal.sym(M.MapleGap<U32>, P.gscan(V, P.app(V, L(V, ch), L(V, r)), M.MapleGapFound{s}, d, max), M.MapleGapFound{s}, P.gscan.found(V, P.app(V, L(V, ch), L(V, r)), s, d, max))
        case M.MapleGapBusy{}:
          Equal.sym(M.MapleGap<U32>, P.gscan(V, P.app(V, L(V, ch), L(V, r)), M.MapleGapBusy{}, d, max), M.MapleGapBusy{}, P.gscan.busy(V, P.app(V, L(V, ch), L(V, r)), d, max))

def ea.go(zs: Bool, inv: Bool, -V: Data, +root: Nd(V), +min: U32, +max: U32, +size: U32, +w: {P.wf(V, L(V, root)) == True{} : Bool}, +hp: {pok(V, root) == True{} : Bool}) -> {G.Maple.empty_area.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, ~M.MapleKey32.add, V, zs, inv, root, min, max, size) == M.MapleModel.empty_area.go(~U32, ~U32.cmp, ~M.MapleKey32.inc, ~M.MapleKey32.dec, ~M.MapleKey32.add, V, zs, inv, L(V, root), min, max, size) : Result<&2, &2, M.MapleError<U32>, U32>}:
  match zs:
    case True{}:
      {==}
    case False{}:
      match inv:
        case True{}:
          {==}
        case False{}:
          Equal.cong(M.MapleGap<U32>, Result<&2, &2, M.MapleError<U32>, U32>, st => P.gend(st, U32.sub(size, 1), max), gnode(V, root, M.MapleGapScan{min}, U32.sub(size, 1), max), P.gscan(V, L(V, root), M.MapleGapScan{min}, U32.sub(size, 1), max), gn(V, root, M.MapleGapScan{min}, U32.sub(size, 1), max, w, hp))

def tr.empty_area(-V: Data, t: Tr(V), +min: U32, +max: U32, +size: U32, +e: {X.Maple32.valid(V, t) == True{} : Bool}) -> {G.Maple32.empty_area(V, t, min, max, size) == M.MapleModel32.empty_area(V, TL(V, t), min, max, size) : Result<&2, &2, M.MapleError<U32>, U32>}:
  match t:
    case N.MapleTree{o, h, +n}:
      ea.go(Cmp.is_eq(U32.cmp(size, 0)), O.ult(max, min), V, n, min, max, size, vw(V, n, e), vp(V, n, e))
