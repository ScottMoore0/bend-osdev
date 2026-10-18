# Proofs of LAWS.bend. Internal lemmas are prefixed BP.
import Base
import ../bytes/bytes.bend as B
import ./blockdev.bend as D
import ./imgdev.bend as I
import ../array/array.bend as A
import ../array/LAWS.bend as AL
import ../array/PROOF.bend as APF
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BPF
import ./LAWS.bend as Laws

def BP.bool_t(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

# a false premise closes any goal
def BP.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : BP.bool_t(_)
  Unit{}

def BP.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : BP.bool_t(_)
  Unit{}

def BP.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, BP.ft(e))

def BP.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, BP.ft(e))

# Nat facts

def BP.lt_irrefl(n: Nat) -> {Nat.is_lt(n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      BP.lt_irrefl(p)

def BP.sub_self(n: Nat) -> {Nat.sub(n, n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      BP.sub_self(p)

def BP.eq_sym(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      BP.eq_sym(p, q)

# m at or after n, and not n: m - n is not 0
def BP.sub_nz(m: Nat, n: Nat, h1: {Nat.is_lt(m, n) == False{} : Bool}, h2: {Nat.is_eq(n, m) == False{} : Bool}) -> {Nat.is_eq(Nat.sub(m, n), 0n) == False{} : Bool}:
  match m n:
    case 0n 0n:
      Empty.absurd({Nat.is_eq(Nat.sub(0n, 0n), 0n) == False{} : Bool}, BP.tf(h2))
    case 0n 1n+q:
      Empty.absurd({Nat.is_eq(Nat.sub(0n, 1n+q), 0n) == False{} : Bool}, BP.tf(h1))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      BP.sub_nz(p, q, h1, h2)

# two numbers at or after k that differ still differ less k
def BP.sub_ne(n: Nat, m: Nat, k: Nat, hn: {Nat.is_lt(n, k) == False{} : Bool}, hm: {Nat.is_lt(m, k) == False{} : Bool}, h: {Nat.is_eq(n, m) == False{} : Bool}) -> {Nat.is_eq(Nat.sub(n, k), Nat.sub(m, k)) == False{} : Bool}:
  match n m k:
    case 0n 0n 0n:
      h
    case 0n 1n+q 0n:
      h
    case 1n+p 0n 0n:
      h
    case 1n+p 1n+q 0n:
      h
    case 0n _ 1n+r:
      Empty.absurd({Nat.is_eq(Nat.sub(0n, 1n+r), Nat.sub(m, 1n+r)) == False{} : Bool}, BP.tf(hn))
    case 1n+p 0n 1n+r:
      Empty.absurd({Nat.is_eq(Nat.sub(1n+p, 1n+r), Nat.sub(0n, 1n+r)) == False{} : Bool}, BP.tf(hm))
    case 1n+p 1n+q 1n+r:
      BP.sub_ne(p, q, r, hn, hm, h)

# The tree: a read after a write

def BP.get_set_same(t: D.MemTree, +n: Nat, +v: B.Octets, z: Bool, ez: {z == Nat.is_lt(n, D.MemTree.left_count(t)) : Bool}) -> {D.MemTree.get(D.MemTree.set.at(t, n, v, z), n) == Some{v} : Maybe<&2, B.Octets>}:
  match t z:
    case D.MemTEmpty{} _:
      %Equal.sym(Bool, Nat.is_lt(n, n), False{}, BP.lt_irrefl(n)) : {D.MemTree.get.at(D.MemTNode{n, D.MemTEmpty{}, D.MemTLeaf{v}}, n, _) == Some{v} : Maybe<&2, B.Octets>}
      %Equal.sym(Nat, Nat.sub(n, n), 0n, BP.sub_self(n)) : {D.MemTree.get.at(D.MemTLeaf{v}, _, Nat.is_lt(_, 0n)) == Some{v} : Maybe<&2, B.Octets>}
      {==}
    case D.MemTLeaf{b} _:
      match n:
        case 0n:
          {==}
        case 1n+p:
          %Equal.sym(Bool, Nat.is_lt(p, p), False{}, BP.lt_irrefl(p)) : {D.MemTree.get.at(D.MemTNode{1n+p, D.MemTLeaf{b}, D.MemTLeaf{v}}, 1n+p, _) == Some{v} : Maybe<&2, B.Octets>}
          %Equal.sym(Nat, Nat.sub(p, p), 0n, BP.sub_self(p)) : {D.MemTree.get.at(D.MemTLeaf{v}, _, Nat.is_lt(_, 0n)) == Some{v} : Maybe<&2, B.Octets>}
          {==}
    case D.MemTNode{+k, +l, r} True{}:
      +zl = Nat.is_lt(n, D.MemTree.left_count(l))
      %ez : {D.MemTree.get.at(D.MemTNode{k, D.MemTree.set.at(l, n, v, zl), r}, n, _) == Some{v} : Maybe<&2, B.Octets>}
      BP.get_set_same(l, n, v, zl, {==})
    case D.MemTNode{+k, l, +r} False{}:
      +m = Nat.sub(n, k)
      +zr = Nat.is_lt(m, D.MemTree.left_count(r))
      %ez : {D.MemTree.get.at(D.MemTNode{k, l, D.MemTree.set.at(r, m, v, zr)}, n, _) == Some{v} : Maybe<&2, B.Octets>}
      BP.get_set_same(r, m, v, zr, {==})

# the tree after a write at n, read at m (b: whether m is left of the node)
def BP.node_other(+k: Nat, +l: D.MemTree, +r: D.MemTree, +l2: D.MemTree, +m: Nat, b: Bool, +eb: {Nat.is_lt(m, k) == b : Bool}, e: {D.MemTree.get(l2, m) == D.MemTree.get(l, m) : Maybe<&2, B.Octets>}) -> {D.MemTree.get(D.MemTNode{k, l2, r}, m) == D.MemTree.get(D.MemTNode{k, l, r}, m) : Maybe<&2, B.Octets>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(m, k), True{}, eb) : {D.MemTree.get.at(D.MemTNode{k, l2, r}, m, _) == D.MemTree.get.at(D.MemTNode{k, l, r}, m, _) : Maybe<&2, B.Octets>}
      e
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(m, k), False{}, eb) : {D.MemTree.get.at(D.MemTNode{k, l2, r}, m, _) == D.MemTree.get.at(D.MemTNode{k, l, r}, m, _) : Maybe<&2, B.Octets>}
      {==}

def BP.node_other_r(+k: Nat, +l: D.MemTree, +r: D.MemTree, +r2: D.MemTree, +m: Nat, b: Bool, +eb: {Nat.is_lt(m, k) == b : Bool}, e: {Nat.is_lt(m, k) == False{} : Bool} -> {D.MemTree.get(r2, Nat.sub(m, k)) == D.MemTree.get(r, Nat.sub(m, k)) : Maybe<&2, B.Octets>}) -> {D.MemTree.get(D.MemTNode{k, l, r2}, m) == D.MemTree.get(D.MemTNode{k, l, r}, m) : Maybe<&2, B.Octets>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(m, k), True{}, eb) : {D.MemTree.get.at(D.MemTNode{k, l, r2}, m, _) == D.MemTree.get.at(D.MemTNode{k, l, r}, m, _) : Maybe<&2, B.Octets>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(m, k), False{}, eb) : {D.MemTree.get.at(D.MemTNode{k, l, r2}, m, _) == D.MemTree.get.at(D.MemTNode{k, l, r}, m, _) : Maybe<&2, B.Octets>}
      e(eb)

def BP.empty_other(+n: Nat, +v: B.Octets, +m: Nat, b: Bool, +eb: {Nat.is_lt(m, n) == b : Bool}, h: {Nat.is_eq(n, m) == False{} : Bool}) -> {D.MemTree.get(D.MemTNode{n, D.MemTEmpty{}, D.MemTLeaf{v}}, m) == None{} : Maybe<&2, B.Octets>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(m, n), True{}, eb) : {D.MemTree.get.at(D.MemTNode{n, D.MemTEmpty{}, D.MemTLeaf{v}}, m, _) == None{} : Maybe<&2, B.Octets>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(m, n), False{}, eb) : {D.MemTree.get.at(D.MemTNode{n, D.MemTEmpty{}, D.MemTLeaf{v}}, m, _) == None{} : Maybe<&2, B.Octets>}
      %Equal.sym(Bool, Nat.is_eq(Nat.sub(m, n), 0n), False{}, BP.sub_nz(m, n, eb, h)) : {D.MemTree.get.leaf(_, v) == None{} : Maybe<&2, B.Octets>}
      {==}

def BP.leaf_other_f(m: Nat, +p: Nat, +bl: B.Octets, +v: B.Octets, +eb: {Nat.is_lt(m, 1n+p) == False{} : Bool}, h: {Nat.is_eq(1n+p, m) == False{} : Bool}) -> {D.MemTree.get(D.MemTNode{1n+p, D.MemTLeaf{bl}, D.MemTLeaf{v}}, m) == D.MemTree.get(D.MemTLeaf{bl}, m) : Maybe<&2, B.Octets>}:
  match m:
    case 0n:
      Empty.absurd({D.MemTree.get(D.MemTNode{1n+p, D.MemTLeaf{bl}, D.MemTLeaf{v}}, 0n) == D.MemTree.get(D.MemTLeaf{bl}, 0n) : Maybe<&2, B.Octets>}, BP.tf(eb))
    case 1n+ +q:
      %Equal.sym(Bool, Nat.is_lt(1n+q, 1n+p), False{}, eb) : {D.MemTree.get.at(D.MemTNode{1n+p, D.MemTLeaf{bl}, D.MemTLeaf{v}}, 1n+q, _) == None{} : Maybe<&2, B.Octets>}
      %Equal.sym(Bool, Nat.is_eq(Nat.sub(1n+q, 1n+p), 0n), False{}, BP.sub_nz(1n+q, 1n+p, eb, h)) : {D.MemTree.get.leaf(_, v) == None{} : Maybe<&2, B.Octets>}
      {==}

def BP.leaf_other(+p: Nat, +bl: B.Octets, +v: B.Octets, +m: Nat, b: Bool, +eb: {Nat.is_lt(m, 1n+p) == b : Bool}, h: {Nat.is_eq(1n+p, m) == False{} : Bool}) -> {D.MemTree.get(D.MemTNode{1n+p, D.MemTLeaf{bl}, D.MemTLeaf{v}}, m) == D.MemTree.get(D.MemTLeaf{bl}, m) : Maybe<&2, B.Octets>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(m, 1n+p), True{}, eb) : {D.MemTree.get.at(D.MemTNode{1n+p, D.MemTLeaf{bl}, D.MemTLeaf{v}}, m, _) == D.MemTree.get(D.MemTLeaf{bl}, m) : Maybe<&2, B.Octets>}
      {==}
    case False{}:
      BP.leaf_other_f(m, p, bl, v, eb, h)

# a write at n leaves every other read unchanged
def BP.get_set_other(t: D.MemTree, +n: Nat, +v: B.Octets, z: Bool, ez: {z == Nat.is_lt(n, D.MemTree.left_count(t)) : Bool}, +m: Nat, h: {Nat.is_eq(n, m) == False{} : Bool}) -> {D.MemTree.get(D.MemTree.set.at(t, n, v, z), m) == D.MemTree.get(t, m) : Maybe<&2, B.Octets>}:
  match t z:
    case D.MemTEmpty{} _:
      BP.empty_other(n, v, m, Nat.is_lt(m, n), {==}, h)
    case D.MemTLeaf{+b} _:
      match n:
        case 0n:
          match m:
            case 0n:
              Empty.absurd({D.MemTree.get(D.MemTLeaf{v}, 0n) == D.MemTree.get(D.MemTLeaf{b}, 0n) : Maybe<&2, B.Octets>}, BP.tf(h))
            case 1n+q:
              {==}
        case 1n+ +p:
          BP.leaf_other(p, b, v, m, Nat.is_lt(m, 1n+p), {==}, h)
    case D.MemTNode{+k, +l, +r} True{}:
      +zl = Nat.is_lt(n, D.MemTree.left_count(l))
      BP.node_other(k, l, r, D.MemTree.set.at(l, n, v, zl), m, Nat.is_lt(m, k), {==}, BP.get_set_other(l, n, v, zl, {==}, m, h))
    case D.MemTNode{+k, +l, +r} False{}:
      +nk = Nat.sub(n, k)
      +zr = Nat.is_lt(nk, D.MemTree.left_count(r))
      BP.node_other_r(k, l, r, D.MemTree.set.at(r, nk, v, zr), m, Nat.is_lt(m, k), {==}, hm => BP.get_set_other(r, nk, v, zr, {==}, Nat.sub(m, k), BP.sub_ne(n, m, k, Equal.sym(Bool, False{}, Nat.is_lt(n, k), ez), hm, h)))

# MemDev's laws

def BP.read_after_update(d: D.MemDev, +n: Nat, +data: B.Octets, len_ok: {Nat.is_eq(B.Octets.len(data), D.MemDev.block_size(d)) == True{} : Bool}, +in_range: {Nat.is_lt(n, D.MemDev.block_count(d)) == True{} : Bool}) -> {D.MemDev.read_block(D.MemDev.update(d, n, data), n) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}:
  match d:
    case D.MemDev{+bs, +c, +t}:
      %Equal.sym(Bool, Nat.is_eq(B.Octets.len(data), bs), True{}, len_ok) : {D.MemDev.read_block(D.MemDev.update.check(Bool.and(_, Nat.is_lt(n, c)), bs, c, t, n, data), n) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}
      %Equal.sym(Bool, Nat.is_lt(n, c), True{}, in_range) : {D.MemDev.read_block(D.MemDev.update.check(Bool.and(True{}, _), bs, c, t, n, data), n) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}
      %Equal.sym(Bool, Nat.is_lt(n, c), True{}, in_range) : {D.MemDev.read.check(_, bs, D.MemTree.set(t, n, data), n) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}
      %Equal.sym(Maybe<&2, B.Octets>, D.MemTree.get(D.MemTree.set(t, n, data), n), Some{data}, BP.get_set_same(t, n, data, Nat.is_lt(n, D.MemTree.left_count(t)), {==})) : {Done{D.MemDev.read.got(bs, _)} == Done{data} : Result<&2, &2, D.DevError, B.Octets>}
      {==}

def Laws.read_after_update(d, n, data, len_ok, in_range):
  BP.read_after_update(d, n, data, len_ok, in_range)

def BP.read_other(b: Bool, +bs: Nat, +t: D.MemTree, +t2: D.MemTree, +m: Nat, e: {D.MemTree.get(t2, m) == D.MemTree.get(t, m) : Maybe<&2, B.Octets>}) -> {D.MemDev.read.check(b, bs, t2, m) == D.MemDev.read.check(b, bs, t, m) : Result<&2, &2, D.DevError, B.Octets>}:
  match b:
    case True{}:
      %e : {Done{D.MemDev.read.got(bs, D.MemTree.get(t2, m))} == Done{D.MemDev.read.got(bs, _)} : Result<&2, &2, D.DevError, B.Octets>}
      {==}
    case False{}:
      {==}

def BP.upd_other(ok: Bool, +bs: Nat, +c: Nat, +t: D.MemTree, +n: Nat, +m: Nat, +data: B.Octets, diff: {Nat.is_eq(m, n) == False{} : Bool}) -> {D.MemDev.read_block(D.MemDev.update.check(ok, bs, c, t, n, data), m) == D.MemDev.read_block(D.MemDev{bs, c, t}, m) : Result<&2, &2, D.DevError, B.Octets>}:
  match ok:
    case True{}:
      BP.read_other(Nat.is_lt(m, c), bs, t, D.MemTree.set(t, n, data), m, BP.get_set_other(t, n, data, Nat.is_lt(n, D.MemTree.left_count(t)), {==}, m, Equal.trans(Bool, Nat.is_eq(n, m), Nat.is_eq(m, n), False{}, BP.eq_sym(n, m), diff)))
    case False{}:
      {==}

def Laws.update_other(d, n, m, data, diff):
  match d:
    case D.MemDev{+bs, +c, +t}:
      BP.upd_other(Bool.and(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, c)), bs, c, t, n, m, data, diff)

def BP.upd_size(ok: Bool, +bs: Nat, +c: Nat, +t: D.MemTree, +n: Nat, +data: B.Octets) -> {D.MemDev.block_size(D.MemDev.update.check(ok, bs, c, t, n, data)) == bs : Nat}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.update_keeps_size(d, n, data):
  match d:
    case D.MemDev{+bs, +c, +t}:
      BP.upd_size(Bool.and(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, c)), bs, c, t, n, data)

def BP.upd_count(ok: Bool, +bs: Nat, +c: Nat, +t: D.MemTree, +n: Nat, +data: B.Octets) -> {D.MemDev.block_count(D.MemDev.update.check(ok, bs, c, t, n, data)) == c : Nat}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.update_keeps_count(d, n, data):
  match d:
    case D.MemDev{+bs, +c, +t}:
      BP.upd_count(Bool.and(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, c)), bs, c, t, n, data)

# The owned helpers on an adapted MemDev are the pure ones

def BP.join(+d: D.MemDev, +blk: B.Octets, x: Result<&2, &2, D.DevError, B.Octets>) -> {D.ODev.join(~D.MemDev, blk, (d, x)) == (d, Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, x, rest => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.append(blk, rest)))) : D.MemDev & Result<&2, &2, D.DevError, B.Octets>}:
  match x:
    case Done{rest}:
      {==}
    case Fail{e}:
      {==}

def BP.then_step(+d: D.MemDev, res: Result<&2, &2, D.DevError, B.Octets>, +p: Nat, +first: Nat, +ih: {D.ODev.read_blocks(~D.MemDev, ~D.MemDev.own_read_block, p, d, Nat.add(first, 1n)) == (d, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, p, Nat.add(first, 1n))) : D.MemDev & Result<&2, &2, D.DevError, B.Octets>}) -> {D.ODev.then(~D.MemDev, (d, res), d2 => D.ODev.read_blocks(~D.MemDev, ~D.MemDev.own_read_block, p, d2, Nat.add(first, 1n))) == (d, Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, res, blk => Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, p, Nat.add(first, 1n)), rest => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.append(blk, rest))))) : D.MemDev & Result<&2, &2, D.DevError, B.Octets>}:
  match res:
    case Done{+blk}:
      %Equal.sym(D.MemDev & Result<&2, &2, D.DevError, B.Octets>, D.ODev.read_blocks(~D.MemDev, ~D.MemDev.own_read_block, p, d, Nat.add(first, 1n)), (d, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, p, Nat.add(first, 1n))), ih) : {D.ODev.join(~D.MemDev, blk, _) == (d, Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, p, Nat.add(first, 1n)), rest => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.append(blk, rest)))) : D.MemDev & Result<&2, &2, D.DevError, B.Octets>}
      BP.join(d, blk, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, p, Nat.add(first, 1n)))
    case Fail{e}:
      {==}

def BP.own_read_blocks(+count: Nat, +d: D.MemDev, +first: Nat) -> {D.ODev.read_blocks(~D.MemDev, ~D.MemDev.own_read_block, count, d, first) == (d, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, count, first)) : D.MemDev & Result<&2, &2, D.DevError, B.Octets>}:
  match count:
    case 0n:
      {==}
    case 1n+p:
      BP.then_step(d, D.MemDev.read_block(d, first), p, first, BP.own_read_blocks(p, d, Nat.add(first, 1n)))

def Laws.own_read_blocks(d, count, first):
  BP.own_read_blocks(count, d, first)

def BP.slice(+d: D.MemDev, +skip: Nat, +len: Nat, x: Result<&2, &2, D.DevError, B.Octets>) -> {D.ODev.slice(~D.MemDev, skip, len, (d, x)) == (d, Result.bind(&2, &2, D.DevError, B.Octets, B.Octets, x, blocks => Result.pure(&2, &2, D.DevError, B.Octets, B.Octets.slice(skip, len, blocks)))) : D.MemDev & Result<&2, &2, D.DevError, B.Octets>}:
  match x:
    case Done{blocks}:
      {==}
    case Fail{e}:
      {==}

def BP.own_bytes(b: Bool, +d: D.MemDev, +off: Nat, +len: Nat) -> {D.ODev.read_bytes.some(~D.MemDev, ~D.MemDev.own_block_size, ~D.MemDev.own_read_block, b, d, off, len) == (d, D.Dev.read_bytes.some(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, b, d, off, len)) : D.MemDev & Result<&2, &2, D.DevError, B.Octets>}:
  match b:
    case True{}:
      {==}
    case False{}:
      +bs = D.MemDev.block_size(d)
      +skip = Nat.mod(off, bs)
      +count = Nat.div(Nat.add(Nat.add(skip, len), Nat.sub(bs, 1n)), bs)
      +first = Nat.div(off, bs)
      %Equal.sym(D.MemDev & Result<&2, &2, D.DevError, B.Octets>, D.ODev.read_blocks(~D.MemDev, ~D.MemDev.own_read_block, count, d, first), (d, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, count, first)), BP.own_read_blocks(count, d, first)) : {D.ODev.slice(~D.MemDev, skip, len, _) == (d, D.Dev.read_bytes.go(~D.MemDev, ~D.MemDev.read_block, d, bs, off, len)) : D.MemDev & Result<&2, &2, D.DevError, B.Octets>}
      BP.slice(d, skip, len, D.Dev.read_blocks(~D.MemDev, ~D.MemDev.read_block, d, count, first))

def Laws.own_read_bytes(d, off, len):
  BP.own_bytes(Nat.is_eq(len, 0n), d, off, len)

def BP.own_write(okl: Bool, okn: Bool, +d: D.MemDev, +n: Nat, +data: B.Octets, el: {okl == True{} : Bool}, en: {okn == True{} : Bool}) -> {D.Dev.own_write.fin(~D.MemDev, d, D.MemDev.write.check(okl, okn, d, n, data)) == (D.MemDev.update(d, n, data), Done{Unit{}}) : D.MemDev & Result<&2, &2, D.DevError, Unit>}:
  match okl okn:
    case True{} True{}:
      {==}
    case False{} _:
      Empty.absurd({D.Dev.own_write.fin(~D.MemDev, d, D.MemDev.write.check(False{}, okn, d, n, data)) == (D.MemDev.update(d, n, data), Done{Unit{}}) : D.MemDev & Result<&2, &2, D.DevError, Unit>}, BP.ft(el))
    case True{} False{}:
      Empty.absurd({D.Dev.own_write.fin(~D.MemDev, d, D.MemDev.write.check(True{}, False{}, d, n, data)) == (D.MemDev.update(d, n, data), Done{Unit{}}) : D.MemDev & Result<&2, &2, D.DevError, Unit>}, BP.ft(en))

def Laws.own_write_ok(d, n, data, len_ok, in_range):
  BP.own_write(Nat.is_eq(B.Octets.len(data), D.MemDev.block_size(d)), Nat.is_lt(n, D.MemDev.block_count(d)), d, n, data, len_ok, in_range)

def Laws.vector_count():
  {==}

def Laws.vector_block():
  {==}

def Laws.vector_out_of_range():
  {==}

def Laws.vector_span():
  {==}

def Laws.vector_span_past_end():
  {==}

def Laws.vector_write():
  {==}

def Laws.vector_write_bad_length():
  {==}

def Laws.vector_blank():
  {==}

def Laws.vector_own_span():
  {==}

def IP.orf(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def IP.byte_orf(+a0: Bool, +a1: Bool, +a2: Bool, +a3: Bool, +a4: Bool, +a5: Bool, +a6: Bool, +a7: Bool) -> {U32{WCon{Bool.or(a0, False{}), WCon{Bool.or(a1, False{}), WCon{Bool.or(a2, False{}), WCon{Bool.or(a3, False{}), WCon{Bool.or(a4, False{}), WCon{Bool.or(a5, False{}), WCon{Bool.or(a6, False{}), WCon{Bool.or(a7, False{}), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}:
  %Equal.sym(Bool, Bool.or(a0, False{}), a0, IP.orf(a0)) : {U32{WCon{_, WCon{Bool.or(a1, False{}), WCon{Bool.or(a2, False{}), WCon{Bool.or(a3, False{}), WCon{Bool.or(a4, False{}), WCon{Bool.or(a5, False{}), WCon{Bool.or(a6, False{}), WCon{Bool.or(a7, False{}), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %Equal.sym(Bool, Bool.or(a1, False{}), a1, IP.orf(a1)) : {U32{WCon{a0, WCon{_, WCon{Bool.or(a2, False{}), WCon{Bool.or(a3, False{}), WCon{Bool.or(a4, False{}), WCon{Bool.or(a5, False{}), WCon{Bool.or(a6, False{}), WCon{Bool.or(a7, False{}), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %Equal.sym(Bool, Bool.or(a2, False{}), a2, IP.orf(a2)) : {U32{WCon{a0, WCon{a1, WCon{_, WCon{Bool.or(a3, False{}), WCon{Bool.or(a4, False{}), WCon{Bool.or(a5, False{}), WCon{Bool.or(a6, False{}), WCon{Bool.or(a7, False{}), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %Equal.sym(Bool, Bool.or(a3, False{}), a3, IP.orf(a3)) : {U32{WCon{a0, WCon{a1, WCon{a2, WCon{_, WCon{Bool.or(a4, False{}), WCon{Bool.or(a5, False{}), WCon{Bool.or(a6, False{}), WCon{Bool.or(a7, False{}), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %Equal.sym(Bool, Bool.or(a4, False{}), a4, IP.orf(a4)) : {U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{_, WCon{Bool.or(a5, False{}), WCon{Bool.or(a6, False{}), WCon{Bool.or(a7, False{}), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %Equal.sym(Bool, Bool.or(a5, False{}), a5, IP.orf(a5)) : {U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{_, WCon{Bool.or(a6, False{}), WCon{Bool.or(a7, False{}), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %Equal.sym(Bool, Bool.or(a6, False{}), a6, IP.orf(a6)) : {U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{_, WCon{Bool.or(a7, False{}), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  %Equal.sym(Bool, Bool.or(a7, False{}), a7, IP.orf(a7)) : {U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{_, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} == U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} : U32}
  {==}

def IP.con4(-a: U32, -a2: U32, -b: U32, -b2: U32, -c: U32, -c2: U32, -d: U32, -d2: U32, -acc: List<&2, U32>, ea: {a == a2 : U32}, eb: {b == b2 : U32}, ec: {c == c2 : U32}, ed: {d == d2 : U32}) -> {Con{a, Con{b, Con{c, Con{d, acc}}}} == Con{a2, Con{b2, Con{c2, Con{d2, acc}}}} : List<&2, U32>}:
  %ea : {Con{a, Con{b, Con{c, Con{d, acc}}}} == Con{_, Con{b2, Con{c2, Con{d2, acc}}}} : List<&2, U32>}
  %eb : {Con{a, Con{b, Con{c, Con{d, acc}}}} == Con{a, Con{_, Con{c2, Con{d2, acc}}}} : List<&2, U32>}
  %ec : {Con{a, Con{b, Con{c, Con{d, acc}}}} == Con{a, Con{b, Con{_, Con{d2, acc}}}} : List<&2, U32>}
  %ed : {Con{a, Con{b, Con{c, Con{d, acc}}}} == Con{a, Con{b, Con{c, Con{_, acc}}}} : List<&2, U32>}
  {==}

# a word's bytes are the bytes it was packed from (each masked to 8 bits)
def IP.unword_word(b0: U32, b1: U32, b2: U32, b3: U32, -acc: List<&2, U32>) -> {I.ImgDev.unword(I.ImgDev.word(b0, b1, b2, b3), acc) == Con{B.byte(b0), Con{B.byte(b1), Con{B.byte(b2), Con{B.byte(b3), acc}}}} : List<&2, U32>}:
  match b0 b1 b2 b3:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, WCon{z8, WCon{z9, WCon{z10, WCon{z11, WCon{z12, WCon{z13, WCon{z14, WCon{z15, WCon{z16, WCon{z17, WCon{z18, WCon{z19, WCon{z20, WCon{z21, WCon{z22, WCon{z23, WCon{z24, WCon{z25, WCon{z26, WCon{z27, WCon{z28, WCon{z29, WCon{z30, WCon{z31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{w0, WCon{w1, WCon{w2, WCon{w3, WCon{w4, WCon{w5, WCon{w6, WCon{w7, WCon{w8, WCon{w9, WCon{w10, WCon{w11, WCon{w12, WCon{w13, WCon{w14, WCon{w15, WCon{w16, WCon{w17, WCon{w18, WCon{w19, WCon{w20, WCon{w21, WCon{w22, WCon{w23, WCon{w24, WCon{w25, WCon{w26, WCon{w27, WCon{w28, WCon{w29, WCon{w30, WCon{w31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      IP.con4(U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{Bool.or(y0, False{}), WCon{Bool.or(y1, False{}), WCon{Bool.or(y2, False{}), WCon{Bool.or(y3, False{}), WCon{Bool.or(y4, False{}), WCon{Bool.or(y5, False{}), WCon{Bool.or(y6, False{}), WCon{Bool.or(y7, False{}), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{Bool.or(z0, False{}), WCon{Bool.or(z1, False{}), WCon{Bool.or(z2, False{}), WCon{Bool.or(z3, False{}), WCon{Bool.or(z4, False{}), WCon{Bool.or(z5, False{}), WCon{Bool.or(z6, False{}), WCon{Bool.or(z7, False{}), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{z0, WCon{z1, WCon{z2, WCon{z3, WCon{z4, WCon{z5, WCon{z6, WCon{z7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{Bool.or(w0, False{}), WCon{Bool.or(w1, False{}), WCon{Bool.or(w2, False{}), WCon{Bool.or(w3, False{}), WCon{Bool.or(w4, False{}), WCon{Bool.or(w5, False{}), WCon{Bool.or(w6, False{}), WCon{Bool.or(w7, False{}), WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{w0, WCon{w1, WCon{w2, WCon{w3, WCon{w4, WCon{w5, WCon{w6, WCon{w7, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, acc, {==}, IP.byte_orf(y0, y1, y2, y3, y4, y5, y6, y7), IP.byte_orf(z0, z1, z2, z3, z4, z5, z6, z7), IP.byte_orf(w0, w1, w2, w3, w4, w5, w6, w7))


# ImgDev
# ======
#
# The method: a valid image's array is a perfect tree, so array's `reflect`
# law turns it, once, into Arrays.of_list(d, L, 0) for a Data list L of
# 2^d words. array's of_list_get / of_list_set laws then follow every read
# and write on L alone: a block read is IP.blk (the words), a block write
# IP.writes (List.set, slot by slot). The bytes go through IP.words and
# IP.bytes, and the pack / unpack lemma IP.unword_word.

# Nat facts

def IP.add_zero(x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 0n), p, IP.add_zero(p))

def IP.add_succ(x: Nat, -y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 1n+y), 1n+Nat.add(p, y), IP.add_succ(p, y))

def IP.add_one(+s: Nat) -> {Nat.add(s, 1n) == 1n+s : Nat}:
  Equal.trans(Nat, Nat.add(s, 1n), 1n+Nat.add(s, 0n), 1n+s, IP.add_succ(s, 0n), Equal.cong(Nat, Nat, k => 1n+k, Nat.add(s, 0n), s, IP.add_zero(s)))

def IP.add_one_r(+p: Nat, +s: Nat) -> {Nat.add(p, Nat.add(s, 1n)) == 1n+Nat.add(p, s) : Nat}:
  %Equal.sym(Nat, Nat.add(s, 1n), 1n+s, IP.add_one(s)) : {Nat.add(p, _) == 1n+Nat.add(p, s) : Nat}
  IP.add_succ(p, s)

def IP.le_succ(a: Nat, b: Nat) -> {Nat.is_le(1n+a, b) == Nat.is_lt(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      match q:
        case 0n:
          {==}
        case 1n+r:
          {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      IP.le_succ(p, q)

def IP.le_lt(+a: Nat, +b: Nat, h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_lt(a, b), Nat.is_le(1n+a, b), True{}, Equal.sym(Bool, Nat.is_le(1n+a, b), Nat.is_lt(a, b), IP.le_succ(a, b)), h)

def IP.lt_le(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(1n+a, b), Nat.is_lt(a, b), True{}, IP.le_succ(a, b), h)

def IP.le_refl(x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      IP.le_refl(p)

def IP.le_zero(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def IP.le_succ_r(x: Nat, y: Nat, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(x, 1n+y) == True{} : Bool}:
  match x y:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, BP.ft(h))
    case 1n+p 1n+q:
      IP.le_succ_r(p, q, h)

def IP.le_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      IP.le_zero(c)
    case 1n+p 0n _:
      Empty.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, BP.ft(h1))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, BP.ft(h2))
    case 1n+p 1n+q 1n+r:
      IP.le_trans(p, q, r, h1, h2)

def IP.le_add(+p: Nat, +s: Nat) -> {Nat.is_le(s, Nat.add(p, s)) == True{} : Bool}:
  match p:
    case 0n:
      IP.le_refl(s)
    case 1n+q:
      IP.le_succ_r(s, Nat.add(q, s), IP.le_add(q, s))

def IP.le_cancel(w: Nat, -x: Nat, -y: Nat) -> {Nat.is_le(Nat.add(w, x), Nat.add(w, y)) == Nat.is_le(x, y) : Bool}:
  match w:
    case 0n:
      {==}
    case 1n+p:
      IP.le_cancel(p, x, y)

def IP.mul_mono(a: Nat, b: Nat, +w: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.mul(a, w), Nat.mul(b, w)) == True{} : Bool}:
  match a b:
    case 0n _:
      IP.le_zero(Nat.mul(b, w))
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(Nat.mul(1n+p, w), 0n) == True{} : Bool}, BP.ft(h))
    case 1n+p 1n+q:
      %Equal.sym(Bool, Nat.is_le(Nat.add(w, Nat.mul(p, w)), Nat.add(w, Nat.mul(q, w))), Nat.is_le(Nat.mul(p, w), Nat.mul(q, w)), IP.le_cancel(w, Nat.mul(p, w), Nat.mul(q, w))) : {_ == True{} : Bool}
      IP.mul_mono(p, q, w, h)

def IP.lt_zero(x: Nat) -> {Nat.is_lt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def IP.ne_lt(s: Nat, j: Nat, h: {Nat.is_lt(j, s) == True{} : Bool}) -> {Nat.is_eq(s, j) == False{} : Bool}:
  match s j:
    case 0n _:
      Empty.absurd({Nat.is_eq(0n, j) == False{} : Bool}, BP.ft(Equal.trans(Bool, False{}, Nat.is_lt(j, 0n), True{}, Equal.sym(Bool, Nat.is_lt(j, 0n), False{}, IP.lt_zero(j)), h)))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      IP.ne_lt(p, q, h)

def IP.ne_gt(s: Nat, j: Nat, h: {Nat.is_lt(s, j) == True{} : Bool}) -> {Nat.is_eq(s, j) == False{} : Bool}:
  match s j:
    case _ 0n:
      Empty.absurd({Nat.is_eq(s, 0n) == False{} : Bool}, BP.ft(Equal.trans(Bool, False{}, Nat.is_lt(s, 0n), True{}, Equal.sym(Bool, Nat.is_lt(s, 0n), False{}, IP.lt_zero(s)), h)))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      IP.ne_gt(p, q, h)

def IP.lt_gt(m: Nat, n: Nat, h1: {Nat.is_lt(m, n) == False{} : Bool}, h2: {Nat.is_eq(m, n) == False{} : Bool}) -> {Nat.is_lt(n, m) == True{} : Bool}:
  match m n:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, BP.tf(h2))
    case 0n 1n+q:
      Empty.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, BP.tf(h1))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      IP.lt_gt(p, q, h1, h2)

def IP.eq_nat(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, BP.ft(h))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, BP.ft(h))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, k => 1n+k, p, q, IP.eq_nat(p, q, h))

def IP.nat_t(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def IP.sz(-k: Nat, e: {1n+k == 0n : Nat}) -> Empty:
  %Equal.sym(Nat, 1n+k, 0n, e) : IP.nat_t(_)
  Unit{}

def IP.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def IP.pred_cong(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, n => IP.pred(n), 1n+a, 1n+b, e)

# a block of `w` slots from slot n * w ends inside 2^d when n < c and
# c * w <= 2^d
def IP.block_in(+n: Nat, +c: Nat, +w: Nat, +s: Nat, hn: {Nat.is_lt(n, c) == True{} : Bool}, hs: {Nat.is_le(Nat.mul(c, w), s) == True{} : Bool}) -> {Nat.is_le(Nat.add(w, Nat.mul(n, w)), s) == True{} : Bool}:
  IP.le_trans(Nat.mul(1n+n, w), Nat.mul(c, w), s, IP.mul_mono(1n+n, c, w, IP.lt_le(n, c, hn)), hs)

# The model: words, bytes, a block's words, writing words

def IP.words(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{b0, Con{b1, Con{b2, Con{b3, t}}}}:
      Con{I.ImgDev.word(b0, b1, b2, b3), IP.words(t)}
    case _:
      Nil{}

def IP.bytes(ws: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      I.ImgDev.unword(x, IP.bytes(t))

def IP.blk(k: Nat, +l: List<&2, U32>, +s: Nat) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      Con{A.Arrays.nth(U32, l, s, 0), IP.blk(p, l, Nat.add(s, 1n))}

def IP.writes(ws: List<&2, U32>, l: List<&2, U32>, +s: Nat) -> List<&2, U32>:
  match ws:
    case Nil{}:
      l
    case Con{x, t}:
      IP.writes(t, List.set(&2, U32, l, s, x), Nat.add(s, 1n))

def IP.le_rw_l(-x: Nat, -y: Nat, -m: Nat, e: {x == y : Nat}, h: {Nat.is_le(y, m) == True{} : Bool}) -> {Nat.is_le(x, m) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {Nat.is_le(_, m) == True{} : Bool}
  h

def IP.le_rw_r(-k: Nat, -x: Nat, -y: Nat, e: {x == y : Nat}, h: {Nat.is_le(k, y) == True{} : Bool}) -> {Nat.is_le(k, x) == True{} : Bool}:
  %Equal.sym(Nat, x, y, e) : {Nat.is_le(k, _) == True{} : Bool}
  h

def IP.lt_succ_r(x: Nat, y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x, 1n+y) == True{} : Bool}:
  match x y:
    case _ 0n:
      Empty.absurd({Nat.is_lt(x, 1n) == True{} : Bool}, BP.ft(Equal.trans(Bool, False{}, Nat.is_lt(x, 0n), True{}, Equal.sym(Bool, Nat.is_lt(x, 0n), False{}, IP.lt_zero(x)), h)))
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      IP.lt_succ_r(p, q, h)

def IP.lt_s1(+j: Nat, +s: Nat, h: {Nat.is_lt(j, s) == True{} : Bool}) -> {Nat.is_lt(j, Nat.add(s, 1n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(s, 1n), 1n+s, IP.add_one(s)) : {Nat.is_lt(j, _) == True{} : Bool}
  IP.lt_succ_r(j, s, h)

def IP.lt_self(x: Nat) -> {Nat.is_lt(x, 1n+x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      IP.lt_self(p)

def IP.lt_s_s1(+s: Nat) -> {Nat.is_lt(s, Nat.add(s, 1n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(s, 1n), 1n+s, IP.add_one(s)) : {Nat.is_lt(s, _) == True{} : Bool}
  IP.lt_self(s)

def IP.le_s1(+x: Nat) -> {Nat.is_le(x, Nat.add(x, 1n)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(x, 1n), 1n+x, IP.add_one(x)) : {Nat.is_le(x, _) == True{} : Bool}
  IP.le_succ_r(x, x, IP.le_refl(x))

# s is inside a range that starts at s and has 1 + n more slots before m
def IP.lt_of_range(+n: Nat, +s: Nat, +m: Nat, h: {Nat.is_le(1n+Nat.add(n, s), m) == True{} : Bool}) -> {Nat.is_lt(s, m) == True{} : Bool}:
  IP.le_lt(s, m, IP.le_trans(1n+s, 1n+Nat.add(n, s), m, IP.le_add(n, s), h))

def IP.cong_succ(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

# The read loop: the bytes of k words from slot s

def IP.read_go(k: Nat, +s: Nat, +d: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.add(k, s), A.Arrays.slots(d)) == True{} : Bool}) -> {I.ImgDev.read.go(k, s, A.Arrays.of_list(U32, d, l, 0)) == (A.Arrays.of_list(U32, d, l, 0), IP.bytes(IP.blk(k, l, s))) : Array<U32> & List<&2, U32>}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      -a0 = A.Arrays.of_list(U32, d, l, 0)
      +x = A.Arrays.nth(U32, l, s, 0)
      +s1 = Nat.add(s, 1n)
      +hs0 = IP.lt_of_range(p, s, A.Arrays.slots(d), hs)
      +hs1 = IP.le_rw_l(Nat.add(p, s1), 1n+Nat.add(p, s), A.Arrays.slots(d), IP.add_one_r(p, s), hs)
      %Equal.sym(Array<U32> & U32, Array.get(U32, a0, U32.from_nat(s)), (a0, A.Arrays.nth(U32, l, A.Arrays.index(d, U32.from_nat(s)), 0)), AL.of_list_get(U32, d, l, 0, hl, hd, U32.from_nat(s))) : {I.ImgDev.read.word(_, a2 => x2 => I.ImgDev.read.cons(x2, I.ImgDev.read.go(p, s1, a2))) == (a0, IP.bytes(IP.blk(1n+p, l, s))) : Array<U32> & List<&2, U32>}
      %Equal.sym(Nat, A.Arrays.index(d, U32.from_nat(s)), s, AL.index_of_nat(d, hd, s, hs0)) : {I.ImgDev.read.cons(A.Arrays.nth(U32, l, _, 0), I.ImgDev.read.go(p, s1, a0)) == (a0, IP.bytes(IP.blk(1n+p, l, s))) : Array<U32> & List<&2, U32>}
      %Equal.sym(Array<U32> & List<&2, U32>, I.ImgDev.read.go(p, s1, a0), (a0, IP.bytes(IP.blk(p, l, s1))), IP.read_go(p, s1, d, l, hl, hd, hs1)) : {I.ImgDev.read.cons(x, _) == (a0, IP.bytes(IP.blk(1n+p, l, s))) : Array<U32> & List<&2, U32>}
      {==}

# The write loop: the bytes xs, four to a word, written from slot s

def IP.write_go(xs: List<&2, U32>, +s: Nat, +d: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.add(List.length(&2, U32, IP.words(xs)), s), A.Arrays.slots(d)) == True{} : Bool}) -> {I.ImgDev.write.go(xs, s, A.Arrays.of_list(U32, d, l, 0)) == A.Arrays.of_list(U32, d, IP.writes(IP.words(xs), l, s), 0) : Array<U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{b0, Nil{}}:
      {==}
    case Con{b0, Con{b1, Nil{}}}:
      {==}
    case Con{b0, Con{b1, Con{b2, Nil{}}}}:
      {==}
    case Con{+b0, Con{+b1, Con{+b2, Con{+b3, +t}}}}:
      +wd = I.ImgDev.word(b0, b1, b2, b3)
      +l2 = List.set(&2, U32, l, s, wd)
      +s1 = Nat.add(s, 1n)
      +n0 = List.length(&2, U32, IP.words(t))
      +hs0 = IP.lt_of_range(n0, s, A.Arrays.slots(d), hs)
      +hl2 = Equal.trans(Nat, List.length(&2, U32, l2), List.length(&2, U32, l), A.Arrays.slots(d), AL.set_length(U32, l, s, wd), hl)
      +hs1 = IP.le_rw_l(Nat.add(n0, s1), 1n+Nat.add(n0, s), A.Arrays.slots(d), IP.add_one_r(n0, s), hs)
      %Equal.sym(Array<U32>, Array.set(U32, A.Arrays.of_list(U32, d, l, 0), U32.from_nat(s), wd), A.Arrays.of_list(U32, d, List.set(&2, U32, l, A.Arrays.index(d, U32.from_nat(s)), wd), 0), AL.of_list_set(U32, d, l, 0, hl, hd, U32.from_nat(s), wd)) : {I.ImgDev.write.go(t, s1, _) == A.Arrays.of_list(U32, d, IP.writes(IP.words(t), l2, s1), 0) : Array<U32>}
      %Equal.sym(Nat, A.Arrays.index(d, U32.from_nat(s)), s, AL.index_of_nat(d, hd, s, hs0)) : {I.ImgDev.write.go(t, s1, A.Arrays.of_list(U32, d, List.set(&2, U32, l, _, wd), 0)) == A.Arrays.of_list(U32, d, IP.writes(IP.words(t), l2, s1), 0) : Array<U32>}
      IP.write_go(t, s1, d, l2, hl2, hd, hs1)

# Bytes to words and back

def IP.pred4(-a: Nat, -b: Nat, e: {4n+a == 4n+b : Nat}) -> {a == b : Nat}:
  IP.pred_cong(a, b, IP.pred_cong(1n+a, 1n+b, IP.pred_cong(2n+a, 2n+b, IP.pred_cong(3n+a, 3n+b, e))))

def IP.short1(-x: Nat, h: {1n == Nat.add(4n, x) : Nat}) -> Empty:
  IP.sz(Nat.add(2n, x), Equal.sym(Nat, 0n, Nat.add(3n, x), IP.pred_cong(0n, Nat.add(3n, x), h)))

def IP.short2(-x: Nat, h: {2n == Nat.add(4n, x) : Nat}) -> Empty:
  IP.sz(Nat.add(1n, x), Equal.sym(Nat, 0n, Nat.add(2n, x), IP.pred_cong(0n, Nat.add(2n, x), IP.pred_cong(1n, Nat.add(3n, x), h))))

def IP.short3(-x: Nat, h: {3n == Nat.add(4n, x) : Nat}) -> Empty:
  IP.sz(Nat.add(0n, x), Equal.sym(Nat, 0n, Nat.add(1n, x), IP.pred_cong(0n, Nat.add(1n, x), IP.pred_cong(1n, Nat.add(2n, x), IP.pred_cong(2n, Nat.add(3n, x), h)))))

def IP.words_len(k: Nat, xs: List<&2, U32>, h: {List.length(&2, U32, xs) == Nat.mul(k, 4n) : Nat}) -> {List.length(&2, U32, IP.words(xs)) == k : Nat}:
  match k:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case Con{b, t}:
          Empty.absurd({List.length(&2, U32, IP.words(Con{b, t})) == 0n : Nat}, IP.sz(List.length(&2, U32, t), h))
    case 1n+ +q:
      match xs:
        case Nil{}:
          Empty.absurd({List.length(&2, U32, IP.words(Nil{})) == 1n+q : Nat}, IP.sz(Nat.add(3n, Nat.mul(q, 4n)), Equal.sym(Nat, 0n, Nat.add(4n, Nat.mul(q, 4n)), h)))
        case Con{b0, Nil{}}:
          Empty.absurd({List.length(&2, U32, IP.words(Con{b0, Nil{}})) == 1n+q : Nat}, IP.short1(Nat.mul(q, 4n), h))
        case Con{b0, Con{b1, Nil{}}}:
          Empty.absurd({List.length(&2, U32, IP.words(Con{b0, Con{b1, Nil{}}})) == 1n+q : Nat}, IP.short2(Nat.mul(q, 4n), h))
        case Con{b0, Con{b1, Con{b2, Nil{}}}}:
          Empty.absurd({List.length(&2, U32, IP.words(Con{b0, Con{b1, Con{b2, Nil{}}}})) == 1n+q : Nat}, IP.short3(Nat.mul(q, 4n), h))
        case Con{b0, Con{b1, Con{b2, Con{b3, +t}}}}:
          IP.cong_succ(List.length(&2, U32, IP.words(t)), q, IP.words_len(q, t, IP.pred4(List.length(&2, U32, t), Nat.mul(q, 4n), h)))

def IP.bytes_words(k: Nat, xs: List<&2, U32>, h: {List.length(&2, U32, xs) == Nat.mul(k, 4n) : Nat}) -> {IP.bytes(IP.words(xs)) == B.mask(xs) : List<&2, U32>}:
  match k:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case Con{b, t}:
          Empty.absurd({IP.bytes(IP.words(Con{b, t})) == B.mask(Con{b, t}) : List<&2, U32>}, IP.sz(List.length(&2, U32, t), h))
    case 1n+ +q:
      match xs:
        case Nil{}:
          Empty.absurd({IP.bytes(IP.words(Nil{})) == B.mask(Nil{}) : List<&2, U32>}, IP.sz(Nat.add(3n, Nat.mul(q, 4n)), Equal.sym(Nat, 0n, Nat.add(4n, Nat.mul(q, 4n)), h)))
        case Con{b0, Nil{}}:
          Empty.absurd({IP.bytes(IP.words(Con{b0, Nil{}})) == B.mask(Con{b0, Nil{}}) : List<&2, U32>}, IP.short1(Nat.mul(q, 4n), h))
        case Con{b0, Con{b1, Nil{}}}:
          Empty.absurd({IP.bytes(IP.words(Con{b0, Con{b1, Nil{}}})) == B.mask(Con{b0, Con{b1, Nil{}}}) : List<&2, U32>}, IP.short2(Nat.mul(q, 4n), h))
        case Con{b0, Con{b1, Con{b2, Nil{}}}}:
          Empty.absurd({IP.bytes(IP.words(Con{b0, Con{b1, Con{b2, Nil{}}}})) == B.mask(Con{b0, Con{b1, Con{b2, Nil{}}}}) : List<&2, U32>}, IP.short3(Nat.mul(q, 4n), h))
        case Con{+b0, Con{+b1, Con{+b2, Con{+b3, +t}}}}:
          +r = IP.bytes(IP.words(t))
          %Equal.sym(List<&2, U32>, I.ImgDev.unword(I.ImgDev.word(b0, b1, b2, b3), r), Con{B.byte(b0), Con{B.byte(b1), Con{B.byte(b2), Con{B.byte(b3), r}}}}, IP.unword_word(b0, b1, b2, b3, r)) : {_ == B.mask(Con{b0, Con{b1, Con{b2, Con{b3, t}}}}) : List<&2, U32>}
          %Equal.sym(List<&2, U32>, r, B.mask(t), IP.bytes_words(q, t, IP.pred4(List.length(&2, U32, t), Nat.mul(q, 4n), h))) : {Con{B.byte(b0), Con{B.byte(b1), Con{B.byte(b2), Con{B.byte(b3), _}}}} == B.mask(Con{b0, Con{b1, Con{b2, Con{b3, t}}}}) : List<&2, U32>}
          {==}

# a block's bytes, unpacked from the words they were packed into, are the
# block itself
def IP.octets_back(+data: B.Octets, +k: Nat, +h: {List.length(&2, U32, B.Octets.to_list(data)) == Nat.mul(k, 4n) : Nat}) -> {B.Octets.of_list(IP.bytes(IP.words(B.Octets.to_list(data)))) == data : B.Octets}:
  +xs = B.Octets.to_list(data)
  %Equal.sym(List<&2, U32>, IP.bytes(IP.words(xs)), B.mask(xs), IP.bytes_words(k, xs, h)) : {B.Octets.of_list(_) == data : B.Octets}
  %BL.octets_to_of(xs) : {B.Octets.of_list(_) == data : B.Octets}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(B.Octets.of_list(xs))), B.Octets.of_list(xs), BL.octets_of_list_idempotent(xs)) : {_ == data : B.Octets}
  BL.octets_of_to(data)

# The model: writes keep the length; a write leaves the slots outside its
# range; a block written reads back; a block outside a write is unchanged

def IP.wlen(ws: List<&2, U32>, +l: List<&2, U32>, +s: Nat) -> {List.length(&2, U32, IP.writes(ws, l, s)) == List.length(&2, U32, l) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case Con{+x, t}:
      Equal.trans(Nat, List.length(&2, U32, IP.writes(t, List.set(&2, U32, l, s, x), Nat.add(s, 1n))), List.length(&2, U32, List.set(&2, U32, l, s, x)), List.length(&2, U32, l), IP.wlen(t, List.set(&2, U32, l, s, x), Nat.add(s, 1n)), AL.set_length(U32, l, s, x))

def IP.wo_lt(ws: List<&2, U32>, +l: List<&2, U32>, +s: Nat, +j: Nat, +h: {Nat.is_lt(j, s) == True{} : Bool}) -> {A.Arrays.nth(U32, IP.writes(ws, l, s), j, 0) == A.Arrays.nth(U32, l, j, 0) : U32}:
  match ws:
    case Nil{}:
      {==}
    case Con{+x, t}:
      +l2 = List.set(&2, U32, l, s, x)
      Equal.trans(U32, A.Arrays.nth(U32, IP.writes(t, l2, Nat.add(s, 1n)), j, 0), A.Arrays.nth(U32, l2, j, 0), A.Arrays.nth(U32, l, j, 0), IP.wo_lt(t, l2, Nat.add(s, 1n), j, IP.lt_s1(j, s, h)), AL.nth_set_other(U32, l, s, j, x, 0, IP.ne_lt(s, j, h)))

def IP.wo_ge(ws: List<&2, U32>, +l: List<&2, U32>, +s: Nat, +j: Nat, +h: {Nat.is_le(Nat.add(List.length(&2, U32, ws), s), j) == True{} : Bool}) -> {A.Arrays.nth(U32, IP.writes(ws, l, s), j, 0) == A.Arrays.nth(U32, l, j, 0) : U32}:
  match ws:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +l2 = List.set(&2, U32, l, s, x)
      +n0 = List.length(&2, U32, t)
      Equal.trans(U32, A.Arrays.nth(U32, IP.writes(t, l2, Nat.add(s, 1n)), j, 0), A.Arrays.nth(U32, l2, j, 0), A.Arrays.nth(U32, l, j, 0), IP.wo_ge(t, l2, Nat.add(s, 1n), j, IP.le_rw_l(Nat.add(n0, Nat.add(s, 1n)), 1n+Nat.add(n0, s), j, IP.add_one_r(n0, s), h)), AL.nth_set_other(U32, l, s, j, x, 0, IP.ne_gt(s, j, IP.lt_of_range(n0, s, j, h))))

def IP.wr(ws: List<&2, U32>, +l: List<&2, U32>, +s: Nat, +hl: {Nat.is_le(Nat.add(List.length(&2, U32, ws), s), List.length(&2, U32, l)) == True{} : Bool}) -> {IP.blk(List.length(&2, U32, ws), IP.writes(ws, l, s), s) == ws : List<&2, U32>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +n0 = List.length(&2, U32, t)
      +l2 = List.set(&2, U32, l, s, x)
      +s1 = Nat.add(s, 1n)
      +w2 = IP.writes(t, l2, s1)
      +e1 = Equal.trans(U32, A.Arrays.nth(U32, w2, s, 0), A.Arrays.nth(U32, l2, s, 0), x, IP.wo_lt(t, l2, s1, s, IP.lt_s_s1(s)), AL.nth_set_same(U32, l, s, x, 0, IP.lt_of_range(n0, s, List.length(&2, U32, l), hl)))
      +hl2 = IP.le_rw_r(Nat.add(n0, s1), List.length(&2, U32, l2), List.length(&2, U32, l), AL.set_length(U32, l, s, x), IP.le_rw_l(Nat.add(n0, s1), 1n+Nat.add(n0, s), List.length(&2, U32, l), IP.add_one_r(n0, s), hl))
      %Equal.sym(U32, A.Arrays.nth(U32, w2, s, 0), x, e1) : {Con{_, IP.blk(n0, w2, s1)} == Con{x, t} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, IP.blk(n0, w2, s1), t, IP.wr(t, l2, s1, hl2)) : {Con{x, _} == Con{x, t} : List<&2, U32>}
      {==}

def IP.wd_before(k: Nat, +ws: List<&2, U32>, +l: List<&2, U32>, +s: Nat, +s2: Nat, +h: {Nat.is_le(Nat.add(k, s2), s) == True{} : Bool}) -> {IP.blk(k, IP.writes(ws, l, s), s2) == IP.blk(k, l, s2) : List<&2, U32>}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +wl = IP.writes(ws, l, s)
      +t1 = Nat.add(s2, 1n)
      %Equal.sym(U32, A.Arrays.nth(U32, wl, s2, 0), A.Arrays.nth(U32, l, s2, 0), IP.wo_lt(ws, l, s, s2, IP.lt_of_range(p, s2, s, h))) : {Con{_, IP.blk(p, wl, t1)} == Con{A.Arrays.nth(U32, l, s2, 0), IP.blk(p, l, t1)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, IP.blk(p, wl, t1), IP.blk(p, l, t1), IP.wd_before(p, ws, l, s, t1, IP.le_rw_l(Nat.add(p, t1), 1n+Nat.add(p, s2), s, IP.add_one_r(p, s2), h))) : {Con{A.Arrays.nth(U32, l, s2, 0), _} == Con{A.Arrays.nth(U32, l, s2, 0), IP.blk(p, l, t1)} : List<&2, U32>}
      {==}

def IP.wd_after(k: Nat, +ws: List<&2, U32>, +l: List<&2, U32>, +s: Nat, +s2: Nat, +h: {Nat.is_le(Nat.add(List.length(&2, U32, ws), s), s2) == True{} : Bool}) -> {IP.blk(k, IP.writes(ws, l, s), s2) == IP.blk(k, l, s2) : List<&2, U32>}:
  match k:
    case 0n:
      {==}
    case 1n+ +p:
      +wl = IP.writes(ws, l, s)
      +t1 = Nat.add(s2, 1n)
      %Equal.sym(U32, A.Arrays.nth(U32, wl, s2, 0), A.Arrays.nth(U32, l, s2, 0), IP.wo_ge(ws, l, s, s2, h)) : {Con{_, IP.blk(p, wl, t1)} == Con{A.Arrays.nth(U32, l, s2, 0), IP.blk(p, l, t1)} : List<&2, U32>}
      %Equal.sym(List<&2, U32>, IP.blk(p, wl, t1), IP.blk(p, l, t1), IP.wd_after(p, ws, l, s, t1, IP.le_trans(Nat.add(List.length(&2, U32, ws), s), s2, t1, h, IP.le_s1(s2)))) : {Con{A.Arrays.nth(U32, l, s2, 0), _} == Con{A.Arrays.nth(U32, l, s2, 0), IP.blk(p, l, t1)} : List<&2, U32>}
      {==}

# Images over a model list: reads, writes, validity

def IP.read_model(+w: Nat, +c: Nat, +d: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}, +n: Nat, +hn: {Nat.is_lt(n, c) == True{} : Bool}) -> {I.ImgDev.read_block(I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l, 0)}, n) == (I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l, 0)}, Done{B.Octets.of_list(IP.bytes(IP.blk(w, l, Nat.mul(n, w))))}) : I.ImgDev & Result<&2, &2, D.DevError, B.Octets>}:
  -a0 = A.Arrays.of_list(U32, d, l, 0)
  +s = Nat.mul(n, w)
  %Equal.sym(Bool, Nat.is_lt(n, c), True{}, hn) : {I.ImgDev.read.check(_, w, c, d, a0, n) == (I.ImgDev{w, c, d, a0}, Done{B.Octets.of_list(IP.bytes(IP.blk(w, l, s)))}) : I.ImgDev & Result<&2, &2, D.DevError, B.Octets>}
  %Equal.sym(Array<U32> & List<&2, U32>, I.ImgDev.read.go(w, s, a0), (a0, IP.bytes(IP.blk(w, l, s))), IP.read_go(w, s, d, l, hl, hd, IP.block_in(n, c, w, A.Arrays.slots(d), hn, hs))) : {I.ImgDev.read.fin(w, c, d, _) == (I.ImgDev{w, c, d, a0}, Done{B.Octets.of_list(IP.bytes(IP.blk(w, l, s)))}) : I.ImgDev & Result<&2, &2, D.DevError, B.Octets>}
  {==}

def IP.list_len(+data: B.Octets, +w: Nat, hlen: {Nat.is_eq(B.Octets.len(data), Nat.mul(w, 4n)) == True{} : Bool}) -> {List.length(&2, U32, B.Octets.to_list(data)) == Nat.mul(w, 4n) : Nat}:
  Equal.trans(Nat, List.length(&2, U32, B.Octets.to_list(data)), B.Octets.len(data), Nat.mul(w, 4n), Equal.sym(Nat, B.Octets.len(data), B.len(B.Octets.to_list(data)), BL.octets_len_list(data)), IP.eq_nat(B.Octets.len(data), Nat.mul(w, 4n), hlen))

def IP.write_model(+w: Nat, +c: Nat, +d: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}, +n: Nat, +hn: {Nat.is_lt(n, c) == True{} : Bool}, +data: B.Octets, +hlen: {Nat.is_eq(B.Octets.len(data), Nat.mul(w, 4n)) == True{} : Bool}) -> {I.ImgDev.write_block(I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l, 0)}, n, data) == (I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, IP.writes(IP.words(B.Octets.to_list(data)), l, Nat.mul(n, w)), 0)}, Done{Unit{}}) : I.ImgDev & Result<&2, &2, D.DevError, Unit>}:
  -a0 = A.Arrays.of_list(U32, d, l, 0)
  +s = Nat.mul(n, w)
  +ws = IP.words(B.Octets.to_list(data))
  +hw = IP.words_len(w, B.Octets.to_list(data), IP.list_len(data, w, hlen))
  +hsw = IP.le_rw_l(Nat.add(List.length(&2, U32, ws), s), Nat.add(w, s), A.Arrays.slots(d), Equal.cong(Nat, Nat, k => Nat.add(k, s), List.length(&2, U32, ws), w, hw), IP.block_in(n, c, w, A.Arrays.slots(d), hn, hs))
  %Equal.sym(Bool, Nat.is_eq(B.Octets.len(data), Nat.mul(w, 4n)), True{}, hlen) : {I.ImgDev.write.check(_, Nat.is_lt(n, c), w, c, d, a0, n, data) == (I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, IP.writes(ws, l, s), 0)}, Done{Unit{}}) : I.ImgDev & Result<&2, &2, D.DevError, Unit>}
  %Equal.sym(Bool, Nat.is_lt(n, c), True{}, hn) : {I.ImgDev.write.check(True{}, _, w, c, d, a0, n, data) == (I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, IP.writes(ws, l, s), 0)}, Done{Unit{}}) : I.ImgDev & Result<&2, &2, D.DevError, Unit>}
  %Equal.sym(Array<U32>, I.ImgDev.write.go(B.Octets.to_list(data), s, a0), A.Arrays.of_list(U32, d, IP.writes(ws, l, s), 0), IP.write_go(B.Octets.to_list(data), s, d, l, hl, hd, hsw)) : {(I.ImgDev{w, c, d, _}, Done{Unit{}}) == (I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, IP.writes(ws, l, s), 0)}, Done{Unit{}}) : I.ImgDev & Result<&2, &2, D.DevError, Unit>}
  {==}

def IP.valid_of(+w: Nat, +c: Nat, +d: Nat, +l: List<&2, U32>, hd: {Nat.is_lt(d, 32n) == True{} : Bool}, hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}) -> {I.ImgDev.valid(I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l, 0)}) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(d, 32n), True{}, hd) : {Bool.and(_, Bool.and(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, A.Arrays.of_list(U32, d, l, 0)))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), True{}, hs) : {Bool.and(_, A.Arrays.is_perfect(U32, d, A.Arrays.of_list(U32, d, l, 0))) == True{} : Bool}
  AL.of_list_perfect(U32, d, l, 0)

# a block written reads back
def IP.rw_model(+w: Nat, +c: Nat, +d: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}, +n: Nat, +hn: {Nat.is_lt(n, c) == True{} : Bool}, +data: B.Octets, +hlen: {Nat.is_eq(B.Octets.len(data), Nat.mul(w, 4n)) == True{} : Bool}) -> {B.Octets.of_list(IP.bytes(IP.blk(w, IP.writes(IP.words(B.Octets.to_list(data)), l, Nat.mul(n, w)), Nat.mul(n, w)))) == data : B.Octets}:
  +s = Nat.mul(n, w)
  +ws = IP.words(B.Octets.to_list(data))
  +hw = IP.words_len(w, B.Octets.to_list(data), IP.list_len(data, w, hlen))
  +hle = IP.le_rw_r(Nat.add(List.length(&2, U32, ws), s), List.length(&2, U32, l), A.Arrays.slots(d), hl, IP.le_rw_l(Nat.add(List.length(&2, U32, ws), s), Nat.add(w, s), A.Arrays.slots(d), Equal.cong(Nat, Nat, k => Nat.add(k, s), List.length(&2, U32, ws), w, hw), IP.block_in(n, c, w, A.Arrays.slots(d), hn, hs)))
  +ewr = Equal.trans(List<&2, U32>, IP.blk(w, IP.writes(ws, l, s), s), IP.blk(List.length(&2, U32, ws), IP.writes(ws, l, s), s), ws, Equal.cong(Nat, List<&2, U32>, k => IP.blk(k, IP.writes(ws, l, s), s), w, List.length(&2, U32, ws), Equal.sym(Nat, List.length(&2, U32, ws), w, hw)), IP.wr(ws, l, s, hle))
  %Equal.sym(List<&2, U32>, IP.blk(w, IP.writes(ws, l, s), s), ws, ewr) : {B.Octets.of_list(IP.bytes(_)) == data : B.Octets}
  IP.octets_back(data, w, IP.list_len(data, w, hlen))

# the block m of a write at block n, for m and n that differ (b: m < n)
def IP.disjoint(+w: Nat, +ws: List<&2, U32>, +hw: {List.length(&2, U32, ws) == w : Nat}, +l: List<&2, U32>, +n: Nat, +m: Nat, +diff: {Nat.is_eq(m, n) == False{} : Bool}, b: Bool, +eb: {Nat.is_lt(m, n) == b : Bool}) -> {IP.blk(w, IP.writes(ws, l, Nat.mul(n, w)), Nat.mul(m, w)) == IP.blk(w, l, Nat.mul(m, w)) : List<&2, U32>}:
  match b:
    case True{}:
      IP.wd_before(w, ws, l, Nat.mul(n, w), Nat.mul(m, w), IP.mul_mono(1n+m, n, w, IP.lt_le(m, n, eb)))
    case False{}:
      IP.wd_after(w, ws, l, Nat.mul(n, w), Nat.mul(m, w), IP.le_rw_l(Nat.add(List.length(&2, U32, ws), Nat.mul(n, w)), Nat.add(w, Nat.mul(n, w)), Nat.mul(m, w), Equal.cong(Nat, Nat, k => Nat.add(k, Nat.mul(n, w)), List.length(&2, U32, ws), w, hw), IP.mul_mono(1n+n, m, w, IP.lt_le(n, m, IP.lt_gt(m, n, eb, diff)))))

# a block written leaves every other block (bm: whether m is a block)
def IP.other_model(+w: Nat, +c: Nat, +d: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}, +n: Nat, +hn: {Nat.is_lt(n, c) == True{} : Bool}, +ws: List<&2, U32>, +hw: {List.length(&2, U32, ws) == w : Nat}, +m: Nat, +diff: {Nat.is_eq(m, n) == False{} : Bool}, bm: Bool, +em: {Nat.is_lt(m, c) == bm : Bool}) -> {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, IP.writes(ws, l, Nat.mul(n, w)), 0)}, m)) == Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l, 0)}, m)) : Result<&2, &2, D.DevError, B.Octets>}:
  match bm:
    case True{}:
      +s = Nat.mul(n, w)
      +l2 = IP.writes(ws, l, s)
      +hl2 = Equal.trans(Nat, List.length(&2, U32, l2), List.length(&2, U32, l), A.Arrays.slots(d), IP.wlen(ws, l, s), hl)
      %Equal.sym(I.ImgDev & Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l2, 0)}, m), (I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l2, 0)}, Done{B.Octets.of_list(IP.bytes(IP.blk(w, l2, Nat.mul(m, w))))}), IP.read_model(w, c, d, l2, hl2, hd, hs, m, em)) : {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, _) == Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l, 0)}, m)) : Result<&2, &2, D.DevError, B.Octets>}
      %Equal.sym(I.ImgDev & Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l, 0)}, m), (I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l, 0)}, Done{B.Octets.of_list(IP.bytes(IP.blk(w, l, Nat.mul(m, w))))}), IP.read_model(w, c, d, l, hl, hd, hs, m, em)) : {Done{B.Octets.of_list(IP.bytes(IP.blk(w, l2, Nat.mul(m, w))))} == Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, _) : Result<&2, &2, D.DevError, B.Octets>}
      %Equal.sym(List<&2, U32>, IP.blk(w, l2, Nat.mul(m, w)), IP.blk(w, l, Nat.mul(m, w)), IP.disjoint(w, ws, hw, l, n, m, diff, Nat.is_lt(m, n), {==})) : {Done{B.Octets.of_list(IP.bytes(_))} == Done{B.Octets.of_list(IP.bytes(IP.blk(w, l, Nat.mul(m, w))))} : Result<&2, &2, D.DevError, B.Octets>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_lt(m, c), False{}, em) : {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read.check(_, w, c, d, A.Arrays.of_list(U32, d, IP.writes(ws, l, Nat.mul(n, w)), 0), m)) == Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read.check(_, w, c, d, A.Arrays.of_list(U32, d, l, 0), m)) : Result<&2, &2, D.DevError, B.Octets>}
      {==}

# Images built from blocks

def IP.build(bs: List<&2, B.Octets>, l: List<&2, U32>, +k: Nat, +w: Nat) -> List<&2, U32>:
  match bs:
    case Nil{}:
      l
    case Con{b, t}:
      IP.build(t, IP.writes(IP.words(B.Octets.to_list(b)), l, Nat.mul(k, w)), 1n+k, w)

def IP.blen(bs: List<&2, B.Octets>, +l: List<&2, U32>, +k: Nat, +w: Nat) -> {List.length(&2, U32, IP.build(bs, l, k, w)) == List.length(&2, U32, l) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, t}:
      +l1 = IP.writes(IP.words(B.Octets.to_list(b)), l, Nat.mul(k, w))
      Equal.trans(Nat, List.length(&2, U32, IP.build(t, l1, 1n+k, w)), List.length(&2, U32, l1), List.length(&2, U32, l), IP.blen(t, l1, 1n+k, w), IP.wlen(IP.words(B.Octets.to_list(b)), l, Nat.mul(k, w)))

def IP.rep_len(n: Nat, -v: U32) -> {List.length(&2, U32, List.replicate(U32, n, v)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      IP.cong_succ(List.length(&2, U32, List.replicate(U32, p, v)), p, IP.rep_len(p, v))

def IP.ob(bs: List<&2, B.Octets>, +k: Nat, +w: Nat, +c: Nat, +d: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}, +hk: {Nat.is_le(Nat.add(List.length(&2, B.Octets, bs), k), c) == True{} : Bool}, +hal: {I.ImgDev.all_len(bs, Nat.mul(w, 4n)) == True{} : Bool}) -> {I.ImgDev.of_blocks.go(bs, k, I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l, 0)}) == I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, IP.build(bs, l, k, w), 0)} : I.ImgDev}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      +n0 = List.length(&2, B.Octets, t)
      +hn = IP.lt_of_range(n0, k, c, hk)
      +hb = BP.and_l(Nat.is_eq(B.Octets.len(b), Nat.mul(w, 4n)), I.ImgDev.all_len(t, Nat.mul(w, 4n)), hal)
      +ht = BP.and_r(Nat.is_eq(B.Octets.len(b), Nat.mul(w, 4n)), I.ImgDev.all_len(t, Nat.mul(w, 4n)), hal)
      +l1 = IP.writes(IP.words(B.Octets.to_list(b)), l, Nat.mul(k, w))
      +hl1 = Equal.trans(Nat, List.length(&2, U32, l1), List.length(&2, U32, l), A.Arrays.slots(d), IP.wlen(IP.words(B.Octets.to_list(b)), l, Nat.mul(k, w)), hl)
      +hk1 = IP.le_rw_l(Nat.add(n0, 1n+k), 1n+Nat.add(n0, k), c, IP.add_succ(n0, k), hk)
      %Equal.sym(I.ImgDev & Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l, 0)}, k, b), (I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l1, 0)}, Done{Unit{}}), IP.write_model(w, c, d, l, hl, hd, hs, k, hn, b, hb)) : {I.ImgDev.of_blocks.go(t, 1n+k, I.ImgDev.of_blocks.step(_)) == I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, IP.build(t, l1, 1n+k, w), 0)} : I.ImgDev}
      IP.ob(t, 1n+k, w, c, d, l1, hl1, hd, hs, hk1, ht)

def IP.le_succ_self(+k: Nat) -> {Nat.is_le(k, 1n+k) == True{} : Bool}:
  IP.le_succ_r(k, k, IP.le_refl(k))

# later blocks leave an earlier block's words
def IP.bu(bs: List<&2, B.Octets>, +l: List<&2, U32>, +k: Nat, +w: Nat, +s2: Nat, +h: {Nat.is_le(Nat.add(w, s2), Nat.mul(k, w)) == True{} : Bool}) -> {IP.blk(w, IP.build(bs, l, k, w), s2) == IP.blk(w, l, s2) : List<&2, U32>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, t}:
      +ws = IP.words(B.Octets.to_list(b))
      +l1 = IP.writes(ws, l, Nat.mul(k, w))
      Equal.trans(List<&2, U32>, IP.blk(w, IP.build(t, l1, 1n+k, w), s2), IP.blk(w, l1, s2), IP.blk(w, l, s2), IP.bu(t, l1, 1n+k, w, s2, IP.le_trans(Nat.add(w, s2), Nat.mul(k, w), Nat.mul(1n+k, w), h, IP.mul_mono(k, 1n+k, w, IP.le_succ_self(k)))), IP.wd_before(w, ws, l, Nat.mul(k, w), s2, h))

# block i of a build from block k holds the words of the i-th block
def IP.bb(bs: List<&2, B.Octets>, +l: List<&2, U32>, +k: Nat, +w: Nat, i: Nat, +hi: {Nat.is_lt(i, List.length(&2, B.Octets, bs)) == True{} : Bool}, +hal: {I.ImgDev.all_len(bs, Nat.mul(w, 4n)) == True{} : Bool}, +hlb: {Nat.is_le(Nat.mul(Nat.add(List.length(&2, B.Octets, bs), k), w), List.length(&2, U32, l)) == True{} : Bool}) -> {IP.blk(w, IP.build(bs, l, k, w), Nat.mul(Nat.add(i, k), w)) == IP.words(B.Octets.to_list(A.Arrays.nth(B.Octets, bs, i, B.Octets.empty()))) : List<&2, U32>}:
  match bs i:
    case Nil{} _:
      Empty.absurd({IP.blk(w, IP.build(Nil{}, l, k, w), Nat.mul(Nat.add(i, k), w)) == IP.words(B.Octets.to_list(A.Arrays.nth(B.Octets, Nil{}, i, B.Octets.empty()))) : List<&2, U32>}, BP.ft(Equal.trans(Bool, False{}, Nat.is_lt(i, 0n), True{}, Equal.sym(Bool, Nat.is_lt(i, 0n), False{}, IP.lt_zero(i)), hi)))
    case Con{+b, +t} 0n:
      +n0 = List.length(&2, B.Octets, t)
      +hb = BP.and_l(Nat.is_eq(B.Octets.len(b), Nat.mul(w, 4n)), I.ImgDev.all_len(t, Nat.mul(w, 4n)), hal)
      +ht = BP.and_r(Nat.is_eq(B.Octets.len(b), Nat.mul(w, 4n)), I.ImgDev.all_len(t, Nat.mul(w, 4n)), hal)
      +ws = IP.words(B.Octets.to_list(b))
      +s = Nat.mul(k, w)
      +l1 = IP.writes(ws, l, s)
      +hw = IP.words_len(w, B.Octets.to_list(b), IP.list_len(b, w, hb))
      +hl1 = IP.wlen(ws, l, s)
      +hle = IP.le_rw_l(Nat.add(List.length(&2, U32, ws), s), Nat.mul(1n+k, w), List.length(&2, U32, l), Equal.cong(Nat, Nat, x => Nat.add(x, s), List.length(&2, U32, ws), w, hw), IP.le_trans(Nat.mul(1n+k, w), Nat.mul(Nat.add(1n+n0, k), w), List.length(&2, U32, l), IP.mul_mono(1n+k, Nat.add(1n+n0, k), w, IP.le_add(n0, k)), hlb))
      +e2 = Equal.trans(List<&2, U32>, IP.blk(w, l1, s), IP.blk(List.length(&2, U32, ws), l1, s), ws, Equal.cong(Nat, List<&2, U32>, x => IP.blk(x, l1, s), w, List.length(&2, U32, ws), Equal.sym(Nat, List.length(&2, U32, ws), w, hw)), IP.wr(ws, l, s, hle))
      Equal.trans(List<&2, U32>, IP.blk(w, IP.build(t, l1, 1n+k, w), s), IP.blk(w, l1, s), ws, IP.bu(t, l1, 1n+k, w, s, IP.le_refl(Nat.mul(1n+k, w))), e2)
    case Con{+b, +t} 1n+ +j:
      +n0 = List.length(&2, B.Octets, t)
      +hb = BP.and_l(Nat.is_eq(B.Octets.len(b), Nat.mul(w, 4n)), I.ImgDev.all_len(t, Nat.mul(w, 4n)), hal)
      +ht = BP.and_r(Nat.is_eq(B.Octets.len(b), Nat.mul(w, 4n)), I.ImgDev.all_len(t, Nat.mul(w, 4n)), hal)
      +ws = IP.words(B.Octets.to_list(b))
      +s = Nat.mul(k, w)
      +l1 = IP.writes(ws, l, s)
      +hw = IP.words_len(w, B.Octets.to_list(b), IP.list_len(b, w, hb))
      +hl1 = IP.wlen(ws, l, s)
      +hlb1 = IP.le_rw_r(Nat.mul(Nat.add(n0, 1n+k), w), List.length(&2, U32, l1), List.length(&2, U32, l), hl1, IP.le_rw_l(Nat.mul(Nat.add(n0, 1n+k), w), Nat.mul(1n+Nat.add(n0, k), w), List.length(&2, U32, l), Equal.cong(Nat, Nat, x => Nat.mul(x, w), Nat.add(n0, 1n+k), 1n+Nat.add(n0, k), IP.add_succ(n0, k)), hlb))
      %IP.add_succ(j, k) : {IP.blk(w, IP.build(t, l1, 1n+k, w), Nat.mul(_, w)) == IP.words(B.Octets.to_list(A.Arrays.nth(B.Octets, t, j, B.Octets.empty()))) : List<&2, U32>}
      IP.bb(t, l1, 1n+k, w, j, hi, ht, hlb1)

def IP.all_len_nth(bs: List<&2, B.Octets>, n: Nat, +m: Nat, hn: {Nat.is_lt(n, List.length(&2, B.Octets, bs)) == True{} : Bool}, +hal: {I.ImgDev.all_len(bs, m) == True{} : Bool}) -> {Nat.is_eq(B.Octets.len(A.Arrays.nth(B.Octets, bs, n, B.Octets.empty())), m) == True{} : Bool}:
  match bs n:
    case Nil{} _:
      Empty.absurd({Nat.is_eq(B.Octets.len(A.Arrays.nth(B.Octets, Nil{}, n, B.Octets.empty())), m) == True{} : Bool}, BP.ft(Equal.trans(Bool, False{}, Nat.is_lt(n, 0n), True{}, Equal.sym(Bool, Nat.is_lt(n, 0n), False{}, IP.lt_zero(n)), hn)))
    case Con{+b, +t} 0n:
      BP.and_l(Nat.is_eq(B.Octets.len(b), m), I.ImgDev.all_len(t, m), hal)
    case Con{+b, +t} 1n+p:
      IP.all_len_nth(t, p, m, hn, BP.and_r(Nat.is_eq(B.Octets.len(b), m), I.ImgDev.all_len(t, m), hal))

def IP.of_blocks(+d: Nat, +w: Nat, +bs: List<&2, B.Octets>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.mul(List.length(&2, B.Octets, bs), w), A.Arrays.slots(d)) == True{} : Bool}, +hal: {I.ImgDev.all_len(bs, Nat.mul(w, 4n)) == True{} : Bool}, +n: Nat, +hn: {Nat.is_lt(n, List.length(&2, B.Octets, bs)) == True{} : Bool}) -> {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev.of_blocks.at(d, w, bs), n)) == Done{A.Arrays.nth(B.Octets, bs, n, B.Octets.empty())} : Result<&2, &2, D.DevError, B.Octets>}:
  +c = List.length(&2, B.Octets, bs)
  +sd = A.Arrays.slots(d)
  +l0 = List.replicate(U32, sd, 0)
  +hl0 = IP.rep_len(sd, 0)
  +lf = IP.build(bs, l0, 0n, w)
  +hlf = Equal.trans(Nat, List.length(&2, U32, lf), List.length(&2, U32, l0), sd, IP.blen(bs, l0, 0n, w), hl0)
  +nb = A.Arrays.nth(B.Octets, bs, n, B.Octets.empty())
  +hk0 = IP.le_rw_l(Nat.add(c, 0n), c, c, IP.add_zero(c), IP.le_refl(c))
  +hlb = IP.le_rw_r(Nat.mul(Nat.add(c, 0n), w), List.length(&2, U32, l0), sd, hl0, IP.le_rw_l(Nat.mul(Nat.add(c, 0n), w), Nat.mul(c, w), sd, Equal.cong(Nat, Nat, x => Nat.mul(x, w), Nat.add(c, 0n), c, IP.add_zero(c)), hs))
  +ebb = Equal.trans(List<&2, U32>, IP.blk(w, lf, Nat.mul(n, w)), IP.blk(w, lf, Nat.mul(Nat.add(n, 0n), w)), IP.words(B.Octets.to_list(nb)), Equal.cong(Nat, List<&2, U32>, x => IP.blk(w, lf, Nat.mul(x, w)), n, Nat.add(n, 0n), Equal.sym(Nat, Nat.add(n, 0n), n, IP.add_zero(n))), IP.bb(bs, l0, 0n, w, n, hn, hal, hlb))
  %Equal.sym(Array<U32>, Array.new(U32, d, 0), A.Arrays.of_list(U32, d, l0, 0), AL.of_list_new(U32, d, 0)) : {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev.of_blocks.go(bs, 0n, I.ImgDev{w, c, d, _}), n)) == Done{nb} : Result<&2, &2, D.DevError, B.Octets>}
  %Equal.sym(I.ImgDev, I.ImgDev.of_blocks.go(bs, 0n, I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l0, 0)}), I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, lf, 0)}, IP.ob(bs, 0n, w, c, d, l0, hl0, hd, hs, hk0, hal)) : {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(_, n)) == Done{nb} : Result<&2, &2, D.DevError, B.Octets>}
  %Equal.sym(I.ImgDev & Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, lf, 0)}, n), (I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, lf, 0)}, Done{B.Octets.of_list(IP.bytes(IP.blk(w, lf, Nat.mul(n, w))))}), IP.read_model(w, c, d, lf, hlf, hd, hs, n, hn)) : {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, _) == Done{nb} : Result<&2, &2, D.DevError, B.Octets>}
  %Equal.sym(List<&2, U32>, IP.blk(w, lf, Nat.mul(n, w)), IP.words(B.Octets.to_list(nb)), ebb) : {Done{B.Octets.of_list(IP.bytes(_))} == Done{nb} : Result<&2, &2, D.DevError, B.Octets>}
  Equal.cong(B.Octets, Result<&2, &2, D.DevError, B.Octets>, o => Done{o}, B.Octets.of_list(IP.bytes(IP.words(B.Octets.to_list(nb)))), nb, IP.octets_back(nb, w, IP.list_len(nb, w, IP.all_len_nth(bs, n, Nat.mul(w, 4n), hn, hal))))

# The laws for every valid image: each reflects the image's array once

def IP.rw.body(+w: Nat, +c: Nat, +d: Nat, -a: Array<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}, +n: Nat, +data: B.Octets, +len_ok: {Nat.is_eq(B.Octets.len(data), Nat.mul(w, 4n)) == True{} : Bool}, +in_range: {Nat.is_lt(n, c) == True{} : Bool}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, d, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}) -> {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(I.ImgDev{w, c, d, a}, n, data)), n)) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}:
  +l2 = IP.writes(IP.words(B.Octets.to_list(data)), l, Nat.mul(n, w))
  +hl2 = Equal.trans(Nat, List.length(&2, U32, l2), List.length(&2, U32, l), A.Arrays.slots(d), IP.wlen(IP.words(B.Octets.to_list(data)), l, Nat.mul(n, w)), hl)
  %e1 : {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(I.ImgDev{w, c, d, _}, n, data)), n)) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}
  %Equal.sym(I.ImgDev & Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l, 0)}, n, data), (I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l2, 0)}, Done{Unit{}}), IP.write_model(w, c, d, l, hl, hd, hs, n, in_range, data, len_ok)) : {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, _), n)) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}
  %Equal.sym(I.ImgDev & Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l2, 0)}, n), (I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l2, 0)}, Done{B.Octets.of_list(IP.bytes(IP.blk(w, l2, Nat.mul(n, w))))}), IP.read_model(w, c, d, l2, hl2, hd, hs, n, in_range)) : {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, _) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}
  Equal.cong(B.Octets, Result<&2, &2, D.DevError, B.Octets>, o => Done{o}, B.Octets.of_list(IP.bytes(IP.blk(w, l2, Nat.mul(n, w)))), data, IP.rw_model(w, c, d, l, hl, hd, hs, n, in_range, data, len_ok))

def IP.rw.ref(+w: Nat, +c: Nat, +d: Nat, -a: Array<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}, +n: Nat, +data: B.Octets, +len_ok: {Nat.is_eq(B.Octets.len(data), Nat.mul(w, 4n)) == True{} : Bool}, +in_range: {Nat.is_lt(n, c) == True{} : Bool}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, d, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}) -> {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(I.ImgDev{w, c, d, a}, n, data)), n)) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}:
  (l, e) = r
  (e1, hl) = e
  IP.rw.body(w, c, d, a, hd, hs, n, data, len_ok, in_range, l, e1, hl)

def IP.ro.body(+w: Nat, +c: Nat, +d: Nat, -a: Array<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}, +n: Nat, +m: Nat, +data: B.Octets, +len_ok: {Nat.is_eq(B.Octets.len(data), Nat.mul(w, 4n)) == True{} : Bool}, +in_range: {Nat.is_lt(n, c) == True{} : Bool}, +diff: {Nat.is_eq(m, n) == False{} : Bool}, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, d, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}) -> {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(I.ImgDev{w, c, d, a}, n, data)), m)) == Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev{w, c, d, a}, m)) : Result<&2, &2, D.DevError, B.Octets>}:
  +ws = IP.words(B.Octets.to_list(data))
  +l2 = IP.writes(ws, l, Nat.mul(n, w))
  %e1 : {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(I.ImgDev{w, c, d, _}, n, data)), m)) == Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev{w, c, d, _}, m)) : Result<&2, &2, D.DevError, B.Octets>}
  %Equal.sym(I.ImgDev & Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l, 0)}, n, data), (I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l2, 0)}, Done{Unit{}}), IP.write_model(w, c, d, l, hl, hd, hs, n, in_range, data, len_ok)) : {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, _), m)) == Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l, 0)}, m)) : Result<&2, &2, D.DevError, B.Octets>}
  IP.other_model(w, c, d, l, hl, hd, hs, n, in_range, ws, IP.words_len(w, B.Octets.to_list(data), IP.list_len(data, w, len_ok)), m, diff, Nat.is_lt(m, c), {==})

def IP.ro.ref(+w: Nat, +c: Nat, +d: Nat, -a: Array<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}, +n: Nat, +m: Nat, +data: B.Octets, +len_ok: {Nat.is_eq(B.Octets.len(data), Nat.mul(w, 4n)) == True{} : Bool}, +in_range: {Nat.is_lt(n, c) == True{} : Bool}, +diff: {Nat.is_eq(m, n) == False{} : Bool}, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, d, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}) -> {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(I.ImgDev{w, c, d, a}, n, data)), m)) == Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev{w, c, d, a}, m)) : Result<&2, &2, D.DevError, B.Octets>}:
  (l, e) = r
  (e1, hl) = e
  IP.ro.body(w, c, d, a, hd, hs, n, m, data, len_ok, in_range, diff, l, e1, hl)

def IP.wv(+w: Nat, +c: Nat, +d: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}, +n: Nat, +data: B.Octets, okl: Bool, okn: Bool, +el: {Nat.is_eq(B.Octets.len(data), Nat.mul(w, 4n)) == okl : Bool}, +en: {Nat.is_lt(n, c) == okn : Bool}) -> {I.ImgDev.valid(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write.check(okl, okn, w, c, d, A.Arrays.of_list(U32, d, l, 0), n, data))) == True{} : Bool}:
  match okl okn:
    case True{} True{}:
      +ws = IP.words(B.Octets.to_list(data))
      +s = Nat.mul(n, w)
      +hw = IP.words_len(w, B.Octets.to_list(data), IP.list_len(data, w, el))
      +hsw = IP.le_rw_l(Nat.add(List.length(&2, U32, ws), s), Nat.add(w, s), A.Arrays.slots(d), Equal.cong(Nat, Nat, k => Nat.add(k, s), List.length(&2, U32, ws), w, hw), IP.block_in(n, c, w, A.Arrays.slots(d), en, hs))
      %Equal.sym(Array<U32>, I.ImgDev.write.go(B.Octets.to_list(data), s, A.Arrays.of_list(U32, d, l, 0)), A.Arrays.of_list(U32, d, IP.writes(ws, l, s), 0), IP.write_go(B.Octets.to_list(data), s, d, l, hl, hd, hsw)) : {I.ImgDev.valid(I.ImgDev{w, c, d, _}) == True{} : Bool}
      IP.valid_of(w, c, d, IP.writes(ws, l, s), hd, hs)
    case True{} False{}:
      IP.valid_of(w, c, d, l, hd, hs)
    case False{} _:
      IP.valid_of(w, c, d, l, hd, hs)

def IP.wv.body(+w: Nat, +c: Nat, +d: Nat, -a: Array<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}, +n: Nat, +data: B.Octets, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, d, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}) -> {I.ImgDev.valid(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(I.ImgDev{w, c, d, a}, n, data))) == True{} : Bool}:
  %e1 : {I.ImgDev.valid(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(I.ImgDev{w, c, d, _}, n, data))) == True{} : Bool}
  IP.wv(w, c, d, l, hl, hd, hs, n, data, Nat.is_eq(B.Octets.len(data), Nat.mul(w, 4n)), Nat.is_lt(n, c), {==}, {==})

def IP.wv.ref(+w: Nat, +c: Nat, +d: Nat, -a: Array<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}, +n: Nat, +data: B.Octets, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, d, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}) -> {I.ImgDev.valid(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(I.ImgDev{w, c, d, a}, n, data))) == True{} : Bool}:
  (l, e) = r
  (e1, hl) = e
  IP.wv.body(w, c, d, a, hd, hs, n, data, l, e1, hl)

def IP.rs(+w: Nat, +c: Nat, +d: Nat, +l: List<&2, U32>, +hl: {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}, +n: Nat, b: Bool, +eb: {Nat.is_lt(n, c) == b : Bool}) -> {Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read.check(b, w, c, d, A.Arrays.of_list(U32, d, l, 0), n)) == I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l, 0)} : I.ImgDev}:
  match b:
    case True{}:
      %Equal.sym(Array<U32> & List<&2, U32>, I.ImgDev.read.go(w, Nat.mul(n, w), A.Arrays.of_list(U32, d, l, 0)), (A.Arrays.of_list(U32, d, l, 0), IP.bytes(IP.blk(w, l, Nat.mul(n, w)))), IP.read_go(w, Nat.mul(n, w), d, l, hl, hd, IP.block_in(n, c, w, A.Arrays.slots(d), eb, hs))) : {Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read.fin(w, c, d, _)) == I.ImgDev{w, c, d, A.Arrays.of_list(U32, d, l, 0)} : I.ImgDev}
      {==}
    case False{}:
      {==}

def IP.rs.body(+w: Nat, +c: Nat, +d: Nat, -a: Array<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}, +n: Nat, +l: List<&2, U32>, +e1: {A.Arrays.of_list(U32, d, l, 0) == a : Array<U32>}, +hl: {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}) -> {Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev{w, c, d, a}, n)) == I.ImgDev{w, c, d, a} : I.ImgDev}:
  %e1 : {Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev{w, c, d, _}, n)) == I.ImgDev{w, c, d, _} : I.ImgDev}
  IP.rs(w, c, d, l, hl, hd, hs, n, Nat.is_lt(n, c), {==})

def IP.rs.ref(+w: Nat, +c: Nat, +d: Nat, -a: Array<U32>, +hd: {Nat.is_lt(d, 32n) == True{} : Bool}, +hs: {Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)) == True{} : Bool}, +n: Nat, r: &l: List<&2, U32> -> {A.Arrays.of_list(U32, d, l, 0) == a : Array<U32>} & {List.length(&2, U32, l) == A.Arrays.slots(d) : Nat}) -> {Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(I.ImgDev{w, c, d, a}, n)) == I.ImgDev{w, c, d, a} : I.ImgDev}:
  (l, e) = r
  (e1, hl) = e
  IP.rs.body(w, c, d, a, hd, hs, n, l, e1, hl)

def IP.rw.top(img: I.ImgDev, +h: {I.ImgDev.valid(img) == True{} : Bool}, +n: Nat, +data: B.Octets, len_ok: {Nat.is_eq(B.Octets.len(data), Pair.snd(I.ImgDev, Nat, I.ImgDev.block_size(img))) == True{} : Bool}, in_range: {Nat.is_lt(n, Pair.snd(I.ImgDev, Nat, I.ImgDev.block_count(img))) == True{} : Bool}) -> {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(img, n, data)), n)) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}:
  match img:
    case I.ImgDev{+w, +c, +d, a}:
      +hr = BP.and_r(Nat.is_lt(d, 32n), Bool.and(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a)), h)
      IP.rw.ref(w, c, d, a, BP.and_l(Nat.is_lt(d, 32n), Bool.and(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a)), h), BP.and_l(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a), hr), n, data, len_ok, in_range, AL.reflect(U32, d, a, BP.and_r(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a), hr), 0))

def IP.ro.top(img: I.ImgDev, +h: {I.ImgDev.valid(img) == True{} : Bool}, +n: Nat, +m: Nat, +data: B.Octets, len_ok: {Nat.is_eq(B.Octets.len(data), Pair.snd(I.ImgDev, Nat, I.ImgDev.block_size(img))) == True{} : Bool}, in_range: {Nat.is_lt(n, Pair.snd(I.ImgDev, Nat, I.ImgDev.block_count(img))) == True{} : Bool}, diff: {Nat.is_eq(m, n) == False{} : Bool}) -> {Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(img, n, data)), m)) == Pair.snd(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(img, m)) : Result<&2, &2, D.DevError, B.Octets>}:
  match img:
    case I.ImgDev{+w, +c, +d, a}:
      +hr = BP.and_r(Nat.is_lt(d, 32n), Bool.and(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a)), h)
      IP.ro.ref(w, c, d, a, BP.and_l(Nat.is_lt(d, 32n), Bool.and(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a)), h), BP.and_l(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a), hr), n, m, data, len_ok, in_range, diff, AL.reflect(U32, d, a, BP.and_r(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a), hr), 0))

def IP.wv.top(img: I.ImgDev, +h: {I.ImgDev.valid(img) == True{} : Bool}, +n: Nat, +data: B.Octets) -> {I.ImgDev.valid(Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, Unit>, I.ImgDev.write_block(img, n, data))) == True{} : Bool}:
  match img:
    case I.ImgDev{+w, +c, +d, a}:
      +hr = BP.and_r(Nat.is_lt(d, 32n), Bool.and(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a)), h)
      IP.wv.ref(w, c, d, a, BP.and_l(Nat.is_lt(d, 32n), Bool.and(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a)), h), BP.and_l(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a), hr), n, data, AL.reflect(U32, d, a, BP.and_r(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a), hr), 0))

def IP.rs.top(img: I.ImgDev, +h: {I.ImgDev.valid(img) == True{} : Bool}, +n: Nat) -> {Pair.fst(I.ImgDev, Result<&2, &2, D.DevError, B.Octets>, I.ImgDev.read_block(img, n)) == img : I.ImgDev}:
  match img:
    case I.ImgDev{+w, +c, +d, a}:
      +hr = BP.and_r(Nat.is_lt(d, 32n), Bool.and(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a)), h)
      IP.rs.ref(w, c, d, a, BP.and_l(Nat.is_lt(d, 32n), Bool.and(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a)), h), BP.and_l(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a), hr), n, AL.reflect(U32, d, a, BP.and_r(Nat.is_le(Nat.mul(c, w), A.Arrays.slots(d)), A.Arrays.is_perfect(U32, d, a), hr), 0))

def Laws.img_read_write(img, h, n, data, len_ok, in_range):
  IP.rw.top(img, h, n, data, len_ok, in_range)

def Laws.img_write_other(img, h, n, m, data, len_ok, in_range, diff):
  IP.ro.top(img, h, n, m, data, len_ok, in_range, diff)

def Laws.img_write_valid(img, h, n, data):
  IP.wv.top(img, h, n, data)

def Laws.img_read_same(img, h, n):
  IP.rs.top(img, h, n)

def Laws.img_blank_valid(d, w, c, hd, hs):
  %Equal.sym(Array<U32>, Array.new(U32, d, 0), A.Arrays.of_list(U32, d, List.replicate(U32, A.Arrays.slots(d), 0), 0), AL.of_list_new(U32, d, 0)) : {I.ImgDev.valid(I.ImgDev{w, c, d, _}) == True{} : Bool}
  IP.valid_of(w, c, d, List.replicate(U32, A.Arrays.slots(d), 0), hd, hs)

def Laws.img_of_blocks(d, w, bs, hd, hs, hal, n, hn):
  IP.of_blocks(d, w, bs, hd, hs, hal, n, hn)

def Laws.img_witness():
  {==}

def Laws.img_vector_built():
  {==}

def Laws.img_vector_write():
  {==}

def Laws.img_vector_octets():
  {==}

def Laws.img_vector_out_of_range():
  {==}
