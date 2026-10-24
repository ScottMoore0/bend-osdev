# Proofs of LAWS_canon.bend: huff_tree's codes are RFC 1951 3.2.2's
# canonical codes.
#
# huff_tree (huffman.bend) counts the lengths into a list of 16 counts
# (hf.counts), turns them into the list of first codes (hf.next), and then
# walks the symbols in order (hf.assign), giving each symbol of length l the
# entry l of that list, and adding one to it, and inserting the code into
# the tree (hf.ins). The proof follows symbol s through that walk:
#
# * counting by length: hf.counts(ls) is the list of canon_count(ls, n) for
#   n from 0 to 15 (cn.counts_eq, through cn.incshape: one more at the
#   symbol's length);
# * next_code: its entry l, for l from 1 to 15, is canon_next(ls, l)
#   (cn.next_get: the 16 counts are symbolic, the list's shape is not, so
#   each entry computes);
# * codes increasing within a length: before s, each symbol of s's length
#   adds one to that entry, so s gets next_code[l] counted on by those
#   symbols (cn.put_next, cn.stepfix), which is canon_code's value (cn.at);
# * the tree: inserting another symbol leaves s's path as it was
#   (cn.ins_other, cn.others_lo, cn.others_hi: symbols are counted in U32,
#   and a list no longer than a word's value keeps them apart, by
#   bend-osdev-u32's laws), and inserting s itself gives s, if anything,
#   the path of its code's bits, the most significant first (cn.ins_self,
#   cn.ib_bits).
#
# The case splits on the 16 lengths are generated (gen/canon.py).
import Base
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ./eq.bend as Q
import ./huffman.bend as H
import ./LAWS_canon.bend as Laws

# Logic

def cn.bt(+b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def cn.ft(+e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : cn.bt(_)
  Unit{}

def cn.mb(+m: Maybe<&2, List<&2, Bool>>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{p}:
      Unit

def cn.ns(-p: List<&2, Bool>, +e: {None{} == Some{p} : Maybe<&2, List<&2, Bool>>}) -> Empty:
  %Equal.sym(Maybe<&2, List<&2, Bool>>, None{}, Some{p}, e) : cn.mb(_)
  Unit{}

def cn.sn(-p: List<&2, Bool>, +e: {Some{p} == None{} : Maybe<&2, List<&2, Bool>>}) -> Empty:
  %e : cn.mb(_)
  Unit{}

def cn.get(+m: Maybe<&2, List<&2, Bool>>) -> List<&2, Bool>:
  match m:
    case None{}:
      Nil{}
    case Some{p}:
      p

def cn.some_inj(-a: List<&2, Bool>, -b: List<&2, Bool>, +e: {Some{a} == Some{b} : Maybe<&2, List<&2, Bool>>}) -> {a == b : List<&2, Bool>}:
  Equal.cong(Maybe<&2, List<&2, Bool>>, List<&2, Bool>, m => cn.get(m), Some{a}, Some{b}, e)

# Bitwise equality of words is equality (as in PROOF.bend)

def cn.and_l(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def cn.and_r(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, cn.ft(h))

def cn.bit_sound(+a: Bool, +b: Bool, +h: {Bool.not(Bool.xor(a, b)) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, cn.ft(h))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, cn.ft(h))
    case False{} False{}:
      {==}

def cn.word_sound(+n: Nat, +x: Word(n), +y: Word(n), +h: {Q.eq.word(n, x, y) == True{} : Bool}) -> {x == y : Word(n)}:
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match x y:
        case WCon{+a, +s} WCon{+b, +t}:
          %cn.bit_sound(a, b, cn.and_l(Bool.not(Bool.xor(a, b)), Q.eq.word(p, s, t), h)) : {WCon{a, s} == WCon{_, t} : Word(1n+p)}
          %cn.word_sound(p, s, t, cn.and_r(Bool.not(Bool.xor(a, b)), Q.eq.word(p, s, t), h)) : {WCon{a, s} == WCon{a, _} : Word(1n+p)}
          {==}

def cn.u32_sound(+a: U32, +b: U32, +h: {Q.eq.u32(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      %cn.word_sound(32n, x, y, h) : {U32{x} == U32{_} : U32}
      {==}

def cn.word_refl(+n: Nat, +x: Word(n)) -> {Q.eq.word(n, x, x) == True{} : Bool}:
  match n:
    case 0n:
      match x:
        case WNil{}:
          {==}
    case 1n+ +p:
      match x:
        case WCon{a, s}:
          match a:
            case True{}:
              cn.word_refl(p, s)
            case False{}:
              cn.word_refl(p, s)

def cn.u32_refl(+a: U32) -> {Q.eq.u32(a, a) == True{} : Bool}:
  match a:
    case U32{x}:
      cn.word_refl(32n, x)

# Nat

def cn.add1(+j: Nat) -> {Nat.add(j, 1n) == 1n+j : Nat}:
  %UL.nat_add_zero(j) : {Nat.add(j, 1n) == 1n+_ : Nat}
  UL.nat_add_succ(j, 0n)

def cn.sub0(+n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      {==}

def cn.lt_irrefl(+n: Nat) -> {Nat.is_lt(n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      cn.lt_irrefl(p)

def cn.le_succ_lt(+a: Nat, +b: Nat, +h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, cn.ft(h))
    case 0n 1n+ +q:
      {==}
    case 1n+ +p 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, cn.ft(h))
    case 1n+ +p 1n+ +q:
      cn.le_succ_lt(p, q, h)

def cn.le_step(+a: Nat, +b: Nat, +h: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_le(0n, 0n) == True{} : Bool}, cn.ft(h))
    case 0n 1n+ +q:
      {==}
    case 1n+ +p 0n:
      Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, cn.ft(h))
    case 1n+ +p 1n+ +q:
      cn.le_step(p, q, h)

def cn.le_add(+m: Nat, +j: Nat, +b: Nat, +h: {Nat.is_le(Nat.add(m, j), b) == True{} : Bool}) -> {Nat.is_le(j, b) == True{} : Bool}:
  match m:
    case 0n:
      h
    case 1n+ +q:
      cn.le_add(q, j, b, cn.le_step(Nat.add(q, j), b, h))

def cn.lt_succ(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +q:
      {==}
    case 1n+ +p 0n:
      Empty.absurd({Nat.is_lt(1n+p, 1n) == True{} : Bool}, cn.ft(h))
    case 1n+ +p 1n+ +q:
      cn.lt_succ(p, q, h)

def cn.lt_self(+j: Nat) -> {Nat.is_lt(j, 1n+j) == True{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+ +p:
      cn.lt_self(p)

def cn.lt_add_succ(+k: Nat, +j: Nat) -> {Nat.is_lt(j, 1n+Nat.add(k, j)) == True{} : Bool}:
  match k:
    case 0n:
      cn.lt_self(j)
    case 1n+ +q:
      cn.lt_succ(j, 1n+Nat.add(q, j), cn.lt_add_succ(q, j))

def cn.le_lt_succ(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+ +q:
      {==}
    case 1n+ +p 0n:
      Empty.absurd({Nat.is_lt(1n+p, 1n) == True{} : Bool}, cn.ft(h))
    case 1n+ +p 1n+ +q:
      cn.le_lt_succ(p, q, h)

# 1 + (m + j) <= b, as m + (1 + j) <= b
def cn.shift(+m: Nat, +j: Nat, +b: Nat, +h: {Nat.is_le(1n+Nat.add(m, j), b) == True{} : Bool}) -> {Nat.is_le(Nat.add(m, 1n+j), b) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(m, 1n+j), 1n+Nat.add(m, j), UL.nat_add_succ(m, j)) : {Nat.is_le(_, b) == True{} : Bool}
  h

# Symbol numbers: counted in U32, below a word's value they are the
# positions

def cn.sj1(+sym: U32, +j: Nat, +e: {U32.to_nat(sym) == j : Nat}) -> {Nat.add(U32.to_nat(sym), 1n) == 1n+j : Nat}:
  %Equal.sym(Nat, U32.to_nat(sym), j, e) : {Nat.add(_, 1n) == 1n+j : Nat}
  cn.add1(j)

def cn.hb1(+sym: U32, +j: Nat, +e: {U32.to_nat(sym) == j : Nat}, +c: U32, +hb: {Nat.is_le(1n+j, U32.to_nat(c)) == True{} : Bool}) -> {Nat.is_le(Nat.add(U32.to_nat(sym), 1n), U32.to_nat(c)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(U32.to_nat(sym), 1n), 1n+j, cn.sj1(sym, j, e)) : {Nat.is_le(_, U32.to_nat(c)) == True{} : Bool}
  hb

def cn.inc_nat(+sym: U32, +j: Nat, +e: {U32.to_nat(sym) == j : Nat}, +c: U32, +hb: {Nat.is_le(1n+j, U32.to_nat(c)) == True{} : Bool}) -> {U32.to_nat(U32.add(sym, 1)) == 1n+j : Nat}:
  Equal.trans(Nat, U32.to_nat(U32.add(sym, 1)), Nat.add(U32.to_nat(sym), 1n), 1n+j, UL.u32_add_value(sym, 1, c, cn.hb1(sym, j, e, c, hb)), cn.sj1(sym, j, e))

def cn.rw_lt(+sym: U32, +j: Nat, +e: {U32.to_nat(sym) == j : Nat}, +n: Nat, +h: {Nat.is_lt(j, n) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(sym), n) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(sym), j, e) : {Nat.is_lt(_, n) == True{} : Bool}
  h

def cn.rw_gt(+sym: U32, +j: Nat, +e: {U32.to_nat(sym) == j : Nat}, +n: Nat, +h: {Nat.is_lt(n, j) == True{} : Bool}) -> {Nat.is_lt(n, U32.to_nat(sym)) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(sym), j, e) : {Nat.is_lt(n, _) == True{} : Bool}
  h

def cn.rw2(+sym: U32, +j: Nat, +e: {U32.to_nat(sym) == j : Nat}, +s: U32, +n: Nat, +es: {U32.to_nat(s) == n : Nat}, +h: {Nat.is_lt(j, n) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(sym), U32.to_nat(s)) == True{} : Bool}:
  %Equal.sym(Nat, U32.to_nat(sym), j, e) : {Nat.is_lt(_, U32.to_nat(s)) == True{} : Bool}
  %Equal.sym(Nat, U32.to_nat(s), n, es) : {Nat.is_lt(j, _) == True{} : Bool}
  h

def cn.lt_xx(+x: U32, +y: U32, +exy: {x == y : U32}, +h: {Nat.is_lt(U32.to_nat(x), U32.to_nat(y)) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(x), U32.to_nat(x)) == True{} : Bool}:
  %Equal.sym(U32, x, y, exy) : {Nat.is_lt(U32.to_nat(x), U32.to_nat(_)) == True{} : Bool}
  h

def cn.lt_yy(+x: U32, +y: U32, +exy: {x == y : U32}, +h: {Nat.is_lt(U32.to_nat(y), U32.to_nat(x)) == True{} : Bool}) -> {Nat.is_lt(U32.to_nat(y), U32.to_nat(y)) == True{} : Bool}:
  %exy : {Nat.is_lt(U32.to_nat(y), U32.to_nat(_)) == True{} : Bool}
  h

def cn.irrefl_true(+n: Nat, +h: {Nat.is_lt(n, n) == True{} : Bool}) -> Empty:
  cn.ft(Equal.trans(Bool, False{}, Nat.is_lt(n, n), True{}, Equal.sym(Bool, Nat.is_lt(n, n), False{}, cn.lt_irrefl(n)), h))

def cn.eqf_lt(+b: Bool, +x: U32, +y: U32, +eb: {Q.eq.u32(x, y) == b : Bool}, +h: {Nat.is_lt(U32.to_nat(x), U32.to_nat(y)) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, cn.irrefl_true(U32.to_nat(x), cn.lt_xx(x, y, cn.u32_sound(x, y, eb), h)))

def cn.eqf_gt(+b: Bool, +x: U32, +y: U32, +eb: {Q.eq.u32(x, y) == b : Bool}, +h: {Nat.is_lt(U32.to_nat(y), U32.to_nat(x)) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, cn.irrefl_true(U32.to_nat(y), cn.lt_yy(x, y, cn.u32_sound(x, y, eb), h)))

def cn.eq_false_lt(+x: U32, +y: U32, +h: {Nat.is_lt(U32.to_nat(x), U32.to_nat(y)) == True{} : Bool}) -> {Q.eq.u32(x, y) == False{} : Bool}:
  cn.eqf_lt(Q.eq.u32(x, y), x, y, {==}, h)

def cn.eq_false_gt(+x: U32, +y: U32, +h: {Nat.is_lt(U32.to_nat(y), U32.to_nat(x)) == True{} : Bool}) -> {Q.eq.u32(x, y) == False{} : Bool}:
  cn.eqf_gt(Q.eq.u32(x, y), x, y, {==}, h)

# The tree: inserting another symbol leaves s's path as it was

def cn.ins_other(+l: Nat, +b: Bool, +code: U32, +t: H.DflTree, +sym: U32, +s: U32, +e: {Q.eq.u32(sym, s) == False{} : Bool}) -> {H.huff_path(H.hf.ins(l, b, code, t, sym), s) == H.huff_path(t, s) : Maybe<&2, List<&2, Bool>>}:
  match l:
    case 0n:
      match t:
        case H.DflHNil{}:
          %e : {H.hf.path.leaf(Q.eq.u32(sym, s)) == H.hf.path.leaf(_) : Maybe<&2, List<&2, Bool>>}
          {==}
        case H.DflHLeaf{x}:
          {==}
        case H.DflHNode{z, o}:
          {==}
    case 1n+ +p:
      match b:
        case True{}:
          match t:
            case H.DflHNode{+z, o}:
              %cn.ins_other(p, H.hf.bit(code, Nat.sub(p, 1n)), code, o, sym, s, e) : {H.hf.path.pick(H.huff_path(z, s), H.huff_path(H.hf.ins(p, H.hf.bit(code, Nat.sub(p, 1n)), code, o, sym), s)) == H.hf.path.pick(H.huff_path(z, s), _) : Maybe<&2, List<&2, Bool>>}
              {==}
            case H.DflHNil{}:
              %Equal.sym(Maybe<&2, List<&2, Bool>>, H.huff_path(H.hf.ins(p, H.hf.bit(code, Nat.sub(p, 1n)), code, H.DflHNil{}, sym), s), H.huff_path(H.DflHNil{}, s), cn.ins_other(p, H.hf.bit(code, Nat.sub(p, 1n)), code, H.DflHNil{}, sym, s, e)) : {H.hf.path.pick(None{}, _) == None{} : Maybe<&2, List<&2, Bool>>}
              {==}
            case H.DflHLeaf{x}:
              {==}
        case False{}:
          match t:
            case H.DflHNode{z, +o}:
              %cn.ins_other(p, H.hf.bit(code, Nat.sub(p, 1n)), code, z, sym, s, e) : {H.hf.path.pick(H.huff_path(H.hf.ins(p, H.hf.bit(code, Nat.sub(p, 1n)), code, z, sym), s), H.huff_path(o, s)) == H.hf.path.pick(_, H.huff_path(o, s)) : Maybe<&2, List<&2, Bool>>}
              {==}
            case H.DflHNil{}:
              %Equal.sym(Maybe<&2, List<&2, Bool>>, H.huff_path(H.hf.ins(p, H.hf.bit(code, Nat.sub(p, 1n)), code, H.DflHNil{}, sym), s), H.huff_path(H.DflHNil{}, s), cn.ins_other(p, H.hf.bit(code, Nat.sub(p, 1n)), code, H.DflHNil{}, sym, s, e)) : {H.hf.path.pick(_, None{}) == None{} : Maybe<&2, List<&2, Bool>>}
              {==}
            case H.DflHLeaf{x}:
              {==}

# The tree: inserting s itself gives s (if anything) the path of the bits
# the insertion follows

def cn.insbits(+l: Nat, +b: Bool, +code: U32) -> List<&2, Bool>:
  match l:
    case 0n:
      Nil{}
    case 1n+ +p:
      Con{b, cn.insbits(p, H.hf.bit(code, Nat.sub(p, 1n)), code)}

# m is none, or q
def cn.mres(+m: Maybe<&2, List<&2, Bool>>, +q: List<&2, Bool>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      {x == q : List<&2, Bool>}

def cn.mres_t(+m: Maybe<&2, List<&2, Bool>>, +q: List<&2, Bool>, ih: cn.mres(m, q)) -> cn.mres(H.hf.path.pick(None{}, m), Con{True{}, q}):
  match m:
    case None{}:
      Unit{}
    case Some{x}:
      %ih : {Con{True{}, x} == Con{True{}, _} : List<&2, Bool>}
      {==}

def cn.mres_f(+m: Maybe<&2, List<&2, Bool>>, +q: List<&2, Bool>, ih: cn.mres(m, q)) -> cn.mres(H.hf.path.pick(m, None{}), Con{False{}, q}):
  match m:
    case None{}:
      Unit{}
    case Some{x}:
      %ih : {Con{False{}, x} == Con{False{}, _} : List<&2, Bool>}
      {==}

def cn.pick_none_l(+mz: Maybe<&2, List<&2, Bool>>, +mo: Maybe<&2, List<&2, Bool>>, +e: {H.hf.path.pick(mz, mo) == None{} : Maybe<&2, List<&2, Bool>>}) -> {mz == None{} : Maybe<&2, List<&2, Bool>>}:
  match mz:
    case None{}:
      {==}
    case Some{x}:
      Empty.absurd({Some{x} == None{} : Maybe<&2, List<&2, Bool>>}, cn.sn(Con{False{}, x}, e))

def cn.pick_none_r(+mz: Maybe<&2, List<&2, Bool>>, +mo: Maybe<&2, List<&2, Bool>>, +e: {H.hf.path.pick(mz, mo) == None{} : Maybe<&2, List<&2, Bool>>}) -> {mo == None{} : Maybe<&2, List<&2, Bool>>}:
  match mz:
    case Some{x}:
      Empty.absurd({mo == None{} : Maybe<&2, List<&2, Bool>>}, cn.sn(Con{False{}, x}, e))
    case None{}:
      match mo:
        case None{}:
          {==}
        case Some{y}:
          Empty.absurd({Some{y} == None{} : Maybe<&2, List<&2, Bool>>}, cn.sn(Con{True{}, y}, e))

def cn.ins_self(+l: Nat, +b: Bool, +code: U32, +t: H.DflTree, +s: U32, +e: {H.huff_path(t, s) == None{} : Maybe<&2, List<&2, Bool>>}) -> cn.mres(H.huff_path(H.hf.ins(l, b, code, t, s), s), cn.insbits(l, b, code)):
  match l:
    case 0n:
      match t:
        case H.DflHNil{}:
          %Equal.sym(Bool, Q.eq.u32(s, s), True{}, cn.u32_refl(s)) : cn.mres(H.hf.path.leaf(_), Nil{})
          {==}
        case H.DflHLeaf{x}:
          %Equal.sym(Maybe<&2, List<&2, Bool>>, H.huff_path(H.DflHLeaf{x}, s), None{}, e) : cn.mres(_, Nil{})
          Unit{}
        case H.DflHNode{z, o}:
          %Equal.sym(Maybe<&2, List<&2, Bool>>, H.huff_path(H.DflHNode{z, o}, s), None{}, e) : cn.mres(_, Nil{})
          Unit{}
    case 1n+ +p:
      match b:
        case True{}:
          match t:
            case H.DflHNode{+z, +o}:
              +bb = H.hf.bit(code, Nat.sub(p, 1n))
              %Equal.sym(Maybe<&2, List<&2, Bool>>, H.huff_path(z, s), None{}, cn.pick_none_l(H.huff_path(z, s), H.huff_path(o, s), e)) : cn.mres(H.hf.path.pick(_, H.huff_path(H.hf.ins(p, bb, code, o, s), s)), Con{True{}, cn.insbits(p, bb, code)})
              cn.mres_t(H.huff_path(H.hf.ins(p, bb, code, o, s), s), cn.insbits(p, bb, code), cn.ins_self(p, bb, code, o, s, cn.pick_none_r(H.huff_path(z, s), H.huff_path(o, s), e)))
            case H.DflHNil{}:
              +bb = H.hf.bit(code, Nat.sub(p, 1n))
              cn.mres_t(H.huff_path(H.hf.ins(p, bb, code, H.DflHNil{}, s), s), cn.insbits(p, bb, code), cn.ins_self(p, bb, code, H.DflHNil{}, s, {==}))
            case H.DflHLeaf{x}:
              %Equal.sym(Maybe<&2, List<&2, Bool>>, H.huff_path(H.DflHLeaf{x}, s), None{}, e) : cn.mres(_, Con{True{}, cn.insbits(p, H.hf.bit(code, Nat.sub(p, 1n)), code)})
              Unit{}
        case False{}:
          match t:
            case H.DflHNode{+z, +o}:
              +bb = H.hf.bit(code, Nat.sub(p, 1n))
              %Equal.sym(Maybe<&2, List<&2, Bool>>, H.huff_path(o, s), None{}, cn.pick_none_r(H.huff_path(z, s), H.huff_path(o, s), e)) : cn.mres(H.hf.path.pick(H.huff_path(H.hf.ins(p, bb, code, z, s), s), _), Con{False{}, cn.insbits(p, bb, code)})
              cn.mres_f(H.huff_path(H.hf.ins(p, bb, code, z, s), s), cn.insbits(p, bb, code), cn.ins_self(p, bb, code, z, s, cn.pick_none_l(H.huff_path(z, s), H.huff_path(o, s), e)))
            case H.DflHNil{}:
              +bb = H.hf.bit(code, Nat.sub(p, 1n))
              cn.mres_f(H.huff_path(H.hf.ins(p, bb, code, H.DflHNil{}, s), s), cn.insbits(p, bb, code), cn.ins_self(p, bb, code, H.DflHNil{}, s, {==}))
            case H.DflHLeaf{x}:
              %Equal.sym(Maybe<&2, List<&2, Bool>>, H.huff_path(H.DflHLeaf{x}, s), None{}, e) : cn.mres(_, Con{False{}, cn.insbits(p, H.hf.bit(code, Nat.sub(p, 1n)), code)})
              Unit{}

# the bits followed are the code's bits, the most significant first
def cn.ib_bits(+p: Nat, +code: U32) -> {cn.insbits(p, H.hf.bit(code, Nat.sub(p, 1n)), code) == Laws.canon_bits(p, code) : List<&2, Bool>}:
  match p:
    case 0n:
      {==}
    case 1n+ +q:
      %cn.sub0(q) : {Con{H.hf.bit(code, Nat.sub(q, 0n)), cn.insbits(q, H.hf.bit(code, Nat.sub(q, 1n)), code)} == Con{H.hf.bit(code, _), Laws.canon_bits(q, code)} : List<&2, Bool>}
      %cn.ib_bits(q, code) : {Con{H.hf.bit(code, Nat.sub(q, 0n)), cn.insbits(q, H.hf.bit(code, Nat.sub(q, 1n)), code)} == Con{H.hf.bit(code, Nat.sub(q, 0n)), _} : List<&2, Bool>}
      {==}

def cn.ib_top(+q: Nat, +code: U32) -> {cn.insbits(1n+q, H.hf.bit(code, q), code) == Laws.canon_bits(1n+q, code) : List<&2, Bool>}:
  %cn.ib_bits(q, code) : {Con{H.hf.bit(code, q), cn.insbits(q, H.hf.bit(code, Nat.sub(q, 1n)), code)} == Con{H.hf.bit(code, q), _} : List<&2, Bool>}
  {==}

def cn.mres_use(+m: Maybe<&2, List<&2, Bool>>, +q: List<&2, Bool>, +p: List<&2, Bool>, +e: {m == Some{p} : Maybe<&2, List<&2, Bool>>}, r: cn.mres(m, q)) -> {p == q : List<&2, Bool>}:
  match m:
    case None{}:
      Empty.absurd({p == q : List<&2, Bool>}, cn.ns(p, e))
    case Some{+x}:
      Equal.trans(List<&2, Bool>, p, x, q, Equal.sym(List<&2, Bool>, x, p, cn.some_inj(x, p, e)), r)

# The walk over the symbols

def cn.accn(+a: H.DflHufAcc) -> List<&2, U32>:
  match a:
    case H.DflHufAcc{n, t}:
      n

def cn.put_other(+l: Nat, +a: H.DflHufAcc, +sym: U32, +s: U32, +e: {Q.eq.u32(sym, s) == False{} : Bool}) -> {H.huff_path(H.hf.acc.tree(H.hf.put.len(l, a, sym)), s) == H.huff_path(H.hf.acc.tree(a), s) : Maybe<&2, List<&2, Bool>>}:
  match l:
    case 0n:
      {==}
    case 1n+ +p:
      match a:
        case H.DflHufAcc{+nx, t}:
          cn.ins_other(1n+p, H.hf.bit(H.hf.get(nx, 1n+p), p), H.hf.get(nx, 1n+p), t, sym, s, e)

# the symbols before s (positions j on, all below s's) leave its path
def cn.others_lo(+xs: List<&2, U32>, +sym: U32, +j: Nat, +e: {U32.to_nat(sym) == j : Nat}, +a: H.DflHufAcc, +s: U32, +c: U32, +hb: {Nat.is_le(Nat.add(List.length(&2, U32, xs), j), U32.to_nat(c)) == True{} : Bool}, +hlo: {Nat.is_le(Nat.add(List.length(&2, U32, xs), j), U32.to_nat(s)) == True{} : Bool}) -> {H.huff_path(H.hf.acc.tree(H.hf.assign(xs, sym, a)), s) == H.huff_path(H.hf.acc.tree(a), s) : Maybe<&2, List<&2, Bool>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +hb2 = cn.shift(List.length(&2, U32, t), j, U32.to_nat(c), hb)
      +hlo2 = cn.shift(List.length(&2, U32, t), j, U32.to_nat(s), hlo)
      +e2 = cn.inc_nat(sym, j, e, c, cn.le_add(List.length(&2, U32, t), 1n+j, U32.to_nat(c), hb2))
      +lt = cn.rw_lt(sym, j, e, U32.to_nat(s), cn.le_succ_lt(j, U32.to_nat(s), cn.le_add(List.length(&2, U32, t), 1n+j, U32.to_nat(s), hlo2)))
      +a2 = H.hf.put.len(U32.to_nat(h), a, sym)
      Equal.trans(Maybe<&2, List<&2, Bool>>, H.huff_path(H.hf.acc.tree(H.hf.assign(t, U32.add(sym, 1), a2)), s), H.huff_path(H.hf.acc.tree(a2), s), H.huff_path(H.hf.acc.tree(a), s), cn.others_lo(t, U32.add(sym, 1), 1n+j, e2, a2, s, c, hb2, hlo2), cn.put_other(U32.to_nat(h), a, sym, s, cn.eq_false_lt(sym, s, lt)))

# the symbols after s (positions j on, all above s's) leave its path
def cn.others_hi(+xs: List<&2, U32>, +sym: U32, +j: Nat, +e: {U32.to_nat(sym) == j : Nat}, +a: H.DflHufAcc, +s: U32, +c: U32, +hb: {Nat.is_le(Nat.add(List.length(&2, U32, xs), j), U32.to_nat(c)) == True{} : Bool}, +hhi: {Nat.is_lt(U32.to_nat(s), j) == True{} : Bool}) -> {H.huff_path(H.hf.acc.tree(H.hf.assign(xs, sym, a)), s) == H.huff_path(H.hf.acc.tree(a), s) : Maybe<&2, List<&2, Bool>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +hb2 = cn.shift(List.length(&2, U32, t), j, U32.to_nat(c), hb)
      +e2 = cn.inc_nat(sym, j, e, c, cn.le_add(List.length(&2, U32, t), 1n+j, U32.to_nat(c), hb2))
      +gt = cn.rw_gt(sym, j, e, U32.to_nat(s), hhi)
      +a2 = H.hf.put.len(U32.to_nat(h), a, sym)
      Equal.trans(Maybe<&2, List<&2, Bool>>, H.huff_path(H.hf.acc.tree(H.hf.assign(t, U32.add(sym, 1), a2)), s), H.huff_path(H.hf.acc.tree(a2), s), H.huff_path(H.hf.acc.tree(a), s), cn.others_hi(t, U32.add(sym, 1), 1n+j, e2, a2, s, c, hb2, cn.lt_succ(U32.to_nat(s), j, hhi)), cn.put_other(U32.to_nat(h), a, sym, s, cn.eq_false_gt(sym, s, gt)))

# The first codes: one more at a symbol's length

def cn.get_inc(+xs: List<&2, U32>, +jn: Nat, +L: Nat, +h: {Nat.is_lt(L, List.length(&2, U32, xs)) == True{} : Bool}) -> {H.hf.get(H.hf.inc(xs, jn), L) == Laws.canon_step(Nat.is_eq(jn, L), H.hf.get(xs, L)) : U32}:
  match xs:
    case Nil{}:
      match L:
        case 0n:
          Empty.absurd({H.hf.get(H.hf.inc(Nil{}, jn), 0n) == Laws.canon_step(Nat.is_eq(jn, 0n), H.hf.get(Nil{}, 0n)) : U32}, cn.ft(h))
        case 1n+ +lp:
          Empty.absurd({H.hf.get(H.hf.inc(Nil{}, jn), 1n+lp) == Laws.canon_step(Nat.is_eq(jn, 1n+lp), H.hf.get(Nil{}, 1n+lp)) : U32}, cn.ft(h))
    case Con{+x, t}:
      match jn L:
        case 0n 0n:
          {==}
        case 0n 1n+ +lp:
          {==}
        case 1n+ +jp 0n:
          {==}
        case 1n+ +jp 1n+ +lp:
          cn.get_inc(t, jp, lp, h)

def cn.len_inc(+xs: List<&2, U32>, +jn: Nat) -> {List.length(&2, U32, H.hf.inc(xs, jn)) == List.length(&2, U32, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      match jn:
        case 0n:
          {==}
        case 1n+ +jp:
          %cn.len_inc(t, jp) : {1n+List.length(&2, U32, H.hf.inc(t, jp)) == 1n+_ : Nat}
          {==}

def cn.put_next(+q: Nat, +lh: Nat, +a: H.DflHufAcc, +sym: U32, +h: {Nat.is_lt(1n+q, List.length(&2, U32, cn.accn(a))) == True{} : Bool}) -> {H.hf.get(cn.accn(H.hf.put.len(lh, a, sym)), 1n+q) == Laws.canon_step(Nat.is_eq(lh, 1n+q), H.hf.get(cn.accn(a), 1n+q)) : U32}:
  match lh:
    case 0n:
      {==}
    case 1n+ +p:
      match a:
        case H.DflHufAcc{+nx, t}:
          cn.get_inc(nx, 1n+p, 1n+q, h)

def cn.put_len(+lh: Nat, +a: H.DflHufAcc, +sym: U32) -> {List.length(&2, U32, cn.accn(H.hf.put.len(lh, a, sym))) == List.length(&2, U32, cn.accn(a)) : Nat}:
  match lh:
    case 0n:
      {==}
    case 1n+ +p:
      match a:
        case H.DflHufAcc{+nx, t}:
          cn.len_inc(nx, 1n+p)

def cn.hlen2(+L: Nat, +lh: Nat, +a: H.DflHufAcc, +sym: U32, +h: {Nat.is_lt(L, List.length(&2, U32, cn.accn(a))) == True{} : Bool}) -> {Nat.is_lt(L, List.length(&2, U32, cn.accn(H.hf.put.len(lh, a, sym)))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, U32, cn.accn(H.hf.put.len(lh, a, sym))), List.length(&2, U32, cn.accn(a)), cn.put_len(lh, a, sym)) : {Nat.is_lt(L, _) == True{} : Bool}
  h

# What the walk gives s: for a length of 0, nothing (Empty: the case cannot
# arise); else the code's bits, of the value v
def cn.atty(+L: Nat, +p: List<&2, Bool>, +v: U32) -> Type:
  match L:
    case 0n:
      Empty
    case 1n+ +q:
      {Some{Laws.canon_bits(1n+q, v)} == Some{p} : Maybe<&2, List<&2, Bool>>}

def cn.stepfix(+L: Nat, +lh: Nat, +a: H.DflHufAcc, +sym: U32, +T: List<&2, U32>, +p: List<&2, Bool>, +hlen: {Nat.is_lt(L, List.length(&2, U32, cn.accn(a))) == True{} : Bool}, ih: cn.atty(L, p, Laws.canon_count.go(T, L, H.hf.get(cn.accn(H.hf.put.len(lh, a, sym)), L)))) -> cn.atty(L, p, Laws.canon_count.go(T, L, Laws.canon_step(Nat.is_eq(lh, L), H.hf.get(cn.accn(a), L)))):
  match L:
    case 0n:
      ih
    case 1n+ +q:
      %cn.put_next(q, lh, a, sym, hlen) : cn.atty(1n+q, p, Laws.canon_count.go(T, 1n+q, _))
      ih

def cn.rw_put(+lh: Nat, +L: Nat, +hL: {lh == L : Nat}, +a: H.DflHufAcc, +sym: U32, +s: U32, +eqs: {sym == s : U32}, +p: List<&2, Bool>, +hp2: {H.huff_path(H.hf.acc.tree(H.hf.put.len(lh, a, sym)), s) == Some{p} : Maybe<&2, List<&2, Bool>>}) -> {H.huff_path(H.hf.acc.tree(H.hf.put.len(L, a, s)), s) == Some{p} : Maybe<&2, List<&2, Bool>>}:
  %hL : {H.huff_path(H.hf.acc.tree(H.hf.put.len(_, a, s)), s) == Some{p} : Maybe<&2, List<&2, Bool>>}
  %eqs : {H.huff_path(H.hf.acc.tree(H.hf.put.len(lh, a, _)), s) == Some{p} : Maybe<&2, List<&2, Bool>>}
  hp2

# s's own step: its code is the entry of its length
def cn.fin(+L: Nat, +a: H.DflHufAcc, +s: U32, +p: List<&2, Bool>, +hn: {H.huff_path(H.hf.acc.tree(a), s) == None{} : Maybe<&2, List<&2, Bool>>}, +hp3: {H.huff_path(H.hf.acc.tree(H.hf.put.len(L, a, s)), s) == Some{p} : Maybe<&2, List<&2, Bool>>}) -> cn.atty(L, p, H.hf.get(cn.accn(a), L)):
  match L:
    case 0n:
      cn.ns(p, Equal.trans(Maybe<&2, List<&2, Bool>>, None{}, H.huff_path(H.hf.acc.tree(a), s), Some{p}, Equal.sym(Maybe<&2, List<&2, Bool>>, H.huff_path(H.hf.acc.tree(a), s), None{}, hn), hp3))
    case 1n+ +q:
      match a:
        case H.DflHufAcc{+nx, +tr}:
          +code = H.hf.get(nx, 1n+q)
          +ins = H.hf.ins(1n+q, H.hf.bit(code, q), code, tr, s)
          +ib = cn.insbits(1n+q, H.hf.bit(code, q), code)
          +pe = cn.mres_use(H.huff_path(ins, s), ib, p, hp3, cn.ins_self(1n+q, H.hf.bit(code, q), code, tr, s, hn))
          +cb = Laws.canon_bits(1n+q, code)
          Equal.cong(List<&2, Bool>, Maybe<&2, List<&2, Bool>>, v => Some{v}, cb, p, Equal.trans(List<&2, Bool>, cb, ib, p, Equal.sym(List<&2, Bool>, ib, cb, cn.ib_top(q, code)), Equal.sym(List<&2, Bool>, p, ib, pe)))

# the walk from position j on, s being k positions further: s's path, if
# any, is the code of s's length L, of value the entry L counted on by the
# symbols before s of length L
def cn.at(+xs: List<&2, U32>, +k: Nat, +sym: U32, +j: Nat, +e: {U32.to_nat(sym) == j : Nat}, +a: H.DflHufAcc, +s: U32, +es: {U32.to_nat(s) == Nat.add(k, j) : Nat}, +c: U32, +hb: {Nat.is_le(Nat.add(List.length(&2, U32, xs), j), U32.to_nat(c)) == True{} : Bool}, +hn: {H.huff_path(H.hf.acc.tree(a), s) == None{} : Maybe<&2, List<&2, Bool>>}, +L: Nat, +hL: {U32.to_nat(Laws.canon_len(xs, k)) == L : Nat}, +hlen: {Nat.is_lt(L, List.length(&2, U32, cn.accn(a))) == True{} : Bool}, +p: List<&2, Bool>, +hp: {H.huff_path(H.hf.acc.tree(H.hf.assign(xs, sym, a)), s) == Some{p} : Maybe<&2, List<&2, Bool>>}) -> cn.atty(L, p, Laws.canon_count.go(List.take(&2, U32, xs, k), L, H.hf.get(cn.accn(a), L))):
  match xs k:
    case Nil{} _:
      Empty.absurd(cn.atty(L, p, Laws.canon_count.go(List.take(&2, U32, Nil{}, k), L, H.hf.get(cn.accn(a), L))), cn.ns(p, Equal.trans(Maybe<&2, List<&2, Bool>>, None{}, H.huff_path(H.hf.acc.tree(a), s), Some{p}, Equal.sym(Maybe<&2, List<&2, Bool>>, H.huff_path(H.hf.acc.tree(a), s), None{}, hn), hp)))
    case Con{+h, +t} 0n:
      +hb2 = cn.shift(List.length(&2, U32, t), j, U32.to_nat(c), hb)
      +e2 = cn.inc_nat(sym, j, e, c, cn.le_add(List.length(&2, U32, t), 1n+j, U32.to_nat(c), hb2))
      +a2 = H.hf.put.len(U32.to_nat(h), a, sym)
      +eqs = UL.u32_value_eq(sym, s, Equal.trans(Nat, U32.to_nat(sym), j, U32.to_nat(s), e, Equal.sym(Nat, U32.to_nat(s), j, es)))
      +hhi = cn.rw_lt(s, j, es, 1n+j, cn.lt_self(j))
      +oh = cn.others_hi(t, U32.add(sym, 1), 1n+j, e2, a2, s, c, hb2, hhi)
      +hp2 = Equal.trans(Maybe<&2, List<&2, Bool>>, H.huff_path(H.hf.acc.tree(a2), s), H.huff_path(H.hf.acc.tree(H.hf.assign(t, U32.add(sym, 1), a2)), s), Some{p}, Equal.sym(Maybe<&2, List<&2, Bool>>, H.huff_path(H.hf.acc.tree(H.hf.assign(t, U32.add(sym, 1), a2)), s), H.huff_path(H.hf.acc.tree(a2), s), oh), hp)
      cn.fin(L, a, s, p, hn, cn.rw_put(U32.to_nat(h), L, hL, a, sym, s, eqs, p, hp2))
    case Con{+h, +t} 1n+ +kp:
      +hb2 = cn.shift(List.length(&2, U32, t), j, U32.to_nat(c), hb)
      +e2 = cn.inc_nat(sym, j, e, c, cn.le_add(List.length(&2, U32, t), 1n+j, U32.to_nat(c), hb2))
      +a2 = H.hf.put.len(U32.to_nat(h), a, sym)
      +lt = cn.rw2(sym, j, e, s, 1n+Nat.add(kp, j), es, cn.lt_add_succ(kp, j))
      +hn2 = Equal.trans(Maybe<&2, List<&2, Bool>>, H.huff_path(H.hf.acc.tree(a2), s), H.huff_path(H.hf.acc.tree(a), s), None{}, cn.put_other(U32.to_nat(h), a, sym, s, cn.eq_false_lt(sym, s, lt)), hn)
      +es2 = Equal.trans(Nat, U32.to_nat(s), 1n+Nat.add(kp, j), Nat.add(kp, 1n+j), es, Equal.sym(Nat, Nat.add(kp, 1n+j), 1n+Nat.add(kp, j), UL.nat_add_succ(kp, j)))
      ih = cn.at(t, kp, U32.add(sym, 1), 1n+j, e2, a2, s, es2, c, hb2, hn2, L, hL, cn.hlen2(L, U32.to_nat(h), a, sym, hlen), p, hp)
      cn.stepfix(L, U32.to_nat(h), a, sym, List.take(&2, U32, t, kp), p, hlen, ih)

# Counting by length, and the first codes

# BEGIN GENERATED by gen/canon.py
# one more at length n, for each n (a symbol of length 16 or more is
# not counted)
def cn.incshape(+n: Nat, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +a8: U32, +a9: U32, +a10: U32, +a11: U32, +a12: U32, +a13: U32, +a14: U32, +a15: U32) -> {H.hf.inc(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Nil{}}}}}}}}}}}}}}}}}, n) == Con{Laws.canon_step(Nat.is_eq(n, 0n), a0), Con{Laws.canon_step(Nat.is_eq(n, 1n), a1), Con{Laws.canon_step(Nat.is_eq(n, 2n), a2), Con{Laws.canon_step(Nat.is_eq(n, 3n), a3), Con{Laws.canon_step(Nat.is_eq(n, 4n), a4), Con{Laws.canon_step(Nat.is_eq(n, 5n), a5), Con{Laws.canon_step(Nat.is_eq(n, 6n), a6), Con{Laws.canon_step(Nat.is_eq(n, 7n), a7), Con{Laws.canon_step(Nat.is_eq(n, 8n), a8), Con{Laws.canon_step(Nat.is_eq(n, 9n), a9), Con{Laws.canon_step(Nat.is_eq(n, 10n), a10), Con{Laws.canon_step(Nat.is_eq(n, 11n), a11), Con{Laws.canon_step(Nat.is_eq(n, 12n), a12), Con{Laws.canon_step(Nat.is_eq(n, 13n), a13), Con{Laws.canon_step(Nat.is_eq(n, 14n), a14), Con{Laws.canon_step(Nat.is_eq(n, 15n), a15), Nil{}}}}}}}}}}}}}}}}} : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+ +n1:
      match n1:
        case 0n:
          {==}
        case 1n+ +n2:
          match n2:
            case 0n:
              {==}
            case 1n+ +n3:
              match n3:
                case 0n:
                  {==}
                case 1n+ +n4:
                  match n4:
                    case 0n:
                      {==}
                    case 1n+ +n5:
                      match n5:
                        case 0n:
                          {==}
                        case 1n+ +n6:
                          match n6:
                            case 0n:
                              {==}
                            case 1n+ +n7:
                              match n7:
                                case 0n:
                                  {==}
                                case 1n+ +n8:
                                  match n8:
                                    case 0n:
                                      {==}
                                    case 1n+ +n9:
                                      match n9:
                                        case 0n:
                                          {==}
                                        case 1n+ +n10:
                                          match n10:
                                            case 0n:
                                              {==}
                                            case 1n+ +n11:
                                              match n11:
                                                case 0n:
                                                  {==}
                                                case 1n+ +n12:
                                                  match n12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+ +n13:
                                                      match n13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+ +n14:
                                                          match n14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+ +n15:
                                                              match n15:
                                                                case 0n:
                                                                  {==}
                                                                case 1n+ +n16:
                                                                  {==}

# the counts, from any 16 starting values
def cn.cgo(+ls: List<&2, U32>, +a0: U32, +a1: U32, +a2: U32, +a3: U32, +a4: U32, +a5: U32, +a6: U32, +a7: U32, +a8: U32, +a9: U32, +a10: U32, +a11: U32, +a12: U32, +a13: U32, +a14: U32, +a15: U32) -> {H.hf.counts.go(ls, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Nil{}}}}}}}}}}}}}}}}}) == Con{Laws.canon_count.go(ls, 0n, a0), Con{Laws.canon_count.go(ls, 1n, a1), Con{Laws.canon_count.go(ls, 2n, a2), Con{Laws.canon_count.go(ls, 3n, a3), Con{Laws.canon_count.go(ls, 4n, a4), Con{Laws.canon_count.go(ls, 5n, a5), Con{Laws.canon_count.go(ls, 6n, a6), Con{Laws.canon_count.go(ls, 7n, a7), Con{Laws.canon_count.go(ls, 8n, a8), Con{Laws.canon_count.go(ls, 9n, a9), Con{Laws.canon_count.go(ls, 10n, a10), Con{Laws.canon_count.go(ls, 11n, a11), Con{Laws.canon_count.go(ls, 12n, a12), Con{Laws.canon_count.go(ls, 13n, a13), Con{Laws.canon_count.go(ls, 14n, a14), Con{Laws.canon_count.go(ls, 15n, a15), Nil{}}}}}}}}}}}}}}}}} : List<&2, U32>}:
  match ls:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %Equal.sym(List<&2, U32>, H.hf.inc(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Nil{}}}}}}}}}}}}}}}}}, U32.to_nat(h)), Con{Laws.canon_step(Nat.is_eq(U32.to_nat(h), 0n), a0), Con{Laws.canon_step(Nat.is_eq(U32.to_nat(h), 1n), a1), Con{Laws.canon_step(Nat.is_eq(U32.to_nat(h), 2n), a2), Con{Laws.canon_step(Nat.is_eq(U32.to_nat(h), 3n), a3), Con{Laws.canon_step(Nat.is_eq(U32.to_nat(h), 4n), a4), Con{Laws.canon_step(Nat.is_eq(U32.to_nat(h), 5n), a5), Con{Laws.canon_step(Nat.is_eq(U32.to_nat(h), 6n), a6), Con{Laws.canon_step(Nat.is_eq(U32.to_nat(h), 7n), a7), Con{Laws.canon_step(Nat.is_eq(U32.to_nat(h), 8n), a8), Con{Laws.canon_step(Nat.is_eq(U32.to_nat(h), 9n), a9), Con{Laws.canon_step(Nat.is_eq(U32.to_nat(h), 10n), a10), Con{Laws.canon_step(Nat.is_eq(U32.to_nat(h), 11n), a11), Con{Laws.canon_step(Nat.is_eq(U32.to_nat(h), 12n), a12), Con{Laws.canon_step(Nat.is_eq(U32.to_nat(h), 13n), a13), Con{Laws.canon_step(Nat.is_eq(U32.to_nat(h), 14n), a14), Con{Laws.canon_step(Nat.is_eq(U32.to_nat(h), 15n), a15), Nil{}}}}}}}}}}}}}}}}}, cn.incshape(U32.to_nat(h), a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15)) : {H.hf.counts.go(t, _) == Con{Laws.canon_count.go(t, 0n, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 0n), a0)), Con{Laws.canon_count.go(t, 1n, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 1n), a1)), Con{Laws.canon_count.go(t, 2n, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 2n), a2)), Con{Laws.canon_count.go(t, 3n, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 3n), a3)), Con{Laws.canon_count.go(t, 4n, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 4n), a4)), Con{Laws.canon_count.go(t, 5n, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 5n), a5)), Con{Laws.canon_count.go(t, 6n, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 6n), a6)), Con{Laws.canon_count.go(t, 7n, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 7n), a7)), Con{Laws.canon_count.go(t, 8n, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 8n), a8)), Con{Laws.canon_count.go(t, 9n, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 9n), a9)), Con{Laws.canon_count.go(t, 10n, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 10n), a10)), Con{Laws.canon_count.go(t, 11n, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 11n), a11)), Con{Laws.canon_count.go(t, 12n, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 12n), a12)), Con{Laws.canon_count.go(t, 13n, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 13n), a13)), Con{Laws.canon_count.go(t, 14n, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 14n), a14)), Con{Laws.canon_count.go(t, 15n, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 15n), a15)), Nil{}}}}}}}}}}}}}}}}} : List<&2, U32>}
      cn.cgo(t, Laws.canon_step(Nat.is_eq(U32.to_nat(h), 0n), a0), Laws.canon_step(Nat.is_eq(U32.to_nat(h), 1n), a1), Laws.canon_step(Nat.is_eq(U32.to_nat(h), 2n), a2), Laws.canon_step(Nat.is_eq(U32.to_nat(h), 3n), a3), Laws.canon_step(Nat.is_eq(U32.to_nat(h), 4n), a4), Laws.canon_step(Nat.is_eq(U32.to_nat(h), 5n), a5), Laws.canon_step(Nat.is_eq(U32.to_nat(h), 6n), a6), Laws.canon_step(Nat.is_eq(U32.to_nat(h), 7n), a7), Laws.canon_step(Nat.is_eq(U32.to_nat(h), 8n), a8), Laws.canon_step(Nat.is_eq(U32.to_nat(h), 9n), a9), Laws.canon_step(Nat.is_eq(U32.to_nat(h), 10n), a10), Laws.canon_step(Nat.is_eq(U32.to_nat(h), 11n), a11), Laws.canon_step(Nat.is_eq(U32.to_nat(h), 12n), a12), Laws.canon_step(Nat.is_eq(U32.to_nat(h), 13n), a13), Laws.canon_step(Nat.is_eq(U32.to_nat(h), 14n), a14), Laws.canon_step(Nat.is_eq(U32.to_nat(h), 15n), a15))

# counting by length: hf.counts is bl_count[0..15]
def cn.counts_eq(+ls: List<&2, U32>) -> {H.hf.counts(ls) == Con{Laws.canon_count(ls, 0n), Con{Laws.canon_count(ls, 1n), Con{Laws.canon_count(ls, 2n), Con{Laws.canon_count(ls, 3n), Con{Laws.canon_count(ls, 4n), Con{Laws.canon_count(ls, 5n), Con{Laws.canon_count(ls, 6n), Con{Laws.canon_count(ls, 7n), Con{Laws.canon_count(ls, 8n), Con{Laws.canon_count(ls, 9n), Con{Laws.canon_count(ls, 10n), Con{Laws.canon_count(ls, 11n), Con{Laws.canon_count(ls, 12n), Con{Laws.canon_count(ls, 13n), Con{Laws.canon_count(ls, 14n), Con{Laws.canon_count(ls, 15n), Nil{}}}}}}}}}}}}}}}}} : List<&2, U32>}:
  cn.cgo(ls, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

# next_code: the first codes of the 16 counts, entry by entry
def cn.next_cases(+ls: List<&2, U32>, +q: Nat, +hq: {Nat.is_le(1n+q, 15n) == True{} : Bool}) -> {H.hf.get(H.hf.next(Con{Laws.canon_count(ls, 0n), Con{Laws.canon_count(ls, 1n), Con{Laws.canon_count(ls, 2n), Con{Laws.canon_count(ls, 3n), Con{Laws.canon_count(ls, 4n), Con{Laws.canon_count(ls, 5n), Con{Laws.canon_count(ls, 6n), Con{Laws.canon_count(ls, 7n), Con{Laws.canon_count(ls, 8n), Con{Laws.canon_count(ls, 9n), Con{Laws.canon_count(ls, 10n), Con{Laws.canon_count(ls, 11n), Con{Laws.canon_count(ls, 12n), Con{Laws.canon_count(ls, 13n), Con{Laws.canon_count(ls, 14n), Con{Laws.canon_count(ls, 15n), Nil{}}}}}}}}}}}}}}}}}), 1n+q) == Laws.canon_next(ls, 1n+q) : U32}:
  match q:
    case 0n:
      {==}
    case 1n+ +q1:
      match q1:
        case 0n:
          {==}
        case 1n+ +q2:
          match q2:
            case 0n:
              {==}
            case 1n+ +q3:
              match q3:
                case 0n:
                  {==}
                case 1n+ +q4:
                  match q4:
                    case 0n:
                      {==}
                    case 1n+ +q5:
                      match q5:
                        case 0n:
                          {==}
                        case 1n+ +q6:
                          match q6:
                            case 0n:
                              {==}
                            case 1n+ +q7:
                              match q7:
                                case 0n:
                                  {==}
                                case 1n+ +q8:
                                  match q8:
                                    case 0n:
                                      {==}
                                    case 1n+ +q9:
                                      match q9:
                                        case 0n:
                                          {==}
                                        case 1n+ +q10:
                                          match q10:
                                            case 0n:
                                              {==}
                                            case 1n+ +q11:
                                              match q11:
                                                case 0n:
                                                  {==}
                                                case 1n+ +q12:
                                                  match q12:
                                                    case 0n:
                                                      {==}
                                                    case 1n+ +q13:
                                                      match q13:
                                                        case 0n:
                                                          {==}
                                                        case 1n+ +q14:
                                                          match q14:
                                                            case 0n:
                                                              {==}
                                                            case 1n+ +q15:
                                                              Empty.absurd({H.hf.get(H.hf.next(Con{Laws.canon_count(ls, 0n), Con{Laws.canon_count(ls, 1n), Con{Laws.canon_count(ls, 2n), Con{Laws.canon_count(ls, 3n), Con{Laws.canon_count(ls, 4n), Con{Laws.canon_count(ls, 5n), Con{Laws.canon_count(ls, 6n), Con{Laws.canon_count(ls, 7n), Con{Laws.canon_count(ls, 8n), Con{Laws.canon_count(ls, 9n), Con{Laws.canon_count(ls, 10n), Con{Laws.canon_count(ls, 11n), Con{Laws.canon_count(ls, 12n), Con{Laws.canon_count(ls, 13n), Con{Laws.canon_count(ls, 14n), Con{Laws.canon_count(ls, 15n), Nil{}}}}}}}}}}}}}}}}}), 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+q15) == Laws.canon_next(ls, 1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+1n+q15) : U32}, cn.ft(hq))

def cn.next_get(+ls: List<&2, U32>, +q: Nat, +hq: {Nat.is_le(1n+q, 15n) == True{} : Bool}) -> {H.hf.get(H.hf.next(H.hf.counts(ls)), 1n+q) == Laws.canon_next(ls, 1n+q) : U32}:
  %Equal.sym(List<&2, U32>, H.hf.counts(ls), Con{Laws.canon_count(ls, 0n), Con{Laws.canon_count(ls, 1n), Con{Laws.canon_count(ls, 2n), Con{Laws.canon_count(ls, 3n), Con{Laws.canon_count(ls, 4n), Con{Laws.canon_count(ls, 5n), Con{Laws.canon_count(ls, 6n), Con{Laws.canon_count(ls, 7n), Con{Laws.canon_count(ls, 8n), Con{Laws.canon_count(ls, 9n), Con{Laws.canon_count(ls, 10n), Con{Laws.canon_count(ls, 11n), Con{Laws.canon_count(ls, 12n), Con{Laws.canon_count(ls, 13n), Con{Laws.canon_count(ls, 14n), Con{Laws.canon_count(ls, 15n), Nil{}}}}}}}}}}}}}}}}}, cn.counts_eq(ls)) : {H.hf.get(H.hf.next(_), 1n+q) == Laws.canon_next(ls, 1n+q) : U32}
  cn.next_cases(ls, q, hq)

def cn.next_len(+ls: List<&2, U32>) -> {List.length(&2, U32, H.hf.next(H.hf.counts(ls))) == 16n : Nat}:
  %Equal.sym(List<&2, U32>, H.hf.counts(ls), Con{Laws.canon_count(ls, 0n), Con{Laws.canon_count(ls, 1n), Con{Laws.canon_count(ls, 2n), Con{Laws.canon_count(ls, 3n), Con{Laws.canon_count(ls, 4n), Con{Laws.canon_count(ls, 5n), Con{Laws.canon_count(ls, 6n), Con{Laws.canon_count(ls, 7n), Con{Laws.canon_count(ls, 8n), Con{Laws.canon_count(ls, 9n), Con{Laws.canon_count(ls, 10n), Con{Laws.canon_count(ls, 11n), Con{Laws.canon_count(ls, 12n), Con{Laws.canon_count(ls, 13n), Con{Laws.canon_count(ls, 14n), Con{Laws.canon_count(ls, 15n), Nil{}}}}}}}}}}}}}}}}}, cn.counts_eq(ls)) : {List.length(&2, U32, H.hf.next(_)) == 16n : Nat}
  {==}
# END GENERATED by gen/canon.py

def cn.hlen0(+ls: List<&2, U32>, +L: Nat, +hl: {Nat.is_le(L, 15n) == True{} : Bool}) -> {Nat.is_lt(L, List.length(&2, U32, cn.accn(H.DflHufAcc{H.hf.next(H.hf.counts(ls)), H.DflHNil{}}))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, U32, H.hf.next(H.hf.counts(ls))), 16n, cn.next_len(ls)) : {Nat.is_lt(L, _) == True{} : Bool}
  cn.le_lt_succ(L, 15n, hl)

# The law

def cn.code_path(+t: H.DflTree, +s: U32, +p: List<&2, Bool>, +h: {H.hf.code.of(t, s) == Some{p} : Maybe<&2, List<&2, Bool>>}) -> {H.huff_path(t, s) == Some{p} : Maybe<&2, List<&2, Bool>>}:
  match t:
    case H.DflHNode{z, o}:
      h
    case H.DflHNil{}:
      Empty.absurd({H.huff_path(H.DflHNil{}, s) == Some{p} : Maybe<&2, List<&2, Bool>>}, cn.ns(p, h))
    case H.DflHLeaf{x}:
      Empty.absurd({H.huff_path(H.DflHLeaf{x}, s) == Some{p} : Maybe<&2, List<&2, Bool>>}, cn.ns(p, h))

def cn.hb0(+ls: List<&2, U32>, +c: U32, +hc: {Nat.is_le(List.length(&2, U32, ls), U32.to_nat(c)) == True{} : Bool}) -> {Nat.is_le(Nat.add(List.length(&2, U32, ls), 0n), U32.to_nat(c)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(List.length(&2, U32, ls), 0n), List.length(&2, U32, ls), UL.nat_add_zero(List.length(&2, U32, ls))) : {Nat.is_le(_, U32.to_nat(c)) == True{} : Bool}
  hc

def cn.final(+L: Nat, +ls: List<&2, U32>, +i: Nat, +p: List<&2, Bool>, +hl: {Nat.is_le(L, 15n) == True{} : Bool}, r: cn.atty(L, p, Laws.canon_count.go(List.take(&2, U32, ls, i), L, H.hf.get(H.hf.next(H.hf.counts(ls)), L)))) -> {Laws.canon_code.of(L, ls, i) == Some{p} : Maybe<&2, List<&2, Bool>>}:
  match L:
    case 0n:
      Empty.absurd({Laws.canon_code.of(0n, ls, i) == Some{p} : Maybe<&2, List<&2, Bool>>}, r)
    case 1n+ +q:
      %cn.next_get(ls, q, hl) : {Some{Laws.canon_bits(1n+q, Laws.canon_count.go(List.take(&2, U32, ls, i), 1n+q, _))} == Some{p} : Maybe<&2, List<&2, Bool>>}
      r

def Laws.huff_code_canonical(ls, s, p, c, hc, hl, h):
  +i = U32.to_nat(s)
  +a0 = {H.DflHufAcc{H.hf.next(H.hf.counts(ls)), H.DflHNil{}} : H.DflHufAcc}
  +L = U32.to_nat(Laws.canon_len(ls, i))
  +es = Equal.sym(Nat, Nat.add(i, 0n), i, UL.nat_add_zero(i))
  cn.final(L, ls, i, p, hl, cn.at(ls, i, 0, 0n, {==}, a0, s, es, c, cn.hb0(ls, c, hc), {==}, L, {==}, cn.hlen0(ls, L, hl), p, cn.code_path(H.huff_tree(ls), s, p, h)))
