import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tree.bend as T
import ./props.bend as P
import ./path.bend as Pa
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../word64/LAWS.bend as WL
import ../word64/PROOF.bend as WP
import ./PROOF.bend as FP
import ./LAWS_lookup.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP

# Lemmas are mostly stated as {value == expression}, the direction a rewrite
# needs: %e : P replaces the expression (marked _ in P) by the value.

# Booleans and words

def or_false_l(+a: Bool, +b: Bool, +e: {Bool.or(a, b) == False{} : Bool}) -> {False{} == a : Bool}:
  match a:
    case True{}:
      Empty.absurd({False{} == True{} : Bool}, FP.tf_absurd(e))
    case False{}:
      {==}

def or_false_r(+a: Bool, +b: Bool, +e: {Bool.or(a, b) == False{} : Bool}) -> {False{} == b : Bool}:
  match a:
    case True{}:
      Empty.absurd({False{} == b : Bool}, FP.tf_absurd(e))
    case False{}:
      Equal.sym(Bool, b, False{}, e)

# <u32> values read back (as fdt's own u32_round_trip, through bytes' laws)

def u32rt(+v: U32) -> {Done{v} == P.FdtProp.u32(P.FdtProp.of_u32(v)) : Result<&2, &2, E.FdtError, U32>}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.be32(v)), B.len(B.Octets.to_list(B.Octets.be32(v))), BL.octets_len_list(B.Octets.be32(v))) : {Done{v} == P.pr.u32.pick(Nat.is_eq(_, 4n), B.Octets.be32(v)) : Result<&2, &2, E.FdtError, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.be32(v))), B.mask(B.be32(v)), BL.octets_to_of(B.be32(v))) : {Done{v} == P.pr.u32.pick(Nat.is_eq(B.len(_), 4n), B.Octets.be32(v)) : Result<&2, &2, E.FdtError, U32>}
  %FP.len4(v) : {Done{v} == P.pr.u32.pick(_, B.Octets.be32(v)) : Result<&2, &2, E.FdtError, U32>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.be32(v), 0n), Some{v}, BL.octets_be32_round_trip(v)) : {Done{v} == P.pr.must32(_) : Result<&2, &2, E.FdtError, U32>}
  {==}

# Phandles: the search is the specification's, one node at a time

def ph_res(+r: Result<&2, &2, E.FdtError, U32>, +ph: U32) -> {Pa.lk.ph.res(r, ph) == Laws.fdtlaw.is_u32.r(r, ph) : Bool}:
  match r:
    case Done{x}:
      {==}
    case Fail{e}:
      {==}

def ph_is(+m: Maybe<&2, B.Octets>, +ph: U32) -> {Pa.lk.ph.is(m, ph) == Laws.fdtlaw.is_u32(m, ph) : Bool}:
  match m:
    case Some{v}:
      ph_res(P.FdtProp.u32(v), ph)
    case None{}:
      {==}

def ph_has(+nm: B.Octets, +ps: List<&2, T.FdtProp>, +cs: List<&2, T.FdtNode>, +ph: U32) -> {Pa.lk.ph.match(ps, ph) == Laws.fdtlaw.has_phandle(T.FdtNode{nm, ps, cs}, ph) : Bool}:
  %ph_is(Pa.lk.prop(ps, B.Octets.of_string("phandle")), ph) : {Pa.lk.ph.match(ps, ph) == Bool.or(_, Laws.fdtlaw.is_u32(Pa.lk.prop(ps, B.Octets.of_string("linux,phandle")), ph)) : Bool}
  %ph_is(Pa.lk.prop(ps, B.Octets.of_string("linux,phandle")), ph) : {Pa.lk.ph.match(ps, ph) == Bool.or(Pa.lk.ph.is(Pa.lk.prop(ps, B.Octets.of_string("phandle")), ph), _) : Bool}
  {==}

def or_pick(+h: Bool, +n: T.FdtNode, +x: Maybe<&2, T.FdtNode>, +y: Maybe<&2, T.FdtNode>) -> {Pa.lk.or(Laws.fdtlaw.first.pick(h, n, x), y) == Laws.fdtlaw.first.pick(h, n, Pa.lk.or(x, y)) : Maybe<&2, T.FdtNode>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def pick_or(+h: Bool, +n: T.FdtNode, +x: Maybe<&2, T.FdtNode>, +y: Maybe<&2, T.FdtNode>) -> {Laws.fdtlaw.first.pick(h, n, Pa.lk.or(x, y)) == Pa.lk.ph.pick(h, n, x, y) : Maybe<&2, T.FdtNode>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

# the first match in two lists one after the other
def first_app(+a: List<&2, T.FdtNode>, +b: List<&2, T.FdtNode>, +ph: U32) -> {Pa.lk.or(Laws.fdtlaw.first_phandle(a, ph), Laws.fdtlaw.first_phandle(b, ph)) == Laws.fdtlaw.first_phandle(List.append(&2, T.FdtNode, a, b), ph) : Maybe<&2, T.FdtNode>}:
  match a:
    case Nil{}:
      {==}
    case Con{+n, t}:
      %first_app(t, b, ph) : {Pa.lk.or(Laws.fdtlaw.first.pick(Laws.fdtlaw.has_phandle(n, ph), n, Laws.fdtlaw.first_phandle(t, ph)), Laws.fdtlaw.first_phandle(b, ph)) == Laws.fdtlaw.first.pick(Laws.fdtlaw.has_phandle(n, ph), n, _) : Maybe<&2, T.FdtNode>}
      or_pick(Laws.fdtlaw.has_phandle(n, ph), n, Laws.fdtlaw.first_phandle(t, ph), Laws.fdtlaw.first_phandle(b, ph))

def ph_go(+ns: List<&2, T.FdtNode>, +ph: U32) -> {Laws.fdtlaw.first_phandle(Laws.fdtlaw.nodes(ns), ph) == Pa.lk.ph.go(ns, ph) : Maybe<&2, T.FdtNode>}:
  match ns:
    case Nil{}:
      {==}
    case Con{n, t}:
      match n:
        case T.FdtNode{+nm, +ps, +cs}:
          %first_app(Laws.fdtlaw.nodes(cs), Laws.fdtlaw.nodes(t), ph) : {Laws.fdtlaw.first.pick(Laws.fdtlaw.has_phandle(T.FdtNode{nm, ps, cs}, ph), T.FdtNode{nm, ps, cs}, _) == Pa.lk.ph.go(Con{T.FdtNode{nm, ps, cs}, t}, ph) : Maybe<&2, T.FdtNode>}
          %ph_go(cs, ph) : {Laws.fdtlaw.first.pick(Laws.fdtlaw.has_phandle(T.FdtNode{nm, ps, cs}, ph), T.FdtNode{nm, ps, cs}, Pa.lk.or(Laws.fdtlaw.first_phandle(Laws.fdtlaw.nodes(cs), ph), Laws.fdtlaw.first_phandle(Laws.fdtlaw.nodes(t), ph))) == Pa.lk.ph.pick(Pa.lk.ph.match(ps, ph), T.FdtNode{nm, ps, cs}, _, Pa.lk.ph.go(t, ph)) : Maybe<&2, T.FdtNode>}
          %ph_go(t, ph) : {Laws.fdtlaw.first.pick(Laws.fdtlaw.has_phandle(T.FdtNode{nm, ps, cs}, ph), T.FdtNode{nm, ps, cs}, Pa.lk.or(Laws.fdtlaw.first_phandle(Laws.fdtlaw.nodes(cs), ph), Laws.fdtlaw.first_phandle(Laws.fdtlaw.nodes(t), ph))) == Pa.lk.ph.pick(Pa.lk.ph.match(ps, ph), T.FdtNode{nm, ps, cs}, Laws.fdtlaw.first_phandle(Laws.fdtlaw.nodes(cs), ph), _) : Maybe<&2, T.FdtNode>}
          %ph_has(nm, ps, cs, ph) : {Laws.fdtlaw.first.pick(_, T.FdtNode{nm, ps, cs}, Pa.lk.or(Laws.fdtlaw.first_phandle(Laws.fdtlaw.nodes(cs), ph), Laws.fdtlaw.first_phandle(Laws.fdtlaw.nodes(t), ph))) == Pa.lk.ph.pick(Pa.lk.ph.match(ps, ph), T.FdtNode{nm, ps, cs}, Laws.fdtlaw.first_phandle(Laws.fdtlaw.nodes(cs), ph), Laws.fdtlaw.first_phandle(Laws.fdtlaw.nodes(t), ph)) : Maybe<&2, T.FdtNode>}
          pick_or(Pa.lk.ph.match(ps, ph), T.FdtNode{nm, ps, cs}, Laws.fdtlaw.first_phandle(Laws.fdtlaw.nodes(cs), ph), Laws.fdtlaw.first_phandle(Laws.fdtlaw.nodes(t), ph))

def first_none(+ns: List<&2, T.FdtNode>, +ph: U32, +e: {Laws.fdtlaw.any_phandle(ns, ph) == False{} : Bool}) -> {Laws.fdtlaw.first_phandle(ns, ph) == None{} : Maybe<&2, T.FdtNode>}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, t}:
      %or_false_l(Laws.fdtlaw.has_phandle(n, ph), Laws.fdtlaw.any_phandle(t, ph), e) : {Laws.fdtlaw.first.pick(_, n, Laws.fdtlaw.first_phandle(t, ph)) == None{} : Maybe<&2, T.FdtNode>}
      first_none(t, ph, Equal.sym(Bool, False{}, Laws.fdtlaw.any_phandle(t, ph), or_false_r(Laws.fdtlaw.has_phandle(n, ph), Laws.fdtlaw.any_phandle(t, ph), e)))

def Laws.find_phandle_first(root, ph):
  Equal.sym(Maybe<&2, T.FdtNode>, Laws.fdtlaw.first_phandle(Laws.fdtlaw.nodes([root]), ph), Pa.lk.ph.go([root], ph), ph_go([root], ph))

def Laws.find_phandle_none(root, ph, e):
  %ph_go([root], ph) : {_ == None{} : Maybe<&2, T.FdtNode>}
  first_none(Laws.fdtlaw.nodes([root]), ph, e)

def Laws.find_phandle_head(nm, ph, ps, cs):
  %u32rt(ph) : {Pa.lk.ph.pick(Bool.or(Pa.lk.ph.res(_, ph), Pa.lk.ph.is(Pa.lk.prop(Con{T.FdtProp{B.Octets.of_string("phandle"), P.FdtProp.of_u32(ph)}, ps}, B.Octets.of_string("linux,phandle")), ph)), T.FdtNode{nm, Con{T.FdtProp{B.Octets.of_string("phandle"), P.FdtProp.of_u32(ph)}, ps}, cs}, Pa.lk.ph.go(cs, ph), None{}) == Some{T.FdtNode{nm, Con{T.FdtProp{B.Octets.of_string("phandle"), P.FdtProp.of_u32(ph)}, ps}, cs}} : Maybe<&2, T.FdtNode>}
  %FP.irefl(ph) : {Pa.lk.ph.pick(Bool.or(_, Pa.lk.ph.is(Pa.lk.prop(Con{T.FdtProp{B.Octets.of_string("phandle"), P.FdtProp.of_u32(ph)}, ps}, B.Octets.of_string("linux,phandle")), ph)), T.FdtNode{nm, Con{T.FdtProp{B.Octets.of_string("phandle"), P.FdtProp.of_u32(ph)}, ps}, cs}, Pa.lk.ph.go(cs, ph), None{}) == Some{T.FdtNode{nm, Con{T.FdtProp{B.Octets.of_string("phandle"), P.FdtProp.of_u32(ph)}, ps}, cs}} : Maybe<&2, T.FdtNode>}
  {==}

def Laws.find_phandle_none_example():
  {==}

# cells read back as written (with PROOF.bend's lemmas, FP)

def cells_rt0(+cs: List<&2, U32>) -> {P.FdtProp.cells(P.FdtProp.of_cells(cs)) == Done{cs} : Result<&2, &2, E.FdtError, List<&2, U32>>}:
  %FP.cells_fast(cs) : {P.pr.cells.go(B.Octets.to_list(B.Octets.of_list(_)), Nil{}) == Done{cs} : Result<&2, &2, E.FdtError, List<&2, U32>>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(P.pr.cells.list(cs))), B.mask(P.pr.cells.list(cs)), BL.octets_to_of(P.pr.cells.list(cs))) : {P.pr.cells.go(_, Nil{}) == Done{cs} : Result<&2, &2, E.FdtError, List<&2, U32>>}
  %FP.mask_cl(cs) : {P.pr.cells.go(_, Nil{}) == Done{cs} : Result<&2, &2, E.FdtError, List<&2, U32>>}
  %FP.cells_rt(cs, Nil{}) : {_ == Done{cs} : Result<&2, &2, E.FdtError, List<&2, U32>>}
  %FP.revrev(U32, cs) : {Done{_} == Done{cs} : Result<&2, &2, E.FdtError, List<&2, U32>>}
  {==}

# More lists

def gapp_assoc(-A: Data, +a: List<&2, A>, +b: List<&2, A>, +c: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, a, b), c) == List.append(&2, A, a, List.append(&2, A, b, c)) : List<&2, A>}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %gapp_assoc(A, t, b, c) : {Con{h, List.append(&2, A, List.append(&2, A, t, b), c)} == Con{h, _} : List<&2, A>}
      {==}

def rev_acc.go(-A: Data, +l: List<&2, A>, +m: List<&2, A>, +acc: List<&2, A>) -> {List.append(&2, A, List.reverse.go(&2, A, l, m), acc) == List.reverse.go(&2, A, l, List.append(&2, A, m, acc)) : List<&2, A>}:
  match l:
    case Nil{}:
      {==}
    case Con{h, t}:
      rev_acc.go(A, t, Con{h, m}, acc)

# reversing onto acc is reversing, then acc after it
def rev_acc(-A: Data, +l: List<&2, A>, +acc: List<&2, A>) -> {List.append(&2, A, List.reverse.go(&2, A, l, Nil{}), acc) == List.reverse.go(&2, A, l, acc) : List<&2, A>}:
  rev_acc.go(A, l, Nil{}, acc)

def and_false_r(+x: Bool) -> {False{} == Bool.and(x, False{}) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def npred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def succ_inj(+a: Nat, +b: Nat, +e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, x => npred(x), 1n+a, 1n+b, e)

def nrefl(+n: Nat) -> {True{} == Nat.is_eq(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nrefl(p)

def neq(+n: Nat, +b: Nat) -> {False{} == Nat.is_eq(n, 1n+Nat.add(b, n)) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %FP.add_succ_r(b, p) : {False{} == Nat.is_eq(p, _) : Bool}
      neq(p, b)

# Children: the specification's searches are the code's

def sp.or_eq(+a: Maybe<&2, T.FdtNode>, +b: Maybe<&2, T.FdtNode>) -> {Laws.fdtlaw.or(a, b) == Pa.lk.or(a, b) : Maybe<&2, T.FdtNode>}:
  match a:
    case Some{n}:
      {==}
    case None{}:
      {==}

def sp.pick_eq(+h: Bool, +n: T.FdtNode, +r: Maybe<&2, T.FdtNode>) -> {Laws.fdtlaw.first.pick(h, n, r) == Pa.lk.child.pick(h, n, r) : Maybe<&2, T.FdtNode>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def sp.named(+cs: List<&2, T.FdtNode>, +k: B.Octets) -> {Laws.fdtlaw.named(cs, k) == Pa.lk.child.exact(cs, k) : Maybe<&2, T.FdtNode>}:
  match cs:
    case Nil{}:
      {==}
    case Con{n, t}:
      match n:
        case T.FdtNode{+nm, +ps, +cs2}:
          %sp.named(t, k) : {Laws.fdtlaw.first.pick(B.Octets.is_eq(nm, k), T.FdtNode{nm, ps, cs2}, Laws.fdtlaw.named(t, k)) == Pa.lk.child.pick(B.Octets.is_eq(nm, k), T.FdtNode{nm, ps, cs2}, _) : Maybe<&2, T.FdtNode>}
          sp.pick_eq(B.Octets.is_eq(nm, k), T.FdtNode{nm, ps, cs2}, Laws.fdtlaw.named(t, k))

def sp.bpick(+at: Bool, +h: U32, +rest: List<&2, U32>) -> {Laws.fdtlaw.base.pick(at, h, rest) == Pa.lk.base.pick(at, h, rest) : List<&2, U32>}:
  match at:
    case True{}:
      {==}
    case False{}:
      {==}

def sp.base(+xs: List<&2, U32>) -> {Laws.fdtlaw.base(xs) == Pa.lk.base(xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %sp.base(t) : {Laws.fdtlaw.base.pick(U32.is_eq(h, 64), h, Laws.fdtlaw.base(t)) == Pa.lk.base.pick(U32.is_eq(h, 64), h, _) : List<&2, U32>}
      sp.bpick(U32.is_eq(h, 64), h, Laws.fdtlaw.base(t))

def sp.hasat(+xs: List<&2, U32>) -> {Laws.fdtlaw.has_at(xs) == Pa.lk.has_at(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %sp.hasat(t) : {Bool.or(U32.is_eq(h, 64), Laws.fdtlaw.has_at(t)) == Bool.or(U32.is_eq(h, 64), _) : Bool}
      {==}

def sp.based(+cs: List<&2, T.FdtNode>, +k: B.Octets) -> {Laws.fdtlaw.based(cs, k) == Pa.lk.child.base(cs, k) : Maybe<&2, T.FdtNode>}:
  match cs:
    case Nil{}:
      {==}
    case Con{n, t}:
      match n:
        case T.FdtNode{+nm, +ps, +cs2}:
          %sp.based(t, k) : {Laws.fdtlaw.first.pick(B.Octets.is_eq(B.Octets.of_list(Laws.fdtlaw.base(B.Octets.to_list(nm))), k), T.FdtNode{nm, ps, cs2}, Laws.fdtlaw.based(t, k)) == Pa.lk.child.pick(B.Octets.is_eq(B.Octets.of_list(Pa.lk.base(B.Octets.to_list(nm))), k), T.FdtNode{nm, ps, cs2}, _) : Maybe<&2, T.FdtNode>}
          %sp.base(B.Octets.to_list(nm)) : {Laws.fdtlaw.first.pick(B.Octets.is_eq(B.Octets.of_list(Laws.fdtlaw.base(B.Octets.to_list(nm))), k), T.FdtNode{nm, ps, cs2}, Laws.fdtlaw.based(t, k)) == Pa.lk.child.pick(B.Octets.is_eq(B.Octets.of_list(_), k), T.FdtNode{nm, ps, cs2}, Laws.fdtlaw.based(t, k)) : Maybe<&2, T.FdtNode>}
          sp.pick_eq(B.Octets.is_eq(B.Octets.of_list(Laws.fdtlaw.base(B.Octets.to_list(nm))), k), T.FdtNode{nm, ps, cs2}, Laws.fdtlaw.based(t, k))

def sp.bif(+has: Bool, +cs: List<&2, T.FdtNode>, +k: B.Octets) -> {Laws.fdtlaw.based_if(has, cs, k) == Pa.lk.child.base_if(has, cs, k) : Maybe<&2, T.FdtNode>}:
  match has:
    case True{}:
      {==}
    case False{}:
      sp.based(cs, k)

def Laws.child_rule(nm, ps, cs, k):
  %sp.named(cs, k) : {Pa.lk.or(_, Pa.lk.child.base_if(Pa.lk.has_at(B.Octets.to_list(k)), cs, k)) == Laws.fdtlaw.or(Laws.fdtlaw.named(cs, k), Laws.fdtlaw.based_if(Laws.fdtlaw.has_at(B.Octets.to_list(k)), cs, k)) : Maybe<&2, T.FdtNode>}
  %sp.hasat(B.Octets.to_list(k)) : {Pa.lk.or(Laws.fdtlaw.named(cs, k), Pa.lk.child.base_if(_, cs, k)) == Laws.fdtlaw.or(Laws.fdtlaw.named(cs, k), Laws.fdtlaw.based_if(Laws.fdtlaw.has_at(B.Octets.to_list(k)), cs, k)) : Maybe<&2, T.FdtNode>}
  %sp.bif(Laws.fdtlaw.has_at(B.Octets.to_list(k)), cs, k) : {Pa.lk.or(Laws.fdtlaw.named(cs, k), _) == Laws.fdtlaw.or(Laws.fdtlaw.named(cs, k), Laws.fdtlaw.based_if(Laws.fdtlaw.has_at(B.Octets.to_list(k)), cs, k)) : Maybe<&2, T.FdtNode>}
  Equal.sym(Maybe<&2, T.FdtNode>, Laws.fdtlaw.or(Laws.fdtlaw.named(cs, k), Laws.fdtlaw.based_if(Laws.fdtlaw.has_at(B.Octets.to_list(k)), cs, k)), Pa.lk.or(Laws.fdtlaw.named(cs, k), Laws.fdtlaw.based_if(Laws.fdtlaw.has_at(B.Octets.to_list(k)), cs, k)), sp.or_eq(Laws.fdtlaw.named(cs, k), Laws.fdtlaw.based_if(Laws.fdtlaw.has_at(B.Octets.to_list(k)), cs, k)))

# Paths: the code splits a path with an accumulator (the component being
# read, reversed, and the components so far, reversed); the specification
# splits it structurally. sp.K is what is left to emit: the pieces of the
# rest of the path, the first one after rc.

def sp.K(rc: List<&2, U32>, p: Laws.FdtPathParts) -> List<&2, List<&2, U32>>:
  match p:
    case Laws.FdtPathParts{f, r}:
      Laws.fdtlaw.nonempty(Con{B.append(rc, f), r})

# a reversed non-empty component is non-empty
def sp.ne_rev(+t: List<&2, U32>, +h: U32, +acc: List<&2, U32>, +r: List<&2, List<&2, U32>>) -> {Con{List.reverse.go(&2, U32, t, Con{h, acc}), Laws.fdtlaw.nonempty(r)} == Laws.fdtlaw.nonempty(Con{List.reverse.go(&2, U32, t, Con{h, acc}), r}) : List<&2, List<&2, U32>>}:
  match t:
    case Nil{}:
      {==}
    case Con{y, t2}:
      sp.ne_rev(t2, y, Con{h, acc}, r)

# a '/': the component read so far is emitted (if not empty)
def sp.slash(+cur: List<&2, U32>, +comps: List<&2, List<&2, U32>>, +h: U32, +p: Laws.FdtPathParts) -> {List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, Pa.lk.push(cur, comps)), sp.K(Nil{}, p)) == List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, comps), sp.K(List.reverse(&2, U32, cur), Laws.fdtlaw.parts.byte(True{}, h, p))) : List<&2, List<&2, U32>>}:
  match cur:
    case Nil{}:
      match p:
        case Laws.FdtPathParts{f, r}:
          {==}
    case Con{h2, t2}:
      match p:
        case Laws.FdtPathParts{+f, +r}:
          %FP.gapp_nil(U32, List.reverse.go(&2, U32, t2, Con{h2, Nil{}})) : {List.append(&2, List<&2, U32>, List.reverse.go(&2, List<&2, U32>, comps, Con{List.reverse.go(&2, U32, t2, Con{h2, Nil{}}), Nil{}}), Laws.fdtlaw.nonempty(Con{f, r})) == List.append(&2, List<&2, U32>, List.reverse.go(&2, List<&2, U32>, comps, Nil{}), Laws.fdtlaw.nonempty(Con{_, Con{f, r}})) : List<&2, List<&2, U32>>}
          %sp.ne_rev(t2, h2, Nil{}, Con{f, r}) : {List.append(&2, List<&2, U32>, List.reverse.go(&2, List<&2, U32>, comps, Con{List.reverse.go(&2, U32, t2, Con{h2, Nil{}}), Nil{}}), Laws.fdtlaw.nonempty(Con{f, r})) == List.append(&2, List<&2, U32>, List.reverse.go(&2, List<&2, U32>, comps, Nil{}), _) : List<&2, List<&2, U32>>}
          %rev_acc(List<&2, U32>, comps, Con{List.reverse.go(&2, U32, t2, Con{h2, Nil{}}), Nil{}}) : {List.append(&2, List<&2, U32>, _, Laws.fdtlaw.nonempty(Con{f, r})) == List.append(&2, List<&2, U32>, List.reverse.go(&2, List<&2, U32>, comps, Nil{}), Con{List.reverse.go(&2, U32, t2, Con{h2, Nil{}}), Laws.fdtlaw.nonempty(Con{f, r})}) : List<&2, List<&2, U32>>}
          gapp_assoc(List<&2, U32>, List.reverse.go(&2, List<&2, U32>, comps, Nil{}), Con{List.reverse.go(&2, U32, t2, Con{h2, Nil{}}), Nil{}}, Laws.fdtlaw.nonempty(Con{f, r}))

# any other byte: it joins the component being read
def sp.byte(+cur: List<&2, U32>, +comps: List<&2, List<&2, U32>>, +h: U32, +p: Laws.FdtPathParts) -> {List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, comps), sp.K(List.reverse(&2, U32, Con{h, cur}), p)) == List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, comps), sp.K(List.reverse(&2, U32, cur), Laws.fdtlaw.parts.byte(False{}, h, p))) : List<&2, List<&2, U32>>}:
  match p:
    case Laws.FdtPathParts{+f, +r}:
      %rev_acc(U32, cur, Con{h, Nil{}}) : {List.append(&2, List<&2, U32>, List.reverse.go(&2, List<&2, U32>, comps, Nil{}), Laws.fdtlaw.nonempty(Con{B.append(_, f), r})) == List.append(&2, List<&2, U32>, List.reverse.go(&2, List<&2, U32>, comps, Nil{}), Laws.fdtlaw.nonempty(Con{B.append(List.reverse.go(&2, U32, cur, Nil{}), Con{h, f}), r})) : List<&2, List<&2, U32>>}
      %gapp_assoc(U32, List.reverse.go(&2, U32, cur, Nil{}), Con{h, Nil{}}, f) : {List.append(&2, List<&2, U32>, List.reverse.go(&2, List<&2, U32>, comps, Nil{}), Laws.fdtlaw.nonempty(Con{B.append(B.append(List.reverse.go(&2, U32, cur, Nil{}), Con{h, Nil{}}), f), r})) == List.append(&2, List<&2, U32>, List.reverse.go(&2, List<&2, U32>, comps, Nil{}), Laws.fdtlaw.nonempty(Con{_, r})) : List<&2, List<&2, U32>>}
      {==}

def sp.Sb(+b: Bool, +h: U32, +t: List<&2, U32>, +cur: List<&2, U32>, +comps: List<&2, List<&2, U32>>, +ih1: {Pa.lk.split.go(t, Pa.FdtPathAcc{Nil{}, Pa.lk.push(cur, comps)}) == List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, Pa.lk.push(cur, comps)), sp.K(List.reverse(&2, U32, Nil{}), Laws.fdtlaw.parts(t))) : List<&2, List<&2, U32>>}, +ih2: {Pa.lk.split.go(t, Pa.FdtPathAcc{Con{h, cur}, comps}) == List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, comps), sp.K(List.reverse(&2, U32, Con{h, cur}), Laws.fdtlaw.parts(t))) : List<&2, List<&2, U32>>}) -> {Pa.lk.split.go(t, Pa.lk.split.byte(b, h, cur, comps)) == List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, comps), sp.K(List.reverse(&2, U32, cur), Laws.fdtlaw.parts.byte(b, h, Laws.fdtlaw.parts(t)))) : List<&2, List<&2, U32>>}:
  match b:
    case True{}:
      Equal.trans(List<&2, List<&2, U32>>, Pa.lk.split.go(t, Pa.FdtPathAcc{Nil{}, Pa.lk.push(cur, comps)}), List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, Pa.lk.push(cur, comps)), sp.K(Nil{}, Laws.fdtlaw.parts(t))), List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, comps), sp.K(List.reverse(&2, U32, cur), Laws.fdtlaw.parts.byte(True{}, h, Laws.fdtlaw.parts(t)))), ih1, sp.slash(cur, comps, h, Laws.fdtlaw.parts(t)))
    case False{}:
      Equal.trans(List<&2, List<&2, U32>>, Pa.lk.split.go(t, Pa.FdtPathAcc{Con{h, cur}, comps}), List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, comps), sp.K(List.reverse(&2, U32, Con{h, cur}), Laws.fdtlaw.parts(t))), List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, comps), sp.K(List.reverse(&2, U32, cur), Laws.fdtlaw.parts.byte(False{}, h, Laws.fdtlaw.parts(t)))), ih2, sp.byte(cur, comps, h, Laws.fdtlaw.parts(t)))

def sp.S(+xs: List<&2, U32>, +cur: List<&2, U32>, +comps: List<&2, List<&2, U32>>) -> {Pa.lk.split.go(xs, Pa.FdtPathAcc{cur, comps}) == List.append(&2, List<&2, U32>, List.reverse(&2, List<&2, U32>, comps), sp.K(List.reverse(&2, U32, cur), Laws.fdtlaw.parts(xs))) : List<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      match cur:
        case Nil{}:
          FP.gapp_nil(List<&2, U32>, List.reverse.go(&2, List<&2, U32>, comps, Nil{}))
        case Con{h, t}:
          %FP.gapp_nil(U32, List.reverse.go(&2, U32, t, Con{h, Nil{}})) : {List.reverse.go(&2, List<&2, U32>, comps, Con{List.reverse.go(&2, U32, t, Con{h, Nil{}}), Nil{}}) == List.append(&2, List<&2, U32>, List.reverse.go(&2, List<&2, U32>, comps, Nil{}), Laws.fdtlaw.nonempty(Con{_, Nil{}})) : List<&2, List<&2, U32>>}
          %sp.ne_rev(t, h, Nil{}, Nil{}) : {List.reverse.go(&2, List<&2, U32>, comps, Con{List.reverse.go(&2, U32, t, Con{h, Nil{}}), Nil{}}) == List.append(&2, List<&2, U32>, List.reverse.go(&2, List<&2, U32>, comps, Nil{}), _) : List<&2, List<&2, U32>>}
          Equal.sym(List<&2, List<&2, U32>>, List.append(&2, List<&2, U32>, List.reverse.go(&2, List<&2, U32>, comps, Nil{}), Con{List.reverse.go(&2, U32, t, Con{h, Nil{}}), Nil{}}), List.reverse.go(&2, List<&2, U32>, comps, Con{List.reverse.go(&2, U32, t, Con{h, Nil{}}), Nil{}}), rev_acc(List<&2, U32>, comps, Con{List.reverse.go(&2, U32, t, Con{h, Nil{}}), Nil{}}))
    case Con{+h, t}:
      sp.Sb(U32.is_eq(h, 47), h, t, cur, comps, sp.S(t, Nil{}, Pa.lk.push(cur, comps)), sp.S(t, Con{h, cur}, comps))

def sp.kc(+p: Laws.FdtPathParts) -> {Laws.fdtlaw.components.of(p) == sp.K(Nil{}, p) : List<&2, List<&2, U32>>}:
  match p:
    case Laws.FdtPathParts{f, r}:
      {==}

# the specification's components are the code's, for every path
def sp.comp(+xs: List<&2, U32>) -> {Laws.fdtlaw.components(xs) == Pa.lk.components(xs) : List<&2, List<&2, U32>>}:
  Equal.trans(List<&2, List<&2, U32>>, Laws.fdtlaw.components(xs), sp.K(Nil{}, Laws.fdtlaw.parts(xs)), Pa.lk.components(xs), sp.kc(Laws.fdtlaw.parts(xs)), Equal.sym(List<&2, List<&2, U32>>, Pa.lk.components(xs), sp.K(Nil{}, Laws.fdtlaw.parts(xs)), sp.S(xs, Nil{}, Nil{})))

def sp.walk(+cs: List<&2, List<&2, U32>>, +m: Maybe<&2, T.FdtNode>) -> {Laws.fdtlaw.walk(cs, m) == Pa.lk.walk(cs, m) : Maybe<&2, T.FdtNode>}:
  match cs:
    case Nil{}:
      match m:
        case Some{n}:
          {==}
        case None{}:
          {==}
    case Con{c, t}:
      match m:
        case Some{n}:
          sp.walk(t, Pa.FdtNode.child(n, B.Octets.of_list(c)))
        case None{}:
          {==}

def sp.abs(+xs: List<&2, U32>) -> {Laws.fdtlaw.absolute(xs) == Pa.lk.is_abs(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def sp.astr(+r: Result<&2, &2, E.FdtError, B.Octets>, +rest: List<&2, List<&2, U32>>, +root: T.FdtNode) -> {Laws.fdtlaw.resolve(Laws.fdtlaw.alias.str(r), rest, root) == Pa.lk.alias.str(r, rest, root) : Maybe<&2, T.FdtNode>}:
  match r:
    case Done{+s}:
      %sp.comp(B.Octets.to_list(s)) : {Laws.fdtlaw.walk(List.append(&2, List<&2, U32>, Laws.fdtlaw.components(B.Octets.to_list(s)), rest), Some{root}) == Pa.lk.walk(List.append(&2, List<&2, U32>, _, rest), Some{root}) : Maybe<&2, T.FdtNode>}
      sp.walk(List.append(&2, List<&2, U32>, Laws.fdtlaw.components(B.Octets.to_list(s)), rest), Some{root})
    case Fail{e}:
      {==}

def sp.aval(+mv: Maybe<&2, B.Octets>, +rest: List<&2, List<&2, U32>>, +root: T.FdtNode) -> {Laws.fdtlaw.resolve(Laws.fdtlaw.alias.val(mv), rest, root) == Pa.lk.alias.val(mv, rest, root) : Maybe<&2, T.FdtNode>}:
  match mv:
    case Some{v}:
      sp.astr(P.FdtProp.string(v), rest, root)
    case None{}:
      {==}

def sp.anode(+m: Maybe<&2, T.FdtNode>, +a: List<&2, U32>, +rest: List<&2, List<&2, U32>>, +root: T.FdtNode) -> {Laws.fdtlaw.resolve(Laws.fdtlaw.alias.node(m, a), rest, root) == Pa.lk.alias.val(Pa.lk.prop_of(m, B.Octets.of_list(a)), rest, root) : Maybe<&2, T.FdtNode>}:
  match m:
    case Some{n}:
      sp.aval(Pa.FdtNode.prop(n, B.Octets.of_list(a)), rest, root)
    case None{}:
      {==}

def sp.rel(+root: T.FdtNode, +cs: List<&2, List<&2, U32>>) -> {Laws.fdtlaw.relative(root, cs) == Pa.lk.alias(root, cs) : Maybe<&2, T.FdtNode>}:
  match cs:
    case Nil{}:
      {==}
    case Con{a, rest}:
      sp.anode(Pa.FdtNode.child(root, B.Octets.of_string("aliases")), a, rest, root)

def Laws.find_absolute(root, path, e):
  %sp.abs(B.of_string(path)) : {Pa.lk.find(_, root, Pa.lk.components(B.of_string(path))) == Laws.fdtlaw.walk(Laws.fdtlaw.components(B.of_string(path)), Some{root}) : Maybe<&2, T.FdtNode>}
  %Equal.sym(Bool, Laws.fdtlaw.absolute(B.of_string(path)), True{}, e) : {Pa.lk.find(_, root, Pa.lk.components(B.of_string(path))) == Laws.fdtlaw.walk(Laws.fdtlaw.components(B.of_string(path)), Some{root}) : Maybe<&2, T.FdtNode>}
  %sp.comp(B.of_string(path)) : {Pa.lk.walk(_, Some{root}) == Laws.fdtlaw.walk(Laws.fdtlaw.components(B.of_string(path)), Some{root}) : Maybe<&2, T.FdtNode>}
  Equal.sym(Maybe<&2, T.FdtNode>, Laws.fdtlaw.walk(Laws.fdtlaw.components(B.of_string(path)), Some{root}), Pa.lk.walk(Laws.fdtlaw.components(B.of_string(path)), Some{root}), sp.walk(Laws.fdtlaw.components(B.of_string(path)), Some{root}))

def Laws.find_alias(root, path, e):
  %sp.abs(B.of_string(path)) : {Pa.lk.find(_, root, Pa.lk.components(B.of_string(path))) == Laws.fdtlaw.relative(root, Laws.fdtlaw.components(B.of_string(path))) : Maybe<&2, T.FdtNode>}
  %Equal.sym(Bool, Laws.fdtlaw.absolute(B.of_string(path)), False{}, e) : {Pa.lk.find(_, root, Pa.lk.components(B.of_string(path))) == Laws.fdtlaw.relative(root, Laws.fdtlaw.components(B.of_string(path))) : Maybe<&2, T.FdtNode>}
  %sp.comp(B.of_string(path)) : {Pa.lk.alias(root, _) == Laws.fdtlaw.relative(root, Laws.fdtlaw.components(B.of_string(path))) : Maybe<&2, T.FdtNode>}
  Equal.sym(Maybe<&2, T.FdtNode>, Laws.fdtlaw.relative(root, Laws.fdtlaw.components(B.of_string(path))), Pa.lk.alias(root, Laws.fdtlaw.components(B.of_string(path))), sp.rel(root, Laws.fdtlaw.components(B.of_string(path))))

# reg: the cells of_reg writes (rg.cells, structural), cut back into pairs

def rg.cells(+ac: Nat, +sc: Nat, rs: List<&2, P.FdtReg>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      match r:
        case P.FdtReg{a, s}:
          B.append(B.append(P.pr.cells_of(ac, a), P.pr.cells_of(sc, s)), rg.cells(ac, sc, t))

def rg.rout(+ac: Nat, +sc: Nat, +rs: List<&2, P.FdtReg>, +acc: List<&2, U32>) -> {List.reverse.go(&2, U32, rg.cells(ac, sc, rs), acc) == P.pr.reg.out(ac, sc, rs, acc) : List<&2, U32>}:
  match rs:
    case Nil{}:
      {==}
    case Con{r, t}:
      match r:
        case P.FdtReg{+a, +s}:
          %FP.grev_app(U32, B.append(P.pr.cells_of(ac, a), P.pr.cells_of(sc, s)), rg.cells(ac, sc, t), acc) : {_ == P.pr.reg.out(ac, sc, t, List.reverse.go(&2, U32, P.pr.cells_of(sc, s), List.reverse.go(&2, U32, P.pr.cells_of(ac, a), acc))) : List<&2, U32>}
          %FP.grev_app(U32, P.pr.cells_of(ac, a), P.pr.cells_of(sc, s), acc) : {List.reverse.go(&2, U32, rg.cells(ac, sc, t), _) == P.pr.reg.out(ac, sc, t, List.reverse.go(&2, U32, P.pr.cells_of(sc, s), List.reverse.go(&2, U32, P.pr.cells_of(ac, a), acc))) : List<&2, U32>}
          rg.rout(ac, sc, t, List.reverse.go(&2, U32, P.pr.cells_of(sc, s), List.reverse.go(&2, U32, P.pr.cells_of(ac, a), acc)))

# n cells (0, 1 or 2) of a number: n of them
def rg.co_len(+n: Nat, +v: W.W64, +hle: {Nat.is_le(n, 2n) == True{} : Bool}) -> {n == B.len(P.pr.cells_of(n, v)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      match m:
        case 0n:
          {==}
        case 1n+k:
          match k:
            case 0n:
              {==}
            case 1n+j:
              Empty.absurd({1n+1n+1n+j == B.len(P.pr.cells_of(1n+1n+1n+j, v)) : Nat}, FP.ft_absurd(hle))

# and they read back as the number, when it fits them (W64 through word64's
# parts_of; a W64 of halves 0 and x is from_u32(x) and, for x = 0, zero(),
# by word64's from_parts_zero_hi and from_parts_zero)
def rg.co_num(+n: Nat, +v: W.W64, +hle: {Nat.is_le(n, 2n) == True{} : Bool}, +hf: {Laws.fdtlaw.fits(n, v) == True{} : Bool}) -> {v == P.pr.num(P.pr.cells_of(n, v)) : W.W64}:
  match n:
    case 0n:
      %WL.parts_of(v) : {_ == W.W64.zero() : W.W64}
      %Equal.sym(U32, W.W64.hi(v), 0, FP.ieq(W.W64.hi(v), 0, FP.and_l(U32.is_eq(W.W64.hi(v), 0), U32.is_eq(W.W64.lo(v), 0), hf))) : {W.W64.from_parts(_, W.W64.lo(v)) == W.W64.zero() : W.W64}
      %Equal.sym(U32, W.W64.lo(v), 0, FP.ieq(W.W64.lo(v), 0, FP.and_r(U32.is_eq(W.W64.hi(v), 0), U32.is_eq(W.W64.lo(v), 0), hf))) : {W.W64.from_parts(0, _) == W.W64.zero() : W.W64}
      WL.from_parts_zero()
    case 1n+m:
      match m:
        case 0n:
          %WL.parts_of(v) : {_ == W.W64.from_u32(W.W64.lo(v)) : W.W64}
          %Equal.sym(U32, W.W64.hi(v), 0, FP.ieq(W.W64.hi(v), 0, hf)) : {W.W64.from_parts(_, W.W64.lo(v)) == W.W64.from_u32(W.W64.lo(v)) : W.W64}
          WL.from_parts_zero_hi(W.W64.lo(v))
        case 1n+k:
          match k:
            case 0n:
              Equal.sym(W.W64, W.W64.from_parts(W.W64.hi(v), W.W64.lo(v)), v, WL.parts_of(v))
            case 1n+j:
              Empty.absurd({v == P.pr.num(P.pr.cells_of(1n+1n+1n+j, v)) : W.W64}, FP.ft_absurd(hle))

def rg.glen(+ac: Nat, +sc: Nat, +a: W.W64, +s: W.W64, +q: Nat, +hk: {Nat.add(ac, sc) == 1n+q : Nat}, +hac: {Nat.is_le(ac, 2n) == True{} : Bool}, +hsc: {Nat.is_le(sc, 2n) == True{} : Bool}) -> {B.len(B.append(P.pr.cells_of(ac, a), P.pr.cells_of(sc, s))) == 1n+q : Nat}:
  %FP.len_app(P.pr.cells_of(ac, a), P.pr.cells_of(sc, s)) : {_ == 1n+q : Nat}
  %rg.co_len(ac, a, hac) : {Nat.add(_, B.len(P.pr.cells_of(sc, s))) == 1n+q : Nat}
  %rg.co_len(sc, s, hsc) : {Nat.add(ac, _) == 1n+q : Nat}
  hk

def rg.elem(+ac: Nat, +sc: Nat, +a: W.W64, +s: W.W64, +hac: {Nat.is_le(ac, 2n) == True{} : Bool}, +hsc: {Nat.is_le(sc, 2n) == True{} : Bool}, +hfa: {Laws.fdtlaw.fits(ac, a) == True{} : Bool}, +hfs: {Laws.fdtlaw.fits(sc, s) == True{} : Bool}) -> {P.FdtReg{a, s} == P.FdtReg{P.pr.num(B.take(ac, B.append(P.pr.cells_of(ac, a), P.pr.cells_of(sc, s)))), P.pr.num(B.drop(ac, B.append(P.pr.cells_of(ac, a), P.pr.cells_of(sc, s))))} : P.FdtReg}:
  %Equal.sym(Nat, ac, B.len(P.pr.cells_of(ac, a)), rg.co_len(ac, a, hac)) : {P.FdtReg{a, s} == P.FdtReg{P.pr.num(B.take(_, B.append(P.pr.cells_of(ac, a), P.pr.cells_of(sc, s)))), P.pr.num(B.drop(_, B.append(P.pr.cells_of(ac, a), P.pr.cells_of(sc, s))))} : P.FdtReg}
  %FP.take_app(P.pr.cells_of(ac, a), P.pr.cells_of(sc, s)) : {P.FdtReg{a, s} == P.FdtReg{P.pr.num(_), P.pr.num(B.drop(B.len(P.pr.cells_of(ac, a)), B.append(P.pr.cells_of(ac, a), P.pr.cells_of(sc, s))))} : P.FdtReg}
  %FP.drop_app(P.pr.cells_of(ac, a), P.pr.cells_of(sc, s)) : {P.FdtReg{a, s} == P.FdtReg{P.pr.num(P.pr.cells_of(ac, a)), P.pr.num(_)} : P.FdtReg}
  %rg.co_num(ac, a, hac, hfa) : {P.FdtReg{a, s} == P.FdtReg{_, P.pr.num(P.pr.cells_of(sc, s))} : P.FdtReg}
  %rg.co_num(sc, s, hsc, hfs) : {P.FdtReg{a, s} == P.FdtReg{a, _} : P.FdtReg}
  {==}

# the cells of one pair, k = 1 + q of them, the first x then t: the counter
# reaches k at the last cell, and the pair is emitted
def rg.piece(+t: List<&2, U32>, +x: U32, +r: List<&2, U32>, +ac: Nat, +q: Nat, +n: Nat, +buf: List<&2, U32>, +regs: List<&2, P.FdtReg>, +hyp: {Nat.add(B.len(t), n) == q : Nat}) -> {P.pr.reg.go(r, ac, 1n+q, P.FdtRegAcc{Nil{}, 0n, Con{P.FdtReg{P.pr.num(B.take(ac, List.reverse(&2, U32, List.reverse.go(&2, U32, t, Con{x, buf})))), P.pr.num(B.drop(ac, List.reverse(&2, U32, List.reverse.go(&2, U32, t, Con{x, buf}))))}, regs}}) == P.pr.reg.go(Con{x, B.append(t, r)}, ac, 1n+q, P.FdtRegAcc{buf, n, regs}) : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}:
  match t:
    case Nil{}:
      %hyp : {P.pr.reg.go(r, ac, 1n+q, P.FdtRegAcc{Nil{}, 0n, Con{P.FdtReg{P.pr.num(B.take(ac, List.reverse(&2, U32, Con{x, buf}))), P.pr.num(B.drop(ac, List.reverse(&2, U32, Con{x, buf})))}, regs}}) == P.pr.reg.go(r, ac, 1n+q, P.pr.reg.emit(Nat.is_eq(1n+n, 1n+_), ac, Con{x, buf}, 1n+n, regs)) : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
      %nrefl(1n+n) : {P.pr.reg.go(r, ac, 1n+q, P.FdtRegAcc{Nil{}, 0n, Con{P.FdtReg{P.pr.num(B.take(ac, List.reverse(&2, U32, Con{x, buf}))), P.pr.num(B.drop(ac, List.reverse(&2, U32, Con{x, buf})))}, regs}}) == P.pr.reg.go(r, ac, 1n+q, P.pr.reg.emit(_, ac, Con{x, buf}, 1n+n, regs)) : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
      {==}
    case Con{y, t2}:
      %hyp : {P.pr.reg.go(r, ac, 1n+q, P.FdtRegAcc{Nil{}, 0n, Con{P.FdtReg{P.pr.num(B.take(ac, List.reverse(&2, U32, List.reverse.go(&2, U32, t2, Con{y, Con{x, buf}})))), P.pr.num(B.drop(ac, List.reverse(&2, U32, List.reverse.go(&2, U32, t2, Con{y, Con{x, buf}}))))}, regs}}) == P.pr.reg.go(Con{y, B.append(t2, r)}, ac, 1n+q, P.pr.reg.emit(Nat.is_eq(1n+n, 1n+_), ac, Con{x, buf}, 1n+n, regs)) : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
      %neq(n, B.len(t2)) : {P.pr.reg.go(r, ac, 1n+q, P.FdtRegAcc{Nil{}, 0n, Con{P.FdtReg{P.pr.num(B.take(ac, List.reverse(&2, U32, List.reverse.go(&2, U32, t2, Con{y, Con{x, buf}})))), P.pr.num(B.drop(ac, List.reverse(&2, U32, List.reverse.go(&2, U32, t2, Con{y, Con{x, buf}}))))}, regs}}) == P.pr.reg.go(Con{y, B.append(t2, r)}, ac, 1n+q, P.pr.reg.emit(_, ac, Con{x, buf}, 1n+n, regs)) : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
      rg.piece(t2, y, r, ac, q, 1n+n, Con{x, buf}, regs, Equal.trans(Nat, Nat.add(B.len(t2), 1n+n), 1n+Nat.add(B.len(t2), n), q, Equal.sym(Nat, 1n+Nat.add(B.len(t2), n), Nat.add(B.len(t2), 1n+n), FP.add_succ_r(B.len(t2), n)), hyp))

def rg.group(+g: List<&2, U32>, +r: List<&2, U32>, +ac: Nat, +q: Nat, +regs: List<&2, P.FdtReg>, +hl: {B.len(g) == 1n+q : Nat}) -> {P.pr.reg.go(r, ac, 1n+q, P.FdtRegAcc{Nil{}, 0n, Con{P.FdtReg{P.pr.num(B.take(ac, g)), P.pr.num(B.drop(ac, g))}, regs}}) == P.pr.reg.go(B.append(g, r), ac, 1n+q, P.FdtRegAcc{Nil{}, 0n, regs}) : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}:
  match g:
    case Nil{}:
      Empty.absurd({P.pr.reg.go(r, ac, 1n+q, P.FdtRegAcc{Nil{}, 0n, Con{P.FdtReg{P.pr.num(B.take(ac, Nil{})), P.pr.num(B.drop(ac, Nil{}))}, regs}}) == P.pr.reg.go(B.append(Nil{}, r), ac, 1n+q, P.FdtRegAcc{Nil{}, 0n, regs}) : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}, FP.nz_absurd(q, hl))
    case Con{+x, +t}:
      %Equal.sym(List<&2, U32>, Con{x, t}, List.reverse(&2, U32, List.reverse.go(&2, U32, Con{x, t}, Nil{})), FP.revrev(U32, Con{x, t})) : {P.pr.reg.go(r, ac, 1n+q, P.FdtRegAcc{Nil{}, 0n, Con{P.FdtReg{P.pr.num(B.take(ac, _)), P.pr.num(B.drop(ac, _))}, regs}}) == P.pr.reg.go(B.append(Con{x, t}, r), ac, 1n+q, P.FdtRegAcc{Nil{}, 0n, regs}) : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
      rg.piece(t, x, r, ac, q, 0n, Nil{}, regs, Equal.trans(Nat, Nat.add(B.len(t), 0n), B.len(t), q, UL.nat_add_zero(B.len(t)), succ_inj(B.len(t), q, hl)))

def rg.M(+rs: List<&2, P.FdtReg>, +ac: Nat, +sc: Nat, +q: Nat, +hk: {Nat.add(ac, sc) == 1n+q : Nat}, +hac: {Nat.is_le(ac, 2n) == True{} : Bool}, +hsc: {Nat.is_le(sc, 2n) == True{} : Bool}, +hf: {Laws.fdtlaw.reg_fits(ac, sc, rs) == True{} : Bool}, +regs: List<&2, P.FdtReg>) -> {P.pr.reg.go(rg.cells(ac, sc, rs), ac, 1n+q, P.FdtRegAcc{Nil{}, 0n, regs}) == Done{List.reverse(&2, P.FdtReg, List.reverse.go(&2, P.FdtReg, rs, regs))} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}:
  match rs:
    case Nil{}:
      {==}
    case Con{r, t}:
      match r:
        case P.FdtReg{+a, +s}:
          %rg.group(B.append(P.pr.cells_of(ac, a), P.pr.cells_of(sc, s)), rg.cells(ac, sc, t), ac, q, regs, rg.glen(ac, sc, a, s, q, hk, hac, hsc)) : {_ == Done{List.reverse(&2, P.FdtReg, List.reverse.go(&2, P.FdtReg, t, Con{P.FdtReg{a, s}, regs}))} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
          %rg.elem(ac, sc, a, s, hac, hsc, FP.and_l(Laws.fdtlaw.fits(ac, a), Laws.fdtlaw.fits(sc, s), FP.and_l(Bool.and(Laws.fdtlaw.fits(ac, a), Laws.fdtlaw.fits(sc, s)), Laws.fdtlaw.reg_fits(ac, sc, t), hf)), FP.and_r(Laws.fdtlaw.fits(ac, a), Laws.fdtlaw.fits(sc, s), FP.and_l(Bool.and(Laws.fdtlaw.fits(ac, a), Laws.fdtlaw.fits(sc, s)), Laws.fdtlaw.reg_fits(ac, sc, t), hf))) : {P.pr.reg.go(rg.cells(ac, sc, t), ac, 1n+q, P.FdtRegAcc{Nil{}, 0n, Con{_, regs}}) == Done{List.reverse(&2, P.FdtReg, List.reverse.go(&2, P.FdtReg, t, Con{P.FdtReg{a, s}, regs}))} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
          rg.M(t, ac, sc, q, hk, hac, hsc, FP.and_r(Bool.and(Laws.fdtlaw.fits(ac, a), Laws.fdtlaw.fits(sc, s)), Laws.fdtlaw.reg_fits(ac, sc, t), hf), Con{P.FdtReg{a, s}, regs})

def rg.fin(+ac: Nat, +sc: Nat, +k: Nat, +ek: {Nat.add(ac, sc) == k : Nat}, +hz: {Nat.is_eq(k, 0n) == False{} : Bool}, +hac: {Nat.is_le(ac, 2n) == True{} : Bool}, +hsc: {Nat.is_le(sc, 2n) == True{} : Bool}, +rs: List<&2, P.FdtReg>, +hf: {Laws.fdtlaw.reg_fits(ac, sc, rs) == True{} : Bool}) -> {P.pr.reg.go(rg.cells(ac, sc, rs), ac, k, P.FdtRegAcc{Nil{}, 0n, Nil{}}) == Done{rs} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}:
  match k:
    case 0n:
      Empty.absurd({P.pr.reg.go(rg.cells(ac, sc, rs), ac, 0n, P.FdtRegAcc{Nil{}, 0n, Nil{}}) == Done{rs} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}, FP.tf_absurd(hz))
    case 1n+q:
      %Equal.sym(List<&2, P.FdtReg>, rs, List.reverse(&2, P.FdtReg, List.reverse.go(&2, P.FdtReg, rs, Nil{})), FP.revrev(P.FdtReg, rs)) : {P.pr.reg.go(rg.cells(ac, sc, rs), ac, 1n+q, P.FdtRegAcc{Nil{}, 0n, Nil{}}) == Done{_} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
      rg.M(rs, ac, sc, q, ek, hac, hsc, hf, Nil{})

def Laws.reg_round_trip(ac, sc, hac, hsc, hnz, rs, hf):
  %Equal.sym(Bool, Nat.is_le(ac, 2n), True{}, hac) : {P.pr.reg.ok(Bool.and(_, Bool.and(Nat.is_le(sc, 2n), Bool.not(Nat.is_eq(Nat.add(ac, sc), 0n)))), P.FdtProp.of_reg(ac, sc, rs), ac, sc) == Done{rs} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
  %Equal.sym(Bool, Nat.is_le(sc, 2n), True{}, hsc) : {P.pr.reg.ok(Bool.and(True{}, Bool.and(_, Bool.not(Nat.is_eq(Nat.add(ac, sc), 0n)))), P.FdtProp.of_reg(ac, sc, rs), ac, sc) == Done{rs} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
  %Equal.sym(Bool, Nat.is_eq(Nat.add(ac, sc), 0n), False{}, hnz) : {P.pr.reg.ok(Bool.and(True{}, Bool.and(True{}, Bool.not(_))), P.FdtProp.of_reg(ac, sc, rs), ac, sc) == Done{rs} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
  %rg.rout(ac, sc, rs, Nil{}) : {P.pr.reg.cells(P.FdtProp.cells(P.FdtProp.of_cells(List.reverse(&2, U32, _))), ac, sc) == Done{rs} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
  %FP.revrev(U32, rg.cells(ac, sc, rs)) : {P.pr.reg.cells(P.FdtProp.cells(P.FdtProp.of_cells(_)), ac, sc) == Done{rs} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
  %Equal.sym(Result<&2, &2, E.FdtError, List<&2, U32>>, P.FdtProp.cells(P.FdtProp.of_cells(rg.cells(ac, sc, rs))), Done{rg.cells(ac, sc, rs)}, cells_rt0(rg.cells(ac, sc, rs))) : {P.pr.reg.cells(_, ac, sc) == Done{rs} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
  rg.fin(ac, sc, Nat.add(ac, sc), {==}, hnz, hac, hsc, rs, hf)

def Laws.reg_address_cells_bad(ac, sc, h, o):
  %Equal.sym(Bool, Nat.is_le(ac, 2n), False{}, h) : {P.pr.reg.ok(Bool.and(_, Bool.and(Nat.is_le(sc, 2n), Bool.not(Nat.is_eq(Nat.add(ac, sc), 0n)))), o, ac, sc) == Fail{E.FdtBadCells{}} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
  {==}

def Laws.reg_size_cells_bad(ac, sc, h, o):
  %Equal.sym(Bool, Nat.is_le(sc, 2n), False{}, h) : {P.pr.reg.ok(Bool.and(Nat.is_le(ac, 2n), Bool.and(_, Bool.not(Nat.is_eq(Nat.add(ac, sc), 0n)))), o, ac, sc) == Fail{E.FdtBadCells{}} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
  %and_false_r(Nat.is_le(ac, 2n)) : {P.pr.reg.ok(_, o, ac, sc) == Fail{E.FdtBadCells{}} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
  {==}

def Laws.reg_no_cells(o):
  {==}

def Laws.address_cells_value(n, x, h):
  %Equal.sym(Maybe<&2, B.Octets>, Pa.FdtNode.get(n, "#address-cells"), Some{P.FdtProp.of_u32(x)}, h) : {Pa.lk.cells(_, 2n) == U32.to_nat(x) : Nat}
  %u32rt(x) : {Pa.lk.cells.r(_, 2n) == U32.to_nat(x) : Nat}
  {==}

def Laws.size_cells_value(n, x, h):
  %Equal.sym(Maybe<&2, B.Octets>, Pa.FdtNode.get(n, "#size-cells"), Some{P.FdtProp.of_u32(x)}, h) : {Pa.lk.cells(_, 1n) == U32.to_nat(x) : Nat}
  %u32rt(x) : {Pa.lk.cells.r(_, 1n) == U32.to_nat(x) : Nat}
  {==}

def Laws.node_reg(parent, node, v, h):
  %Equal.sym(Maybe<&2, B.Octets>, Pa.FdtNode.get(node, "reg"), Some{v}, h) : {Pa.lk.reg(_, Pa.FdtNode.address_cells(parent), Pa.FdtNode.size_cells(parent)) == P.FdtProp.reg(Pa.FdtNode.address_cells(parent), Pa.FdtNode.size_cells(parent), v) : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
  {==}

def Laws.node_reg_none(parent, node, h):
  %Equal.sym(Maybe<&2, B.Octets>, Pa.FdtNode.get(node, "reg"), None{}, h) : {Pa.lk.reg(_, Pa.FdtNode.address_cells(parent), Pa.FdtNode.size_cells(parent)) == Done{Nil{}} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}
  {==}

def Laws.find_absolute_example():
  {==}

def Laws.find_alias_example():
  {==}

def Laws.reg_fits_example():
  {==}

def Laws.components_example():
  {==}
