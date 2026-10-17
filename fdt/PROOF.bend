import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./layout.bend as L
import ./header.bend as H
import ./rsvmap.bend as R
import ./structure.bend as S
import ./tree.bend as T
import ./props.bend as P
import ./path.bend as Pa
import ./fdt.bend as F
import ./example.bend as X
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../word64/LAWS.bend as WL
import ../word64/PROOF.bend as WP
import ./LAWS.bend as Laws

# Lemmas are mostly stated as {value == expression}, the direction a rewrite
# needs: %e : P replaces the expression (marked _ in P) by the value.

# Booleans

def bdisc(+b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def ft_absurd(+e: {False{} == True{} : Bool}) -> Empty:
  %e : bdisc(_)
  Unit{}

def and_l(+a: Bool, +b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ft_absurd(e))

def and_r(+a: Bool, +b: Bool, +e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, ft_absurd(e))

def not_t(+a: Bool, +e: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, ft_absurd(e))
    case False{}:
      {==}

def zero_t(+n: Nat, +e: {L.fdt.is_zero(n) == True{} : Bool}) -> {n == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, ft_absurd(e))

# Numbers

def ndisc(+n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def nz_absurd(+p: Nat, +e: {0n == 1n+p : Nat}) -> Empty:
  %e : ndisc(_)
  Unit{}

def sub_self(+n: Nat) -> {0n == Nat.sub(n, n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      sub_self(p)

def sub_zero(+n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def sub_add(+a: Nat, +b: Nat, +c: Nat) -> {Nat.sub(b, c) == Nat.sub(Nat.add(a, b), Nat.add(a, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      sub_add(p, b, c)

def sub_succ(+l: Nat, +x: Nat, +e: {0n == Nat.sub(l, x) : Nat}) -> {0n == Nat.sub(l, 1n+x) : Nat}:
  match l x:
    case 0n _:
      {==}
    case 1n+lp 0n:
      Empty.absurd({0n == Nat.sub(1n+lp, 1n) : Nat}, nz_absurd(lp, e))
    case 1n+lp 1n+xp:
      sub_succ(lp, xp, e)

def le_trans(+a: Nat, +b: Nat, +c: Nat, +e1: {0n == Nat.sub(a, b) : Nat}, +e2: {0n == Nat.sub(b, c) : Nat}) -> {0n == Nat.sub(a, c) : Nat}:
  match a b c:
    case 0n _ _:
      {==}
    case 1n+ap 0n _:
      Empty.absurd({0n == Nat.sub(1n+ap, c) : Nat}, nz_absurd(ap, e1))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({0n == Nat.sub(1n+ap, 0n) : Nat}, nz_absurd(bp, e2))
    case 1n+ap 1n+bp 1n+cp:
      le_trans(ap, bp, cp, e1, e2)

# Lists of bytes

def app_nil(+xs: List<&2, U32>) -> {B.append(xs, Nil{}) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %app_nil(t) : {Con{h, B.append(t, Nil{})} == Con{h, _} : List<&2, U32>}
      {==}

def app_assoc(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> {B.append(a, B.append(b, c)) == B.append(B.append(a, b), c) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %app_assoc(t, b, c) : {Con{h, B.append(t, B.append(b, c))} == Con{h, _} : List<&2, U32>}
      {==}

def len_app(+a: List<&2, U32>, +b: List<&2, U32>) -> {Nat.add(B.len(a), B.len(b)) == B.len(B.append(a, b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %len_app(t, b) : {1n+Nat.add(B.len(t), B.len(b)) == 1n+_ : Nat}
      {==}

def drop_app(+a: List<&2, U32>, +b: List<&2, U32>) -> {b == B.drop(B.len(a), B.append(a, b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      drop_app(t, b)

def take_app(+a: List<&2, U32>, +b: List<&2, U32>) -> {a == B.take(B.len(a), B.append(a, b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %take_app(t, b) : {Con{h, t} == Con{h, _} : List<&2, U32>}
      {==}

def prefix_le(+a: List<&2, U32>, +b: List<&2, U32>) -> {0n == Nat.sub(B.len(a), B.len(B.append(a, b))) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      prefix_le(t, b)

def suffix_le(+a: List<&2, U32>, +b: List<&2, U32>) -> {0n == Nat.sub(B.len(b), B.len(B.append(a, b))) : Nat}:
  match a:
    case Nil{}:
      sub_self(B.len(b))
    case Con{h, t}:
      sub_succ(B.len(b), B.len(B.append(t, b)), suffix_le(t, b))

# Lists of anything: reversal

def gapp_nil(-A: Data, +xs: List<&2, A>) -> {xs == List.append(&2, A, xs, Nil{}) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %gapp_nil(A, t) : {Con{h, t} == Con{h, _} : List<&2, A>}
      {==}

def rev_app(-A: Data, +xs: List<&2, A>, +a: List<&2, A>, +b: List<&2, A>) -> {List.reverse.go(&2, A, a, List.append(&2, A, xs, b)) == List.reverse.go(&2, A, List.reverse.go(&2, A, xs, a), b) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      rev_app(A, t, Con{h, a}, b)

# reversing a reversed list gives it back
def revrev(-A: Data, +xs: List<&2, A>) -> {xs == List.reverse(&2, A, List.reverse.go(&2, A, xs, Nil{})) : List<&2, A>}:
  Equal.trans(List<&2, A>, xs, List.append(&2, A, xs, Nil{}), List.reverse(&2, A, List.reverse.go(&2, A, xs, Nil{})), gapp_nil(A, xs), rev_app(A, xs, Nil{}, Nil{}))

# The fast forms: the code runs tail-recursive forms (layout.bend,
# structure.bend, tree.bend, fdt.bend: the .fast and .go defs), and each is
# equal, for every input, to the reference form the proofs below compute
# through. Stated {reference == fast}, the direction a rewrite needs to turn
# a fast form back into its reference. Each accumulator lemma has the shape
# go(xs, acc) == reverse.go(ref(xs), acc), and then reversing twice gives the
# reference back (revrev), as in bytes' own proofs.

def add_succ_r(+x: Nat, +a: Nat) -> {1n+Nat.add(x, a) == Nat.add(x, 1n+a) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %add_succ_r(p, a) : {1n+1n+Nat.add(p, a) == 1n+_ : Nat}
      {==}

def add_zero_r(+x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %add_zero_r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def and_true(+b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def and_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# reversing a joined list onto acc reverses its parts in turn
def grev_app(-A: Data, +xs: List<&2, A>, +b: List<&2, A>, +acc: List<&2, A>) -> {List.reverse.go(&2, A, b, List.reverse.go(&2, A, xs, acc)) == List.reverse.go(&2, A, List.append(&2, A, xs, b), acc) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      grev_app(A, t, b, Con{h, acc})

# Numbers: halving with an accumulator

def hgo(+n: Nat, +a: Nat) -> {Nat.add(L.fdt.half(n), a) == L.fdt.half.go(n, a) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          %hgo(q, 1n+a) : {1n+Nat.add(L.fdt.half(q), a) == _ : Nat}
          add_succ_r(L.fdt.half(q), a)

def half_fast(+n: Nat) -> {L.fdt.half(n) == L.fdt.half.fast(n) : Nat}:
  %hgo(n, 0n) : {L.fdt.half(n) == _ : Nat}
  Equal.sym(Nat, Nat.add(L.fdt.half(n), 0n), L.fdt.half(n), add_zero_r(L.fdt.half(n)))

def nbits_fast(+k: Nat, +n: Nat) -> {L.fdt.nbits(k, n) == L.fdt.nbits.fast(k, n) : Word(k)}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %half_fast(n) : {WCon{L.fdt.odd(n), L.fdt.nbits(p, L.fdt.half(n))} == WCon{L.fdt.odd(n), L.fdt.nbits.fast(p, _)} : Word(1n+p)}
      %nbits_fast(p, L.fdt.half(n)) : {WCon{L.fdt.odd(n), L.fdt.nbits(p, L.fdt.half(n))} == WCon{L.fdt.odd(n), _} : Word(1n+p)}
      {==}

def high_fast(+k: Nat, +n: Nat) -> {L.fdt.high(k, n) == L.fdt.high.fast(k, n) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %half_fast(n) : {L.fdt.high(p, L.fdt.half(n)) == L.fdt.high.fast(p, _) : Nat}
      high_fast(p, L.fdt.half(n))

def u32n_fast(+n: Nat) -> {L.fdt.u32n(n) == L.fdt.u32n.fast(n) : U32}:
  %nbits_fast(32n, n) : {L.fdt.u32n(n) == U32{_} : U32}
  {==}

def fits_fast(+n: Nat) -> {L.fdt.fits(n) == L.fdt.fits.fast(n) : Bool}:
  %high_fast(32n, n) : {L.fdt.fits(n) == L.fdt.is_zero(_) : Bool}
  {==}

# Tokens: the structure block's bytes, and the token checks

def tprop_fast(+off: U32, +vb: List<&2, U32>) -> {S.tok.prop(off, vb) == S.tok.prop.fast(off, vb) : List<&2, U32>}:
  %BL.len_fast(vb) : {S.tok.prop(off, vb) == B.append(B.be32(3), B.append(B.be32(L.fdt.u32n.fast(_)), B.append(B.be32(off), B.append.fast(vb, B.zeros(L.fdt.pad4(_)))))) : List<&2, U32>}
  %u32n_fast(B.len(vb)) : {S.tok.prop(off, vb) == B.append(B.be32(3), B.append(B.be32(_), B.append(B.be32(off), B.append.fast(vb, B.zeros(L.fdt.pad4(B.len(vb))))))) : List<&2, U32>}
  %BL.append_fast(vb, B.zeros(L.fdt.pad4(B.len(vb)))) : {S.tok.prop(off, vb) == B.append(B.be32(3), B.append(B.be32(L.fdt.u32n(B.len(vb))), B.append(B.be32(off), _))) : List<&2, U32>}
  {==}

def tok_fast(+t: S.FdtToken) -> {S.tok.list(t) == S.tok.list.fast(t) : List<&2, U32>}:
  match t:
    case S.FdtTokBegin{name}:
      {==}
    case S.FdtTokEnd{}:
      {==}
    case S.FdtTokProp{off, v}:
      tprop_fast(off, B.Octets.to_list(v))
    case S.FdtTokNop{}:
      {==}

def toks_go(+ts: List<&2, S.FdtToken>, +acc: List<&2, U32>) -> {List.reverse.go(&2, U32, S.toks.list(ts), acc) == S.toks.go(ts, acc) : List<&2, U32>}:
  match ts:
    case Nil{}:
      {==}
    case Con{t, r}:
      %grev_app(U32, S.tok.list(t), S.toks.list(r), acc) : {_ == S.toks.go(r, List.reverse.go(&2, U32, S.tok.list.fast(t), acc)) : List<&2, U32>}
      %tok_fast(t) : {List.reverse.go(&2, U32, S.toks.list(r), List.reverse.go(&2, U32, S.tok.list(t), acc)) == S.toks.go(r, List.reverse.go(&2, U32, _, acc)) : List<&2, U32>}
      toks_go(r, List.reverse.go(&2, U32, S.tok.list(t), acc))

def toks_fast(+ts: List<&2, S.FdtToken>) -> {S.toks.list(ts) == S.toks.fast(ts) : List<&2, U32>}:
  %toks_go(ts, Nil{}) : {S.toks.list(ts) == List.reverse(&2, U32, _) : List<&2, U32>}
  revrev(U32, S.toks.list(ts))

def valid_fast(+t: S.FdtToken) -> {S.tok.valid.ref(t) == S.FdtToken.valid(t) : Bool}:
  match t:
    case S.FdtTokBegin{name}:
      {==}
    case S.FdtTokEnd{}:
      {==}
    case S.FdtTokProp{off, v}:
      %Equal.sym(Nat, B.Octets.len(v), B.len(B.Octets.to_list(v)), BL.octets_len_list(v)) : {L.fdt.fits(B.len(B.Octets.to_list(v))) == L.fdt.fits.fast(_) : Bool}
      fits_fast(B.len(B.Octets.to_list(v)))
    case S.FdtTokNop{}:
      {==}

def vgo(+ts: List<&2, S.FdtToken>, +b: Bool) -> {Bool.and(b, S.tok.valid_all.ref(ts)) == S.tok.valid.go(ts, b) : Bool}:
  match ts:
    case Nil{}:
      and_true(b)
    case Con{t, r}:
      %vgo(r, Bool.and(b, S.FdtToken.valid(t))) : {Bool.and(b, Bool.and(S.tok.valid.ref(t), S.tok.valid_all.ref(r))) == _ : Bool}
      %valid_fast(t) : {Bool.and(b, Bool.and(S.tok.valid.ref(t), S.tok.valid_all.ref(r))) == Bool.and(Bool.and(b, _), S.tok.valid_all.ref(r)) : Bool}
      Equal.sym(Bool, Bool.and(Bool.and(b, S.tok.valid.ref(t)), S.tok.valid_all.ref(r)), Bool.and(b, Bool.and(S.tok.valid.ref(t), S.tok.valid_all.ref(r))), and_assoc(b, S.tok.valid.ref(t), S.tok.valid_all.ref(r)))

def valid_all_fast(+ts: List<&2, S.FdtToken>) -> {S.tok.valid_all.ref(ts) == S.FdtToken.valid_all(ts) : Bool}:
  vgo(ts, True{})

# The tree: the strings block, the tokens, and the checks

def pstrs_go(+ps: List<&2, T.FdtProp>, +acc: List<&2, U32>) -> {List.reverse.go(&2, U32, T.prop.strs(ps), acc) == T.pstrs.go(ps, acc) : List<&2, U32>}:
  match ps:
    case Nil{}:
      {==}
    case Con{p, t}:
      match p:
        case T.FdtProp{k, v}:
          %grev_app(U32, B.Octets.to_list(k), Con{0, T.prop.strs(t)}, acc) : {_ == T.pstrs.go(t, Con{0, List.reverse.go(&2, U32, B.Octets.to_list(k), acc)}) : List<&2, U32>}
          pstrs_go(t, Con{0, List.reverse.go(&2, U32, B.Octets.to_list(k), acc)})

def pstrs_fast(+ps: List<&2, T.FdtProp>) -> {T.prop.strs(ps) == T.pstrs.fast(ps) : List<&2, U32>}:
  %pstrs_go(ps, Nil{}) : {T.prop.strs(ps) == List.reverse(&2, U32, _) : List<&2, U32>}
  revrev(U32, T.prop.strs(ps))

def strs_go(+ns: List<&2, T.FdtNode>, +acc: List<&2, U32>) -> {List.reverse.go(&2, U32, T.flat.strs(ns), acc) == T.strs.go(ns, acc) : List<&2, U32>}:
  match ns:
    case Nil{}:
      {==}
    case Con{n, t}:
      match n:
        case T.FdtNode{nm, ps, cs}:
          %strs_go(t, T.strs.go(cs, T.pstrs.go(ps, acc))) : {List.reverse.go(&2, U32, T.flat.strs(Con{T.FdtNode{nm, ps, cs}, t}), acc) == _ : List<&2, U32>}
          %strs_go(cs, T.pstrs.go(ps, acc)) : {List.reverse.go(&2, U32, T.flat.strs(Con{T.FdtNode{nm, ps, cs}, t}), acc) == List.reverse.go(&2, U32, T.flat.strs(t), _) : List<&2, U32>}
          %pstrs_go(ps, acc) : {List.reverse.go(&2, U32, T.flat.strs(Con{T.FdtNode{nm, ps, cs}, t}), acc) == List.reverse.go(&2, U32, T.flat.strs(t), List.reverse.go(&2, U32, T.flat.strs(cs), _)) : List<&2, U32>}
          %grev_app(U32, T.prop.strs(ps), List.append(&2, U32, T.flat.strs(cs), T.flat.strs(t)), acc) : {_ == List.reverse.go(&2, U32, T.flat.strs(t), List.reverse.go(&2, U32, T.flat.strs(cs), List.reverse.go(&2, U32, T.prop.strs(ps), acc))) : List<&2, U32>}
          %grev_app(U32, T.flat.strs(cs), T.flat.strs(t), List.reverse.go(&2, U32, T.prop.strs(ps), acc)) : {_ == List.reverse.go(&2, U32, T.flat.strs(t), List.reverse.go(&2, U32, T.flat.strs(cs), List.reverse.go(&2, U32, T.prop.strs(ps), acc))) : List<&2, U32>}
          {==}

def strs_fast(+ns: List<&2, T.FdtNode>) -> {T.flat.strs(ns) == T.flat.strs.fast(ns) : List<&2, U32>}:
  %strs_go(ns, Nil{}) : {T.flat.strs(ns) == List.reverse(&2, U32, _) : List<&2, U32>}
  revrev(U32, T.flat.strs(ns))

def ptoks_go(+ps: List<&2, T.FdtProp>, +off: Nat, +acc: List<&2, S.FdtToken>) -> {List.reverse.go(&2, S.FdtToken, T.prop.toks(ps, off), acc) == T.ptoks.go(ps, off, acc) : List<&2, S.FdtToken>}:
  match ps:
    case Nil{}:
      {==}
    case Con{p, t}:
      match p:
        case T.FdtProp{k, v}:
          %u32n_fast(off) : {List.reverse.go(&2, S.FdtToken, T.prop.toks(Con{T.FdtProp{k, v}, t}, off), acc) == T.ptoks.go(t, Nat.add(off, B.len(B.append(B.Octets.to_list(k), [0]))), Con{S.FdtTokProp{_, v}, acc}) : List<&2, S.FdtToken>}
          ptoks_go(t, Nat.add(off, B.len(B.append(B.Octets.to_list(k), [0]))), Con{S.FdtTokProp{L.fdt.u32n(off), v}, acc})

def ftoks_go(+ns: List<&2, T.FdtNode>, +off: Nat, +acc: List<&2, S.FdtToken>) -> {List.reverse.go(&2, S.FdtToken, T.flat.toks(ns, off), acc) == T.ftoks.go(ns, off, acc) : List<&2, S.FdtToken>}:
  match ns:
    case Nil{}:
      {==}
    case Con{n, t}:
      match n:
        case T.FdtNode{nm, ps, cs}:
          %pstrs_fast(ps) : {List.reverse.go(&2, S.FdtToken, T.flat.toks(Con{T.FdtNode{nm, ps, cs}, t}, off), acc) == T.ftoks.go(t, Nat.add(Nat.add(off, B.len.fast(_)), B.len.fast(T.flat.strs.fast(cs))), Con{S.FdtTokEnd{}, T.ftoks.go(cs, Nat.add(off, B.len.fast(_)), T.ptoks.go(ps, off, Con{S.FdtTokBegin{nm}, acc}))}) : List<&2, S.FdtToken>}
          %BL.len_fast(T.prop.strs(ps)) : {List.reverse.go(&2, S.FdtToken, T.flat.toks(Con{T.FdtNode{nm, ps, cs}, t}, off), acc) == T.ftoks.go(t, Nat.add(Nat.add(off, _), B.len.fast(T.flat.strs.fast(cs))), Con{S.FdtTokEnd{}, T.ftoks.go(cs, Nat.add(off, _), T.ptoks.go(ps, off, Con{S.FdtTokBegin{nm}, acc}))}) : List<&2, S.FdtToken>}
          %strs_fast(cs) : {List.reverse.go(&2, S.FdtToken, T.flat.toks(Con{T.FdtNode{nm, ps, cs}, t}, off), acc) == T.ftoks.go(t, Nat.add(Nat.add(off, B.len(T.prop.strs(ps))), B.len.fast(_)), Con{S.FdtTokEnd{}, T.ftoks.go(cs, Nat.add(off, B.len(T.prop.strs(ps))), T.ptoks.go(ps, off, Con{S.FdtTokBegin{nm}, acc}))}) : List<&2, S.FdtToken>}
          %BL.len_fast(T.flat.strs(cs)) : {List.reverse.go(&2, S.FdtToken, T.flat.toks(Con{T.FdtNode{nm, ps, cs}, t}, off), acc) == T.ftoks.go(t, Nat.add(Nat.add(off, B.len(T.prop.strs(ps))), _), Con{S.FdtTokEnd{}, T.ftoks.go(cs, Nat.add(off, B.len(T.prop.strs(ps))), T.ptoks.go(ps, off, Con{S.FdtTokBegin{nm}, acc}))}) : List<&2, S.FdtToken>}
          %ftoks_go(t, Nat.add(Nat.add(off, B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs))), Con{S.FdtTokEnd{}, T.ftoks.go(cs, Nat.add(off, B.len(T.prop.strs(ps))), T.ptoks.go(ps, off, Con{S.FdtTokBegin{nm}, acc}))}) : {List.reverse.go(&2, S.FdtToken, T.flat.toks(Con{T.FdtNode{nm, ps, cs}, t}, off), acc) == _ : List<&2, S.FdtToken>}
          %ftoks_go(cs, Nat.add(off, B.len(T.prop.strs(ps))), T.ptoks.go(ps, off, Con{S.FdtTokBegin{nm}, acc})) : {List.reverse.go(&2, S.FdtToken, T.flat.toks(Con{T.FdtNode{nm, ps, cs}, t}, off), acc) == List.reverse.go(&2, S.FdtToken, T.flat.toks(t, Nat.add(Nat.add(off, B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs)))), Con{S.FdtTokEnd{}, _}) : List<&2, S.FdtToken>}
          %ptoks_go(ps, off, Con{S.FdtTokBegin{nm}, acc}) : {List.reverse.go(&2, S.FdtToken, T.flat.toks(Con{T.FdtNode{nm, ps, cs}, t}, off), acc) == List.reverse.go(&2, S.FdtToken, T.flat.toks(t, Nat.add(Nat.add(off, B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs)))), Con{S.FdtTokEnd{}, List.reverse.go(&2, S.FdtToken, T.flat.toks(cs, Nat.add(off, B.len(T.prop.strs(ps)))), _)}) : List<&2, S.FdtToken>}
          %grev_app(S.FdtToken, T.prop.toks(ps, off), List.append(&2, S.FdtToken, T.flat.toks(cs, Nat.add(off, B.len(T.prop.strs(ps)))), Con{S.FdtTokEnd{}, T.flat.toks(t, Nat.add(Nat.add(off, B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs))))}), Con{S.FdtTokBegin{nm}, acc}) : {_ == List.reverse.go(&2, S.FdtToken, T.flat.toks(t, Nat.add(Nat.add(off, B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs)))), Con{S.FdtTokEnd{}, List.reverse.go(&2, S.FdtToken, T.flat.toks(cs, Nat.add(off, B.len(T.prop.strs(ps)))), List.reverse.go(&2, S.FdtToken, T.prop.toks(ps, off), Con{S.FdtTokBegin{nm}, acc}))}) : List<&2, S.FdtToken>}
          %grev_app(S.FdtToken, T.flat.toks(cs, Nat.add(off, B.len(T.prop.strs(ps)))), Con{S.FdtTokEnd{}, T.flat.toks(t, Nat.add(Nat.add(off, B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs))))}, List.reverse.go(&2, S.FdtToken, T.prop.toks(ps, off), Con{S.FdtTokBegin{nm}, acc})) : {_ == List.reverse.go(&2, S.FdtToken, T.flat.toks(t, Nat.add(Nat.add(off, B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs)))), Con{S.FdtTokEnd{}, List.reverse.go(&2, S.FdtToken, T.flat.toks(cs, Nat.add(off, B.len(T.prop.strs(ps)))), List.reverse.go(&2, S.FdtToken, T.prop.toks(ps, off), Con{S.FdtTokBegin{nm}, acc}))}) : List<&2, S.FdtToken>}
          {==}

def ftoks_fast(+ns: List<&2, T.FdtNode>, +off: Nat) -> {T.flat.toks(ns, off) == T.flat.toks.fast(ns, off) : List<&2, S.FdtToken>}:
  %ftoks_go(ns, off, Nil{}) : {T.flat.toks(ns, off) == List.reverse(&2, S.FdtToken, _) : List<&2, S.FdtToken>}
  revrev(S.FdtToken, T.flat.toks(ns, off))

def pnames_go(+ps: List<&2, T.FdtProp>, +b: Bool) -> {Bool.and(b, T.prop.names_ok(ps)) == T.pnames.go(ps, b) : Bool}:
  match ps:
    case Nil{}:
      and_true(b)
    case Con{p, t}:
      match p:
        case T.FdtProp{k, v}:
          %pnames_go(t, Bool.and(b, L.fdt.nonul(B.Octets.to_list(k)))) : {Bool.and(b, Bool.and(L.fdt.nonul(B.Octets.to_list(k)), T.prop.names_ok(t))) == _ : Bool}
          Equal.sym(Bool, Bool.and(Bool.and(b, L.fdt.nonul(B.Octets.to_list(k))), T.prop.names_ok(t)), Bool.and(b, Bool.and(L.fdt.nonul(B.Octets.to_list(k)), T.prop.names_ok(t))), and_assoc(b, L.fdt.nonul(B.Octets.to_list(k)), T.prop.names_ok(t)))

def names_go(+ns: List<&2, T.FdtNode>, +b: Bool) -> {Bool.and(b, T.flat.names_ok(ns)) == T.names.go(ns, b) : Bool}:
  match ns:
    case Nil{}:
      and_true(b)
    case Con{n, t}:
      match n:
        case T.FdtNode{nm, ps, cs}:
          %names_go(t, T.names.go(cs, T.pnames.go(ps, Bool.and(b, L.fdt.nonul(B.Octets.to_list(nm)))))) : {Bool.and(b, Bool.and(L.fdt.nonul(B.Octets.to_list(nm)), Bool.and(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(t))))) == _ : Bool}
          %names_go(cs, T.pnames.go(ps, Bool.and(b, L.fdt.nonul(B.Octets.to_list(nm))))) : {Bool.and(b, Bool.and(L.fdt.nonul(B.Octets.to_list(nm)), Bool.and(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(t))))) == Bool.and(_, T.flat.names_ok(t)) : Bool}
          %pnames_go(ps, Bool.and(b, L.fdt.nonul(B.Octets.to_list(nm)))) : {Bool.and(b, Bool.and(L.fdt.nonul(B.Octets.to_list(nm)), Bool.and(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(t))))) == Bool.and(Bool.and(_, T.flat.names_ok(cs)), T.flat.names_ok(t)) : Bool}
          %and_assoc(b, L.fdt.nonul(B.Octets.to_list(nm)), Bool.and(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(t)))) : {_ == Bool.and(Bool.and(Bool.and(Bool.and(b, L.fdt.nonul(B.Octets.to_list(nm))), T.prop.names_ok(ps)), T.flat.names_ok(cs)), T.flat.names_ok(t)) : Bool}
          %and_assoc(Bool.and(b, L.fdt.nonul(B.Octets.to_list(nm))), T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(t))) : {_ == Bool.and(Bool.and(Bool.and(Bool.and(b, L.fdt.nonul(B.Octets.to_list(nm))), T.prop.names_ok(ps)), T.flat.names_ok(cs)), T.flat.names_ok(t)) : Bool}
          %and_assoc(Bool.and(Bool.and(b, L.fdt.nonul(B.Octets.to_list(nm))), T.prop.names_ok(ps)), T.flat.names_ok(cs), T.flat.names_ok(t)) : {_ == Bool.and(Bool.and(Bool.and(Bool.and(b, L.fdt.nonul(B.Octets.to_list(nm))), T.prop.names_ok(ps)), T.flat.names_ok(cs)), T.flat.names_ok(t)) : Bool}
          {==}

def names_fast(+root: T.FdtNode) -> {T.names_ok.ref(root) == T.FdtNode.names_ok(root) : Bool}:
  names_go([root], True{})

def pvalues_go(+ps: List<&2, T.FdtProp>, +b: Bool) -> {Bool.and(b, T.prop.values_ok(ps)) == T.pvalues.go(ps, b) : Bool}:
  match ps:
    case Nil{}:
      and_true(b)
    case Con{p, t}:
      match p:
        case T.FdtProp{k, v}:
          %Equal.sym(Nat, B.Octets.len(v), B.len(B.Octets.to_list(v)), BL.octets_len_list(v)) : {Bool.and(b, Bool.and(L.fdt.fits(B.len(B.Octets.to_list(v))), T.prop.values_ok(t))) == T.pvalues.go(t, Bool.and(b, L.fdt.fits.fast(_))) : Bool}
          %fits_fast(B.len(B.Octets.to_list(v))) : {Bool.and(b, Bool.and(L.fdt.fits(B.len(B.Octets.to_list(v))), T.prop.values_ok(t))) == T.pvalues.go(t, Bool.and(b, _)) : Bool}
          %pvalues_go(t, Bool.and(b, L.fdt.fits(B.len(B.Octets.to_list(v))))) : {Bool.and(b, Bool.and(L.fdt.fits(B.len(B.Octets.to_list(v))), T.prop.values_ok(t))) == _ : Bool}
          Equal.sym(Bool, Bool.and(Bool.and(b, L.fdt.fits(B.len(B.Octets.to_list(v)))), T.prop.values_ok(t)), Bool.and(b, Bool.and(L.fdt.fits(B.len(B.Octets.to_list(v))), T.prop.values_ok(t))), and_assoc(b, L.fdt.fits(B.len(B.Octets.to_list(v))), T.prop.values_ok(t)))

def values_go(+ns: List<&2, T.FdtNode>, +b: Bool) -> {Bool.and(b, T.flat.values_ok(ns)) == T.values.go(ns, b) : Bool}:
  match ns:
    case Nil{}:
      and_true(b)
    case Con{n, t}:
      match n:
        case T.FdtNode{nm, ps, cs}:
          %values_go(t, T.values.go(cs, T.pvalues.go(ps, b))) : {Bool.and(b, Bool.and(T.prop.values_ok(ps), Bool.and(T.flat.values_ok(cs), T.flat.values_ok(t)))) == _ : Bool}
          %values_go(cs, T.pvalues.go(ps, b)) : {Bool.and(b, Bool.and(T.prop.values_ok(ps), Bool.and(T.flat.values_ok(cs), T.flat.values_ok(t)))) == Bool.and(_, T.flat.values_ok(t)) : Bool}
          %pvalues_go(ps, b) : {Bool.and(b, Bool.and(T.prop.values_ok(ps), Bool.and(T.flat.values_ok(cs), T.flat.values_ok(t)))) == Bool.and(Bool.and(_, T.flat.values_ok(cs)), T.flat.values_ok(t)) : Bool}
          %and_assoc(b, T.prop.values_ok(ps), Bool.and(T.flat.values_ok(cs), T.flat.values_ok(t))) : {_ == Bool.and(Bool.and(Bool.and(b, T.prop.values_ok(ps)), T.flat.values_ok(cs)), T.flat.values_ok(t)) : Bool}
          %and_assoc(Bool.and(b, T.prop.values_ok(ps)), T.flat.values_ok(cs), T.flat.values_ok(t)) : {_ == Bool.and(Bool.and(Bool.and(b, T.prop.values_ok(ps)), T.flat.values_ok(cs)), T.flat.values_ok(t)) : Bool}
          {==}

def wf_fast(+root: T.FdtNode) -> {T.wf.ref(root) == T.FdtNode.wf(root) : Bool}:
  %names_fast(root) : {T.wf.ref(root) == Bool.and(_, T.values.go([root], True{})) : Bool}
  %values_go([root], True{}) : {T.wf.ref(root) == Bool.and(T.names_ok.ref(root), _) : Bool}
  {==}

def flat_ok_fast(+root: T.FdtNode) -> {T.flat_ok.ref(root) == T.FdtNode.flat_ok(root) : Bool}:
  %names_fast(root) : {T.flat_ok.ref(root) == Bool.and(_, L.fdt.fits.fast(B.len.fast(T.flat.strs.fast([root])))) : Bool}
  %strs_fast([root]) : {T.flat_ok.ref(root) == Bool.and(T.names_ok.ref(root), L.fdt.fits.fast(B.len.fast(_))) : Bool}
  %BL.len_fast(T.flat.strs([root])) : {T.flat_ok.ref(root) == Bool.and(T.names_ok.ref(root), L.fdt.fits.fast(_)) : Bool}
  %fits_fast(B.len(T.flat.strs([root]))) : {T.flat_ok.ref(root) == Bool.and(T.names_ok.ref(root), _) : Bool}
  {==}

# The blob: the writer and the reader

def layout_fast(+r: List<&2, U32>, +s: List<&2, U32>, +t: List<&2, U32>, +boot: U32) -> {F.build.layout(r, s, t, boot) == F.build.layout.fast(r, s, t, boot) : List<&2, U32>}:
  %BL.append_fast(s, t) : {F.build.layout(r, s, t, boot) == B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n.fast(Nat.add(40n, B.len.fast(B.append(r, _)))), L.fdt.u32n(Nat.add(40n, B.len(r))), L.fdt.u32n.fast(Nat.add(40n, B.len.fast(B.append(r, s)))), 40, 17, 16, boot, L.fdt.u32n.fast(B.len.fast(t)), L.fdt.u32n.fast(B.len.fast(s))}), B.append(r, _)) : List<&2, U32>}
  %BL.len_fast(B.append(r, B.append(s, t))) : {F.build.layout(r, s, t, boot) == B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n.fast(Nat.add(40n, _)), L.fdt.u32n(Nat.add(40n, B.len(r))), L.fdt.u32n.fast(Nat.add(40n, B.len.fast(B.append(r, s)))), 40, 17, 16, boot, L.fdt.u32n.fast(B.len.fast(t)), L.fdt.u32n.fast(B.len.fast(s))}), B.append(r, B.append(s, t))) : List<&2, U32>}
  %BL.len_fast(B.append(r, s)) : {F.build.layout(r, s, t, boot) == B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n.fast(Nat.add(40n, B.len(B.append(r, B.append(s, t))))), L.fdt.u32n(Nat.add(40n, B.len(r))), L.fdt.u32n.fast(Nat.add(40n, _)), 40, 17, 16, boot, L.fdt.u32n.fast(B.len.fast(t)), L.fdt.u32n.fast(B.len.fast(s))}), B.append(r, B.append(s, t))) : List<&2, U32>}
  %BL.len_fast(t) : {F.build.layout(r, s, t, boot) == B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n.fast(Nat.add(40n, B.len(B.append(r, B.append(s, t))))), L.fdt.u32n(Nat.add(40n, B.len(r))), L.fdt.u32n.fast(Nat.add(40n, B.len(B.append(r, s)))), 40, 17, 16, boot, L.fdt.u32n.fast(_), L.fdt.u32n.fast(B.len.fast(s))}), B.append(r, B.append(s, t))) : List<&2, U32>}
  %BL.len_fast(s) : {F.build.layout(r, s, t, boot) == B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n.fast(Nat.add(40n, B.len(B.append(r, B.append(s, t))))), L.fdt.u32n(Nat.add(40n, B.len(r))), L.fdt.u32n.fast(Nat.add(40n, B.len(B.append(r, s)))), 40, 17, 16, boot, L.fdt.u32n.fast(B.len(t)), L.fdt.u32n.fast(_)}), B.append(r, B.append(s, t))) : List<&2, U32>}
  %u32n_fast(Nat.add(40n, B.len(B.append(r, B.append(s, t))))) : {F.build.layout(r, s, t, boot) == B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), _, L.fdt.u32n(Nat.add(40n, B.len(r))), L.fdt.u32n.fast(Nat.add(40n, B.len(B.append(r, s)))), 40, 17, 16, boot, L.fdt.u32n.fast(B.len(t)), L.fdt.u32n.fast(B.len(s))}), B.append(r, B.append(s, t))) : List<&2, U32>}
  %u32n_fast(Nat.add(40n, B.len(B.append(r, s)))) : {F.build.layout(r, s, t, boot) == B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(r, B.append(s, t))))), L.fdt.u32n(Nat.add(40n, B.len(r))), _, 40, 17, 16, boot, L.fdt.u32n.fast(B.len(t)), L.fdt.u32n.fast(B.len(s))}), B.append(r, B.append(s, t))) : List<&2, U32>}
  %u32n_fast(B.len(t)) : {F.build.layout(r, s, t, boot) == B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(r, B.append(s, t))))), L.fdt.u32n(Nat.add(40n, B.len(r))), L.fdt.u32n(Nat.add(40n, B.len(B.append(r, s)))), 40, 17, 16, boot, _, L.fdt.u32n.fast(B.len(s))}), B.append(r, B.append(s, t))) : List<&2, U32>}
  %u32n_fast(B.len(s)) : {F.build.layout(r, s, t, boot) == B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(r, B.append(s, t))))), L.fdt.u32n(Nat.add(40n, B.len(r))), L.fdt.u32n(Nat.add(40n, B.len(B.append(r, s)))), 40, 17, 16, boot, L.fdt.u32n(B.len(t)), _}), B.append(r, B.append(s, t))) : List<&2, U32>}
  {==}

def build_fast(+root: T.FdtNode, +rsv: List<&2, R.FdtRsv>, +boot: U32) -> {F.build.simple(root, rsv, boot) == F.build.fast(root, rsv, boot) : List<&2, U32>}:
  %ftoks_fast([root], 0n) : {F.build.simple(root, rsv, boot) == F.build.layout.fast(R.rsv.list(rsv), S.toks.fast(_), T.flat.strs.fast([root]), boot) : List<&2, U32>}
  %toks_fast(T.flat.toks([root], 0n)) : {F.build.simple(root, rsv, boot) == F.build.layout.fast(R.rsv.list(rsv), _, T.flat.strs.fast([root]), boot) : List<&2, U32>}
  %strs_fast([root]) : {F.build.simple(root, rsv, boot) == F.build.layout.fast(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)), _, boot) : List<&2, U32>}
  layout_fast(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]), boot)

def buildable_fast(+root: T.FdtNode, +rsv: List<&2, R.FdtRsv>) -> {F.buildable.ref(root, rsv) == F.Fdt.buildable(root, rsv) : Bool}:
  %wf_fast(root) : {F.buildable.ref(root, rsv) == Bool.and(_, Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits.fast(Nat.add(40n, B.len.fast(F.build.rest.fast(root, rsv)))))) : Bool}
  %ftoks_fast([root], 0n) : {F.buildable.ref(root, rsv) == Bool.and(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits.fast(Nat.add(40n, B.len.fast(B.append(R.rsv.list(rsv), B.append.fast(S.toks.fast(_), T.flat.strs.fast([root])))))))) : Bool}
  %toks_fast(T.flat.toks([root], 0n)) : {F.buildable.ref(root, rsv) == Bool.and(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits.fast(Nat.add(40n, B.len.fast(B.append(R.rsv.list(rsv), B.append.fast(_, T.flat.strs.fast([root])))))))) : Bool}
  %strs_fast([root]) : {F.buildable.ref(root, rsv) == Bool.and(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits.fast(Nat.add(40n, B.len.fast(B.append(R.rsv.list(rsv), B.append.fast(S.toks.list(T.flat.toks([root], 0n)), _))))))) : Bool}
  %BL.append_fast(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])) : {F.buildable.ref(root, rsv) == Bool.and(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits.fast(Nat.add(40n, B.len.fast(B.append(R.rsv.list(rsv), _)))))) : Bool}
  %BL.len_fast(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))) : {F.buildable.ref(root, rsv) == Bool.and(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits.fast(Nat.add(40n, _)))) : Bool}
  %fits_fast(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))) : {F.buildable.ref(root, rsv) == Bool.and(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), _)) : Bool}
  {==}

def fstruct_eq(+is17: Bool, +os: Nat, +sst: Nat, +region: List<&2, U32>) -> {F.parse.struct(is17, os, sst, region) == F.parse.fstruct(is17, os, sst, region) : Result<&2, &2, E.FdtError, List<&2, S.FdtToken>>}:
  match is17:
    case True{}:
      %BL.take_fast(sst, B.drop(os, region)) : {F.parse.struct(True{}, os, sst, region) == S.FdtLexer.finish(True{}, S.lx.go(_, S.FdtLexer.start())) : Result<&2, &2, E.FdtError, List<&2, S.FdtToken>>}
      {==}
    case False{}:
      {==}

def f6_eq(+rules: T.FdtTreeRules, +v: U32, +boot: U32, +region: List<&2, U32>, +orsv: Nat, +os: Nat, +sst: Nat, +ostr: Nat, +sstr: Nat) -> {F.parse.p6(rules, v, boot, region, orsv, os, sst, ostr, sstr) == F.parse.f6(rules, v, boot, region, orsv, os, sst, ostr, sstr) : Result<&2, &2, E.FdtError, F.FdtBlob>}:
  %fstruct_eq(U32.is_lt(16, v), os, sst, region) : {F.parse.p6(rules, v, boot, region, orsv, os, sst, ostr, sstr) == F.parse.p7(R.rsv.read(B.drop(orsv, region)), _, rules, v, boot, B.take.fast(sstr, B.drop(ostr, region))) : Result<&2, &2, E.FdtError, F.FdtBlob>}
  %BL.take_fast(sstr, B.drop(ostr, region)) : {F.parse.p6(rules, v, boot, region, orsv, os, sst, ostr, sstr) == F.parse.p7(R.rsv.read(B.drop(orsv, region)), F.parse.struct(U32.is_lt(16, v), os, sst, region), rules, v, boot, _) : Result<&2, &2, E.FdtError, F.FdtBlob>}
  {==}

def f5_eq(+r: Result<&2, &2, E.FdtError, Unit>, +rules: T.FdtTreeRules, +h: H.FdtHeader, +xs: List<&2, U32>) -> {F.parse.p5(r, rules, h, xs) == F.parse.f5(r, rules, h, xs) : Result<&2, &2, E.FdtError, F.FdtBlob>}:
  match r:
    case Done{u}:
      match h:
        case H.FdtHeader{magic, totalsize, off_dt_struct, off_dt_strings, off_mem_rsvmap, version, last_comp_version, boot_cpuid_phys, size_dt_strings, size_dt_struct}:
          %BL.take_fast(U32.to_nat(totalsize), xs) : {F.parse.p5(Done{u}, rules, H.FdtHeader{magic, totalsize, off_dt_struct, off_dt_strings, off_mem_rsvmap, version, last_comp_version, boot_cpuid_phys, size_dt_strings, size_dt_struct}, xs) == F.parse.f6(rules, version, boot_cpuid_phys, _, U32.to_nat(off_mem_rsvmap), U32.to_nat(off_dt_struct), U32.to_nat(size_dt_struct), U32.to_nat(off_dt_strings), U32.to_nat(size_dt_strings)) : Result<&2, &2, E.FdtError, F.FdtBlob>}
          f6_eq(rules, version, boot_cpuid_phys, B.take(U32.to_nat(totalsize), xs), U32.to_nat(off_mem_rsvmap), U32.to_nat(off_dt_struct), U32.to_nat(size_dt_struct), U32.to_nat(off_dt_strings), U32.to_nat(size_dt_strings))
    case Fail{e}:
      {==}

def f4_eq(+m: Maybe<&2, H.FdtHeader>, +opts: F.FdtOptions, +xs: List<&2, U32>) -> {F.parse.p4(m, opts, xs) == F.parse.f4(m, opts, xs) : Result<&2, &2, E.FdtError, F.FdtBlob>}:
  match m:
    case Some{h}:
      match opts:
        case F.FdtOptions{vs, rules}:
          %BL.len_fast(xs) : {F.parse.p4(Some{h}, F.FdtOptions{vs, rules}, xs) == F.parse.f5(H.FdtHeader.check(vs, h, _), rules, h, xs) : Result<&2, &2, E.FdtError, F.FdtBlob>}
          f5_eq(H.FdtHeader.check(vs, h, B.len(xs)), rules, h, xs)
    case None{}:
      {==}

def f3_eq(+ok: Bool, +opts: F.FdtOptions, +xs: List<&2, U32>) -> {F.parse.p3(ok, opts, xs) == F.parse.f3(ok, opts, xs) : Result<&2, &2, E.FdtError, F.FdtBlob>}:
  match ok:
    case True{}:
      f4_eq(H.hdr.decode(xs), opts, xs)
    case False{}:
      {==}

def f2_eq(+m: Maybe<&2, U32>, +opts: F.FdtOptions, +xs: List<&2, U32>) -> {F.parse.p2(m, opts, xs) == F.parse.f2(m, opts, xs) : Result<&2, &2, E.FdtError, F.FdtBlob>}:
  match m:
    case Some{v}:
      f3_eq(U32.is_eq(v, H.FdtHeader.magic_value()), opts, xs)
    case None{}:
      {==}

# the reader the package runs is the reference reader, on every list
def parse_fast(+opts: F.FdtOptions, +xs: List<&2, U32>) -> {F.parse.p1(opts, xs) == F.parse.f1(opts, xs) : Result<&2, &2, E.FdtError, F.FdtBlob>}:
  f2_eq(B.be32_at(xs, 0n), opts, xs)

# Property values: the encoders and the string checks

def nngo(+xs: List<&2, U32>, +b: Bool) -> {Bool.and(b, L.fdt.nonul(xs)) == L.fdt.nonul.go(xs, b) : Bool}:
  match xs:
    case Nil{}:
      and_true(b)
    case Con{h, t}:
      %nngo(t, Bool.and(b, Bool.not(U32.is_eq(h, 0)))) : {Bool.and(b, Bool.and(Bool.not(U32.is_eq(h, 0)), L.fdt.nonul(t))) == _ : Bool}
      Equal.sym(Bool, Bool.and(Bool.and(b, Bool.not(U32.is_eq(h, 0))), L.fdt.nonul(t)), Bool.and(b, Bool.and(Bool.not(U32.is_eq(h, 0)), L.fdt.nonul(t))), and_assoc(b, Bool.not(U32.is_eq(h, 0)), L.fdt.nonul(t)))

def nonul_fast(+xs: List<&2, U32>) -> {L.fdt.nonul(xs) == L.fdt.nonul.fast(xs) : Bool}:
  nngo(xs, True{})

def slok(+ss: List<&2, B.Octets>, +b: Bool) -> {Bool.and(b, P.pr.strings_ok.ref(ss)) == P.pr.sl.ok(ss, b) : Bool}:
  match ss:
    case Nil{}:
      and_true(b)
    case Con{s, t}:
      %nonul_fast(B.Octets.to_list(s)) : {Bool.and(b, Bool.and(L.fdt.nonul(B.Octets.to_list(s)), P.pr.strings_ok.ref(t))) == P.pr.sl.ok(t, Bool.and(b, _)) : Bool}
      %slok(t, Bool.and(b, L.fdt.nonul(B.Octets.to_list(s)))) : {Bool.and(b, Bool.and(L.fdt.nonul(B.Octets.to_list(s)), P.pr.strings_ok.ref(t))) == _ : Bool}
      Equal.sym(Bool, Bool.and(Bool.and(b, L.fdt.nonul(B.Octets.to_list(s))), P.pr.strings_ok.ref(t)), Bool.and(b, Bool.and(L.fdt.nonul(B.Octets.to_list(s)), P.pr.strings_ok.ref(t))), and_assoc(b, L.fdt.nonul(B.Octets.to_list(s)), P.pr.strings_ok.ref(t)))

def strings_ok_fast(+ss: List<&2, B.Octets>) -> {P.pr.strings_ok.ref(ss) == P.FdtProp.strings_ok(ss) : Bool}:
  slok(ss, True{})

def slout(+ss: List<&2, B.Octets>, +acc: List<&2, U32>) -> {List.reverse.go(&2, U32, P.pr.sl.list(ss), acc) == P.pr.sl.out(ss, acc) : List<&2, U32>}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, t}:
      %grev_app(U32, B.Octets.to_list(s), Con{0, P.pr.sl.list(t)}, acc) : {_ == P.pr.sl.out(t, Con{0, List.reverse.go(&2, U32, B.Octets.to_list(s), acc)}) : List<&2, U32>}
      slout(t, Con{0, List.reverse.go(&2, U32, B.Octets.to_list(s), acc)})

def sl_fast(+ss: List<&2, B.Octets>) -> {P.pr.sl.list(ss) == P.pr.sl.fast(ss) : List<&2, U32>}:
  %slout(ss, Nil{}) : {P.pr.sl.list(ss) == List.reverse(&2, U32, _) : List<&2, U32>}
  revrev(U32, P.pr.sl.list(ss))

def cout(+cs: List<&2, U32>, +acc: List<&2, U32>) -> {List.reverse.go(&2, U32, P.pr.cells.list(cs), acc) == P.pr.cells.out(cs, acc) : List<&2, U32>}:
  match cs:
    case Nil{}:
      {==}
    case Con{c, t}:
      %grev_app(U32, B.be32(c), P.pr.cells.list(t), acc) : {_ == P.pr.cells.out(t, List.reverse.go(&2, U32, B.be32(c), acc)) : List<&2, U32>}
      cout(t, List.reverse.go(&2, U32, B.be32(c), acc))

def cells_fast(+cs: List<&2, U32>) -> {P.pr.cells.list(cs) == P.pr.cells.fast(cs) : List<&2, U32>}:
  %cout(cs, Nil{}) : {P.pr.cells.list(cs) == List.reverse(&2, U32, _) : List<&2, U32>}
  revrev(U32, P.pr.cells.list(cs))

# Sizes: a length below 2^32 survives its 32-bit field. fdt.nbits writes n's
# bits from the bottom (its parity, then half of it); reading them back
# rebuilds n once its high part is zero.

def rec(+b: Bool, +h: Nat) -> Nat:
  match b:
    case False{}:
      Nat.double(h)
    case True{}:
      1n+Nat.double(h)

def tn_con(+p: Nat, +b: Bool, +t: Word(p)) -> {rec(b, Word.to_nat(p, t)) == Word.to_nat(1n+p, WCon{b, t}) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def rc_succ(+b: Bool, +h: Nat) -> {1n+1n+rec(b, h) == rec(b, 1n+h) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def decomp(+n: Nat) -> {n == rec(L.fdt.odd(n), L.fdt.half(n)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          %rc_succ(L.fdt.odd(q), L.fdt.half(q)) : {1n+1n+q == _ : Nat}
          %decomp(q) : {1n+1n+q == 1n+1n+_ : Nat}
          {==}

def bits_rt(+k: Nat, +n: Nat, +e: {L.fdt.high(k, n) == 0n : Nat}) -> {n == Word.to_nat(k, L.fdt.nbits(k, n)) : Nat}:
  match k:
    case 0n:
      e
    case 1n+p:
      %tn_con(p, L.fdt.odd(n), L.fdt.nbits(p, L.fdt.half(n))) : {n == _ : Nat}
      %bits_rt(p, L.fdt.half(n), e) : {n == rec(L.fdt.odd(n), _) : Nat}
      decomp(n)

def size_rt(+n: Nat, +e: {L.fdt.over(n) == 0n : Nat}) -> {n == U32.to_nat(L.fdt.u32n(n)) : Nat}:
  bits_rt(32n, n, e)

# halving keeps order, so a number at most a fitting one fits

def half_mono(+n: Nat, +m: Nat, +e: {0n == Nat.sub(n, m) : Nat}) -> {0n == Nat.sub(L.fdt.half(n), L.fdt.half(m)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+n1:
      match n1:
        case 0n:
          {==}
        case 1n+n2:
          match m:
            case 0n:
              Empty.absurd({0n == Nat.sub(L.fdt.half(1n+1n+n2), 0n) : Nat}, nz_absurd(1n+n2, e))
            case 1n+m1:
              match m1:
                case 0n:
                  Empty.absurd({0n == Nat.sub(L.fdt.half(1n+1n+n2), 0n) : Nat}, nz_absurd(n2, e))
                case 1n+m2:
                  half_mono(n2, m2, e)

def high_mono(+k: Nat, +n: Nat, +m: Nat, +e1: {L.fdt.high(k, m) == 0n : Nat}, +e2: {0n == Nat.sub(n, m) : Nat}) -> {L.fdt.high(k, n) == 0n : Nat}:
  match k:
    case 0n:
      %sub_zero(n) : {_ == 0n : Nat}
      %e1 : {Nat.sub(n, _) == 0n : Nat}
      Equal.sym(Nat, 0n, Nat.sub(n, m), e2)
    case 1n+p:
      high_mono(p, L.fdt.half(n), L.fdt.half(m), e1, half_mono(n, m, e2))

def fits_le(+n: Nat, +m: Nat, +e1: {L.fdt.over(m) == 0n : Nat}, +e2: {0n == Nat.sub(n, m) : Nat}) -> {L.fdt.over(n) == 0n : Nat}:
  high_mono(32n, n, m, e1, e2)

# Masking: lists that hold bytes already are unchanged by B.mask

def mask_app(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.append(B.mask(a), B.mask(b)) == B.mask(B.append(a, b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %mask_app(t, b) : {Con{B.byte(h), B.append(B.mask(t), B.mask(b))} == Con{B.byte(h), _} : List<&2, U32>}
      {==}

def mask_id_app(+a: List<&2, U32>, +b: List<&2, U32>, +ea: {a == B.mask(a) : List<&2, U32>}, +eb: {b == B.mask(b) : List<&2, U32>}) -> {B.append(a, b) == B.mask(B.append(a, b)) : List<&2, U32>}:
  %mask_app(a, b) : {B.append(a, b) == _ : List<&2, U32>}
  %ea : {B.append(a, b) == B.append(_, B.mask(b)) : List<&2, U32>}
  %eb : {B.append(a, b) == B.append(a, _) : List<&2, U32>}
  {==}

def mask_be32(+x: U32) -> {B.be32(x) == B.mask(B.be32(x)) : List<&2, U32>}:
  match x:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, WCon{x8, WCon{x9, WCon{x10, WCon{x11, WCon{x12, WCon{x13, WCon{x14, WCon{x15, WCon{x16, WCon{x17, WCon{x18, WCon{x19, WCon{x20, WCon{x21, WCon{x22, WCon{x23, WCon{x24, WCon{x25, WCon{x26, WCon{x27, WCon{x28, WCon{x29, WCon{x30, WCon{x31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def mask_zeros(+n: Nat) -> {B.zeros(n) == B.mask(B.zeros(n)) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %mask_zeros(p) : {Con{0, B.zeros(p)} == Con{0, _} : List<&2, U32>}
      {==}

def mask_cz(+n: Nat) -> {Con{0, B.zeros(n)} == B.mask(Con{0, B.zeros(n)}) : List<&2, U32>}:
  mask_zeros(1n+n)

def mask_tl(+o: B.Octets) -> {B.Octets.to_list(o) == B.mask(B.Octets.to_list(o)) : List<&2, U32>}:
  %BL.octets_to_of(B.Octets.to_list(o)) : {B.Octets.to_list(o) == _ : List<&2, U32>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)) : {B.Octets.to_list(o) == B.Octets.to_list(_) : List<&2, U32>}
  {==}

# The header: with every field split into its bits, decoding computes

def hdr_rt(+h: H.FdtHeader) -> {H.hdr.decode.pub(H.hdr.decode(B.mask(H.hdr.list(h)))) == Done{h} : Result<&2, &2, E.FdtError, H.FdtHeader>}:
  match h:
    case H.FdtHeader{U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WCon{d8, WCon{d9, WCon{d10, WCon{d11, WCon{d12, WCon{d13, WCon{d14, WCon{d15, WCon{d16, WCon{d17, WCon{d18, WCon{d19, WCon{d20, WCon{d21, WCon{d22, WCon{d23, WCon{d24, WCon{d25, WCon{d26, WCon{d27, WCon{d28, WCon{d29, WCon{d30, WCon{d31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{e0, WCon{e1, WCon{e2, WCon{e3, WCon{e4, WCon{e5, WCon{e6, WCon{e7, WCon{e8, WCon{e9, WCon{e10, WCon{e11, WCon{e12, WCon{e13, WCon{e14, WCon{e15, WCon{e16, WCon{e17, WCon{e18, WCon{e19, WCon{e20, WCon{e21, WCon{e22, WCon{e23, WCon{e24, WCon{e25, WCon{e26, WCon{e27, WCon{e28, WCon{e29, WCon{e30, WCon{e31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{f0, WCon{f1, WCon{f2, WCon{f3, WCon{f4, WCon{f5, WCon{f6, WCon{f7, WCon{f8, WCon{f9, WCon{f10, WCon{f11, WCon{f12, WCon{f13, WCon{f14, WCon{f15, WCon{f16, WCon{f17, WCon{f18, WCon{f19, WCon{f20, WCon{f21, WCon{f22, WCon{f23, WCon{f24, WCon{f25, WCon{f26, WCon{f27, WCon{f28, WCon{f29, WCon{f30, WCon{f31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{g0, WCon{g1, WCon{g2, WCon{g3, WCon{g4, WCon{g5, WCon{g6, WCon{g7, WCon{g8, WCon{g9, WCon{g10, WCon{g11, WCon{g12, WCon{g13, WCon{g14, WCon{g15, WCon{g16, WCon{g17, WCon{g18, WCon{g19, WCon{g20, WCon{g21, WCon{g22, WCon{g23, WCon{g24, WCon{g25, WCon{g26, WCon{g27, WCon{g28, WCon{g29, WCon{g30, WCon{g31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{i0, WCon{i1, WCon{i2, WCon{i3, WCon{i4, WCon{i5, WCon{i6, WCon{i7, WCon{i8, WCon{i9, WCon{i10, WCon{i11, WCon{i12, WCon{i13, WCon{i14, WCon{i15, WCon{i16, WCon{i17, WCon{i18, WCon{i19, WCon{i20, WCon{i21, WCon{i22, WCon{i23, WCon{i24, WCon{i25, WCon{i26, WCon{i27, WCon{i28, WCon{i29, WCon{i30, WCon{i31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{j0, WCon{j1, WCon{j2, WCon{j3, WCon{j4, WCon{j5, WCon{j6, WCon{j7, WCon{j8, WCon{j9, WCon{j10, WCon{j11, WCon{j12, WCon{j13, WCon{j14, WCon{j15, WCon{j16, WCon{j17, WCon{j18, WCon{j19, WCon{j20, WCon{j21, WCon{j22, WCon{j23, WCon{j24, WCon{j25, WCon{j26, WCon{j27, WCon{j28, WCon{j29, WCon{j30, WCon{j31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{k0, WCon{k1, WCon{k2, WCon{k3, WCon{k4, WCon{k5, WCon{k6, WCon{k7, WCon{k8, WCon{k9, WCon{k10, WCon{k11, WCon{k12, WCon{k13, WCon{k14, WCon{k15, WCon{k16, WCon{k17, WCon{k18, WCon{k19, WCon{k20, WCon{k21, WCon{k22, WCon{k23, WCon{k24, WCon{k25, WCon{k26, WCon{k27, WCon{k28, WCon{k29, WCon{k30, WCon{k31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.header_round_trip(h):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(H.hdr.list(h))), B.mask(H.hdr.list(h)), BL.octets_to_of(H.hdr.list(h))) : {H.hdr.decode.pub(H.hdr.decode(_)) == Done{h} : Result<&2, &2, E.FdtError, H.FdtHeader>}
  hdr_rt(h)

def rd_magic(+m: U32, +r: List<&2, U32>) -> {Some{m} == B.be32_at(B.append(B.mask(B.be32(m)), r), 0n) : Maybe<&2, U32>}:
  match m:
    case U32{WCon{m0, WCon{m1, WCon{m2, WCon{m3, WCon{m4, WCon{m5, WCon{m6, WCon{m7, WCon{m8, WCon{m9, WCon{m10, WCon{m11, WCon{m12, WCon{m13, WCon{m14, WCon{m15, WCon{m16, WCon{m17, WCon{m18, WCon{m19, WCon{m20, WCon{m21, WCon{m22, WCon{m23, WCon{m24, WCon{m25, WCon{m26, WCon{m27, WCon{m28, WCon{m29, WCon{m30, WCon{m31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.bad_magic(opts, m, ne, rest):
  %parse_fast(opts, B.Octets.to_list(B.Octets.append(B.Octets.be32(m), rest))) : {_ == Fail{E.FdtBadMagic{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.be32(m), rest)), B.append(B.Octets.to_list(B.Octets.be32(m)), B.Octets.to_list(rest)), BL.octets_append_list(B.Octets.be32(m), rest)) : {F.parse.p1(opts, _) == Fail{E.FdtBadMagic{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.be32(m))), B.mask(B.be32(m)), BL.octets_to_of(B.be32(m))) : {F.parse.p1(opts, B.append(_, B.Octets.to_list(rest))) == Fail{E.FdtBadMagic{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
  %rd_magic(m, B.Octets.to_list(rest)) : {F.parse.p2(_, opts, B.append(B.mask(B.be32(m)), B.Octets.to_list(rest))) == Fail{E.FdtBadMagic{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
  %Equal.sym(Bool, U32.is_eq(m, H.FdtHeader.magic_value()), False{}, ne) : {F.parse.p3(_, opts, B.append(B.mask(B.be32(m)), B.Octets.to_list(rest))) == Fail{E.FdtBadMagic{}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
  {==}

# Property values

def len4(+x: U32) -> {True{} == Nat.is_eq(B.len(B.mask(B.be32(x))), 4n) : Bool}:
  match x:
    case U32{w}:
      {==}

def Laws.u32_round_trip(v):
  %Equal.sym(Nat, B.Octets.len(B.Octets.be32(v)), B.len(B.Octets.to_list(B.Octets.be32(v))), BL.octets_len_list(B.Octets.be32(v))) : {P.pr.u32.pick(Nat.is_eq(_, 4n), B.Octets.be32(v)) == Done{v} : Result<&2, &2, E.FdtError, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.be32(v))), B.mask(B.be32(v)), BL.octets_to_of(B.be32(v))) : {P.pr.u32.pick(Nat.is_eq(B.len(_), 4n), B.Octets.be32(v)) == Done{v} : Result<&2, &2, E.FdtError, U32>}
  %len4(v) : {P.pr.u32.pick(_, B.Octets.be32(v)) == Done{v} : Result<&2, &2, E.FdtError, U32>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.be32(v), 0n), Some{v}, BL.octets_be32_round_trip(v)) : {P.pr.must32(_) == Done{v} : Result<&2, &2, E.FdtError, U32>}
  {==}

def len8(+x: U32, +y: U32) -> {True{} == Nat.is_eq(B.len(B.mask(B.append(B.be32(x), B.be32(y)))), 8n) : Bool}:
  match x y:
    case U32{a} U32{b}:
      {==}

def Laws.u64_round_trip(v):
  %Equal.sym(Nat, B.Octets.len(B.Octets.be64(v)), B.len(B.Octets.to_list(B.Octets.be64(v))), BL.octets_len_list(B.Octets.be64(v))) : {P.pr.u64.pick(Nat.is_eq(_, 8n), B.Octets.be64(v)) == Done{v} : Result<&2, &2, E.FdtError, W.W64>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.be64(v))), B.mask(B.be64(v)), BL.octets_to_of(B.be64(v))) : {P.pr.u64.pick(Nat.is_eq(B.len(_), 8n), B.Octets.be64(v)) == Done{v} : Result<&2, &2, E.FdtError, W.W64>}
  %len8(W.W64.hi(v), W.W64.lo(v)) : {P.pr.u64.pick(_, B.Octets.be64(v)) == Done{v} : Result<&2, &2, E.FdtError, W.W64>}
  %Equal.sym(Maybe<&2, W.W64>, B.Octets.be64_at(B.Octets.be64(v), 0n), Some{v}, BL.octets_be64_round_trip(v)) : {P.pr.must64(_) == Done{v} : Result<&2, &2, E.FdtError, W.W64>}
  {==}

# a string without NULs, then a NUL and the rest, scans as itself and the rest
def scan_rt(+xs: List<&2, U32>, +rest: List<&2, U32>, +acc: List<&2, U32>, +ok: {L.fdt.nonul(xs) == True{} : Bool}) -> {Some{L.FdtCut{List.reverse(&2, U32, List.reverse.go(&2, U32, xs, acc)), rest}} == L.fdt.scan.go(B.append(xs, Con{0, rest}), L.FdtScanning{acc}) : Maybe<&2, L.FdtCut>}:
  match xs:
    case Nil{}:
      match rest:
        case Nil{}:
          {==}
        case Con{h, t}:
          {==}
    case Con{h, t}:
      %Equal.sym(Bool, U32.is_eq(h, 0), False{}, not_t(U32.is_eq(h, 0), and_l(Bool.not(U32.is_eq(h, 0)), L.fdt.nonul(t), ok))) : {Some{L.FdtCut{List.reverse(&2, U32, List.reverse.go(&2, U32, t, Con{h, acc})), rest}} == L.fdt.scan.go(B.append(t, Con{0, rest}), L.fdt.scan.pick(_, acc, h)) : Maybe<&2, L.FdtCut>}
      scan_rt(t, rest, Con{h, acc}, and_r(Bool.not(U32.is_eq(h, 0)), L.fdt.nonul(t), ok))

def Laws.string_round_trip(s, ok):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(s, B.Octets.zeros(1n))), B.append(B.Octets.to_list(s), B.Octets.to_list(B.Octets.zeros(1n))), BL.octets_append_list(s, B.Octets.zeros(1n))) : {P.pr.str(L.fdt.cstr(_)) == Done{s} : Result<&2, &2, E.FdtError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.zeros(1n)), B.zeros(1n), BL.octets_zeros_list(1n)) : {P.pr.str(L.fdt.cstr(B.append(B.Octets.to_list(s), _))) == Done{s} : Result<&2, &2, E.FdtError, B.Octets>}
  %scan_rt(B.Octets.to_list(s), Nil{}, Nil{}, Equal.trans(Bool, L.fdt.nonul(B.Octets.to_list(s)), P.FdtProp.string_ok(s), True{}, nonul_fast(B.Octets.to_list(s)), ok)) : {P.pr.str(_) == Done{s} : Result<&2, &2, E.FdtError, B.Octets>}
  %revrev(U32, B.Octets.to_list(s)) : {Done{B.Octets.of_list(_)} == Done{s} : Result<&2, &2, E.FdtError, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(s)), s, BL.octets_of_to(s)) : {Done{_} == Done{s} : Result<&2, &2, E.FdtError, B.Octets>}
  {==}

# The reservation block

# after the terminator, nothing more is read
def rsv_stop(+xs: List<&2, U32>, +acc: List<&2, R.FdtRsv>) -> {Done{List.reverse(&2, R.FdtRsv, acc)} == R.rsv.go(xs, True{}, acc) : Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h0, t0}:
      match t0:
        case Nil{}:
          {==}
        case Con{h1, t1}:
          match t1:
            case Nil{}:
              {==}
            case Con{h2, t2}:
              match t2:
                case Nil{}:
                  {==}
                case Con{h3, t3}:
                  match t3:
                    case Nil{}:
                      {==}
                    case Con{h4, t4}:
                      match t4:
                        case Nil{}:
                          {==}
                        case Con{h5, t5}:
                          match t5:
                            case Nil{}:
                              {==}
                            case Con{h6, t6}:
                              match t6:
                                case Nil{}:
                                  {==}
                                case Con{h7, t7}:
                                  match t7:
                                    case Nil{}:
                                      {==}
                                    case Con{h8, t8}:
                                      match t8:
                                        case Nil{}:
                                          {==}
                                        case Con{h9, t9}:
                                          match t9:
                                            case Nil{}:
                                              {==}
                                            case Con{h10, t10}:
                                              match t10:
                                                case Nil{}:
                                                  {==}
                                                case Con{h11, t11}:
                                                  match t11:
                                                    case Nil{}:
                                                      {==}
                                                    case Con{h12, t12}:
                                                      match t12:
                                                        case Nil{}:
                                                          {==}
                                                        case Con{h13, t13}:
                                                          match t13:
                                                            case Nil{}:
                                                              {==}
                                                            case Con{h14, t14}:
                                                              match t14:
                                                                case Nil{}:
                                                                  {==}
                                                                case Con{h15, t15}:
                                                                  {==}

# one entry, its four 32-bit halves split into bits
def rsv_ent32(+h1: U32, +l1: U32, +h2: U32, +l2: U32, +x: List<&2, U32>, +acc: List<&2, R.FdtRsv>) -> {R.rsv.go(x, R.FdtRsv.is_end(R.FdtRsv{W.W64.from_parts(h1, l1), W.W64.from_parts(h2, l2)}), R.rsv.push(R.FdtRsv.is_end(R.FdtRsv{W.W64.from_parts(h1, l1), W.W64.from_parts(h2, l2)}), R.FdtRsv{W.W64.from_parts(h1, l1), W.W64.from_parts(h2, l2)}, acc)) == R.rsv.go(B.append(B.append(B.append(B.be32(h1), B.be32(l1)), B.append(B.be32(h2), B.be32(l2))), x), False{}, acc) : Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>}:
  match h1 l1 h2 l2:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WCon{d8, WCon{d9, WCon{d10, WCon{d11, WCon{d12, WCon{d13, WCon{d14, WCon{d15, WCon{d16, WCon{d17, WCon{d18, WCon{d19, WCon{d20, WCon{d21, WCon{d22, WCon{d23, WCon{d24, WCon{d25, WCon{d26, WCon{d27, WCon{d28, WCon{d29, WCon{d30, WCon{d31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# one entry: a word is its two halves joined (word64's parts_of)
def rsv_ent(+a: W.W64, +s: W.W64, +x: List<&2, U32>, +acc: List<&2, R.FdtRsv>) -> {R.rsv.go(x, R.FdtRsv.is_end(R.FdtRsv{a, s}), R.rsv.push(R.FdtRsv.is_end(R.FdtRsv{a, s}), R.FdtRsv{a, s}, acc)) == R.rsv.go(B.append(R.rsv.entry(R.FdtRsv{a, s}), x), False{}, acc) : Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>}:
  %WL.parts_of(a) : {R.rsv.go(x, R.FdtRsv.is_end(R.FdtRsv{_, s}), R.rsv.push(R.FdtRsv.is_end(R.FdtRsv{_, s}), R.FdtRsv{_, s}, acc)) == R.rsv.go(B.append(R.rsv.entry(R.FdtRsv{a, s}), x), False{}, acc) : Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>}
  %WL.parts_of(s) : {R.rsv.go(x, R.FdtRsv.is_end(R.FdtRsv{W.W64.from_parts(W.W64.hi(a), W.W64.lo(a)), _}), R.rsv.push(R.FdtRsv.is_end(R.FdtRsv{W.W64.from_parts(W.W64.hi(a), W.W64.lo(a)), _}), R.FdtRsv{W.W64.from_parts(W.W64.hi(a), W.W64.lo(a)), _}, acc)) == R.rsv.go(B.append(R.rsv.entry(R.FdtRsv{a, s}), x), False{}, acc) : Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>}
  rsv_ent32(W.W64.hi(a), W.W64.lo(a), W.W64.hi(s), W.W64.lo(s), x, acc)

def rsv_rt(+rs: List<&2, R.FdtRsv>, +x: List<&2, U32>, +acc: List<&2, R.FdtRsv>, +ok: {R.FdtRsv.valid_all(rs) == True{} : Bool}) -> {Done{List.reverse(&2, R.FdtRsv, List.reverse.go(&2, R.FdtRsv, rs, acc))} == R.rsv.go(B.append(R.rsv.list(rs), x), False{}, acc) : Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>}:
  match rs:
    case Nil{}:
      rsv_stop(x, acc)
    case Con{r, t}:
      match r:
        case R.FdtRsv{a, s}:
          %app_assoc(R.rsv.entry(R.FdtRsv{a, s}), R.rsv.list(t), x) : {Done{List.reverse(&2, R.FdtRsv, List.reverse.go(&2, R.FdtRsv, Con{R.FdtRsv{a, s}, t}, acc))} == R.rsv.go(_, False{}, acc) : Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>}
          %rsv_ent(a, s, B.append(R.rsv.list(t), x), acc) : {Done{List.reverse(&2, R.FdtRsv, List.reverse.go(&2, R.FdtRsv, Con{R.FdtRsv{a, s}, t}, acc))} == _ : Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>}
          %Equal.sym(Bool, R.FdtRsv.is_end(R.FdtRsv{a, s}), False{}, not_t(R.FdtRsv.is_end(R.FdtRsv{a, s}), and_l(Bool.not(R.FdtRsv.is_end(R.FdtRsv{a, s})), R.FdtRsv.valid_all(t), ok))) : {Done{List.reverse(&2, R.FdtRsv, List.reverse.go(&2, R.FdtRsv, Con{R.FdtRsv{a, s}, t}, acc))} == R.rsv.go(B.append(R.rsv.list(t), x), _, R.rsv.push(_, R.FdtRsv{a, s}, acc)) : Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>}
          rsv_rt(t, x, Con{R.FdtRsv{a, s}, acc}, and_r(Bool.not(R.FdtRsv.is_end(R.FdtRsv{a, s})), R.FdtRsv.valid_all(t), ok))

def mask_rsv(+rs: List<&2, R.FdtRsv>) -> {R.rsv.list(rs) == B.mask(R.rsv.list(rs)) : List<&2, U32>}:
  match rs:
    case Nil{}:
      mask_zeros(16n)
    case Con{r, t}:
      match r:
        case R.FdtRsv{a, s}:
          mask_id_app(R.rsv.entry(R.FdtRsv{a, s}), R.rsv.list(t), mask_id_app(B.be64(a), B.be64(s), mask_id_app(B.be32(W.W64.hi(a)), B.be32(W.W64.lo(a)), mask_be32(W.W64.hi(a)), mask_be32(W.W64.lo(a))), mask_id_app(B.be32(W.W64.hi(s)), B.be32(W.W64.lo(s)), mask_be32(W.W64.hi(s)), mask_be32(W.W64.lo(s)))), mask_rsv(t))

def Laws.rsv_round_trip(rs, ok):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(R.rsv.list(rs))), B.mask(R.rsv.list(rs)), BL.octets_to_of(R.rsv.list(rs))) : {R.rsv.go(_, False{}, Nil{}) == Done{rs} : Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>}
  %mask_rsv(rs) : {R.rsv.go(_, False{}, Nil{}) == Done{rs} : Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>}
  %app_nil(R.rsv.list(rs)) : {R.rsv.go(_, False{}, Nil{}) == Done{rs} : Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>}
  %rsv_rt(rs, Nil{}, Nil{}, ok) : {_ == Done{rs} : Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>}
  %revrev(R.FdtRsv, rs) : {Done{_} == Done{rs} : Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>}
  {==}

# The lexer: a fold over the bytes

def go_app(+xs: List<&2, U32>, +ys: List<&2, U32>, +st: S.FdtLexer) -> {S.lx.go(ys, S.lx.go(xs, st)) == S.lx.go(B.append(xs, ys), st) : S.FdtLexer}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      go_app(t, ys, S.lx.step(st, h))

def Laws.lexer_streaming(st, a, b):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {S.lx.go(B.Octets.to_list(b), S.lx.go(B.Octets.to_list(a), st)) == S.lx.go(_, st) : S.FdtLexer}
  go_app(B.Octets.to_list(a), B.Octets.to_list(b), st)

# Tokens, one at a time

def lx_pad(+p: Nat, +toks: List<&2, S.FdtToken>) -> {S.FdtLexer{S.lx.tagword(), toks} == S.lx.go(B.zeros(p), S.FdtLexer{S.lx.padded(p), toks}) : S.FdtLexer}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      lx_pad(q, toks)

def lx_name(+nb: List<&2, U32>, +z: List<&2, U32>, +acc: List<&2, U32>, +toks: List<&2, S.FdtToken>, +ok: {L.fdt.nonul(nb) == True{} : Bool}) -> {S.lx.go(z, S.lx.name_end(List.reverse(&2, U32, List.reverse.go(&2, U32, nb, acc)), toks)) == S.lx.go(B.append(nb, Con{0, z}), S.FdtLexer{S.LxName{acc}, toks}) : S.FdtLexer}:
  match nb:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(Bool, U32.is_eq(h, 0), False{}, not_t(U32.is_eq(h, 0), and_l(Bool.not(U32.is_eq(h, 0)), L.fdt.nonul(t), ok))) : {S.lx.go(z, S.lx.name_end(List.reverse(&2, U32, List.reverse.go(&2, U32, t, Con{h, acc})), toks)) == S.lx.go(B.append(t, Con{0, z}), S.lx.name(_, h, acc, toks)) : S.FdtLexer}
      lx_name(t, z, Con{h, acc}, toks, and_r(Bool.not(U32.is_eq(h, 0)), L.fdt.nonul(t), ok))

def lx_begin(+nb: List<&2, U32>, +acc: List<&2, S.FdtToken>, +ok: {L.fdt.nonul(nb) == True{} : Bool}) -> {S.FdtLexer{S.lx.tagword(), Con{S.FdtTokBegin{B.Octets.of_list(nb)}, acc}} == S.lx.go(S.tok.begin(nb), S.FdtLexer{S.lx.tagword(), acc}) : S.FdtLexer}:
  %go_app(B.be32(1), B.append(nb, Con{0, B.zeros(L.fdt.pad4(1n+B.len(nb)))}), S.FdtLexer{S.lx.tagword(), acc}) : {S.FdtLexer{S.lx.tagword(), Con{S.FdtTokBegin{B.Octets.of_list(nb)}, acc}} == _ : S.FdtLexer}
  %lx_name(nb, B.zeros(L.fdt.pad4(1n+B.len(nb))), Nil{}, acc, ok) : {S.FdtLexer{S.lx.tagword(), Con{S.FdtTokBegin{B.Octets.of_list(nb)}, acc}} == _ : S.FdtLexer}
  %revrev(U32, nb) : {S.FdtLexer{S.lx.tagword(), Con{S.FdtTokBegin{B.Octets.of_list(nb)}, acc}} == S.lx.go(B.zeros(L.fdt.pad4(1n+B.len(nb))), S.lx.name_end(_, acc)) : S.FdtLexer}
  %BL.len_fast(nb) : {S.FdtLexer{S.lx.tagword(), Con{S.FdtTokBegin{B.Octets.of_list(nb)}, acc}} == S.lx.go(B.zeros(L.fdt.pad4(1n+B.len(nb))), S.FdtLexer{S.lx.padded(L.fdt.pad4(1n+_)), Con{S.FdtTokBegin{B.Octets.of_list(nb)}, acc}}) : S.FdtLexer}
  lx_pad(L.fdt.pad4(1n+B.len(nb)), Con{S.FdtTokBegin{B.Octets.of_list(nb)}, acc})

def lx_len(+n: Nat, +acc: List<&2, S.FdtToken>, +e: {L.fdt.over(n) == 0n : Nat}) -> {S.FdtLexer{S.LxWord{S.LxOff{n}, Nil{}}, acc} == S.lx.go(B.be32(L.fdt.u32n(n)), S.FdtLexer{S.LxWord{S.LxLen{}, Nil{}}, acc}) : S.FdtLexer}:
  %size_rt(n, e) : {S.FdtLexer{S.LxWord{S.LxOff{n}, Nil{}}, acc} == S.FdtLexer{S.LxWord{S.LxOff{_}, Nil{}}, acc} : S.FdtLexer}
  {==}

def lx_off(+o: U32, +n: Nat, +acc: List<&2, S.FdtToken>) -> {S.lx.value_start(n, o, acc) == S.lx.go(B.be32(o), S.FdtLexer{S.LxWord{S.LxOff{n}, Nil{}}, acc}) : S.FdtLexer}:
  match o:
    case U32{WCon{o0, WCon{o1, WCon{o2, WCon{o3, WCon{o4, WCon{o5, WCon{o6, WCon{o7, WCon{o8, WCon{o9, WCon{o10, WCon{o11, WCon{o12, WCon{o13, WCon{o14, WCon{o15, WCon{o16, WCon{o17, WCon{o18, WCon{o19, WCon{o20, WCon{o21, WCon{o22, WCon{o23, WCon{o24, WCon{o25, WCon{o26, WCon{o27, WCon{o28, WCon{o29, WCon{o30, WCon{o31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def lx_val(+t: List<&2, U32>, +h: U32, +z: List<&2, U32>, +off: U32, +total: Nat, +acc: List<&2, U32>, +toks: List<&2, S.FdtToken>) -> {S.lx.go(z, S.FdtLexer{S.lx.padded(L.fdt.pad4(total)), Con{S.FdtTokProp{off, B.Octets.of_list(List.reverse(&2, U32, List.reverse.go(&2, U32, Con{h, t}, acc)))}, toks}}) == S.lx.go(B.append(Con{h, t}, z), S.FdtLexer{S.LxValue{off, B.len(Con{h, t}), total, acc}, toks}) : S.FdtLexer}:
  match t:
    case Nil{}:
      {==}
    case Con{h2, t2}:
      lx_val(t2, h2, z, off, total, Con{h, acc}, toks)

def lx_prop_tail(+vb: List<&2, U32>, +off: U32, +acc: List<&2, S.FdtToken>) -> {S.FdtLexer{S.lx.tagword(), Con{S.FdtTokProp{off, B.Octets.of_list(vb)}, acc}} == S.lx.go(B.append(vb, B.zeros(L.fdt.pad4(B.len(vb)))), S.lx.value_start(B.len(vb), off, acc)) : S.FdtLexer}:
  match vb:
    case Nil{}:
      {==}
    case Con{h, t}:
      %lx_val(t, h, B.zeros(L.fdt.pad4(B.len(Con{h, t}))), off, B.len(Con{h, t}), Nil{}, acc) : {S.FdtLexer{S.lx.tagword(), Con{S.FdtTokProp{off, B.Octets.of_list(Con{h, t})}, acc}} == _ : S.FdtLexer}
      %revrev(U32, Con{h, t}) : {S.FdtLexer{S.lx.tagword(), Con{S.FdtTokProp{off, B.Octets.of_list(Con{h, t})}, acc}} == S.lx.go(B.zeros(L.fdt.pad4(B.len(Con{h, t}))), S.FdtLexer{S.lx.padded(L.fdt.pad4(B.len(Con{h, t}))), Con{S.FdtTokProp{off, B.Octets.of_list(_)}, acc}}) : S.FdtLexer}
      lx_pad(L.fdt.pad4(B.len(Con{h, t})), Con{S.FdtTokProp{off, B.Octets.of_list(Con{h, t})}, acc})

def lx_prop(+off: U32, +vb: List<&2, U32>, +acc: List<&2, S.FdtToken>, +e: {L.fdt.over(B.len(vb)) == 0n : Nat}) -> {S.FdtLexer{S.lx.tagword(), Con{S.FdtTokProp{off, B.Octets.of_list(vb)}, acc}} == S.lx.go(S.tok.prop(off, vb), S.FdtLexer{S.lx.tagword(), acc}) : S.FdtLexer}:
  %go_app(B.be32(3), B.append(B.be32(L.fdt.u32n(B.len(vb))), B.append(B.be32(off), B.append(vb, B.zeros(L.fdt.pad4(B.len(vb)))))), S.FdtLexer{S.lx.tagword(), acc}) : {S.FdtLexer{S.lx.tagword(), Con{S.FdtTokProp{off, B.Octets.of_list(vb)}, acc}} == _ : S.FdtLexer}
  %go_app(B.be32(L.fdt.u32n(B.len(vb))), B.append(B.be32(off), B.append(vb, B.zeros(L.fdt.pad4(B.len(vb))))), S.FdtLexer{S.LxWord{S.LxLen{}, Nil{}}, acc}) : {S.FdtLexer{S.lx.tagword(), Con{S.FdtTokProp{off, B.Octets.of_list(vb)}, acc}} == _ : S.FdtLexer}
  %lx_len(B.len(vb), acc, e) : {S.FdtLexer{S.lx.tagword(), Con{S.FdtTokProp{off, B.Octets.of_list(vb)}, acc}} == S.lx.go(B.append(B.be32(off), B.append(vb, B.zeros(L.fdt.pad4(B.len(vb))))), _) : S.FdtLexer}
  %go_app(B.be32(off), B.append(vb, B.zeros(L.fdt.pad4(B.len(vb)))), S.FdtLexer{S.LxWord{S.LxOff{B.len(vb)}, Nil{}}, acc}) : {S.FdtLexer{S.lx.tagword(), Con{S.FdtTokProp{off, B.Octets.of_list(vb)}, acc}} == _ : S.FdtLexer}
  %lx_off(off, B.len(vb), acc) : {S.FdtLexer{S.lx.tagword(), Con{S.FdtTokProp{off, B.Octets.of_list(vb)}, acc}} == S.lx.go(B.append(vb, B.zeros(L.fdt.pad4(B.len(vb)))), _) : S.FdtLexer}
  lx_prop_tail(vb, off, acc)

def lx_tok(+t: S.FdtToken, +acc: List<&2, S.FdtToken>, +ok: {S.tok.valid.ref(t) == True{} : Bool}) -> {S.FdtLexer{S.lx.tagword(), Con{t, acc}} == S.lx.go(S.tok.list(t), S.FdtLexer{S.lx.tagword(), acc}) : S.FdtLexer}:
  match t:
    case S.FdtTokBegin{name}:
      %BL.octets_of_to(name) : {S.FdtLexer{S.lx.tagword(), Con{S.FdtTokBegin{_}, acc}} == S.lx.go(S.tok.list(S.FdtTokBegin{name}), S.FdtLexer{S.lx.tagword(), acc}) : S.FdtLexer}
      lx_begin(B.Octets.to_list(name), acc, ok)
    case S.FdtTokEnd{}:
      {==}
    case S.FdtTokProp{off, v}:
      %BL.octets_of_to(v) : {S.FdtLexer{S.lx.tagword(), Con{S.FdtTokProp{off, _}, acc}} == S.lx.go(S.tok.list(S.FdtTokProp{off, v}), S.FdtLexer{S.lx.tagword(), acc}) : S.FdtLexer}
      lx_prop(off, B.Octets.to_list(v), acc, zero_t(L.fdt.over(B.len(B.Octets.to_list(v))), ok))
    case S.FdtTokNop{}:
      {==}

def lx_toks(+ts: List<&2, S.FdtToken>, +acc: List<&2, S.FdtToken>, +ok: {S.tok.valid_all.ref(ts) == True{} : Bool}) -> {S.FdtLexer{S.LxEnd{False{}}, List.reverse.go(&2, S.FdtToken, ts, acc)} == S.lx.go(S.toks.list(ts), S.FdtLexer{S.lx.tagword(), acc}) : S.FdtLexer}:
  match ts:
    case Nil{}:
      {==}
    case Con{t, r}:
      %go_app(S.tok.list(t), S.toks.list(r), S.FdtLexer{S.lx.tagword(), acc}) : {S.FdtLexer{S.LxEnd{False{}}, List.reverse.go(&2, S.FdtToken, Con{t, r}, acc)} == _ : S.FdtLexer}
      %lx_tok(t, acc, and_l(S.tok.valid.ref(t), S.tok.valid_all.ref(r), ok)) : {S.FdtLexer{S.LxEnd{False{}}, List.reverse.go(&2, S.FdtToken, Con{t, r}, acc)} == S.lx.go(S.toks.list(r), _) : S.FdtLexer}
      lx_toks(r, Con{t, acc}, and_r(S.tok.valid.ref(t), S.tok.valid_all.ref(r), ok))

def mask_tok(+t: S.FdtToken) -> {S.tok.list(t) == B.mask(S.tok.list(t)) : List<&2, U32>}:
  match t:
    case S.FdtTokBegin{name}:
      mask_id_app(B.be32(1), B.append(B.Octets.to_list(name), Con{0, B.zeros(L.fdt.pad4(1n+B.len(B.Octets.to_list(name))))}), mask_be32(1), mask_id_app(B.Octets.to_list(name), Con{0, B.zeros(L.fdt.pad4(1n+B.len(B.Octets.to_list(name))))}, mask_tl(name), mask_cz(L.fdt.pad4(1n+B.len(B.Octets.to_list(name))))))
    case S.FdtTokEnd{}:
      {==}
    case S.FdtTokProp{off, v}:
      mask_id_app(B.be32(3), B.append(B.be32(L.fdt.u32n(B.len(B.Octets.to_list(v)))), B.append(B.be32(off), B.append(B.Octets.to_list(v), B.zeros(L.fdt.pad4(B.len(B.Octets.to_list(v))))))), mask_be32(3), mask_id_app(B.be32(L.fdt.u32n(B.len(B.Octets.to_list(v)))), B.append(B.be32(off), B.append(B.Octets.to_list(v), B.zeros(L.fdt.pad4(B.len(B.Octets.to_list(v)))))), mask_be32(L.fdt.u32n(B.len(B.Octets.to_list(v)))), mask_id_app(B.be32(off), B.append(B.Octets.to_list(v), B.zeros(L.fdt.pad4(B.len(B.Octets.to_list(v))))), mask_be32(off), mask_id_app(B.Octets.to_list(v), B.zeros(L.fdt.pad4(B.len(B.Octets.to_list(v)))), mask_tl(v), mask_zeros(L.fdt.pad4(B.len(B.Octets.to_list(v))))))))
    case S.FdtTokNop{}:
      {==}

def mask_toks(+ts: List<&2, S.FdtToken>) -> {S.toks.list(ts) == B.mask(S.toks.list(ts)) : List<&2, U32>}:
  match ts:
    case Nil{}:
      {==}
    case Con{t, r}:
      mask_id_app(S.tok.list(t), S.toks.list(r), mask_tok(t), mask_toks(r))

# the law for the reference encoder and check
def tokens_rt(+ts: List<&2, S.FdtToken>, +ok: {S.tok.valid_all.ref(ts) == True{} : Bool}) -> {S.FdtLexer.finish(True{}, S.lx.go(B.Octets.to_list(B.Octets.of_list(S.toks.list(ts))), S.FdtLexer.start())) == Done{ts} : Result<&2, &2, E.FdtError, List<&2, S.FdtToken>>}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(S.toks.list(ts))), B.mask(S.toks.list(ts)), BL.octets_to_of(S.toks.list(ts))) : {S.FdtLexer.finish(True{}, S.lx.go(_, S.FdtLexer.start())) == Done{ts} : Result<&2, &2, E.FdtError, List<&2, S.FdtToken>>}
  %mask_toks(ts) : {S.FdtLexer.finish(True{}, S.lx.go(_, S.FdtLexer.start())) == Done{ts} : Result<&2, &2, E.FdtError, List<&2, S.FdtToken>>}
  %lx_toks(ts, Nil{}, ok) : {S.FdtLexer.finish(True{}, _) == Done{ts} : Result<&2, &2, E.FdtError, List<&2, S.FdtToken>>}
  %revrev(S.FdtToken, ts) : {Done{_} == Done{ts} : Result<&2, &2, E.FdtError, List<&2, S.FdtToken>>}
  {==}

def Laws.tokens_round_trip(ts, ok):
  %toks_fast(ts) : {S.FdtLexer.finish(True{}, S.lx.go(B.Octets.to_list(B.Octets.of_list(_)), S.FdtLexer.start())) == Done{ts} : Result<&2, &2, E.FdtError, List<&2, S.FdtToken>>}
  tokens_rt(ts, Equal.trans(Bool, S.tok.valid_all.ref(ts), S.FdtToken.valid_all(ts), True{}, valid_all_fast(ts), ok))

# The tree builder: a fold over the tokens

def tb_go_app(+xs: List<&2, S.FdtToken>, +ys: List<&2, S.FdtToken>, +rules: T.FdtTreeRules, +strs: List<&2, U32>, +st: T.FdtTb) -> {T.tb.go(ys, rules, strs, T.tb.go(xs, rules, strs, st)) == T.tb.go(List.append(&2, S.FdtToken, xs, ys), rules, strs, st) : T.FdtTb}:
  match xs:
    case Nil{}:
      {==}
    case Con{t, r}:
      tb_go_app(r, ys, rules, strs, T.tb.step(rules, strs, st, t))

# a prefix of the strings block is at most its length
def le_via(+p: List<&2, U32>, +x: List<&2, U32>, +t: List<&2, U32>, +e: {B.append(p, x) == t : List<&2, U32>}) -> {0n == Nat.sub(B.len(p), B.len(t)) : Nat}:
  %e : {0n == Nat.sub(B.len(p), B.len(_)) : Nat}
  prefix_le(p, x)

def eq_tr(+p: List<&2, U32>, +x1: List<&2, U32>, +x2: List<&2, U32>, +t: List<&2, U32>, +e: {x2 == x1 : List<&2, U32>}, +et: {B.append(p, x2) == t : List<&2, U32>}) -> {B.append(p, x1) == t : List<&2, U32>}:
  %e : {B.append(p, _) == t : List<&2, U32>}
  et

def assoc3(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>, +q: List<&2, U32>) -> {B.append(a, B.append(b, B.append(c, q))) == B.append(B.append(a, B.append(b, c)), q) : List<&2, U32>}:
  %app_assoc(a, B.append(b, c), q) : {B.append(a, B.append(b, B.append(c, q))) == _ : List<&2, U32>}
  %app_assoc(b, c, q) : {B.append(a, B.append(b, B.append(c, q))) == B.append(a, _) : List<&2, U32>}
  {==}

# the strings block seen from the next property's name
def eq_prop(+p: List<&2, U32>, +kb: List<&2, U32>, +z: List<&2, U32>, +q: List<&2, U32>) -> {B.append(B.append(p, B.append(kb, [0])), B.append(z, q)) == B.append(p, B.append(B.append(kb, Con{0, z}), q)) : List<&2, U32>}:
  %app_assoc(p, B.append(kb, [0]), B.append(z, q)) : {_ == B.append(p, B.append(B.append(kb, Con{0, z}), q)) : List<&2, U32>}
  %app_assoc(kb, [0], B.append(z, q)) : {B.append(p, _) == B.append(p, B.append(B.append(kb, Con{0, z}), q)) : List<&2, U32>}
  %app_assoc(kb, Con{0, z}, q) : {B.append(p, B.append(kb, Con{0, B.append(z, q)})) == B.append(p, _) : List<&2, U32>}
  {==}

# the strings block seen from a node's properties, its children, the nodes after it
def et_props(+p: List<&2, U32>, +ps: List<&2, U32>, +cs: List<&2, U32>, +ts: List<&2, U32>, +q: List<&2, U32>, +strs: List<&2, U32>, +et: {B.append(p, B.append(B.append(ps, B.append(cs, ts)), q)) == strs : List<&2, U32>}) -> {B.append(p, B.append(ps, B.append(cs, B.append(ts, q)))) == strs : List<&2, U32>}:
  eq_tr(p, B.append(ps, B.append(cs, B.append(ts, q))), B.append(B.append(ps, B.append(cs, ts)), q), strs, Equal.sym(List<&2, U32>, B.append(ps, B.append(cs, B.append(ts, q))), B.append(B.append(ps, B.append(cs, ts)), q), assoc3(ps, cs, ts, q)), et)

def et_kids(+p: List<&2, U32>, +ps: List<&2, U32>, +y: List<&2, U32>, +strs: List<&2, U32>, +et: {B.append(p, B.append(ps, y)) == strs : List<&2, U32>}) -> {B.append(B.append(p, ps), y) == strs : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.append(B.append(p, ps), y), B.append(p, B.append(ps, y)), strs, Equal.sym(List<&2, U32>, B.append(p, B.append(ps, y)), B.append(B.append(p, ps), y), app_assoc(p, ps, y)), et)

def tb_props(+ps: List<&2, T.FdtProp>, +nop: Bool, +pf: Bool, +strs: List<&2, U32>, +p: List<&2, U32>, +q: List<&2, U32>, +nm: B.Octets, +pr: List<&2, T.FdtProp>, +s: List<&2, T.FdtFrame>, +et: {B.append(p, B.append(T.prop.strs(ps), q)) == strs : List<&2, U32>}, +ft: {L.fdt.over(B.len(strs)) == 0n : Nat}, +ok: {T.prop.names_ok(ps) == True{} : Bool}) -> {T.TbOpen{Con{T.FdtFrame{nm, List.reverse.go(&2, T.FdtProp, ps, pr), Nil{}}, s}} == T.tb.go(T.prop.toks(ps, B.len(p)), T.FdtTreeRules{nop, pf}, strs, T.TbOpen{Con{T.FdtFrame{nm, pr, Nil{}}, s}}) : T.FdtTb}:
  match ps:
    case Nil{}:
      {==}
    case Con{pp, t}:
      match pp:
        case T.FdtProp{k, v}:
          %size_rt(B.len(p), fits_le(B.len(p), B.len(strs), ft, le_via(p, B.append(T.prop.strs(Con{T.FdtProp{k, v}, t}), q), strs, et))) : {T.TbOpen{Con{T.FdtFrame{nm, List.reverse.go(&2, T.FdtProp, Con{T.FdtProp{k, v}, t}, pr), Nil{}}, s}} == T.tb.go(T.prop.toks(t, Nat.add(B.len(p), B.len(B.append(B.Octets.to_list(k), [0])))), T.FdtTreeRules{nop, pf}, strs, T.tb.prop.named(T.FdtFrame{nm, pr, Nil{}}, T.tb.name_at(strs, _), pf, v, s)) : T.FdtTb}
          %et : {T.TbOpen{Con{T.FdtFrame{nm, List.reverse.go(&2, T.FdtProp, Con{T.FdtProp{k, v}, t}, pr), Nil{}}, s}} == T.tb.go(T.prop.toks(t, Nat.add(B.len(p), B.len(B.append(B.Octets.to_list(k), [0])))), T.FdtTreeRules{nop, pf}, strs, T.tb.prop.named(T.FdtFrame{nm, pr, Nil{}}, L.fdt.cstr(B.drop(B.len(p), _)), pf, v, s)) : T.FdtTb}
          %drop_app(p, B.append(B.append(B.Octets.to_list(k), Con{0, T.prop.strs(t)}), q)) : {T.TbOpen{Con{T.FdtFrame{nm, List.reverse.go(&2, T.FdtProp, Con{T.FdtProp{k, v}, t}, pr), Nil{}}, s}} == T.tb.go(T.prop.toks(t, Nat.add(B.len(p), B.len(B.append(B.Octets.to_list(k), [0])))), T.FdtTreeRules{nop, pf}, strs, T.tb.prop.named(T.FdtFrame{nm, pr, Nil{}}, L.fdt.cstr(_), pf, v, s)) : T.FdtTb}
          %app_assoc(B.Octets.to_list(k), Con{0, T.prop.strs(t)}, q) : {T.TbOpen{Con{T.FdtFrame{nm, List.reverse.go(&2, T.FdtProp, Con{T.FdtProp{k, v}, t}, pr), Nil{}}, s}} == T.tb.go(T.prop.toks(t, Nat.add(B.len(p), B.len(B.append(B.Octets.to_list(k), [0])))), T.FdtTreeRules{nop, pf}, strs, T.tb.prop.named(T.FdtFrame{nm, pr, Nil{}}, L.fdt.cstr(_), pf, v, s)) : T.FdtTb}
          %scan_rt(B.Octets.to_list(k), B.append(T.prop.strs(t), q), Nil{}, and_l(L.fdt.nonul(B.Octets.to_list(k)), T.prop.names_ok(t), ok)) : {T.TbOpen{Con{T.FdtFrame{nm, List.reverse.go(&2, T.FdtProp, Con{T.FdtProp{k, v}, t}, pr), Nil{}}, s}} == T.tb.go(T.prop.toks(t, Nat.add(B.len(p), B.len(B.append(B.Octets.to_list(k), [0])))), T.FdtTreeRules{nop, pf}, strs, T.tb.prop.named(T.FdtFrame{nm, pr, Nil{}}, _, pf, v, s)) : T.FdtTb}
          %revrev(U32, B.Octets.to_list(k)) : {T.TbOpen{Con{T.FdtFrame{nm, List.reverse.go(&2, T.FdtProp, Con{T.FdtProp{k, v}, t}, pr), Nil{}}, s}} == T.tb.go(T.prop.toks(t, Nat.add(B.len(p), B.len(B.append(B.Octets.to_list(k), [0])))), T.FdtTreeRules{nop, pf}, strs, T.tb.prop.named(T.FdtFrame{nm, pr, Nil{}}, Some{L.FdtCut{_, B.append(T.prop.strs(t), q)}}, pf, v, s)) : T.FdtTb}
          %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(k)), k, BL.octets_of_to(k)) : {T.TbOpen{Con{T.FdtFrame{nm, List.reverse.go(&2, T.FdtProp, Con{T.FdtProp{k, v}, t}, pr), Nil{}}, s}} == T.tb.go(T.prop.toks(t, Nat.add(B.len(p), B.len(B.append(B.Octets.to_list(k), [0])))), T.FdtTreeRules{nop, pf}, strs, T.TbOpen{Con{T.FdtFrame{nm, Con{T.FdtProp{_, v}, pr}, Nil{}}, s}}) : T.FdtTb}
          %Equal.sym(Nat, Nat.add(B.len(p), B.len(B.append(B.Octets.to_list(k), [0]))), B.len(B.append(p, B.append(B.Octets.to_list(k), [0]))), len_app(p, B.append(B.Octets.to_list(k), [0]))) : {T.TbOpen{Con{T.FdtFrame{nm, List.reverse.go(&2, T.FdtProp, Con{T.FdtProp{k, v}, t}, pr), Nil{}}, s}} == T.tb.go(T.prop.toks(t, _), T.FdtTreeRules{nop, pf}, strs, T.TbOpen{Con{T.FdtFrame{nm, Con{T.FdtProp{k, v}, pr}, Nil{}}, s}}) : T.FdtTb}
          tb_props(t, nop, pf, strs, B.append(p, B.append(B.Octets.to_list(k), [0])), q, nm, Con{T.FdtProp{k, v}, pr}, s, Equal.trans(List<&2, U32>, B.append(B.append(p, B.append(B.Octets.to_list(k), [0])), B.append(T.prop.strs(t), q)), B.append(p, B.append(B.append(B.Octets.to_list(k), Con{0, T.prop.strs(t)}), q)), strs, eq_prop(p, B.Octets.to_list(k), T.prop.strs(t), q), et), ft, and_r(L.fdt.nonul(B.Octets.to_list(k)), T.prop.names_ok(t), ok))

def tb_forest(+ns: List<&2, T.FdtNode>, +nop: Bool, +pf: Bool, +strs: List<&2, U32>, +p: List<&2, U32>, +q: List<&2, U32>, +fn: B.Octets, +fp: List<&2, T.FdtProp>, +fk: List<&2, T.FdtNode>, +s: List<&2, T.FdtFrame>, +et: {B.append(p, B.append(T.flat.strs(ns), q)) == strs : List<&2, U32>}, +ft: {L.fdt.over(B.len(strs)) == 0n : Nat}, +ok: {T.flat.names_ok(ns) == True{} : Bool}) -> {T.TbOpen{Con{T.FdtFrame{fn, fp, List.reverse.go(&2, T.FdtNode, ns, fk)}, s}} == T.tb.go(T.flat.toks(ns, B.len(p)), T.FdtTreeRules{nop, pf}, strs, T.TbOpen{Con{T.FdtFrame{fn, fp, fk}, s}}) : T.FdtTb}:
  match ns:
    case Nil{}:
      {==}
    case Con{n, t}:
      match n:
        case T.FdtNode{nm, ps, cs}:
          %tb_go_app(T.prop.toks(ps, B.len(p)), List.append(&2, S.FdtToken, T.flat.toks(cs, Nat.add(B.len(p), B.len(T.prop.strs(ps)))), Con{S.FdtTokEnd{}, T.flat.toks(t, Nat.add(Nat.add(B.len(p), B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs))))}), T.FdtTreeRules{nop, pf}, strs, T.TbOpen{Con{T.FdtFrame{nm, Nil{}, Nil{}}, Con{T.FdtFrame{fn, fp, fk}, s}}}) : {T.TbOpen{Con{T.FdtFrame{fn, fp, List.reverse.go(&2, T.FdtNode, Con{T.FdtNode{nm, ps, cs}, t}, fk)}, s}} == _ : T.FdtTb}
          %tb_props(ps, nop, pf, strs, p, B.append(T.flat.strs(cs), B.append(T.flat.strs(t), q)), nm, Nil{}, Con{T.FdtFrame{fn, fp, fk}, s}, et_props(p, T.prop.strs(ps), T.flat.strs(cs), T.flat.strs(t), q, strs, et), ft, and_l(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(t)), and_r(L.fdt.nonul(B.Octets.to_list(nm)), Bool.and(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(t))), ok))) : {T.TbOpen{Con{T.FdtFrame{fn, fp, List.reverse.go(&2, T.FdtNode, Con{T.FdtNode{nm, ps, cs}, t}, fk)}, s}} == T.tb.go(List.append(&2, S.FdtToken, T.flat.toks(cs, Nat.add(B.len(p), B.len(T.prop.strs(ps)))), Con{S.FdtTokEnd{}, T.flat.toks(t, Nat.add(Nat.add(B.len(p), B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs))))}), T.FdtTreeRules{nop, pf}, strs, _) : T.FdtTb}
          %tb_go_app(T.flat.toks(cs, Nat.add(B.len(p), B.len(T.prop.strs(ps)))), Con{S.FdtTokEnd{}, T.flat.toks(t, Nat.add(Nat.add(B.len(p), B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs))))}, T.FdtTreeRules{nop, pf}, strs, T.TbOpen{Con{T.FdtFrame{nm, List.reverse.go(&2, T.FdtProp, ps, Nil{}), Nil{}}, Con{T.FdtFrame{fn, fp, fk}, s}}}) : {T.TbOpen{Con{T.FdtFrame{fn, fp, List.reverse.go(&2, T.FdtNode, Con{T.FdtNode{nm, ps, cs}, t}, fk)}, s}} == _ : T.FdtTb}
          %Equal.sym(Nat, Nat.add(B.len(p), B.len(T.prop.strs(ps))), B.len(B.append(p, T.prop.strs(ps))), len_app(p, T.prop.strs(ps))) : {T.TbOpen{Con{T.FdtFrame{fn, fp, List.reverse.go(&2, T.FdtNode, Con{T.FdtNode{nm, ps, cs}, t}, fk)}, s}} == T.tb.go(Con{S.FdtTokEnd{}, T.flat.toks(t, Nat.add(Nat.add(B.len(p), B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs))))}, T.FdtTreeRules{nop, pf}, strs, T.tb.go(T.flat.toks(cs, _), T.FdtTreeRules{nop, pf}, strs, T.TbOpen{Con{T.FdtFrame{nm, List.reverse.go(&2, T.FdtProp, ps, Nil{}), Nil{}}, Con{T.FdtFrame{fn, fp, fk}, s}}})) : T.FdtTb}
          %tb_forest(cs, nop, pf, strs, B.append(p, T.prop.strs(ps)), B.append(T.flat.strs(t), q), nm, List.reverse.go(&2, T.FdtProp, ps, Nil{}), Nil{}, Con{T.FdtFrame{fn, fp, fk}, s}, et_kids(p, T.prop.strs(ps), B.append(T.flat.strs(cs), B.append(T.flat.strs(t), q)), strs, et_props(p, T.prop.strs(ps), T.flat.strs(cs), T.flat.strs(t), q, strs, et)), ft, and_l(T.flat.names_ok(cs), T.flat.names_ok(t), and_r(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(t)), and_r(L.fdt.nonul(B.Octets.to_list(nm)), Bool.and(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(t))), ok)))) : {T.TbOpen{Con{T.FdtFrame{fn, fp, List.reverse.go(&2, T.FdtNode, Con{T.FdtNode{nm, ps, cs}, t}, fk)}, s}} == T.tb.go(Con{S.FdtTokEnd{}, T.flat.toks(t, Nat.add(Nat.add(B.len(p), B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs))))}, T.FdtTreeRules{nop, pf}, strs, _) : T.FdtTb}
          %revrev(T.FdtProp, ps) : {T.TbOpen{Con{T.FdtFrame{fn, fp, List.reverse.go(&2, T.FdtNode, Con{T.FdtNode{nm, ps, cs}, t}, fk)}, s}} == T.tb.go(T.flat.toks(t, Nat.add(Nat.add(B.len(p), B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs)))), T.FdtTreeRules{nop, pf}, strs, T.TbOpen{Con{T.FdtFrame{fn, fp, Con{T.FdtNode{nm, _, List.reverse(&2, T.FdtNode, List.reverse.go(&2, T.FdtNode, cs, Nil{}))}, fk}}, s}}) : T.FdtTb}
          %revrev(T.FdtNode, cs) : {T.TbOpen{Con{T.FdtFrame{fn, fp, List.reverse.go(&2, T.FdtNode, Con{T.FdtNode{nm, ps, cs}, t}, fk)}, s}} == T.tb.go(T.flat.toks(t, Nat.add(Nat.add(B.len(p), B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs)))), T.FdtTreeRules{nop, pf}, strs, T.TbOpen{Con{T.FdtFrame{fn, fp, Con{T.FdtNode{nm, ps, _}, fk}}, s}}) : T.FdtTb}
          %Equal.sym(Nat, Nat.add(B.len(p), B.len(T.prop.strs(ps))), B.len(B.append(p, T.prop.strs(ps))), len_app(p, T.prop.strs(ps))) : {T.TbOpen{Con{T.FdtFrame{fn, fp, List.reverse.go(&2, T.FdtNode, Con{T.FdtNode{nm, ps, cs}, t}, fk)}, s}} == T.tb.go(T.flat.toks(t, Nat.add(_, B.len(T.flat.strs(cs)))), T.FdtTreeRules{nop, pf}, strs, T.TbOpen{Con{T.FdtFrame{fn, fp, Con{T.FdtNode{nm, ps, cs}, fk}}, s}}) : T.FdtTb}
          %Equal.sym(Nat, Nat.add(B.len(B.append(p, T.prop.strs(ps))), B.len(T.flat.strs(cs))), B.len(B.append(B.append(p, T.prop.strs(ps)), T.flat.strs(cs))), len_app(B.append(p, T.prop.strs(ps)), T.flat.strs(cs))) : {T.TbOpen{Con{T.FdtFrame{fn, fp, List.reverse.go(&2, T.FdtNode, Con{T.FdtNode{nm, ps, cs}, t}, fk)}, s}} == T.tb.go(T.flat.toks(t, _), T.FdtTreeRules{nop, pf}, strs, T.TbOpen{Con{T.FdtFrame{fn, fp, Con{T.FdtNode{nm, ps, cs}, fk}}, s}}) : T.FdtTb}
          tb_forest(t, nop, pf, strs, B.append(B.append(p, T.prop.strs(ps)), T.flat.strs(cs)), q, fn, fp, Con{T.FdtNode{nm, ps, cs}, fk}, s, et_kids(B.append(p, T.prop.strs(ps)), T.flat.strs(cs), B.append(T.flat.strs(t), q), strs, et_kids(p, T.prop.strs(ps), B.append(T.flat.strs(cs), B.append(T.flat.strs(t), q)), strs, et_props(p, T.prop.strs(ps), T.flat.strs(cs), T.flat.strs(t), q, strs, et))), ft, and_r(T.flat.names_ok(cs), T.flat.names_ok(t), and_r(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(t)), and_r(L.fdt.nonul(B.Octets.to_list(nm)), Bool.and(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(t))), ok))))

def tb_root(+root: T.FdtNode, +nop: Bool, +pf: Bool, +strs: List<&2, U32>, +et: {T.flat.strs([root]) == strs : List<&2, U32>}, +ft: {L.fdt.over(B.len(strs)) == 0n : Nat}, +ok: {T.flat.names_ok([root]) == True{} : Bool}) -> {Done{root} == T.tb.run(T.flat.toks([root], 0n), T.FdtTreeRules{nop, pf}, strs) : Result<&2, &2, E.FdtError, T.FdtNode>}:
  match root:
    case T.FdtNode{nm, ps, cs}:
      %tb_go_app(T.prop.toks(ps, 0n), List.append(&2, S.FdtToken, T.flat.toks(cs, B.len(T.prop.strs(ps))), Con{S.FdtTokEnd{}, Nil{}}), T.FdtTreeRules{nop, pf}, strs, T.TbOpen{Con{T.FdtFrame{nm, Nil{}, Nil{}}, Nil{}}}) : {Done{T.FdtNode{nm, ps, cs}} == T.tb.finish(_) : Result<&2, &2, E.FdtError, T.FdtNode>}
      %tb_props(ps, nop, pf, strs, Nil{}, B.append(T.flat.strs(cs), Nil{}), nm, Nil{}, Nil{}, et, ft, and_l(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(Nil{})), and_r(L.fdt.nonul(B.Octets.to_list(nm)), Bool.and(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(Nil{}))), ok))) : {Done{T.FdtNode{nm, ps, cs}} == T.tb.finish(T.tb.go(List.append(&2, S.FdtToken, T.flat.toks(cs, B.len(T.prop.strs(ps))), Con{S.FdtTokEnd{}, Nil{}}), T.FdtTreeRules{nop, pf}, strs, _)) : Result<&2, &2, E.FdtError, T.FdtNode>}
      %tb_go_app(T.flat.toks(cs, B.len(T.prop.strs(ps))), Con{S.FdtTokEnd{}, Nil{}}, T.FdtTreeRules{nop, pf}, strs, T.TbOpen{Con{T.FdtFrame{nm, List.reverse.go(&2, T.FdtProp, ps, Nil{}), Nil{}}, Nil{}}}) : {Done{T.FdtNode{nm, ps, cs}} == T.tb.finish(_) : Result<&2, &2, E.FdtError, T.FdtNode>}
      %tb_forest(cs, nop, pf, strs, T.prop.strs(ps), Nil{}, nm, List.reverse.go(&2, T.FdtProp, ps, Nil{}), Nil{}, Nil{}, et, ft, and_l(T.flat.names_ok(cs), T.flat.names_ok(Nil{}), and_r(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(Nil{})), and_r(L.fdt.nonul(B.Octets.to_list(nm)), Bool.and(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(Nil{}))), ok)))) : {Done{T.FdtNode{nm, ps, cs}} == T.tb.finish(T.tb.go(Con{S.FdtTokEnd{}, Nil{}}, T.FdtTreeRules{nop, pf}, strs, _)) : Result<&2, &2, E.FdtError, T.FdtNode>}
      %revrev(T.FdtProp, ps) : {Done{T.FdtNode{nm, ps, cs}} == Done{T.FdtNode{nm, _, List.reverse(&2, T.FdtNode, List.reverse.go(&2, T.FdtNode, cs, Nil{}))}} : Result<&2, &2, E.FdtError, T.FdtNode>}
      %revrev(T.FdtNode, cs) : {Done{T.FdtNode{nm, ps, cs}} == Done{T.FdtNode{nm, ps, _}} : Result<&2, &2, E.FdtError, T.FdtNode>}
      {==}

def mask_c0(+x: List<&2, U32>, +e: {x == B.mask(x) : List<&2, U32>}) -> {Con{0, x} == B.mask(Con{0, x}) : List<&2, U32>}:
  %e : {Con{0, x} == Con{0, _} : List<&2, U32>}
  {==}

def mask_pstrs(+ps: List<&2, T.FdtProp>) -> {T.prop.strs(ps) == B.mask(T.prop.strs(ps)) : List<&2, U32>}:
  match ps:
    case Nil{}:
      {==}
    case Con{pp, t}:
      match pp:
        case T.FdtProp{k, v}:
          mask_id_app(B.Octets.to_list(k), Con{0, T.prop.strs(t)}, mask_tl(k), mask_c0(T.prop.strs(t), mask_pstrs(t)))

def mask_strs(+ns: List<&2, T.FdtNode>) -> {T.flat.strs(ns) == B.mask(T.flat.strs(ns)) : List<&2, U32>}:
  match ns:
    case Nil{}:
      {==}
    case Con{n, t}:
      match n:
        case T.FdtNode{nm, ps, cs}:
          mask_id_app(T.prop.strs(ps), B.append(T.flat.strs(cs), T.flat.strs(t)), mask_pstrs(ps), mask_id_app(T.flat.strs(cs), T.flat.strs(t), mask_strs(cs), mask_strs(t)))

# the law for the reference writer and check
def tree_rt(+rules: T.FdtTreeRules, +root: T.FdtNode, +ok: {T.flat_ok.ref(root) == True{} : Bool}) -> {T.tb.run(T.flat.toks([root], 0n), rules, B.Octets.to_list(B.Octets.of_list(T.flat.strs([root])))) == Done{root} : Result<&2, &2, E.FdtError, T.FdtNode>}:
  match rules:
    case T.FdtTreeRules{nop, pf}:
      %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(T.flat.strs([root]))), B.mask(T.flat.strs([root])), BL.octets_to_of(T.flat.strs([root]))) : {T.tb.run(T.flat.toks([root], 0n), T.FdtTreeRules{nop, pf}, _) == Done{root} : Result<&2, &2, E.FdtError, T.FdtNode>}
      %mask_strs([root]) : {T.tb.run(T.flat.toks([root], 0n), T.FdtTreeRules{nop, pf}, _) == Done{root} : Result<&2, &2, E.FdtError, T.FdtNode>}
      %tb_root(root, nop, pf, T.flat.strs([root]), {==}, zero_t(L.fdt.over(B.len(T.flat.strs([root]))), and_r(T.names_ok.ref(root), L.fdt.fits(B.len(T.flat.strs([root]))), ok)), and_l(T.names_ok.ref(root), L.fdt.fits(B.len(T.flat.strs([root]))), ok)) : {_ == Done{root} : Result<&2, &2, E.FdtError, T.FdtNode>}
      {==}

def Laws.tree_round_trip(rules, root, ok):
  %ftoks_fast([root], 0n) : {T.tb.run(_, rules, B.Octets.to_list(B.Octets.of_list(T.flat.strs.fast([root])))) == Done{root} : Result<&2, &2, E.FdtError, T.FdtNode>}
  %strs_fast([root]) : {T.tb.run(T.flat.toks([root], 0n), rules, B.Octets.to_list(B.Octets.of_list(_))) == Done{root} : Result<&2, &2, E.FdtError, T.FdtNode>}
  tree_rt(rules, root, Equal.trans(Bool, T.flat_ok.ref(root), T.FdtNode.flat_ok(root), True{}, flat_ok_fast(root), ok))

# The whole blob

def le_addk(+k: Nat, +n: Nat) -> {0n == Nat.sub(n, Nat.add(k, n)) : Nat}:
  match k:
    case 0n:
      sub_self(n)
    case 1n+p:
      sub_succ(n, Nat.add(p, n), le_addk(p, n))

def prefix2(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> {0n == Nat.sub(B.len(B.append(a, b)), B.len(B.append(a, B.append(b, c)))) : Nat}:
  match a:
    case Nil{}:
      prefix_le(b, c)
    case Con{h, t}:
      prefix2(t, b, c)

def le_struct(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> {0n == Nat.sub(Nat.add(B.len(a), B.len(b)), B.len(B.append(a, B.append(b, c)))) : Nat}:
  match a:
    case Nil{}:
      prefix_le(b, c)
    case Con{h, t}:
      le_struct(t, b, c)

def le_strs(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> {0n == Nat.sub(Nat.add(B.len(B.append(a, b)), B.len(c)), B.len(B.append(a, B.append(b, c)))) : Nat}:
  match a:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(B.len(b), B.len(c)), B.len(B.append(b, c)), len_app(b, c)) : {0n == Nat.sub(_, B.len(B.append(b, c))) : Nat}
      sub_self(B.len(B.append(b, c)))
    case Con{h, t}:
      le_strs(t, b, c)

def take_all(+x: List<&2, U32>) -> {x == B.take(B.len(x), x) : List<&2, U32>}:
  match x:
    case Nil{}:
      {==}
    case Con{h, t}:
      %take_all(t) : {Con{h, t} == Con{h, _} : List<&2, U32>}
      {==}

# the sizes and offsets of a blob's blocks fit, when its total size does
def f_os(+rl: List<&2, U32>, +sl: List<&2, U32>, +tl: List<&2, U32>, +ef: {L.fdt.over(Nat.add(40n, B.len(B.append(rl, B.append(sl, tl))))) == 0n : Nat}) -> {L.fdt.over(Nat.add(40n, B.len(rl))) == 0n : Nat}:
  fits_le(Nat.add(40n, B.len(rl)), Nat.add(40n, B.len(B.append(rl, B.append(sl, tl)))), ef, prefix_le(rl, B.append(sl, tl)))

def f_ostr(+rl: List<&2, U32>, +sl: List<&2, U32>, +tl: List<&2, U32>, +ef: {L.fdt.over(Nat.add(40n, B.len(B.append(rl, B.append(sl, tl))))) == 0n : Nat}) -> {L.fdt.over(Nat.add(40n, B.len(B.append(rl, sl)))) == 0n : Nat}:
  fits_le(Nat.add(40n, B.len(B.append(rl, sl))), Nat.add(40n, B.len(B.append(rl, B.append(sl, tl)))), ef, prefix2(rl, sl, tl))

def f_s(+rl: List<&2, U32>, +sl: List<&2, U32>, +tl: List<&2, U32>, +ef: {L.fdt.over(Nat.add(40n, B.len(B.append(rl, B.append(sl, tl))))) == 0n : Nat}) -> {L.fdt.over(B.len(sl)) == 0n : Nat}:
  fits_le(B.len(sl), Nat.add(40n, B.len(B.append(rl, B.append(sl, tl)))), ef, le_trans(B.len(sl), B.len(B.append(rl, B.append(sl, tl))), Nat.add(40n, B.len(B.append(rl, B.append(sl, tl)))), le_trans(B.len(sl), B.len(B.append(sl, tl)), B.len(B.append(rl, B.append(sl, tl))), prefix_le(sl, tl), suffix_le(rl, B.append(sl, tl))), le_addk(40n, B.len(B.append(rl, B.append(sl, tl))))))

def f_t(+rl: List<&2, U32>, +sl: List<&2, U32>, +tl: List<&2, U32>, +ef: {L.fdt.over(Nat.add(40n, B.len(B.append(rl, B.append(sl, tl))))) == 0n : Nat}) -> {L.fdt.over(B.len(tl)) == 0n : Nat}:
  fits_le(B.len(tl), Nat.add(40n, B.len(B.append(rl, B.append(sl, tl)))), ef, le_trans(B.len(tl), B.len(B.append(rl, B.append(sl, tl))), Nat.add(40n, B.len(B.append(rl, B.append(sl, tl)))), le_trans(B.len(tl), B.len(B.append(sl, tl)), B.len(B.append(rl, B.append(sl, tl))), suffix_le(sl, tl), suffix_le(rl, B.append(sl, tl))), le_addk(40n, B.len(B.append(rl, B.append(sl, tl))))))

# the reservation block is a whole number of 16-byte entries
def lenent(+h1: U32, +l1: U32, +h2: U32, +l2: U32) -> {16n == B.len(B.append(B.append(B.be32(h1), B.be32(l1)), B.append(B.be32(h2), B.be32(l2)))) : Nat}:
  match h1 l1 h2 l2:
    case U32{a} U32{b} U32{c} U32{d}:
      {==}

def pad_rsv(+rs: List<&2, R.FdtRsv>) -> {0n == L.fdt.pad4(B.len(R.rsv.list(rs))) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case Con{r, t}:
      match r:
        case R.FdtRsv{a, s}:
          %len_app(R.rsv.entry(R.FdtRsv{a, s}), R.rsv.list(t)) : {0n == L.fdt.pad4(_) : Nat}
          %lenent(W.W64.hi(a), W.W64.lo(a), W.W64.hi(s), W.W64.lo(s)) : {0n == L.fdt.pad4(Nat.add(_, B.len(R.rsv.list(t)))) : Nat}
          pad_rsv(t)

# The header's 40 bytes: reading them, and skipping them

def hdr_dec(+h: H.FdtHeader, +x: List<&2, U32>) -> {Some{h} == H.hdr.decode(B.append(H.hdr.list(h), x)) : Maybe<&2, H.FdtHeader>}:
  match h:
    case H.FdtHeader{U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WCon{d8, WCon{d9, WCon{d10, WCon{d11, WCon{d12, WCon{d13, WCon{d14, WCon{d15, WCon{d16, WCon{d17, WCon{d18, WCon{d19, WCon{d20, WCon{d21, WCon{d22, WCon{d23, WCon{d24, WCon{d25, WCon{d26, WCon{d27, WCon{d28, WCon{d29, WCon{d30, WCon{d31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{e0, WCon{e1, WCon{e2, WCon{e3, WCon{e4, WCon{e5, WCon{e6, WCon{e7, WCon{e8, WCon{e9, WCon{e10, WCon{e11, WCon{e12, WCon{e13, WCon{e14, WCon{e15, WCon{e16, WCon{e17, WCon{e18, WCon{e19, WCon{e20, WCon{e21, WCon{e22, WCon{e23, WCon{e24, WCon{e25, WCon{e26, WCon{e27, WCon{e28, WCon{e29, WCon{e30, WCon{e31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{f0, WCon{f1, WCon{f2, WCon{f3, WCon{f4, WCon{f5, WCon{f6, WCon{f7, WCon{f8, WCon{f9, WCon{f10, WCon{f11, WCon{f12, WCon{f13, WCon{f14, WCon{f15, WCon{f16, WCon{f17, WCon{f18, WCon{f19, WCon{f20, WCon{f21, WCon{f22, WCon{f23, WCon{f24, WCon{f25, WCon{f26, WCon{f27, WCon{f28, WCon{f29, WCon{f30, WCon{f31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{g0, WCon{g1, WCon{g2, WCon{g3, WCon{g4, WCon{g5, WCon{g6, WCon{g7, WCon{g8, WCon{g9, WCon{g10, WCon{g11, WCon{g12, WCon{g13, WCon{g14, WCon{g15, WCon{g16, WCon{g17, WCon{g18, WCon{g19, WCon{g20, WCon{g21, WCon{g22, WCon{g23, WCon{g24, WCon{g25, WCon{g26, WCon{g27, WCon{g28, WCon{g29, WCon{g30, WCon{g31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{i0, WCon{i1, WCon{i2, WCon{i3, WCon{i4, WCon{i5, WCon{i6, WCon{i7, WCon{i8, WCon{i9, WCon{i10, WCon{i11, WCon{i12, WCon{i13, WCon{i14, WCon{i15, WCon{i16, WCon{i17, WCon{i18, WCon{i19, WCon{i20, WCon{i21, WCon{i22, WCon{i23, WCon{i24, WCon{i25, WCon{i26, WCon{i27, WCon{i28, WCon{i29, WCon{i30, WCon{i31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{j0, WCon{j1, WCon{j2, WCon{j3, WCon{j4, WCon{j5, WCon{j6, WCon{j7, WCon{j8, WCon{j9, WCon{j10, WCon{j11, WCon{j12, WCon{j13, WCon{j14, WCon{j15, WCon{j16, WCon{j17, WCon{j18, WCon{j19, WCon{j20, WCon{j21, WCon{j22, WCon{j23, WCon{j24, WCon{j25, WCon{j26, WCon{j27, WCon{j28, WCon{j29, WCon{j30, WCon{j31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{k0, WCon{k1, WCon{k2, WCon{k3, WCon{k4, WCon{k5, WCon{k6, WCon{k7, WCon{k8, WCon{k9, WCon{k10, WCon{k11, WCon{k12, WCon{k13, WCon{k14, WCon{k15, WCon{k16, WCon{k17, WCon{k18, WCon{k19, WCon{k20, WCon{k21, WCon{k22, WCon{k23, WCon{k24, WCon{k25, WCon{k26, WCon{k27, WCon{k28, WCon{k29, WCon{k30, WCon{k31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def hs_drop(+h: H.FdtHeader, +n: Nat, +x: List<&2, U32>) -> {B.drop(n, x) == B.drop(Nat.add(40n, n), B.append(H.hdr.list(h), x)) : List<&2, U32>}:
  match h:
    case H.FdtHeader{U32{a}, U32{b}, U32{c}, U32{d}, U32{e}, U32{f}, U32{g}, U32{i}, U32{j}, U32{k}}:
      {==}

def hs_take(+h: H.FdtHeader, +n: Nat, +x: List<&2, U32>) -> {B.append(H.hdr.list(h), B.take(n, x)) == B.take(Nat.add(40n, n), B.append(H.hdr.list(h), x)) : List<&2, U32>}:
  match h:
    case H.FdtHeader{U32{a}, U32{b}, U32{c}, U32{d}, U32{e}, U32{f}, U32{g}, U32{i}, U32{j}, U32{k}}:
      {==}

def mask_hdr(+h: H.FdtHeader) -> {H.hdr.list(h) == B.mask(H.hdr.list(h)) : List<&2, U32>}:
  match h:
    case H.FdtHeader{a, b, c, d, e, f, g, i, j, k}:
      mask_id_app(B.be32(a), B.append(B.be32(b), B.append(B.be32(c), B.append(B.be32(d), B.append(B.be32(e), B.append(B.be32(f), B.append(B.be32(g), B.append(B.be32(i), B.append(B.be32(j), B.be32(k))))))))), mask_be32(a), mask_id_app(B.be32(b), B.append(B.be32(c), B.append(B.be32(d), B.append(B.be32(e), B.append(B.be32(f), B.append(B.be32(g), B.append(B.be32(i), B.append(B.be32(j), B.be32(k)))))))), mask_be32(b), mask_id_app(B.be32(c), B.append(B.be32(d), B.append(B.be32(e), B.append(B.be32(f), B.append(B.be32(g), B.append(B.be32(i), B.append(B.be32(j), B.be32(k))))))), mask_be32(c), mask_id_app(B.be32(d), B.append(B.be32(e), B.append(B.be32(f), B.append(B.be32(g), B.append(B.be32(i), B.append(B.be32(j), B.be32(k)))))), mask_be32(d), mask_id_app(B.be32(e), B.append(B.be32(f), B.append(B.be32(g), B.append(B.be32(i), B.append(B.be32(j), B.be32(k))))), mask_be32(e), mask_id_app(B.be32(f), B.append(B.be32(g), B.append(B.be32(i), B.append(B.be32(j), B.be32(k)))), mask_be32(f), mask_id_app(B.be32(g), B.append(B.be32(i), B.append(B.be32(j), B.be32(k))), mask_be32(g), mask_id_app(B.be32(i), B.append(B.be32(j), B.be32(k)), mask_be32(i), mask_id_app(B.be32(j), B.be32(k), mask_be32(j), mask_be32(k))))))))))

# Checking the header Fdt.build writes: its sizes and offsets read back as
# the blocks' lengths, and every check holds
def hdr_ok(+vs: H.FdtVersions, +rl: List<&2, U32>, +sl: List<&2, U32>, +tl: List<&2, U32>, +b: U32, +ef: {L.fdt.over(Nat.add(40n, B.len(B.append(rl, B.append(sl, tl))))) == 0n : Nat}, +ep: {0n == L.fdt.pad4(B.len(rl)) : Nat}) -> {Done{Unit{}} == H.FdtHeader.check(vs, H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(rl, B.append(sl, tl))))), L.fdt.u32n(Nat.add(40n, B.len(rl))), L.fdt.u32n(Nat.add(40n, B.len(B.append(rl, sl)))), 40, 17, 16, b, L.fdt.u32n(B.len(tl)), L.fdt.u32n(B.len(sl))}, B.len(B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(rl, B.append(sl, tl))))), L.fdt.u32n(Nat.add(40n, B.len(rl))), L.fdt.u32n(Nat.add(40n, B.len(B.append(rl, sl)))), 40, 17, 16, b, L.fdt.u32n(B.len(tl)), L.fdt.u32n(B.len(sl))}), B.append(rl, B.append(sl, tl))))) : Result<&2, &2, E.FdtError, Unit>}:
  match b:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %size_rt(Nat.add(40n, B.len(B.append(rl, B.append(sl, tl)))), ef) : {Done{Unit{}} == H.hdr.c1(True{}, vs, 17, 16, _, U32.to_nat(L.fdt.u32n(Nat.add(40n, B.len(rl)))), U32.to_nat(L.fdt.u32n(Nat.add(40n, B.len(B.append(rl, sl))))), U32.to_nat(40), U32.to_nat(L.fdt.u32n(B.len(tl))), U32.to_nat(L.fdt.u32n(B.len(sl))), B.len(B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(rl, B.append(sl, tl))))), L.fdt.u32n(Nat.add(40n, B.len(rl))), L.fdt.u32n(Nat.add(40n, B.len(B.append(rl, sl)))), 40, 17, 16, U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, L.fdt.u32n(B.len(tl)), L.fdt.u32n(B.len(sl))}), B.append(rl, B.append(sl, tl))))) : Result<&2, &2, E.FdtError, Unit>}
      %size_rt(Nat.add(40n, B.len(rl)), f_os(rl, sl, tl, ef)) : {Done{Unit{}} == H.hdr.c1(True{}, vs, 17, 16, Nat.add(40n, B.len(B.append(rl, B.append(sl, tl)))), _, U32.to_nat(L.fdt.u32n(Nat.add(40n, B.len(B.append(rl, sl))))), U32.to_nat(40), U32.to_nat(L.fdt.u32n(B.len(tl))), U32.to_nat(L.fdt.u32n(B.len(sl))), B.len(B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(rl, B.append(sl, tl))))), L.fdt.u32n(Nat.add(40n, B.len(rl))), L.fdt.u32n(Nat.add(40n, B.len(B.append(rl, sl)))), 40, 17, 16, U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, L.fdt.u32n(B.len(tl)), L.fdt.u32n(B.len(sl))}), B.append(rl, B.append(sl, tl))))) : Result<&2, &2, E.FdtError, Unit>}
      %size_rt(Nat.add(40n, B.len(B.append(rl, sl))), f_ostr(rl, sl, tl, ef)) : {Done{Unit{}} == H.hdr.c1(True{}, vs, 17, 16, Nat.add(40n, B.len(B.append(rl, B.append(sl, tl)))), Nat.add(40n, B.len(rl)), _, U32.to_nat(40), U32.to_nat(L.fdt.u32n(B.len(tl))), U32.to_nat(L.fdt.u32n(B.len(sl))), B.len(B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(rl, B.append(sl, tl))))), L.fdt.u32n(Nat.add(40n, B.len(rl))), L.fdt.u32n(Nat.add(40n, B.len(B.append(rl, sl)))), 40, 17, 16, U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, L.fdt.u32n(B.len(tl)), L.fdt.u32n(B.len(sl))}), B.append(rl, B.append(sl, tl))))) : Result<&2, &2, E.FdtError, Unit>}
      %size_rt(B.len(tl), f_t(rl, sl, tl, ef)) : {Done{Unit{}} == H.hdr.c1(True{}, vs, 17, 16, Nat.add(40n, B.len(B.append(rl, B.append(sl, tl)))), Nat.add(40n, B.len(rl)), Nat.add(40n, B.len(B.append(rl, sl))), U32.to_nat(40), _, U32.to_nat(L.fdt.u32n(B.len(sl))), B.len(B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(rl, B.append(sl, tl))))), L.fdt.u32n(Nat.add(40n, B.len(rl))), L.fdt.u32n(Nat.add(40n, B.len(B.append(rl, sl)))), 40, 17, 16, U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, L.fdt.u32n(B.len(tl)), L.fdt.u32n(B.len(sl))}), B.append(rl, B.append(sl, tl))))) : Result<&2, &2, E.FdtError, Unit>}
      %size_rt(B.len(sl), f_s(rl, sl, tl, ef)) : {Done{Unit{}} == H.hdr.c1(True{}, vs, 17, 16, Nat.add(40n, B.len(B.append(rl, B.append(sl, tl)))), Nat.add(40n, B.len(rl)), Nat.add(40n, B.len(B.append(rl, sl))), U32.to_nat(40), B.len(tl), _, B.len(B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(rl, B.append(sl, tl))))), L.fdt.u32n(Nat.add(40n, B.len(rl))), L.fdt.u32n(Nat.add(40n, B.len(B.append(rl, sl)))), 40, 17, 16, U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, L.fdt.u32n(B.len(tl)), L.fdt.u32n(B.len(sl))}), B.append(rl, B.append(sl, tl))))) : Result<&2, &2, E.FdtError, Unit>}
      %sub_self(B.len(B.append(rl, B.append(sl, tl)))) : {Done{Unit{}} == H.hdr.c4(Bool.and(L.fdt.le(40n, Nat.add(40n, B.len(B.append(rl, B.append(sl, tl))))), L.fdt.is_zero(_)), 17, Nat.add(40n, B.len(B.append(rl, B.append(sl, tl)))), Nat.add(40n, B.len(rl)), Nat.add(40n, B.len(B.append(rl, sl))), U32.to_nat(40), B.len(tl), B.len(sl)) : Result<&2, &2, E.FdtError, Unit>}
      %ep : {Done{Unit{}} == H.hdr.c6(Bool.and(L.fdt.is_zero(_), Bool.and(L.fdt.le(40n, Nat.add(40n, B.len(rl))), L.fdt.le(H.hdr.struct_end(U32.is_lt(16, 17), Nat.add(40n, B.len(rl)), B.len(sl)), Nat.add(40n, B.len(B.append(rl, B.append(sl, tl))))))), Nat.add(40n, B.len(B.append(rl, B.append(sl, tl)))), Nat.add(40n, B.len(B.append(rl, sl))), B.len(tl)) : Result<&2, &2, E.FdtError, Unit>}
      %le_struct(rl, sl, tl) : {Done{Unit{}} == H.hdr.c6(Bool.and(L.fdt.is_zero(0n), Bool.and(L.fdt.le(40n, Nat.add(40n, B.len(rl))), L.fdt.is_zero(_))), Nat.add(40n, B.len(B.append(rl, B.append(sl, tl)))), Nat.add(40n, B.len(B.append(rl, sl))), B.len(tl)) : Result<&2, &2, E.FdtError, Unit>}
      %le_strs(rl, sl, tl) : {Done{Unit{}} == H.hdr.c7(Bool.and(L.fdt.le(40n, Nat.add(40n, B.len(B.append(rl, sl)))), L.fdt.is_zero(_))) : Result<&2, &2, E.FdtError, Unit>}
      {==}

# The tokens of a tree that wf admits are valid tokens

def valid_app(+xs: List<&2, S.FdtToken>, +ys: List<&2, S.FdtToken>, +ex: {S.tok.valid_all.ref(xs) == True{} : Bool}, +ey: {S.tok.valid_all.ref(ys) == True{} : Bool}) -> {S.tok.valid_all.ref(List.append(&2, S.FdtToken, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      ey
    case Con{t, r}:
      %Equal.sym(Bool, S.tok.valid.ref(t), True{}, and_l(S.tok.valid.ref(t), S.tok.valid_all.ref(r), ex)) : {Bool.and(_, S.tok.valid_all.ref(List.append(&2, S.FdtToken, r, ys))) == True{} : Bool}
      valid_app(r, ys, and_r(S.tok.valid.ref(t), S.tok.valid_all.ref(r), ex), ey)

def ptoks_valid(+ps: List<&2, T.FdtProp>, +off: Nat, +ok: {T.prop.values_ok(ps) == True{} : Bool}) -> {S.tok.valid_all.ref(T.prop.toks(ps, off)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{pp, t}:
      match pp:
        case T.FdtProp{k, v}:
          %Equal.sym(Bool, L.fdt.fits(B.len(B.Octets.to_list(v))), True{}, and_l(L.fdt.fits(B.len(B.Octets.to_list(v))), T.prop.values_ok(t), ok)) : {Bool.and(_, S.tok.valid_all.ref(T.prop.toks(t, Nat.add(off, B.len(B.append(B.Octets.to_list(k), [0])))))) == True{} : Bool}
          ptoks_valid(t, Nat.add(off, B.len(B.append(B.Octets.to_list(k), [0]))), and_r(L.fdt.fits(B.len(B.Octets.to_list(v))), T.prop.values_ok(t), ok))


def ftoks_valid(+ns: List<&2, T.FdtNode>, +off: Nat, +okn: {T.flat.names_ok(ns) == True{} : Bool}, +okv: {T.flat.values_ok(ns) == True{} : Bool}) -> {S.tok.valid_all.ref(T.flat.toks(ns, off)) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{n, t}:
      match n:
        case T.FdtNode{nm, ps, cs}:
          %Equal.sym(Bool, L.fdt.nonul(B.Octets.to_list(nm)), True{}, and_l(L.fdt.nonul(B.Octets.to_list(nm)), Bool.and(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(t))), okn)) : {Bool.and(_, S.tok.valid_all.ref(List.append(&2, S.FdtToken, T.prop.toks(ps, off), List.append(&2, S.FdtToken, T.flat.toks(cs, Nat.add(off, B.len(T.prop.strs(ps)))), Con{S.FdtTokEnd{}, T.flat.toks(t, Nat.add(Nat.add(off, B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs))))})))) == True{} : Bool}
          valid_app(T.prop.toks(ps, off), List.append(&2, S.FdtToken, T.flat.toks(cs, Nat.add(off, B.len(T.prop.strs(ps)))), Con{S.FdtTokEnd{}, T.flat.toks(t, Nat.add(Nat.add(off, B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs))))}), ptoks_valid(ps, off, and_l(T.prop.values_ok(ps), Bool.and(T.flat.values_ok(cs), T.flat.values_ok(t)), okv)), valid_app(T.flat.toks(cs, Nat.add(off, B.len(T.prop.strs(ps)))), Con{S.FdtTokEnd{}, T.flat.toks(t, Nat.add(Nat.add(off, B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs))))}, ftoks_valid(cs, Nat.add(off, B.len(T.prop.strs(ps))), and_l(T.flat.names_ok(cs), T.flat.names_ok(t), and_r(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(t)), and_r(L.fdt.nonul(B.Octets.to_list(nm)), Bool.and(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(t))), okn))), and_l(T.flat.values_ok(cs), T.flat.values_ok(t), and_r(T.prop.values_ok(ps), Bool.and(T.flat.values_ok(cs), T.flat.values_ok(t)), okv))), ftoks_valid(t, Nat.add(Nat.add(off, B.len(T.prop.strs(ps))), B.len(T.flat.strs(cs))), and_r(T.flat.names_ok(cs), T.flat.names_ok(t), and_r(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(t)), and_r(L.fdt.nonul(B.Octets.to_list(nm)), Bool.and(T.prop.names_ok(ps), Bool.and(T.flat.names_ok(cs), T.flat.names_ok(t))), okn))), and_r(T.flat.values_ok(cs), T.flat.values_ok(t), and_r(T.prop.values_ok(ps), Bool.and(T.flat.values_ok(cs), T.flat.values_ok(t)), okv)))))

def mask_lb(+rsv: List<&2, R.FdtRsv>, +root: T.FdtNode, +boot: U32) -> {B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))) == B.mask(B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))) : List<&2, U32>}:
  mask_id_app(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))), mask_hdr(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), mask_id_app(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])), mask_rsv(rsv), mask_id_app(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]), mask_toks(T.flat.toks([root], 0n)), mask_strs([root]))))

# the law for the reference reader, writer and check
def parse_build_rt(+opts: F.FdtOptions, +root: T.FdtNode, +rsv: List<&2, R.FdtRsv>, +boot: U32, +ok: {F.buildable.ref(root, rsv) == True{} : Bool}) -> {F.parse.p1(opts, B.Octets.to_list(B.Octets.of_list(F.build.simple(root, rsv, boot)))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}:
  match opts:
    case F.FdtOptions{vs, rules}:
      match rules:
        case T.FdtTreeRules{nop, pf}:
          %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), B.mask(B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))), BL.octets_to_of(B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))) : {F.parse.p1(F.FdtOptions{vs, T.FdtTreeRules{nop, pf}}, _) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %mask_lb(rsv, root, boot) : {F.parse.p1(F.FdtOptions{vs, T.FdtTreeRules{nop, pf}}, _) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %hdr_dec(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}, B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))) : {F.parse.p4(_, F.FdtOptions{vs, T.FdtTreeRules{nop, pf}}, B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %hdr_ok(vs, R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]), boot, zero_t(L.fdt.over(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), and_r(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), and_r(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))), ok))), pad_rsv(rsv)) : {F.parse.p5(_, T.FdtTreeRules{nop, pf}, H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}, B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %size_rt(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))), zero_t(L.fdt.over(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), and_r(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), and_r(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))), ok)))) : {F.parse.p6(T.FdtTreeRules{nop, pf}, 17, boot, B.take(_, B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))), U32.to_nat(40), U32.to_nat(L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv))))), U32.to_nat(L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))), U32.to_nat(L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))))))), U32.to_nat(L.fdt.u32n(B.len(T.flat.strs([root]))))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %size_rt(Nat.add(40n, B.len(R.rsv.list(rsv))), f_os(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]), zero_t(L.fdt.over(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), and_r(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), and_r(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))), ok))))) : {F.parse.p6(T.FdtTreeRules{nop, pf}, 17, boot, B.take(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))), B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))), U32.to_nat(40), _, U32.to_nat(L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))), U32.to_nat(L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))))))), U32.to_nat(L.fdt.u32n(B.len(T.flat.strs([root]))))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %size_rt(B.len(S.toks.list(T.flat.toks([root], 0n))), f_s(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]), zero_t(L.fdt.over(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), and_r(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), and_r(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))), ok))))) : {F.parse.p6(T.FdtTreeRules{nop, pf}, 17, boot, B.take(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))), B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))), U32.to_nat(40), Nat.add(40n, B.len(R.rsv.list(rsv))), _, U32.to_nat(L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))))))), U32.to_nat(L.fdt.u32n(B.len(T.flat.strs([root]))))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %size_rt(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))))), f_ostr(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]), zero_t(L.fdt.over(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), and_r(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), and_r(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))), ok))))) : {F.parse.p6(T.FdtTreeRules{nop, pf}, 17, boot, B.take(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))), B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))), U32.to_nat(40), Nat.add(40n, B.len(R.rsv.list(rsv))), B.len(S.toks.list(T.flat.toks([root], 0n))), _, U32.to_nat(L.fdt.u32n(B.len(T.flat.strs([root]))))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %size_rt(B.len(T.flat.strs([root])), f_t(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]), zero_t(L.fdt.over(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), and_r(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), and_r(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))), ok))))) : {F.parse.p6(T.FdtTreeRules{nop, pf}, 17, boot, B.take(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))), B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))), U32.to_nat(40), Nat.add(40n, B.len(R.rsv.list(rsv))), B.len(S.toks.list(T.flat.toks([root], 0n))), Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))))), _) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %hs_take(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))) : {F.parse.p6(T.FdtTreeRules{nop, pf}, 17, boot, _, U32.to_nat(40), Nat.add(40n, B.len(R.rsv.list(rsv))), B.len(S.toks.list(T.flat.toks([root], 0n))), Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))))), B.len(T.flat.strs([root]))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %take_all(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))) : {F.parse.p6(T.FdtTreeRules{nop, pf}, 17, boot, B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), _), U32.to_nat(40), Nat.add(40n, B.len(R.rsv.list(rsv))), B.len(S.toks.list(T.flat.toks([root], 0n))), Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))))), B.len(T.flat.strs([root]))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %hs_drop(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}, 0n, B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))) : {F.parse.p7(R.rsv.read(_), F.parse.struct(U32.is_lt(16, 17), Nat.add(40n, B.len(R.rsv.list(rsv))), B.len(S.toks.list(T.flat.toks([root], 0n))), B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))), T.FdtTreeRules{nop, pf}, 17, boot, B.take(B.len(T.flat.strs([root])), B.drop(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))))), B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %rsv_rt(rsv, B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])), Nil{}, and_l(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), and_r(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))), ok))) : {F.parse.p7(_, F.parse.struct(U32.is_lt(16, 17), Nat.add(40n, B.len(R.rsv.list(rsv))), B.len(S.toks.list(T.flat.toks([root], 0n))), B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))), T.FdtTreeRules{nop, pf}, 17, boot, B.take(B.len(T.flat.strs([root])), B.drop(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))))), B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %revrev(R.FdtRsv, rsv) : {F.parse.p7(Done{_}, F.parse.struct(U32.is_lt(16, 17), Nat.add(40n, B.len(R.rsv.list(rsv))), B.len(S.toks.list(T.flat.toks([root], 0n))), B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))), T.FdtTreeRules{nop, pf}, 17, boot, B.take(B.len(T.flat.strs([root])), B.drop(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))))), B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %hs_drop(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}, B.len(R.rsv.list(rsv)), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))) : {F.parse.p7(Done{rsv}, S.FdtLexer.finish(True{}, S.lx.go(B.take(B.len(S.toks.list(T.flat.toks([root], 0n))), _), S.FdtLexer.start())), T.FdtTreeRules{nop, pf}, 17, boot, B.take(B.len(T.flat.strs([root])), B.drop(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))))), B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %drop_app(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))) : {F.parse.p7(Done{rsv}, S.FdtLexer.finish(True{}, S.lx.go(B.take(B.len(S.toks.list(T.flat.toks([root], 0n))), _), S.FdtLexer.start())), T.FdtTreeRules{nop, pf}, 17, boot, B.take(B.len(T.flat.strs([root])), B.drop(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))))), B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %take_app(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])) : {F.parse.p7(Done{rsv}, S.FdtLexer.finish(True{}, S.lx.go(_, S.FdtLexer.start())), T.FdtTreeRules{nop, pf}, 17, boot, B.take(B.len(T.flat.strs([root])), B.drop(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))))), B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %lx_toks(T.flat.toks([root], 0n), Nil{}, ftoks_valid([root], 0n, and_l(T.names_ok.ref(root), T.flat.values_ok([root]), and_l(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))), ok)), and_r(T.names_ok.ref(root), T.flat.values_ok([root]), and_l(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))), ok)))) : {F.parse.p7(Done{rsv}, S.FdtLexer.finish(True{}, _), T.FdtTreeRules{nop, pf}, 17, boot, B.take(B.len(T.flat.strs([root])), B.drop(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))))), B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %revrev(S.FdtToken, T.flat.toks([root], 0n)) : {F.parse.p7(Done{rsv}, Done{_}, T.FdtTreeRules{nop, pf}, 17, boot, B.take(B.len(T.flat.strs([root])), B.drop(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))))), B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %hs_drop(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), L.fdt.u32n(Nat.add(40n, B.len(R.rsv.list(rsv)))), L.fdt.u32n(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))))), 40, 17, 16, boot, L.fdt.u32n(B.len(T.flat.strs([root]))), L.fdt.u32n(B.len(S.toks.list(T.flat.toks([root], 0n))))}, B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))), B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))) : {F.parse.p7(Done{rsv}, Done{T.flat.toks([root], 0n)}, T.FdtTreeRules{nop, pf}, 17, boot, B.take(B.len(T.flat.strs([root])), _)) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %Equal.sym(List<&2, U32>, B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))), B.append(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))), T.flat.strs([root])), app_assoc(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))) : {F.parse.p7(Done{rsv}, Done{T.flat.toks([root], 0n)}, T.FdtTreeRules{nop, pf}, 17, boot, B.take(B.len(T.flat.strs([root])), B.drop(B.len(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)))), _))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %drop_app(B.append(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n))), T.flat.strs([root])) : {F.parse.p7(Done{rsv}, Done{T.flat.toks([root], 0n)}, T.FdtTreeRules{nop, pf}, 17, boot, B.take(B.len(T.flat.strs([root])), _)) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %take_all(T.flat.strs([root])) : {F.parse.p7(Done{rsv}, Done{T.flat.toks([root], 0n)}, T.FdtTreeRules{nop, pf}, 17, boot, _) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          %tb_root(root, nop, pf, T.flat.strs([root]), {==}, f_t(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]), zero_t(L.fdt.over(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), and_r(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))))), and_r(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))), ok)))), and_l(T.names_ok.ref(root), T.flat.values_ok([root]), and_l(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]))))))), ok))) : {F.parse.p9(_, 17, boot, rsv) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
          {==}

def Laws.parse_build(opts, root, rsv, boot, ok):
  %parse_fast(opts, B.Octets.to_list(B.Octets.of_list(F.build.fast(root, rsv, boot)))) : {_ == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
  %build_fast(root, rsv, boot) : {F.parse.p1(opts, B.Octets.to_list(B.Octets.of_list(_))) == Done{F.FdtBlob{17, boot, rsv, root}} : Result<&2, &2, E.FdtError, F.FdtBlob>}
  parse_build_rt(opts, root, rsv, boot, Equal.trans(Bool, F.buildable.ref(root, rsv), F.Fdt.buildable(root, rsv), True{}, buildable_fast(root, rsv), ok))

# More property values: a string list folds byte by byte

def sl_one(+sl: List<&2, U32>, +r: List<&2, U32>, +cur: List<&2, U32>, +done: List<&2, B.Octets>, +ok: {L.fdt.nonul(sl) == True{} : Bool}) -> {P.pr.sl.fold(r, P.FdtStrList{Nil{}, Con{B.Octets.of_list(List.reverse(&2, U32, List.reverse.go(&2, U32, sl, cur))), done}}) == P.pr.sl.fold(B.append(sl, Con{0, r}), P.FdtStrList{cur, done}) : P.FdtStrList}:
  match sl:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(Bool, U32.is_eq(h, 0), False{}, not_t(U32.is_eq(h, 0), and_l(Bool.not(U32.is_eq(h, 0)), L.fdt.nonul(t), ok))) : {P.pr.sl.fold(r, P.FdtStrList{Nil{}, Con{B.Octets.of_list(List.reverse(&2, U32, List.reverse.go(&2, U32, t, Con{h, cur}))), done}}) == P.pr.sl.fold(B.append(t, Con{0, r}), P.pr.sl.byte(_, h, cur, done)) : P.FdtStrList}
      sl_one(t, r, Con{h, cur}, done, and_r(Bool.not(U32.is_eq(h, 0)), L.fdt.nonul(t), ok))

def sl_all(+ss: List<&2, B.Octets>, +done: List<&2, B.Octets>, +ok: {P.pr.strings_ok.ref(ss) == True{} : Bool}) -> {P.FdtStrList{Nil{}, List.reverse.go(&2, B.Octets, ss, done)} == P.pr.sl.fold(P.pr.sl.list(ss), P.FdtStrList{Nil{}, done}) : P.FdtStrList}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, t}:
      %sl_one(B.Octets.to_list(s), P.pr.sl.list(t), Nil{}, done, and_l(L.fdt.nonul(B.Octets.to_list(s)), P.pr.strings_ok.ref(t), ok)) : {P.FdtStrList{Nil{}, List.reverse.go(&2, B.Octets, Con{s, t}, done)} == _ : P.FdtStrList}
      %revrev(U32, B.Octets.to_list(s)) : {P.FdtStrList{Nil{}, List.reverse.go(&2, B.Octets, Con{s, t}, done)} == P.pr.sl.fold(P.pr.sl.list(t), P.FdtStrList{Nil{}, Con{B.Octets.of_list(_), done}}) : P.FdtStrList}
      %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(s)), s, BL.octets_of_to(s)) : {P.FdtStrList{Nil{}, List.reverse.go(&2, B.Octets, Con{s, t}, done)} == P.pr.sl.fold(P.pr.sl.list(t), P.FdtStrList{Nil{}, Con{_, done}}) : P.FdtStrList}
      sl_all(t, Con{s, done}, and_r(L.fdt.nonul(B.Octets.to_list(s)), P.pr.strings_ok.ref(t), ok))

def mask_sl(+ss: List<&2, B.Octets>) -> {P.pr.sl.list(ss) == B.mask(P.pr.sl.list(ss)) : List<&2, U32>}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, t}:
      mask_id_app(B.Octets.to_list(s), Con{0, P.pr.sl.list(t)}, mask_tl(s), mask_c0(P.pr.sl.list(t), mask_sl(t)))

def Laws.strings_round_trip(ss, ok):
  %sl_fast(ss) : {P.pr.sl.fin(P.pr.sl.fold(B.Octets.to_list(B.Octets.of_list(_)), P.FdtStrList{Nil{}, Nil{}})) == Done{ss} : Result<&2, &2, E.FdtError, List<&2, B.Octets>>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(P.pr.sl.list(ss))), B.mask(P.pr.sl.list(ss)), BL.octets_to_of(P.pr.sl.list(ss))) : {P.pr.sl.fin(P.pr.sl.fold(_, P.FdtStrList{Nil{}, Nil{}})) == Done{ss} : Result<&2, &2, E.FdtError, List<&2, B.Octets>>}
  %mask_sl(ss) : {P.pr.sl.fin(P.pr.sl.fold(_, P.FdtStrList{Nil{}, Nil{}})) == Done{ss} : Result<&2, &2, E.FdtError, List<&2, B.Octets>>}
  %sl_all(ss, Nil{}, Equal.trans(Bool, P.pr.strings_ok.ref(ss), P.FdtProp.strings_ok(ss), True{}, strings_ok_fast(ss), ok)) : {P.pr.sl.fin(_) == Done{ss} : Result<&2, &2, E.FdtError, List<&2, B.Octets>>}
  %revrev(B.Octets, ss) : {Done{_} == Done{ss} : Result<&2, &2, E.FdtError, List<&2, B.Octets>>}
  {==}

# cells: each cell's four bytes read back as the cell

def cstep(+c: U32, +rest: List<&2, U32>, +acc: List<&2, U32>) -> {P.pr.cells.go(rest, Con{c, acc}) == P.pr.cells.go(B.append(B.be32(c), rest), acc) : Result<&2, &2, E.FdtError, List<&2, U32>>}:
  match c:
    case U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WCon{c8, WCon{c9, WCon{c10, WCon{c11, WCon{c12, WCon{c13, WCon{c14, WCon{c15, WCon{c16, WCon{c17, WCon{c18, WCon{c19, WCon{c20, WCon{c21, WCon{c22, WCon{c23, WCon{c24, WCon{c25, WCon{c26, WCon{c27, WCon{c28, WCon{c29, WCon{c30, WCon{c31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def cells_rt(+cs: List<&2, U32>, +acc: List<&2, U32>) -> {Done{List.reverse(&2, U32, List.reverse.go(&2, U32, cs, acc))} == P.pr.cells.go(P.pr.cells.list(cs), acc) : Result<&2, &2, E.FdtError, List<&2, U32>>}:
  match cs:
    case Nil{}:
      {==}
    case Con{c, t}:
      %cstep(c, P.pr.cells.list(t), acc) : {Done{List.reverse(&2, U32, List.reverse.go(&2, U32, Con{c, t}, acc))} == _ : Result<&2, &2, E.FdtError, List<&2, U32>>}
      cells_rt(t, Con{c, acc})

def mask_cl(+cs: List<&2, U32>) -> {P.pr.cells.list(cs) == B.mask(P.pr.cells.list(cs)) : List<&2, U32>}:
  match cs:
    case Nil{}:
      {==}
    case Con{c, t}:
      mask_id_app(B.be32(c), P.pr.cells.list(t), mask_be32(c), mask_cl(t))

def Laws.cells_round_trip(cs):
  %cells_fast(cs) : {P.pr.cells.go(B.Octets.to_list(B.Octets.of_list(_)), Nil{}) == Done{cs} : Result<&2, &2, E.FdtError, List<&2, U32>>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(P.pr.cells.list(cs))), B.mask(P.pr.cells.list(cs)), BL.octets_to_of(P.pr.cells.list(cs))) : {P.pr.cells.go(_, Nil{}) == Done{cs} : Result<&2, &2, E.FdtError, List<&2, U32>>}
  %mask_cl(cs) : {P.pr.cells.go(_, Nil{}) == Done{cs} : Result<&2, &2, E.FdtError, List<&2, U32>>}
  %cells_rt(cs, Nil{}) : {_ == Done{cs} : Result<&2, &2, E.FdtError, List<&2, U32>>}
  %revrev(U32, cs) : {Done{_} == Done{cs} : Result<&2, &2, E.FdtError, List<&2, U32>>}
  {==}

# Lookups: a name compares equal to itself (bytes' octets_is_eq_refl)

def Laws.prop_head(nm, k, v, ps, cs):
  %Equal.sym(Bool, B.Octets.is_eq(k, k), True{}, BL.octets_is_eq_refl(k)) : {Pa.lk.prop.pick(_, v, Pa.lk.prop(ps, k)) == Some{v} : Maybe<&2, B.Octets>}
  {==}

def Laws.child_head(nm, ps, k, kps, kcs, cs):
  %Equal.sym(Bool, B.Octets.is_eq(k, k), True{}, BL.octets_is_eq_refl(k)) : {Pa.lk.or(Pa.lk.child.pick(_, T.FdtNode{k, kps, kcs}, Pa.lk.child.exact(cs, k)), Pa.lk.child.base_if(Pa.lk.has_at(B.Octets.to_list(k)), Con{T.FdtNode{k, kps, kcs}, cs}, k)) == Some{T.FdtNode{k, kps, kcs}} : Maybe<&2, T.FdtNode>}
  {==}

def Laws.find_root(root):
  {==}

# Witnesses and vectors: computed

def Laws.bad_magic_example():
  {==}

def Laws.string_ok_example():
  {==}

def Laws.strings_ok_example():
  {==}

def Laws.rsv_valid_example():
  {==}

def Laws.tokens_valid_example():
  {==}

def Laws.flat_ok_example():
  {==}

def Laws.buildable_example():
  {==}

def Laws.u32_vector():
  {==}

def Laws.u32_short():
  {==}

def Laws.u64_vector():
  {==}

def Laws.text_vector():
  {==}

def Laws.string_no_nul():
  {==}

def Laws.string_inner_nul():
  {==}

def Laws.strings_vector():
  {==}

def Laws.strings_unterminated():
  {==}

def Laws.cells_bad_length():
  {==}

def Laws.reg_vector():
  {==}

def Laws.reg_bad_cells():
  {==}

def Laws.reg_bad_length():
  {==}

def Laws.find_cpu():
  {==}

def Laws.find_cpu_base():
  {==}

def Laws.find_alias():
  {==}

def Laws.find_missing():
  {==}

def Laws.find_bootargs():
  {==}

def Laws.find_reg_uart():
  {==}

def Laws.find_reg_cpu():
  {==}

def Laws.address_cells_default():
  {==}

def Laws.size_cells_default():
  {==}

def Laws.find_phandle():
  {==}

def Laws.empty_blob():
  {==}

def Laws.zero_magic():
  {==}

def Laws.example_build():
  {==}

def Laws.example_dtc():
  {==}

def Laws.example_parse_dtc():
  {==}

def Laws.reject_short():
  {==}

def Laws.reject_version():
  {==}

def Laws.reject_v16_only17():
  {==}

def Laws.reject_last_comp():
  {==}

def Laws.reject_total_size():
  {==}

def Laws.reject_rsvmap():
  {==}

def Laws.reject_struct():
  {==}

def Laws.reject_strings():
  {==}

def Laws.reject_rsv_unterminated():
  {==}

def Laws.reject_token():
  {==}

def Laws.reject_truncated():
  {==}

def Laws.reject_after_end():
  {==}

def Laws.reject_unbalanced():
  {==}

def Laws.reject_no_root():
  {==}

def Laws.reject_prop_after_node():
  {==}

def Laws.lenient_prop_after_node():
  {==}

def Laws.reject_nameoff():
  {==}

def Laws.reject_nop():
  {==}

def Laws.accept_nop():
  {==}
