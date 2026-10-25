# Proofs. The laws over Octets go through bytes' interface laws
# (octets_of_to, octets_to_of, octets_len_list, octets_zeros_list,
# octets_append_list), never through how Octets stores its bytes: each law
# becomes a law about the byte lists Xorb.xor_list and Xorb.xor_cut_list,
# proved by induction, with XOR's algebra proved on the 32 bits of a word.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./xorblocks.bend as X
import ./LAWS.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP

# Contradictions

def xb.bdisc(+b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def xb.ft_absurd(+e: {False{} == True{} : Bool}) -> Empty:
  %e : xb.bdisc(_)
  Unit{}

def xb.ndisc(+n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

# 1 + n is not 0
def xb.succ_zero(-n: Nat, +e: {1n+n == 0n : Nat}) -> Empty:
  %e : xb.ndisc(_)
  Unit{}

def xb.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def xb.succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, n => xb.pred(n), 1n+a, 1n+b, e)

# XOR on bits and words

def xb.bx_assoc(+a: Bool, +b: Bool, +c: Bool) -> {Bool.xor(Bool.xor(a, b), c) == Bool.xor(a, Bool.xor(b, c)) : Bool}:
  match a b c:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def xb.bx_self(+a: Bool) -> {Bool.xor(a, a) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def xb.bx_zero(+a: Bool) -> {Bool.xor(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def xb.wx_assoc(n: Nat, a: Word(n), b: Word(n), c: Word(n)) -> {Word.xor(n, Word.xor(n, a, b), c) == Word.xor(n, a, Word.xor(n, b, c)) : Word(n)}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{ah, at} WCon{bh, bt} WCon{ch, ct}:
          %xb.bx_assoc(ah, bh, ch) : {WCon{Bool.xor(Bool.xor(ah, bh), ch), Word.xor(p, Word.xor(p, at, bt), ct)} == WCon{_, Word.xor(p, at, Word.xor(p, bt, ct))} : Word(1n+p)}
          %xb.wx_assoc(p, at, bt, ct) : {WCon{Bool.xor(Bool.xor(ah, bh), ch), Word.xor(p, Word.xor(p, at, bt), ct)} == WCon{Bool.xor(Bool.xor(ah, bh), ch), _} : Word(1n+p)}
          {==}

def xb.wx_self(n: Nat, a: Word(n)) -> {Word.xor(n, a, a) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{+ah, +at}:
          %xb.bx_self(ah) : {WCon{Bool.xor(ah, ah), Word.xor(p, at, at)} == WCon{_, Word.zero(p)} : Word(1n+p)}
          %xb.wx_self(p, at) : {WCon{Bool.xor(ah, ah), Word.xor(p, at, at)} == WCon{Bool.xor(ah, ah), _} : Word(1n+p)}
          {==}

def xb.wx_zero(n: Nat, a: Word(n)) -> {Word.xor(n, a, Word.zero(n)) == a : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{+ah, +at}:
          %xb.bx_zero(ah) : {WCon{Bool.xor(ah, False{}), Word.xor(p, at, Word.zero(p))} == WCon{_, at} : Word(1n+p)}
          %xb.wx_zero(p, at) : {WCon{Bool.xor(ah, False{}), Word.xor(p, at, Word.zero(p))} == WCon{Bool.xor(ah, False{}), _} : Word(1n+p)}
          {==}

def xb.ux_assoc(a: U32, b: U32, c: U32) -> {U32.xor(U32.xor(a, b), c) == U32.xor(a, U32.xor(b, c)) : U32}:
  match a b c:
    case U32{x} U32{y} U32{z}:
      %xb.wx_assoc(32n, x, y, z) : {U32{Word.xor(32n, Word.xor(32n, x, y), z)} == U32{_} : U32}
      {==}

def xb.ux_self(a: U32) -> {U32.xor(a, a) == 0 : U32}:
  match a:
    case U32{+x}:
      %xb.wx_self(32n, x) : {U32{Word.xor(32n, x, x)} == U32{_} : U32}
      {==}

def xb.ux_zero(a: U32) -> {U32.xor(a, 0) == a : U32}:
  match a:
    case U32{+x}:
      %xb.wx_zero(32n, x) : {U32{Word.xor(32n, x, Word.zero(32n))} == U32{_} : U32}
      {==}

# a byte XOR a byte is a byte; a byte's byte is itself
def xb.byte_xor(x: U32, y: U32) -> {B.byte(U32.xor(B.byte(x), B.byte(y))) == U32.xor(B.byte(x), B.byte(y)) : U32}:
  match x y:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, xr}}}}}}}}} U32{WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, yr}}}}}}}}}:
      {==}

def xb.byte_byte(x: U32) -> {B.byte(B.byte(x)) == B.byte(x) : U32}:
  match x:
    case U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, xr}}}}}}}}}:
      {==}

# Lists: the masking lemmas

def xb.mask_mask(xs: List<&2, U32>) -> {B.mask(B.mask(xs)) == B.mask(xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %xb.byte_byte(h) : {Con{B.byte(B.byte(h)), B.mask(B.mask(t))} == Con{_, B.mask(t)} : List<&2, U32>}
      %xb.mask_mask(t) : {Con{B.byte(B.byte(h)), B.mask(B.mask(t))} == Con{B.byte(B.byte(h)), _} : List<&2, U32>}
      {==}

def xb.pad_mask(xs: List<&2, U32>, ys: List<&2, U32>) -> {B.mask(X.Xorb.xor_list(B.mask(xs), B.mask(ys))) == X.Xorb.xor_list(B.mask(xs), B.mask(ys)) : List<&2, U32>}:
  match xs ys:
    case Nil{} _:
      xb.mask_mask(ys)
    case Con{+x, +s} Nil{}:
      %xb.byte_byte(x) : {Con{B.byte(B.byte(x)), B.mask(B.mask(s))} == Con{_, B.mask(s)} : List<&2, U32>}
      %xb.mask_mask(s) : {Con{B.byte(B.byte(x)), B.mask(B.mask(s))} == Con{B.byte(B.byte(x)), _} : List<&2, U32>}
      {==}
    case Con{+x, +s} Con{+y, +t}:
      %xb.byte_xor(x, y) : {Con{B.byte(U32.xor(B.byte(x), B.byte(y))), B.mask(X.Xorb.xor_list(B.mask(s), B.mask(t)))} == Con{_, X.Xorb.xor_list(B.mask(s), B.mask(t))} : List<&2, U32>}
      %xb.pad_mask(s, t) : {Con{B.byte(U32.xor(B.byte(x), B.byte(y))), B.mask(X.Xorb.xor_list(B.mask(s), B.mask(t)))} == Con{B.byte(U32.xor(B.byte(x), B.byte(y))), _} : List<&2, U32>}
      {==}

def xb.cut_mask(xs: List<&2, U32>, ys: List<&2, U32>) -> {B.mask(X.Xorb.xor_cut_list(B.mask(xs), B.mask(ys))) == X.Xorb.xor_cut_list(B.mask(xs), B.mask(ys)) : List<&2, U32>}:
  match xs ys:
    case Nil{} _:
      {==}
    case Con{+x, +s} Nil{}:
      {==}
    case Con{+x, +s} Con{+y, +t}:
      %xb.byte_xor(x, y) : {Con{B.byte(U32.xor(B.byte(x), B.byte(y))), B.mask(X.Xorb.xor_cut_list(B.mask(s), B.mask(t)))} == Con{_, X.Xorb.xor_cut_list(B.mask(s), B.mask(t))} : List<&2, U32>}
      %xb.cut_mask(s, t) : {Con{B.byte(U32.xor(B.byte(x), B.byte(y))), B.mask(X.Xorb.xor_cut_list(B.mask(s), B.mask(t)))} == Con{B.byte(U32.xor(B.byte(x), B.byte(y))), _} : List<&2, U32>}
      {==}

# Lists: the fast forms are the structural forms

def xb.pad_go(a: List<&2, U32>, b: List<&2, U32>, acc: List<&2, U32>) -> {B.rev_onto(acc, X.Xorb.xor_list(a, b)) == X.xorb.pad.go(a, b, acc) : List<&2, U32>}:
  match a b:
    case Nil{} _:
      {==}
    case Con{x, s} Nil{}:
      {==}
    case Con{x, s} Con{y, t}:
      xb.pad_go(s, t, Con{U32.xor(x, y), acc})

def xb.cut_go(a: List<&2, U32>, b: List<&2, U32>, acc: List<&2, U32>) -> {B.rev_onto(acc, X.Xorb.xor_cut_list(a, b)) == X.xorb.cut.go(a, b, acc) : List<&2, U32>}:
  match a b:
    case Nil{} _:
      {==}
    case Con{x, s} Nil{}:
      {==}
    case Con{x, s} Con{y, t}:
      xb.cut_go(s, t, Con{U32.xor(x, y), acc})

# Lists: XOR's algebra

def xb.pad_comm(a: List<&2, U32>, b: List<&2, U32>) -> {X.Xorb.xor_list(a, b) == X.Xorb.xor_list(b, a) : List<&2, U32>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      {==}
    case Con{x, s} Nil{}:
      {==}
    case Con{+x, s} Con{+y, t}:
      %UL.u32_xor_comm(x, y) : {Con{U32.xor(x, y), X.Xorb.xor_list(s, t)} == Con{_, X.Xorb.xor_list(t, s)} : List<&2, U32>}
      %xb.pad_comm(s, t) : {Con{U32.xor(x, y), X.Xorb.xor_list(s, t)} == Con{U32.xor(x, y), _} : List<&2, U32>}
      {==}

def xb.pad_assoc(a: List<&2, U32>, b: List<&2, U32>, c: List<&2, U32>) -> {X.Xorb.xor_list(X.Xorb.xor_list(a, b), c) == X.Xorb.xor_list(a, X.Xorb.xor_list(b, c)) : List<&2, U32>}:
  match a b c:
    case Nil{} _ _:
      {==}
    case Con{x, s} Nil{} _:
      {==}
    case Con{x, s} Con{y, t} Nil{}:
      {==}
    case Con{+x, s} Con{+y, t} Con{+z, u}:
      %xb.ux_assoc(x, y, z) : {Con{U32.xor(U32.xor(x, y), z), X.Xorb.xor_list(X.Xorb.xor_list(s, t), u)} == Con{_, X.Xorb.xor_list(s, X.Xorb.xor_list(t, u))} : List<&2, U32>}
      %xb.pad_assoc(s, t, u) : {Con{U32.xor(U32.xor(x, y), z), X.Xorb.xor_list(X.Xorb.xor_list(s, t), u)} == Con{U32.xor(U32.xor(x, y), z), _} : List<&2, U32>}
      {==}

def xb.pad_nil(a: List<&2, U32>) -> {X.Xorb.xor_list(a, Nil{}) == a : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{x, s}:
      {==}

def xb.pad_self(a: List<&2, U32>) -> {X.Xorb.xor_list(a, a) == B.zeros(B.len(a)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +s}:
      %xb.ux_self(x) : {Con{U32.xor(x, x), X.Xorb.xor_list(s, s)} == Con{_, B.zeros(B.len(s))} : List<&2, U32>}
      %xb.pad_self(s) : {Con{U32.xor(x, x), X.Xorb.xor_list(s, s)} == Con{U32.xor(x, x), _} : List<&2, U32>}
      {==}

def xb.pad_zeros(n: Nat, a: List<&2, U32>, le: {Nat.is_le(n, B.len(a)) == True{} : Bool}) -> {X.Xorb.xor_list(a, B.zeros(n)) == a : List<&2, U32>}:
  match n:
    case 0n:
      xb.pad_nil(a)
    case 1n+p:
      match a:
        case Nil{}:
          Empty.absurd({X.Xorb.xor_list(Nil{}, B.zeros(1n+p)) == Nil{} : List<&2, U32>}, xb.ft_absurd(le))
        case Con{+x, +s}:
          %xb.ux_zero(x) : {Con{U32.xor(x, 0), X.Xorb.xor_list(s, B.zeros(p))} == Con{_, s} : List<&2, U32>}
          %xb.pad_zeros(p, s, le) : {Con{U32.xor(x, 0), X.Xorb.xor_list(s, B.zeros(p))} == Con{U32.xor(x, 0), _} : List<&2, U32>}
          {==}

def xb.pad_len(a: List<&2, U32>, b: List<&2, U32>) -> {B.len(X.Xorb.xor_list(a, b)) == Nat.max(B.len(a), B.len(b)) : Nat}:
  match a b:
    case Nil{} _:
      {==}
    case Con{x, s} Nil{}:
      {==}
    case Con{x, s} Con{y, t}:
      %xb.pad_len(s, t) : {1n+B.len(X.Xorb.xor_list(s, t)) == 1n+_ : Nat}
      {==}

def xb.pad_app(a1: List<&2, U32>, a2: List<&2, U32>, b1: List<&2, U32>, b2: List<&2, U32>, same: {B.len(a1) == B.len(b1) : Nat}) -> {X.Xorb.xor_list(B.append(a1, a2), B.append(b1, b2)) == B.append(X.Xorb.xor_list(a1, b1), X.Xorb.xor_list(a2, b2)) : List<&2, U32>}:
  match a1 b1:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      Empty.absurd({X.Xorb.xor_list(B.append(Nil{}, a2), B.append(Con{y, t}, b2)) == B.append(X.Xorb.xor_list(Nil{}, Con{y, t}), X.Xorb.xor_list(a2, b2)) : List<&2, U32>}, xb.succ_zero(B.len(t), Equal.sym(Nat, 0n, 1n+B.len(t), same)))
    case Con{x, s} Nil{}:
      Empty.absurd({X.Xorb.xor_list(B.append(Con{x, s}, a2), B.append(Nil{}, b2)) == B.append(X.Xorb.xor_list(Con{x, s}, Nil{}), X.Xorb.xor_list(a2, b2)) : List<&2, U32>}, xb.succ_zero(B.len(s), same))
    case Con{+x, s} Con{+y, t}:
      %xb.pad_app(s, a2, t, b2, xb.succ_inj(B.len(s), B.len(t), same)) : {Con{U32.xor(x, y), X.Xorb.xor_list(B.append(s, a2), B.append(t, b2))} == Con{U32.xor(x, y), _} : List<&2, U32>}
      {==}

def xb.cut_comm(a: List<&2, U32>, b: List<&2, U32>) -> {X.Xorb.xor_cut_list(a, b) == X.Xorb.xor_cut_list(b, a) : List<&2, U32>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      {==}
    case Con{x, s} Nil{}:
      {==}
    case Con{+x, s} Con{+y, t}:
      %UL.u32_xor_comm(x, y) : {Con{U32.xor(x, y), X.Xorb.xor_cut_list(s, t)} == Con{_, X.Xorb.xor_cut_list(t, s)} : List<&2, U32>}
      %xb.cut_comm(s, t) : {Con{U32.xor(x, y), X.Xorb.xor_cut_list(s, t)} == Con{U32.xor(x, y), _} : List<&2, U32>}
      {==}

def xb.cut_assoc(a: List<&2, U32>, b: List<&2, U32>, c: List<&2, U32>) -> {X.Xorb.xor_cut_list(X.Xorb.xor_cut_list(a, b), c) == X.Xorb.xor_cut_list(a, X.Xorb.xor_cut_list(b, c)) : List<&2, U32>}:
  match a b c:
    case Nil{} _ _:
      {==}
    case Con{x, s} Nil{} _:
      {==}
    case Con{x, s} Con{y, t} Nil{}:
      {==}
    case Con{+x, s} Con{+y, t} Con{+z, u}:
      %xb.ux_assoc(x, y, z) : {Con{U32.xor(U32.xor(x, y), z), X.Xorb.xor_cut_list(X.Xorb.xor_cut_list(s, t), u)} == Con{_, X.Xorb.xor_cut_list(s, X.Xorb.xor_cut_list(t, u))} : List<&2, U32>}
      %xb.cut_assoc(s, t, u) : {Con{U32.xor(U32.xor(x, y), z), X.Xorb.xor_cut_list(X.Xorb.xor_cut_list(s, t), u)} == Con{U32.xor(U32.xor(x, y), z), _} : List<&2, U32>}
      {==}

def xb.cut_len(a: List<&2, U32>, b: List<&2, U32>) -> {B.len(X.Xorb.xor_cut_list(a, b)) == Nat.min(B.len(a), B.len(b)) : Nat}:
  match a b:
    case Nil{} _:
      {==}
    case Con{x, s} Nil{}:
      {==}
    case Con{x, s} Con{y, t}:
      %xb.cut_len(s, t) : {1n+B.len(X.Xorb.xor_cut_list(s, t)) == 1n+_ : Nat}
      {==}

def xb.cut_pad(a: List<&2, U32>, b: List<&2, U32>, same: {B.len(a) == B.len(b) : Nat}) -> {X.Xorb.xor_cut_list(a, b) == X.Xorb.xor_list(a, b) : List<&2, U32>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      Empty.absurd({X.Xorb.xor_cut_list(Nil{}, Con{y, t}) == X.Xorb.xor_list(Nil{}, Con{y, t}) : List<&2, U32>}, xb.succ_zero(B.len(t), Equal.sym(Nat, 0n, 1n+B.len(t), same)))
    case Con{x, s} Nil{}:
      Empty.absurd({X.Xorb.xor_cut_list(Con{x, s}, Nil{}) == X.Xorb.xor_list(Con{x, s}, Nil{}) : List<&2, U32>}, xb.succ_zero(B.len(s), same))
    case Con{+x, s} Con{+y, t}:
      %xb.cut_pad(s, t, xb.succ_inj(B.len(s), B.len(t), same)) : {Con{U32.xor(x, y), X.Xorb.xor_cut_list(s, t)} == Con{U32.xor(x, y), _} : List<&2, U32>}
      {==}

# From Octets to lists and back

# an Octets' list is masked
def xb.tl_mask(+o: B.Octets) -> {B.mask(B.Octets.to_list(o)) == B.Octets.to_list(o) : List<&2, U32>}:
  %BL.octets_of_to(o) : {B.mask(B.Octets.to_list(o)) == B.Octets.to_list(_) : List<&2, U32>}
  Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(o))), B.mask(B.Octets.to_list(o)), BL.octets_to_of(B.Octets.to_list(o)))

# two Octets with the same list are the same
def xb.lift(+x: B.Octets, +y: B.Octets, e: {B.Octets.to_list(x) == B.Octets.to_list(y) : List<&2, U32>}) -> {x == y : B.Octets}:
  %BL.octets_of_to(x) : {_ == y : B.Octets}
  %BL.octets_of_to(y) : {B.Octets.of_list(B.Octets.to_list(x)) == _ : B.Octets}
  %e : {B.Octets.of_list(B.Octets.to_list(x)) == B.Octets.of_list(_) : B.Octets}
  {==}

def xb.to_xor(+a: B.Octets, +b: B.Octets) -> {X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b)) == B.Octets.to_list(X.Xorb.xor(a, b)) : List<&2, U32>}:
  %xb.pad_go(B.Octets.to_list(a), B.Octets.to_list(b), Nil{}) : {X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b)) == B.Octets.to_list(B.Octets.of_list(_)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b)))), B.mask(X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b))), BL.octets_to_of(X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b)))) : {X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b)) == _ : List<&2, U32>}
  %xb.tl_mask(a) : {X.Xorb.xor_list(_, B.Octets.to_list(b)) == B.mask(X.Xorb.xor_list(_, B.Octets.to_list(b))) : List<&2, U32>}
  %xb.tl_mask(b) : {X.Xorb.xor_list(B.mask(B.Octets.to_list(a)), _) == B.mask(X.Xorb.xor_list(B.mask(B.Octets.to_list(a)), _)) : List<&2, U32>}
  Equal.sym(List<&2, U32>, B.mask(X.Xorb.xor_list(B.mask(B.Octets.to_list(a)), B.mask(B.Octets.to_list(b)))), X.Xorb.xor_list(B.mask(B.Octets.to_list(a)), B.mask(B.Octets.to_list(b))), xb.pad_mask(B.Octets.to_list(a), B.Octets.to_list(b)))

def xb.to_cut(+a: B.Octets, +b: B.Octets) -> {X.Xorb.xor_cut_list(B.Octets.to_list(a), B.Octets.to_list(b)) == B.Octets.to_list(X.Xorb.xor_cut(a, b)) : List<&2, U32>}:
  %xb.cut_go(B.Octets.to_list(a), B.Octets.to_list(b), Nil{}) : {X.Xorb.xor_cut_list(B.Octets.to_list(a), B.Octets.to_list(b)) == B.Octets.to_list(B.Octets.of_list(_)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(X.Xorb.xor_cut_list(B.Octets.to_list(a), B.Octets.to_list(b)))), B.mask(X.Xorb.xor_cut_list(B.Octets.to_list(a), B.Octets.to_list(b))), BL.octets_to_of(X.Xorb.xor_cut_list(B.Octets.to_list(a), B.Octets.to_list(b)))) : {X.Xorb.xor_cut_list(B.Octets.to_list(a), B.Octets.to_list(b)) == _ : List<&2, U32>}
  %xb.tl_mask(a) : {X.Xorb.xor_cut_list(_, B.Octets.to_list(b)) == B.mask(X.Xorb.xor_cut_list(_, B.Octets.to_list(b))) : List<&2, U32>}
  %xb.tl_mask(b) : {X.Xorb.xor_cut_list(B.mask(B.Octets.to_list(a)), _) == B.mask(X.Xorb.xor_cut_list(B.mask(B.Octets.to_list(a)), _)) : List<&2, U32>}
  Equal.sym(List<&2, U32>, B.mask(X.Xorb.xor_cut_list(B.mask(B.Octets.to_list(a)), B.mask(B.Octets.to_list(b)))), X.Xorb.xor_cut_list(B.mask(B.Octets.to_list(a)), B.mask(B.Octets.to_list(b))), xb.cut_mask(B.Octets.to_list(a), B.Octets.to_list(b)))

def xb.len_list(+o: B.Octets) -> {B.len(B.Octets.to_list(o)) == B.Octets.len(o) : Nat}:
  Equal.sym(Nat, B.Octets.len(o), B.len(B.Octets.to_list(o)), BL.octets_len_list(o))

# The laws

def Laws.xor_list(a, b):
  Equal.sym(List<&2, U32>, X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b)), B.Octets.to_list(X.Xorb.xor(a, b)), xb.to_xor(a, b))

def Laws.xor_cut_list(a, b):
  Equal.sym(List<&2, U32>, X.Xorb.xor_cut_list(B.Octets.to_list(a), B.Octets.to_list(b)), B.Octets.to_list(X.Xorb.xor_cut(a, b)), xb.to_cut(a, b))

def xb.comm_list(+a: B.Octets, +b: B.Octets) -> {B.Octets.to_list(X.Xorb.xor(a, b)) == B.Octets.to_list(X.Xorb.xor(b, a)) : List<&2, U32>}:
  %xb.to_xor(a, b) : {_ == B.Octets.to_list(X.Xorb.xor(b, a)) : List<&2, U32>}
  %xb.to_xor(b, a) : {X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b)) == _ : List<&2, U32>}
  xb.pad_comm(B.Octets.to_list(a), B.Octets.to_list(b))

def Laws.xor_comm(a, b):
  xb.lift(X.Xorb.xor(a, b), X.Xorb.xor(b, a), xb.comm_list(a, b))

def xb.assoc_list(+a: B.Octets, +b: B.Octets, +c: B.Octets) -> {B.Octets.to_list(X.Xorb.xor(X.Xorb.xor(a, b), c)) == B.Octets.to_list(X.Xorb.xor(a, X.Xorb.xor(b, c))) : List<&2, U32>}:
  %xb.to_xor(X.Xorb.xor(a, b), c) : {_ == B.Octets.to_list(X.Xorb.xor(a, X.Xorb.xor(b, c))) : List<&2, U32>}
  %xb.to_xor(a, b) : {X.Xorb.xor_list(_, B.Octets.to_list(c)) == B.Octets.to_list(X.Xorb.xor(a, X.Xorb.xor(b, c))) : List<&2, U32>}
  %xb.to_xor(a, X.Xorb.xor(b, c)) : {X.Xorb.xor_list(X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b)), B.Octets.to_list(c)) == _ : List<&2, U32>}
  %xb.to_xor(b, c) : {X.Xorb.xor_list(X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b)), B.Octets.to_list(c)) == X.Xorb.xor_list(B.Octets.to_list(a), _) : List<&2, U32>}
  xb.pad_assoc(B.Octets.to_list(a), B.Octets.to_list(b), B.Octets.to_list(c))

def Laws.xor_assoc(a, b, c):
  xb.lift(X.Xorb.xor(X.Xorb.xor(a, b), c), X.Xorb.xor(a, X.Xorb.xor(b, c)), xb.assoc_list(a, b, c))

def xb.empty_list(+a: B.Octets) -> {B.Octets.to_list(X.Xorb.xor(a, B.Octets.empty())) == B.Octets.to_list(a) : List<&2, U32>}:
  %xb.to_xor(a, B.Octets.empty()) : {_ == B.Octets.to_list(a) : List<&2, U32>}
  xb.pad_nil(B.Octets.to_list(a))

def Laws.xor_empty(a):
  xb.lift(X.Xorb.xor(a, B.Octets.empty()), a, xb.empty_list(a))

def xb.self_list(+a: B.Octets) -> {B.Octets.to_list(X.Xorb.xor(a, a)) == B.Octets.to_list(B.Octets.zeros(B.Octets.len(a))) : List<&2, U32>}:
  %xb.to_xor(a, a) : {_ == B.Octets.to_list(B.Octets.zeros(B.Octets.len(a))) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.zeros(B.Octets.len(a))), B.zeros(B.Octets.len(a)), BL.octets_zeros_list(B.Octets.len(a))) : {X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(a)) == _ : List<&2, U32>}
  %xb.len_list(a) : {X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(a)) == B.zeros(_) : List<&2, U32>}
  xb.pad_self(B.Octets.to_list(a))

def Laws.xor_self(a):
  xb.lift(X.Xorb.xor(a, a), B.Octets.zeros(B.Octets.len(a)), xb.self_list(a))

def xb.le_list(+a: B.Octets, +n: Nat, le: {Nat.is_le(n, B.Octets.len(a)) == True{} : Bool}) -> {Nat.is_le(n, B.len(B.Octets.to_list(a))) == True{} : Bool}:
  %BL.octets_len_list(a) : {Nat.is_le(n, _) == True{} : Bool}
  le

def xb.zeros_list(+a: B.Octets, +n: Nat, le: {Nat.is_le(n, B.Octets.len(a)) == True{} : Bool}) -> {B.Octets.to_list(X.Xorb.xor(a, B.Octets.zeros(n))) == B.Octets.to_list(a) : List<&2, U32>}:
  %xb.to_xor(a, B.Octets.zeros(n)) : {_ == B.Octets.to_list(a) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.zeros(n)), B.zeros(n), BL.octets_zeros_list(n)) : {X.Xorb.xor_list(B.Octets.to_list(a), _) == B.Octets.to_list(a) : List<&2, U32>}
  xb.pad_zeros(n, B.Octets.to_list(a), xb.le_list(a, n, le))

def Laws.xor_zeros(a, n, le):
  xb.lift(X.Xorb.xor(a, B.Octets.zeros(n)), a, xb.zeros_list(a, n, le))

def Laws.xor_len(a, b):
  %xb.len_list(X.Xorb.xor(a, b)) : {_ == Nat.max(B.Octets.len(a), B.Octets.len(b)) : Nat}
  %xb.to_xor(a, b) : {B.len(_) == Nat.max(B.Octets.len(a), B.Octets.len(b)) : Nat}
  %xb.len_list(a) : {B.len(X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b))) == Nat.max(_, B.Octets.len(b)) : Nat}
  %xb.len_list(b) : {B.len(X.Xorb.xor_list(B.Octets.to_list(a), B.Octets.to_list(b))) == Nat.max(B.len(B.Octets.to_list(a)), _) : Nat}
  xb.pad_len(B.Octets.to_list(a), B.Octets.to_list(b))

# equal lengths of two byte strings are equal lengths of their lists
def xb.same_list(+a: B.Octets, +b: B.Octets, same: {B.Octets.len(a) == B.Octets.len(b) : Nat}) -> {B.len(B.Octets.to_list(a)) == B.len(B.Octets.to_list(b)) : Nat}:
  %BL.octets_len_list(a) : {_ == B.len(B.Octets.to_list(b)) : Nat}
  %BL.octets_len_list(b) : {B.Octets.len(a) == _ : Nat}
  same

def xb.app_sym(+a: B.Octets, +b: B.Octets) -> {B.append(B.Octets.to_list(a), B.Octets.to_list(b)) == B.Octets.to_list(B.Octets.append(a, b)) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b))

def xb.append_list(+a1: B.Octets, +a2: B.Octets, +b1: B.Octets, +b2: B.Octets, same: {B.Octets.len(a1) == B.Octets.len(b1) : Nat}) -> {B.Octets.to_list(X.Xorb.xor(B.Octets.append(a1, a2), B.Octets.append(b1, b2))) == B.Octets.to_list(B.Octets.append(X.Xorb.xor(a1, b1), X.Xorb.xor(a2, b2))) : List<&2, U32>}:
  %xb.to_xor(B.Octets.append(a1, a2), B.Octets.append(b1, b2)) : {_ == B.Octets.to_list(B.Octets.append(X.Xorb.xor(a1, b1), X.Xorb.xor(a2, b2))) : List<&2, U32>}
  %xb.app_sym(a1, a2) : {X.Xorb.xor_list(_, B.Octets.to_list(B.Octets.append(b1, b2))) == B.Octets.to_list(B.Octets.append(X.Xorb.xor(a1, b1), X.Xorb.xor(a2, b2))) : List<&2, U32>}
  %xb.app_sym(b1, b2) : {X.Xorb.xor_list(B.append(B.Octets.to_list(a1), B.Octets.to_list(a2)), _) == B.Octets.to_list(B.Octets.append(X.Xorb.xor(a1, b1), X.Xorb.xor(a2, b2))) : List<&2, U32>}
  %xb.app_sym(X.Xorb.xor(a1, b1), X.Xorb.xor(a2, b2)) : {X.Xorb.xor_list(B.append(B.Octets.to_list(a1), B.Octets.to_list(a2)), B.append(B.Octets.to_list(b1), B.Octets.to_list(b2))) == _ : List<&2, U32>}
  %xb.to_xor(a1, b1) : {X.Xorb.xor_list(B.append(B.Octets.to_list(a1), B.Octets.to_list(a2)), B.append(B.Octets.to_list(b1), B.Octets.to_list(b2))) == B.append(_, B.Octets.to_list(X.Xorb.xor(a2, b2))) : List<&2, U32>}
  %xb.to_xor(a2, b2) : {X.Xorb.xor_list(B.append(B.Octets.to_list(a1), B.Octets.to_list(a2)), B.append(B.Octets.to_list(b1), B.Octets.to_list(b2))) == B.append(X.Xorb.xor_list(B.Octets.to_list(a1), B.Octets.to_list(b1)), _) : List<&2, U32>}
  xb.pad_app(B.Octets.to_list(a1), B.Octets.to_list(a2), B.Octets.to_list(b1), B.Octets.to_list(b2), xb.same_list(a1, b1, same))

def Laws.xor_append(a1, a2, b1, b2, same):
  xb.lift(X.Xorb.xor(B.Octets.append(a1, a2), B.Octets.append(b1, b2)), B.Octets.append(X.Xorb.xor(a1, b1), X.Xorb.xor(a2, b2)), xb.append_list(a1, a2, b1, b2, same))

def xb.cut_comm_list(+a: B.Octets, +b: B.Octets) -> {B.Octets.to_list(X.Xorb.xor_cut(a, b)) == B.Octets.to_list(X.Xorb.xor_cut(b, a)) : List<&2, U32>}:
  %xb.to_cut(a, b) : {_ == B.Octets.to_list(X.Xorb.xor_cut(b, a)) : List<&2, U32>}
  %xb.to_cut(b, a) : {X.Xorb.xor_cut_list(B.Octets.to_list(a), B.Octets.to_list(b)) == _ : List<&2, U32>}
  xb.cut_comm(B.Octets.to_list(a), B.Octets.to_list(b))

def Laws.xor_cut_comm(a, b):
  xb.lift(X.Xorb.xor_cut(a, b), X.Xorb.xor_cut(b, a), xb.cut_comm_list(a, b))

def xb.cut_assoc_list(+a: B.Octets, +b: B.Octets, +c: B.Octets) -> {B.Octets.to_list(X.Xorb.xor_cut(X.Xorb.xor_cut(a, b), c)) == B.Octets.to_list(X.Xorb.xor_cut(a, X.Xorb.xor_cut(b, c))) : List<&2, U32>}:
  %xb.to_cut(X.Xorb.xor_cut(a, b), c) : {_ == B.Octets.to_list(X.Xorb.xor_cut(a, X.Xorb.xor_cut(b, c))) : List<&2, U32>}
  %xb.to_cut(a, b) : {X.Xorb.xor_cut_list(_, B.Octets.to_list(c)) == B.Octets.to_list(X.Xorb.xor_cut(a, X.Xorb.xor_cut(b, c))) : List<&2, U32>}
  %xb.to_cut(a, X.Xorb.xor_cut(b, c)) : {X.Xorb.xor_cut_list(X.Xorb.xor_cut_list(B.Octets.to_list(a), B.Octets.to_list(b)), B.Octets.to_list(c)) == _ : List<&2, U32>}
  %xb.to_cut(b, c) : {X.Xorb.xor_cut_list(X.Xorb.xor_cut_list(B.Octets.to_list(a), B.Octets.to_list(b)), B.Octets.to_list(c)) == X.Xorb.xor_cut_list(B.Octets.to_list(a), _) : List<&2, U32>}
  xb.cut_assoc(B.Octets.to_list(a), B.Octets.to_list(b), B.Octets.to_list(c))

def Laws.xor_cut_assoc(a, b, c):
  xb.lift(X.Xorb.xor_cut(X.Xorb.xor_cut(a, b), c), X.Xorb.xor_cut(a, X.Xorb.xor_cut(b, c)), xb.cut_assoc_list(a, b, c))

def Laws.xor_cut_len(a, b):
  %xb.len_list(X.Xorb.xor_cut(a, b)) : {_ == Nat.min(B.Octets.len(a), B.Octets.len(b)) : Nat}
  %xb.to_cut(a, b) : {B.len(_) == Nat.min(B.Octets.len(a), B.Octets.len(b)) : Nat}
  %xb.len_list(a) : {B.len(X.Xorb.xor_cut_list(B.Octets.to_list(a), B.Octets.to_list(b))) == Nat.min(_, B.Octets.len(b)) : Nat}
  %xb.len_list(b) : {B.len(X.Xorb.xor_cut_list(B.Octets.to_list(a), B.Octets.to_list(b))) == Nat.min(B.len(B.Octets.to_list(a)), _) : Nat}
  xb.cut_len(B.Octets.to_list(a), B.Octets.to_list(b))

def xb.cut_same_list(+a: B.Octets, +b: B.Octets, same: {B.Octets.len(a) == B.Octets.len(b) : Nat}) -> {B.Octets.to_list(X.Xorb.xor_cut(a, b)) == B.Octets.to_list(X.Xorb.xor(a, b)) : List<&2, U32>}:
  %xb.to_cut(a, b) : {_ == B.Octets.to_list(X.Xorb.xor(a, b)) : List<&2, U32>}
  %xb.to_xor(a, b) : {X.Xorb.xor_cut_list(B.Octets.to_list(a), B.Octets.to_list(b)) == _ : List<&2, U32>}
  xb.cut_pad(B.Octets.to_list(a), B.Octets.to_list(b), xb.same_list(a, b, same))

def Laws.xor_cut_same(a, b, same):
  xb.lift(X.Xorb.xor_cut(a, b), X.Xorb.xor(a, b), xb.cut_same_list(a, b, same))

def Laws.xor_with_longer(a, b):
  {==}

def Laws.xor_with_shorter(a, b):
  {==}

def Laws.into_nil(d):
  {==}

def Laws.into_cons(d, s, r):
  {==}

# s == empty XOR s
def xb.empty_l(+s: B.Octets) -> {s == X.Xorb.xor(B.Octets.empty(), s) : B.Octets}:
  Equal.trans(B.Octets, s, X.Xorb.xor(s, B.Octets.empty()), X.Xorb.xor(B.Octets.empty(), s), Equal.sym(B.Octets, X.Xorb.xor(s, B.Octets.empty()), s, Laws.xor_empty(s)), Laws.xor_comm(s, B.Octets.empty()))

def xb.into_all(srcs: List<&2, B.Octets>, +d: B.Octets) -> {X.xorb.into.go(srcs, d) == X.Xorb.xor(d, X.xorb.into.go(srcs, B.Octets.empty())) : B.Octets}:
  match srcs:
    case Nil{}:
      Equal.sym(B.Octets, X.Xorb.xor(d, B.Octets.empty()), d, Laws.xor_empty(d))
    case Con{+s, +r}:
      %Equal.sym(B.Octets, X.xorb.into.go(r, X.Xorb.xor(d, s)), X.Xorb.xor(X.Xorb.xor(d, s), X.xorb.into.go(r, B.Octets.empty())), xb.into_all(r, X.Xorb.xor(d, s))) : {_ == X.Xorb.xor(d, X.xorb.into.go(r, X.Xorb.xor(B.Octets.empty(), s))) : B.Octets}
      %Equal.sym(B.Octets, X.xorb.into.go(r, X.Xorb.xor(B.Octets.empty(), s)), X.Xorb.xor(X.Xorb.xor(B.Octets.empty(), s), X.xorb.into.go(r, B.Octets.empty())), xb.into_all(r, X.Xorb.xor(B.Octets.empty(), s))) : {X.Xorb.xor(X.Xorb.xor(d, s), X.xorb.into.go(r, B.Octets.empty())) == X.Xorb.xor(d, _) : B.Octets}
      %xb.empty_l(s) : {X.Xorb.xor(X.Xorb.xor(d, s), X.xorb.into.go(r, B.Octets.empty())) == X.Xorb.xor(d, X.Xorb.xor(_, X.xorb.into.go(r, B.Octets.empty()))) : B.Octets}
      Laws.xor_assoc(d, s, X.xorb.into.go(r, B.Octets.empty()))

def Laws.into_all(d, srcs):
  xb.into_all(srcs, d)

def Laws.v_xor():
  {==}

def Laws.v_xor_cut():
  {==}

def Laws.v_into():
  {==}
