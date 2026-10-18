# Proof helpers for bend-osdev-packing: a W64 value as its 64 bits and back
# (field.bend), through word64's interface law parts_of.
import Base
import ../word64/word64.bend as W
import ../word64/LAWS.bend as WL
import ../word64/PROOF.bend as WP
import ./field.bend as F
import ./proof_list.bend as PL

def pw.drop0(xs: List<&2, Bool>) -> {List.drop(&2, Bool, xs, 0n) == xs : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case Con{b, t}:
      {==}

def pw.wb(+n: Nat, w: Word(n), -rest: List<&2, Bool>) -> {F.packing.bits_word(n, F.packing.word_bits(n, w, rest)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+b, +t}:
          %pw.wb(p, t, rest) : {WCon{b, F.packing.bits_word(p, F.packing.word_bits(p, t, rest))} == WCon{b, _} : Word(1n+p)}
          {==}

def pw.dwb(+n: Nat, w: Word(n), +rest: List<&2, Bool>) -> {List.drop(&2, Bool, F.packing.word_bits(n, w, rest), n) == rest : List<&2, Bool>}:
  match n:
    case 0n:
      pw.drop0(rest)
    case 1n+p:
      match w:
        case WCon{b, t}:
          pw.dwb(p, t, rest)

def pw.u32_rt(x: U32, -rest: List<&2, Bool>) -> {U32{F.packing.bits_word(32n, F.packing.u32_bits(x, rest))} == x : U32}:
  match x:
    case U32{+w}:
      Equal.cong(Word(32n), U32, z => U32{z}, F.packing.bits_word(32n, F.packing.word_bits(32n, w, rest)), w, pw.wb(32n, w, rest))

def pw.u32_drop(x: U32, +rest: List<&2, Bool>) -> {List.drop(&2, Bool, F.packing.u32_bits(x, rest), 32n) == rest : List<&2, Bool>}:
  match x:
    case U32{w}:
      pw.dwb(32n, w, rest)

def pw.val(+v: W.W64) -> {F.packing.bits_w64(F.packing.w64_bits(v)) == v : W.W64}:
  +r = F.packing.u32_bits(W.W64.hi(v), Nil{})
  +l = F.packing.u32_bits(W.W64.lo(v), r)
  %Equal.sym(List<&2, Bool>, List.drop(&2, Bool, l, 32n), r, pw.u32_drop(W.W64.lo(v), r)) : {W.W64.from_parts(U32{F.packing.bits_word(32n, _)}, U32{F.packing.bits_word(32n, l)}) == v : W.W64}
  %Equal.sym(U32, U32{F.packing.bits_word(32n, r)}, W.W64.hi(v), pw.u32_rt(W.W64.hi(v), Nil{})) : {W.W64.from_parts(_, U32{F.packing.bits_word(32n, l)}) == v : W.W64}
  %Equal.sym(U32, U32{F.packing.bits_word(32n, l)}, W.W64.lo(v), pw.u32_rt(W.W64.lo(v), r)) : {W.W64.from_parts(W.W64.hi(v), _) == v : W.W64}
  WL.parts_of(v)

# lists of bits equal but for trailing False bits

def pw.beq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _ _:
      False{}

def pw.eq0(xs: List<&2, Bool>, ys: List<&2, Bool>) -> Bool:
  match xs ys:
    case Nil{} r:
      F.packing.none_set(r)
    case Con{+a, +s} Nil{}:
      F.packing.none_set(Con{a, s})
    case Con{a, s} Con{b, t}:
      Bool.and(pw.beq(a, b), pw.eq0(s, t))

def pw.beq_eq(a: Bool, b: Bool, h: {pw.beq(a, b) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case False{} False{}:
      {==}
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, PL.pl.ft(h))
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, PL.pl.ft(h))

def pw.beq_refl(a: Bool) -> {pw.beq(a, a) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pw.not_t(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, PL.pl.ft(e))

def pw.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, PL.pl.ft(e))

def pw.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, PL.pl.ft(e))

def pw.eq0_nil(xs: List<&2, Bool>) -> {pw.eq0(xs, Nil{}) == F.packing.none_set(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, s}:
      {==}

def pw.ns_word(+n: Nat, xs: List<&2, Bool>, +h: {F.packing.none_set(xs) == True{} : Bool}) -> {F.packing.bits_word(n, xs) == F.packing.bits_word(n, Nil{}) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match xs:
        case Nil{}:
          {==}
        case Con{+b, +t}:
          %Equal.sym(Bool, b, False{}, pw.not_t(b, pw.and_l(Bool.not(b), F.packing.none_set(t), h))) : {WCon{_, F.packing.bits_word(p, t)} == WCon{False{}, F.packing.bits_word(p, Nil{})} : Word(1n+p)}
          %Equal.sym(Word(p), F.packing.bits_word(p, t), F.packing.bits_word(p, Nil{}), pw.ns_word(p, t, pw.and_r(Bool.not(b), F.packing.none_set(t), h))) : {WCon{False{}, _} == WCon{False{}, F.packing.bits_word(p, Nil{})} : Word(1n+p)}
          {==}

def pw.eq0_word(+n: Nat, xs: List<&2, Bool>, ys: List<&2, Bool>, +h: {pw.eq0(xs, ys) == True{} : Bool}) -> {F.packing.bits_word(n, xs) == F.packing.bits_word(n, ys) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match xs ys:
        case Nil{} Nil{}:
          {==}
        case Nil{} Con{+b, +t}:
          %Equal.sym(Bool, b, False{}, pw.not_t(b, pw.and_l(Bool.not(b), F.packing.none_set(t), h))) : {WCon{False{}, F.packing.bits_word(p, Nil{})} == WCon{_, F.packing.bits_word(p, t)} : Word(1n+p)}
          %Equal.sym(Word(p), F.packing.bits_word(p, t), F.packing.bits_word(p, Nil{}), pw.ns_word(p, t, pw.and_r(Bool.not(b), F.packing.none_set(t), h))) : {WCon{False{}, F.packing.bits_word(p, Nil{})} == WCon{False{}, _} : Word(1n+p)}
          {==}
        case Con{+a, +s} Nil{}:
          %Equal.sym(Bool, a, False{}, pw.not_t(a, pw.and_l(Bool.not(a), F.packing.none_set(s), h))) : {WCon{_, F.packing.bits_word(p, s)} == WCon{False{}, F.packing.bits_word(p, Nil{})} : Word(1n+p)}
          %Equal.sym(Word(p), F.packing.bits_word(p, s), F.packing.bits_word(p, Nil{}), pw.ns_word(p, s, pw.and_r(Bool.not(a), F.packing.none_set(s), h))) : {WCon{False{}, _} == WCon{False{}, F.packing.bits_word(p, Nil{})} : Word(1n+p)}
          {==}
        case Con{+a, +s} Con{+b, +t}:
          %pw.beq_eq(a, b, pw.and_l(pw.beq(a, b), pw.eq0(s, t), h)) : {WCon{a, F.packing.bits_word(p, s)} == WCon{_, F.packing.bits_word(p, t)} : Word(1n+p)}
          %pw.eq0_word(p, s, t, pw.and_r(pw.beq(a, b), pw.eq0(s, t), h)) : {WCon{a, F.packing.bits_word(p, s)} == WCon{a, _} : Word(1n+p)}
          {==}

def pw.ns_drop(t: List<&2, Bool>, +j: Nat, +h: {F.packing.none_set(t) == True{} : Bool}) -> {F.packing.none_set(List.drop(&2, Bool, t, j)) == True{} : Bool}:
  match t j:
    case Nil{} _:
      {==}
    case Con{b, s} 0n:
      h
    case Con{+b, +s} 1n+i:
      pw.ns_drop(s, i, pw.and_r(Bool.not(b), F.packing.none_set(s), h))

def pw.eq0_drop(+k: Nat, xs: List<&2, Bool>, ys: List<&2, Bool>, +h: {pw.eq0(xs, ys) == True{} : Bool}) -> {pw.eq0(List.drop(&2, Bool, xs, k), List.drop(&2, Bool, ys, k)) == True{} : Bool}:
  match k xs ys:
    case 0n Nil{} Nil{}:
      h
    case 0n Nil{} Con{b, t}:
      h
    case 0n Con{a, s} Nil{}:
      h
    case 0n Con{a, s} Con{b, t}:
      h
    case 1n+j Nil{} Nil{}:
      {==}
    case 1n+j Nil{} Con{+b, +t}:
      pw.ns_drop(t, j, pw.and_r(Bool.not(b), F.packing.none_set(t), h))
    case 1n+j Con{+a, +s} Nil{}:
      %Equal.sym(Bool, pw.eq0(List.drop(&2, Bool, s, j), Nil{}), F.packing.none_set(List.drop(&2, Bool, s, j)), pw.eq0_nil(List.drop(&2, Bool, s, j))) : {_ == True{} : Bool}
      pw.ns_drop(s, j, pw.and_r(Bool.not(a), F.packing.none_set(s), h))
    case 1n+j Con{+a, +s} Con{+b, +t}:
      pw.eq0_drop(j, s, t, pw.and_r(pw.beq(a, b), pw.eq0(s, t), h))

def pw.eq0_take(w: Nat, bs: List<&2, Bool>, +h: {F.packing.none_set(List.drop(&2, Bool, bs, w)) == True{} : Bool}) -> {pw.eq0(List.take(&2, Bool, bs, w), bs) == True{} : Bool}:
  match w bs:
    case 0n Nil{}:
      {==}
    case 0n Con{b, t}:
      h
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{+b, +t}:
      %Equal.sym(Bool, pw.beq(b, b), True{}, pw.beq_refl(b)) : {Bool.and(_, pw.eq0(List.take(&2, Bool, t, j), t)) == True{} : Bool}
      pw.eq0_take(j, t, h)

# a value that fits in w bits is its low w bits
def pw.fits_low(+v: W.W64, +w: Nat, +h: {F.packing.fits(v, w) == True{} : Bool}) -> {F.packing.bits_w64(List.take(&2, Bool, F.packing.w64_bits(v), w)) == v : W.W64}:
  +l = F.packing.w64_bits(v)
  +t = List.take(&2, Bool, l, w)
  +e = pw.eq0_take(w, l, h)
  %Equal.sym(Word(32n), F.packing.bits_word(32n, t), F.packing.bits_word(32n, l), pw.eq0_word(32n, t, l, e)) : {W.W64.from_parts(U32{F.packing.bits_word(32n, List.drop(&2, Bool, t, 32n))}, U32{_}) == v : W.W64}
  %Equal.sym(Word(32n), F.packing.bits_word(32n, List.drop(&2, Bool, t, 32n)), F.packing.bits_word(32n, List.drop(&2, Bool, l, 32n)), pw.eq0_word(32n, List.drop(&2, Bool, t, 32n), List.drop(&2, Bool, l, 32n), pw.eq0_drop(32n, t, l, e))) : {W.W64.from_parts(U32{_}, U32{F.packing.bits_word(32n, l)}) == v : W.W64}
  pw.val(v)

# Lengths

def pw.wb_len(+n: Nat, w: Word(n), +rest: List<&2, Bool>) -> {List.length(&2, Bool, F.packing.word_bits(n, w, rest)) == Nat.add(n, List.length(&2, Bool, rest)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          %pw.wb_len(p, t, rest) : {1n+List.length(&2, Bool, F.packing.word_bits(p, t, rest)) == 1n+_ : Nat}
          {==}

def pw.u32_len(x: U32, +rest: List<&2, Bool>) -> {List.length(&2, Bool, F.packing.u32_bits(x, rest)) == Nat.add(32n, List.length(&2, Bool, rest)) : Nat}:
  match x:
    case U32{w}:
      pw.wb_len(32n, w, rest)

def pw.bits_len(+v: W.W64) -> {List.length(&2, Bool, F.packing.w64_bits(v)) == 64n : Nat}:
  %Equal.sym(Nat, List.length(&2, Bool, F.packing.w64_bits(v)), Nat.add(32n, List.length(&2, Bool, F.packing.u32_bits(W.W64.hi(v), Nil{}))), pw.u32_len(W.W64.lo(v), F.packing.u32_bits(W.W64.hi(v), Nil{}))) : {_ == 64n : Nat}
  %Equal.sym(Nat, List.length(&2, Bool, F.packing.u32_bits(W.W64.hi(v), Nil{})), Nat.add(32n, 0n), pw.u32_len(W.W64.hi(v), Nil{})) : {Nat.add(32n, _) == 64n : Nat}
  {==}

def pw.take_len(xs: List<&2, Bool>, w: Nat, +h: {Nat.is_le(w, List.length(&2, Bool, xs)) == True{} : Bool}) -> {List.length(&2, Bool, List.take(&2, Bool, xs, w)) == w : Nat}:
  match xs w:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      Empty.absurd({0n == 1n+j : Nat}, PL.pl.ft(h))
    case Con{b, t} 0n:
      {==}
    case Con{b, +t} 1n+ +j:
      %pw.take_len(t, j, h) : {1n+List.length(&2, Bool, List.take(&2, Bool, t, j)) == 1n+_ : Nat}
      {==}
