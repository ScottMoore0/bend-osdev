import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./error.bend as E
import ./bits.bend as Bi
import ./fse.bend as F
import ./huffman.bend as H
import ./xxh64.bend as X
import ./block.bend as K
import ./sequences.bend as S
import ./dict.bend as D
import ./frame.bend as Fr
import ./zstd.bend as Z
import ./compress.bend as C
import ./LAWS.bend as Laws

# The lemmas below are about the package's internals; Octets enter them only
# through bytes' interface laws (octets_append_list, octets_to_of,
# octets_of_to), never through how Octets stores its bytes.



# Nat arithmetic

def bool_disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def false_not_true(h: {False{} == True{} : Bool}) -> Empty:
  %h : bool_disc(_)
  Unit{}

def true_not_false(h: {True{} == False{} : Bool}) -> Empty:
  false_not_true(Equal.sym(Bool, True{}, False{}, h))

def absurd(-P: Type, e: Empty) -> P:
  match e:

def add_zero(p: Nat) -> {Nat.add(p, 0n) == p : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      %add_zero(q) : {1n+Nat.add(q, 0n) == 1n+_ : Nat}
      {==}

def add_succ(p: Nat, x: Nat) -> {Nat.add(p, 1n+x) == 1n+Nat.add(p, x) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      %add_succ(q, x) : {1n+Nat.add(q, 1n+x) == 1n+_ : Nat}
      {==}

def add_comm(+p: Nat, +q: Nat) -> {Nat.add(p, q) == Nat.add(q, p) : Nat}:
  match p:
    case 0n:
      Equal.sym(Nat, Nat.add(q, 0n), q, add_zero(q))
    case 1n+r:
      %Equal.sym(Nat, Nat.add(q, 1n+r), 1n+Nat.add(q, r), add_succ(q, r)) : {1n+Nat.add(r, q) == _ : Nat}
      %add_comm(r, q) : {1n+Nat.add(r, q) == 1n+_ : Nat}
      {==}

def add_assoc(p: Nat, +q: Nat, +r: Nat) -> {Nat.add(Nat.add(p, q), r) == Nat.add(p, Nat.add(q, r)) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+s:
      %add_assoc(s, q, r) : {1n+Nat.add(Nat.add(s, q), r) == 1n+_ : Nat}
      {==}

# (a + b) + (c + d) == (a + c) + (b + d)
def add_swap(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), add_assoc(a, b, Nat.add(c, d))) : {_ == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), add_assoc(a, c, Nat.add(b, d))) : {Nat.add(a, Nat.add(b, Nat.add(c, d))) == _ : Nat}
  %add_assoc(b, c, d) : {Nat.add(a, _) == Nat.add(a, Nat.add(c, Nat.add(b, d))) : Nat}
  %add_assoc(c, b, d) : {Nat.add(a, Nat.add(Nat.add(b, c), d)) == Nat.add(a, _) : Nat}
  %Equal.sym(Nat, Nat.add(b, c), Nat.add(c, b), add_comm(b, c)) : {Nat.add(a, Nat.add(_, d)) == Nat.add(a, Nat.add(Nat.add(c, b), d)) : Nat}
  {==}

def sub_zero(m: Nat) -> {Nat.sub(m, 0n) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_zero_true(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a + (v - a) == v when a <= v
def le_add_sub(a: Nat, v: Nat, h: {Nat.is_le(a, v) == True{} : Bool}) -> {Nat.add(a, Nat.sub(v, a)) == v : Nat}:
  match a v:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      absurd({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, false_not_true(h))
    case 1n+p 1n+q:
      %le_add_sub(p, q, h) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
      {==}

# not (a <= v) means v < a
def not_le_lt(a: Nat, v: Nat, h: {Nat.is_le(a, v) == False{} : Bool}) -> {Nat.is_lt(v, a) == True{} : Bool}:
  match a v:
    case 0n 0n:
      absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, true_not_false(h))
    case 0n 1n+q:
      absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, true_not_false(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      not_le_lt(p, q, h)

# v - a < b when a <= v < a + b
def sub_lt(a: Nat, v: Nat, +b: Nat, h1: {Nat.is_le(a, v) == True{} : Bool}, h2: {Nat.is_lt(v, Nat.add(a, b)) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(v, a), b) == True{} : Bool}:
  match a v:
    case 0n 0n:
      h2
    case 0n 1n+q:
      h2
    case 1n+p 0n:
      absurd({Nat.is_lt(Nat.sub(0n, 1n+p), b) == True{} : Bool}, false_not_true(h1))
    case 1n+p 1n+q:
      sub_lt(p, q, b, h1, h2)

# v < 1 means v is 0
def lt1_zero(v: Nat, h: {Nat.is_lt(v, 1n) == True{} : Bool}) -> {v == 0n : Nat}:
  match v:
    case 0n:
      {==}
    case 1n+q:
      match q:
        case 0n:
          absurd({1n == 0n : Nat}, false_not_true(h))
        case 1n+r:
          absurd({2n+r == 0n : Nat}, false_not_true(h))

# Bit fields: a field of n bits holding v reads back as v

# a * 2^n, as the reader builds it: doubled n times
def sh(n: Nat, a: Nat) -> Nat:
  match n:
    case 0n:
      a
    case 1n+p:
      +x = a
      sh(p, Nat.add(x, x))

def sh_add(n: Nat, +x: Nat, +y: Nat) -> {sh(n, Nat.add(x, y)) == Nat.add(sh(n, x), sh(n, y)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      %Equal.sym(Nat, Nat.add(Nat.add(x, y), Nat.add(x, y)), Nat.add(Nat.add(x, x), Nat.add(y, y)), add_swap(x, y, x, y)) : {sh(p, _) == Nat.add(sh(p, Nat.add(x, x)), sh(p, Nat.add(y, y))) : Nat}
      sh_add(p, Nat.add(x, x), Nat.add(y, y))

def sh_one(n: Nat) -> {sh(n, 1n) == Bi.ZstdBits.pow2(n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      %Equal.sym(Nat, sh(p, Nat.add(1n, 1n)), Nat.add(sh(p, 1n), sh(p, 1n)), sh_add(p, 1n, 1n)) : {_ == Nat.add(Bi.ZstdBits.pow2(p), Bi.ZstdBits.pow2(p)) : Nat}
      %Equal.sym(Nat, sh(p, 1n), Bi.ZstdBits.pow2(p), sh_one(p)) : {Nat.add(_, _) == Nat.add(Bi.ZstdBits.pow2(p), Bi.ZstdBits.pow2(p)) : Nat}
      {==}

def sh_zero(n: Nat) -> {sh(n, 0n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      sh_zero(p)

def pow_pred(p: Nat) -> {Bi.ZstdBits.pow2(Nat.sub(p, 0n)) == Bi.ZstdBits.pow2(p) : Nat}:
  %Equal.sym(Nat, Nat.sub(p, 0n), p, sub_zero(p)) : {Bi.ZstdBits.pow2(_) == Bi.ZstdBits.pow2(p) : Nat}
  {==}

# the digit step: sh(p, 2a + 1) + (v - 2^p) == sh(p, 2a) + v when 2^p <= v
def rd_one(+p: Nat, +a: Nat, +v: Nat, h: {Nat.is_le(Bi.ZstdBits.pow2(p), v) == True{} : Bool}) -> {Nat.add(sh(p, Nat.add(a, 1n)), Nat.sub(v, Bi.ZstdBits.pow2(p))) == Nat.add(sh(p, a), v) : Nat}:
  %Equal.sym(Nat, sh(p, Nat.add(a, 1n)), Nat.add(sh(p, a), sh(p, 1n)), sh_add(p, a, 1n)) : {Nat.add(_, Nat.sub(v, Bi.ZstdBits.pow2(p))) == Nat.add(sh(p, a), v) : Nat}
  %Equal.sym(Nat, sh(p, 1n), Bi.ZstdBits.pow2(p), sh_one(p)) : {Nat.add(Nat.add(sh(p, a), _), Nat.sub(v, Bi.ZstdBits.pow2(p))) == Nat.add(sh(p, a), v) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(sh(p, a), Bi.ZstdBits.pow2(p)), Nat.sub(v, Bi.ZstdBits.pow2(p))), Nat.add(sh(p, a), Nat.add(Bi.ZstdBits.pow2(p), Nat.sub(v, Bi.ZstdBits.pow2(p)))), add_assoc(sh(p, a), Bi.ZstdBits.pow2(p), Nat.sub(v, Bi.ZstdBits.pow2(p)))) : {_ == Nat.add(sh(p, a), v) : Nat}
  %le_add_sub(Bi.ZstdBits.pow2(p), v, h) : {Nat.add(sh(p, a), Nat.add(Bi.ZstdBits.pow2(p), Nat.sub(v, Bi.ZstdBits.pow2(p)))) == Nat.add(sh(p, a), _) : Nat}
  {==}

# the test of the first bit: 2^(n-1) <= v, written as the encoder writes it
def hi_of(+p: Nat, +v: Nat, hi: Bool, h1: {hi == Nat.is_le(Bi.ZstdBits.pow2(Nat.sub(p, 0n)), v) : Bool}) -> {Nat.is_le(Bi.ZstdBits.pow2(p), v) == hi : Bool}:
  Equal.trans(Bool, Nat.is_le(Bi.ZstdBits.pow2(p), v), Nat.is_le(Bi.ZstdBits.pow2(Nat.sub(p, 0n)), v), hi, Equal.sym(Bool, Nat.is_le(Bi.ZstdBits.pow2(Nat.sub(p, 0n)), v), Nat.is_le(Bi.ZstdBits.pow2(p), v), Equal.cong(Nat, Bool, x => Nat.is_le(x, v), Bi.ZstdBits.pow2(Nat.sub(p, 0n)), Bi.ZstdBits.pow2(p), pow_pred(p))), Equal.sym(Bool, hi, Nat.is_le(Bi.ZstdBits.pow2(Nat.sub(p, 0n)), v), h1))

def rd_go(n: Nat, hi: Bool, +v: Nat, +acc: Nat, +rest: List<&2, Bool>, h1: {hi == Nat.is_le(Bi.ZstdBits.pow2(Nat.sub(n, 1n)), v) : Bool}, h2: {Nat.is_lt(v, Bi.ZstdBits.pow2(n)) == True{} : Bool}) -> {Bi.bits.read.go(n, List.append(&2, Bool, Bi.bits.of_nat.go(n, hi, v), rest), acc) == Some{Bi.ZstdBits{Nat.add(sh(n, acc), v), rest}} : Maybe<&2, Bi.ZstdBits>}:
  match n:
    case 0n:
      %Equal.sym(Nat, v, 0n, lt1_zero(v, h2)) : {Some{Bi.ZstdBits{acc, rest}} == Some{Bi.ZstdBits{Nat.add(acc, _), rest}} : Maybe<&2, Bi.ZstdBits>}
      %Equal.sym(Nat, Nat.add(acc, 0n), acc, add_zero(acc)) : {Some{Bi.ZstdBits{acc, rest}} == Some{Bi.ZstdBits{_, rest}} : Maybe<&2, Bi.ZstdBits>}
      {==}
    case 1n+(+p):
      match hi:
        case True{}:
          +le = hi_of(p, v, True{}, h1)
          +v2 = Nat.sub(v, Bi.ZstdBits.pow2(p))
          +a2 = Nat.add(Nat.add(acc, acc), 1n)
          Equal.trans(Maybe<&2, Bi.ZstdBits>, Bi.bits.read.go(p, List.append(&2, Bool, Bi.bits.of_nat.go(p, Nat.is_le(Bi.ZstdBits.pow2(Nat.sub(p, 1n)), v2), v2), rest), a2), Some{Bi.ZstdBits{Nat.add(sh(p, a2), v2), rest}}, Some{Bi.ZstdBits{Nat.add(sh(p, Nat.add(acc, acc)), v), rest}}, rd_go(p, Nat.is_le(Bi.ZstdBits.pow2(Nat.sub(p, 1n)), v2), v2, a2, rest, {==}, sub_lt(Bi.ZstdBits.pow2(p), v, Bi.ZstdBits.pow2(p), le, h2)), Equal.cong(Nat, Maybe<&2, Bi.ZstdBits>, x => Some{Bi.ZstdBits{x, rest}}, Nat.add(sh(p, a2), v2), Nat.add(sh(p, Nat.add(acc, acc)), v), rd_one(p, Nat.add(acc, acc), v, le)))
        case False{}:
          +nle = hi_of(p, v, False{}, h1)
          +a2 = Nat.add(Nat.add(acc, acc), 0n)
          Equal.trans(Maybe<&2, Bi.ZstdBits>, Bi.bits.read.go(p, List.append(&2, Bool, Bi.bits.of_nat.go(p, Nat.is_le(Bi.ZstdBits.pow2(Nat.sub(p, 1n)), v), v), rest), a2), Some{Bi.ZstdBits{Nat.add(sh(p, a2), v), rest}}, Some{Bi.ZstdBits{Nat.add(sh(p, Nat.add(acc, acc)), v), rest}}, rd_go(p, Nat.is_le(Bi.ZstdBits.pow2(Nat.sub(p, 1n)), v), v, a2, rest, {==}, not_le_lt(Bi.ZstdBits.pow2(p), v, nle)), Equal.cong(Nat, Maybe<&2, Bi.ZstdBits>, x => Some{Bi.ZstdBits{Nat.add(sh(p, x), v), rest}}, a2, Nat.add(acc, acc), add_zero(Nat.add(acc, acc))))

def Laws.bits_round_trip(n, v, rest, h):
  match n:
    case 0n:
      %Equal.sym(Nat, v, 0n, lt1_zero(v, h)) : {Some{Bi.ZstdBits{0n, rest}} == Some{Bi.ZstdBits{_, rest}} : Maybe<&2, Bi.ZstdBits>}
      {==}
    case 1n+(+p):
      Equal.trans(Maybe<&2, Bi.ZstdBits>, Bi.ZstdBits.read(1n+p, List.append(&2, Bool, Bi.ZstdBits.of_nat(1n+p, v), rest)), Some{Bi.ZstdBits{Nat.add(sh(p, 0n), v), rest}}, Some{Bi.ZstdBits{v, rest}}, rd_go(1n+p, Nat.is_le(Bi.ZstdBits.pow2(p), v), v, 0n, rest, hi_of(p, v, Nat.is_le(Bi.ZstdBits.pow2(Nat.sub(p, 0n)), v), {==}), h), Equal.cong(Nat, Maybe<&2, Bi.ZstdBits>, x => Some{Bi.ZstdBits{Nat.add(x, v), rest}}, sh(p, 0n), 0n, sh_zero(p)))

# The output limit: the guard in decompress_with

def fits_le(b: Bool, +o: B.Octets, +m: Nat, e: {Nat.is_le(B.Octets.len(o), m) == b : Bool}) -> {Nat.is_le(B.Octets.len(Result.default(&2, &2, E.ZstdError, B.Octets, Z.zstd.fits(b, o), B.Octets.empty())), m) == True{} : Bool}:
  match b:
    case True{}:
      e
    case False{}:
      le_zero_true(m)

def guard_le(+max: U32, r: Result<&2, &2, E.ZstdError, B.Octets>) -> {Nat.is_le(B.Octets.len(Result.default(&2, &2, E.ZstdError, B.Octets, Z.zstd.guard(Fr.ZstdLimit{max}, r), B.Octets.empty())), U32.to_nat(max)) == True{} : Bool}:
  match r:
    case Fail{e}:
      le_zero_true(U32.to_nat(max))
    case Done{+o}:
      fits_le(Nat.is_le(B.Octets.len(o), U32.to_nat(max)), o, U32.to_nat(max), {==})

def Laws.output_within_max(max, verify, dict, mw, src):
  guard_le(max, Z.Zstd.finish(Z.Zstd.feed(Z.Zstd.start(Z.ZstdOptions{Fr.ZstdLimit{max}, verify, dict, mw}), src)))

# Streaming: the machine folds its step over the bytes

def run_append(xs: List<&2, U32>, ys: List<&2, U32>, d: Fr.ZstdDecoder) -> {Fr.ZstdFrame.run(B.append(xs, ys), d) == Fr.ZstdFrame.run(ys, Fr.ZstdFrame.run(xs, d)) : Fr.ZstdDecoder}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      run_append(t, ys, Fr.ZstdFrame.step(d, h))

def Laws.stream_pieces(opts, a, b):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {Z.Zstd.finish(Fr.ZstdFrame.run(B.Octets.to_list(b), Fr.ZstdFrame.run(B.Octets.to_list(a), Z.Zstd.start(opts)))) == Z.Zstd.finish(Fr.ZstdFrame.run(_, Z.Zstd.start(opts))) : Result<&2, &2, E.ZstdError, B.Octets>}
  %Equal.sym(Fr.ZstdDecoder, Fr.ZstdFrame.run(B.append(B.Octets.to_list(a), B.Octets.to_list(b)), Z.Zstd.start(opts)), Fr.ZstdFrame.run(B.Octets.to_list(b), Fr.ZstdFrame.run(B.Octets.to_list(a), Z.Zstd.start(opts))), run_append(B.Octets.to_list(a), B.Octets.to_list(b), Z.Zstd.start(opts))) : {Z.Zstd.finish(Fr.ZstdFrame.run(B.Octets.to_list(b), Fr.ZstdFrame.run(B.Octets.to_list(a), Z.Zstd.start(opts)))) == Z.Zstd.finish(_) : Result<&2, &2, E.ZstdError, B.Octets>}
  {==}

def Laws.one_shot_is_streaming(verify, dict, mw, a, b):
  Equal.sym(Result<&2, &2, E.ZstdError, B.Octets>, Z.Zstd.finish(Z.Zstd.feed(Z.Zstd.feed(Z.Zstd.start(Z.ZstdOptions{Fr.ZstdNoLimit{}, verify, dict, mw}), a), b)), Z.Zstd.finish(Z.Zstd.feed(Z.Zstd.start(Z.ZstdOptions{Fr.ZstdNoLimit{}, verify, dict, mw}), B.Octets.append(a, b))), Laws.stream_pieces(Z.ZstdOptions{Fr.ZstdNoLimit{}, verify, dict, mw}, a, b))

# Lists and small facts

def append_assoc_bool(+xs: List<&2, Bool>, +ys: List<&2, Bool>, +zs: List<&2, Bool>) -> {List.append(&2, Bool, List.append(&2, Bool, xs, ys), zs) == List.append(&2, Bool, xs, List.append(&2, Bool, ys, zs)) : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %append_assoc_bool(t, ys, zs) : {Con{h, List.append(&2, Bool, List.append(&2, Bool, t, ys), zs)} == Con{h, _} : List<&2, Bool>}
      {==}

# reversing onto acc, then onto ys: acc onto xs ++ ys
def rev_rev_go(+xs: List<&2, Nat>, +acc: List<&2, Nat>, +ys: List<&2, Nat>) -> {List.reverse.go(&2, Nat, List.reverse.go(&2, Nat, xs, acc), ys) == List.reverse.go(&2, Nat, acc, List.append(&2, Nat, xs, ys)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      rev_rev_go(t, Con{h, acc}, ys)

def append_nil_nat(+xs: List<&2, Nat>) -> {List.append(&2, Nat, xs, Nil{}) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %append_nil_nat(t) : {Con{h, List.append(&2, Nat, t, Nil{})} == Con{h, _} : List<&2, Nat>}
      {==}

def rev_rev_nat(+xs: List<&2, Nat>) -> {List.reverse(&2, Nat, List.reverse(&2, Nat, xs)) == xs : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, List.reverse(&2, Nat, List.reverse(&2, Nat, xs)), List.append(&2, Nat, xs, Nil{}), xs, rev_rev_go(xs, Nil{}, Nil{}), append_nil_nat(xs))

def len_rev_go(+xs: List<&2, Nat>, +acc: List<&2, Nat>) -> {List.length(&2, Nat, List.reverse.go(&2, Nat, xs, acc)) == Nat.add(List.length(&2, Nat, xs), List.length(&2, Nat, acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.trans(Nat, List.length(&2, Nat, List.reverse.go(&2, Nat, t, Con{h, acc})), Nat.add(List.length(&2, Nat, t), 1n+List.length(&2, Nat, acc)), 1n+Nat.add(List.length(&2, Nat, t), List.length(&2, Nat, acc)), len_rev_go(t, Con{h, acc}), add_succ(List.length(&2, Nat, t), List.length(&2, Nat, acc)))

def and_true_l(+a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      absurd({False{} == True{} : Bool}, false_not_true(h))

def and_true_r(+a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      absurd({b == True{} : Bool}, false_not_true(h))

def nat_eq_true(+a: Nat, +b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      absurd({0n == 1n+q : Nat}, false_not_true(h))
    case 1n+p 0n:
      absurd({1n+p == 0n : Nat}, false_not_true(h))
    case 1n+p 1n+q:
      %nat_eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

def maybe_disc(-A: Data, +m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      Empty

# None is not Some
def none_some(-A: Data, +x: A, h: {None{} == Some{x} : Maybe<&2, A>}) -> Empty:
  %h : maybe_disc(A, _)
  Unit{}

def some_inj(-A: Data, +x: A, +y: A, +d: A, h: {Some{x} == Some{y} : Maybe<&2, A>}) -> {x == y : A}:
  Equal.cong(Maybe<&2, A>, A, m => Maybe.default(&2, A, m, d), Some{x}, Some{y}, h)

# FSE: the encoder's choices decode back
#
# FseInv(t, tn, acc, done): from state tn, on the bits acc and then any
# rest, the decoder gives the symbols done and leaves the rest (whatever it
# had decoded before, a, reversed)

def FseInv(+t: F.ZstdFseTable, +tn: Nat, +acc: List<&2, Bool>, +done: List<&2, Nat>) -> Type:
  @rest: List<&2, Bool> -> @a: List<&2, Nat> -> {F.fse.dec(List.length(&2, Nat, done), t, Some{Bi.ZstdBits{tn, List.append(&2, Bool, acc, rest)}}, a) == Some{F.ZstdFseSyms{List.reverse(&2, Nat, List.reverse.go(&2, Nat, done, a)), rest}} : Maybe<&2, F.ZstdFseSyms>}

def fse_base(+t: F.ZstdFseTable, +s: Nat, +last: Nat, h: {F.ZstdFse.sym(F.ZstdFse.entry(t, s)) == last : Nat}) -> FseInv(t, s, Nil{}, [last]):
  +rest => +a => Equal.cong(Nat, Maybe<&2, F.ZstdFseSyms>, x => Some{F.ZstdFseSyms{List.reverse(&2, Nat, Con{x, a}), rest}}, F.ZstdFse.sym(F.ZstdFse.entry(t, s)), last, h)

def ZsEnt.sym(+e: F.ZstdFseEntry) -> Nat:
  match e:
    case F.ZstdFseEntry{sym, nb, base}:
      sym

# the decoder's step from state s1, whose entry is (sym, nb, base): the
# encoder chose s1 for x because sym is x and tn lies in its range, and
# wrote tn - base in nb bits before acc
def fse_next(+t: F.ZstdFseTable, +s1: Nat, +sym: Nat, +nb: Nat, +base: Nat, +tn: Nat, +acc: List<&2, Bool>, +rest: List<&2, Bool>, he: {F.ZstdFse.entry(t, s1) == F.ZstdFseEntry{sym, nb, base} : F.ZstdFseEntry}, hle: {Nat.is_le(base, tn) == True{} : Bool}, hlt: {Nat.is_lt(Nat.sub(tn, base), Bi.ZstdBits.pow2(nb)) == True{} : Bool}) -> {F.ZstdFse.next(F.ZstdFse.entry(t, s1), List.append(&2, Bool, List.append(&2, Bool, Bi.ZstdBits.of_nat(nb, Nat.sub(tn, base)), acc), rest)) == Some{Bi.ZstdBits{tn, List.append(&2, Bool, acc, rest)}} : Maybe<&2, Bi.ZstdBits>}:
  +v = Nat.sub(tn, base)
  +r = List.append(&2, Bool, acc, rest)
  +bb = List.append(&2, Bool, List.append(&2, Bool, Bi.ZstdBits.of_nat(nb, v), acc), rest)
  Equal.trans(Maybe<&2, Bi.ZstdBits>, F.ZstdFse.next(F.ZstdFse.entry(t, s1), bb), F.fse.next.add(Bi.ZstdBits.read(nb, bb), base), Some{Bi.ZstdBits{tn, r}}, Equal.cong(F.ZstdFseEntry, Maybe<&2, Bi.ZstdBits>, e => F.ZstdFse.next(e, bb), F.ZstdFse.entry(t, s1), F.ZstdFseEntry{sym, nb, base}, he), Equal.trans(Maybe<&2, Bi.ZstdBits>, F.fse.next.add(Bi.ZstdBits.read(nb, bb), base), F.fse.next.add(Bi.ZstdBits.read(nb, List.append(&2, Bool, Bi.ZstdBits.of_nat(nb, v), r)), base), Some{Bi.ZstdBits{tn, r}}, Equal.cong(List<&2, Bool>, Maybe<&2, Bi.ZstdBits>, b => F.fse.next.add(Bi.ZstdBits.read(nb, b), base), bb, List.append(&2, Bool, Bi.ZstdBits.of_nat(nb, v), r), append_assoc_bool(Bi.ZstdBits.of_nat(nb, v), acc, rest)), Equal.trans(Maybe<&2, Bi.ZstdBits>, F.fse.next.add(Bi.ZstdBits.read(nb, List.append(&2, Bool, Bi.ZstdBits.of_nat(nb, v), r)), base), Some{Bi.ZstdBits{Nat.add(base, v), r}}, Some{Bi.ZstdBits{tn, r}}, Equal.cong(Maybe<&2, Bi.ZstdBits>, Maybe<&2, Bi.ZstdBits>, m => F.fse.next.add(m, base), Bi.ZstdBits.read(nb, List.append(&2, Bool, Bi.ZstdBits.of_nat(nb, v), r)), Some{Bi.ZstdBits{v, r}}, Laws.bits_round_trip(nb, v, r, hlt)), Equal.cong(Nat, Maybe<&2, Bi.ZstdBits>, n => Some{Bi.ZstdBits{n, r}}, Nat.add(base, v), tn, le_add_sub(base, tn, hle)))))

def fse_step.at(+t: F.ZstdFseTable, +s1: Nat, +sym: Nat, +nb: Nat, +base: Nat, +x: Nat, +tn: Nat, +acc: List<&2, Bool>, +d: Nat, +ds: List<&2, Nat>, +rest: List<&2, Bool>, +a: List<&2, Nat>, +he: {F.ZstdFse.entry(t, s1) == F.ZstdFseEntry{sym, nb, base} : F.ZstdFseEntry}, hx: {sym == x : Nat}, hle: {Nat.is_le(base, tn) == True{} : Bool}, hlt: {Nat.is_lt(Nat.sub(tn, base), Bi.ZstdBits.pow2(nb)) == True{} : Bool}, iv: {F.fse.dec(List.length(&2, Nat, Con{d, ds}), t, Some{Bi.ZstdBits{tn, List.append(&2, Bool, acc, rest)}}, Con{x, a}) == Some{F.ZstdFseSyms{List.reverse(&2, Nat, List.reverse.go(&2, Nat, Con{d, ds}, Con{x, a})), rest}} : Maybe<&2, F.ZstdFseSyms>}) -> {F.fse.dec(List.length(&2, Nat, Con{x, Con{d, ds}}), t, Some{Bi.ZstdBits{s1, List.append(&2, Bool, List.append(&2, Bool, Bi.ZstdBits.of_nat(nb, Nat.sub(tn, base)), acc), rest)}}, a) == Some{F.ZstdFseSyms{List.reverse(&2, Nat, List.reverse.go(&2, Nat, Con{x, Con{d, ds}}, a)), rest}} : Maybe<&2, F.ZstdFseSyms>}:
  +n = {1n+List.length(&2, Nat, ds) : Nat}
  +bb = List.append(&2, Bool, List.append(&2, Bool, Bi.ZstdBits.of_nat(nb, Nat.sub(tn, base)), acc), rest)
  +nx = F.ZstdFse.next(F.ZstdFse.entry(t, s1), bb)
  +sm = {Some{Bi.ZstdBits{tn, List.append(&2, Bool, acc, rest)}} : Maybe<&2, Bi.ZstdBits>}
  +sy = F.ZstdFse.sym(F.ZstdFse.entry(t, s1))
  +hs = Equal.trans(Nat, sy, sym, x, Equal.cong(F.ZstdFseEntry, Nat, e => F.ZstdFse.sym(e), F.ZstdFse.entry(t, s1), F.ZstdFseEntry{sym, nb, base}, he), hx)
  Equal.trans(Maybe<&2, F.ZstdFseSyms>, F.fse.dec(n, t, nx, Con{sy, a}), F.fse.dec(n, t, sm, Con{x, a}), Some{F.ZstdFseSyms{List.reverse(&2, Nat, List.reverse.go(&2, Nat, Con{d, ds}, Con{x, a})), rest}}, Equal.trans(Maybe<&2, F.ZstdFseSyms>, F.fse.dec(n, t, nx, Con{sy, a}), F.fse.dec(n, t, sm, Con{sy, a}), F.fse.dec(n, t, sm, Con{x, a}), Equal.cong(Maybe<&2, Bi.ZstdBits>, Maybe<&2, F.ZstdFseSyms>, c => F.fse.dec(n, t, c, Con{sy, a}), nx, sm, fse_next(t, s1, sym, nb, base, tn, acc, rest, he, hle, hlt)), Equal.cong(Nat, Maybe<&2, F.ZstdFseSyms>, y => F.fse.dec(n, t, sm, Con{y, a}), sy, x, hs)), iv)

def fse_step(+t: F.ZstdFseTable, +s1: Nat, +sym: Nat, +nb: Nat, +base: Nat, +x: Nat, +tn: Nat, +acc: List<&2, Bool>, +d: Nat, +ds: List<&2, Nat>, he: {F.ZstdFse.entry(t, s1) == F.ZstdFseEntry{sym, nb, base} : F.ZstdFseEntry}, hx: {sym == x : Nat}, hle: {Nat.is_le(base, tn) == True{} : Bool}, hlt: {Nat.is_lt(Nat.sub(tn, base), Bi.ZstdBits.pow2(nb)) == True{} : Bool}, inv: FseInv(t, tn, acc, Con{d, ds})) -> FseInv(t, s1, List.append(&2, Bool, Bi.ZstdBits.of_nat(nb, Nat.sub(tn, base)), acc), Con{x, Con{d, ds}}):
  +rest => +a => fse_step.at(t, s1, sym, nb, base, x, tn, acc, d, ds, rest, a, he, hx, hle, hlt, inv(rest, Con{x, a}))

# the invariant of an encoder state (none: nothing to show)
def FseInvM(t: F.ZstdFseTable, cur: Maybe<&2, F.ZsFseEnc>, done: List<&2, Nat>) -> Type:
  match cur:
    case None{}:
      Unit
    case Some{F.ZsFseEnc{tn, acc}}:
      FseInv(t, tn, acc, done)

def fse_fits_inv(+t: F.ZstdFseTable, +x: Nat, +tn: Nat, +acc: List<&2, Bool>, +d: Nat, +ds: List<&2, Nat>, inv: FseInv(t, tn, acc, Con{d, ds}), +s1: Nat, +sym: Nat, +nb: Nat, +base: Nat, he: {F.ZstdFse.entry(t, s1) == F.ZstdFseEntry{sym, nb, base} : F.ZstdFseEntry}, b: Bool, +hb: {Bool.and(Nat.is_eq(sym, x), Bool.and(Nat.is_le(base, tn), Nat.is_lt(Nat.sub(tn, base), Bi.ZstdBits.pow2(nb)))) == b : Bool}) -> FseInvM(t, F.fse.enc.ok(b, F.ZstdFseEntry{sym, nb, base}, s1, tn, acc), Con{x, Con{d, ds}}):
  match b:
    case False{}:
      Unit{}
    case True{}:
      +inner = and_true_r(Nat.is_eq(sym, x), Bool.and(Nat.is_le(base, tn), Nat.is_lt(Nat.sub(tn, base), Bi.ZstdBits.pow2(nb))), hb)
      fse_step(t, s1, sym, nb, base, x, tn, acc, d, ds, he, nat_eq_true(sym, x, and_true_l(Nat.is_eq(sym, x), Bool.and(Nat.is_le(base, tn), Nat.is_lt(Nat.sub(tn, base), Bi.ZstdBits.pow2(nb))), hb)), and_true_l(Nat.is_le(base, tn), Nat.is_lt(Nat.sub(tn, base), Bi.ZstdBits.pow2(nb)), inner), and_true_r(Nat.is_le(base, tn), Nat.is_lt(Nat.sub(tn, base), Bi.ZstdBits.pow2(nb)), inner), inv)

def fse_ok_inv(+t: F.ZstdFseTable, +x: Nat, +tn: Nat, +acc: List<&2, Bool>, +d: Nat, +ds: List<&2, Nat>, inv: FseInv(t, tn, acc, Con{d, ds}), +s1: Nat, e: F.ZstdFseEntry, he: {F.ZstdFse.entry(t, s1) == e : F.ZstdFseEntry}) -> FseInvM(t, F.fse.enc.ok(F.ZstdFse.fits(e, x, tn), e, s1, tn, acc), Con{x, Con{d, ds}}):
  match e:
    case F.ZstdFseEntry{+sym, +nb, +base}:
      fse_fits_inv(t, x, tn, acc, d, ds, inv, s1, sym, nb, base, he, Bool.and(Nat.is_eq(sym, x), Bool.and(Nat.is_le(base, tn), Nat.is_lt(Nat.sub(tn, base), Bi.ZstdBits.pow2(nb)))), {==})

def fse_found_inv(+t: F.ZstdFseTable, +x: Nat, +tn: Nat, +acc: List<&2, Bool>, +d: Nat, +ds: List<&2, Nat>, inv: FseInv(t, tn, acc, Con{d, ds}), m: Maybe<&2, Nat>) -> FseInvM(t, F.fse.enc.found(m, t, x, tn, acc), Con{x, Con{d, ds}}):
  match m:
    case None{}:
      Unit{}
    case Some{+s1}:
      fse_ok_inv(t, x, tn, acc, d, ds, inv, s1, F.ZstdFse.entry(t, s1), {==})

# the encoder's loop keeps the invariant: done grows by each symbol it adds
def fse_enc_inv(+xs: List<&2, Nat>, +t: F.ZstdFseTable, +d: Nat, +ds: List<&2, Nat>, cur: Maybe<&2, F.ZsFseEnc>, inv: FseInvM(t, cur, Con{d, ds})) -> FseInvM(t, F.fse.enc(xs, t, cur), List.reverse.go(&2, Nat, xs, Con{d, ds})):
  match xs:
    case Nil{}:
      inv
    case Con{+x, rest}:
      match cur:
        case None{}:
          Unit{}
        case Some{F.ZsFseEnc{+tn, +acc}}:
          fse_enc_inv(rest, t, x, Con{d, ds}, F.fse.enc.found(F.fse.find(F.ZstdFse.entries(t), 0n, x, tn, None{}), t, x, tn, acc), fse_found_inv(t, x, tn, acc, d, ds, inv, F.fse.find(F.ZstdFse.entries(t), 0n, x, tn, None{})))

def fse_start_ok(+t: F.ZstdFseTable, +s: Nat, +last: Nat, b: Bool, +hb: {Nat.is_eq(F.ZstdFse.sym(F.ZstdFse.entry(t, s)), last) == b : Bool}) -> FseInvM(t, F.fse.enc.start.ok(b, s), [last]):
  match b:
    case False{}:
      Unit{}
    case True{}:
      fse_base(t, s, last, nat_eq_true(F.ZstdFse.sym(F.ZstdFse.entry(t, s)), last, hb))

def fse_start_inv(+t: F.ZstdFseTable, +last: Nat, m: Maybe<&2, Nat>) -> FseInvM(t, F.fse.enc.start(m, t, last), [last]):
  match m:
    case None{}:
      Unit{}
    case Some{+s}:
      fse_start_ok(t, s, last, Nat.is_eq(F.ZstdFse.sym(F.ZstdFse.entry(t, s)), last), {==})

def fse_proj_bits(m: Maybe<&2, List<&2, Bool>>) -> List<&2, Bool>:
  match m:
    case Some{b}:
      b
    case None{}:
      Nil{}

# the first state, written in al bits before acc, read back
def fse_first(+t: F.ZstdFseTable, +s0: Nat, +acc: List<&2, Bool>, +rest: List<&2, Bool>, +k: Nat, hlt: {Nat.is_lt(s0, Bi.ZstdBits.pow2(F.ZstdFse.al(t))) == True{} : Bool}) -> {F.ZstdFse.decode(t, List.append(&2, Bool, List.append(&2, Bool, Bi.ZstdBits.of_nat(F.ZstdFse.al(t), s0), acc), rest), 1n+k) == F.fse.dec(1n+k, t, Some{Bi.ZstdBits{s0, List.append(&2, Bool, acc, rest)}}, Nil{}) : Maybe<&2, F.ZstdFseSyms>}:
  +al = F.ZstdFse.al(t)
  +r = List.append(&2, Bool, acc, rest)
  Equal.trans(Maybe<&2, F.ZstdFseSyms>, F.fse.dec(1n+k, t, Bi.ZstdBits.read(al, List.append(&2, Bool, List.append(&2, Bool, Bi.ZstdBits.of_nat(al, s0), acc), rest)), Nil{}), F.fse.dec(1n+k, t, Bi.ZstdBits.read(al, List.append(&2, Bool, Bi.ZstdBits.of_nat(al, s0), r)), Nil{}), F.fse.dec(1n+k, t, Some{Bi.ZstdBits{s0, r}}, Nil{}), Equal.cong(List<&2, Bool>, Maybe<&2, F.ZstdFseSyms>, b => F.fse.dec(1n+k, t, Bi.ZstdBits.read(al, b), Nil{}), List.append(&2, Bool, List.append(&2, Bool, Bi.ZstdBits.of_nat(al, s0), acc), rest), List.append(&2, Bool, Bi.ZstdBits.of_nat(al, s0), r), append_assoc_bool(Bi.ZstdBits.of_nat(al, s0), acc, rest)), Equal.cong(Maybe<&2, Bi.ZstdBits>, Maybe<&2, F.ZstdFseSyms>, c => F.fse.dec(1n+k, t, c, Nil{}), Bi.ZstdBits.read(al, List.append(&2, Bool, Bi.ZstdBits.of_nat(al, s0), r)), Some{Bi.ZstdBits{s0, r}}, Laws.bits_round_trip(al, s0, r, hlt)))

def fse_fin_dec(+t: F.ZstdFseTable, +s0: Nat, +acc: List<&2, Bool>, +done: List<&2, Nat>, +k: Nat, +hn: {List.length(&2, Nat, done) == 1n+k : Nat}, inv: FseInv(t, s0, acc, done), +rest: List<&2, Bool>) -> {F.fse.dec(1n+k, t, Some{Bi.ZstdBits{s0, List.append(&2, Bool, acc, rest)}}, Nil{}) == Some{F.ZstdFseSyms{List.reverse(&2, Nat, List.reverse.go(&2, Nat, done, Nil{})), rest}} : Maybe<&2, F.ZstdFseSyms>}:
  %hn : {F.fse.dec(_, t, Some{Bi.ZstdBits{s0, List.append(&2, Bool, acc, rest)}}, Nil{}) == Some{F.ZstdFseSyms{List.reverse(&2, Nat, List.reverse.go(&2, Nat, done, Nil{})), rest}} : Maybe<&2, F.ZstdFseSyms>}
  inv(rest, Nil{})

def fse_fin_ok(+t: F.ZstdFseTable, +s0: Nat, +acc: List<&2, Bool>, +done: List<&2, Nat>, +k: Nat, +hn: {List.length(&2, Nat, done) == 1n+k : Nat}, inv: FseInv(t, s0, acc, done), +bits: List<&2, Bool>, +rest: List<&2, Bool>, b: Bool, +hb: {Nat.is_lt(s0, Bi.ZstdBits.pow2(F.ZstdFse.al(t))) == b : Bool}, h: {F.fse.enc.finish.ok(b, F.ZstdFse.al(t), s0, acc) == Some{bits} : Maybe<&2, List<&2, Bool>>}) -> {F.ZstdFse.decode(t, List.append(&2, Bool, bits, rest), List.length(&2, Nat, done)) == Some{F.ZstdFseSyms{List.reverse(&2, Nat, List.reverse.go(&2, Nat, done, Nil{})), rest}} : Maybe<&2, F.ZstdFseSyms>}:
  match b:
    case False{}:
      absurd({F.ZstdFse.decode(t, List.append(&2, Bool, bits, rest), List.length(&2, Nat, done)) == Some{F.ZstdFseSyms{List.reverse(&2, Nat, List.reverse.go(&2, Nat, done, Nil{})), rest}} : Maybe<&2, F.ZstdFseSyms>}, none_some(List<&2, Bool>, bits, h))
    case True{}:
      +hbits = Equal.cong(Maybe<&2, List<&2, Bool>>, List<&2, Bool>, m => fse_proj_bits(m), Some{List.append(&2, Bool, Bi.ZstdBits.of_nat(F.ZstdFse.al(t), s0), acc)}, Some{bits}, h)
      %hbits : {F.ZstdFse.decode(t, List.append(&2, Bool, _, rest), List.length(&2, Nat, done)) == Some{F.ZstdFseSyms{List.reverse(&2, Nat, List.reverse.go(&2, Nat, done, Nil{})), rest}} : Maybe<&2, F.ZstdFseSyms>}
      %Equal.sym(Nat, List.length(&2, Nat, done), 1n+k, hn) : {F.ZstdFse.decode(t, List.append(&2, Bool, List.append(&2, Bool, Bi.ZstdBits.of_nat(F.ZstdFse.al(t), s0), acc), rest), _) == Some{F.ZstdFseSyms{List.reverse(&2, Nat, List.reverse.go(&2, Nat, done, Nil{})), rest}} : Maybe<&2, F.ZstdFseSyms>}
      Equal.trans(Maybe<&2, F.ZstdFseSyms>, F.ZstdFse.decode(t, List.append(&2, Bool, List.append(&2, Bool, Bi.ZstdBits.of_nat(F.ZstdFse.al(t), s0), acc), rest), 1n+k), F.fse.dec(1n+k, t, Some{Bi.ZstdBits{s0, List.append(&2, Bool, acc, rest)}}, Nil{}), Some{F.ZstdFseSyms{List.reverse(&2, Nat, List.reverse.go(&2, Nat, done, Nil{})), rest}}, fse_first(t, s0, acc, rest, k, hb), fse_fin_dec(t, s0, acc, done, k, hn, inv, rest))

def fse_fin(+t: F.ZstdFseTable, m: Maybe<&2, F.ZsFseEnc>, +done: List<&2, Nat>, +k: Nat, +hn: {List.length(&2, Nat, done) == 1n+k : Nat}, inv: FseInvM(t, m, done), +bits: List<&2, Bool>, +rest: List<&2, Bool>, h: {F.fse.enc.finish(m, F.ZstdFse.al(t)) == Some{bits} : Maybe<&2, List<&2, Bool>>}) -> {F.ZstdFse.decode(t, List.append(&2, Bool, bits, rest), List.length(&2, Nat, done)) == Some{F.ZstdFseSyms{List.reverse(&2, Nat, List.reverse.go(&2, Nat, done, Nil{})), rest}} : Maybe<&2, F.ZstdFseSyms>}:
  match m:
    case None{}:
      absurd({F.ZstdFse.decode(t, List.append(&2, Bool, bits, rest), List.length(&2, Nat, done)) == Some{F.ZstdFseSyms{List.reverse(&2, Nat, List.reverse.go(&2, Nat, done, Nil{})), rest}} : Maybe<&2, F.ZstdFseSyms>}, none_some(List<&2, Bool>, bits, h))
    case Some{F.ZsFseEnc{+s0, +acc}}:
      fse_fin_ok(t, s0, acc, done, k, hn, inv, bits, rest, Nat.is_lt(s0, Bi.ZstdBits.pow2(F.ZstdFse.al(t))), {==}, h)

# the length of the symbols decoded: one, and the earlier ones
def fse_len(+last: Nat, +earlier: List<&2, Nat>) -> {List.length(&2, Nat, List.reverse.go(&2, Nat, earlier, [last])) == 1n+List.length(&2, Nat, earlier) : Nat}:
  Equal.trans(Nat, List.length(&2, Nat, List.reverse.go(&2, Nat, earlier, [last])), Nat.add(List.length(&2, Nat, earlier), 1n), 1n+List.length(&2, Nat, earlier), len_rev_go(earlier, [last]), Equal.trans(Nat, Nat.add(List.length(&2, Nat, earlier), 1n), 1n+Nat.add(List.length(&2, Nat, earlier), 0n), 1n+List.length(&2, Nat, earlier), add_succ(List.length(&2, Nat, earlier), 0n), Equal.cong(Nat, Nat, n => 1n+n, Nat.add(List.length(&2, Nat, earlier), 0n), List.length(&2, Nat, earlier), add_zero(List.length(&2, Nat, earlier)))))

# the encoder over the symbols reversed (rs): what it writes decodes to them
def fse_go(+rs: List<&2, Nat>, +t: F.ZstdFseTable, +bits: List<&2, Bool>, +rest: List<&2, Bool>, h: {F.fse.encode.go(rs, t) == Some{bits} : Maybe<&2, List<&2, Bool>>}) -> {F.ZstdFse.decode(t, List.append(&2, Bool, bits, rest), List.length(&2, Nat, List.reverse(&2, Nat, rs))) == Some{F.ZstdFseSyms{List.reverse(&2, Nat, rs), rest}} : Maybe<&2, F.ZstdFseSyms>}:
  match rs:
    case Nil{}:
      +hb = Equal.cong(Maybe<&2, List<&2, Bool>>, List<&2, Bool>, m => fse_proj_bits(m), Some{Nil{}}, Some{bits}, h)
      %hb : {F.ZstdFse.decode(t, List.append(&2, Bool, _, rest), 0n) == Some{F.ZstdFseSyms{Nil{}, rest}} : Maybe<&2, F.ZstdFseSyms>}
      {==}
    case Con{+last, +earlier}:
      +done = List.reverse.go(&2, Nat, earlier, [last])
      +m = F.fse.enc(earlier, t, F.fse.enc.start(F.fse.first(F.ZstdFse.entries(t), 0n, last, None{}), t, last))
      Equal.trans(Maybe<&2, F.ZstdFseSyms>, F.ZstdFse.decode(t, List.append(&2, Bool, bits, rest), List.length(&2, Nat, done)), Some{F.ZstdFseSyms{List.reverse(&2, Nat, List.reverse.go(&2, Nat, done, Nil{})), rest}}, Some{F.ZstdFseSyms{done, rest}}, fse_fin(t, m, done, List.length(&2, Nat, earlier), fse_len(last, earlier), fse_enc_inv(earlier, t, last, Nil{}, F.fse.enc.start(F.fse.first(F.ZstdFse.entries(t), 0n, last, None{}), t, last), fse_start_inv(t, last, F.fse.first(F.ZstdFse.entries(t), 0n, last, None{}))), bits, rest, h), Equal.cong(List<&2, Nat>, Maybe<&2, F.ZstdFseSyms>, xs => Some{F.ZstdFseSyms{xs, rest}}, List.reverse(&2, Nat, List.reverse(&2, Nat, done)), done, rev_rev_nat(done)))

def Laws.fse_round_trip(t, syms, bits, rest, h):
  %rev_rev_nat(syms) : {F.ZstdFse.decode(t, List.append(&2, Bool, bits, rest), List.length(&2, Nat, _)) == Some{F.ZstdFseSyms{_, rest}} : Maybe<&2, F.ZstdFseSyms>}
  fse_go(List.reverse(&2, Nat, syms), t, bits, rest, h)

# Huffman: what the encoder writes decodes back

def mb_val(m: Maybe<&2, Bi.ZstdBits>) -> Nat:
  match m:
    case Some{Bi.ZstdBits{v, r}}:
      v
    case None{}:
      0n

def mb_rest(m: Maybe<&2, Bi.ZstdBits>) -> List<&2, Bool>:
  match m:
    case Some{Bi.ZstdBits{v, r}}:
      r
    case None{}:
      Nil{}

# a walk that ends exactly at the end of p ends the same way before rest
def huf_walk_pre(+tr: H.ZsHufTree, +p: List<&2, Bool>, +y: Nat, +rest: List<&2, Bool>, +h: {H.ZstdHuf.walk(tr, p) == Some{Bi.ZstdBits{y, Nil{}}} : Maybe<&2, Bi.ZstdBits>}) -> {H.ZstdHuf.walk(tr, List.append(&2, Bool, p, rest)) == Some{Bi.ZstdBits{y, rest}} : Maybe<&2, Bi.ZstdBits>}:
  match tr:
    case H.ZsHufNone{}:
      absurd({H.ZstdHuf.walk(H.ZsHufNone{}, List.append(&2, Bool, p, rest)) == Some{Bi.ZstdBits{y, rest}} : Maybe<&2, Bi.ZstdBits>}, none_some(Bi.ZstdBits, Bi.ZstdBits{y, Nil{}}, h))
    case H.ZsHufLeaf{+sym}:
      +hs = Equal.cong(Maybe<&2, Bi.ZstdBits>, Nat, m => mb_val(m), Some{Bi.ZstdBits{sym, p}}, Some{Bi.ZstdBits{y, Nil{}}}, h)
      +hp = Equal.cong(Maybe<&2, Bi.ZstdBits>, List<&2, Bool>, m => mb_rest(m), Some{Bi.ZstdBits{sym, p}}, Some{Bi.ZstdBits{y, Nil{}}}, h)
      %hs : {Some{Bi.ZstdBits{sym, List.append(&2, Bool, p, rest)}} == Some{Bi.ZstdBits{_, rest}} : Maybe<&2, Bi.ZstdBits>}
      %Equal.sym(List<&2, Bool>, p, Nil{}, hp) : {Some{Bi.ZstdBits{sym, List.append(&2, Bool, _, rest)}} == Some{Bi.ZstdBits{sym, rest}} : Maybe<&2, Bi.ZstdBits>}
      {==}
    case H.ZsHufNode{+z, +o}:
      match p:
        case Nil{}:
          absurd({H.ZstdHuf.walk(H.ZsHufNode{z, o}, List.append(&2, Bool, Nil{}, rest)) == Some{Bi.ZstdBits{y, rest}} : Maybe<&2, Bi.ZstdBits>}, none_some(Bi.ZstdBits, Bi.ZstdBits{y, Nil{}}, h))
        case Con{+b, +q}:
          match b:
            case True{}:
              huf_walk_pre(o, q, y, rest, h)
            case False{}:
              huf_walk_pre(z, q, y, rest, h)

# HufInv(t, xs, acc, m): if the encoder wrote m = Some{bits} for xs, the
# decoder on bits and any rest gives xs (after acc, the symbols before them,
# reversed) and leaves the rest
def HufInv(t: H.ZstdHufTable, xs: List<&2, Nat>, acc: List<&2, Nat>, m: Maybe<&2, List<&2, Bool>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{bits}:
      @rest: List<&2, Bool> -> {H.huf.dec(List.length(&2, Nat, xs), H.ZstdHuf.tree(t), H.ZsHufGo{List.append(&2, Bool, bits, rest), acc}) == H.ZsHufGo{rest, List.reverse.go(&2, Nat, xs, acc)} : H.ZsHufDec}

def huf_mr_inv.at(+t: H.ZstdHufTable, +x: Nat, +xs: List<&2, Nat>, +acc: List<&2, Nat>, +p: List<&2, Bool>, +hw: {H.ZstdHuf.walk(H.ZstdHuf.tree(t), p) == Some{Bi.ZstdBits{x, Nil{}}} : Maybe<&2, Bi.ZstdBits>}, +b2: List<&2, Bool>, +rest: List<&2, Bool>, iv: {H.huf.dec(List.length(&2, Nat, xs), H.ZstdHuf.tree(t), H.ZsHufGo{List.append(&2, Bool, b2, rest), Con{x, acc}}) == H.ZsHufGo{rest, List.reverse.go(&2, Nat, xs, Con{x, acc})} : H.ZsHufDec}) -> {H.huf.dec(List.length(&2, Nat, Con{x, xs}), H.ZstdHuf.tree(t), H.ZsHufGo{List.append(&2, Bool, List.append(&2, Bool, p, b2), rest), acc}) == H.ZsHufGo{rest, List.reverse.go(&2, Nat, Con{x, xs}, acc)} : H.ZsHufDec}:
  +tr = H.ZstdHuf.tree(t)
  +n = List.length(&2, Nat, xs)
  +r = List.append(&2, Bool, b2, rest)
  +wk = Equal.trans(Maybe<&2, Bi.ZstdBits>, H.ZstdHuf.walk(tr, List.append(&2, Bool, List.append(&2, Bool, p, b2), rest)), H.ZstdHuf.walk(tr, List.append(&2, Bool, p, r)), Some{Bi.ZstdBits{x, r}}, Equal.cong(List<&2, Bool>, Maybe<&2, Bi.ZstdBits>, bs => H.ZstdHuf.walk(tr, bs), List.append(&2, Bool, List.append(&2, Bool, p, b2), rest), List.append(&2, Bool, p, r), append_assoc_bool(p, b2, rest)), huf_walk_pre(tr, p, x, r, hw))
  Equal.trans(H.ZsHufDec, H.huf.dec(n, tr, H.huf.push(H.ZstdHuf.walk(tr, List.append(&2, Bool, List.append(&2, Bool, p, b2), rest)), acc)), H.huf.dec(n, tr, H.huf.push(Some{Bi.ZstdBits{x, r}}, acc)), H.ZsHufGo{rest, List.reverse.go(&2, Nat, xs, Con{x, acc})}, Equal.cong(Maybe<&2, Bi.ZstdBits>, H.ZsHufDec, w => H.huf.dec(n, tr, H.huf.push(w, acc)), H.ZstdHuf.walk(tr, List.append(&2, Bool, List.append(&2, Bool, p, b2), rest)), Some{Bi.ZstdBits{x, r}}, wk), iv)

def huf_mr_inv(+t: H.ZstdHufTable, +x: Nat, +xs: List<&2, Nat>, +acc: List<&2, Nat>, +p: List<&2, Bool>, +hw: {H.ZstdHuf.walk(H.ZstdHuf.tree(t), p) == Some{Bi.ZstdBits{x, Nil{}}} : Maybe<&2, Bi.ZstdBits>}, mr: Maybe<&2, List<&2, Bool>>, ih: HufInv(t, xs, Con{x, acc}, mr)) -> HufInv(t, Con{x, xs}, acc, H.huf.cons(Some{p}, mr)):
  match mr:
    case None{}:
      Unit{}
    case Some{+b2}:
      +rest => huf_mr_inv.at(t, x, xs, acc, p, hw, b2, rest, ih(rest))

def huf_eq_inv(+t: H.ZstdHufTable, +x: Nat, +xs: List<&2, Nat>, +acc: List<&2, Nat>, +p: List<&2, Bool>, +y: Nat, +ew: {H.ZstdHuf.walk(H.ZstdHuf.tree(t), p) == Some{Bi.ZstdBits{y, Nil{}}} : Maybe<&2, Bi.ZstdBits>}, b: Bool, +hb: {Nat.is_eq(y, x) == b : Bool}, mr: Maybe<&2, List<&2, Bool>>, ih: HufInv(t, xs, Con{x, acc}, mr)) -> HufInv(t, Con{x, xs}, acc, H.huf.cons(H.huf.enc.code(b, p), mr)):
  match b:
    case False{}:
      Unit{}
    case True{}:
      +hyx = nat_eq_true(y, x, hb)
      +hw = Equal.trans(Maybe<&2, Bi.ZstdBits>, H.ZstdHuf.walk(H.ZstdHuf.tree(t), p), Some{Bi.ZstdBits{y, Nil{}}}, Some{Bi.ZstdBits{x, Nil{}}}, ew, Equal.cong(Nat, Maybe<&2, Bi.ZstdBits>, v => Some{Bi.ZstdBits{v, Nil{}}}, y, x, hyx))
      huf_mr_inv(t, x, xs, acc, p, hw, mr, ih)

def huf_walk_inv(+t: H.ZstdHufTable, +x: Nat, +xs: List<&2, Nat>, +acc: List<&2, Nat>, +p: List<&2, Bool>, w: Maybe<&2, Bi.ZstdBits>, +ew: {H.ZstdHuf.walk(H.ZstdHuf.tree(t), p) == w : Maybe<&2, Bi.ZstdBits>}, mr: Maybe<&2, List<&2, Bool>>, ih: HufInv(t, xs, Con{x, acc}, mr)) -> HufInv(t, Con{x, xs}, acc, H.huf.cons(H.huf.enc.code(H.huf.enc.ok(w, x), p), mr)):
  match w:
    case None{}:
      Unit{}
    case Some{Bi.ZstdBits{+y, r}}:
      match r:
        case Con{bb, rr}:
          Unit{}
        case Nil{}:
          huf_eq_inv(t, x, xs, acc, p, y, ew, Nat.is_eq(y, x), {==}, mr, ih)

def huf_cons_inv(+t: H.ZstdHufTable, +x: Nat, +xs: List<&2, Nat>, +acc: List<&2, Nat>, mc: Maybe<&2, List<&2, Bool>>, mr: Maybe<&2, List<&2, Bool>>, ih: HufInv(t, xs, Con{x, acc}, mr)) -> HufInv(t, Con{x, xs}, acc, H.huf.cons(H.huf.enc.sym(mc, H.ZstdHuf.tree(t), x), mr)):
  match mc:
    case None{}:
      Unit{}
    case Some{+p}:
      huf_walk_inv(t, x, xs, acc, p, H.ZstdHuf.walk(H.ZstdHuf.tree(t), p), {==}, mr, ih)

# every symbol list keeps the invariant
def huf_inv(+t: H.ZstdHufTable, +xs: List<&2, Nat>, +acc: List<&2, Nat>) -> HufInv(t, xs, acc, H.ZstdHuf.encode(t, xs)):
  match xs:
    case Nil{}:
      +rest => {==}
    case Con{+x, +r}:
      huf_cons_inv(t, x, r, acc, H.ZstdHuf.code(t, x), H.ZstdHuf.encode(t, r), huf_inv(t, r, Con{x, acc}))

def huf_use(+t: H.ZstdHufTable, +syms: List<&2, Nat>, +rest: List<&2, Bool>, m: Maybe<&2, List<&2, Bool>>, inv: HufInv(t, syms, Nil{}, m), +bits: List<&2, Bool>, +h: {m == Some{bits} : Maybe<&2, List<&2, Bool>>}) -> {H.ZstdHuf.decode(t, List.append(&2, Bool, bits, rest), List.length(&2, Nat, syms)) == Some{H.ZstdHufSyms{syms, rest}} : Maybe<&2, H.ZstdHufSyms>}:
  match m:
    case None{}:
      absurd({H.ZstdHuf.decode(t, List.append(&2, Bool, bits, rest), List.length(&2, Nat, syms)) == Some{H.ZstdHufSyms{syms, rest}} : Maybe<&2, H.ZstdHufSyms>}, none_some(List<&2, Bool>, bits, h))
    case Some{+b}:
      +hb = Equal.cong(Maybe<&2, List<&2, Bool>>, List<&2, Bool>, mm => fse_proj_bits(mm), Some{b}, Some{bits}, h)
      %hb : {H.ZstdHuf.decode(t, List.append(&2, Bool, _, rest), List.length(&2, Nat, syms)) == Some{H.ZstdHufSyms{syms, rest}} : Maybe<&2, H.ZstdHufSyms>}
      Equal.trans(Maybe<&2, H.ZstdHufSyms>, H.huf.dec.out(H.huf.dec(List.length(&2, Nat, syms), H.ZstdHuf.tree(t), H.ZsHufGo{List.append(&2, Bool, b, rest), Nil{}})), H.huf.dec.out(H.ZsHufGo{rest, List.reverse.go(&2, Nat, syms, Nil{})}), Some{H.ZstdHufSyms{syms, rest}}, Equal.cong(H.ZsHufDec, Maybe<&2, H.ZstdHufSyms>, d => H.huf.dec.out(d), H.huf.dec(List.length(&2, Nat, syms), H.ZstdHuf.tree(t), H.ZsHufGo{List.append(&2, Bool, b, rest), Nil{}}), H.ZsHufGo{rest, List.reverse.go(&2, Nat, syms, Nil{})}, inv(rest)), Equal.cong(List<&2, Nat>, Maybe<&2, H.ZstdHufSyms>, xs => Some{H.ZstdHufSyms{xs, rest}}, List.reverse(&2, Nat, List.reverse(&2, Nat, syms)), syms, rev_rev_nat(syms)))

def Laws.huf_round_trip(t, syms, bits, rest, h):
  huf_use(t, syms, rest, H.ZstdHuf.encode(t, syms), huf_inv(t, syms, Nil{}), bits, h)

# The frame of raw blocks: the machine, a byte at a time

def rf_cfg() -> Fr.ZsCfg:
  Fr.ZsCfg{D.ZstdDict{0, Nil{}, None{}, S.ZstdSeqTables.none(), K.ZstdReps.initial()}, 0n, True{}, 134217728}

def rf_state(+p: Nat, +out: List<&2, U32>, win: K.ZstdWindow) -> Fr.ZstdDecoder:
  Fr.ZstdDecoder{Fr.ZsPhBlock{0n, Nil{}}, Fr.ZsFrm{1024n, 1024n, False{}, None{}, K.ZstdBlockState{None{}, S.ZstdSeqTables.none(), K.ZstdReps.initial(), p}, X.ZstdXxh64.start(W.W64.zero())}, out, Fr.ZsRoomAny{}, rf_cfg(), win}

def rf_head(+xs: List<&2, U32>) -> {Fr.ZstdFrame.run(Con{40, Con{181, Con{47, Con{253, Con{0, Con{0, xs}}}}}}, Z.Zstd.start(Z.ZstdOptions.unlimited())) == Fr.ZstdFrame.run(xs, rf_state(0n, Nil{}, K.ZstdWin.new(10n))) : Fr.ZstdDecoder}:
  {==}

def rf_p(xs: List<&2, U32>, p: Nat) -> Nat:
  match xs:
    case Nil{}:
      p
    case Con{h, t}:
      rf_p(t, 1n+p)

# each byte's block (raw, size 1) puts the byte out and in the window
def rf_blocks(+xs: List<&2, U32>, +p: Nat, +out: List<&2, U32>, win: K.ZstdWindow) -> {Fr.ZstdFrame.run(C.cmp.raw_blocks(xs), rf_state(p, out, win)) == Fr.ZstdFrame.run([1, 0, 0], rf_state(rf_p(xs, p), B.rev_onto(xs, out), K.ZstdWin.puts(xs, win))) : Fr.ZstdDecoder}:
  match xs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      rf_blocks(t, 1n+p, Con{b, out}, K.ZstdWin.put(win, b))

def rf_end(+p: Nat, +out: List<&2, U32>, win: K.ZstdWindow) -> {Fr.ZstdFrame.finish(Fr.ZstdFrame.run([1, 0, 0], rf_state(p, out, win))) == Done{B.rev(out)} : Result<&2, &2, E.ZstdError, List<&2, U32>>}:
  {==}

def mask_rb(+xs: List<&2, U32>) -> {C.cmp.raw_blocks(B.mask(xs)) == B.mask(C.cmp.raw_blocks(xs)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %mask_rb(t) : {Con{8, Con{0, Con{0, Con{B.byte(b), C.cmp.raw_blocks(B.mask(t))}}}} == Con{8, Con{0, Con{0, Con{B.byte(b), _}}}} : List<&2, U32>}
      {==}

# the bytes of an Octets are already masked
def mask_id(+o: B.Octets) -> {B.Octets.to_list(o) == B.mask(B.Octets.to_list(o)) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.Octets.to_list(o), B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(o))), B.mask(B.Octets.to_list(o)), Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.Octets.to_list(o))), B.Octets.to_list(o), Equal.cong(B.Octets, List<&2, U32>, z => B.Octets.to_list(z), B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o))), BL.octets_to_of(B.Octets.to_list(o)))

def Laws.raw_frame_round_trip(o):
  +x = B.Octets.to_list(o)
  +hd = {Con{40, Con{181, Con{47, Con{253, Con{0, Con{0, C.cmp.raw_blocks(x)}}}}}} : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(hd)), B.mask(hd), BL.octets_to_of(hd)) : {Z.zstd.fin(Fr.ZstdFrame.finish(Fr.ZstdFrame.run(_, Z.Zstd.start(Z.ZstdOptions.unlimited())))) == Done{o} : Result<&2, &2, E.ZstdError, B.Octets>}
  %mask_rb(x) : {Z.zstd.fin(Fr.ZstdFrame.finish(Fr.ZstdFrame.run(Con{40, Con{181, Con{47, Con{253, Con{0, Con{0, _}}}}}}, Z.Zstd.start(Z.ZstdOptions.unlimited())))) == Done{o} : Result<&2, &2, E.ZstdError, B.Octets>}
  %mask_id(o) : {Z.zstd.fin(Fr.ZstdFrame.finish(Fr.ZstdFrame.run(Con{40, Con{181, Con{47, Con{253, Con{0, Con{0, C.cmp.raw_blocks(_)}}}}}}, Z.Zstd.start(Z.ZstdOptions.unlimited())))) == Done{o} : Result<&2, &2, E.ZstdError, B.Octets>}
  %Equal.sym(Fr.ZstdDecoder, Fr.ZstdFrame.run(hd, Z.Zstd.start(Z.ZstdOptions.unlimited())), Fr.ZstdFrame.run(C.cmp.raw_blocks(x), rf_state(0n, Nil{}, K.ZstdWin.new(10n))), rf_head(C.cmp.raw_blocks(x))) : {Z.zstd.fin(Fr.ZstdFrame.finish(_)) == Done{o} : Result<&2, &2, E.ZstdError, B.Octets>}
  %Equal.sym(Fr.ZstdDecoder, Fr.ZstdFrame.run(C.cmp.raw_blocks(x), rf_state(0n, Nil{}, K.ZstdWin.new(10n))), Fr.ZstdFrame.run([1, 0, 0], rf_state(rf_p(x, 0n), B.rev_onto(x, Nil{}), K.ZstdWin.puts(x, K.ZstdWin.new(10n)))), rf_blocks(x, 0n, Nil{}, K.ZstdWin.new(10n))) : {Z.zstd.fin(Fr.ZstdFrame.finish(_)) == Done{o} : Result<&2, &2, E.ZstdError, B.Octets>}
  %Equal.sym(Result<&2, &2, E.ZstdError, List<&2, U32>>, Fr.ZstdFrame.finish(Fr.ZstdFrame.run([1, 0, 0], rf_state(rf_p(x, 0n), B.rev_onto(x, Nil{}), K.ZstdWin.puts(x, K.ZstdWin.new(10n))))), Done{B.rev(B.rev_onto(x, Nil{}))}, rf_end(rf_p(x, 0n), B.rev_onto(x, Nil{}), K.ZstdWin.puts(x, K.ZstdWin.new(10n)))) : {Z.zstd.fin(_) == Done{o} : Result<&2, &2, E.ZstdError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.rev(B.rev(x)), x, BL.rev_rev(x)) : {Done{B.Octets.of_list(_)} == Done{o} : Result<&2, &2, E.ZstdError, B.Octets>}
  %BL.octets_of_to(o) : {Done{B.Octets.of_list(B.Octets.to_list(o))} == Done{_} : Result<&2, &2, E.ZstdError, B.Octets>}
  {==}

# The compressor's check: equal bytes, by comparing their bits

def bit_eq_true(+x: Bool, +y: Bool, h: {Bool.not(Bool.xor(x, y)) == True{} : Bool}) -> {x == y : Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      absurd({True{} == False{} : Bool}, false_not_true(h))
    case False{} True{}:
      absurd({False{} == True{} : Bool}, false_not_true(h))
    case False{} False{}:
      {==}

def weq_true(+n: Nat, +a: Word(n), +b: Word(n), +h: {C.cmp.weq(n, a, b) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{+x, +s} WCon{+y, +t}:
          +hx = bit_eq_true(x, y, and_true_l(Bool.not(Bool.xor(x, y)), C.cmp.weq(p, s, t), h))
          +hs = weq_true(p, s, t, and_true_r(Bool.not(Bool.xor(x, y)), C.cmp.weq(p, s, t), h))
          %hx : {WCon{x, s} == WCon{_, t} : Word(1n+p)}
          %hs : {WCon{x, s} == WCon{x, _} : Word(1n+p)}
          {==}

def u32_eq_true(+a: U32, +b: U32, h: {C.cmp.u32_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, weq_true(32n, x, y, h))

def same_go_live(+xs: List<&2, U32>, +ys: List<&2, U32>, +live: Bool, +h: {C.cmp.same.go(xs, ys, live) == True{} : Bool}) -> {live == True{} : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      h
    case Con{+a, +s} Con{+b, +t}:
      and_true_l(live, C.cmp.u32_eq(a, b), same_go_live(s, t, Bool.and(live, C.cmp.u32_eq(a, b)), h))
    case Nil{} Con{b, t}:
      absurd({live == True{} : Bool}, false_not_true(h))
    case Con{a, s} Nil{}:
      absurd({live == True{} : Bool}, false_not_true(h))

def same_go_true(+xs: List<&2, U32>, +ys: List<&2, U32>, +live: Bool, +h: {C.cmp.same.go(xs, ys, live) == True{} : Bool}) -> {xs == ys : List<&2, U32>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Con{+a, +s} Con{+b, +t}:
      +ab = u32_eq_true(a, b, and_true_r(live, C.cmp.u32_eq(a, b), same_go_live(s, t, Bool.and(live, C.cmp.u32_eq(a, b)), h)))
      +st = same_go_true(s, t, Bool.and(live, C.cmp.u32_eq(a, b)), h)
      %ab : {Con{a, s} == Con{_, t} : List<&2, U32>}
      %st : {Con{a, s} == Con{a, _} : List<&2, U32>}
      {==}
    case Nil{} Con{b, t}:
      absurd({Nil{} == Con{b, t} : List<&2, U32>}, false_not_true(h))
    case Con{a, s} Nil{}:
      absurd({Con{a, s} == Nil{} : List<&2, U32>}, false_not_true(h))

# byte strings with the same bytes are the same
def octets_eq(+d: B.Octets, +o: B.Octets, h: {B.Octets.to_list(d) == B.Octets.to_list(o) : List<&2, U32>}) -> {d == o : B.Octets}:
  Equal.trans(B.Octets, d, B.Octets.of_list(B.Octets.to_list(o)), o, Equal.trans(B.Octets, d, B.Octets.of_list(B.Octets.to_list(d)), B.Octets.of_list(B.Octets.to_list(o)), Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(d)), d, BL.octets_of_to(d)), Equal.cong(List<&2, U32>, B.Octets, z => B.Octets.of_list(z), B.Octets.to_list(d), B.Octets.to_list(o), h)), BL.octets_of_to(o))

def cr_same(+o: B.Octets, +c: B.Octets, +d: B.Octets, +er: {Z.decompress_with(Z.ZstdOptions.unlimited(), c) == Done{d} : Result<&2, &2, E.ZstdError, B.Octets>}, b: Bool, +hb: {C.cmp.same(B.Octets.to_list(d), B.Octets.to_list(o)) == b : Bool}) -> {Z.decompress_with(Z.ZstdOptions.unlimited(), C.cmp.keep(b, c, o)) == Done{o} : Result<&2, &2, E.ZstdError, B.Octets>}:
  match b:
    case True{}:
      Equal.trans(Result<&2, &2, E.ZstdError, B.Octets>, Z.decompress_with(Z.ZstdOptions.unlimited(), c), Done{d}, Done{o}, er, Equal.cong(B.Octets, Result<&2, &2, E.ZstdError, B.Octets>, z => Done{z}, d, o, octets_eq(d, o, same_go_true(B.Octets.to_list(d), B.Octets.to_list(o), True{}, hb))))
    case False{}:
      Laws.raw_frame_round_trip(o)

def cr_keep(+o: B.Octets, +c: B.Octets, r: Result<&2, &2, E.ZstdError, B.Octets>, +er: {Z.decompress_with(Z.ZstdOptions.unlimited(), c) == r : Result<&2, &2, E.ZstdError, B.Octets>}) -> {Z.decompress_with(Z.ZstdOptions.unlimited(), C.cmp.check(r, c, o)) == Done{o} : Result<&2, &2, E.ZstdError, B.Octets>}:
  match r:
    case Fail{e}:
      Laws.raw_frame_round_trip(o)
    case Done{+d}:
      cr_same(o, c, d, er, C.cmp.same(B.Octets.to_list(d), B.Octets.to_list(o)), {==})

def Laws.compress_round_trip(opts, o):
  cr_keep(o, C.compress_unchecked(opts, o), Z.decompress_with(Z.ZstdOptions.unlimited(), C.compress_unchecked(opts, o)), {==})

# Bad magic numbers

def or_false_l(+a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      absurd({True{} == False{} : Bool}, true_not_false(h))
    case False{}:
      {==}

def or_false_r(+a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      absurd({b == False{} : Bool}, true_not_false(h))
    case False{}:
      h

def bm_cfg(+verify: Bool, +mw: U32) -> Fr.ZsCfg:
  Fr.ZsCfg{D.ZstdDict{0, Nil{}, None{}, S.ZstdSeqTables.none(), K.ZstdReps.initial()}, 0n, verify, mw}

def bm_bad(+limit: Fr.ZstdLimit, +verify: Bool, +mw: U32) -> Fr.ZstdDecoder:
  Fr.frm.bad(E.ZstdBadMagic{}, Fr.frm.none(), Nil{}, Z.zstd.room(limit), bm_cfg(verify, mw), K.ZstdWin.new(0n))

def bm_classify(z: Bool, s: Bool, hz: {z == False{} : Bool}, hs: {s == False{} : Bool}, +limit: Fr.ZstdLimit, +verify: Bool, +mw: U32) -> {Fr.frm.classify(z, s, Fr.frm.none(), Nil{}, Z.zstd.room(limit), bm_cfg(verify, mw), K.ZstdWin.new(0n)) == bm_bad(limit, verify, mw) : Fr.ZstdDecoder}:
  match z:
    case True{}:
      absurd({Fr.frm.classify(True{}, s, Fr.frm.none(), Nil{}, Z.zstd.room(limit), bm_cfg(verify, mw), K.ZstdWin.new(0n)) == bm_bad(limit, verify, mw) : Fr.ZstdDecoder}, true_not_false(hz))
    case False{}:
      match s:
        case True{}:
          absurd({Fr.frm.classify(False{}, True{}, Fr.frm.none(), Nil{}, Z.zstd.room(limit), bm_cfg(verify, mw), K.ZstdWin.new(0n)) == bm_bad(limit, verify, mw) : Fr.ZstdDecoder}, true_not_false(hs))
        case False{}:
          {==}

# a failed decoder stays failed
def bad_absorbs(+xs: List<&2, U32>, +e: E.ZstdError, +f: Fr.ZsFrm, +out: List<&2, U32>, +room: Fr.ZsRoom, +cfg: Fr.ZsCfg, win: K.ZstdWindow) -> {Fr.ZstdFrame.run(xs, Fr.ZstdDecoder{Fr.ZsPhBad{e}, f, out, room, cfg, win}) == Fr.ZstdDecoder{Fr.ZsPhBad{e}, f, out, room, cfg, win} : Fr.ZstdDecoder}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      bad_absorbs(t, e, f, out, room, cfg, win)

def guard_fail(+limit: Fr.ZstdLimit, +e: E.ZstdError) -> {Z.zstd.guard(limit, Fail{e}) == Fail{e} : Result<&2, &2, E.ZstdError, B.Octets>}:
  match limit:
    case Fr.ZstdNoLimit{}:
      {==}
    case Fr.ZstdLimit{max}:
      {==}

def Laws.bad_magic_refused(limit, verify, mw, a, b, c, d, rest, h):
  +xs = {[a, b, c, d] : List<&2, U32>}
  +opts = {Z.ZstdOptions{limit, verify, B.Octets.empty(), mw} : Z.ZstdOptions}
  +hz = or_false_l(Fr.ZstdFrame.is_zstd(B.mask(xs)), Fr.ZstdFrame.is_skippable(B.mask(xs)), h)
  +hs = or_false_r(Fr.ZstdFrame.is_zstd(B.mask(xs)), Fr.ZstdFrame.is_skippable(B.mask(xs)), h)
  +run4 = {bm_classify(Fr.ZstdFrame.is_zstd(B.mask(xs)), Fr.ZstdFrame.is_skippable(B.mask(xs)), hz, hs, limit, verify, mw) : {Fr.ZstdFrame.run(B.mask(xs), Z.Zstd.start(opts)) == bm_bad(limit, verify, mw) : Fr.ZstdDecoder}}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.of_list(xs), rest)), B.append(B.Octets.to_list(B.Octets.of_list(xs)), B.Octets.to_list(rest)), BL.octets_append_list(B.Octets.of_list(xs), rest)) : {Z.zstd.guard(limit, Z.zstd.fin(Fr.ZstdFrame.finish(Fr.ZstdFrame.run(_, Z.Zstd.start(opts))))) == Fail{E.ZstdBadMagic{}} : Result<&2, &2, E.ZstdError, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(xs)), B.mask(xs), BL.octets_to_of(xs)) : {Z.zstd.guard(limit, Z.zstd.fin(Fr.ZstdFrame.finish(Fr.ZstdFrame.run(B.append(_, B.Octets.to_list(rest)), Z.Zstd.start(opts))))) == Fail{E.ZstdBadMagic{}} : Result<&2, &2, E.ZstdError, B.Octets>}
  %Equal.sym(Fr.ZstdDecoder, Fr.ZstdFrame.run(B.append(B.mask(xs), B.Octets.to_list(rest)), Z.Zstd.start(opts)), Fr.ZstdFrame.run(B.Octets.to_list(rest), Fr.ZstdFrame.run(B.mask(xs), Z.Zstd.start(opts))), run_append(B.mask(xs), B.Octets.to_list(rest), Z.Zstd.start(opts))) : {Z.zstd.guard(limit, Z.zstd.fin(Fr.ZstdFrame.finish(_))) == Fail{E.ZstdBadMagic{}} : Result<&2, &2, E.ZstdError, B.Octets>}
  %Equal.sym(Fr.ZstdDecoder, Fr.ZstdFrame.run(B.mask(xs), Z.Zstd.start(opts)), bm_bad(limit, verify, mw), run4) : {Z.zstd.guard(limit, Z.zstd.fin(Fr.ZstdFrame.finish(Fr.ZstdFrame.run(B.Octets.to_list(rest), _)))) == Fail{E.ZstdBadMagic{}} : Result<&2, &2, E.ZstdError, B.Octets>}
  %Equal.sym(Fr.ZstdDecoder, Fr.ZstdFrame.run(B.Octets.to_list(rest), bm_bad(limit, verify, mw)), bm_bad(limit, verify, mw), bad_absorbs(B.Octets.to_list(rest), E.ZstdBadMagic{}, Fr.frm.none(), Nil{}, Z.zstd.room(limit), bm_cfg(verify, mw), K.ZstdWin.new(0n))) : {Z.zstd.guard(limit, Z.zstd.fin(Fr.ZstdFrame.finish(_))) == Fail{E.ZstdBadMagic{}} : Result<&2, &2, E.ZstdError, B.Octets>}
  guard_fail(limit, E.ZstdBadMagic{})

# Witnesses and vectors: by computation

def Laws.witness_bits():
  {==}

def Laws.witness_fse():
  {==}

def Laws.witness_huf():
  {==}

def Laws.witness_bad_magic():
  {==}

def Laws.rfc_huffman_weights():
  {==}

def Laws.rfc_huffman_code_0():
  {==}

def Laws.rfc_huffman_code_1():
  {==}

def Laws.rfc_huffman_code_2():
  {==}

def Laws.rfc_huffman_code_3():
  {==}

def Laws.rfc_huffman_code_4():
  {==}

def Laws.rfc_huffman_code_5():
  {==}

def Laws.rfc_predefined_ll():
  {==}

def Laws.rfc_predefined_ml():
  {==}

def Laws.rfc_predefined_of():
  {==}

def Laws.xxh64_empty():
  {==}

def Laws.xxh64_abc():
  {==}

def Laws.frame_empty_input():
  {==}

def Laws.frame_raw():
  {==}

def Laws.frame_rle_checksum():
  {==}

def Laws.frame_skippable():
  {==}

def Laws.frame_two():
  {==}

def Laws.frame_compressed():
  {==}

def Laws.frame_huffman():
  {==}

def Laws.frame_dictionary():
  {==}

def Laws.frame_bad_magic():
  {==}

def Laws.frame_bad_checksum():
  {==}

def Laws.frame_reserved_bit():
  {==}

def Laws.frame_block_type_3():
  {==}

def Laws.frame_content_size():
  {==}

def Laws.frame_window_too_large():
  {==}

def Laws.frame_dictionary_mismatch():
  {==}

def Laws.frame_truncated():
  {==}

def Laws.frame_output_limit():
  {==}

def Laws.frame_block_too_large():
  {==}

def Laws.frame_literals_exhausted():
  {==}

def Laws.frame_bad_offset():
  {==}

def Laws.frame_no_huffman_tree():
  {==}

def Laws.frame_no_fse_table():
  {==}

def Laws.frame_sequences_reserved():
  {==}

def Laws.compress_empty():
  {==}

def Laws.compress_rle():
  {==}

def Laws.compress_matches():
  {==}

def Laws.raw_frame_bytes():
  {==}
