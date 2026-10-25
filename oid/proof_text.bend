# Proofs for bend-osdev-oid: the dotted text of a valid Oid reads back as it.
# Decimal digits read back by Horner's rule, are below 10, and lead with a
# non-zero digit (for arcs above 0); with proof_digit.bend's facts about
# each digit's character, the text cuts at its full stops into the arcs' texts.
import Base
import ./oid.bend as O
import ./text.bend as T
import ./proof_nat.bend as ON
import ./proof_digit.bend as OG
import ../u32/LAWS.bend as UL
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF.bend as UP
import ../u32/PROOF_order.bend as UOP
import ../u32/LAWS_div.bend as UD
import ../u32/PROOF_div.bend as UDP

# Decimal digits

def ot.all_lt(ds: List<&2, Nat>, +b: Nat) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, t}:
      Bool.and(Nat.is_lt(d, b), ot.all_lt(t, b))

def ot.all_lt_app(xs: List<&2, Nat>, +ys: List<&2, Nat>, +b: Nat, +hx: {ot.all_lt(xs, b) == True{} : Bool}, +hy: {ot.all_lt(ys, b) == True{} : Bool}) -> {ot.all_lt(List.append(&2, Nat, xs, ys), b) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+d, +t}:
      ON.on.and_i(Nat.is_lt(d, b), ot.all_lt(List.append(&2, Nat, t, ys), b), ON.on.and_l(Nat.is_lt(d, b), ot.all_lt(t, b), hx), ot.all_lt_app(t, ys, b, ON.on.and_r(Nat.is_lt(d, b), ot.all_lt(t, b), hx), hy))

def ot.horner(ds: List<&2, Nat>, acc: Nat) -> Nat:
  match ds:
    case Nil{}:
      acc
    case Con{d, t}:
      ot.horner(t, Nat.add(Nat.mul(acc, 10n), d))

def ot.horner_snoc(xs: List<&2, Nat>, +acc: Nat, +d: Nat) -> {ot.horner(List.append(&2, Nat, xs, [d]), acc) == Nat.add(Nat.mul(ot.horner(xs, acc), 10n), d) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      ot.horner_snoc(t, Nat.add(Nat.mul(acc, 10n), x), d)

def ot.horner_digits(fuel: Nat, lt: Bool, +n: Nat) -> {ot.horner(O.oid.dg.go(fuel, lt, n), 0n) == n : Nat}:
  match fuel lt:
    case _ True{}:
      {==}
    case 0n False{}:
      {==}
    case 1n+ +f False{}:
      +q = Nat.div(n, 10n)
      +ds = O.oid.dg.go(f, Nat.is_lt(q, 10n), q)
      %Equal.sym(Nat, ot.horner(List.append(&2, Nat, ds, [Nat.mod(n, 10n)]), 0n), Nat.add(Nat.mul(ot.horner(ds, 0n), 10n), Nat.mod(n, 10n)), ot.horner_snoc(ds, 0n, Nat.mod(n, 10n))) : {_ == n : Nat}
      %Equal.sym(Nat, ot.horner(ds, 0n), q, ot.horner_digits(f, Nat.is_lt(q, 10n), q)) : {Nat.add(Nat.mul(_, 10n), Nat.mod(n, 10n)) == n : Nat}
      UD.nat_div_mod(n, 9n)

def ot.le_not_lt(+a: Nat, +b: Nat) -> {Nat.is_le(a, b) == Bool.not(Nat.is_lt(b, a)) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ot.le_not_lt(p, q)

def ot.digits_lt(fuel: Nat, lt: Bool, +n: Nat, +hl: {Nat.is_lt(n, 10n) == lt : Bool}, +hf: {Nat.is_le(n, fuel) == True{} : Bool}) -> {ot.all_lt(O.oid.dg.go(fuel, lt, n), 10n) == True{} : Bool}:
  match fuel lt:
    case _ True{}:
      %Equal.sym(Bool, Nat.is_lt(n, 10n), True{}, hl) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case 0n False{}:
      match n:
        case 0n:
          Empty.absurd({ot.all_lt([0n], 10n) == True{} : Bool}, ON.on.tf(hl))
        case 1n+m:
          Empty.absurd({ot.all_lt([1n+m], 10n) == True{} : Bool}, ON.on.ft(hf))
    case 1n+ +f False{}:
      +q = Nat.div(n, 10n)
      +hb = Equal.trans(Bool, Nat.is_le(10n, n), Bool.not(Nat.is_lt(n, 10n)), True{}, ot.le_not_lt(10n, n), Equal.cong(Bool, Bool, z => Bool.not(z), Nat.is_lt(n, 10n), False{}, hl))
      +hq = ON.on.lt_succ_le(q, f, UO.nat_lt_le_trans(q, n, 1n+f, ON.on.div_lt(n, 8n, hb), hf))
      +ih = ot.digits_lt(f, Nat.is_lt(q, 10n), q, {==}, hq)
      ot.all_lt_app(O.oid.dg.go(f, Nat.is_lt(q, 10n), q), [Nat.mod(n, 10n)], 10n, ih, ON.on.and_i(Nat.is_lt(Nat.mod(n, 10n), 10n), True{}, UD.nat_mod_lt(n, 9n), {==}))

def ot.digits_lt_top(+n: Nat) -> {ot.all_lt(O.oid.digits(n), 10n) == True{} : Bool}:
  ot.digits_lt(n, Nat.is_lt(n, 10n), n, {==}, UL.nat_le_refl(n))

def ot.head(ds: List<&2, Nat>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{d, t}:
      d

def ot.ne(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, t}:
      True{}

def ot.head_app(xs: List<&2, Nat>, +d: Nat, +h: {ot.ne(xs) == True{} : Bool}) -> {ot.head(List.append(&2, Nat, xs, [d])) == ot.head(xs) : Nat}:
  match xs:
    case Nil{}:
      Empty.absurd({ot.head([d]) == 0n : Nat}, ON.on.ft(h))
    case Con{x, t}:
      {==}

def ot.ne_app(xs: List<&2, Nat>, +d: Nat) -> {ot.ne(List.append(&2, Nat, xs, [d])) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

def ot.digits_ne(fuel: Nat, lt: Bool, +n: Nat) -> {ot.ne(O.oid.dg.go(fuel, lt, n)) == True{} : Bool}:
  match fuel lt:
    case _ True{}:
      {==}
    case 0n False{}:
      {==}
    case 1n+ +f False{}:
      +q = Nat.div(n, 10n)
      +xs = O.oid.dg.go(f, Nat.is_lt(q, 10n), q)
      ot.ne_app(xs, Nat.mod(n, 10n))

def ot.q_pos.go(q: Nat, +r: Nat, +n: Nat, +hr: {Nat.add(Nat.mul(q, 10n), r) == n : Nat}, +hm: {Nat.is_lt(r, 10n) == True{} : Bool}, +h: {Nat.is_le(10n, n) == True{} : Bool}) -> {Nat.is_le(1n, q) == True{} : Bool}:
  match q:
    case 0n:
      +x = Equal.trans(Bool, False{}, Bool.not(Nat.is_lt(r, 10n)), Nat.is_le(10n, r), Equal.cong(Bool, Bool, z => Bool.not(z), True{}, Nat.is_lt(r, 10n), Equal.sym(Bool, Nat.is_lt(r, 10n), True{}, hm)), Equal.sym(Bool, Nat.is_le(10n, r), Bool.not(Nat.is_lt(r, 10n)), ot.le_not_lt(10n, r)))
      +y = Equal.trans(Bool, Nat.is_le(10n, r), Nat.is_le(10n, n), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(10n, z), r, n, hr), h)
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, ON.on.ft(Equal.trans(Bool, False{}, Nat.is_le(10n, r), True{}, x, y)))
    case 1n+p:
      ON.on.le_zero(p)

# n >= 10 implies n / 10 >= 1
def ot.q_pos(+n: Nat, +h: {Nat.is_le(10n, n) == True{} : Bool}) -> {Nat.is_le(1n, Nat.div(n, 10n)) == True{} : Bool}:
  ot.q_pos.go(Nat.div(n, 10n), Nat.mod(n, 10n), n, UD.nat_div_mod(n, 9n), UD.nat_mod_lt(n, 9n), h)

# the leading digit of an arc above 0 is not 0
def ot.head_pos(fuel: Nat, lt: Bool, +n: Nat, +hl: {Nat.is_lt(n, 10n) == lt : Bool}, +hn: {Nat.is_le(1n, n) == True{} : Bool}) -> {Nat.is_le(1n, ot.head(O.oid.dg.go(fuel, lt, n))) == True{} : Bool}:
  match fuel lt:
    case _ True{}:
      hn
    case 0n False{}:
      hn
    case 1n+ +f False{}:
      +q = Nat.div(n, 10n)
      +xs = O.oid.dg.go(f, Nat.is_lt(q, 10n), q)
      +hb = Equal.trans(Bool, Nat.is_le(10n, n), Bool.not(Nat.is_lt(n, 10n)), True{}, ot.le_not_lt(10n, n), Equal.cong(Bool, Bool, z => Bool.not(z), Nat.is_lt(n, 10n), False{}, hl))
      %Equal.sym(Nat, ot.head(List.append(&2, Nat, xs, [Nat.mod(n, 10n)])), ot.head(xs), ot.head_app(xs, Nat.mod(n, 10n), ot.digits_ne(f, Nat.is_lt(q, 10n), q))) : {Nat.is_le(1n, _) == True{} : Bool}
      ot.head_pos(f, Nat.is_lt(q, 10n), q, {==}, ot.q_pos(n, hb))

# Cutting text at full stops

def ot.split_dot(ds: List<&2, Nat>, +rest: String, +h: {ot.all_lt(ds, 10n) == True{} : Bool}) -> {T.oid.split(T.oid.dstr(ds, SCon{'.', rest})) == Con{T.oid.dstr(ds, SNil{}), T.oid.split(rest)} : List<&2, String>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      +hd = ON.on.and_l(Nat.is_lt(d, 10n), ot.all_lt(t, 10n), h)
      +ht = ON.on.and_r(Nat.is_lt(d, 10n), ot.all_lt(t, 10n), h)
      +c = T.oid.dchar(d)
      +want : List<&2, String> = Con{SCon{c, T.oid.dstr(t, SNil{})}, T.oid.split(rest)}
      %Equal.sym(Bool, T.oid.is_dot(c), False{}, OG.og.notdot(d, hd)) : {T.oid.split.step(_, c, T.oid.split(T.oid.dstr(t, SCon{'.', rest}))) == want : List<&2, String>}
      %Equal.sym(List<&2, String>, T.oid.split(T.oid.dstr(t, SCon{'.', rest})), Con{T.oid.dstr(t, SNil{}), T.oid.split(rest)}, ot.split_dot(t, rest, ht)) : {T.oid.put_first(c, _) == want : List<&2, String>}
      {==}

def ot.split_end(ds: List<&2, Nat>, +h: {ot.all_lt(ds, 10n) == True{} : Bool}) -> {T.oid.split(T.oid.dstr(ds, SNil{})) == [T.oid.dstr(ds, SNil{})] : List<&2, String>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      +hd = ON.on.and_l(Nat.is_lt(d, 10n), ot.all_lt(t, 10n), h)
      +ht = ON.on.and_r(Nat.is_lt(d, 10n), ot.all_lt(t, 10n), h)
      +c = T.oid.dchar(d)
      +want : List<&2, String> = [SCon{c, T.oid.dstr(t, SNil{})}]
      %Equal.sym(Bool, T.oid.is_dot(c), False{}, OG.og.notdot(d, hd)) : {T.oid.split.step(_, c, T.oid.split(T.oid.dstr(t, SNil{}))) == want : List<&2, String>}
      %Equal.sym(List<&2, String>, T.oid.split(T.oid.dstr(t, SNil{})), [T.oid.dstr(t, SNil{})], ot.split_end(t, ht)) : {T.oid.put_first(c, _) == want : List<&2, String>}
      {==}

# each arc's text
def ot.strs(arcs: List<&2, Nat>) -> List<&2, String>:
  match arcs:
    case Nil{}:
      Nil{}
    case Con{+a, t}:
      Con{T.oid.dstr(O.oid.digits(a), SNil{}), ot.strs(t)}

def ot.split_text(t: List<&2, Nat>, +a: Nat) -> {T.oid.split(T.oid.text(Con{a, t})) == ot.strs(Con{a, t}) : List<&2, String>}:
  match t:
    case Nil{}:
      ot.split_end(O.oid.digits(a), ot.digits_lt_top(a))
    case Con{+b, +u}:
      +ds = O.oid.digits(a)
      %Equal.sym(List<&2, String>, T.oid.split(T.oid.dstr(ds, SCon{'.', T.oid.text(Con{b, u})})), Con{T.oid.dstr(ds, SNil{}), T.oid.split(T.oid.text(Con{b, u}))}, ot.split_dot(ds, T.oid.text(Con{b, u}), ot.digits_lt_top(a))) : {_ == ot.strs(Con{a, Con{b, u}}) : List<&2, String>}
      %Equal.sym(List<&2, String>, T.oid.split(T.oid.text(Con{b, u})), ot.strs(Con{b, u}), ot.split_text(u, b)) : {Con{T.oid.dstr(ds, SNil{}), _} == ot.strs(Con{a, Con{b, u}}) : List<&2, String>}
      {==}

# Reading an arc's text

def ot.len_str(ds: List<&2, Nat>) -> {String.length(T.oid.dstr(ds, SNil{})) == List.length(&2, Nat, ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, +t}:
      %ot.len_str(t) : {1n+String.length(T.oid.dstr(t, SNil{})) == 1n+_ : Nat}
      {==}

def ot.fold_str(ds: List<&2, Nat>, +acc: Nat, +h: {ot.all_lt(ds, 10n) == True{} : Bool}) -> {T.oid.fold(T.oid.dstr(ds, SNil{}), Some{acc}) == Some{ot.horner(ds, acc)} : Maybe<&2, Nat>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      +hd = ON.on.and_l(Nat.is_lt(d, 10n), ot.all_lt(t, 10n), h)
      +ht = ON.on.and_r(Nat.is_lt(d, 10n), ot.all_lt(t, 10n), h)
      %Equal.sym(Maybe<&2, Nat>, T.oid.cval(T.oid.dchar(d)), Some{d}, OG.og.cval(d, hd)) : {T.oid.fold(T.oid.dstr(t, SNil{}), T.oid.fold.step(_, Some{acc})) == Some{ot.horner(t, Nat.add(Nat.mul(acc, 10n), d))} : Maybe<&2, Nat>}
      ot.fold_str(t, Nat.add(Nat.mul(acc, 10n), d), ht)

def ot.lead_ds(ds: List<&2, Nat>, +hh: {Nat.is_le(1n, ot.head(ds)) == True{} : Bool}, +h: {ot.all_lt(ds, 10n) == True{} : Bool}) -> {T.oid.lead_ok(T.oid.dstr(ds, SNil{})) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, t}:
      match t:
        case Nil{}:
          {==}
        case Con{+e, +u}:
          +hd = ON.on.and_l(Nat.is_lt(d, 10n), ot.all_lt(Con{e, u}, 10n), h)
          %Equal.sym(Bool, T.oid.is_zero(T.oid.dchar(d)), False{}, OG.og.nonzero(d, hh, hd)) : {Bool.not(_) == True{} : Bool}
          {==}

def ot.lead(+a: Nat) -> {T.oid.lead_ok(T.oid.dstr(O.oid.digits(a), SNil{})) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+ +m:
      ot.lead_ds(O.oid.digits(1n+m), ot.head_pos(1n+m, Nat.is_lt(1n+m, 10n), 1n+m, {==}, ON.on.le_zero(m)), ot.digits_lt_top(1n+m))

def ot.or_t(lz: Bool) -> {Bool.or(lz, True{}) == True{} : Bool}:
  match lz:
    case True{}:
      {==}
    case False{}:
      {==}

def ot.ne_len(ds: List<&2, Nat>, +h: {ot.ne(ds) == True{} : Bool}) -> {Nat.is_le(1n, List.length(&2, Nat, ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, ON.on.ft(h))
    case Con{d, t}:
      ON.on.le_zero(List.length(&2, Nat, t))

def ot.arc_ok(+lz: Bool, +a: Nat, +hlen: {Nat.is_le(List.length(&2, Nat, O.oid.digits(a)), O.oid.max_digits()) == True{} : Bool}) -> {T.oid.arc(lz, T.oid.dstr(O.oid.digits(a), SNil{})) == Some{a} : Maybe<&2, Nat>}:
  +ds = O.oid.digits(a)
  +s = T.oid.dstr(ds, SNil{})
  %Equal.sym(Nat, String.length(s), List.length(&2, Nat, ds), ot.len_str(ds)) : {T.oid.arc.pick(Bool.and(Nat.is_le(1n, _), Bool.and(Nat.is_le(_, O.oid.max_digits()), Bool.or(lz, T.oid.lead_ok(s)))), s) == Some{a} : Maybe<&2, Nat>}
  +hne = ot.ne_len(ds, ot.digits_ne(a, Nat.is_lt(a, 10n), a))
  %Equal.sym(Bool, Nat.is_le(1n, List.length(&2, Nat, ds)), True{}, hne) : {T.oid.arc.pick(Bool.and(_, Bool.and(Nat.is_le(List.length(&2, Nat, ds), O.oid.max_digits()), Bool.or(lz, T.oid.lead_ok(s)))), s) == Some{a} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Nat.is_le(List.length(&2, Nat, ds), O.oid.max_digits()), True{}, hlen) : {T.oid.arc.pick(Bool.and(_, Bool.or(lz, T.oid.lead_ok(s))), s) == Some{a} : Maybe<&2, Nat>}
  %Equal.sym(Bool, T.oid.lead_ok(s), True{}, ot.lead(a)) : {T.oid.arc.pick(Bool.or(lz, _), s) == Some{a} : Maybe<&2, Nat>}
  %Equal.sym(Bool, Bool.or(lz, True{}), True{}, ot.or_t(lz)) : {T.oid.arc.pick(_, s) == Some{a} : Maybe<&2, Nat>}
  %Equal.sym(Maybe<&2, Nat>, T.oid.fold(s, Some{0n}), Some{ot.horner(ds, 0n)}, ot.fold_str(ds, 0n, ot.digits_lt_top(a))) : {_ == Some{a} : Maybe<&2, Nat>}
  %Equal.sym(Nat, ot.horner(ds, 0n), a, ot.horner_digits(a, Nat.is_lt(a, 10n), a)) : {Some{_} == Some{a} : Maybe<&2, Nat>}
  {==}

def ot.parse(arcs: List<&2, Nat>, +lz: Bool, +h: {O.oid.text_ok(arcs) == True{} : Bool}) -> {T.oid.arcs(ot.strs(arcs), lz) == Some{arcs} : Maybe<&2, List<&2, Nat>>}:
  match arcs:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      +ok1 = Nat.is_le(List.length(&2, Nat, O.oid.digits(a)), O.oid.max_digits())
      +h1 = ON.on.and_l(ok1, O.oid.text_ok(t), h)
      +h2 = ON.on.and_r(ok1, O.oid.text_ok(t), h)
      %Equal.sym(Maybe<&2, Nat>, T.oid.arc(lz, T.oid.dstr(O.oid.digits(a), SNil{})), Some{a}, ot.arc_ok(lz, a, h1)) : {T.oid.arcs.cons(_, T.oid.arcs(ot.strs(t), lz)) == Some{Con{a, t}} : Maybe<&2, List<&2, Nat>>}
      %Equal.sym(Maybe<&2, List<&2, Nat>>, T.oid.arcs(ot.strs(t), lz), Some{t}, ot.parse(t, lz, h2)) : {T.oid.arcs.cons(Some{a}, _) == Some{Con{a, t}} : Maybe<&2, List<&2, Nat>>}
      {==}

# a valid Oid's text reads back as it
def ot.text_rt(r: T.OidTextRules, arcs: List<&2, Nat>, +hv: {O.Oid.valid_arcs(arcs) == True{} : Bool}) -> {T.Oid.of_text(r, T.Oid.to_text(O.Oid{arcs})) == Done{O.Oid{arcs}} : Result<&2, &2, O.OidError, O.Oid>}:
  match r:
    case T.OidTextRules{+lz}:
      match arcs:
        case Nil{}:
          Empty.absurd({T.Oid.of_text(T.OidTextRules{lz}, T.Oid.to_text(O.Oid{Nil{}})) == Done{O.Oid{Nil{}}} : Result<&2, &2, O.OidError, O.Oid>}, ON.on.ft(hv))
        case Con{+a, +t}:
          +x : List<&2, Nat> = Con{a, t}
          +htok = ON.on.and_l(O.oid.text_ok(x), O.oid.done(O.oid.der(x)), hv)
          %Equal.sym(List<&2, String>, T.oid.split(T.oid.text(x)), ot.strs(x), ot.split_text(t, a)) : {T.oid.of_text.go(T.oid.arcs(_, lz)) == Done{O.Oid{x}} : Result<&2, &2, O.OidError, O.Oid>}
          %Equal.sym(Maybe<&2, List<&2, Nat>>, T.oid.arcs(ot.strs(x), lz), Some{x}, ot.parse(x, lz, htok)) : {T.oid.of_text.go(_) == Done{O.Oid{x}} : Result<&2, &2, O.OidError, O.Oid>}
          %Equal.sym(Bool, O.Oid.valid_arcs(x), True{}, hv) : {O.oid.mk(_, x) == Done{O.Oid{x}} : Result<&2, &2, O.OidError, O.Oid>}
          {==}
