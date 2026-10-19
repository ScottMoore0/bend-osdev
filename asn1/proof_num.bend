# Proof helpers for bend-osdev-asn1: numbers in octets. The digits of n in
# any base read back as n by Horner's rule, and are below the base; base-128
# octets read back (a1.r128), big-endian octets read back (a1.fold256); and
# so the length octets (length.bend) and identifier octets (tag.bend) the
# encoder writes read back as what was written.
import Base
import ../bytes/bytes.bend as B
import ./number.bend as Nu
import ./tag.bend as T
import ./length.bend as L
import ./rules.bend as R
import ./proof_nat.bend as AN
import ./proof_list.bend as AL
import ./proof_u32.bend as AU
import ./proof_byte.bend as AB

# every element of ds is below b
def pn.all_lt(ds: List<&2, Nat>, +b: Nat) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, t}:
      Bool.and(Nat.is_lt(d, b), pn.all_lt(t, b))

def pn.all_lt_app(xs: List<&2, Nat>, +ys: List<&2, Nat>, +b: Nat, +hx: {pn.all_lt(xs, b) == True{} : Bool}, +hy: {pn.all_lt(ys, b) == True{} : Bool}) -> {pn.all_lt(List.append(&2, Nat, xs, ys), b) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{+d, +t}:
      AN.an.and_i(Nat.is_lt(d, b), pn.all_lt(List.append(&2, Nat, t, ys), b), AN.an.and_l(Nat.is_lt(d, b), pn.all_lt(t, b), hx), pn.all_lt_app(t, ys, b, AN.an.and_r(Nat.is_lt(d, b), pn.all_lt(t, b), hx), hy))

def pn.ne(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, t}:
      True{}

def pn.ne_app(xs: List<&2, Nat>, +d: Nat) -> {pn.ne(List.append(&2, Nat, xs, [d])) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

# Horner's rule

def pn.horner_snoc(xs: List<&2, Nat>, +b: Nat, +acc: Nat, +d: Nat) -> {Nu.a1.horner(List.append(&2, Nat, xs, [d]), b, acc) == Nat.add(Nat.mul(Nu.a1.horner(xs, b, acc), b), d) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      pn.horner_snoc(t, b, Nat.add(Nat.mul(acc, b), x), d)

# the digits of n read back as n (b = 1 + bp; lt is whether n < b)
def pn.horner_digits(fuel: Nat, lt: Bool, +bp: Nat, +n: Nat) -> {Nu.a1.horner(Nu.a1.digits.go(fuel, lt, 1n+bp, n), 1n+bp, 0n) == n : Nat}:
  match fuel lt:
    case _ True{}:
      {==}
    case 0n False{}:
      {==}
    case 1n+ +f False{}:
      +q = Nat.div(n, 1n+bp)
      +ds = Nu.a1.digits.go(f, Nat.is_lt(q, 1n+bp), 1n+bp, q)
      %Equal.sym(Nat, Nu.a1.horner(List.append(&2, Nat, ds, [Nat.mod(n, 1n+bp)]), 1n+bp, 0n), Nat.add(Nat.mul(Nu.a1.horner(ds, 1n+bp, 0n), 1n+bp), Nat.mod(n, 1n+bp)), pn.horner_snoc(ds, 1n+bp, 0n, Nat.mod(n, 1n+bp))) : {_ == n : Nat}
      %Equal.sym(Nat, Nu.a1.horner(ds, 1n+bp, 0n), q, pn.horner_digits(f, Nat.is_lt(q, 1n+bp), bp, q)) : {Nat.add(Nat.mul(_, 1n+bp), Nat.mod(n, 1n+bp)) == n : Nat}
      AN.an.recon(n, bp)

def pn.horner_digits_top(+bp: Nat, +n: Nat) -> {Nu.a1.horner(Nu.a1.digits(1n+bp, n), 1n+bp, 0n) == n : Nat}:
  pn.horner_digits(n, Nat.is_lt(n, 1n+bp), bp, n)

def pn.le_not_lt(+a: Nat, +b: Nat) -> {Nat.is_le(a, b) == Bool.not(Nat.is_lt(b, a)) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pn.le_not_lt(p, q)

# the digits are below the base (b = 2 + bp; fuel at least n)
def pn.digits_lt(fuel: Nat, lt: Bool, +bp: Nat, +n: Nat, +hl: {Nat.is_lt(n, 2n+bp) == lt : Bool}, +hf: {Nat.is_le(n, fuel) == True{} : Bool}) -> {pn.all_lt(Nu.a1.digits.go(fuel, lt, 2n+bp, n), 2n+bp) == True{} : Bool}:
  match fuel lt:
    case _ True{}:
      %Equal.sym(Bool, Nat.is_lt(n, 2n+bp), True{}, hl) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case 0n False{}:
      match n:
        case 0n:
          Empty.absurd({pn.all_lt([0n], 2n+bp) == True{} : Bool}, AN.an.tf(hl))
        case 1n+m:
          Empty.absurd({pn.all_lt([1n+m], 2n+bp) == True{} : Bool}, AN.an.ft(hf))
    case 1n+ +f False{}:
      +b : Nat = 2n+bp
      +q = Nat.div(n, b)
      +hb = Equal.trans(Bool, Nat.is_le(b, n), Bool.not(Nat.is_lt(n, b)), True{}, pn.le_not_lt(b, n), Equal.cong(Bool, Bool, z => Bool.not(z), Nat.is_lt(n, b), False{}, hl))
      +hq = AN.an.lt_succ_le(q, f, AN.an.lt_le_trans(q, n, 1n+f, AN.an.div_lt(n, bp, hb), hf))
      +ih = pn.digits_lt(f, Nat.is_lt(q, b), bp, q, {==}, hq)
      pn.all_lt_app(Nu.a1.digits.go(f, Nat.is_lt(q, b), b, q), [Nat.mod(n, b)], b, ih, AN.an.and_i(Nat.is_lt(Nat.mod(n, b), b), True{}, AN.an.mod_lt(n, 1n+bp), {==}))


def pn.digits_lt_top(+bp: Nat, +n: Nat) -> {pn.all_lt(Nu.a1.digits(2n+bp, n), 2n+bp) == True{} : Bool}:
  pn.digits_lt(n, Nat.is_lt(n, 2n+bp), bp, n, {==}, AN.an.le_refl(n))

def pn.digits_ne(fuel: Nat, lt: Bool, +b: Nat, +n: Nat) -> {pn.ne(Nu.a1.digits.go(fuel, lt, b, n)) == True{} : Bool}:
  match fuel lt:
    case _ True{}:
      {==}
    case 0n False{}:
      {==}
    case 1n+ +f False{}:
      +q = Nat.div(n, b)
      pn.ne_app(Nu.a1.digits.go(f, Nat.is_lt(q, b), b, q), Nat.mod(n, b))

def pn.digits_ne_top(+b: Nat, +n: Nat) -> {pn.ne(Nu.a1.digits(b, n)) == True{} : Bool}:
  pn.digits_ne(n, Nat.is_lt(n, b), b, n)

# Base-128 octets

def pn.lt128_256(+d: Nat, +h: {Nat.is_lt(d, 128n) == True{} : Bool}) -> {Nat.is_lt(d, 256n) == True{} : Bool}:
  AN.an.lt_le_trans(d, 128n, 256n, h, {==})

def pn.lt_add128(+d: Nat, +h: {Nat.is_lt(d, 128n) == True{} : Bool}) -> {Nat.is_lt(Nat.add(128n, d), 256n) == True{} : Bool}:
  h

# reading one base-128 octet whose value is v
def pn.r128_step(+x: U32, +t: List<&2, U32>, +j: Nat, +acc: Nat, +v: Nat, +hv: {U32.to_nat(x) == v : Nat}) -> {Nu.a1.r128(Con{x, t}, True{}, 1n+j, acc) == Nu.a1.num_cons(x, Nu.a1.r128(t, Nat.is_le(128n, v), j, Nat.add(Nat.mul(acc, 128n), Nat.sub(v, Bool.pick(Nat, Nat.is_le(128n, v), 128n, 0n))))) : Maybe<&2, Nu.A1Num>}:
  %hv : {Nu.a1.r128(Con{x, t}, True{}, 1n+j, acc) == Nu.a1.num_cons(x, Nu.a1.r128(t, Nat.is_le(128n, _), j, Nat.add(Nat.mul(acc, 128n), Nat.sub(_, Bool.pick(Nat, Nat.is_le(128n, _), 128n, 0n))))) : Maybe<&2, Nu.A1Num>}
  {==}

def pn.r128_end(xs: List<&2, U32>, +k: Nat, +acc: Nat) -> {Nu.a1.r128(xs, False{}, k, acc) == Some{Nu.A1Num{acc, Nil{}, xs}} : Maybe<&2, Nu.A1Num>}:
  match xs:
    case Nil{}:
      {==}
    case Con{y, z}:
      {==}

def pn.step_sym(+x: U32, +t: List<&2, U32>, +j: Nat, +acc: Nat, +v: Nat, +hv: {U32.to_nat(x) == v : Nat}) -> {Nu.a1.num_cons(x, Nu.a1.r128(t, Nat.is_le(128n, v), j, Nat.add(Nat.mul(acc, 128n), Nat.sub(v, Bool.pick(Nat, Nat.is_le(128n, v), 128n, 0n))))) == Nu.a1.r128(Con{x, t}, True{}, 1n+j, acc) : Maybe<&2, Nu.A1Num>}:
  Equal.sym(Maybe<&2, Nu.A1Num>, Nu.a1.r128(Con{x, t}, True{}, 1n+j, acc), Nu.a1.num_cons(x, Nu.a1.r128(t, Nat.is_le(128n, v), j, Nat.add(Nat.mul(acc, 128n), Nat.sub(v, Bool.pick(Nat, Nat.is_le(128n, v), 128n, 0n))))), pn.r128_step(x, t, j, acc, v, hv))

# the last octet of a base-128 number (d < 128): bit 8 clear, so it ends
def pn.r128_last(+d: Nat, +rest: List<&2, U32>, +j: Nat, +acc: Nat, +hd: {Nat.is_lt(d, 128n) == True{} : Bool}) -> {Nu.a1.r128(Con{Nu.a1.b(d), rest}, True{}, 1n+j, acc) == Some{Nu.A1Num{Nat.add(Nat.mul(acc, 128n), d), [Nu.a1.b(d)], rest}} : Maybe<&2, Nu.A1Num>}:
  +hv = AB.ab.byte(d, pn.lt128_256(d, hd))
  +hle = AN.an.lt_nle(d, 128n, hd)
  +want : Maybe<&2, Nu.A1Num> = Some{Nu.A1Num{Nat.add(Nat.mul(acc, 128n), d), [Nu.a1.b(d)], rest}}
  %pn.step_sym(Nu.a1.b(d), rest, j, acc, d, hv) : {_ == want : Maybe<&2, Nu.A1Num>}
  %Equal.sym(Bool, Nat.is_le(128n, d), False{}, hle) : {Nu.a1.num_cons(Nu.a1.b(d), Nu.a1.r128(rest, _, j, Nat.add(Nat.mul(acc, 128n), Nat.sub(d, Bool.pick(Nat, _, 128n, 0n))))) == want : Maybe<&2, Nu.A1Num>}
  %Equal.sym(Nat, Nat.sub(d, 0n), d, AN.an.sub_zero(d)) : {Nu.a1.num_cons(Nu.a1.b(d), Nu.a1.r128(rest, False{}, j, Nat.add(Nat.mul(acc, 128n), _))) == want : Maybe<&2, Nu.A1Num>}
  %Equal.sym(Maybe<&2, Nu.A1Num>, Nu.a1.r128(rest, False{}, j, Nat.add(Nat.mul(acc, 128n), d)), Some{Nu.A1Num{Nat.add(Nat.mul(acc, 128n), d), Nil{}, rest}}, pn.r128_end(rest, j, Nat.add(Nat.mul(acc, 128n), d))) : {Nu.a1.num_cons(Nu.a1.b(d), _) == want : Maybe<&2, Nu.A1Num>}
  {==}

# an octet before the last (bit 8 set): it goes on
def pn.r128_more(+d: Nat, +t: List<&2, U32>, +j: Nat, +acc: Nat, +hd: {Nat.is_lt(d, 128n) == True{} : Bool}) -> {Nu.a1.r128(Con{Nu.a1.b(Nat.add(128n, d)), t}, True{}, 1n+j, acc) == Nu.a1.num_cons(Nu.a1.b(Nat.add(128n, d)), Nu.a1.r128(t, True{}, j, Nat.add(Nat.mul(acc, 128n), d))) : Maybe<&2, Nu.A1Num>}:
  +x = Nu.a1.b(Nat.add(128n, d))
  +hv = AB.ab.byte(Nat.add(128n, d), pn.lt_add128(d, hd))
  +want : Maybe<&2, Nu.A1Num> = Nu.a1.num_cons(x, Nu.a1.r128(t, True{}, j, Nat.add(Nat.mul(acc, 128n), d)))
  %pn.step_sym(x, t, j, acc, Nat.add(128n, d), hv) : {_ == want : Maybe<&2, Nu.A1Num>}
  %Equal.sym(Bool, Nat.is_le(128n, Nat.add(128n, d)), True{}, AN.an.le_add(128n, d)) : {Nu.a1.num_cons(x, Nu.a1.r128(t, _, j, Nat.add(Nat.mul(acc, 128n), Nat.sub(Nat.add(128n, d), Bool.pick(Nat, _, 128n, 0n))))) == want : Maybe<&2, Nu.A1Num>}
  %Equal.sym(Nat, Nat.sub(Nat.add(128n, d), 128n), d, AN.an.sub_add_l(128n, d)) : {Nu.a1.num_cons(x, Nu.a1.r128(t, True{}, j, Nat.add(Nat.mul(acc, 128n), _))) == want : Maybe<&2, Nu.A1Num>}
  {==}

# base-128 octets of digits below 128 read back as their value, within a
# budget of k octets
def pn.r128_enc(ds: List<&2, Nat>, +rest: List<&2, U32>, k: Nat, +acc: Nat, +hne: {pn.ne(ds) == True{} : Bool}, +hall: {pn.all_lt(ds, 128n) == True{} : Bool}, +hk: {Nat.is_le(List.length(&2, Nat, ds), k) == True{} : Bool}) -> {Nu.a1.r128(List.append(&2, U32, Nu.a1.enc128(ds), rest), True{}, k, acc) == Some{Nu.A1Num{Nu.a1.horner(ds, 128n, acc), Nu.a1.enc128(ds), rest}} : Maybe<&2, Nu.A1Num>}:
  match ds:
    case Nil{}:
      Empty.absurd({Nu.a1.r128(List.append(&2, U32, Nu.a1.enc128(Nil{}), rest), True{}, k, acc) == Some{Nu.A1Num{Nu.a1.horner(Nil{}, 128n, acc), Nu.a1.enc128(Nil{}), rest}} : Maybe<&2, Nu.A1Num>}, AN.an.ft(hne))
    case Con{+d, +t}:
      match t k:
        case _ 0n:
          Empty.absurd({Nu.a1.r128(List.append(&2, U32, Nu.a1.enc128(Con{d, t}), rest), True{}, 0n, acc) == Some{Nu.A1Num{Nu.a1.horner(Con{d, t}, 128n, acc), Nu.a1.enc128(Con{d, t}), rest}} : Maybe<&2, Nu.A1Num>}, AN.an.ft(hk))
        case Nil{} 1n+ +j:
          pn.r128_last(d, rest, j, acc, AN.an.and_l(Nat.is_lt(d, 128n), True{}, hall))
        case Con{+e, +u} 1n+ +j:
          +hd = AN.an.and_l(Nat.is_lt(d, 128n), pn.all_lt(Con{e, u}, 128n), hall)
          +ht = AN.an.and_r(Nat.is_lt(d, 128n), pn.all_lt(Con{e, u}, 128n), hall)
          +x = Nu.a1.b(Nat.add(128n, d))
          +tl = List.append(&2, U32, Nu.a1.enc128(Con{e, u}), rest)
          +acc2 = Nat.add(Nat.mul(acc, 128n), d)
          +want : Maybe<&2, Nu.A1Num> = Some{Nu.A1Num{Nu.a1.horner(Con{e, u}, 128n, acc2), Con{x, Nu.a1.enc128(Con{e, u})}, rest}}
          %Equal.sym(Maybe<&2, Nu.A1Num>, Nu.a1.r128(Con{x, tl}, True{}, 1n+j, acc), Nu.a1.num_cons(x, Nu.a1.r128(tl, True{}, j, acc2)), pn.r128_more(d, tl, j, acc, hd)) : {_ == want : Maybe<&2, Nu.A1Num>}
          %Equal.sym(Maybe<&2, Nu.A1Num>, Nu.a1.r128(tl, True{}, j, acc2), Some{Nu.A1Num{Nu.a1.horner(Con{e, u}, 128n, acc2), Nu.a1.enc128(Con{e, u}), rest}}, pn.r128_enc(Con{e, u}, rest, j, acc2, {==}, ht, hk)) : {Nu.a1.num_cons(x, _) == want : Maybe<&2, Nu.A1Num>}
          {==}

def pn.len_enc128(ds: List<&2, Nat>) -> {List.length(&2, U32, Nu.a1.enc128(ds)) == List.length(&2, Nat, ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      match t:
        case Nil{}:
          {==}
        case Con{+e, +u}:
          %pn.len_enc128(Con{e, u}) : {1n+List.length(&2, U32, Nu.a1.enc128(Con{e, u})) == 1n+_ : Nat}
          {==}

# a number's base-128 octets (at most k of them) read back as it
def pn.r128_b128(+n: Nat, +rest: List<&2, U32>, +k: Nat, +hk: {Nat.is_le(List.length(&2, U32, Nu.a1.b128(n)), k) == True{} : Bool}) -> {Nu.a1.r128(List.append(&2, U32, Nu.a1.b128(n), rest), True{}, k, 0n) == Some{Nu.A1Num{n, Nu.a1.b128(n), rest}} : Maybe<&2, Nu.A1Num>}:
  +ds = Nu.a1.digits(128n, n)
  +hk2 = Equal.trans(Bool, Nat.is_le(List.length(&2, Nat, ds), k), Nat.is_le(List.length(&2, U32, Nu.a1.enc128(ds)), k), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, k), List.length(&2, Nat, ds), List.length(&2, U32, Nu.a1.enc128(ds)), Equal.sym(Nat, List.length(&2, U32, Nu.a1.enc128(ds)), List.length(&2, Nat, ds), pn.len_enc128(ds))), hk)
  %Equal.sym(Maybe<&2, Nu.A1Num>, Nu.a1.r128(List.append(&2, U32, Nu.a1.enc128(ds), rest), True{}, k, 0n), Some{Nu.A1Num{Nu.a1.horner(ds, 128n, 0n), Nu.a1.enc128(ds), rest}}, pn.r128_enc(ds, rest, k, 0n, pn.digits_ne_top(128n, n), pn.digits_lt_top(126n, n), hk2)) : {_ == Some{Nu.A1Num{n, Nu.a1.b128(n), rest}} : Maybe<&2, Nu.A1Num>}
  %Equal.sym(Nat, Nu.a1.horner(ds, 128n, 0n), n, pn.horner_digits_top(127n, n)) : {Some{Nu.A1Num{_, Nu.a1.enc128(ds), rest}} == Some{Nu.A1Num{n, Nu.a1.b128(n), rest}} : Maybe<&2, Nu.A1Num>}
  {==}

# Big-endian octets

def pn.fold_bytes(ds: List<&2, Nat>, +acc: Nat, +hall: {pn.all_lt(ds, 256n) == True{} : Bool}) -> {Nu.a1.fold256(Nu.a1.bytes_of(ds), acc) == Nu.a1.horner(ds, 256n, acc) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      +hd = AN.an.and_l(Nat.is_lt(d, 256n), pn.all_lt(t, 256n), hall)
      +ht = AN.an.and_r(Nat.is_lt(d, 256n), pn.all_lt(t, 256n), hall)
      %Equal.sym(Nat, U32.to_nat(Nu.a1.b(d)), d, AB.ab.byte(d, hd)) : {Nu.a1.fold256(Nu.a1.bytes_of(t), Nat.add(Nat.mul(acc, 256n), _)) == Nu.a1.horner(t, 256n, Nat.add(Nat.mul(acc, 256n), d)) : Nat}
      pn.fold_bytes(t, Nat.add(Nat.mul(acc, 256n), d), ht)

def pn.len_bytes_of(ds: List<&2, Nat>) -> {List.length(&2, U32, Nu.a1.bytes_of(ds)) == List.length(&2, Nat, ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, +t}:
      %pn.len_bytes_of(t) : {1n+List.length(&2, U32, Nu.a1.bytes_of(t)) == 1n+_ : Nat}
      {==}

def pn.ne_len(ds: List<&2, Nat>, +h: {pn.ne(ds) == True{} : Bool}) -> {Nat.is_le(1n, List.length(&2, Nat, ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, AN.an.ft(h))
    case Con{d, t}:
      AN.an.le_zero(List.length(&2, Nat, t))

# the octets of be(n) read back as n (fold256)
def pn.fold_be(+n: Nat) -> {Nu.a1.fold256(Nu.a1.be(n), 0n) == n : Nat}:
  +ds = Nu.a1.digits(256n, n)
  Equal.trans(Nat, Nu.a1.fold256(Nu.a1.bytes_of(ds), 0n), Nu.a1.horner(ds, 256n, 0n), n, pn.fold_bytes(ds, 0n, pn.digits_lt_top(254n, n)), pn.horner_digits_top(255n, n))

def pn.be_len(+n: Nat) -> {Nat.is_le(1n, List.length(&2, U32, Nu.a1.be(n))) == True{} : Bool}:
  +ds = Nu.a1.digits(256n, n)
  %Equal.sym(Nat, List.length(&2, U32, Nu.a1.bytes_of(ds)), List.length(&2, Nat, ds), pn.len_bytes_of(ds)) : {Nat.is_le(1n, _) == True{} : Bool}
  pn.ne_len(ds, pn.digits_ne_top(256n, n))

# Length octets

def pn.lb_short(+n: Nat, +h: {Nat.is_lt(n, 128n) == True{} : Bool}) -> {L.a1.len_bytes(n) == [Nu.a1.b(n)] : List<&2, U32>}:
  %Equal.sym(Bool, Nat.is_lt(n, 128n), True{}, h) : {L.a1.len_pick(_, n) == [Nu.a1.b(n)] : List<&2, U32>}
  {==}

def pn.lr_short(+n: Nat, +rest: List<&2, U32>, +h: {Nat.is_lt(n, 128n) == True{} : Bool}) -> {L.a1.len.read(Con{Nu.a1.b(n), rest}) == L.A1LDef{n, [Nu.a1.b(n)], rest} : L.A1Len}:
  %Equal.sym(Nat, U32.to_nat(Nu.a1.b(n)), n, AB.ab.byte(n, pn.lt128_256(n, h))) : {L.a1.len.first(Nat.is_lt(_, 128n), _, Nu.a1.b(n), rest) == L.A1LDef{n, [Nu.a1.b(n)], rest} : L.A1Len}
  %Equal.sym(Bool, Nat.is_lt(n, 128n), True{}, h) : {L.a1.len.first(_, n, Nu.a1.b(n), rest) == L.A1LDef{n, [Nu.a1.b(n)], rest} : L.A1Len}
  {==}

def pn.lb_long(+n: Nat, +h: {Nat.is_lt(n, 128n) == False{} : Bool}) -> {L.a1.len_bytes(n) == Con{Nu.a1.b(Nat.add(128n, List.length(&2, U32, Nu.a1.be(n)))), Nu.a1.be(n)} : List<&2, U32>}:
  %Equal.sym(Bool, Nat.is_lt(n, 128n), False{}, h) : {L.a1.len_pick(_, n) == Con{Nu.a1.b(Nat.add(128n, List.length(&2, U32, Nu.a1.be(n)))), Nu.a1.be(n)} : List<&2, U32>}
  {==}

def pn.okm(+n: Nat, +h: {Nat.is_lt(n, 128n) == False{} : Bool}, +hok: {L.a1.len_ok(n) == True{} : Bool}) -> {Nat.is_le(List.length(&2, U32, Nu.a1.be(n)), 6n) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(List.length(&2, U32, Nu.a1.be(n)), 6n), L.a1.len_ok(n), True{}, Equal.cong(Bool, Bool, z => L.a1.len_ok.pick(z, n), False{}, Nat.is_lt(n, 128n), Equal.sym(Bool, Nat.is_lt(n, 128n), False{}, h)), hok)

# a <= b: not b < a
def pn.le_nlt(+a: Nat, +b: Nat, +h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n _:
      AN.an.lt0(b)
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(0n, 1n+p) == False{} : Bool}, AN.an.ft(h))
    case 1n+p 1n+q:
      pn.le_nlt(p, q, h)

def pn.long_pos(+k: Nat, +y: U32, +t: List<&2, U32>, +hk: {Nat.is_le(1n, k) == True{} : Bool}) -> {L.a1.len.long(k, y, t) == L.a1.len.reserved(Nat.is_eq(k, 127n), k, y, t) : L.A1Len}:
  match k:
    case 0n:
      Empty.absurd({L.a1.len.long(0n, y, t) == L.a1.len.reserved(Nat.is_eq(0n, 127n), 0n, y, t) : L.A1Len}, AN.an.ft(hk))
    case 1n+j:
      {==}

def pn.rbe_app(+ds: List<&2, U32>, +rest: List<&2, U32>) -> {Nu.a1.rbe(List.length(&2, U32, ds), List.append(&2, U32, ds, rest)) == Some{Nu.A1Num{Nu.a1.fold256(ds, 0n), ds, rest}} : Maybe<&2, Nu.A1Num>}:
  +m = List.length(&2, U32, ds)
  +xs = List.append(&2, U32, ds, rest)
  +hle = Equal.trans(Bool, Nat.is_le(m, List.length(&2, U32, xs)), Nat.is_le(m, Nat.add(m, List.length(&2, U32, rest))), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(m, z), List.length(&2, U32, xs), Nat.add(m, List.length(&2, U32, rest)), AL.al.app_len(ds, rest)), AN.an.le_add(m, List.length(&2, U32, rest)))
  %Equal.sym(Bool, Nat.is_le(m, List.length(&2, U32, xs)), True{}, hle) : {Nu.a1.rbe.pick(_, m, xs) == Some{Nu.A1Num{Nu.a1.fold256(ds, 0n), ds, rest}} : Maybe<&2, Nu.A1Num>}
  %Equal.sym(List<&2, U32>, B.take(m, xs), ds, AL.al.take_app(ds, rest)) : {Some{Nu.A1Num{Nu.a1.fold256(_, 0n), _, B.drop(m, xs)}} == Some{Nu.A1Num{Nu.a1.fold256(ds, 0n), ds, rest}} : Maybe<&2, Nu.A1Num>}
  %Equal.sym(List<&2, U32>, B.drop(m, xs), rest, AL.al.drop_app(ds, rest)) : {Some{Nu.A1Num{Nu.a1.fold256(ds, 0n), ds, _}} == Some{Nu.A1Num{Nu.a1.fold256(ds, 0n), ds, rest}} : Maybe<&2, Nu.A1Num>}
  {==}

def pn.lr_long(+n: Nat, +rest: List<&2, U32>, +h: {Nat.is_lt(n, 128n) == False{} : Bool}, +hok: {L.a1.len_ok(n) == True{} : Bool}) -> {L.a1.len.read(Con{Nu.a1.b(Nat.add(128n, List.length(&2, U32, Nu.a1.be(n)))), List.append(&2, U32, Nu.a1.be(n), rest)}) == L.A1LDef{n, Con{Nu.a1.b(Nat.add(128n, List.length(&2, U32, Nu.a1.be(n)))), Nu.a1.be(n)}, rest} : L.A1Len}:
  +ds = Nu.a1.be(n)
  +m = List.length(&2, U32, ds)
  +y = Nu.a1.b(Nat.add(128n, m))
  +t = List.append(&2, U32, ds, rest)
  +want : L.A1Len = L.A1LDef{n, Con{y, ds}, rest}
  +hm = pn.okm(n, h, hok)
  +hm7 = AN.an.le_lt_succ(m, 6n, hm)
  +hm127 = AN.an.lt_le_trans(m, 7n, 127n, hm7, {==})
  +hm128 = AN.an.lt_le_trans(m, 7n, 128n, hm7, {==})
  %Equal.sym(Nat, U32.to_nat(y), Nat.add(128n, m), AB.ab.byte(Nat.add(128n, m), pn.lt_add128(m, hm128))) : {L.a1.len.first(Nat.is_lt(_, 128n), _, y, t) == want : L.A1Len}
  %Equal.sym(Bool, Nat.is_lt(m, 0n), False{}, AN.an.lt0(m)) : {L.a1.len.first(_, Nat.add(128n, m), y, t) == want : L.A1Len}
  %Equal.sym(Nat, Nat.sub(Nat.add(128n, m), 128n), m, AN.an.sub_add_l(128n, m)) : {L.a1.len.long(_, y, t) == want : L.A1Len}
  %Equal.sym(L.A1Len, L.a1.len.long(m, y, t), L.a1.len.reserved(Nat.is_eq(m, 127n), m, y, t), pn.long_pos(m, y, t, pn.be_len(n))) : {_ == want : L.A1Len}
  %Equal.sym(Bool, Nat.is_eq(m, 127n), False{}, AN.an.lt_ne(m, 127n, hm127)) : {L.a1.len.reserved(_, m, y, t) == want : L.A1Len}
  %Equal.sym(Bool, Nat.is_lt(6n, m), False{}, pn.le_nlt(m, 6n, hm)) : {L.a1.len.many(_, m, y, t) == want : L.A1Len}
  %Equal.sym(Maybe<&2, Nu.A1Num>, Nu.a1.rbe(m, t), Some{Nu.A1Num{Nu.a1.fold256(ds, 0n), ds, rest}}, pn.rbe_app(ds, rest)) : {L.a1.len.bytes(y, _) == want : L.A1Len}
  %Equal.sym(Nat, Nu.a1.fold256(ds, 0n), n, pn.fold_be(n)) : {L.a1.len.bytes(y, Some{Nu.A1Num{_, ds, rest}}) == want : L.A1Len}
  {==}

def pn.len_read.go(lt: Bool, +n: Nat, +rest: List<&2, U32>, +hl: {Nat.is_lt(n, 128n) == lt : Bool}, +hok: {L.a1.len_ok(n) == True{} : Bool}) -> {L.a1.len.read(List.append(&2, U32, L.a1.len_bytes(n), rest)) == L.A1LDef{n, L.a1.len_bytes(n), rest} : L.A1Len}:
  match lt:
    case True{}:
      %Equal.sym(List<&2, U32>, L.a1.len_bytes(n), [Nu.a1.b(n)], pn.lb_short(n, hl)) : {L.a1.len.read(List.append(&2, U32, _, rest)) == L.A1LDef{n, _, rest} : L.A1Len}
      pn.lr_short(n, rest, hl)
    case False{}:
      +l1 : List<&2, U32> = Con{Nu.a1.b(Nat.add(128n, List.length(&2, U32, Nu.a1.be(n)))), Nu.a1.be(n)}
      %Equal.sym(List<&2, U32>, L.a1.len_bytes(n), l1, pn.lb_long(n, hl)) : {L.a1.len.read(List.append(&2, U32, _, rest)) == L.A1LDef{n, _, rest} : L.A1Len}
      pn.lr_long(n, rest, hl, hok)

# the length octets of n (that has them) read back as n
def pn.len_read(+n: Nat, +rest: List<&2, U32>, +hok: {L.a1.len_ok(n) == True{} : Bool}) -> {L.a1.len.read(List.append(&2, U32, L.a1.len_bytes(n), rest)) == L.A1LDef{n, L.a1.len_bytes(n), rest} : L.A1Len}:
  pn.len_read.go(Nat.is_lt(n, 128n), n, rest, {==}, hok)
