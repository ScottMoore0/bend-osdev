import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../blockdev/blockdev.bend as BD
import ./fields.bend as F
import ./joliet.bend as J
import ./dirrec.bend as R
import ./dir.bend as DR
import ./file.bend as FL
import ./fence.bend as FN
import ./LAWS.bend as Laws

# The proofs use bytes' interface laws (octets_to_of, octets_of_to,
# octets_append_list, octets_of_list_idempotent) where a byte string's
# contents are not known, and compute with every U32 split into its bits
# where the both-endian halves must be compared.

def bool_disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def bool_absurd(e: {False{} == True{} : Bool}) -> Empty:
  %e : bool_disc(_)
  Unit{}

def add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def dlen(ds: List<&2, F.IsoDigit>) -> Nat:
  List.length(&2, F.IsoDigit, ds)

def undig(d: F.IsoDigit) -> {Some{d} == F.IsoDigit.of_byte(B.byte(F.IsoDigit.byte(d))) : Maybe<&2, F.IsoDigit>}:
  match d:
    case F.IsoDig0{}:
      {==}
    case F.IsoDig1{}:
      {==}
    case F.IsoDig2{}:
      {==}
    case F.IsoDig3{}:
      {==}
    case F.IsoDig4{}:
      {==}
    case F.IsoDig5{}:
      {==}
    case F.IsoDig6{}:
      {==}
    case F.IsoDig7{}:
      {==}
    case F.IsoDig8{}:
      {==}
    case F.IsoDig9{}:
      {==}

def read_step(+d: F.IsoDigit, +rest: List<&2, U32>, +j: Nat, +acc: List<&2, F.IsoDigit>) -> {F.iso.digits.read(1n+j, B.mask(Con{F.IsoDigit.byte(d), rest}), Some{acc}) == F.iso.digits.read(j, B.mask(rest), Some{Con{d, acc}}) : Maybe<&2, F.IsoDigitsRest>}:
  %undig(d) : {F.iso.digits.read(j, B.mask(rest), F.iso.digits.push(_, Some{acc})) == F.iso.digits.read(j, B.mask(rest), Some{Con{d, acc}}) : Maybe<&2, F.IsoDigitsRest>}
  {==}

# reading the characters of ds pushes ds on the digits read so far
def read_bytes(ds: List<&2, F.IsoDigit>, +rest: List<&2, U32>, +j: Nat, +acc: List<&2, F.IsoDigit>) -> {F.iso.digits.read(Nat.add(dlen(ds), j), B.mask(F.iso.digits.bytes(ds, rest)), Some{acc}) == F.iso.digits.read(j, B.mask(rest), Some{List.append(&2, F.IsoDigit, ds, acc)}) : Maybe<&2, F.IsoDigitsRest>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      %add_succ(dlen(t), j) : {F.iso.digits.read(_, B.mask(F.iso.digits.bytes(t, Con{F.IsoDigit.byte(d), rest})), Some{acc}) == F.iso.digits.read(j, B.mask(rest), Some{Con{d, List.append(&2, F.IsoDigit, t, acc)}}) : Maybe<&2, F.IsoDigitsRest>}
      Equal.trans(Maybe<&2, F.IsoDigitsRest>, F.iso.digits.read(Nat.add(dlen(t), 1n+j), B.mask(F.iso.digits.bytes(t, Con{F.IsoDigit.byte(d), rest})), Some{acc}), F.iso.digits.read(1n+j, B.mask(Con{F.IsoDigit.byte(d), rest}), Some{List.append(&2, F.IsoDigit, t, acc)}), F.iso.digits.read(j, B.mask(rest), Some{Con{d, List.append(&2, F.IsoDigit, t, acc)}}), read_bytes(t, Con{F.IsoDigit.byte(d), rest}, 1n+j, acc), read_step(d, rest, j, List.append(&2, F.IsoDigit, t, acc)))

def and_l(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, bool_absurd(h))

def and_r(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, bool_absurd(h))

# Both-endian fields: equal halves agree, unequal ones are refused

def word_refl(n: Nat, w: Word(n)) -> {EQ{} == Word.cmp(n, w, w) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{True{}, t}:
          %word_refl(p, t) : {EQ{} == Word.cmp.fin(True{}, True{}, _) : Cmp}
          {==}
        case WCon{False{}, t}:
          %word_refl(p, t) : {EQ{} == Word.cmp.fin(False{}, False{}, _) : Cmp}
          {==}

def u32_refl(a: U32) -> {True{} == U32.is_eq(a, a) : Bool}:
  match a:
    case U32{+w}:
      %word_refl(32n, w) : {True{} == Cmp.is_eq(_) : Bool}
      {==}

def agree_refl(+v: U32, +off: Nat) -> {F.iso.both.agree(U32.is_eq(v, v), v, off) == Done{v} : Result<&2, &2, F.IsoError, U32>}:
  %u32_refl(v) : {F.iso.both.agree(_, v, off) == Done{v} : Result<&2, &2, F.IsoError, U32>}
  {==}

def agree_false(+a: U32, +b: U32, +off: Nat, h: {U32.is_eq(a, b) == False{} : Bool}) -> {F.iso.both.agree(U32.is_eq(a, b), a, off) == Fail{F.IsoBothEndianMismatch{off}} : Result<&2, &2, F.IsoError, U32>}:
  %Equal.sym(Bool, U32.is_eq(a, b), False{}, h) : {F.iso.both.agree(_, a, off) == Fail{F.IsoBothEndianMismatch{off}} : Result<&2, &2, F.IsoError, U32>}
  {==}

def Laws.both32_round_trip(v):
  match v:
    case {U32:v}:
      agree_refl({U32:v}, 0n)

def Laws.both16_round_trip(v):
  match v:
    case {U32:v}:
      agree_refl(B.low16({U32:v}), 0n)

def Laws.both32_trust_little(lo, hi):
  match lo hi:
    case {U32:l} U32{w}:
      {==}

def Laws.both32_trust_big(lo, hi):
  match lo hi:
    case U32{w} {U32:h}:
      {==}

def Laws.both32_mismatch(lo, hi, h):
  match lo hi:
    case {U32:l} {U32:k}:
      agree_false({U32:l}, {U32:k}, 0n, h)

def Laws.both32_mismatch_witness():
  {==}

def Laws.both16_mismatch(lo, hi, h):
  match lo hi:
    case {U32:l} {U32:k}:
      agree_false(B.low16({U32:l}), B.low16({U32:k}), 0n, h)

def Laws.both16_mismatch_witness():
  {==}

# The 7-byte date

def Laws.dir_date_round_trip(d):
  match d:
    case F.IsoDirDate{a0, a1, a2, a3, a4, a5, a6}:
      {==}

def Laws.dir_date_bytes(a0, a1, a2, a3, a4, a5, a6):
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(B.Octets.of_list([a0, a1, a2, a3, a4, a5, a6]))), B.Octets.of_list([a0, a1, a2, a3, a4, a5, a6]), BL.octets_of_list_idempotent([a0, a1, a2, a3, a4, a5, a6])) : {Done{_} == Done{B.Octets.of_list([a0, a1, a2, a3, a4, a5, a6])} : Result<&2, &2, F.IsoError, B.Octets>}
  {==}

# The 17-byte date: its digits (fields.bend's counter), read back

def len_inc(+ds: List<&2, F.IsoDigit>) -> {dlen(ds) == dlen(F.iso.digits.inc(ds)) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      match d:
        case F.IsoDig0{}:
          {==}
        case F.IsoDig1{}:
          {==}
        case F.IsoDig2{}:
          {==}
        case F.IsoDig3{}:
          {==}
        case F.IsoDig4{}:
          {==}
        case F.IsoDig5{}:
          {==}
        case F.IsoDig6{}:
          {==}
        case F.IsoDig7{}:
          {==}
        case F.IsoDig8{}:
          {==}
        case F.IsoDig9{}:
          %len_inc(t) : {1n+dlen(t) == 1n+_ : Nat}
          {==}

def len_zero(+k: Nat) -> {k == dlen(F.iso.digits.zero(k)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %len_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def len_of(+k: Nat, +n: Nat) -> {k == dlen(F.iso.digits.of(k, n)) : Nat}:
  match n:
    case 0n:
      len_zero(k)
    case 1n+p:
      %len_inc(F.iso.digits.of(k, p)) : {k == _ : Nat}
      len_of(k, p)

def nines(ds: List<&2, F.IsoDigit>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{d, t}:
      match d:
        case F.IsoDig9{}:
          nines(t)
        case _:
          False{}

def top(k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+p:
      Nat.add(9n, Nat.mul(top(p), 10n))

def value(ds: List<&2, F.IsoDigit>) -> Nat:
  F.iso.digits.value(ds)

# counting up adds one, unless every digit is a nine
def value_inc(+ds: List<&2, F.IsoDigit>, h: {nines(ds) == False{} : Bool}) -> {1n+value(ds) == value(F.iso.digits.inc(ds)) : Nat}:
  match ds:
    case Nil{}:
      Empty.absurd({1n+value(Nil{}) == value(F.iso.digits.inc(Nil{})) : Nat}, bool_absurd(Equal.sym(Bool, True{}, False{}, h)))
    case Con{d, t}:
      match d:
        case F.IsoDig0{}:
          {==}
        case F.IsoDig1{}:
          {==}
        case F.IsoDig2{}:
          {==}
        case F.IsoDig3{}:
          {==}
        case F.IsoDig4{}:
          {==}
        case F.IsoDig5{}:
          {==}
        case F.IsoDig6{}:
          {==}
        case F.IsoDig7{}:
          {==}
        case F.IsoDig8{}:
          {==}
        case F.IsoDig9{}:
          %value_inc(t, h) : {10n+Nat.mul(value(t), 10n) == Nat.mul(_, 10n) : Nat}
          {==}

# all nines: the largest number of that many digits
def value_nines(+ds: List<&2, F.IsoDigit>, h: {nines(ds) == True{} : Bool}) -> {top(dlen(ds)) == value(ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, t}:
      match d:
        case F.IsoDig9{}:
          %value_nines(t, h) : {Nat.add(9n, Nat.mul(top(dlen(t)), 10n)) == Nat.add(9n, Nat.mul(_, 10n)) : Nat}
          {==}
        case F.IsoDig0{}:
          Empty.absurd({top(dlen(Con{F.IsoDig0{}, t})) == value(Con{F.IsoDig0{}, t}) : Nat}, bool_absurd(h))
        case F.IsoDig1{}:
          Empty.absurd({top(dlen(Con{F.IsoDig1{}, t})) == value(Con{F.IsoDig1{}, t}) : Nat}, bool_absurd(h))
        case F.IsoDig2{}:
          Empty.absurd({top(dlen(Con{F.IsoDig2{}, t})) == value(Con{F.IsoDig2{}, t}) : Nat}, bool_absurd(h))
        case F.IsoDig3{}:
          Empty.absurd({top(dlen(Con{F.IsoDig3{}, t})) == value(Con{F.IsoDig3{}, t}) : Nat}, bool_absurd(h))
        case F.IsoDig4{}:
          Empty.absurd({top(dlen(Con{F.IsoDig4{}, t})) == value(Con{F.IsoDig4{}, t}) : Nat}, bool_absurd(h))
        case F.IsoDig5{}:
          Empty.absurd({top(dlen(Con{F.IsoDig5{}, t})) == value(Con{F.IsoDig5{}, t}) : Nat}, bool_absurd(h))
        case F.IsoDig6{}:
          Empty.absurd({top(dlen(Con{F.IsoDig6{}, t})) == value(Con{F.IsoDig6{}, t}) : Nat}, bool_absurd(h))
        case F.IsoDig7{}:
          Empty.absurd({top(dlen(Con{F.IsoDig7{}, t})) == value(Con{F.IsoDig7{}, t}) : Nat}, bool_absurd(h))
        case F.IsoDig8{}:
          Empty.absurd({top(dlen(Con{F.IsoDig8{}, t})) == value(Con{F.IsoDig8{}, t}) : Nat}, bool_absurd(h))

def value_zero(+k: Nat) -> {0n == value(F.iso.digits.zero(k)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %value_zero(p) : {0n == Nat.mul(_, 10n) : Nat}
      {==}

def lt_irrefl(+n: Nat) -> {False{} == Nat.is_lt(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt_irrefl(p)

def lt_weaken(+n: Nat, +t: Nat, h: {Nat.is_lt(n, t) == True{} : Bool}) -> {Nat.is_lt(n, 1n+t) == True{} : Bool}:
  match n t:
    case 0n _:
      {==}
    case 1n+a 0n:
      Empty.absurd({Nat.is_lt(1n+a, 1n) == True{} : Bool}, bool_absurd(h))
    case 1n+a 1n+b:
      lt_weaken(a, b, h)

# p is top(k), when its digits are all nines
def value_of.top(+k: Nat, +p: Nat, hb: {nines(F.iso.digits.of(k, p)) == True{} : Bool}, ih: {p == value(F.iso.digits.of(k, p)) : Nat}) -> {p == top(k) : Nat}:
  %Equal.sym(Nat, k, dlen(F.iso.digits.of(k, p)), len_of(k, p)) : {p == top(_) : Nat}
  %Equal.sym(Nat, top(dlen(F.iso.digits.of(k, p))), value(F.iso.digits.of(k, p)), value_nines(F.iso.digits.of(k, p), hb)) : {p == _ : Nat}
  ih

def value_of.lt(+k: Nat, +p: Nat, e: {p == top(k) : Nat}, h: {Nat.is_lt(p, top(k)) == True{} : Bool}) -> {Nat.is_lt(top(k), top(k)) == True{} : Bool}:
  %e : {Nat.is_lt(_, top(k)) == True{} : Bool}
  h

def value_of.pick(+k: Nat, +p: Nat, b: Bool, hb: {nines(F.iso.digits.of(k, p)) == b : Bool}, h: {Nat.is_lt(p, top(k)) == True{} : Bool}, ih: {p == value(F.iso.digits.of(k, p)) : Nat}) -> {1n+p == value(F.iso.digits.inc(F.iso.digits.of(k, p))) : Nat}:
  match b:
    case False{}:
      %value_inc(F.iso.digits.of(k, p), hb) : {1n+p == _ : Nat}
      %ih : {1n+p == 1n+_ : Nat}
      {==}
    case True{}:
      Empty.absurd({1n+p == value(F.iso.digits.inc(F.iso.digits.of(k, p))) : Nat}, bool_absurd(Equal.trans(Bool, False{}, Nat.is_lt(top(k), top(k)), True{}, lt_irrefl(top(k)), value_of.lt(k, p, value_of.top(k, p, hb, ih), h))))

# the digits of a number below 10^k give the number back
def value_of(+k: Nat, +n: Nat, +h: {Nat.is_lt(n, 1n+top(k)) == True{} : Bool}) -> {n == value(F.iso.digits.of(k, n)) : Nat}:
  match n:
    case 0n:
      value_zero(k)
    case 1n+p:
      value_of.pick(k, p, nines(F.iso.digits.of(k, p)), {==}, h, value_of(k, p, lt_weaken(p, top(k), h)))

def append_nil(+ds: List<&2, F.IsoDigit>) -> {ds == List.append(&2, F.IsoDigit, ds, Nil{}) : List<&2, F.IsoDigit>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      %append_nil(t) : {Con{d, t} == Con{d, _} : List<&2, F.IsoDigit>}
      {==}

# one field: the k digits of n, then the rest
def field_lemma(+k: Nat, +n: Nat, +rest: List<&2, U32>) -> {Done{F.IsoDigitsRest{F.iso.digits.of(k, n), B.mask(rest)}} == F.iso.voldate.field(k, B.mask(F.iso.digits.bytes(F.iso.digits.of(k, n), rest))) : Result<&2, &2, F.IsoError, F.IsoDigitsRest>}:
  %Equal.trans(Nat, Nat.add(dlen(F.iso.digits.of(k, n)), 0n), dlen(F.iso.digits.of(k, n)), k, add_zero(dlen(F.iso.digits.of(k, n))), Equal.sym(Nat, k, dlen(F.iso.digits.of(k, n)), len_of(k, n))) : {Done{F.IsoDigitsRest{F.iso.digits.of(k, n), B.mask(rest)}} == F.iso.voldate.got(F.iso.digits.read(_, B.mask(F.iso.digits.bytes(F.iso.digits.of(k, n), rest)), Some{Nil{}})) : Result<&2, &2, F.IsoError, F.IsoDigitsRest>}
  %Equal.sym(Maybe<&2, F.IsoDigitsRest>, F.iso.digits.read(Nat.add(dlen(F.iso.digits.of(k, n)), 0n), B.mask(F.iso.digits.bytes(F.iso.digits.of(k, n), rest)), Some{Nil{}}), F.iso.digits.read(0n, B.mask(rest), Some{List.append(&2, F.IsoDigit, F.iso.digits.of(k, n), Nil{})}), read_bytes(F.iso.digits.of(k, n), rest, 0n, Nil{})) : {Done{F.IsoDigitsRest{F.iso.digits.of(k, n), B.mask(rest)}} == F.iso.voldate.got(_) : Result<&2, &2, F.IsoError, F.IsoDigitsRest>}
  %append_nil(F.iso.digits.of(k, n)) : {Done{F.IsoDigitsRest{F.iso.digits.of(k, n), B.mask(rest)}} == Done{F.IsoDigitsRest{_, B.mask(rest)}} : Result<&2, &2, F.IsoError, F.IsoDigitsRest>}
  {==}

def vd_main(+y: Nat, +mo: Nat, +dd: Nat, +h: Nat, +mi: Nat, +s: Nat, +c: Nat, +o: U32, hy: {Nat.is_lt(y, 10000n) == True{} : Bool}, hmo: {Nat.is_lt(mo, 100n) == True{} : Bool}, hdd: {Nat.is_lt(dd, 100n) == True{} : Bool}, hh: {Nat.is_lt(h, 100n) == True{} : Bool}, hmi: {Nat.is_lt(mi, 100n) == True{} : Bool}, hs: {Nat.is_lt(s, 100n) == True{} : Bool}, hc: {Nat.is_lt(c, 100n) == True{} : Bool}) -> {F.IsoVolDate.decode(F.IsoVolDate.encode(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})) == Done{F.IsoVolDate.norm(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})} : Result<&2, &2, F.IsoError, F.IsoVolDate>}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(F.IsoVolDate.bytes(F.IsoVolDate{y, mo, dd, h, mi, s, c, o}))), B.mask(F.IsoVolDate.bytes(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})), BL.octets_to_of(F.IsoVolDate.bytes(F.IsoVolDate{y, mo, dd, h, mi, s, c, o}))) : {F.iso.voldate.list(_) == Done{F.IsoVolDate.norm(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})} : Result<&2, &2, F.IsoError, F.IsoVolDate>}
  %field_lemma(4n, y, F.iso.digits.bytes(F.iso.digits.of(2n, mo), F.iso.digits.bytes(F.iso.digits.of(2n, dd), F.iso.digits.bytes(F.iso.digits.of(2n, h), F.iso.digits.bytes(F.iso.digits.of(2n, mi), F.iso.digits.bytes(F.iso.digits.of(2n, s), F.iso.digits.bytes(F.iso.digits.of(2n, c), [o]))))))) : {F.iso.voldate.d1(_) == Done{F.IsoVolDate.norm(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})} : Result<&2, &2, F.IsoError, F.IsoVolDate>}
  %field_lemma(2n, mo, F.iso.digits.bytes(F.iso.digits.of(2n, dd), F.iso.digits.bytes(F.iso.digits.of(2n, h), F.iso.digits.bytes(F.iso.digits.of(2n, mi), F.iso.digits.bytes(F.iso.digits.of(2n, s), F.iso.digits.bytes(F.iso.digits.of(2n, c), [o])))))) : {F.iso.voldate.d2(F.iso.digits.value(F.iso.digits.of(4n, y)), _) == Done{F.IsoVolDate.norm(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})} : Result<&2, &2, F.IsoError, F.IsoVolDate>}
  %field_lemma(2n, dd, F.iso.digits.bytes(F.iso.digits.of(2n, h), F.iso.digits.bytes(F.iso.digits.of(2n, mi), F.iso.digits.bytes(F.iso.digits.of(2n, s), F.iso.digits.bytes(F.iso.digits.of(2n, c), [o]))))) : {F.iso.voldate.d3(F.iso.digits.value(F.iso.digits.of(4n, y)), F.iso.digits.value(F.iso.digits.of(2n, mo)), _) == Done{F.IsoVolDate.norm(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})} : Result<&2, &2, F.IsoError, F.IsoVolDate>}
  %field_lemma(2n, h, F.iso.digits.bytes(F.iso.digits.of(2n, mi), F.iso.digits.bytes(F.iso.digits.of(2n, s), F.iso.digits.bytes(F.iso.digits.of(2n, c), [o])))) : {F.iso.voldate.d4(F.iso.digits.value(F.iso.digits.of(4n, y)), F.iso.digits.value(F.iso.digits.of(2n, mo)), F.iso.digits.value(F.iso.digits.of(2n, dd)), _) == Done{F.IsoVolDate.norm(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})} : Result<&2, &2, F.IsoError, F.IsoVolDate>}
  %field_lemma(2n, mi, F.iso.digits.bytes(F.iso.digits.of(2n, s), F.iso.digits.bytes(F.iso.digits.of(2n, c), [o]))) : {F.iso.voldate.d5(F.iso.digits.value(F.iso.digits.of(4n, y)), F.iso.digits.value(F.iso.digits.of(2n, mo)), F.iso.digits.value(F.iso.digits.of(2n, dd)), F.iso.digits.value(F.iso.digits.of(2n, h)), _) == Done{F.IsoVolDate.norm(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})} : Result<&2, &2, F.IsoError, F.IsoVolDate>}
  %field_lemma(2n, s, F.iso.digits.bytes(F.iso.digits.of(2n, c), [o])) : {F.iso.voldate.d6(F.iso.digits.value(F.iso.digits.of(4n, y)), F.iso.digits.value(F.iso.digits.of(2n, mo)), F.iso.digits.value(F.iso.digits.of(2n, dd)), F.iso.digits.value(F.iso.digits.of(2n, h)), F.iso.digits.value(F.iso.digits.of(2n, mi)), _) == Done{F.IsoVolDate.norm(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})} : Result<&2, &2, F.IsoError, F.IsoVolDate>}
  %field_lemma(2n, c, [o]) : {F.iso.voldate.d7(F.iso.digits.value(F.iso.digits.of(4n, y)), F.iso.digits.value(F.iso.digits.of(2n, mo)), F.iso.digits.value(F.iso.digits.of(2n, dd)), F.iso.digits.value(F.iso.digits.of(2n, h)), F.iso.digits.value(F.iso.digits.of(2n, mi)), F.iso.digits.value(F.iso.digits.of(2n, s)), _) == Done{F.IsoVolDate.norm(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})} : Result<&2, &2, F.IsoError, F.IsoVolDate>}
  %value_of(4n, y, hy) : {Done{F.IsoVolDate{_, F.iso.digits.value(F.iso.digits.of(2n, mo)), F.iso.digits.value(F.iso.digits.of(2n, dd)), F.iso.digits.value(F.iso.digits.of(2n, h)), F.iso.digits.value(F.iso.digits.of(2n, mi)), F.iso.digits.value(F.iso.digits.of(2n, s)), F.iso.digits.value(F.iso.digits.of(2n, c)), B.byte(o)}} == Done{F.IsoVolDate.norm(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})} : Result<&2, &2, F.IsoError, F.IsoVolDate>}
  %value_of(2n, mo, hmo) : {Done{F.IsoVolDate{y, _, F.iso.digits.value(F.iso.digits.of(2n, dd)), F.iso.digits.value(F.iso.digits.of(2n, h)), F.iso.digits.value(F.iso.digits.of(2n, mi)), F.iso.digits.value(F.iso.digits.of(2n, s)), F.iso.digits.value(F.iso.digits.of(2n, c)), B.byte(o)}} == Done{F.IsoVolDate.norm(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})} : Result<&2, &2, F.IsoError, F.IsoVolDate>}
  %value_of(2n, dd, hdd) : {Done{F.IsoVolDate{y, mo, _, F.iso.digits.value(F.iso.digits.of(2n, h)), F.iso.digits.value(F.iso.digits.of(2n, mi)), F.iso.digits.value(F.iso.digits.of(2n, s)), F.iso.digits.value(F.iso.digits.of(2n, c)), B.byte(o)}} == Done{F.IsoVolDate.norm(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})} : Result<&2, &2, F.IsoError, F.IsoVolDate>}
  %value_of(2n, h, hh) : {Done{F.IsoVolDate{y, mo, dd, _, F.iso.digits.value(F.iso.digits.of(2n, mi)), F.iso.digits.value(F.iso.digits.of(2n, s)), F.iso.digits.value(F.iso.digits.of(2n, c)), B.byte(o)}} == Done{F.IsoVolDate.norm(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})} : Result<&2, &2, F.IsoError, F.IsoVolDate>}
  %value_of(2n, mi, hmi) : {Done{F.IsoVolDate{y, mo, dd, h, _, F.iso.digits.value(F.iso.digits.of(2n, s)), F.iso.digits.value(F.iso.digits.of(2n, c)), B.byte(o)}} == Done{F.IsoVolDate.norm(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})} : Result<&2, &2, F.IsoError, F.IsoVolDate>}
  %value_of(2n, s, hs) : {Done{F.IsoVolDate{y, mo, dd, h, mi, _, F.iso.digits.value(F.iso.digits.of(2n, c)), B.byte(o)}} == Done{F.IsoVolDate.norm(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})} : Result<&2, &2, F.IsoError, F.IsoVolDate>}
  %value_of(2n, c, hc) : {Done{F.IsoVolDate{y, mo, dd, h, mi, s, _, B.byte(o)}} == Done{F.IsoVolDate.norm(F.IsoVolDate{y, mo, dd, h, mi, s, c, o})} : Result<&2, &2, F.IsoError, F.IsoVolDate>}
  {==}

def Laws.vol_date_round_trip(d, h):
  match d:
    case F.IsoVolDate{+y, +mo, +dd, +hr, +mi, +s, +c, +o}:
      +h0 = h
      +h1 = and_r(Nat.is_lt(y, 10000n), Bool.and(Nat.is_lt(mo, 100n), Bool.and(Nat.is_lt(dd, 100n), Bool.and(Nat.is_lt(hr, 100n), Bool.and(Nat.is_lt(mi, 100n), Bool.and(Nat.is_lt(s, 100n), Nat.is_lt(c, 100n)))))), h0)
      +h2 = and_r(Nat.is_lt(mo, 100n), Bool.and(Nat.is_lt(dd, 100n), Bool.and(Nat.is_lt(hr, 100n), Bool.and(Nat.is_lt(mi, 100n), Bool.and(Nat.is_lt(s, 100n), Nat.is_lt(c, 100n))))), h1)
      +h3 = and_r(Nat.is_lt(dd, 100n), Bool.and(Nat.is_lt(hr, 100n), Bool.and(Nat.is_lt(mi, 100n), Bool.and(Nat.is_lt(s, 100n), Nat.is_lt(c, 100n)))), h2)
      +h4 = and_r(Nat.is_lt(hr, 100n), Bool.and(Nat.is_lt(mi, 100n), Bool.and(Nat.is_lt(s, 100n), Nat.is_lt(c, 100n))), h3)
      +h5 = and_r(Nat.is_lt(mi, 100n), Bool.and(Nat.is_lt(s, 100n), Nat.is_lt(c, 100n)), h4)
      vd_main(y, mo, dd, hr, mi, s, c, o, and_l(Nat.is_lt(y, 10000n), Bool.and(Nat.is_lt(mo, 100n), Bool.and(Nat.is_lt(dd, 100n), Bool.and(Nat.is_lt(hr, 100n), Bool.and(Nat.is_lt(mi, 100n), Bool.and(Nat.is_lt(s, 100n), Nat.is_lt(c, 100n)))))), h0), and_l(Nat.is_lt(mo, 100n), Bool.and(Nat.is_lt(dd, 100n), Bool.and(Nat.is_lt(hr, 100n), Bool.and(Nat.is_lt(mi, 100n), Bool.and(Nat.is_lt(s, 100n), Nat.is_lt(c, 100n))))), h1), and_l(Nat.is_lt(dd, 100n), Bool.and(Nat.is_lt(hr, 100n), Bool.and(Nat.is_lt(mi, 100n), Bool.and(Nat.is_lt(s, 100n), Nat.is_lt(c, 100n)))), h2), and_l(Nat.is_lt(hr, 100n), Bool.and(Nat.is_lt(mi, 100n), Bool.and(Nat.is_lt(s, 100n), Nat.is_lt(c, 100n))), h3), and_l(Nat.is_lt(mi, 100n), Bool.and(Nat.is_lt(s, 100n), Nat.is_lt(c, 100n)), h4), and_l(Nat.is_lt(s, 100n), Nat.is_lt(c, 100n), h5), and_r(Nat.is_lt(s, 100n), Nat.is_lt(c, 100n), h5))

# UCS-2 names

def ucs2_head(c: U32) -> {Some{B.low16(c)} == B.be16.head(B.mask(B.be16(c))) : Maybe<&2, U32>}:
  match c:
    case {U32:c}:
      {==}

def ucs2_list(s: String) -> {Done{J.Iso.ucs2_norm(s)} == J.iso.ucs2.list(B.mask(J.iso.ucs2.bytes(s))) : Result<&2, &2, F.IsoError, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{U32{+w}}, +t}:
      %ucs2_head(U32{w}) : {Done{SCon{Chr{B.low16(U32{w})}, J.Iso.ucs2_norm(t)}} == J.iso.ucs2.cons(_, J.iso.ucs2.list(B.mask(J.iso.ucs2.bytes(t)))) : Result<&2, &2, F.IsoError, String>}
      %ucs2_list(t) : {Done{SCon{Chr{B.low16(U32{w})}, J.Iso.ucs2_norm(t)}} == J.iso.ucs2.cons(Some{B.low16(U32{w})}, _) : Result<&2, &2, F.IsoError, String>}
      {==}

def Laws.ucs2_round_trip(s):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(J.iso.ucs2.bytes(s))), B.mask(J.iso.ucs2.bytes(s)), BL.octets_to_of(J.iso.ucs2.bytes(s))) : {J.iso.ucs2.list(_) == Done{J.Iso.ucs2_norm(s)} : Result<&2, &2, F.IsoError, String>}
  Equal.sym(Result<&2, &2, F.IsoError, String>, Done{J.Iso.ucs2_norm(s)}, J.iso.ucs2.list(B.mask(J.iso.ucs2.bytes(s))), ucs2_list(s))

# Reading only what is needed: the end of a stream reads nothing

def Laws.stream_end_reads_nothing(d, i, left):
  {==}

# Vectors, by computation

def Laws.joliet_level_3():
  {==}

def Laws.joliet_level_1():
  {==}

def Laws.joliet_level_none():
  {==}

def Laws.text_trims_spaces():
  {==}

def Laws.ucs2_text():
  {==}

def Laws.ucs2_odd_refused():
  {==}

def Laws.susp_two_entries():
  {==}

def Laws.susp_stops_at_st():
  {==}

def Laws.susp_short_length_refused():
  {==}

def Laws.susp_past_area_refused():
  {==}

def Laws.sp_skip():
  {==}

def Laws.rr_link_root():
  {==}

def Laws.rr_link_continued():
  {==}

def Laws.rr_name_from_nm():
  {==}

def Laws.rr_px_short_refused():
  {==}

def Laws.dirrec_no_identifier():
  {==}

def Laws.dirrec_truncated():
  {==}

def Laws.vol_date_bad_digit():
  {==}

def Laws.blocks_round_up():
  {==}

def Laws.blocks_exact():
  {==}

def Laws.vol_date_witness():
  {==}

def Laws.dirrec_witness():
  {==}

# Reading only what is needed: order on naturals

def le_zero(+b: Nat) -> {True{} == Nat.is_le(0n, b) : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_refl(+a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

def lt_succ_self(+a: Nat) -> {True{} == Nat.is_lt(a, Nat.add(a, 1n)) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      lt_succ_self(p)

def le_add(+a: Nat, +b: Nat) -> {True{} == Nat.is_le(a, Nat.add(a, b)) : Bool}:
  match a:
    case 0n:
      le_zero(b)
    case 1n+p:
      le_add(p, b)

def lt_add_both(+e: Nat, +i: Nat, +c: Nat, h: {Nat.is_lt(i, c) == True{} : Bool}) -> {True{} == Nat.is_lt(Nat.add(e, i), Nat.add(e, c)) : Bool}:
  match e:
    case 0n:
      Equal.sym(Bool, Nat.is_lt(i, c), True{}, h)
    case 1n+p:
      lt_add_both(p, i, c, h)

# i + (1 + p) <= c: so i < c
def le_lt(+i: Nat, +p: Nat, +c: Nat, h: {Nat.is_le(Nat.add(i, 1n+p), c) == True{} : Bool}) -> {Nat.is_lt(i, c) == True{} : Bool}:
  match i c:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, bool_absurd(h))
    case 0n 1n+q:
      {==}
    case 1n+j 0n:
      Empty.absurd({Nat.is_lt(1n+j, 0n) == True{} : Bool}, bool_absurd(h))
    case 1n+j 1n+q:
      le_lt(j, p, q, h)

def le_next(+i: Nat, +p: Nat, +c: Nat, h: {Nat.is_le(Nat.add(i, 1n+p), c) == True{} : Bool}) -> {Nat.is_le(Nat.add(1n+i, p), c) == True{} : Bool}:
  %add_succ(i, p) : {Nat.is_le(_, c) == True{} : Bool}
  h

# a block inside the fence reads as on the device
def fence_in(+d: BD.MemDev, +ext: Nat, +count: Nat, +i: Nat, h: {Nat.is_lt(i, count) == True{} : Bool}) -> {BD.MemDev.read_block(d, Nat.add(ext, i)) == FN.IsoFence.read_block(FN.IsoFence{d, ext, count}, Nat.add(ext, i)) : Result<&2, &2, BD.DevError, B.Octets>}:
  %le_add(ext, i) : {BD.MemDev.read_block(d, Nat.add(ext, i)) == FN.iso.fence.pick(Bool.and(_, Nat.is_lt(Nat.add(ext, i), Nat.add(ext, count))), d, Nat.add(ext, i)) : Result<&2, &2, BD.DevError, B.Octets>}
  %lt_add_both(ext, i, count, h) : {BD.MemDev.read_block(d, Nat.add(ext, i)) == FN.iso.fence.pick(Bool.and(True{}, _), d, Nat.add(ext, i)) : Result<&2, &2, BD.DevError, B.Octets>}
  {==}

# the reference walk of k sectors from sector i, inside a fence of count
# blocks from ext, reads as on the device
def walk_fenced(+k: Nat, +d: BD.MemDev, +mode: F.IsoEndian, +ext: Nat, +left: Nat, +i: Nat, +count: Nat, +h: {Nat.is_le(Nat.add(i, k), count) == True{} : Bool}) -> {DR.iso.dir.walk.ref(~BD.MemDev, ~BD.MemDev.read_block, k, d, mode, ext, left, i) == DR.iso.dir.walk.ref(~FN.IsoFence, ~FN.IsoFence.read_block, k, FN.IsoFence{d, ext, count}, mode, ext, left, i) : Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %fence_in(d, ext, count, i, le_lt(i, p, count, h)) : {DR.iso.dir.walk.ref(~BD.MemDev, ~BD.MemDev.read_block, 1n+p, d, mode, ext, left, i) == DR.iso.dir.walk.step(F.iso.dev(_), mode, left, DR.iso.dir.walk.ref(~FN.IsoFence, ~FN.IsoFence.read_block, p, FN.IsoFence{d, ext, count}, mode, ext, Nat.sub(left, 2048n), 1n+i)) : Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>}
      %walk_fenced(p, d, mode, ext, Nat.sub(left, 2048n), 1n+i, count, le_next(i, p, count, h)) : {DR.iso.dir.walk.ref(~BD.MemDev, ~BD.MemDev.read_block, 1n+p, d, mode, ext, left, i) == DR.iso.dir.walk.step(F.iso.dev(BD.MemDev.read_block(d, Nat.add(ext, i))), mode, left, _) : Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>}
      {==}

# Iso.dir_records runs the loop iso.dir.walk; it equals the reference
# iso.dir.walk.ref (on which the fence is proved above) for every device and
# input: with acc the records of the sectors before (latest first), the loop
# gives the reference's records with acc reversed in front of them.

def dw_lift(a: List<&2, R.IsoDirRec>, r: Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>) -> Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{rs}:
      Done{DR.iso.dir.rev(a, rs)}

def dw_lift2(acc: Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>, r: Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>) -> Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>:
  match acc:
    case Fail{e}:
      Fail{e}
    case Done{a}:
      dw_lift(a, r)

def dw_rr(xs: List<&2, R.IsoDirRec>, acc: List<&2, R.IsoDirRec>, b: List<&2, R.IsoDirRec>) -> {DR.iso.dir.rev(DR.iso.dir.rev(xs, acc), b) == DR.iso.dir.rev(acc, List.append(&2, R.IsoDirRec, xs, b)) : List<&2, R.IsoDirRec>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      dw_rr(t, Con{h, acc}, b)

def dw_more(+recs: List<&2, R.IsoDirRec>, +a: List<&2, R.IsoDirRec>, rest: Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>) -> {dw_lift(DR.iso.dir.rev(recs, a), rest) == dw_lift(a, DR.iso.dir.walk.join(Done{recs}, rest)) : Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>}:
  match rest:
    case Fail{e}:
      {==}
    case Done{more}:
      Equal.cong(List<&2, R.IsoDirRec>, Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>, l => Done{l}, DR.iso.dir.rev(DR.iso.dir.rev(recs, a), more), DR.iso.dir.rev(a, List.append(&2, R.IsoDirRec, recs, more)), dw_rr(recs, a, more))

def dw_push(rr: Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>, +a: List<&2, R.IsoDirRec>, +rest: Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>) -> {dw_lift2(DR.iso.dir.walk.push(rr, a), rest) == dw_lift(a, DR.iso.dir.walk.join(rr, rest)) : Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>}:
  match rr:
    case Fail{e}:
      {==}
    case Done{recs}:
      dw_more(recs, a, rest)

def dw_add(r: Result<&2, &2, F.IsoError, B.Octets>, +mode: F.IsoEndian, +left: Nat, +a: List<&2, R.IsoDirRec>, +rest: Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>) -> {dw_lift2(DR.iso.dir.walk.add(r, mode, left, a), rest) == dw_lift(a, DR.iso.dir.walk.step(r, mode, left, rest)) : Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>}:
  match r:
    case Fail{e}:
      {==}
    case Done{blk}:
      dw_push(DR.iso.dir.records(mode, left, blk), a, rest)

def dw_go(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, +k: Nat, +d: D, +mode: F.IsoEndian, +ext: Nat, +left: Nat, +i: Nat, acc: Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>) -> {DR.iso.dir.walk(~D, ~read_block, k, d, mode, ext, left, i, acc) == dw_lift2(acc, DR.iso.dir.walk.ref(~D, ~read_block, k, d, mode, ext, left, i)) : Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>}:
  match k:
    case 0n:
      match acc:
        case Fail{e}:
          {==}
        case Done{a}:
          {==}
    case 1n+p:
      match acc:
        case Fail{e}:
          {==}
        case Done{+a}:
          Equal.trans(Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>, DR.iso.dir.walk(~D, ~read_block, p, d, mode, ext, Nat.sub(left, 2048n), 1n+i, DR.iso.dir.walk.add(F.iso.read_sector(~D, ~read_block, d, Nat.add(ext, i)), mode, left, a)), dw_lift2(DR.iso.dir.walk.add(F.iso.read_sector(~D, ~read_block, d, Nat.add(ext, i)), mode, left, a), DR.iso.dir.walk.ref(~D, ~read_block, p, d, mode, ext, Nat.sub(left, 2048n), 1n+i)), dw_lift(a, DR.iso.dir.walk.step(F.iso.read_sector(~D, ~read_block, d, Nat.add(ext, i)), mode, left, DR.iso.dir.walk.ref(~D, ~read_block, p, d, mode, ext, Nat.sub(left, 2048n), 1n+i))),
            dw_go(~D, ~read_block, p, d, mode, ext, Nat.sub(left, 2048n), 1n+i, DR.iso.dir.walk.add(F.iso.read_sector(~D, ~read_block, d, Nat.add(ext, i)), mode, left, a)),
            dw_add(F.iso.read_sector(~D, ~read_block, d, Nat.add(ext, i)), mode, left, a, DR.iso.dir.walk.ref(~D, ~read_block, p, d, mode, ext, Nat.sub(left, 2048n), 1n+i)))

def dw_nil(r: Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>) -> {r == dw_lift2(Done{Nil{}}, r) : Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>}:
  match r:
    case Fail{e}:
      {==}
    case Done{rs}:
      {==}

# reference == loop, the direction a rewrite uses
def dw_eq(~D: Data, ~read_block: D -> Nat -> Result<&2, &2, BD.DevError, B.Octets>, +k: Nat, +d: D, +mode: F.IsoEndian, +ext: Nat, +left: Nat, +i: Nat) -> {DR.iso.dir.walk.ref(~D, ~read_block, k, d, mode, ext, left, i) == DR.iso.dir.walk(~D, ~read_block, k, d, mode, ext, left, i, Done{Nil{}}) : Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>}:
  Equal.trans(Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>, DR.iso.dir.walk.ref(~D, ~read_block, k, d, mode, ext, left, i), dw_lift2(Done{Nil{}}, DR.iso.dir.walk.ref(~D, ~read_block, k, d, mode, ext, left, i)), DR.iso.dir.walk(~D, ~read_block, k, d, mode, ext, left, i, Done{Nil{}}), dw_nil(DR.iso.dir.walk.ref(~D, ~read_block, k, d, mode, ext, left, i)), Equal.sym(Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>, DR.iso.dir.walk(~D, ~read_block, k, d, mode, ext, left, i, Done{Nil{}}), dw_lift2(Done{Nil{}}, DR.iso.dir.walk.ref(~D, ~read_block, k, d, mode, ext, left, i)), dw_go(~D, ~read_block, k, d, mode, ext, left, i, Done{Nil{}})))

def Laws.dir_records_fenced(d, mode, ext, size):
  %dw_eq(~BD.MemDev, ~BD.MemDev.read_block, R.Iso.blocks(size), d, mode, U32.to_nat(ext), U32.to_nat(size), 0n) : {_ == DR.iso.dir.walk(~FN.IsoFence, ~FN.IsoFence.read_block, R.Iso.blocks(size), FN.IsoFence{d, U32.to_nat(ext), R.Iso.blocks(size)}, mode, U32.to_nat(ext), U32.to_nat(size), 0n, Done{Nil{}}) : Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>}
  %dw_eq(~FN.IsoFence, ~FN.IsoFence.read_block, R.Iso.blocks(size), FN.IsoFence{d, U32.to_nat(ext), R.Iso.blocks(size)}, mode, U32.to_nat(ext), U32.to_nat(size), 0n) : {DR.iso.dir.walk.ref(~BD.MemDev, ~BD.MemDev.read_block, R.Iso.blocks(size), d, mode, U32.to_nat(ext), U32.to_nat(size), 0n) == _ : Result<&2, &2, F.IsoError, List<&2, R.IsoDirRec>>}
  walk_fenced(R.Iso.blocks(size), d, mode, U32.to_nat(ext), U32.to_nat(size), 0n, R.Iso.blocks(size), le_refl(R.Iso.blocks(size)))

def Laws.stream_step_fenced(d, b, s, t, i, left):
  %Equal.sym(Bool, Nat.is_le(Nat.add(U32.to_nat(b), i), Nat.add(U32.to_nat(b), i)), True{}, le_refl(Nat.add(U32.to_nat(b), i))) : {FL.Iso.file_next(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, d, FL.IsoCursor{Con{DR.IsoExtent{b, s}, t}, i, left}) == FL.iso.file.piece.r(Con{DR.IsoExtent{b, s}, t}, i, left, F.iso.dev(FN.iso.fence.pick(Bool.and(_, Nat.is_lt(Nat.add(U32.to_nat(b), i), Nat.add(Nat.add(U32.to_nat(b), i), 1n))), d, Nat.add(U32.to_nat(b), i)))) : Result<&2, &2, F.IsoError, FL.IsoChunk>}
  %lt_succ_self(Nat.add(U32.to_nat(b), i)) : {FL.Iso.file_next(~BD.MemDev, ~BD.MemDev.block_size, ~BD.MemDev.read_block, d, FL.IsoCursor{Con{DR.IsoExtent{b, s}, t}, i, left}) == FL.iso.file.piece.r(Con{DR.IsoExtent{b, s}, t}, i, left, F.iso.dev(FN.iso.fence.pick(Bool.and(True{}, _), d, Nat.add(U32.to_nat(b), i)))) : Result<&2, &2, F.IsoError, FL.IsoChunk>}
  {==}

# Directory records

# lengths below 256 survive the length bytes: a reflection over 0..255
def bn(+n: Nat) -> Bool:
  Nat.is_eq(U32.to_nat(B.byte(U32.from_nat(n))), n)

def allb(k: Nat, +i: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+p:
      Bool.and(bn(i), allb(p, 1n+i))

def all256() -> {allb(256n, 0n) == True{} : Bool}:
  {==}

def nat_eq(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, bool_absurd(h))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, bool_absurd(h))
    case 1n+p 1n+q:
      %nat_eq(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

def lt_zero(+m: Nat, h: {Nat.is_lt(m, 0n) == True{} : Bool}) -> {False{} == True{} : Bool}:
  match m:
    case 0n:
      h
    case 1n+k:
      h

def below(+k: Nat, +n: Nat, +i: Nat, hk: {allb(k, i) == True{} : Bool}, hn: {Nat.is_lt(n, k) == True{} : Bool}) -> {bn(Nat.add(n, i)) == True{} : Bool}:
  match k n:
    case 0n _:
      Empty.absurd({bn(Nat.add(n, i)) == True{} : Bool}, bool_absurd(lt_zero(n, hn)))
    case 1n+p 0n:
      and_l(bn(i), allb(p, 1n+i), hk)
    case 1n+p 1n+m:
      %add_succ(m, i) : {bn(_) == True{} : Bool}
      below(p, m, 1n+i, and_r(bn(i), allb(p, 1n+i), hk), hn)

def byte_nat(+n: Nat, h: {Nat.is_lt(n, 256n) == True{} : Bool}) -> {n == U32.to_nat(B.byte(U32.from_nat(n))) : Nat}:
  +h2 = below(256n, n, 0n, all256(), h)
  %add_zero(n) : {_ == U32.to_nat(B.byte(U32.from_nat(_))) : Nat}
  Equal.sym(Nat, U32.to_nat(B.byte(U32.from_nat(Nat.add(n, 0n)))), Nat.add(n, 0n), nat_eq(U32.to_nat(B.byte(U32.from_nat(Nat.add(n, 0n)))), Nat.add(n, 0n), h2))

def nat_eq_refl(+a: Nat) -> {True{} == Nat.is_eq(a, a) : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      nat_eq_refl(p)

def sub_add(+a: Nat, +b: Nat) -> {b == Nat.sub(Nat.add(a, b), a) : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      sub_add(p, b)

def lt_add_l(+a: Nat, +b: Nat, +c: Nat, h: {Nat.is_lt(Nat.add(a, b), c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a c:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, bool_absurd(lt_zero(b, h)))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, bool_absurd(h))
    case 1n+p 1n+q:
      lt_add_l(p, b, q, h)

def lt_mono(+n: Nat, +t: Nat, +k: Nat, h: {Nat.is_lt(n, t) == True{} : Bool}) -> {Nat.is_lt(n, Nat.add(k, t)) == True{} : Bool}:
  match k:
    case 0n:
      h
    case 1n+p:
      lt_weaken(n, Nat.add(p, t), lt_mono(n, t, p, h))

# Lists: taking and dropping what was appended, masking

def take_len(+a: List<&2, U32>, +b: List<&2, U32>) -> {a == B.take(B.len(a), B.append(a, b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %take_len(t, b) : {Con{h, t} == Con{h, _} : List<&2, U32>}
      {==}

def drop_len(+a: List<&2, U32>, +b: List<&2, U32>) -> {b == B.drop(B.len(a), B.append(a, b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      drop_len(t, b)

def drop_zeros(+n: Nat, +b: List<&2, U32>) -> {b == B.drop(n, B.append(B.zeros(n), b)) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      drop_zeros(p, b)

def mask_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.append(B.mask(a), B.mask(b)) == B.mask(B.append(a, b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %mask_append(t, b) : {Con{B.byte(h), B.append(B.mask(t), B.mask(b))} == Con{B.byte(h), _} : List<&2, U32>}
      {==}

def mask_zeros(+n: Nat) -> {B.zeros(n) == B.mask(B.zeros(n)) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %mask_zeros(p) : {Con{0, B.zeros(p)} == Con{0, _} : List<&2, U32>}
      {==}

# the bytes of an Octets are bytes already
def mask_octets(+o: B.Octets) -> {B.Octets.to_list(o) == B.mask(B.Octets.to_list(o)) : List<&2, U32>}:
  %BL.octets_to_of(B.Octets.to_list(o)) : {B.Octets.to_list(o) == _ : List<&2, U32>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(o)), o, BL.octets_of_to(o)) : {B.Octets.to_list(o) == B.Octets.to_list(_) : List<&2, U32>}
  {==}

def append_assoc(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> {B.append(a, B.append(b, c)) == B.append(B.append(a, b), c) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %append_assoc(t, b, c) : {Con{h, B.append(t, B.append(b, c))} == Con{h, _} : List<&2, U32>}
      {==}

# The identifier and system use area of a record (stage A): from the bytes
# after the 33-byte header, with LEN_DR and LEN_FI as the writer stored them
def tail_lemma(+id: B.Octets, +su: B.Octets, +rest: List<&2, U32>, h1: {Nat.is_le(1n, R.iso.olen(id)) == True{} : Bool}, +h2: {Nat.is_lt(Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)), 256n) == True{} : Bool}) -> {Done{R.IsoDirRecTail{id, su}} == R.iso.dirrec.tail(U32.to_nat(B.byte(U32.from_nat(Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su))))), U32.to_nat(B.byte(U32.from_nat(R.iso.olen(id)))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), rest)))) : Result<&2, &2, F.IsoError, R.IsoDirRecTail>}:
  +hl = lt_mono(R.iso.olen(id), 223n, 33n, lt_add_l(R.iso.olen(id), R.iso.pad(R.iso.olen(id)), 223n, lt_add_l(Nat.add(R.iso.olen(id), R.iso.pad(R.iso.olen(id))), R.iso.olen(su), 223n, h2)))
  %byte_nat(Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)), h2) : {Done{R.IsoDirRecTail{id, su}} == R.iso.dirrec.tail(_, U32.to_nat(B.byte(U32.from_nat(R.iso.olen(id)))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), rest)))) : Result<&2, &2, F.IsoError, R.IsoDirRecTail>}
  %byte_nat(R.iso.olen(id), hl) : {Done{R.IsoDirRecTail{id, su}} == R.iso.dirrec.tail(Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)), _, B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), rest)))) : Result<&2, &2, F.IsoError, R.IsoDirRecTail>}
  %Equal.sym(Bool, Nat.is_le(1n, R.iso.olen(id)), True{}, h1) : {Done{R.IsoDirRecTail{id, su}} == R.iso.dirrec.named(_, Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)), R.iso.olen(id), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), rest)))) : Result<&2, &2, F.IsoError, R.IsoDirRecTail>}
  %le_add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)) : {Done{R.IsoDirRecTail{id, su}} == R.iso.dirrec.room(_, Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)), R.iso.olen(id), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), rest)))) : Result<&2, &2, F.IsoError, R.IsoDirRecTail>}
  %take_len(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), rest))) : {Done{R.IsoDirRecTail{id, su}} == R.iso.dirrec.ident(Nat.is_eq(B.len(_), R.iso.olen(id)), _, Nat.sub(Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)), R.iso.fixed(R.iso.olen(id))), B.drop(R.iso.pad(R.iso.olen(id)), B.drop(R.iso.olen(id), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), rest)))))) : Result<&2, &2, F.IsoError, R.IsoDirRecTail>}
  %nat_eq_refl(R.iso.olen(id)) : {Done{R.IsoDirRecTail{id, su}} == R.iso.dirrec.ident(_, B.Octets.to_list(id), Nat.sub(Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)), R.iso.fixed(R.iso.olen(id))), B.drop(R.iso.pad(R.iso.olen(id)), B.drop(R.iso.olen(id), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), rest)))))) : Result<&2, &2, F.IsoError, R.IsoDirRecTail>}
  %drop_len(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), rest))) : {Done{R.IsoDirRecTail{id, su}} == R.iso.dirrec.su(Nat.is_eq(B.len(B.take(Nat.sub(Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)), R.iso.fixed(R.iso.olen(id))), B.drop(R.iso.pad(R.iso.olen(id)), _))), Nat.sub(Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)), R.iso.fixed(R.iso.olen(id)))), B.Octets.to_list(id), B.take(Nat.sub(Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)), R.iso.fixed(R.iso.olen(id))), B.drop(R.iso.pad(R.iso.olen(id)), _))) : Result<&2, &2, F.IsoError, R.IsoDirRecTail>}
  %drop_zeros(R.iso.pad(R.iso.olen(id)), B.append(B.Octets.to_list(su), rest)) : {Done{R.IsoDirRecTail{id, su}} == R.iso.dirrec.su(Nat.is_eq(B.len(B.take(Nat.sub(Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)), R.iso.fixed(R.iso.olen(id))), _)), Nat.sub(Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)), R.iso.fixed(R.iso.olen(id)))), B.Octets.to_list(id), B.take(Nat.sub(Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)), R.iso.fixed(R.iso.olen(id))), _)) : Result<&2, &2, F.IsoError, R.IsoDirRecTail>}
  %sub_add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)) : {Done{R.IsoDirRecTail{id, su}} == R.iso.dirrec.su(Nat.is_eq(B.len(B.take(_, B.append(B.Octets.to_list(su), rest))), _), B.Octets.to_list(id), B.take(_, B.append(B.Octets.to_list(su), rest))) : Result<&2, &2, F.IsoError, R.IsoDirRecTail>}
  %take_len(B.Octets.to_list(su), rest) : {Done{R.IsoDirRecTail{id, su}} == R.iso.dirrec.su(Nat.is_eq(B.len(_), R.iso.olen(su)), B.Octets.to_list(id), _) : Result<&2, &2, F.IsoError, R.IsoDirRecTail>}
  %nat_eq_refl(R.iso.olen(su)) : {Done{R.IsoDirRecTail{id, su}} == R.iso.dirrec.su(_, B.Octets.to_list(id), B.Octets.to_list(su)) : Result<&2, &2, F.IsoError, R.IsoDirRecTail>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(id)), id, BL.octets_of_to(id)) : {Done{R.IsoDirRecTail{id, su}} == Done{R.IsoDirRecTail{_, B.Octets.of_list(B.Octets.to_list(su))}} : Result<&2, &2, F.IsoError, R.IsoDirRecTail>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(su)), su, BL.octets_of_to(su)) : {Done{R.IsoDirRecTail{id, su}} == Done{R.IsoDirRecTail{id, _}} : Result<&2, &2, F.IsoError, R.IsoDirRecTail>}
  {==}

# Both-endian fields inside a list of bytes (stage B)
def both32_lemma(+v: U32, +r1: List<&2, U32>, +r2: List<&2, U32>, +off: Nat) -> {Done{v} == F.iso.both32.list(F.IsoEndianCheck{}, B.append(B.mask(B.append(B.le32(v), B.append(B.be32(v), r1))), r2), off) : Result<&2, &2, F.IsoError, U32>}:
  match v:
    case {U32:v}:
      Equal.sym(Result<&2, &2, F.IsoError, U32>, F.iso.both.agree(U32.is_eq({U32:v}, {U32:v}), {U32:v}, off), Done{{U32:v}}, agree_refl({U32:v}, off))

def both16_lemma(+v: U32, +r1: List<&2, U32>, +r2: List<&2, U32>, +off: Nat) -> {Done{B.low16(v)} == F.iso.both16.list(F.IsoEndianCheck{}, B.append(B.mask(B.append(B.le16(v), B.append(B.be16(v), r1))), r2), off) : Result<&2, &2, F.IsoError, U32>}:
  match v:
    case {U32:v}:
      Equal.sym(Result<&2, &2, F.IsoError, U32>, F.iso.both.agree(U32.is_eq(B.low16({U32:v}), B.low16({U32:v})), B.low16({U32:v}), off), Done{B.low16({U32:v})}, agree_refl(B.low16({U32:v}), off))

# the bytes the decoder sees: the masked header, then the identifier, the
# padding, the system use area and whatever follows, unchanged
def bytes_lemma(+hdr: List<&2, U32>, +id: B.Octets, +su: B.Octets, +rest: B.Octets) -> {B.append(B.mask(hdr), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))) == B.Octets.to_list(B.Octets.append(B.Octets.of_list(B.append(hdr, R.iso.dirrec.body(id, R.iso.olen(id), su))), rest)) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.of_list(B.append(hdr, B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.Octets.to_list(su))))), rest)), B.append(B.Octets.to_list(B.Octets.of_list(B.append(hdr, B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.Octets.to_list(su)))))), B.Octets.to_list(rest)), BL.octets_append_list(B.Octets.of_list(B.append(hdr, B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.Octets.to_list(su))))), rest)) : {B.append(B.mask(hdr), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))) == _ : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.append(hdr, B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.Octets.to_list(su)))))), B.mask(B.append(hdr, B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.Octets.to_list(su))))), BL.octets_to_of(B.append(hdr, B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.Octets.to_list(su)))))) : {B.append(B.mask(hdr), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))) == B.append(_, B.Octets.to_list(rest)) : List<&2, U32>}
  %mask_append(hdr, B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.Octets.to_list(su)))) : {B.append(B.mask(hdr), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))) == B.append(_, B.Octets.to_list(rest)) : List<&2, U32>}
  %mask_append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.Octets.to_list(su))) : {B.append(B.mask(hdr), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))) == B.append(B.append(B.mask(hdr), _), B.Octets.to_list(rest)) : List<&2, U32>}
  %mask_append(B.zeros(R.iso.pad(R.iso.olen(id))), B.Octets.to_list(su)) : {B.append(B.mask(hdr), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))) == B.append(B.append(B.mask(hdr), B.append(B.mask(B.Octets.to_list(id)), _)), B.Octets.to_list(rest)) : List<&2, U32>}
  %mask_octets(id) : {B.append(B.mask(hdr), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))) == B.append(B.append(B.mask(hdr), B.append(_, B.append(B.mask(B.zeros(R.iso.pad(R.iso.olen(id)))), B.mask(B.Octets.to_list(su))))), B.Octets.to_list(rest)) : List<&2, U32>}
  %mask_zeros(R.iso.pad(R.iso.olen(id))) : {B.append(B.mask(hdr), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))) == B.append(B.append(B.mask(hdr), B.append(B.Octets.to_list(id), B.append(_, B.mask(B.Octets.to_list(su))))), B.Octets.to_list(rest)) : List<&2, U32>}
  %mask_octets(su) : {B.append(B.mask(hdr), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))) == B.append(B.append(B.mask(hdr), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), _))), B.Octets.to_list(rest)) : List<&2, U32>}
  %append_assoc(B.mask(hdr), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.Octets.to_list(su))), B.Octets.to_list(rest)) : {B.append(B.mask(hdr), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))) == _ : List<&2, U32>}
  %append_assoc(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.Octets.to_list(su)), B.Octets.to_list(rest)) : {B.append(B.mask(hdr), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))) == B.append(B.mask(hdr), _) : List<&2, U32>}
  %append_assoc(B.zeros(R.iso.pad(R.iso.olen(id))), B.Octets.to_list(su), B.Octets.to_list(rest)) : {B.append(B.mask(hdr), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))) == B.append(B.mask(hdr), B.append(B.Octets.to_list(id), _)) : List<&2, U32>}
  {==}

def dirrec_main(+ea: U32, +we: Word(32n), +ws: Word(32n), +dt: F.IsoDirDate, +fl: U32, +us: U32, +gp: U32, +wv: Word(32n), +id: B.Octets, +su: B.Octets, +rest: B.Octets, h1: {Nat.is_le(1n, R.iso.olen(id)) == True{} : Bool}, +h2: {Nat.is_lt(Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)), 256n) == True{} : Bool}) -> {R.IsoDirRec.decode(F.IsoEndianCheck{}, B.Octets.append(R.IsoDirRec.encode(R.IsoDirRec{ea, U32{we}, U32{ws}, dt, fl, us, gp, U32{wv}, id, su}), rest)) == Done{R.IsoDirRec.norm(R.IsoDirRec{ea, U32{we}, U32{ws}, dt, fl, us, gp, U32{wv}, id, su})} : Result<&2, &2, F.IsoError, R.IsoDirRec>}:
  match dt:
    case F.IsoDirDate{+y, +mo, +dd, +hh, +mi, +se, +of}:
      %bytes_lemma(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id)), id, su, rest) : {R.iso.dirrec.list(F.IsoEndianCheck{}, _) == Done{R.IsoDirRec.norm(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su})} : Result<&2, &2, F.IsoError, R.IsoDirRec>}
      %both32_lemma(U32{we}, B.drop(10n, R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest)))), 2n) : {R.iso.dirrec.build(R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 1n), _, F.iso.both32.list(F.IsoEndianCheck{}, B.drop(10n, B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest)))))), 10n), F.iso.dirdate.list(B.drop(18n, B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))))), R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 25n), R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 26n), R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 27n), F.iso.both16.list(F.IsoEndianCheck{}, B.drop(28n, B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest)))))), 28n), R.iso.dirrec.tail.m(R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 0n), R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 32n), B.drop(33n, B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest)))))))) == Done{R.IsoDirRec.norm(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su})} : Result<&2, &2, F.IsoError, R.IsoDirRec>}
      %both32_lemma(U32{ws}, B.drop(18n, R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest)))), 10n) : {R.iso.dirrec.build(R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 1n), Done{U32{we}}, _, F.iso.dirdate.list(B.drop(18n, B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))))), R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 25n), R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 26n), R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 27n), F.iso.both16.list(F.IsoEndianCheck{}, B.drop(28n, B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest)))))), 28n), R.iso.dirrec.tail.m(R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 0n), R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 32n), B.drop(33n, B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest)))))))) == Done{R.IsoDirRec.norm(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su})} : Result<&2, &2, F.IsoError, R.IsoDirRec>}
      %both16_lemma(U32{wv}, B.drop(32n, R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest)))), 28n) : {R.iso.dirrec.build(R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 1n), Done{U32{we}}, Done{U32{ws}}, F.iso.dirdate.list(B.drop(18n, B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))))), R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 25n), R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 26n), R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 27n), _, R.iso.dirrec.tail.m(R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 0n), R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 32n), B.drop(33n, B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest)))))))) == Done{R.IsoDirRec.norm(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su})} : Result<&2, &2, F.IsoError, R.IsoDirRec>}
      %tail_lemma(id, su, B.Octets.to_list(rest), h1, h2) : {R.iso.dirrec.build(R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 1n), Done{U32{we}}, Done{U32{ws}}, F.iso.dirdate.list(B.drop(18n, B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))))), R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 25n), R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 26n), R.iso.at(B.append(B.mask(R.iso.dirrec.header(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}, R.IsoDirRec.length(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su}), R.iso.olen(id))), B.append(B.Octets.to_list(id), B.append(B.zeros(R.iso.pad(R.iso.olen(id))), B.append(B.Octets.to_list(su), B.Octets.to_list(rest))))), 27n), Done{B.low16(U32{wv})}, _) == Done{R.IsoDirRec.norm(R.IsoDirRec{ea, U32{we}, U32{ws}, F.IsoDirDate{y, mo, dd, hh, mi, se, of}, fl, us, gp, U32{wv}, id, su})} : Result<&2, &2, F.IsoError, R.IsoDirRec>}
      {==}

def Laws.dirrec_round_trip(r, rest, h):
  match r:
    case R.IsoDirRec{+ea, U32{+we}, U32{+ws}, +dt, +fl, +us, +gp, U32{+wv}, +id, +su}:
      +h0 = h
      dirrec_main(ea, we, ws, dt, fl, us, gp, wv, id, su, rest, and_l(Nat.is_le(1n, R.iso.olen(id)), Nat.is_lt(Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)), 256n), h0), and_r(Nat.is_le(1n, R.iso.olen(id)), Nat.is_lt(Nat.add(R.iso.fixed(R.iso.olen(id)), R.iso.olen(su)), 256n), h0))

def Laws.gi_root_record():
  {==}

def Laws.gi_file_record():
  {==}

def Laws.gi_file_rr_name():
  {==}

def Laws.gi_creation_date():
  {==}
