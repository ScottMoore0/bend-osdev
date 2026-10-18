# The proofs of LAWS.bend.
#
# Octets enter only through bytes' interface laws (octets_to_of,
# octets_of_to, octets_len_list, octets_of_list_idempotent); the list layer's
# mask and byte are computed through. Each stage's fast (tail-recursive)
# form is proved equal to its structural form, which the round trips follow.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./list.bend as L
import ./error.bend as E
import ./rle.bend as R
import ./mtf.bend as M
import ./bwt.bend as W
import ./stream.bend as S
import ./bzip2.bend as Z
import ./LAWS.bend as Laws

# Bytes: masking twice is masking once (B.byte reads only the low 8 bits)
def byte_idem(b: U32) -> {B.byte(b) == B.byte(B.byte(b)) : U32}:
  match b:
    case U32{WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, hi}}}}}}}}}:
      {==}

# The output bound: decompression ends with a guard that refuses any output
# longer than the maximum. e says which way the guard went.
def bound_pick(+max: U32, +o: B.Octets, b: Bool, +e: {b == Nat.is_le(B.Octets.len(o), U32.to_nat(max)) : Bool}) -> {Laws.bzip2_within(max, S.stm.bound.pick(Nat.is_le(B.Octets.len(o), U32.to_nat(max)), o)) == True{} : Bool}:
  match b:
    case True{}:
      %e : {Laws.bzip2_within(max, S.stm.bound.pick(_, o)) == True{} : Bool}
      %e : {_ == True{} : Bool}
      {==}
    case False{}:
      %e : {Laws.bzip2_within(max, S.stm.bound.pick(_, o)) == True{} : Bool}
      {==}

def bound_ok(+max: U32, r: Result<&2, &2, E.Bzip2Error, B.Octets>) -> {Laws.bzip2_within(max, S.stm.bound(max, r)) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{+o}:
      bound_pick(max, o, Nat.is_le(B.Octets.len(o), U32.to_nat(max)), {==})

def Laws.output_bounded(opts, src):
  match opts:
    case S.Bzip2Options{+max, ignore}:
      +xs = B.Octets.to_list(src)
      bound_ok(max, S.dec.result(S.dec.go(1n+1n+L.bz.len(xs), S.Bzip2DecHead{xs, True{}, U32.to_nat(max), Nil{}}, ignore)))

def Laws.empty_input(opts):
  match opts:
    case S.Bzip2Options{+max, ignore}:
      {==}


# Absurdities

def absurd.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def absurd.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : absurd.bool(_)
  Unit{}

def absurd.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : absurd.bool(_)
  Unit{}

# not b is True: b is False
def not_true(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {False{} == b : Bool}:
  match b:
    case True{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))
    case False{}:
      {==}

# Words: is_eq is equality

def bool_cmp_self(b: Bool) -> {Bool.cmp(b, b) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def word_cmp_self(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+b, t}:
          Equal.trans(Cmp, Word.cmp.fin(b, b, Word.cmp(p, t, t)), Word.cmp.fin(b, b, EQ{}), EQ{}, Equal.cong(Cmp, Cmp, x => Word.cmp.fin(b, b, x), Word.cmp(p, t, t), EQ{}, word_cmp_self(p, t)), bool_cmp_self(b))

def u32_eq_self(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{+w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, word_cmp_self(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# rewriting form: is_eq(a, a) becomes True
def u32_eq_self_r(+a: U32) -> {True{} == U32.is_eq(a, a) : Bool}:
  Equal.sym(Bool, U32.is_eq(a, a), True{}, u32_eq_self(a))

def word.eq_tail(c: Cmp, x: Bool, y: Bool, e: {Cmp.is_eq(Word.cmp.fin(x, y, c)) == True{} : Bool}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))

def word.eq_head(c: Cmp, x: Bool, y: Bool, e: {Cmp.is_eq(Word.cmp.fin(x, y, c)) == True{} : Bool}) -> {x == y : Bool}:
  match c:
    case LT{}:
      Empty.absurd({x == y : Bool}, absurd.ft(e))
    case EQ{}:
      match x y:
        case True{} True{}:
          {==}
        case False{} False{}:
          {==}
        case True{} False{}:
          Empty.absurd({True{} == False{} : Bool}, absurd.ft(e))
        case False{} True{}:
          Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))
    case GT{}:
      Empty.absurd({x == y : Bool}, absurd.ft(e))

def word.eq(n: Nat, a: Word(n), b: Word(n), e: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          +e2 = e
          %word.eq(p, at, bt, word.eq_tail(Word.cmp(p, at, bt), x, y, e2)) : {WCon{x, at} == WCon{y, _} : Word(1n+p)}
          %word.eq_head(Word.cmp(p, at, bt), x, y, e2) : {WCon{x, at} == WCon{_, at} : Word(1n+p)}
          {==}

# is_eq(a, b) is True: a is b
def u32_eq(a: U32, b: U32, e: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+wa} U32{+wb}:
      %word.eq(32n, wa, wb, e) : {U32{wa} == U32{_} : U32}
      {==}

# Nat: a < b + 1 is a <= b
def nat_lt_succ(a: Nat, b: Nat) -> {Nat.is_lt(a, 1n+b) == Nat.is_le(a, b) : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      match p:
        case 0n:
          match b:
            case 0n:
              {==}
            case 1n+q:
              match q:
                case 0n:
                  {==}
                case 1n+u:
                  {==}
        case 1n+r:
          match b:
            case 0n:
              {==}
            case 1n+q:
              nat_lt_succ(1n+r, q)

# Lists

def app_nil(xs: List<&2, U32>) -> {L.bz.app(xs, Nil{}) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, x => Con{h, x}, L.bz.app(t, Nil{}), t, app_nil(t))

def rep_snoc(n: Nat, +h: U32, +z: List<&2, U32>) -> {L.bz.app(L.bz.rep(n, h), Con{h, z}) == Con{h, L.bz.app(L.bz.rep(n, h), z)} : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(List<&2, U32>, List<&2, U32>, x => Con{h, x}, L.bz.app(L.bz.rep(p, h), Con{h, z}), Con{h, L.bz.app(L.bz.rep(p, h), z)}, rep_snoc(p, h, z))

# pushing e onto acc, then all onto ys, is acc onto e ++ ys
def push_push(e: List<&2, U32>, acc: List<&2, U32>, ys: List<&2, U32>) -> {L.bz.push(L.bz.push(e, acc), ys) == L.bz.push(acc, L.bz.app(e, ys)) : List<&2, U32>}:
  match e:
    case Nil{}:
      {==}
    case Con{h, t}:
      push_push(t, Con{h, acc}, ys)

# the reverse of e pushed onto acc: acc onto e
def rev_push(+e: List<&2, U32>, +acc: List<&2, U32>) -> {L.bz.rev(L.bz.push(e, acc)) == L.bz.push(acc, e) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, L.bz.push(L.bz.push(e, acc), Nil{}), L.bz.push(acc, L.bz.app(e, Nil{})), L.bz.push(acc, e), push_push(e, acc, Nil{}), Equal.cong(List<&2, U32>, List<&2, U32>, x => L.bz.push(acc, x), L.bz.app(e, Nil{}), e, app_nil(e)))

# Small numbers: U32.from_nat and back (and B.byte) give a small Nat back.
# One def per value, generated (ref: none; scratchpad gensmall.py).

def small.k251(j: Nat, e: {Nat.is_le(j, 0n) == True{} : Bool}) -> {Nat.add(251n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(251n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({Nat.add(251n, 1n+p) == U32.to_nat(B.byte(U32.from_nat(Nat.add(251n, 1n+p)))) : Nat}, absurd.ft(e))

def small.k250(j: Nat, e: {Nat.is_le(j, 1n) == True{} : Bool}) -> {Nat.add(250n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(250n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k251(p, e)

def small.k249(j: Nat, e: {Nat.is_le(j, 2n) == True{} : Bool}) -> {Nat.add(249n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(249n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k250(p, e)

def small.k248(j: Nat, e: {Nat.is_le(j, 3n) == True{} : Bool}) -> {Nat.add(248n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(248n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k249(p, e)

def small.k247(j: Nat, e: {Nat.is_le(j, 4n) == True{} : Bool}) -> {Nat.add(247n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(247n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k248(p, e)

def small.k246(j: Nat, e: {Nat.is_le(j, 5n) == True{} : Bool}) -> {Nat.add(246n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(246n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k247(p, e)

def small.k245(j: Nat, e: {Nat.is_le(j, 6n) == True{} : Bool}) -> {Nat.add(245n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(245n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k246(p, e)

def small.k244(j: Nat, e: {Nat.is_le(j, 7n) == True{} : Bool}) -> {Nat.add(244n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(244n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k245(p, e)

def small.k243(j: Nat, e: {Nat.is_le(j, 8n) == True{} : Bool}) -> {Nat.add(243n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(243n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k244(p, e)

def small.k242(j: Nat, e: {Nat.is_le(j, 9n) == True{} : Bool}) -> {Nat.add(242n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(242n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k243(p, e)

def small.k241(j: Nat, e: {Nat.is_le(j, 10n) == True{} : Bool}) -> {Nat.add(241n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(241n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k242(p, e)

def small.k240(j: Nat, e: {Nat.is_le(j, 11n) == True{} : Bool}) -> {Nat.add(240n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(240n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k241(p, e)

def small.k239(j: Nat, e: {Nat.is_le(j, 12n) == True{} : Bool}) -> {Nat.add(239n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(239n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k240(p, e)

def small.k238(j: Nat, e: {Nat.is_le(j, 13n) == True{} : Bool}) -> {Nat.add(238n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(238n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k239(p, e)

def small.k237(j: Nat, e: {Nat.is_le(j, 14n) == True{} : Bool}) -> {Nat.add(237n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(237n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k238(p, e)

def small.k236(j: Nat, e: {Nat.is_le(j, 15n) == True{} : Bool}) -> {Nat.add(236n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(236n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k237(p, e)

def small.k235(j: Nat, e: {Nat.is_le(j, 16n) == True{} : Bool}) -> {Nat.add(235n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(235n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k236(p, e)

def small.k234(j: Nat, e: {Nat.is_le(j, 17n) == True{} : Bool}) -> {Nat.add(234n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(234n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k235(p, e)

def small.k233(j: Nat, e: {Nat.is_le(j, 18n) == True{} : Bool}) -> {Nat.add(233n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(233n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k234(p, e)

def small.k232(j: Nat, e: {Nat.is_le(j, 19n) == True{} : Bool}) -> {Nat.add(232n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(232n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k233(p, e)

def small.k231(j: Nat, e: {Nat.is_le(j, 20n) == True{} : Bool}) -> {Nat.add(231n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(231n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k232(p, e)

def small.k230(j: Nat, e: {Nat.is_le(j, 21n) == True{} : Bool}) -> {Nat.add(230n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(230n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k231(p, e)

def small.k229(j: Nat, e: {Nat.is_le(j, 22n) == True{} : Bool}) -> {Nat.add(229n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(229n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k230(p, e)

def small.k228(j: Nat, e: {Nat.is_le(j, 23n) == True{} : Bool}) -> {Nat.add(228n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(228n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k229(p, e)

def small.k227(j: Nat, e: {Nat.is_le(j, 24n) == True{} : Bool}) -> {Nat.add(227n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(227n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k228(p, e)

def small.k226(j: Nat, e: {Nat.is_le(j, 25n) == True{} : Bool}) -> {Nat.add(226n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(226n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k227(p, e)

def small.k225(j: Nat, e: {Nat.is_le(j, 26n) == True{} : Bool}) -> {Nat.add(225n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(225n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k226(p, e)

def small.k224(j: Nat, e: {Nat.is_le(j, 27n) == True{} : Bool}) -> {Nat.add(224n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(224n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k225(p, e)

def small.k223(j: Nat, e: {Nat.is_le(j, 28n) == True{} : Bool}) -> {Nat.add(223n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(223n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k224(p, e)

def small.k222(j: Nat, e: {Nat.is_le(j, 29n) == True{} : Bool}) -> {Nat.add(222n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(222n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k223(p, e)

def small.k221(j: Nat, e: {Nat.is_le(j, 30n) == True{} : Bool}) -> {Nat.add(221n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(221n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k222(p, e)

def small.k220(j: Nat, e: {Nat.is_le(j, 31n) == True{} : Bool}) -> {Nat.add(220n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(220n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k221(p, e)

def small.k219(j: Nat, e: {Nat.is_le(j, 32n) == True{} : Bool}) -> {Nat.add(219n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(219n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k220(p, e)

def small.k218(j: Nat, e: {Nat.is_le(j, 33n) == True{} : Bool}) -> {Nat.add(218n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(218n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k219(p, e)

def small.k217(j: Nat, e: {Nat.is_le(j, 34n) == True{} : Bool}) -> {Nat.add(217n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(217n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k218(p, e)

def small.k216(j: Nat, e: {Nat.is_le(j, 35n) == True{} : Bool}) -> {Nat.add(216n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(216n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k217(p, e)

def small.k215(j: Nat, e: {Nat.is_le(j, 36n) == True{} : Bool}) -> {Nat.add(215n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(215n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k216(p, e)

def small.k214(j: Nat, e: {Nat.is_le(j, 37n) == True{} : Bool}) -> {Nat.add(214n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(214n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k215(p, e)

def small.k213(j: Nat, e: {Nat.is_le(j, 38n) == True{} : Bool}) -> {Nat.add(213n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(213n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k214(p, e)

def small.k212(j: Nat, e: {Nat.is_le(j, 39n) == True{} : Bool}) -> {Nat.add(212n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(212n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k213(p, e)

def small.k211(j: Nat, e: {Nat.is_le(j, 40n) == True{} : Bool}) -> {Nat.add(211n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(211n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k212(p, e)

def small.k210(j: Nat, e: {Nat.is_le(j, 41n) == True{} : Bool}) -> {Nat.add(210n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(210n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k211(p, e)

def small.k209(j: Nat, e: {Nat.is_le(j, 42n) == True{} : Bool}) -> {Nat.add(209n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(209n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k210(p, e)

def small.k208(j: Nat, e: {Nat.is_le(j, 43n) == True{} : Bool}) -> {Nat.add(208n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(208n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k209(p, e)

def small.k207(j: Nat, e: {Nat.is_le(j, 44n) == True{} : Bool}) -> {Nat.add(207n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(207n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k208(p, e)

def small.k206(j: Nat, e: {Nat.is_le(j, 45n) == True{} : Bool}) -> {Nat.add(206n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(206n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k207(p, e)

def small.k205(j: Nat, e: {Nat.is_le(j, 46n) == True{} : Bool}) -> {Nat.add(205n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(205n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k206(p, e)

def small.k204(j: Nat, e: {Nat.is_le(j, 47n) == True{} : Bool}) -> {Nat.add(204n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(204n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k205(p, e)

def small.k203(j: Nat, e: {Nat.is_le(j, 48n) == True{} : Bool}) -> {Nat.add(203n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(203n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k204(p, e)

def small.k202(j: Nat, e: {Nat.is_le(j, 49n) == True{} : Bool}) -> {Nat.add(202n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(202n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k203(p, e)

def small.k201(j: Nat, e: {Nat.is_le(j, 50n) == True{} : Bool}) -> {Nat.add(201n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(201n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k202(p, e)

def small.k200(j: Nat, e: {Nat.is_le(j, 51n) == True{} : Bool}) -> {Nat.add(200n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(200n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k201(p, e)

def small.k199(j: Nat, e: {Nat.is_le(j, 52n) == True{} : Bool}) -> {Nat.add(199n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(199n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k200(p, e)

def small.k198(j: Nat, e: {Nat.is_le(j, 53n) == True{} : Bool}) -> {Nat.add(198n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(198n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k199(p, e)

def small.k197(j: Nat, e: {Nat.is_le(j, 54n) == True{} : Bool}) -> {Nat.add(197n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(197n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k198(p, e)

def small.k196(j: Nat, e: {Nat.is_le(j, 55n) == True{} : Bool}) -> {Nat.add(196n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(196n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k197(p, e)

def small.k195(j: Nat, e: {Nat.is_le(j, 56n) == True{} : Bool}) -> {Nat.add(195n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(195n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k196(p, e)

def small.k194(j: Nat, e: {Nat.is_le(j, 57n) == True{} : Bool}) -> {Nat.add(194n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(194n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k195(p, e)

def small.k193(j: Nat, e: {Nat.is_le(j, 58n) == True{} : Bool}) -> {Nat.add(193n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(193n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k194(p, e)

def small.k192(j: Nat, e: {Nat.is_le(j, 59n) == True{} : Bool}) -> {Nat.add(192n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(192n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k193(p, e)

def small.k191(j: Nat, e: {Nat.is_le(j, 60n) == True{} : Bool}) -> {Nat.add(191n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(191n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k192(p, e)

def small.k190(j: Nat, e: {Nat.is_le(j, 61n) == True{} : Bool}) -> {Nat.add(190n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(190n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k191(p, e)

def small.k189(j: Nat, e: {Nat.is_le(j, 62n) == True{} : Bool}) -> {Nat.add(189n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(189n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k190(p, e)

def small.k188(j: Nat, e: {Nat.is_le(j, 63n) == True{} : Bool}) -> {Nat.add(188n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(188n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k189(p, e)

def small.k187(j: Nat, e: {Nat.is_le(j, 64n) == True{} : Bool}) -> {Nat.add(187n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(187n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k188(p, e)

def small.k186(j: Nat, e: {Nat.is_le(j, 65n) == True{} : Bool}) -> {Nat.add(186n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(186n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k187(p, e)

def small.k185(j: Nat, e: {Nat.is_le(j, 66n) == True{} : Bool}) -> {Nat.add(185n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(185n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k186(p, e)

def small.k184(j: Nat, e: {Nat.is_le(j, 67n) == True{} : Bool}) -> {Nat.add(184n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(184n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k185(p, e)

def small.k183(j: Nat, e: {Nat.is_le(j, 68n) == True{} : Bool}) -> {Nat.add(183n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(183n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k184(p, e)

def small.k182(j: Nat, e: {Nat.is_le(j, 69n) == True{} : Bool}) -> {Nat.add(182n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(182n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k183(p, e)

def small.k181(j: Nat, e: {Nat.is_le(j, 70n) == True{} : Bool}) -> {Nat.add(181n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(181n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k182(p, e)

def small.k180(j: Nat, e: {Nat.is_le(j, 71n) == True{} : Bool}) -> {Nat.add(180n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(180n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k181(p, e)

def small.k179(j: Nat, e: {Nat.is_le(j, 72n) == True{} : Bool}) -> {Nat.add(179n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(179n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k180(p, e)

def small.k178(j: Nat, e: {Nat.is_le(j, 73n) == True{} : Bool}) -> {Nat.add(178n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(178n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k179(p, e)

def small.k177(j: Nat, e: {Nat.is_le(j, 74n) == True{} : Bool}) -> {Nat.add(177n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(177n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k178(p, e)

def small.k176(j: Nat, e: {Nat.is_le(j, 75n) == True{} : Bool}) -> {Nat.add(176n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(176n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k177(p, e)

def small.k175(j: Nat, e: {Nat.is_le(j, 76n) == True{} : Bool}) -> {Nat.add(175n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(175n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k176(p, e)

def small.k174(j: Nat, e: {Nat.is_le(j, 77n) == True{} : Bool}) -> {Nat.add(174n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(174n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k175(p, e)

def small.k173(j: Nat, e: {Nat.is_le(j, 78n) == True{} : Bool}) -> {Nat.add(173n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(173n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k174(p, e)

def small.k172(j: Nat, e: {Nat.is_le(j, 79n) == True{} : Bool}) -> {Nat.add(172n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(172n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k173(p, e)

def small.k171(j: Nat, e: {Nat.is_le(j, 80n) == True{} : Bool}) -> {Nat.add(171n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(171n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k172(p, e)

def small.k170(j: Nat, e: {Nat.is_le(j, 81n) == True{} : Bool}) -> {Nat.add(170n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(170n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k171(p, e)

def small.k169(j: Nat, e: {Nat.is_le(j, 82n) == True{} : Bool}) -> {Nat.add(169n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(169n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k170(p, e)

def small.k168(j: Nat, e: {Nat.is_le(j, 83n) == True{} : Bool}) -> {Nat.add(168n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(168n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k169(p, e)

def small.k167(j: Nat, e: {Nat.is_le(j, 84n) == True{} : Bool}) -> {Nat.add(167n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(167n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k168(p, e)

def small.k166(j: Nat, e: {Nat.is_le(j, 85n) == True{} : Bool}) -> {Nat.add(166n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(166n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k167(p, e)

def small.k165(j: Nat, e: {Nat.is_le(j, 86n) == True{} : Bool}) -> {Nat.add(165n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(165n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k166(p, e)

def small.k164(j: Nat, e: {Nat.is_le(j, 87n) == True{} : Bool}) -> {Nat.add(164n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(164n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k165(p, e)

def small.k163(j: Nat, e: {Nat.is_le(j, 88n) == True{} : Bool}) -> {Nat.add(163n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(163n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k164(p, e)

def small.k162(j: Nat, e: {Nat.is_le(j, 89n) == True{} : Bool}) -> {Nat.add(162n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(162n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k163(p, e)

def small.k161(j: Nat, e: {Nat.is_le(j, 90n) == True{} : Bool}) -> {Nat.add(161n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(161n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k162(p, e)

def small.k160(j: Nat, e: {Nat.is_le(j, 91n) == True{} : Bool}) -> {Nat.add(160n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(160n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k161(p, e)

def small.k159(j: Nat, e: {Nat.is_le(j, 92n) == True{} : Bool}) -> {Nat.add(159n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(159n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k160(p, e)

def small.k158(j: Nat, e: {Nat.is_le(j, 93n) == True{} : Bool}) -> {Nat.add(158n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(158n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k159(p, e)

def small.k157(j: Nat, e: {Nat.is_le(j, 94n) == True{} : Bool}) -> {Nat.add(157n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(157n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k158(p, e)

def small.k156(j: Nat, e: {Nat.is_le(j, 95n) == True{} : Bool}) -> {Nat.add(156n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(156n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k157(p, e)

def small.k155(j: Nat, e: {Nat.is_le(j, 96n) == True{} : Bool}) -> {Nat.add(155n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(155n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k156(p, e)

def small.k154(j: Nat, e: {Nat.is_le(j, 97n) == True{} : Bool}) -> {Nat.add(154n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(154n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k155(p, e)

def small.k153(j: Nat, e: {Nat.is_le(j, 98n) == True{} : Bool}) -> {Nat.add(153n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(153n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k154(p, e)

def small.k152(j: Nat, e: {Nat.is_le(j, 99n) == True{} : Bool}) -> {Nat.add(152n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(152n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k153(p, e)

def small.k151(j: Nat, e: {Nat.is_le(j, 100n) == True{} : Bool}) -> {Nat.add(151n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(151n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k152(p, e)

def small.k150(j: Nat, e: {Nat.is_le(j, 101n) == True{} : Bool}) -> {Nat.add(150n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(150n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k151(p, e)

def small.k149(j: Nat, e: {Nat.is_le(j, 102n) == True{} : Bool}) -> {Nat.add(149n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(149n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k150(p, e)

def small.k148(j: Nat, e: {Nat.is_le(j, 103n) == True{} : Bool}) -> {Nat.add(148n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(148n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k149(p, e)

def small.k147(j: Nat, e: {Nat.is_le(j, 104n) == True{} : Bool}) -> {Nat.add(147n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(147n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k148(p, e)

def small.k146(j: Nat, e: {Nat.is_le(j, 105n) == True{} : Bool}) -> {Nat.add(146n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(146n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k147(p, e)

def small.k145(j: Nat, e: {Nat.is_le(j, 106n) == True{} : Bool}) -> {Nat.add(145n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(145n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k146(p, e)

def small.k144(j: Nat, e: {Nat.is_le(j, 107n) == True{} : Bool}) -> {Nat.add(144n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(144n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k145(p, e)

def small.k143(j: Nat, e: {Nat.is_le(j, 108n) == True{} : Bool}) -> {Nat.add(143n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(143n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k144(p, e)

def small.k142(j: Nat, e: {Nat.is_le(j, 109n) == True{} : Bool}) -> {Nat.add(142n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(142n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k143(p, e)

def small.k141(j: Nat, e: {Nat.is_le(j, 110n) == True{} : Bool}) -> {Nat.add(141n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(141n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k142(p, e)

def small.k140(j: Nat, e: {Nat.is_le(j, 111n) == True{} : Bool}) -> {Nat.add(140n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(140n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k141(p, e)

def small.k139(j: Nat, e: {Nat.is_le(j, 112n) == True{} : Bool}) -> {Nat.add(139n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(139n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k140(p, e)

def small.k138(j: Nat, e: {Nat.is_le(j, 113n) == True{} : Bool}) -> {Nat.add(138n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(138n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k139(p, e)

def small.k137(j: Nat, e: {Nat.is_le(j, 114n) == True{} : Bool}) -> {Nat.add(137n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(137n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k138(p, e)

def small.k136(j: Nat, e: {Nat.is_le(j, 115n) == True{} : Bool}) -> {Nat.add(136n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(136n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k137(p, e)

def small.k135(j: Nat, e: {Nat.is_le(j, 116n) == True{} : Bool}) -> {Nat.add(135n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(135n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k136(p, e)

def small.k134(j: Nat, e: {Nat.is_le(j, 117n) == True{} : Bool}) -> {Nat.add(134n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(134n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k135(p, e)

def small.k133(j: Nat, e: {Nat.is_le(j, 118n) == True{} : Bool}) -> {Nat.add(133n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(133n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k134(p, e)

def small.k132(j: Nat, e: {Nat.is_le(j, 119n) == True{} : Bool}) -> {Nat.add(132n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(132n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k133(p, e)

def small.k131(j: Nat, e: {Nat.is_le(j, 120n) == True{} : Bool}) -> {Nat.add(131n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(131n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k132(p, e)

def small.k130(j: Nat, e: {Nat.is_le(j, 121n) == True{} : Bool}) -> {Nat.add(130n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(130n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k131(p, e)

def small.k129(j: Nat, e: {Nat.is_le(j, 122n) == True{} : Bool}) -> {Nat.add(129n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(129n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k130(p, e)

def small.k128(j: Nat, e: {Nat.is_le(j, 123n) == True{} : Bool}) -> {Nat.add(128n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(128n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k129(p, e)

def small.k127(j: Nat, e: {Nat.is_le(j, 124n) == True{} : Bool}) -> {Nat.add(127n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(127n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k128(p, e)

def small.k126(j: Nat, e: {Nat.is_le(j, 125n) == True{} : Bool}) -> {Nat.add(126n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(126n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k127(p, e)

def small.k125(j: Nat, e: {Nat.is_le(j, 126n) == True{} : Bool}) -> {Nat.add(125n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(125n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k126(p, e)

def small.k124(j: Nat, e: {Nat.is_le(j, 127n) == True{} : Bool}) -> {Nat.add(124n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(124n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k125(p, e)

def small.k123(j: Nat, e: {Nat.is_le(j, 128n) == True{} : Bool}) -> {Nat.add(123n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(123n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k124(p, e)

def small.k122(j: Nat, e: {Nat.is_le(j, 129n) == True{} : Bool}) -> {Nat.add(122n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(122n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k123(p, e)

def small.k121(j: Nat, e: {Nat.is_le(j, 130n) == True{} : Bool}) -> {Nat.add(121n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(121n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k122(p, e)

def small.k120(j: Nat, e: {Nat.is_le(j, 131n) == True{} : Bool}) -> {Nat.add(120n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(120n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k121(p, e)

def small.k119(j: Nat, e: {Nat.is_le(j, 132n) == True{} : Bool}) -> {Nat.add(119n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(119n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k120(p, e)

def small.k118(j: Nat, e: {Nat.is_le(j, 133n) == True{} : Bool}) -> {Nat.add(118n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(118n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k119(p, e)

def small.k117(j: Nat, e: {Nat.is_le(j, 134n) == True{} : Bool}) -> {Nat.add(117n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(117n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k118(p, e)

def small.k116(j: Nat, e: {Nat.is_le(j, 135n) == True{} : Bool}) -> {Nat.add(116n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(116n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k117(p, e)

def small.k115(j: Nat, e: {Nat.is_le(j, 136n) == True{} : Bool}) -> {Nat.add(115n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(115n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k116(p, e)

def small.k114(j: Nat, e: {Nat.is_le(j, 137n) == True{} : Bool}) -> {Nat.add(114n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(114n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k115(p, e)

def small.k113(j: Nat, e: {Nat.is_le(j, 138n) == True{} : Bool}) -> {Nat.add(113n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(113n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k114(p, e)

def small.k112(j: Nat, e: {Nat.is_le(j, 139n) == True{} : Bool}) -> {Nat.add(112n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(112n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k113(p, e)

def small.k111(j: Nat, e: {Nat.is_le(j, 140n) == True{} : Bool}) -> {Nat.add(111n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(111n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k112(p, e)

def small.k110(j: Nat, e: {Nat.is_le(j, 141n) == True{} : Bool}) -> {Nat.add(110n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(110n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k111(p, e)

def small.k109(j: Nat, e: {Nat.is_le(j, 142n) == True{} : Bool}) -> {Nat.add(109n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(109n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k110(p, e)

def small.k108(j: Nat, e: {Nat.is_le(j, 143n) == True{} : Bool}) -> {Nat.add(108n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(108n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k109(p, e)

def small.k107(j: Nat, e: {Nat.is_le(j, 144n) == True{} : Bool}) -> {Nat.add(107n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(107n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k108(p, e)

def small.k106(j: Nat, e: {Nat.is_le(j, 145n) == True{} : Bool}) -> {Nat.add(106n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(106n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k107(p, e)

def small.k105(j: Nat, e: {Nat.is_le(j, 146n) == True{} : Bool}) -> {Nat.add(105n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(105n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k106(p, e)

def small.k104(j: Nat, e: {Nat.is_le(j, 147n) == True{} : Bool}) -> {Nat.add(104n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(104n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k105(p, e)

def small.k103(j: Nat, e: {Nat.is_le(j, 148n) == True{} : Bool}) -> {Nat.add(103n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(103n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k104(p, e)

def small.k102(j: Nat, e: {Nat.is_le(j, 149n) == True{} : Bool}) -> {Nat.add(102n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(102n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k103(p, e)

def small.k101(j: Nat, e: {Nat.is_le(j, 150n) == True{} : Bool}) -> {Nat.add(101n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(101n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k102(p, e)

def small.k100(j: Nat, e: {Nat.is_le(j, 151n) == True{} : Bool}) -> {Nat.add(100n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(100n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k101(p, e)

def small.k99(j: Nat, e: {Nat.is_le(j, 152n) == True{} : Bool}) -> {Nat.add(99n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(99n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k100(p, e)

def small.k98(j: Nat, e: {Nat.is_le(j, 153n) == True{} : Bool}) -> {Nat.add(98n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(98n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k99(p, e)

def small.k97(j: Nat, e: {Nat.is_le(j, 154n) == True{} : Bool}) -> {Nat.add(97n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(97n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k98(p, e)

def small.k96(j: Nat, e: {Nat.is_le(j, 155n) == True{} : Bool}) -> {Nat.add(96n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(96n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k97(p, e)

def small.k95(j: Nat, e: {Nat.is_le(j, 156n) == True{} : Bool}) -> {Nat.add(95n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(95n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k96(p, e)

def small.k94(j: Nat, e: {Nat.is_le(j, 157n) == True{} : Bool}) -> {Nat.add(94n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(94n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k95(p, e)

def small.k93(j: Nat, e: {Nat.is_le(j, 158n) == True{} : Bool}) -> {Nat.add(93n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(93n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k94(p, e)

def small.k92(j: Nat, e: {Nat.is_le(j, 159n) == True{} : Bool}) -> {Nat.add(92n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(92n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k93(p, e)

def small.k91(j: Nat, e: {Nat.is_le(j, 160n) == True{} : Bool}) -> {Nat.add(91n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(91n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k92(p, e)

def small.k90(j: Nat, e: {Nat.is_le(j, 161n) == True{} : Bool}) -> {Nat.add(90n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(90n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k91(p, e)

def small.k89(j: Nat, e: {Nat.is_le(j, 162n) == True{} : Bool}) -> {Nat.add(89n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(89n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k90(p, e)

def small.k88(j: Nat, e: {Nat.is_le(j, 163n) == True{} : Bool}) -> {Nat.add(88n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(88n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k89(p, e)

def small.k87(j: Nat, e: {Nat.is_le(j, 164n) == True{} : Bool}) -> {Nat.add(87n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(87n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k88(p, e)

def small.k86(j: Nat, e: {Nat.is_le(j, 165n) == True{} : Bool}) -> {Nat.add(86n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(86n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k87(p, e)

def small.k85(j: Nat, e: {Nat.is_le(j, 166n) == True{} : Bool}) -> {Nat.add(85n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(85n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k86(p, e)

def small.k84(j: Nat, e: {Nat.is_le(j, 167n) == True{} : Bool}) -> {Nat.add(84n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(84n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k85(p, e)

def small.k83(j: Nat, e: {Nat.is_le(j, 168n) == True{} : Bool}) -> {Nat.add(83n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(83n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k84(p, e)

def small.k82(j: Nat, e: {Nat.is_le(j, 169n) == True{} : Bool}) -> {Nat.add(82n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(82n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k83(p, e)

def small.k81(j: Nat, e: {Nat.is_le(j, 170n) == True{} : Bool}) -> {Nat.add(81n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(81n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k82(p, e)

def small.k80(j: Nat, e: {Nat.is_le(j, 171n) == True{} : Bool}) -> {Nat.add(80n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(80n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k81(p, e)

def small.k79(j: Nat, e: {Nat.is_le(j, 172n) == True{} : Bool}) -> {Nat.add(79n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(79n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k80(p, e)

def small.k78(j: Nat, e: {Nat.is_le(j, 173n) == True{} : Bool}) -> {Nat.add(78n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(78n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k79(p, e)

def small.k77(j: Nat, e: {Nat.is_le(j, 174n) == True{} : Bool}) -> {Nat.add(77n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(77n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k78(p, e)

def small.k76(j: Nat, e: {Nat.is_le(j, 175n) == True{} : Bool}) -> {Nat.add(76n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(76n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k77(p, e)

def small.k75(j: Nat, e: {Nat.is_le(j, 176n) == True{} : Bool}) -> {Nat.add(75n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(75n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k76(p, e)

def small.k74(j: Nat, e: {Nat.is_le(j, 177n) == True{} : Bool}) -> {Nat.add(74n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(74n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k75(p, e)

def small.k73(j: Nat, e: {Nat.is_le(j, 178n) == True{} : Bool}) -> {Nat.add(73n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(73n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k74(p, e)

def small.k72(j: Nat, e: {Nat.is_le(j, 179n) == True{} : Bool}) -> {Nat.add(72n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(72n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k73(p, e)

def small.k71(j: Nat, e: {Nat.is_le(j, 180n) == True{} : Bool}) -> {Nat.add(71n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(71n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k72(p, e)

def small.k70(j: Nat, e: {Nat.is_le(j, 181n) == True{} : Bool}) -> {Nat.add(70n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(70n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k71(p, e)

def small.k69(j: Nat, e: {Nat.is_le(j, 182n) == True{} : Bool}) -> {Nat.add(69n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(69n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k70(p, e)

def small.k68(j: Nat, e: {Nat.is_le(j, 183n) == True{} : Bool}) -> {Nat.add(68n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(68n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k69(p, e)

def small.k67(j: Nat, e: {Nat.is_le(j, 184n) == True{} : Bool}) -> {Nat.add(67n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(67n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k68(p, e)

def small.k66(j: Nat, e: {Nat.is_le(j, 185n) == True{} : Bool}) -> {Nat.add(66n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(66n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k67(p, e)

def small.k65(j: Nat, e: {Nat.is_le(j, 186n) == True{} : Bool}) -> {Nat.add(65n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(65n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k66(p, e)

def small.k64(j: Nat, e: {Nat.is_le(j, 187n) == True{} : Bool}) -> {Nat.add(64n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(64n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k65(p, e)

def small.k63(j: Nat, e: {Nat.is_le(j, 188n) == True{} : Bool}) -> {Nat.add(63n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(63n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k64(p, e)

def small.k62(j: Nat, e: {Nat.is_le(j, 189n) == True{} : Bool}) -> {Nat.add(62n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(62n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k63(p, e)

def small.k61(j: Nat, e: {Nat.is_le(j, 190n) == True{} : Bool}) -> {Nat.add(61n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(61n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k62(p, e)

def small.k60(j: Nat, e: {Nat.is_le(j, 191n) == True{} : Bool}) -> {Nat.add(60n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(60n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k61(p, e)

def small.k59(j: Nat, e: {Nat.is_le(j, 192n) == True{} : Bool}) -> {Nat.add(59n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(59n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k60(p, e)

def small.k58(j: Nat, e: {Nat.is_le(j, 193n) == True{} : Bool}) -> {Nat.add(58n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(58n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k59(p, e)

def small.k57(j: Nat, e: {Nat.is_le(j, 194n) == True{} : Bool}) -> {Nat.add(57n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(57n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k58(p, e)

def small.k56(j: Nat, e: {Nat.is_le(j, 195n) == True{} : Bool}) -> {Nat.add(56n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(56n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k57(p, e)

def small.k55(j: Nat, e: {Nat.is_le(j, 196n) == True{} : Bool}) -> {Nat.add(55n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(55n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k56(p, e)

def small.k54(j: Nat, e: {Nat.is_le(j, 197n) == True{} : Bool}) -> {Nat.add(54n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(54n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k55(p, e)

def small.k53(j: Nat, e: {Nat.is_le(j, 198n) == True{} : Bool}) -> {Nat.add(53n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(53n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k54(p, e)

def small.k52(j: Nat, e: {Nat.is_le(j, 199n) == True{} : Bool}) -> {Nat.add(52n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(52n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k53(p, e)

def small.k51(j: Nat, e: {Nat.is_le(j, 200n) == True{} : Bool}) -> {Nat.add(51n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(51n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k52(p, e)

def small.k50(j: Nat, e: {Nat.is_le(j, 201n) == True{} : Bool}) -> {Nat.add(50n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(50n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k51(p, e)

def small.k49(j: Nat, e: {Nat.is_le(j, 202n) == True{} : Bool}) -> {Nat.add(49n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(49n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k50(p, e)

def small.k48(j: Nat, e: {Nat.is_le(j, 203n) == True{} : Bool}) -> {Nat.add(48n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(48n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k49(p, e)

def small.k47(j: Nat, e: {Nat.is_le(j, 204n) == True{} : Bool}) -> {Nat.add(47n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(47n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k48(p, e)

def small.k46(j: Nat, e: {Nat.is_le(j, 205n) == True{} : Bool}) -> {Nat.add(46n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(46n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k47(p, e)

def small.k45(j: Nat, e: {Nat.is_le(j, 206n) == True{} : Bool}) -> {Nat.add(45n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(45n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k46(p, e)

def small.k44(j: Nat, e: {Nat.is_le(j, 207n) == True{} : Bool}) -> {Nat.add(44n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(44n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k45(p, e)

def small.k43(j: Nat, e: {Nat.is_le(j, 208n) == True{} : Bool}) -> {Nat.add(43n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(43n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k44(p, e)

def small.k42(j: Nat, e: {Nat.is_le(j, 209n) == True{} : Bool}) -> {Nat.add(42n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(42n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k43(p, e)

def small.k41(j: Nat, e: {Nat.is_le(j, 210n) == True{} : Bool}) -> {Nat.add(41n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(41n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k42(p, e)

def small.k40(j: Nat, e: {Nat.is_le(j, 211n) == True{} : Bool}) -> {Nat.add(40n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(40n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k41(p, e)

def small.k39(j: Nat, e: {Nat.is_le(j, 212n) == True{} : Bool}) -> {Nat.add(39n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(39n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k40(p, e)

def small.k38(j: Nat, e: {Nat.is_le(j, 213n) == True{} : Bool}) -> {Nat.add(38n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(38n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k39(p, e)

def small.k37(j: Nat, e: {Nat.is_le(j, 214n) == True{} : Bool}) -> {Nat.add(37n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(37n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k38(p, e)

def small.k36(j: Nat, e: {Nat.is_le(j, 215n) == True{} : Bool}) -> {Nat.add(36n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(36n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k37(p, e)

def small.k35(j: Nat, e: {Nat.is_le(j, 216n) == True{} : Bool}) -> {Nat.add(35n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(35n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k36(p, e)

def small.k34(j: Nat, e: {Nat.is_le(j, 217n) == True{} : Bool}) -> {Nat.add(34n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(34n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k35(p, e)

def small.k33(j: Nat, e: {Nat.is_le(j, 218n) == True{} : Bool}) -> {Nat.add(33n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(33n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k34(p, e)

def small.k32(j: Nat, e: {Nat.is_le(j, 219n) == True{} : Bool}) -> {Nat.add(32n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(32n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k33(p, e)

def small.k31(j: Nat, e: {Nat.is_le(j, 220n) == True{} : Bool}) -> {Nat.add(31n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(31n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k32(p, e)

def small.k30(j: Nat, e: {Nat.is_le(j, 221n) == True{} : Bool}) -> {Nat.add(30n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(30n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k31(p, e)

def small.k29(j: Nat, e: {Nat.is_le(j, 222n) == True{} : Bool}) -> {Nat.add(29n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(29n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k30(p, e)

def small.k28(j: Nat, e: {Nat.is_le(j, 223n) == True{} : Bool}) -> {Nat.add(28n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(28n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k29(p, e)

def small.k27(j: Nat, e: {Nat.is_le(j, 224n) == True{} : Bool}) -> {Nat.add(27n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(27n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k28(p, e)

def small.k26(j: Nat, e: {Nat.is_le(j, 225n) == True{} : Bool}) -> {Nat.add(26n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(26n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k27(p, e)

def small.k25(j: Nat, e: {Nat.is_le(j, 226n) == True{} : Bool}) -> {Nat.add(25n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(25n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k26(p, e)

def small.k24(j: Nat, e: {Nat.is_le(j, 227n) == True{} : Bool}) -> {Nat.add(24n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(24n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k25(p, e)

def small.k23(j: Nat, e: {Nat.is_le(j, 228n) == True{} : Bool}) -> {Nat.add(23n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(23n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k24(p, e)

def small.k22(j: Nat, e: {Nat.is_le(j, 229n) == True{} : Bool}) -> {Nat.add(22n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(22n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k23(p, e)

def small.k21(j: Nat, e: {Nat.is_le(j, 230n) == True{} : Bool}) -> {Nat.add(21n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(21n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k22(p, e)

def small.k20(j: Nat, e: {Nat.is_le(j, 231n) == True{} : Bool}) -> {Nat.add(20n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(20n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k21(p, e)

def small.k19(j: Nat, e: {Nat.is_le(j, 232n) == True{} : Bool}) -> {Nat.add(19n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(19n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k20(p, e)

def small.k18(j: Nat, e: {Nat.is_le(j, 233n) == True{} : Bool}) -> {Nat.add(18n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(18n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k19(p, e)

def small.k17(j: Nat, e: {Nat.is_le(j, 234n) == True{} : Bool}) -> {Nat.add(17n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(17n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k18(p, e)

def small.k16(j: Nat, e: {Nat.is_le(j, 235n) == True{} : Bool}) -> {Nat.add(16n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(16n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k17(p, e)

def small.k15(j: Nat, e: {Nat.is_le(j, 236n) == True{} : Bool}) -> {Nat.add(15n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(15n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k16(p, e)

def small.k14(j: Nat, e: {Nat.is_le(j, 237n) == True{} : Bool}) -> {Nat.add(14n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(14n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k15(p, e)

def small.k13(j: Nat, e: {Nat.is_le(j, 238n) == True{} : Bool}) -> {Nat.add(13n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(13n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k14(p, e)

def small.k12(j: Nat, e: {Nat.is_le(j, 239n) == True{} : Bool}) -> {Nat.add(12n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(12n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k13(p, e)

def small.k11(j: Nat, e: {Nat.is_le(j, 240n) == True{} : Bool}) -> {Nat.add(11n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(11n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k12(p, e)

def small.k10(j: Nat, e: {Nat.is_le(j, 241n) == True{} : Bool}) -> {Nat.add(10n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(10n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k11(p, e)

def small.k9(j: Nat, e: {Nat.is_le(j, 242n) == True{} : Bool}) -> {Nat.add(9n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(9n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k10(p, e)

def small.k8(j: Nat, e: {Nat.is_le(j, 243n) == True{} : Bool}) -> {Nat.add(8n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(8n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k9(p, e)

def small.k7(j: Nat, e: {Nat.is_le(j, 244n) == True{} : Bool}) -> {Nat.add(7n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(7n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k8(p, e)

def small.k6(j: Nat, e: {Nat.is_le(j, 245n) == True{} : Bool}) -> {Nat.add(6n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(6n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k7(p, e)

def small.k5(j: Nat, e: {Nat.is_le(j, 246n) == True{} : Bool}) -> {Nat.add(5n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(5n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k6(p, e)

def small.k4(j: Nat, e: {Nat.is_le(j, 247n) == True{} : Bool}) -> {Nat.add(4n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(4n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k5(p, e)

def small.k3(j: Nat, e: {Nat.is_le(j, 248n) == True{} : Bool}) -> {Nat.add(3n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(3n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k4(p, e)

def small.k2(j: Nat, e: {Nat.is_le(j, 249n) == True{} : Bool}) -> {Nat.add(2n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(2n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k3(p, e)

def small.k1(j: Nat, e: {Nat.is_le(j, 250n) == True{} : Bool}) -> {Nat.add(1n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(1n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k2(p, e)

def small.k0(j: Nat, e: {Nat.is_le(j, 251n) == True{} : Bool}) -> {Nat.add(0n, j) == U32.to_nat(B.byte(U32.from_nat(Nat.add(0n, j)))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      small.k1(p, e)

def symn.k256(j: Nat, e: {Nat.is_le(j, 0n) == True{} : Bool}) -> {Nat.add(256n, j) == U32.to_nat(U32.from_nat(Nat.add(256n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({Nat.add(256n, 1n+p) == U32.to_nat(U32.from_nat(Nat.add(256n, 1n+p))) : Nat}, absurd.ft(e))

def symn.k255(j: Nat, e: {Nat.is_le(j, 1n) == True{} : Bool}) -> {Nat.add(255n, j) == U32.to_nat(U32.from_nat(Nat.add(255n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k256(p, e)

def symn.k254(j: Nat, e: {Nat.is_le(j, 2n) == True{} : Bool}) -> {Nat.add(254n, j) == U32.to_nat(U32.from_nat(Nat.add(254n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k255(p, e)

def symn.k253(j: Nat, e: {Nat.is_le(j, 3n) == True{} : Bool}) -> {Nat.add(253n, j) == U32.to_nat(U32.from_nat(Nat.add(253n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k254(p, e)

def symn.k252(j: Nat, e: {Nat.is_le(j, 4n) == True{} : Bool}) -> {Nat.add(252n, j) == U32.to_nat(U32.from_nat(Nat.add(252n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k253(p, e)

def symn.k251(j: Nat, e: {Nat.is_le(j, 5n) == True{} : Bool}) -> {Nat.add(251n, j) == U32.to_nat(U32.from_nat(Nat.add(251n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k252(p, e)

def symn.k250(j: Nat, e: {Nat.is_le(j, 6n) == True{} : Bool}) -> {Nat.add(250n, j) == U32.to_nat(U32.from_nat(Nat.add(250n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k251(p, e)

def symn.k249(j: Nat, e: {Nat.is_le(j, 7n) == True{} : Bool}) -> {Nat.add(249n, j) == U32.to_nat(U32.from_nat(Nat.add(249n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k250(p, e)

def symn.k248(j: Nat, e: {Nat.is_le(j, 8n) == True{} : Bool}) -> {Nat.add(248n, j) == U32.to_nat(U32.from_nat(Nat.add(248n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k249(p, e)

def symn.k247(j: Nat, e: {Nat.is_le(j, 9n) == True{} : Bool}) -> {Nat.add(247n, j) == U32.to_nat(U32.from_nat(Nat.add(247n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k248(p, e)

def symn.k246(j: Nat, e: {Nat.is_le(j, 10n) == True{} : Bool}) -> {Nat.add(246n, j) == U32.to_nat(U32.from_nat(Nat.add(246n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k247(p, e)

def symn.k245(j: Nat, e: {Nat.is_le(j, 11n) == True{} : Bool}) -> {Nat.add(245n, j) == U32.to_nat(U32.from_nat(Nat.add(245n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k246(p, e)

def symn.k244(j: Nat, e: {Nat.is_le(j, 12n) == True{} : Bool}) -> {Nat.add(244n, j) == U32.to_nat(U32.from_nat(Nat.add(244n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k245(p, e)

def symn.k243(j: Nat, e: {Nat.is_le(j, 13n) == True{} : Bool}) -> {Nat.add(243n, j) == U32.to_nat(U32.from_nat(Nat.add(243n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k244(p, e)

def symn.k242(j: Nat, e: {Nat.is_le(j, 14n) == True{} : Bool}) -> {Nat.add(242n, j) == U32.to_nat(U32.from_nat(Nat.add(242n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k243(p, e)

def symn.k241(j: Nat, e: {Nat.is_le(j, 15n) == True{} : Bool}) -> {Nat.add(241n, j) == U32.to_nat(U32.from_nat(Nat.add(241n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k242(p, e)

def symn.k240(j: Nat, e: {Nat.is_le(j, 16n) == True{} : Bool}) -> {Nat.add(240n, j) == U32.to_nat(U32.from_nat(Nat.add(240n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k241(p, e)

def symn.k239(j: Nat, e: {Nat.is_le(j, 17n) == True{} : Bool}) -> {Nat.add(239n, j) == U32.to_nat(U32.from_nat(Nat.add(239n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k240(p, e)

def symn.k238(j: Nat, e: {Nat.is_le(j, 18n) == True{} : Bool}) -> {Nat.add(238n, j) == U32.to_nat(U32.from_nat(Nat.add(238n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k239(p, e)

def symn.k237(j: Nat, e: {Nat.is_le(j, 19n) == True{} : Bool}) -> {Nat.add(237n, j) == U32.to_nat(U32.from_nat(Nat.add(237n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k238(p, e)

def symn.k236(j: Nat, e: {Nat.is_le(j, 20n) == True{} : Bool}) -> {Nat.add(236n, j) == U32.to_nat(U32.from_nat(Nat.add(236n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k237(p, e)

def symn.k235(j: Nat, e: {Nat.is_le(j, 21n) == True{} : Bool}) -> {Nat.add(235n, j) == U32.to_nat(U32.from_nat(Nat.add(235n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k236(p, e)

def symn.k234(j: Nat, e: {Nat.is_le(j, 22n) == True{} : Bool}) -> {Nat.add(234n, j) == U32.to_nat(U32.from_nat(Nat.add(234n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k235(p, e)

def symn.k233(j: Nat, e: {Nat.is_le(j, 23n) == True{} : Bool}) -> {Nat.add(233n, j) == U32.to_nat(U32.from_nat(Nat.add(233n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k234(p, e)

def symn.k232(j: Nat, e: {Nat.is_le(j, 24n) == True{} : Bool}) -> {Nat.add(232n, j) == U32.to_nat(U32.from_nat(Nat.add(232n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k233(p, e)

def symn.k231(j: Nat, e: {Nat.is_le(j, 25n) == True{} : Bool}) -> {Nat.add(231n, j) == U32.to_nat(U32.from_nat(Nat.add(231n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k232(p, e)

def symn.k230(j: Nat, e: {Nat.is_le(j, 26n) == True{} : Bool}) -> {Nat.add(230n, j) == U32.to_nat(U32.from_nat(Nat.add(230n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k231(p, e)

def symn.k229(j: Nat, e: {Nat.is_le(j, 27n) == True{} : Bool}) -> {Nat.add(229n, j) == U32.to_nat(U32.from_nat(Nat.add(229n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k230(p, e)

def symn.k228(j: Nat, e: {Nat.is_le(j, 28n) == True{} : Bool}) -> {Nat.add(228n, j) == U32.to_nat(U32.from_nat(Nat.add(228n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k229(p, e)

def symn.k227(j: Nat, e: {Nat.is_le(j, 29n) == True{} : Bool}) -> {Nat.add(227n, j) == U32.to_nat(U32.from_nat(Nat.add(227n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k228(p, e)

def symn.k226(j: Nat, e: {Nat.is_le(j, 30n) == True{} : Bool}) -> {Nat.add(226n, j) == U32.to_nat(U32.from_nat(Nat.add(226n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k227(p, e)

def symn.k225(j: Nat, e: {Nat.is_le(j, 31n) == True{} : Bool}) -> {Nat.add(225n, j) == U32.to_nat(U32.from_nat(Nat.add(225n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k226(p, e)

def symn.k224(j: Nat, e: {Nat.is_le(j, 32n) == True{} : Bool}) -> {Nat.add(224n, j) == U32.to_nat(U32.from_nat(Nat.add(224n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k225(p, e)

def symn.k223(j: Nat, e: {Nat.is_le(j, 33n) == True{} : Bool}) -> {Nat.add(223n, j) == U32.to_nat(U32.from_nat(Nat.add(223n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k224(p, e)

def symn.k222(j: Nat, e: {Nat.is_le(j, 34n) == True{} : Bool}) -> {Nat.add(222n, j) == U32.to_nat(U32.from_nat(Nat.add(222n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k223(p, e)

def symn.k221(j: Nat, e: {Nat.is_le(j, 35n) == True{} : Bool}) -> {Nat.add(221n, j) == U32.to_nat(U32.from_nat(Nat.add(221n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k222(p, e)

def symn.k220(j: Nat, e: {Nat.is_le(j, 36n) == True{} : Bool}) -> {Nat.add(220n, j) == U32.to_nat(U32.from_nat(Nat.add(220n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k221(p, e)

def symn.k219(j: Nat, e: {Nat.is_le(j, 37n) == True{} : Bool}) -> {Nat.add(219n, j) == U32.to_nat(U32.from_nat(Nat.add(219n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k220(p, e)

def symn.k218(j: Nat, e: {Nat.is_le(j, 38n) == True{} : Bool}) -> {Nat.add(218n, j) == U32.to_nat(U32.from_nat(Nat.add(218n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k219(p, e)

def symn.k217(j: Nat, e: {Nat.is_le(j, 39n) == True{} : Bool}) -> {Nat.add(217n, j) == U32.to_nat(U32.from_nat(Nat.add(217n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k218(p, e)

def symn.k216(j: Nat, e: {Nat.is_le(j, 40n) == True{} : Bool}) -> {Nat.add(216n, j) == U32.to_nat(U32.from_nat(Nat.add(216n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k217(p, e)

def symn.k215(j: Nat, e: {Nat.is_le(j, 41n) == True{} : Bool}) -> {Nat.add(215n, j) == U32.to_nat(U32.from_nat(Nat.add(215n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k216(p, e)

def symn.k214(j: Nat, e: {Nat.is_le(j, 42n) == True{} : Bool}) -> {Nat.add(214n, j) == U32.to_nat(U32.from_nat(Nat.add(214n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k215(p, e)

def symn.k213(j: Nat, e: {Nat.is_le(j, 43n) == True{} : Bool}) -> {Nat.add(213n, j) == U32.to_nat(U32.from_nat(Nat.add(213n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k214(p, e)

def symn.k212(j: Nat, e: {Nat.is_le(j, 44n) == True{} : Bool}) -> {Nat.add(212n, j) == U32.to_nat(U32.from_nat(Nat.add(212n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k213(p, e)

def symn.k211(j: Nat, e: {Nat.is_le(j, 45n) == True{} : Bool}) -> {Nat.add(211n, j) == U32.to_nat(U32.from_nat(Nat.add(211n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k212(p, e)

def symn.k210(j: Nat, e: {Nat.is_le(j, 46n) == True{} : Bool}) -> {Nat.add(210n, j) == U32.to_nat(U32.from_nat(Nat.add(210n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k211(p, e)

def symn.k209(j: Nat, e: {Nat.is_le(j, 47n) == True{} : Bool}) -> {Nat.add(209n, j) == U32.to_nat(U32.from_nat(Nat.add(209n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k210(p, e)

def symn.k208(j: Nat, e: {Nat.is_le(j, 48n) == True{} : Bool}) -> {Nat.add(208n, j) == U32.to_nat(U32.from_nat(Nat.add(208n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k209(p, e)

def symn.k207(j: Nat, e: {Nat.is_le(j, 49n) == True{} : Bool}) -> {Nat.add(207n, j) == U32.to_nat(U32.from_nat(Nat.add(207n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k208(p, e)

def symn.k206(j: Nat, e: {Nat.is_le(j, 50n) == True{} : Bool}) -> {Nat.add(206n, j) == U32.to_nat(U32.from_nat(Nat.add(206n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k207(p, e)

def symn.k205(j: Nat, e: {Nat.is_le(j, 51n) == True{} : Bool}) -> {Nat.add(205n, j) == U32.to_nat(U32.from_nat(Nat.add(205n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k206(p, e)

def symn.k204(j: Nat, e: {Nat.is_le(j, 52n) == True{} : Bool}) -> {Nat.add(204n, j) == U32.to_nat(U32.from_nat(Nat.add(204n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k205(p, e)

def symn.k203(j: Nat, e: {Nat.is_le(j, 53n) == True{} : Bool}) -> {Nat.add(203n, j) == U32.to_nat(U32.from_nat(Nat.add(203n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k204(p, e)

def symn.k202(j: Nat, e: {Nat.is_le(j, 54n) == True{} : Bool}) -> {Nat.add(202n, j) == U32.to_nat(U32.from_nat(Nat.add(202n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k203(p, e)

def symn.k201(j: Nat, e: {Nat.is_le(j, 55n) == True{} : Bool}) -> {Nat.add(201n, j) == U32.to_nat(U32.from_nat(Nat.add(201n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k202(p, e)

def symn.k200(j: Nat, e: {Nat.is_le(j, 56n) == True{} : Bool}) -> {Nat.add(200n, j) == U32.to_nat(U32.from_nat(Nat.add(200n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k201(p, e)

def symn.k199(j: Nat, e: {Nat.is_le(j, 57n) == True{} : Bool}) -> {Nat.add(199n, j) == U32.to_nat(U32.from_nat(Nat.add(199n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k200(p, e)

def symn.k198(j: Nat, e: {Nat.is_le(j, 58n) == True{} : Bool}) -> {Nat.add(198n, j) == U32.to_nat(U32.from_nat(Nat.add(198n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k199(p, e)

def symn.k197(j: Nat, e: {Nat.is_le(j, 59n) == True{} : Bool}) -> {Nat.add(197n, j) == U32.to_nat(U32.from_nat(Nat.add(197n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k198(p, e)

def symn.k196(j: Nat, e: {Nat.is_le(j, 60n) == True{} : Bool}) -> {Nat.add(196n, j) == U32.to_nat(U32.from_nat(Nat.add(196n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k197(p, e)

def symn.k195(j: Nat, e: {Nat.is_le(j, 61n) == True{} : Bool}) -> {Nat.add(195n, j) == U32.to_nat(U32.from_nat(Nat.add(195n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k196(p, e)

def symn.k194(j: Nat, e: {Nat.is_le(j, 62n) == True{} : Bool}) -> {Nat.add(194n, j) == U32.to_nat(U32.from_nat(Nat.add(194n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k195(p, e)

def symn.k193(j: Nat, e: {Nat.is_le(j, 63n) == True{} : Bool}) -> {Nat.add(193n, j) == U32.to_nat(U32.from_nat(Nat.add(193n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k194(p, e)

def symn.k192(j: Nat, e: {Nat.is_le(j, 64n) == True{} : Bool}) -> {Nat.add(192n, j) == U32.to_nat(U32.from_nat(Nat.add(192n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k193(p, e)

def symn.k191(j: Nat, e: {Nat.is_le(j, 65n) == True{} : Bool}) -> {Nat.add(191n, j) == U32.to_nat(U32.from_nat(Nat.add(191n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k192(p, e)

def symn.k190(j: Nat, e: {Nat.is_le(j, 66n) == True{} : Bool}) -> {Nat.add(190n, j) == U32.to_nat(U32.from_nat(Nat.add(190n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k191(p, e)

def symn.k189(j: Nat, e: {Nat.is_le(j, 67n) == True{} : Bool}) -> {Nat.add(189n, j) == U32.to_nat(U32.from_nat(Nat.add(189n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k190(p, e)

def symn.k188(j: Nat, e: {Nat.is_le(j, 68n) == True{} : Bool}) -> {Nat.add(188n, j) == U32.to_nat(U32.from_nat(Nat.add(188n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k189(p, e)

def symn.k187(j: Nat, e: {Nat.is_le(j, 69n) == True{} : Bool}) -> {Nat.add(187n, j) == U32.to_nat(U32.from_nat(Nat.add(187n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k188(p, e)

def symn.k186(j: Nat, e: {Nat.is_le(j, 70n) == True{} : Bool}) -> {Nat.add(186n, j) == U32.to_nat(U32.from_nat(Nat.add(186n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k187(p, e)

def symn.k185(j: Nat, e: {Nat.is_le(j, 71n) == True{} : Bool}) -> {Nat.add(185n, j) == U32.to_nat(U32.from_nat(Nat.add(185n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k186(p, e)

def symn.k184(j: Nat, e: {Nat.is_le(j, 72n) == True{} : Bool}) -> {Nat.add(184n, j) == U32.to_nat(U32.from_nat(Nat.add(184n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k185(p, e)

def symn.k183(j: Nat, e: {Nat.is_le(j, 73n) == True{} : Bool}) -> {Nat.add(183n, j) == U32.to_nat(U32.from_nat(Nat.add(183n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k184(p, e)

def symn.k182(j: Nat, e: {Nat.is_le(j, 74n) == True{} : Bool}) -> {Nat.add(182n, j) == U32.to_nat(U32.from_nat(Nat.add(182n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k183(p, e)

def symn.k181(j: Nat, e: {Nat.is_le(j, 75n) == True{} : Bool}) -> {Nat.add(181n, j) == U32.to_nat(U32.from_nat(Nat.add(181n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k182(p, e)

def symn.k180(j: Nat, e: {Nat.is_le(j, 76n) == True{} : Bool}) -> {Nat.add(180n, j) == U32.to_nat(U32.from_nat(Nat.add(180n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k181(p, e)

def symn.k179(j: Nat, e: {Nat.is_le(j, 77n) == True{} : Bool}) -> {Nat.add(179n, j) == U32.to_nat(U32.from_nat(Nat.add(179n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k180(p, e)

def symn.k178(j: Nat, e: {Nat.is_le(j, 78n) == True{} : Bool}) -> {Nat.add(178n, j) == U32.to_nat(U32.from_nat(Nat.add(178n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k179(p, e)

def symn.k177(j: Nat, e: {Nat.is_le(j, 79n) == True{} : Bool}) -> {Nat.add(177n, j) == U32.to_nat(U32.from_nat(Nat.add(177n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k178(p, e)

def symn.k176(j: Nat, e: {Nat.is_le(j, 80n) == True{} : Bool}) -> {Nat.add(176n, j) == U32.to_nat(U32.from_nat(Nat.add(176n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k177(p, e)

def symn.k175(j: Nat, e: {Nat.is_le(j, 81n) == True{} : Bool}) -> {Nat.add(175n, j) == U32.to_nat(U32.from_nat(Nat.add(175n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k176(p, e)

def symn.k174(j: Nat, e: {Nat.is_le(j, 82n) == True{} : Bool}) -> {Nat.add(174n, j) == U32.to_nat(U32.from_nat(Nat.add(174n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k175(p, e)

def symn.k173(j: Nat, e: {Nat.is_le(j, 83n) == True{} : Bool}) -> {Nat.add(173n, j) == U32.to_nat(U32.from_nat(Nat.add(173n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k174(p, e)

def symn.k172(j: Nat, e: {Nat.is_le(j, 84n) == True{} : Bool}) -> {Nat.add(172n, j) == U32.to_nat(U32.from_nat(Nat.add(172n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k173(p, e)

def symn.k171(j: Nat, e: {Nat.is_le(j, 85n) == True{} : Bool}) -> {Nat.add(171n, j) == U32.to_nat(U32.from_nat(Nat.add(171n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k172(p, e)

def symn.k170(j: Nat, e: {Nat.is_le(j, 86n) == True{} : Bool}) -> {Nat.add(170n, j) == U32.to_nat(U32.from_nat(Nat.add(170n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k171(p, e)

def symn.k169(j: Nat, e: {Nat.is_le(j, 87n) == True{} : Bool}) -> {Nat.add(169n, j) == U32.to_nat(U32.from_nat(Nat.add(169n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k170(p, e)

def symn.k168(j: Nat, e: {Nat.is_le(j, 88n) == True{} : Bool}) -> {Nat.add(168n, j) == U32.to_nat(U32.from_nat(Nat.add(168n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k169(p, e)

def symn.k167(j: Nat, e: {Nat.is_le(j, 89n) == True{} : Bool}) -> {Nat.add(167n, j) == U32.to_nat(U32.from_nat(Nat.add(167n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k168(p, e)

def symn.k166(j: Nat, e: {Nat.is_le(j, 90n) == True{} : Bool}) -> {Nat.add(166n, j) == U32.to_nat(U32.from_nat(Nat.add(166n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k167(p, e)

def symn.k165(j: Nat, e: {Nat.is_le(j, 91n) == True{} : Bool}) -> {Nat.add(165n, j) == U32.to_nat(U32.from_nat(Nat.add(165n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k166(p, e)

def symn.k164(j: Nat, e: {Nat.is_le(j, 92n) == True{} : Bool}) -> {Nat.add(164n, j) == U32.to_nat(U32.from_nat(Nat.add(164n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k165(p, e)

def symn.k163(j: Nat, e: {Nat.is_le(j, 93n) == True{} : Bool}) -> {Nat.add(163n, j) == U32.to_nat(U32.from_nat(Nat.add(163n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k164(p, e)

def symn.k162(j: Nat, e: {Nat.is_le(j, 94n) == True{} : Bool}) -> {Nat.add(162n, j) == U32.to_nat(U32.from_nat(Nat.add(162n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k163(p, e)

def symn.k161(j: Nat, e: {Nat.is_le(j, 95n) == True{} : Bool}) -> {Nat.add(161n, j) == U32.to_nat(U32.from_nat(Nat.add(161n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k162(p, e)

def symn.k160(j: Nat, e: {Nat.is_le(j, 96n) == True{} : Bool}) -> {Nat.add(160n, j) == U32.to_nat(U32.from_nat(Nat.add(160n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k161(p, e)

def symn.k159(j: Nat, e: {Nat.is_le(j, 97n) == True{} : Bool}) -> {Nat.add(159n, j) == U32.to_nat(U32.from_nat(Nat.add(159n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k160(p, e)

def symn.k158(j: Nat, e: {Nat.is_le(j, 98n) == True{} : Bool}) -> {Nat.add(158n, j) == U32.to_nat(U32.from_nat(Nat.add(158n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k159(p, e)

def symn.k157(j: Nat, e: {Nat.is_le(j, 99n) == True{} : Bool}) -> {Nat.add(157n, j) == U32.to_nat(U32.from_nat(Nat.add(157n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k158(p, e)

def symn.k156(j: Nat, e: {Nat.is_le(j, 100n) == True{} : Bool}) -> {Nat.add(156n, j) == U32.to_nat(U32.from_nat(Nat.add(156n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k157(p, e)

def symn.k155(j: Nat, e: {Nat.is_le(j, 101n) == True{} : Bool}) -> {Nat.add(155n, j) == U32.to_nat(U32.from_nat(Nat.add(155n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k156(p, e)

def symn.k154(j: Nat, e: {Nat.is_le(j, 102n) == True{} : Bool}) -> {Nat.add(154n, j) == U32.to_nat(U32.from_nat(Nat.add(154n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k155(p, e)

def symn.k153(j: Nat, e: {Nat.is_le(j, 103n) == True{} : Bool}) -> {Nat.add(153n, j) == U32.to_nat(U32.from_nat(Nat.add(153n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k154(p, e)

def symn.k152(j: Nat, e: {Nat.is_le(j, 104n) == True{} : Bool}) -> {Nat.add(152n, j) == U32.to_nat(U32.from_nat(Nat.add(152n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k153(p, e)

def symn.k151(j: Nat, e: {Nat.is_le(j, 105n) == True{} : Bool}) -> {Nat.add(151n, j) == U32.to_nat(U32.from_nat(Nat.add(151n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k152(p, e)

def symn.k150(j: Nat, e: {Nat.is_le(j, 106n) == True{} : Bool}) -> {Nat.add(150n, j) == U32.to_nat(U32.from_nat(Nat.add(150n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k151(p, e)

def symn.k149(j: Nat, e: {Nat.is_le(j, 107n) == True{} : Bool}) -> {Nat.add(149n, j) == U32.to_nat(U32.from_nat(Nat.add(149n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k150(p, e)

def symn.k148(j: Nat, e: {Nat.is_le(j, 108n) == True{} : Bool}) -> {Nat.add(148n, j) == U32.to_nat(U32.from_nat(Nat.add(148n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k149(p, e)

def symn.k147(j: Nat, e: {Nat.is_le(j, 109n) == True{} : Bool}) -> {Nat.add(147n, j) == U32.to_nat(U32.from_nat(Nat.add(147n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k148(p, e)

def symn.k146(j: Nat, e: {Nat.is_le(j, 110n) == True{} : Bool}) -> {Nat.add(146n, j) == U32.to_nat(U32.from_nat(Nat.add(146n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k147(p, e)

def symn.k145(j: Nat, e: {Nat.is_le(j, 111n) == True{} : Bool}) -> {Nat.add(145n, j) == U32.to_nat(U32.from_nat(Nat.add(145n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k146(p, e)

def symn.k144(j: Nat, e: {Nat.is_le(j, 112n) == True{} : Bool}) -> {Nat.add(144n, j) == U32.to_nat(U32.from_nat(Nat.add(144n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k145(p, e)

def symn.k143(j: Nat, e: {Nat.is_le(j, 113n) == True{} : Bool}) -> {Nat.add(143n, j) == U32.to_nat(U32.from_nat(Nat.add(143n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k144(p, e)

def symn.k142(j: Nat, e: {Nat.is_le(j, 114n) == True{} : Bool}) -> {Nat.add(142n, j) == U32.to_nat(U32.from_nat(Nat.add(142n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k143(p, e)

def symn.k141(j: Nat, e: {Nat.is_le(j, 115n) == True{} : Bool}) -> {Nat.add(141n, j) == U32.to_nat(U32.from_nat(Nat.add(141n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k142(p, e)

def symn.k140(j: Nat, e: {Nat.is_le(j, 116n) == True{} : Bool}) -> {Nat.add(140n, j) == U32.to_nat(U32.from_nat(Nat.add(140n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k141(p, e)

def symn.k139(j: Nat, e: {Nat.is_le(j, 117n) == True{} : Bool}) -> {Nat.add(139n, j) == U32.to_nat(U32.from_nat(Nat.add(139n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k140(p, e)

def symn.k138(j: Nat, e: {Nat.is_le(j, 118n) == True{} : Bool}) -> {Nat.add(138n, j) == U32.to_nat(U32.from_nat(Nat.add(138n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k139(p, e)

def symn.k137(j: Nat, e: {Nat.is_le(j, 119n) == True{} : Bool}) -> {Nat.add(137n, j) == U32.to_nat(U32.from_nat(Nat.add(137n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k138(p, e)

def symn.k136(j: Nat, e: {Nat.is_le(j, 120n) == True{} : Bool}) -> {Nat.add(136n, j) == U32.to_nat(U32.from_nat(Nat.add(136n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k137(p, e)

def symn.k135(j: Nat, e: {Nat.is_le(j, 121n) == True{} : Bool}) -> {Nat.add(135n, j) == U32.to_nat(U32.from_nat(Nat.add(135n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k136(p, e)

def symn.k134(j: Nat, e: {Nat.is_le(j, 122n) == True{} : Bool}) -> {Nat.add(134n, j) == U32.to_nat(U32.from_nat(Nat.add(134n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k135(p, e)

def symn.k133(j: Nat, e: {Nat.is_le(j, 123n) == True{} : Bool}) -> {Nat.add(133n, j) == U32.to_nat(U32.from_nat(Nat.add(133n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k134(p, e)

def symn.k132(j: Nat, e: {Nat.is_le(j, 124n) == True{} : Bool}) -> {Nat.add(132n, j) == U32.to_nat(U32.from_nat(Nat.add(132n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k133(p, e)

def symn.k131(j: Nat, e: {Nat.is_le(j, 125n) == True{} : Bool}) -> {Nat.add(131n, j) == U32.to_nat(U32.from_nat(Nat.add(131n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k132(p, e)

def symn.k130(j: Nat, e: {Nat.is_le(j, 126n) == True{} : Bool}) -> {Nat.add(130n, j) == U32.to_nat(U32.from_nat(Nat.add(130n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k131(p, e)

def symn.k129(j: Nat, e: {Nat.is_le(j, 127n) == True{} : Bool}) -> {Nat.add(129n, j) == U32.to_nat(U32.from_nat(Nat.add(129n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k130(p, e)

def symn.k128(j: Nat, e: {Nat.is_le(j, 128n) == True{} : Bool}) -> {Nat.add(128n, j) == U32.to_nat(U32.from_nat(Nat.add(128n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k129(p, e)

def symn.k127(j: Nat, e: {Nat.is_le(j, 129n) == True{} : Bool}) -> {Nat.add(127n, j) == U32.to_nat(U32.from_nat(Nat.add(127n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k128(p, e)

def symn.k126(j: Nat, e: {Nat.is_le(j, 130n) == True{} : Bool}) -> {Nat.add(126n, j) == U32.to_nat(U32.from_nat(Nat.add(126n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k127(p, e)

def symn.k125(j: Nat, e: {Nat.is_le(j, 131n) == True{} : Bool}) -> {Nat.add(125n, j) == U32.to_nat(U32.from_nat(Nat.add(125n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k126(p, e)

def symn.k124(j: Nat, e: {Nat.is_le(j, 132n) == True{} : Bool}) -> {Nat.add(124n, j) == U32.to_nat(U32.from_nat(Nat.add(124n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k125(p, e)

def symn.k123(j: Nat, e: {Nat.is_le(j, 133n) == True{} : Bool}) -> {Nat.add(123n, j) == U32.to_nat(U32.from_nat(Nat.add(123n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k124(p, e)

def symn.k122(j: Nat, e: {Nat.is_le(j, 134n) == True{} : Bool}) -> {Nat.add(122n, j) == U32.to_nat(U32.from_nat(Nat.add(122n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k123(p, e)

def symn.k121(j: Nat, e: {Nat.is_le(j, 135n) == True{} : Bool}) -> {Nat.add(121n, j) == U32.to_nat(U32.from_nat(Nat.add(121n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k122(p, e)

def symn.k120(j: Nat, e: {Nat.is_le(j, 136n) == True{} : Bool}) -> {Nat.add(120n, j) == U32.to_nat(U32.from_nat(Nat.add(120n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k121(p, e)

def symn.k119(j: Nat, e: {Nat.is_le(j, 137n) == True{} : Bool}) -> {Nat.add(119n, j) == U32.to_nat(U32.from_nat(Nat.add(119n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k120(p, e)

def symn.k118(j: Nat, e: {Nat.is_le(j, 138n) == True{} : Bool}) -> {Nat.add(118n, j) == U32.to_nat(U32.from_nat(Nat.add(118n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k119(p, e)

def symn.k117(j: Nat, e: {Nat.is_le(j, 139n) == True{} : Bool}) -> {Nat.add(117n, j) == U32.to_nat(U32.from_nat(Nat.add(117n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k118(p, e)

def symn.k116(j: Nat, e: {Nat.is_le(j, 140n) == True{} : Bool}) -> {Nat.add(116n, j) == U32.to_nat(U32.from_nat(Nat.add(116n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k117(p, e)

def symn.k115(j: Nat, e: {Nat.is_le(j, 141n) == True{} : Bool}) -> {Nat.add(115n, j) == U32.to_nat(U32.from_nat(Nat.add(115n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k116(p, e)

def symn.k114(j: Nat, e: {Nat.is_le(j, 142n) == True{} : Bool}) -> {Nat.add(114n, j) == U32.to_nat(U32.from_nat(Nat.add(114n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k115(p, e)

def symn.k113(j: Nat, e: {Nat.is_le(j, 143n) == True{} : Bool}) -> {Nat.add(113n, j) == U32.to_nat(U32.from_nat(Nat.add(113n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k114(p, e)

def symn.k112(j: Nat, e: {Nat.is_le(j, 144n) == True{} : Bool}) -> {Nat.add(112n, j) == U32.to_nat(U32.from_nat(Nat.add(112n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k113(p, e)

def symn.k111(j: Nat, e: {Nat.is_le(j, 145n) == True{} : Bool}) -> {Nat.add(111n, j) == U32.to_nat(U32.from_nat(Nat.add(111n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k112(p, e)

def symn.k110(j: Nat, e: {Nat.is_le(j, 146n) == True{} : Bool}) -> {Nat.add(110n, j) == U32.to_nat(U32.from_nat(Nat.add(110n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k111(p, e)

def symn.k109(j: Nat, e: {Nat.is_le(j, 147n) == True{} : Bool}) -> {Nat.add(109n, j) == U32.to_nat(U32.from_nat(Nat.add(109n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k110(p, e)

def symn.k108(j: Nat, e: {Nat.is_le(j, 148n) == True{} : Bool}) -> {Nat.add(108n, j) == U32.to_nat(U32.from_nat(Nat.add(108n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k109(p, e)

def symn.k107(j: Nat, e: {Nat.is_le(j, 149n) == True{} : Bool}) -> {Nat.add(107n, j) == U32.to_nat(U32.from_nat(Nat.add(107n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k108(p, e)

def symn.k106(j: Nat, e: {Nat.is_le(j, 150n) == True{} : Bool}) -> {Nat.add(106n, j) == U32.to_nat(U32.from_nat(Nat.add(106n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k107(p, e)

def symn.k105(j: Nat, e: {Nat.is_le(j, 151n) == True{} : Bool}) -> {Nat.add(105n, j) == U32.to_nat(U32.from_nat(Nat.add(105n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k106(p, e)

def symn.k104(j: Nat, e: {Nat.is_le(j, 152n) == True{} : Bool}) -> {Nat.add(104n, j) == U32.to_nat(U32.from_nat(Nat.add(104n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k105(p, e)

def symn.k103(j: Nat, e: {Nat.is_le(j, 153n) == True{} : Bool}) -> {Nat.add(103n, j) == U32.to_nat(U32.from_nat(Nat.add(103n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k104(p, e)

def symn.k102(j: Nat, e: {Nat.is_le(j, 154n) == True{} : Bool}) -> {Nat.add(102n, j) == U32.to_nat(U32.from_nat(Nat.add(102n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k103(p, e)

def symn.k101(j: Nat, e: {Nat.is_le(j, 155n) == True{} : Bool}) -> {Nat.add(101n, j) == U32.to_nat(U32.from_nat(Nat.add(101n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k102(p, e)

def symn.k100(j: Nat, e: {Nat.is_le(j, 156n) == True{} : Bool}) -> {Nat.add(100n, j) == U32.to_nat(U32.from_nat(Nat.add(100n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k101(p, e)

def symn.k99(j: Nat, e: {Nat.is_le(j, 157n) == True{} : Bool}) -> {Nat.add(99n, j) == U32.to_nat(U32.from_nat(Nat.add(99n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k100(p, e)

def symn.k98(j: Nat, e: {Nat.is_le(j, 158n) == True{} : Bool}) -> {Nat.add(98n, j) == U32.to_nat(U32.from_nat(Nat.add(98n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k99(p, e)

def symn.k97(j: Nat, e: {Nat.is_le(j, 159n) == True{} : Bool}) -> {Nat.add(97n, j) == U32.to_nat(U32.from_nat(Nat.add(97n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k98(p, e)

def symn.k96(j: Nat, e: {Nat.is_le(j, 160n) == True{} : Bool}) -> {Nat.add(96n, j) == U32.to_nat(U32.from_nat(Nat.add(96n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k97(p, e)

def symn.k95(j: Nat, e: {Nat.is_le(j, 161n) == True{} : Bool}) -> {Nat.add(95n, j) == U32.to_nat(U32.from_nat(Nat.add(95n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k96(p, e)

def symn.k94(j: Nat, e: {Nat.is_le(j, 162n) == True{} : Bool}) -> {Nat.add(94n, j) == U32.to_nat(U32.from_nat(Nat.add(94n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k95(p, e)

def symn.k93(j: Nat, e: {Nat.is_le(j, 163n) == True{} : Bool}) -> {Nat.add(93n, j) == U32.to_nat(U32.from_nat(Nat.add(93n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k94(p, e)

def symn.k92(j: Nat, e: {Nat.is_le(j, 164n) == True{} : Bool}) -> {Nat.add(92n, j) == U32.to_nat(U32.from_nat(Nat.add(92n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k93(p, e)

def symn.k91(j: Nat, e: {Nat.is_le(j, 165n) == True{} : Bool}) -> {Nat.add(91n, j) == U32.to_nat(U32.from_nat(Nat.add(91n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k92(p, e)

def symn.k90(j: Nat, e: {Nat.is_le(j, 166n) == True{} : Bool}) -> {Nat.add(90n, j) == U32.to_nat(U32.from_nat(Nat.add(90n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k91(p, e)

def symn.k89(j: Nat, e: {Nat.is_le(j, 167n) == True{} : Bool}) -> {Nat.add(89n, j) == U32.to_nat(U32.from_nat(Nat.add(89n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k90(p, e)

def symn.k88(j: Nat, e: {Nat.is_le(j, 168n) == True{} : Bool}) -> {Nat.add(88n, j) == U32.to_nat(U32.from_nat(Nat.add(88n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k89(p, e)

def symn.k87(j: Nat, e: {Nat.is_le(j, 169n) == True{} : Bool}) -> {Nat.add(87n, j) == U32.to_nat(U32.from_nat(Nat.add(87n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k88(p, e)

def symn.k86(j: Nat, e: {Nat.is_le(j, 170n) == True{} : Bool}) -> {Nat.add(86n, j) == U32.to_nat(U32.from_nat(Nat.add(86n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k87(p, e)

def symn.k85(j: Nat, e: {Nat.is_le(j, 171n) == True{} : Bool}) -> {Nat.add(85n, j) == U32.to_nat(U32.from_nat(Nat.add(85n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k86(p, e)

def symn.k84(j: Nat, e: {Nat.is_le(j, 172n) == True{} : Bool}) -> {Nat.add(84n, j) == U32.to_nat(U32.from_nat(Nat.add(84n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k85(p, e)

def symn.k83(j: Nat, e: {Nat.is_le(j, 173n) == True{} : Bool}) -> {Nat.add(83n, j) == U32.to_nat(U32.from_nat(Nat.add(83n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k84(p, e)

def symn.k82(j: Nat, e: {Nat.is_le(j, 174n) == True{} : Bool}) -> {Nat.add(82n, j) == U32.to_nat(U32.from_nat(Nat.add(82n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k83(p, e)

def symn.k81(j: Nat, e: {Nat.is_le(j, 175n) == True{} : Bool}) -> {Nat.add(81n, j) == U32.to_nat(U32.from_nat(Nat.add(81n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k82(p, e)

def symn.k80(j: Nat, e: {Nat.is_le(j, 176n) == True{} : Bool}) -> {Nat.add(80n, j) == U32.to_nat(U32.from_nat(Nat.add(80n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k81(p, e)

def symn.k79(j: Nat, e: {Nat.is_le(j, 177n) == True{} : Bool}) -> {Nat.add(79n, j) == U32.to_nat(U32.from_nat(Nat.add(79n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k80(p, e)

def symn.k78(j: Nat, e: {Nat.is_le(j, 178n) == True{} : Bool}) -> {Nat.add(78n, j) == U32.to_nat(U32.from_nat(Nat.add(78n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k79(p, e)

def symn.k77(j: Nat, e: {Nat.is_le(j, 179n) == True{} : Bool}) -> {Nat.add(77n, j) == U32.to_nat(U32.from_nat(Nat.add(77n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k78(p, e)

def symn.k76(j: Nat, e: {Nat.is_le(j, 180n) == True{} : Bool}) -> {Nat.add(76n, j) == U32.to_nat(U32.from_nat(Nat.add(76n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k77(p, e)

def symn.k75(j: Nat, e: {Nat.is_le(j, 181n) == True{} : Bool}) -> {Nat.add(75n, j) == U32.to_nat(U32.from_nat(Nat.add(75n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k76(p, e)

def symn.k74(j: Nat, e: {Nat.is_le(j, 182n) == True{} : Bool}) -> {Nat.add(74n, j) == U32.to_nat(U32.from_nat(Nat.add(74n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k75(p, e)

def symn.k73(j: Nat, e: {Nat.is_le(j, 183n) == True{} : Bool}) -> {Nat.add(73n, j) == U32.to_nat(U32.from_nat(Nat.add(73n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k74(p, e)

def symn.k72(j: Nat, e: {Nat.is_le(j, 184n) == True{} : Bool}) -> {Nat.add(72n, j) == U32.to_nat(U32.from_nat(Nat.add(72n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k73(p, e)

def symn.k71(j: Nat, e: {Nat.is_le(j, 185n) == True{} : Bool}) -> {Nat.add(71n, j) == U32.to_nat(U32.from_nat(Nat.add(71n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k72(p, e)

def symn.k70(j: Nat, e: {Nat.is_le(j, 186n) == True{} : Bool}) -> {Nat.add(70n, j) == U32.to_nat(U32.from_nat(Nat.add(70n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k71(p, e)

def symn.k69(j: Nat, e: {Nat.is_le(j, 187n) == True{} : Bool}) -> {Nat.add(69n, j) == U32.to_nat(U32.from_nat(Nat.add(69n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k70(p, e)

def symn.k68(j: Nat, e: {Nat.is_le(j, 188n) == True{} : Bool}) -> {Nat.add(68n, j) == U32.to_nat(U32.from_nat(Nat.add(68n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k69(p, e)

def symn.k67(j: Nat, e: {Nat.is_le(j, 189n) == True{} : Bool}) -> {Nat.add(67n, j) == U32.to_nat(U32.from_nat(Nat.add(67n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k68(p, e)

def symn.k66(j: Nat, e: {Nat.is_le(j, 190n) == True{} : Bool}) -> {Nat.add(66n, j) == U32.to_nat(U32.from_nat(Nat.add(66n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k67(p, e)

def symn.k65(j: Nat, e: {Nat.is_le(j, 191n) == True{} : Bool}) -> {Nat.add(65n, j) == U32.to_nat(U32.from_nat(Nat.add(65n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k66(p, e)

def symn.k64(j: Nat, e: {Nat.is_le(j, 192n) == True{} : Bool}) -> {Nat.add(64n, j) == U32.to_nat(U32.from_nat(Nat.add(64n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k65(p, e)

def symn.k63(j: Nat, e: {Nat.is_le(j, 193n) == True{} : Bool}) -> {Nat.add(63n, j) == U32.to_nat(U32.from_nat(Nat.add(63n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k64(p, e)

def symn.k62(j: Nat, e: {Nat.is_le(j, 194n) == True{} : Bool}) -> {Nat.add(62n, j) == U32.to_nat(U32.from_nat(Nat.add(62n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k63(p, e)

def symn.k61(j: Nat, e: {Nat.is_le(j, 195n) == True{} : Bool}) -> {Nat.add(61n, j) == U32.to_nat(U32.from_nat(Nat.add(61n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k62(p, e)

def symn.k60(j: Nat, e: {Nat.is_le(j, 196n) == True{} : Bool}) -> {Nat.add(60n, j) == U32.to_nat(U32.from_nat(Nat.add(60n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k61(p, e)

def symn.k59(j: Nat, e: {Nat.is_le(j, 197n) == True{} : Bool}) -> {Nat.add(59n, j) == U32.to_nat(U32.from_nat(Nat.add(59n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k60(p, e)

def symn.k58(j: Nat, e: {Nat.is_le(j, 198n) == True{} : Bool}) -> {Nat.add(58n, j) == U32.to_nat(U32.from_nat(Nat.add(58n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k59(p, e)

def symn.k57(j: Nat, e: {Nat.is_le(j, 199n) == True{} : Bool}) -> {Nat.add(57n, j) == U32.to_nat(U32.from_nat(Nat.add(57n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k58(p, e)

def symn.k56(j: Nat, e: {Nat.is_le(j, 200n) == True{} : Bool}) -> {Nat.add(56n, j) == U32.to_nat(U32.from_nat(Nat.add(56n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k57(p, e)

def symn.k55(j: Nat, e: {Nat.is_le(j, 201n) == True{} : Bool}) -> {Nat.add(55n, j) == U32.to_nat(U32.from_nat(Nat.add(55n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k56(p, e)

def symn.k54(j: Nat, e: {Nat.is_le(j, 202n) == True{} : Bool}) -> {Nat.add(54n, j) == U32.to_nat(U32.from_nat(Nat.add(54n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k55(p, e)

def symn.k53(j: Nat, e: {Nat.is_le(j, 203n) == True{} : Bool}) -> {Nat.add(53n, j) == U32.to_nat(U32.from_nat(Nat.add(53n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k54(p, e)

def symn.k52(j: Nat, e: {Nat.is_le(j, 204n) == True{} : Bool}) -> {Nat.add(52n, j) == U32.to_nat(U32.from_nat(Nat.add(52n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k53(p, e)

def symn.k51(j: Nat, e: {Nat.is_le(j, 205n) == True{} : Bool}) -> {Nat.add(51n, j) == U32.to_nat(U32.from_nat(Nat.add(51n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k52(p, e)

def symn.k50(j: Nat, e: {Nat.is_le(j, 206n) == True{} : Bool}) -> {Nat.add(50n, j) == U32.to_nat(U32.from_nat(Nat.add(50n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k51(p, e)

def symn.k49(j: Nat, e: {Nat.is_le(j, 207n) == True{} : Bool}) -> {Nat.add(49n, j) == U32.to_nat(U32.from_nat(Nat.add(49n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k50(p, e)

def symn.k48(j: Nat, e: {Nat.is_le(j, 208n) == True{} : Bool}) -> {Nat.add(48n, j) == U32.to_nat(U32.from_nat(Nat.add(48n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k49(p, e)

def symn.k47(j: Nat, e: {Nat.is_le(j, 209n) == True{} : Bool}) -> {Nat.add(47n, j) == U32.to_nat(U32.from_nat(Nat.add(47n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k48(p, e)

def symn.k46(j: Nat, e: {Nat.is_le(j, 210n) == True{} : Bool}) -> {Nat.add(46n, j) == U32.to_nat(U32.from_nat(Nat.add(46n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k47(p, e)

def symn.k45(j: Nat, e: {Nat.is_le(j, 211n) == True{} : Bool}) -> {Nat.add(45n, j) == U32.to_nat(U32.from_nat(Nat.add(45n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k46(p, e)

def symn.k44(j: Nat, e: {Nat.is_le(j, 212n) == True{} : Bool}) -> {Nat.add(44n, j) == U32.to_nat(U32.from_nat(Nat.add(44n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k45(p, e)

def symn.k43(j: Nat, e: {Nat.is_le(j, 213n) == True{} : Bool}) -> {Nat.add(43n, j) == U32.to_nat(U32.from_nat(Nat.add(43n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k44(p, e)

def symn.k42(j: Nat, e: {Nat.is_le(j, 214n) == True{} : Bool}) -> {Nat.add(42n, j) == U32.to_nat(U32.from_nat(Nat.add(42n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k43(p, e)

def symn.k41(j: Nat, e: {Nat.is_le(j, 215n) == True{} : Bool}) -> {Nat.add(41n, j) == U32.to_nat(U32.from_nat(Nat.add(41n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k42(p, e)

def symn.k40(j: Nat, e: {Nat.is_le(j, 216n) == True{} : Bool}) -> {Nat.add(40n, j) == U32.to_nat(U32.from_nat(Nat.add(40n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k41(p, e)

def symn.k39(j: Nat, e: {Nat.is_le(j, 217n) == True{} : Bool}) -> {Nat.add(39n, j) == U32.to_nat(U32.from_nat(Nat.add(39n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k40(p, e)

def symn.k38(j: Nat, e: {Nat.is_le(j, 218n) == True{} : Bool}) -> {Nat.add(38n, j) == U32.to_nat(U32.from_nat(Nat.add(38n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k39(p, e)

def symn.k37(j: Nat, e: {Nat.is_le(j, 219n) == True{} : Bool}) -> {Nat.add(37n, j) == U32.to_nat(U32.from_nat(Nat.add(37n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k38(p, e)

def symn.k36(j: Nat, e: {Nat.is_le(j, 220n) == True{} : Bool}) -> {Nat.add(36n, j) == U32.to_nat(U32.from_nat(Nat.add(36n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k37(p, e)

def symn.k35(j: Nat, e: {Nat.is_le(j, 221n) == True{} : Bool}) -> {Nat.add(35n, j) == U32.to_nat(U32.from_nat(Nat.add(35n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k36(p, e)

def symn.k34(j: Nat, e: {Nat.is_le(j, 222n) == True{} : Bool}) -> {Nat.add(34n, j) == U32.to_nat(U32.from_nat(Nat.add(34n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k35(p, e)

def symn.k33(j: Nat, e: {Nat.is_le(j, 223n) == True{} : Bool}) -> {Nat.add(33n, j) == U32.to_nat(U32.from_nat(Nat.add(33n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k34(p, e)

def symn.k32(j: Nat, e: {Nat.is_le(j, 224n) == True{} : Bool}) -> {Nat.add(32n, j) == U32.to_nat(U32.from_nat(Nat.add(32n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k33(p, e)

def symn.k31(j: Nat, e: {Nat.is_le(j, 225n) == True{} : Bool}) -> {Nat.add(31n, j) == U32.to_nat(U32.from_nat(Nat.add(31n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k32(p, e)

def symn.k30(j: Nat, e: {Nat.is_le(j, 226n) == True{} : Bool}) -> {Nat.add(30n, j) == U32.to_nat(U32.from_nat(Nat.add(30n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k31(p, e)

def symn.k29(j: Nat, e: {Nat.is_le(j, 227n) == True{} : Bool}) -> {Nat.add(29n, j) == U32.to_nat(U32.from_nat(Nat.add(29n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k30(p, e)

def symn.k28(j: Nat, e: {Nat.is_le(j, 228n) == True{} : Bool}) -> {Nat.add(28n, j) == U32.to_nat(U32.from_nat(Nat.add(28n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k29(p, e)

def symn.k27(j: Nat, e: {Nat.is_le(j, 229n) == True{} : Bool}) -> {Nat.add(27n, j) == U32.to_nat(U32.from_nat(Nat.add(27n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k28(p, e)

def symn.k26(j: Nat, e: {Nat.is_le(j, 230n) == True{} : Bool}) -> {Nat.add(26n, j) == U32.to_nat(U32.from_nat(Nat.add(26n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k27(p, e)

def symn.k25(j: Nat, e: {Nat.is_le(j, 231n) == True{} : Bool}) -> {Nat.add(25n, j) == U32.to_nat(U32.from_nat(Nat.add(25n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k26(p, e)

def symn.k24(j: Nat, e: {Nat.is_le(j, 232n) == True{} : Bool}) -> {Nat.add(24n, j) == U32.to_nat(U32.from_nat(Nat.add(24n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k25(p, e)

def symn.k23(j: Nat, e: {Nat.is_le(j, 233n) == True{} : Bool}) -> {Nat.add(23n, j) == U32.to_nat(U32.from_nat(Nat.add(23n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k24(p, e)

def symn.k22(j: Nat, e: {Nat.is_le(j, 234n) == True{} : Bool}) -> {Nat.add(22n, j) == U32.to_nat(U32.from_nat(Nat.add(22n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k23(p, e)

def symn.k21(j: Nat, e: {Nat.is_le(j, 235n) == True{} : Bool}) -> {Nat.add(21n, j) == U32.to_nat(U32.from_nat(Nat.add(21n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k22(p, e)

def symn.k20(j: Nat, e: {Nat.is_le(j, 236n) == True{} : Bool}) -> {Nat.add(20n, j) == U32.to_nat(U32.from_nat(Nat.add(20n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k21(p, e)

def symn.k19(j: Nat, e: {Nat.is_le(j, 237n) == True{} : Bool}) -> {Nat.add(19n, j) == U32.to_nat(U32.from_nat(Nat.add(19n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k20(p, e)

def symn.k18(j: Nat, e: {Nat.is_le(j, 238n) == True{} : Bool}) -> {Nat.add(18n, j) == U32.to_nat(U32.from_nat(Nat.add(18n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k19(p, e)

def symn.k17(j: Nat, e: {Nat.is_le(j, 239n) == True{} : Bool}) -> {Nat.add(17n, j) == U32.to_nat(U32.from_nat(Nat.add(17n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k18(p, e)

def symn.k16(j: Nat, e: {Nat.is_le(j, 240n) == True{} : Bool}) -> {Nat.add(16n, j) == U32.to_nat(U32.from_nat(Nat.add(16n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k17(p, e)

def symn.k15(j: Nat, e: {Nat.is_le(j, 241n) == True{} : Bool}) -> {Nat.add(15n, j) == U32.to_nat(U32.from_nat(Nat.add(15n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k16(p, e)

def symn.k14(j: Nat, e: {Nat.is_le(j, 242n) == True{} : Bool}) -> {Nat.add(14n, j) == U32.to_nat(U32.from_nat(Nat.add(14n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k15(p, e)

def symn.k13(j: Nat, e: {Nat.is_le(j, 243n) == True{} : Bool}) -> {Nat.add(13n, j) == U32.to_nat(U32.from_nat(Nat.add(13n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k14(p, e)

def symn.k12(j: Nat, e: {Nat.is_le(j, 244n) == True{} : Bool}) -> {Nat.add(12n, j) == U32.to_nat(U32.from_nat(Nat.add(12n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k13(p, e)

def symn.k11(j: Nat, e: {Nat.is_le(j, 245n) == True{} : Bool}) -> {Nat.add(11n, j) == U32.to_nat(U32.from_nat(Nat.add(11n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k12(p, e)

def symn.k10(j: Nat, e: {Nat.is_le(j, 246n) == True{} : Bool}) -> {Nat.add(10n, j) == U32.to_nat(U32.from_nat(Nat.add(10n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k11(p, e)

def symn.k9(j: Nat, e: {Nat.is_le(j, 247n) == True{} : Bool}) -> {Nat.add(9n, j) == U32.to_nat(U32.from_nat(Nat.add(9n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k10(p, e)

def symn.k8(j: Nat, e: {Nat.is_le(j, 248n) == True{} : Bool}) -> {Nat.add(8n, j) == U32.to_nat(U32.from_nat(Nat.add(8n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k9(p, e)

def symn.k7(j: Nat, e: {Nat.is_le(j, 249n) == True{} : Bool}) -> {Nat.add(7n, j) == U32.to_nat(U32.from_nat(Nat.add(7n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k8(p, e)

def symn.k6(j: Nat, e: {Nat.is_le(j, 250n) == True{} : Bool}) -> {Nat.add(6n, j) == U32.to_nat(U32.from_nat(Nat.add(6n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k7(p, e)

def symn.k5(j: Nat, e: {Nat.is_le(j, 251n) == True{} : Bool}) -> {Nat.add(5n, j) == U32.to_nat(U32.from_nat(Nat.add(5n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k6(p, e)

def symn.k4(j: Nat, e: {Nat.is_le(j, 252n) == True{} : Bool}) -> {Nat.add(4n, j) == U32.to_nat(U32.from_nat(Nat.add(4n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k5(p, e)

def symn.k3(j: Nat, e: {Nat.is_le(j, 253n) == True{} : Bool}) -> {Nat.add(3n, j) == U32.to_nat(U32.from_nat(Nat.add(3n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k4(p, e)

def symn.k2(j: Nat, e: {Nat.is_le(j, 254n) == True{} : Bool}) -> {Nat.add(2n, j) == U32.to_nat(U32.from_nat(Nat.add(2n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k3(p, e)

def symn.k1(j: Nat, e: {Nat.is_le(j, 255n) == True{} : Bool}) -> {Nat.add(1n, j) == U32.to_nat(U32.from_nat(Nat.add(1n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k2(p, e)

def symn.k0(j: Nat, e: {Nat.is_le(j, 256n) == True{} : Bool}) -> {Nat.add(0n, j) == U32.to_nat(U32.from_nat(Nat.add(0n, j))) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      symn.k1(p, e)



# Bad magic: the header's byte comparison fails, so the first stream fails,
# so the decoder stops there, whatever follows

def magic_ne(+b: U32, +w: U32, e: {U32.is_eq(B.byte(b), w) == False{} : Bool}) -> {U32.is_eq(B.byte(B.byte(b)), w) == False{} : Bool}:
  %byte_idem(b) : {U32.is_eq(_, w) == False{} : Bool}
  e

# the first stream's header fails with err: the decoder fails with it
def first_fails(+n: Nat, +h: U32, +t: List<&2, U32>, +room: Nat, +ignore: Bool, -err: E.Bzip2Error, +e: {S.stream_header(Con{h, t}) == Fail{err} : Result<&2, &2, E.Bzip2Error, S.Bzip2Head>}) -> {S.dec.go(1n+1n+n, S.Bzip2DecHead{Con{h, t}, True{}, room, Nil{}}, ignore) == S.Bzip2DecBad{err} : S.Bzip2Dec}:
  %Equal.sym(Result<&2, &2, E.Bzip2Error, S.Bzip2Head>, S.stream_header(Con{h, t}), Fail{err}, e) : {S.dec.go(1n+n, S.dec.head(_, True{}, ignore, room, Nil{}), ignore) == S.Bzip2DecBad{err} : S.Bzip2Dec}
  {==}

def hdr1(+h: U32, +t: List<&2, U32>, e: {U32.is_eq(B.byte(h), 66) == False{} : Bool}) -> {S.stream_header(Con{h, t}) == Fail{E.Bzip2BadMagic{}} : Result<&2, &2, E.Bzip2Error, S.Bzip2Head>}:
  %Equal.sym(Bool, U32.is_eq(B.byte(h), 66), False{}, e) : {S.hdr.magic([90, 104], _, t) == Fail{E.Bzip2BadMagic{}} : Result<&2, &2, E.Bzip2Error, S.Bzip2Head>}
  {==}

def hdr2(+h: U32, +t: List<&2, U32>, e: {U32.is_eq(B.byte(h), 90) == False{} : Bool}) -> {S.stream_header(Con{66, Con{h, t}}) == Fail{E.Bzip2BadMagic{}} : Result<&2, &2, E.Bzip2Error, S.Bzip2Head>}:
  %Equal.sym(Bool, U32.is_eq(B.byte(h), 90), False{}, e) : {S.hdr.magic([104], _, t) == Fail{E.Bzip2BadMagic{}} : Result<&2, &2, E.Bzip2Error, S.Bzip2Head>}
  {==}

def hdr3(+h: U32, +t: List<&2, U32>, e: {U32.is_eq(B.byte(h), 104) == False{} : Bool}) -> {S.stream_header(Con{66, Con{90, Con{h, t}}}) == Fail{E.Bzip2BadMagic{}} : Result<&2, &2, E.Bzip2Error, S.Bzip2Head>}:
  %Equal.sym(Bool, U32.is_eq(B.byte(h), 104), False{}, e) : {S.hdr.magic(Nil{}, _, t) == Fail{E.Bzip2BadMagic{}} : Result<&2, &2, E.Bzip2Error, S.Bzip2Head>}
  {==}

# a stream whose header fails with err, as the decoder's whole answer
def run_fails(+xs: List<&2, U32>, +max: U32, +ignore: Bool, -err: E.Bzip2Error, e: {S.dec.go(1n+1n+L.bz.len(xs), S.Bzip2DecHead{xs, True{}, U32.to_nat(max), Nil{}}, ignore) == S.Bzip2DecBad{err} : S.Bzip2Dec}) -> {S.stm.run(xs, max, ignore) == Fail{err} : Result<&2, &2, E.Bzip2Error, B.Octets>}:
  %Equal.sym(S.Bzip2Dec, S.dec.go(1n+1n+L.bz.len(xs), S.Bzip2DecHead{xs, True{}, U32.to_nat(max), Nil{}}, ignore), S.Bzip2DecBad{err}, e) : {S.stm.bound(max, S.dec.result(_)) == Fail{err} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  {==}

def Laws.bad_magic_1(opts, b, xs, e):
  match opts:
    case S.Bzip2Options{+max, +ignore}:
      %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(Con{b, xs})), B.mask(Con{b, xs}), BL.octets_to_of(Con{b, xs})) : {S.stm.run(_, max, ignore) == Fail{E.Bzip2BadMagic{}} : Result<&2, &2, E.Bzip2Error, B.Octets>}
      run_fails(Con{B.byte(b), B.mask(xs)}, max, ignore, E.Bzip2BadMagic{}, first_fails(L.bz.len.go(B.mask(xs), 1n), B.byte(b), B.mask(xs), U32.to_nat(max), ignore, E.Bzip2BadMagic{}, hdr1(B.byte(b), B.mask(xs), magic_ne(b, 66, e))))

def Laws.bad_magic_2(opts, b, xs, e):
  match opts:
    case S.Bzip2Options{+max, +ignore}:
      %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(Con{66, Con{b, xs}})), B.mask(Con{66, Con{b, xs}}), BL.octets_to_of(Con{66, Con{b, xs}})) : {S.stm.run(_, max, ignore) == Fail{E.Bzip2BadMagic{}} : Result<&2, &2, E.Bzip2Error, B.Octets>}
      run_fails(Con{66, Con{B.byte(b), B.mask(xs)}}, max, ignore, E.Bzip2BadMagic{}, first_fails(L.bz.len.go(Con{B.byte(b), B.mask(xs)}, 1n), 66, Con{B.byte(b), B.mask(xs)}, U32.to_nat(max), ignore, E.Bzip2BadMagic{}, hdr2(B.byte(b), B.mask(xs), magic_ne(b, 90, e))))

def Laws.bad_magic_3(opts, b, xs, e):
  match opts:
    case S.Bzip2Options{+max, +ignore}:
      %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(Con{66, Con{90, Con{b, xs}}})), B.mask(Con{66, Con{90, Con{b, xs}}}), BL.octets_to_of(Con{66, Con{90, Con{b, xs}}})) : {S.stm.run(_, max, ignore) == Fail{E.Bzip2BadMagic{}} : Result<&2, &2, E.Bzip2Error, B.Octets>}
      run_fails(Con{66, Con{90, Con{B.byte(b), B.mask(xs)}}}, max, ignore, E.Bzip2BadMagic{}, first_fails(L.bz.len.go(Con{90, Con{B.byte(b), B.mask(xs)}}, 1n), 66, Con{90, Con{B.byte(b), B.mask(xs)}}, U32.to_nat(max), ignore, E.Bzip2BadMagic{}, hdr3(B.byte(b), B.mask(xs), magic_ne(b, 104, e))))


# RLE1
#
# The fast forms are the structural ones with an accumulator (push_push).

def enc_fast(xs: List<&2, U32>, +r: R.Bzip2Rle1Run, +acc: List<&2, U32>) -> {R.rle1.enc.fast(xs, r, acc) == L.bz.push(acc, R.rle1.enc(xs, r)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      rev_push(R.rle1.emit.run(r), acc)
    case Con{+y, +t}:
      +e = R.rle1.enc.step(y, r)
      Equal.trans(List<&2, U32>, R.rle1.enc.fast(t, R.rle1.emit.next(e), L.bz.push(R.rle1.emit.out(e), acc)), L.bz.push(L.bz.push(R.rle1.emit.out(e), acc), R.rle1.enc(t, R.rle1.emit.next(e))), L.bz.push(acc, L.bz.app(R.rle1.emit.out(e), R.rle1.enc(t, R.rle1.emit.next(e)))), enc_fast(t, R.rle1.emit.next(e), L.bz.push(R.rle1.emit.out(e), acc)), push_push(R.rle1.emit.out(e), acc, R.rle1.enc(t, R.rle1.emit.next(e))))

def dec_fast(ys: List<&2, U32>, +s: R.Bzip2Rle1Dec, +acc: List<&2, U32>) -> {R.rle1.dec.fast(ys, s, acc) == L.bz.push(acc, R.rle1.dec(ys, s)) : List<&2, U32>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      +o = R.rle1.dec.step(y, s)
      Equal.trans(List<&2, U32>, R.rle1.dec.fast(t, R.rle1.out.next(o), L.bz.push(R.rle1.out.out(o), acc)), L.bz.push(L.bz.push(R.rle1.out.out(o), acc), R.rle1.dec(t, R.rle1.out.next(o))), L.bz.push(acc, L.bz.app(R.rle1.out.out(o), R.rle1.dec(t, R.rle1.out.next(o)))), dec_fast(t, R.rle1.out.next(o), L.bz.push(R.rle1.out.out(o), acc)), push_push(R.rle1.out.out(o), acc, R.rle1.dec(t, R.rle1.out.next(o))))

# the decoder masks what it reads, so a masked input decodes the same
def dec_mask(ys: List<&2, U32>, +s: R.Bzip2Rle1Dec) -> {R.rle1.dec(B.mask(ys), s) == R.rle1.dec(ys, s) : List<&2, U32>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %byte_idem(y) : {L.bz.app(R.rle1.out.out(R.rle1.dec.step.b(_, s)), R.rle1.dec(B.mask(t), R.rle1.out.next(R.rle1.dec.step.b(_, s)))) == L.bz.app(R.rle1.out.out(R.rle1.dec.step.b(B.byte(y), s)), R.rle1.dec(t, R.rle1.out.next(R.rle1.dec.step.b(B.byte(y), s)))) : List<&2, U32>}
      +o = R.rle1.dec.step.b(B.byte(y), s)
      Equal.cong(List<&2, U32>, List<&2, U32>, x => L.bz.app(R.rle1.out.out(o), x), R.rle1.dec(B.mask(t), R.rle1.out.next(o)), R.rle1.dec(t, R.rle1.out.next(o)), dec_mask(t, R.rle1.out.next(o)))

# The decoder's state before a run of h: fresh (0), or 1 to 3 of a byte
# other than h
def compat(+last: U32, n: Nat, +h: U32) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+n1:
      match n1:
        case 0n:
          Bool.not(U32.is_eq(h, last))
        case 1n+n2:
          match n2:
            case 0n:
              Bool.not(U32.is_eq(h, last))
            case 1n+n3:
              match n3:
                case 0n:
                  Bool.not(U32.is_eq(h, last))
                case 1n+n4:
                  False{}

# the state after a run of k copies of h
def after(k: Nat, +h: U32, last: U32, n: Nat) -> R.Bzip2Rle1Dec:
  match k:
    case 0n:
      R.Bzip2Rle1Dec{last, n}
    case 1n+k1:
      match k1:
        case 0n:
          R.Bzip2Rle1Dec{h, 1n}
        case 1n+k2:
          match k2:
            case 0n:
              R.Bzip2Rle1Dec{h, 2n}
            case 1n+k3:
              match k3:
                case 0n:
                  R.Bzip2Rle1Dec{h, 3n}
                case 1n+m:
                  R.Bzip2Rle1Dec{h, 0n}

# the first byte of a run, from a compatible state
def first(+h: U32, +last: U32, n: Nat, ch: {compat(last, n, h) == True{} : Bool}) -> {R.Bzip2Rle1Out{[h], R.Bzip2Rle1Dec{h, 1n}} == R.rle1.dec.step.b(h, R.Bzip2Rle1Dec{last, n}) : R.Bzip2Rle1Out}:
  match n:
    case 0n:
      {==}
    case 1n+n1:
      match n1:
        case 0n:
          %not_true(U32.is_eq(h, last), ch) : {R.Bzip2Rle1Out{[h], R.Bzip2Rle1Dec{h, 1n}} == R.rle1.dec.lit(_, h, last, 2n) : R.Bzip2Rle1Out}
          {==}
        case 1n+n2:
          match n2:
            case 0n:
              %not_true(U32.is_eq(h, last), ch) : {R.Bzip2Rle1Out{[h], R.Bzip2Rle1Dec{h, 1n}} == R.rle1.dec.lit(_, h, last, 3n) : R.Bzip2Rle1Out}
              {==}
            case 1n+n3:
              match n3:
                case 0n:
                  %not_true(U32.is_eq(h, last), ch) : {R.Bzip2Rle1Out{[h], R.Bzip2Rle1Dec{h, 1n}} == R.rle1.dec.lit(_, h, last, 4n) : R.Bzip2Rle1Out}
                  {==}
                case 1n+n4:
                  Empty.absurd({R.Bzip2Rle1Out{[h], R.Bzip2Rle1Dec{h, 1n}} == R.rle1.dec.step.b(h, R.Bzip2Rle1Dec{last, 1n+1n+1n+1n+n4}) : R.Bzip2Rle1Out}, absurd.ft(ch))

# one more byte of the run (from j to j + 1 in a row)
def more(+h: U32, +j: Nat) -> {R.Bzip2Rle1Out{[h], R.Bzip2Rle1Dec{h, 1n+j}} == R.rle1.dec.lit(U32.is_eq(h, h), h, h, 1n+j) : R.Bzip2Rle1Out}:
  %u32_eq_self_r(h) : {R.Bzip2Rle1Out{[h], R.Bzip2Rle1Dec{h, 1n+j}} == R.rle1.dec.lit(_, h, h, 1n+j) : R.Bzip2Rle1Out}
  {==}

# decoding steps, as rewrites (the decoded form == the decoder's term)
def d1(+h: U32, +last: U32, +n: Nat, +rs: List<&2, U32>, ch: {compat(last, n, h) == True{} : Bool}, hm: {h == B.byte(h) : U32}) -> {Con{h, R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 1n})} == R.rle1.dec(Con{h, rs}, R.Bzip2Rle1Dec{last, n}) : List<&2, U32>}:
  %hm : {Con{h, R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 1n})} == L.bz.app(R.rle1.out.out(R.rle1.dec.step.b(_, R.Bzip2Rle1Dec{last, n})), R.rle1.dec(rs, R.rle1.out.next(R.rle1.dec.step.b(_, R.Bzip2Rle1Dec{last, n})))) : List<&2, U32>}
  %first(h, last, n, ch) : {Con{h, R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 1n})} == L.bz.app(R.rle1.out.out(_), R.rle1.dec(rs, R.rle1.out.next(_))) : List<&2, U32>}
  {==}

def d2(+h: U32, +j: Nat, +rs: List<&2, U32>, hm: {h == B.byte(h) : U32}, lit: {R.Bzip2Rle1Out{[h], R.Bzip2Rle1Dec{h, 1n+j}} == R.rle1.dec.step.b(h, R.Bzip2Rle1Dec{h, j}) : R.Bzip2Rle1Out}) -> {Con{h, R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 1n+j})} == R.rle1.dec(Con{h, rs}, R.Bzip2Rle1Dec{h, j}) : List<&2, U32>}:
  %hm : {Con{h, R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 1n+j})} == L.bz.app(R.rle1.out.out(R.rle1.dec.step.b(_, R.Bzip2Rle1Dec{h, j})), R.rle1.dec(rs, R.rle1.out.next(R.rle1.dec.step.b(_, R.Bzip2Rle1Dec{h, j})))) : List<&2, U32>}
  %lit : {Con{h, R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 1n+j})} == L.bz.app(R.rle1.out.out(_), R.rle1.dec(rs, R.rle1.out.next(_))) : List<&2, U32>}
  {==}

# the count byte after four in a row
def d4(+h: U32, +m: Nat, +rs: List<&2, U32>, mb: {Nat.is_le(m, 251n) == True{} : Bool}) -> {L.bz.app(L.bz.rep(m, h), R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 0n})) == R.rle1.dec(Con{U32.from_nat(m), rs}, R.Bzip2Rle1Dec{h, 4n}) : List<&2, U32>}:
  %small.k0(m, mb) : {L.bz.app(L.bz.rep(m, h), R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 0n})) == L.bz.app(L.bz.rep(_, h), R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 0n})) : List<&2, U32>}
  {==}

# A run, emitted and decoded from a compatible state, comes back, and leaves
# the state after it
def e0(k: Nat, +h: U32, +last: U32, +n: Nat, +rs: List<&2, U32>, ch: {compat(last, n, h) == True{} : Bool}, kb: {Nat.is_le(k, 255n) == True{} : Bool}, +hm: {h == B.byte(h) : U32}) -> {R.rle1.dec(L.bz.app(R.rle1.emit(k, h), rs), R.Bzip2Rle1Dec{last, n}) == L.bz.app(L.bz.rep(k, h), R.rle1.dec(rs, after(k, h, last, n))) : List<&2, U32>}:
  match k:
    case 0n:
      {==}
    case 1n+k1:
      match k1:
        case 0n:
          Equal.sym(List<&2, U32>, Con{h, R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 1n})}, R.rle1.dec(Con{h, rs}, R.Bzip2Rle1Dec{last, n}), d1(h, last, n, rs, ch, hm))
        case 1n+k2:
          match k2:
            case 0n:
              %d1(h, last, n, Con{h, rs}, ch, hm) : {_ == L.bz.app(L.bz.rep(2n, h), R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 2n})) : List<&2, U32>}
              %d2(h, 1n, rs, hm, more(h, 1n)) : {Con{h, _} == L.bz.app(L.bz.rep(2n, h), R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 2n})) : List<&2, U32>}
              {==}
            case 1n+k3:
              match k3:
                case 0n:
                  %d1(h, last, n, Con{h, Con{h, rs}}, ch, hm) : {_ == L.bz.app(L.bz.rep(3n, h), R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 3n})) : List<&2, U32>}
                  %d2(h, 1n, Con{h, rs}, hm, more(h, 1n)) : {Con{h, _} == L.bz.app(L.bz.rep(3n, h), R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 3n})) : List<&2, U32>}
                  %d2(h, 2n, rs, hm, more(h, 2n)) : {Con{h, Con{h, _}} == L.bz.app(L.bz.rep(3n, h), R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 3n})) : List<&2, U32>}
                  {==}
                case 1n+(+m):
                  +c = {Con{U32.from_nat(m), rs} : List<&2, U32>}
                  %d1(h, last, n, Con{h, Con{h, Con{h, c}}}, ch, hm) : {_ == L.bz.app(L.bz.rep(1n+1n+1n+1n+m, h), R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 0n})) : List<&2, U32>}
                  %d2(h, 1n, Con{h, Con{h, c}}, hm, more(h, 1n)) : {Con{h, _} == L.bz.app(L.bz.rep(1n+1n+1n+1n+m, h), R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 0n})) : List<&2, U32>}
                  %d2(h, 2n, Con{h, c}, hm, more(h, 2n)) : {Con{h, Con{h, _}} == L.bz.app(L.bz.rep(1n+1n+1n+1n+m, h), R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 0n})) : List<&2, U32>}
                  %d2(h, 3n, c, hm, more(h, 3n)) : {Con{h, Con{h, Con{h, _}}} == L.bz.app(L.bz.rep(1n+1n+1n+1n+m, h), R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 0n})) : List<&2, U32>}
                  %d4(h, m, rs, kb) : {Con{h, Con{h, Con{h, Con{h, _}}}} == L.bz.app(L.bz.rep(1n+1n+1n+1n+m, h), R.rle1.dec(rs, R.Bzip2Rle1Dec{h, 0n})) : List<&2, U32>}
                  {==}


# The round trip. The encoder holds a run (h, k) not yet emitted; the
# decoder is in a state compatible with h. The step on the next byte y
# either lengthens the run (y is h and k < 255) or emits it and starts a run
# of y; ih1 and ih2 are the induction hypotheses for those two cases.

def compatd(+s: R.Bzip2Rle1Dec, +h: U32) -> Bool:
  match s:
    case R.Bzip2Rle1Dec{last, n}:
      compat(last, n, h)

# after a run that was cut (y differs, or 255 in a row), the state suits y
def rl_ch2(+k1: Nat, +h: U32, +by: U32, +last: U32, +n: Nat, +q: Bool, +eq: {q == U32.is_eq(by, h) : Bool}, +brk: {Bool.and(q, Nat.is_lt(1n+k1, 255n)) == False{} : Bool}) -> {compatd(after(1n+k1, h, last, n), by) == True{} : Bool}:
  match k1:
    case 0n:
      match q:
        case True{}:
          Empty.absurd({compatd(after(1n, h, last, n), by) == True{} : Bool}, absurd.tf(brk))
        case False{}:
          %eq : {Bool.not(_) == True{} : Bool}
          {==}
    case 1n+k2:
      match k2:
        case 0n:
          match q:
            case True{}:
              Empty.absurd({compatd(after(2n, h, last, n), by) == True{} : Bool}, absurd.tf(brk))
            case False{}:
              %eq : {Bool.not(_) == True{} : Bool}
              {==}
        case 1n+k3:
          match k3:
            case 0n:
              match q:
                case True{}:
                  Empty.absurd({compatd(after(3n, h, last, n), by) == True{} : Bool}, absurd.tf(brk))
                case False{}:
                  %eq : {Bool.not(_) == True{} : Bool}
                  {==}
            case 1n+m:
              {==}

def rl_brk(+k1: Nat, +h: U32, +by: U32, +last: U32, +n: Nat, +t: List<&2, U32>, +q: Bool, +eq: {q == U32.is_eq(by, h) : Bool}, +ch: {compat(last, n, h) == True{} : Bool}, +kb: {Nat.is_le(1n+k1, 255n) == True{} : Bool}, +hm: {h == B.byte(h) : U32}, +brk: {Bool.and(q, Nat.is_lt(1n+k1, 255n)) == False{} : Bool}, ih2: {compatd(after(1n+k1, h, last, n), by) == True{} : Bool} -> {R.rle1.dec(R.rle1.enc(t, R.Bzip2Rle1Run{by, 1n}), after(1n+k1, h, last, n)) == Con{by, B.mask(t)} : List<&2, U32>}) -> {R.rle1.dec(L.bz.app(R.rle1.emit(1n+k1, h), R.rle1.enc(t, R.Bzip2Rle1Run{by, 1n})), R.Bzip2Rle1Dec{last, n}) == L.bz.app(L.bz.rep(1n+k1, h), Con{by, B.mask(t)}) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, R.rle1.dec(L.bz.app(R.rle1.emit(1n+k1, h), R.rle1.enc(t, R.Bzip2Rle1Run{by, 1n})), R.Bzip2Rle1Dec{last, n}), L.bz.app(L.bz.rep(1n+k1, h), R.rle1.dec(R.rle1.enc(t, R.Bzip2Rle1Run{by, 1n}), after(1n+k1, h, last, n))), L.bz.app(L.bz.rep(1n+k1, h), Con{by, B.mask(t)}), e0(1n+k1, h, last, n, R.rle1.enc(t, R.Bzip2Rle1Run{by, 1n}), ch, kb, hm), Equal.cong(List<&2, U32>, List<&2, U32>, x => L.bz.app(L.bz.rep(1n+k1, h), x), R.rle1.dec(R.rle1.enc(t, R.Bzip2Rle1Run{by, 1n}), after(1n+k1, h, last, n)), Con{by, B.mask(t)}, ih2(rl_ch2(k1, h, by, last, n, q, eq, brk))))

# the run goes on: y is h, and fewer than 255 so far
def rl_cont(+k1: Nat, +h: U32, +by: U32, +last: U32, +n: Nat, +t: List<&2, U32>, +eq: {True{} == U32.is_eq(by, h) : Bool}, +ep: {True{} == Nat.is_lt(1n+k1, 255n) : Bool}, ih1: {Nat.is_le(1n+1n+k1, 255n) == True{} : Bool} -> {R.rle1.dec(R.rle1.enc(t, R.Bzip2Rle1Run{h, 1n+1n+k1}), R.Bzip2Rle1Dec{last, n}) == L.bz.app(L.bz.rep(1n+1n+k1, h), B.mask(t)) : List<&2, U32>}) -> {R.rle1.dec(R.rle1.enc(t, R.Bzip2Rle1Run{h, 1n+1n+k1}), R.Bzip2Rle1Dec{last, n}) == L.bz.app(L.bz.rep(1n+k1, h), Con{by, B.mask(t)}) : List<&2, U32>}:
  +kb2 = Equal.trans(Bool, Nat.is_le(1n+1n+k1, 255n), Nat.is_lt(1n+k1, 255n), True{}, Equal.sym(Bool, Nat.is_lt(1n+k1, 1n+254n), Nat.is_le(1n+k1, 254n), nat_lt_succ(1n+k1, 254n)), Equal.sym(Bool, True{}, Nat.is_lt(1n+k1, 255n), ep))
  %Equal.sym(U32, by, h, u32_eq(by, h, Equal.sym(Bool, True{}, U32.is_eq(by, h), eq))) : {R.rle1.dec(R.rle1.enc(t, R.Bzip2Rle1Run{h, 1n+1n+k1}), R.Bzip2Rle1Dec{last, n}) == L.bz.app(L.bz.rep(1n+k1, h), Con{_, B.mask(t)}) : List<&2, U32>}
  Equal.trans(List<&2, U32>, R.rle1.dec(R.rle1.enc(t, R.Bzip2Rle1Run{h, 1n+1n+k1}), R.Bzip2Rle1Dec{last, n}), L.bz.app(L.bz.rep(1n+1n+k1, h), B.mask(t)), L.bz.app(L.bz.rep(1n+k1, h), Con{h, B.mask(t)}), ih1(kb2), Equal.sym(List<&2, U32>, L.bz.app(L.bz.rep(1n+k1, h), Con{h, B.mask(t)}), Con{h, L.bz.app(L.bz.rep(1n+k1, h), B.mask(t))}, rep_snoc(1n+k1, h, B.mask(t))))

def rl_qp(+q: Bool, +p: Bool, +k1: Nat, +h: U32, +by: U32, +last: U32, +n: Nat, +t: List<&2, U32>, +eq: {q == U32.is_eq(by, h) : Bool}, +ep: {p == Nat.is_lt(1n+k1, 255n) : Bool}, +ch: {compat(last, n, h) == True{} : Bool}, +kb: {Nat.is_le(1n+k1, 255n) == True{} : Bool}, +hm: {h == B.byte(h) : U32}, ih1: {Nat.is_le(1n+1n+k1, 255n) == True{} : Bool} -> {R.rle1.dec(R.rle1.enc(t, R.Bzip2Rle1Run{h, 1n+1n+k1}), R.Bzip2Rle1Dec{last, n}) == L.bz.app(L.bz.rep(1n+1n+k1, h), B.mask(t)) : List<&2, U32>}, ih2: {compatd(after(1n+k1, h, last, n), by) == True{} : Bool} -> {R.rle1.dec(R.rle1.enc(t, R.Bzip2Rle1Run{by, 1n}), after(1n+k1, h, last, n)) == Con{by, B.mask(t)} : List<&2, U32>}) -> {R.rle1.dec(L.bz.app(R.rle1.emit.out(R.rle1.enc.pick(Bool.and(q, p), by, h, 1n+k1)), R.rle1.enc(t, R.rle1.emit.next(R.rle1.enc.pick(Bool.and(q, p), by, h, 1n+k1)))), R.Bzip2Rle1Dec{last, n}) == L.bz.app(L.bz.rep(1n+k1, h), Con{by, B.mask(t)}) : List<&2, U32>}:
  match q:
    case True{}:
      match p:
        case True{}:
          rl_cont(k1, h, by, last, n, t, eq, ep, ih1)
        case False{}:
          %ep : {R.rle1.dec(L.bz.app(R.rle1.emit(1n+k1, h), R.rle1.enc(t, R.Bzip2Rle1Run{by, 1n})), R.Bzip2Rle1Dec{last, n}) == L.bz.app(L.bz.rep(1n+k1, h), Con{by, B.mask(t)}) : List<&2, U32>}
          rl_brk(k1, h, by, last, n, t, True{}, eq, ch, kb, hm, Equal.sym(Bool, False{}, Nat.is_lt(1n+k1, 255n), ep), ih2)
    case False{}:
      rl_brk(k1, h, by, last, n, t, False{}, eq, ch, kb, hm, {==}, ih2)

def rl_step(+k1: Nat, +h: U32, +y: U32, +last: U32, +n: Nat, +t: List<&2, U32>, +ch: {compat(last, n, h) == True{} : Bool}, +kb: {Nat.is_le(1n+k1, 255n) == True{} : Bool}, +hm: {h == B.byte(h) : U32}, ih1: {Nat.is_le(1n+1n+k1, 255n) == True{} : Bool} -> {R.rle1.dec(R.rle1.enc(t, R.Bzip2Rle1Run{h, 1n+1n+k1}), R.Bzip2Rle1Dec{last, n}) == L.bz.app(L.bz.rep(1n+1n+k1, h), B.mask(t)) : List<&2, U32>}, ih2: {compatd(after(1n+k1, h, last, n), B.byte(y)) == True{} : Bool} -> {R.rle1.dec(R.rle1.enc(t, R.Bzip2Rle1Run{B.byte(y), 1n}), after(1n+k1, h, last, n)) == Con{B.byte(y), B.mask(t)} : List<&2, U32>}) -> {R.rle1.dec(R.rle1.enc(Con{y, t}, R.Bzip2Rle1Run{h, 1n+k1}), R.Bzip2Rle1Dec{last, n}) == L.bz.app(L.bz.rep(1n+k1, h), B.mask(Con{y, t})) : List<&2, U32>}:
  rl_qp(U32.is_eq(B.byte(y), h), Nat.is_lt(1n+k1, 255n), k1, h, B.byte(y), last, n, t, {==}, {==}, ch, kb, hm, ih1, ih2)

def rl(+xs: List<&2, U32>, +h: U32, +k1: Nat, +s: R.Bzip2Rle1Dec, +ch: {compatd(s, h) == True{} : Bool}, +kb: {Nat.is_le(1n+k1, 255n) == True{} : Bool}, +hm: {h == B.byte(h) : U32}) -> {R.rle1.dec(R.rle1.enc(xs, R.Bzip2Rle1Run{h, 1n+k1}), s) == L.bz.app(L.bz.rep(1n+k1, h), B.mask(xs)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      match s:
        case R.Bzip2Rle1Dec{+last, +n}:
          %app_nil(R.rle1.emit(1n+k1, h)) : {R.rle1.dec(_, R.Bzip2Rle1Dec{last, n}) == L.bz.app(L.bz.rep(1n+k1, h), Nil{}) : List<&2, U32>}
          e0(1n+k1, h, last, n, Nil{}, ch, kb, hm)
    case Con{+y, +t}:
      match s:
        case R.Bzip2Rle1Dec{+last, +n}:
          rl_step(k1, h, y, last, n, t, ch, kb, hm, kb2 => rl(t, h, 1n+k1, R.Bzip2Rle1Dec{last, n}, ch, kb2, hm), ch2 => rl(t, B.byte(y), 0n, after(1n+k1, h, last, n), ch2, {==}, byte_idem(y)))

# from the start: no run, a fresh decoder
def top_q(+q: Bool, +y: U32, +t: List<&2, U32>, +eq: {q == U32.is_eq(B.byte(y), 0) : Bool}, +iha: {R.rle1.dec(R.rle1.enc(t, R.Bzip2Rle1Run{0, 1n}), R.Bzip2Rle1Dec{0, 0n}) == Con{0, B.mask(t)} : List<&2, U32>}, +ihb: {R.rle1.dec(R.rle1.enc(t, R.Bzip2Rle1Run{B.byte(y), 1n}), R.Bzip2Rle1Dec{0, 0n}) == Con{B.byte(y), B.mask(t)} : List<&2, U32>}) -> {R.rle1.dec(L.bz.app(R.rle1.emit.out(R.rle1.enc.pick(Bool.and(q, True{}), B.byte(y), 0, 0n)), R.rle1.enc(t, R.rle1.emit.next(R.rle1.enc.pick(Bool.and(q, True{}), B.byte(y), 0, 0n)))), R.Bzip2Rle1Dec{0, 0n}) == Con{B.byte(y), B.mask(t)} : List<&2, U32>}:
  match q:
    case True{}:
      %Equal.sym(U32, B.byte(y), 0, u32_eq(B.byte(y), 0, Equal.sym(Bool, True{}, U32.is_eq(B.byte(y), 0), eq))) : {R.rle1.dec(R.rle1.enc(t, R.Bzip2Rle1Run{0, 1n}), R.Bzip2Rle1Dec{0, 0n}) == Con{_, B.mask(t)} : List<&2, U32>}
      iha
    case False{}:
      ihb

def top(+xs: List<&2, U32>) -> {R.rle1.dec(R.rle1.enc(xs, R.rle1.enc.start()), R.rle1.dec.start()) == B.mask(xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      top_q(U32.is_eq(B.byte(y), 0), y, t, {==}, rl(t, 0, 0n, R.Bzip2Rle1Dec{0, 0n}, {==}, {==}, {==}), rl(t, B.byte(y), 0n, R.Bzip2Rle1Dec{0, 0n}, {==}, {==}, byte_idem(y)))

def Laws.rle1_round_trip(o):
  +xs = B.Octets.to_list(o)
  +e = R.rle1.enc(xs, R.rle1.enc.start())
  %Equal.sym(List<&2, U32>, R.rle1.enc.fast(xs, R.rle1.enc.start(), Nil{}), e, enc_fast(xs, R.rle1.enc.start(), Nil{})) : {B.Octets.of_list(R.rle1.dec.fast(B.Octets.to_list(B.Octets.of_list(_)), R.rle1.dec.start(), Nil{})) == o : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(e)), B.mask(e), BL.octets_to_of(e)) : {B.Octets.of_list(R.rle1.dec.fast(_, R.rle1.dec.start(), Nil{})) == o : B.Octets}
  %Equal.sym(List<&2, U32>, R.rle1.dec.fast(B.mask(e), R.rle1.dec.start(), Nil{}), R.rle1.dec(B.mask(e), R.rle1.dec.start()), dec_fast(B.mask(e), R.rle1.dec.start(), Nil{})) : {B.Octets.of_list(_) == o : B.Octets}
  %Equal.sym(List<&2, U32>, R.rle1.dec(B.mask(e), R.rle1.dec.start()), R.rle1.dec(e, R.rle1.dec.start()), dec_mask(e, R.rle1.dec.start())) : {B.Octets.of_list(_) == o : B.Octets}
  %Equal.sym(List<&2, U32>, R.rle1.dec(e, R.rle1.dec.start()), B.mask(xs), top(xs)) : {B.Octets.of_list(_) == o : B.Octets}
  %BL.octets_to_of(xs) : {B.Octets.of_list(_) == o : B.Octets}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(B.Octets.of_list(xs))), B.Octets.of_list(xs), BL.octets_of_list_idempotent(xs)) : {_ == o : B.Octets}
  BL.octets_of_to(o)


# Move-to-front and RLE2
#
# Nat arithmetic

def add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, add_zero(p))

def add_succ_r(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 1n+b), 1n+Nat.add(p, b), add_succ_r(p, b))

def add_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), add_assoc(p, b, c))

def sub_add(a: Nat, +x: Nat) -> {Nat.sub(Nat.add(a, x), a) == x : Nat}:
  match a:
    case 0n:
      match x:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      sub_add(p, x)

def le_add(a: Nat, +x: Nat) -> {Nat.is_le(a, Nat.add(a, x)) == True{} : Bool}:
  match a:
    case 0n:
      match x:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      le_add(p, x)

def le_self(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      le_self(p)

def nat_eq_self(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      nat_eq_self(p)

def le_zero(r: Nat) -> {Nat.is_le(0n, r) == True{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+q:
      {==}

# i + 1 <= j: i is not j
def le_succ_ne(i: Nat, j: Nat, e: {Nat.is_le(1n+i, j) == True{} : Bool}) -> {Nat.is_eq(i, j) == False{} : Bool}:
  match i:
    case 0n:
      match j:
        case 0n:
          Empty.absurd({Nat.is_eq(0n, 0n) == False{} : Bool}, absurd.ft(e))
        case 1n+q:
          {==}
    case 1n+p:
      match j:
        case 0n:
          Empty.absurd({Nat.is_eq(1n+p, 0n) == False{} : Bool}, absurd.ft(e))
        case 1n+q:
          le_succ_ne(p, q, e)

# i + 1 <= j: i <= j
def le_succ_l(i: Nat, j: Nat, e: {Nat.is_le(1n+i, j) == True{} : Bool}) -> {Nat.is_le(i, j) == True{} : Bool}:
  match i:
    case 0n:
      le_zero(j)
    case 1n+p:
      match j:
        case 0n:
          Empty.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, absurd.ft(e))
        case 1n+q:
          le_succ_l(p, q, e)

def lt_add_succ(i: Nat, +l: Nat) -> {Nat.is_lt(i, Nat.add(i, 1n+l)) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      lt_add_succ(p, l)

# a < b <= c: a + 1 <= c
def lt_le(a: Nat, b: Nat, c: Nat, e1: {Nat.is_lt(a, b) == True{} : Bool}, e2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(1n+a, c) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n, c) == True{} : Bool}, absurd.ft(e1))
        case 1n+q:
          match c:
            case 0n:
              Empty.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, absurd.ft(e2))
            case 1n+r:
              le_zero(r)
    case 1n+p:
      match b:
        case 0n:
          Empty.absurd({Nat.is_le(1n+1n+p, c) == True{} : Bool}, absurd.ft(e1))
        case 1n+q:
          match c:
            case 0n:
              Empty.absurd({Nat.is_le(1n+1n+p, 0n) == True{} : Bool}, absurd.ft(e2))
            case 1n+r:
              lt_le(p, q, r, e1, e2)

# Lists

def app_one(a: List<&2, U32>, +x: U32, +b: List<&2, U32>) -> {L.bz.app(L.bz.app(a, [x]), b) == L.bz.app(a, Con{x, b}) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, t}:
      Equal.cong(List<&2, U32>, List<&2, U32>, z => Con{h, z}, L.bz.app(L.bz.app(t, [x]), b), L.bz.app(t, Con{x, b}), app_one(t, x, b))

def len_push(p: List<&2, U32>, +ys: List<&2, U32>) -> {B.len(L.bz.push(p, ys)) == Nat.add(B.len(p), B.len(ys)) : Nat}:
  match p:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Equal.trans(Nat, B.len(L.bz.push(t, Con{h, ys})), Nat.add(B.len(t), 1n+B.len(ys)), 1n+Nat.add(B.len(t), B.len(ys)), len_push(t, Con{h, ys}), add_succ_r(B.len(t), B.len(ys)))

# Membership, and its order not mattering

def mem.s(xs: List<&2, U32>, +x: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(U32.is_eq(h, x), mem.s(t, x))

def or_nil(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# a or (b or c) is (b or a) or c
def or_swap(a: Bool, b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(b, a), c) : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

# a or (b or c) is b or (a or c)
def or_comm3(a: Bool, b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

def mem_push(pre: List<&2, U32>, +ys: List<&2, U32>, +z: U32) -> {mem.s(L.bz.push(pre, ys), z) == Bool.or(mem.s(pre, z), mem.s(ys, z)) : Bool}:
  match pre:
    case Nil{}:
      {==}
    case Con{+p, +pt}:
      Equal.trans(Bool, mem.s(L.bz.push(pt, Con{p, ys}), z), Bool.or(mem.s(pt, z), Bool.or(U32.is_eq(p, z), mem.s(ys, z))), Bool.or(Bool.or(U32.is_eq(p, z), mem.s(pt, z)), mem.s(ys, z)), mem_push(pt, Con{p, ys}, z), or_swap(mem.s(pt, z), U32.is_eq(p, z), mem.s(ys, z)))

# the byte at the front, or where it was: the same members
def mem_perm(+h: U32, +pre: List<&2, U32>, +t: List<&2, U32>, +z: U32) -> {mem.s(Con{h, L.bz.push(pre, t)}, z) == mem.s(L.bz.push(pre, Con{h, t}), z) : Bool}:
  %Equal.sym(Bool, mem.s(L.bz.push(pre, t), z), Bool.or(mem.s(pre, z), mem.s(t, z)), mem_push(pre, t, z)) : {Bool.or(U32.is_eq(h, z), _) == mem.s(L.bz.push(pre, Con{h, t}), z) : Bool}
  %Equal.sym(Bool, mem.s(L.bz.push(pre, Con{h, t}), z), Bool.or(mem.s(pre, z), mem.s(Con{h, t}, z)), mem_push(pre, Con{h, t}, z)) : {Bool.or(U32.is_eq(h, z), Bool.or(mem.s(pre, z), mem.s(t, z))) == _ : Bool}
  or_comm3(U32.is_eq(h, z), mem.s(pre, z), mem.s(t, z))

# idx.go finds x exactly when x is a member

def idx_hit(t: List<&2, U32>, +i: Nat, +x: U32) -> {Some{i} == M.mtf.idx.go(t, M.Bzip2MtfHit{i}, x) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{h, r}:
      {==}

def idx_mem_q(q: Bool, +t: List<&2, U32>, +i: Nat, +x: U32, ih: {M.mtf.covers.has(M.mtf.idx.go(t, M.Bzip2MtfLook{1n+i}, x)) == mem.s(t, x) : Bool}) -> {M.mtf.covers.has(M.mtf.idx.go(t, M.mtf.idx.step(q, i), x)) == Bool.or(q, mem.s(t, x)) : Bool}:
  match q:
    case True{}:
      %idx_hit(t, i, x) : {M.mtf.covers.has(_) == True{} : Bool}
      {==}
    case False{}:
      ih

def idx_mem(xs: List<&2, U32>, +i: Nat, +x: U32) -> {M.mtf.covers.has(M.mtf.idx.go(xs, M.Bzip2MtfLook{i}, x)) == mem.s(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      idx_mem_q(U32.is_eq(h, x), t, i, x, idx_mem(t, 1n+i, x))

# covers depends only on the members
def covers_perm(xs: List<&2, U32>, +h: U32, +pre: List<&2, U32>, +t: List<&2, U32>) -> {M.mtf.covers(xs, Con{h, L.bz.push(pre, t)}) == M.mtf.covers(xs, L.bz.push(pre, Con{h, t})) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +ys}:
      +a = {Con{h, L.bz.push(pre, t)} : List<&2, U32>}
      +b = L.bz.push(pre, Con{h, t})
      +by = B.byte(y)
      %Equal.sym(Bool, M.mtf.covers.has(M.mtf.idx.go(a, M.Bzip2MtfLook{0n}, by)), mem.s(a, by), idx_mem(a, 0n, by)) : {Bool.and(_, M.mtf.covers(ys, a)) == Bool.and(M.mtf.covers.has(M.mtf.idx.go(b, M.Bzip2MtfLook{0n}, by)), M.mtf.covers(ys, b)) : Bool}
      %Equal.sym(Bool, M.mtf.covers.has(M.mtf.idx.go(b, M.Bzip2MtfLook{0n}, by)), mem.s(b, by), idx_mem(b, 0n, by)) : {Bool.and(mem.s(a, by), M.mtf.covers(ys, a)) == Bool.and(_, M.mtf.covers(ys, b)) : Bool}
      %mem_perm(h, pre, t, by) : {Bool.and(mem.s(a, by), M.mtf.covers(ys, a)) == Bool.and(_, M.mtf.covers(ys, b)) : Bool}
      Equal.cong(Bool, Bool, v => Bool.and(mem.s(a, by), v), M.mtf.covers(ys, a), M.mtf.covers(ys, b), covers_perm(ys, h, pre, t))

# What take answers, for the members and the length

def TkCov(m: Maybe<&2, M.Bzip2MtfTake>, xs: List<&2, U32>, +bs: List<&2, U32>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{t}:
      match t:
        case M.Bzip2MtfTake{x, r}:
          {M.mtf.covers(xs, Con{x, r}) == M.mtf.covers(xs, bs) : Bool}

def TkLen(m: Maybe<&2, M.Bzip2MtfTake>, +bs: List<&2, U32>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{t}:
      match t:
        case M.Bzip2MtfTake{x, r}:
          {B.len(Con{x, r}) == B.len(bs) : Nat}

def tk_cov(alpha: List<&2, U32>, here: Bool, +i: Nat, +pre: List<&2, U32>, +j: Nat, +xs: List<&2, U32>) -> TkCov(M.mtf.take.go(alpha, here, i, pre, j), xs, L.bz.push(pre, alpha)):
  match alpha:
    case Nil{}:
      Unit{}
    case Con{+h, +t}:
      match here:
        case True{}:
          covers_perm(xs, h, pre, t)
        case False{}:
          tk_cov(t, Nat.is_eq(1n+i, j), 1n+i, Con{h, pre}, j, xs)

def tk_len(alpha: List<&2, U32>, here: Bool, +i: Nat, +pre: List<&2, U32>, +j: Nat) -> TkLen(M.mtf.take.go(alpha, here, i, pre, j), L.bz.push(pre, alpha)):
  match alpha:
    case Nil{}:
      Unit{}
    case Con{+h, +t}:
      match here:
        case True{}:
          Equal.trans(Nat, 1n+B.len(L.bz.push(pre, t)), 1n+Nat.add(B.len(pre), B.len(t)), B.len(L.bz.push(pre, Con{h, t})), Equal.cong(Nat, Nat, v => 1n+v, B.len(L.bz.push(pre, t)), Nat.add(B.len(pre), B.len(t)), len_push(pre, t)), Equal.sym(Nat, B.len(L.bz.push(pre, Con{h, t})), 1n+Nat.add(B.len(pre), B.len(t)), Equal.trans(Nat, B.len(L.bz.push(pre, Con{h, t})), Nat.add(B.len(pre), 1n+B.len(t)), 1n+Nat.add(B.len(pre), B.len(t)), len_push(pre, Con{h, t}), add_succ_r(B.len(pre), B.len(t)))))
        case False{}:
          tk_len(t, Nat.is_eq(1n+i, j), 1n+i, Con{h, pre}, j)

# idx and take agree: take at the position idx finds is the byte found

def tk_ok(m: Maybe<&2, M.Bzip2MtfTake>, +x: U32) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{t}:
      match t:
        case M.Bzip2MtfTake{y, r}:
          U32.is_eq(y, x)

def idxtake(mi: Maybe<&2, Nat>, +alpha: List<&2, U32>, +i: Nat, +pre: List<&2, U32>, +x: U32) -> Bool:
  match mi:
    case None{}:
      True{}
    case Some{+j}:
      tk_ok(M.mtf.take.go(alpha, Nat.is_eq(i, j), i, pre, j), x)

def idxge(mi: Maybe<&2, Nat>, +i: Nat) -> Bool:
  match mi:
    case None{}:
      True{}
    case Some{j}:
      Nat.is_le(i, j)

def idxlt(mi: Maybe<&2, Nat>, +b: Nat) -> Bool:
  match mi:
    case None{}:
      True{}
    case Some{j}:
      Nat.is_lt(j, b)

def ge_shift(mi: Maybe<&2, Nat>, +i: Nat, ih: {idxge(mi, 1n+i) == True{} : Bool}) -> {idxge(mi, i) == True{} : Bool}:
  match mi:
    case None{}:
      {==}
    case Some{j}:
      le_succ_l(i, j, ih)

def ge_q(q: Bool, +t: List<&2, U32>, +i: Nat, +x: U32, ih: {idxge(M.mtf.idx.go(t, M.Bzip2MtfLook{1n+i}, x), 1n+i) == True{} : Bool}) -> {idxge(M.mtf.idx.go(t, M.mtf.idx.step(q, i), x), i) == True{} : Bool}:
  match q:
    case True{}:
      %idx_hit(t, i, x) : {idxge(_, i) == True{} : Bool}
      le_self(i)
    case False{}:
      ge_shift(M.mtf.idx.go(t, M.Bzip2MtfLook{1n+i}, x), i, ih)

def ge_ok(alpha: List<&2, U32>, +i: Nat, +x: U32) -> {idxge(M.mtf.idx.go(alpha, M.Bzip2MtfLook{i}, x), i) == True{} : Bool}:
  match alpha:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      ge_q(U32.is_eq(h, x), t, i, x, ge_ok(t, 1n+i, x))

def lt_q(q: Bool, +t: List<&2, U32>, +i: Nat, +x: U32, ih: {idxlt(M.mtf.idx.go(t, M.Bzip2MtfLook{1n+i}, x), Nat.add(1n+i, B.len(t))) == True{} : Bool}) -> {idxlt(M.mtf.idx.go(t, M.mtf.idx.step(q, i), x), Nat.add(i, 1n+B.len(t))) == True{} : Bool}:
  match q:
    case True{}:
      %idx_hit(t, i, x) : {idxlt(_, Nat.add(i, 1n+B.len(t))) == True{} : Bool}
      lt_add_succ(i, B.len(t))
    case False{}:
      %Equal.sym(Nat, Nat.add(i, 1n+B.len(t)), 1n+Nat.add(i, B.len(t)), add_succ_r(i, B.len(t))) : {idxlt(M.mtf.idx.go(t, M.Bzip2MtfLook{1n+i}, x), _) == True{} : Bool}
      ih

def lt_ok(alpha: List<&2, U32>, +i: Nat, +x: U32) -> {idxlt(M.mtf.idx.go(alpha, M.Bzip2MtfLook{i}, x), Nat.add(i, B.len(alpha))) == True{} : Bool}:
  match alpha:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      lt_q(U32.is_eq(h, x), t, i, x, lt_ok(t, 1n+i, x))

def it_shift(mi: Maybe<&2, Nat>, +h: U32, +t: List<&2, U32>, +i: Nat, +pre: List<&2, U32>, +x: U32, ih: {idxtake(mi, t, 1n+i, Con{h, pre}, x) == True{} : Bool}, ge: {idxge(mi, 1n+i) == True{} : Bool}) -> {idxtake(mi, Con{h, t}, i, pre, x) == True{} : Bool}:
  match mi:
    case None{}:
      {==}
    case Some{+j}:
      %Equal.sym(Bool, Nat.is_eq(i, j), False{}, le_succ_ne(i, j, ge)) : {tk_ok(M.mtf.take.go(Con{h, t}, _, i, pre, j), x) == True{} : Bool}
      ih

def it_q(q: Bool, +h: U32, +t: List<&2, U32>, +i: Nat, +pre: List<&2, U32>, +x: U32, eq: {q == U32.is_eq(h, x) : Bool}, ih: {idxtake(M.mtf.idx.go(t, M.Bzip2MtfLook{1n+i}, x), t, 1n+i, Con{h, pre}, x) == True{} : Bool}, ge: {idxge(M.mtf.idx.go(t, M.Bzip2MtfLook{1n+i}, x), 1n+i) == True{} : Bool}) -> {idxtake(M.mtf.idx.go(t, M.mtf.idx.step(q, i), x), Con{h, t}, i, pre, x) == True{} : Bool}:
  match q:
    case True{}:
      %idx_hit(t, i, x) : {idxtake(_, Con{h, t}, i, pre, x) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(i, i), True{}, nat_eq_self(i)) : {tk_ok(M.mtf.take.go(Con{h, t}, _, i, pre, i), x) == True{} : Bool}
      %eq : {_ == True{} : Bool}
      {==}
    case False{}:
      it_shift(M.mtf.idx.go(t, M.Bzip2MtfLook{1n+i}, x), h, t, i, pre, x, ih, ge)

def it_ok(alpha: List<&2, U32>, +i: Nat, +pre: List<&2, U32>, +x: U32) -> {idxtake(M.mtf.idx.go(alpha, M.Bzip2MtfLook{i}, x), alpha, i, pre, x) == True{} : Bool}:
  match alpha:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      it_q(U32.is_eq(h, x), h, t, i, pre, x, {==}, it_ok(t, 1n+i, Con{h, pre}, x), ge_ok(t, 1n+i, x))


# The digits of a run: their value from weight w on (RUNA counts w, RUNB
# 2w, each digit doubling the weight), and the weight after them

def mv(ds: List<&2, M.Bzip2Digit>, +w: Nat) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{d, t}:
      match d:
        case M.Bzip2RunA{}:
          Nat.add(w, mv(t, Nat.add(w, w)))
        case M.Bzip2RunB{}:
          Nat.add(Nat.add(w, w), mv(t, Nat.add(w, w)))

def wafter(ds: List<&2, M.Bzip2Digit>, +w: Nat) -> Nat:
  match ds:
    case Nil{}:
      w
    case Con{d, t}:
      wafter(t, Nat.add(w, w))

# one more zero adds the lowest weight
def mv_inc(ds: List<&2, M.Bzip2Digit>, +w: Nat) -> {mv(M.mtf.inc(ds), w) == Nat.add(w, mv(ds, w)) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, +t}:
      match d:
        case M.Bzip2RunA{}:
          add_assoc(w, w, mv(t, Nat.add(w, w)))
        case M.Bzip2RunB{}:
          Equal.cong(Nat, Nat, v => Nat.add(w, v), mv(M.mtf.inc(t), Nat.add(w, w)), Nat.add(Nat.add(w, w), mv(t, Nat.add(w, w))), mv_inc(t, Nat.add(w, w)))

def res_app_nil(r: Result<&2, &2, E.Bzip2Error, List<&2, U32>>) -> {M.mtf.res.app(Nil{}, r) == r : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}:
  match r:
    case Fail{e}:
      {==}
    case Done{ys}:
      {==}

# the decoder reads the digits' symbols into its count
def digits(ds: List<&2, M.Bzip2Digit>, +rs: List<&2, U32>, +alpha: List<&2, U32>, +cnt: Nat, +w: Nat, +room: Nat) -> {M.mtf.dec(L.bz.app(M.mtf.syms(ds), rs), M.Bzip2MtfDec{alpha, cnt, w, room}) == M.mtf.dec(rs, M.Bzip2MtfDec{alpha, Nat.add(cnt, mv(ds, w)), wafter(ds, w), room}) : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}:
  match ds:
    case Nil{}:
      %Equal.sym(Nat, Nat.add(cnt, 0n), cnt, add_zero(cnt)) : {M.mtf.dec(rs, M.Bzip2MtfDec{alpha, cnt, w, room}) == M.mtf.dec(rs, M.Bzip2MtfDec{alpha, _, w, room}) : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
      {==}
    case Con{d, +t}:
      match d:
        case M.Bzip2RunA{}:
          +c2 = Nat.add(cnt, w)
          +w2 = Nat.add(w, w)
          %Equal.sym(Result<&2, &2, E.Bzip2Error, List<&2, U32>>, M.mtf.res.app(Nil{}, M.mtf.dec(L.bz.app(M.mtf.syms(t), rs), M.Bzip2MtfDec{alpha, c2, w2, room})), M.mtf.dec(L.bz.app(M.mtf.syms(t), rs), M.Bzip2MtfDec{alpha, c2, w2, room}), res_app_nil(M.mtf.dec(L.bz.app(M.mtf.syms(t), rs), M.Bzip2MtfDec{alpha, c2, w2, room}))) : {_ == M.mtf.dec(rs, M.Bzip2MtfDec{alpha, Nat.add(cnt, Nat.add(w, mv(t, w2))), wafter(t, w2), room}) : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
          %add_assoc(cnt, w, mv(t, w2)) : {M.mtf.dec(L.bz.app(M.mtf.syms(t), rs), M.Bzip2MtfDec{alpha, c2, w2, room}) == M.mtf.dec(rs, M.Bzip2MtfDec{alpha, _, wafter(t, w2), room}) : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
          digits(t, rs, alpha, c2, w2, room)
        case M.Bzip2RunB{}:
          +w2 = Nat.add(w, w)
          +c2 = Nat.add(cnt, w2)
          %Equal.sym(Result<&2, &2, E.Bzip2Error, List<&2, U32>>, M.mtf.res.app(Nil{}, M.mtf.dec(L.bz.app(M.mtf.syms(t), rs), M.Bzip2MtfDec{alpha, c2, w2, room})), M.mtf.dec(L.bz.app(M.mtf.syms(t), rs), M.Bzip2MtfDec{alpha, c2, w2, room}), res_app_nil(M.mtf.dec(L.bz.app(M.mtf.syms(t), rs), M.Bzip2MtfDec{alpha, c2, w2, room}))) : {_ == M.mtf.dec(rs, M.Bzip2MtfDec{alpha, Nat.add(cnt, Nat.add(w2, mv(t, w2))), wafter(t, w2), room}) : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
          %add_assoc(cnt, w2, mv(t, w2)) : {M.mtf.dec(L.bz.app(M.mtf.syms(t), rs), M.Bzip2MtfDec{alpha, c2, w2, room}) == M.mtf.dec(rs, M.Bzip2MtfDec{alpha, _, wafter(t, w2), room}) : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
          digits(t, rs, alpha, c2, w2, room)

# the run of c zeros, with room for it and l + k more
def le_room(+c: Nat, +l: Nat, +k: Nat) -> {True{} == Nat.is_le(c, Nat.add(Nat.add(c, l), k)) : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.add(c, l), k), Nat.add(c, Nat.add(l, k)), add_assoc(c, l, k)) : {True{} == Nat.is_le(c, _) : Bool}
  Equal.sym(Bool, Nat.is_le(c, Nat.add(c, Nat.add(l, k))), True{}, le_add(c, Nat.add(l, k)))

def sub_room(+c: Nat, +l: Nat, +k: Nat) -> {Nat.add(l, k) == Nat.sub(Nat.add(Nat.add(c, l), k), c) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(c, l), k), Nat.add(c, Nat.add(l, k)), add_assoc(c, l, k)) : {Nat.add(l, k) == Nat.sub(_, c) : Nat}
  Equal.sym(Nat, Nat.sub(Nat.add(c, Nat.add(l, k)), c), Nat.add(l, k), sub_add(c, Nat.add(l, k)))

def flush_ok(c: Nat, +a0: U32, +at: List<&2, U32>, +l: Nat, +k: Nat) -> {M.mtf.flush(c, Con{a0, at}, Nat.add(Nat.add(c, l), k)) == M.Bzip2MtfOut{L.bz.rep(c, a0), M.Bzip2MtfDec{Con{a0, at}, 0n, 1n, Nat.add(l, k)}} : M.Bzip2MtfOut}:
  match c:
    case 0n:
      {==}
    case 1n+(+p):
      %le_room(1n+p, l, k) : {M.mtf.flush.pick(_, a0, at, 1n+p, Nat.add(Nat.add(1n+p, l), k)) == M.Bzip2MtfOut{L.bz.rep(1n+p, a0), M.Bzip2MtfDec{Con{a0, at}, 0n, 1n, Nat.add(l, k)}} : M.Bzip2MtfOut}
      %sub_room(1n+p, l, k) : {M.Bzip2MtfOut{L.bz.rep(1n+p, a0), M.Bzip2MtfDec{Con{a0, at}, 0n, 1n, _}} == M.Bzip2MtfOut{L.bz.rep(1n+p, a0), M.Bzip2MtfDec{Con{a0, at}, 0n, 1n, Nat.add(l, k)}} : M.Bzip2MtfOut}
      {==}

# The fast forms

def syms_push(ds: List<&2, M.Bzip2Digit>, +acc: List<&2, U32>) -> {M.mtf.syms.push(ds, acc) == L.bz.push(M.mtf.syms(ds), acc) : List<&2, U32>}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, +t}:
      match d:
        case M.Bzip2RunA{}:
          syms_push(t, Con{0, acc})
        case M.Bzip2RunB{}:
          syms_push(t, Con{1, acc})

def menc_fast(xs: List<&2, U32>, +alpha: List<&2, U32>, +ds: List<&2, M.Bzip2Digit>, +acc: List<&2, U32>) -> {M.mtf.enc.fast(xs, alpha, ds, acc) == L.bz.push(acc, M.mtf.enc(xs, alpha, ds)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      %Equal.sym(List<&2, U32>, M.mtf.syms.push(ds, acc), L.bz.push(M.mtf.syms(ds), acc), syms_push(ds, acc)) : {L.bz.rev(_) == L.bz.push(acc, M.mtf.syms(ds)) : List<&2, U32>}
      rev_push(M.mtf.syms(ds), acc)
    case Con{+y, +t}:
      +e = M.mtf.enc.step(y, alpha, ds)
      Equal.trans(List<&2, U32>, M.mtf.enc.fast(t, M.mtf.enc.alpha(e), M.mtf.enc.ds(e), L.bz.push(M.mtf.enc.out(e), acc)), L.bz.push(L.bz.push(M.mtf.enc.out(e), acc), M.mtf.enc(t, M.mtf.enc.alpha(e), M.mtf.enc.ds(e))), L.bz.push(acc, L.bz.app(M.mtf.enc.out(e), M.mtf.enc(t, M.mtf.enc.alpha(e), M.mtf.enc.ds(e)))), menc_fast(t, M.mtf.enc.alpha(e), M.mtf.enc.ds(e), L.bz.push(M.mtf.enc.out(e), acc)), push_push(M.mtf.enc.out(e), acc, M.mtf.enc(t, M.mtf.enc.alpha(e), M.mtf.enc.ds(e))))

def res_push_app(+e: List<&2, U32>, +acc: List<&2, U32>, r: Result<&2, &2, E.Bzip2Error, List<&2, U32>>) -> {M.mtf.res.push(L.bz.push(e, acc), r) == M.mtf.res.push(acc, M.mtf.res.app(e, r)) : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}:
  match r:
    case Fail{x}:
      {==}
    case Done{ys}:
      Equal.cong(List<&2, U32>, Result<&2, &2, E.Bzip2Error, List<&2, U32>>, v => Done{v}, L.bz.push(L.bz.push(e, acc), ys), L.bz.push(acc, L.bz.app(e, ys)), push_push(e, acc, ys))

def mdec_bad(syms: List<&2, U32>, +x: E.Bzip2Error) -> {M.mtf.dec(syms, M.Bzip2MtfBad{x}) == Fail{x} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}:
  match syms:
    case Nil{}:
      {==}
    case Con{s, t}:
      %Equal.sym(Result<&2, &2, E.Bzip2Error, List<&2, U32>>, M.mtf.dec(t, M.Bzip2MtfBad{x}), Fail{x}, mdec_bad(t, x)) : {M.mtf.res.app(Nil{}, _) == Fail{x} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
      {==}

def mdec_fast(syms: List<&2, U32>, +st: M.Bzip2MtfDec, +acc: List<&2, U32>) -> {M.mtf.dec.fast(syms, st, acc) == M.mtf.res.push(acc, M.mtf.dec(syms, st)) : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}:
  match syms:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      match st:
        case M.Bzip2MtfBad{+x}:
          %Equal.sym(Result<&2, &2, E.Bzip2Error, List<&2, U32>>, M.mtf.dec(t, M.Bzip2MtfBad{x}), Fail{x}, mdec_bad(t, x)) : {Fail{x} == M.mtf.res.push(acc, M.mtf.res.app(Nil{}, _)) : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
          {==}
        case M.Bzip2MtfDec{+alpha, +cnt, +w, +room}:
          +o = M.mtf.dec.step(s, M.Bzip2MtfDec{alpha, cnt, w, room})
          Equal.trans(Result<&2, &2, E.Bzip2Error, List<&2, U32>>, M.mtf.dec.fast(t, M.mtf.out.next(o), L.bz.push(M.mtf.out.out(o), acc)), M.mtf.res.push(L.bz.push(M.mtf.out.out(o), acc), M.mtf.dec(t, M.mtf.out.next(o))), M.mtf.res.push(acc, M.mtf.res.app(M.mtf.out.out(o), M.mtf.dec(t, M.mtf.out.next(o)))), mdec_fast(t, M.mtf.out.next(o), L.bz.push(M.mtf.out.out(o), acc)), res_push_app(M.mtf.out.out(o), acc, M.mtf.dec(t, M.mtf.out.next(o))))

def res_push_nil(r: Result<&2, &2, E.Bzip2Error, List<&2, U32>>) -> {M.mtf.res.push(Nil{}, r) == r : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}:
  match r:
    case Fail{x}:
      {==}
    case Done{ys}:
      {==}


# What idx found, take finds; and the position is inside the alphabet

def tk_found(+j: Nat, +a0: U32, +at: List<&2, U32>, +x: U32, +eqm: {Some{j} == M.mtf.idx(Con{a0, at}, x) : Maybe<&2, Nat>}) -> {idxtake(Some{j}, Con{a0, at}, 0n, Nil{}, x) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Nat>, Some{j}, M.mtf.idx(Con{a0, at}, x), eqm) : {idxtake(_, Con{a0, at}, 0n, Nil{}, x) == True{} : Bool}
  it_ok(Con{a0, at}, 0n, Nil{}, x)

def lt_found(+j: Nat, +a0: U32, +at: List<&2, U32>, +x: U32, +eqm: {Some{j} == M.mtf.idx(Con{a0, at}, x) : Maybe<&2, Nat>}) -> {idxlt(Some{j}, B.len(Con{a0, at})) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Nat>, Some{j}, M.mtf.idx(Con{a0, at}, x), eqm) : {idxlt(_, B.len(Con{a0, at})) == True{} : Bool}
  lt_ok(Con{a0, at}, 0n, x)

def head_is(+a0: U32, +at: List<&2, U32>, +x: U32, +eqm: {Some{0n} == M.mtf.idx(Con{a0, at}, x) : Maybe<&2, Nat>}) -> {a0 == x : U32}:
  u32_eq(a0, x, tk_found(0n, a0, at, x, eqm))

def tk_none(+j: Nat, +a0: U32, +at: List<&2, U32>, +x: U32, +eqt: {None{} == M.mtf.take(Con{a0, at}, j) : Maybe<&2, M.Bzip2MtfTake>}, +eqm: {Some{j} == M.mtf.idx(Con{a0, at}, x) : Maybe<&2, Nat>}) -> {tk_ok(None{}, x) == True{} : Bool}:
  %Equal.sym(Maybe<&2, M.Bzip2MtfTake>, None{}, M.mtf.take(Con{a0, at}, j), eqt) : {tk_ok(_, x) == True{} : Bool}
  tk_found(j, a0, at, x, eqm)

def tk_some(+j: Nat, +a0: U32, +at: List<&2, U32>, +x: U32, +y: U32, +r: List<&2, U32>, +eqt: {Some{M.Bzip2MtfTake{y, r}} == M.mtf.take(Con{a0, at}, j) : Maybe<&2, M.Bzip2MtfTake>}, +eqm: {Some{j} == M.mtf.idx(Con{a0, at}, x) : Maybe<&2, Nat>}) -> {tk_ok(Some{M.Bzip2MtfTake{y, r}}, x) == True{} : Bool}:
  %Equal.sym(Maybe<&2, M.Bzip2MtfTake>, Some{M.Bzip2MtfTake{y, r}}, M.mtf.take(Con{a0, at}, j), eqt) : {tk_ok(_, x) == True{} : Bool}
  tk_found(j, a0, at, x, eqm)

def tk_cov2(+j: Nat, +a0: U32, +at: List<&2, U32>, +y: U32, +r: List<&2, U32>, +t: List<&2, U32>, +eqt: {Some{M.Bzip2MtfTake{y, r}} == M.mtf.take(Con{a0, at}, j) : Maybe<&2, M.Bzip2MtfTake>}) -> TkCov(Some{M.Bzip2MtfTake{y, r}}, t, Con{a0, at}):
  %Equal.sym(Maybe<&2, M.Bzip2MtfTake>, Some{M.Bzip2MtfTake{y, r}}, M.mtf.take(Con{a0, at}, j), eqt) : TkCov(_, t, Con{a0, at})
  tk_cov(Con{a0, at}, Nat.is_eq(0n, j), 0n, Nil{}, j, t)

def tk_len2(+j: Nat, +a0: U32, +at: List<&2, U32>, +y: U32, +r: List<&2, U32>, +eqt: {Some{M.Bzip2MtfTake{y, r}} == M.mtf.take(Con{a0, at}, j) : Maybe<&2, M.Bzip2MtfTake>}) -> TkLen(Some{M.Bzip2MtfTake{y, r}}, Con{a0, at}):
  %Equal.sym(Maybe<&2, M.Bzip2MtfTake>, Some{M.Bzip2MtfTake{y, r}}, M.mtf.take(Con{a0, at}, j), eqt) : TkLen(_, Con{a0, at})
  tk_len(Con{a0, at}, Nat.is_eq(0n, j), 0n, Nil{}, j)

def ln_moved(+y: U32, +r: List<&2, U32>, +bs: List<&2, U32>, +e: {B.len(Con{y, r}) == B.len(bs) : Nat}, +ln: {Nat.is_le(B.len(bs), 256n) == True{} : Bool}) -> {Nat.is_le(B.len(Con{y, r}), 256n) == True{} : Bool}:
  %Equal.sym(Nat, B.len(Con{y, r}), B.len(bs), e) : {Nat.is_le(_, 256n) == True{} : Bool}
  ln

# The main lemma: the decoder, at the start of a segment (count 0, weight
# 1), decodes the encoder's symbols for xs, from the same alphabet, with the
# run ds pending, to that run then xs, with room for it all and k more

def mm_nil(+a0: U32, +at: List<&2, U32>, +ds: List<&2, M.Bzip2Digit>, +k: Nat) -> {M.mtf.dec(M.mtf.syms(ds), M.Bzip2MtfDec{Con{a0, at}, 0n, 1n, Nat.add(Nat.add(mv(ds, 1n), 0n), k)}) == Done{L.bz.app(L.bz.rep(mv(ds, 1n), a0), Nil{})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}:
  +m1 = mv(ds, 1n)
  +room = Nat.add(Nat.add(m1, 0n), k)
  +alpha = {Con{a0, at} : List<&2, U32>}
  %app_nil(M.mtf.syms(ds)) : {M.mtf.dec(_, M.Bzip2MtfDec{alpha, 0n, 1n, room}) == Done{L.bz.app(L.bz.rep(m1, a0), Nil{})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  %Equal.sym(Result<&2, &2, E.Bzip2Error, List<&2, U32>>, M.mtf.dec(L.bz.app(M.mtf.syms(ds), Nil{}), M.Bzip2MtfDec{alpha, 0n, 1n, room}), M.mtf.dec(Nil{}, M.Bzip2MtfDec{alpha, m1, wafter(ds, 1n), room}), digits(ds, Nil{}, alpha, 0n, 1n, room)) : {_ == Done{L.bz.app(L.bz.rep(m1, a0), Nil{})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  %Equal.sym(M.Bzip2MtfOut, M.mtf.flush(m1, alpha, room), M.Bzip2MtfOut{L.bz.rep(m1, a0), M.Bzip2MtfDec{alpha, 0n, 1n, Nat.add(0n, k)}}, flush_ok(m1, a0, at, 0n, k)) : {M.mtf.end.out(_) == Done{L.bz.app(L.bz.rep(m1, a0), Nil{})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  %Equal.sym(List<&2, U32>, L.bz.app(L.bz.rep(m1, a0), Nil{}), L.bz.rep(m1, a0), app_nil(L.bz.rep(m1, a0))) : {Done{L.bz.rep(m1, a0)} == Done{_} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  {==}

def mm_zero(+y: U32, +t: List<&2, U32>, +a0: U32, +at: List<&2, U32>, +ds: List<&2, M.Bzip2Digit>, +k: Nat, +eqm: {Some{0n} == M.mtf.idx(Con{a0, at}, B.byte(y)) : Maybe<&2, Nat>}, +cvt: {M.mtf.covers(t, Con{a0, at}) == True{} : Bool}, ih0: {M.mtf.covers(t, Con{a0, at}) == True{} : Bool} -> {M.mtf.dec(M.mtf.enc(t, Con{a0, at}, M.mtf.inc(ds)), M.Bzip2MtfDec{Con{a0, at}, 0n, 1n, Nat.add(Nat.add(mv(M.mtf.inc(ds), 1n), B.len(t)), k)}) == Done{L.bz.app(L.bz.rep(mv(M.mtf.inc(ds), 1n), a0), B.mask(t))} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}) -> {M.mtf.dec(M.mtf.enc(t, Con{a0, at}, M.mtf.inc(ds)), M.Bzip2MtfDec{Con{a0, at}, 0n, 1n, Nat.add(Nat.add(mv(ds, 1n), 1n+B.len(t)), k)}) == Done{L.bz.app(L.bz.rep(mv(ds, 1n), a0), Con{B.byte(y), B.mask(t)})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}:
  +m1 = mv(ds, 1n)
  +alpha = {Con{a0, at} : List<&2, U32>}
  +e1 = M.mtf.enc(t, alpha, M.mtf.inc(ds))
  %head_is(a0, at, B.byte(y), eqm) : {M.mtf.dec(e1, M.Bzip2MtfDec{alpha, 0n, 1n, Nat.add(Nat.add(m1, 1n+B.len(t)), k)}) == Done{L.bz.app(L.bz.rep(m1, a0), Con{_, B.mask(t)})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  %Equal.sym(List<&2, U32>, L.bz.app(L.bz.rep(m1, a0), Con{a0, B.mask(t)}), Con{a0, L.bz.app(L.bz.rep(m1, a0), B.mask(t))}, rep_snoc(m1, a0, B.mask(t))) : {M.mtf.dec(e1, M.Bzip2MtfDec{alpha, 0n, 1n, Nat.add(Nat.add(m1, 1n+B.len(t)), k)}) == Done{_} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  %Equal.sym(Nat, Nat.add(m1, 1n+B.len(t)), 1n+Nat.add(m1, B.len(t)), add_succ_r(m1, B.len(t))) : {M.mtf.dec(e1, M.Bzip2MtfDec{alpha, 0n, 1n, Nat.add(_, k)}) == Done{Con{a0, L.bz.app(L.bz.rep(m1, a0), B.mask(t))}} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  %mv_inc(ds, 1n) : {M.mtf.dec(e1, M.Bzip2MtfDec{alpha, 0n, 1n, Nat.add(Nat.add(_, B.len(t)), k)}) == Done{L.bz.app(L.bz.rep(_, a0), B.mask(t))} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  ih0(cvt)

def mm_moved(+q: Nat, +y: U32, +t: List<&2, U32>, +a0: U32, +at: List<&2, U32>, +ds: List<&2, M.Bzip2Digit>, +k: Nat, +x2: U32, +r2: List<&2, U32>, +eqt: {Some{M.Bzip2MtfTake{x2, r2}} == M.mtf.take(Con{a0, at}, 1n+q) : Maybe<&2, M.Bzip2MtfTake>}, +eqm: {Some{1n+q} == M.mtf.idx(Con{a0, at}, B.byte(y)) : Maybe<&2, Nat>}, +ln: {Nat.is_le(B.len(Con{a0, at}), 256n) == True{} : Bool}, +ihr: {M.mtf.dec(M.mtf.enc(t, Con{x2, r2}, Nil{}), M.Bzip2MtfDec{Con{x2, r2}, 0n, 1n, Nat.add(Nat.add(0n, B.len(t)), k)}) == Done{L.bz.app(L.bz.rep(0n, x2), B.mask(t))} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}) -> {M.mtf.dec(L.bz.app(L.bz.app(M.mtf.syms(ds), [U32.from_nat(1n+1n+q)]), M.mtf.enc(t, Con{x2, r2}, Nil{})), M.Bzip2MtfDec{Con{a0, at}, 0n, 1n, Nat.add(Nat.add(mv(ds, 1n), 1n+B.len(t)), k)}) == Done{L.bz.app(L.bz.rep(mv(ds, 1n), a0), Con{B.byte(y), B.mask(t)})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}:
  +m1 = mv(ds, 1n)
  +alpha = {Con{a0, at} : List<&2, U32>}
  +room = Nat.add(Nat.add(m1, 1n+B.len(t)), k)
  +bound = lt_le(1n+q, B.len(alpha), 256n, lt_found(1n+q, a0, at, B.byte(y), eqm), ln)
  +ex = u32_eq(x2, B.byte(y), tk_some(1n+q, a0, at, B.byte(y), x2, r2, eqt, eqm))
  %Equal.sym(List<&2, U32>, L.bz.app(L.bz.app(M.mtf.syms(ds), [U32.from_nat(1n+1n+q)]), M.mtf.enc(t, Con{x2, r2}, Nil{})), L.bz.app(M.mtf.syms(ds), Con{U32.from_nat(1n+1n+q), M.mtf.enc(t, Con{x2, r2}, Nil{})}), app_one(M.mtf.syms(ds), U32.from_nat(1n+1n+q), M.mtf.enc(t, Con{x2, r2}, Nil{}))) : {M.mtf.dec(_, M.Bzip2MtfDec{alpha, 0n, 1n, room}) == Done{L.bz.app(L.bz.rep(mv(ds, 1n), a0), Con{B.byte(y), B.mask(t)})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  %Equal.sym(Result<&2, &2, E.Bzip2Error, List<&2, U32>>, M.mtf.dec(L.bz.app(M.mtf.syms(ds), Con{U32.from_nat(1n+1n+q), M.mtf.enc(t, Con{x2, r2}, Nil{})}), M.Bzip2MtfDec{alpha, 0n, 1n, room}), M.mtf.dec(Con{U32.from_nat(1n+1n+q), M.mtf.enc(t, Con{x2, r2}, Nil{})}, M.Bzip2MtfDec{alpha, m1, wafter(ds, 1n), room}), digits(ds, Con{U32.from_nat(1n+1n+q), M.mtf.enc(t, Con{x2, r2}, Nil{})}, alpha, 0n, 1n, room)) : {_ == Done{L.bz.app(L.bz.rep(mv(ds, 1n), a0), Con{B.byte(y), B.mask(t)})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  %symn.k0(1n+1n+q, bound) : {M.mtf.res.app(M.mtf.out.out(M.mtf.dec.sym(_, alpha, m1, wafter(ds, 1n), room)), M.mtf.dec(M.mtf.enc(t, Con{x2, r2}, Nil{}), M.mtf.out.next(M.mtf.dec.sym(_, alpha, m1, wafter(ds, 1n), room)))) == Done{L.bz.app(L.bz.rep(mv(ds, 1n), a0), Con{B.byte(y), B.mask(t)})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  %Equal.sym(M.Bzip2MtfOut, M.mtf.flush(m1, alpha, room), M.Bzip2MtfOut{L.bz.rep(m1, a0), M.Bzip2MtfDec{alpha, 0n, 1n, Nat.add(1n+B.len(t), k)}}, flush_ok(m1, a0, at, 1n+B.len(t), k)) : {M.mtf.res.app(M.mtf.out.out(M.mtf.dec.index(_, 1n+q)), M.mtf.dec(M.mtf.enc(t, Con{x2, r2}, Nil{}), M.mtf.out.next(M.mtf.dec.index(_, 1n+q)))) == Done{L.bz.app(L.bz.rep(mv(ds, 1n), a0), Con{B.byte(y), B.mask(t)})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  %eqt : {M.mtf.res.app(M.mtf.out.out(M.mtf.dec.put(_, L.bz.rep(m1, a0), Nat.add(1n+B.len(t), k))), M.mtf.dec(M.mtf.enc(t, Con{x2, r2}, Nil{}), M.mtf.out.next(M.mtf.dec.put(_, L.bz.rep(m1, a0), Nat.add(1n+B.len(t), k))))) == Done{L.bz.app(L.bz.rep(mv(ds, 1n), a0), Con{B.byte(y), B.mask(t)})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  %Equal.sym(Result<&2, &2, E.Bzip2Error, List<&2, U32>>, M.mtf.dec(M.mtf.enc(t, Con{x2, r2}, Nil{}), M.Bzip2MtfDec{Con{x2, r2}, 0n, 1n, Nat.add(B.len(t), k)}), Done{B.mask(t)}, ihr) : {M.mtf.res.app(L.bz.app(L.bz.rep(m1, a0), [x2]), _) == Done{L.bz.app(L.bz.rep(mv(ds, 1n), a0), Con{B.byte(y), B.mask(t)})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  %Equal.sym(List<&2, U32>, L.bz.app(L.bz.app(L.bz.rep(m1, a0), [x2]), B.mask(t)), L.bz.app(L.bz.rep(m1, a0), Con{x2, B.mask(t)}), app_one(L.bz.rep(m1, a0), x2, B.mask(t))) : {Done{_} == Done{L.bz.app(L.bz.rep(mv(ds, 1n), a0), Con{B.byte(y), B.mask(t)})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  %ex : {Done{L.bz.app(L.bz.rep(m1, a0), Con{x2, B.mask(t)})} == Done{L.bz.app(L.bz.rep(m1, a0), Con{_, B.mask(t)})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  {==}


def mm_take(+q: Nat, +y: U32, +t: List<&2, U32>, +a0: U32, +at: List<&2, U32>, +ds: List<&2, M.Bzip2Digit>, +k: Nat, +mt: Maybe<&2, M.Bzip2MtfTake>, +eqt: {mt == M.mtf.take(Con{a0, at}, 1n+q) : Maybe<&2, M.Bzip2MtfTake>}, +eqm: {Some{1n+q} == M.mtf.idx(Con{a0, at}, B.byte(y)) : Maybe<&2, Nat>}, +cvt: {M.mtf.covers(t, Con{a0, at}) == True{} : Bool}, +ln: {Nat.is_le(B.len(Con{a0, at}), 256n) == True{} : Bool}, ihm: @x2: U32 -> @r2: List<&2, U32> -> {M.mtf.covers(t, Con{x2, r2}) == True{} : Bool} -> {Nat.is_le(B.len(Con{x2, r2}), 256n) == True{} : Bool} -> {M.mtf.dec(M.mtf.enc(t, Con{x2, r2}, Nil{}), M.Bzip2MtfDec{Con{x2, r2}, 0n, 1n, Nat.add(Nat.add(0n, B.len(t)), k)}) == Done{L.bz.app(L.bz.rep(0n, x2), B.mask(t))} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}) -> {M.mtf.dec(L.bz.app(M.mtf.enc.out(M.mtf.enc.moved(mt, ds, U32.from_nat(1n+1n+q), Con{a0, at})), M.mtf.enc(t, M.mtf.enc.alpha(M.mtf.enc.moved(mt, ds, U32.from_nat(1n+1n+q), Con{a0, at})), M.mtf.enc.ds(M.mtf.enc.moved(mt, ds, U32.from_nat(1n+1n+q), Con{a0, at})))), M.Bzip2MtfDec{Con{a0, at}, 0n, 1n, Nat.add(Nat.add(mv(ds, 1n), 1n+B.len(t)), k)}) == Done{L.bz.app(L.bz.rep(mv(ds, 1n), a0), Con{B.byte(y), B.mask(t)})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}:
  match mt:
    case None{}:
      Empty.absurd({M.mtf.dec(L.bz.app(M.mtf.enc.out(M.mtf.enc.moved(None{}, ds, U32.from_nat(1n+1n+q), Con{a0, at})), M.mtf.enc(t, M.mtf.enc.alpha(M.mtf.enc.moved(None{}, ds, U32.from_nat(1n+1n+q), Con{a0, at})), M.mtf.enc.ds(M.mtf.enc.moved(None{}, ds, U32.from_nat(1n+1n+q), Con{a0, at})))), M.Bzip2MtfDec{Con{a0, at}, 0n, 1n, Nat.add(Nat.add(mv(ds, 1n), 1n+B.len(t)), k)}) == Done{L.bz.app(L.bz.rep(mv(ds, 1n), a0), Con{B.byte(y), B.mask(t)})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}, absurd.ft(tk_none(1n+q, a0, at, B.byte(y), eqt, eqm)))
    case Some{tk}:
      match tk:
        case M.Bzip2MtfTake{+x2, +r2}:
          mm_moved(q, y, t, a0, at, ds, k, x2, r2, eqt, eqm, ln, ihm(x2, r2, Equal.trans(Bool, M.mtf.covers(t, Con{x2, r2}), M.mtf.covers(t, Con{a0, at}), True{}, tk_cov2(1n+q, a0, at, x2, r2, t, eqt), cvt), ln_moved(x2, r2, Con{a0, at}, tk_len2(1n+q, a0, at, x2, r2, eqt), ln)))

def mm_at(+y: U32, +t: List<&2, U32>, +a0: U32, +at: List<&2, U32>, +ds: List<&2, M.Bzip2Digit>, +k: Nat, +m: Maybe<&2, Nat>, +eqm: {m == M.mtf.idx(Con{a0, at}, B.byte(y)) : Maybe<&2, Nat>}, +cvm: {Bool.and(M.mtf.covers.has(m), M.mtf.covers(t, Con{a0, at})) == True{} : Bool}, +ln: {Nat.is_le(B.len(Con{a0, at}), 256n) == True{} : Bool}, ih0: {M.mtf.covers(t, Con{a0, at}) == True{} : Bool} -> {M.mtf.dec(M.mtf.enc(t, Con{a0, at}, M.mtf.inc(ds)), M.Bzip2MtfDec{Con{a0, at}, 0n, 1n, Nat.add(Nat.add(mv(M.mtf.inc(ds), 1n), B.len(t)), k)}) == Done{L.bz.app(L.bz.rep(mv(M.mtf.inc(ds), 1n), a0), B.mask(t))} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}, ihm: @x2: U32 -> @r2: List<&2, U32> -> {M.mtf.covers(t, Con{x2, r2}) == True{} : Bool} -> {Nat.is_le(B.len(Con{x2, r2}), 256n) == True{} : Bool} -> {M.mtf.dec(M.mtf.enc(t, Con{x2, r2}, Nil{}), M.Bzip2MtfDec{Con{x2, r2}, 0n, 1n, Nat.add(Nat.add(0n, B.len(t)), k)}) == Done{L.bz.app(L.bz.rep(0n, x2), B.mask(t))} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}) -> {M.mtf.dec(L.bz.app(M.mtf.enc.out(M.mtf.enc.at(m, Con{a0, at}, ds)), M.mtf.enc(t, M.mtf.enc.alpha(M.mtf.enc.at(m, Con{a0, at}, ds)), M.mtf.enc.ds(M.mtf.enc.at(m, Con{a0, at}, ds)))), M.Bzip2MtfDec{Con{a0, at}, 0n, 1n, Nat.add(Nat.add(mv(ds, 1n), 1n+B.len(t)), k)}) == Done{L.bz.app(L.bz.rep(mv(ds, 1n), a0), Con{B.byte(y), B.mask(t)})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}:
  match m:
    case None{}:
      Empty.absurd({M.mtf.dec(L.bz.app(M.mtf.enc.out(M.mtf.enc.at(None{}, Con{a0, at}, ds)), M.mtf.enc(t, M.mtf.enc.alpha(M.mtf.enc.at(None{}, Con{a0, at}, ds)), M.mtf.enc.ds(M.mtf.enc.at(None{}, Con{a0, at}, ds)))), M.Bzip2MtfDec{Con{a0, at}, 0n, 1n, Nat.add(Nat.add(mv(ds, 1n), 1n+B.len(t)), k)}) == Done{L.bz.app(L.bz.rep(mv(ds, 1n), a0), Con{B.byte(y), B.mask(t)})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}, absurd.ft(cvm))
    case Some{p}:
      match p:
        case 0n:
          mm_zero(y, t, a0, at, ds, k, eqm, cvm, ih0)
        case 1n+(+q):
          mm_take(q, y, t, a0, at, ds, k, M.mtf.take(Con{a0, at}, 1n+q), {==}, eqm, cvm, ln, ihm)

def mm(+xs: List<&2, U32>, +a0: U32, +at: List<&2, U32>, +ds: List<&2, M.Bzip2Digit>, +k: Nat, +cv: {M.mtf.covers(xs, Con{a0, at}) == True{} : Bool}, +ln: {Nat.is_le(B.len(Con{a0, at}), 256n) == True{} : Bool}) -> {M.mtf.dec(M.mtf.enc(xs, Con{a0, at}, ds), M.Bzip2MtfDec{Con{a0, at}, 0n, 1n, Nat.add(Nat.add(mv(ds, 1n), B.len(xs)), k)}) == Done{L.bz.app(L.bz.rep(mv(ds, 1n), a0), B.mask(xs))} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}:
  match xs:
    case Nil{}:
      mm_nil(a0, at, ds, k)
    case Con{+y, +t}:
      mm_at(y, t, a0, at, ds, k, M.mtf.idx(Con{a0, at}, B.byte(y)), {==}, cv, ln, c => mm(t, a0, at, M.mtf.inc(ds), k, c, ln), x2 => r2 => c2 => l2 => mm(t, x2, r2, Nil{}, k, c2, l2))

# any alphabet (an empty one covers only the empty input)
def mrt(+alpha: List<&2, U32>, +xs: List<&2, U32>, +k: Nat, +cv: {M.mtf.covers(xs, alpha) == True{} : Bool}, +ln: {Nat.is_le(B.len(alpha), 256n) == True{} : Bool}) -> {M.mtf.dec(M.mtf.enc(xs, alpha, Nil{}), M.Bzip2MtfDec{alpha, 0n, 1n, Nat.add(B.len(xs), k)}) == Done{B.mask(xs)} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}:
  match alpha:
    case Nil{}:
      match xs:
        case Nil{}:
          {==}
        case Con{y, t}:
          Empty.absurd({M.mtf.dec(M.mtf.enc(Con{y, t}, Nil{}, Nil{}), M.Bzip2MtfDec{Nil{}, 0n, 1n, Nat.add(B.len(Con{y, t}), k)}) == Done{B.mask(Con{y, t})} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}, absurd.ft(cv))
    case Con{+a0, +at}:
      mm(xs, a0, at, Nil{}, k, cv, ln)

# a byte string's list, masked, is the byte string
def of_mask(+o: B.Octets) -> {B.Octets.of_list(B.mask(B.Octets.to_list(o))) == o : B.Octets}:
  +xs = B.Octets.to_list(o)
  %BL.octets_to_of(xs) : {B.Octets.of_list(_) == o : B.Octets}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(B.Octets.of_list(xs))), B.Octets.of_list(xs), BL.octets_of_list_idempotent(xs)) : {_ == o : B.Octets}
  BL.octets_of_to(o)

def len_hyp(+alpha: B.Octets, +s: {Nat.is_le(B.Octets.len(alpha), 256n) == True{} : Bool}) -> {Nat.is_le(B.len(B.Octets.to_list(alpha)), 256n) == True{} : Bool}:
  %BL.octets_len_list(alpha) : {Nat.is_le(_, 256n) == True{} : Bool}
  s

def Laws.mtf_round_trip(alpha, o, k, c, s):
  +xs = B.Octets.to_list(o)
  +a = B.Octets.to_list(alpha)
  +dz = {M.Bzip2MtfDec{a, 0n, 1n, Nat.add(B.len(xs), k)} : M.Bzip2MtfDec}
  +sy = M.mtf.enc(xs, a, Nil{})
  %Equal.sym(List<&2, U32>, M.mtf.enc.fast(xs, a, Nil{}, Nil{}), sy, menc_fast(xs, a, Nil{}, Nil{})) : {M.mtf.res.octets(M.mtf.dec.fast(_, M.Bzip2MtfDec{a, 0n, 1n, Nat.add(B.Octets.len(o), k)}, Nil{})) == Done{o} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %Equal.sym(Nat, B.Octets.len(o), B.len(xs), BL.octets_len_list(o)) : {M.mtf.res.octets(M.mtf.dec.fast(sy, M.Bzip2MtfDec{a, 0n, 1n, Nat.add(_, k)}, Nil{})) == Done{o} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %Equal.sym(Result<&2, &2, E.Bzip2Error, List<&2, U32>>, M.mtf.dec.fast(sy, dz, Nil{}), M.mtf.dec(sy, dz), Equal.trans(Result<&2, &2, E.Bzip2Error, List<&2, U32>>, M.mtf.dec.fast(sy, dz, Nil{}), M.mtf.res.push(Nil{}, M.mtf.dec(sy, dz)), M.mtf.dec(sy, dz), mdec_fast(sy, dz, Nil{}), res_push_nil(M.mtf.dec(sy, dz)))) : {M.mtf.res.octets(_) == Done{o} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %Equal.sym(Result<&2, &2, E.Bzip2Error, List<&2, U32>>, M.mtf.dec(sy, dz), Done{B.mask(xs)}, mrt(a, xs, k, c, len_hyp(alpha, s))) : {M.mtf.res.octets(_) == Done{o} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  Equal.cong(B.Octets, Result<&2, &2, E.Bzip2Error, B.Octets>, v => Done{v}, B.Octets.of_list(B.mask(xs)), o, of_mask(o))


# The Burrows-Wheeler transform, by the references
#
# A block of n copies of c: every rotation is the block, so every
# comparison is equal, the stable sort keeps the positions in order, every
# last byte is c and the rotation at 0 stays first; the inverse's table is
# n equal rows at every round.

def drop_rep(i: Nat, n: Nat, +c: U32) -> {W.bwt.drop(i, L.bz.rep(n, c)) == L.bz.rep(Nat.sub(n, i), c) : List<&2, U32>}:
  match i:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n+(+p):
          {==}
    case 1n+(+j):
      match n:
        case 0n:
          {==}
        case 1n+(+p):
          drop_rep(j, p, c)

def rot_rep(i: Nat, n: Nat, +c: U32) -> {W.bwt.rot(i, L.bz.rep(n, c)) == L.bz.rep(n, c) : List<&2, U32>}:
  match i:
    case 0n:
      app_nil(L.bz.rep(n, c))
    case 1n+(+j):
      match n:
        case 0n:
          {==}
        case 1n+(+p):
          +d = W.bwt.drop(j, L.bz.rep(p, c))
          +tk = W.bwt.take(j, L.bz.rep(p, c))
          %Equal.sym(List<&2, U32>, d, L.bz.rep(Nat.sub(p, j), c), drop_rep(j, p, c)) : {L.bz.app(_, Con{c, tk}) == L.bz.rep(1n+p, c) : List<&2, U32>}
          %Equal.sym(List<&2, U32>, L.bz.app(L.bz.rep(Nat.sub(p, j), c), Con{c, tk}), Con{c, L.bz.app(L.bz.rep(Nat.sub(p, j), c), tk)}, rep_snoc(Nat.sub(p, j), c, tk)) : {_ == L.bz.rep(1n+p, c) : List<&2, U32>}
          %drop_rep(j, p, c) : {Con{c, L.bz.app(_, tk)} == L.bz.rep(1n+p, c) : List<&2, U32>}
          Equal.cong(List<&2, U32>, List<&2, U32>, v => Con{c, v}, L.bz.app(d, tk), L.bz.rep(p, c), rot_rep(j, p, c))

def u32_cmp_self(a: U32) -> {U32.cmp(a, a) == EQ{} : Cmp}:
  match a:
    case U32{+w}:
      word_cmp_self(32n, w)

def cmp_self_list(xs: List<&2, U32>) -> {W.bwt.cmp(xs, xs) == EQ{} : Cmp}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, u32_cmp_self(x)) : {W.bwt.cmp.fin(_, W.bwt.cmp(t, t)) == EQ{} : Cmp}
      cmp_self_list(t)

def le_self_list(+xs: List<&2, U32>) -> {True{} == W.bwt.le(xs, xs) : Bool}:
  %Equal.sym(Cmp, W.bwt.cmp(xs, xs), EQ{}, cmp_self_list(xs)) : {True{} == Bool.not(Cmp.is_gt(_)) : Bool}
  {==}

def le_rot(+i: Nat, +j: Nat, +n: Nat, +c: U32) -> {True{} == W.bwt.le(W.bwt.rot(i, L.bz.rep(n, c)), W.bwt.rot(j, L.bz.rep(n, c))) : Bool}:
  %Equal.sym(List<&2, U32>, W.bwt.rot(i, L.bz.rep(n, c)), L.bz.rep(n, c), rot_rep(i, n, c)) : {True{} == W.bwt.le(_, W.bwt.rot(j, L.bz.rep(n, c))) : Bool}
  %Equal.sym(List<&2, U32>, W.bwt.rot(j, L.bz.rep(n, c)), L.bz.rep(n, c), rot_rep(j, n, c)) : {True{} == W.bwt.le(L.bz.rep(n, c), _) : Bool}
  le_self_list(L.bz.rep(n, c))

def ins_const(ys: List<&2, Nat>, +i: Nat, +n: Nat, +c: U32) -> {W.ref.ins(ys, i, L.bz.rep(n, c)) == Con{i, ys} : List<&2, Nat>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %le_rot(i, j, n, c) : {W.ref.ins.pick(_, i, j, t, W.ref.ins(t, i, L.bz.rep(n, c))) == Con{i, Con{j, t}} : List<&2, Nat>}
      {==}

def sort_const(ps: List<&2, Nat>, +n: Nat, +c: U32) -> {W.ref.sort(ps, L.bz.rep(n, c)) == ps : List<&2, Nat>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+i, +t}:
      %Equal.sym(List<&2, Nat>, W.ref.sort(t, L.bz.rep(n, c)), t, sort_const(t, n, c)) : {W.ref.ins(_, i, L.bz.rep(n, c)) == Con{i, t} : List<&2, Nat>}
      ins_const(t, i, n, c)

def final_rep(m: Nat, +c: U32, +d: U32) -> {W.ref.final(L.bz.rep(1n+m, c), d) == c : U32}:
  match m:
    case 0n:
      {==}
    case 1n+(+p):
      final_rep(p, c, c)

def lasts_upto(k: Nat, +i: Nat, +m: Nat, +c: U32) -> {W.ref.lasts(W.ref.upto(k, i), L.bz.rep(1n+m, c)) == L.bz.rep(k, c) : List<&2, U32>}:
  match k:
    case 0n:
      {==}
    case 1n+(+p):
      %Equal.sym(List<&2, U32>, W.bwt.rot(i, L.bz.rep(1n+m, c)), L.bz.rep(1n+m, c), rot_rep(i, 1n+m, c)) : {Con{W.ref.final(_, 0), W.ref.lasts(W.ref.upto(p, 1n+i), L.bz.rep(1n+m, c))} == L.bz.rep(1n+p, c) : List<&2, U32>}
      %Equal.sym(U32, W.ref.final(L.bz.rep(1n+m, c), 0), c, final_rep(m, c, 0)) : {Con{_, W.ref.lasts(W.ref.upto(p, 1n+i), L.bz.rep(1n+m, c))} == L.bz.rep(1n+p, c) : List<&2, U32>}
      Equal.cong(List<&2, U32>, List<&2, U32>, v => Con{c, v}, W.ref.lasts(W.ref.upto(p, 1n+i), L.bz.rep(1n+m, c)), L.bz.rep(p, c), lasts_upto(p, 1n+i, m, c))

def len_rep(n: Nat, +c: U32, +a: Nat) -> {L.bz.len.go(L.bz.rep(n, c), a) == Nat.add(n, a) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.trans(Nat, L.bz.len.go(L.bz.rep(p, c), 1n+a), Nat.add(p, 1n+a), 1n+Nat.add(p, a), len_rep(p, c, 1n+a), add_succ_r(p, a))

def len_rep_r(+n: Nat, +c: U32) -> {n == L.bz.len(L.bz.rep(n, c)) : Nat}:
  Equal.sym(Nat, L.bz.len(L.bz.rep(n, c)), n, Equal.trans(Nat, L.bz.len.go(L.bz.rep(n, c), 0n), Nat.add(n, 0n), n, len_rep(n, c, 0n), add_zero(n)))

def fwd_const(n: Nat, +c: U32) -> {W.ref.forward(L.bz.rep(n, c)) == W.Bzip2BwtList{L.bz.rep(n, c), 0} : W.Bzip2BwtList}:
  match n:
    case 0n:
      {==}
    case 1n+(+m):
      +xs = L.bz.rep(1n+m, c)
      %len_rep_r(1n+m, c) : {W.Bzip2BwtList{W.ref.lasts(W.ref.sort(W.ref.upto(_, 0n), xs), xs), U32.from_nat(W.ref.pos(W.ref.sort(W.ref.upto(_, 0n), xs), 0n))} == W.Bzip2BwtList{xs, 0} : W.Bzip2BwtList}
      %Equal.sym(List<&2, Nat>, W.ref.sort(W.ref.upto(1n+m, 0n), xs), W.ref.upto(1n+m, 0n), sort_const(W.ref.upto(1n+m, 0n), 1n+m, c)) : {W.Bzip2BwtList{W.ref.lasts(_, xs), U32.from_nat(W.ref.pos(_, 0n))} == W.Bzip2BwtList{xs, 0} : W.Bzip2BwtList}
      %Equal.sym(List<&2, U32>, W.ref.lasts(W.ref.upto(1n+m, 0n), xs), xs, lasts_upto(1n+m, 0n, m, c)) : {W.Bzip2BwtList{_, U32.from_nat(W.ref.pos(W.ref.upto(1n+m, 0n), 0n))} == W.Bzip2BwtList{xs, 0} : W.Bzip2BwtList}
      {==}

# the inverse's table: n equal rows

def reps(n: Nat, +r: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match n:
    case 0n:
      Nil{}
    case 1n+(+p):
      Con{r, reps(p, r)}

def empties_reps(n: Nat) -> {W.ref.empties(n) == reps(n, Nil{}) : List<&2, List<&2, U32>>}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.cong(List<&2, List<&2, U32>>, List<&2, List<&2, U32>>, v => Con{Nil{}, v}, W.ref.empties(p), reps(p, Nil{}), empties_reps(p))

def cons_reps(n: Nat, +c: U32, +r: List<&2, U32>) -> {W.ref.cons(L.bz.rep(n, c), reps(n, r)) == reps(n, Con{c, r}) : List<&2, List<&2, U32>>}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.cong(List<&2, List<&2, U32>>, List<&2, List<&2, U32>>, v => Con{Con{c, r}, v}, W.ref.cons(L.bz.rep(p, c), reps(p, r)), reps(p, Con{c, r}), cons_reps(p, c, r))

def rins_same(n: Nat, +r: List<&2, U32>) -> {W.ref.rins(reps(n, r), r) == Con{r, reps(n, r)} : List<&2, List<&2, U32>>}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      %le_self_list(r) : {W.ref.rins.pick(_, r, r, reps(p, r), W.ref.rins(reps(p, r), r)) == Con{r, Con{r, reps(p, r)}} : List<&2, List<&2, U32>>}
      {==}

def rsort_reps(n: Nat, +r: List<&2, U32>) -> {W.ref.rsort(reps(n, r)) == reps(n, r) : List<&2, List<&2, U32>>}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      %Equal.sym(List<&2, List<&2, U32>>, W.ref.rsort(reps(p, r)), reps(p, r), rsort_reps(p, r)) : {W.ref.rins(_, r) == Con{r, reps(p, r)} : List<&2, List<&2, U32>>}
      rins_same(p, r)

def rounds_const(k: Nat, +n: Nat, +c: U32, +j: Nat) -> {W.ref.rounds(k, L.bz.rep(n, c), reps(n, L.bz.rep(j, c))) == reps(n, L.bz.rep(Nat.add(k, j), c)) : List<&2, List<&2, U32>>}:
  match k:
    case 0n:
      {==}
    case 1n+(+p):
      %Equal.sym(List<&2, List<&2, U32>>, W.ref.cons(L.bz.rep(n, c), reps(n, L.bz.rep(j, c))), reps(n, L.bz.rep(1n+j, c)), cons_reps(n, c, L.bz.rep(j, c))) : {W.ref.rounds(p, L.bz.rep(n, c), W.ref.rsort(_)) == reps(n, L.bz.rep(1n+Nat.add(p, j), c)) : List<&2, List<&2, U32>>}
      %Equal.sym(List<&2, List<&2, U32>>, W.ref.rsort(reps(n, L.bz.rep(1n+j, c))), reps(n, L.bz.rep(1n+j, c)), rsort_reps(n, L.bz.rep(1n+j, c))) : {W.ref.rounds(p, L.bz.rep(n, c), _) == reps(n, L.bz.rep(1n+Nat.add(p, j), c)) : List<&2, List<&2, U32>>}
      %add_succ_r(p, j) : {W.ref.rounds(p, L.bz.rep(n, c), reps(n, L.bz.rep(1n+j, c))) == reps(n, L.bz.rep(_, c)) : List<&2, List<&2, U32>>}
      rounds_const(p, n, c, 1n+j)

def inv_const(n: Nat, +c: U32) -> {W.ref.inverse(L.bz.rep(n, c), 0) == Done{L.bz.rep(n, c)} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}:
  match n:
    case 0n:
      {==}
    case 1n+(+m):
      +xs = L.bz.rep(1n+m, c)
      %len_rep_r(1n+m, c) : {W.ref.inverse.n(_, xs, 0) == Done{xs} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
      %Equal.sym(List<&2, List<&2, U32>>, W.ref.empties(1n+m), reps(1n+m, Nil{}), empties_reps(1n+m)) : {W.ref.row(List.get(&2, List<&2, U32>, W.ref.rounds(1n+m, xs, _), 0n)) == Done{xs} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
      %Equal.sym(List<&2, List<&2, U32>>, W.ref.rounds(1n+m, xs, reps(1n+m, L.bz.rep(0n, c))), reps(1n+m, L.bz.rep(Nat.add(1n+m, 0n), c)), rounds_const(1n+m, 1n+m, c, 0n)) : {W.ref.row(List.get(&2, List<&2, U32>, _, 0n)) == Done{xs} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
      %Equal.sym(Nat, Nat.add(1n+m, 0n), 1n+m, add_zero(1n+m)) : {W.ref.row(List.get(&2, List<&2, U32>, reps(1n+m, L.bz.rep(_, c)), 0n)) == Done{xs} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
      {==}

# Octets: a list of copies, masked; a list masked makes the same Octets

def mask_rep(n: Nat, +b: U32) -> {B.mask(L.bz.rep(n, b)) == L.bz.rep(n, B.byte(b)) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      Equal.cong(List<&2, U32>, List<&2, U32>, v => Con{B.byte(b), v}, B.mask(L.bz.rep(p, b)), L.bz.rep(p, B.byte(b)), mask_rep(p, b))

def of_list_mask(+ys: List<&2, U32>) -> {B.Octets.of_list(B.mask(ys)) == B.Octets.of_list(ys) : B.Octets}:
  %BL.octets_to_of(ys) : {B.Octets.of_list(_) == B.Octets.of_list(ys) : B.Octets}
  BL.octets_of_list_idempotent(ys)

# a block of copies of a byte already masked
def const_c(+n: Nat, +c: U32, hc: {c == B.byte(c) : U32}) -> {Laws.bwt_undo_ref(W.bwt.octets(W.ref.forward(L.bz.rep(n, c)))) == Done{B.Octets.of_list(L.bz.rep(n, c))} : Result<&2, &2, E.Bzip2Error, B.Octets>}:
  +xs = L.bz.rep(n, c)
  %Equal.sym(W.Bzip2BwtList, W.ref.forward(xs), W.Bzip2BwtList{xs, 0}, fwd_const(n, c)) : {Laws.bwt_undo_ref(W.bwt.octets(_)) == Done{B.Octets.of_list(xs)} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(xs)), B.mask(xs), BL.octets_to_of(xs)) : {W.bwt.res(W.ref.inverse(_, 0)) == Done{B.Octets.of_list(xs)} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %Equal.sym(List<&2, U32>, B.mask(xs), L.bz.rep(n, B.byte(c)), mask_rep(n, c)) : {W.bwt.res(W.ref.inverse(_, 0)) == Done{B.Octets.of_list(xs)} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %hc : {W.bwt.res(W.ref.inverse(L.bz.rep(n, _), 0)) == Done{B.Octets.of_list(xs)} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %Equal.sym(Result<&2, &2, E.Bzip2Error, List<&2, U32>>, W.ref.inverse(xs, 0), Done{xs}, inv_const(n, c)) : {W.bwt.res(_) == Done{B.Octets.of_list(xs)} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  {==}

def Laws.bwt_ref_round_trip_constant(b, n):
  +c = B.byte(b)
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(L.bz.rep(n, b))), B.mask(L.bz.rep(n, b)), BL.octets_to_of(L.bz.rep(n, b))) : {Laws.bwt_undo_ref(W.bwt.octets(W.ref.forward(_))) == Done{B.Octets.of_list(L.bz.rep(n, b))} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %Equal.sym(List<&2, U32>, B.mask(L.bz.rep(n, b)), L.bz.rep(n, c), mask_rep(n, b)) : {Laws.bwt_undo_ref(W.bwt.octets(W.ref.forward(_))) == Done{B.Octets.of_list(L.bz.rep(n, b))} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %of_list_mask(L.bz.rep(n, b)) : {Laws.bwt_undo_ref(W.bwt.octets(W.ref.forward(L.bz.rep(n, c)))) == Done{_} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %Equal.sym(List<&2, U32>, B.mask(L.bz.rep(n, b)), L.bz.rep(n, c), mask_rep(n, b)) : {Laws.bwt_undo_ref(W.bwt.octets(W.ref.forward(L.bz.rep(n, c)))) == Done{B.Octets.of_list(_)} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  const_c(n, c, byte_idem(b))


# Two-byte blocks: the comparisons, then the transform and its inverse

def two.le0(+x: U32, +y: U32, e1: {LT{} == U32.cmp(x, y) : Cmp}) -> {True{} == W.bwt.le([x, y], [y, x]) : Bool}:
  %e1 : {True{} == Bool.not(Cmp.is_gt(W.bwt.cmp.fin(_, W.bwt.cmp([y], [x])))) : Bool}
  {==}

def two.le1(+y: U32, +x: U32, e2: {GT{} == U32.cmp(y, x) : Cmp}) -> {False{} == W.bwt.le([y], [x]) : Bool}:
  %e2 : {False{} == Bool.not(Cmp.is_gt(W.bwt.cmp.fin(_, W.bwt.cmp(Nil{}, Nil{})))) : Bool}
  {==}

def two.le2(+y: U32, +x: U32, e2: {GT{} == U32.cmp(y, x) : Cmp}) -> {False{} == W.bwt.le([y, x], [x, y]) : Bool}:
  %e2 : {False{} == Bool.not(Cmp.is_gt(W.bwt.cmp.fin(_, W.bwt.cmp([x], [y])))) : Bool}
  {==}

def two.le0g(+x: U32, +y: U32, e1: {GT{} == U32.cmp(x, y) : Cmp}) -> {False{} == W.bwt.le([x, y], [y, x]) : Bool}:
  %e1 : {False{} == Bool.not(Cmp.is_gt(W.bwt.cmp.fin(_, W.bwt.cmp([y], [x])))) : Bool}
  {==}

def two.le1g(+x: U32, +y: U32, e1: {GT{} == U32.cmp(x, y) : Cmp}) -> {False{} == W.bwt.le([x], [y]) : Bool}:
  %e1 : {False{} == Bool.not(Cmp.is_gt(W.bwt.cmp.fin(_, W.bwt.cmp(Nil{}, Nil{})))) : Bool}
  {==}

def two.iseq(+x: U32, +y: U32, e1: {EQ{} == U32.cmp(x, y) : Cmp}) -> {U32.is_eq(x, y) == True{} : Bool}:
  %e1 : {Cmp.is_eq(_) == True{} : Bool}
  {==}

def two.fwd_lt(+x: U32, +y: U32, le0: {True{} == W.bwt.le([x, y], [y, x]) : Bool}) -> {W.ref.forward([x, y]) == W.Bzip2BwtList{[y, x], 0} : W.Bzip2BwtList}:
  %le0 : {W.Bzip2BwtList{W.ref.lasts(W.ref.ins.pick(_, 0n, 1n, Nil{}, W.ref.ins(Nil{}, 0n, [x, y])), [x, y]), U32.from_nat(W.ref.pos(W.ref.ins.pick(_, 0n, 1n, Nil{}, W.ref.ins(Nil{}, 0n, [x, y])), 0n))} == W.Bzip2BwtList{[y, x], 0} : W.Bzip2BwtList}
  {==}

def two.fwd_gt(+x: U32, +y: U32, le0: {False{} == W.bwt.le([x, y], [y, x]) : Bool}) -> {W.ref.forward([x, y]) == W.Bzip2BwtList{[x, y], 1} : W.Bzip2BwtList}:
  %le0 : {W.Bzip2BwtList{W.ref.lasts(W.ref.ins.pick(_, 0n, 1n, Nil{}, W.ref.ins(Nil{}, 0n, [x, y])), [x, y]), U32.from_nat(W.ref.pos(W.ref.ins.pick(_, 0n, 1n, Nil{}, W.ref.ins(Nil{}, 0n, [x, y])), 0n))} == W.Bzip2BwtList{[x, y], 1} : W.Bzip2BwtList}
  {==}

def two.inv_lt(+x: U32, +y: U32, le1: {False{} == W.bwt.le([y], [x]) : Bool}, le2: {False{} == W.bwt.le([y, x], [x, y]) : Bool}) -> {W.ref.inverse([y, x], 0) == Done{[x, y]} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}:
  %le1 : {W.ref.row(List.get(&2, List<&2, U32>, W.ref.rounds(1n, [y, x], W.ref.rins.pick(_, [y], [x], Nil{}, W.ref.rins(Nil{}, [y]))), 0n)) == Done{[x, y]} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  %le2 : {W.ref.row(List.get(&2, List<&2, U32>, W.ref.rins.pick(_, [y, x], [x, y], Nil{}, W.ref.rins(Nil{}, [y, x])), 0n)) == Done{[x, y]} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  {==}

def two.inv_gt(+x: U32, +y: U32, le1: {False{} == W.bwt.le([x], [y]) : Bool}, le0: {False{} == W.bwt.le([x, y], [y, x]) : Bool}) -> {W.ref.inverse([x, y], 1) == Done{[x, y]} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}:
  %le1 : {W.ref.row(List.get(&2, List<&2, U32>, W.ref.rounds(1n, [x, y], W.ref.rins.pick(_, [x], [y], Nil{}, W.ref.rins(Nil{}, [x]))), 1n)) == Done{[x, y]} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  %le0 : {W.ref.row(List.get(&2, List<&2, U32>, W.ref.rins.pick(_, [x, y], [y, x], Nil{}, W.ref.rins(Nil{}, [x, y])), 1n)) == Done{[x, y]} : Result<&2, &2, E.Bzip2Error, List<&2, U32>>}
  {==}


# Two-byte blocks [x, y]: by cases on how x compares with y. Equal bytes
# are the constant case; otherwise the two rotations are [x, y] and [y, x]
# and each round of the inverse sorts two rows of different bytes.

def cmp_flip(+c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def fin_flip(+t: Cmp, +x: Bool, +y: Bool) -> {Word.cmp.fin(y, x, cmp_flip(t)) == cmp_flip(Word.cmp.fin(x, y, t)) : Cmp}:
  match t:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      match x y:
        case True{} True{}:
          {==}
        case True{} False{}:
          {==}
        case False{} True{}:
          {==}
        case False{} False{}:
          {==}

def word_flip(+n: Nat, +a: Word(n), +b: Word(n)) -> {Word.cmp(n, b, a) == cmp_flip(Word.cmp(n, a, b)) : Cmp}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          %Equal.sym(Cmp, Word.cmp(p, bt, at), cmp_flip(Word.cmp(p, at, bt)), word_flip(p, at, bt)) : {Word.cmp.fin(y, x, _) == cmp_flip(Word.cmp.fin(x, y, Word.cmp(p, at, bt))) : Cmp}
          fin_flip(Word.cmp(p, at, bt), x, y)

def u32_flip(+a: U32, +b: U32) -> {U32.cmp(b, a) == cmp_flip(U32.cmp(a, b)) : Cmp}:
  match a b:
    case U32{+wa} U32{+wb}:
      word_flip(32n, wa, wb)

# x before y: the rotations sort as [x, y], [y, x]
def two_lt(+x: U32, +y: U32, +e1: {LT{} == U32.cmp(x, y) : Cmp}, +e2: {GT{} == U32.cmp(y, x) : Cmp}, +hx: {x == B.byte(x) : U32}, +hy: {y == B.byte(y) : U32}) -> {Laws.bwt_undo_ref(W.bwt.octets(W.ref.forward([x, y]))) == Done{B.Octets.of_list([x, y])} : Result<&2, &2, E.Bzip2Error, B.Octets>}:
  +le0 = two.le0(x, y, e1)
  +le1 = two.le1(y, x, e2)
  +le2 = two.le2(y, x, e2)
  %Equal.sym(W.Bzip2BwtList, W.ref.forward([x, y]), W.Bzip2BwtList{[y, x], 0}, two.fwd_lt(x, y, le0)) : {Laws.bwt_undo_ref(W.bwt.octets(_)) == Done{B.Octets.of_list([x, y])} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([y, x])), B.mask([y, x]), BL.octets_to_of([y, x])) : {W.bwt.res(W.ref.inverse(_, 0)) == Done{B.Octets.of_list([x, y])} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %hx : {W.bwt.res(W.ref.inverse([B.byte(y), _], 0)) == Done{B.Octets.of_list([x, y])} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %hy : {W.bwt.res(W.ref.inverse([_, x], 0)) == Done{B.Octets.of_list([x, y])} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %Equal.sym(Result<&2, &2, E.Bzip2Error, List<&2, U32>>, W.ref.inverse([y, x], 0), Done{[x, y]}, two.inv_lt(x, y, le1, le2)) : {W.bwt.res(_) == Done{B.Octets.of_list([x, y])} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  {==}

def two_gt(+x: U32, +y: U32, +e1: {GT{} == U32.cmp(x, y) : Cmp}, +hx: {x == B.byte(x) : U32}, +hy: {y == B.byte(y) : U32}) -> {Laws.bwt_undo_ref(W.bwt.octets(W.ref.forward([x, y]))) == Done{B.Octets.of_list([x, y])} : Result<&2, &2, E.Bzip2Error, B.Octets>}:
  +le0 = two.le0g(x, y, e1)
  +le1 = two.le1g(x, y, e1)
  %Equal.sym(W.Bzip2BwtList, W.ref.forward([x, y]), W.Bzip2BwtList{[x, y], 1}, two.fwd_gt(x, y, le0)) : {Laws.bwt_undo_ref(W.bwt.octets(_)) == Done{B.Octets.of_list([x, y])} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([x, y])), B.mask([x, y]), BL.octets_to_of([x, y])) : {W.bwt.res(W.ref.inverse(_, 1)) == Done{B.Octets.of_list([x, y])} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %hx : {W.bwt.res(W.ref.inverse([_, B.byte(y)], 1)) == Done{B.Octets.of_list([x, y])} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %hy : {W.bwt.res(W.ref.inverse([x, _], 1)) == Done{B.Octets.of_list([x, y])} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %Equal.sym(Result<&2, &2, E.Bzip2Error, List<&2, U32>>, W.ref.inverse([x, y], 1), Done{[x, y]}, two.inv_gt(x, y, le1, le0)) : {W.bwt.res(_) == Done{B.Octets.of_list([x, y])} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  {==}

def two_eq(+x: U32, +y: U32, +e1: {EQ{} == U32.cmp(x, y) : Cmp}, +hx: {x == B.byte(x) : U32}) -> {Laws.bwt_undo_ref(W.bwt.octets(W.ref.forward([x, y]))) == Done{B.Octets.of_list([x, y])} : Result<&2, &2, E.Bzip2Error, B.Octets>}:
  +xy = u32_eq(x, y, two.iseq(x, y, e1))
  %xy : {Laws.bwt_undo_ref(W.bwt.octets(W.ref.forward([x, _]))) == Done{B.Octets.of_list([x, _])} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  const_c(2n, x, hx)

def two_c(+x: U32, +y: U32, +c: Cmp, +ec: {c == U32.cmp(x, y) : Cmp}, +hx: {x == B.byte(x) : U32}, +hy: {y == B.byte(y) : U32}) -> {Laws.bwt_undo_ref(W.bwt.octets(W.ref.forward([x, y]))) == Done{B.Octets.of_list([x, y])} : Result<&2, &2, E.Bzip2Error, B.Octets>}:
  match c:
    case LT{}:
      two_lt(x, y, ec, Equal.trans(Cmp, GT{}, cmp_flip(U32.cmp(x, y)), U32.cmp(y, x), Equal.cong(Cmp, Cmp, v => cmp_flip(v), LT{}, U32.cmp(x, y), ec), Equal.sym(Cmp, U32.cmp(y, x), cmp_flip(U32.cmp(x, y)), u32_flip(x, y))), hx, hy)
    case EQ{}:
      two_eq(x, y, ec, hx)
    case GT{}:
      two_gt(x, y, ec, hx, hy)

def Laws.bwt_ref_round_trip_two(a, b):
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list([a, b])), B.mask([a, b]), BL.octets_to_of([a, b])) : {Laws.bwt_undo_ref(W.bwt.octets(W.ref.forward(_))) == Done{B.Octets.of_list([a, b])} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  %of_list_mask([a, b]) : {Laws.bwt_undo_ref(W.bwt.octets(W.ref.forward([B.byte(a), B.byte(b)]))) == Done{_} : Result<&2, &2, E.Bzip2Error, B.Octets>}
  two_c(B.byte(a), B.byte(b), U32.cmp(B.byte(a), B.byte(b)), {==}, byte_idem(a), byte_idem(b))

# Vectors, by computation

def Laws.rle1_encode_run():
  {==}

def Laws.mtf_covers_banana():
  {==}

def Laws.symbol_map_banana():
  {==}

def Laws.mtf_encode_banana():
  {==}

def Laws.mtf_encode_run():
  {==}

def Laws.mtf_decode_too_large():
  {==}

def Laws.mtf_decode_bad_symbol():
  {==}

def Laws.bwt_banana():
  {==}

def Laws.bwt_ref_banana():
  {==}

def Laws.bwt_inverse_banana():
  {==}

def Laws.bwt_inverse_ref_banana():
  {==}

def Laws.bwt_inverse_bad_ptr():
  {==}

def Laws.not_magic_byte():
  {==}

def Laws.decode_empty_stream():
  {==}

def Laws.decode_two_streams():
  {==}

def Laws.decode_trailing_refused():
  {==}

def Laws.compress_empty():
  {==}

def Laws.crc_check():
  {==}
