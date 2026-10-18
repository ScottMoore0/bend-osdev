# Proof helpers for bend-osdev-timerqueue: the order of times and timers.
import Base
import ../word64/word64.bend as W
import ../word64/LAWS.bend as WL
import ../word64/PROOF.bend as WP
import ./timer.bend as T

# Contradictions

def ab.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def ab.tf(+e: {True{} == False{} : Bool}) -> Empty:
  %e : ab.bool(_)
  Unit{}

def ab.ft(+e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : ab.bool(_)
  Unit{}

def ab.is_lt(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case o:
      Empty

def ab.is_eq(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Unit
    case o:
      Empty

def ab.is_gt(c: Cmp) -> Type:
  match c:
    case GT{}:
      Unit
    case o:
      Empty

def ab.eq_lt(+e: {EQ{} == LT{} : Cmp}) -> Empty:
  %e : ab.is_eq(_)
  Unit{}

def ab.gt_lt(+e: {GT{} == LT{} : Cmp}) -> Empty:
  %e : ab.is_gt(_)
  Unit{}

def ab.lt_eq(+e: {LT{} == EQ{} : Cmp}) -> Empty:
  %e : ab.is_lt(_)
  Unit{}

def ab.gt_eq(+e: {GT{} == EQ{} : Cmp}) -> Empty:
  %e : ab.is_gt(_)
  Unit{}

def ab.lt_gt(+e: {LT{} == GT{} : Cmp}) -> Empty:
  %e : ab.is_lt(_)
  Unit{}

def ab.eq_gt(+e: {EQ{} == GT{} : Cmp}) -> Empty:
  %e : ab.is_eq(_)
  Unit{}

def ab.some(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case Some{x}:
      Unit
    case None{}:
      Empty

def ab.none_some(-A: Data, -x: A, +e: {None{} == Some{x} : Maybe<&2, A>}) -> Empty:
  %Equal.sym(Maybe<&2, A>, None{}, Some{x}, e) : ab.some(A, _)
  Unit{}

def ab.some_none(-A: Data, -x: A, +e: {Some{x} == None{} : Maybe<&2, A>}) -> Empty:
  %e : ab.some(A, _)
  Unit{}

# Bool

def bo.and_l(x: Bool, -y: Bool, +e: {Bool.and(x, y) == True{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ab.ft(e))

def bo.and_r(x: Bool, -y: Bool, +e: {Bool.and(x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      e
    case False{}:
      Empty.absurd({y == True{} : Bool}, ab.ft(e))

def bo.and_intro(-x: Bool, -y: Bool, +ex: {x == True{} : Bool}, +ey: {y == True{} : Bool}) -> {Bool.and(x, y) == True{} : Bool}:
  %Equal.sym(Bool, x, True{}, ex) : {Bool.and(_, y) == True{} : Bool}
  ey

def bo.and_false_l(-x: Bool, -y: Bool, +ex: {x == False{} : Bool}) -> {Bool.and(x, y) == False{} : Bool}:
  %Equal.sym(Bool, x, False{}, ex) : {Bool.and(_, y) == False{} : Bool}
  {==}

def bo.and_false_r(x: Bool, -y: Bool, +ey: {y == False{} : Bool}) -> {Bool.and(x, y) == False{} : Bool}:
  match x:
    case True{}:
      ey
    case False{}:
      {==}

# from and(x, y) == False and x == True: y == False
def bo.and_false_rest(x: Bool, -y: Bool, +e: {Bool.and(x, y) == False{} : Bool}, +ex: {x == True{} : Bool}) -> {y == False{} : Bool}:
  match x:
    case True{}:
      e
    case False{}:
      Empty.absurd({y == False{} : Bool}, ab.ft(ex))

def bo.not_true(x: Bool, +e: {x == True{} : Bool}, +f: {x == False{} : Bool}) -> Empty:
  match x:
    case True{}:
      ab.tf(f)
    case False{}:
      ab.ft(e)

# Cmp

def cm.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def cm.lt_of(c: Cmp, +e: {Cmp.is_lt(c) == True{} : Bool}) -> {c == LT{} : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({EQ{} == LT{} : Cmp}, ab.ft(e))
    case GT{}:
      Empty.absurd({GT{} == LT{} : Cmp}, ab.ft(e))

def cm.eq_of(c: Cmp, +e: {Cmp.is_eq(c) == True{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, ab.ft(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, ab.ft(e))

def cm.is_lt_of(-c: Cmp, +e: {c == LT{} : Cmp}) -> {Cmp.is_lt(c) == True{} : Bool}:
  %Equal.sym(Cmp, c, LT{}, e) : {Cmp.is_lt(_) == True{} : Bool}
  {==}

def cm.is_le_of_lt(-c: Cmp, +e: {c == LT{} : Cmp}) -> {Cmp.is_le(c) == True{} : Bool}:
  %Equal.sym(Cmp, c, LT{}, e) : {Cmp.is_le(_) == True{} : Bool}
  {==}

def cm.le_of_lt(c: Cmp, +e: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_le(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({True{} == True{} : Bool}, ab.ft(e))
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, ab.ft(e))

# is_le(c) and not is_lt(c): c is EQ
def cm.eq_of_le(c: Cmp, +e: {Cmp.is_le(c) == True{} : Bool}, +f: {Cmp.is_lt(c) == False{} : Bool}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, ab.tf(f))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, ab.ft(e))

# flipping turns not-less into at-most and the other way
def cm.le_flip(c: Cmp, +e: {Cmp.is_lt(c) == False{} : Bool}) -> {Cmp.is_le(cm.flip(c)) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, ab.tf(e))
    case EQ{}:
      {==}
    case GT{}:
      {==}

def cm.lt_flip(c: Cmp, +e: {Cmp.is_le(c) == False{} : Bool}) -> {Cmp.is_lt(cm.flip(c)) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, ab.tf(e))
    case EQ{}:
      Empty.absurd({False{} == True{} : Bool}, ab.tf(e))
    case GT{}:
      {==}

def cm.not_le_flip(c: Cmp, +e: {Cmp.is_lt(c) == True{} : Bool}) -> {Cmp.is_le(cm.flip(c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({True{} == False{} : Bool}, ab.ft(e))
    case GT{}:
      Empty.absurd({True{} == False{} : Bool}, ab.ft(e))

def cm.not_lt_flip(c: Cmp, +e: {Cmp.is_le(c) == True{} : Bool}) -> {Cmp.is_lt(cm.flip(c)) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({True{} == False{} : Bool}, ab.ft(e))

# Words: Base's order on Word(n), compared from the top bit down

def wd.fin_refl(x: Bool) -> {Word.cmp.fin(x, x, EQ{}) == EQ{} : Cmp}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def wd.refl(n: Nat, a: Word(n)) -> {Word.cmp(n, a, a) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a:
        case WCon{+x, +at}:
          %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, wd.refl(p, at)) : {Word.cmp.fin(x, x, _) == EQ{} : Cmp}
          wd.fin_refl(x)

def wd.fin_eq_tail(c: Cmp, -x: Bool, -y: Bool, +e: {Word.cmp.fin(x, y, c) == EQ{} : Cmp}) -> {c == EQ{} : Cmp}:
  match c:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, ab.lt_eq(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, ab.gt_eq(e))

def wd.bool_eq(x: Bool, y: Bool, +e: {Bool.cmp(x, y) == EQ{} : Cmp}) -> {x == y : Bool}:
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({False{} == True{} : Bool}, ab.lt_eq(e))
    case True{} False{}:
      Empty.absurd({True{} == False{} : Bool}, ab.gt_eq(e))
    case True{} True{}:
      {==}

def wd.fin_eq_head(c: Cmp, x: Bool, y: Bool, +e: {Word.cmp.fin(x, y, c) == EQ{} : Cmp}) -> {x == y : Bool}:
  match c:
    case LT{}:
      Empty.absurd({x == y : Bool}, ab.lt_eq(e))
    case EQ{}:
      wd.bool_eq(x, y, e)
    case GT{}:
      Empty.absurd({x == y : Bool}, ab.gt_eq(e))

def wd.eq(n: Nat, a: Word(n), b: Word(n), +e: {Word.cmp(n, a, b) == EQ{} : Cmp}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          %wd.eq(p, at, bt, wd.fin_eq_tail(Word.cmp(p, at, bt), x, y, e)) : {WCon{x, at} == WCon{y, _} : Word(1n+p)}
          %wd.fin_eq_head(Word.cmp(p, at, bt), x, y, e) : {WCon{x, at} == WCon{_, at} : Word(1n+p)}
          {==}

def wd.bool_flip(x: Bool, y: Bool) -> {Bool.cmp(y, x) == cm.flip(Bool.cmp(x, y)) : Cmp}:
  match x y:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def wd.fin_flip(c: Cmp, x: Bool, y: Bool) -> {Word.cmp.fin(y, x, cm.flip(c)) == cm.flip(Word.cmp.fin(x, y, c)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      wd.bool_flip(x, y)
    case GT{}:
      {==}

def wd.flip(n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, b, a) == cm.flip(Word.cmp(n, a, b)) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          %Equal.sym(Cmp, Word.cmp(p, bt, at), cm.flip(Word.cmp(p, at, bt)), wd.flip(p, at, bt)) : {Word.cmp.fin(y, x, _) == cm.flip(Word.cmp.fin(x, y, Word.cmp(p, at, bt))) : Cmp}
          wd.fin_flip(Word.cmp(p, at, bt), x, y)

def wd.bool_trans(x: Bool, y: Bool, z: Bool, +h1: {Bool.cmp(x, y) == LT{} : Cmp}, +h2: {Bool.cmp(y, z) == LT{} : Cmp}) -> {Bool.cmp(x, z) == LT{} : Cmp}:
  match x y z:
    case False{} False{} z:
      Empty.absurd({Bool.cmp(False{}, z) == LT{} : Cmp}, ab.eq_lt(h1))
    case False{} True{} False{}:
      Empty.absurd({EQ{} == LT{} : Cmp}, ab.gt_lt(h2))
    case False{} True{} True{}:
      Empty.absurd({LT{} == LT{} : Cmp}, ab.eq_lt(h2))
    case True{} False{} z:
      Empty.absurd({Bool.cmp(True{}, z) == LT{} : Cmp}, ab.gt_lt(h1))
    case True{} True{} z:
      Empty.absurd({Bool.cmp(True{}, z) == LT{} : Cmp}, ab.eq_lt(h1))

def wd.fin_trans(c1: Cmp, c2: Cmp, +p: Nat, +x: Bool, +y: Bool, +z: Bool, +at: Word(p), +bt: Word(p), +ct: Word(p), +e1: {Word.cmp(p, at, bt) == c1 : Cmp}, +e2: {Word.cmp(p, bt, ct) == c2 : Cmp}, +h1: {Word.cmp.fin(x, y, c1) == LT{} : Cmp}, +h2: {Word.cmp.fin(y, z, c2) == LT{} : Cmp}, ih: {Word.cmp(p, at, bt) == LT{} : Cmp} -> {Word.cmp(p, bt, ct) == LT{} : Cmp} -> {Word.cmp(p, at, ct) == LT{} : Cmp}) -> {Word.cmp.fin(x, z, Word.cmp(p, at, ct)) == LT{} : Cmp}:
  match c1 c2:
    case LT{} LT{}:
      %Equal.sym(Cmp, Word.cmp(p, at, ct), LT{}, ih(e1, e2)) : {Word.cmp.fin(x, z, _) == LT{} : Cmp}
      {==}
    case LT{} EQ{}:
      %wd.eq(p, bt, ct, e2) : {Word.cmp.fin(x, z, Word.cmp(p, at, _)) == LT{} : Cmp}
      %Equal.sym(Cmp, Word.cmp(p, at, bt), LT{}, e1) : {Word.cmp.fin(x, z, _) == LT{} : Cmp}
      {==}
    case EQ{} LT{}:
      %Equal.sym(Word(p), at, bt, wd.eq(p, at, bt, e1)) : {Word.cmp.fin(x, z, Word.cmp(p, _, ct)) == LT{} : Cmp}
      %Equal.sym(Cmp, Word.cmp(p, bt, ct), LT{}, e2) : {Word.cmp.fin(x, z, _) == LT{} : Cmp}
      {==}
    case EQ{} EQ{}:
      %Equal.trans(Word(p), at, bt, ct, wd.eq(p, at, bt, e1), wd.eq(p, bt, ct, e2)) : {Word.cmp.fin(x, z, Word.cmp(p, at, _)) == LT{} : Cmp}
      %Equal.sym(Cmp, Word.cmp(p, at, at), EQ{}, wd.refl(p, at)) : {Word.cmp.fin(x, z, _) == LT{} : Cmp}
      wd.bool_trans(x, y, z, h1, h2)
    case GT{} c2:
      Empty.absurd({Word.cmp.fin(x, z, Word.cmp(p, at, ct)) == LT{} : Cmp}, ab.gt_lt(h1))
    case c1 GT{}:
      Empty.absurd({Word.cmp.fin(x, z, Word.cmp(p, at, ct)) == LT{} : Cmp}, ab.gt_lt(h2))

def wd.lt_trans(n: Nat, a: Word(n), b: Word(n), c: Word(n), +h1: {Word.cmp(n, a, b) == LT{} : Cmp}, +h2: {Word.cmp(n, b, c) == LT{} : Cmp}) -> {Word.cmp(n, a, c) == LT{} : Cmp}:
  match n:
    case 0n:
      Empty.absurd({Word.cmp(0n, a, c) == LT{} : Cmp}, ab.eq_lt(h1))
    case 1n+ +p:
      match a b c:
        case WCon{+x, +at} WCon{+y, +bt} WCon{+z, +ct}:
          wd.fin_trans(Word.cmp(p, at, bt), Word.cmp(p, bt, ct), p, x, y, z, at, bt, ct, {==}, {==}, h1, h2, u => w => wd.lt_trans(p, at, bt, ct, u, w))

# U32's order, as Bools

def ult(+a: U32, +b: U32) -> Bool:
  Cmp.is_lt(U32.cmp(a, b))

def ule(+a: U32, +b: U32) -> Bool:
  Cmp.is_le(U32.cmp(a, b))

def u.refl(a: U32) -> {U32.cmp(a, a) == EQ{} : Cmp}:
  match a:
    case U32{+w}:
      wd.refl(32n, w)

def u.eq(a: U32, b: U32, +e: {U32.cmp(a, b) == EQ{} : Cmp}) -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      %wd.eq(32n, x, y, e) : {U32{x} == U32{_} : U32}
      {==}

def u.flip(a: U32, b: U32) -> {U32.cmp(b, a) == cm.flip(U32.cmp(a, b)) : Cmp}:
  match a b:
    case U32{+x} U32{+y}:
      wd.flip(32n, x, y)

def u.cmp_lt_trans(a: U32, b: U32, c: U32, +h1: {U32.cmp(a, b) == LT{} : Cmp}, +h2: {U32.cmp(b, c) == LT{} : Cmp}) -> {U32.cmp(a, c) == LT{} : Cmp}:
  match a b c:
    case U32{+x} U32{+y} U32{+z}:
      wd.lt_trans(32n, x, y, z, h1, h2)

def u.le_refl(+a: U32) -> {ule(a, a) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(a, a), EQ{}, u.refl(a)) : {Cmp.is_le(_) == True{} : Bool}
  {==}

def ab.lt_eqc(c: Cmp, +h: {c == EQ{} : Cmp}, +e: {Cmp.is_lt(c) == True{} : Bool}) -> Empty:
  match c:
    case LT{}:
      ab.lt_eq(h)
    case EQ{}:
      ab.ft(e)
    case GT{}:
      ab.gt_eq(h)

def u.lt_irrefl(+a: U32, +e: {ult(a, a) == True{} : Bool}) -> Empty:
  ab.lt_eqc(U32.cmp(a, a), u.refl(a), e)

def u.le_of_lt(+a: U32, +b: U32, +e: {ult(a, b) == True{} : Bool}) -> {ule(a, b) == True{} : Bool}:
  cm.le_of_lt(U32.cmp(a, b), e)

def u.lt_trans(+a: U32, +b: U32, +c: U32, +h1: {ult(a, b) == True{} : Bool}, +h2: {ult(b, c) == True{} : Bool}) -> {ult(a, c) == True{} : Bool}:
  cm.is_lt_of(U32.cmp(a, c), u.cmp_lt_trans(a, b, c, cm.lt_of(U32.cmp(a, b), h1), cm.lt_of(U32.cmp(b, c), h2)))

def u.not_lt(+a: U32, +b: U32, +e: {ult(a, b) == False{} : Bool}) -> {ule(b, a) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(b, a), cm.flip(U32.cmp(a, b)), u.flip(a, b)) : {Cmp.is_le(_) == True{} : Bool}
  cm.le_flip(U32.cmp(a, b), e)

def u.not_le(+a: U32, +b: U32, +e: {ule(a, b) == False{} : Bool}) -> {ult(b, a) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(b, a), cm.flip(U32.cmp(a, b)), u.flip(a, b)) : {Cmp.is_lt(_) == True{} : Bool}
  cm.lt_flip(U32.cmp(a, b), e)

# a < b: not b <= a
def u.lt_not_le(+a: U32, +b: U32, +e: {ult(a, b) == True{} : Bool}) -> {ule(b, a) == False{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(b, a), cm.flip(U32.cmp(a, b)), u.flip(a, b)) : {Cmp.is_le(_) == False{} : Bool}
  cm.not_le_flip(U32.cmp(a, b), e)

# a <= b: not b < a
def u.le_not_lt(+a: U32, +b: U32, +e: {ule(a, b) == True{} : Bool}) -> {ult(b, a) == False{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(b, a), cm.flip(U32.cmp(a, b)), u.flip(a, b)) : {Cmp.is_lt(_) == False{} : Bool}
  cm.not_lt_flip(U32.cmp(a, b), e)

def u.lt_le_absurd(+a: U32, +b: U32, +e: {ult(a, b) == True{} : Bool}, +f: {ule(b, a) == True{} : Bool}) -> Empty:
  bo.not_true(ule(b, a), f, u.lt_not_le(a, b, e))

def u.le_lt.go(c1: Cmp, +a: U32, +b: U32, +c: U32, +e1: {U32.cmp(a, b) == c1 : Cmp}, +h1: {Cmp.is_le(c1) == True{} : Bool}, +h2: {U32.cmp(b, c) == LT{} : Cmp}) -> {U32.cmp(a, c) == LT{} : Cmp}:
  match c1:
    case LT{}:
      u.cmp_lt_trans(a, b, c, e1, h2)
    case EQ{}:
      %Equal.sym(U32, a, b, u.eq(a, b, e1)) : {U32.cmp(_, c) == LT{} : Cmp}
      h2
    case GT{}:
      Empty.absurd({U32.cmp(a, c) == LT{} : Cmp}, ab.ft(h1))

# a <= b < c
def u.le_lt(+a: U32, +b: U32, +c: U32, +h1: {ule(a, b) == True{} : Bool}, +h2: {ult(b, c) == True{} : Bool}) -> {ult(a, c) == True{} : Bool}:
  cm.is_lt_of(U32.cmp(a, c), u.le_lt.go(U32.cmp(a, b), a, b, c, {==}, h1, cm.lt_of(U32.cmp(b, c), h2)))

def u.lt_le.go(c2: Cmp, +a: U32, +b: U32, +c: U32, +e2: {U32.cmp(b, c) == c2 : Cmp}, +h1: {U32.cmp(a, b) == LT{} : Cmp}, +h2: {Cmp.is_le(c2) == True{} : Bool}) -> {U32.cmp(a, c) == LT{} : Cmp}:
  match c2:
    case LT{}:
      u.cmp_lt_trans(a, b, c, h1, e2)
    case EQ{}:
      %u.eq(b, c, e2) : {U32.cmp(a, _) == LT{} : Cmp}
      h1
    case GT{}:
      Empty.absurd({U32.cmp(a, c) == LT{} : Cmp}, ab.ft(h2))

# a < b <= c
def u.lt_le(+a: U32, +b: U32, +c: U32, +h1: {ult(a, b) == True{} : Bool}, +h2: {ule(b, c) == True{} : Bool}) -> {ult(a, c) == True{} : Bool}:
  cm.is_lt_of(U32.cmp(a, c), u.lt_le.go(U32.cmp(b, c), a, b, c, {==}, cm.lt_of(U32.cmp(a, b), h1), h2))

def u.le_le.go(c1: Cmp, +a: U32, +b: U32, +c: U32, +e1: {U32.cmp(a, b) == c1 : Cmp}, +h1: {Cmp.is_le(c1) == True{} : Bool}, +h2: {ule(b, c) == True{} : Bool}) -> {ule(a, c) == True{} : Bool}:
  match c1:
    case LT{}:
      u.le_of_lt(a, c, u.lt_le(a, b, c, cm.is_lt_of(U32.cmp(a, b), e1), h2))
    case EQ{}:
      %Equal.sym(U32, a, b, u.eq(a, b, e1)) : {Cmp.is_le(U32.cmp(_, c)) == True{} : Bool}
      h2
    case GT{}:
      Empty.absurd({ule(a, c) == True{} : Bool}, ab.ft(h1))

# a <= b <= c
def u.le_trans(+a: U32, +b: U32, +c: U32, +h1: {ule(a, b) == True{} : Bool}, +h2: {ule(b, c) == True{} : Bool}) -> {ule(a, c) == True{} : Bool}:
  u.le_le.go(U32.cmp(a, b), a, b, c, {==}, h1, h2)

# a <= b and b <= a: a == b
def u.antisym(+a: U32, +b: U32, +h1: {ule(a, b) == True{} : Bool}, +h2: {ule(b, a) == True{} : Bool}) -> {a == b : U32}:
  u.eq(a, b, cm.eq_of_le(U32.cmp(a, b), h1, u.le_not_lt(b, a, h2)))


# Below: the timer order's lemmas (this package's own). Above: Base's
# Bool, Cmp, Word and U32 order lemmas, copied from bend-osdev-maple's
# proof_order.bend (they mention no package).

# Bool, more

def bo.or_swap(a: Bool, b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(b, Bool.or(a, c)) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def bo.or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def bo.or_false_pair(a: Bool, -b: Bool, +e: {Bool.or(a, b) == False{} : Bool}) -> {(a, b) == (False{}, False{}) : Bool & Bool}:
  match a:
    case True{}:
      Empty.absurd({(True{}, b) == (False{}, False{}) : Bool & Bool}, ab.tf(e))
    case False{}:
      %Equal.sym(Bool, b, False{}, e) : {(False{}, _) == (False{}, False{}) : Bool & Bool}
      {==}

# Nat's order

def n.refl(a: Nat) -> {Nat.cmp(a, a) == EQ{} : Cmp}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      n.refl(p)

def n.eq(a: Nat, b: Nat, +e: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, ab.lt_eq(e))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, ab.gt_eq(e))
    case 1n+ +ap 1n+bp:
      %n.eq(ap, bp, e) : {1n+ap == 1n+_ : Nat}
      {==}

def n.flip(a: Nat, b: Nat) -> {Nat.cmp(b, a) == cm.flip(Nat.cmp(a, b)) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      n.flip(ap, bp)

def n.lt_trans(a: Nat, b: Nat, c: Nat, +h1: {Nat.cmp(a, b) == LT{} : Cmp}, +h2: {Nat.cmp(b, c) == LT{} : Cmp}) -> {Nat.cmp(a, c) == LT{} : Cmp}:
  match a b c:
    case 0n 0n c:
      Empty.absurd({Nat.cmp(0n, c) == LT{} : Cmp}, ab.eq_lt(h1))
    case 1n+ap 0n c:
      Empty.absurd({Nat.cmp(1n+ap, c) == LT{} : Cmp}, ab.gt_lt(h1))
    case 0n 1n+bp 0n:
      Empty.absurd({Nat.cmp(0n, 0n) == LT{} : Cmp}, ab.gt_lt(h2))
    case 0n 1n+bp 1n+cp:
      {==}
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.cmp(1n+ap, 0n) == LT{} : Cmp}, ab.gt_lt(h2))
    case 1n+ap 1n+bp 1n+cp:
      n.lt_trans(ap, bp, cp, h1, h2)

def n.tr1(+a: Nat, +b: Nat, -c: Nat, +e: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {Nat.cmp(a, c) == Nat.cmp(b, c) : Cmp}:
  %Equal.sym(Nat, a, b, n.eq(a, b, e)) : {Nat.cmp(_, c) == Nat.cmp(b, c) : Cmp}
  {==}

def n.tr2(-a: Nat, +b: Nat, +c: Nat, +e: {Nat.cmp(b, c) == EQ{} : Cmp}) -> {Nat.cmp(a, c) == Nat.cmp(a, b) : Cmp}:
  %n.eq(b, c, e) : {Nat.cmp(a, _) == Nat.cmp(a, b) : Cmp}
  {==}

def n.lt_succ(a: Nat, b: Nat, +e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 1n) == True{} : Bool}, ab.ft(e))
    case 1n+ap 0n:
      Empty.absurd({Nat.is_lt(1n+ap, 1n) == True{} : Bool}, ab.ft(e))
    case 0n 1n+bp:
      {==}
    case 1n+ap 1n+bp:
      n.lt_succ(ap, bp, e)

def n.lt_self_succ(a: Nat) -> {Nat.is_lt(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      n.lt_self_succ(p)

# U32's order, as the three facts of a transitive comparison

def u.tr1(+a: U32, +b: U32, -c: U32, +e: {U32.cmp(a, b) == EQ{} : Cmp}) -> {U32.cmp(a, c) == U32.cmp(b, c) : Cmp}:
  %Equal.sym(U32, a, b, u.eq(a, b, e)) : {U32.cmp(_, c) == U32.cmp(b, c) : Cmp}
  {==}

def u.tr2(-a: U32, +b: U32, +c: U32, +e: {U32.cmp(b, c) == EQ{} : Cmp}) -> {U32.cmp(a, c) == U32.cmp(a, b) : Cmp}:
  %u.eq(b, c, e) : {U32.cmp(a, _) == U32.cmp(a, b) : Cmp}
  {==}

# Lexicographic comparisons: the three facts carry over

def lex.tr1(x1: Cmp, -y1: Cmp, -z1: Cmp, -x2: Cmp, -y2: Cmp, -z2: Cmp, a1: {x1 == EQ{} : Cmp} -> {z1 == y1 : Cmp}, a2: {x2 == EQ{} : Cmp} -> {z2 == y2 : Cmp}, +e: {T.TqCmp.lex(x1, x2) == EQ{} : Cmp}) -> {T.TqCmp.lex(z1, z2) == T.TqCmp.lex(y1, y2) : Cmp}:
  match x1:
    case LT{}:
      Empty.absurd({T.TqCmp.lex(z1, z2) == T.TqCmp.lex(y1, y2) : Cmp}, ab.lt_eq(e))
    case EQ{}:
      %Equal.sym(Cmp, z1, y1, a1({==})) : {T.TqCmp.lex(_, z2) == T.TqCmp.lex(y1, y2) : Cmp}
      %Equal.sym(Cmp, z2, y2, a2(e)) : {T.TqCmp.lex(y1, _) == T.TqCmp.lex(y1, y2) : Cmp}
      {==}
    case GT{}:
      Empty.absurd({T.TqCmp.lex(z1, z2) == T.TqCmp.lex(y1, y2) : Cmp}, ab.gt_eq(e))

def lex.tr2(-x1: Cmp, y1: Cmp, -z1: Cmp, -x2: Cmp, -y2: Cmp, -z2: Cmp, b1: {y1 == EQ{} : Cmp} -> {z1 == x1 : Cmp}, b2: {y2 == EQ{} : Cmp} -> {z2 == x2 : Cmp}, +e: {T.TqCmp.lex(y1, y2) == EQ{} : Cmp}) -> {T.TqCmp.lex(z1, z2) == T.TqCmp.lex(x1, x2) : Cmp}:
  match y1:
    case LT{}:
      Empty.absurd({T.TqCmp.lex(z1, z2) == T.TqCmp.lex(x1, x2) : Cmp}, ab.lt_eq(e))
    case EQ{}:
      %Equal.sym(Cmp, z1, x1, b1({==})) : {T.TqCmp.lex(_, z2) == T.TqCmp.lex(x1, x2) : Cmp}
      %Equal.sym(Cmp, z2, x2, b2(e)) : {T.TqCmp.lex(x1, _) == T.TqCmp.lex(x1, x2) : Cmp}
      {==}
    case GT{}:
      Empty.absurd({T.TqCmp.lex(z1, z2) == T.TqCmp.lex(x1, x2) : Cmp}, ab.gt_eq(e))

def lex.tr3(x1: Cmp, y1: Cmp, -z1: Cmp, -x2: Cmp, -y2: Cmp, -z2: Cmp, a1: {x1 == EQ{} : Cmp} -> {z1 == y1 : Cmp}, b1: {y1 == EQ{} : Cmp} -> {z1 == x1 : Cmp}, c1: {x1 == LT{} : Cmp} -> {y1 == LT{} : Cmp} -> {z1 == LT{} : Cmp}, c2: {x2 == LT{} : Cmp} -> {y2 == LT{} : Cmp} -> {z2 == LT{} : Cmp}, +ex: {T.TqCmp.lex(x1, x2) == LT{} : Cmp}, +ey: {T.TqCmp.lex(y1, y2) == LT{} : Cmp}) -> {T.TqCmp.lex(z1, z2) == LT{} : Cmp}:
  match x1 y1:
    case LT{} LT{}:
      %Equal.sym(Cmp, z1, LT{}, c1({==}, {==})) : {T.TqCmp.lex(_, z2) == LT{} : Cmp}
      {==}
    case LT{} EQ{}:
      %Equal.sym(Cmp, z1, LT{}, b1({==})) : {T.TqCmp.lex(_, z2) == LT{} : Cmp}
      {==}
    case EQ{} LT{}:
      %Equal.sym(Cmp, z1, LT{}, a1({==})) : {T.TqCmp.lex(_, z2) == LT{} : Cmp}
      {==}
    case EQ{} EQ{}:
      %Equal.sym(Cmp, z1, EQ{}, a1({==})) : {T.TqCmp.lex(_, z2) == LT{} : Cmp}
      c2(ex, ey)
    case GT{} y1:
      Empty.absurd({T.TqCmp.lex(z1, z2) == LT{} : Cmp}, ab.gt_lt(ex))
    case x1 GT{}:
      Empty.absurd({T.TqCmp.lex(z1, z2) == LT{} : Cmp}, ab.gt_lt(ey))

def lex.flip(c1: Cmp, -c2: Cmp) -> {T.TqCmp.lex(cm.flip(c1), cm.flip(c2)) == cm.flip(T.TqCmp.lex(c1, c2)) : Cmp}:
  match c1:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def lex.eq_l(c1: Cmp, -c2: Cmp, +e: {T.TqCmp.lex(c1, c2) == EQ{} : Cmp}) -> {c1 == EQ{} : Cmp}:
  match c1:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, ab.lt_eq(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, ab.gt_eq(e))

def lex.eq_r(c1: Cmp, -c2: Cmp, +e: {T.TqCmp.lex(c1, c2) == EQ{} : Cmp}) -> {c2 == EQ{} : Cmp}:
  match c1:
    case LT{}:
      Empty.absurd({c2 == EQ{} : Cmp}, ab.lt_eq(e))
    case EQ{}:
      e
    case GT{}:
      Empty.absurd({c2 == EQ{} : Cmp}, ab.gt_eq(e))

def lex.le_l(c1: Cmp, -c2: Cmp, +e: {Cmp.is_le(T.TqCmp.lex(c1, c2)) == True{} : Bool}) -> {Cmp.is_le(c1) == True{} : Bool}:
  match c1:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({Cmp.is_le(GT{}) == True{} : Bool}, ab.ft(e))

def lex.ne_lt(c: Cmp) -> {Cmp.is_eq(T.TqCmp.lex(c, LT{})) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def lex.ne_gt(c: Cmp) -> {Cmp.is_eq(T.TqCmp.lex(c, GT{})) == False{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# From the three facts to at-most and less-than

def tr.le(X: Cmp, Y: Cmp, -Z: Cmp, t1: {X == EQ{} : Cmp} -> {Z == Y : Cmp}, t2: {Y == EQ{} : Cmp} -> {Z == X : Cmp}, t3: {X == LT{} : Cmp} -> {Y == LT{} : Cmp} -> {Z == LT{} : Cmp}, +hx: {Cmp.is_le(X) == True{} : Bool}, +hy: {Cmp.is_le(Y) == True{} : Bool}) -> {Cmp.is_le(Z) == True{} : Bool}:
  match X Y:
    case LT{} LT{}:
      %Equal.sym(Cmp, Z, LT{}, t3({==}, {==})) : {Cmp.is_le(_) == True{} : Bool}
      {==}
    case LT{} EQ{}:
      %Equal.sym(Cmp, Z, LT{}, t2({==})) : {Cmp.is_le(_) == True{} : Bool}
      {==}
    case EQ{} LT{}:
      %Equal.sym(Cmp, Z, LT{}, t1({==})) : {Cmp.is_le(_) == True{} : Bool}
      {==}
    case EQ{} EQ{}:
      %Equal.sym(Cmp, Z, EQ{}, t1({==})) : {Cmp.is_le(_) == True{} : Bool}
      {==}
    case GT{} Y:
      Empty.absurd({Cmp.is_le(Z) == True{} : Bool}, ab.ft(hx))
    case X GT{}:
      Empty.absurd({Cmp.is_le(Z) == True{} : Bool}, ab.ft(hy))

def tr.lt_le(X: Cmp, Y: Cmp, -Z: Cmp, t1: {X == EQ{} : Cmp} -> {Z == Y : Cmp}, t2: {Y == EQ{} : Cmp} -> {Z == X : Cmp}, t3: {X == LT{} : Cmp} -> {Y == LT{} : Cmp} -> {Z == LT{} : Cmp}, +hx: {Cmp.is_lt(X) == True{} : Bool}, +hy: {Cmp.is_le(Y) == True{} : Bool}) -> {Cmp.is_lt(Z) == True{} : Bool}:
  match X Y:
    case LT{} LT{}:
      %Equal.sym(Cmp, Z, LT{}, t3({==}, {==})) : {Cmp.is_lt(_) == True{} : Bool}
      {==}
    case LT{} EQ{}:
      %Equal.sym(Cmp, Z, LT{}, t2({==})) : {Cmp.is_lt(_) == True{} : Bool}
      {==}
    case LT{} GT{}:
      Empty.absurd({Cmp.is_lt(Z) == True{} : Bool}, ab.ft(hy))
    case EQ{} Y:
      Empty.absurd({Cmp.is_lt(Z) == True{} : Bool}, ab.ft(hx))
    case GT{} Y:
      Empty.absurd({Cmp.is_lt(Z) == True{} : Bool}, ab.ft(hx))

# Times: TqTime.cmp, high halves then low halves

def tm.tr1(+a: W.W64, +b: W.W64, +c: W.W64, +e: {T.TqTime.cmp(a, b) == EQ{} : Cmp}) -> {T.TqTime.cmp(a, c) == T.TqTime.cmp(b, c) : Cmp}:
  lex.tr1(U32.cmp(W.W64.hi(a), W.W64.hi(b)), U32.cmp(W.W64.hi(b), W.W64.hi(c)), U32.cmp(W.W64.hi(a), W.W64.hi(c)), U32.cmp(W.W64.lo(a), W.W64.lo(b)), U32.cmp(W.W64.lo(b), W.W64.lo(c)), U32.cmp(W.W64.lo(a), W.W64.lo(c)), f => u.tr1(W.W64.hi(a), W.W64.hi(b), W.W64.hi(c), f), f => u.tr1(W.W64.lo(a), W.W64.lo(b), W.W64.lo(c), f), e)

def tm.tr2(+a: W.W64, +b: W.W64, +c: W.W64, +e: {T.TqTime.cmp(b, c) == EQ{} : Cmp}) -> {T.TqTime.cmp(a, c) == T.TqTime.cmp(a, b) : Cmp}:
  lex.tr2(U32.cmp(W.W64.hi(a), W.W64.hi(b)), U32.cmp(W.W64.hi(b), W.W64.hi(c)), U32.cmp(W.W64.hi(a), W.W64.hi(c)), U32.cmp(W.W64.lo(a), W.W64.lo(b)), U32.cmp(W.W64.lo(b), W.W64.lo(c)), U32.cmp(W.W64.lo(a), W.W64.lo(c)), f => u.tr2(W.W64.hi(a), W.W64.hi(b), W.W64.hi(c), f), f => u.tr2(W.W64.lo(a), W.W64.lo(b), W.W64.lo(c), f), e)

def tm.tr3(+a: W.W64, +b: W.W64, +c: W.W64, +h1: {T.TqTime.cmp(a, b) == LT{} : Cmp}, +h2: {T.TqTime.cmp(b, c) == LT{} : Cmp}) -> {T.TqTime.cmp(a, c) == LT{} : Cmp}:
  lex.tr3(U32.cmp(W.W64.hi(a), W.W64.hi(b)), U32.cmp(W.W64.hi(b), W.W64.hi(c)), U32.cmp(W.W64.hi(a), W.W64.hi(c)), U32.cmp(W.W64.lo(a), W.W64.lo(b)), U32.cmp(W.W64.lo(b), W.W64.lo(c)), U32.cmp(W.W64.lo(a), W.W64.lo(c)), f => u.tr1(W.W64.hi(a), W.W64.hi(b), W.W64.hi(c), f), f => u.tr2(W.W64.hi(a), W.W64.hi(b), W.W64.hi(c), f), f => g => u.cmp_lt_trans(W.W64.hi(a), W.W64.hi(b), W.W64.hi(c), f, g), f => g => u.cmp_lt_trans(W.W64.lo(a), W.W64.lo(b), W.W64.lo(c), f, g), h1, h2)

def tm.flip(+a: W.W64, +b: W.W64) -> {T.TqTime.cmp(b, a) == cm.flip(T.TqTime.cmp(a, b)) : Cmp}:
  %Equal.sym(Cmp, U32.cmp(W.W64.hi(b), W.W64.hi(a)), cm.flip(U32.cmp(W.W64.hi(a), W.W64.hi(b))), u.flip(W.W64.hi(a), W.W64.hi(b))) : {T.TqCmp.lex(_, U32.cmp(W.W64.lo(b), W.W64.lo(a))) == cm.flip(T.TqTime.cmp(a, b)) : Cmp}
  %Equal.sym(Cmp, U32.cmp(W.W64.lo(b), W.W64.lo(a)), cm.flip(U32.cmp(W.W64.lo(a), W.W64.lo(b))), u.flip(W.W64.lo(a), W.W64.lo(b))) : {T.TqCmp.lex(cm.flip(U32.cmp(W.W64.hi(a), W.W64.hi(b))), _) == cm.flip(T.TqTime.cmp(a, b)) : Cmp}
  lex.flip(U32.cmp(W.W64.hi(a), W.W64.hi(b)), U32.cmp(W.W64.lo(a), W.W64.lo(b)))

def tm.refl(+a: W.W64) -> {T.TqTime.cmp(a, a) == EQ{} : Cmp}:
  %Equal.sym(Cmp, U32.cmp(W.W64.hi(a), W.W64.hi(a)), EQ{}, u.refl(W.W64.hi(a))) : {T.TqCmp.lex(_, U32.cmp(W.W64.lo(a), W.W64.lo(a))) == EQ{} : Cmp}
  %Equal.sym(Cmp, U32.cmp(W.W64.lo(a), W.W64.lo(a)), EQ{}, u.refl(W.W64.lo(a))) : {T.TqCmp.lex(EQ{}, _) == EQ{} : Cmp}
  {==}

def tm.eq(+a: W.W64, +b: W.W64, +e: {T.TqTime.cmp(a, b) == EQ{} : Cmp}) -> {a == b : W.W64}:
  %WL.parts_of(a) : {_ == b : W.W64}
  %WL.parts_of(b) : {W.W64.from_parts(W.W64.hi(a), W.W64.lo(a)) == _ : W.W64}
  %Equal.sym(U32, W.W64.hi(a), W.W64.hi(b), u.eq(W.W64.hi(a), W.W64.hi(b), lex.eq_l(U32.cmp(W.W64.hi(a), W.W64.hi(b)), U32.cmp(W.W64.lo(a), W.W64.lo(b)), e))) : {W.W64.from_parts(_, W.W64.lo(a)) == W.W64.from_parts(W.W64.hi(b), W.W64.lo(b)) : W.W64}
  %Equal.sym(U32, W.W64.lo(a), W.W64.lo(b), u.eq(W.W64.lo(a), W.W64.lo(b), lex.eq_r(U32.cmp(W.W64.hi(a), W.W64.hi(b)), U32.cmp(W.W64.lo(a), W.W64.lo(b)), e))) : {W.W64.from_parts(W.W64.hi(b), _) == W.W64.from_parts(W.W64.hi(b), W.W64.lo(b)) : W.W64}
  {==}

def tm.le_refl(+a: W.W64) -> {T.TqTime.le(a, a) == True{} : Bool}:
  %Equal.sym(Cmp, T.TqTime.cmp(a, a), EQ{}, tm.refl(a)) : {Cmp.is_le(_) == True{} : Bool}
  {==}

def tm.not_le(+a: W.W64, +b: W.W64, +e: {T.TqTime.le(a, b) == False{} : Bool}) -> {T.TqTime.lt(b, a) == True{} : Bool}:
  %Equal.sym(Cmp, T.TqTime.cmp(b, a), cm.flip(T.TqTime.cmp(a, b)), tm.flip(a, b)) : {Cmp.is_lt(_) == True{} : Bool}
  cm.lt_flip(T.TqTime.cmp(a, b), e)

def tm.lt_le(+a: W.W64, +b: W.W64, +c: W.W64, +h1: {T.TqTime.lt(a, b) == True{} : Bool}, +h2: {T.TqTime.le(b, c) == True{} : Bool}) -> {T.TqTime.lt(a, c) == True{} : Bool}:
  tr.lt_le(T.TqTime.cmp(a, b), T.TqTime.cmp(b, c), T.TqTime.cmp(a, c), f => tm.tr1(a, b, c, f), f => tm.tr2(a, b, c, f), f => g => tm.tr3(a, b, c, f, g), h1, h2)

# Timers: TqTimer.cmp, expiry then id

def kt.tr1(+ea: W.W64, +ia: Nat, +eb: W.W64, +ib: Nat, +ec: W.W64, +ic: Nat, +e: {T.TqTimer.cmp(T.TqTimer{ea, ia}, T.TqTimer{eb, ib}) == EQ{} : Cmp}) -> {T.TqTimer.cmp(T.TqTimer{ea, ia}, T.TqTimer{ec, ic}) == T.TqTimer.cmp(T.TqTimer{eb, ib}, T.TqTimer{ec, ic}) : Cmp}:
  lex.tr1(T.TqTime.cmp(ea, eb), T.TqTime.cmp(eb, ec), T.TqTime.cmp(ea, ec), Nat.cmp(ia, ib), Nat.cmp(ib, ic), Nat.cmp(ia, ic), f => tm.tr1(ea, eb, ec, f), f => n.tr1(ia, ib, ic, f), e)

def kt.tr2(+ea: W.W64, +ia: Nat, +eb: W.W64, +ib: Nat, +ec: W.W64, +ic: Nat, +e: {T.TqTimer.cmp(T.TqTimer{eb, ib}, T.TqTimer{ec, ic}) == EQ{} : Cmp}) -> {T.TqTimer.cmp(T.TqTimer{ea, ia}, T.TqTimer{ec, ic}) == T.TqTimer.cmp(T.TqTimer{ea, ia}, T.TqTimer{eb, ib}) : Cmp}:
  lex.tr2(T.TqTime.cmp(ea, eb), T.TqTime.cmp(eb, ec), T.TqTime.cmp(ea, ec), Nat.cmp(ia, ib), Nat.cmp(ib, ic), Nat.cmp(ia, ic), f => tm.tr2(ea, eb, ec, f), f => n.tr2(ia, ib, ic, f), e)

def kt.tr3(+ea: W.W64, +ia: Nat, +eb: W.W64, +ib: Nat, +ec: W.W64, +ic: Nat, +h1: {T.TqTimer.cmp(T.TqTimer{ea, ia}, T.TqTimer{eb, ib}) == LT{} : Cmp}, +h2: {T.TqTimer.cmp(T.TqTimer{eb, ib}, T.TqTimer{ec, ic}) == LT{} : Cmp}) -> {T.TqTimer.cmp(T.TqTimer{ea, ia}, T.TqTimer{ec, ic}) == LT{} : Cmp}:
  lex.tr3(T.TqTime.cmp(ea, eb), T.TqTime.cmp(eb, ec), T.TqTime.cmp(ea, ec), Nat.cmp(ia, ib), Nat.cmp(ib, ic), Nat.cmp(ia, ic), f => tm.tr1(ea, eb, ec, f), f => tm.tr2(ea, eb, ec, f), f => g => tm.tr3(ea, eb, ec, f, g), f => g => n.lt_trans(ia, ib, ic, f, g), h1, h2)

def kt.le_trans(x: T.TqTimer, y: T.TqTimer, z: T.TqTimer, +h1: {T.TqTimer.le(x, y) == True{} : Bool}, +h2: {T.TqTimer.le(y, z) == True{} : Bool}) -> {T.TqTimer.le(x, z) == True{} : Bool}:
  match x y z:
    case T.TqTimer{+ea, +ia} T.TqTimer{+eb, +ib} T.TqTimer{+ec, +ic}:
      tr.le(T.TqTimer.cmp(T.TqTimer{ea, ia}, T.TqTimer{eb, ib}), T.TqTimer.cmp(T.TqTimer{eb, ib}, T.TqTimer{ec, ic}), T.TqTimer.cmp(T.TqTimer{ea, ia}, T.TqTimer{ec, ic}), f => kt.tr1(ea, ia, eb, ib, ec, ic, f), f => kt.tr2(ea, ia, eb, ib, ec, ic, f), f => g => kt.tr3(ea, ia, eb, ib, ec, ic, f, g), h1, h2)

def kt.lt_le(+x: T.TqTimer, +y: T.TqTimer, +e: {T.TqTimer.lt(x, y) == True{} : Bool}) -> {T.TqTimer.le(x, y) == True{} : Bool}:
  cm.le_of_lt(T.TqTimer.cmp(x, y), e)

def kt.not_lt(x: T.TqTimer, y: T.TqTimer, +e: {T.TqTimer.lt(x, y) == False{} : Bool}) -> {T.TqTimer.le(y, x) == True{} : Bool}:
  match x y:
    case T.TqTimer{+ea, +ia} T.TqTimer{+eb, +ib}:
      %Equal.sym(Cmp, T.TqTime.cmp(eb, ea), cm.flip(T.TqTime.cmp(ea, eb)), tm.flip(ea, eb)) : {Cmp.is_le(T.TqCmp.lex(_, Nat.cmp(ib, ia))) == True{} : Bool}
      %Equal.sym(Cmp, Nat.cmp(ib, ia), cm.flip(Nat.cmp(ia, ib)), n.flip(ia, ib)) : {Cmp.is_le(T.TqCmp.lex(cm.flip(T.TqTime.cmp(ea, eb)), _)) == True{} : Bool}
      %Equal.sym(Cmp, T.TqCmp.lex(cm.flip(T.TqTime.cmp(ea, eb)), cm.flip(Nat.cmp(ia, ib))), cm.flip(T.TqCmp.lex(T.TqTime.cmp(ea, eb), Nat.cmp(ia, ib))), lex.flip(T.TqTime.cmp(ea, eb), Nat.cmp(ia, ib))) : {Cmp.is_le(_) == True{} : Bool}
      cm.le_flip(T.TqCmp.lex(T.TqTime.cmp(ea, eb), Nat.cmp(ia, ib)), e)

def kt.le_time(x: T.TqTimer, y: T.TqTimer, +e: {T.TqTimer.le(x, y) == True{} : Bool}) -> {T.TqTime.le(T.TqTimer.expiry(x), T.TqTimer.expiry(y)) == True{} : Bool}:
  match x y:
    case T.TqTimer{+ea, +ia} T.TqTimer{+eb, +ib}:
      lex.le_l(T.TqTime.cmp(ea, eb), Nat.cmp(ia, ib), e)

def kt.refl(x: T.TqTimer) -> {T.TqTimer.is_eq(x, x) == True{} : Bool}:
  match x:
    case T.TqTimer{+e, +i}:
      %Equal.sym(Cmp, T.TqTime.cmp(e, e), EQ{}, tm.refl(e)) : {Cmp.is_eq(T.TqCmp.lex(_, Nat.cmp(i, i))) == True{} : Bool}
      %Equal.sym(Cmp, Nat.cmp(i, i), EQ{}, n.refl(i)) : {Cmp.is_eq(T.TqCmp.lex(EQ{}, _)) == True{} : Bool}
      {==}

def kt.eq(x: T.TqTimer, y: T.TqTimer, +e: {T.TqTimer.is_eq(x, y) == True{} : Bool}) -> {x == y : T.TqTimer}:
  match x y:
    case T.TqTimer{+ea, +ia} T.TqTimer{+eb, +ib}:
      %tm.eq(ea, eb, lex.eq_l(T.TqTime.cmp(ea, eb), Nat.cmp(ia, ib), cm.eq_of(T.TqTimer.cmp(T.TqTimer{ea, ia}, T.TqTimer{eb, ib}), e))) : {T.TqTimer{ea, ia} == T.TqTimer{_, ib} : T.TqTimer}
      %n.eq(ia, ib, lex.eq_r(T.TqTime.cmp(ea, eb), Nat.cmp(ia, ib), cm.eq_of(T.TqTimer.cmp(T.TqTimer{ea, ia}, T.TqTimer{eb, ib}), e))) : {T.TqTimer{ea, ia} == T.TqTimer{ea, _} : T.TqTimer}
      {==}

# a timer with a smaller id than another is not that timer, either way round
def kt.fresh(+e1: W.W64, +i: Nat, +e2: W.W64, +n: Nat, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {T.TqTimer.is_eq(T.TqTimer{e1, i}, T.TqTimer{e2, n}) == False{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(i, n), LT{}, cm.lt_of(Nat.cmp(i, n), h)) : {Cmp.is_eq(T.TqCmp.lex(T.TqTime.cmp(e1, e2), _)) == False{} : Bool}
  lex.ne_lt(T.TqTime.cmp(e1, e2))

def kt.fresh2(+e2: W.W64, +n: Nat, +e1: W.W64, +i: Nat, +h: {Nat.is_lt(i, n) == True{} : Bool}) -> {T.TqTimer.is_eq(T.TqTimer{e2, n}, T.TqTimer{e1, i}) == False{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(n, i), cm.flip(Nat.cmp(i, n)), n.flip(i, n)) : {Cmp.is_eq(T.TqCmp.lex(T.TqTime.cmp(e2, e1), _)) == False{} : Bool}
  %Equal.sym(Cmp, Nat.cmp(i, n), LT{}, cm.lt_of(Nat.cmp(i, n), h)) : {Cmp.is_eq(T.TqCmp.lex(T.TqTime.cmp(e2, e1), cm.flip(_))) == False{} : Bool}
  lex.ne_gt(T.TqTime.cmp(e2, e1))
