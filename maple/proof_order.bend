# Proof helpers for bend-osdev-maple: Bool, Cmp and U32's order, U32's
# successor and predecessor, and the monotonicity of U32 addition (through
# the value of a word as a Nat). Nothing here mentions the package.
import Base

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

# Successor: Word.inc, and U32.inc on it

def wd.fin_xf_lt(c: Cmp, x: Bool, +e: {Word.cmp.fin(x, False{}, c) == LT{} : Cmp}) -> {c == LT{} : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match x:
        case False{}:
          Empty.absurd({EQ{} == LT{} : Cmp}, ab.eq_lt(e))
        case True{}:
          Empty.absurd({EQ{} == LT{} : Cmp}, ab.gt_lt(e))
    case GT{}:
      Empty.absurd({GT{} == LT{} : Cmp}, ab.gt_lt(e))

def wd.fin_ty_lt(c: Cmp, y: Bool, +e: {Word.cmp.fin(True{}, y, c) == LT{} : Cmp}) -> {c == LT{} : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match y:
        case False{}:
          Empty.absurd({EQ{} == LT{} : Cmp}, ab.gt_lt(e))
        case True{}:
          Empty.absurd({EQ{} == LT{} : Cmp}, ab.eq_lt(e))
    case GT{}:
      Empty.absurd({GT{} == LT{} : Cmp}, ab.gt_lt(e))

def wd.le_fin_t(c: Cmp, x: Bool, +e: {Cmp.is_le(c) == True{} : Bool}) -> {Cmp.is_le(Word.cmp.fin(x, True{}, c)) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match x:
        case False{}:
          {==}
        case True{}:
          {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, ab.ft(e))

def wd.le_fin_f(c: Cmp, y: Bool, +e: {Cmp.is_le(c) == True{} : Bool}) -> {Cmp.is_le(Word.cmp.fin(False{}, y, c)) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match y:
        case False{}:
          {==}
        case True{}:
          {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, ab.ft(e))

def wd.w1.step(c: Cmp, x: Bool, +e: {Word.cmp.fin(x, True{}, c) == LT{} : Cmp}) -> {Cmp.is_le(Word.cmp.fin(x, False{}, c)) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match x:
        case False{}:
          {==}
        case True{}:
          Empty.absurd({False{} == True{} : Bool}, ab.eq_lt(e))
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, ab.gt_lt(e))

def wd.w3.step(c: Cmp, y: Bool, +e: {Word.cmp.fin(False{}, y, c) == LT{} : Cmp}) -> {Cmp.is_le(Word.cmp.fin(True{}, y, c)) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      match y:
        case False{}:
          Empty.absurd({False{} == True{} : Bool}, ab.eq_lt(e))
        case True{}:
          {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, ab.gt_lt(e))

# i < inc(p): i <= p
def wd.inc_lt_le(n: Nat, i: Word(n), p: Word(n), +e: {Word.cmp(n, i, Word.inc(n, p)) == LT{} : Cmp}) -> {Cmp.is_le(Word.cmp(n, i, p)) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({True{} == True{} : Bool}, ab.eq_lt(e))
    case 1n+ +q:
      match i p:
        case WCon{+ib, +it} WCon{pb, +pt}:
          match pb:
            case False{}:
              wd.w1.step(Word.cmp(q, it, pt), ib, e)
            case True{}:
              wd.le_fin_t(Word.cmp(q, it, pt), ib, wd.inc_lt_le(q, it, pt, wd.fin_xf_lt(Word.cmp(q, it, Word.inc(q, pt)), ib, e)))

# s < inc(p): p < inc(p), so inc did not wrap
def wd.inc_gt2(n: Nat, s: Word(n), p: Word(n), +e: {Word.cmp(n, s, Word.inc(n, p)) == LT{} : Cmp}) -> {Word.cmp(n, p, Word.inc(n, p)) == LT{} : Cmp}:
  match n:
    case 0n:
      Empty.absurd({EQ{} == LT{} : Cmp}, ab.eq_lt(e))
    case 1n+ +q:
      match s p:
        case WCon{+sb, +st} WCon{pb, +pt}:
          match pb:
            case False{}:
              %Equal.sym(Cmp, Word.cmp(q, pt, pt), EQ{}, wd.refl(q, pt)) : {Word.cmp.fin(False{}, True{}, _) == LT{} : Cmp}
              {==}
            case True{}:
              %Equal.sym(Cmp, Word.cmp(q, pt, Word.inc(q, pt)), LT{}, wd.inc_gt2(q, st, pt, wd.fin_xf_lt(Word.cmp(q, st, Word.inc(q, pt)), sb, e))) : {Word.cmp.fin(True{}, False{}, _) == LT{} : Cmp}
              {==}

# p < r: p < inc(p)
def wd.inc_gt(n: Nat, r: Word(n), p: Word(n), +e: {Word.cmp(n, p, r) == LT{} : Cmp}) -> {Word.cmp(n, p, Word.inc(n, p)) == LT{} : Cmp}:
  match n:
    case 0n:
      Empty.absurd({EQ{} == LT{} : Cmp}, ab.eq_lt(e))
    case 1n+ +q:
      match r p:
        case WCon{+rb, +rt} WCon{pb, +pt}:
          match pb:
            case False{}:
              %Equal.sym(Cmp, Word.cmp(q, pt, pt), EQ{}, wd.refl(q, pt)) : {Word.cmp.fin(False{}, True{}, _) == LT{} : Cmp}
              {==}
            case True{}:
              %Equal.sym(Cmp, Word.cmp(q, pt, Word.inc(q, pt)), LT{}, wd.inc_gt(q, rt, pt, wd.fin_ty_lt(Word.cmp(q, pt, rt), rb, e))) : {Word.cmp.fin(True{}, False{}, _) == LT{} : Cmp}
              {==}

# p < r: inc(p) <= r
def wd.inc_le(n: Nat, r: Word(n), p: Word(n), +e: {Word.cmp(n, p, r) == LT{} : Cmp}) -> {Cmp.is_le(Word.cmp(n, Word.inc(n, p), r)) == True{} : Bool}:
  match n:
    case 0n:
      Empty.absurd({True{} == True{} : Bool}, ab.eq_lt(e))
    case 1n+ +q:
      match r p:
        case WCon{+rb, +rt} WCon{pb, +pt}:
          match pb:
            case False{}:
              wd.w3.step(Word.cmp(q, pt, rt), rb, e)
            case True{}:
              wd.le_fin_f(Word.cmp(q, Word.inc(q, pt), rt), rb, wd.inc_le(q, rt, pt, wd.fin_ty_lt(Word.cmp(q, pt, rt), rb, e)))

# Predecessor: U32.sub(a, 1) is the predecessor of a, as inc undoes it

def wd.adc_z_tt(n: Nat, a: Word(n)) -> {Word.adc(n, a, Word.zero(n), True{}, True{}) == a : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+ +q:
      match a:
        case WCon{x, +t}:
          match x:
            case False{}:
              %wd.adc_z_tt(q, t) : {WCon{False{}, Word.adc(q, t, Word.zero(q), True{}, True{})} == WCon{False{}, _} : Word(1n+q)}
              {==}
            case True{}:
              %wd.adc_z_tt(q, t) : {WCon{True{}, Word.adc(q, t, Word.zero(q), True{}, True{})} == WCon{True{}, _} : Word(1n+q)}
              {==}

def wd.inc_adc_z_tf(n: Nat, a: Word(n)) -> {Word.inc(n, Word.adc(n, a, Word.zero(n), True{}, False{})) == a : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+ +q:
      match a:
        case WCon{x, +t}:
          match x:
            case False{}:
              %wd.inc_adc_z_tf(q, t) : {WCon{False{}, Word.inc(q, Word.adc(q, t, Word.zero(q), True{}, False{}))} == WCon{False{}, _} : Word(1n+q)}
              {==}
            case True{}:
              %wd.adc_z_tt(q, t) : {WCon{True{}, Word.adc(q, t, Word.zero(q), True{}, True{})} == WCon{True{}, _} : Word(1n+q)}
              {==}

def u.inc_dec(a: U32) -> {U32.inc(U32.sub(a, 1)) == a : U32}:
  match a:
    case U32{w}:
      match w:
        case WCon{x, +t}:
          match x:
            case False{}:
              %wd.inc_adc_z_tf(31n, t) : {U32{WCon{False{}, Word.inc(31n, Word.adc(31n, t, Word.zero(31n), True{}, False{}))}} == U32{WCon{False{}, _}} : U32}
              {==}
            case True{}:
              %wd.adc_z_tt(31n, t) : {U32{WCon{True{}, Word.adc(31n, t, Word.zero(31n), True{}, True{})}} == U32{WCon{True{}, _}} : U32}
              {==}

# The successor and predecessor, as Bools on U32

def u.inc_lt_le(+i: U32, +p: U32, +e: {ult(i, U32.inc(p)) == True{} : Bool}) -> {ule(i, p) == True{} : Bool}:
  match i p:
    case U32{+x} U32{+y}:
      wd.inc_lt_le(32n, x, y, cm.lt_of(Word.cmp(32n, x, Word.inc(32n, y)), e))

def u.inc_gt2(+s: U32, +p: U32, +e: {ult(s, U32.inc(p)) == True{} : Bool}) -> {ult(p, U32.inc(p)) == True{} : Bool}:
  match s p:
    case U32{+x} U32{+y}:
      cm.is_lt_of(Word.cmp(32n, y, Word.inc(32n, y)), wd.inc_gt2(32n, x, y, cm.lt_of(Word.cmp(32n, x, Word.inc(32n, y)), e)))

def u.inc_gt(+p: U32, +r: U32, +e: {ult(p, r) == True{} : Bool}) -> {ult(p, U32.inc(p)) == True{} : Bool}:
  match p r:
    case U32{+x} U32{+y}:
      cm.is_lt_of(Word.cmp(32n, x, Word.inc(32n, x)), wd.inc_gt(32n, y, x, cm.lt_of(Word.cmp(32n, x, y), e)))

def u.inc_le(+p: U32, +r: U32, +e: {ult(p, r) == True{} : Bool}) -> {ule(U32.inc(p), r) == True{} : Bool}:
  match p r:
    case U32{+x} U32{+y}:
      wd.inc_le(32n, y, x, cm.lt_of(Word.cmp(32n, x, y), e))

# Predecessor facts, as Bools: dec(a) = U32.sub(a, 1)

def u.lt_incdec(+s: U32, +a: U32, +e: {ult(s, a) == True{} : Bool}) -> {ult(s, U32.inc(U32.sub(a, 1))) == True{} : Bool}:
  %Equal.sym(U32, U32.inc(U32.sub(a, 1)), a, u.inc_dec(a)) : {ult(s, _) == True{} : Bool}
  e

# s < a: s <= dec(a)
def u.dec_le(+s: U32, +a: U32, +e: {ult(s, a) == True{} : Bool}) -> {ule(s, U32.sub(a, 1)) == True{} : Bool}:
  u.inc_lt_le(s, U32.sub(a, 1), u.lt_incdec(s, a, e))

# s < a: dec(a) < a
def u.dec_lt(+s: U32, +a: U32, +e: {ult(s, a) == True{} : Bool}) -> {ult(U32.sub(a, 1), a) == True{} : Bool}:
  %u.inc_dec(a) : {ult(U32.sub(a, 1), _) == True{} : Bool}
  u.inc_gt2(s, U32.sub(a, 1), u.lt_incdec(s, a, e))

# i <= dec(a) and s < a: i < a
def u.le_dec_lt(+i: U32, +s: U32, +a: U32, +f: {ule(i, U32.sub(a, 1)) == True{} : Bool}, +e: {ult(s, a) == True{} : Bool}) -> {ult(i, a) == True{} : Bool}:
  u.le_lt(i, U32.sub(a, 1), a, f, u.dec_lt(s, a, e))

# Successor facts, as Bools, for b < l (so inc(b) does not wrap)

# inc(b) <= i and b < l: b < i
def u.inc_le_lt(+b: U32, +i: U32, +l: U32, +f: {ule(U32.inc(b), i) == True{} : Bool}, +e: {ult(b, l) == True{} : Bool}) -> {ult(b, i) == True{} : Bool}:
  u.lt_le(b, U32.inc(b), i, u.inc_gt(b, l, e), f)

# s <= b and b < l: s < inc(b)
def u.le_lt_inc(+s: U32, +b: U32, +l: U32, +f: {ule(s, b) == True{} : Bool}, +e: {ult(b, l) == True{} : Bool}) -> {ult(s, U32.inc(b)) == True{} : Bool}:
  u.le_lt(s, b, U32.inc(b), f, u.inc_gt(b, l, e))

# Nat

def nt.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %nt.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def nt.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %nt.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def nt.add_one(+a: Nat) -> {Nat.add(a, 1n) == 1n+a : Nat}:
  %nt.add_zero(a) : {Nat.add(a, 1n) == 1n+_ : Nat}
  nt.add_succ(a, 0n)

def nt.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, nt.add_zero(b))
    case 1n+ +p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), nt.add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %nt.add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def nt.add_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %nt.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def nt.refl(a: Nat) -> {Nat.cmp(a, a) == EQ{} : Cmp}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      nt.refl(p)

def nt.flip(a: Nat, b: Nat) -> {Nat.cmp(b, a) == cm.flip(Nat.cmp(a, b)) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      nt.flip(p, q)

def nt.cmp_add_l(k: Nat, +a: Nat, +b: Nat) -> {Nat.cmp(Nat.add(k, a), Nat.add(k, b)) == Nat.cmp(a, b) : Cmp}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      nt.cmp_add_l(p, a, b)

def nt.cmp_add_r(+a: Nat, +b: Nat, +k: Nat) -> {Nat.cmp(Nat.add(a, k), Nat.add(b, k)) == Nat.cmp(a, b) : Cmp}:
  %nt.add_comm(k, a) : {Nat.cmp(_, Nat.add(b, k)) == Nat.cmp(a, b) : Cmp}
  %nt.add_comm(k, b) : {Nat.cmp(Nat.add(k, a), _) == Nat.cmp(a, b) : Cmp}
  nt.cmp_add_l(k, a, b)

def nt.le_add(a: Nat, d: Nat) -> {Cmp.is_le(Nat.cmp(a, Nat.add(a, d))) == True{} : Bool}:
  match a:
    case 0n:
      match d:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      nt.le_add(p, d)

def nt.not_lt_zero(a: Nat, +e: {Nat.cmp(a, 0n) == LT{} : Cmp}) -> Empty:
  match a:
    case 0n:
      ab.eq_lt(e)
    case 1n+p:
      ab.gt_lt(e)

# a <= b < c: a < c
def nt.le_lt(a: Nat, b: Nat, c: Nat, +h1: {Cmp.is_le(Nat.cmp(a, b)) == True{} : Bool}, +h2: {Nat.cmp(b, c) == LT{} : Cmp}) -> {Nat.cmp(a, c) == LT{} : Cmp}:
  match a b c:
    case 0n b 0n:
      Empty.absurd({EQ{} == LT{} : Cmp}, nt.not_lt_zero(b, h2))
    case 0n b 1n+r:
      {==}
    case 1n+p 0n c:
      Empty.absurd({Nat.cmp(1n+p, c) == LT{} : Cmp}, ab.ft(h1))
    case 1n+p 1n+q 0n:
      Empty.absurd({GT{} == LT{} : Cmp}, ab.gt_lt(h2))
    case 1n+p 1n+q 1n+r:
      nt.le_lt(p, q, r, h1, h2)

def nt.double_add(x: Nat, +y: Nat) -> {Nat.double(Nat.add(x, y)) == Nat.add(Nat.double(x), Nat.double(y)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %nt.double_add(p, y) : {2n+Nat.double(Nat.add(p, y)) == 2n+_ : Nat}
      {==}

# The value of a word

def bitN(b: Bool) -> Nat:
  match b:
    case False{}:
      0n
    case True{}:
      1n

def wN(n: Nat, w: Word(n)) -> Nat:
  Word.to_nat(n, w)

def nt.cmp_bd(a: Nat, b: Nat, i: Bool, j: Bool) -> {Nat.cmp(Nat.add(bitN(i), Nat.double(a)), Nat.add(bitN(j), Nat.double(b))) == Word.cmp.fin(i, j, Nat.cmp(a, b)) : Cmp}:
  match a b:
    case 0n 0n:
      match i j:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 0n 1n+q:
      match i j:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+p 0n:
      match i j:
        case False{} False{}:
          {==}
        case False{} True{}:
          {==}
        case True{} False{}:
          {==}
        case True{} True{}:
          {==}
    case 1n+p 1n+q:
      match i j:
        case False{} False{}:
          nt.cmp_bd(p, q, False{}, False{})
        case False{} True{}:
          nt.cmp_bd(p, q, False{}, True{})
        case True{} False{}:
          nt.cmp_bd(p, q, True{}, False{})
        case True{} True{}:
          nt.cmp_bd(p, q, True{}, True{})

def nt.to_nat_con(-q: Nat, x: Bool, -t: Word(q)) -> {Word.to_nat(1n+q, WCon{x, t}) == Nat.add(bitN(x), Nat.double(Word.to_nat(q, t))) : Nat}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

# Word's order is the order of the values
def nt.word_cmp(n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +q:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          %Equal.sym(Nat, Word.to_nat(1n+q, WCon{x, at}), Nat.add(bitN(x), Nat.double(Word.to_nat(q, at))), nt.to_nat_con(q, x, at)) : {Word.cmp.fin(x, y, Word.cmp(q, at, bt)) == Nat.cmp(_, Word.to_nat(1n+q, WCon{y, bt})) : Cmp}
          %Equal.sym(Nat, Word.to_nat(1n+q, WCon{y, bt}), Nat.add(bitN(y), Nat.double(Word.to_nat(q, bt))), nt.to_nat_con(q, y, bt)) : {Word.cmp.fin(x, y, Word.cmp(q, at, bt)) == Nat.cmp(Nat.add(bitN(x), Nat.double(Word.to_nat(q, at))), _) : Cmp}
          %Equal.sym(Cmp, Word.cmp(q, at, bt), Nat.cmp(Word.to_nat(q, at), Word.to_nat(q, bt)), nt.word_cmp(q, at, bt)) : {Word.cmp.fin(x, y, _) == Nat.cmp(Nat.add(bitN(x), Nat.double(Word.to_nat(q, at))), Nat.add(bitN(y), Nat.double(Word.to_nat(q, bt)))) : Cmp}
          Equal.sym(Cmp, Nat.cmp(Nat.add(bitN(x), Nat.double(Word.to_nat(q, at))), Nat.add(bitN(y), Nat.double(Word.to_nat(q, bt)))), Word.cmp.fin(x, y, Nat.cmp(Word.to_nat(q, at), Word.to_nat(q, bt))), nt.cmp_bd(Word.to_nat(q, at), Word.to_nat(q, bt), x, y))

def p2(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+m:
      Nat.double(p2(m))

# a word is below 2^n
def nt.word_lt(n: Nat, w: Word(n)) -> {Nat.cmp(Word.to_nat(n, w), p2(n)) == LT{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+ +q:
      match w:
        case WCon{+x, +t}:
          %Equal.sym(Nat, Word.to_nat(1n+q, WCon{x, t}), Nat.add(bitN(x), Nat.double(Word.to_nat(q, t))), nt.to_nat_con(q, x, t)) : {Nat.cmp(_, Nat.double(p2(q))) == LT{} : Cmp}
          %Equal.sym(Cmp, Nat.cmp(Nat.add(bitN(x), Nat.double(Word.to_nat(q, t))), Nat.add(bitN(False{}), Nat.double(p2(q)))), Word.cmp.fin(x, False{}, Nat.cmp(Word.to_nat(q, t), p2(q))), nt.cmp_bd(Word.to_nat(q, t), p2(q), x, False{})) : {_ == LT{} : Cmp}
          %Equal.sym(Cmp, Nat.cmp(Word.to_nat(q, t), p2(q)), LT{}, nt.word_lt(q, t)) : {Word.cmp.fin(x, False{}, _) == LT{} : Cmp}
          {==}

# The value of a sum: adc with carry in c gives a + b + c, less 2^n if it
# carries out

def kbit(x: Bool, +y: Bool, +c: Bool) -> Bool:
  match x:
    case False{}:
      Bool.and(y, c)
    case True{}:
      Bool.or(y, c)

def sbit(x: Bool, +y: Bool, +c: Bool) -> Bool:
  match x:
    case False{}:
      Bool.xor(y, c)
    case True{}:
      Bool.not(Bool.xor(y, c))

def wco(n: Nat, a: Word(n), b: Word(n), c: Bool) -> Bool:
  match n:
    case 0n:
      c
    case 1n+q:
      match a b:
        case WCon{x, at} WCon{y, bt}:
          wco(q, at, bt, kbit(x, y, c))

def copP(k: Bool, +p: Nat) -> Nat:
  match k:
    case False{}:
      0n
    case True{}:
      p

def nt.cop_succ(k: Bool, +q: Nat) -> {copP(k, p2(1n+q)) == Nat.double(copP(k, p2(q))) : Nat}:
  match k:
    case False{}:
      {==}
    case True{}:
      {==}

# the algebra of one bit: s + 2 (A + B + k) = (x + 2 A) + (y + 2 B) + c

def nt.lhs(s: Bool, k: Bool, +a: Nat, +b: Nat) -> {Nat.add(bitN(s), Nat.double(Nat.add(Nat.add(a, b), bitN(k)))) == Nat.add(Nat.add(bitN(s), Nat.double(bitN(k))), Nat.add(Nat.double(a), Nat.double(b))) : Nat}:
  match s:
    case False{}:
      match k:
        case False{}:
          %Equal.sym(Nat, Nat.add(Nat.add(a, b), 0n), Nat.add(a, b), nt.add_zero(Nat.add(a, b))) : {Nat.double(_) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}
          nt.double_add(a, b)
        case True{}:
          %Equal.sym(Nat, Nat.add(Nat.add(a, b), 1n), 1n+Nat.add(a, b), nt.add_one(Nat.add(a, b))) : {Nat.double(_) == 2n+Nat.add(Nat.double(a), Nat.double(b)) : Nat}
          %nt.double_add(a, b) : {2n+Nat.double(Nat.add(a, b)) == 2n+_ : Nat}
          {==}
    case True{}:
      match k:
        case False{}:
          %Equal.sym(Nat, Nat.add(Nat.add(a, b), 0n), Nat.add(a, b), nt.add_zero(Nat.add(a, b))) : {1n+Nat.double(_) == 1n+Nat.add(Nat.double(a), Nat.double(b)) : Nat}
          %nt.double_add(a, b) : {1n+Nat.double(Nat.add(a, b)) == 1n+_ : Nat}
          {==}
        case True{}:
          %Equal.sym(Nat, Nat.add(Nat.add(a, b), 1n), 1n+Nat.add(a, b), nt.add_one(Nat.add(a, b))) : {1n+Nat.double(_) == 3n+Nat.add(Nat.double(a), Nat.double(b)) : Nat}
          %nt.double_add(a, b) : {3n+Nat.double(Nat.add(a, b)) == 3n+_ : Nat}
          {==}

def nt.rhs_y(y: Bool, +da: Nat, +db: Nat) -> {Nat.add(da, Nat.add(bitN(y), db)) == Nat.add(bitN(y), Nat.add(da, db)) : Nat}:
  match y:
    case False{}:
      {==}
    case True{}:
      nt.add_succ(da, db)

def nt.rhs_c(c: Bool, +z: Nat) -> {Nat.add(z, bitN(c)) == Nat.add(bitN(c), z) : Nat}:
  match c:
    case False{}:
      nt.add_zero(z)
    case True{}:
      nt.add_one(z)

def nt.rhs.f(y: Bool, c: Bool, +w: Nat) -> {Nat.add(bitN(c), Nat.add(bitN(y), w)) == Nat.add(Nat.add(Nat.add(bitN(False{}), bitN(y)), bitN(c)), w) : Nat}:
  match y c:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def nt.rhs.t(y: Bool, c: Bool, +w: Nat) -> {Nat.add(bitN(c), 1n+Nat.add(bitN(y), w)) == Nat.add(Nat.add(Nat.add(bitN(True{}), bitN(y)), bitN(c)), w) : Nat}:
  match y c:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def nt.rhs.x(x: Bool, +y: Bool, +c: Bool, +da: Nat, +db: Nat) -> {Nat.add(bitN(c), Nat.add(Nat.add(bitN(x), da), Nat.add(bitN(y), db))) == Nat.add(Nat.add(Nat.add(bitN(x), bitN(y)), bitN(c)), Nat.add(da, db)) : Nat}:
  match x:
    case False{}:
      %Equal.sym(Nat, Nat.add(da, Nat.add(bitN(y), db)), Nat.add(bitN(y), Nat.add(da, db)), nt.rhs_y(y, da, db)) : {Nat.add(bitN(c), _) == Nat.add(Nat.add(Nat.add(bitN(False{}), bitN(y)), bitN(c)), Nat.add(da, db)) : Nat}
      nt.rhs.f(y, c, Nat.add(da, db))
    case True{}:
      %Equal.sym(Nat, Nat.add(da, Nat.add(bitN(y), db)), Nat.add(bitN(y), Nat.add(da, db)), nt.rhs_y(y, da, db)) : {Nat.add(bitN(c), 1n+_) == Nat.add(Nat.add(Nat.add(bitN(True{}), bitN(y)), bitN(c)), Nat.add(da, db)) : Nat}
      nt.rhs.t(y, c, Nat.add(da, db))

def nt.rhs(+x: Bool, +y: Bool, +c: Bool, +da: Nat, +db: Nat) -> {Nat.add(Nat.add(Nat.add(bitN(x), da), Nat.add(bitN(y), db)), bitN(c)) == Nat.add(Nat.add(Nat.add(bitN(x), bitN(y)), bitN(c)), Nat.add(da, db)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.add(bitN(x), da), Nat.add(bitN(y), db)), bitN(c)), Nat.add(bitN(c), Nat.add(Nat.add(bitN(x), da), Nat.add(bitN(y), db))), nt.rhs_c(c, Nat.add(Nat.add(bitN(x), da), Nat.add(bitN(y), db)))) : {_ == Nat.add(Nat.add(Nat.add(bitN(x), bitN(y)), bitN(c)), Nat.add(da, db)) : Nat}
  nt.rhs.x(x, y, c, da, db)

def nt.bits(x: Bool, y: Bool, c: Bool) -> {Nat.add(bitN(sbit(x, y, c)), Nat.double(bitN(kbit(x, y, c)))) == Nat.add(Nat.add(bitN(x), bitN(y)), bitN(c)) : Nat}:
  match x y c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} True{} True{}:
      {==}

def nt.alg(+x: Bool, +y: Bool, +c: Bool, +a: Nat, +b: Nat) -> {Nat.add(bitN(sbit(x, y, c)), Nat.double(Nat.add(Nat.add(a, b), bitN(kbit(x, y, c))))) == Nat.add(Nat.add(Nat.add(bitN(x), Nat.double(a)), Nat.add(bitN(y), Nat.double(b))), bitN(c)) : Nat}:
  %Equal.sym(Nat, Nat.add(bitN(sbit(x, y, c)), Nat.double(Nat.add(Nat.add(a, b), bitN(kbit(x, y, c))))), Nat.add(Nat.add(bitN(sbit(x, y, c)), Nat.double(bitN(kbit(x, y, c)))), Nat.add(Nat.double(a), Nat.double(b))), nt.lhs(sbit(x, y, c), kbit(x, y, c), a, b)) : {_ == Nat.add(Nat.add(Nat.add(bitN(x), Nat.double(a)), Nat.add(bitN(y), Nat.double(b))), bitN(c)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.add(bitN(x), Nat.double(a)), Nat.add(bitN(y), Nat.double(b))), bitN(c)), Nat.add(Nat.add(Nat.add(bitN(x), bitN(y)), bitN(c)), Nat.add(Nat.double(a), Nat.double(b))), nt.rhs(x, y, c, Nat.double(a), Nat.double(b))) : {Nat.add(Nat.add(bitN(sbit(x, y, c)), Nat.double(bitN(kbit(x, y, c)))), Nat.add(Nat.double(a), Nat.double(b))) == _ : Nat}
  %Equal.sym(Nat, Nat.add(bitN(sbit(x, y, c)), Nat.double(bitN(kbit(x, y, c)))), Nat.add(Nat.add(bitN(x), bitN(y)), bitN(c)), nt.bits(x, y, c)) : {Nat.add(_, Nat.add(Nat.double(a), Nat.double(b))) == Nat.add(Nat.add(Nat.add(bitN(x), bitN(y)), bitN(c)), Nat.add(Nat.double(a), Nat.double(b))) : Nat}
  {==}

# one step of adc: the sum bit and the carry are sbit and kbit
def nt.adc_con(-q: Nat, x: Bool, +y: Bool, +c: Bool, -at: Word(q), -bt: Word(q)) -> {Word.adc(1n+q, WCon{x, at}, WCon{y, bt}, False{}, c) == WCon{sbit(x, y, c), Word.adc(q, at, bt, False{}, kbit(x, y, c))} : Word(1n+q)}:
  match x:
    case False{}:
      {==}
    case True{}:
      {==}

def nt.adc(n: Nat, a: Word(n), b: Word(n), +c: Bool) -> {Nat.add(Word.to_nat(n, Word.adc(n, a, b, False{}, c)), copP(wco(n, a, b, c), p2(n))) == Nat.add(Nat.add(Word.to_nat(n, a), Word.to_nat(n, b)), bitN(c)) : Nat}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          match c:
            case False{}:
              {==}
            case True{}:
              {==}
    case 1n+ +q:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          %Equal.sym(Word(1n+q), Word.adc(1n+q, WCon{x, at}, WCon{y, bt}, False{}, c), WCon{sbit(x, y, c), Word.adc(q, at, bt, False{}, kbit(x, y, c))}, nt.adc_con(q, x, y, c, at, bt)) : {Nat.add(Word.to_nat(1n+q, _), copP(wco(q, at, bt, kbit(x, y, c)), p2(1n+q))) == Nat.add(Nat.add(Word.to_nat(1n+q, WCon{x, at}), Word.to_nat(1n+q, WCon{y, bt})), bitN(c)) : Nat}
          %Equal.sym(Nat, Word.to_nat(1n+q, WCon{sbit(x, y, c), Word.adc(q, at, bt, False{}, kbit(x, y, c))}), Nat.add(bitN(sbit(x, y, c)), Nat.double(Word.to_nat(q, Word.adc(q, at, bt, False{}, kbit(x, y, c))))), nt.to_nat_con(q, sbit(x, y, c), Word.adc(q, at, bt, False{}, kbit(x, y, c)))) : {Nat.add(_, copP(wco(q, at, bt, kbit(x, y, c)), p2(1n+q))) == Nat.add(Nat.add(Word.to_nat(1n+q, WCon{x, at}), Word.to_nat(1n+q, WCon{y, bt})), bitN(c)) : Nat}
          %Equal.sym(Nat, copP(wco(q, at, bt, kbit(x, y, c)), p2(1n+q)), Nat.double(copP(wco(q, at, bt, kbit(x, y, c)), p2(q))), nt.cop_succ(wco(q, at, bt, kbit(x, y, c)), q)) : {Nat.add(Nat.add(bitN(sbit(x, y, c)), Nat.double(Word.to_nat(q, Word.adc(q, at, bt, False{}, kbit(x, y, c))))), _) == Nat.add(Nat.add(Word.to_nat(1n+q, WCon{x, at}), Word.to_nat(1n+q, WCon{y, bt})), bitN(c)) : Nat}
          %Equal.sym(Nat, Nat.add(Nat.add(bitN(sbit(x, y, c)), Nat.double(Word.to_nat(q, Word.adc(q, at, bt, False{}, kbit(x, y, c))))), Nat.double(copP(wco(q, at, bt, kbit(x, y, c)), p2(q)))), Nat.add(bitN(sbit(x, y, c)), Nat.add(Nat.double(Word.to_nat(q, Word.adc(q, at, bt, False{}, kbit(x, y, c)))), Nat.double(copP(wco(q, at, bt, kbit(x, y, c)), p2(q))))), nt.add_assoc(bitN(sbit(x, y, c)), Nat.double(Word.to_nat(q, Word.adc(q, at, bt, False{}, kbit(x, y, c)))), Nat.double(copP(wco(q, at, bt, kbit(x, y, c)), p2(q))))) : {_ == Nat.add(Nat.add(Word.to_nat(1n+q, WCon{x, at}), Word.to_nat(1n+q, WCon{y, bt})), bitN(c)) : Nat}
          %nt.double_add(Word.to_nat(q, Word.adc(q, at, bt, False{}, kbit(x, y, c))), copP(wco(q, at, bt, kbit(x, y, c)), p2(q))) : {Nat.add(bitN(sbit(x, y, c)), _) == Nat.add(Nat.add(Word.to_nat(1n+q, WCon{x, at}), Word.to_nat(1n+q, WCon{y, bt})), bitN(c)) : Nat}
          %Equal.sym(Nat, Nat.add(Word.to_nat(q, Word.adc(q, at, bt, False{}, kbit(x, y, c))), copP(wco(q, at, bt, kbit(x, y, c)), p2(q))), Nat.add(Nat.add(Word.to_nat(q, at), Word.to_nat(q, bt)), bitN(kbit(x, y, c))), nt.adc(q, at, bt, kbit(x, y, c))) : {Nat.add(bitN(sbit(x, y, c)), Nat.double(_)) == Nat.add(Nat.add(Word.to_nat(1n+q, WCon{x, at}), Word.to_nat(1n+q, WCon{y, bt})), bitN(c)) : Nat}
          %Equal.sym(Nat, Word.to_nat(1n+q, WCon{x, at}), Nat.add(bitN(x), Nat.double(Word.to_nat(q, at))), nt.to_nat_con(q, x, at)) : {Nat.add(bitN(sbit(x, y, c)), Nat.double(Nat.add(Nat.add(Word.to_nat(q, at), Word.to_nat(q, bt)), bitN(kbit(x, y, c))))) == Nat.add(Nat.add(_, Word.to_nat(1n+q, WCon{y, bt})), bitN(c)) : Nat}
          %Equal.sym(Nat, Word.to_nat(1n+q, WCon{y, bt}), Nat.add(bitN(y), Nat.double(Word.to_nat(q, bt))), nt.to_nat_con(q, y, bt)) : {Nat.add(bitN(sbit(x, y, c)), Nat.double(Nat.add(Nat.add(Word.to_nat(q, at), Word.to_nat(q, bt)), bitN(kbit(x, y, c))))) == Nat.add(Nat.add(Nat.add(bitN(x), Nat.double(Word.to_nat(q, at))), _), bitN(c)) : Nat}
          nt.alg(x, y, c, Word.to_nat(q, at), Word.to_nat(q, bt))

# Adding d is monotone when it does not wrap. In Nat, with P = 2^32:
# a sum that carries out is the true sum less P.

def cm.flip_lt(-c: Cmp, +e: {c == LT{} : Cmp}) -> {cm.flip(c) == GT{} : Cmp}:
  %Equal.sym(Cmp, c, LT{}, e) : {cm.flip(_) == GT{} : Cmp}
  {==}

def ab.le_gt(c: Cmp, +h: {c == GT{} : Cmp}, +e: {Cmp.is_le(c) == True{} : Bool}) -> Empty:
  match c:
    case LT{}:
      ab.lt_gt(h)
    case EQ{}:
      ab.eq_gt(h)
    case GT{}:
      ab.ft(e)

# y <= s and s < y cannot both hold
def nt.le_gt_absurd(+y: Nat, +s: Nat, +h: {Cmp.is_le(Nat.cmp(y, s)) == True{} : Bool}, +lt: {Nat.cmp(s, y) == LT{} : Cmp}) -> Empty:
  ab.le_gt(Nat.cmp(y, s), Equal.trans(Cmp, Nat.cmp(y, s), cm.flip(Nat.cmp(s, y)), GT{}, nt.flip(s, y), cm.flip_lt(Nat.cmp(s, y), lt)), h)

def nt.carry_y.r(+sy: Nat, +y: Nat, +d: Nat, +p: Nat, +hy: {Nat.add(sy, p) == Nat.add(Nat.add(y, d), 0n) : Nat}) -> {Nat.cmp(Nat.add(sy, p), Nat.add(y, p)) == Nat.cmp(Nat.add(y, d), Nat.add(y, p)) : Cmp}:
  %Equal.sym(Nat, Nat.add(sy, p), Nat.add(Nat.add(y, d), 0n), hy) : {Nat.cmp(_, Nat.add(y, p)) == Nat.cmp(Nat.add(y, d), Nat.add(y, p)) : Cmp}
  %nt.add_zero(Nat.add(y, d)) : {Nat.cmp(Nat.add(Nat.add(y, d), 0n), Nat.add(y, p)) == Nat.cmp(_, Nat.add(y, p)) : Cmp}
  {==}

def nt.carry_y(+y: Nat, +d: Nat, +sy: Nat, cy: Bool, +p: Nat, +hy: {Nat.add(sy, copP(cy, p)) == Nat.add(Nat.add(y, d), 0n) : Nat}, +hd: {Nat.cmp(d, p) == LT{} : Cmp}, +h2: {Cmp.is_le(Nat.cmp(y, sy)) == True{} : Bool}) -> {sy == Nat.add(y, d) : Nat}:
  match cy:
    case False{}:
      Equal.trans(Nat, sy, Nat.add(sy, 0n), Nat.add(y, d), Equal.sym(Nat, Nat.add(sy, 0n), sy, nt.add_zero(sy)), Equal.trans(Nat, Nat.add(sy, 0n), Nat.add(Nat.add(y, d), 0n), Nat.add(y, d), hy, nt.add_zero(Nat.add(y, d))))
    case True{}:
      +lt = Equal.trans(Cmp, Nat.cmp(sy, y), Nat.cmp(Nat.add(sy, p), Nat.add(y, p)), LT{}, Equal.sym(Cmp, Nat.cmp(Nat.add(sy, p), Nat.add(y, p)), Nat.cmp(sy, y), nt.cmp_add_r(sy, y, p)), Equal.trans(Cmp, Nat.cmp(Nat.add(sy, p), Nat.add(y, p)), Nat.cmp(Nat.add(y, d), Nat.add(y, p)), LT{}, nt.carry_y.r(sy, y, d, p, hy), Equal.trans(Cmp, Nat.cmp(Nat.add(y, d), Nat.add(y, p)), Nat.cmp(d, p), LT{}, nt.cmp_add_l(y, d, p), hd)))
      Empty.absurd({sy == Nat.add(y, d) : Nat}, nt.le_gt_absurd(y, sy, h2, lt))

def nt.carry_x.le(+x: Nat, +y: Nat, +d: Nat, +h1: {Cmp.is_le(Nat.cmp(x, y)) == True{} : Bool}) -> {Cmp.is_le(Nat.cmp(Nat.add(x, d), Nat.add(y, d))) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(Nat.add(x, d), Nat.add(y, d)), Nat.cmp(x, y), nt.cmp_add_r(x, y, d)) : {Cmp.is_le(_) == True{} : Bool}
  h1

def nt.carry_x.lt(+y: Nat, +d: Nat, +sy: Nat, +p: Nat, +hsy: {Nat.cmp(sy, p) == LT{} : Cmp}, +ey: {sy == Nat.add(y, d) : Nat}) -> {Nat.cmp(Nat.add(y, d), p) == LT{} : Cmp}:
  %ey : {Nat.cmp(_, p) == LT{} : Cmp}
  hsy

def nt.carry_x.top(+sx: Nat, +x: Nat, +d: Nat, +p: Nat, +hx: {Nat.add(sx, p) == Nat.add(Nat.add(x, d), 0n) : Nat}, +lt: {Nat.cmp(Nat.add(x, d), p) == LT{} : Cmp}) -> {Nat.cmp(Nat.add(sx, p), p) == LT{} : Cmp}:
  %Equal.sym(Nat, Nat.add(sx, p), Nat.add(Nat.add(x, d), 0n), hx) : {Nat.cmp(_, p) == LT{} : Cmp}
  %Equal.sym(Nat, Nat.add(Nat.add(x, d), 0n), Nat.add(x, d), nt.add_zero(Nat.add(x, d))) : {Nat.cmp(_, p) == LT{} : Cmp}
  lt

def nt.carry_x(+x: Nat, +y: Nat, +d: Nat, +sx: Nat, +sy: Nat, cx: Bool, +p: Nat, +hx: {Nat.add(sx, copP(cx, p)) == Nat.add(Nat.add(x, d), 0n) : Nat}, +hsy: {Nat.cmp(sy, p) == LT{} : Cmp}, +h1: {Cmp.is_le(Nat.cmp(x, y)) == True{} : Bool}, +ey: {sy == Nat.add(y, d) : Nat}) -> {sx == Nat.add(x, d) : Nat}:
  match cx:
    case False{}:
      Equal.trans(Nat, sx, Nat.add(sx, 0n), Nat.add(x, d), Equal.sym(Nat, Nat.add(sx, 0n), sx, nt.add_zero(sx)), Equal.trans(Nat, Nat.add(sx, 0n), Nat.add(Nat.add(x, d), 0n), Nat.add(x, d), hx, nt.add_zero(Nat.add(x, d))))
    case True{}:
      +top = nt.carry_x.top(sx, x, d, p, hx, nt.le_lt(Nat.add(x, d), Nat.add(y, d), p, nt.carry_x.le(x, y, d, h1), nt.carry_x.lt(y, d, sy, p, hsy, ey)))
      Empty.absurd({sx == Nat.add(x, d) : Nat}, nt.not_lt_zero(sx, Equal.trans(Cmp, Nat.cmp(sx, 0n), Nat.cmp(Nat.add(sx, p), Nat.add(0n, p)), LT{}, Equal.sym(Cmp, Nat.cmp(Nat.add(sx, p), Nat.add(0n, p)), Nat.cmp(sx, 0n), nt.cmp_add_r(sx, 0n, p)), top)))

def nt.am_le1(+x: Nat, +d: Nat, +sx: Nat, +ex: {sx == Nat.add(x, d) : Nat}) -> {Cmp.is_le(Nat.cmp(x, sx)) == True{} : Bool}:
  %Equal.sym(Nat, sx, Nat.add(x, d), ex) : {Cmp.is_le(Nat.cmp(x, _)) == True{} : Bool}
  nt.le_add(x, d)

def nt.am_le2(+x: Nat, +y: Nat, +d: Nat, +sx: Nat, +sy: Nat, +ex: {sx == Nat.add(x, d) : Nat}, +ey: {sy == Nat.add(y, d) : Nat}, +h1: {Cmp.is_le(Nat.cmp(x, y)) == True{} : Bool}) -> {Cmp.is_le(Nat.cmp(sx, sy)) == True{} : Bool}:
  %Equal.sym(Nat, sx, Nat.add(x, d), ex) : {Cmp.is_le(Nat.cmp(_, sy)) == True{} : Bool}
  %Equal.sym(Nat, sy, Nat.add(y, d), ey) : {Cmp.is_le(Nat.cmp(Nat.add(x, d), _)) == True{} : Bool}
  nt.carry_x.le(x, y, d, h1)

def wd.to_nat_le(+n: Nat, +a: Word(n), +b: Word(n), +h: {Cmp.is_le(Word.cmp(n, a, b)) == True{} : Bool}) -> {Cmp.is_le(Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b))) == True{} : Bool}:
  %nt.word_cmp(n, a, b) : {Cmp.is_le(_) == True{} : Bool}
  h

def wd.of_nat_le(+n: Nat, +a: Word(n), +b: Word(n), +h: {Cmp.is_le(Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b))) == True{} : Bool}) -> {Cmp.is_le(Word.cmp(n, a, b)) == True{} : Bool}:
  %Equal.sym(Cmp, Word.cmp(n, a, b), Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)), nt.word_cmp(n, a, b)) : {Cmp.is_le(_) == True{} : Bool}
  h

def wd.am(+n: Nat, +xw: Word(n), +yw: Word(n), +dw: Word(n), +h1: {Cmp.is_le(Word.cmp(n, xw, yw)) == True{} : Bool}, +h2: {Cmp.is_le(Word.cmp(n, yw, Word.adc(n, yw, dw, False{}, False{}))) == True{} : Bool}) -> {Bool.and(Cmp.is_le(Word.cmp(n, xw, Word.adc(n, xw, dw, False{}, False{}))), Cmp.is_le(Word.cmp(n, Word.adc(n, xw, dw, False{}, False{}), Word.adc(n, yw, dw, False{}, False{})))) == True{} : Bool}:
  +ey = nt.carry_y(Word.to_nat(n, yw), Word.to_nat(n, dw), Word.to_nat(n, Word.adc(n, yw, dw, False{}, False{})), wco(n, yw, dw, False{}), p2(n), nt.adc(n, yw, dw, False{}), nt.word_lt(n, dw), wd.to_nat_le(n, yw, Word.adc(n, yw, dw, False{}, False{}), h2))
  +nh1 = wd.to_nat_le(n, xw, yw, h1)
  +ex = nt.carry_x(Word.to_nat(n, xw), Word.to_nat(n, yw), Word.to_nat(n, dw), Word.to_nat(n, Word.adc(n, xw, dw, False{}, False{})), Word.to_nat(n, Word.adc(n, yw, dw, False{}, False{})), wco(n, xw, dw, False{}), p2(n), nt.adc(n, xw, dw, False{}), nt.word_lt(n, Word.adc(n, yw, dw, False{}, False{})), nh1, ey)
  bo.and_intro(Cmp.is_le(Word.cmp(n, xw, Word.adc(n, xw, dw, False{}, False{}))), Cmp.is_le(Word.cmp(n, Word.adc(n, xw, dw, False{}, False{}), Word.adc(n, yw, dw, False{}, False{}))), wd.of_nat_le(n, xw, Word.adc(n, xw, dw, False{}, False{}), nt.am_le1(Word.to_nat(n, xw), Word.to_nat(n, dw), Word.to_nat(n, Word.adc(n, xw, dw, False{}, False{})), ex)), wd.of_nat_le(n, Word.adc(n, xw, dw, False{}, False{}), Word.adc(n, yw, dw, False{}, False{}), nt.am_le2(Word.to_nat(n, xw), Word.to_nat(n, yw), Word.to_nat(n, dw), Word.to_nat(n, Word.adc(n, xw, dw, False{}, False{})), Word.to_nat(n, Word.adc(n, yw, dw, False{}, False{})), ex, ey, nh1)))

# x <= y and y + d does not wrap: x + d does not wrap, and x + d <= y + d
def u.am(+x: U32, +y: U32, +d: U32, +h1: {ule(x, y) == True{} : Bool}, +h2: {ule(y, U32.add(y, d)) == True{} : Bool}) -> {Bool.and(ule(x, U32.add(x, d)), ule(U32.add(x, d), U32.add(y, d))) == True{} : Bool}:
  match x y d:
    case U32{+xw} U32{+yw} U32{+dw}:
      wd.am(32n, xw, yw, dw, h1, h2)

# 0 is below or equal to every index
def wd.zero_le(n: Nat, a: Word(n)) -> {Cmp.is_le(Word.cmp(n, Word.zero(n), a)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +q:
      match a:
        case WCon{+ab, +at}:
          wd.le_fin_f(Word.cmp(q, Word.zero(q), at), ab, wd.zero_le(q, at))

def u.zero_le(a: U32) -> {ule(0, a) == True{} : Bool}:
  match a:
    case U32{+w}:
      wd.zero_le(32n, w)
