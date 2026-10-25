# Proofs of LAWS_order.bend: the order of Nat by induction on Base's unary
# Nat, and that of Word(n) by induction over the bits, compared from the top
# bit down (Word.cmp.fin); U32's is Word(32)'s. The lemmas on Bool, Cmp and
# words are those bend-osdev-maple, -timerqueue and -itree proved for their
# own use (proof_order.bend), now proved here once.
import Base
import ./LAWS_order.bend as Laws

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

def cm.is_lt_of(-c: Cmp, +e: {c == LT{} : Cmp}) -> {Cmp.is_lt(c) == True{} : Bool}:
  %Equal.sym(Cmp, c, LT{}, e) : {Cmp.is_lt(_) == True{} : Bool}
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

# Nat

def nt.le_trans(x: Nat, y: Nat, z: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_le(y, z) == True{} : Bool}) -> {Nat.is_le(x, z) == True{} : Bool}:
  match x y z:
    case 0n _ _:
      match z:
        case 0n:
          {==}
        case 1n+zp:
          {==}
    case 1n+xp 0n _:
      Empty.absurd({Nat.is_le(1n+xp, z) == True{} : Bool}, ab.ft(h1))
    case 1n+xp 1n+yp 0n:
      Empty.absurd({Nat.is_le(1n+xp, 0n) == True{} : Bool}, ab.ft(h2))
    case 1n+xp 1n+yp 1n+zp:
      nt.le_trans(xp, yp, zp, h1, h2)

def nt.lt_trans(x: Nat, y: Nat, z: Nat, h1: {Nat.is_lt(x, y) == True{} : Bool}, h2: {Nat.is_lt(y, z) == True{} : Bool}) -> {Nat.is_lt(x, z) == True{} : Bool}:
  match x y z:
    case 0n 0n _:
      Empty.absurd({Nat.is_lt(0n, z) == True{} : Bool}, ab.ft(h1))
    case 0n 1n+yp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ab.ft(h2))
    case 0n 1n+yp 1n+zp:
      {==}
    case 1n+xp 0n _:
      Empty.absurd({Nat.is_lt(1n+xp, z) == True{} : Bool}, ab.ft(h1))
    case 1n+xp 1n+yp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 0n) == True{} : Bool}, ab.ft(h2))
    case 1n+xp 1n+yp 1n+zp:
      nt.lt_trans(xp, yp, zp, h1, h2)

def nt.lt_le_trans(x: Nat, y: Nat, z: Nat, h1: {Nat.is_lt(x, y) == True{} : Bool}, h2: {Nat.is_le(y, z) == True{} : Bool}) -> {Nat.is_lt(x, z) == True{} : Bool}:
  match x y z:
    case 0n 0n _:
      Empty.absurd({Nat.is_lt(0n, z) == True{} : Bool}, ab.ft(h1))
    case 0n 1n+yp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ab.ft(h2))
    case 0n 1n+yp 1n+zp:
      {==}
    case 1n+xp 0n _:
      Empty.absurd({Nat.is_lt(1n+xp, z) == True{} : Bool}, ab.ft(h1))
    case 1n+xp 1n+yp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 0n) == True{} : Bool}, ab.ft(h2))
    case 1n+xp 1n+yp 1n+zp:
      nt.lt_le_trans(xp, yp, zp, h1, h2)

def nt.le_lt_trans(x: Nat, y: Nat, z: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_lt(y, z) == True{} : Bool}) -> {Nat.is_lt(x, z) == True{} : Bool}:
  match x y z:
    case 0n 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ab.ft(h2))
    case 0n 0n 1n+zp:
      {==}
    case 0n 1n+yp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ab.ft(h2))
    case 0n 1n+yp 1n+zp:
      {==}
    case 1n+xp 0n _:
      Empty.absurd({Nat.is_lt(1n+xp, z) == True{} : Bool}, ab.ft(h1))
    case 1n+xp 1n+yp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 0n) == True{} : Bool}, ab.ft(h2))
    case 1n+xp 1n+yp 1n+zp:
      nt.le_lt_trans(xp, yp, zp, h1, h2)

def nt.le_add_r(x: Nat, +w: Nat) -> {Nat.is_le(x, Nat.add(x, w)) == True{} : Bool}:
  match x:
    case 0n:
      match w:
        case 0n:
          {==}
        case 1n+wp:
          {==}
    case 1n+xp:
      nt.le_add_r(xp, w)

# The laws

def Laws.nat_le_trans(x, y, z, h1, h2):
  nt.le_trans(x, y, z, h1, h2)

def Laws.nat_lt_trans(x, y, z, h1, h2):
  nt.lt_trans(x, y, z, h1, h2)

def Laws.nat_lt_le_trans(x, y, z, h1, h2):
  nt.lt_le_trans(x, y, z, h1, h2)

def Laws.nat_le_lt_trans(x, y, z, h1, h2):
  nt.le_lt_trans(x, y, z, h1, h2)

def Laws.nat_le_add_r(x, w):
  nt.le_add_r(x, w)

def Laws.word_cmp_refl(n, a):
  wd.refl(n, a)

def Laws.word_cmp_eq(n, a, b, e):
  wd.eq(n, a, b, e)

def Laws.word_cmp_lt_trans(n, a, b, c, h1, h2):
  wd.lt_trans(n, a, b, c, h1, h2)

def Laws.u32_cmp_refl(a):
  u.refl(a)

def Laws.u32_cmp_eq(a, b, e):
  u.eq(a, b, e)

def Laws.u32_cmp_lt_trans(a, b, c, h1, h2):
  u.cmp_lt_trans(a, b, c, h1, h2)

def Laws.u32_le_refl(a):
  u.le_refl(a)

def Laws.u32_lt_irrefl(a, e):
  u.lt_irrefl(a, e)

def Laws.u32_lt_le(a, b, e):
  u.le_of_lt(a, b, e)

def Laws.u32_lt_trans(a, b, c, h1, h2):
  u.lt_trans(a, b, c, h1, h2)

def Laws.u32_le_trans(a, b, c, h1, h2):
  u.le_trans(a, b, c, h1, h2)

def Laws.u32_lt_le_trans(a, b, c, h1, h2):
  u.lt_le(a, b, c, h1, h2)

def Laws.u32_le_lt_trans(a, b, c, h1, h2):
  u.le_lt(a, b, c, h1, h2)

def Laws.u32_le_antisym(a, b, h1, h2):
  u.antisym(a, b, h1, h2)

def Laws.u32_not_lt(a, b, e):
  u.not_lt(a, b, e)

def Laws.u32_not_le(a, b, e):
  u.not_le(a, b, e)

def Laws.u32_lt_not_le(a, b, e):
  u.lt_not_le(a, b, e)

def Laws.u32_le_not_lt(a, b, e):
  u.le_not_lt(a, b, e)
