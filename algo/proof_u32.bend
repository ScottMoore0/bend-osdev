# Proof helpers for bend-osdev-algo: the bound on a word's value (below
# 2^n, uq.pw) and the Nat facts the binary search's bounds use. The U32
# arithmetic as Nat arithmetic (subtraction, addition, increment and
# halving when nothing wraps), first proved here, is now bend-osdev-u32's
# laws (u32_sub_value, u32_add_value, u32_inc_value, u32_shr_value), which
# PROOF.bend and proof_bsearch.bend use.
import Base

# 2^n
def uq.pw(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      Nat.double(uq.pw(p))



# Contradictions

def uq.bt(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def uq.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : uq.bt(_)
  Unit{}

def uq.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : uq.bt(_)
  Unit{}

# Nat

def uq.succ_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {1n+a == 1n+b : Nat}:
  %e : {1n+a == 1n+_ : Nat}
  {==}

def uq.double_cong(-a: Nat, -b: Nat, e: {a == b : Nat}) -> {Nat.double(a) == Nat.double(b) : Nat}:
  %e : {Nat.double(a) == Nat.double(_) : Nat}
  {==}

def uq.add_zero(x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      uq.succ_cong(Nat.add(p, 0n), p, uq.add_zero(p))

def uq.add_succ(x: Nat, -y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      uq.succ_cong(Nat.add(p, 1n+y), 1n+Nat.add(p, y), uq.add_succ(p, y))

def uq.add_comm(x: Nat, +y: Nat) -> {Nat.add(x, y) == Nat.add(y, x) : Nat}:
  match x:
    case 0n:
      Equal.sym(Nat, Nat.add(y, 0n), y, uq.add_zero(y))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, y), 1n+Nat.add(y, p), Nat.add(y, 1n+p), uq.succ_cong(Nat.add(p, y), Nat.add(y, p), uq.add_comm(p, y)), Equal.sym(Nat, Nat.add(y, 1n+p), 1n+Nat.add(y, p), uq.add_succ(y, p)))

def uq.double_add(x: Nat, -y: Nat) -> {Nat.double(Nat.add(x, y)) == Nat.add(Nat.double(x), Nat.double(y)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      uq.succ_cong(1n+Nat.double(Nat.add(p, y)), 1n+Nat.add(Nat.double(p), Nat.double(y)), uq.succ_cong(Nat.double(Nat.add(p, y)), Nat.add(Nat.double(p), Nat.double(y)), uq.double_add(p, y)))

def uq.sub_add_l(y: Nat, +r: Nat) -> {Nat.sub(Nat.add(y, r), y) == r : Nat}:
  match y:
    case 0n:
      match r:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+q:
      uq.sub_add_l(q, r)

def uq.sub_add(+r: Nat, +y: Nat) -> {Nat.sub(Nat.add(r, y), y) == r : Nat}:
  %uq.add_comm(y, r) : {Nat.sub(_, y) == r : Nat}
  uq.sub_add_l(y, r)

def uq.le_succ(y: Nat, x: Nat) -> {Nat.is_le(1n+y, x) == Nat.is_lt(y, x) : Bool}:
  match y x:
    case 0n 0n:
      {==}
    case 0n 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+q 0n:
      {==}
    case 1n+q 1n+p:
      uq.le_succ(q, p)

def uq.lt_dbl(x: Nat, y: Nat) -> {Nat.is_lt(Nat.double(x), Nat.double(y)) == Nat.is_lt(x, y) : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      uq.lt_dbl(p, q)

def uq.lt_dbl1(x: Nat, y: Nat) -> {Nat.is_lt(1n+Nat.double(x), Nat.double(y)) == Nat.is_lt(x, y) : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      uq.lt_dbl1(p, q)

def uq.lt_rw(-x: Nat, -x2: Nat, -y: Nat, e: {x == x2 : Nat}, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x2, y) == True{} : Bool}:
  %e : {Nat.is_lt(_, y) == True{} : Bool}
  h

# Bounds: every word is below 2^n

def uq.val_lt(n: Nat, w: Word(n)) -> {Nat.is_lt(Word.to_nat(n, w), uq.pw(n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{False{}, +t}:
          Equal.trans(Bool, Nat.is_lt(Nat.double(Word.to_nat(p, t)), Nat.double(uq.pw(p))), Nat.is_lt(Word.to_nat(p, t), uq.pw(p)), True{}, uq.lt_dbl(Word.to_nat(p, t), uq.pw(p)), uq.val_lt(p, t))
        case WCon{True{}, +t}:
          Equal.trans(Bool, Nat.is_lt(1n+Nat.double(Word.to_nat(p, t)), Nat.double(uq.pw(p))), Nat.is_lt(Word.to_nat(p, t), uq.pw(p)), True{}, uq.lt_dbl1(Word.to_nat(p, t), uq.pw(p)), uq.val_lt(p, t))

def uq.lt_succ_r(x: Nat, y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x, 1n+y) == True{} : Bool}:
  match x y:
    case 0n _:
      {==}
    case 1n+xp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 1n) == True{} : Bool}, uq.ft(h))
    case 1n+xp 1n+yp:
      uq.lt_succ_r(xp, yp, h)

def uq.le_lt_trans(x: Nat, y: Nat, z: Nat, h1: {Nat.is_le(x, y) == True{} : Bool}, h2: {Nat.is_lt(y, z) == True{} : Bool}) -> {Nat.is_lt(x, z) == True{} : Bool}:
  match x y z:
    case 0n 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, uq.ft(h2))
    case 0n 0n 1n+zp:
      {==}
    case 0n 1n+yp 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, uq.ft(h2))
    case 0n 1n+yp 1n+zp:
      {==}
    case 1n+xp 0n _:
      Empty.absurd({Nat.is_lt(1n+xp, z) == True{} : Bool}, uq.ft(h1))
    case 1n+xp 1n+yp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 0n) == True{} : Bool}, uq.ft(h2))
    case 1n+xp 1n+yp 1n+zp:
      uq.le_lt_trans(xp, yp, zp, h1, h2)

def uq.lt_dbl_self(x: Nat, y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x, Nat.double(y)) == True{} : Bool}:
  match x y:
    case 0n 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, uq.ft(h))
    case 0n 1n+yp:
      {==}
    case 1n+xp 0n:
      Empty.absurd({Nat.is_lt(1n+xp, 0n) == True{} : Bool}, uq.ft(h))
    case 1n+ +xp 1n+ +yp:
      uq.lt_succ_r(xp, Nat.double(yp), uq.lt_dbl_self(xp, yp, h))

# x < 2^f: x2 < 2^g, for x == x2 and g == 1 + f (stated so that a fixed g,
# such as the search's 33, is never expanded)
def uq.lt_succ_pw(+f: Nat, -g: Nat, eg: {1n+f == g : Nat}, +x: Nat, -x2: Nat, e: {x == x2 : Nat}, h: {Nat.is_lt(x, uq.pw(f)) == True{} : Bool}) -> {Nat.is_lt(x2, uq.pw(g)) == True{} : Bool}:
  %eg : {Nat.is_lt(x2, uq.pw(_)) == True{} : Bool}
  %e : {Nat.is_lt(_, uq.pw(1n+f)) == True{} : Bool}
  uq.lt_dbl_self(x, uq.pw(f), h)
