import Base
import ./errseq.bend as E
import ./LAWS.bend as Laws

# Contradictions

def ab.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def ab.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : ab.bool(_)
  Unit{}

def ab.some(m: Maybe<&2, U32>) -> Type:
  match m:
    case Some{x}:
      Unit
    case None{}:
      Empty

def ab.some_none(-x: U32, e: {Some{x} == None{} : Maybe<&2, U32>}) -> Empty:
  %e : ab.some(_)
  Unit{}

# Nat

def nat.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat.eq_refl(p)

def nat.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      nat.le_refl(p)

def nat.le_succ(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+ap 0n:
      Empty.absurd({Nat.is_le(1n+ap, 1n) == True{} : Bool}, ab.ft(e))
    case 1n+ap 1n+bp:
      nat.le_succ(ap, bp, e)

# k <= n: k is not 1 + n
def nat.le_ne_succ(k: Nat, n: Nat, e: {Nat.is_le(k, n) == True{} : Bool}) -> {Nat.is_eq(k, 1n+n) == False{} : Bool}:
  match k n:
    case 0n _:
      {==}
    case 1n+kp 0n:
      Empty.absurd({Nat.is_eq(1n+kp, 1n) == False{} : Bool}, ab.ft(e))
    case 1n+kp 1n+np:
      nat.le_ne_succ(kp, np, e)

def nat.sub_zero(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nat.sub_one_le(n: Nat) -> {Nat.is_le(Nat.sub(n, 1n), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      %Equal.sym(Nat, Nat.sub(p, 0n), p, nat.sub_zero(p)) : {Nat.is_le(_, 1n+p) == True{} : Bool}
      nat.le_succ(p, p, nat.le_refl(p))

# Sampling

def sample.default(s: E.Errseq) -> {E.Errseq.sample(E.ErrseqOptions.default(), s) == E.ErrseqCursor{E.Errseq.seq(s)} : E.ErrseqCursor}:
  match s:
    case E.Errseq{n, e, f}:
      {==}

# Checks with the cursor at the count, and one behind it

def check.at(+n: Nat, -e: U32, -f: Bool) -> {E.Errseq.check(E.Errseq{n, e, f}, E.ErrseqCursor{n}) == None{} : Maybe<&2, U32>}:
  %Equal.sym(Bool, Nat.is_eq(n, n), True{}, nat.eq_refl(n)) : {E.Errseq.check.go(_, e) == None{} : Maybe<&2, U32>}
  {==}

def check.below(+k: Nat, +n: Nat, -e: U32, -f: Bool, v: {Nat.is_le(k, n) == True{} : Bool}) -> {E.Errseq.check(E.Errseq{1n+n, e, f}, E.ErrseqCursor{k}) == Some{e} : Maybe<&2, U32>}:
  %Equal.sym(Bool, Nat.is_eq(k, 1n+n), False{}, nat.le_ne_succ(k, n, v)) : {E.Errseq.check.go(_, e) == Some{e} : Maybe<&2, U32>}
  {==}

# Advancing, by the outcome of the comparison

def adv.state(b: Bool, -n: Nat, -e: U32, -f: Bool, -k: Nat) -> {E.Errseq.seq(E.ErrseqCheck.state(E.Errseq.advance.go(b, n, e, f, k))) == n : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def adv.quiet(b: Bool, +n: Nat, -e: U32, -f: Bool, +k: Nat, eb: {Nat.is_eq(k, n) == b : Bool}) -> {E.Errseq.check(E.ErrseqCheck.state(E.Errseq.advance.go(b, n, e, f, k)), E.ErrseqCheck.cursor(E.Errseq.advance.go(b, n, e, f, k))) == None{} : Maybe<&2, U32>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(k, n), True{}, eb) : {E.Errseq.check.go(_, e) == None{} : Maybe<&2, U32>}
      {==}
    case False{}:
      check.at(n, e, True{})

def adv.twice(b: Bool, +n: Nat, +e: U32, +f: Bool, +k: Nat, eb: {Nat.is_eq(k, n) == b : Bool}) -> {E.Errseq.check_and_advance(E.ErrseqCheck.state(E.Errseq.advance.go(b, n, e, f, k)), E.ErrseqCheck.cursor(E.Errseq.advance.go(b, n, e, f, k))) == E.ErrseqCheck{E.ErrseqCheck.state(E.Errseq.advance.go(b, n, e, f, k)), E.ErrseqCheck.cursor(E.Errseq.advance.go(b, n, e, f, k)), None{}} : E.ErrseqCheck}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(k, n), True{}, eb) : {E.Errseq.advance.go(_, n, e, f, k) == E.ErrseqCheck{E.Errseq{n, e, f}, E.ErrseqCursor{k}, None{}} : E.ErrseqCheck}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(n, n), True{}, nat.eq_refl(n)) : {E.Errseq.advance.go(_, n, e, True{}, n) == E.ErrseqCheck{E.Errseq{n, e, True{}}, E.ErrseqCursor{n}, None{}} : E.ErrseqCheck}
      {==}

def adv.report(b: Bool, -n: Nat, -e: U32, -f: Bool, -k: Nat) -> {E.ErrseqCheck.error(E.Errseq.advance.go(b, n, e, f, k)) == E.Errseq.check.go(b, e) : Maybe<&2, U32>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def adv.unchanged(b: Bool, -n: Nat, -e: U32, -f: Bool, -k: Nat, q: {E.Errseq.check.go(b, e) == None{} : Maybe<&2, U32>}) -> {E.Errseq.advance.go(b, n, e, f, k) == E.ErrseqCheck{E.Errseq{n, e, f}, E.ErrseqCursor{k}, None{}} : E.ErrseqCheck}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({E.Errseq.advance.go(False{}, n, e, f, k) == E.ErrseqCheck{E.Errseq{n, e, f}, E.ErrseqCursor{k}, None{}} : E.ErrseqCheck}, ab.some_none(e, q))

def adv.valid(b: Bool, +n: Nat, -e: U32, -f: Bool, +k: Nat, v: {Nat.is_le(k, n) == True{} : Bool}) -> {E.Errseq.cursor_valid(E.ErrseqCheck.state(E.Errseq.advance.go(b, n, e, f, k)), E.ErrseqCheck.cursor(E.Errseq.advance.go(b, n, e, f, k))) == True{} : Bool}:
  match b:
    case True{}:
      v
    case False{}:
      nat.le_refl(n)

def adv.other_valid(b: Bool, -n: Nat, -e: U32, -f: Bool, -k: Nat, d: E.ErrseqCursor) -> {E.Errseq.cursor_valid(E.ErrseqCheck.state(E.Errseq.advance.go(b, n, e, f, k)), d) == E.Errseq.cursor_valid(E.Errseq{n, e, f}, d) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      match d:
        case E.ErrseqCursor{j}:
          {==}

def adv.other_check(b: Bool, -n: Nat, -e: U32, -f: Bool, -k: Nat, d: E.ErrseqCursor) -> {E.Errseq.check(E.ErrseqCheck.state(E.Errseq.advance.go(b, n, e, f, k)), d) == E.Errseq.check(E.Errseq{n, e, f}, d) : Maybe<&2, U32>}:
  match b:
    case True{}:
      {==}
    case False{}:
      match d:
        case E.ErrseqCursor{j}:
          {==}


def new.quiet(k: Nat, v: {Nat.is_le(k, 0n) == True{} : Bool}) -> {E.Errseq.check(E.Errseq.new(), E.ErrseqCursor{k}) == None{} : Maybe<&2, U32>}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({E.Errseq.check(E.Errseq.new(), E.ErrseqCursor{1n+p}) == None{} : Maybe<&2, U32>}, ab.ft(v))

def sample.le(b: Bool, +n: Nat) -> {Nat.is_le(E.Errseq.sample.back(b, n), n) == True{} : Bool}:
  match b:
    case True{}:
      nat.sub_one_le(n)
    case False{}:
      nat.le_refl(n)

def set.valid(z: Bool, +n: Nat, -o: U32, -f: Bool, +k: Nat, -e: U32, v: {Nat.is_le(k, n) == True{} : Bool}) -> {E.Errseq.cursor_valid(E.Errseq.set.go(z, E.Errseq{n, o, f}, e), E.ErrseqCursor{k}) == True{} : Bool}:
  match z:
    case True{}:
      v
    case False{}:
      nat.le_succ(k, n, v)

# The laws

def Laws.errseq_fresh_quiet(s):
  match s:
    case E.Errseq{+n, e, f}:
      check.at(n, e, f)

def Laws.errseq_fresh_sees_next(s, e, h):
  match s:
    case E.Errseq{+n, o, f}:
      %Equal.sym(Bool, U32.is_zero(e), False{}, h) : {E.Errseq.check(E.Errseq.set.go(_, E.Errseq{n, o, f}, e), E.ErrseqCursor{n}) == Some{e} : Maybe<&2, U32>}
      check.below(n, n, e, False{}, nat.le_refl(n))

def Laws.errseq_new_error_seen(s, c, e, v, h):
  match s c:
    case E.Errseq{+n, o, f} E.ErrseqCursor{+k}:
      %Equal.sym(Bool, U32.is_zero(e), False{}, h) : {E.Errseq.check(E.Errseq.set.go(_, E.Errseq{n, o, f}, e), E.ErrseqCursor{k}) == Some{e} : Maybe<&2, U32>}
      check.below(k, n, e, False{}, v)

def Laws.errseq_advance_reports_check(s, c):
  match s c:
    case E.Errseq{+n, e, f} E.ErrseqCursor{+k}:
      adv.report(Nat.is_eq(k, n), n, e, f, k)

def Laws.errseq_advance_then_quiet(s, c):
  match s c:
    case E.Errseq{+n, e, f} E.ErrseqCursor{+k}:
      adv.quiet(Nat.is_eq(k, n), n, e, f, k, {==})

def Laws.errseq_advance_twice(s, c):
  match s c:
    case E.Errseq{+n, e, f} E.ErrseqCursor{+k}:
      adv.twice(Nat.is_eq(k, n), n, e, f, k, {==})

def Laws.errseq_quiet_unchanged(s, c, q):
  match s c:
    case E.Errseq{+n, e, f} E.ErrseqCursor{+k}:
      adv.unchanged(Nat.is_eq(k, n), n, e, f, k, q)

def Laws.errseq_set_zero(s):
  {==}

def Laws.errseq_new_quiet(c, v):
  match c:
    case E.ErrseqCursor{k}:
      new.quiet(k, v)

def Laws.errseq_sample_valid(o, s):
  match o s:
    case E.ErrseqOptions{ru} E.Errseq{+n, e, f}:
      sample.le(Bool.and(ru, Bool.not(f)), n)

def Laws.errseq_advance_valid(s, c, v):
  match s c:
    case E.Errseq{+n, e, f} E.ErrseqCursor{+k}:
      adv.valid(Nat.is_eq(k, n), n, e, f, k, v)

def Laws.errseq_set_keeps_valid(s, c, e, v):
  match s c:
    case E.Errseq{+n, o, f} E.ErrseqCursor{+k}:
      set.valid(U32.is_zero(e), n, o, f, k, e, v)

def Laws.errseq_advance_keeps_other_valid(s, c, d):
  match s c:
    case E.Errseq{+n, e, f} E.ErrseqCursor{+k}:
      adv.other_valid(Nat.is_eq(k, n), n, e, f, k, d)

def Laws.errseq_advance_other_check(s, c, d):
  match s c:
    case E.Errseq{+n, e, f} E.ErrseqCursor{+k}:
      adv.other_check(Nat.is_eq(k, n), n, e, f, k, d)

def Laws.errseq_kernel_unseen(s, e, h):
  match s:
    case E.Errseq{+n, o, f}:
      %Equal.sym(Bool, U32.is_zero(e), False{}, h) : {E.Errseq.check(E.Errseq.set.go(_, E.Errseq{n, o, f}, e), E.Errseq.sample(E.ErrseqOptions.kernel(), E.Errseq.set.go(_, E.Errseq{n, o, f}, e))) == Some{e} : Maybe<&2, U32>}
      %Equal.sym(Nat, Nat.sub(n, 0n), n, nat.sub_zero(n)) : {E.Errseq.check(E.Errseq{1n+n, e, False{}}, E.ErrseqCursor{_}) == Some{e} : Maybe<&2, U32>}
      check.below(n, n, e, False{}, nat.le_refl(n))

def Laws.errseq_kernel_seen_quiet(s, c, e, v, h):
  match s c:
    case E.Errseq{+n, o, f} E.ErrseqCursor{+k}:
      %Equal.sym(Bool, U32.is_zero(e), False{}, h) : {E.Errseq.check(E.ErrseqCheck.state(E.Errseq.check_and_advance(E.Errseq.set.go(_, E.Errseq{n, o, f}, e), E.ErrseqCursor{k})), E.Errseq.sample(E.ErrseqOptions.kernel(), E.ErrseqCheck.state(E.Errseq.check_and_advance(E.Errseq.set.go(_, E.Errseq{n, o, f}, e), E.ErrseqCursor{k})))) == None{} : Maybe<&2, U32>}
      %Equal.sym(Bool, Nat.is_eq(k, 1n+n), False{}, nat.le_ne_succ(k, n, v)) : {E.Errseq.check(E.ErrseqCheck.state(E.Errseq.advance.go(_, 1n+n, e, False{}, k)), E.Errseq.sample(E.ErrseqOptions.kernel(), E.ErrseqCheck.state(E.Errseq.advance.go(_, 1n+n, e, False{}, k)))) == None{} : Maybe<&2, U32>}
      check.at(1n+n, e, True{})

def Laws.errseq_kernel_quiet_when_seen(s, h):
  match s:
    case E.Errseq{+n, e, f}:
      %Equal.sym(Bool, f, True{}, h) : {E.ErrseqCursor{E.Errseq.sample.back(Bool.and(True{}, Bool.not(_)), n)} == E.ErrseqCursor{n} : E.ErrseqCursor}
      {==}

def Laws.errseq_wit():
  {==}

def Laws.errseq_vec_two_observers():
  {==}
