import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./seq.bend as S
import ./rcvq.bend as Q
import ./cc.bend as CC
import ./segment.bend as G
import ./tcp.bend as T
import ./demux.bend as D
import ./rto.bend as R
import ./udp.bend as U
import ./icmp.bend as IC
import ./LAWS.bend as Laws

# The proofs. Sequence numbers: lemmas on Base's words (bit by bit, the
# carries of two subtractions related by a small table of states found by
# enumerating the bit and carry cases). The receive queue: induction on the
# held pieces, with bytes' interface laws for lengths. The TCP laws: the
# state is Tcp.next_state of the input a step computes, checked state by
# state; SND.UNA is followed through every stage of a step, each stage a
# lemma that matches what the code matches. The demultiplexer, UDP, ICMP and
# the timer: induction on the table, or the cases of the code.

# a - a = 0, with the carry in of a subtraction
def w_sub_self(n: Nat, a: Word(n)) -> {Word.adc(n, a, a, True{}, True{}) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{False{}, t}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, t, t, True{}, True{}), Word.zero(p), w_sub_self(p, t))
        case WCon{True{}, t}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, t, t, True{}, True{}), Word.zero(p), w_sub_self(p, t))

def Laws.seq_lt_irrefl(a):
  match a:
    case U32{x}:
      %Equal.sym(Word(32n), Word.adc(32n, x, x, True{}, True{}), Word.zero(32n), w_sub_self(32n, x)) : {S.SeqNum.in_half(U32{_}) == False{} : Bool}
      {==}

# (a + d + c) - a - (1 - c') = d: the carries of the two chains are each
# other's negation
def w_add_sub(n: Nat, a: Word(n), d: Word(n), c: Bool) -> {Word.adc(n, Word.adc(n, a, d, False{}, c), a, True{}, Bool.not(c)) == d : Word(n)}:
  match n:
    case 0n:
      match a d:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a d c:
        case WCon{False{}, at} WCon{False{}, dt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, at, dt, False{}, False{}), at, True{}, True{}), dt, w_add_sub(p, at, dt, False{}))
        case WCon{False{}, at} WCon{False{}, dt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, at, dt, False{}, False{}), at, True{}, True{}), dt, w_add_sub(p, at, dt, False{}))
        case WCon{False{}, at} WCon{True{}, dt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, at, dt, False{}, False{}), at, True{}, True{}), dt, w_add_sub(p, at, dt, False{}))
        case WCon{False{}, at} WCon{True{}, dt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, at, dt, False{}, True{}), at, True{}, False{}), dt, w_add_sub(p, at, dt, True{}))
        case WCon{True{}, at} WCon{False{}, dt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, at, dt, False{}, False{}), at, True{}, True{}), dt, w_add_sub(p, at, dt, False{}))
        case WCon{True{}, at} WCon{False{}, dt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, at, dt, False{}, True{}), at, True{}, False{}), dt, w_add_sub(p, at, dt, True{}))
        case WCon{True{}, at} WCon{True{}, dt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, at, dt, False{}, True{}), at, True{}, False{}), dt, w_add_sub(p, at, dt, True{}))
        case WCon{True{}, at} WCon{True{}, dt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, at, dt, False{}, True{}), at, True{}, False{}), dt, w_add_sub(p, at, dt, True{}))

def Laws.seq_lt_add(a, d):
  match a d:
    case U32{x} U32{y}:
      %Equal.sym(Word(32n), Word.adc(32n, Word.adc(32n, x, y, False{}, False{}), x, True{}, True{}), y, w_add_sub(32n, x, y, False{})) : {S.SeqNum.in_half(U32{_}) == S.SeqNum.in_half(U32{y}) : Bool}
      {==}
# The carries of a - b and of 0 - (b - a), bit by bit: three combinations
# occur (found by enumerating the bit and carry cases)
type TpW4 is Data:
  TpW4a{}
  TpW4b{}
  TpW4c{}

def w4.c1(s: TpW4) -> Bool:
  match s:
    case TpW4a{}:
      False{}
    case TpW4b{}:
      True{}
    case TpW4c{}:
      True{}

def w4.c2(s: TpW4) -> Bool:
  match s:
    case TpW4a{}:
      True{}
    case TpW4b{}:
      False{}
    case TpW4c{}:
      True{}

def w4.c3(s: TpW4) -> Bool:
  match s:
    case TpW4a{}:
      False{}
    case TpW4b{}:
      False{}
    case TpW4c{}:
      True{}

# a - b = 0 - (b - a)
def w_sub_neg(n: Nat, s: TpW4, a: Word(n), b: Word(n)) -> {Word.adc(n, a, b, True{}, w4.c1(s)) == Word.adc(n, Word.zero(n), Word.adc(n, b, a, True{}, w4.c2(s)), True{}, w4.c3(s)) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match s a b:
        case TpW4a{} WCon{False{}, at} WCon{False{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, at, bt, True{}, False{}), Word.adc(p, Word.zero(p), Word.adc(p, bt, at, True{}, True{}), True{}, False{}), w_sub_neg(p, TpW4a{}, at, bt))
        case TpW4a{} WCon{False{}, at} WCon{True{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, at, bt, True{}, False{}), Word.adc(p, Word.zero(p), Word.adc(p, bt, at, True{}, True{}), True{}, False{}), w_sub_neg(p, TpW4a{}, at, bt))
        case TpW4a{} WCon{True{}, at} WCon{False{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, at, bt, True{}, True{}), Word.adc(p, Word.zero(p), Word.adc(p, bt, at, True{}, False{}), True{}, False{}), w_sub_neg(p, TpW4b{}, at, bt))
        case TpW4a{} WCon{True{}, at} WCon{True{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, at, bt, True{}, False{}), Word.adc(p, Word.zero(p), Word.adc(p, bt, at, True{}, True{}), True{}, False{}), w_sub_neg(p, TpW4a{}, at, bt))
        case TpW4b{} WCon{False{}, at} WCon{False{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, at, bt, True{}, True{}), Word.adc(p, Word.zero(p), Word.adc(p, bt, at, True{}, False{}), True{}, False{}), w_sub_neg(p, TpW4b{}, at, bt))
        case TpW4b{} WCon{False{}, at} WCon{True{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, at, bt, True{}, False{}), Word.adc(p, Word.zero(p), Word.adc(p, bt, at, True{}, True{}), True{}, False{}), w_sub_neg(p, TpW4a{}, at, bt))
        case TpW4b{} WCon{True{}, at} WCon{False{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, at, bt, True{}, True{}), Word.adc(p, Word.zero(p), Word.adc(p, bt, at, True{}, False{}), True{}, False{}), w_sub_neg(p, TpW4b{}, at, bt))
        case TpW4b{} WCon{True{}, at} WCon{True{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, at, bt, True{}, True{}), Word.adc(p, Word.zero(p), Word.adc(p, bt, at, True{}, False{}), True{}, False{}), w_sub_neg(p, TpW4b{}, at, bt))
        case TpW4c{} WCon{False{}, at} WCon{False{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, at, bt, True{}, True{}), Word.adc(p, Word.zero(p), Word.adc(p, bt, at, True{}, True{}), True{}, True{}), w_sub_neg(p, TpW4c{}, at, bt))
        case TpW4c{} WCon{False{}, at} WCon{True{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, at, bt, True{}, False{}), Word.adc(p, Word.zero(p), Word.adc(p, bt, at, True{}, True{}), True{}, False{}), w_sub_neg(p, TpW4a{}, at, bt))
        case TpW4c{} WCon{True{}, at} WCon{False{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, at, bt, True{}, True{}), Word.adc(p, Word.zero(p), Word.adc(p, bt, at, True{}, False{}), True{}, False{}), w_sub_neg(p, TpW4b{}, at, bt))
        case TpW4c{} WCon{True{}, at} WCon{True{}, bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, at, bt, True{}, True{}), Word.adc(p, Word.zero(p), Word.adc(p, bt, at, True{}, True{}), True{}, True{}), w_sub_neg(p, TpW4c{}, at, bt))

# The top bit of 0 - x - (1 - c) (Base's subtraction adds the complement and
# a carry c): the complement of x's top bit, flipped when the carry reaches
# it, which happens when c is set and every lower bit of x is zero
def w_neg_top(n: Nat, x: Word(1n+n), c: Bool) -> {S.SeqNum.word.top(1n+n, Word.adc(1n+n, Word.zero(1n+n), x, True{}, c)) == Bool.xor(Bool.not(S.SeqNum.word.top(1n+n, x)), Bool.and(c, S.SeqNum.word.low0(1n+n, x))) : Bool}:
  match n:
    case 0n:
      match x c:
        case WCon{x0, xt} True{}:
          {==}
        case WCon{x0, xt} False{}:
          {==}
    case 1n+p:
      match x c:
        case WCon{False{}, WCon{x1, xr}} False{}:
          w_neg_top(p, WCon{x1, xr}, False{})
        case WCon{False{}, WCon{x1, xr}} True{}:
          w_neg_top(p, WCon{x1, xr}, True{})
        case WCon{True{}, WCon{x1, xr}} False{}:
          w_neg_top(p, WCon{x1, xr}, False{})
        case WCon{True{}, WCon{x1, xr}} True{}:
          w_neg_top(p, WCon{x1, xr}, False{})

# Contradictions

def absurd.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def absurd.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : absurd.bool(_)
  Unit{}

# a distance in (0, 2^31) has a negation outside it
def bool_neg_half(t: Bool, l: Bool, z: Bool, h: {Bool.and(Bool.not(t), Bool.not(l)) == True{} : Bool}) -> {Bool.and(Bool.not(Bool.xor(Bool.not(t), l)), z) == False{} : Bool}:
  match t l:
    case False{} False{}:
      {==}
    case False{} True{}:
      Empty.absurd({Bool.and(Bool.not(Bool.xor(Bool.not(False{}), True{})), z) == False{} : Bool}, absurd.ft(h))
    case True{} False{}:
      Empty.absurd({Bool.and(Bool.not(Bool.xor(Bool.not(True{}), False{})), z) == False{} : Bool}, absurd.ft(h))
    case True{} True{}:
      Empty.absurd({Bool.and(Bool.not(Bool.xor(Bool.not(True{}), True{})), z) == False{} : Bool}, absurd.ft(h))

def Laws.seq_lt_asym(a, b, h):
  match a b:
    case U32{xa} U32{xb}:
      +w = Word.adc(32n, xb, xa, True{}, True{})
      +nw = Word.adc(32n, Word.zero(32n), w, True{}, True{})
      %Equal.sym(Word(32n), Word.adc(32n, xa, xb, True{}, True{}), nw, w_sub_neg(32n, TpW4c{}, xa, xb)) : {S.SeqNum.in_half(U32{_}) == False{} : Bool}
      %Equal.sym(Bool, S.SeqNum.word.top(32n, nw), Bool.xor(Bool.not(S.SeqNum.word.top(32n, w)), S.SeqNum.word.low0(32n, w)), w_neg_top(31n, w, True{})) : {Bool.and(Bool.not(_), Bool.not(S.SeqNum.word.low0(32n, nw))) == False{} : Bool}
      bool_neg_half(S.SeqNum.word.top(32n, w), S.SeqNum.word.low0(32n, w), Bool.not(S.SeqNum.word.low0(32n, nw)), h)
# The carries of (b - a) + (c - b) and of c - a, bit by bit: six
# combinations occur
type TpW7 is Data:
  TpW7a{}
  TpW7b{}
  TpW7c{}
  TpW7d{}
  TpW7e{}
  TpW7f{}

def w7.c1(s: TpW7) -> Bool:
  match s:
    case TpW7a{}:
      True{}
    case TpW7b{}:
      True{}
    case TpW7c{}:
      False{}
    case TpW7d{}:
      False{}
    case TpW7e{}:
      True{}
    case TpW7f{}:
      False{}

def w7.c2(s: TpW7) -> Bool:
  match s:
    case TpW7a{}:
      True{}
    case TpW7b{}:
      False{}
    case TpW7c{}:
      True{}
    case TpW7d{}:
      True{}
    case TpW7e{}:
      False{}
    case TpW7f{}:
      False{}

def w7.c3(s: TpW7) -> Bool:
  match s:
    case TpW7a{}:
      False{}
    case TpW7b{}:
      True{}
    case TpW7c{}:
      False{}
    case TpW7d{}:
      True{}
    case TpW7e{}:
      False{}
    case TpW7f{}:
      True{}

def w7.c4(s: TpW7) -> Bool:
  match s:
    case TpW7a{}:
      True{}
    case TpW7b{}:
      True{}
    case TpW7c{}:
      False{}
    case TpW7d{}:
      True{}
    case TpW7e{}:
      False{}
    case TpW7f{}:
      False{}

# (b - a) + (c - b) = c - a
def w_dist_add(n: Nat, s: TpW7, a: Word(n), b: Word(n), c: Word(n)) -> {Word.adc(n, Word.adc(n, b, a, True{}, w7.c1(s)), Word.adc(n, c, b, True{}, w7.c2(s)), False{}, w7.c3(s)) == Word.adc(n, c, a, True{}, w7.c4(s)) : Word(n)}:
  match n:
    case 0n:
      match a b c:
        case WNil{} WNil{} WNil{}:
          {==}
    case 1n+p:
      match s a b c:
        case TpW7a{} WCon{False{}, at} WCon{False{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, True{}), False{}, False{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7a{}, at, bt, ct))
        case TpW7a{} WCon{False{}, at} WCon{False{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, True{}), False{}, False{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7a{}, at, bt, ct))
        case TpW7a{} WCon{False{}, at} WCon{True{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, False{}), False{}, True{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7b{}, at, bt, ct))
        case TpW7a{} WCon{False{}, at} WCon{True{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, True{}), False{}, False{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7a{}, at, bt, ct))
        case TpW7a{} WCon{True{}, at} WCon{False{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, True{}), False{}, False{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7c{}, at, bt, ct))
        case TpW7a{} WCon{True{}, at} WCon{False{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, True{}), False{}, True{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7d{}, at, bt, ct))
        case TpW7a{} WCon{True{}, at} WCon{True{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, False{}), False{}, False{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7e{}, at, bt, ct))
        case TpW7a{} WCon{True{}, at} WCon{True{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, True{}), False{}, False{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7a{}, at, bt, ct))
        case TpW7b{} WCon{False{}, at} WCon{False{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, False{}), False{}, True{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7b{}, at, bt, ct))
        case TpW7b{} WCon{False{}, at} WCon{False{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, True{}), False{}, False{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7a{}, at, bt, ct))
        case TpW7b{} WCon{False{}, at} WCon{True{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, False{}), False{}, True{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7b{}, at, bt, ct))
        case TpW7b{} WCon{False{}, at} WCon{True{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, False{}), False{}, True{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7b{}, at, bt, ct))
        case TpW7b{} WCon{True{}, at} WCon{False{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, False{}), False{}, True{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7f{}, at, bt, ct))
        case TpW7b{} WCon{True{}, at} WCon{False{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, True{}), False{}, True{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7d{}, at, bt, ct))
        case TpW7b{} WCon{True{}, at} WCon{True{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, False{}), False{}, False{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7e{}, at, bt, ct))
        case TpW7b{} WCon{True{}, at} WCon{True{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, False{}), False{}, True{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7b{}, at, bt, ct))
        case TpW7c{} WCon{False{}, at} WCon{False{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, True{}), False{}, False{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7c{}, at, bt, ct))
        case TpW7c{} WCon{False{}, at} WCon{False{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, True{}), False{}, True{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7d{}, at, bt, ct))
        case TpW7c{} WCon{False{}, at} WCon{True{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, False{}), False{}, False{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7e{}, at, bt, ct))
        case TpW7c{} WCon{False{}, at} WCon{True{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, True{}), False{}, False{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7a{}, at, bt, ct))
        case TpW7c{} WCon{True{}, at} WCon{False{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, True{}), False{}, False{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7c{}, at, bt, ct))
        case TpW7c{} WCon{True{}, at} WCon{False{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, True{}), False{}, False{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7c{}, at, bt, ct))
        case TpW7c{} WCon{True{}, at} WCon{True{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, False{}), False{}, True{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7f{}, at, bt, ct))
        case TpW7c{} WCon{True{}, at} WCon{True{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, True{}), False{}, False{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7c{}, at, bt, ct))
        case TpW7d{} WCon{False{}, at} WCon{False{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, True{}), False{}, True{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7d{}, at, bt, ct))
        case TpW7d{} WCon{False{}, at} WCon{False{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, True{}), False{}, True{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7d{}, at, bt, ct))
        case TpW7d{} WCon{False{}, at} WCon{True{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, False{}), False{}, True{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7b{}, at, bt, ct))
        case TpW7d{} WCon{False{}, at} WCon{True{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, True{}), False{}, False{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7a{}, at, bt, ct))
        case TpW7d{} WCon{True{}, at} WCon{False{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, True{}), False{}, False{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7c{}, at, bt, ct))
        case TpW7d{} WCon{True{}, at} WCon{False{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, True{}), False{}, True{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7d{}, at, bt, ct))
        case TpW7d{} WCon{True{}, at} WCon{True{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, False{}), False{}, True{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7f{}, at, bt, ct))
        case TpW7d{} WCon{True{}, at} WCon{True{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, True{}), False{}, True{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7d{}, at, bt, ct))
        case TpW7e{} WCon{False{}, at} WCon{False{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, False{}), False{}, False{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7e{}, at, bt, ct))
        case TpW7e{} WCon{False{}, at} WCon{False{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, True{}), False{}, False{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7a{}, at, bt, ct))
        case TpW7e{} WCon{False{}, at} WCon{True{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, False{}), False{}, False{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7e{}, at, bt, ct))
        case TpW7e{} WCon{False{}, at} WCon{True{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, False{}), False{}, True{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7b{}, at, bt, ct))
        case TpW7e{} WCon{True{}, at} WCon{False{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, False{}), False{}, True{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7f{}, at, bt, ct))
        case TpW7e{} WCon{True{}, at} WCon{False{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, True{}), False{}, False{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7c{}, at, bt, ct))
        case TpW7e{} WCon{True{}, at} WCon{True{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, False{}), False{}, False{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7e{}, at, bt, ct))
        case TpW7e{} WCon{True{}, at} WCon{True{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, False{}), False{}, False{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7e{}, at, bt, ct))
        case TpW7f{} WCon{False{}, at} WCon{False{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, False{}), False{}, True{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7f{}, at, bt, ct))
        case TpW7f{} WCon{False{}, at} WCon{False{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, True{}), False{}, True{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7d{}, at, bt, ct))
        case TpW7f{} WCon{False{}, at} WCon{True{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, False{}), False{}, False{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7e{}, at, bt, ct))
        case TpW7f{} WCon{False{}, at} WCon{True{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, True{}), Word.adc(p, ct, bt, True{}, False{}), False{}, True{}), Word.adc(p, ct, at, True{}, True{}), w_dist_add(p, TpW7b{}, at, bt, ct))
        case TpW7f{} WCon{True{}, at} WCon{False{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, False{}), False{}, True{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7f{}, at, bt, ct))
        case TpW7f{} WCon{True{}, at} WCon{False{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, True{}), False{}, False{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7c{}, at, bt, ct))
        case TpW7f{} WCon{True{}, at} WCon{True{}, bt} WCon{False{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, False{}), False{}, True{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7f{}, at, bt, ct))
        case TpW7f{} WCon{True{}, at} WCon{True{}, bt} WCon{True{}, ct}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.adc(p, Word.adc(p, bt, at, True{}, False{}), Word.adc(p, ct, bt, True{}, False{}), False{}, True{}), Word.adc(p, ct, at, True{}, False{}), w_dist_add(p, TpW7f{}, at, bt, ct))

def Laws.seq_dist_add(a, b, c):
  match a b c:
    case U32{xa} U32{xb} U32{xc}:
      %w_dist_add(32n, TpW7a{}, xa, xb, xc) : {U32{_} == U32{Word.adc(32n, Word.adc(32n, xb, xa, True{}, True{}), Word.adc(32n, xc, xb, True{}, True{}), False{}, False{})} : U32}
      {==}

def Laws.seq_lt_trans(a, b, c, h1, h2, h3):
  %Equal.sym(U32, U32.sub(c, a), U32.add(U32.sub(b, a), U32.sub(c, b)), Laws.seq_dist_add(a, b, c)) : {S.SeqNum.in_half(_) == True{} : Bool}
  h3

# Nat and length lemmas

def nat_add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 0n), p, nat_add_zero(p))

def nat_add_assoc(a: Nat, b: Nat, c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), nat_add_assoc(p, b, c))

def list_len_append(xs: List<&2, U32>, ys: List<&2, U32>) -> {B.len(B.append(xs, ys)) == Nat.add(B.len(xs), B.len(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, x => 1n+x, B.len(B.append(t, ys)), Nat.add(B.len(t), B.len(ys)), list_len_append(t, ys))

def len_list(+o: B.Octets) -> {B.len(B.Octets.to_list(o)) == B.Octets.len(o) : Nat}:
  Equal.sym(Nat, B.Octets.len(o), B.len(B.Octets.to_list(o)), BL.octets_len_list(o))

def octets_len_append(+a: B.Octets, +b: B.Octets) -> {B.Octets.len(B.Octets.append(a, b)) == Nat.add(B.Octets.len(a), B.Octets.len(b)) : Nat}:
  %len_list(B.Octets.append(a, b)) : {_ == Nat.add(B.Octets.len(a), B.Octets.len(b)) : Nat}
  %len_list(a) : {B.len(B.Octets.to_list(B.Octets.append(a, b))) == Nat.add(_, B.Octets.len(b)) : Nat}
  %len_list(b) : {B.len(B.Octets.to_list(B.Octets.append(a, b))) == Nat.add(B.len(B.Octets.to_list(a)), _) : Nat}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b)) : {B.len(_) == Nat.add(B.len(B.Octets.to_list(a)), B.len(B.Octets.to_list(b))) : Nat}
  list_len_append(B.Octets.to_list(a), B.Octets.to_list(b))

# The receive queue: what is delivered moves the next offset by its length

def cons_next(f: B.Octets, o: Q.RcvOut) -> {Q.RcvQ.next(Q.RcvOut.queue(Q.RcvOut.cons(f, o))) == Q.RcvQ.next(Q.RcvOut.queue(o)) : Nat}:
  match o:
    case Q.RcvOut{n, h, d}:
      {==}

def cons_data(f: B.Octets, o: Q.RcvOut) -> {Q.RcvOut.data(Q.RcvOut.cons(f, o)) == B.Octets.append(f, Q.RcvOut.data(o)) : B.Octets}:
  match o:
    case Q.RcvOut{n, h, d}:
      {==}

def pull_contig(+xs: List<&2, Q.RcvSeg>, +n: Nat, r: Bool) -> {Q.RcvQ.next(Q.RcvOut.queue(Q.RcvQ.pull(xs, n, r))) == Nat.add(n, B.Octets.len(Q.RcvOut.data(Q.RcvQ.pull(xs, n, r)))) : Nat}:
  match xs:
    case Nil{}:
      Equal.sym(Nat, Nat.add(n, 0n), n, nat_add_zero(n))
    case Con{Q.RcvSeg{+at, +d}, +t}:
      match r:
        case False{}:
          Equal.sym(Nat, Nat.add(n, 0n), n, nat_add_zero(n))
        case True{}:
          +f = B.Octets.drop(Nat.sub(n, at), d)
          +n2 = Nat.add(n, B.Octets.len(f))
          +o = Q.RcvQ.pull(t, n2, Q.RcvQ.ready(t, n2))
          +lo = B.Octets.len(Q.RcvOut.data(o))
          +e1 = cons_next(f, o)
          +e2 = pull_contig(t, n2, Q.RcvQ.ready(t, n2))
          +e3 = nat_add_assoc(n, B.Octets.len(f), lo)
          +e4 = Equal.cong(Nat, Nat, x => Nat.add(n, x), Nat.add(B.Octets.len(f), lo), B.Octets.len(B.Octets.append(f, Q.RcvOut.data(o))), Equal.sym(Nat, B.Octets.len(B.Octets.append(f, Q.RcvOut.data(o))), Nat.add(B.Octets.len(f), lo), octets_len_append(f, Q.RcvOut.data(o))))
          +e5 = Equal.cong(B.Octets, Nat, x => Nat.add(n, B.Octets.len(x)), B.Octets.append(f, Q.RcvOut.data(o)), Q.RcvOut.data(Q.RcvOut.cons(f, o)), Equal.sym(B.Octets, Q.RcvOut.data(Q.RcvOut.cons(f, o)), B.Octets.append(f, Q.RcvOut.data(o)), cons_data(f, o)))
          +x1 = Q.RcvQ.next(Q.RcvOut.queue(Q.RcvOut.cons(f, o)))
          +x2 = Q.RcvQ.next(Q.RcvOut.queue(o))
          +x3 = Nat.add(n2, lo)
          +x4 = Nat.add(n, Nat.add(B.Octets.len(f), lo))
          +x5 = Nat.add(n, B.Octets.len(B.Octets.append(f, Q.RcvOut.data(o))))
          +x6 = Nat.add(n, B.Octets.len(Q.RcvOut.data(Q.RcvOut.cons(f, o))))
          Equal.trans(Nat, x1, x2, x6, e1, Equal.trans(Nat, x2, x3, x6, e2, Equal.trans(Nat, x3, x4, x6, e3, Equal.trans(Nat, x4, x5, x6, e4, e5))))

def Laws.rcvq_contiguous(limit, q, rel, d):
  match q:
    case Q.RcvQ{n, held}:
      +xs = Q.RcvQ.admit(Bool.and(Nat.is_gt(B.Octets.len(d), 0n), Bool.or(Nat.is_eq(rel, 0n), Nat.is_lt(Q.RcvQ.held.count(held, 0n), limit))), held, Q.RcvSeg{Nat.add(n, rel), d}, Nat.add(n, rel))
      pull_contig(xs, n, Q.RcvQ.ready(xs, n))

# The state diagram: every transition Tcp.next_state takes is allowed,
# checked state by state and input by input
def tcp_next_allowed(s: T.TcpState, k: T.TcpInput) -> {T.Tcp.allowed(s, T.Tcp.next_state(s, k)) == True{} : Bool}:
  match s k:
    case T.TcpClosed{} T.TcpInPassiveOpen{}:
      {==}
    case T.TcpClosed{} T.TcpInActiveOpen{}:
      {==}
    case T.TcpClosed{} T.TcpInClose{}:
      {==}
    case T.TcpClosed{} T.TcpInAbort{}:
      {==}
    case T.TcpClosed{} T.TcpInNone{}:
      {==}
    case T.TcpClosed{} T.TcpInReset{True{}}:
      {==}
    case T.TcpClosed{} T.TcpInReset{False{}}:
      {==}
    case T.TcpClosed{} T.TcpInSyn{}:
      {==}
    case T.TcpClosed{} T.TcpInSynAck{True{}}:
      {==}
    case T.TcpClosed{} T.TcpInSynAck{False{}}:
      {==}
    case T.TcpClosed{} T.TcpInSeg{True{}, True{}}:
      {==}
    case T.TcpClosed{} T.TcpInSeg{True{}, False{}}:
      {==}
    case T.TcpClosed{} T.TcpInSeg{False{}, True{}}:
      {==}
    case T.TcpClosed{} T.TcpInSeg{False{}, False{}}:
      {==}
    case T.TcpClosed{} T.TcpInGiveUp{}:
      {==}
    case T.TcpClosed{} T.TcpInTimeWaitEnd{}:
      {==}
    case T.TcpListen{} T.TcpInPassiveOpen{}:
      {==}
    case T.TcpListen{} T.TcpInActiveOpen{}:
      {==}
    case T.TcpListen{} T.TcpInClose{}:
      {==}
    case T.TcpListen{} T.TcpInAbort{}:
      {==}
    case T.TcpListen{} T.TcpInNone{}:
      {==}
    case T.TcpListen{} T.TcpInReset{True{}}:
      {==}
    case T.TcpListen{} T.TcpInReset{False{}}:
      {==}
    case T.TcpListen{} T.TcpInSyn{}:
      {==}
    case T.TcpListen{} T.TcpInSynAck{True{}}:
      {==}
    case T.TcpListen{} T.TcpInSynAck{False{}}:
      {==}
    case T.TcpListen{} T.TcpInSeg{True{}, True{}}:
      {==}
    case T.TcpListen{} T.TcpInSeg{True{}, False{}}:
      {==}
    case T.TcpListen{} T.TcpInSeg{False{}, True{}}:
      {==}
    case T.TcpListen{} T.TcpInSeg{False{}, False{}}:
      {==}
    case T.TcpListen{} T.TcpInGiveUp{}:
      {==}
    case T.TcpListen{} T.TcpInTimeWaitEnd{}:
      {==}
    case T.TcpSynSent{} T.TcpInPassiveOpen{}:
      {==}
    case T.TcpSynSent{} T.TcpInActiveOpen{}:
      {==}
    case T.TcpSynSent{} T.TcpInClose{}:
      {==}
    case T.TcpSynSent{} T.TcpInAbort{}:
      {==}
    case T.TcpSynSent{} T.TcpInNone{}:
      {==}
    case T.TcpSynSent{} T.TcpInReset{True{}}:
      {==}
    case T.TcpSynSent{} T.TcpInReset{False{}}:
      {==}
    case T.TcpSynSent{} T.TcpInSyn{}:
      {==}
    case T.TcpSynSent{} T.TcpInSynAck{True{}}:
      {==}
    case T.TcpSynSent{} T.TcpInSynAck{False{}}:
      {==}
    case T.TcpSynSent{} T.TcpInSeg{True{}, True{}}:
      {==}
    case T.TcpSynSent{} T.TcpInSeg{True{}, False{}}:
      {==}
    case T.TcpSynSent{} T.TcpInSeg{False{}, True{}}:
      {==}
    case T.TcpSynSent{} T.TcpInSeg{False{}, False{}}:
      {==}
    case T.TcpSynSent{} T.TcpInGiveUp{}:
      {==}
    case T.TcpSynSent{} T.TcpInTimeWaitEnd{}:
      {==}
    case T.TcpSynReceived{} T.TcpInPassiveOpen{}:
      {==}
    case T.TcpSynReceived{} T.TcpInActiveOpen{}:
      {==}
    case T.TcpSynReceived{} T.TcpInClose{}:
      {==}
    case T.TcpSynReceived{} T.TcpInAbort{}:
      {==}
    case T.TcpSynReceived{} T.TcpInNone{}:
      {==}
    case T.TcpSynReceived{} T.TcpInReset{True{}}:
      {==}
    case T.TcpSynReceived{} T.TcpInReset{False{}}:
      {==}
    case T.TcpSynReceived{} T.TcpInSyn{}:
      {==}
    case T.TcpSynReceived{} T.TcpInSynAck{True{}}:
      {==}
    case T.TcpSynReceived{} T.TcpInSynAck{False{}}:
      {==}
    case T.TcpSynReceived{} T.TcpInSeg{True{}, True{}}:
      {==}
    case T.TcpSynReceived{} T.TcpInSeg{True{}, False{}}:
      {==}
    case T.TcpSynReceived{} T.TcpInSeg{False{}, True{}}:
      {==}
    case T.TcpSynReceived{} T.TcpInSeg{False{}, False{}}:
      {==}
    case T.TcpSynReceived{} T.TcpInGiveUp{}:
      {==}
    case T.TcpSynReceived{} T.TcpInTimeWaitEnd{}:
      {==}
    case T.TcpEstablished{} T.TcpInPassiveOpen{}:
      {==}
    case T.TcpEstablished{} T.TcpInActiveOpen{}:
      {==}
    case T.TcpEstablished{} T.TcpInClose{}:
      {==}
    case T.TcpEstablished{} T.TcpInAbort{}:
      {==}
    case T.TcpEstablished{} T.TcpInNone{}:
      {==}
    case T.TcpEstablished{} T.TcpInReset{True{}}:
      {==}
    case T.TcpEstablished{} T.TcpInReset{False{}}:
      {==}
    case T.TcpEstablished{} T.TcpInSyn{}:
      {==}
    case T.TcpEstablished{} T.TcpInSynAck{True{}}:
      {==}
    case T.TcpEstablished{} T.TcpInSynAck{False{}}:
      {==}
    case T.TcpEstablished{} T.TcpInSeg{True{}, True{}}:
      {==}
    case T.TcpEstablished{} T.TcpInSeg{True{}, False{}}:
      {==}
    case T.TcpEstablished{} T.TcpInSeg{False{}, True{}}:
      {==}
    case T.TcpEstablished{} T.TcpInSeg{False{}, False{}}:
      {==}
    case T.TcpEstablished{} T.TcpInGiveUp{}:
      {==}
    case T.TcpEstablished{} T.TcpInTimeWaitEnd{}:
      {==}
    case T.TcpFinWait1{} T.TcpInPassiveOpen{}:
      {==}
    case T.TcpFinWait1{} T.TcpInActiveOpen{}:
      {==}
    case T.TcpFinWait1{} T.TcpInClose{}:
      {==}
    case T.TcpFinWait1{} T.TcpInAbort{}:
      {==}
    case T.TcpFinWait1{} T.TcpInNone{}:
      {==}
    case T.TcpFinWait1{} T.TcpInReset{True{}}:
      {==}
    case T.TcpFinWait1{} T.TcpInReset{False{}}:
      {==}
    case T.TcpFinWait1{} T.TcpInSyn{}:
      {==}
    case T.TcpFinWait1{} T.TcpInSynAck{True{}}:
      {==}
    case T.TcpFinWait1{} T.TcpInSynAck{False{}}:
      {==}
    case T.TcpFinWait1{} T.TcpInSeg{True{}, True{}}:
      {==}
    case T.TcpFinWait1{} T.TcpInSeg{True{}, False{}}:
      {==}
    case T.TcpFinWait1{} T.TcpInSeg{False{}, True{}}:
      {==}
    case T.TcpFinWait1{} T.TcpInSeg{False{}, False{}}:
      {==}
    case T.TcpFinWait1{} T.TcpInGiveUp{}:
      {==}
    case T.TcpFinWait1{} T.TcpInTimeWaitEnd{}:
      {==}
    case T.TcpFinWait2{} T.TcpInPassiveOpen{}:
      {==}
    case T.TcpFinWait2{} T.TcpInActiveOpen{}:
      {==}
    case T.TcpFinWait2{} T.TcpInClose{}:
      {==}
    case T.TcpFinWait2{} T.TcpInAbort{}:
      {==}
    case T.TcpFinWait2{} T.TcpInNone{}:
      {==}
    case T.TcpFinWait2{} T.TcpInReset{True{}}:
      {==}
    case T.TcpFinWait2{} T.TcpInReset{False{}}:
      {==}
    case T.TcpFinWait2{} T.TcpInSyn{}:
      {==}
    case T.TcpFinWait2{} T.TcpInSynAck{True{}}:
      {==}
    case T.TcpFinWait2{} T.TcpInSynAck{False{}}:
      {==}
    case T.TcpFinWait2{} T.TcpInSeg{True{}, True{}}:
      {==}
    case T.TcpFinWait2{} T.TcpInSeg{True{}, False{}}:
      {==}
    case T.TcpFinWait2{} T.TcpInSeg{False{}, True{}}:
      {==}
    case T.TcpFinWait2{} T.TcpInSeg{False{}, False{}}:
      {==}
    case T.TcpFinWait2{} T.TcpInGiveUp{}:
      {==}
    case T.TcpFinWait2{} T.TcpInTimeWaitEnd{}:
      {==}
    case T.TcpCloseWait{} T.TcpInPassiveOpen{}:
      {==}
    case T.TcpCloseWait{} T.TcpInActiveOpen{}:
      {==}
    case T.TcpCloseWait{} T.TcpInClose{}:
      {==}
    case T.TcpCloseWait{} T.TcpInAbort{}:
      {==}
    case T.TcpCloseWait{} T.TcpInNone{}:
      {==}
    case T.TcpCloseWait{} T.TcpInReset{True{}}:
      {==}
    case T.TcpCloseWait{} T.TcpInReset{False{}}:
      {==}
    case T.TcpCloseWait{} T.TcpInSyn{}:
      {==}
    case T.TcpCloseWait{} T.TcpInSynAck{True{}}:
      {==}
    case T.TcpCloseWait{} T.TcpInSynAck{False{}}:
      {==}
    case T.TcpCloseWait{} T.TcpInSeg{True{}, True{}}:
      {==}
    case T.TcpCloseWait{} T.TcpInSeg{True{}, False{}}:
      {==}
    case T.TcpCloseWait{} T.TcpInSeg{False{}, True{}}:
      {==}
    case T.TcpCloseWait{} T.TcpInSeg{False{}, False{}}:
      {==}
    case T.TcpCloseWait{} T.TcpInGiveUp{}:
      {==}
    case T.TcpCloseWait{} T.TcpInTimeWaitEnd{}:
      {==}
    case T.TcpClosing{} T.TcpInPassiveOpen{}:
      {==}
    case T.TcpClosing{} T.TcpInActiveOpen{}:
      {==}
    case T.TcpClosing{} T.TcpInClose{}:
      {==}
    case T.TcpClosing{} T.TcpInAbort{}:
      {==}
    case T.TcpClosing{} T.TcpInNone{}:
      {==}
    case T.TcpClosing{} T.TcpInReset{True{}}:
      {==}
    case T.TcpClosing{} T.TcpInReset{False{}}:
      {==}
    case T.TcpClosing{} T.TcpInSyn{}:
      {==}
    case T.TcpClosing{} T.TcpInSynAck{True{}}:
      {==}
    case T.TcpClosing{} T.TcpInSynAck{False{}}:
      {==}
    case T.TcpClosing{} T.TcpInSeg{True{}, True{}}:
      {==}
    case T.TcpClosing{} T.TcpInSeg{True{}, False{}}:
      {==}
    case T.TcpClosing{} T.TcpInSeg{False{}, True{}}:
      {==}
    case T.TcpClosing{} T.TcpInSeg{False{}, False{}}:
      {==}
    case T.TcpClosing{} T.TcpInGiveUp{}:
      {==}
    case T.TcpClosing{} T.TcpInTimeWaitEnd{}:
      {==}
    case T.TcpLastAck{} T.TcpInPassiveOpen{}:
      {==}
    case T.TcpLastAck{} T.TcpInActiveOpen{}:
      {==}
    case T.TcpLastAck{} T.TcpInClose{}:
      {==}
    case T.TcpLastAck{} T.TcpInAbort{}:
      {==}
    case T.TcpLastAck{} T.TcpInNone{}:
      {==}
    case T.TcpLastAck{} T.TcpInReset{True{}}:
      {==}
    case T.TcpLastAck{} T.TcpInReset{False{}}:
      {==}
    case T.TcpLastAck{} T.TcpInSyn{}:
      {==}
    case T.TcpLastAck{} T.TcpInSynAck{True{}}:
      {==}
    case T.TcpLastAck{} T.TcpInSynAck{False{}}:
      {==}
    case T.TcpLastAck{} T.TcpInSeg{True{}, True{}}:
      {==}
    case T.TcpLastAck{} T.TcpInSeg{True{}, False{}}:
      {==}
    case T.TcpLastAck{} T.TcpInSeg{False{}, True{}}:
      {==}
    case T.TcpLastAck{} T.TcpInSeg{False{}, False{}}:
      {==}
    case T.TcpLastAck{} T.TcpInGiveUp{}:
      {==}
    case T.TcpLastAck{} T.TcpInTimeWaitEnd{}:
      {==}
    case T.TcpTimeWait{} T.TcpInPassiveOpen{}:
      {==}
    case T.TcpTimeWait{} T.TcpInActiveOpen{}:
      {==}
    case T.TcpTimeWait{} T.TcpInClose{}:
      {==}
    case T.TcpTimeWait{} T.TcpInAbort{}:
      {==}
    case T.TcpTimeWait{} T.TcpInNone{}:
      {==}
    case T.TcpTimeWait{} T.TcpInReset{True{}}:
      {==}
    case T.TcpTimeWait{} T.TcpInReset{False{}}:
      {==}
    case T.TcpTimeWait{} T.TcpInSyn{}:
      {==}
    case T.TcpTimeWait{} T.TcpInSynAck{True{}}:
      {==}
    case T.TcpTimeWait{} T.TcpInSynAck{False{}}:
      {==}
    case T.TcpTimeWait{} T.TcpInSeg{True{}, True{}}:
      {==}
    case T.TcpTimeWait{} T.TcpInSeg{True{}, False{}}:
      {==}
    case T.TcpTimeWait{} T.TcpInSeg{False{}, True{}}:
      {==}
    case T.TcpTimeWait{} T.TcpInSeg{False{}, False{}}:
      {==}
    case T.TcpTimeWait{} T.TcpInGiveUp{}:
      {==}
    case T.TcpTimeWait{} T.TcpInTimeWaitEnd{}:
      {==}

def Laws.tcp_step_allowed(o, conn, ev, now, isn):
  match conn:
    case T.TcpConn{st, tcb, c}:
      tcp_next_allowed(st, T.TcpFx.input(CC.RenoState, T.Tcp.process(~CC.RenoState, ~CC.Reno.cc(), o, st, tcb, c, ev, now, isn)))


# Equality of 32-bit words is reflexive

def word_cmp_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, word_cmp_refl(p, t)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
          {==}
        case WCon{True{}, t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, word_cmp_refl(p, t)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
          {==}

def u32_eq_refl(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, word_cmp_refl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

def key_refl(k: D.DemuxKey) -> {D.DemuxKey.is_eq(k, k) == True{} : Bool}:
  match k:
    case D.DemuxKey{+p, +a, +r}:
      %Equal.sym(Bool, U32.is_eq(p, p), True{}, u32_eq_refl(p)) : {Bool.and(_, Bool.and(U32.is_eq(a, a), U32.is_eq(r, r))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(a, a), True{}, u32_eq_refl(a)) : {Bool.and(True{}, Bool.and(_, U32.is_eq(r, r))) == True{} : Bool}
      %Equal.sym(Bool, U32.is_eq(r, r), True{}, u32_eq_refl(r)) : {Bool.and(True{}, Bool.and(True{}, _)) == True{} : Bool}
      {==}

# The demultiplexer

def Laws.demux_find_insert(S, d, k, s):
  match d:
    case D.Demux{+xs}:
      +rest = D.Demux.remove.go(S, xs, k, D.Demux.head_is(S, xs, k))
      %Equal.sym(Bool, D.DemuxKey.is_eq(k, k), True{}, key_refl(k)) : {D.Demux.find.go(S, Con{D.DemuxEntry{k, s}, rest}, k, _) == Some{s} : Maybe<&2, S>}
      {==}

def remove_find(-S: Data, +xs: List<&2, D.DemuxEntry<S>>, +k: D.DemuxKey, +hit: Bool, e: {D.Demux.head_is(S, xs, k) == hit : Bool}) -> {D.Demux.find.go(S, D.Demux.remove.go(S, xs, k, hit), k, D.Demux.head_is(S, D.Demux.remove.go(S, xs, k, hit), k)) == None{} : Maybe<&2, S>}:
  match xs:
    case Nil{}:
      match hit:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{D.DemuxEntry{+ek, +s}, +t}:
      match hit:
        case True{}:
          remove_find(S, t, k, D.Demux.head_is(S, t, k), {==})
        case False{}:
          +r = D.Demux.remove.go(S, t, k, D.Demux.head_is(S, t, k))
          %Equal.sym(Bool, D.DemuxKey.is_eq(k, ek), False{}, e) : {D.Demux.find.go(S, Con{D.DemuxEntry{ek, s}, r}, k, _) == None{} : Maybe<&2, S>}
          remove_find(S, t, k, D.Demux.head_is(S, t, k), {==})

def Laws.demux_find_remove(S, d, k):
  match d:
    case D.Demux{+xs}:
      remove_find(S, xs, k, D.Demux.head_is(S, xs, k), {==})

def Laws.demux_route_exact(S, d, p, a, r, s):
  +k = {D.DemuxKey{p, a, r} : D.DemuxKey}
  %Equal.sym(Maybe<&2, S>, D.Demux.find(S, D.Demux.insert(S, d, k, s), k), Some{s}, Laws.demux_find_insert(S, d, k, s)) : {D.Demux.route.go(S, _, D.Demux.insert(S, d, k, s), k, p) == Some{D.DemuxHit{k, s}} : Maybe<&2, D.DemuxHit<S>>}
  {==}


# The retransmission timer

def u32_le_refl(a: U32) -> {U32.is_le(a, a) == True{} : Bool}:
  match a:
    case U32{w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, word_cmp_refl(32n, w)) : {Cmp.is_le(_) == True{} : Bool}
      {==}

# at_most(x, hi) is at most hi, whatever x
def at_most_le(+fits: Bool, +x: U32, +hi: U32, e: {U32.is_le(x, hi) == fits : Bool}) -> {U32.is_le(R.Rto.at_most.pick(fits, x, hi), hi) == True{} : Bool}:
  match fits:
    case True{}:
      e
    case False{}:
      u32_le_refl(hi)

def at_most_bounded(+x: U32, +hi: U32) -> {U32.is_le(R.Rto.at_most(x, hi), hi) == True{} : Bool}:
  at_most_le(U32.is_le(x, hi), x, hi, {==})

def double_bounded(+small: Bool, +x: U32, +hi: U32) -> {U32.is_le(R.Rto.double.pick(small, x, hi), hi) == True{} : Bool}:
  match small:
    case True{}:
      at_most_bounded(U32.add(x, x), hi)
    case False{}:
      u32_le_refl(hi)

def Laws.rto_backoff_bounded(p, r):
  match p r:
    case R.RtoParams{i, lo, +hi, g, a} R.Rto{s, v, +rto, k}:
      double_bounded(U32.is_lt(rto, 2147483648), rto, hi)

def Laws.rto_backoff_doubles(p, r, h1, h2):
  match p r:
    case R.RtoParams{i, lo, +hi, g, a} R.Rto{s, v, +rto, k}:
      %Equal.sym(Bool, U32.is_lt(rto, 2147483648), True{}, h1) : {R.Rto.double.pick(_, rto, hi) == U32.add(rto, rto) : U32}
      %Equal.sym(Bool, U32.is_le(U32.add(rto, rto), hi), True{}, h2) : {R.Rto.at_most.pick(_, U32.add(rto, rto), hi) == U32.add(rto, rto) : U32}
      {==}

def of_bounded(+p: R.RtoParams, +s: U32, +v: U32) -> {U32.is_le(R.Rto.current(R.Rto.of(p, s, v)), R.RtoParams.max(p)) == True{} : Bool}:
  match p:
    case R.RtoParams{i, +lo, +hi, +g, a}:
      at_most_bounded(R.Rto.at_least(U32.add(U32.shrn(s, 3n), R.Rto.max32(g, v)), lo), hi)

def sample_bounded(+sampled: Bool, +p: R.RtoParams, +s: U32, +v: U32, +rtt: U32) -> {U32.is_le(R.Rto.current(R.Rto.sample.go(sampled, p, s, v, rtt)), R.RtoParams.max(p)) == True{} : Bool}:
  match sampled:
    case False{}:
      of_bounded(p, U32.shln(rtt, 3n), U32.shl(rtt))
    case True{}:
      of_bounded(p, U32.add(U32.sub(s, U32.shrn(s, 3n)), rtt), U32.add(U32.sub(v, U32.shrn(v, 2n)), R.Rto.absdiff(U32.shrn(s, 3n), rtt)))

def Laws.rto_sample_bounded(p, r, rtt):
  match r:
    case R.Rto{s, v, rto, k}:
      sample_bounded(k, p, s, v, rtt)

def Laws.rto_vector_first():
  {==}

def Laws.rto_vector_unclamped():
  {==}

def Laws.rto_vector_second():
  {==}

def Laws.rto_vector_backoff():
  {==}

def Laws.rto_vector_backoff_32():
  {==}

# Equality of words, keys: Word.cmp answering EQ means the words are equal

def absurd.cmp(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Unit
    case _:
      Empty

def fin_eq_t(x: Bool, y: Bool, t: Cmp, h: {Cmp.is_eq(Word.cmp.fin(x, y, t)) == True{} : Bool}) -> {t == EQ{} : Cmp}:
  match t:
    case LT{}:
      Empty.absurd({LT{} == EQ{} : Cmp}, absurd.ft(h))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({GT{} == EQ{} : Cmp}, absurd.ft(h))

def fin_eq_xy(x: Bool, y: Bool, t: Cmp, h: {Cmp.is_eq(Word.cmp.fin(x, y, t)) == True{} : Bool}) -> {x == y : Bool}:
  match x y t:
    case False{} False{} LT{}:
      Empty.absurd({False{} == False{} : Bool}, absurd.ft(h))
    case False{} False{} EQ{}:
      {==}
    case False{} False{} GT{}:
      Empty.absurd({False{} == False{} : Bool}, absurd.ft(h))
    case False{} True{} LT{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(h))
    case False{} True{} EQ{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(h))
    case False{} True{} GT{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(h))
    case True{} False{} LT{}:
      Empty.absurd({True{} == False{} : Bool}, absurd.ft(h))
    case True{} False{} EQ{}:
      Empty.absurd({True{} == False{} : Bool}, absurd.ft(h))
    case True{} False{} GT{}:
      Empty.absurd({True{} == False{} : Bool}, absurd.ft(h))
    case True{} True{} LT{}:
      Empty.absurd({True{} == True{} : Bool}, absurd.ft(h))
    case True{} True{} EQ{}:
      {==}
    case True{} True{} GT{}:
      Empty.absurd({True{} == True{} : Bool}, absurd.ft(h))

def word_eq(n: Nat, a: Word(n), b: Word(n), +h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+(+p):
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          +ht = fin_eq_t(x, y, Word.cmp(p, at, bt), h)
          +hi = Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), Word.cmp(p, at, bt), EQ{}, ht)
          +ih = word_eq(p, at, bt, hi)
          +hxy = fin_eq_xy(x, y, Word.cmp(p, at, bt), h)
          %ih : {WCon{x, at} == WCon{y, _} : Word(1n+p)}
          %hxy : {WCon{x, at} == WCon{_, at} : Word(1n+p)}
          {==}

def u32_eq(a: U32, b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{x} U32{y}:
      Equal.cong(Word(32n), U32, w => U32{w}, x, y, word_eq(32n, x, y, h))

def and_l(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(h))

def and_r(a: Bool, b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, absurd.ft(h))

def key_eq(k1: D.DemuxKey, k2: D.DemuxKey, +h: {D.DemuxKey.is_eq(k1, k2) == True{} : Bool}) -> {k1 == k2 : D.DemuxKey}:
  match k1 k2:
    case D.DemuxKey{+p1, +a1, +r1} D.DemuxKey{+p2, +a2, +r2}:
      +ep = u32_eq(p1, p2, and_l(U32.is_eq(p1, p2), Bool.and(U32.is_eq(a1, a2), U32.is_eq(r1, r2)), h))
      +rest = and_r(U32.is_eq(p1, p2), Bool.and(U32.is_eq(a1, a2), U32.is_eq(r1, r2)), h)
      +ea = u32_eq(a1, a2, and_l(U32.is_eq(a1, a2), U32.is_eq(r1, r2), rest))
      +er = u32_eq(r1, r2, and_r(U32.is_eq(a1, a2), U32.is_eq(r1, r2), rest))
      %ep : {D.DemuxKey{p1, a1, r1} == D.DemuxKey{_, a2, r2} : D.DemuxKey}
      %ea : {D.DemuxKey{p1, a1, r1} == D.DemuxKey{p1, _, r2} : D.DemuxKey}
      %er : {D.DemuxKey{p1, a1, r1} == D.DemuxKey{p1, a1, _} : D.DemuxKey}
      {==}

# Another key's socket leaves a lookup alone

# hit True: the entry ek dropped is k2, so k1 (not k2) does not match it
def other_dropped(+k1: D.DemuxKey, +k2: D.DemuxKey, +ek: D.DemuxKey, e: {D.DemuxKey.is_eq(k2, ek) == True{} : Bool}, ne: {D.DemuxKey.is_eq(k1, k2) == False{} : Bool}) -> {D.DemuxKey.is_eq(k1, ek) == False{} : Bool}:
  %key_eq(k2, ek, e) : {D.DemuxKey.is_eq(k1, _) == False{} : Bool}
  ne

def other_kept(-S: Data, b: Bool, +ek: D.DemuxKey, +s: S, +r: List<&2, D.DemuxEntry<S>>, +t: List<&2, D.DemuxEntry<S>>, +k1: D.DemuxKey, ih: {D.Demux.find.go(S, r, k1, D.Demux.head_is(S, r, k1)) == D.Demux.find.go(S, t, k1, D.Demux.head_is(S, t, k1)) : Maybe<&2, S>}) -> {D.Demux.find.go(S, Con{D.DemuxEntry{ek, s}, r}, k1, b) == D.Demux.find.go(S, Con{D.DemuxEntry{ek, s}, t}, k1, b) : Maybe<&2, S>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def remove_find_other(-S: Data, +xs: List<&2, D.DemuxEntry<S>>, +k1: D.DemuxKey, +k2: D.DemuxKey, +hit: Bool, e: {D.Demux.head_is(S, xs, k2) == hit : Bool}, +ne: {D.DemuxKey.is_eq(k1, k2) == False{} : Bool}) -> {D.Demux.find.go(S, D.Demux.remove.go(S, xs, k2, hit), k1, D.Demux.head_is(S, D.Demux.remove.go(S, xs, k2, hit), k1)) == D.Demux.find.go(S, xs, k1, D.Demux.head_is(S, xs, k1)) : Maybe<&2, S>}:
  match xs:
    case Nil{}:
      match hit:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{D.DemuxEntry{+ek, +s}, +t}:
      match hit:
        case True{}:
          +ih = remove_find_other(S, t, k1, k2, D.Demux.head_is(S, t, k2), {==}, ne)
          %Equal.sym(Bool, D.DemuxKey.is_eq(k1, ek), False{}, other_dropped(k1, k2, ek, e, ne)) : {D.Demux.find.go(S, D.Demux.remove.go(S, t, k2, D.Demux.head_is(S, t, k2)), k1, D.Demux.head_is(S, D.Demux.remove.go(S, t, k2, D.Demux.head_is(S, t, k2)), k1)) == D.Demux.find.go(S, Con{D.DemuxEntry{ek, s}, t}, k1, _) : Maybe<&2, S>}
          ih
        case False{}:
          +r = D.Demux.remove.go(S, t, k2, D.Demux.head_is(S, t, k2))
          other_kept(S, D.DemuxKey.is_eq(k1, ek), ek, s, r, t, k1, remove_find_other(S, t, k1, k2, D.Demux.head_is(S, t, k2), {==}, ne))

def Laws.demux_find_insert_other(S, d, k1, k2, s, ne):
  match d:
    case D.Demux{+xs}:
      +r = D.Demux.remove.go(S, xs, k2, D.Demux.head_is(S, xs, k2))
      %Equal.sym(Bool, D.DemuxKey.is_eq(k1, k2), False{}, ne) : {D.Demux.find.go(S, Con{D.DemuxEntry{k2, s}, r}, k1, _) == D.Demux.find.go(S, xs, k1, D.Demux.head_is(S, xs, k1)) : Maybe<&2, S>}
      remove_find_other(S, xs, k1, k2, D.Demux.head_is(S, xs, k2), {==}, ne)

def Laws.demux_keys_differ():
  {==}

# UDP

def udp_route_bound(b: Bool, +d: D.Demux<U.UdpSock>, +p: U32, +tag: U32, +src: U32, +dst: U32, +sport: U32, +data: B.Octets, e: {D.DemuxKey.is_eq(D.DemuxKey{p, src, sport}, D.DemuxKey.any(p)) == b : Bool}, h2: {D.Demux.find(U.UdpSock, d, D.DemuxKey{p, src, sport}) == None{} : Maybe<&2, U.UdpSock>}) -> {U.Udp.deliver(D.Demux.route(U.UdpSock, D.Demux.insert(U.UdpSock, d, D.DemuxKey.any(p), U.UdpSock{tag}), p, src, sport), src, dst, sport, p, data) == [U.UdpDeliver{tag, src, sport, p, data}] : List<&2, U.UdpAction>}:
  match b:
    case True{}:
      +d2 = D.Demux.insert(U.UdpSock, d, D.DemuxKey.any(p), U.UdpSock{tag})
      +exact = {D.DemuxKey{p, src, sport} : D.DemuxKey}
      +ke = key_eq(exact, D.DemuxKey.any(p), e)
      %Equal.sym(D.DemuxKey, exact, D.DemuxKey.any(p), ke) : {U.Udp.deliver(D.Demux.route.go(U.UdpSock, D.Demux.find(U.UdpSock, d2, _), d2, _, p), src, dst, sport, p, data) == [U.UdpDeliver{tag, src, sport, p, data}] : List<&2, U.UdpAction>}
      %Equal.sym(Maybe<&2, U.UdpSock>, D.Demux.find(U.UdpSock, d2, D.DemuxKey.any(p)), Some{U.UdpSock{tag}}, Laws.demux_find_insert(U.UdpSock, d, D.DemuxKey.any(p), U.UdpSock{tag})) : {U.Udp.deliver(D.Demux.route.go(U.UdpSock, _, d2, D.DemuxKey.any(p), p), src, dst, sport, p, data) == [U.UdpDeliver{tag, src, sport, p, data}] : List<&2, U.UdpAction>}
      {==}
    case False{}:
      +d2 = D.Demux.insert(U.UdpSock, d, D.DemuxKey.any(p), U.UdpSock{tag})
      +exact = {D.DemuxKey{p, src, sport} : D.DemuxKey}
      +other = Laws.demux_find_insert_other(U.UdpSock, d, exact, D.DemuxKey.any(p), U.UdpSock{tag}, e)
      %Equal.sym(Maybe<&2, U.UdpSock>, D.Demux.find(U.UdpSock, d2, exact), D.Demux.find(U.UdpSock, d, exact), other) : {U.Udp.deliver(D.Demux.route.go(U.UdpSock, _, d2, exact, p), src, dst, sport, p, data) == [U.UdpDeliver{tag, src, sport, p, data}] : List<&2, U.UdpAction>}
      %Equal.sym(Maybe<&2, U.UdpSock>, D.Demux.find(U.UdpSock, d, exact), None{}, h2) : {U.Udp.deliver(D.Demux.route.go(U.UdpSock, _, d2, exact, p), src, dst, sport, p, data) == [U.UdpDeliver{tag, src, sport, p, data}] : List<&2, U.UdpAction>}
      %Equal.sym(Maybe<&2, U.UdpSock>, D.Demux.find(U.UdpSock, d2, D.DemuxKey.any(p)), Some{U.UdpSock{tag}}, Laws.demux_find_insert(U.UdpSock, d, D.DemuxKey.any(p), U.UdpSock{tag})) : {U.Udp.deliver(D.Demux.hit(U.UdpSock, D.DemuxKey.any(p), _), src, dst, sport, p, data) == [U.UdpDeliver{tag, src, sport, p, data}] : List<&2, U.UdpAction>}
      {==}

def Laws.udp_bound_delivers(a, d, p, tag, src, dst, sport, data, h1, h2):
  %Equal.sym(Maybe<&2, U.UdpSock>, D.Demux.find(U.UdpSock, d, D.DemuxKey.any(p)), None{}, h1) : {U.Udp.receive(Pair.fst(U.UdpState, List<&2, U.UdpAction>, U.Udp.bind.go(_, U.UdpState{a, d}, p, tag)), src, dst, sport, p, data) == [U.UdpDeliver{tag, src, sport, p, data}] : List<&2, U.UdpAction>}
  udp_route_bound(D.DemuxKey.is_eq(D.DemuxKey{p, src, sport}, D.DemuxKey.any(p)), d, p, tag, src, dst, sport, data, {==}, h2)

def Laws.udp_unbound_unreachable(a, d, src, dst, sport, dport, data, h1, h2):
  +exact = {D.DemuxKey{dport, src, sport} : D.DemuxKey}
  %Equal.sym(Maybe<&2, U.UdpSock>, D.Demux.find(U.UdpSock, d, exact), None{}, h1) : {U.Udp.deliver(D.Demux.route.go(U.UdpSock, _, d, exact, dport), src, dst, sport, dport, data) == [U.UdpNoPort{src, dst}] : List<&2, U.UdpAction>}
  %Equal.sym(Maybe<&2, U.UdpSock>, D.Demux.find(U.UdpSock, d, D.DemuxKey.any(dport)), None{}, h2) : {U.Udp.deliver(D.Demux.hit(U.UdpSock, D.DemuxKey.any(dport), _), src, dst, sport, dport, data) == [U.UdpNoPort{src, dst}] : List<&2, U.UdpAction>}
  {==}

def Laws.udp_hypotheses_hold():
  {==}

# ICMP

def Laws.icmp_echo_answered(id, seq, data):
  {==}

def Laws.icmp_reply_not_answered(id, seq, data):
  {==}

def Laws.icmp_unreachable_not_answered(code, q):
  {==}

def Laws.icmp_exceeded_not_answered(code, q):
  {==}

def Laws.icmp_vector_decode():
  {==}

def Laws.icmp_vector_answer():
  {==}

def Laws.icmp_vector_bad_checksum():
  {==}

# An ACK never acknowledges data that was not sent: through every stage of a
# step, SND.UNA stays, except in the acknowledgment step, where it moves to
# SEG.ACK only when SND.UNA < SEG.ACK =< SND.MAX

def absurd.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : absurd.bool(_)
  Unit{}

def or_r(x: Bool, y: Bool, e: {y == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      e

def ack_refl(+una0: U32, +max0: U32) -> {T.Tcp.acked_sent(una0, max0, una0) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(una0, una0), True{}, u32_eq_refl(una0)) : {Bool.or(_, Bool.and(S.SeqNum.lt(una0, una0), S.SeqNum.le(una0, max0))) == True{} : Bool}
  {==}

# SND.UNA unchanged: then the property holds
def ack_same(+una0: U32, +max0: U32, +t: T.TcpTcb, e: {T.TcpSnd.una(T.TcpTcb.snd(t)) == una0 : U32}) -> {T.Tcp.acked_sent(una0, max0, T.TcpSnd.una(T.TcpTcb.snd(t))) == True{} : Bool}:
  %Equal.sym(U32, T.TcpSnd.una(T.TcpTcb.snd(t)), una0, e) : {T.Tcp.acked_sent(una0, max0, _) == True{} : Bool}
  ack_refl(una0, max0)

# Sending moves SND.NXT and SND.MAX, never SND.UNA

def una_emit(+snd: T.TcpSnd, +rcv: T.TcpRcv, +o: T.TcpOptions, +now: U32, +n: Nat, +fin: Bool, +tim: T.TcpTim, +acts: List<&2, T.TcpAction>) -> {T.TcpSnd.una(T.TcpSent.snd(T.Tcp.emit(snd, rcv, o, now, n, fin, tim, acts))) == T.TcpSnd.una(snd) : U32}:
  match snd rcv:
    case T.TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, f} T.TcpRcv{irs, rn, q, u}:
      {==}

def una_outgo(fuel: Nat, +plan: T.TcpPlan, +o: T.TcpOptions, +rcv: T.TcpRcv, +now: U32, +cwnd: U32, +r: T.TcpSent) -> {T.TcpSnd.una(T.TcpSent.snd(T.Tcp.output.go(fuel, plan, o, rcv, now, cwnd, r))) == T.TcpSnd.una(T.TcpSent.snd(r)) : U32}:
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      match plan:
        case T.TcpPlan{go, +n, +fin}:
          match go:
            case False{}:
              {==}
            case True{}:
              match r:
                case T.TcpSent{+snd, +tim, +acts, sent}:
                  +r2 = T.Tcp.emit(snd, rcv, o, now, n, fin, tim, acts)
                  Equal.trans(U32, T.TcpSnd.una(T.TcpSent.snd(T.Tcp.output.go(f, T.Tcp.plan(o, T.TcpSent.snd(r2), cwnd), o, rcv, now, cwnd, r2))), T.TcpSnd.una(T.TcpSent.snd(r2)), T.TcpSnd.una(snd), una_outgo(f, T.Tcp.plan(o, T.TcpSent.snd(r2), cwnd), o, rcv, now, cwnd, r2), una_emit(snd, rcv, o, now, n, fin, tim, acts))

def una_output(+o: T.TcpOptions, +rcv: T.TcpRcv, +now: U32, +cwnd: U32, +snd: T.TcpSnd, +tim: T.TcpTim, +acts: List<&2, T.TcpAction>) -> {T.TcpSnd.una(T.TcpSent.snd(T.Tcp.output(o, rcv, now, cwnd, snd, tim, acts))) == T.TcpSnd.una(snd) : U32}:
  una_outgo(1n+T.Tcp.unsent(snd), T.Tcp.plan(o, snd, cwnd), o, rcv, now, cwnd, T.TcpSent{snd, tim, acts, False{}})

def una_out_done(+an: Bool, +p: Bool, +rcv: T.TcpRcv, +r: T.TcpSent) -> {T.TcpSnd.una(T.TcpTcb.snd(Pair.fst(T.TcpTcb, Pair(Bool, List<&2, T.TcpAction>), T.Tcp.fin.output.done(an, p, rcv, r)))) == T.TcpSnd.una(T.TcpSent.snd(r)) : U32}:
  match r:
    case T.TcpSent{snd, tim, acts, sent}:
      {==}

def una_fin_output(can: Bool, +o: T.TcpOptions, +now: U32, +cwnd: U32, +tcb: T.TcpTcb, +an: Bool, +acts: List<&2, T.TcpAction>) -> {T.TcpSnd.una(T.TcpTcb.snd(Pair.fst(T.TcpTcb, Pair(Bool, List<&2, T.TcpAction>), T.Tcp.fin.output(can, o, now, cwnd, tcb, an, acts)))) == T.TcpSnd.una(T.TcpTcb.snd(tcb)) : U32}:
  match can:
    case False{}:
      {==}
    case True{}:
      match tcb:
        case T.TcpTcb{+p, +snd, +rcv, +tim}:
          Equal.trans(U32, T.TcpSnd.una(T.TcpTcb.snd(Pair.fst(T.TcpTcb, Pair(Bool, List<&2, T.TcpAction>), T.Tcp.fin.output.done(an, p, rcv, T.Tcp.output(o, rcv, now, cwnd, snd, tim, acts))))), T.TcpSnd.una(T.TcpSent.snd(T.Tcp.output(o, rcv, now, cwnd, snd, tim, acts))), T.TcpSnd.una(snd), una_out_done(an, p, rcv, T.Tcp.output(o, rcv, now, cwnd, snd, tim, acts)), una_output(o, rcv, now, cwnd, snd, tim, acts))

# The timers, and entering a state, leave SND.UNA alone

def una_timers(tw: Bool, quiet: Bool, +o: T.TcpOptions, +now: U32, +tcb: T.TcpTcb) -> {T.TcpSnd.una(T.TcpTcb.snd(T.Tcp.fin.timers(tw, quiet, o, now, tcb))) == T.TcpSnd.una(T.TcpTcb.snd(tcb)) : U32}:
  match tw:
    case True{}:
      match tcb:
        case T.TcpTcb{p, s, r, m}:
          {==}
    case False{}:
      match quiet:
        case True{}:
          match tcb:
            case T.TcpTcb{p, s, r, m}:
              {==}
        case False{}:
          {==}

def una_rtx(timed: Bool, +now: U32, +cwnd: U32, +nw: Bool, +tcb: T.TcpTcb) -> {T.TcpSnd.una(T.TcpTcb.snd(T.Tcp.fin.rtx(timed, now, cwnd, nw, tcb))) == T.TcpSnd.una(T.TcpTcb.snd(tcb)) : U32}:
  match timed:
    case False{}:
      {==}
    case True{}:
      match tcb:
        case T.TcpTcb{p, s, r, m}:
          {==}

def una_enter(entered: Bool, +o: T.TcpOptions, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.TcpSnd.una(T.TcpTcb.snd(Pair.fst(T.TcpTcb, CC.RenoState, T.Tcp.fin.enter(~CC.RenoState, ~CC.Reno.cc(), entered, o, tcb, c)))) == T.TcpSnd.una(T.TcpTcb.snd(tcb)) : U32}:
  match entered:
    case False{}:
      {==}
    case True{}:
      match tcb:
        case T.TcpTcb{p, s, r, m}:
          match m:
            case T.TcpTim{rto, rtx, tw, retx, rtt, sl}:
              {==}

def una_finish_go(+st: T.TcpState, +st2: T.TcpState, +k: T.TcpInput, +entered: Bool, +o: T.TcpOptions, +now: U32, +cwnd: U32, +old: T.TcpTim, +nw: Bool, +tcb: T.TcpTcb, +c: CC.RenoState, r: Pair(T.TcpTcb, Pair(Bool, List<&2, T.TcpAction>))) -> {T.TcpSnd.una(T.TcpTcb.snd(T.TcpFx.tcb(CC.RenoState, T.Tcp.finish.go(CC.RenoState, st, st2, k, entered, o, now, cwnd, old, nw, tcb, c, r)))) == T.TcpSnd.una(T.TcpTcb.snd(Pair.fst(T.TcpTcb, Pair(Bool, List<&2, T.TcpAction>), r))) : U32}:
  match r:
    case (+tcb2, rest):
      match rest:
        case (an, acts):
          una_rtx(T.TcpState.timed(st2), now, cwnd, nw, tcb2)

def una_finish_cc(+st: T.TcpState, +st2: T.TcpState, +k: T.TcpInput, +entered: Bool, +o: T.TcpOptions, +now: U32, +old: T.TcpTim, +an: Bool, +nw: Bool, +acts: List<&2, T.TcpAction>, r: Pair(T.TcpTcb, CC.RenoState)) -> {T.TcpSnd.una(T.TcpTcb.snd(T.TcpFx.tcb(CC.RenoState, T.Tcp.finish.cc(~CC.RenoState, ~CC.Reno.cc(), st, st2, k, entered, o, now, old, an, nw, acts, r)))) == T.TcpSnd.una(T.TcpTcb.snd(Pair.fst(T.TcpTcb, CC.RenoState, r))) : U32}:
  match r:
    case (+tcb1, +c1):
      +tw = Bool.and(T.TcpState.is(st2, 10), Bool.or(Bool.not(T.TcpState.is(st, 10)), T.TcpInput.is_seg(k)))
      +quiet = Bool.or(T.TcpState.is(st2, 0), T.TcpState.is(st2, 1))
      +tcb2 = T.Tcp.fin.timers(tw, quiet, o, now, tcb1)
      +cwnd = T.Tcp.cc_cwnd(~CC.RenoState, ~CC.Reno.cc(), c1)
      +can = Bool.and(T.TcpState.can_send(st2), T.Tcp.syn_acked(T.TcpTcb.snd(tcb2)))
      fo = T.Tcp.fin.output(can, o, now, cwnd, tcb2, an, acts)
      +e1 = una_finish_go(st, st2, k, entered, o, now, cwnd, old, nw, tcb2, c1, fo)
      +e2 = una_fin_output(can, o, now, cwnd, tcb2, an, acts)
      +e3 = una_timers(tw, quiet, o, now, tcb1)
      Equal.trans(U32, T.TcpSnd.una(T.TcpTcb.snd(T.TcpFx.tcb(CC.RenoState, T.Tcp.finish.go(CC.RenoState, st, st2, k, entered, o, now, cwnd, old, nw, tcb2, c1, fo)))), T.TcpSnd.una(T.TcpTcb.snd(Pair.fst(T.TcpTcb, Pair(Bool, List<&2, T.TcpAction>), fo))), T.TcpSnd.una(T.TcpTcb.snd(tcb1)), e1, Equal.trans(U32, T.TcpSnd.una(T.TcpTcb.snd(Pair.fst(T.TcpTcb, Pair(Bool, List<&2, T.TcpAction>), fo))), T.TcpSnd.una(T.TcpTcb.snd(tcb2)), T.TcpSnd.una(T.TcpTcb.snd(tcb1)), e2, e3))

def una_finish(+st: T.TcpState, +o: T.TcpOptions, +now: U32, +old: T.TcpTim, +w: T.TcpW<CC.RenoState>) -> {T.TcpSnd.una(T.TcpTcb.snd(T.TcpFx.tcb(CC.RenoState, T.Tcp.finish(~CC.RenoState, ~CC.Reno.cc(), st, o, now, old, w)))) == T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, w))) : U32}:
  match w:
    case T.TcpW{go, +k, +tcb, +c, +acts, +an, +nw}:
      +st2 = T.Tcp.next_state(st, k)
      +entered = Bool.and(T.TcpState.opening(st), T.TcpState.est_like(st2))
      fe = T.Tcp.fin.enter(~CC.RenoState, ~CC.Reno.cc(), entered, o, tcb, c)
      Equal.trans(U32, T.TcpSnd.una(T.TcpTcb.snd(T.TcpFx.tcb(CC.RenoState, T.Tcp.finish.cc(~CC.RenoState, ~CC.Reno.cc(), st, st2, k, entered, o, now, old, an, nw, acts, fe)))), T.TcpSnd.una(T.TcpTcb.snd(Pair.fst(T.TcpTcb, CC.RenoState, fe))), T.TcpSnd.una(T.TcpTcb.snd(tcb)), una_finish_cc(st, st2, k, entered, o, now, old, an, nw, acts, fe), una_enter(entered, o, tcb, c))

# The acknowledgment step

def una_wnd_go(upd: Bool, +snd: T.TcpSnd, +sq: U32, +ack: U32, +sw: U32) -> {T.TcpSnd.una(T.Tcp.wnd_update.go(upd, snd, sq, ack, sw)) == T.TcpSnd.una(snd) : U32}:
  match upd:
    case False{}:
      {==}
    case True{}:
      match snd:
        case T.TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
          {==}

def una_wnd(inrange: Bool, +snd: T.TcpSnd, +sq: U32, +ack: U32, +sw: U32) -> {T.TcpSnd.una(T.Tcp.wnd_update(inrange, snd, sq, ack, sw)) == T.TcpSnd.una(snd) : U32}:
  match inrange:
    case False{}:
      {==}
    case True{}:
      match snd:
        case T.TcpSnd{iss, una, nxt, max, wnd, +wl1, +wl2, smss, buf, bseq, fin}:
          una_wnd_go(Bool.or(S.SeqNum.lt(wl1, sq), Bool.and(U32.is_eq(wl1, sq), S.SeqNum.le(wl2, ack))), T.TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}, sq, ack, sw)

def una_ack_fin(+inrange: Bool, +new: Bool, +seg: G.TcpSeg, +an: Bool, +acts: List<&2, T.TcpAction>, r: Pair(T.TcpTcb, CC.RenoState)) -> {T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.on_ack.fin(CC.RenoState, inrange, new, seg, an, acts, r)))) == T.TcpSnd.una(T.TcpTcb.snd(Pair.fst(T.TcpTcb, CC.RenoState, r))) : U32}:
  match r:
    case (t, c2):
      match t:
        case T.TcpTcb{p, +snd2, rcv2, tim2}:
          una_wnd(inrange, snd2, G.TcpSeg.seq(seg), G.TcpSeg.ack(seg), T.TcpSeg.wnd(seg))

# a new acknowledgment moves SND.UNA to SEG.ACK, which SND.UNA < SEG.ACK =<
# SND.MAX allows
def ack_new_ok(new: Bool, +o: T.TcpOptions, +now: U32, +ack: U32, +tcb: T.TcpTcb, +c: CC.RenoState, e: {T.Tcp.acks_new(T.TcpTcb.snd(tcb), ack) == new : Bool}) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(Pair.fst(T.TcpTcb, CC.RenoState, T.Tcp.on_new(~CC.RenoState, ~CC.Reno.cc(), new, o, now, ack, tcb, c))))) == True{} : Bool}:
  match new:
    case False{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case True{}:
      match tcb:
        case T.TcpTcb{p, snd, rcv, tim}:
          match snd:
            case T.TcpSnd{iss, +una, nxt, +max, wnd, wl1, wl2, smss, buf, bseq, fin}:
              or_r(U32.is_eq(ack, una), Bool.and(S.SeqNum.lt(una, ack), S.SeqNum.le(ack, max)), e)

def ack_dup_ok(+o: T.TcpOptions, +now: U32, +seg: G.TcpSeg, +tcb: T.TcpTcb, +an: Bool, r: Pair(CC.RenoState, List<&2, T.TcpAction>)) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.on_ack.dup(~CC.RenoState, ~CC.Reno.cc(), o, now, seg, tcb, an, r))))) == True{} : Bool}:
  match r:
    case (+c1, +acts1):
      +ack = G.TcpSeg.ack(seg)
      +snd = T.TcpTcb.snd(tcb)
      +new = T.Tcp.acks_new(snd, ack)
      +inrange = Bool.and(S.SeqNum.le(T.TcpSnd.una(snd), ack), S.SeqNum.le(ack, T.TcpSnd.max(snd)))
      rn = T.Tcp.on_new(~CC.RenoState, ~CC.Reno.cc(), new, o, now, ack, tcb, c1)
      %Equal.sym(U32, T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.on_ack.fin(CC.RenoState, inrange, new, seg, an, acts1, rn)))), T.TcpSnd.una(T.TcpTcb.snd(Pair.fst(T.TcpTcb, CC.RenoState, rn))), una_ack_fin(inrange, new, seg, an, acts1, rn)) : {T.Tcp.acked_sent(T.TcpSnd.una(snd), T.TcpSnd.max(snd), _) == True{} : Bool}
      ack_new_ok(new, o, now, ack, tcb, c1, {==})

def ack_go_ok(future: Bool, +o: T.TcpOptions, +now: U32, +seg: G.TcpSeg, +tcb: T.TcpTcb, +c: CC.RenoState, +acts: List<&2, T.TcpAction>, +an: Bool) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.on_ack.go(~CC.RenoState, ~CC.Reno.cc(), future, o, now, seg, tcb, c, acts, an))))) == True{} : Bool}:
  match future:
    case True{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case False{}:
      ack_dup_ok(o, now, seg, tcb, an, T.Tcp.on_dup(~CC.RenoState, ~CC.Reno.cc(), T.Tcp.is_dupack(T.TcpTcb.snd(tcb), seg), o, tcb, c, acts))

def ack_ok(+o: T.TcpOptions, +now: U32, +seg: G.TcpSeg, +w: T.TcpW<CC.RenoState>) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, w))), T.TcpSnd.max(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, w))), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.on_ack(~CC.RenoState, ~CC.Reno.cc(), o, now, seg, w))))) == True{} : Bool}:
  match w:
    case T.TcpW{go, k, +tcb, +c, +acts, +an, nw}:
      match go:
        case False{}:
          ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
        case True{}:
          ack_go_ok(S.SeqNum.lt(T.TcpSnd.max(T.TcpTcb.snd(tcb)), G.TcpSeg.ack(seg)), o, now, seg, tcb, c, acts, an)

# Data and FIN leave the send side alone

def snd_text_done(+synsent: Bool, +af: Bool, +p: Bool, +snd: T.TcpSnd, +tim: T.TcpTim, +c: CC.RenoState, +an: Bool, +nw: Bool, t: T.TcpText) -> {T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.on_text.done(CC.RenoState, synsent, af, p, snd, tim, c, an, nw, t))) == snd : T.TcpSnd}:
  match t:
    case T.TcpText{r, f, a}:
      {==}

def snd_text_go(takes: Bool, +synsent: Bool, +o: T.TcpOptions, +seg: G.TcpSeg, +tcb: T.TcpTcb, +c: CC.RenoState, +acts: List<&2, T.TcpAction>, +an: Bool, +nw: Bool) -> {T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.on_text.go(CC.RenoState, takes, synsent, o, seg, tcb, c, acts, an, nw))) == T.TcpTcb.snd(tcb) : T.TcpSnd}:
  match takes:
    case False{}:
      {==}
    case True{}:
      match tcb:
        case T.TcpTcb{+p, +snd, +rcv, +tim}:
          snd_text_done(synsent, T.Tcp.fin_acked(snd), p, snd, tim, c, Bool.or(an, Nat.is_gt(T.TcpSeg.dlen(seg), 0n)), nw, T.Tcp.text(o, seg, rcv, acts))

def snd_text(+takes: Bool, +synsent: Bool, +o: T.TcpOptions, +seg: G.TcpSeg, +w: T.TcpW<CC.RenoState>) -> {T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.on_text(CC.RenoState, takes, synsent, o, seg, w))) == T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, w)) : T.TcpSnd}:
  match w:
    case T.TcpW{go, k, +tcb, +c, +acts, +an, +nw}:
      match go:
        case False{}:
          {==}
        case True{}:
          snd_text_go(takes, synsent, o, seg, tcb, c, acts, an, nw)

# The checks before the acknowledgment step leave the send side alone

def snd_pick_tw(b: Bool, +tcb: T.TcpTcb, +m: T.TcpTim) -> {T.TcpTcb.snd(T.Tcp.pick(T.TcpTcb, b, T.TcpTcb.set_tim(tcb, m), tcb)) == T.TcpTcb.snd(tcb) : T.TcpSnd}:
  match b:
    case True{}:
      match tcb:
        case T.TcpTcb{p, s, r, x}:
          {==}
    case False{}:
      {==}


def snd_rst(exact: Bool, +tl: Bool, +o: T.TcpOptions, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.sync.rst(exact, CC.RenoState, tl, o, tcb, c, Nil{}))) == T.TcpTcb.snd(tcb) : T.TcpSnd}:
  match exact:
    case True{}:
      {==}
    case False{}:
      {==}

def snd_syn(back: Bool, +o: T.TcpOptions, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.sync.syn(back, CC.RenoState, o, tcb, c, Nil{}))) == T.TcpTcb.snd(tcb) : T.TcpSnd}:
  match back:
    case True{}:
      {==}
    case False{}:
      {==}

def snd_synrcvd(bad: Bool, +seg: G.TcpSeg, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.sync.synrcvd(bad, CC.RenoState, seg, tcb, c, Nil{}))) == T.TcpTcb.snd(tcb) : T.TcpSnd}:
  match bad:
    case True{}:
      {==}
    case False{}:
      {==}

def snd_checks(acc: Bool, rst: Bool, syn: Bool, ackf: Bool, +st: T.TcpState, +o: T.TcpOptions, +now: U32, +seg: G.TcpSeg, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.sync.checks(acc, rst, syn, ackf, CC.RenoState, st, o, now, seg, tcb, c))) == T.TcpTcb.snd(tcb) : T.TcpSnd}:
  match acc:
    case False{}:
      snd_pick_tw(Bool.and(T.TcpState.is(st, 10), G.TcpSeg.fin(seg)), tcb, T.TcpTim.set_tw(T.TcpTcb.tim(tcb), Some{U32.add(now, T.Tcp.opt.msl2(o))}))
    case True{}:
      match rst:
        case True{}:
          snd_rst(U32.is_eq(G.TcpSeg.seq(seg), T.TcpRcv.nxt(T.TcpTcb.rcv(tcb))), Bool.and(T.TcpState.is(st, 3), T.TcpTcb.passive(tcb)), o, tcb, c)
        case False{}:
          match syn:
            case True{}:
              snd_syn(Bool.and(T.TcpState.is(st, 3), T.TcpTcb.passive(tcb)), o, tcb, c)
            case False{}:
              match ackf:
                case False{}:
                  {==}
                case True{}:
                  snd_synrcvd(Bool.and(T.TcpState.is(st, 3), Bool.not(Bool.and(S.SeqNum.lt(T.TcpSnd.una(T.TcpTcb.snd(tcb)), G.TcpSeg.ack(seg)), S.SeqNum.le(G.TcpSeg.ack(seg), T.TcpSnd.max(T.TcpTcb.snd(tcb)))))), seg, tcb, c)

# Arrival in a synchronized state: the checks keep the send side, the
# acknowledgment step moves SND.UNA within what was sent, data and FIN keep it
def ack_sync_ok(+st: T.TcpState, +o: T.TcpOptions, +now: U32, +seg: G.TcpSeg, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.arrive.sync(~CC.RenoState, ~CC.Reno.cc(), st, o, now, seg, tcb, c))))) == True{} : Bool}:
  +rcv = T.TcpTcb.rcv(tcb)
  +acc = T.Tcp.acceptable(G.TcpSeg.len(seg), G.TcpSeg.seq(seg), T.TcpRcv.nxt(rcv), T.Tcp.rcv_wnd(o, rcv))
  +w = T.Tcp.sync.checks(acc, G.TcpSeg.rst(seg), G.TcpSeg.syn(seg), G.TcpSeg.is_ack(seg), CC.RenoState, st, o, now, seg, tcb, c)
  +wa = T.Tcp.on_ack(~CC.RenoState, ~CC.Reno.cc(), o, now, seg, w)
  +e1 = snd_text(T.TcpState.takes_text(st), False{}, o, seg, wa)
  +e2 = snd_checks(acc, G.TcpSeg.rst(seg), G.TcpSeg.syn(seg), G.TcpSeg.is_ack(seg), st, o, now, seg, tcb, c)
  %Equal.sym(T.TcpSnd, T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.on_text(CC.RenoState, T.TcpState.takes_text(st), False{}, o, seg, wa))), T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, wa)), e1) : {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(_)) == True{} : Bool}
  %e2 : {T.Tcp.acked_sent(T.TcpSnd.una(_), T.TcpSnd.max(_), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, wa)))) == True{} : Bool}
  ack_ok(o, now, seg, w)

# Arrival in SYN-SENT

def una_ss_tcb(+o: T.TcpOptions, +seg: G.TcpSeg, +tcb: T.TcpTcb) -> {T.TcpSnd.una(T.TcpTcb.snd(T.Tcp.synsent.tcb(o, seg, tcb))) == T.TcpSnd.una(T.TcpTcb.snd(tcb)) : U32}:
  match tcb:
    case T.TcpTcb{p, snd, rcv, tim}:
      match snd:
        case T.TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
          {==}

def max_ss_tcb(+o: T.TcpOptions, +seg: G.TcpSeg, +tcb: T.TcpTcb) -> {T.TcpSnd.max(T.TcpTcb.snd(T.Tcp.synsent.tcb(o, seg, tcb))) == T.TcpSnd.max(T.TcpTcb.snd(tcb)) : U32}:
  match tcb:
    case T.TcpTcb{p, snd, rcv, tim}:
      match snd:
        case T.TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
          {==}

def ack_ss_syn(ackf: Bool, +o: T.TcpOptions, +now: U32, +seg: G.TcpSeg, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.synsent.syn(~CC.RenoState, ~CC.Reno.cc(), ackf, o, now, seg, T.Tcp.synsent.tcb(o, seg, tcb), c))))) == True{} : Bool}:
  match ackf:
    case False{}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.Tcp.synsent.tcb(o, seg, tcb), una_ss_tcb(o, seg, tcb))
    case True{}:
      +t2 = T.Tcp.synsent.tcb(o, seg, tcb)
      +eu = una_ss_tcb(o, seg, tcb)
      +em = max_ss_tcb(o, seg, tcb)
      +w = {T.TcpW{True{}, T.TcpInNone{}, t2, c, Nil{}, True{}, False{}} : T.TcpW<CC.RenoState>}
      +wa = T.Tcp.on_ack(~CC.RenoState, ~CC.Reno.cc(), o, now, seg, w)
      %Equal.sym(T.TcpSnd, T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.on_text(CC.RenoState, True{}, True{}, o, seg, wa))), T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, wa)), snd_text(True{}, True{}, o, seg, wa)) : {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(_)) == True{} : Bool}
      %eu : {T.Tcp.acked_sent(_, T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, wa)))) == True{} : Bool}
      %em : {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(t2)), _, T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, wa)))) == True{} : Bool}
      ack_ok(o, now, seg, w)

def ack_ss_go(bad: Bool, rst: Bool, syn: Bool, +ackf: Bool, +o: T.TcpOptions, +now: U32, +seg: G.TcpSeg, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.synsent.go(~CC.RenoState, ~CC.Reno.cc(), bad, rst, syn, ackf, o, now, seg, tcb, c))))) == True{} : Bool}:
  match bad:
    case True{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case False{}:
      match rst:
        case True{}:
          ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
        case False{}:
          match syn:
            case False{}:
              ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
            case True{}:
              ack_ss_syn(ackf, o, now, seg, tcb, c)

def ack_ss_ok(+o: T.TcpOptions, +now: U32, +seg: G.TcpSeg, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.arrive.synsent(~CC.RenoState, ~CC.Reno.cc(), o, now, seg, tcb, c))))) == True{} : Bool}:
  +snd = T.TcpTcb.snd(tcb)
  +ack = G.TcpSeg.ack(seg)
  +ackf = G.TcpSeg.is_ack(seg)
  +ack_ok = Bool.and(S.SeqNum.lt(T.TcpSnd.iss(snd), ack), S.SeqNum.le(ack, T.TcpSnd.max(snd)))
  ack_ss_go(Bool.and(ackf, Bool.not(ack_ok)), G.TcpSeg.rst(seg), G.TcpSeg.syn(seg), ackf, o, now, seg, tcb, c)

# Calls and timers keep SND.UNA

def una_queue(+o: T.TcpOptions, +data: B.Octets, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.call.queue(CC.RenoState, o, data, tcb, c)))) == T.TcpSnd.una(T.TcpTcb.snd(tcb)) : U32}:
  match tcb:
    case T.TcpTcb{p, snd, r, m}:
      match snd:
        case T.TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
          {==}

def una_read(+o: T.TcpOptions, +n: U32, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.call.read(True{}, CC.RenoState, o, n, tcb, c)))) == T.TcpSnd.una(T.TcpTcb.snd(tcb)) : U32}:
  match tcb:
    case T.TcpTcb{p, s, r, m}:
      match r:
        case T.TcpRcv{irs, rn, q, u}:
          {==}

def una_fin(+tcb: T.TcpTcb, +c: CC.RenoState) -> {T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.call.fin(CC.RenoState, tcb, c)))) == T.TcpSnd.una(T.TcpTcb.snd(tcb)) : U32}:
  match tcb:
    case T.TcpTcb{p, snd, r, m}:
      match snd:
        case T.TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
          {==}

def una_rsyn(g: Bool, +st: T.TcpState, +o: T.TcpOptions, +now: U32, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.rtx.syn(g, CC.RenoState, st, o, now, tcb, c)))) == T.TcpSnd.una(T.TcpTcb.snd(tcb)) : U32}:
  match g:
    case True{}:
      {==}
    case False{}:
      match tcb:
        case T.TcpTcb{p, s, r, m}:
          {==}

def una_rdata(g: Bool, +o: T.TcpOptions, +now: U32, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.rtx.data(~CC.RenoState, ~CC.Reno.cc(), g, o, now, tcb, c)))) == T.TcpSnd.una(T.TcpTcb.snd(tcb)) : U32}:
  match g:
    case True{}:
      {==}
    case False{}:
      match tcb:
        case T.TcpTcb{p, snd, r, m}:
          match snd:
            case T.TcpSnd{iss, una, nxt, max, wnd, wl1, wl2, smss, buf, bseq, fin}:
              {==}

def una_probe(+tim: T.TcpTim, +o: T.TcpOptions, +rcv: T.TcpRcv, +now: U32, +snd: T.TcpSnd, +acts: List<&2, T.TcpAction>) -> {T.TcpSnd.una(T.TcpSent.snd(T.Tcp.probe(tim, o, rcv, now, snd, acts))) == T.TcpSnd.una(snd) : U32}:
  match tim:
    case T.TcpTim{rto, rtx, tw, retx, rtt, sl}:
      una_emit(snd, rcv, o, now, 1n, False{}, T.TcpTim{rto, rtx, tw, retx, None{}, sl}, acts)

def una_probed(+p: Bool, +rcv: T.TcpRcv, +c: CC.RenoState, +r: T.TcpSent) -> {T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.rtx.probed(CC.RenoState, p, rcv, c, r)))) == T.TcpSnd.una(T.TcpSent.snd(r)) : U32}:
  match r:
    case T.TcpSent{s, t, a, x}:
      {==}

def una_rprobe(pr: Bool, +o: T.TcpOptions, +now: U32, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.rtx.probe(pr, CC.RenoState, o, now, tcb, c)))) == T.TcpSnd.una(T.TcpTcb.snd(tcb)) : U32}:
  match pr:
    case False{}:
      match tcb:
        case T.TcpTcb{p, s, r, m}:
          {==}
    case True{}:
      match tcb:
        case T.TcpTcb{+p, +snd, +rcv, +tim}:
          +pt = T.Tcp.probe(T.Tcp.backed_off(o, now, False{}, tim), o, rcv, now, snd, Nil{})
          Equal.trans(U32, T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.rtx.probed(CC.RenoState, p, rcv, c, pt)))), T.TcpSnd.una(T.TcpSent.snd(pt)), T.TcpSnd.una(snd), una_probed(p, rcv, c, pt), una_probe(T.Tcp.backed_off(o, now, False{}, tim), o, rcv, now, snd, Nil{}))

def una_which(sd: Bool, out: Bool, +st: T.TcpState, +o: T.TcpOptions, +now: U32, +retx: U32, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.rtx.which(~CC.RenoState, ~CC.Reno.cc(), sd, out, st, o, now, retx, tcb, c)))) == T.TcpSnd.una(T.TcpTcb.snd(tcb)) : U32}:
  match sd:
    case False{}:
      una_rsyn(U32.is_ge(retx, T.Tcp.retries(True{}, o)), st, o, now, tcb, c)
    case True{}:
      match out:
        case True{}:
          una_rdata(U32.is_ge(retx, T.Tcp.retries(False{}, o)), o, now, tcb, c)
        case False{}:
          una_rprobe(Bool.and(Nat.is_gt(T.Tcp.unsent(T.TcpTcb.snd(tcb)), 0n), U32.is_lt(retx, T.Tcp.retries(False{}, o))), o, now, tcb, c)

def una_rfire(due: Bool, +st: T.TcpState, +o: T.TcpOptions, +now: U32, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.rtx.fire(~CC.RenoState, ~CC.Reno.cc(), due, st, o, now, tcb, c)))) == T.TcpSnd.una(T.TcpTcb.snd(tcb)) : U32}:
  match due:
    case False{}:
      {==}
    case True{}:
      una_which(T.Tcp.syn_acked(T.TcpTcb.snd(tcb)), T.Tcp.outstanding(T.TcpTcb.snd(tcb)), st, o, now, T.TcpTim.retx(T.TcpTcb.tim(tcb)), tcb, c)

def una_fire(t: T.TcpTimer, +st: T.TcpState, +o: T.TcpOptions, +now: U32, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.fire(~CC.RenoState, ~CC.Reno.cc(), t, st, o, now, tcb, c)))) == T.TcpSnd.una(T.TcpTcb.snd(tcb)) : U32}:
  match t:
    case T.TcpTimerRtx{}:
      una_rfire(T.Tcp.due(now, T.TcpTim.rtx_at(T.TcpTcb.tim(tcb))), st, o, now, tcb, c)
    case T.TcpTimerTimeWait{}:
      {==}

# Every event, in every state but CLOSED and LISTEN (where an open sets up
# a new send side)
def ack_disp.TcpSynSent(ev: T.TcpEvent, +o: T.TcpOptions, +now: U32, +isn: U32, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpSynSent{}, o, now, isn, tcb, c))))) == True{} : Bool}:
  match ev:
    case T.TcpCallOpen{a}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallSend{+d}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.call.queue(CC.RenoState, o, d, tcb, c)), una_queue(o, d, tcb, c))
    case T.TcpCallRead{+n}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallClose{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallAbort{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpArrive{+seg}:
      ack_ss_ok(o, now, seg, tcb, c)
    case T.TcpFire{+t}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.fire(~CC.RenoState, ~CC.Reno.cc(), t, T.TcpSynSent{}, o, now, tcb, c)), una_fire(t, T.TcpSynSent{}, o, now, tcb, c))

def ack_disp.TcpSynReceived(ev: T.TcpEvent, +o: T.TcpOptions, +now: U32, +isn: U32, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpSynReceived{}, o, now, isn, tcb, c))))) == True{} : Bool}:
  match ev:
    case T.TcpCallOpen{a}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallSend{+d}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.call.queue(CC.RenoState, o, d, tcb, c)), una_queue(o, d, tcb, c))
    case T.TcpCallRead{+n}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.call.read(True{}, CC.RenoState, o, n, tcb, c)), una_read(o, n, tcb, c))
    case T.TcpCallClose{}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.call.fin(CC.RenoState, tcb, c)), una_fin(tcb, c))
    case T.TcpCallAbort{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpArrive{+seg}:
      ack_sync_ok(T.TcpSynReceived{}, o, now, seg, tcb, c)
    case T.TcpFire{+t}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.fire(~CC.RenoState, ~CC.Reno.cc(), t, T.TcpSynReceived{}, o, now, tcb, c)), una_fire(t, T.TcpSynReceived{}, o, now, tcb, c))

def ack_disp.TcpEstablished(ev: T.TcpEvent, +o: T.TcpOptions, +now: U32, +isn: U32, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpEstablished{}, o, now, isn, tcb, c))))) == True{} : Bool}:
  match ev:
    case T.TcpCallOpen{a}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallSend{+d}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.call.queue(CC.RenoState, o, d, tcb, c)), una_queue(o, d, tcb, c))
    case T.TcpCallRead{+n}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.call.read(True{}, CC.RenoState, o, n, tcb, c)), una_read(o, n, tcb, c))
    case T.TcpCallClose{}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.call.fin(CC.RenoState, tcb, c)), una_fin(tcb, c))
    case T.TcpCallAbort{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpArrive{+seg}:
      ack_sync_ok(T.TcpEstablished{}, o, now, seg, tcb, c)
    case T.TcpFire{+t}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.fire(~CC.RenoState, ~CC.Reno.cc(), t, T.TcpEstablished{}, o, now, tcb, c)), una_fire(t, T.TcpEstablished{}, o, now, tcb, c))

def ack_disp.TcpFinWait1(ev: T.TcpEvent, +o: T.TcpOptions, +now: U32, +isn: U32, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpFinWait1{}, o, now, isn, tcb, c))))) == True{} : Bool}:
  match ev:
    case T.TcpCallOpen{a}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallSend{+d}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallRead{+n}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.call.read(True{}, CC.RenoState, o, n, tcb, c)), una_read(o, n, tcb, c))
    case T.TcpCallClose{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallAbort{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpArrive{+seg}:
      ack_sync_ok(T.TcpFinWait1{}, o, now, seg, tcb, c)
    case T.TcpFire{+t}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.fire(~CC.RenoState, ~CC.Reno.cc(), t, T.TcpFinWait1{}, o, now, tcb, c)), una_fire(t, T.TcpFinWait1{}, o, now, tcb, c))

def ack_disp.TcpFinWait2(ev: T.TcpEvent, +o: T.TcpOptions, +now: U32, +isn: U32, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpFinWait2{}, o, now, isn, tcb, c))))) == True{} : Bool}:
  match ev:
    case T.TcpCallOpen{a}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallSend{+d}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallRead{+n}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.call.read(True{}, CC.RenoState, o, n, tcb, c)), una_read(o, n, tcb, c))
    case T.TcpCallClose{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallAbort{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpArrive{+seg}:
      ack_sync_ok(T.TcpFinWait2{}, o, now, seg, tcb, c)
    case T.TcpFire{+t}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.fire(~CC.RenoState, ~CC.Reno.cc(), t, T.TcpFinWait2{}, o, now, tcb, c)), una_fire(t, T.TcpFinWait2{}, o, now, tcb, c))

def ack_disp.TcpCloseWait(ev: T.TcpEvent, +o: T.TcpOptions, +now: U32, +isn: U32, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpCloseWait{}, o, now, isn, tcb, c))))) == True{} : Bool}:
  match ev:
    case T.TcpCallOpen{a}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallSend{+d}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.call.queue(CC.RenoState, o, d, tcb, c)), una_queue(o, d, tcb, c))
    case T.TcpCallRead{+n}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.call.read(True{}, CC.RenoState, o, n, tcb, c)), una_read(o, n, tcb, c))
    case T.TcpCallClose{}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.call.fin(CC.RenoState, tcb, c)), una_fin(tcb, c))
    case T.TcpCallAbort{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpArrive{+seg}:
      ack_sync_ok(T.TcpCloseWait{}, o, now, seg, tcb, c)
    case T.TcpFire{+t}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.fire(~CC.RenoState, ~CC.Reno.cc(), t, T.TcpCloseWait{}, o, now, tcb, c)), una_fire(t, T.TcpCloseWait{}, o, now, tcb, c))

def ack_disp.TcpClosing(ev: T.TcpEvent, +o: T.TcpOptions, +now: U32, +isn: U32, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpClosing{}, o, now, isn, tcb, c))))) == True{} : Bool}:
  match ev:
    case T.TcpCallOpen{a}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallSend{+d}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallRead{+n}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.call.read(True{}, CC.RenoState, o, n, tcb, c)), una_read(o, n, tcb, c))
    case T.TcpCallClose{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallAbort{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpArrive{+seg}:
      ack_sync_ok(T.TcpClosing{}, o, now, seg, tcb, c)
    case T.TcpFire{+t}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.fire(~CC.RenoState, ~CC.Reno.cc(), t, T.TcpClosing{}, o, now, tcb, c)), una_fire(t, T.TcpClosing{}, o, now, tcb, c))

def ack_disp.TcpLastAck(ev: T.TcpEvent, +o: T.TcpOptions, +now: U32, +isn: U32, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpLastAck{}, o, now, isn, tcb, c))))) == True{} : Bool}:
  match ev:
    case T.TcpCallOpen{a}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallSend{+d}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallRead{+n}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.call.read(True{}, CC.RenoState, o, n, tcb, c)), una_read(o, n, tcb, c))
    case T.TcpCallClose{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallAbort{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpArrive{+seg}:
      ack_sync_ok(T.TcpLastAck{}, o, now, seg, tcb, c)
    case T.TcpFire{+t}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.fire(~CC.RenoState, ~CC.Reno.cc(), t, T.TcpLastAck{}, o, now, tcb, c)), una_fire(t, T.TcpLastAck{}, o, now, tcb, c))

def ack_disp.TcpTimeWait(ev: T.TcpEvent, +o: T.TcpOptions, +now: U32, +isn: U32, +tcb: T.TcpTcb, +c: CC.RenoState) -> {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpTimeWait{}, o, now, isn, tcb, c))))) == True{} : Bool}:
  match ev:
    case T.TcpCallOpen{a}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallSend{+d}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallRead{+n}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.call.read(True{}, CC.RenoState, o, n, tcb, c)), una_read(o, n, tcb, c))
    case T.TcpCallClose{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpCallAbort{}:
      ack_refl(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)))
    case T.TcpArrive{+seg}:
      ack_sync_ok(T.TcpTimeWait{}, o, now, seg, tcb, c)
    case T.TcpFire{+t}:
      ack_same(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpW.tcb(CC.RenoState, T.Tcp.fire(~CC.RenoState, ~CC.Reno.cc(), t, T.TcpTimeWait{}, o, now, tcb, c)), una_fire(t, T.TcpTimeWait{}, o, now, tcb, c))

def Laws.tcp_acks_only_sent(o, conn, ev, now, isn, h):
  match conn:
    case T.TcpConn{st, +tcb, +c}:
      match st:
        case T.TcpClosed{}:
          Empty.absurd({T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpConn.una(CC.RenoState, Pair.fst(T.TcpConn<CC.RenoState>, List<&2, T.TcpAction>, T.Tcp.step(~CC.RenoState, ~CC.Reno.cc(), o, T.TcpConn{T.TcpClosed{}, tcb, c}, ev, now, isn)))) == True{} : Bool}, absurd.tf(h))
        case T.TcpListen{}:
          Empty.absurd({T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), T.TcpConn.una(CC.RenoState, Pair.fst(T.TcpConn<CC.RenoState>, List<&2, T.TcpAction>, T.Tcp.step(~CC.RenoState, ~CC.Reno.cc(), o, T.TcpConn{T.TcpListen{}, tcb, c}, ev, now, isn)))) == True{} : Bool}, absurd.tf(h))
        case T.TcpSynSent{}:
          %Equal.sym(U32, T.TcpSnd.una(T.TcpTcb.snd(T.TcpFx.tcb(CC.RenoState, T.Tcp.finish(~CC.RenoState, ~CC.Reno.cc(), T.TcpSynSent{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpSynSent{}, o, now, isn, tcb, c))))), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpSynSent{}, o, now, isn, tcb, c)))), una_finish(T.TcpSynSent{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpSynSent{}, o, now, isn, tcb, c))) : {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), _) == True{} : Bool}
          ack_disp.TcpSynSent(ev, o, now, isn, tcb, c)
        case T.TcpSynReceived{}:
          %Equal.sym(U32, T.TcpSnd.una(T.TcpTcb.snd(T.TcpFx.tcb(CC.RenoState, T.Tcp.finish(~CC.RenoState, ~CC.Reno.cc(), T.TcpSynReceived{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpSynReceived{}, o, now, isn, tcb, c))))), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpSynReceived{}, o, now, isn, tcb, c)))), una_finish(T.TcpSynReceived{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpSynReceived{}, o, now, isn, tcb, c))) : {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), _) == True{} : Bool}
          ack_disp.TcpSynReceived(ev, o, now, isn, tcb, c)
        case T.TcpEstablished{}:
          %Equal.sym(U32, T.TcpSnd.una(T.TcpTcb.snd(T.TcpFx.tcb(CC.RenoState, T.Tcp.finish(~CC.RenoState, ~CC.Reno.cc(), T.TcpEstablished{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpEstablished{}, o, now, isn, tcb, c))))), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpEstablished{}, o, now, isn, tcb, c)))), una_finish(T.TcpEstablished{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpEstablished{}, o, now, isn, tcb, c))) : {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), _) == True{} : Bool}
          ack_disp.TcpEstablished(ev, o, now, isn, tcb, c)
        case T.TcpFinWait1{}:
          %Equal.sym(U32, T.TcpSnd.una(T.TcpTcb.snd(T.TcpFx.tcb(CC.RenoState, T.Tcp.finish(~CC.RenoState, ~CC.Reno.cc(), T.TcpFinWait1{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpFinWait1{}, o, now, isn, tcb, c))))), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpFinWait1{}, o, now, isn, tcb, c)))), una_finish(T.TcpFinWait1{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpFinWait1{}, o, now, isn, tcb, c))) : {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), _) == True{} : Bool}
          ack_disp.TcpFinWait1(ev, o, now, isn, tcb, c)
        case T.TcpFinWait2{}:
          %Equal.sym(U32, T.TcpSnd.una(T.TcpTcb.snd(T.TcpFx.tcb(CC.RenoState, T.Tcp.finish(~CC.RenoState, ~CC.Reno.cc(), T.TcpFinWait2{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpFinWait2{}, o, now, isn, tcb, c))))), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpFinWait2{}, o, now, isn, tcb, c)))), una_finish(T.TcpFinWait2{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpFinWait2{}, o, now, isn, tcb, c))) : {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), _) == True{} : Bool}
          ack_disp.TcpFinWait2(ev, o, now, isn, tcb, c)
        case T.TcpCloseWait{}:
          %Equal.sym(U32, T.TcpSnd.una(T.TcpTcb.snd(T.TcpFx.tcb(CC.RenoState, T.Tcp.finish(~CC.RenoState, ~CC.Reno.cc(), T.TcpCloseWait{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpCloseWait{}, o, now, isn, tcb, c))))), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpCloseWait{}, o, now, isn, tcb, c)))), una_finish(T.TcpCloseWait{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpCloseWait{}, o, now, isn, tcb, c))) : {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), _) == True{} : Bool}
          ack_disp.TcpCloseWait(ev, o, now, isn, tcb, c)
        case T.TcpClosing{}:
          %Equal.sym(U32, T.TcpSnd.una(T.TcpTcb.snd(T.TcpFx.tcb(CC.RenoState, T.Tcp.finish(~CC.RenoState, ~CC.Reno.cc(), T.TcpClosing{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpClosing{}, o, now, isn, tcb, c))))), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpClosing{}, o, now, isn, tcb, c)))), una_finish(T.TcpClosing{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpClosing{}, o, now, isn, tcb, c))) : {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), _) == True{} : Bool}
          ack_disp.TcpClosing(ev, o, now, isn, tcb, c)
        case T.TcpLastAck{}:
          %Equal.sym(U32, T.TcpSnd.una(T.TcpTcb.snd(T.TcpFx.tcb(CC.RenoState, T.Tcp.finish(~CC.RenoState, ~CC.Reno.cc(), T.TcpLastAck{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpLastAck{}, o, now, isn, tcb, c))))), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpLastAck{}, o, now, isn, tcb, c)))), una_finish(T.TcpLastAck{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpLastAck{}, o, now, isn, tcb, c))) : {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), _) == True{} : Bool}
          ack_disp.TcpLastAck(ev, o, now, isn, tcb, c)
        case T.TcpTimeWait{}:
          %Equal.sym(U32, T.TcpSnd.una(T.TcpTcb.snd(T.TcpFx.tcb(CC.RenoState, T.Tcp.finish(~CC.RenoState, ~CC.Reno.cc(), T.TcpTimeWait{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpTimeWait{}, o, now, isn, tcb, c))))), T.TcpSnd.una(T.TcpTcb.snd(T.TcpW.tcb(CC.RenoState, T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpTimeWait{}, o, now, isn, tcb, c)))), una_finish(T.TcpTimeWait{}, o, now, T.TcpTcb.tim(tcb), T.Tcp.dispatch(~CC.RenoState, ~CC.Reno.cc(), ev, T.TcpTimeWait{}, o, now, isn, tcb, c))) : {T.Tcp.acked_sent(T.TcpSnd.una(T.TcpTcb.snd(tcb)), T.TcpSnd.max(T.TcpTcb.snd(tcb)), _) == True{} : Bool}
          ack_disp.TcpTimeWait(ev, o, now, isn, tcb, c)

def Laws.seq_lt_asym_sat():
  {==}

def Laws.seq_lt_trans_sat():
  {==}

def Laws.rto_backoff_doubles_sat():
  {==}

def Laws.udp_sat():
  {==}

def Laws.tcp_acks_only_sent_sat():
  {==}


# Totality: any two sequence numbers are ordered one way or the other, equal,
# or exactly 2^31 apart

# whether every bit below the top is one
def low1.go(p: Nat, b: Bool, t: Word(p)) -> Bool:
  match p:
    case 0n:
      True{}
    case 1n+q:
      match t:
        case WCon{h, r}:
          Bool.and(b, low1.go(q, h, r))

def low1(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          low1.go(p, b, t)

def bpick(c: Bool, x: Bool, y: Bool) -> Bool:
  match c:
    case True{}:
      x
    case False{}:
      y

# the bits below the top of 0 - x - (1 - c): zero when x's are and c is set,
# or when x's are all ones and c is clear
def w_neg_low0(n: Nat, x: Word(1n+n), c: Bool) -> {S.SeqNum.word.low0(1n+n, Word.adc(1n+n, Word.zero(1n+n), x, True{}, c)) == bpick(c, S.SeqNum.word.low0(1n+n, x), low1(1n+n, x)) : Bool}:
  match n:
    case 0n:
      match x c:
        case WCon{x0, xt} True{}:
          {==}
        case WCon{x0, xt} False{}:
          {==}
    case 1n+p:
      match x c:
        case WCon{False{}, WCon{x1, xr}} True{}:
          w_neg_low0(p, WCon{x1, xr}, True{})
        case WCon{True{}, WCon{x1, xr}} True{}:
          {==}
        case WCon{False{}, WCon{x1, xr}} False{}:
          {==}
        case WCon{True{}, WCon{x1, xr}} False{}:
          w_neg_low0(p, WCon{x1, xr}, False{})

def and_true_l(a: Bool, b: Bool, h: {Bool.and(Bool.not(a), b) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, absurd.ft(h))

def and_true_r(a: Bool, b: Bool, h: {Bool.and(Bool.not(a), b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case False{}:
      h
    case True{}:
      Empty.absurd({b == True{} : Bool}, absurd.ft(h))

# a word whose top bit is clear and whose other bits are zero is zero
def w_zero_of(n: Nat, w: Word(1n+n), et: {S.SeqNum.word.top(1n+n, w) == False{} : Bool}, +el: {S.SeqNum.word.low0(1n+n, w) == True{} : Bool}) -> {w == Word.zero(1n+n) : Word(1n+n)}:
  match n:
    case 0n:
      match w:
        case WCon{False{}, WNil{}}:
          {==}
        case WCon{True{}, WNil{}}:
          Empty.absurd({WCon{True{}, WNil{}} == Word.zero(1n) : Word(1n)}, absurd.tf(et))
    case 1n+(+p):
      match w:
        case WCon{+w0, WCon{+w1, +wr}}:
          +e0 = and_true_l(w0, S.SeqNum.word.low0.go(p, w1, wr), el)
          +ih = w_zero_of(p, WCon{w1, wr}, et, and_true_r(w0, S.SeqNum.word.low0.go(p, w1, wr), el))
          %e0 : {WCon{w0, WCon{w1, wr}} == WCon{_, Word.zero(1n+p)} : Word(2n+p)}
          %ih : {WCon{w0, WCon{w1, wr}} == WCon{w0, _} : Word(2n+p)}
          {==}

# the word with only its top bit set
def topw(n: Nat) -> Word(1n+n):
  match n:
    case 0n:
      WCon{True{}, WNil{}}
    case 1n+p:
      WCon{False{}, topw(p)}

def w_top_of(n: Nat, w: Word(1n+n), et: {S.SeqNum.word.top(1n+n, w) == True{} : Bool}, +el: {S.SeqNum.word.low0(1n+n, w) == True{} : Bool}) -> {w == topw(n) : Word(1n+n)}:
  match n:
    case 0n:
      match w:
        case WCon{True{}, WNil{}}:
          {==}
        case WCon{False{}, WNil{}}:
          Empty.absurd({WCon{False{}, WNil{}} == topw(0n) : Word(1n)}, absurd.ft(et))
    case 1n+(+p):
      match w:
        case WCon{+w0, WCon{+w1, +wr}}:
          +e0 = and_true_l(w0, S.SeqNum.word.low0.go(p, w1, wr), el)
          +ih = w_top_of(p, WCon{w1, wr}, et, and_true_r(w0, S.SeqNum.word.low0.go(p, w1, wr), el))
          %e0 : {WCon{w0, WCon{w1, wr}} == WCon{_, topw(p)} : Word(2n+p)}
          %ih : {WCon{w0, WCon{w1, wr}} == WCon{w0, _} : Word(2n+p)}
          {==}

# b - a = 0 means b = a
def w_head(n: Nat, w: Word(1n+n)) -> Bool:
  match w:
    case WCon{h, t}:
      h

def w_tail(n: Nat, w: Word(1n+n)) -> Word(n):
  match w:
    case WCon{h, t}:
      t

def w_sub_zero(n: Nat, a: Word(n), b: Word(n), h: {Word.adc(n, b, a, True{}, True{}) == Word.zero(n) : Word(n)}) -> {b == a : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          +ih = w_sub_zero(p, at, bt, Equal.cong(Word(1n+p), Word(p), w => w_tail(p, w), Word.adc(1n+p, WCon{False{}, bt}, WCon{False{}, at}, True{}, True{}), Word.zero(1n+p), h))
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, bt, at, ih)
        case WCon{True{}, +at} WCon{True{}, +bt}:
          +ih = w_sub_zero(p, at, bt, Equal.cong(Word(1n+p), Word(p), w => w_tail(p, w), Word.adc(1n+p, WCon{True{}, bt}, WCon{True{}, at}, True{}, True{}), Word.zero(1n+p), h))
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, bt, at, ih)
        case WCon{False{}, at} WCon{True{}, bt}:
          Empty.absurd({WCon{True{}, bt} == WCon{False{}, at} : Word(1n+p)}, absurd.tf(Equal.cong(Word(1n+p), Bool, w => w_head(p, w), Word.adc(1n+p, WCon{True{}, bt}, WCon{False{}, at}, True{}, True{}), Word.zero(1n+p), h)))
        case WCon{True{}, at} WCon{False{}, bt}:
          Empty.absurd({WCon{False{}, bt} == WCon{True{}, at} : Word(1n+p)}, absurd.tf(Equal.cong(Word(1n+p), Bool, w => w_head(p, w), Word.adc(1n+p, WCon{False{}, bt}, WCon{True{}, at}, True{}, True{}), Word.zero(1n+p), h)))

# b = a when b - a is zero
def u32_eq_of_zero(+xa: Word(32n), +xb: Word(32n), et: {S.SeqNum.word.top(32n, Word.adc(32n, xb, xa, True{}, True{})) == False{} : Bool}, el: {S.SeqNum.word.low0(32n, Word.adc(32n, xb, xa, True{}, True{})) == True{} : Bool}) -> {U32.is_eq(U32{xa}, U32{xb}) == True{} : Bool}:
  +wz = w_zero_of(31n, Word.adc(32n, xb, xa, True{}, True{}), et, el)
  +ba = w_sub_zero(32n, xa, xb, wz)
  %Equal.sym(Word(32n), xb, xa, ba) : {U32.is_eq(U32{xa}, U32{_}) == True{} : Bool}
  u32_eq_refl(U32{xa})

# b - a is 2^31 when its top bit is set and the others are zero
def u32_half_of(w: Word(32n), et: {S.SeqNum.word.top(32n, w) == True{} : Bool}, el: {S.SeqNum.word.low0(32n, w) == True{} : Bool}) -> {U32.is_eq(U32{w}, 2147483648) == True{} : Bool}:
  %Equal.sym(Word(32n), w, topw(31n), w_top_of(31n, w, et, el)) : {U32.is_eq(U32{_}, 2147483648) == True{} : Bool}
  {==}

def total.go(+xa: Word(32n), +xb: Word(32n), t: Bool, l: Bool, et: {S.SeqNum.word.top(32n, Word.adc(32n, xb, xa, True{}, True{})) == t : Bool}, el: {S.SeqNum.word.low0(32n, Word.adc(32n, xb, xa, True{}, True{})) == l : Bool}) -> {Bool.or(Bool.and(Bool.not(t), Bool.not(l)), Bool.or(Bool.and(Bool.not(Bool.xor(Bool.not(t), l)), Bool.not(l)), Bool.or(U32.is_eq(U32{xa}, U32{xb}), U32.is_eq(U32{Word.adc(32n, xb, xa, True{}, True{})}, 2147483648)))) == True{} : Bool}:
  match t l:
    case False{} False{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      %Equal.sym(Bool, U32.is_eq(U32{xa}, U32{xb}), True{}, u32_eq_of_zero(xa, xb, et, el)) : {Bool.or(_, U32.is_eq(U32{Word.adc(32n, xb, xa, True{}, True{})}, 2147483648)) == True{} : Bool}
      {==}
    case True{} True{}:
      or_r(U32.is_eq(U32{xa}, U32{xb}), U32.is_eq(U32{Word.adc(32n, xb, xa, True{}, True{})}, 2147483648), u32_half_of(Word.adc(32n, xb, xa, True{}, True{}), et, el))

def Laws.seq_lt_total(a, b):
  match a b:
    case U32{+xa} U32{+xb}:
      +w = Word.adc(32n, xb, xa, True{}, True{})
      +nw = Word.adc(32n, Word.zero(32n), w, True{}, True{})
      +rest = {Bool.or(U32.is_eq(U32{xa}, U32{xb}), U32.is_eq(U32{w}, 2147483648)) : Bool}
      %Equal.sym(Word(32n), Word.adc(32n, xa, xb, True{}, True{}), nw, w_sub_neg(32n, TpW4c{}, xa, xb)) : {Bool.or(S.SeqNum.in_half(U32{w}), Bool.or(S.SeqNum.in_half(U32{_}), rest)) == True{} : Bool}
      %Equal.sym(Bool, S.SeqNum.word.top(32n, nw), Bool.xor(Bool.not(S.SeqNum.word.top(32n, w)), S.SeqNum.word.low0(32n, w)), w_neg_top(31n, w, True{})) : {Bool.or(S.SeqNum.in_half(U32{w}), Bool.or(Bool.and(Bool.not(_), Bool.not(S.SeqNum.word.low0(32n, nw))), rest)) == True{} : Bool}
      %Equal.sym(Bool, S.SeqNum.word.low0(32n, nw), S.SeqNum.word.low0(32n, w), w_neg_low0(31n, w, True{})) : {Bool.or(S.SeqNum.in_half(U32{w}), Bool.or(Bool.and(Bool.not(Bool.xor(Bool.not(S.SeqNum.word.top(32n, w)), S.SeqNum.word.low0(32n, w))), Bool.not(_)), rest)) == True{} : Bool}
      total.go(xa, xb, S.SeqNum.word.top(32n, w), S.SeqNum.word.low0(32n, w), {==}, {==})

def Laws.seq_vector_wrap():
  {==}

def Laws.reno_vector_slow_start():
  {==}

def Laws.reno_vector_avoidance():
  {==}

def Laws.reno_vector_fast_retransmit():
  {==}

def Laws.reno_vector_recovery_ends():
  {==}

def Laws.reno_vector_timeout():
  {==}

def Laws.tcp_vector_syn_ack():
  {==}

def Laws.tcp_vector_reset_reply():
  {==}

def Laws.tcp_vector_reset_reply_ack():
  {==}

def Laws.tcp_vector_no_reply_to_reset():
  {==}

