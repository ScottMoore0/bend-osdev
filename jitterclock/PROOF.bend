import Base
import ../word64/word64.bend as W
import ../word64/LAWS.bend as WL
import ../word64/PROOF.bend as WP
import ../jitter/jitter.bend as J
import ./time.bend as T
import ./LAWS.bend as Laws

def Laws.time_join_hi(h, l):
  WL.hi_from_parts(h, l)

def Laws.time_join_lo(h, l):
  WL.lo_from_parts(h, l)

# the deltas after a stamp: as many as the stamps that follow it
def from_len(ts: List<&2, W.W64>, +prev: W.W64) -> {List.length(&2, W.W64, T.JClock.time.deltas.from(ts, prev)) == List.length(&2, W.W64, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, rest}:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, W.W64, T.JClock.time.deltas.from(rest, t)), List.length(&2, W.W64, rest), from_len(rest, t))

def nat.sub_zero(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Laws.deltas_length(ts):
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +rest}:
      Equal.trans(Nat, List.length(&2, W.W64, T.JClock.time.deltas.from(rest, t)), List.length(&2, W.W64, rest), Nat.sub(List.length(&2, W.W64, rest), 0n), from_len(rest, t), Equal.sym(Nat, Nat.sub(List.length(&2, W.W64, rest), 0n), List.length(&2, W.W64, rest), nat.sub_zero(List.length(&2, W.W64, rest))))

def Laws.deltas_step(a, b, t):
  {==}

def Laws.deltas_vec():
  {==}

def Laws.budget_default():
  {==}
