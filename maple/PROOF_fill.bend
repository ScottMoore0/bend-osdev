# Proofs of LAWS_fill.bend, for the U32 instance (Maple32). The lemmas are
# in proof_counts.bend; see its header for the plan.
import Base
import ./model.bend as M
import ./node.bend as N
import ./maple.bend as T
import ./proof_counts.bend as F
import ./LAWS_fill.bend as Laws

def le3max(n: Nat) -> {Nat.is_le(3n, Nat.max(3n, n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+m:
              F.nt.le_zero(m)

def Laws.balanced_empty(V):
  {==}

def Laws.balanced_empty_with(V, o):
  match o:
    case N.MapleOptions{+n}:
      F.nt.le_zero(Nat.max(3n, n))

def Laws.order_empty_with(V, o):
  match o:
    case N.MapleOptions{+n}:
      le3max(n)

def Laws.order_set_range(V, t, a, b, v):
  F.ord.sr.go(M.MapleKey.le(~U32, ~U32.cmp, a, b), V, t, a, b, v)

def Laws.order_clear_range(V, t, a, b):
  F.ord.cr.go(M.MapleKey.le(~U32, ~U32.cmp, a, b), V, t, a, b)

def Laws.order_erase(V, t, i):
  F.ord.erase.go(V, T.Maple32.lookup(V, t, i), t)

def Laws.balanced_set_range(V, t, a, b, v, e, f):
  F.tb.set_range(V, t, a, b, v, e, f)

def Laws.balanced_clear_range(V, t, a, b, e, f):
  F.tb.clear_range(V, t, a, b, e, f)

def Laws.balanced_erase(V, t, i, e, f):
  F.tb.erase(V, t, i, e, f)

def Laws.size_bound(V, t, m, g, e, f, h):
  F.size.ok(V, t, m, g, e, f, h)

def Laws.example_order():
  {==}

def Laws.example_order_small():
  {==}

def Laws.example_fill():
  {==}

def Laws.example_size_bound():
  {==}
