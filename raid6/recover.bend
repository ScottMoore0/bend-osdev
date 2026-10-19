# bend-osdev-raid6, recovery: rebuilding up to two lost blocks of a stripe
# from the others, following H. Peter Anvin, "The mathematics of RAID-6",
# section 2:
#
#   * one data block D_x: from P, as for RAID-5: D_x = P + P_x, where P_x is
#     P computed with D_x set to zero;
#   * P or Q, or both: recomputed from the data;
#   * D_x and Q: D_x from P, then Q recomputed;
#   * D_x and P: D_x = (Q + Q_x) g^(-x)                    (equation 5)
#     then P recomputed;
#   * D_x and D_y: with P_xy and Q_xy computed with both set to zero,
#       A = g^(y-x) (g^(y-x) + {01})^(-1)                  (equation 17)
#       B = g^(-x) (g^(y-x) + {01})^(-1)                   (equation 18)
#       D_x = A (P + P_xy) + B (Q + Q_xy)                  (equation 19)
#       D_y = (P + P_xy) + D_x                             (equation 20)
#     where g^(-x) is the inverse of g^x and g^(y-x) is g^y g^(-x).
#
# A lost block is never read: recovery first erases the lost blocks
# (Raid6.erase sets them to the empty block, which XOR treats as zeros, the
# paper's "setting the missing drives to {00}"). The paper allows at most
# 255 data blocks (section 1: g^x, x < 255, are distinct), and so does
# Raid6.check.
import Base
import ../bytes/bytes.bend as B
import ../gf/gf.bend as G
import ../xorblocks/xorblocks.bend as X
import ./scale.bend as S
import ./raid6.bend as R

# Which blocks are lost (x and y index the data blocks, from 0)
type Raid6Lost is Data:
  Raid6LostNone{}
  Raid6LostData{x: Nat}
  Raid6LostP{}
  Raid6LostQ{}
  Raid6LostDataData{x: Nat, y: Nat}
  Raid6LostDataP{x: Nat}
  Raid6LostDataQ{x: Nat}
  Raid6LostPQ{}

type Raid6Error is Data:
  Raid6TooManyDisks{n: Nat}
  Raid6BadIndex{i: Nat}
  Raid6SameIndex{i: Nat}

# The most data blocks: the order of g in GF(2^8)
def Raid6.max_disks() -> Nat:
  255n

# Checking a loss against the number of data blocks n

def r6.chk.index(lt: Bool, +i: Nat) -> Maybe<&2, Raid6Error>:
  match lt:
    case True{}:
      None{}
    case False{}:
      Some{Raid6BadIndex{i}}

def r6.chk.two(ex: Maybe<&2, Raid6Error>, y: Maybe<&2, Raid6Error>, ne: Bool, +x: Nat) -> Maybe<&2, Raid6Error>:
  match ex:
    case Some{e}:
      Some{e}
    case None{}:
      match y:
        case Some{e}:
          Some{e}
        case None{}:
          match ne:
            case True{}:
              None{}
            case False{}:
              Some{Raid6SameIndex{x}}

def r6.chk.lost(+n: Nat, lost: Raid6Lost) -> Maybe<&2, Raid6Error>:
  match lost:
    case Raid6LostNone{}:
      None{}
    case Raid6LostData{+x}:
      r6.chk.index(Nat.is_lt(x, n), x)
    case Raid6LostP{}:
      None{}
    case Raid6LostQ{}:
      None{}
    case Raid6LostDataData{+x, +y}:
      r6.chk.two(r6.chk.index(Nat.is_lt(x, n), x), r6.chk.index(Nat.is_lt(y, n), y), Nat.is_ne(x, y), x)
    case Raid6LostDataP{+x}:
      r6.chk.index(Nat.is_lt(x, n), x)
    case Raid6LostDataQ{+x}:
      r6.chk.index(Nat.is_lt(x, n), x)
    case Raid6LostPQ{}:
      None{}

def r6.chk.size(ok: Bool, +n: Nat, lost: Raid6Lost) -> Maybe<&2, Raid6Error>:
  match ok:
    case True{}:
      r6.chk.lost(n, lost)
    case False{}:
      Some{Raid6TooManyDisks{n}}

# None if the loss can be recovered in a stripe of n data blocks, else why not
def Raid6.check(+n: Nat, lost: Raid6Lost) -> Maybe<&2, Raid6Error>:
  r6.chk.size(Nat.is_le(n, Raid6.max_disks()), n, lost)

# The lost blocks set to the empty block
def Raid6.erase(st: R.Raid6Stripe, lost: Raid6Lost) -> R.Raid6Stripe:
  match st:
    case R.Raid6Stripe{ds, p, q}:
      match lost:
        case Raid6LostNone{}:
          R.Raid6Stripe{ds, p, q}
        case Raid6LostData{x}:
          R.Raid6Stripe{R.Raid6.set_block(ds, x, B.Octets.empty()), p, q}
        case Raid6LostP{}:
          R.Raid6Stripe{ds, B.Octets.empty(), q}
        case Raid6LostQ{}:
          R.Raid6Stripe{ds, p, B.Octets.empty()}
        case Raid6LostDataData{x, y}:
          R.Raid6Stripe{R.Raid6.set_block(R.Raid6.set_block(ds, x, B.Octets.empty()), y, B.Octets.empty()), p, q}
        case Raid6LostDataP{x}:
          R.Raid6Stripe{R.Raid6.set_block(ds, x, B.Octets.empty()), B.Octets.empty(), q}
        case Raid6LostDataQ{x}:
          R.Raid6Stripe{R.Raid6.set_block(ds, x, B.Octets.empty()), p, B.Octets.empty()}
        case Raid6LostPQ{}:
          R.Raid6Stripe{ds, B.Octets.empty(), B.Octets.empty()}

# The coefficients of equations 17 and 18, for lost data blocks x and y
def Raid6.coef_a(+s: R.Raid6Spec, +x: Nat, +y: Nat) -> U32:
  +f = R.Raid6.field(s)
  +gyx = G.Gf8.mul(f, R.Raid6.gpow(s, y), G.Gf8.inv(f, R.Raid6.gpow(s, x)))
  G.Gf8.mul(f, gyx, G.Gf8.inv(f, G.Gf8.add(gyx, 1)))

def Raid6.coef_b(+s: R.Raid6Spec, +x: Nat, +y: Nat) -> U32:
  +f = R.Raid6.field(s)
  +gyx = G.Gf8.mul(f, R.Raid6.gpow(s, y), G.Gf8.inv(f, R.Raid6.gpow(s, x)))
  G.Gf8.mul(f, G.Gf8.inv(f, R.Raid6.gpow(s, x)), G.Gf8.inv(f, G.Gf8.add(gyx, 1)))

# D_x from P: P + P_x, where ds has D_x erased
def r6.from_p(ds: List<&2, B.Octets>, p: B.Octets) -> B.Octets:
  X.Xorb.xor(p, R.Raid6.p(ds))

# D_x from Q: (Q + Q_x) g^(-x), where ds has D_x erased (equation 5)
def r6.from_q(+s: R.Raid6Spec, +x: Nat, ds: List<&2, B.Octets>, q: B.Octets) -> B.Octets:
  S.Raid6.scale(R.Raid6.field(s), G.Gf8.inv(R.Raid6.field(s), R.Raid6.gpow(s, x)), X.Xorb.xor(q, R.Raid6.q(s, ds)))

# D_x and D_y from the differences pd = P + P_xy and qd = Q + Q_xy
def r6.two.fin(+ds: List<&2, B.Octets>, +x: Nat, +y: Nat, +pd: B.Octets, +dx: B.Octets) -> List<&2, B.Octets>:
  R.Raid6.set_block(R.Raid6.set_block(ds, x, dx), y, X.Xorb.xor(pd, dx))

def r6.two(+s: R.Raid6Spec, +x: Nat, +y: Nat, +ds: List<&2, B.Octets>, +pd: B.Octets, +qd: B.Octets) -> List<&2, B.Octets>:
  r6.two.fin(ds, x, y, pd, X.Xorb.xor(S.Raid6.scale(R.Raid6.field(s), Raid6.coef_a(s, x, y), pd), S.Raid6.scale(R.Raid6.field(s), Raid6.coef_b(s, x, y), qd)))

def r6.with_q(+s: R.Raid6Spec, +ds: List<&2, B.Octets>, p: B.Octets) -> R.Raid6Stripe:
  R.Raid6Stripe{ds, p, R.Raid6.q(s, ds)}

def r6.with_p(+ds: List<&2, B.Octets>, q: B.Octets) -> R.Raid6Stripe:
  R.Raid6Stripe{ds, R.Raid6.p(ds), q}

# Rebuilding an erased stripe whose loss has been checked
def r6.rebuild(+s: R.Raid6Spec, st: R.Raid6Stripe, lost: Raid6Lost) -> R.Raid6Stripe:
  match st:
    case R.Raid6Stripe{+ds, +p, +q}:
      match lost:
        case Raid6LostNone{}:
          R.Raid6Stripe{ds, p, q}
        case Raid6LostData{+x}:
          R.Raid6Stripe{R.Raid6.set_block(ds, x, r6.from_p(ds, p)), p, q}
        case Raid6LostP{}:
          R.Raid6Stripe{ds, R.Raid6.p(ds), q}
        case Raid6LostQ{}:
          R.Raid6Stripe{ds, p, R.Raid6.q(s, ds)}
        case Raid6LostDataData{+x, +y}:
          R.Raid6Stripe{r6.two(s, x, y, ds, r6.from_p(ds, p), X.Xorb.xor(q, R.Raid6.q(s, ds))), p, q}
        case Raid6LostDataP{+x}:
          r6.with_p(R.Raid6.set_block(ds, x, r6.from_q(s, x, ds, q)), q)
        case Raid6LostDataQ{+x}:
          r6.with_q(s, R.Raid6.set_block(ds, x, r6.from_p(ds, p)), p)
        case Raid6LostPQ{}:
          R.Raid6.encode(s, ds)

def r6.recover.pick(err: Maybe<&2, Raid6Error>, +s: R.Raid6Spec, st: R.Raid6Stripe, +lost: Raid6Lost) -> Result<&2, &2, Raid6Error, R.Raid6Stripe>:
  match err:
    case Some{e}:
      Fail{e}
    case None{}:
      Done{r6.rebuild(s, Raid6.erase(st, lost), lost)}

def r6.width(st: R.Raid6Stripe) -> Nat:
  match st:
    case R.Raid6Stripe{ds, p, q}:
      R.Raid6.width(ds)

# The stripe with the lost blocks rebuilt (their contents in st are ignored)
def Raid6.recover(+s: R.Raid6Spec, +st: R.Raid6Stripe, +lost: Raid6Lost) -> Result<&2, &2, Raid6Error, R.Raid6Stripe>:
  r6.recover.pick(Raid6.check(r6.width(st), lost), s, st, lost)
