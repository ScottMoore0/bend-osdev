# bend-osdev-bzip2: the Burrows-Wheeler transform (Burrows and Wheeler, "A
# Block-sorting Lossless Data Compression Algorithm", SRC report 124, 1994;
# Tsai, "BZip2 Format Specification", section 4.2).
#
# The forward transform sorts the n rotations of a block (cyclically: the
# rotation at k is the block from k on, then the block before k) and keeps
# the last byte of each, in sorted order, and the position (origPtr) of the
# rotation at 0. The inverse rebuilds the block from those.
#
# Two implementations of each, which must agree:
#   * the fast ones (bwt_forward, bwt_inverse), on arrays: the forward
#     transform sorts by prefix doubling (Manber and Myers), ranking the
#     rotations by their first 1, 2, 4, ... bytes with a counting sort per
#     round, so n log n steps at most; the inverse follows the LF mapping;
#   * the references (bwt_forward_ref, bwt_inverse_ref), on lists, written
#     to be read rather than run: the forward one sorts the rotations by
#     insertion; the inverse one is the textbook rebuild of the sorted
#     table, a column at a time (n rounds of "prepend the last column, sort").
#     They are quadratic or worse: use them on small blocks.
# Rotations that are equal may come out in either order; that changes
# neither the last column nor the block the inverse rebuilds.
import Base
import ../bytes/bytes.bend as B
import ./list.bend as L
import ./error.bend as E

# A block's transform: the last column and the origin pointer
type Bzip2Bwt is Data:
  Bzip2Bwt{last: B.Octets, ptr: U32}

# Arrays

def bwt.depth.next(more: Bool, +d: Nat) -> Nat:
  match more:
    case True{}:
      1n+d
    case False{}:
      d

def bwt.depth.loop(fuel: Nat, +n: U32, +d: Nat) -> Nat:
  match fuel:
    case 0n:
      d
    case 1n+f:
      bwt.depth.loop(f, n, bwt.depth.next(U32.is_lt(U32.shln(1, d), n), d))

# the smallest d with 2^d >= n
def bwt.depth(+n: U32) -> Nat:
  bwt.depth.loop(32n, n, 0n)

# the list xs into a from index i
def bwt.fill(xs: List<&2, U32>, a: Array<U32>, +i: U32) -> Array<U32>:
  match xs:
    case Nil{}:
      a
    case Con{h, t}:
      bwt.fill(t, Array.set(U32, a, i, h), U32.add(i, 1))

# a[i] = i for the first n slots
def bwt.iota(n: Nat, a: Array<U32>, +i: U32) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      bwt.iota(p, Array.set(U32, a, i, i), U32.add(i, 1))

# the first n slots set to 0
def bwt.zero(n: Nat, a: Array<U32>, +i: U32) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+p:
      bwt.zero(p, Array.set(U32, a, i, 0), U32.add(i, 1))

def bwt.bump(r: Array<U32> & U32, +c: U32) -> Array<U32>:
  (a, v) = r
  Array.set(U32, a, c, U32.add(v, 1))

# exclusive prefix sums of the first n slots (r: the array and slot i)
def bwt.prefix(n: Nat, r: Array<U32> & U32, +i: U32, +sum: U32) -> Array<U32>:
  match n:
    case 0n:
      (a, v) = r
      a
    case 1n+p:
      (a, +v) = r
      +j = U32.add(i, 1)
      bwt.prefix(p, Array.get(U32, Array.set(U32, a, i, sum), j), j, U32.add(sum, v))

# The forward transform, by prefix doubling

type Bzip2Sort is Type:
  Bzip2Sort{s: Array<U32>, sa: Array<U32>, rk: Array<U32>, tmp: Array<U32>, cnt: Array<U32>}

def bwt.back.pick(ge: Bool, +i: U32, +k: U32, +n: U32) -> U32:
  match ge:
    case True{}:
      U32.sub(i, k)
    case False{}:
      U32.sub(U32.add(i, n), k)

# (i - k) mod n, for i, k < n
def bwt.back(+i: U32, +k: U32, +n: U32) -> U32:
  bwt.back.pick(U32.is_le(k, i), i, k, n)

# (i + k) mod n, for i, k < n
def bwt.fwd(+i: U32, +k: U32, +n: U32) -> U32:
  bwt.back(i, U32.sub(n, k), n)

# a. tmp[j] = (sa[j] - k) mod n
def bwt.shift.one(r: Array<U32> & U32, tmp: Array<U32>, +j: U32, +k: U32, +n: U32) -> Array<U32> & Array<U32>:
  (sa, v) = r
  (sa, Array.set(U32, tmp, j, bwt.back(v, k, n)))

def bwt.shift(m: Nat, st: Array<U32> & Array<U32>, +j: U32, +k: U32, +n: U32) -> Array<U32> & Array<U32>:
  match m:
    case 0n:
      st
    case 1n+p:
      (sa, tmp) = st
      bwt.shift(p, bwt.shift.one(Array.get(U32, sa, j), tmp, j, k, n), U32.add(j, 1), k, n)

# b. counting: cnt[rk[i]] += 1
def bwt.count.one(r: Array<U32> & U32, cnt: Array<U32>) -> Array<U32> & Array<U32>:
  (rk, +c) = r
  (rk, bwt.bump(Array.get(U32, cnt, c), c))

def bwt.count(m: Nat, st: Array<U32> & Array<U32>, +i: U32) -> Array<U32> & Array<U32>:
  match m:
    case 0n:
      st
    case 1n+p:
      (rk, cnt) = st
      bwt.count(p, bwt.count.one(Array.get(U32, rk, i), cnt), U32.add(i, 1))

# b. placing: i = tmp[j]; sa[cnt[rk[i]]++] = i
def bwt.place.d(r: Array<U32> & U32, sa: Array<U32>, +c: U32, +i: U32) -> Array<U32> & Array<U32>:
  (cnt, +pos) = r
  (Array.set(U32, cnt, c, U32.add(pos, 1)), Array.set(U32, sa, pos, i))

def bwt.place.fin(rk: Array<U32>, cs: Array<U32> & Array<U32>) -> Bzip2Place:
  (cnt, sa) = cs
  Bzip2Place{Array.new(U32, 0n, 0), rk, cnt, sa}

def bwt.place.c(r: Array<U32> & U32, cnt: Array<U32>, sa: Array<U32>, +i: U32) -> Bzip2Place:
  (rk, +c) = r
  bwt.place.fin(rk, bwt.place.d(Array.get(U32, cnt, c), sa, c, i))

type Bzip2Place is Type:
  Bzip2Place{tmp: Array<U32>, rk: Array<U32>, cnt: Array<U32>, sa: Array<U32>}

def bwt.place.tmp(tmp: Array<U32>, p: Bzip2Place) -> Bzip2Place:
  match p:
    case Bzip2Place{t0, rk, cnt, sa}:
      Bzip2Place{tmp, rk, cnt, sa}

def bwt.place.b(r: Array<U32> & U32, rk: Array<U32>, cnt: Array<U32>, sa: Array<U32>) -> Bzip2Place:
  (tmp, +i) = r
  bwt.place.tmp(tmp, bwt.place.c(Array.get(U32, rk, i), cnt, sa, i))

def bwt.place(m: Nat, p: Bzip2Place, +j: U32) -> Bzip2Place:
  match m:
    case 0n:
      p
    case 1n+q:
      match p:
        case Bzip2Place{tmp, rk, cnt, sa}:
          bwt.place(q, bwt.place.b(Array.get(U32, tmp, j), rk, cnt, sa), U32.add(j, 1))

# c. re-ranking: walk sa; a rotation whose (rank, rank k on) differs from the
# one before gets the next rank. new ranks go to tmp.
type Bzip2Rank is Type:
  Bzip2Rank{sa: Array<U32>, rk: Array<U32>, nr: Array<U32>, p1: U32, p2: U32, r: U32}

def bwt.rank.set(nr: Array<U32>, +a: U32, +r: U32) -> Array<U32>:
  Array.set(U32, nr, a, r)

def bwt.rank.new(same: Bool, +r: U32) -> U32:
  match same:
    case True{}:
      r
    case False{}:
      U32.add(r, 1)

def bwt.rank.e(r2: Array<U32> & U32, sa: Array<U32>, nr: Array<U32>, +a: U32, +k1: U32, +p1: U32, +p2: U32, +r: U32) -> Bzip2Rank:
  (rk, +k2) = r2
  +nrk = bwt.rank.new(Bool.and(U32.is_eq(k1, p1), U32.is_eq(k2, p2)), r)
  Bzip2Rank{sa, rk, bwt.rank.set(nr, a, nrk), k1, k2, nrk}

def bwt.rank.d(r1: Array<U32> & U32, sa: Array<U32>, nr: Array<U32>, +a: U32, +k: U32, +n: U32, +p1: U32, +p2: U32, +r: U32) -> Bzip2Rank:
  (rk, +k1) = r1
  bwt.rank.e(Array.get(U32, rk, bwt.fwd(a, k, n)), sa, nr, a, k1, p1, p2, r)

def bwt.rank.c(r0: Array<U32> & U32, rk: Array<U32>, nr: Array<U32>, +k: U32, +n: U32, +p1: U32, +p2: U32, +r: U32) -> Bzip2Rank:
  (sa, +a) = r0
  bwt.rank.d(Array.get(U32, rk, a), sa, nr, a, k, n, p1, p2, r)

def bwt.rank(m: Nat, st: Bzip2Rank, +j: U32, +k: U32, +n: U32) -> Bzip2Rank:
  match m:
    case 0n:
      st
    case 1n+q:
      match st:
        case Bzip2Rank{sa, rk, nr, +p1, +p2, +r}:
          bwt.rank(q, bwt.rank.c(Array.get(U32, sa, j), rk, nr, k, n, p1, p2, r), U32.add(j, 1), k, n)

# One round: sort by (rank, rank k on), then re-rank. Answers the highest rank.
type Bzip2Round is Type:
  Bzip2Round{st: Bzip2Sort, top: U32}

def bwt.round.fin(rs: Bzip2Rank, s: Array<U32>, cnt: Array<U32>) -> Bzip2Round:
  match rs:
    case Bzip2Rank{sa, rk, nr, p1, p2, r}:
      Bzip2Round{Bzip2Sort{s, sa, nr, rk, cnt}, r}

def bwt.round.c(p: Bzip2Place, s: Array<U32>, +k: U32, +n: U32, +nn: Nat) -> Bzip2Round:
  match p:
    case Bzip2Place{tmp, rk, cnt, sa}:
      bwt.round.fin(bwt.rank(nn, Bzip2Rank{sa, rk, tmp, 4294967295, 4294967295, 4294967295}, 0, k, n), s, cnt)

def bwt.round.b(rc: Array<U32> & Array<U32>, s: Array<U32>, sa: Array<U32>, tmp: Array<U32>, +k: U32, +n: U32, +nn: Nat, +nb: Nat) -> Bzip2Round:
  (rk, cnt) = rc
  bwt.round.c(bwt.place(nn, Bzip2Place{tmp, rk, bwt.prefix(nb, Array.get(U32, cnt, 0), 0, 0), sa}, 0), s, k, n, nn)

def bwt.round.a(st2: Array<U32> & Array<U32>, s: Array<U32>, rk: Array<U32>, cnt: Array<U32>, +k: U32, +n: U32, +nn: Nat, +nb: Nat) -> Bzip2Round:
  (sa, tmp) = st2
  bwt.round.b(bwt.count(nn, (rk, bwt.zero(nb, cnt, 0)), 0), s, sa, tmp, k, n, nn, nb)

def bwt.round(st: Bzip2Sort, +k: U32, +n: U32, +nn: Nat, +nb: Nat) -> Bzip2Round:
  match st:
    case Bzip2Sort{s, sa, rk, tmp, cnt}:
      bwt.round.a(bwt.shift(nn, (sa, tmp), 0, k, n), s, rk, cnt, k, n, nn, nb)

# rounds with k = 0, then 1, 2, 4, ... until the ranks are all different or
# the prefixes compared cover whole rotations
type Bzip2Rounds is Type:
  Bzip2RoundsGo{st: Bzip2Sort}
  Bzip2RoundsStop{st: Bzip2Sort}

def bwt.rounds.pick(more: Bool, st: Bzip2Sort) -> Bzip2Rounds:
  match more:
    case True{}:
      Bzip2RoundsGo{st}
    case False{}:
      Bzip2RoundsStop{st}

def bwt.rounds.check(r: Bzip2Round, +k: U32, +n: U32) -> Bzip2Rounds:
  match r:
    case Bzip2Round{st, +top}:
      bwt.rounds.pick(Bool.and(U32.is_lt(top, U32.sub(n, 1)), U32.is_lt(k, n)), st)

# st has been through the rounds before k; nb: how many ranks there may be
# (the byte values before the first round, then fewer than n)
def bwt.rounds(fuel: Nat, r: Bzip2Rounds, +k: U32, +n: U32, +nn: Nat, +nb: Nat) -> Bzip2Sort:
  match fuel:
    case 0n:
      match r:
        case Bzip2RoundsGo{st}:
          st
        case Bzip2RoundsStop{st}:
          st
    case 1n+f:
      match r:
        case Bzip2RoundsStop{st}:
          st
        case Bzip2RoundsGo{st}:
          +k2 = U32.max(1, U32.add(k, k))
          bwt.rounds(f, bwt.rounds.check(bwt.round(st, k, n, nn, nb), k2, n), k2, n, nn, nn)

# The last column and the origin pointer: L[j] = s[(sa[j] - 1) mod n]; ptr is
# the j with sa[j] = 0. Walked from j = n - 1 down, so the list comes out in
# order.
type Bzip2Last is Type:
  Bzip2Last{s: Array<U32>, sa: Array<U32>, acc: List<&2, U32>, ptr: U32}

def bwt.last.ptr(z: Bool, +j: U32, +ptr: U32) -> U32:
  match z:
    case True{}:
      j
    case False{}:
      ptr

def bwt.last.c(r: Array<U32> & U32, sa: Array<U32>, acc: List<&2, U32>, ptr: U32) -> Bzip2Last:
  (s, c) = r
  Bzip2Last{s, sa, Con{c, acc}, ptr}

def bwt.last.b(r: Array<U32> & U32, s: Array<U32>, acc: List<&2, U32>, +j: U32, +ptr: U32, +n: U32) -> Bzip2Last:
  (sa, +a) = r
  bwt.last.c(Array.get(U32, s, bwt.back(a, 1, n)), sa, acc, bwt.last.ptr(U32.is_eq(a, 0), j, ptr))

def bwt.last.go(m: Nat, st: Bzip2Last, +j: U32, +n: U32) -> Bzip2Last:
  match m:
    case 0n:
      st
    case 1n+q:
      match st:
        case Bzip2Last{s, sa, acc, ptr}:
          bwt.last.go(q, bwt.last.b(Array.get(U32, sa, j), s, acc, j, ptr, n), U32.sub(j, 1), n)

type Bzip2BwtList is Data:
  Bzip2BwtList{last: List<&2, U32>, ptr: U32}

def bwt.last.fin(st: Bzip2Last) -> Bzip2BwtList:
  match st:
    case Bzip2Last{s, sa, acc, ptr}:
      Bzip2BwtList{acc, ptr}

def bwt.forward.sorted(st: Bzip2Sort, +n: U32, +nn: Nat) -> Bzip2BwtList:
  match st:
    case Bzip2Sort{s, sa, rk, tmp, cnt}:
      bwt.last.fin(bwt.last.go(nn, Bzip2Last{s, sa, Nil{}, 0}, U32.sub(n, 1), n))

def bwt.forward.arrays(+xs: List<&2, U32>, +nn: Nat, +n: U32, +d: Nat, +db: Nat) -> Bzip2Sort:
  Bzip2Sort{bwt.fill(xs, Array.new(U32, d, 0), 0), bwt.iota(nn, Array.new(U32, d, 0), 0), bwt.fill(xs, Array.new(U32, d, 0), 0), Array.new(U32, d, 0), Array.new(U32, db, 0)}

def bwt.forward.run(st: Bzip2Sort, +nn: Nat, +n: U32, +nb: Nat) -> Bzip2BwtList:
  bwt.forward.sorted(bwt.rounds(1n+nn, Bzip2RoundsGo{st}, 0, n, nn, nb), n, nn)

def bwt.forward.go2(+xs: List<&2, U32>, +nn: Nat, +n: U32, +d: Nat, +db: Nat) -> Bzip2BwtList:
  bwt.forward.run(bwt.forward.arrays(xs, nn, n, d, db), nn, n, U32.to_nat(U32.shln(1, db)))

def bwt.forward.go1(+xs: List<&2, U32>, +nn: Nat, +n: U32, +d: Nat) -> Bzip2BwtList:
  bwt.forward.go2(xs, nn, n, d, Nat.max(d, 8n))

def bwt.forward.go(+xs: List<&2, U32>, +nn: Nat) -> Bzip2BwtList:
  bwt.forward.go1(xs, nn, U32.from_nat(nn), bwt.depth(U32.from_nat(nn)))

def bwt.forward.n(+xs: List<&2, U32>, nn: Nat) -> Bzip2BwtList:
  match nn:
    case 0n:
      Bzip2BwtList{Nil{}, 0}
    case 1n+m:
      bwt.forward.go(xs, 1n+m)

def bwt_forward_list(+xs: List<&2, U32>) -> Bzip2BwtList:
  bwt.forward.n(xs, L.bz.len(xs))

# The inverse, by the LF mapping
#
# Counting sort gives, for each position j of the sorted first column, the
# position i in the last column of the same occurrence of the same byte. With
# A[j] = (i << 8) | L[j], the block is L[A[p]] for p = origPtr, A[p] >> 8,
# ... (the walk the bzip2 format describes).

def bwt.cnt(xs: List<&2, U32>, a: Array<U32>) -> Array<U32>:
  match xs:
    case Nil{}:
      a
    case Con{+h, t}:
      bwt.cnt(t, bwt.bump(Array.get(U32, a, h), h))

def bwt.link.c(r: Array<U32> & U32, cs: Array<U32>, +j: U32, +i: U32) -> Array<U32> & Array<U32>:
  (a, v) = r
  (cs, Array.set(U32, a, j, U32.or(v, U32.mul(i, 256))))

def bwt.link.b(r: Array<U32> & U32, a: Array<U32>, +h: U32, +i: U32) -> Array<U32> & Array<U32>:
  (cs, +j) = r
  bwt.link.c(Array.get(U32, a, j), Array.set(U32, cs, h, U32.add(j, 1)), j, i)

def bwt.link(xs: List<&2, U32>, st: Array<U32> & Array<U32>, +i: U32) -> Array<U32>:
  match xs:
    case Nil{}:
      (cs, a) = st
      a
    case Con{+h, t}:
      (cs, a) = st
      bwt.link(t, bwt.link.b(Array.get(U32, cs, h), a, h, i), U32.add(i, 1))

# n steps of the walk (r: the array and the entry at the current position)
def bwt.walk(n: Nat, r: Array<U32> & U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      (a, +v) = r
      bwt.walk(p, Array.get(U32, a, U32.shrn(v, 8n)), Con{U32.and(v, 255), acc})

def bwt.walk.start(r: Array<U32> & U32, +nn: Nat) -> List<&2, U32>:
  (a, +v) = r
  bwt.walk(nn, Array.get(U32, a, U32.shrn(v, 8n)), Nil{})

# the block (reversed) whose last column is xs (masked bytes) and whose
# origin pointer is ptr, n = len(xs) >= 1, ptr < n
def bwt.inverse.go(+xs: List<&2, U32>, +nn: Nat, +ptr: U32) -> List<&2, U32>:
  +d = bwt.depth(U32.from_nat(nn))
  cs = bwt.prefix(256n, Array.get(U32, bwt.cnt(xs, Array.new(U32, 8n, 0)), 0), 0, 0)
  a = bwt.link(xs, (cs, bwt.fill(xs, Array.new(U32, d, 0), 0)), 0)
  bwt.walk.start(Array.get(U32, a, ptr), nn)

def bwt.inverse.check(ok: Bool, +xs: List<&2, U32>, +nn: Nat, +ptr: U32) -> Result<&2, &2, E.Bzip2Error, List<&2, U32>>:
  match ok:
    case True{}:
      Done{L.bz.rev(bwt.inverse.go(xs, nn, ptr))}
    case False{}:
      Fail{E.Bzip2BadOrigPtr{}}

def bwt.inverse.empty(ok: Bool) -> Result<&2, &2, E.Bzip2Error, List<&2, U32>>:
  match ok:
    case True{}:
      Done{Nil{}}
    case False{}:
      Fail{E.Bzip2BadOrigPtr{}}

def bwt.inverse.n(+xs: List<&2, U32>, nn: Nat, +ptr: U32) -> Result<&2, &2, E.Bzip2Error, List<&2, U32>>:
  match nn:
    case 0n:
      bwt.inverse.empty(U32.is_eq(ptr, 0))
    case 1n+(+m):
      bwt.inverse.check(Nat.is_lt(U32.to_nat(ptr), 1n+m), xs, 1n+m, ptr)

# the block whose last column is xs (bytes 0 to 255) and origin pointer ptr
def bwt_inverse_list(+xs: List<&2, U32>, +ptr: U32) -> Result<&2, &2, E.Bzip2Error, List<&2, U32>>:
  bwt.inverse.n(xs, L.bz.len(xs), ptr)

# The references, on lists

def bwt.drop(k: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      xs
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          bwt.drop(p, t)

def bwt.take(k: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          Con{h, bwt.take(p, t)}

# the rotation of xs at k: xs from k on, then xs before k
def bwt.rot(+k: Nat, +xs: List<&2, U32>) -> List<&2, U32>:
  L.bz.app(bwt.drop(k, xs), bwt.take(k, xs))

def bwt.cmp.fin(c: Cmp, rest: Cmp) -> Cmp:
  match c:
    case EQ{}:
      rest
    case LT{}:
      LT{}
    case GT{}:
      GT{}

# lexicographic order
def bwt.cmp(xs: List<&2, U32>, ys: List<&2, U32>) -> Cmp:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          EQ{}
        case Con{y, yt}:
          LT{}
    case Con{x, xt}:
      match ys:
        case Nil{}:
          GT{}
        case Con{y, yt}:
          bwt.cmp.fin(U32.cmp(x, y), bwt.cmp(xt, yt))

def bwt.le(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  Bool.not(Cmp.is_gt(bwt.cmp(xs, ys)))

# insertion sort of rotation positions (stable: a position goes before the
# equal ones already sorted)
def ref.ins.pick(le: Bool, +i: Nat, +j: Nat, +t: List<&2, Nat>, rest: List<&2, Nat>) -> List<&2, Nat>:
  match le:
    case True{}:
      Con{i, Con{j, t}}
    case False{}:
      Con{j, rest}

def ref.ins(ys: List<&2, Nat>, +i: Nat, +xs: List<&2, U32>) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      [i]
    case Con{+j, +t}:
      ref.ins.pick(bwt.le(bwt.rot(i, xs), bwt.rot(j, xs)), i, j, t, ref.ins(t, i, xs))

def ref.sort(ps: List<&2, Nat>, +xs: List<&2, U32>) -> List<&2, Nat>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{i, t}:
      ref.ins(ref.sort(t, xs), i, xs)

# [i, i + 1, ..., i + m - 1]
def ref.upto(m: Nat, +i: Nat) -> List<&2, Nat>:
  match m:
    case 0n:
      Nil{}
    case 1n+p:
      Con{i, ref.upto(p, 1n+i)}

def ref.final(xs: List<&2, U32>, d: U32) -> U32:
  match xs:
    case Nil{}:
      d
    case Con{h, t}:
      ref.final(t, h)

# the last byte of each sorted rotation
def ref.lasts(ps: List<&2, Nat>, +xs: List<&2, U32>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{i, t}:
      Con{ref.final(bwt.rot(i, xs), 0), ref.lasts(t, xs)}

# where the rotation at 0 is
def ref.pos(ps: List<&2, Nat>, +k: Nat) -> Nat:
  match ps:
    case Nil{}:
      k
    case Con{i, t}:
      match i:
        case 0n:
          k
        case 1n+j:
          ref.pos(t, 1n+k)

def ref.forward(+xs: List<&2, U32>) -> Bzip2BwtList:
  +ps = ref.sort(ref.upto(L.bz.len(xs), 0n), xs)
  Bzip2BwtList{ref.lasts(ps, xs), U32.from_nat(ref.pos(ps, 0n))}

# The inverse reference: n rounds of putting the last column in front of the
# rows and sorting the rows; the row at the origin pointer is the block

def ref.cons(cs: List<&2, U32>, rows: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, ct}:
      match rows:
        case Nil{}:
          Nil{}
        case Con{r, rt}:
          Con{Con{c, r}, ref.cons(ct, rt)}

def ref.rins.pick(le: Bool, +x: List<&2, U32>, +y: List<&2, U32>, +t: List<&2, List<&2, U32>>, rest: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match le:
    case True{}:
      Con{x, Con{y, t}}
    case False{}:
      Con{y, rest}

def ref.rins(ys: List<&2, List<&2, U32>>, +x: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match ys:
    case Nil{}:
      [x]
    case Con{+y, +t}:
      ref.rins.pick(bwt.le(x, y), x, y, t, ref.rins(t, x))

def ref.rsort(rows: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      ref.rins(ref.rsort(t), r)

def ref.rounds(k: Nat, +cs: List<&2, U32>, rows: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match k:
    case 0n:
      rows
    case 1n+p:
      ref.rounds(p, cs, ref.rsort(ref.cons(cs, rows)))

def ref.empties(n: Nat) -> List<&2, List<&2, U32>>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{Nil{}, ref.empties(p)}

def ref.row(m: Maybe<&2, List<&2, U32>>) -> Result<&2, &2, E.Bzip2Error, List<&2, U32>>:
  match m:
    case None{}:
      Fail{E.Bzip2BadOrigPtr{}}
    case Some{r}:
      Done{r}

def ref.inverse.n(nn: Nat, +cs: List<&2, U32>, +ptr: U32) -> Result<&2, &2, E.Bzip2Error, List<&2, U32>>:
  match nn:
    case 0n:
      bwt.inverse.empty(U32.is_eq(ptr, 0))
    case 1n+(+m):
      ref.row(List.get(&2, List<&2, U32>, ref.rounds(1n+m, cs, ref.empties(1n+m)), U32.to_nat(ptr)))

def ref.inverse(+cs: List<&2, U32>, +ptr: U32) -> Result<&2, &2, E.Bzip2Error, List<&2, U32>>:
  ref.inverse.n(L.bz.len(cs), cs, ptr)

# The public interface

def bwt.octets(r: Bzip2BwtList) -> Bzip2Bwt:
  match r:
    case Bzip2BwtList{last, ptr}:
      Bzip2Bwt{B.Octets.of_list(last), ptr}

def bwt.res(r: Result<&2, &2, E.Bzip2Error, List<&2, U32>>) -> Result<&2, &2, E.Bzip2Error, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{ys}:
      Done{B.Octets.of_list(ys)}

# the transform of the block o (fast)
def bwt_forward(o: B.Octets) -> Bzip2Bwt:
  bwt.octets(bwt_forward_list(B.Octets.to_list(o)))

# the block whose last column is last and origin pointer ptr (fast); a
# pointer past the end is Bzip2BadOrigPtr
def bwt_inverse(last: B.Octets, +ptr: U32) -> Result<&2, &2, E.Bzip2Error, B.Octets>:
  bwt.res(bwt_inverse_list(B.Octets.to_list(last), ptr))

# the same two, by the references (slow: for small blocks and for proofs)
def bwt_forward_ref(o: B.Octets) -> Bzip2Bwt:
  bwt.octets(ref.forward(B.Octets.to_list(o)))

def bwt_inverse_ref(last: B.Octets, +ptr: U32) -> Result<&2, &2, E.Bzip2Error, B.Octets>:
  bwt.res(ref.inverse(B.Octets.to_list(last), ptr))
