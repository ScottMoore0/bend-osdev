import Base
import ./genalloc.bend as G
import ./fit.bend as F

def show_e(e: G.GpError) -> String:
  match e:
    case G.GpBadSize{}:
      "GpBadSize"
    case G.GpNoSpace{}:
      "GpNoSpace"
    case G.GpBadFit{c}:
      "GpBadFit"
    case G.GpOverlap{}:
      "GpOverlap"
    case G.GpNotInPool{}:
      "GpNotInPool"
    case G.GpMisaligned{}:
      "GpMisaligned"
    case G.GpNotInUse{}:
      "GpNotInUse"

def show_r(r: Result<&2, &2, G.GpError, G.GpAlloc>) -> String:
  match r:
    case Done{G.GpAlloc{q, a, c, s, n}}:
      Nat.show(a) ++ " (chunk " ++ Nat.show(c) ++ ", granule " ++ Nat.show(s) ++ ", " ++ Nat.show(n) ++ ")"
    case Fail{e}:
      show_e(e)

def show_p(r: Result<&2, &2, G.GpError, G.GpPool>) -> String:
  match r:
    case Done{q}:
      "ok"
    case Fail{e}:
      show_e(e)

def sizes(+p: G.GpPool) -> String:
  Nat.show(G.genpool.avail(p)) ++ " free, " ++ Nat.show(G.genpool.allocated(p)) ++ " allocated, " ++ Nat.show(G.genpool.size(p)) ++ " in all"

def addp(+p: G.GpPool, +a: Nat, +s: Nat) -> G.GpPool:
  G.genpool.pool(G.genpool.add(p, a, s), p)

def first(+p: G.GpPool, +s: Nat) -> G.GpPool:
  G.genpool.state(F.genpool.alloc_first(p, s), p)

def freep(+p: G.GpPool, +a: Nat, +s: Nat) -> G.GpPool:
  G.genpool.pool(G.genpool.free(p, a, s), p)

# 16-byte granules; chunks of 16 granules at 1000 and of 8 at 4096
def two() -> G.GpPool:
  addp(addp(G.genpool.new(4n), 1000n, 256n), 4096n, 128n)

# 48 bytes then 16 allocated
def used() -> G.GpPool:
  first(first(two(), 48n), 16n)

# granules 0-2 and 5, 7 of chunk 0 in use: holes of 2 at 3, of 1 at 6,
# and of 8 from 8
def holes() -> G.GpPool:
  freep(freep(first(first(first(first(first(two(), 48n), 32n), 16n), 16n), 16n), 1048n, 32n), 1096n, 16n)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(sizes(two()))
    IO.print(show_p(G.genpool.add(two(), 1100n, 64n)))
    IO.print(show_p(G.genpool.add(two(), 2000n, 10n)))
    IO.print(show_r(F.genpool.alloc_first(two(), 40n)))
    IO.print(show_r(F.genpool.alloc_first(first(two(), 40n), 16n)))
    IO.print(sizes(used()))
    IO.print(show_r(F.genpool.alloc_first(freep(used(), 1000n, 48n), 20n)))
    IO.print(show_r(F.genpool.alloc_first(used(), 300n)))
    IO.print(show_r(F.genpool.alloc_first(used(), 0n)))
    IO.print(show_p(G.genpool.free(used(), 1008n, 16n)))
    IO.print(show_p(G.genpool.free(used(), 1064n, 16n)))
    IO.print(show_p(G.genpool.free(used(), 5000n, 16n)))
    IO.print(show_r(G.genpool.alloc(~F.genpool.first_fit_align, used(), 16n, G.GpAlign{64n})))
    IO.print(show_r(G.genpool.alloc(~F.genpool.first_fit_order_align, used(), 48n, G.GpNoData{})))
    IO.print(show_r(G.genpool.alloc(~F.genpool.fixed_offset, used(), 32n, G.GpOffset{160n})))
    IO.print(show_r(G.genpool.alloc(~F.genpool.fixed_offset, used(), 32n, G.GpOffset{24n})))
    IO.print(show_r(G.genpool.alloc(~F.genpool.best_fit, holes(), 16n, G.GpNoData{})))
    IO.print(show_r(F.genpool.alloc_first(holes(), 16n)))
    IO.print(show_r(G.genpool.alloc(~F.genpool.best_fit, holes(), 32n, G.GpNoData{})))
    IO.print(sizes(holes()))
    IO.print(Bool.show(G.genpool.disjoint(holes())))

#|384 free, 0 allocated, 384 in all
#|GpOverlap
#|GpBadSize
#|1000 (chunk 0, granule 0, 3)
#|1048 (chunk 0, granule 3, 1)
#|320 free, 64 allocated, 384 in all
#|1000 (chunk 0, granule 0, 2)
#|GpNoSpace
#|GpBadSize
#|GpMisaligned
#|GpNotInUse
#|GpNotInPool
#|4096 (chunk 1, granule 0, 1)
#|1064 (chunk 0, granule 4, 3)
#|1160 (chunk 0, granule 10, 2)
#|GpNoSpace
#|1096 (chunk 0, granule 6, 1)
#|1048 (chunk 0, granule 3, 1)
#|1048 (chunk 0, granule 3, 2)
#|304 free, 80 allocated, 384 in all
#|True
