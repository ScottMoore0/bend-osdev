# Properties, for every pool, fit algorithm (lawful or not), size, address
# and fit data:
#
# * every pool's free and allocated bytes add up to its size;
# * an allocation stays inside one chunk, at the address of its first
#   granule; its granules were free and are now allocated; no other granule
#   changes, nor the chunks themselves; the free bytes drop by its size in
#   granules;
# * on a valid pool (granules of at least a byte, no two chunks
#   overlapping), freeing an allocation gives back the pool from before it,
#   so allocating again gives the same allocation;
# * genpool.new is valid, and add, alloc and free keep a pool valid.
#
# Vectors: a few allocations, frees and fits.
import Base
import ./bits.bend as Bits
import ./genalloc.bend as G
import ./fit.bend as F

# Sizes

law avail_size:
  for p: G.GpPool
  {Nat.add(G.genpool.avail(p), G.genpool.allocated(p)) == G.genpool.size(p) : Nat}

# Allocation

law alloc_inside:
  for ~fit: G.GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>
  for +p: G.GpPool
  for +size: Nat
  for +data: G.GpFitData
  for q: G.GpPool
  for a: Nat
  for +c: Nat
  for +s: Nat
  for +n: Nat
  for e: {G.genpool.alloc(~fit, p, size, data) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}
  {Bool.and(Nat.is_lt(0n, n), Nat.is_le(Nat.add(s, n), G.genpool.chunk_granules(p, c))) == True{} : Bool}

law alloc_addr:
  for ~fit: G.GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>
  for +p: G.GpPool
  for +size: Nat
  for +data: G.GpFitData
  for q: G.GpPool
  for a: Nat
  for +c: Nat
  for +s: Nat
  for n: Nat
  for e: {G.genpool.alloc(~fit, p, size, data) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}
  {a == Nat.add(G.genpool.chunk_addr(p, c), Nat.mul(s, G.genpool.granule(p))) : Nat}

law alloc_was_free:
  for ~fit: G.GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>
  for +p: G.GpPool
  for +size: Nat
  for +data: G.GpFitData
  for q: G.GpPool
  for a: Nat
  for +c: Nat
  for +s: Nat
  for +n: Nat
  for +j: Nat
  for e: {G.genpool.alloc(~fit, p, size, data) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}
  for l: {Nat.is_le(s, j) == True{} : Bool}
  for m: {Nat.is_lt(j, Nat.add(s, n)) == True{} : Bool}
  {G.genpool.used_at(p, c, j) == False{} : Bool}

law alloc_in_use:
  for ~fit: G.GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>
  for +p: G.GpPool
  for +size: Nat
  for +data: G.GpFitData
  for +q: G.GpPool
  for a: Nat
  for +c: Nat
  for +s: Nat
  for +n: Nat
  for +j: Nat
  for e: {G.genpool.alloc(~fit, p, size, data) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}
  for l: {Nat.is_le(s, j) == True{} : Bool}
  for m: {Nat.is_lt(j, Nat.add(s, n)) == True{} : Bool}
  {G.genpool.used_at(q, c, j) == True{} : Bool}

law alloc_others:
  for ~fit: G.GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>
  for +p: G.GpPool
  for +size: Nat
  for +data: G.GpFitData
  for +q: G.GpPool
  for a: Nat
  for +c: Nat
  for +s: Nat
  for +n: Nat
  for +c2: Nat
  for +j: Nat
  for e: {G.genpool.alloc(~fit, p, size, data) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}
  for ho: {Bool.and(Nat.is_eq(c2, c), Bool.and(Nat.is_le(s, j), Nat.is_lt(j, Nat.add(s, n)))) == False{} : Bool}
  {G.genpool.used_at(q, c2, j) == G.genpool.used_at(p, c2, j) : Bool}

law alloc_blank:
  for ~fit: G.GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>
  for +p: G.GpPool
  for +size: Nat
  for +data: G.GpFitData
  for +q: G.GpPool
  for a: Nat
  for c: Nat
  for s: Nat
  for n: Nat
  for e: {G.genpool.alloc(~fit, p, size, data) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}
  {G.genpool.blank(q) == G.genpool.blank(p) : G.GpPool}

law alloc_avail:
  for ~fit: G.GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>
  for +p: G.GpPool
  for +size: Nat
  for +data: G.GpFitData
  for +q: G.GpPool
  for a: Nat
  for c: Nat
  for s: Nat
  for +n: Nat
  for e: {G.genpool.alloc(~fit, p, size, data) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}
  {Nat.add(G.genpool.avail(q), Nat.mul(n, G.genpool.granule(p))) == G.genpool.avail(p) : Nat}

# Freeing what was allocated

law free_alloc:
  for ~fit: G.GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>
  for +p: G.GpPool
  for +size: Nat
  for +data: G.GpFitData
  for +q: G.GpPool
  for +a: Nat
  for c: Nat
  for s: Nat
  for n: Nat
  for +hv: {G.genpool.valid(p) == True{} : Bool}
  for e: {G.genpool.alloc(~fit, p, size, data) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}
  {G.genpool.free(q, a, size) == Done{p} : Result<&2, &2, G.GpError, G.GpPool>}

law realloc:
  for ~fit: G.GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>
  for +p: G.GpPool
  for +size: Nat
  for +data: G.GpFitData
  for +q: G.GpPool
  for +a: Nat
  for +c: Nat
  for +s: Nat
  for +n: Nat
  for +hv: {G.genpool.valid(p) == True{} : Bool}
  for +e: {G.genpool.alloc(~fit, p, size, data) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}
  {G.genpool.alloc(~fit, G.genpool.pool(G.genpool.free(q, a, size), q), size, data) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}

# Validity

law new_valid:
  for +order: Nat
  {G.genpool.valid(G.genpool.new(order)) == True{} : Bool}

law add_valid:
  for +p: G.GpPool
  for +addr: Nat
  for size: Nat
  for +q: G.GpPool
  for +hv: {G.genpool.valid(p) == True{} : Bool}
  for e: {G.genpool.add(p, addr, size) == Done{q} : Result<&2, &2, G.GpError, G.GpPool>}
  {G.genpool.valid(q) == True{} : Bool}

law alloc_valid:
  for ~fit: G.GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>
  for +p: G.GpPool
  for +size: Nat
  for +data: G.GpFitData
  for +q: G.GpPool
  for a: Nat
  for c: Nat
  for s: Nat
  for n: Nat
  for +hv: {G.genpool.valid(p) == True{} : Bool}
  for e: {G.genpool.alloc(~fit, p, size, data) == Done{G.GpAlloc{q, a, c, s, n}} : Result<&2, &2, G.GpError, G.GpAlloc>}
  {G.genpool.valid(q) == True{} : Bool}

law free_valid:
  for +p: G.GpPool
  for +addr: Nat
  for +size: Nat
  for +q: G.GpPool
  for +hv: {G.genpool.valid(p) == True{} : Bool}
  for e: {G.genpool.free(p, addr, size) == Done{q} : Result<&2, &2, G.GpError, G.GpPool>}
  {G.genpool.valid(q) == True{} : Bool}

# Vectors: 16-byte granules, chunks of 16 granules at 1000 and 8 at 4096

law vec_first:
  {G.genpool.addr(F.genpool.alloc_first(G.genpool.pool(G.genpool.add(G.genpool.pool(G.genpool.add(G.genpool.new(4n), 1000n, 256n), G.genpool.new(4n)), 4096n, 128n), G.genpool.new(4n)), 40n)) == Some{1000n} : Maybe<&2, Nat>}

law vec_align:
  {G.genpool.addr(G.genpool.alloc(~F.genpool.first_fit_align, G.genpool.pool(G.genpool.add(G.genpool.pool(G.genpool.add(G.genpool.new(4n), 1000n, 256n), G.genpool.new(4n)), 4096n, 128n), G.genpool.new(4n)), 16n, G.GpAlign{64n})) == Some{4096n} : Maybe<&2, Nat>}

law vec_overlap:
  {G.genpool.add(G.genpool.pool(G.genpool.add(G.genpool.new(4n), 1000n, 256n), G.genpool.new(4n)), 1100n, 64n) == Fail{G.GpOverlap{}} : Result<&2, &2, G.GpError, G.GpPool>}
