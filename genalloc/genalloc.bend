# bend-osdev-genalloc: a general-purpose pool allocator in the style of the
# kernel's genalloc (gen_pool), as a pure state machine.
#
# A pool hands out pieces of address ranges ("chunks") added to it. Space is
# managed in granules of 2^order bytes (the minimum allocation order): each
# chunk keeps one bit per granule, set while the granule is allocated. An
# allocation of size bytes takes ceil(size / 2^order) consecutive free
# granules of one chunk; where in which chunk is decided by a fit algorithm,
# a template argument (fit.bend holds the kernel's: first fit, best fit,
# first fit with alignment, first fit aligned to the size's order, fixed
# offset). The pool checks every answer of the fit algorithm, so a wrong
# one cannot corrupt it.
#
# Addresses and sizes are Nat (a native build holds a Nat below 2^48).
import Base
import ./bits.bend as Bits

# Types

type GpError is Data:
  GpBadSize{}
  GpNoSpace{}
  GpBadFit{chunk: Nat}
  GpOverlap{}
  GpNotInPool{}
  GpMisaligned{}
  GpNotInUse{}

# a chunk: its first address, and one bit per granule (True: allocated)
type GpChunk is Data:
  GpChunk{addr: Nat, used: List<&2, Bool>}

# a pool: the minimum allocation order, the granule size 2^order, and the
# chunks, in the order they were added
type GpPool is Data:
  GpPool{order: Nat, granule: Nat, chunks: List<&2, GpChunk>}

# what an allocation answers: the new pool, the address, and where it lies:
# the chunk's index, its first granule there, and how many granules
type GpAlloc is Data:
  GpAlloc{pool: GpPool, addr: Nat, chunk: Nat, first: Nat, count: Nat}

# the data a fit algorithm takes (the kernel's void *data)
type GpFitData is Data:
  GpNoData{}
  GpAlign{align: Nat}
  GpOffset{offset: Nat}

# where a fit algorithm placed an allocation: chunk, first granule, and the
# chunk's address
type GpPlan is Data:
  GpPlan{chunk: Nat, first: Nat, base: Nat}

# Chunks

def genpool.chunk.addr(c: GpChunk) -> Nat:
  match c:
    case GpChunk{a, u}:
      a

def genpool.chunk.used(c: GpChunk) -> List<&2, Bool>:
  match c:
    case GpChunk{a, u}:
      u

# the address just past the chunk
def genpool.chunk.end(c: GpChunk, g: Nat) -> Nat:
  match c:
    case GpChunk{a, u}:
      Nat.add(a, Nat.mul(List.length(&2, Bool, u), g))

# two address ranges [b1, e1) and [b2, e2) do not overlap
def genpool.apart(+b1: Nat, +e1: Nat, +b2: Nat, +e2: Nat) -> Bool:
  Bool.or(Nat.is_le(e1, b2), Nat.is_le(e2, b1))

# [b, e) overlaps no chunk of cs
def genpool.apart_all(+b: Nat, +e: Nat, cs: List<&2, GpChunk>, +g: Nat) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      Bool.and(genpool.apart(b, e, genpool.chunk.addr(c), genpool.chunk.end(c, g)), genpool.apart_all(b, e, t, g))

def genpool.disjoint.go(+cs: List<&2, GpChunk>, +g: Nat) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      Bool.and(genpool.apart_all(genpool.chunk.addr(c), genpool.chunk.end(c, g), t, g), genpool.disjoint.go(t, g))

# Building a pool

# an empty pool whose granules are 2^order bytes (gen_pool_create)
def genpool.new(+order: Nat) -> GpPool:
  GpPool{order, Nat.pow(2n, order), Nil{}}

def genpool.add.check(ok: Bool, +order: Nat, +g: Nat, cs: List<&2, GpChunk>, +addr: Nat, +n: Nat) -> Result<&2, &2, GpError, GpPool>:
  match ok:
    case True{}:
      Done{GpPool{order, g, List.append(&2, GpChunk, cs, [GpChunk{addr, List.replicate(Bool, n, False{})}])}}
    case False{}:
      Fail{GpOverlap{}}

def genpool.add.go(+n: Nat, +order: Nat, +g: Nat, +cs: List<&2, GpChunk>, +addr: Nat) -> Result<&2, &2, GpError, GpPool>:
  match n:
    case 0n:
      Fail{GpBadSize{}}
    case 1n+m:
      genpool.add.check(genpool.apart_all(addr, Nat.add(addr, Nat.mul(1n+m, g)), cs, g), order, g, cs, addr, 1n+m)

# the chunk [addr, addr + size) added, its size rounded down to whole
# granules; GpBadSize if that is none, GpOverlap if it overlaps a chunk of
# the pool (gen_pool_add)
def genpool.add(p: GpPool, +addr: Nat, size: Nat) -> Result<&2, &2, GpError, GpPool>:
  match p:
    case GpPool{+order, +g, cs}:
      genpool.add.go(Nat.div(size, g), order, g, cs, addr)

# Allocating

# the granules that hold size bytes (at least one)
def genpool.granules_for(size: Nat, +g: Nat) -> Nat:
  Nat.max(Nat.div(Nat.add(size, Nat.sub(g, 1n)), g), 1n)

def genpool.plan.check(ok: Bool, +c: Nat, +s: Nat, +b: Nat) -> Result<&2, &2, GpError, GpPlan>:
  match ok:
    case True{}:
      Done{GpPlan{c, s, b}}
    case False{}:
      Fail{GpBadFit{c}}

# chunk ch (index c) asked, m the fit's answer for it; rest the chunks after
def genpool.plan.go(~fit: GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>, rest: List<&2, GpChunk>, m: Maybe<&2, Nat>, +ch: GpChunk, +n: Nat, +data: GpFitData, +g: Nat, +c: Nat) -> Result<&2, &2, GpError, GpPlan>:
  match rest m:
    case r Some{+s}:
      genpool.plan.check(Bits.genpool.bits.run_free(genpool.chunk.used(ch), s, n), c, s, genpool.chunk.addr(ch))
    case Nil{} None{}:
      Fail{GpNoSpace{}}
    case Con{+h, t} None{}:
      genpool.plan.go(~fit, t, fit(data, genpool.chunk.used(h), n, genpool.chunk.addr(h), g), h, n, data, g, 1n+c)

# the first chunk the fit algorithm places n granules in, and where
def genpool.plan(~fit: GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>, cs: List<&2, GpChunk>, +n: Nat, +data: GpFitData, +g: Nat) -> Result<&2, &2, GpError, GpPlan>:
  match cs:
    case Nil{}:
      Fail{GpNoSpace{}}
    case Con{+h, t}:
      genpool.plan.go(~fit, t, fit(data, genpool.chunk.used(h), n, genpool.chunk.addr(h), g), h, n, data, g, 0n)

# granules s to s + n - 1 of chunk c set to v
def genpool.mark(cs: List<&2, GpChunk>, c: Nat, +s: Nat, +n: Nat, +v: Bool) -> List<&2, GpChunk>:
  match cs c:
    case Nil{} _:
      Nil{}
    case Con{GpChunk{a, u}, t} 0n:
      Con{GpChunk{a, Bits.genpool.bits.fill(u, s, n, v)}, t}
    case Con{h, t} 1n+i:
      Con{h, genpool.mark(t, i, s, n, v)}

def genpool.alloc.apply(r: Result<&2, &2, GpError, GpPlan>, +order: Nat, +g: Nat, cs: List<&2, GpChunk>, +n: Nat) -> Result<&2, &2, GpError, GpAlloc>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{GpPlan{+c, +s, b}}:
      Done{GpAlloc{GpPool{order, g, genpool.mark(cs, c, s, n, True{})}, Nat.add(b, Nat.mul(s, g)), c, s, n}}

# size bytes allocated where the fit algorithm places them, with data passed
# to it (gen_pool_alloc_algo): GpBadSize for size 0, GpNoSpace when no chunk
# has room, GpBadFit when the fit answered granules that are not free
def genpool.alloc(~fit: GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>, p: GpPool, size: Nat, +data: GpFitData) -> Result<&2, &2, GpError, GpAlloc>:
  match p size:
    case GpPool{order, g, cs} 0n:
      Fail{GpBadSize{}}
    case GpPool{+order, +g, +cs} 1n+k:
      +n = genpool.granules_for(1n+k, g)
      genpool.alloc.apply(genpool.plan(~fit, cs, n, data, g), order, g, cs, n)

# Freeing

def genpool.free.clear(ok: Bool, bs: List<&2, Bool>, +n: Nat) -> Result<&2, &2, GpError, List<&2, Bool>>:
  match ok:
    case True{}:
      Done{Bits.genpool.bits.fill_prefix(bs, n, False{})}
    case False{}:
      Fail{GpNotInUse{}}

def genpool.free.cons(b: Bool, r: Result<&2, &2, GpError, List<&2, Bool>>) -> Result<&2, &2, GpError, List<&2, Bool>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{bs}:
      Done{Con{b, bs}}

# the chunk's bits from address x on: hit says x is addr, past that it is
# above it; the n granules from addr freed
def genpool.free.walk(bits: List<&2, Bool>, hit: Bool, past: Bool, +x: Nat, +addr: Nat, +g: Nat, +n: Nat) -> Result<&2, &2, GpError, List<&2, Bool>>:
  match bits hit past:
    case Nil{} True{} _:
      genpool.free.clear(Bits.genpool.bits.used_prefix(Nil{}, n), Nil{}, n)
    case Con{+b, +t} True{} _:
      genpool.free.clear(Bits.genpool.bits.used_prefix(Con{b, t}, n), Con{b, t}, n)
    case Nil{} False{} _:
      Fail{GpMisaligned{}}
    case Con{b, t} False{} True{}:
      Fail{GpMisaligned{}}
    case Con{b, t} False{} False{}:
      +y = Nat.add(x, g)
      genpool.free.cons(b, genpool.free.walk(t, Nat.is_eq(y, addr), Nat.is_lt(addr, y), y, addr, g, n))

def genpool.free.chunk(a: Nat, r: Result<&2, &2, GpError, List<&2, Bool>>, t: List<&2, GpChunk>) -> Result<&2, &2, GpError, List<&2, GpChunk>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{bs}:
      Done{Con{GpChunk{a, bs}, t}}

def genpool.free.ccons(h: GpChunk, r: Result<&2, &2, GpError, List<&2, GpChunk>>) -> Result<&2, &2, GpError, List<&2, GpChunk>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{cs}:
      Done{Con{h, cs}}

# n granules from addr freed in chunk c
def genpool.free.at(cs: List<&2, GpChunk>, c: Nat, +addr: Nat, +n: Nat, +g: Nat) -> Result<&2, &2, GpError, List<&2, GpChunk>>:
  match cs c:
    case Nil{} _:
      Fail{GpNotInPool{}}
    case Con{GpChunk{+a, u}, t} 0n:
      genpool.free.chunk(a, genpool.free.walk(u, Nat.is_eq(a, addr), Nat.is_lt(addr, a), a, addr, g, n), t)
    case Con{h, t} 1n+i:
      genpool.free.ccons(h, genpool.free.at(t, i, addr, n, g))

# addr lies in chunk c
def genpool.inside(+c: GpChunk, +addr: Nat, +g: Nat) -> Bool:
  Bool.and(Nat.is_le(genpool.chunk.addr(c), addr), Nat.is_lt(addr, genpool.chunk.end(c, g)))

def genpool.locate.pick(hit: Bool, +i: Nat, r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{i}
    case False{}:
      r

# the index of the first chunk holding addr
def genpool.locate(cs: List<&2, GpChunk>, +addr: Nat, +g: Nat, +i: Nat) -> Maybe<&2, Nat>:
  match cs:
    case Nil{}:
      None{}
    case Con{+c, t}:
      genpool.locate.pick(genpool.inside(c, addr, g), i, genpool.locate(t, addr, g, 1n+i))

def genpool.free.pool(r: Result<&2, &2, GpError, List<&2, GpChunk>>, +order: Nat, +g: Nat) -> Result<&2, &2, GpError, GpPool>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{cs}:
      Done{GpPool{order, g, cs}}

def genpool.free.found(m: Maybe<&2, Nat>, cs: List<&2, GpChunk>, +addr: Nat, +n: Nat, +order: Nat, +g: Nat) -> Result<&2, &2, GpError, GpPool>:
  match m:
    case None{}:
      Fail{GpNotInPool{}}
    case Some{c}:
      genpool.free.pool(genpool.free.at(cs, c, addr, n, g), order, g)

# the size bytes at addr freed (gen_pool_free): GpBadSize for size 0,
# GpNotInPool when no chunk holds addr, GpMisaligned when addr does not
# start a granule, GpNotInUse when a granule is not allocated
def genpool.free(p: GpPool, +addr: Nat, size: Nat) -> Result<&2, &2, GpError, GpPool>:
  match p size:
    case GpPool{order, g, cs} 0n:
      Fail{GpBadSize{}}
    case GpPool{+order, +g, +cs} 1n+k:
      genpool.free.found(genpool.locate(cs, addr, g, 0n), cs, addr, genpool.granules_for(1n+k, g), order, g)

# Reading a pool

def genpool.granule(p: GpPool) -> Nat:
  match p:
    case GpPool{o, g, cs}:
      g

def genpool.order(p: GpPool) -> Nat:
  match p:
    case GpPool{o, g, cs}:
      o

def genpool.chunks(p: GpPool) -> List<&2, GpChunk>:
  match p:
    case GpPool{o, g, cs}:
      cs

def genpool.chunk.at(cs: List<&2, GpChunk>, c: Nat) -> Maybe<&2, GpChunk>:
  List.get(&2, GpChunk, cs, c)

def genpool.used_at.go(m: Maybe<&2, GpChunk>, j: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{c}:
      Bits.genpool.bits.get(genpool.chunk.used(c), j)

# granule j of chunk c is allocated (False when there is no such granule)
def genpool.used_at(p: GpPool, c: Nat, j: Nat) -> Bool:
  genpool.used_at.go(genpool.chunk.at(genpool.chunks(p), c), j)

def genpool.count_free.go(cs: List<&2, GpChunk>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Con{c, t}:
      Nat.add(Bits.genpool.bits.count_free(genpool.chunk.used(c)), genpool.count_free.go(t))

def genpool.count_used.go(cs: List<&2, GpChunk>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Con{c, t}:
      Nat.add(Bits.genpool.bits.count_used(genpool.chunk.used(c)), genpool.count_used.go(t))

def genpool.count.go(cs: List<&2, GpChunk>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Con{c, t}:
      Nat.add(List.length(&2, Bool, genpool.chunk.used(c)), genpool.count.go(t))

# the bytes free (gen_pool_avail), allocated, and in all (gen_pool_size)
def genpool.avail(p: GpPool) -> Nat:
  match p:
    case GpPool{o, g, cs}:
      Nat.mul(genpool.count_free.go(cs), g)

def genpool.allocated(p: GpPool) -> Nat:
  match p:
    case GpPool{o, g, cs}:
      Nat.mul(genpool.count_used.go(cs), g)

def genpool.size(p: GpPool) -> Nat:
  match p:
    case GpPool{o, g, cs}:
      Nat.mul(genpool.count.go(cs), g)

# the chunks with every granule free: what an allocation or a free leaves
# unchanged
def genpool.blank.go(cs: List<&2, GpChunk>) -> List<&2, GpChunk>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{GpChunk{a, u}, t}:
      Con{GpChunk{a, List.replicate(Bool, List.length(&2, Bool, u), False{})}, genpool.blank.go(t)}

def genpool.blank(p: GpPool) -> GpPool:
  match p:
    case GpPool{o, g, cs}:
      GpPool{o, g, genpool.blank.go(cs)}

# no two chunks overlap
def genpool.disjoint(p: GpPool) -> Bool:
  match p:
    case GpPool{o, +g, cs}:
      genpool.disjoint.go(cs, g)

# the granule size is not 0 and no two chunks overlap: what genpool.new
# makes and every operation keeps
def genpool.valid(+p: GpPool) -> Bool:
  Bool.and(Nat.is_lt(0n, genpool.granule(p)), genpool.disjoint(p))

# chunk c's address and granule count (0 when there is no chunk c)
def genpool.chunk_addr(p: GpPool, c: Nat) -> Nat:
  Maybe.default(&2, Nat, Maybe.map(&2, GpChunk, Nat, h => genpool.chunk.addr(h), genpool.chunk.at(genpool.chunks(p), c)), 0n)

def genpool.chunk_granules(p: GpPool, c: Nat) -> Nat:
  Maybe.default(&2, Nat, Maybe.map(&2, GpChunk, Nat, h => List.length(&2, Bool, genpool.chunk.used(h)), genpool.chunk.at(genpool.chunks(p), c)), 0n)

# the pool after an allocation (p if it failed), and its address
def genpool.state(res: Result<&2, &2, GpError, GpAlloc>, p: GpPool) -> GpPool:
  match res:
    case Fail{e}:
      p
    case Done{GpAlloc{q, a, c, s, n}}:
      q

def genpool.addr(res: Result<&2, &2, GpError, GpAlloc>) -> Maybe<&2, Nat>:
  match res:
    case Fail{e}:
      None{}
    case Done{GpAlloc{q, a, c, s, n}}:
      Some{a}

def genpool.pool(res: Result<&2, &2, GpError, GpPool>, p: GpPool) -> GpPool:
  match res:
    case Fail{e}:
      p
    case Done{q}:
      q
