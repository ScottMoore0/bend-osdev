# bend-osdev-genalloc, the fit algorithms: where in a chunk an allocation
# goes, the counterparts of the kernel's gen_pool_first_fit,
# gen_pool_best_fit, gen_pool_first_fit_align,
# gen_pool_first_fit_order_align and gen_pool_fixed_alloc.
#
# A fit algorithm is any def of type
#   GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>
# taking the data passed to genpool.alloc, the chunk's granule bits, the
# number of granules wanted, the chunk's address and the granule size, and
# answering the first granule to use (None: this chunk has no room). It is
# passed to genpool.alloc as a template argument; the pool checks its answer.
import Base
import ./bits.bend as Bits
import ./genalloc.bend as G

# whether granule s can start the allocation: the granules are free, and
# off + s * g is a multiple of a
def genpool.fit.cand(+full: List<&2, Bool>, +s: Nat, +n: Nat, +off: Nat, +g: Nat, +a: Nat) -> Bool:
  Bool.and(Nat.is_eq(Nat.mod(Nat.add(off, Nat.mul(s, g)), a), 0n), Bits.genpool.bits.run_free(full, s, n))

# the lowest candidate from s on; ok says whether s is one
def genpool.fit.scan(rest: List<&2, Bool>, ok: Bool, +full: List<&2, Bool>, +n: Nat, +s: Nat, +off: Nat, +g: Nat, +a: Nat) -> Maybe<&2, Nat>:
  match rest ok:
    case r True{}:
      Some{s}
    case Nil{} False{}:
      None{}
    case Con{b, t} False{}:
      genpool.fit.scan(t, genpool.fit.cand(full, 1n+s, n, off, g, a), full, n, 1n+s, off, g, a)

# the lowest granule s whose run of n is free and with off + s * g a
# multiple of a (a of 0 taken as 1)
def genpool.fit.lowest(+bits: List<&2, Bool>, +n: Nat, +off: Nat, +g: Nat, a: Nat) -> Maybe<&2, Nat>:
  +a1 = Nat.max(a, 1n)
  genpool.fit.scan(bits, genpool.fit.cand(bits, 0n, n, off, g, a1), bits, n, 0n, off, g, a1)

# the first free run of n granules (gen_pool_first_fit)
def genpool.first_fit(data: G.GpFitData, bits: List<&2, Bool>, n: Nat, base: Nat, g: Nat) -> Maybe<&2, Nat>:
  genpool.fit.lowest(bits, n, 0n, g, 1n)

def genpool.fit.align(data: G.GpFitData) -> Nat:
  match data:
    case G.GpAlign{a}:
      a
    case G.GpNoData{}:
      1n
    case G.GpOffset{o}:
      1n

# the first free run of n granules whose address is a multiple of the
# alignment given as GpAlign{align} (gen_pool_first_fit_align)
def genpool.first_fit_align(data: G.GpFitData, bits: List<&2, Bool>, n: Nat, base: Nat, g: Nat) -> Maybe<&2, Nat>:
  genpool.fit.lowest(bits, n, base, g, genpool.fit.align(data))

def genpool.fit.pow2.go(fuel: Nat, done: Bool, +p: Nat, +n: Nat) -> Nat:
  match fuel done:
    case _ True{}:
      p
    case 0n False{}:
      p
    case 1n+f False{}:
      genpool.fit.pow2.go(f, Nat.is_le(n, Nat.double(p)), Nat.double(p), n)

# the least power of two at least n (1 for 0)
def genpool.fit.pow2(+n: Nat) -> Nat:
  genpool.fit.pow2.go(48n, Nat.is_le(n, 1n), 1n, n)

# the first free run of n granules starting at a multiple of n rounded up
# to a power of two, counted from the chunk's start
# (gen_pool_first_fit_order_align)
def genpool.fit.order_align(+bits: List<&2, Bool>, +n: Nat, +g: Nat) -> Maybe<&2, Nat>:
  genpool.fit.lowest(bits, n, 0n, g, Nat.mul(genpool.fit.pow2(n), g))

def genpool.first_fit_order_align(data: G.GpFitData, bits: List<&2, Bool>, n: Nat, base: Nat, g: Nat) -> Maybe<&2, Nat>:
  genpool.fit.order_align(bits, n, g)

def genpool.fit.fixed.at(ok: Bool, +s: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{s}
    case False{}:
      None{}

def genpool.fit.fixed(+off: Nat, +bits: List<&2, Bool>, +n: Nat, +g: Nat) -> Maybe<&2, Nat>:
  +s = Nat.div(off, g)
  genpool.fit.fixed.at(Bool.and(Nat.is_eq(Nat.mod(off, g), 0n), Bits.genpool.bits.run_free(bits, s, n)), s)

# the n granules at the byte offset given as GpOffset{offset} from the
# chunk's start, if they are free (gen_pool_fixed_alloc)
def genpool.fixed_offset(data: G.GpFitData, bits: List<&2, Bool>, n: Nat, base: Nat, g: Nat) -> Maybe<&2, Nat>:
  match data:
    case G.GpOffset{off}:
      genpool.fit.fixed(off, bits, n, g)
    case G.GpNoData{}:
      None{}
    case G.GpAlign{a}:
      None{}

# Best fit

# a maximal run of free granules
type GpRun is Data:
  GpRun{start: Nat, len: Nat}

def genpool.fit.runs.close(+start: Nat, len: Nat, r: List<&2, GpRun>) -> List<&2, GpRun>:
  match len:
    case 0n:
      r
    case 1n+k:
      Con{GpRun{start, 1n+k}, r}

# the free runs from granule i on, the current one starting at start with
# len granules so far
def genpool.fit.runs.go(bits: List<&2, Bool>, +i: Nat, +start: Nat, +len: Nat) -> List<&2, GpRun>:
  match bits:
    case Nil{}:
      genpool.fit.runs.close(start, len, Nil{})
    case Con{False{}, t}:
      genpool.fit.runs.go(t, 1n+i, start, 1n+len)
    case Con{True{}, t}:
      genpool.fit.runs.close(start, len, genpool.fit.runs.go(t, 1n+i, 1n+i, 0n))

def genpool.fit.runs(bits: List<&2, Bool>) -> List<&2, GpRun>:
  genpool.fit.runs.go(bits, 0n, 0n, 0n)

def genpool.fit.run_len(r: GpRun) -> Nat:
  match r:
    case GpRun{s, l}:
      l

def genpool.fit.run_start(r: GpRun) -> Nat:
  match r:
    case GpRun{s, l}:
      s

def genpool.fit.better(fits: Bool, +r: GpRun, best: Maybe<&2, GpRun>) -> Maybe<&2, GpRun>:
  match fits best:
    case False{} b:
      b
    case True{} None{}:
      Some{r}
    case True{} Some{GpRun{+s, +l}}:
      Bool.pick(Maybe<&2, GpRun>, Nat.is_lt(genpool.fit.run_len(r), l), Some{r}, Some{GpRun{s, l}})

# the shortest run of at least n granules, the first of those on ties
def genpool.fit.best.go(rs: List<&2, GpRun>, +n: Nat, best: Maybe<&2, GpRun>) -> Maybe<&2, GpRun>:
  match rs:
    case Nil{}:
      best
    case Con{+r, t}:
      genpool.fit.best.go(t, n, genpool.fit.better(Nat.is_le(n, genpool.fit.run_len(r)), r, best))

# the start of the smallest free run that holds n granules
# (gen_pool_best_fit)
def genpool.best_fit(data: G.GpFitData, bits: List<&2, Bool>, n: Nat, base: Nat, g: Nat) -> Maybe<&2, Nat>:
  Maybe.map(&2, GpRun, Nat, r => genpool.fit.run_start(r), genpool.fit.best.go(genpool.fit.runs(bits), n, None{}))

# Allocating with the defaults

# size bytes, first fit (gen_pool_alloc with the default algorithm)
def genpool.alloc_first(p: G.GpPool, size: Nat) -> Result<&2, &2, G.GpError, G.GpAlloc>:
  G.genpool.alloc(~genpool.first_fit, p, size, G.GpNoData{})
