# bend-osdev-genalloc

A general-purpose pool allocator in the style of the Linux kernel's
genalloc (`gen_pool`), as a pure state machine: address ranges ("chunks")
are added to a pool, allocations are carved out of them, and each fit
algorithm the kernel offers is a template argument.

## What it implements

The behaviour follows the kernel's public documentation of genalloc (the
"The genalloc/genpool subsystem" page of its core API documentation),
restated here in this package's own words; no kernel source was read.

* **Granules.** A pool is created with a minimum allocation order: space is
  managed in granules of `2^order` bytes. Each chunk keeps one bit per
  granule, set while the granule is allocated. A chunk's size is rounded
  down to whole granules.
* **Chunks** are added with `genpool.add(p, addr, size)` (`gen_pool_add`).
  Unlike the kernel, a chunk that overlaps one already in the pool is
  refused (`GpOverlap`), so the pool's chunks never overlap.
* **Allocation**: `genpool.alloc(~fit, p, size, data)` (`gen_pool_alloc_algo`)
  takes `ceil(size / 2^order)` consecutive free granules (at least one) of
  the first chunk, in the order chunks were added, for which the fit
  algorithm answers a place. It answers the new pool, the address, and where
  the allocation lies (`GpAlloc{pool, addr, chunk, first, count}`). The pool
  checks the fit algorithm's answer: if the granules it names are not all
  free and inside the chunk, the allocation fails with `GpBadFit` and nothing
  changes. `genpool.alloc_first(p, size)` is `gen_pool_alloc` with the
  default algorithm, first fit.
* **Fit algorithms** (`fit.bend`), the kernel's:
  * `genpool.first_fit`: the lowest run of free granules that is long
    enough (`gen_pool_first_fit`);
  * `genpool.best_fit`: the start of the shortest free run that is long
    enough, the first of those on ties (`gen_pool_best_fit`);
  * `genpool.first_fit_align`: the lowest free run whose address is a
    multiple of the alignment passed as `GpAlign{align}`
    (`gen_pool_first_fit_align`);
  * `genpool.first_fit_order_align`: the lowest free run whose offset from
    the chunk's start is a multiple of the allocation's size rounded up to a
    power of two (`gen_pool_first_fit_order_align`);
  * `genpool.fixed_offset`: exactly the granules at the byte offset passed as
    `GpOffset{offset}` from the chunk's start, if they are free
    (`gen_pool_fixed_alloc`).
* **Freeing**: `genpool.free(p, addr, size)` (`gen_pool_free`) finds the
  first chunk holding `addr` and frees the granules from `addr` on. Where
  the kernel trusts the caller, it fails instead: `GpNotInPool` (no chunk
  holds `addr`), `GpMisaligned` (`addr` does not start a granule),
  `GpNotInUse` (a granule is not allocated), `GpBadSize` (size 0).
* **Sizes**: `genpool.avail(p)` (`gen_pool_avail`), `genpool.size(p)`
  (`gen_pool_size`) and `genpool.allocated(p)`, in bytes.

## Files

| File | Holds |
|---|---|
| `genalloc.bend` | the types, the pool and its operations: create, add, alloc, free, sizes, reading |
| `fit.bend` | the fit algorithms, and `genpool.alloc_first` |
| `bits.bend` | granule bitmaps: reading, runs, filling, counting (shared by the pool and the fit algorithms) |
| `LAWS.bend`, `PROOF.bend` | the laws and their proofs |
| `proof_nat.bend`, `proof_bits.bend`, `proof_pool.bend` | the lemmas `PROOF.bend` uses: `Nat` arithmetic and order; bitmaps and the walk of `free`; plans, marking and locating chunks |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh` | the differential test (`ref/.gitignore` lists the files it generates) |

## API

| Def or type | Meaning |
|---|---|
| `GpPool` | a pool (opaque: use the defs below) |
| `GpChunk{addr, used}` | a chunk: its address and its granule bits (open, as `genpool.chunks` answers them) |
| `GpAlloc{pool, addr, chunk, first, count}` | what an allocation answers |
| `GpFitData`: `GpNoData`, `GpAlign{align}`, `GpOffset{offset}` | the data a fit algorithm takes |
| `GpError`: `GpBadSize`, `GpNoSpace`, `GpBadFit{chunk}`, `GpOverlap`, `GpNotInPool`, `GpMisaligned`, `GpNotInUse` | why an operation failed |
| `genpool.new(order)` | an empty pool of `2^order`-byte granules |
| `genpool.add(p, addr, size)` | `Result<&2, &2, GpError, GpPool>` |
| `genpool.alloc(~fit, p, size, data)` | `Result<&2, &2, GpError, GpAlloc>` |
| `genpool.alloc_first(p, size)` (fit.bend) | `alloc` with first fit |
| `genpool.free(p, addr, size)` | `Result<&2, &2, GpError, GpPool>` |
| `genpool.avail(p)`, `genpool.allocated(p)`, `genpool.size(p)` | bytes free, allocated, in all |
| `genpool.used_at(p, c, j)` | granule `j` of chunk `c` is allocated |
| `genpool.chunk_addr(p, c)`, `genpool.chunk_granules(p, c)`, `genpool.chunks(p)`, `genpool.granule(p)`, `genpool.order(p)` | reading the pool |
| `genpool.blank(p)` | the pool with every granule free: what alloc and free leave unchanged |
| `genpool.disjoint(p)`, `genpool.valid(p)` | no two chunks overlap; and granules of at least a byte |
| `genpool.state(res, p)`, `genpool.addr(res)`, `genpool.pool(res, p)` | the pool after an allocation or an add/free (`p` if it failed), and an allocation's address |
| `genpool.first_fit`, `genpool.best_fit`, `genpool.first_fit_align`, `genpool.first_fit_order_align`, `genpool.fixed_offset` (fit.bend) | the fit algorithms |
| `genpool.bits.*` (bits.bend) | bitmap helpers for writing a fit algorithm |

Everything else (`genpool.plan`, `genpool.mark`, `genpool.locate`,
`genpool.free.*`, `GpPlan`, `GpRun`, `genpool.fit.*`) is internal.

## Extension points

* **The fit algorithm is a template argument** of type
  `GpFitData -> List<&2, Bool> -> Nat -> Nat -> Nat -> Maybe<&2, Nat>`: the
  data passed to `alloc`, the chunk's granule bits, the number of granules
  wanted, the chunk's address and the granule size, answering the first
  granule to use. A new algorithm is any such def; the laws hold for every
  one, because the pool checks the answer.
* **The minimum allocation order** is the parameter of `genpool.new`.
* **Fit data** is an open type with the kernel's three cases; a new
  algorithm needing other data can take a new case of it (a breaking change
  to the type) or encode it in `GpOffset` / `GpAlign`.
* **The representation is internal**: a chunk's bits are a list, scanned
  from the start (as the kernel scans its bitmap). A faster representation
  (a tree of free runs, or bend-osdev-maple's ranges) can replace it behind
  the same defs; the laws, which use only the public defs, state what it must
  keep.
* **No streaming interface:** a pool is a state machine of discrete
  operations.

## Laws

`LAWS.bend`, for **every** pool, fit algorithm (any def of the type above,
lawful or not), size, address and fit data:

* `avail_size`: free plus allocated bytes is the pool's size;
* for every allocation that answers `Done{GpAlloc{q, a, c, s, n}}`:
  * `alloc_inside`: `n >= 1` and `s + n` is at most chunk `c`'s granule
    count, so the allocation lies inside its chunk;
  * `alloc_addr`: `a` is chunk `c`'s address plus `s` granules;
  * `alloc_was_free`: every granule from `s` to `s + n - 1` of chunk `c` was
    free before, so the allocation overlaps no allocation already made;
  * `alloc_in_use`: and is allocated after;
  * `alloc_others`: every other granule of every chunk is unchanged;
  * `alloc_blank`: no chunk's address or size changes;
  * `alloc_avail`: the free bytes drop by `n` granules;
* on a **valid** pool (`genpool.valid`: granules of at least one byte, no two
  chunks overlapping):
  * `free_alloc`: freeing an allocation's address and size gives back
    exactly the pool from before it;
  * `realloc`: so allocating again after the free gives the same allocation;
* `new_valid`, `add_valid`, `alloc_valid`, `free_valid`: a new pool is
  valid, and `add`, `alloc` and `free` keep a pool valid; so every pool built
  with this package's operations is valid;
* **vectors:** first fit, aligned fit, and a refused overlapping chunk.

Not stated as laws: which place each fit algorithm picks (that the first fit
is the lowest, the best fit the shortest run). These are tested against the
model below.

## Tests

`ref/run.sh` runs 40 random sequences (1233 operations: adds, some
overlapping or too small; allocations with every fit algorithm, sizes 0 to
12 granules, random alignments and offsets; frees of random addresses and of
real allocations) on pools of granule orders 0, 2, 4 and 6, and compares
every result, and the sizes at the end, with a model in Python. There is no
pool allocator outside this repository to compare with (the kernel's lives
inside the kernel), so the model is written in `ref/gen.py` from the
behaviour above and shares an author with the package.

## Limitations

* Addresses and sizes are `Nat`; a native build holds a `Nat` below 2^48, so
  a pool of kernel virtual addresses above that should hold offsets from a
  base instead.
* The scans are linear in the chunk's granules (first fit is quadratic in
  the worst case), as the bit-per-granule list is walked from the start.
* No per-NUMA-node chunks (`nid`), no `gen_pool_dma_alloc` or
  `gen_pool_virt_to_phys` (a chunk has one address), and no
  `gen_pool_for_each_chunk` beyond `genpool.chunks`.

## Relation to idalloc and maple

The interface follows bend-osdev-idalloc's: an allocation answers the new
state and what was allocated in one record, with `genpool.state` and
`genpool.addr` beside it, and the laws have the same shape (was free before,
in use after, nothing else changes, free then allocate again gives the same
answer). bend-osdev-maple's `empty_area` gap search finds a free range in a
range tree; genalloc keeps the kernel's bitmap-per-chunk model instead, so
that each fit algorithm works on a granule bitmap as the kernel's do.
Neither is imported.

## Dependencies

None: Base only (`DEPS` is empty).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 1233 operations in 40 sequences match,
`scripts/deps.sh genalloc` ok.
