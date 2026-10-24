# Where the fit algorithms (fit.bend) place an allocation, for every fit
# data, granule bitmap, run length n, chunk address and granule size:
#
# * first fit answers a free run of n granules, and no run of n granules
#   starting lower is free; when it answers None (and n >= 1), no run of n
#   granules is free anywhere;
# * first fit with an alignment (GpAlign{al}) does the same over the runs
#   whose address base + s * g is a multiple of al (al of 0 taken as 1);
# * first fit with the order alignment answers a free run of n granules;
# * the fixed offset answers exactly the granules at the offset, when the
#   offset is a whole number of granules and they are free;
# * best fit answers the start of a maximal free run of n or more granules
#   no longer than any other, and shorter than any that starts before it;
#   when it answers None (and n >= 1), no run of n granules is free.
import Base
import ./bits.bend as Bits
import ./genalloc.bend as G
import ./fit.bend as F

# First fit: the lowest free run

law first_fit_free:
  for +d: G.GpFitData
  for +bits: List<&2, Bool>
  for +n: Nat
  for +base: Nat
  for +g: Nat
  for +s: Nat
  for e: {F.genpool.first_fit(d, bits, n, base, g) == Some{s} : Maybe<&2, Nat>}
  {Bits.genpool.bits.run_free(bits, s, n) == True{} : Bool}

law first_fit_lowest:
  for +d: G.GpFitData
  for +bits: List<&2, Bool>
  for +n: Nat
  for +base: Nat
  for +g: Nat
  for +s: Nat
  for +j: Nat
  for e: {F.genpool.first_fit(d, bits, n, base, g) == Some{s} : Maybe<&2, Nat>}
  for h: {Nat.is_lt(j, s) == True{} : Bool}
  {Bits.genpool.bits.run_free(bits, j, n) == False{} : Bool}

law first_fit_none:
  for +d: G.GpFitData
  for +bits: List<&2, Bool>
  for +n: Nat
  for +base: Nat
  for +g: Nat
  for +j: Nat
  for e: {F.genpool.first_fit(d, bits, n, base, g) == None{} : Maybe<&2, Nat>}
  for hn: {Nat.is_lt(0n, n) == True{} : Bool}
  {Bits.genpool.bits.run_free(bits, j, n) == False{} : Bool}

# First fit with an alignment: the lowest free run at an aligned address

law first_fit_align_free:
  for +al: Nat
  for +bits: List<&2, Bool>
  for +n: Nat
  for +base: Nat
  for +g: Nat
  for +s: Nat
  for e: {F.genpool.first_fit_align(G.GpAlign{al}, bits, n, base, g) == Some{s} : Maybe<&2, Nat>}
  {Bool.and(Nat.is_eq(Nat.mod(Nat.add(base, Nat.mul(s, g)), Nat.max(al, 1n)), 0n), Bits.genpool.bits.run_free(bits, s, n)) == True{} : Bool}

law first_fit_align_lowest:
  for +al: Nat
  for +bits: List<&2, Bool>
  for +n: Nat
  for +base: Nat
  for +g: Nat
  for +s: Nat
  for +j: Nat
  for e: {F.genpool.first_fit_align(G.GpAlign{al}, bits, n, base, g) == Some{s} : Maybe<&2, Nat>}
  for h: {Nat.is_lt(j, s) == True{} : Bool}
  {Bool.and(Nat.is_eq(Nat.mod(Nat.add(base, Nat.mul(j, g)), Nat.max(al, 1n)), 0n), Bits.genpool.bits.run_free(bits, j, n)) == False{} : Bool}

law first_fit_align_none:
  for +al: Nat
  for +bits: List<&2, Bool>
  for +n: Nat
  for +base: Nat
  for +g: Nat
  for +j: Nat
  for e: {F.genpool.first_fit_align(G.GpAlign{al}, bits, n, base, g) == None{} : Maybe<&2, Nat>}
  for hn: {Nat.is_lt(0n, n) == True{} : Bool}
  {Bool.and(Nat.is_eq(Nat.mod(Nat.add(base, Nat.mul(j, g)), Nat.max(al, 1n)), 0n), Bits.genpool.bits.run_free(bits, j, n)) == False{} : Bool}

# First fit with the order alignment: the answer is a free run

law first_fit_order_align_free:
  for +d: G.GpFitData
  for +bits: List<&2, Bool>
  for +n: Nat
  for +base: Nat
  for +g: Nat
  for +s: Nat
  for e: {F.genpool.first_fit_order_align(d, bits, n, base, g) == Some{s} : Maybe<&2, Nat>}
  {Bits.genpool.bits.run_free(bits, s, n) == True{} : Bool}

# The fixed offset: exactly the granules at the offset, if they are free and
# the offset is a whole number of granules; nothing without GpOffset

law fixed_offset_at:
  for +off: Nat
  for +bits: List<&2, Bool>
  for +n: Nat
  for +base: Nat
  for +g: Nat
  for +s: Nat
  for e: {F.genpool.fixed_offset(G.GpOffset{off}, bits, n, base, g) == Some{s} : Maybe<&2, Nat>}
  {s == Nat.div(off, g) : Nat}

law fixed_offset_free:
  for +off: Nat
  for +bits: List<&2, Bool>
  for +n: Nat
  for +base: Nat
  for +g: Nat
  for +s: Nat
  for e: {F.genpool.fixed_offset(G.GpOffset{off}, bits, n, base, g) == Some{s} : Maybe<&2, Nat>}
  {Bool.and(Nat.is_eq(Nat.mod(off, g), 0n), Bits.genpool.bits.run_free(bits, Nat.div(off, g), n)) == True{} : Bool}

law fixed_offset_none:
  for +off: Nat
  for +bits: List<&2, Bool>
  for +n: Nat
  for +base: Nat
  for +g: Nat
  for e: {F.genpool.fixed_offset(G.GpOffset{off}, bits, n, base, g) == None{} : Maybe<&2, Nat>}
  {Bool.and(Nat.is_eq(Nat.mod(off, g), 0n), Bits.genpool.bits.run_free(bits, Nat.div(off, g), n)) == False{} : Bool}

law fixed_offset_no_data:
  for bits: List<&2, Bool>
  for n: Nat
  for base: Nat
  for g: Nat
  {F.genpool.fixed_offset(G.GpNoData{}, bits, n, base, g) == None{} : Maybe<&2, Nat>}

law fixed_offset_align_data:
  for a: Nat
  for bits: List<&2, Bool>
  for n: Nat
  for base: Nat
  for g: Nat
  {F.genpool.fixed_offset(G.GpAlign{a}, bits, n, base, g) == None{} : Maybe<&2, Nat>}

# Best fit: the shortest free run long enough, the first of those on ties.
# A maximal free run of l granules at s (bf.maximal): l >= 1 granules from
# s are free, s is 0 or the granule before it is allocated, and the
# granule after them is allocated or past the end.

def bf.left(bits: List<&2, Bool>, s: Nat) -> Bool:
  match s:
    case 0n:
      True{}
    case 1n+p:
      Bits.genpool.bits.get(bits, p)

def bf.right(+bits: List<&2, Bool>, +e: Nat) -> Bool:
  Bool.or(Nat.is_le(List.length(&2, Bool, bits), e), Bits.genpool.bits.get(bits, e))

def bf.maximal(+bits: List<&2, Bool>, +s: Nat, +l: Nat) -> Bool:
  Bool.and(Nat.is_lt(0n, l), Bool.and(Bits.genpool.bits.run_free(bits, s, l), Bool.and(bf.left(bits, s), bf.right(bits, Nat.add(s, l)))))

law best_fit_free:
  for +d: G.GpFitData
  for +bits: List<&2, Bool>
  for +n: Nat
  for +base: Nat
  for +g: Nat
  for +s: Nat
  for e: {F.genpool.best_fit(d, bits, n, base, g) == Some{s} : Maybe<&2, Nat>}
  {Bits.genpool.bits.run_free(bits, s, n) == True{} : Bool}

law best_fit_starts:
  for +d: G.GpFitData
  for +bits: List<&2, Bool>
  for +n: Nat
  for +base: Nat
  for +g: Nat
  for +s: Nat
  for e: {F.genpool.best_fit(d, bits, n, base, g) == Some{s} : Maybe<&2, Nat>}
  {bf.left(bits, s) == True{} : Bool}

law best_fit_shortest:
  for +d: G.GpFitData
  for +bits: List<&2, Bool>
  for +n: Nat
  for +base: Nat
  for +g: Nat
  for +s: Nat
  for +l: Nat
  for +s2: Nat
  for +l2: Nat
  for e: {F.genpool.best_fit(d, bits, n, base, g) == Some{s} : Maybe<&2, Nat>}
  for h1: {bf.maximal(bits, s, l) == True{} : Bool}
  for h2: {bf.maximal(bits, s2, l2) == True{} : Bool}
  for h3: {Nat.is_le(n, l2) == True{} : Bool}
  {Nat.is_le(l, l2) == True{} : Bool}

law best_fit_first:
  for +d: G.GpFitData
  for +bits: List<&2, Bool>
  for +n: Nat
  for +base: Nat
  for +g: Nat
  for +s: Nat
  for +l: Nat
  for +s2: Nat
  for +l2: Nat
  for e: {F.genpool.best_fit(d, bits, n, base, g) == Some{s} : Maybe<&2, Nat>}
  for h1: {bf.maximal(bits, s, l) == True{} : Bool}
  for h2: {bf.maximal(bits, s2, l2) == True{} : Bool}
  for h3: {Nat.is_le(n, l2) == True{} : Bool}
  for h4: {Nat.is_lt(s2, s) == True{} : Bool}
  {Nat.is_lt(l, l2) == True{} : Bool}

law best_fit_none:
  for +d: G.GpFitData
  for +bits: List<&2, Bool>
  for +n: Nat
  for +base: Nat
  for +g: Nat
  for +j: Nat
  for e: {F.genpool.best_fit(d, bits, n, base, g) == None{} : Maybe<&2, Nat>}
  for hn: {Nat.is_lt(0n, n) == True{} : Bool}
  {Bits.genpool.bits.run_free(bits, j, n) == False{} : Bool}
