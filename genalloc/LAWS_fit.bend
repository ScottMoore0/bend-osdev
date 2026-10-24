# Where the fit algorithms (fit.bend) place an allocation, for every fit
# data, granule bitmap, run length n, chunk address and granule size:
#
# * first fit answers a free run of n granules, and no run of n granules
#   starting lower is free; when it answers None (and n >= 1), no run of n
#   granules is free anywhere;
# * first fit with an alignment (GpAlign{al}) does the same over the runs
#   whose address base + s * g is a multiple of al (al of 0 taken as 1).
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
