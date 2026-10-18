# bend-osdev-genalloc, granule bitmaps: one Bool per granule of a chunk,
# True when the granule is allocated. The pool and the fit algorithms
# share these; a custom fit algorithm can use them too.
import Base

# granule j: allocated? (False past the end)
def genpool.bits.get(bits: List<&2, Bool>, j: Nat) -> Bool:
  match bits j:
    case Nil{} _:
      False{}
    case Con{b, t} 0n:
      b
    case Con{b, t} 1n+i:
      genpool.bits.get(t, i)

# the first n granules exist and are free
def genpool.bits.free_prefix(bits: List<&2, Bool>, n: Nat) -> Bool:
  match bits n:
    case _ 0n:
      True{}
    case Nil{} 1n+m:
      False{}
    case Con{b, t} 1n+m:
      Bool.and(Bool.not(b), genpool.bits.free_prefix(t, m))

# the first n granules exist and are allocated
def genpool.bits.used_prefix(bits: List<&2, Bool>, n: Nat) -> Bool:
  match bits n:
    case _ 0n:
      True{}
    case Nil{} 1n+m:
      False{}
    case Con{b, t} 1n+m:
      Bool.and(b, genpool.bits.used_prefix(t, m))

# granules s to s + n - 1 exist and are free
def genpool.bits.run_free(bits: List<&2, Bool>, s: Nat, n: Nat) -> Bool:
  genpool.bits.free_prefix(List.drop(&2, Bool, bits, s), n)

# the first n granules set to v (those past the end ignored)
def genpool.bits.fill_prefix(bits: List<&2, Bool>, n: Nat, +v: Bool) -> List<&2, Bool>:
  match bits n:
    case Nil{} _:
      Nil{}
    case Con{b, t} 0n:
      Con{b, t}
    case Con{b, t} 1n+m:
      Con{v, genpool.bits.fill_prefix(t, m, v)}

# granules s to s + n - 1 set to v (those past the end ignored)
def genpool.bits.fill(bits: List<&2, Bool>, s: Nat, +n: Nat, +v: Bool) -> List<&2, Bool>:
  match bits s:
    case Nil{} _:
      Nil{}
    case Con{b, t} 0n:
      genpool.bits.fill_prefix(Con{b, t}, n, v)
    case Con{b, t} 1n+i:
      Con{b, genpool.bits.fill(t, i, n, v)}

def genpool.bits.count_used(bits: List<&2, Bool>) -> Nat:
  match bits:
    case Nil{}:
      0n
    case Con{True{}, t}:
      1n+genpool.bits.count_used(t)
    case Con{False{}, t}:
      genpool.bits.count_used(t)

def genpool.bits.count_free(bits: List<&2, Bool>) -> Nat:
  match bits:
    case Nil{}:
      0n
    case Con{True{}, t}:
      genpool.bits.count_free(t)
    case Con{False{}, t}:
      1n+genpool.bits.count_free(t)
