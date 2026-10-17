# bend-osdev-idalloc: ID allocation in the style of the kernel's IDR and IDA.
#
# An Idr<V> hands out small integer IDs, each mapped to a value of type V:
# allocation takes the lowest free ID within a range [min, max] and stores
# the value under it; find looks a value up; remove frees an ID; replace
# changes the value of an ID in use. An IDA allocates IDs alone: it is an
# Idr<Unit>, and the ida.* defs are the same operations without values.
#
# The state is a list of slots, slot i for ID i (None when the ID is free),
# as long as the highest ID ever allocated, plus one. Allocation is linear
# in the ID it returns; see the README.
import Base

# Types

type IdError is Data:
  IdExhausted{}
  IdBadRange{}
  IdNotFound{}

# the IDs allocation may hand out: min to max, both included
type IdRange is Data:
  IdRange{min: Nat, max: Nat}

type Idr<-V: Data> is Data:
  Idr{slots: List<&2, Maybe<&2, V>>}

# what an allocation answers: the new state and the ID
type IdrAlloc<-V: Data> is Data:
  IdrAlloc{map: Idr<V>, id: Nat}

# what a replace answers: the new state and the old value
type IdrOld<-V: Data> is Data:
  IdrOld{map: Idr<V>, old: V}

# The default range: 0 to 2^31 - 1, the IDs the kernel's allocators hand
# out by default (its non-negative int)
def id.max_default() -> Nat:
  2147483647n

def id.range_default() -> IdRange:
  IdRange{0n, id.max_default()}

def id.range_min(min: Nat) -> IdRange:
  IdRange{min, id.max_default()}

# Slots

def idr.slots.get(-V: Data, xs: List<&2, Maybe<&2, V>>, i: Nat) -> Maybe<&2, V>:
  match xs i:
    case Nil{} _:
      None{}
    case Con{m, t} 0n:
      m
    case Con{m, t} 1n+j:
      idr.slots.get(V, t, j)

# slot i set to m, the list grown with free slots if it is shorter
def idr.slots.put(-V: Data, xs: List<&2, Maybe<&2, V>>, i: Nat, m: Maybe<&2, V>) -> List<&2, Maybe<&2, V>>:
  match xs i:
    case Nil{} 0n:
      Con{m, Nil{}}
    case Nil{} 1n+j:
      Con{None{}, idr.slots.put(V, Nil{}, j, m)}
    case Con{h, t} 0n:
      Con{m, t}
    case Con{h, t} 1n+j:
      Con{h, idr.slots.put(V, t, j, m)}

# slot i freed (the list is unchanged past its end)
def idr.slots.clear(-V: Data, xs: List<&2, Maybe<&2, V>>, i: Nat) -> List<&2, Maybe<&2, V>>:
  match xs i:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      Con{None{}, t}
    case Con{h, t} 1n+j:
      Con{h, idr.slots.clear(V, t, j)}

# the lowest free slot at or after min (every slot past the end is free)
def idr.slots.free_from(-V: Data, xs: List<&2, Maybe<&2, V>>, min: Nat) -> Nat:
  match xs min:
    case Nil{} m:
      m
    case Con{h, t} 1n+m:
      1n+idr.slots.free_from(V, t, m)
    case Con{None{}, t} 0n:
      0n
    case Con{Some{x}, t} 0n:
      1n+idr.slots.free_from(V, t, 0n)

# IDR

def idr.new(-V: Data) -> Idr<V>:
  Idr{Nil{}}

# the value of ID id, if it is in use
def idr.find(-V: Data, r: Idr<V>, id: Nat) -> Maybe<&2, V>:
  match r:
    case Idr{xs}:
      idr.slots.get(V, xs, id)

def idr.in_use(-V: Data, r: Idr<V>, id: Nat) -> Bool:
  Maybe.is_some(&2, V, idr.find(V, r, id))

def idr.alloc.at(-V: Data, fits: Bool, xs: List<&2, Maybe<&2, V>>, +i: Nat, v: V) -> Result<&2, &2, IdError, IdrAlloc<V>>:
  match fits:
    case True{}:
      Done{IdrAlloc{Idr{idr.slots.put(V, xs, i, Some{v})}, i}}
    case False{}:
      Fail{IdExhausted{}}

def idr.alloc.order(-V: Data, ordered: Bool, +xs: List<&2, Maybe<&2, V>>, min: Nat, +max: Nat, v: V) -> Result<&2, &2, IdError, IdrAlloc<V>>:
  match ordered:
    case True{}:
      +i = idr.slots.free_from(V, xs, min)
      idr.alloc.at(V, Nat.is_le(i, max), xs, i, v)
    case False{}:
      Fail{IdBadRange{}}

# the lowest free ID in the range, now mapped to v; IdExhausted if every ID
# in the range is in use, IdBadRange if max < min (idr_alloc)
def idr.alloc_range(-V: Data, r: Idr<V>, rg: IdRange, v: V) -> Result<&2, &2, IdError, IdrAlloc<V>>:
  match r rg:
    case Idr{xs} IdRange{+min, +max}:
      idr.alloc.order(V, Nat.is_le(min, max), xs, min, max, v)

def idr.alloc(-V: Data, r: Idr<V>, v: V) -> Result<&2, &2, IdError, IdrAlloc<V>>:
  idr.alloc_range(V, r, id.range_default(), v)

def idr.alloc_min(-V: Data, r: Idr<V>, min: Nat, v: V) -> Result<&2, &2, IdError, IdrAlloc<V>>:
  idr.alloc_range(V, r, id.range_min(min), v)

# ID id freed; the value it had, if it was in use (idr_remove)
def idr.remove(-V: Data, r: Idr<V>, +id: Nat) -> Idr<V> & Maybe<&2, V>:
  match r:
    case Idr{+xs}:
      (Idr{idr.slots.clear(V, xs, id)}, idr.slots.get(V, xs, id))

# ID id freed
def idr.free(-V: Data, r: Idr<V>, id: Nat) -> Idr<V>:
  match r:
    case Idr{xs}:
      Idr{idr.slots.clear(V, xs, id)}

def idr.replace.at(-V: Data, m: Maybe<&2, V>, xs: List<&2, Maybe<&2, V>>, id: Nat, v: V) -> Result<&2, &2, IdError, IdrOld<V>>:
  match m:
    case None{}:
      Fail{IdNotFound{}}
    case Some{old}:
      Done{IdrOld{Idr{idr.slots.put(V, xs, id, Some{v})}, old}}

# ID id, in use, now mapped to v; its old value. IdNotFound if it is free
# (idr_replace)
def idr.replace(-V: Data, r: Idr<V>, +id: Nat, v: V) -> Result<&2, &2, IdError, IdrOld<V>>:
  match r:
    case Idr{+xs}:
      idr.replace.at(V, idr.slots.get(V, xs, id), xs, id, v)

# the IDs in use, in increasing order
def idr.ids.go(-V: Data, xs: List<&2, Maybe<&2, V>>, +i: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{None{}, t}:
      idr.ids.go(V, t, 1n+i)
    case Con{Some{x}, t}:
      Con{i, idr.ids.go(V, t, 1n+i)}

def idr.ids(-V: Data, r: Idr<V>) -> List<&2, Nat>:
  match r:
    case Idr{xs}:
      idr.ids.go(V, xs, 0n)

# what an allocation leaves: the new state if it succeeded, else r
def idr.state(-V: Data, res: Result<&2, &2, IdError, IdrAlloc<V>>, r: Idr<V>) -> Idr<V>:
  match res:
    case Fail{e}:
      r
    case Done{IdrAlloc{t, i}}:
      t

# the ID an allocation answered, if it succeeded
def idr.id(-V: Data, res: Result<&2, &2, IdError, IdrAlloc<V>>) -> Maybe<&2, Nat>:
  match res:
    case Fail{e}:
      None{}
    case Done{IdrAlloc{t, i}}:
      Some{i}

# IDA: an Idr<Unit>

def ida.new() -> Idr<Unit>:
  idr.new(Unit)

# the lowest free ID in the range, now in use (ida_alloc_range)
def ida.alloc_range(s: Idr<Unit>, rg: IdRange) -> Result<&2, &2, IdError, IdrAlloc<Unit>>:
  idr.alloc_range(Unit, s, rg, Unit{})

# the lowest free ID (ida_alloc)
def ida.alloc(s: Idr<Unit>) -> Result<&2, &2, IdError, IdrAlloc<Unit>>:
  ida.alloc_range(s, id.range_default())

# the lowest free ID at or above min (ida_alloc_min)
def ida.alloc_min(s: Idr<Unit>, min: Nat) -> Result<&2, &2, IdError, IdrAlloc<Unit>>:
  ida.alloc_range(s, id.range_min(min))

# ID id freed; freeing a free ID changes nothing (ida_free)
def ida.free(s: Idr<Unit>, id: Nat) -> Idr<Unit>:
  idr.free(Unit, s, id)

def ida.in_use(s: Idr<Unit>, id: Nat) -> Bool:
  idr.in_use(Unit, s, id)

def ida.ids(s: Idr<Unit>) -> List<&2, Nat>:
  idr.ids(Unit, s)

def ida.state(res: Result<&2, &2, IdError, IdrAlloc<Unit>>, s: Idr<Unit>) -> Idr<Unit>:
  idr.state(Unit, res, s)

def ida.id(res: Result<&2, &2, IdError, IdrAlloc<Unit>>) -> Maybe<&2, Nat>:
  idr.id(Unit, res)
