# bend-osdev-ringbuf, the reference: a ring as the list of its elements,
# oldest first, and its capacity. Written to be obviously correct; the
# Array ring of ringbuf.bend is the fast implementation of the same
# interface (the laws in LAWS.bend and the differential test in ref/ hold
# the two together).
import Base
import ./ringbuf.bend as R

type RingModel is Data:
  RingModel{cap: Nat, items: List<&2, U32>}

# an empty model of 2^order slots, like ring.new
def model.new(+order: Nat) -> RingModel:
  RingModel{R.ring.size(order), Nil{}}

def model.items(m: RingModel) -> List<&2, U32>:
  match m:
    case RingModel{cap, items}:
      items

def model.capacity(m: RingModel) -> Nat:
  match m:
    case RingModel{cap, items}:
      cap

def model.len(m: RingModel) -> Nat:
  match m:
    case RingModel{cap, items}:
      List.length(&2, U32, items)

def model.avail(m: RingModel) -> Nat:
  match m:
    case RingModel{cap, items}:
      Nat.sub(cap, List.length(&2, U32, items))

def model.is_empty(m: RingModel) -> Bool:
  match m:
    case RingModel{cap, items}:
      Nat.is_eq(List.length(&2, U32, items), 0n)

def model.is_full(m: RingModel) -> Bool:
  match m:
    case RingModel{cap, items}:
      Nat.is_eq(List.length(&2, U32, items), cap)

# the length is at most the capacity
def model.valid(m: RingModel) -> Bool:
  match m:
    case RingModel{cap, items}:
      Nat.is_le(List.length(&2, U32, items), cap)

def model.push.go(full: Bool, +cap: Nat, items: List<&2, U32>, x: U32) -> RingModel & Result<&2, &2, R.RingError, Unit>:
  match full:
    case True{}:
      (RingModel{cap, items}, Fail{R.RingFull{}})
    case False{}:
      (RingModel{cap, List.append(&2, U32, items, Con{x, Nil{}})}, Done{Unit{}})

# x appended at the end; RingFull if the model is full
def model.push(m: RingModel, x: U32) -> RingModel & Result<&2, &2, R.RingError, Unit>:
  match m:
    case RingModel{+cap, +items}:
      model.push.go(Nat.is_eq(List.length(&2, U32, items), cap), cap, items, x)

# the first element removed; RingEmpty if there is none
def model.pop(m: RingModel) -> RingModel & Result<&2, &2, R.RingError, U32>:
  match m:
    case RingModel{cap, items}:
      match items:
        case Nil{}:
          (RingModel{cap, Nil{}}, Fail{R.RingEmpty{}})
        case Con{h, t}:
          (RingModel{cap, t}, Done{h})

# the first element, left in place
def model.peek(m: RingModel) -> RingModel & Result<&2, &2, R.RingError, U32>:
  match m:
    case RingModel{cap, items}:
      match items:
        case Nil{}:
          (RingModel{cap, Nil{}}, Fail{R.RingEmpty{}})
        case Con{+h, t}:
          (RingModel{cap, Con{h, t}}, Done{h})

# the first elements of xs that fit, appended; how many
def model.push_list(m: RingModel, +xs: List<&2, U32>) -> RingModel & Nat:
  match m:
    case RingModel{+cap, +items}:
      +n = Nat.min(List.length(&2, U32, xs), Nat.sub(cap, List.length(&2, U32, items)))
      (RingModel{cap, List.append(&2, U32, items, List.take(&2, U32, xs, n))}, n)

# the first n elements (all of them if there are fewer), removed
def model.pop_list(m: RingModel, +n: Nat) -> RingModel & List<&2, U32>:
  match m:
    case RingModel{cap, +items}:
      (RingModel{cap, List.drop(&2, U32, items, n)}, List.take(&2, U32, items, n))
