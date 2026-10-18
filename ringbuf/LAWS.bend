# Properties, for every ring, element, list and count:
#
# * the invariant: a new ring is valid, and push, pop, peek, push_list and
#   pop_list keep a ring valid; so every ring these defs build is valid. For
#   a valid ring, the length is at most the capacity, the length and the free
#   space add up to the capacity, and the ring is empty exactly when its
#   length is 0 and full exactly when its free space is 0;
# * refusals: push on a full ring and pop or peek on an empty one answer
#   RingFull or RingEmpty and change nothing;
# * otherwise push succeeds and adds one to the length, and pop succeeds and
#   takes one from it; peek answers what pop would, and leaves the length;
# * batches: push_list pushes as many elements as fit (the smaller of the
#   list's length and the free space), and pop_list pops as many as asked
#   for, or as there are;
# * the reference model (model.bend), for every model and list: the queue
#   laws for push, pop and peek, push_list and pop_list on the list of
#   elements, and FIFO: pushing a list that fits and popping everything
#   answers the old elements and then the list, in order;
# * the Array ring against the model: for a valid ring and a model with the
#   same capacity and length, every operation answers the same (for pop:
#   succeeds on both or on neither) and keeps capacity and length equal.
#
# The Array ring's elements are stated for every value of the elements but
# on fixed shapes of ring, as vectors with variables: pushing a list that
# fits and then popping that many gives the list back in order, from an
# empty ring, across the end of the slots, when full, and interleaved. Tying
# them to the model for every ring needs lemmas about Base's Array.get after
# Array.set at a symbolic index, which Base does not have yet (see the
# README). Witnesses show that each hypothesis can hold.
import Base
import ./ringbuf.bend as R
import ./model.bend as M

# The invariant

law new_valid:
  for o: Nat
  {Pair.snd(R.RingBuf, Bool, R.ring.valid(R.ring.new(o))) == True{} : Bool}

law new_empty:
  for o: Nat
  {Pair.snd(R.RingBuf, Nat, R.ring.len(R.ring.new(o))) == 0n : Nat}

law new_capacity:
  for o: Nat
  {Pair.snd(R.RingBuf, Nat, R.ring.capacity(R.ring.new(o))) == R.ring.size(o) : Nat}

law len_le_capacity:
  for r: R.RingBuf
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  {Nat.is_le(Pair.snd(R.RingBuf, Nat, R.ring.len(r)), Pair.snd(R.RingBuf, Nat, R.ring.capacity(r))) == True{} : Bool}

law len_avail:
  for r: R.RingBuf
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  {Nat.add(Pair.snd(R.RingBuf, Nat, R.ring.len(r)), Pair.snd(R.RingBuf, Nat, R.ring.avail(r))) == Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) : Nat}

law empty_iff:
  for r: R.RingBuf
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  {Pair.snd(R.RingBuf, Bool, R.ring.is_empty(r)) == Nat.is_eq(Pair.snd(R.RingBuf, Nat, R.ring.len(r)), 0n) : Bool}

law full_iff:
  for r: R.RingBuf
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  {Pair.snd(R.RingBuf, Bool, R.ring.is_full(r)) == Nat.is_eq(Pair.snd(R.RingBuf, Nat, R.ring.avail(r)), 0n) : Bool}

# Push

law push_valid:
  for r: R.RingBuf
  for x: U32
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(r, x)))) == True{} : Bool}

law push_full:
  for r: R.RingBuf
  for x: U32
  for e: {Pair.snd(R.RingBuf, Bool, R.ring.is_full(r)) == True{} : Bool}
  {R.ring.push(r, x) == (r, Fail{R.RingFull{}}) : R.RingBuf & Result<&2, &2, R.RingError, Unit>}

law push_room:
  for r: R.RingBuf
  for x: U32
  for e: {Pair.snd(R.RingBuf, Bool, R.ring.is_full(r)) == False{} : Bool}
  {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(r, x)) == Done{Unit{}} : Result<&2, &2, R.RingError, Unit>}

law push_len:
  for r: R.RingBuf
  for x: U32
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  for e: {Pair.snd(R.RingBuf, Bool, R.ring.is_full(r)) == False{} : Bool}
  {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(r, x)))) == 1n+Pair.snd(R.RingBuf, Nat, R.ring.len(r)) : Nat}

# Pop and peek

law pop_valid:
  for r: R.RingBuf
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r)))) == True{} : Bool}

law pop_empty:
  for r: R.RingBuf
  for e: {Pair.snd(R.RingBuf, Bool, R.ring.is_empty(r)) == True{} : Bool}
  {R.ring.pop(r) == (r, Fail{R.RingEmpty{}}) : R.RingBuf & Result<&2, &2, R.RingError, U32>}

law pop_done:
  for r: R.RingBuf
  for e: {Pair.snd(R.RingBuf, Bool, R.ring.is_empty(r)) == False{} : Bool}
  {Result.is_done(&2, &2, R.RingError, U32, Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r))) == True{} : Bool}

law pop_len:
  for r: R.RingBuf
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  for e: {Pair.snd(R.RingBuf, Bool, R.ring.is_empty(r)) == False{} : Bool}
  {1n+Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r)))) == Pair.snd(R.RingBuf, Nat, R.ring.len(r)) : Nat}

law peek_is_pop:
  for r: R.RingBuf
  {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(r)) == Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r)) : Result<&2, &2, R.RingError, U32>}

law peek_empty:
  for r: R.RingBuf
  for e: {Pair.snd(R.RingBuf, Bool, R.ring.is_empty(r)) == True{} : Bool}
  {R.ring.peek(r) == (r, Fail{R.RingEmpty{}}) : R.RingBuf & Result<&2, &2, R.RingError, U32>}

law peek_valid:
  for r: R.RingBuf
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(r)))) == True{} : Bool}

law peek_len:
  for r: R.RingBuf
  {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.peek(r)))) == Pair.snd(R.RingBuf, Nat, R.ring.len(r)) : Nat}

# Batches

law push_list_valid:
  for r: R.RingBuf
  for xs: List<&2, U32>
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Nat, R.ring.push_list(r, xs)))) == True{} : Bool}

law push_list_count:
  for r: R.RingBuf
  for xs: List<&2, U32>
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  {Pair.snd(R.RingBuf, Nat, R.ring.push_list(r, xs)) == Nat.min(List.length(&2, U32, xs), Pair.snd(R.RingBuf, Nat, R.ring.avail(r))) : Nat}

law pop_list_valid:
  for r: R.RingBuf
  for n: Nat
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  {Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(r, n)))) == True{} : Bool}

law pop_list_count:
  for r: R.RingBuf
  for n: Nat
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list(r, n))) == Nat.min(n, Pair.snd(R.RingBuf, Nat, R.ring.len(r))) : Nat}

# FIFO order, for every value of the elements (vectors with variables)

# four slots, from empty: four elements back in order
law fifo_fill:
  for a: U32
  for b: U32
  for c: U32
  for d: U32
  {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list(Pair.fst(R.RingBuf, Nat, R.ring.push_list(R.ring.new(2n), [a, b, c, d])), 4n)) == [a, b, c, d] : List<&2, U32>}

# four slots, the counters at 3: the elements wrap past the last slot
law fifo_wrap:
  for a: U32
  for b: U32
  for c: U32
  for d: U32
  {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list(Pair.fst(R.RingBuf, Nat, R.ring.push_list(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(Pair.fst(R.RingBuf, Nat, R.ring.push_list(R.ring.new(2n), [0, 0, 0])), 3n)), [a, b, c, d])), 4n)) == [a, b, c, d] : List<&2, U32>}

# eight slots, the counters at 6: three elements across the end
law fifo_wrap8:
  for a: U32
  for b: U32
  for c: U32
  {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list(Pair.fst(R.RingBuf, Nat, R.ring.push_list(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(Pair.fst(R.RingBuf, Nat, R.ring.push_list(R.ring.new(3n), [0, 0, 0, 0, 0, 0])), 6n)), [a, b, c])), 3n)) == [a, b, c] : List<&2, U32>}

# four slots, five pushed: the fifth is refused and the four come back
law fifo_full:
  for a: U32
  for b: U32
  for c: U32
  for d: U32
  for e: U32
  {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list(Pair.fst(R.RingBuf, Nat, R.ring.push_list(R.ring.new(2n), [a, b, c, d, e])), 5n)) == [a, b, c, d] : List<&2, U32>}

# pushes and pops interleaved: a, b in; a out; c in; b, c out
law fifo_interleaved:
  for a: U32
  for b: U32
  for c: U32
  {Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list(Pair.fst(R.RingBuf, Nat, R.ring.push_list(Pair.fst(R.RingBuf, List<&2, U32>, R.ring.pop_list(Pair.fst(R.RingBuf, Nat, R.ring.push_list(R.ring.new(1n), [a, b])), 1n)), [c])), 2n)) == [b, c] : List<&2, U32>}

# The reference model (model.bend): element order, for every model and list

law model_new_valid:
  for o: Nat
  {M.model.valid(M.model.new(o)) == True{} : Bool}

law model_new_empty:
  for o: Nat
  {M.model.items(M.model.new(o)) == Nil{} : List<&2, U32>}

law model_new_capacity:
  for o: Nat
  {M.model.capacity(M.model.new(o)) == R.ring.size(o) : Nat}

law model_push_items:
  for m: M.RingModel
  for x: U32
  for e: {M.model.is_full(m) == False{} : Bool}
  {M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(m, x))) == List.append(&2, U32, M.model.items(m), [x]) : List<&2, U32>}

law model_push_done:
  for m: M.RingModel
  for x: U32
  for e: {M.model.is_full(m) == False{} : Bool}
  {Pair.snd(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(m, x)) == Done{Unit{}} : Result<&2, &2, R.RingError, Unit>}

law model_push_full:
  for m: M.RingModel
  for x: U32
  for e: {M.model.is_full(m) == True{} : Bool}
  {M.model.push(m, x) == (m, Fail{R.RingFull{}}) : M.RingModel & Result<&2, &2, R.RingError, Unit>}

law model_push_valid:
  for m: M.RingModel
  for x: U32
  for h: {M.model.valid(m) == True{} : Bool}
  {M.model.valid(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(m, x))) == True{} : Bool}

law model_pop:
  for m: M.RingModel
  for y: U32
  for t: List<&2, U32>
  for e: {M.model.items(m) == Con{y, t} : List<&2, U32>}
  {Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(m)) == Done{y} : Result<&2, &2, R.RingError, U32>}

law model_pop_items:
  for m: M.RingModel
  for y: U32
  for t: List<&2, U32>
  for e: {M.model.items(m) == Con{y, t} : List<&2, U32>}
  {M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(m))) == t : List<&2, U32>}

law model_pop_empty:
  for m: M.RingModel
  for e: {M.model.is_empty(m) == True{} : Bool}
  {M.model.pop(m) == (m, Fail{R.RingEmpty{}}) : M.RingModel & Result<&2, &2, R.RingError, U32>}

law model_pop_valid:
  for m: M.RingModel
  for h: {M.model.valid(m) == True{} : Bool}
  {M.model.valid(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(m))) == True{} : Bool}

law model_peek_is_pop:
  for m: M.RingModel
  {Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(m)) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(m)) : Result<&2, &2, R.RingError, U32>}

law model_peek_keeps:
  for m: M.RingModel
  {Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.peek(m)) == m : M.RingModel}

law model_push_list:
  for m: M.RingModel
  for xs: List<&2, U32>
  for h: {M.model.valid(m) == True{} : Bool}
  for l: {Nat.is_le(List.length(&2, U32, xs), M.model.avail(m)) == True{} : Bool}
  {M.model.items(Pair.fst(M.RingModel, Nat, M.model.push_list(m, xs))) == List.append(&2, U32, M.model.items(m), xs) : List<&2, U32>}

law model_push_list_count:
  for m: M.RingModel
  for xs: List<&2, U32>
  {Pair.snd(M.RingModel, Nat, M.model.push_list(m, xs)) == Nat.min(List.length(&2, U32, xs), M.model.avail(m)) : Nat}

law model_push_list_valid:
  for m: M.RingModel
  for xs: List<&2, U32>
  for h: {M.model.valid(m) == True{} : Bool}
  {M.model.valid(Pair.fst(M.RingModel, Nat, M.model.push_list(m, xs))) == True{} : Bool}

law model_pop_list:
  for m: M.RingModel
  for n: Nat
  {Pair.snd(M.RingModel, List<&2, U32>, M.model.pop_list(m, n)) == List.take(&2, U32, M.model.items(m), n) : List<&2, U32>}

law model_pop_list_items:
  for m: M.RingModel
  for n: Nat
  {M.model.items(Pair.fst(M.RingModel, List<&2, U32>, M.model.pop_list(m, n))) == List.drop(&2, U32, M.model.items(m), n) : List<&2, U32>}

law model_pop_list_valid:
  for m: M.RingModel
  for n: Nat
  for h: {M.model.valid(m) == True{} : Bool}
  {M.model.valid(Pair.fst(M.RingModel, List<&2, U32>, M.model.pop_list(m, n))) == True{} : Bool}

# FIFO: pushing a list that fits and popping everything gives the old
# elements, then the list, in order

law model_fifo:
  for m: M.RingModel
  for xs: List<&2, U32>
  for h: {M.model.valid(m) == True{} : Bool}
  for l: {Nat.is_le(List.length(&2, U32, xs), M.model.avail(m)) == True{} : Bool}
  {Pair.snd(M.RingModel, List<&2, U32>, M.model.pop_list(Pair.fst(M.RingModel, Nat, M.model.push_list(m, xs)), Nat.add(M.model.len(m), List.length(&2, U32, xs)))) == List.append(&2, U32, M.model.items(m), xs) : List<&2, U32>}

# The Array ring against the model: a valid ring and a model with the same
# capacity and length answer the same, and keep the capacity and length
# equal (the relation is on counters only, so it needs no Array lemma)

law rel_is_full:
  for r: R.RingBuf
  for m: M.RingModel
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  for c: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}
  for n: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}
  {Pair.snd(R.RingBuf, Bool, R.ring.is_full(r)) == M.model.is_full(m) : Bool}

law rel_is_empty:
  for r: R.RingBuf
  for m: M.RingModel
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  for c: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}
  for n: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}
  {Pair.snd(R.RingBuf, Bool, R.ring.is_empty(r)) == M.model.is_empty(m) : Bool}

law rel_avail:
  for r: R.RingBuf
  for m: M.RingModel
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  for c: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}
  for n: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}
  {Pair.snd(R.RingBuf, Nat, R.ring.avail(r)) == M.model.avail(m) : Nat}

law rel_push:
  for r: R.RingBuf
  for m: M.RingModel
  for x: U32
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  for c: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}
  for n: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}
  {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(r, x)) == Pair.snd(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(m, x)) : Result<&2, &2, R.RingError, Unit>}

law rel_push_len:
  for r: R.RingBuf
  for m: M.RingModel
  for x: U32
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  for c: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}
  for n: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}
  {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(r, x)))) == M.model.len(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(m, x))) : Nat}

law rel_push_capacity:
  for r: R.RingBuf
  for m: M.RingModel
  for x: U32
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  for c: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}
  for n: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}
  {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(r, x)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(m, x))) : Nat}

law rel_pop_done:
  for r: R.RingBuf
  for m: M.RingModel
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  for c: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}
  for n: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}
  {Result.is_done(&2, &2, R.RingError, U32, Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r))) == Result.is_done(&2, &2, R.RingError, U32, Pair.snd(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(m))) : Bool}

law rel_pop_len:
  for r: R.RingBuf
  for m: M.RingModel
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  for c: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}
  for n: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}
  {Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r)))) == M.model.len(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(m))) : Nat}

law rel_pop_capacity:
  for r: R.RingBuf
  for m: M.RingModel
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  for c: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}
  for n: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}
  {Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(r)))) == M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, U32>, M.model.pop(m))) : Nat}

law rel_push_list:
  for r: R.RingBuf
  for m: M.RingModel
  for xs: List<&2, U32>
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  for c: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}
  for n: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}
  {Pair.snd(R.RingBuf, Nat, R.ring.push_list(r, xs)) == Pair.snd(M.RingModel, Nat, M.model.push_list(m, xs)) : Nat}

law rel_pop_list:
  for r: R.RingBuf
  for m: M.RingModel
  for k: Nat
  for h: {Pair.snd(R.RingBuf, Bool, R.ring.valid(r)) == True{} : Bool}
  for c: {Pair.snd(R.RingBuf, Nat, R.ring.capacity(r)) == M.model.capacity(m) : Nat}
  for n: {Pair.snd(R.RingBuf, Nat, R.ring.len(r)) == M.model.len(m) : Nat}
  {List.length(&2, U32, Pair.snd(R.RingBuf, List<&2, U32>, R.ring.pop_list(r, k))) == List.length(&2, U32, Pair.snd(M.RingModel, List<&2, U32>, M.model.pop_list(m, k))) : Nat}

# Witnesses: each hypothesis above can hold

law wit_full:
  {(Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Nat, R.ring.push_list(R.ring.new(1n), [7, 8])))), Pair.snd(R.RingBuf, Bool, R.ring.is_full(Pair.fst(R.RingBuf, Nat, R.ring.push_list(R.ring.new(1n), [7, 8]))))) == (True{}, True{}) : Bool & Bool}

law wit_not_full:
  {(Pair.snd(R.RingBuf, Bool, R.ring.valid(R.ring.new(1n))), Pair.snd(R.RingBuf, Bool, R.ring.is_full(R.ring.new(1n))), Pair.snd(R.RingBuf, Bool, R.ring.is_empty(R.ring.new(1n)))) == (True{}, False{}, True{}) : Bool & Bool & Bool}

law wit_not_empty:
  {(Pair.snd(R.RingBuf, Bool, R.ring.valid(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(R.ring.new(1n), 5)))), Pair.snd(R.RingBuf, Bool, R.ring.is_empty(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(R.ring.new(1n), 5))))) == (True{}, False{}) : Bool & Bool}

law wit_related:
  {(Pair.snd(R.RingBuf, Nat, R.ring.capacity(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(R.ring.new(1n), 5)))), Pair.snd(R.RingBuf, Nat, R.ring.len(Pair.fst(R.RingBuf, Result<&2, &2, R.RingError, Unit>, R.ring.push(R.ring.new(1n), 5))))) == (M.model.capacity(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.model.new(1n), 5))), M.model.len(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.model.new(1n), 5)))) : Nat & Nat}

law wit_model:
  {(M.model.is_full(Pair.fst(M.RingModel, Nat, M.model.push_list(M.model.new(1n), [7, 8]))), M.model.is_full(M.model.new(1n)), M.model.is_empty(M.model.new(1n)), M.model.items(Pair.fst(M.RingModel, Result<&2, &2, R.RingError, Unit>, M.model.push(M.model.new(1n), 5))), Nat.is_le(List.length(&2, U32, [7, 8]), M.model.avail(M.model.new(1n)))) == (True{}, False{}, True{}, [5], True{}) : Bool & Bool & Bool & List<&2, U32> & Bool}

# Vectors

law vec_default_capacity:
  {Pair.snd(R.RingBuf, Nat, R.ring.capacity(R.ring.new_default())) == 256n : Nat}

law vec_pop_new:
  {Pair.snd(R.RingBuf, Result<&2, &2, R.RingError, U32>, R.ring.pop(R.ring.new(3n))) == Fail{R.RingEmpty{}} : Result<&2, &2, R.RingError, U32>}
