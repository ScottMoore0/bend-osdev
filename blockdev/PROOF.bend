import Base
import ../bytes/bytes.bend as B
import ./blockdev.bend as D
import ./LAWS.bend as Laws

def bool_disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

# a false premise False == True closes any goal
def false_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : bool_disc(_)
  Unit{}

def true_false(e: {True{} == False{} : Bool}) -> Empty:
  false_true(Equal.sym(Bool, True{}, False{}, e))

# reading the block a write replaced
def nth_set(i: Nat, blocks: List<&2, B.Octets>, +v: B.Octets, +e: Nat, lt: {Nat.is_lt(i, List.length(&2, B.Octets, blocks)) == True{} : Bool}) -> {D.MemDev.nth(i, D.MemDev.set(i, blocks, v), e) == Done{v} : Result<&2, &2, D.DevError, B.Octets>}:
  match i blocks:
    case 0n Con{h, t}:
      {==}
    case 1n+p Con{h, t}:
      nth_set(p, t, v, e, lt)
    case 0n Nil{}:
      Empty.absurd({D.MemDev.nth(0n, D.MemDev.set(0n, Nil{}, v), e) == Done{v} : Result<&2, &2, D.DevError, B.Octets>}, false_true(lt))
    case 1n+p Nil{}:
      Empty.absurd({D.MemDev.nth(1n+p, D.MemDev.set(1n+p, Nil{}, v), e) == Done{v} : Result<&2, &2, D.DevError, B.Octets>}, false_true(lt))

# reading any other block
def nth_set_other(m: Nat, i: Nat, blocks: List<&2, B.Octets>, +v: B.Octets, +e: Nat, diff: {Nat.is_eq(m, i) == False{} : Bool}) -> {D.MemDev.nth(m, D.MemDev.set(i, blocks, v), e) == D.MemDev.nth(m, blocks, e) : Result<&2, &2, D.DevError, B.Octets>}:
  match m i blocks:
    case 0n 0n Con{h, t}:
      Empty.absurd({D.MemDev.nth(0n, D.MemDev.set(0n, Con{h, t}, v), e) == D.MemDev.nth(0n, Con{h, t}, e) : Result<&2, &2, D.DevError, B.Octets>}, true_false(diff))
    case 0n 0n Nil{}:
      {==}
    case 0n 1n+p Con{h, t}:
      {==}
    case 0n 1n+p Nil{}:
      {==}
    case 1n+q 0n Con{h, t}:
      {==}
    case 1n+q 0n Nil{}:
      {==}
    case 1n+q 1n+p Con{h, t}:
      nth_set_other(q, p, t, v, e, diff)
    case 1n+q 1n+p Nil{}:
      {==}

def set_length(i: Nat, blocks: List<&2, B.Octets>, +v: B.Octets) -> {List.length(&2, B.Octets, D.MemDev.set(i, blocks, v)) == List.length(&2, B.Octets, blocks) : Nat}:
  match i blocks:
    case 0n Con{h, t}:
      {==}
    case 1n+p Con{h, t}:
      %set_length(p, t, v) : {1n+List.length(&2, B.Octets, D.MemDev.set(p, t, v)) == 1n+_ : Nat}
      {==}
    case 0n Nil{}:
      {==}
    case 1n+p Nil{}:
      {==}

def Laws.read_after_update(d, n, data, len_ok, in_range):
  match d:
    case D.MemDev{+bs, +blocks}:
      %Equal.sym(Bool, Nat.is_eq(B.Octets.len(data), bs), True{}, len_ok) : {D.MemDev.read_block(D.MemDev.update.check(_, bs, blocks, n, data), n) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}
      nth_set(n, blocks, data, n, in_range)

def upd_other(ok: Bool, +bs: Nat, +blocks: List<&2, B.Octets>, +n: Nat, +m: Nat, +data: B.Octets, diff: {Nat.is_eq(m, n) == False{} : Bool}) -> {D.MemDev.read_block(D.MemDev.update.check(ok, bs, blocks, n, data), m) == D.MemDev.read_block(D.MemDev{bs, blocks}, m) : Result<&2, &2, D.DevError, B.Octets>}:
  match ok:
    case True{}:
      nth_set_other(m, n, blocks, data, m, diff)
    case False{}:
      {==}

def Laws.update_other(d, n, m, data, diff):
  match d:
    case D.MemDev{+bs, +blocks}:
      upd_other(Nat.is_eq(B.Octets.len(data), bs), bs, blocks, n, m, data, diff)

def upd_size(ok: Bool, +bs: Nat, +blocks: List<&2, B.Octets>, +n: Nat, +data: B.Octets) -> {D.MemDev.block_size(D.MemDev.update.check(ok, bs, blocks, n, data)) == bs : Nat}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.update_keeps_size(d, n, data):
  match d:
    case D.MemDev{+bs, +blocks}:
      upd_size(Nat.is_eq(B.Octets.len(data), bs), bs, blocks, n, data)

def upd_count(ok: Bool, +bs: Nat, +blocks: List<&2, B.Octets>, +n: Nat, +data: B.Octets) -> {D.MemDev.block_count(D.MemDev.update.check(ok, bs, blocks, n, data)) == List.length(&2, B.Octets, blocks) : Nat}:
  match ok:
    case True{}:
      set_length(n, blocks, data)
    case False{}:
      {==}

def Laws.update_keeps_count(d, n, data):
  match d:
    case D.MemDev{+bs, +blocks}:
      upd_count(Nat.is_eq(B.Octets.len(data), bs), bs, blocks, n, data)

def Laws.vector_count():
  {==}

def Laws.vector_block():
  {==}

def Laws.vector_out_of_range():
  {==}

def Laws.vector_span():
  {==}

def Laws.vector_span_past_end():
  {==}

def Laws.vector_write():
  {==}

def Laws.vector_write_bad_length():
  {==}
