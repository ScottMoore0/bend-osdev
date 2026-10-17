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
def nth_set(i: Nat, blocks: List<&2, B.Octets>, +v: B.Octets, +e: Nat, lt: {Nat.is_lt(i, List.length(&2, B.Octets, blocks)) == True{} : Bool}) -> {D.MemDev.nth(i, D.MemDev.set.ref(i, blocks, v), e) == Done{v} : Result<&2, &2, D.DevError, B.Octets>}:
  match i blocks:
    case 0n Con{h, t}:
      {==}
    case 1n+p Con{h, t}:
      nth_set(p, t, v, e, lt)
    case 0n Nil{}:
      Empty.absurd({D.MemDev.nth(0n, D.MemDev.set.ref(0n, Nil{}, v), e) == Done{v} : Result<&2, &2, D.DevError, B.Octets>}, false_true(lt))
    case 1n+p Nil{}:
      Empty.absurd({D.MemDev.nth(1n+p, D.MemDev.set.ref(1n+p, Nil{}, v), e) == Done{v} : Result<&2, &2, D.DevError, B.Octets>}, false_true(lt))

# reading any other block
def nth_set_other(m: Nat, i: Nat, blocks: List<&2, B.Octets>, +v: B.Octets, +e: Nat, diff: {Nat.is_eq(m, i) == False{} : Bool}) -> {D.MemDev.nth(m, D.MemDev.set.ref(i, blocks, v), e) == D.MemDev.nth(m, blocks, e) : Result<&2, &2, D.DevError, B.Octets>}:
  match m i blocks:
    case 0n 0n Con{h, t}:
      Empty.absurd({D.MemDev.nth(0n, D.MemDev.set.ref(0n, Con{h, t}, v), e) == D.MemDev.nth(0n, Con{h, t}, e) : Result<&2, &2, D.DevError, B.Octets>}, true_false(diff))
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

def set_length(i: Nat, blocks: List<&2, B.Octets>, +v: B.Octets) -> {List.length(&2, B.Octets, D.MemDev.set.ref(i, blocks, v)) == List.length(&2, B.Octets, blocks) : Nat}:
  match i blocks:
    case 0n Con{h, t}:
      {==}
    case 1n+p Con{h, t}:
      %set_length(p, t, v) : {1n+List.length(&2, B.Octets, D.MemDev.set.ref(p, t, v)) == 1n+_ : Nat}
      {==}
    case 0n Nil{}:
      {==}
    case 1n+p Nil{}:
      {==}

# the tail-recursive block lists equal the structural ones

def set_go(+i: Nat, +blocks: List<&2, B.Octets>, +v: B.Octets, +acc: List<&2, B.Octets>) -> {D.MemDev.set.go(i, blocks, v, acc) == D.MemDev.blocks.rev_onto(acc, D.MemDev.set.ref(i, blocks, v)) : List<&2, B.Octets>}:
  match i blocks:
    case 0n Con{h, t}:
      {==}
    case 1n+p Con{h, t}:
      set_go(p, t, v, Con{h, acc})
    case 0n Nil{}:
      {==}
    case 1n+p Nil{}:
      {==}

def set_eq(+i: Nat, +blocks: List<&2, B.Octets>, +v: B.Octets) -> {D.MemDev.set.ref(i, blocks, v) == D.MemDev.set(i, blocks, v) : List<&2, B.Octets>}:
  Equal.sym(List<&2, B.Octets>, D.MemDev.set(i, blocks, v), D.MemDev.set.ref(i, blocks, v), set_go(i, blocks, v, Nil{}))

def add_succ(+a: Nat, +n: Nat) -> {Nat.add(a, 1n+n) == 1n+Nat.add(a, n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 1n+n), 1n+Nat.add(p, n), add_succ(p, n))

def add_zero(+a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 0n), p, add_zero(p))

def count_go(+blocks: List<&2, B.Octets>, +n: Nat) -> {D.MemDev.count.go(blocks, n) == Nat.add(List.length(&2, B.Octets, blocks), n) : Nat}:
  match blocks:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.trans(Nat, D.MemDev.count.go(t, 1n+n), Nat.add(List.length(&2, B.Octets, t), 1n+n), 1n+Nat.add(List.length(&2, B.Octets, t), n),
        count_go(t, 1n+n), add_succ(List.length(&2, B.Octets, t), n))

def cnt(+blocks: List<&2, B.Octets>) -> {List.length(&2, B.Octets, blocks) == D.MemDev.count.go(blocks, 0n) : Nat}:
  Equal.sym(Nat, D.MemDev.count.go(blocks, 0n), List.length(&2, B.Octets, blocks),
    Equal.trans(Nat, D.MemDev.count.go(blocks, 0n), Nat.add(List.length(&2, B.Octets, blocks), 0n), List.length(&2, B.Octets, blocks), count_go(blocks, 0n), add_zero(List.length(&2, B.Octets, blocks))))

def Laws.read_after_update(d, n, data, len_ok, in_range):
  match d:
    case D.MemDev{+bs, +blocks}:
      %Equal.sym(Bool, Nat.is_eq(B.Octets.len(data), bs), True{}, len_ok) : {D.MemDev.read_block(D.MemDev.update.check(_, bs, blocks, n, data), n) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}
      %set_eq(n, blocks, data) : {D.MemDev.nth(n, _, n) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}
      nth_set(n, blocks, data, n, Equal.trans(Bool, Nat.is_lt(n, List.length(&2, B.Octets, blocks)), Nat.is_lt(n, D.MemDev.count.go(blocks, 0n)), True{}, Equal.cong(Nat, Bool, k => Nat.is_lt(n, k), List.length(&2, B.Octets, blocks), D.MemDev.count.go(blocks, 0n), cnt(blocks)), in_range))

def upd_other(ok: Bool, +bs: Nat, +blocks: List<&2, B.Octets>, +n: Nat, +m: Nat, +data: B.Octets, diff: {Nat.is_eq(m, n) == False{} : Bool}) -> {D.MemDev.read_block(D.MemDev.update.check(ok, bs, blocks, n, data), m) == D.MemDev.read_block(D.MemDev{bs, blocks}, m) : Result<&2, &2, D.DevError, B.Octets>}:
  match ok:
    case True{}:
      %set_eq(n, blocks, data) : {D.MemDev.nth(m, _, m) == D.MemDev.nth(m, blocks, m) : Result<&2, &2, D.DevError, B.Octets>}
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

def upd_count(ok: Bool, +bs: Nat, +blocks: List<&2, B.Octets>, +n: Nat, +data: B.Octets) -> {D.MemDev.block_count(D.MemDev.update.check(ok, bs, blocks, n, data)) == D.MemDev.block_count(D.MemDev{bs, blocks}) : Nat}:
  match ok:
    case True{}:
      %cnt(D.MemDev.set(n, blocks, data)) : {_ == D.MemDev.count.go(blocks, 0n) : Nat}
      %cnt(blocks) : {List.length(&2, B.Octets, D.MemDev.set(n, blocks, data)) == _ : Nat}
      %set_eq(n, blocks, data) : {List.length(&2, B.Octets, _) == List.length(&2, B.Octets, blocks) : Nat}
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
