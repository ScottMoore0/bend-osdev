# Proof helpers for bend-osdev-gf: the exp/log tables (tables.bend) as lists.
#
# The method (as bend-osdev-blockdev's ImgDev and bend-osdev-crc's tables
# follow their arrays): array's laws turn each table fill, write by write,
# into Arrays.of_list(d, l, 0) for a Data list l (of_list_new, of_list_set;
# the fill's counter i is U32.from_nat(i), and its running power is
# Gf8.exp(f, i)). The exp table's list is gt.elist(510, f, 0): entry i is
# Gf8.exp(f, i), for every field. The log table's list is computed for the
# named fields (proof_tab_cases.bend). A read of a table is then
# array's of_list_get: a literal pair of the same table and the list's
# entry. Lemmas are prefixed gt.
import Base
import ../array/array.bend as A
import ../array/LAWS.bend as AL
import ../array/PROOF.bend as APF
import ./gf.bend as G
import ./tables.bend as T

# Contradictions and congruence

def gt.bt(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def gt.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : gt.bt(_)
  Unit{}

def gt.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : gt.bt(_)
  Unit{}

def gt.wcon2(-p: Nat, -a: Bool, -b: Bool, -x: Word(p), -y: Word(p), ea: {a == b : Bool}, ex: {x == y : Word(p)}) -> {WCon{a, x} == WCon{b, y} : Word(1n+p)}:
  %ea : {WCon{a, x} == WCon{_, y} : Word(1n+p)}
  %ex : {WCon{a, x} == WCon{a, _} : Word(1n+p)}
  {==}

def gt.u32_cong(-x: Word(32n), -y: Word(32n), e: {x == y : Word(32n)}) -> {U32{x} == U32{y} : U32}:
  %e : {U32{x} == U32{_} : U32}
  {==}

# U32 addition of small counts: adding zero, adding an increment

def gt.adc_zero(n: Nat, w: Word(n)) -> {Word.adc(n, w, Word.zero(n), False{}, False{}) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          gt.wcon2(p, False{}, False{}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, {==}, gt.adc_zero(p, t))
        case WCon{True{}, +t}:
          gt.wcon2(p, True{}, True{}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, {==}, gt.adc_zero(p, t))

# a + (b + 1) = a + b with a carry in
def gt.adc_inc(n: Nat, a: Word(n), b: Word(n)) -> {Word.adc(n, a, Word.inc(n, b), False{}, False{}) == Word.adc(n, a, b, False{}, True{}) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{False{}, bt}:
          {==}
        case WCon{True{}, at} WCon{False{}, bt}:
          {==}
        case WCon{False{}, +at} WCon{True{}, +bt}:
          gt.wcon2(p, False{}, False{}, Word.adc(p, at, Word.inc(p, bt), False{}, False{}), Word.adc(p, at, bt, False{}, True{}), {==}, gt.adc_inc(p, at, bt))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          gt.wcon2(p, True{}, True{}, Word.adc(p, at, Word.inc(p, bt), False{}, False{}), Word.adc(p, at, bt, False{}, True{}), {==}, gt.adc_inc(p, at, bt))

# a + b with a carry in is (a + b) + 1
def gt.adc_carry(n: Nat, a: Word(n), b: Word(n)) -> {Word.adc(n, a, b, False{}, True{}) == Word.inc(n, Word.adc(n, a, b, False{}, False{})) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{False{}, bt}:
          {==}
        case WCon{True{}, +at} WCon{False{}, +bt}:
          gt.wcon2(p, False{}, False{}, Word.adc(p, at, bt, False{}, True{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})), {==}, gt.adc_carry(p, at, bt))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          gt.wcon2(p, False{}, False{}, Word.adc(p, at, bt, False{}, True{}), Word.inc(p, Word.adc(p, at, bt, False{}, False{})), {==}, gt.adc_carry(p, at, bt))
        case WCon{True{}, at} WCon{True{}, bt}:
          {==}

def gt.add_zero(x: U32) -> {U32.add(x, 0) == x : U32}:
  match x:
    case U32{+w}:
      gt.u32_cong(Word.adc(32n, w, Word.zero(32n), False{}, False{}), w, gt.adc_zero(32n, w))

def gt.add_inc(a: U32, b: U32) -> {U32.add(a, U32.inc(b)) == U32.inc(U32.add(a, b)) : U32}:
  match a b:
    case U32{+x} U32{+y}:
      gt.u32_cong(Word.adc(32n, x, Word.inc(32n, y), False{}, False{}), Word.inc(32n, Word.adc(32n, x, y, False{}, False{})), Equal.trans(Word(32n), Word.adc(32n, x, Word.inc(32n, y), False{}, False{}), Word.adc(32n, x, y, False{}, True{}), Word.inc(32n, Word.adc(32n, x, y, False{}, False{})), gt.adc_inc(32n, x, y), gt.adc_carry(32n, x, y)))

# the fills' counter: i + 1 is the increment
def gt.add_one(+x: U32) -> {U32.add(x, 1) == U32.inc(x) : U32}:
  %gt.add_zero(x) : {U32.add(x, 1) == U32.inc(_) : U32}
  gt.add_inc(x, 0)

# the sum of two counts, as U32, is the U32 of their sum
def gt.add_nat(+p: Nat, +q: Nat) -> {U32.add(U32.from_nat(p), U32.from_nat(q)) == U32.from_nat(Nat.add(q, p)) : U32}:
  match q:
    case 0n:
      gt.add_zero(U32.from_nat(p))
    case 1n+r:
      %gt.add_nat(p, r) : {U32.add(U32.from_nat(p), U32.inc(U32.from_nat(r))) == U32.inc(_) : U32}
      gt.add_inc(U32.from_nat(p), U32.from_nat(r))

# Nat facts

def gt.add_zero_r(+x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 0n), p, gt.add_zero_r(p)) : {1n+_ == 1n+p : Nat}
      {==}

def gt.add_succ(+x: Nat, +y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+y), 1n+Nat.add(p, y), gt.add_succ(p, y)) : {1n+_ == 2n+Nat.add(p, y) : Nat}
      {==}

def gt.lt_succ_r(+x: Nat, +y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_lt(x, 1n+y) == True{} : Bool}:
  match x y:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(1n+p, 1n) == True{} : Bool}, gt.ft(h))
    case 1n+p 1n+q:
      gt.lt_succ_r(p, q, h)

def gt.lt_self(+x: Nat) -> {Nat.is_lt(x, 1n+x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      gt.lt_self(p)

# x < 1 + (n + x)
def gt.lt_self_add(+n: Nat, +x: Nat) -> {Nat.is_lt(x, 1n+Nat.add(n, x)) == True{} : Bool}:
  match n:
    case 0n:
      gt.lt_self(x)
    case 1n+k:
      gt.lt_succ_r(x, 1n+Nat.add(k, x), gt.lt_self_add(k, x))

# b < n, so b < m + n
def gt.lt_add_left(+m: Nat, +b: Nat, +n: Nat, +h: {Nat.is_lt(b, n) == True{} : Bool}) -> {Nat.is_lt(b, Nat.add(m, n)) == True{} : Bool}:
  match m:
    case 0n:
      h
    case 1n+k:
      gt.lt_succ_r(b, Nat.add(k, n), gt.lt_add_left(k, b, n, h))

# a < m and b < n, so a + b < m + n
def gt.lt_sum(+a: Nat, +m: Nat, +b: Nat, +n: Nat, ha: {Nat.is_lt(a, m) == True{} : Bool}, +hb: {Nat.is_lt(b, n) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, b), Nat.add(m, n)) == True{} : Bool}:
  match a m:
    case 0n _:
      gt.lt_add_left(m, b, n, hb)
    case 1n+p 0n:
      Empty.absurd({Nat.is_lt(Nat.add(1n+p, b), n) == True{} : Bool}, gt.ft(ha))
    case 1n+p 1n+q:
      gt.lt_sum(p, q, b, n, ha, hb)

# two logarithms (each below 255) sum below the exp table's 2^9 slots
def gt.sum_lt(+a: Nat, +b: Nat, +ha: {Nat.is_lt(a, 255n) == True{} : Bool}, +hb: {Nat.is_lt(b, 255n) == True{} : Bool}) -> {Nat.is_lt(Nat.add(a, b), A.Arrays.slots(9n)) == True{} : Bool}:
  gt.lt_add_left(2n, Nat.add(a, b), 510n, gt.lt_sum(a, 255n, b, 255n, ha, hb))

# Gf8.log is below 255

def gt.log_go_lt(+n: Nat, hit: Bool, +f: G.Gf8Field, +a: U32, +cur: U32, +i: Nat) -> {Nat.is_lt(G.Gf8.log.go(n, hit, f, a, cur, i), 1n+Nat.add(n, i)) == True{} : Bool}:
  match n hit:
    case _ True{}:
      gt.lt_self_add(n, i)
    case 0n False{}:
      {==}
    case 1n+k False{}:
      %gt.add_succ(k, i) : {Nat.is_lt(G.Gf8.log.go(k, U32.is_eq(G.Gf8.mul(f, G.Gf8.gen(f), cur), a), f, a, G.Gf8.mul(f, G.Gf8.gen(f), cur), 1n+i), 1n+_) == True{} : Bool}
      gt.log_go_lt(k, U32.is_eq(G.Gf8.mul(f, G.Gf8.gen(f), cur), a), f, a, G.Gf8.mul(f, G.Gf8.gen(f), cur), 1n+i)

def gt.log_lt(+f: G.Gf8Field, +a: U32) -> {Nat.is_lt(G.Gf8.log(f, a), 255n) == True{} : Bool}:
  gt.log_go_lt(254n, U32.is_eq(1, G.Gf8.elt(a)), f, G.Gf8.elt(a), 1, 0n)

# The fills, write by write

def gt.hd9() -> {Nat.is_lt(9n, 32n) == True{} : Bool}:
  {==}

def gt.hd8() -> {Nat.is_lt(8n, 32n) == True{} : Bool}:
  {==}

def gt.hl_set(+d: Nat, +xs: List<&2, U32>, +k: Nat, +v: U32, +hl: {List.length(&2, U32, xs) == A.Arrays.slots(d) : Nat}) -> {List.length(&2, U32, List.set(&2, U32, xs, k, v)) == A.Arrays.slots(d) : Nat}:
  Equal.trans(Nat, List.length(&2, U32, List.set(&2, U32, xs, k, v)), List.length(&2, U32, xs), A.Arrays.slots(d), AL.set_length(U32, xs, k, v), hl)

# the exp fill's model: slot i (from slot k) holds gen^i
def gt.fe(n: Nat, xs: List<&2, U32>, +f: G.Gf8Field, +k: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+j:
      gt.fe(j, List.set(&2, U32, xs, A.Arrays.index(9n, U32.from_nat(k)), G.Gf8.exp(f, k)), f, 1n+k)

def gt.fill_exp(n: Nat, +xs: List<&2, U32>, +f: G.Gf8Field, +k: Nat, +hl: {List.length(&2, U32, xs) == A.Arrays.slots(9n) : Nat}) -> {T.gf8tab.fill.exp(n, A.Arrays.of_list(U32, 9n, xs, 0), f, G.Gf8.exp(f, k), U32.from_nat(k)) == A.Arrays.of_list(U32, 9n, gt.fe(n, xs, f, k), 0) : Array<U32>}:
  match n:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(U32, U32.add(U32.from_nat(k), 1), U32.inc(U32.from_nat(k)), gt.add_one(U32.from_nat(k))) : {T.gf8tab.fill.exp(j, Array.set(U32, A.Arrays.of_list(U32, 9n, xs, 0), U32.from_nat(k), G.Gf8.exp(f, k)), f, G.Gf8.mul(f, G.Gf8.gen(f), G.Gf8.exp(f, k)), _) == A.Arrays.of_list(U32, 9n, gt.fe(j, List.set(&2, U32, xs, A.Arrays.index(9n, U32.from_nat(k)), G.Gf8.exp(f, k)), f, 1n+k), 0) : Array<U32>}
      %Equal.sym(Array<U32>, Array.set(U32, A.Arrays.of_list(U32, 9n, xs, 0), U32.from_nat(k), G.Gf8.exp(f, k)), A.Arrays.of_list(U32, 9n, List.set(&2, U32, xs, A.Arrays.index(9n, U32.from_nat(k)), G.Gf8.exp(f, k)), 0), AL.of_list_set(U32, 9n, xs, 0, hl, gt.hd9(), U32.from_nat(k), G.Gf8.exp(f, k))) : {T.gf8tab.fill.exp(j, _, f, G.Gf8.mul(f, G.Gf8.gen(f), G.Gf8.exp(f, k)), U32.inc(U32.from_nat(k))) == A.Arrays.of_list(U32, 9n, gt.fe(j, List.set(&2, U32, xs, A.Arrays.index(9n, U32.from_nat(k)), G.Gf8.exp(f, k)), f, 1n+k), 0) : Array<U32>}
      gt.fill_exp(j, List.set(&2, U32, xs, A.Arrays.index(9n, U32.from_nat(k)), G.Gf8.exp(f, k)), f, 1n+k, gt.hl_set(9n, xs, A.Arrays.index(9n, U32.from_nat(k)), G.Gf8.exp(f, k), hl))

# the log fill's model: slot gen^i holds i, from i = k
def gt.fl(n: Nat, xs: List<&2, U32>, +f: G.Gf8Field, +k: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+j:
      gt.fl(j, List.set(&2, U32, xs, A.Arrays.index(8n, G.Gf8.exp(f, k)), U32.from_nat(k)), f, 1n+k)

def gt.fill_log(n: Nat, +xs: List<&2, U32>, +f: G.Gf8Field, +k: Nat, +hl: {List.length(&2, U32, xs) == A.Arrays.slots(8n) : Nat}) -> {T.gf8tab.fill.log(n, A.Arrays.of_list(U32, 8n, xs, 0), f, G.Gf8.exp(f, k), U32.from_nat(k)) == A.Arrays.of_list(U32, 8n, gt.fl(n, xs, f, k), 0) : Array<U32>}:
  match n:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(U32, U32.add(U32.from_nat(k), 1), U32.inc(U32.from_nat(k)), gt.add_one(U32.from_nat(k))) : {T.gf8tab.fill.log(j, Array.set(U32, A.Arrays.of_list(U32, 8n, xs, 0), G.Gf8.exp(f, k), U32.from_nat(k)), f, G.Gf8.mul(f, G.Gf8.gen(f), G.Gf8.exp(f, k)), _) == A.Arrays.of_list(U32, 8n, gt.fl(j, List.set(&2, U32, xs, A.Arrays.index(8n, G.Gf8.exp(f, k)), U32.from_nat(k)), f, 1n+k), 0) : Array<U32>}
      %Equal.sym(Array<U32>, Array.set(U32, A.Arrays.of_list(U32, 8n, xs, 0), G.Gf8.exp(f, k), U32.from_nat(k)), A.Arrays.of_list(U32, 8n, List.set(&2, U32, xs, A.Arrays.index(8n, G.Gf8.exp(f, k)), U32.from_nat(k)), 0), AL.of_list_set(U32, 8n, xs, 0, hl, gt.hd8(), G.Gf8.exp(f, k), U32.from_nat(k))) : {T.gf8tab.fill.log(j, _, f, G.Gf8.mul(f, G.Gf8.gen(f), G.Gf8.exp(f, k)), U32.inc(U32.from_nat(k))) == A.Arrays.of_list(U32, 8n, gt.fl(j, List.set(&2, U32, xs, A.Arrays.index(8n, G.Gf8.exp(f, k)), U32.from_nat(k)), f, 1n+k), 0) : Array<U32>}
      gt.fill_log(j, List.set(&2, U32, xs, A.Arrays.index(8n, G.Gf8.exp(f, k)), U32.from_nat(k)), f, 1n+k, gt.hl_set(8n, xs, A.Arrays.index(8n, G.Gf8.exp(f, k)), U32.from_nat(k), hl))

# The exp table, for every field: entry i is gen^i (i < 510), then two 0s

def gt.elist(n: Nat, +f: G.Gf8Field, +k: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      [0, 0]
    case 1n+j:
      Con{G.Gf8.exp(f, k), gt.elist(j, f, 1n+k)}

def gt.elist_model(+f: G.Gf8Field) -> {gt.fe(510n, List.replicate(U32, A.Arrays.slots(9n), 0), f, 0n) == gt.elist(510n, f, 0n) : List<&2, U32>}:
  {==}

def gt.rep_len(+n: Nat) -> {List.length(&2, U32, List.replicate(U32, n, 0)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(Nat, List.length(&2, U32, List.replicate(U32, k, 0)), k, gt.rep_len(k)) : {1n+_ == 1n+k : Nat}
      {==}

def gt.hl_rep(+d: Nat) -> {List.length(&2, U32, List.replicate(U32, A.Arrays.slots(d), 0)) == A.Arrays.slots(d) : Nat}:
  gt.rep_len(A.Arrays.slots(d))

def gt.hl_elist(+f: G.Gf8Field) -> {List.length(&2, U32, gt.elist(510n, f, 0n)) == A.Arrays.slots(9n) : Nat}:
  {==}

def gt.f0() -> {U32.from_nat(0n) == 0 : U32}:
  {==}

def gt.e0(+f: G.Gf8Field) -> {G.Gf8.exp(f, 0n) == 1 : U32}:
  {==}

# the exp table of a field f, given that it is its fill (for a named field
# that is computation, proof_tab_cases.bend; it is stated per field because
# --verdict's kernel compares the two sides by running them)
def gt.exp_table(+f: G.Gf8Field, +e0: {T.Gf8Tab.exp_table(f) == T.gf8tab.fill.exp(510n, Array.new(U32, 9n, 0), f, 1, 0) : Array<U32>}) -> {T.Gf8Tab.exp_table(f) == A.Arrays.of_list(U32, 9n, gt.elist(510n, f, 0n), 0) : Array<U32>}:
  %Equal.sym(Array<U32>, T.Gf8Tab.exp_table(f), T.gf8tab.fill.exp(510n, Array.new(U32, 9n, 0), f, 1, 0), e0) : {_ == A.Arrays.of_list(U32, 9n, gt.elist(510n, f, 0n), 0) : Array<U32>}
  %Equal.sym(Array<U32>, Array.new(U32, 9n, 0), A.Arrays.of_list(U32, 9n, List.replicate(U32, A.Arrays.slots(9n), 0), 0), AL.of_list_new(U32, 9n, 0)) : {T.gf8tab.fill.exp(510n, _, f, 1, 0) == A.Arrays.of_list(U32, 9n, gt.elist(510n, f, 0n), 0) : Array<U32>}
  %gt.elist_model(f) : {T.gf8tab.fill.exp(510n, A.Arrays.of_list(U32, 9n, List.replicate(U32, A.Arrays.slots(9n), 0), 0), f, 1, 0) == A.Arrays.of_list(U32, 9n, _, 0) : Array<U32>}
  %gt.e0(f) : {T.gf8tab.fill.exp(510n, A.Arrays.of_list(U32, 9n, List.replicate(U32, A.Arrays.slots(9n), 0), 0), f, _, 0) == A.Arrays.of_list(U32, 9n, gt.fe(510n, List.replicate(U32, A.Arrays.slots(9n), 0), f, 0n), 0) : Array<U32>}
  %gt.f0() : {T.gf8tab.fill.exp(510n, A.Arrays.of_list(U32, 9n, List.replicate(U32, A.Arrays.slots(9n), 0), 0), f, G.Gf8.exp(f, 0n), _) == A.Arrays.of_list(U32, 9n, gt.fe(510n, List.replicate(U32, A.Arrays.slots(9n), 0), f, 0n), 0) : Array<U32>}
  gt.fill_exp(510n, List.replicate(U32, A.Arrays.slots(9n), 0), f, 0n, gt.hl_rep(9n))

# entry j of the exp table's list is gen^j, for j < 510
def gt.elist_nth(+n: Nat, +f: G.Gf8Field, +k: Nat, +j: Nat, h: {Nat.is_lt(j, n) == True{} : Bool}) -> {A.Arrays.nth(U32, gt.elist(n, f, k), j, 0) == G.Gf8.exp(f, Nat.add(j, k)) : U32}:
  match n j:
    case 0n 0n:
      Empty.absurd({A.Arrays.nth(U32, gt.elist(0n, f, k), 0n, 0) == G.Gf8.exp(f, Nat.add(0n, k)) : U32}, gt.ft(h))
    case 0n 1n+i:
      Empty.absurd({A.Arrays.nth(U32, gt.elist(0n, f, k), 1n+i, 0) == G.Gf8.exp(f, Nat.add(1n+i, k)) : U32}, gt.ft(h))
    case 1n+m 0n:
      {==}
    case 1n+m 1n+i:
      %gt.add_succ(i, k) : {A.Arrays.nth(U32, gt.elist(m, f, 1n+k), i, 0) == G.Gf8.exp(f, _) : U32}
      gt.elist_nth(m, f, 1n+k, i, h)

# The log table, for a field whose log list is given

def gt.log_table(+f: G.Gf8Field, +l: List<&2, U32>, +e0: {T.Gf8Tab.log_table(f) == T.gf8tab.fill.log(255n, Array.new(U32, 8n, 0), f, 1, 0) : Array<U32>}, +e: {gt.fl(255n, List.replicate(U32, A.Arrays.slots(8n), 0), f, 0n) == l : List<&2, U32>}) -> {T.Gf8Tab.log_table(f) == A.Arrays.of_list(U32, 8n, l, 0) : Array<U32>}:
  %Equal.sym(Array<U32>, T.Gf8Tab.log_table(f), T.gf8tab.fill.log(255n, Array.new(U32, 8n, 0), f, 1, 0), e0) : {_ == A.Arrays.of_list(U32, 8n, l, 0) : Array<U32>}
  %Equal.sym(Array<U32>, Array.new(U32, 8n, 0), A.Arrays.of_list(U32, 8n, List.replicate(U32, A.Arrays.slots(8n), 0), 0), AL.of_list_new(U32, 8n, 0)) : {T.gf8tab.fill.log(255n, _, f, 1, 0) == A.Arrays.of_list(U32, 8n, l, 0) : Array<U32>}
  %e : {T.gf8tab.fill.log(255n, A.Arrays.of_list(U32, 8n, List.replicate(U32, A.Arrays.slots(8n), 0), 0), f, 1, 0) == A.Arrays.of_list(U32, 8n, _, 0) : Array<U32>}
  %gt.e0(f) : {T.gf8tab.fill.log(255n, A.Arrays.of_list(U32, 8n, List.replicate(U32, A.Arrays.slots(8n), 0), 0), f, _, 0) == A.Arrays.of_list(U32, 8n, gt.fl(255n, List.replicate(U32, A.Arrays.slots(8n), 0), f, 0n), 0) : Array<U32>}
  %gt.f0() : {T.gf8tab.fill.log(255n, A.Arrays.of_list(U32, 8n, List.replicate(U32, A.Arrays.slots(8n), 0), 0), f, G.Gf8.exp(f, 0n), _) == A.Arrays.of_list(U32, 8n, gt.fl(255n, List.replicate(U32, A.Arrays.slots(8n), 0), f, 0n), 0) : Array<U32>}
  gt.fill_log(255n, List.replicate(U32, A.Arrays.slots(8n), 0), f, 0n, gt.hl_rep(8n))

# the log fill splits: n + m writes are n writes, then m more
def gt.fl_split(+n: Nat, +m: Nat, xs: List<&2, U32>, +f: G.Gf8Field, +k: Nat) -> {gt.fl(Nat.add(n, m), xs, f, k) == gt.fl(m, gt.fl(n, xs, f, k), f, Nat.add(n, k)) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+j:
      %gt.add_succ(j, k) : {gt.fl(Nat.add(j, m), List.set(&2, U32, xs, A.Arrays.index(8n, G.Gf8.exp(f, k)), U32.from_nat(k)), f, 1n+k) == gt.fl(m, gt.fl(j, List.set(&2, U32, xs, A.Arrays.index(8n, G.Gf8.exp(f, k)), U32.from_nat(k)), f, 1n+k), f, _) : List<&2, U32>}
      gt.fl_split(j, m, List.set(&2, U32, xs, A.Arrays.index(8n, G.Gf8.exp(f, k)), U32.from_nat(k)), f, 1n+k)

# A table whose lists are known

def gt.tab(+f: G.Gf8Field, +l: List<&2, U32>) -> T.Gf8Tab:
  T.Gf8Tab{A.Arrays.of_list(U32, 9n, gt.elist(510n, f, 0n), 0), A.Arrays.of_list(U32, 8n, l, 0)}

def gt.new(+f: G.Gf8Field, +l: List<&2, U32>, +ex0: {T.Gf8Tab.exp_table(f) == T.gf8tab.fill.exp(510n, Array.new(U32, 9n, 0), f, 1, 0) : Array<U32>}, +el0: {T.Gf8Tab.log_table(f) == T.gf8tab.fill.log(255n, Array.new(U32, 8n, 0), f, 1, 0) : Array<U32>}, +e: {gt.fl(255n, List.replicate(U32, A.Arrays.slots(8n), 0), f, 0n) == l : List<&2, U32>}) -> {gt.tab(f, l) == T.Gf8Tab.new(f) : T.Gf8Tab}:
  %Equal.sym(Array<U32>, T.Gf8Tab.exp_table(f), A.Arrays.of_list(U32, 9n, gt.elist(510n, f, 0n), 0), gt.exp_table(f, ex0)) : {gt.tab(f, l) == T.Gf8Tab{_, T.Gf8Tab.log_table(f)} : T.Gf8Tab}
  %Equal.sym(Array<U32>, T.Gf8Tab.log_table(f), A.Arrays.of_list(U32, 8n, l, 0), gt.log_table(f, l, el0, e)) : {gt.tab(f, l) == T.Gf8Tab{A.Arrays.of_list(U32, 9n, gt.elist(510n, f, 0n), 0), _} : T.Gf8Tab}
  {==}
