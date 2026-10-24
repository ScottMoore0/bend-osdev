# Proofs of LAWS_kmp.bend: KMP finds exactly what the reference finds.
#
# The theory of borders, on sets of prefix lengths. A set is a list of
# Bools, entry j for the prefix of j bytes. Reading byte c moves a set S
# to ext(S, c): the empty prefix, and j + 1 for each j in S whose next
# pattern byte is c (the shift-and automaton). B(k), the set after reading
# the pattern's own first k bytes, is the set of borders of those bytes
# (the prefixes they end with).
#
# * The prefix table is right (bd.ok): for every k, B(k) is k itself added
#   to B(table(k)), table(k) < k. The table is built by KMP's own step, so
#   this goes by induction along the table, with:
# * following the table loses nothing (bd.back_ok, bd.next_ok): from a
#   prefix of k bytes, the prefix KMP's step finds after byte c, q2, has
#   B(q2) = ext(B(k), c): strong induction along the table's entries.
# * the set's semantics (kp.gstep): what the shift-and automaton reports
#   from a set S on the rest of the text is the reference's matches,
#   preceded by those of the prefixes in S still to be completed.
#
# KMP's state q stands for B(q) (kp.run), and B(0) has no prefix to
# complete, so KMP reports what the reference reports.
import Base
import ./textsearch.bend as T
import ./auto.bend as A
import ./kmp.bend as K
import ./naive.bend as V
import ./proof_lib.bend as L
import ./LAWS_kmp.bend as Laws

# Sets of prefix lengths

def bd.hd(s: List<&2, Bool>) -> Bool:
  match s:
    case Nil{}:
      False{}
    case Con{b, t}:
      b

def bd.tl(s: List<&2, Bool>) -> List<&2, Bool>:
  match s:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      t

# entry n (False past the end)
def bd.get(s: List<&2, Bool>, n: Nat) -> Bool:
  match s n:
    case Nil{} _:
      False{}
    case Con{b, t} 0n:
      b
    case Con{b, t} 1n+j:
      bd.get(t, j)

# one False per pattern byte
def bd.falses(p: List<&2, U32>) -> List<&2, Bool>:
  match p:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      Con{False{}, bd.falses(t)}

# entry k set
def bd.set(k: Nat, +s: List<&2, Bool>) -> List<&2, Bool>:
  match k:
    case 0n:
      Con{True{}, bd.tl(s)}
    case 1n+j:
      Con{bd.hd(s), bd.set(j, bd.tl(s))}

# entry j + 1 of ext(S, c): j in S, and pattern byte j is c
def bd.zm(p: List<&2, U32>, +s: List<&2, Bool>, +c: U32) -> List<&2, Bool>:
  match p:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      Con{Bool.and(bd.hd(s), U32.is_eq(a, c)), bd.zm(t, bd.tl(s), c)}

# the set after byte c: one entry per prefix length 0 to the pattern's
def bd.ext(+p: List<&2, U32>, +s: List<&2, Bool>, +c: U32) -> List<&2, Bool>:
  Con{True{}, bd.zm(p, s, c)}

# the borders of the pattern's first k bytes
def bd.B(+p: List<&2, U32>, k: Nat) -> List<&2, Bool>:
  match k:
    case 0n:
      Con{True{}, bd.falses(p)}
    case 1n+ +j:
      bd.ext(p, bd.B(p, j), K.ts.kmp.at(p, j))

def bd.biff(x: Bool, +y: Bool) -> Bool:
  match x:
    case True{}:
      y
    case False{}:
      Bool.not(y)

# whether two sets are the same
def bd.beq(a: List<&2, Bool>, b: List<&2, Bool>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(bd.biff(x, y), bd.beq(xt, yt))
    case _ _:
      False{}

# entry j of a prefix table is right: below j + 1, and the borders of
# j + 1 bytes are j + 1 and the borders of entry j's
def bd.ok1(+p: List<&2, U32>, +fail: List<&2, Nat>, +j: Nat) -> Bool:
  Bool.and(Nat.is_lt(K.ts.kmp.nat_at(fail, j), 1n+j), bd.beq(bd.B(p, 1n+j), bd.set(1n+j, bd.B(p, K.ts.kmp.nat_at(fail, j)))))

# entries 0 to k - 1 are right
def bd.ok(+p: List<&2, U32>, +fail: List<&2, Nat>, k: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+ +j:
      Bool.and(bd.ok(p, fail, j), bd.ok1(p, fail, j))

# Sets: equality

def bd.biff_eq(+x: Bool, +y: Bool, +e: {bd.biff(x, y) == True{} : Bool}) -> {x == y : Bool}:
  match x:
    case True{}:
      Equal.sym(Bool, y, True{}, e)
    case False{}:
      match y:
        case True{}:
          L.tsl.absurd(Bool, False{}, True{}, e)
        case False{}:
          {==}

def bd.beq_eq(a: List<&2, Bool>, b: List<&2, Bool>, +e: {bd.beq(a, b) == True{} : Bool}) -> {a == b : List<&2, Bool>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+y, +yt}:
      L.tsl.absurd(List<&2, Bool>, Nil{}, Con{y, yt}, e)
    case Con{+x, +xt} Nil{}:
      L.tsl.absurd(List<&2, Bool>, Con{x, xt}, Nil{}, e)
    case Con{+x, +xt} Con{+y, +yt}:
      %bd.biff_eq(x, y, L.tsl.and_l(bd.biff(x, y), bd.beq(xt, yt), e)) : {Con{x, xt} == Con{_, yt} : List<&2, Bool>}
      %bd.beq_eq(xt, yt, L.tsl.and_r(bd.biff(x, y), bd.beq(xt, yt), e)) : {Con{x, xt} == Con{x, _} : List<&2, Bool>}
      {==}

def bd.biff_refl(+x: Bool) -> {bd.biff(x, x) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def bd.beq_refl(a: List<&2, Bool>) -> {bd.beq(a, a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +xt}:
      %Equal.sym(Bool, bd.biff(x, x), True{}, bd.biff_refl(x)) : {Bool.and(_, bd.beq(xt, xt)) == True{} : Bool}
      bd.beq_refl(xt)

# Sets: entries

def bd.get0(s: List<&2, Bool>) -> {bd.get(s, 0n) == bd.hd(s) : Bool}:
  match s:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      {==}

def bd.get_tl(s: List<&2, Bool>, +n: Nat) -> {bd.get(s, 1n+n) == bd.get(bd.tl(s), n) : Bool}:
  match s:
    case Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+ +j:
          {==}
    case Con{+b, +t}:
      {==}

def bd.get_falses(p: List<&2, U32>, n: Nat) -> {bd.get(bd.falses(p), n) == False{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      match n:
        case 0n:
          {==}
        case 1n+ +j:
          bd.get_falses(t, j)

# entry n of zm(p, S, c): entry n of S, and pattern byte n is c
def bd.get_zm(p: List<&2, U32>, +s: List<&2, Bool>, +c: U32, n: Nat, +h: {Nat.is_lt(n, List.length(&2, U32, p)) == True{} : Bool}) -> {bd.get(bd.zm(p, s, c), n) == Bool.and(bd.get(s, n), U32.is_eq(K.ts.kmp.at(p, n), c)) : Bool}:
  match p:
    case Nil{}:
      L.tsl.lt_zero_abs(Bool, bd.get(Nil{}, n), Bool.and(bd.get(s, n), U32.is_eq(0, c)), n, h)
    case Con{+a, +t}:
      match n:
        case 0n:
          %Equal.sym(Bool, bd.get(s, 0n), bd.hd(s), bd.get0(s)) : {Bool.and(bd.hd(s), U32.is_eq(a, c)) == Bool.and(_, U32.is_eq(a, c)) : Bool}
          {==}
        case 1n+ +j:
          %Equal.sym(Bool, bd.get(s, 1n+j), bd.get(bd.tl(s), j), bd.get_tl(s, j)) : {bd.get(bd.zm(t, bd.tl(s), c), j) == Bool.and(_, U32.is_eq(K.ts.kmp.at(t, j), c)) : Bool}
          bd.get_zm(t, bd.tl(s), c, j, h)

# Sets: ext and set

# no prefix in the set: none after a byte either
def bd.zm_falses(q: List<&2, U32>, +c: U32) -> {bd.zm(q, Con{False{}, bd.falses(q)}, c) == bd.falses(q) : List<&2, Bool>}:
  match q:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      %bd.zm_falses(t, c) : {Con{False{}, bd.zm(t, Con{False{}, bd.falses(t)}, c)} == Con{False{}, _} : List<&2, Bool>}
      {==}

# an entry whose next byte is not c adds nothing after c
def bd.zm_set_miss(k: Nat, p: List<&2, U32>, +s: List<&2, Bool>, +c: U32, +h: {U32.is_eq(K.ts.kmp.at(p, k), c) == False{} : Bool}) -> {bd.zm(p, bd.set(k, s), c) == bd.zm(p, s, c) : List<&2, Bool>}:
  match k:
    case 0n:
      match p:
        case Nil{}:
          {==}
        case Con{+a, +t}:
          %Equal.sym(Bool, U32.is_eq(a, c), False{}, h) : {Con{_, bd.zm(t, bd.tl(s), c)} == Con{Bool.and(bd.hd(s), _), bd.zm(t, bd.tl(s), c)} : List<&2, Bool>}
          %Equal.sym(Bool, Bool.and(bd.hd(s), False{}), False{}, L.tsl.and_false_r(bd.hd(s))) : {Con{False{}, bd.zm(t, bd.tl(s), c)} == Con{_, bd.zm(t, bd.tl(s), c)} : List<&2, Bool>}
          {==}
    case 1n+ +j:
      match p:
        case Nil{}:
          {==}
        case Con{+a, +t}:
          %bd.zm_set_miss(j, t, bd.tl(s), c, h) : {Con{Bool.and(bd.hd(s), U32.is_eq(a, c)), bd.zm(t, bd.set(j, bd.tl(s)), c)} == Con{Bool.and(bd.hd(s), U32.is_eq(a, c)), _} : List<&2, Bool>}
          {==}

# an entry whose next byte is c moves up one after c
def bd.zm_set_hit(k: Nat, p: List<&2, U32>, +s: List<&2, Bool>, +c: U32, +h: {U32.is_eq(K.ts.kmp.at(p, k), c) == True{} : Bool}, +hk: {Nat.is_lt(k, List.length(&2, U32, p)) == True{} : Bool}) -> {bd.zm(p, bd.set(k, s), c) == bd.set(k, bd.zm(p, s, c)) : List<&2, Bool>}:
  match k:
    case 0n:
      match p:
        case Nil{}:
          L.tsl.absurd(List<&2, Bool>, Nil{}, Con{True{}, Nil{}}, hk)
        case Con{+a, +t}:
          %Equal.sym(Bool, U32.is_eq(a, c), True{}, h) : {Con{_, bd.zm(t, bd.tl(s), c)} == Con{True{}, bd.zm(t, bd.tl(s), c)} : List<&2, Bool>}
          {==}
    case 1n+ +j:
      match p:
        case Nil{}:
          L.tsl.absurd(List<&2, Bool>, Nil{}, bd.set(1n+j, Nil{}), hk)
        case Con{+a, +t}:
          %bd.zm_set_hit(j, t, bd.tl(s), c, h, hk) : {Con{Bool.and(bd.hd(s), U32.is_eq(a, c)), bd.zm(t, bd.set(j, bd.tl(s)), c)} == Con{Bool.and(bd.hd(s), U32.is_eq(a, c)), _} : List<&2, Bool>}
          {==}

# Prefix tables: what bd.ok says

def bd.ok_l(+p: List<&2, U32>, +fail: List<&2, Nat>, +j: Nat, +h: {bd.ok(p, fail, 1n+j) == True{} : Bool}) -> {bd.ok(p, fail, j) == True{} : Bool}:
  L.tsl.and_l(bd.ok(p, fail, j), bd.ok1(p, fail, j), h)

def bd.ok_r(+p: List<&2, U32>, +fail: List<&2, Nat>, +j: Nat, +h: {bd.ok(p, fail, 1n+j) == True{} : Bool}) -> {bd.ok1(p, fail, j) == True{} : Bool}:
  L.tsl.and_r(bd.ok(p, fail, j), bd.ok1(p, fail, j), h)

# entry j is below j + 1
def bd.ok_lt(+p: List<&2, U32>, +fail: List<&2, Nat>, +j: Nat, +h: {bd.ok(p, fail, 1n+j) == True{} : Bool}) -> {Nat.is_lt(K.ts.kmp.nat_at(fail, j), 1n+j) == True{} : Bool}:
  L.tsl.and_l(Nat.is_lt(K.ts.kmp.nat_at(fail, j), 1n+j), bd.beq(bd.B(p, 1n+j), bd.set(1n+j, bd.B(p, K.ts.kmp.nat_at(fail, j)))), bd.ok_r(p, fail, j, h))

# the borders of j + 1 bytes: j + 1, and the borders of entry j
def bd.ok_eq(+p: List<&2, U32>, +fail: List<&2, Nat>, +j: Nat, +h: {bd.ok(p, fail, 1n+j) == True{} : Bool}) -> {bd.B(p, 1n+j) == bd.set(1n+j, bd.B(p, K.ts.kmp.nat_at(fail, j))) : List<&2, Bool>}:
  bd.beq_eq(bd.B(p, 1n+j), bd.set(1n+j, bd.B(p, K.ts.kmp.nat_at(fail, j))), L.tsl.and_r(Nat.is_lt(K.ts.kmp.nat_at(fail, j), 1n+j), bd.beq(bd.B(p, 1n+j), bd.set(1n+j, bd.B(p, K.ts.kmp.nat_at(fail, j)))), bd.ok_r(p, fail, j, h)))

def bd.ok_mono_k(b: Bool, +k: Nat, +j: Nat, +p: List<&2, U32>, +fail: List<&2, Nat>, +h: {bd.ok(p, fail, 1n+k) == True{} : Bool}, +hle: {Nat.is_lt(j, 2n+k) == True{} : Bool}, +e: {Nat.is_lt(j, 1n+k) == b : Bool}, rec: {Nat.is_lt(j, 1n+k) == True{} : Bool} -> {bd.ok(p, fail, j) == True{} : Bool}) -> {bd.ok(p, fail, j) == True{} : Bool}:
  match b:
    case True{}:
      rec(e)
    case False{}:
      %Equal.sym(Nat, j, 1n+k, L.tsl.lt_succ_eq(j, 1n+k, hle, e)) : {bd.ok(p, fail, _) == True{} : Bool}
      h

# entries below k right: entries below any j up to k right
def bd.ok_mono(k: Nat, +j: Nat, +p: List<&2, U32>, +fail: List<&2, Nat>, +h: {bd.ok(p, fail, k) == True{} : Bool}, +hle: {Nat.is_lt(j, 1n+k) == True{} : Bool}) -> {bd.ok(p, fail, j) == True{} : Bool}:
  match k:
    case 0n:
      match j:
        case 0n:
          {==}
        case 1n+ +i:
          L.tsl.lt_zero_abs(Bool, bd.ok(p, fail, 1n+i), True{}, i, hle)
    case 1n+ +k1:
      bd.ok_mono_k(Nat.is_lt(j, 1n+k1), k1, j, p, fail, h, hle, {==}, hl => bd.ok_mono(k1, j, p, fail, bd.ok_l(p, fail, k1, h), hl))

# Following the table loses nothing

def bd.k0_nil(b: Bool) -> {Con{True{}, Nil{}} == bd.B(Nil{}, K.ts.kmp.ext(b, 0n)) : List<&2, Bool>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def bd.k0_con(b: Bool, +a0: U32, +p1: List<&2, U32>, +c: U32, +e: {U32.is_eq(a0, c) == b : Bool}) -> {Con{True{}, Con{b, bd.falses(p1)}} == bd.B(Con{a0, p1}, K.ts.kmp.ext(b, 0n)) : List<&2, Bool>}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(a0, a0), True{}, L.tsl.u32_refl(a0)) : {Con{True{}, Con{True{}, bd.falses(p1)}} == Con{True{}, Con{_, bd.zm(p1, Con{False{}, bd.falses(p1)}, a0)}} : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, bd.zm(p1, Con{False{}, bd.falses(p1)}, a0), bd.falses(p1), bd.zm_falses(p1, a0)) : {Con{True{}, Con{True{}, bd.falses(p1)}} == Con{True{}, Con{True{}, _}} : List<&2, Bool>}
      {==}
    case False{}:
      {==}

# the empty prefix: after c, the prefix of one byte if the pattern starts
# with c, else the empty one
def bd.k0(p: List<&2, U32>, +c: U32) -> {bd.ext(p, bd.B(p, 0n), c) == bd.B(p, K.ts.kmp.ext(U32.is_eq(K.ts.kmp.at(p, 0n), c), 0n)) : List<&2, Bool>}:
  match p:
    case Nil{}:
      bd.k0_nil(U32.is_eq(0, c))
    case Con{+a0, +p1}:
      %Equal.sym(List<&2, Bool>, bd.zm(p1, Con{False{}, bd.falses(p1)}, c), bd.falses(p1), bd.zm_falses(p1, c)) : {Con{True{}, Con{U32.is_eq(a0, c), _}} == bd.B(Con{a0, p1}, K.ts.kmp.ext(U32.is_eq(a0, c), 0n)) : List<&2, Bool>}
      bd.k0_con(U32.is_eq(a0, c), a0, p1, c, {==})

def bd.back_step(b: Bool, +f: Nat, +j: Nat, +p: List<&2, U32>, +fail: List<&2, Nat>, +c: U32, +h_ok: {bd.ok(p, fail, 1n+j) == True{} : Bool}, +h_f: {Nat.is_lt(1n+j, 1n+f) == True{} : Bool}, +e: {U32.is_eq(K.ts.kmp.at(p, 1n+j), c) == b : Bool}, rec: {bd.ok(p, fail, K.ts.kmp.nat_at(fail, j)) == True{} : Bool} -> {Nat.is_lt(K.ts.kmp.nat_at(fail, j), f) == True{} : Bool} -> {bd.ext(p, bd.B(p, K.ts.kmp.nat_at(fail, j)), c) == bd.B(p, K.ts.kmp.ext(U32.is_eq(K.ts.kmp.at(p, K.ts.kmp.back(f, p, fail, c, K.ts.kmp.nat_at(fail, j))), c), K.ts.kmp.back(f, p, fail, c, K.ts.kmp.nat_at(fail, j)))) : List<&2, Bool>}) -> {bd.ext(p, bd.B(p, 1n+j), c) == bd.B(p, K.ts.kmp.ext(U32.is_eq(K.ts.kmp.at(p, K.ts.kmp.back.pick(b, 1n+j, K.ts.kmp.back(f, p, fail, c, K.ts.kmp.nat_at(fail, j)))), c), K.ts.kmp.back.pick(b, 1n+j, K.ts.kmp.back(f, p, fail, c, K.ts.kmp.nat_at(fail, j))))) : List<&2, Bool>}:
  match b:
    case True{}:
      %Equal.sym(Bool, U32.is_eq(K.ts.kmp.at(p, 1n+j), c), True{}, e) : {bd.ext(p, bd.B(p, 1n+j), c) == bd.B(p, K.ts.kmp.ext(_, 1n+j)) : List<&2, Bool>}
      %L.tsl.u32_eq(K.ts.kmp.at(p, 1n+j), c, e) : {bd.ext(p, bd.B(p, 1n+j), _) == bd.ext(p, bd.B(p, 1n+j), K.ts.kmp.at(p, 1n+j)) : List<&2, Bool>}
      {==}
    case False{}:
      %Equal.sym(List<&2, Bool>, bd.B(p, 1n+j), bd.set(1n+j, bd.B(p, K.ts.kmp.nat_at(fail, j))), bd.ok_eq(p, fail, j, h_ok)) : {bd.ext(p, _, c) == bd.B(p, K.ts.kmp.ext(U32.is_eq(K.ts.kmp.at(p, K.ts.kmp.back(f, p, fail, c, K.ts.kmp.nat_at(fail, j))), c), K.ts.kmp.back(f, p, fail, c, K.ts.kmp.nat_at(fail, j)))) : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, bd.zm(p, bd.set(1n+j, bd.B(p, K.ts.kmp.nat_at(fail, j))), c), bd.zm(p, bd.B(p, K.ts.kmp.nat_at(fail, j)), c), bd.zm_set_miss(1n+j, p, bd.B(p, K.ts.kmp.nat_at(fail, j)), c, e)) : {Con{True{}, _} == bd.B(p, K.ts.kmp.ext(U32.is_eq(K.ts.kmp.at(p, K.ts.kmp.back(f, p, fail, c, K.ts.kmp.nat_at(fail, j))), c), K.ts.kmp.back(f, p, fail, c, K.ts.kmp.nat_at(fail, j)))) : List<&2, Bool>}
      rec(bd.ok_mono(j, K.ts.kmp.nat_at(fail, j), p, fail, bd.ok_l(p, fail, j, h_ok), bd.ok_lt(p, fail, j, h_ok)), L.tsl.lt_le_trans(K.ts.kmp.nat_at(fail, j), 1n+j, f, bd.ok_lt(p, fail, j, h_ok), h_f))

# from a prefix of k bytes and byte c, the prefix the walk along the table
# finds, r, and then r + 1 if pattern byte r is c: its borders are the set
# after c from the borders of k
def bd.back_ok(fuel: Nat, k: Nat, +p: List<&2, U32>, +fail: List<&2, Nat>, +c: U32, +h_ok: {bd.ok(p, fail, k) == True{} : Bool}, +h_f: {Nat.is_lt(k, fuel) == True{} : Bool}) -> {bd.ext(p, bd.B(p, k), c) == bd.B(p, K.ts.kmp.ext(U32.is_eq(K.ts.kmp.at(p, K.ts.kmp.back(fuel, p, fail, c, k)), c), K.ts.kmp.back(fuel, p, fail, c, k))) : List<&2, Bool>}:
  match fuel:
    case 0n:
      match k:
        case 0n:
          bd.k0(p, c)
        case 1n+ +j:
          L.tsl.absurd(List<&2, Bool>, bd.ext(p, bd.B(p, 1n+j), c), bd.B(p, K.ts.kmp.ext(U32.is_eq(K.ts.kmp.at(p, 0n), c), 0n)), h_f)
    case 1n+ +f:
      match k:
        case 0n:
          bd.k0(p, c)
        case 1n+ +j:
          bd.back_step(U32.is_eq(K.ts.kmp.at(p, 1n+j), c), f, j, p, fail, c, h_ok, h_f, {==}, h1 => h2 => bd.back_ok(f, K.ts.kmp.nat_at(fail, j), p, fail, c, h1, h2))

# KMP's step from a prefix of k bytes: its borders are the set after c
def bd.next_ok(+k: Nat, +p: List<&2, U32>, +fail: List<&2, Nat>, +c: U32, +h_ok: {bd.ok(p, fail, k) == True{} : Bool}) -> {bd.ext(p, bd.B(p, k), c) == bd.B(p, K.ts.kmp.next(p, fail, c, k)) : List<&2, Bool>}:
  bd.back_ok(1n+k, k, p, fail, c, h_ok, L.tsl.lt_succ(k))

# The walk and the step stay below k + 1 and k + 2

def bd.back_le_step(b: Bool, +f: Nat, +j: Nat, +p: List<&2, U32>, +fail: List<&2, Nat>, +c: U32, +h_ok: {bd.ok(p, fail, 1n+j) == True{} : Bool}, +h_f: {Nat.is_lt(1n+j, 1n+f) == True{} : Bool}, rec: {bd.ok(p, fail, K.ts.kmp.nat_at(fail, j)) == True{} : Bool} -> {Nat.is_lt(K.ts.kmp.nat_at(fail, j), f) == True{} : Bool} -> {Nat.is_lt(K.ts.kmp.back(f, p, fail, c, K.ts.kmp.nat_at(fail, j)), 1n+K.ts.kmp.nat_at(fail, j)) == True{} : Bool}) -> {Nat.is_lt(K.ts.kmp.back.pick(b, 1n+j, K.ts.kmp.back(f, p, fail, c, K.ts.kmp.nat_at(fail, j))), 2n+j) == True{} : Bool}:
  match b:
    case True{}:
      L.tsl.lt_succ(j)
    case False{}:
      L.tsl.lt_weak(K.ts.kmp.back(f, p, fail, c, K.ts.kmp.nat_at(fail, j)), 1n+j, L.tsl.lt_le_trans(K.ts.kmp.back(f, p, fail, c, K.ts.kmp.nat_at(fail, j)), 1n+K.ts.kmp.nat_at(fail, j), 1n+j, rec(bd.ok_mono(j, K.ts.kmp.nat_at(fail, j), p, fail, bd.ok_l(p, fail, j, h_ok), bd.ok_lt(p, fail, j, h_ok)), L.tsl.lt_le_trans(K.ts.kmp.nat_at(fail, j), 1n+j, f, bd.ok_lt(p, fail, j, h_ok), h_f)), bd.ok_lt(p, fail, j, h_ok)))

def bd.back_le(fuel: Nat, k: Nat, +p: List<&2, U32>, +fail: List<&2, Nat>, +c: U32, +h_ok: {bd.ok(p, fail, k) == True{} : Bool}, +h_f: {Nat.is_lt(k, fuel) == True{} : Bool}) -> {Nat.is_lt(K.ts.kmp.back(fuel, p, fail, c, k), 1n+k) == True{} : Bool}:
  match fuel:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+ +j:
          {==}
    case 1n+ +f:
      match k:
        case 0n:
          {==}
        case 1n+ +j:
          bd.back_le_step(U32.is_eq(K.ts.kmp.at(p, 1n+j), c), f, j, p, fail, c, h_ok, h_f, h1 => h2 => bd.back_le(f, K.ts.kmp.nat_at(fail, j), p, fail, c, h1, h2))

def bd.next_le_h(b: Bool, +k1: Nat, +k: Nat, +h: {Nat.is_lt(k1, 1n+k) == True{} : Bool}) -> {Nat.is_lt(K.ts.kmp.ext(b, k1), 2n+k) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      L.tsl.lt_weak(k1, 1n+k, h)

# KMP's step from a prefix of k bytes finds at most k + 1
def bd.next_le(+k: Nat, +p: List<&2, U32>, +fail: List<&2, Nat>, +c: U32, +h_ok: {bd.ok(p, fail, k) == True{} : Bool}) -> {Nat.is_lt(K.ts.kmp.next(p, fail, c, k), 2n+k) == True{} : Bool}:
  bd.next_le_h(U32.is_eq(K.ts.kmp.at(p, K.ts.kmp.back(1n+k, p, fail, c, k)), c), K.ts.kmp.back(1n+k, p, fail, c, k), k, bd.back_le(1n+k, k, p, fail, c, h_ok, L.tsl.lt_succ(k)))

# The prefix table is right

def bd.nat_at_app(acc: List<&2, Nat>, +ys: List<&2, Nat>, j: Nat, +h: {Nat.is_lt(j, List.length(&2, Nat, acc)) == True{} : Bool}) -> {K.ts.kmp.nat_at(List.append(&2, Nat, acc, ys), j) == K.ts.kmp.nat_at(acc, j) : Nat}:
  match acc:
    case Nil{}:
      L.tsl.lt_zero_abs(Nat, K.ts.kmp.nat_at(ys, j), 0n, j, h)
    case Con{+x, +t}:
      match j:
        case 0n:
          {==}
        case 1n+ +i:
          bd.nat_at_app(t, ys, i, h)

def bd.nat_at_end(acc: List<&2, Nat>, +x: Nat) -> {K.ts.kmp.nat_at(List.append(&2, Nat, acc, [x]), List.length(&2, Nat, acc)) == x : Nat}:
  match acc:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      bd.nat_at_end(t, x)

def bd.len_app1(acc: List<&2, Nat>, +x: Nat) -> {List.length(&2, Nat, List.append(&2, Nat, acc, [x])) == 1n+List.length(&2, Nat, acc) : Nat}:
  match acc:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      %bd.len_app1(t, x) : {1n+List.length(&2, Nat, List.append(&2, Nat, t, [x])) == 1n+_ : Nat}
      {==}

# entries below the length of acc: the same after more are appended
def bd.ok_app(k: Nat, +p: List<&2, U32>, +acc: List<&2, Nat>, +ys: List<&2, Nat>, +h: {Nat.is_lt(k, 1n+List.length(&2, Nat, acc)) == True{} : Bool}) -> {bd.ok(p, List.append(&2, Nat, acc, ys), k) == bd.ok(p, acc, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      %Equal.sym(Nat, K.ts.kmp.nat_at(List.append(&2, Nat, acc, ys), j), K.ts.kmp.nat_at(acc, j), bd.nat_at_app(acc, ys, j, h)) : {Bool.and(bd.ok(p, List.append(&2, Nat, acc, ys), j), Bool.and(Nat.is_lt(_, 1n+j), bd.beq(bd.B(p, 1n+j), bd.set(1n+j, bd.B(p, _))))) == Bool.and(bd.ok(p, acc, j), bd.ok1(p, acc, j)) : Bool}
      %Equal.sym(Bool, bd.ok(p, List.append(&2, Nat, acc, ys), j), bd.ok(p, acc, j), bd.ok_app(j, p, acc, ys, L.tsl.lt_weak(j, List.length(&2, Nat, acc), h))) : {Bool.and(_, bd.ok1(p, acc, j)) == Bool.and(bd.ok(p, acc, j), bd.ok1(p, acc, j)) : Bool}
      {==}

def bd.nil_con(-b: U32, -t: List<&2, U32>, +e: {Nil{} == Con{b, t} : List<&2, U32>}) -> {False{} == True{} : Bool}:
  Equal.sym(Bool, True{}, False{}, Equal.cong(List<&2, U32>, Bool, xs => List.is_empty(&2, U32, xs), Nil{}, Con{b, t}, e))

def bd.con_hd(-x: U32, -xs: List<&2, U32>, -b: U32, -t: List<&2, U32>, +e: {Con{x, xs} == Con{b, t} : List<&2, U32>}) -> {x == b : U32}:
  Equal.cong(List<&2, U32>, U32, ys => K.ts.kmp.at(ys, 0n), Con{x, xs}, Con{b, t}, e)

def bd.con_tl(-x: U32, -xs: List<&2, U32>, -b: U32, -t: List<&2, U32>, +e: {Con{x, xs} == Con{b, t} : List<&2, U32>}) -> {xs == t : List<&2, U32>}:
  Equal.cong(List<&2, U32>, List<&2, U32>, ys => List.tail(&2, U32, ys), Con{x, xs}, Con{b, t}, e)

def bd.drop0(xs: List<&2, U32>) -> {List.drop(&2, U32, xs, 0n) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      {==}

# the rest from n is b then t: byte n is b
def bd.drop_at(p: List<&2, U32>, n: Nat, -b: U32, -t: List<&2, U32>, +e: {List.drop(&2, U32, p, n) == Con{b, t} : List<&2, U32>}) -> {K.ts.kmp.at(p, n) == b : U32}:
  match p:
    case Nil{}:
      L.tsl.absurd(U32, 0, b, bd.nil_con(b, t, e))
    case Con{+x, +q}:
      match n:
        case 0n:
          bd.con_hd(x, q, b, t, e)
        case 1n+ +i:
          bd.drop_at(q, i, b, t, e)

# ... and the rest from n + 1 is t
def bd.drop_tl(p: List<&2, U32>, n: Nat, -b: U32, -t: List<&2, U32>, +e: {List.drop(&2, U32, p, n) == Con{b, t} : List<&2, U32>}) -> {List.drop(&2, U32, p, 1n+n) == t : List<&2, U32>}:
  match p:
    case Nil{}:
      L.tsl.absurd(List<&2, U32>, Nil{}, t, bd.nil_con(b, t, e))
    case Con{+x, +q}:
      match n:
        case 0n:
          Equal.trans(List<&2, U32>, List.drop(&2, U32, q, 0n), q, t, bd.drop0(q), bd.con_tl(x, q, b, t, e))
        case 1n+ +i:
          bd.drop_tl(q, i, b, t, e)

# one entry more: the borders of i + 2 bytes are i + 2 and those of the
# entry the step finds
def bd.tab_step(+p: List<&2, U32>, +acc: List<&2, Nat>, +k: Nat, +i: Nat, +b: U32, +h_ok: {bd.ok(p, acc, 1n+i) == True{} : Bool}, +h_k: {K.ts.kmp.nat_at(acc, i) == k : Nat}, +h_b: {K.ts.kmp.at(p, 1n+i) == b : U32}, +h_lt: {Nat.is_lt(1n+i, List.length(&2, U32, p)) == True{} : Bool}, +h_okk: {bd.ok(p, acc, k) == True{} : Bool}) -> {bd.B(p, 2n+i) == bd.set(2n+i, bd.B(p, K.ts.kmp.next(p, acc, b, k))) : List<&2, Bool>}:
  %Equal.sym(U32, K.ts.kmp.at(p, 1n+i), b, h_b) : {bd.ext(p, bd.B(p, 1n+i), _) == bd.set(2n+i, bd.B(p, K.ts.kmp.next(p, acc, b, k))) : List<&2, Bool>}
  %Equal.sym(List<&2, Bool>, bd.B(p, 1n+i), bd.set(1n+i, bd.B(p, K.ts.kmp.nat_at(acc, i))), bd.ok_eq(p, acc, i, h_ok)) : {bd.ext(p, _, b) == bd.set(2n+i, bd.B(p, K.ts.kmp.next(p, acc, b, k))) : List<&2, Bool>}
  %Equal.sym(Nat, K.ts.kmp.nat_at(acc, i), k, h_k) : {bd.ext(p, bd.set(1n+i, bd.B(p, _)), b) == bd.set(2n+i, bd.B(p, K.ts.kmp.next(p, acc, b, k))) : List<&2, Bool>}
  %Equal.sym(List<&2, Bool>, bd.zm(p, bd.set(1n+i, bd.B(p, k)), b), bd.set(1n+i, bd.zm(p, bd.B(p, k), b)), bd.zm_set_hit(1n+i, p, bd.B(p, k), b, Equal.trans(Bool, U32.is_eq(K.ts.kmp.at(p, 1n+i), b), U32.is_eq(b, b), True{}, Equal.cong(U32, Bool, x => U32.is_eq(x, b), K.ts.kmp.at(p, 1n+i), b, h_b), L.tsl.u32_refl(b)), h_lt)) : {Con{True{}, _} == bd.set(2n+i, bd.B(p, K.ts.kmp.next(p, acc, b, k))) : List<&2, Bool>}
  %bd.next_ok(k, p, acc, b, h_okk) : {bd.set(2n+i, bd.ext(p, bd.B(p, k), b)) == bd.set(2n+i, _) : List<&2, Bool>}
  {==}

# the table with one entry more is right up to it
def bd.tab_ok2(+p: List<&2, U32>, +acc: List<&2, Nat>, +k: Nat, +i: Nat, +b: U32, +t: List<&2, U32>, +h_ok: {bd.ok(p, acc, 1n+i) == True{} : Bool}, +h_len: {List.length(&2, Nat, acc) == 1n+i : Nat}, +h_k: {K.ts.kmp.nat_at(acc, i) == k : Nat}, +h_xs: {List.drop(&2, U32, p, 1n+i) == Con{b, t} : List<&2, U32>}, +h_m: {List.length(&2, U32, p) == Nat.add(1n+i, 1n+List.length(&2, U32, t)) : Nat}) -> {bd.ok(p, List.append(&2, Nat, acc, [K.ts.kmp.next(p, acc, b, k)]), 2n+i) == True{} : Bool}:
  +k2 = K.ts.kmp.next(p, acc, b, k)
  +acc2 = List.append(&2, Nat, acc, [k2])
  +e_k2 = Equal.trans(Nat, K.ts.kmp.nat_at(acc2, 1n+i), K.ts.kmp.nat_at(acc2, List.length(&2, Nat, acc)), k2, Equal.cong(Nat, Nat, n => K.ts.kmp.nat_at(acc2, n), 1n+i, List.length(&2, Nat, acc), Equal.sym(Nat, List.length(&2, Nat, acc), 1n+i, h_len)), bd.nat_at_end(acc, k2))
  +h_ki = Equal.trans(Bool, Nat.is_lt(k, 1n+i), Nat.is_lt(K.ts.kmp.nat_at(acc, i), 1n+i), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(n, 1n+i), k, K.ts.kmp.nat_at(acc, i), Equal.sym(Nat, K.ts.kmp.nat_at(acc, i), k, h_k)), bd.ok_lt(p, acc, i, h_ok))
  +h_okk = bd.ok_mono(1n+i, k, p, acc, h_ok, L.tsl.lt_weak(k, 1n+i, h_ki))
  +h_lt = Equal.trans(Bool, Nat.is_lt(1n+i, List.length(&2, U32, p)), Nat.is_lt(1n+i, Nat.add(1n+i, 1n+List.length(&2, U32, t))), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(1n+i, n), List.length(&2, U32, p), Nat.add(1n+i, 1n+List.length(&2, U32, t)), h_m), L.tsl.lt_add(1n+i, List.length(&2, U32, t)))
  +e_tab = bd.tab_step(p, acc, k, i, b, h_ok, h_k, bd.drop_at(p, 1n+i, b, t, h_xs), h_lt, h_okk)
  +e_old = Equal.trans(Bool, bd.ok(p, acc2, 1n+i), bd.ok(p, acc, 1n+i), True{}, bd.ok_app(1n+i, p, acc, [k2], Equal.trans(Bool, Nat.is_lt(1n+i, 1n+List.length(&2, Nat, acc)), Nat.is_lt(1n+i, 2n+i), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(1n+i, 1n+n), List.length(&2, Nat, acc), 1n+i, h_len), L.tsl.lt_succ(1n+i))), h_ok)
  +e_lt2 = L.tsl.lt_le_trans(k2, 2n+k, 2n+i, bd.next_le(k, p, acc, b, h_okk), h_ki)
  +e_beq = Equal.trans(Bool, bd.beq(bd.B(p, 2n+i), bd.set(2n+i, bd.B(p, k2))), bd.beq(bd.set(2n+i, bd.B(p, k2)), bd.set(2n+i, bd.B(p, k2))), True{}, Equal.cong(List<&2, Bool>, Bool, x => bd.beq(x, bd.set(2n+i, bd.B(p, k2))), bd.B(p, 2n+i), bd.set(2n+i, bd.B(p, k2)), e_tab), bd.beq_refl(bd.set(2n+i, bd.B(p, k2))))
  %Equal.sym(Nat, K.ts.kmp.nat_at(acc2, 1n+i), k2, e_k2) : {Bool.and(bd.ok(p, acc2, 1n+i), Bool.and(Nat.is_lt(_, 2n+i), bd.beq(bd.B(p, 2n+i), bd.set(2n+i, bd.B(p, _))))) == True{} : Bool}
  %Equal.sym(Bool, bd.ok(p, acc2, 1n+i), True{}, e_old) : {Bool.and(_, Bool.and(Nat.is_lt(k2, 2n+i), bd.beq(bd.B(p, 2n+i), bd.set(2n+i, bd.B(p, k2))))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_lt(k2, 2n+i), True{}, e_lt2) : {Bool.and(True{}, Bool.and(_, bd.beq(bd.B(p, 2n+i), bd.set(2n+i, bd.B(p, k2))))) == True{} : Bool}
  e_beq

# the table under construction: acc holds entries 0 to i, all right, k is
# entry i, and xs is the rest of the pattern from byte i + 1
def bd.pi_go(xs: List<&2, U32>, +p: List<&2, U32>, +acc: List<&2, Nat>, +k: Nat, +i: Nat, +h_ok: {bd.ok(p, acc, 1n+i) == True{} : Bool}, +h_len: {List.length(&2, Nat, acc) == 1n+i : Nat}, +h_k: {K.ts.kmp.nat_at(acc, i) == k : Nat}, +h_xs: {List.drop(&2, U32, p, 1n+i) == xs : List<&2, U32>}, +h_m: {List.length(&2, U32, p) == Nat.add(1n+i, List.length(&2, U32, xs)) : Nat}) -> {bd.ok(p, K.ts.kmp.pi.go(xs, p, acc, k), List.length(&2, U32, p)) == True{} : Bool}:
  match xs:
    case Nil{}:
      %Equal.sym(Nat, List.length(&2, U32, p), 1n+i, Equal.trans(Nat, List.length(&2, U32, p), Nat.add(1n+i, 0n), 1n+i, h_m, L.tsl.add_zero(1n+i))) : {bd.ok(p, acc, _) == True{} : Bool}
      h_ok
    case Con{+b, +t}:
      +k2 = K.ts.kmp.next(p, acc, b, k)
      +acc2 = List.append(&2, Nat, acc, [k2])
      +e_len = Equal.trans(Nat, List.length(&2, Nat, acc2), 1n+List.length(&2, Nat, acc), 2n+i, bd.len_app1(acc, k2), Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Nat, acc), 1n+i, h_len))
      +e_k2 = Equal.trans(Nat, K.ts.kmp.nat_at(acc2, 1n+i), K.ts.kmp.nat_at(acc2, List.length(&2, Nat, acc)), k2, Equal.cong(Nat, Nat, n => K.ts.kmp.nat_at(acc2, n), 1n+i, List.length(&2, Nat, acc), Equal.sym(Nat, List.length(&2, Nat, acc), 1n+i, h_len)), bd.nat_at_end(acc, k2))
      bd.pi_go(t, p, acc2, k2, 1n+i, bd.tab_ok2(p, acc, k, i, b, t, h_ok, h_len, h_k, h_xs, h_m), e_len, e_k2, bd.drop_tl(p, 1n+i, b, t, h_xs), Equal.trans(Nat, List.length(&2, U32, p), Nat.add(1n+i, 1n+List.length(&2, U32, t)), 1n+Nat.add(1n+i, List.length(&2, U32, t)), h_m, L.tsl.add_succ(1n+i, List.length(&2, U32, t))))

# the first entry: the borders of one byte are 1 and 0
def bd.pi_first(+b0: U32, +t: List<&2, U32>) -> {bd.ok(Con{b0, t}, [0n], 1n) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(b0, b0), True{}, L.tsl.u32_refl(b0)) : {bd.beq(Con{True{}, Con{_, bd.zm(t, Con{False{}, bd.falses(t)}, b0)}}, Con{True{}, Con{True{}, bd.falses(t)}}) == True{} : Bool}
  %Equal.sym(List<&2, Bool>, bd.zm(t, Con{False{}, bd.falses(t)}, b0), bd.falses(t), bd.zm_falses(t, b0)) : {bd.beq(Con{True{}, Con{True{}, _}}, Con{True{}, Con{True{}, bd.falses(t)}}) == True{} : Bool}
  bd.beq_refl(Con{True{}, Con{True{}, bd.falses(t)}})

# KMP's prefix table is right, for every pattern of at least one byte
def bd.pi_ok(+b0: U32, +t: List<&2, U32>) -> {bd.ok(Con{b0, t}, K.ts.kmp.pi(Con{b0, t}), 1n+List.length(&2, U32, t)) == True{} : Bool}:
  bd.pi_go(t, Con{b0, t}, [0n], 0n, 0n, bd.pi_first(b0, t), {==}, {==}, bd.drop0(t), {==})

# The borders of k bytes: k is the largest

def bd.and_eq(b: Bool, +j: Nat, +n: Nat, +p: List<&2, U32>, +e: {Nat.is_eq(j, n) == b : Bool}) -> {Bool.and(b, U32.is_eq(K.ts.kmp.at(p, n), K.ts.kmp.at(p, j))) == b : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, j, n, L.tsl.nat_eq(j, n, e)) : {U32.is_eq(K.ts.kmp.at(p, n), K.ts.kmp.at(p, _)) == True{} : Bool}
      L.tsl.u32_refl(K.ts.kmp.at(p, n))
    case False{}:
      {==}

# entry n of the borders of k bytes, for k <= n <= the pattern's length:
# whether n is k
def bd.B_get(k: Nat, n: Nat, +p: List<&2, U32>, +h1: {Nat.is_lt(k, 1n+n) == True{} : Bool}, +h2: {Nat.is_lt(n, 1n+List.length(&2, U32, p)) == True{} : Bool}) -> {bd.get(bd.B(p, k), n) == Nat.is_eq(k, n) : Bool}:
  match k:
    case 0n:
      match n:
        case 0n:
          {==}
        case 1n+ +i:
          bd.get_falses(p, i)
    case 1n+ +j:
      match n:
        case 0n:
          L.tsl.lt_zero_abs(Bool, bd.get(bd.B(p, 1n+j), 0n), False{}, j, h1)
        case 1n+ +i:
          %Equal.sym(Bool, bd.get(bd.zm(p, bd.B(p, j), K.ts.kmp.at(p, j)), i), Bool.and(bd.get(bd.B(p, j), i), U32.is_eq(K.ts.kmp.at(p, i), K.ts.kmp.at(p, j))), bd.get_zm(p, bd.B(p, j), K.ts.kmp.at(p, j), i, h2)) : {_ == Nat.is_eq(1n+j, 1n+i) : Bool}
          %Equal.sym(Bool, bd.get(bd.B(p, j), i), Nat.is_eq(j, i), bd.B_get(j, i, p, h1, L.tsl.lt_weak(i, List.length(&2, U32, p), h2))) : {Bool.and(_, U32.is_eq(K.ts.kmp.at(p, i), K.ts.kmp.at(p, j))) == Nat.is_eq(1n+j, 1n+i) : Bool}
          bd.and_eq(Nat.is_eq(j, i), j, i, p, {==})

def bd.B_hd(+p: List<&2, U32>, k: Nat) -> {bd.hd(bd.B(p, k)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+ +j:
      {==}

# The shift-and automaton's semantics

def kp.hits(+h: Bool, +e: Nat, +xs: List<&2, Nat>) -> {V.ts.naive.hit(h, e, xs) == A.ts.auto.hit(h, e, xs) : List<&2, Nat>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

# the matches of the prefixes in the set still to be completed, in order:
# q is the pattern after the byte the set's first entry stands for, and
# the prefix whose rest is r ends a match |r| bytes on, if r follows
def kp.pend(q: List<&2, U32>, +s: List<&2, Bool>, +ys: List<&2, U32>, +pos: Nat) -> List<&2, Nat>:
  match q:
    case Nil{}:
      Nil{}
    case Con{+b, +r}:
      List.append(&2, Nat, kp.pend(r, bd.tl(s), ys, pos), V.ts.naive.hit(Bool.and(bd.hd(s), V.ts.naive.at(False{}, Con{b, r}, ys)), Nat.add(pos, List.length(&2, U32, Con{b, r})), Nil{}))

# what the shift-and automaton reports from set s on the text ys (the
# pattern a0 then p1): the prefixes still to complete, then the reference
# on ys (the prefix of no bytes is always in the set)
def kp.G(+a0: U32, +p1: List<&2, U32>, +s: List<&2, Bool>, +ys: List<&2, U32>, +pos: Nat) -> List<&2, Nat>:
  List.append(&2, Nat, kp.pend(p1, bd.tl(s), ys, pos), V.ts.naive.go(False{}, Con{a0, p1}, 1n+List.length(&2, U32, p1), ys, pos))

# the last entry of zm
def kp.lastz(q: List<&2, U32>, +s: List<&2, Bool>, +c: U32) -> Bool:
  match q:
    case Nil{}:
      False{}
    case Con{+b, +r}:
      bd.get(bd.zm(Con{b, r}, s, c), List.length(&2, U32, r))

# one byte: the shortest pending match ends, or the others move on
def kp.pshift(r: List<&2, U32>, +b: U32, +s: List<&2, Bool>, +c: U32, +t: List<&2, U32>, +pos: Nat) -> {kp.pend(Con{b, r}, s, Con{c, t}, pos) == V.ts.naive.hit(kp.lastz(Con{b, r}, s, c), 1n+pos, kp.pend(r, bd.zm(Con{b, r}, s, c), t, 1n+pos)) : List<&2, Nat>}:
  match r:
    case Nil{}:
      %Equal.sym(Bool, Bool.and(U32.is_eq(b, c), True{}), U32.is_eq(b, c), L.tsl.and_true_r(U32.is_eq(b, c))) : {V.ts.naive.hit(Bool.and(bd.hd(s), _), Nat.add(pos, 1n), Nil{}) == V.ts.naive.hit(Bool.and(bd.hd(s), U32.is_eq(b, c)), 1n+pos, Nil{}) : List<&2, Nat>}
      %Equal.sym(Nat, Nat.add(pos, 1n), 1n+pos, L.tsl.add_one(pos)) : {V.ts.naive.hit(Bool.and(bd.hd(s), U32.is_eq(b, c)), _, Nil{}) == V.ts.naive.hit(Bool.and(bd.hd(s), U32.is_eq(b, c)), 1n+pos, Nil{}) : List<&2, Nat>}
      {==}
    case Con{+b2, +r2}:
      +LZ = kp.lastz(Con{b2, r2}, bd.tl(s), c)
      +X = kp.pend(r2, bd.zm(Con{b2, r2}, bd.tl(s), c), t, 1n+pos)
      +AT = V.ts.naive.at(False{}, Con{b2, r2}, t)
      +H0 = V.ts.naive.hit(Bool.and(bd.hd(s), Bool.and(U32.is_eq(b, c), AT)), Nat.add(pos, 2n+List.length(&2, U32, r2)), Nil{})
      +RHS = V.ts.naive.hit(LZ, 1n+pos, List.append(&2, Nat, X, V.ts.naive.hit(Bool.and(Bool.and(bd.hd(s), U32.is_eq(b, c)), AT), Nat.add(1n+pos, 1n+List.length(&2, U32, r2)), Nil{})))
      %Equal.sym(List<&2, Nat>, kp.pend(Con{b2, r2}, bd.tl(s), Con{c, t}, pos), V.ts.naive.hit(LZ, 1n+pos, X), kp.pshift(r2, b2, bd.tl(s), c, t, pos)) : {List.append(&2, Nat, _, H0) == RHS : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, V.ts.naive.hit(LZ, 1n+pos, X), H0), V.ts.naive.hit(LZ, 1n+pos, List.append(&2, Nat, X, H0)), L.tsl.hit_app(LZ, 1n+pos, X, H0)) : {_ == RHS : List<&2, Nat>}
      %L.tsl.and_assoc(bd.hd(s), U32.is_eq(b, c), AT) : {V.ts.naive.hit(LZ, 1n+pos, List.append(&2, Nat, X, V.ts.naive.hit(_, Nat.add(pos, 2n+List.length(&2, U32, r2)), Nil{}))) == RHS : List<&2, Nat>}
      %Equal.sym(Nat, Nat.add(pos, 2n+List.length(&2, U32, r2)), 1n+Nat.add(pos, 1n+List.length(&2, U32, r2)), L.tsl.add_succ(pos, 1n+List.length(&2, U32, r2))) : {V.ts.naive.hit(LZ, 1n+pos, List.append(&2, Nat, X, V.ts.naive.hit(Bool.and(Bool.and(bd.hd(s), U32.is_eq(b, c)), AT), _, Nil{}))) == RHS : List<&2, Nat>}
      {==}

# one byte: the automaton's report, then the rest from the set after it
def kp.gstep(+a0: U32, p1: List<&2, U32>, +s: List<&2, Bool>, +c: U32, +t: List<&2, U32>, +pos: Nat, +hs: {bd.hd(s) == True{} : Bool}) -> {kp.G(a0, p1, s, Con{c, t}, pos) == A.ts.auto.hit(bd.get(bd.ext(Con{a0, p1}, s, c), 1n+List.length(&2, U32, p1)), 1n+pos, kp.G(a0, p1, bd.ext(Con{a0, p1}, s, c), t, 1n+pos)) : List<&2, Nat>}:
  match p1:
    case Nil{}:
      +N = V.ts.naive.go(False{}, Con{a0, Nil{}}, 1n, t, 1n+pos)
      %Equal.sym(Bool, bd.hd(s), True{}, hs) : {V.ts.naive.hit(Bool.and(U32.is_eq(a0, c), True{}), Nat.add(pos, 1n), N) == A.ts.auto.hit(Bool.and(_, U32.is_eq(a0, c)), 1n+pos, N) : List<&2, Nat>}
      %Equal.sym(Bool, Bool.and(U32.is_eq(a0, c), True{}), U32.is_eq(a0, c), L.tsl.and_true_r(U32.is_eq(a0, c))) : {V.ts.naive.hit(_, Nat.add(pos, 1n), N) == A.ts.auto.hit(U32.is_eq(a0, c), 1n+pos, N) : List<&2, Nat>}
      %Equal.sym(Nat, Nat.add(pos, 1n), 1n+pos, L.tsl.add_one(pos)) : {V.ts.naive.hit(U32.is_eq(a0, c), _, N) == A.ts.auto.hit(U32.is_eq(a0, c), 1n+pos, N) : List<&2, Nat>}
      kp.hits(U32.is_eq(a0, c), 1n+pos, N)
    case Con{+b1, +p2}:
      +AT = V.ts.naive.at(False{}, Con{b1, p2}, t)
      +LZ = kp.lastz(Con{b1, p2}, bd.tl(s), c)
      +Z = bd.zm(Con{b1, p2}, bd.tl(s), c)
      +Y = kp.pend(p2, Z, t, 1n+pos)
      +N = V.ts.naive.go(False{}, Con{a0, Con{b1, p2}}, 1n+List.length(&2, U32, Con{b1, p2}), t, 1n+pos)
      +E0 = Nat.add(pos, 1n+List.length(&2, U32, Con{b1, p2}))
      +E1 = Nat.add(1n+pos, List.length(&2, U32, Con{b1, p2}))
      +H1 = V.ts.naive.hit(Bool.and(U32.is_eq(a0, c), AT), E1, Nil{})
      +RHS0 = A.ts.auto.hit(bd.get(bd.ext(Con{a0, Con{b1, p2}}, s, c), 1n+List.length(&2, U32, Con{b1, p2})), 1n+pos, kp.G(a0, Con{b1, p2}, bd.ext(Con{a0, Con{b1, p2}}, s, c), t, 1n+pos))
      %Equal.sym(List<&2, Nat>, kp.pend(Con{b1, p2}, bd.tl(s), Con{c, t}, pos), V.ts.naive.hit(LZ, 1n+pos, Y), kp.pshift(p2, b1, bd.tl(s), c, t, pos)) : {List.append(&2, Nat, _, V.ts.naive.hit(Bool.and(U32.is_eq(a0, c), AT), E0, N)) == RHS0 : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, V.ts.naive.hit(LZ, 1n+pos, Y), V.ts.naive.hit(Bool.and(U32.is_eq(a0, c), AT), E0, N)), V.ts.naive.hit(LZ, 1n+pos, List.append(&2, Nat, Y, V.ts.naive.hit(Bool.and(U32.is_eq(a0, c), AT), E0, N))), L.tsl.hit_app(LZ, 1n+pos, Y, V.ts.naive.hit(Bool.and(U32.is_eq(a0, c), AT), E0, N))) : {_ == RHS0 : List<&2, Nat>}
      %Equal.sym(Bool, bd.hd(s), True{}, hs) : {V.ts.naive.hit(LZ, 1n+pos, List.append(&2, Nat, Y, V.ts.naive.hit(Bool.and(U32.is_eq(a0, c), AT), E0, N))) == A.ts.auto.hit(LZ, 1n+pos, List.append(&2, Nat, List.append(&2, Nat, Y, V.ts.naive.hit(Bool.and(Bool.and(_, U32.is_eq(a0, c)), AT), E1, Nil{})), N)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.append(&2, Nat, Y, H1), N), List.append(&2, Nat, Y, List.append(&2, Nat, H1, N)), L.tsl.app_assoc(Y, H1, N)) : {V.ts.naive.hit(LZ, 1n+pos, List.append(&2, Nat, Y, V.ts.naive.hit(Bool.and(U32.is_eq(a0, c), AT), E0, N))) == A.ts.auto.hit(LZ, 1n+pos, _) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, H1, N), V.ts.naive.hit(Bool.and(U32.is_eq(a0, c), AT), E1, List.append(&2, Nat, Nil{}, N)), L.tsl.hit_app(Bool.and(U32.is_eq(a0, c), AT), E1, Nil{}, N)) : {V.ts.naive.hit(LZ, 1n+pos, List.append(&2, Nat, Y, V.ts.naive.hit(Bool.and(U32.is_eq(a0, c), AT), E0, N))) == A.ts.auto.hit(LZ, 1n+pos, List.append(&2, Nat, Y, _)) : List<&2, Nat>}
      %Equal.sym(Nat, E0, 1n+Nat.add(pos, List.length(&2, U32, Con{b1, p2})), L.tsl.add_succ(pos, List.length(&2, U32, Con{b1, p2}))) : {V.ts.naive.hit(LZ, 1n+pos, List.append(&2, Nat, Y, V.ts.naive.hit(Bool.and(U32.is_eq(a0, c), AT), _, N))) == A.ts.auto.hit(LZ, 1n+pos, List.append(&2, Nat, Y, V.ts.naive.hit(Bool.and(U32.is_eq(a0, c), AT), E1, N))) : List<&2, Nat>}
      kp.hits(LZ, 1n+pos, List.append(&2, Nat, Y, V.ts.naive.hit(Bool.and(U32.is_eq(a0, c), AT), E1, N)))

# the automaton does not look at the entry for the whole pattern
def kp.pend_set(q: List<&2, U32>, +s: List<&2, Bool>, +ys: List<&2, U32>, +pos: Nat) -> {kp.pend(q, bd.set(List.length(&2, U32, q), s), ys, pos) == kp.pend(q, s, ys, pos) : List<&2, Nat>}:
  match q:
    case Nil{}:
      {==}
    case Con{+b, +r}:
      %Equal.sym(List<&2, Nat>, kp.pend(r, bd.set(List.length(&2, U32, r), bd.tl(s)), ys, pos), kp.pend(r, bd.tl(s), ys, pos), kp.pend_set(r, bd.tl(s), ys, pos)) : {List.append(&2, Nat, _, V.ts.naive.hit(Bool.and(bd.hd(s), V.ts.naive.at(False{}, Con{b, r}, ys)), Nat.add(pos, List.length(&2, U32, Con{b, r})), Nil{})) == kp.pend(Con{b, r}, s, ys, pos) : List<&2, Nat>}
      {==}

def kp.G_set(+a0: U32, +p1: List<&2, U32>, +s: List<&2, Bool>, +ys: List<&2, U32>, +pos: Nat) -> {kp.G(a0, p1, bd.set(1n+List.length(&2, U32, p1), s), ys, pos) == kp.G(a0, p1, s, ys, pos) : List<&2, Nat>}:
  %Equal.sym(List<&2, Nat>, kp.pend(p1, bd.set(List.length(&2, U32, p1), bd.tl(s)), ys, pos), kp.pend(p1, bd.tl(s), ys, pos), kp.pend_set(p1, bd.tl(s), ys, pos)) : {List.append(&2, Nat, _, V.ts.naive.go(False{}, Con{a0, p1}, 1n+List.length(&2, U32, p1), ys, pos)) == kp.G(a0, p1, s, ys, pos) : List<&2, Nat>}
  {==}

# at the end of the text no prefix completes
def kp.pend_nil(q: List<&2, U32>, +s: List<&2, Bool>, +pos: Nat) -> {kp.pend(q, s, Nil{}, pos) == Nil{} : List<&2, Nat>}:
  match q:
    case Nil{}:
      {==}
    case Con{+b, +r}:
      %Equal.sym(List<&2, Nat>, kp.pend(r, bd.tl(s), Nil{}, pos), Nil{}, kp.pend_nil(r, bd.tl(s), pos)) : {List.append(&2, Nat, _, V.ts.naive.hit(Bool.and(bd.hd(s), False{}), Nat.add(pos, List.length(&2, U32, Con{b, r})), Nil{})) == Nil{} : List<&2, Nat>}
      %Equal.sym(Bool, Bool.and(bd.hd(s), False{}), False{}, L.tsl.and_false_r(bd.hd(s))) : {V.ts.naive.hit(_, Nat.add(pos, List.length(&2, U32, Con{b, r})), Nil{}) == Nil{} : List<&2, Nat>}
      {==}

# no prefix in the set: none to complete
def kp.pend_falses(q: List<&2, U32>, +ys: List<&2, U32>, +pos: Nat) -> {kp.pend(q, Con{False{}, bd.falses(q)}, ys, pos) == Nil{} : List<&2, Nat>}:
  match q:
    case Nil{}:
      {==}
    case Con{+b, +r}:
      %Equal.sym(List<&2, Nat>, kp.pend(r, Con{False{}, bd.falses(r)}, ys, pos), Nil{}, kp.pend_falses(r, ys, pos)) : {List.append(&2, Nat, _, Nil{}) == Nil{} : List<&2, Nat>}
      {==}

# KMP's state q stands for the borders of q bytes

def kp.run_k(b: Bool, +icase: Bool, +a0: U32, +p1: List<&2, U32>, +fail: List<&2, Nat>, +q2: Nat, +t: List<&2, U32>, +pos: Nat, +h_ok: {bd.ok(Con{a0, p1}, fail, 1n+List.length(&2, U32, p1)) == True{} : Bool}, +h_q2: {Nat.is_lt(q2, 2n+List.length(&2, U32, p1)) == True{} : Bool}, +e: {Nat.is_eq(q2, 1n+List.length(&2, U32, p1)) == b : Bool}, ih: @q:Nat -> {Nat.is_lt(q, 1n+List.length(&2, U32, p1)) == True{} : Bool} -> {A.ts.auto.snd(~K.TsKmp, A.ts.auto.feed(~K.TsKmp, ~K.ts.kmp.step, K.TsKmp{icase, Con{a0, p1}, fail, 1n+List.length(&2, U32, p1), q}, 1n+pos, t)) == kp.G(a0, p1, bd.B(Con{a0, p1}, q), T.ts.fold_all(icase, t), 1n+pos) : List<&2, Nat>}) -> {A.ts.auto.snd(~K.TsKmp, A.ts.auto.go(~K.TsKmp, ~K.ts.kmp.step, t, 1n+pos, K.ts.kmp.done(icase, Con{a0, p1}, fail, 1n+List.length(&2, U32, p1), q2, b))) == A.ts.auto.hit(b, 1n+pos, kp.G(a0, p1, bd.B(Con{a0, p1}, q2), T.ts.fold_all(icase, t), 1n+pos)) : List<&2, Nat>}:
  match b:
    case True{}:
      +P : List<&2, U32> = Con{a0, p1}
      +M : Nat = 1n+List.length(&2, U32, p1)
      +F = K.ts.kmp.nat_at(fail, List.length(&2, U32, p1))
      +F1 = K.ts.kmp.nat_at(fail, Nat.sub(List.length(&2, U32, p1), 0n))
      +ft = T.ts.fold_all(icase, t)
      +eF = Equal.cong(Nat, Nat, n => K.ts.kmp.nat_at(fail, n), Nat.sub(List.length(&2, U32, p1), 0n), List.length(&2, U32, p1), L.tsl.sub_zero(List.length(&2, U32, p1)))
      +hF1 = Equal.trans(Bool, Nat.is_lt(F1, M), Nat.is_lt(F, M), True{}, Equal.cong(Nat, Bool, n => Nat.is_lt(n, M), F1, F, eF), bd.ok_lt(P, fail, List.length(&2, U32, p1), h_ok))
      %Equal.sym(Nat, q2, M, L.tsl.nat_eq(q2, M, e)) : {A.ts.auto.snd(~K.TsKmp, A.ts.auto.go(~K.TsKmp, ~K.ts.kmp.step, t, 1n+pos, (K.TsKmp{icase, P, fail, M, F1}, True{}))) == A.ts.auto.hit(True{}, 1n+pos, kp.G(a0, p1, bd.B(P, _), ft, 1n+pos)) : List<&2, Nat>}
      %Equal.sym(List<&2, Bool>, bd.B(P, M), bd.set(M, bd.B(P, F)), bd.ok_eq(P, fail, List.length(&2, U32, p1), h_ok)) : {A.ts.auto.snd(~K.TsKmp, A.ts.auto.go(~K.TsKmp, ~K.ts.kmp.step, t, 1n+pos, (K.TsKmp{icase, P, fail, M, F1}, True{}))) == A.ts.auto.hit(True{}, 1n+pos, kp.G(a0, p1, _, ft, 1n+pos)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, kp.G(a0, p1, bd.set(M, bd.B(P, F)), ft, 1n+pos), kp.G(a0, p1, bd.B(P, F), ft, 1n+pos), kp.G_set(a0, p1, bd.B(P, F), ft, 1n+pos)) : {A.ts.auto.snd(~K.TsKmp, A.ts.auto.go(~K.TsKmp, ~K.ts.kmp.step, t, 1n+pos, (K.TsKmp{icase, P, fail, M, F1}, True{}))) == A.ts.auto.hit(True{}, 1n+pos, _) : List<&2, Nat>}
      %eF : {A.ts.auto.snd(~K.TsKmp, A.ts.auto.go(~K.TsKmp, ~K.ts.kmp.step, t, 1n+pos, (K.TsKmp{icase, P, fail, M, F1}, True{}))) == A.ts.auto.hit(True{}, 1n+pos, kp.G(a0, p1, bd.B(P, _), ft, 1n+pos)) : List<&2, Nat>}
      Equal.trans(List<&2, Nat>, A.ts.auto.snd(~K.TsKmp, A.ts.auto.go(~K.TsKmp, ~K.ts.kmp.step, t, 1n+pos, (K.TsKmp{icase, P, fail, M, F1}, True{}))), A.ts.auto.hit(True{}, 1n+pos, A.ts.auto.snd(~K.TsKmp, A.ts.auto.feed(~K.TsKmp, ~K.ts.kmp.step, K.TsKmp{icase, P, fail, M, F1}, 1n+pos, t))), A.ts.auto.hit(True{}, 1n+pos, kp.G(a0, p1, bd.B(P, F1), ft, 1n+pos)), L.tsl.go_snd(~K.TsKmp, ~K.ts.kmp.step, t, 1n+pos, K.TsKmp{icase, P, fail, M, F1}, True{}), Equal.cong(List<&2, Nat>, List<&2, Nat>, x => A.ts.auto.hit(True{}, 1n+pos, x), A.ts.auto.snd(~K.TsKmp, A.ts.auto.feed(~K.TsKmp, ~K.ts.kmp.step, K.TsKmp{icase, P, fail, M, F1}, 1n+pos, t)), kp.G(a0, p1, bd.B(P, F1), ft, 1n+pos), ih(F1, hF1)))
    case False{}:
      +P : List<&2, U32> = Con{a0, p1}
      +M : Nat = 1n+List.length(&2, U32, p1)
      Equal.trans(List<&2, Nat>, A.ts.auto.snd(~K.TsKmp, A.ts.auto.go(~K.TsKmp, ~K.ts.kmp.step, t, 1n+pos, (K.TsKmp{icase, P, fail, M, q2}, False{}))), A.ts.auto.hit(False{}, 1n+pos, A.ts.auto.snd(~K.TsKmp, A.ts.auto.feed(~K.TsKmp, ~K.ts.kmp.step, K.TsKmp{icase, P, fail, M, q2}, 1n+pos, t))), kp.G(a0, p1, bd.B(P, q2), T.ts.fold_all(icase, t), 1n+pos), L.tsl.go_snd(~K.TsKmp, ~K.ts.kmp.step, t, 1n+pos, K.TsKmp{icase, P, fail, M, q2}, False{}), ih(q2, L.tsl.lt_succ_ne(q2, M, h_q2, e)))

# from state q (below the pattern's length) KMP reports what the
# shift-and automaton reports from the borders of q bytes
def kp.run(ys: List<&2, U32>, +icase: Bool, +a0: U32, +p1: List<&2, U32>, +fail: List<&2, Nat>, +q: Nat, +pos: Nat, +h_ok: {bd.ok(Con{a0, p1}, fail, 1n+List.length(&2, U32, p1)) == True{} : Bool}, +h_q: {Nat.is_lt(q, 1n+List.length(&2, U32, p1)) == True{} : Bool}) -> {A.ts.auto.snd(~K.TsKmp, A.ts.auto.feed(~K.TsKmp, ~K.ts.kmp.step, K.TsKmp{icase, Con{a0, p1}, fail, 1n+List.length(&2, U32, p1), q}, pos, ys)) == kp.G(a0, p1, bd.B(Con{a0, p1}, q), T.ts.fold_all(icase, ys), pos) : List<&2, Nat>}:
  match ys:
    case Nil{}:
      %Equal.sym(List<&2, Nat>, kp.pend(p1, bd.tl(bd.B(Con{a0, p1}, q)), Nil{}, pos), Nil{}, kp.pend_nil(p1, bd.tl(bd.B(Con{a0, p1}, q)), pos)) : {Nil{} == List.append(&2, Nat, _, Nil{}) : List<&2, Nat>}
      {==}
    case Con{+c, +t}:
      +P : List<&2, U32> = Con{a0, p1}
      +M : Nat = 1n+List.length(&2, U32, p1)
      +fc = T.ts.fold(icase, c)
      +ft = T.ts.fold_all(icase, t)
      +Q2 = K.ts.kmp.next(P, fail, fc, q)
      +h_okq = bd.ok_mono(M, q, P, fail, h_ok, L.tsl.lt_weak(q, M, h_q))
      +h_q2 = L.tsl.lt_le_trans(Q2, 2n+q, 1n+M, bd.next_le(q, P, fail, fc, h_okq), h_q)
      +e_n = bd.next_ok(q, P, fail, fc, h_okq)
      +e_top = bd.B_get(Q2, M, P, h_q2, L.tsl.lt_succ(M))
      +eqR = Equal.trans(List<&2, Nat>, kp.G(a0, p1, bd.B(P, q), Con{fc, ft}, pos), A.ts.auto.hit(bd.get(bd.ext(P, bd.B(P, q), fc), M), 1n+pos, kp.G(a0, p1, bd.ext(P, bd.B(P, q), fc), ft, 1n+pos)), A.ts.auto.hit(Nat.is_eq(Q2, M), 1n+pos, kp.G(a0, p1, bd.B(P, Q2), ft, 1n+pos)), kp.gstep(a0, p1, bd.B(P, q), fc, ft, pos, bd.B_hd(P, q)), Equal.trans(List<&2, Nat>, A.ts.auto.hit(bd.get(bd.ext(P, bd.B(P, q), fc), M), 1n+pos, kp.G(a0, p1, bd.ext(P, bd.B(P, q), fc), ft, 1n+pos)), A.ts.auto.hit(bd.get(bd.B(P, Q2), M), 1n+pos, kp.G(a0, p1, bd.B(P, Q2), ft, 1n+pos)), A.ts.auto.hit(Nat.is_eq(Q2, M), 1n+pos, kp.G(a0, p1, bd.B(P, Q2), ft, 1n+pos)), Equal.cong(List<&2, Bool>, List<&2, Nat>, x => A.ts.auto.hit(bd.get(x, M), 1n+pos, kp.G(a0, p1, x, ft, 1n+pos)), bd.ext(P, bd.B(P, q), fc), bd.B(P, Q2), e_n), Equal.cong(Bool, List<&2, Nat>, x => A.ts.auto.hit(x, 1n+pos, kp.G(a0, p1, bd.B(P, Q2), ft, 1n+pos)), bd.get(bd.B(P, Q2), M), Nat.is_eq(Q2, M), e_top)))
      Equal.trans(List<&2, Nat>, A.ts.auto.snd(~K.TsKmp, A.ts.auto.go(~K.TsKmp, ~K.ts.kmp.step, t, 1n+pos, K.ts.kmp.done(icase, P, fail, M, Q2, Nat.is_eq(Q2, M)))), A.ts.auto.hit(Nat.is_eq(Q2, M), 1n+pos, kp.G(a0, p1, bd.B(P, Q2), ft, 1n+pos)), kp.G(a0, p1, bd.B(P, q), Con{fc, ft}, pos), kp.run_k(Nat.is_eq(Q2, M), icase, a0, p1, fail, Q2, t, pos, h_ok, h_q2, {==}, q3 => hq => kp.run(t, icase, a0, p1, fail, q3, 1n+pos, h_ok, hq)), Equal.sym(List<&2, Nat>, kp.G(a0, p1, bd.B(P, q), Con{fc, ft}, pos), A.ts.auto.hit(Nat.is_eq(Q2, M), 1n+pos, kp.G(a0, p1, bd.B(P, Q2), ft, 1n+pos)), eqR))

# an empty pattern: no match
def kp.m0(ys: List<&2, U32>, +icase: Bool, +fail: List<&2, Nat>, +q: Nat, +pos: Nat) -> {A.ts.auto.snd(~K.TsKmp, A.ts.auto.feed(~K.TsKmp, ~K.ts.kmp.step, K.TsKmp{icase, Nil{}, fail, 0n, q}, pos, ys)) == Nil{} : List<&2, Nat>}:
  match ys:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      Equal.trans(List<&2, Nat>, A.ts.auto.snd(~K.TsKmp, A.ts.auto.go(~K.TsKmp, ~K.ts.kmp.step, t, 1n+pos, (K.TsKmp{icase, Nil{}, fail, 0n, q}, False{}))), A.ts.auto.hit(False{}, 1n+pos, A.ts.auto.snd(~K.TsKmp, A.ts.auto.feed(~K.TsKmp, ~K.ts.kmp.step, K.TsKmp{icase, Nil{}, fail, 0n, q}, 1n+pos, t))), Nil{}, L.tsl.go_snd(~K.TsKmp, ~K.ts.kmp.step, t, 1n+pos, K.TsKmp{icase, Nil{}, fail, 0n, q}, False{}), kp.m0(t, icase, fail, q, 1n+pos))

# The laws

def kp.ref(+icase: Bool, p: List<&2, U32>, +xs: List<&2, U32>) -> {K.ts.kmp.ends(icase, p, xs) == V.ts.naive.ends(icase, p, xs) : List<&2, Nat>}:
  match p:
    case Nil{}:
      kp.m0(xs, icase, Nil{}, 0n, 0n)
    case Con{+a, +t}:
      +fa = T.ts.fold(icase, a)
      +ft = T.ts.fold_all(icase, t)
      +fp : List<&2, U32> = Con{fa, ft}
      +fxs = T.ts.fold_all(icase, xs)
      +e_run = kp.run(xs, icase, fa, ft, K.ts.kmp.pi(fp), 0n, 0n, bd.pi_ok(fa, ft), {==})
      %Equal.sym(List<&2, Nat>, V.ts.naive.go(icase, Con{a, t}, 1n+List.length(&2, U32, t), xs, 0n), V.ts.naive.go(False{}, fp, 1n+List.length(&2, U32, t), fxs, 0n), L.tsl.go_fold(icase, Con{a, t}, 1n+List.length(&2, U32, t), xs, 0n)) : {K.ts.kmp.ends(icase, Con{a, t}, xs) == _ : List<&2, Nat>}
      %L.tsl.fold_len(icase, t) : {K.ts.kmp.ends(icase, Con{a, t}, xs) == V.ts.naive.go(False{}, fp, 1n+_, fxs, 0n) : List<&2, Nat>}
      %kp.pend_falses(ft, fxs, 0n) : {K.ts.kmp.ends(icase, Con{a, t}, xs) == List.append(&2, Nat, _, V.ts.naive.go(False{}, fp, 1n+List.length(&2, U32, ft), fxs, 0n)) : List<&2, Nat>}
      e_run

def Laws.kmp_ref(icase, p, xs):
  kp.ref(icase, p, xs)

def kp.search(+icase: Bool, +p: List<&2, U32>, +cs: List<&2, List<&2, U32>>) -> {K.ts.kmp.search(icase, p, cs) == V.ts.naive.ends(icase, p, T.ts.concat(cs)) : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, K.ts.kmp.search(icase, p, cs), K.ts.kmp.ends(icase, p, T.ts.concat(cs)), V.ts.naive.ends(icase, p, T.ts.concat(cs)), L.tsl.split(~K.TsKmp, ~K.ts.kmp.step, cs, 0n, K.ts.kmp.start(icase, p), Nil{}), kp.ref(icase, p, T.ts.concat(cs)))

def Laws.kmp_search_ref(icase, p, cs):
  kp.search(icase, p, cs)
