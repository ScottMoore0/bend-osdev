import Base
import ./idalloc.bend as I
import ./LAWS.bend as Laws

# Contradictions

def absurd.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def absurd.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : absurd.bool(_)
  Unit{}

def absurd.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : absurd.bool(_)
  Unit{}

# a Result of an allocation: Fail is not Done, and IdExhausted is not
# IdBadRange
def res.disc(-V: Data, r: Result<&2, &2, I.IdError, I.IdrAlloc<V>>) -> Type:
  match r:
    case Fail{x}:
      Empty
    case Done{y}:
      Unit

def absurd.fd(-V: Data, -x: I.IdError, -y: I.IdrAlloc<V>, e: {Fail{x} == Done{y} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> Empty:
  %Equal.sym(Result<&2, &2, I.IdError, I.IdrAlloc<V>>, Fail{x}, Done{y}, e) : res.disc(V, _)
  Unit{}

def absurd.df(-V: Data, -x: I.IdError, -y: I.IdrAlloc<V>, e: {Done{y} == Fail{x} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> Empty:
  %e : res.disc(V, _)
  Unit{}

def res.exhausted(-V: Data, r: Result<&2, &2, I.IdError, I.IdrAlloc<V>>) -> Type:
  match r:
    case Fail{I.IdExhausted{}}:
      Unit
    case Fail{x}:
      Empty
    case Done{y}:
      Empty

def absurd.eb(-V: Data, e: {Fail{I.IdExhausted{}} == Fail{I.IdBadRange{}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> Empty:
  %e : res.exhausted(V, _)
  Unit{}

def absurd.be(-V: Data, e: {Fail{I.IdBadRange{}} == Fail{I.IdExhausted{}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> Empty:
  %Equal.sym(Result<&2, &2, I.IdError, I.IdrAlloc<V>>, Fail{I.IdBadRange{}}, Fail{I.IdExhausted{}}, e) : res.exhausted(V, _)
  Unit{}

def old.disc(-V: Data, r: Result<&2, &2, I.IdError, I.IdrOld<V>>) -> Type:
  match r:
    case Fail{x}:
      Empty
    case Done{y}:
      Unit

def absurd.ofd(-V: Data, -x: I.IdError, -y: I.IdrOld<V>, e: {Fail{x} == Done{y} : Result<&2, &2, I.IdError, I.IdrOld<V>>}) -> Empty:
  %Equal.sym(Result<&2, &2, I.IdError, I.IdrOld<V>>, Fail{x}, Done{y}, e) : old.disc(V, _)
  Unit{}

def maybe.disc(-V: Data, m: Maybe<&2, V>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

def absurd.ns(-V: Data, -x: V, e: {None{} == Some{x} : Maybe<&2, V>}) -> Empty:
  %Equal.sym(Maybe<&2, V>, None{}, Some{x}, e) : maybe.disc(V, _)
  Unit{}

# Fields of a Done

def res.id(-V: Data, r: Result<&2, &2, I.IdError, I.IdrAlloc<V>>) -> Nat:
  match r:
    case Fail{x}:
      0n
    case Done{I.IdrAlloc{t, i}}:
      i

def res.map(-V: Data, r: Result<&2, &2, I.IdError, I.IdrAlloc<V>>, d: I.Idr<V>) -> I.Idr<V>:
  match r:
    case Fail{x}:
      d
    case Done{I.IdrAlloc{t, i}}:
      t

def old.map(-V: Data, r: Result<&2, &2, I.IdError, I.IdrOld<V>>, d: I.Idr<V>) -> I.Idr<V>:
  match r:
    case Fail{x}:
      d
    case Done{I.IdrOld{t, o}}:
      t

def old.val(-V: Data, r: Result<&2, &2, I.IdError, I.IdrOld<V>>, d: V) -> V:
  match r:
    case Fail{x}:
      d
    case Done{I.IdrOld{t, o}}:
      o

# Nat

def nat.le_zero(x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nat.lt_zero(x: Nat) -> {Nat.is_lt(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def nat.le_refl(x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      nat.le_refl(p)

def nat.le_antisym(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}, f: {Nat.is_le(b, a) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      Empty.absurd({0n == 1n+bp : Nat}, absurd.ft(f))
    case 1n+ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, absurd.ft(e))
    case 1n+ +ap 1n+ +bp:
      %nat.le_antisym(ap, bp, e, f) : {1n+ap == 1n+_ : Nat}
      {==}

def nat.lt_absurd0(+x: Nat, -T: Type, e: {Nat.is_lt(x, 0n) == True{} : Bool}) -> T:
  Empty.absurd(T, absurd.ft(Equal.trans(Bool, False{}, Nat.is_lt(x, 0n), True{}, Equal.sym(Bool, Nat.is_lt(x, 0n), False{}, nat.lt_zero(x)), e)))

def nat.le_lt_absurd(m: Nat, j: Nat, e: {Nat.is_le(m, j) == True{} : Bool}, f: {Nat.is_lt(j, m) == True{} : Bool}) -> Empty:
  match m j:
    case 0n +j0:
      nat.lt_absurd0(j0, Empty, f)
    case 1n+mp 0n:
      absurd.ft(e)
    case 1n+mp 1n+jp:
      nat.le_lt_absurd(mp, jp, e, f)

def nat.lt_le(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n _:
      nat.le_zero(b)
    case 1n+ap 0n:
      Empty.absurd({False{} == True{} : Bool}, absurd.ft(e))
    case 1n+ap 1n+bp:
      nat.lt_le(ap, bp, e)

def nat.le_trans(a: Nat, b: Nat, c: Nat, e: {Nat.is_le(a, b) == True{} : Bool}, f: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      nat.le_zero(c)
    case 1n+ap 0n _:
      Empty.absurd({Nat.is_le(1n+ap, c) == True{} : Bool}, absurd.ft(e))
    case 1n+ap 1n+bp 0n:
      Empty.absurd({Nat.is_le(1n+ap, 0n) == True{} : Bool}, absurd.ft(f))
    case 1n+ap 1n+bp 1n+cp:
      nat.le_trans(ap, bp, cp, e, f)

# not i <= max, j <= max: j < i
def nat.nle_le_lt(i: Nat, max: Nat, j: Nat, e: {Nat.is_le(i, max) == False{} : Bool}, f: {Nat.is_le(j, max) == True{} : Bool}) -> {Nat.is_lt(j, i) == True{} : Bool}:
  match i max j:
    case 0n +mx _:
      Empty.absurd({Nat.is_lt(j, 0n) == True{} : Bool}, absurd.tf(Equal.trans(Bool, True{}, Nat.is_le(0n, mx), False{}, Equal.sym(Bool, Nat.is_le(0n, mx), True{}, nat.le_zero(mx)), e)))
    case 1n+ip _ 0n:
      {==}
    case 1n+ip 0n 1n+jp:
      Empty.absurd({Nat.is_lt(1n+jp, 1n+ip) == True{} : Bool}, absurd.ft(f))
    case 1n+ip 1n+mp 1n+jp:
      nat.nle_le_lt(ip, mp, jp, e, f)

# not a <= b: b < a
def nat.nle_lt(a: Nat, b: Nat, e: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n +bb:
      Empty.absurd({Nat.is_lt(bb, 0n) == True{} : Bool}, absurd.tf(Equal.trans(Bool, True{}, Nat.is_le(0n, bb), False{}, Equal.sym(Bool, Nat.is_le(0n, bb), True{}, nat.le_zero(bb)), e)))
    case 1n+ap 0n:
      {==}
    case 1n+ap 1n+bp:
      nat.nle_lt(ap, bp, e)

# moving a comparison across an equality
def tr.lt(-j: Nat, -a: Nat, -b: Nat, eq: {a == b : Nat}, h: {Nat.is_lt(j, b) == True{} : Bool}) -> {Nat.is_lt(j, a) == True{} : Bool}:
  %Equal.sym(Nat, a, b, eq) : {Nat.is_lt(j, _) == True{} : Bool}
  h

def tr.ne(-j: Nat, -a: Nat, -b: Nat, eq: {a == b : Nat}, h: {Nat.is_eq(j, b) == False{} : Bool}) -> {Nat.is_eq(j, a) == False{} : Bool}:
  %Equal.sym(Nat, a, b, eq) : {Nat.is_eq(j, _) == False{} : Bool}
  h

# Slots

def sl.get_put(-V: Data, xs: List<&2, Maybe<&2, V>>, i: Nat, +m: Maybe<&2, V>) -> {I.idr.slots.get(V, I.idr.slots.put(V, xs, i, m), i) == m : Maybe<&2, V>}:
  match xs i:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      sl.get_put(V, Nil{}, j, m)
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+j:
      sl.get_put(V, t, j, m)

def sl.get_put_other(-V: Data, xs: List<&2, Maybe<&2, V>>, i: Nat, +m: Maybe<&2, V>, j: Nat, n: {Nat.is_eq(j, i) == False{} : Bool}) -> {I.idr.slots.get(V, I.idr.slots.put(V, xs, i, m), j) == I.idr.slots.get(V, xs, j) : Maybe<&2, V>}:
  match xs i j:
    case Nil{} 0n 0n:
      Empty.absurd({m == None{} : Maybe<&2, V>}, absurd.tf(n))
    case Nil{} 0n 1n+jp:
      {==}
    case Nil{} 1n+ip 0n:
      {==}
    case Nil{} 1n+ip 1n+jp:
      sl.get_put_other(V, Nil{}, ip, m, jp, n)
    case Con{h, t} 0n 0n:
      Empty.absurd({m == h : Maybe<&2, V>}, absurd.tf(n))
    case Con{h, t} 0n 1n+jp:
      {==}
    case Con{h, t} 1n+ip 0n:
      {==}
    case Con{h, t} 1n+ip 1n+jp:
      sl.get_put_other(V, t, ip, m, jp, n)

def sl.get_clear(-V: Data, xs: List<&2, Maybe<&2, V>>, i: Nat) -> {I.idr.slots.get(V, I.idr.slots.clear(V, xs, i), i) == None{} : Maybe<&2, V>}:
  match xs i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+j:
      sl.get_clear(V, t, j)

def sl.get_clear_other(-V: Data, xs: List<&2, Maybe<&2, V>>, i: Nat, j: Nat, n: {Nat.is_eq(j, i) == False{} : Bool}) -> {I.idr.slots.get(V, I.idr.slots.clear(V, xs, i), j) == I.idr.slots.get(V, xs, j) : Maybe<&2, V>}:
  match xs i j:
    case Nil{} _ _:
      {==}
    case Con{h, t} 0n 0n:
      Empty.absurd({None{} == h : Maybe<&2, V>}, absurd.tf(n))
    case Con{h, t} 0n 1n+jp:
      {==}
    case Con{h, t} 1n+ip 0n:
      {==}
    case Con{h, t} 1n+ip 1n+jp:
      sl.get_clear_other(V, t, ip, jp, n)

def sl.ff_free(-V: Data, xs: List<&2, Maybe<&2, V>>, min: Nat) -> {I.idr.slots.get(V, xs, I.idr.slots.free_from(V, xs, min)) == None{} : Maybe<&2, V>}:
  match xs min:
    case Nil{} m:
      {==}
    case Con{h, t} 1n+m:
      sl.ff_free(V, t, m)
    case Con{None{}, t} 0n:
      {==}
    case Con{Some{x}, t} 0n:
      sl.ff_free(V, t, 0n)

def sl.ff_ge(-V: Data, xs: List<&2, Maybe<&2, V>>, min: Nat) -> {Nat.is_le(min, I.idr.slots.free_from(V, xs, min)) == True{} : Bool}:
  match xs min:
    case Nil{} m:
      nat.le_refl(m)
    case Con{h, t} 1n+m:
      sl.ff_ge(V, t, m)
    case Con{None{}, t} 0n:
      {==}
    case Con{Some{x}, t} 0n:
      {==}

def sl.ff_lowest(-V: Data, xs: List<&2, Maybe<&2, V>>, min: Nat, j: Nat, l: {Nat.is_le(min, j) == True{} : Bool}, m: {Nat.is_lt(j, I.idr.slots.free_from(V, xs, min)) == True{} : Bool}) -> {Maybe.is_some(&2, V, I.idr.slots.get(V, xs, j)) == True{} : Bool}:
  match xs min j:
    case Nil{} mn jj:
      Empty.absurd({False{} == True{} : Bool}, nat.le_lt_absurd(mn, jj, l, m))
    case Con{h, t} 1n+mn 0n:
      Empty.absurd({Maybe.is_some(&2, V, h) == True{} : Bool}, absurd.ft(l))
    case Con{h, t} 1n+mn 1n+jp:
      sl.ff_lowest(V, t, mn, jp, l, m)
    case Con{None{}, t} 0n +jj:
      nat.lt_absurd0(jj, {Maybe.is_some(&2, V, I.idr.slots.get(V, Con{None{}, t}, jj)) == True{} : Bool}, m)
    case Con{Some{x}, t} 0n 0n:
      {==}
    case Con{Some{x}, t} 0n 1n+ +jp:
      sl.ff_lowest(V, t, 0n, jp, nat.le_zero(jp), m)

def sl.ff_clear(-V: Data, xs: List<&2, Maybe<&2, V>>, min: Nat, k: Nat, l: {Nat.is_le(min, k) == True{} : Bool}, m: {Nat.is_le(k, I.idr.slots.free_from(V, xs, min)) == True{} : Bool}) -> {I.idr.slots.free_from(V, I.idr.slots.clear(V, xs, k), min) == k : Nat}:
  match xs min k:
    case Nil{} mn kk:
      nat.le_antisym(mn, kk, l, m)
    case Con{h, t} 1n+mn 0n:
      Empty.absurd({1n+I.idr.slots.free_from(V, t, mn) == 0n : Nat}, absurd.ft(l))
    case Con{h, +t} 1n+ +mn 1n+ +kp:
      %sl.ff_clear(V, t, mn, kp, l, m) : {1n+I.idr.slots.free_from(V, I.idr.slots.clear(V, t, kp), mn) == 1n+_ : Nat}
      {==}
    case Con{None{}, t} 0n 0n:
      {==}
    case Con{None{}, t} 0n 1n+kp:
      Empty.absurd({0n == 1n+kp : Nat}, absurd.ft(m))
    case Con{Some{x}, t} 0n 0n:
      {==}
    case Con{Some{x}, +t} 0n 1n+ +kp:
      %sl.ff_clear(V, t, 0n, kp, nat.le_zero(kp), m) : {1n+I.idr.slots.free_from(V, I.idr.slots.clear(V, t, kp), 0n) == 1n+_ : Nat}
      {==}

def sl.ff_realloc.nil(-V: Data, m: Nat, +v: V) -> {I.idr.slots.free_from(V, I.idr.slots.clear(V, I.idr.slots.put(V, Nil{}, m, Some{v}), m), m) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+ +p:
      %sl.ff_realloc.nil(V, p, v) : {1n+I.idr.slots.free_from(V, I.idr.slots.clear(V, I.idr.slots.put(V, Nil{}, p, Some{v}), p), p) == 1n+_ : Nat}
      {==}

# freeing the slot just allocated makes it the lowest free slot again
def sl.ff_realloc(-V: Data, xs: List<&2, Maybe<&2, V>>, min: Nat, +v: V) -> {I.idr.slots.free_from(V, I.idr.slots.clear(V, I.idr.slots.put(V, xs, I.idr.slots.free_from(V, xs, min), Some{v}), I.idr.slots.free_from(V, xs, min)), min) == I.idr.slots.free_from(V, xs, min) : Nat}:
  match xs min:
    case Nil{} m:
      sl.ff_realloc.nil(V, m, v)
    case Con{h, +t} 1n+ +m:
      %sl.ff_realloc(V, t, m, v) : {1n+I.idr.slots.free_from(V, I.idr.slots.clear(V, I.idr.slots.put(V, t, I.idr.slots.free_from(V, t, m), Some{v}), I.idr.slots.free_from(V, t, m)), m) == 1n+_ : Nat}
      {==}
    case Con{None{}, t} 0n:
      {==}
    case Con{Some{x}, +t} 0n:
      %sl.ff_realloc(V, t, 0n, v) : {1n+I.idr.slots.free_from(V, I.idr.slots.clear(V, I.idr.slots.put(V, t, I.idr.slots.free_from(V, t, 0n), Some{v}), I.idr.slots.free_from(V, t, 0n)), 0n) == 1n+_ : Nat}
      {==}

def sl.put_clear(-V: Data, ys: List<&2, Maybe<&2, V>>, i: Nat, +m: Maybe<&2, V>) -> {I.idr.slots.put(V, I.idr.slots.clear(V, ys, i), i, m) == I.idr.slots.put(V, ys, i, m) : List<&2, Maybe<&2, V>>}:
  match ys i:
    case Nil{} _:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{+h, +t} 1n+ +j:
      %sl.put_clear(V, t, j, m) : {Con{h, I.idr.slots.put(V, I.idr.slots.clear(V, t, j), j, m)} == Con{h, _} : List<&2, Maybe<&2, V>>}
      {==}

def sl.put_put(-V: Data, xs: List<&2, Maybe<&2, V>>, i: Nat, +a: Maybe<&2, V>, +b: Maybe<&2, V>) -> {I.idr.slots.put(V, I.idr.slots.put(V, xs, i, a), i, b) == I.idr.slots.put(V, xs, i, b) : List<&2, Maybe<&2, V>>}:
  match xs i:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+ +j:
      %sl.put_put(V, Nil{}, j, a, b) : {Con{None{}, I.idr.slots.put(V, I.idr.slots.put(V, Nil{}, j, a), j, b)} == Con{None{}, _} : List<&2, Maybe<&2, V>>}
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{+h, +t} 1n+ +j:
      %sl.put_put(V, t, j, a, b) : {Con{h, I.idr.slots.put(V, I.idr.slots.put(V, t, j, a), j, b)} == Con{h, _} : List<&2, Maybe<&2, V>>}
      {==}

def sl.put_same(-V: Data, xs: List<&2, Maybe<&2, V>>, k: Nat, +w: V, e: {I.idr.slots.get(V, xs, k) == Some{w} : Maybe<&2, V>}) -> {I.idr.slots.put(V, xs, k, Some{w}) == xs : List<&2, Maybe<&2, V>>}:
  match xs k:
    case Nil{} _:
      Empty.absurd({I.idr.slots.put(V, Nil{}, k, Some{w}) == Nil{} : List<&2, Maybe<&2, V>>}, absurd.ns(V, w, e))
    case Con{+h, +t} 0n:
      %Equal.sym(Maybe<&2, V>, h, Some{w}, e) : {Con{Some{w}, t} == Con{_, t} : List<&2, Maybe<&2, V>>}
      {==}
    case Con{+h, +t} 1n+ +j:
      %sl.put_same(V, t, j, w, e) : {Con{h, I.idr.slots.put(V, t, j, Some{w})} == Con{h, _} : List<&2, Maybe<&2, V>>}
      {==}

def unit.some(m: Maybe<&2, Unit>, e: {Maybe.is_some(&2, Unit, m) == True{} : Bool}) -> {m == Some{Unit{}} : Maybe<&2, Unit>}:
  match m:
    case None{}:
      Empty.absurd({None{} == Some{Unit{}} : Maybe<&2, Unit>}, absurd.ft(e))
    case Some{u}:
      match u:
        case Unit{}:
          {==}

# Inverting an allocation

def inv.ord(-V: Data, c: Bool, +xs: List<&2, Maybe<&2, V>>, +min: Nat, +max: Nat, +v: V, -t: I.Idr<V>, -id: Nat, e: {I.idr.alloc.order(V, c, xs, min, max, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {I.idr.alloc.at(V, Nat.is_le(I.idr.slots.free_from(V, xs, min), max), xs, I.idr.slots.free_from(V, xs, min), v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}:
  match c:
    case True{}:
      e
    case False{}:
      Empty.absurd({I.idr.alloc.at(V, Nat.is_le(I.idr.slots.free_from(V, xs, min), max), xs, I.idr.slots.free_from(V, xs, min), v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}, absurd.fd(V, I.IdBadRange{}, I.IdrAlloc{t, id}, e))

def inv.ord_c(-V: Data, c: Bool, -xs: List<&2, Maybe<&2, V>>, -min: Nat, -max: Nat, -v: V, -t: I.Idr<V>, -id: Nat, e: {I.idr.alloc.order(V, c, xs, min, max, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.fd(V, I.IdBadRange{}, I.IdrAlloc{t, id}, e))

def inv.fits(-V: Data, c: Bool, -xs: List<&2, Maybe<&2, V>>, -i: Nat, -v: V, -t: I.Idr<V>, -id: Nat, e: {I.idr.alloc.at(V, c, xs, i, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {c == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, absurd.fd(V, I.IdExhausted{}, I.IdrAlloc{t, id}, e))

def inv.id(-V: Data, c: Bool, +xs: List<&2, Maybe<&2, V>>, +i: Nat, +v: V, +t: I.Idr<V>, +id: Nat, e: {I.idr.alloc.at(V, c, xs, i, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {i == id : Nat}:
  match c:
    case True{}:
      Equal.cong(Result<&2, &2, I.IdError, I.IdrAlloc<V>>, Nat, r => res.id(V, r), Done{I.IdrAlloc{I.Idr{I.idr.slots.put(V, xs, i, Some{v})}, i}}, Done{I.IdrAlloc{t, id}}, e)
    case False{}:
      Empty.absurd({i == id : Nat}, absurd.fd(V, I.IdExhausted{}, I.IdrAlloc{t, id}, e))

def inv.map(-V: Data, c: Bool, +xs: List<&2, Maybe<&2, V>>, +i: Nat, +v: V, +t: I.Idr<V>, +id: Nat, e: {I.idr.alloc.at(V, c, xs, i, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {I.Idr{I.idr.slots.put(V, xs, i, Some{v})} == t : I.Idr<V>}:
  match c:
    case True{}:
      %e : {I.Idr{I.idr.slots.put(V, xs, i, Some{v})} == res.map(V, _, I.Idr{I.idr.slots.put(V, xs, i, Some{v})}) : I.Idr<V>}
      {==}
    case False{}:
      Empty.absurd({I.Idr{I.idr.slots.put(V, xs, i, Some{v})} == t : I.Idr<V>}, absurd.fd(V, I.IdExhausted{}, I.IdrAlloc{t, id}, e))

# What an allocation tells: e is alloc_range(Idr{xs}, [min, max], v) == Done{t, id}

def al.at(-V: Data, +xs: List<&2, Maybe<&2, V>>, +min: Nat, +max: Nat, +v: V, -t: I.Idr<V>, -id: Nat, e: {I.idr.alloc_range(V, I.Idr{xs}, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {I.idr.alloc.at(V, Nat.is_le(I.idr.slots.free_from(V, xs, min), max), xs, I.idr.slots.free_from(V, xs, min), v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}:
  inv.ord(V, Nat.is_le(min, max), xs, min, max, v, t, id, e)

def al.ord(-V: Data, +xs: List<&2, Maybe<&2, V>>, +min: Nat, +max: Nat, +v: V, -t: I.Idr<V>, -id: Nat, e: {I.idr.alloc_range(V, I.Idr{xs}, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {Nat.is_le(min, max) == True{} : Bool}:
  inv.ord_c(V, Nat.is_le(min, max), xs, min, max, v, t, id, e)

def al.fits(-V: Data, +xs: List<&2, Maybe<&2, V>>, +min: Nat, +max: Nat, +v: V, -t: I.Idr<V>, -id: Nat, e: {I.idr.alloc_range(V, I.Idr{xs}, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {Nat.is_le(I.idr.slots.free_from(V, xs, min), max) == True{} : Bool}:
  inv.fits(V, Nat.is_le(I.idr.slots.free_from(V, xs, min), max), xs, I.idr.slots.free_from(V, xs, min), v, t, id, al.at(V, xs, min, max, v, t, id, e))

def al.id(-V: Data, +xs: List<&2, Maybe<&2, V>>, +min: Nat, +max: Nat, +v: V, +t: I.Idr<V>, +id: Nat, e: {I.idr.alloc_range(V, I.Idr{xs}, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {I.idr.slots.free_from(V, xs, min) == id : Nat}:
  inv.id(V, Nat.is_le(I.idr.slots.free_from(V, xs, min), max), xs, I.idr.slots.free_from(V, xs, min), v, t, id, al.at(V, xs, min, max, v, t, id, e))

def al.map(-V: Data, +xs: List<&2, Maybe<&2, V>>, +min: Nat, +max: Nat, +v: V, +t: I.Idr<V>, +id: Nat, e: {I.idr.alloc_range(V, I.Idr{xs}, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {I.Idr{I.idr.slots.put(V, xs, I.idr.slots.free_from(V, xs, min), Some{v})} == t : I.Idr<V>}:
  inv.map(V, Nat.is_le(I.idr.slots.free_from(V, xs, min), max), xs, I.idr.slots.free_from(V, xs, min), v, t, id, al.at(V, xs, min, max, v, t, id, e))

# The allocation laws, for any V

def g.find(-V: Data, r: I.Idr<V>, +min: Nat, +max: Nat, +v: V, +t: I.Idr<V>, +id: Nat, +e: {I.idr.alloc_range(V, r, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {I.idr.find(V, t, id) == Some{v} : Maybe<&2, V>}:
  match r:
    case I.Idr{+xs}:
      %al.map(V, xs, min, max, v, t, id, e) : {I.idr.find(V, _, id) == Some{v} : Maybe<&2, V>}
      %al.id(V, xs, min, max, v, t, id, e) : {I.idr.find(V, I.Idr{I.idr.slots.put(V, xs, I.idr.slots.free_from(V, xs, min), Some{v})}, _) == Some{v} : Maybe<&2, V>}
      sl.get_put(V, xs, I.idr.slots.free_from(V, xs, min), Some{v})

def g.was_free(-V: Data, r: I.Idr<V>, +min: Nat, +max: Nat, +v: V, +t: I.Idr<V>, +id: Nat, +e: {I.idr.alloc_range(V, r, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {I.idr.find(V, r, id) == None{} : Maybe<&2, V>}:
  match r:
    case I.Idr{+xs}:
      %al.id(V, xs, min, max, v, t, id, e) : {I.idr.find(V, I.Idr{xs}, _) == None{} : Maybe<&2, V>}
      sl.ff_free(V, xs, min)

def g.at_least(-V: Data, r: I.Idr<V>, +min: Nat, +max: Nat, +v: V, +t: I.Idr<V>, +id: Nat, +e: {I.idr.alloc_range(V, r, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {Nat.is_le(min, id) == True{} : Bool}:
  match r:
    case I.Idr{+xs}:
      %al.id(V, xs, min, max, v, t, id, e) : {Nat.is_le(min, _) == True{} : Bool}
      sl.ff_ge(V, xs, min)

def g.at_most(-V: Data, r: I.Idr<V>, +min: Nat, +max: Nat, +v: V, +t: I.Idr<V>, +id: Nat, +e: {I.idr.alloc_range(V, r, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {Nat.is_le(id, max) == True{} : Bool}:
  match r:
    case I.Idr{+xs}:
      %al.id(V, xs, min, max, v, t, id, e) : {Nat.is_le(_, max) == True{} : Bool}
      al.fits(V, xs, min, max, v, t, id, e)

def g.in_range(-V: Data, +r: I.Idr<V>, +min: Nat, +max: Nat, +v: V, +t: I.Idr<V>, +id: Nat, +e: {I.idr.alloc_range(V, r, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {Bool.and(Nat.is_le(min, id), Nat.is_le(id, max)) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(min, id), True{}, g.at_least(V, r, min, max, v, t, id, e)) : {Bool.and(_, Nat.is_le(id, max)) == True{} : Bool}
  g.at_most(V, r, min, max, v, t, id, e)

def g.lowest(-V: Data, r: I.Idr<V>, +min: Nat, +max: Nat, +v: V, +t: I.Idr<V>, +id: Nat, +j: Nat, +e: {I.idr.alloc_range(V, r, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}, l: {Nat.is_le(min, j) == True{} : Bool}, m: {Nat.is_lt(j, id) == True{} : Bool}) -> {Maybe.is_some(&2, V, I.idr.find(V, r, j)) == True{} : Bool}:
  match r:
    case I.Idr{+xs}:
      sl.ff_lowest(V, xs, min, j, l, tr.lt(j, I.idr.slots.free_from(V, xs, min), id, al.id(V, xs, min, max, v, t, id, e), m))

def g.others(-V: Data, r: I.Idr<V>, +min: Nat, +max: Nat, +v: V, +t: I.Idr<V>, +id: Nat, +j: Nat, +e: {I.idr.alloc_range(V, r, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}, n: {Nat.is_eq(j, id) == False{} : Bool}) -> {I.idr.find(V, t, j) == I.idr.find(V, r, j) : Maybe<&2, V>}:
  match r:
    case I.Idr{+xs}:
      %al.map(V, xs, min, max, v, t, id, e) : {I.idr.find(V, _, j) == I.idr.find(V, I.Idr{xs}, j) : Maybe<&2, V>}
      sl.get_put_other(V, xs, I.idr.slots.free_from(V, xs, min), Some{v}, j, tr.ne(j, I.idr.slots.free_from(V, xs, min), id, al.id(V, xs, min, max, v, t, id, e), n))

def ex.ord(-V: Data, c: Bool, +xs: List<&2, Maybe<&2, V>>, +min: Nat, +max: Nat, +v: V, e: {I.idr.alloc.order(V, c, xs, min, max, v) == Fail{I.IdExhausted{}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {I.idr.alloc.at(V, Nat.is_le(I.idr.slots.free_from(V, xs, min), max), xs, I.idr.slots.free_from(V, xs, min), v) == Fail{I.IdExhausted{}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}:
  match c:
    case True{}:
      e
    case False{}:
      Empty.absurd({I.idr.alloc.at(V, Nat.is_le(I.idr.slots.free_from(V, xs, min), max), xs, I.idr.slots.free_from(V, xs, min), v) == Fail{I.IdExhausted{}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}, absurd.be(V, e))

def ex.at(-V: Data, c: Bool, +xs: List<&2, Maybe<&2, V>>, +i: Nat, +v: V, e: {I.idr.alloc.at(V, c, xs, i, v) == Fail{I.IdExhausted{}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, absurd.df(V, I.IdExhausted{}, I.IdrAlloc{I.Idr{I.idr.slots.put(V, xs, i, Some{v})}, i}, e))
    case False{}:
      {==}

def g.exhausted(-V: Data, r: I.Idr<V>, +min: Nat, +max: Nat, +v: V, +j: Nat, e: {I.idr.alloc_range(V, r, I.IdRange{min, max}, v) == Fail{I.IdExhausted{}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}, l: {Nat.is_le(min, j) == True{} : Bool}, m: {Nat.is_le(j, max) == True{} : Bool}) -> {Maybe.is_some(&2, V, I.idr.find(V, r, j)) == True{} : Bool}:
  match r:
    case I.Idr{+xs}:
      +ff = I.idr.slots.free_from(V, xs, min)
      sl.ff_lowest(V, xs, min, j, l, nat.nle_le_lt(ff, max, j, ex.at(V, Nat.is_le(ff, max), xs, ff, v, ex.ord(V, Nat.is_le(min, max), xs, min, max, v, e)), m))

def br.at(-V: Data, c: Bool, +xs: List<&2, Maybe<&2, V>>, +i: Nat, +v: V, e: {I.idr.alloc.at(V, c, xs, i, v) == Fail{I.IdBadRange{}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> Empty:
  match c:
    case True{}:
      absurd.df(V, I.IdBadRange{}, I.IdrAlloc{I.Idr{I.idr.slots.put(V, xs, i, Some{v})}, i}, e)
    case False{}:
      absurd.eb(V, e)

def br.ord(-V: Data, c: Bool, +xs: List<&2, Maybe<&2, V>>, +min: Nat, +max: Nat, +v: V, e: {I.idr.alloc.order(V, c, xs, min, max, v) == Fail{I.IdBadRange{}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, br.at(V, Nat.is_le(I.idr.slots.free_from(V, xs, min), max), xs, I.idr.slots.free_from(V, xs, min), v, e))
    case False{}:
      {==}

def g.bad_range(-V: Data, r: I.Idr<V>, +min: Nat, +max: Nat, +v: V, e: {I.idr.alloc_range(V, r, I.IdRange{min, max}, v) == Fail{I.IdBadRange{}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {Nat.is_lt(max, min) == True{} : Bool}:
  match r:
    case I.Idr{+xs}:
      nat.nle_lt(min, max, br.ord(V, Nat.is_le(min, max), xs, min, max, v, e))

def g.realloc(-V: Data, r: I.Idr<V>, +min: Nat, +max: Nat, +v: V, +t: I.Idr<V>, +id: Nat, +e: {I.idr.alloc_range(V, r, I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}) -> {I.idr.alloc_range(V, I.idr.free(V, t, id), I.IdRange{min, max}, v) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}:
  match r:
    case I.Idr{+xs}:
      +i = I.idr.slots.free_from(V, xs, min)
      +p = I.idr.slots.put(V, xs, i, Some{v})
      %al.map(V, xs, min, max, v, t, id, e) : {I.idr.alloc_range(V, I.idr.free(V, _, id), I.IdRange{min, max}, v) == Done{I.IdrAlloc{_, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}
      %al.id(V, xs, min, max, v, t, id, e) : {I.idr.alloc_range(V, I.idr.free(V, I.Idr{p}, _), I.IdRange{min, max}, v) == Done{I.IdrAlloc{I.Idr{p}, _}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}
      %Equal.sym(Bool, Nat.is_le(min, max), True{}, al.ord(V, xs, min, max, v, t, id, e)) : {I.idr.alloc.order(V, _, I.idr.slots.clear(V, p, i), min, max, v) == Done{I.IdrAlloc{I.Idr{p}, i}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}
      %Equal.sym(Nat, I.idr.slots.free_from(V, I.idr.slots.clear(V, p, i), min), i, sl.ff_realloc(V, xs, min, v)) : {I.idr.alloc.at(V, Nat.is_le(_, max), I.idr.slots.clear(V, p, i), _, v) == Done{I.IdrAlloc{I.Idr{p}, i}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}
      %Equal.sym(Bool, Nat.is_le(i, max), True{}, al.fits(V, xs, min, max, v, t, id, e)) : {I.idr.alloc.at(V, _, I.idr.slots.clear(V, p, i), i, v) == Done{I.IdrAlloc{I.Idr{p}, i}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}
      %Equal.sym(List<&2, Maybe<&2, V>>, I.idr.slots.put(V, I.idr.slots.clear(V, p, i), i, Some{v}), I.idr.slots.put(V, p, i, Some{v}), sl.put_clear(V, p, i, Some{v})) : {Done{I.IdrAlloc{I.Idr{_}, i}} == Done{I.IdrAlloc{I.Idr{p}, i}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}
      %Equal.sym(List<&2, Maybe<&2, V>>, I.idr.slots.put(V, p, i, Some{v}), p, sl.put_put(V, xs, i, Some{v}, Some{v})) : {Done{I.IdrAlloc{I.Idr{_}, i}} == Done{I.IdrAlloc{I.Idr{p}, i}} : Result<&2, &2, I.IdError, I.IdrAlloc<V>>}
      {==}

# IDA: freeing an ID below the next one makes it the next one
def g.free_lowest(s: I.Idr<Unit>, +min: Nat, +max: Nat, +t: I.Idr<Unit>, +id: Nat, +k: Nat, +e: {I.idr.alloc_range(Unit, s, I.IdRange{min, max}, Unit{}) == Done{I.IdrAlloc{t, id}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}, +l: {Nat.is_le(min, k) == True{} : Bool}, m: {Nat.is_lt(k, id) == True{} : Bool}) -> {I.idr.alloc_range(Unit, I.idr.free(Unit, s, k), I.IdRange{min, max}, Unit{}) == Done{I.IdrAlloc{s, k}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}:
  match s:
    case I.Idr{+xs}:
      +i = I.idr.slots.free_from(Unit, xs, min)
      +c = I.idr.slots.clear(Unit, xs, k)
      +lt = tr.lt(k, i, id, al.id(Unit, xs, min, max, Unit{}, t, id, e), m)
      +le = nat.lt_le(k, i, lt)
      %Equal.sym(Bool, Nat.is_le(min, max), True{}, al.ord(Unit, xs, min, max, Unit{}, t, id, e)) : {I.idr.alloc.order(Unit, _, c, min, max, Unit{}) == Done{I.IdrAlloc{I.Idr{xs}, k}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}
      %Equal.sym(Nat, I.idr.slots.free_from(Unit, c, min), k, sl.ff_clear(Unit, xs, min, k, l, le)) : {I.idr.alloc.at(Unit, Nat.is_le(_, max), c, _, Unit{}) == Done{I.IdrAlloc{I.Idr{xs}, k}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}
      %Equal.sym(Bool, Nat.is_le(k, max), True{}, nat.le_trans(k, i, max, le, al.fits(Unit, xs, min, max, Unit{}, t, id, e))) : {I.idr.alloc.at(Unit, _, c, k, Unit{}) == Done{I.IdrAlloc{I.Idr{xs}, k}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}
      %Equal.sym(List<&2, Maybe<&2, Unit>>, I.idr.slots.put(Unit, c, k, Some{Unit{}}), I.idr.slots.put(Unit, xs, k, Some{Unit{}}), sl.put_clear(Unit, xs, k, Some{Unit{}})) : {Done{I.IdrAlloc{I.Idr{_}, k}} == Done{I.IdrAlloc{I.Idr{xs}, k}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}
      %Equal.sym(List<&2, Maybe<&2, Unit>>, I.idr.slots.put(Unit, xs, k, Some{Unit{}}), xs, sl.put_same(Unit, xs, k, Unit{}, unit.some(I.idr.slots.get(Unit, xs, k), sl.ff_lowest(Unit, xs, min, k, l, lt)))) : {Done{I.IdrAlloc{I.Idr{_}, k}} == Done{I.IdrAlloc{I.Idr{xs}, k}} : Result<&2, &2, I.IdError, I.IdrAlloc<Unit>>}
      {==}

# Replace

def rp.find(-V: Data, m: Maybe<&2, V>, +xs: List<&2, Maybe<&2, V>>, +k: Nat, +v: V, +t: I.Idr<V>, -old: V, e: {I.idr.replace.at(V, m, xs, k, v) == Done{I.IdrOld{t, old}} : Result<&2, &2, I.IdError, I.IdrOld<V>>}) -> {I.idr.find(V, t, k) == Some{v} : Maybe<&2, V>}:
  match m:
    case None{}:
      Empty.absurd({I.idr.find(V, t, k) == Some{v} : Maybe<&2, V>}, absurd.ofd(V, I.IdNotFound{}, I.IdrOld{t, old}, e))
    case Some{o}:
      %e : {I.idr.find(V, old.map(V, _, t), k) == Some{v} : Maybe<&2, V>}
      sl.get_put(V, xs, k, Some{v})

def rp.old(-V: Data, m: Maybe<&2, V>, -xs: List<&2, Maybe<&2, V>>, -k: Nat, -v: V, -t: I.Idr<V>, +old: V, g: {I.idr.slots.get(V, xs, k) == m : Maybe<&2, V>}, e: {I.idr.replace.at(V, m, xs, k, v) == Done{I.IdrOld{t, old}} : Result<&2, &2, I.IdError, I.IdrOld<V>>}) -> {I.idr.slots.get(V, xs, k) == Some{old} : Maybe<&2, V>}:
  match m:
    case None{}:
      Empty.absurd({I.idr.slots.get(V, xs, k) == Some{old} : Maybe<&2, V>}, absurd.ofd(V, I.IdNotFound{}, I.IdrOld{t, old}, e))
    case Some{o}:
      %e : {I.idr.slots.get(V, xs, k) == Some{old.val(V, _, old)} : Maybe<&2, V>}
      g

def rp.others(-V: Data, m: Maybe<&2, V>, +xs: List<&2, Maybe<&2, V>>, +k: Nat, +v: V, +t: I.Idr<V>, -old: V, +j: Nat, e: {I.idr.replace.at(V, m, xs, k, v) == Done{I.IdrOld{t, old}} : Result<&2, &2, I.IdError, I.IdrOld<V>>}, n: {Nat.is_eq(j, k) == False{} : Bool}) -> {I.idr.find(V, t, j) == I.idr.slots.get(V, xs, j) : Maybe<&2, V>}:
  match m:
    case None{}:
      Empty.absurd({I.idr.find(V, t, j) == I.idr.slots.get(V, xs, j) : Maybe<&2, V>}, absurd.ofd(V, I.IdNotFound{}, I.IdrOld{t, old}, e))
    case Some{o}:
      %e : {I.idr.find(V, old.map(V, _, t), j) == I.idr.slots.get(V, xs, j) : Maybe<&2, V>}
      sl.get_put_other(V, xs, k, Some{v}, j, n)

# The laws: IDA

def Laws.ida_alloc_was_free(s, min, max, t, id, e):
  %Equal.sym(Maybe<&2, Unit>, I.idr.find(Unit, s, id), None{}, g.was_free(Unit, s, min, max, Unit{}, t, id, e)) : {Maybe.is_some(&2, Unit, _) == False{} : Bool}
  {==}

def Laws.ida_alloc_in_use(s, min, max, t, id, e):
  %Equal.sym(Maybe<&2, Unit>, I.idr.find(Unit, t, id), Some{Unit{}}, g.find(Unit, s, min, max, Unit{}, t, id, e)) : {Maybe.is_some(&2, Unit, _) == True{} : Bool}
  {==}

def Laws.ida_alloc_at_least(s, min, max, t, id, e):
  g.at_least(Unit, s, min, max, Unit{}, t, id, e)

def Laws.ida_alloc_at_most(s, min, max, t, id, e):
  g.at_most(Unit, s, min, max, Unit{}, t, id, e)

def Laws.ida_alloc_lowest(s, min, max, t, id, j, e, l, m):
  g.lowest(Unit, s, min, max, Unit{}, t, id, j, e, l, m)

def Laws.ida_alloc_others(s, min, max, t, id, j, e, n):
  %g.others(Unit, s, min, max, Unit{}, t, id, j, e, n) : {Maybe.is_some(&2, Unit, I.idr.find(Unit, t, j)) == Maybe.is_some(&2, Unit, _) : Bool}
  {==}

def Laws.ida_alloc_exhausted(s, min, max, j, e, l, m):
  g.exhausted(Unit, s, min, max, Unit{}, j, e, l, m)

def Laws.ida_alloc_bad_range(s, min, max, e):
  g.bad_range(Unit, s, min, max, Unit{}, e)

def Laws.ida_free_frees(s, k):
  match s:
    case I.Idr{+xs}:
      %Equal.sym(Maybe<&2, Unit>, I.idr.slots.get(Unit, I.idr.slots.clear(Unit, xs, k), k), None{}, sl.get_clear(Unit, xs, k)) : {Maybe.is_some(&2, Unit, _) == False{} : Bool}
      {==}

def Laws.ida_free_others(s, k, j, n):
  match s:
    case I.Idr{+xs}:
      %sl.get_clear_other(Unit, xs, k, j, n) : {Maybe.is_some(&2, Unit, I.idr.slots.get(Unit, I.idr.slots.clear(Unit, xs, k), j)) == Maybe.is_some(&2, Unit, _) : Bool}
      {==}

def Laws.ida_realloc(s, min, max, t, id, e):
  g.realloc(Unit, s, min, max, Unit{}, t, id, e)

def Laws.ida_free_lowest(s, min, max, t, id, k, e, l, m):
  g.free_lowest(s, min, max, t, id, k, e, l, m)

# The laws: IDR

def Laws.idr_alloc_find(V, r, min, max, v, t, id, e):
  g.find(V, r, min, max, v, t, id, e)

def Laws.idr_alloc_was_free(V, r, min, max, v, t, id, e):
  g.was_free(V, r, min, max, v, t, id, e)

def Laws.idr_alloc_in_range(V, r, min, max, v, t, id, e):
  g.in_range(V, r, min, max, v, t, id, e)

def Laws.idr_alloc_lowest(V, r, min, max, v, t, id, j, e, l, m):
  g.lowest(V, r, min, max, v, t, id, j, e, l, m)

def Laws.idr_alloc_others(V, r, min, max, v, t, id, j, e, n):
  g.others(V, r, min, max, v, t, id, j, e, n)

def Laws.idr_realloc(V, r, min, max, v, t, id, e):
  g.realloc(V, r, min, max, v, t, id, e)

def Laws.idr_remove_old(V, r, k):
  match r:
    case I.Idr{xs}:
      {==}

def Laws.idr_remove_frees(V, r, k):
  match r:
    case I.Idr{xs}:
      sl.get_clear(V, xs, k)

def Laws.idr_remove_others(V, r, k, j, n):
  match r:
    case I.Idr{xs}:
      sl.get_clear_other(V, xs, k, j, n)

def Laws.idr_free_is_remove(V, r, k):
  match r:
    case I.Idr{xs}:
      {==}

def l.replace_find(-V: Data, r: I.Idr<V>, +k: Nat, +v: V, +t: I.Idr<V>, -old: V, e: {I.idr.replace(V, r, k, v) == Done{I.IdrOld{t, old}} : Result<&2, &2, I.IdError, I.IdrOld<V>>}) -> {I.idr.find(V, t, k) == Some{v} : Maybe<&2, V>}:
  match r:
    case I.Idr{+xs}:
      rp.find(V, I.idr.slots.get(V, xs, k), xs, k, v, t, old, e)

def l.replace_old(-V: Data, r: I.Idr<V>, +k: Nat, -v: V, -t: I.Idr<V>, +old: V, e: {I.idr.replace(V, r, k, v) == Done{I.IdrOld{t, old}} : Result<&2, &2, I.IdError, I.IdrOld<V>>}) -> {I.idr.find(V, r, k) == Some{old} : Maybe<&2, V>}:
  match r:
    case I.Idr{+xs}:
      rp.old(V, I.idr.slots.get(V, xs, k), xs, k, v, t, old, {==}, e)

def l.replace_others(-V: Data, r: I.Idr<V>, +k: Nat, +v: V, +t: I.Idr<V>, -old: V, +j: Nat, e: {I.idr.replace(V, r, k, v) == Done{I.IdrOld{t, old}} : Result<&2, &2, I.IdError, I.IdrOld<V>>}, n: {Nat.is_eq(j, k) == False{} : Bool}) -> {I.idr.find(V, t, j) == I.idr.find(V, r, j) : Maybe<&2, V>}:
  match r:
    case I.Idr{+xs}:
      rp.others(V, I.idr.slots.get(V, xs, k), xs, k, v, t, old, j, e, n)

def l.replace_absent(-V: Data, r: I.Idr<V>, +k: Nat, +v: V, e: {I.idr.find(V, r, k) == None{} : Maybe<&2, V>}) -> {I.idr.replace(V, r, k, v) == Fail{I.IdNotFound{}} : Result<&2, &2, I.IdError, I.IdrOld<V>>}:
  match r:
    case I.Idr{+xs}:
      %Equal.sym(Maybe<&2, V>, I.idr.slots.get(V, xs, k), None{}, e) : {I.idr.replace.at(V, _, xs, k, v) == Fail{I.IdNotFound{}} : Result<&2, &2, I.IdError, I.IdrOld<V>>}
      {==}

def Laws.idr_replace_find(V, r, k, v, t, old, e):
  l.replace_find(V, r, k, v, t, old, e)

def Laws.idr_replace_old(V, r, k, v, t, old, e):
  l.replace_old(V, r, k, v, t, old, e)

def Laws.idr_replace_others(V, r, k, v, t, old, j, e, n):
  l.replace_others(V, r, k, v, t, old, j, e, n)

def Laws.idr_replace_absent(V, r, k, v, e):
  l.replace_absent(V, r, k, v, e)

# Vectors

def Laws.vec_three():
  {==}

def Laws.vec_gap():
  {==}

def Laws.vec_min():
  {==}

def Laws.vec_exhausted():
  {==}

def Laws.vec_bad_range():
  {==}

def Laws.vec_idr():
  {==}

def Laws.wit_alloc_below():
  {==}

def Laws.wit_replace():
  {==}
