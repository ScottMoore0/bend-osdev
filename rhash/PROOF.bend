import Base
import ./rhash.bend as R
import ./model.bend as M
import ./LAWS.bend as Laws

# ---------------------------------------------------------------- contradictions

def ab.bool(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def ab.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : ab.bool(_)
  Unit{}

def ab.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : ab.bool(_)
  Unit{}

def bool.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, ab.ft(e))

def bool.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, ab.ft(e))

# ---------------------------------------------------------------- U32 equality

def bool_cmp_self(b: Bool) -> {Word.cmp.fin(b, b, EQ{}) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def word_cmp_self(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+b, t}:
          Equal.trans(Cmp, Word.cmp.fin(b, b, Word.cmp(p, t, t)), Word.cmp.fin(b, b, EQ{}), EQ{},
            Equal.cong(Cmp, Cmp, x => Word.cmp.fin(b, b, x), Word.cmp(p, t, t), EQ{}, word_cmp_self(p, t)),
            bool_cmp_self(b))

def u32_eq_self(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{+w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, word_cmp_self(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

def word.eq_tail(c: Cmp, x: Bool, y: Bool, e: {Cmp.is_eq(Word.cmp.fin(x, y, c)) == True{} : Bool}) -> {Cmp.is_eq(c) == True{} : Bool}:
  match c:
    case LT{}:
      Empty.absurd({False{} == True{} : Bool}, ab.ft(e))
    case EQ{}:
      {==}
    case GT{}:
      Empty.absurd({False{} == True{} : Bool}, ab.ft(e))

def word.eq_head(c: Cmp, x: Bool, y: Bool, e: {Cmp.is_eq(Word.cmp.fin(x, y, c)) == True{} : Bool}) -> {x == y : Bool}:
  match c:
    case LT{}:
      Empty.absurd({x == y : Bool}, ab.ft(e))
    case EQ{}:
      match x y:
        case True{} True{}:
          {==}
        case False{} False{}:
          {==}
        case True{} False{}:
          Empty.absurd({True{} == False{} : Bool}, ab.ft(e))
        case False{} True{}:
          Empty.absurd({False{} == True{} : Bool}, ab.ft(e))
    case GT{}:
      Empty.absurd({x == y : Bool}, ab.ft(e))

def word.eq(n: Nat, a: Word(n), b: Word(n), e: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          +e2 = e
          %word.eq(p, at, bt, word.eq_tail(Word.cmp(p, at, bt), x, y, e2)) : {WCon{x, at} == WCon{y, _} : Word(1n+p)}
          %word.eq_head(Word.cmp(p, at, bt), x, y, e2) : {WCon{x, at} == WCon{_, at} : Word(1n+p)}
          {==}

def u32.eq(a: U32, b: U32, e: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a b:
    case U32{+wa} U32{+wb}:
      %word.eq(32n, wa, wb, e) : {U32{wa} == U32{_} : U32}
      {==}

# ---------------------------------------------------------------- equality of encodings

def weq_self(xs: List<&2, U32>) -> {R.rh.weq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(Bool, U32.is_eq(h, h), True{}, u32_eq_self(h)) : {Bool.and(_, R.rh.weq(t, t)) == True{} : Bool}
      weq_self(t)

def weq_sound(xs: List<&2, U32>, ys: List<&2, U32>, e: {R.rh.weq(xs, ys) == True{} : Bool}) -> {xs == ys : List<&2, U32>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Con{+x, +xt} Con{+y, +yt}:
      +e2 = e
      %u32.eq(x, y, bool.and_l(U32.is_eq(x, y), R.rh.weq(xt, yt), e2)) : {Con{x, xt} == Con{_, yt} : List<&2, U32>}
      %weq_sound(xt, yt, bool.and_r(U32.is_eq(x, y), R.rh.weq(xt, yt), e2)) : {Con{x, xt} == Con{x, _} : List<&2, U32>}
      {==}
    case Nil{} Con{y, yt}:
      Empty.absurd({Nil{} == Con{y, yt} : List<&2, U32>}, ab.ft(e))
    case Con{x, xt} Nil{}:
      Empty.absurd({Con{x, xt} == Nil{} : List<&2, U32>}, ab.ft(e))

def weq_false_sym.go(+a: List<&2, U32>, +b: List<&2, U32>, x: Bool, ex: {R.rh.weq(b, a) == x : Bool}, e: {R.rh.weq(a, b) == False{} : Bool}) -> {R.rh.weq(b, a) == False{} : Bool}:
  match x:
    case False{}:
      ex
    case True{}:
      +s = weq_sound(b, a, ex)
      Empty.absurd({R.rh.weq(b, a) == False{} : Bool}, ab.tf(Equal.trans(Bool, True{}, R.rh.weq(a, b), False{}, Equal.trans(Bool, True{}, R.rh.weq(a, a), R.rh.weq(a, b), Equal.sym(Bool, R.rh.weq(a, a), True{}, weq_self(a)), Equal.cong(List<&2, U32>, Bool, z => R.rh.weq(a, z), a, b, Equal.sym(List<&2, U32>, b, a, s))), e)))

def weq_false_sym(+a: List<&2, U32>, +b: List<&2, U32>, e: {R.rh.weq(a, b) == False{} : Bool}) -> {R.rh.weq(b, a) == False{} : Bool}:
  weq_false_sym.go(a, b, R.rh.weq(b, a), {==}, e)


# ---------------------------------------------------------------- buckets

def orelse_none(~K: Data, ~V: Data, x: Maybe<&2, V>) -> {R.rh.orelse(~V, x, None{}) == x : Maybe<&2, V>}:
  match x:
    case Some{v}:
      {==}
    case None{}:
      {==}

def orelse_some(~K: Data, ~V: Data, x: Maybe<&2, V>, -v: V, -y: Maybe<&2, V>) -> {R.rh.orelse(~V, R.rh.orelse(~V, x, Some{v}), y) == R.rh.orelse(~V, x, Some{v}) : Maybe<&2, V>}:
  match x:
    case Some{u}:
      {==}
    case None{}:
      {==}

def orelse_assoc(~K: Data, ~V: Data, x: Maybe<&2, V>, -y: Maybe<&2, V>, -z: Maybe<&2, V>) -> {R.rh.orelse(~V, R.rh.orelse(~V, x, y), z) == R.rh.orelse(~V, x, R.rh.orelse(~V, y, z)) : Maybe<&2, V>}:
  match x:
    case Some{u}:
      {==}
    case None{}:
      {==}

def fds.go(~K: Data, ~V: Data, +kw: List<&2, U32>, +w: List<&2, U32>, -k: K, -v: V, -t: List<&2, R.RhEntry<K, V>>, b: Bool, +eb: {R.rh.weq(kw, w) == b : Bool}, ih: {R.rh.find(~K, ~V, kw, R.rh.drop(~K, ~V, kw, t)) == None{} : Maybe<&2, V>}) -> {R.rh.find(~K, ~V, kw, R.rh.keep(~K, ~V, R.rh.weq(kw, w), R.RhEntry{w, k, v}, R.rh.drop(~K, ~V, kw, t))) == None{} : Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(Bool, R.rh.weq(kw, w), True{}, eb) : {R.rh.find(~K, ~V, kw, R.rh.keep(~K, ~V, _, R.RhEntry{w, k, v}, R.rh.drop(~K, ~V, kw, t))) == None{} : Maybe<&2, V>}
      ih
    case False{}:
      %Equal.sym(Bool, R.rh.weq(kw, w), False{}, eb) : {R.rh.find(~K, ~V, kw, R.rh.keep(~K, ~V, _, R.RhEntry{w, k, v}, R.rh.drop(~K, ~V, kw, t))) == None{} : Maybe<&2, V>}
      %Equal.sym(Bool, R.rh.weq(kw, w), False{}, eb) : {R.rh.hit(~V, _, v, R.rh.find(~K, ~V, kw, R.rh.drop(~K, ~V, kw, t))) == None{} : Maybe<&2, V>}
      ih

# a key's bucket has no entry for it after the key is dropped
def find_drop_same(~K: Data, ~V: Data, +kw: List<&2, U32>, es: List<&2, R.RhEntry<K, V>>) -> {R.rh.find(~K, ~V, kw, R.rh.drop(~K, ~V, kw, es)) == None{} : Maybe<&2, V>}:
  match es:
    case Nil{}:
      {==}
    case Con{e, t}:
      match e:
        case R.RhEntry{+w, k, v}:
          fds.go(~K, ~V, kw, w, k, v, t, R.rh.weq(kw, w), {==}, find_drop_same(~K, ~V, kw, t))

def fdo.go(~K: Data, ~V: Data, +kw: List<&2, U32>, +jw: List<&2, U32>, +ne: {R.rh.weq(jw, kw) == False{} : Bool}, +w: List<&2, U32>, -k: K, -v: V, -t: List<&2, R.RhEntry<K, V>>, b: Bool, +eb: {R.rh.weq(kw, w) == b : Bool}, ih: {R.rh.find(~K, ~V, jw, R.rh.drop(~K, ~V, kw, t)) == R.rh.find(~K, ~V, jw, t) : Maybe<&2, V>}) -> {R.rh.find(~K, ~V, jw, R.rh.keep(~K, ~V, R.rh.weq(kw, w), R.RhEntry{w, k, v}, R.rh.drop(~K, ~V, kw, t))) == R.rh.hit(~V, R.rh.weq(jw, w), v, R.rh.find(~K, ~V, jw, t)) : Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(Bool, R.rh.weq(kw, w), True{}, eb) : {R.rh.find(~K, ~V, jw, R.rh.keep(~K, ~V, _, R.RhEntry{w, k, v}, R.rh.drop(~K, ~V, kw, t))) == R.rh.hit(~V, R.rh.weq(jw, w), v, R.rh.find(~K, ~V, jw, t)) : Maybe<&2, V>}
      %weq_sound(kw, w, eb) : {R.rh.find(~K, ~V, jw, R.rh.drop(~K, ~V, kw, t)) == R.rh.hit(~V, R.rh.weq(jw, _), v, R.rh.find(~K, ~V, jw, t)) : Maybe<&2, V>}
      %Equal.sym(Bool, R.rh.weq(jw, kw), False{}, ne) : {R.rh.find(~K, ~V, jw, R.rh.drop(~K, ~V, kw, t)) == R.rh.hit(~V, _, v, R.rh.find(~K, ~V, jw, t)) : Maybe<&2, V>}
      ih
    case False{}:
      %Equal.sym(Bool, R.rh.weq(kw, w), False{}, eb) : {R.rh.find(~K, ~V, jw, R.rh.keep(~K, ~V, _, R.RhEntry{w, k, v}, R.rh.drop(~K, ~V, kw, t))) == R.rh.hit(~V, R.rh.weq(jw, w), v, R.rh.find(~K, ~V, jw, t)) : Maybe<&2, V>}
      %ih : {R.rh.hit(~V, R.rh.weq(jw, w), v, R.rh.find(~K, ~V, jw, R.rh.drop(~K, ~V, kw, t))) == R.rh.hit(~V, R.rh.weq(jw, w), v, _) : Maybe<&2, V>}
      {==}

# dropping one key leaves every other key's value
def find_drop_other(~K: Data, ~V: Data, +kw: List<&2, U32>, +jw: List<&2, U32>, +ne: {R.rh.weq(jw, kw) == False{} : Bool}, es: List<&2, R.RhEntry<K, V>>) -> {R.rh.find(~K, ~V, jw, R.rh.drop(~K, ~V, kw, es)) == R.rh.find(~K, ~V, jw, es) : Maybe<&2, V>}:
  match es:
    case Nil{}:
      {==}
    case Con{e, t}:
      match e:
        case R.RhEntry{+w, k, v}:
          fdo.go(~K, ~V, kw, jw, ne, w, k, v, t, R.rh.weq(kw, w), {==}, find_drop_other(~K, ~V, kw, jw, ne, t))

def find_cons_same(~K: Data, ~V: Data, +kw: List<&2, U32>, -k: K, v: V, -l: List<&2, R.RhEntry<K, V>>) -> {R.rh.find(~K, ~V, kw, Con{R.RhEntry{kw, k, v}, l}) == Some{v} : Maybe<&2, V>}:
  %Equal.sym(Bool, R.rh.weq(kw, kw), True{}, weq_self(kw)) : {R.rh.hit(~V, _, v, R.rh.find(~K, ~V, kw, l)) == Some{v} : Maybe<&2, V>}
  {==}

def find_cons_other(~K: Data, ~V: Data, +jw: List<&2, U32>, +w: List<&2, U32>, ne: {R.rh.weq(jw, w) == False{} : Bool}, -k: K, -v: V, -l: List<&2, R.RhEntry<K, V>>) -> {R.rh.find(~K, ~V, jw, Con{R.RhEntry{w, k, v}, l}) == R.rh.find(~K, ~V, jw, l) : Maybe<&2, V>}:
  %Equal.sym(Bool, R.rh.weq(jw, w), False{}, ne) : {R.rh.hit(~V, _, v, R.rh.find(~K, ~V, jw, l)) == R.rh.find(~K, ~V, jw, l) : Maybe<&2, V>}
  {==}

def fsn.go(~K: Data, ~V: Data, +kw: List<&2, U32>, +w2: List<&2, U32>, -v2: V, -t: List<&2, R.RhEntry<K, V>>, -x: Maybe<&2, V>, b: Bool, +eb: {R.rh.weq(kw, w2) == b : Bool}, -s: List<&2, R.RhEntry<K, V>>, ih: {R.rh.find(~K, ~V, kw, s) == R.rh.orelse(~V, R.rh.find(~K, ~V, kw, t), x) : Maybe<&2, V>}) -> {R.rh.hit(~V, R.rh.weq(kw, w2), v2, R.rh.find(~K, ~V, kw, s)) == R.rh.orelse(~V, R.rh.hit(~V, R.rh.weq(kw, w2), v2, R.rh.find(~K, ~V, kw, t)), x) : Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(Bool, R.rh.weq(kw, w2), True{}, eb) : {R.rh.hit(~V, _, v2, R.rh.find(~K, ~V, kw, s)) == R.rh.orelse(~V, R.rh.hit(~V, _, v2, R.rh.find(~K, ~V, kw, t)), x) : Maybe<&2, V>}
      {==}
    case False{}:
      %Equal.sym(Bool, R.rh.weq(kw, w2), False{}, eb) : {R.rh.hit(~V, _, v2, R.rh.find(~K, ~V, kw, s)) == R.rh.orelse(~V, R.rh.hit(~V, _, v2, R.rh.find(~K, ~V, kw, t)), x) : Maybe<&2, V>}
      ih

# an entry added at the end is found only after every earlier one
def find_snoc(~K: Data, ~V: Data, +kw: List<&2, U32>, l: List<&2, R.RhEntry<K, V>>, +w: List<&2, U32>, -k: K, -v: V) -> {R.rh.find(~K, ~V, kw, R.rh.snoc(~K, ~V, l, R.RhEntry{w, k, v})) == R.rh.orelse(~V, R.rh.find(~K, ~V, kw, l), R.rh.hit(~V, R.rh.weq(kw, w), v, None{})) : Maybe<&2, V>}:
  match l:
    case Nil{}:
      {==}
    case Con{h, t}:
      match h:
        case R.RhEntry{+w2, k2, v2}:
          fsn.go(~K, ~V, kw, w2, v2, t, R.rh.hit(~V, R.rh.weq(kw, w), v, None{}), R.rh.weq(kw, w2), {==}, R.rh.snoc(~K, ~V, t, R.RhEntry{w, k, v}), find_snoc(~K, ~V, kw, t, w, k, v))

# ---------------------------------------------------------------- trees

def get_put_same(~K: Data, ~V: Data, t: R.RhTree<K, V>, +p: List<&2, Bool>, op: R.RhBop<K, V>) -> {R.RhTree.get(~K, ~V, R.RhTree.put(~K, ~V, t, p, op), p) == R.rh.apply(~K, ~V, op, R.RhTree.get(~K, ~V, t, p)) : List<&2, R.RhEntry<K, V>>}:
  match t:
    case R.RhLeaf{es}:
      {==}
    case R.RhNode{lo, hi}:
      match p:
        case Nil{}:
          get_put_same(~K, ~V, lo, Nil{}, op)
        case Con{b, ps}:
          match b:
            case True{}:
              get_put_same(~K, ~V, hi, ps, op)
            case False{}:
              get_put_same(~K, ~V, lo, ps, op)

# a bucket operation that does not change one key's value in any bucket
# does not change it in the tree
def frame(~K: Data, ~V: Data, +kw: List<&2, U32>, t: R.RhTree<K, V>, +p: List<&2, Bool>, +q: List<&2, Bool>, op: R.RhBop<K, V>, h: @l: List<&2, R.RhEntry<K, V>> -> {R.rh.find(~K, ~V, kw, R.rh.apply(~K, ~V, op, l)) == R.rh.find(~K, ~V, kw, l) : Maybe<&2, V>}) -> {R.rh.find(~K, ~V, kw, R.RhTree.get(~K, ~V, R.RhTree.put(~K, ~V, t, p, op), q)) == R.rh.find(~K, ~V, kw, R.RhTree.get(~K, ~V, t, q)) : Maybe<&2, V>}:
  match t:
    case R.RhLeaf{es}:
      h(es)
    case R.RhNode{lo, hi}:
      match p:
        case Nil{}:
          match q:
            case Nil{}:
              frame(~K, ~V, kw, lo, Nil{}, Nil{}, op, h)
            case Con{c, qs}:
              match c:
                case True{}:
                  {==}
                case False{}:
                  frame(~K, ~V, kw, lo, Nil{}, qs, op, h)
        case Con{b, ps}:
          match b:
            case True{}:
              match q:
                case Nil{}:
                  {==}
                case Con{c, qs}:
                  match c:
                    case True{}:
                      frame(~K, ~V, kw, hi, ps, qs, op, h)
                    case False{}:
                      {==}
            case False{}:
              match q:
                case Nil{}:
                  frame(~K, ~V, kw, lo, ps, Nil{}, op, h)
                case Con{c, qs}:
                  match c:
                    case True{}:
                      {==}
                    case False{}:
                      frame(~K, ~V, kw, lo, ps, qs, op, h)

def get_full(~K: Data, ~V: Data, n: Nat, q: List<&2, Bool>) -> {R.RhTree.get(~K, ~V, R.RhTree.full(~K, ~V, n), q) == Nil{} : List<&2, R.RhEntry<K, V>>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match q:
        case Nil{}:
          get_full(~K, ~V, p, Nil{})
        case Con{c, qs}:
          match c:
            case True{}:
              get_full(~K, ~V, p, qs)
            case False{}:
              get_full(~K, ~V, p, qs)

def get_nil2(~K: Data, ~V: Data, q: List<&2, Bool>) -> {R.RhTree.get(~K, ~V, R.RhNode{R.RhLeaf{Nil{}}, R.RhLeaf{Nil{}}}, q) == Nil{} : List<&2, R.RhEntry<K, V>>}:
  match q:
    case Nil{}:
      {==}
    case Con{c, qs}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}

# collapsing two empty halves changes no bucket
def get_prune(~K: Data, ~V: Data, a: R.RhTree<K, V>, b: R.RhTree<K, V>, q: List<&2, Bool>) -> {R.RhTree.get(~K, ~V, R.rh.prune(~K, ~V, a, b), q) == R.RhTree.get(~K, ~V, R.RhNode{a, b}, q) : List<&2, R.RhEntry<K, V>>}:
  match a:
    case R.RhLeaf{x}:
      match x:
        case Nil{}:
          match b:
            case R.RhLeaf{y}:
              match y:
                case Nil{}:
                  Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.RhNode{R.RhLeaf{Nil{}}, R.RhLeaf{Nil{}}}, q), Nil{}, get_nil2(~K, ~V, q))
                case Con{y1, ys}:
                  {==}
            case R.RhNode{c, d}:
              {==}
        case Con{x1, xs}:
          match b:
            case R.RhLeaf{y}:
              {==}
            case R.RhNode{c, d}:
              {==}
    case R.RhNode{c, d}:
      {==}

# ---------------------------------------------------------------- taking a bucket out

def tk.path(~K: Data, ~V: Data, r: R.RhTake<K, V>) -> List<&2, Bool>:
  match r:
    case R.RhTake{tp, es, rest}:
      tp

def tk.es(~K: Data, ~V: Data, r: R.RhTake<K, V>) -> List<&2, R.RhEntry<K, V>>:
  match r:
    case R.RhTake{tp, es, rest}:
      es

def tk.rest(~K: Data, ~V: Data, r: R.RhTake<K, V>) -> R.RhTree<K, V>:
  match r:
    case R.RhTake{tp, es, rest}:
      rest

# (1) a bucket of the tree is the bucket taken if the path leads to it,
# and otherwise the same bucket of what is left

def tk1.lo_same(~K: Data, ~V: Data, -lo: R.RhTree<K, V>, +hi: R.RhTree<K, V>, r: R.RhTake<K, V>, +q: List<&2, Bool>, ih: {R.RhTree.get(~K, ~V, lo, q) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, r), q), tk.es(~K, ~V, r), R.RhTree.get(~K, ~V, tk.rest(~K, ~V, r), q)) : List<&2, R.RhEntry<K, V>>}) -> {R.RhTree.get(~K, ~V, R.RhNode{lo, hi}, Con{False{}, q}) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, R.rh.take.lo(~K, ~V, r, hi)), Con{False{}, q}), tk.es(~K, ~V, R.rh.take.lo(~K, ~V, r, hi)), R.RhTree.get(~K, ~V, tk.rest(~K, ~V, R.rh.take.lo(~K, ~V, r, hi)), Con{False{}, q})) : List<&2, R.RhEntry<K, V>>}:
  match r:
    case R.RhTake{+tp, es, +rest}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.rh.prune(~K, ~V, rest, hi), Con{False{}, q}), R.RhTree.get(~K, ~V, R.RhNode{rest, hi}, Con{False{}, q}), get_prune(~K, ~V, rest, hi, Con{False{}, q})) : {R.RhTree.get(~K, ~V, lo, q) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tp, q), es, _) : List<&2, R.RhEntry<K, V>>}
      ih

def tk1.lo_nil(~K: Data, ~V: Data, -lo: R.RhTree<K, V>, +hi: R.RhTree<K, V>, r: R.RhTake<K, V>, ih: {R.RhTree.get(~K, ~V, lo, Nil{}) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, r), Nil{}), tk.es(~K, ~V, r), R.RhTree.get(~K, ~V, tk.rest(~K, ~V, r), Nil{})) : List<&2, R.RhEntry<K, V>>}) -> {R.RhTree.get(~K, ~V, R.RhNode{lo, hi}, Nil{}) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, R.rh.take.lo(~K, ~V, r, hi)), Nil{}), tk.es(~K, ~V, R.rh.take.lo(~K, ~V, r, hi)), R.RhTree.get(~K, ~V, tk.rest(~K, ~V, R.rh.take.lo(~K, ~V, r, hi)), Nil{})) : List<&2, R.RhEntry<K, V>>}:
  match r:
    case R.RhTake{+tp, es, +rest}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.rh.prune(~K, ~V, rest, hi), Nil{}), R.RhTree.get(~K, ~V, R.RhNode{rest, hi}, Nil{}), get_prune(~K, ~V, rest, hi, Nil{})) : {R.RhTree.get(~K, ~V, lo, Nil{}) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tp, Nil{}), es, _) : List<&2, R.RhEntry<K, V>>}
      ih

def tk1.lo_other(~K: Data, ~V: Data, -lo: R.RhTree<K, V>, +hi: R.RhTree<K, V>, r: R.RhTake<K, V>, +q: List<&2, Bool>) -> {R.RhTree.get(~K, ~V, R.RhNode{lo, hi}, Con{True{}, q}) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, R.rh.take.lo(~K, ~V, r, hi)), Con{True{}, q}), tk.es(~K, ~V, R.rh.take.lo(~K, ~V, r, hi)), R.RhTree.get(~K, ~V, tk.rest(~K, ~V, R.rh.take.lo(~K, ~V, r, hi)), Con{True{}, q})) : List<&2, R.RhEntry<K, V>>}:
  match r:
    case R.RhTake{+tp, es, +rest}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.rh.prune(~K, ~V, rest, hi), Con{True{}, q}), R.RhTree.get(~K, ~V, R.RhNode{rest, hi}, Con{True{}, q}), get_prune(~K, ~V, rest, hi, Con{True{}, q})) : {R.RhTree.get(~K, ~V, hi, q) == _ : List<&2, R.RhEntry<K, V>>}
      {==}

def tk1.hi_same(~K: Data, ~V: Data, +lo: R.RhTree<K, V>, -hi: R.RhTree<K, V>, r: R.RhTake<K, V>, +q: List<&2, Bool>, ih: {R.RhTree.get(~K, ~V, hi, q) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, r), q), tk.es(~K, ~V, r), R.RhTree.get(~K, ~V, tk.rest(~K, ~V, r), q)) : List<&2, R.RhEntry<K, V>>}) -> {R.RhTree.get(~K, ~V, R.RhNode{lo, hi}, Con{True{}, q}) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, R.rh.take.hi(~K, ~V, lo, r)), Con{True{}, q}), tk.es(~K, ~V, R.rh.take.hi(~K, ~V, lo, r)), R.RhTree.get(~K, ~V, tk.rest(~K, ~V, R.rh.take.hi(~K, ~V, lo, r)), Con{True{}, q})) : List<&2, R.RhEntry<K, V>>}:
  match r:
    case R.RhTake{+tp, es, +rest}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.rh.prune(~K, ~V, lo, rest), Con{True{}, q}), R.RhTree.get(~K, ~V, R.RhNode{lo, rest}, Con{True{}, q}), get_prune(~K, ~V, lo, rest, Con{True{}, q})) : {R.RhTree.get(~K, ~V, hi, q) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tp, q), es, _) : List<&2, R.RhEntry<K, V>>}
      ih

def tk1.hi_other_f(~K: Data, ~V: Data, +lo: R.RhTree<K, V>, -hi: R.RhTree<K, V>, r: R.RhTake<K, V>, +q: List<&2, Bool>) -> {R.RhTree.get(~K, ~V, R.RhNode{lo, hi}, Con{False{}, q}) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, R.rh.take.hi(~K, ~V, lo, r)), Con{False{}, q}), tk.es(~K, ~V, R.rh.take.hi(~K, ~V, lo, r)), R.RhTree.get(~K, ~V, tk.rest(~K, ~V, R.rh.take.hi(~K, ~V, lo, r)), Con{False{}, q})) : List<&2, R.RhEntry<K, V>>}:
  match r:
    case R.RhTake{+tp, es, +rest}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.rh.prune(~K, ~V, lo, rest), Con{False{}, q}), R.RhTree.get(~K, ~V, R.RhNode{lo, rest}, Con{False{}, q}), get_prune(~K, ~V, lo, rest, Con{False{}, q})) : {R.RhTree.get(~K, ~V, lo, q) == _ : List<&2, R.RhEntry<K, V>>}
      {==}

def tk1.hi_other_n(~K: Data, ~V: Data, +lo: R.RhTree<K, V>, -hi: R.RhTree<K, V>, r: R.RhTake<K, V>) -> {R.RhTree.get(~K, ~V, R.RhNode{lo, hi}, Nil{}) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, R.rh.take.hi(~K, ~V, lo, r)), Nil{}), tk.es(~K, ~V, R.rh.take.hi(~K, ~V, lo, r)), R.RhTree.get(~K, ~V, tk.rest(~K, ~V, R.rh.take.hi(~K, ~V, lo, r)), Nil{})) : List<&2, R.RhEntry<K, V>>}:
  match r:
    case R.RhTake{+tp, es, +rest}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.rh.prune(~K, ~V, lo, rest), Nil{}), R.RhTree.get(~K, ~V, R.RhNode{lo, rest}, Nil{}), get_prune(~K, ~V, lo, rest, Nil{})) : {R.RhTree.get(~K, ~V, lo, Nil{}) == _ : List<&2, R.RhEntry<K, V>>}
      {==}

def tk1(~K: Data, ~V: Data, t: R.RhTree<K, V>, +p: List<&2, Bool>, +q: List<&2, Bool>) -> {R.RhTree.get(~K, ~V, t, q) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, R.rh.take(~K, ~V, t, p)), q), tk.es(~K, ~V, R.rh.take(~K, ~V, t, p)), R.RhTree.get(~K, ~V, tk.rest(~K, ~V, R.rh.take(~K, ~V, t, p)), q)) : List<&2, R.RhEntry<K, V>>}:
  match t:
    case R.RhLeaf{es}:
      {==}
    case R.RhNode{+lo, +hi}:
      match p:
        case Nil{}:
          match q:
            case Nil{}:
              tk1.lo_nil(~K, ~V, lo, hi, R.rh.take(~K, ~V, lo, Nil{}), tk1(~K, ~V, lo, Nil{}, Nil{}))
            case Con{c, qs}:
              match c:
                case True{}:
                  tk1.lo_other(~K, ~V, lo, hi, R.rh.take(~K, ~V, lo, Nil{}), qs)
                case False{}:
                  tk1.lo_same(~K, ~V, lo, hi, R.rh.take(~K, ~V, lo, Nil{}), qs, tk1(~K, ~V, lo, Nil{}, qs))
        case Con{b, ps}:
          match b:
            case True{}:
              match q:
                case Nil{}:
                  tk1.hi_other_n(~K, ~V, lo, hi, R.rh.take(~K, ~V, hi, ps))
                case Con{c, qs}:
                  match c:
                    case True{}:
                      tk1.hi_same(~K, ~V, lo, hi, R.rh.take(~K, ~V, hi, ps), qs, tk1(~K, ~V, hi, ps, qs))
                    case False{}:
                      tk1.hi_other_f(~K, ~V, lo, hi, R.rh.take(~K, ~V, hi, ps), qs)
            case False{}:
              match q:
                case Nil{}:
                  tk1.lo_nil(~K, ~V, lo, hi, R.rh.take(~K, ~V, lo, ps), tk1(~K, ~V, lo, ps, Nil{}))
                case Con{c, qs}:
                  match c:
                    case True{}:
                      tk1.lo_other(~K, ~V, lo, hi, R.rh.take(~K, ~V, lo, ps), qs)
                    case False{}:
                      tk1.lo_same(~K, ~V, lo, hi, R.rh.take(~K, ~V, lo, ps), qs, tk1(~K, ~V, lo, ps, qs))

# (2) what is left has nothing where the path leads, and elsewhere what the
# tree had

def tk2.lo_same(~K: Data, ~V: Data, -lo: R.RhTree<K, V>, +hi: R.RhTree<K, V>, r: R.RhTake<K, V>, +q: List<&2, Bool>, ih: {R.RhTree.get(~K, ~V, tk.rest(~K, ~V, r), q) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, r), q), Nil{}, R.RhTree.get(~K, ~V, lo, q)) : List<&2, R.RhEntry<K, V>>}) -> {R.RhTree.get(~K, ~V, tk.rest(~K, ~V, R.rh.take.lo(~K, ~V, r, hi)), Con{False{}, q}) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, R.rh.take.lo(~K, ~V, r, hi)), Con{False{}, q}), Nil{}, R.RhTree.get(~K, ~V, R.RhNode{lo, hi}, Con{False{}, q})) : List<&2, R.RhEntry<K, V>>}:
  match r:
    case R.RhTake{+tp, es, +rest}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.rh.prune(~K, ~V, rest, hi), Con{False{}, q}), R.RhTree.get(~K, ~V, R.RhNode{rest, hi}, Con{False{}, q}), get_prune(~K, ~V, rest, hi, Con{False{}, q})) : {_ == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tp, q), Nil{}, R.RhTree.get(~K, ~V, lo, q)) : List<&2, R.RhEntry<K, V>>}
      ih

def tk2.lo_nil(~K: Data, ~V: Data, -lo: R.RhTree<K, V>, +hi: R.RhTree<K, V>, r: R.RhTake<K, V>, ih: {R.RhTree.get(~K, ~V, tk.rest(~K, ~V, r), Nil{}) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, r), Nil{}), Nil{}, R.RhTree.get(~K, ~V, lo, Nil{})) : List<&2, R.RhEntry<K, V>>}) -> {R.RhTree.get(~K, ~V, tk.rest(~K, ~V, R.rh.take.lo(~K, ~V, r, hi)), Nil{}) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, R.rh.take.lo(~K, ~V, r, hi)), Nil{}), Nil{}, R.RhTree.get(~K, ~V, R.RhNode{lo, hi}, Nil{})) : List<&2, R.RhEntry<K, V>>}:
  match r:
    case R.RhTake{+tp, es, +rest}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.rh.prune(~K, ~V, rest, hi), Nil{}), R.RhTree.get(~K, ~V, R.RhNode{rest, hi}, Nil{}), get_prune(~K, ~V, rest, hi, Nil{})) : {_ == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tp, Nil{}), Nil{}, R.RhTree.get(~K, ~V, lo, Nil{})) : List<&2, R.RhEntry<K, V>>}
      ih

def tk2.lo_other(~K: Data, ~V: Data, -lo: R.RhTree<K, V>, +hi: R.RhTree<K, V>, r: R.RhTake<K, V>, +q: List<&2, Bool>) -> {R.RhTree.get(~K, ~V, tk.rest(~K, ~V, R.rh.take.lo(~K, ~V, r, hi)), Con{True{}, q}) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, R.rh.take.lo(~K, ~V, r, hi)), Con{True{}, q}), Nil{}, R.RhTree.get(~K, ~V, R.RhNode{lo, hi}, Con{True{}, q})) : List<&2, R.RhEntry<K, V>>}:
  match r:
    case R.RhTake{+tp, es, +rest}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.rh.prune(~K, ~V, rest, hi), Con{True{}, q}), R.RhTree.get(~K, ~V, R.RhNode{rest, hi}, Con{True{}, q}), get_prune(~K, ~V, rest, hi, Con{True{}, q})) : {_ == R.RhTree.get(~K, ~V, hi, q) : List<&2, R.RhEntry<K, V>>}
      {==}

def tk2.hi_same(~K: Data, ~V: Data, +lo: R.RhTree<K, V>, -hi: R.RhTree<K, V>, r: R.RhTake<K, V>, +q: List<&2, Bool>, ih: {R.RhTree.get(~K, ~V, tk.rest(~K, ~V, r), q) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, r), q), Nil{}, R.RhTree.get(~K, ~V, hi, q)) : List<&2, R.RhEntry<K, V>>}) -> {R.RhTree.get(~K, ~V, tk.rest(~K, ~V, R.rh.take.hi(~K, ~V, lo, r)), Con{True{}, q}) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, R.rh.take.hi(~K, ~V, lo, r)), Con{True{}, q}), Nil{}, R.RhTree.get(~K, ~V, R.RhNode{lo, hi}, Con{True{}, q})) : List<&2, R.RhEntry<K, V>>}:
  match r:
    case R.RhTake{+tp, es, +rest}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.rh.prune(~K, ~V, lo, rest), Con{True{}, q}), R.RhTree.get(~K, ~V, R.RhNode{lo, rest}, Con{True{}, q}), get_prune(~K, ~V, lo, rest, Con{True{}, q})) : {_ == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tp, q), Nil{}, R.RhTree.get(~K, ~V, hi, q)) : List<&2, R.RhEntry<K, V>>}
      ih

def tk2.hi_other_f(~K: Data, ~V: Data, +lo: R.RhTree<K, V>, -hi: R.RhTree<K, V>, r: R.RhTake<K, V>, +q: List<&2, Bool>) -> {R.RhTree.get(~K, ~V, tk.rest(~K, ~V, R.rh.take.hi(~K, ~V, lo, r)), Con{False{}, q}) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, R.rh.take.hi(~K, ~V, lo, r)), Con{False{}, q}), Nil{}, R.RhTree.get(~K, ~V, R.RhNode{lo, hi}, Con{False{}, q})) : List<&2, R.RhEntry<K, V>>}:
  match r:
    case R.RhTake{+tp, es, +rest}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.rh.prune(~K, ~V, lo, rest), Con{False{}, q}), R.RhTree.get(~K, ~V, R.RhNode{lo, rest}, Con{False{}, q}), get_prune(~K, ~V, lo, rest, Con{False{}, q})) : {_ == R.RhTree.get(~K, ~V, lo, q) : List<&2, R.RhEntry<K, V>>}
      {==}

def tk2.hi_other_n(~K: Data, ~V: Data, +lo: R.RhTree<K, V>, -hi: R.RhTree<K, V>, r: R.RhTake<K, V>) -> {R.RhTree.get(~K, ~V, tk.rest(~K, ~V, R.rh.take.hi(~K, ~V, lo, r)), Nil{}) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, R.rh.take.hi(~K, ~V, lo, r)), Nil{}), Nil{}, R.RhTree.get(~K, ~V, R.RhNode{lo, hi}, Nil{})) : List<&2, R.RhEntry<K, V>>}:
  match r:
    case R.RhTake{+tp, es, +rest}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.rh.prune(~K, ~V, lo, rest), Nil{}), R.RhTree.get(~K, ~V, R.RhNode{lo, rest}, Nil{}), get_prune(~K, ~V, lo, rest, Nil{})) : {_ == R.RhTree.get(~K, ~V, lo, Nil{}) : List<&2, R.RhEntry<K, V>>}
      {==}

def tk2(~K: Data, ~V: Data, t: R.RhTree<K, V>, +p: List<&2, Bool>, +q: List<&2, Bool>) -> {R.RhTree.get(~K, ~V, tk.rest(~K, ~V, R.rh.take(~K, ~V, t, p)), q) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, R.rh.take(~K, ~V, t, p)), q), Nil{}, R.RhTree.get(~K, ~V, t, q)) : List<&2, R.RhEntry<K, V>>}:
  match t:
    case R.RhLeaf{es}:
      {==}
    case R.RhNode{+lo, +hi}:
      match p:
        case Nil{}:
          match q:
            case Nil{}:
              tk2.lo_nil(~K, ~V, lo, hi, R.rh.take(~K, ~V, lo, Nil{}), tk2(~K, ~V, lo, Nil{}, Nil{}))
            case Con{c, qs}:
              match c:
                case True{}:
                  tk2.lo_other(~K, ~V, lo, hi, R.rh.take(~K, ~V, lo, Nil{}), qs)
                case False{}:
                  tk2.lo_same(~K, ~V, lo, hi, R.rh.take(~K, ~V, lo, Nil{}), qs, tk2(~K, ~V, lo, Nil{}, qs))
        case Con{b, ps}:
          match b:
            case True{}:
              match q:
                case Nil{}:
                  tk2.hi_other_n(~K, ~V, lo, hi, R.rh.take(~K, ~V, hi, ps))
                case Con{c, qs}:
                  match c:
                    case True{}:
                      tk2.hi_same(~K, ~V, lo, hi, R.rh.take(~K, ~V, hi, ps), qs, tk2(~K, ~V, hi, ps, qs))
                    case False{}:
                      tk2.hi_other_f(~K, ~V, lo, hi, R.rh.take(~K, ~V, hi, ps), qs)
            case False{}:
              match q:
                case Nil{}:
                  tk2.lo_nil(~K, ~V, lo, hi, R.rh.take(~K, ~V, lo, ps), tk2(~K, ~V, lo, ps, Nil{}))
                case Con{c, qs}:
                  match c:
                    case True{}:
                      tk2.lo_other(~K, ~V, lo, hi, R.rh.take(~K, ~V, lo, ps), qs)
                    case False{}:
                      tk2.lo_same(~K, ~V, lo, hi, R.rh.take(~K, ~V, lo, ps), qs, tk2(~K, ~V, lo, ps, qs))

# ---------------------------------------------------------------- one array

def tab_ins_same(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +cur: R.RhTab<K, V>, +kw: List<&2, U32>, +k: K, +v: V) -> {R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, cur, kw, R.RhBIns{R.RhEntry{kw, k, v}}), kw) == Some{v} : Maybe<&2, V>}:
  match cur:
    case R.RhTab{+log, +seed, +tree}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.RhTree.put(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw), R.RhBIns{R.RhEntry{kw, k, v}}), R.RhTab.path(~hash, log, seed, kw)), R.rh.apply(~K, ~V, R.RhBIns{R.RhEntry{kw, k, v}}, R.RhTree.get(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw))), get_put_same(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw), R.RhBIns{R.RhEntry{kw, k, v}})) : {R.rh.find(~K, ~V, kw, _) == Some{v} : Maybe<&2, V>}
      find_cons_same(~K, ~V, kw, k, v, R.rh.drop(~K, ~V, kw, R.RhTree.get(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw))))

def tab_del_same(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +cur: R.RhTab<K, V>, +kw: List<&2, U32>) -> {R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, cur, kw, R.RhBDel{kw}), kw) == None{} : Maybe<&2, V>}:
  match cur:
    case R.RhTab{+log, +seed, +tree}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.RhTree.put(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw), R.RhBDel{kw}), R.RhTab.path(~hash, log, seed, kw)), R.rh.apply(~K, ~V, R.RhBDel{kw}, R.RhTree.get(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw))), get_put_same(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw), R.RhBDel{kw})) : {R.rh.find(~K, ~V, kw, _) == None{} : Maybe<&2, V>}
      find_drop_same(~K, ~V, kw, R.RhTree.get(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw)))

def tab_frame(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +cur: R.RhTab<K, V>, +kw: List<&2, U32>, +jw: List<&2, U32>, +op: R.RhBop<K, V>, h: @l: List<&2, R.RhEntry<K, V>> -> {R.rh.find(~K, ~V, jw, R.rh.apply(~K, ~V, op, l)) == R.rh.find(~K, ~V, jw, l) : Maybe<&2, V>}) -> {R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, cur, kw, op), jw) == R.RhTab.find(~K, ~V, ~hash, cur, jw) : Maybe<&2, V>}:
  match cur:
    case R.RhTab{+log, +seed, +tree}:
      frame(~K, ~V, jw, tree, R.RhTab.path(~hash, log, seed, kw), R.RhTab.path(~hash, log, seed, jw), op, h)

def find_snoc_other(~K: Data, ~V: Data, +kw: List<&2, U32>, +l: List<&2, R.RhEntry<K, V>>, +w: List<&2, U32>, +k: K, +v: V, +ne: {R.rh.weq(kw, w) == False{} : Bool}) -> {R.rh.find(~K, ~V, kw, R.rh.snoc(~K, ~V, l, R.RhEntry{w, k, v})) == R.rh.find(~K, ~V, kw, l) : Maybe<&2, V>}:
  %Equal.sym(Maybe<&2, V>, R.rh.find(~K, ~V, kw, R.rh.snoc(~K, ~V, l, R.RhEntry{w, k, v})), R.rh.orelse(~V, R.rh.find(~K, ~V, kw, l), R.rh.hit(~V, R.rh.weq(kw, w), v, None{})), find_snoc(~K, ~V, kw, l, w, k, v)) : {_ == R.rh.find(~K, ~V, kw, l) : Maybe<&2, V>}
  %Equal.sym(Bool, R.rh.weq(kw, w), False{}, ne) : {R.rh.orelse(~V, R.rh.find(~K, ~V, kw, l), R.rh.hit(~V, _, v, None{})) == R.rh.find(~K, ~V, kw, l) : Maybe<&2, V>}
  orelse_none(~K, ~V, R.rh.find(~K, ~V, kw, l))

# ---------------------------------------------------------------- insert and remove, before the resize work

def ins_same(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +present: Bool, +t: R.RHash<K, V>, +kw: List<&2, U32>, +k: K, +v: V) -> {R.rh.lookup(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, present, t, kw, k, v), kw) == Some{v} : Maybe<&2, V>}:
  match t:
    case R.RHash{p, n, cur, old, c}:
      %Equal.sym(Maybe<&2, V>, R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, cur, kw, R.RhBIns{R.RhEntry{kw, k, v}}), kw), Some{v}, tab_ins_same(~K, ~V, ~hash, cur, kw, k, v)) : {R.rh.orelse(~V, _, R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, old, kw, R.RhBDel{kw}), kw)) == Some{v} : Maybe<&2, V>}
      {==}

def ins_other(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +present: Bool, +t: R.RHash<K, V>, +kw: List<&2, U32>, +k: K, +v: V, +jw: List<&2, U32>, +ne: {R.rh.weq(kw, jw) == False{} : Bool}) -> {R.rh.lookup(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, present, t, kw, k, v), jw) == R.rh.lookup(~K, ~V, ~hash, t, jw) : Maybe<&2, V>}:
  match t:
    case R.RHash{p, n, +cur, +old, c}:
      +ne2 = weq_false_sym(kw, jw, ne)
      %tab_frame(~K, ~V, ~hash, cur, kw, jw, R.RhBIns{R.RhEntry{kw, k, v}}, l => Equal.trans(Maybe<&2, V>, R.rh.find(~K, ~V, jw, Con{R.RhEntry{kw, k, v}, R.rh.drop(~K, ~V, kw, l)}), R.rh.find(~K, ~V, jw, R.rh.drop(~K, ~V, kw, l)), R.rh.find(~K, ~V, jw, l), find_cons_other(~K, ~V, jw, kw, ne2, k, v, R.rh.drop(~K, ~V, kw, l)), find_drop_other(~K, ~V, kw, jw, ne2, l))) : {R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, cur, kw, R.RhBIns{R.RhEntry{kw, k, v}}), jw), R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, old, kw, R.RhBDel{kw}), jw)) == R.rh.orelse(~V, _, R.RhTab.find(~K, ~V, ~hash, old, jw)) : Maybe<&2, V>}
      %tab_frame(~K, ~V, ~hash, old, kw, jw, R.RhBDel{kw}, l => find_drop_other(~K, ~V, kw, jw, ne2, l)) : {R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, cur, kw, R.RhBIns{R.RhEntry{kw, k, v}}), jw), R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, old, kw, R.RhBDel{kw}), jw)) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, cur, kw, R.RhBIns{R.RhEntry{kw, k, v}}), jw), _) : Maybe<&2, V>}
      {==}

def del_same(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +present: Bool, +t: R.RHash<K, V>, +kw: List<&2, U32>) -> {R.rh.lookup(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, present, t, kw), kw) == None{} : Maybe<&2, V>}:
  match t:
    case R.RHash{p, n, cur, old, c}:
      %Equal.sym(Maybe<&2, V>, R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, cur, kw, R.RhBDel{kw}), kw), None{}, tab_del_same(~K, ~V, ~hash, cur, kw)) : {R.rh.orelse(~V, _, R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, old, kw, R.RhBDel{kw}), kw)) == None{} : Maybe<&2, V>}
      tab_del_same(~K, ~V, ~hash, old, kw)

def del_other(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +present: Bool, +t: R.RHash<K, V>, +kw: List<&2, U32>, +jw: List<&2, U32>, +ne: {R.rh.weq(kw, jw) == False{} : Bool}) -> {R.rh.lookup(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, present, t, kw), jw) == R.rh.lookup(~K, ~V, ~hash, t, jw) : Maybe<&2, V>}:
  match t:
    case R.RHash{p, n, +cur, +old, c}:
      +ne2 = weq_false_sym(kw, jw, ne)
      %tab_frame(~K, ~V, ~hash, cur, kw, jw, R.RhBDel{kw}, l => find_drop_other(~K, ~V, kw, jw, ne2, l)) : {R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, cur, kw, R.RhBDel{kw}), jw), R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, old, kw, R.RhBDel{kw}), jw)) == R.rh.orelse(~V, _, R.RhTab.find(~K, ~V, ~hash, old, jw)) : Maybe<&2, V>}
      %tab_frame(~K, ~V, ~hash, old, kw, jw, R.RhBDel{kw}, l => find_drop_other(~K, ~V, kw, jw, ne2, l)) : {R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, cur, kw, R.RhBDel{kw}), jw), R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, old, kw, R.RhBDel{kw}), jw)) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.RhTab.put(~K, ~V, ~hash, cur, kw, R.RhBDel{kw}), jw), _) : Maybe<&2, V>}
      {==}

def size_ins(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +present: Bool, +t: R.RHash<K, V>, -kw: List<&2, U32>, +k: K, +v: V) -> {R.RHash.size(~K, ~V, R.rh.ins(~K, ~V, ~hash, present, t, kw, k, v)) == R.rh.bump(present, R.RHash.size(~K, ~V, t)) : Nat}:
  match t:
    case R.RHash{p, n, cur, old, c}:
      {==}

def size_del(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +present: Bool, +t: R.RHash<K, V>, -kw: List<&2, U32>) -> {R.RHash.size(~K, ~V, R.rh.del(~K, ~V, ~hash, present, t, kw)) == R.rh.unbump(present, R.RHash.size(~K, ~V, t)) : Nat}:
  match t:
    case R.RHash{p, n, cur, old, c}:
      {==}

# ---------------------------------------------------------------- migration keeps every lookup

def m1o.go(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +kw: List<&2, U32>, +tp: List<&2, Bool>, +olog: Nat, +oseed: U32, +cur: R.RhTab<K, V>, +w: List<&2, U32>, +k: K, +v: V, +ne: {R.rh.weq(kw, w) == False{} : Bool}, b: Bool, +eb: {R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, w)) == b : Bool}) -> {R.RhTab.find(~K, ~V, ~hash, R.rh.mig1.go(~K, ~V, ~hash, R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, w)), cur, R.RhEntry{w, k, v}), kw) == R.RhTab.find(~K, ~V, ~hash, cur, kw) : Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(Bool, R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, w)), True{}, eb) : {R.RhTab.find(~K, ~V, ~hash, R.rh.mig1.go(~K, ~V, ~hash, _, cur, R.RhEntry{w, k, v}), kw) == R.RhTab.find(~K, ~V, ~hash, cur, kw) : Maybe<&2, V>}
      tab_frame(~K, ~V, ~hash, cur, w, kw, R.RhBApp{R.RhEntry{w, k, v}}, l => find_snoc_other(~K, ~V, kw, l, w, k, v, ne))
    case False{}:
      %Equal.sym(Bool, R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, w)), False{}, eb) : {R.RhTab.find(~K, ~V, ~hash, R.rh.mig1.go(~K, ~V, ~hash, _, cur, R.RhEntry{w, k, v}), kw) == R.RhTab.find(~K, ~V, ~hash, cur, kw) : Maybe<&2, V>}
      {==}

# an entry of another key moved into the current array leaves this key
def mig1_other(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +kw: List<&2, U32>, +tp: List<&2, Bool>, +olog: Nat, +oseed: U32, +cur: R.RhTab<K, V>, +w: List<&2, U32>, +k: K, +v: V, +ne: {R.rh.weq(kw, w) == False{} : Bool}) -> {R.RhTab.find(~K, ~V, ~hash, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, R.RhEntry{w, k, v}), kw) == R.RhTab.find(~K, ~V, ~hash, cur, kw) : Maybe<&2, V>}:
  m1o.go(~K, ~V, ~hash, kw, tp, olog, oseed, cur, w, k, v, ne, R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, w)), {==})

# an entry of this key, from the bucket taken, goes after the current
# array's own entries for it
def mig1_same(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +kw: List<&2, U32>, +tp: List<&2, Bool>, +olog: Nat, +oseed: U32, +cur: R.RhTab<K, V>, +k: K, +v: V, +hf: {R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)) == True{} : Bool}) -> {R.RhTab.find(~K, ~V, ~hash, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, R.RhEntry{kw, k, v}), kw) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), Some{v}) : Maybe<&2, V>}:
  match cur:
    case R.RhTab{+log, +seed, +tree}:
      %Equal.sym(Bool, R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)), True{}, hf) : {R.RhTab.find(~K, ~V, ~hash, R.rh.mig1.go(~K, ~V, ~hash, _, R.RhTab{log, seed, tree}, R.RhEntry{kw, k, v}), kw) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.RhTab{log, seed, tree}, kw), Some{v}) : Maybe<&2, V>}
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.RhTree.put(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw), R.RhBApp{R.RhEntry{kw, k, v}}), R.RhTab.path(~hash, log, seed, kw)), R.rh.apply(~K, ~V, R.RhBApp{R.RhEntry{kw, k, v}}, R.RhTree.get(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw))), get_put_same(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw), R.RhBApp{R.RhEntry{kw, k, v}})) : {R.rh.find(~K, ~V, kw, _) == R.rh.orelse(~V, R.rh.find(~K, ~V, kw, R.RhTree.get(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw))), Some{v}) : Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, R.rh.find(~K, ~V, kw, R.rh.snoc(~K, ~V, R.RhTree.get(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw)), R.RhEntry{kw, k, v})), R.rh.orelse(~V, R.rh.find(~K, ~V, kw, R.RhTree.get(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw))), R.rh.hit(~V, R.rh.weq(kw, kw), v, None{})), find_snoc(~K, ~V, kw, R.RhTree.get(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw)), kw, k, v)) : {_ == R.rh.orelse(~V, R.rh.find(~K, ~V, kw, R.RhTree.get(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw))), Some{v}) : Maybe<&2, V>}
      %Equal.sym(Bool, R.rh.weq(kw, kw), True{}, weq_self(kw)) : {R.rh.orelse(~V, R.rh.find(~K, ~V, kw, R.RhTree.get(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw))), R.rh.hit(~V, _, v, None{})) == R.rh.orelse(~V, R.rh.find(~K, ~V, kw, R.RhTree.get(~K, ~V, tree, R.RhTab.path(~hash, log, seed, kw))), Some{v}) : Maybe<&2, V>}
      {==}

def mt.go(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +kw: List<&2, U32>, +tp: List<&2, Bool>, +olog: Nat, +oseed: U32, +cur: R.RhTab<K, V>, +w: List<&2, U32>, +k: K, +v: V, +t: List<&2, R.RhEntry<K, V>>, +hf: {R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)) == True{} : Bool}, b: Bool, +eb: {R.rh.weq(kw, w) == b : Bool}) -> {R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, R.RhEntry{w, k, v}), kw), R.rh.find(~K, ~V, kw, t)) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.rh.hit(~V, R.rh.weq(kw, w), v, R.rh.find(~K, ~V, kw, t))) : Maybe<&2, V>}:
  match b:
    case True{}:
      %weq_sound(kw, w, eb) : {R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, R.RhEntry{_, k, v}), kw), R.rh.find(~K, ~V, kw, t)) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.rh.hit(~V, R.rh.weq(kw, _), v, R.rh.find(~K, ~V, kw, t))) : Maybe<&2, V>}
      %Equal.sym(Bool, R.rh.weq(kw, kw), True{}, weq_self(kw)) : {R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, R.RhEntry{kw, k, v}), kw), R.rh.find(~K, ~V, kw, t)) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.rh.hit(~V, _, v, R.rh.find(~K, ~V, kw, t))) : Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, R.RhTab.find(~K, ~V, ~hash, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, R.RhEntry{kw, k, v}), kw), R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), Some{v}), mig1_same(~K, ~V, ~hash, kw, tp, olog, oseed, cur, k, v, hf)) : {R.rh.orelse(~V, _, R.rh.find(~K, ~V, kw, t)) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), Some{v}) : Maybe<&2, V>}
      orelse_some(~K, ~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), v, R.rh.find(~K, ~V, kw, t))
    case False{}:
      %Equal.sym(Bool, R.rh.weq(kw, w), False{}, eb) : {R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, R.RhEntry{w, k, v}), kw), R.rh.find(~K, ~V, kw, t)) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.rh.hit(~V, _, v, R.rh.find(~K, ~V, kw, t))) : Maybe<&2, V>}
      %mig1_other(~K, ~V, ~hash, kw, tp, olog, oseed, cur, w, k, v, eb) : {R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, R.RhEntry{w, k, v}), kw), R.rh.find(~K, ~V, kw, t)) == R.rh.orelse(~V, _, R.rh.find(~K, ~V, kw, t)) : Maybe<&2, V>}
      {==}

# when this key's old bucket is the one taken: its value is the current
# array's, and failing that the bucket's
def mig_true(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, es: List<&2, R.RhEntry<K, V>>, +kw: List<&2, U32>, +tp: List<&2, Bool>, +olog: Nat, +oseed: U32, +cur: R.RhTab<K, V>, +hf: {R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)) == True{} : Bool}) -> {R.RhTab.find(~K, ~V, ~hash, R.rh.mig(~K, ~V, ~hash, es, tp, olog, oseed, cur), kw) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.rh.find(~K, ~V, kw, es)) : Maybe<&2, V>}:
  match es:
    case Nil{}:
      Equal.sym(Maybe<&2, V>, R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), None{}), R.RhTab.find(~K, ~V, ~hash, cur, kw), orelse_none(~K, ~V, R.RhTab.find(~K, ~V, ~hash, cur, kw)))
    case Con{e, +t}:
      match e:
        case R.RhEntry{+w, +k, +v}:
          %Equal.sym(Maybe<&2, V>, R.RhTab.find(~K, ~V, ~hash, R.rh.mig(~K, ~V, ~hash, t, tp, olog, oseed, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, R.RhEntry{w, k, v})), kw), R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, R.RhEntry{w, k, v}), kw), R.rh.find(~K, ~V, kw, t)), mig_true(~K, ~V, ~hash, t, kw, tp, olog, oseed, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, R.RhEntry{w, k, v}), hf)) : {_ == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.rh.hit(~V, R.rh.weq(kw, w), v, R.rh.find(~K, ~V, kw, t))) : Maybe<&2, V>}
          mt.go(~K, ~V, ~hash, kw, tp, olog, oseed, cur, w, k, v, t, hf, R.rh.weq(kw, w), {==})

def mf.go(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +kw: List<&2, U32>, +tp: List<&2, Bool>, +olog: Nat, +oseed: U32, +cur: R.RhTab<K, V>, +w: List<&2, U32>, +k: K, +v: V, +hf: {R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)) == False{} : Bool}, b: Bool, +eb: {R.rh.weq(kw, w) == b : Bool}) -> {R.RhTab.find(~K, ~V, ~hash, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, R.RhEntry{w, k, v}), kw) == R.RhTab.find(~K, ~V, ~hash, cur, kw) : Maybe<&2, V>}:
  match b:
    case True{}:
      %weq_sound(kw, w, eb) : {R.RhTab.find(~K, ~V, ~hash, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, R.RhEntry{_, k, v}), kw) == R.RhTab.find(~K, ~V, ~hash, cur, kw) : Maybe<&2, V>}
      %Equal.sym(Bool, R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)), False{}, hf) : {R.RhTab.find(~K, ~V, ~hash, R.rh.mig1.go(~K, ~V, ~hash, _, cur, R.RhEntry{kw, k, v}), kw) == R.RhTab.find(~K, ~V, ~hash, cur, kw) : Maybe<&2, V>}
      {==}
    case False{}:
      mig1_other(~K, ~V, ~hash, kw, tp, olog, oseed, cur, w, k, v, eb)

# when this key's old bucket is not the one taken: the current array's
# value for it does not change
def mig_false(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, es: List<&2, R.RhEntry<K, V>>, +kw: List<&2, U32>, +tp: List<&2, Bool>, +olog: Nat, +oseed: U32, +cur: R.RhTab<K, V>, +hf: {R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)) == False{} : Bool}) -> {R.RhTab.find(~K, ~V, ~hash, R.rh.mig(~K, ~V, ~hash, es, tp, olog, oseed, cur), kw) == R.RhTab.find(~K, ~V, ~hash, cur, kw) : Maybe<&2, V>}:
  match es:
    case Nil{}:
      {==}
    case Con{e, +t}:
      match e:
        case R.RhEntry{+w, +k, +v}:
          Equal.trans(Maybe<&2, V>, R.RhTab.find(~K, ~V, ~hash, R.rh.mig(~K, ~V, ~hash, t, tp, olog, oseed, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, R.RhEntry{w, k, v})), kw), R.RhTab.find(~K, ~V, ~hash, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, R.RhEntry{w, k, v}), kw), R.RhTab.find(~K, ~V, ~hash, cur, kw), mig_false(~K, ~V, ~hash, t, kw, tp, olog, oseed, R.rh.mig1(~K, ~V, ~hash, tp, olog, oseed, cur, R.RhEntry{w, k, v}), hf), mf.go(~K, ~V, ~hash, kw, tp, olog, oseed, cur, w, k, v, hf, R.rh.weq(kw, w), {==}))

# ---------------------------------------------------------------- a step, steps, starting a resize, the policy

def st.f(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +kw: List<&2, U32>, +cur: R.RhTab<K, V>, +olog: Nat, +oseed: U32, +otree: R.RhTree<K, V>, +tp: List<&2, Bool>, +es: List<&2, R.RhEntry<K, V>>, +rest: R.RhTree<K, V>, f1: {R.RhTree.get(~K, ~V, otree, R.RhTab.path(~hash, olog, oseed, kw)) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)), es, R.RhTree.get(~K, ~V, rest, R.RhTab.path(~hash, olog, oseed, kw))) : List<&2, R.RhEntry<K, V>>}, f2: {R.RhTree.get(~K, ~V, rest, R.RhTab.path(~hash, olog, oseed, kw)) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)), Nil{}, R.RhTree.get(~K, ~V, otree, R.RhTab.path(~hash, olog, oseed, kw))) : List<&2, R.RhEntry<K, V>>}, b: Bool, +eb: {R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)) == b : Bool}) -> {R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.rh.mig(~K, ~V, ~hash, es, tp, olog, oseed, cur), kw), R.rh.find(~K, ~V, kw, R.RhTree.get(~K, ~V, rest, R.RhTab.path(~hash, olog, oseed, kw)))) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.rh.find(~K, ~V, kw, R.RhTree.get(~K, ~V, otree, R.RhTab.path(~hash, olog, oseed, kw)))) : Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, otree, R.RhTab.path(~hash, olog, oseed, kw)), Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)), es, R.RhTree.get(~K, ~V, rest, R.RhTab.path(~hash, olog, oseed, kw))), f1) : {R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.rh.mig(~K, ~V, ~hash, es, tp, olog, oseed, cur), kw), R.rh.find(~K, ~V, kw, R.RhTree.get(~K, ~V, rest, R.RhTab.path(~hash, olog, oseed, kw)))) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.rh.find(~K, ~V, kw, _)) : Maybe<&2, V>}
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, rest, R.RhTab.path(~hash, olog, oseed, kw)), Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)), Nil{}, R.RhTree.get(~K, ~V, otree, R.RhTab.path(~hash, olog, oseed, kw))), f2) : {R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.rh.mig(~K, ~V, ~hash, es, tp, olog, oseed, cur), kw), R.rh.find(~K, ~V, kw, _)) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.rh.find(~K, ~V, kw, Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)), es, R.RhTree.get(~K, ~V, rest, R.RhTab.path(~hash, olog, oseed, kw))))) : Maybe<&2, V>}
      %Equal.sym(Bool, R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)), True{}, eb) : {R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.rh.mig(~K, ~V, ~hash, es, tp, olog, oseed, cur), kw), R.rh.find(~K, ~V, kw, Bool.pick(List<&2, R.RhEntry<K, V>>, _, Nil{}, R.RhTree.get(~K, ~V, otree, R.RhTab.path(~hash, olog, oseed, kw))))) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.rh.find(~K, ~V, kw, Bool.pick(List<&2, R.RhEntry<K, V>>, _, es, R.RhTree.get(~K, ~V, rest, R.RhTab.path(~hash, olog, oseed, kw))))) : Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.rh.mig(~K, ~V, ~hash, es, tp, olog, oseed, cur), kw), None{}), R.RhTab.find(~K, ~V, ~hash, R.rh.mig(~K, ~V, ~hash, es, tp, olog, oseed, cur), kw), orelse_none(~K, ~V, R.RhTab.find(~K, ~V, ~hash, R.rh.mig(~K, ~V, ~hash, es, tp, olog, oseed, cur), kw))) : {_ == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.rh.find(~K, ~V, kw, es)) : Maybe<&2, V>}
      mig_true(~K, ~V, ~hash, es, kw, tp, olog, oseed, cur, eb)
    case False{}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, rest, R.RhTab.path(~hash, olog, oseed, kw)), Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)), Nil{}, R.RhTree.get(~K, ~V, otree, R.RhTab.path(~hash, olog, oseed, kw))), f2) : {R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.rh.mig(~K, ~V, ~hash, es, tp, olog, oseed, cur), kw), R.rh.find(~K, ~V, kw, _)) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.rh.find(~K, ~V, kw, R.RhTree.get(~K, ~V, otree, R.RhTab.path(~hash, olog, oseed, kw)))) : Maybe<&2, V>}
      %Equal.sym(Bool, R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)), False{}, eb) : {R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.rh.mig(~K, ~V, ~hash, es, tp, olog, oseed, cur), kw), R.rh.find(~K, ~V, kw, Bool.pick(List<&2, R.RhEntry<K, V>>, _, Nil{}, R.RhTree.get(~K, ~V, otree, R.RhTab.path(~hash, olog, oseed, kw))))) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.rh.find(~K, ~V, kw, R.RhTree.get(~K, ~V, otree, R.RhTab.path(~hash, olog, oseed, kw)))) : Maybe<&2, V>}
      %mig_false(~K, ~V, ~hash, es, kw, tp, olog, oseed, cur, eb) : {R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, R.rh.mig(~K, ~V, ~hash, es, tp, olog, oseed, cur), kw), R.rh.find(~K, ~V, kw, R.RhTree.get(~K, ~V, otree, R.RhTab.path(~hash, olog, oseed, kw)))) == R.rh.orelse(~V, _, R.rh.find(~K, ~V, kw, R.RhTree.get(~K, ~V, otree, R.RhTab.path(~hash, olog, oseed, kw)))) : Maybe<&2, V>}
      {==}

def st.take(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +kw: List<&2, U32>, -p: R.RhParams, -n: Nat, +cur: R.RhTab<K, V>, +olog: Nat, +oseed: U32, -c: U32, +otree: R.RhTree<K, V>, r: R.RhTake<K, V>, f1: {R.RhTree.get(~K, ~V, otree, R.RhTab.path(~hash, olog, oseed, kw)) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, r), R.RhTab.path(~hash, olog, oseed, kw)), tk.es(~K, ~V, r), R.RhTree.get(~K, ~V, tk.rest(~K, ~V, r), R.RhTab.path(~hash, olog, oseed, kw))) : List<&2, R.RhEntry<K, V>>}, f2: {R.RhTree.get(~K, ~V, tk.rest(~K, ~V, r), R.RhTab.path(~hash, olog, oseed, kw)) == Bool.pick(List<&2, R.RhEntry<K, V>>, R.rh.follows(tk.path(~K, ~V, r), R.RhTab.path(~hash, olog, oseed, kw)), Nil{}, R.RhTree.get(~K, ~V, otree, R.RhTab.path(~hash, olog, oseed, kw))) : List<&2, R.RhEntry<K, V>>}) -> {R.rh.lookup(~K, ~V, ~hash, R.rh.step.take(~K, ~V, ~hash, p, n, cur, olog, oseed, c, r), kw) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.RhTab.find(~K, ~V, ~hash, R.RhTab{olog, oseed, otree}, kw)) : Maybe<&2, V>}:
  match r:
    case R.RhTake{+tp, +es, +rest}:
      st.f(~K, ~V, ~hash, kw, cur, olog, oseed, otree, tp, es, rest, f1, f2, R.rh.follows(tp, R.RhTab.path(~hash, olog, oseed, kw)), {==})

def st.go(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +kw: List<&2, U32>, +p: R.RhParams, +n: Nat, +cur: R.RhTab<K, V>, +c: U32, b: Bool, +old: R.RhTab<K, V>, +eb: {R.rh.old_empty(~K, ~V, old) == b : Bool}) -> {R.rh.lookup(~K, ~V, ~hash, R.rh.step.go(~K, ~V, ~hash, R.rh.old_empty(~K, ~V, old), p, n, cur, old, c), kw) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.RhTab.find(~K, ~V, ~hash, old, kw)) : Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(Bool, R.rh.old_empty(~K, ~V, old), True{}, eb) : {R.rh.lookup(~K, ~V, ~hash, R.rh.step.go(~K, ~V, ~hash, _, p, n, cur, old, c), kw) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.RhTab.find(~K, ~V, ~hash, old, kw)) : Maybe<&2, V>}
      {==}
    case False{}:
      match old:
        case R.RhTab{+olog, +oseed, +otree}:
          %Equal.sym(Bool, R.rh.old_empty(~K, ~V, R.RhTab{olog, oseed, otree}), False{}, eb) : {R.rh.lookup(~K, ~V, ~hash, R.rh.step.go(~K, ~V, ~hash, _, p, n, cur, R.RhTab{olog, oseed, otree}, c), kw) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.RhTab.find(~K, ~V, ~hash, R.RhTab{olog, oseed, otree}, kw)) : Maybe<&2, V>}
          st.take(~K, ~V, ~hash, kw, p, n, cur, olog, oseed, c, otree, R.rh.take(~K, ~V, otree, R.rh.path(olog, c)), tk1(~K, ~V, otree, R.rh.path(olog, c), R.RhTab.path(~hash, olog, oseed, kw)), tk2(~K, ~V, otree, R.rh.path(olog, c), R.RhTab.path(~hash, olog, oseed, kw)))

# one migration step changes no lookup
def step_lookup(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, t: R.RHash<K, V>, +kw: List<&2, U32>) -> {R.rh.lookup(~K, ~V, ~hash, R.rh.step(~K, ~V, ~hash, t), kw) == R.rh.lookup(~K, ~V, ~hash, t, kw) : Maybe<&2, V>}:
  match t:
    case R.RHash{+p, +n, +cur, +old, +c}:
      st.go(~K, ~V, ~hash, kw, p, n, cur, c, R.rh.old_empty(~K, ~V, old), old, {==})

def steps_lookup(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, k: Nat, +t: R.RHash<K, V>, +kw: List<&2, U32>) -> {R.rh.lookup(~K, ~V, ~hash, R.rh.steps(~K, ~V, ~hash, k, t), kw) == R.rh.lookup(~K, ~V, ~hash, t, kw) : Maybe<&2, V>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.trans(Maybe<&2, V>, R.rh.lookup(~K, ~V, ~hash, R.rh.steps(~K, ~V, ~hash, j, R.rh.step(~K, ~V, ~hash, t)), kw), R.rh.lookup(~K, ~V, ~hash, R.rh.step(~K, ~V, ~hash, t), kw), R.rh.lookup(~K, ~V, ~hash, t, kw), steps_lookup(~K, ~V, ~hash, j, R.rh.step(~K, ~V, ~hash, t), kw), step_lookup(~K, ~V, ~hash, t, kw))

def sz.take(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +p: R.RhParams, +n: Nat, +cur: R.RhTab<K, V>, +olog: Nat, +oseed: U32, +c: U32, r: R.RhTake<K, V>) -> {R.RHash.size(~K, ~V, R.rh.step.take(~K, ~V, ~hash, p, n, cur, olog, oseed, c, r)) == n : Nat}:
  match r:
    case R.RhTake{tp, es, rest}:
      {==}

def sz.go(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +p: R.RhParams, +n: Nat, +cur: R.RhTab<K, V>, +c: U32, b: Bool, +old: R.RhTab<K, V>, +eb: {R.rh.old_empty(~K, ~V, old) == b : Bool}) -> {R.RHash.size(~K, ~V, R.rh.step.go(~K, ~V, ~hash, R.rh.old_empty(~K, ~V, old), p, n, cur, old, c)) == n : Nat}:
  match b:
    case True{}:
      %Equal.sym(Bool, R.rh.old_empty(~K, ~V, old), True{}, eb) : {R.RHash.size(~K, ~V, R.rh.step.go(~K, ~V, ~hash, _, p, n, cur, old, c)) == n : Nat}
      {==}
    case False{}:
      match old:
        case R.RhTab{+olog, +oseed, +otree}:
          %Equal.sym(Bool, R.rh.old_empty(~K, ~V, R.RhTab{olog, oseed, otree}), False{}, eb) : {R.RHash.size(~K, ~V, R.rh.step.go(~K, ~V, ~hash, _, p, n, cur, R.RhTab{olog, oseed, otree}, c)) == n : Nat}
          sz.take(~K, ~V, ~hash, p, n, cur, olog, oseed, c, R.rh.take(~K, ~V, otree, R.rh.path(olog, c)))

def step_size(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, t: R.RHash<K, V>) -> {R.RHash.size(~K, ~V, R.rh.step(~K, ~V, ~hash, t)) == R.RHash.size(~K, ~V, t) : Nat}:
  match t:
    case R.RHash{+p, +n, +cur, +old, +c}:
      sz.go(~K, ~V, ~hash, p, n, cur, c, R.rh.old_empty(~K, ~V, old), old, {==})

def steps_size(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, k: Nat, +t: R.RHash<K, V>) -> {R.RHash.size(~K, ~V, R.rh.steps(~K, ~V, ~hash, k, t)) == R.RHash.size(~K, ~V, t) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.trans(Nat, R.RHash.size(~K, ~V, R.rh.steps(~K, ~V, ~hash, j, R.rh.step(~K, ~V, ~hash, t))), R.RHash.size(~K, ~V, R.rh.step(~K, ~V, ~hash, t)), R.RHash.size(~K, ~V, t), steps_size(~K, ~V, ~hash, j, R.rh.step(~K, ~V, ~hash, t)), step_size(~K, ~V, ~hash, t))

def empty_find(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, old: R.RhTab<K, V>, +kw: List<&2, U32>, e: {R.rh.old_empty(~K, ~V, old) == True{} : Bool}) -> {R.RhTab.find(~K, ~V, ~hash, old, kw) == None{} : Maybe<&2, V>}:
  match old:
    case R.RhTab{log, seed, tree}:
      match tree:
        case R.RhLeaf{es}:
          match es:
            case Nil{}:
              {==}
            case Con{x, xs}:
              Empty.absurd({R.RhTab.find(~K, ~V, ~hash, R.RhTab{log, seed, R.RhLeaf{Con{x, xs}}}, kw) == None{} : Maybe<&2, V>}, ab.ft(e))
        case R.RhNode{lo, hi}:
          Empty.absurd({R.RhTab.find(~K, ~V, ~hash, R.RhTab{log, seed, R.RhNode{lo, hi}}, kw) == None{} : Maybe<&2, V>}, ab.ft(e))

def sa.go(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +kw: List<&2, U32>, +p: R.RhParams, +n: Nat, +cur: R.RhTab<K, V>, +c: U32, +log: Nat, +seed: U32, b: Bool, +old: R.RhTab<K, V>, +eb: {R.rh.old_empty(~K, ~V, old) == b : Bool}) -> {R.rh.lookup(~K, ~V, ~hash, R.rh.start.go(~K, ~V, b, R.RHash{p, n, cur, old, c}, log, seed), kw) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.RhTab.find(~K, ~V, ~hash, old, kw)) : Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.RhTree.full(~K, ~V, log), R.RhTab.path(~hash, log, seed, kw)), Nil{}, get_full(~K, ~V, log, R.RhTab.path(~hash, log, seed, kw))) : {R.rh.orelse(~V, R.rh.find(~K, ~V, kw, _), R.RhTab.find(~K, ~V, ~hash, cur, kw)) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), R.RhTab.find(~K, ~V, ~hash, old, kw)) : Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, R.RhTab.find(~K, ~V, ~hash, old, kw), None{}, empty_find(~K, ~V, ~hash, old, kw, eb)) : {R.RhTab.find(~K, ~V, ~hash, cur, kw) == R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), _) : Maybe<&2, V>}
      Equal.sym(Maybe<&2, V>, R.rh.orelse(~V, R.RhTab.find(~K, ~V, ~hash, cur, kw), None{}), R.RhTab.find(~K, ~V, ~hash, cur, kw), orelse_none(~K, ~V, R.RhTab.find(~K, ~V, ~hash, cur, kw)))
    case False{}:
      {==}

# starting a resize changes no lookup
def start_lookup(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, t: R.RHash<K, V>, +log: Nat, +seed: U32, +kw: List<&2, U32>) -> {R.rh.lookup(~K, ~V, ~hash, R.rh.start(~K, ~V, t, log, seed), kw) == R.rh.lookup(~K, ~V, ~hash, t, kw) : Maybe<&2, V>}:
  match t:
    case R.RHash{+p, +n, +cur, +old, +c}:
      sa.go(~K, ~V, ~hash, kw, p, n, cur, c, log, seed, R.rh.old_empty(~K, ~V, old), old, {==})

def ss.go(~K: Data, ~V: Data, +p: R.RhParams, +n: Nat, +cur: R.RhTab<K, V>, +c: U32, +log: Nat, +seed: U32, b: Bool, +old: R.RhTab<K, V>) -> {R.RHash.size(~K, ~V, R.rh.start.go(~K, ~V, b, R.RHash{p, n, cur, old, c}, log, seed)) == n : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def start_size(~K: Data, ~V: Data, t: R.RHash<K, V>, +log: Nat, +seed: U32) -> {R.RHash.size(~K, ~V, R.rh.start(~K, ~V, t, log, seed)) == R.RHash.size(~K, ~V, t) : Nat}:
  match t:
    case R.RHash{+p, +n, +cur, +old, +c}:
      ss.go(~K, ~V, p, n, cur, c, log, seed, R.rh.old_empty(~K, ~V, old), old)

def au.go(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +kw: List<&2, U32>, +t: R.RHash<K, V>, +seed: U32, w: Maybe<&2, Nat>) -> {R.rh.lookup(~K, ~V, ~hash, R.rh.auto.go(~K, ~V, w, t, seed), kw) == R.rh.lookup(~K, ~V, ~hash, t, kw) : Maybe<&2, V>}:
  match w:
    case None{}:
      {==}
    case Some{l2}:
      start_lookup(~K, ~V, ~hash, t, l2, seed, kw)

def auto_lookup(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, t: R.RHash<K, V>, +kw: List<&2, U32>) -> {R.rh.lookup(~K, ~V, ~hash, R.rh.auto(~K, ~V, t), kw) == R.rh.lookup(~K, ~V, ~hash, t, kw) : Maybe<&2, V>}:
  match t:
    case R.RHash{+p, +n, +cur, +old, +c}:
      match cur:
        case R.RhTab{+log, +seed, +tree}:
          au.go(~K, ~V, ~hash, kw, R.RHash{p, n, R.RhTab{log, seed, tree}, old, c}, U32.add(seed, R.rh.seed_step(p)), R.rh.want(p, n, log))

def asz.go(~K: Data, ~V: Data, +t: R.RHash<K, V>, +seed: U32, w: Maybe<&2, Nat>) -> {R.RHash.size(~K, ~V, R.rh.auto.go(~K, ~V, w, t, seed)) == R.RHash.size(~K, ~V, t) : Nat}:
  match w:
    case None{}:
      {==}
    case Some{l2}:
      start_size(~K, ~V, t, l2, seed)

def auto_size(~K: Data, ~V: Data, t: R.RHash<K, V>) -> {R.RHash.size(~K, ~V, R.rh.auto(~K, ~V, t)) == R.RHash.size(~K, ~V, t) : Nat}:
  match t:
    case R.RHash{+p, +n, +cur, +old, +c}:
      match cur:
        case R.RhTab{+log, +seed, +tree}:
          asz.go(~K, ~V, R.RHash{p, n, R.RhTab{log, seed, tree}, old, c}, U32.add(seed, R.rh.seed_step(p)), R.rh.want(p, n, log))

# the resize work after an operation changes no lookup and not the size
def after_lookup(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, t: R.RHash<K, V>, +kw: List<&2, U32>) -> {R.rh.lookup(~K, ~V, ~hash, R.rh.after(~K, ~V, ~hash, t), kw) == R.rh.lookup(~K, ~V, ~hash, t, kw) : Maybe<&2, V>}:
  match t:
    case R.RHash{+p, +n, +cur, +old, +c}:
      Equal.trans(Maybe<&2, V>, R.rh.lookup(~K, ~V, ~hash, R.rh.auto(~K, ~V, R.rh.steps(~K, ~V, ~hash, R.rh.nsteps(p), R.RHash{p, n, cur, old, c})), kw), R.rh.lookup(~K, ~V, ~hash, R.rh.steps(~K, ~V, ~hash, R.rh.nsteps(p), R.RHash{p, n, cur, old, c}), kw), R.rh.lookup(~K, ~V, ~hash, R.RHash{p, n, cur, old, c}, kw), auto_lookup(~K, ~V, ~hash, R.rh.steps(~K, ~V, ~hash, R.rh.nsteps(p), R.RHash{p, n, cur, old, c}), kw), steps_lookup(~K, ~V, ~hash, R.rh.nsteps(p), R.RHash{p, n, cur, old, c}, kw))

def after_size(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, t: R.RHash<K, V>) -> {R.RHash.size(~K, ~V, R.rh.after(~K, ~V, ~hash, t)) == R.RHash.size(~K, ~V, t) : Nat}:
  match t:
    case R.RHash{+p, +n, +cur, +old, +c}:
      Equal.trans(Nat, R.RHash.size(~K, ~V, R.rh.auto(~K, ~V, R.rh.steps(~K, ~V, ~hash, R.rh.nsteps(p), R.RHash{p, n, cur, old, c}))), R.RHash.size(~K, ~V, R.rh.steps(~K, ~V, ~hash, R.rh.nsteps(p), R.RHash{p, n, cur, old, c})), n, auto_size(~K, ~V, R.rh.steps(~K, ~V, ~hash, R.rh.nsteps(p), R.RHash{p, n, cur, old, c})), steps_size(~K, ~V, ~hash, R.rh.nsteps(p), R.RHash{p, n, cur, old, c}))

# ---------------------------------------------------------------- the laws: a new table, the map, size, migration

def Laws.lookup_new(K, V, kenc, hash, p, k):
  match p:
    case R.RhParams{gp, sp, au, mn, mx, +il, st, +s0, ss}:
      %Equal.sym(List<&2, R.RhEntry<K, V>>, R.RhTree.get(~K, ~V, R.RhTree.full(~K, ~V, il), R.RhTab.path(~hash, il, s0, kenc(k))), Nil{}, get_full(~K, ~V, il, R.RhTab.path(~hash, il, s0, kenc(k)))) : {R.rh.orelse(~V, R.rh.find(~K, ~V, kenc(k), _), None{}) == None{} : Maybe<&2, V>}
      {==}

def Laws.size_new(K, V, p):
  match p:
    case R.RhParams{gp, sp, au, mn, mx, il, st, s0, ss}:
      {==}

def Laws.lookup_insert(K, V, kenc, hash, t, k, v):
  Equal.trans(Maybe<&2, V>, R.rh.lookup(~K, ~V, ~hash, R.rh.after(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), k, v)), kenc(k)), R.rh.lookup(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), k, v), kenc(k)), Some{v}, after_lookup(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), k, v), kenc(k)), ins_same(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), k, v))

def Laws.lookup_insert_other(K, V, kenc, hash, t, k, j, v, e):
  Equal.trans(Maybe<&2, V>, R.rh.lookup(~K, ~V, ~hash, R.rh.after(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), k, v)), kenc(j)), R.rh.lookup(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), k, v), kenc(j)), R.rh.lookup(~K, ~V, ~hash, t, kenc(j)), after_lookup(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), k, v), kenc(j)), ins_other(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), k, v, kenc(j), e))

def Laws.lookup_remove(K, V, kenc, hash, t, k):
  Equal.trans(Maybe<&2, V>, R.rh.lookup(~K, ~V, ~hash, R.rh.after(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k))), kenc(k)), R.rh.lookup(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k)), kenc(k)), None{}, after_lookup(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k)), kenc(k)), del_same(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k)))

def Laws.lookup_remove_other(K, V, kenc, hash, t, k, j, e):
  Equal.trans(Maybe<&2, V>, R.rh.lookup(~K, ~V, ~hash, R.rh.after(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k))), kenc(j)), R.rh.lookup(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k)), kenc(j)), R.rh.lookup(~K, ~V, ~hash, t, kenc(j)), after_lookup(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k)), kenc(j)), del_other(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), kenc(j), e))

def Laws.lookup_same_key(K, V, kenc, hash, t, k, j, e):
  %weq_sound(kenc(k), kenc(j), e) : {R.rh.lookup(~K, ~V, ~hash, t, _) == R.rh.lookup(~K, ~V, ~hash, t, kenc(k)) : Maybe<&2, V>}
  {==}

def Laws.size_insert_absent(K, V, kenc, hash, t, k, v, h):
  %Equal.sym(Bool, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), False{}, h) : {R.RHash.size(~K, ~V, R.rh.after(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, _, t, kenc(k), k, v))) == 1n+R.RHash.size(~K, ~V, t) : Nat}
  Equal.trans(Nat, R.RHash.size(~K, ~V, R.rh.after(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, False{}, t, kenc(k), k, v))), R.RHash.size(~K, ~V, R.rh.ins(~K, ~V, ~hash, False{}, t, kenc(k), k, v)), 1n+R.RHash.size(~K, ~V, t), after_size(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, False{}, t, kenc(k), k, v)), size_ins(~K, ~V, ~hash, False{}, t, kenc(k), k, v))

def Laws.size_insert_present(K, V, kenc, hash, t, k, v, h):
  %Equal.sym(Bool, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), True{}, h) : {R.RHash.size(~K, ~V, R.rh.after(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, _, t, kenc(k), k, v))) == R.RHash.size(~K, ~V, t) : Nat}
  Equal.trans(Nat, R.RHash.size(~K, ~V, R.rh.after(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, True{}, t, kenc(k), k, v))), R.RHash.size(~K, ~V, R.rh.ins(~K, ~V, ~hash, True{}, t, kenc(k), k, v)), R.RHash.size(~K, ~V, t), after_size(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, True{}, t, kenc(k), k, v)), size_ins(~K, ~V, ~hash, True{}, t, kenc(k), k, v))

def Laws.size_remove_present(K, V, kenc, hash, t, k, h):
  %Equal.sym(Bool, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), True{}, h) : {R.RHash.size(~K, ~V, R.rh.after(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, _, t, kenc(k)))) == Nat.sub(R.RHash.size(~K, ~V, t), 1n) : Nat}
  Equal.trans(Nat, R.RHash.size(~K, ~V, R.rh.after(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, True{}, t, kenc(k)))), R.RHash.size(~K, ~V, R.rh.del(~K, ~V, ~hash, True{}, t, kenc(k))), Nat.sub(R.RHash.size(~K, ~V, t), 1n), after_size(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, True{}, t, kenc(k))), size_del(~K, ~V, ~hash, True{}, t, kenc(k)))

def Laws.size_remove_absent(K, V, kenc, hash, t, k, h):
  %Equal.sym(Bool, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), False{}, h) : {R.RHash.size(~K, ~V, R.rh.after(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, _, t, kenc(k)))) == R.RHash.size(~K, ~V, t) : Nat}
  Equal.trans(Nat, R.RHash.size(~K, ~V, R.rh.after(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, False{}, t, kenc(k)))), R.RHash.size(~K, ~V, R.rh.del(~K, ~V, ~hash, False{}, t, kenc(k))), R.RHash.size(~K, ~V, t), after_size(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, False{}, t, kenc(k))), size_del(~K, ~V, ~hash, False{}, t, kenc(k)))

def Laws.lookup_step(K, V, kenc, hash, t, k):
  step_lookup(~K, ~V, ~hash, t, kenc(k))

def Laws.size_step(K, V, hash, t):
  step_size(~K, ~V, ~hash, t)

def Laws.lookup_steps(K, V, kenc, hash, n, t, k):
  steps_lookup(~K, ~V, ~hash, n, t, kenc(k))

def drain_lookup(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +t: R.RHash<K, V>, +kw: List<&2, U32>) -> {R.rh.lookup(~K, ~V, ~hash, R.RHash.drain(~K, ~V, ~hash, t), kw) == R.rh.lookup(~K, ~V, ~hash, t, kw) : Maybe<&2, V>}:
  steps_lookup(~K, ~V, ~hash, R.rh.pow2(R.rh.old_log(~K, ~V, t)), t, kw)

def Laws.lookup_drain(K, V, kenc, hash, t, k):
  drain_lookup(~K, ~V, ~hash, t, kenc(k))

def resize_lookup(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +t: R.RHash<K, V>, +log: Nat, +seed: U32, +kw: List<&2, U32>) -> {R.rh.lookup(~K, ~V, ~hash, R.RHash.resize(~K, ~V, ~hash, t, log, seed), kw) == R.rh.lookup(~K, ~V, ~hash, t, kw) : Maybe<&2, V>}:
  Equal.trans(Maybe<&2, V>, R.rh.lookup(~K, ~V, ~hash, R.rh.start(~K, ~V, R.RHash.drain(~K, ~V, ~hash, t), log, seed), kw), R.rh.lookup(~K, ~V, ~hash, R.RHash.drain(~K, ~V, ~hash, t), kw), R.rh.lookup(~K, ~V, ~hash, t, kw), start_lookup(~K, ~V, ~hash, R.RHash.drain(~K, ~V, ~hash, t), log, seed, kw), drain_lookup(~K, ~V, ~hash, t, kw))

def resize_size(~K: Data, ~V: Data, ~hash: U32 -> List<&2, U32> -> U32, +t: R.RHash<K, V>, +log: Nat, +seed: U32) -> {R.RHash.size(~K, ~V, R.RHash.resize(~K, ~V, ~hash, t, log, seed)) == R.RHash.size(~K, ~V, t) : Nat}:
  Equal.trans(Nat, R.RHash.size(~K, ~V, R.rh.start(~K, ~V, R.RHash.drain(~K, ~V, ~hash, t), log, seed)), R.RHash.size(~K, ~V, R.RHash.drain(~K, ~V, ~hash, t)), R.RHash.size(~K, ~V, t), start_size(~K, ~V, R.RHash.drain(~K, ~V, ~hash, t), log, seed), steps_size(~K, ~V, ~hash, R.rh.pow2(R.rh.old_log(~K, ~V, t)), t))

def Laws.lookup_resize(K, V, kenc, hash, t, log, seed, k):
  resize_lookup(~K, ~V, ~hash, t, log, seed, kenc(k))

def Laws.size_resize(K, V, hash, t, log, seed):
  resize_size(~K, ~V, ~hash, t, log, seed)

def Laws.vec_lookup():
  {==}

def Laws.vec_size():
  {==}

# ---------------------------------------------------------------- any interleaving

def opi.go(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, +t: R.RHash<K, V>, +k2: K, +v: V, +k: K, b: Bool, +eb: {R.RHash.same_key(~K, ~kenc, k2, k) == b : Bool}) -> {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.insert(~K, ~V, ~kenc, ~hash, t, k2, v), k) == R.rh.hit(~V, R.RHash.same_key(~K, ~kenc, k2, k), v, R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, k)) : Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(Bool, R.RHash.same_key(~K, ~kenc, k2, k), True{}, eb) : {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.insert(~K, ~V, ~kenc, ~hash, t, k2, v), k) == R.rh.hit(~V, _, v, R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, k)) : Maybe<&2, V>}
      %weq_sound(kenc(k2), kenc(k), eb) : {R.rh.lookup(~K, ~V, ~hash, R.RHash.insert(~K, ~V, ~kenc, ~hash, t, k2, v), _) == Some{v} : Maybe<&2, V>}
      Laws.lookup_insert(~K, ~V, ~kenc, ~hash, t, k2, v)
    case False{}:
      %Equal.sym(Bool, R.RHash.same_key(~K, ~kenc, k2, k), False{}, eb) : {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.insert(~K, ~V, ~kenc, ~hash, t, k2, v), k) == R.rh.hit(~V, _, v, R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, k)) : Maybe<&2, V>}
      Laws.lookup_insert_other(~K, ~V, ~kenc, ~hash, t, k2, k, v, eb)

def opd.go(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, +t: R.RHash<K, V>, +k2: K, +k: K, b: Bool, +eb: {R.RHash.same_key(~K, ~kenc, k2, k) == b : Bool}) -> {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.remove(~K, ~V, ~kenc, ~hash, t, k2), k) == R.rh.miss(~V, R.RHash.same_key(~K, ~kenc, k2, k), R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, k)) : Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(Bool, R.RHash.same_key(~K, ~kenc, k2, k), True{}, eb) : {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.remove(~K, ~V, ~kenc, ~hash, t, k2), k) == R.rh.miss(~V, _, R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, k)) : Maybe<&2, V>}
      %weq_sound(kenc(k2), kenc(k), eb) : {R.rh.lookup(~K, ~V, ~hash, R.RHash.remove(~K, ~V, ~kenc, ~hash, t, k2), _) == None{} : Maybe<&2, V>}
      Laws.lookup_remove(~K, ~V, ~kenc, ~hash, t, k2)
    case False{}:
      %Equal.sym(Bool, R.RHash.same_key(~K, ~kenc, k2, k), False{}, eb) : {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.remove(~K, ~V, ~kenc, ~hash, t, k2), k) == R.rh.miss(~V, _, R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, k)) : Maybe<&2, V>}
      Laws.lookup_remove_other(~K, ~V, ~kenc, ~hash, t, k2, k, eb)

# one operation moves a key's lookup as the model moves it
def op_lookup(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, +t: R.RHash<K, V>, op: R.RhOp<K, V>, +k: K) -> {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.apply(~K, ~V, ~kenc, ~hash, t, op), k) == M.RhModel.after.op(~K, ~V, ~kenc, op, k, R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, k)) : Maybe<&2, V>}:
  match op:
    case R.RhIns{+k2, +v}:
      opi.go(~K, ~V, ~kenc, ~hash, t, k2, v, k, R.RHash.same_key(~K, ~kenc, k2, k), {==})
    case R.RhDel{+k2}:
      opd.go(~K, ~V, ~kenc, ~hash, t, k2, k, R.RHash.same_key(~K, ~kenc, k2, k), {==})
    case R.RhStep{}:
      step_lookup(~K, ~V, ~hash, t, kenc(k))
    case R.RhResize{+log, +seed}:
      resize_lookup(~K, ~V, ~hash, t, log, seed, kenc(k))

def run_lookup(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, ops: List<&2, R.RhOp<K, V>>, +t: R.RHash<K, V>, +k: K) -> {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.rh.run(~K, ~V, ~kenc, ~hash, ops, t), k) == M.RhModel.after(~K, ~V, ~kenc, ops, k, R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, k)) : Maybe<&2, V>}:
  match ops:
    case Nil{}:
      {==}
    case Con{+op, +rest}:
      %Equal.sym(Maybe<&2, V>, R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.rh.run(~K, ~V, ~kenc, ~hash, rest, R.RHash.apply(~K, ~V, ~kenc, ~hash, t, op)), k), M.RhModel.after(~K, ~V, ~kenc, rest, k, R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.apply(~K, ~V, ~kenc, ~hash, t, op), k)), run_lookup(~K, ~V, ~kenc, ~hash, rest, R.RHash.apply(~K, ~V, ~kenc, ~hash, t, op), k)) : {_ == M.RhModel.after(~K, ~V, ~kenc, rest, k, M.RhModel.after.op(~K, ~V, ~kenc, op, k, R.RHash.lookup(~K, ~V, ~kenc, ~hash, t, k))) : Maybe<&2, V>}
      %op_lookup(~K, ~V, ~kenc, ~hash, t, op, k) : {M.RhModel.after(~K, ~V, ~kenc, rest, k, R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.apply(~K, ~V, ~kenc, ~hash, t, op), k)) == M.RhModel.after(~K, ~V, ~kenc, rest, k, _) : Maybe<&2, V>}
      {==}

def Laws.lookup_run(K, V, kenc, hash, t, ops, k):
  run_lookup(~K, ~V, ~kenc, ~hash, ops, t, k)

# the model moves a key's value as RhModel.after.op says

def mi.go(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, +k2: K, +v: V, +k: K, +m: List<&2, R.RhEntry<K, V>>, b: Bool, +eb: {R.rh.weq(kenc(k2), kenc(k)) == b : Bool}) -> {R.rh.hit(~V, R.rh.weq(kenc(k), kenc(k2)), v, R.rh.find(~K, ~V, kenc(k), R.rh.drop(~K, ~V, kenc(k2), m))) == R.rh.hit(~V, R.rh.weq(kenc(k2), kenc(k)), v, R.rh.find(~K, ~V, kenc(k), m)) : Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(Bool, R.rh.weq(kenc(k2), kenc(k)), True{}, eb) : {R.rh.hit(~V, R.rh.weq(kenc(k), kenc(k2)), v, R.rh.find(~K, ~V, kenc(k), R.rh.drop(~K, ~V, kenc(k2), m))) == R.rh.hit(~V, _, v, R.rh.find(~K, ~V, kenc(k), m)) : Maybe<&2, V>}
      %weq_sound(kenc(k2), kenc(k), eb) : {R.rh.hit(~V, R.rh.weq(_, kenc(k2)), v, R.rh.find(~K, ~V, kenc(k), R.rh.drop(~K, ~V, kenc(k2), m))) == Some{v} : Maybe<&2, V>}
      %Equal.sym(Bool, R.rh.weq(kenc(k2), kenc(k2)), True{}, weq_self(kenc(k2))) : {R.rh.hit(~V, _, v, R.rh.find(~K, ~V, kenc(k), R.rh.drop(~K, ~V, kenc(k2), m))) == Some{v} : Maybe<&2, V>}
      {==}
    case False{}:
      +ne = weq_false_sym(kenc(k2), kenc(k), eb)
      %Equal.sym(Bool, R.rh.weq(kenc(k2), kenc(k)), False{}, eb) : {R.rh.hit(~V, R.rh.weq(kenc(k), kenc(k2)), v, R.rh.find(~K, ~V, kenc(k), R.rh.drop(~K, ~V, kenc(k2), m))) == R.rh.hit(~V, _, v, R.rh.find(~K, ~V, kenc(k), m)) : Maybe<&2, V>}
      %Equal.sym(Bool, R.rh.weq(kenc(k), kenc(k2)), False{}, ne) : {R.rh.hit(~V, _, v, R.rh.find(~K, ~V, kenc(k), R.rh.drop(~K, ~V, kenc(k2), m))) == R.rh.find(~K, ~V, kenc(k), m) : Maybe<&2, V>}
      find_drop_other(~K, ~V, kenc(k2), kenc(k), ne, m)

def md.go(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, +k2: K, +k: K, +m: List<&2, R.RhEntry<K, V>>, b: Bool, +eb: {R.rh.weq(kenc(k2), kenc(k)) == b : Bool}) -> {R.rh.find(~K, ~V, kenc(k), R.rh.drop(~K, ~V, kenc(k2), m)) == R.rh.miss(~V, R.rh.weq(kenc(k2), kenc(k)), R.rh.find(~K, ~V, kenc(k), m)) : Maybe<&2, V>}:
  match b:
    case True{}:
      %Equal.sym(Bool, R.rh.weq(kenc(k2), kenc(k)), True{}, eb) : {R.rh.find(~K, ~V, kenc(k), R.rh.drop(~K, ~V, kenc(k2), m)) == R.rh.miss(~V, _, R.rh.find(~K, ~V, kenc(k), m)) : Maybe<&2, V>}
      %weq_sound(kenc(k2), kenc(k), eb) : {R.rh.find(~K, ~V, _, R.rh.drop(~K, ~V, kenc(k2), m)) == None{} : Maybe<&2, V>}
      find_drop_same(~K, ~V, kenc(k2), m)
    case False{}:
      %Equal.sym(Bool, R.rh.weq(kenc(k2), kenc(k)), False{}, eb) : {R.rh.find(~K, ~V, kenc(k), R.rh.drop(~K, ~V, kenc(k2), m)) == R.rh.miss(~V, _, R.rh.find(~K, ~V, kenc(k), m)) : Maybe<&2, V>}
      find_drop_other(~K, ~V, kenc(k2), kenc(k), weq_false_sym(kenc(k2), kenc(k), eb), m)

def model_op(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, +m: List<&2, R.RhEntry<K, V>>, op: R.RhOp<K, V>, +k: K) -> {M.RhModel.lookup(~K, ~V, ~kenc, M.RhModel.apply(~K, ~V, ~kenc, m, op), k) == M.RhModel.after.op(~K, ~V, ~kenc, op, k, M.RhModel.lookup(~K, ~V, ~kenc, m, k)) : Maybe<&2, V>}:
  match op:
    case R.RhIns{+k2, +v}:
      mi.go(~K, ~V, ~kenc, k2, v, k, m, R.rh.weq(kenc(k2), kenc(k)), {==})
    case R.RhDel{+k2}:
      md.go(~K, ~V, ~kenc, k2, k, m, R.rh.weq(kenc(k2), kenc(k)), {==})
    case R.RhStep{}:
      {==}
    case R.RhResize{log, seed}:
      {==}

def replay_lookup(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, +p: R.RhParams, tr: List<&2, R.RhOp<K, V>>, +k: K) -> {R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, tr), k) == M.RhModel.lookup(~K, ~V, ~kenc, M.RhModel.replay(~K, ~V, ~kenc, tr), k) : Maybe<&2, V>}:
  match tr:
    case Nil{}:
      Laws.lookup_new(~K, ~V, ~kenc, ~hash, p, k)
    case Con{+op, +older}:
      %Equal.sym(Maybe<&2, V>, R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.apply(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), op), k), M.RhModel.after.op(~K, ~V, ~kenc, op, k, R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), k)), op_lookup(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), op, k)) : {_ == M.RhModel.lookup(~K, ~V, ~kenc, M.RhModel.apply(~K, ~V, ~kenc, M.RhModel.replay(~K, ~V, ~kenc, older), op), k) : Maybe<&2, V>}
      %Equal.sym(Maybe<&2, V>, R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), k), M.RhModel.lookup(~K, ~V, ~kenc, M.RhModel.replay(~K, ~V, ~kenc, older), k), replay_lookup(~K, ~V, ~kenc, ~hash, p, older, k)) : {M.RhModel.after.op(~K, ~V, ~kenc, op, k, _) == M.RhModel.lookup(~K, ~V, ~kenc, M.RhModel.apply(~K, ~V, ~kenc, M.RhModel.replay(~K, ~V, ~kenc, older), op), k) : Maybe<&2, V>}
      Equal.sym(Maybe<&2, V>, M.RhModel.lookup(~K, ~V, ~kenc, M.RhModel.apply(~K, ~V, ~kenc, M.RhModel.replay(~K, ~V, ~kenc, older), op), k), M.RhModel.after.op(~K, ~V, ~kenc, op, k, M.RhModel.lookup(~K, ~V, ~kenc, M.RhModel.replay(~K, ~V, ~kenc, older), k)), model_op(~K, ~V, ~kenc, M.RhModel.replay(~K, ~V, ~kenc, older), op, k))

def Laws.lookup_replay(K, V, kenc, hash, p, tr, k):
  replay_lookup(~K, ~V, ~kenc, ~hash, p, tr, k)

# ---------------------------------------------------------------- the model binds each key once, so its length counts keys

def uq(~K: Data, ~V: Data, m: List<&2, R.RhEntry<K, V>>) -> Bool:
  match m:
    case Nil{}:
      True{}
    case Con{e, +t}:
      match e:
        case R.RhEntry{+w, k, v}:
          Bool.and(Bool.not(R.rh.present(~V, R.rh.find(~K, ~V, w, t))), uq(~K, ~V, t))

def not_true(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, ab.ft(e))
    case False{}:
      {==}

def fdn.go(~K: Data, ~V: Data, +x: List<&2, U32>, +kw: List<&2, U32>, +t: List<&2, R.RhEntry<K, V>>, +hx: {R.rh.present(~V, R.rh.find(~K, ~V, x, t)) == False{} : Bool}, b: Bool, +eb: {R.rh.weq(x, kw) == b : Bool}) -> {R.rh.present(~V, R.rh.find(~K, ~V, x, R.rh.drop(~K, ~V, kw, t))) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(List<&2, U32>, x, kw, weq_sound(x, kw, eb)) : {R.rh.present(~V, R.rh.find(~K, ~V, _, R.rh.drop(~K, ~V, kw, t))) == False{} : Bool}
      %Equal.sym(Maybe<&2, V>, R.rh.find(~K, ~V, kw, R.rh.drop(~K, ~V, kw, t)), None{}, find_drop_same(~K, ~V, kw, t)) : {R.rh.present(~V, _) == False{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, V>, R.rh.find(~K, ~V, x, R.rh.drop(~K, ~V, kw, t)), R.rh.find(~K, ~V, x, t), find_drop_other(~K, ~V, kw, x, eb, t)) : {R.rh.present(~V, _) == False{} : Bool}
      hx

# dropping keys never brings one back
def fdn(~K: Data, ~V: Data, +x: List<&2, U32>, +kw: List<&2, U32>, +t: List<&2, R.RhEntry<K, V>>, +hx: {R.rh.present(~V, R.rh.find(~K, ~V, x, t)) == False{} : Bool}) -> {R.rh.present(~V, R.rh.find(~K, ~V, x, R.rh.drop(~K, ~V, kw, t))) == False{} : Bool}:
  fdn.go(~K, ~V, x, kw, t, hx, R.rh.weq(x, kw), {==})

def ud.go(~K: Data, ~V: Data, +kw: List<&2, U32>, +w: List<&2, U32>, +k: K, +v: V, +t: List<&2, R.RhEntry<K, V>>, +hw: {Bool.not(R.rh.present(~V, R.rh.find(~K, ~V, w, t))) == True{} : Bool}, +ih: {uq(~K, ~V, R.rh.drop(~K, ~V, kw, t)) == True{} : Bool}, b: Bool, +eb: {R.rh.weq(kw, w) == b : Bool}) -> {uq(~K, ~V, R.rh.keep(~K, ~V, R.rh.weq(kw, w), R.RhEntry{w, k, v}, R.rh.drop(~K, ~V, kw, t))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, R.rh.weq(kw, w), True{}, eb) : {uq(~K, ~V, R.rh.keep(~K, ~V, _, R.RhEntry{w, k, v}, R.rh.drop(~K, ~V, kw, t))) == True{} : Bool}
      ih
    case False{}:
      %Equal.sym(Bool, R.rh.weq(kw, w), False{}, eb) : {uq(~K, ~V, R.rh.keep(~K, ~V, _, R.RhEntry{w, k, v}, R.rh.drop(~K, ~V, kw, t))) == True{} : Bool}
      %Equal.sym(Bool, R.rh.present(~V, R.rh.find(~K, ~V, w, R.rh.drop(~K, ~V, kw, t))), False{}, fdn(~K, ~V, w, kw, t, not_true(R.rh.present(~V, R.rh.find(~K, ~V, w, t)), hw))) : {Bool.and(Bool.not(_), uq(~K, ~V, R.rh.drop(~K, ~V, kw, t))) == True{} : Bool}
      ih

def u_drop(~K: Data, ~V: Data, +kw: List<&2, U32>, m: List<&2, R.RhEntry<K, V>>, u: {uq(~K, ~V, m) == True{} : Bool}) -> {uq(~K, ~V, R.rh.drop(~K, ~V, kw, m)) == True{} : Bool}:
  match m:
    case Nil{}:
      {==}
    case Con{e, +t}:
      match e:
        case R.RhEntry{+w, +k, +v}:
          +u2 = u
          ud.go(~K, ~V, kw, w, k, v, t, bool.and_l(Bool.not(R.rh.present(~V, R.rh.find(~K, ~V, w, t))), uq(~K, ~V, t), u2), u_drop(~K, ~V, kw, t, bool.and_r(Bool.not(R.rh.present(~V, R.rh.find(~K, ~V, w, t))), uq(~K, ~V, t), u2)), R.rh.weq(kw, w), {==})

def u_ins(~K: Data, ~V: Data, +kw: List<&2, U32>, -k: K, -v: V, +m: List<&2, R.RhEntry<K, V>>, u: {uq(~K, ~V, m) == True{} : Bool}) -> {uq(~K, ~V, Con{R.RhEntry{kw, k, v}, R.rh.drop(~K, ~V, kw, m)}) == True{} : Bool}:
  %Equal.sym(Maybe<&2, V>, R.rh.find(~K, ~V, kw, R.rh.drop(~K, ~V, kw, m)), None{}, find_drop_same(~K, ~V, kw, m)) : {Bool.and(Bool.not(R.rh.present(~V, _)), uq(~K, ~V, R.rh.drop(~K, ~V, kw, m))) == True{} : Bool}
  u_drop(~K, ~V, kw, m, u)

def u_replay(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, tr: List<&2, R.RhOp<K, V>>) -> {uq(~K, ~V, M.RhModel.replay(~K, ~V, ~kenc, tr)) == True{} : Bool}:
  match tr:
    case Nil{}:
      {==}
    case Con{op, +older}:
      match op:
        case R.RhIns{+k2, +v}:
          u_ins(~K, ~V, kenc(k2), k2, v, M.RhModel.replay(~K, ~V, ~kenc, older), u_replay(~K, ~V, ~kenc, older))
        case R.RhDel{+k2}:
          u_drop(~K, ~V, kenc(k2), M.RhModel.replay(~K, ~V, ~kenc, older), u_replay(~K, ~V, ~kenc, older))
        case R.RhStep{}:
          u_replay(~K, ~V, ~kenc, older)
        case R.RhResize{log, seed}:
          u_replay(~K, ~V, ~kenc, older)

def bump_succ(b: Bool, n: Nat) -> {R.rh.bump(b, 1n+n) == 1n+R.rh.bump(b, n) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ld.go(~K: Data, ~V: Data, +kw: List<&2, U32>, +w: List<&2, U32>, +k: K, +v: V, +t: List<&2, R.RhEntry<K, V>>, +hw: {Bool.not(R.rh.present(~V, R.rh.find(~K, ~V, w, t))) == True{} : Bool}, +ih: {List.length(&2, R.RhEntry<K, V>, t) == R.rh.bump(Bool.not(R.rh.present(~V, R.rh.find(~K, ~V, kw, t))), List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kw, t))) : Nat}, b: Bool, +eb: {R.rh.weq(kw, w) == b : Bool}) -> {1n+List.length(&2, R.RhEntry<K, V>, t) == R.rh.bump(Bool.not(R.rh.present(~V, R.rh.hit(~V, R.rh.weq(kw, w), v, R.rh.find(~K, ~V, kw, t)))), List.length(&2, R.RhEntry<K, V>, R.rh.keep(~K, ~V, R.rh.weq(kw, w), R.RhEntry{w, k, v}, R.rh.drop(~K, ~V, kw, t)))) : Nat}:
  match b:
    case True{}:
      %Equal.sym(Bool, R.rh.weq(kw, w), True{}, eb) : {1n+List.length(&2, R.RhEntry<K, V>, t) == R.rh.bump(Bool.not(R.rh.present(~V, R.rh.hit(~V, _, v, R.rh.find(~K, ~V, kw, t)))), List.length(&2, R.RhEntry<K, V>, R.rh.keep(~K, ~V, _, R.RhEntry{w, k, v}, R.rh.drop(~K, ~V, kw, t)))) : Nat}
      +s = weq_sound(kw, w, eb)
      +pf = not_true(R.rh.present(~V, R.rh.find(~K, ~V, w, t)), hw)
      %Equal.sym(Nat, List.length(&2, R.RhEntry<K, V>, t), R.rh.bump(Bool.not(R.rh.present(~V, R.rh.find(~K, ~V, kw, t))), List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kw, t))), ih) : {1n+_ == 1n+List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kw, t)) : Nat}
      %Equal.sym(List<&2, U32>, kw, w, s) : {1n+R.rh.bump(Bool.not(R.rh.present(~V, R.rh.find(~K, ~V, _, t))), List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kw, t))) == 1n+List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kw, t)) : Nat}
      %Equal.sym(Bool, R.rh.present(~V, R.rh.find(~K, ~V, w, t)), False{}, pf) : {1n+R.rh.bump(Bool.not(_), List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kw, t))) == 1n+List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kw, t)) : Nat}
      {==}
    case False{}:
      %Equal.sym(Bool, R.rh.weq(kw, w), False{}, eb) : {1n+List.length(&2, R.RhEntry<K, V>, t) == R.rh.bump(Bool.not(R.rh.present(~V, R.rh.hit(~V, _, v, R.rh.find(~K, ~V, kw, t)))), List.length(&2, R.RhEntry<K, V>, R.rh.keep(~K, ~V, _, R.RhEntry{w, k, v}, R.rh.drop(~K, ~V, kw, t)))) : Nat}
      %Equal.sym(Nat, R.rh.bump(Bool.not(R.rh.present(~V, R.rh.find(~K, ~V, kw, t))), 1n+List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kw, t))), 1n+R.rh.bump(Bool.not(R.rh.present(~V, R.rh.find(~K, ~V, kw, t))), List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kw, t))), bump_succ(Bool.not(R.rh.present(~V, R.rh.find(~K, ~V, kw, t))), List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kw, t)))) : {1n+List.length(&2, R.RhEntry<K, V>, t) == _ : Nat}
      %ih : {1n+List.length(&2, R.RhEntry<K, V>, t) == 1n+_ : Nat}
      {==}

# a model that binds each key once loses exactly one entry when a bound
# key is dropped, and none when an unbound one is
def len_drop(~K: Data, ~V: Data, +kw: List<&2, U32>, m: List<&2, R.RhEntry<K, V>>, u: {uq(~K, ~V, m) == True{} : Bool}) -> {List.length(&2, R.RhEntry<K, V>, m) == R.rh.bump(Bool.not(R.rh.present(~V, R.rh.find(~K, ~V, kw, m))), List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kw, m))) : Nat}:
  match m:
    case Nil{}:
      {==}
    case Con{e, +t}:
      match e:
        case R.RhEntry{+w, +k, +v}:
          +u2 = u
          ld.go(~K, ~V, kw, w, k, v, t, bool.and_l(Bool.not(R.rh.present(~V, R.rh.find(~K, ~V, w, t))), uq(~K, ~V, t), u2), len_drop(~K, ~V, kw, t, bool.and_r(Bool.not(R.rh.present(~V, R.rh.find(~K, ~V, w, t))), uq(~K, ~V, t), u2)), R.rh.weq(kw, w), {==})

def nat.sub_zero(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def il.go(+x: Nat, +y: Nat, c: Bool, ld: {x == R.rh.bump(Bool.not(c), y) : Nat}) -> {R.rh.bump(c, x) == 1n+y : Nat}:
  match c:
    case True{}:
      ld
    case False{}:
      %ld : {1n+x == 1n+_ : Nat}
      {==}

def dl.go(+x: Nat, +y: Nat, c: Bool, ld: {x == R.rh.bump(Bool.not(c), y) : Nat}) -> {R.rh.unbump(c, x) == y : Nat}:
  match c:
    case True{}:
      %Equal.sym(Nat, x, 1n+y, ld) : {Nat.sub(_, 1n) == y : Nat}
      nat.sub_zero(y)
    case False{}:
      ld

def sz_insert(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, +t: R.RHash<K, V>, +k: K, +v: V) -> {R.RHash.size(~K, ~V, R.RHash.insert(~K, ~V, ~kenc, ~hash, t, k, v)) == R.rh.bump(R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), R.RHash.size(~K, ~V, t)) : Nat}:
  Equal.trans(Nat, R.RHash.size(~K, ~V, R.rh.after(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), k, v))), R.RHash.size(~K, ~V, R.rh.ins(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), k, v)), R.rh.bump(R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), R.RHash.size(~K, ~V, t)), after_size(~K, ~V, ~hash, R.rh.ins(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), k, v)), size_ins(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k), k, v))

def sz_remove(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, +t: R.RHash<K, V>, +k: K) -> {R.RHash.size(~K, ~V, R.RHash.remove(~K, ~V, ~kenc, ~hash, t, k)) == R.rh.unbump(R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), R.RHash.size(~K, ~V, t)) : Nat}:
  Equal.trans(Nat, R.RHash.size(~K, ~V, R.rh.after(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k)))), R.RHash.size(~K, ~V, R.rh.del(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k))), R.rh.unbump(R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), R.RHash.size(~K, ~V, t)), after_size(~K, ~V, ~hash, R.rh.del(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k))), size_del(~K, ~V, ~hash, R.RHash.contains(~K, ~V, ~kenc, ~hash, t, k), t, kenc(k)))

def replay_size(~K: Data, ~V: Data, ~kenc: K -> List<&2, U32>, ~hash: U32 -> List<&2, U32> -> U32, +p: R.RhParams, tr: List<&2, R.RhOp<K, V>>) -> {R.RHash.size(~K, ~V, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, tr)) == List.length(&2, R.RhEntry<K, V>, M.RhModel.replay(~K, ~V, ~kenc, tr)) : Nat}:
  match tr:
    case Nil{}:
      Laws.size_new(~K, ~V, p)
    case Con{op, +older}:
      match op:
        case R.RhIns{+k2, +v}:
          %Equal.sym(Nat, R.RHash.size(~K, ~V, R.RHash.insert(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), k2, v)), R.rh.bump(R.RHash.contains(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), k2), R.RHash.size(~K, ~V, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older))), sz_insert(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), k2, v)) : {_ == 1n+List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kenc(k2), M.RhModel.replay(~K, ~V, ~kenc, older))) : Nat}
          %Equal.sym(Nat, R.RHash.size(~K, ~V, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older)), List.length(&2, R.RhEntry<K, V>, M.RhModel.replay(~K, ~V, ~kenc, older)), replay_size(~K, ~V, ~kenc, ~hash, p, older)) : {R.rh.bump(R.RHash.contains(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), k2), _) == 1n+List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kenc(k2), M.RhModel.replay(~K, ~V, ~kenc, older))) : Nat}
          %Equal.sym(Maybe<&2, V>, R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), k2), M.RhModel.lookup(~K, ~V, ~kenc, M.RhModel.replay(~K, ~V, ~kenc, older), k2), replay_lookup(~K, ~V, ~kenc, ~hash, p, older, k2)) : {R.rh.bump(R.rh.present(~V, _), List.length(&2, R.RhEntry<K, V>, M.RhModel.replay(~K, ~V, ~kenc, older))) == 1n+List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kenc(k2), M.RhModel.replay(~K, ~V, ~kenc, older))) : Nat}
          il.go(List.length(&2, R.RhEntry<K, V>, M.RhModel.replay(~K, ~V, ~kenc, older)), List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kenc(k2), M.RhModel.replay(~K, ~V, ~kenc, older))), R.rh.present(~V, R.rh.find(~K, ~V, kenc(k2), M.RhModel.replay(~K, ~V, ~kenc, older))), len_drop(~K, ~V, kenc(k2), M.RhModel.replay(~K, ~V, ~kenc, older), u_replay(~K, ~V, ~kenc, older)))
        case R.RhDel{+k2}:
          %Equal.sym(Nat, R.RHash.size(~K, ~V, R.RHash.remove(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), k2)), R.rh.unbump(R.RHash.contains(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), k2), R.RHash.size(~K, ~V, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older))), sz_remove(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), k2)) : {_ == List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kenc(k2), M.RhModel.replay(~K, ~V, ~kenc, older))) : Nat}
          %Equal.sym(Nat, R.RHash.size(~K, ~V, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older)), List.length(&2, R.RhEntry<K, V>, M.RhModel.replay(~K, ~V, ~kenc, older)), replay_size(~K, ~V, ~kenc, ~hash, p, older)) : {R.rh.unbump(R.RHash.contains(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), k2), _) == List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kenc(k2), M.RhModel.replay(~K, ~V, ~kenc, older))) : Nat}
          %Equal.sym(Maybe<&2, V>, R.RHash.lookup(~K, ~V, ~kenc, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), k2), M.RhModel.lookup(~K, ~V, ~kenc, M.RhModel.replay(~K, ~V, ~kenc, older), k2), replay_lookup(~K, ~V, ~kenc, ~hash, p, older, k2)) : {R.rh.unbump(R.rh.present(~V, _), List.length(&2, R.RhEntry<K, V>, M.RhModel.replay(~K, ~V, ~kenc, older))) == List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kenc(k2), M.RhModel.replay(~K, ~V, ~kenc, older))) : Nat}
          dl.go(List.length(&2, R.RhEntry<K, V>, M.RhModel.replay(~K, ~V, ~kenc, older)), List.length(&2, R.RhEntry<K, V>, R.rh.drop(~K, ~V, kenc(k2), M.RhModel.replay(~K, ~V, ~kenc, older))), R.rh.present(~V, R.rh.find(~K, ~V, kenc(k2), M.RhModel.replay(~K, ~V, ~kenc, older))), len_drop(~K, ~V, kenc(k2), M.RhModel.replay(~K, ~V, ~kenc, older), u_replay(~K, ~V, ~kenc, older)))
        case R.RhStep{}:
          Equal.trans(Nat, R.RHash.size(~K, ~V, R.RHash.step(~K, ~V, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older))), R.RHash.size(~K, ~V, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older)), List.length(&2, R.RhEntry<K, V>, M.RhModel.replay(~K, ~V, ~kenc, older)), step_size(~K, ~V, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older)), replay_size(~K, ~V, ~kenc, ~hash, p, older))
        case R.RhResize{+log, +seed}:
          Equal.trans(Nat, R.RHash.size(~K, ~V, R.RHash.resize(~K, ~V, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), log, seed)), R.RHash.size(~K, ~V, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older)), List.length(&2, R.RhEntry<K, V>, M.RhModel.replay(~K, ~V, ~kenc, older)), resize_size(~K, ~V, ~hash, R.RHash.replay(~K, ~V, ~kenc, ~hash, p, older), log, seed), replay_size(~K, ~V, ~kenc, ~hash, p, older))

def Laws.size_replay(K, V, kenc, hash, p, tr):
  replay_size(~K, ~V, ~kenc, ~hash, p, tr)
