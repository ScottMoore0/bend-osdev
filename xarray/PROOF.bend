import Base
import ./xarray.bend as X
import ./LAWS.bend as Laws

# Contradictions

def XP.bool_t(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def XP.tf(e: {True{} == False{} : Bool}) -> Empty:
  %e : XP.bool_t(_)
  Unit{}

def XP.ft(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, e) : XP.bool_t(_)
  Unit{}

# Path order: most significant bit first

def XP.then(c: Cmp, d: Cmp) -> Cmp:
  match c:
    case LT{}:
      LT{}
    case EQ{}:
      d
    case GT{}:
      GT{}

def XP.cmp(n: Nat, a: Word(n), b: Word(n)) -> Cmp:
  match n:
    case 0n:
      EQ{}
    case 1n+m:
      match a b:
        case WCon{x, xs} WCon{y, ys}:
          XP.then(Bool.cmp(x, y), XP.cmp(m, xs, ys))

def XP.then_fin(w: Cmp, -x: Bool, -y: Bool, -c: Cmp) -> {XP.then(Word.cmp.fin(x, y, w), c) == XP.then(w, XP.then(Bool.cmp(x, y), c)) : Cmp}:
  match w:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def XP.then_eq(c: Cmp) -> {XP.then(c, EQ{}) == c : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def XP.cmp_rev(n: Nat, a: Word(n), b: Word(n), +m: Nat, +acc: Word(m), +bcc: Word(m)) -> {XP.cmp(X.XPath.plus(n, m), X.XPath.rev(n, a, m, acc), X.XPath.rev(n, b, m, bcc)) == XP.then(Word.cmp(n, a, b), XP.cmp(m, acc, bcc)) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match a b:
        case WCon{+x, +at} WCon{+y, +bt}:
          Equal.trans(Cmp, XP.cmp(X.XPath.plus(p, 1n+m), X.XPath.rev(p, at, 1n+m, WCon{x, acc}), X.XPath.rev(p, bt, 1n+m, WCon{y, bcc})), XP.then(Word.cmp(p, at, bt), XP.then(Bool.cmp(x, y), XP.cmp(m, acc, bcc))), XP.then(Word.cmp.fin(x, y, Word.cmp(p, at, bt)), XP.cmp(m, acc, bcc)), XP.cmp_rev(p, at, bt, 1n+m, WCon{x, acc}, WCon{y, bcc}), Equal.sym(Cmp, XP.then(Word.cmp.fin(x, y, Word.cmp(p, at, bt)), XP.cmp(m, acc, bcc)), XP.then(Word.cmp(p, at, bt), XP.then(Bool.cmp(x, y), XP.cmp(m, acc, bcc))), XP.then_fin(Word.cmp(p, at, bt), x, y, XP.cmp(m, acc, bcc))))

def XP.path_cmp(i: U32, j: U32) -> {XP.cmp(32n, X.XArray.path(i), X.XArray.path(j)) == U32.cmp(i, j) : Cmp}:
  match i j:
    case U32{+w} U32{+v}:
      Equal.trans(Cmp, XP.cmp(32n, X.XArray.path(U32{w}), X.XArray.path(U32{v})), XP.then(Word.cmp(32n, w, v), EQ{}), Word.cmp(32n, w, v), XP.cmp_rev(32n, w, v, 0n, WNil{}, WNil{}), XP.then_eq(Word.cmp(32n, w, v)))

# Loads and stores on paths

def XP.load_nil(-V: Data, n: Nat, p: Word(n)) -> {X.XTree.load(V, n, p, X.XNil{}) == None{} : Maybe<&2, V>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      match p:
        case WCon{b, bs}:
          match b:
            case False{}:
              {==}
            case True{}:
              {==}

def XP.load_store(-V: Data, n: Nat, +p: Word(n), t: X.XTree<V>, v: V) -> {X.XTree.load(V, n, p, X.XTree.store(V, n, p, t, v)) == Some{v} : Maybe<&2, V>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      match p:
        case WCon{b, bs}:
          match b:
            case False{}:
              match t:
                case X.XBin{lo, hi}:
                  XP.load_store(V, m, bs, lo, v)
                case X.XNil{}:
                  XP.load_store(V, m, bs, X.XNil{}, v)
                case X.XLeaf{w}:
                  XP.load_store(V, m, bs, X.XNil{}, v)
            case True{}:
              match t:
                case X.XBin{lo, hi}:
                  XP.load_store(V, m, bs, hi, v)
                case X.XNil{}:
                  XP.load_store(V, m, bs, X.XNil{}, v)
                case X.XLeaf{w}:
                  XP.load_store(V, m, bs, X.XNil{}, v)

def XP.load_store_other(-V: Data, n: Nat, p: Word(n), q: Word(n), t: X.XTree<V>, v: V, e: {Cmp.is_eq(XP.cmp(n, p, q)) == False{} : Bool}) -> {X.XTree.load(V, n, q, X.XTree.store(V, n, p, t, v)) == X.XTree.load(V, n, q, t) : Maybe<&2, V>}:
  match n:
    case 0n:
      Empty.absurd({X.XTree.load(V, 0n, q, X.XTree.store(V, 0n, p, t, v)) == X.XTree.load(V, 0n, q, t) : Maybe<&2, V>}, XP.tf(e))
    case 1n+ +m:
      match p:
        case WCon{b, bs}:
          match b:
            case False{}:
              match q:
                case WCon{c, +cs}:
                  match c:
                    case False{}:
                      match t:
                        case X.XBin{lo, hi}:
                          XP.load_store_other(V, m, bs, cs, lo, v, e)
                        case X.XNil{}:
                          Equal.trans(Maybe<&2, V>, X.XTree.load(V, m, cs, X.XTree.store(V, m, bs, X.XNil{}, v)), X.XTree.load(V, m, cs, X.XNil{}), None{}, XP.load_store_other(V, m, bs, cs, X.XNil{}, v, e), XP.load_nil(V, m, cs))
                        case X.XLeaf{w}:
                          Equal.trans(Maybe<&2, V>, X.XTree.load(V, m, cs, X.XTree.store(V, m, bs, X.XNil{}, v)), X.XTree.load(V, m, cs, X.XNil{}), None{}, XP.load_store_other(V, m, bs, cs, X.XNil{}, v, e), XP.load_nil(V, m, cs))
                    case True{}:
                      match t:
                        case X.XBin{lo, hi}:
                          {==}
                        case X.XNil{}:
                          XP.load_nil(V, m, cs)
                        case X.XLeaf{w}:
                          XP.load_nil(V, m, cs)
            case True{}:
              match q:
                case WCon{c, +cs}:
                  match c:
                    case False{}:
                      match t:
                        case X.XBin{lo, hi}:
                          {==}
                        case X.XNil{}:
                          XP.load_nil(V, m, cs)
                        case X.XLeaf{w}:
                          XP.load_nil(V, m, cs)
                    case True{}:
                      match t:
                        case X.XBin{lo, hi}:
                          XP.load_store_other(V, m, bs, cs, hi, v, e)
                        case X.XNil{}:
                          Equal.trans(Maybe<&2, V>, X.XTree.load(V, m, cs, X.XTree.store(V, m, bs, X.XNil{}, v)), X.XTree.load(V, m, cs, X.XNil{}), None{}, XP.load_store_other(V, m, bs, cs, X.XNil{}, v, e), XP.load_nil(V, m, cs))
                        case X.XLeaf{w}:
                          Equal.trans(Maybe<&2, V>, X.XTree.load(V, m, cs, X.XTree.store(V, m, bs, X.XNil{}, v)), X.XTree.load(V, m, cs, X.XNil{}), None{}, XP.load_store_other(V, m, bs, cs, X.XNil{}, v, e), XP.load_nil(V, m, cs))

# A path read back as an index gives the path again, and an index read as a
# path gives the index again: both by splitting the word into its 32 bits.

def XP.path_index(q: Word(32n)) -> {X.XArray.path(X.XArray.index(q)) == q : Word(32n)}:
  match q:
    case WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def XP.index_path(i: U32) -> {X.XArray.index(X.XArray.path(i)) == i : U32}:
  match i:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# Erasing

def XP.join_lo(-V: Data, m: Nat, +cs: Word(m), l: X.XTree<V>, h: X.XTree<V>) -> {X.XTree.load(V, 1n+m, WCon{False{}, cs}, X.XTree.join(V, l, h)) == X.XTree.load(V, m, cs, l) : Maybe<&2, V>}:
  match l:
    case X.XNil{}:
      match h:
        case X.XNil{}:
          Equal.sym(Maybe<&2, V>, X.XTree.load(V, m, cs, X.XNil{}), None{}, XP.load_nil(V, m, cs))
        case X.XLeaf{v}:
          {==}
        case X.XBin{a, b}:
          {==}
    case X.XLeaf{v}:
      {==}
    case X.XBin{a, b}:
      {==}

def XP.join_hi(-V: Data, m: Nat, +cs: Word(m), l: X.XTree<V>, h: X.XTree<V>) -> {X.XTree.load(V, 1n+m, WCon{True{}, cs}, X.XTree.join(V, l, h)) == X.XTree.load(V, m, cs, h) : Maybe<&2, V>}:
  match l:
    case X.XNil{}:
      match h:
        case X.XNil{}:
          Equal.sym(Maybe<&2, V>, X.XTree.load(V, m, cs, X.XNil{}), None{}, XP.load_nil(V, m, cs))
        case X.XLeaf{v}:
          {==}
        case X.XBin{a, b}:
          {==}
    case X.XLeaf{v}:
      {==}
    case X.XBin{a, b}:
      {==}

def XP.load_erase(-V: Data, n: Nat, +p: Word(n), t: X.XTree<V>) -> {X.XTree.load(V, n, p, X.XTree.erase(V, n, p, t)) == None{} : Maybe<&2, V>}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      match p:
        case WCon{b, +bs}:
          match b:
            case False{}:
              match t:
                case X.XBin{+lo, +hi}:
                  Equal.trans(Maybe<&2, V>, X.XTree.load(V, 1n+m, WCon{False{}, bs}, X.XTree.join(V, X.XTree.erase(V, m, bs, lo), hi)), X.XTree.load(V, m, bs, X.XTree.erase(V, m, bs, lo)), None{}, XP.join_lo(V, m, bs, X.XTree.erase(V, m, bs, lo), hi), XP.load_erase(V, m, bs, lo))
                case X.XNil{}:
                  {==}
                case X.XLeaf{v}:
                  {==}
            case True{}:
              match t:
                case X.XBin{+lo, +hi}:
                  Equal.trans(Maybe<&2, V>, X.XTree.load(V, 1n+m, WCon{True{}, bs}, X.XTree.join(V, lo, X.XTree.erase(V, m, bs, hi))), X.XTree.load(V, m, bs, X.XTree.erase(V, m, bs, hi)), None{}, XP.join_hi(V, m, bs, lo, X.XTree.erase(V, m, bs, hi)), XP.load_erase(V, m, bs, hi))
                case X.XNil{}:
                  {==}
                case X.XLeaf{v}:
                  {==}

def XP.load_erase_other(-V: Data, n: Nat, p: Word(n), q: Word(n), t: X.XTree<V>, e: {Cmp.is_eq(XP.cmp(n, p, q)) == False{} : Bool}) -> {X.XTree.load(V, n, q, X.XTree.erase(V, n, p, t)) == X.XTree.load(V, n, q, t) : Maybe<&2, V>}:
  match n:
    case 0n:
      Empty.absurd({X.XTree.load(V, 0n, q, X.XTree.erase(V, 0n, p, t)) == X.XTree.load(V, 0n, q, t) : Maybe<&2, V>}, XP.tf(e))
    case 1n+ +m:
      match p:
        case WCon{b, +bs}:
          match b:
            case False{}:
              match q:
                case WCon{c, +cs}:
                  match c:
                    case False{}:
                      match t:
                        case X.XBin{+lo, +hi}:
                          Equal.trans(Maybe<&2, V>, X.XTree.load(V, 1n+m, WCon{False{}, cs}, X.XTree.join(V, X.XTree.erase(V, m, bs, lo), hi)), X.XTree.load(V, m, cs, X.XTree.erase(V, m, bs, lo)), X.XTree.load(V, m, cs, lo), XP.join_lo(V, m, cs, X.XTree.erase(V, m, bs, lo), hi), XP.load_erase_other(V, m, bs, cs, lo, e))
                        case X.XNil{}:
                          {==}
                        case X.XLeaf{v}:
                          {==}
                    case True{}:
                      match t:
                        case X.XBin{+lo, +hi}:
                          XP.join_hi(V, m, cs, X.XTree.erase(V, m, bs, lo), hi)
                        case X.XNil{}:
                          {==}
                        case X.XLeaf{v}:
                          {==}
            case True{}:
              match q:
                case WCon{c, +cs}:
                  match c:
                    case False{}:
                      match t:
                        case X.XBin{+lo, +hi}:
                          XP.join_lo(V, m, cs, lo, X.XTree.erase(V, m, bs, hi))
                        case X.XNil{}:
                          {==}
                        case X.XLeaf{v}:
                          {==}
                    case True{}:
                      match t:
                        case X.XBin{+lo, +hi}:
                          Equal.trans(Maybe<&2, V>, X.XTree.load(V, 1n+m, WCon{True{}, cs}, X.XTree.join(V, lo, X.XTree.erase(V, m, bs, hi))), X.XTree.load(V, m, cs, X.XTree.erase(V, m, bs, hi)), X.XTree.load(V, m, cs, hi), XP.join_hi(V, m, cs, lo, X.XTree.erase(V, m, bs, hi)), XP.load_erase_other(V, m, bs, cs, hi, e))
                        case X.XNil{}:
                          {==}
                        case X.XLeaf{v}:
                          {==}

# Searching. d is the direction: False orders paths upward, True downward.

def XP.dcmp(d: Bool, n: Nat, a: Word(n), b: Word(n)) -> Cmp:
  match d:
    case False{}:
      XP.cmp(n, a, b)
    case True{}:
      XP.cmp(n, b, a)

def XP.side(-V: Data, b: Bool, lo: X.XTree<V>, hi: X.XTree<V>) -> X.XTree<V>:
  match b:
    case False{}:
      lo
    case True{}:
      hi

# the extreme path in direction d is at or before every path
def XP.fill_ok(d: Bool, n: Nat, r: Word(n)) -> {Cmp.is_le(XP.dcmp(d, n, X.XPath.fill(n, d), r)) == True{} : Bool}:
  match d:
    case False{}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          match r:
            case WCon{c, cs}:
              match c:
                case False{}:
                  XP.fill_ok(False{}, m, cs)
                case True{}:
                  {==}
    case True{}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          match r:
            case WCon{c, cs}:
              match c:
                case False{}:
                  {==}
                case True{}:
                  XP.fill_ok(True{}, m, cs)

# What a search result promises, as types over the result

# the path found holds an entry
def XP.IsIn(-V: Data, +n: Nat, +t: X.XTree<V>, r: Maybe<&2, Word(n)>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{q}:
      {Maybe.is_some(&2, V, X.XTree.load(V, n, q, t)) == True{} : Bool}

# the path found is at or after p
def XP.After(+d: Bool, +n: Nat, +p: Word(n), r: Maybe<&2, Word(n)>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{q}:
      {Cmp.is_le(XP.dcmp(d, n, p, q)) == True{} : Bool}

# when nothing is found, nothing is at r if r is at or after p
def XP.NoneAt(-V: Data, +d: Bool, +n: Nat, +p: Word(n), +t: X.XTree<V>, +r: Word(n), res: Maybe<&2, Word(n)>) -> Type:
  match res:
    case None{}:
      {Cmp.is_le(XP.dcmp(d, n, p, r)) == True{} : Bool} -> {X.XTree.load(V, n, r, t) == None{} : Maybe<&2, V>}
    case Some{q}:
      Unit

# when q is found, nothing is at r if r lies between p and q
def XP.MinAt(-V: Data, +d: Bool, +n: Nat, +p: Word(n), +t: X.XTree<V>, +r: Word(n), res: Maybe<&2, Word(n)>) -> Type:
  match res:
    case None{}:
      Unit
    case Some{q}:
      {Cmp.is_le(XP.dcmp(d, n, p, r)) == True{} : Bool} -> {Cmp.is_lt(XP.dcmp(d, n, r, q)) == True{} : Bool} -> {X.XTree.load(V, n, r, t) == None{} : Maybe<&2, V>}

# Soundness: the path found holds an entry

def XP.in_pre(-V: Data, -m: Nat, -lo: X.XTree<V>, -hi: X.XTree<V>, b: Bool, r: Maybe<&2, Word(m)>, ih: XP.IsIn(V, m, XP.side(V, b, lo, hi), r)) -> XP.IsIn(V, 1n+m, X.XBin{lo, hi}, X.XTree.pre(m, b, r)):
  match b:
    case False{}:
      match r:
        case None{}:
          Unit{}
        case Some{q}:
          ih
    case True{}:
      match r:
        case None{}:
          Unit{}
        case Some{q}:
          ih

def XP.in_or(-V: Data, -n: Nat, -t: X.XTree<V>, r: Maybe<&2, Word(n)>, ih1: XP.IsIn(V, n, t, r), -k: Unit -> Maybe<&2, Word(n)>, ih2: XP.IsIn(V, n, t, k(Unit{}))) -> XP.IsIn(V, n, t, X.XTree.orelse(n, r, k)):
  match r:
    case None{}:
      ih2
    case Some{q}:
      ih1

def XP.seek_in(-V: Data, n: Nat, p: Word(n), t: X.XTree<V>, d: Bool) -> XP.IsIn(V, n, t, X.XTree.seek(V, n, p, t, d)):
  match n:
    case 0n:
      match t:
        case X.XLeaf{v}:
          {==}
        case X.XNil{}:
          Unit{}
        case X.XBin{lo, hi}:
          Unit{}
    case 1n+ +m:
      match p:
        case WCon{b, +bs}:
          match b:
            case False{}:
              match t:
                case X.XBin{+lo, +hi}:
                  match d:
                    case False{}:
                      XP.in_or(V, 1n+m, X.XBin{lo, hi}, X.XTree.pre(m, False{}, X.XTree.seek(V, m, bs, lo, False{})), XP.in_pre(V, m, lo, hi, False{}, X.XTree.seek(V, m, bs, lo, False{}), XP.seek_in(V, m, bs, lo, False{})), u => X.XTree.pre(m, True{}, X.XTree.seek(V, m, X.XPath.fill(m, False{}), hi, False{})), XP.in_pre(V, m, lo, hi, True{}, X.XTree.seek(V, m, X.XPath.fill(m, False{}), hi, False{}), XP.seek_in(V, m, X.XPath.fill(m, False{}), hi, False{})))
                    case True{}:
                      XP.in_pre(V, m, lo, hi, False{}, X.XTree.seek(V, m, bs, lo, True{}), XP.seek_in(V, m, bs, lo, True{}))
                case X.XNil{}:
                  Unit{}
                case X.XLeaf{v}:
                  Unit{}
            case True{}:
              match t:
                case X.XBin{+lo, +hi}:
                  match d:
                    case False{}:
                      XP.in_pre(V, m, lo, hi, True{}, X.XTree.seek(V, m, bs, hi, False{}), XP.seek_in(V, m, bs, hi, False{}))
                    case True{}:
                      XP.in_or(V, 1n+m, X.XBin{lo, hi}, X.XTree.pre(m, True{}, X.XTree.seek(V, m, bs, hi, True{})), XP.in_pre(V, m, lo, hi, True{}, X.XTree.seek(V, m, bs, hi, True{}), XP.seek_in(V, m, bs, hi, True{})), u => X.XTree.pre(m, False{}, X.XTree.seek(V, m, X.XPath.fill(m, True{}), lo, True{})), XP.in_pre(V, m, lo, hi, False{}, X.XTree.seek(V, m, X.XPath.fill(m, True{}), lo, True{}), XP.seek_in(V, m, X.XPath.fill(m, True{}), lo, True{})))
                case X.XNil{}:
                  Unit{}
                case X.XLeaf{v}:
                  Unit{}

# The path found is at or after the start

def XP.after_pre_same(d: Bool, -m: Nat, b: Bool, -bs: Word(m), r: Maybe<&2, Word(m)>, ih: XP.After(d, m, bs, r)) -> XP.After(d, 1n+m, WCon{b, bs}, X.XTree.pre(m, b, r)):
  match d:
    case False{}:
      match b:
        case False{}:
          match r:
            case None{}:
              Unit{}
            case Some{q}:
              ih
        case True{}:
          match r:
            case None{}:
              Unit{}
            case Some{q}:
              ih
    case True{}:
      match b:
        case False{}:
          match r:
            case None{}:
              Unit{}
            case Some{q}:
              ih
        case True{}:
          match r:
            case None{}:
              Unit{}
            case Some{q}:
              ih

def XP.after_pre_jump(d: Bool, -m: Nat, -bs: Word(m), r: Maybe<&2, Word(m)>) -> XP.After(d, 1n+m, WCon{d, bs}, X.XTree.pre(m, Bool.not(d), r)):
  match d:
    case False{}:
      match r:
        case None{}:
          Unit{}
        case Some{q}:
          {==}
    case True{}:
      match r:
        case None{}:
          Unit{}
        case Some{q}:
          {==}

def XP.after_or(-d: Bool, -n: Nat, -p: Word(n), r: Maybe<&2, Word(n)>, ih1: XP.After(d, n, p, r), -k: Unit -> Maybe<&2, Word(n)>, ih2: XP.After(d, n, p, k(Unit{}))) -> XP.After(d, n, p, X.XTree.orelse(n, r, k)):
  match r:
    case None{}:
      ih2
    case Some{q}:
      ih1

def XP.seek_after(-V: Data, n: Nat, p: Word(n), t: X.XTree<V>, d: Bool) -> XP.After(d, n, p, X.XTree.seek(V, n, p, t, d)):
  match n:
    case 0n:
      match t:
        case X.XLeaf{v}:
          match d:
            case False{}:
              {==}
            case True{}:
              {==}
        case X.XNil{}:
          Unit{}
        case X.XBin{lo, hi}:
          Unit{}
    case 1n+ +m:
      match p:
        case WCon{b, +bs}:
          match b:
            case False{}:
              match t:
                case X.XBin{+lo, +hi}:
                  match d:
                    case False{}:
                      XP.after_or(False{}, 1n+m, WCon{False{}, bs}, X.XTree.pre(m, False{}, X.XTree.seek(V, m, bs, lo, False{})), XP.after_pre_same(False{}, m, False{}, bs, X.XTree.seek(V, m, bs, lo, False{}), XP.seek_after(V, m, bs, lo, False{})), u => X.XTree.pre(m, True{}, X.XTree.seek(V, m, X.XPath.fill(m, False{}), hi, False{})), XP.after_pre_jump(False{}, m, bs, X.XTree.seek(V, m, X.XPath.fill(m, False{}), hi, False{})))
                    case True{}:
                      XP.after_pre_same(True{}, m, False{}, bs, X.XTree.seek(V, m, bs, lo, True{}), XP.seek_after(V, m, bs, lo, True{}))
                case X.XNil{}:
                  Unit{}
                case X.XLeaf{v}:
                  Unit{}
            case True{}:
              match t:
                case X.XBin{+lo, +hi}:
                  match d:
                    case False{}:
                      XP.after_pre_same(False{}, m, True{}, bs, X.XTree.seek(V, m, bs, hi, False{}), XP.seek_after(V, m, bs, hi, False{}))
                    case True{}:
                      XP.after_or(True{}, 1n+m, WCon{True{}, bs}, X.XTree.pre(m, True{}, X.XTree.seek(V, m, bs, hi, True{})), XP.after_pre_same(True{}, m, True{}, bs, X.XTree.seek(V, m, bs, hi, True{}), XP.seek_after(V, m, bs, hi, True{})), u => X.XTree.pre(m, False{}, X.XTree.seek(V, m, X.XPath.fill(m, True{}), lo, True{})), XP.after_pre_jump(True{}, m, bs, X.XTree.seek(V, m, X.XPath.fill(m, True{}), lo, True{})))
                case X.XNil{}:
                  Unit{}
                case X.XLeaf{v}:
                  Unit{}

# Completeness: when nothing is found, no path at or after the start holds an
# entry

def XP.none2(-V: Data, d: Bool, +m: Nat, -lo: X.XTree<V>, -hi: X.XTree<V>, -bs: Word(m), c: Bool, +cs: Word(m), r1: Maybe<&2, Word(m)>, ih1: XP.NoneAt(V, d, m, bs, XP.side(V, d, lo, hi), cs, r1), r2: Maybe<&2, Word(m)>, ih2: XP.NoneAt(V, d, m, X.XPath.fill(m, d), XP.side(V, Bool.not(d), lo, hi), cs, r2)) -> XP.NoneAt(V, d, 1n+m, WCon{d, bs}, X.XBin{lo, hi}, WCon{c, cs}, X.XTree.orelse(1n+m, X.XTree.pre(m, d, r1), u => X.XTree.pre(m, Bool.not(d), r2))):
  match d:
    case False{}:
      match c:
        case False{}:
          match r1:
            case None{}:
              match r2:
                case None{}:
                  ih1
                case Some{q}:
                  Unit{}
            case Some{q}:
              Unit{}
        case True{}:
          match r1:
            case None{}:
              match r2:
                case None{}:
                  h => ih2(XP.fill_ok(False{}, m, cs))
                case Some{q}:
                  Unit{}
            case Some{q}:
              Unit{}
    case True{}:
      match c:
        case False{}:
          match r1:
            case None{}:
              match r2:
                case None{}:
                  h => ih2(XP.fill_ok(True{}, m, cs))
                case Some{q}:
                  Unit{}
            case Some{q}:
              Unit{}
        case True{}:
          match r1:
            case None{}:
              match r2:
                case None{}:
                  ih1
                case Some{q}:
                  Unit{}
            case Some{q}:
              Unit{}

def XP.none_pre(-V: Data, d: Bool, -m: Nat, -lo: X.XTree<V>, -hi: X.XTree<V>, -bs: Word(m), c: Bool, -cs: Word(m), r: Maybe<&2, Word(m)>, ih: XP.NoneAt(V, d, m, bs, XP.side(V, Bool.not(d), lo, hi), cs, r)) -> XP.NoneAt(V, d, 1n+m, WCon{Bool.not(d), bs}, X.XBin{lo, hi}, WCon{c, cs}, X.XTree.pre(m, Bool.not(d), r)):
  match d:
    case False{}:
      match c:
        case False{}:
          match r:
            case None{}:
              h => Empty.absurd({X.XTree.load(V, 1n+m, WCon{False{}, cs}, X.XBin{lo, hi}) == None{} : Maybe<&2, V>}, XP.ft(h))
            case Some{q}:
              Unit{}
        case True{}:
          match r:
            case None{}:
              ih
            case Some{q}:
              Unit{}
    case True{}:
      match c:
        case False{}:
          match r:
            case None{}:
              ih
            case Some{q}:
              Unit{}
        case True{}:
          match r:
            case None{}:
              h => Empty.absurd({X.XTree.load(V, 1n+m, WCon{True{}, cs}, X.XBin{lo, hi}) == None{} : Maybe<&2, V>}, XP.ft(h))
            case Some{q}:
              Unit{}

def XP.seek_none(-V: Data, n: Nat, p: Word(n), t: X.XTree<V>, d: Bool, r: Word(n)) -> XP.NoneAt(V, d, n, p, t, r, X.XTree.seek(V, n, p, t, d)):
  match n:
    case 0n:
      match t:
        case X.XLeaf{v}:
          Unit{}
        case X.XNil{}:
          h => {==}
        case X.XBin{lo, hi}:
          h => {==}
    case 1n+ +m:
      match p:
        case WCon{b, +bs}:
          match b:
            case False{}:
              match t:
                case X.XBin{+lo, +hi}:
                  match d:
                    case False{}:
                      match r:
                        case WCon{c, +cs}:
                          XP.none2(V, False{}, m, lo, hi, bs, c, cs, X.XTree.seek(V, m, bs, lo, False{}), XP.seek_none(V, m, bs, lo, False{}, cs), X.XTree.seek(V, m, X.XPath.fill(m, False{}), hi, False{}), XP.seek_none(V, m, X.XPath.fill(m, False{}), hi, False{}, cs))
                    case True{}:
                      match r:
                        case WCon{c, +cs}:
                          XP.none_pre(V, True{}, m, lo, hi, bs, c, cs, X.XTree.seek(V, m, bs, lo, True{}), XP.seek_none(V, m, bs, lo, True{}, cs))
                case X.XNil{}:
                  match r:
                    case WCon{c, cs}:
                      match c:
                        case False{}:
                          h => {==}
                        case True{}:
                          h => {==}
                case X.XLeaf{v}:
                  match r:
                    case WCon{c, cs}:
                      match c:
                        case False{}:
                          h => {==}
                        case True{}:
                          h => {==}
            case True{}:
              match t:
                case X.XBin{+lo, +hi}:
                  match d:
                    case False{}:
                      match r:
                        case WCon{c, +cs}:
                          XP.none_pre(V, False{}, m, lo, hi, bs, c, cs, X.XTree.seek(V, m, bs, hi, False{}), XP.seek_none(V, m, bs, hi, False{}, cs))
                    case True{}:
                      match r:
                        case WCon{c, +cs}:
                          XP.none2(V, True{}, m, lo, hi, bs, c, cs, X.XTree.seek(V, m, bs, hi, True{}), XP.seek_none(V, m, bs, hi, True{}, cs), X.XTree.seek(V, m, X.XPath.fill(m, True{}), lo, True{}), XP.seek_none(V, m, X.XPath.fill(m, True{}), lo, True{}, cs))
                case X.XNil{}:
                  match r:
                    case WCon{c, cs}:
                      match c:
                        case False{}:
                          h => {==}
                        case True{}:
                          h => {==}
                case X.XLeaf{v}:
                  match r:
                    case WCon{c, cs}:
                      match c:
                        case False{}:
                          h => {==}
                        case True{}:
                          h => {==}

# Minimality: when q is found, no path between the start and q holds an entry

def XP.min2(-V: Data, d: Bool, +m: Nat, -lo: X.XTree<V>, -hi: X.XTree<V>, -bs: Word(m), c: Bool, +cs: Word(m), r1: Maybe<&2, Word(m)>, ih1m: XP.MinAt(V, d, m, bs, XP.side(V, d, lo, hi), cs, r1), ih1n: XP.NoneAt(V, d, m, bs, XP.side(V, d, lo, hi), cs, r1), r2: Maybe<&2, Word(m)>, ih2m: XP.MinAt(V, d, m, X.XPath.fill(m, d), XP.side(V, Bool.not(d), lo, hi), cs, r2)) -> XP.MinAt(V, d, 1n+m, WCon{d, bs}, X.XBin{lo, hi}, WCon{c, cs}, X.XTree.orelse(1n+m, X.XTree.pre(m, d, r1), u => X.XTree.pre(m, Bool.not(d), r2))):
  match d:
    case False{}:
      match c:
        case False{}:
          match r1:
            case None{}:
              match r2:
                case None{}:
                  Unit{}
                case Some{q}:
                  h1 => h2 => ih1n(h1)
            case Some{q}:
              ih1m
        case True{}:
          match r1:
            case None{}:
              match r2:
                case None{}:
                  Unit{}
                case Some{q}:
                  h1 => h2 => ih2m(XP.fill_ok(False{}, m, cs))(h2)
            case Some{q}:
              h1 => h2 => Empty.absurd({X.XTree.load(V, 1n+m, WCon{True{}, cs}, X.XBin{lo, hi}) == None{} : Maybe<&2, V>}, XP.ft(h2))
    case True{}:
      match c:
        case False{}:
          match r1:
            case None{}:
              match r2:
                case None{}:
                  Unit{}
                case Some{q}:
                  h1 => h2 => ih2m(XP.fill_ok(True{}, m, cs))(h2)
            case Some{q}:
              h1 => h2 => Empty.absurd({X.XTree.load(V, 1n+m, WCon{False{}, cs}, X.XBin{lo, hi}) == None{} : Maybe<&2, V>}, XP.ft(h2))
        case True{}:
          match r1:
            case None{}:
              match r2:
                case None{}:
                  Unit{}
                case Some{q}:
                  h1 => h2 => ih1n(h1)
            case Some{q}:
              ih1m

def XP.min_pre(-V: Data, d: Bool, -m: Nat, -lo: X.XTree<V>, -hi: X.XTree<V>, -bs: Word(m), c: Bool, -cs: Word(m), r: Maybe<&2, Word(m)>, ih: XP.MinAt(V, d, m, bs, XP.side(V, Bool.not(d), lo, hi), cs, r)) -> XP.MinAt(V, d, 1n+m, WCon{Bool.not(d), bs}, X.XBin{lo, hi}, WCon{c, cs}, X.XTree.pre(m, Bool.not(d), r)):
  match d:
    case False{}:
      match c:
        case False{}:
          match r:
            case None{}:
              Unit{}
            case Some{q}:
              h1 => h2 => Empty.absurd({X.XTree.load(V, 1n+m, WCon{False{}, cs}, X.XBin{lo, hi}) == None{} : Maybe<&2, V>}, XP.ft(h1))
        case True{}:
          match r:
            case None{}:
              Unit{}
            case Some{q}:
              ih
    case True{}:
      match c:
        case False{}:
          match r:
            case None{}:
              Unit{}
            case Some{q}:
              ih
        case True{}:
          match r:
            case None{}:
              Unit{}
            case Some{q}:
              h1 => h2 => Empty.absurd({X.XTree.load(V, 1n+m, WCon{True{}, cs}, X.XBin{lo, hi}) == None{} : Maybe<&2, V>}, XP.ft(h1))

def XP.seek_min(-V: Data, n: Nat, p: Word(n), t: X.XTree<V>, d: Bool, r: Word(n)) -> XP.MinAt(V, d, n, p, t, r, X.XTree.seek(V, n, p, t, d)):
  match n:
    case 0n:
      match t:
        case X.XLeaf{v}:
          match d:
            case False{}:
              h1 => h2 => Empty.absurd({X.XTree.load(V, 0n, r, X.XLeaf{v}) == None{} : Maybe<&2, V>}, XP.ft(h2))
            case True{}:
              h1 => h2 => Empty.absurd({X.XTree.load(V, 0n, r, X.XLeaf{v}) == None{} : Maybe<&2, V>}, XP.ft(h2))
        case X.XNil{}:
          Unit{}
        case X.XBin{lo, hi}:
          Unit{}
    case 1n+ +m:
      match p:
        case WCon{b, +bs}:
          match b:
            case False{}:
              match t:
                case X.XBin{+lo, +hi}:
                  match d:
                    case False{}:
                      match r:
                        case WCon{c, +cs}:
                          XP.min2(V, False{}, m, lo, hi, bs, c, cs, X.XTree.seek(V, m, bs, lo, False{}), XP.seek_min(V, m, bs, lo, False{}, cs), XP.seek_none(V, m, bs, lo, False{}, cs), X.XTree.seek(V, m, X.XPath.fill(m, False{}), hi, False{}), XP.seek_min(V, m, X.XPath.fill(m, False{}), hi, False{}, cs))
                    case True{}:
                      match r:
                        case WCon{c, +cs}:
                          XP.min_pre(V, True{}, m, lo, hi, bs, c, cs, X.XTree.seek(V, m, bs, lo, True{}), XP.seek_min(V, m, bs, lo, True{}, cs))
                case X.XNil{}:
                  Unit{}
                case X.XLeaf{v}:
                  Unit{}
            case True{}:
              match t:
                case X.XBin{+lo, +hi}:
                  match d:
                    case False{}:
                      match r:
                        case WCon{c, +cs}:
                          XP.min_pre(V, False{}, m, lo, hi, bs, c, cs, X.XTree.seek(V, m, bs, hi, False{}), XP.seek_min(V, m, bs, hi, False{}, cs))
                    case True{}:
                      match r:
                        case WCon{c, +cs}:
                          XP.min2(V, True{}, m, lo, hi, bs, c, cs, X.XTree.seek(V, m, bs, hi, True{}), XP.seek_min(V, m, bs, hi, True{}, cs), XP.seek_none(V, m, bs, hi, True{}, cs), X.XTree.seek(V, m, X.XPath.fill(m, True{}), lo, True{}), XP.seek_min(V, m, X.XPath.fill(m, True{}), lo, True{}, cs))
                case X.XNil{}:
                  Unit{}
                case X.XLeaf{v}:
                  Unit{}

# Iteration over a range

def XP.some_t(-A: Data, m: Maybe<&2, A>) -> Type:
  match m:
    case None{}:
      Empty
    case Some{x}:
      Unit

# None is not Some
def XP.none_some(-A: Data, -x: A, e: {None{} == Some{x} : Maybe<&2, A>}) -> Empty:
  %Equal.sym(Maybe<&2, A>, None{}, Some{x}, e) : XP.some_t(A, _)
  Unit{}

# Every entry listed lies in t, between a and b
def XP.Sound(-V: Data, +n: Nat, +t: X.XTree<V>, +a: Word(n), +b: Word(n), xs: List<&2, X.XAt<n, V>>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{h, rest}:
      match h:
        case X.XAt{+q, +v}:
          ({X.XTree.load(V, n, q, t) == Some{v} : Maybe<&2, V>} & ({Cmp.is_le(XP.cmp(n, a, q)) == True{} : Bool} & {Cmp.is_le(XP.cmp(n, q, b)) == True{} : Bool})) & XP.Sound(V, n, t, a, b, rest)

def XP.sound_same(-V: Data, -m: Nat, b: Bool, -lo: X.XTree<V>, -hi: X.XTree<V>, -as: Word(m), -bs: Word(m), xs: List<&2, X.XAt<m, V>>, ev: XP.Sound(V, m, XP.side(V, b, lo, hi), as, bs, xs)) -> XP.Sound(V, 1n+m, X.XBin{lo, hi}, WCon{b, as}, WCon{b, bs}, X.XTree.tag(V, m, b, xs)):
  match b:
    case False{}:
      match xs:
        case Nil{}:
          Unit{}
        case Con{h, rest}:
          match h:
            case X.XAt{q, v}:
              match ev:
                case (e1, e2):
                  (e1, XP.sound_same(V, m, False{}, lo, hi, as, bs, rest, e2))
    case True{}:
      match xs:
        case Nil{}:
          Unit{}
        case Con{h, rest}:
          match h:
            case X.XAt{q, v}:
              match ev:
                case (e1, e2):
                  (e1, XP.sound_same(V, m, True{}, lo, hi, as, bs, rest, e2))

def XP.sound_left(-V: Data, +m: Nat, -lo: X.XTree<V>, -hi: X.XTree<V>, -as: Word(m), -bs: Word(m), xs: List<&2, X.XAt<m, V>>, ev: XP.Sound(V, m, lo, as, X.XPath.fill(m, True{}), xs)) -> XP.Sound(V, 1n+m, X.XBin{lo, hi}, WCon{False{}, as}, WCon{True{}, bs}, X.XTree.tag(V, m, False{}, xs)):
  match xs:
    case Nil{}:
      Unit{}
    case Con{h, rest}:
      match h:
        case X.XAt{q, v}:
          match ev:
            case (e1, e2):
              match e1:
                case (l, fg):
                  match fg:
                    case (f, g):
                      ((l, (f, {==})), XP.sound_left(V, m, lo, hi, as, bs, rest, e2))

def XP.sound_right(-V: Data, +m: Nat, -lo: X.XTree<V>, -hi: X.XTree<V>, -as: Word(m), -bs: Word(m), xs: List<&2, X.XAt<m, V>>, ev: XP.Sound(V, m, hi, X.XPath.fill(m, False{}), bs, xs)) -> XP.Sound(V, 1n+m, X.XBin{lo, hi}, WCon{False{}, as}, WCon{True{}, bs}, X.XTree.tag(V, m, True{}, xs)):
  match xs:
    case Nil{}:
      Unit{}
    case Con{h, rest}:
      match h:
        case X.XAt{q, v}:
          match ev:
            case (e1, e2):
              match e1:
                case (l, fg):
                  match fg:
                    case (f, g):
                      ((l, ({==}, g)), XP.sound_right(V, m, lo, hi, as, bs, rest, e2))

def XP.sound_append(-V: Data, -n: Nat, -t: X.XTree<V>, -a: Word(n), -b: Word(n), xs: List<&2, X.XAt<n, V>>, ys: List<&2, X.XAt<n, V>>, ex: XP.Sound(V, n, t, a, b, xs), ey: XP.Sound(V, n, t, a, b, ys)) -> XP.Sound(V, n, t, a, b, List.append(&2, X.XAt<n, V>, xs, ys)):
  match xs:
    case Nil{}:
      ey
    case Con{h, rest}:
      match h:
        case X.XAt{q, v}:
          match ex:
            case (e1, e2):
              (e1, XP.sound_append(V, n, t, a, b, rest, ys, e2, ey))

def XP.range_sound(-V: Data, n: Nat, t: X.XTree<V>, a: Word(n), b: Word(n)) -> XP.Sound(V, n, t, a, b, X.XTree.range(V, n, t, a, b)):
  match n:
    case 0n:
      match t:
        case X.XLeaf{v}:
          (({==}, ({==}, {==})), Unit{})
        case X.XNil{}:
          Unit{}
        case X.XBin{lo, hi}:
          Unit{}
    case 1n+ +m:
      match t:
        case X.XBin{+lo, +hi}:
          match a:
            case WCon{x, +as}:
              match x:
                case False{}:
                  match b:
                    case WCon{y, +bs}:
                      match y:
                        case False{}:
                          XP.sound_same(V, m, False{}, lo, hi, as, bs, X.XTree.range(V, m, lo, as, bs), XP.range_sound(V, m, lo, as, bs))
                        case True{}:
                          XP.sound_append(V, 1n+m, X.XBin{lo, hi}, WCon{False{}, as}, WCon{True{}, bs}, X.XTree.tag(V, m, False{}, X.XTree.range(V, m, lo, as, X.XPath.fill(m, True{}))), X.XTree.tag(V, m, True{}, X.XTree.range(V, m, hi, X.XPath.fill(m, False{}), bs)), XP.sound_left(V, m, lo, hi, as, bs, X.XTree.range(V, m, lo, as, X.XPath.fill(m, True{})), XP.range_sound(V, m, lo, as, X.XPath.fill(m, True{}))), XP.sound_right(V, m, lo, hi, as, bs, X.XTree.range(V, m, hi, X.XPath.fill(m, False{}), bs), XP.range_sound(V, m, hi, X.XPath.fill(m, False{}), bs)))
                case True{}:
                  match b:
                    case WCon{y, +bs}:
                      match y:
                        case False{}:
                          Unit{}
                        case True{}:
                          XP.sound_same(V, m, True{}, lo, hi, as, bs, X.XTree.range(V, m, hi, as, bs), XP.range_sound(V, m, hi, as, bs))
        case X.XNil{}:
          Unit{}
        case X.XLeaf{v}:
          Unit{}

# The entries listed are in strictly ascending order of path

def XP.SortedFrom(-V: Data, +n: Nat, xs: List<&2, X.XAt<n, V>>, +prev: Word(n)) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{h, rest}:
      match h:
        case X.XAt{+q, v}:
          {Cmp.is_lt(XP.cmp(n, prev, q)) == True{} : Bool} & XP.SortedFrom(V, n, rest, q)

def XP.Sorted(-V: Data, +n: Nat, xs: List<&2, X.XAt<n, V>>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{h, rest}:
      match h:
        case X.XAt{q, v}:
          XP.SortedFrom(V, n, rest, q)

def XP.sorted_tag_from(-V: Data, -m: Nat, b: Bool, xs: List<&2, X.XAt<m, V>>, -prev: Word(m), ev: XP.SortedFrom(V, m, xs, prev)) -> XP.SortedFrom(V, 1n+m, X.XTree.tag(V, m, b, xs), WCon{b, prev}):
  match b:
    case False{}:
      match xs:
        case Nil{}:
          Unit{}
        case Con{h, rest}:
          match h:
            case X.XAt{q, v}:
              match ev:
                case (l, e2):
                  (l, XP.sorted_tag_from(V, m, False{}, rest, q, e2))
    case True{}:
      match xs:
        case Nil{}:
          Unit{}
        case Con{h, rest}:
          match h:
            case X.XAt{q, v}:
              match ev:
                case (l, e2):
                  (l, XP.sorted_tag_from(V, m, True{}, rest, q, e2))

def XP.sorted_tag(-V: Data, -m: Nat, +b: Bool, xs: List<&2, X.XAt<m, V>>, ev: XP.Sorted(V, m, xs)) -> XP.Sorted(V, 1n+m, X.XTree.tag(V, m, b, xs)):
  match xs:
    case Nil{}:
      Unit{}
    case Con{h, rest}:
      match h:
        case X.XAt{q, v}:
          XP.sorted_tag_from(V, m, b, rest, q, ev)

def XP.sorted_join_from(-V: Data, -m: Nat, xs: List<&2, X.XAt<m, V>>, -prev: Word(m), ys: List<&2, X.XAt<m, V>>, ev: XP.SortedFrom(V, m, xs, prev), ey: XP.Sorted(V, m, ys)) -> XP.SortedFrom(V, 1n+m, List.append(&2, X.XAt<1n+m, V>, X.XTree.tag(V, m, False{}, xs), X.XTree.tag(V, m, True{}, ys)), WCon{False{}, prev}):
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          Unit{}
        case Con{h, rest}:
          match h:
            case X.XAt{q, v}:
              ({==}, XP.sorted_tag_from(V, m, True{}, rest, q, ey))
    case Con{h, rest}:
      match h:
        case X.XAt{q, v}:
          match ev:
            case (l, e2):
              (l, XP.sorted_join_from(V, m, rest, q, ys, e2, ey))

def XP.sorted_join(-V: Data, -m: Nat, xs: List<&2, X.XAt<m, V>>, ys: List<&2, X.XAt<m, V>>, ex: XP.Sorted(V, m, xs), ey: XP.Sorted(V, m, ys)) -> XP.Sorted(V, 1n+m, List.append(&2, X.XAt<1n+m, V>, X.XTree.tag(V, m, False{}, xs), X.XTree.tag(V, m, True{}, ys))):
  match xs:
    case Nil{}:
      XP.sorted_tag(V, m, True{}, ys, ey)
    case Con{h, rest}:
      match h:
        case X.XAt{q, v}:
          XP.sorted_join_from(V, m, rest, q, ys, ex, ey)

def XP.range_sorted(-V: Data, n: Nat, t: X.XTree<V>, a: Word(n), b: Word(n)) -> XP.Sorted(V, n, X.XTree.range(V, n, t, a, b)):
  match n:
    case 0n:
      match t:
        case X.XLeaf{v}:
          Unit{}
        case X.XNil{}:
          Unit{}
        case X.XBin{lo, hi}:
          Unit{}
    case 1n+ +m:
      match t:
        case X.XBin{+lo, +hi}:
          match a:
            case WCon{x, +as}:
              match x:
                case False{}:
                  match b:
                    case WCon{y, +bs}:
                      match y:
                        case False{}:
                          XP.sorted_tag(V, m, False{}, X.XTree.range(V, m, lo, as, bs), XP.range_sorted(V, m, lo, as, bs))
                        case True{}:
                          XP.sorted_join(V, m, X.XTree.range(V, m, lo, as, X.XPath.fill(m, True{})), X.XTree.range(V, m, hi, X.XPath.fill(m, False{}), bs), XP.range_sorted(V, m, lo, as, X.XPath.fill(m, True{})), XP.range_sorted(V, m, hi, X.XPath.fill(m, False{}), bs))
                case True{}:
                  match b:
                    case WCon{y, +bs}:
                      match y:
                        case False{}:
                          Unit{}
                        case True{}:
                          XP.sorted_tag(V, m, True{}, X.XTree.range(V, m, hi, as, bs), XP.range_sorted(V, m, hi, as, bs))
        case X.XNil{}:
          Unit{}
        case X.XLeaf{v}:
          Unit{}

# Every entry of t between a and b is listed

def XP.Mem(-V: Data, +n: Nat, +q: Word(n), +v: V, xs: List<&2, X.XAt<n, V>>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case Con{h, rest}:
      {h == X.XAt{q, v} : X.XAt<n, V>} | XP.Mem(V, n, q, v, rest)

def XP.tag_at(-V: Data, -m: Nat, b: Bool, e: X.XAt<m, V>) -> X.XAt<1n+m, V>:
  match e:
    case X.XAt{q, v}:
      X.XAt{WCon{b, q}, v}

def XP.mem_tag(-V: Data, +m: Nat, +b: Bool, -q: Word(m), -v: V, xs: List<&2, X.XAt<m, V>>, e: XP.Mem(V, m, q, v, xs)) -> XP.Mem(V, 1n+m, WCon{b, q}, v, X.XTree.tag(V, m, b, xs)):
  match xs:
    case Nil{}:
      match e:
    case Con{h, rest}:
      match h:
        case X.XAt{hq, hv}:
          match e:
            case Inl{eq}:
              Inl{Equal.cong(X.XAt<m, V>, X.XAt<1n+m, V>, z => XP.tag_at(V, m, b, z), X.XAt{hq, hv}, X.XAt{q, v}, eq)}
            case Inr{e2}:
              Inr{XP.mem_tag(V, m, b, q, v, rest, e2)}

def XP.mem_app_l(-V: Data, -n: Nat, -q: Word(n), -v: V, xs: List<&2, X.XAt<n, V>>, -ys: List<&2, X.XAt<n, V>>, e: XP.Mem(V, n, q, v, xs)) -> XP.Mem(V, n, q, v, List.append(&2, X.XAt<n, V>, xs, ys)):
  match xs:
    case Nil{}:
      match e:
    case Con{h, rest}:
      match e:
        case Inl{eq}:
          Inl{eq}
        case Inr{e2}:
          Inr{XP.mem_app_l(V, n, q, v, rest, ys, e2)}

def XP.mem_app_r(-V: Data, -n: Nat, -q: Word(n), -v: V, xs: List<&2, X.XAt<n, V>>, -ys: List<&2, X.XAt<n, V>>, e: XP.Mem(V, n, q, v, ys)) -> XP.Mem(V, n, q, v, List.append(&2, X.XAt<n, V>, xs, ys)):
  match xs:
    case Nil{}:
      e
    case Con{h, rest}:
      Inr{XP.mem_app_r(V, n, q, v, rest, ys, e)}

def XP.at_of(-V: Data, +w: V, mm: Maybe<&2, V>) -> X.XAt<0n, V>:
  X.XAt{WNil{}, Maybe.default(&2, V, mm, w)}

def XP.range_mem(-V: Data, n: Nat, t: X.XTree<V>, a: Word(n), b: Word(n), q: Word(n), v: V, h1: {Cmp.is_le(XP.cmp(n, a, q)) == True{} : Bool}, h2: {Cmp.is_le(XP.cmp(n, q, b)) == True{} : Bool}, h3: {X.XTree.load(V, n, q, t) == Some{v} : Maybe<&2, V>}) -> XP.Mem(V, n, q, v, X.XTree.range(V, n, t, a, b)):
  match n:
    case 0n:
      match t:
        case X.XLeaf{+w}:
          match q:
            case WNil{}:
              Inl{Equal.cong(Maybe<&2, V>, X.XAt<0n, V>, mm => XP.at_of(V, w, mm), Some{w}, Some{v}, h3)}
        case X.XNil{}:
          Empty.absurd(Empty, XP.none_some(V, v, h3))
        case X.XBin{lo, hi}:
          Empty.absurd(Empty, XP.none_some(V, v, h3))
    case 1n+ +m:
      match t:
        case X.XBin{+lo, +hi}:
          match a:
            case WCon{x, +as}:
              match x:
                case False{}:
                  match b:
                    case WCon{y, +bs}:
                      match y:
                        case False{}:
                          match q:
                            case WCon{c, +cs}:
                              match c:
                                case False{}:
                                  XP.mem_tag(V, m, False{}, cs, v, X.XTree.range(V, m, lo, as, bs), XP.range_mem(V, m, lo, as, bs, cs, v, h1, h2, h3))
                                case True{}:
                                  Empty.absurd(XP.Mem(V, 1n+m, WCon{True{}, cs}, v, X.XTree.tag(V, m, False{}, X.XTree.range(V, m, lo, as, bs))), XP.ft(h2))
                        case True{}:
                          match q:
                            case WCon{c, +cs}:
                              match c:
                                case False{}:
                                  XP.mem_app_l(V, 1n+m, WCon{False{}, cs}, v, X.XTree.tag(V, m, False{}, X.XTree.range(V, m, lo, as, X.XPath.fill(m, True{}))), X.XTree.tag(V, m, True{}, X.XTree.range(V, m, hi, X.XPath.fill(m, False{}), bs)), XP.mem_tag(V, m, False{}, cs, v, X.XTree.range(V, m, lo, as, X.XPath.fill(m, True{})), XP.range_mem(V, m, lo, as, X.XPath.fill(m, True{}), cs, v, h1, XP.fill_ok(True{}, m, cs), h3)))
                                case True{}:
                                  XP.mem_app_r(V, 1n+m, WCon{True{}, cs}, v, X.XTree.tag(V, m, False{}, X.XTree.range(V, m, lo, as, X.XPath.fill(m, True{}))), X.XTree.tag(V, m, True{}, X.XTree.range(V, m, hi, X.XPath.fill(m, False{}), bs)), XP.mem_tag(V, m, True{}, cs, v, X.XTree.range(V, m, hi, X.XPath.fill(m, False{}), bs), XP.range_mem(V, m, hi, X.XPath.fill(m, False{}), bs, cs, v, XP.fill_ok(False{}, m, cs), h2, h3)))
                case True{}:
                  match b:
                    case WCon{y, +bs}:
                      match y:
                        case False{}:
                          match q:
                            case WCon{c, +cs}:
                              match c:
                                case False{}:
                                  Empty.absurd(Empty, XP.ft(h1))
                                case True{}:
                                  Empty.absurd(Empty, XP.ft(h2))
                        case True{}:
                          match q:
                            case WCon{c, +cs}:
                              match c:
                                case False{}:
                                  Empty.absurd(XP.Mem(V, 1n+m, WCon{False{}, cs}, v, X.XTree.tag(V, m, True{}, X.XTree.range(V, m, hi, as, bs))), XP.ft(h1))
                                case True{}:
                                  XP.mem_tag(V, m, True{}, cs, v, X.XTree.range(V, m, hi, as, bs), XP.range_mem(V, m, hi, as, bs, cs, v, h1, h2, h3))
        case X.XNil{}:
          match q:
            case WCon{c, cs}:
              match c:
                case False{}:
                  Empty.absurd(Empty, XP.none_some(V, v, h3))
                case True{}:
                  Empty.absurd(Empty, XP.none_some(V, v, h3))
        case X.XLeaf{w}:
          match q:
            case WCon{c, cs}:
              match c:
                case False{}:
                  Empty.absurd(Empty, XP.none_some(V, v, h3))
                case True{}:
                  Empty.absurd(Empty, XP.none_some(V, v, h3))

# From U32 order to path order, and back

def XP.ne_path(+i: U32, +j: U32, e: {U32.is_eq(i, j) == False{} : Bool}) -> {Cmp.is_eq(XP.cmp(32n, X.XArray.path(i), X.XArray.path(j))) == False{} : Bool}:
  %Equal.sym(Cmp, XP.cmp(32n, X.XArray.path(i), X.XArray.path(j)), U32.cmp(i, j), XP.path_cmp(i, j)) : {Cmp.is_eq(_) == False{} : Bool}
  e

def XP.le_path(+i: U32, +j: U32, e: {U32.is_le(i, j) == True{} : Bool}) -> {Cmp.is_le(XP.cmp(32n, X.XArray.path(i), X.XArray.path(j))) == True{} : Bool}:
  %Equal.sym(Cmp, XP.cmp(32n, X.XArray.path(i), X.XArray.path(j)), U32.cmp(i, j), XP.path_cmp(i, j)) : {Cmp.is_le(_) == True{} : Bool}
  e

# i < index(q), as paths
def XP.lt_path_r(+j: U32, +q: Word(32n), e: {U32.is_lt(j, X.XArray.index(q)) == True{} : Bool}) -> {Cmp.is_lt(XP.cmp(32n, X.XArray.path(j), q)) == True{} : Bool}:
  %XP.path_index(q) : {Cmp.is_lt(XP.cmp(32n, X.XArray.path(j), _)) == True{} : Bool}
  %Equal.sym(Cmp, XP.cmp(32n, X.XArray.path(j), X.XArray.path(X.XArray.index(q))), U32.cmp(j, X.XArray.index(q)), XP.path_cmp(j, X.XArray.index(q))) : {Cmp.is_lt(_) == True{} : Bool}
  e

# index(q) < j, as paths
def XP.lt_path_l(+q: Word(32n), +j: U32, e: {U32.is_lt(X.XArray.index(q), j) == True{} : Bool}) -> {Cmp.is_lt(XP.cmp(32n, q, X.XArray.path(j))) == True{} : Bool}:
  %XP.path_index(q) : {Cmp.is_lt(XP.cmp(32n, _, X.XArray.path(j))) == True{} : Bool}
  %Equal.sym(Cmp, XP.cmp(32n, X.XArray.path(X.XArray.index(q)), X.XArray.path(j)), U32.cmp(X.XArray.index(q), j), XP.path_cmp(X.XArray.index(q), j)) : {Cmp.is_lt(_) == True{} : Bool}
  e

# i <= index(q), from paths
def XP.le_index_r(+i: U32, +q: Word(32n), e: {Cmp.is_le(XP.cmp(32n, X.XArray.path(i), q)) == True{} : Bool}) -> {U32.is_le(i, X.XArray.index(q)) == True{} : Bool}:
  %XP.path_cmp(i, X.XArray.index(q)) : {Cmp.is_le(_) == True{} : Bool}
  %Equal.sym(Word(32n), X.XArray.path(X.XArray.index(q)), q, XP.path_index(q)) : {Cmp.is_le(XP.cmp(32n, X.XArray.path(i), _)) == True{} : Bool}
  e

# index(q) <= i, from paths
def XP.le_index_l(+q: Word(32n), +i: U32, e: {Cmp.is_le(XP.cmp(32n, q, X.XArray.path(i))) == True{} : Bool}) -> {U32.is_le(X.XArray.index(q), i) == True{} : Bool}:
  %XP.path_cmp(X.XArray.index(q), i) : {Cmp.is_le(_) == True{} : Bool}
  %Equal.sym(Word(32n), X.XArray.path(X.XArray.index(q)), q, XP.path_index(q)) : {Cmp.is_le(XP.cmp(32n, _, X.XArray.path(i))) == True{} : Bool}
  e

# index(p) < index(q), from paths
def XP.lt_index(+p: Word(32n), +q: Word(32n), e: {Cmp.is_lt(XP.cmp(32n, p, q)) == True{} : Bool}) -> {U32.is_lt(X.XArray.index(p), X.XArray.index(q)) == True{} : Bool}:
  %XP.path_cmp(X.XArray.index(p), X.XArray.index(q)) : {Cmp.is_lt(_) == True{} : Bool}
  %Equal.sym(Word(32n), X.XArray.path(X.XArray.index(p)), p, XP.path_index(p)) : {Cmp.is_lt(XP.cmp(32n, _, X.XArray.path(X.XArray.index(q)))) == True{} : Bool}
  %Equal.sym(Word(32n), X.XArray.path(X.XArray.index(q)), q, XP.path_index(q)) : {Cmp.is_lt(XP.cmp(32n, p, _)) == True{} : Bool}
  e

def XP.conv_load(-V: Data, +vals: X.XTree<V>, +q: Word(32n), +v: V, e: {X.XTree.load(V, 32n, q, vals) == Some{v} : Maybe<&2, V>}) -> {X.XTree.load(V, 32n, X.XArray.path(X.XArray.index(q)), vals) == Some{v} : Maybe<&2, V>}:
  %Equal.sym(Word(32n), X.XArray.path(X.XArray.index(q)), q, XP.path_index(q)) : {X.XTree.load(V, 32n, _, vals) == Some{v} : Maybe<&2, V>}
  e

def XP.some_is_some(-A: Data, -mm: Maybe<&2, A>, -x: A, e: {mm == Some{x} : Maybe<&2, A>}) -> {Maybe.is_some(&2, A, mm) == True{} : Bool}:
  %Equal.sym(Maybe<&2, A>, mm, Some{x}, e) : {Maybe.is_some(&2, A, _) == True{} : Bool}
  {==}

def XP.not_some(-A: Data, -mm: Maybe<&2, A>, e: {mm == None{} : Maybe<&2, A>}) -> {Maybe.is_some(&2, A, mm) == False{} : Bool}:
  %Equal.sym(Maybe<&2, A>, mm, None{}, e) : {Maybe.is_some(&2, A, _) == False{} : Bool}
  {==}

def XP.some_cong(-A: Data, -x: Maybe<&2, A>, -y: Maybe<&2, A>, e: {x == y : Maybe<&2, A>}) -> {Maybe.is_some(&2, A, x) == Maybe.is_some(&2, A, y) : Bool}:
  Equal.cong(Maybe<&2, A>, Bool, z => Maybe.is_some(&2, A, z), x, y, e)

# What find promises, over its answer

def XP.FPresent(-V: Data, +t: X.XArray<V>, r: Maybe<&2, U32>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{k}:
      {Maybe.is_some(&2, V, X.XArray.load(V, t, k)) == True{} : Bool}

def XP.FAfter(+s: U32, r: Maybe<&2, U32>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{k}:
      {U32.is_le(s, k) == True{} : Bool}

def XP.FBefore(+s: U32, r: Maybe<&2, U32>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{k}:
      {U32.is_le(k, s) == True{} : Bool}

def XP.FFirst(-V: Data, +t: X.XArray<V>, +s: U32, +j: U32, r: Maybe<&2, U32>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{k}:
      {U32.is_le(s, j) == True{} : Bool} -> {U32.is_lt(j, k) == True{} : Bool} -> {X.XArray.load(V, t, j) == None{} : Maybe<&2, V>}

def XP.FLast(-V: Data, +t: X.XArray<V>, +s: U32, +j: U32, r: Maybe<&2, U32>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{k}:
      {U32.is_le(j, s) == True{} : Bool} -> {U32.is_lt(k, j) == True{} : Bool} -> {X.XArray.load(V, t, j) == None{} : Maybe<&2, V>}

def XP.FNone(-V: Data, +t: X.XArray<V>, +s: U32, +j: U32, r: Maybe<&2, U32>) -> Type:
  match r:
    case None{}:
      {U32.is_le(s, j) == True{} : Bool} -> {X.XArray.load(V, t, j) == None{} : Maybe<&2, V>}
    case Some{k}:
      Unit

def XP.FLastNone(-V: Data, +t: X.XArray<V>, +s: U32, +j: U32, r: Maybe<&2, U32>) -> Type:
  match r:
    case None{}:
      {U32.is_le(j, s) == True{} : Bool} -> {X.XArray.load(V, t, j) == None{} : Maybe<&2, V>}
    case Some{k}:
      Unit

def XP.found_present(-V: Data, +vals: X.XTree<V>, -m0: X.XTree<Unit>, -m1: X.XTree<Unit>, -m2: X.XTree<Unit>, res: Maybe<&2, Word(32n)>, ih: XP.IsIn(V, 32n, vals, res)) -> XP.FPresent(V, X.XArray{vals, m0, m1, m2}, X.XArray.found(res)):
  match res:
    case None{}:
      Unit{}
    case Some{+q}:
      %Equal.sym(Word(32n), X.XArray.path(X.XArray.index(q)), q, XP.path_index(q)) : {Maybe.is_some(&2, V, X.XTree.load(V, 32n, _, vals)) == True{} : Bool}
      ih

def XP.found_after(+s: U32, res: Maybe<&2, Word(32n)>, ih: XP.After(False{}, 32n, X.XArray.path(s), res)) -> XP.FAfter(s, X.XArray.found(res)):
  match res:
    case None{}:
      Unit{}
    case Some{+q}:
      XP.le_index_r(s, q, ih)

def XP.found_before(+s: U32, res: Maybe<&2, Word(32n)>, ih: XP.After(True{}, 32n, X.XArray.path(s), res)) -> XP.FBefore(s, X.XArray.found(res)):
  match res:
    case None{}:
      Unit{}
    case Some{+q}:
      XP.le_index_l(q, s, ih)

def XP.found_first(-V: Data, -vals: X.XTree<V>, -m0: X.XTree<Unit>, -m1: X.XTree<Unit>, -m2: X.XTree<Unit>, +s: U32, +j: U32, res: Maybe<&2, Word(32n)>, ih: XP.MinAt(V, False{}, 32n, X.XArray.path(s), vals, X.XArray.path(j), res)) -> XP.FFirst(V, X.XArray{vals, m0, m1, m2}, s, j, X.XArray.found(res)):
  match res:
    case None{}:
      Unit{}
    case Some{+q}:
      h1 => h2 => ih(XP.le_path(s, j, h1))(XP.lt_path_r(j, q, h2))

def XP.found_last(-V: Data, -vals: X.XTree<V>, -m0: X.XTree<Unit>, -m1: X.XTree<Unit>, -m2: X.XTree<Unit>, +s: U32, +j: U32, res: Maybe<&2, Word(32n)>, ih: XP.MinAt(V, True{}, 32n, X.XArray.path(s), vals, X.XArray.path(j), res)) -> XP.FLast(V, X.XArray{vals, m0, m1, m2}, s, j, X.XArray.found(res)):
  match res:
    case None{}:
      Unit{}
    case Some{+q}:
      h1 => h2 => ih(XP.le_path(j, s, h1))(XP.lt_path_l(q, j, h2))

def XP.found_none(-V: Data, -vals: X.XTree<V>, -m0: X.XTree<Unit>, -m1: X.XTree<Unit>, -m2: X.XTree<Unit>, +s: U32, +j: U32, res: Maybe<&2, Word(32n)>, ih: XP.NoneAt(V, False{}, 32n, X.XArray.path(s), vals, X.XArray.path(j), res)) -> XP.FNone(V, X.XArray{vals, m0, m1, m2}, s, j, X.XArray.found(res)):
  match res:
    case None{}:
      h => ih(XP.le_path(s, j, h))
    case Some{q}:
      Unit{}

def XP.found_last_none(-V: Data, -vals: X.XTree<V>, -m0: X.XTree<Unit>, -m1: X.XTree<Unit>, -m2: X.XTree<Unit>, +s: U32, +j: U32, res: Maybe<&2, Word(32n)>, ih: XP.NoneAt(V, True{}, 32n, X.XArray.path(s), vals, X.XArray.path(j), res)) -> XP.FLastNone(V, X.XArray{vals, m0, m1, m2}, s, j, X.XArray.found(res)):
  match res:
    case None{}:
      h => ih(XP.le_path(j, s, h))
    case Some{q}:
      Unit{}

def XP.find_present(-V: Data, t: X.XArray<V>, +s: U32) -> XP.FPresent(V, t, X.XArray.find(V, t, s)):
  match t:
    case X.XArray{+vals, m0, m1, m2}:
      XP.found_present(V, vals, m0, m1, m2, X.XTree.seek(V, 32n, X.XArray.path(s), vals, False{}), XP.seek_in(V, 32n, X.XArray.path(s), vals, False{}))

def XP.find_last_present(-V: Data, t: X.XArray<V>, +s: U32) -> XP.FPresent(V, t, X.XArray.find_last(V, t, s)):
  match t:
    case X.XArray{+vals, m0, m1, m2}:
      XP.found_present(V, vals, m0, m1, m2, X.XTree.seek(V, 32n, X.XArray.path(s), vals, True{}), XP.seek_in(V, 32n, X.XArray.path(s), vals, True{}))

def XP.find_after(-V: Data, t: X.XArray<V>, +s: U32) -> XP.FAfter(s, X.XArray.find(V, t, s)):
  match t:
    case X.XArray{+vals, m0, m1, m2}:
      XP.found_after(s, X.XTree.seek(V, 32n, X.XArray.path(s), vals, False{}), XP.seek_after(V, 32n, X.XArray.path(s), vals, False{}))

def XP.find_last_before(-V: Data, t: X.XArray<V>, +s: U32) -> XP.FBefore(s, X.XArray.find_last(V, t, s)):
  match t:
    case X.XArray{+vals, m0, m1, m2}:
      XP.found_before(s, X.XTree.seek(V, 32n, X.XArray.path(s), vals, True{}), XP.seek_after(V, 32n, X.XArray.path(s), vals, True{}))

def XP.find_first(-V: Data, t: X.XArray<V>, +s: U32, +j: U32) -> XP.FFirst(V, t, s, j, X.XArray.find(V, t, s)):
  match t:
    case X.XArray{+vals, m0, m1, m2}:
      XP.found_first(V, vals, m0, m1, m2, s, j, X.XTree.seek(V, 32n, X.XArray.path(s), vals, False{}), XP.seek_min(V, 32n, X.XArray.path(s), vals, False{}, X.XArray.path(j)))

def XP.find_last_last(-V: Data, t: X.XArray<V>, +s: U32, +j: U32) -> XP.FLast(V, t, s, j, X.XArray.find_last(V, t, s)):
  match t:
    case X.XArray{+vals, m0, m1, m2}:
      XP.found_last(V, vals, m0, m1, m2, s, j, X.XTree.seek(V, 32n, X.XArray.path(s), vals, True{}), XP.seek_min(V, 32n, X.XArray.path(s), vals, True{}, X.XArray.path(j)))

def XP.find_none(-V: Data, t: X.XArray<V>, +s: U32, +j: U32) -> XP.FNone(V, t, s, j, X.XArray.find(V, t, s)):
  match t:
    case X.XArray{+vals, m0, m1, m2}:
      XP.found_none(V, vals, m0, m1, m2, s, j, X.XTree.seek(V, 32n, X.XArray.path(s), vals, False{}), XP.seek_none(V, 32n, X.XArray.path(s), vals, False{}, X.XArray.path(j)))

def XP.find_last_none(-V: Data, t: X.XArray<V>, +s: U32, +j: U32) -> XP.FLastNone(V, t, s, j, X.XArray.find_last(V, t, s)):
  match t:
    case X.XArray{+vals, m0, m1, m2}:
      XP.found_last_none(V, vals, m0, m1, m2, s, j, X.XTree.seek(V, 32n, X.XArray.path(s), vals, True{}), XP.seek_none(V, 32n, X.XArray.path(s), vals, True{}, X.XArray.path(j)))

def XP.find_first_at(-V: Data, +t: X.XArray<V>, +s: U32, -k: U32, +j: U32, e: {X.XArray.find(V, t, s) == Some{k} : Maybe<&2, U32>}) -> XP.FFirst(V, t, s, j, Some{k}):
  %e : XP.FFirst(V, t, s, j, _)
  XP.find_first(V, t, s, j)

def XP.find_none_at(-V: Data, +t: X.XArray<V>, +s: U32, +j: U32, e: {X.XArray.find(V, t, s) == None{} : Maybe<&2, U32>}) -> XP.FNone(V, t, s, j, None{}):
  %e : XP.FNone(V, t, s, j, _)
  XP.find_none(V, t, s, j)

def XP.find_last_at(-V: Data, +t: X.XArray<V>, +s: U32, -k: U32, +j: U32, e: {X.XArray.find_last(V, t, s) == Some{k} : Maybe<&2, U32>}) -> XP.FLast(V, t, s, j, Some{k}):
  %e : XP.FLast(V, t, s, j, _)
  XP.find_last_last(V, t, s, j)

def XP.find_last_none_at(-V: Data, +t: X.XArray<V>, +s: U32, +j: U32, e: {X.XArray.find_last(V, t, s) == None{} : Maybe<&2, U32>}) -> XP.FLastNone(V, t, s, j, None{}):
  %e : XP.FLastNone(V, t, s, j, _)
  XP.find_last_none(V, t, s, j)

# What find_marked promises

def XP.MPresent(-V: Data, +t: X.XArray<V>, +m: X.XMark, r: Maybe<&2, U32>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{k}:
      {X.XArray.get_mark(V, t, k, m) == True{} : Bool}

def XP.MFirst(-V: Data, +t: X.XArray<V>, +m: X.XMark, +s: U32, +j: U32, r: Maybe<&2, U32>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{k}:
      {U32.is_le(s, j) == True{} : Bool} -> {U32.is_lt(j, k) == True{} : Bool} -> {X.XArray.get_mark(V, t, j, m) == False{} : Bool}

def XP.MNone(-V: Data, +t: X.XArray<V>, +m: X.XMark, +s: U32, +j: U32, r: Maybe<&2, U32>) -> Type:
  match r:
    case None{}:
      {U32.is_le(s, j) == True{} : Bool} -> {X.XArray.get_mark(V, t, j, m) == False{} : Bool}
    case Some{k}:
      Unit

def XP.mfound_present(-V: Data, +t: X.XArray<V>, +m: X.XMark, res: Maybe<&2, Word(32n)>, ih: XP.IsIn(Unit, 32n, X.XArray.marks(V, t, m), res)) -> XP.MPresent(V, t, m, X.XArray.found(res)):
  match res:
    case None{}:
      Unit{}
    case Some{+q}:
      %Equal.sym(Word(32n), X.XArray.path(X.XArray.index(q)), q, XP.path_index(q)) : {Maybe.is_some(&2, Unit, X.XTree.load(Unit, 32n, _, X.XArray.marks(V, t, m))) == True{} : Bool}
      ih

def XP.mfound_first(-V: Data, +t: X.XArray<V>, +m: X.XMark, +s: U32, +j: U32, res: Maybe<&2, Word(32n)>, ih: XP.MinAt(Unit, False{}, 32n, X.XArray.path(s), X.XArray.marks(V, t, m), X.XArray.path(j), res)) -> XP.MFirst(V, t, m, s, j, X.XArray.found(res)):
  match res:
    case None{}:
      Unit{}
    case Some{+q}:
      h1 => h2 => XP.not_some(Unit, X.XTree.load(Unit, 32n, X.XArray.path(j), X.XArray.marks(V, t, m)), ih(XP.le_path(s, j, h1))(XP.lt_path_r(j, q, h2)))

def XP.mfound_none(-V: Data, +t: X.XArray<V>, +m: X.XMark, +s: U32, +j: U32, res: Maybe<&2, Word(32n)>, ih: XP.NoneAt(Unit, False{}, 32n, X.XArray.path(s), X.XArray.marks(V, t, m), X.XArray.path(j), res)) -> XP.MNone(V, t, m, s, j, X.XArray.found(res)):
  match res:
    case None{}:
      h => XP.not_some(Unit, X.XTree.load(Unit, 32n, X.XArray.path(j), X.XArray.marks(V, t, m)), ih(XP.le_path(s, j, h)))
    case Some{q}:
      Unit{}

def XP.find_marked_first_at(-V: Data, +t: X.XArray<V>, +s: U32, +m: X.XMark, -k: U32, +j: U32, e: {X.XArray.find_marked(V, t, s, m) == Some{k} : Maybe<&2, U32>}) -> XP.MFirst(V, t, m, s, j, Some{k}):
  %e : XP.MFirst(V, t, m, s, j, _)
  XP.mfound_first(V, t, m, s, j, X.XTree.seek(Unit, 32n, X.XArray.path(s), X.XArray.marks(V, t, m), False{}), XP.seek_min(Unit, 32n, X.XArray.path(s), X.XArray.marks(V, t, m), False{}, X.XArray.path(j)))

def XP.find_marked_none_at(-V: Data, +t: X.XArray<V>, +s: U32, +m: X.XMark, +j: U32, e: {X.XArray.find_marked(V, t, s, m) == None{} : Maybe<&2, U32>}) -> XP.MNone(V, t, m, s, j, None{}):
  %e : XP.MNone(V, t, m, s, j, _)
  XP.mfound_none(V, t, m, s, j, X.XTree.seek(Unit, 32n, X.XArray.path(s), X.XArray.marks(V, t, m), False{}), XP.seek_none(Unit, 32n, X.XArray.path(s), X.XArray.marks(V, t, m), False{}, X.XArray.path(j)))

# Emptiness

def XP.empty_none(-V: Data, -vals: X.XTree<V>, +i: U32, res: Maybe<&2, Word(32n)>, e: {Maybe.is_none(&2, Word(32n), res) == True{} : Bool}, ih: XP.NoneAt(V, False{}, 32n, X.XPath.fill(32n, False{}), vals, X.XArray.path(i), res)) -> {X.XTree.load(V, 32n, X.XArray.path(i), vals) == None{} : Maybe<&2, V>}:
  match res:
    case None{}:
      ih(XP.fill_ok(False{}, 32n, X.XArray.path(i)))
    case Some{q}:
      Empty.absurd({X.XTree.load(V, 32n, X.XArray.path(i), vals) == None{} : Maybe<&2, V>}, XP.ft(e))

def XP.store_nonempty(-V: Data, -tr: X.XTree<V>, +i: U32, -v: V, res: Maybe<&2, Word(32n)>, ih: XP.NoneAt(V, False{}, 32n, X.XPath.fill(32n, False{}), tr, X.XArray.path(i), res), ls: {X.XTree.load(V, 32n, X.XArray.path(i), tr) == Some{v} : Maybe<&2, V>}) -> {Maybe.is_none(&2, Word(32n), res) == False{} : Bool}:
  match res:
    case None{}:
      Empty.absurd({Maybe.is_none(&2, Word(32n), None{}) == False{} : Bool}, XP.none_some(V, v, Equal.trans(Maybe<&2, V>, None{}, X.XTree.load(V, 32n, X.XArray.path(i), tr), Some{v}, Equal.sym(Maybe<&2, V>, X.XTree.load(V, 32n, X.XArray.path(i), tr), None{}, ih(XP.fill_ok(False{}, 32n, X.XArray.path(i)))), ls)))
    case Some{q}:
      {==}

def XP.nonempty_some(-V: Data, +vals: X.XTree<V>, +m0: X.XTree<Unit>, +m1: X.XTree<Unit>, +m2: X.XTree<Unit>, res: Maybe<&2, Word(32n)>, e: {Maybe.is_none(&2, Word(32n), res) == False{} : Bool}, ih: XP.IsIn(V, 32n, vals, res)) -> &i: U32 -> {Maybe.is_some(&2, V, X.XArray.load(V, X.XArray{vals, m0, m1, m2}, i)) == True{} : Bool}:
  match res:
    case None{}:
      Empty.absurd(&i: U32 -> {Maybe.is_some(&2, V, X.XArray.load(V, X.XArray{vals, m0, m1, m2}, i)) == True{} : Bool}, XP.tf(e))
    case Some{+q}:
      (X.XArray.index(q), XP.found_present(V, vals, m0, m1, m2, Some{q}, ih))

# Marks

def XP.mark_set_go(-V: Data, -vals: X.XTree<V>, +m0: X.XTree<Unit>, +m1: X.XTree<Unit>, +m2: X.XTree<Unit>, +i: U32, m: X.XMark) -> {X.XArray.get_mark(V, X.XArray.set_mark.go(V, True{}, m, X.XArray.path(i), vals, m0, m1, m2), i, m) == True{} : Bool}:
  match m:
    case X.XMark0{}:
      XP.some_is_some(Unit, X.XTree.load(Unit, 32n, X.XArray.path(i), X.XTree.store(Unit, 32n, X.XArray.path(i), m0, Unit{})), Unit{}, XP.load_store(Unit, 32n, X.XArray.path(i), m0, Unit{}))
    case X.XMark1{}:
      XP.some_is_some(Unit, X.XTree.load(Unit, 32n, X.XArray.path(i), X.XTree.store(Unit, 32n, X.XArray.path(i), m1, Unit{})), Unit{}, XP.load_store(Unit, 32n, X.XArray.path(i), m1, Unit{}))
    case X.XMark2{}:
      XP.some_is_some(Unit, X.XTree.load(Unit, 32n, X.XArray.path(i), X.XTree.store(Unit, 32n, X.XArray.path(i), m2, Unit{})), Unit{}, XP.load_store(Unit, 32n, X.XArray.path(i), m2, Unit{}))

def XP.mark_set_index(-V: Data, present: Bool, -vals: X.XTree<V>, +m0: X.XTree<Unit>, +m1: X.XTree<Unit>, +m2: X.XTree<Unit>, +i: U32, +j: U32, m: X.XMark, n: X.XMark, e: {U32.is_eq(i, j) == False{} : Bool}) -> {X.XArray.get_mark(V, X.XArray.set_mark.go(V, present, m, X.XArray.path(i), vals, m0, m1, m2), j, n) == X.XArray.get_mark(V, X.XArray{vals, m0, m1, m2}, j, n) : Bool}:
  match present:
    case False{}:
      {==}
    case True{}:
      match m n:
        case X.XMark0{} X.XMark0{}:
          XP.some_cong(Unit, X.XTree.load(Unit, 32n, X.XArray.path(j), X.XTree.store(Unit, 32n, X.XArray.path(i), m0, Unit{})), X.XTree.load(Unit, 32n, X.XArray.path(j), m0), XP.load_store_other(Unit, 32n, X.XArray.path(i), X.XArray.path(j), m0, Unit{}, XP.ne_path(i, j, e)))
        case X.XMark1{} X.XMark1{}:
          XP.some_cong(Unit, X.XTree.load(Unit, 32n, X.XArray.path(j), X.XTree.store(Unit, 32n, X.XArray.path(i), m1, Unit{})), X.XTree.load(Unit, 32n, X.XArray.path(j), m1), XP.load_store_other(Unit, 32n, X.XArray.path(i), X.XArray.path(j), m1, Unit{}, XP.ne_path(i, j, e)))
        case X.XMark2{} X.XMark2{}:
          XP.some_cong(Unit, X.XTree.load(Unit, 32n, X.XArray.path(j), X.XTree.store(Unit, 32n, X.XArray.path(i), m2, Unit{})), X.XTree.load(Unit, 32n, X.XArray.path(j), m2), XP.load_store_other(Unit, 32n, X.XArray.path(i), X.XArray.path(j), m2, Unit{}, XP.ne_path(i, j, e)))
        case X.XMark0{} X.XMark1{}:
          {==}
        case X.XMark0{} X.XMark2{}:
          {==}
        case X.XMark1{} X.XMark0{}:
          {==}
        case X.XMark1{} X.XMark2{}:
          {==}
        case X.XMark2{} X.XMark0{}:
          {==}
        case X.XMark2{} X.XMark1{}:
          {==}

def XP.mark_set_mark(-V: Data, present: Bool, -vals: X.XTree<V>, -m0: X.XTree<Unit>, -m1: X.XTree<Unit>, -m2: X.XTree<Unit>, -i: U32, -j: U32, m: X.XMark, n: X.XMark, e: {X.XMark.is_eq(m, n) == False{} : Bool}) -> {X.XArray.get_mark(V, X.XArray.set_mark.go(V, present, m, X.XArray.path(i), vals, m0, m1, m2), j, n) == X.XArray.get_mark(V, X.XArray{vals, m0, m1, m2}, j, n) : Bool}:
  match present:
    case False{}:
      {==}
    case True{}:
      match m n:
        case X.XMark0{} X.XMark0{}:
          Empty.absurd({X.XArray.get_mark(V, X.XArray.set_mark.go(V, True{}, X.XMark0{}, X.XArray.path(i), vals, m0, m1, m2), j, X.XMark0{}) == X.XArray.get_mark(V, X.XArray{vals, m0, m1, m2}, j, X.XMark0{}) : Bool}, XP.tf(e))
        case X.XMark1{} X.XMark1{}:
          Empty.absurd({X.XArray.get_mark(V, X.XArray.set_mark.go(V, True{}, X.XMark1{}, X.XArray.path(i), vals, m0, m1, m2), j, X.XMark1{}) == X.XArray.get_mark(V, X.XArray{vals, m0, m1, m2}, j, X.XMark1{}) : Bool}, XP.tf(e))
        case X.XMark2{} X.XMark2{}:
          Empty.absurd({X.XArray.get_mark(V, X.XArray.set_mark.go(V, True{}, X.XMark2{}, X.XArray.path(i), vals, m0, m1, m2), j, X.XMark2{}) == X.XArray.get_mark(V, X.XArray{vals, m0, m1, m2}, j, X.XMark2{}) : Bool}, XP.tf(e))
        case X.XMark0{} X.XMark1{}:
          {==}
        case X.XMark0{} X.XMark2{}:
          {==}
        case X.XMark1{} X.XMark0{}:
          {==}
        case X.XMark1{} X.XMark2{}:
          {==}
        case X.XMark2{} X.XMark0{}:
          {==}
        case X.XMark2{} X.XMark1{}:
          {==}

def XP.load_set_mark_go(-V: Data, present: Bool, -vals: X.XTree<V>, -m0: X.XTree<Unit>, -m1: X.XTree<Unit>, -m2: X.XTree<Unit>, -i: U32, -j: U32, m: X.XMark) -> {X.XArray.load(V, X.XArray.set_mark.go(V, present, m, X.XArray.path(i), vals, m0, m1, m2), j) == X.XArray.load(V, X.XArray{vals, m0, m1, m2}, j) : Maybe<&2, V>}:
  match present:
    case False{}:
      {==}
    case True{}:
      match m:
        case X.XMark0{}:
          {==}
        case X.XMark1{}:
          {==}
        case X.XMark2{}:
          {==}

# Iteration over a range: from paths to indices

def XP.ESound(-V: Data, +t: X.XArray<V>, +a: U32, +b: U32, ys: List<&2, X.XEntry<V>>) -> Type:
  match ys:
    case Nil{}:
      Unit
    case Con{h, rest}:
      match h:
        case X.XEntry{+i, +v}:
          ({X.XArray.load(V, t, i) == Some{v} : Maybe<&2, V>} & ({U32.is_le(a, i) == True{} : Bool} & {U32.is_le(i, b) == True{} : Bool})) & XP.ESound(V, t, a, b, rest)

def XP.entries_sound(-V: Data, +vals: X.XTree<V>, +m0: X.XTree<Unit>, +m1: X.XTree<Unit>, +m2: X.XTree<Unit>, +a: U32, +b: U32, xs: List<&2, X.XAt<32n, V>>, ev: XP.Sound(V, 32n, vals, X.XArray.path(a), X.XArray.path(b), xs)) -> XP.ESound(V, X.XArray{vals, m0, m1, m2}, a, b, X.XArray.entries(V, xs)):
  match xs:
    case Nil{}:
      Unit{}
    case Con{h, rest}:
      match h:
        case X.XAt{+q, +v}:
          match ev:
            case (e1, e2):
              match e1:
                case (l, fg):
                  match fg:
                    case (f, g):
                      ((XP.conv_load(V, vals, q, v, l), (XP.le_index_r(a, q, f), XP.le_index_l(q, b, g))), XP.entries_sound(V, vals, m0, m1, m2, a, b, rest, e2))

def XP.range_sound_pub(-V: Data, t: X.XArray<V>, +a: U32, +b: U32) -> XP.ESound(V, t, a, b, X.XArray.range(V, t, a, b)):
  match t:
    case X.XArray{+vals, +m0, +m1, +m2}:
      XP.entries_sound(V, vals, m0, m1, m2, a, b, X.XTree.range(V, 32n, vals, X.XArray.path(a), X.XArray.path(b)), XP.range_sound(V, 32n, vals, X.XArray.path(a), X.XArray.path(b)))

def XP.EGet(-V: Data, +t: X.XArray<V>, +a: U32, +b: U32, r: Maybe<&2, X.XEntry<V>>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{h}:
      match h:
        case X.XEntry{+i, +v}:
          {X.XArray.load(V, t, i) == Some{v} : Maybe<&2, V>} & ({U32.is_le(a, i) == True{} : Bool} & {U32.is_le(i, b) == True{} : Bool})

def XP.esound_get(-V: Data, -t: X.XArray<V>, -a: U32, -b: U32, k: Nat, ys: List<&2, X.XEntry<V>>, ev: XP.ESound(V, t, a, b, ys)) -> XP.EGet(V, t, a, b, List.get(&2, X.XEntry<V>, ys, k)):
  match k:
    case 0n:
      match ys:
        case Nil{}:
          Unit{}
        case Con{h, rest}:
          match h:
            case X.XEntry{i, v}:
              match ev:
                case (e1, e2):
                  e1
    case 1n+p:
      match ys:
        case Nil{}:
          Unit{}
        case Con{h, rest}:
          match h:
            case X.XEntry{i, v}:
              match ev:
                case (e1, e2):
                  XP.esound_get(V, t, a, b, p, rest, e2)

def XP.EGetL(-V: Data, +t: X.XArray<V>, r: Maybe<&2, X.XEntry<V>>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{h}:
      match h:
        case X.XEntry{i, v}:
          {X.XArray.load(V, t, i) == Some{v} : Maybe<&2, V>}

def XP.EGetA(-V: Data, +a: U32, r: Maybe<&2, X.XEntry<V>>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{h}:
      match h:
        case X.XEntry{i, v}:
          {U32.is_le(a, i) == True{} : Bool}

def XP.EGetB(-V: Data, +b: U32, r: Maybe<&2, X.XEntry<V>>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{h}:
      match h:
        case X.XEntry{i, v}:
          {U32.is_le(i, b) == True{} : Bool}

def XP.eget_l(-V: Data, -t: X.XArray<V>, -a: U32, -b: U32, r: Maybe<&2, X.XEntry<V>>, ev: XP.EGet(V, t, a, b, r)) -> XP.EGetL(V, t, r):
  match r:
    case None{}:
      Unit{}
    case Some{h}:
      match h:
        case X.XEntry{i, v}:
          match ev:
            case (l, fg):
              l

def XP.eget_a(-V: Data, -t: X.XArray<V>, -a: U32, -b: U32, r: Maybe<&2, X.XEntry<V>>, ev: XP.EGet(V, t, a, b, r)) -> XP.EGetA(V, a, r):
  match r:
    case None{}:
      Unit{}
    case Some{h}:
      match h:
        case X.XEntry{i, v}:
          match ev:
            case (l, fg):
              match fg:
                case (f, g):
                  f

def XP.eget_b(-V: Data, -t: X.XArray<V>, -a: U32, -b: U32, r: Maybe<&2, X.XEntry<V>>, ev: XP.EGet(V, t, a, b, r)) -> XP.EGetB(V, b, r):
  match r:
    case None{}:
      Unit{}
    case Some{h}:
      match h:
        case X.XEntry{i, v}:
          match ev:
            case (l, fg):
              match fg:
                case (f, g):
                  g

def XP.ESortedFrom(-V: Data, ys: List<&2, X.XEntry<V>>, +prev: U32) -> Type:
  match ys:
    case Nil{}:
      Unit
    case Con{h, rest}:
      match h:
        case X.XEntry{+i, v}:
          {U32.is_lt(prev, i) == True{} : Bool} & XP.ESortedFrom(V, rest, i)

def XP.ESorted(-V: Data, ys: List<&2, X.XEntry<V>>) -> Type:
  match ys:
    case Nil{}:
      Unit
    case Con{h, rest}:
      match h:
        case X.XEntry{i, v}:
          XP.ESortedFrom(V, rest, i)

def XP.entries_sorted_from(-V: Data, xs: List<&2, X.XAt<32n, V>>, +prev: Word(32n), ev: XP.SortedFrom(V, 32n, xs, prev)) -> XP.ESortedFrom(V, X.XArray.entries(V, xs), X.XArray.index(prev)):
  match xs:
    case Nil{}:
      Unit{}
    case Con{h, rest}:
      match h:
        case X.XAt{+q, v}:
          match ev:
            case (l, e2):
              (XP.lt_index(prev, q, l), XP.entries_sorted_from(V, rest, q, e2))

def XP.entries_sorted(-V: Data, xs: List<&2, X.XAt<32n, V>>, ev: XP.Sorted(V, 32n, xs)) -> XP.ESorted(V, X.XArray.entries(V, xs)):
  match xs:
    case Nil{}:
      Unit{}
    case Con{h, rest}:
      match h:
        case X.XAt{q, v}:
          XP.entries_sorted_from(V, rest, q, ev)

def XP.range_sorted_pub(-V: Data, t: X.XArray<V>, +a: U32, +b: U32) -> XP.ESorted(V, X.XArray.range(V, t, a, b)):
  match t:
    case X.XArray{+vals, m0, m1, m2}:
      XP.entries_sorted(V, X.XTree.range(V, 32n, vals, X.XArray.path(a), X.XArray.path(b)), XP.range_sorted(V, 32n, vals, X.XArray.path(a), X.XArray.path(b)))

def XP.ELt(-V: Data, r1: Maybe<&2, X.XEntry<V>>, r2: Maybe<&2, X.XEntry<V>>) -> Type:
  match r1:
    case None{}:
      Unit
    case Some{h1}:
      match h1:
        case X.XEntry{i, v}:
          match r2:
            case None{}:
              Unit
            case Some{h2}:
              match h2:
                case X.XEntry{j, w}:
                  {U32.is_lt(i, j) == True{} : Bool}

def XP.esorted_rest(-V: Data, ys: List<&2, X.XEntry<V>>, -prev: U32, ev: XP.ESortedFrom(V, ys, prev)) -> XP.ESorted(V, ys):
  match ys:
    case Nil{}:
      Unit{}
    case Con{h, rest}:
      match h:
        case X.XEntry{i, v}:
          match ev:
            case (l, e2):
              e2

def XP.esorted_get(-V: Data, k: Nat, ys: List<&2, X.XEntry<V>>, ev: XP.ESorted(V, ys)) -> XP.ELt(V, List.get(&2, X.XEntry<V>, ys, k), List.get(&2, X.XEntry<V>, ys, 1n+k)):
  match k:
    case 0n:
      match ys:
        case Nil{}:
          Unit{}
        case Con{h, rest}:
          match h:
            case X.XEntry{i, v}:
              match rest:
                case Nil{}:
                  Unit{}
                case Con{h2, r2}:
                  match h2:
                    case X.XEntry{j, w}:
                      match ev:
                        case (l, e2):
                          l
    case 1n+p:
      match ys:
        case Nil{}:
          Unit{}
        case Con{h, +rest}:
          match h:
            case X.XEntry{+i, v}:
              XP.esorted_get(V, p, rest, XP.esorted_rest(V, rest, i, ev))

def XP.EMem(-V: Data, +i: U32, +v: V, ys: List<&2, X.XEntry<V>>) -> Type:
  match ys:
    case Nil{}:
      Empty
    case Con{h, rest}:
      {h == X.XEntry{i, v} : X.XEntry<V>} | XP.EMem(V, i, v, rest)

def XP.entry_of(-V: Data, e: X.XAt<32n, V>) -> X.XEntry<V>:
  match e:
    case X.XAt{q, v}:
      X.XEntry{X.XArray.index(q), v}

def XP.entries_mem(-V: Data, -q: Word(32n), -v: V, xs: List<&2, X.XAt<32n, V>>, e: XP.Mem(V, 32n, q, v, xs)) -> XP.EMem(V, X.XArray.index(q), v, X.XArray.entries(V, xs)):
  match xs:
    case Nil{}:
      match e:
    case Con{h, rest}:
      match h:
        case X.XAt{hq, hv}:
          match e:
            case Inl{eq}:
              Inl{Equal.cong(X.XAt<32n, V>, X.XEntry<V>, z => XP.entry_of(V, z), X.XAt{hq, hv}, X.XAt{q, v}, eq)}
            case Inr{e2}:
              Inr{XP.entries_mem(V, q, v, rest, e2)}

def XP.emem_succ(-V: Data, -i: U32, -v: V, -h: X.XEntry<V>, -rest: List<&2, X.XEntry<V>>, r: &k: Nat -> {List.get(&2, X.XEntry<V>, rest, k) == Some{X.XEntry{i, v}} : Maybe<&2, X.XEntry<V>>}) -> &k: Nat -> {List.get(&2, X.XEntry<V>, Con{h, rest}, k) == Some{X.XEntry{i, v}} : Maybe<&2, X.XEntry<V>>}:
  match r:
    case (k, p):
      (1n+k, p)

def XP.emem_index(-V: Data, -i: U32, -v: V, ys: List<&2, X.XEntry<V>>, e: XP.EMem(V, i, v, ys)) -> &k: Nat -> {List.get(&2, X.XEntry<V>, ys, k) == Some{X.XEntry{i, v}} : Maybe<&2, X.XEntry<V>>}:
  match ys:
    case Nil{}:
      match e:
    case Con{h, rest}:
      match e:
        case Inl{eq}:
          (0n, Equal.cong(X.XEntry<V>, Maybe<&2, X.XEntry<V>>, z => Some{z}, h, X.XEntry{i, v}, eq))
        case Inr{e2}:
          XP.emem_succ(V, i, v, h, rest, XP.emem_index(V, i, v, rest, e2))

def XP.emem_conv(-V: Data, +i: U32, -v: V, -ys: List<&2, X.XEntry<V>>, e: XP.EMem(V, X.XArray.index(X.XArray.path(i)), v, ys)) -> XP.EMem(V, i, v, ys):
  %XP.index_path(i) : XP.EMem(V, _, v, ys)
  e

def XP.range_mem_pub(-V: Data, t: X.XArray<V>, +a: U32, +b: U32, +i: U32, +v: V, h1: {U32.is_le(a, i) == True{} : Bool}, h2: {U32.is_le(i, b) == True{} : Bool}, h3: {X.XArray.load(V, t, i) == Some{v} : Maybe<&2, V>}) -> XP.EMem(V, i, v, X.XArray.range(V, t, a, b)):
  match t:
    case X.XArray{+vals, m0, m1, m2}:
      XP.emem_conv(V, i, v, X.XArray.entries(V, X.XTree.range(V, 32n, vals, X.XArray.path(a), X.XArray.path(b))), XP.entries_mem(V, X.XArray.path(i), v, X.XTree.range(V, 32n, vals, X.XArray.path(a), X.XArray.path(b)), XP.range_mem(V, 32n, vals, X.XArray.path(a), X.XArray.path(b), X.XArray.path(i), v, XP.le_path(a, i, h1), XP.le_path(i, b, h2), h3)))

# The laws

def XP.law.load_empty(-V: Data, +i: U32) -> {X.XArray.load(V, X.XArray.empty(V), i) == None{} : Maybe<&2, V>}:
  XP.load_nil(V, 32n, X.XArray.path(i))

def XP.law.load_store(-V: Data, +t: X.XArray<V>, +i: U32, +v: V) -> {X.XArray.load(V, X.XArray.store(V, t, i, v), i) == Some{v} : Maybe<&2, V>}:
  match t:
    case X.XArray{vals, m0, m1, m2}:
      XP.load_store(V, 32n, X.XArray.path(i), vals, v)

def XP.law.load_store_other(-V: Data, +t: X.XArray<V>, +i: U32, +j: U32, +v: V, +e: {U32.is_eq(i, j) == False{} : Bool}) -> {X.XArray.load(V, X.XArray.store(V, t, i, v), j) == X.XArray.load(V, t, j) : Maybe<&2, V>}:
  match t:
    case X.XArray{vals, m0, m1, m2}:
      XP.load_store_other(V, 32n, X.XArray.path(i), X.XArray.path(j), vals, v, XP.ne_path(i, j, e))

def XP.law.load_erase(-V: Data, +t: X.XArray<V>, +i: U32) -> {X.XArray.load(V, X.XArray.erase(V, t, i), i) == None{} : Maybe<&2, V>}:
  match t:
    case X.XArray{vals, m0, m1, m2}:
      XP.load_erase(V, 32n, X.XArray.path(i), vals)

def XP.law.load_erase_other(-V: Data, +t: X.XArray<V>, +i: U32, +j: U32, +e: {U32.is_eq(i, j) == False{} : Bool}) -> {X.XArray.load(V, X.XArray.erase(V, t, i), j) == X.XArray.load(V, t, j) : Maybe<&2, V>}:
  match t:
    case X.XArray{vals, m0, m1, m2}:
      XP.load_erase_other(V, 32n, X.XArray.path(i), X.XArray.path(j), vals, XP.ne_path(i, j, e))

def XP.law.is_empty_empty(-V: Data) -> {X.XArray.is_empty(V, X.XArray.empty(V)) == True{} : Bool}:
  {==}

def XP.law.is_empty_load(-V: Data, +t: X.XArray<V>, +i: U32, +e: {X.XArray.is_empty(V, t) == True{} : Bool}) -> {X.XArray.load(V, t, i) == None{} : Maybe<&2, V>}:
  match t:
    case X.XArray{+vals, m0, m1, m2}:
      XP.empty_none(V, vals, i, X.XTree.seek(V, 32n, X.XPath.fill(32n, False{}), vals, False{}), e, XP.seek_none(V, 32n, X.XPath.fill(32n, False{}), vals, False{}, X.XArray.path(i)))

def XP.law.is_empty_store(-V: Data, +t: X.XArray<V>, +i: U32, +v: V) -> {X.XArray.is_empty(V, X.XArray.store(V, t, i, v)) == False{} : Bool}:
  match t:
    case X.XArray{vals, m0, m1, m2}:
      XP.store_nonempty(V, X.XTree.store(V, 32n, X.XArray.path(i), vals, v), i, v, X.XTree.seek(V, 32n, X.XPath.fill(32n, False{}), X.XTree.store(V, 32n, X.XArray.path(i), vals, v), False{}), XP.seek_none(V, 32n, X.XPath.fill(32n, False{}), X.XTree.store(V, 32n, X.XArray.path(i), vals, v), False{}, X.XArray.path(i)), XP.load_store(V, 32n, X.XArray.path(i), vals, v))

def XP.law.is_empty_false(-V: Data, +t: X.XArray<V>, +e: {X.XArray.is_empty(V, t) == False{} : Bool}) -> &i: U32 -> {Maybe.is_some(&2, V, X.XArray.load(V, t, i)) == True{} : Bool}:
  match t:
    case X.XArray{+vals, m0, m1, m2}:
      XP.nonempty_some(V, vals, m0, m1, m2, X.XTree.seek(V, 32n, X.XPath.fill(32n, False{}), vals, False{}), e, XP.seek_in(V, 32n, X.XPath.fill(32n, False{}), vals, False{}))

def XP.law.find_present(-V: Data, +t: X.XArray<V>, +s: U32, +k: U32, +e: {X.XArray.find(V, t, s) == Some{k} : Maybe<&2, U32>}) -> {Maybe.is_some(&2, V, X.XArray.load(V, t, k)) == True{} : Bool}:
  %e : XP.FPresent(V, t, _)
  XP.find_present(V, t, s)

def XP.law.find_at_or_after(-V: Data, +t: X.XArray<V>, +s: U32, +k: U32, +e: {X.XArray.find(V, t, s) == Some{k} : Maybe<&2, U32>}) -> {U32.is_le(s, k) == True{} : Bool}:
  %e : XP.FAfter(s, _)
  XP.find_after(V, t, s)

def XP.law.find_first(-V: Data, +t: X.XArray<V>, +s: U32, +k: U32, +j: U32, +e: {X.XArray.find(V, t, s) == Some{k} : Maybe<&2, U32>}, +h1: {U32.is_le(s, j) == True{} : Bool}, +h2: {U32.is_lt(j, k) == True{} : Bool}) -> {X.XArray.load(V, t, j) == None{} : Maybe<&2, V>}:
  XP.find_first_at(V, t, s, k, j, e)(h1)(h2)

def XP.law.find_none(-V: Data, +t: X.XArray<V>, +s: U32, +j: U32, +e: {X.XArray.find(V, t, s) == None{} : Maybe<&2, U32>}, +h: {U32.is_le(s, j) == True{} : Bool}) -> {X.XArray.load(V, t, j) == None{} : Maybe<&2, V>}:
  XP.find_none_at(V, t, s, j, e)(h)

def XP.law.find_last_present(-V: Data, +t: X.XArray<V>, +s: U32, +k: U32, +e: {X.XArray.find_last(V, t, s) == Some{k} : Maybe<&2, U32>}) -> {Maybe.is_some(&2, V, X.XArray.load(V, t, k)) == True{} : Bool}:
  %e : XP.FPresent(V, t, _)
  XP.find_last_present(V, t, s)

def XP.law.find_last_at_or_before(-V: Data, +t: X.XArray<V>, +s: U32, +k: U32, +e: {X.XArray.find_last(V, t, s) == Some{k} : Maybe<&2, U32>}) -> {U32.is_le(k, s) == True{} : Bool}:
  %e : XP.FBefore(s, _)
  XP.find_last_before(V, t, s)

def XP.law.find_last_last(-V: Data, +t: X.XArray<V>, +s: U32, +k: U32, +j: U32, +e: {X.XArray.find_last(V, t, s) == Some{k} : Maybe<&2, U32>}, +h1: {U32.is_le(j, s) == True{} : Bool}, +h2: {U32.is_lt(k, j) == True{} : Bool}) -> {X.XArray.load(V, t, j) == None{} : Maybe<&2, V>}:
  XP.find_last_at(V, t, s, k, j, e)(h1)(h2)

def XP.law.find_last_none(-V: Data, +t: X.XArray<V>, +s: U32, +j: U32, +e: {X.XArray.find_last(V, t, s) == None{} : Maybe<&2, U32>}, +h: {U32.is_le(j, s) == True{} : Bool}) -> {X.XArray.load(V, t, j) == None{} : Maybe<&2, V>}:
  XP.find_last_none_at(V, t, s, j, e)(h)

def XP.law.range_present(-V: Data, +t: X.XArray<V>, +a: U32, +b: U32, +k: Nat, +i: U32, +v: V, +e: {List.get(&2, X.XEntry<V>, X.XArray.range(V, t, a, b), k) == Some{X.XEntry{i, v}} : Maybe<&2, X.XEntry<V>>}) -> {X.XArray.load(V, t, i) == Some{v} : Maybe<&2, V>}:
  %e : XP.EGetL(V, t, _)
  XP.eget_l(V, t, a, b, List.get(&2, X.XEntry<V>, X.XArray.range(V, t, a, b), k), XP.esound_get(V, t, a, b, k, X.XArray.range(V, t, a, b), XP.range_sound_pub(V, t, a, b)))

def XP.law.range_from(-V: Data, +t: X.XArray<V>, +a: U32, +b: U32, +k: Nat, +i: U32, +v: V, +e: {List.get(&2, X.XEntry<V>, X.XArray.range(V, t, a, b), k) == Some{X.XEntry{i, v}} : Maybe<&2, X.XEntry<V>>}) -> {U32.is_le(a, i) == True{} : Bool}:
  %e : XP.EGetA(V, a, _)
  XP.eget_a(V, t, a, b, List.get(&2, X.XEntry<V>, X.XArray.range(V, t, a, b), k), XP.esound_get(V, t, a, b, k, X.XArray.range(V, t, a, b), XP.range_sound_pub(V, t, a, b)))

def XP.law.range_to(-V: Data, +t: X.XArray<V>, +a: U32, +b: U32, +k: Nat, +i: U32, +v: V, +e: {List.get(&2, X.XEntry<V>, X.XArray.range(V, t, a, b), k) == Some{X.XEntry{i, v}} : Maybe<&2, X.XEntry<V>>}) -> {U32.is_le(i, b) == True{} : Bool}:
  %e : XP.EGetB(V, b, _)
  XP.eget_b(V, t, a, b, List.get(&2, X.XEntry<V>, X.XArray.range(V, t, a, b), k), XP.esound_get(V, t, a, b, k, X.XArray.range(V, t, a, b), XP.range_sound_pub(V, t, a, b)))

def XP.law.range_ascending(-V: Data, +t: X.XArray<V>, +a: U32, +b: U32, +k: Nat, +i: U32, +v: V, +j: U32, +w: V, +e1: {List.get(&2, X.XEntry<V>, X.XArray.range(V, t, a, b), k) == Some{X.XEntry{i, v}} : Maybe<&2, X.XEntry<V>>}, +e2: {List.get(&2, X.XEntry<V>, X.XArray.range(V, t, a, b), 1n+k) == Some{X.XEntry{j, w}} : Maybe<&2, X.XEntry<V>>}) -> {U32.is_lt(i, j) == True{} : Bool}:
  %e1 : XP.ELt(V, _, Some{X.XEntry{j, w}})
  %e2 : XP.ELt(V, List.get(&2, X.XEntry<V>, X.XArray.range(V, t, a, b), k), _)
  XP.esorted_get(V, k, X.XArray.range(V, t, a, b), XP.range_sorted_pub(V, t, a, b))

def XP.law.range_complete(-V: Data, +t: X.XArray<V>, +a: U32, +b: U32, +i: U32, +v: V, +h1: {U32.is_le(a, i) == True{} : Bool}, +h2: {U32.is_le(i, b) == True{} : Bool}, +h3: {X.XArray.load(V, t, i) == Some{v} : Maybe<&2, V>}) -> &k: Nat -> {List.get(&2, X.XEntry<V>, X.XArray.range(V, t, a, b), k) == Some{X.XEntry{i, v}} : Maybe<&2, X.XEntry<V>>}:
  XP.emem_index(V, i, v, X.XArray.range(V, t, a, b), XP.range_mem_pub(V, t, a, b, i, v, h1, h2, h3))

def XP.law.mark_empty(-V: Data, +i: U32, +m: X.XMark) -> {X.XArray.get_mark(V, X.XArray.empty(V), i, m) == False{} : Bool}:
  match m:
    case X.XMark0{}:
      XP.not_some(Unit, X.XTree.load(Unit, 32n, X.XArray.path(i), X.XNil{}), XP.load_nil(Unit, 32n, X.XArray.path(i)))
    case X.XMark1{}:
      XP.not_some(Unit, X.XTree.load(Unit, 32n, X.XArray.path(i), X.XNil{}), XP.load_nil(Unit, 32n, X.XArray.path(i)))
    case X.XMark2{}:
      XP.not_some(Unit, X.XTree.load(Unit, 32n, X.XArray.path(i), X.XNil{}), XP.load_nil(Unit, 32n, X.XArray.path(i)))

def XP.law.mark_set(-V: Data, +t: X.XArray<V>, +i: U32, +m: X.XMark, +v: V, +e: {X.XArray.load(V, t, i) == Some{v} : Maybe<&2, V>}) -> {X.XArray.get_mark(V, X.XArray.set_mark(V, t, i, m), i, m) == True{} : Bool}:
  match t:
    case X.XArray{+vals, +m0, +m1, +m2}:
      %Equal.sym(Maybe<&2, V>, X.XTree.load(V, 32n, X.XArray.path(i), vals), Some{v}, e) : {X.XArray.get_mark(V, X.XArray.set_mark.go(V, Maybe.is_some(&2, V, _), m, X.XArray.path(i), vals, m0, m1, m2), i, m) == True{} : Bool}
      XP.mark_set_go(V, vals, m0, m1, m2, i, m)

def XP.law.mark_set_absent(-V: Data, +t: X.XArray<V>, +i: U32, +m: X.XMark, +e: {X.XArray.load(V, t, i) == None{} : Maybe<&2, V>}) -> {X.XArray.set_mark(V, t, i, m) == t : X.XArray<V>}:
  match t:
    case X.XArray{+vals, +m0, +m1, +m2}:
      %Equal.sym(Maybe<&2, V>, X.XTree.load(V, 32n, X.XArray.path(i), vals), None{}, e) : {X.XArray.set_mark.go(V, Maybe.is_some(&2, V, _), m, X.XArray.path(i), vals, m0, m1, m2) == X.XArray{vals, m0, m1, m2} : X.XArray<V>}
      {==}

def XP.law.mark_clear(-V: Data, +t: X.XArray<V>, +i: U32, +m: X.XMark) -> {X.XArray.get_mark(V, X.XArray.clear_mark(V, t, i, m), i, m) == False{} : Bool}:
  match t:
    case X.XArray{vals, m0, m1, m2}:
      match m:
        case X.XMark0{}:
          XP.not_some(Unit, X.XTree.load(Unit, 32n, X.XArray.path(i), X.XTree.erase(Unit, 32n, X.XArray.path(i), m0)), XP.load_erase(Unit, 32n, X.XArray.path(i), m0))
        case X.XMark1{}:
          XP.not_some(Unit, X.XTree.load(Unit, 32n, X.XArray.path(i), X.XTree.erase(Unit, 32n, X.XArray.path(i), m1)), XP.load_erase(Unit, 32n, X.XArray.path(i), m1))
        case X.XMark2{}:
          XP.not_some(Unit, X.XTree.load(Unit, 32n, X.XArray.path(i), X.XTree.erase(Unit, 32n, X.XArray.path(i), m2)), XP.load_erase(Unit, 32n, X.XArray.path(i), m2))

def XP.law.mark_set_other_index(-V: Data, +t: X.XArray<V>, +i: U32, +j: U32, +m: X.XMark, +n: X.XMark, +e: {U32.is_eq(i, j) == False{} : Bool}) -> {X.XArray.get_mark(V, X.XArray.set_mark(V, t, i, m), j, n) == X.XArray.get_mark(V, t, j, n) : Bool}:
  match t:
    case X.XArray{+vals, m0, m1, m2}:
      XP.mark_set_index(V, Maybe.is_some(&2, V, X.XTree.load(V, 32n, X.XArray.path(i), vals)), vals, m0, m1, m2, i, j, m, n, e)

def XP.law.mark_set_other_mark(-V: Data, +t: X.XArray<V>, +i: U32, +j: U32, +m: X.XMark, +n: X.XMark, +e: {X.XMark.is_eq(m, n) == False{} : Bool}) -> {X.XArray.get_mark(V, X.XArray.set_mark(V, t, i, m), j, n) == X.XArray.get_mark(V, t, j, n) : Bool}:
  match t:
    case X.XArray{+vals, m0, m1, m2}:
      XP.mark_set_mark(V, Maybe.is_some(&2, V, X.XTree.load(V, 32n, X.XArray.path(i), vals)), vals, m0, m1, m2, i, j, m, n, e)

def XP.law.mark_clear_other_index(-V: Data, +t: X.XArray<V>, +i: U32, +j: U32, +m: X.XMark, +n: X.XMark, +e: {U32.is_eq(i, j) == False{} : Bool}) -> {X.XArray.get_mark(V, X.XArray.clear_mark(V, t, i, m), j, n) == X.XArray.get_mark(V, t, j, n) : Bool}:
  match t:
    case X.XArray{vals, m0, m1, m2}:
      match m n:
        case X.XMark0{} X.XMark0{}:
          XP.some_cong(Unit, X.XTree.load(Unit, 32n, X.XArray.path(j), X.XTree.erase(Unit, 32n, X.XArray.path(i), m0)), X.XTree.load(Unit, 32n, X.XArray.path(j), m0), XP.load_erase_other(Unit, 32n, X.XArray.path(i), X.XArray.path(j), m0, XP.ne_path(i, j, e)))
        case X.XMark1{} X.XMark1{}:
          XP.some_cong(Unit, X.XTree.load(Unit, 32n, X.XArray.path(j), X.XTree.erase(Unit, 32n, X.XArray.path(i), m1)), X.XTree.load(Unit, 32n, X.XArray.path(j), m1), XP.load_erase_other(Unit, 32n, X.XArray.path(i), X.XArray.path(j), m1, XP.ne_path(i, j, e)))
        case X.XMark2{} X.XMark2{}:
          XP.some_cong(Unit, X.XTree.load(Unit, 32n, X.XArray.path(j), X.XTree.erase(Unit, 32n, X.XArray.path(i), m2)), X.XTree.load(Unit, 32n, X.XArray.path(j), m2), XP.load_erase_other(Unit, 32n, X.XArray.path(i), X.XArray.path(j), m2, XP.ne_path(i, j, e)))
        case X.XMark0{} X.XMark1{}:
          {==}
        case X.XMark0{} X.XMark2{}:
          {==}
        case X.XMark1{} X.XMark0{}:
          {==}
        case X.XMark1{} X.XMark2{}:
          {==}
        case X.XMark2{} X.XMark0{}:
          {==}
        case X.XMark2{} X.XMark1{}:
          {==}

def XP.law.mark_clear_other_mark(-V: Data, +t: X.XArray<V>, +i: U32, +j: U32, +m: X.XMark, +n: X.XMark, +e: {X.XMark.is_eq(m, n) == False{} : Bool}) -> {X.XArray.get_mark(V, X.XArray.clear_mark(V, t, i, m), j, n) == X.XArray.get_mark(V, t, j, n) : Bool}:
  match t:
    case X.XArray{vals, m0, m1, m2}:
      match m n:
        case X.XMark0{} X.XMark0{}:
          Empty.absurd({X.XArray.get_mark(V, X.XArray.clear_mark(V, X.XArray{vals, m0, m1, m2}, i, X.XMark0{}), j, X.XMark0{}) == X.XArray.get_mark(V, X.XArray{vals, m0, m1, m2}, j, X.XMark0{}) : Bool}, XP.tf(e))
        case X.XMark1{} X.XMark1{}:
          Empty.absurd({X.XArray.get_mark(V, X.XArray.clear_mark(V, X.XArray{vals, m0, m1, m2}, i, X.XMark1{}), j, X.XMark1{}) == X.XArray.get_mark(V, X.XArray{vals, m0, m1, m2}, j, X.XMark1{}) : Bool}, XP.tf(e))
        case X.XMark2{} X.XMark2{}:
          Empty.absurd({X.XArray.get_mark(V, X.XArray.clear_mark(V, X.XArray{vals, m0, m1, m2}, i, X.XMark2{}), j, X.XMark2{}) == X.XArray.get_mark(V, X.XArray{vals, m0, m1, m2}, j, X.XMark2{}) : Bool}, XP.tf(e))
        case X.XMark0{} X.XMark1{}:
          {==}
        case X.XMark0{} X.XMark2{}:
          {==}
        case X.XMark1{} X.XMark0{}:
          {==}
        case X.XMark1{} X.XMark2{}:
          {==}
        case X.XMark2{} X.XMark0{}:
          {==}
        case X.XMark2{} X.XMark1{}:
          {==}

def XP.law.load_set_mark(-V: Data, +t: X.XArray<V>, +i: U32, +j: U32, +m: X.XMark) -> {X.XArray.load(V, X.XArray.set_mark(V, t, i, m), j) == X.XArray.load(V, t, j) : Maybe<&2, V>}:
  match t:
    case X.XArray{+vals, m0, m1, m2}:
      XP.load_set_mark_go(V, Maybe.is_some(&2, V, X.XTree.load(V, 32n, X.XArray.path(i), vals)), vals, m0, m1, m2, i, j, m)

def XP.law.load_clear_mark(-V: Data, +t: X.XArray<V>, +i: U32, +j: U32, +m: X.XMark) -> {X.XArray.load(V, X.XArray.clear_mark(V, t, i, m), j) == X.XArray.load(V, t, j) : Maybe<&2, V>}:
  match t:
    case X.XArray{vals, m0, m1, m2}:
      match m:
        case X.XMark0{}:
          {==}
        case X.XMark1{}:
          {==}
        case X.XMark2{}:
          {==}

def XP.law.mark_erase(-V: Data, +t: X.XArray<V>, +i: U32, +m: X.XMark) -> {X.XArray.get_mark(V, X.XArray.erase(V, t, i), i, m) == False{} : Bool}:
  match t:
    case X.XArray{vals, m0, m1, m2}:
      match m:
        case X.XMark0{}:
          XP.not_some(Unit, X.XTree.load(Unit, 32n, X.XArray.path(i), X.XTree.erase(Unit, 32n, X.XArray.path(i), m0)), XP.load_erase(Unit, 32n, X.XArray.path(i), m0))
        case X.XMark1{}:
          XP.not_some(Unit, X.XTree.load(Unit, 32n, X.XArray.path(i), X.XTree.erase(Unit, 32n, X.XArray.path(i), m1)), XP.load_erase(Unit, 32n, X.XArray.path(i), m1))
        case X.XMark2{}:
          XP.not_some(Unit, X.XTree.load(Unit, 32n, X.XArray.path(i), X.XTree.erase(Unit, 32n, X.XArray.path(i), m2)), XP.load_erase(Unit, 32n, X.XArray.path(i), m2))

def XP.law.mark_erase_other(-V: Data, +t: X.XArray<V>, +i: U32, +j: U32, +m: X.XMark, +e: {U32.is_eq(i, j) == False{} : Bool}) -> {X.XArray.get_mark(V, X.XArray.erase(V, t, i), j, m) == X.XArray.get_mark(V, t, j, m) : Bool}:
  match t:
    case X.XArray{vals, m0, m1, m2}:
      match m:
        case X.XMark0{}:
          XP.some_cong(Unit, X.XTree.load(Unit, 32n, X.XArray.path(j), X.XTree.erase(Unit, 32n, X.XArray.path(i), m0)), X.XTree.load(Unit, 32n, X.XArray.path(j), m0), XP.load_erase_other(Unit, 32n, X.XArray.path(i), X.XArray.path(j), m0, XP.ne_path(i, j, e)))
        case X.XMark1{}:
          XP.some_cong(Unit, X.XTree.load(Unit, 32n, X.XArray.path(j), X.XTree.erase(Unit, 32n, X.XArray.path(i), m1)), X.XTree.load(Unit, 32n, X.XArray.path(j), m1), XP.load_erase_other(Unit, 32n, X.XArray.path(i), X.XArray.path(j), m1, XP.ne_path(i, j, e)))
        case X.XMark2{}:
          XP.some_cong(Unit, X.XTree.load(Unit, 32n, X.XArray.path(j), X.XTree.erase(Unit, 32n, X.XArray.path(i), m2)), X.XTree.load(Unit, 32n, X.XArray.path(j), m2), XP.load_erase_other(Unit, 32n, X.XArray.path(i), X.XArray.path(j), m2, XP.ne_path(i, j, e)))

def XP.law.mark_store(-V: Data, +t: X.XArray<V>, +i: U32, +j: U32, +v: V, +m: X.XMark) -> {X.XArray.get_mark(V, X.XArray.store(V, t, i, v), j, m) == X.XArray.get_mark(V, t, j, m) : Bool}:
  match t:
    case X.XArray{vals, m0, m1, m2}:
      match m:
        case X.XMark0{}:
          {==}
        case X.XMark1{}:
          {==}
        case X.XMark2{}:
          {==}

def XP.law.find_marked_present(-V: Data, +t: X.XArray<V>, +s: U32, +m: X.XMark, +k: U32, +e: {X.XArray.find_marked(V, t, s, m) == Some{k} : Maybe<&2, U32>}) -> {X.XArray.get_mark(V, t, k, m) == True{} : Bool}:
  %e : XP.MPresent(V, t, m, _)
  XP.mfound_present(V, t, m, X.XTree.seek(Unit, 32n, X.XArray.path(s), X.XArray.marks(V, t, m), False{}), XP.seek_in(Unit, 32n, X.XArray.path(s), X.XArray.marks(V, t, m), False{}))

def XP.law.find_marked_at_or_after(-V: Data, +t: X.XArray<V>, +s: U32, +m: X.XMark, +k: U32, +e: {X.XArray.find_marked(V, t, s, m) == Some{k} : Maybe<&2, U32>}) -> {U32.is_le(s, k) == True{} : Bool}:
  %e : XP.FAfter(s, _)
  XP.found_after(s, X.XTree.seek(Unit, 32n, X.XArray.path(s), X.XArray.marks(V, t, m), False{}), XP.seek_after(Unit, 32n, X.XArray.path(s), X.XArray.marks(V, t, m), False{}))

def XP.law.find_marked_first(-V: Data, +t: X.XArray<V>, +s: U32, +m: X.XMark, +k: U32, +j: U32, +e: {X.XArray.find_marked(V, t, s, m) == Some{k} : Maybe<&2, U32>}, +h1: {U32.is_le(s, j) == True{} : Bool}, +h2: {U32.is_lt(j, k) == True{} : Bool}) -> {X.XArray.get_mark(V, t, j, m) == False{} : Bool}:
  XP.find_marked_first_at(V, t, s, m, k, j, e)(h1)(h2)

def XP.law.find_marked_none(-V: Data, +t: X.XArray<V>, +s: U32, +m: X.XMark, +j: U32, +e: {X.XArray.find_marked(V, t, s, m) == None{} : Maybe<&2, U32>}, +h: {U32.is_le(s, j) == True{} : Bool}) -> {X.XArray.get_mark(V, t, j, m) == False{} : Bool}:
  XP.find_marked_none_at(V, t, s, m, j, e)(h)

def Laws.vec_find():
  {==}

def Laws.vec_find_last():
  {==}

def Laws.vec_find_none():
  {==}

def Laws.vec_range():
  {==}

def Laws.vec_erase_empty():
  {==}

def Laws.vec_find_marked():
  {==}

def XP.law.insert_absent(-V: Data, +t: X.XArray<V>, +i: U32, +v: V, e: {X.XArray.load(V, t, i) == None{} : Maybe<&2, V>}) -> {X.XArray.insert(V, t, i, v) == Done{X.XArray.store(V, t, i, v)} : Result<&2, &2, X.XArrayError, X.XArray<V>>}:
  %Equal.sym(Maybe<&2, V>, X.XArray.load(V, t, i), None{}, e) : {X.XArray.insert.go(V, Maybe.is_some(&2, V, _), t, i, v) == Done{X.XArray.store(V, t, i, v)} : Result<&2, &2, X.XArrayError, X.XArray<V>>}
  {==}

def XP.law.insert_present(-V: Data, +t: X.XArray<V>, +i: U32, +v: V, -w: V, e: {X.XArray.load(V, t, i) == Some{w} : Maybe<&2, V>}) -> {X.XArray.insert(V, t, i, v) == Fail{X.XArrayBusy{}} : Result<&2, &2, X.XArrayError, X.XArray<V>>}:
  %Equal.sym(Maybe<&2, V>, X.XArray.load(V, t, i), Some{w}, e) : {X.XArray.insert.go(V, Maybe.is_some(&2, V, _), t, i, v) == Fail{X.XArrayBusy{}} : Result<&2, &2, X.XArrayError, X.XArray<V>>}
  {==}

# The marks' invariant (XArray.wf): XTree.sub(n, s, t) says every path that
# holds an entry of s holds one of t

def XW.and_l(x: Bool, -y: Bool, e: {Bool.and(x, y) == True{} : Bool}) -> {x == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, XP.ft(e))

def XW.and_r(x: Bool, -y: Bool, e: {Bool.and(x, y) == True{} : Bool}) -> {y == True{} : Bool}:
  match x:
    case True{}:
      e
    case False{}:
      Empty.absurd({y == True{} : Bool}, XP.ft(e))

def XW.and_i(-x: Bool, -y: Bool, ex: {x == True{} : Bool}, ey: {y == True{} : Bool}) -> {Bool.and(x, y) == True{} : Bool}:
  %Equal.sym(Bool, x, True{}, ex) : {Bool.and(_, y) == True{} : Bool}
  ey

def XW.sub_nil(-V: Data, n: Nat, -t: X.XTree<V>) -> {X.XTree.sub(V, n, X.XNil{}, t) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def XW.issome_nil(-V: Data, n: Nat, p: Word(n)) -> {Maybe.is_some(&2, V, X.XTree.load(V, n, p, X.XNil{})) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      match p:
        case WCon{b, bs}:
          match b:
            case False{}:
              {==}
            case True{}:
              {==}

# a path holding an entry of s holds one of t
def XW.sub_load(-V: Data, n: Nat, p: Word(n), +s: X.XTree<Unit>, +t: X.XTree<V>, +e: {X.XTree.sub(V, n, s, t) == True{} : Bool}, +f: {Maybe.is_some(&2, Unit, X.XTree.load(Unit, n, p, s)) == True{} : Bool}) -> {Maybe.is_some(&2, V, X.XTree.load(V, n, p, t)) == True{} : Bool}:
  match n:
    case 0n:
      match s:
        case X.XLeaf{u}:
          e
        case X.XNil{}:
          Empty.absurd({Maybe.is_some(&2, V, X.XTree.load(V, 0n, p, t)) == True{} : Bool}, XP.ft(f))
        case X.XBin{a, b}:
          Empty.absurd({Maybe.is_some(&2, V, X.XTree.load(V, 0n, p, t)) == True{} : Bool}, XP.ft(f))
    case 1n+ +m:
      match p:
        case WCon{c, +bs}:
          match c:
            case False{}:
              match s:
                case X.XBin{a, b}:
                  match t:
                    case X.XBin{lo, hi}:
                      XW.sub_load(V, m, bs, a, lo, XW.and_l(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e), f)
                    case X.XNil{}:
                      Equal.trans(Bool, False{}, Maybe.is_some(&2, V, X.XTree.load(V, m, bs, X.XNil{})), True{}, Equal.sym(Bool, Maybe.is_some(&2, V, X.XTree.load(V, m, bs, X.XNil{})), False{}, XW.issome_nil(V, m, bs)), XW.sub_load(V, m, bs, a, X.XNil{}, XW.and_l(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e), f))
                    case X.XLeaf{w}:
                      Equal.trans(Bool, False{}, Maybe.is_some(&2, V, X.XTree.load(V, m, bs, X.XNil{})), True{}, Equal.sym(Bool, Maybe.is_some(&2, V, X.XTree.load(V, m, bs, X.XNil{})), False{}, XW.issome_nil(V, m, bs)), XW.sub_load(V, m, bs, a, X.XNil{}, XW.and_l(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e), f))
                case X.XNil{}:
                  Empty.absurd({Maybe.is_some(&2, V, X.XTree.load(V, 1n+m, WCon{False{}, bs}, t)) == True{} : Bool}, XP.ft(f))
                case X.XLeaf{u}:
                  Empty.absurd({Maybe.is_some(&2, V, X.XTree.load(V, 1n+m, WCon{False{}, bs}, t)) == True{} : Bool}, XP.ft(f))
            case True{}:
              match s:
                case X.XBin{a, b}:
                  match t:
                    case X.XBin{lo, hi}:
                      XW.sub_load(V, m, bs, b, hi, XW.and_r(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e), f)
                    case X.XNil{}:
                      Equal.trans(Bool, False{}, Maybe.is_some(&2, V, X.XTree.load(V, m, bs, X.XNil{})), True{}, Equal.sym(Bool, Maybe.is_some(&2, V, X.XTree.load(V, m, bs, X.XNil{})), False{}, XW.issome_nil(V, m, bs)), XW.sub_load(V, m, bs, b, X.XNil{}, XW.and_r(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e), f))
                    case X.XLeaf{w}:
                      Equal.trans(Bool, False{}, Maybe.is_some(&2, V, X.XTree.load(V, m, bs, X.XNil{})), True{}, Equal.sym(Bool, Maybe.is_some(&2, V, X.XTree.load(V, m, bs, X.XNil{})), False{}, XW.issome_nil(V, m, bs)), XW.sub_load(V, m, bs, b, X.XNil{}, XW.and_r(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e), f))
                case X.XNil{}:
                  Empty.absurd({Maybe.is_some(&2, V, X.XTree.load(V, 1n+m, WCon{True{}, bs}, t)) == True{} : Bool}, XP.ft(f))
                case X.XLeaf{u}:
                  Empty.absurd({Maybe.is_some(&2, V, X.XTree.load(V, 1n+m, WCon{True{}, bs}, t)) == True{} : Bool}, XP.ft(f))

# a store into t keeps s within it
def XW.sub_store(-V: Data, n: Nat, p: Word(n), +t: X.XTree<V>, +s: X.XTree<Unit>, +v: V, +e: {X.XTree.sub(V, n, s, t) == True{} : Bool}) -> {X.XTree.sub(V, n, s, X.XTree.store(V, n, p, t, v)) == True{} : Bool}:
  match n:
    case 0n:
      match s:
        case X.XLeaf{u}:
          {==}
        case X.XNil{}:
          {==}
        case X.XBin{a, b}:
          {==}
    case 1n+ +m:
      match p:
        case WCon{c, +bs}:
          match c:
            case False{}:
              match t:
                case X.XBin{lo, hi}:
                  match s:
                    case X.XBin{a, b}:
                      XW.and_i(X.XTree.sub(V, m, a, X.XTree.store(V, m, bs, lo, v)), X.XTree.sub(V, m, b, hi), XW.sub_store(V, m, bs, lo, a, v, XW.and_l(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e)), XW.and_r(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e))
                    case X.XNil{}:
                      {==}
                    case X.XLeaf{u}:
                      {==}
                case X.XNil{}:
                  match s:
                    case X.XBin{a, b}:
                      XW.and_i(X.XTree.sub(V, m, a, X.XTree.store(V, m, bs, X.XNil{}, v)), X.XTree.sub(V, m, b, X.XNil{}), XW.sub_store(V, m, bs, X.XNil{}, a, v, XW.and_l(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e)), XW.and_r(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e))
                    case X.XNil{}:
                      {==}
                    case X.XLeaf{u}:
                      {==}
                case X.XLeaf{w}:
                  match s:
                    case X.XBin{a, b}:
                      XW.and_i(X.XTree.sub(V, m, a, X.XTree.store(V, m, bs, X.XNil{}, v)), X.XTree.sub(V, m, b, X.XNil{}), XW.sub_store(V, m, bs, X.XNil{}, a, v, XW.and_l(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e)), XW.and_r(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e))
                    case X.XNil{}:
                      {==}
                    case X.XLeaf{u}:
                      {==}
            case True{}:
              match t:
                case X.XBin{lo, hi}:
                  match s:
                    case X.XBin{a, b}:
                      XW.and_i(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, X.XTree.store(V, m, bs, hi, v)), XW.and_l(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e), XW.sub_store(V, m, bs, hi, b, v, XW.and_r(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e)))
                    case X.XNil{}:
                      {==}
                    case X.XLeaf{u}:
                      {==}
                case X.XNil{}:
                  match s:
                    case X.XBin{a, b}:
                      XW.and_i(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XTree.store(V, m, bs, X.XNil{}, v)), XW.and_l(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e), XW.sub_store(V, m, bs, X.XNil{}, b, v, XW.and_r(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e)))
                    case X.XNil{}:
                      {==}
                    case X.XLeaf{u}:
                      {==}
                case X.XLeaf{w}:
                  match s:
                    case X.XBin{a, b}:
                      XW.and_i(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XTree.store(V, m, bs, X.XNil{}, v)), XW.and_l(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e), XW.sub_store(V, m, bs, X.XNil{}, b, v, XW.and_r(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e)))
                    case X.XNil{}:
                      {==}
                    case X.XLeaf{u}:
                      {==}

# marking a path that holds an entry of t keeps s within t
def XW.sub_mark(-V: Data, n: Nat, p: Word(n), +t: X.XTree<V>, +s: X.XTree<Unit>, +e: {X.XTree.sub(V, n, s, t) == True{} : Bool}, +f: {Maybe.is_some(&2, V, X.XTree.load(V, n, p, t)) == True{} : Bool}) -> {X.XTree.sub(V, n, X.XTree.store(Unit, n, p, s, Unit{}), t) == True{} : Bool}:
  match n:
    case 0n:
      f
    case 1n+ +m:
      match p:
        case WCon{c, +bs}:
          match c:
            case False{}:
              match t:
                case X.XBin{lo, hi}:
                  match s:
                    case X.XBin{a, b}:
                      XW.and_i(X.XTree.sub(V, m, X.XTree.store(Unit, m, bs, a, Unit{}), lo), X.XTree.sub(V, m, b, hi), XW.sub_mark(V, m, bs, lo, a, XW.and_l(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e), f), XW.and_r(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e))
                    case X.XNil{}:
                      XW.and_i(X.XTree.sub(V, m, X.XTree.store(Unit, m, bs, X.XNil{}, Unit{}), lo), X.XTree.sub(V, m, X.XNil{}, hi), XW.sub_mark(V, m, bs, lo, X.XNil{}, XW.sub_nil(V, m, lo), f), XW.sub_nil(V, m, hi))
                    case X.XLeaf{u}:
                      XW.and_i(X.XTree.sub(V, m, X.XTree.store(Unit, m, bs, X.XNil{}, Unit{}), lo), X.XTree.sub(V, m, X.XNil{}, hi), XW.sub_mark(V, m, bs, lo, X.XNil{}, XW.sub_nil(V, m, lo), f), XW.sub_nil(V, m, hi))
                case X.XNil{}:
                  Empty.absurd({X.XTree.sub(V, 1n+m, X.XTree.store(Unit, 1n+m, WCon{False{}, bs}, s, Unit{}), X.XNil{}) == True{} : Bool}, XP.ft(f))
                case X.XLeaf{w}:
                  Empty.absurd({X.XTree.sub(V, 1n+m, X.XTree.store(Unit, 1n+m, WCon{False{}, bs}, s, Unit{}), X.XLeaf{w}) == True{} : Bool}, XP.ft(f))
            case True{}:
              match t:
                case X.XBin{lo, hi}:
                  match s:
                    case X.XBin{a, b}:
                      XW.and_i(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, X.XTree.store(Unit, m, bs, b, Unit{}), hi), XW.and_l(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e), XW.sub_mark(V, m, bs, hi, b, XW.and_r(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e), f))
                    case X.XNil{}:
                      XW.and_i(X.XTree.sub(V, m, X.XNil{}, lo), X.XTree.sub(V, m, X.XTree.store(Unit, m, bs, X.XNil{}, Unit{}), hi), XW.sub_nil(V, m, lo), XW.sub_mark(V, m, bs, hi, X.XNil{}, XW.sub_nil(V, m, hi), f))
                    case X.XLeaf{u}:
                      XW.and_i(X.XTree.sub(V, m, X.XNil{}, lo), X.XTree.sub(V, m, X.XTree.store(Unit, m, bs, X.XNil{}, Unit{}), hi), XW.sub_nil(V, m, lo), XW.sub_mark(V, m, bs, hi, X.XNil{}, XW.sub_nil(V, m, hi), f))
                case X.XNil{}:
                  Empty.absurd({X.XTree.sub(V, 1n+m, X.XTree.store(Unit, 1n+m, WCon{True{}, bs}, s, Unit{}), X.XNil{}) == True{} : Bool}, XP.ft(f))
                case X.XLeaf{w}:
                  Empty.absurd({X.XTree.sub(V, 1n+m, X.XTree.store(Unit, 1n+m, WCon{True{}, bs}, s, Unit{}), X.XLeaf{w}) == True{} : Bool}, XP.ft(f))

# join's halves, as the node of them, for sub on either side
def XW.join_sub(-V: Data, +m: Nat, +x: X.XTree<Unit>, +y: X.XTree<Unit>, +t: X.XTree<V>) -> {X.XTree.sub(V, 1n+m, X.XTree.join(Unit, x, y), t) == X.XTree.sub(V, 1n+m, X.XBin{x, y}, t) : Bool}:
  match x:
    case X.XNil{}:
      match y:
        case X.XNil{}:
          match t:
            case X.XBin{c, d}:
              Equal.sym(Bool, Bool.and(X.XTree.sub(V, m, X.XNil{}, c), X.XTree.sub(V, m, X.XNil{}, d)), True{}, XW.and_i(X.XTree.sub(V, m, X.XNil{}, c), X.XTree.sub(V, m, X.XNil{}, d), XW.sub_nil(V, m, c), XW.sub_nil(V, m, d)))
            case X.XNil{}:
              Equal.sym(Bool, Bool.and(X.XTree.sub(V, m, X.XNil{}, X.XNil{}), X.XTree.sub(V, m, X.XNil{}, X.XNil{})), True{}, XW.and_i(X.XTree.sub(V, m, X.XNil{}, X.XNil{}), X.XTree.sub(V, m, X.XNil{}, X.XNil{}), XW.sub_nil(V, m, X.XNil{}), XW.sub_nil(V, m, X.XNil{})))
            case X.XLeaf{w}:
              Equal.sym(Bool, Bool.and(X.XTree.sub(V, m, X.XNil{}, X.XNil{}), X.XTree.sub(V, m, X.XNil{}, X.XNil{})), True{}, XW.and_i(X.XTree.sub(V, m, X.XNil{}, X.XNil{}), X.XTree.sub(V, m, X.XNil{}, X.XNil{}), XW.sub_nil(V, m, X.XNil{}), XW.sub_nil(V, m, X.XNil{})))
        case X.XLeaf{u}:
          {==}
        case X.XBin{a, b}:
          {==}
    case X.XLeaf{u}:
      {==}
    case X.XBin{a, b}:
      {==}

def XW.sub_join(-V: Data, +m: Nat, +z: X.XTree<V>, +w: X.XTree<V>, +s: X.XTree<Unit>) -> {X.XTree.sub(V, 1n+m, s, X.XTree.join(V, z, w)) == X.XTree.sub(V, 1n+m, s, X.XBin{z, w}) : Bool}:
  match z:
    case X.XNil{}:
      match w:
        case X.XNil{}:
          match s:
            case X.XBin{a, b}:
              {==}
            case X.XNil{}:
              {==}
            case X.XLeaf{u}:
              {==}
        case X.XLeaf{u}:
          {==}
        case X.XBin{a, b}:
          {==}
    case X.XLeaf{u}:
      {==}
    case X.XBin{a, b}:
      {==}

# an erase from s keeps it within t
def XW.sub_clear(-V: Data, n: Nat, p: Word(n), +s: X.XTree<Unit>, +t: X.XTree<V>, +e: {X.XTree.sub(V, n, s, t) == True{} : Bool}) -> {X.XTree.sub(V, n, X.XTree.erase(Unit, n, p, s), t) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      match p:
        case WCon{c, +bs}:
          match c:
            case False{}:
              match s:
                case X.XBin{a, b}:
                  match t:
                    case X.XBin{lo, hi}:
                      Equal.trans(Bool, X.XTree.sub(V, 1n+m, X.XTree.join(Unit, X.XTree.erase(Unit, m, bs, a), b), X.XBin{lo, hi}), X.XTree.sub(V, 1n+m, X.XBin{X.XTree.erase(Unit, m, bs, a), b}, X.XBin{lo, hi}), True{}, XW.join_sub(V, m, X.XTree.erase(Unit, m, bs, a), b, X.XBin{lo, hi}), XW.and_i(X.XTree.sub(V, m, X.XTree.erase(Unit, m, bs, a), lo), X.XTree.sub(V, m, b, hi), XW.sub_clear(V, m, bs, a, lo, XW.and_l(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e)), XW.and_r(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e)))
                    case X.XNil{}:
                      Equal.trans(Bool, X.XTree.sub(V, 1n+m, X.XTree.join(Unit, X.XTree.erase(Unit, m, bs, a), b), X.XNil{}), X.XTree.sub(V, 1n+m, X.XBin{X.XTree.erase(Unit, m, bs, a), b}, X.XNil{}), True{}, XW.join_sub(V, m, X.XTree.erase(Unit, m, bs, a), b, X.XNil{}), XW.and_i(X.XTree.sub(V, m, X.XTree.erase(Unit, m, bs, a), X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), XW.sub_clear(V, m, bs, a, X.XNil{}, XW.and_l(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e)), XW.and_r(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e)))
                    case X.XLeaf{w}:
                      Equal.trans(Bool, X.XTree.sub(V, 1n+m, X.XTree.join(Unit, X.XTree.erase(Unit, m, bs, a), b), X.XLeaf{w}), X.XTree.sub(V, 1n+m, X.XBin{X.XTree.erase(Unit, m, bs, a), b}, X.XLeaf{w}), True{}, XW.join_sub(V, m, X.XTree.erase(Unit, m, bs, a), b, X.XLeaf{w}), XW.and_i(X.XTree.sub(V, m, X.XTree.erase(Unit, m, bs, a), X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), XW.sub_clear(V, m, bs, a, X.XNil{}, XW.and_l(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e)), XW.and_r(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e)))
                case X.XNil{}:
                  {==}
                case X.XLeaf{u}:
                  {==}
            case True{}:
              match s:
                case X.XBin{a, b}:
                  match t:
                    case X.XBin{lo, hi}:
                      Equal.trans(Bool, X.XTree.sub(V, 1n+m, X.XTree.join(Unit, a, X.XTree.erase(Unit, m, bs, b)), X.XBin{lo, hi}), X.XTree.sub(V, 1n+m, X.XBin{a, X.XTree.erase(Unit, m, bs, b)}, X.XBin{lo, hi}), True{}, XW.join_sub(V, m, a, X.XTree.erase(Unit, m, bs, b), X.XBin{lo, hi}), XW.and_i(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, X.XTree.erase(Unit, m, bs, b), hi), XW.and_l(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e), XW.sub_clear(V, m, bs, b, hi, XW.and_r(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e))))
                    case X.XNil{}:
                      Equal.trans(Bool, X.XTree.sub(V, 1n+m, X.XTree.join(Unit, a, X.XTree.erase(Unit, m, bs, b)), X.XNil{}), X.XTree.sub(V, 1n+m, X.XBin{a, X.XTree.erase(Unit, m, bs, b)}, X.XNil{}), True{}, XW.join_sub(V, m, a, X.XTree.erase(Unit, m, bs, b), X.XNil{}), XW.and_i(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, X.XTree.erase(Unit, m, bs, b), X.XNil{}), XW.and_l(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e), XW.sub_clear(V, m, bs, b, X.XNil{}, XW.and_r(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e))))
                    case X.XLeaf{w}:
                      Equal.trans(Bool, X.XTree.sub(V, 1n+m, X.XTree.join(Unit, a, X.XTree.erase(Unit, m, bs, b)), X.XLeaf{w}), X.XTree.sub(V, 1n+m, X.XBin{a, X.XTree.erase(Unit, m, bs, b)}, X.XLeaf{w}), True{}, XW.join_sub(V, m, a, X.XTree.erase(Unit, m, bs, b), X.XLeaf{w}), XW.and_i(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, X.XTree.erase(Unit, m, bs, b), X.XNil{}), XW.and_l(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e), XW.sub_clear(V, m, bs, b, X.XNil{}, XW.and_r(X.XTree.sub(V, m, a, X.XNil{}), X.XTree.sub(V, m, b, X.XNil{}), e))))
                case X.XNil{}:
                  {==}
                case X.XLeaf{u}:
                  {==}

# an erase from both keeps s within t
def XW.sub_erase(-V: Data, n: Nat, p: Word(n), +s: X.XTree<Unit>, +t: X.XTree<V>, +e: {X.XTree.sub(V, n, s, t) == True{} : Bool}) -> {X.XTree.sub(V, n, X.XTree.erase(Unit, n, p, s), X.XTree.erase(V, n, p, t)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +m:
      match p:
        case WCon{c, +bs}:
          match c:
            case False{}:
              match s:
                case X.XBin{a, b}:
                  match t:
                    case X.XBin{lo, hi}:
                      Equal.trans(Bool, X.XTree.sub(V, 1n+m, X.XTree.join(Unit, X.XTree.erase(Unit, m, bs, a), b), X.XTree.join(V, X.XTree.erase(V, m, bs, lo), hi)), X.XTree.sub(V, 1n+m, X.XTree.join(Unit, X.XTree.erase(Unit, m, bs, a), b), X.XBin{X.XTree.erase(V, m, bs, lo), hi}), True{}, XW.sub_join(V, m, X.XTree.erase(V, m, bs, lo), hi, X.XTree.join(Unit, X.XTree.erase(Unit, m, bs, a), b)), Equal.trans(Bool, X.XTree.sub(V, 1n+m, X.XTree.join(Unit, X.XTree.erase(Unit, m, bs, a), b), X.XBin{X.XTree.erase(V, m, bs, lo), hi}), X.XTree.sub(V, 1n+m, X.XBin{X.XTree.erase(Unit, m, bs, a), b}, X.XBin{X.XTree.erase(V, m, bs, lo), hi}), True{}, XW.join_sub(V, m, X.XTree.erase(Unit, m, bs, a), b, X.XBin{X.XTree.erase(V, m, bs, lo), hi}), XW.and_i(X.XTree.sub(V, m, X.XTree.erase(Unit, m, bs, a), X.XTree.erase(V, m, bs, lo)), X.XTree.sub(V, m, b, hi), XW.sub_erase(V, m, bs, a, lo, XW.and_l(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e)), XW.and_r(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e))))
                    case X.XNil{}:
                      XW.sub_clear(V, 1n+m, WCon{False{}, bs}, X.XBin{a, b}, X.XNil{}, e)
                    case X.XLeaf{w}:
                      XW.sub_clear(V, 1n+m, WCon{False{}, bs}, X.XBin{a, b}, X.XLeaf{w}, e)
                case X.XNil{}:
                  {==}
                case X.XLeaf{u}:
                  {==}
            case True{}:
              match s:
                case X.XBin{a, b}:
                  match t:
                    case X.XBin{lo, hi}:
                      Equal.trans(Bool, X.XTree.sub(V, 1n+m, X.XTree.join(Unit, a, X.XTree.erase(Unit, m, bs, b)), X.XTree.join(V, lo, X.XTree.erase(V, m, bs, hi))), X.XTree.sub(V, 1n+m, X.XTree.join(Unit, a, X.XTree.erase(Unit, m, bs, b)), X.XBin{lo, X.XTree.erase(V, m, bs, hi)}), True{}, XW.sub_join(V, m, lo, X.XTree.erase(V, m, bs, hi), X.XTree.join(Unit, a, X.XTree.erase(Unit, m, bs, b))), Equal.trans(Bool, X.XTree.sub(V, 1n+m, X.XTree.join(Unit, a, X.XTree.erase(Unit, m, bs, b)), X.XBin{lo, X.XTree.erase(V, m, bs, hi)}), X.XTree.sub(V, 1n+m, X.XBin{a, X.XTree.erase(Unit, m, bs, b)}, X.XBin{lo, X.XTree.erase(V, m, bs, hi)}), True{}, XW.join_sub(V, m, a, X.XTree.erase(Unit, m, bs, b), X.XBin{lo, X.XTree.erase(V, m, bs, hi)}), XW.and_i(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, X.XTree.erase(Unit, m, bs, b), X.XTree.erase(V, m, bs, hi)), XW.and_l(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e), XW.sub_erase(V, m, bs, b, hi, XW.and_r(X.XTree.sub(V, m, a, lo), X.XTree.sub(V, m, b, hi), e)))))
                    case X.XNil{}:
                      XW.sub_clear(V, 1n+m, WCon{True{}, bs}, X.XBin{a, b}, X.XNil{}, e)
                    case X.XLeaf{w}:
                      XW.sub_clear(V, 1n+m, WCon{True{}, bs}, X.XBin{a, b}, X.XLeaf{w}, e)
                case X.XNil{}:
                  {==}
                case X.XLeaf{u}:
                  {==}

# The invariant's laws
def XW.law.wf_empty(-V: Data) -> {X.XArray.wf(V, X.XArray.empty(V)) == True{} : Bool}:
  {==}

def XW.law.wf_store(-V: Data, +t: X.XArray<V>, +i: U32, +v: V, +e: {X.XArray.wf(V, t) == True{} : Bool}) -> {X.XArray.wf(V, X.XArray.store(V, t, i, v)) == True{} : Bool}:
  match t:
    case X.XArray{+vals, +m0, +m1, +m2}:
      XW.and_i(X.XTree.sub(V, 32n, m0, X.XTree.store(V, 32n, X.XArray.path(i), vals, v)), Bool.and(X.XTree.sub(V, 32n, m1, X.XTree.store(V, 32n, X.XArray.path(i), vals, v)), X.XTree.sub(V, 32n, m2, X.XTree.store(V, 32n, X.XArray.path(i), vals, v))), XW.sub_store(V, 32n, X.XArray.path(i), vals, m0, v, XW.and_l(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e)), XW.and_i(X.XTree.sub(V, 32n, m1, X.XTree.store(V, 32n, X.XArray.path(i), vals, v)), X.XTree.sub(V, 32n, m2, X.XTree.store(V, 32n, X.XArray.path(i), vals, v)), XW.sub_store(V, 32n, X.XArray.path(i), vals, m1, v, XW.and_l(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e))), XW.sub_store(V, 32n, X.XArray.path(i), vals, m2, v, XW.and_r(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e)))))

def XW.law.wf_erase(-V: Data, +t: X.XArray<V>, +i: U32, +e: {X.XArray.wf(V, t) == True{} : Bool}) -> {X.XArray.wf(V, X.XArray.erase(V, t, i)) == True{} : Bool}:
  match t:
    case X.XArray{+vals, +m0, +m1, +m2}:
      XW.and_i(X.XTree.sub(V, 32n, X.XTree.erase(Unit, 32n, X.XArray.path(i), m0), X.XTree.erase(V, 32n, X.XArray.path(i), vals)), Bool.and(X.XTree.sub(V, 32n, X.XTree.erase(Unit, 32n, X.XArray.path(i), m1), X.XTree.erase(V, 32n, X.XArray.path(i), vals)), X.XTree.sub(V, 32n, X.XTree.erase(Unit, 32n, X.XArray.path(i), m2), X.XTree.erase(V, 32n, X.XArray.path(i), vals))), XW.sub_erase(V, 32n, X.XArray.path(i), m0, vals, XW.and_l(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e)), XW.and_i(X.XTree.sub(V, 32n, X.XTree.erase(Unit, 32n, X.XArray.path(i), m1), X.XTree.erase(V, 32n, X.XArray.path(i), vals)), X.XTree.sub(V, 32n, X.XTree.erase(Unit, 32n, X.XArray.path(i), m2), X.XTree.erase(V, 32n, X.XArray.path(i), vals)), XW.sub_erase(V, 32n, X.XArray.path(i), m1, vals, XW.and_l(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e))), XW.sub_erase(V, 32n, X.XArray.path(i), m2, vals, XW.and_r(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e)))))

def XW.set_go(-V: Data, pr: Bool, +m: X.XMark, +p: Word(32n), +vals: X.XTree<V>, +m0: X.XTree<Unit>, +m1: X.XTree<Unit>, +m2: X.XTree<Unit>, +hp: {Maybe.is_some(&2, V, X.XTree.load(V, 32n, p, vals)) == pr : Bool}, +e: {X.XArray.wf(V, X.XArray{vals, m0, m1, m2}) == True{} : Bool}) -> {X.XArray.wf(V, X.XArray.set_mark.go(V, pr, m, p, vals, m0, m1, m2)) == True{} : Bool}:
  match pr:
    case False{}:
      e
    case True{}:
      match m:
        case X.XMark0{}:
          XW.and_i(X.XTree.sub(V, 32n, X.XTree.store(Unit, 32n, p, m0, Unit{}), vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), XW.sub_mark(V, 32n, p, vals, m0, XW.and_l(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e), hp), XW.and_i(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_l(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e)), XW.and_r(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e))))
        case X.XMark1{}:
          XW.and_i(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, X.XTree.store(Unit, 32n, p, m1, Unit{}), vals), X.XTree.sub(V, 32n, m2, vals)), XW.and_l(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e), XW.and_i(X.XTree.sub(V, 32n, X.XTree.store(Unit, 32n, p, m1, Unit{}), vals), X.XTree.sub(V, 32n, m2, vals), XW.sub_mark(V, 32n, p, vals, m1, XW.and_l(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e)), hp), XW.and_r(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e))))
        case X.XMark2{}:
          XW.and_i(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, X.XTree.store(Unit, 32n, p, m2, Unit{}), vals)), XW.and_l(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e), XW.and_i(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, X.XTree.store(Unit, 32n, p, m2, Unit{}), vals), XW.and_l(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e)), XW.sub_mark(V, 32n, p, vals, m2, XW.and_r(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e)), hp)))

def XW.law.wf_set_mark(-V: Data, +t: X.XArray<V>, +i: U32, +m: X.XMark, +e: {X.XArray.wf(V, t) == True{} : Bool}) -> {X.XArray.wf(V, X.XArray.set_mark(V, t, i, m)) == True{} : Bool}:
  match t:
    case X.XArray{+vals, +m0, +m1, +m2}:
      XW.set_go(V, Maybe.is_some(&2, V, X.XTree.load(V, 32n, X.XArray.path(i), vals)), m, X.XArray.path(i), vals, m0, m1, m2, {==}, e)

def XW.law.wf_clear_mark(-V: Data, +t: X.XArray<V>, +i: U32, +m: X.XMark, +e: {X.XArray.wf(V, t) == True{} : Bool}) -> {X.XArray.wf(V, X.XArray.clear_mark(V, t, i, m)) == True{} : Bool}:
  match t:
    case X.XArray{+vals, +m0, +m1, +m2}:
      match m:
        case X.XMark0{}:
          XW.and_i(X.XTree.sub(V, 32n, X.XTree.erase(Unit, 32n, X.XArray.path(i), m0), vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), XW.sub_clear(V, 32n, X.XArray.path(i), m0, vals, XW.and_l(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e)), XW.and_i(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_l(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e)), XW.and_r(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e))))
        case X.XMark1{}:
          XW.and_i(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, X.XTree.erase(Unit, 32n, X.XArray.path(i), m1), vals), X.XTree.sub(V, 32n, m2, vals)), XW.and_l(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e), XW.and_i(X.XTree.sub(V, 32n, X.XTree.erase(Unit, 32n, X.XArray.path(i), m1), vals), X.XTree.sub(V, 32n, m2, vals), XW.sub_clear(V, 32n, X.XArray.path(i), m1, vals, XW.and_l(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e))), XW.and_r(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e))))
        case X.XMark2{}:
          XW.and_i(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, X.XTree.erase(Unit, 32n, X.XArray.path(i), m2), vals)), XW.and_l(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e), XW.and_i(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, X.XTree.erase(Unit, 32n, X.XArray.path(i), m2), vals), XW.and_l(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e)), XW.sub_clear(V, 32n, X.XArray.path(i), m2, vals, XW.and_r(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e)))))

def XW.law.wf_mark_present(-V: Data, +t: X.XArray<V>, +i: U32, +m: X.XMark, +e: {X.XArray.wf(V, t) == True{} : Bool}, +f: {X.XArray.get_mark(V, t, i, m) == True{} : Bool}) -> {Maybe.is_some(&2, V, X.XArray.load(V, t, i)) == True{} : Bool}:
  match t:
    case X.XArray{+vals, +m0, +m1, +m2}:
      match m:
        case X.XMark0{}:
          XW.sub_load(V, 32n, X.XArray.path(i), m0, vals, XW.and_l(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e), f)
        case X.XMark1{}:
          XW.sub_load(V, 32n, X.XArray.path(i), m1, vals, XW.and_l(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e)), f)
        case X.XMark2{}:
          XW.sub_load(V, 32n, X.XArray.path(i), m2, vals, XW.and_r(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals), XW.and_r(X.XTree.sub(V, 32n, m0, vals), Bool.and(X.XTree.sub(V, 32n, m1, vals), X.XTree.sub(V, 32n, m2, vals)), e)), f)


# Each law, from its proof above

def Laws.insert_absent(V, t, i, v, e):
  XP.law.insert_absent(V, t, i, v, e)

def Laws.insert_present(V, t, i, v, w, e):
  XP.law.insert_present(V, t, i, v, w, e)

def Laws.load_empty(V, i):
  XP.law.load_empty(V, i)

def Laws.load_store(V, t, i, v):
  XP.law.load_store(V, t, i, v)

def Laws.load_store_other(V, t, i, j, v, e):
  XP.law.load_store_other(V, t, i, j, v, e)

def Laws.load_erase(V, t, i):
  XP.law.load_erase(V, t, i)

def Laws.load_erase_other(V, t, i, j, e):
  XP.law.load_erase_other(V, t, i, j, e)

def Laws.is_empty_empty(V):
  XP.law.is_empty_empty(V)

def Laws.is_empty_load(V, t, i, e):
  XP.law.is_empty_load(V, t, i, e)

def Laws.is_empty_store(V, t, i, v):
  XP.law.is_empty_store(V, t, i, v)

def Laws.is_empty_false(V, t, e):
  XP.law.is_empty_false(V, t, e)

def Laws.find_present(V, t, s, k, e):
  XP.law.find_present(V, t, s, k, e)

def Laws.find_at_or_after(V, t, s, k, e):
  XP.law.find_at_or_after(V, t, s, k, e)

def Laws.find_first(V, t, s, k, j, e, h1, h2):
  XP.law.find_first(V, t, s, k, j, e, h1, h2)

def Laws.find_none(V, t, s, j, e, h):
  XP.law.find_none(V, t, s, j, e, h)

def Laws.find_last_present(V, t, s, k, e):
  XP.law.find_last_present(V, t, s, k, e)

def Laws.find_last_at_or_before(V, t, s, k, e):
  XP.law.find_last_at_or_before(V, t, s, k, e)

def Laws.find_last_last(V, t, s, k, j, e, h1, h2):
  XP.law.find_last_last(V, t, s, k, j, e, h1, h2)

def Laws.find_last_none(V, t, s, j, e, h):
  XP.law.find_last_none(V, t, s, j, e, h)

def Laws.range_present(V, t, a, b, k, i, v, e):
  XP.law.range_present(V, t, a, b, k, i, v, e)

def Laws.range_from(V, t, a, b, k, i, v, e):
  XP.law.range_from(V, t, a, b, k, i, v, e)

def Laws.range_to(V, t, a, b, k, i, v, e):
  XP.law.range_to(V, t, a, b, k, i, v, e)

def Laws.range_ascending(V, t, a, b, k, i, v, j, w, e1, e2):
  XP.law.range_ascending(V, t, a, b, k, i, v, j, w, e1, e2)

def Laws.range_complete(V, t, a, b, i, v, h1, h2, h3):
  XP.law.range_complete(V, t, a, b, i, v, h1, h2, h3)

def Laws.mark_empty(V, i, m):
  XP.law.mark_empty(V, i, m)

def Laws.mark_set(V, t, i, m, v, e):
  XP.law.mark_set(V, t, i, m, v, e)

def Laws.mark_set_absent(V, t, i, m, e):
  XP.law.mark_set_absent(V, t, i, m, e)

def Laws.mark_clear(V, t, i, m):
  XP.law.mark_clear(V, t, i, m)

def Laws.mark_set_other_index(V, t, i, j, m, n, e):
  XP.law.mark_set_other_index(V, t, i, j, m, n, e)

def Laws.mark_set_other_mark(V, t, i, j, m, n, e):
  XP.law.mark_set_other_mark(V, t, i, j, m, n, e)

def Laws.mark_clear_other_index(V, t, i, j, m, n, e):
  XP.law.mark_clear_other_index(V, t, i, j, m, n, e)

def Laws.mark_clear_other_mark(V, t, i, j, m, n, e):
  XP.law.mark_clear_other_mark(V, t, i, j, m, n, e)

def Laws.load_set_mark(V, t, i, j, m):
  XP.law.load_set_mark(V, t, i, j, m)

def Laws.load_clear_mark(V, t, i, j, m):
  XP.law.load_clear_mark(V, t, i, j, m)

def Laws.mark_erase(V, t, i, m):
  XP.law.mark_erase(V, t, i, m)

def Laws.mark_erase_other(V, t, i, j, m, e):
  XP.law.mark_erase_other(V, t, i, j, m, e)

def Laws.mark_store(V, t, i, j, v, m):
  XP.law.mark_store(V, t, i, j, v, m)

def Laws.find_marked_present(V, t, s, m, k, e):
  XP.law.find_marked_present(V, t, s, m, k, e)

def Laws.find_marked_at_or_after(V, t, s, m, k, e):
  XP.law.find_marked_at_or_after(V, t, s, m, k, e)

def Laws.find_marked_first(V, t, s, m, k, j, e, h1, h2):
  XP.law.find_marked_first(V, t, s, m, k, j, e, h1, h2)

def Laws.find_marked_none(V, t, s, m, j, e, h):
  XP.law.find_marked_none(V, t, s, m, j, e, h)

def Laws.wf_empty(V):
  XW.law.wf_empty(V)

def Laws.wf_store(V, t, i, v, e):
  XW.law.wf_store(V, t, i, v, e)

def Laws.wf_erase(V, t, i, e):
  XW.law.wf_erase(V, t, i, e)

def Laws.wf_set_mark(V, t, i, m, e):
  XW.law.wf_set_mark(V, t, i, m, e)

def Laws.wf_clear_mark(V, t, i, m, e):
  XW.law.wf_clear_mark(V, t, i, m, e)

def Laws.wf_mark_present(V, t, i, m, e, f):
  XW.law.wf_mark_present(V, t, i, m, e, f)
