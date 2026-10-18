import Base
import ../bytes/bytes.bend as B
import ../ext2/dir.bend as DR
import ./htree.bend as T
import ./htwrite.bend as HW
import ./jlog.bend as JL
import ./jsuper.bend as J
import ./jblock.bend as JB
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../blockdev/blockdev.bend as D
import ../blockdev/LAWS.bend as BDL
import ../blockdev/PROOF.bend as BDP
import ./error.bend as E
import ./jwrite.bend as JW
import ./devwrite.bend as DW
import ./LAWS.bend as Laws

# Logic

def Ext4Proof.disc(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

def Ext4Proof.clash(h: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, h) : Ext4Proof.disc(_)
  Unit{}

def Ext4Proof.absurd(-A: Type, e: Empty) -> A:
  match e:

def Ext4Proof.no(-A: Type, h: {False{} == True{} : Bool}) -> A:
  Ext4Proof.absurd(A, Ext4Proof.clash(h))

def Ext4Proof.and_l(+a: Bool, +b: Bool) -> {Bool.and(a, b) == True{} : Bool} -> {a == True{} : Bool}:
  match a:
    case True{}:
      h => {==}
    case False{}:
      h => Ext4Proof.no({False{} == True{} : Bool}, h)

def Ext4Proof.and_r(+a: Bool, +b: Bool) -> {Bool.and(a, b) == True{} : Bool} -> {b == True{} : Bool}:
  match a:
    case True{}:
      h => h
    case False{}:
      h => Ext4Proof.no({b == True{} : Bool}, h)

# Natural numbers: comparisons

# a < x <= h: a is not h
def Ext4Proof.lt_le_ne(+a: Nat, +x: Nat, +h: Nat) -> {Nat.is_lt(a, x) == True{} : Bool} -> {Nat.is_le(x, h) == True{} : Bool} -> {Nat.is_eq(a, h) == False{} : Bool}:
  match a x h:
    case _ 0n _:
      p => q => Ext4Proof.no({Nat.is_eq(a, h) == False{} : Bool}, p)
    case 0n 1n+xp 0n:
      p => q => Ext4Proof.no({Nat.is_eq(0n, 0n) == False{} : Bool}, q)
    case 0n 1n+xp 1n+hp:
      p => q => {==}
    case 1n+ap 1n+xp 0n:
      p => q => Ext4Proof.no({Nat.is_eq(1n+ap, 0n) == False{} : Bool}, q)
    case 1n+ap 1n+xp 1n+hp:
      p => q => Ext4Proof.lt_le_ne(ap, xp, hp, p, q)

# h < x <= a: a is not h
def Ext4Proof.le_lt_ne(+x: Nat, +a: Nat, +h: Nat) -> {Nat.is_le(x, a) == True{} : Bool} -> {Nat.is_lt(h, x) == True{} : Bool} -> {Nat.is_eq(a, h) == False{} : Bool}:
  match x a h:
    case 0n _ 0n:
      p => q => Ext4Proof.no({Nat.is_eq(a, 0n) == False{} : Bool}, q)
    case 0n _ 1n+hp:
      p => q => Ext4Proof.no({Nat.is_eq(a, 1n+hp) == False{} : Bool}, q)
    case 1n+xp 0n _:
      p => q => Ext4Proof.no({Nat.is_eq(0n, h) == False{} : Bool}, p)
    case 1n+xp 1n+ap 0n:
      p => q => {==}
    case 1n+xp 1n+ap 1n+hp:
      p => q => Ext4Proof.le_lt_ne(xp, ap, hp, p, q)

# h < a <= b: h < b
def Ext4Proof.lt_le_lt(+h: Nat, +a: Nat, +b: Nat) -> {Nat.is_lt(h, a) == True{} : Bool} -> {Nat.is_le(a, b) == True{} : Bool} -> {Nat.is_lt(h, b) == True{} : Bool}:
  match h a b:
    case 0n 0n _:
      p => q => Ext4Proof.no({Nat.is_lt(0n, b) == True{} : Bool}, p)
    case 1n+hp 0n _:
      p => q => Ext4Proof.no({Nat.is_lt(1n+hp, b) == True{} : Bool}, p)
    case _ 1n+ap 0n:
      p => q => Ext4Proof.no({Nat.is_lt(h, 0n) == True{} : Bool}, q)
    case 0n 1n+ap 1n+bp:
      p => q => {==}
    case 1n+hp 1n+ap 1n+bp:
      p => q => Ext4Proof.lt_le_lt(hp, ap, bp, p, q)

# not (a <= b): b < a
def Ext4Proof.not_le_lt(+a: Nat, +b: Nat) -> {Nat.is_le(a, b) == False{} : Bool} -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      p => Ext4Proof.no({Nat.is_lt(0n, 0n) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, p))
    case 0n 1n+bp:
      p => Ext4Proof.no({Nat.is_lt(1n+bp, 0n) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, p))
    case 1n+ap 0n:
      p => {==}
    case 1n+ap 1n+bp:
      p => Ext4Proof.not_le_lt(ap, bp, p)

def Ext4Proof.ne_clash(+x: Bool, a: {x == True{} : Bool}, b: {x == False{} : Bool}) -> {False{} == True{} : Bool}:
  Equal.trans(Bool, False{}, x, True{}, Equal.sym(Bool, x, False{}, b), a)

# Htree: a leaf none of whose entries can have hash h has no entry named n

def Ext4Proof.find_lt.at(b: Bool, +e: T.Ext4HtEnt, +t: List<&2, T.Ext4HtEnt>, +n: B.Octets, +h: Nat, +x: Nat, ih: {T.Ext4Htree.named(t, n, h) == True{} : Bool} -> {T.Ext4Htree.all_lt(t, x) == True{} : Bool} -> {Nat.is_le(x, h) == True{} : Bool} -> {T.Ext4Htree.find_ent(t, n) == None{} : Maybe<&2, T.Ext4HtEnt>}) -> {Bool.and(Bool.or(Bool.not(b), Nat.is_eq(T.Ext4HtEnt.hash(e), h)), T.Ext4Htree.named(t, n, h)) == True{} : Bool} -> {Bool.and(Nat.is_lt(T.Ext4HtEnt.hash(e), x), T.Ext4Htree.all_lt(t, x)) == True{} : Bool} -> {Nat.is_le(x, h) == True{} : Bool} -> {T.Ext4Htree.find.go(~T.Ext4HtEnt, ~T.Ext4HtEnt.name, Con{e, t}, b, n) == None{} : Maybe<&2, T.Ext4HtEnt>}:
  match b:
    case True{}:
      hn => hl => hx =>
        +k = Ext4Proof.and_l(Nat.is_eq(T.Ext4HtEnt.hash(e), h), T.Ext4Htree.named(t, n, h), hn)
        +lt = Ext4Proof.and_l(Nat.is_lt(T.Ext4HtEnt.hash(e), x), T.Ext4Htree.all_lt(t, x), hl)
        Ext4Proof.no({Some{e} == None{} : Maybe<&2, T.Ext4HtEnt>}, Ext4Proof.ne_clash(Nat.is_eq(T.Ext4HtEnt.hash(e), h), k, Ext4Proof.lt_le_ne(T.Ext4HtEnt.hash(e), x, h, lt, hx)))
    case False{}:
      hn => hl => hx => ih(Ext4Proof.and_r(Bool.or(Bool.not(False{}), Nat.is_eq(T.Ext4HtEnt.hash(e), h)), T.Ext4Htree.named(t, n, h), hn), Ext4Proof.and_r(Nat.is_lt(T.Ext4HtEnt.hash(e), x), T.Ext4Htree.all_lt(t, x), hl), hx)

# entries all below x, and x <= h
def Ext4Proof.find_lt(es: List<&2, T.Ext4HtEnt>, +n: B.Octets, +h: Nat, +x: Nat) -> {T.Ext4Htree.named(es, n, h) == True{} : Bool} -> {T.Ext4Htree.all_lt(es, x) == True{} : Bool} -> {Nat.is_le(x, h) == True{} : Bool} -> {T.Ext4Htree.find_ent(es, n) == None{} : Maybe<&2, T.Ext4HtEnt>}:
  match es:
    case Nil{}:
      hn => hl => hx => {==}
    case Con{+e, +t}:
      Ext4Proof.find_lt.at(B.Octets.is_eq(T.Ext4HtEnt.name(e), n), e, t, n, h, x, Ext4Proof.find_lt(t, n, h, x))

def Ext4Proof.find_ge.at(b: Bool, +e: T.Ext4HtEnt, +t: List<&2, T.Ext4HtEnt>, +n: B.Octets, +h: Nat, +x: Nat, ih: {T.Ext4Htree.named(t, n, h) == True{} : Bool} -> {T.Ext4Htree.all_ge(t, x) == True{} : Bool} -> {Nat.is_lt(h, x) == True{} : Bool} -> {T.Ext4Htree.find_ent(t, n) == None{} : Maybe<&2, T.Ext4HtEnt>}) -> {Bool.and(Bool.or(Bool.not(b), Nat.is_eq(T.Ext4HtEnt.hash(e), h)), T.Ext4Htree.named(t, n, h)) == True{} : Bool} -> {Bool.and(Nat.is_le(x, T.Ext4HtEnt.hash(e)), T.Ext4Htree.all_ge(t, x)) == True{} : Bool} -> {Nat.is_lt(h, x) == True{} : Bool} -> {T.Ext4Htree.find.go(~T.Ext4HtEnt, ~T.Ext4HtEnt.name, Con{e, t}, b, n) == None{} : Maybe<&2, T.Ext4HtEnt>}:
  match b:
    case True{}:
      hn => hl => hx =>
        +k = Ext4Proof.and_l(Nat.is_eq(T.Ext4HtEnt.hash(e), h), T.Ext4Htree.named(t, n, h), hn)
        +ge = Ext4Proof.and_l(Nat.is_le(x, T.Ext4HtEnt.hash(e)), T.Ext4Htree.all_ge(t, x), hl)
        Ext4Proof.no({Some{e} == None{} : Maybe<&2, T.Ext4HtEnt>}, Ext4Proof.ne_clash(Nat.is_eq(T.Ext4HtEnt.hash(e), h), k, Ext4Proof.le_lt_ne(x, T.Ext4HtEnt.hash(e), h, ge, hx)))
    case False{}:
      hn => hl => hx => ih(Ext4Proof.and_r(Bool.or(Bool.not(False{}), Nat.is_eq(T.Ext4HtEnt.hash(e), h)), T.Ext4Htree.named(t, n, h), hn), Ext4Proof.and_r(Nat.is_le(x, T.Ext4HtEnt.hash(e)), T.Ext4Htree.all_ge(t, x), hl), hx)

# entries all at least x, and h < x
def Ext4Proof.find_ge(es: List<&2, T.Ext4HtEnt>, +n: B.Octets, +h: Nat, +x: Nat) -> {T.Ext4Htree.named(es, n, h) == True{} : Bool} -> {T.Ext4Htree.all_ge(es, x) == True{} : Bool} -> {Nat.is_lt(h, x) == True{} : Bool} -> {T.Ext4Htree.find_ent(es, n) == None{} : Maybe<&2, T.Ext4HtEnt>}:
  match es:
    case Nil{}:
      hn => hl => hx => {==}
    case Con{+e, +t}:
      Ext4Proof.find_ge.at(B.Octets.is_eq(T.Ext4HtEnt.name(e), n), e, t, n, h, x, Ext4Proof.find_ge(t, n, h, x))

# Leaves whose entries are all above h hold no entry named n: neither the
# scan nor the lookup's continuation finds one there

def Ext4Proof.above_scan(u: List<&2, T.Ext4HtLeaf>, +m: T.Ext4HtLeaf, +n: B.Octets, +h: Nat) -> {T.Ext4Htree.all_ge(T.Ext4HtLeaf.ents(m), T.Ext4HtLeaf.lo(m)) == True{} : Bool} -> {Nat.is_lt(h, T.Ext4HtLeaf.lo(m)) == True{} : Bool} -> {T.Ext4Htree.ordered(Con{m, u}) == True{} : Bool} -> {T.Ext4Htree.consistent(Con{m, u}, n, h) == True{} : Bool} -> {T.Ext4Htree.scan.go(Con{m, u}, n, None{}) == None{} : Maybe<&2, T.Ext4HtEnt>}:
  match u:
    case Nil{}:
      +g => +lt => +o => +c =>
        +f = Ext4Proof.find_ge(T.Ext4HtLeaf.ents(m), n, h, T.Ext4HtLeaf.lo(m), Ext4Proof.and_l(T.Ext4Htree.named(T.Ext4HtLeaf.ents(m), n, h), T.Ext4Htree.consistent(Nil{}, n, h), c), g, lt)
        %Equal.sym(Maybe<&2, T.Ext4HtEnt>, T.Ext4Htree.find_ent(T.Ext4HtLeaf.ents(m), n), None{}, f) : {T.Ext4Htree.scan.go(Nil{}, n, _) == None{} : Maybe<&2, T.Ext4HtEnt>}
        {==}
    case Con{+m2, +u2}:
      +g => +lt => +o => +c =>
        +f = Ext4Proof.find_ge(T.Ext4HtLeaf.ents(m), n, h, T.Ext4HtLeaf.lo(m), Ext4Proof.and_l(T.Ext4Htree.named(T.Ext4HtLeaf.ents(m), n, h), T.Ext4Htree.consistent(Con{m2, u2}, n, h), c), g, lt)
        +pr = Ext4Proof.and_l(T.Ext4Htree.ordered.pair(m, m2), T.Ext4Htree.ordered(Con{m2, u2}), o)
        +le = Ext4Proof.and_l(Nat.is_le(T.Ext4HtLeaf.lo(m), T.Ext4HtLeaf.lo(m2)), Bool.and(T.Ext4Htree.all_lt(T.Ext4HtLeaf.ents(m), T.Ext4HtLeaf.lo(m2)), T.Ext4Htree.all_ge(T.Ext4HtLeaf.ents(m2), T.Ext4HtLeaf.lo(m2))), pr)
        +g2 = Ext4Proof.and_r(T.Ext4Htree.all_lt(T.Ext4HtLeaf.ents(m), T.Ext4HtLeaf.lo(m2)), T.Ext4Htree.all_ge(T.Ext4HtLeaf.ents(m2), T.Ext4HtLeaf.lo(m2)), Ext4Proof.and_r(Nat.is_le(T.Ext4HtLeaf.lo(m), T.Ext4HtLeaf.lo(m2)), Bool.and(T.Ext4Htree.all_lt(T.Ext4HtLeaf.ents(m), T.Ext4HtLeaf.lo(m2)), T.Ext4Htree.all_ge(T.Ext4HtLeaf.ents(m2), T.Ext4HtLeaf.lo(m2))), pr))
        %Equal.sym(Maybe<&2, T.Ext4HtEnt>, T.Ext4Htree.find_ent(T.Ext4HtLeaf.ents(m), n), None{}, f) : {T.Ext4Htree.scan.go(Con{m2, u2}, n, _) == None{} : Maybe<&2, T.Ext4HtEnt>}
        Ext4Proof.above_scan(u2, m2, n, h, g2, Ext4Proof.lt_le_lt(h, T.Ext4HtLeaf.lo(m), T.Ext4HtLeaf.lo(m2), lt, le), Ext4Proof.and_r(T.Ext4Htree.ordered.pair(m, m2), T.Ext4Htree.ordered(Con{m2, u2}), o), Ext4Proof.and_r(T.Ext4Htree.named(T.Ext4HtLeaf.ents(m), n, h), T.Ext4Htree.consistent(Con{m2, u2}, n, h), c))

def Ext4Proof.above_from(u: List<&2, T.Ext4HtLeaf>, +m: T.Ext4HtLeaf, c: Bool, +n: B.Octets, +h: Nat) -> {T.Ext4Htree.all_ge(T.Ext4HtLeaf.ents(m), T.Ext4HtLeaf.lo(m)) == True{} : Bool} -> {Nat.is_lt(h, T.Ext4HtLeaf.lo(m)) == True{} : Bool} -> {T.Ext4Htree.ordered(Con{m, u}) == True{} : Bool} -> {T.Ext4Htree.consistent(Con{m, u}, n, h) == True{} : Bool} -> {T.Ext4Htree.from(Con{m, u}, None{}, c, h, n) == None{} : Maybe<&2, T.Ext4HtEnt>}:
  match u c:
    case _ False{}:
      +g => +lt => +o => +k => {==}
    case Nil{} True{}:
      +g => +lt => +o => +k =>
        +f = Ext4Proof.find_ge(T.Ext4HtLeaf.ents(m), n, h, T.Ext4HtLeaf.lo(m), Ext4Proof.and_l(T.Ext4Htree.named(T.Ext4HtLeaf.ents(m), n, h), T.Ext4Htree.consistent(Nil{}, n, h), k), g, lt)
        %Equal.sym(Maybe<&2, T.Ext4HtEnt>, T.Ext4Htree.find_ent(T.Ext4HtLeaf.ents(m), n), None{}, f) : {T.Ext4Htree.from(Nil{}, _, False{}, h, n) == None{} : Maybe<&2, T.Ext4HtEnt>}
        {==}
    case Con{+m2, +u2} True{}:
      +g => +lt => +o => +k =>
        +f = Ext4Proof.find_ge(T.Ext4HtLeaf.ents(m), n, h, T.Ext4HtLeaf.lo(m), Ext4Proof.and_l(T.Ext4Htree.named(T.Ext4HtLeaf.ents(m), n, h), T.Ext4Htree.consistent(Con{m2, u2}, n, h), k), g, lt)
        +pr = Ext4Proof.and_l(T.Ext4Htree.ordered.pair(m, m2), T.Ext4Htree.ordered(Con{m2, u2}), o)
        +le = Ext4Proof.and_l(Nat.is_le(T.Ext4HtLeaf.lo(m), T.Ext4HtLeaf.lo(m2)), Bool.and(T.Ext4Htree.all_lt(T.Ext4HtLeaf.ents(m), T.Ext4HtLeaf.lo(m2)), T.Ext4Htree.all_ge(T.Ext4HtLeaf.ents(m2), T.Ext4HtLeaf.lo(m2))), pr)
        +g2 = Ext4Proof.and_r(T.Ext4Htree.all_lt(T.Ext4HtLeaf.ents(m), T.Ext4HtLeaf.lo(m2)), T.Ext4Htree.all_ge(T.Ext4HtLeaf.ents(m2), T.Ext4HtLeaf.lo(m2)), Ext4Proof.and_r(Nat.is_le(T.Ext4HtLeaf.lo(m), T.Ext4HtLeaf.lo(m2)), Bool.and(T.Ext4Htree.all_lt(T.Ext4HtLeaf.ents(m), T.Ext4HtLeaf.lo(m2)), T.Ext4Htree.all_ge(T.Ext4HtLeaf.ents(m2), T.Ext4HtLeaf.lo(m2))), pr))
        %Equal.sym(Maybe<&2, T.Ext4HtEnt>, T.Ext4Htree.find_ent(T.Ext4HtLeaf.ents(m), n), None{}, f) : {T.Ext4Htree.from(Con{m2, u2}, _, T.Ext4Htree.cont(~T.Ext4HtLeaf, ~T.Ext4HtLeaf.lo, Con{m2, u2}, h), h, n) == None{} : Maybe<&2, T.Ext4HtEnt>}
        Ext4Proof.above_from(u2, m2, T.Ext4Htree.cont(~T.Ext4HtLeaf, ~T.Ext4HtLeaf.lo, Con{m2, u2}, h), n, h, g2, Ext4Proof.lt_le_lt(h, T.Ext4HtLeaf.lo(m), T.Ext4HtLeaf.lo(m2), lt, le), Ext4Proof.and_r(T.Ext4Htree.ordered.pair(m, m2), T.Ext4Htree.ordered(Con{m2, u2}), o), Ext4Proof.and_r(T.Ext4Htree.named(T.Ext4HtLeaf.ents(m), n, h), T.Ext4Htree.consistent(Con{m2, u2}, n, h), k))

# after the picked leaf l, the next leaf m starts above h: the lookup and
# the scan agree whatever the search of l found
def Ext4Proof.after_pick(f: Maybe<&2, T.Ext4HtEnt>, +m: T.Ext4HtLeaf, +u: List<&2, T.Ext4HtLeaf>, +c: Bool, +n: B.Octets, +h: Nat) -> {T.Ext4Htree.all_ge(T.Ext4HtLeaf.ents(m), T.Ext4HtLeaf.lo(m)) == True{} : Bool} -> {Nat.is_lt(h, T.Ext4HtLeaf.lo(m)) == True{} : Bool} -> {T.Ext4Htree.ordered(Con{m, u}) == True{} : Bool} -> {T.Ext4Htree.consistent(Con{m, u}, n, h) == True{} : Bool} -> {T.Ext4Htree.from(Con{m, u}, f, c, h, n) == T.Ext4Htree.scan.go(Con{m, u}, n, f) : Maybe<&2, T.Ext4HtEnt>}:
  match f:
    case Some{e}:
      +g => +lt => +o => +k => {==}
    case None{}:
      +g => +lt => +o => +k => Equal.trans(Maybe<&2, T.Ext4HtEnt>, T.Ext4Htree.from(Con{m, u}, None{}, c, h, n), None{}, T.Ext4Htree.scan.go(Con{m, u}, n, None{}), Ext4Proof.above_from(u, m, c, n, h, g, lt, o, k), Equal.sym(Maybe<&2, T.Ext4HtEnt>, T.Ext4Htree.scan.go(Con{m, u}, n, None{}), None{}, Ext4Proof.above_scan(u, m, n, h, g, lt, o, k)))

# the last leaf: the lookup searches it, as the scan does
def Ext4Proof.last_leaf(f: Maybe<&2, T.Ext4HtEnt>, +n: B.Octets, +h: Nat) -> {T.Ext4Htree.from(Nil{}, f, False{}, h, n) == T.Ext4Htree.scan.go(Nil{}, n, f) : Maybe<&2, T.Ext4HtEnt>}:
  match f:
    case Some{e}:
      {==}
    case None{}:
      {==}

# one step of the pick: past leaf l when the next leaf m starts at most at
# h (then l holds no entry of hash h), or stop at l
def Ext4Proof.pick_step(b: Bool, +u: List<&2, T.Ext4HtLeaf>, +l: T.Ext4HtLeaf, +m: T.Ext4HtLeaf, +n: B.Octets, +h: Nat, ih: {T.Ext4Htree.ordered(Con{m, u}) == True{} : Bool} -> {T.Ext4Htree.consistent(Con{m, u}, n, h) == True{} : Bool} -> {T.Ext4Htree.lookup.at(T.Ext4Htree.pick.go(~T.Ext4HtLeaf, ~T.Ext4HtLeaf.lo, u, m, T.Ext4Htree.adv(~T.Ext4HtLeaf, ~T.Ext4HtLeaf.lo, u, h), h), h, n) == T.Ext4Htree.scan.go(u, n, T.Ext4Htree.find_ent(T.Ext4HtLeaf.ents(m), n)) : Maybe<&2, T.Ext4HtEnt>}) -> {Nat.is_le(T.Ext4HtLeaf.lo(m), h) == b : Bool} -> {T.Ext4Htree.ordered(Con{l, Con{m, u}}) == True{} : Bool} -> {T.Ext4Htree.consistent(Con{l, Con{m, u}}, n, h) == True{} : Bool} -> {T.Ext4Htree.lookup.at(T.Ext4Htree.pick.go(~T.Ext4HtLeaf, ~T.Ext4HtLeaf.lo, Con{m, u}, l, b, h), h, n) == T.Ext4Htree.scan.go(Con{m, u}, n, T.Ext4Htree.find_ent(T.Ext4HtLeaf.ents(l), n)) : Maybe<&2, T.Ext4HtEnt>}:
  match b:
    case True{}:
      +pair = T.Ext4Htree.ordered.pair(l, m)
      +rest = T.Ext4Htree.ordered(Con{m, u})
      +lom = T.Ext4HtLeaf.lo(m)
      +lt2 = T.Ext4Htree.all_lt(T.Ext4HtLeaf.ents(l), lom)
      +ge2 = T.Ext4Htree.all_ge(T.Ext4HtLeaf.ents(m), lom)
      +nl = T.Ext4Htree.named(T.Ext4HtLeaf.ents(l), n, h)
      +cr = T.Ext4Htree.consistent(Con{m, u}, n, h)
      +eq => +o => +k =>
        +pr = Ext4Proof.and_l(pair, rest, o)
        +lr = Ext4Proof.and_r(Nat.is_le(T.Ext4HtLeaf.lo(l), lom), Bool.and(lt2, ge2), pr)
        +fl = Ext4Proof.find_lt(T.Ext4HtLeaf.ents(l), n, h, lom, Ext4Proof.and_l(nl, cr, k), Ext4Proof.and_l(lt2, ge2, lr), eq)
        %Equal.sym(Maybe<&2, T.Ext4HtEnt>, T.Ext4Htree.find_ent(T.Ext4HtLeaf.ents(l), n), None{}, fl) : {T.Ext4Htree.lookup.at(T.Ext4Htree.pick.go(~T.Ext4HtLeaf, ~T.Ext4HtLeaf.lo, Con{m, u}, l, True{}, h), h, n) == T.Ext4Htree.scan.go(Con{m, u}, n, _) : Maybe<&2, T.Ext4HtEnt>}
        ih(Ext4Proof.and_r(pair, rest, o), Ext4Proof.and_r(nl, cr, k))
    case False{}:
      +pair = T.Ext4Htree.ordered.pair(l, m)
      +rest = T.Ext4Htree.ordered(Con{m, u})
      +lom = T.Ext4HtLeaf.lo(m)
      +lt2 = T.Ext4Htree.all_lt(T.Ext4HtLeaf.ents(l), lom)
      +ge2 = T.Ext4Htree.all_ge(T.Ext4HtLeaf.ents(m), lom)
      +nl = T.Ext4Htree.named(T.Ext4HtLeaf.ents(l), n, h)
      +cr = T.Ext4Htree.consistent(Con{m, u}, n, h)
      +eq => +o => +k =>
        +pr = Ext4Proof.and_l(pair, rest, o)
        +lr = Ext4Proof.and_r(Nat.is_le(T.Ext4HtLeaf.lo(l), lom), Bool.and(lt2, ge2), pr)
        Ext4Proof.after_pick(T.Ext4Htree.find_ent(T.Ext4HtLeaf.ents(l), n), m, u, T.Ext4Htree.cont(~T.Ext4HtLeaf, ~T.Ext4HtLeaf.lo, Con{m, u}, h), n, h, Ext4Proof.and_r(lt2, ge2, lr), Ext4Proof.not_le_lt(lom, h, eq), Ext4Proof.and_r(pair, rest, o), Ext4Proof.and_r(nl, cr, k))

# the lookup from leaf l on, the leaves t after it, finds what the scan of
# l and t finds
def Ext4Proof.lookup_from(t: List<&2, T.Ext4HtLeaf>, +l: T.Ext4HtLeaf, +n: B.Octets, +h: Nat) -> {T.Ext4Htree.ordered(Con{l, t}) == True{} : Bool} -> {T.Ext4Htree.consistent(Con{l, t}, n, h) == True{} : Bool} -> {T.Ext4Htree.lookup.at(T.Ext4Htree.pick.go(~T.Ext4HtLeaf, ~T.Ext4HtLeaf.lo, t, l, T.Ext4Htree.adv(~T.Ext4HtLeaf, ~T.Ext4HtLeaf.lo, t, h), h), h, n) == T.Ext4Htree.scan.go(t, n, T.Ext4Htree.find_ent(T.Ext4HtLeaf.ents(l), n)) : Maybe<&2, T.Ext4HtEnt>}:
  match t:
    case Nil{}:
      +o => +k => Ext4Proof.last_leaf(T.Ext4Htree.find_ent(T.Ext4HtLeaf.ents(l), n), n, h)
    case Con{+m, +u}:
      Ext4Proof.pick_step(Nat.is_le(T.Ext4HtLeaf.lo(m), h), u, l, m, n, h, Ext4Proof.lookup_from(u, m, n, h), {==})

def Ext4Proof.lookup_scan(ls: List<&2, T.Ext4HtLeaf>, +n: B.Octets, +h: Nat) -> {T.Ext4Htree.ordered(ls) == True{} : Bool} -> {T.Ext4Htree.consistent(ls, n, h) == True{} : Bool} -> {T.Ext4Htree.lookup(ls, h, n) == T.Ext4Htree.scan(ls, n) : Maybe<&2, T.Ext4HtEnt>}:
  match ls:
    case Nil{}:
      +o => +k => {==}
    case Con{+l, +t}:
      Ext4Proof.lookup_from(t, l, n, h)

def Laws.htree_lookup_scan(ls, n, h, ord, con):
  Ext4Proof.lookup_scan(ls, n, h, ord, con)

# The writer's plan is ordered

# more comparisons

def Ext4Proof.lt_zero(+a: Nat) -> {Nat.is_lt(a, 0n) == True{} : Bool} -> {False{} == True{} : Bool}:
  match a:
    case 0n:
      +p => p
    case 1n+q:
      +p => p

def Ext4Proof.le_zero(+x: Nat) -> {Nat.is_le(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Ext4Proof.le_refl(+x: Nat) -> {Nat.is_le(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Ext4Proof.le_refl(p)

def Ext4Proof.lt_le(+a: Nat, +b: Nat) -> {Nat.is_lt(a, b) == True{} : Bool} -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      +p => Ext4Proof.no({Nat.is_le(a, 0n) == True{} : Bool}, Ext4Proof.lt_zero(a, p))
    case 0n 1n+bp:
      +p => {==}
    case 1n+ap 1n+bp:
      +p => Ext4Proof.lt_le(ap, bp, p)

def Ext4Proof.le_trans(+a: Nat, +b: Nat, +c: Nat) -> {Nat.is_le(a, b) == True{} : Bool} -> {Nat.is_le(b, c) == True{} : Bool} -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      +p => +q => Ext4Proof.le_zero(c)
    case 1n+ap 0n _:
      +p => +q => Ext4Proof.no({Nat.is_le(1n+ap, c) == True{} : Bool}, p)
    case 1n+ap 1n+bp 0n:
      +p => +q => Ext4Proof.no({Nat.is_le(1n+ap, 0n) == True{} : Bool}, q)
    case 1n+ap 1n+bp 1n+cp:
      +p => +q => Ext4Proof.le_trans(ap, bp, cp, p, q)

# a <= b < c: a < c
def Ext4Proof.le_lt_lt(+a: Nat, +b: Nat, +c: Nat) -> {Nat.is_le(a, b) == True{} : Bool} -> {Nat.is_lt(b, c) == True{} : Bool} -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ _ 0n:
      +p => +q => Ext4Proof.no({Nat.is_lt(a, 0n) == True{} : Bool}, Ext4Proof.lt_zero(b, q))
    case 0n _ 1n+cp:
      +p => +q => {==}
    case 1n+ap 0n 1n+cp:
      +p => +q => Ext4Proof.no({Nat.is_lt(1n+ap, 1n+cp) == True{} : Bool}, p)
    case 1n+ap 1n+bp 1n+cp:
      +p => +q => Ext4Proof.le_lt_lt(ap, bp, cp, p, q)

# not (a < b): b <= a
def Ext4Proof.not_lt_le(+a: Nat, +b: Nat) -> {Nat.is_lt(a, b) == False{} : Bool} -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case _ 0n:
      +p => Ext4Proof.le_zero(a)
    case 0n 1n+bp:
      +p => Ext4Proof.no({Nat.is_le(1n+bp, 0n) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, p))
    case 1n+ap 1n+bp:
      +p => Ext4Proof.not_lt_le(ap, bp, p)

def Ext4Proof.and_i(+a: Bool, +b: Bool) -> {a == True{} : Bool} -> {b == True{} : Bool} -> {Bool.and(a, b) == True{} : Bool}:
  match a b:
    case True{} True{}:
      +p => +q => {==}
    case False{} _:
      +p => +q => Ext4Proof.no({Bool.and(False{}, b) == True{} : Bool}, p)
    case True{} False{}:
      +p => +q => Ext4Proof.no({Bool.and(True{}, False{}) == True{} : Bool}, q)

# Bounds on a leaf's entries

def Ext4Proof.all_le(es: List<&2, T.Ext4HtEnt>, +x: Nat) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      Bool.and(Nat.is_le(T.Ext4HtEnt.hash(e), x), Ext4Proof.all_le(t, x))

def Ext4Proof.all_le_up(es: List<&2, T.Ext4HtEnt>, +a: Nat, +b: Nat) -> {Ext4Proof.all_le(es, a) == True{} : Bool} -> {Nat.is_le(a, b) == True{} : Bool} -> {Ext4Proof.all_le(es, b) == True{} : Bool}:
  match es:
    case Nil{}:
      +p => +q => {==}
    case Con{+e, +t}:
      +p => +q =>
        +he = T.Ext4HtEnt.hash(e)
        Ext4Proof.and_i(Nat.is_le(he, b), Ext4Proof.all_le(t, b), Ext4Proof.le_trans(he, a, b, Ext4Proof.and_l(Nat.is_le(he, a), Ext4Proof.all_le(t, a), p), q), Ext4Proof.all_le_up(t, a, b, Ext4Proof.and_r(Nat.is_le(he, a), Ext4Proof.all_le(t, a), p), q))

def Ext4Proof.all_le_lt(es: List<&2, T.Ext4HtEnt>, +a: Nat, +b: Nat) -> {Ext4Proof.all_le(es, a) == True{} : Bool} -> {Nat.is_lt(a, b) == True{} : Bool} -> {T.Ext4Htree.all_lt(es, b) == True{} : Bool}:
  match es:
    case Nil{}:
      +p => +q => {==}
    case Con{+e, +t}:
      +p => +q =>
        +he = T.Ext4HtEnt.hash(e)
        Ext4Proof.and_i(Nat.is_lt(he, b), T.Ext4Htree.all_lt(t, b), Ext4Proof.le_lt_lt(he, a, b, Ext4Proof.and_l(Nat.is_le(he, a), Ext4Proof.all_le(t, a), p), q), Ext4Proof.all_le_lt(t, a, b, Ext4Proof.and_r(Nat.is_le(he, a), Ext4Proof.all_le(t, a), p), q))

def Ext4Proof.all_ge_down(es: List<&2, T.Ext4HtEnt>, +a: Nat, +b: Nat) -> {T.Ext4Htree.all_ge(es, b) == True{} : Bool} -> {Nat.is_le(a, b) == True{} : Bool} -> {T.Ext4Htree.all_ge(es, a) == True{} : Bool}:
  match es:
    case Nil{}:
      +p => +q => {==}
    case Con{+e, +t}:
      +p => +q =>
        +he = T.Ext4HtEnt.hash(e)
        Ext4Proof.and_i(Nat.is_le(a, he), T.Ext4Htree.all_ge(t, a), Ext4Proof.le_trans(a, b, he, q, Ext4Proof.and_l(Nat.is_le(b, he), T.Ext4Htree.all_ge(t, b), p)), Ext4Proof.all_ge_down(t, a, b, Ext4Proof.and_r(Nat.is_le(b, he), T.Ext4Htree.all_ge(t, b), p), q))

def Ext4Proof.all_ge_rev(xs: List<&2, T.Ext4HtEnt>, +acc: List<&2, T.Ext4HtEnt>, +x: Nat) -> {T.Ext4Htree.all_ge(xs, x) == True{} : Bool} -> {T.Ext4Htree.all_ge(acc, x) == True{} : Bool} -> {T.Ext4Htree.all_ge(List.reverse.go(&2, T.Ext4HtEnt, xs, acc), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      +p => +q => q
    case Con{+e, +t}:
      +p => +q => Ext4Proof.all_ge_rev(t, Con{e, acc}, x, Ext4Proof.and_r(Nat.is_le(x, T.Ext4HtEnt.hash(e)), T.Ext4Htree.all_ge(t, x), p), Ext4Proof.and_i(Nat.is_le(x, T.Ext4HtEnt.hash(e)), T.Ext4Htree.all_ge(acc, x), Ext4Proof.and_l(Nat.is_le(x, T.Ext4HtEnt.hash(e)), T.Ext4Htree.all_ge(t, x), p), q))

def Ext4Proof.all_lt_rev(xs: List<&2, T.Ext4HtEnt>, +acc: List<&2, T.Ext4HtEnt>, +x: Nat) -> {T.Ext4Htree.all_lt(xs, x) == True{} : Bool} -> {T.Ext4Htree.all_lt(acc, x) == True{} : Bool} -> {T.Ext4Htree.all_lt(List.reverse.go(&2, T.Ext4HtEnt, xs, acc), x) == True{} : Bool}:
  match xs:
    case Nil{}:
      +p => +q => q
    case Con{+e, +t}:
      +p => +q => Ext4Proof.all_lt_rev(t, Con{e, acc}, x, Ext4Proof.and_r(Nat.is_lt(T.Ext4HtEnt.hash(e), x), T.Ext4Htree.all_lt(t, x), p), Ext4Proof.and_i(Nat.is_lt(T.Ext4HtEnt.hash(e), x), T.Ext4Htree.all_lt(acc, x), Ext4Proof.and_l(Nat.is_lt(T.Ext4HtEnt.hash(e), x), T.Ext4Htree.all_lt(t, x), p), q))

# Sorting: the insertion sort's output is sorted by hash

def Ext4Proof.sorted_from(xs: List<&2, T.Ext4HtEnt>, +p: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(Nat.is_le(p, T.Ext4HtEnt.hash(x)), Ext4Proof.sorted_from(t, T.Ext4HtEnt.hash(x)))

# the insertion insert.go computes, without its accumulator
def Ext4Proof.ins(xs: List<&2, T.Ext4HtEnt>, lt: Bool, +e: T.Ext4HtEnt, +h: Nat) -> List<&2, T.Ext4HtEnt>:
  match xs lt:
    case Nil{} _:
      Con{e, Nil{}}
    case Con{x, t} True{}:
      Con{e, Con{x, t}}
    case Con{x, +t} False{}:
      Con{x, Ext4Proof.ins(t, HW.Ext4Htree.lt_head(t, h), e, h)}

def Ext4Proof.insert_eq(xs: List<&2, T.Ext4HtEnt>, lt: Bool, +e: T.Ext4HtEnt, +h: Nat, +acc: List<&2, T.Ext4HtEnt>) -> {HW.Ext4Htree.insert.go(xs, lt, e, h, acc) == List.reverse.go(&2, T.Ext4HtEnt, acc, Ext4Proof.ins(xs, lt, e, h)) : List<&2, T.Ext4HtEnt>}:
  match xs lt:
    case Nil{} _:
      {==}
    case Con{x, t} True{}:
      {==}
    case Con{+x, +t} False{}:
      Ext4Proof.insert_eq(t, HW.Ext4Htree.lt_head(t, h), e, h, Con{x, acc})

def Ext4Proof.ins_sorted(xs: List<&2, T.Ext4HtEnt>, lt: Bool, +e: T.Ext4HtEnt, +p: Nat) -> {lt == HW.Ext4Htree.lt_head(xs, T.Ext4HtEnt.hash(e)) : Bool} -> {Ext4Proof.sorted_from(xs, p) == True{} : Bool} -> {Nat.is_le(p, T.Ext4HtEnt.hash(e)) == True{} : Bool} -> {Ext4Proof.sorted_from(Ext4Proof.ins(xs, lt, e, T.Ext4HtEnt.hash(e)), p) == True{} : Bool}:
  match xs lt:
    case Nil{} _:
      +l => +s => +q => Ext4Proof.and_i(Nat.is_le(p, T.Ext4HtEnt.hash(e)), True{}, q, {==})
    case Con{+x, +t} True{}:
      +l => +s => +q =>
        +he = T.Ext4HtEnt.hash(e)
        +hx = T.Ext4HtEnt.hash(x)
        Ext4Proof.and_i(Nat.is_le(p, he), Bool.and(Nat.is_le(he, hx), Ext4Proof.sorted_from(t, hx)), q, Ext4Proof.and_i(Nat.is_le(he, hx), Ext4Proof.sorted_from(t, hx), Ext4Proof.lt_le(he, hx, Equal.sym(Bool, True{}, Nat.is_lt(he, hx), l)), Ext4Proof.and_r(Nat.is_le(p, hx), Ext4Proof.sorted_from(t, hx), s)))
    case Con{+x, +t} False{}:
      +l => +s => +q =>
        +he = T.Ext4HtEnt.hash(e)
        +hx = T.Ext4HtEnt.hash(x)
        Ext4Proof.and_i(Nat.is_le(p, hx), Ext4Proof.sorted_from(Ext4Proof.ins(t, HW.Ext4Htree.lt_head(t, he), e, he), hx), Ext4Proof.and_l(Nat.is_le(p, hx), Ext4Proof.sorted_from(t, hx), s), Ext4Proof.ins_sorted(t, HW.Ext4Htree.lt_head(t, he), e, hx, {==}, Ext4Proof.and_r(Nat.is_le(p, hx), Ext4Proof.sorted_from(t, hx), s), Ext4Proof.not_lt_le(he, hx, Equal.sym(Bool, False{}, Nat.is_lt(he, hx), l))))

def Ext4Proof.insert_sorted(+e: T.Ext4HtEnt, +xs: List<&2, T.Ext4HtEnt>, +p: Nat) -> {Ext4Proof.sorted_from(xs, p) == True{} : Bool} -> {Nat.is_le(p, T.Ext4HtEnt.hash(e)) == True{} : Bool} -> {Ext4Proof.sorted_from(HW.Ext4Htree.insert(e, xs), p) == True{} : Bool}:
  +s => +q =>
    +he = T.Ext4HtEnt.hash(e)
    %Equal.sym(List<&2, T.Ext4HtEnt>, HW.Ext4Htree.insert.go(xs, HW.Ext4Htree.lt_head(xs, he), e, he, Nil{}), List.reverse.go(&2, T.Ext4HtEnt, Nil{}, Ext4Proof.ins(xs, HW.Ext4Htree.lt_head(xs, he), e, he)), Ext4Proof.insert_eq(xs, HW.Ext4Htree.lt_head(xs, he), e, he, Nil{})) : {Ext4Proof.sorted_from(_, p) == True{} : Bool}
    Ext4Proof.ins_sorted(xs, HW.Ext4Htree.lt_head(xs, he), e, p, {==}, s, q)

def Ext4Proof.sort_sorted(xs: List<&2, T.Ext4HtEnt>, +acc: List<&2, T.Ext4HtEnt>) -> {Ext4Proof.sorted_from(acc, 0n) == True{} : Bool} -> {Ext4Proof.sorted_from(HW.Ext4Htree.sort.go(xs, acc), 0n) == True{} : Bool}:
  match xs:
    case Nil{}:
      +s => s
    case Con{+x, +t}:
      +s => Ext4Proof.sort_sorted(t, HW.Ext4Htree.insert(x, acc), Ext4Proof.insert_sorted(x, acc, 0n, s, Ext4Proof.le_zero(T.Ext4HtEnt.hash(x))))

# Filling leaves: the leaves come out in order

# chunk's accumulator holds the closed leaves, last first, in front of what
# the rest produces
def Ext4Proof.chunk_acc(xs: List<&2, T.Ext4HtEnt>, sp: Bool, +cap: Nat, +cur: List<&2, T.Ext4HtEnt>, +used: Nat, +lo: Nat, +prev: Nat, +acc: List<&2, T.Ext4HtLeaf>) -> {HW.Ext4Htree.chunk(xs, sp, cap, cur, used, lo, prev, acc) == List.reverse.go(&2, T.Ext4HtLeaf, acc, HW.Ext4Htree.chunk(xs, sp, cap, cur, used, lo, prev, Nil{})) : List<&2, T.Ext4HtLeaf>}:
  match xs sp:
    case Nil{} _:
      {==}
    case Con{+e, +t} True{}:
      +h = T.Ext4HtEnt.hash(e)
      +sz = HW.Ext4Htree.size(e)
      +sp2 = HW.Ext4Htree.split(t, cap, sz, h)
      +l = {T.Ext4HtLeaf{lo, List.reverse(&2, T.Ext4HtEnt, cur)} : T.Ext4HtLeaf}
      +k = HW.Ext4Htree.chunk(t, sp2, cap, Con{e, Nil{}}, sz, h, h, Nil{})
      +i1 = Ext4Proof.chunk_acc(t, sp2, cap, Con{e, Nil{}}, sz, h, h, Con{l, acc})
      +i2 = Ext4Proof.chunk_acc(t, sp2, cap, Con{e, Nil{}}, sz, h, h, Con{l, Nil{}})
      %Equal.sym(List<&2, T.Ext4HtLeaf>, HW.Ext4Htree.chunk(t, sp2, cap, Con{e, Nil{}}, sz, h, h, Con{l, Nil{}}), List.reverse.go(&2, T.Ext4HtLeaf, Con{l, Nil{}}, k), i2) : {HW.Ext4Htree.chunk(t, sp2, cap, Con{e, Nil{}}, sz, h, h, Con{l, acc}) == List.reverse.go(&2, T.Ext4HtLeaf, acc, _) : List<&2, T.Ext4HtLeaf>}
      i1
    case Con{+e, +t} False{}:
      +h = T.Ext4HtEnt.hash(e)
      +u = Nat.add(used, HW.Ext4Htree.size(e))
      Ext4Proof.chunk_acc(t, HW.Ext4Htree.split(t, cap, u, h), cap, Con{e, cur}, u, lo, h, acc)

def Ext4Proof.leaf_pair(+lo0: Nat, +es0: List<&2, T.Ext4HtEnt>, +lo: Nat, +cur: List<&2, T.Ext4HtEnt>) -> {Nat.is_le(lo0, lo) == True{} : Bool} -> {T.Ext4Htree.all_lt(es0, lo) == True{} : Bool} -> {T.Ext4Htree.all_ge(cur, lo) == True{} : Bool} -> {T.Ext4Htree.ordered.pair(T.Ext4HtLeaf{lo0, es0}, T.Ext4HtLeaf{lo, List.reverse(&2, T.Ext4HtEnt, cur)}) == True{} : Bool}:
  +a => +b => +c =>
    +rv = List.reverse(&2, T.Ext4HtEnt, cur)
    Ext4Proof.and_i(Nat.is_le(lo0, lo), Bool.and(T.Ext4Htree.all_lt(es0, lo), T.Ext4Htree.all_ge(rv, lo)), a, Ext4Proof.and_i(T.Ext4Htree.all_lt(es0, lo), T.Ext4Htree.all_ge(rv, lo), b, Ext4Proof.all_ge_rev(cur, Nil{}, lo, c, {==})))

# from any point of the fill: the leaves it produces are in order, and may
# follow any leaf (lo0, es0) that starts at most at the open leaf's lo and
# whose entries are all below it. The entries left are sorted from prev on;
# the open leaf's entries (cur) lie between lo and prev.
def Ext4Proof.chunk_ord(xs: List<&2, T.Ext4HtEnt>, sp: Bool, +cap: Nat, +cur: List<&2, T.Ext4HtEnt>, +used: Nat, +lo: Nat, +prev: Nat, +lo0: Nat, +es0: List<&2, T.Ext4HtEnt>) -> {sp == HW.Ext4Htree.split(xs, cap, used, prev) : Bool} -> {Ext4Proof.sorted_from(xs, prev) == True{} : Bool} -> {Nat.is_le(lo, prev) == True{} : Bool} -> {Ext4Proof.all_le(cur, prev) == True{} : Bool} -> {T.Ext4Htree.all_ge(cur, lo) == True{} : Bool} -> {Nat.is_le(lo0, lo) == True{} : Bool} -> {T.Ext4Htree.all_lt(es0, lo) == True{} : Bool} -> {T.Ext4Htree.ordered(Con{T.Ext4HtLeaf{lo0, es0}, HW.Ext4Htree.chunk(xs, sp, cap, cur, used, lo, prev, Nil{})}) == True{} : Bool}:
  match xs sp:
    case Nil{} _:
      +q => +s => +hl => +hc => +hg => +h0 => +h1 =>
        Ext4Proof.and_i(T.Ext4Htree.ordered.pair(T.Ext4HtLeaf{lo0, es0}, T.Ext4HtLeaf{lo, List.reverse(&2, T.Ext4HtEnt, cur)}), True{}, Ext4Proof.leaf_pair(lo0, es0, lo, cur, h0, h1, hg), {==})
    case Con{+e, +t} True{}:
      +q => +s => +hl => +hc => +hg => +h0 => +h1 =>
        +h = T.Ext4HtEnt.hash(e)
        +sz = HW.Ext4Htree.size(e)
        +sp2 = HW.Ext4Htree.split(t, cap, sz, h)
        +l = {T.Ext4HtLeaf{lo, List.reverse(&2, T.Ext4HtEnt, cur)} : T.Ext4HtLeaf}
        +k = HW.Ext4Htree.chunk(t, sp2, cap, Con{e, Nil{}}, sz, h, h, Nil{})
        +a1 = Nat.is_lt(0n, used)
        +a2 = Nat.is_lt(cap, Nat.add(used, sz))
        +a3 = Nat.is_lt(prev, h)
        +plt = Ext4Proof.and_r(a2, a3, Ext4Proof.and_r(a1, Bool.and(a2, a3), Equal.sym(Bool, True{}, Bool.and(a1, Bool.and(a2, a3)), q)))
        +st = Ext4Proof.and_r(Nat.is_le(prev, h), Ext4Proof.sorted_from(t, h), s)
        %Equal.sym(List<&2, T.Ext4HtLeaf>, HW.Ext4Htree.chunk(t, sp2, cap, Con{e, Nil{}}, sz, h, h, Con{l, Nil{}}), List.reverse.go(&2, T.Ext4HtLeaf, Con{l, Nil{}}, k), Ext4Proof.chunk_acc(t, sp2, cap, Con{e, Nil{}}, sz, h, h, Con{l, Nil{}})) : {T.Ext4Htree.ordered(Con{T.Ext4HtLeaf{lo0, es0}, _}) == True{} : Bool}
        +rest = Ext4Proof.chunk_ord(t, sp2, cap, Con{e, Nil{}}, sz, h, h, lo, List.reverse(&2, T.Ext4HtEnt, cur), {==}, st, Ext4Proof.le_refl(h), Ext4Proof.and_i(Nat.is_le(h, h), True{}, Ext4Proof.le_refl(h), {==}), Ext4Proof.and_i(Nat.is_le(h, h), True{}, Ext4Proof.le_refl(h), {==}), Ext4Proof.le_trans(lo, prev, h, hl, Ext4Proof.lt_le(prev, h, plt)), Ext4Proof.all_lt_rev(cur, Nil{}, h, Ext4Proof.all_le_lt(cur, prev, h, hc, plt), {==}))
        Ext4Proof.and_i(T.Ext4Htree.ordered.pair(T.Ext4HtLeaf{lo0, es0}, l), T.Ext4Htree.ordered(Con{l, k}), Ext4Proof.leaf_pair(lo0, es0, lo, cur, h0, h1, hg), rest)
    case Con{+e, +t} False{}:
      +q => +s => +hl => +hc => +hg => +h0 => +h1 =>
        +h = T.Ext4HtEnt.hash(e)
        +u = Nat.add(used, HW.Ext4Htree.size(e))
        +ph = Ext4Proof.and_l(Nat.is_le(prev, h), Ext4Proof.sorted_from(t, h), s)
        +lh = Ext4Proof.le_trans(lo, prev, h, hl, ph)
        Ext4Proof.chunk_ord(t, HW.Ext4Htree.split(t, cap, u, h), cap, Con{e, cur}, u, lo, h, lo0, es0, {==}, Ext4Proof.and_r(Nat.is_le(prev, h), Ext4Proof.sorted_from(t, h), s), lh, Ext4Proof.and_i(Nat.is_le(h, h), Ext4Proof.all_le(cur, h), Ext4Proof.le_refl(h), Ext4Proof.all_le_up(cur, prev, h, hc, ph)), Ext4Proof.and_i(Nat.is_le(lo, h), T.Ext4Htree.all_ge(cur, lo), lh, hg), h0, h1)

def Ext4Proof.ordered_tail(+l: T.Ext4HtLeaf, k: List<&2, T.Ext4HtLeaf>) -> {T.Ext4Htree.ordered(Con{l, k}) == True{} : Bool} -> {T.Ext4Htree.ordered(k) == True{} : Bool}:
  match k:
    case Nil{}:
      +p => {==}
    case Con{+m, +u}:
      +p => Ext4Proof.and_r(T.Ext4Htree.ordered.pair(l, m), T.Ext4Htree.ordered(Con{m, u}), p)

def Laws.htree_plan_ordered(es, cap):
  +xs = HW.Ext4Htree.sort(es)
  Ext4Proof.ordered_tail(T.Ext4HtLeaf{0n, Nil{}}, HW.Ext4Htree.plan(es, cap), Ext4Proof.chunk_ord(xs, HW.Ext4Htree.split(xs, cap, 0n, 0n), cap, Nil{}, 0n, 0n, 0n, 0n, Nil{}, {==}, Ext4Proof.sort_sorted(es, Nil{}, {==}), {==}, {==}, {==}, {==}, {==}))

def Laws.htree_writer_lookup(es, cap, n, h, con):
  Ext4Proof.lookup_scan(HW.Ext4Htree.plan(es, cap), n, h, Laws.htree_plan_ordered(es, cap), con)

# The journal: records after the last commit, with no commit among them,
# change nothing the scan answers

def Ext4Proof.no_commit_tail(u: List<&2, JL.Jbd2Rec>, ok: Bool, +s: Nat, +ps: List<&2, JL.Jbd2Put>, +vs: List<&2, Nat>, +out: List<&2, JL.Jbd2Tx>) -> {JL.Jbd2Log.no_commit(u) == True{} : Bool} -> {JL.Jbd2Log.scan.go(u, ok, s, ps, vs, out) == List.reverse(&2, JL.Jbd2Tx, out) : List<&2, JL.Jbd2Tx>}:
  match u ok:
    case Nil{} _:
      +nc => {==}
    case Con{r, t} False{}:
      +nc => {==}
    case Con{JL.Jbd2RDesc{q, xs}, +t} True{}:
      +nc => Ext4Proof.no_commit_tail(t, JL.Jbd2Log.fits(t, s), s, JL.Jbd2Log.rev_onto(JL.Jbd2Put, xs, ps), vs, out, nc)
    case Con{JL.Jbd2RRevoke{q, bs}, +t} True{}:
      +nc => Ext4Proof.no_commit_tail(t, JL.Jbd2Log.fits(t, s), s, ps, JL.Jbd2Log.rev_onto(Nat, bs, vs), out, nc)
    case Con{JL.Jbd2RCommit{q}, +t} True{}:
      +nc => Ext4Proof.no({JL.Jbd2Log.scan.go(Con{JL.Jbd2RCommit{q}, t}, True{}, s, ps, vs, out) == List.reverse(&2, JL.Jbd2Tx, out) : List<&2, JL.Jbd2Tx>}, nc)

def Ext4Proof.scan_step(b: Bool, +r: JL.Jbd2Rec, +t: List<&2, JL.Jbd2Rec>, +s: Nat, +ps: List<&2, JL.Jbd2Put>, +vs: List<&2, Nat>, +out: List<&2, JL.Jbd2Tx>, +u: List<&2, JL.Jbd2Rec>, ih: @s2: Nat -> @ps2: List<&2, JL.Jbd2Put> -> @vs2: List<&2, Nat> -> @out2: List<&2, JL.Jbd2Tx> -> {JL.Jbd2Log.no_commit(u) == True{} : Bool} -> {JL.Jbd2Log.scan.go(List.append(&2, JL.Jbd2Rec, t, u), JL.Jbd2Log.fits(List.append(&2, JL.Jbd2Rec, t, u), s2), s2, ps2, vs2, out2) == JL.Jbd2Log.scan.go(t, JL.Jbd2Log.fits(t, s2), s2, ps2, vs2, out2) : List<&2, JL.Jbd2Tx>}) -> {JL.Jbd2Log.no_commit(u) == True{} : Bool} -> {JL.Jbd2Log.scan.go(Con{r, List.append(&2, JL.Jbd2Rec, t, u)}, b, s, ps, vs, out) == JL.Jbd2Log.scan.go(Con{r, t}, b, s, ps, vs, out) : List<&2, JL.Jbd2Tx>}:
  match b r:
    case False{} JL.Jbd2RDesc{q, xs}:
      +nc => {==}
    case False{} JL.Jbd2RRevoke{q, bs}:
      +nc => {==}
    case False{} JL.Jbd2RCommit{q}:
      +nc => {==}
    case True{} JL.Jbd2RDesc{q, xs}:
      +nc => ih(s, JL.Jbd2Log.rev_onto(JL.Jbd2Put, xs, ps), vs, out, nc)
    case True{} JL.Jbd2RRevoke{q, bs}:
      +nc => ih(s, ps, JL.Jbd2Log.rev_onto(Nat, bs, vs), out, nc)
    case True{} JL.Jbd2RCommit{q}:
      +nc => ih(1n+s, Nil{}, Nil{}, Con{JL.Jbd2Tx{s, List.reverse(&2, JL.Jbd2Put, ps), List.reverse(&2, Nat, vs)}, out}, nc)

def Ext4Proof.scan_append(rs: List<&2, JL.Jbd2Rec>, +s: Nat, +ps: List<&2, JL.Jbd2Put>, +vs: List<&2, Nat>, +out: List<&2, JL.Jbd2Tx>, +u: List<&2, JL.Jbd2Rec>) -> {JL.Jbd2Log.no_commit(u) == True{} : Bool} -> {JL.Jbd2Log.scan.go(List.append(&2, JL.Jbd2Rec, rs, u), JL.Jbd2Log.fits(List.append(&2, JL.Jbd2Rec, rs, u), s), s, ps, vs, out) == JL.Jbd2Log.scan.go(rs, JL.Jbd2Log.fits(rs, s), s, ps, vs, out) : List<&2, JL.Jbd2Tx>}:
  match rs:
    case Nil{}:
      +nc => Ext4Proof.no_commit_tail(u, JL.Jbd2Log.fits(u, s), s, ps, vs, out, nc)
    case Con{+r, +t}:
      Ext4Proof.scan_step(Nat.is_eq(JL.Jbd2Rec.seq(r), s), r, t, s, ps, vs, out, u, s2 => ps2 => vs2 => out2 => Ext4Proof.scan_append(t, s2, ps2, vs2, out2, u))

def Laws.scan_incomplete(s, rs, u, nc):
  Ext4Proof.scan_append(rs, s, Nil{}, Nil{}, Nil{}, u, nc)

# Revocation: the revoke table answers what the transactions say

def Ext4Proof.or_and_false(+a: Bool, +r: Bool) -> {Bool.or(Bool.and(a, False{}), r) == r : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def Ext4Proof.or_and_dist(+a: Bool, +e: Bool, +m: Bool, +r: Bool) -> {Bool.or(Bool.and(a, m), Bool.or(Bool.and(e, a), r)) == Bool.or(Bool.and(a, Bool.or(e, m)), r) : Bool}:
  match a e m r:
    case True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} False{}:
      {==}
    case True{} True{} False{} True{}:
      {==}
    case True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{}:
      {==}
    case False{} True{} True{} False{}:
      {==}
    case False{} True{} False{} True{}:
      {==}
    case False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{}:
      {==}

def Ext4Proof.or_swap(+p: Bool, +q: Bool, +r: Bool) -> {Bool.or(p, Bool.or(q, r)) == Bool.or(Bool.or(q, p), r) : Bool}:
  match p q r:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def Ext4Proof.or_false(+a: Bool) -> {Bool.or(a, False{}) == False{} : Bool} -> {a == False{} : Bool}:
  match a:
    case True{}:
      +p => p
    case False{}:
      +p => {==}

# the records rvs pushes for a revoke block's numbers vs of transaction s
def Ext4Proof.rvs(vs: List<&2, Nat>, +s: Nat, +acc: List<&2, JL.Jbd2Rv>, +b: Nat, +x: Nat) -> {JL.Jbd2Log.revoked(JL.Jbd2Log.rvs(vs, s, acc), b, x) == Bool.or(Bool.and(Nat.is_le(x, s), JL.Jbd2Log.member(vs, b)), JL.Jbd2Log.revoked(acc, b, x)) : Bool}:
  match vs:
    case Nil{}:
      Equal.sym(Bool, Bool.or(Bool.and(Nat.is_le(x, s), False{}), JL.Jbd2Log.revoked(acc, b, x)), JL.Jbd2Log.revoked(acc, b, x), Ext4Proof.or_and_false(Nat.is_le(x, s), JL.Jbd2Log.revoked(acc, b, x)))
    case Con{+v, +t}:
      +a = Nat.is_le(x, s)
      +m = JL.Jbd2Log.member(t, b)
      +e = Nat.is_eq(v, b)
      +r = JL.Jbd2Log.revoked(acc, b, x)
      Equal.trans(Bool, JL.Jbd2Log.revoked(JL.Jbd2Log.rvs(t, s, Con{JL.Jbd2Rv{v, s}, acc}), b, x), Bool.or(Bool.and(a, m), Bool.or(Bool.and(e, a), r)), Bool.or(Bool.and(a, Bool.or(e, m)), r), Ext4Proof.rvs(t, s, Con{JL.Jbd2Rv{v, s}, acc}, b, x), Ext4Proof.or_and_dist(a, e, m, r))

# the table built from the transactions txs onto acc
def Ext4Proof.table(txs: List<&2, JL.Jbd2Tx>, +acc: List<&2, JL.Jbd2Rv>, +b: Nat, +x: Nat) -> {JL.Jbd2Log.revoked(JL.Jbd2Log.table.go(txs, acc), b, x) == Bool.or(JL.Jbd2Log.revoked_in(txs, b, x), JL.Jbd2Log.revoked(acc, b, x)) : Bool}:
  match txs:
    case Nil{}:
      {==}
    case Con{JL.Jbd2Tx{+s, ps, +vs}, +t}:
      +ri = JL.Jbd2Log.revoked_in(t, b, x)
      +q = Bool.and(Nat.is_le(x, s), JL.Jbd2Log.member(vs, b))
      +r = JL.Jbd2Log.revoked(acc, b, x)
      +rv = JL.Jbd2Log.revoked(JL.Jbd2Log.rvs(vs, s, acc), b, x)
      +rhs = Bool.or(Bool.or(q, ri), r)
      %Equal.sym(Bool, JL.Jbd2Log.revoked(JL.Jbd2Log.table.go(t, JL.Jbd2Log.rvs(vs, s, acc)), b, x), Bool.or(ri, rv), Ext4Proof.table(t, JL.Jbd2Log.rvs(vs, s, acc), b, x)) : {_ == rhs : Bool}
      %Equal.sym(Bool, rv, Bool.or(q, r), Ext4Proof.rvs(vs, s, acc, b, x)) : {Bool.or(ri, _) == rhs : Bool}
      Ext4Proof.or_swap(ri, q, r)

# Planning: every block kept is one the transactions do not revoke

def Ext4Proof.keep_pick(b: Bool, +txs: List<&2, JL.Jbd2Tx>, +s: Nat, +p: JL.Jbd2Put, +acc: List<&2, JL.Jbd2Do>) -> {JL.Jbd2Log.revoked(JL.Jbd2Log.table(txs), JL.Jbd2Put.block(p), s) == b : Bool} -> {JL.Jbd2Log.none_revoked(txs, acc) == True{} : Bool} -> {JL.Jbd2Log.none_revoked(txs, JL.Jbd2Log.keep.pick(b, s, p, acc)) == True{} : Bool}:
  match b:
    case True{}:
      +e => +h => h
    case False{}:
      +e => +h =>
        +ri = JL.Jbd2Log.revoked_in(txs, JL.Jbd2Put.block(p), s)
        +f = Ext4Proof.or_false(ri, Equal.trans(Bool, Bool.or(ri, JL.Jbd2Log.revoked(Nil{}, JL.Jbd2Put.block(p), s)), JL.Jbd2Log.revoked(JL.Jbd2Log.table(txs), JL.Jbd2Put.block(p), s), False{}, Equal.sym(Bool, JL.Jbd2Log.revoked(JL.Jbd2Log.table.go(txs, Nil{}), JL.Jbd2Put.block(p), s), Bool.or(ri, JL.Jbd2Log.revoked(Nil{}, JL.Jbd2Put.block(p), s)), Ext4Proof.table(txs, Nil{}, JL.Jbd2Put.block(p), s)), e))
        %Equal.sym(Bool, ri, False{}, f) : {Bool.and(Bool.not(_), JL.Jbd2Log.none_revoked(txs, acc)) == True{} : Bool}
        h

def Ext4Proof.keep(ps: List<&2, JL.Jbd2Put>, +s: Nat, +txs: List<&2, JL.Jbd2Tx>, +acc: List<&2, JL.Jbd2Do>) -> {JL.Jbd2Log.none_revoked(txs, acc) == True{} : Bool} -> {JL.Jbd2Log.none_revoked(txs, JL.Jbd2Log.keep(ps, s, JL.Jbd2Log.table(txs), acc)) == True{} : Bool}:
  match ps:
    case Nil{}:
      +h => h
    case Con{+p, +t}:
      +h => Ext4Proof.keep(t, s, txs, JL.Jbd2Log.keep.pick(JL.Jbd2Log.revoked(JL.Jbd2Log.table(txs), JL.Jbd2Put.block(p), s), s, p, acc), Ext4Proof.keep_pick(JL.Jbd2Log.revoked(JL.Jbd2Log.table(txs), JL.Jbd2Put.block(p), s), txs, s, p, acc, {==}, h))

def Ext4Proof.none_rev(xs: List<&2, JL.Jbd2Do>, +txs: List<&2, JL.Jbd2Tx>, +acc: List<&2, JL.Jbd2Do>) -> {JL.Jbd2Log.none_revoked(txs, xs) == True{} : Bool} -> {JL.Jbd2Log.none_revoked(txs, acc) == True{} : Bool} -> {JL.Jbd2Log.none_revoked(txs, List.reverse.go(&2, JL.Jbd2Do, xs, acc)) == True{} : Bool}:
  match xs:
    case Nil{}:
      +p => +q => q
    case Con{JL.Jbd2Do{+s, +p}, +t}:
      +a => +q =>
        +nr = Bool.not(JL.Jbd2Log.revoked_in(txs, JL.Jbd2Put.block(p), s))
        Ext4Proof.none_rev(t, txs, Con{JL.Jbd2Do{s, p}, acc}, Ext4Proof.and_r(nr, JL.Jbd2Log.none_revoked(txs, t), a), Ext4Proof.and_i(nr, JL.Jbd2Log.none_revoked(txs, acc), Ext4Proof.and_l(nr, JL.Jbd2Log.none_revoked(txs, t), a), q))

def Ext4Proof.plan(it: List<&2, JL.Jbd2Tx>, +txs: List<&2, JL.Jbd2Tx>, +acc: List<&2, JL.Jbd2Do>) -> {JL.Jbd2Log.none_revoked(txs, acc) == True{} : Bool} -> {JL.Jbd2Log.none_revoked(txs, JL.Jbd2Log.plan.go(it, JL.Jbd2Log.table(txs), acc)) == True{} : Bool}:
  match it:
    case Nil{}:
      +h => Ext4Proof.none_rev(acc, txs, Nil{}, h, {==})
    case Con{JL.Jbd2Tx{+s, +ps, vs}, +t}:
      +h => Ext4Proof.plan(t, txs, JL.Jbd2Log.keep(ps, s, JL.Jbd2Log.table(txs), acc), Ext4Proof.keep(ps, s, txs, acc, h))

def Laws.plan_revoked(txs):
  Ext4Proof.plan(txs, txs, Nil{}, {==})

# Replay on a MemDev: every write good, each is blockdev's update, and
# reading afterwards gives the last write of each block

def Ext4Proof.eq_refl(+x: Nat) -> {Nat.is_eq(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Ext4Proof.eq_refl(p)

def Ext4Proof.eq_sound(+a: Nat, +b: Nat) -> {Nat.is_eq(a, b) == True{} : Bool} -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      +p => {==}
    case 0n 1n+bp:
      +p => Ext4Proof.no({0n == 1n+bp : Nat}, p)
    case 1n+ap 0n:
      +p => Ext4Proof.no({1n+ap == 0n : Nat}, p)
    case 1n+ap 1n+bp:
      +p => Equal.cong(Nat, Nat, k => 1n+k, ap, bp, Ext4Proof.eq_sound(ap, bp, p))

def Ext4Proof.eq_sym_false(+a: Nat, +b: Nat) -> {Nat.is_eq(a, b) == False{} : Bool} -> {Nat.is_eq(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      +p => p
    case 0n 1n+bp:
      +p => {==}
    case 1n+ap 0n:
      +p => {==}
    case 1n+ap 1n+bp:
      +p => Ext4Proof.eq_sym_false(ap, bp, p)

# the writes as blockdev's updates
def Ext4Proof.updates(ws: List<&2, JW.Jbd2Write>, d: D.MemDev) -> D.MemDev:
  match ws:
    case Nil{}:
      d
    case Con{JW.Jbd2Write{n, data}, t}:
      Ext4Proof.updates(t, D.MemDev.update(d, n, data))

def Ext4Proof.eq_move(+x: Nat, +a: Nat, +b: Nat) -> {a == b : Nat} -> {Nat.is_eq(x, b) == True{} : Bool} -> {Nat.is_eq(x, a) == True{} : Bool}:
  +e => +h =>
    %Equal.sym(Nat, a, b, e) : {Nat.is_eq(x, _) == True{} : Bool}
    h

# one good write is the update (blockdev's own_write_ok)
def Ext4Proof.write_one(+d: D.MemDev, +bs: Nat, +n: Nat, +data: B.Octets) -> {Nat.is_eq(D.MemDev.block_size(d), bs) == True{} : Bool} -> {Nat.is_eq(B.Octets.len(data), bs) == True{} : Bool} -> {Nat.is_lt(n, D.MemDev.block_count(d)) == True{} : Bool} -> {DW.Ext4Dev.write(~D.MemDev, ~D.MemDev.block_size, ~DW.Ext4Dev.mem_write, d, bs, n, data) == Done{D.MemDev.update(d, n, data)} : Result<&2, &2, E.Ext4Error, D.MemDev>}:
  +hb => +hl => +hn =>
    +dbs = D.MemDev.block_size(d)
    +up = D.MemDev.update(d, n, data)
    %Equal.sym(Bool, Nat.is_eq(dbs, bs), True{}, hb) : {DW.Ext4Dev.write.go(~D.MemDev, ~DW.Ext4Dev.mem_write, _, Bool.and(Nat.is_lt(0n, dbs), Nat.is_eq(Nat.mod(bs, dbs), 0n)), d, dbs, bs, n, data) == Done{up} : Result<&2, &2, E.Ext4Error, D.MemDev>}
    %Equal.sym(D.MemDev & Result<&2, &2, D.DevError, Unit>, D.MemDev.own_write_block(d, n, data), (up, Done{Unit{}}), BDL.own_write_ok(d, n, data, Ext4Proof.eq_move(B.Octets.len(data), dbs, bs, Ext4Proof.eq_sound(dbs, bs, hb), hl), hn)) : {DW.Ext4Dev.lift(D.MemDev, DW.Ext4Dev.mem_write.fin(_)) == Done{up} : Result<&2, &2, E.Ext4Error, D.MemDev>}
    {==}

def Ext4Proof.lt_move(+x: Nat, +a: Nat, +b: Nat) -> {a == b : Nat} -> {Nat.is_lt(x, b) == True{} : Bool} -> {Nat.is_lt(x, a) == True{} : Bool}:
  +e => +h =>
    %Equal.sym(Nat, a, b, e) : {Nat.is_lt(x, _) == True{} : Bool}
    h

def Ext4Proof.eq_left(+a: Nat, +b: Nat, +c: Nat) -> {a == b : Nat} -> {Nat.is_eq(b, c) == True{} : Bool} -> {Nat.is_eq(a, c) == True{} : Bool}:
  +e => +h =>
    %Equal.sym(Nat, a, b, e) : {Nat.is_eq(_, c) == True{} : Bool}
    h

# an update keeps the block size and count (blockdev's laws), so the
# updates do
def Ext4Proof.size_updates(ws: List<&2, JW.Jbd2Write>, +d: D.MemDev) -> {D.MemDev.block_size(Ext4Proof.updates(ws, d)) == D.MemDev.block_size(d) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case Con{JW.Jbd2Write{+n, +data}, +t}:
      Equal.trans(Nat, D.MemDev.block_size(Ext4Proof.updates(t, D.MemDev.update(d, n, data))), D.MemDev.block_size(D.MemDev.update(d, n, data)), D.MemDev.block_size(d), Ext4Proof.size_updates(t, D.MemDev.update(d, n, data)), BDL.update_keeps_size(d, n, data))

def Ext4Proof.count_updates(ws: List<&2, JW.Jbd2Write>, +d: D.MemDev) -> {D.MemDev.block_count(Ext4Proof.updates(ws, d)) == D.MemDev.block_count(d) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case Con{JW.Jbd2Write{+n, +data}, +t}:
      Equal.trans(Nat, D.MemDev.block_count(Ext4Proof.updates(t, D.MemDev.update(d, n, data))), D.MemDev.block_count(D.MemDev.update(d, n, data)), D.MemDev.block_count(d), Ext4Proof.count_updates(t, D.MemDev.update(d, n, data)), BDL.update_keeps_count(d, n, data))

# writing good writes to a MemDev is updating it with them
def Ext4Proof.write_all(ws: List<&2, JW.Jbd2Write>, +d: D.MemDev, +bs: Nat, +cnt: Nat) -> {D.MemDev.block_size(d) == bs : Nat} -> {D.MemDev.block_count(d) == cnt : Nat} -> {DW.Ext4Dev.fits(bs, cnt, ws) == True{} : Bool} -> {DW.Ext4Dev.write_all(~D.MemDev, ~D.MemDev.block_size, ~DW.Ext4Dev.mem_write, ws, Done{d}, bs) == Done{Ext4Proof.updates(ws, d)} : Result<&2, &2, E.Ext4Error, D.MemDev>}:
  match ws:
    case Nil{}:
      +hb => +hc => +hf => {==}
    case Con{JW.Jbd2Write{+n, +data}, +t}:
      +hb => +hc => +hf =>
        +a = Bool.and(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, cnt))
        +ha = Ext4Proof.and_l(a, DW.Ext4Dev.fits(bs, cnt, t), hf)
        +hl = Ext4Proof.and_l(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, cnt), ha)
        +hn = Ext4Proof.and_r(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, cnt), ha)
        +up = D.MemDev.update(d, n, data)
        +w = Ext4Proof.write_one(d, bs, n, data, Ext4Proof.eq_left(D.MemDev.block_size(d), bs, bs, hb, Ext4Proof.eq_refl(bs)), hl, Ext4Proof.lt_move(n, D.MemDev.block_count(d), cnt, hc, hn))
        %Equal.sym(Result<&2, &2, E.Ext4Error, D.MemDev>, DW.Ext4Dev.write(~D.MemDev, ~D.MemDev.block_size, ~DW.Ext4Dev.mem_write, d, bs, n, data), Done{up}, w) : {DW.Ext4Dev.write_all(~D.MemDev, ~D.MemDev.block_size, ~DW.Ext4Dev.mem_write, t, _, bs) == Done{Ext4Proof.updates(t, up)} : Result<&2, &2, E.Ext4Error, D.MemDev>}
        Ext4Proof.write_all(t, up, bs, cnt, Equal.trans(Nat, D.MemDev.block_size(up), D.MemDev.block_size(d), bs, BDL.update_keeps_size(d, n, data), hb), Equal.trans(Nat, D.MemDev.block_count(up), D.MemDev.block_count(d), cnt, BDL.update_keeps_count(d, n, data), hc), Ext4Proof.and_r(a, DW.Ext4Dev.fits(bs, cnt, t), hf))

# Reading after the updates: the last write to the block, if any

def Ext4Proof.last.pick(hit: Bool, data: B.Octets, x: Result<&2, &2, D.DevError, B.Octets>) -> Result<&2, &2, D.DevError, B.Octets>:
  match hit:
    case True{}:
      Done{data}
    case False{}:
      x

def Ext4Proof.last(ws: List<&2, JW.Jbd2Write>, +m: Nat, x: Result<&2, &2, D.DevError, B.Octets>) -> Result<&2, &2, D.DevError, B.Octets>:
  match ws:
    case Nil{}:
      x
    case Con{JW.Jbd2Write{n, data}, t}:
      Ext4Proof.last(t, m, Ext4Proof.last.pick(Nat.is_eq(n, m), data, x))

def Ext4Proof.read_one(b: Bool, +d: D.MemDev, +n: Nat, +data: B.Octets, +m: Nat) -> {Nat.is_eq(n, m) == b : Bool} -> {Nat.is_eq(B.Octets.len(data), D.MemDev.block_size(d)) == True{} : Bool} -> {Nat.is_lt(n, D.MemDev.block_count(d)) == True{} : Bool} -> {D.MemDev.read_block(D.MemDev.update(d, n, data), m) == Ext4Proof.last.pick(b, data, D.MemDev.read_block(d, m)) : Result<&2, &2, D.DevError, B.Octets>}:
  match b:
    case True{}:
      +e => +hl => +hn =>
        %Ext4Proof.eq_sound(n, m, e) : {D.MemDev.read_block(D.MemDev.update(d, n, data), _) == Done{data} : Result<&2, &2, D.DevError, B.Octets>}
        BDL.read_after_update(d, n, data, hl, hn)
    case False{}:
      +e => +hl => +hn => BDL.update_other(d, n, m, data, Ext4Proof.eq_sym_false(n, m, e))

def Ext4Proof.reads(ws: List<&2, JW.Jbd2Write>, +d: D.MemDev, +m: Nat, +bs: Nat, +cnt: Nat) -> {D.MemDev.block_size(d) == bs : Nat} -> {D.MemDev.block_count(d) == cnt : Nat} -> {DW.Ext4Dev.fits(bs, cnt, ws) == True{} : Bool} -> {D.MemDev.read_block(Ext4Proof.updates(ws, d), m) == Ext4Proof.last(ws, m, D.MemDev.read_block(d, m)) : Result<&2, &2, D.DevError, B.Octets>}:
  match ws:
    case Nil{}:
      +hb => +hc => +hf => {==}
    case Con{JW.Jbd2Write{+n, +data}, +t}:
      +hb => +hc => +hf =>
        +a = Bool.and(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, cnt))
        +ha = Ext4Proof.and_l(a, DW.Ext4Dev.fits(bs, cnt, t), hf)
        +hl = Ext4Proof.and_l(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, cnt), ha)
        +hn = Ext4Proof.and_r(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, cnt), ha)
        +up = D.MemDev.update(d, n, data)
        +ih = Ext4Proof.reads(t, up, m, bs, cnt, Equal.trans(Nat, D.MemDev.block_size(up), D.MemDev.block_size(d), bs, BDL.update_keeps_size(d, n, data), hb), Equal.trans(Nat, D.MemDev.block_count(up), D.MemDev.block_count(d), cnt, BDL.update_keeps_count(d, n, data), hc), Ext4Proof.and_r(a, DW.Ext4Dev.fits(bs, cnt, t), hf))
        +one = Ext4Proof.read_one(Nat.is_eq(n, m), d, n, data, m, {==}, Ext4Proof.eq_move(B.Octets.len(data), D.MemDev.block_size(d), bs, hb, hl), Ext4Proof.lt_move(n, D.MemDev.block_count(d), cnt, hc, hn))
        Equal.trans(Result<&2, &2, D.DevError, B.Octets>, D.MemDev.read_block(Ext4Proof.updates(t, up), m), Ext4Proof.last(t, m, D.MemDev.read_block(up, m)), Ext4Proof.last(t, m, Ext4Proof.last.pick(Nat.is_eq(n, m), data, D.MemDev.read_block(d, m))), ih, Equal.cong(Result<&2, &2, D.DevError, B.Octets>, Result<&2, &2, D.DevError, B.Octets>, x => Ext4Proof.last(t, m, x), D.MemDev.read_block(up, m), Ext4Proof.last.pick(Nat.is_eq(n, m), data, D.MemDev.read_block(d, m)), one))

# the last write wins, so writing the same list twice is writing it once

def Ext4Proof.lp(acc: Maybe<&2, B.Octets>, x: Result<&2, &2, D.DevError, B.Octets>) -> Result<&2, &2, D.DevError, B.Octets>:
  match acc:
    case Some{v}:
      Done{v}
    case None{}:
      x

def Ext4Proof.fl.pick(hit: Bool, data: B.Octets, acc: Maybe<&2, B.Octets>) -> Maybe<&2, B.Octets>:
  match hit:
    case True{}:
      Some{data}
    case False{}:
      acc

def Ext4Proof.fl(ws: List<&2, JW.Jbd2Write>, +m: Nat, acc: Maybe<&2, B.Octets>) -> Maybe<&2, B.Octets>:
  match ws:
    case Nil{}:
      acc
    case Con{JW.Jbd2Write{n, data}, t}:
      Ext4Proof.fl(t, m, Ext4Proof.fl.pick(Nat.is_eq(n, m), data, acc))

def Ext4Proof.last_fl.at(b: Bool, +t: List<&2, JW.Jbd2Write>, +m: Nat, +data: B.Octets, +acc: Maybe<&2, B.Octets>, +x: Result<&2, &2, D.DevError, B.Octets>, ih: @a2: Maybe<&2, B.Octets> -> {Ext4Proof.last(t, m, Ext4Proof.lp(a2, x)) == Ext4Proof.lp(Ext4Proof.fl(t, m, a2), x) : Result<&2, &2, D.DevError, B.Octets>}) -> {Ext4Proof.last(t, m, Ext4Proof.last.pick(b, data, Ext4Proof.lp(acc, x))) == Ext4Proof.lp(Ext4Proof.fl(t, m, Ext4Proof.fl.pick(b, data, acc)), x) : Result<&2, &2, D.DevError, B.Octets>}:
  match b:
    case True{}:
      ih(Some{data})
    case False{}:
      ih(acc)

def Ext4Proof.last_fl(ws: List<&2, JW.Jbd2Write>, +m: Nat, +acc: Maybe<&2, B.Octets>, +x: Result<&2, &2, D.DevError, B.Octets>) -> {Ext4Proof.last(ws, m, Ext4Proof.lp(acc, x)) == Ext4Proof.lp(Ext4Proof.fl(ws, m, acc), x) : Result<&2, &2, D.DevError, B.Octets>}:
  match ws:
    case Nil{}:
      {==}
    case Con{JW.Jbd2Write{+n, +data}, +t}:
      Ext4Proof.last_fl.at(Nat.is_eq(n, m), t, m, data, acc, x, a2 => Ext4Proof.last_fl(t, m, a2, x))

def Ext4Proof.lp_twice(f: Maybe<&2, B.Octets>, +x: Result<&2, &2, D.DevError, B.Octets>) -> {Ext4Proof.lp(f, Ext4Proof.lp(f, x)) == Ext4Proof.lp(f, x) : Result<&2, &2, D.DevError, B.Octets>}:
  match f:
    case Some{v}:
      {==}
    case None{}:
      {==}

def Ext4Proof.last_twice(+ws: List<&2, JW.Jbd2Write>, +m: Nat, +x: Result<&2, &2, D.DevError, B.Octets>) -> {Ext4Proof.last(ws, m, Ext4Proof.last(ws, m, x)) == Ext4Proof.last(ws, m, x) : Result<&2, &2, D.DevError, B.Octets>}:
  +f = Ext4Proof.fl(ws, m, None{})
  %Equal.sym(Result<&2, &2, D.DevError, B.Octets>, Ext4Proof.last(ws, m, x), Ext4Proof.lp(f, x), Ext4Proof.last_fl(ws, m, None{}, x)) : {Ext4Proof.last(ws, m, _) == _ : Result<&2, &2, D.DevError, B.Octets>}
  Equal.trans(Result<&2, &2, D.DevError, B.Octets>, Ext4Proof.last(ws, m, Ext4Proof.lp(f, x)), Ext4Proof.lp(f, Ext4Proof.lp(f, x)), Ext4Proof.lp(f, x), Ext4Proof.last_fl(ws, m, None{}, Ext4Proof.lp(f, x)), Ext4Proof.lp_twice(f, x))

def Laws.replay_idempotent(d, ws, m, ok):
  +bs = D.MemDev.block_size(d)
  +cnt = D.MemDev.block_count(d)
  +d1 = Ext4Proof.updates(ws, d)
  +s1 = Ext4Proof.size_updates(ws, d)
  +c1 = Ext4Proof.count_updates(ws, d)
  %Equal.sym(Result<&2, &2, E.Ext4Error, D.MemDev>, DW.Ext4Dev.write_all(~D.MemDev, ~D.MemDev.block_size, ~DW.Ext4Dev.mem_write, ws, Done{d}, bs), Done{d1}, Ext4Proof.write_all(ws, d, bs, cnt, {==}, {==}, ok)) : {DW.Ext4Dev.read_mem(DW.Ext4Dev.write_all(~D.MemDev, ~D.MemDev.block_size, ~DW.Ext4Dev.mem_write, ws, _, bs), m) == DW.Ext4Dev.read_mem(_, m) : Result<&2, &2, E.Ext4Error, B.Octets>}
  %Equal.sym(Result<&2, &2, E.Ext4Error, D.MemDev>, DW.Ext4Dev.write_all(~D.MemDev, ~D.MemDev.block_size, ~DW.Ext4Dev.mem_write, ws, Done{d1}, bs), Done{Ext4Proof.updates(ws, d1)}, Ext4Proof.write_all(ws, d1, bs, cnt, s1, c1, ok)) : {DW.Ext4Dev.read_mem(_, m) == DW.Ext4Dev.read_mem(Done{d1}, m) : Result<&2, &2, E.Ext4Error, B.Octets>}
  +r = D.MemDev.read_block(d, m)
  +e2 = Ext4Proof.reads(ws, d1, m, bs, cnt, s1, c1, ok)
  +e1 = Ext4Proof.reads(ws, d, m, bs, cnt, {==}, {==}, ok)
  +same = Equal.trans(Result<&2, &2, D.DevError, B.Octets>, D.MemDev.read_block(Ext4Proof.updates(ws, d1), m), Ext4Proof.last(ws, m, D.MemDev.read_block(d1, m)), D.MemDev.read_block(d1, m), e2, Equal.trans(Result<&2, &2, D.DevError, B.Octets>, Ext4Proof.last(ws, m, D.MemDev.read_block(d1, m)), Ext4Proof.last(ws, m, Ext4Proof.last(ws, m, r)), D.MemDev.read_block(d1, m), Equal.cong(Result<&2, &2, D.DevError, B.Octets>, Result<&2, &2, D.DevError, B.Octets>, x => Ext4Proof.last(ws, m, x), D.MemDev.read_block(d1, m), Ext4Proof.last(ws, m, r), e1), Equal.trans(Result<&2, &2, D.DevError, B.Octets>, Ext4Proof.last(ws, m, Ext4Proof.last(ws, m, r)), Ext4Proof.last(ws, m, r), D.MemDev.read_block(d1, m), Ext4Proof.last_twice(ws, m, r), Equal.sym(Result<&2, &2, D.DevError, B.Octets>, D.MemDev.read_block(d1, m), Ext4Proof.last(ws, m, r), e1))))
  Equal.cong(Result<&2, &2, D.DevError, B.Octets>, Result<&2, &2, E.Ext4Error, B.Octets>, x => DW.Ext4Dev.dev_read(x), D.MemDev.read_block(Ext4Proof.updates(ws, d1), m), D.MemDev.read_block(d1, m), same)

# A committed transaction recovers as its unrevoked blocks

def Ext4Proof.append_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(List<&2, A>, List<&2, A>, ys => Con{x, ys}, List.append(&2, A, t, Nil{}), t, Ext4Proof.append_nil(A, t))

def Ext4Proof.rev_rev(-A: Data, xs: List<&2, A>, +acc: List<&2, A>, +ys: List<&2, A>) -> {List.reverse.go(&2, A, List.reverse.go(&2, A, xs, acc), ys) == List.reverse.go(&2, A, acc, List.append(&2, A, xs, ys)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Ext4Proof.rev_rev(A, t, Con{x, acc}, ys)

def Ext4Proof.rev_onto(-A: Data, xs: List<&2, A>, +acc: List<&2, A>) -> {JL.Jbd2Log.rev_onto(A, xs, acc) == List.reverse.go(&2, A, xs, acc) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Ext4Proof.rev_onto(A, t, Con{x, acc})

# reversing what rev_onto reversed onto nothing gives the list back
def Ext4Proof.rr(-A: Data, +xs: List<&2, A>) -> {List.reverse(&2, A, JL.Jbd2Log.rev_onto(A, xs, Nil{})) == xs : List<&2, A>}:
  %Equal.sym(List<&2, A>, JL.Jbd2Log.rev_onto(A, xs, Nil{}), List.reverse.go(&2, A, xs, Nil{}), Ext4Proof.rev_onto(A, xs, Nil{})) : {List.reverse(&2, A, _) == xs : List<&2, A>}
  Equal.trans(List<&2, A>, List.reverse.go(&2, A, List.reverse.go(&2, A, xs, Nil{}), Nil{}), List.append(&2, A, xs, Nil{}), xs, Ext4Proof.rev_rev(A, xs, Nil{}, Nil{}), Ext4Proof.append_nil(A, xs))

def Ext4Proof.or_f(+a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# keep, with the table rv, as a filter
def Ext4Proof.filt(ps: List<&2, JL.Jbd2Put>, +s: Nat, +rv: List<&2, JL.Jbd2Rv>) -> List<&2, JL.Jbd2Do>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      JL.Jbd2Log.unrevoked.pick(JL.Jbd2Log.revoked(rv, JL.Jbd2Put.block(p), s), JL.Jbd2Do{s, p}, Ext4Proof.filt(t, s, rv))

def Ext4Proof.keep_filt.at(b: Bool, +p: JL.Jbd2Put, +t: List<&2, JL.Jbd2Put>, +s: Nat, +rv: List<&2, JL.Jbd2Rv>, +acc: List<&2, JL.Jbd2Do>, ih: @a2: List<&2, JL.Jbd2Do> -> {JL.Jbd2Log.keep(t, s, rv, a2) == List.reverse.go(&2, JL.Jbd2Do, Ext4Proof.filt(t, s, rv), a2) : List<&2, JL.Jbd2Do>}) -> {JL.Jbd2Log.keep(t, s, rv, JL.Jbd2Log.keep.pick(b, s, p, acc)) == List.reverse.go(&2, JL.Jbd2Do, JL.Jbd2Log.unrevoked.pick(b, JL.Jbd2Do{s, p}, Ext4Proof.filt(t, s, rv)), acc) : List<&2, JL.Jbd2Do>}:
  match b:
    case True{}:
      ih(acc)
    case False{}:
      ih(Con{JL.Jbd2Do{s, p}, acc})

def Ext4Proof.keep_filt(ps: List<&2, JL.Jbd2Put>, +s: Nat, +rv: List<&2, JL.Jbd2Rv>, +acc: List<&2, JL.Jbd2Do>) -> {JL.Jbd2Log.keep(ps, s, rv, acc) == List.reverse.go(&2, JL.Jbd2Do, Ext4Proof.filt(ps, s, rv), acc) : List<&2, JL.Jbd2Do>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      Ext4Proof.keep_filt.at(JL.Jbd2Log.revoked(rv, JL.Jbd2Put.block(p), s), p, t, s, rv, acc, a2 => Ext4Proof.keep_filt(t, s, rv, a2))

# the table of one transaction's revokes rv: revoked for it exactly when
# rv lists the block
def Ext4Proof.one_table(+rv: List<&2, Nat>, +s: Nat, +b: Nat) -> {JL.Jbd2Log.revoked(JL.Jbd2Log.rvs(rv, s, Nil{}), b, s) == JL.Jbd2Log.member(rv, b) : Bool}:
  +m = JL.Jbd2Log.member(rv, b)
  %Equal.sym(Bool, JL.Jbd2Log.revoked(JL.Jbd2Log.rvs(rv, s, Nil{}), b, s), Bool.or(Bool.and(Nat.is_le(s, s), m), JL.Jbd2Log.revoked(Nil{}, b, s)), Ext4Proof.rvs(rv, s, Nil{}, b, s)) : {_ == m : Bool}
  %Equal.sym(Bool, Nat.is_le(s, s), True{}, Ext4Proof.le_refl(s)) : {Bool.or(Bool.and(_, m), False{}) == m : Bool}
  Ext4Proof.or_f(m)

def Ext4Proof.filt_unrevoked(ps: List<&2, JL.Jbd2Put>, +s: Nat, +rv: List<&2, Nat>) -> {Ext4Proof.filt(ps, s, JL.Jbd2Log.rvs(rv, s, Nil{})) == JL.Jbd2Log.unrevoked(s, rv, ps) : List<&2, JL.Jbd2Do>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      +tb = JL.Jbd2Log.rvs(rv, s, Nil{})
      +d = {JL.Jbd2Do{s, p} : JL.Jbd2Do}
      %Equal.sym(Bool, JL.Jbd2Log.revoked(tb, JL.Jbd2Put.block(p), s), JL.Jbd2Log.member(rv, JL.Jbd2Put.block(p)), Ext4Proof.one_table(rv, s, JL.Jbd2Put.block(p))) : {JL.Jbd2Log.unrevoked.pick(_, d, Ext4Proof.filt(t, s, tb)) == JL.Jbd2Log.unrevoked(s, rv, Con{p, t}) : List<&2, JL.Jbd2Do>}
      Equal.cong(List<&2, JL.Jbd2Do>, List<&2, JL.Jbd2Do>, xs => JL.Jbd2Log.unrevoked.pick(JL.Jbd2Log.member(rv, JL.Jbd2Put.block(p)), d, xs), Ext4Proof.filt(t, s, tb), JL.Jbd2Log.unrevoked(s, rv, t), Ext4Proof.filt_unrevoked(t, s, rv))

def Laws.commit_replays(s, rv, ps):
  +u = JL.Jbd2Log.unrevoked(s, rv, ps)
  +t3 = {[JL.Jbd2RCommit{s}] : List<&2, JL.Jbd2Rec>}
  +t2 = {Con{JL.Jbd2RDesc{s, ps}, t3} : List<&2, JL.Jbd2Rec>}
  +t1 = {Con{JL.Jbd2RRevoke{s, rv}, t2} : List<&2, JL.Jbd2Rec>}
  +qs = JL.Jbd2Log.rev_onto(JL.Jbd2Put, ps, Nil{})
  +qv = JL.Jbd2Log.rev_onto(Nat, rv, Nil{})
  +tb = JL.Jbd2Log.rvs(rv, s, Nil{})
  %Equal.sym(Bool, Nat.is_eq(s, s), True{}, Ext4Proof.eq_refl(s)) : {JL.Jbd2Log.plan(JL.Jbd2Log.scan.go(t1, _, s, Nil{}, Nil{}, Nil{})) == u : List<&2, JL.Jbd2Do>}
  %Equal.sym(Bool, Nat.is_eq(s, s), True{}, Ext4Proof.eq_refl(s)) : {JL.Jbd2Log.plan(JL.Jbd2Log.scan.go(t2, _, s, Nil{}, qv, Nil{})) == u : List<&2, JL.Jbd2Do>}
  %Equal.sym(Bool, Nat.is_eq(s, s), True{}, Ext4Proof.eq_refl(s)) : {JL.Jbd2Log.plan(JL.Jbd2Log.scan.go(t3, _, s, qs, qv, Nil{})) == u : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Put>, List.reverse(&2, JL.Jbd2Put, qs), ps, Ext4Proof.rr(JL.Jbd2Put, ps)) : {JL.Jbd2Log.plan([JL.Jbd2Tx{s, _, List.reverse(&2, Nat, qv)}]) == u : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, Nat>, List.reverse(&2, Nat, qv), rv, Ext4Proof.rr(Nat, rv)) : {JL.Jbd2Log.plan([JL.Jbd2Tx{s, ps, _}]) == u : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Do>, JL.Jbd2Log.keep(ps, s, tb, Nil{}), List.reverse.go(&2, JL.Jbd2Do, Ext4Proof.filt(ps, s, tb), Nil{}), Ext4Proof.keep_filt(ps, s, tb, Nil{})) : {List.reverse(&2, JL.Jbd2Do, _) == u : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Do>, List.reverse.go(&2, JL.Jbd2Do, List.reverse.go(&2, JL.Jbd2Do, Ext4Proof.filt(ps, s, tb), Nil{}), Nil{}), List.append(&2, JL.Jbd2Do, Ext4Proof.filt(ps, s, tb), Nil{}), Ext4Proof.rev_rev(JL.Jbd2Do, Ext4Proof.filt(ps, s, tb), Nil{}, Nil{})) : {_ == u : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Do>, List.append(&2, JL.Jbd2Do, Ext4Proof.filt(ps, s, tb), Nil{}), Ext4Proof.filt(ps, s, tb), Ext4Proof.append_nil(JL.Jbd2Do, Ext4Proof.filt(ps, s, tb))) : {_ == u : List<&2, JL.Jbd2Do>}
  Ext4Proof.filt_unrevoked(ps, s, rv)

# Equal words: U32.is_eq says True only of equal words (Base's Word.cmp,
# bit by bit)

def Ext4Proof.cmp_clash(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Unit
    case _:
      Empty

def Ext4Proof.bool_cmp_eq(+a: Bool, +b: Bool) -> {Cmp.is_eq(Bool.cmp(a, b)) == True{} : Bool} -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      +h => {==}
    case False{} False{}:
      +h => {==}
    case True{} False{}:
      +h => Ext4Proof.no({True{} == False{} : Bool}, h)
    case False{} True{}:
      +h => Ext4Proof.no({False{} == True{} : Bool}, h)

def Ext4Proof.wcmp_fin(c: Cmp, +p: Nat, +a: Bool, +at: Word(p), +b: Bool, +bt: Word(p), ih: {Cmp.is_eq(Word.cmp(p, at, bt)) == True{} : Bool} -> {at == bt : Word(p)}) -> {Word.cmp(p, at, bt) == c : Cmp} -> {Cmp.is_eq(Word.cmp.fin(a, b, c)) == True{} : Bool} -> {WCon{a, at} == WCon{b, bt} : Word(1n+p)}:
  match c:
    case LT{}:
      +e => +h => Ext4Proof.no({WCon{a, at} == WCon{b, bt} : Word(1n+p)}, h)
    case GT{}:
      +e => +h => Ext4Proof.no({WCon{a, at} == WCon{b, bt} : Word(1n+p)}, h)
    case EQ{}:
      +e => +h =>
        +t = ih(Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, at, bt), EQ{}, e))
        %Equal.sym(Bool, a, b, Ext4Proof.bool_cmp_eq(a, b, h)) : {WCon{_, at} == WCon{b, bt} : Word(1n+p)}
        %Equal.sym(Word(p), at, bt, t) : {WCon{b, _} == WCon{b, bt} : Word(1n+p)}
        {==}

def Ext4Proof.wcmp_eq(+n: Nat, +x: Word(n), +y: Word(n)) -> {Cmp.is_eq(Word.cmp(n, x, y)) == True{} : Bool} -> {x == y : Word(n)}:
  match n:
    case 0n:
      match x y:
        case WNil{} WNil{}:
          +h => {==}
    case 1n+p:
      match x y:
        case WCon{+a, +at} WCon{+b, +bt}:
          Ext4Proof.wcmp_fin(Word.cmp(p, at, bt), p, a, at, b, bt, Ext4Proof.wcmp_eq(p, at, bt), {==})

def Ext4Proof.u32_eq(+a: U32, +b: U32) -> {U32.is_eq(a, b) == True{} : Bool} -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      +h => Equal.cong(Word(32n), U32, w => U32{w}, x, y, Ext4Proof.wcmp_eq(32n, x, y, h))

# bytes' list_eq says True only of equal lists
def Ext4Proof.list_eq(xs: List<&2, U32>, +ys: List<&2, U32>) -> {B.list_eq(xs, ys) == True{} : Bool} -> {xs == ys : List<&2, U32>}:
  match xs ys:
    case Nil{} Nil{}:
      +h => {==}
    case Nil{} Con{b, t}:
      +h => Ext4Proof.no({Nil{} == Con{b, t} : List<&2, U32>}, h)
    case Con{a, s} Nil{}:
      +h => Ext4Proof.no({Con{a, s} == Nil{} : List<&2, U32>}, h)
    case Con{+a, +s} Con{+b, +t}:
      +h =>
        %Equal.sym(U32, a, b, Ext4Proof.u32_eq(a, b, Ext4Proof.and_l(U32.is_eq(a, b), B.list_eq(s, t), h))) : {Con{_, s} == Con{b, t} : List<&2, U32>}
        %Equal.sym(List<&2, U32>, s, t, Ext4Proof.list_eq(s, t, Ext4Proof.and_r(U32.is_eq(a, b), B.list_eq(s, t), h))) : {Con{b, _} == Con{b, t} : List<&2, U32>}
        {==}

def Ext4Proof.escape_rt(b: Bool, +d: B.Octets) -> {JB.Jbd2.needs_escape(d) == b : Bool} -> {JB.Jbd2.unescape(b, JB.Jbd2.escape.pick(b, d)) == d : B.Octets}:
  match b:
    case False{}:
      +e => {==}
    case True{}:
      +e =>
        +x = B.Octets.drop(4n, d)
        +k = B.Octets.take(4n, d)
        +m = B.be32(J.Jbd2.magic())
        +tl = Ext4Proof.list_eq(B.Octets.to_list(k), m, e)
        +tk = Equal.trans(B.Octets, k, B.Octets.of_list(B.Octets.to_list(k)), B.Octets.of_list(m), Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(k)), k, BL.octets_of_to(k)), Equal.cong(List<&2, U32>, B.Octets, xs => B.Octets.of_list(xs), B.Octets.to_list(k), m, tl))
        %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(B.Octets.zeros(4n)), B.Octets.append(B.Octets.zeros(4n), x)), x, BL.octets_drop_append(B.Octets.zeros(4n), x)) : {B.Octets.append(B.Octets.be32(J.Jbd2.magic()), _) == d : B.Octets}
        %tk : {B.Octets.append(_, x) == d : B.Octets}
        BL.octets_take_drop(4n, d)

def Laws.escape_round_trip(d):
  Ext4Proof.escape_rt(JB.Jbd2.needs_escape(d), d, {==})

# Vectors

def Laws.hash_legacy():
  {==}

def Laws.hash_legacy_signed():
  {==}

def Laws.hash_legacy_unsigned():
  {==}

def Laws.hash_half_md4():
  {==}

def Laws.hash_half_md4_signed():
  {==}

def Laws.hash_half_md4_unsigned():
  {==}

def Laws.hash_half_md4_long():
  {==}

def Laws.hash_half_md4_seed():
  {==}

def Laws.hash_tea():
  {==}

def Laws.hash_tea_signed():
  {==}

def Laws.hash_tea_unsigned():
  {==}

def Laws.hash_tea_long():
  {==}

def Laws.hash_version_unsigned():
  {==}

def Laws.hash_bad_version():
  {==}

def Laws.xattr_entry_hash():
  {==}

def Laws.xattr_inode_hash():
  {==}

# Witnesses and vectors

def Laws.htree_lookup_scan_witness():
  {==}

def Laws.htree_writer_lookup_witness():
  {==}

def Laws.scan_incomplete_witness():
  {==}

def Laws.replay_idempotent_witness():
  {==}

def Laws.htree_lookup_vector():
  {==}

def Laws.htree_lookup_missing():
  {==}

def Laws.commit_replays_vector():
  {==}
