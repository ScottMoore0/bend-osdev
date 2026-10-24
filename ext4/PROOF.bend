import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../ext2/csum.bend as K
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
import ./overlay.bend as OV
import ./jtx.bend as JT
import ./jscan.bend as JN
import ./super.bend as S
import ../ext2/super.bend as XS
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

# Journalled writes: the journalling device (overlay.bend) on a MemDev

# one good write through the overlay keeps it
def Ext4Proof.ov_write_one(+d: D.MemDev, +acc: List<&2, JW.Jbd2Write>, +n: Nat, +data: B.Octets) -> {Nat.is_eq(B.Octets.len(data), D.MemDev.block_size(d)) == True{} : Bool} -> {DW.Ext4Dev.write(~OV.Ext4Ov<D.MemDev>, ~OV.Ext4Ov.mem_block_size, ~OV.Ext4Ov.mem_write, OV.Ext4Ov{d, acc}, D.MemDev.block_size(d), n, data) == Done{OV.Ext4Ov{d, Con{JW.Jbd2Write{n, data}, acc}}} : Result<&2, &2, E.Ext4Error, OV.Ext4Ov<D.MemDev>>}:
  +hl =>
    +bs = D.MemDev.block_size(d)
    +o = {OV.Ext4Ov{d, acc} : OV.Ext4Ov<D.MemDev>}
    +r = {Done{OV.Ext4Ov{d, Con{JW.Jbd2Write{n, data}, acc}}} : Result<&2, &2, E.Ext4Error, OV.Ext4Ov<D.MemDev>>}
    %Equal.sym(Bool, Nat.is_eq(bs, bs), True{}, Ext4Proof.eq_refl(bs)) : {DW.Ext4Dev.write.go(~OV.Ext4Ov<D.MemDev>, ~OV.Ext4Ov.mem_write, _, Bool.and(Nat.is_lt(0n, bs), Nat.is_eq(Nat.mod(bs, bs), 0n)), o, bs, bs, n, data) == r : Result<&2, &2, E.Ext4Error, OV.Ext4Ov<D.MemDev>>}
    %Equal.sym(Bool, Nat.is_eq(B.Octets.len(data), bs), True{}, hl) : {DW.Ext4Dev.lift(OV.Ext4Ov<D.MemDev>, OV.Ext4Ov.write.check(D.MemDev, _, d, acc, n, data, bs)) == r : Result<&2, &2, E.Ext4Error, OV.Ext4Ov<D.MemDev>>}
    {==}

# good writes through the overlay are kept, last first
def Ext4Proof.ov_write_all(ws: List<&2, JW.Jbd2Write>, +d: D.MemDev, +acc: List<&2, JW.Jbd2Write>) -> {DW.Ext4Dev.fits(D.MemDev.block_size(d), D.MemDev.block_count(d), ws) == True{} : Bool} -> {DW.Ext4Dev.write_all(~OV.Ext4Ov<D.MemDev>, ~OV.Ext4Ov.mem_block_size, ~OV.Ext4Ov.mem_write, ws, Done{OV.Ext4Ov{d, acc}}, D.MemDev.block_size(d)) == Done{OV.Ext4Ov{d, JL.Jbd2Log.rev_onto(JW.Jbd2Write, ws, acc)}} : Result<&2, &2, E.Ext4Error, OV.Ext4Ov<D.MemDev>>}:
  match ws:
    case Nil{}:
      +hf => {==}
    case Con{JW.Jbd2Write{+n, +data}, +t}:
      +hf =>
        +bs = D.MemDev.block_size(d)
        +cnt = D.MemDev.block_count(d)
        +a = Bool.and(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, cnt))
        +ha = Ext4Proof.and_l(a, DW.Ext4Dev.fits(bs, cnt, t), hf)
        +hl = Ext4Proof.and_l(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, cnt), ha)
        +acc2 = {Con{JW.Jbd2Write{n, data}, acc} : List<&2, JW.Jbd2Write>}
        %Equal.sym(Result<&2, &2, E.Ext4Error, OV.Ext4Ov<D.MemDev>>, DW.Ext4Dev.write(~OV.Ext4Ov<D.MemDev>, ~OV.Ext4Ov.mem_block_size, ~OV.Ext4Ov.mem_write, OV.Ext4Ov{d, acc}, bs, n, data), Done{OV.Ext4Ov{d, acc2}}, Ext4Proof.ov_write_one(d, acc, n, data, hl)) : {DW.Ext4Dev.write_all(~OV.Ext4Ov<D.MemDev>, ~OV.Ext4Ov.mem_block_size, ~OV.Ext4Ov.mem_write, t, _, bs) == Done{OV.Ext4Ov{d, JL.Jbd2Log.rev_onto(JW.Jbd2Write, t, acc2)}} : Result<&2, &2, E.Ext4Error, OV.Ext4Ov<D.MemDev>>}
        Ext4Proof.ov_write_all(t, d, acc2, Ext4Proof.and_r(a, DW.Ext4Dev.fits(bs, cnt, t), hf))

# the overlay's search, one write further on
def Ext4Proof.find_step(b: Bool, acc: List<&2, JW.Jbd2Write>, +m: Nat, +data: B.Octets) -> {OV.Ext4Ov.find(acc, m, OV.Ext4Ov.find.pick(b, data)) == Ext4Proof.fl.pick(b, data, OV.Ext4Ov.find(acc, m, None{})) : Maybe<&2, B.Octets>}:
  match b acc:
    case True{} Nil{}:
      {==}
    case True{} Con{JW.Jbd2Write{b2, d2}, t}:
      {==}
    case False{} _:
      {==}

# searching the writes kept last first finds the last write
def Ext4Proof.find_rev(ws: List<&2, JW.Jbd2Write>, +m: Nat, +acc: List<&2, JW.Jbd2Write>) -> {OV.Ext4Ov.find(JL.Jbd2Log.rev_onto(JW.Jbd2Write, ws, acc), m, None{}) == Ext4Proof.fl(ws, m, OV.Ext4Ov.find(acc, m, None{})) : Maybe<&2, B.Octets>}:
  match ws:
    case Nil{}:
      {==}
    case Con{JW.Jbd2Write{+n, +data}, +t}:
      +acc2 = {Con{JW.Jbd2Write{n, data}, acc} : List<&2, JW.Jbd2Write>}
      Equal.trans(Maybe<&2, B.Octets>, OV.Ext4Ov.find(JL.Jbd2Log.rev_onto(JW.Jbd2Write, t, acc2), m, None{}), Ext4Proof.fl(t, m, OV.Ext4Ov.find(acc2, m, None{})), Ext4Proof.fl(t, m, Ext4Proof.fl.pick(Nat.is_eq(n, m), data, OV.Ext4Ov.find(acc, m, None{}))), Ext4Proof.find_rev(t, m, acc2), Equal.cong(Maybe<&2, B.Octets>, Maybe<&2, B.Octets>, x => Ext4Proof.fl(t, m, x), OV.Ext4Ov.find(acc2, m, None{}), Ext4Proof.fl.pick(Nat.is_eq(n, m), data, OV.Ext4Ov.find(acc, m, None{})), Ext4Proof.find_step(Nat.is_eq(n, m), acc, m, data)))

def Ext4Proof.got_lp(mm: Maybe<&2, B.Octets>, +d: D.MemDev, +m: Nat) -> {OV.Ext4Ov.read.got(~D.MemDev, ~D.MemDev.read_block, mm, d, m) == Ext4Proof.lp(mm, D.MemDev.read_block(d, m)) : Result<&2, &2, D.DevError, B.Octets>}:
  match mm:
    case Some{v}:
      {==}
    case None{}:
      {==}

# reading the overlay after good writes: the last write, else the device
def Ext4Proof.ov_read(+ws: List<&2, JW.Jbd2Write>, +d: D.MemDev, +m: Nat) -> {OV.Ext4Ov.mem_read(OV.Ext4Ov{d, JL.Jbd2Log.rev_onto(JW.Jbd2Write, ws, Nil{})}, m) == Ext4Proof.last(ws, m, D.MemDev.read_block(d, m)) : Result<&2, &2, D.DevError, B.Octets>}:
  +x = D.MemDev.read_block(d, m)
  +f = Ext4Proof.fl(ws, m, None{})
  +e1 = Equal.cong(Maybe<&2, B.Octets>, Result<&2, &2, D.DevError, B.Octets>, y => OV.Ext4Ov.read.got(~D.MemDev, ~D.MemDev.read_block, y, d, m), OV.Ext4Ov.find(JL.Jbd2Log.rev_onto(JW.Jbd2Write, ws, Nil{}), m, None{}), f, Ext4Proof.find_rev(ws, m, Nil{}))
  Equal.trans(Result<&2, &2, D.DevError, B.Octets>, OV.Ext4Ov.read.got(~D.MemDev, ~D.MemDev.read_block, OV.Ext4Ov.find(JL.Jbd2Log.rev_onto(JW.Jbd2Write, ws, Nil{}), m, None{}), d, m), OV.Ext4Ov.read.got(~D.MemDev, ~D.MemDev.read_block, f, d, m), Ext4Proof.last(ws, m, x), e1, Equal.trans(Result<&2, &2, D.DevError, B.Octets>, OV.Ext4Ov.read.got(~D.MemDev, ~D.MemDev.read_block, f, d, m), Ext4Proof.lp(f, x), Ext4Proof.last(ws, m, x), Ext4Proof.got_lp(f, d, m), Equal.sym(Result<&2, &2, D.DevError, B.Octets>, Ext4Proof.last(ws, m, x), Ext4Proof.lp(f, x), Ext4Proof.last_fl(ws, m, None{}, x))))

# the device written directly, read: the last write, else the device
def Ext4Proof.direct_read(+d: D.MemDev, +ws: List<&2, JW.Jbd2Write>, +m: Nat, +ok: {DW.Ext4Dev.fits(D.MemDev.block_size(d), D.MemDev.block_count(d), ws) == True{} : Bool}) -> {DW.Ext4Dev.read_mem(Laws.Ext4Laws.direct(d, ws), m) == DW.Ext4Dev.dev_read(Ext4Proof.last(ws, m, D.MemDev.read_block(d, m))) : Result<&2, &2, E.Ext4Error, B.Octets>}:
  +bs = D.MemDev.block_size(d)
  +cnt = D.MemDev.block_count(d)
  %Equal.sym(Result<&2, &2, E.Ext4Error, D.MemDev>, DW.Ext4Dev.write_all(~D.MemDev, ~D.MemDev.block_size, ~DW.Ext4Dev.mem_write, ws, Done{d}, bs), Done{Ext4Proof.updates(ws, d)}, Ext4Proof.write_all(ws, d, bs, cnt, {==}, {==}, ok)) : {DW.Ext4Dev.read_mem(_, m) == DW.Ext4Dev.dev_read(Ext4Proof.last(ws, m, D.MemDev.read_block(d, m))) : Result<&2, &2, E.Ext4Error, B.Octets>}
  Equal.cong(Result<&2, &2, D.DevError, B.Octets>, Result<&2, &2, E.Ext4Error, B.Octets>, x => DW.Ext4Dev.dev_read(x), D.MemDev.read_block(Ext4Proof.updates(ws, d), m), Ext4Proof.last(ws, m, D.MemDev.read_block(d, m)), Ext4Proof.reads(ws, d, m, bs, cnt, {==}, {==}, ok))

def Laws.ov_reads(d, ws, m, ok):
  +r = JL.Jbd2Log.rev_onto(JW.Jbd2Write, ws, Nil{})
  %Equal.sym(Result<&2, &2, E.Ext4Error, OV.Ext4Ov<D.MemDev>>, Laws.Ext4Laws.ov(d, ws), Done{OV.Ext4Ov{d, r}}, Ext4Proof.ov_write_all(ws, d, Nil{}, ok)) : {OV.Ext4Ov.read_mem(_, m) == DW.Ext4Dev.read_mem(Laws.Ext4Laws.direct(d, ws), m) : Result<&2, &2, E.Ext4Error, B.Octets>}
  Equal.trans(Result<&2, &2, E.Ext4Error, B.Octets>, DW.Ext4Dev.dev_read(OV.Ext4Ov.mem_read(OV.Ext4Ov{d, r}, m)), DW.Ext4Dev.dev_read(Ext4Proof.last(ws, m, D.MemDev.read_block(d, m))), DW.Ext4Dev.read_mem(Laws.Ext4Laws.direct(d, ws), m), Equal.cong(Result<&2, &2, D.DevError, B.Octets>, Result<&2, &2, E.Ext4Error, B.Octets>, x => DW.Ext4Dev.dev_read(x), OV.Ext4Ov.mem_read(OV.Ext4Ov{d, r}, m), Ext4Proof.last(ws, m, D.MemDev.read_block(d, m)), Ext4Proof.ov_read(ws, d, m)), Equal.sym(Result<&2, &2, E.Ext4Error, B.Octets>, DW.Ext4Dev.read_mem(Laws.Ext4Laws.direct(d, ws), m), DW.Ext4Dev.dev_read(Ext4Proof.last(ws, m, D.MemDev.read_block(d, m))), Ext4Proof.direct_read(d, ws, m, ok)))

# The overlay's kept writes (each block once, its last contents), written
# home: reading them gives the last write of every block

def Ext4Proof.or_l_false(+a: Bool, +b: Bool) -> {Bool.or(a, b) == False{} : Bool} -> {a == False{} : Bool}:
  match a:
    case True{}:
      +h => h
    case False{}:
      +h => {==}

def Ext4Proof.or_r_false(+a: Bool, +b: Bool) -> {Bool.or(a, b) == False{} : Bool} -> {b == False{} : Bool}:
  match a:
    case True{}:
      +h => Ext4Proof.no({b == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case False{}:
      +h => h

# whether some write of ws is to block m
def Ext4Proof.inb(ws: List<&2, JW.Jbd2Write>, +m: Nat) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{JW.Jbd2Write{b, d}, t}:
      Bool.or(Nat.is_eq(b, m), Ext4Proof.inb(t, m))

# the dedup walk's invariant at m: m was seen, or acc holds no write to it
def Ext4Proof.inv(+seen: List<&2, Nat>, +acc: List<&2, JW.Jbd2Write>, +m: Nat) -> Bool:
  Bool.or(OV.Ext4Ov.seen(seen, m), Bool.not(Ext4Proof.inb(acc, m)))

def Ext4Proof.not_t(+a: Bool) -> {Bool.not(a) == True{} : Bool} -> {a == False{} : Bool}:
  match a:
    case True{}:
      +h => Equal.sym(Bool, False{}, True{}, h)
    case False{}:
      +h => {==}

def Ext4Proof.inv_use(+seen: List<&2, Nat>, +acc: List<&2, JW.Jbd2Write>, +m: Nat) -> {Ext4Proof.inv(seen, acc, m) == True{} : Bool} -> {OV.Ext4Ov.seen(seen, m) == False{} : Bool} -> {Ext4Proof.inb(acc, m) == False{} : Bool}:
  +hi => +hs =>
    +h2 = {Equal.trans(Bool, Bool.not(Ext4Proof.inb(acc, m)), Bool.or(OV.Ext4Ov.seen(seen, m), Bool.not(Ext4Proof.inb(acc, m))), True{}, Equal.cong(Bool, Bool, y => Bool.or(y, Bool.not(Ext4Proof.inb(acc, m))), False{}, OV.Ext4Ov.seen(seen, m), Equal.sym(Bool, OV.Ext4Ov.seen(seen, m), False{}, hs)), hi) : {Bool.not(Ext4Proof.inb(acc, m)) == True{} : Bool}}
    Ext4Proof.not_t(Ext4Proof.inb(acc, m), h2)

# writes none of which is to m leave m's read as it was
def Ext4Proof.last_none(ws: List<&2, JW.Jbd2Write>, +m: Nat, +y: Result<&2, &2, D.DevError, B.Octets>) -> {Ext4Proof.inb(ws, m) == False{} : Bool} -> {Ext4Proof.last(ws, m, y) == y : Result<&2, &2, D.DevError, B.Octets>}:
  match ws:
    case Nil{}:
      +h => {==}
    case Con{JW.Jbd2Write{+b, +data}, +t}:
      +h =>
        +e = Ext4Proof.or_l_false(Nat.is_eq(b, m), Ext4Proof.inb(t, m), h)
        %Equal.sym(Bool, Nat.is_eq(b, m), False{}, e) : {Ext4Proof.last(t, m, Ext4Proof.last.pick(_, data, y)) == y : Result<&2, &2, D.DevError, B.Octets>}
        Ext4Proof.last_none(t, m, y, Ext4Proof.or_r_false(Nat.is_eq(b, m), Ext4Proof.inb(t, m), h))

def Ext4Proof.seen_ne.at(c: Bool, +x: Nat, +t: List<&2, Nat>, +b: Nat, +m: Nat, ih: {OV.Ext4Ov.seen(t, b) == True{} : Bool} -> {OV.Ext4Ov.seen(t, m) == False{} : Bool} -> {Nat.is_eq(b, m) == False{} : Bool}) -> {Nat.is_eq(x, b) == c : Bool} -> {Bool.or(c, OV.Ext4Ov.seen(t, b)) == True{} : Bool} -> {Nat.is_eq(x, m) == False{} : Bool} -> {OV.Ext4Ov.seen(t, m) == False{} : Bool} -> {Nat.is_eq(b, m) == False{} : Bool}:
  match c:
    case True{}:
      +hc => +h1 => +hx => +ht =>
        %Ext4Proof.eq_sound(x, b, hc) : {Nat.is_eq(_, m) == False{} : Bool}
        hx
    case False{}:
      +hc => +h1 => +hx => +ht => ih(h1, ht)

# a block seen and a block not seen differ
def Ext4Proof.seen_ne(xs: List<&2, Nat>, +b: Nat, +m: Nat) -> {OV.Ext4Ov.seen(xs, b) == True{} : Bool} -> {OV.Ext4Ov.seen(xs, m) == False{} : Bool} -> {Nat.is_eq(b, m) == False{} : Bool}:
  match xs:
    case Nil{}:
      +h1 => +h2 => Ext4Proof.no({Nat.is_eq(b, m) == False{} : Bool}, h1)
    case Con{+x, +t}:
      +h1 => +h2 =>
        +hx = Ext4Proof.or_l_false(Nat.is_eq(x, m), OV.Ext4Ov.seen(t, m), h2)
        +ht = Ext4Proof.or_r_false(Nat.is_eq(x, m), OV.Ext4Ov.seen(t, m), h2)
        Ext4Proof.seen_ne.at(Nat.is_eq(x, b), x, t, b, m, p => q => Ext4Proof.seen_ne(t, b, m, p, q), {==}, h1, hx, ht)

def Ext4Proof.find_some(ws: List<&2, JW.Jbd2Write>, +m: Nat, +v: B.Octets) -> {OV.Ext4Ov.find(ws, m, Some{v}) == Some{v} : Maybe<&2, B.Octets>}:
  match ws:
    case Nil{}:
      {==}
    case Con{JW.Jbd2Write{b, d}, t}:
      {==}

# what reading after the deduplicated writes gives: sm says whether m was
# seen already (then acc holds its write, if any), else the first write to
# m in l (the newest), if any
def Ext4Proof.dr(sm: Bool, +l: List<&2, JW.Jbd2Write>, +acc: List<&2, JW.Jbd2Write>, +m: Nat, +x: Result<&2, &2, D.DevError, B.Octets>) -> Result<&2, &2, D.DevError, B.Octets>:
  match sm:
    case True{}:
      Ext4Proof.last(acc, m, x)
    case False{}:
      Ext4Proof.lp(OV.Ext4Ov.find(l, m, None{}), x)

# a seen block's write skipped
def Ext4Proof.dr_skip(sm: Bool, +b: Nat, +data: B.Octets, +t: List<&2, JW.Jbd2Write>, +seen: List<&2, Nat>, +acc: List<&2, JW.Jbd2Write>, +m: Nat, +x: Result<&2, &2, D.DevError, B.Octets>) -> {OV.Ext4Ov.seen(seen, b) == True{} : Bool} -> {OV.Ext4Ov.seen(seen, m) == sm : Bool} -> {Ext4Proof.dr(sm, t, acc, m, x) == Ext4Proof.dr(sm, Con{JW.Jbd2Write{b, data}, t}, acc, m, x) : Result<&2, &2, D.DevError, B.Octets>}:
  match sm:
    case True{}:
      +hd => +hs => {==}
    case False{}:
      +hd => +hs =>
        %Equal.sym(Bool, Nat.is_eq(b, m), False{}, Ext4Proof.seen_ne(seen, b, m, hd, hs)) : {Ext4Proof.lp(OV.Ext4Ov.find(t, m, None{}), x) == Ext4Proof.lp(OV.Ext4Ov.find(t, m, OV.Ext4Ov.find.pick(_, data)), x) : Result<&2, &2, D.DevError, B.Octets>}
        {==}

# a new block's write kept
def Ext4Proof.dr_keep(e: Bool, sm: Bool, +b: Nat, +data: B.Octets, +t: List<&2, JW.Jbd2Write>, +seen: List<&2, Nat>, +acc: List<&2, JW.Jbd2Write>, +m: Nat, +x: Result<&2, &2, D.DevError, B.Octets>) -> {Nat.is_eq(b, m) == e : Bool} -> {OV.Ext4Ov.seen(seen, b) == False{} : Bool} -> {OV.Ext4Ov.seen(seen, m) == sm : Bool} -> {Ext4Proof.inv(seen, acc, m) == True{} : Bool} -> {Ext4Proof.dr(Bool.or(e, sm), t, Con{JW.Jbd2Write{b, data}, acc}, m, x) == Ext4Proof.dr(sm, Con{JW.Jbd2Write{b, data}, t}, acc, m, x) : Result<&2, &2, D.DevError, B.Octets>}:
  match e sm:
    case True{} True{}:
      +he => +hb => +hs => +hi =>
        +bad = {Equal.trans(Bool, False{}, OV.Ext4Ov.seen(seen, b), True{}, Equal.sym(Bool, OV.Ext4Ov.seen(seen, b), False{}, hb), Equal.trans(Bool, OV.Ext4Ov.seen(seen, b), OV.Ext4Ov.seen(seen, m), True{}, Equal.cong(Nat, Bool, k => OV.Ext4Ov.seen(seen, k), b, m, Ext4Proof.eq_sound(b, m, he)), hs)) : {False{} == True{} : Bool}}
        Ext4Proof.no({Ext4Proof.dr(True{}, t, Con{JW.Jbd2Write{b, data}, acc}, m, x) == Ext4Proof.dr(True{}, Con{JW.Jbd2Write{b, data}, t}, acc, m, x) : Result<&2, &2, D.DevError, B.Octets>}, bad)
    case True{} False{}:
      +he => +hb => +hs => +hi =>
        %Equal.sym(Bool, Nat.is_eq(b, m), True{}, he) : {Ext4Proof.last(acc, m, Ext4Proof.last.pick(_, data, x)) == Ext4Proof.lp(OV.Ext4Ov.find(t, m, OV.Ext4Ov.find.pick(_, data)), x) : Result<&2, &2, D.DevError, B.Octets>}
        %Equal.sym(Maybe<&2, B.Octets>, OV.Ext4Ov.find(t, m, Some{data}), Some{data}, Ext4Proof.find_some(t, m, data)) : {Ext4Proof.last(acc, m, Done{data}) == Ext4Proof.lp(_, x) : Result<&2, &2, D.DevError, B.Octets>}
        Ext4Proof.last_none(acc, m, Done{data}, Ext4Proof.inv_use(seen, acc, m, hi, hs))
    case False{} True{}:
      +he => +hb => +hs => +hi =>
        %Equal.sym(Bool, Nat.is_eq(b, m), False{}, he) : {Ext4Proof.last(acc, m, Ext4Proof.last.pick(_, data, x)) == Ext4Proof.last(acc, m, x) : Result<&2, &2, D.DevError, B.Octets>}
        {==}
    case False{} False{}:
      +he => +hb => +hs => +hi =>
        %Equal.sym(Bool, Nat.is_eq(b, m), False{}, he) : {Ext4Proof.lp(OV.Ext4Ov.find(t, m, None{}), x) == Ext4Proof.lp(OV.Ext4Ov.find(t, m, OV.Ext4Ov.find.pick(_, data)), x) : Result<&2, &2, D.DevError, B.Octets>}
        {==}

# the new state's invariant, when a write to a block not seen is kept
def Ext4Proof.inv_keep(e: Bool, +b: Nat, +data: B.Octets, +seen: List<&2, Nat>, +acc: List<&2, JW.Jbd2Write>, +m: Nat) -> {Nat.is_eq(b, m) == e : Bool} -> {Ext4Proof.inv(seen, acc, m) == True{} : Bool} -> {Ext4Proof.inv(Con{b, seen}, Con{JW.Jbd2Write{b, data}, acc}, m) == True{} : Bool}:
  match e:
    case True{}:
      +he => +hi =>
        %Equal.sym(Bool, Nat.is_eq(b, m), True{}, he) : {Bool.or(Bool.or(_, OV.Ext4Ov.seen(seen, m)), Bool.not(Bool.or(_, Ext4Proof.inb(acc, m)))) == True{} : Bool}
        {==}
    case False{}:
      +he => +hi =>
        %Equal.sym(Bool, Nat.is_eq(b, m), False{}, he) : {Bool.or(Bool.or(_, OV.Ext4Ov.seen(seen, m)), Bool.not(Bool.or(_, Ext4Proof.inb(acc, m)))) == True{} : Bool}
        hi

def Ext4Proof.dedup_nil(sm: Bool, +seen: List<&2, Nat>, +acc: List<&2, JW.Jbd2Write>, +m: Nat, +x: Result<&2, &2, D.DevError, B.Octets>) -> {OV.Ext4Ov.seen(seen, m) == sm : Bool} -> {Ext4Proof.inv(seen, acc, m) == True{} : Bool} -> {Ext4Proof.last(acc, m, x) == Ext4Proof.dr(sm, Nil{}, acc, m, x) : Result<&2, &2, D.DevError, B.Octets>}:
  match sm:
    case True{}:
      +hs => +hi => {==}
    case False{}:
      +hs => +hi => Ext4Proof.last_none(acc, m, x, Ext4Proof.inv_use(seen, acc, m, hi, hs))

def Ext4Proof.dedup_read.at(dup: Bool, +b: Nat, +data: B.Octets, +t: List<&2, JW.Jbd2Write>, +seen: List<&2, Nat>, +acc: List<&2, JW.Jbd2Write>, +m: Nat, +x: Result<&2, &2, D.DevError, B.Octets>, +sm: Bool, ih: @s2: List<&2, Nat> -> @a2: List<&2, JW.Jbd2Write> -> @sm2: Bool -> {OV.Ext4Ov.seen(s2, m) == sm2 : Bool} -> {Ext4Proof.inv(s2, a2, m) == True{} : Bool} -> {Ext4Proof.last(OV.Ext4Ov.dedup(t, (s2, a2)), m, x) == Ext4Proof.dr(sm2, t, a2, m, x) : Result<&2, &2, D.DevError, B.Octets>}) -> {OV.Ext4Ov.seen(seen, b) == dup : Bool} -> {OV.Ext4Ov.seen(seen, m) == sm : Bool} -> {Ext4Proof.inv(seen, acc, m) == True{} : Bool} -> {Ext4Proof.last(OV.Ext4Ov.dedup(t, OV.Ext4Ov.keep(dup, JW.Jbd2Write{b, data}, b, seen, acc)), m, x) == Ext4Proof.dr(sm, Con{JW.Jbd2Write{b, data}, t}, acc, m, x) : Result<&2, &2, D.DevError, B.Octets>}:
  match dup:
    case True{}:
      +hd => +hs => +hi =>
        Equal.trans(Result<&2, &2, D.DevError, B.Octets>, Ext4Proof.last(OV.Ext4Ov.dedup(t, (seen, acc)), m, x), Ext4Proof.dr(sm, t, acc, m, x), Ext4Proof.dr(sm, Con{JW.Jbd2Write{b, data}, t}, acc, m, x), ih(seen, acc, sm, hs, hi), Ext4Proof.dr_skip(sm, b, data, t, seen, acc, m, x, hd, hs))
    case False{}:
      +hd => +hs => +hi =>
        +w = {JW.Jbd2Write{b, data} : JW.Jbd2Write}
        +sm2 = Bool.or(Nat.is_eq(b, m), sm)
        +hs2 = {Equal.cong(Bool, Bool, y => Bool.or(Nat.is_eq(b, m), y), OV.Ext4Ov.seen(seen, m), sm, hs) : {OV.Ext4Ov.seen(Con{b, seen}, m) == sm2 : Bool}}
        Equal.trans(Result<&2, &2, D.DevError, B.Octets>, Ext4Proof.last(OV.Ext4Ov.dedup(t, (Con{b, seen}, Con{w, acc})), m, x), Ext4Proof.dr(sm2, t, Con{w, acc}, m, x), Ext4Proof.dr(sm, Con{w, t}, acc, m, x), ih(Con{b, seen}, Con{w, acc}, sm2, hs2, Ext4Proof.inv_keep(Nat.is_eq(b, m), b, data, seen, acc, m, {==}, hi)), Ext4Proof.dr_keep(Nat.is_eq(b, m), sm, b, data, t, seen, acc, m, x, {==}, hd, hs, hi))

def Ext4Proof.dedup_read(l: List<&2, JW.Jbd2Write>, +seen: List<&2, Nat>, +acc: List<&2, JW.Jbd2Write>, +m: Nat, +x: Result<&2, &2, D.DevError, B.Octets>, +sm: Bool) -> {OV.Ext4Ov.seen(seen, m) == sm : Bool} -> {Ext4Proof.inv(seen, acc, m) == True{} : Bool} -> {Ext4Proof.last(OV.Ext4Ov.dedup(l, (seen, acc)), m, x) == Ext4Proof.dr(sm, l, acc, m, x) : Result<&2, &2, D.DevError, B.Octets>}:
  match l:
    case Nil{}:
      +hs => +hi => Ext4Proof.dedup_nil(sm, seen, acc, m, x, hs, hi)
    case Con{JW.Jbd2Write{+b, +data}, +t}:
      +hs => +hi => Ext4Proof.dedup_read.at(OV.Ext4Ov.seen(seen, b), b, data, t, seen, acc, m, x, sm, s2 => a2 => sm2 => p => q => Ext4Proof.dedup_read(t, s2, a2, m, x, sm2, p, q), {==}, hs, hi)

# the kept writes fit the device as the writes did
def Ext4Proof.fits_rev(ws: List<&2, JW.Jbd2Write>, +bs: Nat, +cnt: Nat, +acc: List<&2, JW.Jbd2Write>) -> {DW.Ext4Dev.fits(bs, cnt, ws) == True{} : Bool} -> {DW.Ext4Dev.fits(bs, cnt, acc) == True{} : Bool} -> {DW.Ext4Dev.fits(bs, cnt, JL.Jbd2Log.rev_onto(JW.Jbd2Write, ws, acc)) == True{} : Bool}:
  match ws:
    case Nil{}:
      +hw => +ha => ha
    case Con{JW.Jbd2Write{+n, +data}, +t}:
      +hw => +ha =>
        +a = Bool.and(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, cnt))
        Ext4Proof.fits_rev(t, bs, cnt, Con{JW.Jbd2Write{n, data}, acc}, Ext4Proof.and_r(a, DW.Ext4Dev.fits(bs, cnt, t), hw), Ext4Proof.and_i(a, DW.Ext4Dev.fits(bs, cnt, acc), Ext4Proof.and_l(a, DW.Ext4Dev.fits(bs, cnt, t), hw), ha))

def Ext4Proof.fits_dedup.at(dup: Bool, +n: Nat, +data: B.Octets, +t: List<&2, JW.Jbd2Write>, +seen: List<&2, Nat>, +acc: List<&2, JW.Jbd2Write>, +bs: Nat, +cnt: Nat, ih: @s2: List<&2, Nat> -> @a2: List<&2, JW.Jbd2Write> -> {DW.Ext4Dev.fits(bs, cnt, a2) == True{} : Bool} -> {DW.Ext4Dev.fits(bs, cnt, OV.Ext4Ov.dedup(t, (s2, a2))) == True{} : Bool}) -> {Bool.and(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, cnt)) == True{} : Bool} -> {DW.Ext4Dev.fits(bs, cnt, acc) == True{} : Bool} -> {DW.Ext4Dev.fits(bs, cnt, OV.Ext4Ov.dedup(t, OV.Ext4Ov.keep(dup, JW.Jbd2Write{n, data}, n, seen, acc))) == True{} : Bool}:
  match dup:
    case True{}:
      +hw => +ha => ih(seen, acc, ha)
    case False{}:
      +hw => +ha => ih(Con{n, seen}, Con{JW.Jbd2Write{n, data}, acc}, Ext4Proof.and_i(Bool.and(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, cnt)), DW.Ext4Dev.fits(bs, cnt, acc), hw, ha))

def Ext4Proof.fits_dedup(l: List<&2, JW.Jbd2Write>, +bs: Nat, +cnt: Nat, +seen: List<&2, Nat>, +acc: List<&2, JW.Jbd2Write>) -> {DW.Ext4Dev.fits(bs, cnt, l) == True{} : Bool} -> {DW.Ext4Dev.fits(bs, cnt, acc) == True{} : Bool} -> {DW.Ext4Dev.fits(bs, cnt, OV.Ext4Ov.dedup(l, (seen, acc))) == True{} : Bool}:
  match l:
    case Nil{}:
      +hl => +ha => ha
    case Con{JW.Jbd2Write{+n, +data}, +t}:
      +hl => +ha =>
        +a = Bool.and(Nat.is_eq(B.Octets.len(data), bs), Nat.is_lt(n, cnt))
        +ht = Ext4Proof.and_r(a, DW.Ext4Dev.fits(bs, cnt, t), hl)
        Ext4Proof.fits_dedup.at(OV.Ext4Ov.seen(seen, n), n, data, t, seen, acc, bs, cnt, s2 => a2 => q => Ext4Proof.fits_dedup(t, bs, cnt, s2, a2, ht, q), Ext4Proof.and_l(a, DW.Ext4Dev.fits(bs, cnt, t), hl), ha)

def Laws.ov_flush(d, ws, m, ok):
  +bs = D.MemDev.block_size(d)
  +cnt = D.MemDev.block_count(d)
  +r = JL.Jbd2Log.rev_onto(JW.Jbd2Write, ws, Nil{})
  +dd = OV.Ext4Ov.dedup(r, (Nil{}, Nil{}))
  +x = D.MemDev.read_block(d, m)
  +fd = Ext4Proof.fits_dedup(r, bs, cnt, Nil{}, Nil{}, Ext4Proof.fits_rev(ws, bs, cnt, Nil{}, ok, {==}), {==})
  %Equal.sym(Result<&2, &2, E.Ext4Error, OV.Ext4Ov<D.MemDev>>, Laws.Ext4Laws.ov(d, ws), Done{OV.Ext4Ov{d, r}}, Ext4Proof.ov_write_all(ws, d, Nil{}, ok)) : {DW.Ext4Dev.read_mem(OV.Ext4Ov.flush(~D.MemDev, ~D.MemDev.block_size, ~DW.Ext4Dev.mem_write, _), m) == DW.Ext4Dev.read_mem(Laws.Ext4Laws.direct(d, ws), m) : Result<&2, &2, E.Ext4Error, B.Octets>}
  %Equal.sym(Result<&2, &2, E.Ext4Error, D.MemDev>, DW.Ext4Dev.write_all(~D.MemDev, ~D.MemDev.block_size, ~DW.Ext4Dev.mem_write, dd, Done{d}, bs), Done{Ext4Proof.updates(dd, d)}, Ext4Proof.write_all(dd, d, bs, cnt, {==}, {==}, fd)) : {DW.Ext4Dev.read_mem(_, m) == DW.Ext4Dev.read_mem(Laws.Ext4Laws.direct(d, ws), m) : Result<&2, &2, E.Ext4Error, B.Octets>}
  +f = Ext4Proof.fl(ws, m, None{})
  +e1 = Ext4Proof.reads(dd, d, m, bs, cnt, {==}, {==}, fd)
  +e2 = Ext4Proof.dedup_read(r, Nil{}, Nil{}, m, x, False{}, {==}, {==})
  +e3 = Equal.cong(Maybe<&2, B.Octets>, Result<&2, &2, D.DevError, B.Octets>, y => Ext4Proof.lp(y, x), OV.Ext4Ov.find(r, m, None{}), f, Ext4Proof.find_rev(ws, m, Nil{}))
  +e4 = Equal.sym(Result<&2, &2, D.DevError, B.Octets>, Ext4Proof.last(ws, m, x), Ext4Proof.lp(f, x), Ext4Proof.last_fl(ws, m, None{}, x))
  +same = Equal.trans(Result<&2, &2, D.DevError, B.Octets>, D.MemDev.read_block(Ext4Proof.updates(dd, d), m), Ext4Proof.last(dd, m, x), Ext4Proof.last(ws, m, x), e1, Equal.trans(Result<&2, &2, D.DevError, B.Octets>, Ext4Proof.last(dd, m, x), Ext4Proof.lp(OV.Ext4Ov.find(r, m, None{}), x), Ext4Proof.last(ws, m, x), e2, Equal.trans(Result<&2, &2, D.DevError, B.Octets>, Ext4Proof.lp(OV.Ext4Ov.find(r, m, None{}), x), Ext4Proof.lp(f, x), Ext4Proof.last(ws, m, x), e3, e4)))
  Equal.trans(Result<&2, &2, E.Ext4Error, B.Octets>, DW.Ext4Dev.dev_read(D.MemDev.read_block(Ext4Proof.updates(dd, d), m)), DW.Ext4Dev.dev_read(Ext4Proof.last(ws, m, x)), DW.Ext4Dev.read_mem(Laws.Ext4Laws.direct(d, ws), m), Equal.cong(Result<&2, &2, D.DevError, B.Octets>, Result<&2, &2, E.Ext4Error, B.Octets>, y => DW.Ext4Dev.dev_read(y), D.MemDev.read_block(Ext4Proof.updates(dd, d), m), Ext4Proof.last(ws, m, x), same), Equal.sym(Result<&2, &2, E.Ext4Error, B.Octets>, DW.Ext4Dev.read_mem(Laws.Ext4Laws.direct(d, ws), m), DW.Ext4Dev.dev_read(Ext4Proof.last(ws, m, x)), Ext4Proof.direct_read(d, ws, m, ok)))

# Journalled writes: a transaction's plan (jtx.bend)

def Ext4Proof.cons_nil(-A: Data, +x: A, +t: List<&2, A>, h: {Con{x, t} == Nil{} : List<&2, A>}) -> Empty:
  Ext4Proof.clash(Equal.cong(List<&2, A>, Bool, l => List.is_empty(&2, A, l), Con{x, t}, Nil{}, h))

def Ext4Proof.take_zero(-A: Data, xs: List<&2, A>) -> {List.take(&2, A, xs, 0n) == Nil{} : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

def Ext4Proof.drop_zero(-A: Data, xs: List<&2, A>) -> {List.drop(&2, A, xs, 0n) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

def Ext4Proof.rev_onto_app(-A: Data, xs: List<&2, A>, +ys: List<&2, A>, +acc: List<&2, A>) -> {JL.Jbd2Log.rev_onto(A, List.append(&2, A, xs, ys), acc) == JL.Jbd2Log.rev_onto(A, ys, JL.Jbd2Log.rev_onto(A, xs, acc)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Ext4Proof.rev_onto_app(A, t, ys, Con{x, acc})

def Ext4Proof.app_nil2(-A: Data, +xs: List<&2, A>, +ys: List<&2, A>) -> {xs == Nil{} : List<&2, A>} -> {ys == Nil{} : List<&2, A>} -> {List.append(&2, A, xs, ys) == Nil{} : List<&2, A>}:
  +hx => +hy =>
    %Equal.sym(List<&2, A>, xs, Nil{}, hx) : {List.append(&2, A, _, ys) == Nil{} : List<&2, A>}
    hy

# k < 1 + l: k <= l
def Ext4Proof.lt_succ_le(+k: Nat, +l: Nat) -> {Nat.is_lt(k, 1n+l) == True{} : Bool} -> {Nat.is_le(k, l) == True{} : Bool}:
  match k l:
    case 0n _:
      +h => Ext4Proof.le_zero(l)
    case 1n+kp 0n:
      +h => Ext4Proof.no({Nat.is_le(1n+kp, 0n) == True{} : Bool}, Ext4Proof.lt_zero(kp, h))
    case 1n+kp 1n+lp:
      +h => Ext4Proof.lt_succ_le(kp, lp, h)

# Steps: what each reading answers of a join

def Ext4Proof.records_app(+s: Nat, xs: List<&2, JT.Ext4JStep>, +ys: List<&2, JT.Ext4JStep>) -> {JT.Ext4JTx.records(s, List.append(&2, JT.Ext4JStep, xs, ys)) == List.append(&2, JL.Jbd2Rec, JT.Ext4JTx.records(s, xs), JT.Ext4JTx.records(s, ys)) : List<&2, JL.Jbd2Rec>}:
  match xs:
    case Nil{}:
      {==}
    case Con{JT.Ext4JDesc{+p, +o, +ps}, +t}:
      Equal.cong(List<&2, JL.Jbd2Rec>, List<&2, JL.Jbd2Rec>, r => Con{JL.Jbd2RDesc{s, ps}, r}, JT.Ext4JTx.records(s, List.append(&2, JT.Ext4JStep, t, ys)), List.append(&2, JL.Jbd2Rec, JT.Ext4JTx.records(s, t), JT.Ext4JTx.records(s, ys)), Ext4Proof.records_app(s, t, ys))
    case Con{JT.Ext4JCommit{+p, +o}, +t}:
      Equal.cong(List<&2, JL.Jbd2Rec>, List<&2, JL.Jbd2Rec>, r => Con{JL.Jbd2RCommit{s}, r}, JT.Ext4JTx.records(s, List.append(&2, JT.Ext4JStep, t, ys)), List.append(&2, JL.Jbd2Rec, JT.Ext4JTx.records(s, t), JT.Ext4JTx.records(s, ys)), Ext4Proof.records_app(s, t, ys))
    case Con{JT.Ext4JHome{w}, +t}:
      Ext4Proof.records_app(s, t, ys)
    case Con{JT.Ext4JLog{p, o}, +t}:
      Ext4Proof.records_app(s, t, ys)
    case Con{JT.Ext4JData{p, u, o}, +t}:
      Ext4Proof.records_app(s, t, ys)
    case Con{JT.Ext4JFlag{a, b}, +t}:
      Ext4Proof.records_app(s, t, ys)

def Ext4Proof.dp_app(xs: List<&2, JT.Ext4JStep>, +ys: List<&2, JT.Ext4JStep>) -> {JT.Ext4JTx.data_puts(List.append(&2, JT.Ext4JStep, xs, ys)) == List.append(&2, JL.Jbd2Put, JT.Ext4JTx.data_puts(xs), JT.Ext4JTx.data_puts(ys)) : List<&2, JL.Jbd2Put>}:
  match xs:
    case Nil{}:
      {==}
    case Con{JT.Ext4JData{+p, +u, +o}, +t}:
      Equal.cong(List<&2, JL.Jbd2Put>, List<&2, JL.Jbd2Put>, r => Con{u, r}, JT.Ext4JTx.data_puts(List.append(&2, JT.Ext4JStep, t, ys)), List.append(&2, JL.Jbd2Put, JT.Ext4JTx.data_puts(t), JT.Ext4JTx.data_puts(ys)), Ext4Proof.dp_app(t, ys))
    case Con{JT.Ext4JHome{w}, +t}:
      Ext4Proof.dp_app(t, ys)
    case Con{JT.Ext4JLog{p, o}, +t}:
      Ext4Proof.dp_app(t, ys)
    case Con{JT.Ext4JDesc{p, o, ps}, +t}:
      Ext4Proof.dp_app(t, ys)
    case Con{JT.Ext4JCommit{p, o}, +t}:
      Ext4Proof.dp_app(t, ys)
    case Con{JT.Ext4JFlag{a, b}, +t}:
      Ext4Proof.dp_app(t, ys)

def Ext4Proof.rw_app(xs: List<&2, JT.Ext4JStep>, +ys: List<&2, JT.Ext4JStep>) -> {JT.Ext4JTx.replay_writes(List.append(&2, JT.Ext4JStep, xs, ys)) == List.append(&2, JW.Jbd2Write, JT.Ext4JTx.replay_writes(xs), JT.Ext4JTx.replay_writes(ys)) : List<&2, JW.Jbd2Write>}:
  match xs:
    case Nil{}:
      {==}
    case Con{JT.Ext4JData{+p, JL.Jbd2Put{+b, +src, +f, +c}, +o}, +t}:
      +w = {JW.Jbd2Write{b, JB.Jbd2.unescape(J.Jbd2.has(f, JB.Jbd2.flag_escape()), o)} : JW.Jbd2Write}
      Equal.cong(List<&2, JW.Jbd2Write>, List<&2, JW.Jbd2Write>, r => Con{w, r}, JT.Ext4JTx.replay_writes(List.append(&2, JT.Ext4JStep, t, ys)), List.append(&2, JW.Jbd2Write, JT.Ext4JTx.replay_writes(t), JT.Ext4JTx.replay_writes(ys)), Ext4Proof.rw_app(t, ys))
    case Con{JT.Ext4JHome{w}, +t}:
      Ext4Proof.rw_app(t, ys)
    case Con{JT.Ext4JLog{p, o}, +t}:
      Ext4Proof.rw_app(t, ys)
    case Con{JT.Ext4JDesc{p, o, ps}, +t}:
      Ext4Proof.rw_app(t, ys)
    case Con{JT.Ext4JCommit{p, o}, +t}:
      Ext4Proof.rw_app(t, ys)
    case Con{JT.Ext4JFlag{a, b}, +t}:
      Ext4Proof.rw_app(t, ys)

def Ext4Proof.homes_app(xs: List<&2, JT.Ext4JStep>, +ys: List<&2, JT.Ext4JStep>) -> {JT.Ext4JTx.homes(List.append(&2, JT.Ext4JStep, xs, ys)) == List.append(&2, JW.Jbd2Write, JT.Ext4JTx.homes(xs), JT.Ext4JTx.homes(ys)) : List<&2, JW.Jbd2Write>}:
  match xs:
    case Nil{}:
      {==}
    case Con{JT.Ext4JHome{+w}, +t}:
      Equal.cong(List<&2, JW.Jbd2Write>, List<&2, JW.Jbd2Write>, r => Con{w, r}, JT.Ext4JTx.homes(List.append(&2, JT.Ext4JStep, t, ys)), List.append(&2, JW.Jbd2Write, JT.Ext4JTx.homes(t), JT.Ext4JTx.homes(ys)), Ext4Proof.homes_app(t, ys))
    case Con{JT.Ext4JLog{p, o}, +t}:
      Ext4Proof.homes_app(t, ys)
    case Con{JT.Ext4JDesc{p, o, ps}, +t}:
      Ext4Proof.homes_app(t, ys)
    case Con{JT.Ext4JData{p, u, o}, +t}:
      Ext4Proof.homes_app(t, ys)
    case Con{JT.Ext4JCommit{p, o}, +t}:
      Ext4Proof.homes_app(t, ys)
    case Con{JT.Ext4JFlag{a, b}, +t}:
      Ext4Proof.homes_app(t, ys)

def Ext4Proof.committed_app(xs: List<&2, JT.Ext4JStep>, +ys: List<&2, JT.Ext4JStep>) -> {JT.Ext4JTx.committed(xs) == False{} : Bool} -> {JT.Ext4JTx.committed(ys) == False{} : Bool} -> {JT.Ext4JTx.committed(List.append(&2, JT.Ext4JStep, xs, ys)) == False{} : Bool}:
  match xs:
    case Nil{}:
      +hx => +hy => hy
    case Con{JT.Ext4JCommit{p, o}, t}:
      +hx => +hy => Ext4Proof.no({JT.Ext4JTx.committed(List.append(&2, JT.Ext4JStep, Con{JT.Ext4JCommit{p, o}, t}, ys)) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, hx))
    case Con{JT.Ext4JHome{w}, +t}:
      +hx => +hy => Ext4Proof.committed_app(t, ys, hx, hy)
    case Con{JT.Ext4JLog{p, o}, +t}:
      +hx => +hy => Ext4Proof.committed_app(t, ys, hx, hy)
    case Con{JT.Ext4JDesc{p, o, ps}, +t}:
      +hx => +hy => Ext4Proof.committed_app(t, ys, hx, hy)
    case Con{JT.Ext4JData{p, u, o}, +t}:
      +hx => +hy => Ext4Proof.committed_app(t, ys, hx, hy)
    case Con{JT.Ext4JFlag{a, b}, +t}:
      +hx => +hy => Ext4Proof.committed_app(t, ys, hx, hy)

# steps without the commit leave records without one
def Ext4Proof.no_commit_records(+s: Nat, xs: List<&2, JT.Ext4JStep>) -> {JT.Ext4JTx.committed(xs) == False{} : Bool} -> {JL.Jbd2Log.no_commit(JT.Ext4JTx.records(s, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      +h => {==}
    case Con{JT.Ext4JCommit{p, o}, t}:
      +h => Ext4Proof.no({JL.Jbd2Log.no_commit(JT.Ext4JTx.records(s, Con{JT.Ext4JCommit{p, o}, t})) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case Con{JT.Ext4JDesc{p, o, ps}, +t}:
      +h => Ext4Proof.no_commit_records(s, t, h)
    case Con{JT.Ext4JHome{w}, +t}:
      +h => Ext4Proof.no_commit_records(s, t, h)
    case Con{JT.Ext4JLog{p, o}, +t}:
      +h => Ext4Proof.no_commit_records(s, t, h)
    case Con{JT.Ext4JData{p, u, o}, +t}:
      +h => Ext4Proof.no_commit_records(s, t, h)
    case Con{JT.Ext4JFlag{a, b}, +t}:
      +h => Ext4Proof.no_commit_records(s, t, h)

# a prefix no longer than steps without the commit has none
def Ext4Proof.committed_take(xs: List<&2, JT.Ext4JStep>, +ys: List<&2, JT.Ext4JStep>, k: Nat) -> {JT.Ext4JTx.committed(xs) == False{} : Bool} -> {Nat.is_le(k, List.length(&2, JT.Ext4JStep, xs)) == True{} : Bool} -> {JT.Ext4JTx.committed(List.take(&2, JT.Ext4JStep, List.append(&2, JT.Ext4JStep, xs, ys), k)) == False{} : Bool}:
  match xs k:
    case Nil{} 0n:
      +hc => +hk => Equal.cong(List<&2, JT.Ext4JStep>, Bool, l => JT.Ext4JTx.committed(l), List.take(&2, JT.Ext4JStep, ys, 0n), Nil{}, Ext4Proof.take_zero(JT.Ext4JStep, ys))
    case Nil{} 1n+q:
      +hc => +hk => Ext4Proof.no({JT.Ext4JTx.committed(List.take(&2, JT.Ext4JStep, ys, 1n+q)) == False{} : Bool}, hk)
    case Con{x, t} 0n:
      +hc => +hk => {==}
    case Con{JT.Ext4JCommit{p, o}, t} 1n+q:
      +hc => +hk => Ext4Proof.no({JT.Ext4JTx.committed(List.take(&2, JT.Ext4JStep, List.append(&2, JT.Ext4JStep, Con{JT.Ext4JCommit{p, o}, t}, ys), 1n+q)) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, hc))
    case Con{JT.Ext4JHome{w}, +t} 1n+q:
      +hc => +hk => Ext4Proof.committed_take(t, ys, q, hc, hk)
    case Con{JT.Ext4JLog{p, o}, +t} 1n+q:
      +hc => +hk => Ext4Proof.committed_take(t, ys, q, hc, hk)
    case Con{JT.Ext4JDesc{p, o, ps}, +t} 1n+q:
      +hc => +hk => Ext4Proof.committed_take(t, ys, q, hc, hk)
    case Con{JT.Ext4JData{p, u, o}, +t} 1n+q:
      +hc => +hk => Ext4Proof.committed_take(t, ys, q, hc, hk)
    case Con{JT.Ext4JFlag{a, b}, +t} 1n+q:
      +hc => +hk => Ext4Proof.committed_take(t, ys, q, hc, hk)

# a prefix of steps without records has none
def Ext4Proof.records_nil_take(+s: Nat, xs: List<&2, JT.Ext4JStep>, k: Nat) -> {JT.Ext4JTx.records(s, xs) == Nil{} : List<&2, JL.Jbd2Rec>} -> {JT.Ext4JTx.records(s, List.take(&2, JT.Ext4JStep, xs, k)) == Nil{} : List<&2, JL.Jbd2Rec>}:
  match xs k:
    case Nil{} _:
      +h => {==}
    case Con{x, t} 0n:
      +h => {==}
    case Con{JT.Ext4JDesc{p, +o, +ps}, +t} 1n+q:
      +h => Ext4Proof.absurd({JT.Ext4JTx.records(s, List.take(&2, JT.Ext4JStep, Con{JT.Ext4JDesc{p, o, ps}, t}, 1n+q)) == Nil{} : List<&2, JL.Jbd2Rec>}, Ext4Proof.cons_nil(JL.Jbd2Rec, JL.Jbd2RDesc{s, ps}, JT.Ext4JTx.records(s, t), h))
    case Con{JT.Ext4JCommit{p, +o}, +t} 1n+q:
      +h => Ext4Proof.absurd({JT.Ext4JTx.records(s, List.take(&2, JT.Ext4JStep, Con{JT.Ext4JCommit{p, o}, t}, 1n+q)) == Nil{} : List<&2, JL.Jbd2Rec>}, Ext4Proof.cons_nil(JL.Jbd2Rec, JL.Jbd2RCommit{s}, JT.Ext4JTx.records(s, t), h))
    case Con{JT.Ext4JHome{w}, +t} 1n+q:
      +h => Ext4Proof.records_nil_take(s, t, q, h)
    case Con{JT.Ext4JLog{p, o}, +t} 1n+q:
      +h => Ext4Proof.records_nil_take(s, t, q, h)
    case Con{JT.Ext4JData{p, u, o}, +t} 1n+q:
      +h => Ext4Proof.records_nil_take(s, t, q, h)
    case Con{JT.Ext4JFlag{a, b}, +t} 1n+q:
      +h => Ext4Proof.records_nil_take(s, t, q, h)

def Ext4Proof.fh_app(+f: List<&2, Nat>, xs: List<&2, JT.Ext4JStep>, +ys: List<&2, JT.Ext4JStep>) -> {JT.Ext4JTx.fresh_homes(f, xs) == True{} : Bool} -> {JT.Ext4JTx.fresh_homes(f, ys) == True{} : Bool} -> {JT.Ext4JTx.fresh_homes(f, List.append(&2, JT.Ext4JStep, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      +hx => +hy => hy
    case Con{JT.Ext4JHome{+w}, +t}:
      +hx => +hy =>
        +a = JL.Jbd2Log.member(f, JW.Jbd2Write.block(w))
        Ext4Proof.and_i(a, JT.Ext4JTx.fresh_homes(f, List.append(&2, JT.Ext4JStep, t, ys)), Ext4Proof.and_l(a, JT.Ext4JTx.fresh_homes(f, t), hx), Ext4Proof.fh_app(f, t, ys, Ext4Proof.and_r(a, JT.Ext4JTx.fresh_homes(f, t), hx), hy))
    case Con{JT.Ext4JLog{p, o}, +t}:
      +hx => +hy => Ext4Proof.fh_app(f, t, ys, hx, hy)
    case Con{JT.Ext4JDesc{p, o, ps}, +t}:
      +hx => +hy => Ext4Proof.fh_app(f, t, ys, hx, hy)
    case Con{JT.Ext4JData{p, u, o}, +t}:
      +hx => +hy => Ext4Proof.fh_app(f, t, ys, hx, hy)
    case Con{JT.Ext4JCommit{p, o}, +t}:
      +hx => +hy => Ext4Proof.fh_app(f, t, ys, hx, hy)
    case Con{JT.Ext4JFlag{a, b}, +t}:
      +hx => +hy => Ext4Proof.fh_app(f, t, ys, hx, hy)

def Ext4Proof.fh_nohomes(+f: List<&2, Nat>, xs: List<&2, JT.Ext4JStep>) -> {JT.Ext4JTx.homes(xs) == Nil{} : List<&2, JW.Jbd2Write>} -> {JT.Ext4JTx.fresh_homes(f, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      +h => {==}
    case Con{JT.Ext4JHome{+w}, +t}:
      +h => Ext4Proof.absurd({JT.Ext4JTx.fresh_homes(f, Con{JT.Ext4JHome{w}, t}) == True{} : Bool}, Ext4Proof.cons_nil(JW.Jbd2Write, w, JT.Ext4JTx.homes(t), h))
    case Con{JT.Ext4JLog{p, o}, +t}:
      +h => Ext4Proof.fh_nohomes(f, t, h)
    case Con{JT.Ext4JDesc{p, o, ps}, +t}:
      +h => Ext4Proof.fh_nohomes(f, t, h)
    case Con{JT.Ext4JData{p, u, o}, +t}:
      +h => Ext4Proof.fh_nohomes(f, t, h)
    case Con{JT.Ext4JCommit{p, o}, +t}:
      +h => Ext4Proof.fh_nohomes(f, t, h)
    case Con{JT.Ext4JFlag{a, b}, +t}:
      +h => Ext4Proof.fh_nohomes(f, t, h)

# Cutting the steps around the commit

def Ext4Proof.take_commit(a: List<&2, JT.Ext4JStep>, +c: JT.Ext4JStep, +p: List<&2, JT.Ext4JStep>, +j: Nat) -> {List.take(&2, JT.Ext4JStep, List.append(&2, JT.Ext4JStep, a, Con{c, p}), 1n+Nat.add(List.length(&2, JT.Ext4JStep, a), j)) == List.append(&2, JT.Ext4JStep, a, Con{c, List.take(&2, JT.Ext4JStep, p, j)}) : List<&2, JT.Ext4JStep>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(List<&2, JT.Ext4JStep>, List<&2, JT.Ext4JStep>, r => Con{x, r}, List.take(&2, JT.Ext4JStep, List.append(&2, JT.Ext4JStep, t, Con{c, p}), 1n+Nat.add(List.length(&2, JT.Ext4JStep, t), j)), List.append(&2, JT.Ext4JStep, t, Con{c, List.take(&2, JT.Ext4JStep, p, j)}), Ext4Proof.take_commit(t, c, p, j))

def Ext4Proof.take_commit0(a: List<&2, JT.Ext4JStep>, +c: JT.Ext4JStep, +p: List<&2, JT.Ext4JStep>) -> {List.take(&2, JT.Ext4JStep, List.append(&2, JT.Ext4JStep, a, Con{c, p}), 1n+List.length(&2, JT.Ext4JStep, a)) == List.append(&2, JT.Ext4JStep, a, [c]) : List<&2, JT.Ext4JStep>}:
  match a:
    case Nil{}:
      Equal.cong(List<&2, JT.Ext4JStep>, List<&2, JT.Ext4JStep>, r => Con{c, r}, List.take(&2, JT.Ext4JStep, p, 0n), Nil{}, Ext4Proof.take_zero(JT.Ext4JStep, p))
    case Con{+x, +t}:
      Equal.cong(List<&2, JT.Ext4JStep>, List<&2, JT.Ext4JStep>, r => Con{x, r}, List.take(&2, JT.Ext4JStep, List.append(&2, JT.Ext4JStep, t, Con{c, p}), 1n+List.length(&2, JT.Ext4JStep, t)), List.append(&2, JT.Ext4JStep, t, [c]), Ext4Proof.take_commit0(t, c, p))

def Ext4Proof.drop_commit(a: List<&2, JT.Ext4JStep>, +c: JT.Ext4JStep, +p: List<&2, JT.Ext4JStep>) -> {List.drop(&2, JT.Ext4JStep, List.append(&2, JT.Ext4JStep, a, Con{c, p}), 1n+List.length(&2, JT.Ext4JStep, a)) == p : List<&2, JT.Ext4JStep>}:
  match a:
    case Nil{}:
      Ext4Proof.drop_zero(JT.Ext4JStep, p)
    case Con{x, +t}:
      Ext4Proof.drop_commit(t, c, p)

# Home steps

def Ext4Proof.rec_hs(+s: Nat, ws: List<&2, JW.Jbd2Write>, +os: List<&2, JT.Ext4JStep>) -> {JT.Ext4JTx.records(s, os) == Nil{} : List<&2, JL.Jbd2Rec>} -> {JT.Ext4JTx.records(s, List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(ws), os)) == Nil{} : List<&2, JL.Jbd2Rec>}:
  match ws:
    case Nil{}:
      +h => h
    case Con{w, +t}:
      +h => Ext4Proof.rec_hs(s, t, os, h)

def Ext4Proof.com_hs(ws: List<&2, JW.Jbd2Write>, +os: List<&2, JT.Ext4JStep>) -> {JT.Ext4JTx.committed(os) == False{} : Bool} -> {JT.Ext4JTx.committed(List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(ws), os)) == False{} : Bool}:
  match ws:
    case Nil{}:
      +h => h
    case Con{w, +t}:
      +h => Ext4Proof.com_hs(t, os, h)

def Ext4Proof.dp_hs(ws: List<&2, JW.Jbd2Write>, +os: List<&2, JT.Ext4JStep>) -> {JT.Ext4JTx.data_puts(os) == Nil{} : List<&2, JL.Jbd2Put>} -> {JT.Ext4JTx.data_puts(List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(ws), os)) == Nil{} : List<&2, JL.Jbd2Put>}:
  match ws:
    case Nil{}:
      +h => h
    case Con{w, +t}:
      +h => Ext4Proof.dp_hs(t, os, h)

def Ext4Proof.rw_hs(ws: List<&2, JW.Jbd2Write>, +os: List<&2, JT.Ext4JStep>) -> {JT.Ext4JTx.replay_writes(os) == Nil{} : List<&2, JW.Jbd2Write>} -> {JT.Ext4JTx.replay_writes(List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(ws), os)) == Nil{} : List<&2, JW.Jbd2Write>}:
  match ws:
    case Nil{}:
      +h => h
    case Con{w, +t}:
      +h => Ext4Proof.rw_hs(t, os, h)

def Ext4Proof.homes_hs(ws: List<&2, JW.Jbd2Write>, +os: List<&2, JT.Ext4JStep>) -> {JT.Ext4JTx.homes(os) == Nil{} : List<&2, JW.Jbd2Write>} -> {JT.Ext4JTx.homes(List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(ws), os)) == ws : List<&2, JW.Jbd2Write>}:
  match ws:
    case Nil{}:
      +h => h
    case Con{+w, +t}:
      +h => Equal.cong(List<&2, JW.Jbd2Write>, List<&2, JW.Jbd2Write>, r => Con{w, r}, JT.Ext4JTx.homes(List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(t), os)), t, Ext4Proof.homes_hs(t, os, h))

def Ext4Proof.fh_fresh_in.at(b: Bool, +fresh: List<&2, Nat>, +w: JW.Jbd2Write, +t: List<&2, JW.Jbd2Write>, +os: List<&2, JT.Ext4JStep>, ih: {JT.Ext4JTx.fresh_homes(fresh, List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(JT.Ext4JTx.fresh_in(fresh, t)), os)) == True{} : Bool}) -> {JL.Jbd2Log.member(fresh, JW.Jbd2Write.block(w)) == b : Bool} -> {JT.Ext4JTx.fresh_homes(fresh, List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(JT.Ext4JTx.keep(b, w, JT.Ext4JTx.fresh_in(fresh, t))), os)) == True{} : Bool}:
  match b:
    case True{}:
      +hb =>
        %Equal.sym(Bool, JL.Jbd2Log.member(fresh, JW.Jbd2Write.block(w)), True{}, hb) : {Bool.and(_, JT.Ext4JTx.fresh_homes(fresh, List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(JT.Ext4JTx.fresh_in(fresh, t)), os))) == True{} : Bool}
        ih
    case False{}:
      +hb => ih

# data=ordered: every block written in place is fresh
def Ext4Proof.fh_fresh_in(+fresh: List<&2, Nat>, ws: List<&2, JW.Jbd2Write>, +os: List<&2, JT.Ext4JStep>) -> {JT.Ext4JTx.fresh_homes(fresh, os) == True{} : Bool} -> {JT.Ext4JTx.fresh_homes(fresh, List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(JT.Ext4JTx.fresh_in(fresh, ws)), os)) == True{} : Bool}:
  match ws:
    case Nil{}:
      +h => h
    case Con{+w, +t}:
      +h => Ext4Proof.fh_fresh_in.at(JL.Jbd2Log.member(fresh, JW.Jbd2Write.block(w)), fresh, w, t, os, Ext4Proof.fh_fresh_in(fresh, t, os, h), {==})

def Ext4Proof.fh_in_place(m: JT.Jbd2Mode, +fresh: List<&2, Nat>, +ws: List<&2, JW.Jbd2Write>, +os: List<&2, JT.Ext4JStep>) -> {JT.Ext4JTx.fresh_homes(fresh, os) == True{} : Bool} -> {JT.Ext4JTx.fresh_homes(fresh, List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(JT.Ext4JTx.in_place(m, fresh, ws)), os)) == True{} : Bool}:
  match m:
    case JT.Jbd2DataJournal{}:
      +h => h
    case JT.Jbd2DataOrdered{}:
      +h => Ext4Proof.fh_fresh_in(fresh, ws, os, h)

# A group's logged copies

def Ext4Proof.flags_esc(+e: Bool, +f: Bool, +l: Bool) -> {J.Jbd2.has(JW.Jbd2Write.flags(e, f, l), JB.Jbd2.flag_escape()) == e : Bool}:
  match e f l:
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

def Ext4Proof.rec_datas(+sq: Nat, ws: List<&2, JW.Jbd2Write>, +g: J.Jbd2Geom, +s: U32, first: Bool, +pos: Nat) -> {JT.Ext4JTx.records(sq, JT.Ext4JTx.datas(ws, g, s, first, pos)) == Nil{} : List<&2, JL.Jbd2Rec>}:
  match ws:
    case Nil{}:
      {==}
    case Con{JW.Jbd2Write{b, d}, +t}:
      Ext4Proof.rec_datas(sq, t, g, s, False{}, Nat.add(pos, 1n))

def Ext4Proof.com_datas(ws: List<&2, JW.Jbd2Write>, +g: J.Jbd2Geom, +s: U32, first: Bool, +pos: Nat) -> {JT.Ext4JTx.committed(JT.Ext4JTx.datas(ws, g, s, first, pos)) == False{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{JW.Jbd2Write{b, d}, +t}:
      Ext4Proof.com_datas(t, g, s, False{}, Nat.add(pos, 1n))

def Ext4Proof.homes_datas(ws: List<&2, JW.Jbd2Write>, +g: J.Jbd2Geom, +s: U32, first: Bool, +pos: Nat) -> {JT.Ext4JTx.homes(JT.Ext4JTx.datas(ws, g, s, first, pos)) == Nil{} : List<&2, JW.Jbd2Write>}:
  match ws:
    case Nil{}:
      {==}
    case Con{JW.Jbd2Write{b, d}, +t}:
      Ext4Proof.homes_datas(t, g, s, False{}, Nat.add(pos, 1n))

# the copies, replayed, are the writes (escaping undone: escape_round_trip)
def Ext4Proof.rw_datas(ws: List<&2, JW.Jbd2Write>, +g: J.Jbd2Geom, +s: U32, +first: Bool, +pos: Nat) -> {JT.Ext4JTx.replay_writes(JT.Ext4JTx.datas(ws, g, s, first, pos)) == ws : List<&2, JW.Jbd2Write>}:
  match ws:
    case Nil{}:
      {==}
    case Con{JW.Jbd2Write{+b, +d}, +t}:
      +rest = JT.Ext4JTx.replay_writes(JT.Ext4JTx.datas(t, g, s, False{}, Nat.add(pos, 1n)))
      %Equal.sym(Bool, J.Jbd2.has(JW.Jbd2Write.flags(JB.Jbd2.needs_escape(d), first, JW.Jbd2Write.is_nil(t)), JB.Jbd2.flag_escape()), JB.Jbd2.needs_escape(d), Ext4Proof.flags_esc(JB.Jbd2.needs_escape(d), first, JW.Jbd2Write.is_nil(t))) : {Con{JW.Jbd2Write{b, JB.Jbd2.unescape(_, JB.Jbd2.escape(d))}, rest} == Con{JW.Jbd2Write{b, d}, t} : List<&2, JW.Jbd2Write>}
      %Equal.sym(B.Octets, JB.Jbd2.unescape(JB.Jbd2.needs_escape(d), JB.Jbd2.escape(d)), d, Laws.escape_round_trip(d)) : {Con{JW.Jbd2Write{b, _}, rest} == Con{JW.Jbd2Write{b, d}, t} : List<&2, JW.Jbd2Write>}
      Equal.cong(List<&2, JW.Jbd2Write>, List<&2, JW.Jbd2Write>, r => Con{JW.Jbd2Write{b, d}, r}, rest, t, Ext4Proof.rw_datas(t, g, s, False{}, Nat.add(pos, 1n)))

# The log

def Ext4Proof.com_logs(gs: List<&2, List<&2, JW.Jbd2Write>>, +g: J.Jbd2Geom, +s: U32, +uuid: B.Octets, +pos: Nat) -> {JT.Ext4JTx.committed(JT.Ext4JTx.logs(gs, g, s, uuid, pos)) == False{} : Bool}:
  match gs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      Ext4Proof.committed_app(JT.Ext4JTx.group(h, g, s, uuid, pos), JT.Ext4JTx.logs(t, g, s, uuid, Nat.add(pos, 1n+List.length(&2, JW.Jbd2Write, h))), Ext4Proof.com_datas(h, g, s, True{}, Nat.add(pos, 1n)), Ext4Proof.com_logs(t, g, s, uuid, Nat.add(pos, 1n+List.length(&2, JW.Jbd2Write, h))))

def Ext4Proof.homes_logs(gs: List<&2, List<&2, JW.Jbd2Write>>, +g: J.Jbd2Geom, +s: U32, +uuid: B.Octets, +pos: Nat) -> {JT.Ext4JTx.homes(JT.Ext4JTx.logs(gs, g, s, uuid, pos)) == Nil{} : List<&2, JW.Jbd2Write>}:
  match gs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +gr = JT.Ext4JTx.group(h, g, s, uuid, pos)
      +lt = JT.Ext4JTx.logs(t, g, s, uuid, Nat.add(pos, 1n+List.length(&2, JW.Jbd2Write, h)))
      Equal.trans(List<&2, JW.Jbd2Write>, JT.Ext4JTx.homes(List.append(&2, JT.Ext4JStep, gr, lt)), List.append(&2, JW.Jbd2Write, JT.Ext4JTx.homes(gr), JT.Ext4JTx.homes(lt)), Nil{}, Ext4Proof.homes_app(gr, lt), Ext4Proof.app_nil2(JW.Jbd2Write, JT.Ext4JTx.homes(gr), JT.Ext4JTx.homes(lt), Ext4Proof.homes_datas(h, g, s, True{}, Nat.add(pos, 1n)), Ext4Proof.homes_logs(t, g, s, uuid, Nat.add(pos, 1n+List.length(&2, JW.Jbd2Write, h)))))

def Ext4Proof.rw_logs(gs: List<&2, List<&2, JW.Jbd2Write>>, +g: J.Jbd2Geom, +s: U32, +uuid: B.Octets, +pos: Nat) -> {JT.Ext4JTx.replay_writes(JT.Ext4JTx.logs(gs, g, s, uuid, pos)) == List.concat(&2, JW.Jbd2Write, gs) : List<&2, JW.Jbd2Write>}:
  match gs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +gr = JT.Ext4JTx.group(h, g, s, uuid, pos)
      +lt = JT.Ext4JTx.logs(t, g, s, uuid, Nat.add(pos, 1n+List.length(&2, JW.Jbd2Write, h)))
      %Equal.sym(List<&2, JW.Jbd2Write>, JT.Ext4JTx.replay_writes(List.append(&2, JT.Ext4JStep, gr, lt)), List.append(&2, JW.Jbd2Write, JT.Ext4JTx.replay_writes(gr), JT.Ext4JTx.replay_writes(lt)), Ext4Proof.rw_app(gr, lt)) : {_ == List.concat(&2, JW.Jbd2Write, Con{h, t}) : List<&2, JW.Jbd2Write>}
      %Equal.sym(List<&2, JW.Jbd2Write>, JT.Ext4JTx.replay_writes(gr), h, Ext4Proof.rw_datas(h, g, s, True{}, Nat.add(pos, 1n))) : {List.append(&2, JW.Jbd2Write, _, JT.Ext4JTx.replay_writes(lt)) == List.concat(&2, JW.Jbd2Write, Con{h, t}) : List<&2, JW.Jbd2Write>}
      Equal.cong(List<&2, JW.Jbd2Write>, List<&2, JW.Jbd2Write>, r => List.append(&2, JW.Jbd2Write, h, r), JT.Ext4JTx.replay_writes(lt), List.concat(&2, JW.Jbd2Write, t), Ext4Proof.rw_logs(t, g, s, uuid, Nat.add(pos, 1n+List.length(&2, JW.Jbd2Write, h))))

# the groups hold the writes, in order
def Ext4Proof.chunks_add(full: Bool, +w: JW.Jbd2Write, +g: List<&2, JW.Jbd2Write>, +rest: List<&2, List<&2, JW.Jbd2Write>>) -> {List.concat(&2, JW.Jbd2Write, JT.Ext4JTx.chunks.add(full, w, g, rest)) == Con{w, List.concat(&2, JW.Jbd2Write, Con{g, rest})} : List<&2, JW.Jbd2Write>}:
  match full:
    case True{}:
      {==}
    case False{}:
      {==}

def Ext4Proof.chunks_put(+w: JW.Jbd2Write, gs: List<&2, List<&2, JW.Jbd2Write>>, +cap: Nat) -> {List.concat(&2, JW.Jbd2Write, JT.Ext4JTx.chunks.put(w, gs, cap)) == Con{w, List.concat(&2, JW.Jbd2Write, gs)} : List<&2, JW.Jbd2Write>}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      Ext4Proof.chunks_add(Nat.is_le(cap, List.length(&2, JW.Jbd2Write, g)), w, g, rest)

def Ext4Proof.chunks(xs: List<&2, JW.Jbd2Write>, +cap: Nat) -> {List.concat(&2, JW.Jbd2Write, JT.Ext4JTx.chunks(xs, cap)) == xs : List<&2, JW.Jbd2Write>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      Equal.trans(List<&2, JW.Jbd2Write>, List.concat(&2, JW.Jbd2Write, JT.Ext4JTx.chunks.put(w, JT.Ext4JTx.chunks(t, cap), cap)), Con{w, List.concat(&2, JW.Jbd2Write, JT.Ext4JTx.chunks(t, cap))}, Con{w, t}, Ext4Proof.chunks_put(w, JT.Ext4JTx.chunks(t, cap), cap), Equal.cong(List<&2, JW.Jbd2Write>, List<&2, JW.Jbd2Write>, r => Con{w, r}, List.concat(&2, JW.Jbd2Write, JT.Ext4JTx.chunks(t, cap)), t, Ext4Proof.chunks(t, cap)))

# Recovery of the log: the scan finds one transaction holding every copy

def Ext4Proof.fits_commit(+s: Nat, xs: List<&2, JT.Ext4JStep>) -> {JL.Jbd2Log.fits(List.append(&2, JL.Jbd2Rec, JT.Ext4JTx.records(s, xs), [JL.Jbd2RCommit{s}]), s) == True{} : Bool}:
  match xs:
    case Nil{}:
      Ext4Proof.eq_refl(s)
    case Con{JT.Ext4JDesc{p, o, ps}, t}:
      Ext4Proof.eq_refl(s)
    case Con{JT.Ext4JCommit{p, o}, t}:
      Ext4Proof.eq_refl(s)
    case Con{JT.Ext4JHome{w}, +t}:
      Ext4Proof.fits_commit(s, t)
    case Con{JT.Ext4JLog{p, o}, +t}:
      Ext4Proof.fits_commit(s, t)
    case Con{JT.Ext4JData{p, u, o}, +t}:
      Ext4Proof.fits_commit(s, t)
    case Con{JT.Ext4JFlag{a, b}, +t}:
      Ext4Proof.fits_commit(s, t)

def Ext4Proof.scan_logs(gs: List<&2, List<&2, JW.Jbd2Write>>, +g: J.Jbd2Geom, +s32: U32, +uuid: B.Octets, +pos: Nat, +s: Nat, +ps: List<&2, JL.Jbd2Put>) -> {JL.Jbd2Log.scan.go(List.append(&2, JL.Jbd2Rec, JT.Ext4JTx.records(s, JT.Ext4JTx.logs(gs, g, s32, uuid, pos)), [JL.Jbd2RCommit{s}]), True{}, s, ps, Nil{}, Nil{}) == [JL.Jbd2Tx{s, List.reverse(&2, JL.Jbd2Put, JL.Jbd2Log.rev_onto(JL.Jbd2Put, JT.Ext4JTx.data_puts(JT.Ext4JTx.logs(gs, g, s32, uuid, pos)), ps)), Nil{}}] : List<&2, JL.Jbd2Tx>}:
  match gs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +ds = JT.Ext4JTx.datas(h, g, s32, True{}, Nat.add(pos, 1n))
      +gr = JT.Ext4JTx.group(h, g, s32, uuid, pos)
      +pos2 = Nat.add(pos, 1n+List.length(&2, JW.Jbd2Write, h))
      +lt = JT.Ext4JTx.logs(t, g, s32, uuid, pos2)
      +dp = JT.Ext4JTx.data_puts(ds)
      +dl = JT.Ext4JTx.data_puts(lt)
      +rc = {[JL.Jbd2RCommit{s}] : List<&2, JL.Jbd2Rec>}
      +rl = JT.Ext4JTx.records(s, lt)
      +tl = List.append(&2, JL.Jbd2Rec, rl, rc)
      +er = {Equal.trans(List<&2, JL.Jbd2Rec>, JT.Ext4JTx.records(s, List.append(&2, JT.Ext4JStep, gr, lt)), List.append(&2, JL.Jbd2Rec, JT.Ext4JTx.records(s, gr), rl), Con{JL.Jbd2RDesc{s, dp}, rl}, Ext4Proof.records_app(s, gr, lt), Equal.cong(List<&2, JL.Jbd2Rec>, List<&2, JL.Jbd2Rec>, r => Con{JL.Jbd2RDesc{s, dp}, List.append(&2, JL.Jbd2Rec, r, rl)}, JT.Ext4JTx.records(s, ds), Nil{}, Ext4Proof.rec_datas(s, h, g, s32, True{}, Nat.add(pos, 1n)))) : {JT.Ext4JTx.records(s, List.append(&2, JT.Ext4JStep, gr, lt)) == Con{JL.Jbd2RDesc{s, dp}, rl} : List<&2, JL.Jbd2Rec>}}
      +rhs = {[JL.Jbd2Tx{s, List.reverse(&2, JL.Jbd2Put, JL.Jbd2Log.rev_onto(JL.Jbd2Put, JT.Ext4JTx.data_puts(List.append(&2, JT.Ext4JStep, gr, lt)), ps)), Nil{}}] : List<&2, JL.Jbd2Tx>}
      %Equal.sym(List<&2, JL.Jbd2Rec>, JT.Ext4JTx.records(s, List.append(&2, JT.Ext4JStep, gr, lt)), Con{JL.Jbd2RDesc{s, dp}, rl}, er) : {JL.Jbd2Log.scan.go(List.append(&2, JL.Jbd2Rec, _, rc), True{}, s, ps, Nil{}, Nil{}) == rhs : List<&2, JL.Jbd2Tx>}
      %Equal.sym(Bool, JL.Jbd2Log.fits(tl, s), True{}, Ext4Proof.fits_commit(s, lt)) : {JL.Jbd2Log.scan.go(tl, _, s, JL.Jbd2Log.rev_onto(JL.Jbd2Put, dp, ps), Nil{}, Nil{}) == rhs : List<&2, JL.Jbd2Tx>}
      %Equal.sym(List<&2, JL.Jbd2Put>, JT.Ext4JTx.data_puts(List.append(&2, JT.Ext4JStep, gr, lt)), List.append(&2, JL.Jbd2Put, dp, dl), Ext4Proof.dp_app(gr, lt)) : {JL.Jbd2Log.scan.go(tl, True{}, s, JL.Jbd2Log.rev_onto(JL.Jbd2Put, dp, ps), Nil{}, Nil{}) == [JL.Jbd2Tx{s, List.reverse(&2, JL.Jbd2Put, JL.Jbd2Log.rev_onto(JL.Jbd2Put, _, ps)), Nil{}}] : List<&2, JL.Jbd2Tx>}
      %Equal.sym(List<&2, JL.Jbd2Put>, JL.Jbd2Log.rev_onto(JL.Jbd2Put, List.append(&2, JL.Jbd2Put, dp, dl), ps), JL.Jbd2Log.rev_onto(JL.Jbd2Put, dl, JL.Jbd2Log.rev_onto(JL.Jbd2Put, dp, ps)), Ext4Proof.rev_onto_app(JL.Jbd2Put, dp, dl, ps)) : {JL.Jbd2Log.scan.go(tl, True{}, s, JL.Jbd2Log.rev_onto(JL.Jbd2Put, dp, ps), Nil{}, Nil{}) == [JL.Jbd2Tx{s, List.reverse(&2, JL.Jbd2Put, _), Nil{}}] : List<&2, JL.Jbd2Tx>}
      Ext4Proof.scan_logs(t, g, s32, uuid, pos2, s, JL.Jbd2Log.rev_onto(JL.Jbd2Put, dp, ps))

# one transaction revoking nothing replays its blocks
def Ext4Proof.plan_one(+s: Nat, +ps: List<&2, JL.Jbd2Put>) -> {JL.Jbd2Log.plan([JL.Jbd2Tx{s, ps, Nil{}}]) == JL.Jbd2Log.unrevoked(s, Nil{}, ps) : List<&2, JL.Jbd2Do>}:
  +u = JL.Jbd2Log.unrevoked(s, Nil{}, ps)
  +fi = Ext4Proof.filt(ps, s, Nil{})
  %Equal.sym(List<&2, JL.Jbd2Do>, JL.Jbd2Log.keep(ps, s, Nil{}, Nil{}), List.reverse.go(&2, JL.Jbd2Do, fi, Nil{}), Ext4Proof.keep_filt(ps, s, Nil{}, Nil{})) : {List.reverse(&2, JL.Jbd2Do, _) == u : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Do>, List.reverse.go(&2, JL.Jbd2Do, List.reverse.go(&2, JL.Jbd2Do, fi, Nil{}), Nil{}), List.append(&2, JL.Jbd2Do, fi, Nil{}), Ext4Proof.rev_rev(JL.Jbd2Do, fi, Nil{}, Nil{})) : {_ == u : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Do>, List.append(&2, JL.Jbd2Do, fi, Nil{}), fi, Ext4Proof.append_nil(JL.Jbd2Do, fi)) : {_ == u : List<&2, JL.Jbd2Do>}
  Ext4Proof.filt_unrevoked(ps, s, Nil{})

# The laws of a plan. Its parts, for build's inputs: pre (in-place writes
# and the opening steps), log, the commit, post (the checkpoint and the
# closing steps); steps = (pre ++ log) ++ commit :: post.

def Laws.jtx_uncommitted(g, uuid, jsb, seq, m, fresh, ws, sec, nsec, k, h):
  +tx = Laws.Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)
  +s32 = U32.from_nat(seq)
  +first = J.Jbd2Geom.first(g)
  +lg = JT.Ext4JTx.logged(m, fresh, J.Jbd2Geom.bs(g), ws)
  +ip = JT.Ext4JTx.in_place(m, fresh, ws)
  +os = JT.Ext4JTx.open_steps(jsb, first, s32)
  +pre = List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(ip), os)
  +log = JT.Ext4JTx.log_of(g, uuid, seq, lg)
  +a = List.append(&2, JT.Ext4JStep, pre, log)
  +c = JT.Ext4JTx.commit(tx)
  +post = JT.Ext4JTx.post(tx)
  +ca = Ext4Proof.committed_app(pre, log, Ext4Proof.com_hs(ip, os, {==}), Ext4Proof.com_logs(JT.Ext4JTx.chunks(lg, JT.Ext4JTx.cap(g)), g, s32, uuid, first))
  +hle = Ext4Proof.lt_succ_le(k, List.length(&2, JT.Ext4JStep, a), h)
  +tk = List.take(&2, JT.Ext4JStep, List.append(&2, JT.Ext4JStep, a, Con{c, post}), k)
  +rs = JT.Ext4JTx.records(seq, tk)
  +nc = Ext4Proof.no_commit_records(seq, tk, Ext4Proof.committed_take(a, Con{c, post}, k, ca, hle))
  Equal.cong(List<&2, JL.Jbd2Tx>, List<&2, JL.Jbd2Do>, x => JL.Jbd2Log.plan(x), JL.Jbd2Log.scan(seq, rs), Nil{}, Laws.scan_incomplete(seq, Nil{}, rs, nc))

def Laws.jtx_committed(g, uuid, jsb, seq, m, fresh, ws, sec, nsec, j):
  +tx = Laws.Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)
  +s32 = U32.from_nat(seq)
  +first = J.Jbd2Geom.first(g)
  +lg = JT.Ext4JTx.logged(m, fresh, J.Jbd2Geom.bs(g), ws)
  +gs = JT.Ext4JTx.chunks(lg, JT.Ext4JTx.cap(g))
  +ip = JT.Ext4JTx.in_place(m, fresh, ws)
  +os = JT.Ext4JTx.open_steps(jsb, first, s32)
  +cs = JT.Ext4JTx.close_steps(jsb, seq)
  +pre = List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(ip), os)
  +log = JT.Ext4JTx.log_of(g, uuid, seq, lg)
  +a = List.append(&2, JT.Ext4JStep, pre, log)
  +c = JT.Ext4JTx.commit(tx)
  +post = List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(lg), cs)
  +pj = List.take(&2, JT.Ext4JStep, post, j)
  +rc = {[JL.Jbd2RCommit{seq}] : List<&2, JL.Jbd2Rec>}
  +rlog = JT.Ext4JTx.records(seq, log)
  +rs = List.append(&2, JL.Jbd2Rec, rlog, rc)
  +dl = JT.Ext4JTx.data_puts(log)
  +da = JT.Ext4JTx.data_puts(a)
  +rhs0 = JL.Jbd2Log.unrevoked(seq, Nil{}, JT.Ext4JTx.data_puts(JT.Ext4JTx.steps(tx)))
  %Equal.sym(List<&2, JT.Ext4JStep>, List.take(&2, JT.Ext4JStep, List.append(&2, JT.Ext4JStep, a, Con{c, post}), 1n+Nat.add(List.length(&2, JT.Ext4JStep, a), j)), List.append(&2, JT.Ext4JStep, a, Con{c, pj}), Ext4Proof.take_commit(a, c, post, j)) : {JL.Jbd2Log.recover(seq, JT.Ext4JTx.records(seq, _)) == rhs0 : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Rec>, JT.Ext4JTx.records(seq, List.append(&2, JT.Ext4JStep, a, Con{c, pj})), List.append(&2, JL.Jbd2Rec, JT.Ext4JTx.records(seq, a), JT.Ext4JTx.records(seq, Con{c, pj})), Ext4Proof.records_app(seq, a, Con{c, pj})) : {JL.Jbd2Log.recover(seq, _) == rhs0 : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Rec>, JT.Ext4JTx.records(seq, pj), Nil{}, Ext4Proof.records_nil_take(seq, post, j, Ext4Proof.rec_hs(seq, lg, cs, {==}))) : {JL.Jbd2Log.recover(seq, List.append(&2, JL.Jbd2Rec, JT.Ext4JTx.records(seq, a), Con{JL.Jbd2RCommit{seq}, _})) == rhs0 : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Rec>, JT.Ext4JTx.records(seq, a), List.append(&2, JL.Jbd2Rec, JT.Ext4JTx.records(seq, pre), rlog), Ext4Proof.records_app(seq, pre, log)) : {JL.Jbd2Log.recover(seq, List.append(&2, JL.Jbd2Rec, _, rc)) == rhs0 : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Rec>, JT.Ext4JTx.records(seq, pre), Nil{}, Ext4Proof.rec_hs(seq, ip, os, {==})) : {JL.Jbd2Log.recover(seq, List.append(&2, JL.Jbd2Rec, List.append(&2, JL.Jbd2Rec, _, rlog), rc)) == rhs0 : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Put>, JT.Ext4JTx.data_puts(List.append(&2, JT.Ext4JStep, a, Con{c, post})), List.append(&2, JL.Jbd2Put, da, JT.Ext4JTx.data_puts(post)), Ext4Proof.dp_app(a, Con{c, post})) : {JL.Jbd2Log.recover(seq, rs) == JL.Jbd2Log.unrevoked(seq, Nil{}, _) : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Put>, JT.Ext4JTx.data_puts(post), Nil{}, Ext4Proof.dp_hs(lg, cs, {==})) : {JL.Jbd2Log.recover(seq, rs) == JL.Jbd2Log.unrevoked(seq, Nil{}, List.append(&2, JL.Jbd2Put, da, _)) : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Put>, List.append(&2, JL.Jbd2Put, da, Nil{}), da, Ext4Proof.append_nil(JL.Jbd2Put, da)) : {JL.Jbd2Log.recover(seq, rs) == JL.Jbd2Log.unrevoked(seq, Nil{}, _) : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Put>, da, List.append(&2, JL.Jbd2Put, JT.Ext4JTx.data_puts(pre), dl), Ext4Proof.dp_app(pre, log)) : {JL.Jbd2Log.recover(seq, rs) == JL.Jbd2Log.unrevoked(seq, Nil{}, _) : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Put>, JT.Ext4JTx.data_puts(pre), Nil{}, Ext4Proof.dp_hs(ip, os, {==})) : {JL.Jbd2Log.recover(seq, rs) == JL.Jbd2Log.unrevoked(seq, Nil{}, List.append(&2, JL.Jbd2Put, _, dl)) : List<&2, JL.Jbd2Do>}
  %Equal.sym(Bool, JL.Jbd2Log.fits(rs, seq), True{}, Ext4Proof.fits_commit(seq, log)) : {JL.Jbd2Log.plan(JL.Jbd2Log.scan.go(rs, _, seq, Nil{}, Nil{}, Nil{})) == JL.Jbd2Log.unrevoked(seq, Nil{}, dl) : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Tx>, JL.Jbd2Log.scan.go(rs, True{}, seq, Nil{}, Nil{}, Nil{}), [JL.Jbd2Tx{seq, List.reverse(&2, JL.Jbd2Put, JL.Jbd2Log.rev_onto(JL.Jbd2Put, dl, Nil{})), Nil{}}], Ext4Proof.scan_logs(gs, g, s32, uuid, first, seq, Nil{})) : {JL.Jbd2Log.plan(_) == JL.Jbd2Log.unrevoked(seq, Nil{}, dl) : List<&2, JL.Jbd2Do>}
  %Equal.sym(List<&2, JL.Jbd2Put>, List.reverse(&2, JL.Jbd2Put, JL.Jbd2Log.rev_onto(JL.Jbd2Put, dl, Nil{})), dl, Ext4Proof.rr(JL.Jbd2Put, dl)) : {JL.Jbd2Log.plan([JL.Jbd2Tx{seq, _, Nil{}}]) == JL.Jbd2Log.unrevoked(seq, Nil{}, dl) : List<&2, JL.Jbd2Do>}
  Ext4Proof.plan_one(seq, dl)

# the logged copies, replayed, are the logged writes
def Ext4Proof.copies(+g: J.Jbd2Geom, +uuid: B.Octets, +jsb: B.Octets, +seq: Nat, +m: JT.Jbd2Mode, +fresh: List<&2, Nat>, +ws: List<&2, JW.Jbd2Write>, +sec: U32, +nsec: U32) -> {JT.Ext4JTx.replay_writes(JT.Ext4JTx.steps(Laws.Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec))) == JT.Ext4JTx.logged(m, fresh, J.Jbd2Geom.bs(g), ws) : List<&2, JW.Jbd2Write>}:
  +tx = Laws.Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)
  +s32 = U32.from_nat(seq)
  +first = J.Jbd2Geom.first(g)
  +lg = JT.Ext4JTx.logged(m, fresh, J.Jbd2Geom.bs(g), ws)
  +gs = JT.Ext4JTx.chunks(lg, JT.Ext4JTx.cap(g))
  +ip = JT.Ext4JTx.in_place(m, fresh, ws)
  +os = JT.Ext4JTx.open_steps(jsb, first, s32)
  +cs = JT.Ext4JTx.close_steps(jsb, seq)
  +pre = List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(ip), os)
  +log = JT.Ext4JTx.log_of(g, uuid, seq, lg)
  +a = List.append(&2, JT.Ext4JStep, pre, log)
  +c = JT.Ext4JTx.commit(tx)
  +post = List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(lg), cs)
  +ra = JT.Ext4JTx.replay_writes(a)
  %Equal.sym(List<&2, JW.Jbd2Write>, JT.Ext4JTx.replay_writes(List.append(&2, JT.Ext4JStep, a, Con{c, post})), List.append(&2, JW.Jbd2Write, ra, JT.Ext4JTx.replay_writes(post)), Ext4Proof.rw_app(a, Con{c, post})) : {_ == lg : List<&2, JW.Jbd2Write>}
  %Equal.sym(List<&2, JW.Jbd2Write>, JT.Ext4JTx.replay_writes(post), Nil{}, Ext4Proof.rw_hs(lg, cs, {==})) : {List.append(&2, JW.Jbd2Write, ra, _) == lg : List<&2, JW.Jbd2Write>}
  %Equal.sym(List<&2, JW.Jbd2Write>, List.append(&2, JW.Jbd2Write, ra, Nil{}), ra, Ext4Proof.append_nil(JW.Jbd2Write, ra)) : {_ == lg : List<&2, JW.Jbd2Write>}
  %Equal.sym(List<&2, JW.Jbd2Write>, ra, List.append(&2, JW.Jbd2Write, JT.Ext4JTx.replay_writes(pre), JT.Ext4JTx.replay_writes(log)), Ext4Proof.rw_app(pre, log)) : {_ == lg : List<&2, JW.Jbd2Write>}
  %Equal.sym(List<&2, JW.Jbd2Write>, JT.Ext4JTx.replay_writes(pre), Nil{}, Ext4Proof.rw_hs(ip, os, {==})) : {List.append(&2, JW.Jbd2Write, _, JT.Ext4JTx.replay_writes(log)) == lg : List<&2, JW.Jbd2Write>}
  %Equal.sym(List<&2, JW.Jbd2Write>, JT.Ext4JTx.replay_writes(log), List.concat(&2, JW.Jbd2Write, gs), Ext4Proof.rw_logs(gs, g, s32, uuid, first)) : {_ == lg : List<&2, JW.Jbd2Write>}
  Ext4Proof.chunks(lg, JT.Ext4JTx.cap(g))

def Laws.jtx_copies(g, uuid, jsb, seq, m, fresh, ws, sec, nsec):
  Ext4Proof.copies(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)

def Laws.jtx_checkpoint(g, uuid, jsb, seq, m, fresh, ws, sec, nsec):
  +tx = Laws.Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)
  +s32 = U32.from_nat(seq)
  +first = J.Jbd2Geom.first(g)
  +lg = JT.Ext4JTx.logged(m, fresh, J.Jbd2Geom.bs(g), ws)
  +ip = JT.Ext4JTx.in_place(m, fresh, ws)
  +os = JT.Ext4JTx.open_steps(jsb, first, s32)
  +cs = JT.Ext4JTx.close_steps(jsb, seq)
  +pre = List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(ip), os)
  +log = JT.Ext4JTx.log_of(g, uuid, seq, lg)
  +a = List.append(&2, JT.Ext4JStep, pre, log)
  +c = JT.Ext4JTx.commit(tx)
  +post = List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(lg), cs)
  %Equal.sym(List<&2, JT.Ext4JStep>, List.drop(&2, JT.Ext4JStep, List.append(&2, JT.Ext4JStep, a, Con{c, post}), 1n+List.length(&2, JT.Ext4JStep, a)), post, Ext4Proof.drop_commit(a, c, post)) : {JT.Ext4JTx.homes(_) == JT.Ext4JTx.replay_writes(JT.Ext4JTx.steps(tx)) : List<&2, JW.Jbd2Write>}
  Equal.trans(List<&2, JW.Jbd2Write>, JT.Ext4JTx.homes(post), lg, JT.Ext4JTx.replay_writes(JT.Ext4JTx.steps(tx)), Ext4Proof.homes_hs(lg, cs, {==}), Equal.sym(List<&2, JW.Jbd2Write>, JT.Ext4JTx.replay_writes(JT.Ext4JTx.steps(tx)), lg, Ext4Proof.copies(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)))

def Laws.jtx_in_place(g, uuid, jsb, seq, m, fresh, ws, sec, nsec):
  +tx = Laws.Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)
  +s32 = U32.from_nat(seq)
  +first = J.Jbd2Geom.first(g)
  +lg = JT.Ext4JTx.logged(m, fresh, J.Jbd2Geom.bs(g), ws)
  +gs = JT.Ext4JTx.chunks(lg, JT.Ext4JTx.cap(g))
  +ip = JT.Ext4JTx.in_place(m, fresh, ws)
  +os = JT.Ext4JTx.open_steps(jsb, first, s32)
  +pre = List.append(&2, JT.Ext4JStep, JT.Ext4JTx.home_steps(ip), os)
  +log = JT.Ext4JTx.log_of(g, uuid, seq, lg)
  +a = List.append(&2, JT.Ext4JStep, pre, log)
  +c = JT.Ext4JTx.commit(tx)
  +post = JT.Ext4JTx.post(tx)
  %Equal.sym(List<&2, JT.Ext4JStep>, List.take(&2, JT.Ext4JStep, List.append(&2, JT.Ext4JStep, a, Con{c, post}), 1n+List.length(&2, JT.Ext4JStep, a)), List.append(&2, JT.Ext4JStep, a, [c]), Ext4Proof.take_commit0(a, c, post)) : {JT.Ext4JTx.fresh_homes(fresh, _) == True{} : Bool}
  Ext4Proof.fh_app(fresh, a, [c], Ext4Proof.fh_app(fresh, pre, log, Ext4Proof.fh_in_place(m, fresh, ws, os, {==}), Ext4Proof.fh_nohomes(fresh, log, Ext4Proof.homes_logs(gs, g, s32, uuid, first))), {==})

def Laws.jtx_journal_mode(g, uuid, jsb, seq, fresh, ws, sec, nsec):
  +m = {JT.Jbd2DataJournal{} : JT.Jbd2Mode}
  +tx = Laws.Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)
  +s32 = U32.from_nat(seq)
  +first = J.Jbd2Geom.first(g)
  +lg = JT.Ext4JTx.logged(m, fresh, J.Jbd2Geom.bs(g), ws)
  +gs = JT.Ext4JTx.chunks(lg, JT.Ext4JTx.cap(g))
  +os = JT.Ext4JTx.open_steps(jsb, first, s32)
  +log = JT.Ext4JTx.log_of(g, uuid, seq, lg)
  +a = List.append(&2, JT.Ext4JStep, os, log)
  +c = JT.Ext4JTx.commit(tx)
  +post = JT.Ext4JTx.post(tx)
  %Equal.sym(List<&2, JT.Ext4JStep>, List.take(&2, JT.Ext4JStep, List.append(&2, JT.Ext4JStep, a, Con{c, post}), 1n+List.length(&2, JT.Ext4JStep, a)), List.append(&2, JT.Ext4JStep, a, [c]), Ext4Proof.take_commit0(a, c, post)) : {JT.Ext4JTx.homes(_) == Nil{} : List<&2, JW.Jbd2Write>}
  +ea = {Equal.trans(List<&2, JW.Jbd2Write>, JT.Ext4JTx.homes(a), List.append(&2, JW.Jbd2Write, JT.Ext4JTx.homes(os), JT.Ext4JTx.homes(log)), Nil{}, Ext4Proof.homes_app(os, log), Ext4Proof.app_nil2(JW.Jbd2Write, JT.Ext4JTx.homes(os), JT.Ext4JTx.homes(log), {==}, Ext4Proof.homes_logs(gs, g, s32, uuid, first))) : {JT.Ext4JTx.homes(a) == Nil{} : List<&2, JW.Jbd2Write>}}
  Equal.trans(List<&2, JW.Jbd2Write>, JT.Ext4JTx.homes(List.append(&2, JT.Ext4JStep, a, [c])), List.append(&2, JW.Jbd2Write, JT.Ext4JTx.homes(a), JT.Ext4JTx.homes([c])), Nil{}, Ext4Proof.homes_app(a, [c]), Ext4Proof.app_nil2(JW.Jbd2Write, JT.Ext4JTx.homes(a), JT.Ext4JTx.homes([c]), ea, {==}))

def Laws.jtx_uncommitted_witness():
  {==}

# The journal's codec: lemmas (Jc.*). The reads of the blocks the writer
# makes go through bytes' laws only: field reads inside joined bytes, and
# inside a field patched by Jbd2.patch32.

# Natural numbers

def Jc.add_zero(+a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 0n), p, Jc.add_zero(p))

def Jc.add_succ(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 1n+b), 1n+Nat.add(p, b), Jc.add_succ(p, b))

def Jc.add_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), Jc.add_assoc(p, b, c))

def Jc.add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, Jc.add_zero(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p), Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, b), Nat.add(b, p), Jc.add_comm(p, b)), Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), Jc.add_succ(b, p)))

def Jc.le_add_r(+a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      Ext4Proof.le_zero(b)
    case 1n+p:
      Jc.le_add_r(p, b)

# i + n <= m: i <= m
def Jc.le_add_l(+i: Nat, +n: Nat, +m: Nat) -> {Nat.is_le(Nat.add(i, n), m) == True{} : Bool} -> {Nat.is_le(i, m) == True{} : Bool}:
  match i m:
    case 0n _:
      h => Ext4Proof.le_zero(m)
    case 1n+p 0n:
      h => Ext4Proof.no({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      h => Jc.le_add_l(p, n, q, h)

# a <= c: a + (c - a) == c
def Jc.add_sub(+a: Nat, +c: Nat) -> {Nat.is_le(a, c) == True{} : Bool} -> {Nat.add(a, Nat.sub(c, a)) == c : Nat}:
  match a c:
    case 0n 0n:
      h => {==}
    case 0n 1n+q:
      h => {==}
    case 1n+p 0n:
      h => Ext4Proof.no({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, h)
    case 1n+p 1n+q:
      h => Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, Nat.sub(q, p)), q, Jc.add_sub(p, q, h))

# x == y as Bool to a <= x being a <= y
def Jc.le_eq(+a: Nat, +x: Nat, +y: Nat, e: {x == y : Nat}, h: {Nat.is_le(a, y) == True{} : Bool}) -> {Nat.is_le(a, x) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(a, x), Nat.is_le(a, y), True{}, Equal.cong(Nat, Bool, k => Nat.is_le(a, k), x, y, e), h)

# Words: every U32 equals itself

def Jc.bool_cmp_self(+b: Bool) -> {Word.cmp.fin(b, b, EQ{}) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Jc.word_cmp_self(+n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{+b, t}:
          Equal.trans(Cmp, Word.cmp.fin(b, b, Word.cmp(p, t, t)), Word.cmp.fin(b, b, EQ{}), EQ{},
            Equal.cong(Cmp, Cmp, x => Word.cmp.fin(b, b, x), Word.cmp(p, t, t), EQ{}, Jc.word_cmp_self(p, t)),
            Jc.bool_cmp_self(b))

def Jc.u32_refl(+a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{+w}:
      %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, Jc.word_cmp_self(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

# Bytes: lengths of joined bytes, and reads at the head and past a part

def Jc.len2(+a: B.Octets, +b: B.Octets, +ka: Nat, +kb: Nat, ha: {B.Octets.len(a) == ka : Nat}, hb: {B.Octets.len(b) == kb : Nat}) -> {B.Octets.len(B.Octets.append(a, b)) == Nat.add(ka, kb) : Nat}:
  %Equal.sym(Nat, B.Octets.len(B.Octets.append(a, b)), Nat.add(B.Octets.len(a), B.Octets.len(b)), BL.octets_len_append(a, b)) : {_ == Nat.add(ka, kb) : Nat}
  %Equal.sym(Nat, B.Octets.len(a), ka, ha) : {Nat.add(_, B.Octets.len(b)) == Nat.add(ka, kb) : Nat}
  %Equal.sym(Nat, B.Octets.len(b), kb, hb) : {Nat.add(ka, _) == Nat.add(ka, kb) : Nat}
  {==}

def Jc.app3(+a: B.Octets, +b: B.Octets, +c: B.Octets) -> {B.Octets.append(a, B.Octets.append(b, c)) == B.Octets.append(B.Octets.append(a, b), c) : B.Octets}:
  Equal.sym(B.Octets, B.Octets.append(B.Octets.append(a, b), c), B.Octets.append(a, B.Octets.append(b, c)), BL.octets_append_assoc(a, b, c))

def Jc.be32_head(+v: U32, +r: B.Octets) -> {B.Octets.be32_at(B.Octets.append(B.Octets.be32(v), r), 0n) == Some{v} : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(B.Octets.be32(v), r), 0n), B.Octets.be32_at(B.Octets.be32(v), 0n), Some{v},
    BL.octets_be32_at_append_le(B.Octets.be32(v), r, 0n, Equal.cong(Nat, Bool, k => Nat.is_le(4n, k), B.Octets.len(B.Octets.be32(v)), 4n, BL.octets_len_be32(v))),
    BL.octets_be32_round_trip(v))

def Jc.be16_head(+v: U32, +r: B.Octets) -> {B.Octets.be16_at(B.Octets.append(B.Octets.be16(v), r), 0n) == Some{B.low16(v)} : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.append(B.Octets.be16(v), r), 0n), B.Octets.be16_at(B.Octets.be16(v), 0n), Some{B.low16(v)},
    BL.octets_be16_at_append_le(B.Octets.be16(v), r, 0n, Equal.cong(Nat, Bool, k => Nat.is_le(2n, k), B.Octets.len(B.Octets.be16(v)), 2n, BL.octets_len_be16(v))),
    BL.octets_be16_round_trip(v))

def Jc.be64_head(+v: W.W64, +r: B.Octets) -> {B.Octets.be64_at(B.Octets.append(B.Octets.be64(v), r), 0n) == Some{v} : Maybe<&2, W.W64>}:
  Equal.trans(Maybe<&2, W.W64>, B.Octets.be64_at(B.Octets.append(B.Octets.be64(v), r), 0n), B.Octets.be64_at(B.Octets.be64(v), 0n), Some{v},
    BL.octets_be64_at_append_le(B.Octets.be64(v), r, 0n, Equal.cong(Nat, Bool, k => Nat.is_le(8n, k), B.Octets.len(B.Octets.be64(v)), 8n, BL.octets_len_be64(v))),
    BL.octets_be64_round_trip(v))

def Jc.skip32(+a: B.Octets, +r: B.Octets, +k: Nat, +i: Nat, h: {B.Octets.len(a) == k : Nat}) -> {B.Octets.be32_at(B.Octets.append(a, r), Nat.add(k, i)) == B.Octets.be32_at(r, i) : Maybe<&2, U32>}:
  %h : {B.Octets.be32_at(B.Octets.append(a, r), Nat.add(_, i)) == B.Octets.be32_at(r, i) : Maybe<&2, U32>}
  BL.octets_be32_at_append_add(a, r, i)

def Jc.skip16(+a: B.Octets, +r: B.Octets, +k: Nat, +i: Nat, h: {B.Octets.len(a) == k : Nat}) -> {B.Octets.be16_at(B.Octets.append(a, r), Nat.add(k, i)) == B.Octets.be16_at(r, i) : Maybe<&2, U32>}:
  %h : {B.Octets.be16_at(B.Octets.append(a, r), Nat.add(_, i)) == B.Octets.be16_at(r, i) : Maybe<&2, U32>}
  BL.octets_be16_at_append_add(a, r, i)

def Jc.skip64(+a: B.Octets, +r: B.Octets, +k: Nat, +i: Nat, h: {B.Octets.len(a) == k : Nat}) -> {B.Octets.be64_at(B.Octets.append(a, r), Nat.add(k, i)) == B.Octets.be64_at(r, i) : Maybe<&2, W.W64>}:
  %h : {B.Octets.be64_at(B.Octets.append(a, r), Nat.add(_, i)) == B.Octets.be64_at(r, i) : Maybe<&2, W.W64>}
  BL.octets_be64_at_append_add(a, r, i)

def Jc.skip8(+a: B.Octets, +r: B.Octets, +k: Nat, +i: Nat, h: {B.Octets.len(a) == k : Nat}) -> {B.Octets.at(B.Octets.append(a, r), Nat.add(k, i)) == B.Octets.at(r, i) : Maybe<&2, U32>}:
  %h : {B.Octets.at(B.Octets.append(a, r), Nat.add(_, i)) == B.Octets.at(r, i) : Maybe<&2, U32>}
  BL.octets_at_append_add(a, r, i)

# Fields: a 32-bit field patched (Jbd2.patch32) reads back; the bytes before
# and after it read as before; the bytes before it and after it are kept

def Jc.patch_take(+o: B.Octets, +i: Nat, +v: U32, h1: {Nat.is_le(i, B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.take(i, J.Jbd2.patch32(o, i, v)) == B.Octets.take(i, o) : B.Octets}:
  %BL.octets_len_take_le(i, o, h1) : {B.Octets.take(_, B.Octets.append(B.Octets.take(i, o), B.Octets.append(B.Octets.be32(v), B.Octets.drop(Nat.add(i, 4n), o)))) == B.Octets.take(i, o) : B.Octets}
  BL.octets_take_append(B.Octets.take(i, o), B.Octets.append(B.Octets.be32(v), B.Octets.drop(Nat.add(i, 4n), o)))

def Jc.patch_drop(+o: B.Octets, +i: Nat, +v: U32, h1: {Nat.is_le(Nat.add(i, 4n), B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.drop(Nat.add(i, 4n), J.Jbd2.patch32(o, i, v)) == B.Octets.drop(Nat.add(i, 4n), o) : B.Octets}:
  +t = B.Octets.take(i, o)
  +q = B.Octets.be32(v)
  +d = B.Octets.drop(Nat.add(i, 4n), o)
  %BL.octets_len_take_le(i, o, Jc.le_add_l(i, 4n, B.Octets.len(o), h1)) : {B.Octets.drop(Nat.add(_, 4n), B.Octets.append(t, B.Octets.append(q, d))) == d : B.Octets}
  %BL.octets_len_be32(v) : {B.Octets.drop(Nat.add(B.Octets.len(t), _), B.Octets.append(t, B.Octets.append(q, d))) == d : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(Nat.add(B.Octets.len(t), B.Octets.len(q)), B.Octets.append(t, B.Octets.append(q, d))), B.Octets.drop(B.Octets.len(q), B.Octets.append(q, d)), BL.octets_drop_append_add(t, B.Octets.len(q), B.Octets.append(q, d))) : {_ == d : B.Octets}
  BL.octets_drop_append(q, d)

def Jc.patch_same32(+o: B.Octets, +i: Nat, +v: U32, h1: {Nat.is_le(Nat.add(i, 4n), B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.be32_at(J.Jbd2.patch32(o, i, v), i) == Some{v} : Maybe<&2, U32>}:
  +t = B.Octets.take(i, o)
  +y = B.Octets.append(B.Octets.be32(v), B.Octets.drop(Nat.add(i, 4n), o))
  +lt = BL.octets_len_take_le(i, o, Jc.le_add_l(i, 4n, B.Octets.len(o), h1))
  %Equal.trans(Nat, Nat.add(B.Octets.len(t), 0n), B.Octets.len(t), i, Jc.add_zero(B.Octets.len(t)), lt) : {B.Octets.be32_at(B.Octets.append(t, y), _) == Some{v} : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(t, y), Nat.add(B.Octets.len(t), 0n)), B.Octets.be32_at(y, 0n), BL.octets_be32_at_append_add(t, y, 0n)) : {_ == Some{v} : Maybe<&2, U32>}
  Jc.be32_head(v, B.Octets.drop(Nat.add(i, 4n), o))

# the offset past the patched field, as reads past the first parts see it
def Jc.off_eq(+t: B.Octets, +q: B.Octets, +i: Nat, +d: Nat, et: {B.Octets.len(t) == i : Nat}, eq: {B.Octets.len(q) == 4n : Nat}) -> {Nat.add(B.Octets.len(t), Nat.add(B.Octets.len(q), d)) == Nat.add(Nat.add(i, 4n), d) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(i, 4n), d), Nat.add(i, Nat.add(4n, d)), Jc.add_assoc(i, 4n, d)) : {Nat.add(B.Octets.len(t), Nat.add(B.Octets.len(q), d)) == _ : Nat}
  %Equal.sym(Nat, B.Octets.len(t), i, et) : {Nat.add(_, Nat.add(B.Octets.len(q), d)) == Nat.add(i, Nat.add(4n, d)) : Nat}
  %Equal.sym(Nat, B.Octets.len(q), 4n, eq) : {Nat.add(i, Nat.add(_, d)) == Nat.add(i, Nat.add(4n, d)) : Nat}
  {==}

def Jc.patch_high32(+o: B.Octets, +i: Nat, +v: U32, +d: Nat, h1: {Nat.is_le(Nat.add(i, 4n), B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.be32_at(J.Jbd2.patch32(o, i, v), Nat.add(Nat.add(i, 4n), d)) == B.Octets.be32_at(o, Nat.add(Nat.add(i, 4n), d)) : Maybe<&2, U32>}:
  +t = B.Octets.take(i, o)
  +q = B.Octets.be32(v)
  +r = B.Octets.drop(Nat.add(i, 4n), o)
  %Jc.off_eq(t, q, i, d, BL.octets_len_take_le(i, o, Jc.le_add_l(i, 4n, B.Octets.len(o), h1)), BL.octets_len_be32(v)) : {B.Octets.be32_at(B.Octets.append(t, B.Octets.append(q, r)), _) == B.Octets.be32_at(o, Nat.add(Nat.add(i, 4n), d)) : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(t, B.Octets.append(q, r)), Nat.add(B.Octets.len(t), Nat.add(B.Octets.len(q), d))), B.Octets.be32_at(B.Octets.append(q, r), Nat.add(B.Octets.len(q), d)), BL.octets_be32_at_append_add(t, B.Octets.append(q, r), Nat.add(B.Octets.len(q), d))) : {_ == B.Octets.be32_at(o, Nat.add(Nat.add(i, 4n), d)) : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(q, r), Nat.add(B.Octets.len(q), d)), B.Octets.be32_at(r, d), BL.octets_be32_at_append_add(q, r, d)) : {_ == B.Octets.be32_at(o, Nat.add(Nat.add(i, 4n), d)) : Maybe<&2, U32>}
  BL.octets_be32_at_drop(Nat.add(i, 4n), o, d)

def Jc.patch_high64(+o: B.Octets, +i: Nat, +v: U32, +d: Nat, h1: {Nat.is_le(Nat.add(i, 4n), B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.be64_at(J.Jbd2.patch32(o, i, v), Nat.add(Nat.add(i, 4n), d)) == B.Octets.be64_at(o, Nat.add(Nat.add(i, 4n), d)) : Maybe<&2, W.W64>}:
  +t = B.Octets.take(i, o)
  +q = B.Octets.be32(v)
  +r = B.Octets.drop(Nat.add(i, 4n), o)
  %Jc.off_eq(t, q, i, d, BL.octets_len_take_le(i, o, Jc.le_add_l(i, 4n, B.Octets.len(o), h1)), BL.octets_len_be32(v)) : {B.Octets.be64_at(B.Octets.append(t, B.Octets.append(q, r)), _) == B.Octets.be64_at(o, Nat.add(Nat.add(i, 4n), d)) : Maybe<&2, W.W64>}
  %Equal.sym(Maybe<&2, W.W64>, B.Octets.be64_at(B.Octets.append(t, B.Octets.append(q, r)), Nat.add(B.Octets.len(t), Nat.add(B.Octets.len(q), d))), B.Octets.be64_at(B.Octets.append(q, r), Nat.add(B.Octets.len(q), d)), BL.octets_be64_at_append_add(t, B.Octets.append(q, r), Nat.add(B.Octets.len(q), d))) : {_ == B.Octets.be64_at(o, Nat.add(Nat.add(i, 4n), d)) : Maybe<&2, W.W64>}
  %Equal.sym(Maybe<&2, W.W64>, B.Octets.be64_at(B.Octets.append(q, r), Nat.add(B.Octets.len(q), d)), B.Octets.be64_at(r, d), BL.octets_be64_at_append_add(q, r, d)) : {_ == B.Octets.be64_at(o, Nat.add(Nat.add(i, 4n), d)) : Maybe<&2, W.W64>}
  BL.octets_be64_at_drop(Nat.add(i, 4n), o, d)

def Jc.patch_high8(+o: B.Octets, +i: Nat, +v: U32, +d: Nat, h1: {Nat.is_le(Nat.add(i, 4n), B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.at(J.Jbd2.patch32(o, i, v), Nat.add(Nat.add(i, 4n), d)) == B.Octets.at(o, Nat.add(Nat.add(i, 4n), d)) : Maybe<&2, U32>}:
  +t = B.Octets.take(i, o)
  +q = B.Octets.be32(v)
  +r = B.Octets.drop(Nat.add(i, 4n), o)
  %Jc.off_eq(t, q, i, d, BL.octets_len_take_le(i, o, Jc.le_add_l(i, 4n, B.Octets.len(o), h1)), BL.octets_len_be32(v)) : {B.Octets.at(B.Octets.append(t, B.Octets.append(q, r)), _) == B.Octets.at(o, Nat.add(Nat.add(i, 4n), d)) : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.at(B.Octets.append(t, B.Octets.append(q, r)), Nat.add(B.Octets.len(t), Nat.add(B.Octets.len(q), d))), B.Octets.at(B.Octets.append(q, r), Nat.add(B.Octets.len(q), d)), BL.octets_at_append_add(t, B.Octets.append(q, r), Nat.add(B.Octets.len(q), d))) : {_ == B.Octets.at(o, Nat.add(Nat.add(i, 4n), d)) : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.at(B.Octets.append(q, r), Nat.add(B.Octets.len(q), d)), B.Octets.at(r, d), BL.octets_at_append_add(q, r, d)) : {_ == B.Octets.at(o, Nat.add(Nat.add(i, 4n), d)) : Maybe<&2, U32>}
  BL.octets_at_drop(Nat.add(i, 4n), o, d)

def Jc.patch_high_sl(+o: B.Octets, +i: Nat, +v: U32, +d: Nat, +n: Nat, h1: {Nat.is_le(Nat.add(i, 4n), B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.slice(Nat.add(Nat.add(i, 4n), d), n, J.Jbd2.patch32(o, i, v)) == B.Octets.slice(Nat.add(Nat.add(i, 4n), d), n, o) : B.Octets}:
  +t = B.Octets.take(i, o)
  +q = B.Octets.be32(v)
  +r = B.Octets.drop(Nat.add(i, 4n), o)
  %Jc.off_eq(t, q, i, d, BL.octets_len_take_le(i, o, Jc.le_add_l(i, 4n, B.Octets.len(o), h1)), BL.octets_len_be32(v)) : {B.Octets.slice(_, n, B.Octets.append(t, B.Octets.append(q, r))) == B.Octets.slice(Nat.add(Nat.add(i, 4n), d), n, o) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.slice(Nat.add(B.Octets.len(t), Nat.add(B.Octets.len(q), d)), n, B.Octets.append(t, B.Octets.append(q, r))), B.Octets.slice(Nat.add(B.Octets.len(q), d), n, B.Octets.append(q, r)), BL.octets_slice_append_add(t, Nat.add(B.Octets.len(q), d), n, B.Octets.append(q, r))) : {_ == B.Octets.slice(Nat.add(Nat.add(i, 4n), d), n, o) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.slice(Nat.add(B.Octets.len(q), d), n, B.Octets.append(q, r)), B.Octets.slice(d, n, r), BL.octets_slice_append_add(q, d, n, r)) : {_ == B.Octets.slice(Nat.add(Nat.add(i, 4n), d), n, o) : B.Octets}
  BL.octets_slice_drop(Nat.add(i, 4n), d, n, o)

# reads before the patched field (it starts at i, inside o)

def Jc.take_len(+i: Nat, +o: B.Octets, +k: Nat, h1: {Nat.is_le(i, B.Octets.len(o)) == True{} : Bool}, h2: {Nat.is_le(k, i) == True{} : Bool}) -> {Nat.is_le(k, B.Octets.len(B.Octets.take(i, o))) == True{} : Bool}:
  Jc.le_eq(k, B.Octets.len(B.Octets.take(i, o)), i, BL.octets_len_take_le(i, o, h1), h2)

def Jc.patch_low32(+o: B.Octets, +i: Nat, +v: U32, +j: Nat, h1: {Nat.is_le(i, B.Octets.len(o)) == True{} : Bool}, +h2: {Nat.is_le(Nat.add(j, 4n), i) == True{} : Bool}) -> {B.Octets.be32_at(J.Jbd2.patch32(o, i, v), j) == B.Octets.be32_at(o, j) : Maybe<&2, U32>}:
  +t = B.Octets.take(i, o)
  +y = B.Octets.append(B.Octets.be32(v), B.Octets.drop(Nat.add(i, 4n), o))
  Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(t, y), j), B.Octets.be32_at(t, j), B.Octets.be32_at(o, j),
    BL.octets_be32_at_append_le(t, y, j, Jc.take_len(i, o, Nat.add(j, 4n), h1, h2)),
    BL.octets_be32_at_take(i, o, j, h2))

def Jc.patch_low8(+o: B.Octets, +i: Nat, +v: U32, +j: Nat, h1: {Nat.is_le(i, B.Octets.len(o)) == True{} : Bool}, +h2: {Nat.is_lt(j, i) == True{} : Bool}) -> {B.Octets.at(J.Jbd2.patch32(o, i, v), j) == B.Octets.at(o, j) : Maybe<&2, U32>}:
  +t = B.Octets.take(i, o)
  +y = B.Octets.append(B.Octets.be32(v), B.Octets.drop(Nat.add(i, 4n), o))
  Equal.trans(Maybe<&2, U32>, B.Octets.at(B.Octets.append(t, y), j), B.Octets.at(t, j), B.Octets.at(o, j),
    BL.octets_at_append_lt(t, y, j, Equal.trans(Bool, Nat.is_lt(j, B.Octets.len(t)), Nat.is_lt(j, i), True{}, Equal.cong(Nat, Bool, k => Nat.is_lt(j, k), B.Octets.len(t), i, BL.octets_len_take_le(i, o, h1)), h2)),
    BL.octets_at_take(i, o, j, h2))

def Jc.patch_low_sl(+o: B.Octets, +i: Nat, +v: U32, +j: Nat, +n: Nat, h1: {Nat.is_le(i, B.Octets.len(o)) == True{} : Bool}, +h2: {Nat.is_le(Nat.add(j, n), i) == True{} : Bool}) -> {B.Octets.slice(j, n, J.Jbd2.patch32(o, i, v)) == B.Octets.slice(j, n, o) : B.Octets}:
  +t = B.Octets.take(i, o)
  +y = B.Octets.append(B.Octets.be32(v), B.Octets.drop(Nat.add(i, 4n), o))
  Equal.trans(B.Octets, B.Octets.slice(j, n, B.Octets.append(t, y)), B.Octets.slice(j, n, t), B.Octets.slice(j, n, o),
    BL.octets_slice_append_le(j, n, t, y, Jc.take_len(i, o, Nat.add(j, n), h1, h2)),
    BL.octets_slice_take(i, j, n, o, h2))

# a patched string keeps its length
def Jc.patch_len(+o: B.Octets, +i: Nat, +v: U32, +h1: {Nat.is_le(Nat.add(i, 4n), B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.len(J.Jbd2.patch32(o, i, v)) == B.Octets.len(o) : Nat}:
  +x = Nat.sub(B.Octets.len(o), Nat.add(i, 4n))
  Equal.trans(Nat, B.Octets.len(J.Jbd2.patch32(o, i, v)), Nat.add(i, Nat.add(4n, x)), B.Octets.len(o),
    Jc.len2(B.Octets.take(i, o), B.Octets.append(B.Octets.be32(v), B.Octets.drop(Nat.add(i, 4n), o)), i, Nat.add(4n, x), BL.octets_len_take_le(i, o, Jc.le_add_l(i, 4n, B.Octets.len(o), h1)),
      Jc.len2(B.Octets.be32(v), B.Octets.drop(Nat.add(i, 4n), o), 4n, x, BL.octets_len_be32(v), BL.octets_len_drop(Nat.add(i, 4n), o))),
    Equal.trans(Nat, Nat.add(i, Nat.add(4n, x)), Nat.add(Nat.add(i, 4n), x), B.Octets.len(o), Equal.sym(Nat, Nat.add(Nat.add(i, 4n), x), Nat.add(i, Nat.add(4n, x)), Jc.add_assoc(i, 4n, x)), Jc.add_sub(Nat.add(i, 4n), B.Octets.len(o), h1)))

# Block headers: a block of kind k for transaction s starts with them

def Jc.hdr_len(+kind: U32, +seq: U32) -> {B.Octets.len(JB.Jbd2.header(kind, seq)) == 12n : Nat}:
  Jc.len2(B.Octets.be32(J.Jbd2.magic()), B.Octets.append(B.Octets.be32(kind), B.Octets.be32(seq)), 4n, 8n, BL.octets_len_be32(J.Jbd2.magic()), Jc.len2(B.Octets.be32(kind), B.Octets.be32(seq), 4n, 4n, BL.octets_len_be32(kind), BL.octets_len_be32(seq)))

def Jc.hdr_r0(+kind: U32, +seq: U32, +r: B.Octets) -> {B.Octets.be32_at(B.Octets.append(JB.Jbd2.header(kind, seq), r), 0n) == Some{J.Jbd2.magic()} : Maybe<&2, U32>}:
  +m = B.Octets.be32(J.Jbd2.magic())
  +ks = B.Octets.append(B.Octets.be32(kind), B.Octets.be32(seq))
  %Jc.app3(m, ks, r) : {B.Octets.be32_at(_, 0n) == Some{J.Jbd2.magic()} : Maybe<&2, U32>}
  Jc.be32_head(J.Jbd2.magic(), B.Octets.append(ks, r))

def Jc.hdr_r4(+kind: U32, +seq: U32, +r: B.Octets) -> {B.Octets.be32_at(B.Octets.append(JB.Jbd2.header(kind, seq), r), 4n) == Some{kind} : Maybe<&2, U32>}:
  +m = B.Octets.be32(J.Jbd2.magic())
  +k = B.Octets.be32(kind)
  +s = B.Octets.be32(seq)
  %Jc.app3(m, B.Octets.append(k, s), r) : {B.Octets.be32_at(_, 4n) == Some{kind} : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(m, B.Octets.append(B.Octets.append(k, s), r)), Nat.add(4n, 0n)), B.Octets.be32_at(B.Octets.append(B.Octets.append(k, s), r), 0n), Jc.skip32(m, B.Octets.append(B.Octets.append(k, s), r), 4n, 0n, BL.octets_len_be32(J.Jbd2.magic()))) : {_ == Some{kind} : Maybe<&2, U32>}
  %Jc.app3(k, s, r) : {B.Octets.be32_at(_, 0n) == Some{kind} : Maybe<&2, U32>}
  Jc.be32_head(kind, B.Octets.append(s, r))

def Jc.hdr_r8(+kind: U32, +seq: U32, +r: B.Octets) -> {B.Octets.be32_at(B.Octets.append(JB.Jbd2.header(kind, seq), r), 8n) == Some{seq} : Maybe<&2, U32>}:
  +m = B.Octets.be32(J.Jbd2.magic())
  +k = B.Octets.be32(kind)
  +s = B.Octets.be32(seq)
  %Jc.app3(m, B.Octets.append(k, s), r) : {B.Octets.be32_at(_, 8n) == Some{seq} : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(m, B.Octets.append(B.Octets.append(k, s), r)), Nat.add(4n, 4n)), B.Octets.be32_at(B.Octets.append(B.Octets.append(k, s), r), 4n), Jc.skip32(m, B.Octets.append(B.Octets.append(k, s), r), 4n, 4n, BL.octets_len_be32(J.Jbd2.magic()))) : {_ == Some{seq} : Maybe<&2, U32>}
  %Jc.app3(k, s, r) : {B.Octets.be32_at(_, 4n) == Some{seq} : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(k, B.Octets.append(s, r)), Nat.add(4n, 0n)), B.Octets.be32_at(B.Octets.append(s, r), 0n), Jc.skip32(k, B.Octets.append(s, r), 4n, 0n, BL.octets_len_be32(kind))) : {_ == Some{seq} : Maybe<&2, U32>}
  Jc.be32_head(seq, r)

# a block starting with the header of kind k for s is read as kind k for s
def Jc.kind_hdr(+kind: U32, +seq: U32, +r: B.Octets) -> {JB.Jbd2Block.kind(B.Octets.append(JB.Jbd2.header(kind, seq), r), seq) == kind : U32}:
  +x = B.Octets.append(JB.Jbd2.header(kind, seq), r)
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(x, 0n), Some{J.Jbd2.magic()}, Jc.hdr_r0(kind, seq, r)) : {JB.Jbd2Block.kind.pick(Bool.and(U32.is_eq(Maybe.default(&2, U32, _, 0), J.Jbd2.magic()), U32.is_eq(J.Jbd2.be32(x, 8n), seq)), x) == kind : U32}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(x, 8n), Some{seq}, Jc.hdr_r8(kind, seq, r)) : {JB.Jbd2Block.kind.pick(Bool.and(U32.is_eq(J.Jbd2.magic(), J.Jbd2.magic()), U32.is_eq(Maybe.default(&2, U32, _, 0), seq)), x) == kind : U32}
  %Equal.sym(Bool, U32.is_eq(seq, seq), True{}, Jc.u32_refl(seq)) : {JB.Jbd2Block.kind.pick(Bool.and(U32.is_eq(J.Jbd2.magic(), J.Jbd2.magic()), _), x) == kind : U32}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(x, 4n), Some{kind}, Jc.hdr_r4(kind, seq, r)) : {Maybe.default(&2, U32, _, 0) == kind : U32}
  {==}

# a header, a body r1 and padding z, with a tail (sealed) or not
def Jc.kind_seal(b: Bool, +g: J.Jbd2Geom, +kind: U32, +seq: U32, +r1: B.Octets, +z: B.Octets) -> {JB.Jbd2Block.kind(JB.Jbd2Block.seal(b, g, B.Octets.append(B.Octets.append(JB.Jbd2.header(kind, seq), r1), z)), seq) == kind : U32}:
  match b:
    case True{}:
      +h = JB.Jbd2.header(kind, seq)
      +p = B.Octets.append(B.Octets.append(h, r1), z)
      +c = B.Octets.be32(JB.Jbd2Block.tail_csum(g, B.Octets.append(p, B.Octets.zeros(4n))))
      %Jc.app3(B.Octets.append(h, r1), z, c) : {JB.Jbd2Block.kind(_, seq) == kind : U32}
      %Jc.app3(h, r1, B.Octets.append(z, c)) : {JB.Jbd2Block.kind(_, seq) == kind : U32}
      Jc.kind_hdr(kind, seq, B.Octets.append(r1, B.Octets.append(z, c)))
    case False{}:
      %Jc.app3(JB.Jbd2.header(kind, seq), r1, z) : {JB.Jbd2Block.kind(_, seq) == kind : U32}
      Jc.kind_hdr(kind, seq, B.Octets.append(r1, z))

def Laws.jdesc_kind(g, seq, ts, uuid):
  +body = B.Octets.append(JB.Jbd2.header(JB.Jbd2.kind_desc(), seq), B.Octets.concat(JB.Jbd2Desc.tag_bytes(g, ts, uuid, Nil{})))
  Jc.kind_seal(J.Jbd2Geom.has_csum(g), g, 1, seq, B.Octets.concat(JB.Jbd2Desc.tag_bytes(g, ts, uuid, Nil{})), B.Octets.zeros(Nat.sub(Nat.sub(J.Jbd2Geom.bs(g), J.Jbd2Geom.tail(g)), B.Octets.len(body))))

def Laws.jrevoke_kind(g, seq, bs):
  +wide = J.Jbd2Geom.wide(g)
  +count = Nat.add(16n, Nat.mul(List.length(&2, Nat, bs), JB.Jbd2Revoke.entry_size(wide)))
  +r1 = B.Octets.append(B.Octets.be32(U32.from_nat(count)), B.Octets.concat(JB.Jbd2Revoke.entries(bs, wide, Nil{})))
  +body = B.Octets.append(JB.Jbd2.header(JB.Jbd2.kind_revoke(), seq), r1)
  Jc.kind_seal(J.Jbd2Geom.has_csum(g), g, 5, seq, r1, B.Octets.zeros(Nat.sub(Nat.sub(J.Jbd2Geom.bs(g), J.Jbd2Geom.tail(g)), B.Octets.len(body))))

# The commit block

def Jc.commit_r1(+sec: U32, +nsec: U32) -> B.Octets:
  B.Octets.append(B.Octets.zeros(36n), B.Octets.append(B.Octets.be64(W.W64.from_parts(0, sec)), B.Octets.be32(nsec)))

def Jc.commit_body(+seq: U32, +sec: U32, +nsec: U32) -> B.Octets:
  B.Octets.append(JB.Jbd2.header(JB.Jbd2.kind_commit(), seq), Jc.commit_r1(sec, nsec))

def Jc.commit_raw(+g: J.Jbd2Geom, +seq: U32, +sec: U32, +nsec: U32) -> B.Octets:
  B.Octets.append(Jc.commit_body(seq, sec, nsec), B.Octets.zeros(Nat.sub(J.Jbd2Geom.bs(g), B.Octets.len(Jc.commit_body(seq, sec, nsec)))))

def Jc.commit_body_len(+seq: U32, +sec: U32, +nsec: U32) -> {B.Octets.len(Jc.commit_body(seq, sec, nsec)) == 60n : Nat}:
  Jc.len2(JB.Jbd2.header(2, seq), Jc.commit_r1(sec, nsec), 12n, 48n, Jc.hdr_len(2, seq),
    Jc.len2(B.Octets.zeros(36n), B.Octets.append(B.Octets.be64(W.W64.from_parts(0, sec)), B.Octets.be32(nsec)), 36n, 12n, BL.octets_len_zeros(36n),
      Jc.len2(B.Octets.be64(W.W64.from_parts(0, sec)), B.Octets.be32(nsec), 8n, 4n, BL.octets_len_be64(W.W64.from_parts(0, sec)), BL.octets_len_be32(nsec))))

def Jc.commit_raw_len(+g: J.Jbd2Geom, +seq: U32, +sec: U32, +nsec: U32) -> {B.Octets.len(Jc.commit_raw(g, seq, sec, nsec)) == Nat.add(60n, B.Octets.len(B.Octets.zeros(Nat.sub(J.Jbd2Geom.bs(g), B.Octets.len(Jc.commit_body(seq, sec, nsec)))))) : Nat}:
  +z = B.Octets.zeros(Nat.sub(J.Jbd2Geom.bs(g), B.Octets.len(Jc.commit_body(seq, sec, nsec))))
  Jc.len2(Jc.commit_body(seq, sec, nsec), z, 60n, B.Octets.len(z), Jc.commit_body_len(seq, sec, nsec), {==})

def Jc.commit_le(+g: J.Jbd2Geom, +seq: U32, +sec: U32, +nsec: U32, +k: Nat, h: {Nat.is_le(k, 60n) == True{} : Bool}) -> {Nat.is_le(k, B.Octets.len(Jc.commit_raw(g, seq, sec, nsec))) == True{} : Bool}:
  +z = B.Octets.zeros(Nat.sub(J.Jbd2Geom.bs(g), B.Octets.len(Jc.commit_body(seq, sec, nsec))))
  Jc.le_eq(k, B.Octets.len(Jc.commit_raw(g, seq, sec, nsec)), Nat.add(60n, B.Octets.len(z)), Jc.commit_raw_len(g, seq, sec, nsec), Ext4Proof.le_trans(k, 60n, Nat.add(60n, B.Octets.len(z)), h, Jc.le_add_r(60n, B.Octets.len(z))))

# the kind is read from the header, under the checksum's patch
def Jc.kind_eq.pick(b: Bool, +x: B.Octets, +y: B.Octets, e4: {B.Octets.be32_at(x, 4n) == B.Octets.be32_at(y, 4n) : Maybe<&2, U32>}) -> {JB.Jbd2Block.kind.pick(b, x) == JB.Jbd2Block.kind.pick(b, y) : U32}:
  match b:
    case True{}:
      Equal.cong(Maybe<&2, U32>, U32, m => Maybe.default(&2, U32, m, 0), B.Octets.be32_at(x, 4n), B.Octets.be32_at(y, 4n), e4)
    case False{}:
      {==}

def Jc.kind_eq(+x: B.Octets, +y: B.Octets, +seq: U32, e0: {B.Octets.be32_at(x, 0n) == B.Octets.be32_at(y, 0n) : Maybe<&2, U32>}, e4: {B.Octets.be32_at(x, 4n) == B.Octets.be32_at(y, 4n) : Maybe<&2, U32>}, e8: {B.Octets.be32_at(x, 8n) == B.Octets.be32_at(y, 8n) : Maybe<&2, U32>}) -> {JB.Jbd2Block.kind(x, seq) == JB.Jbd2Block.kind(y, seq) : U32}:
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(x, 0n), B.Octets.be32_at(y, 0n), e0) : {JB.Jbd2Block.kind.pick(Bool.and(U32.is_eq(Maybe.default(&2, U32, _, 0), J.Jbd2.magic()), U32.is_eq(J.Jbd2.be32(x, 8n), seq)), x) == JB.Jbd2Block.kind(y, seq) : U32}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(x, 8n), B.Octets.be32_at(y, 8n), e8) : {JB.Jbd2Block.kind.pick(Bool.and(U32.is_eq(J.Jbd2.be32(y, 0n), J.Jbd2.magic()), U32.is_eq(Maybe.default(&2, U32, _, 0), seq)), x) == JB.Jbd2Block.kind(y, seq) : U32}
  Jc.kind_eq.pick(Bool.and(U32.is_eq(J.Jbd2.be32(y, 0n), J.Jbd2.magic()), U32.is_eq(J.Jbd2.be32(y, 8n), seq)), x, y, e4)

def Jc.commit_kind_raw(+g: J.Jbd2Geom, +seq: U32, +sec: U32, +nsec: U32) -> {JB.Jbd2Block.kind(Jc.commit_raw(g, seq, sec, nsec), seq) == 2 : U32}:
  +o = Jc.commit_raw(g, seq, sec, nsec)
  +z = B.Octets.zeros(Nat.sub(J.Jbd2Geom.bs(g), B.Octets.len(Jc.commit_body(seq, sec, nsec))))
  +y = B.Octets.append(JB.Jbd2.header(2, seq), B.Octets.append(Jc.commit_r1(sec, nsec), z))
  Equal.trans(U32, JB.Jbd2Block.kind(o, seq), JB.Jbd2Block.kind(y, seq), 2, Equal.cong(B.Octets, U32, x => JB.Jbd2Block.kind(x, seq), o, y, BL.octets_append_assoc(JB.Jbd2.header(2, seq), Jc.commit_r1(sec, nsec), z)), Jc.kind_hdr(2, seq, B.Octets.append(Jc.commit_r1(sec, nsec), z)))

def Jc.commit_kind(b: Bool, +g: J.Jbd2Geom, +seq: U32, +sec: U32, +nsec: U32) -> {JB.Jbd2Block.kind(JB.Jbd2Commit.seal(b, g, Jc.commit_raw(g, seq, sec, nsec)), seq) == 2 : U32}:
  match b:
    case True{}:
      +o = Jc.commit_raw(g, seq, sec, nsec)
      +h16 = Jc.commit_le(g, seq, sec, nsec, 16n, {==})
      +c = JB.Jbd2Commit.csum(g, o)
      Equal.trans(U32, JB.Jbd2Block.kind(J.Jbd2.patch32(o, 16n, c), seq), JB.Jbd2Block.kind(o, seq), 2,
        Jc.kind_eq(J.Jbd2.patch32(o, 16n, c), o, seq, Jc.patch_low32(o, 16n, c, 0n, h16, {==}), Jc.patch_low32(o, 16n, c, 4n, h16, {==}), Jc.patch_low32(o, 16n, c, 8n, h16, {==})),
        Jc.commit_kind_raw(g, seq, sec, nsec))
    case False{}:
      Jc.commit_kind_raw(g, seq, sec, nsec)

def Laws.jcommit_kind(g, seq, sec, nsec):
  Jc.commit_kind(J.Jbd2Geom.has_csum(g), g, seq, sec, nsec)

# the checksum over a patched commit block is the one over the block
def Jc.commit_csum_patch(+g: J.Jbd2Geom, +o: B.Octets, +v: U32, +h: {Nat.is_le(20n, B.Octets.len(o)) == True{} : Bool}) -> {JB.Jbd2Commit.csum(g, J.Jbd2.patch32(o, 16n, v)) == JB.Jbd2Commit.csum(g, o) : U32}:
  +p = J.Jbd2.patch32(o, 16n, v)
  +s = J.Jbd2Geom.seed(g)
  Equal.trans(U32, JB.Jbd2Commit.csum(g, p), K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(s, B.Octets.take(16n, o)), B.Octets.zeros(4n)), B.Octets.drop(20n, p)), JB.Jbd2Commit.csum(g, o),
    Equal.cong(B.Octets, U32, x => K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(s, x), B.Octets.zeros(4n)), B.Octets.drop(20n, p)), B.Octets.take(16n, p), B.Octets.take(16n, o), Jc.patch_take(o, 16n, v, Jc.le_add_l(16n, 4n, B.Octets.len(o), h))),
    Equal.cong(B.Octets, U32, x => K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(s, B.Octets.take(16n, o)), B.Octets.zeros(4n)), x), B.Octets.drop(20n, p), B.Octets.drop(20n, o), Jc.patch_drop(o, 16n, v, h)))

def Jc.or_not_and_t(+check: Bool, +x: Bool, h: {x == True{} : Bool}) -> {Bool.or(Bool.not(Bool.and(check, True{})), x) == True{} : Bool}:
  match check:
    case True{}:
      h
    case False{}:
      {==}

def Jc.or_not_and_f(+check: Bool, x: Bool) -> {Bool.or(Bool.not(Bool.and(check, False{})), x) == True{} : Bool}:
  match check:
    case True{}:
      {==}
    case False{}:
      {==}

def Jc.commit_ok_t(+check: Bool, +g: J.Jbd2Geom, +o: B.Octets, +h: {Nat.is_le(20n, B.Octets.len(o)) == True{} : Bool}, hb: {J.Jbd2Geom.has_csum(g) == True{} : Bool}) -> {JB.Jbd2Commit.ok(check, g, J.Jbd2.patch32(o, 16n, JB.Jbd2Commit.csum(g, o))) == True{} : Bool}:
  +c = JB.Jbd2Commit.csum(g, o)
  +p = J.Jbd2.patch32(o, 16n, c)
  %Equal.sym(Bool, J.Jbd2Geom.has_csum(g), True{}, hb) : {Bool.or(Bool.not(Bool.and(check, _)), U32.is_eq(JB.Jbd2Commit.csum(g, p), J.Jbd2.be32(p, 16n))) == True{} : Bool}
  %Equal.sym(U32, JB.Jbd2Commit.csum(g, p), c, Jc.commit_csum_patch(g, o, c, h)) : {Bool.or(Bool.not(Bool.and(check, True{})), U32.is_eq(_, J.Jbd2.be32(p, 16n))) == True{} : Bool}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(p, 16n), Some{c}, Jc.patch_same32(o, 16n, c, h)) : {Bool.or(Bool.not(Bool.and(check, True{})), U32.is_eq(c, Maybe.default(&2, U32, _, 0))) == True{} : Bool}
  Jc.or_not_and_t(check, U32.is_eq(c, c), Jc.u32_refl(c))

def Jc.commit_ok_f(+check: Bool, +g: J.Jbd2Geom, +o: B.Octets, hb: {J.Jbd2Geom.has_csum(g) == False{} : Bool}) -> {JB.Jbd2Commit.ok(check, g, o) == True{} : Bool}:
  %Equal.sym(Bool, J.Jbd2Geom.has_csum(g), False{}, hb) : {Bool.or(Bool.not(Bool.and(check, _)), U32.is_eq(JB.Jbd2Commit.csum(g, o), J.Jbd2.be32(o, 16n))) == True{} : Bool}
  Jc.or_not_and_f(check, U32.is_eq(JB.Jbd2Commit.csum(g, o), J.Jbd2.be32(o, 16n)))

# a sealed commit block, its checksum patched in or not (stated so that
# rewriting with them spares the kernel reducing a seal under a read)
def Jc.cseal_t(+g: J.Jbd2Geom, +o: B.Octets) -> {JB.Jbd2Commit.seal(True{}, g, o) == J.Jbd2.patch32(o, 16n, JB.Jbd2Commit.csum(g, o)) : B.Octets}:
  {==}

def Jc.cseal_f(+g: J.Jbd2Geom, +o: B.Octets) -> {JB.Jbd2Commit.seal(False{}, g, o) == o : B.Octets}:
  {==}

def Jc.commit_ok(b: Bool, +check: Bool, +g: J.Jbd2Geom, +o: B.Octets, h: {Nat.is_le(20n, B.Octets.len(o)) == True{} : Bool}) -> {J.Jbd2Geom.has_csum(g) == b : Bool} -> {JB.Jbd2Commit.ok(check, g, JB.Jbd2Commit.seal(b, g, o)) == True{} : Bool}:
  match b:
    case True{}:
      hb =>
        %Equal.sym(B.Octets, JB.Jbd2Commit.seal(True{}, g, o), J.Jbd2.patch32(o, 16n, JB.Jbd2Commit.csum(g, o)), Jc.cseal_t(g, o)) : {JB.Jbd2Commit.ok(check, g, _) == True{} : Bool}
        Jc.commit_ok_t(check, g, o, h, hb)
    case False{}:
      hb =>
        %Equal.sym(B.Octets, JB.Jbd2Commit.seal(False{}, g, o), o, Jc.cseal_f(g, o)) : {JB.Jbd2Commit.ok(check, g, _) == True{} : Bool}
        Jc.commit_ok_f(check, g, o, hb)

# a commit block is its raw block, sealed
def Jc.cenc(+g: J.Jbd2Geom, +seq: U32, +sec: U32, +nsec: U32) -> {JB.Jbd2Commit.encode(g, seq, sec, nsec) == JB.Jbd2Commit.seal(J.Jbd2Geom.has_csum(g), g, Jc.commit_raw(g, seq, sec, nsec)) : B.Octets}:
  {==}

def Laws.jcommit_ok(check, g, seq, sec, nsec):
  %Equal.sym(B.Octets, JB.Jbd2Commit.encode(g, seq, sec, nsec), JB.Jbd2Commit.seal(J.Jbd2Geom.has_csum(g), g, Jc.commit_raw(g, seq, sec, nsec)), Jc.cenc(g, seq, sec, nsec)) : {JB.Jbd2Commit.ok(check, g, _) == True{} : Bool}
  Jc.commit_ok(J.Jbd2Geom.has_csum(g), check, g, Jc.commit_raw(g, seq, sec, nsec), Jc.commit_le(g, seq, sec, nsec, 20n, {==}), {==})

# the time fields, read under the checksum's patch

def Jc.commit_sec_raw(+g: J.Jbd2Geom, +seq: U32, +sec: U32, +nsec: U32) -> {B.Octets.be64_at(Jc.commit_raw(g, seq, sec, nsec), 48n) == Some{W.W64.from_parts(0, sec)} : Maybe<&2, W.W64>}:
  +bd = Jc.commit_body(seq, sec, nsec)
  +z = B.Octets.zeros(Nat.sub(J.Jbd2Geom.bs(g), B.Octets.len(bd)))
  +q = B.Octets.append(B.Octets.be64(W.W64.from_parts(0, sec)), B.Octets.be32(nsec))
  %Equal.sym(Maybe<&2, W.W64>, B.Octets.be64_at(B.Octets.append(bd, z), 48n), B.Octets.be64_at(bd, 48n), BL.octets_be64_at_append_le(bd, z, 48n, Jc.le_eq(56n, B.Octets.len(bd), 60n, Jc.commit_body_len(seq, sec, nsec), {==}))) : {_ == Some{W.W64.from_parts(0, sec)} : Maybe<&2, W.W64>}
  %Equal.sym(Maybe<&2, W.W64>, B.Octets.be64_at(bd, Nat.add(12n, 36n)), B.Octets.be64_at(Jc.commit_r1(sec, nsec), 36n), Jc.skip64(JB.Jbd2.header(2, seq), Jc.commit_r1(sec, nsec), 12n, 36n, Jc.hdr_len(2, seq))) : {_ == Some{W.W64.from_parts(0, sec)} : Maybe<&2, W.W64>}
  %Equal.sym(Maybe<&2, W.W64>, B.Octets.be64_at(Jc.commit_r1(sec, nsec), Nat.add(36n, 0n)), B.Octets.be64_at(q, 0n), Jc.skip64(B.Octets.zeros(36n), q, 36n, 0n, BL.octets_len_zeros(36n))) : {_ == Some{W.W64.from_parts(0, sec)} : Maybe<&2, W.W64>}
  Jc.be64_head(W.W64.from_parts(0, sec), B.Octets.be32(nsec))

def Jc.commit_nsec_raw(+g: J.Jbd2Geom, +seq: U32, +sec: U32, +nsec: U32) -> {B.Octets.be32_at(Jc.commit_raw(g, seq, sec, nsec), 56n) == Some{nsec} : Maybe<&2, U32>}:
  +bd = Jc.commit_body(seq, sec, nsec)
  +z = B.Octets.zeros(Nat.sub(J.Jbd2Geom.bs(g), B.Octets.len(bd)))
  +b8 = B.Octets.be64(W.W64.from_parts(0, sec))
  +q = B.Octets.append(b8, B.Octets.be32(nsec))
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(bd, z), 56n), B.Octets.be32_at(bd, 56n), BL.octets_be32_at_append_le(bd, z, 56n, Jc.le_eq(60n, B.Octets.len(bd), 60n, Jc.commit_body_len(seq, sec, nsec), {==}))) : {_ == Some{nsec} : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(bd, Nat.add(12n, 44n)), B.Octets.be32_at(Jc.commit_r1(sec, nsec), 44n), Jc.skip32(JB.Jbd2.header(2, seq), Jc.commit_r1(sec, nsec), 12n, 44n, Jc.hdr_len(2, seq))) : {_ == Some{nsec} : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(Jc.commit_r1(sec, nsec), Nat.add(36n, 8n)), B.Octets.be32_at(q, 8n), Jc.skip32(B.Octets.zeros(36n), q, 36n, 8n, BL.octets_len_zeros(36n))) : {_ == Some{nsec} : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(q, Nat.add(8n, 0n)), B.Octets.be32_at(B.Octets.be32(nsec), 0n), Jc.skip32(b8, B.Octets.be32(nsec), 8n, 0n, BL.octets_len_be64(W.W64.from_parts(0, sec)))) : {_ == Some{nsec} : Maybe<&2, U32>}
  BL.octets_be32_round_trip(nsec)

def Jc.commit_sec(b: Bool, +g: J.Jbd2Geom, +seq: U32, +sec: U32, +nsec: U32) -> {B.Octets.be64_at(JB.Jbd2Commit.seal(b, g, Jc.commit_raw(g, seq, sec, nsec)), 48n) == Some{W.W64.from_parts(0, sec)} : Maybe<&2, W.W64>}:
  match b:
    case True{}:
      +o = Jc.commit_raw(g, seq, sec, nsec)
      +c = JB.Jbd2Commit.csum(g, o)
      Equal.trans(Maybe<&2, W.W64>, B.Octets.be64_at(J.Jbd2.patch32(o, 16n, c), Nat.add(Nat.add(16n, 4n), 28n)), B.Octets.be64_at(o, 48n), Some{W.W64.from_parts(0, sec)},
        Jc.patch_high64(o, 16n, c, 28n, Jc.commit_le(g, seq, sec, nsec, 20n, {==})),
        Jc.commit_sec_raw(g, seq, sec, nsec))
    case False{}:
      Jc.commit_sec_raw(g, seq, sec, nsec)

def Jc.commit_nsec(b: Bool, +g: J.Jbd2Geom, +seq: U32, +sec: U32, +nsec: U32) -> {B.Octets.be32_at(JB.Jbd2Commit.seal(b, g, Jc.commit_raw(g, seq, sec, nsec)), 56n) == Some{nsec} : Maybe<&2, U32>}:
  match b:
    case True{}:
      +o = Jc.commit_raw(g, seq, sec, nsec)
      +c = JB.Jbd2Commit.csum(g, o)
      Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(J.Jbd2.patch32(o, 16n, c), Nat.add(Nat.add(16n, 4n), 36n)), B.Octets.be32_at(o, 56n), Some{nsec},
        Jc.patch_high32(o, 16n, c, 36n, Jc.commit_le(g, seq, sec, nsec, 20n, {==})),
        Jc.commit_nsec_raw(g, seq, sec, nsec))
    case False{}:
      Jc.commit_nsec_raw(g, seq, sec, nsec)

def Laws.jcommit_sec(g, seq, sec, nsec):
  Jc.commit_sec(J.Jbd2Geom.has_csum(g), g, seq, sec, nsec)

def Laws.jcommit_nsec(g, seq, sec, nsec):
  Jc.commit_nsec(J.Jbd2Geom.has_csum(g), g, seq, sec, nsec)

# The journal superblock after with_log: two fields patched (24, 28), then
# with checksums the checksum patched (252)

def Jc.wl_x(+o: B.Octets, +start: Nat, +seq: U32) -> B.Octets:
  J.Jbd2.patch32(J.Jbd2.patch32(o, 24n, seq), 28n, U32.from_nat(start))

def Jc.wl_shape(+o: B.Octets, +start: Nat, +seq: U32) -> {J.Jbd2Super.with_log(o, start, seq) == J.Jbd2Super.reseal(J.Jbd2Super.has_csum(J.Jbd2Super.parse(o)), Jc.wl_x(o, start, seq)) : B.Octets}:
  {==}

def Jc.rs_t(+o: B.Octets) -> {J.Jbd2Super.reseal(True{}, o) == J.Jbd2.patch32(o, 252n, J.Jbd2Super.csum(o)) : B.Octets}:
  {==}

def Jc.rs_f(+o: B.Octets) -> {J.Jbd2Super.reseal(False{}, o) == o : B.Octets}:
  {==}

def Jc.le256(+k: Nat, +o: B.Octets, +h: {Nat.is_le(256n, B.Octets.len(o)) == True{} : Bool}, hk: {Nat.is_le(k, 256n) == True{} : Bool}) -> {Nat.is_le(k, B.Octets.len(o)) == True{} : Bool}:
  Ext4Proof.le_trans(k, 256n, B.Octets.len(o), hk, h)

# the length a patch keeps, as a bound
def Jc.patch_le(+o: B.Octets, +i: Nat, +v: U32, +k: Nat, +h: {Nat.is_le(Nat.add(i, 4n), B.Octets.len(o)) == True{} : Bool}, hk: {Nat.is_le(k, B.Octets.len(o)) == True{} : Bool}) -> {Nat.is_le(k, B.Octets.len(J.Jbd2.patch32(o, i, v))) == True{} : Bool}:
  Jc.le_eq(k, B.Octets.len(J.Jbd2.patch32(o, i, v)), B.Octets.len(o), Jc.patch_len(o, i, v, h), hk)

# reads through the checksum's patch, below it
def Jc.rs_r32(b: Bool, +x: B.Octets, +j: Nat, +h: {Nat.is_le(256n, B.Octets.len(x)) == True{} : Bool}, +hj: {Nat.is_le(Nat.add(j, 4n), 252n) == True{} : Bool}) -> {B.Octets.be32_at(J.Jbd2Super.reseal(b, x), j) == B.Octets.be32_at(x, j) : Maybe<&2, U32>}:
  match b:
    case True{}:
      %Equal.sym(B.Octets, J.Jbd2Super.reseal(True{}, x), J.Jbd2.patch32(x, 252n, J.Jbd2Super.csum(x)), Jc.rs_t(x)) : {B.Octets.be32_at(_, j) == B.Octets.be32_at(x, j) : Maybe<&2, U32>}
      Jc.patch_low32(x, 252n, J.Jbd2Super.csum(x), j, Jc.le256(252n, x, h, {==}), hj)
    case False{}:
      %Equal.sym(B.Octets, J.Jbd2Super.reseal(False{}, x), x, Jc.rs_f(x)) : {B.Octets.be32_at(_, j) == B.Octets.be32_at(x, j) : Maybe<&2, U32>}
      {==}

def Jc.rs_r8(b: Bool, +x: B.Octets, +j: Nat, +h: {Nat.is_le(256n, B.Octets.len(x)) == True{} : Bool}, +hj: {Nat.is_lt(j, 252n) == True{} : Bool}) -> {B.Octets.at(J.Jbd2Super.reseal(b, x), j) == B.Octets.at(x, j) : Maybe<&2, U32>}:
  match b:
    case True{}:
      %Equal.sym(B.Octets, J.Jbd2Super.reseal(True{}, x), J.Jbd2.patch32(x, 252n, J.Jbd2Super.csum(x)), Jc.rs_t(x)) : {B.Octets.at(_, j) == B.Octets.at(x, j) : Maybe<&2, U32>}
      Jc.patch_low8(x, 252n, J.Jbd2Super.csum(x), j, Jc.le256(252n, x, h, {==}), hj)
    case False{}:
      %Equal.sym(B.Octets, J.Jbd2Super.reseal(False{}, x), x, Jc.rs_f(x)) : {B.Octets.at(_, j) == B.Octets.at(x, j) : Maybe<&2, U32>}
      {==}

def Jc.rs_sl(b: Bool, +x: B.Octets, +j: Nat, +n: Nat, +h: {Nat.is_le(256n, B.Octets.len(x)) == True{} : Bool}, +hj: {Nat.is_le(Nat.add(j, n), 252n) == True{} : Bool}) -> {B.Octets.slice(j, n, J.Jbd2Super.reseal(b, x)) == B.Octets.slice(j, n, x) : B.Octets}:
  match b:
    case True{}:
      %Equal.sym(B.Octets, J.Jbd2Super.reseal(True{}, x), J.Jbd2.patch32(x, 252n, J.Jbd2Super.csum(x)), Jc.rs_t(x)) : {B.Octets.slice(j, n, _) == B.Octets.slice(j, n, x) : B.Octets}
      Jc.patch_low_sl(x, 252n, J.Jbd2Super.csum(x), j, n, Jc.le256(252n, x, h, {==}), hj)
    case False{}:
      %Equal.sym(B.Octets, J.Jbd2Super.reseal(False{}, x), x, Jc.rs_f(x)) : {B.Octets.slice(j, n, _) == B.Octets.slice(j, n, x) : B.Octets}
      {==}

# the two log fields patched: its length, and reads

def Jc.wl_len(+o: B.Octets, +start: Nat, +seq: U32, +h: {Nat.is_le(256n, B.Octets.len(o)) == True{} : Bool}) -> {Nat.is_le(256n, B.Octets.len(Jc.wl_x(o, start, seq))) == True{} : Bool}:
  +x1 = J.Jbd2.patch32(o, 24n, seq)
  +h1 = Jc.patch_le(o, 24n, seq, 256n, Jc.le256(28n, o, h, {==}), h)
  Jc.patch_le(x1, 28n, U32.from_nat(start), 256n, Ext4Proof.le_trans(32n, 256n, B.Octets.len(x1), {==}, h1), h1)

def Jc.wl_low32(+o: B.Octets, +start: Nat, +seq: U32, +j: Nat, +h: {Nat.is_le(256n, B.Octets.len(o)) == True{} : Bool}, +hj: {Nat.is_le(Nat.add(j, 4n), 24n) == True{} : Bool}) -> {B.Octets.be32_at(Jc.wl_x(o, start, seq), j) == B.Octets.be32_at(o, j) : Maybe<&2, U32>}:
  +x1 = J.Jbd2.patch32(o, 24n, seq)
  +h1 = Jc.patch_le(o, 24n, seq, 256n, Jc.le256(28n, o, h, {==}), h)
  Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(Jc.wl_x(o, start, seq), j), B.Octets.be32_at(x1, j), B.Octets.be32_at(o, j),
    Jc.patch_low32(x1, 28n, U32.from_nat(start), j, Ext4Proof.le_trans(28n, 256n, B.Octets.len(x1), {==}, h1), Ext4Proof.le_trans(Nat.add(j, 4n), 24n, 28n, hj, {==})),
    Jc.patch_low32(o, 24n, seq, j, Jc.le256(24n, o, h, {==}), hj))

def Jc.wl_high32(+o: B.Octets, +start: Nat, +seq: U32, +d: Nat, +h: {Nat.is_le(256n, B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.be32_at(Jc.wl_x(o, start, seq), Nat.add(32n, d)) == B.Octets.be32_at(o, Nat.add(32n, d)) : Maybe<&2, U32>}:
  +x1 = J.Jbd2.patch32(o, 24n, seq)
  +h1 = Jc.patch_le(o, 24n, seq, 256n, Jc.le256(28n, o, h, {==}), h)
  Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(Jc.wl_x(o, start, seq), Nat.add(Nat.add(28n, 4n), d)), B.Octets.be32_at(x1, Nat.add(Nat.add(24n, 4n), Nat.add(4n, d))), B.Octets.be32_at(o, Nat.add(Nat.add(24n, 4n), Nat.add(4n, d))),
    Jc.patch_high32(x1, 28n, U32.from_nat(start), d, Ext4Proof.le_trans(32n, 256n, B.Octets.len(x1), {==}, h1)),
    Jc.patch_high32(o, 24n, seq, Nat.add(4n, d), Jc.le256(28n, o, h, {==})))

def Jc.wl_high8(+o: B.Octets, +start: Nat, +seq: U32, +d: Nat, +h: {Nat.is_le(256n, B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.at(Jc.wl_x(o, start, seq), Nat.add(32n, d)) == B.Octets.at(o, Nat.add(32n, d)) : Maybe<&2, U32>}:
  +x1 = J.Jbd2.patch32(o, 24n, seq)
  +h1 = Jc.patch_le(o, 24n, seq, 256n, Jc.le256(28n, o, h, {==}), h)
  Equal.trans(Maybe<&2, U32>, B.Octets.at(Jc.wl_x(o, start, seq), Nat.add(Nat.add(28n, 4n), d)), B.Octets.at(x1, Nat.add(Nat.add(24n, 4n), Nat.add(4n, d))), B.Octets.at(o, Nat.add(Nat.add(24n, 4n), Nat.add(4n, d))),
    Jc.patch_high8(x1, 28n, U32.from_nat(start), d, Ext4Proof.le_trans(32n, 256n, B.Octets.len(x1), {==}, h1)),
    Jc.patch_high8(o, 24n, seq, Nat.add(4n, d), Jc.le256(28n, o, h, {==})))

def Jc.wl_high_sl(+o: B.Octets, +start: Nat, +seq: U32, +d: Nat, +n: Nat, +h: {Nat.is_le(256n, B.Octets.len(o)) == True{} : Bool}) -> {B.Octets.slice(Nat.add(32n, d), n, Jc.wl_x(o, start, seq)) == B.Octets.slice(Nat.add(32n, d), n, o) : B.Octets}:
  +x1 = J.Jbd2.patch32(o, 24n, seq)
  +h1 = Jc.patch_le(o, 24n, seq, 256n, Jc.le256(28n, o, h, {==}), h)
  Equal.trans(B.Octets, B.Octets.slice(Nat.add(Nat.add(28n, 4n), d), n, Jc.wl_x(o, start, seq)), B.Octets.slice(Nat.add(Nat.add(24n, 4n), Nat.add(4n, d)), n, x1), B.Octets.slice(Nat.add(Nat.add(24n, 4n), Nat.add(4n, d)), n, o),
    Jc.patch_high_sl(x1, 28n, U32.from_nat(start), d, n, Ext4Proof.le_trans(32n, 256n, B.Octets.len(x1), {==}, h1)),
    Jc.patch_high_sl(o, 24n, seq, Nat.add(4n, d), n, Jc.le256(28n, o, h, {==})))

# The superblock's fields but the three with_log sets, as reads

def Jc.d32(m: Maybe<&2, U32>) -> U32:
  Maybe.default(&2, U32, m, 0)

def Jc.rec_t(a4: Maybe<&2, U32>, a12: Maybe<&2, U32>, a16: Maybe<&2, U32>, a20: Maybe<&2, U32>, a32: Maybe<&2, U32>, a36: Maybe<&2, U32>, a40: Maybe<&2, U32>, a44: Maybe<&2, U32>, s48: B.Octets, a80: Maybe<&2, U32>) -> J.Jbd2Super:
  J.Jbd2Super{Jc.d32(a4), U32.to_nat(Jc.d32(a12)), U32.to_nat(Jc.d32(a16)), U32.to_nat(Jc.d32(a20)), 0, 0n, Jc.d32(a32), Jc.d32(a36), Jc.d32(a40), Jc.d32(a44), s48, Jc.d32(a80), 0}

def Jc.rec_f(a4: Maybe<&2, U32>, a12: Maybe<&2, U32>, a16: Maybe<&2, U32>, a20: Maybe<&2, U32>, a32: Maybe<&2, U32>, s48: B.Octets) -> J.Jbd2Super:
  J.Jbd2Super{Jc.d32(a4), U32.to_nat(Jc.d32(a12)), U32.to_nat(Jc.d32(a16)), U32.to_nat(Jc.d32(a20)), 0, 0n, Jc.d32(a32), 0, 0, 0, s48, 0, 0}

def Jc.fx_t(+x: B.Octets) -> {J.Jbd2Super.fixed(J.Jbd2Super.parse.go(True{}, x)) == Jc.rec_t(B.Octets.be32_at(x, 4n), B.Octets.be32_at(x, 12n), B.Octets.be32_at(x, 16n), B.Octets.be32_at(x, 20n), B.Octets.be32_at(x, 32n), B.Octets.be32_at(x, 36n), B.Octets.be32_at(x, 40n), B.Octets.be32_at(x, 44n), B.Octets.slice(48n, 16n, x), B.Octets.at(x, 80n)) : J.Jbd2Super}:
  {==}

def Jc.fx_f(+x: B.Octets) -> {J.Jbd2Super.fixed(J.Jbd2Super.parse.go(False{}, x)) == Jc.rec_f(B.Octets.be32_at(x, 4n), B.Octets.be32_at(x, 12n), B.Octets.be32_at(x, 16n), B.Octets.be32_at(x, 20n), B.Octets.be32_at(x, 32n), B.Octets.slice(48n, 16n, x)) : J.Jbd2Super}:
  {==}

def Jc.parse_go(+x: B.Octets) -> {J.Jbd2Super.parse(x) == J.Jbd2Super.parse.go(U32.is_eq(Jc.d32(B.Octets.be32_at(x, 4n)), 4), x) : J.Jbd2Super}:
  {==}

def Jc.rec_t_eq(+a4: Maybe<&2, U32>, +a12: Maybe<&2, U32>, +a16: Maybe<&2, U32>, +a20: Maybe<&2, U32>, +a32: Maybe<&2, U32>, +a36: Maybe<&2, U32>, +a40: Maybe<&2, U32>, +a44: Maybe<&2, U32>, +s48: B.Octets, +a80: Maybe<&2, U32>, +b4: Maybe<&2, U32>, +b12: Maybe<&2, U32>, +b16: Maybe<&2, U32>, +b20: Maybe<&2, U32>, +b32: Maybe<&2, U32>, +b36: Maybe<&2, U32>, +b40: Maybe<&2, U32>, +b44: Maybe<&2, U32>, +t48: B.Octets, +b80: Maybe<&2, U32>, e4: {a4 == b4 : Maybe<&2, U32>}, e12: {a12 == b12 : Maybe<&2, U32>}, e16: {a16 == b16 : Maybe<&2, U32>}, e20: {a20 == b20 : Maybe<&2, U32>}, e32: {a32 == b32 : Maybe<&2, U32>}, e36: {a36 == b36 : Maybe<&2, U32>}, e40: {a40 == b40 : Maybe<&2, U32>}, e44: {a44 == b44 : Maybe<&2, U32>}, e48: {s48 == t48 : B.Octets}, e80: {a80 == b80 : Maybe<&2, U32>}) -> {Jc.rec_t(a4, a12, a16, a20, a32, a36, a40, a44, s48, a80) == Jc.rec_t(b4, b12, b16, b20, b32, b36, b40, b44, t48, b80) : J.Jbd2Super}:
  %e4 : {Jc.rec_t(a4, a12, a16, a20, a32, a36, a40, a44, s48, a80) == Jc.rec_t(_, b12, b16, b20, b32, b36, b40, b44, t48, b80) : J.Jbd2Super}
  %e12 : {Jc.rec_t(a4, a12, a16, a20, a32, a36, a40, a44, s48, a80) == Jc.rec_t(a4, _, b16, b20, b32, b36, b40, b44, t48, b80) : J.Jbd2Super}
  %e16 : {Jc.rec_t(a4, a12, a16, a20, a32, a36, a40, a44, s48, a80) == Jc.rec_t(a4, a12, _, b20, b32, b36, b40, b44, t48, b80) : J.Jbd2Super}
  %e20 : {Jc.rec_t(a4, a12, a16, a20, a32, a36, a40, a44, s48, a80) == Jc.rec_t(a4, a12, a16, _, b32, b36, b40, b44, t48, b80) : J.Jbd2Super}
  %e32 : {Jc.rec_t(a4, a12, a16, a20, a32, a36, a40, a44, s48, a80) == Jc.rec_t(a4, a12, a16, a20, _, b36, b40, b44, t48, b80) : J.Jbd2Super}
  %e36 : {Jc.rec_t(a4, a12, a16, a20, a32, a36, a40, a44, s48, a80) == Jc.rec_t(a4, a12, a16, a20, a32, _, b40, b44, t48, b80) : J.Jbd2Super}
  %e40 : {Jc.rec_t(a4, a12, a16, a20, a32, a36, a40, a44, s48, a80) == Jc.rec_t(a4, a12, a16, a20, a32, a36, _, b44, t48, b80) : J.Jbd2Super}
  %e44 : {Jc.rec_t(a4, a12, a16, a20, a32, a36, a40, a44, s48, a80) == Jc.rec_t(a4, a12, a16, a20, a32, a36, a40, _, t48, b80) : J.Jbd2Super}
  %e48 : {Jc.rec_t(a4, a12, a16, a20, a32, a36, a40, a44, s48, a80) == Jc.rec_t(a4, a12, a16, a20, a32, a36, a40, a44, _, b80) : J.Jbd2Super}
  %e80 : {Jc.rec_t(a4, a12, a16, a20, a32, a36, a40, a44, s48, a80) == Jc.rec_t(a4, a12, a16, a20, a32, a36, a40, a44, s48, _) : J.Jbd2Super}
  {==}

def Jc.rec_f_eq(+a4: Maybe<&2, U32>, +a12: Maybe<&2, U32>, +a16: Maybe<&2, U32>, +a20: Maybe<&2, U32>, +a32: Maybe<&2, U32>, +s48: B.Octets, +b4: Maybe<&2, U32>, +b12: Maybe<&2, U32>, +b16: Maybe<&2, U32>, +b20: Maybe<&2, U32>, +b32: Maybe<&2, U32>, +t48: B.Octets, e4: {a4 == b4 : Maybe<&2, U32>}, e12: {a12 == b12 : Maybe<&2, U32>}, e16: {a16 == b16 : Maybe<&2, U32>}, e20: {a20 == b20 : Maybe<&2, U32>}, e32: {a32 == b32 : Maybe<&2, U32>}, e48: {s48 == t48 : B.Octets}) -> {Jc.rec_f(a4, a12, a16, a20, a32, s48) == Jc.rec_f(b4, b12, b16, b20, b32, t48) : J.Jbd2Super}:
  %e4 : {Jc.rec_f(a4, a12, a16, a20, a32, s48) == Jc.rec_f(_, b12, b16, b20, b32, t48) : J.Jbd2Super}
  %e12 : {Jc.rec_f(a4, a12, a16, a20, a32, s48) == Jc.rec_f(a4, _, b16, b20, b32, t48) : J.Jbd2Super}
  %e16 : {Jc.rec_f(a4, a12, a16, a20, a32, s48) == Jc.rec_f(a4, a12, _, b20, b32, t48) : J.Jbd2Super}
  %e20 : {Jc.rec_f(a4, a12, a16, a20, a32, s48) == Jc.rec_f(a4, a12, a16, _, b32, t48) : J.Jbd2Super}
  %e32 : {Jc.rec_f(a4, a12, a16, a20, a32, s48) == Jc.rec_f(a4, a12, a16, a20, _, t48) : J.Jbd2Super}
  %e48 : {Jc.rec_f(a4, a12, a16, a20, a32, s48) == Jc.rec_f(a4, a12, a16, a20, a32, _) : J.Jbd2Super}
  {==}

def Jc.fixed_go(b: Bool, +x: B.Octets, +y: B.Octets, +e4: {B.Octets.be32_at(x, 4n) == B.Octets.be32_at(y, 4n) : Maybe<&2, U32>}, +e12: {B.Octets.be32_at(x, 12n) == B.Octets.be32_at(y, 12n) : Maybe<&2, U32>}, +e16: {B.Octets.be32_at(x, 16n) == B.Octets.be32_at(y, 16n) : Maybe<&2, U32>}, +e20: {B.Octets.be32_at(x, 20n) == B.Octets.be32_at(y, 20n) : Maybe<&2, U32>}, +e32: {B.Octets.be32_at(x, 32n) == B.Octets.be32_at(y, 32n) : Maybe<&2, U32>}, e36: {B.Octets.be32_at(x, 36n) == B.Octets.be32_at(y, 36n) : Maybe<&2, U32>}, e40: {B.Octets.be32_at(x, 40n) == B.Octets.be32_at(y, 40n) : Maybe<&2, U32>}, e44: {B.Octets.be32_at(x, 44n) == B.Octets.be32_at(y, 44n) : Maybe<&2, U32>}, +e48: {B.Octets.slice(48n, 16n, x) == B.Octets.slice(48n, 16n, y) : B.Octets}, e80: {B.Octets.at(x, 80n) == B.Octets.at(y, 80n) : Maybe<&2, U32>}) -> {J.Jbd2Super.fixed(J.Jbd2Super.parse.go(b, x)) == J.Jbd2Super.fixed(J.Jbd2Super.parse.go(b, y)) : J.Jbd2Super}:
  match b:
    case True{}:
      +rx = Jc.rec_t(B.Octets.be32_at(x, 4n), B.Octets.be32_at(x, 12n), B.Octets.be32_at(x, 16n), B.Octets.be32_at(x, 20n), B.Octets.be32_at(x, 32n), B.Octets.be32_at(x, 36n), B.Octets.be32_at(x, 40n), B.Octets.be32_at(x, 44n), B.Octets.slice(48n, 16n, x), B.Octets.at(x, 80n))
      +ry = Jc.rec_t(B.Octets.be32_at(y, 4n), B.Octets.be32_at(y, 12n), B.Octets.be32_at(y, 16n), B.Octets.be32_at(y, 20n), B.Octets.be32_at(y, 32n), B.Octets.be32_at(y, 36n), B.Octets.be32_at(y, 40n), B.Octets.be32_at(y, 44n), B.Octets.slice(48n, 16n, y), B.Octets.at(y, 80n))
      Equal.trans(J.Jbd2Super, J.Jbd2Super.fixed(J.Jbd2Super.parse.go(True{}, x)), rx, J.Jbd2Super.fixed(J.Jbd2Super.parse.go(True{}, y)), Jc.fx_t(x),
        Equal.trans(J.Jbd2Super, rx, ry, J.Jbd2Super.fixed(J.Jbd2Super.parse.go(True{}, y)),
          Jc.rec_t_eq(B.Octets.be32_at(x, 4n), B.Octets.be32_at(x, 12n), B.Octets.be32_at(x, 16n), B.Octets.be32_at(x, 20n), B.Octets.be32_at(x, 32n), B.Octets.be32_at(x, 36n), B.Octets.be32_at(x, 40n), B.Octets.be32_at(x, 44n), B.Octets.slice(48n, 16n, x), B.Octets.at(x, 80n), B.Octets.be32_at(y, 4n), B.Octets.be32_at(y, 12n), B.Octets.be32_at(y, 16n), B.Octets.be32_at(y, 20n), B.Octets.be32_at(y, 32n), B.Octets.be32_at(y, 36n), B.Octets.be32_at(y, 40n), B.Octets.be32_at(y, 44n), B.Octets.slice(48n, 16n, y), B.Octets.at(y, 80n), e4, e12, e16, e20, e32, e36, e40, e44, e48, e80),
          Equal.sym(J.Jbd2Super, J.Jbd2Super.fixed(J.Jbd2Super.parse.go(True{}, y)), ry, Jc.fx_t(y))))
    case False{}:
      +rx = Jc.rec_f(B.Octets.be32_at(x, 4n), B.Octets.be32_at(x, 12n), B.Octets.be32_at(x, 16n), B.Octets.be32_at(x, 20n), B.Octets.be32_at(x, 32n), B.Octets.slice(48n, 16n, x))
      +ry = Jc.rec_f(B.Octets.be32_at(y, 4n), B.Octets.be32_at(y, 12n), B.Octets.be32_at(y, 16n), B.Octets.be32_at(y, 20n), B.Octets.be32_at(y, 32n), B.Octets.slice(48n, 16n, y))
      Equal.trans(J.Jbd2Super, J.Jbd2Super.fixed(J.Jbd2Super.parse.go(False{}, x)), rx, J.Jbd2Super.fixed(J.Jbd2Super.parse.go(False{}, y)), Jc.fx_f(x),
        Equal.trans(J.Jbd2Super, rx, ry, J.Jbd2Super.fixed(J.Jbd2Super.parse.go(False{}, y)),
          Jc.rec_f_eq(B.Octets.be32_at(x, 4n), B.Octets.be32_at(x, 12n), B.Octets.be32_at(x, 16n), B.Octets.be32_at(x, 20n), B.Octets.be32_at(x, 32n), B.Octets.slice(48n, 16n, x), B.Octets.be32_at(y, 4n), B.Octets.be32_at(y, 12n), B.Octets.be32_at(y, 16n), B.Octets.be32_at(y, 20n), B.Octets.be32_at(y, 32n), B.Octets.slice(48n, 16n, y), e4, e12, e16, e20, e32, e48),
          Equal.sym(J.Jbd2Super, J.Jbd2Super.fixed(J.Jbd2Super.parse.go(False{}, y)), ry, Jc.fx_f(y))))

def Jc.fixed_eq(+x: B.Octets, +y: B.Octets, +e4: {B.Octets.be32_at(x, 4n) == B.Octets.be32_at(y, 4n) : Maybe<&2, U32>}, e12: {B.Octets.be32_at(x, 12n) == B.Octets.be32_at(y, 12n) : Maybe<&2, U32>}, e16: {B.Octets.be32_at(x, 16n) == B.Octets.be32_at(y, 16n) : Maybe<&2, U32>}, e20: {B.Octets.be32_at(x, 20n) == B.Octets.be32_at(y, 20n) : Maybe<&2, U32>}, e32: {B.Octets.be32_at(x, 32n) == B.Octets.be32_at(y, 32n) : Maybe<&2, U32>}, e36: {B.Octets.be32_at(x, 36n) == B.Octets.be32_at(y, 36n) : Maybe<&2, U32>}, e40: {B.Octets.be32_at(x, 40n) == B.Octets.be32_at(y, 40n) : Maybe<&2, U32>}, e44: {B.Octets.be32_at(x, 44n) == B.Octets.be32_at(y, 44n) : Maybe<&2, U32>}, e48: {B.Octets.slice(48n, 16n, x) == B.Octets.slice(48n, 16n, y) : B.Octets}, e80: {B.Octets.at(x, 80n) == B.Octets.at(y, 80n) : Maybe<&2, U32>}) -> {J.Jbd2Super.fixed(J.Jbd2Super.parse(x)) == J.Jbd2Super.fixed(J.Jbd2Super.parse(y)) : J.Jbd2Super}:
  +vy = U32.is_eq(Jc.d32(B.Octets.be32_at(y, 4n)), 4)
  %Equal.sym(J.Jbd2Super, J.Jbd2Super.parse(x), J.Jbd2Super.parse.go(U32.is_eq(Jc.d32(B.Octets.be32_at(x, 4n)), 4), x), Jc.parse_go(x)) : {J.Jbd2Super.fixed(_) == J.Jbd2Super.fixed(J.Jbd2Super.parse(y)) : J.Jbd2Super}
  %Equal.sym(J.Jbd2Super, J.Jbd2Super.parse(y), J.Jbd2Super.parse.go(vy, y), Jc.parse_go(y)) : {J.Jbd2Super.fixed(J.Jbd2Super.parse.go(U32.is_eq(Jc.d32(B.Octets.be32_at(x, 4n)), 4), x)) == J.Jbd2Super.fixed(_) : J.Jbd2Super}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(x, 4n), B.Octets.be32_at(y, 4n), e4) : {J.Jbd2Super.fixed(J.Jbd2Super.parse.go(U32.is_eq(Jc.d32(_), 4), x)) == J.Jbd2Super.fixed(J.Jbd2Super.parse.go(vy, y)) : J.Jbd2Super}
  Jc.fixed_go(vy, x, y, e4, e12, e16, e20, e32, e36, e40, e44, e48, e80)

def Laws.jsuper_log_fixed(o, start, seq, h):
  +b = J.Jbd2Super.has_csum(J.Jbd2Super.parse(o))
  +x = Jc.wl_x(o, start, seq)
  +w = J.Jbd2Super.reseal(b, x)
  +hx = Jc.wl_len(o, start, seq, h)
  %Equal.sym(B.Octets, J.Jbd2Super.with_log(o, start, seq), w, Jc.wl_shape(o, start, seq)) : {J.Jbd2Super.fixed(J.Jbd2Super.parse(_)) == J.Jbd2Super.fixed(J.Jbd2Super.parse(o)) : J.Jbd2Super}
  Jc.fixed_eq(w, o,
    Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(w, 4n), B.Octets.be32_at(x, 4n), B.Octets.be32_at(o, 4n), Jc.rs_r32(b, x, 4n, hx, {==}), Jc.wl_low32(o, start, seq, 4n, h, {==})),
    Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(w, 12n), B.Octets.be32_at(x, 12n), B.Octets.be32_at(o, 12n), Jc.rs_r32(b, x, 12n, hx, {==}), Jc.wl_low32(o, start, seq, 12n, h, {==})),
    Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(w, 16n), B.Octets.be32_at(x, 16n), B.Octets.be32_at(o, 16n), Jc.rs_r32(b, x, 16n, hx, {==}), Jc.wl_low32(o, start, seq, 16n, h, {==})),
    Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(w, 20n), B.Octets.be32_at(x, 20n), B.Octets.be32_at(o, 20n), Jc.rs_r32(b, x, 20n, hx, {==}), Jc.wl_low32(o, start, seq, 20n, h, {==})),
    Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(w, 32n), B.Octets.be32_at(x, 32n), B.Octets.be32_at(o, 32n), Jc.rs_r32(b, x, 32n, hx, {==}), Jc.wl_high32(o, start, seq, 0n, h)),
    Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(w, 36n), B.Octets.be32_at(x, 36n), B.Octets.be32_at(o, 36n), Jc.rs_r32(b, x, 36n, hx, {==}), Jc.wl_high32(o, start, seq, 4n, h)),
    Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(w, 40n), B.Octets.be32_at(x, 40n), B.Octets.be32_at(o, 40n), Jc.rs_r32(b, x, 40n, hx, {==}), Jc.wl_high32(o, start, seq, 8n, h)),
    Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(w, 44n), B.Octets.be32_at(x, 44n), B.Octets.be32_at(o, 44n), Jc.rs_r32(b, x, 44n, hx, {==}), Jc.wl_high32(o, start, seq, 12n, h)),
    Equal.trans(B.Octets, B.Octets.slice(48n, 16n, w), B.Octets.slice(48n, 16n, x), B.Octets.slice(48n, 16n, o), Jc.rs_sl(b, x, 48n, 16n, hx, {==}), Jc.wl_high_sl(o, start, seq, 16n, 16n, h)),
    Equal.trans(Maybe<&2, U32>, B.Octets.at(w, 80n), B.Octets.at(x, 80n), B.Octets.at(o, 80n), Jc.rs_r8(b, x, 80n, hx, {==}), Jc.wl_high8(o, start, seq, 48n, h)))

# s_sequence and s_start

def Jc.seq_go(+x: B.Octets) -> {J.Jbd2Super.sequence(J.Jbd2Super.parse(x)) == Jc.d32(B.Octets.be32_at(x, 24n)) : U32}:
  {==}

def Jc.start_go(+x: B.Octets) -> {J.Jbd2Super.start(J.Jbd2Super.parse(x)) == U32.to_nat(Jc.d32(B.Octets.be32_at(x, 28n))) : Nat}:
  {==}

def Laws.jsuper_log_sequence(o, start, seq, h):
  +b = J.Jbd2Super.has_csum(J.Jbd2Super.parse(o))
  +x1 = J.Jbd2.patch32(o, 24n, seq)
  +x = Jc.wl_x(o, start, seq)
  +w = J.Jbd2Super.reseal(b, x)
  +h1 = Jc.patch_le(o, 24n, seq, 256n, Jc.le256(28n, o, h, {==}), h)
  +r = Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(w, 24n), B.Octets.be32_at(x, 24n), Some{seq}, Jc.rs_r32(b, x, 24n, Jc.wl_len(o, start, seq, h), {==}),
    Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(x, 24n), B.Octets.be32_at(x1, 24n), Some{seq}, Jc.patch_low32(x1, 28n, U32.from_nat(start), 24n, Ext4Proof.le_trans(28n, 256n, B.Octets.len(x1), {==}, h1), {==}), Jc.patch_same32(o, 24n, seq, Jc.le256(28n, o, h, {==}))))
  %Equal.sym(B.Octets, J.Jbd2Super.with_log(o, start, seq), w, Jc.wl_shape(o, start, seq)) : {J.Jbd2Super.sequence(J.Jbd2Super.parse(_)) == seq : U32}
  %Equal.sym(U32, J.Jbd2Super.sequence(J.Jbd2Super.parse(w)), Jc.d32(B.Octets.be32_at(w, 24n)), Jc.seq_go(w)) : {_ == seq : U32}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(w, 24n), Some{seq}, r) : {Jc.d32(_) == seq : U32}
  {==}

def Laws.jsuper_log_start(o, start, seq, h):
  +b = J.Jbd2Super.has_csum(J.Jbd2Super.parse(o))
  +x1 = J.Jbd2.patch32(o, 24n, seq)
  +x = Jc.wl_x(o, start, seq)
  +w = J.Jbd2Super.reseal(b, x)
  +h1 = Jc.patch_le(o, 24n, seq, 256n, Jc.le256(28n, o, h, {==}), h)
  +r = Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(w, 28n), B.Octets.be32_at(x, 28n), Some{U32.from_nat(start)}, Jc.rs_r32(b, x, 28n, Jc.wl_len(o, start, seq, h), {==}),
    Jc.patch_same32(x1, 28n, U32.from_nat(start), Ext4Proof.le_trans(32n, 256n, B.Octets.len(x1), {==}, h1)))
  %Equal.sym(B.Octets, J.Jbd2Super.with_log(o, start, seq), w, Jc.wl_shape(o, start, seq)) : {J.Jbd2Super.start(J.Jbd2Super.parse(_)) == U32.to_nat(U32.from_nat(start)) : Nat}
  %Equal.sym(Nat, J.Jbd2Super.start(J.Jbd2Super.parse(w)), U32.to_nat(Jc.d32(B.Octets.be32_at(w, 28n))), Jc.start_go(w)) : {_ == U32.to_nat(U32.from_nat(start)) : Nat}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(w, 28n), Some{U32.from_nat(start)}, r) : {U32.to_nat(Jc.d32(_)) == U32.to_nat(U32.from_nat(start)) : Nat}
  {==}

# The checksum: with checksums the superblock is version 2 (a version 1
# superblock reads no features), and the patched checksum is the one over
# the bytes around it

def Jc.hc_go(b: Bool, +x: B.Octets) -> {J.Jbd2Super.has_csum(J.Jbd2Super.parse.go(b, x)) == True{} : Bool} -> {b == True{} : Bool}:
  match b:
    case True{}:
      h => {==}
    case False{}:
      h => Ext4Proof.no({False{} == True{} : Bool}, h)

def Jc.jcsum_go(+x: B.Octets) -> {J.Jbd2Super.csum(x) == K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(4294967295, B.Octets.take(252n, x)), B.Octets.zeros(4n)), B.Octets.slice(256n, 768n, x)) : U32}:
  {==}

def Jc.ck_go(+x: B.Octets) -> {J.Jbd2Super.checksum(J.Jbd2Super.parse(x)) == J.Jbd2Super.v2_field(U32.is_eq(Jc.d32(B.Octets.be32_at(x, 4n)), 4), x, 252n) : U32}:
  {==}

def Jc.v2f_t(+x: B.Octets) -> {J.Jbd2Super.v2_field(True{}, x, 252n) == Jc.d32(B.Octets.be32_at(x, 252n)) : U32}:
  {==}

def Laws.jsuper_log_csum(o, start, seq, h, c):
  +x = Jc.wl_x(o, start, seq)
  +hx = Jc.wl_len(o, start, seq, h)
  +p = J.Jbd2.patch32(x, 252n, J.Jbd2Super.csum(x))
  +hp = Jc.le256(256n, x, hx, {==})
  +v = U32.is_eq(Jc.d32(B.Octets.be32_at(o, 4n)), 4)
  +cv = Jc.hc_go(v, o, Equal.trans(Bool, J.Jbd2Super.has_csum(J.Jbd2Super.parse.go(v, o)), J.Jbd2Super.has_csum(J.Jbd2Super.parse(o)), True{}, Equal.cong(J.Jbd2Super, Bool, s => J.Jbd2Super.has_csum(s), J.Jbd2Super.parse.go(v, o), J.Jbd2Super.parse(o), Equal.sym(J.Jbd2Super, J.Jbd2Super.parse(o), J.Jbd2Super.parse.go(v, o), Jc.parse_go(o))), c))
  +r4 = Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(p, 4n), B.Octets.be32_at(x, 4n), B.Octets.be32_at(o, 4n), Jc.patch_low32(x, 252n, J.Jbd2Super.csum(x), 4n, Jc.le256(252n, x, hx, {==}), {==}), Jc.wl_low32(o, start, seq, 4n, h, {==}))
  %Equal.sym(B.Octets, J.Jbd2Super.with_log(o, start, seq), J.Jbd2Super.reseal(J.Jbd2Super.has_csum(J.Jbd2Super.parse(o)), x), Jc.wl_shape(o, start, seq)) : {J.Jbd2Super.csum(_) == J.Jbd2Super.checksum(J.Jbd2Super.parse(_)) : U32}
  %Equal.sym(Bool, J.Jbd2Super.has_csum(J.Jbd2Super.parse(o)), True{}, c) : {J.Jbd2Super.csum(J.Jbd2Super.reseal(_, x)) == J.Jbd2Super.checksum(J.Jbd2Super.parse(J.Jbd2Super.reseal(_, x))) : U32}
  %Equal.sym(B.Octets, J.Jbd2Super.reseal(True{}, x), p, Jc.rs_t(x)) : {J.Jbd2Super.csum(_) == J.Jbd2Super.checksum(J.Jbd2Super.parse(_)) : U32}
  %Equal.sym(U32, J.Jbd2Super.csum(p), K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(4294967295, B.Octets.take(252n, p)), B.Octets.zeros(4n)), B.Octets.slice(256n, 768n, p)), Jc.jcsum_go(p)) : {_ == J.Jbd2Super.checksum(J.Jbd2Super.parse(p)) : U32}
  %Equal.sym(B.Octets, B.Octets.take(252n, p), B.Octets.take(252n, x), Jc.patch_take(x, 252n, J.Jbd2Super.csum(x), Jc.le256(252n, x, hx, {==}))) : {K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(4294967295, _), B.Octets.zeros(4n)), B.Octets.slice(256n, 768n, p)) == J.Jbd2Super.checksum(J.Jbd2Super.parse(p)) : U32}
  %Equal.sym(B.Octets, B.Octets.slice(Nat.add(Nat.add(252n, 4n), 0n), 768n, p), B.Octets.slice(Nat.add(Nat.add(252n, 4n), 0n), 768n, x), Jc.patch_high_sl(x, 252n, J.Jbd2Super.csum(x), 0n, 768n, hp)) : {K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(4294967295, B.Octets.take(252n, x)), B.Octets.zeros(4n)), _) == J.Jbd2Super.checksum(J.Jbd2Super.parse(p)) : U32}
  %Jc.jcsum_go(x) : {_ == J.Jbd2Super.checksum(J.Jbd2Super.parse(p)) : U32}
  %Equal.sym(U32, J.Jbd2Super.checksum(J.Jbd2Super.parse(p)), J.Jbd2Super.v2_field(U32.is_eq(Jc.d32(B.Octets.be32_at(p, 4n)), 4), p, 252n), Jc.ck_go(p)) : {J.Jbd2Super.csum(x) == _ : U32}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(p, 4n), B.Octets.be32_at(o, 4n), r4) : {J.Jbd2Super.csum(x) == J.Jbd2Super.v2_field(U32.is_eq(Jc.d32(_), 4), p, 252n) : U32}
  %Equal.sym(Bool, v, True{}, cv) : {J.Jbd2Super.csum(x) == J.Jbd2Super.v2_field(_, p, 252n) : U32}
  %Equal.sym(U32, J.Jbd2Super.v2_field(True{}, p, 252n), Jc.d32(B.Octets.be32_at(p, 252n)), Jc.v2f_t(p)) : {J.Jbd2Super.csum(x) == _ : U32}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(p, 252n), Some{J.Jbd2Super.csum(x)}, Jc.patch_same32(x, 252n, J.Jbd2Super.csum(x), hp)) : {J.Jbd2Super.csum(x) == Jc.d32(_) : U32}
  {==}

# The tag codec: each layout encode.go writes, read back by parse.go

# (a ++ x) ++ r, x ++ r normalised to y: a ++ y
def Jc.na(+a: B.Octets, +x: B.Octets, +r: B.Octets, +y: B.Octets, e: {B.Octets.append(x, r) == y : B.Octets}) -> {B.Octets.append(B.Octets.append(a, x), r) == B.Octets.append(a, y) : B.Octets}:
  Equal.trans(B.Octets, B.Octets.append(B.Octets.append(a, x), r), B.Octets.append(a, B.Octets.append(x, r)), B.Octets.append(a, y), BL.octets_append_assoc(a, x, r), Equal.cong(B.Octets, B.Octets, z => B.Octets.append(a, z), B.Octets.append(x, r), y, e))

def Jc.rd32(+a: B.Octets, +rest: B.Octets, +k: Nat, +i: Nat, +v: Maybe<&2, U32>, e: {B.Octets.len(a) == k : Nat}, t: {B.Octets.be32_at(rest, i) == v : Maybe<&2, U32>}) -> {B.Octets.be32_at(B.Octets.append(a, rest), Nat.add(k, i)) == v : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(a, rest), Nat.add(k, i)), B.Octets.be32_at(rest, i), v, Jc.skip32(a, rest, k, i, e), t)

def Jc.rd16(+a: B.Octets, +rest: B.Octets, +k: Nat, +i: Nat, +v: Maybe<&2, U32>, e: {B.Octets.len(a) == k : Nat}, t: {B.Octets.be16_at(rest, i) == v : Maybe<&2, U32>}) -> {B.Octets.be16_at(B.Octets.append(a, rest), Nat.add(k, i)) == v : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.append(a, rest), Nat.add(k, i)), B.Octets.be16_at(rest, i), v, Jc.skip16(a, rest, k, i, e), t)

def Jc.d16(m: Maybe<&2, U32>) -> U32:
  Maybe.default(&2, U32, m, 0)

def Jc.EA(+b: Nat, +f: U32, +c: U32) -> B.Octets:
  B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.be32(c))))

def Jc.NA(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.append(Jc.EA(b, f, c), r) == B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))) : B.Octets}:
  Jc.na(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.be32(c))), r, B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r))), Jc.na(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.be32(c)), r, B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)), BL.octets_append_assoc(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.be32(c), r)))

def Jc.RA0(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 0n) == Some{JB.Jbd2.lo(b)} : Maybe<&2, U32>}:
  Jc.be32_head(JB.Jbd2.lo(b), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r))))

def Jc.RA1(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 4n) == Some{f} : Maybe<&2, U32>}:
  Jc.rd32(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r))), 4n, 0n, Some{f}, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.be32_head(f, B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r))))

def Jc.RA2(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 8n) == Some{JB.Jbd2.hi(b)} : Maybe<&2, U32>}:
  Jc.rd32(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r))), 4n, 4n, Some{JB.Jbd2.hi(b)}, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.rd32(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)), 4n, 0n, Some{JB.Jbd2.hi(b)}, BL.octets_len_be32(f), Jc.be32_head(JB.Jbd2.hi(b), B.Octets.append(B.Octets.be32(c), r))))

def Jc.RA3(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 12n) == Some{c} : Maybe<&2, U32>}:
  Jc.rd32(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r))), 4n, 8n, Some{c}, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.rd32(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)), 4n, 4n, Some{c}, BL.octets_len_be32(f), Jc.rd32(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r), 4n, 0n, Some{c}, BL.octets_len_be32(JB.Jbd2.hi(b)), Jc.be32_head(c, r))))

def Jc.lenA(+b: Nat, +f: U32, +c: U32) -> {B.Octets.len(Jc.EA(b, f, c)) == 16n : Nat}:
  Jc.len2(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.be32(c))), 4n, 12n, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.len2(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.be32(c)), 4n, 8n, BL.octets_len_be32(f), Jc.len2(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.be32(c), 4n, 4n, BL.octets_len_be32(JB.Jbd2.hi(b)), BL.octets_len_be32(c))))

def Jc.EB(+b: Nat, +f: U32, +c: U32) -> B.Octets:
  B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.zeros(2n)))))

def Jc.NB(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.append(Jc.EB(b, f, c), r) == B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))) : B.Octets}:
  Jc.na(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.zeros(2n)))), r, B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r)))), Jc.na(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.zeros(2n))), r, B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))), Jc.na(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.zeros(2n)), r, B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r)), BL.octets_append_assoc(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.zeros(2n), r))))

def Jc.RB0(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 0n) == Some{JB.Jbd2.lo(b)} : Maybe<&2, U32>}:
  Jc.be32_head(JB.Jbd2.lo(b), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r)))))

def Jc.RB1(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 4n) == Some{B.low16(c)} : Maybe<&2, U32>}:
  Jc.rd16(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r)))), 4n, 0n, Some{B.low16(c)}, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.be16_head(c, B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r)))))

def Jc.RB2(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 6n) == Some{B.low16(f)} : Maybe<&2, U32>}:
  Jc.rd16(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r)))), 4n, 2n, Some{B.low16(f)}, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.rd16(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))), 2n, 0n, Some{B.low16(f)}, BL.octets_len_be16(c), Jc.be16_head(f, B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r)))))

def Jc.RB3(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 8n) == Some{JB.Jbd2.hi(b)} : Maybe<&2, U32>}:
  Jc.rd32(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r)))), 4n, 4n, Some{JB.Jbd2.hi(b)}, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.rd32(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))), 2n, 2n, Some{JB.Jbd2.hi(b)}, BL.octets_len_be16(c), Jc.rd32(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r)), 2n, 0n, Some{JB.Jbd2.hi(b)}, BL.octets_len_be16(f), Jc.be32_head(JB.Jbd2.hi(b), B.Octets.append(B.Octets.zeros(2n), r)))))

def Jc.lenB(+b: Nat, +f: U32, +c: U32) -> {B.Octets.len(Jc.EB(b, f, c)) == 14n : Nat}:
  Jc.len2(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.zeros(2n)))), 4n, 10n, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.len2(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.zeros(2n))), 2n, 8n, BL.octets_len_be16(c), Jc.len2(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.zeros(2n)), 2n, 6n, BL.octets_len_be16(f), Jc.len2(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.zeros(2n), 4n, 2n, BL.octets_len_be32(JB.Jbd2.hi(b)), BL.octets_len_zeros(2n)))))

def Jc.EC(+b: Nat, +f: U32, +c: U32) -> B.Octets:
  B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.zeros(2n))))

def Jc.NC(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.append(Jc.EC(b, f, c), r) == B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))) : B.Octets}:
  Jc.na(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.zeros(2n))), r, B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r))), Jc.na(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.zeros(2n)), r, B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)), BL.octets_append_assoc(B.Octets.be16(f), B.Octets.zeros(2n), r)))

def Jc.RC0(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), 0n) == Some{JB.Jbd2.lo(b)} : Maybe<&2, U32>}:
  Jc.be32_head(JB.Jbd2.lo(b), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r))))

def Jc.RC1(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), 4n) == Some{B.low16(c)} : Maybe<&2, U32>}:
  Jc.rd16(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r))), 4n, 0n, Some{B.low16(c)}, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.be16_head(c, B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r))))

def Jc.RC2(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), 6n) == Some{B.low16(f)} : Maybe<&2, U32>}:
  Jc.rd16(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r))), 4n, 2n, Some{B.low16(f)}, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.rd16(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)), 2n, 0n, Some{B.low16(f)}, BL.octets_len_be16(c), Jc.be16_head(f, B.Octets.append(B.Octets.zeros(2n), r))))

def Jc.lenC(+b: Nat, +f: U32, +c: U32) -> {B.Octets.len(Jc.EC(b, f, c)) == 10n : Nat}:
  Jc.len2(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.zeros(2n))), 4n, 6n, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.len2(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.zeros(2n)), 2n, 4n, BL.octets_len_be16(c), Jc.len2(B.Octets.be16(f), B.Octets.zeros(2n), 2n, 2n, BL.octets_len_be16(f), BL.octets_len_zeros(2n))))

def Jc.ED(+b: Nat, +f: U32, +c: U32) -> B.Octets:
  B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.be32(JB.Jbd2.hi(b)))))

def Jc.ND(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.append(Jc.ED(b, f, c), r) == B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))) : B.Octets}:
  Jc.na(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.be32(JB.Jbd2.hi(b)))), r, B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r))), Jc.na(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.be32(JB.Jbd2.hi(b))), r, B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)), BL.octets_append_assoc(B.Octets.be16(f), B.Octets.be32(JB.Jbd2.hi(b)), r)))

def Jc.RD0(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 0n) == Some{JB.Jbd2.lo(b)} : Maybe<&2, U32>}:
  Jc.be32_head(JB.Jbd2.lo(b), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r))))

def Jc.RD1(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 4n) == Some{B.low16(c)} : Maybe<&2, U32>}:
  Jc.rd16(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r))), 4n, 0n, Some{B.low16(c)}, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.be16_head(c, B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r))))

def Jc.RD2(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 6n) == Some{B.low16(f)} : Maybe<&2, U32>}:
  Jc.rd16(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r))), 4n, 2n, Some{B.low16(f)}, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.rd16(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)), 2n, 0n, Some{B.low16(f)}, BL.octets_len_be16(c), Jc.be16_head(f, B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r))))

def Jc.RD3(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 8n) == Some{JB.Jbd2.hi(b)} : Maybe<&2, U32>}:
  Jc.rd32(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r))), 4n, 4n, Some{JB.Jbd2.hi(b)}, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.rd32(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)), 2n, 2n, Some{JB.Jbd2.hi(b)}, BL.octets_len_be16(c), Jc.rd32(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r), 2n, 0n, Some{JB.Jbd2.hi(b)}, BL.octets_len_be16(f), Jc.be32_head(JB.Jbd2.hi(b), r))))

def Jc.lenD(+b: Nat, +f: U32, +c: U32) -> {B.Octets.len(Jc.ED(b, f, c)) == 12n : Nat}:
  Jc.len2(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.be32(JB.Jbd2.hi(b)))), 4n, 8n, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.len2(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.be32(JB.Jbd2.hi(b))), 2n, 6n, BL.octets_len_be16(c), Jc.len2(B.Octets.be16(f), B.Octets.be32(JB.Jbd2.hi(b)), 2n, 4n, BL.octets_len_be16(f), BL.octets_len_be32(JB.Jbd2.hi(b)))))

def Jc.EE(+b: Nat, +f: U32, +c: U32) -> B.Octets:
  B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.be16(f)))

def Jc.NE(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.append(Jc.EE(b, f, c), r) == B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))) : B.Octets}:
  Jc.na(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.be16(f)), r, B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r)), BL.octets_append_assoc(B.Octets.be16(c), B.Octets.be16(f), r))

def Jc.RE0(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), 0n) == Some{JB.Jbd2.lo(b)} : Maybe<&2, U32>}:
  Jc.be32_head(JB.Jbd2.lo(b), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r)))

def Jc.RE1(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), 4n) == Some{B.low16(c)} : Maybe<&2, U32>}:
  Jc.rd16(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r)), 4n, 0n, Some{B.low16(c)}, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.be16_head(c, B.Octets.append(B.Octets.be16(f), r)))

def Jc.RE2(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), 6n) == Some{B.low16(f)} : Maybe<&2, U32>}:
  Jc.rd16(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r)), 4n, 2n, Some{B.low16(f)}, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.rd16(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r), 2n, 0n, Some{B.low16(f)}, BL.octets_len_be16(c), Jc.be16_head(f, r)))

def Jc.lenE(+b: Nat, +f: U32, +c: U32) -> {B.Octets.len(Jc.EE(b, f, c)) == 8n : Nat}:
  Jc.len2(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.be16(f)), 4n, 4n, BL.octets_len_be32(JB.Jbd2.lo(b)), Jc.len2(B.Octets.be16(c), B.Octets.be16(f), 2n, 2n, BL.octets_len_be16(c), BL.octets_len_be16(f)))

def Jc.pgo_t(+w: Bool, +x: B.Octets) -> {JB.Jbd2Tag.parse.go(True{}, w, x) == JB.Jbd2Tag{JB.Jbd2.join(w, Jc.d32(B.Octets.be32_at(x, 8n)), Jc.d32(B.Octets.be32_at(x, 0n))), Jc.d32(B.Octets.be32_at(x, 4n)), Jc.d32(B.Octets.be32_at(x, 12n))} : JB.Jbd2Tag}:
  {==}

def Jc.pgo_f(+w: Bool, +x: B.Octets) -> {JB.Jbd2Tag.parse.go(False{}, w, x) == JB.Jbd2Tag{JB.Jbd2.join(w, Jc.d32(B.Octets.be32_at(x, 8n)), Jc.d32(B.Octets.be32_at(x, 0n))), Jc.d16(B.Octets.be16_at(x, 6n)), Jc.d16(B.Octets.be16_at(x, 4n))} : JB.Jbd2Tag}:
  {==}

def Jc.LA(+w: Bool, +b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {JB.Jbd2Tag.parse.go(True{}, w, B.Octets.append(Jc.EA(b, f, c), r)) == JB.Jbd2Tag{JB.Jbd2.join(w, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), f, c} : JB.Jbd2Tag}:
  %Equal.sym(B.Octets, B.Octets.append(Jc.EA(b, f, c), r), B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), Jc.NA(b, f, c, r)) : {JB.Jbd2Tag.parse.go(True{}, w, _) == JB.Jbd2Tag{JB.Jbd2.join(w, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), f, c} : JB.Jbd2Tag}
  %Equal.sym(JB.Jbd2Tag, JB.Jbd2Tag.parse.go(True{}, w, B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r))))), JB.Jbd2Tag{JB.Jbd2.join(w, Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 8n)), Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 0n))), Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 4n)), Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 12n))}, Jc.pgo_t(w, B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))))) : {_ == JB.Jbd2Tag{JB.Jbd2.join(w, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), f, c} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 8n), Some{JB.Jbd2.hi(b)}, Jc.RA2(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(w, Jc.d32(_), Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 0n))), Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 4n)), Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 12n))} == JB.Jbd2Tag{JB.Jbd2.join(w, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), f, c} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 0n), Some{JB.Jbd2.lo(b)}, Jc.RA0(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(w, JB.Jbd2.hi(b), Jc.d32(_)), Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 4n)), Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 12n))} == JB.Jbd2Tag{JB.Jbd2.join(w, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), f, c} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 4n), Some{f}, Jc.RA1(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(w, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), Jc.d32(_), Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 12n))} == JB.Jbd2Tag{JB.Jbd2.join(w, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), f, c} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be32(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.be32(c), r)))), 12n), Some{c}, Jc.RA3(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(w, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), f, Jc.d32(_)} == JB.Jbd2Tag{JB.Jbd2.join(w, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), f, c} : JB.Jbd2Tag}
  {==}

def Jc.LB(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {JB.Jbd2Tag.parse.go(False{}, True{}, B.Octets.append(Jc.EB(b, f, c), r)) == JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}:
  %Equal.sym(B.Octets, B.Octets.append(Jc.EB(b, f, c), r), B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), Jc.NB(b, f, c, r)) : {JB.Jbd2Tag.parse.go(False{}, True{}, _) == JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(JB.Jbd2Tag, JB.Jbd2Tag.parse.go(False{}, True{}, B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r)))))), JB.Jbd2Tag{JB.Jbd2.join(True{}, Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 8n)), Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 0n))), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 6n)), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 4n))}, Jc.pgo_f(True{}, B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))))) : {_ == JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 8n), Some{JB.Jbd2.hi(b)}, Jc.RB3(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(True{}, Jc.d32(_), Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 0n))), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 6n)), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 4n))} == JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 0n), Some{JB.Jbd2.lo(b)}, Jc.RB0(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), Jc.d32(_)), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 6n)), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 4n))} == JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 6n), Some{B.low16(f)}, Jc.RB2(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), Jc.d16(_), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 4n))} == JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.append(B.Octets.zeros(2n), r))))), 4n), Some{B.low16(c)}, Jc.RB1(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), Jc.d16(_)} == JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  {==}

def Jc.LC(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {JB.Jbd2Tag.parse.go(False{}, False{}, B.Octets.append(Jc.EC(b, f, c), r)) == JB.Jbd2Tag{JB.Jbd2.join(False{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}:
  %Equal.sym(B.Octets, B.Octets.append(Jc.EC(b, f, c), r), B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), Jc.NC(b, f, c, r)) : {JB.Jbd2Tag.parse.go(False{}, False{}, _) == JB.Jbd2Tag{JB.Jbd2.join(False{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(JB.Jbd2Tag, JB.Jbd2Tag.parse.go(False{}, False{}, B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r))))), JB.Jbd2Tag{JB.Jbd2.join(False{}, Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), 8n)), Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), 0n))), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), 6n)), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), 4n))}, Jc.pgo_f(False{}, B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))))) : {_ == JB.Jbd2Tag{JB.Jbd2.join(False{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), 0n), Some{JB.Jbd2.lo(b)}, Jc.RC0(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(False{}, Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), 8n)), Jc.d32(_)), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), 6n)), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), 4n))} == JB.Jbd2Tag{JB.Jbd2.join(False{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), 6n), Some{B.low16(f)}, Jc.RC2(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(False{}, Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), 8n)), JB.Jbd2.lo(b)), Jc.d16(_), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), 4n))} == JB.Jbd2Tag{JB.Jbd2.join(False{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), 4n), Some{B.low16(c)}, Jc.RC1(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(False{}, Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.zeros(2n), r)))), 8n)), JB.Jbd2.lo(b)), B.low16(f), Jc.d16(_)} == JB.Jbd2Tag{JB.Jbd2.join(False{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  {==}

def Jc.LD(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {JB.Jbd2Tag.parse.go(False{}, True{}, B.Octets.append(Jc.ED(b, f, c), r)) == JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}:
  %Equal.sym(B.Octets, B.Octets.append(Jc.ED(b, f, c), r), B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), Jc.ND(b, f, c, r)) : {JB.Jbd2Tag.parse.go(False{}, True{}, _) == JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(JB.Jbd2Tag, JB.Jbd2Tag.parse.go(False{}, True{}, B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r))))), JB.Jbd2Tag{JB.Jbd2.join(True{}, Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 8n)), Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 0n))), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 6n)), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 4n))}, Jc.pgo_f(True{}, B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))))) : {_ == JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 8n), Some{JB.Jbd2.hi(b)}, Jc.RD3(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(True{}, Jc.d32(_), Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 0n))), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 6n)), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 4n))} == JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 0n), Some{JB.Jbd2.lo(b)}, Jc.RD0(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), Jc.d32(_)), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 6n)), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 4n))} == JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 6n), Some{B.low16(f)}, Jc.RD2(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), Jc.d16(_), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 4n))} == JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), B.Octets.append(B.Octets.be32(JB.Jbd2.hi(b)), r)))), 4n), Some{B.low16(c)}, Jc.RD1(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), Jc.d16(_)} == JB.Jbd2Tag{JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  {==}

def Jc.LE(+b: Nat, +f: U32, +c: U32, +r: B.Octets) -> {JB.Jbd2Tag.parse.go(False{}, False{}, B.Octets.append(Jc.EE(b, f, c), r)) == JB.Jbd2Tag{JB.Jbd2.join(False{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}:
  %Equal.sym(B.Octets, B.Octets.append(Jc.EE(b, f, c), r), B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), Jc.NE(b, f, c, r)) : {JB.Jbd2Tag.parse.go(False{}, False{}, _) == JB.Jbd2Tag{JB.Jbd2.join(False{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(JB.Jbd2Tag, JB.Jbd2Tag.parse.go(False{}, False{}, B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r)))), JB.Jbd2Tag{JB.Jbd2.join(False{}, Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), 8n)), Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), 0n))), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), 6n)), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), 4n))}, Jc.pgo_f(False{}, B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))))) : {_ == JB.Jbd2Tag{JB.Jbd2.join(False{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), 0n), Some{JB.Jbd2.lo(b)}, Jc.RE0(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(False{}, Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), 8n)), Jc.d32(_)), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), 6n)), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), 4n))} == JB.Jbd2Tag{JB.Jbd2.join(False{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), 6n), Some{B.low16(f)}, Jc.RE2(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(False{}, Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), 8n)), JB.Jbd2.lo(b)), Jc.d16(_), Jc.d16(B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), 4n))} == JB.Jbd2Tag{JB.Jbd2.join(False{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be16_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), 4n), Some{B.low16(c)}, Jc.RE1(b, f, c, r)) : {JB.Jbd2Tag{JB.Jbd2.join(False{}, Jc.d32(B.Octets.be32_at(B.Octets.append(B.Octets.be32(JB.Jbd2.lo(b)), B.Octets.append(B.Octets.be16(c), B.Octets.append(B.Octets.be16(f), r))), 8n)), JB.Jbd2.lo(b)), B.low16(f), Jc.d16(_)} == JB.Jbd2Tag{JB.Jbd2.join(False{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)} : JB.Jbd2Tag}
  {==}

# the tag as the log stores it: the block number through its halves, and
# without csum_v3 the flags and checksum cut to 16 bits
def Jc.stored.go(v3: Bool, +w: Bool, +b: Nat, +f: U32, +c: U32) -> JB.Jbd2Tag:
  match v3:
    case True{}:
      JB.Jbd2Tag{JB.Jbd2.join(w, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), f, c}
    case False{}:
      JB.Jbd2Tag{JB.Jbd2.join(w, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), B.low16(f), B.low16(c)}

def Jc.stored(+g: J.Jbd2Geom, t: JB.Jbd2Tag) -> JB.Jbd2Tag:
  match t:
    case JB.Jbd2Tag{b, f, c}:
      Jc.stored.go(Nat.is_eq(J.Jbd2Geom.csum(g), 3n), J.Jbd2Geom.wide(g), b, f, c)

# a tag, encoded and followed by anything, parses as its stored form
def Jc.tag_rt(+g: J.Jbd2Geom, +t: JB.Jbd2Tag, +r: B.Octets) -> {JB.Jbd2Tag.parse(g, B.Octets.append(JB.Jbd2Tag.encode(g, t), r)) == Jc.stored(g, t) : JB.Jbd2Tag}:
  match g:
    case J.Jbd2Geom{+bs, +w, +cs, +sd, +fi, +mx}:
      match w:
        case True{}:
          match cs:
            case 0n:
              match t:
                case JB.Jbd2Tag{+b, +f, +c}:
                  Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 0n, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 0n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse.go(False{}, True{}, B.Octets.append(Jc.ED(b, f, c), r)), Jc.stored(J.Jbd2Geom{bs, True{}, 0n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 0n, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 0n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 0n, sd, fi, mx}, B.Octets.append(Jc.ED(b, f, c), r)), JB.Jbd2Tag.parse.go(False{}, True{}, B.Octets.append(Jc.ED(b, f, c), r)), Equal.cong(B.Octets, JB.Jbd2Tag, x => JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 0n, sd, fi, mx}, B.Octets.append(x, r)), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 0n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.ED(b, f, c), {==}), {==}), Jc.LD(b, f, c, r))
            case 1n+q1:
              match q1:
                case 0n:
                  match t:
                    case JB.Jbd2Tag{+b, +f, +c}:
                      Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 1n, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 1n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse.go(False{}, True{}, B.Octets.append(Jc.ED(b, f, c), r)), Jc.stored(J.Jbd2Geom{bs, True{}, 1n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 1n, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 1n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 1n, sd, fi, mx}, B.Octets.append(Jc.ED(b, f, c), r)), JB.Jbd2Tag.parse.go(False{}, True{}, B.Octets.append(Jc.ED(b, f, c), r)), Equal.cong(B.Octets, JB.Jbd2Tag, x => JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 1n, sd, fi, mx}, B.Octets.append(x, r)), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 1n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.ED(b, f, c), {==}), {==}), Jc.LD(b, f, c, r))
                case 1n+q2:
                  match q2:
                    case 0n:
                      match t:
                        case JB.Jbd2Tag{+b, +f, +c}:
                          Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 2n, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 2n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse.go(False{}, True{}, B.Octets.append(Jc.EB(b, f, c), r)), Jc.stored(J.Jbd2Geom{bs, True{}, 2n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 2n, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 2n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 2n, sd, fi, mx}, B.Octets.append(Jc.EB(b, f, c), r)), JB.Jbd2Tag.parse.go(False{}, True{}, B.Octets.append(Jc.EB(b, f, c), r)), Equal.cong(B.Octets, JB.Jbd2Tag, x => JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 2n, sd, fi, mx}, B.Octets.append(x, r)), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 2n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.EB(b, f, c), {==}), {==}), Jc.LB(b, f, c, r))
                    case 1n+q3:
                      match q3:
                        case 0n:
                          match t:
                            case JB.Jbd2Tag{+b, +f, +c}:
                              Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 3n, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 3n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse.go(True{}, True{}, B.Octets.append(Jc.EA(b, f, c), r)), Jc.stored(J.Jbd2Geom{bs, True{}, 3n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 3n, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 3n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 3n, sd, fi, mx}, B.Octets.append(Jc.EA(b, f, c), r)), JB.Jbd2Tag.parse.go(True{}, True{}, B.Octets.append(Jc.EA(b, f, c), r)), Equal.cong(B.Octets, JB.Jbd2Tag, x => JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 3n, sd, fi, mx}, B.Octets.append(x, r)), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 3n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.EA(b, f, c), {==}), {==}), Jc.LA(True{}, b, f, c, r))
                        case 1n+q4:
                          match t:
                            case JB.Jbd2Tag{+b, +f, +c}:
                              Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 4n+q4, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 4n+q4, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse.go(False{}, True{}, B.Octets.append(Jc.ED(b, f, c), r)), Jc.stored(J.Jbd2Geom{bs, True{}, 4n+q4, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 4n+q4, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 4n+q4, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 4n+q4, sd, fi, mx}, B.Octets.append(Jc.ED(b, f, c), r)), JB.Jbd2Tag.parse.go(False{}, True{}, B.Octets.append(Jc.ED(b, f, c), r)), Equal.cong(B.Octets, JB.Jbd2Tag, x => JB.Jbd2Tag.parse(J.Jbd2Geom{bs, True{}, 4n+q4, sd, fi, mx}, B.Octets.append(x, r)), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 4n+q4, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.ED(b, f, c), {==}), {==}), Jc.LD(b, f, c, r))
        case False{}:
          match cs:
            case 0n:
              match t:
                case JB.Jbd2Tag{+b, +f, +c}:
                  Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 0n, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 0n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse.go(False{}, False{}, B.Octets.append(Jc.EE(b, f, c), r)), Jc.stored(J.Jbd2Geom{bs, False{}, 0n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 0n, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 0n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 0n, sd, fi, mx}, B.Octets.append(Jc.EE(b, f, c), r)), JB.Jbd2Tag.parse.go(False{}, False{}, B.Octets.append(Jc.EE(b, f, c), r)), Equal.cong(B.Octets, JB.Jbd2Tag, x => JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 0n, sd, fi, mx}, B.Octets.append(x, r)), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 0n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.EE(b, f, c), {==}), {==}), Jc.LE(b, f, c, r))
            case 1n+q1:
              match q1:
                case 0n:
                  match t:
                    case JB.Jbd2Tag{+b, +f, +c}:
                      Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 1n, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 1n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse.go(False{}, False{}, B.Octets.append(Jc.EE(b, f, c), r)), Jc.stored(J.Jbd2Geom{bs, False{}, 1n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 1n, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 1n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 1n, sd, fi, mx}, B.Octets.append(Jc.EE(b, f, c), r)), JB.Jbd2Tag.parse.go(False{}, False{}, B.Octets.append(Jc.EE(b, f, c), r)), Equal.cong(B.Octets, JB.Jbd2Tag, x => JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 1n, sd, fi, mx}, B.Octets.append(x, r)), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 1n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.EE(b, f, c), {==}), {==}), Jc.LE(b, f, c, r))
                case 1n+q2:
                  match q2:
                    case 0n:
                      match t:
                        case JB.Jbd2Tag{+b, +f, +c}:
                          Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 2n, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 2n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse.go(False{}, False{}, B.Octets.append(Jc.EC(b, f, c), r)), Jc.stored(J.Jbd2Geom{bs, False{}, 2n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 2n, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 2n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 2n, sd, fi, mx}, B.Octets.append(Jc.EC(b, f, c), r)), JB.Jbd2Tag.parse.go(False{}, False{}, B.Octets.append(Jc.EC(b, f, c), r)), Equal.cong(B.Octets, JB.Jbd2Tag, x => JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 2n, sd, fi, mx}, B.Octets.append(x, r)), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 2n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.EC(b, f, c), {==}), {==}), Jc.LC(b, f, c, r))
                    case 1n+q3:
                      match q3:
                        case 0n:
                          match t:
                            case JB.Jbd2Tag{+b, +f, +c}:
                              Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 3n, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 3n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse.go(True{}, False{}, B.Octets.append(Jc.EA(b, f, c), r)), Jc.stored(J.Jbd2Geom{bs, False{}, 3n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 3n, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 3n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 3n, sd, fi, mx}, B.Octets.append(Jc.EA(b, f, c), r)), JB.Jbd2Tag.parse.go(True{}, False{}, B.Octets.append(Jc.EA(b, f, c), r)), Equal.cong(B.Octets, JB.Jbd2Tag, x => JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 3n, sd, fi, mx}, B.Octets.append(x, r)), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 3n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.EA(b, f, c), {==}), {==}), Jc.LA(False{}, b, f, c, r))
                        case 1n+q4:
                          match t:
                            case JB.Jbd2Tag{+b, +f, +c}:
                              Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 4n+q4, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 4n+q4, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse.go(False{}, False{}, B.Octets.append(Jc.EE(b, f, c), r)), Jc.stored(J.Jbd2Geom{bs, False{}, 4n+q4, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 4n+q4, sd, fi, mx}, B.Octets.append(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 4n+q4, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), r)), JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 4n+q4, sd, fi, mx}, B.Octets.append(Jc.EE(b, f, c), r)), JB.Jbd2Tag.parse.go(False{}, False{}, B.Octets.append(Jc.EE(b, f, c), r)), Equal.cong(B.Octets, JB.Jbd2Tag, x => JB.Jbd2Tag.parse(J.Jbd2Geom{bs, False{}, 4n+q4, sd, fi, mx}, B.Octets.append(x, r)), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 4n+q4, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.EE(b, f, c), {==}), {==}), Jc.LE(b, f, c, r))

# a tag's encoding takes tag_size bytes
def Jc.tag_len(+g: J.Jbd2Geom, +t: JB.Jbd2Tag) -> {B.Octets.len(JB.Jbd2Tag.encode(g, t)) == J.Jbd2Geom.tag_size(g) : Nat}:
  match g:
    case J.Jbd2Geom{+bs, +w, +cs, +sd, +fi, +mx}:
      match w:
        case True{}:
          match cs:
            case 0n:
              match t:
                case JB.Jbd2Tag{+b, +f, +c}:
                  Equal.trans(Nat, B.Octets.len(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 0n, sd, fi, mx}, JB.Jbd2Tag{b, f, c})), B.Octets.len(Jc.ED(b, f, c)), J.Jbd2Geom.tag_size(J.Jbd2Geom{bs, True{}, 0n, sd, fi, mx}), Equal.cong(B.Octets, Nat, x => B.Octets.len(x), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 0n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.ED(b, f, c), {==}), Jc.lenD(b, f, c))
            case 1n+q1:
              match q1:
                case 0n:
                  match t:
                    case JB.Jbd2Tag{+b, +f, +c}:
                      Equal.trans(Nat, B.Octets.len(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 1n, sd, fi, mx}, JB.Jbd2Tag{b, f, c})), B.Octets.len(Jc.ED(b, f, c)), J.Jbd2Geom.tag_size(J.Jbd2Geom{bs, True{}, 1n, sd, fi, mx}), Equal.cong(B.Octets, Nat, x => B.Octets.len(x), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 1n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.ED(b, f, c), {==}), Jc.lenD(b, f, c))
                case 1n+q2:
                  match q2:
                    case 0n:
                      match t:
                        case JB.Jbd2Tag{+b, +f, +c}:
                          Equal.trans(Nat, B.Octets.len(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 2n, sd, fi, mx}, JB.Jbd2Tag{b, f, c})), B.Octets.len(Jc.EB(b, f, c)), J.Jbd2Geom.tag_size(J.Jbd2Geom{bs, True{}, 2n, sd, fi, mx}), Equal.cong(B.Octets, Nat, x => B.Octets.len(x), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 2n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.EB(b, f, c), {==}), Jc.lenB(b, f, c))
                    case 1n+q3:
                      match q3:
                        case 0n:
                          match t:
                            case JB.Jbd2Tag{+b, +f, +c}:
                              Equal.trans(Nat, B.Octets.len(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 3n, sd, fi, mx}, JB.Jbd2Tag{b, f, c})), B.Octets.len(Jc.EA(b, f, c)), J.Jbd2Geom.tag_size(J.Jbd2Geom{bs, True{}, 3n, sd, fi, mx}), Equal.cong(B.Octets, Nat, x => B.Octets.len(x), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 3n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.EA(b, f, c), {==}), Jc.lenA(b, f, c))
                        case 1n+q4:
                          match t:
                            case JB.Jbd2Tag{+b, +f, +c}:
                              Equal.trans(Nat, B.Octets.len(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 4n+q4, sd, fi, mx}, JB.Jbd2Tag{b, f, c})), B.Octets.len(Jc.ED(b, f, c)), J.Jbd2Geom.tag_size(J.Jbd2Geom{bs, True{}, 4n+q4, sd, fi, mx}), Equal.cong(B.Octets, Nat, x => B.Octets.len(x), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, True{}, 4n+q4, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.ED(b, f, c), {==}), Jc.lenD(b, f, c))
        case False{}:
          match cs:
            case 0n:
              match t:
                case JB.Jbd2Tag{+b, +f, +c}:
                  Equal.trans(Nat, B.Octets.len(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 0n, sd, fi, mx}, JB.Jbd2Tag{b, f, c})), B.Octets.len(Jc.EE(b, f, c)), J.Jbd2Geom.tag_size(J.Jbd2Geom{bs, False{}, 0n, sd, fi, mx}), Equal.cong(B.Octets, Nat, x => B.Octets.len(x), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 0n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.EE(b, f, c), {==}), Jc.lenE(b, f, c))
            case 1n+q1:
              match q1:
                case 0n:
                  match t:
                    case JB.Jbd2Tag{+b, +f, +c}:
                      Equal.trans(Nat, B.Octets.len(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 1n, sd, fi, mx}, JB.Jbd2Tag{b, f, c})), B.Octets.len(Jc.EE(b, f, c)), J.Jbd2Geom.tag_size(J.Jbd2Geom{bs, False{}, 1n, sd, fi, mx}), Equal.cong(B.Octets, Nat, x => B.Octets.len(x), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 1n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.EE(b, f, c), {==}), Jc.lenE(b, f, c))
                case 1n+q2:
                  match q2:
                    case 0n:
                      match t:
                        case JB.Jbd2Tag{+b, +f, +c}:
                          Equal.trans(Nat, B.Octets.len(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 2n, sd, fi, mx}, JB.Jbd2Tag{b, f, c})), B.Octets.len(Jc.EC(b, f, c)), J.Jbd2Geom.tag_size(J.Jbd2Geom{bs, False{}, 2n, sd, fi, mx}), Equal.cong(B.Octets, Nat, x => B.Octets.len(x), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 2n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.EC(b, f, c), {==}), Jc.lenC(b, f, c))
                    case 1n+q3:
                      match q3:
                        case 0n:
                          match t:
                            case JB.Jbd2Tag{+b, +f, +c}:
                              Equal.trans(Nat, B.Octets.len(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 3n, sd, fi, mx}, JB.Jbd2Tag{b, f, c})), B.Octets.len(Jc.EA(b, f, c)), J.Jbd2Geom.tag_size(J.Jbd2Geom{bs, False{}, 3n, sd, fi, mx}), Equal.cong(B.Octets, Nat, x => B.Octets.len(x), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 3n, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.EA(b, f, c), {==}), Jc.lenA(b, f, c))
                        case 1n+q4:
                          match t:
                            case JB.Jbd2Tag{+b, +f, +c}:
                              Equal.trans(Nat, B.Octets.len(JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 4n+q4, sd, fi, mx}, JB.Jbd2Tag{b, f, c})), B.Octets.len(Jc.EE(b, f, c)), J.Jbd2Geom.tag_size(J.Jbd2Geom{bs, False{}, 4n+q4, sd, fi, mx}), Equal.cong(B.Octets, Nat, x => B.Octets.len(x), JB.Jbd2Tag.encode(J.Jbd2Geom{bs, False{}, 4n+q4, sd, fi, mx}, JB.Jbd2Tag{b, f, c}), Jc.EE(b, f, c), {==}), Jc.lenE(b, f, c))

# a storable tag's stored form is the tag
def Jc.sgo_t(+w: Bool, +b: Nat, +f: U32, +c: U32, hb: {JB.Jbd2.block_fits(w, b) == True{} : Bool}) -> {Jc.stored.go(True{}, w, b, f, c) == JB.Jbd2Tag{b, f, c} : JB.Jbd2Tag}:
  %Equal.sym(Nat, JB.Jbd2.join(w, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), b, Ext4Proof.eq_sound(JB.Jbd2.join(w, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), b, hb)) : {JB.Jbd2Tag{_, f, c} == JB.Jbd2Tag{b, f, c} : JB.Jbd2Tag}
  {==}

def Jc.sgo_f(+w: Bool, +b: Nat, +f: U32, +c: U32, hb: {JB.Jbd2.block_fits(w, b) == True{} : Bool}, +hf: {Bool.and(U32.is_eq(B.low16(f), f), U32.is_eq(B.low16(c), c)) == True{} : Bool}) -> {Jc.stored.go(False{}, w, b, f, c) == JB.Jbd2Tag{b, f, c} : JB.Jbd2Tag}:
  %Equal.sym(Nat, JB.Jbd2.join(w, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), b, Ext4Proof.eq_sound(JB.Jbd2.join(w, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), b, hb)) : {JB.Jbd2Tag{_, B.low16(f), B.low16(c)} == JB.Jbd2Tag{b, f, c} : JB.Jbd2Tag}
  %Equal.sym(U32, B.low16(f), f, Ext4Proof.u32_eq(B.low16(f), f, Ext4Proof.and_l(U32.is_eq(B.low16(f), f), U32.is_eq(B.low16(c), c), hf))) : {JB.Jbd2Tag{b, _, B.low16(c)} == JB.Jbd2Tag{b, f, c} : JB.Jbd2Tag}
  %Equal.sym(U32, B.low16(c), c, Ext4Proof.u32_eq(B.low16(c), c, Ext4Proof.and_r(U32.is_eq(B.low16(f), f), U32.is_eq(B.low16(c), c), hf))) : {JB.Jbd2Tag{b, f, _} == JB.Jbd2Tag{b, f, c} : JB.Jbd2Tag}
  {==}

def Jc.sgo(v3: Bool, +w: Bool, +b: Nat, +f: U32, +c: U32) -> {JB.Jbd2.block_fits(w, b) == True{} : Bool} -> {JB.Jbd2Tag.storable.fields(v3, f, c) == True{} : Bool} -> {Jc.stored.go(v3, w, b, f, c) == JB.Jbd2Tag{b, f, c} : JB.Jbd2Tag}:
  match v3:
    case True{}:
      hb => hf => Jc.sgo_t(w, b, f, c, hb)
    case False{}:
      hb => hf => Jc.sgo_f(w, b, f, c, hb, hf)

def Jc.stored_eq(+g: J.Jbd2Geom, +t: JB.Jbd2Tag) -> {JB.Jbd2Tag.storable(g, t) == True{} : Bool} -> {Jc.stored(g, t) == t : JB.Jbd2Tag}:
  match t:
    case JB.Jbd2Tag{+b, +f, +c}:
      +hs => Jc.sgo(Nat.is_eq(J.Jbd2Geom.csum(g), 3n), J.Jbd2Geom.wide(g), b, f, c, Ext4Proof.and_l(JB.Jbd2.block_fits(J.Jbd2Geom.wide(g), b), JB.Jbd2Tag.storable.fields(Nat.is_eq(J.Jbd2Geom.csum(g), 3n), f, c), hs), Ext4Proof.and_r(JB.Jbd2.block_fits(J.Jbd2Geom.wide(g), b), JB.Jbd2Tag.storable.fields(Nat.is_eq(J.Jbd2Geom.csum(g), 3n), f, c), hs))

# a storable tag, encoded and followed by anything, parses as itself
def Jc.tag_rt2(+g: J.Jbd2Geom, +t: JB.Jbd2Tag, +r: B.Octets, hs: {JB.Jbd2Tag.storable(g, t) == True{} : Bool}) -> {JB.Jbd2Tag.parse(g, B.Octets.append(JB.Jbd2Tag.encode(g, t), r)) == t : JB.Jbd2Tag}:
  Equal.trans(JB.Jbd2Tag, JB.Jbd2Tag.parse(g, B.Octets.append(JB.Jbd2Tag.encode(g, t), r)), Jc.stored(g, t), t, Jc.tag_rt(g, t, r), Jc.stored_eq(g, t, hs))

# More natural numbers

def Jc.le_succ(+q: Nat) -> {Nat.is_le(q, 1n+q) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      Jc.le_succ(p)

def Jc.le_mono_l(+c: Nat, +a: Nat, +b: Nat) -> {Nat.is_le(a, b) == True{} : Bool} -> {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  match c:
    case 0n:
      h => h
    case 1n+p:
      h => Jc.le_mono_l(p, a, b, h)

def Jc.le_mono_r(+a: Nat, +b: Nat, +c: Nat) -> {Nat.is_le(a, b) == True{} : Bool} -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  match a b:
    case 0n _:
      h => Jc.le_eq(c, Nat.add(b, c), Nat.add(c, b), Jc.add_comm(b, c), Jc.le_add_r(c, b))
    case 1n+p 0n:
      h => Ext4Proof.no({Nat.is_le(Nat.add(1n+p, c), Nat.add(0n, c)) == True{} : Bool}, h)
    case 1n+p 1n+q:
      h => Jc.le_mono_r(p, q, c, h)

def Jc.le_add2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  Ext4Proof.le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), Jc.le_mono_r(a, b, c, h1), Jc.le_mono_l(b, c, d, h2))

# a <= b: not (b < a)
def Jc.le_not_lt(+a: Nat, +b: Nat) -> {Nat.is_le(a, b) == True{} : Bool} -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      h => {==}
    case 0n 1n+q:
      h => {==}
    case 1n+p 0n:
      h => Ext4Proof.no({Nat.is_lt(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      h => Jc.le_not_lt(p, q, h)

def Jc.not_t(+x: Bool) -> {Bool.not(x) == True{} : Bool} -> {x == False{} : Bool}:
  match x:
    case True{}:
      h => Ext4Proof.no({True{} == False{} : Bool}, h)
    case False{}:
      h => {==}

# 0 < x, x <= y - c: c + x <= y
def Jc.le_sub_add(+c: Nat, +y: Nat, +x: Nat) -> {Nat.is_lt(0n, x) == True{} : Bool} -> {Nat.is_le(x, Nat.sub(y, c)) == True{} : Bool} -> {Nat.is_le(Nat.add(c, x), y) == True{} : Bool}:
  match c y:
    case 0n 0n:
      +p => +h => Ext4Proof.no({Nat.is_le(Nat.add(0n, x), 0n) == True{} : Bool}, Ext4Proof.ne_clash(Nat.is_lt(0n, x), p, Jc.le_not_lt(x, 0n, h)))
    case 0n 1n+q:
      +p => +h => h
    case 1n+k 0n:
      +p => +h => Ext4Proof.no({Nat.is_le(Nat.add(1n+k, x), 0n) == True{} : Bool}, Ext4Proof.ne_clash(Nat.is_lt(0n, x), p, Jc.le_not_lt(x, 0n, h)))
    case 1n+k 1n+q:
      +p => +h => Jc.le_sub_add(k, q, x, p, h)

# i + n <= m: n <= m - i
def Jc.le_sub(+i: Nat, +n: Nat, +m: Nat) -> {Nat.is_le(Nat.add(i, n), m) == True{} : Bool} -> {Nat.is_le(n, Nat.sub(m, i)) == True{} : Bool}:
  match i m:
    case 0n 0n:
      h => h
    case 0n 1n+q:
      h => h
    case 1n+p 0n:
      h => Ext4Proof.no({Nat.is_le(n, Nat.sub(0n, 1n+p)) == True{} : Bool}, h)
    case 1n+p 1n+q:
      h => Jc.le_sub(p, n, q, h)

# Division by 8 (the descriptor walk's fuel is the area's size / 8, plus 1)

def Jc.go_ge(+n: Nat, +m: Nat, +q: Nat, +r: Nat) -> {Nat.is_le(q, Pair.fst(Nat, Nat, Nat.divmod.go(n, m, q, r))) == True{} : Bool}:
  match n:
    case 0n:
      Ext4Proof.le_refl(q)
    case 1n+np:
      match m:
        case 0n:
          Ext4Proof.le_trans(q, 1n+q, Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+q, 0n)), Jc.le_succ(q), Jc.go_ge(np, r, 1n+q, 0n))
        case 1n+mp:
          Jc.go_ge(np, mp, q, 1n+r)

def Jc.go8(+k: Nat, +e: Nat, +q: Nat) -> {Pair.fst(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(k, 8n), e), 7n, q, 0n)) == Pair.fst(Nat, Nat, Nat.divmod.go(e, 7n, Nat.add(k, q), 0n)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(p, 8n), e), 7n, 1n+q, 0n)), Pair.fst(Nat, Nat, Nat.divmod.go(e, 7n, Nat.add(p, 1n+q), 0n)), Pair.fst(Nat, Nat, Nat.divmod.go(e, 7n, 1n+Nat.add(p, q), 0n)),
        Jc.go8(p, e, 1n+q),
        Equal.cong(Nat, Nat, x => Pair.fst(Nat, Nat, Nat.divmod.go(e, 7n, x, 0n)), Nat.add(p, 1n+q), 1n+Nat.add(p, q), Jc.add_succ(p, q)))

def Jc.div8(+k: Nat, +n: Nat, +h: {Nat.is_le(Nat.mul(k, 8n), n) == True{} : Bool}) -> {Nat.is_le(k, Nat.div(n, 8n)) == True{} : Bool}:
  +e = Nat.sub(n, Nat.mul(k, 8n))
  %Jc.add_sub(Nat.mul(k, 8n), n, h) : {Nat.is_le(k, Pair.fst(Nat, Nat, Nat.divmod.go(_, 7n, 0n, 0n))) == True{} : Bool}
  %Equal.sym(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(k, 8n), e), 7n, 0n, 0n)), Pair.fst(Nat, Nat, Nat.divmod.go(e, 7n, Nat.add(k, 0n), 0n)), Jc.go8(k, e, 0n)) : {Nat.is_le(k, _) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(k, 0n), k, Jc.add_zero(k)) : {Nat.is_le(k, Pair.fst(Nat, Nat, Nat.divmod.go(e, 7n, _, 0n))) == True{} : Bool}
  Jc.go_ge(e, 7n, k, 0n)

# Descriptor tags: every tag takes at least 8 bytes

def Jc.ts8(+g: J.Jbd2Geom) -> {Nat.is_le(8n, J.Jbd2Geom.tag_size(g)) == True{} : Bool}:
  match g:
    case J.Jbd2Geom{bs, w, cs, sd, fi, mx}:
      match w:
        case True{}:
          match cs:
            case 0n:
              {==}
            case 1n+q1:
              match q1:
                case 0n:
                  {==}
                case 1n+q2:
                  match q2:
                    case 0n:
                      {==}
                    case 1n+q3:
                      match q3:
                        case 0n:
                          {==}
                        case 1n+q4:
                          {==}
        case False{}:
          match cs:
            case 0n:
              {==}
            case 1n+q1:
              match q1:
                case 0n:
                  {==}
                case 1n+q2:
                  match q2:
                    case 0n:
                      {==}
                    case 1n+q3:
                      match q3:
                        case 0n:
                          {==}
                        case 1n+q4:
                          {==}

def Jc.size8(+g: J.Jbd2Geom, +t: JB.Jbd2Tag) -> {Nat.is_le(8n, JB.Jbd2Tag.size(g, t)) == True{} : Bool}:
  Ext4Proof.le_trans(8n, J.Jbd2Geom.tag_size(g), JB.Jbd2Tag.size(g, t), Jc.ts8(g), Jc.le_add_r(J.Jbd2Geom.tag_size(g), JB.Jbd2Tag.uuid.pick(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_same_uuid()))))

# the bytes the tags take: each tag's fields and UUID (if any), in order

def Jc.tu(+t: JB.Jbd2Tag, +uuid: B.Octets) -> B.Octets:
  JB.Jbd2Desc.tag_uuid(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_same_uuid()), uuid)

def Jc.tb(+g: J.Jbd2Geom, ts: List<&2, JB.Jbd2Tag>, +uuid: B.Octets) -> List<&2, B.Octets>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, rest}:
      Con{JB.Jbd2Tag.encode(g, t), Con{Jc.tu(t, uuid), Jc.tb(g, rest, uuid)}}

def Jc.ER(+g: J.Jbd2Geom, ts: List<&2, JB.Jbd2Tag>, +uuid: B.Octets, +r: B.Octets) -> B.Octets:
  match ts:
    case Nil{}:
      r
    case Con{+t, rest}:
      B.Octets.append(JB.Jbd2Tag.encode(g, t), B.Octets.append(Jc.tu(t, uuid), Jc.ER(g, rest, uuid, r)))

def Jc.sizes(+g: J.Jbd2Geom, ts: List<&2, JB.Jbd2Tag>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case Con{+t, rest}:
      Nat.add(JB.Jbd2Tag.size(g, t), Jc.sizes(g, rest))

def Jc.tb_acc(+g: J.Jbd2Geom, ts: List<&2, JB.Jbd2Tag>, +uuid: B.Octets, +acc: List<&2, B.Octets>) -> {JB.Jbd2Desc.tag_bytes(g, ts, uuid, acc) == List.reverse.go(&2, B.Octets, acc, Jc.tb(g, ts, uuid)) : List<&2, B.Octets>}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, rest}:
      Jc.tb_acc(g, rest, uuid, Con{Jc.tu(t, uuid), Con{JB.Jbd2Tag.encode(g, t), acc}})

def Jc.concat_tb(+g: J.Jbd2Geom, ts: List<&2, JB.Jbd2Tag>, +uuid: B.Octets, +r: B.Octets) -> {B.Octets.append(B.Octets.concat(Jc.tb(g, ts, uuid)), r) == Jc.ER(g, ts, uuid, r) : B.Octets}:
  match ts:
    case Nil{}:
      %BL.octets_concat_nil() : {B.Octets.append(_, r) == r : B.Octets}
      BL.octets_append_empty_l(r)
    case Con{+t, +rest}:
      +e = JB.Jbd2Tag.encode(g, t)
      +u = Jc.tu(t, uuid)
      +c = B.Octets.concat(Jc.tb(g, rest, uuid))
      %Equal.sym(B.Octets, B.Octets.concat(Con{e, Con{u, Jc.tb(g, rest, uuid)}}), B.Octets.append(e, B.Octets.concat(Con{u, Jc.tb(g, rest, uuid)})), BL.octets_concat_cons(e, Con{u, Jc.tb(g, rest, uuid)})) : {B.Octets.append(_, r) == Jc.ER(g, Con{t, rest}, uuid, r) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.concat(Con{u, Jc.tb(g, rest, uuid)}), B.Octets.append(u, c), BL.octets_concat_cons(u, Jc.tb(g, rest, uuid))) : {B.Octets.append(B.Octets.append(e, _), r) == Jc.ER(g, Con{t, rest}, uuid, r) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.append(B.Octets.append(e, B.Octets.append(u, c)), r), B.Octets.append(e, B.Octets.append(B.Octets.append(u, c), r)), BL.octets_append_assoc(e, B.Octets.append(u, c), r)) : {_ == Jc.ER(g, Con{t, rest}, uuid, r) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.append(B.Octets.append(u, c), r), B.Octets.append(u, B.Octets.append(c, r)), BL.octets_append_assoc(u, c, r)) : {B.Octets.append(e, _) == Jc.ER(g, Con{t, rest}, uuid, r) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.append(c, r), Jc.ER(g, rest, uuid, r), Jc.concat_tb(g, rest, uuid, r)) : {B.Octets.append(e, B.Octets.append(u, _)) == Jc.ER(g, Con{t, rest}, uuid, r) : B.Octets}
      {==}

def Jc.len_tu(b: Bool, +uuid: B.Octets, hu: {Nat.is_eq(B.Octets.len(uuid), 16n) == True{} : Bool}) -> {B.Octets.len(JB.Jbd2Desc.tag_uuid(b, uuid)) == JB.Jbd2Tag.uuid.pick(b) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      Ext4Proof.eq_sound(B.Octets.len(uuid), 16n, hu)

def Jc.len_tb(+g: J.Jbd2Geom, ts: List<&2, JB.Jbd2Tag>, +uuid: B.Octets, +hu: {Nat.is_eq(B.Octets.len(uuid), 16n) == True{} : Bool}) -> {B.Octets.len(Jc.ER(g, ts, uuid, B.Octets.empty())) == Jc.sizes(g, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +rest}:
      +f = JB.Jbd2Tag.flags(t)
      +pk = JB.Jbd2Tag.uuid.pick(J.Jbd2.has(f, JB.Jbd2.flag_same_uuid()))
      Equal.trans(Nat, B.Octets.len(Jc.ER(g, Con{t, rest}, uuid, B.Octets.empty())), Nat.add(J.Jbd2Geom.tag_size(g), Nat.add(pk, Jc.sizes(g, rest))), Jc.sizes(g, Con{t, rest}),
        Jc.len2(JB.Jbd2Tag.encode(g, t), B.Octets.append(Jc.tu(t, uuid), Jc.ER(g, rest, uuid, B.Octets.empty())), J.Jbd2Geom.tag_size(g), Nat.add(pk, Jc.sizes(g, rest)), Jc.tag_len(g, t),
          Jc.len2(Jc.tu(t, uuid), Jc.ER(g, rest, uuid, B.Octets.empty()), pk, Jc.sizes(g, rest), Jc.len_tu(J.Jbd2.has(f, JB.Jbd2.flag_same_uuid()), uuid, hu), Jc.len_tb(g, rest, uuid, hu))),
        Equal.sym(Nat, Nat.add(Nat.add(J.Jbd2Geom.tag_size(g), pk), Jc.sizes(g, rest)), Nat.add(J.Jbd2Geom.tag_size(g), Nat.add(pk, Jc.sizes(g, rest))), Jc.add_assoc(J.Jbd2Geom.tag_size(g), pk, Jc.sizes(g, rest))))

# the tag's fields and UUID, dropped, leave what follows
def Jc.drop_tag(+g: J.Jbd2Geom, +t: JB.Jbd2Tag, +uuid: B.Octets, +x: B.Octets, hu: {Nat.is_eq(B.Octets.len(uuid), 16n) == True{} : Bool}) -> {B.Octets.drop(JB.Jbd2Tag.size(g, t), B.Octets.append(JB.Jbd2Tag.encode(g, t), B.Octets.append(Jc.tu(t, uuid), x))) == x : B.Octets}:
  +e = JB.Jbd2Tag.encode(g, t)
  +u = Jc.tu(t, uuid)
  +pk = JB.Jbd2Tag.uuid.pick(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_same_uuid()))
  +ln = Equal.trans(Nat, B.Octets.len(B.Octets.append(e, u)), Nat.add(J.Jbd2Geom.tag_size(g), pk), JB.Jbd2Tag.size(g, t), Jc.len2(e, u, J.Jbd2Geom.tag_size(g), pk, Jc.tag_len(g, t), Jc.len_tu(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_same_uuid()), uuid, hu)), {==})
  %ln : {B.Octets.drop(_, B.Octets.append(e, B.Octets.append(u, x))) == x : B.Octets}
  %BL.octets_append_assoc(e, u, x) : {B.Octets.drop(B.Octets.len(B.Octets.append(e, u)), _) == x : B.Octets}
  BL.octets_drop_append(B.Octets.append(e, u), x)

# One step of the walk: a storable tag at the head of the area, with room
def Jc.step_t(+g: J.Jbd2Geom, +o: B.Octets, +avail: Nat, +t: JB.Jbd2Tag, hroom: {Nat.is_le(J.Jbd2Geom.tag_size(g), avail) == True{} : Bool}, hp: {JB.Jbd2Tag.parse(g, o) == t : JB.Jbd2Tag}) -> {JB.Jbd2Tag.step(g, o, avail) == JB.Jbd2TagAt{t, JB.Jbd2Tag.size(g, t), Bool.or(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_last()), Nat.is_lt(avail, Nat.add(JB.Jbd2Tag.size(g, t), J.Jbd2Geom.tag_size(g))))} : JB.Jbd2TagStep}:
  %Equal.sym(JB.Jbd2TagStep, JB.Jbd2Tag.step(g, o, avail), JB.Jbd2Tag.step.go(Nat.is_le(J.Jbd2Geom.tag_size(g), avail), g, o, avail), {==}) : {_ == JB.Jbd2TagAt{t, JB.Jbd2Tag.size(g, t), Bool.or(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_last()), Nat.is_lt(avail, Nat.add(JB.Jbd2Tag.size(g, t), J.Jbd2Geom.tag_size(g))))} : JB.Jbd2TagStep}
  %Equal.sym(Bool, Nat.is_le(J.Jbd2Geom.tag_size(g), avail), True{}, hroom) : {JB.Jbd2Tag.step.go(_, g, o, avail) == JB.Jbd2TagAt{t, JB.Jbd2Tag.size(g, t), Bool.or(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_last()), Nat.is_lt(avail, Nat.add(JB.Jbd2Tag.size(g, t), J.Jbd2Geom.tag_size(g))))} : JB.Jbd2TagStep}
  Equal.cong(JB.Jbd2Tag, JB.Jbd2TagStep, x => JB.Jbd2TagAt{x, JB.Jbd2Tag.size(g, x), Bool.or(J.Jbd2.has(JB.Jbd2Tag.flags(x), JB.Jbd2.flag_last()), Nat.is_lt(avail, Nat.add(JB.Jbd2Tag.size(g, x), J.Jbd2Geom.tag_size(g))))}, JB.Jbd2Tag.parse(g, o), t, hp)

# The walk over the tag area reads back every tag, given they fit it
def Jc.walk_last(+f: Nat, +g: J.Jbd2Geom, +t: JB.Jbd2Tag, +uuid: B.Octets, +r: B.Octets, +avail: Nat, +acc: List<&2, JB.Jbd2Tag>, +hf: {JB.Jbd2Desc.fits.go(g, Con{t, Nil{}}, avail) == True{} : Bool}) -> {JB.Jbd2Desc.walk(1n+f, JB.Jbd2Tag.step(g, Jc.ER(g, Con{t, Nil{}}, uuid, r), avail), Jc.ER(g, Con{t, Nil{}}, uuid, r), avail, g, acc) == List.reverse.go(&2, JB.Jbd2Tag, acc, Con{t, Nil{}}) : List<&2, JB.Jbd2Tag>}:
  +o = Jc.ER(g, Con{t, Nil{}}, uuid, r)
  +hs = Ext4Proof.and_l(JB.Jbd2Tag.storable(g, t), Bool.and(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_last()), Nat.is_le(JB.Jbd2Tag.size(g, t), avail)), hf)
  +h2 = Ext4Proof.and_r(JB.Jbd2Tag.storable(g, t), Bool.and(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_last()), Nat.is_le(JB.Jbd2Tag.size(g, t), avail)), hf)
  +hl = Ext4Proof.and_l(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_last()), Nat.is_le(JB.Jbd2Tag.size(g, t), avail), h2)
  +hz = Ext4Proof.and_r(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_last()), Nat.is_le(JB.Jbd2Tag.size(g, t), avail), h2)
  +hroom = Jc.le_add_l(J.Jbd2Geom.tag_size(g), JB.Jbd2Tag.uuid.pick(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_same_uuid())), avail, hz)
  +hp = Jc.tag_rt2(g, t, B.Octets.append(Jc.tu(t, uuid), r), hs)
  %Equal.sym(JB.Jbd2TagStep, JB.Jbd2Tag.step(g, o, avail), JB.Jbd2TagAt{t, JB.Jbd2Tag.size(g, t), Bool.or(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_last()), Nat.is_lt(avail, Nat.add(JB.Jbd2Tag.size(g, t), J.Jbd2Geom.tag_size(g))))}, Jc.step_t(g, o, avail, t, hroom, hp)) : {JB.Jbd2Desc.walk(1n+f, _, o, avail, g, acc) == List.reverse.go(&2, JB.Jbd2Tag, acc, Con{t, Nil{}}) : List<&2, JB.Jbd2Tag>}
  %Equal.sym(Bool, J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_last()), True{}, hl) : {JB.Jbd2Desc.walk(1n+f, JB.Jbd2TagAt{t, JB.Jbd2Tag.size(g, t), Bool.or(_, Nat.is_lt(avail, Nat.add(JB.Jbd2Tag.size(g, t), J.Jbd2Geom.tag_size(g))))}, o, avail, g, acc) == List.reverse.go(&2, JB.Jbd2Tag, acc, Con{t, Nil{}}) : List<&2, JB.Jbd2Tag>}
  {==}

def Jc.walk_more(+f: Nat, +g: J.Jbd2Geom, +t: JB.Jbd2Tag, +rest: List<&2, JB.Jbd2Tag>, +uuid: B.Octets, +r: B.Octets, +avail: Nat, +acc: List<&2, JB.Jbd2Tag>, hu: {Nat.is_eq(B.Octets.len(uuid), 16n) == True{} : Bool}, +hs: {JB.Jbd2Tag.storable(g, t) == True{} : Bool}, hl: {J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_last()) == False{} : Bool}, +hz: {Nat.is_le(Nat.add(JB.Jbd2Tag.size(g, t), J.Jbd2Geom.tag_size(g)), avail) == True{} : Bool}, ih: {JB.Jbd2Desc.walk(f, JB.Jbd2Tag.step(g, Jc.ER(g, rest, uuid, r), Nat.sub(avail, JB.Jbd2Tag.size(g, t))), Jc.ER(g, rest, uuid, r), Nat.sub(avail, JB.Jbd2Tag.size(g, t)), g, Con{t, acc}) == List.reverse.go(&2, JB.Jbd2Tag, Con{t, acc}, rest) : List<&2, JB.Jbd2Tag>}) -> {JB.Jbd2Desc.walk(1n+f, JB.Jbd2Tag.step(g, Jc.ER(g, Con{t, rest}, uuid, r), avail), Jc.ER(g, Con{t, rest}, uuid, r), avail, g, acc) == List.reverse.go(&2, JB.Jbd2Tag, acc, Con{t, rest}) : List<&2, JB.Jbd2Tag>}:
  +o = Jc.ER(g, Con{t, rest}, uuid, r)
  +x = Jc.ER(g, rest, uuid, r)
  +sz = JB.Jbd2Tag.size(g, t)
  +hroom = Jc.le_add_l(J.Jbd2Geom.tag_size(g), JB.Jbd2Tag.uuid.pick(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_same_uuid())), avail, Jc.le_add_l(sz, J.Jbd2Geom.tag_size(g), avail, hz))
  +hp = Jc.tag_rt2(g, t, B.Octets.append(Jc.tu(t, uuid), x), hs)
  %Equal.sym(JB.Jbd2TagStep, JB.Jbd2Tag.step(g, o, avail), JB.Jbd2TagAt{t, sz, Bool.or(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_last()), Nat.is_lt(avail, Nat.add(sz, J.Jbd2Geom.tag_size(g))))}, Jc.step_t(g, o, avail, t, hroom, hp)) : {JB.Jbd2Desc.walk(1n+f, _, o, avail, g, acc) == List.reverse.go(&2, JB.Jbd2Tag, acc, Con{t, rest}) : List<&2, JB.Jbd2Tag>}
  %Equal.sym(Bool, J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_last()), False{}, hl) : {JB.Jbd2Desc.walk(1n+f, JB.Jbd2TagAt{t, sz, Bool.or(_, Nat.is_lt(avail, Nat.add(sz, J.Jbd2Geom.tag_size(g))))}, o, avail, g, acc) == List.reverse.go(&2, JB.Jbd2Tag, acc, Con{t, rest}) : List<&2, JB.Jbd2Tag>}
  %Equal.sym(Bool, Nat.is_lt(avail, Nat.add(sz, J.Jbd2Geom.tag_size(g))), False{}, Jc.le_not_lt(Nat.add(sz, J.Jbd2Geom.tag_size(g)), avail, hz)) : {JB.Jbd2Desc.walk(1n+f, JB.Jbd2TagAt{t, sz, Bool.or(False{}, _)}, o, avail, g, acc) == List.reverse.go(&2, JB.Jbd2Tag, acc, Con{t, rest}) : List<&2, JB.Jbd2Tag>}
  %Equal.sym(B.Octets, B.Octets.drop(sz, o), x, Jc.drop_tag(g, t, uuid, x, hu)) : {JB.Jbd2Desc.walk(f, JB.Jbd2Tag.step(g, _, Nat.sub(avail, sz)), _, Nat.sub(avail, sz), g, Con{t, acc}) == List.reverse.go(&2, JB.Jbd2Tag, acc, Con{t, rest}) : List<&2, JB.Jbd2Tag>}
  ih

def Jc.walk_rt(ts: List<&2, JB.Jbd2Tag>, +f: Nat, +g: J.Jbd2Geom, +uuid: B.Octets, +r: B.Octets, +avail: Nat, +acc: List<&2, JB.Jbd2Tag>) -> {Nat.is_eq(B.Octets.len(uuid), 16n) == True{} : Bool} -> {JB.Jbd2Desc.fits.go(g, ts, avail) == True{} : Bool} -> {Nat.is_le(List.length(&2, JB.Jbd2Tag, ts), f) == True{} : Bool} -> {JB.Jbd2Desc.walk(f, JB.Jbd2Tag.step(g, Jc.ER(g, ts, uuid, r), avail), Jc.ER(g, ts, uuid, r), avail, g, acc) == List.reverse.go(&2, JB.Jbd2Tag, acc, ts) : List<&2, JB.Jbd2Tag>}:
  match ts f:
    case Nil{} _:
      +hu => +hf => +hn => Ext4Proof.no({JB.Jbd2Desc.walk(f, JB.Jbd2Tag.step(g, r, avail), r, avail, g, acc) == List.reverse.go(&2, JB.Jbd2Tag, acc, Nil{}) : List<&2, JB.Jbd2Tag>}, hf)
    case Con{+t, +rest} 0n:
      +hu => +hf => +hn => Ext4Proof.no({JB.Jbd2Desc.walk(0n, JB.Jbd2Tag.step(g, Jc.ER(g, Con{t, rest}, uuid, r), avail), Jc.ER(g, Con{t, rest}, uuid, r), avail, g, acc) == List.reverse.go(&2, JB.Jbd2Tag, acc, Con{t, rest}) : List<&2, JB.Jbd2Tag>}, hn)
    case Con{+t, Nil{}} 1n+fp:
      +hu => +hf => +hn => Jc.walk_last(fp, g, t, uuid, r, avail, acc, hf)
    case Con{+t, Con{+t2, +r2}} 1n+fp:
      +hu => +hf => +hn =>
        +sz = JB.Jbd2Tag.size(g, t)
        +a1 = JB.Jbd2Tag.storable(g, t)
        +a2 = Bool.not(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_last()))
        +a3 = Nat.is_le(Nat.add(sz, J.Jbd2Geom.tag_size(g)), avail)
        +a4 = JB.Jbd2Desc.fits.go(g, Con{t2, r2}, Nat.sub(avail, sz))
        +h234 = Ext4Proof.and_r(a1, Bool.and(a2, Bool.and(a3, a4)), hf)
        +h34 = Ext4Proof.and_r(a2, Bool.and(a3, a4), h234)
        Jc.walk_more(fp, g, t, Con{t2, r2}, uuid, r, avail, acc, hu, Ext4Proof.and_l(a1, Bool.and(a2, Bool.and(a3, a4)), hf), Jc.not_t(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_last()), Ext4Proof.and_l(a2, Bool.and(a3, a4), h234)), Ext4Proof.and_l(a3, a4, h34), Jc.walk_rt(Con{t2, r2}, fp, g, uuid, r, Nat.sub(avail, sz), Con{t, acc}, hu, Ext4Proof.and_r(a3, a4, h34), hn))

# What fitting the area bounds: the tags' bytes, and their count (8 bytes
# a tag at least)

def Jc.le_eql(+a: Nat, +b: Nat, +y: Nat, e: {a == b : Nat}, h: {Nat.is_le(b, y) == True{} : Bool}) -> {Nat.is_le(a, y) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(a, y), Nat.is_le(b, y), True{}, Equal.cong(Nat, Bool, k => Nat.is_le(k, y), a, b, e), h)

def Jc.lt0(+x: Nat) -> {Nat.is_le(8n, x) == True{} : Bool} -> {Nat.is_lt(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      h => Ext4Proof.no({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
    case 1n+p:
      h => {==}

def Jc.fits_parts(+g: J.Jbd2Geom, +t: JB.Jbd2Tag, +t2: JB.Jbd2Tag, +r2: List<&2, JB.Jbd2Tag>, +avail: Nat, +hf: {JB.Jbd2Desc.fits.go(g, Con{t, Con{t2, r2}}, avail) == True{} : Bool}) -> {Bool.and(Nat.is_le(Nat.add(JB.Jbd2Tag.size(g, t), J.Jbd2Geom.tag_size(g)), avail), JB.Jbd2Desc.fits.go(g, Con{t2, r2}, Nat.sub(avail, JB.Jbd2Tag.size(g, t)))) == True{} : Bool}:
  +sz = JB.Jbd2Tag.size(g, t)
  +a1 = JB.Jbd2Tag.storable(g, t)
  +a2 = Bool.not(J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_last()))
  +a3 = Nat.is_le(Nat.add(sz, J.Jbd2Geom.tag_size(g)), avail)
  +a4 = JB.Jbd2Desc.fits.go(g, Con{t2, r2}, Nat.sub(avail, sz))
  Ext4Proof.and_r(a2, Bool.and(a3, a4), Ext4Proof.and_r(a1, Bool.and(a2, Bool.and(a3, a4)), hf))

def Jc.fits_one(+g: J.Jbd2Geom, +t: JB.Jbd2Tag, +avail: Nat, +hf: {JB.Jbd2Desc.fits.go(g, Con{t, Nil{}}, avail) == True{} : Bool}) -> {Nat.is_le(JB.Jbd2Tag.size(g, t), avail) == True{} : Bool}:
  +a2 = J.Jbd2.has(JB.Jbd2Tag.flags(t), JB.Jbd2.flag_last())
  +a3 = Nat.is_le(JB.Jbd2Tag.size(g, t), avail)
  Ext4Proof.and_r(a2, a3, Ext4Proof.and_r(JB.Jbd2Tag.storable(g, t), Bool.and(a2, a3), hf))

def Jc.fm8(ts: List<&2, JB.Jbd2Tag>, +g: J.Jbd2Geom, +avail: Nat) -> {JB.Jbd2Desc.fits.go(g, ts, avail) == True{} : Bool} -> {Nat.is_le(Nat.mul(List.length(&2, JB.Jbd2Tag, ts), 8n), avail) == True{} : Bool}:
  match ts:
    case Nil{}:
      +hf => Ext4Proof.no({Nat.is_le(0n, avail) == True{} : Bool}, hf)
    case Con{+t, Nil{}}:
      +hf => Ext4Proof.le_trans(8n, JB.Jbd2Tag.size(g, t), avail, Jc.size8(g, t), Jc.fits_one(g, t, avail, hf))
    case Con{+t, Con{+t2, +r2}}:
      +hf =>
        +sz = JB.Jbd2Tag.size(g, t)
        +a3 = Nat.is_le(Nat.add(sz, J.Jbd2Geom.tag_size(g)), avail)
        +a4 = JB.Jbd2Desc.fits.go(g, Con{t2, r2}, Nat.sub(avail, sz))
        +h34 = Jc.fits_parts(g, t, t2, r2, avail, hf)
        +hsz = Jc.le_add_l(sz, J.Jbd2Geom.tag_size(g), avail, Ext4Proof.and_l(a3, a4, h34))
        +m = Nat.mul(List.length(&2, JB.Jbd2Tag, Con{t2, r2}), 8n)
        Jc.le_eq(Nat.add(8n, m), avail, Nat.add(sz, Nat.sub(avail, sz)), Equal.sym(Nat, Nat.add(sz, Nat.sub(avail, sz)), avail, Jc.add_sub(sz, avail, hsz)),
          Jc.le_add2(8n, sz, m, Nat.sub(avail, sz), Jc.size8(g, t), Jc.fm8(Con{t2, r2}, g, Nat.sub(avail, sz), Ext4Proof.and_r(a3, a4, h34))))

def Jc.fsz(ts: List<&2, JB.Jbd2Tag>, +g: J.Jbd2Geom, +avail: Nat) -> {JB.Jbd2Desc.fits.go(g, ts, avail) == True{} : Bool} -> {Nat.is_le(Jc.sizes(g, ts), avail) == True{} : Bool}:
  match ts:
    case Nil{}:
      +hf => Ext4Proof.no({Nat.is_le(0n, avail) == True{} : Bool}, hf)
    case Con{+t, Nil{}}:
      +hf => Jc.le_eql(Nat.add(JB.Jbd2Tag.size(g, t), 0n), JB.Jbd2Tag.size(g, t), avail, Jc.add_zero(JB.Jbd2Tag.size(g, t)), Jc.fits_one(g, t, avail, hf))
    case Con{+t, Con{+t2, +r2}}:
      +hf =>
        +sz = JB.Jbd2Tag.size(g, t)
        +a3 = Nat.is_le(Nat.add(sz, J.Jbd2Geom.tag_size(g)), avail)
        +a4 = JB.Jbd2Desc.fits.go(g, Con{t2, r2}, Nat.sub(avail, sz))
        +h34 = Jc.fits_parts(g, t, t2, r2, avail, hf)
        +hsz = Jc.le_add_l(sz, J.Jbd2Geom.tag_size(g), avail, Ext4Proof.and_l(a3, a4, h34))
        Jc.le_eq(Nat.add(sz, Jc.sizes(g, Con{t2, r2})), avail, Nat.add(sz, Nat.sub(avail, sz)), Equal.sym(Nat, Nat.add(sz, Nat.sub(avail, sz)), avail, Jc.add_sub(sz, avail, hsz)),
          Jc.le_mono_l(sz, Jc.sizes(g, Con{t2, r2}), Nat.sub(avail, sz), Jc.fsz(Con{t2, r2}, g, Nat.sub(avail, sz), Ext4Proof.and_r(a3, a4, h34))))

def Jc.fpos(ts: List<&2, JB.Jbd2Tag>, +g: J.Jbd2Geom, +avail: Nat) -> {JB.Jbd2Desc.fits.go(g, ts, avail) == True{} : Bool} -> {Nat.is_lt(0n, Jc.sizes(g, ts)) == True{} : Bool}:
  match ts:
    case Nil{}:
      +hf => Ext4Proof.no({Nat.is_lt(0n, 0n) == True{} : Bool}, hf)
    case Con{+t, +rest}:
      +hf => Jc.lt0(Jc.sizes(g, Con{t, rest}), Ext4Proof.le_trans(8n, JB.Jbd2Tag.size(g, t), Jc.sizes(g, Con{t, rest}), Jc.size8(g, t), Jc.le_add_r(JB.Jbd2Tag.size(g, t), Jc.sizes(g, rest))))

# The descriptor block: its shape, the area after the header, the tail

def Jc.dbody(+g: J.Jbd2Geom, +seq: U32, +ts: List<&2, JB.Jbd2Tag>, +uuid: B.Octets) -> B.Octets:
  B.Octets.append(JB.Jbd2.header(JB.Jbd2.kind_desc(), seq), B.Octets.concat(JB.Jbd2Desc.tag_bytes(g, ts, uuid, Nil{})))

def Jc.dpad(+g: J.Jbd2Geom, +seq: U32, +ts: List<&2, JB.Jbd2Tag>, +uuid: B.Octets) -> B.Octets:
  B.Octets.zeros(Nat.sub(Nat.sub(J.Jbd2Geom.bs(g), J.Jbd2Geom.tail(g)), B.Octets.len(Jc.dbody(g, seq, ts, uuid))))

def Jc.dshape(+g: J.Jbd2Geom, +seq: U32, +ts: List<&2, JB.Jbd2Tag>, +uuid: B.Octets) -> {JB.Jbd2Desc.encode(g, seq, ts, uuid) == JB.Jbd2Block.seal(J.Jbd2Geom.has_csum(g), g, B.Octets.append(Jc.dbody(g, seq, ts, uuid), Jc.dpad(g, seq, ts, uuid))) : B.Octets}:
  {==}

def Jc.bseal_t(+g: J.Jbd2Geom, +x: B.Octets) -> {JB.Jbd2Block.seal(True{}, g, x) == B.Octets.append(x, B.Octets.be32(JB.Jbd2Block.tail_csum(g, B.Octets.append(x, B.Octets.zeros(4n))))) : B.Octets}:
  {==}

def Jc.bseal_f(+g: J.Jbd2Geom, +x: B.Octets) -> {JB.Jbd2Block.seal(False{}, g, x) == x : B.Octets}:
  {==}

def Jc.dec_go(+check: Bool, +g: J.Jbd2Geom, +x: B.Octets) -> {JB.Jbd2Desc.decode(check, g, x) == JB.Jbd2Desc.decode.go(JB.Jbd2Block.tail_ok(check, g, x), g, x) : Maybe<&2, List<&2, JB.Jbd2Tag>>}:
  {==}

def Jc.dgo_t(+g: J.Jbd2Geom, +x: B.Octets) -> {JB.Jbd2Desc.decode.go(True{}, g, x) == Some{JB.Jbd2Desc.tags(g, x)} : Maybe<&2, List<&2, JB.Jbd2Tag>>}:
  {==}

def Jc.darea(+g: J.Jbd2Geom) -> Nat:
  Nat.sub(Nat.sub(J.Jbd2Geom.bs(g), 12n), J.Jbd2Geom.tail(g))

def Jc.tags_go(+g: J.Jbd2Geom, +x: B.Octets) -> {JB.Jbd2Desc.tags(g, x) == JB.Jbd2Desc.walk(Nat.add(Nat.div(Jc.darea(g), 8n), 1n), JB.Jbd2Tag.step(g, B.Octets.drop(12n, x), Jc.darea(g)), B.Octets.drop(12n, x), Jc.darea(g), g, Nil{}) : List<&2, JB.Jbd2Tag>}:
  {==}

def Jc.area(+g: J.Jbd2Geom, +seq: U32, +ts: List<&2, JB.Jbd2Tag>, +uuid: B.Octets, +z: B.Octets) -> {B.Octets.drop(12n, B.Octets.append(Jc.dbody(g, seq, ts, uuid), z)) == Jc.ER(g, ts, uuid, z) : B.Octets}:
  +h = JB.Jbd2.header(JB.Jbd2.kind_desc(), seq)
  +c = B.Octets.concat(JB.Jbd2Desc.tag_bytes(g, ts, uuid, Nil{}))
  %Jc.app3(h, c, z) : {B.Octets.drop(12n, _) == Jc.ER(g, ts, uuid, z) : B.Octets}
  %Jc.hdr_len(JB.Jbd2.kind_desc(), seq) : {B.Octets.drop(_, B.Octets.append(h, B.Octets.append(c, z))) == Jc.ER(g, ts, uuid, z) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(h), B.Octets.append(h, B.Octets.append(c, z))), B.Octets.append(c, z), BL.octets_drop_append(h, B.Octets.append(c, z))) : {_ == Jc.ER(g, ts, uuid, z) : B.Octets}
  %Equal.sym(List<&2, B.Octets>, JB.Jbd2Desc.tag_bytes(g, ts, uuid, Nil{}), List.reverse.go(&2, B.Octets, Nil{}, Jc.tb(g, ts, uuid)), Jc.tb_acc(g, ts, uuid, Nil{})) : {B.Octets.append(B.Octets.concat(_), z) == Jc.ER(g, ts, uuid, z) : B.Octets}
  Jc.concat_tb(g, ts, uuid, z)

# the tag bytes take the tags' sizes
def Jc.len_c(+g: J.Jbd2Geom, +ts: List<&2, JB.Jbd2Tag>, +uuid: B.Octets, +hu: {Nat.is_eq(B.Octets.len(uuid), 16n) == True{} : Bool}) -> {B.Octets.len(B.Octets.concat(JB.Jbd2Desc.tag_bytes(g, ts, uuid, Nil{}))) == Jc.sizes(g, ts) : Nat}:
  +cb = B.Octets.concat(Jc.tb(g, ts, uuid))
  +e1 = Equal.trans(B.Octets, cb, B.Octets.append(cb, B.Octets.empty()), Jc.ER(g, ts, uuid, B.Octets.empty()), Equal.sym(B.Octets, B.Octets.append(cb, B.Octets.empty()), cb, BL.octets_append_empty_r(cb)), Jc.concat_tb(g, ts, uuid, B.Octets.empty()))
  %Equal.sym(List<&2, B.Octets>, JB.Jbd2Desc.tag_bytes(g, ts, uuid, Nil{}), List.reverse.go(&2, B.Octets, Nil{}, Jc.tb(g, ts, uuid)), Jc.tb_acc(g, ts, uuid, Nil{})) : {B.Octets.len(B.Octets.concat(_)) == Jc.sizes(g, ts) : Nat}
  %Equal.sym(B.Octets, cb, Jc.ER(g, ts, uuid, B.Octets.empty()), e1) : {B.Octets.len(_) == Jc.sizes(g, ts) : Nat}
  Jc.len_tb(g, ts, uuid, hu)

def Jc.tail4(+g: J.Jbd2Geom, hb: {J.Jbd2Geom.has_csum(g) == True{} : Bool}) -> {J.Jbd2Geom.tail(g) == 4n : Nat}:
  %Equal.sym(Bool, J.Jbd2Geom.has_csum(g), True{}, hb) : {J.Jbd2Geom.tail.pick(_) == 4n : Nat}
  {==}

def Jc.tok_f(+check: Bool, +g: J.Jbd2Geom, +x: B.Octets, hb: {J.Jbd2Geom.has_csum(g) == False{} : Bool}) -> {JB.Jbd2Block.tail_ok(check, g, x) == True{} : Bool}:
  %Equal.sym(Bool, J.Jbd2Geom.has_csum(g), False{}, hb) : {Bool.or(Bool.not(Bool.and(check, _)), U32.is_eq(JB.Jbd2Block.tail_csum(g, x), J.Jbd2.be32(x, Nat.sub(J.Jbd2Geom.bs(g), 4n)))) == True{} : Bool}
  Jc.or_not_and_f(check, U32.is_eq(JB.Jbd2Block.tail_csum(g, x), J.Jbd2.be32(x, Nat.sub(J.Jbd2Geom.bs(g), 4n))))

# the tail checksum over a block whose first bs - 4 bytes are p
def Jc.tcs(+g: J.Jbd2Geom, +p: B.Octets, +x: B.Octets, lp: {B.Octets.len(p) == Nat.sub(J.Jbd2Geom.bs(g), 4n) : Nat}) -> {JB.Jbd2Block.tail_csum(g, B.Octets.append(p, x)) == K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(J.Jbd2Geom.seed(g), p), B.Octets.zeros(4n)) : U32}:
  %lp : {K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(J.Jbd2Geom.seed(g), B.Octets.take(_, B.Octets.append(p, x))), B.Octets.zeros(4n)) == K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(J.Jbd2Geom.seed(g), p), B.Octets.zeros(4n)) : U32}
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(p), B.Octets.append(p, x)), p, BL.octets_take_append(p, x)) : {K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(J.Jbd2Geom.seed(g), _), B.Octets.zeros(4n)) == K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(J.Jbd2Geom.seed(g), p), B.Octets.zeros(4n)) : U32}
  {==}

def Jc.tok_t(+check: Bool, +g: J.Jbd2Geom, +p: B.Octets, hb: {J.Jbd2Geom.has_csum(g) == True{} : Bool}, +lp: {B.Octets.len(p) == Nat.sub(J.Jbd2Geom.bs(g), 4n) : Nat}) -> {JB.Jbd2Block.tail_ok(check, g, B.Octets.append(p, B.Octets.be32(JB.Jbd2Block.tail_csum(g, B.Octets.append(p, B.Octets.zeros(4n)))))) == True{} : Bool}:
  +c = JB.Jbd2Block.tail_csum(g, B.Octets.append(p, B.Octets.zeros(4n)))
  +q = B.Octets.be32(c)
  +blk = B.Octets.append(p, q)
  +k = K.Ext2Csum.crc32c(K.Ext2Csum.crc32c(J.Jbd2Geom.seed(g), p), B.Octets.zeros(4n))
  %Equal.sym(Bool, J.Jbd2Geom.has_csum(g), True{}, hb) : {Bool.or(Bool.not(Bool.and(check, _)), U32.is_eq(JB.Jbd2Block.tail_csum(g, blk), J.Jbd2.be32(blk, Nat.sub(J.Jbd2Geom.bs(g), 4n)))) == True{} : Bool}
  %Equal.sym(U32, JB.Jbd2Block.tail_csum(g, blk), k, Jc.tcs(g, p, q, lp)) : {Bool.or(Bool.not(Bool.and(check, True{})), U32.is_eq(_, J.Jbd2.be32(blk, Nat.sub(J.Jbd2Geom.bs(g), 4n)))) == True{} : Bool}
  %Equal.trans(Nat, Nat.add(B.Octets.len(p), 0n), B.Octets.len(p), Nat.sub(J.Jbd2Geom.bs(g), 4n), Jc.add_zero(B.Octets.len(p)), lp) : {Bool.or(Bool.not(Bool.and(check, True{})), U32.is_eq(k, Maybe.default(&2, U32, B.Octets.be32_at(blk, _), 0))) == True{} : Bool}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(blk, Nat.add(B.Octets.len(p), 0n)), B.Octets.be32_at(q, 0n), BL.octets_be32_at_append_add(p, q, 0n)) : {Bool.or(Bool.not(Bool.and(check, True{})), U32.is_eq(k, Maybe.default(&2, U32, _, 0))) == True{} : Bool}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(q, 0n), Some{c}, BL.octets_be32_round_trip(c)) : {Bool.or(Bool.not(Bool.and(check, True{})), U32.is_eq(k, Maybe.default(&2, U32, _, 0))) == True{} : Bool}
  %Equal.sym(U32, c, k, Jc.tcs(g, p, B.Octets.zeros(4n), lp)) : {Bool.or(Bool.not(Bool.and(check, True{})), U32.is_eq(k, _)) == True{} : Bool}
  Jc.or_not_and_t(check, U32.is_eq(k, k), Jc.u32_refl(k))

# the walk's fuel suffices
def Jc.dfuel(+g: J.Jbd2Geom, +ts: List<&2, JB.Jbd2Tag>, +hf: {JB.Jbd2Desc.fits.go(g, ts, Jc.darea(g)) == True{} : Bool}) -> {Nat.is_le(List.length(&2, JB.Jbd2Tag, ts), Nat.add(Nat.div(Jc.darea(g), 8n), 1n)) == True{} : Bool}:
  Ext4Proof.le_trans(List.length(&2, JB.Jbd2Tag, ts), Nat.div(Jc.darea(g), 8n), Nat.add(Nat.div(Jc.darea(g), 8n), 1n), Jc.div8(List.length(&2, JB.Jbd2Tag, ts), Jc.darea(g), Jc.fm8(ts, g, Jc.darea(g), hf)), Jc.le_add_r(Nat.div(Jc.darea(g), 8n), 1n))

# without checksums
def Jc.desc_f(+check: Bool, +g: J.Jbd2Geom, +seq: U32, +ts: List<&2, JB.Jbd2Tag>, +uuid: B.Octets, +hu: {Nat.is_eq(B.Octets.len(uuid), 16n) == True{} : Bool}, +hf: {JB.Jbd2Desc.fits.go(g, ts, Jc.darea(g)) == True{} : Bool}, hb: {J.Jbd2Geom.has_csum(g) == False{} : Bool}) -> {JB.Jbd2Desc.decode(check, g, JB.Jbd2Block.seal(False{}, g, B.Octets.append(Jc.dbody(g, seq, ts, uuid), Jc.dpad(g, seq, ts, uuid)))) == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}:
  +z = Jc.dpad(g, seq, ts, uuid)
  +p = B.Octets.append(Jc.dbody(g, seq, ts, uuid), z)
  +n = Jc.darea(g)
  +fu = Nat.add(Nat.div(n, 8n), 1n)
  +er = Jc.ER(g, ts, uuid, z)
  %Equal.sym(B.Octets, JB.Jbd2Block.seal(False{}, g, p), p, Jc.bseal_f(g, p)) : {JB.Jbd2Desc.decode(check, g, _) == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}
  %Equal.sym(Maybe<&2, List<&2, JB.Jbd2Tag>>, JB.Jbd2Desc.decode(check, g, p), JB.Jbd2Desc.decode.go(JB.Jbd2Block.tail_ok(check, g, p), g, p), Jc.dec_go(check, g, p)) : {_ == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}
  %Equal.sym(Bool, JB.Jbd2Block.tail_ok(check, g, p), True{}, Jc.tok_f(check, g, p, hb)) : {JB.Jbd2Desc.decode.go(_, g, p) == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}
  %Equal.sym(Maybe<&2, List<&2, JB.Jbd2Tag>>, JB.Jbd2Desc.decode.go(True{}, g, p), Some{JB.Jbd2Desc.tags(g, p)}, Jc.dgo_t(g, p)) : {_ == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}
  %Equal.sym(List<&2, JB.Jbd2Tag>, JB.Jbd2Desc.tags(g, p), JB.Jbd2Desc.walk(fu, JB.Jbd2Tag.step(g, B.Octets.drop(12n, p), n), B.Octets.drop(12n, p), n, g, Nil{}), Jc.tags_go(g, p)) : {Some{_} == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}
  %Equal.sym(B.Octets, B.Octets.drop(12n, p), er, Jc.area(g, seq, ts, uuid, z)) : {Some{JB.Jbd2Desc.walk(fu, JB.Jbd2Tag.step(g, _, n), _, n, g, Nil{})} == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}
  Equal.cong(List<&2, JB.Jbd2Tag>, Maybe<&2, List<&2, JB.Jbd2Tag>>, l => Some{l}, JB.Jbd2Desc.walk(fu, JB.Jbd2Tag.step(g, er, n), er, n, g, Nil{}), ts, Jc.walk_rt(ts, fu, g, uuid, z, n, Nil{}, hu, hf, Jc.dfuel(g, ts, hf)))

# with checksums: the block before its tail is bs - 4 bytes
def Jc.dlen(+g: J.Jbd2Geom, +seq: U32, +ts: List<&2, JB.Jbd2Tag>, +uuid: B.Octets, +hu: {Nat.is_eq(B.Octets.len(uuid), 16n) == True{} : Bool}, +hf: {JB.Jbd2Desc.fits.go(g, ts, Jc.darea(g)) == True{} : Bool}, +hb: {J.Jbd2Geom.has_csum(g) == True{} : Bool}) -> {B.Octets.len(B.Octets.append(Jc.dbody(g, seq, ts, uuid), Jc.dpad(g, seq, ts, uuid))) == Nat.sub(J.Jbd2Geom.bs(g), 4n) : Nat}:
  +bd = Jc.dbody(g, seq, ts, uuid)
  +bs = J.Jbd2Geom.bs(g)
  +tg = J.Jbd2Geom.tail(g)
  +s = Jc.sizes(g, ts)
  +t4 = Jc.tail4(g, hb)
  +lb = Equal.trans(Nat, B.Octets.len(bd), Nat.add(12n, B.Octets.len(B.Octets.concat(JB.Jbd2Desc.tag_bytes(g, ts, uuid, Nil{})))), Nat.add(12n, s), Jc.len2(JB.Jbd2.header(JB.Jbd2.kind_desc(), seq), B.Octets.concat(JB.Jbd2Desc.tag_bytes(g, ts, uuid, Nil{})), 12n, B.Octets.len(B.Octets.concat(JB.Jbd2Desc.tag_bytes(g, ts, uuid, Nil{}))), Jc.hdr_len(JB.Jbd2.kind_desc(), seq), {==}), Equal.cong(Nat, Nat, k => Nat.add(12n, k), B.Octets.len(B.Octets.concat(JB.Jbd2Desc.tag_bytes(g, ts, uuid, Nil{}))), s, Jc.len_c(g, ts, uuid, hu)))
  +hs = Jc.le_eq(s, Nat.sub(Nat.sub(bs, 12n), 4n), Jc.darea(g), Equal.cong(Nat, Nat, k => Nat.sub(Nat.sub(bs, 12n), k), 4n, tg, Equal.sym(Nat, tg, 4n, t4)), Jc.fsz(ts, g, Jc.darea(g), hf))
  +h1 = Jc.le_sub_add(4n, Nat.sub(bs, 12n), s, Jc.fpos(ts, g, Jc.darea(g), hf), hs)
  +h2 = Jc.le_sub_add(12n, bs, Nat.add(4n, s), {==}, h1)
  +h3 = Jc.le_sub(4n, Nat.add(12n, s), bs, h2)
  +hlb = Jc.le_eql(B.Octets.len(bd), Nat.add(12n, s), Nat.sub(bs, tg), lb, Jc.le_eq(Nat.add(12n, s), Nat.sub(bs, tg), Nat.sub(bs, 4n), Equal.cong(Nat, Nat, k => Nat.sub(bs, k), tg, 4n, t4), h3))
  +x = Nat.sub(Nat.sub(bs, tg), B.Octets.len(bd))
  Equal.trans(Nat, B.Octets.len(B.Octets.append(bd, B.Octets.zeros(x))), Nat.add(B.Octets.len(bd), x), Nat.sub(bs, 4n),
    Jc.len2(bd, B.Octets.zeros(x), B.Octets.len(bd), x, {==}, BL.octets_len_zeros(x)),
    Equal.trans(Nat, Nat.add(B.Octets.len(bd), x), Nat.sub(bs, tg), Nat.sub(bs, 4n), Jc.add_sub(B.Octets.len(bd), Nat.sub(bs, tg), hlb), Equal.cong(Nat, Nat, k => Nat.sub(bs, k), tg, 4n, t4)))

def Jc.desc_t(+check: Bool, +g: J.Jbd2Geom, +seq: U32, +ts: List<&2, JB.Jbd2Tag>, +uuid: B.Octets, +hu: {Nat.is_eq(B.Octets.len(uuid), 16n) == True{} : Bool}, +hf: {JB.Jbd2Desc.fits.go(g, ts, Jc.darea(g)) == True{} : Bool}, +hb: {J.Jbd2Geom.has_csum(g) == True{} : Bool}) -> {JB.Jbd2Desc.decode(check, g, JB.Jbd2Block.seal(True{}, g, B.Octets.append(Jc.dbody(g, seq, ts, uuid), Jc.dpad(g, seq, ts, uuid)))) == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}:
  +bd = Jc.dbody(g, seq, ts, uuid)
  +z = Jc.dpad(g, seq, ts, uuid)
  +p = B.Octets.append(bd, z)
  +q = B.Octets.be32(JB.Jbd2Block.tail_csum(g, B.Octets.append(p, B.Octets.zeros(4n))))
  +blk = B.Octets.append(p, q)
  +n = Jc.darea(g)
  +fu = Nat.add(Nat.div(n, 8n), 1n)
  +er = Jc.ER(g, ts, uuid, B.Octets.append(z, q))
  %Equal.sym(B.Octets, JB.Jbd2Block.seal(True{}, g, p), blk, Jc.bseal_t(g, p)) : {JB.Jbd2Desc.decode(check, g, _) == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}
  %Equal.sym(Maybe<&2, List<&2, JB.Jbd2Tag>>, JB.Jbd2Desc.decode(check, g, blk), JB.Jbd2Desc.decode.go(JB.Jbd2Block.tail_ok(check, g, blk), g, blk), Jc.dec_go(check, g, blk)) : {_ == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}
  %Equal.sym(Bool, JB.Jbd2Block.tail_ok(check, g, blk), True{}, Jc.tok_t(check, g, p, hb, Jc.dlen(g, seq, ts, uuid, hu, hf, hb))) : {JB.Jbd2Desc.decode.go(_, g, blk) == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}
  %Equal.sym(Maybe<&2, List<&2, JB.Jbd2Tag>>, JB.Jbd2Desc.decode.go(True{}, g, blk), Some{JB.Jbd2Desc.tags(g, blk)}, Jc.dgo_t(g, blk)) : {_ == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}
  %Equal.sym(List<&2, JB.Jbd2Tag>, JB.Jbd2Desc.tags(g, blk), JB.Jbd2Desc.walk(fu, JB.Jbd2Tag.step(g, B.Octets.drop(12n, blk), n), B.Octets.drop(12n, blk), n, g, Nil{}), Jc.tags_go(g, blk)) : {Some{_} == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}
  %Jc.app3(bd, z, q) : {Some{JB.Jbd2Desc.walk(fu, JB.Jbd2Tag.step(g, B.Octets.drop(12n, _), n), B.Octets.drop(12n, _), n, g, Nil{})} == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}
  %Equal.sym(B.Octets, B.Octets.drop(12n, B.Octets.append(bd, B.Octets.append(z, q))), er, Jc.area(g, seq, ts, uuid, B.Octets.append(z, q))) : {Some{JB.Jbd2Desc.walk(fu, JB.Jbd2Tag.step(g, _, n), _, n, g, Nil{})} == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}
  Equal.cong(List<&2, JB.Jbd2Tag>, Maybe<&2, List<&2, JB.Jbd2Tag>>, l => Some{l}, JB.Jbd2Desc.walk(fu, JB.Jbd2Tag.step(g, er, n), er, n, g, Nil{}), ts, Jc.walk_rt(ts, fu, g, uuid, B.Octets.append(z, q), n, Nil{}, hu, hf, Jc.dfuel(g, ts, hf)))

def Jc.desc_b(b: Bool, +check: Bool, +g: J.Jbd2Geom, +seq: U32, +ts: List<&2, JB.Jbd2Tag>, +uuid: B.Octets, +hu: {Nat.is_eq(B.Octets.len(uuid), 16n) == True{} : Bool}, +hf: {JB.Jbd2Desc.fits.go(g, ts, Jc.darea(g)) == True{} : Bool}) -> {J.Jbd2Geom.has_csum(g) == b : Bool} -> {JB.Jbd2Desc.decode(check, g, JB.Jbd2Block.seal(b, g, B.Octets.append(Jc.dbody(g, seq, ts, uuid), Jc.dpad(g, seq, ts, uuid)))) == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}:
  match b:
    case True{}:
      hb => Jc.desc_t(check, g, seq, ts, uuid, hu, hf, hb)
    case False{}:
      hb => Jc.desc_f(check, g, seq, ts, uuid, hu, hf, hb)

def Laws.jdesc_round_trip(check, g, seq, ts, uuid, u, f):
  %Equal.sym(B.Octets, JB.Jbd2Desc.encode(g, seq, ts, uuid), JB.Jbd2Block.seal(J.Jbd2Geom.has_csum(g), g, B.Octets.append(Jc.dbody(g, seq, ts, uuid), Jc.dpad(g, seq, ts, uuid))), Jc.dshape(g, seq, ts, uuid)) : {JB.Jbd2Desc.decode(check, g, _) == Some{ts} : Maybe<&2, List<&2, JB.Jbd2Tag>>}
  Jc.desc_b(J.Jbd2Geom.has_csum(g), check, g, seq, ts, uuid, u, f, {==})

# Revoke blocks: the records, joined, and read back

def Jc.go4(+k: Nat, +e: Nat, +q: Nat) -> {Pair.fst(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(k, 4n), e), 3n, q, 0n)) == Pair.fst(Nat, Nat, Nat.divmod.go(e, 3n, Nat.add(k, q), 0n)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(p, 4n), e), 3n, 1n+q, 0n)), Pair.fst(Nat, Nat, Nat.divmod.go(e, 3n, Nat.add(p, 1n+q), 0n)), Pair.fst(Nat, Nat, Nat.divmod.go(e, 3n, 1n+Nat.add(p, q), 0n)),
        Jc.go4(p, e, 1n+q),
        Equal.cong(Nat, Nat, x => Pair.fst(Nat, Nat, Nat.divmod.go(e, 3n, x, 0n)), Nat.add(p, 1n+q), 1n+Nat.add(p, q), Jc.add_succ(p, q)))

# k records of e bytes, divided by e, are k
def Jc.rdiv(w: Bool, +k: Nat) -> {Nat.div(Nat.mul(k, JB.Jbd2Revoke.entry_size(w)), JB.Jbd2Revoke.entry_size(w)) == k : Nat}:
  match w:
    case True{}:
      %Jc.add_zero(Nat.mul(k, 8n)) : {Pair.fst(Nat, Nat, Nat.divmod.go(_, 7n, 0n, 0n)) == k : Nat}
      %Equal.sym(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(k, 8n), 0n), 7n, 0n, 0n)), Pair.fst(Nat, Nat, Nat.divmod.go(0n, 7n, Nat.add(k, 0n), 0n)), Jc.go8(k, 0n, 0n)) : {_ == k : Nat}
      Jc.add_zero(k)
    case False{}:
      %Jc.add_zero(Nat.mul(k, 4n)) : {Pair.fst(Nat, Nat, Nat.divmod.go(_, 3n, 0n, 0n)) == k : Nat}
      %Equal.sym(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(Nat.add(Nat.mul(k, 4n), 0n), 3n, 0n, 0n)), Pair.fst(Nat, Nat, Nat.divmod.go(0n, 3n, Nat.add(k, 0n), 0n)), Jc.go4(k, 0n, 0n)) : {_ == k : Nat}
      Jc.add_zero(k)

def Jc.el(+w: Bool, bs: List<&2, Nat>) -> List<&2, B.Octets>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+b, t}:
      Con{JB.Jbd2Revoke.entry(w, b), Jc.el(w, t)}

def Jc.EV(+w: Bool, bs: List<&2, Nat>, +r: B.Octets) -> B.Octets:
  match bs:
    case Nil{}:
      r
    case Con{+b, t}:
      B.Octets.append(JB.Jbd2Revoke.entry(w, b), Jc.EV(w, t, r))

def Jc.ent_acc(bs: List<&2, Nat>, +w: Bool, +acc: List<&2, B.Octets>) -> {JB.Jbd2Revoke.entries(bs, w, acc) == List.reverse.go(&2, B.Octets, acc, Jc.el(w, bs)) : List<&2, B.Octets>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, t}:
      Jc.ent_acc(t, w, Con{JB.Jbd2Revoke.entry(w, b), acc})

def Jc.concat_el(+w: Bool, bs: List<&2, Nat>, +r: B.Octets) -> {B.Octets.append(B.Octets.concat(Jc.el(w, bs)), r) == Jc.EV(w, bs, r) : B.Octets}:
  match bs:
    case Nil{}:
      %BL.octets_concat_nil() : {B.Octets.append(_, r) == r : B.Octets}
      BL.octets_append_empty_l(r)
    case Con{+b, +t}:
      +e = JB.Jbd2Revoke.entry(w, b)
      +c = B.Octets.concat(Jc.el(w, t))
      %Equal.sym(B.Octets, B.Octets.concat(Con{e, Jc.el(w, t)}), B.Octets.append(e, c), BL.octets_concat_cons(e, Jc.el(w, t))) : {B.Octets.append(_, r) == Jc.EV(w, Con{b, t}, r) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.append(B.Octets.append(e, c), r), B.Octets.append(e, B.Octets.append(c, r)), BL.octets_append_assoc(e, c, r)) : {_ == Jc.EV(w, Con{b, t}, r) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.append(c, r), Jc.EV(w, t, r), Jc.concat_el(w, t, r)) : {B.Octets.append(e, _) == Jc.EV(w, Con{b, t}, r) : B.Octets}
      {==}

def Jc.len_entry(w: Bool, +b: Nat) -> {B.Octets.len(JB.Jbd2Revoke.entry(w, b)) == JB.Jbd2Revoke.entry_size(w) : Nat}:
  match w:
    case True{}:
      Jc.len2(B.Octets.be32(JB.Jbd2.hi(b)), B.Octets.be32(JB.Jbd2.lo(b)), 4n, 4n, BL.octets_len_be32(JB.Jbd2.hi(b)), BL.octets_len_be32(JB.Jbd2.lo(b)))
    case False{}:
      BL.octets_len_be32(JB.Jbd2.lo(b))

def Jc.len_el(+w: Bool, bs: List<&2, Nat>) -> {B.Octets.len(B.Octets.concat(Jc.el(w, bs))) == Nat.mul(List.length(&2, Nat, bs), JB.Jbd2Revoke.entry_size(w)) : Nat}:
  match bs:
    case Nil{}:
      %BL.octets_concat_nil() : {B.Octets.len(_) == 0n : Nat}
      {==}
    case Con{+b, +t}:
      +e = JB.Jbd2Revoke.entry(w, b)
      %Equal.sym(B.Octets, B.Octets.concat(Con{e, Jc.el(w, t)}), B.Octets.append(e, B.Octets.concat(Jc.el(w, t))), BL.octets_concat_cons(e, Jc.el(w, t))) : {B.Octets.len(_) == Nat.mul(List.length(&2, Nat, Con{b, t}), JB.Jbd2Revoke.entry_size(w)) : Nat}
      Jc.len2(e, B.Octets.concat(Jc.el(w, t)), JB.Jbd2Revoke.entry_size(w), Nat.mul(List.length(&2, Nat, t), JB.Jbd2Revoke.entry_size(w)), Jc.len_entry(w, b), Jc.len_el(w, t))

# a record, followed by anything, is read back as its block number
def Jc.rread_t(+b: Nat, +x: B.Octets, hb: {JB.Jbd2.block_fits(True{}, b) == True{} : Bool}) -> {JB.Jbd2Revoke.read(True{}, B.Octets.append(JB.Jbd2Revoke.entry(True{}, b), x)) == b : Nat}:
  +h4 = B.Octets.be32(JB.Jbd2.hi(b))
  +l4 = B.Octets.be32(JB.Jbd2.lo(b))
  +n = B.Octets.append(h4, B.Octets.append(l4, x))
  %Jc.app3(h4, l4, x) : {JB.Jbd2.join(True{}, Jc.d32(B.Octets.be32_at(_, 0n)), Jc.d32(B.Octets.be32_at(_, 4n))) == b : Nat}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(n, 0n), Some{JB.Jbd2.hi(b)}, Jc.be32_head(JB.Jbd2.hi(b), B.Octets.append(l4, x))) : {JB.Jbd2.join(True{}, Jc.d32(_), Jc.d32(B.Octets.be32_at(n, 4n))) == b : Nat}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(n, Nat.add(4n, 0n)), Some{JB.Jbd2.lo(b)}, Jc.rd32(h4, B.Octets.append(l4, x), 4n, 0n, Some{JB.Jbd2.lo(b)}, BL.octets_len_be32(JB.Jbd2.hi(b)), Jc.be32_head(JB.Jbd2.lo(b), x))) : {JB.Jbd2.join(True{}, JB.Jbd2.hi(b), Jc.d32(_)) == b : Nat}
  Ext4Proof.eq_sound(JB.Jbd2.join(True{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), b, hb)

def Jc.rread_f(+b: Nat, +x: B.Octets, hb: {JB.Jbd2.block_fits(False{}, b) == True{} : Bool}) -> {JB.Jbd2Revoke.read(False{}, B.Octets.append(JB.Jbd2Revoke.entry(False{}, b), x)) == b : Nat}:
  +l4 = B.Octets.be32(JB.Jbd2.lo(b))
  +n = B.Octets.append(l4, x)
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(n, 0n), Some{JB.Jbd2.lo(b)}, Jc.be32_head(JB.Jbd2.lo(b), x)) : {JB.Jbd2.join(False{}, Jc.d32(_), Jc.d32(_)) == b : Nat}
  Ext4Proof.eq_sound(JB.Jbd2.join(False{}, JB.Jbd2.hi(b), JB.Jbd2.lo(b)), b, hb)

def Jc.rread(w: Bool, +b: Nat, +x: B.Octets) -> {JB.Jbd2.block_fits(w, b) == True{} : Bool} -> {JB.Jbd2Revoke.read(w, B.Octets.append(JB.Jbd2Revoke.entry(w, b), x)) == b : Nat}:
  match w:
    case True{}:
      hb => Jc.rread_t(b, x, hb)
    case False{}:
      hb => Jc.rread_f(b, x, hb)

def Jc.rdrop(+w: Bool, +b: Nat, +x: B.Octets) -> {B.Octets.drop(JB.Jbd2Revoke.entry_size(w), B.Octets.append(JB.Jbd2Revoke.entry(w, b), x)) == x : B.Octets}:
  %Jc.len_entry(w, b) : {B.Octets.drop(_, B.Octets.append(JB.Jbd2Revoke.entry(w, b), x)) == x : B.Octets}
  BL.octets_drop_append(JB.Jbd2Revoke.entry(w, b), x)

def Jc.rwalk(bs: List<&2, Nat>, +w: Bool, +r: B.Octets, +acc: List<&2, Nat>) -> {JB.Jbd2Revoke.blocks_fit(w, bs) == True{} : Bool} -> {JB.Jbd2Revoke.walk(List.length(&2, Nat, bs), Jc.EV(w, bs, r), w, acc) == List.reverse.go(&2, Nat, acc, bs) : List<&2, Nat>}:
  match bs:
    case Nil{}:
      +hf => {==}
    case Con{+b, +t}:
      +hf =>
        +o = Jc.EV(w, Con{b, t}, r)
        +x = Jc.EV(w, t, r)
        +h1 = Ext4Proof.and_l(JB.Jbd2.block_fits(w, b), JB.Jbd2Revoke.blocks_fit(w, t), hf)
        +h2 = Ext4Proof.and_r(JB.Jbd2.block_fits(w, b), JB.Jbd2Revoke.blocks_fit(w, t), hf)
        %Equal.sym(Nat, JB.Jbd2Revoke.read(w, o), b, Jc.rread(w, b, x, h1)) : {JB.Jbd2Revoke.walk(List.length(&2, Nat, t), B.Octets.drop(JB.Jbd2Revoke.entry_size(w), o), w, Con{_, acc}) == List.reverse.go(&2, Nat, acc, Con{b, t}) : List<&2, Nat>}
        %Equal.sym(B.Octets, B.Octets.drop(JB.Jbd2Revoke.entry_size(w), o), x, Jc.rdrop(w, b, x)) : {JB.Jbd2Revoke.walk(List.length(&2, Nat, t), _, w, Con{b, acc}) == List.reverse.go(&2, Nat, acc, Con{b, t}) : List<&2, Nat>}
        Jc.rwalk(t, w, r, Con{b, acc}, h2)

# The revoke block: its shape, r_count, the records after the header

def Jc.rbody(+g: J.Jbd2Geom, +seq: U32, +bs: List<&2, Nat>) -> B.Octets:
  B.Octets.append(JB.Jbd2.header(JB.Jbd2.kind_revoke(), seq), B.Octets.append(B.Octets.be32(U32.from_nat(JB.Jbd2Revoke.count(g, bs))), B.Octets.concat(JB.Jbd2Revoke.entries(bs, J.Jbd2Geom.wide(g), Nil{}))))

def Jc.rpad(+g: J.Jbd2Geom, +seq: U32, +bs: List<&2, Nat>) -> B.Octets:
  B.Octets.zeros(Nat.sub(Nat.sub(J.Jbd2Geom.bs(g), J.Jbd2Geom.tail(g)), B.Octets.len(Jc.rbody(g, seq, bs))))

def Jc.rshape(+g: J.Jbd2Geom, +seq: U32, +bs: List<&2, Nat>) -> {JB.Jbd2Revoke.encode(g, seq, bs) == JB.Jbd2Block.seal(J.Jbd2Geom.has_csum(g), g, B.Octets.append(Jc.rbody(g, seq, bs), Jc.rpad(g, seq, bs))) : B.Octets}:
  {==}

def Jc.rdec(+check: Bool, +g: J.Jbd2Geom, +x: B.Octets) -> {JB.Jbd2Revoke.decode(check, g, x) == JB.Jbd2Revoke.decode.go(Bool.and(JB.Jbd2Block.tail_ok(check, g, x), Bool.and(Nat.is_le(16n, U32.to_nat(Jc.d32(B.Octets.be32_at(x, 12n)))), Nat.is_le(U32.to_nat(Jc.d32(B.Octets.be32_at(x, 12n))), Nat.sub(J.Jbd2Geom.bs(g), J.Jbd2Geom.tail(g))))), g, x, U32.to_nat(Jc.d32(B.Octets.be32_at(x, 12n)))) : Maybe<&2, List<&2, Nat>>}:
  {==}

def Jc.rgo_t(+g: J.Jbd2Geom, +x: B.Octets, +count: Nat) -> {JB.Jbd2Revoke.decode.go(True{}, g, x, count) == Some{JB.Jbd2Revoke.walk(Nat.div(Nat.sub(count, 16n), JB.Jbd2Revoke.entry_size(J.Jbd2Geom.wide(g))), B.Octets.drop(16n, x), J.Jbd2Geom.wide(g), Nil{})} : Maybe<&2, List<&2, Nat>>}:
  {==}

def Jc.rv12(+g: J.Jbd2Geom, +seq: U32, +bs: List<&2, Nat>, +r: B.Octets) -> {B.Octets.be32_at(B.Octets.append(Jc.rbody(g, seq, bs), r), 12n) == Some{U32.from_nat(JB.Jbd2Revoke.count(g, bs))} : Maybe<&2, U32>}:
  +h = JB.Jbd2.header(JB.Jbd2.kind_revoke(), seq)
  +q = B.Octets.be32(U32.from_nat(JB.Jbd2Revoke.count(g, bs)))
  +c = B.Octets.concat(JB.Jbd2Revoke.entries(bs, J.Jbd2Geom.wide(g), Nil{}))
  %Jc.app3(h, B.Octets.append(q, c), r) : {B.Octets.be32_at(_, 12n) == Some{U32.from_nat(JB.Jbd2Revoke.count(g, bs))} : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(h, B.Octets.append(B.Octets.append(q, c), r)), Nat.add(12n, 0n)), B.Octets.be32_at(B.Octets.append(B.Octets.append(q, c), r), 0n), Jc.skip32(h, B.Octets.append(B.Octets.append(q, c), r), 12n, 0n, Jc.hdr_len(JB.Jbd2.kind_revoke(), seq))) : {_ == Some{U32.from_nat(JB.Jbd2Revoke.count(g, bs))} : Maybe<&2, U32>}
  %Jc.app3(q, c, r) : {B.Octets.be32_at(_, 0n) == Some{U32.from_nat(JB.Jbd2Revoke.count(g, bs))} : Maybe<&2, U32>}
  Jc.be32_head(U32.from_nat(JB.Jbd2Revoke.count(g, bs)), B.Octets.append(c, r))

def Jc.rv16(+g: J.Jbd2Geom, +seq: U32, +bs: List<&2, Nat>, +r: B.Octets) -> {B.Octets.drop(16n, B.Octets.append(Jc.rbody(g, seq, bs), r)) == Jc.EV(J.Jbd2Geom.wide(g), bs, r) : B.Octets}:
  +w = J.Jbd2Geom.wide(g)
  +h = JB.Jbd2.header(JB.Jbd2.kind_revoke(), seq)
  +q = B.Octets.be32(U32.from_nat(JB.Jbd2Revoke.count(g, bs)))
  +c = B.Octets.concat(JB.Jbd2Revoke.entries(bs, w, Nil{}))
  %Jc.app3(h, B.Octets.append(q, c), r) : {B.Octets.drop(16n, _) == Jc.EV(w, bs, r) : B.Octets}
  %Equal.cong(Nat, Nat, k => Nat.add(k, 4n), B.Octets.len(h), 12n, Jc.hdr_len(JB.Jbd2.kind_revoke(), seq)) : {B.Octets.drop(_, B.Octets.append(h, B.Octets.append(B.Octets.append(q, c), r))) == Jc.EV(w, bs, r) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(Nat.add(B.Octets.len(h), 4n), B.Octets.append(h, B.Octets.append(B.Octets.append(q, c), r))), B.Octets.drop(4n, B.Octets.append(B.Octets.append(q, c), r)), BL.octets_drop_append_add(h, 4n, B.Octets.append(B.Octets.append(q, c), r))) : {_ == Jc.EV(w, bs, r) : B.Octets}
  %Jc.app3(q, c, r) : {B.Octets.drop(4n, _) == Jc.EV(w, bs, r) : B.Octets}
  %BL.octets_len_be32(U32.from_nat(JB.Jbd2Revoke.count(g, bs))) : {B.Octets.drop(_, B.Octets.append(q, B.Octets.append(c, r))) == Jc.EV(w, bs, r) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(q), B.Octets.append(q, B.Octets.append(c, r))), B.Octets.append(c, r), BL.octets_drop_append(q, B.Octets.append(c, r))) : {_ == Jc.EV(w, bs, r) : B.Octets}
  %Equal.sym(List<&2, B.Octets>, JB.Jbd2Revoke.entries(bs, w, Nil{}), List.reverse.go(&2, B.Octets, Nil{}, Jc.el(w, bs)), Jc.ent_acc(bs, w, Nil{})) : {B.Octets.append(B.Octets.concat(_), r) == Jc.EV(w, bs, r) : B.Octets}
  Jc.concat_el(w, bs, r)

def Jc.rlen(+g: J.Jbd2Geom, +seq: U32, +bs: List<&2, Nat>) -> {B.Octets.len(Jc.rbody(g, seq, bs)) == JB.Jbd2Revoke.count(g, bs) : Nat}:
  +w = J.Jbd2Geom.wide(g)
  +m = Nat.mul(List.length(&2, Nat, bs), JB.Jbd2Revoke.entry_size(w))
  +c = B.Octets.concat(JB.Jbd2Revoke.entries(bs, w, Nil{}))
  +lc = Equal.trans(Nat, B.Octets.len(c), B.Octets.len(B.Octets.concat(Jc.el(w, bs))), m, Equal.cong(List<&2, B.Octets>, Nat, l => B.Octets.len(B.Octets.concat(l)), JB.Jbd2Revoke.entries(bs, w, Nil{}), List.reverse.go(&2, B.Octets, Nil{}, Jc.el(w, bs)), Jc.ent_acc(bs, w, Nil{})), Jc.len_el(w, bs))
  Jc.len2(JB.Jbd2.header(JB.Jbd2.kind_revoke(), seq), B.Octets.append(B.Octets.be32(U32.from_nat(JB.Jbd2Revoke.count(g, bs))), c), 12n, Nat.add(4n, m), Jc.hdr_len(JB.Jbd2.kind_revoke(), seq),
    Jc.len2(B.Octets.be32(U32.from_nat(JB.Jbd2Revoke.count(g, bs))), c, 4n, m, BL.octets_len_be32(U32.from_nat(JB.Jbd2Revoke.count(g, bs))), lc))

# the condition decode.go checks holds; then the records read back
def Jc.rcond(+g: J.Jbd2Geom, +bs: List<&2, Nat>, +hc: {Nat.is_le(JB.Jbd2Revoke.count(g, bs), Nat.sub(J.Jbd2Geom.bs(g), J.Jbd2Geom.tail(g))) == True{} : Bool}) -> {Bool.and(True{}, Bool.and(Nat.is_le(16n, JB.Jbd2Revoke.count(g, bs)), Nat.is_le(JB.Jbd2Revoke.count(g, bs), Nat.sub(J.Jbd2Geom.bs(g), J.Jbd2Geom.tail(g))))) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(16n, JB.Jbd2Revoke.count(g, bs)), True{}, Jc.le_add_r(16n, Nat.mul(List.length(&2, Nat, bs), JB.Jbd2Revoke.entry_size(J.Jbd2Geom.wide(g))))) : {Bool.and(True{}, Bool.and(_, Nat.is_le(JB.Jbd2Revoke.count(g, bs), Nat.sub(J.Jbd2Geom.bs(g), J.Jbd2Geom.tail(g))))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_le(JB.Jbd2Revoke.count(g, bs), Nat.sub(J.Jbd2Geom.bs(g), J.Jbd2Geom.tail(g))), True{}, hc) : {Bool.and(True{}, Bool.and(True{}, _)) == True{} : Bool}
  {==}

def Jc.sub_zero(+x: Nat) -> {Nat.sub(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Jc.sub_add(+a: Nat, +x: Nat) -> {Nat.sub(Nat.add(a, x), a) == x : Nat}:
  match a:
    case 0n:
      Jc.sub_zero(x)
    case 1n+p:
      Jc.sub_add(p, x)

# with r_count read as written: the walk over the records gives them back
def Jc.rfin(+g: J.Jbd2Geom, +seq: U32, +bs: List<&2, Nat>, +r: B.Octets, +hb: {JB.Jbd2Revoke.blocks_fit(J.Jbd2Geom.wide(g), bs) == True{} : Bool}) -> {JB.Jbd2Revoke.decode.go(True{}, g, B.Octets.append(Jc.rbody(g, seq, bs), r), JB.Jbd2Revoke.count(g, bs)) == Some{bs} : Maybe<&2, List<&2, Nat>>}:
  +w = J.Jbd2Geom.wide(g)
  +x = B.Octets.append(Jc.rbody(g, seq, bs), r)
  +n = List.length(&2, Nat, bs)
  %Equal.sym(Maybe<&2, List<&2, Nat>>, JB.Jbd2Revoke.decode.go(True{}, g, x, JB.Jbd2Revoke.count(g, bs)), Some{JB.Jbd2Revoke.walk(Nat.div(Nat.sub(JB.Jbd2Revoke.count(g, bs), 16n), JB.Jbd2Revoke.entry_size(w)), B.Octets.drop(16n, x), w, Nil{})}, Jc.rgo_t(g, x, JB.Jbd2Revoke.count(g, bs))) : {_ == Some{bs} : Maybe<&2, List<&2, Nat>>}
  %Equal.sym(Nat, Nat.sub(Nat.add(16n, Nat.mul(n, JB.Jbd2Revoke.entry_size(w))), 16n), Nat.mul(n, JB.Jbd2Revoke.entry_size(w)), Jc.sub_add(16n, Nat.mul(n, JB.Jbd2Revoke.entry_size(w)))) : {Some{JB.Jbd2Revoke.walk(Nat.div(_, JB.Jbd2Revoke.entry_size(w)), B.Octets.drop(16n, x), w, Nil{})} == Some{bs} : Maybe<&2, List<&2, Nat>>}
  %Equal.sym(Nat, Nat.div(Nat.mul(n, JB.Jbd2Revoke.entry_size(w)), JB.Jbd2Revoke.entry_size(w)), n, Jc.rdiv(w, n)) : {Some{JB.Jbd2Revoke.walk(_, B.Octets.drop(16n, x), w, Nil{})} == Some{bs} : Maybe<&2, List<&2, Nat>>}
  %Equal.sym(B.Octets, B.Octets.drop(16n, x), Jc.EV(w, bs, r), Jc.rv16(g, seq, bs, r)) : {Some{JB.Jbd2Revoke.walk(n, _, w, Nil{})} == Some{bs} : Maybe<&2, List<&2, Nat>>}
  Equal.cong(List<&2, Nat>, Maybe<&2, List<&2, Nat>>, l => Some{l}, JB.Jbd2Revoke.walk(n, Jc.EV(w, bs, r), w, Nil{}), bs, Jc.rwalk(bs, w, r, Nil{}, hb))

# r_count read from the block: the count, given it fits in 32 bits
def Jc.rcount(+g: J.Jbd2Geom, +seq: U32, +bs: List<&2, Nat>, +r: B.Octets, hn: {Nat.is_eq(U32.to_nat(U32.from_nat(JB.Jbd2Revoke.count(g, bs))), JB.Jbd2Revoke.count(g, bs)) == True{} : Bool}) -> {U32.to_nat(Jc.d32(B.Octets.be32_at(B.Octets.append(Jc.rbody(g, seq, bs), r), 12n))) == JB.Jbd2Revoke.count(g, bs) : Nat}:
  %Equal.sym(Maybe<&2, U32>, B.Octets.be32_at(B.Octets.append(Jc.rbody(g, seq, bs), r), 12n), Some{U32.from_nat(JB.Jbd2Revoke.count(g, bs))}, Jc.rv12(g, seq, bs, r)) : {U32.to_nat(Jc.d32(_)) == JB.Jbd2Revoke.count(g, bs) : Nat}
  Ext4Proof.eq_sound(U32.to_nat(U32.from_nat(JB.Jbd2Revoke.count(g, bs))), JB.Jbd2Revoke.count(g, bs), hn)

def Jc.rev_f(+check: Bool, +g: J.Jbd2Geom, +seq: U32, +bs: List<&2, Nat>, +hb: {JB.Jbd2Revoke.blocks_fit(J.Jbd2Geom.wide(g), bs) == True{} : Bool}, +hn: {Nat.is_eq(U32.to_nat(U32.from_nat(JB.Jbd2Revoke.count(g, bs))), JB.Jbd2Revoke.count(g, bs)) == True{} : Bool}, +hc: {Nat.is_le(JB.Jbd2Revoke.count(g, bs), Nat.sub(J.Jbd2Geom.bs(g), J.Jbd2Geom.tail(g))) == True{} : Bool}, hs: {J.Jbd2Geom.has_csum(g) == False{} : Bool}) -> {JB.Jbd2Revoke.decode(check, g, JB.Jbd2Block.seal(False{}, g, B.Octets.append(Jc.rbody(g, seq, bs), Jc.rpad(g, seq, bs)))) == Some{bs} : Maybe<&2, List<&2, Nat>>}:
  +z = Jc.rpad(g, seq, bs)
  +x = B.Octets.append(Jc.rbody(g, seq, bs), z)
  +ct = JB.Jbd2Revoke.count(g, bs)
  +lim = Nat.sub(J.Jbd2Geom.bs(g), J.Jbd2Geom.tail(g))
  %Equal.sym(B.Octets, JB.Jbd2Block.seal(False{}, g, x), x, Jc.bseal_f(g, x)) : {JB.Jbd2Revoke.decode(check, g, _) == Some{bs} : Maybe<&2, List<&2, Nat>>}
  %Equal.sym(Maybe<&2, List<&2, Nat>>, JB.Jbd2Revoke.decode(check, g, x), JB.Jbd2Revoke.decode.go(Bool.and(JB.Jbd2Block.tail_ok(check, g, x), Bool.and(Nat.is_le(16n, U32.to_nat(Jc.d32(B.Octets.be32_at(x, 12n)))), Nat.is_le(U32.to_nat(Jc.d32(B.Octets.be32_at(x, 12n))), lim))), g, x, U32.to_nat(Jc.d32(B.Octets.be32_at(x, 12n)))), Jc.rdec(check, g, x)) : {_ == Some{bs} : Maybe<&2, List<&2, Nat>>}
  %Equal.sym(Bool, JB.Jbd2Block.tail_ok(check, g, x), True{}, Jc.tok_f(check, g, x, hs)) : {JB.Jbd2Revoke.decode.go(Bool.and(_, Bool.and(Nat.is_le(16n, U32.to_nat(Jc.d32(B.Octets.be32_at(x, 12n)))), Nat.is_le(U32.to_nat(Jc.d32(B.Octets.be32_at(x, 12n))), lim))), g, x, U32.to_nat(Jc.d32(B.Octets.be32_at(x, 12n)))) == Some{bs} : Maybe<&2, List<&2, Nat>>}
  %Equal.sym(Nat, U32.to_nat(Jc.d32(B.Octets.be32_at(x, 12n))), ct, Jc.rcount(g, seq, bs, z, hn)) : {JB.Jbd2Revoke.decode.go(Bool.and(True{}, Bool.and(Nat.is_le(16n, _), Nat.is_le(_, lim))), g, x, _) == Some{bs} : Maybe<&2, List<&2, Nat>>}
  %Equal.sym(Bool, Bool.and(True{}, Bool.and(Nat.is_le(16n, ct), Nat.is_le(ct, lim))), True{}, Jc.rcond(g, bs, hc)) : {JB.Jbd2Revoke.decode.go(_, g, x, ct) == Some{bs} : Maybe<&2, List<&2, Nat>>}
  Jc.rfin(g, seq, bs, z, hb)

def Jc.rev_t(+check: Bool, +g: J.Jbd2Geom, +seq: U32, +bs: List<&2, Nat>, +hb: {JB.Jbd2Revoke.blocks_fit(J.Jbd2Geom.wide(g), bs) == True{} : Bool}, +hn: {Nat.is_eq(U32.to_nat(U32.from_nat(JB.Jbd2Revoke.count(g, bs))), JB.Jbd2Revoke.count(g, bs)) == True{} : Bool}, +hc: {Nat.is_le(JB.Jbd2Revoke.count(g, bs), Nat.sub(J.Jbd2Geom.bs(g), J.Jbd2Geom.tail(g))) == True{} : Bool}, +hs: {J.Jbd2Geom.has_csum(g) == True{} : Bool}) -> {JB.Jbd2Revoke.decode(check, g, JB.Jbd2Block.seal(True{}, g, B.Octets.append(Jc.rbody(g, seq, bs), Jc.rpad(g, seq, bs)))) == Some{bs} : Maybe<&2, List<&2, Nat>>}:
  +bd = Jc.rbody(g, seq, bs)
  +z = Jc.rpad(g, seq, bs)
  +p = B.Octets.append(bd, z)
  +q = B.Octets.be32(JB.Jbd2Block.tail_csum(g, B.Octets.append(p, B.Octets.zeros(4n))))
  +x = B.Octets.append(p, q)
  +y = B.Octets.append(bd, B.Octets.append(z, q))
  +ct = JB.Jbd2Revoke.count(g, bs)
  +bsz = J.Jbd2Geom.bs(g)
  +tg = J.Jbd2Geom.tail(g)
  +lim = Nat.sub(bsz, tg)
  +t4 = Jc.tail4(g, hs)
  +lb = Jc.rlen(g, seq, bs)
  +xz = Nat.sub(lim, B.Octets.len(bd))
  +lp = Equal.trans(Nat, B.Octets.len(p), Nat.add(B.Octets.len(bd), xz), Nat.sub(bsz, 4n),
    Jc.len2(bd, B.Octets.zeros(xz), B.Octets.len(bd), xz, {==}, BL.octets_len_zeros(xz)),
    Equal.trans(Nat, Nat.add(B.Octets.len(bd), xz), lim, Nat.sub(bsz, 4n), Jc.add_sub(B.Octets.len(bd), lim, Jc.le_eql(B.Octets.len(bd), ct, lim, lb, hc)), Equal.cong(Nat, Nat, k => Nat.sub(bsz, k), tg, 4n, t4)))
  %Equal.sym(B.Octets, JB.Jbd2Block.seal(True{}, g, p), x, Jc.bseal_t(g, p)) : {JB.Jbd2Revoke.decode(check, g, _) == Some{bs} : Maybe<&2, List<&2, Nat>>}
  %Equal.sym(Maybe<&2, List<&2, Nat>>, JB.Jbd2Revoke.decode(check, g, x), JB.Jbd2Revoke.decode.go(Bool.and(JB.Jbd2Block.tail_ok(check, g, x), Bool.and(Nat.is_le(16n, U32.to_nat(Jc.d32(B.Octets.be32_at(x, 12n)))), Nat.is_le(U32.to_nat(Jc.d32(B.Octets.be32_at(x, 12n))), lim))), g, x, U32.to_nat(Jc.d32(B.Octets.be32_at(x, 12n)))), Jc.rdec(check, g, x)) : {_ == Some{bs} : Maybe<&2, List<&2, Nat>>}
  %Equal.sym(Bool, JB.Jbd2Block.tail_ok(check, g, x), True{}, Jc.tok_t(check, g, p, hs, lp)) : {JB.Jbd2Revoke.decode.go(Bool.and(_, Bool.and(Nat.is_le(16n, U32.to_nat(Jc.d32(B.Octets.be32_at(x, 12n)))), Nat.is_le(U32.to_nat(Jc.d32(B.Octets.be32_at(x, 12n))), lim))), g, x, U32.to_nat(Jc.d32(B.Octets.be32_at(x, 12n)))) == Some{bs} : Maybe<&2, List<&2, Nat>>}
  %Jc.app3(bd, z, q) : {JB.Jbd2Revoke.decode.go(Bool.and(True{}, Bool.and(Nat.is_le(16n, U32.to_nat(Jc.d32(B.Octets.be32_at(_, 12n)))), Nat.is_le(U32.to_nat(Jc.d32(B.Octets.be32_at(_, 12n))), lim))), g, _, U32.to_nat(Jc.d32(B.Octets.be32_at(_, 12n)))) == Some{bs} : Maybe<&2, List<&2, Nat>>}
  %Equal.sym(Nat, U32.to_nat(Jc.d32(B.Octets.be32_at(y, 12n))), ct, Jc.rcount(g, seq, bs, B.Octets.append(z, q), hn)) : {JB.Jbd2Revoke.decode.go(Bool.and(True{}, Bool.and(Nat.is_le(16n, _), Nat.is_le(_, lim))), g, y, _) == Some{bs} : Maybe<&2, List<&2, Nat>>}
  %Equal.sym(Bool, Bool.and(True{}, Bool.and(Nat.is_le(16n, ct), Nat.is_le(ct, lim))), True{}, Jc.rcond(g, bs, hc)) : {JB.Jbd2Revoke.decode.go(_, g, y, ct) == Some{bs} : Maybe<&2, List<&2, Nat>>}
  Jc.rfin(g, seq, bs, B.Octets.append(z, q), hb)

def Jc.rev_b(b: Bool, +check: Bool, +g: J.Jbd2Geom, +seq: U32, +bs: List<&2, Nat>, +hb: {JB.Jbd2Revoke.blocks_fit(J.Jbd2Geom.wide(g), bs) == True{} : Bool}, +hn: {Nat.is_eq(U32.to_nat(U32.from_nat(JB.Jbd2Revoke.count(g, bs))), JB.Jbd2Revoke.count(g, bs)) == True{} : Bool}, +hc: {Nat.is_le(JB.Jbd2Revoke.count(g, bs), Nat.sub(J.Jbd2Geom.bs(g), J.Jbd2Geom.tail(g))) == True{} : Bool}) -> {J.Jbd2Geom.has_csum(g) == b : Bool} -> {JB.Jbd2Revoke.decode(check, g, JB.Jbd2Block.seal(b, g, B.Octets.append(Jc.rbody(g, seq, bs), Jc.rpad(g, seq, bs)))) == Some{bs} : Maybe<&2, List<&2, Nat>>}:
  match b:
    case True{}:
      hs => Jc.rev_t(check, g, seq, bs, hb, hn, hc, hs)
    case False{}:
      hs => Jc.rev_f(check, g, seq, bs, hb, hn, hc, hs)

def Laws.jrevoke_round_trip(check, g, seq, bs, f):
  +ct = JB.Jbd2Revoke.count(g, bs)
  +a1 = JB.Jbd2Revoke.blocks_fit(J.Jbd2Geom.wide(g), bs)
  +a2 = Nat.is_eq(U32.to_nat(U32.from_nat(ct)), ct)
  +a3 = Nat.is_le(ct, Nat.sub(J.Jbd2Geom.bs(g), J.Jbd2Geom.tail(g)))
  +h23 = Ext4Proof.and_r(a1, Bool.and(a2, a3), f)
  %Equal.sym(B.Octets, JB.Jbd2Revoke.encode(g, seq, bs), JB.Jbd2Block.seal(J.Jbd2Geom.has_csum(g), g, B.Octets.append(Jc.rbody(g, seq, bs), Jc.rpad(g, seq, bs))), Jc.rshape(g, seq, bs)) : {JB.Jbd2Revoke.decode(check, g, _) == Some{bs} : Maybe<&2, List<&2, Nat>>}
  Jc.rev_b(J.Jbd2Geom.has_csum(g), check, g, seq, bs, Ext4Proof.and_l(a1, Bool.and(a2, a3), f), Ext4Proof.and_l(a2, a3, h23), Ext4Proof.and_r(a2, a3, h23), {==})

# The plan's log, scanned: arithmetic

def Jc.add_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Nat.add(b, Nat.add(a, c)),
    Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Jc.add_assoc(a, b, c)),
    Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(b, a), c), Nat.add(b, Nat.add(a, c)),
      Equal.cong(Nat, Nat, k => Nat.add(k, c), Nat.add(a, b), Nat.add(b, a), Jc.add_comm(a, b)),
      Jc.add_assoc(b, a, c)))

# a < b: 1 + a <= b
def Jc.lt_succ_le(+a: Nat, +b: Nat) -> {Nat.is_lt(a, b) == True{} : Bool} -> {Nat.is_le(1n+a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      h => Ext4Proof.no({Nat.is_le(1n, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      h => Ext4Proof.no({Nat.is_le(2n+p, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      h => Ext4Proof.le_zero(q)
    case 1n+p 1n+q:
      h => Jc.lt_succ_le(p, q, h)

# 1 + a <= b: a < b
def Jc.le_succ_lt(+a: Nat, +b: Nat) -> {Nat.is_le(1n+a, b) == True{} : Bool} -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case _ 0n:
      h => Ext4Proof.no({Nat.is_lt(a, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      h => {==}
    case 1n+p 1n+q:
      h => Jc.le_succ_lt(p, q, h)

# a < b: not (b <= a)
def Jc.lt_not_le(+a: Nat, +b: Nat) -> {Nat.is_lt(a, b) == True{} : Bool} -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case _ 0n:
      h => Ext4Proof.no({Nat.is_le(0n, a) == False{} : Bool}, Ext4Proof.lt_zero(a, h))
    case 0n 1n+q:
      h => {==}
    case 1n+p 1n+q:
      h => Jc.lt_not_le(p, q, h)

def Jc.le_mul(+j: Nat, +k: Nat, +d: Nat) -> {Nat.is_le(j, k) == True{} : Bool} -> {Nat.is_le(Nat.mul(j, d), Nat.mul(k, d)) == True{} : Bool}:
  match j k:
    case 0n _:
      h => Ext4Proof.le_zero(Nat.mul(k, d))
    case 1n+p 0n:
      h => Ext4Proof.no({Nat.is_le(Nat.mul(1n+p, d), 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      h => Jc.le_mono_l(d, Nat.mul(p, d), Nat.mul(q, d), Jc.le_mul(p, q, d, h))

# 0 < n - k: k <= n
def Jc.sub_pos(+n: Nat, +k: Nat) -> {Nat.is_lt(0n, Nat.sub(n, k)) == True{} : Bool} -> {Nat.is_le(k, n) == True{} : Bool}:
  match n k:
    case _ 0n:
      h => Ext4Proof.le_zero(n)
    case 0n 1n+p:
      h => Ext4Proof.no({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n+q 1n+p:
      h => Jc.sub_pos(q, p, h)

def Jc.dm_z(+np: Nat, +q: Nat, +r: Nat, +bp: Nat, e: {Nat.add(0n, r) == bp : Nat}, ih: {Nat.is_le(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+q, 0n)), 1n+bp), Nat.add(np, Nat.add(Nat.mul(1n+q, 1n+bp), 0n))) == True{} : Bool}) -> {Nat.is_le(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+q, 0n)), 1n+bp), Nat.add(1n+np, Nat.add(Nat.mul(q, 1n+bp), r))) == True{} : Bool}:
  +d = {1n+bp : Nat}
  +mq = Nat.mul(q, d)
  +b1 = Nat.add(np, Nat.add(Nat.mul(1n+q, d), 0n))
  +b2 = Nat.add(1n+np, Nat.add(mq, r))
  +e1 = Equal.cong(Nat, Nat, k => Nat.add(np, k), Nat.add(Nat.mul(1n+q, d), 0n), Nat.mul(1n+q, d), Jc.add_zero(Nat.mul(1n+q, d)))
  +e2 = Jc.add_succ(np, Nat.add(bp, mq))
  +e3 = Equal.cong(Nat, Nat, k => 1n+Nat.add(np, k), Nat.add(bp, mq), Nat.add(mq, r), Equal.trans(Nat, Nat.add(bp, mq), Nat.add(mq, bp), Nat.add(mq, r), Jc.add_comm(bp, mq), Equal.cong(Nat, Nat, k => Nat.add(mq, k), bp, r, Equal.sym(Nat, r, bp, e))))
  +ch = Equal.trans(Nat, b1, Nat.add(np, Nat.mul(1n+q, d)), b2, e1, Equal.trans(Nat, Nat.add(np, Nat.mul(1n+q, d)), 1n+Nat.add(np, Nat.add(bp, mq)), b2, e2, e3))
  Jc.le_eq(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+q, 0n)), d), b2, b1, Equal.sym(Nat, b1, b2, ch), ih)

def Jc.dm_s(+np: Nat, +mp: Nat, +q: Nat, +r: Nat, +bp: Nat, ih: {Nat.is_le(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, mp, q, 1n+r)), 1n+bp), Nat.add(np, Nat.add(Nat.mul(q, 1n+bp), 1n+r))) == True{} : Bool}) -> {Nat.is_le(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, mp, q, 1n+r)), 1n+bp), Nat.add(1n+np, Nat.add(Nat.mul(q, 1n+bp), r))) == True{} : Bool}:
  +mq = Nat.mul(q, 1n+bp)
  +b1 = Nat.add(np, Nat.add(mq, 1n+r))
  +b2 = Nat.add(1n+np, Nat.add(mq, r))
  +ch = Equal.trans(Nat, b1, Nat.add(np, 1n+Nat.add(mq, r)), b2, Equal.cong(Nat, Nat, k => Nat.add(np, k), Nat.add(mq, 1n+r), 1n+Nat.add(mq, r), Jc.add_succ(mq, r)), Jc.add_succ(np, Nat.add(mq, r)))
  Jc.le_eq(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, mp, q, 1n+r)), 1n+bp), b2, b1, Equal.sym(Nat, b1, b2, ch), ih)

# the quotient times the divisor is at most the dividend (divmod's
# remainder and quotient walk, for a divisor 1 + bp)
def Jc.dm(+n: Nat, +m: Nat, +q: Nat, +r: Nat, +bp: Nat) -> {Nat.add(m, r) == bp : Nat} -> {Nat.is_le(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, q, r)), 1n+bp), Nat.add(n, Nat.add(Nat.mul(q, 1n+bp), r))) == True{} : Bool}:
  match n:
    case 0n:
      e => Jc.le_add_r(Nat.mul(q, 1n+bp), r)
    case 1n+np:
      match m:
        case 0n:
          +e => Jc.dm_z(np, q, r, bp, e, Jc.dm(np, r, 1n+q, 0n, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, Jc.add_zero(r), e)))
        case 1n+mp:
          +e => Jc.dm_s(np, mp, q, r, bp, Jc.dm(np, mp, q, 1n+r, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, Jc.add_succ(mp, r), e)))

def Jc.mul_div_le(+x: Nat, +d: Nat) -> {Nat.is_lt(0n, d) == True{} : Bool} -> {Nat.is_le(Nat.mul(Nat.div(x, d), d), x) == True{} : Bool}:
  match d:
    case 0n:
      h => Ext4Proof.no({Nat.is_le(Nat.mul(Nat.div(x, 0n), 0n), x) == True{} : Bool}, h)
    case 1n+bp:
      h => Jc.le_eq(Nat.mul(Nat.div(x, 1n+bp), 1n+bp), x, Nat.add(x, Nat.add(Nat.mul(0n, 1n+bp), 0n)), Equal.sym(Nat, Nat.add(x, 0n), x, Jc.add_zero(x)), Jc.dm(x, bp, 0n, 0n, bp, Jc.add_zero(bp)))

# The plan's tags: flags, checksums, and that a group's tags fit its
# descriptor

def Jc.flags_last(+e: Bool, +f: Bool, +l: Bool) -> {J.Jbd2.has(JW.Jbd2Write.flags(e, f, l), JB.Jbd2.flag_last()) == l : Bool}:
  match e f l:
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

def Jc.flags_same(+e: Bool, +f: Bool, +l: Bool) -> {J.Jbd2.has(JW.Jbd2Write.flags(e, f, l), JB.Jbd2.flag_same_uuid()) == Bool.not(f) : Bool}:
  match e f l:
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

def Jc.flags16(+e: Bool, +f: Bool, +l: Bool) -> {U32.is_eq(B.low16(JW.Jbd2Write.flags(e, f, l)), JW.Jbd2Write.flags(e, f, l)) == True{} : Bool}:
  match e f l:
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

def Jc.sf_zero(+fl: U32, hfl: {U32.is_eq(B.low16(fl), fl) == True{} : Bool}) -> {Bool.and(U32.is_eq(B.low16(fl), fl), U32.is_eq(B.low16(0), 0)) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(B.low16(fl), fl), True{}, hfl) : {Bool.and(_, U32.is_eq(B.low16(0), 0)) == True{} : Bool}
  {==}

def Jc.sf_two(+fl: U32, +c: U32, hfl: {U32.is_eq(B.low16(fl), fl) == True{} : Bool}) -> {Bool.and(U32.is_eq(B.low16(fl), fl), U32.is_eq(B.low16(U32.and(c, 65535)), U32.and(c, 65535))) == True{} : Bool}:
  %Equal.sym(Bool, U32.is_eq(B.low16(fl), fl), True{}, hfl) : {Bool.and(_, U32.is_eq(B.low16(U32.and(c, 65535)), U32.and(c, 65535))) == True{} : Bool}
  %Equal.sym(U32, B.low16(U32.and(c, 65535)), U32.and(c, 65535), BL.low16_mask(c)) : {Bool.and(True{}, U32.is_eq(_, U32.and(c, 65535))) == True{} : Bool}
  Jc.u32_refl(U32.and(c, 65535))

# a tag the plan writes has storable flags and checksum
def Jc.sfields(+g: J.Jbd2Geom, +fl: U32, +s: U32, +stored: B.Octets, +hfl: {U32.is_eq(B.low16(fl), fl) == True{} : Bool}) -> {JB.Jbd2Tag.storable.fields(Nat.is_eq(J.Jbd2Geom.csum(g), 3n), fl, JB.Jbd2.tag_csum(J.Jbd2Geom.csum(g), g, s, stored)) == True{} : Bool}:
  match g:
    case J.Jbd2Geom{+bs, +w, +cs, +sd, +fi, +mx}:
      match cs:
        case 0n:
          Jc.sf_zero(fl, hfl)
        case 1n+q1:
          match q1:
            case 0n:
              Jc.sf_zero(fl, hfl)
            case 1n+q2:
              match q2:
                case 0n:
                  Jc.sf_two(fl, JB.Jbd2.data_csum(J.Jbd2Geom{bs, w, 2n, sd, fi, mx}, s, stored), hfl)
                case 1n+q3:
                  match q3:
                    case 0n:
                      {==}
                    case 1n+q4:
                      Jc.sf_zero(fl, hfl)

# the bytes a group's tags take, the first carrying the UUID
def Jc.dsz(ws: List<&2, JW.Jbd2Write>, +g: J.Jbd2Geom, first: Bool) -> Nat:
  match ws:
    case Nil{}:
      0n
    case Con{w, t}:
      Nat.add(Nat.add(J.Jbd2Geom.tag_size(g), JB.Jbd2Tag.uuid.pick(Bool.not(first))), Jc.dsz(t, g, False{}))

def Jc.gt(ws: List<&2, JW.Jbd2Write>, +g: J.Jbd2Geom, +s: U32, first: Bool, +q: Nat) -> List<&2, JB.Jbd2Tag>:
  JT.Ext4JTx.tags(JT.Ext4JTx.data_puts(JT.Ext4JTx.datas(ws, g, s, first, q)))

def Jc.tsize(+g: J.Jbd2Geom, +b: Nat, +e: Bool, +f: Bool, +l: Bool, +c: U32) -> {JB.Jbd2Tag.size(g, JB.Jbd2Tag{b, JW.Jbd2Write.flags(e, f, l), c}) == Nat.add(J.Jbd2Geom.tag_size(g), JB.Jbd2Tag.uuid.pick(Bool.not(f))) : Nat}:
  Equal.cong(Bool, Nat, k => Nat.add(J.Jbd2Geom.tag_size(g), JB.Jbd2Tag.uuid.pick(k)), J.Jbd2.has(JW.Jbd2Write.flags(e, f, l), JB.Jbd2.flag_same_uuid()), Bool.not(f), Jc.flags_same(e, f, l))

def Jc.dfits_one(+g: J.Jbd2Geom, +s: U32, +first: Bool, +q: Nat, +avail: Nat, +b: Nat, +d: B.Octets, hb: {JB.Jbd2.block_fits(J.Jbd2Geom.wide(g), b) == True{} : Bool}, hd: {Nat.is_le(Nat.add(Nat.add(J.Jbd2Geom.tag_size(g), JB.Jbd2Tag.uuid.pick(Bool.not(first))), 0n), avail) == True{} : Bool}) -> {JB.Jbd2Desc.fits.go(g, Jc.gt(Con{JW.Jbd2Write{b, d}, Nil{}}, g, s, first, q), avail) == True{} : Bool}:
  +e = JB.Jbd2.needs_escape(d)
  +fl = JW.Jbd2Write.flags(e, first, True{})
  +c = JB.Jbd2.tag_csum(J.Jbd2Geom.csum(g), g, s, JB.Jbd2.escape(d))
  +t = {JB.Jbd2Tag{b, fl, c} : JB.Jbd2Tag}
  +pk = Nat.add(J.Jbd2Geom.tag_size(g), JB.Jbd2Tag.uuid.pick(Bool.not(first)))
  Ext4Proof.and_i(JB.Jbd2Tag.storable(g, t), Bool.and(J.Jbd2.has(fl, JB.Jbd2.flag_last()), Nat.is_le(JB.Jbd2Tag.size(g, t), avail)),
    Ext4Proof.and_i(JB.Jbd2.block_fits(J.Jbd2Geom.wide(g), b), JB.Jbd2Tag.storable.fields(Nat.is_eq(J.Jbd2Geom.csum(g), 3n), fl, c), hb, Jc.sfields(g, fl, s, JB.Jbd2.escape(d), Jc.flags16(e, first, True{}))),
    Ext4Proof.and_i(J.Jbd2.has(fl, JB.Jbd2.flag_last()), Nat.is_le(JB.Jbd2Tag.size(g, t), avail), Jc.flags_last(e, first, True{}),
      Jc.le_eql(JB.Jbd2Tag.size(g, t), pk, avail, Jc.tsize(g, b, e, first, True{}, c), Jc.le_eql(pk, Nat.add(pk, 0n), avail, Equal.sym(Nat, Nat.add(pk, 0n), pk, Jc.add_zero(pk)), hd))))

def Jc.dfits(ws: List<&2, JW.Jbd2Write>, +g: J.Jbd2Geom, +s: U32, +first: Bool, +q: Nat, +avail: Nat) -> {JT.Ext4JTx.blocks_fit(J.Jbd2Geom.wide(g), ws) == True{} : Bool} -> {Nat.is_lt(0n, List.length(&2, JW.Jbd2Write, ws)) == True{} : Bool} -> {Nat.is_le(Jc.dsz(ws, g, first), avail) == True{} : Bool} -> {JB.Jbd2Desc.fits.go(g, Jc.gt(ws, g, s, first, q), avail) == True{} : Bool}:
  match ws:
    case Nil{}:
      +hb => +hz => +hd => Ext4Proof.no({JB.Jbd2Desc.fits.go(g, Nil{}, avail) == True{} : Bool}, hz)
    case Con{JW.Jbd2Write{+b, +d}, Nil{}}:
      +hb => +hz => +hd => Jc.dfits_one(g, s, first, q, avail, b, d, Ext4Proof.and_l(JB.Jbd2.block_fits(J.Jbd2Geom.wide(g), b), True{}, hb), hd)
    case Con{JW.Jbd2Write{+b, +d}, Con{JW.Jbd2Write{+b2, +d2}, +t2}}:
      +hb => +hz => +hd =>
        +w = J.Jbd2Geom.wide(g)
        +tz = J.Jbd2Geom.tag_size(g)
        +e = JB.Jbd2.needs_escape(d)
        +fl = JW.Jbd2Write.flags(e, first, False{})
        +c = JB.Jbd2.tag_csum(J.Jbd2Geom.csum(g), g, s, JB.Jbd2.escape(d))
        +t = {JB.Jbd2Tag{b, fl, c} : JB.Jbd2Tag}
        +sz = JB.Jbd2Tag.size(g, t)
        +sz0 = Nat.add(tz, JB.Jbd2Tag.uuid.pick(Bool.not(first)))
        +rws = {Con{JW.Jbd2Write{b2, d2}, t2} : List<&2, JW.Jbd2Write>}
        +d2s = Jc.dsz(rws, g, False{})
        +rest = Jc.gt(rws, g, s, False{}, Nat.add(q, 1n))
        +esz = Jc.tsize(g, b, e, first, False{}, c)
        +hb2 = Ext4Proof.and_r(JB.Jbd2.block_fits(w, b), JT.Ext4JTx.blocks_fit(w, rws), hb)
        +ht = Ext4Proof.le_trans(tz, Nat.add(tz, 0n), d2s, Jc.le_add_r(tz, 0n), Jc.le_add_r(Nat.add(tz, 0n), Jc.dsz(t2, g, False{})))
        +h3 = Jc.le_eql(Nat.add(sz, tz), Nat.add(sz0, tz), avail, Equal.cong(Nat, Nat, k => Nat.add(k, tz), sz, sz0, esz), Ext4Proof.le_trans(Nat.add(sz0, tz), Nat.add(sz0, d2s), avail, Jc.le_mono_l(sz0, tz, d2s, ht), hd))
        +h4 = Jc.le_eq(d2s, Nat.sub(avail, sz), Nat.sub(avail, sz0), Equal.cong(Nat, Nat, k => Nat.sub(avail, k), sz, sz0, esz), Jc.le_sub(sz0, d2s, avail, hd))
        Ext4Proof.and_i(JB.Jbd2Tag.storable(g, t), Bool.and(Bool.not(J.Jbd2.has(fl, JB.Jbd2.flag_last())), Bool.and(Nat.is_le(Nat.add(sz, tz), avail), JB.Jbd2Desc.fits.go(g, rest, Nat.sub(avail, sz)))),
          Ext4Proof.and_i(JB.Jbd2.block_fits(w, b), JB.Jbd2Tag.storable.fields(Nat.is_eq(J.Jbd2Geom.csum(g), 3n), fl, c), Ext4Proof.and_l(JB.Jbd2.block_fits(w, b), JT.Ext4JTx.blocks_fit(w, rws), hb), Jc.sfields(g, fl, s, JB.Jbd2.escape(d), Jc.flags16(e, first, False{}))),
          Ext4Proof.and_i(Bool.not(J.Jbd2.has(fl, JB.Jbd2.flag_last())), Bool.and(Nat.is_le(Nat.add(sz, tz), avail), JB.Jbd2Desc.fits.go(g, rest, Nat.sub(avail, sz))),
            Equal.cong(Bool, Bool, x => Bool.not(x), J.Jbd2.has(fl, JB.Jbd2.flag_last()), False{}, Jc.flags_last(e, first, False{})),
            Ext4Proof.and_i(Nat.is_le(Nat.add(sz, tz), avail), JB.Jbd2Desc.fits.go(g, rest, Nat.sub(avail, sz)), h3,
              Jc.dfits(rws, g, s, False{}, Nat.add(q, 1n), Nat.sub(avail, sz), hb2, {==}, h4))))

def Jc.dsz_f(+g: J.Jbd2Geom, ws: List<&2, JW.Jbd2Write>) -> {Jc.dsz(ws, g, False{}) == Nat.mul(List.length(&2, JW.Jbd2Write, ws), J.Jbd2Geom.tag_size(g)) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      +tz = J.Jbd2Geom.tag_size(g)
      Equal.trans(Nat, Nat.add(Nat.add(tz, 0n), Jc.dsz(t, g, False{})), Nat.add(tz, Jc.dsz(t, g, False{})), Nat.add(tz, Nat.mul(List.length(&2, JW.Jbd2Write, t), tz)),
        Equal.cong(Nat, Nat, k => Nat.add(k, Jc.dsz(t, g, False{})), Nat.add(tz, 0n), tz, Jc.add_zero(tz)),
        Equal.cong(Nat, Nat, k => Nat.add(tz, k), Jc.dsz(t, g, False{}), Nat.mul(List.length(&2, JW.Jbd2Write, t), tz), Jc.dsz_f(g, t)))

# a group of at most capacity writes fits its descriptor's tag area
def Jc.gbound(+g: J.Jbd2Geom, h: List<&2, JW.Jbd2Write>) -> {Nat.is_lt(0n, JB.Jbd2Desc.capacity(g)) == True{} : Bool} -> {Nat.is_lt(0n, List.length(&2, JW.Jbd2Write, h)) == True{} : Bool} -> {Nat.is_le(List.length(&2, JW.Jbd2Write, h), JB.Jbd2Desc.capacity(g)) == True{} : Bool} -> {Nat.is_le(Jc.dsz(h, g, True{}), Jc.darea(g)) == True{} : Bool}:
  match h:
    case Nil{}:
      +hc => +hz => +hk => Ext4Proof.no({Nat.is_le(0n, Jc.darea(g)) == True{} : Bool}, hz)
    case Con{+w, +t}:
      +hc => +hz => +hk =>
        +tz = J.Jbd2Geom.tag_size(g)
        +n = Jc.darea(g)
        +x = Nat.sub(n, 16n)
        +lh = List.length(&2, JW.Jbd2Write, Con{w, t})
        +mt = Nat.mul(List.length(&2, JW.Jbd2Write, t), tz)
        +hpos = Jc.lt0(tz, Jc.ts8(g))
        +hm = Ext4Proof.le_trans(Nat.mul(lh, tz), Nat.mul(JB.Jbd2Desc.capacity(g), tz), x, Jc.le_mul(lh, JB.Jbd2Desc.capacity(g), tz, hk), Jc.mul_div_le(x, tz, hpos))
        +h16 = Jc.sub_pos(n, 16n, Ext4Proof.lt_le_lt(0n, tz, x, hpos, Ext4Proof.le_trans(tz, Nat.mul(lh, tz), x, Jc.le_add_r(tz, mt), hm)))
        +eqd = Equal.trans(Nat, Jc.dsz(Con{w, t}, g, True{}), Nat.add(Nat.add(tz, 16n), mt), Nat.add(16n, Nat.mul(lh, tz)),
          Equal.cong(Nat, Nat, k => Nat.add(Nat.add(tz, 16n), k), Jc.dsz(t, g, False{}), mt, Jc.dsz_f(g, t)),
          Equal.trans(Nat, Nat.add(Nat.add(tz, 16n), mt), Nat.add(tz, Nat.add(16n, mt)), Nat.add(16n, Nat.mul(lh, tz)), Jc.add_assoc(tz, 16n, mt), Jc.add_swap(tz, 16n, mt)))
        Jc.le_eql(Jc.dsz(Con{w, t}, g, True{}), Nat.add(16n, Nat.mul(lh, tz)), n, eqd, Jc.le_eq(Nat.add(16n, Nat.mul(lh, tz)), n, Nat.add(16n, x), Equal.sym(Nat, Nat.add(16n, x), n, Jc.add_sub(16n, n, h16)), Jc.le_mono_l(16n, Nat.mul(lh, tz), x, hm)))

# Groups: each nonempty and at most capacity long; every block fits

def Jc.chunks_ok(gs: List<&2, List<&2, JW.Jbd2Write>>, +cap: Nat) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case Con{+h, t}:
      Bool.and(Nat.is_lt(0n, List.length(&2, JW.Jbd2Write, h)), Bool.and(Nat.is_le(List.length(&2, JW.Jbd2Write, h), cap), Jc.chunks_ok(t, cap)))

def Jc.ck_add(full: Bool, +w: JW.Jbd2Write, +g0: List<&2, JW.Jbd2Write>, +rest: List<&2, List<&2, JW.Jbd2Write>>, +cap: Nat) -> {Nat.is_le(cap, List.length(&2, JW.Jbd2Write, g0)) == full : Bool} -> {Nat.is_lt(0n, cap) == True{} : Bool} -> {Jc.chunks_ok(Con{g0, rest}, cap) == True{} : Bool} -> {Jc.chunks_ok(JT.Ext4JTx.chunks.add(full, w, g0, rest), cap) == True{} : Bool}:
  match full:
    case True{}:
      +hf => +hc => +hk => Ext4Proof.and_i(True{}, Bool.and(Nat.is_le(1n, cap), Jc.chunks_ok(Con{g0, rest}, cap)), {==}, Ext4Proof.and_i(Nat.is_le(1n, cap), Jc.chunks_ok(Con{g0, rest}, cap), Jc.lt_succ_le(0n, cap, hc), hk))
    case False{}:
      +hf => +hc => +hk =>
        +l0 = List.length(&2, JW.Jbd2Write, g0)
        +a1 = Nat.is_lt(0n, l0)
        +a2 = Nat.is_le(l0, cap)
        +a3 = Jc.chunks_ok(rest, cap)
        Ext4Proof.and_i(True{}, Bool.and(Nat.is_le(1n+l0, cap), a3), {==}, Ext4Proof.and_i(Nat.is_le(1n+l0, cap), a3, Jc.lt_succ_le(l0, cap, Ext4Proof.not_le_lt(cap, l0, hf)), Ext4Proof.and_r(a2, a3, Ext4Proof.and_r(a1, Bool.and(a2, a3), hk))))

def Jc.ck_put(+w: JW.Jbd2Write, gs: List<&2, List<&2, JW.Jbd2Write>>, +cap: Nat) -> {Nat.is_lt(0n, cap) == True{} : Bool} -> {Jc.chunks_ok(gs, cap) == True{} : Bool} -> {Jc.chunks_ok(JT.Ext4JTx.chunks.put(w, gs, cap), cap) == True{} : Bool}:
  match gs:
    case Nil{}:
      +hc => +hk => Ext4Proof.and_i(True{}, Bool.and(Nat.is_le(1n, cap), True{}), {==}, Ext4Proof.and_i(Nat.is_le(1n, cap), True{}, Jc.lt_succ_le(0n, cap, hc), {==}))
    case Con{+g0, +rest}:
      +hc => +hk => Jc.ck_add(Nat.is_le(cap, List.length(&2, JW.Jbd2Write, g0)), w, g0, rest, cap, {==}, hc, hk)

def Jc.ck_all(ws: List<&2, JW.Jbd2Write>, +cap: Nat) -> {Nat.is_lt(0n, cap) == True{} : Bool} -> {Jc.chunks_ok(JT.Ext4JTx.chunks(ws, cap), cap) == True{} : Bool}:
  match ws:
    case Nil{}:
      +hc => {==}
    case Con{+w, +t}:
      +hc => Jc.ck_put(w, JT.Ext4JTx.chunks(t, cap), cap, hc, Jc.ck_all(t, cap, hc))

def Jc.band_assoc(+x: Bool, +y: Bool, +z: Bool) -> {Bool.and(x, Bool.and(y, z)) == Bool.and(Bool.and(x, y), z) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def Jc.bf_app(+w: Bool, a: List<&2, JW.Jbd2Write>, +b: List<&2, JW.Jbd2Write>) -> {JT.Ext4JTx.blocks_fit(w, List.append(&2, JW.Jbd2Write, a, b)) == Bool.and(JT.Ext4JTx.blocks_fit(w, a), JT.Ext4JTx.blocks_fit(w, b)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{JW.Jbd2Write{+bb, +d}, +t}:
      Equal.trans(Bool, Bool.and(JB.Jbd2.block_fits(w, bb), JT.Ext4JTx.blocks_fit(w, List.append(&2, JW.Jbd2Write, t, b))), Bool.and(JB.Jbd2.block_fits(w, bb), Bool.and(JT.Ext4JTx.blocks_fit(w, t), JT.Ext4JTx.blocks_fit(w, b))), Bool.and(Bool.and(JB.Jbd2.block_fits(w, bb), JT.Ext4JTx.blocks_fit(w, t)), JT.Ext4JTx.blocks_fit(w, b)),
        Equal.cong(Bool, Bool, k => Bool.and(JB.Jbd2.block_fits(w, bb), k), JT.Ext4JTx.blocks_fit(w, List.append(&2, JW.Jbd2Write, t, b)), Bool.and(JT.Ext4JTx.blocks_fit(w, t), JT.Ext4JTx.blocks_fit(w, b)), Jc.bf_app(w, t, b)),
        Jc.band_assoc(JB.Jbd2.block_fits(w, bb), JT.Ext4JTx.blocks_fit(w, t), JT.Ext4JTx.blocks_fit(w, b)))

def Jc.gfit(+w: Bool, gs: List<&2, List<&2, JW.Jbd2Write>>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case Con{+h, t}:
      Bool.and(JT.Ext4JTx.blocks_fit(w, h), Jc.gfit(w, t))

def Jc.gfit_concat(gs: List<&2, List<&2, JW.Jbd2Write>>, +w: Bool) -> {JT.Ext4JTx.blocks_fit(w, List.concat(&2, JW.Jbd2Write, gs)) == True{} : Bool} -> {Jc.gfit(w, gs) == True{} : Bool}:
  match gs:
    case Nil{}:
      +hh => {==}
    case Con{+h, +t}:
      +hh =>
        +ha = Equal.trans(Bool, Bool.and(JT.Ext4JTx.blocks_fit(w, h), JT.Ext4JTx.blocks_fit(w, List.concat(&2, JW.Jbd2Write, t))), JT.Ext4JTx.blocks_fit(w, List.append(&2, JW.Jbd2Write, h, List.concat(&2, JW.Jbd2Write, t))), True{}, Equal.sym(Bool, JT.Ext4JTx.blocks_fit(w, List.append(&2, JW.Jbd2Write, h, List.concat(&2, JW.Jbd2Write, t))), Bool.and(JT.Ext4JTx.blocks_fit(w, h), JT.Ext4JTx.blocks_fit(w, List.concat(&2, JW.Jbd2Write, t))), Jc.bf_app(w, h, List.concat(&2, JW.Jbd2Write, t))), hh)
        Ext4Proof.and_i(JT.Ext4JTx.blocks_fit(w, h), Jc.gfit(w, t), Ext4Proof.and_l(JT.Ext4JTx.blocks_fit(w, h), JT.Ext4JTx.blocks_fit(w, List.concat(&2, JW.Jbd2Write, t)), ha), Jc.gfit_concat(t, w, Ext4Proof.and_r(JT.Ext4JTx.blocks_fit(w, h), JT.Ext4JTx.blocks_fit(w, List.concat(&2, JW.Jbd2Write, t)), ha)))

def Jc.bf_marks(+bs: Nat, ws: List<&2, JW.Jbd2Write>, +w: Bool) -> {JT.Ext4JTx.blocks_fit(w, JT.Ext4JTx.marks(bs, ws)) == JT.Ext4JTx.blocks_fit(w, ws) : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{JW.Jbd2Write{+b, +d}, +t}:
      Equal.cong(Bool, Bool, k => Bool.and(JB.Jbd2.block_fits(w, b), k), JT.Ext4JTx.blocks_fit(w, JT.Ext4JTx.marks(bs, t)), JT.Ext4JTx.blocks_fit(w, t), Jc.bf_marks(bs, t, w))

def Jc.bf_keep(hit: Bool, +b0: Nat, +d0: B.Octets, +rest: List<&2, JW.Jbd2Write>, +w: Bool) -> {JB.Jbd2.block_fits(w, b0) == True{} : Bool} -> {JT.Ext4JTx.blocks_fit(w, rest) == True{} : Bool} -> {JT.Ext4JTx.blocks_fit(w, JT.Ext4JTx.keep(hit, JW.Jbd2Write{b0, d0}, rest)) == True{} : Bool}:
  match hit:
    case True{}:
      h1 => h2 => Ext4Proof.and_i(JB.Jbd2.block_fits(w, b0), JT.Ext4JTx.blocks_fit(w, rest), h1, h2)
    case False{}:
      h1 => h2 => h2

def Jc.bf_out(+fresh: List<&2, Nat>, ws: List<&2, JW.Jbd2Write>, +w: Bool) -> {JT.Ext4JTx.blocks_fit(w, ws) == True{} : Bool} -> {JT.Ext4JTx.blocks_fit(w, JT.Ext4JTx.fresh_out(fresh, ws)) == True{} : Bool}:
  match ws:
    case Nil{}:
      +h => {==}
    case Con{JW.Jbd2Write{+b0, +d0}, +t}:
      +h => Jc.bf_keep(Bool.not(JL.Jbd2Log.member(fresh, b0)), b0, d0, JT.Ext4JTx.fresh_out(fresh, t), w, Ext4Proof.and_l(JB.Jbd2.block_fits(w, b0), JT.Ext4JTx.blocks_fit(w, t), h), Jc.bf_out(fresh, t, w, Ext4Proof.and_r(JB.Jbd2.block_fits(w, b0), JT.Ext4JTx.blocks_fit(w, t), h)))

def Jc.bf_logged(m: JT.Jbd2Mode, +fresh: List<&2, Nat>, +bs: Nat, +ws: List<&2, JW.Jbd2Write>, +w: Bool) -> {JT.Ext4JTx.blocks_fit(w, ws) == True{} : Bool} -> {JT.Ext4JTx.blocks_fit(w, JT.Ext4JTx.logged(m, fresh, bs, ws)) == True{} : Bool}:
  match m:
    case JT.Jbd2DataJournal{}:
      h => Equal.trans(Bool, JT.Ext4JTx.blocks_fit(w, JT.Ext4JTx.marks(bs, ws)), JT.Ext4JTx.blocks_fit(w, ws), True{}, Jc.bf_marks(bs, ws, w), h)
    case JT.Jbd2DataOrdered{}:
      h => Equal.trans(Bool, JT.Ext4JTx.blocks_fit(w, JT.Ext4JTx.marks(bs, JT.Ext4JTx.fresh_out(fresh, ws))), JT.Ext4JTx.blocks_fit(w, JT.Ext4JTx.fresh_out(fresh, ws)), True{}, Jc.bf_marks(bs, JT.Ext4JTx.fresh_out(fresh, ws), w), Jc.bf_out(fresh, ws, w, h))

def Jc.lt_ne0(+x: Nat) -> {Nat.is_lt(0n, x) == True{} : Bool} -> {Nat.is_eq(x, 0n) == False{} : Bool}:
  match x:
    case 0n:
      h => Ext4Proof.no({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 1n+p:
      h => {==}

def Jc.cap_eq(+g: J.Jbd2Geom, hc: {Nat.is_lt(0n, JB.Jbd2Desc.capacity(g)) == True{} : Bool}) -> {JT.Ext4JTx.cap(g) == JB.Jbd2Desc.capacity(g) : Nat}:
  %Equal.sym(Bool, Nat.is_eq(JB.Jbd2Desc.capacity(g), 0n), False{}, Jc.lt_ne0(JB.Jbd2Desc.capacity(g), hc)) : {JT.Ext4JTx.cap.pick(_, JB.Jbd2Desc.capacity(g)) == JB.Jbd2Desc.capacity(g) : Nat}
  {==}

# Positions in the log: the scanner's, and the steps'

def Jc.lt_add1(+q: Nat) -> {Nat.is_lt(q, Nat.add(q, 1n)) == True{} : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      Jc.lt_add1(p)

def Jc.adv(ws: List<&2, JW.Jbd2Write>, +q: Nat) -> Nat:
  match ws:
    case Nil{}:
      q
    case Con{w, t}:
      Jc.adv(t, Nat.add(q, 1n))

def Jc.adv_add(ws: List<&2, JW.Jbd2Write>, +q: Nat) -> {Jc.adv(ws, q) == Nat.add(q, List.length(&2, JW.Jbd2Write, ws)) : Nat}:
  match ws:
    case Nil{}:
      Equal.sym(Nat, Nat.add(q, 0n), q, Jc.add_zero(q))
    case Con{+w, +t}:
      Equal.trans(Nat, Jc.adv(t, Nat.add(q, 1n)), Nat.add(Nat.add(q, 1n), List.length(&2, JW.Jbd2Write, t)), Nat.add(q, Nat.add(1n, List.length(&2, JW.Jbd2Write, t))), Jc.adv_add(t, Nat.add(q, 1n)), Jc.add_assoc(q, 1n, List.length(&2, JW.Jbd2Write, t)))

def Jc.adv_ge(+ws: List<&2, JW.Jbd2Write>, +q: Nat) -> {Nat.is_le(q, Jc.adv(ws, q)) == True{} : Bool}:
  Jc.le_eq(q, Jc.adv(ws, q), Nat.add(q, List.length(&2, JW.Jbd2Write, ws)), Jc.adv_add(ws, q), Jc.le_add_r(q, List.length(&2, JW.Jbd2Write, ws)))

def Jc.next_nw(+g: J.Jbd2Geom, +p: Nat, h: {Nat.is_lt(Nat.add(p, 1n), J.Jbd2Geom.maxlen(g)) == True{} : Bool}) -> {J.Jbd2Geom.next(g, p) == Nat.add(p, 1n) : Nat}:
  %Equal.sym(Bool, Nat.is_le(J.Jbd2Geom.maxlen(g), Nat.add(p, 1n)), False{}, Jc.lt_not_le(Nat.add(p, 1n), J.Jbd2Geom.maxlen(g), h)) : {J.Jbd2Geom.next.pick(_, J.Jbd2Geom.first(g), Nat.add(p, 1n)) == Nat.add(p, 1n) : Nat}
  {==}

# the scanner places a descriptor's tags at the plan's positions
def Jc.place_ok(ws: List<&2, JW.Jbd2Write>, +g: J.Jbd2Geom, +s: U32, +f: Bool, +q: Nat, +acc: List<&2, JL.Jbd2Put>) -> {Nat.is_lt(Jc.adv(ws, q), J.Jbd2Geom.maxlen(g)) == True{} : Bool} -> {JN.Jbd2Scan.place(Jc.gt(ws, g, s, f, q), g, q, acc) == (List.reverse.go(&2, JL.Jbd2Put, acc, JT.Ext4JTx.data_puts(JT.Ext4JTx.datas(ws, g, s, f, q))), Jc.adv(ws, q)) : List<&2, JL.Jbd2Put> & Nat}:
  match ws:
    case Nil{}:
      +h => {==}
    case Con{JW.Jbd2Write{+b, +d}, +t}:
      +h =>
        +fl = JW.Jbd2Write.flags(JB.Jbd2.needs_escape(d), f, JW.Jbd2Write.is_nil(t))
        +c = JB.Jbd2.tag_csum(J.Jbd2Geom.csum(g), g, s, JB.Jbd2.escape(d))
        +hn = Ext4Proof.le_lt_lt(Nat.add(q, 1n), Jc.adv(t, Nat.add(q, 1n)), J.Jbd2Geom.maxlen(g), Jc.adv_ge(t, Nat.add(q, 1n)), h)
        %Equal.sym(Nat, J.Jbd2Geom.next(g, q), Nat.add(q, 1n), Jc.next_nw(g, q, hn)) : {JN.Jbd2Scan.place(Jc.gt(t, g, s, False{}, Nat.add(q, 1n)), g, _, Con{JL.Jbd2Put{b, q, fl, c}, acc}) == (List.reverse.go(&2, JL.Jbd2Put, Con{JL.Jbd2Put{b, q, fl, c}, acc}, JT.Ext4JTx.data_puts(JT.Ext4JTx.datas(t, g, s, False{}, Nat.add(q, 1n)))), Jc.adv(t, Nat.add(q, 1n))) : List<&2, JL.Jbd2Put> & Nat}
        Jc.place_ok(t, g, s, False{}, Nat.add(q, 1n), Con{JL.Jbd2Put{b, q, fl, c}, acc}, h)

# the data blocks, at positions the scanner has passed, are passed over
def Jc.skip_ds(ws: List<&2, JW.Jbd2Write>, +g: J.Jbd2Geom, +s: U32, +f: Bool, +q: Nat, +check: Bool, +st: JN.Jbd2Scan, +rest: List<&2, JT.Ext4JStep>) -> {Nat.is_le(Jc.adv(ws, q), JN.Jbd2Scan.pos(st)) == True{} : Bool} -> {Laws.Ext4Laws.feed(List.append(&2, JT.Ext4JStep, JT.Ext4JTx.datas(ws, g, s, f, q), rest), check, g, st) == Laws.Ext4Laws.feed(rest, check, g, st) : JN.Jbd2Scan}:
  match ws:
    case Nil{}:
      +h => {==}
    case Con{JW.Jbd2Write{+b, +d}, +t}:
      +h =>
        +ne = Ext4Proof.lt_le_ne(q, Nat.add(q, 1n), JN.Jbd2Scan.pos(st), Jc.lt_add1(q), Ext4Proof.le_trans(Nat.add(q, 1n), Jc.adv(t, Nat.add(q, 1n)), JN.Jbd2Scan.pos(st), Jc.adv_ge(t, Nat.add(q, 1n)), h))
        %Equal.sym(Bool, Nat.is_eq(q, JN.Jbd2Scan.pos(st)), False{}, ne) : {Laws.Ext4Laws.feed(List.append(&2, JT.Ext4JStep, JT.Ext4JTx.datas(t, g, s, False{}, Nat.add(q, 1n)), rest), check, g, Laws.Ext4Laws.feed.at(_, check, g, st, JB.Jbd2.escape(d))) == Laws.Ext4Laws.feed(rest, check, g, st) : JN.Jbd2Scan}
        Jc.skip_ds(t, g, s, False{}, Nat.add(q, 1n), check, st, rest, h)

# One group: the descriptor at pos, read; its data blocks passed over

def Jc.fg1(+h: List<&2, JW.Jbd2Write>, +check: Bool, +g: J.Jbd2Geom, +uuid: B.Octets, +seq: Nat, +pos: Nat, +rs: List<&2, JL.Jbd2Rec>, +rest: List<&2, JT.Ext4JStep>) -> {Laws.Ext4Laws.feed(List.append(&2, JT.Ext4JStep, JT.Ext4JTx.group(h, g, U32.from_nat(seq), uuid, pos), rest), check, g, JN.Jbd2Scan{pos, seq, rs, True{}, None{}}) == Laws.Ext4Laws.feed(List.append(&2, JT.Ext4JStep, JT.Ext4JTx.datas(h, g, U32.from_nat(seq), True{}, Nat.add(pos, 1n)), rest), check, g, Laws.Ext4Laws.feed.at(Nat.is_eq(pos, pos), check, g, JN.Jbd2Scan{pos, seq, rs, True{}, None{}}, JB.Jbd2Desc.encode(g, U32.from_nat(seq), Jc.gt(h, g, U32.from_nat(seq), True{}, Nat.add(pos, 1n)), uuid))) : JN.Jbd2Scan}:
  {==}

def Jc.fg2(+check: Bool, +g: J.Jbd2Geom, +blk: B.Octets, +seq: Nat, +pos: Nat, +rs: List<&2, JL.Jbd2Rec>) -> {Laws.Ext4Laws.feed.at(True{}, check, g, JN.Jbd2Scan{pos, seq, rs, True{}, None{}}, blk) == JN.Jbd2Scan.kind(U32.to_nat(JB.Jbd2Block.kind(blk, U32.from_nat(seq))), check, g, blk, pos, seq, rs) : JN.Jbd2Scan}:
  {==}

def Jc.fg3(+check: Bool, +g: J.Jbd2Geom, +blk: B.Octets, +seq: Nat, +pos: Nat, +rs: List<&2, JL.Jbd2Rec>) -> {JN.Jbd2Scan.kind(U32.to_nat(1), check, g, blk, pos, seq, rs) == JN.Jbd2Scan.desc(JB.Jbd2Desc.decode(check, g, blk), g, pos, seq, rs) : JN.Jbd2Scan}:
  {==}

def Jc.fg4(+ts: List<&2, JB.Jbd2Tag>, +g: J.Jbd2Geom, +seq: Nat, +pos: Nat, +rs: List<&2, JL.Jbd2Rec>) -> {JN.Jbd2Scan.desc(Some{ts}, g, pos, seq, rs) == JN.Jbd2Scan.desc.go(JN.Jbd2Scan.place(ts, g, J.Jbd2Geom.next(g, pos), Nil{}), seq, rs) : JN.Jbd2Scan}:
  {==}

def Jc.fg5(+ps: List<&2, JL.Jbd2Put>, +e: Nat, +seq: Nat, +rs: List<&2, JL.Jbd2Rec>) -> {JN.Jbd2Scan.desc.go((List.reverse.go(&2, JL.Jbd2Put, Nil{}, ps), e), seq, rs) == JN.Jbd2Scan{e, seq, Con{JL.Jbd2RDesc{seq, ps}, rs}, True{}, None{}} : JN.Jbd2Scan}:
  {==}

def Jc.feed_group(+h: List<&2, JW.Jbd2Write>, +check: Bool, +g: J.Jbd2Geom, +uuid: B.Octets, +seq: Nat, +pos: Nat, +rs: List<&2, JL.Jbd2Rec>, +rest: List<&2, JT.Ext4JStep>, hu: {Nat.is_eq(B.Octets.len(uuid), 16n) == True{} : Bool}, hf: {JB.Jbd2Desc.fits(g, Jc.gt(h, g, U32.from_nat(seq), True{}, Nat.add(pos, 1n))) == True{} : Bool}, +hnw: {Nat.is_lt(Jc.adv(h, Nat.add(pos, 1n)), J.Jbd2Geom.maxlen(g)) == True{} : Bool}) -> {Laws.Ext4Laws.feed(List.append(&2, JT.Ext4JStep, JT.Ext4JTx.group(h, g, U32.from_nat(seq), uuid, pos), rest), check, g, JN.Jbd2Scan{pos, seq, rs, True{}, None{}}) == Laws.Ext4Laws.feed(rest, check, g, JN.Jbd2Scan{Jc.adv(h, Nat.add(pos, 1n)), seq, Con{JL.Jbd2RDesc{seq, JT.Ext4JTx.data_puts(JT.Ext4JTx.datas(h, g, U32.from_nat(seq), True{}, Nat.add(pos, 1n)))}, rs}, True{}, None{}}) : JN.Jbd2Scan}:
  +s = U32.from_nat(seq)
  +q = Nat.add(pos, 1n)
  +ds = JT.Ext4JTx.datas(h, g, s, True{}, q)
  +ps = JT.Ext4JTx.data_puts(ds)
  +ts = Jc.gt(h, g, s, True{}, q)
  +blk = JB.Jbd2Desc.encode(g, s, ts, uuid)
  +st = {JN.Jbd2Scan{pos, seq, rs, True{}, None{}} : JN.Jbd2Scan}
  +e = Jc.adv(h, q)
  +st2 = {JN.Jbd2Scan{e, seq, Con{JL.Jbd2RDesc{seq, ps}, rs}, True{}, None{}} : JN.Jbd2Scan}
  +ad = List.append(&2, JT.Ext4JStep, ds, rest)
  +rhs = Laws.Ext4Laws.feed(rest, check, g, st2)
  %Equal.sym(JN.Jbd2Scan, Laws.Ext4Laws.feed(List.append(&2, JT.Ext4JStep, JT.Ext4JTx.group(h, g, s, uuid, pos), rest), check, g, st), Laws.Ext4Laws.feed(ad, check, g, Laws.Ext4Laws.feed.at(Nat.is_eq(pos, pos), check, g, st, blk)), Jc.fg1(h, check, g, uuid, seq, pos, rs, rest)) : {_ == rhs : JN.Jbd2Scan}
  %Equal.sym(Bool, Nat.is_eq(pos, pos), True{}, Ext4Proof.eq_refl(pos)) : {Laws.Ext4Laws.feed(ad, check, g, Laws.Ext4Laws.feed.at(_, check, g, st, blk)) == rhs : JN.Jbd2Scan}
  %Equal.sym(JN.Jbd2Scan, Laws.Ext4Laws.feed.at(True{}, check, g, st, blk), JN.Jbd2Scan.kind(U32.to_nat(JB.Jbd2Block.kind(blk, s)), check, g, blk, pos, seq, rs), Jc.fg2(check, g, blk, seq, pos, rs)) : {Laws.Ext4Laws.feed(ad, check, g, _) == rhs : JN.Jbd2Scan}
  %Equal.sym(U32, JB.Jbd2Block.kind(blk, s), 1, Laws.jdesc_kind(g, s, ts, uuid)) : {Laws.Ext4Laws.feed(ad, check, g, JN.Jbd2Scan.kind(U32.to_nat(_), check, g, blk, pos, seq, rs)) == rhs : JN.Jbd2Scan}
  %Equal.sym(JN.Jbd2Scan, JN.Jbd2Scan.kind(U32.to_nat(1), check, g, blk, pos, seq, rs), JN.Jbd2Scan.desc(JB.Jbd2Desc.decode(check, g, blk), g, pos, seq, rs), Jc.fg3(check, g, blk, seq, pos, rs)) : {Laws.Ext4Laws.feed(ad, check, g, _) == rhs : JN.Jbd2Scan}
  %Equal.sym(Maybe<&2, List<&2, JB.Jbd2Tag>>, JB.Jbd2Desc.decode(check, g, blk), Some{ts}, Laws.jdesc_round_trip(check, g, s, ts, uuid, hu, hf)) : {Laws.Ext4Laws.feed(ad, check, g, JN.Jbd2Scan.desc(_, g, pos, seq, rs)) == rhs : JN.Jbd2Scan}
  %Equal.sym(JN.Jbd2Scan, JN.Jbd2Scan.desc(Some{ts}, g, pos, seq, rs), JN.Jbd2Scan.desc.go(JN.Jbd2Scan.place(ts, g, J.Jbd2Geom.next(g, pos), Nil{}), seq, rs), Jc.fg4(ts, g, seq, pos, rs)) : {Laws.Ext4Laws.feed(ad, check, g, _) == rhs : JN.Jbd2Scan}
  %Equal.sym(Nat, J.Jbd2Geom.next(g, pos), q, Jc.next_nw(g, pos, Ext4Proof.le_lt_lt(q, e, J.Jbd2Geom.maxlen(g), Jc.adv_ge(h, q), hnw))) : {Laws.Ext4Laws.feed(ad, check, g, JN.Jbd2Scan.desc.go(JN.Jbd2Scan.place(ts, g, _, Nil{}), seq, rs)) == rhs : JN.Jbd2Scan}
  %Equal.sym(List<&2, JL.Jbd2Put> & Nat, JN.Jbd2Scan.place(ts, g, q, Nil{}), (List.reverse.go(&2, JL.Jbd2Put, Nil{}, ps), e), Jc.place_ok(h, g, s, True{}, q, Nil{}, hnw)) : {Laws.Ext4Laws.feed(ad, check, g, JN.Jbd2Scan.desc.go(_, seq, rs)) == rhs : JN.Jbd2Scan}
  %Equal.sym(JN.Jbd2Scan, JN.Jbd2Scan.desc.go((List.reverse.go(&2, JL.Jbd2Put, Nil{}, ps), e), seq, rs), st2, Jc.fg5(ps, e, seq, rs)) : {Laws.Ext4Laws.feed(ad, check, g, _) == rhs : JN.Jbd2Scan}
  Jc.skip_ds(h, g, s, True{}, q, check, st2, rest, Ext4Proof.le_refl(e))

# Every group

def Jc.lend(gs: List<&2, List<&2, JW.Jbd2Write>>, +pos: Nat) -> Nat:
  match gs:
    case Nil{}:
      pos
    case Con{+h, t}:
      Jc.lend(t, Nat.add(pos, 1n+List.length(&2, JW.Jbd2Write, h)))

def Jc.drecs(gs: List<&2, List<&2, JW.Jbd2Write>>, +seq: Nat, +g: J.Jbd2Geom, +s: U32, +pos: Nat) -> List<&2, JL.Jbd2Rec>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{JL.Jbd2RDesc{seq, JT.Ext4JTx.data_puts(JT.Ext4JTx.datas(h, g, s, True{}, Nat.add(pos, 1n)))}, Jc.drecs(t, seq, g, s, Nat.add(pos, 1n+List.length(&2, JW.Jbd2Write, h)))}

def Jc.lend_ge(gs: List<&2, List<&2, JW.Jbd2Write>>, +pos: Nat) -> {Nat.is_le(pos, Jc.lend(gs, pos)) == True{} : Bool}:
  match gs:
    case Nil{}:
      Ext4Proof.le_refl(pos)
    case Con{+h, +t}:
      Ext4Proof.le_trans(pos, Nat.add(pos, 1n+List.length(&2, JW.Jbd2Write, h)), Jc.lend(t, Nat.add(pos, 1n+List.length(&2, JW.Jbd2Write, h))), Jc.le_add_r(pos, 1n+List.length(&2, JW.Jbd2Write, h)), Jc.lend_ge(t, Nat.add(pos, 1n+List.length(&2, JW.Jbd2Write, h))))

def Jc.lassoc(-A: Data, xs: List<&2, A>, +ys: List<&2, A>, +zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      Equal.cong(List<&2, A>, List<&2, A>, l => Con{x, l}, List.append(&2, A, List.append(&2, A, t, ys), zs), List.append(&2, A, t, List.append(&2, A, ys, zs)), Jc.lassoc(A, t, ys, zs))

def Jc.llen_app(-A: Data, xs: List<&2, A>, +ys: List<&2, A>) -> {List.length(&2, A, List.append(&2, A, xs, ys)) == Nat.add(List.length(&2, A, xs), List.length(&2, A, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, A, List.append(&2, A, t, ys)), Nat.add(List.length(&2, A, t), List.length(&2, A, ys)), Jc.llen_app(A, t, ys))

def Jc.len_datas(ws: List<&2, JW.Jbd2Write>, +g: J.Jbd2Geom, +s: U32, f: Bool, +q: Nat) -> {List.length(&2, JT.Ext4JStep, JT.Ext4JTx.datas(ws, g, s, f, q)) == List.length(&2, JW.Jbd2Write, ws) : Nat}:
  match ws:
    case Nil{}:
      {==}
    case Con{JW.Jbd2Write{+b, +d}, +t}:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, JT.Ext4JStep, JT.Ext4JTx.datas(t, g, s, False{}, Nat.add(q, 1n))), List.length(&2, JW.Jbd2Write, t), Jc.len_datas(t, g, s, False{}, Nat.add(q, 1n)))

def Jc.lend_len(gs: List<&2, List<&2, JW.Jbd2Write>>, +g: J.Jbd2Geom, +s: U32, +uuid: B.Octets, +pos: Nat) -> {Nat.add(pos, List.length(&2, JT.Ext4JStep, JT.Ext4JTx.logs(gs, g, s, uuid, pos))) == Jc.lend(gs, pos) : Nat}:
  match gs:
    case Nil{}:
      Jc.add_zero(pos)
    case Con{+h, +t}:
      +lh = {1n+List.length(&2, JW.Jbd2Write, h) : Nat}
      +p2 = Nat.add(pos, lh)
      +lt = List.length(&2, JT.Ext4JStep, JT.Ext4JTx.logs(t, g, s, uuid, p2))
      +gr = JT.Ext4JTx.group(h, g, s, uuid, pos)
      +lg = Equal.trans(Nat, List.length(&2, JT.Ext4JStep, List.append(&2, JT.Ext4JStep, gr, JT.Ext4JTx.logs(t, g, s, uuid, p2))), Nat.add(List.length(&2, JT.Ext4JStep, gr), lt), Nat.add(lh, lt), Jc.llen_app(JT.Ext4JStep, gr, JT.Ext4JTx.logs(t, g, s, uuid, p2)), Equal.cong(Nat, Nat, k => Nat.add(1n+k, lt), List.length(&2, JT.Ext4JStep, JT.Ext4JTx.datas(h, g, s, True{}, Nat.add(pos, 1n))), List.length(&2, JW.Jbd2Write, h), Jc.len_datas(h, g, s, True{}, Nat.add(pos, 1n))))
      Equal.trans(Nat, Nat.add(pos, List.length(&2, JT.Ext4JStep, JT.Ext4JTx.logs(Con{h, t}, g, s, uuid, pos))), Nat.add(pos, Nat.add(lh, lt)), Jc.lend(t, p2),
        Equal.cong(Nat, Nat, k => Nat.add(pos, k), List.length(&2, JT.Ext4JStep, JT.Ext4JTx.logs(Con{h, t}, g, s, uuid, pos)), Nat.add(lh, lt), lg),
        Equal.trans(Nat, Nat.add(pos, Nat.add(lh, lt)), Nat.add(p2, lt), Jc.lend(t, p2), Equal.sym(Nat, Nat.add(p2, lt), Nat.add(pos, Nat.add(lh, lt)), Jc.add_assoc(pos, lh, lt)), Jc.lend_len(t, g, s, uuid, p2)))

def Jc.recs_logs(gs: List<&2, List<&2, JW.Jbd2Write>>, +seq: Nat, +g: J.Jbd2Geom, +s: U32, +uuid: B.Octets, +pos: Nat) -> {JT.Ext4JTx.records(seq, JT.Ext4JTx.logs(gs, g, s, uuid, pos)) == Jc.drecs(gs, seq, g, s, pos) : List<&2, JL.Jbd2Rec>}:
  match gs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      +p2 = Nat.add(pos, 1n+List.length(&2, JW.Jbd2Write, h))
      +gr = JT.Ext4JTx.group(h, g, s, uuid, pos)
      +ds = JT.Ext4JTx.datas(h, g, s, True{}, Nat.add(pos, 1n))
      +rd = {JL.Jbd2RDesc{seq, JT.Ext4JTx.data_puts(ds)} : JL.Jbd2Rec}
      %Equal.sym(List<&2, JL.Jbd2Rec>, JT.Ext4JTx.records(seq, List.append(&2, JT.Ext4JStep, gr, JT.Ext4JTx.logs(t, g, s, uuid, p2))), List.append(&2, JL.Jbd2Rec, JT.Ext4JTx.records(seq, gr), JT.Ext4JTx.records(seq, JT.Ext4JTx.logs(t, g, s, uuid, p2))), Ext4Proof.records_app(seq, gr, JT.Ext4JTx.logs(t, g, s, uuid, p2))) : {_ == Jc.drecs(Con{h, t}, seq, g, s, pos) : List<&2, JL.Jbd2Rec>}
      %Equal.sym(List<&2, JL.Jbd2Rec>, JT.Ext4JTx.records(seq, ds), Nil{}, Ext4Proof.rec_datas(seq, h, g, s, True{}, Nat.add(pos, 1n))) : {List.append(&2, JL.Jbd2Rec, Con{rd, _}, JT.Ext4JTx.records(seq, JT.Ext4JTx.logs(t, g, s, uuid, p2))) == Jc.drecs(Con{h, t}, seq, g, s, pos) : List<&2, JL.Jbd2Rec>}
      Equal.cong(List<&2, JL.Jbd2Rec>, List<&2, JL.Jbd2Rec>, l => Con{rd, l}, JT.Ext4JTx.records(seq, JT.Ext4JTx.logs(t, g, s, uuid, p2)), Jc.drecs(t, seq, g, s, p2), Jc.recs_logs(t, seq, g, s, uuid, p2))

def Jc.feed_logs(gs: List<&2, List<&2, JW.Jbd2Write>>, +check: Bool, +g: J.Jbd2Geom, +uuid: B.Octets, +seq: Nat, +pos: Nat, +rs: List<&2, JL.Jbd2Rec>, +rest: List<&2, JT.Ext4JStep>) -> {Nat.is_eq(B.Octets.len(uuid), 16n) == True{} : Bool} -> {Nat.is_lt(0n, JB.Jbd2Desc.capacity(g)) == True{} : Bool} -> {Jc.chunks_ok(gs, JB.Jbd2Desc.capacity(g)) == True{} : Bool} -> {Jc.gfit(J.Jbd2Geom.wide(g), gs) == True{} : Bool} -> {Nat.is_lt(Jc.lend(gs, pos), J.Jbd2Geom.maxlen(g)) == True{} : Bool} -> {Laws.Ext4Laws.feed(List.append(&2, JT.Ext4JStep, JT.Ext4JTx.logs(gs, g, U32.from_nat(seq), uuid, pos), rest), check, g, JN.Jbd2Scan{pos, seq, rs, True{}, None{}}) == Laws.Ext4Laws.feed(rest, check, g, JN.Jbd2Scan{Jc.lend(gs, pos), seq, List.reverse.go(&2, JL.Jbd2Rec, Jc.drecs(gs, seq, g, U32.from_nat(seq), pos), rs), True{}, None{}}) : JN.Jbd2Scan}:
  match gs:
    case Nil{}:
      +hu => +hc => +hk => +hb => +hn => {==}
    case Con{+h, +t}:
      +hu => +hc => +hk => +hb => +hn =>
        +s = U32.from_nat(seq)
        +w = J.Jbd2Geom.wide(g)
        +cp = JB.Jbd2Desc.capacity(g)
        +lh = List.length(&2, JW.Jbd2Write, h)
        +p2 = Nat.add(pos, 1n+lh)
        +q = Nat.add(pos, 1n)
        +gr = JT.Ext4JTx.group(h, g, s, uuid, pos)
        +lt = JT.Ext4JTx.logs(t, g, s, uuid, p2)
        +rd = {JL.Jbd2RDesc{seq, JT.Ext4JTx.data_puts(JT.Ext4JTx.datas(h, g, s, True{}, q))} : JL.Jbd2Rec}
        +a1 = Nat.is_lt(0n, lh)
        +a2 = Nat.is_le(lh, cp)
        +a3 = Jc.chunks_ok(t, cp)
        +k23 = Ext4Proof.and_r(a1, Bool.and(a2, a3), hk)
        +bh = Ext4Proof.and_l(JT.Ext4JTx.blocks_fit(w, h), Jc.gfit(w, t), hb)
        +hz = Ext4Proof.and_l(a1, Bool.and(a2, a3), hk)
        +hfit = Jc.dfits(h, g, s, True{}, q, Jc.darea(g), bh, hz, Jc.gbound(g, h, hc, hz, Ext4Proof.and_l(a2, a3, k23)))
        +ea = Equal.trans(Nat, Jc.adv(h, q), Nat.add(q, lh), p2, Jc.adv_add(h, q), Jc.add_assoc(pos, 1n, lh))
        +hnw = Ext4Proof.le_lt_lt(Jc.adv(h, q), Jc.lend(t, p2), J.Jbd2Geom.maxlen(g), Jc.le_eql(Jc.adv(h, q), p2, Jc.lend(t, p2), ea, Jc.lend_ge(t, p2)), hn)
        %Equal.sym(List<&2, JT.Ext4JStep>, List.append(&2, JT.Ext4JStep, List.append(&2, JT.Ext4JStep, gr, lt), rest), List.append(&2, JT.Ext4JStep, gr, List.append(&2, JT.Ext4JStep, lt, rest)), Jc.lassoc(JT.Ext4JStep, gr, lt, rest)) : {Laws.Ext4Laws.feed(_, check, g, JN.Jbd2Scan{pos, seq, rs, True{}, None{}}) == Laws.Ext4Laws.feed(rest, check, g, JN.Jbd2Scan{Jc.lend(Con{h, t}, pos), seq, List.reverse.go(&2, JL.Jbd2Rec, Jc.drecs(Con{h, t}, seq, g, s, pos), rs), True{}, None{}}) : JN.Jbd2Scan}
        %Equal.sym(JN.Jbd2Scan, Laws.Ext4Laws.feed(List.append(&2, JT.Ext4JStep, gr, List.append(&2, JT.Ext4JStep, lt, rest)), check, g, JN.Jbd2Scan{pos, seq, rs, True{}, None{}}), Laws.Ext4Laws.feed(List.append(&2, JT.Ext4JStep, lt, rest), check, g, JN.Jbd2Scan{Jc.adv(h, q), seq, Con{rd, rs}, True{}, None{}}), Jc.feed_group(h, check, g, uuid, seq, pos, rs, List.append(&2, JT.Ext4JStep, lt, rest), hu, hfit, hnw)) : {_ == Laws.Ext4Laws.feed(rest, check, g, JN.Jbd2Scan{Jc.lend(Con{h, t}, pos), seq, List.reverse.go(&2, JL.Jbd2Rec, Jc.drecs(Con{h, t}, seq, g, s, pos), rs), True{}, None{}}) : JN.Jbd2Scan}
        %Equal.sym(Nat, Jc.adv(h, q), p2, ea) : {Laws.Ext4Laws.feed(List.append(&2, JT.Ext4JStep, lt, rest), check, g, JN.Jbd2Scan{_, seq, Con{rd, rs}, True{}, None{}}) == Laws.Ext4Laws.feed(rest, check, g, JN.Jbd2Scan{Jc.lend(Con{h, t}, pos), seq, List.reverse.go(&2, JL.Jbd2Rec, Jc.drecs(Con{h, t}, seq, g, s, pos), rs), True{}, None{}}) : JN.Jbd2Scan}
        Jc.feed_logs(t, check, g, uuid, seq, p2, Con{rd, rs}, rest, hu, hc, Ext4Proof.and_r(a2, a3, k23), Ext4Proof.and_r(JT.Ext4JTx.blocks_fit(w, h), Jc.gfit(w, t), hb), hn)

# The commit block, at the position the scanner has reached

def Jc.fc1(+check: Bool, +g: J.Jbd2Geom, +pc: Nat, +o: B.Octets, +st: JN.Jbd2Scan) -> {Laws.Ext4Laws.feed([JT.Ext4JCommit{pc, o}], check, g, st) == Laws.Ext4Laws.feed.at(Nat.is_eq(pc, JN.Jbd2Scan.pos(st)), check, g, st, o) : JN.Jbd2Scan}:
  {==}

def Jc.fc3(+check: Bool, +g: J.Jbd2Geom, +blk: B.Octets, +seq: Nat, +pos: Nat, +rs: List<&2, JL.Jbd2Rec>) -> {JN.Jbd2Scan.kind(U32.to_nat(2), check, g, blk, pos, seq, rs) == JN.Jbd2Scan.commit(JB.Jbd2Commit.ok(check, g, blk), g, pos, seq, rs) : JN.Jbd2Scan}:
  {==}

def Jc.feed_commit(+check: Bool, +g: J.Jbd2Geom, +seq: Nat, +sec: U32, +nsec: U32, +p: Nat, +pc: Nat, +rs: List<&2, JL.Jbd2Rec>, he: {Nat.is_eq(pc, p) == True{} : Bool}) -> {Laws.Ext4Laws.feed([JT.Ext4JCommit{pc, JB.Jbd2Commit.encode(g, U32.from_nat(seq), sec, nsec)}], check, g, JN.Jbd2Scan{p, seq, rs, True{}, None{}}) == JN.Jbd2Scan{J.Jbd2Geom.next(g, p), 1n+seq, Con{JL.Jbd2RCommit{seq}, rs}, True{}, None{}} : JN.Jbd2Scan}:
  +s = U32.from_nat(seq)
  +blk = JB.Jbd2Commit.encode(g, s, sec, nsec)
  +st = {JN.Jbd2Scan{p, seq, rs, True{}, None{}} : JN.Jbd2Scan}
  +rhs = {JN.Jbd2Scan{J.Jbd2Geom.next(g, p), 1n+seq, Con{JL.Jbd2RCommit{seq}, rs}, True{}, None{}} : JN.Jbd2Scan}
  %Equal.sym(JN.Jbd2Scan, Laws.Ext4Laws.feed([JT.Ext4JCommit{pc, blk}], check, g, st), Laws.Ext4Laws.feed.at(Nat.is_eq(pc, p), check, g, st, blk), Jc.fc1(check, g, pc, blk, st)) : {_ == rhs : JN.Jbd2Scan}
  %Equal.sym(Bool, Nat.is_eq(pc, p), True{}, he) : {Laws.Ext4Laws.feed.at(_, check, g, st, blk) == rhs : JN.Jbd2Scan}
  %Equal.sym(JN.Jbd2Scan, Laws.Ext4Laws.feed.at(True{}, check, g, st, blk), JN.Jbd2Scan.kind(U32.to_nat(JB.Jbd2Block.kind(blk, s)), check, g, blk, p, seq, rs), Jc.fg2(check, g, blk, seq, p, rs)) : {_ == rhs : JN.Jbd2Scan}
  %Equal.sym(U32, JB.Jbd2Block.kind(blk, s), 2, Laws.jcommit_kind(g, s, sec, nsec)) : {JN.Jbd2Scan.kind(U32.to_nat(_), check, g, blk, p, seq, rs) == rhs : JN.Jbd2Scan}
  %Equal.sym(JN.Jbd2Scan, JN.Jbd2Scan.kind(U32.to_nat(2), check, g, blk, p, seq, rs), JN.Jbd2Scan.commit(JB.Jbd2Commit.ok(check, g, blk), g, p, seq, rs), Jc.fc3(check, g, blk, seq, p, rs)) : {_ == rhs : JN.Jbd2Scan}
  %Equal.sym(Bool, JB.Jbd2Commit.ok(check, g, blk), True{}, Laws.jcommit_ok(check, g, s, sec, nsec)) : {JN.Jbd2Scan.commit(_, g, p, seq, rs) == rhs : JN.Jbd2Scan}
  {==}

# The plan's log, scanned

def Jc.tx_log(+g: J.Jbd2Geom, +uuid: B.Octets, +jsb: B.Octets, +seq: Nat, +m: JT.Jbd2Mode, +fresh: List<&2, Nat>, +ws: List<&2, JW.Jbd2Write>, +sec: U32, +nsec: U32) -> {Laws.Ext4Laws.log(Laws.Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)) == List.append(&2, JT.Ext4JStep, JT.Ext4JTx.logs(JT.Ext4JTx.chunks(JT.Ext4JTx.logged(m, fresh, J.Jbd2Geom.bs(g), ws), JT.Ext4JTx.cap(g)), g, U32.from_nat(seq), uuid, J.Jbd2Geom.first(g)), [JT.Ext4JCommit{Nat.add(J.Jbd2Geom.first(g), List.length(&2, JT.Ext4JStep, JT.Ext4JTx.logs(JT.Ext4JTx.chunks(JT.Ext4JTx.logged(m, fresh, J.Jbd2Geom.bs(g), ws), JT.Ext4JTx.cap(g)), g, U32.from_nat(seq), uuid, J.Jbd2Geom.first(g)))), JB.Jbd2Commit.encode(g, U32.from_nat(seq), sec, nsec)}]) : List<&2, JT.Ext4JStep>}:
  {==}

def Jc.tx_blocks(+g: J.Jbd2Geom, +uuid: B.Octets, +jsb: B.Octets, +seq: Nat, +m: JT.Jbd2Mode, +fresh: List<&2, Nat>, +ws: List<&2, JW.Jbd2Write>, +sec: U32, +nsec: U32) -> {JT.Ext4JTx.log_blocks(Laws.Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)) == 1n+List.length(&2, JT.Ext4JStep, JT.Ext4JTx.logs(JT.Ext4JTx.chunks(JT.Ext4JTx.logged(m, fresh, J.Jbd2Geom.bs(g), ws), JT.Ext4JTx.cap(g)), g, U32.from_nat(seq), uuid, J.Jbd2Geom.first(g))) : Nat}:
  {==}

def Jc.scan_start(+pos: Nat, +seq: Nat) -> {JN.Jbd2Scan.start(pos, seq) == JN.Jbd2Scan{pos, seq, Nil{}, True{}, None{}} : JN.Jbd2Scan}:
  {==}

def Jc.recs_go(+p: Nat, +s: Nat, +rs: List<&2, JL.Jbd2Rec>) -> {JN.Jbd2Scan.records(JN.Jbd2Scan{p, s, rs, True{}, None{}}) == List.reverse(&2, JL.Jbd2Rec, rs) : List<&2, JL.Jbd2Rec>}:
  {==}

def Laws.jtx_log_scan(check, g, uuid, jsb, seq, m, fresh, ws, sec, nsec, u, c, b, r):
  +s = U32.from_nat(seq)
  +w = J.Jbd2Geom.wide(g)
  +cp = JB.Jbd2Desc.capacity(g)
  +lg = JT.Ext4JTx.logged(m, fresh, J.Jbd2Geom.bs(g), ws)
  +gs = JT.Ext4JTx.chunks(lg, JT.Ext4JTx.cap(g))
  +f0 = J.Jbd2Geom.first(g)
  +lo = JT.Ext4JTx.logs(gs, g, s, uuid, f0)
  +ln = List.length(&2, JT.Ext4JStep, lo)
  +cm = {JT.Ext4JCommit{Nat.add(f0, ln), JB.Jbd2Commit.encode(g, s, sec, nsec)} : JT.Ext4JStep}
  +dr = Jc.drecs(gs, seq, g, s, f0)
  +p = Jc.lend(gs, f0)
  +rc = {JL.Jbd2RCommit{seq} : JL.Jbd2Rec}
  +ll = Jc.lend_len(gs, g, s, uuid, f0)
  +hok = Equal.trans(Bool, Jc.chunks_ok(gs, cp), Jc.chunks_ok(JT.Ext4JTx.chunks(lg, cp), cp), True{}, Equal.cong(Nat, Bool, k => Jc.chunks_ok(JT.Ext4JTx.chunks(lg, k), cp), JT.Ext4JTx.cap(g), cp, Jc.cap_eq(g, c)), Jc.ck_all(lg, cp, c))
  +hbf = Jc.gfit_concat(gs, w, Equal.trans(Bool, JT.Ext4JTx.blocks_fit(w, List.concat(&2, JW.Jbd2Write, gs)), JT.Ext4JTx.blocks_fit(w, lg), True{}, Equal.cong(List<&2, JW.Jbd2Write>, Bool, k => JT.Ext4JTx.blocks_fit(w, k), List.concat(&2, JW.Jbd2Write, gs), lg, Ext4Proof.chunks(lg, JT.Ext4JTx.cap(g))), Jc.bf_logged(m, fresh, J.Jbd2Geom.bs(g), ws, w, b)))
  +r2 = Jc.le_eql(1n+ln, JT.Ext4JTx.log_blocks(Laws.Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)), Nat.sub(J.Jbd2Geom.maxlen(g), f0), Equal.sym(Nat, JT.Ext4JTx.log_blocks(Laws.Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)), 1n+ln, Jc.tx_blocks(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)), r)
  +r3 = Jc.le_sub_add(f0, J.Jbd2Geom.maxlen(g), 1n+ln, {==}, r2)
  +r4 = Jc.le_succ_lt(Nat.add(f0, ln), J.Jbd2Geom.maxlen(g), Jc.le_eql(1n+Nat.add(f0, ln), Nat.add(f0, 1n+ln), J.Jbd2Geom.maxlen(g), Equal.sym(Nat, Nat.add(f0, 1n+ln), 1n+Nat.add(f0, ln), Jc.add_succ(f0, ln)), r3))
  +hn = Equal.trans(Bool, Nat.is_lt(p, J.Jbd2Geom.maxlen(g)), Nat.is_lt(Nat.add(f0, ln), J.Jbd2Geom.maxlen(g)), True{}, Equal.cong(Nat, Bool, k => Nat.is_lt(k, J.Jbd2Geom.maxlen(g)), p, Nat.add(f0, ln), Equal.sym(Nat, Nat.add(f0, ln), p, ll)), r4)
  +he = Equal.trans(Bool, Nat.is_eq(Nat.add(f0, ln), p), Nat.is_eq(p, p), True{}, Equal.cong(Nat, Bool, k => Nat.is_eq(k, p), Nat.add(f0, ln), p, ll), Ext4Proof.eq_refl(p))
  +st0 = {JN.Jbd2Scan{f0, seq, Nil{}, True{}, None{}} : JN.Jbd2Scan}
  +st1 = {JN.Jbd2Scan{p, seq, List.reverse.go(&2, JL.Jbd2Rec, dr, Nil{}), True{}, None{}} : JN.Jbd2Scan}
  +st2 = {JN.Jbd2Scan{J.Jbd2Geom.next(g, p), 1n+seq, Con{rc, List.reverse.go(&2, JL.Jbd2Rec, dr, Nil{})}, True{}, None{}} : JN.Jbd2Scan}
  +lgl = List.append(&2, JT.Ext4JStep, lo, [cm])
  %Equal.sym(List<&2, JT.Ext4JStep>, Laws.Ext4Laws.log(Laws.Ext4Laws.tx(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)), lgl, Jc.tx_log(g, uuid, jsb, seq, m, fresh, ws, sec, nsec)) : {JN.Jbd2Scan.records(Laws.Ext4Laws.feed(_, check, g, JN.Jbd2Scan.start(f0, seq))) == JT.Ext4JTx.records(seq, _) : List<&2, JL.Jbd2Rec>}
  %Equal.sym(JN.Jbd2Scan, JN.Jbd2Scan.start(f0, seq), st0, Jc.scan_start(f0, seq)) : {JN.Jbd2Scan.records(Laws.Ext4Laws.feed(lgl, check, g, _)) == JT.Ext4JTx.records(seq, lgl) : List<&2, JL.Jbd2Rec>}
  %Equal.sym(JN.Jbd2Scan, Laws.Ext4Laws.feed(lgl, check, g, st0), Laws.Ext4Laws.feed([cm], check, g, st1), Jc.feed_logs(gs, check, g, uuid, seq, f0, Nil{}, [cm], u, c, hok, hbf, hn)) : {JN.Jbd2Scan.records(_) == JT.Ext4JTx.records(seq, lgl) : List<&2, JL.Jbd2Rec>}
  %Equal.sym(JN.Jbd2Scan, Laws.Ext4Laws.feed([cm], check, g, st1), st2, Jc.feed_commit(check, g, seq, sec, nsec, p, Nat.add(f0, ln), List.reverse.go(&2, JL.Jbd2Rec, dr, Nil{}), he)) : {JN.Jbd2Scan.records(_) == JT.Ext4JTx.records(seq, lgl) : List<&2, JL.Jbd2Rec>}
  %Equal.sym(List<&2, JL.Jbd2Rec>, JN.Jbd2Scan.records(st2), List.reverse(&2, JL.Jbd2Rec, Con{rc, List.reverse.go(&2, JL.Jbd2Rec, dr, Nil{})}), Jc.recs_go(J.Jbd2Geom.next(g, p), 1n+seq, Con{rc, List.reverse.go(&2, JL.Jbd2Rec, dr, Nil{})})) : {_ == JT.Ext4JTx.records(seq, lgl) : List<&2, JL.Jbd2Rec>}
  %Equal.sym(List<&2, JL.Jbd2Rec>, JT.Ext4JTx.records(seq, lgl), List.append(&2, JL.Jbd2Rec, JT.Ext4JTx.records(seq, lo), JT.Ext4JTx.records(seq, [cm])), Ext4Proof.records_app(seq, lo, [cm])) : {List.reverse(&2, JL.Jbd2Rec, Con{rc, List.reverse.go(&2, JL.Jbd2Rec, dr, Nil{})}) == _ : List<&2, JL.Jbd2Rec>}
  %Equal.sym(List<&2, JL.Jbd2Rec>, JT.Ext4JTx.records(seq, lo), dr, Jc.recs_logs(gs, seq, g, s, uuid, f0)) : {List.reverse(&2, JL.Jbd2Rec, Con{rc, List.reverse.go(&2, JL.Jbd2Rec, dr, Nil{})}) == List.append(&2, JL.Jbd2Rec, _, [rc]) : List<&2, JL.Jbd2Rec>}
  Ext4Proof.rev_rev(JL.Jbd2Rec, dr, Nil{}, [rc])

def Laws.jsuper_log_witness():
  {==}

def Laws.jdesc_round_trip_witness():
  {==}

def Laws.jrevoke_round_trip_witness():
  {==}

def Laws.jtx_log_scan_witness():
  {==}

# The needs_recovery mark and clear: the superblock's incompat field
# patched, then (metadata_csum) the checksum resealed

def Jc.le32_head(+v: U32, +r: B.Octets) -> {B.Octets.le32_at(B.Octets.append(B.Octets.le32(v), r), 0n) == Some{v} : Maybe<&2, U32>}:
  Equal.trans(Maybe<&2, U32>, B.Octets.le32_at(B.Octets.append(B.Octets.le32(v), r), 0n), B.Octets.le32_at(B.Octets.le32(v), 0n), Some{v},
    BL.octets_le32_at_append_le(B.Octets.le32(v), r, 0n, Equal.cong(Nat, Bool, k => Nat.is_le(4n, k), B.Octets.len(B.Octets.le32(v)), 4n, BL.octets_len_le32(v))),
    BL.octets_le32_round_trip(v))

def Jc.swnew(+sb: B.Octets, +set: U32, +clear: U32) -> U32:
  U32.and(U32.or(Maybe.default(&2, U32, B.Octets.le32_at(sb, 96n), 0), set), U32.not(clear))

def Jc.swx(+sb: B.Octets, +set: U32, +clear: U32) -> B.Octets:
  B.Octets.append(B.Octets.take(96n, sb), B.Octets.append(B.Octets.le32(Jc.swnew(sb, set, clear)), B.Octets.drop(100n, sb)))

def Jc.sw_shape(+sb: B.Octets, +set: U32, +clear: U32) -> {DW.Ext4Dev.super_with(sb, set, clear) == DW.Ext4Dev.super_with.seal(XS.Ext2Super.has_ro_compat(XS.Ext2Super.parse(Jc.swx(sb, set, clear)), XS.Ext2Super.ro_compat_metadata_csum()), Jc.swx(sb, set, clear)) : B.Octets}:
  {==}

def Jc.sws_t(+x: B.Octets) -> {DW.Ext4Dev.super_with.seal(True{}, x) == B.Octets.append(B.Octets.take(1020n, x), B.Octets.le32(K.Ext2Csum.super(x))) : B.Octets}:
  {==}

def Jc.sws_f(+x: B.Octets) -> {DW.Ext4Dev.super_with.seal(False{}, x) == x : B.Octets}:
  {==}

def Jc.esup(+x: B.Octets) -> {K.Ext2Csum.super(x) == K.Ext2Csum.crc32c(4294967295, B.Octets.take(1020n, x)) : U32}:
  {==}

# the lengths of the patched superblock's parts
def Jc.lt96(+sb: B.Octets, +hl: {B.Octets.len(sb) == 1024n : Nat}) -> {B.Octets.len(B.Octets.take(96n, sb)) == 96n : Nat}:
  BL.octets_len_take_le(96n, sb, Jc.le_eq(96n, B.Octets.len(sb), 1024n, hl, {==}))

def Jc.swx_len(+sb: B.Octets, +set: U32, +clear: U32, +hl: {B.Octets.len(sb) == 1024n : Nat}) -> {B.Octets.len(Jc.swx(sb, set, clear)) == 1024n : Nat}:
  +d = B.Octets.drop(100n, sb)
  +ld = Equal.trans(Nat, B.Octets.len(d), Nat.sub(B.Octets.len(sb), 100n), 924n, BL.octets_len_drop(100n, sb), Equal.cong(Nat, Nat, k => Nat.sub(k, 100n), B.Octets.len(sb), 1024n, hl))
  Jc.len2(B.Octets.take(96n, sb), B.Octets.append(B.Octets.le32(Jc.swnew(sb, set, clear)), d), 96n, 928n, Jc.lt96(sb, hl), Jc.len2(B.Octets.le32(Jc.swnew(sb, set, clear)), d, 4n, 924n, BL.octets_len_le32(Jc.swnew(sb, set, clear)), ld))

def Jc.t1020(+x: B.Octets, +hx: {B.Octets.len(x) == 1024n : Nat}) -> {B.Octets.len(B.Octets.take(1020n, x)) == 1020n : Nat}:
  BL.octets_len_take_le(1020n, x, Jc.le_eq(1020n, B.Octets.len(x), 1024n, hx, {==}))

def Jc.sw_len_b(b: Bool, +x: B.Octets, +hx: {B.Octets.len(x) == 1024n : Nat}) -> {B.Octets.len(DW.Ext4Dev.super_with.seal(b, x)) == 1024n : Nat}:
  match b:
    case True{}:
      %Equal.sym(B.Octets, DW.Ext4Dev.super_with.seal(True{}, x), B.Octets.append(B.Octets.take(1020n, x), B.Octets.le32(K.Ext2Csum.super(x))), Jc.sws_t(x)) : {B.Octets.len(_) == 1024n : Nat}
      Jc.len2(B.Octets.take(1020n, x), B.Octets.le32(K.Ext2Csum.super(x)), 1020n, 4n, Jc.t1020(x, hx), BL.octets_len_le32(K.Ext2Csum.super(x)))
    case False{}:
      %Equal.sym(B.Octets, DW.Ext4Dev.super_with.seal(False{}, x), x, Jc.sws_f(x)) : {B.Octets.len(_) == 1024n : Nat}
      hx

def Laws.super_with_len(sb, set, clear, h):
  +x = Jc.swx(sb, set, clear)
  +hl = Ext4Proof.eq_sound(B.Octets.len(sb), 1024n, h)
  %Equal.sym(B.Octets, DW.Ext4Dev.super_with(sb, set, clear), DW.Ext4Dev.super_with.seal(XS.Ext2Super.has_ro_compat(XS.Ext2Super.parse(x), XS.Ext2Super.ro_compat_metadata_csum()), x), Jc.sw_shape(sb, set, clear)) : {B.Octets.len(_) == 1024n : Nat}
  Jc.sw_len_b(XS.Ext2Super.has_ro_compat(XS.Ext2Super.parse(x), XS.Ext2Super.ro_compat_metadata_csum()), x, Jc.swx_len(sb, set, clear, hl))

# s_feature_incompat
def Jc.swx96(+sb: B.Octets, +set: U32, +clear: U32, +hl: {B.Octets.len(sb) == 1024n : Nat}) -> {B.Octets.le32_at(Jc.swx(sb, set, clear), 96n) == Some{Jc.swnew(sb, set, clear)} : Maybe<&2, U32>}:
  +t = B.Octets.take(96n, sb)
  +y = B.Octets.append(B.Octets.le32(Jc.swnew(sb, set, clear)), B.Octets.drop(100n, sb))
  %Equal.trans(Nat, Nat.add(B.Octets.len(t), 0n), B.Octets.len(t), 96n, Jc.add_zero(B.Octets.len(t)), Jc.lt96(sb, hl)) : {B.Octets.le32_at(B.Octets.append(t, y), _) == Some{Jc.swnew(sb, set, clear)} : Maybe<&2, U32>}
  %Equal.sym(Maybe<&2, U32>, B.Octets.le32_at(B.Octets.append(t, y), Nat.add(B.Octets.len(t), 0n)), B.Octets.le32_at(y, 0n), BL.octets_le32_at_append_add(t, y, 0n)) : {_ == Some{Jc.swnew(sb, set, clear)} : Maybe<&2, U32>}
  Jc.le32_head(Jc.swnew(sb, set, clear), B.Octets.drop(100n, sb))

def Jc.sw96_b(b: Bool, +sb: B.Octets, +set: U32, +clear: U32, +hl: {B.Octets.len(sb) == 1024n : Nat}) -> {B.Octets.le32_at(DW.Ext4Dev.super_with.seal(b, Jc.swx(sb, set, clear)), 96n) == Some{Jc.swnew(sb, set, clear)} : Maybe<&2, U32>}:
  match b:
    case True{}:
      +x = Jc.swx(sb, set, clear)
      +t = B.Octets.take(1020n, x)
      +q = B.Octets.le32(K.Ext2Csum.super(x))
      %Equal.sym(B.Octets, DW.Ext4Dev.super_with.seal(True{}, x), B.Octets.append(t, q), Jc.sws_t(x)) : {B.Octets.le32_at(_, 96n) == Some{Jc.swnew(sb, set, clear)} : Maybe<&2, U32>}
      %Equal.sym(Maybe<&2, U32>, B.Octets.le32_at(B.Octets.append(t, q), 96n), B.Octets.le32_at(t, 96n), BL.octets_le32_at_append_le(t, q, 96n, Jc.le_eq(100n, B.Octets.len(t), 1020n, Jc.t1020(x, Jc.swx_len(sb, set, clear, hl)), {==}))) : {_ == Some{Jc.swnew(sb, set, clear)} : Maybe<&2, U32>}
      %Equal.sym(Maybe<&2, U32>, B.Octets.le32_at(t, 96n), B.Octets.le32_at(x, 96n), BL.octets_le32_at_take(1020n, x, 96n, {==})) : {_ == Some{Jc.swnew(sb, set, clear)} : Maybe<&2, U32>}
      Jc.swx96(sb, set, clear, hl)
    case False{}:
      %Equal.sym(B.Octets, DW.Ext4Dev.super_with.seal(False{}, Jc.swx(sb, set, clear)), Jc.swx(sb, set, clear), Jc.sws_f(Jc.swx(sb, set, clear))) : {B.Octets.le32_at(_, 96n) == Some{Jc.swnew(sb, set, clear)} : Maybe<&2, U32>}
      Jc.swx96(sb, set, clear, hl)

def Laws.super_with_incompat(sb, set, clear, h):
  +x = Jc.swx(sb, set, clear)
  %Equal.sym(B.Octets, DW.Ext4Dev.super_with(sb, set, clear), DW.Ext4Dev.super_with.seal(XS.Ext2Super.has_ro_compat(XS.Ext2Super.parse(x), XS.Ext2Super.ro_compat_metadata_csum()), x), Jc.sw_shape(sb, set, clear)) : {B.Octets.le32_at(_, 96n) == Some{Jc.swnew(sb, set, clear)} : Maybe<&2, U32>}
  Jc.sw96_b(XS.Ext2Super.has_ro_compat(XS.Ext2Super.parse(x), XS.Ext2Super.ro_compat_metadata_csum()), sb, set, clear, Ext4Proof.eq_sound(B.Octets.len(sb), 1024n, h))

# the bytes before the field
def Jc.swx_head(+sb: B.Octets, +set: U32, +clear: U32, +hl: {B.Octets.len(sb) == 1024n : Nat}) -> {B.Octets.slice(0n, 96n, Jc.swx(sb, set, clear)) == B.Octets.slice(0n, 96n, sb) : B.Octets}:
  +t = B.Octets.take(96n, sb)
  +y = B.Octets.append(B.Octets.le32(Jc.swnew(sb, set, clear)), B.Octets.drop(100n, sb))
  Equal.trans(B.Octets, B.Octets.slice(0n, 96n, B.Octets.append(t, y)), B.Octets.slice(0n, 96n, t), B.Octets.slice(0n, 96n, sb),
    BL.octets_slice_append_le(0n, 96n, t, y, Jc.le_eq(96n, B.Octets.len(t), 96n, Jc.lt96(sb, hl), {==})),
    BL.octets_slice_take(96n, 0n, 96n, sb, {==}))

def Jc.swhead_b(b: Bool, +sb: B.Octets, +set: U32, +clear: U32, +hl: {B.Octets.len(sb) == 1024n : Nat}) -> {B.Octets.slice(0n, 96n, DW.Ext4Dev.super_with.seal(b, Jc.swx(sb, set, clear))) == B.Octets.slice(0n, 96n, sb) : B.Octets}:
  match b:
    case True{}:
      +x = Jc.swx(sb, set, clear)
      +t = B.Octets.take(1020n, x)
      +q = B.Octets.le32(K.Ext2Csum.super(x))
      %Equal.sym(B.Octets, DW.Ext4Dev.super_with.seal(True{}, x), B.Octets.append(t, q), Jc.sws_t(x)) : {B.Octets.slice(0n, 96n, _) == B.Octets.slice(0n, 96n, sb) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.slice(0n, 96n, B.Octets.append(t, q)), B.Octets.slice(0n, 96n, t), BL.octets_slice_append_le(0n, 96n, t, q, Jc.le_eq(96n, B.Octets.len(t), 1020n, Jc.t1020(x, Jc.swx_len(sb, set, clear, hl)), {==}))) : {_ == B.Octets.slice(0n, 96n, sb) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.slice(0n, 96n, t), B.Octets.slice(0n, 96n, x), BL.octets_slice_take(1020n, 0n, 96n, x, {==})) : {_ == B.Octets.slice(0n, 96n, sb) : B.Octets}
      Jc.swx_head(sb, set, clear, hl)
    case False{}:
      %Equal.sym(B.Octets, DW.Ext4Dev.super_with.seal(False{}, Jc.swx(sb, set, clear)), Jc.swx(sb, set, clear), Jc.sws_f(Jc.swx(sb, set, clear))) : {B.Octets.slice(0n, 96n, _) == B.Octets.slice(0n, 96n, sb) : B.Octets}
      Jc.swx_head(sb, set, clear, hl)

def Laws.super_with_head(sb, set, clear, h):
  +x = Jc.swx(sb, set, clear)
  %Equal.sym(B.Octets, DW.Ext4Dev.super_with(sb, set, clear), DW.Ext4Dev.super_with.seal(XS.Ext2Super.has_ro_compat(XS.Ext2Super.parse(x), XS.Ext2Super.ro_compat_metadata_csum()), x), Jc.sw_shape(sb, set, clear)) : {B.Octets.slice(0n, 96n, _) == B.Octets.slice(0n, 96n, sb) : B.Octets}
  Jc.swhead_b(XS.Ext2Super.has_ro_compat(XS.Ext2Super.parse(x), XS.Ext2Super.ro_compat_metadata_csum()), sb, set, clear, Ext4Proof.eq_sound(B.Octets.len(sb), 1024n, h))

# the bytes after the field: the superblock's, from byte 100 on
def Jc.swx_from(+sb: B.Octets, +set: U32, +clear: U32, +k: Nat, +n: Nat, +hl: {B.Octets.len(sb) == 1024n : Nat}) -> {B.Octets.slice(Nat.add(100n, k), n, Jc.swx(sb, set, clear)) == B.Octets.slice(Nat.add(100n, k), n, sb) : B.Octets}:
  +t = B.Octets.take(96n, sb)
  +l4 = B.Octets.le32(Jc.swnew(sb, set, clear))
  +d = B.Octets.drop(100n, sb)
  +e = Equal.trans(Nat, Nat.add(B.Octets.len(t), Nat.add(B.Octets.len(l4), k)), Nat.add(96n, Nat.add(B.Octets.len(l4), k)), Nat.add(96n, Nat.add(4n, k)), Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(B.Octets.len(l4), k)), B.Octets.len(t), 96n, Jc.lt96(sb, hl)), Equal.cong(Nat, Nat, z => Nat.add(96n, Nat.add(z, k)), B.Octets.len(l4), 4n, BL.octets_len_le32(Jc.swnew(sb, set, clear))))
  %e : {B.Octets.slice(_, n, B.Octets.append(t, B.Octets.append(l4, d))) == B.Octets.slice(Nat.add(100n, k), n, sb) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.slice(Nat.add(B.Octets.len(t), Nat.add(B.Octets.len(l4), k)), n, B.Octets.append(t, B.Octets.append(l4, d))), B.Octets.slice(Nat.add(B.Octets.len(l4), k), n, B.Octets.append(l4, d)), BL.octets_slice_append_add(t, Nat.add(B.Octets.len(l4), k), n, B.Octets.append(l4, d))) : {_ == B.Octets.slice(Nat.add(100n, k), n, sb) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.slice(Nat.add(B.Octets.len(l4), k), n, B.Octets.append(l4, d)), B.Octets.slice(k, n, d), BL.octets_slice_append_add(l4, k, n, d)) : {_ == B.Octets.slice(Nat.add(100n, k), n, sb) : B.Octets}
  BL.octets_slice_drop(100n, k, n, sb)

def Jc.swbody_b(b: Bool, +sb: B.Octets, +set: U32, +clear: U32, +hl: {B.Octets.len(sb) == 1024n : Nat}) -> {B.Octets.slice(100n, 920n, DW.Ext4Dev.super_with.seal(b, Jc.swx(sb, set, clear))) == B.Octets.slice(100n, 920n, sb) : B.Octets}:
  match b:
    case True{}:
      +x = Jc.swx(sb, set, clear)
      +t = B.Octets.take(1020n, x)
      +q = B.Octets.le32(K.Ext2Csum.super(x))
      %Equal.sym(B.Octets, DW.Ext4Dev.super_with.seal(True{}, x), B.Octets.append(t, q), Jc.sws_t(x)) : {B.Octets.slice(100n, 920n, _) == B.Octets.slice(100n, 920n, sb) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.slice(100n, 920n, B.Octets.append(t, q)), B.Octets.slice(100n, 920n, t), BL.octets_slice_append_le(100n, 920n, t, q, Jc.le_eq(1020n, B.Octets.len(t), 1020n, Jc.t1020(x, Jc.swx_len(sb, set, clear, hl)), {==}))) : {_ == B.Octets.slice(100n, 920n, sb) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.slice(100n, 920n, t), B.Octets.slice(100n, 920n, x), BL.octets_slice_take(1020n, 100n, 920n, x, {==})) : {_ == B.Octets.slice(100n, 920n, sb) : B.Octets}
      Jc.swx_from(sb, set, clear, 0n, 920n, hl)
    case False{}:
      %Equal.sym(B.Octets, DW.Ext4Dev.super_with.seal(False{}, Jc.swx(sb, set, clear)), Jc.swx(sb, set, clear), Jc.sws_f(Jc.swx(sb, set, clear))) : {B.Octets.slice(100n, 920n, _) == B.Octets.slice(100n, 920n, sb) : B.Octets}
      Jc.swx_from(sb, set, clear, 0n, 920n, hl)

def Laws.super_with_body(sb, set, clear, h):
  +x = Jc.swx(sb, set, clear)
  %Equal.sym(B.Octets, DW.Ext4Dev.super_with(sb, set, clear), DW.Ext4Dev.super_with.seal(XS.Ext2Super.has_ro_compat(XS.Ext2Super.parse(x), XS.Ext2Super.ro_compat_metadata_csum()), x), Jc.sw_shape(sb, set, clear)) : {B.Octets.slice(100n, 920n, _) == B.Octets.slice(100n, 920n, sb) : B.Octets}
  Jc.swbody_b(XS.Ext2Super.has_ro_compat(XS.Ext2Super.parse(x), XS.Ext2Super.ro_compat_metadata_csum()), sb, set, clear, Ext4Proof.eq_sound(B.Octets.len(sb), 1024n, h))

# the checksum field: resealed, or untouched
def Jc.or_t_r(+a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def Jc.swtail_t(+x: B.Octets, +sb: B.Octets, +hx: {B.Octets.len(x) == 1024n : Nat}) -> {Bool.or(U32.is_eq(Maybe.default(&2, U32, B.Octets.le32_at(DW.Ext4Dev.super_with.seal(True{}, x), 1020n), 0), K.Ext2Csum.super(DW.Ext4Dev.super_with.seal(True{}, x))), B.Octets.is_eq(B.Octets.slice(1020n, 4n, DW.Ext4Dev.super_with.seal(True{}, x)), B.Octets.slice(1020n, 4n, sb))) == True{} : Bool}:
  +t = B.Octets.take(1020n, x)
  +c = K.Ext2Csum.super(x)
  +q = B.Octets.le32(c)
  +y = B.Octets.append(t, q)
  +lt = Jc.t1020(x, hx)
  %Equal.sym(B.Octets, DW.Ext4Dev.super_with.seal(True{}, x), y, Jc.sws_t(x)) : {Bool.or(U32.is_eq(Maybe.default(&2, U32, B.Octets.le32_at(_, 1020n), 0), K.Ext2Csum.super(_)), B.Octets.is_eq(B.Octets.slice(1020n, 4n, _), B.Octets.slice(1020n, 4n, sb))) == True{} : Bool}
  %Equal.trans(Nat, Nat.add(B.Octets.len(t), 0n), B.Octets.len(t), 1020n, Jc.add_zero(B.Octets.len(t)), lt) : {Bool.or(U32.is_eq(Maybe.default(&2, U32, B.Octets.le32_at(y, _), 0), K.Ext2Csum.super(y)), B.Octets.is_eq(B.Octets.slice(1020n, 4n, y), B.Octets.slice(1020n, 4n, sb))) == True{} : Bool}
  %Equal.sym(Maybe<&2, U32>, B.Octets.le32_at(y, Nat.add(B.Octets.len(t), 0n)), B.Octets.le32_at(q, 0n), BL.octets_le32_at_append_add(t, q, 0n)) : {Bool.or(U32.is_eq(Maybe.default(&2, U32, _, 0), K.Ext2Csum.super(y)), B.Octets.is_eq(B.Octets.slice(1020n, 4n, y), B.Octets.slice(1020n, 4n, sb))) == True{} : Bool}
  %Equal.sym(Maybe<&2, U32>, B.Octets.le32_at(q, 0n), Some{c}, BL.octets_le32_round_trip(c)) : {Bool.or(U32.is_eq(Maybe.default(&2, U32, _, 0), K.Ext2Csum.super(y)), B.Octets.is_eq(B.Octets.slice(1020n, 4n, y), B.Octets.slice(1020n, 4n, sb))) == True{} : Bool}
  %Equal.sym(U32, K.Ext2Csum.super(y), K.Ext2Csum.crc32c(4294967295, B.Octets.take(1020n, y)), Jc.esup(y)) : {Bool.or(U32.is_eq(c, _), B.Octets.is_eq(B.Octets.slice(1020n, 4n, y), B.Octets.slice(1020n, 4n, sb))) == True{} : Bool}
  %lt : {Bool.or(U32.is_eq(c, K.Ext2Csum.crc32c(4294967295, B.Octets.take(_, y))), B.Octets.is_eq(B.Octets.slice(1020n, 4n, y), B.Octets.slice(1020n, 4n, sb))) == True{} : Bool}
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(t), y), t, BL.octets_take_append(t, q)) : {Bool.or(U32.is_eq(c, K.Ext2Csum.crc32c(4294967295, _)), B.Octets.is_eq(B.Octets.slice(1020n, 4n, y), B.Octets.slice(1020n, 4n, sb))) == True{} : Bool}
  %Equal.sym(Bool, U32.is_eq(c, c), True{}, Jc.u32_refl(c)) : {Bool.or(_, B.Octets.is_eq(B.Octets.slice(1020n, 4n, y), B.Octets.slice(1020n, 4n, sb))) == True{} : Bool}
  {==}

def Jc.swtail_f(+sb: B.Octets, +set: U32, +clear: U32, +hl: {B.Octets.len(sb) == 1024n : Nat}) -> {Bool.or(U32.is_eq(Maybe.default(&2, U32, B.Octets.le32_at(DW.Ext4Dev.super_with.seal(False{}, Jc.swx(sb, set, clear)), 1020n), 0), K.Ext2Csum.super(DW.Ext4Dev.super_with.seal(False{}, Jc.swx(sb, set, clear)))), B.Octets.is_eq(B.Octets.slice(1020n, 4n, DW.Ext4Dev.super_with.seal(False{}, Jc.swx(sb, set, clear))), B.Octets.slice(1020n, 4n, sb))) == True{} : Bool}:
  +x = Jc.swx(sb, set, clear)
  %Equal.sym(B.Octets, DW.Ext4Dev.super_with.seal(False{}, x), x, Jc.sws_f(x)) : {Bool.or(U32.is_eq(Maybe.default(&2, U32, B.Octets.le32_at(_, 1020n), 0), K.Ext2Csum.super(_)), B.Octets.is_eq(B.Octets.slice(1020n, 4n, _), B.Octets.slice(1020n, 4n, sb))) == True{} : Bool}
  %Equal.sym(B.Octets, B.Octets.slice(Nat.add(100n, 920n), 4n, x), B.Octets.slice(Nat.add(100n, 920n), 4n, sb), Jc.swx_from(sb, set, clear, 920n, 4n, hl)) : {Bool.or(U32.is_eq(Maybe.default(&2, U32, B.Octets.le32_at(x, 1020n), 0), K.Ext2Csum.super(x)), B.Octets.is_eq(_, B.Octets.slice(1020n, 4n, sb))) == True{} : Bool}
  %Equal.sym(Bool, B.Octets.is_eq(B.Octets.slice(1020n, 4n, sb), B.Octets.slice(1020n, 4n, sb)), True{}, BL.octets_is_eq_refl(B.Octets.slice(1020n, 4n, sb))) : {Bool.or(U32.is_eq(Maybe.default(&2, U32, B.Octets.le32_at(x, 1020n), 0), K.Ext2Csum.super(x)), _) == True{} : Bool}
  Jc.or_t_r(U32.is_eq(Maybe.default(&2, U32, B.Octets.le32_at(x, 1020n), 0), K.Ext2Csum.super(x)))

def Jc.swtail_b(b: Bool, +sb: B.Octets, +set: U32, +clear: U32, +hl: {B.Octets.len(sb) == 1024n : Nat}) -> {Bool.or(U32.is_eq(Maybe.default(&2, U32, B.Octets.le32_at(DW.Ext4Dev.super_with.seal(b, Jc.swx(sb, set, clear)), 1020n), 0), K.Ext2Csum.super(DW.Ext4Dev.super_with.seal(b, Jc.swx(sb, set, clear)))), B.Octets.is_eq(B.Octets.slice(1020n, 4n, DW.Ext4Dev.super_with.seal(b, Jc.swx(sb, set, clear))), B.Octets.slice(1020n, 4n, sb))) == True{} : Bool}:
  match b:
    case True{}:
      Jc.swtail_t(Jc.swx(sb, set, clear), sb, Jc.swx_len(sb, set, clear, hl))
    case False{}:
      Jc.swtail_f(sb, set, clear, hl)

def Laws.super_with_tail(sb, set, clear, h):
  +x = Jc.swx(sb, set, clear)
  +sw = DW.Ext4Dev.super_with.seal(XS.Ext2Super.has_ro_compat(XS.Ext2Super.parse(x), XS.Ext2Super.ro_compat_metadata_csum()), x)
  %Equal.sym(B.Octets, DW.Ext4Dev.super_with(sb, set, clear), sw, Jc.sw_shape(sb, set, clear)) : {Bool.or(U32.is_eq(Maybe.default(&2, U32, B.Octets.le32_at(_, 1020n), 0), K.Ext2Csum.super(_)), B.Octets.is_eq(B.Octets.slice(1020n, 4n, _), B.Octets.slice(1020n, 4n, sb))) == True{} : Bool}
  Jc.swtail_b(XS.Ext2Super.has_ro_compat(XS.Ext2Super.parse(x), XS.Ext2Super.ro_compat_metadata_csum()), sb, set, clear, Ext4Proof.eq_sound(B.Octets.len(sb), 1024n, h))

# The plan's mark: the logged copy of the superblock's block

def Jc.mk_shape(+bs: Nat, +d: B.Octets) -> {Laws.Ext4Laws.marked(bs, d) == JT.Ext4JTx.mark.at(Nat.is_eq(JT.Ext4JTx.super_block(bs), JT.Ext4JTx.super_block(bs)), bs, d) : B.Octets}:
  {==}

def Jc.mkt(+bs: Nat, +d: B.Octets) -> {JT.Ext4JTx.mark.at(True{}, bs, d) == B.Octets.append(B.Octets.take(JT.Ext4JTx.super_off(bs), d), B.Octets.append(DW.Ext4Dev.super_with(B.Octets.slice(JT.Ext4JTx.super_off(bs), 1024n, d), S.Ext4Super.incompat_recover(), 0), B.Octets.drop(Nat.add(JT.Ext4JTx.super_off(bs), 1024n), d))) : B.Octets}:
  {==}

# the marked block, its pieces' lengths
def Jc.mk_eq(+bs: Nat, +d: B.Octets) -> {Laws.Ext4Laws.marked(bs, d) == B.Octets.append(B.Octets.take(JT.Ext4JTx.super_off(bs), d), B.Octets.append(DW.Ext4Dev.super_with(B.Octets.slice(JT.Ext4JTx.super_off(bs), 1024n, d), S.Ext4Super.incompat_recover(), 0), B.Octets.drop(Nat.add(JT.Ext4JTx.super_off(bs), 1024n), d))) : B.Octets}:
  +sbk = JT.Ext4JTx.super_block(bs)
  %Equal.sym(B.Octets, Laws.Ext4Laws.marked(bs, d), JT.Ext4JTx.mark.at(Nat.is_eq(sbk, sbk), bs, d), Jc.mk_shape(bs, d)) : {_ == B.Octets.append(B.Octets.take(JT.Ext4JTx.super_off(bs), d), B.Octets.append(DW.Ext4Dev.super_with(B.Octets.slice(JT.Ext4JTx.super_off(bs), 1024n, d), S.Ext4Super.incompat_recover(), 0), B.Octets.drop(Nat.add(JT.Ext4JTx.super_off(bs), 1024n), d))) : B.Octets}
  %Equal.sym(Bool, Nat.is_eq(sbk, sbk), True{}, Ext4Proof.eq_refl(sbk)) : {JT.Ext4JTx.mark.at(_, bs, d) == B.Octets.append(B.Octets.take(JT.Ext4JTx.super_off(bs), d), B.Octets.append(DW.Ext4Dev.super_with(B.Octets.slice(JT.Ext4JTx.super_off(bs), 1024n, d), S.Ext4Super.incompat_recover(), 0), B.Octets.drop(Nat.add(JT.Ext4JTx.super_off(bs), 1024n), d))) : B.Octets}
  Jc.mkt(bs, d)

def Jc.mk_lsw(+bs: Nat, +d: B.Octets, +h: {Nat.is_le(Nat.add(JT.Ext4JTx.super_off(bs), 1024n), B.Octets.len(d)) == True{} : Bool}) -> {B.Octets.len(DW.Ext4Dev.super_with(B.Octets.slice(JT.Ext4JTx.super_off(bs), 1024n, d), S.Ext4Super.incompat_recover(), 0)) == 1024n : Nat}:
  +sl = B.Octets.slice(JT.Ext4JTx.super_off(bs), 1024n, d)
  Laws.super_with_len(sl, S.Ext4Super.incompat_recover(), 0, Equal.trans(Bool, Nat.is_eq(B.Octets.len(sl), 1024n), Nat.is_eq(1024n, 1024n), True{}, Equal.cong(Nat, Bool, k => Nat.is_eq(k, 1024n), B.Octets.len(sl), 1024n, BL.octets_len_slice_le(JT.Ext4JTx.super_off(bs), 1024n, d, h)), {==}))

def Laws.jtx_mark_super(bs, d, h):
  +off = JT.Ext4JTx.super_off(bs)
  +t = B.Octets.take(off, d)
  +sw = DW.Ext4Dev.super_with(B.Octets.slice(off, 1024n, d), S.Ext4Super.incompat_recover(), 0)
  +r = B.Octets.drop(Nat.add(off, 1024n), d)
  +lt = BL.octets_len_take_le(off, d, Jc.le_add_l(off, 1024n, B.Octets.len(d), h))
  +ls = Jc.mk_lsw(bs, d, h)
  %Equal.sym(B.Octets, Laws.Ext4Laws.marked(bs, d), B.Octets.append(t, B.Octets.append(sw, r)), Jc.mk_eq(bs, d)) : {B.Octets.slice(off, 1024n, _) == sw : B.Octets}
  %Equal.trans(Nat, Nat.add(B.Octets.len(t), 0n), B.Octets.len(t), off, Jc.add_zero(B.Octets.len(t)), lt) : {B.Octets.slice(_, 1024n, B.Octets.append(t, B.Octets.append(sw, r))) == sw : B.Octets}
  %Equal.sym(B.Octets, B.Octets.slice(Nat.add(B.Octets.len(t), 0n), 1024n, B.Octets.append(t, B.Octets.append(sw, r))), B.Octets.slice(0n, 1024n, B.Octets.append(sw, r)), BL.octets_slice_append_add(t, 0n, 1024n, B.Octets.append(sw, r))) : {_ == sw : B.Octets}
  %Equal.sym(B.Octets, B.Octets.slice(0n, 1024n, B.Octets.append(sw, r)), B.Octets.slice(0n, 1024n, sw), BL.octets_slice_append_le(0n, 1024n, sw, r, Jc.le_eq(1024n, B.Octets.len(sw), 1024n, ls, {==}))) : {_ == sw : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(0n, sw), sw, BL.octets_drop_zero(sw)) : {B.Octets.take(1024n, _) == sw : B.Octets}
  %ls : {B.Octets.take(_, sw) == sw : B.Octets}
  BL.octets_take_len(sw)

def Laws.jtx_mark_before(bs, d, h):
  +off = JT.Ext4JTx.super_off(bs)
  +t = B.Octets.take(off, d)
  +sw = DW.Ext4Dev.super_with(B.Octets.slice(off, 1024n, d), S.Ext4Super.incompat_recover(), 0)
  +r = B.Octets.drop(Nat.add(off, 1024n), d)
  %Equal.sym(B.Octets, Laws.Ext4Laws.marked(bs, d), B.Octets.append(t, B.Octets.append(sw, r)), Jc.mk_eq(bs, d)) : {B.Octets.take(off, _) == t : B.Octets}
  %BL.octets_len_take_le(off, d, Jc.le_add_l(off, 1024n, B.Octets.len(d), h)) : {B.Octets.take(_, B.Octets.append(t, B.Octets.append(sw, r))) == t : B.Octets}
  BL.octets_take_append(t, B.Octets.append(sw, r))

def Laws.jtx_mark_after(bs, d, h):
  +off = JT.Ext4JTx.super_off(bs)
  +t = B.Octets.take(off, d)
  +sw = DW.Ext4Dev.super_with(B.Octets.slice(off, 1024n, d), S.Ext4Super.incompat_recover(), 0)
  +r = B.Octets.drop(Nat.add(off, 1024n), d)
  %Equal.sym(B.Octets, Laws.Ext4Laws.marked(bs, d), B.Octets.append(t, B.Octets.append(sw, r)), Jc.mk_eq(bs, d)) : {B.Octets.drop(Nat.add(off, 1024n), _) == r : B.Octets}
  %BL.octets_len_take_le(off, d, Jc.le_add_l(off, 1024n, B.Octets.len(d), h)) : {B.Octets.drop(Nat.add(_, 1024n), B.Octets.append(t, B.Octets.append(sw, r))) == r : B.Octets}
  %Jc.mk_lsw(bs, d, h) : {B.Octets.drop(Nat.add(B.Octets.len(t), _), B.Octets.append(t, B.Octets.append(sw, r))) == r : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(Nat.add(B.Octets.len(t), B.Octets.len(sw)), B.Octets.append(t, B.Octets.append(sw, r))), B.Octets.drop(B.Octets.len(sw), B.Octets.append(sw, r)), BL.octets_drop_append_add(t, B.Octets.len(sw), B.Octets.append(sw, r))) : {_ == r : B.Octets}
  BL.octets_drop_append(sw, r)

def Laws.jtx_mark_other(bs, b, d, h):
  %Equal.sym(Bool, Nat.is_eq(b, JT.Ext4JTx.super_block(bs)), False{}, h) : {[JW.Jbd2Write{b, JT.Ext4JTx.mark.at(_, bs, d)}] == [JW.Jbd2Write{b, d}] : List<&2, JW.Jbd2Write>}
  {==}

def Laws.super_with_witness():
  {==}
