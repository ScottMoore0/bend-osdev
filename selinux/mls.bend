# bend-osdev-selinux: MLS levels and ranges, and dominance.
#
# A level is a sensitivity and a set of categories (SELinux Notebook, "MLS
# and MCS"; the policy language's level and range statements). Sensitivities
# are numbered by their place in sensitivityorder, lowest first, and
# categories by their place in categoryorder, so a level's categories are a
# SeBits set of those places. l1 dominates l2 when its sensitivity is at
# least l2's and its categories include l2's.
import Base
import ./bits.bend as Bits

type SeLevel is Data:
  SeLevel{sens: Nat, cats: List<&2, Bool>}

def SeLevel.sens(x: SeLevel) -> Nat:
  match x:
    case SeLevel{v, _}:
      v

def SeLevel.cats(x: SeLevel) -> List<&2, Bool>:
  match x:
    case SeLevel{_, v}:
      v

type SeRange is Data:
  SeRange{low: SeLevel, high: SeLevel}

def SeRange.low(x: SeRange) -> SeLevel:
  match x:
    case SeRange{v, _}:
      v

def SeRange.high(x: SeRange) -> SeLevel:
  match x:
    case SeRange{_, v}:
      v

# a level with its category set made canonical
def SeLevel.make(s: Nat, cats: List<&2, Bool>) -> SeLevel:
  SeLevel{s, Bits.SeBits.norm(cats)}

def SeLevel.canonical(l: SeLevel) -> Bool:
  match l:
    case SeLevel{s, cats}:
      Bits.SeBits.is_norm(cats)

def SeLevel.has_cat(l: SeLevel, c: Nat) -> Bool:
  match l:
    case SeLevel{s, cats}:
      Bits.SeBits.has(cats, c)

# a dominates b ("dom")
def SeLevel.dom(a: SeLevel, b: SeLevel) -> Bool:
  match a:
    case SeLevel{sa, ca}:
      match b:
        case SeLevel{sb, cb}:
          Bool.and(Nat.is_ge(sa, sb), Bits.SeBits.subset(cb, ca))

# a is dominated by b ("domby")
def SeLevel.domby(a: SeLevel, b: SeLevel) -> Bool:
  SeLevel.dom(b, a)

# the same level: each dominates the other ("eq")
def SeLevel.eq(+a: SeLevel, +b: SeLevel) -> Bool:
  Bool.and(SeLevel.dom(a, b), SeLevel.dom(b, a))

# neither dominates the other ("incomp")
def SeLevel.incomp(+a: SeLevel, +b: SeLevel) -> Bool:
  Bool.and(Bool.not(SeLevel.dom(a, b)), Bool.not(SeLevel.dom(b, a)))

def SeRange.single(+l: SeLevel) -> SeRange:
  SeRange{l, l}

# a range is valid when its high level dominates its low level
def SeRange.valid(r: SeRange) -> Bool:
  match r:
    case SeRange{lo, hi}:
      SeLevel.dom(hi, lo)

# l lies within r
def SeRange.contains(r: SeRange, +l: SeLevel) -> Bool:
  match r:
    case SeRange{lo, hi}:
      Bool.and(SeLevel.dom(l, lo), SeLevel.dom(hi, l))

# inner lies within outer
def SeRange.within(outer: SeRange, inner: SeRange) -> Bool:
  match outer:
    case SeRange{olo, ohi}:
      match inner:
        case SeRange{ilo, ihi}:
          Bool.and(SeLevel.dom(ilo, olo), SeLevel.dom(ohi, ihi))

# the same range: equal low levels and equal high levels
def SeRange.is_eq(a: SeRange, b: SeRange) -> Bool:
  match a:
    case SeRange{la, ha}:
      match b:
        case SeRange{lb, hb}:
          Bool.and(SeLevel.eq(la, lb), SeLevel.eq(ha, hb))
