# bend-osdev-apparmor: byte-string helpers on List<&2, U32>, the form the
# package works on inside (profile text, names, paths). Public interfaces take
# Octets (bend-osdev-bytes) and convert once.
import Base

def AaText.is_nil(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

def AaText.append(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, AaText.append(t, ys)}

def AaText.rev_onto(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      AaText.rev_onto(t, Con{h, acc})

def AaText.rev(xs: List<&2, U32>) -> List<&2, U32>:
  AaText.rev_onto(xs, Nil{})

def AaText.len(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+AaText.len(t)

def AaText.eq(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{h, t}:
      False{}
    case Con{h, t} Nil{}:
      False{}
    case Con{a, as} Con{b, bs}:
      Bool.and(U32.is_eq(a, b), AaText.eq(as, bs))

# the codes of a string's characters
def AaText.of_string(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      Con{Char.to_u32(c), AaText.of_string(t)}

def AaText.to_string(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      SCon{Char.from_u32(h), AaText.to_string(t)}

# xs is exactly the string s
def AaText.is(xs: List<&2, U32>, s: String) -> Bool:
  match xs s:
    case Nil{} SNil{}:
      True{}
    case Nil{} SCon{c, t}:
      False{}
    case Con{h, t} SNil{}:
      False{}
    case Con{h, t} SCon{c, u}:
      Bool.and(U32.is_eq(h, Char.to_u32(c)), AaText.is(t, u))

# xs begins with the string s
def AaText.starts(xs: List<&2, U32>, s: String) -> Bool:
  match xs s:
    case Nil{} SNil{}:
      True{}
    case Nil{} SCon{c, t}:
      False{}
    case Con{h, t} SNil{}:
      True{}
    case Con{h, t} SCon{c, u}:
      Bool.and(U32.is_eq(h, Char.to_u32(c)), AaText.starts(t, u))

# xs begins with ys
def AaText.prefix(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{c, t}:
      False{}
    case Con{h, t} Nil{}:
      True{}
    case Con{h, t} Con{c, u}:
      Bool.and(U32.is_eq(h, c), AaText.prefix(t, u))

def AaText.drop(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      xs
    case 1n+p:
      match xs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          AaText.drop(p, t)

def AaText.has(xs: List<&2, U32>, +c: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(U32.is_eq(h, c), AaText.has(t, c))

def AaText.head(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      h

def AaText.last(xs: List<&2, U32>, l: U32) -> U32:
  match xs:
    case Nil{}:
      l
    case Con{h, t}:
      AaText.last(t, h)

# the list without its last element
def AaText.init(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match t:
        case Nil{}:
          Nil{}
        case Con{a, b}:
          Con{h, AaText.init(Con{a, b})}

# x is one of the names xs
def AaText.member(xs: List<&2, List<&2, U32>>, +x: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(AaText.eq(h, x), AaText.member(t, x))

# s is one of the strings ns
def AaText.one_of(ns: List<&2, String>, +s: List<&2, U32>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(AaText.is(s, h), AaText.one_of(t, s))

# every name of xs is one of ys
def AaText.subset(xs: List<&2, List<&2, U32>>, +ys: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(AaText.member(ys, h), AaText.subset(t, ys))

# split at the first "//": the text before it, and the rest after it
def AaText.tail(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

# a name cut at its first "//": the part before it, and the rest after it
type AaSplit is Data:
  AaSplit{first: List<&2, U32>, rest: Maybe<&2, List<&2, U32>>}

def AaText.split2.go(xs: List<&2, U32>, +prev: Bool, +acc: List<&2, U32>) -> AaSplit:
  match xs:
    case Nil{}:
      AaSplit{AaText.rev(acc), None{}}
    case Con{+h, +t}:
      +slash = U32.is_eq(h, 47)
      Bool.pick(AaSplit, Bool.and(prev, slash), AaSplit{AaText.rev(AaText.tail(acc)), Some{t}}, AaText.split2.go(t, slash, Con{h, acc}))

def AaText.split2(xs: List<&2, U32>) -> AaSplit:
  AaText.split2.go(xs, False{}, Nil{})

# the split of a rest, if there is one
def AaText.split2.opt(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, AaSplit>:
  match m:
    case None{}:
      None{}
    case Some{xs}:
      Some{AaText.split2(xs)}

def AaText.lappend(xs: List<&2, List<&2, U32>>, ys: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, AaText.lappend(t, ys)}
