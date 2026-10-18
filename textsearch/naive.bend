# bend-osdev-textsearch, the reference: a pattern tried at every offset of
# the whole text. Written to be obviously right; the other algorithms are
# held to it.
import Base
import ./textsearch.bend as T

# whether p is a prefix of xs (bytes compared as T.ts.same says)
def ts.naive.at(+icase: Bool, p: List<&2, U32>, xs: List<&2, U32>) -> Bool:
  match p xs:
    case Nil{} _:
      True{}
    case Con{a, pt} Nil{}:
      False{}
    case Con{a, pt} Con{b, xt}:
      Bool.and(T.ts.same(icase, a, b), ts.naive.at(icase, pt, xt))

def ts.naive.hit(h: Bool, +e: Nat, ms: List<&2, Nat>) -> List<&2, Nat>:
  match h:
    case True{}:
      Con{e, ms}
    case False{}:
      ms

def ts.naive.go(+icase: Bool, +p: List<&2, U32>, +m: Nat, xs: List<&2, U32>, +pos: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+c, +t}:
      ts.naive.hit(ts.naive.at(icase, p, Con{c, t}), Nat.add(pos, m), ts.naive.go(icase, p, m, t, 1n+pos))

# the ends of the occurrences of p in xs, in order; an empty pattern has
# none
def ts.naive.ends(+icase: Bool, +p: List<&2, U32>, xs: List<&2, U32>) -> List<&2, Nat>:
  match p:
    case Nil{}:
      Nil{}
    case Con{+a, +t}:
      ts.naive.go(icase, Con{a, t}, List.length(&2, U32, Con{a, t}), xs, 0n)
