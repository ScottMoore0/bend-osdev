# bend-osdev-deflate, internal: equality of words and of byte lists, bit by
# bit, so that a proof can follow it for values it knows only symbolically
# (PROOF.bend proves eq.u32 sound and reflexive). The checksums' compare,
# the Huffman code search and the compressor's self-check use it.
import Base

def eq.word(n: Nat, a: Word(n), b: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match a b:
        case WCon{x, s} WCon{y, t}:
          Bool.and(Bool.not(Bool.xor(x, y)), eq.word(p, s, t))

def eq.u32(a: U32, b: U32) -> Bool:
  match a b:
    case U32{x} U32{y}:
      eq.word(32n, x, y)

# the same bytes in the same order; live: the bytes so far agree (a tail
# call, so it runs on lists of any length)
def eq.list.go(xs: List<&2, U32>, ys: List<&2, U32>, live: Bool) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      live
    case Con{a, s} Con{b, t}:
      eq.list.go(s, t, Bool.and(live, eq.u32(a, b)))
    case _ _:
      False{}

def eq.list(xs: List<&2, U32>, ys: List<&2, U32>) -> Bool:
  eq.list.go(xs, ys, True{})
