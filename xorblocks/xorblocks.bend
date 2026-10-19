# bend-osdev-xorblocks: the XOR of byte blocks, the counterpart of the
# kernel's xor_blocks (which XORs a number of source blocks into a
# destination block), as used for RAID-5 and RAID-6's P parity.
#
# XOR is bitwise exclusive or of each pair of bytes at the same offset. The
# one choice is what to do when two blocks differ in length, and it is a
# parameter (XorbLen):
#   * XorbLonger (the default): the shorter block counts as padded with zero
#     bytes, so the result is as long as the longer one. XOR is then a
#     commutative, associative operation with the empty block as its
#     identity, and a block XORed with itself gives zeros;
#   * XorbShorter: the result stops where the shorter block ends.
# On blocks of equal length the two agree (LAWS.bend).
#
# Byte strings are Octets (bend-osdev-bytes). The work is done on the
# blocks' lists of bytes, tail-recursively, so that blocks of any length run
# on both of Bend's lanes. Xorb.xor_list and Xorb.xor_cut_list are the
# structural forms, on byte lists: they are public, as the bytewise meaning
# of the two XORs (the laws xor_list and xor_cut_list), for dependents'
# proofs; each fast form is proved equal to its structural form.
import Base
import ../bytes/bytes.bend as B

type XorbLen is Data:
  XorbLonger{}
  XorbShorter{}

# The default length policy: pad the shorter block with zeros
def Xorb.len_default() -> XorbLen:
  XorbLonger{}

# The structural forms, on byte lists (public: the bytewise meaning)

# the XOR of two byte lists, the shorter padded with zeros
def Xorb.xor_list(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  match a b:
    case Nil{} _:
      b
    case Con{x, s} Nil{}:
      Con{x, s}
    case Con{x, s} Con{y, t}:
      Con{U32.xor(x, y), Xorb.xor_list(s, t)}

# the XOR of two byte lists, as long as the shorter
def Xorb.xor_cut_list(a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  match a b:
    case Con{x, s} Con{y, t}:
      Con{U32.xor(x, y), Xorb.xor_cut_list(s, t)}
    case _ _:
      Nil{}

# The tail-recursive forms (internal): the result so far is kept reversed in
# acc, and turned round at the end

def xorb.pad.go(a: List<&2, U32>, b: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match a b:
    case Nil{} _:
      B.rev_onto(acc, b)
    case Con{x, s} Nil{}:
      B.rev_onto(acc, Con{x, s})
    case Con{x, s} Con{y, t}:
      xorb.pad.go(s, t, Con{U32.xor(x, y), acc})

def xorb.cut.go(a: List<&2, U32>, b: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match a b:
    case Con{x, s} Con{y, t}:
      xorb.cut.go(s, t, Con{U32.xor(x, y), acc})
    case _ _:
      B.rev_onto(acc, Nil{})

# The public interface

# a XOR b, the shorter padded with zero bytes (the result is as long as the
# longer)
def Xorb.xor(a: B.Octets, b: B.Octets) -> B.Octets:
  B.Octets.of_list(xorb.pad.go(B.Octets.to_list(a), B.Octets.to_list(b), Nil{}))

# a XOR b, as long as the shorter
def Xorb.xor_cut(a: B.Octets, b: B.Octets) -> B.Octets:
  B.Octets.of_list(xorb.cut.go(B.Octets.to_list(a), B.Octets.to_list(b), Nil{}))

# a XOR b under a length policy
def Xorb.xor_with(p: XorbLen, a: B.Octets, b: B.Octets) -> B.Octets:
  match p:
    case XorbLonger{}:
      Xorb.xor(a, b)
    case XorbShorter{}:
      Xorb.xor_cut(a, b)

# xor_blocks: every source XORed into the destination, in order (the
# sources come first in the helpers, the shrinking argument)
def xorb.into.go(srcs: List<&2, B.Octets>, dest: B.Octets) -> B.Octets:
  match srcs:
    case Nil{}:
      dest
    case Con{s, rest}:
      xorb.into.go(rest, Xorb.xor(dest, s))

def Xorb.into(dest: B.Octets, srcs: List<&2, B.Octets>) -> B.Octets:
  xorb.into.go(srcs, dest)

def xorb.into_with.go(srcs: List<&2, B.Octets>, +p: XorbLen, dest: B.Octets) -> B.Octets:
  match srcs:
    case Nil{}:
      dest
    case Con{s, rest}:
      xorb.into_with.go(rest, p, Xorb.xor_with(p, dest, s))

# the same under a length policy
def Xorb.into_with(+p: XorbLen, dest: B.Octets, srcs: List<&2, B.Octets>) -> B.Octets:
  xorb.into_with.go(srcs, p, dest)

# the XOR of all the blocks (RAID-5's parity); the empty block for none
def Xorb.all(srcs: List<&2, B.Octets>) -> B.Octets:
  Xorb.into(B.Octets.empty(), srcs)
