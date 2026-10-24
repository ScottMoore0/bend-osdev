# bend-osdev-c842, the pointer rule: the position a pointer reads.
#
# An index i of an s-byte sub-phrase (P2: 2 bytes, P4: 4, P8: 8), in a
# history of H bytes (512 for P2, 2048 for P4 and P8: the paper's ring
# histories), reads s bytes at the latest position p congruent to i * s
# modulo H with p below the output's length rounded down to 8
# (ref/OBSERVATIONS.md, E3 to E6). There may be no such position: the
# decoder then refuses the stream (C842BadPointer).
#
# The decoder (decode.bend) resolves every pointer here, with the length of
# its output so far. LAWS.bend states the rule for every length and every
# index of the kind's width (pointer_found, pointer_rule,
# pointer_in_window), and that every index the parser reads has that width
# (parser_indices_fit).
import Base
import ./format.bend as F

def c842.pointer.wrap(lt: Bool, +p0: U32, h: U32) -> Maybe<&2, U32>:
  match lt:
    case True{}:
      None{}
    case False{}:
      Some{U32.sub(p0, h)}

def c842.pointer.at(below: Bool, +p0: U32, +h: U32) -> Maybe<&2, U32>:
  match below:
    case True{}:
      Some{p0}
    case False{}:
      c842.pointer.wrap(U32.is_lt(p0, h), p0, h)

# base + index * size, where base is the output's length n rounded down to 8
# (t8) and then to the history h (a power of two); less h if that is t8 or
# more; none if that would be below 0
def c842.pointer.pos(+n: U32, idx: U32, size: U32, +h: U32) -> Maybe<&2, U32>:
  +t8 = U32.and(n, 4294967288)
  +p0 = U32.add(U32.and(t8, U32.sub(0, h)), U32.mul(size, idx))
  c842.pointer.at(U32.is_lt(p0, t8), p0, h)

# the position the pointer of kind k with index i reads after n bytes of
# output, or None if there is none (k is P2, P4 or P8)
def c842.pointer(+n: U32, +k: F.C842Kind, i: U32) -> Maybe<&2, U32>:
  c842.pointer.pos(n, i, F.C842Kind.size(k), F.C842Kind.history(k))
