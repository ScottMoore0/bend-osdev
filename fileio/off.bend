# bend-osdev-fileio: 64-bit offsets and sizes as the effects pass them.
#
# The effects in fileio.bend take a 64-bit offset as two U32 halves (high,
# low) and answer a 64-bit size as such a pair: a U32 is what Base's own
# effects pass, and it crosses to C and JavaScript as a plain number. These
# pure helpers convert between that pair and a W64 (bend-osdev-word64),
# through word64's public defs only; the laws say no offset is changed on
# the way (LAWS.bend).
import Base
import ../word64/word64.bend as W

# the high and low halves of a word, as an effect takes them
def FileIO.off.halves(+v: W.W64) -> U32 & U32:
  (W.W64.hi(v), W.W64.lo(v))

# the word whose halves are the pair (high, low), as an effect answers it
def FileIO.off.join(p: U32 & U32) -> W.W64:
  (h, l) = p
  W.W64.from_parts(h, l)

# a 32-bit offset (as Base's File.read_at takes) as a 64-bit one
def FileIO.off.of_u32(o: U32) -> W.W64:
  W.W64.from_parts(0, o)

# whether the word is below 2^32, so that Base's 32-bit defs could take it
def FileIO.off.fits32(v: W.W64) -> Bool:
  U32.is_eq(W.W64.hi(v), 0)
