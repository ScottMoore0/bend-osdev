# DRAFT: not yet reviewed by the maintainer
#
# The offset conversions (off.bend), for every input: an offset reaches an
# effect as two halves and a size comes back as two, and nothing is lost
# either way; a 32-bit offset has a zero high half, so it fits Base's
# 32-bit defs. Vectors: a sum that carries into the high half, the largest
# word, and a word past 4 GiB.
#
# The effects themselves (fileio.bend, fileio.c, fileio.js) have no laws:
# they are tested against Python on both lanes (check.bend, ref/).
import Base
import ../word64/word64.bend as W
import ./off.bend as O

# For every word: its halves joined give it back.
law off_join_halves:
  for v: W.W64
  {O.FileIO.off.join(O.FileIO.off.halves(v)) == v : W.W64}

# For every pair of halves: the joined word splits back into them.
law off_halves_join:
  for +h: U32
  for +l: U32
  {O.FileIO.off.halves(O.FileIO.off.join((h, l))) == (h, l) : U32 & U32}

# For every 32-bit offset: its halves are 0 and itself.
law off_of_u32:
  for o: U32
  {O.FileIO.off.halves(O.FileIO.off.of_u32(o)) == (0, o) : U32 & U32}

# For every 32-bit offset: it fits.
law off_fits32_of_u32:
  for +o: U32
  {O.FileIO.off.fits32(O.FileIO.off.of_u32(o)) == True{} : Bool}

# (2^32 - 1) + 6 = 2^32 + 5
law off_halves_carry:
  {O.FileIO.off.halves(W.W64.add(W.W64.from_u32(4294967295), W.W64.from_u32(6))) == (1, 5) : U32 & U32}

law off_halves_max:
  {O.FileIO.off.halves(W.W64.max()) == (4294967295, 4294967295) : U32 & U32}

law off_fits32_past:
  {O.FileIO.off.fits32(O.FileIO.off.join((1, 0))) == False{} : Bool}
