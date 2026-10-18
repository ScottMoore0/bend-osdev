# bend-osdev-c842, the CRC trailer: the 32 bits after the end template.
#
# Linux's 842 ends a stream with a CRC-32 of the uncompressed bytes: the
# polynomial 0x04C11DB7 (CRC-32's), most significant bit first, initial
# value 0, no final XOR (ref/OBSERVATIONS.md, E1: one byte 01 gives
# 0x04C11DB7 itself, zeros give 0, and 42 outputs match). The check value of
# "123456789" is 0x89A1897F. No named CRC in the reveng catalogue has these
# parameters (CRC-32/MPEG-2 is the same but starts at 0xFFFFFFFF), so the
# package builds the parameter set with bend-osdev-crc's model and computes
# it through that package's interface.
import Base
import ../bytes/bytes.bend as B
import ../crc/crc.bend as K

# poly 0x04C11DB7 = 79764919
def C842Crc.spec() -> K.Crc32Spec:
  K.Crc32Spec{32n, 79764919, 0, False{}, 0}

# the trailer's CRC of a stream's uncompressed bytes
def c842.crc(o: B.Octets) -> U32:
  K.Crc32Spec.compute(C842Crc.spec(), o)
