# bend-osdev-lzo: LZO1X compression and decompression, written from the
# Linux kernel's documentation of the LZO1X stream format
# (Documentation/staging/lzo.rst); clean-room, see README.md.
#
# This file is the main concern: an LZO1X stream in, its bytes out (and
# back), with a maximum output size. The stream format is in decode.bend
# (decompression) and encode.bend (compression); the lzop file container is
# in lzop.bend, with its checksums in adler32.bend and the crc package.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./decode.bend as D
import ./encode.bend as C

# max: the most bytes decompression may produce
type LzoOptions is Data:
  LzoOptions{max: U32}

# 64 MiB
def LzoOptions.default() -> LzoOptions:
  LzoOptions{67108864}

# the bytes of the LZO1X stream src, with these options
def decompress_with(opts: LzoOptions, src: B.Octets) -> Result<&2, &2, E.LzoError, B.Octets>:
  match opts:
    case LzoOptions{max}:
      D.lzo1x_decompress(src, U32.to_nat(max))

# the bytes of the LZO1X stream src, at most 64 MiB of them
def decompress(src: B.Octets) -> Result<&2, &2, E.LzoError, B.Octets>:
  decompress_with(LzoOptions.default(), src)

# an LZO1X stream holding o
def compress(o: B.Octets) -> B.Octets:
  C.lzo1x_compress(o)
