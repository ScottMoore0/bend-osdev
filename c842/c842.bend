# bend-osdev-c842: IBM's 842 compression, as Linux's 842 (and POWER's NX
# accelerator) reads and writes it. Clean-room: written from IBM's published
# paper and patent and from black-box observations of Linux's 842 (see
# README.md and ref/OBSERVATIONS.md); no Linux source was read.
#
# This file is the main concern: a stream in, its bytes out (and back), with
# options or the defaults. The format is in format.bend, the decoder in
# decode.bend, the matcher in match.bend, the encoder in encode.bend, the CRC
# trailer in crc.bend.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./decode.bend as D
import ./encode.bend as C

# max: the most bytes decompression may produce
type C842Options is Data:
  C842Options{max: U32}

# 64 MiB
def C842Options.default() -> C842Options:
  C842Options{67108864}

# the bytes of the 842 stream src, with these options
def decompress_with(opts: C842Options, src: B.Octets) -> Result<&2, &2, E.C842Error, B.Octets>:
  match opts:
    case C842Options{max}:
      D.c842.decompress(src, U32.to_nat(max))

# the bytes of the 842 stream src, at most 64 MiB of them
def decompress(src: B.Octets) -> Result<&2, &2, E.C842Error, B.Octets>:
  decompress_with(C842Options.default(), src)

# an 842 stream holding o, with these options
def compress_with(opts: C.C842CompressOptions, +o: B.Octets) -> B.Octets:
  C.c842.compress_with(opts, o)

# an 842 stream holding o
def compress(+o: B.Octets) -> B.Octets:
  C.c842.compress(o)
