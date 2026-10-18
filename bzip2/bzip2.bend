# bend-osdev-bzip2: bzip2 decompression and compression, from Joe Tsai's
# "BZip2 Format Specification" and the bzip2 manual (version 1.0.8).
#
# This file is the main concern: a .bz2 file (one stream or more) to its
# content, and content to a .bz2 stream. The parts are in their own files,
# each usable alone: the stream format (stream.bend), one block
# (block.bend), the Huffman codes (huffman.bend), move-to-front and RLE2
# (mtf.bend), the Burrows-Wheeler transform (bwt.bend), RLE1 (rle.bend), the
# bits (bits.bend), the compressor (compress.bend) and the errors
# (error.bend).
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./stream.bend as S
import ./compress.bend as Z

# the content of the bzip2 file src, with these options
def decompress_with(opts: S.Bzip2Options, src: B.Octets) -> Result<&2, &2, E.Bzip2Error, B.Octets>:
  S.stream_decode(opts, src)

# the content of the bzip2 file src, with the default options (at most
# 64 MiB, bytes after the last stream ignored)
def decompress(src: B.Octets) -> Result<&2, &2, E.Bzip2Error, B.Octets>:
  decompress_with(S.Bzip2Options.default(), src)

# o as a bzip2 stream, with these options
def compress_with(opts: Z.Bzip2CompressOptions, o: B.Octets) -> B.Octets:
  Z.compress_with(opts, o)

# o as a bzip2 stream, level 9
def compress(o: B.Octets) -> B.Octets:
  Z.compress(o)
