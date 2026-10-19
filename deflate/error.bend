# bend-osdev-deflate: the failures, one constructor each.
#
# Every fallible def in the package (raw DEFLATE, zlib and gzip) answers
# Result<&2, &2, DeflateError, A>.
import Base

type DeflateError is Data:
  # the input ends inside the stream (or is empty)
  DeflateTruncated{}
  # a block header's BTYPE is 11 (RFC 1951, 3.2.3: "reserved (error)")
  DeflateBadBlockType{}
  # a stored block's NLEN is not the one's complement of its LEN (3.2.4)
  DeflateBadStoredLength{}
  # HLIT names more than 286 literal/length codes, or HDIST more than 30
  # distance codes
  DeflateTooManyCodes{}
  # the code length code is over-subscribed or incomplete
  DeflateBadCodeLengthCode{}
  # code 16 with no previous length, or a repeat past the HLIT + HDIST
  # lengths
  DeflateBadRepeat{}
  # the literal/length code is over-subscribed, or incomplete (other than
  # a single code of one bit)
  DeflateBadLitLenCode{}
  # the distance code is over-subscribed, or incomplete (other than a
  # single code of one bit)
  DeflateBadDistCode{}
  # the literal/length code has no code for 256, the end of the block
  DeflateNoEndCode{}
  # the bits match no code of the code length code
  DeflateBadCodeLengthSymbol{}
  # the bits match no literal/length code, or name 286 or 287
  DeflateBadLitLenSymbol{}
  # the bits match no distance code, or name 30 or 31
  DeflateBadDistSymbol{}
  # a distance reaches back before the start of the output (and dictionary)
  DeflateDistanceTooFar{}
  # the output would pass the caller's maximum
  DeflateOutputTooLarge{}
  # bytes after the stream, when refused
  DeflateTrailingData{}
  # zlib (RFC 1950): CMF * 256 + FLG is not a multiple of 31
  DeflateZlibBadHeader{}
  # zlib: CM is not 8
  DeflateZlibBadMethod{}
  # zlib: CINFO is above 7
  DeflateZlibBadWindow{}
  # zlib: FDICT is set and no dictionary was given
  DeflateZlibNeedDict{}
  # zlib: DICTID is not the Adler-32 of the dictionary given
  DeflateZlibBadDictId{}
  # zlib: the Adler-32 of the output is not ADLER32
  DeflateZlibBadChecksum{}
  # gzip (RFC 1952): ID1, ID2 are not 31, 139
  DeflateGzipBadMagic{}
  # gzip: CM is not 8
  DeflateGzipBadMethod{}
  # gzip: a reserved FLG bit is set
  DeflateGzipReservedFlags{}
  # gzip: the header's CRC16 (FHCRC) does not match
  DeflateGzipBadHeaderCrc{}
  # gzip: the CRC-32 of a member's output is not its CRC32
  DeflateGzipBadCrc{}
  # gzip: a member's output size modulo 2^32 is not its ISIZE
  DeflateGzipBadSize{}

def DeflateError.show(e: DeflateError) -> String:
  match e:
    case DeflateTruncated{}:
      "Truncated"
    case DeflateBadBlockType{}:
      "BadBlockType"
    case DeflateBadStoredLength{}:
      "BadStoredLength"
    case DeflateTooManyCodes{}:
      "TooManyCodes"
    case DeflateBadCodeLengthCode{}:
      "BadCodeLengthCode"
    case DeflateBadRepeat{}:
      "BadRepeat"
    case DeflateBadLitLenCode{}:
      "BadLitLenCode"
    case DeflateBadDistCode{}:
      "BadDistCode"
    case DeflateNoEndCode{}:
      "NoEndCode"
    case DeflateBadCodeLengthSymbol{}:
      "BadCodeLengthSymbol"
    case DeflateBadLitLenSymbol{}:
      "BadLitLenSymbol"
    case DeflateBadDistSymbol{}:
      "BadDistSymbol"
    case DeflateDistanceTooFar{}:
      "DistanceTooFar"
    case DeflateOutputTooLarge{}:
      "OutputTooLarge"
    case DeflateTrailingData{}:
      "TrailingData"
    case DeflateZlibBadHeader{}:
      "ZlibBadHeader"
    case DeflateZlibBadMethod{}:
      "ZlibBadMethod"
    case DeflateZlibBadWindow{}:
      "ZlibBadWindow"
    case DeflateZlibNeedDict{}:
      "ZlibNeedDict"
    case DeflateZlibBadDictId{}:
      "ZlibBadDictId"
    case DeflateZlibBadChecksum{}:
      "ZlibBadChecksum"
    case DeflateGzipBadMagic{}:
      "GzipBadMagic"
    case DeflateGzipBadMethod{}:
      "GzipBadMethod"
    case DeflateGzipReservedFlags{}:
      "GzipReservedFlags"
    case DeflateGzipBadHeaderCrc{}:
      "GzipBadHeaderCrc"
    case DeflateGzipBadCrc{}:
      "GzipBadCrc"
    case DeflateGzipBadSize{}:
      "GzipBadSize"
