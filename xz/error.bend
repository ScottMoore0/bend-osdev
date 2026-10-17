# bend-osdev-xz: the failures a decoder reports, one constructor each.
#
# Every fallible def in the package answers Result<&2, &2, XzError, A> (or,
# for a streaming decoder, whose state holds arrays, Result<&2, &1, XzError,
# A>). XzError.show gives a message, naming the check or the filter when one
# is not supported.
import Base

type XzError is Data:
  # the input ended before the data did
  XzTruncated{}
  # the stream header does not start with the .xz magic bytes FD 37 7A 58 5A 00
  XzBadMagic{}
  # the stream footer does not end with the magic bytes 59 5A ("YZ")
  XzBadFooterMagic{}
  # a CRC32 over a header, the index or a footer does not match
  XzBadHeaderCrc{}
  XzBadBlockHeaderCrc{}
  XzBadIndexCrc{}
  XzBadFooterCrc{}
  # a block's check (CRC32, CRC64 or SHA-256) does not match its data
  XzBadCheck{}
  # reserved bits are set in the stream flags
  XzBadStreamFlags{}
  # the stream footer's flags differ from the stream header's
  XzFlagsMismatch{}
  # a block header is malformed: reserved bits, a bad size field, bad padding,
  # or a filter chain that does not end with LZMA2
  XzBadBlockHeader{}
  # a filter's properties are malformed (wrong size, or a value out of range)
  XzBadFilterProps{}
  # a block's data does not have the sizes its header declares
  XzBadBlockSize{}
  # the index does not describe the blocks that came before it
  XzBadIndex{}
  # the footer's backward size is not the size of the index
  XzBadBackwardSize{}
  # padding that must be null bytes is not, or stream padding is not a
  # multiple of four bytes
  XzBadPadding{}
  # a check type this decoder cannot verify (id: the 4-bit check ID)
  XzUnsupportedCheck{id: U32}
  # a filter this decoder does not implement (id: the filter ID)
  XzUnsupportedFilter{id: Nat}
  # the LZMA2 or LZMA data is corrupt
  XzCorruptLzma{}
  # the output would exceed the caller's maximum
  XzOutputTooLarge{}
  # bytes follow the end of a raw LZMA2 stream
  XzTrailingData{}

# The check IDs ("The .xz File Format", 2.1.1.2)
def XzError.check_name(n: Nat) -> String:
  match n:
    case 0n:
      "none"
    case 1n:
      "CRC32"
    case 4n:
      "CRC64"
    case 10n:
      "SHA-256"
    case _:
      "reserved"

# The filter IDs ("The .xz File Format", 5.3)
def XzError.filter_name(n: Nat) -> String:
  match n:
    case 3n:
      "delta"
    case 4n:
      "x86 BCJ"
    case 5n:
      "PowerPC BCJ"
    case 6n:
      "IA-64 BCJ"
    case 7n:
      "ARM BCJ"
    case 8n:
      "ARM-Thumb BCJ"
    case 9n:
      "SPARC BCJ"
    case 10n:
      "ARM64 BCJ"
    case 11n:
      "RISC-V BCJ"
    case 33n:
      "LZMA2"
    case _:
      "unknown"

def XzError.show(e: XzError) -> String:
  match e:
    case XzTruncated{}:
      "truncated input"
    case XzBadMagic{}:
      "not an .xz stream (bad header magic)"
    case XzBadFooterMagic{}:
      "bad stream footer magic"
    case XzBadHeaderCrc{}:
      "stream header CRC32 mismatch"
    case XzBadBlockHeaderCrc{}:
      "block header CRC32 mismatch"
    case XzBadIndexCrc{}:
      "index CRC32 mismatch"
    case XzBadFooterCrc{}:
      "stream footer CRC32 mismatch"
    case XzBadCheck{}:
      "block check mismatch: the data is corrupt"
    case XzBadStreamFlags{}:
      "reserved stream flags set"
    case XzFlagsMismatch{}:
      "stream footer flags differ from the header's"
    case XzBadBlockHeader{}:
      "malformed block header"
    case XzBadFilterProps{}:
      "malformed filter properties"
    case XzBadBlockSize{}:
      "block sizes differ from its header's"
    case XzBadIndex{}:
      "the index does not match the blocks"
    case XzBadBackwardSize{}:
      "the footer's backward size does not match the index"
    case XzBadPadding{}:
      "non-null or misaligned padding"
    case XzUnsupportedCheck{+id}:
      "unsupported check " ++ U32.show(id) ++ " (" ++ XzError.check_name(U32.to_nat(id)) ++ ")"
    case XzUnsupportedFilter{+id}:
      "unsupported filter " ++ Nat.show(id) ++ " (" ++ XzError.filter_name(id) ++ ")"
    case XzCorruptLzma{}:
      "corrupt LZMA2 data"
    case XzOutputTooLarge{}:
      "output larger than the maximum"
    case XzTrailingData{}:
      "data after the end of the LZMA2 stream"
