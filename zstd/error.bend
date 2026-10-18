# bend-osdev-zstd, the failures: every part of the package answers
# Result<&2, &2, ZstdError, A>, with one constructor per failure (RFC 8878
# names the conditions; the names here are the package's own).
import Base

type ZstdError is Data:
  # the input ends inside a frame (a magic number, header, block or checksum)
  ZstdTruncated{}
  # four bytes where a frame starts are neither a Zstandard nor a skippable magic
  ZstdBadMagic{}
  # the frame header descriptor's reserved bit (bit 3) is set
  ZstdReservedBit{}
  # the frame's window is larger than the decoder's limit
  ZstdWindowTooLarge{}
  # the frame names a dictionary (an ID) other than the one given, or none was given
  ZstdDictionaryMismatch{}
  # a block of the reserved type 3
  ZstdBadBlockType{}
  # a block (its size, or what it decodes to) passes Block_Maximum_Size
  ZstdBlockTooLarge{}
  # a literals section header that does not fit its block, or regenerates too much
  ZstdBadLiteralsHeader{}
  # a Huffman tree description that is malformed
  ZstdBadHuffmanTree{}
  # treeless literals with no earlier tree in the frame (or dictionary)
  ZstdNoHuffmanTree{}
  # a Huffman-coded stream that is malformed or not consumed exactly
  ZstdBadHuffmanStream{}
  # an FSE table description that is malformed, or an RLE symbol out of range
  ZstdBadFseTable{}
  # a sequences table in repeat mode with no earlier table
  ZstdNoFseTable{}
  # a sequences section header that is cut short or sets reserved bits
  ZstdBadSequencesHeader{}
  # a sequences bitstream that is malformed or not consumed exactly
  ZstdBadSequenceStream{}
  # a sequence asks for more literals than are left
  ZstdLiteralsExhausted{}
  # an offset of 0, or one that reaches before the history the window allows
  ZstdBadOffset{}
  # the output would pass the caller's maximum
  ZstdOutputTooLarge{}
  # the frame's content is not the size its header gives
  ZstdBadContentSize{}
  # the content checksum does not match
  ZstdBadChecksum{}
  # a dictionary that starts with the dictionary magic number but is malformed
  ZstdBadDictionary{}

def ZstdError.show(e: ZstdError) -> String:
  match e:
    case ZstdTruncated{}:
      "Truncated"
    case ZstdBadMagic{}:
      "BadMagic"
    case ZstdReservedBit{}:
      "ReservedBit"
    case ZstdWindowTooLarge{}:
      "WindowTooLarge"
    case ZstdDictionaryMismatch{}:
      "DictionaryMismatch"
    case ZstdBadBlockType{}:
      "BadBlockType"
    case ZstdBlockTooLarge{}:
      "BlockTooLarge"
    case ZstdBadLiteralsHeader{}:
      "BadLiteralsHeader"
    case ZstdBadHuffmanTree{}:
      "BadHuffmanTree"
    case ZstdNoHuffmanTree{}:
      "NoHuffmanTree"
    case ZstdBadHuffmanStream{}:
      "BadHuffmanStream"
    case ZstdBadFseTable{}:
      "BadFseTable"
    case ZstdNoFseTable{}:
      "NoFseTable"
    case ZstdBadSequencesHeader{}:
      "BadSequencesHeader"
    case ZstdBadSequenceStream{}:
      "BadSequenceStream"
    case ZstdLiteralsExhausted{}:
      "LiteralsExhausted"
    case ZstdBadOffset{}:
      "BadOffset"
    case ZstdOutputTooLarge{}:
      "OutputTooLarge"
    case ZstdBadContentSize{}:
      "BadContentSize"
    case ZstdBadChecksum{}:
      "BadChecksum"
    case ZstdBadDictionary{}:
      "BadDictionary"

# Helpers for the decoders' do blocks

# Done if ok, else Fail with e
def ZstdError.require(ok: Bool, e: ZstdError) -> Result<&2, &2, ZstdError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

# the value in m, or Fail with e
def ZstdError.need(-A: Data, m: Maybe<&2, A>, e: ZstdError) -> Result<&2, &2, ZstdError, A>:
  match m:
    case Some{x}:
      Done{x}
    case None{}:
      Fail{e}
