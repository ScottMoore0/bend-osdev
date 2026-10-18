# bend-osdev-bzip2: the failures, one constructor each.
#
# Every fallible def in the package answers Result<&2, &2, Bzip2Error, A>.
import Base

type Bzip2Error is Data:
  # the input ends inside a stream (or is empty)
  Bzip2Truncated{}
  # a stream does not start with "BZh"
  Bzip2BadMagic{}
  # the block size digit after "BZh" is not 1 to 9
  Bzip2BadBlockSize{}
  # neither a block (0x314159265359) nor the end of the stream
  # (0x177245385090) where one should start
  Bzip2BadBlockMagic{}
  # the block's randomised bit is set (deprecated since bzip2 0.9.5; refused)
  Bzip2Randomised{}
  # the block's origin pointer is not below the block's length
  Bzip2BadOrigPtr{}
  # the symbol map marks no byte as used
  Bzip2BadSymbolMap{}
  # the number of Huffman tables is not 2 to 6
  Bzip2BadTableCount{}
  # the number of selectors is 0
  Bzip2BadSelectorCount{}
  # a selector names a table past the last
  Bzip2BadSelector{}
  # a code length is outside 1 to 20
  Bzip2BadCodeLength{}
  # the bits match no Huffman code, or the symbols outrun the selectors
  Bzip2BadHuffmanCode{}
  # a move-to-front index past the alphabet, or a run with no alphabet
  Bzip2BadSymbol{}
  # the block holds more bytes than its stream's block size allows
  Bzip2BlockTooLarge{}
  # a block's CRC does not match its data
  Bzip2BadBlockCrc{}
  # the stream's combined CRC does not match its blocks' CRCs
  Bzip2BadStreamCrc{}
  # the output would pass the caller's maximum
  Bzip2OutputTooLarge{}
  # bytes after the last stream that do not start a stream (when refused)
  Bzip2TrailingData{}

def Bzip2Error.show(e: Bzip2Error) -> String:
  match e:
    case Bzip2Truncated{}:
      "Truncated"
    case Bzip2BadMagic{}:
      "BadMagic"
    case Bzip2BadBlockSize{}:
      "BadBlockSize"
    case Bzip2BadBlockMagic{}:
      "BadBlockMagic"
    case Bzip2Randomised{}:
      "Randomised"
    case Bzip2BadOrigPtr{}:
      "BadOrigPtr"
    case Bzip2BadSymbolMap{}:
      "BadSymbolMap"
    case Bzip2BadTableCount{}:
      "BadTableCount"
    case Bzip2BadSelectorCount{}:
      "BadSelectorCount"
    case Bzip2BadSelector{}:
      "BadSelector"
    case Bzip2BadCodeLength{}:
      "BadCodeLength"
    case Bzip2BadHuffmanCode{}:
      "BadHuffmanCode"
    case Bzip2BadSymbol{}:
      "BadSymbol"
    case Bzip2BlockTooLarge{}:
      "BlockTooLarge"
    case Bzip2BadBlockCrc{}:
      "BadBlockCrc"
    case Bzip2BadStreamCrc{}:
      "BadStreamCrc"
    case Bzip2OutputTooLarge{}:
      "OutputTooLarge"
    case Bzip2TrailingData{}:
      "TrailingData"
