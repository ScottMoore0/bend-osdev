# bend-osdev-lzo, the failures: one error type for every file of the package
# (the LZO1X stream, the lzop container), one constructor per failure.
import Base

type LzoError is Data:
  LzoTruncated{}
  LzoBadDistance{}
  LzoOutputTooLarge{}
  LzoTrailing{}
  LzoBadMagic{}
  LzoBadVersion{}
  LzoBadMethod{}
  LzoUnsupported{}
  LzoBadHeaderChecksum{}
  LzoBadBlockSize{}
  LzoBadChecksum{}

def LzoError.show(e: LzoError) -> String:
  match e:
    case LzoTruncated{}:
      "Truncated"
    case LzoBadDistance{}:
      "BadDistance"
    case LzoOutputTooLarge{}:
      "OutputTooLarge"
    case LzoTrailing{}:
      "Trailing"
    case LzoBadMagic{}:
      "BadMagic"
    case LzoBadVersion{}:
      "BadVersion"
    case LzoBadMethod{}:
      "BadMethod"
    case LzoUnsupported{}:
      "Unsupported"
    case LzoBadHeaderChecksum{}:
      "BadHeaderChecksum"
    case LzoBadBlockSize{}:
      "BadBlockSize"
    case LzoBadChecksum{}:
      "BadChecksum"
