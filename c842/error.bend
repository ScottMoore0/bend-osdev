# bend-osdev-c842, the failures: one error type for the package, one
# constructor per failure. Linux's decoder answers EOVERFLOW for the first,
# ENOSPC for the second and EINVAL for the rest (ref/OBSERVATIONS.md, E7).
import Base

type C842Error is Data:
  C842Truncated{}
  C842OutputTooLarge{}
  C842BadTemplate{}
  C842BadPointer{}
  C842BadRepeat{}
  C842BadShort{}
  C842BadCrc{}

def C842Error.show(e: C842Error) -> String:
  match e:
    case C842Truncated{}:
      "Truncated"
    case C842OutputTooLarge{}:
      "OutputTooLarge"
    case C842BadTemplate{}:
      "BadTemplate"
    case C842BadPointer{}:
      "BadPointer"
    case C842BadRepeat{}:
      "BadRepeat"
    case C842BadShort{}:
      "BadShort"
    case C842BadCrc{}:
      "BadCrc"
