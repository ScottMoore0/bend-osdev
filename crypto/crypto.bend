# bend-osdev-crypto: one set of typed interfaces for the cryptographic
# algorithms of bend-osdev, the Bend counterpart of Linux's crypto API.
#
# An interface is a signature of template arguments: an algorithm satisfies it
# by supplying a def of each type, and a generic algorithm (HMAC over a hash,
# a mode over a block cipher) takes the signature as its own template
# arguments, so it is specialised at compile time for each algorithm it runs
# over. The interfaces, one file each:
#
#   block.bend    block cipher: key schedule, encrypt and decrypt a block
#   stream.bend   stream cipher: a state that encrypts the next piece of data
#   hash.bend     hash: streaming init / update / final, and one-shot
#   mac.bend      message authentication code: compute and verify
#   aead.bend     authenticated encryption with associated data: seal, open
#   kdf.bend      key derivation
#   sign.bend     signature: sign and verify
#   kex.bend      key agreement
#
# Each interface has laws that every instance must satisfy; README.md states
# them and gen/instances.py writes one law per instance into LAWS.bend. This
# file holds what every interface shares: the error type.
import Base
import ../bytes/bytes.bend as B

# Every failure an interface reports. An instance whose algorithm has its own
# error type maps it onto these (inst_lc.bend, inst_cm.bend).
type CrError is Data:
  CrBadKeyLength{got: Nat}
  CrBadIvLength{got: Nat}
  CrBadNonceLength{got: Nat}
  CrBadTagLength{got: Nat}
  CrBadBlockSize{got: Nat}
  CrNotBlockMultiple{len: Nat}
  CrTooShort{len: Nat}
  CrTooLong{len: Nat}
  CrBadPadding{}
  CrTagMismatch{}
  CrBadOutputLength{got: Nat}
  CrBadKey{}
  CrBadPublicKey{}

# A check, as a step of a Result block
def CrError.check(ok: Bool, e: CrError) -> Result<&2, &2, CrError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{e}

# A result with an algorithm's own error type, its error mapped onto CrError
def CrError.lift(~E: Data, ~A: Data, ~f: E -> CrError, r: Result<&2, &2, E, A>) -> Result<&2, &2, CrError, A>:
  match r:
    case Fail{e}:
      Fail{f(e)}
    case Done{x}:
      Done{x}
