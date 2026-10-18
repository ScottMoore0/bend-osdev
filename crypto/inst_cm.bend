# The adapter for cipher-modes: its error type mapped onto CrError, and the
# block format of its 128-bit block CmBlock (an open type: four big-endian
# 32-bit words), for every 128-bit cipher that uses it (cipher-modes' AES,
# legacy-ciphers' SM4, Camellia, Serpent and Twofish).
#
# The format's conversions are written here, on the open type, so that its
# law (format: blk_of(blk_to(b)) == Some{b}) is proved in this package:
# cipher-modes proves the same of its own CmBlock.of_octets and
# CmBlock.to_octets, but its PROOF.bend cannot be imported by a proof that
# passes --verdict (README.md, "Laws").
import Base
import ../bytes/bytes.bend as B
import ../word64/word64.bend as W
import ../cipher-modes/cipher-modes.bend as M
import ./crypto.bend as Cr

# Errors

def CrCm.err(e: M.CmError) -> Cr.CrError:
  match e:
    case M.CmBadKeyLength{n}:
      Cr.CrBadKeyLength{n}
    case M.CmBadIvLength{n}:
      Cr.CrBadIvLength{n}
    case M.CmBadTweakLength{n}:
      Cr.CrBadIvLength{n}
    case M.CmBadNonceLength{n}:
      Cr.CrBadNonceLength{n}
    case M.CmBadTagLength{n}:
      Cr.CrBadTagLength{n}
    case M.CmBadBlockSize{n}:
      Cr.CrBadBlockSize{n}
    case M.CmNotBlockMultiple{n}:
      Cr.CrNotBlockMultiple{n}
    case M.CmTooShort{n}:
      Cr.CrTooShort{n}
    case M.CmTooLong{n}:
      Cr.CrTooLong{n}
    case M.CmBadPadding{}:
      Cr.CrBadPadding{}
    case M.CmTagMismatch{}:
      Cr.CrTagMismatch{}

# a cipher-modes result as an interface result
def CrCm.lift(~A: Data, r: Result<&2, &2, M.CmError, A>) -> Result<&2, &2, Cr.CrError, A>:
  Cr.CrError.lift(~M.CmError, ~A, ~CrCm.err, r)

# a cipher-modes key schedule as the interface's ~key
def CrCm.key(~K: Data, ~key: B.Octets -> Result<&2, &2, M.CmError, K>, o: B.Octets) -> Result<&2, &2, Cr.CrError, K>:
  CrCm.lift(~K, key(o))

# The 128-bit block format

def cr.f128.bits8(b: U32) -> Word(8n):
  match b:
    case U32{w}:
      W.W64.bits.lo(8n, 24n, w)

# the word with bytes a, b, c, d, most significant first
def cr.f128.word(a: U32, b: U32, c: U32, d: U32) -> U32:
  U32{W.W64.bits.cat(8n, 24n, cr.f128.bits8(d), W.W64.bits.cat(8n, 16n, cr.f128.bits8(c), W.W64.bits.cat(8n, 8n, cr.f128.bits8(b), cr.f128.bits8(a))))}

# the 16 bytes of a block, most significant byte of w0 first
def cr.f128.bytes(b: M.CmBlock) -> List<&2, U32>:
  match b:
    case M.CmBlock{w0, w1, w2, w3}:
      B.append(B.be32(w0), B.append(B.be32(w1), B.append(B.be32(w2), B.be32(w3))))

# exactly 16 bytes as a block
def cr.f128.block(xs: List<&2, U32>) -> Maybe<&2, M.CmBlock>:
  match xs:
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Nil{}}}}}}}}}}}}}}}}}:
      Some{M.CmBlock{cr.f128.word(a0, a1, a2, a3), cr.f128.word(a4, a5, a6, a7), cr.f128.word(a8, a9, a10, a11), cr.f128.word(a12, a13, a14, a15)}}
    case _:
      None{}

# a block's 16 bytes
def CrBlk128.to_octets(b: M.CmBlock) -> B.Octets:
  B.Octets.of_list(cr.f128.bytes(b))

# 16 bytes as a block; None for any other length
def CrBlk128.of_octets(o: B.Octets) -> Maybe<&2, M.CmBlock>:
  cr.f128.block(B.Octets.to_list(o))

def CrBlk128.xor(a: M.CmBlock, b: M.CmBlock) -> M.CmBlock:
  match a b:
    case M.CmBlock{a0, a1, a2, a3} M.CmBlock{b0, b1, b2, b3}:
      M.CmBlock{U32.xor(a0, b0), U32.xor(a1, b1), U32.xor(a2, b2), U32.xor(a3, b3)}
