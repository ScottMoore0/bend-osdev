# The adapter for legacy-ciphers: its error type mapped onto CrError, its
# key schedules as the block-cipher interface's ~key, and the XOR of its
# 64-bit block LcBlock64 (an open type). The 64-bit block format is
# legacy-ciphers' own LcBlock64.of_octets and LcBlock64.to_octets, whose law
# it proves (block64_octets_round_trip); the 128-bit ciphers use
# inst_cm.bend's format.
#
# Each cipher is then an instance with no code of its own, for example SM4:
#   ~S.LcSm4Key, ~M.CmBlock, ~16n, ~CrLc.key(~S.LcSm4Key, ~S.LcSm4.key),
#   ~S.LcSm4.encrypt, ~S.LcSm4.decrypt,
#   ~CrBlk128.of_octets, ~CrBlk128.to_octets, ~CrBlk128.xor
# (README.md lists every instance).
import Base
import ../bytes/bytes.bend as B
import ../legacy-ciphers/legacy-ciphers.bend as L
import ./crypto.bend as Cr

def CrLc.err(e: L.LcError) -> Cr.CrError:
  match e:
    case L.LcBadKeyLength{n}:
      Cr.CrBadKeyLength{n}
    case L.LcBadIvLength{n}:
      Cr.CrBadIvLength{n}
    case L.LcNotBlockMultiple{n}:
      Cr.CrNotBlockMultiple{n}

# a legacy-ciphers result as an interface result
def CrLc.lift(~A: Data, r: Result<&2, &2, L.LcError, A>) -> Result<&2, &2, Cr.CrError, A>:
  Cr.CrError.lift(~L.LcError, ~A, ~CrLc.err, r)

# a legacy-ciphers key schedule as the interface's ~key
def CrLc.key(~K: Data, ~key: B.Octets -> Result<&2, &2, L.LcError, K>, o: B.Octets) -> Result<&2, &2, Cr.CrError, K>:
  CrLc.lift(~K, key(o))

# The 64-bit block's XOR
def CrBlk64.xor(a: L.LcBlock64, b: L.LcBlock64) -> L.LcBlock64:
  match a b:
    case L.LcBlock64{a0, a1} L.LcBlock64{b0, b1}:
      L.LcBlock64{U32.xor(a0, b0), U32.xor(a1, b1)}
