# bend-osdev-kstr's octal round trips, for every input: %o (KStr.format,
# KStr.format32) parsed in base 8 (KStr.to_u64, KStr.to_u32) gives the
# value back. Proved in PROOF_oct.bend.
import Base
import ../word64/word64.bend as W
import ./kstr.bend as K
import ./format.bend as F

law oct64_round_trip:
  for +v: W.W64
  {K.KStr.to_u64(F.KStr.format(F.KFmt.plain(F.KConvO{}), v), 8) == Done{v} : Result<&2, &2, K.KStrError, W.W64>}

law oct32_round_trip:
  for +v: U32
  {K.KStr.to_u32(F.KStr.format32(F.KFmt.plain(F.KConvO{}), v), 8) == Done{v} : Result<&2, &2, K.KStrError, U32>}
