# bend-osdev-kstr's hexadecimal round trips, for every input: %x and %X
# (KStr.format, KStr.format32) parsed in base 16 (KStr.to_u64,
# KStr.to_u32) give the value back. Proved in PROOF_hex.bend.
import Base
import ../word64/word64.bend as W
import ./kstr.bend as K
import ./format.bend as F

law x64_round_trip:
  for +v: W.W64
  {K.KStr.to_u64(F.KStr.format(F.KFmt.plain(F.KConvX{}), v), 16) == Done{v} : Result<&2, &2, K.KStrError, W.W64>}

law x32_round_trip:
  for +v: U32
  {K.KStr.to_u32(F.KStr.format32(F.KFmt.plain(F.KConvX{}), v), 16) == Done{v} : Result<&2, &2, K.KStrError, U32>}

law xu64_round_trip:
  for +v: W.W64
  {K.KStr.to_u64(F.KStr.format(F.KFmt.plain(F.KConvXUpper{}), v), 16) == Done{v} : Result<&2, &2, K.KStrError, W.W64>}

law xu32_round_trip:
  for +v: U32
  {K.KStr.to_u32(F.KStr.format32(F.KFmt.plain(F.KConvXUpper{}), v), 16) == Done{v} : Result<&2, &2, K.KStrError, U32>}
