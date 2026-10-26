# Laws of PKCS #7 padding (pkcs7.bend), for every block size and message:
# unpadding undoes padding, and padding gives a whole number of blocks; and
# RFC 5652's padding examples, with the refusals of bad padding. The proofs
# rest on bytes' and u32's laws only.
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ./pkcs7.bend as P

# Unpadding undoes padding, for every block size bs and message m: when bs
# is one the padding takes (1 to 255), unpad(pad(m)) is m; when it is not,
# both refuse alike (CmBadBlockSize)
law pkcs7_round_trip:
  for +bs: Nat
  for +m: B.Octets
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, P.Pkcs7.pad(bs, m), c => P.Pkcs7.unpad(bs, c)) == Result.map(&2, &2, M.CmError, B.Octets, B.Octets, c => m, P.Pkcs7.pad(bs, m)) : Result<&2, &2, M.CmError, B.Octets>}

# A padded message is a whole number of blocks, for every block size and
# message
law pkcs7_pad_blocks:
  for +bs: Nat
  for +m: B.Octets
  {Result.map(&2, &2, M.CmError, B.Octets, Nat, c => Nat.mod(B.Octets.len(c), bs), P.Pkcs7.pad(bs, m)) == Result.map(&2, &2, M.CmError, B.Octets, Nat, c => 0n, P.Pkcs7.pad(bs, m)) : Result<&2, &2, M.CmError, Nat>}

# Unpadding refuses an empty string (CmTooShort), for every block size the
# padding takes (1 to 255)
law pkcs7_unpad_empty:
  for +bs: Nat
  for +m: B.Octets
  for h0: {Nat.is_lt(0n, bs) == True{} : Bool}
  for h1: {Nat.is_lt(bs, 256n) == True{} : Bool}
  for h: {B.Octets.len(m) == 0n : Nat}
  {P.Pkcs7.unpad(bs, m) == Fail{M.CmTooShort{0n}} : Result<&2, &2, M.CmError, B.Octets>}

# PKCS #7 (RFC 5652, 6.3): the empty message becomes a whole block of 16s; 15 bytes gain one 1
law pkcs7_pad_empty:
  {P.Pkcs7.pad(16n, B.Octets.empty()) == Done{B.Octets.of_list([16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16])} : Result<&2, &2, M.CmError, B.Octets>}

law pkcs7_pad_15:
  {P.Pkcs7.pad(16n, B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23])) == Done{B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 1])} : Result<&2, &2, M.CmError, B.Octets>}

law pkcs7_unpad_15:
  {P.Pkcs7.unpad(16n, B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 1])) == Done{B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23])} : Result<&2, &2, M.CmError, B.Octets>}

# a last byte of 0, or one the bytes before it contradict, is bad padding
law pkcs7_unpad_zero:
  {P.Pkcs7.unpad(16n, B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 147, 23, 0])) == Fail{M.CmBadPadding{}} : Result<&2, &2, M.CmError, B.Octets>}

law pkcs7_unpad_mixed:
  {P.Pkcs7.unpad(16n, B.Octets.of_list([107, 193, 190, 226, 46, 64, 159, 150, 233, 61, 126, 17, 115, 2, 3, 3])) == Fail{M.CmBadPadding{}} : Result<&2, &2, M.CmError, B.Octets>}
