# Laws of PKCS #7 padding (pkcs7.bend), for every block size and message:
# unpadding undoes padding, and padding gives a whole number of blocks.
# They are in a pair of their own (CONVENTIONS.md, Laws): their proofs rest
# on bytes' laws only, so a proof that uses them takes in none of AES's.
import Base
import ../bytes/bytes.bend as B
import ./cipher-modes.bend as M
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
