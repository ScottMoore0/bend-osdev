# PKCS #7 padding (RFC 5652, section 6.3): a message is padded to a whole
# number of blocks by appending p bytes of value p, 1 <= p <= the block size,
# so a message that already fills its blocks gains a whole block of padding.
# The block size is a parameter (1 to 255); CBC uses 16.
import Base
import ../bytes/bytes.bend as B
import ./cipher-modes.bend as M

# n bytes of value v
def pkcs7.fill(n: Nat, +v: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{v, pkcs7.fill(p, v)}

def pkcs7.size_ok(+bs: Nat) -> Bool:
  Bool.and(Nat.is_lt(0n, bs), Nat.is_lt(bs, 256n))

def pkcs7.pad.list(+bs: Nat, +xs: List<&2, U32>) -> List<&2, U32>:
  +p = Nat.sub(bs, Nat.mod(B.len(xs), bs))
  B.append(xs, pkcs7.fill(p, U32.from_nat(p)))

def Pkcs7.pad.go(ok: Bool, +bs: Nat, m: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  match ok:
    case True{}:
      Done{B.Octets.of_list(pkcs7.pad.list(bs, B.Octets.to_list(m)))}
    case False{}:
      Fail{M.CmBadBlockSize{bs}}

# m padded to a whole number of bs-byte blocks
def Pkcs7.pad(+bs: Nat, m: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  Pkcs7.pad.go(pkcs7.size_ok(bs), bs, m)

# Unpadding. The checks do not stop at the first bad byte, but the result
# (padding good or bad) is visible to the caller: see the README on padding
# oracles.

# 0 when every byte of xs is v
def pkcs7.diff(xs: List<&2, U32>, +v: U32, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      pkcs7.diff(t, v, U32.or(acc, U32.xor(M.cm.byte(h), v)))

def pkcs7.last(xs: List<&2, U32>, d: U32) -> U32:
  match xs:
    case Nil{}:
      d
    case Con{h, t}:
      pkcs7.last(t, M.cm.byte(h))

def pkcs7.strip(ok: Bool, +n: Nat, +p: Nat, xs: List<&2, U32>) -> Result<&2, &2, M.CmError, B.Octets>:
  match ok:
    case True{}:
      Done{B.Octets.of_list(B.take(Nat.sub(n, p), xs))}
    case False{}:
      Fail{M.CmBadPadding{}}

# the value p of the last byte must be 1 to bs, and the last p bytes all p
def pkcs7.unpad.list(+bs: Nat, +xs: List<&2, U32>) -> Result<&2, &2, M.CmError, B.Octets>:
  +n = B.len(xs)
  +v = pkcs7.last(xs, 0)
  +p = U32.to_nat(v)
  +good = Bool.and(Nat.is_lt(0n, p), Bool.and(Nat.is_le(p, bs), U32.is_eq(pkcs7.diff(B.drop(Nat.sub(n, p), xs), v, 0), 0)))
  pkcs7.strip(good, n, p, xs)

def Pkcs7.unpad.go(ok: Bool, +bs: Nat, m: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  match ok:
    case True{}:
      +xs = B.Octets.to_list(m)
      +n = B.len(xs)
      do Result<&2, &2, M.CmError, B.Octets>:
        M.cm.check(Nat.is_lt(0n, n), M.CmTooShort{n})
        M.cm.check(Nat.is_eq(Nat.mod(n, bs), 0n), M.CmNotBlockMultiple{n})
        pkcs7.unpad.list(bs, xs)
    case False{}:
      Fail{M.CmBadBlockSize{bs}}

# m without its padding; m must be a non-empty whole number of blocks
def Pkcs7.unpad(+bs: Nat, m: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  Pkcs7.unpad.go(pkcs7.size_ok(bs), bs, m)
