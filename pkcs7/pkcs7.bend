# PKCS #7 padding (RFC 5652, section 6.3): a message is padded to a whole
# number of blocks by appending p bytes of value p, 1 <= p <= the block size,
# so a message that already fills its blocks gains a whole block of padding.
# The block size is a parameter (1 to 255); CBC uses 16.
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M

# n bytes of value v
def pkcs7.fill(n: Nat, +v: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{v, pkcs7.fill(p, v)}

def pkcs7.size_ok(+bs: Nat) -> Bool:
  Bool.and(Nat.is_lt(0n, bs), Nat.is_lt(bs, 256n))

# m and its padding (on Octets, so that a long message is not walked as a
# list: Bend 2.0.37's runtime overflows its stack on deep structural
# recursion)
def pkcs7.pad.oct(+bs: Nat, +m: B.Octets) -> B.Octets:
  +p = Nat.sub(bs, Nat.mod(B.Octets.len(m), bs))
  B.Octets.append(m, B.Octets.of_list(pkcs7.fill(p, U32.from_nat(p))))

def Pkcs7.pad.go(ok: Bool, +bs: Nat, m: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  match ok:
    case True{}:
      Done{pkcs7.pad.oct(bs, m)}
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

# the last byte, or d if there is none
def pkcs7.last(m: Maybe<&2, U32>, d: U32) -> U32:
  match m:
    case Some{b}:
      b
    case None{}:
      d

def pkcs7.strip(ok: Bool, +n: Nat, +p: Nat, m: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  match ok:
    case True{}:
      Done{B.Octets.take(Nat.sub(n, p), m)}
    case False{}:
      Fail{M.CmBadPadding{}}

# the value p of the last byte must be 1 to bs, and the last p bytes all p
# (on Octets of n bytes, so that only those p bytes become a list)
def pkcs7.unpad.oct(+bs: Nat, +m: B.Octets, +n: Nat) -> Result<&2, &2, M.CmError, B.Octets>:
  +v = pkcs7.last(B.Octets.at(m, Nat.sub(n, 1n)), 0)
  +p = U32.to_nat(v)
  +good = Bool.and(Nat.is_lt(0n, p), Bool.and(Nat.is_le(p, bs), U32.is_eq(pkcs7.diff(B.Octets.to_list(B.Octets.drop(Nat.sub(n, p), m)), v, 0), 0)))
  pkcs7.strip(good, n, p, m)

def Pkcs7.unpad.go(ok: Bool, +bs: Nat, +m: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  match ok:
    case True{}:
      +n = B.Octets.len(m)
      do Result<&2, &2, M.CmError, B.Octets>:
        M.cm.check(Nat.is_lt(0n, n), M.CmTooShort{n})
        M.cm.check(Nat.is_eq(Nat.mod(n, bs), 0n), M.CmNotBlockMultiple{n})
        pkcs7.unpad.oct(bs, m, n)
    case False{}:
      Fail{M.CmBadBlockSize{bs}}

# m without its padding; m must be a non-empty whole number of blocks
def Pkcs7.unpad(+bs: Nat, m: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  Pkcs7.unpad.go(pkcs7.size_ok(bs), bs, m)
