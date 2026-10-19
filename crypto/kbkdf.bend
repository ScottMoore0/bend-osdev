# Key derivation using pseudorandom functions (NIST SP 800-108r1-upd1,
# "Recommendation for Key Derivation Using Pseudorandom Functions", L.
# Chen, August 2022), over any MAC (mac.bend) as the PRF:
#   counter mode (section 4.1):  K(i) = PRF(K_IN, [i]_2 || fixed),
#   feedback mode (section 4.2): K(i) = PRF(K_IN, K(i-1) {|| [i]_2} || fixed),
#                                K(0) = IV,
# for i = 1 to n, K_OUT the leftmost L bits of K(1) || K(2) || ..., with
# the fixed input data Label || 0x00 || Context || [L]_2 (section 4). The
# counter [i]_2 is r bits; the encoding of L is a field of its own length.
# Both are template arguments in bytes (~rlen, ~llen: 4 and 4, 32 bits, the
# usual choice); in feedback mode ~rlen = 0 leaves the counter out.
#
# The output is generated a byte at a time, each K(i) computed when the
# bytes before it are used up, so a stream has the length asked for, and a
# shorter stream is a prefix of a longer one with the same fixed input
# (LAWS.bend: kbkdf_*). A derivation of L bits binds L into every PRF input,
# so the derivations of two lengths are not prefixes of each other: the
# KDF interface's prefix law holds of the streams, not of the derivations.
#
# Refused: more than 2^r - 1 blocks in counter mode, or 2^32 - 1 in feedback
# mode (CrBadOutputLength); an L that does not fit its field
# (CrBadOutputLength); and the MAC's own refusal of K_IN. As a KDF
# (kdf.bend) in counter mode, the secret is K_IN, the salt the Label and the
# info the Context: ~CrKbkdf.derive(~K, ~key, ~compute, ~hlen, ~rlen, ~llen).
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr

def cr.kb.head(xs: List<&2, U32>) -> U32:
  match xs:
    case Con{h, t}:
      h
    case Nil{}:
      0

def cr.kb.tail(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{h, t}:
      t
    case Nil{}:
      Nil{}

# [i]_2 as rlen bytes (the low 8 rlen bits of i, big-endian)
def CrKbkdf.counter(+rlen: Nat, i: U32) -> B.Octets:
  B.Octets.drop(Nat.sub(4n, rlen), B.Octets.be32(i))

# n more bytes in counter mode: the rest of the current block cur, then
# PRF(K_IN, [i + 1]_2 || fixed), ...
def cr.kb.ctr(~K: Data, ~compute: K -> B.Octets -> B.Octets, n: Nat, cur: List<&2, U32>, +k: K, +rlen: Nat, +fixed: B.Octets, +i: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match cur:
        case Con{h, t}:
          Con{h, cr.kb.ctr(~K, ~compute, p, t, k, rlen, fixed, i)}
        case Nil{}:
          +blk = B.Octets.to_list(compute(k, B.Octets.append(CrKbkdf.counter(rlen, U32.add(i, 1)), fixed)))
          Con{cr.kb.head(blk), cr.kb.ctr(~K, ~compute, p, cr.kb.tail(blk), k, rlen, fixed, U32.add(i, 1))}

# The first n bytes of counter mode under the prepared key k with the fixed
# input data, unchecked
def CrKbkdf.counter_stream(~K: Data, ~compute: K -> B.Octets -> B.Octets, ~rlen: Nat, k: K, fixed: B.Octets, n: Nat) -> B.Octets:
  B.Octets.of_list(cr.kb.ctr(~K, ~compute, n, Nil{}, k, rlen, fixed, 0))

# n more bytes in feedback mode: the rest of the current block cur, then
# PRF(K_IN, K(i) || [i + 1]_2 || fixed), with prev = K(i)
def cr.kb.fb(~K: Data, ~compute: K -> B.Octets -> B.Octets, n: Nat, cur: List<&2, U32>, +k: K, +rlen: Nat, +fixed: B.Octets, +prev: B.Octets, +i: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match cur:
        case Con{h, t}:
          Con{h, cr.kb.fb(~K, ~compute, p, t, k, rlen, fixed, prev, i)}
        case Nil{}:
          +blk = compute(k, B.Octets.append(prev, B.Octets.append(CrKbkdf.counter(rlen, U32.add(i, 1)), fixed)))
          +bl = B.Octets.to_list(blk)
          Con{cr.kb.head(bl), cr.kb.fb(~K, ~compute, p, cr.kb.tail(bl), k, rlen, fixed, blk, U32.add(i, 1))}

# The first n bytes of feedback mode under the prepared key k from the IV,
# with the fixed input data (rlen 0: no counter), unchecked
def CrKbkdf.feedback_stream(~K: Data, ~compute: K -> B.Octets -> B.Octets, ~rlen: Nat, k: K, iv: B.Octets, fixed: B.Octets, n: Nat) -> B.Octets:
  B.Octets.of_list(cr.kb.fb(~K, ~compute, n, Nil{}, k, rlen, fixed, iv, 0))

# [L]_2: L = 8 n bits as llen big-endian bytes
def CrKbkdf.length(+llen: Nat, +n: Nat) -> B.Octets:
  B.Octets.drop(Nat.sub(4n, llen), B.Octets.be32(U32.from_nat(Nat.mul(8n, n))))

# the fixed input data Label || 0x00 || Context || [L]_2 for n bytes
def CrKbkdf.fixed(~llen: Nat, label: B.Octets, context: B.Octets, +n: Nat) -> B.Octets:
  B.Octets.concat([label, B.Octets.of_list([0]), context, CrKbkdf.length(llen, n)])

# whether n bytes need at most max blocks of hlen bytes, and L = 8 n fits
# llen bytes (and 32 bits)
def cr.kb.fits(+hlen: Nat, +llen: Nat, +n: Nat, +max: Nat) -> Bool:
  Bool.and(Bool.and(Nat.is_lt(0n, hlen), Nat.is_le(Nat.div(Nat.add(n, Nat.sub(hlen, 1n)), hlen), max)), Nat.is_lt(Nat.mul(8n, n), Nat.pow(2n, Nat.mul(8n, Nat.min(llen, 4n)))))

def cr.kb.key(~K: Data, ~compute: K -> B.Octets -> B.Octets, ~rlen: Nat, kr: Result<&2, &2, Cr.CrError, K>, fixed: B.Octets, n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match kr:
    case Fail{e}:
      Fail{e}
    case Done{k}:
      Done{CrKbkdf.counter_stream(~K, ~compute, ~rlen, k, fixed, n)}

def cr.kb.checked(~K: Data, ~compute: K -> B.Octets -> B.Octets, ~rlen: Nat, fits: Bool, kr: Result<&2, &2, Cr.CrError, K>, fixed: B.Octets, +n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match fits:
    case False{}:
      Fail{Cr.CrBadOutputLength{n}}
    case True{}:
      cr.kb.key(~K, ~compute, ~rlen, kr, fixed, n)

# K_OUT of n bytes in counter mode over the MAC (~K, ~key, ~compute) with
# hlen-byte tags, an r = 8 rlen bit counter and an llen-byte [L]_2
def CrKbkdf.counter_kdf(~K: Data, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~compute: K -> B.Octets -> B.Octets, ~hlen: Nat, ~rlen: Nat, ~llen: Nat, ki: B.Octets, label: B.Octets, context: B.Octets, +n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  +max = Nat.sub(Nat.pow(2n, Nat.mul(8n, rlen)), 1n)
  cr.kb.checked(~K, ~compute, ~rlen, cr.kb.fits(hlen, llen, n, max), key(ki), CrKbkdf.fixed(~llen, label, context, n), n)

def cr.kb.fkey(~K: Data, ~compute: K -> B.Octets -> B.Octets, ~rlen: Nat, kr: Result<&2, &2, Cr.CrError, K>, iv: B.Octets, fixed: B.Octets, n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match kr:
    case Fail{e}:
      Fail{e}
    case Done{k}:
      Done{CrKbkdf.feedback_stream(~K, ~compute, ~rlen, k, iv, fixed, n)}

def cr.kb.fchecked(~K: Data, ~compute: K -> B.Octets -> B.Octets, ~rlen: Nat, fits: Bool, kr: Result<&2, &2, Cr.CrError, K>, iv: B.Octets, fixed: B.Octets, +n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match fits:
    case False{}:
      Fail{Cr.CrBadOutputLength{n}}
    case True{}:
      cr.kb.fkey(~K, ~compute, ~rlen, kr, iv, fixed, n)

# K_OUT of n bytes in feedback mode from the IV (rlen 0: no counter)
def CrKbkdf.feedback_kdf(~K: Data, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~compute: K -> B.Octets -> B.Octets, ~hlen: Nat, ~rlen: Nat, ~llen: Nat, ki: B.Octets, iv: B.Octets, label: B.Octets, context: B.Octets, +n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  cr.kb.fchecked(~K, ~compute, ~rlen, cr.kb.fits(hlen, llen, n, 4294967295n), key(ki), iv, CrKbkdf.fixed(~llen, label, context, n), n)

# The KDF interface's ~derive in counter mode: secret K_IN, salt the Label,
# info the Context
def CrKbkdf.derive(~K: Data, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~compute: K -> B.Octets -> B.Octets, ~hlen: Nat, ~rlen: Nat, ~llen: Nat, secret: B.Octets, salt: B.Octets, info: B.Octets, n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  CrKbkdf.counter_kdf(~K, ~key, ~compute, ~hlen, ~rlen, ~llen, secret, salt, info, n)
