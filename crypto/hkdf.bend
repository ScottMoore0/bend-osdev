# HKDF over any hash (RFC 5869), on HMAC (hmac.bend):
#   PRK = HMAC(salt, IKM), the salt dsize zero bytes when it is empty
#   T(0) = empty, T(i) = HMAC(PRK, T(i-1) || info || i), i = 1 .. N
#   OKM = the first len bytes of T(1) || T(2) || ... || T(N), N = ceil(len/dsize)
# len is at most 255 dsize (CrBadOutputLength otherwise). As a KDF
# (kdf.bend), HKDF over a hash (~bsize, ~dsize, ~digest, from its
# interface) is the instance ~CrHkdf.derive(~bsize, ~dsize, ~digest).
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr
import ./hmac.bend as Hm

def cr.hkdf.salt(empty: Bool, +n: Nat, +salt: B.Octets) -> B.Octets:
  match empty:
    case True{}:
      B.Octets.zeros(n)
    case False{}:
      salt

# Extract: the pseudorandom key of the input keying material ikm
def CrHkdf.extract(~bsize: Nat, ~dsize: Nat, ~digest: B.Octets -> B.Octets, +salt: B.Octets, ikm: B.Octets) -> B.Octets:
  Hm.CrHmac.mac(~digest, Hm.CrHmac.key(~bsize, ~digest, cr.hkdf.salt(Nat.is_eq(B.Octets.len(salt), 0n), dsize, salt)), ikm)

# T(i) .. T(i+n-1), last first, onto acc (prev is T(i-1), ctr the byte i)
def cr.hkdf.blocks(~digest: B.Octets -> B.Octets, n: Nat, +kk: Hm.CrHmacKey, +info: B.Octets, prev: B.Octets, +ctr: U32, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +t = Hm.CrHmac.mac(~digest, kk, B.Octets.append(prev, B.Octets.append(info, B.Octets.of_list([ctr]))))
      cr.hkdf.blocks(~digest, p, kk, info, t, U32.add(ctr, 1), Con{t, acc})

def cr.hkdf.rev(os: List<&2, B.Octets>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match os:
    case Nil{}:
      acc
    case Con{h, t}:
      cr.hkdf.rev(t, Con{h, acc})

def cr.hkdf.expand(~bsize: Nat, ~dsize: Nat, ~digest: B.Octets -> B.Octets, ok: Bool, +prk: B.Octets, +info: B.Octets, +len: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match ok:
    case False{}:
      Fail{Cr.CrBadOutputLength{len}}
    case True{}:
      +n = Nat.div(Nat.add(len, Nat.sub(dsize, 1n)), dsize)
      +ts = cr.hkdf.blocks(~digest, n, Hm.CrHmac.key(~bsize, ~digest, prk), info, B.Octets.empty(), 1, Nil{})
      Done{B.Octets.take(len, B.Octets.concat(cr.hkdf.rev(ts, Nil{})))}

def cr.hkdf.ok(pos: Bool, +len: Nat, +dsize: Nat) -> Bool:
  match pos:
    case True{}:
      Nat.is_le(len, Nat.mul(255n, dsize))
    case False{}:
      False{}

# Expand: len bytes of output keying material from the pseudorandom key
def CrHkdf.expand(~bsize: Nat, ~dsize: Nat, ~digest: B.Octets -> B.Octets, +prk: B.Octets, +info: B.Octets, +len: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  cr.hkdf.expand(~bsize, ~dsize, ~digest, cr.hkdf.ok(Nat.is_lt(0n, dsize), len, dsize), prk, info, len)

# Extract, then expand: the KDF interface's ~derive (secret, salt, info, len)
def CrHkdf.derive(~bsize: Nat, ~dsize: Nat, ~digest: B.Octets -> B.Octets, ikm: B.Octets, salt: B.Octets, info: B.Octets, len: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  CrHkdf.expand(~bsize, ~dsize, ~digest, CrHkdf.extract(~bsize, ~dsize, ~digest, salt, ikm), info, len)
