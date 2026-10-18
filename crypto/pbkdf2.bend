# PBKDF2 over any MAC (RFC 8018, PKCS #5 v2.1, section 5.2), on the MAC
# interface (mac.bend) as its pseudorandom function PRF:
#   DK = T_1 || T_2 || ... , cut to dkLen bytes,
#   T_i = F(P, S, c, i) = U_1 xor U_2 xor ... xor U_c,
#   U_1 = PRF(P, S || INT(i)), U_j = PRF(P, U_(j-1)),
# INT(i) the four-byte big-endian block index, from 1. The PRF's key is the
# password P; a MAC that refuses P's length refuses the derivation (its own
# CrError). In practice the PRF is HMAC over a hash (hmac.bend); any MAC
# with hLen-byte tags will do.
#
# Refused (RFC 8018 step 1, and the iteration count's lower bound): an
# iteration count c of 0 (CrTooShort{0}: too few iterations), an output
# longer than (2^32 - 1) hLen bytes, or any output when hLen is 0
# (CrBadOutputLength{dkLen}).
#
# The output is generated a byte at a time, each T_i computed when the
# bytes before it are used up, so its length is dkLen for every MAC and
# input (LAWS.bend: pbkdf2_length), and a shorter output is a prefix of a
# longer one (pbkdf2_stream_prefix). As a KDF (kdf.bend), PBKDF2 over a MAC
# (~K, ~key, ~compute, and its tag length ~hlen) with c iterations is
#   ~CrPbkdf2.derive(~K, ~key, ~compute, ~hlen, ~c)
# whose context argument (info) is unused: PBKDF2 has none. The named
# instances (PBKDF2-HMAC-SHA-256 and PBKDF2-HMAC-SHA-1) are in
# inst_pbkdf2.bend.
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr

# bytewise XOR of two tags (as long as the shorter)
def cr.pbkdf2.xor(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      Con{U32.xor(x, y), cr.pbkdf2.xor(xt, yt)}
    case _ _:
      Nil{}

# acc xor U_(j+1) xor ... for c more iterations, u = U_j
def cr.pbkdf2.chain(~K: Data, ~compute: K -> B.Octets -> B.Octets, c: Nat, +k: K, u: B.Octets, acc: List<&2, U32>) -> List<&2, U32>:
  match c:
    case 0n:
      acc
    case 1n+p:
      +u2 = compute(k, u)
      cr.pbkdf2.chain(~K, ~compute, p, k, u2, cr.pbkdf2.xor(acc, B.Octets.to_list(u2)))

# T_i, with c the iteration count less one
def cr.pbkdf2.block(~K: Data, ~compute: K -> B.Octets -> B.Octets, +k: K, salt: B.Octets, c: Nat, i: U32) -> List<&2, U32>:
  +u1 = compute(k, B.Octets.append(salt, B.Octets.be32(i)))
  cr.pbkdf2.chain(~K, ~compute, c, k, u1, B.Octets.to_list(u1))

def cr.pbkdf2.head(xs: List<&2, U32>) -> U32:
  match xs:
    case Con{h, t}:
      h
    case Nil{}:
      0

def cr.pbkdf2.tail(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{h, t}:
      t
    case Nil{}:
      Nil{}

# n more bytes: the rest of the current block cur, then T_(i+1), T_(i+2), ...
# (a MAC whose tags are empty gives zeros)
def cr.pbkdf2.out(~K: Data, ~compute: K -> B.Octets -> B.Octets, n: Nat, cur: List<&2, U32>, +k: K, +salt: B.Octets, +c: Nat, +i: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match cur:
        case Con{h, t}:
          Con{h, cr.pbkdf2.out(~K, ~compute, p, t, k, salt, c, i)}
        case Nil{}:
          +blk = cr.pbkdf2.block(~K, ~compute, k, salt, c, U32.add(i, 1))
          Con{cr.pbkdf2.head(blk), cr.pbkdf2.out(~K, ~compute, p, cr.pbkdf2.tail(blk), k, salt, c, U32.add(i, 1))}

# The first n bytes of the derived key, under a prepared key k (the MAC's,
# from the password) and an iteration count c of at least 1, without the
# checks: T_1 || T_2 || ... cut to n bytes
def CrPbkdf2.stream(~K: Data, ~compute: K -> B.Octets -> B.Octets, k: K, salt: B.Octets, c: U32, n: Nat) -> B.Octets:
  B.Octets.of_list(cr.pbkdf2.out(~K, ~compute, n, Nil{}, k, salt, Nat.sub(U32.to_nat(c), 1n), 0))

def cr.pbkdf2.key(~K: Data, ~compute: K -> B.Octets -> B.Octets, kr: Result<&2, &2, Cr.CrError, K>, salt: B.Octets, c: U32, n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match kr:
    case Fail{e}:
      Fail{e}
    case Done{k}:
      Done{CrPbkdf2.stream(~K, ~compute, k, salt, c, n)}

def cr.pbkdf2.checked(~K: Data, ~compute: K -> B.Octets -> B.Octets, zero: Bool, fits: Bool, kr: Result<&2, &2, Cr.CrError, K>, salt: B.Octets, c: U32, +n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  match zero:
    case True{}:
      Fail{Cr.CrTooShort{0n}}
    case False{}:
      match fits:
        case False{}:
          Fail{Cr.CrBadOutputLength{n}}
        case True{}:
          cr.pbkdf2.key(~K, ~compute, kr, salt, c, n)

def cr.pbkdf2.fits(pos: Bool, +n: Nat, +hlen: Nat) -> Bool:
  match pos:
    case True{}:
      Nat.is_le(Nat.div(Nat.add(n, Nat.sub(hlen, 1n)), hlen), 4294967295n)
    case False{}:
      False{}

# DK = PBKDF2(P, S, c, dkLen) over the MAC (~K, ~key, ~compute) with
# hLen-byte tags (~hlen)
def CrPbkdf2.pbkdf2(~K: Data, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~compute: K -> B.Octets -> B.Octets, ~hlen: Nat, password: B.Octets, salt: B.Octets, +c: U32, +n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  cr.pbkdf2.checked(~K, ~compute, U32.is_eq(c, 0), cr.pbkdf2.fits(Nat.is_lt(0n, hlen), n, hlen), key(password), salt, c, n)

# The KDF interface's ~derive (secret, salt, info, length) for c iterations;
# info is unused
def CrPbkdf2.derive(~K: Data, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, ~compute: K -> B.Octets -> B.Octets, ~hlen: Nat, ~c: U32, secret: B.Octets, salt: B.Octets, info: B.Octets, n: Nat) -> Result<&2, &2, Cr.CrError, B.Octets>:
  CrPbkdf2.pbkdf2(~K, ~key, ~compute, ~hlen, secret, salt, c, n)
