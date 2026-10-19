# MGF1 (RFC 8017, Appendix B.2.1), the mask generation function over any
# hash (~digest: one-shot, as in bend-osdev-crypto's hash interface):
#   T = Hash(mgfSeed || C(0)) || Hash(mgfSeed || C(1)) || ...,
# the first maskLen bytes, C(i) the counter as four big-endian bytes.
#
# The output is generated a byte at a time, each block hashed when the
# bytes before it are used up, so it has the length asked for, whatever the
# hash (LAWS.bend: mgf1_length), and a shorter mask is a prefix of a longer
# one. RFC 8017's "mask too long" (maskLen > 2^32 hLen) cannot arise for the
# lengths an RSA modulus allows, and is not checked.
import Base
import ../bytes/bytes.bend as B

def rsa.mgf.head(xs: List<&2, U32>) -> U32:
  match xs:
    case Con{h, t}:
      h
    case Nil{}:
      0

def rsa.mgf.tail(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{h, t}:
      t
    case Nil{}:
      Nil{}

# n more bytes: the rest of the current block cur, then Hash(seed || C(i)),
# Hash(seed || C(i + 1)), ...
def rsa.mgf.out(~digest: B.Octets -> B.Octets, n: Nat, cur: List<&2, U32>, +seed: B.Octets, +i: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match cur:
        case Con{h, t}:
          Con{h, rsa.mgf.out(~digest, p, t, seed, i)}
        case Nil{}:
          +blk = B.Octets.to_list(digest(B.Octets.append(seed, B.Octets.be32(i))))
          Con{rsa.mgf.head(blk), rsa.mgf.out(~digest, p, rsa.mgf.tail(blk), seed, U32.add(i, 1))}

# MGF1(mgfSeed, maskLen) over the hash ~digest
def RsaMgf1.mask(~digest: B.Octets -> B.Octets, seed: B.Octets, n: Nat) -> B.Octets:
  B.Octets.of_list(rsa.mgf.out(~digest, n, Nil{}, seed, 0))
