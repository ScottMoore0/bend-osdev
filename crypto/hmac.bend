# HMAC over any hash (RFC 2104; FIPS 198-1), on the hash interface
# (hash.bend):
#   K0 = the key, hashed first if it is longer than the block size B, then
#        zero-padded to B bytes
#   HMAC(K, m) = H((K0 xor opad) || H((K0 xor ipad) || m)),
#   ipad = B bytes of 0x36, opad = B bytes of 0x5c.
#
# The key is prepared once (CrHmac.key: the two padded keys); the tag is
# computed in one call (CrHmac.mac, with the hash's one-shot ~digest) or in
# pieces (CrHmac.start, update, finish, with its streaming interface). As a
# MAC (mac.bend), HMAC over a hash (~H, ~bsize, ~dsize, ~init, ~update,
# ~final, ~digest) is the instance
#   ~CrHmacKey, ~CrHmac.key_of(~bsize, ~digest), ~CrHmac.mac(~digest),
#   ~CrMac.verify_tag(~CrHmacKey, ~CrHmac.mac(~digest))
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr
import ./mac.bend as Mc

# The prepared key: K0 xor ipad and K0 xor opad (open type)
type CrHmacKey is Data:
  CrHmacKey{ipad: B.Octets, opad: B.Octets}

# The state in pieces: the inner hash's state, and the outer padded key
type CrHmacState<-H: Data> is Data:
  CrHmacState{inner: H, opad: B.Octets}

def cr.hmac.pad(xs: List<&2, U32>, +c: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{B.byte(U32.xor(x, c)), cr.hmac.pad(t, c)}

def cr.hmac.k0(~digest: B.Octets -> B.Octets, long: Bool, +key: B.Octets) -> B.Octets:
  match long:
    case True{}:
      digest(key)
    case False{}:
      key

# K0: the key (hashed if longer than bsize), zero-padded to bsize bytes
def cr.hmac.block(~bsize: Nat, ~digest: B.Octets -> B.Octets, +key: B.Octets) -> List<&2, U32>:
  +k = cr.hmac.k0(~digest, Nat.is_lt(bsize, B.Octets.len(key)), key)
  B.append(B.Octets.to_list(k), B.zeros(Nat.sub(bsize, B.Octets.len(k))))

# The prepared key of a raw key of any length
def CrHmac.key(~bsize: Nat, ~digest: B.Octets -> B.Octets, key: B.Octets) -> CrHmacKey:
  +k0 = cr.hmac.block(~bsize, ~digest, key)
  CrHmacKey{B.Octets.of_list(cr.hmac.pad(k0, 54)), B.Octets.of_list(cr.hmac.pad(k0, 92))}

# the same as the MAC interface's ~key (every key length is allowed)
def CrHmac.key_of(~bsize: Nat, ~digest: B.Octets -> B.Octets, key: B.Octets) -> Result<&2, &2, Cr.CrError, CrHmacKey>:
  Done{CrHmac.key(~bsize, ~digest, key)}

# The tag of m, in one call
def CrHmac.mac(~digest: B.Octets -> B.Octets, kk: CrHmacKey, m: B.Octets) -> B.Octets:
  match kk:
    case CrHmacKey{i, o}:
      digest(B.Octets.append(o, digest(B.Octets.append(i, m))))

# whether t is m's tag (every byte compared)
def CrHmac.verify(~digest: B.Octets -> B.Octets, kk: CrHmacKey, m: B.Octets, t: B.Octets) -> Bool:
  Mc.CrMac.verify_tag(~CrHmacKey, ~CrHmac.mac(~digest), kk, m, t)

# The tag in pieces: start, update for each piece, finish
def CrHmac.start(~H: Data, ~init: H, ~update: H -> B.Octets -> H, kk: CrHmacKey) -> CrHmacState<H>:
  match kk:
    case CrHmacKey{i, o}:
      CrHmacState{update(init, i), o}

def CrHmac.update(~H: Data, ~update: H -> B.Octets -> H, s: CrHmacState<H>, m: B.Octets) -> CrHmacState<H>:
  match s:
    case CrHmacState{h, o}:
      CrHmacState{update(h, m), o}

def CrHmac.finish(~H: Data, ~init: H, ~update: H -> B.Octets -> H, ~final: H -> B.Octets, s: CrHmacState<H>) -> B.Octets:
  match s:
    case CrHmacState{h, o}:
      final(update(update(init, o), final(h)))
