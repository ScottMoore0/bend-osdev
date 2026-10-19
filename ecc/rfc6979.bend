# Deterministic per-message secret numbers (RFC 6979, "Deterministic Usage
# of the Digital Signature Algorithm (DSA) and Elliptic Curve Digital
# Signature Algorithm (ECDSA)", 2013, section 3.2; FIPS 186-5 Appendix
# A.3.3 adopts it), over any HMAC (~mac: key, data -> tag; HMAC over the
# hash that made h1):
#   V = 0x01 * hlen, K = 0x00 * hlen,
#   K = HMAC_K(V || 0x00 || int2octets(x) || bits2octets(h1)), V = HMAC_K(V),
#   K = HMAC_K(V || 0x01 || int2octets(x) || bits2octets(h1)), V = HMAC_K(V),
#   then T = V's of HMAC_K(V) until T has qlen bits, k = bits2int(T), taken
#   if 1 <= k < q, else K = HMAC_K(V || 0x00), V = HMAC_K(V) and again.
# hlen is h1's length (the HMAC's hash is the message's). The retry loop
# runs at most 64 times (a retry happens with probability below 2^-31 for
# every named curve), then gives 0, which a signer refuses.
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N

# V and the T built from it (open)
type EcDrbgT is Data:
  EcDrbgT{v: B.Octets, t: B.Octets}

def EcDrbgT.v(s: EcDrbgT) -> B.Octets:
  match s:
    case EcDrbgT{v, t}:
      v

def EcDrbgT.t(s: EcDrbgT) -> B.Octets:
  match s:
    case EcDrbgT{v, t}:
      t

# int2octets: x as rlen / 8 bytes, rlen = 8 ceil(qlen / 8)
def EcRfc6979.int2octets(x: N.BnNat, +qlen: Nat) -> B.Octets:
  +l = Nat.div(Nat.add(qlen, 7n), 8n)
  Maybe.default(&2, B.Octets, N.BnNat.to_octets(x, l), B.Octets.zeros(l))

# bits2int: the leftmost qlen bits of b as an integer
def EcRfc6979.bits2int(+b: B.Octets, +qlen: Nat) -> N.BnNat:
  N.BnNat.shr(N.BnNat.of_octets(b), Nat.sub(Nat.mul(8n, B.Octets.len(b)), qlen))

# bits2octets: int2octets(bits2int(b) mod q)
def EcRfc6979.bits2octets(+b: B.Octets, +q: N.BnNat) -> B.Octets:
  +qlen = N.BnNat.bit_len(q)
  EcRfc6979.int2octets(N.BnNat.mod(EcRfc6979.bits2int(b, qlen), q), qlen)

def ec6979.ones(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{1, ec6979.ones(p)}

# V = HMAC_K(V), T = T || V until T has qlen bits (done: it has)
def ec6979.gen(~mac: B.Octets -> B.Octets -> B.Octets, f: Nat, done: Bool, +k: B.Octets, +v: B.Octets, +t: B.Octets, +qlen: Nat) -> EcDrbgT:
  match f:
    case 0n:
      EcDrbgT{v, t}
    case 1n+p:
      match done:
        case True{}:
          EcDrbgT{v, t}
        case False{}:
          +v2 = mac(k, v)
          +t2 = B.Octets.append(t, v2)
          ec6979.gen(~mac, p, Nat.is_le(qlen, Nat.mul(8n, B.Octets.len(t2))), k, v2, t2, qlen)

def ec6979.t(~mac: B.Octets -> B.Octets -> B.Octets, +k: B.Octets, +v: B.Octets, +qlen: Nat) -> EcDrbgT:
  ec6979.gen(~mac, Nat.add(qlen, 1n), False{}, k, v, B.Octets.empty(), qlen)

def ec6979.ok(+k: N.BnNat, +q: N.BnNat) -> Bool:
  Bool.and(Bool.not(N.BnNat.is_zero(k)), N.BnNat.is_lt(k, q))

# step h: the candidate kk is taken when ok, else K and V move on
def ec6979.loop(~mac: B.Octets -> B.Octets -> B.Octets, f: Nat, ok: Bool, +kk: N.BnNat, +k: B.Octets, +v: B.Octets, +q: N.BnNat, +qlen: Nat) -> N.BnNat:
  match f:
    case 0n:
      N.BnNat.zero()
    case 1n+p:
      match ok:
        case True{}:
          kk
        case False{}:
          +k2 = mac(k, B.Octets.append(v, B.Octets.of_list([0])))
          +s = ec6979.t(~mac, k2, mac(k2, v), qlen)
          +kk2 = EcRfc6979.bits2int(EcDrbgT.t(s), qlen)
          ec6979.loop(~mac, p, ec6979.ok(kk2, q), kk2, k2, EcDrbgT.v(s), q, qlen)

# k for the private key x and the message hash h1, modulo q (the group
# order n)
def EcRfc6979.k(~mac: B.Octets -> B.Octets -> B.Octets, +q: N.BnNat, x: N.BnNat, +h1: B.Octets) -> N.BnNat:
  +qlen = N.BnNat.bit_len(q)
  +hlen = B.Octets.len(h1)
  +tail = B.Octets.append(EcRfc6979.int2octets(x, qlen), EcRfc6979.bits2octets(h1, q))
  +v1 = B.Octets.of_list(ec6979.ones(hlen))
  +k1 = mac(B.Octets.zeros(hlen), B.Octets.append(v1, B.Octets.append(B.Octets.of_list([0]), tail)))
  +v2 = mac(k1, v1)
  +k2 = mac(k1, B.Octets.append(v2, B.Octets.append(B.Octets.of_list([1]), tail)))
  +v3 = mac(k2, v2)
  +s = ec6979.t(~mac, k2, v3, qlen)
  +kk = EcRfc6979.bits2int(EcDrbgT.t(s), qlen)
  ec6979.loop(~mac, 64n, ec6979.ok(kk, q), kk, k2, EcDrbgT.v(s), q, qlen)
