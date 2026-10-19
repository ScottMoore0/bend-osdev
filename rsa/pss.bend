# EMSA-PSS (RFC 8017, section 9.1) and RSASSA-PSS (section 8.1), over any
# hash (~digest, one-shot; hLen is the length of its output) and any mask
# generation function (~mgf: seed, length; MGF1 over a hash is the usual
# one, RsaMgf1.mask in mgf1.bend):
#   M' = 0x00 * 8 || Hash(M) || salt,  H = Hash(M'),
#   DB = PS || 0x01 || salt,  maskedDB = DB xor MGF(H, emLen - hLen - 1),
#   EM = maskedDB || H || 0xbc,
# with the leftmost 8 emLen - emBits bits of maskedDB cleared. The salt is
# a parameter (random bytes from the caller, of any length sLen, empty
# included); verification takes sLen.
#
# Verification takes EM apart from its pieces' lengths (maskedDB is all but
# the last hLen + 1 bytes), checks the cleared bits by clearing them again
# (nothing may change), masks with as many bytes as maskedDB has, and finds
# the separator 0x01 after the zeros of PS: PS's length is then the rest's
# less sLen + 1, as step 10 asks. The number of cleared bits is
# 8 emLen - emBits = (8 - emBits mod 8) mod 8 (rsa.pss.z). LAWS.bend's
# pss_round_trip proves that verification accepts every encoding.
import Base
import ../bytes/bytes.bend as B
import ../bignum/bignum.bend as N
import ./rsa.bend as R
import ./octets.bend as O

# M' = 0x00 * 8 || mHash || salt
def rsa.pss.mprime(+mhash: B.Octets, salt: B.Octets) -> B.Octets:
  B.Octets.append(B.Octets.zeros(8n), B.Octets.append(mhash, salt))

# emLen = ceil(emBits / 8)
def RsaPss.em_len(+embits: Nat) -> Nat:
  Nat.div(Nat.add(embits, 7n), 8n)

# 8 emLen - emBits, the bits of maskedDB cleared: (8 - e mod 8) mod 8
def rsa.pss.z(e: Nat) -> Nat:
  match e:
    case 0n:
      0n
    case 1n+e1:
      match e1:
        case 0n:
          7n
        case 1n+e2:
          match e2:
            case 0n:
              6n
            case 1n+e3:
              match e3:
                case 0n:
                  5n
                case 1n+e4:
                  match e4:
                    case 0n:
                      4n
                    case 1n+e5:
                      match e5:
                        case 0n:
                          3n
                        case 1n+e6:
                          match e6:
                            case 0n:
                              2n
                            case 1n+e7:
                              match e7:
                                case 0n:
                                  1n
                                case 1n+e8:
                                  rsa.pss.z(e8)

# DB = PS || 0x01 || salt, PS ps zero bytes
def rsa.pss.db(+ps: Nat, +salt: B.Octets) -> B.Octets:
  B.Octets.append(B.Octets.zeros(ps), B.Octets.append(B.Octets.of_list([1]), salt))

# maskedDB || H || 0xbc
def rsa.pss.em(~mgf: B.Octets -> Nat -> B.Octets, +h: B.Octets, +db: B.Octets, +embits: Nat) -> B.Octets:
  B.Octets.append(O.RsaOct.clear_left(O.RsaOct.xor(db, mgf(h, B.Octets.len(db))), rsa.pss.z(embits)), B.Octets.append(h, B.Octets.of_list([188])))

def rsa.pss.enc(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, fits: Bool, +mhash: B.Octets, +salt: B.Octets, +embits: Nat) -> Result<&2, &2, R.RsaError, B.Octets>:
  match fits:
    case False{}:
      Fail{R.RsaEncodingError{}}
    case True{}:
      +ps = Nat.sub(RsaPss.em_len(embits), Nat.add(B.Octets.len(salt), Nat.add(B.Octets.len(mhash), 2n)))
      Done{rsa.pss.em(~mgf, digest(rsa.pss.mprime(mhash, salt)), rsa.pss.db(ps, salt), embits)}

def rsa.pss.enc0(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, +mhash: B.Octets, +salt: B.Octets, +embits: Nat) -> Result<&2, &2, R.RsaError, B.Octets>:
  rsa.pss.enc(~digest, ~mgf, Nat.is_le(Nat.add(B.Octets.len(mhash), Nat.add(B.Octets.len(salt), 2n)), RsaPss.em_len(embits)), mhash, salt, embits)

# EMSA-PSS-ENCODE(M, emBits) with the given salt: RsaEncodingError when
# emLen < hLen + sLen + 2
def RsaPss.encode(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, m: B.Octets, salt: B.Octets, embits: Nat) -> Result<&2, &2, R.RsaError, B.Octets>:
  rsa.pss.enc0(~digest, ~mgf, digest(m), salt, embits)

# the salt after the separator: its length, and H' = Hash(M') against H
def rsa.pss.v4(~digest: B.Octets -> B.Octets, ok: Bool, +mhash: B.Octets, +h: B.Octets, z: Maybe<&2, Nat>, t: List<&2, U32>, +slen: Nat) -> Bool:
  match ok z:
    case True{} Some{i}:
      +salt = B.Octets.of_list(B.drop(Nat.add(i, 1n), t))
      Bool.and(Nat.is_eq(B.Octets.len(salt), slen), B.Octets.is_eq(h, digest(rsa.pss.mprime(mhash, salt))))
    case _ _:
      False{}

def rsa.pss.v3(~digest: B.Octets -> B.Octets, ok: Bool, +mhash: B.Octets, +h: B.Octets, +db: B.Octets, +slen: Nat) -> Bool:
  rsa.pss.v4(~digest, ok, mhash, h, O.rsa.sep(B.Octets.to_list(db)), B.Octets.to_list(db), slen)

# the trailer, the cleared bits, and DB = maskedDB xor MGF(H, its length),
# its leftmost bits cleared
def rsa.pss.v2(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, ok1: Bool, +mhash: B.Octets, +masked: B.Octets, +h: B.Octets, +trailer: B.Octets, +embits: Nat, +slen: Nat) -> Bool:
  +z = rsa.pss.z(embits)
  +ok2 = Bool.and(B.Octets.is_eq(trailer, B.Octets.of_list([188])), B.Octets.is_eq(O.RsaOct.clear_left(masked, z), masked))
  rsa.pss.v3(~digest, Bool.and(ok1, ok2), mhash, h, O.RsaOct.clear_left(O.RsaOct.xor(masked, mgf(h, B.Octets.len(masked))), z), slen)

# H and the trailer from what follows maskedDB
def rsa.pss.v1(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, ok1: Bool, +mhash: B.Octets, +masked: B.Octets, +rest: B.Octets, +embits: Nat, +slen: Nat) -> Bool:
  rsa.pss.v2(~digest, ~mgf, ok1, mhash, masked, B.Octets.take(B.Octets.len(mhash), rest), B.Octets.drop(B.Octets.len(mhash), rest), embits, slen)

def rsa.pss.v0(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, +mhash: B.Octets, +em: B.Octets, +embits: Nat, +slen: Nat) -> Bool:
  +dblen = Nat.sub(B.Octets.len(em), Nat.add(B.Octets.len(mhash), 1n))
  rsa.pss.v1(~digest, ~mgf, Nat.is_le(Nat.add(B.Octets.len(mhash), Nat.add(slen, 2n)), RsaPss.em_len(embits)), mhash, B.Octets.take(dblen, em), B.Octets.drop(dblen, em), embits, slen)

# EMSA-PSS-VERIFY(M, EM, emBits) for a salt of slen bytes: whether EM is
# "consistent" (steps 1 to 14; every failure is "inconsistent")
def RsaPss.check(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, m: B.Octets, em: B.Octets, embits: Nat, slen: Nat) -> Bool:
  rsa.pss.v0(~digest, ~mgf, digest(m), em, embits, slen)

# RSASSA-PSS-SIGN(K, M) (section 8.1.1) with the given salt: EM encoded to
# modBits - 1 bits, RSASP1, the k-byte signature
def RsaPss.sign(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, +sk: R.RsaPrivate, m: B.Octets, salt: B.Octets) -> Result<&2, &2, R.RsaError, B.Octets>:
  +pk = R.Rsa.public(sk)
  Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, RsaPss.encode(~digest, ~mgf, m, salt, Nat.sub(R.Rsa.mod_bits(pk), 1n)), em => Result.bind(&2, &2, R.RsaError, N.BnNat, B.Octets, R.Rsa.sp1(sk, N.BnNat.of_octets(em)), s => R.Rsa.i2osp(s, R.Rsa.k(pk))))

def rsa.pss.em_of(r: Result<&2, &2, R.RsaError, N.BnNat>, +emlen: Nat) -> Maybe<&2, B.Octets>:
  match r:
    case Fail{e}:
      None{}
    case Done{x}:
      N.BnNat.to_octets(x, emlen)

def rsa.pss.verify.go(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, em: Maybe<&2, B.Octets>, m: B.Octets, +embits: Nat, +slen: Nat) -> Bool:
  match em:
    case None{}:
      False{}
    case Some{e}:
      RsaPss.check(~digest, ~mgf, m, e, embits, slen)

# RSASSA-PSS-VERIFY((n, e), M, S) (section 8.1.2) for a salt of slen bytes:
# whether S is a valid signature of M (S of k bytes; EM is RSAVP1's
# representative as emLen bytes)
def RsaPss.verify(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, +pk: R.RsaPublic, m: B.Octets, +s: B.Octets, +slen: Nat) -> Bool:
  +embits = Nat.sub(R.Rsa.mod_bits(pk), 1n)
  +ok = Nat.is_eq(B.Octets.len(s), R.Rsa.k(pk))
  Bool.and(ok, rsa.pss.verify.go(~digest, ~mgf, rsa.pss.em_of(R.Rsa.vp1(pk, N.BnNat.of_octets(s)), RsaPss.em_len(embits)), m, embits, slen))
