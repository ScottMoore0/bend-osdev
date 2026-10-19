# EME-OAEP and RSAES-OAEP (RFC 8017, section 7.1), over any hash
# (~digest, one-shot; hLen is the length of its output) and any mask
# generation function (~mgf, MGF1 over a hash the usual one):
#   DB = lHash || PS || 0x01 || M,  lHash = Hash(L),
#   maskedDB = DB xor MGF(seed, k - hLen - 1),
#   maskedSeed = seed xor MGF(maskedDB, hLen),
#   EM = 0x00 || maskedSeed || maskedDB.
# The seed (hLen random bytes) is a parameter, from the caller. Decryption
# answers RsaDecryptionError for every failure, without saying which check
# failed (section 7.1.2, Note).
#
# The decoding takes EM apart by its pieces' lengths (one byte, hLen bytes,
# the rest) and masks DB with as many bytes as maskedDB has, which is
# k - hLen - 1 for a k-byte EM; the encoding masks DB with its own length,
# which is the same. LAWS.bend's oaep_round_trip proves that decoding undoes
# encoding, for every hash and mask generation function.
import Base
import ../bytes/bytes.bend as B
import ./rsa.bend as R
import ./octets.bend as O

# DB = lHash || PS || 0x01 || M, PS ps zero bytes
def rsa.oaep.db(+lhash: B.Octets, +m: B.Octets, +ps: Nat) -> B.Octets:
  B.Octets.append(lhash, B.Octets.append(B.Octets.zeros(ps), B.Octets.append(B.Octets.of_list([1]), m)))

# EM = 0x00 || maskedSeed || maskedDB
def rsa.oaep.em(~mgf: B.Octets -> Nat -> B.Octets, +db: B.Octets, +seed: B.Octets, +hlen: Nat) -> B.Octets:
  +masked = O.RsaOct.xor(db, mgf(seed, B.Octets.len(db)))
  B.Octets.append(B.Octets.of_list([0]), B.Octets.append(O.RsaOct.xor(seed, mgf(masked, hlen)), masked))

def rsa.oaep.enc(~mgf: B.Octets -> Nat -> B.Octets, fits: Bool, good: Bool, +lhash: B.Octets, +m: B.Octets, +seed: B.Octets, +k: Nat) -> Result<&2, &2, R.RsaError, B.Octets>:
  match fits good:
    case False{} _:
      Fail{R.RsaMessageTooLong{}}
    case True{} False{}:
      Fail{R.RsaEncodingError{}}
    case True{} True{}:
      +hlen = B.Octets.len(lhash)
      Done{rsa.oaep.em(~mgf, rsa.oaep.db(lhash, m, Nat.sub(k, Nat.add(B.Octets.len(m), Nat.add(Nat.mul(2n, hlen), 2n)))), seed, hlen)}

def rsa.oaep.enc0(~mgf: B.Octets -> Nat -> B.Octets, +lhash: B.Octets, +m: B.Octets, +seed: B.Octets, +k: Nat) -> Result<&2, &2, R.RsaError, B.Octets>:
  +hlen = B.Octets.len(lhash)
  rsa.oaep.enc(~mgf, Nat.is_le(Nat.add(B.Octets.len(m), Nat.add(Nat.mul(2n, hlen), 2n)), k), Nat.is_eq(B.Octets.len(seed), hlen), lhash, m, seed, k)

# EME-OAEP encoding (section 7.1.1, step 2) of M under label L to k bytes:
# RsaMessageTooLong when mLen > k - 2 hLen - 2, RsaEncodingError for a
# seed that is not hLen bytes
def RsaOaep.encode(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, label: B.Octets, m: B.Octets, seed: B.Octets, k: Nat) -> Result<&2, &2, R.RsaError, B.Octets>:
  rsa.oaep.enc0(~mgf, digest(label), m, seed, k)

def rsa.oaep.msg(ok: Bool, z: Maybe<&2, Nat>, t: List<&2, U32>) -> Result<&2, &2, R.RsaError, B.Octets>:
  match ok z:
    case True{} Some{i}:
      Done{B.Octets.of_list(B.drop(Nat.add(i, 1n), t))}
    case _ _:
      Fail{R.RsaDecryptionError{}}

# DB: lHash' checked, then PS || 0x01 || M
def rsa.oaep.dec5(+lhash: B.Octets, +y: B.Octets, +db: B.Octets) -> Result<&2, &2, R.RsaError, B.Octets>:
  +t = B.Octets.to_list(B.Octets.drop(B.Octets.len(lhash), db))
  rsa.oaep.msg(Bool.and(B.Octets.is_eq(y, B.Octets.of_list([0])), B.Octets.is_eq(B.Octets.take(B.Octets.len(lhash), db), lhash)), O.rsa.sep(t), t)

# DB = maskedDB xor MGF(seed, its length)
def rsa.oaep.dec4(~mgf: B.Octets -> Nat -> B.Octets, +lhash: B.Octets, +y: B.Octets, +seed: B.Octets, +mdb: B.Octets) -> Result<&2, &2, R.RsaError, B.Octets>:
  rsa.oaep.dec5(lhash, y, O.RsaOct.xor(mdb, mgf(seed, B.Octets.len(mdb))))

# seed = maskedSeed xor MGF(maskedDB, hLen)
def rsa.oaep.dec3(~mgf: B.Octets -> Nat -> B.Octets, +lhash: B.Octets, +y: B.Octets, +ms: B.Octets, +mdb: B.Octets) -> Result<&2, &2, R.RsaError, B.Octets>:
  rsa.oaep.dec4(~mgf, lhash, y, O.RsaOct.xor(ms, mgf(mdb, B.Octets.len(lhash))), mdb)

# maskedSeed and maskedDB from what follows Y
def rsa.oaep.dec2(~mgf: B.Octets -> Nat -> B.Octets, +lhash: B.Octets, +y: B.Octets, +rest: B.Octets) -> Result<&2, &2, R.RsaError, B.Octets>:
  rsa.oaep.dec3(~mgf, lhash, y, B.Octets.take(B.Octets.len(lhash), rest), B.Octets.drop(B.Octets.len(lhash), rest))

def rsa.oaep.dec(~mgf: B.Octets -> Nat -> B.Octets, +lhash: B.Octets, +em: B.Octets) -> Result<&2, &2, R.RsaError, B.Octets>:
  rsa.oaep.dec2(~mgf, lhash, B.Octets.take(1n, em), B.Octets.drop(1n, em))

# EME-OAEP decoding (section 7.1.2, step 3) of EM under label L
def RsaOaep.decode(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, label: B.Octets, em: B.Octets) -> Result<&2, &2, R.RsaError, B.Octets>:
  rsa.oaep.dec(~mgf, digest(label), em)

# RSAES-OAEP-ENCRYPT((n, e), M, L) (section 7.1.1) with the given seed
def RsaOaep.encrypt(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, +pk: R.RsaPublic, label: B.Octets, m: B.Octets, seed: B.Octets) -> Result<&2, &2, R.RsaError, B.Octets>:
  Result.bind(&2, &2, R.RsaError, B.Octets, B.Octets, RsaOaep.encode(~digest, ~mgf, label, m, seed, R.Rsa.k(pk)), em => R.Rsa.ep_octets(pk, em))

def rsa.oaep.dec.r(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, r: Result<&2, &2, R.RsaError, B.Octets>, label: B.Octets) -> Result<&2, &2, R.RsaError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{R.RsaDecryptionError{}}
    case Done{em}:
      RsaOaep.decode(~digest, ~mgf, label, em)

# RSAES-OAEP-DECRYPT(K, C, L) (section 7.1.2): RsaDecryptionError for a
# modulus shorter than 2 hLen + 2 bytes, a ciphertext of the wrong length
# or out of range, and for a bad encoding
def RsaOaep.decrypt(~digest: B.Octets -> B.Octets, ~mgf: B.Octets -> Nat -> B.Octets, +sk: R.RsaPrivate, +label: B.Octets, c: B.Octets) -> Result<&2, &2, R.RsaError, B.Octets>:
  +hlen = B.Octets.len(digest(label))
  Result.bind(&2, &2, R.RsaError, Unit, B.Octets, R.RsaError.check(Nat.is_le(Nat.add(Nat.mul(2n, hlen), 2n), R.Rsa.k_of(sk)), R.RsaDecryptionError{}), u => rsa.oaep.dec.r(~digest, ~mgf, R.Rsa.dp_octets(sk, c), label))
