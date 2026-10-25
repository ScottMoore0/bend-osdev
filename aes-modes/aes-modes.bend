# The modes with AES as the cipher: the named defaults. Each takes the raw key
# as Octets and picks AES-128 or AES-256 by its length (XTS: the two keys
# joined, 32 or 64 bytes), so a wrong length answers CmBadKeyLength. To
# expand a key once and use it many times, call CmAes.key (aes.bend) and the
# generic mode with ~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt.
# (CmAes.prepare, applied below before decrypting, is the identity now:
# decryption uses the encryption schedule.)
import Base
import ../bytes/bytes.bend as B
import ../mode-core/mode-core.bend as M
import ../aes/aes.bend as X
import ../cbc/cbc.bend as C
import ../xts/xts.bend as T
import ../ccm/ccm.bend as CC
import ../cmac/cmac.bend as CM

def CmAes.cbc_encrypt(key: B.Octets, iv: B.Octets, m: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  do Result<&2, &2, M.CmError, B.Octets>:
    k : X.CmAesKey <- X.CmAes.key(key)
    C.Cbc.encrypt(~X.CmAesKey, ~X.CmAes.encrypt, k, iv, m)

def CmAes.cbc_decrypt(key: B.Octets, iv: B.Octets, c: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  do Result<&2, &2, M.CmError, B.Octets>:
    k : X.CmAesKey <- X.CmAes.key(key)
    C.Cbc.decrypt(~X.CmAesKey, ~X.CmAes.decrypt, X.CmAes.prepare(k), iv, c)

def CmAes.cbc_encrypt_padded(key: B.Octets, iv: B.Octets, m: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  do Result<&2, &2, M.CmError, B.Octets>:
    k : X.CmAesKey <- X.CmAes.key(key)
    C.Cbc.encrypt_padded(~X.CmAesKey, ~X.CmAes.encrypt, k, iv, m)

def CmAes.cbc_decrypt_padded(key: B.Octets, iv: B.Octets, c: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  do Result<&2, &2, M.CmError, B.Octets>:
    k : X.CmAesKey <- X.CmAes.key(key)
    C.Cbc.decrypt_padded(~X.CmAesKey, ~X.CmAes.decrypt, X.CmAes.prepare(k), iv, c)

# XTS-AES-128 (a 32-byte key) or XTS-AES-256 (64 bytes): Key1 (data) then
# Key2 (tweak), as IEEE 1619 writes them

# the data unit p with 16-byte sequence number i (Xts.sector(n) for sector n)
def CmAes.xts_encrypt(+key: B.Octets, i: B.Octets, p: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  +n = B.Octets.len(key)
  +h = Nat.div(n, 2n)
  do Result<&2, &2, M.CmError, B.Octets>:
    M.cm.check(Bool.or(Nat.is_eq(n, 32n), Nat.is_eq(n, 64n)), M.CmBadKeyLength{n})
    k1 : X.CmAesKey <- X.CmAes.key(B.Octets.take(h, key))
    k2 : X.CmAesKey <- X.CmAes.key(B.Octets.drop(h, key))
    T.Xts.encrypt(~X.CmAesKey, ~X.CmAes.encrypt, k1, k2, i, p)

def CmAes.xts_decrypt(+key: B.Octets, i: B.Octets, c: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  +n = B.Octets.len(key)
  +h = Nat.div(n, 2n)
  do Result<&2, &2, M.CmError, B.Octets>:
    M.cm.check(Bool.or(Nat.is_eq(n, 32n), Nat.is_eq(n, 64n)), M.CmBadKeyLength{n})
    k1 : X.CmAesKey <- X.CmAes.key(B.Octets.take(h, key))
    k2 : X.CmAesKey <- X.CmAes.key(B.Octets.drop(h, key))
    T.Xts.decrypt(~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt, X.CmAes.prepare(k1), k2, i, c)

# CCM with an m-byte tag: the ciphertext, then the tag
def CmAes.ccm_encrypt(key: B.Octets, +m: Nat, nonce: B.Octets, aad: B.Octets, p: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  do Result<&2, &2, M.CmError, B.Octets>:
    k : X.CmAesKey <- X.CmAes.key(key)
    CC.Ccm.encrypt(~X.CmAesKey, ~X.CmAes.encrypt, k, m, nonce, aad, p)

def CmAes.ccm_decrypt(key: B.Octets, +m: Nat, nonce: B.Octets, aad: B.Octets, c: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  do Result<&2, &2, M.CmError, B.Octets>:
    k : X.CmAesKey <- X.CmAes.key(key)
    CC.Ccm.decrypt(~X.CmAesKey, ~X.CmAes.encrypt, k, m, nonce, aad, c)

# AES-CMAC (RFC 4493 with a 16-byte key): the 16-byte MAC
def CmAes.cmac(key: B.Octets, m: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  do Result<&2, &2, M.CmError, B.Octets>:
    k : X.CmAesKey <- X.CmAes.key(key)
    return CM.Cmac.mac(~X.CmAesKey, ~X.CmAes.encrypt, k, m)
