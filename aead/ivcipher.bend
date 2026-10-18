# Ciphers with an IV, of the shape authenc.bend and essiv.bend take (a key
# schedule, an IV and bytes): any block cipher of the crypto package's
# block-cipher interface in CBC (crypto's modes.bend, NIST SP 800-38A),
# whole blocks only (the kernel's cbc) or PKCS #7 padded (RFC 5652, section
# 6.3; cipher-modes' pkcs7.bend), as draft-mcgrew-aead-aes-cbc-hmac-sha2
# uses it.
#
# Each is ~enc and ~dec for those files, for example AES-CBC:
#   ~AdCbc.encrypt(~X.CmAesKey, ~M.CmBlock, ~16n, ~X.CmAes.encrypt,
#     ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets)
import Base
import ../bytes/bytes.bend as B
import ../cipher-modes/pkcs7.bend as P7
import ../crypto/crypto.bend as Cr
import ../crypto/modes.bend as Md
import ../crypto/inst_cm.bend as CM

# CBC, whole blocks (CrNotBlockMultiple otherwise), a one-block IV
def AdCbc.encrypt(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, k: K, iv: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Md.CrCbc.encrypt(~K, ~Blk, ~bsize, ~enc, ~bxor, ~blk_of, ~blk_to, k, iv, m)

def AdCbc.decrypt(~K: Data, ~Blk: Data, ~bsize: Nat, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, k: K, iv: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Md.CrCbc.decrypt(~K, ~Blk, ~bsize, ~dec, ~bxor, ~blk_of, ~blk_to, k, iv, c)

def ad.cbc.encrypt_padded(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +iv: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, CM.CrCm.lift(~B.Octets, P7.Pkcs7.pad(bsize, m)), x => Md.CrCbc.encrypt(~K, ~Blk, ~bsize, ~enc, ~bxor, ~blk_of, ~blk_to, k, iv, x))

def ad.cbc.decrypt_padded(~K: Data, ~Blk: Data, ~bsize: Nat, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +iv: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Md.CrCbc.decrypt(~K, ~Blk, ~bsize, ~dec, ~bxor, ~blk_of, ~blk_to, k, iv, c), x => CM.CrCm.lift(~B.Octets, P7.Pkcs7.unpad(bsize, x)))

# CBC of the PKCS #7 padding of m, any length
def AdCbc.encrypt_padded(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, k: K, iv: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  ad.cbc.encrypt_padded(~K, ~Blk, ~bsize, ~enc, ~bxor, ~blk_of, ~blk_to, k, iv, m)

# the padding removed after CBC decryption (CrBadPadding)
def AdCbc.decrypt_padded(~K: Data, ~Blk: Data, ~bsize: Nat, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, k: K, iv: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  ad.cbc.decrypt_padded(~K, ~Blk, ~bsize, ~dec, ~bxor, ~blk_of, ~blk_to, k, iv, c)
