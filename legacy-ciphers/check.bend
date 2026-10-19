import Base
import ../bytes/bytes.bend as B
import ../cipher-modes/cipher-modes.bend as M
import ../cipher-modes/cbc.bend as CB
import ./legacy-ciphers.bend as L
import ./des.bend as D
import ./tdes.bend as T
import ./sm4.bend as S
import ./camellia.bend as C
import ./serpent.bend as P
import ./twofish.bend as F
import ./rc4.bend as R
import ./modes64.bend as X
import ./aria.bend as A
import ./cast6.bend as C6
import ./blowfish.bend as BF
import ./cast5.bend as C5
import ./tea.bend as TE
import ./xtea.bend as XT
import ./fcrypt.bend as FC

# The specifications' vectors, both ways (each line: the ciphertext, then the
# plaintext decrypted back), the 64-bit modes, every 128-bit cipher through
# cipher-modes' CBC over 32 KB (Serpent over 4 KB) both ways, every newer
# 64-bit cipher through modes64.bend's CBC over 16 KB both ways, RC4's
# vectors from RFC 6229 at every offset it lists, and the refusals. TEA and
# XTEA have no published vectors: their lines are ref/model.py's values.

def err(e: L.LcError) -> String:
  match e:
    case L.LcBadKeyLength{n}:
      "bad key " ++ Nat.show(n)
    case L.LcBadIvLength{n}:
      "bad iv " ++ Nat.show(n)
    case L.LcNotBlockMultiple{n}:
      "not whole blocks " ++ Nat.show(n)

def show(r: Result<&2, &2, L.LcError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{o}:
      B.Octets.hex(o)

def b128.of(m: Maybe<&2, M.CmBlock>) -> M.CmBlock:
  match m:
    case None{}:
      M.CmBlock.zero()
    case Some{b}:
      b

def b128(o: B.Octets) -> M.CmBlock:
  b128.of(M.CmBlock.of_octets(o))

def b64.of(m: Maybe<&2, L.LcBlock64>) -> L.LcBlock64:
  match m:
    case None{}:
      L.LcBlock64.zero()
    case Some{b}:
      b

def b64(o: B.Octets) -> L.LcBlock64:
  b64.of(L.LcBlock64.of_octets(o))

def key(~K: Data, r: Result<&2, &2, L.LcError, K>, d: K) -> K:
  match r:
    case Fail{e}:
      d
    case Done{k}:
      k

def des_key(o: B.Octets) -> D.LcDesKey:
  key(~D.LcDesKey, D.LcDes.key(o), D.LcDesKey{Nil{}})

def des(k: B.Octets, +b: B.Octets) -> String:
  +dk = des_key(k)
  +c = D.LcDes.encrypt(dk, b64(b))
  L.LcBlock64.hex(c) ++ " " ++ L.LcBlock64.hex(D.LcDes.decrypt(dk, c))

def tdes_key(o: B.Octets) -> T.LcTdesKey:
  +z = {D.LcDesKey{Nil{}} : D.LcDesKey}
  key(~T.LcTdesKey, T.LcTdes.key(o), T.LcTdes.of_des(z, z, z))

def tdes_ecb(k: B.Octets, m: B.Octets) -> String:
  +tk = tdes_key(k)
  +c = X.Lc64.ecb_encrypt(~T.LcTdesKey, ~T.LcTdes.encrypt, tk, m)
  show(c) ++ " " ++ show(Result.bind(&2, &2, L.LcError, B.Octets, B.Octets, c, x => X.Lc64.ecb_decrypt(~T.LcTdesKey, ~T.LcTdes.decrypt, tk, x)))

def tdes_cbc(k: B.Octets, +iv: B.Octets, m: B.Octets) -> String:
  +tk = tdes_key(k)
  +c = X.Lc64.cbc_encrypt(~T.LcTdesKey, ~T.LcTdes.encrypt, tk, iv, m)
  show(c) ++ " " ++ show(Result.bind(&2, &2, L.LcError, B.Octets, B.Octets, c, x => X.Lc64.cbc_decrypt(~T.LcTdesKey, ~T.LcTdes.decrypt, tk, iv, x)))

def both(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, b: M.CmBlock) -> String:
  +c = enc(k, b)
  M.CmBlock.hex(c) ++ " " ++ M.CmBlock.hex(dec(k, c))

def sm4(k: B.Octets, b: B.Octets) -> String:
  both(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, key(~S.LcSm4Key, S.LcSm4.key(k), S.LcSm4Key{L.LcLeaf{0}, Nil{}}), b128(b))

def camellia(k: B.Octets, b: B.Octets) -> String:
  both(~C.LcCamelliaKey, ~C.LcCamellia.encrypt, ~C.LcCamellia.decrypt, key(~C.LcCamelliaKey, C.LcCamellia.key(k), C.LcCamelliaKey{Nil{}}), b128(b))

def serpent(k: B.Octets, b: B.Octets) -> String:
  both(~P.LcSerpentKey, ~P.LcSerpent.encrypt, ~P.LcSerpent.decrypt, key(~P.LcSerpentKey, P.LcSerpent.key(k), P.LcSerpentKey{Nil{}}), b128(b))

def twofish(k: B.Octets, b: B.Octets) -> String:
  both(~F.LcTwofishKey, ~F.LcTwofish.encrypt, ~F.LcTwofish.decrypt, key(~F.LcTwofishKey, F.LcTwofish.key(k), F.LcTwofishKey{Nil{}}), b128(b))

def both64(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, ~dec: K -> L.LcBlock64 -> L.LcBlock64, +k: K, b: L.LcBlock64) -> String:
  +c = enc(k, b)
  L.LcBlock64.hex(c) ++ " " ++ L.LcBlock64.hex(dec(k, c))

def aria_key(k: B.Octets) -> A.LcAriaKey:
  key(~A.LcAriaKey, A.LcAria.key(k), A.LcAriaKey{Nil{}})

def cast6_key(k: B.Octets) -> C6.LcCast6Key:
  key(~C6.LcCast6Key, C6.LcCast6.key(k), C6.LcCast6Key{Nil{}})

def blowfish_key(k: B.Octets) -> BF.LcBlowfishKey:
  key(~BF.LcBlowfishKey, BF.LcBlowfish.key_any(k), BF.LcBlowfishKey{Nil{}})

def cast5_key(k: B.Octets) -> C5.LcCast5Key:
  key(~C5.LcCast5Key, C5.LcCast5.key(k), C5.LcCast5Key{Nil{}})

def tea_key(be: Bool, k: B.Octets) -> TE.LcTeaKey:
  key(~TE.LcTeaKey, TE.LcTea.key_with(Bool.not(be), 32n, k), TE.LcTeaKey{Nil{}})

def xtea_key(be: Bool, k: B.Octets) -> XT.LcXteaKey:
  key(~XT.LcXteaKey, XT.LcXtea.key_with(Bool.not(be), 32n, k), XT.LcXteaKey{Nil{}})

def fcrypt_key(k: B.Octets) -> FC.LcFcryptKey:
  key(~FC.LcFcryptKey, FC.LcFcrypt.key(k), FC.LcFcryptKey{Nil{}})

def aria(k: B.Octets, b: B.Octets) -> String:
  both(~A.LcAriaKey, ~A.LcAria.encrypt, ~A.LcAria.decrypt, aria_key(k), b128(b))

def cast6(k: B.Octets, b: B.Octets) -> String:
  both(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, cast6_key(k), b128(b))

def blowfish(k: B.Octets, b: B.Octets) -> String:
  both64(~BF.LcBlowfishKey, ~BF.LcBlowfish.encrypt, ~BF.LcBlowfish.decrypt, blowfish_key(k), b64(b))

def cast5(k: B.Octets, b: B.Octets) -> String:
  both64(~C5.LcCast5Key, ~C5.LcCast5.encrypt, ~C5.LcCast5.decrypt, cast5_key(k), b64(b))

def tea(be: Bool, k: B.Octets, b: B.Octets) -> String:
  both64(~TE.LcTeaKey, ~TE.LcTea.encrypt, ~TE.LcTea.decrypt, tea_key(be, k), b64(b))

def xtea(be: Bool, k: B.Octets, b: B.Octets) -> String:
  both64(~XT.LcXteaKey, ~XT.LcXtea.encrypt, ~XT.LcXtea.decrypt, xtea_key(be, k), b64(b))

def fcrypt(k: B.Octets, b: B.Octets) -> String:
  both64(~FC.LcFcryptKey, ~FC.LcFcrypt.encrypt, ~FC.LcFcrypt.decrypt, fcrypt_key(k), b64(b))

def rc4_state(k: B.Octets) -> R.LcRc4State:
  key(~R.LcRc4State, R.LcRc4.start(k), R.LcRc4State{L.LcLeaf{0}, 0, 0})

def rc4_ks(k: B.Octets, n: Nat) -> B.Octets:
  R.LcRc4.out_data(R.LcRc4.keystream(rc4_state(k), n))

# 48 keystream bytes in pieces of 5, 30 and 13
def rc4_pieces(k: B.Octets) -> String:
  +o1 = R.LcRc4.keystream(rc4_state(k), 5n)
  +o2 = R.LcRc4.keystream(R.LcRc4.out_state(o1), 30n)
  +o3 = R.LcRc4.keystream(R.LcRc4.out_state(o2), 13n)
  B.Octets.hex(B.Octets.append(R.LcRc4.out_data(o1), B.Octets.append(R.LcRc4.out_data(o2), R.LcRc4.out_data(o3))))

def rc4_drop(k: B.Octets) -> String:
  B.Octets.hex(R.LcRc4.out_data(R.LcRc4.keystream(key(~R.LcRc4State, R.LcRc4.start_drop(k, 1536n), R.LcRc4State{L.LcLeaf{0}, 0, 0}), 16n)))

# n bytes, byte i = 7i + 3 (mod 256)
def big.go(n: Nat, +i: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      B.rev(acc)
    case 1n+p:
      big.go(p, U32.add(i, 1), Con{U32.and(255, U32.add(U32.mul(i, 7), 3)), acc})

def big(n: Nat) -> B.Octets:
  B.Octets.of_list(big.go(n, 0, Nil{}))

def iv16() -> B.Octets:
  B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])

def last16(r: Result<&2, &2, M.CmError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{+o}:
      B.Octets.hex(B.Octets.drop(Nat.sub(B.Octets.len(o), 16n), o))

def verdict(b: Bool) -> String:
  match b:
    case True{}:
      "ok"
    case False{}:
      "differs"

def same(r: Result<&2, &2, M.CmError, B.Octets>, +m: B.Octets) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{o}:
      verdict(B.Octets.is_eq(o, m))

def cbc128(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, n: Nat) -> String:
  +m = big(n)
  +c = CB.Cbc.encrypt(~K, ~enc, k, iv16(), m)
  last16(c) ++ " " ++ same(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, c, x => CB.Cbc.decrypt(~K, ~dec, k, iv16(), x)), m)

def sm4_cbc(k: B.Octets, n: Nat) -> String:
  cbc128(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, key(~S.LcSm4Key, S.LcSm4.key(k), S.LcSm4Key{L.LcLeaf{0}, Nil{}}), n)

def camellia_cbc(k: B.Octets, n: Nat) -> String:
  cbc128(~C.LcCamelliaKey, ~C.LcCamellia.encrypt, ~C.LcCamellia.decrypt, key(~C.LcCamelliaKey, C.LcCamellia.key(k), C.LcCamelliaKey{Nil{}}), n)

def twofish_cbc(k: B.Octets, n: Nat) -> String:
  cbc128(~F.LcTwofishKey, ~F.LcTwofish.encrypt, ~F.LcTwofish.decrypt, key(~F.LcTwofishKey, F.LcTwofish.key(k), F.LcTwofishKey{Nil{}}), n)

def serpent_cbc(k: B.Octets, n: Nat) -> String:
  cbc128(~P.LcSerpentKey, ~P.LcSerpent.encrypt, ~P.LcSerpent.decrypt, key(~P.LcSerpentKey, P.LcSerpent.key(k), P.LcSerpentKey{Nil{}}), n)

def aria_cbc(k: B.Octets, n: Nat) -> String:
  cbc128(~A.LcAriaKey, ~A.LcAria.encrypt, ~A.LcAria.decrypt, aria_key(k), n)

def cast6_cbc(k: B.Octets, n: Nat) -> String:
  cbc128(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, cast6_key(k), n)

def last8(r: Result<&2, &2, L.LcError, B.Octets>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{+o}:
      B.Octets.hex(B.Octets.drop(Nat.sub(B.Octets.len(o), 8n), o))

def same64(r: Result<&2, &2, L.LcError, B.Octets>, +m: B.Octets) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{o}:
      verdict(B.Octets.is_eq(o, m))

def tdes_cbc_big(k: B.Octets) -> String:
  +tk = tdes_key(k)
  +m = big(16384n)
  +c = X.Lc64.cbc_encrypt(~T.LcTdesKey, ~T.LcTdes.encrypt, tk, B.Octets.zeros(8n), m)
  last8(c) ++ " " ++ same64(Result.bind(&2, &2, L.LcError, B.Octets, B.Octets, c, x => X.Lc64.cbc_decrypt(~T.LcTdesKey, ~T.LcTdes.decrypt, tk, B.Octets.zeros(8n), x)), m)

def cbc64(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, ~dec: K -> L.LcBlock64 -> L.LcBlock64, +k: K, n: Nat) -> String:
  +m = big(n)
  +c = X.Lc64.cbc_encrypt(~K, ~enc, k, B.Octets.zeros(8n), m)
  last8(c) ++ " " ++ same64(Result.bind(&2, &2, L.LcError, B.Octets, B.Octets, c, x => X.Lc64.cbc_decrypt(~K, ~dec, k, B.Octets.zeros(8n), x)), m)

def blowfish_cbc(k: B.Octets, n: Nat) -> String:
  cbc64(~BF.LcBlowfishKey, ~BF.LcBlowfish.encrypt, ~BF.LcBlowfish.decrypt, blowfish_key(k), n)

def cast5_cbc(k: B.Octets, n: Nat) -> String:
  cbc64(~C5.LcCast5Key, ~C5.LcCast5.encrypt, ~C5.LcCast5.decrypt, cast5_key(k), n)

def tea_cbc(k: B.Octets, n: Nat) -> String:
  cbc64(~TE.LcTeaKey, ~TE.LcTea.encrypt, ~TE.LcTea.decrypt, tea_key(False{}, k), n)

def xtea_cbc(k: B.Octets, n: Nat) -> String:
  cbc64(~XT.LcXteaKey, ~XT.LcXtea.encrypt, ~XT.LcXtea.decrypt, xtea_key(False{}, k), n)

def fcrypt_cbc(k: B.Octets, n: Nat) -> String:
  cbc64(~FC.LcFcryptKey, ~FC.LcFcrypt.encrypt, ~FC.LcFcrypt.decrypt, fcrypt_key(k), n)

# BEGIN GENERATED by gen/vectors.py: check
def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(des(B.Octets.of_list([1, 1, 1, 1, 1, 1, 1, 1]), B.Octets.of_list([128, 0, 0, 0, 0, 0, 0, 0])))
    IO.print(des(B.Octets.of_list([1, 1, 1, 1, 1, 1, 1, 1]), B.Octets.of_list([64, 0, 0, 0, 0, 0, 0, 0])))
    IO.print(des(B.Octets.of_list([1, 1, 1, 1, 1, 1, 1, 1]), B.Octets.of_list([32, 0, 0, 0, 0, 0, 0, 0])))
    IO.print(des(B.Octets.of_list([128, 1, 1, 1, 1, 1, 1, 1]), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0])))
    IO.print(des(B.Octets.of_list([64, 1, 1, 1, 1, 1, 1, 1]), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0])))
    IO.print(tdes_ecb(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 35, 69, 103, 137, 171, 205, 239, 1, 69, 103, 137, 171, 205, 239, 1, 35]), B.Octets.of_list([84, 104, 101, 32, 113, 117, 102, 99, 107, 32, 98, 114, 111, 119, 110, 32, 102, 111, 120, 32, 106, 117, 109, 112])))
    IO.print(tdes_cbc(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 35, 69, 103, 137, 171, 205, 239, 1, 69, 103, 137, 171, 205, 239, 1, 35]), B.Octets.of_list([246, 159, 36, 69, 223, 79, 155, 23]), B.Octets.of_list([84, 104, 101, 32, 113, 117, 102, 99, 107, 32, 98, 114, 111, 119, 110, 32, 102, 111, 120, 32, 106, 117, 109, 112])))
    IO.print(tdes_ecb(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 35, 69, 103, 137, 171, 205, 239, 1]), B.Octets.of_list([84, 104, 101, 32, 113, 117, 102, 99, 107, 32, 98, 114, 111, 119, 110, 32, 102, 111, 120, 32, 106, 117, 109, 112])))
    IO.print(sm4(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16]), B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16])))
    IO.print(camellia(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16]), B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16])))
    IO.print(camellia(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16, 0, 17, 34, 51, 68, 85, 102, 119]), B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16])))
    IO.print(camellia(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16, 0, 17, 34, 51, 68, 85, 102, 119, 136, 153, 170, 187, 204, 221, 238, 255]), B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16])))
    IO.print(serpent(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))
    IO.print(serpent(B.Octets.of_list([128, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))
    IO.print(twofish(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))
    IO.print(twofish(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16, 0, 17, 34, 51, 68, 85, 102, 119]), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))
    IO.print(twofish(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16, 0, 17, 34, 51, 68, 85, 102, 119, 136, 153, 170, 187, 204, 221, 238, 255]), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))
    IO.print(B.Octets.hex(B.Octets.slice(0n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(16n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(240n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(256n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(496n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(512n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(752n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(768n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(1008n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(1024n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(1520n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(1536n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(2032n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(2048n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(3056n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(3072n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(4080n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(B.Octets.hex(B.Octets.slice(4096n, 16n, rc4_ks(B.Octets.of_list([1, 2, 3, 4, 5]), 4112n))))
    IO.print(rc4_pieces(B.Octets.of_list([1, 2, 3, 4, 5])))
    IO.print(rc4_drop(B.Octets.of_list([1, 2, 3, 4, 5])))
    IO.print(sm4_cbc(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16]), 32768n))
    IO.print(camellia_cbc(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16]), 32768n))
    IO.print(twofish_cbc(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16]), 32768n))
    IO.print(serpent_cbc(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16]), 4096n))
    IO.print(tdes_cbc_big(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 35, 69, 103, 137, 171, 205, 239, 1, 69, 103, 137, 171, 205, 239, 1, 35])))
    IO.print(aria(B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([0, 17, 34, 51, 68, 85, 102, 119, 136, 153, 170, 187, 204, 221, 238, 255])))
    IO.print(aria(B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]), B.Octets.of_list([0, 17, 34, 51, 68, 85, 102, 119, 136, 153, 170, 187, 204, 221, 238, 255])))
    IO.print(aria(B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]), B.Octets.of_list([0, 17, 34, 51, 68, 85, 102, 119, 136, 153, 170, 187, 204, 221, 238, 255])))
    IO.print(cast6(B.Octets.of_list([35, 66, 187, 158, 250, 56, 84, 44, 10, 247, 86, 71, 242, 159, 97, 93]), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))
    IO.print(cast6(B.Octets.of_list([35, 66, 187, 158, 250, 56, 84, 44, 190, 208, 172, 131, 148, 10, 194, 152, 186, 199, 122, 119, 23, 148, 40, 99]), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))
    IO.print(cast6(B.Octets.of_list([35, 66, 187, 158, 250, 56, 84, 44, 190, 208, 172, 131, 148, 10, 194, 152, 141, 124, 71, 206, 38, 73, 8, 70, 28, 193, 181, 19, 122, 230, 182, 4]), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))
    IO.print(blowfish(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0])))
    IO.print(blowfish(B.Octets.of_list([255, 255, 255, 255, 255, 255, 255, 255]), B.Octets.of_list([255, 255, 255, 255, 255, 255, 255, 255])))
    IO.print(blowfish(B.Octets.of_list([254, 220, 186, 152, 118, 84, 50, 16]), B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239])))
    IO.print(blowfish(B.Octets.of_list([240]), B.Octets.of_list([254, 220, 186, 152, 118, 84, 50, 16])))
    IO.print(blowfish(B.Octets.of_list([240, 225, 210]), B.Octets.of_list([254, 220, 186, 152, 118, 84, 50, 16])))
    IO.print(blowfish(B.Octets.of_list([240, 225, 210, 195, 180, 165, 150, 135, 120, 105, 90, 75, 60, 45, 30, 15, 0, 17, 34, 51, 68, 85, 102, 119]), B.Octets.of_list([254, 220, 186, 152, 118, 84, 50, 16])))
    IO.print(cast5(B.Octets.of_list([1, 35, 69, 103, 18, 52, 86, 120, 35, 69, 103, 137, 52, 86, 120, 154]), B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239])))
    IO.print(cast5(B.Octets.of_list([1, 35, 69, 103, 18, 52, 86, 120, 35, 69]), B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239])))
    IO.print(cast5(B.Octets.of_list([1, 35, 69, 103, 18]), B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239])))
    IO.print(fcrypt(B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0]), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0])))
    IO.print(fcrypt(B.Octets.of_list([17, 68, 119, 170, 221, 0, 51, 102]), B.Octets.of_list([18, 52, 86, 120, 154, 188, 222, 240])))
    IO.print(tea(False{}, B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7])))
    IO.print(xtea(False{}, B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7])))
    IO.print(tea(True{}, B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7])))
    IO.print(xtea(True{}, B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]), B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7])))
    IO.print(aria_cbc(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16]), 32768n))
    IO.print(cast6_cbc(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16]), 32768n))
    IO.print(blowfish_cbc(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239]), 16384n))
    IO.print(cast5_cbc(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16]), 16384n))
    IO.print(tea_cbc(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16]), 16384n))
    IO.print(xtea_cbc(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239, 254, 220, 186, 152, 118, 84, 50, 16]), 16384n))
    IO.print(fcrypt_cbc(B.Octets.of_list([1, 35, 69, 103, 137, 171, 205, 239]), 16384n))
    IO.print(show(X.Lc64.cbc_encrypt(~D.LcDesKey, ~D.LcDes.encrypt, des_key(B.Octets.of_list([1, 1, 1, 1, 1, 1, 1, 1])), B.Octets.zeros(7n), B.Octets.zeros(8n))))
    IO.print(show(X.Lc64.ecb_encrypt(~D.LcDesKey, ~D.LcDes.encrypt, des_key(B.Octets.of_list([1, 1, 1, 1, 1, 1, 1, 1])), B.Octets.zeros(9n))))

#|95f8a5e5dd31d900 8000000000000000
#|dd7f121ca5015619 4000000000000000
#|2e8653104f3834ea 2000000000000000
#|95a8d72813daa94d 0000000000000000
#|0eec1487dd8c26d5 0000000000000000
#|a826fd8ce53b855fcce21c8112256fe668d5c05dd9b6b900 54686520717566636b2062726f776e20666f78206a756d70
#|a5c282bad0de3774becd2e04386b589fb5057d8552fc4336 54686520717566636b2062726f776e20666f78206a756d70
#|c44862f70cf2fbdc9077d0909fa91b884cabd61fc58e0cbb 54686520717566636b2062726f776e20666f78206a756d70
#|681edf34d206965e86b3e94f536e4246 0123456789abcdeffedcba9876543210
#|67673138549669730857065648eabe43 0123456789abcdeffedcba9876543210
#|b4993401b3e996f84ee5cee7d79b09b9 0123456789abcdeffedcba9876543210
#|9acc237dff16d76c20ef7c919e3a7509 0123456789abcdeffedcba9876543210
#|3620b17ae6a993d09618b8768266bae9 00000000000000000000000000000000
#|264e5481eff42a4606abda06c0bfda3d 00000000000000000000000000000000
#|9f589f5cf6122c32b6bfec2f2ae8c35a 00000000000000000000000000000000
#|cfd1d2e5a9be9cdf501f13b892bd2248 00000000000000000000000000000000
#|37527be0052334b89f0cfccae87cfa20 00000000000000000000000000000000
#|b2396305f03dc027ccc3524a0a1118a8
#|6982944f18fc82d589c403a47a0d0919
#|28cb1132c96ce286421dcaadb8b69eae
#|1cfcf62b03eddb641d77dfcf7f8d8c93
#|42b7d0cdd918a8a33dd51781c81f4041
#|6459844432a7da923cfb3eb4980661f6
#|ec10327bde2beefd18f9277680457e22
#|eb62638d4f0ba1fe9fca20e05bf8ff2b
#|45129048e6a0ed0b56b490338f078da5
#|30abbcc7c20b01609f23ee2d5f6bb7df
#|3294f744d8f9790507e70f62e5bbceea
#|d8729db41882259bee4f825325f5a130
#|1eb14a0c13b3bf47fa2a0ba93ad45b8b
#|cc582f8ba9f265e2b1be9112e975d2d7
#|f2e30f9bd102ecbf75aaade9bc35c43c
#|ec0e11c479dc329dc8da7968fe965681
#|068326a2118416d21f9d04b2cd1ca050
#|ff25b58995996707e51fbdf08b34d875
#|b2396305f03dc027ccc3524a0a1118a86982944f18fc82d589c403a47a0d0919b68f78c28d15d822234c6cb8c5f6c4ac
#|d8729db41882259bee4f825325f5a130
#|c7b0c049ff58ac26268bf935616df708 ok
#|01fbbba61e8bb08562d59ae3b7e70881 ok
#|4e94b3aaf79619126bdd205de807393f ok
#|e0796b397d2533fc445f5c7ede7475fc ok
#|546259b8de55036c ok
#|d718fbd6ab644c739da95f3be6451778 00112233445566778899aabbccddeeff
#|26449c1805dbe7aa25a468ce263a9e79 00112233445566778899aabbccddeeff
#|f92bd7c79fb72e2f2b8f80c1972d24fc 00112233445566778899aabbccddeeff
#|c842a08972b43d20836c91d1b7530f6b 00000000000000000000000000000000
#|1b386c0210dcadcbdd0e41aa08a7a7e8 00000000000000000000000000000000
#|4f6a2038286897b9c9870136553317fa 00000000000000000000000000000000
#|4ef997456198dd78 0000000000000000
#|51866fd5b85ecb8a ffffffffffffffff
#|0aceab0fc6a0a28d 0123456789abcdef
#|f9ad597c49db005e fedcba9876543210
#|e9c2b70a1bc65cf3 fedcba9876543210
#|05044b62fa52d080 fedcba9876543210
#|238b4fe5847e44b2 0123456789abcdef
#|eb6a711a2c02271b 0123456789abcdef
#|7ac816d16e9b302e 0123456789abcdef
#|0e0900c73ef7ed41 0000000000000000
#|d8ed787477ec0680 123456789abcdef0
#|6da901760c539dce 0001020304050607
#|256004e1f55bc0c7 0001020304050607
#|54d51b2bf3e47e12 0001020304050607
#|ffc52d10a010010b 0001020304050607
#|78d7ea7c6c947995b6180eeac7c72206 ok
#|9d178a01c3e61f0a53d8f7cc64e542c6 ok
#|d9e0b4045974d5f0 ok
#|1701cdf260449014 ok
#|772d6e49fc2ee76e ok
#|246f9fb82837f395 ok
#|9469aaeb22e401db ok
#|bad iv 7
#|not whole blocks 9
# END GENERATED: check
