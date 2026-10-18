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

# The specifications' vectors, both ways (each line: the ciphertext, then the
# plaintext decrypted back), the 64-bit modes, every 128-bit cipher through
# cipher-modes' CBC over 32 KB (Serpent over 4 KB) both ways, RC4's vectors
# from RFC 6229 at every offset it lists, and the refusals.

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
#|bad iv 7
#|not whole blocks 9
# END GENERATED: check
