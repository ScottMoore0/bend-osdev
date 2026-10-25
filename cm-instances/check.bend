# Every cipher through cipher-modes' four round trips, at run time: a key
# the cipher accepts, a 16-byte IV or sequence number, and data of 64 bytes
# (CBC, and XTS on whole blocks) and 61 bytes (XTS with ciphertext
# stealing), encrypted and decrypted back. Written by gen/instances.py. The
# ciphers' own values are tested in their packages (sm4, camellia, serpent,
# twofish, aria, cast6: their vectors, and CBC against cryptography, the
# openssl command or their models) and in cipher-modes (AES: FIPS 197's
# vectors, and against cryptography), the modes' in cipher-modes.
import Base
import ../bytes/bytes.bend as B
import ../cipher-core/cipher-core.bend as LC
import ../cipher-modes/cipher-modes.bend as M
import ../cipher-modes/cbc.bend as CB
import ../cipher-modes/xts.bend as XT
import ../sm4/sm4.bend as S
import ../camellia/camellia.bend as Ca
import ../serpent/serpent.bend as Sp
import ../twofish/twofish.bend as Tf
import ../aria/aria.bend as Ar
import ../cast6/cast6.bend as C6
import ../cipher-modes/aes.bend as X

def hx.digit(+c: U32) -> U32:
  U32.sub(c, U32.add(48, U32.mul(39, U32.shrn(c, 6n))))

def hx.go(cs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Con{a, Con{b, t}}:
      hx.go(t, Con{U32.or(U32.shln(hx.digit(a), 4n), hx.digit(b)), acc})
    case _:
      List.reverse(&2, U32, acc)

def hx(s: String) -> B.Octets:
  B.Octets.of_list(hx.go(B.Octets.to_list(B.Octets.of_string(s)), Nil{}))

# n bytes 0, 1, 2, ...
def seq.go(n: Nat, +i: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      List.reverse(&2, U32, acc)
    case 1n+p:
      seq.go(p, U32.add(i, 1), Con{U32.and(255, i), acc})

def seq(n: Nat) -> B.Octets:
  B.Octets.of_list(seq.go(n, 0, Nil{}))

def ok(b: Bool) -> String:
  match b:
    case True{}:
      "ok"
    case False{}:
      "FAIL"

def same(r: Result<&2, &2, M.CmError, B.Octets>, +m: B.Octets) -> String:
  match r:
    case Done{x}:
      ok(B.Octets.is_eq(x, m))
    case Fail{e}:
      "FAIL"

def blocks() -> List<&2, M.CmBlock>:
  [M.CmBlock{1, 2, 3, 4}, M.CmBlock{5, 6, 7, 8}, M.CmBlock{9, 10, 11, 12}, M.CmBlock{13, 14, 15, 16}]

def tw() -> M.CmBlock:
  M.CmBlock{1, 2, 3, 4}

def same_blocks(xs: List<&2, M.CmBlock>, ys: List<&2, M.CmBlock>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(B.Octets.is_eq(M.CmBlock.to_octets(x), M.CmBlock.to_octets(y)), same_blocks(xt, yt))
    case _ _:
      False{}

# the four round trips under k (k2 the XTS tweak key)
def four(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +name: String, +k: K, +k2: K) -> String:
  +iv = seq(16n)
  +m = seq(64n)
  +p = seq(61n)
  +bs = blocks()
  +t = tw()
  name ++ " cbc_blocks " ++ ok(same_blocks(CB.Cbc.decrypt_blocks(~K, ~dec, k, t, CB.Cbc.encrypt_blocks(~K, ~enc, k, t, bs)), bs))
    ++ ", cbc " ++ same(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CB.Cbc.encrypt(~K, ~enc, k, iv, m), c => CB.Cbc.decrypt(~K, ~dec, k, iv, c)), m)
    ++ ", xts_blocks " ++ ok(same_blocks(XT.Xts.decrypt_blocks(~K, ~dec, k, t, XT.Xts.encrypt_blocks(~K, ~enc, k, t, bs)), bs))
    ++ ", xts " ++ same(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, XT.Xts.encrypt(~K, ~enc, k, k2, iv, m), c => XT.Xts.decrypt(~K, ~enc, ~dec, k, k2, iv, c)), m)
    ++ ", xts stealing " ++ same(Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, XT.Xts.encrypt(~K, ~enc, k, k2, iv, p), c => XT.Xts.decrypt(~K, ~enc, ~dec, k, k2, iv, c)), p)

def run.sm4(a: Result<&2, &2, LC.LcError, S.LcSm4Key>, b: Result<&2, &2, LC.LcError, S.LcSm4Key>) -> String:
  match a b:
    case Done{+k} Done{+k2}:
      four(~S.LcSm4Key, ~S.LcSm4.encrypt, ~S.LcSm4.decrypt, "sm4", k, k2)
    case _ _:
      "sm4: key refused"

def run.camellia(a: Result<&2, &2, LC.LcError, Ca.LcCamelliaKey>, b: Result<&2, &2, LC.LcError, Ca.LcCamelliaKey>) -> String:
  match a b:
    case Done{+k} Done{+k2}:
      four(~Ca.LcCamelliaKey, ~Ca.LcCamellia.encrypt, ~Ca.LcCamellia.decrypt, "camellia", k, k2)
    case _ _:
      "camellia: key refused"

def run.serpent(a: Result<&2, &2, LC.LcError, Sp.LcSerpentKey>, b: Result<&2, &2, LC.LcError, Sp.LcSerpentKey>) -> String:
  match a b:
    case Done{+k} Done{+k2}:
      four(~Sp.LcSerpentKey, ~Sp.LcSerpent.encrypt, ~Sp.LcSerpent.decrypt, "serpent", k, k2)
    case _ _:
      "serpent: key refused"

def run.twofish(a: Result<&2, &2, LC.LcError, Tf.LcTwofishKey>, b: Result<&2, &2, LC.LcError, Tf.LcTwofishKey>) -> String:
  match a b:
    case Done{+k} Done{+k2}:
      four(~Tf.LcTwofishKey, ~Tf.LcTwofish.encrypt, ~Tf.LcTwofish.decrypt, "twofish", k, k2)
    case _ _:
      "twofish: key refused"

def run.aria(a: Result<&2, &2, LC.LcError, Ar.LcAriaKey>, b: Result<&2, &2, LC.LcError, Ar.LcAriaKey>) -> String:
  match a b:
    case Done{+k} Done{+k2}:
      four(~Ar.LcAriaKey, ~Ar.LcAria.encrypt, ~Ar.LcAria.decrypt, "aria", k, k2)
    case _ _:
      "aria: key refused"

def run.cast6(a: Result<&2, &2, LC.LcError, C6.LcCast6Key>, b: Result<&2, &2, LC.LcError, C6.LcCast6Key>) -> String:
  match a b:
    case Done{+k} Done{+k2}:
      four(~C6.LcCast6Key, ~C6.LcCast6.encrypt, ~C6.LcCast6.decrypt, "cast6", k, k2)
    case _ _:
      "cast6: key refused"

def run.aes(a: Result<&2, &2, M.CmError, X.CmAesKey>, b: Result<&2, &2, M.CmError, X.CmAesKey>) -> String:
  match a b:
    case Done{+k} Done{+k2}:
      four(~X.CmAesKey, ~X.CmAes.encrypt, ~X.CmAes.decrypt, "aes", k, k2)
    case _ _:
      "aes: key refused"

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(run.sm4(S.LcSm4.key(hx("000102030405060708090a0b0c0d0e0f")), S.LcSm4.key(hx("f0e0d0c0b0a090807060504030201000"))))
    IO.print(run.camellia(Ca.LcCamellia.key(hx("000102030405060708090a0b0c0d0e0f")), Ca.LcCamellia.key(hx("f0e0d0c0b0a090807060504030201000"))))
    IO.print(run.serpent(Sp.LcSerpent.key(hx("000102030405060708090a0b0c0d0e0f")), Sp.LcSerpent.key(hx("f0e0d0c0b0a090807060504030201000"))))
    IO.print(run.twofish(Tf.LcTwofish.key(hx("000102030405060708090a0b0c0d0e0f")), Tf.LcTwofish.key(hx("f0e0d0c0b0a090807060504030201000"))))
    IO.print(run.aria(Ar.LcAria.key(hx("000102030405060708090a0b0c0d0e0f")), Ar.LcAria.key(hx("f0e0d0c0b0a090807060504030201000"))))
    IO.print(run.cast6(C6.LcCast6.key(hx("000102030405060708090a0b0c0d0e0f")), C6.LcCast6.key(hx("f0e0d0c0b0a090807060504030201000"))))
    IO.print(run.aes(X.CmAes.key(hx("000102030405060708090a0b0c0d0e0f")), X.CmAes.key(hx("f0e0d0c0b0a090807060504030201000"))))

#|sm4 cbc_blocks ok, cbc ok, xts_blocks ok, xts ok, xts stealing ok
#|camellia cbc_blocks ok, cbc ok, xts_blocks ok, xts ok, xts stealing ok
#|serpent cbc_blocks ok, cbc ok, xts_blocks ok, xts ok, xts stealing ok
#|twofish cbc_blocks ok, cbc ok, xts_blocks ok, xts ok, xts stealing ok
#|aria cbc_blocks ok, cbc ok, xts_blocks ok, xts ok, xts stealing ok
#|cast6 cbc_blocks ok, cbc ok, xts_blocks ok, xts ok, xts stealing ok
#|aes cbc_blocks ok, cbc ok, xts_blocks ok, xts ok, xts stealing ok
