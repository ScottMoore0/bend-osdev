# cipher-core on its own: a block's hex and byte forms, XOR, tables, the
# word helpers on bits against their native forms, Feistel rounds over a toy
# round function, and the 64-bit modes over a toy cipher (XOR with the key
# block: not a cipher, but enough to show the modes chain and undo
# themselves), with their refusals. The ciphers' own packages test the
# modes over real ciphers (des: against Python's cryptography).
import Base
import ../bytes/bytes.bend as B
import ./cipher-core.bend as L
import ./modes64.bend as X

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

def show_blocks(r: Result<&2, &2, L.LcError, List<&2, L.LcBlock64>>) -> String:
  match r:
    case Fail{e}:
      err(e)
    case Done{bs}:
      B.Octets.hex(X.Lc64.octets_of(bs))

def show_some(m: Maybe<&2, L.LcBlock64>) -> String:
  match m:
    case None{}:
      "none"
    case Some{b}:
      L.LcBlock64.hex(b)

# a word as hex, through the block's hex form
def word(x: U32) -> String:
  L.LcBlock64.hex(L.LcBlock64{0, x})

# the toy cipher: XOR with the key block, its own inverse
def toy(k: L.LcBlock64, b: L.LcBlock64) -> L.LcBlock64:
  L.LcBlock64.xor(k, b)

def toy_key() -> L.LcBlock64:
  L.LcBlock64{19088743, 2309737967}

# a toy round function for the Feistel rounds: x + k, then rotated by 7
def toy_f(k: U32, x: U32) -> U32:
  L.lc.rotl(U32.add(x, k), 7n)

def msg() -> B.Octets:
  B.Octets.of_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23])

def iv() -> B.Octets:
  B.Octets.of_list([240, 241, 242, 243, 244, 245, 246, 247])

def ecb(m: B.Octets) -> String:
  +c = X.Lc64.ecb_encrypt(~L.LcBlock64, ~toy, toy_key(), m)
  show(c) ++ " " ++ show(Result.bind(&2, &2, L.LcError, B.Octets, B.Octets, c, x => X.Lc64.ecb_decrypt(~L.LcBlock64, ~toy, toy_key(), x)))

def cbc(+v: B.Octets, m: B.Octets) -> String:
  +c = X.Lc64.cbc_encrypt(~L.LcBlock64, ~toy, toy_key(), v, m)
  show(c) ++ " " ++ show(Result.bind(&2, &2, L.LcError, B.Octets, B.Octets, c, x => X.Lc64.cbc_decrypt(~L.LcBlock64, ~toy, toy_key(), v, x)))

def feistel(+b: L.LcBlock64) -> String:
  +ks = {[1, 2, 3, 4, 5, 6, 7, 8] : List<&2, U32>}
  +c = L.lc.fe.run(~U32, ~toy_f, ks, b)
  L.LcBlock64.hex(c) ++ " " ++ L.LcBlock64.hex(L.lc.fe.unrun(~U32, ~toy_f, ks, c))

def tab() -> String:
  +t = L.lc.tab(2n, [10, 20, 30, 40])
  word(L.lc.tab.get(2n, t, 2)) ++ " " ++ word(L.lc.tab.get(2n, L.lc.tab.set(2n, t, 1, 99), 1)) ++ " " ++ word(L.lc.tab.get(2n, t, 1))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(L.LcBlock64.hex(toy_key()))
    IO.print(B.Octets.hex(L.LcBlock64.to_octets(toy_key())))
    IO.print(show_some(L.LcBlock64.of_octets(L.LcBlock64.to_octets(toy_key()))))
    IO.print(show_some(L.LcBlock64.of_octets(B.Octets.zeros(7n))))
    IO.print(L.LcBlock64.hex(L.LcBlock64.xor(toy_key(), L.LcBlock64{4294967295, 0})))
    IO.print(word(L.lc.bswap.bits(16909060)) ++ " " ++ word(L.lc.rotl1.bits(2147483649)) ++ " " ++ word(L.lc.rotl(2147483649, 1n)) ++ " " ++ word(L.lc.rotl31.bits(3)))
    IO.print(word(L.lc.be(1, 2, 3, 4)) ++ " " ++ word(L.lc.le(1, 2, 3, 4)) ++ " " ++ word(L.lc.byte(16909060, 3n)))
    IO.print(tab())
    IO.print(feistel(L.LcBlock64{305419896, 2596069104}))
    IO.print(show_blocks(X.Lc64.blocks_of(msg())))
    IO.print(ecb(msg()))
    IO.print(cbc(iv(), msg()))
    IO.print(cbc(B.Octets.zeros(7n), msg()))
    IO.print(ecb(B.Octets.zeros(9n)))

#|0123456789abcdef
#|0123456789abcdef
#|0123456789abcdef
#|none
#|fedcba9889abcdef
#|0000000004030201 0000000000000003 0000000000000003 0000000080000001
#|0000000001020304 0000000004030201 0000000000000001
#|000000000000001e 0000000000000063 0000000000000014
#|3eefc45f6fc66333 123456789abcdef0
#|000102030405060708090a0b0c0d0e0f1011121314151617
#|012247648daecbe8092a4f6c85a6c3e0113257749dbedbf8 000102030405060708090a0b0c0d0e0f1011121314151617
#|f1d3b597795b3d1ff8f9fafbfcfdfeffe9cbad8f61432507 000102030405060708090a0b0c0d0e0f1011121314151617
#|bad iv 7 bad iv 7
#|not whole blocks 9 not whole blocks 9
