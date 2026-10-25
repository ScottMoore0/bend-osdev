# Laws about cipher-core's public interface: 64-bit blocks survive their
# byte form, the 64-bit modes refuse what is not whole blocks; and the
# lemmas the ciphers' proofs share (XOR undone, the rotations and byte swaps
# on bits undone, Feistel rounds undone, the 64-bit modes' layers), as laws.
import Base
import ../bytes/bytes.bend as B
import ./cipher-core.bend as L
import ./modes64.bend as X

# 64-bit blocks as bytes: a block read back from its 8 bytes is itself, 8
# bytes read as a block are written back as those bytes, and a list of
# blocks read back from its bytes is itself
law block64_octets_round_trip:
  for +b: L.LcBlock64
  {L.LcBlock64.of_octets(L.LcBlock64.to_octets(b)) == Some{b} : Maybe<&2, L.LcBlock64>}

law block64_octets_dual:
  for +o: B.Octets
  for +b: L.LcBlock64
  for e: {L.LcBlock64.of_octets(o) == Some{b} : Maybe<&2, L.LcBlock64>}
  {L.LcBlock64.to_octets(b) == o : B.Octets}

law blocks64_octets_round_trip:
  for +bs: List<&2, L.LcBlock64>
  {X.Lc64.blocks_of(X.Lc64.octets_of(bs)) == Done{bs} : Result<&2, &2, L.LcError, List<&2, L.LcBlock64>>}

# Lemmas the ciphers' proofs share, as laws (a package's proofs can use
# another package's laws, not its private lemmas). Each is stated simple
# side first, the form a rewrite (%e : P) takes.

# XOR undone, for every word of any width, every 32-bit word and every
# 64-bit block
law word_xor_cancel:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {a == Word.xor(n, Word.xor(n, a, b), b) : Word(n)}

law u32_xor_cancel:
  for a: U32
  for b: U32
  {a == U32.xor(U32.xor(a, b), b) : U32}

law block64_xor_cancel:
  for a: L.LcBlock64
  for b: L.LcBlock64
  {b == L.LcBlock64.xor(a, L.LcBlock64.xor(a, b)) : L.LcBlock64}

# the rotations by 1 and 31 bits on bits undo each other, and the byte swap
# on bits undoes itself, for every word
law rotl1_rotl31:
  for x: U32
  {x == L.lc.rotl1.bits(L.lc.rotl31.bits(x)) : U32}

law rotl31_rotl1:
  for x: U32
  {x == L.lc.rotl31.bits(L.lc.rotl1.bits(x)) : U32}

law bswap_bswap:
  for x: U32
  {x == L.lc.bswap.bits(L.lc.bswap.bits(x)) : U32}

# Feistel rounds over any round function f and any round keys: the rounds
# undone last to first undo the rounds, and the other way round
law feistel_unrun_run:
  for ~RK: Data
  for ~f: RK -> U32 -> U32
  for ks: List<&2, RK>
  for +b: L.LcBlock64
  {b == L.lc.fe.unrun(~RK, ~f, ks, L.lc.fe.run(~RK, ~f, ks, b)) : L.LcBlock64}

law feistel_run_unrun:
  for ~RK: Data
  for ~f: RK -> U32 -> U32
  for ks: List<&2, RK>
  for +b: L.LcBlock64
  {b == L.lc.fe.run(~RK, ~f, ks, L.lc.fe.unrun(~RK, ~f, ks, b)) : L.LcBlock64}

# The 64-bit modes over any cipher: decryption after encryption on blocks is
# the structural forms' (X.m64.ecb, X.m64.cbc.enc, X.m64.cbc.dec), over
# which a cipher's own round trip proves the mode's by induction; and on
# bytes, for the bytes of a list of blocks under the bytes of an IV, it is
# the block layer's
law modes64_ecb_blocks:
  for ~K: Data
  for ~enc: K -> L.LcBlock64 -> L.LcBlock64
  for ~dec: K -> L.LcBlock64 -> L.LcBlock64
  for +k: K
  for +bs: List<&2, L.LcBlock64>
  {X.m64.ecb(~K, ~dec, k, X.m64.ecb(~K, ~enc, k, bs)) == X.Lc64.ecb_decrypt_blocks(~K, ~dec, k, X.Lc64.ecb_encrypt_blocks(~K, ~enc, k, bs)) : List<&2, L.LcBlock64>}

law modes64_cbc_blocks:
  for ~K: Data
  for ~enc: K -> L.LcBlock64 -> L.LcBlock64
  for ~dec: K -> L.LcBlock64 -> L.LcBlock64
  for +k: K
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {X.m64.cbc.dec(~K, ~dec, k, X.m64.cbc.enc(~K, ~enc, k, bs, iv), iv) == X.Lc64.cbc_decrypt_blocks(~K, ~dec, k, iv, X.Lc64.cbc_encrypt_blocks(~K, ~enc, k, iv, bs)) : List<&2, L.LcBlock64>}

law modes64_ecb_octets:
  for ~K: Data
  for ~enc: K -> L.LcBlock64 -> L.LcBlock64
  for ~dec: K -> L.LcBlock64 -> L.LcBlock64
  for +k: K
  for +bs: List<&2, L.LcBlock64>
  {Done{X.Lc64.octets_of(X.Lc64.ecb_decrypt_blocks(~K, ~dec, k, X.Lc64.ecb_encrypt_blocks(~K, ~enc, k, bs)))} == Result.bind(&2, &2, L.LcError, B.Octets, B.Octets, X.Lc64.ecb_encrypt(~K, ~enc, k, X.Lc64.octets_of(bs)), c => X.Lc64.ecb_decrypt(~K, ~dec, k, c)) : Result<&2, &2, L.LcError, B.Octets>}

law modes64_cbc_octets:
  for ~K: Data
  for ~enc: K -> L.LcBlock64 -> L.LcBlock64
  for ~dec: K -> L.LcBlock64 -> L.LcBlock64
  for +k: K
  for +iv: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  {Done{X.Lc64.octets_of(X.Lc64.cbc_decrypt_blocks(~K, ~dec, k, iv, X.Lc64.cbc_encrypt_blocks(~K, ~enc, k, iv, bs)))} == Result.bind(&2, &2, L.LcError, B.Octets, B.Octets, X.Lc64.cbc_encrypt(~K, ~enc, k, L.LcBlock64.to_octets(iv), X.Lc64.octets_of(bs)), c => X.Lc64.cbc_decrypt(~K, ~dec, k, L.LcBlock64.to_octets(iv), c)) : Result<&2, &2, L.LcError, B.Octets>}


# the 64-bit modes refuse a message that is not whole blocks
law modes64_not_whole_blocks:
  {Result.map(&2, &2, L.LcError, List<&2, L.LcBlock64>, Unit, bs => Unit{}, X.Lc64.blocks_of(B.Octets.zeros(12n))) == Fail{L.LcNotBlockMultiple{12n}} : Result<&2, &2, L.LcError, Unit>}
