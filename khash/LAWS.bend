# Properties, for every input:
#  * the word forms agree: jhash_3words(a, b, c, iv) is jhash2 of [a, b, c],
#    and likewise for two words and one;
#  * hash_32(v, bits) fits in bits bits (for bits up to 32): shifting it
#    right by bits leaves 0.
#
# Vectors: the check values Jenkins publishes with lookup3 (hashlittle of ""
# from 0 and from 0xdeadbeef: 0xdeadbeef, 0xbd5b7dde; of "Four score and
# seven years ago" from 0 and 1: 0x17770551, 0xcd628161), jhash2 and the
# golden-ratio hashes on values from an independent model (ref/gen.py).
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./khash.bend as J
import ./golden.bend as G

law jhash_3words_jhash2:
  for +a: U32
  for +b: U32
  for +c: U32
  for +iv: U32
  {J.Jhash.jhash_3words(a, b, c, iv) == J.Jhash.jhash2([a, b, c], iv) : U32}

law jhash_2words_jhash2:
  for +a: U32
  for +b: U32
  for +iv: U32
  {J.Jhash.jhash_2words(a, b, iv) == J.Jhash.jhash2([a, b], iv) : U32}

law jhash_1word_jhash2:
  for +a: U32
  for +iv: U32
  {J.Jhash.jhash_1word(a, iv) == J.Jhash.jhash2([a], iv) : U32}

law hash_32_fits:
  for +v: U32
  for +bits: Nat
  for h: {Nat.is_le(bits, 32n) == True{} : Bool}
  {U32.shrn(G.KHash.hash_32(v, bits), bits) == 0 : U32}

law v_jhash_empty:
  {[J.Jhash.jhash(B.Octets.empty(), 0), J.Jhash.jhash(B.Octets.empty(), 3735928559)] == [3735928559, 3176889822] : List<&2, U32>}

law v_jhash_four_score:
  {[J.Jhash.jhash(B.Octets.of_string("Four score and seven years ago"), 0), J.Jhash.jhash(B.Octets.of_string("Four score and seven years ago"), 1)] == [393676113, 3445784929] : List<&2, U32>}

law v_jhash2:
  {[J.Jhash.jhash2([1, 2, 3, 4, 5, 6, 7], 13), J.Jhash.jhash2([3735928559], 0), J.Jhash.jhash2([], 5)] == [317751706, 2044973575, 3735928564] : List<&2, U32>}

law v_hash_32:
  {[G.KHash.hash_32(1, 32n), G.KHash.hash_32(1, 10n), G.KHash.hash_32(12345, 16n), G.KHash.hash_32(4294967295, 8n), G.KHash.hash_32(7, 0n)] == [1640531527, 391, 24275, 158, 0] : List<&2, U32>}

law v_hash_64:
  {[G.KHash.hash_64(W.W64.one(), 32n), G.KHash.hash_64(W.W64.one(), 10n), G.KHash.hash_64(W.W64.max(), 8n)] == [1640531526, 391, 158] : List<&2, U32>}
