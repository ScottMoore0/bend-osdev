# Laws about mode-core's public interface: a block survives its byte form;
# and the lemmas the modes' proofs share (bend-osdev-cbc, -xts, -ccm, and
# -aes for the block's bytes), as laws: a package's proofs can use another
# package's laws, not its private lemmas.
import Base
import ../bytes/bytes.bend as B
import ./mode-core.bend as M

# A block written as Octets reads back as the same block, for every block
law block_octets_round_trip:
  for +b: M.CmBlock
  {M.CmBlock.of_octets(M.CmBlock.to_octets(b)) == Some{b} : Maybe<&2, M.CmBlock>}

# Lemmas the modes' proofs share, as laws (new with the split of
# bend-osdev-cipher-modes; they were private lemmas of its PROOF.bend). They
# are about the byte layer every mode is built from (mode-core.bend's cm.*),
# bytes' list layer, XOR, and the round-trip hypothesis CmBlock.dec_enc.

law byte_byte:
  for y: U32
  {B.byte(B.byte(y)) == B.byte(y) : U32}

law split_cons_blocks:
  for b: M.CmBlock
  for s: M.CmSplit
  {M.cm.split.blocks(M.cm.split.cons(b, s)) == Con{b, M.cm.split.blocks(s)} : List<&2, M.CmBlock>}

law split_cons_tail:
  for b: M.CmBlock
  for s: M.CmSplit
  {M.cm.split.tail(M.cm.split.cons(b, s)) == M.cm.split.tail(s) : List<&2, U32>}

law split_eta:
  for s: M.CmSplit
  {M.CmSplit{M.cm.split.blocks(s), M.cm.split.tail(s)} == s : M.CmSplit}

law list_take_append:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {B.take(B.len(a), B.append(a, b)) == a : List<&2, U32>}

law list_drop_append:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {B.drop(B.len(a), B.append(a, b)) == b : List<&2, U32>}

law list_mask_append:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {B.mask(B.append(a, b)) == B.append(B.mask(a), B.mask(b)) : List<&2, U32>}

law list_mask_take:
  for +n: Nat
  for +xs: List<&2, U32>
  {B.mask(B.take(n, xs)) == B.take(n, B.mask(xs)) : List<&2, U32>}

law list_len_append:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {B.len(B.append(a, b)) == Nat.add(B.len(a), B.len(b)) : Nat}

law list_len_take:
  for +n: Nat
  for +xs: List<&2, U32>
  for h1: {Nat.is_le(n, B.len(xs)) == True{} : Bool}
  {B.len(B.take(n, xs)) == n : Nat}

law nat_lt_le:
  for +a: Nat
  for +b: Nat
  for h1: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_le(a, b) == True{} : Bool}

# splitting the bytes of a block gives the block back
law split_bytes_onto:
  for b: M.CmBlock
  for rest: List<&2, U32>
  {M.cm.split(M.cm.bytes_onto(b, rest)) == M.cm.split.cons(b, M.cm.split(rest)) : M.CmSplit}

# the bytes of a block are bytes: masking changes nothing
law mask_bytes_onto:
  for b: M.CmBlock
  for rest: List<&2, U32>
  {B.mask(M.cm.bytes_onto(b, rest)) == M.cm.bytes_onto(b, B.mask(rest)) : List<&2, U32>}

# a masked list is its blocks and its tail joined back
law join_split:
  for ys: List<&2, U32>
  {M.cm.join_onto(M.cm.split.blocks(M.cm.split(B.mask(ys))), M.cm.split.tail(M.cm.split(B.mask(ys)))) == B.mask(ys) : List<&2, U32>}

# the bytes of the block of any 16 values are those values, masked
law bytes_onto_block16:
  for z0: U32
  for z1: U32
  for z2: U32
  for z3: U32
  for z4: U32
  for z5: U32
  for z6: U32
  for z7: U32
  for z8: U32
  for z9: U32
  for z10: U32
  for z11: U32
  for z12: U32
  for z13: U32
  for z14: U32
  for z15: U32
  for rest: List<&2, U32>
  {M.cm.bytes_onto(M.cm.block16(z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15), rest) == Con{B.byte(z0), Con{B.byte(z1), Con{B.byte(z2), Con{B.byte(z3), Con{B.byte(z4), Con{B.byte(z5), Con{B.byte(z6), Con{B.byte(z7), Con{B.byte(z8), Con{B.byte(z9), Con{B.byte(z10), Con{B.byte(z11), Con{B.byte(z12), Con{B.byte(z13), Con{B.byte(z14), Con{B.byte(z15), rest}}}}}}}}}}}}}}}} : List<&2, U32>}

# the tail of a split has fewer than 16 bytes
law split_tail_short:
  for ys: List<&2, U32>
  {Nat.is_lt(B.len(M.cm.split.tail(M.cm.split(B.mask(ys)))), 16n) == True{} : Bool}

# the tail of a masked split is masked
law split_tail_masked:
  for ys: List<&2, U32>
  {B.mask(M.cm.split.tail(M.cm.split(B.mask(ys)))) == M.cm.split.tail(M.cm.split(B.mask(ys))) : List<&2, U32>}

# fewer than 16 bytes are all tail
law split_short:
  for ys: List<&2, U32>
  for h1: {Nat.is_lt(B.len(ys), 16n) == True{} : Bool}
  {M.cm.split(ys) == M.CmSplit{Nil{}, ys} : M.CmSplit}

# the block of a block's bytes is the block
law block_of_bytes_of:
  for b: M.CmBlock
  {M.cm.block_of(M.cm.bytes_of(b)) == b : M.CmBlock}

# Every Octets is masked: to_list(o) = to_list(of_list(to_list(o))) = mask(to_list(o))
law octets_masked:
  for +o: B.Octets
  {B.mask(B.Octets.to_list(o)) == B.Octets.to_list(o) : List<&2, U32>}

law octets_len:
  for +o: B.Octets
  for +n: Nat
  for h: {B.Octets.len(o) == n : Nat}
  {B.len(B.Octets.to_list(o)) == n : Nat}

law blocks_len_fast:
  for +bs: List<&2, M.CmBlock>
  {List.length(&2, M.CmBlock, bs) == M.cm.blocks.len(bs) : Nat}

law split_fast:
  for +xs: List<&2, U32>
  {M.cm.split(xs) == M.cm.split.fast(xs) : M.CmSplit}

law join_onto_fast:
  for +bs: List<&2, M.CmBlock>
  for +rest: List<&2, U32>
  {M.cm.join_onto(bs, rest) == M.cm.join_onto.fast(bs, rest) : List<&2, U32>}

# a bind whose continuations agree on every value agrees
law bind_cong:
  for r: Result<&2, &2, M.CmError, B.Octets>
  for f: B.Octets -> Result<&2, &2, M.CmError, B.Octets>
  for g: B.Octets -> Result<&2, &2, M.CmError, B.Octets>
  for h: @c: B.Octets -> {f(c) == g(c) : Result<&2, &2, M.CmError, B.Octets>}
  {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, r, f) == Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, r, g) : Result<&2, &2, M.CmError, B.Octets>}

# the first block's round trip, and the rest's
law dec_enc_head:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for ~dec: K -> M.CmBlock -> M.CmBlock
  for +k: K
  for +x: M.CmBlock
  for +xs: List<&2, M.CmBlock>
  for +h: {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, Con{x, xs}) == Con{x, xs} : List<&2, M.CmBlock>}
  {dec(k, enc(k, x)) == x : M.CmBlock}

law dec_enc_tail:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for ~dec: K -> M.CmBlock -> M.CmBlock
  for +k: K
  for +x: M.CmBlock
  for +xs: List<&2, M.CmBlock>
  for +h: {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, Con{x, xs}) == Con{x, xs} : List<&2, M.CmBlock>}
  {M.CmBlock.dec_enc(~K, ~enc, ~dec, k, xs) == xs : List<&2, M.CmBlock>}

law word_xor_xor:
  for n: Nat
  for a: Word(n)
  for b: Word(n)
  {Word.xor(n, Word.xor(n, a, b), b) == a : Word(n)}

law u32_xor_xor:
  for a: U32
  for b: U32
  {U32.xor(U32.xor(a, b), b) == a : U32}

law block_xor_xor:
  for +a: M.CmBlock
  for +b: M.CmBlock
  {M.CmBlock.xor(M.CmBlock.xor(a, b), b) == a : M.CmBlock}

law mask_join_onto:
  for bs: List<&2, M.CmBlock>
  for +rest: List<&2, U32>
  {B.mask(M.cm.join_onto(bs, rest)) == M.cm.join_onto(bs, B.mask(rest)) : List<&2, U32>}

# blocks joined in front of a short tail split back into those blocks and tail
law split_join_short:
  for bs: List<&2, M.CmBlock>
  for +rest: List<&2, U32>
  for h1: {M.cm.split(rest) == M.CmSplit{Nil{}, rest} : M.CmSplit}
  {M.cm.split(M.cm.join_onto(bs, rest)) == M.CmSplit{bs, rest} : M.CmSplit}
