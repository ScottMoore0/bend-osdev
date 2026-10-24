# Laws of the byte layer of the block-cipher modes (modes.bend, pcbc.bend,
# lrw.bend): CrModes.blocks_of reads back the blocks that CrModes.octets_of
# wrote, for every block size, and so ECB, CBC, PCBC and LRW on bytes undo
# themselves wherever they do on blocks. In a pair of their own
# (CONVENTIONS.md, Laws): their proofs rest on bytes' laws and on
# legacy-ciphers' 64-bit block format (block64_octets_round_trip, so they
# take in legacy-ciphers' proofs), and on no other package's.
#
# The byte layer cuts a byte string into pieces of the block size and reads
# each through the block format (~blk_of), and writes blocks back through
# ~blk_to. Its law for every block size takes the format's two properties
# at the blocks it is used on, as ordinary hypotheses on the list of
# blocks (README.md, "How the laws are stated"): every block's bytes are
# bsize bytes (hl), and read back as the block (hf). The two block formats
# of the instances (inst_cm.bend's 128-bit CmBlock, legacy-ciphers' 64-bit
# LcBlock64) satisfy them for every list, so their laws take none.
import Base
import ../bytes/bytes.bend as B
import ../cipher-modes/cipher-modes.bend as M
import ../legacy-ciphers/legacy-ciphers.bend as L
import ../gf/gf128.bend as G
import ./crypto.bend as Cr
import ./modes.bend as Md
import ./pcbc.bend as Pc
import ./lrw.bend as Lw
import ./inst_cm.bend as CM
import ./inst_lc.bend as LC

# The format's properties on a list of blocks, through its public defs:
# the length of each block's bytes, and each block's bytes read back

def crbl.lens(~Blk: Data, ~blk_to: Blk -> B.Octets, bs: List<&2, Blk>) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{B.Octets.len(blk_to(b)), crbl.lens(~Blk, ~blk_to, t)}

def crbl.reps(~Blk: Data, +n: Nat, bs: List<&2, Blk>) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{n, crbl.reps(~Blk, n, t)}

def crbl.reads(~Blk: Data, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, bs: List<&2, Blk>) -> List<&2, Maybe<&2, Blk>>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{blk_of(blk_to(b)), crbl.reads(~Blk, ~blk_of, ~blk_to, t)}

def crbl.somes(~Blk: Data, bs: List<&2, Blk>) -> List<&2, Maybe<&2, Blk>>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{Some{b}, crbl.somes(~Blk, t)}

# For every block size (at least 1), block format and list of blocks whose
# bytes are bsize bytes each (hl) and read back as the blocks (hf): the
# bytes of the blocks are read back as the blocks
law modes_blocks_of_octets_of:
  for ~Blk: Data
  for ~bsize: Nat
  for ~blk_of: B.Octets -> Maybe<&2, Blk>
  for ~blk_to: Blk -> B.Octets
  for +bs: List<&2, Blk>
  for hb: {Nat.is_lt(0n, bsize) == True{} : Bool}
  for hl: {crbl.lens(~Blk, ~blk_to, bs) == crbl.reps(~Blk, bsize, bs) : List<&2, Nat>}
  for hf: {crbl.reads(~Blk, ~blk_of, ~blk_to, bs) == crbl.somes(~Blk, bs) : List<&2, Maybe<&2, Blk>>}
  {Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, Md.CrModes.octets_of(~Blk, ~blk_to, bs)) == Done{bs} : Result<&2, &2, Cr.CrError, List<&2, Blk>>}

# The two block formats: every list of blocks is read back from its bytes

law cmblock_blocks_of_octets_of:
  for +bs: List<&2, M.CmBlock>
  {Md.CrModes.blocks_of(~M.CmBlock, ~16n, ~CM.CrBlk128.of_octets, Md.CrModes.octets_of(~M.CmBlock, ~CM.CrBlk128.to_octets, bs)) == Done{bs} : Result<&2, &2, Cr.CrError, List<&2, M.CmBlock>>}

law lcblock64_blocks_of_octets_of:
  for +bs: List<&2, L.LcBlock64>
  {Md.CrModes.blocks_of(~L.LcBlock64, ~8n, ~L.LcBlock64.of_octets, Md.CrModes.octets_of(~L.LcBlock64, ~L.LcBlock64.to_octets, bs)) == Done{bs} : Result<&2, &2, Cr.CrError, List<&2, L.LcBlock64>>}

# ECB, CBC, PCBC and LRW on bytes: for every block cipher over one of the
# formats, every key and every message of whole blocks (the bytes of a list
# of blocks bs, CrModes.octets_of), and for CBC and PCBC every IV block v
# (as its bytes) and for LRW every key pair and first index i (any IV that
# gf128 reads as i): encryption succeeds and decryption gives the message
# back, wherever decryption undoes encryption on the blocks (h, at the
# arguments used: for an instance, its <c>_ecb_round_trip,
# <c>_cbc_round_trip, <c>_pcbc_round_trip or <c>_lrw_round_trip)

law cmblock_ecb_octets_round_trip:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for ~dec: K -> M.CmBlock -> M.CmBlock
  for +k: K
  for +bs: List<&2, M.CmBlock>
  for h: {Md.CrEcb.decrypt_blocks(~K, ~M.CmBlock, ~dec, k, Md.CrEcb.encrypt_blocks(~K, ~M.CmBlock, ~enc, k, bs)) == bs : List<&2, M.CmBlock>}
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Md.CrEcb.encrypt(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, Md.CrModes.octets_of(~M.CmBlock, ~CM.CrBlk128.to_octets, bs)), c => Md.CrEcb.decrypt(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, c)) == Done{Md.CrModes.octets_of(~M.CmBlock, ~CM.CrBlk128.to_octets, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}

law lcblock64_ecb_octets_round_trip:
  for ~K: Data
  for ~enc: K -> L.LcBlock64 -> L.LcBlock64
  for ~dec: K -> L.LcBlock64 -> L.LcBlock64
  for +k: K
  for +bs: List<&2, L.LcBlock64>
  for h: {Md.CrEcb.decrypt_blocks(~K, ~L.LcBlock64, ~dec, k, Md.CrEcb.encrypt_blocks(~K, ~L.LcBlock64, ~enc, k, bs)) == bs : List<&2, L.LcBlock64>}
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Md.CrEcb.encrypt(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, Md.CrModes.octets_of(~L.LcBlock64, ~L.LcBlock64.to_octets, bs)), c => Md.CrEcb.decrypt(~K, ~L.LcBlock64, ~8n, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, c)) == Done{Md.CrModes.octets_of(~L.LcBlock64, ~L.LcBlock64.to_octets, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}

law cmblock_cbc_octets_round_trip:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for ~dec: K -> M.CmBlock -> M.CmBlock
  for +k: K
  for +v: M.CmBlock
  for +bs: List<&2, M.CmBlock>
  for h: {Md.CrCbc.decrypt_blocks(~K, ~M.CmBlock, ~dec, ~CM.CrBlk128.xor, k, v, Md.CrCbc.encrypt_blocks(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.xor, k, v, bs)) == bs : List<&2, M.CmBlock>}
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Md.CrCbc.encrypt(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, CM.CrBlk128.to_octets(v), Md.CrModes.octets_of(~M.CmBlock, ~CM.CrBlk128.to_octets, bs)), c => Md.CrCbc.decrypt(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, CM.CrBlk128.to_octets(v), c)) == Done{Md.CrModes.octets_of(~M.CmBlock, ~CM.CrBlk128.to_octets, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}

law lcblock64_cbc_octets_round_trip:
  for ~K: Data
  for ~enc: K -> L.LcBlock64 -> L.LcBlock64
  for ~dec: K -> L.LcBlock64 -> L.LcBlock64
  for +k: K
  for +v: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  for h: {Md.CrCbc.decrypt_blocks(~K, ~L.LcBlock64, ~dec, ~LC.CrBlk64.xor, k, v, Md.CrCbc.encrypt_blocks(~K, ~L.LcBlock64, ~enc, ~LC.CrBlk64.xor, k, v, bs)) == bs : List<&2, L.LcBlock64>}
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Md.CrCbc.encrypt(~K, ~L.LcBlock64, ~8n, ~enc, ~LC.CrBlk64.xor, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, L.LcBlock64.to_octets(v), Md.CrModes.octets_of(~L.LcBlock64, ~L.LcBlock64.to_octets, bs)), c => Md.CrCbc.decrypt(~K, ~L.LcBlock64, ~8n, ~dec, ~LC.CrBlk64.xor, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, L.LcBlock64.to_octets(v), c)) == Done{Md.CrModes.octets_of(~L.LcBlock64, ~L.LcBlock64.to_octets, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}

law cmblock_pcbc_octets_round_trip:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for ~dec: K -> M.CmBlock -> M.CmBlock
  for +k: K
  for +v: M.CmBlock
  for +bs: List<&2, M.CmBlock>
  for h: {Pc.CrPcbc.decrypt_blocks(~K, ~M.CmBlock, ~dec, ~CM.CrBlk128.xor, k, v, Pc.CrPcbc.encrypt_blocks(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.xor, k, v, bs)) == bs : List<&2, M.CmBlock>}
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Pc.CrPcbc.encrypt(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, CM.CrBlk128.to_octets(v), Md.CrModes.octets_of(~M.CmBlock, ~CM.CrBlk128.to_octets, bs)), c => Pc.CrPcbc.decrypt(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, CM.CrBlk128.to_octets(v), c)) == Done{Md.CrModes.octets_of(~M.CmBlock, ~CM.CrBlk128.to_octets, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}

law lcblock64_pcbc_octets_round_trip:
  for ~K: Data
  for ~enc: K -> L.LcBlock64 -> L.LcBlock64
  for ~dec: K -> L.LcBlock64 -> L.LcBlock64
  for +k: K
  for +v: L.LcBlock64
  for +bs: List<&2, L.LcBlock64>
  for h: {Pc.CrPcbc.decrypt_blocks(~K, ~L.LcBlock64, ~dec, ~LC.CrBlk64.xor, k, v, Pc.CrPcbc.encrypt_blocks(~K, ~L.LcBlock64, ~enc, ~LC.CrBlk64.xor, k, v, bs)) == bs : List<&2, L.LcBlock64>}
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Pc.CrPcbc.encrypt(~K, ~L.LcBlock64, ~8n, ~enc, ~LC.CrBlk64.xor, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, L.LcBlock64.to_octets(v), Md.CrModes.octets_of(~L.LcBlock64, ~L.LcBlock64.to_octets, bs)), c => Pc.CrPcbc.decrypt(~K, ~L.LcBlock64, ~8n, ~dec, ~LC.CrBlk64.xor, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, L.LcBlock64.to_octets(v), c)) == Done{Md.CrModes.octets_of(~L.LcBlock64, ~L.LcBlock64.to_octets, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}

law cmblock_lrw_octets_round_trip:
  for ~K: Data
  for ~enc: K -> M.CmBlock -> M.CmBlock
  for ~dec: K -> M.CmBlock -> M.CmBlock
  for +k: K
  for +k2: G.Gf128
  for +i: G.Gf128
  for +iv: B.Octets
  for hi: {G.Gf128.of_octets(iv) == Done{i} : Result<&2, &2, G.Gf128Error, G.Gf128>}
  for +bs: List<&2, M.CmBlock>
  for h: {Lw.CrLrw.decrypt_blocks(~K, ~M.CmBlock, ~dec, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, Lw.CrLrw.encrypt_blocks(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, k, k2, i, bs)) == bs : List<&2, M.CmBlock>}
  {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Lw.CrLrw.encrypt(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, Lw.CrLrwKey{k, k2}, iv, Md.CrModes.octets_of(~M.CmBlock, ~CM.CrBlk128.to_octets, bs)), c => Lw.CrLrw.decrypt(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.xor, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, Lw.CrLrwKey{k, k2}, iv, c)) == Done{Md.CrModes.octets_of(~M.CmBlock, ~CM.CrBlk128.to_octets, bs)} : Result<&2, &2, Cr.CrError, B.Octets>}
