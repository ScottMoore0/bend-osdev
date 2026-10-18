# PCBC, propagating cipher block chaining, over any block cipher of any block
# size (the block-cipher interface, block.bend), as the FCrypt specification
# (T. Anderson, 2000, "Modes of operation") and Kerberos version 4 use it:
#   C_i = E(P_i xor V_i),  V_1 = IV,  V_(i+1) = P_i xor C_i
#   P_i = D(C_i) xor V_i
# on lists of blocks and on bytes (a whole number of blocks, no padding; the
# chaining value after the last block is P_n xor C_n, so a message may
# arrive a block at a time through the block layer, CrPcbc.next_iv).
#
# Every loop over blocks is a tail call; the structural forms the proofs use
# are proved equal to them in PROOF.bend. Decryption undoes encryption for
# every key, IV and list of blocks wherever the cipher's decryption undoes
# its encryption: a law per instance (gen/instances.py, <c>_pcbc_round_trip).
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr
import ./modes.bend as Md

# Structural forms (the proofs' reference)

def cr.pcbc.enc(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, bs: List<&2, Blk>, v: Blk) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      +c = enc(k, bxor(p, v))
      Con{c, cr.pcbc.enc(~K, ~Blk, ~enc, ~bxor, k, t, bxor(p, c))}

def cr.pcbc.dec(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, bs: List<&2, Blk>, v: Blk) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      +p = bxor(dec(k, c), v)
      Con{p, cr.pcbc.dec(~K, ~Blk, ~dec, ~bxor, k, t, bxor(p, c))}

# The loops that run

def cr.pcbc.enc.go(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, bs: List<&2, Blk>, v: Blk, acc: List<&2, Blk>) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      Md.cr.blks.rev_onto(~Blk, acc, Nil{})
    case Con{+p, t}:
      +c = enc(k, bxor(p, v))
      cr.pcbc.enc.go(~K, ~Blk, ~enc, ~bxor, k, t, bxor(p, c), Con{c, acc})

def cr.pcbc.dec.go(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, bs: List<&2, Blk>, v: Blk, acc: List<&2, Blk>) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      Md.cr.blks.rev_onto(~Blk, acc, Nil{})
    case Con{+c, t}:
      +p = bxor(dec(k, c), v)
      cr.pcbc.dec.go(~K, ~Blk, ~dec, ~bxor, k, t, bxor(p, c), Con{p, acc})

# PCBC on blocks, from the chaining value v (the IV for the first call)
def CrPcbc.encrypt_blocks(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, v: Blk, bs: List<&2, Blk>) -> List<&2, Blk>:
  cr.pcbc.enc.go(~K, ~Blk, ~enc, ~bxor, k, bs, v, Nil{})

def CrPcbc.decrypt_blocks(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, v: Blk, bs: List<&2, Blk>) -> List<&2, Blk>:
  cr.pcbc.dec.go(~K, ~Blk, ~dec, ~bxor, k, bs, v, Nil{})

def cr.pcbc.last(~Blk: Data, ~bxor: Blk -> Blk -> Blk, ps: List<&2, Blk>, cs: List<&2, Blk>, v: Blk) -> Blk:
  match ps cs:
    case Con{p, pt} Con{c, ct}:
      cr.pcbc.last(~Blk, ~bxor, pt, ct, bxor(p, c))
    case _ _:
      v

# The chaining value after the plaintext blocks ps encrypted to cs from v:
# the next call's v, so a message may arrive in pieces of whole blocks
def CrPcbc.next_iv(~Blk: Data, ~bxor: Blk -> Blk -> Blk, v: Blk, ps: List<&2, Blk>, cs: List<&2, Blk>) -> Blk:
  cr.pcbc.last(~Blk, ~bxor, ps, cs, v)

# PCBC on bytes: a message of whole blocks under a one-block IV
# (CrBadIvLength, CrNotBlockMultiple otherwise)
def CrPcbc.encrypt(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, iv: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  do Result<&2, &2, Cr.CrError, B.Octets>:
    v : Blk <- Md.cr.iv(~Blk, ~blk_of, iv)
    bs : List<&2, Blk> <- Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, m)
    return Md.CrModes.octets_of(~Blk, ~blk_to, CrPcbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs))

def CrPcbc.decrypt(~K: Data, ~Blk: Data, ~bsize: Nat, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, iv: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  do Result<&2, &2, Cr.CrError, B.Octets>:
    v : Blk <- Md.cr.iv(~Blk, ~blk_of, iv)
    bs : List<&2, Blk> <- Md.CrModes.blocks_of(~Blk, ~bsize, ~blk_of, c)
    return Md.CrModes.octets_of(~Blk, ~blk_to, CrPcbc.decrypt_blocks(~K, ~Blk, ~dec, ~bxor, k, v, bs))
