# Modes of operation over any block cipher of any block size (the
# block-cipher interface, block.bend): ECB and CBC (NIST SP 800-38A, 6.1 and
# 6.2) on lists of blocks and on bytes, and CTR (SP 800-38A, 6.5) as a stream
# cipher.
#
# the 128-bit ciphers have the modes of their own packages too (cbc, xts, ccm, cmac);
# these are the ones every block size shares, so a 64-bit cipher (DES, 3DES)
# and a 128-bit one run through the same code.
#
# Every loop over blocks or bytes is a tail call (the structural forms the
# proofs use are proved equal to them in PROOF.bend).
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr
import ./stream.bend as St

# Lists of blocks

def cr.blks.rev_onto(~Blk: Data, bs: List<&2, Blk>, acc: List<&2, Blk>) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      acc
    case Con{b, t}:
      cr.blks.rev_onto(~Blk, t, Con{b, acc})

# ECB: each block on its own (structural, and the loop that runs)

def cr.ecb(~K: Data, ~Blk: Data, ~f: K -> Blk -> Blk, +k: K, bs: List<&2, Blk>) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{f(k, b), cr.ecb(~K, ~Blk, ~f, k, t)}

def cr.ecb.go(~K: Data, ~Blk: Data, ~f: K -> Blk -> Blk, +k: K, bs: List<&2, Blk>, acc: List<&2, Blk>) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      cr.blks.rev_onto(~Blk, acc, Nil{})
    case Con{b, t}:
      cr.ecb.go(~K, ~Blk, ~f, k, t, Con{f(k, b), acc})

def CrEcb.encrypt_blocks(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, +k: K, bs: List<&2, Blk>) -> List<&2, Blk>:
  cr.ecb.go(~K, ~Blk, ~enc, k, bs, Nil{})

def CrEcb.decrypt_blocks(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, +k: K, bs: List<&2, Blk>) -> List<&2, Blk>:
  cr.ecb.go(~K, ~Blk, ~dec, k, bs, Nil{})

# CBC: C_i = E(P_i xor C_{i-1}), C_0 the IV (structural, and the loops)

def cr.cbc.enc(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, bs: List<&2, Blk>, iv: Blk) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      +c = enc(k, bxor(p, iv))
      Con{c, cr.cbc.enc(~K, ~Blk, ~enc, ~bxor, k, t, c)}

def cr.cbc.dec(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, bs: List<&2, Blk>, iv: Blk) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      Con{bxor(dec(k, c), iv), cr.cbc.dec(~K, ~Blk, ~dec, ~bxor, k, t, c)}

def cr.cbc.enc.go(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, bs: List<&2, Blk>, iv: Blk, acc: List<&2, Blk>) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      cr.blks.rev_onto(~Blk, acc, Nil{})
    case Con{p, t}:
      +c = enc(k, bxor(p, iv))
      cr.cbc.enc.go(~K, ~Blk, ~enc, ~bxor, k, t, c, Con{c, acc})

def cr.cbc.dec.go(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, bs: List<&2, Blk>, iv: Blk, acc: List<&2, Blk>) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      cr.blks.rev_onto(~Blk, acc, Nil{})
    case Con{+c, t}:
      cr.cbc.dec.go(~K, ~Blk, ~dec, ~bxor, k, t, c, Con{bxor(dec(k, c), iv), acc})

# CBC on blocks: the last ciphertext block of one call is the IV of the next,
# so a message may arrive a block at a time
def CrCbc.encrypt_blocks(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, iv: Blk, bs: List<&2, Blk>) -> List<&2, Blk>:
  cr.cbc.enc.go(~K, ~Blk, ~enc, ~bxor, k, bs, iv, Nil{})

def CrCbc.decrypt_blocks(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, +k: K, iv: Blk, bs: List<&2, Blk>) -> List<&2, Blk>:
  cr.cbc.dec.go(~K, ~Blk, ~dec, ~bxor, k, bs, iv, Nil{})

# Bytes as blocks

def cr.pick_n(full: Bool, +n: Nat) -> Nat:
  match full:
    case True{}:
      0n
    case False{}:
      n

def cr.pick_cur(full: Bool, +c: List<&2, U32>) -> List<&2, U32>:
  match full:
    case True{}:
      Nil{}
    case False{}:
      c

def cr.pick_acc(full: Bool, +c: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match full:
    case True{}:
      Con{St.cr.rev_onto(c, Nil{}), acc}
    case False{}:
      acc

# the whole n-byte pieces of xs, last first (cur: the piece being filled,
# reversed, i bytes long)
def cr.chunks(xs: List<&2, U32>, +n: Nat, +i: Nat, +cur: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      +c : List<&2, U32> = Con{x, cur}
      +full = Nat.is_eq(1n+i, n)
      cr.chunks(t, n, cr.pick_n(full, 1n+i), cr.pick_cur(full, c), cr.pick_acc(full, c, acc))

# a block onto a list of blocks, None if either is missing
def cr.cons_m(~Blk: Data, m: Maybe<&2, Blk>, acc: Maybe<&2, List<&2, Blk>>) -> Maybe<&2, List<&2, Blk>>:
  match m acc:
    case Some{b} Some{l}:
      Some{Con{b, l}}
    case _ _:
      None{}

# the pieces (last first) as blocks, in order, onto acc
def cr.blocks_of.go(~Blk: Data, ~blk_of: B.Octets -> Maybe<&2, Blk>, ps: List<&2, List<&2, U32>>, acc: Maybe<&2, List<&2, Blk>>) -> Maybe<&2, List<&2, Blk>>:
  match ps:
    case Nil{}:
      acc
    case Con{p, t}:
      cr.blocks_of.go(~Blk, ~blk_of, t, cr.cons_m(~Blk, blk_of(B.Octets.of_list(p)), acc))

def cr.divides(pos: Bool, +len: Nat, +n: Nat) -> Bool:
  match pos:
    case True{}:
      Nat.is_eq(Nat.mod(len, n), 0n)
    case False{}:
      False{}

def cr.blocks_of.some(~Blk: Data, m: Maybe<&2, List<&2, Blk>>, +len: Nat) -> Result<&2, &2, Cr.CrError, List<&2, Blk>>:
  match m:
    case None{}:
      Fail{Cr.CrBadBlockSize{len}}
    case Some{bs}:
      Done{bs}

def cr.blocks_of.ok(~Blk: Data, ok: Bool, m: Maybe<&2, List<&2, Blk>>, +len: Nat) -> Result<&2, &2, Cr.CrError, List<&2, Blk>>:
  match ok:
    case False{}:
      Fail{Cr.CrNotBlockMultiple{len}}
    case True{}:
      cr.blocks_of.some(~Blk, m, len)

# A byte string of whole blocks as its blocks (CrNotBlockMultiple otherwise)
def CrModes.blocks_of(~Blk: Data, ~bsize: Nat, ~blk_of: B.Octets -> Maybe<&2, Blk>, o: B.Octets) -> Result<&2, &2, Cr.CrError, List<&2, Blk>>:
  +xs = B.Octets.to_list(o)
  +len = B.len.fast(xs)
  cr.blocks_of.ok(~Blk, cr.divides(Nat.is_lt(0n, bsize), len, bsize), cr.blocks_of.go(~Blk, ~blk_of, cr.chunks(xs, bsize, 0n, Nil{}, Nil{}), Some{Nil{}}), len)

def cr.octets_of.go(~Blk: Data, ~blk_to: Blk -> B.Octets, bs: List<&2, Blk>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match bs:
    case Nil{}:
      acc
    case Con{b, t}:
      cr.octets_of.go(~Blk, ~blk_to, t, Con{blk_to(b), acc})

# The bytes of a list of blocks
def CrModes.octets_of(~Blk: Data, ~blk_to: Blk -> B.Octets, bs: List<&2, Blk>) -> B.Octets:
  B.Octets.concat(cr.blks.rev_onto(~B.Octets, cr.octets_of.go(~Blk, ~blk_to, bs, Nil{}), Nil{}))

def cr.iv.pick(~Blk: Data, m: Maybe<&2, Blk>, +n: Nat) -> Result<&2, &2, Cr.CrError, Blk>:
  match m:
    case None{}:
      Fail{Cr.CrBadIvLength{n}}
    case Some{b}:
      Done{b}

# an IV of one block (CrBadIvLength otherwise)
def cr.iv(~Blk: Data, ~blk_of: B.Octets -> Maybe<&2, Blk>, +iv: B.Octets) -> Result<&2, &2, Cr.CrError, Blk>:
  cr.iv.pick(~Blk, blk_of(iv), B.Octets.len(iv))

# ECB and CBC on bytes: a message of whole blocks (no padding)

def CrEcb.encrypt(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.map(&2, &2, Cr.CrError, List<&2, Blk>, B.Octets, bs => CrModes.octets_of(~Blk, ~blk_to, CrEcb.encrypt_blocks(~K, ~Blk, ~enc, k, bs)), CrModes.blocks_of(~Blk, ~bsize, ~blk_of, m))

def CrEcb.decrypt(~K: Data, ~Blk: Data, ~bsize: Nat, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.map(&2, &2, Cr.CrError, List<&2, Blk>, B.Octets, bs => CrModes.octets_of(~Blk, ~blk_to, CrEcb.decrypt_blocks(~K, ~Blk, ~dec, k, bs)), CrModes.blocks_of(~Blk, ~bsize, ~blk_of, c))

def CrCbc.encrypt(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, iv: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  do Result<&2, &2, Cr.CrError, B.Octets>:
    v : Blk <- cr.iv(~Blk, ~blk_of, iv)
    bs : List<&2, Blk> <- CrModes.blocks_of(~Blk, ~bsize, ~blk_of, m)
    return CrModes.octets_of(~Blk, ~blk_to, CrCbc.encrypt_blocks(~K, ~Blk, ~enc, ~bxor, k, v, bs))

def CrCbc.decrypt(~K: Data, ~Blk: Data, ~bsize: Nat, ~dec: K -> Blk -> Blk, ~bxor: Blk -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, iv: B.Octets, c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  do Result<&2, &2, Cr.CrError, B.Octets>:
    v : Blk <- cr.iv(~Blk, ~blk_of, iv)
    bs : List<&2, Blk> <- CrModes.blocks_of(~Blk, ~bsize, ~blk_of, c)
    return CrModes.octets_of(~Blk, ~blk_to, CrCbc.decrypt_blocks(~K, ~Blk, ~dec, ~bxor, k, v, bs))

# CTR (SP 800-38A, 6.5): the keystream is E(T_1) E(T_2) ..., T_1 the IV and
# T_{i+1} = T_i + 1 (the whole block as a big-endian number, mod 2^(8 bsize):
# Appendix B.1's standard incrementing function). It is a keystream
# generator, so St.CrXor makes it a stream cipher, with the stream-cipher
# laws proved for every block cipher (LAWS.bend: ctr_*).

# the state: the key schedule, the next counter block (its bytes), and the
# keystream bytes left over from the last block
type CrCtrState<-K: Data> is Data:
  CrCtrState{key: K, ctr: List<&2, U32>, buf: List<&2, U32>}

def cr.ctr.sum(carry: Bool, +b: U32) -> U32:
  match carry:
    case True{}:
      B.byte(U32.add(b, 1))
    case False{}:
      b

def cr.ctr.carry(carry: Bool, +b: U32) -> Bool:
  match carry:
    case True{}:
      U32.is_eq(b, 255)
    case False{}:
      False{}

# one added to a number given by its bytes, least significant first (rs),
# the result most significant first, onto acc
def cr.ctr.add1(rs: List<&2, U32>, +carry: Bool, acc: List<&2, U32>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      acc
    case Con{+b, t}:
      cr.ctr.add1(t, cr.ctr.carry(carry, b), Con{cr.ctr.sum(carry, b), acc})

# the next counter block
def cr.ctr.inc(xs: List<&2, U32>) -> List<&2, U32>:
  cr.ctr.add1(St.cr.rev_onto(xs, Nil{}), True{}, Nil{})

def cr.ctr.block(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_to: Blk -> B.Octets, m: Maybe<&2, Blk>, +k: K) -> List<&2, U32>:
  match m:
    case None{}:
      Nil{}
    case Some{b}:
      B.Octets.to_list(blk_to(enc(k, b)))

def cr.head(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      h

def cr.tail(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      t

def cr.ctr.next(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, buf: List<&2, U32>, +k: K, +ctr: List<&2, U32>) -> St.CrKsStep<CrCtrState<K>>:
  match buf:
    case Con{b, t}:
      St.CrKsStep{b, CrCtrState{k, ctr, t}}
    case Nil{}:
      +ks = cr.ctr.block(~K, ~Blk, ~enc, ~blk_to, blk_of(B.Octets.of_list(ctr)), k)
      St.CrKsStep{cr.head(ks), CrCtrState{k, cr.ctr.inc(ctr), cr.tail(ks)}}

# The keystream generator: the next keystream byte and the state after it
def CrCtr.next(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, s: CrCtrState<K>) -> St.CrKsStep<CrCtrState<K>>:
  match s:
    case CrCtrState{+k, +ctr, buf}:
      cr.ctr.next(~K, ~Blk, ~enc, ~blk_of, ~blk_to, buf, k, ctr)

def cr.ctr.start(~K: Data, ~bsize: Nat, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, key_o: B.Octets, +iv: List<&2, U32>) -> Result<&2, &2, Cr.CrError, CrCtrState<K>>:
  +n = B.len(iv)
  do Result<&2, &2, Cr.CrError, CrCtrState<K>>:
    Cr.CrError.check(Nat.is_eq(n, bsize), Cr.CrBadIvLength{n})
    k : K <- key(key_o)
    return CrCtrState{k, iv, Nil{}}

# The state for a raw key and an initial counter block of bsize bytes
# (CrBadIvLength for another length)
def CrCtr.start(~K: Data, ~bsize: Nat, ~key: B.Octets -> Result<&2, &2, Cr.CrError, K>, key_o: B.Octets, iv: B.Octets) -> Result<&2, &2, Cr.CrError, CrCtrState<K>>:
  cr.ctr.start(~K, ~bsize, ~key, key_o, B.Octets.to_list(iv))

# The next piece of data, encrypted or decrypted, and the state after it
def CrCtr.update(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, s: CrCtrState<K>, m: B.Octets) -> St.CrXorOut<CrCtrState<K>>:
  St.CrXor.update(~CrCtrState<K>, ~CrCtr.next(~K, ~Blk, ~enc, ~blk_of, ~blk_to), s, m)
