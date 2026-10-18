# CBC, cipher block chaining (NIST SP 800-38A, section 6.2), over any 128-bit
# block cipher (see cipher-modes.bend for the template arguments):
#   C_1 = E(P_1 xor IV),  C_j = E(P_j xor C_(j-1))
#   P_1 = D(C_1) xor IV,  P_j = D(C_j) xor C_(j-1)
# The block layer (encrypt_blocks, decrypt_blocks) works on lists of blocks;
# chaining one call's last ciphertext block into the next call's IV encrypts a
# long message in pieces. The byte layer takes Octets: a whole number of
# blocks, or any length with PKCS #7 padding (pkcs7.bend).
import Base
import ../bytes/bytes.bend as B
import ./cipher-modes.bend as M
import ./pkcs7.bend as P

# The block layer

def cbc.enc(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, iv: M.CmBlock) -> List<&2, M.CmBlock>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      +c = enc(k, M.CmBlock.xor(iv, p))
      Con{c, cbc.enc(~K, ~enc, k, t, c)}

def cbc.dec(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, iv: M.CmBlock) -> List<&2, M.CmBlock>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      Con{M.CmBlock.xor(iv, dec(k, c)), cbc.dec(~K, ~dec, k, t, c)}

# The same, tail-recursive (the ciphertext so far kept reversed in acc), so a
# message can be of any length: PROOF.bend proves each equal to its structural
# form above for every input

def cbc.enc.go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, iv: M.CmBlock, acc: List<&2, M.CmBlock>) -> List<&2, M.CmBlock>:
  match bs:
    case Nil{}:
      M.cm.blocks.rev_onto(acc, Nil{})
    case Con{p, t}:
      +c = enc(k, M.CmBlock.xor(iv, p))
      cbc.enc.go(~K, ~enc, k, t, c, Con{c, acc})

def cbc.enc.fast(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, iv: M.CmBlock) -> List<&2, M.CmBlock>:
  cbc.enc.go(~K, ~enc, k, bs, iv, Nil{})

def cbc.dec.go(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, iv: M.CmBlock, acc: List<&2, M.CmBlock>) -> List<&2, M.CmBlock>:
  match bs:
    case Nil{}:
      M.cm.blocks.rev_onto(acc, Nil{})
    case Con{+c, t}:
      cbc.dec.go(~K, ~dec, k, t, c, Con{M.CmBlock.xor(iv, dec(k, c)), acc})

def cbc.dec.fast(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, iv: M.CmBlock) -> List<&2, M.CmBlock>:
  cbc.dec.go(~K, ~dec, k, bs, iv, Nil{})

def Cbc.encrypt_blocks(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, iv: M.CmBlock, bs: List<&2, M.CmBlock>) -> List<&2, M.CmBlock>:
  cbc.enc.fast(~K, ~enc, k, bs, iv)

def Cbc.decrypt_blocks(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, iv: M.CmBlock, bs: List<&2, M.CmBlock>) -> List<&2, M.CmBlock>:
  cbc.dec.fast(~K, ~dec, k, bs, iv)

# The byte layer

def cbc.iv(o: B.Octets) -> Result<&2, &2, M.CmError, M.CmBlock>:
  +xs = B.Octets.to_list(o)
  M.cm.need_block(xs, M.CmBadIvLength{B.len(xs)})

# the whole blocks under v, or CmNotBlockMultiple(n) if bytes are left over
def cbc.e2(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, v: M.CmBlock, s: M.CmSplit, +n: Nat) -> Result<&2, &2, M.CmError, B.Octets>:
  match s:
    case M.CmSplit{bs, tail}:
      match tail:
        case Nil{}:
          Done{B.Octets.of_list(M.cm.join(cbc.enc(~K, ~enc, k, bs, v)))}
        case Con{h, t}:
          Fail{M.CmNotBlockMultiple{n}}

def cbc.e1(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +xs: List<&2, U32>) -> Result<&2, &2, M.CmError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{v}:
      cbc.e2(~K, ~enc, k, v, M.cm.split(xs), B.len(xs))

def cbc.d2(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, v: M.CmBlock, s: M.CmSplit, +n: Nat) -> Result<&2, &2, M.CmError, B.Octets>:
  match s:
    case M.CmSplit{bs, tail}:
      match tail:
        case Nil{}:
          Done{B.Octets.of_list(M.cm.join(cbc.dec(~K, ~dec, k, bs, v)))}
        case Con{h, t}:
          Fail{M.CmNotBlockMultiple{n}}

def cbc.d1(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +xs: List<&2, U32>) -> Result<&2, &2, M.CmError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{v}:
      cbc.d2(~K, ~dec, k, v, M.cm.split(xs), B.len(xs))

# m (a whole number of blocks) under the 16-byte iv
# The byte layer, tail-recursive: what Cbc.encrypt and Cbc.decrypt run
# (cbc.e1 .. cbc.d2 are the structural forms; PROOF.bend: cbcp.e1_eq, d1_eq)

def cbc.e2.fast(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, v: M.CmBlock, s: M.CmSplit, +n: Nat) -> Result<&2, &2, M.CmError, B.Octets>:
  match s:
    case M.CmSplit{bs, tail}:
      match tail:
        case Nil{}:
          Done{B.Octets.of_list(M.cm.join_onto.fast(cbc.enc.fast(~K, ~enc, k, bs, v), Nil{}))}
        case Con{h, t}:
          Fail{M.CmNotBlockMultiple{n}}

def cbc.e1.fast(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +xs: List<&2, U32>) -> Result<&2, &2, M.CmError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{v}:
      cbc.e2.fast(~K, ~enc, k, v, M.cm.split.fast(xs), B.len.fast(xs))

def cbc.d2.fast(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, v: M.CmBlock, s: M.CmSplit, +n: Nat) -> Result<&2, &2, M.CmError, B.Octets>:
  match s:
    case M.CmSplit{bs, tail}:
      match tail:
        case Nil{}:
          Done{B.Octets.of_list(M.cm.join_onto.fast(cbc.dec.fast(~K, ~dec, k, bs, v), Nil{}))}
        case Con{h, t}:
          Fail{M.CmNotBlockMultiple{n}}

def cbc.d1.fast(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, r: Result<&2, &2, M.CmError, M.CmBlock>, +xs: List<&2, U32>) -> Result<&2, &2, M.CmError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{v}:
      cbc.d2.fast(~K, ~dec, k, v, M.cm.split.fast(xs), B.len.fast(xs))

# Cbc.encrypt and Cbc.decrypt through the structural forms (the laws' proofs
# reason about these; PROOF.bend proves them equal to the public defs)
def Cbc.encrypt.ref(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, iv: B.Octets, m: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  cbc.e1(~K, ~enc, k, cbc.iv(iv), B.Octets.to_list(m))

def Cbc.decrypt.ref(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, iv: B.Octets, c: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  cbc.d1(~K, ~dec, k, cbc.iv(iv), B.Octets.to_list(c))

def Cbc.encrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, iv: B.Octets, m: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  cbc.e1.fast(~K, ~enc, k, cbc.iv(iv), B.Octets.to_list(m))

def Cbc.decrypt(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, iv: B.Octets, c: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  cbc.d1.fast(~K, ~dec, k, cbc.iv(iv), B.Octets.to_list(c))

# m of any length, PKCS #7 padded to whole blocks, then encrypted
def Cbc.encrypt_padded(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, iv: B.Octets, m: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  do Result<&2, &2, M.CmError, B.Octets>:
    padded : B.Octets <- P.Pkcs7.pad(16n, m)
    Cbc.encrypt(~K, ~enc, k, iv, padded)

# decrypted, then the padding checked and removed (CmBadPadding)
def Cbc.decrypt_padded(~K: Data, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, iv: B.Octets, +c: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  +n = B.Octets.len(c)
  do Result<&2, &2, M.CmError, B.Octets>:
    M.cm.check(Nat.is_lt(0n, n), M.CmTooShort{n})
    padded : B.Octets <- Cbc.decrypt(~K, ~dec, k, iv, c)
    P.Pkcs7.unpad(16n, padded)
