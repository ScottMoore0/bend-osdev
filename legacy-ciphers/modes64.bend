# Modes of operation for 64-bit block ciphers (DES, 3DES): ECB and CBC
# (NIST SP 800-38A, sections 6.1 and 6.2), over any cipher on LcBlock64.
#
# cipher-modes' modes are written for 128-bit blocks (CmBlock), so a 64-bit
# cipher cannot use them; these are the same modes on LcBlock64, with the
# cipher as template arguments in cipher-modes' style:
#   ~K: Data                                  the cipher's (expanded) key
#   ~enc: K -> LcBlock64 -> LcBlock64         encrypt one block
#   ~dec: K -> LcBlock64 -> LcBlock64         decrypt one block
# for instance ~D.LcDesKey, ~D.LcDes.encrypt, ~D.LcDes.decrypt. For padding,
# cipher-modes' Pkcs7.pad(8n, m) and Pkcs7.unpad(8n, m) take any block size.
#
# The block layer works on lists of blocks: chaining one call's last
# ciphertext block into the next call's IV encrypts a long message in pieces.
# The byte layer takes Octets of whole blocks.
import Base
import ../bytes/bytes.bend as B
import ./legacy-ciphers.bend as L

# Block lists, structurally (the forms the proofs reason about)

def m64.ecb(~K: Data, ~f: K -> L.LcBlock64 -> L.LcBlock64, +k: K, bs: List<&2, L.LcBlock64>) -> List<&2, L.LcBlock64>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{f(k, b), m64.ecb(~K, ~f, k, t)}

# C_1 = E(P_1 xor IV), C_j = E(P_j xor C_(j-1))
def m64.cbc.enc(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, +k: K, bs: List<&2, L.LcBlock64>, iv: L.LcBlock64) -> List<&2, L.LcBlock64>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      +c = enc(k, L.LcBlock64.xor(iv, p))
      Con{c, m64.cbc.enc(~K, ~enc, k, t, c)}

# P_1 = D(C_1) xor IV, P_j = D(C_j) xor C_(j-1)
def m64.cbc.dec(~K: Data, ~dec: K -> L.LcBlock64 -> L.LcBlock64, +k: K, bs: List<&2, L.LcBlock64>, iv: L.LcBlock64) -> List<&2, L.LcBlock64>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{+c, t}:
      Con{L.LcBlock64.xor(iv, dec(k, c)), m64.cbc.dec(~K, ~dec, k, t, c)}

# The same, tail-recursive (the output so far kept reversed in acc), so a
# message can be of any length: PROOF.bend proves each equal to its
# structural form for every input

def m64.rev_onto(bs: List<&2, L.LcBlock64>, acc: List<&2, L.LcBlock64>) -> List<&2, L.LcBlock64>:
  match bs:
    case Nil{}:
      acc
    case Con{b, t}:
      m64.rev_onto(t, Con{b, acc})

def m64.ecb.go(~K: Data, ~f: K -> L.LcBlock64 -> L.LcBlock64, +k: K, bs: List<&2, L.LcBlock64>, acc: List<&2, L.LcBlock64>) -> List<&2, L.LcBlock64>:
  match bs:
    case Nil{}:
      m64.rev_onto(acc, Nil{})
    case Con{b, t}:
      m64.ecb.go(~K, ~f, k, t, Con{f(k, b), acc})

def m64.cbc.enc.go(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, +k: K, bs: List<&2, L.LcBlock64>, iv: L.LcBlock64, acc: List<&2, L.LcBlock64>) -> List<&2, L.LcBlock64>:
  match bs:
    case Nil{}:
      m64.rev_onto(acc, Nil{})
    case Con{p, t}:
      +c = enc(k, L.LcBlock64.xor(iv, p))
      m64.cbc.enc.go(~K, ~enc, k, t, c, Con{c, acc})

def m64.cbc.dec.go(~K: Data, ~dec: K -> L.LcBlock64 -> L.LcBlock64, +k: K, bs: List<&2, L.LcBlock64>, iv: L.LcBlock64, acc: List<&2, L.LcBlock64>) -> List<&2, L.LcBlock64>:
  match bs:
    case Nil{}:
      m64.rev_onto(acc, Nil{})
    case Con{+c, t}:
      m64.cbc.dec.go(~K, ~dec, k, t, c, Con{L.LcBlock64.xor(iv, dec(k, c)), acc})

# The block layer

def Lc64.ecb_encrypt_blocks(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, +k: K, bs: List<&2, L.LcBlock64>) -> List<&2, L.LcBlock64>:
  m64.ecb.go(~K, ~enc, k, bs, Nil{})

def Lc64.ecb_decrypt_blocks(~K: Data, ~dec: K -> L.LcBlock64 -> L.LcBlock64, +k: K, bs: List<&2, L.LcBlock64>) -> List<&2, L.LcBlock64>:
  m64.ecb.go(~K, ~dec, k, bs, Nil{})

def Lc64.cbc_encrypt_blocks(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, +k: K, iv: L.LcBlock64, bs: List<&2, L.LcBlock64>) -> List<&2, L.LcBlock64>:
  m64.cbc.enc.go(~K, ~enc, k, bs, iv, Nil{})

def Lc64.cbc_decrypt_blocks(~K: Data, ~dec: K -> L.LcBlock64 -> L.LcBlock64, +k: K, iv: L.LcBlock64, bs: List<&2, L.LcBlock64>) -> List<&2, L.LcBlock64>:
  m64.cbc.dec.go(~K, ~dec, k, bs, iv, Nil{})

# The byte layer

# the bytes as whole blocks (reversed onto acc), or None if bytes are left over
def m64.split(xs: List<&2, U32>, acc: List<&2, L.LcBlock64>) -> Maybe<&2, List<&2, L.LcBlock64>>:
  match xs:
    case Nil{}:
      Some{m64.rev_onto(acc, Nil{})}
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, t}}}}}}}}:
      m64.split(t, Con{L.lc.block8(a0, a1, a2, a3, a4, a5, a6, a7), acc})
    case _:
      None{}

# the bytes of the blocks (reversed) in front of acc
def m64.join(rs: List<&2, L.LcBlock64>, acc: List<&2, U32>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      acc
    case Con{b, t}:
      m64.join(t, L.lc.block_bytes(b, acc))

def m64.octets(bs: List<&2, L.LcBlock64>) -> B.Octets:
  B.Octets.of_list(m64.join(m64.rev_onto(bs, Nil{}), Nil{}))

def m64.blocks(+n: Nat, m: Maybe<&2, List<&2, L.LcBlock64>>) -> Result<&2, &2, L.LcError, List<&2, L.LcBlock64>>:
  match m:
    case None{}:
      Fail{L.LcNotBlockMultiple{n}}
    case Some{bs}:
      Done{bs}

# the message as whole blocks, or LcNotBlockMultiple
def Lc64.blocks_of(+o: B.Octets) -> Result<&2, &2, L.LcError, List<&2, L.LcBlock64>>:
  m64.blocks(B.Octets.len(o), m64.split(B.Octets.to_list(o), Nil{}))

# the blocks' bytes, in order
def Lc64.octets_of(bs: List<&2, L.LcBlock64>) -> B.Octets:
  m64.octets(bs)

def m64.iv(m: Maybe<&2, L.LcBlock64>, +n: Nat) -> Result<&2, &2, L.LcError, L.LcBlock64>:
  match m:
    case None{}:
      Fail{L.LcBadIvLength{n}}
    case Some{b}:
      Done{b}

def Lc64.ecb_encrypt(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, +k: K, m: B.Octets) -> Result<&2, &2, L.LcError, B.Octets>:
  Result.map(&2, &2, L.LcError, List<&2, L.LcBlock64>, B.Octets, bs => Lc64.octets_of(Lc64.ecb_encrypt_blocks(~K, ~enc, k, bs)), Lc64.blocks_of(m))

def Lc64.ecb_decrypt(~K: Data, ~dec: K -> L.LcBlock64 -> L.LcBlock64, +k: K, c: B.Octets) -> Result<&2, &2, L.LcError, B.Octets>:
  Result.map(&2, &2, L.LcError, List<&2, L.LcBlock64>, B.Octets, bs => Lc64.octets_of(Lc64.ecb_decrypt_blocks(~K, ~dec, k, bs)), Lc64.blocks_of(c))

def m64.cbc.e2(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, +k: K, v: L.LcBlock64, r: Result<&2, &2, L.LcError, List<&2, L.LcBlock64>>) -> Result<&2, &2, L.LcError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{bs}:
      Done{Lc64.octets_of(Lc64.cbc_encrypt_blocks(~K, ~enc, k, v, bs))}

def m64.cbc.e1(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, +k: K, r: Result<&2, &2, L.LcError, L.LcBlock64>, +m: B.Octets) -> Result<&2, &2, L.LcError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{v}:
      m64.cbc.e2(~K, ~enc, k, v, Lc64.blocks_of(m))

def m64.cbc.d2(~K: Data, ~dec: K -> L.LcBlock64 -> L.LcBlock64, +k: K, v: L.LcBlock64, r: Result<&2, &2, L.LcError, List<&2, L.LcBlock64>>) -> Result<&2, &2, L.LcError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{bs}:
      Done{Lc64.octets_of(Lc64.cbc_decrypt_blocks(~K, ~dec, k, v, bs))}

def m64.cbc.d1(~K: Data, ~dec: K -> L.LcBlock64 -> L.LcBlock64, +k: K, r: Result<&2, &2, L.LcError, L.LcBlock64>, +c: B.Octets) -> Result<&2, &2, L.LcError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{v}:
      m64.cbc.d2(~K, ~dec, k, v, Lc64.blocks_of(c))

# m (whole blocks) under the 8-byte iv
def Lc64.cbc_encrypt(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, +k: K, +iv: B.Octets, +m: B.Octets) -> Result<&2, &2, L.LcError, B.Octets>:
  m64.cbc.e1(~K, ~enc, k, m64.iv(L.LcBlock64.of_octets(iv), B.Octets.len(iv)), m)

def Lc64.cbc_decrypt(~K: Data, ~dec: K -> L.LcBlock64 -> L.LcBlock64, +k: K, +iv: B.Octets, +c: B.Octets) -> Result<&2, &2, L.LcError, B.Octets>:
  m64.cbc.d1(~K, ~dec, k, m64.iv(L.LcBlock64.of_octets(iv), B.Octets.len(iv)), c)
