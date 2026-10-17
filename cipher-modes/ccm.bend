# CCM, counter with CBC-MAC (NIST SP 800-38C; RFC 3610), authenticated
# encryption over any 128-bit block cipher (only its encryption is used; see
# cipher-modes.bend for the template arguments).
#
# Parameters: the tag length M (4, 6, 8, 10, 12, 14 or 16 bytes) and the nonce
# length N (7 to 13 bytes), which fixes the length field L = 15 - N. The
# message must be shorter than 2^(8L) bytes.
#   B_0 = flags || nonce || l(m)    flags = 64*Adata + 8*((M-2)/2) + (L-1)
#   then l(a) encoded and a (if a is not empty), zero-padded to a block, and m,
#   zero-padded: their CBC-MAC (IV 0) is the tag T (its first M bytes).
#   A_i = (L-1) || nonce || i,  S_i = E(A_i):
#   ciphertext = m xor S_1 S_2 ..., then T xor the first M bytes of S_0.
# CCM needs the message length before it starts (it is in B_0), so it has no
# streaming interface.
import Base
import ../bytes/bytes.bend as B
import ./cipher-modes.bend as M

# the low n bytes of v, most significant first (zeros above the 32 bits of v)
def ccm.be(n: Nat, +v: U32) -> List<&2, U32>:
  B.drop(Nat.sub(8n, n), B.append(B.zeros(4n), M.cm.unword(v, Nil{})))

# xs zero-padded to a whole number of blocks
def ccm.pad(+xs: List<&2, U32>) -> List<&2, U32>:
  B.append(xs, B.zeros(Nat.mod(Nat.sub(16n, Nat.mod(B.len(xs), 16n)), 16n)))

# l(a): two bytes below 65280 (2^16 - 2^8), else 0xFF 0xFE and four bytes
def ccm.alen.pick(short: Bool, +v: U32) -> List<&2, U32>:
  match short:
    case True{}:
      ccm.be(2n, v)
    case False{}:
      Con{255, Con{254, ccm.be(4n, v)}}

def ccm.aad.pick(empty: Bool, +a: List<&2, U32>) -> List<&2, U32>:
  match empty:
    case True{}:
      Nil{}
    case False{}:
      +v = U32.from_nat(B.len(a))
      ccm.pad(B.append(ccm.alen.pick(U32.is_lt(v, 65280), v), a))

# CBC-MAC of whole blocks, from x
def ccm.cbcmac(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, x: M.CmBlock) -> M.CmBlock:
  match bs:
    case Nil{}:
      x
    case Con{b, t}:
      ccm.cbcmac(~K, ~enc, k, t, enc(k, M.CmBlock.xor(x, b)))

# the CBC-MAC of B_0, the encoded a and the padded p
def ccm.mac(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +l: Nat, +nonce: List<&2, U32>, +a: List<&2, U32>, +p: List<&2, U32>) -> M.CmBlock:
  +adata = B.len(a)
  +flags = U32.from_nat(Nat.add(Nat.add(Nat.mul(64n, Nat.min(adata, 1n)), Nat.mul(8n, Nat.div(Nat.sub(m, 2n), 2n))), Nat.sub(l, 1n)))
  +input = B.append(Con{flags, B.append(nonce, ccm.be(l, U32.from_nat(B.len(p))))}, B.append(ccm.aad.pick(Nat.is_eq(adata, 0n), a), ccm.pad(p)))
  ccm.cbcmac(~K, ~enc, k, M.cm.split.blocks(M.cm.split(input)), M.CmBlock.zero())

# the tag: the first m bytes of the MAC
def ccm.tag(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +l: Nat, +nonce: List<&2, U32>, +a: List<&2, U32>, +p: List<&2, U32>) -> List<&2, U32>:
  B.take(m, M.cm.bytes_of(ccm.mac(~K, ~enc, k, m, l, nonce, a, p)))

# A_i = A_0 with counter i (i < 2^(8L), so it stays in the counter field)
def ccm.ai(a0: M.CmBlock, i: U32) -> M.CmBlock:
  M.CmBlock.xor(a0, M.CmBlock{0, 0, 0, i})

# CTR on whole blocks: b_j xor S_(i+j)
def ccm.ctrb(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +a0: M.CmBlock, +i: U32) -> List<&2, M.CmBlock>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, rest}:
      Con{M.CmBlock.xor(b, enc(k, ccm.ai(a0, i))), ccm.ctrb(~K, ~enc, k, rest, a0, U32.add(i, 1))}

# CTR from counter 1: the whole blocks, then the tail xor the next S_i
def ccm.xcrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +a0: M.CmBlock, s: M.CmSplit) -> List<&2, U32>:
  match s:
    case M.CmSplit{+bs, tail}:
      M.cm.join_onto(ccm.ctrb(~K, ~enc, k, bs, a0, 1), M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs))))))))

# A_0: (L-1) || nonce || zeros
def ccm.a0(+l: Nat, +nonce: List<&2, U32>) -> M.CmBlock:
  M.cm.block_of(Con{U32.from_nat(Nat.sub(l, 1n)), B.append(nonce, B.zeros(l))})

def ccm.tag_ok(+m: Nat) -> Bool:
  Bool.and(Nat.is_le(4n, m), Bool.and(Nat.is_le(m, 16n), Nat.is_eq(Nat.mod(m, 2n), 0n)))

# the message must be shorter than 2^(8L) bytes: a bound only for L = 2 or 3
# (with L >= 4 every list is shorter)
def ccm.len_ok.three(three: Bool, +n: Nat) -> Bool:
  match three:
    case True{}:
      U32.is_lt(U32.from_nat(n), 16777216)
    case False{}:
      True{}

def ccm.len_ok.two(two: Bool, +l: Nat, +n: Nat) -> Bool:
  match two:
    case True{}:
      U32.is_lt(U32.from_nat(n), 65536)
    case False{}:
      ccm.len_ok.three(Nat.is_eq(l, 3n), n)

def ccm.len_ok(+l: Nat, +n: Nat) -> Bool:
  ccm.len_ok.two(Nat.is_eq(l, 2n), l, n)

def ccm.checks.len(ok: Bool, +n: Nat) -> Result<&2, &2, M.CmError, Unit>:
  match ok:
    case True{}:
      Done{Unit{}}
    case False{}:
      Fail{M.CmTooLong{n}}

def ccm.checks.nonce(ok: Bool, +nl: Nat, +n: Nat) -> Result<&2, &2, M.CmError, Unit>:
  match ok:
    case True{}:
      ccm.checks.len(ccm.len_ok(Nat.sub(15n, nl), n), n)
    case False{}:
      Fail{M.CmBadNonceLength{nl}}

def ccm.checks.tag(ok: Bool, +m: Nat, +nl: Nat, +n: Nat) -> Result<&2, &2, M.CmError, Unit>:
  match ok:
    case True{}:
      ccm.checks.nonce(Bool.and(Nat.is_le(7n, nl), Nat.is_le(nl, 13n)), nl, n)
    case False{}:
      Fail{M.CmBadTagLength{m}}

# the tag length, the nonce length and the message length n, in that order
def ccm.checks(+m: Nat, +nl: Nat, +n: Nat) -> Result<&2, &2, M.CmError, Unit>:
  ccm.checks.tag(ccm.tag_ok(m), m, nl, n)

# the ciphertext of pv, then the tag
def ccm.ebody(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +pv: List<&2, U32>) -> List<&2, U32>:
  +l = Nat.sub(15n, B.len(nv))
  +a0 = ccm.a0(l, nv)
  B.append(ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(pv)), M.cm.xor_bytes(ccm.tag(~K, ~enc, k, m, l, nv, av, pv), M.cm.bytes_of(enc(k, a0))))

def ccm.e2(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +pv: List<&2, U32>, r: Result<&2, &2, M.CmError, Unit>) -> Result<&2, &2, M.CmError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      Done{B.Octets.of_list(ccm.ebody(~K, ~enc, k, m, nv, av, pv))}

# p with associated data aad under the nonce: the ciphertext, then the m-byte tag
def Ccm.encrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, nonce: B.Octets, aad: B.Octets, p: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  +nv = B.Octets.to_list(nonce)
  +pv = B.Octets.to_list(p)
  ccm.e2(~K, ~enc, k, m, nv, B.Octets.to_list(aad), pv, ccm.checks(m, B.len(nv), B.len(pv)))

def ccm.open(ok: Bool, p: List<&2, U32>) -> Result<&2, &2, M.CmError, B.Octets>:
  match ok:
    case True{}:
      Done{B.Octets.of_list(p)}
    case False{}:
      Fail{M.CmTagMismatch{}}

# the plaintext, if the tag (compared with no early exit) matches
def ccm.dbody(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +cv: List<&2, U32>) -> Result<&2, &2, M.CmError, B.Octets>:
  +body = Nat.sub(B.len(cv), m)
  +l = Nat.sub(15n, B.len(nv))
  +a0 = ccm.a0(l, nv)
  +pv = ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(B.take(body, cv)))
  ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(body, cv), M.cm.bytes_of(enc(k, a0))), ccm.tag(~K, ~enc, k, m, l, nv, av, pv)), pv)

def ccm.d3(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +cv: List<&2, U32>, r: Result<&2, &2, M.CmError, Unit>) -> Result<&2, &2, M.CmError, B.Octets>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{u}:
      ccm.dbody(~K, ~enc, k, m, nv, av, cv)

def ccm.d2(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ok: Bool, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +cv: List<&2, U32>) -> Result<&2, &2, M.CmError, B.Octets>:
  match ok:
    case False{}:
      Fail{M.CmTooShort{B.len(cv)}}
    case True{}:
      ccm.d3(~K, ~enc, k, m, nv, av, cv, ccm.checks(m, B.len(nv), Nat.sub(B.len(cv), m)))

# the plaintext of c (the ciphertext, then the m-byte tag), or CmTagMismatch
# when the tag does not match; no plaintext is released from a message that
# fails
def Ccm.decrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, nonce: B.Octets, aad: B.Octets, c: B.Octets) -> Result<&2, &2, M.CmError, B.Octets>:
  +cv = B.Octets.to_list(c)
  ccm.d2(~K, ~enc, Nat.is_le(m, B.len(cv)), k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), cv)
