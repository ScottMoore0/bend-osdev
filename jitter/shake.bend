# SHAKE256 (FIPS 202, section 6.2) as an extendable-output function (XOF),
# the XOF of jitter's XDRBG conditioner (xdrbg.bend). crypto has a hash
# interface but no XOF interface, so the adapter lives here, as crypto's
# inst_sha3.bend adapts SHA3-256.
#
# The Keccak-f[1600] permutation and the absorbing are
# bend-collections-laws-crypto@1.0.0.0's (src/crypto: keccak/permutation.bend,
# proved equal to FIPS 202's permutation in that package's
# proofs/crypto/keccak/; sha3/core.bend's lanes and absorbing; hash.bend's
# streaming absorb, step3, which buffers an unfinished block). SHAKE256 has
# SHA3-256's capacity of 512 bits, so the same rate of 136 bytes; it differs
# in the padding (FIPS 202, B.2: the suffix 1111, so the first padding byte
# is 0x1F, and the last 0x80; 0x9F when one byte is left) and in squeezing
# as many bytes as are asked for, 136 per permutation.
#
# The XOF interface (template arguments, in this order):
#   ~X: Data                              the state
#   ~xinit: X                             the state before any byte
#   ~xupdate: X -> B.Octets -> X          the state after more bytes
#   ~xread: X -> Nat -> Nat -> B.Octets   xread(s, i, n): the n bytes at
#                                         offset i of the output for the
#                                         bytes so far
# The SHAKE256 instance:
#   ~JitShakeState, ~JitShake.init(), ~JitShake.update, ~JitShake.read
import Base
import ../bytes/bytes.bend as B
import bend-collections-laws-crypto@1.0.0.0/src/crypto/hash.bend as Hc
import bend-collections-laws-crypto@1.0.0.0/src/crypto/sha3/core.bend as C3
import bend-collections-laws-crypto@1.0.0.0/src/crypto/keccak/types.bend as TK
import bend-collections-laws-crypto@1.0.0.0/src/crypto/keccak/permutation.bend as P

# A SHAKE256 state (opaque): the Keccak state and the bytes of the
# unfinished block
type JitShakeState is Data:
  JitShakeState{st: Hc.Sha3State}

def JitShake.init() -> JitShakeState:
  JitShakeState{Hc.St3{C3.zero(), Nil{}}}

# the state after more bytes
def JitShake.update(s: JitShakeState, o: B.Octets) -> JitShakeState:
  match s:
    case JitShakeState{st}:
      JitShakeState{Hc.step3(st, B.Octets.to_list(o), 24n)}

# the padding of a block with q bytes left: 0x1F, zeros, 0x80 (0x9F alone)
def jit.shake.tail(q: Nat) -> List<&2, U32>:
  match q:
    case 0n:
      Nil{}
    case 1n:
      [159]
    case 2n+k:
      Con{31, B.append(B.zeros(k), [128])}

# the Keccak state once the bytes so far are padded and absorbed
def jit.shake.final(st: Hc.Sha3State) -> TK.State:
  match st:
    case Hc.St3{s, +buf}:
      C3.absorb(C3.lanes(B.append(buf, jit.shake.tail(Nat.sub(136n, B.len(buf))))), 24n, s)

def jit.shake.le(+x: U32, t: List<&2, U32>) -> List<&2, U32>:
  C3.le_bytes(x, t)

# the 136 output bytes of a Keccak state: lanes 0 to 16, little-endian
def jit.shake.block(s: TK.State) -> List<&2, U32>:
  match s:
    case TK.S{TK.W{l0, h0}, TK.W{l1, h1}, TK.W{l2, h2}, TK.W{l3, h3}, TK.W{l4, h4}, TK.W{l5, h5}, TK.W{l6, h6}, TK.W{l7, h7}, TK.W{l8, h8}, TK.W{l9, h9}, TK.W{l10, h10}, TK.W{l11, h11}, TK.W{l12, h12}, TK.W{l13, h13}, TK.W{l14, h14}, TK.W{l15, h15}, TK.W{l16, h16}, a17, a18, a19, a20, a21, a22, a23, a24}:
      jit.shake.le(l0, jit.shake.le(h0, jit.shake.le(l1, jit.shake.le(h1, jit.shake.le(l2, jit.shake.le(h2, jit.shake.le(l3, jit.shake.le(h3, jit.shake.le(l4, jit.shake.le(h4, jit.shake.le(l5, jit.shake.le(h5, jit.shake.le(l6, jit.shake.le(h6, jit.shake.le(l7, jit.shake.le(h7, jit.shake.le(l8, jit.shake.le(h8, jit.shake.le(l9, jit.shake.le(h9, jit.shake.le(l10, jit.shake.le(h10, jit.shake.le(l11, jit.shake.le(h11, jit.shake.le(l12, jit.shake.le(h12, jit.shake.le(l13, jit.shake.le(h13, jit.shake.le(l14, jit.shake.le(h14, jit.shake.le(l15, jit.shake.le(h15, jit.shake.le(l16, jit.shake.le(h16, Nil{}))))))))))))))))))))))))))))))))))

# the first byte of a block, and the rest (a block is never empty)
def jit.shake.hd(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{x, t}:
      x

def jit.shake.tl(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

# n output bytes: buf, the rest of the block squeezed from s, then the
# blocks of s permuted again and again
def jit.shake.sq(n: Nat, buf: List<&2, U32>, s: TK.State) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      match buf:
        case Con{x, t}:
          Con{x, jit.shake.sq(m, t, s)}
        case Nil{}:
          +s2 = P.permute(s)
          +b2 = jit.shake.block(s2)
          Con{jit.shake.hd(b2), jit.shake.sq(m, jit.shake.tl(b2), s2)}

# where the output stands: the rest of the current block, and its state
type JitShakeOut is Data:
  JitShakeOut{buf: List<&2, U32>, s: TK.State}

# the output after i bytes are skipped
def jit.shake.skip(i: Nat, buf: List<&2, U32>, s: TK.State) -> JitShakeOut:
  match i:
    case 0n:
      JitShakeOut{buf, s}
    case 1n+m:
      match buf:
        case Con{x, t}:
          jit.shake.skip(m, t, s)
        case Nil{}:
          +s2 = P.permute(s)
          jit.shake.skip(m, jit.shake.tl(jit.shake.block(s2)), s2)

def jit.shake.skip_o(i: Nat, o: JitShakeOut) -> JitShakeOut:
  match o:
    case JitShakeOut{buf, s}:
      jit.shake.skip(i, buf, s)

def jit.shake.sq_o(n: Nat, o: JitShakeOut) -> List<&2, U32>:
  match o:
    case JitShakeOut{buf, s}:
      jit.shake.sq(n, buf, s)

# the output from its start
def jit.shake.out(st: Hc.Sha3State) -> JitShakeOut:
  +f = jit.shake.final(st)
  JitShakeOut{jit.shake.block(f), f}

# the n bytes at offset i of the output for the bytes so far
def JitShake.read(s: JitShakeState, i: Nat, n: Nat) -> B.Octets:
  match s:
    case JitShakeState{st}:
      B.Octets.of_list(jit.shake.sq_o(n, jit.shake.skip_o(i, jit.shake.out(st))))

# SHAKE256(m, 8n): the first n bytes for the message m
def JitShake.shake256(m: B.Octets, n: Nat) -> B.Octets:
  JitShake.read(JitShake.update(JitShake.init(), m), 0n, n)
