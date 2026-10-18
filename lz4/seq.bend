# bend-osdev-lz4, compression: the sequence writer every matcher shares, from
# the LZ4 Block Format Description (lz4_Block_format.md).
#
# A block is a run of sequences: a token (the literal length's nibble, then
# the match length's), the literal length's extra bytes, the literals, a
# two-byte little-endian offset, and the match length's extra bytes. The last
# sequence has literals only. A matcher finds the matches; this file writes
# them. The output is built reversed (most recent byte first), as the
# matchers keep it.
import Base
import ../bytes/bytes.bend as B
import ./block.bend as K

def seq.inc_if(ok: Bool, n: Nat) -> Nat:
  match ok:
    case True{}:
      1n+n
    case False{}:
      n

# how many bytes a and b share from their starts, k at most; live: the bytes
# so far agree
def seq.common(a: List<&2, U32>, live: Bool, b: List<&2, U32>, +k: U32, n: Nat) -> Nat:
  match a live:
    case Con{x, s} True{}:
      match b:
        case Nil{}:
          n
        case Con{y, t}:
          +ok = Bool.and(U32.is_lt(0, k), U32.is_eq(x, y))
          seq.common(s, ok, t, U32.sub(k, 1), seq.inc_if(ok, n))
    case _ _:
      n

# the low nibble of a length: the length itself below 15, else 15
def seq.nib(+n: Nat) -> U32:
  U32.from_nat(Nat.min(n, 15n))

def seq.ext.pick(more: Bool, +n: Nat) -> List<&2, U32>:
  match more:
    case True{}:
      K.lit.ext(Nat.sub(n, 15n), 254n)
    case False{}:
      Nil{}

# the length bytes after a nibble of 15
def seq.ext(+n: Nat) -> List<&2, U32>:
  seq.ext.pick(Nat.is_le(15n, n), n)

# a sequence (literals, then a match at offset off of length ml), pushed onto
# the reversed output
def seq.push(+lits: List<&2, U32>, +off: U32, +ml: Nat, out: List<&2, U32>) -> List<&2, U32>:
  +l = B.len.fast(lits)
  +m = Nat.sub(ml, 4n)
  +tok = U32.or(U32.shln(seq.nib(l), 4n), seq.nib(m))
  K.blk.push(seq.ext(m), Con{U32.shrn(off, 8n), Con{U32.and(off, 255), K.blk.push(lits, K.blk.push(seq.ext(l), Con{tok, out}))}})

# the last sequence: literals only
def seq.last(+lits: List<&2, U32>, out: List<&2, U32>) -> List<&2, U32>:
  +l = B.len.fast(lits)
  K.blk.push(lits, K.blk.push(seq.ext(l), Con{U32.shln(seq.nib(l), 4n), out}))
