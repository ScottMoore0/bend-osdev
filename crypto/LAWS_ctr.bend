# The CTR counter's increment (modes.bend): the counter block moves to its
# value plus one, modulo 2^(8n) for a counter of n bytes (NIST SP 800-38A,
# Appendix B.1's standard incrementing function), for every counter block.
# In a pair of its own (CONVENTIONS.md, Laws), its proof resting on bytes'
# laws only. The stream laws (LAWS.bend: ctr_*) hold whatever the counter
# is; this law fixes what it is.
#
# A counter block's value is its bytes as a big-endian number (crctr.val);
# 2^(8n) is crctr.pw(n), 256 multiplied n times, never a closed constant.
import Base
import ../bytes/bytes.bend as B
import ./stream.bend as St
import ./modes.bend as Md

# the bytes as a number, least significant byte first, and most
# significant first
def crctr.vle(rs: List<&2, U32>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{b, t}:
      Nat.add(U32.to_nat(b), Nat.mul(crctr.vle(t), 256n))

def crctr.val(xs: List<&2, U32>) -> Nat:
  crctr.vle(B.rev(xs))

# 256^n
def crctr.pw(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      Nat.mul(crctr.pw(p), 256n)

# a CTR state's counter block
def crctr.ctr(~K: Data, s: Md.CrCtrState<K>) -> List<&2, U32>:
  match s:
    case Md.CrCtrState{k, c, b}:
      c

# when a state's keystream bytes are used up, the keystream's next step
# moves its counter block (n bytes, from an IV of n bytes) to its value plus
# one modulo 2^(8n), for every block cipher, key and counter block
law ctr_counter_increment:
  for ~K: Data
  for ~Blk: Data
  for ~enc: K -> Blk -> Blk
  for ~blk_of: B.Octets -> Maybe<&2, Blk>
  for ~blk_to: Blk -> B.Octets
  for +k: K
  for +iv: B.Octets
  {crctr.val(crctr.ctr(~K, St.CrKsStep.st(~Md.CrCtrState<K>, Md.CrCtr.next(~K, ~Blk, ~enc, ~blk_of, ~blk_to, Md.CrCtrState{k, B.Octets.to_list(iv), Nil{}})))) == Nat.mod(Nat.add(crctr.val(B.Octets.to_list(iv)), 1n), crctr.pw(B.Octets.len(iv))) : Nat}
