# The stream-cipher interface, and stream ciphers built from a keystream
# generator.
#
# The interface (template arguments, in this order):
#   ~S: Data                                    the state: key, IV and position
#   ~O: Data                                    what one step answers
#   ~start: B.Octets -> B.Octets -> Result<&2, &2, CrError, S>
#                                               the state for a key and an IV
#                                               (a cipher without an IV takes
#                                               the empty one)
#   ~update: S -> B.Octets -> O                 the next piece of data,
#                                               encrypted or decrypted (the
#                                               same thing)
#   ~out_state: O -> S                          the state after the piece
#   ~out_data: O -> B.Octets                    the piece encrypted
# Laws, for every state and all data (README.md, "Laws"):
#   involution       out_data(update(s, out_data(update(s, m)))) == m
#   streaming_data   out_data(update(s, a ++ b)) == out_data(update(s, a)) ++
#                    out_data(update(out_state(update(s, a)), b))
#   streaming_state  out_state(update(s, a ++ b)) ==
#                    out_state(update(out_state(update(s, a)), b))
#
# Keystream generation is the extension point: CrXor turns any function that
# gives the next keystream byte and the next state (~next: S ->
# CrKsStep<S>) into a stream cipher with exactly this interface, and LAWS.bend
# proves its three laws for every such function, once. CTR mode (modes.bend)
# is one; RC4 (inst_rc4.bend) satisfies the interface directly.
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr

# A stream cipher in one call: the data under a key and an IV
def CrStream.crypt(~S: Data, ~O: Data, ~start: B.Octets -> B.Octets -> Result<&2, &2, Cr.CrError, S>, ~update: S -> B.Octets -> O, ~out_data: O -> B.Octets, key: B.Octets, iv: B.Octets, m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.map(&2, &2, Cr.CrError, S, B.Octets, s => out_data(update(s, m)), start(key, iv))

# The next n keystream bytes (the data n zero bytes)
def CrStream.keystream(~S: Data, ~O: Data, ~update: S -> B.Octets -> O, ~out_data: O -> B.Octets, s: S, n: Nat) -> B.Octets:
  out_data(update(s, B.Octets.zeros(n)))

# Keystream generators

# one keystream byte and the state after it
type CrKsStep<-S: Data> is Data:
  CrKsStep{k: U32, st: S}

# what CrXor.update answers: the state after the data, and the data
# encrypted (open type)
type CrXorOut<-S: Data> is Data:
  CrXorOut{state: S, data: B.Octets}

def CrKsStep.k(~S: Data, r: CrKsStep<S>) -> U32:
  match r:
    case CrKsStep{k, st}:
      k

def CrKsStep.st(~S: Data, r: CrKsStep<S>) -> S:
  match r:
    case CrKsStep{k, st}:
      st

# The structural forms the proofs reason about: the data, byte by byte, and
# the state after it
def cr.ks.xs(~S: Data, ~next: S -> CrKsStep<S>, ys: List<&2, U32>, +s: S) -> List<&2, U32>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{B.byte(U32.xor(x, CrKsStep.k(~S, next(s)))), cr.ks.xs(~S, ~next, t, CrKsStep.st(~S, next(s)))}

def cr.ks.after(~S: Data, ~next: S -> CrKsStep<S>, ys: List<&2, U32>, +s: S) -> S:
  match ys:
    case Nil{}:
      s
    case Con{x, t}:
      cr.ks.after(~S, ~next, t, CrKsStep.st(~S, next(s)))

# The loop that runs: tail-recursive, the output kept reversed, each
# keystream byte computed once
type CrKsRun<-S: Data> is Data:
  CrKsRun{st: S, rev: List<&2, U32>}

def cr.rev_onto(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      cr.rev_onto(t, Con{h, acc})

def cr.ks.go(~S: Data, ~next: S -> CrKsStep<S>, ys: List<&2, U32>, +s: S, acc: List<&2, U32>) -> CrKsRun<S>:
  match ys:
    case Nil{}:
      CrKsRun{s, acc}
    case Con{x, t}:
      +r = next(s)
      cr.ks.go(~S, ~next, t, CrKsStep.st(~S, r), Con{B.byte(U32.xor(x, CrKsStep.k(~S, r))), acc})

def cr.ks.out(~S: Data, r: CrKsRun<S>) -> CrXorOut<S>:
  match r:
    case CrKsRun{st, rev}:
      CrXorOut{st, B.Octets.of_list(cr.rev_onto(rev, Nil{}))}

# The stream cipher of a keystream generator: m XORed with the next len(m)
# keystream bytes, and the state after them
def CrXor.update(~S: Data, ~next: S -> CrKsStep<S>, s: S, m: B.Octets) -> CrXorOut<S>:
  cr.ks.out(~S, cr.ks.go(~S, ~next, B.Octets.to_list(m), s, Nil{}))

def CrXor.out_state(~S: Data, o: CrXorOut<S>) -> S:
  match o:
    case CrXorOut{st, d}:
      st

def CrXor.out_data(~S: Data, o: CrXorOut<S>) -> B.Octets:
  match o:
    case CrXorOut{st, d}:
      d
