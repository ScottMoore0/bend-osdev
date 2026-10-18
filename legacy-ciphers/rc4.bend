# RC4 (ARC4), the stream cipher, as RFC 6229 ("Test Vectors for the Stream
# Cipher RC4", 2011) describes it: a key-scheduling algorithm that permutes
# the 256-byte state S under a key of 1 to 256 bytes, then an output
# algorithm that yields one keystream byte per step, XORed into the data.
#
# RC4 is broken: RFC 7465 (2015) forbids it in TLS, and its keystream is
# biased. It is here only to read and write data that old formats and
# protocols already hold (for compatibility); never use it to protect new
# data.
#
# The state (S, i, j) is Data: S is a 256-entry table (a tree read and
# written by the bits of an index), so the cipher is a pure function of its
# state and the laws can quantify over states. Data arrives in pieces:
# LcRc4.update takes the state and a piece and answers the next state and
# the piece encrypted (or decrypted: it is the same operation).
import Base
import ../bytes/bytes.bend as B
import ./legacy-ciphers.bend as L

# The table S

# the bits of i (below 2^d) that pick its entry, most significant first
def rc4.path(d: Nat, +i: U32) -> List<&2, Bool>:
  match d:
    case 0n:
      Nil{}
    case 1n+(+p):
      Con{U32.is_eq(L.lc.bit(i, p), 1), rc4.path(p, i)}

def rc4.get(t: L.LcTab, path: List<&2, Bool>) -> U32:
  match t:
    case L.LcLeaf{v}:
      v
    case L.LcNode{l, r}:
      match path:
        case Nil{}:
          0
        case Con{b, rest}:
          match b:
            case True{}:
              rc4.get(r, rest)
            case False{}:
              rc4.get(l, rest)

def rc4.set(t: L.LcTab, path: List<&2, Bool>, v: U32) -> L.LcTab:
  match t:
    case L.LcLeaf{w}:
      L.LcLeaf{v}
    case L.LcNode{l, r}:
      match path:
        case Nil{}:
          L.LcNode{l, r}
        case Con{b, rest}:
          match b:
            case True{}:
              L.LcNode{l, rc4.set(r, rest, v)}
            case False{}:
              L.LcNode{rc4.set(l, rest, v), r}

def rc4.at(+s: L.LcTab, +i: U32) -> U32:
  rc4.get(s, rc4.path(8n, i))

# S with entries i and j exchanged
def rc4.swap(+s: L.LcTab, +i: U32, +j: U32) -> L.LcTab:
  +a = rc4.at(s, i)
  +b = rc4.at(s, j)
  rc4.set(rc4.set(s, rc4.path(8n, i), b), rc4.path(8n, j), a)

# the identity permutation 0 .. 255
def rc4.ident(n: Nat, +i: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{i, rc4.ident(p, U32.add(i, 1))}

# The state (opaque): S, i and j
type LcRc4State is Data:
  LcRc4State{s: L.LcTab, i: U32, j: U32}

# The key-scheduling algorithm: for i = 0 .. 255,
#   j = j + S[i] + key[i mod keylength]; swap S[i] and S[j]
def rc4.ksa(n: Nat, +key: List<&2, U32>, +klen: Nat, +s: L.LcTab, +i: U32, +j: U32) -> L.LcTab:
  match n:
    case 0n:
      s
    case 1n+p:
      +j2 = U32.and(255, U32.add(U32.add(j, rc4.at(s, i)), L.lc.at(key, Nat.mod(U32.to_nat(i), klen))))
      rc4.ksa(p, key, klen, rc4.swap(s, i, j2), U32.add(i, 1), j2)

# One step of the output algorithm: the next state and keystream byte
type LcRc4Step is Data:
  LcRc4Step{st: LcRc4State, k: U32}

#   i = i + 1; j = j + S[i]; swap S[i] and S[j]; the byte S[S[i] + S[j]]
def rc4.next(st: LcRc4State) -> LcRc4Step:
  match st:
    case LcRc4State{+s, i, j}:
      +i2 = U32.and(255, U32.add(i, 1))
      +j2 = U32.and(255, U32.add(j, rc4.at(s, i2)))
      +s2 = rc4.swap(s, i2, j2)
      LcRc4Step{LcRc4State{s2, i2, j2}, rc4.at(s2, U32.and(255, U32.add(rc4.at(s2, i2), rc4.at(s2, j2))))}

def rc4.step.st(r: LcRc4Step) -> LcRc4State:
  match r:
    case LcRc4Step{st, k}:
      st

def rc4.step.k(r: LcRc4Step) -> U32:
  match r:
    case LcRc4Step{st, k}:
      k

# The data, structurally (the form the proofs reason about): each byte XOR
# the next keystream byte, and the state after the bytes

def rc4.xs(xs: List<&2, U32>, st: LcRc4State) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      +n = rc4.next(st)
      Con{B.byte(U32.xor(x, rc4.step.k(n))), rc4.xs(t, rc4.step.st(n))}

def rc4.after(xs: List<&2, U32>, st: LcRc4State) -> LcRc4State:
  match xs:
    case Nil{}:
      st
    case Con{x, t}:
      rc4.after(t, rc4.step.st(rc4.next(st)))

# A piece of data through the cipher: the state after it, and its bytes
# encrypted (or decrypted). Open: a caller may match it.
type LcRc4Out is Data:
  LcRc4Out{state: LcRc4State, data: B.Octets}

# The same, tail-recursive (the output so far kept reversed in acc), so data
# can be of any length: PROOF.bend proves it equal to the structural form

def rc4.rev_onto(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      rc4.rev_onto(t, Con{h, acc})

type LcRc4Run is Data:
  LcRc4Run{st: LcRc4State, out: List<&2, U32>}

def rc4.go(xs: List<&2, U32>, st: LcRc4State, acc: List<&2, U32>) -> LcRc4Run:
  match xs:
    case Nil{}:
      LcRc4Run{st, rc4.rev_onto(acc, Nil{})}
    case Con{x, t}:
      +n = rc4.next(st)
      rc4.go(t, rc4.step.st(n), Con{B.byte(U32.xor(x, rc4.step.k(n))), acc})

def rc4.out(r: LcRc4Run) -> LcRc4Out:
  match r:
    case LcRc4Run{st, out}:
      LcRc4Out{st, B.Octets.of_list(out)}

# drop n keystream bytes
def rc4.drop(n: Nat, st: LcRc4State) -> LcRc4State:
  match n:
    case 0n:
      st
    case 1n+p:
      rc4.drop(p, rc4.step.st(rc4.next(st)))

def rc4.start.pick(ok: Bool, +key: List<&2, U32>, +klen: Nat) -> Result<&2, &2, L.LcError, LcRc4State>:
  match ok:
    case True{}:
      Done{LcRc4State{rc4.ksa(256n, key, klen, L.lc.tab(8n, rc4.ident(256n, 0)), 0, 0), 0, 0}}
    case False{}:
      Fail{L.LcBadKeyLength{klen}}

# The cipher

# the state after the key-scheduling algorithm, for a key of 1 to 256 bytes
def LcRc4.start(key: B.Octets) -> Result<&2, &2, L.LcError, LcRc4State>:
  +xs = B.Octets.to_list(key)
  +n = B.len(xs)
  rc4.start.pick(Bool.and(Nat.is_lt(0n, n), Nat.is_le(n, 256n)), xs, n)

# the state after dropping the first n keystream bytes (RC4-drop[n]; RFC 4345
# drops 1536 for SSH's arcfour128 and arcfour256)
def LcRc4.start_drop(key: B.Octets, n: Nat) -> Result<&2, &2, L.LcError, LcRc4State>:
  Result.map(&2, &2, L.LcError, LcRc4State, LcRc4State, st => rc4.drop(n, st), LcRc4.start(key))

# the next piece of data, encrypted or decrypted, and the state after it
def LcRc4.update(st: LcRc4State, m: B.Octets) -> LcRc4Out:
  rc4.out(rc4.go(B.Octets.to_list(m), st, Nil{}))

def LcRc4.out_state(o: LcRc4Out) -> LcRc4State:
  match o:
    case LcRc4Out{st, d}:
      st

def LcRc4.out_data(o: LcRc4Out) -> B.Octets:
  match o:
    case LcRc4Out{st, d}:
      d

# the data under a key, in one call
def LcRc4.crypt(key: B.Octets, m: B.Octets) -> Result<&2, &2, L.LcError, B.Octets>:
  Result.map(&2, &2, L.LcError, LcRc4State, B.Octets, st => LcRc4.out_data(LcRc4.update(st, m)), LcRc4.start(key))

# the next n keystream bytes (the data n zero bytes), and the state after them
def LcRc4.keystream(st: LcRc4State, n: Nat) -> LcRc4Out:
  LcRc4.update(st, B.Octets.zeros(n))
