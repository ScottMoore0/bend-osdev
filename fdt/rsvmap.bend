# bend-osdev-fdt, rsvmap.bend: the memory reservation block (Devicetree
# Specification v0.4, section 5.3): a list of regions the client must not
# use, each a 64-bit address and a 64-bit size, big-endian, ending with an
# entry whose address and size are both 0. The block is 8-aligned.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E

type FdtRsv is Data:
  FdtRsv{address: W.W64, size: W.W64}

# the terminating entry: address and size both 0
def FdtRsv.is_end(r: FdtRsv) -> Bool:
  match r:
    case FdtRsv{address, size}:
      Bool.and(W.W64.is_zero(address), W.W64.is_zero(size))

# Writing

def rsv.entry(r: FdtRsv) -> List<&2, U32>:
  match r:
    case FdtRsv{address, size}:
      B.append(B.be64(address), B.be64(size))

# the entries, then the terminator
def rsv.list(rs: List<&2, FdtRsv>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      B.zeros(16n)
    case Con{r, t}:
      B.append(rsv.entry(r), rsv.list(t))

# the block: the entries, then the 0, 0 entry
def FdtRsv.encode(rs: List<&2, FdtRsv>) -> B.Octets:
  B.Octets.of_list(rsv.list(rs))

# Reading

def rsv.w64(m: Maybe<&2, W.W64>) -> W.W64:
  match m:
    case Some{v}:
      v
    case None{}:
      W.W64.zero()

def rsv.of16(a0: U32, a1: U32, a2: U32, a3: U32, a4: U32, a5: U32, a6: U32, a7: U32, a8: U32, a9: U32, a10: U32, a11: U32, a12: U32, a13: U32, a14: U32, a15: U32) -> FdtRsv:
  FdtRsv{rsv.w64(B.be64_at([a0, a1, a2, a3, a4, a5, a6, a7], 0n)), rsv.w64(B.be64_at([a8, a9, a10, a11, a12, a13, a14, a15], 0n))}

def rsv.push(stop: Bool, r: FdtRsv, acc: List<&2, FdtRsv>) -> List<&2, FdtRsv>:
  match stop:
    case True{}:
      acc
    case False{}:
      Con{r, acc}

# stop: the previous entry was the terminator; acc: the entries so far,
# reversed
def rsv.go(xs: List<&2, U32>, stop: Bool, acc: List<&2, FdtRsv>) -> Result<&2, &2, E.FdtError, List<&2, FdtRsv>>:
  match xs stop:
    case _ True{}:
      Done{List.reverse(&2, FdtRsv, acc)}
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, t}}}}}}}}}}}}}}}} False{}:
      +r = rsv.of16(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15)
      +z = FdtRsv.is_end(r)
      rsv.go(t, z, rsv.push(z, r, acc))
    case _ False{}:
      Fail{E.FdtRsvUnterminated{}}

# the entries before the terminator, from the start of the block (bytes after
# the terminator are not read)
def rsv.read(xs: List<&2, U32>) -> Result<&2, &2, E.FdtError, List<&2, FdtRsv>>:
  rsv.go(xs, False{}, Nil{})

def FdtRsv.decode(o: B.Octets) -> Result<&2, &2, E.FdtError, List<&2, FdtRsv>>:
  rsv.read(B.Octets.to_list(o))

# no entry is the terminator, so a list of them encodes and decodes as itself
def FdtRsv.valid_all(rs: List<&2, FdtRsv>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      Bool.and(Bool.not(FdtRsv.is_end(r)), FdtRsv.valid_all(t))
