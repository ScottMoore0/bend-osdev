# bend-osdev-fdt, props.bend: typed property values (Devicetree
# Specification v0.4, section 2.2.4): decoders and encoders for <u32>,
# <u64>, <string>, <stringlist>, <prop-encoded-array> cells, and the reg
# property's (address, size) pairs. All big-endian.
#
# Each decoder answers Result, with FdtBadLength, FdtBadString or
# FdtBadCells when the value does not have its type's shape.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./layout.bend as L

# <u32>

def pr.must32(m: Maybe<&2, U32>) -> Result<&2, &2, E.FdtError, U32>:
  match m:
    case Some{v}:
      Done{v}
    case None{}:
      Fail{E.FdtBadLength{}}

def pr.u32.pick(ok: Bool, o: B.Octets) -> Result<&2, &2, E.FdtError, U32>:
  match ok:
    case True{}:
      pr.must32(B.Octets.be32_at(o, 0n))
    case False{}:
      Fail{E.FdtBadLength{}}

# a value of exactly four bytes, as a big-endian 32-bit number
def FdtProp.u32(+o: B.Octets) -> Result<&2, &2, E.FdtError, U32>:
  pr.u32.pick(Nat.is_eq(B.Octets.len(o), 4n), o)

def FdtProp.of_u32(v: U32) -> B.Octets:
  B.Octets.be32(v)

# <u64>

def pr.must64(m: Maybe<&2, W.W64>) -> Result<&2, &2, E.FdtError, W.W64>:
  match m:
    case Some{v}:
      Done{v}
    case None{}:
      Fail{E.FdtBadLength{}}

def pr.u64.pick(ok: Bool, o: B.Octets) -> Result<&2, &2, E.FdtError, W.W64>:
  match ok:
    case True{}:
      pr.must64(B.Octets.be64_at(o, 0n))
    case False{}:
      Fail{E.FdtBadLength{}}

# a value of exactly eight bytes, as a big-endian 64-bit number
def FdtProp.u64(+o: B.Octets) -> Result<&2, &2, E.FdtError, W.W64>:
  pr.u64.pick(Nat.is_eq(B.Octets.len(o), 8n), o)

def FdtProp.of_u64(v: W.W64) -> B.Octets:
  B.Octets.be64(v)

# <string>

def pr.str.rest(rest: List<&2, U32>, head: List<&2, U32>) -> Result<&2, &2, E.FdtError, B.Octets>:
  match rest:
    case Nil{}:
      Done{B.Octets.of_list(head)}
    case Con{h, t}:
      Fail{E.FdtBadString{}}

def pr.str(m: Maybe<&2, L.FdtCut>) -> Result<&2, &2, E.FdtError, B.Octets>:
  match m:
    case None{}:
      Fail{E.FdtBadString{}}
    case Some{c}:
      match c:
        case L.FdtCut{head, rest}:
          pr.str.rest(rest, head)

# a NUL-terminated string with no other NUL: its bytes, without the NUL
def FdtProp.string(o: B.Octets) -> Result<&2, &2, E.FdtError, B.Octets>:
  pr.str(L.fdt.cstr(B.Octets.to_list(o)))

# the bytes s, then a NUL
def FdtProp.of_string(s: B.Octets) -> B.Octets:
  B.Octets.append(s, B.Octets.zeros(1n))

def pr.text(r: Result<&2, &2, E.FdtError, B.Octets>) -> Result<&2, &2, E.FdtError, String>:
  match r:
    case Done{s}:
      Done{B.Octets.to_string(s)}
    case Fail{e}:
      Fail{e}

# the same, as text (one character per byte)
def FdtProp.text(o: B.Octets) -> Result<&2, &2, E.FdtError, String>:
  pr.text(FdtProp.string(o))

def FdtProp.of_text(s: String) -> B.Octets:
  FdtProp.of_string(B.Octets.of_string(s))

# a string without NULs, which of_string and string carry unchanged
def FdtProp.string_ok(s: B.Octets) -> Bool:
  L.fdt.nonul.fast(B.Octets.to_list(s))

# <stringlist>: strings one after another, each NUL-terminated

# the string being read (reversed), and the strings read so far (reversed)
type FdtStrList is Data:
  FdtStrList{cur: List<&2, U32>, done: List<&2, B.Octets>}

def pr.sl.byte(nul: Bool, h: U32, cur: List<&2, U32>, done: List<&2, B.Octets>) -> FdtStrList:
  match nul:
    case True{}:
      FdtStrList{Nil{}, Con{B.Octets.of_list(List.reverse(&2, U32, cur)), done}}
    case False{}:
      FdtStrList{Con{h, cur}, done}

def pr.sl.end(cur: List<&2, U32>, done: List<&2, B.Octets>) -> Result<&2, &2, E.FdtError, List<&2, B.Octets>>:
  match cur:
    case Nil{}:
      Done{List.reverse(&2, B.Octets, done)}
    case Con{h, t}:
      Fail{E.FdtBadString{}}

def pr.sl.fold(xs: List<&2, U32>, st: FdtStrList) -> FdtStrList:
  match xs:
    case Nil{}:
      st
    case Con{+h, t}:
      match st:
        case FdtStrList{cur, done}:
          pr.sl.fold(t, pr.sl.byte(U32.is_eq(h, 0), h, cur, done))

def pr.sl.fin(st: FdtStrList) -> Result<&2, &2, E.FdtError, List<&2, B.Octets>>:
  match st:
    case FdtStrList{cur, done}:
      pr.sl.end(cur, done)

# the strings of a <stringlist>; the last must end with its NUL (an empty
# value is the empty list)
def FdtProp.strings(o: B.Octets) -> Result<&2, &2, E.FdtError, List<&2, B.Octets>>:
  pr.sl.fin(pr.sl.fold(B.Octets.to_list(o), FdtStrList{Nil{}, Nil{}}))

# the bytes of a <stringlist> (the reference form the proofs compute
# through; it recurses once per string)
def pr.sl.list(ss: List<&2, B.Octets>) -> List<&2, U32>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      B.append(B.Octets.to_list(s), Con{0, pr.sl.list(t)})

# The same, tail-recursive, for lists of any size (PROOF.bend: sl_fast):
# each string's bytes and its NUL pushed, reversed, onto acc
def pr.sl.out(ss: List<&2, B.Octets>, acc: List<&2, U32>) -> List<&2, U32>:
  match ss:
    case Nil{}:
      acc
    case Con{s, t}:
      pr.sl.out(t, Con{0, List.reverse.go(&2, U32, B.Octets.to_list(s), acc)})

def pr.sl.fast(ss: List<&2, B.Octets>) -> List<&2, U32>:
  List.reverse(&2, U32, pr.sl.out(ss, Nil{}))

# each string, then a NUL
def FdtProp.of_strings(ss: List<&2, B.Octets>) -> B.Octets:
  B.Octets.of_list(pr.sl.fast(ss))

# strings_ok as the proofs state it (the reference form)
def pr.strings_ok.ref(ss: List<&2, B.Octets>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, t}:
      Bool.and(L.fdt.nonul(B.Octets.to_list(s)), pr.strings_ok.ref(t))

def pr.sl.ok(ss: List<&2, B.Octets>, ok: Bool) -> Bool:
  match ss:
    case Nil{}:
      ok
    case Con{s, t}:
      pr.sl.ok(t, Bool.and(ok, L.fdt.nonul.fast(B.Octets.to_list(s))))

# strings without NULs, which of_strings and strings carry unchanged
# (PROOF.bend: strings_ok_fast)
def FdtProp.strings_ok(ss: List<&2, B.Octets>) -> Bool:
  pr.sl.ok(ss, True{})

# <prop-encoded-array>: 32-bit cells

def pr.w32(m: Maybe<&2, U32>) -> U32:
  match m:
    case Some{v}:
      v
    case None{}:
      0

def pr.cells.go(xs: List<&2, U32>, acc: List<&2, U32>) -> Result<&2, &2, E.FdtError, List<&2, U32>>:
  match xs:
    case Nil{}:
      Done{List.reverse(&2, U32, acc)}
    case Con{a, Con{b, Con{c, Con{d, t}}}}:
      pr.cells.go(t, Con{pr.w32(B.be32_at([a, b, c, d], 0n)), acc})
    case _:
      Fail{E.FdtBadLength{}}

# the value's 32-bit cells; its length must be a multiple of four
def FdtProp.cells(o: B.Octets) -> Result<&2, &2, E.FdtError, List<&2, U32>>:
  pr.cells.go(B.Octets.to_list(o), Nil{})

# the bytes of the cells (the reference form; it recurses once per cell)
def pr.cells.list(cs: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      B.append(B.be32(c), pr.cells.list(t))

# the same, tail-recursive (PROOF.bend: cells_fast)
def pr.cells.out(cs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match cs:
    case Nil{}:
      acc
    case Con{c, t}:
      pr.cells.out(t, List.reverse.go(&2, U32, B.be32(c), acc))

def pr.cells.fast(cs: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, pr.cells.out(cs, Nil{}))

def FdtProp.of_cells(cs: List<&2, U32>) -> B.Octets:
  B.Octets.of_list(pr.cells.fast(cs))

# reg: (address, size) pairs, each of #address-cells and #size-cells cells
# (taken from the parent node); 0, 1 or 2 cells each, so that a W64 holds it

type FdtReg is Data:
  FdtReg{address: W.W64, size: W.W64}

# a number of 0, 1 or 2 cells, most significant first
def pr.num(cs: List<&2, U32>) -> W.W64:
  match cs:
    case Nil{}:
      W.W64.zero()
    case Con{l, Nil{}}:
      W.W64.from_u32(l)
    case Con{h, Con{l, rest}}:
      W.W64.from_parts(h, l)

# the cells of one pair (reversed), and the pairs so far (reversed)
type FdtRegAcc is Data:
  FdtRegAcc{buf: List<&2, U32>, n: Nat, regs: List<&2, FdtReg>}

def pr.reg.emit(full: Bool, +ac: Nat, buf: List<&2, U32>, +n: Nat, regs: List<&2, FdtReg>) -> FdtRegAcc:
  match full:
    case True{}:
      +cs = List.reverse(&2, U32, buf)
      FdtRegAcc{Nil{}, 0n, Con{FdtReg{pr.num(B.take(ac, cs)), pr.num(B.drop(ac, cs))}, regs}}
    case False{}:
      FdtRegAcc{buf, n, regs}

def pr.reg.go(cs: List<&2, U32>, +ac: Nat, +k: Nat, st: FdtRegAcc) -> Result<&2, &2, E.FdtError, List<&2, FdtReg>>:
  match cs:
    case Nil{}:
      match st:
        case FdtRegAcc{buf, n, regs}:
          match buf:
            case Nil{}:
              Done{List.reverse(&2, FdtReg, regs)}
            case Con{h, t}:
              Fail{E.FdtBadLength{}}
    case Con{c, t}:
      match st:
        case FdtRegAcc{buf, n, regs}:
          +m = Nat.add(1n, n)
          pr.reg.go(t, ac, k, pr.reg.emit(Nat.is_eq(m, k), ac, Con{c, buf}, m, regs))

def pr.reg.cells(r: Result<&2, &2, E.FdtError, List<&2, U32>>, +ac: Nat, +sc: Nat) -> Result<&2, &2, E.FdtError, List<&2, FdtReg>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{cs}:
      pr.reg.go(cs, ac, Nat.add(ac, sc), FdtRegAcc{Nil{}, 0n, Nil{}})

def pr.reg.ok(ok: Bool, o: B.Octets, ac: Nat, sc: Nat) -> Result<&2, &2, E.FdtError, List<&2, FdtReg>>:
  match ok:
    case True{}:
      pr.reg.cells(FdtProp.cells(o), ac, sc)
    case False{}:
      Fail{E.FdtBadCells{}}

# the (address, size) pairs of a reg value, with ac address cells and sc size
# cells per pair: FdtBadCells unless both are at most 2 and not both 0;
# FdtBadLength unless the value is a whole number of pairs
def FdtProp.reg(+ac: Nat, +sc: Nat, o: B.Octets) -> Result<&2, &2, E.FdtError, List<&2, FdtReg>>:
  pr.reg.ok(Bool.and(Nat.is_le(ac, 2n), Bool.and(Nat.is_le(sc, 2n), Bool.not(Nat.is_eq(Nat.add(ac, sc), 0n)))), o, ac, sc)

# a number as n cells (0, 1 or 2; more cells are zero-extended)
def pr.cells_of(n: Nat, +v: W.W64) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      match p:
        case 0n:
          [W.W64.lo(v)]
        case 1n+q:
          List.append(&2, U32, B.zeros(q), [W.W64.hi(v), W.W64.lo(v)])

# each pair's cells, reversed, in front of acc
def pr.reg.out(+ac: Nat, +sc: Nat, rs: List<&2, FdtReg>, acc: List<&2, U32>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      acc
    case Con{r, t}:
      match r:
        case FdtReg{a, s}:
          pr.reg.out(ac, sc, t, List.reverse.go(&2, U32, pr.cells_of(sc, s), List.reverse.go(&2, U32, pr.cells_of(ac, a), acc)))

def FdtProp.of_reg(ac: Nat, sc: Nat, rs: List<&2, FdtReg>) -> B.Octets:
  FdtProp.of_cells(List.reverse(&2, U32, pr.reg.out(ac, sc, rs, Nil{})))
