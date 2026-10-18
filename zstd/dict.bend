# bend-osdev-zstd, dictionaries (RFC 8878, section 5).
#
# A dictionary is either raw content (any bytes that do not start with the
# dictionary magic number), which frames use as history before their first
# byte, or a formatted dictionary: the magic number 0xEC30A437, a 4-byte
# dictionary ID, entropy tables (a Huffman tree description, then FSE table
# descriptions for offsets, match lengths and literals lengths), the three
# repeat offsets (4 bytes each), and the content. A frame decoded with a
# formatted dictionary starts with its tables and repeat offsets, so its
# first block may use treeless literals and repeat modes.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./fse.bend as F
import ./huffman.bend as H
import ./sequences.bend as S
import ./block.bend as K

# the ID (0 for raw content), the content, and what a frame starts with
type ZstdDict is Data:
  ZstdDict{id: U32, content: List<&2, U32>, huf: Maybe<&2, H.ZstdHufTable>, tables: S.ZstdSeqTables, reps: K.ZstdReps}

# no dictionary
def ZstdDict.none() -> ZstdDict:
  ZstdDict{0, Nil{}, None{}, S.ZstdSeqTables.none(), K.ZstdReps.initial()}

def dict.nat(xs: List<&2, U32>, i: Nat) -> Nat:
  U32.to_nat(B.byte(Maybe.default(&2, U32, B.at(xs, i), 0)))

def dict.le32(+xs: List<&2, U32>, +i: Nat) -> Nat:
  Nat.add(Nat.add(dict.nat(xs, i), Nat.mul(dict.nat(xs, 1n+i), 256n)), Nat.add(Nat.mul(dict.nat(xs, 2n+i), 65536n), Nat.mul(dict.nat(xs, 3n+i), 16777216n)))

# the magic number 0xEC30A437 (little-endian: 0x37 0xA4 0x30 0xEC), byte by
# byte
def dict.magic(+xs: List<&2, U32>) -> Bool:
  Bool.and(Nat.is_eq(dict.nat(xs, 0n), 55n), Bool.and(Nat.is_eq(dict.nat(xs, 1n), 164n), Bool.and(Nat.is_eq(dict.nat(xs, 2n), 48n), Nat.is_eq(dict.nat(xs, 3n), 236n))))

# the dictionary ID, bytes 4 to 7
def dict.id_of(+xs: List<&2, U32>) -> U32:
  +b0 = B.byte(Maybe.default(&2, U32, B.at(xs, 4n), 0))
  +b1 = B.byte(Maybe.default(&2, U32, B.at(xs, 5n), 0))
  +b2 = B.byte(Maybe.default(&2, U32, B.at(xs, 6n), 0))
  +b3 = B.byte(Maybe.default(&2, U32, B.at(xs, 7n), 0))
  U32.or(U32.or(b0, U32.shln(b1, 8n)), U32.or(U32.shln(b2, 16n), U32.shln(b3, 24n)))

def dict.desc_at(+xs: List<&2, U32>, +pos: Nat, +max_al: Nat, +max_sym: Nat) -> Result<&2, &2, E.ZstdError, F.ZstdFseDesc>:
  E.ZstdError.need(F.ZstdFseDesc, F.ZstdFse.read_description(B.drop(pos, xs), max_al, max_sym), E.ZstdBadDictionary{})

def dict.table(d: F.ZstdFseDesc) -> Result<&2, &2, E.ZstdError, F.ZstdFseTable>:
  match d:
    case F.ZstdFseDesc{+al, probs, used}:
      E.ZstdError.need(F.ZstdFseTable, F.ZstdFse.table(al, probs), E.ZstdBadDictionary{})

def dict.used(d: F.ZstdFseDesc) -> Nat:
  match d:
    case F.ZstdFseDesc{al, probs, used}:
      used

def dict.rep_ok(+r: Nat, +n: Nat) -> Bool:
  Bool.and(Nat.is_lt(0n, r), Nat.is_le(r, n))

def dict.huf(r: H.ZstdHufRead) -> H.ZstdHufTable:
  match r:
    case H.ZstdHufRead{t, used}:
      t

def dict.huf_used(r: H.ZstdHufRead) -> Nat:
  match r:
    case H.ZstdHufRead{t, used}:
      used

def dict.formatted(+xs: List<&2, U32>) -> Result<&2, &2, E.ZstdError, ZstdDict>:
  do Result<&2, &2, E.ZstdError, ZstdDict>:
    +h : H.ZstdHufRead <- E.ZstdError.need(H.ZstdHufRead, H.ZstdHuf.read_tree(B.drop(8n, xs)), E.ZstdBadDictionary{})
    +p1 : Nat = Nat.add(8n, dict.huf_used(h))
    +dof : F.ZstdFseDesc <- dict.desc_at(xs, p1, 8n, 31n)
    +p2 : Nat = Nat.add(p1, dict.used(dof))
    +dml : F.ZstdFseDesc <- dict.desc_at(xs, p2, 9n, 52n)
    +p3 : Nat = Nat.add(p2, dict.used(dml))
    +dll : F.ZstdFseDesc <- dict.desc_at(xs, p3, 9n, 35n)
    +p4 : Nat = Nat.add(p3, dict.used(dll))
    tof : F.ZstdFseTable <- dict.table(dof)
    tml : F.ZstdFseTable <- dict.table(dml)
    tll : F.ZstdFseTable <- dict.table(dll)
    u1 : Unit <- E.ZstdError.require(Nat.is_le(Nat.add(p4, 12n), B.len.fast(xs)), E.ZstdBadDictionary{})
    content : List<&2, U32> = B.drop(Nat.add(p4, 12n), xs)
    +n : Nat = B.len.fast(B.drop(Nat.add(p4, 12n), xs))
    +r1 : Nat = dict.le32(xs, p4)
    +r2 : Nat = dict.le32(xs, Nat.add(p4, 4n))
    +r3 : Nat = dict.le32(xs, Nat.add(p4, 8n))
    u2 : Unit <- E.ZstdError.require(Bool.and(dict.rep_ok(r1, n), Bool.and(dict.rep_ok(r2, n), dict.rep_ok(r3, n))), E.ZstdBadDictionary{})
    return ZstdDict{dict.id_of(xs), content, Some{dict.huf(h)}, S.ZstdSeqTables{Some{tll}, Some{tof}, Some{tml}}, K.ZstdReps{r1, r2, r3}}

def dict.pick(fmt: Bool, +xs: List<&2, U32>) -> Result<&2, &2, E.ZstdError, ZstdDict>:
  match fmt:
    case True{}:
      dict.formatted(xs)
    case False{}:
      Done{ZstdDict{0, xs, None{}, S.ZstdSeqTables.none(), K.ZstdReps.initial()}}

# The public interface

# the dictionary in o: formatted if it starts with the magic number
# (ZstdBadDictionary if it is malformed), else raw content
def ZstdDict.parse(o: B.Octets) -> Result<&2, &2, E.ZstdError, ZstdDict>:
  +xs = B.Octets.to_list(o)
  dict.pick(Bool.and(Nat.is_le(8n, B.len.fast(xs)), dict.magic(xs)), xs)

def ZstdDict.id(d: ZstdDict) -> U32:
  match d:
    case ZstdDict{id, content, huf, tables, reps}:
      id

def ZstdDict.content(d: ZstdDict) -> List<&2, U32>:
  match d:
    case ZstdDict{id, content, huf, tables, reps}:
      content
