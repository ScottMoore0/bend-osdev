# bend-osdev-ext4: writing a jbd2 transaction: a list of block writes (and
# blocks to revoke) as the log blocks that journal them, ending in the
# commit block. jreplay.bend writes them into an ext4 journal.
#
# The blocks, in order: revoke blocks (if any blocks are revoked), then for
# each group of writes a descriptor holds, the descriptor and the data
# blocks (escaped: a block starting with the magic number is stored with
# its first four bytes zeroed, its tag marked ESCAPE), then the commit
# block. The first tag of each descriptor carries the journal's UUID, the
# others SAME_UUID; the last has LAST_TAG; with checksums each tag holds
# the checksum of the data block as the log stores it.
import Base
import ../bytes/bytes.bend as B
import ./jsuper.bend as J
import ./jblock.bend as JB

# a block write: block n of the filesystem becomes data (one block)
type Jbd2Write is Data:
  Jbd2Write{block: Nat, data: B.Octets}

def Jbd2Write.block(w: Jbd2Write) -> Nat:
  match w:
    case Jbd2Write{b, d}:
      b

def Jbd2Write.data(w: Jbd2Write) -> B.Octets:
  match w:
    case Jbd2Write{b, d}:
      d

# the first n elements and the rest
def Jbd2Write.split(-A: Data, n: Nat, xs: List<&2, A>, acc: List<&2, A>) -> List<&2, A> & List<&2, A>:
  match n xs:
    case 0n _:
      (List.reverse(&2, A, acc), xs)
    case _ Nil{}:
      (List.reverse(&2, A, acc), Nil{})
    case 1n+p Con{h, t}:
      Jbd2Write.split(A, p, t, Con{h, acc})

def Jbd2Write.flag.pick(b: Bool, v: U32) -> U32:
  match b:
    case True{}:
      v
    case False{}:
      0

def Jbd2Write.flags(+esc: Bool, +first: Bool, +last: Bool) -> U32:
  U32.or(Jbd2Write.flag.pick(esc, JB.Jbd2.flag_escape()), U32.or(Jbd2Write.flag.pick(Bool.not(first), JB.Jbd2.flag_same_uuid()), Jbd2Write.flag.pick(last, JB.Jbd2.flag_last())))

def Jbd2Write.is_nil(xs: List<&2, Jbd2Write>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

# the tags and stored data blocks of one descriptor's writes
def Jbd2Write.tags(ws: List<&2, Jbd2Write>, +g: J.Jbd2Geom, +seq: U32, +first: Bool, ts: List<&2, JB.Jbd2Tag>, ds: List<&2, B.Octets>) -> List<&2, JB.Jbd2Tag> & List<&2, B.Octets>:
  match ws:
    case Nil{}:
      (List.reverse(&2, JB.Jbd2Tag, ts), List.reverse(&2, B.Octets, ds))
    case Con{Jbd2Write{b, +d}, +t}:
      +esc = JB.Jbd2.needs_escape(d)
      +stored = JB.Jbd2.escape(d)
      Jbd2Write.tags(t, g, seq, False{}, Con{JB.Jbd2Tag{b, Jbd2Write.flags(esc, first, Jbd2Write.is_nil(t)), JB.Jbd2.tag_csum(J.Jbd2Geom.csum(g), g, seq, stored)}, ts}, Con{stored, ds})

def Jbd2Write.desc(+g: J.Jbd2Geom, +seq: U32, +uuid: B.Octets, r: List<&2, JB.Jbd2Tag> & List<&2, B.Octets>) -> List<&2, B.Octets>:
  (ts, ds) = r
  Con{JB.Jbd2Desc.encode(g, seq, ts, uuid), ds}

# the descriptors and data blocks of the writes, cap writes to a
# descriptor: r is the next group and the writes after it, acc the blocks
# of the groups before (last first); fuel bounds the groups
def Jbd2Write.groups(fuel: Nat, r: List<&2, Jbd2Write> & List<&2, Jbd2Write>, +g: J.Jbd2Geom, +seq: U32, +uuid: B.Octets, +cap: Nat, acc: List<&2, List<&2, B.Octets>>) -> List<&2, B.Octets>:
  match fuel:
    case 0n:
      List.concat(&2, B.Octets, List.reverse(&2, List<&2, B.Octets>, acc))
    case 1n+f:
      (ws, rest) = r
      match ws:
        case Nil{}:
          List.concat(&2, B.Octets, List.reverse(&2, List<&2, B.Octets>, acc))
        case Con{w, t}:
          Jbd2Write.groups(f, Jbd2Write.split(Jbd2Write, cap, rest, Nil{}), g, seq, uuid, cap, Con{Jbd2Write.desc(g, seq, uuid, Jbd2Write.tags(Con{w, t}, g, seq, True{}, Nil{}, Nil{})), acc})

# the revoke blocks for bs, cap block numbers to a block
def Jbd2Write.revokes(fuel: Nat, r: List<&2, Nat> & List<&2, Nat>, +g: J.Jbd2Geom, +seq: U32, +cap: Nat, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match fuel:
    case 0n:
      List.reverse(&2, B.Octets, acc)
    case 1n+f:
      (bs, rest) = r
      match bs:
        case Nil{}:
          List.reverse(&2, B.Octets, acc)
        case Con{b, t}:
          Jbd2Write.revokes(f, Jbd2Write.split(Nat, cap, rest, Nil{}), g, seq, cap, Con{JB.Jbd2Revoke.encode(g, seq, Con{b, t}), acc})

# the log blocks of transaction seq: the revoke blocks for rv, the
# descriptors and data blocks for ws (each write's data one block), and
# the commit block stamped with the time sec, nsec
def Jbd2Write.blocks(+g: J.Jbd2Geom, +uuid: B.Octets, +seq: Nat, +rv: List<&2, Nat>, +ws: List<&2, Jbd2Write>, +sec: U32, +nsec: U32) -> List<&2, B.Octets>:
  +s = U32.from_nat(seq)
  +rcap = JB.Jbd2Revoke.capacity(g)
  +dcap = JB.Jbd2Desc.capacity(g)
  +a = Jbd2Write.revokes(1n+List.length(&2, Nat, rv), Jbd2Write.split(Nat, rcap, rv, Nil{}), g, s, rcap, Nil{})
  +b = Jbd2Write.groups(1n+List.length(&2, Jbd2Write, ws), Jbd2Write.split(Jbd2Write, dcap, ws, Nil{}), g, s, uuid, dcap, Nil{})
  List.append(&2, B.Octets, a, List.append(&2, B.Octets, b, Con{JB.Jbd2Commit.encode(g, s, sec, nsec), Nil{}}))
