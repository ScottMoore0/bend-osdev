# The receive queue delivers the stream's bytes, for every input: if the
# pieces held are the stream's bytes at their offsets, and so is the piece
# that arrives, then what an insert delivers is the stream's bytes from the
# next offset on, and the pieces still held are the stream's at their
# offsets. With rcvq_contiguous (LAWS.bend: the next offset moves by the
# length delivered), the bytes the application reads, insert after insert,
# are the stream's from its start, in order and without gaps, whatever
# order the pieces came in, overlapping or resent.
#
# The stream is any byte string str: a piece RcvSeg{at, d} is the stream's
# when d is str's len(d) bytes at offset at (stream_seg leaves it as it is).
#
# A pair of its own (PROOF_stream.bend): the proofs rest on
# bend-osdev-bytes' laws of take, drop and append on Octets.
import Base
import ../bytes/bytes.bend as B
import ./rcvq.bend as Q

# the piece with the stream's bytes at its offset, as many as it has
def stream_seg(s: Q.RcvSeg, +str: B.Octets) -> Q.RcvSeg:
  match s:
    case Q.RcvSeg{+at, d}:
      Q.RcvSeg{at, B.Octets.slice(at, B.Octets.len(d), str)}

def stream_segs(xs: List<&2, Q.RcvSeg>, +str: B.Octets) -> List<&2, Q.RcvSeg>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      Con{stream_seg(s, str), stream_segs(t, str)}

# the pieces an insert leaves held
def out_held(o: Q.RcvOut) -> List<&2, Q.RcvSeg>:
  match o:
    case Q.RcvOut{n, h, d}:
      h

law rcvq_stream:
  for +limit: Nat
  for +n: Nat
  for +held: List<&2, Q.RcvSeg>
  for +rel: Nat
  for +d: B.Octets
  for +str: B.Octets
  for +hq: {stream_segs(held, str) == held : List<&2, Q.RcvSeg>}
  for +hd: {B.Octets.slice(Nat.add(n, rel), B.Octets.len(d), str) == d : B.Octets}
  {B.Octets.slice(n, B.Octets.len(Q.RcvOut.data(Q.RcvQ.insert(limit, Q.RcvQ{n, held}, rel, d))), str) == Q.RcvOut.data(Q.RcvQ.insert(limit, Q.RcvQ{n, held}, rel, d)) : B.Octets}

law rcvq_stream_held:
  for +limit: Nat
  for +n: Nat
  for +held: List<&2, Q.RcvSeg>
  for +rel: Nat
  for +d: B.Octets
  for +str: B.Octets
  for +hq: {stream_segs(held, str) == held : List<&2, Q.RcvSeg>}
  for +hd: {B.Octets.slice(Nat.add(n, rel), B.Octets.len(d), str) == d : B.Octets}
  {stream_segs(out_held(Q.RcvQ.insert(limit, Q.RcvQ{n, held}, rel, d)), str) == out_held(Q.RcvQ.insert(limit, Q.RcvQ{n, held}, rel, d)) : List<&2, Q.RcvSeg>}

# Vector: "world" at offset 6 is held, then "hello " at 0 delivers both
law rcvq_stream_vec:
  {Q.RcvOut.data(Q.RcvQ.insert(4n, Q.RcvOut.queue(Q.RcvQ.insert(4n, Q.RcvQ.new(), 6n, B.Octets.of_string("world"))), 0n, B.Octets.of_string("hello "))) == B.Octets.of_string("hello world") : B.Octets}

# the hypotheses of rcvq_stream hold: a new queue and a piece of the stream
law rcvq_stream_sat:
  {(stream_segs(Nil{}, B.Octets.of_string("hello world")), B.Octets.slice(Nat.add(0n, 6n), B.Octets.len(B.Octets.of_string("world")), B.Octets.of_string("hello world"))) == (Nil{}, B.Octets.of_string("world")) : List<&2, Q.RcvSeg> & B.Octets}
