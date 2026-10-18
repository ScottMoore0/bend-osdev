# The reference test's Bend side: a sparse in-memory device (the blocks that
# are not all zero, in order), and one line of output per operation, in the
# format ref/gen.py's reader writes to expected.txt. cases.bend (written by
# gen.py) holds the images and calls these.
import Base
import ../../bytes/bytes.bend as B
import ../../blockdev/blockdev.bend as D
import ../error.bend as E
import ../bpb.bend as P
import ../table.bend as T
import ../dirent.bend as R
import ../dir.bend as Q
import ../file.bend as F
import ../fat.bend as M

# A device of count blocks of bs bytes; the blocks not listed are zero
type SparseBlock is Data:
  SparseBlock{at: Nat, data: B.Octets}

type SparseDev is Data:
  SparseDev{bs: Nat, count: Nat, blocks: List<&2, SparseBlock>}

def SparseDev.block_size(d: SparseDev) -> Nat:
  match d:
    case SparseDev{bs, n, xs}:
      bs

def SparseDev.pick(hit: Bool, a: B.Octets, b: B.Octets) -> B.Octets:
  match hit:
    case True{}:
      a
    case False{}:
      b

def SparseDev.find(xs: List<&2, SparseBlock>, +n: Nat, +bs: Nat) -> B.Octets:
  match xs:
    case Nil{}:
      B.Octets.zeros(bs)
    case Con{SparseBlock{+at, data}, t}:
      SparseDev.pick(Nat.is_eq(at, n), data, SparseDev.find(t, n, bs))

def SparseDev.read.go(ok: Bool, d: SparseDev, +n: Nat) -> Result<&2, &2, D.DevError, B.Octets>:
  match ok d:
    case True{} SparseDev{+bs, c, xs}:
      Done{SparseDev.find(xs, n, bs)}
    case False{} _:
      Fail{D.DevOutOfRange{n}}

def SparseDev.read_block.go(+d: SparseDev, +n: Nat) -> Result<&2, &2, D.DevError, B.Octets>:
  match d:
    case SparseDev{bs, +c, xs}:
      SparseDev.read.go(Nat.is_lt(n, c), d, n)

def SparseDev.read_block(d: SparseDev, n: Nat) -> Result<&2, &2, D.DevError, B.Octets>:
  SparseDev.read_block.go(d, n)

# Hex text to bytes, padded with zeros to bs

def H.digit.off(letter: Bool) -> U32:
  match letter:
    case True{}:
      87
    case False{}:
      48

def H.digit(c: Char) -> U32:
  match c:
    case Chr{+x}:
      U32.sub(x, H.digit.off(U32.is_ge(x, 97)))

def H.unhex(s: String) -> List<&2, U32>:
  match s:
    case SCon{a, SCon{b, t}}:
      Con{U32.add(U32.mul(H.digit(a), 16), H.digit(b)), H.unhex(t)}
    case _:
      Nil{}

def H.block(+at: Nat, +bs: Nat, s: String) -> SparseBlock:
  +xs = H.unhex(s)
  SparseBlock{at, B.Octets.of_list(B.append(xs, B.zeros(Nat.sub(bs, B.len(xs)))))}

# Text

def H.hex32(v: U32) -> String:
  B.hex(B.be32(v))

def H.esc.one(plain: Bool, +c: Char) -> String:
  match plain:
    case True{}:
      SCon{c, ""}
    case False{}:
      "\\u" ++ H.hex32(Char.to_u32(c))

def H.esc(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{+c, t}:
      +x = Char.to_u32(c)
      H.esc.one(Bool.and(Bool.and(U32.is_ge(x, 32), U32.is_lt(x, 127)), Bool.not(Bool.or(U32.is_eq(x, 92), Bool.or(U32.is_eq(x, 124), U32.is_eq(x, 59))))), c) ++ H.esc(t)

def H.kind(dir: Bool) -> String:
  match dir:
    case True{}:
      "D"
    case False{}:
      "F"

def H.node(+n: Q.FatNode) -> String:
  H.esc(Q.FatNode.name(n)) ++ "|" ++ H.kind(Q.FatNode.is_dir(n)) ++ "|" ++ U32.show(Q.FatNode.size(n)) ++ "|" ++ H.esc(Q.FatNode.short_name(n))

def H.nodes(ns: List<&2, Q.FatNode>) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{h, t}:
      " " ++ H.node(h) ++ ";" ++ H.nodes(t)

def H.hash.go(xs: List<&2, U32>, +h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case Con{x, t}:
      H.hash.go(t, U32.add(U32.mul(h, 31), x))

def H.hash(o: B.Octets) -> U32:
  H.hash.go(B.Octets.to_list(o), 0)

def H.bytes.small(small: Bool, +o: B.Octets) -> String:
  match small:
    case True{}:
      " " ++ B.Octets.hex(o)
    case False{}:
      ""

# a byte string: its length, its hash, and its bytes when short
def H.bytes(+o: B.Octets) -> String:
  +n = B.Octets.len(o)
  Nat.show(n) ++ " " ++ H.hex32(H.hash(o)) ++ H.bytes.small(Nat.is_le(n, 48n), o)

def H.err(e: E.FatError) -> String:
  "error " ++ E.FatError.show(e)

# Operations; each mounts the volume itself

def H.mount.show(r: Result<&2, &2, E.FatError, M.FatFs>) -> String:
  match r:
    case Done{+fs}:
      P.FatType.show(M.FatFs.kind(fs)) ++ " " ++ U32.show(P.FatVolume.clusters(M.FatFs.volume(fs)))
    case Fail{e}:
      H.err(e)

def H.mount(+d: SparseDev, opts: P.FatOptions) -> String:
  H.mount.show(M.Fat.mount(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, opts))

def H.ls.show(r: Result<&2, &2, E.FatError, List<&2, Q.FatNode>>) -> String:
  match r:
    case Done{+ns}:
      Nat.show(List.length(&2, Q.FatNode, ns)) ++ H.nodes(ns)
    case Fail{e}:
      H.err(e)

def H.ls(+d: SparseDev, +opts: P.FatOptions, path: String) -> String:
  H.ls.show(do Result<&2, &2, E.FatError, List<&2, Q.FatNode>>:
    fs : M.FatFs <- M.Fat.mount(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, opts)
    M.Fat.list(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, fs, path))

def H.read.show(r: Result<&2, &2, E.FatError, B.Octets>) -> String:
  match r:
    case Done{o}:
      H.bytes(o)
    case Fail{e}:
      H.err(e)

# off and len as U32 (the cases are small)
def H.read(+d: SparseDev, +opts: P.FatOptions, path: String, off: U32, len: U32) -> String:
  H.read.show(do Result<&2, &2, E.FatError, B.Octets>:
    fs : M.FatFs <- M.Fat.mount(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, opts)
    M.Fat.read(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, fs, path, U32.to_nat(off), U32.to_nat(len)))

def H.stat.show(r: Result<&2, &2, E.FatError, Q.FatPath>) -> String:
  match r:
    case Done{Q.FatPathRoot{}}:
      "root"
    case Done{Q.FatPathNode{+n}}:
      H.node(n)
    case Fail{e}:
      H.err(e)

def H.stat(+d: SparseDev, +opts: P.FatOptions, path: String) -> String:
  H.stat.show(do Result<&2, &2, E.FatError, Q.FatPath>:
    fs : M.FatFs <- M.Fat.mount(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, opts)
    M.Fat.stat(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, fs, path))

def H.walk.show(r: Result<&2, &2, E.FatError, List<&2, U32>>) -> String:
  match r:
    case Done{+cs}:
      Nat.show(List.length(&2, U32, cs))
    case Fail{e}:
      H.err(e)

def H.walk.node(+d: SparseDev, +fs: M.FatFs, p: Q.FatPath) -> Result<&2, &2, E.FatError, List<&2, U32>>:
  match p:
    case Q.FatPathRoot{}:
      Fail{E.FatIsADirectory{}}
    case Q.FatPathNode{n}:
      T.FatChain.walk(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, M.FatFs.volume(fs), Q.FatNode.cluster(n))

# the number of clusters in the chain of the entry a path names
def H.walk.fs(+d: SparseDev, +fs: M.FatFs, path: String) -> Result<&2, &2, E.FatError, List<&2, U32>>:
  do Result<&2, &2, E.FatError, List<&2, U32>>:
    p : Q.FatPath <- M.Fat.stat(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, fs, path)
    H.walk.node(d, fs, p)

def H.walk(+d: SparseDev, +opts: P.FatOptions, path: String) -> String:
  H.walk.show(do Result<&2, &2, E.FatError, List<&2, U32>>:
    fs : M.FatFs <- M.Fat.mount(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, opts)
    H.walk.fs(d, fs, path))

# Streaming: the pieces Fat.next gives, counted and hashed together

type H.Sum is Data:
  H.Sum{pieces: Nat, total: Nat, hash: U32, ok: Bool}

def H.sum.add(s: H.Sum, +o: B.Octets, +sec: Nat) -> H.Sum:
  match s:
    case H.Sum{p, t, h, ok}:
      H.Sum{Nat.add(p, 1n), Nat.add(t, B.Octets.len(o)), H.hash.go(B.Octets.to_list(o), h), Bool.and(ok, Nat.is_le(B.Octets.len(o), sec))}

def H.stream.go(+d: SparseDev, +fs: M.FatFs, fuel: Nat, r: Result<&2, &2, E.FatError, F.FatChunk>, +s: H.Sum) -> Result<&2, &2, E.FatError, H.Sum>:
  match fuel:
    case 0n:
      Fail{E.FatChainLoop{}}
    case 1n+p:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{F.FatChunk{+o, None{}}}:
          Done{H.sum.add(s, o, P.FatVolume.sector(M.FatFs.volume(fs)))}
        case Done{F.FatChunk{+o, Some{cur}}}:
          H.stream.go(d, fs, p, M.Fat.next(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, fs, cur), H.sum.add(s, o, P.FatVolume.sector(M.FatFs.volume(fs))))

def H.stream.show(r: Result<&2, &2, E.FatError, H.Sum>) -> String:
  match r:
    case Done{H.Sum{p, t, h, ok}}:
      Nat.show(t) ++ " " ++ H.hex32(h) ++ " " ++ Bool.show(ok)
    case Fail{e}:
      H.err(e)

def H.stream.open(+d: SparseDev, +fs: M.FatFs, c: F.FatCursor) -> Result<&2, &2, E.FatError, H.Sum>:
  H.stream.go(d, fs, 100000n, M.Fat.next(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, fs, c), H.Sum{0n, 0n, 0, True{}})

# a whole file read a piece at a time: its length, its hash, and whether
# every piece was at most a sector
def H.stream.fs(+d: SparseDev, +fs: M.FatFs, path: String) -> Result<&2, &2, E.FatError, H.Sum>:
  do Result<&2, &2, E.FatError, H.Sum>:
    c : F.FatCursor <- M.Fat.open(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, fs, path)
    H.stream.open(d, fs, c)

def H.stream(+d: SparseDev, +opts: P.FatOptions, path: String) -> String:
  H.stream.show(do Result<&2, &2, E.FatError, H.Sum>:
    fs : M.FatFs <- M.Fat.mount(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, opts)
    H.stream.fs(d, fs, path))

def H.fsinfo.show(r: Result<&2, &2, E.FatError, P.FatFsInfo>) -> String:
  match r:
    case Done{P.FatFsInfo{f, n}}:
      U32.show(f) ++ " " ++ U32.show(n)
    case Fail{e}:
      H.err(e)

def H.fsinfo(+d: SparseDev, +opts: P.FatOptions) -> String:
  H.fsinfo.show(do Result<&2, &2, E.FatError, P.FatFsInfo>:
    fs : M.FatFs <- M.Fat.mount(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, opts)
    M.Fat.fs_info(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, fs))

def H.label.show(r: Result<&2, &2, E.FatError, P.FatBootExt>) -> String:
  match r:
    case Done{P.FatBootExt{drv, sig, id, label, fst}}:
      H.hex32(id) ++ " " ++ H.esc(B.Octets.to_string(label))
    case Fail{e}:
      H.err(e)

def H.label(+d: SparseDev, +opts: P.FatOptions) -> String:
  H.label.show(do Result<&2, &2, E.FatError, P.FatBootExt>:
    fs : M.FatFs <- M.Fat.mount(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, opts)
    M.Fat.boot_ext(~SparseDev, ~SparseDev.block_size, ~SparseDev.read_block, d, fs))

# Loading an image's device from a file: the listed blocks (those that are
# not all zero), each read on its own

def L.got(res: Result<&1, &1, U32 & String, List<&2, U32>>, +n: Nat, acc: List<&2, SparseBlock>) -> List<&2, SparseBlock>:
  match res:
    case Done{xs}:
      Con{SparseBlock{n, B.Octets.of_list(xs)}, acc}
    case Fail{e}:
      acc

def L.step(p: File & Result<&1, &1, U32 & String, List<&2, U32>>, +n: Nat, acc: List<&2, SparseBlock>) -> IO(File & List<&2, SparseBlock>):
  (f, res) = p
  IO.pure(File & List<&2, SparseBlock>, (f, L.got(res, n, acc)))

def L.go(ns: List<&2, Nat>, st: File & List<&2, SparseBlock>) -> IO(File & List<&2, SparseBlock>):
  match ns:
    case Nil{}:
      IO.pure(File & List<&2, SparseBlock>, st)
    case Con{+n, t}:
      (f, acc) = st
      do IO<File & List<&2, SparseBlock>>:
        r : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_at(f, U32.from_nat(Nat.mul(n, 512n)), 512)
        q : File & List<&2, SparseBlock> <- L.step(r, n, acc)
        L.go(t, q)

def L.rev(xs: List<&2, SparseBlock>, acc: List<&2, SparseBlock>) -> List<&2, SparseBlock>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      L.rev(t, Con{h, acc})

def L.fin(+count: Nat, r: File & List<&2, SparseBlock>) -> IO(SparseDev):
  (f, bs) = r
  do IO<SparseDev>:
    File.close(f)
    return SparseDev{512n, count, L.rev(bs, Nil{})}

def L.opened(r: Result<&1, &1, U32 & String, File>, ns: List<&2, Nat>, +count: Nat) -> IO(SparseDev):
  match r:
    case Done{f}:
      do IO<SparseDev>:
        q : File & List<&2, SparseBlock> <- L.go(ns, (f, Nil{}))
        L.fin(count, q)
    case Fail{e}:
      IO.pure(SparseDev, SparseDev{512n, count, Nil{}})

def L.file(path: String, ns: List<&2, Nat>, +count: Nat) -> IO(SparseDev):
  do IO<SparseDev>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    L.opened(r, ns, count)

# The queries a case file asks of an image, each with the label its line
# carries

type RQuery is Data:
  RQMount{label: String, strict: Bool}
  RQLabel{label: String}
  RQFsinfo{label: String}
  RQLs{label: String, strict: Bool, path: String}
  RQStat{label: String, path: String}
  RQRead{label: String, path: String, off: U32, len: U32}
  RQStream{label: String, path: String}
  RQWalk{label: String, path: String}

def RQ.opts(strict: Bool) -> P.FatOptions:
  match strict:
    case True{}:
      P.FatOptions.default()
    case False{}:
      P.FatOptions.lenient()

def RQ.run(q: RQuery, +d: SparseDev) -> String:
  match q:
    case RQMount{l, s}:
      l ++ " " ++ H.mount(d, RQ.opts(s))
    case RQLabel{l}:
      l ++ " " ++ H.label(d, P.FatOptions.default())
    case RQFsinfo{l}:
      l ++ " " ++ H.fsinfo(d, P.FatOptions.default())
    case RQLs{l, s, p}:
      l ++ " " ++ H.ls(d, RQ.opts(s), p)
    case RQStat{l, p}:
      l ++ " " ++ H.stat(d, P.FatOptions.default(), p)
    case RQRead{l, p, off, len}:
      l ++ " " ++ H.read(d, P.FatOptions.default(), p, off, len)
    case RQStream{l, p}:
      l ++ " " ++ H.stream(d, P.FatOptions.default(), p)
    case RQWalk{l, p}:
      l ++ " " ++ H.walk(d, P.FatOptions.default(), p)

def RQ.all(qs: List<&2, RQuery>, +tag: String, +d: SparseDev) -> IO(Unit):
  match qs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{q, t}:
      do IO<Unit>:
        IO.print(tag ++ " " ++ RQ.run(q, d))
        RQ.all(t, tag, d)

# one image (count 512-byte blocks, the blocks ns read from the file path)
# and its queries
def RImg.run(+tag: String, path: String, ns: List<&2, Nat>, +count: Nat, qs: List<&2, RQuery>) -> IO(Unit):
  do IO<Unit>:
    d : SparseDev <- L.file(path, ns, count)
    RQ.all(qs, tag, d)
