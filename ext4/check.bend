import Base
import ../bytes/bytes.bend as B
import ../crc/crc.bend as C
import ../blockdev/blockdev.bend as D
import ../ext2/options.bend as XO
import ../ext2/inode.bend as N
import ../ext2/dir.bend as DR
import ./error.bend as E
import ./options.bend as O
import ./super.bend as S
import ./hash.bend as H
import ./dx.bend as X
import ./htree.bend as T
import ./htwrite.bend as HW
import ./xattr.bend as XA
import ./jwrite.bend as JW
import ./devwrite.bend as DW
import ./journal.bend as JR
import ./overlay.bend as OV
import ./ext4.bend as X4
import ./sample.bend as SM

# The sample image (sample.bend; ref/sample.py writes it with mke2fs and
# debugfs): /big (12, indexed, 150 names of inode 13), /small (17, an
# inline directory holding a, 18), /inl (15, 50 bytes inline), /inl2 (16,
# 100 bytes: 60 in i_block, 40 in system.data), /file (14, 1500 bytes,
# attributes user.short in the inode, user.mid in the attribute block,
# user.huge in an EA inode), and three journal transactions: blocks 1900
# and 1901, then 1900 revoked, then 1902 (starting with the magic number).

def Ext4Check.p(s: String) -> B.Octets:
  B.Octets.of_string(s)

def Ext4Check.err(+e: E.Ext4Error) -> String:
  "err " ++ E.Ext4Error.kind(e)

def Ext4Check.opts() -> O.Ext4Options:
  O.Ext4Options.with_ext2(O.Ext4Options.default(), XO.Ext2Options.with_recovery(O.Ext4Options.ext2(O.Ext4Options.default()), True{}))

def Ext4Check.ents(es: List<&2, DR.Ext2Dirent>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{+e, t}:
      " " ++ B.Octets.to_string(DR.Ext2Dirent.name(e)) ++ ":" ++ U32.show(DR.Ext2Dirent.inode(e)) ++ ":" ++ U32.show(DR.Ext2Dirent.file_type(e)) ++ Ext4Check.ents(t)

def Ext4Check.ls(r: Result<&2, &2, E.Ext4Error, List<&2, DR.Ext2Dirent>>) -> String:
  match r:
    case Done{es}:
      "ls" ++ Ext4Check.ents(es)
    case Fail{e}:
      Ext4Check.err(e)

def Ext4Check.count(r: Result<&2, &2, E.Ext4Error, List<&2, DR.Ext2Dirent>>) -> String:
  match r:
    case Done{es}:
      "entries " ++ Nat.show(List.length(&2, DR.Ext2Dirent, es))
    case Fail{e}:
      Ext4Check.err(e)

def Ext4Check.ino(r: Result<&2, &2, E.Ext4Error, N.Ext2Inode>) -> String:
  match r:
    case Done{+i}:
      "inode " ++ Nat.show(N.Ext2Inode.number_of(i)) ++ " " ++ N.Ext2Kind.show(N.Ext2Inode.kind(i))
    case Fail{e}:
      Ext4Check.err(e)

def Ext4Check.data(r: Result<&2, &2, E.Ext4Error, B.Octets>) -> String:
  match r:
    case Done{+o}:
      Nat.show(B.Octets.len(o)) ++ " bytes, crc32 " ++ U32.show(C.crc32(o))
    case Fail{e}:
      Ext4Check.err(e)

def Ext4Check.text(r: Result<&2, &2, E.Ext4Error, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.to_string(o)
    case Fail{e}:
      Ext4Check.err(e)

def Ext4Check.xas(xs: List<&2, XA.Ext4Xattr>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, t}:
      " " ++ B.Octets.to_string(XA.Ext4Xattr.full_name(x)) ++ "=" ++ Nat.show(XA.Ext4Xattr.size(x)) ++ Ext4Check.xas(t)

def Ext4Check.xl(r: Result<&2, &2, E.Ext4Error, List<&2, XA.Ext4Xattr>>) -> String:
  match r:
    case Done{xs}:
      "xattrs" ++ Ext4Check.xas(xs)
    case Fail{e}:
      Ext4Check.err(e)

def Ext4Check.block(r: Result<&2, &2, D.DevError, B.Octets>) -> String:
  match r:
    case Done{o}:
      U32.show(C.crc32(o))
    case Fail{e}:
      "fail"

def Ext4Check.text_block(r: Result<&2, &2, D.DevError, B.Octets>) -> String:
  match r:
    case Done{o}:
      B.Octets.to_string(B.Octets.take(23n, o))
    case Fail{e}:
      "fail"

# Reading

def Ext4Check.lookup(+d: D.MemDev, +fs: S.Ext4Fs, s: String) -> String:
  Ext4Check.ino(X4.Ext4.lookup(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext4Check.p(s)))

def Ext4Check.read(+d: D.MemDev, +fs: S.Ext4Fs, s: String) -> String:
  Ext4Check.data(X4.Ext4.read(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext4Check.p(s)))

def Ext4Check.reading(+d: D.MemDev, +fs: S.Ext4Fs) -> IO(Unit):
  do IO<Unit>:
    IO.print(Ext4Check.lookup(d, fs, "/big/f_17"))
    IO.print(Ext4Check.lookup(d, fs, "/big/f_149"))
    IO.print(Ext4Check.lookup(d, fs, "/big/f_150"))
    IO.print(Ext4Check.lookup(d, fs, "/big/.."))
    IO.print(Ext4Check.lookup(d, fs, "/small/a"))
    IO.print(Ext4Check.lookup(d, fs, "/small/a/b"))
    IO.print(Ext4Check.count(X4.Ext4.list(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext4Check.p("/big"))))
    IO.print(Ext4Check.ls(X4.Ext4.list(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext4Check.p("/small"))))
    IO.print(Ext4Check.text(X4.Ext4.read(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext4Check.p("/small/a"))))
    IO.print(Ext4Check.read(d, fs, "/inl"))
    IO.print(Ext4Check.read(d, fs, "/inl2"))
    IO.print(Ext4Check.read(d, fs, "/file"))
    IO.print(Ext4Check.read(d, fs, "/target"))
    IO.print(Ext4Check.xl(X4.Ext4.xattrs(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext4Check.p("/file"))))
    IO.print(Ext4Check.text(X4.Ext4.xattr(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext4Check.p("/file"), Ext4Check.p("user.short"))))
    IO.print(Ext4Check.data(X4.Ext4.xattr(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext4Check.p("/file"), Ext4Check.p("user.mid"))))
    IO.print(Ext4Check.data(X4.Ext4.xattr(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext4Check.p("/file"), Ext4Check.p("user.huge"))))
    IO.print(Ext4Check.data(X4.Ext4.xattr(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext4Check.p("/file"), Ext4Check.p("user.none"))))

# The journal: recovery, then a transaction committed and recovered again

def Ext4Check.recovered(r: Result<&2, &2, E.Ext4Error, JR.Ext4Recovered<D.MemDev>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(Ext4Check.err(e))
    case Done{JR.Ext4Recovered{+d, +rep}}:
      do IO<Unit>:
        IO.print("recovered: " ++ Nat.show(JR.Jbd2Report.transactions(rep)) ++ " transactions, " ++ Nat.show(JR.Jbd2Report.replayed(rep)) ++ " blocks, " ++ Nat.show(JR.Jbd2Report.skipped(rep)) ++ " skipped, next " ++ Nat.show(JR.Jbd2Report.next(rep)))
        IO.print("1900 " ++ Ext4Check.block(D.MemDev.read_block(d, 1900n)) ++ ", 1901 " ++ Ext4Check.text_block(D.MemDev.read_block(d, 1901n)) ++ ", 1902 " ++ Ext4Check.block(D.MemDev.read_block(d, 1902n)))

def Ext4Check.fs(+d: D.MemDev) -> Result<&2, &2, E.Ext4Error, S.Ext4Fs>:
  S.Ext4Fs.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, Ext4Check.opts())

def Ext4Check.recover(+d: D.MemDev, r: Result<&2, &2, E.Ext4Error, S.Ext4Fs>) -> Result<&2, &2, E.Ext4Error, JR.Ext4Recovered<D.MemDev>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+fs}:
      JR.Ext4Journal.recover(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~DW.Ext4Dev.mem_write, d, fs, O.Jbd2Options.default())

def Ext4Check.writes() -> List<&2, JW.Jbd2Write>:
  [JW.Jbd2Write{1950n, B.Octets.append(Ext4Check.p("written by Jbd2Write"), B.Octets.zeros(1004n))}, JW.Jbd2Write{1951n, B.Octets.append(B.Octets.of_list([192, 59, 57, 152]), B.Octets.zeros(1020n))}]

def Ext4Check.commit(+d: D.MemDev, r: Result<&2, &2, E.Ext4Error, S.Ext4Fs>) -> Result<&2, &2, E.Ext4Error, JR.Ext4Committed<D.MemDev>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+fs}:
      JR.Ext4Journal.commit(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~DW.Ext4Dev.mem_write, d, fs, O.Jbd2Options.default(), [1952n], Ext4Check.writes())

def Ext4Check.blk(r: Result<&2, &2, E.Ext4Error, B.Octets>) -> B.Octets:
  match r:
    case Done{o}:
      o
    case Fail{e}:
      B.Octets.empty()

def Ext4Check.same(r: Result<&2, &2, E.Ext4Error, B.Octets>, o: B.Octets) -> String:
  match r:
    case Done{x}:
      Bool.show(B.Octets.is_eq(x, o))
    case Fail{e}:
      Ext4Check.err(e)

def Ext4Check.replayed(r: Result<&2, &2, E.Ext4Error, JR.Ext4Recovered<D.MemDev>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(Ext4Check.err(e))
    case Done{JR.Ext4Recovered{+d, +rep}}:
      +direct = DW.Ext4Dev.write_all(~D.MemDev, ~D.MemDev.block_size, ~DW.Ext4Dev.mem_write, Ext4Check.writes(), Done{SM.Ext4Sample.device()}, 1024n)
      do IO<Unit>:
        IO.print("replayed: " ++ Nat.show(JR.Jbd2Report.transactions(rep)) ++ " transaction, " ++ Nat.show(JR.Jbd2Report.replayed(rep)) ++ " blocks, next " ++ Nat.show(JR.Jbd2Report.next(rep)))
        IO.print("1950 as written directly: " ++ Ext4Check.same(DW.Ext4Dev.read_mem(Done{d}, 1950n), Ext4Check.blk(DW.Ext4Dev.read_mem(direct, 1950n))) ++ ", 1951: " ++ Ext4Check.same(DW.Ext4Dev.read_mem(Done{d}, 1951n), Ext4Check.blk(DW.Ext4Dev.read_mem(direct, 1951n))))

def Ext4Check.after_commit(r: Result<&2, &2, E.Ext4Error, JR.Ext4Committed<D.MemDev>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(Ext4Check.err(e))
    case Done{JR.Ext4Committed{+d, sq, n}}:
      do IO<Unit>:
        IO.print("committed: transaction " ++ Nat.show(sq) ++ ", " ++ Nat.show(n) ++ " log blocks; 1950 before replay " ++ Ext4Check.block(D.MemDev.read_block(d, 1950n)))
        Ext4Check.replayed(Ext4Check.recover(d, Ext4Check.fs(d)))


# Corruptions: a flipped byte in a block (at offset k)

def Ext4Check.flip.at(r: Result<&2, &2, D.DevError, B.Octets>, +k: Nat) -> B.Octets:
  match r:
    case Done{+o}:
      B.Octets.append(B.Octets.take(k, o), B.Octets.append(B.Octets.of_list([U32.xor(Maybe.default(&2, U32, B.Octets.at(o, k), 0), 1)]), B.Octets.drop(Nat.add(k, 1n), o)))
    case Fail{e}:
      B.Octets.empty()

def Ext4Check.flip(+d: D.MemDev, +n: Nat, +k: Nat) -> D.MemDev:
  D.MemDev.update(d, n, Ext4Check.flip.at(D.MemDev.read_block(d, n), k))

def Ext4Check.lookup_in(r: Result<&2, &2, E.Ext4Error, S.Ext4Fs>, +d: D.MemDev, s: String) -> String:
  match r:
    case Fail{e}:
      Ext4Check.err(e)
    case Done{+fs}:
      Ext4Check.lookup(d, fs, s)

def Ext4Check.xattr_in(r: Result<&2, &2, E.Ext4Error, S.Ext4Fs>, +d: D.MemDev, s: String, n: String) -> String:
  match r:
    case Fail{e}:
      Ext4Check.err(e)
    case Done{+fs}:
      Ext4Check.data(X4.Ext4.xattr(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext4Check.p(s), Ext4Check.p(n)))

def Ext4Check.fs_unchecked(+d: D.MemDev) -> Result<&2, &2, E.Ext4Error, S.Ext4Fs>:
  S.Ext4Fs.open(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, O.Ext4Options.with_verify(Ext4Check.opts(), False{}))

def Ext4Check.list_in(r: Result<&2, &2, E.Ext4Error, S.Ext4Fs>, +d: D.MemDev, s: String) -> String:
  match r:
    case Fail{e}:
      Ext4Check.err(e)
    case Done{+fs}:
      Ext4Check.count(X4.Ext4.list(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, fs, Ext4Check.p(s)))

def Ext4Check.recover_strict(+d: D.MemDev, r: Result<&2, &2, E.Ext4Error, S.Ext4Fs>) -> Result<&2, &2, E.Ext4Error, JR.Ext4Recovered<D.MemDev>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+fs}:
      JR.Ext4Journal.recover(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~DW.Ext4Dev.mem_write, d, fs, O.Jbd2Options.with_skip_bad_data(O.Jbd2Options.default(), False{}))

def Ext4Check.recovered_short(r: Result<&2, &2, E.Ext4Error, JR.Ext4Recovered<D.MemDev>>) -> String:
  match r:
    case Fail{e}:
      Ext4Check.err(e)
    case Done{JR.Ext4Recovered{d, +rep}}:
      "recovered: " ++ Nat.show(JR.Jbd2Report.transactions(rep)) ++ " transactions, " ++ Nat.show(JR.Jbd2Report.replayed(rep)) ++ " blocks, " ++ Nat.show(JR.Jbd2Report.skipped(rep)) ++ " skipped"

# The htree writer: a directory of 300 names, its root parsed back, and
# lookups in its plan

def Ext4Check.names.go(n: Nat, acc: List<&2, DR.Ext2Dirent>) -> List<&2, DR.Ext2Dirent>:
  match n:
    case 0n:
      acc
    case 1n+k:
      +j = k
      Ext4Check.names.go(j, Con{DR.Ext2Dirent{U32.from_nat(Nat.add(20n, j)), 0, 0, 1, B.Octets.of_string("entry-" ++ Nat.show(j))}, acc})

def Ext4Check.root.of(r: Result<&2, &2, E.Ext4Error, X.Ext4DxRoot>) -> String:
  match r:
    case Fail{e}:
      Ext4Check.err(e)
    case Done{+x}:
      "levels " ++ U32.show(X.Ext4DxRoot.levels(x)) ++ ", " ++ Nat.show(List.length(&2, X.Ext4DxEntry, X.Ext4DxRoot.entries(x))) ++ " entries"

def Ext4Check.root(m: Maybe<&2, B.Octets>) -> String:
  match m:
    case None{}:
      "none"
    case Some{+o}:
      Ext4Check.root.of(X.Ext4DxRoot.parse(o, 1024n, False{}, None{}, 3n, 11n))

def Ext4Check.built(r: Result<&2, &2, E.Ext4Error, List<&2, B.Octets>>) -> String:
  match r:
    case Fail{e}:
      Ext4Check.err(e)
    case Done{+bs}:
      "built " ++ Nat.show(List.length(&2, B.Octets, bs)) ++ " blocks; root " ++ Ext4Check.root(List.head(&2, B.Octets, bs))


def Ext4Check.run(r: Result<&2, &2, E.Ext4Error, S.Ext4Fs>, +d: D.MemDev) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(Ext4Check.err(e))
    case Done{+fs}:
      Ext4Check.reading(d, fs)

def Ext4Check.go_commit(r: Result<&2, &2, E.Ext4Error, JR.Ext4Recovered<D.MemDev>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(Ext4Check.err(e))
    case Done{JR.Ext4Recovered{+d, rep}}:
      Ext4Check.after_commit(Ext4Check.commit(d, Ext4Check.fs(d)))

def Ext4Check.found(m: Maybe<&2, T.Ext4HtEnt>) -> String:
  match m:
    case Some{e}:
      "inode " ++ U32.show(DR.Ext2Dirent.inode(T.Ext4HtEnt.entry(e)))
    case None{}:
      "none"

def Ext4Check.in_plan(+ls: List<&2, T.Ext4HtLeaf>, r: Result<&2, &2, E.Ext4Error, H.Ext4DxHash>, +n: B.Octets) -> String:
  match r:
    case Fail{e}:
      Ext4Check.err(e)
    case Done{+h}:
      +x = U32.to_nat(H.Ext4DxHash.major(h))
      Ext4Check.found(T.Ext4Htree.lookup(ls, x, n)) ++ " (scan: " ++ Ext4Check.found(T.Ext4Htree.scan(ls, n)) ++ ")"

def Ext4Check.planned(r: Result<&2, &2, E.Ext4Error, List<&2, T.Ext4HtEnt>>) -> String:
  match r:
    case Fail{e}:
      Ext4Check.err(e)
    case Done{es}:
      +ls = HW.Ext4Htree.plan(es, 1024n)
      "plan: " ++ Nat.show(List.length(&2, T.Ext4HtLeaf, ls)) ++ " leaves, ordered " ++ Bool.show(T.Ext4Htree.ordered(ls)) ++ "; entry-123: " ++ Ext4Check.in_plan(ls, H.Ext4Hash.name(1, [0, 0, 0, 0], Ext4Check.p("entry-123")), Ext4Check.p("entry-123")) ++ "; entry-300: " ++ Ext4Check.in_plan(ls, H.Ext4Hash.name(1, [0, 0, 0, 0], Ext4Check.p("entry-300")), Ext4Check.p("entry-300"))

# A journalled update: three writes (block 1960 twice) through an overlay,
# committed as one transaction and replayed

def Ext4Check.ov_write(r: Result<&2, &2, E.Ext4Error, OV.Ext4Ov<D.MemDev>>, n: Nat, +s: String) -> Result<&2, &2, E.Ext4Error, OV.Ext4Ov<D.MemDev>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{o}:
      DW.Ext4Dev.lift(OV.Ext4Ov<D.MemDev>, OV.Ext4Ov.write_block(~D.MemDev, ~D.MemDev.block_size, o, n, B.Octets.append(Ext4Check.p(s), B.Octets.zeros(Nat.sub(1024n, String.length(s))))))

def Ext4Check.op(o: OV.Ext4Ov<D.MemDev>) -> Result<&2, &2, E.Ext4Error, OV.Ext4Ov<D.MemDev>>:
  Ext4Check.ov_write(Ext4Check.ov_write(Ext4Check.ov_write(Done{o}, 1960n, "first write, block 1960"), 1961n, "other write, block 1961"), 1960n, "third write, block 1960")

def Ext4Check.transacted(r: Result<&2, &2, E.Ext4Error, JR.Ext4Recovered<D.MemDev>>) -> String:
  match r:
    case Fail{e}:
      Ext4Check.err(e)
    case Done{JR.Ext4Recovered{+d, +rep}}:
      "transact: " ++ Nat.show(JR.Jbd2Report.transactions(rep)) ++ " transaction, " ++ Nat.show(JR.Jbd2Report.replayed(rep)) ++ " blocks; 1960 " ++ Ext4Check.text_block(D.MemDev.read_block(d, 1960n)) ++ ", 1961 " ++ Ext4Check.text_block(D.MemDev.read_block(d, 1961n))

def Ext4Check.transact.go(+d: D.MemDev, r: Result<&2, &2, E.Ext4Error, S.Ext4Fs>) -> Result<&2, &2, E.Ext4Error, JR.Ext4Recovered<D.MemDev>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{+fs}:
      JR.Ext4Journal.transact(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, ~DW.Ext4Dev.mem_write, d, fs, O.Jbd2Options.default(), o => Ext4Check.op(o))

def Ext4Check.transact(+d: D.MemDev, r: Result<&2, &2, E.Ext4Error, JR.Ext4Recovered<D.MemDev>>) -> String:
  match r:
    case Fail{e}:
      Ext4Check.err(e)
    case Done{JR.Ext4Recovered{+d2, rep}}:
      Ext4Check.transacted(Ext4Check.transact.go(d2, Ext4Check.fs(d2)))

def main() -> IO(Unit):
  +d = SM.Ext4Sample.device()
  do IO<Unit>:
    IO.print("== reading")
    Ext4Check.run(Ext4Check.fs(d), d)
    IO.print("== journal")
    Ext4Check.recovered(Ext4Check.recover(d, Ext4Check.fs(d)))
    Ext4Check.go_commit(Ext4Check.recover(d, Ext4Check.fs(d)))
    IO.print(Ext4Check.transact(d, Ext4Check.recover(d, Ext4Check.fs(d))))
    IO.print("== corruptions")
    IO.print(Ext4Check.lookup_in(Ext4Check.fs(d), Ext4Check.flip(d, 1073n, 40n), "/big/f_17"))
    IO.print(Ext4Check.lookup_in(Ext4Check.fs(d), Ext4Check.flip(d, 1073n, 1020n), "/big/f_17"))
    IO.print(Ext4Check.lookup_in(Ext4Check.fs_unchecked(d), Ext4Check.flip(d, 1073n, 1020n), "/big/f_17"))
    IO.print(Ext4Check.list_in(Ext4Check.fs(d), Ext4Check.flip(d, 1074n, 100n), "/big"))
    IO.print(Ext4Check.xattr_in(Ext4Check.fs(d), Ext4Check.flip(d, 1079n, 40n), "/file", "user.mid"))
    IO.print(Ext4Check.recovered_short(Ext4Check.recover(Ext4Check.flip(d, 42n, 600n), Ext4Check.fs(d))))
    IO.print(Ext4Check.recovered_short(Ext4Check.recover(Ext4Check.flip(d, 40n, 600n), Ext4Check.fs(d))))
    IO.print(Ext4Check.recovered_short(Ext4Check.recover(Ext4Check.flip(d, 36n, 600n), Ext4Check.fs(d))))
    IO.print(Ext4Check.recovered_short(Ext4Check.recover_strict(Ext4Check.flip(d, 36n, 600n), Ext4Check.fs(d))))
    IO.print(Ext4Check.recovered_short(Ext4Check.recover(Ext4Check.flip(d, 31n, 100n), Ext4Check.fs(d))))
    IO.print("== htree writer")
    IO.print(Ext4Check.built(HW.Ext4Htree.build(HW.Ext4HtreeParams.default(1024n, 11, 2), Ext4Check.names.go(300n, Nil{}))))
    IO.print(Ext4Check.planned(HW.Ext4Htree.hashed(Ext4Check.names.go(300n, Nil{}), 1, [0, 0, 0, 0], Nil{})))

#|== reading
#|inode 13 file
#|inode 13 file
#|err Ext4NotFound
#|inode 2 dir
#|inode 18 file
#|err Ext4NotDir
#|entries 152
#|ls .:17:2 ..:2:2 a:18:1
#|hi
#|
#|50 bytes, crc32 2892139011
#|100 bytes, crc32 4066859569
#|1500 bytes, crc32 3933421252
#|21 bytes, crc32 2961567277
#|xattrs user.short=5 user.huge=1024 user.mid=300
#|hello
#|300 bytes, crc32 799973505
#|1024 bytes, crc32 2247956107
#|err Ext4NoXattr
#|== journal
#|recovered: 3 transactions, 2 blocks, 0 skipped, next 5
#|1900 4021661486, 1901 second journalled block, 1902 4094723213
#|committed: transaction 5, 5 log blocks; 1950 before replay 4021661486
#|replayed: 1 transaction, 2 blocks, next 7
#|1950 as written directly: True, 1951: True
#|transact: 1 transaction, 2 blocks; 1960 third write, block 1960, 1961 other write, block 1961
#|== corruptions
#|err Ext4BadDxCsum
#|err Ext4BadDxCsum
#|inode 13 file
#|err Ext4Ext2 Ext2BadDirCsum
#|err Ext4BadXattrCsum
#|recovered: 2 transactions, 1 blocks, 0 skipped
#|err Ext4BadLogCsum
#|recovered: 3 transactions, 1 blocks, 1 skipped
#|err Ext4ReplayCsum
#|err Ext4BadJournalCsum
#|== htree writer
#|built 7 blocks; root levels 0, 6 entries
#|plan: 6 leaves, ordered True; entry-123: inode 143 (scan: inode 143); entry-300: none (scan: none)
