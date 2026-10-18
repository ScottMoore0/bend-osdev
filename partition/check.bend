import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ../crc/crc.bend as C
import ../uuid/uuid.bend as U
import ./mbr.bend as M
import ./gpt.bend as G
import ./partition.bend as P

# Sectors of a 4 MiB image made by sgdisk (two partitions, "EFI system" and
# "root ü", the second with attribute bit 2), and of a 2 MiB image made by
# sfdisk (two MBR partitions, the first bootable)

def hdr() -> B.Octets:
  B.Octets.append(B.Octets.of_list([69, 70, 73, 32, 80, 65, 82, 84, 0, 0, 1, 0, 92, 0, 0, 0, 125, 171, 211, 198, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 255, 31, 0, 0, 0, 0, 0, 0, 34, 0, 0, 0, 0, 0, 0, 0, 222, 31, 0, 0, 0, 0, 0, 0, 27, 48, 32, 148, 177, 137, 179, 64, 170, 235, 143, 149, 202, 132, 158, 228, 2, 0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 128, 0, 0, 0, 51, 150, 150, 146]), B.Octets.zeros(420n))

def e0() -> B.Octets:
  B.Octets.of_list([40, 115, 42, 193, 31, 248, 210, 17, 186, 75, 0, 160, 201, 62, 201, 59, 86, 136, 248, 239, 76, 47, 115, 66, 174, 200, 39, 193, 68, 231, 165, 150, 0, 8, 0, 0, 0, 0, 0, 0, 255, 15, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 69, 0, 70, 0, 73, 0, 32, 0, 115, 0, 121, 0, 115, 0, 116, 0, 101, 0, 109, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

def e1() -> B.Octets:
  B.Octets.of_list([175, 61, 198, 15, 131, 132, 114, 71, 142, 121, 61, 105, 216, 71, 125, 228, 64, 142, 189, 113, 138, 228, 60, 79, 141, 124, 86, 114, 81, 126, 239, 140, 0, 16, 0, 0, 0, 0, 0, 0, 222, 31, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 114, 0, 111, 0, 111, 0, 116, 0, 32, 0, 252, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

def pmbr() -> B.Octets:
  B.Octets.append(B.Octets.zeros(440n), B.Octets.of_list([0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 238, 130, 2, 0, 1, 0, 0, 0, 255, 31, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 170]))

def mbr() -> B.Octets:
  B.Octets.append(B.Octets.zeros(440n), B.Octets.of_list([120, 86, 52, 18, 0, 0, 128, 32, 33, 0, 131, 48, 48, 0, 0, 8, 0, 0, 0, 4, 0, 0, 0, 48, 49, 0, 12, 65, 1, 0, 0, 12, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 85, 170]))

def unused(n: Nat) -> List<&2, G.GptEntry>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{G.GptEntry.unused(), unused(p)}

def show_chs(c: M.MbrChs) -> String:
  match c:
    case M.MbrChs{h, s, y}:
      U32.show(h) ++ "/" ++ U32.show(s) ++ "/" ++ U32.show(y)

def show_mbr_entry(e: M.MbrEntry) -> String:
  match e:
    case M.MbrEntry{status, first, os_type, last, lba, sectors}:
      U32.show(status) ++ " " ++ show_chs(first) ++ " " ++ U32.show(os_type) ++ " " ++ show_chs(last) ++ " " ++ U32.show(lba) ++ " " ++ U32.show(sectors)

def show_mbr(r: Result<&2, &2, M.MbrError, M.Mbr>) -> String:
  match r:
    case Done{M.Mbr{sig, p0, p1, p2, p3}}:
      U32.show(sig) ++ " | " ++ show_mbr_entry(p0) ++ " | " ++ show_mbr_entry(p1) ++ " | " ++ show_mbr_entry(p2) ++ " | " ++ show_mbr_entry(p3)
    case Fail{e}:
      "error: " ++ M.MbrError.show(e)

def show_hdr(r: Result<&2, &2, G.GptError, G.GptHeader>) -> String:
  match r:
    case Done{G.GptHeader{rev, size, crc, my, alt, first, last, guid, elba, count, esize, ecrc}}:
      U32.show(rev) ++ " " ++ U32.show(size) ++ " " ++ U32.show(crc) ++ " " ++ W.W64.show(my) ++ " " ++ W.W64.show(alt) ++ " " ++ W.W64.show(first) ++ " " ++ W.W64.show(last) ++ " " ++ U.Uuid.show(guid) ++ " " ++ W.W64.show(elba) ++ " " ++ U32.show(count) ++ " " ++ U32.show(esize) ++ " " ++ U32.show(ecrc)
    case Fail{e}:
      "error: " ++ G.GptError.show(e)

def show_entry.go(e: G.GptEntry) -> String:
  match e:
    case G.GptEntry{t, u, first, last, attr, name}:
      U.Uuid.show(t) ++ " " ++ U.Uuid.show(u) ++ " " ++ W.W64.show(first) ++ " " ++ W.W64.show(last) ++ " " ++ W.W64.show_hex(attr)

def show_entry(r: Result<&2, &2, G.GptError, G.GptEntry>) -> String:
  match r:
    case Done{+e}:
      show_entry.go(e) ++ " '" ++ G.GptEntry.name_text(e) ++ "'"
    case Fail{e}:
      "error: " ++ G.GptError.show(e)

def rebuilt(r: Result<&2, &2, G.GptError, G.GptHeader>) -> String:
  match r:
    case Done{h}:
      Bool.show(B.Octets.is_eq(G.Gpt.build_header(h), hdr()))
    case Fail{e}:
      "error"

def entries2(a: Result<&2, &2, G.GptError, G.GptEntry>, b: Result<&2, &2, G.GptError, G.GptEntry>) -> List<&2, G.GptEntry>:
  match a b:
    case Done{x} Done{y}:
      Con{x, Con{y, unused(126n)}}
    case _ _:
      Nil{}

def from_scratch(a: Result<&2, &2, G.GptError, G.GptEntry>, b: Result<&2, &2, G.GptError, G.GptEntry>, g: Result<&2, &2, U.UuidError, U.Uuid>) -> String:
  match g:
    case Done{guid}:
      Bool.show(B.Octets.is_eq(G.Gpt.build(G.GptHeader.standard(G.GptLayout.standard(), W.W64.from_u32(8192), guid), entries2(a, b)), hdr()))
    case Fail{e}:
      "error"

# A larger table, as a regression test for long inputs: 384 entries (a
# 48 KB array). Entry i: type GUID 0FC63DAF-8483-4772-8E79-3D69D8477DE4
# (Linux data), a unique GUID with i in its first two bytes, LBAs 2048 + 64i
# to 2111 + 64i, the name "part" and i's last digit.
def big.entry(+i: U32) -> G.GptEntry:
  G.GptEntry{U.Uuid.make(15, 198, 61, 175, 132, 131, 71, 114, 142, 121, 61, 105, 216, 71, 125, 228), U.Uuid.make(U32.and(i, 255), U32.shrn(i, 8n), 1, 2, 3, 4, 69, 6, 135, 8, 9, 10, 11, 12, 13, 14), W.W64.from_u32(U32.add(2048, U32.mul(64, i))), W.W64.from_u32(U32.add(2111, U32.mul(64, i))), W.W64.zero(), [112, 97, 114, 116, U32.add(48, U32.mod(i, 10))]}

def big.entries(n: Nat, +i: U32, acc: List<&2, G.GptEntry>) -> List<&2, G.GptEntry>:
  match n:
    case 0n:
      acc
    case 1n+p:
      big.entries(p, U32.sub(i, 1), Con{big.entry(i), acc})

def big.used(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

def big.tally(es: List<&2, G.GptEntry>, n: Nat, used: Nat, last: String) -> String:
  match es:
    case Nil{}:
      Nat.show(n) ++ " entries, " ++ Nat.show(used) ++ " used, last '" ++ last ++ "'"
    case Con{+e, t}:
      big.tally(t, 1n+n, big.used(G.GptEntry.is_used(e), used), G.GptEntry.name_text(e))

def big.show_entries(r: Result<&2, &2, G.GptError, List<&2, G.GptEntry>>) -> String:
  match r:
    case Done{es}:
      big.tally(es, 0n, 0n, "")
    case Fail{e}:
      "error: " ++ G.GptError.show(e)

def big.check(r: Result<&2, &2, G.GptError, G.GptHeader>, +arr: B.Octets) -> String:
  match r:
    case Done{+h}:
      "entries CRC " ++ Bool.show(G.Gpt.entries_crc_ok(h, arr)) ++ ", " ++ big.show_entries(G.Gpt.entries(h, arr))
    case Fail{e}:
      "error: " ++ G.GptError.show(e)

def main() -> IO(Unit):
  +big_es = big.entries(384n, 383, Nil{})
  +big_arr = G.Gpt.entries_encode(big_es)
  +big_hdr = G.Gpt.build(G.GptHeader.standard(G.GptLayout{512, 384}, W.W64.from_u32(1048576), U.Uuid.make(148, 32, 48, 27, 137, 177, 64, 179, 170, 235, 143, 149, 202, 132, 158, 228)), big_es)
  do IO<Unit>:
    IO.print(show_hdr(G.Gpt.parse_header(hdr())))
    IO.print(show_hdr(G.Gpt.validate_header(hdr())))
    IO.print(U32.show(G.Gpt.header_crc(hdr())))
    IO.print(rebuilt(G.Gpt.parse_header(hdr())))
    IO.print(show_entry(G.GptEntry.decode(e0())))
    IO.print(show_entry(G.GptEntry.decode(e1())))
    IO.print(U32.show(C.crc32(G.Gpt.entries_encode(entries2(G.GptEntry.decode(e0()), G.GptEntry.decode(e1()))))))
    IO.print(from_scratch(G.GptEntry.decode(e0()), G.GptEntry.decode(e1()), U.Uuid.parse("9420301B-89B1-40B3-AAEB-8F95CA849EE4")))
    IO.print(show_mbr(M.Mbr.parse(pmbr())))
    IO.print(show_mbr(M.Mbr.parse(mbr())))
    IO.print(Bool.show(B.Octets.is_eq(M.Mbr.build(B.Octets.empty(), M.Mbr.protective(W.W64.from_u32(8191))), pmbr())))
    IO.print(show_mbr(M.Mbr.parse(B.Octets.zeros(512n))))
    IO.print(show_hdr(G.Gpt.parse_header(B.Octets.zeros(512n))))
    IO.print(P.PartitionScheme.show(P.Partition.detect(pmbr(), hdr())))
    IO.print(P.PartitionScheme.show(P.Partition.detect(mbr(), hdr())))
    IO.print(P.PartitionScheme.show(P.Partition.detect(pmbr(), B.Octets.zeros(512n))))
    IO.print("big " ++ Nat.show(B.Octets.len(big_arr)) ++ " bytes, CRC " ++ U32.show(C.crc32(big_arr)) ++ "; " ++ big.check(G.Gpt.validate_header(big_hdr), big_arr))

#|65536 92 3335760765 1 8191 34 8158 9420301b-89b1-40b3-aaeb-8f95ca849ee4 2 128 128 2459342387
#|65536 92 3335760765 1 8191 34 8158 9420301b-89b1-40b3-aaeb-8f95ca849ee4 2 128 128 2459342387
#|3335760765
#|True
#|c12a7328-f81f-11d2-ba4b-00a0c93ec93b eff88856-2f4c-4273-aec8-27c144e7a596 2048 4095 0000000000000000 'EFI system'
#|0fc63daf-8483-4772-8e79-3d69d8477de4 71bd8e40-e48a-4f3c-8d7c-5672517eef8c 4096 8158 0000000000000004 'root ü'
#|2459342387
#|True
#|0 | 0 0/2/0 238 130/2/0 1 8191 | 0 0/0/0 0 0/0/0 0 0 | 0 0/0/0 0 0/0/0 0 0 | 0 0/0/0 0 0/0/0 0 0
#|305419896 | 128 32/33/0 131 48/48/0 2048 1024 | 0 48/49/0 12 65/1/0 3072 1024 | 0 0/0/0 0 0/0/0 0 0 | 0 0/0/0 0 0/0/0 0 0
#|True
#|error: no 0x55AA signature
#|error: no EFI PART signature
#|gpt
#|mbr
#|bad gpt: no EFI PART signature
#|big 49152 bytes, CRC 2414624829; entries CRC True, 384 entries, 384 used, last 'part3'
