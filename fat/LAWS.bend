# Properties, for every input:
#   * a short directory entry reads back as written: decoding the 32 bytes
#     FatDirent.encode writes gives the entry as stored (FatDirent.norm: the
#     name cut or padded with spaces to 11 bytes, 8- and 16-bit fields
#     masked), for every entry;
#   * the long-name entries FatLfn.build writes for a short name all carry
#     that short name's checksum (FatLfn.carries, the check the directory
#     reader makes), for every short name and every long name;
#   * FAT12 packing: setting an entry in its two bytes and reading it back
#     gives its low 12 bits, and leaves the neighbouring entry that shares a
#     byte unchanged, for every value, both bytes and both neighbours;
#   * FAT32 packing: setting an entry gives back its low 28 bits and keeps
#     the reserved high 4 bits;
#   * the meaning of an entry value: the value written for the end of a
#     chain, a bad cluster or a free cluster reads back as that, on every FAT
#     type; and a next-cluster value does when it is neither 0 nor at or
#     above the bad-cluster value (with a witness that this hypothesis holds);
#   * a cluster chain walk never returns more clusters than the volume's
#     count of clusters, for every in-memory device, volume and start;
#   * the allocation table in memory (map.bend): a read after a write gives
#     the value written (masked to the FAT type) and a write changes no
#     other entry; an allocation (a new chain, or a chain extended) takes
#     only clusters that were free, none twice, as many as asked, links them
#     into a chain (each entry the next cluster, the last the end of the
#     chain), and leaves every other entry, so every cluster in use (in any
#     chain) keeps its entry: no cluster joins two chains; freeing makes
#     each cluster of a list free and changes no other entry; cutting a chain
#     ends it there;
#   * a new entry's short name (alias.bend) is never one its directory
#     already has;
#   * a format's layout (format.bend) always passes the reader's checks as
#     a volume of the type asked for, with the count of clusters it says.
#
# Vectors: the FAT type at the cluster counts where it changes, a short-name
# checksum, a hand-built directory entry, a long name's entries, 8.3 forms
# of path components, and FAT12 packing on known bytes; allocations,
# extensions and frees on a small map, short names for new entries, and a
# format. Every law with a hypothesis has a witness that it holds.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./bpb.bend as P
import ./table.bend as T
import ./dirent.bend as R
import ./map.bend as A
import ./alias.bend as L
import ./format.bend as K

# Properties, for every input

law dirent_round_trip:
  for +d: R.FatDirent
  {R.FatDirent.decode(R.FatDirent.encode(d)) == Done{R.FatDirent.norm(d)} : Result<&2, &2, E.FatError, R.FatDirent>}

law lfn_carries_checksum:
  for +short: B.Octets
  for +name: List<&2, U32>
  {R.FatLfn.carries(R.FatLfn.build(short, name), R.FatLfn.checksum(short)) == True{} : Bool}

law fat12_set_get:
  for +odd: Bool
  for +w: T.Fat12Window
  for +v: U32
  {T.Fat12.get(odd, T.Fat12.set(odd, w, v)) == U32.and(4095, v) : U32}

# setting the even entry of bytes a, b leaves the odd entry of b, c
law fat12_even_keeps_odd:
  for +a: U32
  for +b: U32
  for +c: U32
  for +v: U32
  {T.Fat12.get(True{}, T.Fat12Window{T.Fat12Window.second(T.Fat12.set(False{}, T.Fat12Window{a, b}, v)), c}) == T.Fat12.get(True{}, T.Fat12Window{b, c}) : U32}

# setting the odd entry of bytes b, c leaves the even entry of a, b
law fat12_odd_keeps_even:
  for +a: U32
  for +b: U32
  for +c: U32
  for +v: U32
  {T.Fat12.get(False{}, T.Fat12Window{a, T.Fat12Window.first(T.Fat12.set(True{}, T.Fat12Window{b, c}, v))}) == T.Fat12.get(False{}, T.Fat12Window{a, b}) : U32}

law fat32_set_get:
  for +old: U32
  for +v: U32
  {T.Fat32.get(T.Fat32.set(old, v)) == U32.and(268435455, v) : U32}

law fat32_keeps_reserved:
  for +old: U32
  for +v: U32
  {U32.and(4026531840, T.Fat32.set(old, v)) == U32.and(4026531840, old) : U32}

law entry_end:
  for +t: P.FatType
  {T.FatEntry.of(t, T.FatEntry.value(t, T.FatEnd{})) == T.FatEnd{} : T.FatEntry}

law entry_bad:
  for +t: P.FatType
  {T.FatEntry.of(t, T.FatEntry.value(t, T.FatBad{})) == T.FatBad{} : T.FatEntry}

law entry_free:
  for +t: P.FatType
  {T.FatEntry.of(t, T.FatEntry.value(t, T.FatFree{})) == T.FatFree{} : T.FatEntry}

law entry_next:
  for +t: P.FatType
  for +c: U32
  for nonzero: {U32.is_eq(c, 0) == False{} : Bool}
  for not_bad: {U32.is_eq(c, T.FatEntry.bad(t)) == False{} : Bool}
  for below: {U32.is_gt(c, T.FatEntry.bad(t)) == False{} : Bool}
  {T.FatEntry.of(t, T.FatEntry.value(t, T.FatNext{c})) == T.FatNext{c} : T.FatEntry}

# entry_next's hypotheses hold for cluster 2, on every FAT type
law entry_next_witness_nonzero:
  {U32.is_eq(2, 0) == False{} : Bool}

law entry_next_witness_not_bad:
  for +t: P.FatType
  {U32.is_eq(2, T.FatEntry.bad(t)) == False{} : Bool}

law entry_next_witness_below:
  for +t: P.FatType
  {U32.is_gt(2, T.FatEntry.bad(t)) == False{} : Bool}

# the number of clusters a walk returns (0 when it fails)
def chain_count(r: Result<&2, &2, E.FatError, List<&2, U32>>) -> Nat:
  match r:
    case Fail{e}:
      0n
    case Done{cs}:
      List.length(&2, U32, cs)

law chain_bound:
  for +d: D.MemDev
  for +vol: P.FatVolume
  for +start: U32
  {Nat.is_le(chain_count(T.FatChain.walk(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, vol, start)), U32.to_nat(P.FatVolume.clusters(vol))) == True{} : Bool}

# Vectors

# the FAT type is fixed by the count of clusters: 4085 and 65525 are the
# boundaries (section 3.5)
law type_fat12_max:
  {P.FatType.of_clusters(4084) == P.Fat12{} : P.FatType}

law type_fat16_min:
  {P.FatType.of_clusters(4085) == P.Fat16{} : P.FatType}

law type_fat16_max:
  {P.FatType.of_clusters(65524) == P.Fat16{} : P.FatType}

law type_fat32_min:
  {P.FatType.of_clusters(65525) == P.Fat32{} : P.FatType}

# the checksum of "BOOTX64 EFI" (computed by ref/gen.py's implementation)
law checksum_bootx64:
  {R.FatLfn.checksum(B.Octets.of_string("BOOTX64 EFI")) == 29 : U32}

# README.TXT, archive, first cluster 0x00012345, 1234 bytes, written
# 2024-02-29 12:34:56
def readme() -> B.Octets:
  B.Octets.of_list([82, 69, 65, 68, 77, 69, 32, 32, 84, 88, 84, 32, 0, 100, 92, 100, 93, 88, 93, 88, 1, 0, 92, 100, 93, 88, 69, 35, 210, 4, 0, 0])

def readme.cluster(r: Result<&2, &2, E.FatError, R.FatDirent>) -> U32:
  match r:
    case Done{d}:
      R.FatDirent.cluster(d)
    case Fail{e}:
      0

def readme.size(r: Result<&2, &2, E.FatError, R.FatDirent>) -> U32:
  match r:
    case Done{d}:
      R.FatDirent.size(d)
    case Fail{e}:
      0

def readme.date(r: Result<&2, &2, E.FatError, R.FatDirent>) -> R.FatDate:
  match r:
    case Done{d}:
      R.FatDirent.write_date(d)
    case Fail{e}:
      R.FatDate{0, 0, 0}

def readme.time(r: Result<&2, &2, E.FatError, R.FatDirent>) -> R.FatTime:
  match r:
    case Done{d}:
      R.FatDirent.write_time(d)
    case Fail{e}:
      R.FatTime{0, 0, 0}

law readme_cluster:
  {readme.cluster(R.FatDirent.decode(readme())) == 74565 : U32}

law readme_size:
  {readme.size(R.FatDirent.decode(readme())) == 1234 : U32}

law readme_date:
  {readme.date(R.FatDirent.decode(readme())) == R.FatDate{2024, 2, 29} : R.FatDate}

law readme_time:
  {readme.time(R.FatDirent.decode(readme())) == R.FatTime{12, 34, 56} : R.FatTime}

law readme_short_entry:
  {R.FatDirent.decode(B.Octets.take(31n, readme())) == Fail{E.FatTooShort{}} : Result<&2, &2, E.FatError, R.FatDirent>}

# "Long File Name.txt" (18 units) for the short name LONGFI~1.TXT: two
# entries, the second (ordinal 0x42) first, its piece ended by 0x0000 and
# padded with 0xFFFF; checksum 212
law lfn_build_two:
  {R.FatLfn.build(B.Octets.of_string("LONGFI~1TXT"), R.FatName.units("Long File Name.txt")) == [R.FatLfn{66, [101, 46, 116, 120, 116, 0, 65535, 65535, 65535, 65535, 65535, 65535, 65535], 212}, R.FatLfn{1, [76, 111, 110, 103, 32, 70, 105, 108, 101, 32, 78, 97, 109], 212}] : List<&2, R.FatLfn>}

# a long-name entry reads back from its bytes
law lfn_entry_round_trip:
  {R.FatLfn.decode(R.FatLfn.encode(R.FatLfn{66, [101, 46, 116, 120, 116, 0, 65535, 65535, 65535, 65535, 65535, 65535, 65535], 212})) == Done{R.FatLfn{66, [101, 46, 116, 120, 116, 0, 65535, 65535, 65535, 65535, 65535, 65535, 65535], 212}} : Result<&2, &2, E.FatError, R.FatLfn>}

# a short entry is not a long-name entry
law lfn_not_long:
  {R.FatLfn.decode(readme()) == Fail{E.FatNotLongEntry{}} : Result<&2, &2, E.FatError, R.FatLfn>}

# 8.3 forms of path components: upper-cased and padded; refused when they
# cannot be one
law short_of_efi:
  {R.FatName.short_of("bootx64.efi") == Some{B.Octets.of_string("BOOTX64 EFI")} : Maybe<&2, B.Octets>}

law short_of_dir:
  {R.FatName.short_of("Efi") == Some{B.Octets.of_string("EFI        ")} : Maybe<&2, B.Octets>}

law short_of_long:
  {R.FatName.short_of("toolongname.txt") == None{} : Maybe<&2, B.Octets>}

law short_of_two_dots:
  {R.FatName.short_of("a.b.c") == None{} : Maybe<&2, B.Octets>}

law short_of_space:
  {R.FatName.short_of("a b") == None{} : Maybe<&2, B.Octets>}

# FAT12: bytes 0xAB 0xCD hold the even entry 0xDAB and the odd entry 0xCDA
law fat12_even_vector:
  {T.Fat12.get(False{}, T.Fat12Window{171, 205}) == 3499 : U32}

law fat12_odd_vector:
  {T.Fat12.get(True{}, T.Fat12Window{171, 205}) == 3290 : U32}

# setting the even entry to 0x234 changes 0xAB 0xCD to 0x34 0xC2
law fat12_set_vector:
  {T.Fat12.set(False{}, T.Fat12Window{171, 205}, 564) == T.Fat12Window{52, 194} : T.Fat12Window}

# a short name shown with Windows NT's lower-case flags
law short_text_lower:
  {R.FatDirent.short_text(R.FatDirent{B.Octets.of_string("README  TXT"), 32, 24, 0, 0, 0, 0, 0, 0, 0, 0, 0}) == "readme.txt" : String}

# The writer's laws: the allocation table, names, format

def alloc_clusters(r: Result<&2, &2, E.FatError, A.FatAlloc>) -> List<&2, Nat>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{a}:
      A.FatAlloc.clusters(a)

def alloc_map(+m: A.FatMap, r: Result<&2, &2, E.FatError, A.FatAlloc>) -> A.FatMap:
  match r:
    case Fail{e}:
      m
    case Done{a}:
      A.FatAlloc.map(a)

def alloc_size(+k: Nat, r: Result<&2, &2, E.FatError, A.FatAlloc>) -> Nat:
  match r:
    case Fail{e}:
      k
    case Done{a}:
      List.length(&2, Nat, A.FatAlloc.clusters(a))

# after an extension that succeeds, last and the clusters added are a chain
def chain_after(+last: Nat, r: Result<&2, &2, E.FatError, A.FatAlloc>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{A.FatAlloc{m2, cs}}:
      A.FatMap.links(m2, Con{last, cs})

def alias_free(+taken: List<&2, B.Octets>, r: Result<&2, &2, E.FatError, L.FatAlias>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{L.FatAlias{s, nt, long}}:
      Bool.not(L.FatAlias.taken(s, taken))

def fat_same_type(a: P.FatType, b: P.FatType) -> Bool:
  match a b:
    case P.Fat12{} P.Fat12{}:
      True{}
    case P.Fat16{} P.Fat16{}:
      True{}
    case P.Fat32{} P.Fat32{}:
      True{}
    case _ _:
      False{}

def mounts_as(+t: P.FatType, +l: K.FatLayout, r: Result<&2, &2, E.FatError, P.FatVolume>) -> Bool:
  match r:
    case Done{+v}:
      Bool.and(fat_same_type(P.FatVolume.kind(v), t), Nat.is_eq(U32.to_nat(P.FatVolume.clusters(v)), K.FatLayout.clusters(l)))
    case Fail{e}:
      False{}

def mounts_ok(+t: P.FatType, r: Result<&2, &2, E.FatError, K.FatLayout>) -> Bool:
  match r:
    case Fail{e}:
      True{}
    case Done{+l}:
      mounts_as(t, l, P.FatVolume.of_bpb(P.FatOptions.default(), K.FatLayout.bpb(l)))

# a FAT12 map of 6 entries: cluster 3 in use, 2, 4 and 5 free
def map0() -> A.FatMap:
  A.FatMap.of_list(P.Fat12{}, [4088, 4095, 0, 4095, 0, 0])

def alias_short(r: Result<&2, &2, E.FatError, L.FatAlias>) -> B.Octets:
  match r:
    case Fail{e}:
      B.Octets.empty()
    case Done{a}:
      L.FatAlias.short(a)

def alias_long(r: Result<&2, &2, E.FatError, L.FatAlias>) -> List<&2, U32>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{a}:
      L.FatAlias.long(a)

def alias_nt(r: Result<&2, &2, E.FatError, L.FatAlias>) -> U32:
  match r:
    case Fail{e}:
      0
    case Done{a}:
      L.FatAlias.nt(a)

def layout_clusters(r: Result<&2, &2, E.FatError, K.FatLayout>) -> Nat:
  match r:
    case Fail{e}:
      0n
    case Done{l}:
      K.FatLayout.clusters(l)

law map_get_set:
  for +m: A.FatMap
  for +n: Nat
  for +v: U32
  {A.FatMap.get(A.FatMap.set(m, n, v), n) == A.FatMap.mask(A.FatMap.kind(m), v) : U32}

law map_get_set_other:
  for +m: A.FatMap
  for +n: Nat
  for +k: Nat
  for +v: U32
  for ne: {Nat.is_eq(n, k) == False{} : Bool}
  {A.FatMap.get(A.FatMap.set(m, n, v), k) == A.FatMap.get(m, k) : U32}

law alloc_fresh:
  for +m: A.FatMap
  for +hint: Nat
  for +k: Nat
  {A.FatMap.all_free(m, alloc_clusters(A.FatMap.alloc(m, hint, k))) == True{} : Bool}

law alloc_distinct:
  for +m: A.FatMap
  for +hint: Nat
  for +k: Nat
  {A.FatMap.distinct(alloc_clusters(A.FatMap.alloc(m, hint, k))) == True{} : Bool}

law alloc_count:
  for +m: A.FatMap
  for +hint: Nat
  for +k: Nat
  {alloc_size(k, A.FatMap.alloc(m, hint, k)) == k : Nat}

law alloc_links:
  for +m: A.FatMap
  for +hint: Nat
  for +k: Nat
  {A.FatMap.links(alloc_map(m, A.FatMap.alloc(m, hint, k)), alloc_clusters(A.FatMap.alloc(m, hint, k))) == True{} : Bool}

law alloc_frame:
  for +m: A.FatMap
  for +hint: Nat
  for +k: Nat
  for +n: Nat
  for miss: {A.FatMap.member(n, alloc_clusters(A.FatMap.alloc(m, hint, k))) == False{} : Bool}
  {A.FatMap.get(alloc_map(m, A.FatMap.alloc(m, hint, k)), n) == A.FatMap.get(m, n) : U32}

law alloc_keeps_used:
  for +m: A.FatMap
  for +hint: Nat
  for +k: Nat
  for +n: Nat
  for used: {U32.is_eq(A.FatMap.get(m, n), 0) == False{} : Bool}
  {A.FatMap.get(alloc_map(m, A.FatMap.alloc(m, hint, k)), n) == A.FatMap.get(m, n) : U32}

law extend_fresh:
  for +m: A.FatMap
  for +last: Nat
  for +hint: Nat
  for +k: Nat
  {A.FatMap.all_free(m, alloc_clusters(A.FatMap.extend(m, last, hint, k))) == True{} : Bool}

law extend_distinct:
  for +m: A.FatMap
  for +last: Nat
  for +hint: Nat
  for +k: Nat
  {A.FatMap.distinct(alloc_clusters(A.FatMap.extend(m, last, hint, k))) == True{} : Bool}

law extend_count:
  for +m: A.FatMap
  for +last: Nat
  for +hint: Nat
  for +k: Nat
  {alloc_size(k, A.FatMap.extend(m, last, hint, k)) == k : Nat}

law extend_links:
  for +m: A.FatMap
  for +last: Nat
  for +hint: Nat
  for +k: Nat
  for used_last: {A.FatMap.is_free(m, last) == False{} : Bool}
  for pos: {Nat.is_eq(k, 0n) == False{} : Bool}
  {chain_after(last, A.FatMap.extend(m, last, hint, k)) == True{} : Bool}

law extend_frame:
  for +m: A.FatMap
  for +last: Nat
  for +hint: Nat
  for +k: Nat
  for +n: Nat
  for miss: {A.FatMap.member(n, alloc_clusters(A.FatMap.extend(m, last, hint, k))) == False{} : Bool}
  for other: {Nat.is_eq(n, last) == False{} : Bool}
  {A.FatMap.get(alloc_map(m, A.FatMap.extend(m, last, hint, k)), n) == A.FatMap.get(m, n) : U32}

law extend_keeps_used:
  for +m: A.FatMap
  for +last: Nat
  for +hint: Nat
  for +k: Nat
  for +n: Nat
  for used: {U32.is_eq(A.FatMap.get(m, n), 0) == False{} : Bool}
  for other: {Nat.is_eq(n, last) == False{} : Bool}
  {A.FatMap.get(alloc_map(m, A.FatMap.extend(m, last, hint, k)), n) == A.FatMap.get(m, n) : U32}

law free_frees:
  for +m: A.FatMap
  for +cs: List<&2, Nat>
  for +c: Nat
  for hit: {A.FatMap.member(c, cs) == True{} : Bool}
  {A.FatMap.get(A.FatMap.free(cs, m), c) == 0 : U32}

law free_frame:
  for +m: A.FatMap
  for +cs: List<&2, Nat>
  for +c: Nat
  for miss: {A.FatMap.member(c, cs) == False{} : Bool}
  {A.FatMap.get(A.FatMap.free(cs, m), c) == A.FatMap.get(m, c) : U32}

law cut_ends:
  for +m: A.FatMap
  for +c: Nat
  {A.FatMap.get(A.FatMap.cut(m, c), c) == A.FatMap.end(m) : U32}

law alias_fresh:
  for +nt_case: Bool
  for +name: String
  for +taken: List<&2, B.Octets>
  {alias_free(taken, L.FatAlias.make(nt_case, name, taken)) == True{} : Bool}

law format_mounts:
  for +t: P.FatType
  for +tot: Nat
  for +o: K.FatFormatOptions
  {mounts_ok(t, K.FatFormat.layout(t, tot, o)) == True{} : Bool}

law w_ne:
  {Nat.is_eq(2n, 3n) == False{} : Bool}

law v_alloc:
  {alloc_clusters(A.FatMap.alloc(map0(), 2n, 2n)) == [2n, 4n] : List<&2, Nat>}

law v_alloc_map:
  {A.FatMap.entries(alloc_map(map0(), A.FatMap.alloc(map0(), 2n, 2n))) == [4088, 4095, 4, 4095, 4095, 0] : List<&2, U32>}

law v_alloc_hint:
  {alloc_clusters(A.FatMap.alloc(map0(), 5n, 2n)) == [5n, 2n] : List<&2, Nat>}

law v_alloc_full:
  {Result.is_done(&2, &2, E.FatError, A.FatAlloc, A.FatMap.alloc(map0(), 2n, 4n)) == False{} : Bool}

law w_alloc_miss:
  {A.FatMap.member(5n, alloc_clusters(A.FatMap.alloc(map0(), 2n, 2n))) == False{} : Bool}

law w_used:
  {U32.is_eq(A.FatMap.get(map0(), 3n), 0) == False{} : Bool}

law v_extend_map:
  {A.FatMap.entries(alloc_map(map0(), A.FatMap.extend(map0(), 3n, 2n, 1n))) == [4088, 4095, 4095, 2, 0, 0] : List<&2, U32>}

law w_extend_used:
  {A.FatMap.is_free(map0(), 3n) == False{} : Bool}

law w_extend_pos:
  {Nat.is_eq(1n, 0n) == False{} : Bool}

law w_extend_miss:
  {A.FatMap.member(5n, alloc_clusters(A.FatMap.extend(map0(), 3n, 2n, 1n))) == False{} : Bool}

law w_extend_other:
  {Nat.is_eq(5n, 3n) == False{} : Bool}

law w_free_hit:
  {A.FatMap.member(3n, [3n]) == True{} : Bool}

law w_free_miss:
  {A.FatMap.member(2n, [3n]) == False{} : Bool}

law v_free:
  {A.FatMap.entries(A.FatMap.free([3n], map0())) == [4088, 4095, 0, 0, 0, 0] : List<&2, U32>}

law v_alias_tail:
  {alias_short(L.FatAlias.make(False{}, "Long File Name.txt", [])) == B.Octets.of_string("LONGFI~1TXT") : B.Octets}

law v_alias_tail2:
  {alias_short(L.FatAlias.make(False{}, "Long File Name.txt", [B.Octets.of_string("LONGFI~1TXT")])) == B.Octets.of_string("LONGFI~2TXT") : B.Octets}

law v_alias_83:
  {alias_long(L.FatAlias.make(False{}, "README.TXT", [])) == [] : List<&2, U32>}

law v_alias_lower:
  {alias_long(L.FatAlias.make(False{}, "readme.txt", [])) == R.FatName.units("readme.txt") : List<&2, U32>}

law v_alias_nt:
  {alias_nt(L.FatAlias.make(True{}, "readme.txt", [])) == 24 : U32}

law v_alias_lossy:
  {alias_short(L.FatAlias.make(False{}, "a+b=c", [])) == B.Octets.of_string("A_B_C~1    ") : B.Octets}

law v_format12:
  {layout_clusters(K.FatFormat.layout(P.Fat12{}, 64n, K.FatFormatOptions{512, 1, 1, 1, 16, 248, 63, 255, 0, 128, 0, B.Octets.of_string("NO NAME    "), B.Octets.of_string("MSWIN4.1"), 1, 6})) == 61n : Nat}
