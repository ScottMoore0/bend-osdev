# Proofs of LAWS.bend. Written by gen/genproof.py: edit that, not this.
import Base
import ../bytes/bytes.bend as B
import ../blockdev/blockdev.bend as D
import ./error.bend as E
import ./bpb.bend as P
import ./table.bend as T
import ./dirent.bend as R
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./LAWS.bend as Laws

# Equality of words is reflexive (U32.is_eq(a, a) is True for every a)
def word_refl(n: Nat, w: Word(n)) -> {EQ{} == Word.cmp(n, w, w) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{True{}, t}:
          %word_refl(p, t) : {EQ{} == Word.cmp.fin(True{}, True{}, _) : Cmp}
          {==}
        case WCon{False{}, t}:
          %word_refl(p, t) : {EQ{} == Word.cmp.fin(False{}, False{}, _) : Cmp}
          {==}

def u32_refl(a: U32) -> {True{} == U32.is_eq(a, a) : Bool}:
  match a:
    case U32{+x}:
      %word_refl(32n, x) : {True{} == Cmp.is_eq(_) : Bool}
      {==}

def zero_le(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# Directory entries. The encoder writes the 11 name bytes (cut or padded),
# then the fields; the decoder takes 11 bytes, then reads the fields. Going
# through Octets masks every byte (bytes' interface law octets_to_of); the
# name comes back through octets_of_to, and the fields by computing on their
# bits.

def mask_append(a: List<&2, U32>, +b: List<&2, U32>) -> {B.append(B.mask(a), B.mask(b)) == B.mask(B.append(a, b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %mask_append(t, b) : {Con{B.byte(h), B.append(B.mask(t), B.mask(b))} == Con{B.byte(h), _} : List<&2, U32>}
      {==}

def take_fit(n: Nat, +pad: U32, ys: List<&2, U32>, +r: List<&2, U32>) -> {B.mask(P.Fat.fit(n, pad, ys)) == B.take(n, B.append(B.mask(P.Fat.fit(n, pad, ys)), r)) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match ys:
        case Nil{}:
          %take_fit(p, pad, Nil{}, r) : {Con{B.byte(pad), B.mask(P.Fat.fit(p, pad, Nil{}))} == Con{B.byte(pad), _} : List<&2, U32>}
          {==}
        case Con{+h, t}:
          %take_fit(p, pad, t, r) : {Con{B.byte(h), B.mask(P.Fat.fit(p, pad, t))} == Con{B.byte(h), _} : List<&2, U32>}
          {==}

def drop_fit(n: Nat, +pad: U32, ys: List<&2, U32>, +r: List<&2, U32>) -> {r == B.drop(n, B.append(B.mask(P.Fat.fit(n, pad, ys)), r)) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match ys:
        case Nil{}:
          drop_fit(p, pad, Nil{}, r)
        case Con{h, t}:
          drop_fit(p, pad, t, r)

def of_list_mask(+zs: List<&2, U32>) -> {B.Octets.of_list(zs) == B.Octets.of_list(B.mask(zs)) : B.Octets}:
  %BL.octets_to_of(zs) : {B.Octets.of_list(zs) == B.Octets.of_list(_) : B.Octets}
  Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(B.Octets.of_list(zs))), B.Octets.of_list(zs), BL.octets_of_to(B.Octets.of_list(zs)))

# the fields after the name, for every value: split into bits, computed
def dirent_tail(name: B.Octets, nm: B.Octets, attr: U32, nt: U32, tenth: U32, ctime: U32, cdate: U32, adate: U32, hi: U32, wtime: U32, wdate: U32, lo: U32, size: U32) -> {R.FatDirent.decode.rest(nm, B.mask(R.FatDirent.encode.tail(R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}))) == Done{R.FatDirent{nm, B.byte(attr), B.byte(nt), B.byte(tenth), B.low16(ctime), B.low16(cdate), B.low16(adate), B.low16(hi), B.low16(wtime), B.low16(wdate), B.low16(lo), size}} : Result<&2, &2, E.FatError, R.FatDirent>}:
  match attr nt tenth ctime cdate adate hi wtime wdate lo size:
    case U32{WCon{attr_0, WCon{attr_1, WCon{attr_2, WCon{attr_3, WCon{attr_4, WCon{attr_5, WCon{attr_6, WCon{attr_7, WCon{attr_8, WCon{attr_9, WCon{attr_10, WCon{attr_11, WCon{attr_12, WCon{attr_13, WCon{attr_14, WCon{attr_15, WCon{attr_16, WCon{attr_17, WCon{attr_18, WCon{attr_19, WCon{attr_20, WCon{attr_21, WCon{attr_22, WCon{attr_23, WCon{attr_24, WCon{attr_25, WCon{attr_26, WCon{attr_27, WCon{attr_28, WCon{attr_29, WCon{attr_30, WCon{attr_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{nt_0, WCon{nt_1, WCon{nt_2, WCon{nt_3, WCon{nt_4, WCon{nt_5, WCon{nt_6, WCon{nt_7, WCon{nt_8, WCon{nt_9, WCon{nt_10, WCon{nt_11, WCon{nt_12, WCon{nt_13, WCon{nt_14, WCon{nt_15, WCon{nt_16, WCon{nt_17, WCon{nt_18, WCon{nt_19, WCon{nt_20, WCon{nt_21, WCon{nt_22, WCon{nt_23, WCon{nt_24, WCon{nt_25, WCon{nt_26, WCon{nt_27, WCon{nt_28, WCon{nt_29, WCon{nt_30, WCon{nt_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{tenth_0, WCon{tenth_1, WCon{tenth_2, WCon{tenth_3, WCon{tenth_4, WCon{tenth_5, WCon{tenth_6, WCon{tenth_7, WCon{tenth_8, WCon{tenth_9, WCon{tenth_10, WCon{tenth_11, WCon{tenth_12, WCon{tenth_13, WCon{tenth_14, WCon{tenth_15, WCon{tenth_16, WCon{tenth_17, WCon{tenth_18, WCon{tenth_19, WCon{tenth_20, WCon{tenth_21, WCon{tenth_22, WCon{tenth_23, WCon{tenth_24, WCon{tenth_25, WCon{tenth_26, WCon{tenth_27, WCon{tenth_28, WCon{tenth_29, WCon{tenth_30, WCon{tenth_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{ctime_0, WCon{ctime_1, WCon{ctime_2, WCon{ctime_3, WCon{ctime_4, WCon{ctime_5, WCon{ctime_6, WCon{ctime_7, WCon{ctime_8, WCon{ctime_9, WCon{ctime_10, WCon{ctime_11, WCon{ctime_12, WCon{ctime_13, WCon{ctime_14, WCon{ctime_15, WCon{ctime_16, WCon{ctime_17, WCon{ctime_18, WCon{ctime_19, WCon{ctime_20, WCon{ctime_21, WCon{ctime_22, WCon{ctime_23, WCon{ctime_24, WCon{ctime_25, WCon{ctime_26, WCon{ctime_27, WCon{ctime_28, WCon{ctime_29, WCon{ctime_30, WCon{ctime_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{cdate_0, WCon{cdate_1, WCon{cdate_2, WCon{cdate_3, WCon{cdate_4, WCon{cdate_5, WCon{cdate_6, WCon{cdate_7, WCon{cdate_8, WCon{cdate_9, WCon{cdate_10, WCon{cdate_11, WCon{cdate_12, WCon{cdate_13, WCon{cdate_14, WCon{cdate_15, WCon{cdate_16, WCon{cdate_17, WCon{cdate_18, WCon{cdate_19, WCon{cdate_20, WCon{cdate_21, WCon{cdate_22, WCon{cdate_23, WCon{cdate_24, WCon{cdate_25, WCon{cdate_26, WCon{cdate_27, WCon{cdate_28, WCon{cdate_29, WCon{cdate_30, WCon{cdate_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{adate_0, WCon{adate_1, WCon{adate_2, WCon{adate_3, WCon{adate_4, WCon{adate_5, WCon{adate_6, WCon{adate_7, WCon{adate_8, WCon{adate_9, WCon{adate_10, WCon{adate_11, WCon{adate_12, WCon{adate_13, WCon{adate_14, WCon{adate_15, WCon{adate_16, WCon{adate_17, WCon{adate_18, WCon{adate_19, WCon{adate_20, WCon{adate_21, WCon{adate_22, WCon{adate_23, WCon{adate_24, WCon{adate_25, WCon{adate_26, WCon{adate_27, WCon{adate_28, WCon{adate_29, WCon{adate_30, WCon{adate_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{hi_0, WCon{hi_1, WCon{hi_2, WCon{hi_3, WCon{hi_4, WCon{hi_5, WCon{hi_6, WCon{hi_7, WCon{hi_8, WCon{hi_9, WCon{hi_10, WCon{hi_11, WCon{hi_12, WCon{hi_13, WCon{hi_14, WCon{hi_15, WCon{hi_16, WCon{hi_17, WCon{hi_18, WCon{hi_19, WCon{hi_20, WCon{hi_21, WCon{hi_22, WCon{hi_23, WCon{hi_24, WCon{hi_25, WCon{hi_26, WCon{hi_27, WCon{hi_28, WCon{hi_29, WCon{hi_30, WCon{hi_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{wtime_0, WCon{wtime_1, WCon{wtime_2, WCon{wtime_3, WCon{wtime_4, WCon{wtime_5, WCon{wtime_6, WCon{wtime_7, WCon{wtime_8, WCon{wtime_9, WCon{wtime_10, WCon{wtime_11, WCon{wtime_12, WCon{wtime_13, WCon{wtime_14, WCon{wtime_15, WCon{wtime_16, WCon{wtime_17, WCon{wtime_18, WCon{wtime_19, WCon{wtime_20, WCon{wtime_21, WCon{wtime_22, WCon{wtime_23, WCon{wtime_24, WCon{wtime_25, WCon{wtime_26, WCon{wtime_27, WCon{wtime_28, WCon{wtime_29, WCon{wtime_30, WCon{wtime_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{wdate_0, WCon{wdate_1, WCon{wdate_2, WCon{wdate_3, WCon{wdate_4, WCon{wdate_5, WCon{wdate_6, WCon{wdate_7, WCon{wdate_8, WCon{wdate_9, WCon{wdate_10, WCon{wdate_11, WCon{wdate_12, WCon{wdate_13, WCon{wdate_14, WCon{wdate_15, WCon{wdate_16, WCon{wdate_17, WCon{wdate_18, WCon{wdate_19, WCon{wdate_20, WCon{wdate_21, WCon{wdate_22, WCon{wdate_23, WCon{wdate_24, WCon{wdate_25, WCon{wdate_26, WCon{wdate_27, WCon{wdate_28, WCon{wdate_29, WCon{wdate_30, WCon{wdate_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{lo_0, WCon{lo_1, WCon{lo_2, WCon{lo_3, WCon{lo_4, WCon{lo_5, WCon{lo_6, WCon{lo_7, WCon{lo_8, WCon{lo_9, WCon{lo_10, WCon{lo_11, WCon{lo_12, WCon{lo_13, WCon{lo_14, WCon{lo_15, WCon{lo_16, WCon{lo_17, WCon{lo_18, WCon{lo_19, WCon{lo_20, WCon{lo_21, WCon{lo_22, WCon{lo_23, WCon{lo_24, WCon{lo_25, WCon{lo_26, WCon{lo_27, WCon{lo_28, WCon{lo_29, WCon{lo_30, WCon{lo_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{size_0, WCon{size_1, WCon{size_2, WCon{size_3, WCon{size_4, WCon{size_5, WCon{size_6, WCon{size_7, WCon{size_8, WCon{size_9, WCon{size_10, WCon{size_11, WCon{size_12, WCon{size_13, WCon{size_14, WCon{size_15, WCon{size_16, WCon{size_17, WCon{size_18, WCon{size_19, WCon{size_20, WCon{size_21, WCon{size_22, WCon{size_23, WCon{size_24, WCon{size_25, WCon{size_26, WCon{size_27, WCon{size_28, WCon{size_29, WCon{size_30, WCon{size_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.dirent_round_trip(d):
  match d:
    case R.FatDirent{+name, +attr, +nt, +tenth, +ctime, +cdate, +adate, +hi, +wtime, +wdate, +lo, +size}:
      %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.append(P.Fat.fit(11n, 32, B.Octets.to_list(name)), R.FatDirent.encode.tail(R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size})))), B.mask(B.append(P.Fat.fit(11n, 32, B.Octets.to_list(name)), R.FatDirent.encode.tail(R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}))), BL.octets_to_of(B.append(P.Fat.fit(11n, 32, B.Octets.to_list(name)), R.FatDirent.encode.tail(R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size})))) : {R.FatDirent.decode.list(_) == Done{R.FatDirent.norm(R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size})} : Result<&2, &2, E.FatError, R.FatDirent>}
      %mask_append(P.Fat.fit(11n, 32, B.Octets.to_list(name)), R.FatDirent.encode.tail(R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size})) : {R.FatDirent.decode.list(_) == Done{R.FatDirent.norm(R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size})} : Result<&2, &2, E.FatError, R.FatDirent>}
      %take_fit(11n, 32, B.Octets.to_list(name), B.mask(R.FatDirent.encode.tail(R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}))) : {R.FatDirent.decode.rest(B.Octets.of_list(_), B.drop(11n, B.append(B.mask(P.Fat.fit(11n, 32, B.Octets.to_list(name))), B.mask(R.FatDirent.encode.tail(R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}))))) == Done{R.FatDirent.norm(R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size})} : Result<&2, &2, E.FatError, R.FatDirent>}
      %drop_fit(11n, 32, B.Octets.to_list(name), B.mask(R.FatDirent.encode.tail(R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}))) : {R.FatDirent.decode.rest(B.Octets.of_list(B.mask(P.Fat.fit(11n, 32, B.Octets.to_list(name)))), _) == Done{R.FatDirent.norm(R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size})} : Result<&2, &2, E.FatError, R.FatDirent>}
      %of_list_mask(P.Fat.fit(11n, 32, B.Octets.to_list(name))) : {R.FatDirent.decode.rest(_, B.mask(R.FatDirent.encode.tail(R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size}))) == Done{R.FatDirent.norm(R.FatDirent{name, attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size})} : Result<&2, &2, E.FatError, R.FatDirent>}
      dirent_tail(name, B.Octets.of_list(P.Fat.fit(11n, 32, B.Octets.to_list(name))), attr, nt, tenth, ctime, cdate, adate, hi, wtime, wdate, lo, size)

# Long names: every entry build.go makes carries the checksum it was given

def build_carries(+i: Nat, +k: Nat, +name: List<&2, U32>, +c: U32) -> {R.FatLfn.carries(R.FatLfn.build.go(i, k, name, c), c) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      %u32_refl(c) : {Bool.and(_, R.FatLfn.carries(R.FatLfn.build.go(p, k, name, c), c)) == True{} : Bool}
      build_carries(p, k, name, c)

def Laws.lfn_carries_checksum(short, name):
  build_carries(R.FatLfn.count(B.len(name)), R.FatLfn.count(B.len(name)), name, R.FatLfn.checksum(short))

# FAT12 and FAT32 packing, for every value: split into bits, computed
def Laws.fat12_set_get(odd, w, v):
  match odd w v:
    case True{} T.Fat12Window{U32{WCon{a_0, WCon{a_1, WCon{a_2, WCon{a_3, WCon{a_4, WCon{a_5, WCon{a_6, WCon{a_7, WCon{a_8, WCon{a_9, WCon{a_10, WCon{a_11, WCon{a_12, WCon{a_13, WCon{a_14, WCon{a_15, WCon{a_16, WCon{a_17, WCon{a_18, WCon{a_19, WCon{a_20, WCon{a_21, WCon{a_22, WCon{a_23, WCon{a_24, WCon{a_25, WCon{a_26, WCon{a_27, WCon{a_28, WCon{a_29, WCon{a_30, WCon{a_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{b_0, WCon{b_1, WCon{b_2, WCon{b_3, WCon{b_4, WCon{b_5, WCon{b_6, WCon{b_7, WCon{b_8, WCon{b_9, WCon{b_10, WCon{b_11, WCon{b_12, WCon{b_13, WCon{b_14, WCon{b_15, WCon{b_16, WCon{b_17, WCon{b_18, WCon{b_19, WCon{b_20, WCon{b_21, WCon{b_22, WCon{b_23, WCon{b_24, WCon{b_25, WCon{b_26, WCon{b_27, WCon{b_28, WCon{b_29, WCon{b_30, WCon{b_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{v_0, WCon{v_1, WCon{v_2, WCon{v_3, WCon{v_4, WCon{v_5, WCon{v_6, WCon{v_7, WCon{v_8, WCon{v_9, WCon{v_10, WCon{v_11, WCon{v_12, WCon{v_13, WCon{v_14, WCon{v_15, WCon{v_16, WCon{v_17, WCon{v_18, WCon{v_19, WCon{v_20, WCon{v_21, WCon{v_22, WCon{v_23, WCon{v_24, WCon{v_25, WCon{v_26, WCon{v_27, WCon{v_28, WCon{v_29, WCon{v_30, WCon{v_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}
    case False{} T.Fat12Window{U32{WCon{a_0, WCon{a_1, WCon{a_2, WCon{a_3, WCon{a_4, WCon{a_5, WCon{a_6, WCon{a_7, WCon{a_8, WCon{a_9, WCon{a_10, WCon{a_11, WCon{a_12, WCon{a_13, WCon{a_14, WCon{a_15, WCon{a_16, WCon{a_17, WCon{a_18, WCon{a_19, WCon{a_20, WCon{a_21, WCon{a_22, WCon{a_23, WCon{a_24, WCon{a_25, WCon{a_26, WCon{a_27, WCon{a_28, WCon{a_29, WCon{a_30, WCon{a_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, U32{WCon{b_0, WCon{b_1, WCon{b_2, WCon{b_3, WCon{b_4, WCon{b_5, WCon{b_6, WCon{b_7, WCon{b_8, WCon{b_9, WCon{b_10, WCon{b_11, WCon{b_12, WCon{b_13, WCon{b_14, WCon{b_15, WCon{b_16, WCon{b_17, WCon{b_18, WCon{b_19, WCon{b_20, WCon{b_21, WCon{b_22, WCon{b_23, WCon{b_24, WCon{b_25, WCon{b_26, WCon{b_27, WCon{b_28, WCon{b_29, WCon{b_30, WCon{b_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{v_0, WCon{v_1, WCon{v_2, WCon{v_3, WCon{v_4, WCon{v_5, WCon{v_6, WCon{v_7, WCon{v_8, WCon{v_9, WCon{v_10, WCon{v_11, WCon{v_12, WCon{v_13, WCon{v_14, WCon{v_15, WCon{v_16, WCon{v_17, WCon{v_18, WCon{v_19, WCon{v_20, WCon{v_21, WCon{v_22, WCon{v_23, WCon{v_24, WCon{v_25, WCon{v_26, WCon{v_27, WCon{v_28, WCon{v_29, WCon{v_30, WCon{v_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.fat12_even_keeps_odd(a, b, c, v):
  match a b c v:
    case U32{WCon{a_0, WCon{a_1, WCon{a_2, WCon{a_3, WCon{a_4, WCon{a_5, WCon{a_6, WCon{a_7, WCon{a_8, WCon{a_9, WCon{a_10, WCon{a_11, WCon{a_12, WCon{a_13, WCon{a_14, WCon{a_15, WCon{a_16, WCon{a_17, WCon{a_18, WCon{a_19, WCon{a_20, WCon{a_21, WCon{a_22, WCon{a_23, WCon{a_24, WCon{a_25, WCon{a_26, WCon{a_27, WCon{a_28, WCon{a_29, WCon{a_30, WCon{a_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b_0, WCon{b_1, WCon{b_2, WCon{b_3, WCon{b_4, WCon{b_5, WCon{b_6, WCon{b_7, WCon{b_8, WCon{b_9, WCon{b_10, WCon{b_11, WCon{b_12, WCon{b_13, WCon{b_14, WCon{b_15, WCon{b_16, WCon{b_17, WCon{b_18, WCon{b_19, WCon{b_20, WCon{b_21, WCon{b_22, WCon{b_23, WCon{b_24, WCon{b_25, WCon{b_26, WCon{b_27, WCon{b_28, WCon{b_29, WCon{b_30, WCon{b_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{c_0, WCon{c_1, WCon{c_2, WCon{c_3, WCon{c_4, WCon{c_5, WCon{c_6, WCon{c_7, WCon{c_8, WCon{c_9, WCon{c_10, WCon{c_11, WCon{c_12, WCon{c_13, WCon{c_14, WCon{c_15, WCon{c_16, WCon{c_17, WCon{c_18, WCon{c_19, WCon{c_20, WCon{c_21, WCon{c_22, WCon{c_23, WCon{c_24, WCon{c_25, WCon{c_26, WCon{c_27, WCon{c_28, WCon{c_29, WCon{c_30, WCon{c_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{v_0, WCon{v_1, WCon{v_2, WCon{v_3, WCon{v_4, WCon{v_5, WCon{v_6, WCon{v_7, WCon{v_8, WCon{v_9, WCon{v_10, WCon{v_11, WCon{v_12, WCon{v_13, WCon{v_14, WCon{v_15, WCon{v_16, WCon{v_17, WCon{v_18, WCon{v_19, WCon{v_20, WCon{v_21, WCon{v_22, WCon{v_23, WCon{v_24, WCon{v_25, WCon{v_26, WCon{v_27, WCon{v_28, WCon{v_29, WCon{v_30, WCon{v_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.fat12_odd_keeps_even(a, b, c, v):
  match a b c v:
    case U32{WCon{a_0, WCon{a_1, WCon{a_2, WCon{a_3, WCon{a_4, WCon{a_5, WCon{a_6, WCon{a_7, WCon{a_8, WCon{a_9, WCon{a_10, WCon{a_11, WCon{a_12, WCon{a_13, WCon{a_14, WCon{a_15, WCon{a_16, WCon{a_17, WCon{a_18, WCon{a_19, WCon{a_20, WCon{a_21, WCon{a_22, WCon{a_23, WCon{a_24, WCon{a_25, WCon{a_26, WCon{a_27, WCon{a_28, WCon{a_29, WCon{a_30, WCon{a_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b_0, WCon{b_1, WCon{b_2, WCon{b_3, WCon{b_4, WCon{b_5, WCon{b_6, WCon{b_7, WCon{b_8, WCon{b_9, WCon{b_10, WCon{b_11, WCon{b_12, WCon{b_13, WCon{b_14, WCon{b_15, WCon{b_16, WCon{b_17, WCon{b_18, WCon{b_19, WCon{b_20, WCon{b_21, WCon{b_22, WCon{b_23, WCon{b_24, WCon{b_25, WCon{b_26, WCon{b_27, WCon{b_28, WCon{b_29, WCon{b_30, WCon{b_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{c_0, WCon{c_1, WCon{c_2, WCon{c_3, WCon{c_4, WCon{c_5, WCon{c_6, WCon{c_7, WCon{c_8, WCon{c_9, WCon{c_10, WCon{c_11, WCon{c_12, WCon{c_13, WCon{c_14, WCon{c_15, WCon{c_16, WCon{c_17, WCon{c_18, WCon{c_19, WCon{c_20, WCon{c_21, WCon{c_22, WCon{c_23, WCon{c_24, WCon{c_25, WCon{c_26, WCon{c_27, WCon{c_28, WCon{c_29, WCon{c_30, WCon{c_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{v_0, WCon{v_1, WCon{v_2, WCon{v_3, WCon{v_4, WCon{v_5, WCon{v_6, WCon{v_7, WCon{v_8, WCon{v_9, WCon{v_10, WCon{v_11, WCon{v_12, WCon{v_13, WCon{v_14, WCon{v_15, WCon{v_16, WCon{v_17, WCon{v_18, WCon{v_19, WCon{v_20, WCon{v_21, WCon{v_22, WCon{v_23, WCon{v_24, WCon{v_25, WCon{v_26, WCon{v_27, WCon{v_28, WCon{v_29, WCon{v_30, WCon{v_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.fat32_set_get(old, v):
  match old v:
    case U32{WCon{o_0, WCon{o_1, WCon{o_2, WCon{o_3, WCon{o_4, WCon{o_5, WCon{o_6, WCon{o_7, WCon{o_8, WCon{o_9, WCon{o_10, WCon{o_11, WCon{o_12, WCon{o_13, WCon{o_14, WCon{o_15, WCon{o_16, WCon{o_17, WCon{o_18, WCon{o_19, WCon{o_20, WCon{o_21, WCon{o_22, WCon{o_23, WCon{o_24, WCon{o_25, WCon{o_26, WCon{o_27, WCon{o_28, WCon{o_29, WCon{o_30, WCon{o_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{v_0, WCon{v_1, WCon{v_2, WCon{v_3, WCon{v_4, WCon{v_5, WCon{v_6, WCon{v_7, WCon{v_8, WCon{v_9, WCon{v_10, WCon{v_11, WCon{v_12, WCon{v_13, WCon{v_14, WCon{v_15, WCon{v_16, WCon{v_17, WCon{v_18, WCon{v_19, WCon{v_20, WCon{v_21, WCon{v_22, WCon{v_23, WCon{v_24, WCon{v_25, WCon{v_26, WCon{v_27, WCon{v_28, WCon{v_29, WCon{v_30, WCon{v_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

def Laws.fat32_keeps_reserved(old, v):
  match old v:
    case U32{WCon{o_0, WCon{o_1, WCon{o_2, WCon{o_3, WCon{o_4, WCon{o_5, WCon{o_6, WCon{o_7, WCon{o_8, WCon{o_9, WCon{o_10, WCon{o_11, WCon{o_12, WCon{o_13, WCon{o_14, WCon{o_15, WCon{o_16, WCon{o_17, WCon{o_18, WCon{o_19, WCon{o_20, WCon{o_21, WCon{o_22, WCon{o_23, WCon{o_24, WCon{o_25, WCon{o_26, WCon{o_27, WCon{o_28, WCon{o_29, WCon{o_30, WCon{o_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{v_0, WCon{v_1, WCon{v_2, WCon{v_3, WCon{v_4, WCon{v_5, WCon{v_6, WCon{v_7, WCon{v_8, WCon{v_9, WCon{v_10, WCon{v_11, WCon{v_12, WCon{v_13, WCon{v_14, WCon{v_15, WCon{v_16, WCon{v_17, WCon{v_18, WCon{v_19, WCon{v_20, WCon{v_21, WCon{v_22, WCon{v_23, WCon{v_24, WCon{v_25, WCon{v_26, WCon{v_27, WCon{v_28, WCon{v_29, WCon{v_30, WCon{v_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}

# Entry values: per FAT type, computed; a next-cluster value through its
# three hypotheses

def Laws.entry_end(t):
  match t:
    case P.Fat12{}:
      {==}
    case P.Fat16{}:
      {==}
    case P.Fat32{}:
      {==}

def Laws.entry_bad(t):
  match t:
    case P.Fat12{}:
      {==}
    case P.Fat16{}:
      {==}
    case P.Fat32{}:
      {==}

def Laws.entry_free(t):
  match t:
    case P.Fat12{}:
      {==}
    case P.Fat16{}:
      {==}
    case P.Fat32{}:
      {==}

def Laws.entry_next(t, c, nonzero, not_bad, below):
  %Equal.sym(Bool, U32.is_eq(c, 0), False{}, nonzero) : {T.FatEntry.of.pick(_, U32.is_eq(c, T.FatEntry.bad(t)), U32.is_gt(c, T.FatEntry.bad(t)), c) == T.FatNext{c} : T.FatEntry}
  %Equal.sym(Bool, U32.is_eq(c, T.FatEntry.bad(t)), False{}, not_bad) : {T.FatEntry.of.pick(False{}, _, U32.is_gt(c, T.FatEntry.bad(t)), c) == T.FatNext{c} : T.FatEntry}
  %Equal.sym(Bool, U32.is_gt(c, T.FatEntry.bad(t)), False{}, below) : {T.FatEntry.of.pick(False{}, False{}, _, c) == T.FatNext{c} : T.FatEntry}
  {==}

def Laws.entry_next_witness_nonzero():
  {==}

def Laws.entry_next_witness_not_bad(t):
  match t:
    case P.Fat12{}:
      {==}
    case P.Fat16{}:
      {==}
    case P.Fat32{}:
      {==}

def Laws.entry_next_witness_below(t):
  match t:
    case P.Fat12{}:
      {==}
    case P.Fat16{}:
      {==}
    case P.Fat32{}:
      {==}

# The chain bound. Each step of the walk spends one unit of fuel and adds
# one cluster, so a walk with fuel n returns at most n clusters, whatever the
# device answers: induction on the fuel, a case on each answer.

def cons_le(+c: U32, r: Result<&2, &2, E.FatError, List<&2, U32>>, +p: Nat, ih: {Nat.is_le(Laws.chain_count(r), p) == True{} : Bool}) -> {Nat.is_le(Laws.chain_count(T.FatChain.cons(c, r)), 1n+p) == True{} : Bool}:
  match r:
    case Fail{e}:
      {==}
    case Done{cs}:
      ih

def go_bound(+d: D.MemDev, +vol: P.FatVolume, +fuel: Nat, +c: U32, l: Result<&2, &2, E.FatError, T.FatLink>) -> {Nat.is_le(Laws.chain_count(T.FatChain.go(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, vol, fuel, c, l)), fuel) == True{} : Bool}:
  match fuel:
    case 0n:
      {==}
    case 1n+p:
      match l:
        case Fail{e}:
          {==}
        case Done{T.FatLinkEnd{}}:
          zero_le(p)
        case Done{T.FatLinkNext{+n}}:
          cons_le(c, T.FatChain.go(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, vol, p, n, T.FatChain.next(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, vol, n)), p, go_bound(d, vol, p, n, T.FatChain.next(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, vol, n)))

def walk_bound(empty: Bool, ok: Bool, +d: D.MemDev, +vol: P.FatVolume, +start: U32) -> {Nat.is_le(Laws.chain_count(T.FatChain.walk.from(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, empty, ok, d, vol, start)), U32.to_nat(P.FatVolume.clusters(vol))) == True{} : Bool}:
  match empty ok:
    case True{} _:
      zero_le(U32.to_nat(P.FatVolume.clusters(vol)))
    case False{} False{}:
      zero_le(U32.to_nat(P.FatVolume.clusters(vol)))
    case False{} True{}:
      go_bound(d, vol, U32.to_nat(P.FatVolume.clusters(vol)), start, T.FatChain.next(~D.MemDev, ~D.MemDev.block_size, ~D.MemDev.read_block, d, vol, start))

def Laws.chain_bound(d, vol, start):
  walk_bound(U32.is_eq(start, 0), P.FatVolume.valid_cluster(vol, start), d, vol, start)

# Vectors, computed

def Laws.type_fat12_max():
  {==}

def Laws.type_fat16_min():
  {==}

def Laws.type_fat16_max():
  {==}

def Laws.type_fat32_min():
  {==}

def Laws.checksum_bootx64():
  {==}

def Laws.readme_cluster():
  {==}

def Laws.readme_size():
  {==}

def Laws.readme_date():
  {==}

def Laws.readme_time():
  {==}

def Laws.readme_short_entry():
  {==}

def Laws.lfn_build_two():
  {==}

def Laws.lfn_entry_round_trip():
  {==}

def Laws.lfn_not_long():
  {==}

def Laws.short_of_efi():
  {==}

def Laws.short_of_dir():
  {==}

def Laws.short_of_long():
  {==}

def Laws.short_of_two_dots():
  {==}

def Laws.short_of_space():
  {==}

def Laws.fat12_even_vector():
  {==}

def Laws.fat12_odd_vector():
  {==}

def Laws.fat12_set_vector():
  {==}

def Laws.short_text_lower():
  {==}
