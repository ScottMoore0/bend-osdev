import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./hexfield.bend as H
import ./cpio.bend as C
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ./LAWS.bend as Laws

# Lemmas are stated as {value == expression}, the direction a rewrite needs:
# %e : P replaces the expression by the value.

# Hex fields
#
# A nibble's digit reads back as the nibble: 16 cases, each computed. Eight
# digits read back as eight nibbles, so a field reads back as its value once
# the value is split into its 32 bits.

def nib(n: Word(4n)) -> {Some{n} == H.nibble.decode(B.byte(H.nibble.encode(n))) : Maybe<&2, Word(4n)>}:
  match n:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}:
      {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}:
      {==}

def join8(n0: Word(4n), n1: Word(4n), n2: Word(4n), n3: Word(4n), n4: Word(4n), n5: Word(4n), n6: Word(4n), n7: Word(4n)) -> {Some{U32{W.W64.bits.cat(4n, 28n, n0, W.W64.bits.cat(4n, 24n, n1, W.W64.bits.cat(4n, 20n, n2, W.W64.bits.cat(4n, 16n, n3, W.W64.bits.cat(4n, 12n, n4, W.W64.bits.cat(4n, 8n, n5, W.W64.bits.cat(4n, 4n, n6, n7)))))))}} == H.field.join(H.nibble.decode(B.byte(H.nibble.encode(n7))), H.nibble.decode(B.byte(H.nibble.encode(n6))), H.nibble.decode(B.byte(H.nibble.encode(n5))), H.nibble.decode(B.byte(H.nibble.encode(n4))), H.nibble.decode(B.byte(H.nibble.encode(n3))), H.nibble.decode(B.byte(H.nibble.encode(n2))), H.nibble.decode(B.byte(H.nibble.encode(n1))), H.nibble.decode(B.byte(H.nibble.encode(n0)))) : Maybe<&2, U32>}:
  %nib(n7) : {Some{U32{W.W64.bits.cat(4n, 28n, n0, W.W64.bits.cat(4n, 24n, n1, W.W64.bits.cat(4n, 20n, n2, W.W64.bits.cat(4n, 16n, n3, W.W64.bits.cat(4n, 12n, n4, W.W64.bits.cat(4n, 8n, n5, W.W64.bits.cat(4n, 4n, n6, n7)))))))}} == H.field.join(_, H.nibble.decode(B.byte(H.nibble.encode(n6))), H.nibble.decode(B.byte(H.nibble.encode(n5))), H.nibble.decode(B.byte(H.nibble.encode(n4))), H.nibble.decode(B.byte(H.nibble.encode(n3))), H.nibble.decode(B.byte(H.nibble.encode(n2))), H.nibble.decode(B.byte(H.nibble.encode(n1))), H.nibble.decode(B.byte(H.nibble.encode(n0)))) : Maybe<&2, U32>}
  %nib(n6) : {Some{U32{W.W64.bits.cat(4n, 28n, n0, W.W64.bits.cat(4n, 24n, n1, W.W64.bits.cat(4n, 20n, n2, W.W64.bits.cat(4n, 16n, n3, W.W64.bits.cat(4n, 12n, n4, W.W64.bits.cat(4n, 8n, n5, W.W64.bits.cat(4n, 4n, n6, n7)))))))}} == H.field.join(Some{n7}, _, H.nibble.decode(B.byte(H.nibble.encode(n5))), H.nibble.decode(B.byte(H.nibble.encode(n4))), H.nibble.decode(B.byte(H.nibble.encode(n3))), H.nibble.decode(B.byte(H.nibble.encode(n2))), H.nibble.decode(B.byte(H.nibble.encode(n1))), H.nibble.decode(B.byte(H.nibble.encode(n0)))) : Maybe<&2, U32>}
  %nib(n5) : {Some{U32{W.W64.bits.cat(4n, 28n, n0, W.W64.bits.cat(4n, 24n, n1, W.W64.bits.cat(4n, 20n, n2, W.W64.bits.cat(4n, 16n, n3, W.W64.bits.cat(4n, 12n, n4, W.W64.bits.cat(4n, 8n, n5, W.W64.bits.cat(4n, 4n, n6, n7)))))))}} == H.field.join(Some{n7}, Some{n6}, _, H.nibble.decode(B.byte(H.nibble.encode(n4))), H.nibble.decode(B.byte(H.nibble.encode(n3))), H.nibble.decode(B.byte(H.nibble.encode(n2))), H.nibble.decode(B.byte(H.nibble.encode(n1))), H.nibble.decode(B.byte(H.nibble.encode(n0)))) : Maybe<&2, U32>}
  %nib(n4) : {Some{U32{W.W64.bits.cat(4n, 28n, n0, W.W64.bits.cat(4n, 24n, n1, W.W64.bits.cat(4n, 20n, n2, W.W64.bits.cat(4n, 16n, n3, W.W64.bits.cat(4n, 12n, n4, W.W64.bits.cat(4n, 8n, n5, W.W64.bits.cat(4n, 4n, n6, n7)))))))}} == H.field.join(Some{n7}, Some{n6}, Some{n5}, _, H.nibble.decode(B.byte(H.nibble.encode(n3))), H.nibble.decode(B.byte(H.nibble.encode(n2))), H.nibble.decode(B.byte(H.nibble.encode(n1))), H.nibble.decode(B.byte(H.nibble.encode(n0)))) : Maybe<&2, U32>}
  %nib(n3) : {Some{U32{W.W64.bits.cat(4n, 28n, n0, W.W64.bits.cat(4n, 24n, n1, W.W64.bits.cat(4n, 20n, n2, W.W64.bits.cat(4n, 16n, n3, W.W64.bits.cat(4n, 12n, n4, W.W64.bits.cat(4n, 8n, n5, W.W64.bits.cat(4n, 4n, n6, n7)))))))}} == H.field.join(Some{n7}, Some{n6}, Some{n5}, Some{n4}, _, H.nibble.decode(B.byte(H.nibble.encode(n2))), H.nibble.decode(B.byte(H.nibble.encode(n1))), H.nibble.decode(B.byte(H.nibble.encode(n0)))) : Maybe<&2, U32>}
  %nib(n2) : {Some{U32{W.W64.bits.cat(4n, 28n, n0, W.W64.bits.cat(4n, 24n, n1, W.W64.bits.cat(4n, 20n, n2, W.W64.bits.cat(4n, 16n, n3, W.W64.bits.cat(4n, 12n, n4, W.W64.bits.cat(4n, 8n, n5, W.W64.bits.cat(4n, 4n, n6, n7)))))))}} == H.field.join(Some{n7}, Some{n6}, Some{n5}, Some{n4}, Some{n3}, _, H.nibble.decode(B.byte(H.nibble.encode(n1))), H.nibble.decode(B.byte(H.nibble.encode(n0)))) : Maybe<&2, U32>}
  %nib(n1) : {Some{U32{W.W64.bits.cat(4n, 28n, n0, W.W64.bits.cat(4n, 24n, n1, W.W64.bits.cat(4n, 20n, n2, W.W64.bits.cat(4n, 16n, n3, W.W64.bits.cat(4n, 12n, n4, W.W64.bits.cat(4n, 8n, n5, W.W64.bits.cat(4n, 4n, n6, n7)))))))}} == H.field.join(Some{n7}, Some{n6}, Some{n5}, Some{n4}, Some{n3}, Some{n2}, _, H.nibble.decode(B.byte(H.nibble.encode(n0)))) : Maybe<&2, U32>}
  %nib(n0) : {Some{U32{W.W64.bits.cat(4n, 28n, n0, W.W64.bits.cat(4n, 24n, n1, W.W64.bits.cat(4n, 20n, n2, W.W64.bits.cat(4n, 16n, n3, W.W64.bits.cat(4n, 12n, n4, W.W64.bits.cat(4n, 8n, n5, W.W64.bits.cat(4n, 4n, n6, n7)))))))}} == H.field.join(Some{n7}, Some{n6}, Some{n5}, Some{n4}, Some{n3}, Some{n2}, Some{n1}, _) : Maybe<&2, U32>}
  {==}

# a field's digits, as Octets.to_list gives them back, read as the field
def field_rt(v: U32) -> {Some{v} == H.field.decode(B.Octets.to_list(B.Octets.of_list(H.field.encode(v)))) : Maybe<&2, U32>}:
  match v:
    case U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      join8(WCon{b0, WCon{b1, WCon{b2, WCon{b3, WNil{}}}}}, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WNil{}}}}}, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WNil{}}}}}, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WNil{}}}}}, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WNil{}}}}}, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WNil{}}}}}, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}})

def Laws.hexfield_round_trip(v):
  Equal.sym(Maybe<&2, U32>, Some{v}, H.hexfield_decode(H.hexfield_encode(v)), field_rt(v))

# Header fields: each field's digits, then the rest
def masked_onto(vs: List<&2, U32>, rest: List<&2, U32>) -> List<&2, U32>:
  match vs:
    case Nil{}:
      rest
    case Con{v, t}:
      B.append(B.Octets.to_list(B.Octets.of_list(H.field.encode(v))), masked_onto(t, rest))

def fields_rt(vs: List<&2, U32>, rest: List<&2, U32>) -> {Done{C.CpioFields{vs, rest}} == C.fields.take(List.length(&2, U32, vs), masked_onto(vs, rest)) : Result<&2, &2, C.CpioError, C.CpioFields>}:
  match vs:
    case Nil{}:
      {==}
    case Con{v, t}:
      match v:
        case U32{w}:
          %field_rt(U32{w}) : {Done{C.CpioFields{Con{U32{w}, t}, rest}} == C.fields.cons(_, C.fields.take(List.length(&2, U32, t), masked_onto(t, rest))) : Result<&2, &2, C.CpioError, C.CpioFields>}
          %fields_rt(t, rest) : {Done{C.CpioFields{Con{U32{w}, t}, rest}} == C.fields.cons(Some{U32{w}}, _) : Result<&2, &2, C.CpioError, C.CpioFields>}
          {==}

# A header's bytes, then rest, read back as the header and rest. Matching each
# field as U32{w} makes the 110 bytes a list of known length.
def hdr_rt(h: C.CpioHeader, rest: List<&2, U32>) -> {Done{C.CpioHdrRest{h, rest}} == C.hdr.decode(B.append(B.Octets.to_list(C.CpioHeader.encode(h)), rest)) : Result<&2, &2, C.CpioError, C.CpioHdrRest>}:
  match h:
    case C.CpioHeader{C.CpioNewc{}, U32{w0}, U32{w1}, U32{w2}, U32{w3}, U32{w4}, U32{w5}, U32{w6}, U32{w7}, U32{w8}, U32{w9}, U32{w10}, U32{w11}, U32{w12}}:
      %fields_rt([U32{w0}, U32{w1}, U32{w2}, U32{w3}, U32{w4}, U32{w5}, U32{w6}, U32{w7}, U32{w8}, U32{w9}, U32{w10}, U32{w11}, U32{w12}], rest) : {Done{C.CpioHdrRest{C.CpioHeader{C.CpioNewc{}, U32{w0}, U32{w1}, U32{w2}, U32{w3}, U32{w4}, U32{w5}, U32{w6}, U32{w7}, U32{w8}, U32{w9}, U32{w10}, U32{w11}, U32{w12}}, rest}} == C.hdr.decode.go(True{}, Some{C.CpioNewc{}}, _) : Result<&2, &2, C.CpioError, C.CpioHdrRest>}
      {==}
    case C.CpioHeader{C.CpioCrc{}, U32{w0}, U32{w1}, U32{w2}, U32{w3}, U32{w4}, U32{w5}, U32{w6}, U32{w7}, U32{w8}, U32{w9}, U32{w10}, U32{w11}, U32{w12}}:
      %fields_rt([U32{w0}, U32{w1}, U32{w2}, U32{w3}, U32{w4}, U32{w5}, U32{w6}, U32{w7}, U32{w8}, U32{w9}, U32{w10}, U32{w11}, U32{w12}], rest) : {Done{C.CpioHdrRest{C.CpioHeader{C.CpioCrc{}, U32{w0}, U32{w1}, U32{w2}, U32{w3}, U32{w4}, U32{w5}, U32{w6}, U32{w7}, U32{w8}, U32{w9}, U32{w10}, U32{w11}, U32{w12}}, rest}} == C.hdr.decode.go(True{}, Some{C.CpioCrc{}}, _) : Result<&2, &2, C.CpioError, C.CpioHdrRest>}
      {==}

def append_nil(xs: List<&2, U32>) -> {B.append(xs, Nil{}) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %append_nil(t) : {Con{h, B.append(t, Nil{})} == Con{h, _} : List<&2, U32>}
      {==}

def Laws.header_round_trip(h):
  %append_nil(B.Octets.to_list(C.CpioHeader.encode(h))) : {C.CpioHeader.decode.pub(C.hdr.decode(_)) == Done{C.CpioHeaderAt{h, B.Octets.empty()}} : Result<&2, &2, C.CpioError, C.CpioHeaderAt>}
  %hdr_rt(h, Nil{}) : {C.CpioHeader.decode.pub(_) == Done{C.CpioHeaderAt{h, B.Octets.empty()}} : Result<&2, &2, C.CpioError, C.CpioHeaderAt>}
  {==}

# Sizes: a length below 2^32 survives its 32-bit field. nat.bits writes n's
# bits from the bottom (its parity, then half of it); reading them back
# rebuilds n once its high part is zero.

def rec(b: Bool, h: Nat) -> Nat:
  match b:
    case False{}:
      Nat.double(h)
    case True{}:
      1n+Nat.double(h)

def tn_con(+p: Nat, +b: Bool, +t: Word(p)) -> {rec(b, Word.to_nat(p, t)) == Word.to_nat(1n+p, WCon{b, t}) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def rc_succ(+b: Bool, +h: Nat) -> {1n+1n+rec(b, h) == rec(b, 1n+h) : Nat}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def decomp(+n: Nat) -> {n == rec(C.nat.odd(n), C.nat.half(n)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          %rc_succ(C.nat.odd(q), C.nat.half(q)) : {1n+1n+q == _ : Nat}
          %decomp(q) : {1n+1n+q == 1n+1n+_ : Nat}
          {==}

def bits_rt(+k: Nat, +n: Nat, e: {C.nat.high(k, n) == 0n : Nat}) -> {n == Word.to_nat(k, C.nat.bits(k, n)) : Nat}:
  match k:
    case 0n:
      e
    case 1n+p:
      %tn_con(p, C.nat.odd(n), C.nat.bits(p, C.nat.half(n))) : {n == _ : Nat}
      %bits_rt(p, C.nat.half(n), e) : {n == rec(C.nat.odd(n), _) : Nat}
      decomp(n)

def size_rt(+n: Nat, e: {C.size.over(n) == 0n : Nat}) -> {n == U32.to_nat(C.size32(n)) : Nat}:
  bits_rt(32n, n, e)

# Byte lists

def split_rt(+a: List<&2, U32>, +b: List<&2, U32>) -> {Some{C.CpioCut{a, b}} == C.split(B.len(a), B.append(a, b)) : Maybe<&2, C.CpioCut>}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %split_rt(t, b) : {Some{C.CpioCut{Con{h, t}, b}} == C.split.cons(h, _) : Maybe<&2, C.CpioCut>}
      {==}

def skip_rt(+n: Nat, +b: List<&2, U32>) -> {Some{b} == C.skip(n, B.append(B.zeros(n), b)) : Maybe<&2, List<&2, U32>>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      skip_rt(p, b)

# every word compares equal to itself
def fin_eq(+b: Bool) -> {EQ{} == Word.cmp.fin(b, b, EQ{}) : Cmp}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

def cmp_self(+n: Nat, +x: Word(n)) -> {EQ{} == Word.cmp(n, x, x) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match x:
        case WCon{b, t}:
          %cmp_self(p, t) : {EQ{} == Word.cmp.fin(b, b, _) : Cmp}
          fin_eq(b)

def eq_self(+x: U32) -> {True{} == U32.is_eq(x, x) : Bool}:
  match x:
    case U32{w}:
      %cmp_self(32n, w) : {True{} == Cmp.is_eq(_) : Bool}
      {==}

# An impossible length

def disc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def disc_lemma(p: Nat, e: {1n+p == 0n : Nat}) -> Empty:
  %e : disc(_)
  Unit{}

def sub_succ(+l: Nat, +x: Nat, e: {Nat.sub(l, x) == 0n : Nat}) -> {Nat.sub(l, 1n+x) == 0n : Nat}:
  match l x:
    case 0n _:
      {==}
    case 1n+lp 0n:
      Empty.absurd({Nat.sub(1n+lp, 1n) == 0n : Nat}, disc_lemma(lp, e))
    case 1n+lp 1n+xp:
      sub_succ(lp, xp, e)

def mono_append(+a: List<&2, U32>, +l: Nat, +x: List<&2, U32>, e: {Nat.sub(l, B.len(x)) == 0n : Nat}) -> {Nat.sub(l, B.len(B.append(a, x))) == 0n : Nat}:
  match a:
    case Nil{}:
      e
    case Con{h, t}:
      sub_succ(l, B.len(B.append(t, x)), mono_append(t, l, x, e))

# Octets to lists: bytes' interface law, in the direction rewrites use
def al(+a: B.Octets, +b: B.Octets) -> {B.append(B.Octets.to_list(a), B.Octets.to_list(b)) == B.Octets.to_list(B.Octets.append(a, b)) : List<&2, U32>}:
  Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(a, b)), B.append(B.Octets.to_list(a), B.Octets.to_list(b)), BL.octets_append_list(a, b))

# The list an entry's bytes give, then the list r
def lvstep(+fmt: C.CpioFormat, e: C.CpioEntry, +r: List<&2, U32>) -> List<&2, U32>:
  match e:
    case C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, +name, +data}:
      B.append(B.Octets.to_list(C.CpioHeader.encode(C.CpioHeader{fmt, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(fmt, data)})), B.append(B.Octets.to_list(name), Con{0, B.append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)))}))

# the list an archive's bytes give
def lv(+fmt: C.CpioFormat, es: List<&2, C.CpioEntry>) -> List<&2, U32>:
  match es:
    case Nil{}:
      B.Octets.to_list(C.Cpio.build(fmt, Nil{}))
    case Con{e, t}:
      lvstep(fmt, e, lv(fmt, t))

# Through bytes' interface law, an entry's Octets give that list
def vstep(+fmt: C.CpioFormat, +e: C.CpioEntry, +rb: B.Octets) -> {lvstep(fmt, e, B.Octets.to_list(rb)) == B.Octets.to_list(C.entry.onto(fmt, e, rb)) : List<&2, U32>}:
  match e:
    case C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, +name, +data}:
      %al(C.CpioHeader.encode(C.CpioHeader{fmt, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(fmt, data)}), B.Octets.append(name, B.Octets.append(B.Octets.cons(0, B.Octets.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name)))))), B.Octets.append(data, B.Octets.append(B.Octets.zeros(C.pad4(B.len(B.Octets.to_list(data)))), rb))))) : {lvstep(fmt, C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, name, data}, B.Octets.to_list(rb)) == _ : List<&2, U32>}
      %al(name, B.Octets.append(B.Octets.cons(0, B.Octets.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name)))))), B.Octets.append(data, B.Octets.append(B.Octets.zeros(C.pad4(B.len(B.Octets.to_list(data)))), rb)))) : {lvstep(fmt, C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, name, data}, B.Octets.to_list(rb)) == B.append(B.Octets.to_list(C.CpioHeader.encode(C.CpioHeader{fmt, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(fmt, data)})), _) : List<&2, U32>}
      %al(B.Octets.cons(0, B.Octets.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name)))))), B.Octets.append(data, B.Octets.append(B.Octets.zeros(C.pad4(B.len(B.Octets.to_list(data)))), rb))) : {lvstep(fmt, C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, name, data}, B.Octets.to_list(rb)) == B.append(B.Octets.to_list(C.CpioHeader.encode(C.CpioHeader{fmt, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(fmt, data)})), B.append(B.Octets.to_list(name), _)) : List<&2, U32>}
      %al(data, B.Octets.append(B.Octets.zeros(C.pad4(B.len(B.Octets.to_list(data)))), rb)) : {lvstep(fmt, C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, name, data}, B.Octets.to_list(rb)) == B.append(B.Octets.to_list(C.CpioHeader.encode(C.CpioHeader{fmt, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(fmt, data)})), B.append(B.Octets.to_list(name), B.append(B.Octets.to_list(B.Octets.cons(0, B.Octets.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))))), _))) : List<&2, U32>}
      %al(B.Octets.zeros(C.pad4(B.len(B.Octets.to_list(data)))), rb) : {lvstep(fmt, C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, name, data}, B.Octets.to_list(rb)) == B.append(B.Octets.to_list(C.CpioHeader.encode(C.CpioHeader{fmt, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(fmt, data)})), B.append(B.Octets.to_list(name), B.append(B.Octets.to_list(B.Octets.cons(0, B.Octets.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))))), B.append(B.Octets.to_list(data), _)))) : List<&2, U32>}
      {==}

def vlist(+fmt: C.CpioFormat, +es: List<&2, C.CpioEntry>) -> {lv(fmt, es) == B.Octets.to_list(C.Cpio.build(fmt, es)) : List<&2, U32>}:
  match es:
    case Nil{}:
      {==}
    case Con{e, t}:
      %vstep(fmt, e, C.Cpio.build(fmt, t)) : {lvstep(fmt, e, lv(fmt, t)) == _ : List<&2, U32>}
      %vlist(fmt, t) : {lvstep(fmt, e, lv(fmt, t)) == lvstep(fmt, e, _) : List<&2, U32>}
      {==}

# One entry reads back: the header, the name and its NUL (whose size field
# survives), not the trailer, the padding, the data, its padding, and the
# check; and the entry's Octets are its own (canonical).
def entry_rt(+fmt: C.CpioFormat, +e: C.CpioEntry, +r: List<&2, U32>, ok: C.CpioEntry.valid(e)) -> {C.CpioStepEntry{e, r} == C.entry.read(lvstep(fmt, e, r)) : C.CpioStep}:
  match fmt e:
    case C.CpioNewc{} C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, +name, +data}:
      (okd, ok1) = ok
      (okn, ok2) = ok1
      (okt, ok3) = ok2
      (okcn, okcd) = ok3
      %okcn : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, _, data}, r} == C.entry.read(B.append(B.Octets.to_list(C.CpioHeader.encode(C.CpioHeader{C.CpioNewc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioNewc{}, data)})), B.append(B.Octets.to_list(name), Con{0, B.append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)))}))) : C.CpioStep}
      %okcd : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), _}, r} == C.entry.read(B.append(B.Octets.to_list(C.CpioHeader.encode(C.CpioHeader{C.CpioNewc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioNewc{}, data)})), B.append(B.Octets.to_list(name), Con{0, B.append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)))}))) : C.CpioStep}
      %hdr_rt(C.CpioHeader{C.CpioNewc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioNewc{}, data)}, B.append(B.Octets.to_list(name), Con{0, B.append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)))})) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r1(_) : C.CpioStep}
      %size_rt(1n+B.len(B.Octets.to_list(name)), okn) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r2(_, C.CpioHeader{C.CpioNewc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioNewc{}, data)}, B.append(B.Octets.to_list(name), Con{0, B.append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)))})) : C.CpioStep}
      %split_rt(B.Octets.to_list(name), Con{0, B.append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)))}) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r3(_, B.len(B.Octets.to_list(name)), C.CpioHeader{C.CpioNewc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioNewc{}, data)}) : C.CpioStep}
      %Equal.sym(Bool, C.Cpio.is_trailer_name(name), False{}, okt) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r6(_, B.Octets.to_list(name), B.len(B.Octets.to_list(name)), C.CpioHeader{C.CpioNewc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioNewc{}, data)}, B.append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)))) : C.CpioStep}
      %skip_rt(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name)))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r))) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r7(_, B.Octets.to_list(name), C.CpioHeader{C.CpioNewc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioNewc{}, data)}) : C.CpioStep}
      %size_rt(B.len(B.Octets.to_list(data)), okd) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r8(C.split(_, B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r))), B.Octets.to_list(name), C.CpioHeader{C.CpioNewc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioNewc{}, data)}) : C.CpioStep}
      %split_rt(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r8(_, B.Octets.to_list(name), C.CpioHeader{C.CpioNewc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioNewc{}, data)}) : C.CpioStep}
      %skip_rt(C.pad4(B.len(B.Octets.to_list(data))), r) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r9(_, B.Octets.to_list(name), B.Octets.to_list(data), C.CpioHeader{C.CpioNewc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioNewc{}, data)}) : C.CpioStep}
      {==}
    case C.CpioCrc{} C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, +name, +data}:
      (okd, ok1) = ok
      (okn, ok2) = ok1
      (okt, ok3) = ok2
      (okcn, okcd) = ok3
      %okcn : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, _, data}, r} == C.entry.read(B.append(B.Octets.to_list(C.CpioHeader.encode(C.CpioHeader{C.CpioCrc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioCrc{}, data)})), B.append(B.Octets.to_list(name), Con{0, B.append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)))}))) : C.CpioStep}
      %okcd : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), _}, r} == C.entry.read(B.append(B.Octets.to_list(C.CpioHeader.encode(C.CpioHeader{C.CpioCrc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioCrc{}, data)})), B.append(B.Octets.to_list(name), Con{0, B.append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)))}))) : C.CpioStep}
      %hdr_rt(C.CpioHeader{C.CpioCrc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioCrc{}, data)}, B.append(B.Octets.to_list(name), Con{0, B.append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)))})) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r1(_) : C.CpioStep}
      %size_rt(1n+B.len(B.Octets.to_list(name)), okn) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r2(_, C.CpioHeader{C.CpioCrc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioCrc{}, data)}, B.append(B.Octets.to_list(name), Con{0, B.append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)))})) : C.CpioStep}
      %split_rt(B.Octets.to_list(name), Con{0, B.append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)))}) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r3(_, B.len(B.Octets.to_list(name)), C.CpioHeader{C.CpioCrc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioCrc{}, data)}) : C.CpioStep}
      %Equal.sym(Bool, C.Cpio.is_trailer_name(name), False{}, okt) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r6(_, B.Octets.to_list(name), B.len(B.Octets.to_list(name)), C.CpioHeader{C.CpioCrc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioCrc{}, data)}, B.append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)))) : C.CpioStep}
      %skip_rt(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name)))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r))) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r7(_, B.Octets.to_list(name), C.CpioHeader{C.CpioCrc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioCrc{}, data)}) : C.CpioStep}
      %size_rt(B.len(B.Octets.to_list(data)), okd) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r8(C.split(_, B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r))), B.Octets.to_list(name), C.CpioHeader{C.CpioCrc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioCrc{}, data)}) : C.CpioStep}
      %split_rt(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r8(_, B.Octets.to_list(name), C.CpioHeader{C.CpioCrc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioCrc{}, data)}) : C.CpioStep}
      %skip_rt(C.pad4(B.len(B.Octets.to_list(data))), r) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r9(_, B.Octets.to_list(name), B.Octets.to_list(data), C.CpioHeader{C.CpioCrc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioCrc{}, data)}) : C.CpioStep}
      %eq_self(C.checksum(B.Octets.to_list(data))) : {C.CpioStepEntry{C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, B.Octets.of_list(B.Octets.to_list(name)), B.Octets.of_list(B.Octets.to_list(data))}, r} == C.entry.r10(_, C.entry.of(C.CpioHeader{C.CpioCrc{}, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(C.CpioCrc{}, data)}, B.Octets.to_list(name), B.Octets.to_list(data)), r) : C.CpioStep}
      {==}

# The archive's length bounds its entries: each entry starts with a byte of
# its magic.
def len_step(+fmt: C.CpioFormat, +e: C.CpioEntry, +l: Nat, +r: List<&2, U32>, h: {Nat.sub(l, B.len(r)) == 0n : Nat}) -> {Nat.sub(1n+l, B.len(lvstep(fmt, e, r))) == 0n : Nat}:
  match e:
    case C.CpioEntry{ino, mode, uid, gid, nlink, mtime, devmajor, devminor, rdevmajor, rdevminor, +name, +data}:
      mono_append(B.drop(1n, B.Octets.to_list(C.CpioHeader.encode(C.CpioHeader{fmt, ino, mode, uid, gid, nlink, mtime, C.size32(B.len(B.Octets.to_list(data))), devmajor, devminor, rdevmajor, rdevminor, C.size32(1n+B.len(B.Octets.to_list(name))), C.entry.check(fmt, data)}))), l, B.append(B.Octets.to_list(name), Con{0, B.append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)))}), mono_append(B.Octets.to_list(name), l, Con{0, B.append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)))}, sub_succ(l, B.len(B.append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)))), mono_append(B.zeros(C.pad4(Nat.add(111n, B.len(B.Octets.to_list(name))))), l, B.append(B.Octets.to_list(data), B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r)), mono_append(B.Octets.to_list(data), l, B.append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), r), mono_append(B.zeros(C.pad4(B.len(B.Octets.to_list(data)))), l, r, h))))))

def len_bound(+es: List<&2, C.CpioEntry>, +fmt: C.CpioFormat) -> {Nat.sub(List.length(&2, C.CpioEntry, es), B.len(lv(fmt, es))) == 0n : Nat}:
  match es:
    case Nil{}:
      {==}
    case Con{e, t}:
      len_step(fmt, e, List.length(&2, C.CpioEntry, t), lv(fmt, t), len_bound(t, fmt))

# With fuel for every entry, the archive's entries read back, one at a time.
def parse_rt(+es: List<&2, C.CpioEntry>, +n: Nat, +fmt: C.CpioFormat, ok: C.CpioEntry.valid_all(es), h: {Nat.sub(List.length(&2, C.CpioEntry, es), n) == 0n : Nat}) -> {Done{es} == C.parse.go(n, C.entry.read(lv(fmt, es))) : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}:
  match es:
    case Nil{}:
      match n:
        case 0n:
          match fmt:
            case C.CpioNewc{}:
              {==}
            case C.CpioCrc{}:
              {==}
        case 1n+m:
          match fmt:
            case C.CpioNewc{}:
              {==}
            case C.CpioCrc{}:
              {==}
    case Con{e, t}:
      match n:
        case 0n:
          Empty.absurd({Done{Con{e, t}} == C.parse.go(0n, C.entry.read(lv(fmt, Con{e, t}))) : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}, disc_lemma(List.length(&2, C.CpioEntry, t), h))
        case 1n+m:
          (oke, okt) = ok
          %entry_rt(fmt, e, lv(fmt, t), oke) : {Done{Con{e, t}} == C.parse.go(1n+m, _) : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}
          %parse_rt(t, m, fmt, okt, h) : {Done{Con{e, t}} == C.parse.cons(e, _) : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}
          {==}

def Laws.parse_build(fmt, es, ok):
  %vlist(fmt, es) : {C.parse.go(B.len(_), C.entry.read(B.Octets.to_list(C.Cpio.build(fmt, es)))) == Done{es} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}
  %vlist(fmt, es) : {C.parse.go(B.len(lv(fmt, es)), C.entry.read(_)) == Done{es} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}
  %parse_rt(es, B.len(lv(fmt, es)), fmt, ok, len_bound(es, fmt)) : {_ == Done{es} : Result<&2, &2, C.CpioError, List<&2, C.CpioEntry>>}
  {==}

# Vectors: computed
def Laws.hexfield_digits():
  {==}

def Laws.hexfield_either_case():
  {==}

def Laws.hexfield_order():
  {==}

def Laws.hexfield_not_digit():
  {==}

def Laws.hexfield_short():
  {==}

def Laws.checksum_hello():
  {==}

def Laws.one_file_archive():
  {==}

def Laws.empty_archive_newc():
  {==}

def Laws.empty_archive_crc():
  {==}

def Laws.trailing_bytes():
  {==}

def Laws.reject_empty():
  {==}

def Laws.reject_no_trailer():
  {==}

def Laws.reject_truncated_header():
  {==}

def Laws.reject_truncated_data():
  {==}

def Laws.reject_magic():
  {==}

def Laws.reject_hex():
  {==}

def Laws.reject_checksum():
  {==}

def Laws.newc_ignores_check():
  {==}

def Laws.reject_name_size():
  {==}

def Laws.reject_no_nul():
  {==}


def Laws.valid_example():
  (({==}, ({==}, ({==}, ({==}, {==})))), Unit{})
