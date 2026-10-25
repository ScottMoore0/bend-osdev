# Proofs of LAWS.bend (CCM). The byte layer's lemmas the modes share are
# mode-core's laws, used under the names below.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../word64/word64.bend as W
import ../mode-core/mode-core.bend as M
import ./ccm.bend as CC
import ../mode-core/LAWS.bend as CoreL
import ../mode-core/PROOF.bend as CoreP
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ./LAWS.bend as Laws

# mode-core's laws, under the names these proofs use

def bits.byte_byte(y: U32) -> {B.byte(B.byte(y)) == B.byte(y) : U32}:
  CoreL.byte_byte(y)

def sp.eta(s: M.CmSplit) -> {M.CmSplit{M.cm.split.blocks(s), M.cm.split.tail(s)} == s : M.CmSplit}:
  CoreL.split_eta(s)

def li.take_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.take(B.len(a), B.append(a, b)) == a : List<&2, U32>}:
  CoreL.list_take_append(a, b)

def li.drop_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.drop(B.len(a), B.append(a, b)) == b : List<&2, U32>}:
  CoreL.list_drop_append(a, b)

def li.mask_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.mask(B.append(a, b)) == B.append(B.mask(a), B.mask(b)) : List<&2, U32>}:
  CoreL.list_mask_append(a, b)

def li.mask_take(+n: Nat, +xs: List<&2, U32>) -> {B.mask(B.take(n, xs)) == B.take(n, B.mask(xs)) : List<&2, U32>}:
  CoreL.list_mask_take(n, xs)

def li.len_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.len(B.append(a, b)) == Nat.add(B.len(a), B.len(b)) : Nat}:
  CoreL.list_len_append(a, b)

def li.len_take(+n: Nat, +xs: List<&2, U32>) -> {Nat.is_le(n, B.len(xs)) == True{} : Bool} -> {B.len(B.take(n, xs)) == n : Nat}:
  h1 => CoreL.list_len_take(n, xs, h1)

def na.lt_le(+a: Nat, +b: Nat) -> {Nat.is_lt(a, b) == True{} : Bool} -> {Nat.is_le(a, b) == True{} : Bool}:
  h1 => CoreL.nat_lt_le(a, b, h1)

def sp.mask_blk(b: M.CmBlock, rest: List<&2, U32>) -> {B.mask(M.cm.bytes_onto(b, rest)) == M.cm.bytes_onto(b, B.mask(rest)) : List<&2, U32>}:
  CoreL.mask_bytes_onto(b, rest)

def sp.join_split(ys: List<&2, U32>) -> {M.cm.join_onto(M.cm.split.blocks(M.cm.split(B.mask(ys))), M.cm.split.tail(M.cm.split(B.mask(ys)))) == B.mask(ys) : List<&2, U32>}:
  CoreL.join_split(ys)

def sp.tail_short(ys: List<&2, U32>) -> {Nat.is_lt(B.len(M.cm.split.tail(M.cm.split(B.mask(ys)))), 16n) == True{} : Bool}:
  CoreL.split_tail_short(ys)

def sp.tail_masked(ys: List<&2, U32>) -> {B.mask(M.cm.split.tail(M.cm.split(B.mask(ys)))) == M.cm.split.tail(M.cm.split(B.mask(ys))) : List<&2, U32>}:
  CoreL.split_tail_masked(ys)

def sp.short_split(ys: List<&2, U32>) -> {Nat.is_lt(B.len(ys), 16n) == True{} : Bool} -> {M.cm.split(ys) == M.CmSplit{Nil{}, ys} : M.CmSplit}:
  h1 => CoreL.split_short(ys, h1)

def oc.masked(+o: B.Octets) -> {B.mask(B.Octets.to_list(o)) == B.Octets.to_list(o) : List<&2, U32>}:
  CoreL.octets_masked(o)

def tr.len_eq(+bs: List<&2, M.CmBlock>) -> {List.length(&2, M.CmBlock, bs) == M.cm.blocks.len(bs) : Nat}:
  CoreL.blocks_len_fast(bs)

def tr.split_eq(+xs: List<&2, U32>) -> {M.cm.split(xs) == M.cm.split.fast(xs) : M.CmSplit}:
  CoreL.split_fast(xs)

def tr.join_eq(+bs: List<&2, M.CmBlock>, +rest: List<&2, U32>) -> {M.cm.join_onto(bs, rest) == M.cm.join_onto.fast(bs, rest) : List<&2, U32>}:
  CoreL.join_onto_fast(bs, rest)

def tr.bind_cong(r: Result<&2, &2, M.CmError, B.Octets>, f: B.Octets -> Result<&2, &2, M.CmError, B.Octets>, g: B.Octets -> Result<&2, &2, M.CmError, B.Octets>, h: @c: B.Octets -> {f(c) == g(c) : Result<&2, &2, M.CmError, B.Octets>}) -> {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, r, f) == Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, r, g) : Result<&2, &2, M.CmError, B.Octets>}:
  CoreL.bind_cong(r, f, g, h)

def bx.rword(n: Nat, a: Word(n), b: Word(n)) -> {Word.xor(n, Word.xor(n, a, b), b) == a : Word(n)}:
  CoreL.word_xor_xor(n, a, b)

def bx.rblock(+a: M.CmBlock, +b: M.CmBlock) -> {M.CmBlock.xor(M.CmBlock.xor(a, b), b) == a : M.CmBlock}:
  CoreL.block_xor_xor(a, b)

def sp.mask_join_onto(bs: List<&2, M.CmBlock>, +rest: List<&2, U32>) -> {B.mask(M.cm.join_onto(bs, rest)) == M.cm.join_onto(bs, B.mask(rest)) : List<&2, U32>}:
  CoreL.mask_join_onto(bs, rest)

def sp.split_join_short(bs: List<&2, M.CmBlock>, +rest: List<&2, U32>) -> {M.cm.split(rest) == M.CmSplit{Nil{}, rest} : M.CmSplit} -> {M.cm.split(M.cm.join_onto(bs, rest)) == M.CmSplit{bs, rest} : M.CmSplit}:
  h1 => CoreL.split_join_short(bs, rest, h1)

# Booleans: False is not True

def bo.disc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def bo.empty(h: {False{} == True{} : Bool}) -> Empty:
  %h : bo.disc(_)
  Unit{}

def bo.absurd(-A: Type, h: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, bo.empty(h))

# CCM: the tail-recursive forms are the structural ones, piece by piece

def tr.pad(+xs: List<&2, U32>) -> {CC.ccm.pad(xs) == CC.ccm.pad.fast(xs) : List<&2, U32>}:
  %BL.len_fast(xs) : {CC.ccm.pad(xs) == B.append.fast(xs, B.zeros(Nat.mod(Nat.sub(16n, Nat.mod(_, 16n)), 16n))) : List<&2, U32>}
  %BL.append_fast(xs, B.zeros(Nat.mod(Nat.sub(16n, Nat.mod(B.len(xs), 16n)), 16n))) : {CC.ccm.pad(xs) == _ : List<&2, U32>}
  {==}

def tr.aad(empty: Bool, +a: List<&2, U32>) -> {CC.ccm.aad.pick(empty, a) == CC.ccm.aad.pick.fast(empty, a) : List<&2, U32>}:
  match empty:
    case True{}:
      {==}
    case False{}:
      %BL.len_fast(a) : {CC.ccm.aad.pick(False{}, a) == CC.ccm.pad.fast(B.append(CC.ccm.alen.pick(U32.is_lt(U32.from_nat(_), 65280), U32.from_nat(_)), a)) : List<&2, U32>}
      %tr.pad(B.append(CC.ccm.alen.pick(U32.is_lt(U32.from_nat(B.len(a)), 65280), U32.from_nat(B.len(a))), a)) : {CC.ccm.aad.pick(False{}, a) == _ : List<&2, U32>}
      {==}

def tr.mac(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +l: Nat, +nonce: List<&2, U32>, +a: List<&2, U32>, +p: List<&2, U32>) -> {CC.ccm.mac(~K, ~enc, k, m, l, nonce, a, p) == CC.ccm.mac.fast(~K, ~enc, k, m, l, nonce, a, p) : M.CmBlock}:
  %BL.len_fast(a) : {CC.ccm.mac(~K, ~enc, k, m, l, nonce, a, p) == CC.ccm.cbcmac(~K, ~enc, k, M.cm.split.blocks(M.cm.split.fast(B.append(Con{U32.from_nat(Nat.add(Nat.add(Nat.mul(64n, Nat.min(_, 1n)), Nat.mul(8n, Nat.div(Nat.sub(m, 2n), 2n))), Nat.sub(l, 1n))), B.append(nonce, CC.ccm.be(l, U32.from_nat(B.len.fast(p))))}, B.append.fast(CC.ccm.aad.pick.fast(Nat.is_eq(_, 0n), a), CC.ccm.pad.fast(p))))), M.CmBlock.zero()) : M.CmBlock}
  %BL.len_fast(p) : {CC.ccm.mac(~K, ~enc, k, m, l, nonce, a, p) == CC.ccm.cbcmac(~K, ~enc, k, M.cm.split.blocks(M.cm.split.fast(B.append(Con{U32.from_nat(Nat.add(Nat.add(Nat.mul(64n, Nat.min(B.len(a), 1n)), Nat.mul(8n, Nat.div(Nat.sub(m, 2n), 2n))), Nat.sub(l, 1n))), B.append(nonce, CC.ccm.be(l, U32.from_nat(_)))}, B.append.fast(CC.ccm.aad.pick.fast(Nat.is_eq(B.len(a), 0n), a), CC.ccm.pad.fast(p))))), M.CmBlock.zero()) : M.CmBlock}
  %tr.pad(p) : {CC.ccm.mac(~K, ~enc, k, m, l, nonce, a, p) == CC.ccm.cbcmac(~K, ~enc, k, M.cm.split.blocks(M.cm.split.fast(B.append(Con{U32.from_nat(Nat.add(Nat.add(Nat.mul(64n, Nat.min(B.len(a), 1n)), Nat.mul(8n, Nat.div(Nat.sub(m, 2n), 2n))), Nat.sub(l, 1n))), B.append(nonce, CC.ccm.be(l, U32.from_nat(B.len(p))))}, B.append.fast(CC.ccm.aad.pick.fast(Nat.is_eq(B.len(a), 0n), a), _)))), M.CmBlock.zero()) : M.CmBlock}
  %tr.aad(Nat.is_eq(B.len(a), 0n), a) : {CC.ccm.mac(~K, ~enc, k, m, l, nonce, a, p) == CC.ccm.cbcmac(~K, ~enc, k, M.cm.split.blocks(M.cm.split.fast(B.append(Con{U32.from_nat(Nat.add(Nat.add(Nat.mul(64n, Nat.min(B.len(a), 1n)), Nat.mul(8n, Nat.div(Nat.sub(m, 2n), 2n))), Nat.sub(l, 1n))), B.append(nonce, CC.ccm.be(l, U32.from_nat(B.len(p))))}, B.append.fast(_, CC.ccm.pad(p))))), M.CmBlock.zero()) : M.CmBlock}
  %BL.append_fast(CC.ccm.aad.pick(Nat.is_eq(B.len(a), 0n), a), CC.ccm.pad(p)) : {CC.ccm.mac(~K, ~enc, k, m, l, nonce, a, p) == CC.ccm.cbcmac(~K, ~enc, k, M.cm.split.blocks(M.cm.split.fast(B.append(Con{U32.from_nat(Nat.add(Nat.add(Nat.mul(64n, Nat.min(B.len(a), 1n)), Nat.mul(8n, Nat.div(Nat.sub(m, 2n), 2n))), Nat.sub(l, 1n))), B.append(nonce, CC.ccm.be(l, U32.from_nat(B.len(p))))}, _))), M.CmBlock.zero()) : M.CmBlock}
  %tr.split_eq(B.append(Con{U32.from_nat(Nat.add(Nat.add(Nat.mul(64n, Nat.min(B.len(a), 1n)), Nat.mul(8n, Nat.div(Nat.sub(m, 2n), 2n))), Nat.sub(l, 1n))), B.append(nonce, CC.ccm.be(l, U32.from_nat(B.len(p))))}, B.append(CC.ccm.aad.pick(Nat.is_eq(B.len(a), 0n), a), CC.ccm.pad(p)))) : {CC.ccm.mac(~K, ~enc, k, m, l, nonce, a, p) == CC.ccm.cbcmac(~K, ~enc, k, M.cm.split.blocks(_), M.CmBlock.zero()) : M.CmBlock}
  {==}

def tr.tag(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +l: Nat, +nonce: List<&2, U32>, +a: List<&2, U32>, +p: List<&2, U32>) -> {CC.ccm.tag(~K, ~enc, k, m, l, nonce, a, p) == CC.ccm.tag.fast(~K, ~enc, k, m, l, nonce, a, p) : List<&2, U32>}:
  %tr.mac(~K, ~enc, k, m, l, nonce, a, p) : {CC.ccm.tag(~K, ~enc, k, m, l, nonce, a, p) == B.take(m, M.cm.bytes_of(_)) : List<&2, U32>}
  {==}

def tr.ctrb_go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +a0: M.CmBlock, +i: U32, +acc: List<&2, M.CmBlock>) -> {CC.ccm.ctrb.go(~K, ~enc, k, bs, a0, i, acc) == M.cm.blocks.rev_onto(acc, CC.ccm.ctrb(~K, ~enc, k, bs, a0, i)) : List<&2, M.CmBlock>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      tr.ctrb_go(~K, ~enc, k, rest, a0, U32.add(i, 1), Con{M.CmBlock.xor(b, enc(k, CC.ccm.ai(a0, i))), acc})

def tr.ctrb_eq(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +bs: List<&2, M.CmBlock>, +a0: M.CmBlock, +i: U32) -> {CC.ccm.ctrb(~K, ~enc, k, bs, a0, i) == CC.ccm.ctrb.fast(~K, ~enc, k, bs, a0, i) : List<&2, M.CmBlock>}:
  Equal.sym(List<&2, M.CmBlock>, CC.ccm.ctrb.fast(~K, ~enc, k, bs, a0, i), CC.ccm.ctrb(~K, ~enc, k, bs, a0, i), tr.ctrb_go(~K, ~enc, k, bs, a0, i, Nil{}))

def tr.xcrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +a0: M.CmBlock, s: M.CmSplit) -> {CC.ccm.xcrypt(~K, ~enc, k, a0, s) == CC.ccm.xcrypt.fast(~K, ~enc, k, a0, s) : List<&2, U32>}:
  match s:
    case M.CmSplit{+bs, +tail}:
      %tr.len_eq(bs) : {CC.ccm.xcrypt(~K, ~enc, k, a0, M.CmSplit{bs, tail}) == M.cm.join_onto.fast(CC.ccm.ctrb.fast(~K, ~enc, k, bs, a0, 1), M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(_))))))) : List<&2, U32>}
      %tr.ctrb_eq(~K, ~enc, k, bs, a0, 1) : {CC.ccm.xcrypt(~K, ~enc, k, a0, M.CmSplit{bs, tail}) == M.cm.join_onto.fast(_, M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs)))))))) : List<&2, U32>}
      %tr.join_eq(CC.ccm.ctrb(~K, ~enc, k, bs, a0, 1), M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs)))))))) : {CC.ccm.xcrypt(~K, ~enc, k, a0, M.CmSplit{bs, tail}) == _ : List<&2, U32>}
      {==}

def tr.ebody(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +pv: List<&2, U32>) -> {CC.ccm.ebody(~K, ~enc, k, m, nv, av, pv) == CC.ccm.ebody.fast(~K, ~enc, k, m, nv, av, pv) : List<&2, U32>}:
  %tr.split_eq(pv) : {CC.ccm.ebody(~K, ~enc, k, m, nv, av, pv) == B.append.fast(CC.ccm.xcrypt.fast(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), _), M.cm.xor_bytes(CC.ccm.tag.fast(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))) : List<&2, U32>}
  %tr.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)) : {CC.ccm.ebody(~K, ~enc, k, m, nv, av, pv) == B.append.fast(_, M.cm.xor_bytes(CC.ccm.tag.fast(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))) : List<&2, U32>}
  %tr.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv) : {CC.ccm.ebody(~K, ~enc, k, m, nv, av, pv) == B.append.fast(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(_, M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))) : List<&2, U32>}
  %BL.append_fast(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))) : {CC.ccm.ebody(~K, ~enc, k, m, nv, av, pv) == _ : List<&2, U32>}
  {==}

def tr.e2(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +pv: List<&2, U32>, r: Result<&2, &2, M.CmError, Unit>) -> {CC.ccm.e2(~K, ~enc, k, m, nv, av, pv, r) == CC.ccm.e2.fast(~K, ~enc, k, m, nv, av, pv, r) : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      {==}
    case Done{u}:
      %tr.ebody(~K, ~enc, k, m, nv, av, pv) : {Done{B.Octets.of_list(CC.ccm.ebody(~K, ~enc, k, m, nv, av, pv))} == Done{B.Octets.of_list(_)} : Result<&2, &2, M.CmError, B.Octets>}
      {==}

def tr.ccm_encrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nonce: B.Octets, +aad: B.Octets, +p: B.Octets) -> {CC.Ccm.encrypt.ref(~K, ~enc, k, m, nonce, aad, p) == CC.Ccm.encrypt(~K, ~enc, k, m, nonce, aad, p) : Result<&2, &2, M.CmError, B.Octets>}:
  %BL.len_fast(B.Octets.to_list(p)) : {CC.Ccm.encrypt.ref(~K, ~enc, k, m, nonce, aad, p) == CC.ccm.e2.fast(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p), CC.ccm.checks(m, B.len(B.Octets.to_list(nonce)), _)) : Result<&2, &2, M.CmError, B.Octets>}
  tr.e2(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p), CC.ccm.checks(m, B.len(B.Octets.to_list(nonce)), B.len(B.Octets.to_list(p))))

def tr.dbody(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +cv: List<&2, U32>) -> {CC.ccm.dbody(~K, ~enc, k, m, nv, av, cv) == CC.ccm.dbody.fast(~K, ~enc, k, m, nv, av, cv) : Result<&2, &2, M.CmError, B.Octets>}:
  %BL.len_fast(cv) : {CC.ccm.dbody(~K, ~enc, k, m, nv, av, cv) == CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(Nat.sub(_, m), cv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))), CC.ccm.tag.fast(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, CC.ccm.xcrypt.fast(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split.fast(B.take.fast(Nat.sub(_, m), cv))))), CC.ccm.xcrypt.fast(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split.fast(B.take.fast(Nat.sub(_, m), cv)))) : Result<&2, &2, M.CmError, B.Octets>}
  %BL.take_fast(Nat.sub(B.len(cv), m), cv) : {CC.ccm.dbody(~K, ~enc, k, m, nv, av, cv) == CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(Nat.sub(B.len(cv), m), cv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))), CC.ccm.tag.fast(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, CC.ccm.xcrypt.fast(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split.fast(_)))), CC.ccm.xcrypt.fast(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split.fast(_))) : Result<&2, &2, M.CmError, B.Octets>}
  %tr.split_eq(B.take(Nat.sub(B.len(cv), m), cv)) : {CC.ccm.dbody(~K, ~enc, k, m, nv, av, cv) == CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(Nat.sub(B.len(cv), m), cv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))), CC.ccm.tag.fast(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, CC.ccm.xcrypt.fast(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), _))), CC.ccm.xcrypt.fast(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), _)) : Result<&2, &2, M.CmError, B.Octets>}
  %tr.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(B.take(Nat.sub(B.len(cv), m), cv))) : {CC.ccm.dbody(~K, ~enc, k, m, nv, av, cv) == CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(Nat.sub(B.len(cv), m), cv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))), CC.ccm.tag.fast(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, _)), _) : Result<&2, &2, M.CmError, B.Octets>}
  %tr.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(B.take(Nat.sub(B.len(cv), m), cv)))) : {CC.ccm.dbody(~K, ~enc, k, m, nv, av, cv) == CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(Nat.sub(B.len(cv), m), cv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))), _), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(B.take(Nat.sub(B.len(cv), m), cv)))) : Result<&2, &2, M.CmError, B.Octets>}
  {==}

def tr.d3(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +cv: List<&2, U32>, r: Result<&2, &2, M.CmError, Unit>) -> {CC.ccm.d3(~K, ~enc, k, m, nv, av, cv, r) == CC.ccm.d3.fast(~K, ~enc, k, m, nv, av, cv, r) : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      {==}
    case Done{u}:
      tr.dbody(~K, ~enc, k, m, nv, av, cv)

def tr.d2(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ok: Bool, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +cv: List<&2, U32>) -> {CC.ccm.d2(~K, ~enc, ok, k, m, nv, av, cv) == CC.ccm.d2.fast(~K, ~enc, ok, k, m, nv, av, cv) : Result<&2, &2, M.CmError, B.Octets>}:
  match ok:
    case False{}:
      %BL.len_fast(cv) : {CC.ccm.d2(~K, ~enc, False{}, k, m, nv, av, cv) == Fail{M.CmTooShort{_}} : Result<&2, &2, M.CmError, B.Octets>}
      {==}
    case True{}:
      %BL.len_fast(cv) : {CC.ccm.d2(~K, ~enc, True{}, k, m, nv, av, cv) == CC.ccm.d3.fast(~K, ~enc, k, m, nv, av, cv, CC.ccm.checks(m, B.len(nv), Nat.sub(_, m))) : Result<&2, &2, M.CmError, B.Octets>}
      tr.d3(~K, ~enc, k, m, nv, av, cv, CC.ccm.checks(m, B.len(nv), Nat.sub(B.len(cv), m)))

def tr.ccm_decrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nonce: B.Octets, +aad: B.Octets, +c: B.Octets) -> {CC.Ccm.decrypt.ref(~K, ~enc, k, m, nonce, aad, c) == CC.Ccm.decrypt(~K, ~enc, k, m, nonce, aad, c) : Result<&2, &2, M.CmError, B.Octets>}:
  %BL.len_fast(B.Octets.to_list(c)) : {CC.Ccm.decrypt.ref(~K, ~enc, k, m, nonce, aad, c) == CC.ccm.d2.fast(~K, ~enc, Nat.is_le(m, _), k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(c)) : Result<&2, &2, M.CmError, B.Octets>}
  tr.d2(~K, ~enc, Nat.is_le(m, B.len(B.Octets.to_list(c))), k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(c))

# XOR with a byte twice, and with itself

def bx.wself(n: Nat, w: Word(n)) -> {Word.xor(n, w, w) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{h, t}:
          match h:
            case False{}:
              %bx.wself(p, t) : {WCon{False{}, Word.xor(p, t, t)} == WCon{False{}, _} : Word(1n+p)}
              {==}
            case True{}:
              %bx.wself(p, t) : {WCon{False{}, Word.xor(p, t, t)} == WCon{False{}, _} : Word(1n+p)}
              {==}

def bits.xor_self(a: U32) -> {B.byte(U32.xor(a, a)) == 0 : U32}:
  match a:
    case U32{x}:
      %Equal.sym(Word(32n), Word.xor(32n, x, x), Word.zero(32n), bx.wself(32n, x)) : {B.byte(U32{_}) == 0 : U32}
      {==}

def bits.xor_xor(a: U32, y: U32) -> {B.byte(U32.xor(B.byte(U32.xor(a, y)), y)) == B.byte(a) : U32}:
  match a y:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WCon{y8, WCon{y9, WCon{y10, WCon{y11, WCon{y12, WCon{y13, WCon{y14, WCon{y15, WCon{y16, WCon{y17, WCon{y18, WCon{y19, WCon{y20, WCon{y21, WCon{y22, WCon{y23, WCon{y24, WCon{y25, WCon{y26, WCon{y27, WCon{y28, WCon{y29, WCon{y30, WCon{y31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %Equal.sym(Word(8n), Word.xor(8n, Word.xor(8n, WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}}, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WNil{}}}}}}}}}), WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WNil{}}}}}}}}}), WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}}, bx.rword(8n, WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}}, WCon{y0, WCon{y1, WCon{y2, WCon{y3, WCon{y4, WCon{y5, WCon{y6, WCon{y7, WNil{}}}}}}}}})) : {U32{W.W64.bits.cat(8n, 24n, _, Word.zero(24n))} == B.byte(U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{a11, WCon{a12, WCon{a13, WCon{a14, WCon{a15, WCon{a16, WCon{a17, WCon{a18, WCon{a19, WCon{a20, WCon{a21, WCon{a22, WCon{a23, WCon{a24, WCon{a25, WCon{a26, WCon{a27, WCon{a28, WCon{a29, WCon{a30, WCon{a31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}) : U32}
      {==}

def li.mask_xor(xs: List<&2, U32>, ys: List<&2, U32>) -> {B.mask(M.cm.xor_bytes(xs, ys)) == M.cm.xor_bytes(xs, ys) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +s}:
      match ys:
        case Nil{}:
          {==}
        case Con{+b, +t}:
          %bits.byte_byte(U32.xor(a, b)) : {Con{B.byte(B.byte(U32.xor(a, b))), B.mask(M.cm.xor_bytes(s, t))} == Con{_, M.cm.xor_bytes(s, t)} : List<&2, U32>}
          %li.mask_xor(s, t) : {Con{B.byte(B.byte(U32.xor(a, b))), B.mask(M.cm.xor_bytes(s, t))} == Con{B.byte(B.byte(U32.xor(a, b))), _} : List<&2, U32>}
          {==}

def li.len_xor(xs: List<&2, U32>, ys: List<&2, U32>) -> {Nat.is_le(B.len(xs), B.len(ys)) == True{} : Bool} -> {B.len(M.cm.xor_bytes(xs, ys)) == B.len(xs) : Nat}:
  match xs:
    case Nil{}:
      h => {==}
    case Con{+a, +s}:
      match ys:
        case Nil{}:
          h => bo.absurd({B.len(M.cm.xor_bytes(Con{a, s}, Nil{})) == B.len(Con{a, s}) : Nat}, h)
        case Con{+b, +t}:
          h => %li.len_xor(s, t)(h) : {1n+B.len(M.cm.xor_bytes(s, t)) == 1n+_ : Nat}
            {==}

def li.xor_xor(xs: List<&2, U32>, ys: List<&2, U32>) -> {Nat.is_le(B.len(xs), B.len(ys)) == True{} : Bool} -> {M.cm.xor_bytes(M.cm.xor_bytes(xs, ys), ys) == B.mask(xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      h => {==}
    case Con{+a, +s}:
      match ys:
        case Nil{}:
          h => bo.absurd({M.cm.xor_bytes(M.cm.xor_bytes(Con{a, s}, Nil{}), Nil{}) == B.mask(Con{a, s}) : List<&2, U32>}, h)
        case Con{+b, +t}:
          h => %Equal.sym(U32, B.byte(U32.xor(B.byte(U32.xor(a, b)), b)), B.byte(a), bits.xor_xor(a, b)) : {Con{_, M.cm.xor_bytes(M.cm.xor_bytes(s, t), t)} == Con{B.byte(a), B.mask(s)} : List<&2, U32>}
            %Equal.sym(List<&2, U32>, M.cm.xor_bytes(M.cm.xor_bytes(s, t), t), B.mask(s), li.xor_xor(s, t)(h)) : {Con{B.byte(a), _} == Con{B.byte(a), B.mask(s)} : List<&2, U32>}
            {==}

def na.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (a + b) - b == a
def na.sub_add(+a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), b) == a : Nat}:
  match b:
    case 0n:
      %Equal.sym(Nat, Nat.add(a, 0n), a, UL.nat_add_zero(a)) : {Nat.sub(_, 0n) == a : Nat}
      na.sub_zero(a)
    case 1n+p:
      %Equal.sym(Nat, Nat.add(a, 1n+p), 1n+Nat.add(a, p), UL.nat_add_succ(a, p)) : {Nat.sub(_, 1n+p) == a : Nat}
      na.sub_add(a, p)

def bo.and_r(+a: Bool, +b: Bool) -> {Bool.and(a, b) == True{} : Bool} -> {b == True{} : Bool}:
  match a:
    case False{}:
      h => bo.absurd({b == True{} : Bool}, h)
    case True{}:
      h => h

def bo.and_l(+a: Bool, +b: Bool) -> {Bool.and(a, b) == True{} : Bool} -> {a == True{} : Bool}:
  match a:
    case False{}:
      h => bo.absurd({False{} == True{} : Bool}, h)
    case True{}:
      h => {==}

def rs.disc(r: Result<&2, &2, M.CmError, Unit>) -> Type:
  match r:
    case Fail{e}:
      Unit
    case Done{u}:
      Empty

def rs.empty(+e: M.CmError, +u: Unit, h: {Fail{e} == Done{u} : Result<&2, &2, M.CmError, Unit>}) -> Empty:
  %h : rs.disc(_)
  Unit{}

def rs.absurd(-A: Type, +e: M.CmError, +u: Unit, h: {Fail{e} == Done{u} : Result<&2, &2, M.CmError, Unit>}) -> A:
  Empty.absurd(A, rs.empty(e, u, h))

# CCM

# checks that pass mean a tag of at most 16 bytes
def ccmp.tag_le.go(b: Bool, +m: Nat, +nl: Nat, +n: Nat, +u: Unit) -> {CC.ccm.tag_ok(m) == b : Bool} -> {CC.ccm.checks(m, nl, n) == Done{u} : Result<&2, &2, M.CmError, Unit>} -> {Nat.is_le(m, 16n) == True{} : Bool}:
  match b:
    case False{}:
      eb => h => rs.absurd({Nat.is_le(m, 16n) == True{} : Bool}, M.CmBadTagLength{m}, u, Equal.trans(Result<&2, &2, M.CmError, Unit>, CC.ccm.checks.tag(False{}, m, nl, n), CC.ccm.checks.tag(CC.ccm.tag_ok(m), m, nl, n), Done{u}, Equal.cong(Bool, Result<&2, &2, M.CmError, Unit>, x => CC.ccm.checks.tag(x, m, nl, n), False{}, CC.ccm.tag_ok(m), Equal.sym(Bool, CC.ccm.tag_ok(m), False{}, eb)), h))
    case True{}:
      eb => h => bo.and_l(Nat.is_le(m, 16n), Nat.is_eq(Nat.mod(m, 2n), 0n))(bo.and_r(Nat.is_le(4n, m), Bool.and(Nat.is_le(m, 16n), Nat.is_eq(Nat.mod(m, 2n), 0n)))(eb))

def ccmp.tag_le(+m: Nat, +nl: Nat, +n: Nat, +u: Unit, h: {CC.ccm.checks(m, nl, n) == Done{u} : Result<&2, &2, M.CmError, Unit>}) -> {Nat.is_le(m, 16n) == True{} : Bool}:
  ccmp.tag_le.go(CC.ccm.tag_ok(m), m, nl, n, u)({==})(h)

def ccmp.diff_self(xs: List<&2, U32>) -> {M.cm.diff(xs, xs, 0) == 0 : U32}:
  match xs:
    case Nil{}:
      {==}
    case Con{+a, +s}:
      %Equal.sym(U32, B.byte(U32.xor(a, a)), 0, bits.xor_self(a)) : {M.cm.diff(s, s, U32.or(0, _)) == 0 : U32}
      ccmp.diff_self(s)

def ccmp.ct_refl(+xs: List<&2, U32>) -> {M.cm.ct_eq(xs, xs) == True{} : Bool}:
  %Equal.sym(U32, M.cm.diff(xs, xs, 0), 0, ccmp.diff_self(xs)) : {U32.is_eq(_, 0) == True{} : Bool}
  {==}

def ccmp.len_ctrb(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +a0: M.CmBlock, +i: U32) -> {List.length(&2, M.CmBlock, CC.ccm.ctrb(~K, ~enc, k, bs, a0, i)) == List.length(&2, M.CmBlock, bs) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      %ccmp.len_ctrb(~K, ~enc, k, rest, a0, U32.add(i, 1)) : {1n+List.length(&2, M.CmBlock, CC.ccm.ctrb(~K, ~enc, k, rest, a0, U32.add(i, 1))) == 1n+_ : Nat}
      {==}

# CTR twice is the identity on blocks
def ccmp.ctrb2(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +a0: M.CmBlock, +i: U32) -> {CC.ccm.ctrb(~K, ~enc, k, CC.ccm.ctrb(~K, ~enc, k, bs, a0, i), a0, i) == bs : List<&2, M.CmBlock>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +rest}:
      %Equal.sym(M.CmBlock, M.CmBlock.xor(M.CmBlock.xor(b, enc(k, CC.ccm.ai(a0, i))), enc(k, CC.ccm.ai(a0, i))), b, bx.rblock(b, enc(k, CC.ccm.ai(a0, i)))) : {Con{_, CC.ccm.ctrb(~K, ~enc, k, CC.ccm.ctrb(~K, ~enc, k, rest, a0, U32.add(i, 1)), a0, U32.add(i, 1))} == Con{b, rest} : List<&2, M.CmBlock>}
      %Equal.sym(List<&2, M.CmBlock>, CC.ccm.ctrb(~K, ~enc, k, CC.ccm.ctrb(~K, ~enc, k, rest, a0, U32.add(i, 1)), a0, U32.add(i, 1)), rest, ccmp.ctrb2(~K, ~enc, k, rest, a0, U32.add(i, 1))) : {Con{b, _} == Con{b, rest} : List<&2, M.CmBlock>}
      {==}

def ccmp.mask_xcrypt(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +a0: M.CmBlock, s: M.CmSplit) -> {B.mask(CC.ccm.xcrypt(~K, ~enc, k, a0, s)) == CC.ccm.xcrypt(~K, ~enc, k, a0, s) : List<&2, U32>}:
  match s:
    case M.CmSplit{+bs, +tail}:
      %Equal.sym(List<&2, U32>, B.mask(M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, bs, a0, 1), M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs))))))))), M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, bs, a0, 1), B.mask(M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs))))))))), sp.mask_join_onto(CC.ccm.ctrb(~K, ~enc, k, bs, a0, 1), M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs))))))))) : {_ == M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, bs, a0, 1), M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs)))))))) : List<&2, U32>}
      %li.mask_xor(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs))))))) : {M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, bs, a0, 1), B.mask(M.cm.xor_bytes(tail, M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, bs))))))))) == M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, bs, a0, 1), _) : List<&2, U32>}
      {==}

def ccmp.len_join(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, bs: List<&2, M.CmBlock>, +a0: M.CmBlock, +i: U32, +x: List<&2, U32>, +y: List<&2, U32>, h: {B.len(x) == B.len(y) : Nat}) -> {B.len(M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, bs, a0, i), x)) == B.len(M.cm.join_onto(bs, y)) : Nat}:
  match bs:
    case Nil{}:
      h
    case Con{+b, +rest}:
      %Equal.sym(Nat, B.len(M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, rest, a0, U32.add(i, 1)), x)), B.len(M.cm.join_onto(rest, y)), ccmp.len_join(~K, ~enc, k, rest, a0, U32.add(i, 1), x, y, h)) : {Nat.add(16n, _) == Nat.add(16n, B.len(M.cm.join_onto(rest, y))) : Nat}
      {==}

# the CTR tail is as short as the plaintext tail
def ccmp.xt_short(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +a0: M.CmBlock, +ys: List<&2, U32>) -> {Nat.is_lt(B.len(M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys))))))))))), 16n) == True{} : Bool}:
  %Equal.sym(Nat, B.len(M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys))))))))))), B.len(M.cm.split.tail(M.cm.split(B.mask(ys)))), li.len_xor(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys))))))))))(na.lt_le(B.len(M.cm.split.tail(M.cm.split(B.mask(ys)))), 16n)(sp.tail_short(ys)))) : {Nat.is_lt(_, 16n) == True{} : Bool}
  sp.tail_short(ys)

# CTR from counter 1 undoes itself (on a masked byte string)
def ccmp.xx(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +a0: M.CmBlock, +ys: List<&2, U32>) -> {CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(B.mask(ys))))) == B.mask(ys) : List<&2, U32>}:
  %sp.eta(M.cm.split(B.mask(ys))) : {CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(CC.ccm.xcrypt(~K, ~enc, k, a0, _))) == B.mask(ys) : List<&2, U32>}
  %Equal.sym(M.CmSplit, M.cm.split(M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1), M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))))), M.CmSplit{CC.ccm.ctrb(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1), M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys))))))))))}, sp.split_join_short(CC.ccm.ctrb(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1), M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))))(sp.short_split(M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))))(ccmp.xt_short(~K, ~enc, k, a0, ys)))) : {CC.ccm.xcrypt(~K, ~enc, k, a0, _) == B.mask(ys) : List<&2, U32>}
  %Equal.sym(Nat, List.length(&2, M.CmBlock, CC.ccm.ctrb(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1)), List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))), ccmp.len_ctrb(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1)) : {M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, CC.ccm.ctrb(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1), a0, 1), M.cm.xor_bytes(M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(_))))))) == B.mask(ys) : List<&2, U32>}
  %Equal.sym(List<&2, M.CmBlock>, CC.ccm.ctrb(~K, ~enc, k, CC.ccm.ctrb(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1), a0, 1), M.cm.split.blocks(M.cm.split(B.mask(ys))), ccmp.ctrb2(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1)) : {M.cm.join_onto(_, M.cm.xor_bytes(M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys))))))))))) == B.mask(ys) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, M.cm.xor_bytes(M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))), B.mask(M.cm.split.tail(M.cm.split(B.mask(ys)))), li.xor_xor(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys))))))))))(na.lt_le(B.len(M.cm.split.tail(M.cm.split(B.mask(ys)))), 16n)(sp.tail_short(ys)))) : {M.cm.join_onto(M.cm.split.blocks(M.cm.split(B.mask(ys))), _) == B.mask(ys) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(M.cm.split.tail(M.cm.split(B.mask(ys)))), M.cm.split.tail(M.cm.split(B.mask(ys))), sp.tail_masked(ys)) : {M.cm.join_onto(M.cm.split.blocks(M.cm.split(B.mask(ys))), _) == B.mask(ys) : List<&2, U32>}
  sp.join_split(ys)

# and keeps its length
def ccmp.len_xc(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +a0: M.CmBlock, +ys: List<&2, U32>) -> {B.len(CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(B.mask(ys)))) == B.len(B.mask(ys)) : Nat}:
  %sp.eta(M.cm.split(B.mask(ys))) : {B.len(CC.ccm.xcrypt(~K, ~enc, k, a0, _)) == B.len(B.mask(ys)) : Nat}
  %sp.join_split(ys) : {B.len(M.cm.join_onto(CC.ccm.ctrb(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1), M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))))) == B.len(_) : Nat}
  ccmp.len_join(~K, ~enc, k, M.cm.split.blocks(M.cm.split(B.mask(ys))), a0, 1, M.cm.xor_bytes(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys)))))))))), M.cm.split.tail(M.cm.split(B.mask(ys))), li.len_xor(M.cm.split.tail(M.cm.split(B.mask(ys))), M.cm.bytes_of(enc(k, CC.ccm.ai(a0, U32.add(1, U32.from_nat(List.length(&2, M.CmBlock, M.cm.split.blocks(M.cm.split(B.mask(ys))))))))))(na.lt_le(B.len(M.cm.split.tail(M.cm.split(B.mask(ys)))), 16n)(sp.tail_short(ys))))

def ccmp.xxp(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +a0: M.CmBlock, +p: B.Octets) -> {CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(B.Octets.to_list(p))))) == B.Octets.to_list(p) : List<&2, U32>}:
  %oc.masked(p) : {CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(_)))) == _ : List<&2, U32>}
  ccmp.xx(~K, ~enc, k, a0, B.Octets.to_list(p))

def ccmp.len_xcp(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +a0: M.CmBlock, +p: B.Octets) -> {B.len(CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(B.Octets.to_list(p)))) == B.len(B.Octets.to_list(p)) : Nat}:
  %oc.masked(p) : {B.len(CC.ccm.xcrypt(~K, ~enc, k, a0, M.cm.split(_))) == B.len(_) : Nat}
  ccmp.len_xc(~K, ~enc, k, a0, B.Octets.to_list(p))

def ccmp.len_tag(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +l: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +pv: List<&2, U32>, h: {Nat.is_le(m, 16n) == True{} : Bool}) -> {B.len(CC.ccm.tag(~K, ~enc, k, m, l, nv, av, pv)) == m : Nat}:
  li.len_take(m, M.cm.bytes_of(CC.ccm.mac(~K, ~enc, k, m, l, nv, av, pv)))(h)

def ccmp.le_tag(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +l: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +pv: List<&2, U32>, +h: {Nat.is_le(m, 16n) == True{} : Bool}) -> {Nat.is_le(B.len(CC.ccm.tag(~K, ~enc, k, m, l, nv, av, pv)), 16n) == True{} : Bool}:
  %Equal.sym(Nat, B.len(CC.ccm.tag(~K, ~enc, k, m, l, nv, av, pv)), m, ccmp.len_tag(~K, ~enc, k, m, l, nv, av, pv, h)) : {Nat.is_le(_, 16n) == True{} : Bool}
  h

def ccmp.mask_tag(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +l: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +pv: List<&2, U32>) -> {B.mask(CC.ccm.tag(~K, ~enc, k, m, l, nv, av, pv)) == CC.ccm.tag(~K, ~enc, k, m, l, nv, av, pv) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, B.mask(CC.ccm.tag(~K, ~enc, k, m, l, nv, av, pv)), B.take(m, B.mask(M.cm.bytes_of(CC.ccm.mac(~K, ~enc, k, m, l, nv, av, pv)))), li.mask_take(m, M.cm.bytes_of(CC.ccm.mac(~K, ~enc, k, m, l, nv, av, pv)))) : {_ == CC.ccm.tag(~K, ~enc, k, m, l, nv, av, pv) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.mask(M.cm.bytes_onto(CC.ccm.mac(~K, ~enc, k, m, l, nv, av, pv), Nil{})), M.cm.bytes_onto(CC.ccm.mac(~K, ~enc, k, m, l, nv, av, pv), B.mask(Nil{})), sp.mask_blk(CC.ccm.mac(~K, ~enc, k, m, l, nv, av, pv), Nil{})) : {B.take(m, _) == CC.ccm.tag(~K, ~enc, k, m, l, nv, av, pv) : List<&2, U32>}
  {==}

def ccmp.mask_eb(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +pv: List<&2, U32>) -> {B.mask(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))) == B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))) : List<&2, U32>}:
  %Equal.sym(List<&2, U32>, B.mask(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))), B.append(B.mask(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), B.mask(M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))), li.mask_append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))) : {_ == B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))) : List<&2, U32>}
  %ccmp.mask_xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)) : {B.append(B.mask(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), B.mask(M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))) == B.append(_, M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))) : List<&2, U32>}
  %li.mask_xor(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))) : {B.append(B.mask(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), B.mask(M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))) == B.append(B.mask(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), _) : List<&2, U32>}
  {==}

def ccmp.len_eb(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nv: List<&2, U32>, +av: List<&2, U32>, +pv: List<&2, U32>, +h: {Nat.is_le(m, 16n) == True{} : Bool}) -> {B.len(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))) == Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), m) : Nat}:
  %Equal.sym(Nat, B.len(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))), Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), B.len(M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))), li.len_append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv)), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv)))))) : {_ == Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), m) : Nat}
  %Equal.sym(Nat, B.len(M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))), B.len(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv)), li.len_xor(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv))))(ccmp.le_tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv, h))) : {Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), _) == Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), m) : Nat}
  %Equal.sym(Nat, B.len(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv)), m, ccmp.len_tag(~K, ~enc, k, m, Nat.sub(15n, B.len(nv)), nv, av, pv, h)) : {Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), _) == Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(nv)), nv), M.cm.split(pv))), m) : Nat}
  {==}

# decryption accepts what encryption produced, whatever the parameter checks answer
def ccmp.main(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +m: Nat, +nonce: B.Octets, +aad: B.Octets, +p: B.Octets, r: Result<&2, &2, M.CmError, Unit>) -> {CC.ccm.checks(m, B.len(B.Octets.to_list(nonce)), B.len(B.Octets.to_list(p))) == r : Result<&2, &2, M.CmError, Unit>} -> {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, CC.ccm.e2(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p), r), c => CC.Ccm.decrypt.ref(~K, ~enc, k, m, nonce, aad, c)) == Result.map(&2, &2, M.CmError, B.Octets, B.Octets, c => p, CC.ccm.e2(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p), r)) : Result<&2, &2, M.CmError, B.Octets>}:
  match r:
    case Fail{e}:
      h => {==}
    case Done{+u}:
      +h => +hm = ccmp.tag_le(m, B.len(B.Octets.to_list(nonce)), B.len(B.Octets.to_list(p)), u, h)
        +leb = ccmp.len_eb(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p), hm)
        # decryption reads the ciphertext back, masked
        %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))))), B.mask(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), BL.octets_to_of(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))))) : {CC.ccm.d2(~K, ~enc, Nat.is_le(m, B.len(_)), k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), _) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # which it already is
        %Equal.sym(List<&2, U32>, B.mask(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))), ccmp.mask_eb(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p))) : {CC.ccm.d2(~K, ~enc, Nat.is_le(m, B.len(_)), k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), _) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # it is longer than the tag
        %Equal.sym(Nat, B.len(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m), leb) : {CC.ccm.d2(~K, ~enc, Nat.is_le(m, _), k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # 
        %Equal.sym(Bool, Nat.is_le(m, Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m)), True{}, UL.nat_le_add(m, B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))))) : {CC.ccm.d2(~K, ~enc, _, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # its body is as long as the message
        %Equal.sym(Nat, B.len(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m), leb) : {CC.ccm.d3(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))), CC.ccm.checks(m, B.len(B.Octets.to_list(nonce)), Nat.sub(_, m))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # 
        %Equal.sym(Nat, Nat.sub(Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m), m), B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), na.sub_add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m)) : {CC.ccm.d3(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))), CC.ccm.checks(m, B.len(B.Octets.to_list(nonce)), _)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # 
        %Equal.sym(Nat, B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), B.len(B.Octets.to_list(p)), ccmp.len_xcp(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), p)) : {CC.ccm.d3(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))), CC.ccm.checks(m, B.len(B.Octets.to_list(nonce)), _)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # so its checks pass as encryption's did
        %Equal.sym(Result<&2, &2, M.CmError, Unit>, CC.ccm.checks(m, B.len(B.Octets.to_list(nonce)), B.len(B.Octets.to_list(p))), Done{u}, h) : {CC.ccm.d3(~K, ~enc, k, m, B.Octets.to_list(nonce), B.Octets.to_list(aad), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))), _) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # the body and the tag apart
        %Equal.sym(Nat, B.len(B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m), leb) : {CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(Nat.sub(_, m), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.take(Nat.sub(_, m), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))))))), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.take(Nat.sub(_, m), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))))))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # 
        %Equal.sym(Nat, Nat.sub(Nat.add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m), m), B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), na.sub_add(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), m)) : {CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(_, B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.take(_, B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))))))), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.take(_, B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))))))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # 
        %Equal.sym(List<&2, U32>, B.take(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), li.take_append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))) : {CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(B.drop(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(_)))), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(_))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # 
        %Equal.sym(List<&2, U32>, B.drop(B.len(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))), B.append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), li.drop_append(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))), M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))))) : {CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(_, M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))))))), CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p)))))) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # CTR undoes itself: the plaintext
        %Equal.sym(List<&2, U32>, CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(CC.ccm.xcrypt(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), M.cm.split(B.Octets.to_list(p))))), B.Octets.to_list(p), ccmp.xxp(~K, ~enc, k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)), p)) : {CC.ccm.open(M.cm.ct_eq(M.cm.xor_bytes(M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), _)), _) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # the received tag, unmasked from S_0
        %Equal.sym(List<&2, U32>, M.cm.xor_bytes(M.cm.xor_bytes(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce))))), B.mask(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p))), li.xor_xor(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), M.cm.bytes_of(enc(k, CC.ccm.a0(Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce)))))(ccmp.le_tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p), hm))) : {CC.ccm.open(M.cm.ct_eq(_, CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p))), B.Octets.to_list(p)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # 
        %Equal.sym(List<&2, U32>, B.mask(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p))), CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), ccmp.mask_tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p))) : {CC.ccm.open(M.cm.ct_eq(_, CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p))), B.Octets.to_list(p)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # matches the tag recomputed
        %Equal.sym(Bool, M.cm.ct_eq(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)), CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p))), True{}, ccmp.ct_refl(CC.ccm.tag(~K, ~enc, k, m, Nat.sub(15n, B.len(B.Octets.to_list(nonce))), B.Octets.to_list(nonce), B.Octets.to_list(aad), B.Octets.to_list(p)))) : {CC.ccm.open(_, B.Octets.to_list(p)) == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        # 
        %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(p)), p, BL.octets_of_to(p)) : {Done{_} == Done{p} : Result<&2, &2, M.CmError, B.Octets>}
        {==}

def Laws.ccm_round_trip(K, enc, k, m, nonce, aad, p):
  # the public defs are the structural ones
  %tr.ccm_encrypt(~K, ~enc, k, m, nonce, aad, p) : {Result.bind(&2, &2, M.CmError, B.Octets, B.Octets, _, c => CC.Ccm.decrypt(~K, ~enc, k, m, nonce, aad, c)) == Result.map(&2, &2, M.CmError, B.Octets, B.Octets, c => p, _) : Result<&2, &2, M.CmError, B.Octets>}
  %tr.bind_cong(CC.Ccm.encrypt.ref(~K, ~enc, k, m, nonce, aad, p), c => CC.Ccm.decrypt.ref(~K, ~enc, k, m, nonce, aad, c), c => CC.Ccm.decrypt(~K, ~enc, k, m, nonce, aad, c), c => tr.ccm_decrypt(~K, ~enc, k, m, nonce, aad, c)) : {_ == Result.map(&2, &2, M.CmError, B.Octets, B.Octets, c => p, CC.Ccm.encrypt.ref(~K, ~enc, k, m, nonce, aad, p)) : Result<&2, &2, M.CmError, B.Octets>}
  ccmp.main(~K, ~enc, k, m, nonce, aad, p, CC.ccm.checks(m, B.len(B.Octets.to_list(nonce)), B.len(B.Octets.to_list(p))))({==})
