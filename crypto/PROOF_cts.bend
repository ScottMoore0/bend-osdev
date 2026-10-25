# Proofs of LAWS_cts.bend, from bytes' laws, cipher-core's
# block64_octets_round_trip and PROOF_bytes.bend's lemmas.
import Base
import ../bytes/bytes.bend as B
import ../bytes/LAWS.bend as BL
import ../bytes/PROOF.bend as BP
import ../mode-core/mode-core.bend as M
import ../cipher-core/cipher-core.bend as L
import ../cipher-core/LAWS.bend as CoreL
import ../cipher-core/PROOF.bend as CoreP
import ./crypto.bend as Cr
import ./octets.bend as O
import ./cts.bend as Ct
import ./inst_cm.bend as CM
import ./proof_bits.bend as Bits
import ./PROOF_bytes.bend as PB
import ./LAWS_cts.bend as Laws
import ../u32/LAWS.bend as UL
import ../u32/PROOF.bend as UP
import ../u32/LAWS_order.bend as UO
import ../u32/PROOF_order.bend as UOP

# How the proofs go. CBC-CS3 cuts the message into pieces of the block size
# (CrOct.pieces: whole blocks, then the last 1 to b bytes), and decryption
# cuts the ciphertext the same way. The pieces are a structural function of
# the bytes (pc.PC: pc.go_PC, pc.pieces), which joined give the bytes back
# (pc.cl_PC) and are well-formed (pc.wf_PC); and the pieces of well-formed
# pieces joined are those pieces (pc.L2: a full piece is cut off whole,
# pc.Afull, a short last one flushed at the end, pc.Ashort). The modes' loops
# are structural forms with their accumulators (pc.enc_E, pc.dec_D), and the
# ciphertext's pieces are well-formed and as long as the message's (pc.wfE,
# pc.lenE), so decryption reads back exactly the encrypted pieces. Each
# piece then decrypts to its plaintext (pc.DE): XOR with the chaining value
# undone over the piece's length (pc.ox, on byte lists: pc.xx), and for the
# stolen last two, the zero-padded piece's XOR with C_(n-1) is C_(n-1)'s own
# bytes past it (pc.xdz) and the piece itself before it (pc.xtz). What the
# block cipher contributes is two facts on the list of its inputs (pc.oes):
# each decrypted after encrypting is itself, and each output has its input's
# length; for each block format they follow from the format (its bytes read
# back are the block's both ways) and the hypothesis inv (the generated
# region at the end).

# Booleans and naturals

def pc.bdisc(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

def pc.bd(h: {False{} == True{} : Bool}) -> Empty:
  %h : pc.bdisc(_)
  Unit{}

def pc.absurd(-A: Type, h: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, pc.bd(h))

def pc.and_l(a: Bool, +b: Bool) -> {Bool.and(a, b) == True{} : Bool} -> {a == True{} : Bool}:
  match a:
    case False{}:
      h => h
    case True{}:
      h => {==}

def pc.and_r(a: Bool, +b: Bool) -> {Bool.and(a, b) == True{} : Bool} -> {b == True{} : Bool}:
  match a:
    case False{}:
      h => pc.absurd({b == True{} : Bool}, h)
    case True{}:
      h => h

def pc.le0(+y: Nat) -> {Nat.is_le(0n, y) == True{} : Bool}:
  match y:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pc.le_of_add(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, b) == c : Nat} -> {Nat.is_le(a, c) == True{} : Bool}:
  h => %h : {Nat.is_le(a, _) == True{} : Bool}
    UO.nat_le_add_r(a, b)

def pc.eq_true(+a: Nat, +b: Nat) -> {Nat.is_eq(a, b) == True{} : Bool} -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      h => {==}
    case 0n 1n+bp:
      h => pc.absurd({0n == 1n+bp : Nat}, h)
    case 1n+ap 0n:
      h => pc.absurd({1n+ap == 0n : Nat}, h)
    case 1n+ap 1n+bp:
      h => Equal.cong(Nat, Nat, x => 1n+x, ap, bp, pc.eq_true(ap, bp)(h))

# a <= 1 + q and a != 1 + q give a <= q
def pc.le_neq(+a: Nat, +q: Nat) -> {Nat.is_le(a, 1n+q) == True{} : Bool} -> {Nat.is_eq(a, 1n+q) == False{} : Bool} -> {Nat.is_le(a, q) == True{} : Bool}:
  match a:
    case 0n:
      h1 => h2 => pc.le0(q)
    case 1n+ap:
      match ap:
        case 0n:
          match q:
            case 0n:
              h1 => h2 => pc.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, h2))
            case 1n+qp:
              h1 => h2 => pc.le0(qp)
        case 1n+aq:
          match q:
            case 0n:
              h1 => h2 => pc.absurd({Nat.is_le(2n+aq, 0n) == True{} : Bool}, h1)
            case 1n+qp:
              h1 => h2 => pc.le_neq(ap, qp)(h1)(h2)

# d <= n gives d + (n - d) = n
def pc.add_sub(+d: Nat, +n: Nat) -> {Nat.is_le(d, n) == True{} : Bool} -> {Nat.add(d, Nat.sub(n, d)) == n : Nat}:
  match d n:
    case 0n 0n:
      h => {==}
    case 0n 1n+np:
      h => {==}
    case 1n+dp 0n:
      h => pc.absurd({Nat.add(1n+dp, Nat.sub(0n, 1n+dp)) == 0n : Nat}, h)
    case 1n+dp 1n+np:
      h => %pc.add_sub(dp, np)(h) : {1n+Nat.add(dp, Nat.sub(np, dp)) == 1n+_ : Nat}
        {==}

def pc.eq_refl(+x: Nat) -> {Nat.is_eq(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      pc.eq_refl(p)

def pc.pred(+n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def pc.ndisc(+n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def pc.nd(+p: Nat, h: {1n+p == 0n : Nat}) -> Empty:
  %h : pc.ndisc(_)
  Unit{}

# Lists of bytes

def pc.app_nil(+p: List<&2, U32>) -> {B.append(p, Nil{}) == p : List<&2, U32>}:
  match p:
    case Nil{}:
      {==}
    case Con{h, t}:
      %pc.app_nil(t) : {Con{h, B.append(t, Nil{})} == Con{h, _} : List<&2, U32>}
      {==}

def pc.len_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.len(B.append(a, b)) == Nat.add(B.len(a), B.len(b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      %pc.len_append(t, b) : {1n+B.len(B.append(t, b)) == 1n+_ : Nat}
      {==}

# octets.bend's rev: onto a, then z after
def pc.rev_app(+c: List<&2, U32>, +a: List<&2, U32>, +z: List<&2, U32>) -> {O.cr.oct.rev(c, B.append(a, z)) == B.append(O.cr.oct.rev(c, a), z) : List<&2, U32>}:
  match c:
    case Nil{}:
      {==}
    case Con{y, t}:
      pc.rev_app(t, Con{y, a}, z)

def pc.len_rev(+c: List<&2, U32>, +z: List<&2, U32>) -> {B.len(O.cr.oct.rev(c, z)) == Nat.add(B.len(c), B.len(z)) : Nat}:
  match c:
    case Nil{}:
      {==}
    case Con{y, t}:
      Equal.trans(Nat, B.len(O.cr.oct.rev(t, Con{y, z})), Nat.add(B.len(t), 1n+B.len(z)), 1n+Nat.add(B.len(t), B.len(z)), pc.len_rev(t, Con{y, z}), UL.nat_add_succ(B.len(t), B.len(z)))

def pc.rro(+p: List<&2, U32>, +c: List<&2, U32>, +z: List<&2, U32>) -> {O.cr.oct.rev(O.cr.oct.rev(p, c), z) == O.cr.oct.rev(c, B.append(p, z)) : List<&2, U32>}:
  match p:
    case Nil{}:
      {==}
    case Con{x, t}:
      pc.rro(t, Con{x, c}, z)

def pc.add1(+a: Nat) -> {Nat.add(a, 1n) == 1n+a : Nat}:
  Equal.trans(Nat, Nat.add(a, 1n), 1n+Nat.add(a, 0n), 1n+a, UL.nat_add_succ(a, 0n), Equal.cong(Nat, Nat, w => 1n+w, Nat.add(a, 0n), a, UL.nat_add_zero(a)))

def pc.con2(-A: Data, +x: A, +y: A, +t: List<&2, A>, +u: List<&2, A>, ex: {x == y : A}, et: {t == u : List<&2, A>}) -> {Con{x, t} == Con{y, u} : List<&2, A>}:
  %ex : {Con{x, t} == Con{_, u} : List<&2, A>}
  %et : {Con{x, t} == Con{x, _} : List<&2, A>}
  {==}

def pc.rr(+p: List<&2, U32>) -> {O.cr.oct.rev(O.cr.oct.rev(p, Nil{}), Nil{}) == p : List<&2, U32>}:
  Equal.trans(List<&2, U32>, O.cr.oct.rev(O.cr.oct.rev(p, Nil{}), Nil{}), B.append(p, Nil{}), p, pc.rro(p, Nil{}, Nil{}), pc.app_nil(p))

# Pieces, structurally: pc.PC(xs, q, j, cur, z) cuts xs into pieces of
# 1 + q bytes, with cur (reversed) the piece being filled and j the bytes
# it takes after the next one; the pieces go before z

def pc.PC(+xs: List<&2, U32>, +q: Nat, +j: Nat, +cur: List<&2, U32>, +z: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      O.cr.oct.flush(cur, z)
    case Con{x, t}:
      match j:
        case 0n:
          Con{O.cr.oct.rev(Con{x, cur}, Nil{}), pc.PC(t, q, q, Nil{}, z)}
        case 1n+jp:
          pc.PC(t, q, jp, Con{x, cur}, z)

def pc.cl(+ls: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      B.append(p, pc.cl(t))

# octets.bend's pieces.go with its step's values as arguments
def pc.pg(+t: List<&2, U32>, +n: Nat, +full: Bool, +c: List<&2, U32>, +i: Nat, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  O.cr.oct.pieces.go(t, n, O.cr.oct.pieces.i(full, 1n+i), O.cr.oct.pieces.cur(full, c), O.cr.oct.pieces.step(full, c, acc))

def pc.flush_revs(+cur: List<&2, U32>, +acc: List<&2, List<&2, U32>>, +z: List<&2, List<&2, U32>>) -> {O.cr.oct.revs(O.cr.oct.flush(cur, acc), z) == O.cr.oct.revs(acc, O.cr.oct.flush(cur, z)) : List<&2, List<&2, U32>>}:
  match cur:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# the loop is the structural form (i bytes so far, j after the next)
def pc.go_PC(+xs: List<&2, U32>, +q: Nat, +i: Nat, +j: Nat, +cur: List<&2, U32>, +acc: List<&2, List<&2, U32>>, +z: List<&2, List<&2, U32>>) -> {Nat.add(i, 1n+j) == 1n+q : Nat} -> {O.cr.oct.revs(O.cr.oct.pieces.go(xs, 1n+q, i, cur, acc), z) == O.cr.oct.revs(acc, pc.PC(xs, q, j, cur, z)) : List<&2, List<&2, U32>>}:
  match xs:
    case Nil{}:
      h => pc.flush_revs(cur, acc, z)
    case Con{+x, t}:
      match j:
        case 0n:
          h => %Equal.sym(Bool, Nat.is_eq(1n+i, 1n+q), True{}, PB.pb.full(i, 1n+q)(h)) : {O.cr.oct.revs(pc.pg(t, 1n+q, _, Con{x, cur}, i, acc), z) == O.cr.oct.revs(acc, Con{O.cr.oct.rev(Con{x, cur}, Nil{}), pc.PC(t, q, q, Nil{}, z)}) : List<&2, List<&2, U32>>}
            pc.go_PC(t, q, 0n, q, Nil{}, Con{O.cr.oct.rev(Con{x, cur}, Nil{}), acc}, z)({==})
        case 1n+jp:
          +h => %Equal.sym(Bool, Nat.is_eq(1n+i, 1n+q), False{}, PB.pb.notfull(i, jp, 1n+q)(h)) : {O.cr.oct.revs(pc.pg(t, 1n+q, _, Con{x, cur}, i, acc), z) == O.cr.oct.revs(acc, pc.PC(t, q, jp, Con{x, cur}, z)) : List<&2, List<&2, U32>>}
            pc.go_PC(t, q, 1n+i, jp, Con{x, cur}, acc, z)(Equal.trans(Nat, 1n+Nat.add(i, 1n+jp), Nat.add(i, 2n+jp), 1n+q, Equal.sym(Nat, Nat.add(i, 2n+jp), 1n+Nat.add(i, 1n+jp), UL.nat_add_succ(i, 1n+jp)), h))

def pc.pieces(+q: Nat, +xs: List<&2, U32>) -> {O.CrOct.pieces(1n+q, xs) == pc.PC(xs, q, q, Nil{}, Nil{}) : List<&2, List<&2, U32>>}:
  pc.go_PC(xs, q, 0n, q, Nil{}, Nil{}, Nil{})({==})

# the pieces joined are the bytes
def pc.cl_PC(+xs: List<&2, U32>, +q: Nat, +j: Nat, +cur: List<&2, U32>) -> {pc.cl(pc.PC(xs, q, j, cur, Nil{})) == O.cr.oct.rev(cur, xs) : List<&2, U32>}:
  match xs:
    case Nil{}:
      match cur:
        case Nil{}:
          {==}
        case Con{h, t}:
          pc.app_nil(O.cr.oct.rev(Con{h, t}, Nil{}))
    case Con{+x, +t}:
      match j:
        case 0n:
          %Equal.sym(List<&2, U32>, pc.cl(pc.PC(t, q, q, Nil{}, Nil{})), t, pc.cl_PC(t, q, q, Nil{})) : {B.append(O.cr.oct.rev(Con{x, cur}, Nil{}), _) == O.cr.oct.rev(Con{x, cur}, t) : List<&2, U32>}
          Equal.sym(List<&2, U32>, O.cr.oct.rev(Con{x, cur}, B.append(Nil{}, t)), B.append(O.cr.oct.rev(Con{x, cur}, Nil{}), t), pc.rev_app(Con{x, cur}, Nil{}, t))
        case 1n+jp:
          pc.cl_PC(t, q, jp, Con{x, cur})

# a piece of len(p) = 1 + q bytes is full whatever follows it
def pc.okp(+n: Nat, +p: List<&2, U32>, +t: List<&2, List<&2, U32>>) -> Bool:
  match t:
    case Nil{}:
      Bool.and(Nat.is_lt(0n, B.len(p)), Nat.is_le(B.len(p), n))
    case Con{a, b}:
      Nat.is_eq(B.len(p), n)

# well-formed pieces: each of n bytes, but the last of 1 to n
def pc.wfz(+n: Nat, +ps: List<&2, List<&2, U32>>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{p, +t}:
      Bool.and(pc.okp(n, p, t), pc.wfz(n, t))

def pc.len_rc(+y: U32, +t: List<&2, U32>) -> {B.len(O.cr.oct.rev(Con{y, t}, Nil{})) == 1n+B.len(t) : Nat}:
  Equal.trans(Nat, B.len(O.cr.oct.rev(Con{y, t}, Nil{})), Nat.add(1n+B.len(t), 0n), 1n+B.len(t), pc.len_rev(Con{y, t}, Nil{}), UL.nat_add_zero(1n+B.len(t)))

def pc.lt_rc(+y: U32, +t: List<&2, U32>) -> {Nat.is_lt(0n, B.len(O.cr.oct.rev(Con{y, t}, Nil{}))) == True{} : Bool}:
  %Equal.sym(Nat, B.len(O.cr.oct.rev(Con{y, t}, Nil{})), 1n+B.len(t), pc.len_rc(y, t)) : {Nat.is_lt(0n, _) == True{} : Bool}
  {==}

def pc.le_rc(+y: U32, +t: List<&2, U32>, +q: Nat, h: {Nat.is_le(B.len(t), q) == True{} : Bool}) -> {Nat.is_le(B.len(O.cr.oct.rev(Con{y, t}, Nil{})), 1n+q) == True{} : Bool}:
  %Equal.sym(Nat, B.len(O.cr.oct.rev(Con{y, t}, Nil{})), 1n+B.len(t), pc.len_rc(y, t)) : {Nat.is_le(_, 1n+q) == True{} : Bool}
  h

def pc.okp_full(+q: Nat, +p: List<&2, U32>, +t: List<&2, List<&2, U32>>) -> {B.len(p) == 1n+q : Nat} -> {pc.okp(1n+q, p, t) == True{} : Bool}:
  match t:
    case Nil{}:
      h => %Equal.sym(Nat, B.len(p), 1n+q, h) : {Bool.and(Nat.is_lt(0n, _), Nat.is_le(_, 1n+q)) == True{} : Bool}
        UL.nat_le_refl(q)
    case Con{a, b}:
      h => %Equal.sym(Nat, B.len(p), 1n+q, h) : {Nat.is_eq(_, 1n+q) == True{} : Bool}
        pc.eq_refl(q)

def pc.true_and(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# the structural pieces are well-formed (cur of i bytes, i + 1 + j = 1 + q)
def pc.wf_PC(+xs: List<&2, U32>, +q: Nat, +j: Nat, +cur: List<&2, U32>) -> {Nat.add(B.len(cur), 1n+j) == 1n+q : Nat} -> {pc.wfz(1n+q, pc.PC(xs, q, j, cur, Nil{})) == True{} : Bool}:
  match xs:
    case Nil{}:
      match cur:
        case Nil{}:
          h => {==}
        case Con{+y, +t}:
          h => pc.true_and(pc.okp(1n+q, O.cr.oct.rev(Con{y, t}, Nil{}), Nil{}), True{}, pc.true_and(Nat.is_lt(0n, B.len(O.cr.oct.rev(Con{y, t}, Nil{}))), Nat.is_le(B.len(O.cr.oct.rev(Con{y, t}, Nil{})), 1n+q), pc.lt_rc(y, t), pc.le_rc(y, t, q, pc.le_of_add(B.len(t), 1n+j, q)(Equal.cong(Nat, Nat, w => pc.pred(w), 1n+Nat.add(B.len(t), 1n+j), 1n+q, h)))), {==})
    case Con{+x, +t}:
      match j:
        case 0n:
          h => pc.true_and(pc.okp(1n+q, O.cr.oct.rev(Con{x, cur}, Nil{}), pc.PC(t, q, q, Nil{}, Nil{})), pc.wfz(1n+q, pc.PC(t, q, q, Nil{}, Nil{})), pc.okp_full(q, O.cr.oct.rev(Con{x, cur}, Nil{}), pc.PC(t, q, q, Nil{}, Nil{}))(Equal.trans(Nat, B.len(O.cr.oct.rev(Con{x, cur}, Nil{})), 1n+B.len(cur), 1n+q, pc.len_rc(x, cur), Equal.trans(Nat, 1n+B.len(cur), Nat.add(B.len(cur), 1n), 1n+q, Equal.sym(Nat, Nat.add(B.len(cur), 1n), 1n+B.len(cur), pc.add1(B.len(cur))), h))), pc.wf_PC(t, q, q, Nil{})({==}))
        case 1n+jp:
          h => pc.wf_PC(t, q, jp, Con{x, cur})(Equal.trans(Nat, 1n+Nat.add(B.len(cur), 1n+jp), Nat.add(B.len(cur), 2n+jp), 1n+q, Equal.sym(Nat, Nat.add(B.len(cur), 2n+jp), 1n+Nat.add(B.len(cur), 1n+jp), UL.nat_add_succ(B.len(cur), 1n+jp)), h))

# a piece of 1 + j bytes is cut off whole
def pc.Afull(+p: List<&2, U32>, +r: List<&2, U32>, +q: Nat, +j: Nat, +cur: List<&2, U32>, +z: List<&2, List<&2, U32>>) -> {B.len(p) == 1n+j : Nat} -> {pc.PC(B.append(p, r), q, j, cur, z) == Con{O.cr.oct.rev(O.cr.oct.rev(p, cur), Nil{}), pc.PC(r, q, q, Nil{}, z)} : List<&2, List<&2, U32>>}:
  match p:
    case Nil{}:
      h => Empty.absurd({pc.PC(r, q, j, cur, z) == Con{O.cr.oct.rev(cur, Nil{}), pc.PC(r, q, q, Nil{}, z)} : List<&2, List<&2, U32>>}, pc.nd(j, Equal.sym(Nat, 0n, 1n+j, h)))
    case Con{+x, +t}:
      match t:
        case Nil{}:
          match j:
            case 0n:
              h => {==}
            case 1n+jp:
              h => Empty.absurd({pc.PC(Con{x, r}, q, 1n+jp, cur, z) == Con{O.cr.oct.rev(Con{x, cur}, Nil{}), pc.PC(r, q, q, Nil{}, z)} : List<&2, List<&2, U32>>}, pc.nd(jp, Equal.sym(Nat, 0n, 1n+jp, Equal.cong(Nat, Nat, w => pc.pred(w), 1n, 2n+jp, h))))
        case Con{+y, +t2}:
          match j:
            case 0n:
              h => Empty.absurd({pc.PC(Con{x, B.append(Con{y, t2}, r)}, q, 0n, cur, z) == Con{O.cr.oct.rev(O.cr.oct.rev(Con{x, Con{y, t2}}, cur), Nil{}), pc.PC(r, q, q, Nil{}, z)} : List<&2, List<&2, U32>>}, pc.nd(B.len(t2), Equal.cong(Nat, Nat, w => pc.pred(w), 2n+B.len(t2), 1n, h)))
            case 1n+jp:
              h => pc.Afull(t, r, q, jp, Con{x, cur}, z)(Equal.cong(Nat, Nat, w => pc.pred(w), 2n+B.len(t2), 2n+jp, h))

# a short piece is flushed at the end
def pc.Ashort(+p: List<&2, U32>, +q: Nat, +j: Nat, +cur: List<&2, U32>, +z: List<&2, List<&2, U32>>) -> {Nat.is_le(B.len(p), j) == True{} : Bool} -> {pc.PC(p, q, j, cur, z) == O.cr.oct.flush(O.cr.oct.rev(p, cur), z) : List<&2, List<&2, U32>>}:
  match p:
    case Nil{}:
      h => {==}
    case Con{x, t}:
      match j:
        case 0n:
          h => pc.absurd({pc.PC(Con{x, t}, q, 0n, cur, z) == O.cr.oct.flush(O.cr.oct.rev(Con{x, t}, cur), z) : List<&2, List<&2, U32>>}, h)
        case 1n+jp:
          h => pc.Ashort(t, q, jp, Con{x, cur}, z)(h)

def pc.flush_rev(+p: List<&2, U32>, +h: U32, +c: List<&2, U32>, +z: List<&2, List<&2, U32>>) -> {O.cr.oct.flush(O.cr.oct.rev(p, Con{h, c}), z) == Con{O.cr.oct.rev(O.cr.oct.rev(p, Con{h, c}), Nil{}), z} : List<&2, List<&2, U32>>}:
  match p:
    case Nil{}:
      {==}
    case Con{y, t}:
      pc.flush_rev(t, y, Con{h, c}, z)

# a short last piece
def pc.lastx(+p: List<&2, U32>, +q: Nat) -> {Nat.is_lt(0n, B.len(p)) == True{} : Bool} -> {Nat.is_le(B.len(p), q) == True{} : Bool} -> {pc.PC(B.append(p, Nil{}), q, q, Nil{}, Nil{}) == Con{p, Nil{}} : List<&2, List<&2, U32>>}:
  match p:
    case Nil{}:
      h1 => h2 => pc.absurd({pc.PC(Nil{}, q, q, Nil{}, Nil{}) == Con{Nil{}, Nil{}} : List<&2, List<&2, U32>>}, h1)
    case Con{+x, +t}:
      h1 => h2 => %Equal.sym(List<&2, U32>, B.append(Con{x, t}, Nil{}), Con{x, t}, pc.app_nil(Con{x, t})) : {pc.PC(_, q, q, Nil{}, Nil{}) == Con{Con{x, t}, Nil{}} : List<&2, List<&2, U32>>}
        %Equal.sym(List<&2, List<&2, U32>>, pc.PC(Con{x, t}, q, q, Nil{}, Nil{}), O.cr.oct.flush(O.cr.oct.rev(Con{x, t}, Nil{}), Nil{}), pc.Ashort(Con{x, t}, q, q, Nil{}, Nil{})(h2)) : {_ == Con{Con{x, t}, Nil{}} : List<&2, List<&2, U32>>}
        %Equal.sym(List<&2, List<&2, U32>>, O.cr.oct.flush(O.cr.oct.rev(t, Con{x, Nil{}}), Nil{}), Con{O.cr.oct.rev(O.cr.oct.rev(t, Con{x, Nil{}}), Nil{}), Nil{}}, pc.flush_rev(t, x, Nil{}, Nil{})) : {_ == Con{Con{x, t}, Nil{}} : List<&2, List<&2, U32>>}
        %Equal.sym(List<&2, U32>, O.cr.oct.rev(O.cr.oct.rev(Con{x, t}, Nil{}), Nil{}), Con{x, t}, pc.rr(Con{x, t})) : {Con{_, Nil{}} == Con{Con{x, t}, Nil{}} : List<&2, List<&2, U32>>}
        {==}

# the last piece, 1 to 1 + q bytes
def pc.last(ok: Bool, +p: List<&2, U32>, +q: Nat) -> {Nat.is_eq(B.len(p), 1n+q) == ok : Bool} -> {Nat.is_lt(0n, B.len(p)) == True{} : Bool} -> {Nat.is_le(B.len(p), 1n+q) == True{} : Bool} -> {pc.PC(B.append(p, Nil{}), q, q, Nil{}, Nil{}) == Con{p, Nil{}} : List<&2, List<&2, U32>>}:
  match ok:
    case True{}:
      e => h1 => h2 => Equal.trans(List<&2, List<&2, U32>>, pc.PC(B.append(p, Nil{}), q, q, Nil{}, Nil{}), Con{O.cr.oct.rev(O.cr.oct.rev(p, Nil{}), Nil{}), pc.PC(Nil{}, q, q, Nil{}, Nil{})}, Con{p, Nil{}}, pc.Afull(p, Nil{}, q, q, Nil{}, Nil{})(pc.eq_true(B.len(p), 1n+q)(e)), pc.con2(List<&2, U32>, O.cr.oct.rev(O.cr.oct.rev(p, Nil{}), Nil{}), p, Nil{}, Nil{}, pc.rr(p), {==}))
    case False{}:
      e => h1 => h2 => pc.lastx(p, q)(h1)(pc.le_neq(B.len(p), q)(h2)(e))

# the pieces of well-formed pieces joined are those pieces
def pc.L2(+ps: List<&2, List<&2, U32>>, +q: Nat) -> {pc.wfz(1n+q, ps) == True{} : Bool} -> {pc.PC(pc.cl(ps), q, q, Nil{}, Nil{}) == ps : List<&2, List<&2, U32>>}:
  match ps:
    case Nil{}:
      h => {==}
    case Con{+p, +t}:
      match t:
        case Nil{}:
          +h => pc.last(Nat.is_eq(B.len(p), 1n+q), p, q)({==})(pc.and_l(Nat.is_lt(0n, B.len(p)), Nat.is_le(B.len(p), 1n+q))(pc.and_l(Bool.and(Nat.is_lt(0n, B.len(p)), Nat.is_le(B.len(p), 1n+q)), True{})(h)))(pc.and_r(Nat.is_lt(0n, B.len(p)), Nat.is_le(B.len(p), 1n+q))(pc.and_l(Bool.and(Nat.is_lt(0n, B.len(p)), Nat.is_le(B.len(p), 1n+q)), True{})(h)))
        case Con{+a, +b}:
          +h => Equal.trans(List<&2, List<&2, U32>>, pc.PC(B.append(p, pc.cl(t)), q, q, Nil{}, Nil{}), Con{O.cr.oct.rev(O.cr.oct.rev(p, Nil{}), Nil{}), pc.PC(pc.cl(t), q, q, Nil{}, Nil{})}, Con{p, t}, pc.Afull(p, pc.cl(t), q, q, Nil{}, Nil{})(pc.eq_true(B.len(p), 1n+q)(pc.and_l(Nat.is_eq(B.len(p), 1n+q), pc.wfz(1n+q, t))(h))), pc.con2(List<&2, U32>, O.cr.oct.rev(O.cr.oct.rev(p, Nil{}), Nil{}), p, pc.PC(pc.cl(t), q, q, Nil{}, Nil{}), t, pc.rr(p), pc.L2(t, q)(pc.and_r(Nat.is_eq(B.len(p), 1n+q), pc.wfz(1n+q, t))(h))))

# XOR of byte lists (octets.bend's cr.oct.xorl: over the first list's
# length, a missing byte of the second counting as 0)

def pc.xlen(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.len(O.cr.oct.xorl(a, b)) == B.len(a) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      match b:
        case Nil{}:
          %pc.xlen(t, Nil{}) : {1n+B.len(O.cr.oct.xorl(t, Nil{})) == 1n+_ : Nat}
          {==}
        case Con{+y, +u}:
          %pc.xlen(t, u) : {1n+B.len(O.cr.oct.xorl(t, u)) == 1n+_ : Nat}
          {==}

# XOR with the same bytes twice, masked, changes nothing
def pc.xx(+a: List<&2, U32>, +v: List<&2, U32>) -> {B.mask(O.cr.oct.xorl(B.mask(O.cr.oct.xorl(a, v)), v)) == B.mask(a) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      match v:
        case Nil{}:
          pc.con2(U32, B.byte(U32.xor(B.byte(U32.xor(x, 0)), 0)), B.byte(x), B.mask(O.cr.oct.xorl(B.mask(O.cr.oct.xorl(t, Nil{})), Nil{})), B.mask(t), Equal.sym(U32, B.byte(x), B.byte(U32.xor(B.byte(U32.xor(x, 0)), 0)), Bits.byte_xx(x, 0)), pc.xx(t, Nil{}))
        case Con{+w, +u}:
          pc.con2(U32, B.byte(U32.xor(B.byte(U32.xor(x, w)), w)), B.byte(x), B.mask(O.cr.oct.xorl(B.mask(O.cr.oct.xorl(t, u)), u)), B.mask(t), Equal.sym(U32, B.byte(x), B.byte(U32.xor(B.byte(U32.xor(x, w)), w)), Bits.byte_xx(x, w)), pc.xx(t, u))

def pc.drop_nil(+n: Nat) -> {B.drop(n, Nil{}) == Nil{} : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# XOR of a joined list: each part against its own bytes of x
def pc.xa(+a: List<&2, U32>, +b: List<&2, U32>, +x: List<&2, U32>) -> {O.cr.oct.xorl(B.append(a, b), x) == B.append(O.cr.oct.xorl(a, x), O.cr.oct.xorl(b, B.drop(B.len(a), x))) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      match x:
        case Nil{}:
          %pc.drop_nil(B.len(t)) : {Con{U32.xor(h, 0), O.cr.oct.xorl(B.append(t, b), Nil{})} == Con{U32.xor(h, 0), B.append(O.cr.oct.xorl(t, Nil{}), O.cr.oct.xorl(b, _))} : List<&2, U32>}
          %pc.xa(t, b, Nil{}) : {Con{U32.xor(h, 0), O.cr.oct.xorl(B.append(t, b), Nil{})} == Con{U32.xor(h, 0), _} : List<&2, U32>}
          {==}
        case Con{+y, +u}:
          %pc.xa(t, b, u) : {Con{U32.xor(h, y), O.cr.oct.xorl(B.append(t, b), u)} == Con{U32.xor(h, y), _} : List<&2, U32>}
          {==}

# XOR with zeros, over a list of their length, is that list
def pc.xz(+k: Nat, +y: List<&2, U32>) -> {B.len(y) == k : Nat} -> {O.cr.oct.xorl(B.zeros(k), y) == y : List<&2, U32>}:
  match k:
    case 0n:
      match y:
        case Nil{}:
          h => {==}
        case Con{+a, +t}:
          h => Empty.absurd({Nil{} == Con{a, t} : List<&2, U32>}, pc.nd(B.len(t), h))
    case 1n+kp:
      match y:
        case Nil{}:
          h => Empty.absurd({O.cr.oct.xorl(B.zeros(1n+kp), Nil{}) == Nil{} : List<&2, U32>}, pc.nd(kp, Equal.sym(Nat, 0n, 1n+kp, h)))
        case Con{+a, +t}:
          h => pc.con2(U32, U32.xor(0, a), a, O.cr.oct.xorl(B.zeros(kp), t), t, Bits.u32_xor0(a), pc.xz(kp, t)(Equal.cong(Nat, Nat, w => pc.pred(w), 1n+B.len(t), 1n+kp, h)))

# XOR reads b only over a's length
def pc.xt(+a: List<&2, U32>, +b: List<&2, U32>) -> {O.cr.oct.xorl(a, b) == O.cr.oct.xorl(a, B.take(B.len(a), b)) : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      match b:
        case Nil{}:
          {==}
        case Con{+y, +u}:
          %pc.xt(t, u) : {Con{U32.xor(x, y), O.cr.oct.xorl(t, u)} == Con{U32.xor(x, y), _} : List<&2, U32>}
          {==}

# Lists: take and drop of a joined list, the length of a drop

def pc.take_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.take(B.len(a), B.append(a, b)) == a : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %pc.take_append(t, b) : {Con{h, B.take(B.len(t), B.append(t, b))} == Con{h, _} : List<&2, U32>}
      {==}

def pc.drop_append(+a: List<&2, U32>, +b: List<&2, U32>) -> {B.drop(B.len(a), B.append(a, b)) == b : List<&2, U32>}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      pc.drop_append(t, b)

def pc.len_drop(+n: Nat, +xs: List<&2, U32>) -> {B.len(B.drop(n, xs)) == Nat.sub(B.len(xs), n) : Nat}:
  match n:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case Con{+h, +t}:
          {==}
    case 1n+p:
      match xs:
        case Nil{}:
          {==}
        case Con{+h, +t}:
          pc.len_drop(p, t)

# Octets

def pc.ofmask(+xs: List<&2, U32>) -> {B.Octets.of_list(B.mask(xs)) == B.Octets.of_list(xs) : B.Octets}:
  Equal.trans(B.Octets, B.Octets.of_list(B.mask(xs)), B.Octets.of_list(B.Octets.to_list(B.Octets.of_list(xs))), B.Octets.of_list(xs), Equal.cong(List<&2, U32>, B.Octets, l => B.Octets.of_list(l), B.mask(xs), B.Octets.to_list(B.Octets.of_list(xs)), Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(xs)), B.mask(xs), BL.octets_to_of(xs))), BL.octets_of_list_idempotent(xs))

# the length of an Octets' list, and of an XOR
def pc.olen(+o: B.Octets) -> {B.len(B.Octets.to_list(o)) == B.Octets.len(o) : Nat}:
  Equal.sym(Nat, B.Octets.len(o), B.len(B.Octets.to_list(o)), BL.octets_len_list(o))

def pc.xolen(+a: B.Octets, +b: B.Octets) -> {B.Octets.len(O.CrOct.xor(a, b)) == B.Octets.len(a) : Nat}:
  Equal.trans(Nat, B.Octets.len(O.CrOct.xor(a, b)), B.len(O.cr.oct.xorl(B.Octets.to_list(a), B.Octets.to_list(b))), B.Octets.len(a), BL.octets_len_of_list(O.cr.oct.xorl(B.Octets.to_list(a), B.Octets.to_list(b))), Equal.trans(Nat, B.len(O.cr.oct.xorl(B.Octets.to_list(a), B.Octets.to_list(b))), B.len(B.Octets.to_list(a)), B.Octets.len(a), pc.xlen(B.Octets.to_list(a), B.Octets.to_list(b)), pc.olen(a)))

# a XOR v XOR v is a
def pc.ox(+a: B.Octets, +v: B.Octets) -> {O.CrOct.xor(O.CrOct.xor(a, v), v) == a : B.Octets}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(a), B.Octets.to_list(v)))), B.mask(O.cr.oct.xorl(B.Octets.to_list(a), B.Octets.to_list(v))), BL.octets_to_of(O.cr.oct.xorl(B.Octets.to_list(a), B.Octets.to_list(v)))) : {B.Octets.of_list(O.cr.oct.xorl(_, B.Octets.to_list(v))) == a : B.Octets}
  %pc.ofmask(O.cr.oct.xorl(B.mask(O.cr.oct.xorl(B.Octets.to_list(a), B.Octets.to_list(v))), B.Octets.to_list(v))) : {_ == a : B.Octets}
  %Equal.sym(List<&2, U32>, B.mask(O.cr.oct.xorl(B.mask(O.cr.oct.xorl(B.Octets.to_list(a), B.Octets.to_list(v))), B.Octets.to_list(v))), B.mask(B.Octets.to_list(a)), pc.xx(B.Octets.to_list(a), B.Octets.to_list(v))) : {B.Octets.of_list(_) == a : B.Octets}
  %Equal.sym(B.Octets, B.Octets.of_list(B.mask(B.Octets.to_list(a))), B.Octets.of_list(B.Octets.to_list(a)), pc.ofmask(B.Octets.to_list(a))) : {_ == a : B.Octets}
  BL.octets_of_to(a)

# the list forms of take and drop, within the length
def pc.ttake(+d: Nat, +x: B.Octets, h: {Nat.is_le(d, B.Octets.len(x)) == True{} : Bool}) -> {B.take(d, B.Octets.to_list(x)) == B.Octets.to_list(B.Octets.take(d, x)) : List<&2, U32>}:
  +lt = Equal.trans(Nat, B.len(B.Octets.to_list(B.Octets.take(d, x))), B.Octets.len(B.Octets.take(d, x)), d, pc.olen(B.Octets.take(d, x)), BL.octets_len_take_le(d, x, h))
  %BL.octets_take_drop(d, x) : {B.take(d, B.Octets.to_list(_)) == B.Octets.to_list(B.Octets.take(d, x)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.take(d, x), B.Octets.drop(d, x))), B.append(B.Octets.to_list(B.Octets.take(d, x)), B.Octets.to_list(B.Octets.drop(d, x))), BL.octets_append_list(B.Octets.take(d, x), B.Octets.drop(d, x))) : {B.take(d, _) == B.Octets.to_list(B.Octets.take(d, x)) : List<&2, U32>}
  %lt : {B.take(_, B.append(B.Octets.to_list(B.Octets.take(d, x)), B.Octets.to_list(B.Octets.drop(d, x)))) == B.Octets.to_list(B.Octets.take(d, x)) : List<&2, U32>}
  pc.take_append(B.Octets.to_list(B.Octets.take(d, x)), B.Octets.to_list(B.Octets.drop(d, x)))

def pc.tdrop(+d: Nat, +x: B.Octets, h: {Nat.is_le(d, B.Octets.len(x)) == True{} : Bool}) -> {B.drop(d, B.Octets.to_list(x)) == B.Octets.to_list(B.Octets.drop(d, x)) : List<&2, U32>}:
  +lt = Equal.trans(Nat, B.len(B.Octets.to_list(B.Octets.take(d, x))), B.Octets.len(B.Octets.take(d, x)), d, pc.olen(B.Octets.take(d, x)), BL.octets_len_take_le(d, x, h))
  %BL.octets_take_drop(d, x) : {B.drop(d, B.Octets.to_list(_)) == B.Octets.to_list(B.Octets.drop(d, x)) : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(B.Octets.take(d, x), B.Octets.drop(d, x))), B.append(B.Octets.to_list(B.Octets.take(d, x)), B.Octets.to_list(B.Octets.drop(d, x))), BL.octets_append_list(B.Octets.take(d, x), B.Octets.drop(d, x))) : {B.drop(d, _) == B.Octets.to_list(B.Octets.drop(d, x)) : List<&2, U32>}
  %lt : {B.drop(_, B.append(B.Octets.to_list(B.Octets.take(d, x)), B.Octets.to_list(B.Octets.drop(d, x)))) == B.Octets.to_list(B.Octets.drop(d, x)) : List<&2, U32>}
  pc.drop_append(B.Octets.to_list(B.Octets.take(d, x)), B.Octets.to_list(B.Octets.drop(d, x)))

# Q zero-padded, XOR x: Q's part and the zeros' part
def pc.xsplit(+q: B.Octets, +z: B.Octets, +x: B.Octets) -> {O.CrOct.xor(B.Octets.append(q, z), x) == B.Octets.append(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(z), B.drop(B.len(B.Octets.to_list(q)), B.Octets.to_list(x))))) : B.Octets}:
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(q, z)), B.append(B.Octets.to_list(q), B.Octets.to_list(z)), BL.octets_append_list(q, z)) : {B.Octets.of_list(O.cr.oct.xorl(_, B.Octets.to_list(x))) == B.Octets.append(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(z), B.drop(B.len(B.Octets.to_list(q)), B.Octets.to_list(x))))) : B.Octets}
  %Equal.sym(List<&2, U32>, O.cr.oct.xorl(B.append(B.Octets.to_list(q), B.Octets.to_list(z)), B.Octets.to_list(x)), B.append(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x)), O.cr.oct.xorl(B.Octets.to_list(z), B.drop(B.len(B.Octets.to_list(q)), B.Octets.to_list(x)))), pc.xa(B.Octets.to_list(q), B.Octets.to_list(z), B.Octets.to_list(x))) : {B.Octets.of_list(_) == B.Octets.append(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(z), B.drop(B.len(B.Octets.to_list(q)), B.Octets.to_list(x))))) : B.Octets}
  Bits.octets_of_append(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x)), O.cr.oct.xorl(B.Octets.to_list(z), B.drop(B.len(B.Octets.to_list(q)), B.Octets.to_list(x))))

# the length of Q's part is Q's length
def pc.ulen(+q: B.Octets, +x: B.Octets) -> {B.Octets.len(q) == B.Octets.len(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x)))) : Nat}:
  Equal.sym(Nat, B.Octets.len(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x)))), B.Octets.len(q), Equal.trans(Nat, B.Octets.len(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x)))), B.len(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.Octets.len(q), BL.octets_len_of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), Equal.trans(Nat, B.len(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.len(B.Octets.to_list(q)), B.Octets.len(q), pc.xlen(B.Octets.to_list(q), B.Octets.to_list(x)), pc.olen(q))))

# the stolen bytes: past Q, the XOR with zeros is x's own bytes
def pc.xdz(+q: B.Octets, +n: Nat, +x: B.Octets, hq: {Nat.is_le(B.Octets.len(q), n) == True{} : Bool}, +hx: {B.Octets.len(x) == n : Nat}) -> {B.Octets.drop(B.Octets.len(q), O.CrOct.xor(B.Octets.append(q, B.Octets.zeros(Nat.sub(n, B.Octets.len(q)))), x)) == B.Octets.drop(B.Octets.len(q), x) : B.Octets}:
  +hqx = Equal.trans(Bool, Nat.is_le(B.Octets.len(q), B.Octets.len(x)), Nat.is_le(B.Octets.len(q), n), True{}, Equal.cong(Nat, Bool, w => Nat.is_le(B.Octets.len(q), w), B.Octets.len(x), n, hx), hq)
  %Equal.sym(B.Octets, O.CrOct.xor(B.Octets.append(q, B.Octets.zeros(Nat.sub(n, B.Octets.len(q)))), x), B.Octets.append(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(B.Octets.zeros(Nat.sub(n, B.Octets.len(q)))), B.drop(B.len(B.Octets.to_list(q)), B.Octets.to_list(x))))), pc.xsplit(q, B.Octets.zeros(Nat.sub(n, B.Octets.len(q))), x)) : {B.Octets.drop(B.Octets.len(q), _) == B.Octets.drop(B.Octets.len(q), x) : B.Octets}
  %Equal.sym(Nat, B.Octets.len(q), B.Octets.len(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x)))), pc.ulen(q, x)) : {B.Octets.drop(_, B.Octets.append(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(B.Octets.zeros(Nat.sub(n, B.Octets.len(q)))), B.drop(B.len(B.Octets.to_list(q)), B.Octets.to_list(x)))))) == B.Octets.drop(B.Octets.len(q), x) : B.Octets}
  %Equal.sym(B.Octets, B.Octets.drop(B.Octets.len(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x)))), B.Octets.append(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(B.Octets.zeros(Nat.sub(n, B.Octets.len(q)))), B.drop(B.len(B.Octets.to_list(q)), B.Octets.to_list(x)))))), B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(B.Octets.zeros(Nat.sub(n, B.Octets.len(q)))), B.drop(B.len(B.Octets.to_list(q)), B.Octets.to_list(x)))), BL.octets_drop_append(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(B.Octets.zeros(Nat.sub(n, B.Octets.len(q)))), B.drop(B.len(B.Octets.to_list(q)), B.Octets.to_list(x)))))) : {_ == B.Octets.drop(B.Octets.len(q), x) : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.zeros(Nat.sub(n, B.Octets.len(q)))), B.zeros(Nat.sub(n, B.Octets.len(q))), BL.octets_zeros_list(Nat.sub(n, B.Octets.len(q)))) : {B.Octets.of_list(O.cr.oct.xorl(_, B.drop(B.len(B.Octets.to_list(q)), B.Octets.to_list(x)))) == B.Octets.drop(B.Octets.len(q), x) : B.Octets}
  %Equal.sym(Nat, B.len(B.Octets.to_list(q)), B.Octets.len(q), pc.olen(q)) : {B.Octets.of_list(O.cr.oct.xorl(B.zeros(Nat.sub(n, B.Octets.len(q))), B.drop(_, B.Octets.to_list(x)))) == B.Octets.drop(B.Octets.len(q), x) : B.Octets}
  # past Q, x has n - len(Q) bytes
  %Equal.sym(List<&2, U32>, O.cr.oct.xorl(B.zeros(Nat.sub(n, B.Octets.len(q))), B.drop(B.Octets.len(q), B.Octets.to_list(x))), B.drop(B.Octets.len(q), B.Octets.to_list(x)), pc.xz(Nat.sub(n, B.Octets.len(q)), B.drop(B.Octets.len(q), B.Octets.to_list(x)))(Equal.trans(Nat, B.len(B.drop(B.Octets.len(q), B.Octets.to_list(x))), Nat.sub(B.len(B.Octets.to_list(x)), B.Octets.len(q)), Nat.sub(n, B.Octets.len(q)), pc.len_drop(B.Octets.len(q), B.Octets.to_list(x)), Equal.cong(Nat, Nat, w => Nat.sub(w, B.Octets.len(q)), B.len(B.Octets.to_list(x)), n, Equal.trans(Nat, B.len(B.Octets.to_list(x)), B.Octets.len(x), n, pc.olen(x), hx))))) : {B.Octets.of_list(_) == B.Octets.drop(B.Octets.len(q), x) : B.Octets}
  %Equal.sym(List<&2, U32>, B.drop(B.Octets.len(q), B.Octets.to_list(x)), B.Octets.to_list(B.Octets.drop(B.Octets.len(q), x)), pc.tdrop(B.Octets.len(q), x, hqx)) : {B.Octets.of_list(_) == B.Octets.drop(B.Octets.len(q), x) : B.Octets}
  BL.octets_of_to(B.Octets.drop(B.Octets.len(q), x))

# the last piece: the first len(Q) bytes, XOR x's, are Q
def pc.xtz(+q: B.Octets, +n: Nat, +x: B.Octets, hq: {Nat.is_le(B.Octets.len(q), n) == True{} : Bool}, hx: {B.Octets.len(x) == n : Nat}) -> {O.CrOct.xor(B.Octets.take(B.Octets.len(q), O.CrOct.xor(B.Octets.append(q, B.Octets.zeros(Nat.sub(n, B.Octets.len(q)))), x)), B.Octets.take(B.Octets.len(q), x)) == q : B.Octets}:
  +hqx = Equal.trans(Bool, Nat.is_le(B.Octets.len(q), B.Octets.len(x)), Nat.is_le(B.Octets.len(q), n), True{}, Equal.cong(Nat, Bool, w => Nat.is_le(B.Octets.len(q), w), B.Octets.len(x), n, hx), hq)
  %Equal.sym(B.Octets, O.CrOct.xor(B.Octets.append(q, B.Octets.zeros(Nat.sub(n, B.Octets.len(q)))), x), B.Octets.append(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(B.Octets.zeros(Nat.sub(n, B.Octets.len(q)))), B.drop(B.len(B.Octets.to_list(q)), B.Octets.to_list(x))))), pc.xsplit(q, B.Octets.zeros(Nat.sub(n, B.Octets.len(q))), x)) : {O.CrOct.xor(B.Octets.take(B.Octets.len(q), _), B.Octets.take(B.Octets.len(q), x)) == q : B.Octets}
  %Equal.sym(Nat, B.Octets.len(q), B.Octets.len(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x)))), pc.ulen(q, x)) : {O.CrOct.xor(B.Octets.take(_, B.Octets.append(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(B.Octets.zeros(Nat.sub(n, B.Octets.len(q)))), B.drop(B.len(B.Octets.to_list(q)), B.Octets.to_list(x)))))), B.Octets.take(B.Octets.len(q), x)) == q : B.Octets}
  %Equal.sym(B.Octets, B.Octets.take(B.Octets.len(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x)))), B.Octets.append(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(B.Octets.zeros(Nat.sub(n, B.Octets.len(q)))), B.drop(B.len(B.Octets.to_list(q)), B.Octets.to_list(x)))))), B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), BL.octets_take_append(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(B.Octets.zeros(Nat.sub(n, B.Octets.len(q)))), B.drop(B.len(B.Octets.to_list(q)), B.Octets.to_list(x)))))) : {O.CrOct.xor(_, B.Octets.take(B.Octets.len(q), x)) == q : B.Octets}
  # x's bytes over Q's length
  %pc.ttake(B.Octets.len(q), x, hqx) : {B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x)))), _)) == q : B.Octets}
  %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.of_list(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x)))), B.mask(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), BL.octets_to_of(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x)))) : {B.Octets.of_list(O.cr.oct.xorl(_, B.take(B.Octets.len(q), B.Octets.to_list(x)))) == q : B.Octets}
  # which the XOR reads anyway
  +lm = Equal.trans(Nat, B.len(B.mask(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x)))), B.len(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.Octets.len(q), Bits.mask_len(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), Equal.trans(Nat, B.len(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.len(B.Octets.to_list(q)), B.Octets.len(q), pc.xlen(B.Octets.to_list(q), B.Octets.to_list(x)), pc.olen(q)))
  %lm : {B.Octets.of_list(O.cr.oct.xorl(B.mask(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.take(_, B.Octets.to_list(x)))) == q : B.Octets}
  %pc.xt(B.mask(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.Octets.to_list(x)) : {B.Octets.of_list(_) == q : B.Octets}
  %pc.ofmask(O.cr.oct.xorl(B.mask(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.Octets.to_list(x))) : {_ == q : B.Octets}
  %Equal.sym(List<&2, U32>, B.mask(O.cr.oct.xorl(B.mask(O.cr.oct.xorl(B.Octets.to_list(q), B.Octets.to_list(x))), B.Octets.to_list(x))), B.mask(B.Octets.to_list(q)), pc.xx(B.Octets.to_list(q), B.Octets.to_list(x))) : {B.Octets.of_list(_) == q : B.Octets}
  %Equal.sym(B.Octets, B.Octets.of_list(B.mask(B.Octets.to_list(q))), B.Octets.of_list(B.Octets.to_list(q)), pc.ofmask(B.Octets.to_list(q))) : {_ == q : B.Octets}
  BL.octets_of_to(q)

# The modes' pieces, structurally (cts.bend's enc.go and dec.go without
# their accumulators; n the block size)

def pc.E(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +n: Nat, +ps: List<&2, List<&2, U32>>, +k: K, +v: B.Octets) -> List<&2, B.Octets>:
  match ps:
    case Con{p, t}:
      match t:
        case Con{q, u}:
          match u:
            case Nil{}:
              +x = Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))
              +last = B.Octets.of_list(q)
              +d = B.Octets.len(last)
              Con{Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.append(last, B.Octets.zeros(Nat.sub(n, d))), x)), Con{B.Octets.take(d, x), Nil{}}}
            case Con{r, w}:
              +c = Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))
              Con{c, pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, n, Con{q, Con{r, w}}, k, c)}
        case Nil{}:
          Con{Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)), Nil{}}
    case Nil{}:
      Nil{}

def pc.D(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +ps: List<&2, List<&2, U32>>, +k: K, +v: B.Octets) -> List<&2, B.Octets>:
  match ps:
    case Con{p, t}:
      match t:
        case Con{q, u}:
          match u:
            case Nil{}:
              +cn = B.Octets.of_list(p)
              +xs = B.Octets.of_list(q)
              +d = B.Octets.len(xs)
              +z = Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, cn)
              +x = B.Octets.append(xs, B.Octets.drop(d, z))
              +pn = O.CrOct.xor(B.Octets.take(d, z), xs)
              Con{O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, x), v), Con{pn, Nil{}}}
            case Con{r, w}:
              +c = B.Octets.of_list(p)
              Con{O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, c), v), pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, Con{q, Con{r, w}}, k, c)}
        case Nil{}:
          Con{O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, B.Octets.of_list(p)), v), Nil{}}
    case Nil{}:
      Nil{}

# the inputs of the encryption's block calls, in order
def pc.oes(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +n: Nat, +ps: List<&2, List<&2, U32>>, +k: K, +v: B.Octets) -> List<&2, B.Octets>:
  match ps:
    case Con{p, t}:
      match t:
        case Con{q, u}:
          match u:
            case Nil{}:
              +o1 = O.CrOct.xor(B.Octets.of_list(p), v)
              +x = Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, o1)
              +last = B.Octets.of_list(q)
              Con{o1, Con{O.CrOct.xor(B.Octets.append(last, B.Octets.zeros(Nat.sub(n, B.Octets.len(last)))), x), Nil{}}}
            case Con{r, w}:
              +o1 = O.CrOct.xor(B.Octets.of_list(p), v)
              Con{o1, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, n, Con{q, Con{r, w}}, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, o1))}
        case Nil{}:
          Con{O.CrOct.xor(B.Octets.of_list(p), v), Nil{}}
    case Nil{}:
      Nil{}

# each input decrypted after encrypting, and each output's length
def pc.brs(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +os: List<&2, B.Octets>, +k: K) -> List<&2, B.Octets>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      Con{Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, o)), pc.brs(~K, ~Blk, ~enc, ~dec, ~blk_of, ~blk_to, t, k)}

def pc.bls(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +os: List<&2, B.Octets>, +k: K) -> List<&2, Nat>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      Con{B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, o)), pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, t, k)}

def pc.lns(+os: List<&2, B.Octets>) -> List<&2, Nat>:
  match os:
    case Nil{}:
      Nil{}
    case Con{+o, t}:
      Con{B.Octets.len(o), pc.lns(t)}

def pc.tls(+os: List<&2, B.Octets>) -> List<&2, List<&2, U32>>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      Con{B.Octets.to_list(o), pc.tls(t)}

def pc.ofs(+ps: List<&2, List<&2, U32>>) -> List<&2, B.Octets>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Con{B.Octets.of_list(p), pc.ofs(t)}

def pc.ohd(+l: List<&2, B.Octets>) -> B.Octets:
  match l:
    case Nil{}:
      B.Octets.empty()
    case Con{x, t}:
      x

def pc.otl(+l: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match l:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

def pc.nhd(+l: List<&2, Nat>) -> Nat:
  match l:
    case Nil{}:
      0n
    case Con{x, t}:
      x

def pc.ntl(+l: List<&2, Nat>) -> List<&2, Nat>:
  match l:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

def pc.ohd_eq(+x: B.Octets, +y: B.Octets, +t: List<&2, B.Octets>, +u: List<&2, B.Octets>, h: {Con{x, t} == Con{y, u} : List<&2, B.Octets>}) -> {x == y : B.Octets}:
  Equal.cong(List<&2, B.Octets>, B.Octets, l => pc.ohd(l), Con{x, t}, Con{y, u}, h)

def pc.otl_eq(+x: B.Octets, +y: B.Octets, +t: List<&2, B.Octets>, +u: List<&2, B.Octets>, h: {Con{x, t} == Con{y, u} : List<&2, B.Octets>}) -> {t == u : List<&2, B.Octets>}:
  Equal.cong(List<&2, B.Octets>, List<&2, B.Octets>, l => pc.otl(l), Con{x, t}, Con{y, u}, h)

def pc.nhd_eq(+x: Nat, +y: Nat, +t: List<&2, Nat>, +u: List<&2, Nat>, h: {Con{x, t} == Con{y, u} : List<&2, Nat>}) -> {x == y : Nat}:
  Equal.cong(List<&2, Nat>, Nat, l => pc.nhd(l), Con{x, t}, Con{y, u}, h)

def pc.ntl_eq(+x: Nat, +y: Nat, +t: List<&2, Nat>, +u: List<&2, Nat>, h: {Con{x, t} == Con{y, u} : List<&2, Nat>}) -> {t == u : List<&2, Nat>}:
  Equal.cong(List<&2, Nat>, List<&2, Nat>, l => pc.ntl(l), Con{x, t}, Con{y, u}, h)

# the loops are the structural forms

def pc.enc_E(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +ps: List<&2, List<&2, U32>>, +k: K, +v: B.Octets, +acc: List<&2, B.Octets>) -> {Ct.cr.cts.enc.go(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, ps, k, v, acc) == B.Octets.concat(Ct.cr.cts.rcat(acc, pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, bsize, ps, k, v))) : B.Octets}:
  match ps:
    case Con{p, t}:
      match t:
        case Con{q, u}:
          match u:
            case Nil{}:
              {==}
            case Con{r, w}:
              pc.enc_E(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, Con{q, Con{r, w}}, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)), Con{Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)), acc})
        case Nil{}:
          {==}
    case Nil{}:
      {==}

def pc.dec_D(~K: Data, ~Blk: Data, ~bsize: Nat, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +ps: List<&2, List<&2, U32>>, +k: K, +v: B.Octets, +acc: List<&2, B.Octets>) -> {Ct.cr.cts.dec.go(~K, ~Blk, ~bsize, ~dec, ~blk_of, ~blk_to, ps, k, v, acc) == B.Octets.concat(Ct.cr.cts.rcat(acc, pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, ps, k, v))) : B.Octets}:
  match ps:
    case Con{+p, t}:
      match t:
        case Con{q, u}:
          match u:
            case Nil{}:
              {==}
            case Con{r, w}:
              pc.dec_D(~K, ~Blk, ~bsize, ~dec, ~blk_of, ~blk_to, Con{q, Con{r, w}}, k, B.Octets.of_list(p), Con{O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, B.Octets.of_list(p)), v), acc})
        case Nil{}:
          {==}
    case Nil{}:
      {==}

# Octets lists joined

def pc.cl_tls(+os: List<&2, B.Octets>) -> {pc.cl(pc.tls(os)) == B.Octets.to_list(B.Octets.concat(os)) : List<&2, U32>}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +t}:
      %Equal.sym(B.Octets, B.Octets.concat(Con{o, t}), B.Octets.append(o, B.Octets.concat(t)), BL.octets_concat_cons(o, t)) : {pc.cl(pc.tls(Con{o, t})) == B.Octets.to_list(_) : List<&2, U32>}
      %Equal.sym(List<&2, U32>, B.Octets.to_list(B.Octets.append(o, B.Octets.concat(t))), B.append(B.Octets.to_list(o), B.Octets.to_list(B.Octets.concat(t))), BL.octets_append_list(o, B.Octets.concat(t))) : {pc.cl(pc.tls(Con{o, t})) == _ : List<&2, U32>}
      %pc.cl_tls(t) : {B.append(B.Octets.to_list(o), pc.cl(pc.tls(t))) == B.append(B.Octets.to_list(o), _) : List<&2, U32>}
      {==}

def pc.cat_ofs(+ps: List<&2, List<&2, U32>>) -> {B.Octets.concat(pc.ofs(ps)) == B.Octets.of_list(pc.cl(ps)) : B.Octets}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      %Equal.sym(B.Octets, B.Octets.concat(Con{B.Octets.of_list(p), pc.ofs(t)}), B.Octets.append(B.Octets.of_list(p), B.Octets.concat(pc.ofs(t))), BL.octets_concat_cons(B.Octets.of_list(p), pc.ofs(t))) : {_ == B.Octets.of_list(pc.cl(Con{p, t})) : B.Octets}
      %Equal.sym(B.Octets, B.Octets.concat(pc.ofs(t)), B.Octets.of_list(pc.cl(t)), pc.cat_ofs(t)) : {B.Octets.append(B.Octets.of_list(p), _) == B.Octets.of_list(pc.cl(Con{p, t})) : B.Octets}
      Equal.sym(B.Octets, B.Octets.of_list(B.append(p, pc.cl(t))), B.Octets.append(B.Octets.of_list(p), B.Octets.of_list(pc.cl(t))), Bits.octets_of_append(p, pc.cl(t)))

# Decryption gives the pieces back

def pc.ge2(l: List<&2, List<&2, U32>>) -> Bool:
  match l:
    case Nil{}:
      False{}
    case Con{a, t}:
      match t:
        case Nil{}:
          False{}
        case Con{b, u}:
          True{}

def pc.ge2_cons(+a: List<&2, U32>, x: List<&2, List<&2, U32>>) -> {pc.ge2(x) == True{} : Bool} -> {pc.ge2(Con{a, x}) == True{} : Bool}:
  match x:
    case Nil{}:
      h => h
    case Con{b, u}:
      h => {==}

# the pieces of two or more pieces' encryption are two or more
def pc.E_ge2(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +n: Nat, w: List<&2, List<&2, U32>>, +q: List<&2, U32>, +r: List<&2, U32>, +k: K, +c: B.Octets) -> {pc.ge2(pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, n, Con{q, Con{r, w}}, k, c))) == True{} : Bool}:
  match w:
    case Nil{}:
      {==}
    case Con{+s, +w2}:
      pc.ge2_cons(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(q), c))), pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, n, Con{r, Con{s, w2}}, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(q), c)))))(pc.E_ge2(~K, ~Blk, ~enc, ~blk_of, ~blk_to, n, w2, r, s, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(q), c))))

def pc.D_cons(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +a: List<&2, U32>, r: List<&2, List<&2, U32>>, +k: K, +v: B.Octets) -> {pc.ge2(r) == True{} : Bool} -> {pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, Con{a, r}, k, v) == Con{O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, B.Octets.of_list(a)), v), pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, r, k, B.Octets.of_list(a))} : List<&2, B.Octets>}:
  match r:
    case Nil{}:
      h => pc.absurd({pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, Con{a, Nil{}}, k, v) == Con{O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, B.Octets.of_list(a)), v), Nil{}} : List<&2, B.Octets>}, h)
    case Con{+r1, r2}:
      match r2:
        case Nil{}:
          h => pc.absurd({pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, Con{a, Con{r1, Nil{}}}, k, v) == Con{O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, B.Octets.of_list(a)), v), pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, Con{r1, Nil{}}, k, B.Octets.of_list(a))} : List<&2, B.Octets>}, h)
        case Con{r3, r4}:
          h => {==}

# one piece decrypted after encrypting
def pc.dstep(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +pp: B.Octets, +v: B.Octets, h: {Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(pp, v))) == O.CrOct.xor(pp, v) : B.Octets}) -> {O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, B.Octets.of_list(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(pp, v))))), v) == pp : B.Octets}:
  Equal.trans(B.Octets, O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, B.Octets.of_list(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(pp, v))))), v), O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(pp, v))), v), pp, Equal.cong(B.Octets, B.Octets, w => O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, w), v), B.Octets.of_list(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(pp, v)))), Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(pp, v)), BL.octets_of_to(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(pp, v)))), Equal.trans(B.Octets, O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(pp, v))), v), O.CrOct.xor(O.CrOct.xor(pp, v), v), pp, Equal.cong(B.Octets, B.Octets, w => O.CrOct.xor(w, v), Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(pp, v))), O.CrOct.xor(pp, v), h), pc.ox(pp, v)))

# a piece's encryption has its length
def pc.clen(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +p: List<&2, U32>, +v: B.Octets, h: {B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))) == B.Octets.len(O.CrOct.xor(B.Octets.of_list(p), v)) : Nat}) -> {B.len(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))) == B.len(p) : Nat}:
  Equal.trans(Nat, B.len(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))), B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), B.len(p), pc.olen(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), Equal.trans(Nat, B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), B.Octets.len(O.CrOct.xor(B.Octets.of_list(p), v)), B.len(p), h, Equal.trans(Nat, B.Octets.len(O.CrOct.xor(B.Octets.of_list(p), v)), B.Octets.len(B.Octets.of_list(p)), B.len(p), pc.xolen(B.Octets.of_list(p), v), BL.octets_len_of_list(p))))

# two pieces, the last stolen
def pc.D3(~K: Data, ~Blk: Data, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +v: B.Octets, +xs: B.Octets, +d: Nat, +z: B.Octets) -> List<&2, B.Octets>:
  Con{O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, B.Octets.append(xs, B.Octets.drop(d, z))), v), Con{O.CrOct.xor(B.Octets.take(d, z), xs), Nil{}}}

# the facts of the two-piece case: its x has 1 + q bytes, Q at most that
def pc.hx2(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +q: Nat, +k: K, +p: List<&2, U32>, +v: B.Octets, ep: {B.len(p) == 1n+q : Nat}, l1: {B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))) == B.Octets.len(O.CrOct.xor(B.Octets.of_list(p), v)) : Nat}) -> {B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))) == 1n+q : Nat}:
  Equal.trans(Nat, B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), B.len(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))), 1n+q, Equal.sym(Nat, B.len(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))), B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), pc.olen(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))), Equal.trans(Nat, B.len(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))), B.len(p), 1n+q, pc.clen(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, p, v, l1), ep))

def pc.hq2(+q: Nat, +r: List<&2, U32>, hq: {Nat.is_le(B.len(r), 1n+q) == True{} : Bool}) -> {Nat.is_le(B.Octets.len(B.Octets.of_list(r)), 1n+q) == True{} : Bool}:
  Equal.trans(Bool, Nat.is_le(B.Octets.len(B.Octets.of_list(r)), 1n+q), Nat.is_le(B.len(r), 1n+q), True{}, Equal.cong(Nat, Bool, w => Nat.is_le(w, 1n+q), B.Octets.len(B.Octets.of_list(r)), B.len(r), BL.octets_len_of_list(r)), hq)

def pc.DE2(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +q: Nat, +p: List<&2, U32>, +r: List<&2, U32>, +k: K, +v: B.Octets, ep: {B.len(p) == 1n+q : Nat}, hq: {Nat.is_le(B.len(r), 1n+q) == True{} : Bool}, +hr: {pc.brs(~K, ~Blk, ~enc, ~dec, ~blk_of, ~blk_to, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{p, Con{r, Nil{}}}, k, v), k) == pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{p, Con{r, Nil{}}}, k, v) : List<&2, B.Octets>}, +hl: {pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{p, Con{r, Nil{}}}, k, v), k) == pc.lns(pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{p, Con{r, Nil{}}}, k, v)) : List<&2, Nat>}) -> {pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{p, Con{r, Nil{}}}, k, v)), k, v) == pc.ofs(Con{p, Con{r, Nil{}}}) : List<&2, B.Octets>}:
  # the two block inputs, their outputs, and the two decryptions
  +o1 = O.CrOct.xor(B.Octets.of_list(p), v)
  +x = Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))
  +o2 = O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))
  +cn = Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))))
  +d = B.Octets.len(B.Octets.of_list(r))
  +h1 = pc.ohd_eq(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, x), o1, pc.brs(~K, ~Blk, ~enc, ~dec, ~blk_of, ~blk_to, Con{o2, Nil{}}, k), Con{o2, Nil{}}, hr)
  +h2 = pc.ohd_eq(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, cn), o2, Nil{}, Nil{}, pc.otl_eq(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, x), o1, pc.brs(~K, ~Blk, ~enc, ~dec, ~blk_of, ~blk_to, Con{o2, Nil{}}, k), Con{o2, Nil{}}, hr))
  +l1 = pc.nhd_eq(B.Octets.len(x), B.Octets.len(o1), pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, Con{o2, Nil{}}, k), pc.lns(Con{o2, Nil{}}), hl)
  +hx = pc.hx2(~K, ~Blk, ~enc, ~blk_of, ~blk_to, q, k, p, v, ep, l1)
  +hQ = pc.hq2(q, r, hq)
  +hdx = Equal.trans(Bool, Nat.is_le(d, B.Octets.len(x)), Nat.is_le(d, 1n+q), True{}, Equal.cong(Nat, Bool, w => Nat.is_le(d, w), B.Octets.len(x), 1n+q, hx), hQ)
  # the ciphertext pieces read back
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(cn)), cn, BL.octets_of_to(cn)) : {pc.D3(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, v, B.Octets.of_list(B.Octets.to_list(B.Octets.take(d, x))), B.Octets.len(B.Octets.of_list(B.Octets.to_list(B.Octets.take(d, x)))), Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, _)) == Con{B.Octets.of_list(p), Con{B.Octets.of_list(r), Nil{}}} : List<&2, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.of_list(B.Octets.to_list(B.Octets.take(d, x))), B.Octets.take(d, x), BL.octets_of_to(B.Octets.take(d, x))) : {pc.D3(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, v, _, B.Octets.len(_), Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, cn)) == Con{B.Octets.of_list(p), Con{B.Octets.of_list(r), Nil{}}} : List<&2, B.Octets>}
  %Equal.sym(Nat, B.Octets.len(B.Octets.take(d, x)), d, BL.octets_len_take_le(d, x, hdx)) : {pc.D3(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, v, B.Octets.take(d, x), _, Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, cn)) == Con{B.Octets.of_list(p), Con{B.Octets.of_list(r), Nil{}}} : List<&2, B.Octets>}
  # the last block decrypts to Q zero-padded XOR x
  %Equal.sym(B.Octets, Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, cn), o2, h2) : {pc.D3(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, v, B.Octets.take(d, x), d, _) == Con{B.Octets.of_list(p), Con{B.Octets.of_list(r), Nil{}}} : List<&2, B.Octets>}
  # its bytes past Q are x's: x comes back whole
  %Equal.sym(B.Octets, B.Octets.drop(d, o2), B.Octets.drop(d, x), pc.xdz(B.Octets.of_list(r), 1n+q, x, hQ, hx)) : {Con{O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, B.Octets.append(B.Octets.take(d, x), _)), v), Con{O.CrOct.xor(B.Octets.take(d, o2), B.Octets.take(d, x)), Nil{}}} == Con{B.Octets.of_list(p), Con{B.Octets.of_list(r), Nil{}}} : List<&2, B.Octets>}
  %Equal.sym(B.Octets, B.Octets.append(B.Octets.take(d, x), B.Octets.drop(d, x)), x, BL.octets_take_drop(d, x)) : {Con{O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, _), v), Con{O.CrOct.xor(B.Octets.take(d, o2), B.Octets.take(d, x)), Nil{}}} == Con{B.Octets.of_list(p), Con{B.Octets.of_list(r), Nil{}}} : List<&2, B.Octets>}
  # which decrypts to P XOR v
  %Equal.sym(B.Octets, Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, x), o1, h1) : {Con{O.CrOct.xor(_, v), Con{O.CrOct.xor(B.Octets.take(d, o2), B.Octets.take(d, x)), Nil{}}} == Con{B.Octets.of_list(p), Con{B.Octets.of_list(r), Nil{}}} : List<&2, B.Octets>}
  %Equal.sym(B.Octets, O.CrOct.xor(o1, v), B.Octets.of_list(p), pc.ox(B.Octets.of_list(p), v)) : {Con{_, Con{O.CrOct.xor(B.Octets.take(d, o2), B.Octets.take(d, x)), Nil{}}} == Con{B.Octets.of_list(p), Con{B.Octets.of_list(r), Nil{}}} : List<&2, B.Octets>}
  # and Q's bytes XOR x's first bytes are Q
  %Equal.sym(B.Octets, O.CrOct.xor(B.Octets.take(d, o2), B.Octets.take(d, x)), B.Octets.of_list(r), pc.xtz(B.Octets.of_list(r), 1n+q, x, hQ, hx)) : {Con{B.Octets.of_list(p), Con{_, Nil{}}} == Con{B.Octets.of_list(p), Con{B.Octets.of_list(r), Nil{}}} : List<&2, B.Octets>}
  {==}

# three or more pieces: the first, then the rest from its ciphertext
def pc.DE3(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +q: Nat, +p: List<&2, U32>, +r: List<&2, U32>, +s: List<&2, U32>, +w: List<&2, List<&2, U32>>, +k: K, +v: B.Octets, hr: {pc.brs(~K, ~Blk, ~enc, ~dec, ~blk_of, ~blk_to, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{p, Con{r, Con{s, w}}}, k, v), k) == pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{p, Con{r, Con{s, w}}}, k, v) : List<&2, B.Octets>}, ih: {pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{r, Con{s, w}}, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))), k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))) == pc.ofs(Con{r, Con{s, w}}) : List<&2, B.Octets>}) -> {pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{p, Con{r, Con{s, w}}}, k, v)), k, v) == pc.ofs(Con{p, Con{r, Con{s, w}}}) : List<&2, B.Octets>}:
  +c = Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))
  +h1 = pc.ohd_eq(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, c), O.CrOct.xor(B.Octets.of_list(p), v), pc.brs(~K, ~Blk, ~enc, ~dec, ~blk_of, ~blk_to, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{r, Con{s, w}}, k, c), k), pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{r, Con{s, w}}, k, c), hr)
  Equal.trans(List<&2, B.Octets>, pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, Con{B.Octets.to_list(c), pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{r, Con{s, w}}, k, c))}, k, v), Con{O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, B.Octets.of_list(B.Octets.to_list(c))), v), pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{r, Con{s, w}}, k, c)), k, B.Octets.of_list(B.Octets.to_list(c)))}, Con{B.Octets.of_list(p), pc.ofs(Con{r, Con{s, w}})}, pc.D_cons(~K, ~Blk, ~dec, ~blk_of, ~blk_to, B.Octets.to_list(c), pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{r, Con{s, w}}, k, c)), k, v)(pc.E_ge2(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, w, r, s, k, c)), pc.con2(B.Octets, O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, B.Octets.of_list(B.Octets.to_list(c))), v), B.Octets.of_list(p), pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{r, Con{s, w}}, k, c)), k, B.Octets.of_list(B.Octets.to_list(c))), pc.ofs(Con{r, Con{s, w}}), pc.dstep(~K, ~Blk, ~enc, ~dec, ~blk_of, ~blk_to, k, B.Octets.of_list(p), v, h1), Equal.trans(List<&2, B.Octets>, pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{r, Con{s, w}}, k, c)), k, B.Octets.of_list(B.Octets.to_list(c))), pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{r, Con{s, w}}, k, c)), k, c), pc.ofs(Con{r, Con{s, w}}), Equal.cong(B.Octets, List<&2, B.Octets>, y => pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{r, Con{s, w}}, k, c)), k, y), B.Octets.of_list(B.Octets.to_list(c)), c, BL.octets_of_to(c)), ih)))

def pc.DE(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +q: Nat, +ps: List<&2, List<&2, U32>>, +k: K, +v: B.Octets) -> {pc.wfz(1n+q, ps) == True{} : Bool} -> {pc.brs(~K, ~Blk, ~enc, ~dec, ~blk_of, ~blk_to, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, ps, k, v), k) == pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, ps, k, v) : List<&2, B.Octets>} -> {pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, ps, k, v), k) == pc.lns(pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, ps, k, v)) : List<&2, Nat>} -> {pc.D(~K, ~Blk, ~dec, ~blk_of, ~blk_to, pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, ps, k, v)), k, v) == pc.ofs(ps) : List<&2, B.Octets>}:
  match ps:
    case Nil{}:
      hw => hr => hl => {==}
    case Con{+p, +t}:
      match t:
        case Nil{}:
          hw => hr => hl => pc.con2(B.Octets, O.CrOct.xor(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, B.Octets.of_list(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))))), v), B.Octets.of_list(p), Nil{}, Nil{}, pc.dstep(~K, ~Blk, ~enc, ~dec, ~blk_of, ~blk_to, k, B.Octets.of_list(p), v, pc.ohd_eq(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), O.CrOct.xor(B.Octets.of_list(p), v), Nil{}, Nil{}, hr)), {==})
        case Con{+r, +u}:
          match u:
            case Nil{}:
              +hw => hr => hl => pc.DE2(~K, ~Blk, ~enc, ~dec, ~blk_of, ~blk_to, q, p, r, k, v, pc.eq_true(B.len(p), 1n+q)(pc.and_l(Nat.is_eq(B.len(p), 1n+q), pc.wfz(1n+q, Con{r, Nil{}}))(hw)), pc.and_r(Nat.is_lt(0n, B.len(r)), Nat.is_le(B.len(r), 1n+q))(pc.and_l(Bool.and(Nat.is_lt(0n, B.len(r)), Nat.is_le(B.len(r), 1n+q)), True{})(pc.and_r(Nat.is_eq(B.len(p), 1n+q), pc.wfz(1n+q, Con{r, Nil{}}))(hw))), hr, hl)
            case Con{+s, +w}:
              +hw => +hr => +hl => pc.DE3(~K, ~Blk, ~enc, ~dec, ~blk_of, ~blk_to, q, p, r, s, w, k, v, hr, pc.DE(~K, ~Blk, ~enc, ~dec, ~blk_of, ~blk_to, q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))(pc.and_r(pc.okp(1n+q, p, t), pc.wfz(1n+q, t))(hw))(pc.otl_eq(Ct.cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), O.CrOct.xor(B.Octets.of_list(p), v), pc.brs(~K, ~Blk, ~enc, ~dec, ~blk_of, ~blk_to, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), k), pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), hr))(pc.ntl_eq(B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), B.Octets.len(O.CrOct.xor(B.Octets.of_list(p), v)), pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), k), pc.lns(pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))), hl)))

# The ciphertext's pieces are well-formed, and as long as the message's

# the stolen block's length: Q zero-padded to the block
def pc.cnlen(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +q: Nat, +k: K, +r: List<&2, U32>, +x: B.Octets, hq: {Nat.is_le(B.Octets.len(B.Octets.of_list(r)), 1n+q) == True{} : Bool}, l2: {B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), x))) == B.Octets.len(O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), x)) : Nat}) -> {B.len(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), x)))) == 1n+q : Nat}:
  Equal.trans(Nat, B.len(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), x)))), B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), x))), 1n+q, pc.olen(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), x))), Equal.trans(Nat, B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), x))), B.Octets.len(O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), x)), 1n+q, l2, Equal.trans(Nat, B.Octets.len(O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), x)), B.Octets.len(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r)))))), 1n+q, pc.xolen(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), x), Equal.trans(Nat, B.Octets.len(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r)))))), Nat.add(B.Octets.len(B.Octets.of_list(r)), B.Octets.len(B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r)))))), 1n+q, BL.octets_len_append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), Equal.trans(Nat, Nat.add(B.Octets.len(B.Octets.of_list(r)), B.Octets.len(B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r)))))), Nat.add(B.Octets.len(B.Octets.of_list(r)), Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r)))), 1n+q, Equal.cong(Nat, Nat, y => Nat.add(B.Octets.len(B.Octets.of_list(r)), y), B.Octets.len(B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))), BL.octets_len_zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), pc.add_sub(B.Octets.len(B.Octets.of_list(r)), 1n+q)(hq))))))

# the stolen bytes' length
def pc.tklen(+q: Nat, +r: List<&2, U32>, +x: B.Octets, hdx: {Nat.is_le(B.Octets.len(B.Octets.of_list(r)), B.Octets.len(x)) == True{} : Bool}) -> {B.len(B.Octets.to_list(B.Octets.take(B.Octets.len(B.Octets.of_list(r)), x))) == B.len(r) : Nat}:
  Equal.trans(Nat, B.len(B.Octets.to_list(B.Octets.take(B.Octets.len(B.Octets.of_list(r)), x))), B.Octets.len(B.Octets.take(B.Octets.len(B.Octets.of_list(r)), x)), B.len(r), pc.olen(B.Octets.take(B.Octets.len(B.Octets.of_list(r)), x)), Equal.trans(Nat, B.Octets.len(B.Octets.take(B.Octets.len(B.Octets.of_list(r)), x)), B.Octets.len(B.Octets.of_list(r)), B.len(r), BL.octets_len_take_le(B.Octets.len(B.Octets.of_list(r)), x, hdx), BL.octets_len_of_list(r)))

def pc.len2(+a: List<&2, U32>, +b: List<&2, U32>, +a2: List<&2, U32>, +b2: List<&2, U32>, ea: {B.len(a) == B.len(a2) : Nat}, eb: {B.len(b) == B.len(b2) : Nat}) -> {B.len(B.append(a, b)) == B.len(B.append(a2, b2)) : Nat}:
  %Equal.sym(Nat, B.len(B.append(a, b)), Nat.add(B.len(a), B.len(b)), pc.len_append(a, b)) : {_ == B.len(B.append(a2, b2)) : Nat}
  %Equal.sym(Nat, B.len(B.append(a2, b2)), Nat.add(B.len(a2), B.len(b2)), pc.len_append(a2, b2)) : {Nat.add(B.len(a), B.len(b)) == _ : Nat}
  %ea : {Nat.add(B.len(a), B.len(b)) == Nat.add(_, B.len(b2)) : Nat}
  %eb : {Nat.add(B.len(a), B.len(b)) == Nat.add(B.len(a), _) : Nat}
  {==}

# the facts of a well-formed list of two pieces
def pc.wf2_ep(+q: Nat, +p: List<&2, U32>, +r: List<&2, U32>, hw: {pc.wfz(1n+q, Con{p, Con{r, Nil{}}}) == True{} : Bool}) -> {B.len(p) == 1n+q : Nat}:
  pc.eq_true(B.len(p), 1n+q)(pc.and_l(Nat.is_eq(B.len(p), 1n+q), pc.wfz(1n+q, Con{r, Nil{}}))(hw))

def pc.wf2_r(+q: Nat, +p: List<&2, U32>, +r: List<&2, U32>, hw: {pc.wfz(1n+q, Con{p, Con{r, Nil{}}}) == True{} : Bool}) -> {Bool.and(Bool.and(Nat.is_lt(0n, B.len(r)), Nat.is_le(B.len(r), 1n+q)), True{}) == True{} : Bool}:
  pc.and_r(Nat.is_eq(B.len(p), 1n+q), pc.wfz(1n+q, Con{r, Nil{}}))(hw)

def pc.wf2_hq(+q: Nat, +p: List<&2, U32>, +r: List<&2, U32>, hw: {pc.wfz(1n+q, Con{p, Con{r, Nil{}}}) == True{} : Bool}) -> {Nat.is_le(B.len(r), 1n+q) == True{} : Bool}:
  pc.and_r(Nat.is_lt(0n, B.len(r)), Nat.is_le(B.len(r), 1n+q))(pc.and_l(Bool.and(Nat.is_lt(0n, B.len(r)), Nat.is_le(B.len(r), 1n+q)), True{})(pc.wf2_r(q, p, r, hw)))

# the two-piece case's lengths: the stolen block's and the stolen bytes'
def pc.two_cn(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +q: Nat, +p: List<&2, U32>, +r: List<&2, U32>, +k: K, +v: B.Octets, +hw: {pc.wfz(1n+q, Con{p, Con{r, Nil{}}}) == True{} : Bool}, +hl: {pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{p, Con{r, Nil{}}}, k, v), k) == pc.lns(pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{p, Con{r, Nil{}}}, k, v)) : List<&2, Nat>}) -> {B.len(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))))) == 1n+q : Nat}:
  +x = Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))
  +o2 = O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), x)
  +l1 = pc.nhd_eq(B.Octets.len(x), B.Octets.len(O.CrOct.xor(B.Octets.of_list(p), v)), pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, Con{o2, Nil{}}, k), pc.lns(Con{o2, Nil{}}), hl)
  +l2 = pc.nhd_eq(B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, o2)), B.Octets.len(o2), Nil{}, Nil{}, pc.ntl_eq(B.Octets.len(x), B.Octets.len(O.CrOct.xor(B.Octets.of_list(p), v)), pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, Con{o2, Nil{}}, k), pc.lns(Con{o2, Nil{}}), hl))
  +hx = pc.hx2(~K, ~Blk, ~enc, ~blk_of, ~blk_to, q, k, p, v, pc.wf2_ep(q, p, r, hw), l1)
  +hQ = pc.hq2(q, r, pc.wf2_hq(q, p, r, hw))
  +hdx = Equal.trans(Bool, Nat.is_le(B.Octets.len(B.Octets.of_list(r)), B.Octets.len(x)), Nat.is_le(B.Octets.len(B.Octets.of_list(r)), 1n+q), True{}, Equal.cong(Nat, Bool, y => Nat.is_le(B.Octets.len(B.Octets.of_list(r)), y), B.Octets.len(x), 1n+q, hx), hQ)
  pc.cnlen(~K, ~Blk, ~enc, ~blk_of, ~blk_to, q, k, r, x, hQ, l2)

def pc.two_tk(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +q: Nat, +p: List<&2, U32>, +r: List<&2, U32>, +k: K, +v: B.Octets, +hw: {pc.wfz(1n+q, Con{p, Con{r, Nil{}}}) == True{} : Bool}, +hl: {pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{p, Con{r, Nil{}}}, k, v), k) == pc.lns(pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, Con{p, Con{r, Nil{}}}, k, v)) : List<&2, Nat>}) -> {B.len(B.Octets.to_list(B.Octets.take(B.Octets.len(B.Octets.of_list(r)), Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))))) == B.len(r) : Nat}:
  +x = Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))
  +o2 = O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), x)
  +l1 = pc.nhd_eq(B.Octets.len(x), B.Octets.len(O.CrOct.xor(B.Octets.of_list(p), v)), pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, Con{o2, Nil{}}, k), pc.lns(Con{o2, Nil{}}), hl)
  +l2 = pc.nhd_eq(B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, o2)), B.Octets.len(o2), Nil{}, Nil{}, pc.ntl_eq(B.Octets.len(x), B.Octets.len(O.CrOct.xor(B.Octets.of_list(p), v)), pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, Con{o2, Nil{}}, k), pc.lns(Con{o2, Nil{}}), hl))
  +hx = pc.hx2(~K, ~Blk, ~enc, ~blk_of, ~blk_to, q, k, p, v, pc.wf2_ep(q, p, r, hw), l1)
  +hQ = pc.hq2(q, r, pc.wf2_hq(q, p, r, hw))
  +hdx = Equal.trans(Bool, Nat.is_le(B.Octets.len(B.Octets.of_list(r)), B.Octets.len(x)), Nat.is_le(B.Octets.len(B.Octets.of_list(r)), 1n+q), True{}, Equal.cong(Nat, Bool, y => Nat.is_le(B.Octets.len(B.Octets.of_list(r)), y), B.Octets.len(x), 1n+q, hx), hQ)
  pc.tklen(q, r, x, hdx)

def pc.wfE(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +q: Nat, +ps: List<&2, List<&2, U32>>, +k: K, +v: B.Octets) -> {pc.wfz(1n+q, ps) == True{} : Bool} -> {pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, ps, k, v), k) == pc.lns(pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, ps, k, v)) : List<&2, Nat>} -> {pc.wfz(1n+q, pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, ps, k, v))) == True{} : Bool}:
  match ps:
    case Nil{}:
      hw => hl => {==}
    case Con{+p, +t}:
      match t:
        case Nil{}:
          hw => hl => %Equal.sym(Nat, B.len(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))), B.len(p), pc.clen(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, p, v, pc.nhd_eq(B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), B.Octets.len(O.CrOct.xor(B.Octets.of_list(p), v)), Nil{}, Nil{}, hl))) : {Bool.and(Bool.and(Nat.is_lt(0n, _), Nat.is_le(_, 1n+q)), True{}) == True{} : Bool}
            hw
        case Con{+r, +u}:
          match u:
            case Nil{}:
              +hw => +hl => %Equal.sym(Nat, B.len(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))))), 1n+q, (pc.two_cn(~K, ~Blk, ~enc, ~blk_of, ~blk_to, q, p, r, k, v, hw, hl))) : {Bool.and(Nat.is_eq(_, 1n+q), Bool.and(Bool.and(Nat.is_lt(0n, B.len(B.Octets.to_list(B.Octets.take(B.Octets.len(B.Octets.of_list(r)), Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))))), Nat.is_le(B.len(B.Octets.to_list(B.Octets.take(B.Octets.len(B.Octets.of_list(r)), Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))))), 1n+q)), True{})) == True{} : Bool}
                %Equal.sym(Nat, B.len(B.Octets.to_list(B.Octets.take(B.Octets.len(B.Octets.of_list(r)), Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))))), B.len(r), (pc.two_tk(~K, ~Blk, ~enc, ~blk_of, ~blk_to, q, p, r, k, v, hw, hl))) : {Bool.and(Nat.is_eq(1n+q, 1n+q), Bool.and(Bool.and(Nat.is_lt(0n, _), Nat.is_le(_, 1n+q)), True{})) == True{} : Bool}
                pc.true_and(Nat.is_eq(1n+q, 1n+q), Bool.and(Bool.and(Nat.is_lt(0n, B.len(r)), Nat.is_le(B.len(r), 1n+q)), True{}), pc.eq_refl(1n+q), pc.wf2_r(q, p, r, hw))
            case Con{+s, +w}:
              +hw => +hl => pc.true_and(pc.okp(1n+q, B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))))), pc.wfz(1n+q, pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))))), pc.okp_full(q, B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))))(Equal.trans(Nat, B.len(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))), B.len(p), 1n+q, pc.clen(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, p, v, pc.nhd_eq(B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), B.Octets.len(O.CrOct.xor(B.Octets.of_list(p), v)), pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), k), pc.lns(pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))), hl)), pc.eq_true(B.len(p), 1n+q)(pc.and_l(Nat.is_eq(B.len(p), 1n+q), pc.wfz(1n+q, t))(hw)))), pc.wfE(~K, ~Blk, ~enc, ~blk_of, ~blk_to, q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))(pc.and_r(pc.okp(1n+q, p, t), pc.wfz(1n+q, t))(hw))(pc.ntl_eq(B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), B.Octets.len(O.CrOct.xor(B.Octets.of_list(p), v)), pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), k), pc.lns(pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))), hl)))

def pc.lenE(~K: Data, ~Blk: Data, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +q: Nat, +ps: List<&2, List<&2, U32>>, +k: K, +v: B.Octets) -> {pc.wfz(1n+q, ps) == True{} : Bool} -> {pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, ps, k, v), k) == pc.lns(pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, ps, k, v)) : List<&2, Nat>} -> {B.len(pc.cl(pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, ps, k, v)))) == B.len(pc.cl(ps)) : Nat}:
  match ps:
    case Nil{}:
      hw => hl => {==}
    case Con{+p, +t}:
      match t:
        case Nil{}:
          hw => hl => pc.len2(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), Nil{}, p, Nil{}, pc.clen(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, p, v, pc.nhd_eq(B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), B.Octets.len(O.CrOct.xor(B.Octets.of_list(p), v)), Nil{}, Nil{}, hl)), {==})
        case Con{+r, +u}:
          match u:
            case Nil{}:
              +hw => +hl => pc.len2(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))))), B.append(B.Octets.to_list(B.Octets.take(B.Octets.len(B.Octets.of_list(r)), Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))), Nil{}), p, B.append(r, Nil{}), Equal.trans(Nat, B.len(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.append(B.Octets.of_list(r), B.Octets.zeros(Nat.sub(1n+q, B.Octets.len(B.Octets.of_list(r))))), Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))))), 1n+q, B.len(p), (pc.two_cn(~K, ~Blk, ~enc, ~blk_of, ~blk_to, q, p, r, k, v, hw, hl)), Equal.sym(Nat, B.len(p), 1n+q, pc.wf2_ep(q, p, r, hw))), pc.len2(B.Octets.to_list(B.Octets.take(B.Octets.len(B.Octets.of_list(r)), Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))), Nil{}, r, Nil{}, (pc.two_tk(~K, ~Blk, ~enc, ~blk_of, ~blk_to, q, p, r, k, v, hw, hl)), {==}))
            case Con{+s, +w}:
              +hw => +hl => pc.len2(B.Octets.to_list(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), pc.cl(pc.tls(pc.E(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))))), p, pc.cl(t), pc.clen(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, p, v, pc.nhd_eq(B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), B.Octets.len(O.CrOct.xor(B.Octets.of_list(p), v)), pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), k), pc.lns(pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))), hl)), pc.lenE(~K, ~Blk, ~enc, ~blk_of, ~blk_to, q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))(pc.and_r(pc.okp(1n+q, p, t), pc.wfz(1n+q, t))(hw))(pc.ntl_eq(B.Octets.len(Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), B.Octets.len(O.CrOct.xor(B.Octets.of_list(p), v)), pc.bls(~K, ~Blk, ~enc, ~blk_of, ~blk_to, pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))), k), pc.lns(pc.oes(~K, ~Blk, ~enc, ~blk_of, ~blk_to, 1n+q, t, k, Ct.cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)))), hl)))

# BEGIN GENERATED by gen/cts_proof.py: formats

# The 128-bit block format (inst_cm.bend): the format's byte strings are the blocks' (pc.cm_dual), so a
# block of bytes encrypted and decrypted is itself where the cipher's block
# is (pc.cm_br), and keeps its length (pc.cm_bl)

def pc.cm_mget(m: Maybe<&2, M.CmBlock>, +d: M.CmBlock) -> M.CmBlock:
  match m:
    case Some{b}:
      b
    case None{}:
      d

def pc.cm_mdisc(m: Maybe<&2, M.CmBlock>) -> Type:
  match m:
    case Some{b}:
      Empty
    case None{}:
      Unit

def pc.cm_nsome(+bl: M.CmBlock, h: {None{} == Some{bl} : Maybe<&2, M.CmBlock>}) -> Empty:
  %h : pc.cm_mdisc(_)
  Unit{}

# a block's bytes read from 16 bytes are those bytes (on their bits)
def pc.cm_dbits(a0: U32, a1: U32, a2: U32, a3: U32, a4: U32, a5: U32, a6: U32, a7: U32, a8: U32, a9: U32, a10: U32, a11: U32, a12: U32, a13: U32, a14: U32, a15: U32) -> {CM.CrBlk128.to_octets(pc.cm_mget(CM.cr.f128.block(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Nil{}}}}}}}}}}}}}}}}}), M.CmBlock{0, 0, 0, 0})) == B.Octets.of_list(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Nil{}}}}}}}}}}}}}}}}}) : B.Octets}:
  match a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15:
    case U32{WCon{b0_0, WCon{b0_1, WCon{b0_2, WCon{b0_3, WCon{b0_4, WCon{b0_5, WCon{b0_6, WCon{b0_7, WCon{b0_8, WCon{b0_9, WCon{b0_10, WCon{b0_11, WCon{b0_12, WCon{b0_13, WCon{b0_14, WCon{b0_15, WCon{b0_16, WCon{b0_17, WCon{b0_18, WCon{b0_19, WCon{b0_20, WCon{b0_21, WCon{b0_22, WCon{b0_23, WCon{b0_24, WCon{b0_25, WCon{b0_26, WCon{b0_27, WCon{b0_28, WCon{b0_29, WCon{b0_30, WCon{b0_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b1_0, WCon{b1_1, WCon{b1_2, WCon{b1_3, WCon{b1_4, WCon{b1_5, WCon{b1_6, WCon{b1_7, WCon{b1_8, WCon{b1_9, WCon{b1_10, WCon{b1_11, WCon{b1_12, WCon{b1_13, WCon{b1_14, WCon{b1_15, WCon{b1_16, WCon{b1_17, WCon{b1_18, WCon{b1_19, WCon{b1_20, WCon{b1_21, WCon{b1_22, WCon{b1_23, WCon{b1_24, WCon{b1_25, WCon{b1_26, WCon{b1_27, WCon{b1_28, WCon{b1_29, WCon{b1_30, WCon{b1_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b2_0, WCon{b2_1, WCon{b2_2, WCon{b2_3, WCon{b2_4, WCon{b2_5, WCon{b2_6, WCon{b2_7, WCon{b2_8, WCon{b2_9, WCon{b2_10, WCon{b2_11, WCon{b2_12, WCon{b2_13, WCon{b2_14, WCon{b2_15, WCon{b2_16, WCon{b2_17, WCon{b2_18, WCon{b2_19, WCon{b2_20, WCon{b2_21, WCon{b2_22, WCon{b2_23, WCon{b2_24, WCon{b2_25, WCon{b2_26, WCon{b2_27, WCon{b2_28, WCon{b2_29, WCon{b2_30, WCon{b2_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b3_0, WCon{b3_1, WCon{b3_2, WCon{b3_3, WCon{b3_4, WCon{b3_5, WCon{b3_6, WCon{b3_7, WCon{b3_8, WCon{b3_9, WCon{b3_10, WCon{b3_11, WCon{b3_12, WCon{b3_13, WCon{b3_14, WCon{b3_15, WCon{b3_16, WCon{b3_17, WCon{b3_18, WCon{b3_19, WCon{b3_20, WCon{b3_21, WCon{b3_22, WCon{b3_23, WCon{b3_24, WCon{b3_25, WCon{b3_26, WCon{b3_27, WCon{b3_28, WCon{b3_29, WCon{b3_30, WCon{b3_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b4_0, WCon{b4_1, WCon{b4_2, WCon{b4_3, WCon{b4_4, WCon{b4_5, WCon{b4_6, WCon{b4_7, WCon{b4_8, WCon{b4_9, WCon{b4_10, WCon{b4_11, WCon{b4_12, WCon{b4_13, WCon{b4_14, WCon{b4_15, WCon{b4_16, WCon{b4_17, WCon{b4_18, WCon{b4_19, WCon{b4_20, WCon{b4_21, WCon{b4_22, WCon{b4_23, WCon{b4_24, WCon{b4_25, WCon{b4_26, WCon{b4_27, WCon{b4_28, WCon{b4_29, WCon{b4_30, WCon{b4_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b5_0, WCon{b5_1, WCon{b5_2, WCon{b5_3, WCon{b5_4, WCon{b5_5, WCon{b5_6, WCon{b5_7, WCon{b5_8, WCon{b5_9, WCon{b5_10, WCon{b5_11, WCon{b5_12, WCon{b5_13, WCon{b5_14, WCon{b5_15, WCon{b5_16, WCon{b5_17, WCon{b5_18, WCon{b5_19, WCon{b5_20, WCon{b5_21, WCon{b5_22, WCon{b5_23, WCon{b5_24, WCon{b5_25, WCon{b5_26, WCon{b5_27, WCon{b5_28, WCon{b5_29, WCon{b5_30, WCon{b5_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b6_0, WCon{b6_1, WCon{b6_2, WCon{b6_3, WCon{b6_4, WCon{b6_5, WCon{b6_6, WCon{b6_7, WCon{b6_8, WCon{b6_9, WCon{b6_10, WCon{b6_11, WCon{b6_12, WCon{b6_13, WCon{b6_14, WCon{b6_15, WCon{b6_16, WCon{b6_17, WCon{b6_18, WCon{b6_19, WCon{b6_20, WCon{b6_21, WCon{b6_22, WCon{b6_23, WCon{b6_24, WCon{b6_25, WCon{b6_26, WCon{b6_27, WCon{b6_28, WCon{b6_29, WCon{b6_30, WCon{b6_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b7_0, WCon{b7_1, WCon{b7_2, WCon{b7_3, WCon{b7_4, WCon{b7_5, WCon{b7_6, WCon{b7_7, WCon{b7_8, WCon{b7_9, WCon{b7_10, WCon{b7_11, WCon{b7_12, WCon{b7_13, WCon{b7_14, WCon{b7_15, WCon{b7_16, WCon{b7_17, WCon{b7_18, WCon{b7_19, WCon{b7_20, WCon{b7_21, WCon{b7_22, WCon{b7_23, WCon{b7_24, WCon{b7_25, WCon{b7_26, WCon{b7_27, WCon{b7_28, WCon{b7_29, WCon{b7_30, WCon{b7_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b8_0, WCon{b8_1, WCon{b8_2, WCon{b8_3, WCon{b8_4, WCon{b8_5, WCon{b8_6, WCon{b8_7, WCon{b8_8, WCon{b8_9, WCon{b8_10, WCon{b8_11, WCon{b8_12, WCon{b8_13, WCon{b8_14, WCon{b8_15, WCon{b8_16, WCon{b8_17, WCon{b8_18, WCon{b8_19, WCon{b8_20, WCon{b8_21, WCon{b8_22, WCon{b8_23, WCon{b8_24, WCon{b8_25, WCon{b8_26, WCon{b8_27, WCon{b8_28, WCon{b8_29, WCon{b8_30, WCon{b8_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b9_0, WCon{b9_1, WCon{b9_2, WCon{b9_3, WCon{b9_4, WCon{b9_5, WCon{b9_6, WCon{b9_7, WCon{b9_8, WCon{b9_9, WCon{b9_10, WCon{b9_11, WCon{b9_12, WCon{b9_13, WCon{b9_14, WCon{b9_15, WCon{b9_16, WCon{b9_17, WCon{b9_18, WCon{b9_19, WCon{b9_20, WCon{b9_21, WCon{b9_22, WCon{b9_23, WCon{b9_24, WCon{b9_25, WCon{b9_26, WCon{b9_27, WCon{b9_28, WCon{b9_29, WCon{b9_30, WCon{b9_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b10_0, WCon{b10_1, WCon{b10_2, WCon{b10_3, WCon{b10_4, WCon{b10_5, WCon{b10_6, WCon{b10_7, WCon{b10_8, WCon{b10_9, WCon{b10_10, WCon{b10_11, WCon{b10_12, WCon{b10_13, WCon{b10_14, WCon{b10_15, WCon{b10_16, WCon{b10_17, WCon{b10_18, WCon{b10_19, WCon{b10_20, WCon{b10_21, WCon{b10_22, WCon{b10_23, WCon{b10_24, WCon{b10_25, WCon{b10_26, WCon{b10_27, WCon{b10_28, WCon{b10_29, WCon{b10_30, WCon{b10_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b11_0, WCon{b11_1, WCon{b11_2, WCon{b11_3, WCon{b11_4, WCon{b11_5, WCon{b11_6, WCon{b11_7, WCon{b11_8, WCon{b11_9, WCon{b11_10, WCon{b11_11, WCon{b11_12, WCon{b11_13, WCon{b11_14, WCon{b11_15, WCon{b11_16, WCon{b11_17, WCon{b11_18, WCon{b11_19, WCon{b11_20, WCon{b11_21, WCon{b11_22, WCon{b11_23, WCon{b11_24, WCon{b11_25, WCon{b11_26, WCon{b11_27, WCon{b11_28, WCon{b11_29, WCon{b11_30, WCon{b11_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b12_0, WCon{b12_1, WCon{b12_2, WCon{b12_3, WCon{b12_4, WCon{b12_5, WCon{b12_6, WCon{b12_7, WCon{b12_8, WCon{b12_9, WCon{b12_10, WCon{b12_11, WCon{b12_12, WCon{b12_13, WCon{b12_14, WCon{b12_15, WCon{b12_16, WCon{b12_17, WCon{b12_18, WCon{b12_19, WCon{b12_20, WCon{b12_21, WCon{b12_22, WCon{b12_23, WCon{b12_24, WCon{b12_25, WCon{b12_26, WCon{b12_27, WCon{b12_28, WCon{b12_29, WCon{b12_30, WCon{b12_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b13_0, WCon{b13_1, WCon{b13_2, WCon{b13_3, WCon{b13_4, WCon{b13_5, WCon{b13_6, WCon{b13_7, WCon{b13_8, WCon{b13_9, WCon{b13_10, WCon{b13_11, WCon{b13_12, WCon{b13_13, WCon{b13_14, WCon{b13_15, WCon{b13_16, WCon{b13_17, WCon{b13_18, WCon{b13_19, WCon{b13_20, WCon{b13_21, WCon{b13_22, WCon{b13_23, WCon{b13_24, WCon{b13_25, WCon{b13_26, WCon{b13_27, WCon{b13_28, WCon{b13_29, WCon{b13_30, WCon{b13_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b14_0, WCon{b14_1, WCon{b14_2, WCon{b14_3, WCon{b14_4, WCon{b14_5, WCon{b14_6, WCon{b14_7, WCon{b14_8, WCon{b14_9, WCon{b14_10, WCon{b14_11, WCon{b14_12, WCon{b14_13, WCon{b14_14, WCon{b14_15, WCon{b14_16, WCon{b14_17, WCon{b14_18, WCon{b14_19, WCon{b14_20, WCon{b14_21, WCon{b14_22, WCon{b14_23, WCon{b14_24, WCon{b14_25, WCon{b14_26, WCon{b14_27, WCon{b14_28, WCon{b14_29, WCon{b14_30, WCon{b14_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{b15_0, WCon{b15_1, WCon{b15_2, WCon{b15_3, WCon{b15_4, WCon{b15_5, WCon{b15_6, WCon{b15_7, WCon{b15_8, WCon{b15_9, WCon{b15_10, WCon{b15_11, WCon{b15_12, WCon{b15_13, WCon{b15_14, WCon{b15_15, WCon{b15_16, WCon{b15_17, WCon{b15_18, WCon{b15_19, WCon{b15_20, WCon{b15_21, WCon{b15_22, WCon{b15_23, WCon{b15_24, WCon{b15_25, WCon{b15_26, WCon{b15_27, WCon{b15_28, WCon{b15_29, WCon{b15_30, WCon{b15_31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      {==}


# a block read from a list of bytes is written back as those bytes
def pc.cm_dualL(+xs: List<&2, U32>, +bl: M.CmBlock) -> {CM.cr.f128.block(xs) == Some{bl} : Maybe<&2, M.CmBlock>} -> {CM.CrBlk128.to_octets(bl) == B.Octets.of_list(xs) : B.Octets}:
  match xs:
    case Nil{}:
      h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Nil{}) : B.Octets}, pc.cm_nsome(bl, h))
    case Con{+a0, +x1}:
      match x1:
        case Nil{}:
          h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Con{a0, Nil{}}) : B.Octets}, pc.cm_nsome(bl, h))
        case Con{+a1, +x2}:
          match x2:
            case Nil{}:
              h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Con{a0, Con{a1, Nil{}}}) : B.Octets}, pc.cm_nsome(bl, h))
            case Con{+a2, +x3}:
              match x3:
                case Nil{}:
                  h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Con{a0, Con{a1, Con{a2, Nil{}}}}) : B.Octets}, pc.cm_nsome(bl, h))
                case Con{+a3, +x4}:
                  match x4:
                    case Nil{}:
                      h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Con{a0, Con{a1, Con{a2, Con{a3, Nil{}}}}}) : B.Octets}, pc.cm_nsome(bl, h))
                    case Con{+a4, +x5}:
                      match x5:
                        case Nil{}:
                          h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Nil{}}}}}}) : B.Octets}, pc.cm_nsome(bl, h))
                        case Con{+a5, +x6}:
                          match x6:
                            case Nil{}:
                              h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Nil{}}}}}}}) : B.Octets}, pc.cm_nsome(bl, h))
                            case Con{+a6, +x7}:
                              match x7:
                                case Nil{}:
                                  h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Nil{}}}}}}}}) : B.Octets}, pc.cm_nsome(bl, h))
                                case Con{+a7, +x8}:
                                  match x8:
                                    case Nil{}:
                                      h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Nil{}}}}}}}}}) : B.Octets}, pc.cm_nsome(bl, h))
                                    case Con{+a8, +x9}:
                                      match x9:
                                        case Nil{}:
                                          h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Nil{}}}}}}}}}}) : B.Octets}, pc.cm_nsome(bl, h))
                                        case Con{+a9, +x10}:
                                          match x10:
                                            case Nil{}:
                                              h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Nil{}}}}}}}}}}}) : B.Octets}, pc.cm_nsome(bl, h))
                                            case Con{+a10, +x11}:
                                              match x11:
                                                case Nil{}:
                                                  h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Nil{}}}}}}}}}}}}) : B.Octets}, pc.cm_nsome(bl, h))
                                                case Con{+a11, +x12}:
                                                  match x12:
                                                    case Nil{}:
                                                      h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Nil{}}}}}}}}}}}}}) : B.Octets}, pc.cm_nsome(bl, h))
                                                    case Con{+a12, +x13}:
                                                      match x13:
                                                        case Nil{}:
                                                          h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Nil{}}}}}}}}}}}}}}) : B.Octets}, pc.cm_nsome(bl, h))
                                                        case Con{+a13, +x14}:
                                                          match x14:
                                                            case Nil{}:
                                                              h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Nil{}}}}}}}}}}}}}}}) : B.Octets}, pc.cm_nsome(bl, h))
                                                            case Con{+a14, +x15}:
                                                              match x15:
                                                                case Nil{}:
                                                                  h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Nil{}}}}}}}}}}}}}}}}) : B.Octets}, pc.cm_nsome(bl, h))
                                                                case Con{+a15, +x16}:
                                                                  match x16:
                                                                    case Nil{}:
                                                                      h => %Equal.cong(Maybe<&2, M.CmBlock>, M.CmBlock, mm => pc.cm_mget(mm, bl), CM.cr.f128.block(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Nil{}}}}}}}}}}}}}}}}}), Some{bl}, h) : {CM.CrBlk128.to_octets(_) == B.Octets.of_list(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Nil{}}}}}}}}}}}}}}}}}) : B.Octets}
                                                                        pc.cm_dbits(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15)
                                                                    case Con{+a16, +x17}:
                                                                      h => Empty.absurd({CM.CrBlk128.to_octets(bl) == B.Octets.of_list(Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, Con{a9, Con{a10, Con{a11, Con{a12, Con{a13, Con{a14, Con{a15, Con{a16, x17}}}}}}}}}}}}}}}}}) : B.Octets}, pc.cm_nsome(bl, h))


def pc.cm_dual(+o: B.Octets, +bl: M.CmBlock, em: {CM.CrBlk128.of_octets(o) == Some{bl} : Maybe<&2, M.CmBlock>}) -> {CM.CrBlk128.to_octets(bl) == o : B.Octets}:
  Equal.trans(B.Octets, CM.CrBlk128.to_octets(bl), B.Octets.of_list(B.Octets.to_list(o)), o, pc.cm_dualL(B.Octets.to_list(o), bl)(em), BL.octets_of_to(o))

def pc.cm_ebl.go(m: Maybe<&2, M.CmBlock>) -> M.CmBlock:
  match m:
    case Some{b}:
      b
    case None{}:
      M.CmBlock{0, 0, 0, 0}

def pc.cm_ebl(+o: B.Octets) -> M.CmBlock:
  pc.cm_ebl.go(CM.CrBlk128.of_octets(o))

def pc.cm_br.go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, m: Maybe<&2, M.CmBlock>, +o: B.Octets) -> {CM.CrBlk128.of_octets(o) == m : Maybe<&2, M.CmBlock>} -> {dec(k, enc(k, pc.cm_ebl.go(m))) == pc.cm_ebl.go(m) : M.CmBlock} -> {Ct.cr.cts.b(~K, ~M.CmBlock, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, Ct.cr.cts.b(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, o)) == o : B.Octets}:
  match m:
    case None{}:
      +em => hi => %Equal.sym(Maybe<&2, M.CmBlock>, CM.CrBlk128.of_octets(o), None{}, em) : {Ct.cr.cts.b(~K, ~M.CmBlock, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, Ct.cr.cts.b.go(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.to_octets, k, _, o)) == o : B.Octets}
        %Equal.sym(Maybe<&2, M.CmBlock>, CM.CrBlk128.of_octets(o), None{}, em) : {Ct.cr.cts.b.go(~K, ~M.CmBlock, ~dec, ~CM.CrBlk128.to_octets, k, _, o) == o : B.Octets}
        {==}
    case Some{+bl}:
      +em => hi => %Equal.sym(Maybe<&2, M.CmBlock>, CM.CrBlk128.of_octets(o), Some{bl}, em) : {Ct.cr.cts.b(~K, ~M.CmBlock, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, Ct.cr.cts.b.go(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.to_octets, k, _, o)) == o : B.Octets}
        %Equal.sym(Maybe<&2, M.CmBlock>, CM.CrBlk128.of_octets(CM.CrBlk128.to_octets(enc(k, bl))), Some{enc(k, bl)}, PB.pb.cm_fmt(enc(k, bl))) : {Ct.cr.cts.b.go(~K, ~M.CmBlock, ~dec, ~CM.CrBlk128.to_octets, k, _, CM.CrBlk128.to_octets(enc(k, bl))) == o : B.Octets}
        %Equal.sym(M.CmBlock, dec(k, enc(k, bl)), bl, hi) : {CM.CrBlk128.to_octets(_) == o : B.Octets}
        pc.cm_dual(o, bl, em)

def pc.cm_br(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +o: B.Octets, hi: {dec(k, enc(k, pc.cm_ebl(o))) == pc.cm_ebl(o) : M.CmBlock}) -> {Ct.cr.cts.b(~K, ~M.CmBlock, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, Ct.cr.cts.b(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, o)) == o : B.Octets}:
  pc.cm_br.go(~K, ~enc, ~dec, k, CM.CrBlk128.of_octets(o), o)({==})(hi)

def pc.cm_bl.go(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, m: Maybe<&2, M.CmBlock>, +o: B.Octets) -> {CM.CrBlk128.of_octets(o) == m : Maybe<&2, M.CmBlock>} -> {B.Octets.len(Ct.cr.cts.b(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, o)) == B.Octets.len(o) : Nat}:
  match m:
    case None{}:
      em => %Equal.sym(Maybe<&2, M.CmBlock>, CM.CrBlk128.of_octets(o), None{}, em) : {B.Octets.len(Ct.cr.cts.b.go(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.to_octets, k, _, o)) == B.Octets.len(o) : Nat}
        {==}
    case Some{+bl}:
      +em => %Equal.sym(Maybe<&2, M.CmBlock>, CM.CrBlk128.of_octets(o), Some{bl}, em) : {B.Octets.len(Ct.cr.cts.b.go(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.to_octets, k, _, o)) == B.Octets.len(o) : Nat}
        Equal.trans(Nat, B.Octets.len(CM.CrBlk128.to_octets(enc(k, bl))), 16n, B.Octets.len(o), PB.pb.cm_len(enc(k, bl)), Equal.sym(Nat, B.Octets.len(o), 16n, Equal.trans(Nat, B.Octets.len(o), B.Octets.len(CM.CrBlk128.to_octets(bl)), 16n, Equal.cong(B.Octets, Nat, y => B.Octets.len(y), o, CM.CrBlk128.to_octets(bl), Equal.sym(B.Octets, CM.CrBlk128.to_octets(bl), o, pc.cm_dual(o, bl, em))), PB.pb.cm_len(bl))))

def pc.cm_bl(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +o: B.Octets) -> {B.Octets.len(Ct.cr.cts.b(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, o)) == B.Octets.len(o) : Nat}:
  pc.cm_bl.go(~K, ~enc, k, CM.CrBlk128.of_octets(o), o)({==})

def pc.cm_ebls(os: List<&2, B.Octets>) -> List<&2, M.CmBlock>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      Con{pc.cm_ebl(o), pc.cm_ebls(t)}

def pc.cm_bhd(l: List<&2, M.CmBlock>) -> M.CmBlock:
  match l:
    case Nil{}:
      M.CmBlock{0, 0, 0, 0}
    case Con{x, t}:
      x

def pc.cm_btl(l: List<&2, M.CmBlock>) -> List<&2, M.CmBlock>:
  match l:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

def pc.cm_brs_all(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +os: List<&2, B.Octets>) -> {Laws.crcts.dec_enc(~K, ~M.CmBlock, ~enc, ~dec, k, pc.cm_ebls(os)) == pc.cm_ebls(os) : List<&2, M.CmBlock>} -> {pc.brs(~K, ~M.CmBlock, ~enc, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, os, k) == os : List<&2, B.Octets>}:
  match os:
    case Nil{}:
      h => {==}
    case Con{+o, +t}:
      +h => pc.con2(B.Octets, Ct.cr.cts.b(~K, ~M.CmBlock, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, Ct.cr.cts.b(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, o)), o, pc.brs(~K, ~M.CmBlock, ~enc, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, t, k), t, pc.cm_br(~K, ~enc, ~dec, k, o, Equal.cong(List<&2, M.CmBlock>, M.CmBlock, l => pc.cm_bhd(l), Laws.crcts.dec_enc(~K, ~M.CmBlock, ~enc, ~dec, k, pc.cm_ebls(Con{o, t})), pc.cm_ebls(Con{o, t}), h)), pc.cm_brs_all(~K, ~enc, ~dec, k, t)(Equal.cong(List<&2, M.CmBlock>, List<&2, M.CmBlock>, l => pc.cm_btl(l), Laws.crcts.dec_enc(~K, ~M.CmBlock, ~enc, ~dec, k, pc.cm_ebls(Con{o, t})), pc.cm_ebls(Con{o, t}), h)))

def pc.cm_bls_all(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +os: List<&2, B.Octets>) -> {pc.bls(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, os, k) == pc.lns(os) : List<&2, Nat>}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +t}:
      pc.con2(Nat, B.Octets.len(Ct.cr.cts.b(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, o)), B.Octets.len(o), pc.bls(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, t, k), pc.lns(t), pc.cm_bl(~K, ~enc, k, o), pc.cm_bls_all(~K, ~enc, k, t))

# the ciphertext as long as the message
def pc.cm_len(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, +k: K, +iv: B.Octets, +m: B.Octets) -> {B.Octets.len(Ct.cr.cts.enc.go(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(m)), k, iv, Nil{})) == B.Octets.len(m) : Nat}:
  +xs = B.Octets.to_list(m)
  +ps = pc.PC(B.Octets.to_list(m), 15n, 15n, Nil{}, Nil{})
  +e = pc.E(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, 16n, pc.PC(B.Octets.to_list(m), 15n, 15n, Nil{}, Nil{}), k, iv)
  %Equal.sym(List<&2, List<&2, U32>>, O.CrOct.pieces(1n+15n, xs), ps, pc.pieces(15n, xs)) : {B.Octets.len(Ct.cr.cts.enc.go(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, _, k, iv, Nil{})) == B.Octets.len(m) : Nat}
  %Equal.sym(B.Octets, Ct.cr.cts.enc.go(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ps, k, iv, Nil{}), B.Octets.concat(Ct.cr.cts.rcat(Nil{}, e)), pc.enc_E(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ps, k, iv, Nil{})) : {B.Octets.len(_) == B.Octets.len(m) : Nat}
  %pc.olen(B.Octets.concat(e)) : {_ == B.Octets.len(m) : Nat}
  %pc.cl_tls(e) : {B.len(_) == B.Octets.len(m) : Nat}
  %Equal.sym(Nat, B.len(pc.cl(pc.tls(e))), B.len(pc.cl(ps)), pc.lenE(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, 15n, ps, k, iv)(pc.wf_PC(xs, 15n, 15n, Nil{})({==}))(pc.cm_bls_all(~K, ~enc, k, pc.oes(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, 16n, ps, k, iv)))) : {_ == B.Octets.len(m) : Nat}
  %Equal.sym(List<&2, U32>, pc.cl(ps), O.cr.oct.rev(Nil{}, xs), pc.cl_PC(xs, 15n, 15n, Nil{})) : {B.len(_) == B.Octets.len(m) : Nat}
  pc.olen(m)

# decryption of the ciphertext gives the message
def pc.cm_inner(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, inv: @xs: List<&2, M.CmBlock> -> {Laws.crcts.dec_enc(~K, ~M.CmBlock, ~enc, ~dec, k, xs) == xs : List<&2, M.CmBlock>}, +iv: B.Octets, +m: B.Octets) -> {Ct.cr.cts.dec.go(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(Ct.cr.cts.enc.go(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(m)), k, iv, Nil{}))), k, iv, Nil{}) == m : B.Octets}:
  +xs = B.Octets.to_list(m)
  +ps = pc.PC(B.Octets.to_list(m), 15n, 15n, Nil{}, Nil{})
  +e = pc.E(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, 16n, pc.PC(B.Octets.to_list(m), 15n, 15n, Nil{}, Nil{}), k, iv)
  +os = pc.oes(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, 16n, pc.PC(B.Octets.to_list(m), 15n, 15n, Nil{}, Nil{}), k, iv)
  +hw = pc.wf_PC(xs, 15n, 15n, Nil{})({==})
  +hl = pc.cm_bls_all(~K, ~enc, k, os)
  +hr = pc.cm_brs_all(~K, ~enc, ~dec, k, os)(inv(pc.cm_ebls(os)))
  # the message's pieces, and the ciphertext's bytes
  %Equal.sym(List<&2, List<&2, U32>>, O.CrOct.pieces(1n+15n, xs), ps, pc.pieces(15n, xs)) : {Ct.cr.cts.dec.go(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(Ct.cr.cts.enc.go(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, _, k, iv, Nil{}))), k, iv, Nil{}) == m : B.Octets}
  %Equal.sym(B.Octets, Ct.cr.cts.enc.go(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ps, k, iv, Nil{}), B.Octets.concat(Ct.cr.cts.rcat(Nil{}, e)), pc.enc_E(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, ps, k, iv, Nil{})) : {Ct.cr.cts.dec.go(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(_)), k, iv, Nil{}) == m : B.Octets}
  %pc.cl_tls(e) : {Ct.cr.cts.dec.go(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, _), k, iv, Nil{}) == m : B.Octets}
  # the ciphertext's pieces are the encrypted pieces
  %Equal.sym(List<&2, List<&2, U32>>, O.CrOct.pieces(1n+15n, pc.cl(pc.tls(e))), pc.PC(pc.cl(pc.tls(e)), 15n, 15n, Nil{}, Nil{}), pc.pieces(15n, pc.cl(pc.tls(e)))) : {Ct.cr.cts.dec.go(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, _, k, iv, Nil{}) == m : B.Octets}
  %Equal.sym(List<&2, List<&2, U32>>, pc.PC(pc.cl(pc.tls(e)), 15n, 15n, Nil{}, Nil{}), pc.tls(e), pc.L2(pc.tls(e), 15n)(pc.wfE(~K, ~M.CmBlock, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, 15n, ps, k, iv)(hw)(hl))) : {Ct.cr.cts.dec.go(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, _, k, iv, Nil{}) == m : B.Octets}
  # which decrypt to the message's pieces
  %Equal.sym(B.Octets, Ct.cr.cts.dec.go(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, pc.tls(e), k, iv, Nil{}), B.Octets.concat(Ct.cr.cts.rcat(Nil{}, pc.D(~K, ~M.CmBlock, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, pc.tls(e), k, iv))), pc.dec_D(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, pc.tls(e), k, iv, Nil{})) : {_ == m : B.Octets}
  %Equal.sym(List<&2, B.Octets>, pc.D(~K, ~M.CmBlock, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, pc.tls(e), k, iv), pc.ofs(ps), pc.DE(~K, ~M.CmBlock, ~enc, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, 15n, ps, k, iv)(hw)(hr)(hl)) : {B.Octets.concat(_) == m : B.Octets}
  # joined back
  %Equal.sym(B.Octets, B.Octets.concat(pc.ofs(ps)), B.Octets.of_list(pc.cl(ps)), pc.cat_ofs(ps)) : {_ == m : B.Octets}
  %Equal.sym(List<&2, U32>, pc.cl(ps), O.cr.oct.rev(Nil{}, xs), pc.cl_PC(xs, 15n, 15n, Nil{})) : {B.Octets.of_list(_) == m : B.Octets}
  BL.octets_of_to(m)

def pc.cm_fin(~K: Data, ~enc: K -> M.CmBlock -> M.CmBlock, ~dec: K -> M.CmBlock -> M.CmBlock, +k: K, +iv: B.Octets, +m: B.Octets, inner: {Ct.cr.cts.dec.go(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(Ct.cr.cts.enc.go(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(m)), k, iv, Nil{}))), k, iv, Nil{}) == m : B.Octets}, lenf: {B.Octets.len(Ct.cr.cts.enc.go(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(m)), k, iv, Nil{})) == B.Octets.len(m) : Nat}, chk: Result<&2, &2, Cr.CrError, Unit>) -> {Ct.cr.cts.check(16n, iv, B.Octets.len(m)) == chk : Result<&2, &2, Cr.CrError, Unit>} -> {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Result.map(&2, &2, Cr.CrError, Unit, B.Octets, u => Ct.cr.cts.enc.go(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(m)), k, iv, Nil{}), chk), c => Ct.CrCts.decrypt(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, k, iv, c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => m, Result.map(&2, &2, Cr.CrError, Unit, B.Octets, u => Ct.cr.cts.enc.go(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(m)), k, iv, Nil{}), chk)) : Result<&2, &2, Cr.CrError, B.Octets>}:
  match chk:
    case Fail{e}:
      hc => {==}
    case Done{+u}:
      +hc => %Equal.sym(Nat, B.Octets.len(Ct.cr.cts.enc.go(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(m)), k, iv, Nil{})), B.Octets.len(m), lenf) : {Result.map(&2, &2, Cr.CrError, Unit, B.Octets, u2 => Ct.cr.cts.dec.go(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(Ct.cr.cts.enc.go(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(m)), k, iv, Nil{}))), k, iv, Nil{}), Ct.cr.cts.check(16n, iv, _)) == Done{m} : Result<&2, &2, Cr.CrError, B.Octets>}
        %Equal.sym(Result<&2, &2, Cr.CrError, Unit>, Ct.cr.cts.check(16n, iv, B.Octets.len(m)), Done{u}, hc) : {Result.map(&2, &2, Cr.CrError, Unit, B.Octets, u2 => Ct.cr.cts.dec.go(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(Ct.cr.cts.enc.go(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(m)), k, iv, Nil{}))), k, iv, Nil{}), _) == Done{m} : Result<&2, &2, Cr.CrError, B.Octets>}
        Equal.cong(B.Octets, Result<&2, &2, Cr.CrError, B.Octets>, y => Done{y}, Ct.cr.cts.dec.go(~K, ~M.CmBlock, ~16n, ~dec, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(Ct.cr.cts.enc.go(~K, ~M.CmBlock, ~16n, ~enc, ~CM.CrBlk128.of_octets, ~CM.CrBlk128.to_octets, O.CrOct.pieces(16n, B.Octets.to_list(m)), k, iv, Nil{}))), k, iv, Nil{}), m, inner)

def Laws.cmblock_cts_round_trip(K, enc, dec, k, inv, iv, m):
  pc.cm_fin(~K, ~enc, ~dec, k, iv, m, pc.cm_inner(~K, ~enc, ~dec, k, inv, iv, m), pc.cm_len(~K, ~enc, k, iv, m), Ct.cr.cts.check(16n, iv, B.Octets.len(m)))({==})


# The 64-bit block format (cipher-core's LcBlock64): the format's byte strings are the blocks' (CoreL.block64_octets_dual), so a
# block of bytes encrypted and decrypted is itself where the cipher's block
# is (pc.lc_br), and keeps its length (pc.lc_bl)

def pc.lc_ebl.go(m: Maybe<&2, L.LcBlock64>) -> L.LcBlock64:
  match m:
    case Some{b}:
      b
    case None{}:
      L.LcBlock64{0, 0}

def pc.lc_ebl(+o: B.Octets) -> L.LcBlock64:
  pc.lc_ebl.go(L.LcBlock64.of_octets(o))

def pc.lc_br.go(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, ~dec: K -> L.LcBlock64 -> L.LcBlock64, +k: K, m: Maybe<&2, L.LcBlock64>, +o: B.Octets) -> {L.LcBlock64.of_octets(o) == m : Maybe<&2, L.LcBlock64>} -> {dec(k, enc(k, pc.lc_ebl.go(m))) == pc.lc_ebl.go(m) : L.LcBlock64} -> {Ct.cr.cts.b(~K, ~L.LcBlock64, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, Ct.cr.cts.b(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, o)) == o : B.Octets}:
  match m:
    case None{}:
      +em => hi => %Equal.sym(Maybe<&2, L.LcBlock64>, L.LcBlock64.of_octets(o), None{}, em) : {Ct.cr.cts.b(~K, ~L.LcBlock64, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, Ct.cr.cts.b.go(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.to_octets, k, _, o)) == o : B.Octets}
        %Equal.sym(Maybe<&2, L.LcBlock64>, L.LcBlock64.of_octets(o), None{}, em) : {Ct.cr.cts.b.go(~K, ~L.LcBlock64, ~dec, ~L.LcBlock64.to_octets, k, _, o) == o : B.Octets}
        {==}
    case Some{+bl}:
      +em => hi => %Equal.sym(Maybe<&2, L.LcBlock64>, L.LcBlock64.of_octets(o), Some{bl}, em) : {Ct.cr.cts.b(~K, ~L.LcBlock64, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, Ct.cr.cts.b.go(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.to_octets, k, _, o)) == o : B.Octets}
        %Equal.sym(Maybe<&2, L.LcBlock64>, L.LcBlock64.of_octets(L.LcBlock64.to_octets(enc(k, bl))), Some{enc(k, bl)}, CoreL.block64_octets_round_trip(enc(k, bl))) : {Ct.cr.cts.b.go(~K, ~L.LcBlock64, ~dec, ~L.LcBlock64.to_octets, k, _, L.LcBlock64.to_octets(enc(k, bl))) == o : B.Octets}
        %Equal.sym(L.LcBlock64, dec(k, enc(k, bl)), bl, hi) : {L.LcBlock64.to_octets(_) == o : B.Octets}
        CoreL.block64_octets_dual(o, bl, em)

def pc.lc_br(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, ~dec: K -> L.LcBlock64 -> L.LcBlock64, +k: K, +o: B.Octets, hi: {dec(k, enc(k, pc.lc_ebl(o))) == pc.lc_ebl(o) : L.LcBlock64}) -> {Ct.cr.cts.b(~K, ~L.LcBlock64, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, Ct.cr.cts.b(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, o)) == o : B.Octets}:
  pc.lc_br.go(~K, ~enc, ~dec, k, L.LcBlock64.of_octets(o), o)({==})(hi)

def pc.lc_bl.go(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, +k: K, m: Maybe<&2, L.LcBlock64>, +o: B.Octets) -> {L.LcBlock64.of_octets(o) == m : Maybe<&2, L.LcBlock64>} -> {B.Octets.len(Ct.cr.cts.b(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, o)) == B.Octets.len(o) : Nat}:
  match m:
    case None{}:
      em => %Equal.sym(Maybe<&2, L.LcBlock64>, L.LcBlock64.of_octets(o), None{}, em) : {B.Octets.len(Ct.cr.cts.b.go(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.to_octets, k, _, o)) == B.Octets.len(o) : Nat}
        {==}
    case Some{+bl}:
      +em => %Equal.sym(Maybe<&2, L.LcBlock64>, L.LcBlock64.of_octets(o), Some{bl}, em) : {B.Octets.len(Ct.cr.cts.b.go(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.to_octets, k, _, o)) == B.Octets.len(o) : Nat}
        Equal.trans(Nat, B.Octets.len(L.LcBlock64.to_octets(enc(k, bl))), 8n, B.Octets.len(o), PB.pb.lc_len(enc(k, bl)), Equal.sym(Nat, B.Octets.len(o), 8n, Equal.trans(Nat, B.Octets.len(o), B.Octets.len(L.LcBlock64.to_octets(bl)), 8n, Equal.cong(B.Octets, Nat, y => B.Octets.len(y), o, L.LcBlock64.to_octets(bl), Equal.sym(B.Octets, L.LcBlock64.to_octets(bl), o, CoreL.block64_octets_dual(o, bl, em))), PB.pb.lc_len(bl))))

def pc.lc_bl(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, +k: K, +o: B.Octets) -> {B.Octets.len(Ct.cr.cts.b(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, o)) == B.Octets.len(o) : Nat}:
  pc.lc_bl.go(~K, ~enc, k, L.LcBlock64.of_octets(o), o)({==})

def pc.lc_ebls(os: List<&2, B.Octets>) -> List<&2, L.LcBlock64>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      Con{pc.lc_ebl(o), pc.lc_ebls(t)}

def pc.lc_bhd(l: List<&2, L.LcBlock64>) -> L.LcBlock64:
  match l:
    case Nil{}:
      L.LcBlock64{0, 0}
    case Con{x, t}:
      x

def pc.lc_btl(l: List<&2, L.LcBlock64>) -> List<&2, L.LcBlock64>:
  match l:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

def pc.lc_brs_all(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, ~dec: K -> L.LcBlock64 -> L.LcBlock64, +k: K, +os: List<&2, B.Octets>) -> {Laws.crcts.dec_enc(~K, ~L.LcBlock64, ~enc, ~dec, k, pc.lc_ebls(os)) == pc.lc_ebls(os) : List<&2, L.LcBlock64>} -> {pc.brs(~K, ~L.LcBlock64, ~enc, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, os, k) == os : List<&2, B.Octets>}:
  match os:
    case Nil{}:
      h => {==}
    case Con{+o, +t}:
      +h => pc.con2(B.Octets, Ct.cr.cts.b(~K, ~L.LcBlock64, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, Ct.cr.cts.b(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, o)), o, pc.brs(~K, ~L.LcBlock64, ~enc, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, t, k), t, pc.lc_br(~K, ~enc, ~dec, k, o, Equal.cong(List<&2, L.LcBlock64>, L.LcBlock64, l => pc.lc_bhd(l), Laws.crcts.dec_enc(~K, ~L.LcBlock64, ~enc, ~dec, k, pc.lc_ebls(Con{o, t})), pc.lc_ebls(Con{o, t}), h)), pc.lc_brs_all(~K, ~enc, ~dec, k, t)(Equal.cong(List<&2, L.LcBlock64>, List<&2, L.LcBlock64>, l => pc.lc_btl(l), Laws.crcts.dec_enc(~K, ~L.LcBlock64, ~enc, ~dec, k, pc.lc_ebls(Con{o, t})), pc.lc_ebls(Con{o, t}), h)))

def pc.lc_bls_all(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, +k: K, +os: List<&2, B.Octets>) -> {pc.bls(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, os, k) == pc.lns(os) : List<&2, Nat>}:
  match os:
    case Nil{}:
      {==}
    case Con{+o, +t}:
      pc.con2(Nat, B.Octets.len(Ct.cr.cts.b(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, o)), B.Octets.len(o), pc.bls(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, t, k), pc.lns(t), pc.lc_bl(~K, ~enc, k, o), pc.lc_bls_all(~K, ~enc, k, t))

# the ciphertext as long as the message
def pc.lc_len(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, +k: K, +iv: B.Octets, +m: B.Octets) -> {B.Octets.len(Ct.cr.cts.enc.go(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(m)), k, iv, Nil{})) == B.Octets.len(m) : Nat}:
  +xs = B.Octets.to_list(m)
  +ps = pc.PC(B.Octets.to_list(m), 7n, 7n, Nil{}, Nil{})
  +e = pc.E(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, 8n, pc.PC(B.Octets.to_list(m), 7n, 7n, Nil{}, Nil{}), k, iv)
  %Equal.sym(List<&2, List<&2, U32>>, O.CrOct.pieces(1n+7n, xs), ps, pc.pieces(7n, xs)) : {B.Octets.len(Ct.cr.cts.enc.go(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, _, k, iv, Nil{})) == B.Octets.len(m) : Nat}
  %Equal.sym(B.Octets, Ct.cr.cts.enc.go(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, ps, k, iv, Nil{}), B.Octets.concat(Ct.cr.cts.rcat(Nil{}, e)), pc.enc_E(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, ps, k, iv, Nil{})) : {B.Octets.len(_) == B.Octets.len(m) : Nat}
  %pc.olen(B.Octets.concat(e)) : {_ == B.Octets.len(m) : Nat}
  %pc.cl_tls(e) : {B.len(_) == B.Octets.len(m) : Nat}
  %Equal.sym(Nat, B.len(pc.cl(pc.tls(e))), B.len(pc.cl(ps)), pc.lenE(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, 7n, ps, k, iv)(pc.wf_PC(xs, 7n, 7n, Nil{})({==}))(pc.lc_bls_all(~K, ~enc, k, pc.oes(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, 8n, ps, k, iv)))) : {_ == B.Octets.len(m) : Nat}
  %Equal.sym(List<&2, U32>, pc.cl(ps), O.cr.oct.rev(Nil{}, xs), pc.cl_PC(xs, 7n, 7n, Nil{})) : {B.len(_) == B.Octets.len(m) : Nat}
  pc.olen(m)

# decryption of the ciphertext gives the message
def pc.lc_inner(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, ~dec: K -> L.LcBlock64 -> L.LcBlock64, +k: K, inv: @xs: List<&2, L.LcBlock64> -> {Laws.crcts.dec_enc(~K, ~L.LcBlock64, ~enc, ~dec, k, xs) == xs : List<&2, L.LcBlock64>}, +iv: B.Octets, +m: B.Octets) -> {Ct.cr.cts.dec.go(~K, ~L.LcBlock64, ~8n, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(Ct.cr.cts.enc.go(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(m)), k, iv, Nil{}))), k, iv, Nil{}) == m : B.Octets}:
  +xs = B.Octets.to_list(m)
  +ps = pc.PC(B.Octets.to_list(m), 7n, 7n, Nil{}, Nil{})
  +e = pc.E(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, 8n, pc.PC(B.Octets.to_list(m), 7n, 7n, Nil{}, Nil{}), k, iv)
  +os = pc.oes(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, 8n, pc.PC(B.Octets.to_list(m), 7n, 7n, Nil{}, Nil{}), k, iv)
  +hw = pc.wf_PC(xs, 7n, 7n, Nil{})({==})
  +hl = pc.lc_bls_all(~K, ~enc, k, os)
  +hr = pc.lc_brs_all(~K, ~enc, ~dec, k, os)(inv(pc.lc_ebls(os)))
  # the message's pieces, and the ciphertext's bytes
  %Equal.sym(List<&2, List<&2, U32>>, O.CrOct.pieces(1n+7n, xs), ps, pc.pieces(7n, xs)) : {Ct.cr.cts.dec.go(~K, ~L.LcBlock64, ~8n, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(Ct.cr.cts.enc.go(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, _, k, iv, Nil{}))), k, iv, Nil{}) == m : B.Octets}
  %Equal.sym(B.Octets, Ct.cr.cts.enc.go(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, ps, k, iv, Nil{}), B.Octets.concat(Ct.cr.cts.rcat(Nil{}, e)), pc.enc_E(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, ps, k, iv, Nil{})) : {Ct.cr.cts.dec.go(~K, ~L.LcBlock64, ~8n, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(_)), k, iv, Nil{}) == m : B.Octets}
  %pc.cl_tls(e) : {Ct.cr.cts.dec.go(~K, ~L.LcBlock64, ~8n, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, _), k, iv, Nil{}) == m : B.Octets}
  # the ciphertext's pieces are the encrypted pieces
  %Equal.sym(List<&2, List<&2, U32>>, O.CrOct.pieces(1n+7n, pc.cl(pc.tls(e))), pc.PC(pc.cl(pc.tls(e)), 7n, 7n, Nil{}, Nil{}), pc.pieces(7n, pc.cl(pc.tls(e)))) : {Ct.cr.cts.dec.go(~K, ~L.LcBlock64, ~8n, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, _, k, iv, Nil{}) == m : B.Octets}
  %Equal.sym(List<&2, List<&2, U32>>, pc.PC(pc.cl(pc.tls(e)), 7n, 7n, Nil{}, Nil{}), pc.tls(e), pc.L2(pc.tls(e), 7n)(pc.wfE(~K, ~L.LcBlock64, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, 7n, ps, k, iv)(hw)(hl))) : {Ct.cr.cts.dec.go(~K, ~L.LcBlock64, ~8n, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, _, k, iv, Nil{}) == m : B.Octets}
  # which decrypt to the message's pieces
  %Equal.sym(B.Octets, Ct.cr.cts.dec.go(~K, ~L.LcBlock64, ~8n, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, pc.tls(e), k, iv, Nil{}), B.Octets.concat(Ct.cr.cts.rcat(Nil{}, pc.D(~K, ~L.LcBlock64, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, pc.tls(e), k, iv))), pc.dec_D(~K, ~L.LcBlock64, ~8n, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, pc.tls(e), k, iv, Nil{})) : {_ == m : B.Octets}
  %Equal.sym(List<&2, B.Octets>, pc.D(~K, ~L.LcBlock64, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, pc.tls(e), k, iv), pc.ofs(ps), pc.DE(~K, ~L.LcBlock64, ~enc, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, 7n, ps, k, iv)(hw)(hr)(hl)) : {B.Octets.concat(_) == m : B.Octets}
  # joined back
  %Equal.sym(B.Octets, B.Octets.concat(pc.ofs(ps)), B.Octets.of_list(pc.cl(ps)), pc.cat_ofs(ps)) : {_ == m : B.Octets}
  %Equal.sym(List<&2, U32>, pc.cl(ps), O.cr.oct.rev(Nil{}, xs), pc.cl_PC(xs, 7n, 7n, Nil{})) : {B.Octets.of_list(_) == m : B.Octets}
  BL.octets_of_to(m)

def pc.lc_fin(~K: Data, ~enc: K -> L.LcBlock64 -> L.LcBlock64, ~dec: K -> L.LcBlock64 -> L.LcBlock64, +k: K, +iv: B.Octets, +m: B.Octets, inner: {Ct.cr.cts.dec.go(~K, ~L.LcBlock64, ~8n, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(Ct.cr.cts.enc.go(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(m)), k, iv, Nil{}))), k, iv, Nil{}) == m : B.Octets}, lenf: {B.Octets.len(Ct.cr.cts.enc.go(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(m)), k, iv, Nil{})) == B.Octets.len(m) : Nat}, chk: Result<&2, &2, Cr.CrError, Unit>) -> {Ct.cr.cts.check(8n, iv, B.Octets.len(m)) == chk : Result<&2, &2, Cr.CrError, Unit>} -> {Result.bind(&2, &2, Cr.CrError, B.Octets, B.Octets, Result.map(&2, &2, Cr.CrError, Unit, B.Octets, u => Ct.cr.cts.enc.go(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(m)), k, iv, Nil{}), chk), c => Ct.CrCts.decrypt(~K, ~L.LcBlock64, ~8n, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, k, iv, c)) == Result.map(&2, &2, Cr.CrError, B.Octets, B.Octets, c => m, Result.map(&2, &2, Cr.CrError, Unit, B.Octets, u => Ct.cr.cts.enc.go(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(m)), k, iv, Nil{}), chk)) : Result<&2, &2, Cr.CrError, B.Octets>}:
  match chk:
    case Fail{e}:
      hc => {==}
    case Done{+u}:
      +hc => %Equal.sym(Nat, B.Octets.len(Ct.cr.cts.enc.go(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(m)), k, iv, Nil{})), B.Octets.len(m), lenf) : {Result.map(&2, &2, Cr.CrError, Unit, B.Octets, u2 => Ct.cr.cts.dec.go(~K, ~L.LcBlock64, ~8n, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(Ct.cr.cts.enc.go(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(m)), k, iv, Nil{}))), k, iv, Nil{}), Ct.cr.cts.check(8n, iv, _)) == Done{m} : Result<&2, &2, Cr.CrError, B.Octets>}
        %Equal.sym(Result<&2, &2, Cr.CrError, Unit>, Ct.cr.cts.check(8n, iv, B.Octets.len(m)), Done{u}, hc) : {Result.map(&2, &2, Cr.CrError, Unit, B.Octets, u2 => Ct.cr.cts.dec.go(~K, ~L.LcBlock64, ~8n, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(Ct.cr.cts.enc.go(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(m)), k, iv, Nil{}))), k, iv, Nil{}), _) == Done{m} : Result<&2, &2, Cr.CrError, B.Octets>}
        Equal.cong(B.Octets, Result<&2, &2, Cr.CrError, B.Octets>, y => Done{y}, Ct.cr.cts.dec.go(~K, ~L.LcBlock64, ~8n, ~dec, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(Ct.cr.cts.enc.go(~K, ~L.LcBlock64, ~8n, ~enc, ~L.LcBlock64.of_octets, ~L.LcBlock64.to_octets, O.CrOct.pieces(8n, B.Octets.to_list(m)), k, iv, Nil{}))), k, iv, Nil{}), m, inner)

def Laws.lcblock64_cts_round_trip(K, enc, dec, k, inv, iv, m):
  pc.lc_fin(~K, ~enc, ~dec, k, iv, m, pc.lc_inner(~K, ~enc, ~dec, k, inv, iv, m), pc.lc_len(~K, ~enc, k, iv, m), Ct.cr.cts.check(8n, iv, B.Octets.len(m)))({==})
# END GENERATED: formats
