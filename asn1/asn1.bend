# bend-osdev-asn1: BER and DER decoding (ITU-T X.690 (02/2021)), the entry
# file. Bytes become elements (node.bend): identifier octets (8.1.2, with
# high tag numbers), length octets (8.1.3: short, long and indefinite
# forms), contents octets, and end-of-contents octets (8.1.5) after
# indefinite contents. Rules (rules.bend) say what is accepted beyond that
# structure: DER refuses indefinite lengths and lengths in more octets than
# needed (10.1), constructed strings (10.2) and SETs out of order (10.3,
# 11.6).
#
# The identifier octets are always checked to be the ones the encoder writes
# for the tag read (8.1.2.2 and 8.1.2.4.2 c leave no choice), and, under
# min_length, the length octets likewise (10.1): a canonical form is tested
# by encoding the value read again and comparing. A decoder that succeeds
# under DER rules has read exactly what the encoder writes (LAWS.bend:
# encode_decode), and never reads past its buffer (decode_within).
#
# The decoder works on the buffer's bytes as a list; each step is given the
# header already read at the place it starts (A1Head), since Bend computes a
# call's arguments before the call. fuel (one more than the bytes) bounds the
# steps: each element takes at least two octets.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./number.bend as Nu
import ./tag.bend as T
import ./length.bend as L
import ./node.bend as N
import ./rules.bend as R
import ./encode.bend as En
import ./conform.bend as C

# Headers

type A1Head is Data:
  A1HEnd{}
  A1HEoc{rest: List<&2, U32>}
  A1HErr{error: E.Asn1Error}
  A1HPrim{tag: T.Asn1Tag, content: List<&2, U32>, rest: List<&2, U32>}
  A1HDef{tag: T.Asn1Tag, content: List<&2, U32>, rest: List<&2, U32>}
  A1HIndef{tag: T.Asn1Tag, rest: List<&2, U32>}

# what is decoded: one element (A1One), the elements up to the end of the
# input (A1All), or the elements up to end-of-contents octets (A1Eoc)
type A1Mode is Data:
  A1One{}
  A1All{}
  A1Eoc{}

type A1Out is Data:
  A1Out{nodes: List<&2, N.Asn1Node>, rest: List<&2, U32>}

# One element and the octets after it
type Asn1Read is Data:
  Asn1Read{node: N.Asn1Node, rest: B.Octets}

type Asn1Tlv is Data:
  Asn1Tlv{node: N.Asn1Node, raw: B.Octets}

type Asn1TlvRead is Data:
  Asn1TlvRead{tlv: Asn1Tlv, rest: B.Octets}

# the next element of a run of elements, or its end
type A1Step is Data:
  A1StepEnd{}
  A1StepErr{error: E.Asn1Error}
  A1StepOne{tlv: Asn1Tlv, rest: B.Octets}

def a1.head.fit(ok: Bool, +t: T.Asn1Tag, cons: Bool, +n: Nat, +rest: List<&2, U32>) -> A1Head:
  match ok cons:
    case False{} _:
      A1HErr{E.Asn1Truncated{}}
    case True{} False{}:
      A1HPrim{t, B.take(n, rest), B.drop(n, rest)}
    case True{} True{}:
      A1HDef{t, B.take(n, rest), B.drop(n, rest)}

def a1.head.min(ok: Bool, +t: T.Asn1Tag, cons: Bool, +n: Nat, +rest: List<&2, U32>) -> A1Head:
  match ok:
    case True{}:
      a1.head.fit(Nat.is_le(n, List.length(&2, U32, rest)), t, cons, n, rest)
    case False{}:
      A1HErr{E.Asn1NonMinimalLength{}}

def a1.head.indef(allowed: Bool, cons: Bool, +t: T.Asn1Tag, rest: List<&2, U32>) -> A1Head:
  match allowed cons:
    case False{} _:
      A1HErr{E.Asn1Indefinite{}}
    case True{} False{}:
      A1HErr{E.Asn1PrimIndefinite{}}
    case True{} True{}:
      A1HIndef{t, rest}

def a1.head.len(+r: R.Asn1Rules, +t: T.Asn1Tag, cons: Bool, l: L.A1Len) -> A1Head:
  match l:
    case L.A1LErr{e}:
      A1HErr{e}
    case L.A1LIndef{rest}:
      a1.head.indef(R.Asn1Rules.indefinite(r), cons, t, rest)
    case L.A1LDef{+n, u, rest}:
      a1.head.min(R.a1.when(R.Asn1Rules.min_length(r), Bool.and(L.a1.len_ok(n), Nu.a1.leq(L.a1.len_bytes(n), u))), t, cons, n, rest)

def a1.head.eoc2(z: Bool, t: List<&2, U32>) -> A1Head:
  match z:
    case True{}:
      A1HEoc{t}
    case False{}:
      A1HErr{E.Asn1ReservedTag{}}

def a1.head.eoc(rest: List<&2, U32>) -> A1Head:
  match rest:
    case Nil{}:
      A1HErr{E.Asn1Truncated{}}
    case Con{y, t}:
      a1.head.eoc2(Nat.is_eq(U32.to_nat(y), 0n), t)

def a1.head.res(u0: Bool, +r: R.Asn1Rules, c: T.Asn1Class, cons: Bool, n: Nat, rest: List<&2, U32>) -> A1Head:
  match u0 cons:
    case True{} False{}:
      a1.head.eoc(rest)
    case True{} True{}:
      A1HErr{E.Asn1ReservedTag{}}
    case False{} _:
      a1.head.len(r, T.Asn1Tag{c, n}, cons, L.a1.len.read(rest))

def a1.head.tag2(ok: Bool, +r: R.Asn1Rules, +c: T.Asn1Class, cons: Bool, +n: Nat, rest: List<&2, U32>) -> A1Head:
  match ok:
    case True{}:
      a1.head.res(En.a1.is_univ0(c, n), r, c, cons, n, rest)
    case False{}:
      A1HErr{E.Asn1BadTag{}}

# the identifier octets read (ids) must be those of the tag read (8.1.2)
def a1.head.tag(+r: R.Asn1Rules, +c: T.Asn1Class, +cons: Bool, +n: Nat, ids: List<&2, U32>, rest: List<&2, U32>) -> A1Head:
  a1.head.tag2(Nu.a1.leq(T.a1.id_bytes(c, cons, n), ids), r, c, cons, n, rest)

def a1.head.num(+r: R.Asn1Rules, +c: T.Asn1Class, +cons: Bool, x: U32, m: Maybe<&2, Nu.A1Num>) -> A1Head:
  match m:
    case None{}:
      A1HErr{E.Asn1Truncated{}}
    case Some{Nu.A1Num{n, u, rest}}:
      a1.head.tag(r, c, cons, n, Con{x, u}, rest)

def a1.head.hi(hi: Bool, +r: R.Asn1Rules, +c: T.Asn1Class, +cons: Bool, +low: Nat, x: U32, t: List<&2, U32>) -> A1Head:
  match hi:
    case True{}:
      a1.head.num(r, c, cons, x, Nu.a1.r128(t, True{}, Nu.a1.max_octets(), 0n))
    case False{}:
      a1.head.tag(r, c, cons, low, [x], t)

def a1.head.id(+r: R.Asn1Rules, i: T.A1Id1, x: U32, t: List<&2, U32>) -> A1Head:
  match i:
    case T.A1Id1{c, cons, +low}:
      a1.head.hi(Nat.is_eq(low, 31n), r, c, cons, low, x, t)

# the header at the start of xs, as read
def a1.head0(+r: R.Asn1Rules, xs: List<&2, U32>) -> A1Head:
  match xs:
    case Nil{}:
      A1HEnd{}
    case Con{+x, t}:
      a1.head.id(r, T.a1.id1(U32.to_nat(x)), x, t)

# The canonical check (min_length): the octets before the contents must be
# the encoder's octets for the tag, form and length read, and the contents
# and what follows are cut from the input after them. (a1.head0 has checked
# each part already; this states the whole, so that what is accepted is
# exactly what the encoder writes.)

# the octets before an element's contents, as the encoder writes them
def a1.hdr(c: T.Asn1Class, cons: Bool, +n: Nat, +l: Nat) -> List<&2, U32>:
  List.append(&2, U32, T.a1.id_bytes(c, cons, n), L.a1.len_bytes(l))

def a1.canon.ok(+c: T.Asn1Class, +cons: Bool, +n: Nat, +l: Nat, +xs: List<&2, U32>) -> Bool:
  +hd = a1.hdr(c, cons, n, l)
  +k = List.length(&2, U32, hd)
  Bool.and(Bool.not(En.a1.is_univ0(c, n)), Bool.and(T.a1.id_ok(n), Bool.and(L.a1.len_ok(l), Bool.and(Nu.a1.leq(hd, B.take(k, xs)), Nat.is_le(l, List.length(&2, U32, B.drop(k, xs)))))))

def a1.canon.mk(ok: Bool, +t: T.Asn1Tag, cons: Bool, +k: Nat, +l: Nat, +xs: List<&2, U32>) -> A1Head:
  match ok cons:
    case False{} _:
      A1HErr{E.Asn1NonMinimalLength{}}
    case True{} False{}:
      +d = B.drop(k, xs)
      A1HPrim{t, B.take(l, d), B.drop(l, d)}
    case True{} True{}:
      +d = B.drop(k, xs)
      A1HDef{t, B.take(l, d), B.drop(l, d)}

def a1.canon(+xs: List<&2, U32>, h: A1Head) -> A1Head:
  match h:
    case A1HPrim{T.Asn1Tag{+c, +n}, cs, rest}:
      +l = List.length(&2, U32, cs)
      a1.canon.mk(a1.canon.ok(c, False{}, n, l, xs), T.Asn1Tag{c, n}, False{}, List.length(&2, U32, a1.hdr(c, False{}, n, l)), l, xs)
    case A1HDef{T.Asn1Tag{+c, +n}, cs, rest}:
      +l = List.length(&2, U32, cs)
      a1.canon.mk(a1.canon.ok(c, True{}, n, l, xs), T.Asn1Tag{c, n}, True{}, List.length(&2, U32, a1.hdr(c, True{}, n, l)), l, xs)
    case A1HEnd{}:
      A1HEnd{}
    case A1HEoc{rest}:
      A1HEoc{rest}
    case A1HErr{e}:
      A1HErr{e}
    case A1HIndef{t, rest}:
      A1HIndef{t, rest}

def a1.head.indef_off(allowed: Bool, h: A1Head) -> A1Head:
  match allowed:
    case True{}:
      h
    case False{}:
      match h:
        case A1HIndef{t, rest}:
          A1HErr{E.Asn1Indefinite{}}
        case A1HEnd{}:
          A1HEnd{}
        case A1HEoc{rest}:
          A1HEoc{rest}
        case A1HErr{e}:
          A1HErr{e}
        case A1HPrim{t, cs, rest}:
          A1HPrim{t, cs, rest}
        case A1HDef{t, cs, rest}:
          A1HDef{t, cs, rest}

def a1.head.fin2(m: Bool, +xs: List<&2, U32>, h: A1Head) -> A1Head:
  match m:
    case True{}:
      a1.canon(xs, h)
    case False{}:
      h

def a1.head.fin(+r: R.Asn1Rules, +xs: List<&2, U32>, h: A1Head) -> A1Head:
  a1.head.fin2(R.Asn1Rules.min_length(r), xs, a1.head.indef_off(R.Asn1Rules.indefinite(r), h))

# the end of the input is the end only when nothing is left
def a1.head.nend(xs: List<&2, U32>, h: A1Head) -> A1Head:
  match xs:
    case Nil{}:
      h
    case Con{y, t}:
      match h:
        case A1HEnd{}:
          A1HErr{E.Asn1Truncated{}}
        case A1HEoc{rest}:
          A1HEoc{rest}
        case A1HErr{e}:
          A1HErr{e}
        case A1HPrim{u, cs, rest}:
          A1HPrim{u, cs, rest}
        case A1HDef{u, cs, rest}:
          A1HDef{u, cs, rest}
        case A1HIndef{u, rest}:
          A1HIndef{u, rest}

# the header at the start of xs
def a1.head(+r: R.Asn1Rules, +xs: List<&2, U32>) -> A1Head:
  a1.head.nend(xs, a1.head.fin(r, xs, a1.head0(r, xs)))

# Elements

def a1.at_end(mode: A1Mode) -> Result<&2, &2, E.Asn1Error, A1Out>:
  match mode:
    case A1One{}:
      Fail{E.Asn1Truncated{}}
    case A1All{}:
      Done{A1Out{Nil{}, Nil{}}}
    case A1Eoc{}:
      Fail{E.Asn1NoEoc{}}

def a1.at_eoc(mode: A1Mode, rest: List<&2, U32>) -> Result<&2, &2, E.Asn1Error, A1Out>:
  match mode:
    case A1One{}:
      Fail{E.Asn1BadEoc{}}
    case A1All{}:
      Fail{E.Asn1BadEoc{}}
    case A1Eoc{}:
      Done{A1Out{Nil{}, rest}}

def a1.mk_prim.pick(ok: Bool, t: T.Asn1Tag, o: B.Octets) -> Result<&2, &2, E.Asn1Error, N.Asn1Node>:
  match ok:
    case True{}:
      Done{N.Asn1Prim{t, o}}
    case False{}:
      Fail{E.Asn1BadForm{}}

def a1.mk_prim(+r: R.Asn1Rules, +t: T.Asn1Tag, o: B.Octets) -> Result<&2, &2, E.Asn1Error, N.Asn1Node>:
  a1.mk_prim.pick(R.a1.form_ok(r, t, False{}), t, o)

def a1.mk_cons.set(ok: Bool, t: T.Asn1Tag, xs: List<&2, N.Asn1Node>) -> Result<&2, &2, E.Asn1Error, N.Asn1Node>:
  match ok:
    case True{}:
      Done{N.Asn1Cons{t, xs}}
    case False{}:
      Fail{E.Asn1SetOrder{}}

def a1.mk_cons.form(ok: Bool, +r: R.Asn1Rules, +t: T.Asn1Tag, +xs: List<&2, N.Asn1Node>) -> Result<&2, &2, E.Asn1Error, N.Asn1Node>:
  match ok:
    case True{}:
      a1.mk_cons.set(C.a1.set_ok(r, t, xs), t, xs)
    case False{}:
      Fail{E.Asn1BadForm{}}

# a constructed element from its decoded contents
def a1.mk_cons(+r: R.Asn1Rules, +t: T.Asn1Tag, inner: Result<&2, &2, E.Asn1Error, A1Out>) -> Result<&2, &2, E.Asn1Error, N.Asn1Node>:
  match inner:
    case Fail{e}:
      Fail{e}
    case Done{A1Out{+xs, rest}}:
      a1.mk_cons.form(R.a1.form_ok(r, t, True{}), r, t, xs)

def a1.out_rest(inner: Result<&2, &2, E.Asn1Error, A1Out>) -> List<&2, U32>:
  match inner:
    case Fail{e}:
      Nil{}
    case Done{A1Out{xs, rest}}:
      rest

def a1.one(n: Result<&2, &2, E.Asn1Error, N.Asn1Node>, rest: List<&2, U32>) -> Result<&2, &2, E.Asn1Error, A1Out>:
  match n:
    case Fail{e}:
      Fail{e}
    case Done{x}:
      Done{A1Out{[x], rest}}

def a1.more(n: Result<&2, &2, E.Asn1Error, N.Asn1Node>, more: Result<&2, &2, E.Asn1Error, A1Out>) -> Result<&2, &2, E.Asn1Error, A1Out>:
  match n more:
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}
    case Done{x} Done{A1Out{xs, rest}}:
      Done{A1Out{Con{x, xs}, rest}}

# the elements from header h on, in mode m
def a1.dec(fuel: Nat, +r: R.Asn1Rules, mode: A1Mode, h: A1Head) -> Result<&2, &2, E.Asn1Error, A1Out>:
  match fuel:
    case 0n:
      Fail{E.Asn1Exhausted{}}
    case 1n+ +f:
      match mode:
        case A1One{}:
          match h:
            case A1HEnd{}:
              a1.at_end(A1One{})
            case A1HEoc{rest}:
              a1.at_eoc(A1One{}, rest)
            case A1HErr{e}:
              Fail{e}
            case A1HPrim{+t, cs, +rest}:
              a1.one(a1.mk_prim(r, t, B.Octets.of_list(cs)), rest)
            case A1HDef{+t, +cs, +rest}:
              a1.one(a1.mk_cons(r, t, a1.dec(f, r, A1All{}, a1.head(r, cs))), rest)
            case A1HIndef{+t, +rest}:
              +inner = a1.dec(f, r, A1Eoc{}, a1.head(r, rest))
              a1.one(a1.mk_cons(r, t, inner), a1.out_rest(inner))
        case A1All{}:
          match h:
            case A1HEnd{}:
              a1.at_end(A1All{})
            case A1HEoc{rest}:
              a1.at_eoc(A1All{}, rest)
            case A1HErr{e}:
              Fail{e}
            case A1HPrim{+t, cs, +rest}:
              a1.more(a1.mk_prim(r, t, B.Octets.of_list(cs)), a1.dec(f, r, A1All{}, a1.head(r, rest)))
            case A1HDef{+t, +cs, +rest}:
              a1.more(a1.mk_cons(r, t, a1.dec(f, r, A1All{}, a1.head(r, cs))), a1.dec(f, r, A1All{}, a1.head(r, rest)))
            case A1HIndef{+t, +rest}:
              +inner = a1.dec(f, r, A1Eoc{}, a1.head(r, rest))
              a1.more(a1.mk_cons(r, t, inner), a1.dec(f, r, A1All{}, a1.head(r, a1.out_rest(inner))))
        case A1Eoc{}:
          match h:
            case A1HEnd{}:
              a1.at_end(A1Eoc{})
            case A1HEoc{rest}:
              a1.at_eoc(A1Eoc{}, rest)
            case A1HErr{e}:
              Fail{e}
            case A1HPrim{+t, cs, +rest}:
              a1.more(a1.mk_prim(r, t, B.Octets.of_list(cs)), a1.dec(f, r, A1Eoc{}, a1.head(r, rest)))
            case A1HDef{+t, +cs, +rest}:
              a1.more(a1.mk_cons(r, t, a1.dec(f, r, A1All{}, a1.head(r, cs))), a1.dec(f, r, A1Eoc{}, a1.head(r, rest)))
            case A1HIndef{+t, +rest}:
              +inner = a1.dec(f, r, A1Eoc{}, a1.head(r, rest))
              a1.more(a1.mk_cons(r, t, inner), a1.dec(f, r, A1Eoc{}, a1.head(r, a1.out_rest(inner))))

# the decoder from the start of xs, in mode m (fuel: one more than the
# octets, as each element takes at least two)
def a1.run(+r: R.Asn1Rules, mode: A1Mode, +xs: List<&2, U32>) -> Result<&2, &2, E.Asn1Error, A1Out>:
  a1.dec(Nat.add(1n, List.length(&2, U32, xs)), r, mode, a1.head(r, xs))

# Decoding

def a1.read.out(res: Result<&2, &2, E.Asn1Error, A1Out>) -> Result<&2, &2, E.Asn1Error, Asn1Read>:
  match res:
    case Fail{e}:
      Fail{e}
    case Done{A1Out{Nil{}, rest}}:
      Fail{E.Asn1Truncated{}}
    case Done{A1Out{Con{n, ns}, rest}}:
      Done{Asn1Read{n, B.Octets.of_list(rest)}}

# the first element of b and the octets after it
def Asn1.decode_prefix(+r: R.Asn1Rules, b: B.Octets) -> Result<&2, &2, E.Asn1Error, Asn1Read>:
  a1.read.out(a1.run(r, A1One{}, B.Octets.to_list(b)))

def a1.top.end(ok: Bool, n: N.Asn1Node) -> Result<&2, &2, E.Asn1Error, N.Asn1Node>:
  match ok:
    case True{}:
      Done{n}
    case False{}:
      Fail{E.Asn1Trailing{}}

def a1.top(+r: R.Asn1Rules, res: Result<&2, &2, E.Asn1Error, A1Out>) -> Result<&2, &2, E.Asn1Error, N.Asn1Node>:
  match res:
    case Fail{e}:
      Fail{e}
    case Done{A1Out{Nil{}, rest}}:
      Fail{E.Asn1Truncated{}}
    case Done{A1Out{Con{n, Con{m, ms}}, rest}}:
      Fail{E.Asn1Truncated{}}
    case Done{A1Out{Con{n, Nil{}}, Nil{}}}:
      Done{n}
    case Done{A1Out{Con{n, Nil{}}, Con{y, t}}}:
      a1.top.end(R.Asn1Rules.trailing(r), n)

# the element b holds; octets after it are refused unless r.trailing
def Asn1.decode(+r: R.Asn1Rules, b: B.Octets) -> Result<&2, &2, E.Asn1Error, N.Asn1Node>:
  a1.top(r, a1.run(r, A1One{}, B.Octets.to_list(b)))

def a1.all.out(res: Result<&2, &2, E.Asn1Error, A1Out>) -> Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>:
  match res:
    case Fail{e}:
      Fail{e}
    case Done{A1Out{ns, rest}}:
      Done{ns}

# the elements b holds, one after another, to its end
def Asn1.decode_all(+r: R.Asn1Rules, b: B.Octets) -> Result<&2, &2, E.Asn1Error, List<&2, N.Asn1Node>>:
  a1.all.out(a1.run(r, A1All{}, B.Octets.to_list(b)))

# Raw elements: an element with the octets it was read from

def Asn1Tlv.node(x: Asn1Tlv) -> N.Asn1Node:
  match x:
    case Asn1Tlv{n, raw}:
      n

def Asn1Tlv.raw(x: Asn1Tlv) -> B.Octets:
  match x:
    case Asn1Tlv{n, raw}:
      raw

# the octets of each element, in order (those Asn1.read_all answers join
# back to its input: LAWS.bend, read_all_split)
def Asn1.raws(xs: List<&2, Asn1Tlv>) -> List<&2, B.Octets>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{Asn1Tlv.raw(x), Asn1.raws(t)}

def a1.tlv.out(+xs: List<&2, U32>, res: Result<&2, &2, E.Asn1Error, A1Out>) -> Result<&2, &2, E.Asn1Error, Asn1TlvRead>:
  match res:
    case Fail{e}:
      Fail{e}
    case Done{A1Out{Nil{}, rest}}:
      Fail{E.Asn1Truncated{}}
    case Done{A1Out{Con{n, ns}, +rest}}:
      +used = Nat.sub(List.length(&2, U32, xs), List.length(&2, U32, rest))
      Done{Asn1TlvRead{Asn1Tlv{n, B.Octets.of_list(B.take(used, xs))}, B.Octets.of_list(rest)}}

# the first element of b with the octets it takes, and the octets after it
def Asn1.read(+r: R.Asn1Rules, b: B.Octets) -> Result<&2, &2, E.Asn1Error, Asn1TlvRead>:
  +xs = B.Octets.to_list(b)
  a1.tlv.out(xs, a1.run(r, A1One{}, xs))

def a1.reads.cons(x: Asn1Tlv, r: Result<&2, &2, E.Asn1Error, List<&2, Asn1Tlv>>) -> Result<&2, &2, E.Asn1Error, List<&2, Asn1Tlv>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{xs}:
      Done{Con{x, xs}}

def a1.step.of(res: Result<&2, &2, E.Asn1Error, Asn1TlvRead>) -> A1Step:
  match res:
    case Fail{e}:
      A1StepErr{e}
    case Done{Asn1TlvRead{x, rest}}:
      A1StepOne{x, rest}

def a1.step.pick(xs: List<&2, U32>, +r: R.Asn1Rules, b: B.Octets) -> A1Step:
  match xs:
    case Nil{}:
      A1StepEnd{}
    case Con{y, t}:
      a1.step.of(Asn1.read(r, b))

def a1.step(+r: R.Asn1Rules, +b: B.Octets) -> A1Step:
  a1.step.pick(B.Octets.to_list(b), r, b)

# the elements of a run, from the first step on (fuel bounds the elements)
def a1.reads.go(fuel: Nat, +r: R.Asn1Rules, s: A1Step) -> Result<&2, &2, E.Asn1Error, List<&2, Asn1Tlv>>:
  match fuel s:
    case _ A1StepEnd{}:
      Done{Nil{}}
    case _ A1StepErr{e}:
      Fail{e}
    case 0n A1StepOne{x, rest}:
      Fail{E.Asn1Exhausted{}}
    case 1n+f A1StepOne{x, +rest}:
      a1.reads.cons(x, a1.reads.go(f, r, a1.step(r, rest)))

# the elements of b, each with its octets
def Asn1.read_all(+r: R.Asn1Rules, +b: B.Octets) -> Result<&2, &2, E.Asn1Error, List<&2, Asn1Tlv>>:
  a1.reads.go(Nat.add(1n, B.Octets.len(b)), r, a1.step(r, b))

def a1.content.of(h: A1Head) -> List<&2, U32>:
  match h:
    case A1HPrim{t, cs, rest}:
      cs
    case A1HDef{t, cs, rest}:
      cs
    case A1HIndef{t, +rest}:
      B.take(Nat.sub(List.length(&2, U32, rest), 2n), rest)
    case A1HEnd{}:
      Nil{}
    case A1HEoc{rest}:
      Nil{}
    case A1HErr{e}:
      Nil{}

# the contents octets of an element read with Asn1.read (an indefinite
# element's without its end-of-contents octets)
def Asn1.contents(+r: R.Asn1Rules, x: Asn1Tlv) -> B.Octets:
  match x:
    case Asn1Tlv{n, raw}:
      B.Octets.of_list(a1.content.of(a1.head(r, B.Octets.to_list(raw))))

# the elements of a constructed element read with Asn1.read, each with its
# octets
def Asn1.items(+r: R.Asn1Rules, x: Asn1Tlv) -> Result<&2, &2, E.Asn1Error, List<&2, Asn1Tlv>>:
  Asn1.read_all(r, Asn1.contents(r, x))
