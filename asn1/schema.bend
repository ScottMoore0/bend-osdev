# bend-osdev-asn1, schemas: an ASN.1 type described as a Bend value, and a
# generic matcher that reads an element's octets against it. The
# counterpart of the kernel's asn1_compiler output (a table the decoder
# walks), here as data:
#
#   Asn1SAny{}                 any one element
#   Asn1SElem{tag}             one element with this tag
#   Asn1SSeq{tag, fields}      a constructed element whose elements match
#                              the fields in order (SEQUENCE, X.690 8.9, or
#                              an IMPLICIT-tagged one)
#   Asn1SOf{tag, item, set}    a constructed element whose elements all
#                              match item (SEQUENCE OF / SET OF, 8.10, 8.12);
#                              for a SET OF, under the SET OF order rule its
#                              elements' octets must ascend (11.6)
#   Asn1SChoice{alts}          the first alternative whose tags admit the
#                              element (CHOICE, 8.13)
#   Asn1SExplicit{num, inner}  [num] EXPLICIT inner (8.14.3)
#   Asn1SOpt{inner}            OPTIONAL: absent unless the next element's
#                              tag is one inner admits
#   Asn1SDefault{inner, value} DEFAULT value: absent as for OPTIONAL; under
#                              the values rule, the default value must not
#                              be encoded (11.5)
#
# A match keeps each element's octets (Asn1Tlv: the element and the exact
# octets it was read from), so signed parts can be checked later.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tag.bend as T
import ./node.bend as N
import ./rules.bend as R
import ./encode.bend as En
import ./conform.bend as C
import ./number.bend as Nu
import ./asn1.bend as A

type Asn1Schema is Data:
  Asn1SAny{}
  Asn1SElem{tag: T.Asn1Tag}
  Asn1SSeq{tag: T.Asn1Tag, fields: List<&2, Asn1Schema>}
  Asn1SOf{tag: T.Asn1Tag, item: Asn1Schema, set: Bool}
  Asn1SChoice{alts: List<&2, Asn1Schema>}
  Asn1SExplicit{num: Nat, inner: Asn1Schema}
  Asn1SOpt{inner: Asn1Schema}
  Asn1SDefault{inner: Asn1Schema, value: N.Asn1Node}

type Asn1Match is Data:
  Asn1MElem{tlv: A.Asn1Tlv}
  Asn1MSeq{tlv: A.Asn1Tlv, items: List<&2, Asn1Match>}
  Asn1MChoice{index: Nat, m: Asn1Match}
  Asn1MExplicit{tlv: A.Asn1Tlv, m: Asn1Match}
  Asn1MAbsent{}
  Asn1MDefault{value: N.Asn1Node}

# Common schemas

type A1Slot is Data:
  A1Slot{schema: Asn1Schema, elem: Maybe<&2, A.Asn1Tlv>}

type A1Aligned is Data:
  A1Aligned{slots: List<&2, A1Slot>, extra: Bool}

type A1Work is Data:
  A1WSlots{slots: List<&2, A1Slot>, extra: Bool}
  A1WOne{schema: Asn1Schema, tlv: A.Asn1Tlv}
  A1WNone{}

type A1Pick is Data:
  A1Pick{index: Nat, schema: Asn1Schema}

def Asn1S.seq(fields: List<&2, Asn1Schema>) -> Asn1Schema:
  Asn1SSeq{T.Asn1Tag.sequence(), fields}

def Asn1S.seq_of(item: Asn1Schema) -> Asn1Schema:
  Asn1SOf{T.Asn1Tag.sequence(), item, False{}}

def Asn1S.set_of(item: Asn1Schema) -> Asn1Schema:
  Asn1SOf{T.Asn1Tag.set(), item, True{}}

def Asn1S.elem(t: T.Asn1Tag) -> Asn1Schema:
  Asn1SElem{t}

def Asn1S.any() -> Asn1Schema:
  Asn1SAny{}

def Asn1S.opt(s: Asn1Schema) -> Asn1Schema:
  Asn1SOpt{s}

def Asn1S.explicit(n: Nat, s: Asn1Schema) -> Asn1Schema:
  Asn1SExplicit{n, s}

# [n] IMPLICIT of a primitive type, as an element
def Asn1S.ctx(n: Nat) -> Asn1Schema:
  Asn1SElem{T.Asn1Tag.context(n)}

# Which tags a schema admits as its first element (fuel bounds the nesting)

def Asn1S.depth() -> Nat:
  64n

def a1.s.admits(fuel: Nat, ss: List<&2, Asn1Schema>, +t: T.Asn1Tag) -> Bool:
  match fuel ss:
    case _ Nil{}:
      False{}
    case 0n _:
      False{}
    case 1n+ +f Con{Asn1SAny{}, rest}:
      True{}
    case 1n+ +f Con{Asn1SElem{u}, rest}:
      Bool.or(T.Asn1Tag.is_eq(u, t), a1.s.admits(f, rest, t))
    case 1n+ +f Con{Asn1SSeq{u, fs}, rest}:
      Bool.or(T.Asn1Tag.is_eq(u, t), a1.s.admits(f, rest, t))
    case 1n+ +f Con{Asn1SOf{u, i, st}, rest}:
      Bool.or(T.Asn1Tag.is_eq(u, t), a1.s.admits(f, rest, t))
    case 1n+ +f Con{Asn1SChoice{alts}, rest}:
      Bool.or(a1.s.admits(f, alts, t), a1.s.admits(f, rest, t))
    case 1n+ +f Con{Asn1SExplicit{n, i}, rest}:
      Bool.or(T.Asn1Tag.is_eq(T.Asn1Tag.context(n), t), a1.s.admits(f, rest, t))
    case 1n+ +f Con{Asn1SOpt{i}, rest}:
      Bool.or(a1.s.admits(f, [i], t), a1.s.admits(f, rest, t))
    case 1n+ +f Con{Asn1SDefault{i, v}, rest}:
      Bool.or(a1.s.admits(f, [i], t), a1.s.admits(f, rest, t))

# whether schema s admits an element of tag t first
def Asn1S.admits(s: Asn1Schema, +t: T.Asn1Tag) -> Bool:
  a1.s.admits(Asn1S.depth(), [s], t)

# Fields against elements: each optional field takes the next element only
# when its tags admit it

def a1.s.tlv_tag(x: A.Asn1Tlv) -> T.Asn1Tag:
  match x:
    case A.Asn1Tlv{n, raw}:
      N.Asn1Node.tag(n)

def a1.s.optional(s: Asn1Schema) -> Bool:
  match s:
    case Asn1SOpt{i}:
      True{}
    case Asn1SDefault{i, v}:
      True{}
    case _:
      False{}

# whether field s takes the next element of es
def a1.s.hit(+s: Asn1Schema, es: List<&2, A.Asn1Tlv>) -> Bool:
  match es:
    case Nil{}:
      False{}
    case Con{e, t}:
      Bool.or(Bool.not(a1.s.optional(s)), Asn1S.admits(s, a1.s.tlv_tag(e)))

def a1.s.hit_head(fs: List<&2, Asn1Schema>, +es: List<&2, A.Asn1Tlv>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{s, t}:
      a1.s.hit(s, es)

def a1.s.slot(x: A1Slot, a: A1Aligned) -> A1Aligned:
  match a:
    case A1Aligned{xs, ex}:
      A1Aligned{Con{x, xs}, ex}

# Work for the matcher

def a1.s.align(fs: List<&2, Asn1Schema>, hit: Bool, es: List<&2, A.Asn1Tlv>) -> A1Aligned:
  match fs hit es:
    case Nil{} _ Nil{}:
      A1Aligned{Nil{}, False{}}
    case Nil{} _ Con{e, t}:
      A1Aligned{Nil{}, True{}}
    case Con{s, +rest} True{} Con{e, +t}:
      a1.s.slot(A1Slot{s, Some{e}}, a1.s.align(rest, a1.s.hit_head(rest, t), t))
    case Con{s, +rest} _ +es2:
      a1.s.slot(A1Slot{s, None{}}, a1.s.align(rest, a1.s.hit_head(rest, es2), es2))

def a1.s.ok1(r: Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>) -> Result<&2, &2, E.Asn1Error, Asn1Match>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{[m]}:
      Done{m}
    case Done{ms}:
      Fail{E.Asn1SchemaMismatch{}}

def a1.s.cons(a: Result<&2, &2, E.Asn1Error, Asn1Match>, b: Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>) -> Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>:
  match a b:
    case Fail{e} _:
      Fail{e}
    case Done{x} Fail{e}:
      Fail{e}
    case Done{x} Done{xs}:
      Done{Con{x, xs}}

def a1.s.inner(s: Asn1Schema) -> Asn1Schema:
  match s:
    case Asn1SOpt{i}:
      i
    case Asn1SDefault{i, v}:
      i
    case s2:
      s2

def a1.s.slot_work(s: Asn1Schema, me: Maybe<&2, A.Asn1Tlv>) -> A1Work:
  match me:
    case None{}:
      A1WNone{}
    case Some{e}:
      A1WOne{a1.s.inner(s), e}

def a1.node_eq(a: N.Asn1Node, b: N.Asn1Node) -> Bool:
  Nu.a1.leq(En.a1.enc_list([a], Nil{}), En.a1.enc_list([b], Nil{}))

def a1.s.default_ok(+der: Bool, s: Asn1Schema, e: A.Asn1Tlv) -> Bool:
  match s e:
    case Asn1SDefault{i, v} A.Asn1Tlv{n, raw}:
      R.a1.when(der, Bool.not(a1.node_eq(n, v)))
    case _ _:
      True{}

def a1.s.present(ok: Bool, r: Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>) -> Result<&2, &2, E.Asn1Error, Asn1Match>:
  match ok:
    case True{}:
      a1.s.ok1(r)
    case False{}:
      Fail{E.Asn1SchemaDefault{}}

def a1.s.slot_res(+der: Bool, me: Maybe<&2, A.Asn1Tlv>, s: Asn1Schema, r: Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>) -> Result<&2, &2, E.Asn1Error, Asn1Match>:
  match me s:
    case None{} Asn1SOpt{i}:
      Done{Asn1MAbsent{}}
    case None{} Asn1SDefault{i, v}:
      Done{Asn1MDefault{v}}
    case None{} _:
      Fail{E.Asn1SchemaMissing{}}
    case Some{+e} +s2:
      a1.s.present(a1.s.default_ok(der, s2, e), r)

def a1.s.wrap_seq(e: A.Asn1Tlv, r: Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>) -> Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>:
  match r:
    case Fail{x}:
      Fail{x}
    case Done{ms}:
      Done{[Asn1MSeq{e, ms}]}

def a1.s.wrap_choice(i: Nat, r: Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>) -> Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>:
  match r:
    case Fail{x}:
      Fail{x}
    case Done{[m]}:
      Done{[Asn1MChoice{i, m}]}
    case Done{ms}:
      Fail{E.Asn1SchemaMismatch{}}

def a1.s.wrap_explicit(e: A.Asn1Tlv, r: Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>) -> Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>:
  match r:
    case Fail{x}:
      Fail{x}
    case Done{[m]}:
      Done{[Asn1MExplicit{e, m}]}
    case Done{ms}:
      Fail{E.Asn1SchemaMismatch{}}

def a1.s.tag_ok(+t: T.Asn1Tag, cons: Bool, e: A.Asn1Tlv) -> Bool:
  match e:
    case A.Asn1Tlv{+n, raw}:
      Bool.and(T.Asn1Tag.is_eq(t, N.Asn1Node.tag(n)), Bool.or(Bool.not(cons), N.Asn1Node.is_cons(n)))

def a1.s.items_or_nil(r: Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>) -> List<&2, A.Asn1Tlv>:
  match r:
    case Fail{e}:
      Nil{}
    case Done{xs}:
      xs

def a1.s.items_err(r: Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>, m: Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>) -> Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{xs}:
      m

def a1.s.gate(ok: Bool, m: Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>) -> Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>:
  match ok:
    case True{}:
      m
    case False{}:
      Fail{E.Asn1SchemaMismatch{}}

def a1.s.work_of(a: A1Aligned) -> A1Work:
  match a:
    case A1Aligned{sl, ex}:
      A1WSlots{sl, ex}

def a1.s.seq_work(+fs: List<&2, Asn1Schema>, +xs: List<&2, A.Asn1Tlv>) -> A1Work:
  a1.s.work_of(a1.s.align(fs, a1.s.hit_head(fs, xs), xs))

def a1.s.of_slots(xs: List<&2, A.Asn1Tlv>, +item: Asn1Schema) -> List<&2, A1Slot>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{A1Slot{item, Some{x}}, a1.s.of_slots(t, item)}

def a1.s.raws_sorted(xs: List<&2, A.Asn1Tlv>, prev: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{A.Asn1Tlv{n, raw}, t}:
      +cur = B.Octets.to_list(raw)
      Bool.and(C.a1.le_pad(prev, cur), a1.s.raws_sorted(t, cur))

def a1.s.set_ok.go(o: R.Asn1SetOrder, xs: List<&2, A.Asn1Tlv>) -> Bool:
  match o:
    case R.Asn1SetOfOrder{}:
      a1.s.raws_sorted(xs, Nil{})
    case _:
      True{}

def a1.s.set_ok(+set: Bool, +r: R.Asn1Rules, xs: List<&2, A.Asn1Tlv>) -> Bool:
  match set:
    case True{}:
      a1.s.set_ok.go(R.Asn1Rules.set_order(r), xs)
    case False{}:
      True{}

def a1.s.pick.go(hit: Bool, s: Asn1Schema, i: Nat, r: Maybe<&2, A1Pick>) -> Maybe<&2, A1Pick>:
  match hit:
    case True{}:
      Some{A1Pick{i, s}}
    case False{}:
      r

def a1.s.pick(alts: List<&2, Asn1Schema>, +t: T.Asn1Tag, +i: Nat) -> Maybe<&2, A1Pick>:
  match alts:
    case Nil{}:
      None{}
    case Con{+s, rest}:
      a1.s.pick.go(Asn1S.admits(s, t), s, i, a1.s.pick(rest, t, Nat.add(i, 1n)))

def a1.s.choice_work(p: Maybe<&2, A1Pick>, e: A.Asn1Tlv) -> A1Work:
  match p:
    case None{}:
      A1WNone{}
    case Some{A1Pick{i, s}}:
      A1WOne{s, e}

def a1.s.choice_res(p: Maybe<&2, A1Pick>, r: Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>) -> Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>:
  match p:
    case None{}:
      Fail{E.Asn1SchemaMismatch{}}
    case Some{A1Pick{i, s}}:
      a1.s.wrap_choice(i, r)

def a1.s.one_work(r: Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>, +inner: Asn1Schema) -> A1Work:
  match r:
    case Done{[x]}:
      A1WOne{inner, x}
    case _:
      A1WNone{}

def a1.s.one_res(r: Result<&2, &2, E.Asn1Error, List<&2, A.Asn1Tlv>>, e: A.Asn1Tlv, m: Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>) -> Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>:
  match r:
    case Fail{x}:
      Fail{x}
    case Done{[x]}:
      a1.s.wrap_explicit(e, m)
    case Done{xs}:
      Fail{E.Asn1SchemaMismatch{}}

# the matcher (fuel bounds the steps)
def a1.s.m(fuel: Nat, +r: R.Asn1Rules, w: A1Work) -> Result<&2, &2, E.Asn1Error, List<&2, Asn1Match>>:
  match fuel:
    case 0n:
      Fail{E.Asn1Exhausted{}}
    case 1n+ +f:
      match w:
        case A1WNone{}:
          Done{Nil{}}
        case A1WSlots{Nil{}, True{}}:
          Fail{E.Asn1SchemaExtra{}}
        case A1WSlots{Nil{}, False{}}:
          Done{Nil{}}
        case A1WSlots{Con{A1Slot{+s, +me}, rest}, ex}:
          a1.s.cons(a1.s.slot_res(R.Asn1Rules.values(r), me, s, a1.s.m(f, r, a1.s.slot_work(s, me))), a1.s.m(f, r, A1WSlots{rest, ex}))
        case A1WOne{Asn1SAny{}, e}:
          Done{[Asn1MElem{e}]}
        case A1WOne{Asn1SElem{+t}, +e}:
          a1.s.gate(a1.s.tag_ok(t, False{}, e), Done{[Asn1MElem{e}]})
        case A1WOne{Asn1SSeq{+t, +fs}, +e}:
          +items = A.Asn1.items(r, e)
          a1.s.gate(a1.s.tag_ok(t, True{}, e), a1.s.items_err(items, a1.s.wrap_seq(e, a1.s.m(f, r, a1.s.seq_work(fs, a1.s.items_or_nil(items))))))
        case A1WOne{Asn1SOf{+t, +item, +set}, +e}:
          +items = A.Asn1.items(r, e)
          +xs = a1.s.items_or_nil(items)
          a1.s.gate(Bool.and(a1.s.tag_ok(t, True{}, e), a1.s.set_ok(set, r, xs)), a1.s.items_err(items, a1.s.wrap_seq(e, a1.s.m(f, r, A1WSlots{a1.s.of_slots(xs, item), False{}}))))
        case A1WOne{Asn1SChoice{+alts}, +e}:
          +p = a1.s.pick(alts, a1.s.tlv_tag(e), 0n)
          a1.s.choice_res(p, a1.s.m(f, r, a1.s.choice_work(p, e)))
        case A1WOne{Asn1SExplicit{+n, +inner}, +e}:
          +items = A.Asn1.items(r, e)
          a1.s.gate(a1.s.tag_ok(T.Asn1Tag.context(n), True{}, e), a1.s.one_res(items, e, a1.s.m(f, r, a1.s.one_work(items, inner))))
        case A1WOne{Asn1SOpt{inner}, e}:
          a1.s.m(f, r, A1WOne{inner, e})
        case A1WOne{Asn1SDefault{inner, v}, e}:
          a1.s.m(f, r, A1WOne{inner, e})

# an element (with its octets) matched against a schema
def Asn1.match_tlv(+r: R.Asn1Rules, s: Asn1Schema, +x: A.Asn1Tlv) -> Result<&2, &2, E.Asn1Error, Asn1Match>:
  match x:
    case A.Asn1Tlv{n, +raw}:
      a1.s.ok1(a1.s.m(Nat.mul(Nat.add(B.Octets.len(raw), 1n), 64n), r, A1WOne{s, A.Asn1Tlv{n, raw}}))

def a1.s.top2(ok: Bool, +r: R.Asn1Rules, s: Asn1Schema, x: A.Asn1Tlv) -> Result<&2, &2, E.Asn1Error, Asn1Match>:
  match ok:
    case True{}:
      Asn1.match_tlv(r, s, x)
    case False{}:
      Fail{E.Asn1Trailing{}}

def a1.s.top(+r: R.Asn1Rules, s: Asn1Schema, res: Result<&2, &2, E.Asn1Error, A.Asn1TlvRead>) -> Result<&2, &2, E.Asn1Error, Asn1Match>:
  match res:
    case Fail{e}:
      Fail{e}
    case Done{A.Asn1TlvRead{x, rest}}:
      a1.s.top2(Bool.or(R.Asn1Rules.trailing(r), Nat.is_eq(B.Octets.len(rest), 0n)), r, s, x)

# the element in b matched against a schema (octets after it are refused
# unless r.trailing)
def Asn1.match(+r: R.Asn1Rules, s: Asn1Schema, b: B.Octets) -> Result<&2, &2, E.Asn1Error, Asn1Match>:
  a1.s.top(r, s, A.Asn1.read(r, b))

# Reading matches

def Asn1Match.items(m: Asn1Match) -> List<&2, Asn1Match>:
  match m:
    case Asn1MSeq{e, ms}:
      ms
    case _:
      Nil{}

def a1.s.nth(ms: List<&2, Asn1Match>, i: Nat) -> Asn1Match:
  match ms i:
    case Nil{} _:
      Asn1MAbsent{}
    case Con{m, t} 0n:
      m
    case Con{m, t} 1n+j:
      a1.s.nth(t, j)

# the i-th field's match of a sequence's match (absent past the end)
def Asn1Match.at(m: Asn1Match, i: Nat) -> Asn1Match:
  a1.s.nth(Asn1Match.items(m), i)

# the match inside an EXPLICIT tag or a CHOICE
def Asn1Match.inner(m: Asn1Match) -> Asn1Match:
  match m:
    case Asn1MExplicit{e, x}:
      x
    case Asn1MChoice{i, x}:
      x
    case m2:
      m2

def Asn1Match.present(m: Asn1Match) -> Bool:
  match m:
    case Asn1MAbsent{}:
      False{}
    case Asn1MDefault{v}:
      False{}
    case _:
      True{}

# the element and octets matched (None for an absent field)
def Asn1Match.tlv(m: Asn1Match) -> Maybe<&2, A.Asn1Tlv>:
  match m:
    case Asn1MElem{e}:
      Some{e}
    case Asn1MSeq{e, ms}:
      Some{e}
    case Asn1MExplicit{e, x}:
      Some{e}
    case Asn1MChoice{i, x}:
      Asn1Match.tlv(x)
    case Asn1MAbsent{}:
      None{}
    case Asn1MDefault{v}:
      None{}

# the element matched (a DEFAULT's value when absent)
def Asn1Match.node(m: Asn1Match) -> Maybe<&2, N.Asn1Node>:
  match m:
    case Asn1MDefault{v}:
      Some{v}
    case m2:
      Maybe.map(&2, A.Asn1Tlv, N.Asn1Node, x => A.Asn1Tlv.node(x), Asn1Match.tlv(m2))

# the octets matched (empty for an absent field)
def a1.s.raw_of(t: Maybe<&2, A.Asn1Tlv>) -> B.Octets:
  match t:
    case None{}:
      B.Octets.empty()
    case Some{x}:
      A.Asn1Tlv.raw(x)

def Asn1Match.raw(m: Asn1Match) -> B.Octets:
  a1.s.raw_of(Asn1Match.tlv(m))
