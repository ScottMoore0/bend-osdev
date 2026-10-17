# bend-osdev-fdt, tree.bend: the devicetree as a tree of nodes and
# properties, and its correspondence with the structure block's tokens and
# the strings block (Devicetree Specification v0.4, sections 5.4 and 5.5).
#
# A node is FDT_BEGIN_NODE, its properties, its children, FDT_END_NODE.
# Property names live in the strings block, as NUL-terminated strings; a
# property token holds the offset of its name there.
#
# FdtNode.to_tokens writes a tree as tokens and a strings block; FdtNode.
# of_tokens builds the tree back from tokens (as FdtToken.decode_all reads
# them) and the strings block, checking the nesting.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./layout.bend as L
import ./structure.bend as S

type FdtProp is Data:
  FdtProp{name: B.Octets, value: B.Octets}

type FdtNode is Data:
  FdtNode{name: B.Octets, props: List<&2, FdtProp>, children: List<&2, FdtNode>}

# The rules a tree builder applies (FdtTreeRules.default(): both true)
#   nop_ok: FDT_NOP tokens are skipped (the specification says a reader shall
#     ignore them); false refuses them with FdtNopRefused
#   props_first: a property after a child node is refused with
#     FdtPropAfterNode (the specification requires properties first)
type FdtTreeRules is Data:
  FdtTreeRules{nop_ok: Bool, props_first: Bool}

def FdtTreeRules.default() -> FdtTreeRules:
  FdtTreeRules{True{}, True{}}

# How a writer lays out the strings block
#   FdtStringsSimple: each property's name in turn, repeats included (the
#     default; the round-trip laws are proved for it)
#   FdtStringsDedup: each name once, and a name that is the tail of an
#     earlier one shares its bytes, as dtc writes it
type FdtStrings is Data:
  FdtStringsSimple{}
  FdtStringsDedup{}

def FdtStrings.default() -> FdtStrings:
  FdtStringsSimple{}

# a structure block's tokens and its strings block
type FdtFlat is Data:
  FdtFlat{tokens: List<&2, S.FdtToken>, strings: B.Octets}

# Writing, with the simple strings block

# the strings of a list of properties
def prop.strs(ps: List<&2, FdtProp>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      match p:
        case FdtProp{k, v}:
          B.append(B.Octets.to_list(k), Con{0, prop.strs(t)})

# their tokens, the first name at offset off
def prop.toks(ps: List<&2, FdtProp>, off: Nat) -> List<&2, S.FdtToken>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      match p:
        case FdtProp{k, v}:
          +o = off
          Con{S.FdtTokProp{L.fdt.u32n(o), v}, prop.toks(t, Nat.add(o, B.len(B.append(B.Octets.to_list(k), [0]))))}

# the strings of a list of nodes (a forest)
def flat.strs(ns: List<&2, FdtNode>) -> List<&2, U32>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      match n:
        case FdtNode{nm, ps, cs}:
          B.append(prop.strs(ps), B.append(flat.strs(cs), flat.strs(t)))

# the tokens of a forest, its first name at offset off
def flat.toks(ns: List<&2, FdtNode>, +off: Nat) -> List<&2, S.FdtToken>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      match n:
        case FdtNode{nm, +ps, +cs}:
          +o1 = Nat.add(off, B.len(prop.strs(ps)))
          +o2 = Nat.add(o1, B.len(flat.strs(cs)))
          Con{S.FdtTokBegin{nm}, List.append(&2, S.FdtToken, prop.toks(ps, off), List.append(&2, S.FdtToken, flat.toks(cs, o1), Con{S.FdtTokEnd{}, flat.toks(t, o2)}))}

# The same two writers, for trees of any size (PROOF.bend: strs_fast,
# ftoks_fast). prop.strs, flat.strs, prop.toks and flat.toks above are the
# reference forms the proofs compute through; they recurse once per byte
# or token. These push onto an accumulator (reversed) and recurse into a
# node's children only, so their depth is the tree's depth.

def pstrs.go(ps: List<&2, FdtProp>, acc: List<&2, U32>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      acc
    case Con{p, t}:
      match p:
        case FdtProp{k, v}:
          pstrs.go(t, Con{0, List.reverse.go(&2, U32, B.Octets.to_list(k), acc)})

def pstrs.fast(ps: List<&2, FdtProp>) -> List<&2, U32>:
  List.reverse(&2, U32, pstrs.go(ps, Nil{}))

def strs.go(ns: List<&2, FdtNode>, acc: List<&2, U32>) -> List<&2, U32>:
  match ns:
    case Nil{}:
      acc
    case Con{n, t}:
      match n:
        case FdtNode{nm, ps, cs}:
          strs.go(t, strs.go(cs, pstrs.go(ps, acc)))

def flat.strs.fast(ns: List<&2, FdtNode>) -> List<&2, U32>:
  List.reverse(&2, U32, strs.go(ns, Nil{}))

def ptoks.go(ps: List<&2, FdtProp>, off: Nat, acc: List<&2, S.FdtToken>) -> List<&2, S.FdtToken>:
  match ps:
    case Nil{}:
      acc
    case Con{p, t}:
      match p:
        case FdtProp{k, v}:
          +o = off
          ptoks.go(t, Nat.add(o, B.len(B.append(B.Octets.to_list(k), [0]))), Con{S.FdtTokProp{L.fdt.u32n.fast(o), v}, acc})

def ftoks.go(ns: List<&2, FdtNode>, +off: Nat, acc: List<&2, S.FdtToken>) -> List<&2, S.FdtToken>:
  match ns:
    case Nil{}:
      acc
    case Con{n, t}:
      match n:
        case FdtNode{nm, +ps, +cs}:
          +o1 = Nat.add(off, B.len.fast(pstrs.fast(ps)))
          ftoks.go(t, Nat.add(o1, B.len.fast(flat.strs.fast(cs))), Con{S.FdtTokEnd{}, ftoks.go(cs, o1, ptoks.go(ps, off, Con{S.FdtTokBegin{nm}, acc}))})

def flat.toks.fast(ns: List<&2, FdtNode>, off: Nat) -> List<&2, S.FdtToken>:
  List.reverse(&2, S.FdtToken, ftoks.go(ns, off, Nil{}))

# Writing, with each name's bytes once (as dtc writes it): a name whose
# bytes and NUL already occur in the strings block, also as the tail of a
# longer name, takes that offset; otherwise it is added at the end

# the strings block so far, and its length
type FdtStrTab is Data:
  FdtStrTab{bytes: List<&2, U32>, size: Nat}

# xs is a prefix of ys (ok: the bytes so far agree); tail-recursive
def dedup.prefix(xs: List<&2, U32>, ys: List<&2, U32>, ok: Bool) -> Bool:
  match xs ys:
    case Nil{} _:
      ok
    case Con{a, s} Con{b, t}:
      match ok:
        case True{}:
          dedup.prefix(s, t, U32.is_eq(a, b))
        case False{}:
          False{}
    case Con{a, s} Nil{}:
      False{}

def dedup.hit(hit: Bool, o: Nat) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{o}
    case False{}:
      None{}

# the first offset, from i, at which ys holds k (found: the offset, once
# found); tail-recursive, and it stops at the first hit
def dedup.find(ys: List<&2, U32>, +k: List<&2, U32>, +i: Nat, found: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match ys:
    case Nil{}:
      found
    case Con{+h, +t}:
      match found:
        case Some{o}:
          Some{o}
        case None{}:
          dedup.find(t, k, 1n+i, dedup.hit(dedup.prefix(k, Con{h, t}, True{}), i))

# a name's offset, and the block after it is added if it is new
type FdtStrAt is Data:
  FdtStrAt{off: Nat, tab: FdtStrTab}

def dedup.add(m: Maybe<&2, Nat>, +k: List<&2, U32>, bytes: List<&2, U32>, +size: Nat) -> FdtStrAt:
  match m:
    case Some{o}:
      FdtStrAt{o, FdtStrTab{bytes, size}}
    case None{}:
      FdtStrAt{size, FdtStrTab{B.append.fast(bytes, k), Nat.add(size, B.len(k))}}

# k with its NUL
def dedup.intern.nul(tab: FdtStrTab, +k: List<&2, U32>) -> FdtStrAt:
  match tab:
    case FdtStrTab{+bytes, size}:
      dedup.add(dedup.find(bytes, k, 0n, None{}), k, bytes, size)

def dedup.intern(tab: FdtStrTab, k: List<&2, U32>) -> FdtStrAt:
  dedup.intern.nul(tab, B.append(k, [0]))

type FdtFlatD is Data:
  FdtFlatD{toks: List<&2, S.FdtToken>, tab: FdtStrTab}

# the tokens so far are kept reversed
def dedup.prop.at(a: FdtStrAt, v: B.Octets, toks: List<&2, S.FdtToken>) -> FdtFlatD:
  match a:
    case FdtStrAt{o, tab}:
      FdtFlatD{Con{S.FdtTokProp{L.fdt.u32n(o), v}, toks}, tab}

def dedup.prop(acc: FdtFlatD, p: FdtProp) -> FdtFlatD:
  match acc:
    case FdtFlatD{toks, tab}:
      match p:
        case FdtProp{k, v}:
          dedup.prop.at(dedup.intern(tab, B.Octets.to_list(k)), v, toks)

def dedup.props(ps: List<&2, FdtProp>, acc: FdtFlatD) -> FdtFlatD:
  match ps:
    case Nil{}:
      acc
    case Con{p, t}:
      dedup.props(t, dedup.prop(acc, p))

def dedup.push(acc: FdtFlatD, t: S.FdtToken) -> FdtFlatD:
  match acc:
    case FdtFlatD{toks, tab}:
      FdtFlatD{Con{t, toks}, tab}

def dedup.forest(ns: List<&2, FdtNode>, acc: FdtFlatD) -> FdtFlatD:
  match ns:
    case Nil{}:
      acc
    case Con{n, t}:
      match n:
        case FdtNode{nm, ps, cs}:
          dedup.forest(t, dedup.push(dedup.forest(cs, dedup.props(ps, dedup.push(acc, S.FdtTokBegin{nm}))), S.FdtTokEnd{}))

# the tokens of a tree (in order) and its string table
def dedup.fin(d: FdtFlatD) -> FdtFlatD:
  match d:
    case FdtFlatD{toks, tab}:
      FdtFlatD{List.reverse(&2, S.FdtToken, toks), tab}

def dedup.run(root: FdtNode) -> FdtFlatD:
  dedup.fin(dedup.forest([root], FdtFlatD{Nil{}, FdtStrTab{Nil{}, 0n}}))

def dedup.flat(r: FdtFlatD) -> FdtFlat:
  match r:
    case FdtFlatD{ts, tab}:
      match tab:
        case FdtStrTab{bytes, size}:
          FdtFlat{ts, B.Octets.of_list(bytes)}

# Public writers

# the tokens of a tree and its strings block, laid out as chosen
def FdtNode.to_tokens_with(how: FdtStrings, +root: FdtNode) -> FdtFlat:
  match how:
    case FdtStringsSimple{}:
      FdtFlat{flat.toks.fast([root], 0n), B.Octets.of_list(flat.strs.fast([root]))}
    case FdtStringsDedup{}:
      dedup.flat(dedup.run(root))

def FdtNode.to_tokens(+root: FdtNode) -> FdtFlat:
  FdtNode.to_tokens_with(FdtStrings.default(), root)

# Reading: a state machine over the tokens, with a stack of open nodes

# an open node: its name, its properties and children so far (reversed)
type FdtFrame is Data:
  FdtFrame{name: B.Octets, props: List<&2, FdtProp>, kids: List<&2, FdtNode>}

type FdtTb is Data:
  TbStart{}
  TbOpen{stack: List<&2, FdtFrame>}
  TbDone{root: FdtNode}
  TbFail{error: E.FdtError}

def tb.node(f: FdtFrame) -> FdtNode:
  match f:
    case FdtFrame{nm, ps, ks}:
      FdtNode{nm, List.reverse(&2, FdtProp, ps), List.reverse(&2, FdtNode, ks)}

def tb.begin(st: FdtTb, nm: B.Octets) -> FdtTb:
  match st:
    case TbStart{}:
      TbOpen{[FdtFrame{nm, Nil{}, Nil{}}]}
    case TbOpen{s}:
      TbOpen{Con{FdtFrame{nm, Nil{}, Nil{}}, s}}
    case TbDone{r}:
      TbFail{E.FdtUnbalanced{}}
    case TbFail{e}:
      TbFail{e}

def tb.end.pop(s: List<&2, FdtFrame>) -> FdtTb:
  match s:
    case Nil{}:
      TbFail{E.FdtUnbalanced{}}
    case Con{f, rest}:
      match rest:
        case Nil{}:
          TbDone{tb.node(f)}
        case Con{g, rest2}:
          match g:
            case FdtFrame{gn, gp, gk}:
              TbOpen{Con{FdtFrame{gn, gp, Con{tb.node(f), gk}}, rest2}}

def tb.end(st: FdtTb) -> FdtTb:
  match st:
    case TbOpen{s}:
      tb.end.pop(s)
    case TbStart{}:
      TbFail{E.FdtUnbalanced{}}
    case TbDone{r}:
      TbFail{E.FdtUnbalanced{}}
    case TbFail{e}:
      TbFail{e}

def tb.prop.add(late: Bool, nm: B.Octets, ps: List<&2, FdtProp>, ks: List<&2, FdtNode>, k: B.Octets, v: B.Octets, s: List<&2, FdtFrame>) -> FdtTb:
  match late:
    case True{}:
      TbFail{E.FdtPropAfterNode{}}
    case False{}:
      TbOpen{Con{FdtFrame{nm, Con{FdtProp{k, v}, ps}, ks}, s}}

def tb.prop.named(f: FdtFrame, m: Maybe<&2, L.FdtCut>, pf: Bool, v: B.Octets, s: List<&2, FdtFrame>) -> FdtTb:
  match f:
    case FdtFrame{nm, ps, +ks}:
      match m:
        case None{}:
          TbFail{E.FdtBadNameOff{}}
        case Some{c}:
          match c:
            case L.FdtCut{k, rest}:
              tb.prop.add(Bool.and(Bool.not(List.is_empty(&2, FdtNode, ks)), pf), nm, ps, ks, B.Octets.of_list(k), v, s)

# the name at offset off of the strings block
def tb.name_at(strs: List<&2, U32>, off: Nat) -> Maybe<&2, L.FdtCut>:
  L.fdt.cstr(B.drop(off, strs))

def tb.prop.open(s: List<&2, FdtFrame>, pf: Bool, strs: List<&2, U32>, off: U32, v: B.Octets) -> FdtTb:
  match s:
    case Nil{}:
      TbFail{E.FdtUnbalanced{}}
    case Con{f, rest}:
      tb.prop.named(f, tb.name_at(strs, U32.to_nat(off)), pf, v, rest)

def tb.prop(st: FdtTb, pf: Bool, strs: List<&2, U32>, off: U32, v: B.Octets) -> FdtTb:
  match st:
    case TbOpen{s}:
      tb.prop.open(s, pf, strs, off, v)
    case TbStart{}:
      TbFail{E.FdtUnbalanced{}}
    case TbDone{r}:
      TbFail{E.FdtUnbalanced{}}
    case TbFail{e}:
      TbFail{e}

def tb.nop(ok: Bool, st: FdtTb) -> FdtTb:
  match ok:
    case True{}:
      st
    case False{}:
      match st:
        case TbFail{e}:
          TbFail{e}
        case TbStart{}:
          TbFail{E.FdtNopRefused{}}
        case TbOpen{s}:
          TbFail{E.FdtNopRefused{}}
        case TbDone{r}:
          TbFail{E.FdtNopRefused{}}

def tb.step(rules: FdtTreeRules, strs: List<&2, U32>, st: FdtTb, t: S.FdtToken) -> FdtTb:
  match rules:
    case FdtTreeRules{nop_ok, props_first}:
      match t:
        case S.FdtTokBegin{nm}:
          tb.begin(st, nm)
        case S.FdtTokEnd{}:
          tb.end(st)
        case S.FdtTokProp{off, v}:
          tb.prop(st, props_first, strs, off, v)
        case S.FdtTokNop{}:
          tb.nop(nop_ok, st)

def tb.go(ts: List<&2, S.FdtToken>, +rules: FdtTreeRules, +strs: List<&2, U32>, st: FdtTb) -> FdtTb:
  match ts:
    case Nil{}:
      st
    case Con{t, r}:
      tb.go(r, rules, strs, tb.step(rules, strs, st, t))

def tb.finish(st: FdtTb) -> Result<&2, &2, E.FdtError, FdtNode>:
  match st:
    case TbDone{r}:
      Done{r}
    case TbStart{}:
      Fail{E.FdtNoRoot{}}
    case TbOpen{s}:
      Fail{E.FdtUnbalanced{}}
    case TbFail{e}:
      Fail{e}

def tb.run(ts: List<&2, S.FdtToken>, rules: FdtTreeRules, strs: List<&2, U32>) -> Result<&2, &2, E.FdtError, FdtNode>:
  tb.finish(tb.go(ts, rules, strs, TbStart{}))

# the tree the tokens describe, with property names from the strings block
def FdtNode.of_tokens(rules: FdtTreeRules, ts: List<&2, S.FdtToken>, strings: B.Octets) -> Result<&2, &2, E.FdtError, FdtNode>:
  tb.run(ts, rules, B.Octets.to_list(strings))

def FdtNode.of_flat(rules: FdtTreeRules, f: FdtFlat) -> Result<&2, &2, E.FdtError, FdtNode>:
  match f:
    case FdtFlat{ts, strings}:
      FdtNode.of_tokens(rules, ts, strings)

# The trees a blob can hold: names without NULs (node names and property
# names are NUL-terminated in the blob)

def prop.names_ok(ps: List<&2, FdtProp>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{p, t}:
      match p:
        case FdtProp{k, v}:
          Bool.and(L.fdt.nonul(B.Octets.to_list(k)), prop.names_ok(t))

def flat.names_ok(ns: List<&2, FdtNode>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{n, t}:
      match n:
        case FdtNode{nm, ps, cs}:
          Bool.and(L.fdt.nonul(B.Octets.to_list(nm)), Bool.and(prop.names_ok(ps), Bool.and(flat.names_ok(cs), flat.names_ok(t))))

# every property value is shorter than 2^32 bytes
def prop.values_ok(ps: List<&2, FdtProp>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{p, t}:
      match p:
        case FdtProp{k, v}:
          Bool.and(L.fdt.fits(B.len(B.Octets.to_list(v))), prop.values_ok(t))

def flat.values_ok(ns: List<&2, FdtNode>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{n, t}:
      match n:
        case FdtNode{nm, ps, cs}:
          Bool.and(prop.values_ok(ps), Bool.and(flat.values_ok(cs), flat.values_ok(t)))

# The same checks as folds, for trees of any size: they recurse into a
# node's children only (PROOF.bend: names_fast, wf_fast, flat_ok_fast)

def pnames.go(ps: List<&2, FdtProp>, ok: Bool) -> Bool:
  match ps:
    case Nil{}:
      ok
    case Con{p, t}:
      match p:
        case FdtProp{k, v}:
          pnames.go(t, Bool.and(ok, L.fdt.nonul(B.Octets.to_list(k))))

def names.go(ns: List<&2, FdtNode>, ok: Bool) -> Bool:
  match ns:
    case Nil{}:
      ok
    case Con{n, t}:
      match n:
        case FdtNode{nm, ps, cs}:
          names.go(t, names.go(cs, pnames.go(ps, Bool.and(ok, L.fdt.nonul(B.Octets.to_list(nm))))))

def pvalues.go(ps: List<&2, FdtProp>, ok: Bool) -> Bool:
  match ps:
    case Nil{}:
      ok
    case Con{p, t}:
      match p:
        case FdtProp{k, v}:
          pvalues.go(t, Bool.and(ok, L.fdt.fits.fast(B.Octets.len(v))))

def values.go(ns: List<&2, FdtNode>, ok: Bool) -> Bool:
  match ns:
    case Nil{}:
      ok
    case Con{n, t}:
      match n:
        case FdtNode{nm, ps, cs}:
          values.go(t, values.go(cs, pvalues.go(ps, ok)))

# the reference forms the proofs use
def names_ok.ref(root: FdtNode) -> Bool:
  flat.names_ok([root])

def wf.ref(+root: FdtNode) -> Bool:
  Bool.and(names_ok.ref(root), flat.values_ok([root]))

def flat_ok.ref(+root: FdtNode) -> Bool:
  Bool.and(names_ok.ref(root), L.fdt.fits(B.len(flat.strs([root]))))

# every name in the tree is free of NULs
def FdtNode.names_ok(root: FdtNode) -> Bool:
  names.go([root], True{})

# a tree whose tokens its encoding can carry: names without NULs, values
# shorter than 2^32 bytes
def FdtNode.wf(+root: FdtNode) -> Bool:
  Bool.and(FdtNode.names_ok(root), values.go([root], True{}))

# a tree FdtNode.to_tokens can write so that FdtNode.of_flat reads it back:
# names without NULs, and a strings block shorter than 4 GiB
def FdtNode.flat_ok(+root: FdtNode) -> Bool:
  Bool.and(FdtNode.names_ok(root), L.fdt.fits.fast(B.len.fast(flat.strs.fast([root]))))

# Text: one line per tree, for tests and debugging:
#   name{prop=hex;...;child{...}...}
def dump.props(ps: List<&2, FdtProp>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{p, t}:
      match p:
        case FdtProp{k, v}:
          B.Octets.to_string(k) ++ "=" ++ B.Octets.hex(v) ++ ";" ++ dump.props(t)

def dump.forest(ns: List<&2, FdtNode>) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{n, t}:
      match n:
        case FdtNode{nm, ps, cs}:
          B.Octets.to_string(nm) ++ "{" ++ dump.props(ps) ++ dump.forest(cs) ++ "}" ++ dump.forest(t)

def FdtNode.dump(n: FdtNode) -> String:
  dump.forest([n])
