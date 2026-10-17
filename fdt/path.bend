# bend-osdev-fdt, path.bend: looking things up in a devicetree (Devicetree
# Specification v0.4, sections 2.2.1, 2.2.3, 2.3 and 3.3): a property by
# name, a child by name, a node by path ("/cpus/cpu@0") or alias, a node by
# phandle, and a node's reg property through its parent's #address-cells
# and #size-cells.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tree.bend as T
import ./props.bend as P

def lk.or(a: Maybe<&2, T.FdtNode>, b: Maybe<&2, T.FdtNode>) -> Maybe<&2, T.FdtNode>:
  match a:
    case Some{n}:
      Some{n}
    case None{}:
      b

# Properties

def lk.prop.pick(hit: Bool, v: B.Octets, rest: Maybe<&2, B.Octets>) -> Maybe<&2, B.Octets>:
  match hit:
    case True{}:
      Some{v}
    case False{}:
      rest

def lk.prop(ps: List<&2, T.FdtProp>, +k: B.Octets) -> Maybe<&2, B.Octets>:
  match ps:
    case Nil{}:
      None{}
    case Con{p, t}:
      match p:
        case T.FdtProp{nm, v}:
          lk.prop.pick(B.Octets.is_eq(nm, k), v, lk.prop(t, k))

# the value of the node's first property named k
def FdtNode.prop(n: T.FdtNode, k: B.Octets) -> Maybe<&2, B.Octets>:
  match n:
    case T.FdtNode{nm, ps, cs}:
      lk.prop(ps, k)

# the same, the name given as text
def FdtNode.get(n: T.FdtNode, k: String) -> Maybe<&2, B.Octets>:
  FdtNode.prop(n, B.Octets.of_string(k))

# Children

def lk.base.pick(at: Bool, h: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match at:
    case True{}:
      Nil{}
    case False{}:
      Con{h, rest}

# a node name without its unit address: the bytes before its '@'
def lk.base(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      lk.base.pick(U32.is_eq(h, 64), h, lk.base(t))

def lk.has_at(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(U32.is_eq(h, 64), lk.has_at(t))

def lk.child.pick(hit: Bool, n: T.FdtNode, rest: Maybe<&2, T.FdtNode>) -> Maybe<&2, T.FdtNode>:
  match hit:
    case True{}:
      Some{n}
    case False{}:
      rest

def lk.child.exact(ns: List<&2, T.FdtNode>, +k: B.Octets) -> Maybe<&2, T.FdtNode>:
  match ns:
    case Nil{}:
      None{}
    case Con{n, t}:
      match n:
        case T.FdtNode{+nm, ps, cs}:
          lk.child.pick(B.Octets.is_eq(nm, k), T.FdtNode{nm, ps, cs}, lk.child.exact(t, k))

def lk.child.base(ns: List<&2, T.FdtNode>, +k: B.Octets) -> Maybe<&2, T.FdtNode>:
  match ns:
    case Nil{}:
      None{}
    case Con{n, t}:
      match n:
        case T.FdtNode{+nm, ps, cs}:
          lk.child.pick(B.Octets.is_eq(B.Octets.of_list(lk.base(B.Octets.to_list(nm))), k), T.FdtNode{nm, ps, cs}, lk.child.base(t, k))

def lk.child.base_if(has_at: Bool, ns: List<&2, T.FdtNode>, k: B.Octets) -> Maybe<&2, T.FdtNode>:
  match has_at:
    case True{}:
      None{}
    case False{}:
      lk.child.base(ns, k)

# the child named k; or, if k has no unit address ('@'), the first child
# whose name without its unit address is k
def FdtNode.child(n: T.FdtNode, +k: B.Octets) -> Maybe<&2, T.FdtNode>:
  match n:
    case T.FdtNode{nm, ps, +cs}:
      lk.or(lk.child.exact(cs, k), lk.child.base_if(lk.has_at(B.Octets.to_list(k)), cs, k))

# Paths

# the component being read (reversed), and the components so far (reversed)
type FdtPathAcc is Data:
  FdtPathAcc{cur: List<&2, U32>, comps: List<&2, List<&2, U32>>}

# an empty component (from "//" or a trailing "/") is skipped
def lk.push(cur: List<&2, U32>, comps: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match cur:
    case Nil{}:
      comps
    case Con{h, t}:
      Con{List.reverse(&2, U32, Con{h, t}), comps}

def lk.split.byte(slash: Bool, h: U32, cur: List<&2, U32>, comps: List<&2, List<&2, U32>>) -> FdtPathAcc:
  match slash:
    case True{}:
      FdtPathAcc{Nil{}, lk.push(cur, comps)}
    case False{}:
      FdtPathAcc{Con{h, cur}, comps}

def lk.split.go(xs: List<&2, U32>, st: FdtPathAcc) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      match st:
        case FdtPathAcc{cur, comps}:
          List.reverse(&2, List<&2, U32>, lk.push(cur, comps))
    case Con{+h, t}:
      match st:
        case FdtPathAcc{cur, comps}:
          lk.split.go(t, lk.split.byte(U32.is_eq(h, 47), h, cur, comps))

# the components of a path, between its '/'s
def lk.components(xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  lk.split.go(xs, FdtPathAcc{Nil{}, Nil{}})

def lk.walk(comps: List<&2, List<&2, U32>>, m: Maybe<&2, T.FdtNode>) -> Maybe<&2, T.FdtNode>:
  match comps m:
    case Nil{} Some{n}:
      Some{n}
    case Con{c, t} Some{n}:
      lk.walk(t, FdtNode.child(n, B.Octets.of_list(c)))
    case _ None{}:
      None{}

def lk.prop_of(m: Maybe<&2, T.FdtNode>, k: B.Octets) -> Maybe<&2, B.Octets>:
  match m:
    case Some{n}:
      FdtNode.prop(n, k)
    case None{}:
      None{}

def lk.alias.str(r: Result<&2, &2, E.FdtError, B.Octets>, rest: List<&2, List<&2, U32>>, root: T.FdtNode) -> Maybe<&2, T.FdtNode>:
  match r:
    case Done{s}:
      lk.walk(List.append(&2, List<&2, U32>, lk.components(B.Octets.to_list(s)), rest), Some{root})
    case Fail{e}:
      None{}

def lk.alias.val(m: Maybe<&2, B.Octets>, rest: List<&2, List<&2, U32>>, root: T.FdtNode) -> Maybe<&2, T.FdtNode>:
  match m:
    case Some{v}:
      lk.alias.str(P.FdtProp.string(v), rest, root)
    case None{}:
      None{}

# a path whose first component is an alias: a property of /aliases whose
# value is the path it stands for
def lk.alias(+root: T.FdtNode, comps: List<&2, List<&2, U32>>) -> Maybe<&2, T.FdtNode>:
  match comps:
    case Nil{}:
      None{}
    case Con{a, rest}:
      lk.alias.val(lk.prop_of(FdtNode.child(root, B.Octets.of_string("aliases")), B.Octets.of_list(a)), rest, root)

def lk.is_abs(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      U32.is_eq(h, 47)

def lk.find(abs: Bool, +root: T.FdtNode, comps: List<&2, List<&2, U32>>) -> Maybe<&2, T.FdtNode>:
  match abs:
    case True{}:
      lk.walk(comps, Some{root})
    case False{}:
      lk.alias(root, comps)

# the node at a path from the root ("/cpus/cpu@0"), or, for a path that does
# not start with '/', from the node its first component names in /aliases
def FdtNode.find(root: T.FdtNode, path: String) -> Maybe<&2, T.FdtNode>:
  +xs = B.of_string(path)
  lk.find(lk.is_abs(xs), root, lk.components(xs))

# Phandles

def lk.ph.res(r: Result<&2, &2, E.FdtError, U32>, ph: U32) -> Bool:
  match r:
    case Done{x}:
      U32.is_eq(x, ph)
    case Fail{e}:
      False{}

def lk.ph.is(m: Maybe<&2, B.Octets>, ph: U32) -> Bool:
  match m:
    case Some{v}:
      lk.ph.res(P.FdtProp.u32(v), ph)
    case None{}:
      False{}

# a phandle property ("phandle", or the older "linux,phandle") equal to ph
def lk.ph.match(+ps: List<&2, T.FdtProp>, +ph: U32) -> Bool:
  Bool.or(lk.ph.is(lk.prop(ps, B.Octets.of_string("phandle")), ph), lk.ph.is(lk.prop(ps, B.Octets.of_string("linux,phandle")), ph))

def lk.ph.pick(hit: Bool, n: T.FdtNode, inner: Maybe<&2, T.FdtNode>, rest: Maybe<&2, T.FdtNode>) -> Maybe<&2, T.FdtNode>:
  match hit:
    case True{}:
      Some{n}
    case False{}:
      lk.or(inner, rest)

def lk.ph.go(ns: List<&2, T.FdtNode>, +ph: U32) -> Maybe<&2, T.FdtNode>:
  match ns:
    case Nil{}:
      None{}
    case Con{n, t}:
      match n:
        case T.FdtNode{nm, +ps, +cs}:
          lk.ph.pick(lk.ph.match(ps, ph), T.FdtNode{nm, ps, cs}, lk.ph.go(cs, ph), lk.ph.go(t, ph))

# the first node, in depth-first order, whose phandle is ph
def FdtNode.find_phandle(root: T.FdtNode, ph: U32) -> Maybe<&2, T.FdtNode>:
  lk.ph.go([root], ph)

# reg, through the parent's cells

def lk.cells.r(r: Result<&2, &2, E.FdtError, U32>, dflt: Nat) -> Nat:
  match r:
    case Done{x}:
      U32.to_nat(x)
    case Fail{e}:
      dflt

def lk.cells(m: Maybe<&2, B.Octets>, dflt: Nat) -> Nat:
  match m:
    case Some{v}:
      lk.cells.r(P.FdtProp.u32(v), dflt)
    case None{}:
      dflt

# #address-cells, 2 when absent (or not a <u32>), as the specification says
def FdtNode.address_cells(n: T.FdtNode) -> Nat:
  lk.cells(FdtNode.get(n, "#address-cells"), 2n)

# #size-cells, 1 when absent (or not a <u32>)
def FdtNode.size_cells(n: T.FdtNode) -> Nat:
  lk.cells(FdtNode.get(n, "#size-cells"), 1n)

def lk.reg(m: Maybe<&2, B.Octets>, ac: Nat, sc: Nat) -> Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>:
  match m:
    case Some{v}:
      P.FdtProp.reg(ac, sc, v)
    case None{}:
      Done{Nil{}}

# a node's reg pairs, with its parent's cell counts (none if it has no reg)
def FdtNode.reg(+parent: T.FdtNode, node: T.FdtNode) -> Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>:
  lk.reg(FdtNode.get(node, "reg"), FdtNode.address_cells(parent), FdtNode.size_cells(parent))

# Shortcuts

def lk.prop_at(m: Maybe<&2, T.FdtNode>, k: B.Octets) -> Maybe<&2, B.Octets>:
  match m:
    case Some{n}:
      FdtNode.prop(n, k)
    case None{}:
      None{}

# the value of the property k of the node at a path
def FdtNode.find_prop(+root: T.FdtNode, path: String, k: String) -> Maybe<&2, B.Octets>:
  lk.prop_at(FdtNode.find(root, path), B.Octets.of_string(k))

# the parent of the node at the end of a walk, and that node
type FdtNodeIn is Data:
  FdtNodeIn{parent: T.FdtNode, node: T.FdtNode}

def lk.walk2.next(m: Maybe<&2, T.FdtNode>, parent: T.FdtNode) -> Maybe<&2, FdtNodeIn>:
  match m:
    case Some{n}:
      Some{FdtNodeIn{parent, n}}
    case None{}:
      None{}

def lk.walk2(comps: List<&2, List<&2, U32>>, m: Maybe<&2, FdtNodeIn>) -> Maybe<&2, FdtNodeIn>:
  match comps m:
    case Nil{} Some{pn}:
      Some{pn}
    case Con{c, t} Some{pn}:
      match pn:
        case FdtNodeIn{p, +n}:
          lk.walk2(t, lk.walk2.next(FdtNode.child(n, B.Octets.of_list(c)), n))
    case _ None{}:
      None{}

def lk.reg_in(m: Maybe<&2, FdtNodeIn>) -> Maybe<&2, Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>>:
  match m:
    case Some{pn}:
      match pn:
        case FdtNodeIn{p, n}:
          Some{FdtNode.reg(p, n)}
    case None{}:
      None{}

# the reg pairs of the node at an absolute path, with its parent's cell
# counts; None if there is no such node (the root's parent is itself)
def FdtNode.find_reg(+root: T.FdtNode, path: String) -> Maybe<&2, Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>>:
  lk.reg_in(lk.walk2(lk.components(B.of_string(path)), Some{FdtNodeIn{root, root}}))
