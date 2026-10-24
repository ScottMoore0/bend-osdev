# The lookups, for every tree: what FdtNode.find_phandle returns (the first
# node in depth-first order whose phandle is the value, none if there is
# none), what FdtNode.find returns for a path from the root and for a path
# through /aliases, which child FdtNode.child picks (an exact name first,
# then a name without its unit address), and the reg decoder: its pairs read
# back as of_reg writes them, with the cell counts a parent gives.
#
# The specification each law states is written below with the public
# interface only (FdtNode.get, FdtNode.prop, FdtProp.u32, FdtProp.string),
# in the plainest structural form: a law says the public def equals it.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./tree.bend as T
import ./props.bend as P
import ./path.bend as Pa

# Phandles

# the nodes of a forest in depth-first order: each node, then the nodes
# under it, then the nodes of the siblings after it
def fdtlaw.nodes(ns: List<&2, T.FdtNode>) -> List<&2, T.FdtNode>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      match n:
        case T.FdtNode{nm, ps, +cs}:
          Con{T.FdtNode{nm, ps, cs}, List.append(&2, T.FdtNode, fdtlaw.nodes(cs), fdtlaw.nodes(t))}

def fdtlaw.is_u32.r(r: Result<&2, &2, E.FdtError, U32>, ph: U32) -> Bool:
  match r:
    case Done{x}:
      U32.is_eq(x, ph)
    case Fail{e}:
      False{}

# a property value that is the <u32> ph
def fdtlaw.is_u32(m: Maybe<&2, B.Octets>, ph: U32) -> Bool:
  match m:
    case Some{v}:
      fdtlaw.is_u32.r(P.FdtProp.u32(v), ph)
    case None{}:
      False{}

# the node's "phandle" property, or its older "linux,phandle", is the
# <u32> ph (the first property of each name, as FdtNode.get reads it)
def fdtlaw.has_phandle(+n: T.FdtNode, +ph: U32) -> Bool:
  Bool.or(fdtlaw.is_u32(Pa.FdtNode.get(n, "phandle"), ph), fdtlaw.is_u32(Pa.FdtNode.get(n, "linux,phandle"), ph))

def fdtlaw.first.pick(hit: Bool, n: T.FdtNode, rest: Maybe<&2, T.FdtNode>) -> Maybe<&2, T.FdtNode>:
  match hit:
    case True{}:
      Some{n}
    case False{}:
      rest

# the first node of a list whose phandle is ph
def fdtlaw.first_phandle(ns: List<&2, T.FdtNode>, +ph: U32) -> Maybe<&2, T.FdtNode>:
  match ns:
    case Nil{}:
      None{}
    case Con{+n, t}:
      fdtlaw.first.pick(fdtlaw.has_phandle(n, ph), n, fdtlaw.first_phandle(t, ph))

# some node of a list has the phandle ph
def fdtlaw.any_phandle(ns: List<&2, T.FdtNode>, +ph: U32) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{+n, t}:
      Bool.or(fdtlaw.has_phandle(n, ph), fdtlaw.any_phandle(t, ph))

# the node found is the first node of the tree, in depth-first order (the
# root, then each child's subtree in turn), whose phandle is ph
law find_phandle_first:
  for +root: T.FdtNode
  for +ph: U32
  {Pa.FdtNode.find_phandle(root, ph) == fdtlaw.first_phandle(fdtlaw.nodes([root]), ph) : Maybe<&2, T.FdtNode>}

# no node of the tree has the phandle ph: none is found
law find_phandle_none:
  for +root: T.FdtNode
  for +ph: U32
  for +e: {fdtlaw.any_phandle(fdtlaw.nodes([root]), ph) == False{} : Bool}
  {Pa.FdtNode.find_phandle(root, ph) == None{} : Maybe<&2, T.FdtNode>}

# a node whose first property is its phandle is found by it
law find_phandle_head:
  for +nm: B.Octets
  for +ph: U32
  for +ps: List<&2, T.FdtProp>
  for +cs: List<&2, T.FdtNode>
  {Pa.FdtNode.find_phandle(T.FdtNode{nm, Con{T.FdtProp{B.Octets.of_string("phandle"), P.FdtProp.of_u32(ph)}, ps}, cs}, ph) == Some{T.FdtNode{nm, Con{T.FdtProp{B.Octets.of_string("phandle"), P.FdtProp.of_u32(ph)}, ps}, cs}} : Maybe<&2, T.FdtNode>}

# The hypothesis of find_phandle_none is satisfiable: a tree with no phandle
law find_phandle_none_example:
  {fdtlaw.any_phandle(fdtlaw.nodes([T.FdtNode{B.Octets.empty(), [], [T.FdtNode{B.Octets.of_string("a"), [], []}]}]), 1) == False{} : Bool}

# Children: an exact name first, then a name without its unit address

def fdtlaw.or(a: Maybe<&2, T.FdtNode>, b: Maybe<&2, T.FdtNode>) -> Maybe<&2, T.FdtNode>:
  match a:
    case Some{n}:
      Some{n}
    case None{}:
      b

# the first node of a list named k
def fdtlaw.named(ns: List<&2, T.FdtNode>, +k: B.Octets) -> Maybe<&2, T.FdtNode>:
  match ns:
    case Nil{}:
      None{}
    case Con{n, t}:
      match n:
        case T.FdtNode{+nm, ps, cs}:
          fdtlaw.first.pick(B.Octets.is_eq(nm, k), T.FdtNode{nm, ps, cs}, fdtlaw.named(t, k))

def fdtlaw.base.pick(at: Bool, h: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match at:
    case True{}:
      Nil{}
    case False{}:
      Con{h, rest}

# a name without its unit address: its bytes before the first '@' (64)
def fdtlaw.base(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      fdtlaw.base.pick(U32.is_eq(h, 64), h, fdtlaw.base(t))

# a name has a unit address: it holds an '@'
def fdtlaw.has_at(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      Bool.or(U32.is_eq(h, 64), fdtlaw.has_at(t))

# the first node of a list whose name without its unit address is k
def fdtlaw.based(ns: List<&2, T.FdtNode>, +k: B.Octets) -> Maybe<&2, T.FdtNode>:
  match ns:
    case Nil{}:
      None{}
    case Con{n, t}:
      match n:
        case T.FdtNode{+nm, ps, cs}:
          fdtlaw.first.pick(B.Octets.is_eq(B.Octets.of_list(fdtlaw.base(B.Octets.to_list(nm))), k), T.FdtNode{nm, ps, cs}, fdtlaw.based(t, k))

def fdtlaw.based_if(has: Bool, ns: List<&2, T.FdtNode>, k: B.Octets) -> Maybe<&2, T.FdtNode>:
  match has:
    case True{}:
      None{}
    case False{}:
      fdtlaw.based(ns, k)

# the child named k; else, when k has no unit address, the first child whose
# name without its unit address is k
law child_rule:
  for +nm: B.Octets
  for +ps: List<&2, T.FdtProp>
  for +cs: List<&2, T.FdtNode>
  for +k: B.Octets
  {Pa.FdtNode.child(T.FdtNode{nm, ps, cs}, k) == fdtlaw.or(fdtlaw.named(cs, k), fdtlaw.based_if(fdtlaw.has_at(B.Octets.to_list(k)), cs, k)) : Maybe<&2, T.FdtNode>}

# Paths: split on '/' (47), and walked from the root

type FdtPathParts is Data:
  FdtPathParts{first: List<&2, U32>, rest: List<&2, List<&2, U32>>}

def fdtlaw.parts.byte(slash: Bool, h: U32, p: FdtPathParts) -> FdtPathParts:
  match slash:
    case True{}:
      match p:
        case FdtPathParts{f, r}:
          FdtPathParts{Nil{}, Con{f, r}}
    case False{}:
      match p:
        case FdtPathParts{f, r}:
          FdtPathParts{Con{h, f}, r}

# the pieces of a path between its '/'s, the empty ones included: the first
# piece, and the pieces after each '/'
def fdtlaw.parts(xs: List<&2, U32>) -> FdtPathParts:
  match xs:
    case Nil{}:
      FdtPathParts{Nil{}, Nil{}}
    case Con{+h, t}:
      fdtlaw.parts.byte(U32.is_eq(h, 47), h, fdtlaw.parts(t))

def fdtlaw.nonempty(ps: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, r}:
      match p:
        case Nil{}:
          fdtlaw.nonempty(r)
        case Con{h, t}:
          Con{Con{h, t}, fdtlaw.nonempty(r)}

def fdtlaw.components.of(p: FdtPathParts) -> List<&2, List<&2, U32>>:
  match p:
    case FdtPathParts{f, r}:
      fdtlaw.nonempty(Con{f, r})

# the components of a path: its pieces, without the empty ones (from a
# leading '/', from "//" or from a final '/')
def fdtlaw.components(xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  fdtlaw.components.of(fdtlaw.parts(xs))

# from a node, each component in turn names a child (FdtNode.child)
def fdtlaw.walk(cs: List<&2, List<&2, U32>>, m: Maybe<&2, T.FdtNode>) -> Maybe<&2, T.FdtNode>:
  match cs:
    case Nil{}:
      m
    case Con{c, t}:
      match m:
        case Some{n}:
          fdtlaw.walk(t, Pa.FdtNode.child(n, B.Octets.of_list(c)))
        case None{}:
          None{}

# a path is absolute when it starts with '/'
def fdtlaw.absolute(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      U32.is_eq(h, 47)

def fdtlaw.alias.str(r: Result<&2, &2, E.FdtError, B.Octets>) -> Maybe<&2, B.Octets>:
  match r:
    case Done{s}:
      Some{s}
    case Fail{e}:
      None{}

def fdtlaw.alias.val(m: Maybe<&2, B.Octets>) -> Maybe<&2, B.Octets>:
  match m:
    case Some{v}:
      fdtlaw.alias.str(P.FdtProp.string(v))
    case None{}:
      None{}

def fdtlaw.alias.node(m: Maybe<&2, T.FdtNode>, a: List<&2, U32>) -> Maybe<&2, B.Octets>:
  match m:
    case Some{n}:
      fdtlaw.alias.val(Pa.FdtNode.prop(n, B.Octets.of_list(a)))
    case None{}:
      None{}

# the path an alias a stands for: the <string> value of the property a of
# the root's child "aliases"
def fdtlaw.alias(+root: T.FdtNode, a: List<&2, U32>) -> Maybe<&2, B.Octets>:
  fdtlaw.alias.node(Pa.FdtNode.child(root, B.Octets.of_string("aliases")), a)

def fdtlaw.resolve(m: Maybe<&2, B.Octets>, rest: List<&2, List<&2, U32>>, +root: T.FdtNode) -> Maybe<&2, T.FdtNode>:
  match m:
    case Some{s}:
      fdtlaw.walk(List.append(&2, List<&2, U32>, fdtlaw.components(B.Octets.to_list(s)), rest), Some{root})
    case None{}:
      None{}

# a relative path: its first component is an alias, and the alias's path,
# then the other components, are walked from the root
def fdtlaw.relative(+root: T.FdtNode, cs: List<&2, List<&2, U32>>) -> Maybe<&2, T.FdtNode>:
  match cs:
    case Nil{}:
      None{}
    case Con{a, rest}:
      fdtlaw.resolve(fdtlaw.alias(root, a), rest, root)

# an absolute path's components are walked from the root
law find_absolute:
  for +root: T.FdtNode
  for +path: String
  for +e: {fdtlaw.absolute(B.of_string(path)) == True{} : Bool}
  {Pa.FdtNode.find(root, path) == fdtlaw.walk(fdtlaw.components(B.of_string(path)), Some{root}) : Maybe<&2, T.FdtNode>}

# any other path starts with an alias
law find_alias:
  for +root: T.FdtNode
  for +path: String
  for +e: {fdtlaw.absolute(B.of_string(path)) == False{} : Bool}
  {Pa.FdtNode.find(root, path) == fdtlaw.relative(root, fdtlaw.components(B.of_string(path))) : Maybe<&2, T.FdtNode>}

# The reg property

# a number fits n cells: 0 cells hold only 0, one cell a value below 2^32,
# two cells any value
def fdtlaw.fits(n: Nat, +v: W.W64) -> Bool:
  match n:
    case 0n:
      Bool.and(U32.is_eq(W.W64.hi(v), 0), U32.is_eq(W.W64.lo(v), 0))
    case 1n+m:
      match m:
        case 0n:
          U32.is_eq(W.W64.hi(v), 0)
        case 1n+k:
          True{}

# every pair's address fits ac cells and its size sc cells
def fdtlaw.reg_fits(+ac: Nat, +sc: Nat, rs: List<&2, P.FdtReg>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      match r:
        case P.FdtReg{a, s}:
          Bool.and(Bool.and(fdtlaw.fits(ac, a), fdtlaw.fits(sc, s)), fdtlaw.reg_fits(ac, sc, t))

# the pairs read back as of_reg writes them: the cells are cut into pairs of
# ac + sc cells, ac address cells then sc size cells, for every count of 0,
# 1 or 2 cells each (not both 0) and every list of pairs that fit them
law reg_round_trip:
  for +ac: Nat
  for +sc: Nat
  for +hac: {Nat.is_le(ac, 2n) == True{} : Bool}
  for +hsc: {Nat.is_le(sc, 2n) == True{} : Bool}
  for +hnz: {Nat.is_eq(Nat.add(ac, sc), 0n) == False{} : Bool}
  for +rs: List<&2, P.FdtReg>
  for +hf: {fdtlaw.reg_fits(ac, sc, rs) == True{} : Bool}
  {P.FdtProp.reg(ac, sc, P.FdtProp.of_reg(ac, sc, rs)) == Done{rs} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}

# more than 2 address cells, more than 2 size cells, or none at all: refused,
# whatever the value
law reg_address_cells_bad:
  for +ac: Nat
  for +sc: Nat
  for +h: {Nat.is_le(ac, 2n) == False{} : Bool}
  for +o: B.Octets
  {P.FdtProp.reg(ac, sc, o) == Fail{E.FdtBadCells{}} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}

law reg_size_cells_bad:
  for +ac: Nat
  for +sc: Nat
  for +h: {Nat.is_le(sc, 2n) == False{} : Bool}
  for +o: B.Octets
  {P.FdtProp.reg(ac, sc, o) == Fail{E.FdtBadCells{}} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}

law reg_no_cells:
  for +o: B.Octets
  {P.FdtProp.reg(0n, 0n, o) == Fail{E.FdtBadCells{}} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}

# a node's cell counts are its #address-cells and #size-cells <u32>s
law address_cells_value:
  for +n: T.FdtNode
  for +x: U32
  for +h: {Pa.FdtNode.get(n, "#address-cells") == Some{P.FdtProp.of_u32(x)} : Maybe<&2, B.Octets>}
  {Pa.FdtNode.address_cells(n) == U32.to_nat(x) : Nat}

law size_cells_value:
  for +n: T.FdtNode
  for +x: U32
  for +h: {Pa.FdtNode.get(n, "#size-cells") == Some{P.FdtProp.of_u32(x)} : Maybe<&2, B.Octets>}
  {Pa.FdtNode.size_cells(n) == U32.to_nat(x) : Nat}

# a node's reg is decoded with its parent's cell counts; no reg, no pairs
law node_reg:
  for +parent: T.FdtNode
  for +node: T.FdtNode
  for +v: B.Octets
  for +h: {Pa.FdtNode.get(node, "reg") == Some{v} : Maybe<&2, B.Octets>}
  {Pa.FdtNode.reg(parent, node) == P.FdtProp.reg(Pa.FdtNode.address_cells(parent), Pa.FdtNode.size_cells(parent), v) : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}

law node_reg_none:
  for +parent: T.FdtNode
  for +node: T.FdtNode
  for +h: {Pa.FdtNode.get(node, "reg") == None{} : Maybe<&2, B.Octets>}
  {Pa.FdtNode.reg(parent, node) == Done{Nil{}} : Result<&2, &2, E.FdtError, List<&2, P.FdtReg>>}

# The hypotheses above are satisfiable, and a vector of the splitting

law find_absolute_example:
  {fdtlaw.absolute(B.of_string("/cpus")) == True{} : Bool}

law find_alias_example:
  {fdtlaw.absolute(B.of_string("serial0")) == False{} : Bool}

# 0xfe001000 = 4261416960
law reg_fits_example:
  {fdtlaw.reg_fits(1n, 1n, [P.FdtReg{W.W64.from_u32(4261416960), W.W64.from_u32(256)}]) == True{} : Bool}

law components_example:
  {fdtlaw.components(B.of_string("/cpus//cpu@0/")) == [B.of_string("cpus"), B.of_string("cpu@0")] : List<&2, List<&2, U32>>}
