# bend-osdev-acpi: the ACPI tables of a machine, found and read through
# physical memory (ACPI 6.5, section 5.2: the RSDP leads to the RSDT or
# XSDT, which lists every other table but the DSDT and the FACS, which the
# FADT points to).
#
# Physical memory is read through a template argument, so any memory works
# (a mapped window in a kernel, a firmware image, a test image):
#
#   ~M: Data, ~read: M -> W64 -> Nat -> Result<&2, &2, AcpiError, Octets>
#
# read(m, address, n) answers the n bytes at a physical address, or
# AcpiNotMapped. AcpiMemImage is an in-memory default. Tables are read one
# at a time: a header's first 8 bytes for its length, then the table.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./header.bend as H
import ./rsdp.bend as P
import ./rsdt.bend as S
import ./fadt.bend as F
import ./facs.bend as FS
import ./registry.bend as R

# An in-memory physical memory: regions at base addresses

type AcpiMemRegion is Data:
  AcpiMemRegion{base: W.W64, bytes: B.Octets}

type AcpiMemImage is Data:
  AcpiMemImage{regions: List<&2, AcpiMemRegion>}

def mem.slice(inside: Bool, +off: Nat, +n: Nat, +o: B.Octets) -> Maybe<&2, B.Octets>:
  match inside:
    case False{}:
      None{}
    case True{}:
      Some{B.Octets.slice(off, n, o)}

# the offset into the region is computed only once it is known to be small
# (a Nat holds at most 2^48 - 1 at run time)
def mem.near(near: Bool, +off: W.W64, +n: Nat, +o: B.Octets) -> Maybe<&2, B.Octets>:
  match near:
    case False{}:
      None{}
    case True{}:
      +k = U32.to_nat(W.W64.lo(off))
      mem.slice(Nat.is_le(Nat.add(k, n), B.Octets.len(o)), k, n, o)

def mem.above(above: Bool, +base: W.W64, +addr: W.W64, +n: Nat, +o: B.Octets) -> Maybe<&2, B.Octets>:
  match above:
    case False{}:
      None{}
    case True{}:
      +off = W.W64.sub(addr, base)
      mem.near(U32.is_eq(W.W64.hi(off), 0), off, n, o)

def mem.try(r: AcpiMemRegion, +addr: W.W64, +n: Nat) -> Maybe<&2, B.Octets>:
  match r:
    case AcpiMemRegion{+base, +o}:
      mem.above(W.W64.is_le(base, addr), base, addr, n, o)

def mem.find(rs: List<&2, AcpiMemRegion>, +addr: W.W64, +n: Nat) -> Maybe<&2, B.Octets>:
  match rs:
    case Nil{}:
      None{}
    case Con{h, t}:
      Maybe.or(&2, B.Octets, mem.try(h, addr, n), mem.find(t, addr, n))

def mem.done(m: Maybe<&2, B.Octets>, +addr: W.W64) -> Result<&2, &2, E.AcpiError, B.Octets>:
  match m:
    case None{}:
      Fail{E.AcpiNotMapped{addr}}
    case Some{o}:
      Done{o}

# n bytes at a physical address, from the first region holding all of them
def mem.read(m: AcpiMemImage, +addr: W.W64, +n: Nat) -> Result<&2, &2, E.AcpiError, B.Octets>:
  match m:
    case AcpiMemImage{rs}:
      mem.done(mem.find(rs, addr, n), addr)

# (plain parameters, so that it fits the template type ~read)
def AcpiMemImage.read(m: AcpiMemImage, addr: W.W64, n: Nat) -> Result<&2, &2, E.AcpiError, B.Octets>:
  mem.read(m, addr, n)

def AcpiMemImage.of_list(rs: List<&2, AcpiMemRegion>) -> AcpiMemImage:
  AcpiMemImage{rs}

# Options

type AcpiLoadOptions is Data:
  # use the XSDT when the RSDP has one (ACPI 6.5, 5.2.5.3: OSPM uses the
  # XSDT if present); False reads the RSDT
  AcpiLoadOptions{prefer_xsdt: Bool, registry: R.AcpiRegistry}

def AcpiLoadOptions.default() -> AcpiLoadOptions:
  AcpiLoadOptions{True{}, R.AcpiRegistry.default()}

# What a machine's tables hold

# a table, by the address it was read from; a table that fails to read
# does not stop the others
type AcpiLoaded<-X: Data> is Data:
  AcpiLoaded{address: W.W64, table: Result<&2, &2, E.AcpiError, R.AcpiTable<X>>}

type AcpiTableSet<-X: Data> is Data:
  AcpiTableSet{rsdp: P.AcpiRsdp, root: S.AcpiSdtList, tables: List<&2, AcpiLoaded<X>>, facs: Maybe<&2, Result<&2, &2, E.AcpiError, FS.AcpiFacs>>}

# Reading

# the table at a physical address: its length from its header, then all of
# its bytes
def ld.whole(~M: Data, ~read: M -> W.W64 -> Nat -> Result<&2, &2, E.AcpiError, B.Octets>, +m: M, +addr: W.W64, +head: B.Octets) -> Result<&2, &2, E.AcpiError, B.Octets>:
  read(m, addr, U32.to_nat(Maybe.default(&2, U32, B.Octets.le32_at(head, 4n), 0)))

def AcpiTables.read_table(~M: Data, ~read: M -> W.W64 -> Nat -> Result<&2, &2, E.AcpiError, B.Octets>, +m: M, +addr: W.W64) -> Result<&2, &2, E.AcpiError, B.Octets>:
  do Result<&2, &2, E.AcpiError, B.Octets>:
    head : B.Octets <- read(m, addr, 8n)
    ld.whole(~M, ~read, m, addr, head)

def ld.rsdp.pick(v1: Bool) -> Nat:
  match v1:
    case True{}:
      20n
    case False{}:
      36n

def ld.rsdp.len(+head: B.Octets) -> Nat:
  ld.rsdp.pick(U32.is_lt(Maybe.default(&2, U32, B.Octets.at(head, 15n), 0), 2))

def AcpiTables.read_rsdp(~M: Data, ~read: M -> W.W64 -> Nat -> Result<&2, &2, E.AcpiError, B.Octets>, +m: M, +addr: W.W64) -> Result<&2, &2, E.AcpiError, P.AcpiRsdp>:
  do Result<&2, &2, E.AcpiError, P.AcpiRsdp>:
    head : B.Octets <- read(m, addr, 20n)
    o : B.Octets <- read(m, addr, ld.rsdp.len(head))
    P.AcpiRsdp.parse(o)

def ld.root.parse(xsdt: Bool, +o: B.Octets) -> Result<&2, &2, E.AcpiError, S.AcpiSdtList>:
  match xsdt:
    case True{}:
      S.AcpiXsdt.parse(o)
    case False{}:
      S.AcpiRsdt.parse(o)

def ld.root(~M: Data, ~read: M -> W.W64 -> Nat -> Result<&2, &2, E.AcpiError, B.Octets>, +m: M, +xsdt: Bool, +addr: W.W64) -> Result<&2, &2, E.AcpiError, S.AcpiSdtList>:
  do Result<&2, &2, E.AcpiError, S.AcpiSdtList>:
    o : B.Octets <- AcpiTables.read_table(~M, ~read, m, addr)
    ld.root.parse(xsdt, o)

def ld.one(~M: Data, ~read: M -> W.W64 -> Nat -> Result<&2, &2, E.AcpiError, B.Octets>, ~X: Data, ~ext: U32 -> H.AcpiSdt -> Result<&2, &2, E.AcpiError, X>, +m: M, +reg: R.AcpiRegistry, +addr: W.W64) -> AcpiLoaded<X>:
  AcpiLoaded{addr, Result.bind(&2, &2, E.AcpiError, B.Octets, R.AcpiTable<X>, AcpiTables.read_table(~M, ~read, m, addr), o => R.AcpiTable.parse_with(~X, ~ext, reg, o))}

def ld.all(~M: Data, ~read: M -> W.W64 -> Nat -> Result<&2, &2, E.AcpiError, B.Octets>, ~X: Data, ~ext: U32 -> H.AcpiSdt -> Result<&2, &2, E.AcpiError, X>, as: List<&2, W.W64>, +m: M, +reg: R.AcpiRegistry) -> List<&2, AcpiLoaded<X>>:
  match as:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      Con{ld.one(~M, ~read, ~X, ~ext, m, reg, a), ld.all(~M, ~read, ~X, ~ext, t, m, reg)}

# the FADT among the tables read
def ld.fadt(~X: Data, ts: List<&2, AcpiLoaded<X>>) -> Maybe<&2, F.AcpiFadt>:
  match ts:
    case Nil{}:
      None{}
    case Con{AcpiLoaded{a, Done{R.AcpiTFadt{f}}}, t}:
      Some{f}
    case Con{h, t}:
      ld.fadt(~X, t)

def ld.nz.pick(z: Bool, +a: W.W64) -> Maybe<&2, W.W64>:
  match z:
    case True{}:
      None{}
    case False{}:
      Some{a}

def ld.nz(+a: W.W64) -> Maybe<&2, W.W64>:
  ld.nz.pick(W.W64.is_zero(a), a)

def ld.list(m: Maybe<&2, W.W64>) -> List<&2, W.W64>:
  match m:
    case None{}:
      Nil{}
    case Some{a}:
      [a]

def ld.dsdt(~M: Data, ~read: M -> W.W64 -> Nat -> Result<&2, &2, E.AcpiError, B.Octets>, ~X: Data, ~ext: U32 -> H.AcpiSdt -> Result<&2, &2, E.AcpiError, X>, f: Maybe<&2, F.AcpiFadt>, +m: M, +reg: R.AcpiRegistry) -> List<&2, AcpiLoaded<X>>:
  match f:
    case None{}:
      Nil{}
    case Some{+fa}:
      ld.all(~M, ~read, ~X, ~ext, ld.list(ld.nz(F.AcpiFadt.dsdt_address(fa))), m, reg)

def ld.facs.at(~M: Data, ~read: M -> W.W64 -> Nat -> Result<&2, &2, E.AcpiError, B.Octets>, +m: M, a: Maybe<&2, W.W64>) -> Maybe<&2, Result<&2, &2, E.AcpiError, FS.AcpiFacs>>:
  match a:
    case None{}:
      None{}
    case Some{+addr}:
      Some{Result.bind(&2, &2, E.AcpiError, B.Octets, FS.AcpiFacs, read(m, addr, 64n), o => FS.AcpiFacs.parse(o))}

def ld.facs(~M: Data, ~read: M -> W.W64 -> Nat -> Result<&2, &2, E.AcpiError, B.Octets>, f: Maybe<&2, F.AcpiFadt>, +m: M) -> Maybe<&2, Result<&2, &2, E.AcpiError, FS.AcpiFacs>>:
  match f:
    case None{}:
      None{}
    case Some{+fa}:
      ld.facs.at(~M, ~read, m, ld.nz(F.AcpiFadt.facs_address(fa)))

def ld.use_x(prefer: Bool, +r: P.AcpiRsdp) -> Bool:
  match prefer:
    case True{}:
      Bool.not(W.W64.is_zero(P.AcpiRsdp.xsdt_address(r)))
    case False{}:
      False{}

def ld.root_addr(x: Bool, +r: P.AcpiRsdp) -> W.W64:
  match x:
    case True{}:
      P.AcpiRsdp.xsdt_address(r)
    case False{}:
      W.W64.from_u32(P.AcpiRsdp.rsdt_address(r))

def ld.finish(~M: Data, ~read: M -> W.W64 -> Nat -> Result<&2, &2, E.AcpiError, B.Octets>, ~X: Data, ~ext: U32 -> H.AcpiSdt -> Result<&2, &2, E.AcpiError, X>, +m: M, +reg: R.AcpiRegistry, rsdp: P.AcpiRsdp, +root: S.AcpiSdtList) -> AcpiTableSet<X>:
  +ts = ld.all(~M, ~read, ~X, ~ext, S.AcpiSdtList.entries(root), m, reg)
  +f = ld.fadt(~X, ts)
  AcpiTableSet{rsdp, root, List.append(&2, AcpiLoaded<X>, ts, ld.dsdt(~M, ~read, ~X, ~ext, f, m, reg)), ld.facs(~M, ~read, f, m)}

def ld.opts(o: AcpiLoadOptions) -> Bool:
  match o:
    case AcpiLoadOptions{p, r}:
      p

def ld.reg(o: AcpiLoadOptions) -> R.AcpiRegistry:
  match o:
    case AcpiLoadOptions{p, r}:
      r

# every table of the machine whose RSDP is at rsdp_addr: the RSDP, the RSDT
# or XSDT (Fail if either cannot be read), then each table it lists, the
# DSDT (from the FADT) and the FACS, each read and parsed on its own
def AcpiTables.load_with(~M: Data, ~read: M -> W.W64 -> Nat -> Result<&2, &2, E.AcpiError, B.Octets>, ~X: Data, ~ext: U32 -> H.AcpiSdt -> Result<&2, &2, E.AcpiError, X>, +opts: AcpiLoadOptions, +m: M, +rsdp_addr: W.W64) -> Result<&2, &2, E.AcpiError, AcpiTableSet<X>>:
  do Result<&2, &2, E.AcpiError, AcpiTableSet<X>>:
    +r : P.AcpiRsdp <- AcpiTables.read_rsdp(~M, ~read, m, rsdp_addr)
    +x : Bool = ld.use_x(ld.opts(opts), r)
    root : S.AcpiSdtList <- ld.root(~M, ~read, m, x, ld.root_addr(x, r))
    return ld.finish(~M, ~read, ~X, ~ext, m, ld.reg(opts), r, root)

def AcpiTables.load(~M: Data, ~read: M -> W.W64 -> Nat -> Result<&2, &2, E.AcpiError, B.Octets>, +m: M, +rsdp_addr: W.W64) -> Result<&2, &2, E.AcpiError, AcpiTableSet<R.AcpiNoExt>>:
  AcpiTables.load_with(~M, ~read, ~R.AcpiNoExt, ~R.AcpiNoExt.parse, AcpiLoadOptions.default(), m, rsdp_addr)

# Queries

def AcpiTableSet.tables(~X: Data, s: AcpiTableSet<X>) -> List<&2, AcpiLoaded<X>>:
  match s:
    case AcpiTableSet{r, root, ts, f}:
      ts

def ld.find.pick(~X: Data, hit: Bool, t: R.AcpiTable<X>, rest: Maybe<&2, R.AcpiTable<X>>) -> Maybe<&2, R.AcpiTable<X>>:
  match hit:
    case True{}:
      Some{t}
    case False{}:
      rest

def ld.find(~X: Data, ts: List<&2, AcpiLoaded<X>>, +name: String) -> Maybe<&2, R.AcpiTable<X>>:
  match ts:
    case Nil{}:
      None{}
    case Con{AcpiLoaded{a, Done{+t}}, rest}:
      ld.find.pick(~X, String.eq(R.AcpiTable.name(~X, t), name), t, ld.find(~X, rest, name))
    case Con{h, rest}:
      ld.find(~X, rest, name)

# the first table read whose parser's name (R.AcpiTable.name: the
# signature) is name
def AcpiTableSet.find(~X: Data, s: AcpiTableSet<X>, +name: String) -> Maybe<&2, R.AcpiTable<X>>:
  ld.find(~X, AcpiTableSet.tables(~X, s), name)
