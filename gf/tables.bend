# bend-osdev-gf, the table-driven fast path for GF(2^8): exponential
# (antilog) and logarithm tables to the field's generator, and
# multiplication, inversion and division through them.
#
# exp[i] = gen^i for i from 0 to 509 (two periods of 255), so exp[log a +
# log b] needs no reduction modulo 255; log[a] is the i < 255 with gen^i =
# a, for a nonzero (log[0] is 0 and never read). The tables are built from
# gf.bend's reference multiplication; they are correct only when gen
# generates the field (it does for the named fields).
#
# A Gf8Tab holds two Arrays, so it has one owner: every operation hands it
# back beside its result. Build it once (Gf8Tab.new) and thread it through.
import Base
import ./gf.bend as G

type Gf8Tab is Type:
  Gf8Tab{exp: Array<U32>, log: Array<U32>}

# exp[i] for i from i0, n entries, with cur = gen^i0
def gf8tab.fill.exp(n: Nat, a: Array<U32>, +f: G.Gf8Field, +cur: U32, +i: U32) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+k:
      gf8tab.fill.exp(k, Array.set(U32, a, i, cur), f, G.Gf8.mul(f, G.Gf8.gen(f), cur), U32.add(i, 1))

# log[gen^i] = i for i from i0, n entries
def gf8tab.fill.log(n: Nat, a: Array<U32>, +f: G.Gf8Field, +cur: U32, +i: U32) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+k:
      gf8tab.fill.log(k, Array.set(U32, a, cur, i), f, G.Gf8.mul(f, G.Gf8.gen(f), cur), U32.add(i, 1))

def Gf8Tab.exp_table(+f: G.Gf8Field) -> Array<U32>:
  gf8tab.fill.exp(510n, [0 : U32*512n], f, 1, 0)

def Gf8Tab.log_table(+f: G.Gf8Field) -> Array<U32>:
  gf8tab.fill.log(255n, [0 : U32*256n], f, 1, 0)

def Gf8Tab.new(+f: G.Gf8Field) -> Gf8Tab:
  Gf8Tab{Gf8Tab.exp_table(f), Gf8Tab.log_table(f)}

# Lookups hand the table back: each helper takes an Array.get result

def gf8tab.exp.fin(r: Array<U32> & U32, l: Array<U32>) -> Gf8Tab & U32:
  (e, v) = r
  (Gf8Tab{e, l}, v)

def gf8tab.log.fin(e: Array<U32>, r: Array<U32> & U32) -> Gf8Tab & U32:
  (l, v) = r
  (Gf8Tab{e, l}, v)

# gen^i, for i below 510
def Gf8Tab.exp(t: Gf8Tab, i: U32) -> Gf8Tab & U32:
  match t:
    case Gf8Tab{e, l}:
      gf8tab.exp.fin(Array.get(U32, e, i), l)

# the logarithm of a nonzero a (0 for a = 0)
def Gf8Tab.log(t: Gf8Tab, a: U32) -> Gf8Tab & U32:
  match t:
    case Gf8Tab{e, l}:
      gf8tab.log.fin(e, Array.get(U32, l, G.Gf8.elt(a)))

def gf8tab.two.idx(div: Bool, +lx: U32, +ly: U32) -> U32:
  match div:
    case True{}:
      U32.sub(U32.add(lx, 255), ly)
    case False{}:
      U32.add(lx, ly)

# exp[log x + log y + k], where k is 0 (multiplying) or 255 - 2 log y
# (dividing: log x + 255 - log y)
def gf8tab.two.fin(e: Array<U32>, ry: Array<U32> & U32, +lx: U32, div: Bool) -> Gf8Tab & U32:
  (l, ly) = ry
  gf8tab.exp.fin(Array.get(U32, e, gf8tab.two.idx(div, lx, ly)), l)

def gf8tab.two.mid(e: Array<U32>, rx: Array<U32> & U32, +y: U32, div: Bool) -> Gf8Tab & U32:
  (l, lx) = rx
  gf8tab.two.fin(e, Array.get(U32, l, y), lx, div)

def gf8tab.two.pick(z: Bool, t: Gf8Tab, +x: U32, +y: U32, div: Bool) -> Gf8Tab & U32:
  match z:
    case True{}:
      (t, 0)
    case False{}:
      match t:
        case Gf8Tab{e, l}:
          gf8tab.two.mid(e, Array.get(U32, l, x), y, div)

# a * b = exp[log a + log b], or 0 if either is 0
def Gf8Tab.mul(t: Gf8Tab, a: U32, b: U32) -> Gf8Tab & U32:
  +x = G.Gf8.elt(a)
  +y = G.Gf8.elt(b)
  gf8tab.two.pick(Bool.or(U32.is_eq(x, 0), U32.is_eq(y, 0)), t, x, y, False{})

# a / b = exp[log a + 255 - log b], or 0 if either is 0 (as Gf8.div)
def Gf8Tab.div(t: Gf8Tab, a: U32, b: U32) -> Gf8Tab & U32:
  +x = G.Gf8.elt(a)
  +y = G.Gf8.elt(b)
  gf8tab.two.pick(Bool.or(U32.is_eq(x, 0), U32.is_eq(y, 0)), t, x, y, True{})

def gf8tab.inv.fin(e: Array<U32>, rx: Array<U32> & U32) -> Gf8Tab & U32:
  (l, lx) = rx
  gf8tab.exp.fin(Array.get(U32, e, U32.sub(255, lx)), l)

def gf8tab.inv.pick(z: Bool, t: Gf8Tab, +x: U32) -> Gf8Tab & U32:
  match z:
    case True{}:
      (t, 0)
    case False{}:
      match t:
        case Gf8Tab{e, l}:
          gf8tab.inv.fin(e, Array.get(U32, l, x))

# a^-1 = exp[255 - log a], and the inverse of 0 is 0
def Gf8Tab.inv(t: Gf8Tab, a: U32) -> Gf8Tab & U32:
  +x = G.Gf8.elt(a)
  gf8tab.inv.pick(U32.is_eq(x, 0), t, x)
