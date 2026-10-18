# bend-osdev-apparmor: permission sets, rule qualifiers, and the grants a
# matching rule contributes.
#
# An AaPerms is a set of permissions of one rule kind, as a list of bits: bit
# i is permission i of that kind (file: r w a l k m x; signal: send receive;
# ...). A missing bit is clear, so sets of different lengths combine.
import Base

type AaPerms is Data:
  AaPerms{bits: List<&2, Bool>}

# Operations on the bit lists

def AaBits.or(a: List<&2, Bool>, b: List<&2, Bool>) -> List<&2, Bool>:
  match a b:
    case Nil{} _:
      b
    case Con{x, xs} Nil{}:
      Con{x, xs}
    case Con{x, xs} Con{y, ys}:
      Con{Bool.or(x, y), AaBits.or(xs, ys)}

# a without b
def AaBits.minus(a: List<&2, Bool>, b: List<&2, Bool>) -> List<&2, Bool>:
  match a b:
    case Nil{} _:
      Nil{}
    case Con{x, xs} Nil{}:
      Con{x, xs}
    case Con{x, xs} Con{y, ys}:
      Con{Bool.and(x, Bool.not(y)), AaBits.minus(xs, ys)}

# some bit is set
def AaBits.any(a: List<&2, Bool>) -> Bool:
  match a:
    case Nil{}:
      False{}
    case Con{x, xs}:
      Bool.or(x, AaBits.any(xs))

# every bit of r is in a
def AaBits.covers(a: List<&2, Bool>, r: List<&2, Bool>) -> Bool:
  match a r:
    case _ Nil{}:
      True{}
    case Nil{} Con{y, ys}:
      Bool.not(AaBits.any(Con{y, ys}))
    case Con{x, xs} Con{y, ys}:
      Bool.and(Bool.or(x, Bool.not(y)), AaBits.covers(xs, ys))

# some bit is in both
def AaBits.meets(a: List<&2, Bool>, b: List<&2, Bool>) -> Bool:
  match a b:
    case Nil{} _:
      False{}
    case Con{x, xs} Nil{}:
      False{}
    case Con{x, xs} Con{y, ys}:
      Bool.or(Bool.and(x, y), AaBits.meets(xs, ys))

# bit i alone
def AaBits.bit(i: Nat) -> List<&2, Bool>:
  match i:
    case 0n:
      [True{}]
    case 1n+j:
      Con{False{}, AaBits.bit(j)}

def AaBits.has(a: List<&2, Bool>, i: Nat) -> Bool:
  match a:
    case Nil{}:
      False{}
    case Con{x, xs}:
      match i:
        case 0n:
          x
        case 1n+j:
          AaBits.has(xs, j)

# The set type

def AaPerms.none() -> AaPerms:
  AaPerms{Nil{}}

def AaPerms.bit(i: Nat) -> AaPerms:
  AaPerms{AaBits.bit(i)}

def AaPerms.of_bits(bs: List<&2, Bool>) -> AaPerms:
  AaPerms{bs}

def AaPerms.bits(p: AaPerms) -> List<&2, Bool>:
  match p:
    case AaPerms{bs}:
      bs

def AaPerms.union(a: AaPerms, b: AaPerms) -> AaPerms:
  match a b:
    case AaPerms{x} AaPerms{y}:
      AaPerms{AaBits.or(x, y)}

def AaPerms.minus(a: AaPerms, b: AaPerms) -> AaPerms:
  match a b:
    case AaPerms{x} AaPerms{y}:
      AaPerms{AaBits.minus(x, y)}

def AaPerms.any(a: AaPerms) -> Bool:
  match a:
    case AaPerms{x}:
      AaBits.any(x)

def AaPerms.covers(a: AaPerms, r: AaPerms) -> Bool:
  match a r:
    case AaPerms{x} AaPerms{y}:
      AaBits.covers(x, y)

def AaPerms.meets(a: AaPerms, b: AaPerms) -> Bool:
  match a b:
    case AaPerms{x} AaPerms{y}:
      AaBits.meets(x, y)

def AaPerms.has(a: AaPerms, i: Nat) -> Bool:
  match a:
    case AaPerms{x}:
      AaBits.has(x, i)

def AaPerms.add(a: AaPerms, i: Nat) -> AaPerms:
  AaPerms.union(a, AaPerms.bit(i))

# the permissions as text: the letter of each set bit, in order
def AaPerms.show.go(bs: List<&2, Bool>, ls: List<&2, String>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{b, rest}:
      match ls:
        case Nil{}:
          ""
        case Con{l, more}:
          String.append(Bool.pick(String, b, l, ""), AaPerms.show.go(rest, more))

def AaPerms.show(p: AaPerms, letters: List<&2, String>) -> String:
  AaPerms.show.go(AaPerms.bits(p), letters)

# Rule qualifiers: audit, deny (allow is the default) and owner

type AaQual is Data:
  AaQual{audit: Bool, deny: Bool, owner: Bool}

def AaQual.none() -> AaQual:
  AaQual{False{}, False{}, False{}}

def AaQual.audit(q: AaQual) -> Bool:
  match q:
    case AaQual{a, d, o}:
      a

def AaQual.deny(q: AaQual) -> Bool:
  match q:
    case AaQual{a, d, o}:
      d

def AaQual.owner(q: AaQual) -> Bool:
  match q:
    case AaQual{a, d, o}:
      o

# What a rule that matches a request contributes: its permissions, allowed or
# denied, audited or not

type AaGrant is Data:
  AaGrant{audit: Bool, deny: Bool, perms: AaPerms}

def AaGrant.of(q: AaQual, p: AaPerms) -> AaGrant:
  match q:
    case AaQual{a, d, o}:
      AaGrant{a, d, p}

def AaGrant.append(xs: List<&2, AaGrant>, ys: List<&2, AaGrant>) -> List<&2, AaGrant>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, AaGrant.append(t, ys)}
