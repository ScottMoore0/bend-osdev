# bend-osdev-landlock: the file hierarchy Landlock rules are tied to, as a
# model: a path is its list of components from the root (no real files), its
# parent drops the last component, and a path is beneath another when the
# other's components are a prefix of its own (a path is beneath itself).
#
# Landlock identifies a hierarchy by the file a rule's parent_fd opens, and
# applies a rule to every path that reaches that file (bind mounts included,
# landlock(7)). The model has one name per file, so "reaches the file" is
# "is beneath the path"; a caller modelling bind mounts gives a rule for each
# name.
import Base

type LandlockPath is Data:
  LandlockPath{names: List<&2, String>}

def LandlockPath.root() -> LandlockPath:
  LandlockPath{Nil{}}

def LandlockPath.of_names(xs: List<&2, String>) -> LandlockPath:
  LandlockPath{xs}

def LandlockPath.names(p: LandlockPath) -> List<&2, String>:
  match p:
    case LandlockPath{xs}:
      xs

# p, then the components of q beneath it
def LandlockPath.join(p: LandlockPath, q: LandlockPath) -> LandlockPath:
  match p q:
    case LandlockPath{xs} LandlockPath{ys}:
      LandlockPath{List.append(&2, String, xs, ys)}

def LandlockPath.child(p: LandlockPath, name: String) -> LandlockPath:
  LandlockPath.join(p, LandlockPath{[name]})

# the list less its last element, h being the first
def LandlockPath.parent.go(t: List<&2, String>, h: String) -> List<&2, String>:
  match t:
    case Nil{}:
      Nil{}
    case Con{h2, t2}:
      Con{h, LandlockPath.parent.go(t2, h2)}

# the directory holding p; the root is its own parent
def LandlockPath.parent(p: LandlockPath) -> LandlockPath:
  match p:
    case LandlockPath{xs}:
      match xs:
        case Nil{}:
          LandlockPath{Nil{}}
        case Con{h, t}:
          LandlockPath{LandlockPath.parent.go(t, h)}

def LandlockPath.depth(p: LandlockPath) -> Nat:
  List.length(&2, String, LandlockPath.names(p))

# Component and path equality, character by character

def LandlockPath.name_eq(a: String, b: String) -> Bool:
  match a:
    case SNil{}:
      match b:
        case SNil{}:
          True{}
        case SCon{bh, bt}:
          False{}
    case SCon{ah, at}:
      match b:
        case SNil{}:
          False{}
        case SCon{bh, bt}:
          Bool.and(Char.is_eq(ah, bh), LandlockPath.name_eq(at, bt))

def LandlockPath.names_eq(xs: List<&2, String>, ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          True{}
        case Con{y, yt}:
          False{}
    case Con{x, xt}:
      match ys:
        case Nil{}:
          False{}
        case Con{y, yt}:
          Bool.and(LandlockPath.name_eq(x, y), LandlockPath.names_eq(xt, yt))

def LandlockPath.is_eq(p: LandlockPath, q: LandlockPath) -> Bool:
  match p q:
    case LandlockPath{xs} LandlockPath{ys}:
      LandlockPath.names_eq(xs, ys)

# xs is a prefix of ys
def LandlockPath.prefix(xs: List<&2, String>, ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, xt}:
      match ys:
        case Nil{}:
          False{}
        case Con{y, yt}:
          Bool.and(LandlockPath.name_eq(x, y), LandlockPath.prefix(xt, yt))

# p is q or a path beneath q: a rule on q applies to p
def LandlockPath.is_beneath(p: LandlockPath, q: LandlockPath) -> Bool:
  match p q:
    case LandlockPath{xs} LandlockPath{ys}:
      LandlockPath.prefix(ys, xs)

# Text: "/usr/lib" and back; empty components ("//", a trailing "/") are dropped

def LandlockPath.flush(cur: String, acc: List<&2, String>) -> List<&2, String>:
  match cur:
    case SNil{}:
      acc
    case SCon{h, t}:
      Con{String.reverse(SCon{h, t}), acc}

def LandlockPath.split.step(slash: Bool, c: Char, cur: String, acc: List<&2, String>) -> String & List<&2, String>:
  match slash:
    case True{}:
      (SNil{}, LandlockPath.flush(cur, acc))
    case False{}:
      (SCon{c, cur}, acc)

def LandlockPath.split.go(s: String, st: String & List<&2, String>) -> List<&2, String>:
  match s:
    case SNil{}:
      (cur, acc) = st
      LandlockPath.flush(cur, acc)
    case SCon{+c, t}:
      (cur, acc) = st
      LandlockPath.split.go(t, LandlockPath.split.step(Char.is_eq(c, '/'), c, cur, acc))

def LandlockPath.of_string(s: String) -> LandlockPath:
  LandlockPath{List.reverse(&2, String, LandlockPath.split.go(s, (SNil{}, Nil{})))}

def LandlockPath.show.go(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{h, t}:
      "/" ++ h ++ LandlockPath.show.go(t)

def LandlockPath.show(p: LandlockPath) -> String:
  match p:
    case LandlockPath{xs}:
      match xs:
        case Nil{}:
          "/"
        case Con{h, t}:
          LandlockPath.show.go(Con{h, t})
