# bend-osdev-apparmor: the choices a caller can make, with the documented
# behaviour as the default.
import Base

# a variable and its values, as @{NAME} = v1 v2 ... assigns them
type AaVar is Data:
  AaVar{name: List<&2, U32>, values: List<&2, List<&2, U32>>}

# complain_deny: deny rules still deny in complain mode (apparmor(7),
# "Complain mode": "deny rules will still result in denials"); False makes
# complain mode allow everything.
# depth: how deeply includes may nest.
# vars: variables defined before any file is read (the tunables a system
# provides, when the file map does not hold them).
type AaOptions is Data:
  AaOptions{complain_deny: Bool, depth: Nat, vars: List<&2, AaVar>}

def AaOptions.default() -> AaOptions:
  AaOptions{True{}, 32n, Nil{}}

def AaOptions.complain_deny(o: AaOptions) -> Bool:
  match o:
    case AaOptions{c, d, v}:
      c

def AaOptions.depth(o: AaOptions) -> Nat:
  match o:
    case AaOptions{c, d, v}:
      d

def AaOptions.vars(o: AaOptions) -> List<&2, AaVar>:
  match o:
    case AaOptions{c, d, v}:
      v

def AaOptions.with_complain_deny(o: AaOptions, b: Bool) -> AaOptions:
  match o:
    case AaOptions{c, d, v}:
      AaOptions{b, d, v}

def AaOptions.with_vars(o: AaOptions, vs: List<&2, AaVar>) -> AaOptions:
  match o:
    case AaOptions{c, d, v}:
      AaOptions{c, d, vs}
