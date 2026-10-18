# bend-osdev-apparmor: why a policy fails to load. Each failure names the
# file and line where it was found (line 0 when it belongs to no line).
import Base

type AaError is Data:
  # the text cannot be split into tokens (an unterminated quote, an unbalanced parenthesis)
  AaErrLex{file: List<&2, U32>, line: U32}
  # a statement or block that does not fit the grammar
  AaErrSyntax{file: List<&2, U32>, line: U32}
  # a malformed pattern (glob)
  AaErrGlob{file: List<&2, U32>, line: U32}
  # an unknown name: capability, network domain or type, signal, mount option, flag
  AaErrName{file: List<&2, U32>, line: U32}
  # an invalid permission string: unknown letters, w with a, two exec modes,
  # an exec mode in a deny rule, a bare x in an allow rule, a target without an exec mode
  AaErrPerms{file: List<&2, U32>, line: U32}
  # a rule kind or condition outside the model (unix, pivot_root, rlimit, link, ...)
  AaErrUnsupported{file: List<&2, U32>, line: U32}
  # an included file that is not in the file map (and the include is not "if exists")
  AaErrInclude{file: List<&2, U32>, line: U32}
  # includes nested deeper than the options allow
  AaErrIncludeDepth{file: List<&2, U32>, line: U32}
  # a variable used but never assigned
  AaErrVarUndefined{file: List<&2, U32>, line: U32}
  # a variable assigned with = twice, or extended with += before it is assigned
  AaErrVarRedefined{file: List<&2, U32>, line: U32}
  # a variable or alias statement after the first profile, or inside one
  AaErrPreamble{file: List<&2, U32>, line: U32}
  # an unknown or conflicting profile flag
  AaErrFlag{file: List<&2, U32>, line: U32}
  # two profiles, children or hats with the same name
  AaErrDuplicate{file: List<&2, U32>, line: U32}
  # two rules for the same literal path with different exec modes
  AaErrExecConflict{file: List<&2, U32>, line: U32}

def AaError.line(e: AaError) -> U32:
  match e:
    case AaErrLex{f, l}:
      l
    case AaErrSyntax{f, l}:
      l
    case AaErrGlob{f, l}:
      l
    case AaErrName{f, l}:
      l
    case AaErrPerms{f, l}:
      l
    case AaErrUnsupported{f, l}:
      l
    case AaErrInclude{f, l}:
      l
    case AaErrIncludeDepth{f, l}:
      l
    case AaErrVarUndefined{f, l}:
      l
    case AaErrVarRedefined{f, l}:
      l
    case AaErrPreamble{f, l}:
      l
    case AaErrFlag{f, l}:
      l
    case AaErrDuplicate{f, l}:
      l
    case AaErrExecConflict{f, l}:
      l

def AaError.name(e: AaError) -> String:
  match e:
    case AaErrLex{f, l}:
      "lex"
    case AaErrSyntax{f, l}:
      "syntax"
    case AaErrGlob{f, l}:
      "glob"
    case AaErrName{f, l}:
      "name"
    case AaErrPerms{f, l}:
      "perms"
    case AaErrUnsupported{f, l}:
      "unsupported"
    case AaErrInclude{f, l}:
      "include"
    case AaErrIncludeDepth{f, l}:
      "include-depth"
    case AaErrVarUndefined{f, l}:
      "var-undefined"
    case AaErrVarRedefined{f, l}:
      "var-redefined"
    case AaErrPreamble{f, l}:
      "preamble"
    case AaErrFlag{f, l}:
      "flag"
    case AaErrDuplicate{f, l}:
      "duplicate"
    case AaErrExecConflict{f, l}:
      "exec-conflict"

# where a statement came from: what rule parsers report errors against
type AaSrc is Data:
  AaSrc{file: List<&2, U32>, line: U32}

def AaSrc.line(s: AaSrc) -> U32:
  match s:
    case AaSrc{f, l}:
      l

def AaSrc.lex(s: AaSrc) -> AaError:
  match s:
    case AaSrc{f, l}:
      AaErrLex{f, l}

def AaSrc.syntax(s: AaSrc) -> AaError:
  match s:
    case AaSrc{f, l}:
      AaErrSyntax{f, l}

def AaSrc.glob(s: AaSrc) -> AaError:
  match s:
    case AaSrc{f, l}:
      AaErrGlob{f, l}

def AaSrc.name(s: AaSrc) -> AaError:
  match s:
    case AaSrc{f, l}:
      AaErrName{f, l}

def AaSrc.perms(s: AaSrc) -> AaError:
  match s:
    case AaSrc{f, l}:
      AaErrPerms{f, l}

def AaSrc.unsupported(s: AaSrc) -> AaError:
  match s:
    case AaSrc{f, l}:
      AaErrUnsupported{f, l}

def AaSrc.include(s: AaSrc) -> AaError:
  match s:
    case AaSrc{f, l}:
      AaErrInclude{f, l}

def AaSrc.include_depth(s: AaSrc) -> AaError:
  match s:
    case AaSrc{f, l}:
      AaErrIncludeDepth{f, l}

def AaSrc.var_undefined(s: AaSrc) -> AaError:
  match s:
    case AaSrc{f, l}:
      AaErrVarUndefined{f, l}

def AaSrc.var_redefined(s: AaSrc) -> AaError:
  match s:
    case AaSrc{f, l}:
      AaErrVarRedefined{f, l}

def AaSrc.preamble(s: AaSrc) -> AaError:
  match s:
    case AaSrc{f, l}:
      AaErrPreamble{f, l}

def AaSrc.flag(s: AaSrc) -> AaError:
  match s:
    case AaSrc{f, l}:
      AaErrFlag{f, l}

def AaSrc.duplicate(s: AaSrc) -> AaError:
  match s:
    case AaSrc{f, l}:
      AaErrDuplicate{f, l}

def AaSrc.exec_conflict(s: AaSrc) -> AaError:
  match s:
    case AaSrc{f, l}:
      AaErrExecConflict{f, l}
