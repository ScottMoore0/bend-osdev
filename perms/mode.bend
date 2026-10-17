# bend-osdev-perms, mode.bend: permission triples, the mode bits of a file,
# and the umask (POSIX.1-2017, XBD 4.5 "File Access Permissions" and
# <sys/stat.h>; umask(2)).
#
# A mode is a U32 whose low 12 bits are, from bit 11 down: set-user-ID,
# set-group-ID, sticky (S_ISVTX), then read, write and execute for the owner,
# the group and others. The fields are read by splitting the word into its
# bits, so that laws about them can be proved for every mode.
import Base

# Read, write and execute (search, for a directory)
type PermsRwx is Data:
  PermsRwx{r: Bool, w: Bool, x: Bool}

def PermsRwx.r(p: PermsRwx) -> Bool:
  match p:
    case PermsRwx{r, w, x}:
      r

def PermsRwx.w(p: PermsRwx) -> Bool:
  match p:
    case PermsRwx{r, w, x}:
      w

def PermsRwx.x(p: PermsRwx) -> Bool:
  match p:
    case PermsRwx{r, w, x}:
      x

def PermsRwx.none() -> PermsRwx:
  PermsRwx{False{}, False{}, False{}}

def PermsRwx.all() -> PermsRwx:
  PermsRwx{True{}, True{}, True{}}

# a requested bit q is granted by p, then the rest
def PermsRwx.covers.bit(q: Bool, p: Bool, rest: Bool) -> Bool:
  match q:
    case False{}:
      rest
    case True{}:
      match p:
        case False{}:
          False{}
        case True{}:
          rest

# every permission in q is in p ("the entry contains the requested
# permissions"); q is looked at first, so an empty request needs nothing of p
def PermsRwx.covers(+p: PermsRwx, q: PermsRwx) -> Bool:
  match q:
    case PermsRwx{qr, qw, qx}:
      PermsRwx.covers.bit(qr, PermsRwx.r(p), PermsRwx.covers.bit(qw, PermsRwx.w(p), PermsRwx.covers.bit(qx, PermsRwx.x(p), True{})))

# the permissions of q that are not in g
def PermsRwx.minus(q: PermsRwx, g: PermsRwx) -> PermsRwx:
  match q g:
    case PermsRwx{qr, qw, qx} PermsRwx{gr, gw, gx}:
      PermsRwx{Bool.and(qr, Bool.not(gr)), Bool.and(qw, Bool.not(gw)), Bool.and(qx, Bool.not(gx))}

def PermsRwx.bit(b: Bool, v: U32) -> U32:
  match b:
    case False{}:
      0
    case True{}:
      v

# as access(2)'s mode: R_OK = 4, W_OK = 2, X_OK = 1
def PermsRwx.to_u32(p: PermsRwx) -> U32:
  match p:
    case PermsRwx{r, w, x}:
      U32.or(PermsRwx.bit(r, 4), U32.or(PermsRwx.bit(w, 2), PermsRwx.bit(x, 1)))

def PermsRwx.of_u32(+v: U32) -> PermsRwx:
  PermsRwx{U32.is_ne(U32.and(4, v), 0), U32.is_ne(U32.and(2, v), 0), U32.is_ne(U32.and(1, v), 0)}

def PermsRwx.char(b: Bool, c: Char) -> Char:
  match b:
    case False{}:
      '-'
    case True{}:
      c

# "rwx", "r-x", ...
def PermsRwx.show(p: PermsRwx) -> String:
  match p:
    case PermsRwx{r, w, x}:
      SCon{PermsRwx.char(r, 'r'), SCon{PermsRwx.char(w, 'w'), SCon{PermsRwx.char(x, 'x'), SNil{}}}}

# The fields of a mode

def Mode.other(m: U32) -> PermsRwx:
  match m:
    case U32{WCon{x, WCon{w, WCon{r, t}}}}:
      PermsRwx{r, w, x}

def Mode.group(m: U32) -> PermsRwx:
  match m:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{x, WCon{w, WCon{r, t}}}}}}}:
      PermsRwx{r, w, x}

def Mode.owner(m: U32) -> PermsRwx:
  match m:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{x, WCon{w, WCon{r, t}}}}}}}}}}:
      PermsRwx{r, w, x}

# S_ISVTX (01000)
def Mode.sticky(m: U32) -> Bool:
  match m:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{s, t}}}}}}}}}}}:
      s

# S_ISGID (02000)
def Mode.setgid(m: U32) -> Bool:
  match m:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{s, t}}}}}}}}}}}}:
      s

# S_ISUID (04000)
def Mode.setuid(m: U32) -> Bool:
  match m:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, WCon{a9, WCon{a10, WCon{s, t}}}}}}}}}}}}}:
      s

# the mode m with its nine permission bits replaced
def Mode.with_perms(m: U32, o: PermsRwx, g: PermsRwx, t: PermsRwx) -> U32:
  match m o g t:
    case U32{WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WCon{a8, rest}}}}}}}}}} PermsRwx{ur, uw, ux} PermsRwx{gr, gw, gx} PermsRwx{tr, tw, tx}:
      U32{WCon{tx, WCon{tw, WCon{tr, WCon{gx, WCon{gw, WCon{gr, WCon{ux, WCon{uw, WCon{ur, rest}}}}}}}}}}

# the mode with these permission bits and no others
def Mode.of_perms(o: PermsRwx, g: PermsRwx, t: PermsRwx) -> U32:
  Mode.with_perms(0, o, g, t)

# whether any of the three execute bits is set
def Mode.any_exec(+m: U32) -> Bool:
  Bool.or(PermsRwx.x(Mode.owner(m)), Bool.or(PermsRwx.x(Mode.group(m)), PermsRwx.x(Mode.other(m))))

# "rwxr-x---"-style, the nine permission bits
def Mode.show(+m: U32) -> String:
  String.append(PermsRwx.show(Mode.owner(m)), String.append(PermsRwx.show(Mode.group(m)), PermsRwx.show(Mode.other(m))))

# The umask

# the mode a file is created with: the mode argument's file mode bits
# (07777), less the permission bits of the umask (umask & 0777)
def Mode.create(mode: U32, umask: U32) -> U32:
  U32.and(U32.and(4095, mode), U32.not(U32.and(511, umask)))
