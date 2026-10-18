# bend-osdev-apparmor: mount rules (apparmor.d(5), "MOUNT RULE", "Mount
# Rules"): `mount [CONDS] [SOURCE] [-> MOUNTPOINT]`, `remount [CONDS]
# MOUNTPOINT`, `umount [CONDS] MOUNTPOINT`. Conditions: fstype (or vfstype)
# = or in a list of patterns; options = a set (the mount's options must be
# exactly that set) or in a set (any combination of them). A rule with
# several options conditions grants each set, as the page documents (its
# KNOWN BUGS say the parser merges them; the package follows the
# documented meaning). Unspecified conditions match everything. One
# permission bit: the operation.
import Base
import ./text.bend as X
import ./glob.bend as G
import ./perm.bend as P
import ./token.bend as T
import ./error.bend as E
import ./rule.bend as R

type AaMountOp is Data:
  AaMountOpMount{}
  AaMountOpRemount{}
  AaMountOpUmount{}

# options = (exact) or options in (not exact)
type AaMountOpts is Data:
  AaMountOpts{exact: Bool, flags: List<&2, List<&2, U32>>}

type AaMountRule is Data:
  AaMountRule{qual: P.AaQual, op: AaMountOp, fstypes: Maybe<&2, List<&2, G.AaGlob>>, options: List<&2, AaMountOpts>, source: Maybe<&2, G.AaGlob>, target: Maybe<&2, G.AaGlob>}

# a mount, remount or umount: the filesystem type, the options (names as
# mount(8) -o takes them; rw for a read-write mount), the source device and
# the mountpoint (empty source for remount and umount)
type AaMountQuery is Data:
  AaMountQuery{op: AaMountOp, fstype: List<&2, U32>, options: List<&2, List<&2, U32>>, source: List<&2, U32>, target: List<&2, U32>}

def AaMount.flags() -> List<&2, String>:
  ["ro", "rw", "nosuid", "suid", "nodev", "dev", "noexec", "exec", "sync", "async", "remount", "mand", "nomand", "dirsync", "noatime", "atime", "nodiratime", "diratime", "bind", "rbind", "move", "verbose", "silent", "loud", "acl", "noacl", "unbindable", "runbindable", "private", "rprivate", "slave", "rslave", "shared", "rshared", "relatime", "norelatime", "iversion", "noiversion", "strictatime", "nostrictatime", "lazytime", "nolazytime", "nouser", "user", "symfollow", "nosymfollow"]

def AaMountOp.eq(a: AaMountOp, b: AaMountOp) -> Bool:
  match a b:
    case AaMountOpMount{} AaMountOpMount{}:
      True{}
    case AaMountOpRemount{} AaMountOpRemount{}:
      True{}
    case AaMountOpUmount{} AaMountOpUmount{}:
      True{}
    case _ _:
      False{}

def AaMountOp.is_mount(a: AaMountOp) -> Bool:
  match a:
    case AaMountOpMount{}:
      True{}
    case _:
      False{}

# Reading the terms. pend: 0 nothing pending, 1 after the word fstype, 2
# after options, 3 after fstype in, 4 after options in; arrow: -> seen

type AaMtB is Data:
  AaMtB{pend: Nat, fstypes: Maybe<&2, List<&2, G.AaGlob>>, opts: List<&2, AaMountOpts>, p1: Maybe<&2, G.AaGlob>, arrow: Bool, p2: Maybe<&2, G.AaGlob>}

def AaMtB.fstypes(b: AaMtB, gs: List<&2, G.AaGlob>) -> AaMtB:
  match b:
    case AaMtB{pe, fs, os, p1, ar, p2}:
      AaMtB{0n, R.AaRule.add_globs(fs, gs), os, p1, ar, p2}

def AaMount.opts_append(xs: List<&2, AaMountOpts>, y: AaMountOpts) -> List<&2, AaMountOpts>:
  match xs:
    case Nil{}:
      [y]
    case Con{h, t}:
      Con{h, AaMount.opts_append(t, y)}

def AaMtB.options(b: AaMtB, o: AaMountOpts) -> AaMtB:
  match b:
    case AaMtB{pe, fs, os, p1, ar, p2}:
      AaMtB{0n, fs, AaMount.opts_append(os, o), p1, ar, p2}

def AaMtB.pend(b: AaMtB, n: Nat) -> AaMtB:
  match b:
    case AaMtB{pe, fs, os, p1, ar, p2}:
      AaMtB{n, fs, os, p1, ar, p2}

def AaMtB.pending(b: AaMtB) -> Nat:
  match b:
    case AaMtB{pe, fs, os, p1, ar, p2}:
      pe

def AaMtB.arrow(b: AaMtB, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaMtB>:
  match b:
    case AaMtB{pe, fs, os, p1, ar, p2}:
      match ar:
        case True{}:
          Fail{E.AaSrc.syntax(src)}
        case False{}:
          Done{AaMtB{pe, fs, os, p1, True{}, p2}}

def AaMtB.path.after(p2: Maybe<&2, G.AaGlob>, pe: Nat, fs: Maybe<&2, List<&2, G.AaGlob>>, os: List<&2, AaMountOpts>, p1: Maybe<&2, G.AaGlob>, g: G.AaGlob, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaMtB>:
  match p2:
    case None{}:
      Done{AaMtB{pe, fs, os, p1, True{}, Some{g}}}
    case Some{h}:
      Fail{E.AaSrc.syntax(src)}

def AaMtB.path.before(p1: Maybe<&2, G.AaGlob>, pe: Nat, fs: Maybe<&2, List<&2, G.AaGlob>>, os: List<&2, AaMountOpts>, p2: Maybe<&2, G.AaGlob>, g: G.AaGlob, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaMtB>:
  match p1:
    case None{}:
      Done{AaMtB{pe, fs, os, Some{g}, False{}, p2}}
    case Some{h}:
      Fail{E.AaSrc.syntax(src)}

def AaMtB.path(b: AaMtB, g: G.AaGlob, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaMtB>:
  match b:
    case AaMtB{pe, fs, os, p1, ar, p2}:
      match ar:
        case True{}:
          AaMtB.path.after(p2, pe, fs, os, p1, g, src)
        case False{}:
          AaMtB.path.before(p1, pe, fs, os, p2, g, src)

def AaMtB.cond.fstype(v: T.AaTerm, b: AaMtB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaMtB>:
  do Result<&2, &2, E.AaError, AaMtB>:
    gs : List<&2, G.AaGlob> <- R.AaRule.value_globs(v, src)
    return AaMtB.fstypes(b, gs)

# the pairs of options that cannot both hold, so cannot both be in an exact
# set (what apparmor_parser 4.0.1 refuses as "conflicting flags")
def AaMount.opposed() -> List<&2, String>:
  ["ro", "rw", "suid", "nosuid", "dev", "nodev", "exec", "noexec", "sync", "async", "mand", "nomand", "atime", "noatime", "diratime", "nodiratime", "iversion", "noiversion", "strictatime", "nostrictatime", "lazytime", "nolazytime", "user", "nouser", "symfollow", "nosymfollow", "acl", "noacl", "silent", "loud"]

def AaMount.clash.go(ps: List<&2, String>, +ns: List<&2, List<&2, U32>>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{a, t}:
      match t:
        case Nil{}:
          False{}
        case Con{b, rest}:
          Bool.or(Bool.and(X.AaText.member(ns, X.AaText.of_string(a)), X.AaText.member(ns, X.AaText.of_string(b))), AaMount.clash.go(rest, ns))

def AaMount.check(+exact: Bool, +ns: List<&2, List<&2, U32>>, src: E.AaSrc) -> Result<&2, &2, E.AaError, List<&2, List<&2, U32>>>:
  Bool.pick(Result<&2, &2, E.AaError, List<&2, List<&2, U32>>>, Bool.and(exact, AaMount.clash.go(AaMount.opposed(), ns)), Fail{E.AaSrc.name(src)}, Done{ns})

def AaMtB.cond.options(+exact: Bool, v: T.AaTerm, b: AaMtB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaMtB>:
  do Result<&2, &2, E.AaError, AaMtB>:
    ns0 : List<&2, List<&2, U32>> <- R.AaRule.names(v, AaMount.flags(), src)
    ns : List<&2, List<&2, U32>> <- AaMount.check(exact, ns0, src)
    return AaMtB.options(b, AaMountOpts{exact, ns})

def AaMtB.cond(+k: List<&2, U32>, +v: T.AaTerm, +b: AaMtB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaMtB>:
  Bool.pick(Result<&2, &2, E.AaError, AaMtB>, Bool.or(X.AaText.is(k, "fstype"), X.AaText.is(k, "vfstype")), AaMtB.cond.fstype(v, b, src), Bool.pick(Result<&2, &2, E.AaError, AaMtB>, X.AaText.is(k, "options"), AaMtB.cond.options(True{}, v, b, src), Fail{E.AaSrc.syntax(src)}))

def AaMtB.free.path(r: Result<&2, &2, E.AaError, G.AaGlob>, b: AaMtB, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaMtB>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{g}:
      AaMtB.path(b, g, src)

# a term with nothing pending
def AaMtB.free(t: T.AaTerm, +b: AaMtB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaMtB>:
  match t:
    case T.AaTmWord{+w}:
      Bool.pick(Result<&2, &2, E.AaError, AaMtB>, Bool.or(X.AaText.is(w, "fstype"), X.AaText.is(w, "vfstype")), Done{AaMtB.pend(b, 1n)}, Bool.pick(Result<&2, &2, E.AaError, AaMtB>, X.AaText.is(w, "options"), Done{AaMtB.pend(b, 2n)}, AaMtB.free.path(R.AaRule.glob_text(w, src), b, src)))
    case T.AaTmQuoted{q}:
      AaMtB.free.path(R.AaRule.glob_text(q, src), b, src)
    case T.AaTmCond{k, v}:
      AaMtB.cond(k, v, b, src)
    case T.AaTmArrow{}:
      AaMtB.arrow(b, src)
    case T.AaTmList{xs}:
      Fail{E.AaSrc.syntax(src)}

def AaMtB.step(p: Nat, t: T.AaTerm, +b: AaMtB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaMtB>:
  match p:
    case 0n:
      AaMtB.free(t, b, src)
    case 1n+p1:
      match p1:
        case 0n:
          Bool.pick(Result<&2, &2, E.AaError, AaMtB>, T.AaTerm.is(t, "in"), Done{AaMtB.pend(b, 3n)}, Fail{E.AaSrc.syntax(src)})
        case 1n+p2:
          match p2:
            case 0n:
              Bool.pick(Result<&2, &2, E.AaError, AaMtB>, T.AaTerm.is(t, "in"), Done{AaMtB.pend(b, 4n)}, Fail{E.AaSrc.syntax(src)})
            case 1n+p3:
              match p3:
                case 0n:
                  AaMtB.cond.fstype(t, b, src)
                case 1n+p4:
                  AaMtB.cond.options(False{}, t, b, src)

def AaMtB.run(ts: List<&2, T.AaTerm>, +b: AaMtB, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaMtB>:
  match ts:
    case Nil{}:
      Done{b}
    case Con{t, rest}:
      do Result<&2, &2, E.AaError, AaMtB>:
        b2 : AaMtB <- AaMtB.step(AaMtB.pending(b), t, b, src)
        AaMtB.run(rest, b2, src)

def AaMtB.finish.go(m: Bool, ar: Bool, op: AaMountOp, q: P.AaQual, fs: Maybe<&2, List<&2, G.AaGlob>>, os: List<&2, AaMountOpts>, p1: Maybe<&2, G.AaGlob>, p2: Maybe<&2, G.AaGlob>, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaMountRule>:
  match m:
    case True{}:
      Done{AaMountRule{q, op, fs, os, p1, p2}}
    case False{}:
      match ar:
        case True{}:
          Fail{E.AaSrc.syntax(src)}
        case False{}:
          Done{AaMountRule{q, op, fs, os, None{}, p1}}

# mount: source and mountpoint; remount, umount: one path, the mountpoint, and no arrow
def AaMtB.finish(+op: AaMountOp, q: P.AaQual, b: AaMtB, src: E.AaSrc) -> Result<&2, &2, E.AaError, AaMountRule>:
  match b:
    case AaMtB{pe, fs, os, p1, ar, p2}:
      match pe:
        case 0n:
          AaMtB.finish.go(AaMountOp.is_mount(op), ar, op, q, fs, os, p1, p2, src)
        case 1n+x:
          Fail{E.AaSrc.syntax(src)}

def AaMount.parse.q(r: Result<&2, &2, E.AaError, P.AaQual>, +op: AaMountOp, ts: List<&2, T.AaTerm>, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaMountRule>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{q}:
      do Result<&2, &2, E.AaError, AaMountRule>:
        b : AaMtB <- AaMtB.run(ts, AaMtB{0n, None{}, Nil{}, None{}, False{}, None{}}, src)
        AaMtB.finish(op, q, b, src)

# the terms after mount, remount or umount
def AaMount.parse(op: AaMountOp, ts: List<&2, T.AaTerm>, q: P.AaQual, +src: E.AaSrc) -> Result<&2, &2, E.AaError, AaMountRule>:
  AaMount.parse.q(R.AaRule.no_owner(q, src), op, ts, src)

# Matching

# every option of q is one of the flags; and, for an exact condition, the other way round too
def AaMountOpts.allows(o: AaMountOpts, +q: List<&2, List<&2, U32>>) -> Bool:
  match o:
    case AaMountOpts{exact, +fl}:
      match exact:
        case True{}:
          Bool.and(X.AaText.subset(q, fl), X.AaText.subset(fl, q))
        case False{}:
          X.AaText.subset(q, fl)

def AaMount.opts_ok(os: List<&2, AaMountOpts>, +q: List<&2, List<&2, U32>>) -> Bool:
  match os:
    case Nil{}:
      False{}
    case Con{o, t}:
      Bool.or(AaMountOpts.allows(o, q), AaMount.opts_ok(t, q))

def AaMount.options_ok(os: List<&2, AaMountOpts>, +q: List<&2, List<&2, U32>>) -> Bool:
  match os:
    case Nil{}:
      True{}
    case Con{o, t}:
      AaMount.opts_ok(Con{o, t}, q)

def AaMountRule.matches(r: AaMountRule, q: AaMountQuery) -> Bool:
  match r:
    case AaMountRule{qu, op, fs, os, so, tg}:
      match q:
        case AaMountQuery{qop, qfs, qos, qso, qtg}:
          Bool.and(AaMountOp.eq(op, qop), Bool.and(R.AaRule.opt_any(fs, qfs), Bool.and(AaMount.options_ok(os, qos), Bool.and(R.AaRule.opt_match(so, qso), R.AaRule.opt_match(tg, qtg)))))

def AaMountRule.matching.go(hit: Bool, r: AaMountRule, rest: List<&2, AaMountRule>) -> List<&2, AaMountRule>:
  match hit:
    case True{}:
      Con{r, rest}
    case False{}:
      rest

def AaMountRule.matching(rs: List<&2, AaMountRule>, +q: AaMountQuery) -> List<&2, AaMountRule>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+r, t}:
      AaMountRule.matching.go(AaMountRule.matches(r, q), r, AaMountRule.matching(t, q))

def AaMountRule.grants.of(rs: List<&2, AaMountRule>) -> List<&2, P.AaGrant>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      match r:
        case AaMountRule{qu, op, fs, os, so, tg}:
          Con{P.AaGrant.of(qu, P.AaPerms.bit(0n)), AaMountRule.grants.of(t)}

def AaMountRule.grants(rs: List<&2, AaMountRule>, +q: AaMountQuery) -> List<&2, P.AaGrant>:
  AaMountRule.grants.of(AaMountRule.matching(rs, q))

def AaMountRule.append(xs: List<&2, AaMountRule>, ys: List<&2, AaMountRule>) -> List<&2, AaMountRule>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, AaMountRule.append(t, ys)}

def AaMountQuery.req() -> P.AaPerms:
  P.AaPerms.bit(0n)
