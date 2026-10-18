import Base
import ../bytes/bytes.bend as B
import ./text.bend as X
import ./glob.bend as G
import ./perm.bend as P
import ./error.bend as E
import ./options.bend as O
import ./profile.bend as PR
import ./eval.bend as V
import ./transitions.bend as TR
import ./rule_file.bend as F
import ./rule_mount.bend as RM
import ./rule_dbus.bend as RD
import ./example.bend as EX
import ./apparmor.bend as A

def o(s: String) -> B.Octets:
  B.Octets.of_string(s)

def l(s: String) -> List<&2, U32>:
  X.AaText.of_string(s)

def show.d(m: Maybe<&2, V.AaDecision>) -> String:
  match m:
    case None{}:
      "no profile"
    case Some{d}:
      V.AaDecision.show(d)

def show.load(r: Result<&2, &2, E.AaError, PR.AaPolicy>) -> String:
  match r:
    case Fail{+e}:
      "error " ++ E.AaError.name(e) ++ " at line " ++ U32.show(E.AaError.line(e))
    case Done{p}:
      "ok, " ++ Nat.show(List.length(&2, PR.AaProfile, PR.AaPolicy.profiles(p))) ++ " profiles"

# a one-file policy
def load1(t: String) -> String:
  show.load(A.Aa.load_default([EX.AaExample.source("p", t)], o("p")))

def g(+p: String, +s: String) -> String:
  p ++ " ~ " ++ s ++ ": " ++ Bool.show(G.AaGlob.match_text(l(p), l(s)))

def pol() -> PR.AaPolicy:
  EX.AaExample.pol()

# Larger inputs: a profile of n rules, and a long path

def big.rules(n: Nat, +i: U32, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+k:
      big.rules(k, U32.add(i, 1), acc ++ "  /data/d" ++ U32.show(i) ++ "/** r,\n  deny /data/d" ++ U32.show(i) ++ "/secret w,\n")

def big.text(n: Nat) -> String:
  "profile big {\n" ++ big.rules(n, 0, "") ++ "}\n"

def big.path.go(n: Nat, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+k:
      big.path.go(k, acc ++ "/abcdefghij")

def big.path(n: Nat) -> String:
  "/data/d299" ++ big.path.go(n, "") ++ "/file"

def big.query(+r: Result<&2, &2, E.AaError, PR.AaPolicy>, path: String, perms: String) -> String:
  match r:
    case Fail{e}:
      "no policy"
    case Done{p}:
      show.d(A.Aa.file(O.AaOptions.default(), p, o("big"), o(path), False{}, F.AaFile.perms(perms)))

def main() -> IO(Unit):
  +big = A.Aa.load_default([EX.AaExample.source("big", big.text(300n))], o("big"))
  do IO<Unit>:
    IO.print("example: " ++ show.load(EX.AaExample.loaded()))
    IO.print(show.d(EX.AaExample.file("/usr/bin/foo", "/etc/ld.so.cache", "r")))
    IO.print(show.d(EX.AaExample.file("/usr/bin/foo", "/etc/ld.so.cache", "w")))
    IO.print(show.d(EX.AaExample.file("/usr/bin/foo", "/lib/x86_64/libc.so.6", "mr")))
    IO.print(show.d(EX.AaExample.file("/usr/bin/foo", "/home/bob/.foo_file", "rw")))
    IO.print(show.d(EX.AaExample.file("/usr/bin/foo", "/etc/shadow", "r")))
    IO.print(show.d(EX.AaExample.file("/usr/bin/foo", "/var/log/foo", "w")))
    IO.print(show.d(EX.AaExample.file("/usr/bin/foo", "/tmp/foo.1", "l")))
    IO.print(show.d(A.Aa.file(O.AaOptions.default(), pol(), o("/usr/bin/foo"), o("/proc/42/stat"), True{}, F.AaFile.perms("r"))))
    IO.print(show.d(EX.AaExample.file("/usr/bin/foo", "/proc/42/stat", "r")))
    IO.print(show.d(EX.AaExample.file("/usr/bin/foo//hat", "/var/spool/q", "rw")))
    IO.print(show.d(EX.AaExample.file("bar", "/etc/anything", "r")))
    IO.print(show.d(EX.AaExample.file("bar", "/etc/secret", "r")))
    IO.print(show.d(A.Aa.file(O.AaOptions.with_complain_deny(O.AaOptions.default(), False{}), pol(), o("bar"), o("/etc/secret"), False{}, F.AaFile.perms("r"))))
    IO.print(show.d(A.Aa.capability(O.AaOptions.default(), pol(), o("/usr/bin/foo"), 7)))
    IO.print(show.d(A.Aa.capability(O.AaOptions.default(), pol(), o("/usr/bin/foo"), 21)))
    IO.print(show.d(A.Aa.network(O.AaOptions.default(), pol(), o("/usr/bin/foo"), o("inet"), o("stream"), o("tcp"))))
    IO.print(show.d(A.Aa.network(O.AaOptions.default(), pol(), o("/usr/bin/foo"), o("inet6"), o("stream"), o("tcp"))))
    IO.print(show.d(A.Aa.signal(O.AaOptions.default(), pol(), o("/usr/bin/foo"), P.AaPerms.bit(0n), o("term"), o("/usr/bin/bar"))))
    IO.print(show.d(A.Aa.signal(O.AaOptions.default(), pol(), o("/usr/bin/foo"), P.AaPerms.bit(1n), o("term"), o("/usr/bin/bar"))))
    IO.print(EX.AaExample.exec("/usr/bin/foo", "/bin/mount"))
    IO.print(EX.AaExample.exec("/usr/bin/foo", "/usr/bin/baz"))
    IO.print(EX.AaExample.exec("/usr/bin/foo", "/usr/bin/bar"))
    IO.print(EX.AaExample.exec("/usr/bin/foo", "/usr/bin/zzz"))
    IO.print(EX.AaExample.exec("/usr/bin/foo", "/bin/sh"))
    IO.print(EX.AaExample.exec("/usr/bin/foo//baz", "/bin/bash"))
    IO.print(TR.AaExecResult.show(A.Aa.exec_unconfined(pol(), o("/usr/bin/bar"))))
    IO.print(TR.AaExecResult.show(A.Aa.exec_unconfined(pol(), o("/usr/bin/other"))))
    IO.print(load1("profile e { /x wa, }"))
    IO.print(load1("profile e {\n  /x r,\n  /y ix px,\n}"))
    IO.print(load1("profile e { capability bogus, }"))
    IO.print(load1("profile e { @{NOPE}/x r, }"))
    IO.print(load1("@{A} = /x\n@{A} = /y\nprofile e { }"))
    IO.print(load1("profile e { /x ix, /x px, }"))
    IO.print(load1("profile e { unix, }"))
    IO.print(load1("profile e { include <missing> }"))
    IO.print(load1("profile e { include if exists <missing> }"))
    IO.print(load1("profile e { /x/{a} r, }"))
    IO.print(load1("profile e flags=(complain,kill) { }"))
    IO.print(load1("profile e { } profile e { }"))
    IO.print(load1("profile e { /x r }"))
    IO.print(g("/tmp/*", "/tmp/"))
    IO.print(g("/tmp/**", "/tmp/a/b"))
    IO.print(g("/a/{b,c{d,e}}/*", "/a/cd/x"))
    IO.print(g("/a/[^b]c", "/a//c"))
    IO.print(g("/a/**/b/**/c/**/d/**/e*", "/a/1/2/b/3/c/4/5/d/6/7/8/f/9/x/y/z/w/v/u/t/s/r/q/p/o/n/m/l"))
    IO.print("big: " ++ show.load(big))
    IO.print(big.query(big, "/data/d150/x", "r"))
    IO.print(big.query(big, "/data/d150/secret", "w"))
    IO.print(big.query(big, "/data/d300/x", "r"))
    IO.print(big.query(big, big.path(200n), "r"))

#|example: ok, 2 profiles
#|allow
#|deny
#|allow
#|allow
#|deny-quiet
#|audit
#|allow
#|allow
#|deny
#|allow
#|complain
#|deny-quiet
#|complain
#|allow
#|deny
#|allow
#|deny
#|allow
#|deny
#|unconfined
#|profile /usr/bin/foo//baz scrub
#|profile bar
#|stay
#|denied (deny)
#|stay
#|profile bar
#|unconfined
#|error perms at line 1
#|error syntax at line 3
#|error name at line 1
#|error var-undefined at line 1
#|error var-redefined at line 2
#|error exec-conflict at line 1
#|error unsupported at line 1
#|error include at line 1
#|ok, 1 profiles
#|error glob at line 1
#|error flag at line 1
#|error duplicate at line 1
#|error syntax at line 1
#|/tmp/* ~ /tmp/: False
#|/tmp/** ~ /tmp/a/b: True
#|/a/{b,c{d,e}}/* ~ /a/cd/x: True
#|/a/[^b]c ~ /a//c: True
#|/a/**/b/**/c/**/d/**/e* ~ /a/1/2/b/3/c/4/5/d/6/7/8/f/9/x/y/z/w/v/u/t/s/r/q/p/o/n/m/l: False
#|big: ok, 1 profiles
#|allow
#|deny-quiet
#|deny
#|allow
