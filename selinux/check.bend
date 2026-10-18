import Base
import ./bits.bend as Bits
import ./mls.bend as M
import ./contexts.bend as C
import ./policy.bend as P
import ./te.bend as T
import ./avc.bend as A
import ./example.bend as X
import ./selinux.bend as S

def SeChk.show_avd(+p: P.SePolicy, +cls: String, r: Result<&2, &2, P.SeError, A.SeAvd>) -> String:
  match r:
    case Fail{e}:
      S.SeError.show(e)
    case Done{v}:
      match v:
        case A.SeAvd{a, aa, ad}:
          +c = Result.default(&2, &2, P.SeError, Nat, S.Selinux.class(p, cls), 0n)
          "allowed " ++ S.Selinux.perms_show(p, c, a) ++ " auditallow " ++ S.Selinux.perms_show(p, c, aa) ++ " auditdeny " ++ S.Selinux.perms_show(p, c, ad)

def SeChk.av(+p: P.SePolicy, s: String, t: String, +cls: String) -> String:
  SeChk.show_avd(p, cls, S.Selinux.compute_av(p, s, t, cls))

def SeChk.show_dec(r: Result<&2, &2, P.SeError, A.SeDecision>) -> String:
  match r:
    case Fail{e}:
      S.SeError.show(e)
    case Done{d}:
      match d:
        case A.SeDecision{g, dn, au}:
          "granted " ++ Bool.show(g) ++ " denied " ++ Bool.show(dn) ++ " audited " ++ Bool.show(au)

def SeChk.show_str(r: Result<&2, &2, P.SeError, String>) -> String:
  match r:
    case Fail{e}:
      S.SeError.show(e)
    case Done{x}:
      x

def SeChk.show_load(r: Result<&2, &2, P.SeError, P.SePolicy>) -> String:
  match r:
    case Fail{e}:
      S.SeError.show(e)
    case Done{p}:
      "loaded"

def SeChk.valid.go(+p: P.SePolicy, r: Result<&2, &2, P.SeError, C.SeContext>) -> String:
  match r:
    case Fail{e}:
      S.SeError.show(e)
    case Done{c}:
      Bool.show(P.SePolicy.context_valid(p, c))

def SeChk.valid(+p: P.SePolicy, s: String) -> String:
  SeChk.valid.go(p, S.Selinux.context(p, s))

def SeChk.names(+p: P.SePolicy, xs: List<&2, Nat>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{i, t}:
      Con{P.SePolicy.type_name(p, i), SeChk.names(p, t)}

def SeChk.members.go(+p: P.SePolicy, m: Maybe<&2, P.SeTypeDef>) -> String:
  match m:
    case None{}:
      "?"
    case Some{d}:
      String.join(SeChk.names(p, Bits.SeBits.to_list(P.SeTypeDef.members(d))), " ")

# the members of an attribute
def SeChk.members(+p: P.SePolicy, name: String) -> String:
  SeChk.members.go(p, P.SeTypeDef.find(P.SeDecl.types(P.SePolicy.decl(p)), Maybe.default(&2, Nat, P.SePolicy.lookup(p, "t:" ++ name), 0n)))

def SeChk.run(+p: P.SePolicy, +q: P.SePolicy) -> IO(Unit):
  do IO<Unit>:
    IO.print(SeChk.av(p, "user_u:user_r:user_t:s0", "user_u:object_r:etc_t:s0", "file"))
    IO.print(SeChk.av(q, "user_u:user_r:user_t:s0", "user_u:object_r:etc_t:s0", "file"))
    IO.print(SeChk.av(p, "user_u:user_r:shell_t:s0", "user_u:object_r:bin_t:s0", "file"))
    IO.print(SeChk.av(p, "user_u:user_r:user_t:s0", "user_u:object_r:shadow_t:s0", "file"))
    IO.print(SeChk.av(p, "user_u:passwd_r:passwd_t:s0", "user_u:object_r:shadow_t:s1:c0", "file"))
    IO.print(SeChk.av(p, "user_u:passwd_r:passwd_t:s1:c0.c2", "user_u:object_r:shadow_t:s0:c1", "file"))
    IO.print(SeChk.av(p, "user_u:user_r:user_t:s0", "user_u:user_r:user_t:s0", "process"))
    IO.print(SeChk.av(p, "user_u:user_r:user_t:s0", "user_u:user_r:passwd_t:s0", "process"))
    IO.print(SeChk.show_str(S.Selinux.create(p, "user_u:user_r:user_t:s0-s1:c0.c2", "user_u:object_r:bin_t:s0", "process", None{})))
    IO.print(SeChk.show_str(S.Selinux.create(p, "user_u:passwd_r:passwd_t:s0-s1:c0,c2", "user_u:object_r:etc_t:s0", "file", None{})))
    IO.print(SeChk.show_str(S.Selinux.create(p, "user_u:user_r:user_t:s0", "user_u:object_r:etc_t:s0", "file", Some{"passwd"})))
    IO.print(SeChk.show_str(S.Selinux.create(q, "user_u:user_r:user_t:s0", "user_u:object_r:etc_t:s0", "file", Some{"passwd"})))
    IO.print(SeChk.show_str(S.Selinux.create(q, "user_u:user_r:user_t:s0", "user_u:object_r:etc_t:s0", "file", Some{"group"})))
    IO.print(SeChk.show_str(S.Selinux.create(p, "user_u:user_r:user_t:s0", "user_u:object_r:bin_t:s0", "file", None{})))
    IO.print(SeChk.show_str(S.Selinux.create(q, "user_u:user_r:user_t:s0", "user_u:object_r:bin_t:s0", "file", None{})))
    IO.print(SeChk.show_dec(S.Selinux.check(A.SeOptions.default(), p, "user_u:user_r:user_t:s0", "user_u:object_r:etc_t:s0", "file", ["read"])))
    IO.print(SeChk.show_dec(S.Selinux.check(A.SeOptions.default(), p, "user_u:user_r:user_t:s0", "user_u:object_r:etc_t:s0", "file", ["read", "write"])))
    IO.print(SeChk.show_dec(S.Selinux.check(A.SeOptions.permissive(), p, "user_u:user_r:user_t:s0", "user_u:object_r:etc_t:s0", "file", ["write"])))
    IO.print(SeChk.show_dec(S.Selinux.check(A.SeOptions.default(), p, "user_u:user_r:user_t:s0", "user_u:object_r:shadow_t:s0", "file", ["read"])))
    IO.print(SeChk.show_dec(S.Selinux.check(A.SeOptions.default(), p, "user_u:object_r:bin_t:s0", "user_u:object_r:etc_t:s0", "file", ["write"])))
    IO.print(SeChk.show_dec(S.Selinux.check(A.SeOptions{True{}, False{}}, p, "user_u:object_r:bin_t:s0", "user_u:object_r:etc_t:s0", "file", ["write"])))
    IO.print(SeChk.valid(p, "user_u:user_r:user_t:s0-s1:c0"))
    IO.print(SeChk.valid(p, "user_u:user_r:etc_t:s0"))
    IO.print(SeChk.valid(p, "user_u:passwd_r:passwd_t:s1:c0"))
    IO.print(SeChk.valid(p, "user_u:user_r:nosuch_t:s0"))
    IO.print(Bool.show(T.SeTe.role_allowed(p, 1n, 2n)) ++ " " ++ Bool.show(T.SeTe.role_allowed(p, 2n, 1n)))
    IO.print(S.Selinux.context_show(p, A.SeAvc.compute_relabel(p, C.SeContext{0n, 2n, 1n, M.SeRange{M.SeLevel{0n, Nil{}}, M.SeLevel{0n, Nil{}}}}, C.SeContext{0n, 0n, 2n, M.SeRange{M.SeLevel{0n, Nil{}}, M.SeLevel{0n, Nil{}}}}, 1n)))
    IO.print(SeChk.members(p, "domain") ++ " / " ++ SeChk.members(p, "file_type"))

def SeChk.top(r: Result<&2, &2, P.SeError, P.SePolicy>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(S.SeError.show(e))
    case Done{+p}:
      SeChk.run(p, Result.default(&2, &2, P.SeError, P.SePolicy, S.Selinux.set_bool(p, "allow_etc_write", True{}), p))

def main() -> IO(Unit):
  +ex = X.SeExample.cil()
  do IO<Unit>:
    IO.print(SeChk.show_load(S.Selinux.load_string(ex ++ "(allow user_t shadow_t (file (write)))")))
    IO.print(SeChk.show_load(S.Selinux.load_string(ex ++ "(booleanif allow_etc_write (false (allow user_t shadow_t (file (read)))))")))
    IO.print(SeChk.show_load(S.Selinux.load_string(ex ++ "(allow user_t nosuch_t (file (read)))")))
    IO.print(SeChk.show_load(S.Selinux.load_string(ex ++ "(allow user_t etc_t (file (fly)))")))
    IO.print(SeChk.show_load(S.Selinux.load_string(ex ++ "(frobnicate x)")))
    IO.print(SeChk.show_load(S.Selinux.load_string(ex ++ "(macro m ())")))
    IO.print(SeChk.show_load(S.Selinux.load_string(ex ++ "(type user_t)")))
    IO.print(SeChk.show_load(S.Selinux.load_string(ex ++ "(allow user_t etc_t (file (read))")))
    IO.print(SeChk.show_load(S.Selinux.load_string("(typeattribute a) (typeattribute b) (typeattributeset a (b)) (typeattributeset b (a))")))
    IO.print(SeChk.show_load(S.Selinux.load_string(ex ++ "(constrain (file (read)) (eq t2 t1))")))
    IO.print(SeChk.show_load(S.Selinux.load_string(ex ++ "(constrain (file (read)) (eq t1 t2))")))
    IO.print(SeChk.show_load(S.Selinux.load_string(ex ++ "(booleanif allow_etc_write (false (typetransition user_t shadow_t file \"x\" etc_t)))")))
    IO.print(SeChk.show_load(S.Selinux.load_string(ex ++ "(typetransition domain etc_t file bin_t)")))
    IO.print(SeChk.show_load(S.Selinux.load_string(ex ++ "(booleanif allow_etc_write (true (typetransition user_t bin_t file shadow_t)))")))
    IO.print(SeChk.show_load(S.Selinux.load_string(ex ++ "(roletransition user_r bin_t process user_r)")))
    SeChk.top(S.Selinux.load_string(ex))

#|neverallow violated
#|neverallow violated
#|undeclared: t:nosuch_t
#|undeclared: p:file:fly
#|unknown statement: frobnicate
#|unsupported: macro
#|duplicate: t:user_t
#|syntax: unbalanced (
#|attribute cycle: typeattributeset
#|bad statement: constraint operand t1
#|loaded
#|bad statement: booleanif: typetransition with an object name
#|type rule conflict
#|type rule conflict
#|role transition conflict
#|allowed { read getattr } auditallow { } auditdeny { read write getattr execute entrypoint create }
#|allowed { read write getattr create } auditallow { } auditdeny { read write getattr execute entrypoint create }
#|allowed { read execute } auditallow { } auditdeny { read write getattr execute entrypoint create }
#|allowed { } auditallow { } auditdeny { write execute entrypoint create }
#|allowed { write } auditallow { write } auditdeny { read write getattr execute entrypoint create }
#|allowed { read } auditallow { write } auditdeny { read write getattr execute entrypoint create }
#|allowed { fork } auditallow { } auditdeny { fork transition }
#|allowed { transition } auditallow { } auditdeny { fork transition }
#|user_u:passwd_r:passwd_t:s0-s1:c0,c1,c2
#|user_u:object_r:shadow_t:s0
#|user_u:object_r:shadow_t:s0
#|user_u:object_r:shadow_t:s0
#|user_u:object_r:etc_t:s0
#|user_u:object_r:shadow_t:s0
#|user_u:object_r:etc_t:s0
#|granted True denied False audited False
#|granted False denied True audited True
#|granted True denied True audited True
#|granted False denied True audited False
#|granted True denied True audited True
#|granted False denied True audited True
#|True
#|False
#|True
#|undeclared: t:nosuch_t
#|True False
#|user_u:object_r:shadow_t:s0
#|user_t passwd_t / etc_t shadow_t bin_t
