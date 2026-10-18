# bend-osdev-selinux: example policies.
#
# SeExample.policy() is a small policy built directly in the model (no CIL),
# so that laws can name inputs that satisfy their hypotheses; SeExample.cil()
# is a small policy in CIL, for check.bend and as a starting point.
#
# The model policy: types a_t (0), b_t (1) and the attribute dom_a (2,
# members a_t); classes file (0: read, write) and process (1: fork,
# transition); roles object_r (0) and r_r (1); user u_u (0); boolean flag
# (0, false); MLS on, sensitivities s0 < s1, category c0.
#   allow a_t b_t file read             neverallow a_t b_t file write
#   dontaudit a_t b_t file write        auditallow a_t b_t file read
#   booleanif flag: allow a_t self file write
#   typetransition a_t b_t file a_t     typetransition a_t b_t process b_t
#   constrain file read (eq u1 u2)      mlsconstrain file (read write) (dom l1 l2)
#   typepermissive b_t
import Base
import ./bits.bend as Bits
import ./mls.bend as M
import ./contexts.bend as C
import ./constraints.bend as K
import ./policy.bend as P

def SeExample.s0() -> M.SeLevel:
  M.SeLevel{0n, Nil{}}

def SeExample.s1() -> M.SeLevel:
  M.SeLevel{1n, Nil{}}

def SeExample.syms() -> Map<&2, P.SeSym>:
  Map.set(&2, P.SeSym, Map.set(&2, P.SeSym, Map.set(&2, P.SeSym, Map.set(&2, P.SeSym, Map.new(&2, P.SeSym), "t:a_t", P.SeSymId{0n}), "t:b_t", P.SeSymId{1n}), "c:file", P.SeSymId{0n}), "c:process", P.SeSymId{1n})

def SeExample.decl() -> P.SeDecl:
  P.SeDecl{[P.SeTypeDef{"a_t", False{}, [True{}]}, P.SeTypeDef{"b_t", False{}, [False{}, True{}]}, P.SeTypeDef{"dom_a", True{}, [True{}]}], [P.SeRole{"object_r", [True{}, True{}]}, P.SeRole{"r_r", [True{}, True{}]}], [P.SeUser{"u_u", [False{}, True{}], SeExample.s0(), M.SeRange{SeExample.s0(), SeExample.s1()}}], [P.SeClass{"file", ["read", "write"]}, P.SeClass{"process", ["fork", "transition"]}], ["flag"], ["s0", "s1"], ["c0"], [[True{}], [True{}]], SeExample.syms(), Nil{}}

def SeExample.rules() -> P.SeRules:
  P.SeRules{[P.SeAvRule{P.SeAllow{}, [True{}], [False{}, True{}], False{}, 0n, [True{}]}, P.SeAvRule{P.SeNeverallow{}, [True{}], [False{}, True{}], False{}, 0n, [False{}, True{}]}, P.SeAvRule{P.SeDontaudit{}, [True{}], [False{}, True{}], False{}, 0n, [False{}, True{}]}, P.SeAvRule{P.SeAuditallow{}, [True{}], [False{}, True{}], False{}, 0n, [True{}]}], [P.SeTyRule{P.SeTyTransition{}, [True{}], [False{}, True{}], False{}, 0n, None{}, 0n}, P.SeTyRule{P.SeTyTransition{}, [True{}], [False{}, True{}], False{}, 1n, None{}, 1n}], [P.SeCond{P.SeBVar{0n}, [P.SeAvRule{P.SeAllow{}, [True{}], Nil{}, True{}, 0n, [False{}, True{}]}], Nil{}, Nil{}, Nil{}}], Nil{}, Nil{}, [K.SeConstraint{False{}, 0n, [True{}], K.SeCPair{K.SeCUser{}, True{}}}, K.SeConstraint{True{}, 0n, [True{}, True{}], K.SeCLevel{K.SeLDom{}, K.SeL1{}, K.SeL2{}}}], [False{}, True{}]}

# the model policy, booleans at their defaults
def SeExample.policy() -> P.SePolicy:
  P.SePolicy{SeExample.decl(), SeExample.rules(), True{}, Nil{}}

# u_u:r_r:a_t:s0
def SeExample.source() -> C.SeContext:
  C.SeContext{0n, 1n, 0n, M.SeRange{SeExample.s0(), SeExample.s0()}}

# u_u:object_r:b_t:s0
def SeExample.target() -> C.SeContext:
  C.SeContext{0n, 0n, 1n, M.SeRange{SeExample.s0(), SeExample.s0()}}

# u_u:r_r:b_t:s0, a process of the permissive type b_t
def SeExample.permissive_source() -> C.SeContext:
  C.SeContext{0n, 1n, 1n, M.SeRange{SeExample.s0(), SeExample.s0()}}

# A policy in CIL: a user's shell, the files it reads, a passwd program it
# runs, a boolean that lets it write /etc, MLS read-down, and a neverallow
def SeExample.cil() -> String:
  "; bend-osdev-selinux example policy
(class process (fork transition))
(common file_common (read write getattr))
(class file (execute entrypoint create))
(classcommon file file_common)
(classorder (process file))
(sid kernel)
(sidorder (kernel))
(sensitivity s0)
(sensitivity s1)
(sensitivityorder (s0 s1))
(category c0)
(category c1)
(category c2)
(categoryorder (c0 c1 c2))
(sensitivitycategory s0 (range c0 c2))
(sensitivitycategory s1 (range c0 c2))
(mls true)
(type user_t)
(type passwd_t)
(type etc_t)
(type shadow_t)
(type bin_t)
(typealias shell_t)
(typealiasactual shell_t user_t)
(typeattribute domain)
(typeattribute file_type)
(typeattributeset domain (user_t passwd_t))
(typeattributeset file_type (and (all) (not domain)))
(role user_r)
(role passwd_r)
(roletype user_r domain)
(roletype passwd_r passwd_t)
(roleallow user_r passwd_r)
(roletransition user_r bin_t process passwd_r)
(roletype object_r file_type)
(user user_u)
(userrole user_u user_r)
(userrole user_u passwd_r)
(userlevel user_u (s0))
(userrange user_u ((s0) (s1 (range c0 c2))))
(sidcontext kernel (user_u object_r etc_t ((s0) (s0))))
(boolean allow_etc_write false)
(allow domain etc_t (file (read getattr)))
(allow domain self (process (fork)))
(allow user_t bin_t (file (read execute)))
(allow user_t passwd_t (process (transition)))
(allow passwd_t bin_t (file (entrypoint)))
(allow passwd_t shadow_t (file (read write)))
(auditallow passwd_t shadow_t (file (write)))
(dontaudit user_t shadow_t (file (read getattr)))
(booleanif allow_etc_write
  (true (allow user_t etc_t (file (write create)))
        (typetransition user_t bin_t file etc_t))
  (false (typetransition user_t bin_t file shadow_t)))
(typetransition user_t etc_t file \"passwd\" shadow_t)
(typetransition user_t bin_t process passwd_t)
(typetransition passwd_t etc_t file shadow_t)
(typechange passwd_t etc_t file shadow_t)
(typemember user_t etc_t file bin_t)
(constrain (file (write)) (or (eq u1 u2) (eq t1 passwd_t)))
(mlsconstrain (file (read)) (dom l1 l2))
(mlsconstrain (file (write)) (domby l1 l2))
(neverallow user_t shadow_t (file (read write)))
(typepermissive bin_t)
"
