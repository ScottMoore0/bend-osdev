# DRAFT: not yet reviewed by the maintainer
#
# Properties, for every input (every kernel parameter record, credential,
# file and request):
#   execve: the effective set ends within the permitted set, and the ambient
#     set within the permitted set and (when it was before) the inheritable
#     set; the bounding and inheritable sets are unchanged; the new permitted
#     set is within the old bounding, inheritable and ambient sets (so a
#     capability in none of them never becomes permitted); the documented
#     root and non-root simplifications; execve answers either
#     CapsCapabilityDumb or exactly the transformed sets.
#   capset: the permitted set never grows, the bounding set is unchanged, and
#     the invariants (effective within permitted, ambient within permitted
#     and inheritable) hold afterwards.
#   PR_CAPBSET_DROP: the bounding set never grows, and nothing else changes.
#   PR_CAP_AMBIENT: raising and lowering keep the invariants and change no
#   other set; clearing empties the ambient set.
#
# Vectors: capability names and numbers, the text form of a set, and the
# documented cases of capabilities(7) on concrete credentials.
import Base
import ./caps.bend as C
import ./exec.bend as E
import ./adjust.bend as A

# execve(2)

law execve_result:
  for +k: C.CapsKernel
  for +c: C.CapCred
  for +f: C.CapFile
  for +ign: Bool
  {C.Caps.sets_or(E.Caps.execve(k, c, f, ign), E.Caps.execve.sets(k, c, f, ign)) == E.Caps.execve.sets(k, c, f, ign) : C.CapState}

law execve_effective_within_permitted:
  for +k: C.CapsKernel
  for +c: C.CapCred
  for +f: C.CapFile
  for +ign: Bool
  {C.CapSet.subset(C.CapState.effective(E.Caps.execve.sets(k, c, f, ign)), C.CapState.permitted(E.Caps.execve.sets(k, c, f, ign))) == True{} : Bool}

law execve_ambient_within_permitted:
  for +k: C.CapsKernel
  for +c: C.CapCred
  for +f: C.CapFile
  for +ign: Bool
  {C.CapSet.subset(C.CapState.ambient(E.Caps.execve.sets(k, c, f, ign)), C.CapState.permitted(E.Caps.execve.sets(k, c, f, ign))) == True{} : Bool}

law execve_ambient_within_inheritable:
  for +k: C.CapsKernel
  for +c: C.CapCred
  for +f: C.CapFile
  for +ign: Bool
  for h: {C.CapSet.subset(C.CapState.ambient(C.CapCred.sets(c)), C.CapState.inheritable(C.CapCred.sets(c))) == True{} : Bool}
  {C.CapSet.subset(C.CapState.ambient(E.Caps.execve.sets(k, c, f, ign)), C.CapState.inheritable(E.Caps.execve.sets(k, c, f, ign))) == True{} : Bool}

law execve_valid:
  for +k: C.CapsKernel
  for +c: C.CapCred
  for +f: C.CapFile
  for +ign: Bool
  for h: {C.CapState.valid(C.CapCred.sets(c)) == True{} : Bool}
  {C.CapState.valid(E.Caps.execve.sets(k, c, f, ign)) == True{} : Bool}

law execve_bounding_unchanged:
  for +k: C.CapsKernel
  for +c: C.CapCred
  for +f: C.CapFile
  for +ign: Bool
  {C.CapState.bounding(E.Caps.execve.sets(k, c, f, ign)) == C.CapState.bounding(C.CapCred.sets(c)) : C.CapSet()}

law execve_inheritable_unchanged:
  for +k: C.CapsKernel
  for +c: C.CapCred
  for +f: C.CapFile
  for +ign: Bool
  {C.CapState.inheritable(E.Caps.execve.sets(k, c, f, ign)) == C.CapState.inheritable(C.CapCred.sets(c)) : C.CapSet()}

# a capability that is in none of the bounding, inheritable and ambient sets
# never becomes permitted (the bounding set does not mask the inheritable
# set: capabilities(7), "Capability bounding set")
law execve_permitted_bounded:
  for +k: C.CapsKernel
  for +c: C.CapCred
  for +f: C.CapFile
  for +ign: Bool
  {C.CapSet.subset(C.CapState.permitted(E.Caps.execve.sets(k, c, f, ign)), C.CapSet.union(C.CapState.bounding(C.CapCred.sets(c)), C.CapSet.union(C.CapState.inheritable(C.CapCred.sets(c)), C.CapState.ambient(C.CapCred.sets(c))))) == True{} : Bool}

# with the ambient invariant, the bound is the bounding and inheritable sets
law execve_permitted_bounded_valid:
  for +k: C.CapsKernel
  for +c: C.CapCred
  for +f: C.CapFile
  for +ign: Bool
  for h: {C.CapSet.subset(C.CapState.ambient(C.CapCred.sets(c)), C.CapState.inheritable(C.CapCred.sets(c))) == True{} : Bool}
  {C.CapSet.subset(C.CapState.permitted(E.Caps.execve.sets(k, c, f, ign)), C.CapSet.union(C.CapState.bounding(C.CapCred.sets(c)), C.CapState.inheritable(C.CapCred.sets(c)))) == True{} : Bool}

# "when a process whose real and effective UIDs are zero execve(2)s a
# program": P'(permitted) = P(inheritable) | P(bounding), and
# P'(effective) = P'(permitted). For every state with the ambient invariant,
# every file that is not set-user-ID, without SECBIT_NOROOT.
law execve_root_permitted:
  for +k: C.CapsKernel
  for +s: C.CapState
  for +sv: U32
  for +na: Bool
  for +u: U32
  for +sg: Bool
  for +fc: Maybe<&2, C.CapFileSets>
  for +ign: Bool
  for h: {C.CapSet.subset(C.CapState.ambient(s), C.CapState.inheritable(s)) == True{} : Bool}
  {C.CapState.permitted(E.Caps.execve.sets(k, C.CapCred{0, 0, sv, False{}, na, s}, C.CapFile{u, False{}, sg, fc}, ign)) == C.CapSet.union(C.CapState.inheritable(s), C.CapState.bounding(s)) : C.CapSet()}

law execve_root_effective:
  for +k: C.CapsKernel
  for +s: C.CapState
  for +sv: U32
  for +na: Bool
  for +u: U32
  for +sg: Bool
  for +fc: Maybe<&2, C.CapFileSets>
  for +ign: Bool
  for h: {C.CapSet.subset(C.CapState.ambient(s), C.CapState.inheritable(s)) == True{} : Bool}
  {C.CapState.effective(E.Caps.execve.sets(k, C.CapCred{0, 0, sv, False{}, na, s}, C.CapFile{u, False{}, sg, fc}, ign)) == C.CapSet.union(C.CapState.inheritable(s), C.CapState.bounding(s)) : C.CapSet()}

# "if a process with nonzero user IDs performs an execve(2) then any
# capabilities that are present in its permitted and effective sets will be
# cleared": of a file without set-ID bits or capabilities, only the ambient
# set remains, as both permitted and effective.
law execve_nonroot_permitted:
  for +k: C.CapsKernel
  for +r: U32
  for +e: U32
  for hr: {U32.is_eq(r, 0) == False{} : Bool}
  for he: {U32.is_eq(e, 0) == False{} : Bool}
  for +s: C.CapState
  for +sv: U32
  for +nr: Bool
  for +na: Bool
  for +u: U32
  for +ign: Bool
  {C.CapState.permitted(E.Caps.execve.sets(k, C.CapCred{r, e, sv, nr, na, s}, C.CapFile{u, False{}, False{}, None{}}, ign)) == C.CapState.ambient(s) : C.CapSet()}

law execve_nonroot_effective:
  for +k: C.CapsKernel
  for +r: U32
  for +e: U32
  for hr: {U32.is_eq(r, 0) == False{} : Bool}
  for he: {U32.is_eq(e, 0) == False{} : Bool}
  for +s: C.CapState
  for +sv: U32
  for +nr: Bool
  for +na: Bool
  for +u: U32
  for +ign: Bool
  {C.CapState.effective(E.Caps.execve.sets(k, C.CapCred{r, e, sv, nr, na, s}, C.CapFile{u, False{}, False{}, None{}}, ign)) == C.CapState.ambient(s) : C.CapSet()}

# capset(2)

law capset_permitted_never_grows:
  for +c: C.CapCred
  for +e: C.CapSet()
  for +p: C.CapSet()
  for +i: C.CapSet()
  {C.CapSet.subset(C.CapState.permitted(C.CapCred.sets(C.Caps.or(A.Caps.capset(c, e, p, i), c))), C.CapState.permitted(C.CapCred.sets(c))) == True{} : Bool}

law capset_bounding_unchanged:
  for +c: C.CapCred
  for +e: C.CapSet()
  for +p: C.CapSet()
  for +i: C.CapSet()
  {C.CapState.bounding(C.CapCred.sets(C.Caps.or(A.Caps.capset(c, e, p, i), c))) == C.CapState.bounding(C.CapCred.sets(c)) : C.CapSet()}

law capset_valid:
  for +c: C.CapCred
  for +e: C.CapSet()
  for +p: C.CapSet()
  for +i: C.CapSet()
  for h: {C.CapState.valid(C.CapCred.sets(c)) == True{} : Bool}
  {C.CapState.valid(C.CapCred.sets(C.Caps.or(A.Caps.capset(c, e, p, i), c))) == True{} : Bool}

# prctl(2) PR_CAPBSET_DROP

law bset_drop_never_grows:
  for +k: C.CapsKernel
  for +c: C.CapCred
  for +x: U32
  {C.CapSet.subset(C.CapState.bounding(C.CapCred.sets(C.Caps.or(A.Caps.bset_drop(k, c, x), c))), C.CapState.bounding(C.CapCred.sets(c))) == True{} : Bool}

# dropping from the bounding set changes no other set (in particular, not the
# inheritable set)
law bset_drop_rest_unchanged:
  for +k: C.CapsKernel
  for +c: C.CapCred
  for +x: U32
  {C.CapState.with_bounding(C.CapCred.sets(C.Caps.or(A.Caps.bset_drop(k, c, x), c)), C.CapSet.empty()) == C.CapState.with_bounding(C.CapCred.sets(c), C.CapSet.empty()) : C.CapState}

# prctl(2) PR_CAP_AMBIENT

law ambient_raise_valid:
  for +k: C.CapsKernel
  for +c: C.CapCred
  for +x: U32
  for h: {C.CapState.valid(C.CapCred.sets(c)) == True{} : Bool}
  {C.CapState.valid(C.CapCred.sets(C.Caps.or(A.Caps.ambient_raise(k, c, x), c))) == True{} : Bool}

law ambient_lower_valid:
  for +k: C.CapsKernel
  for +c: C.CapCred
  for +x: U32
  for h: {C.CapState.valid(C.CapCred.sets(c)) == True{} : Bool}
  {C.CapState.valid(C.CapCred.sets(C.Caps.or(A.Caps.ambient_lower(k, c, x), c))) == True{} : Bool}

law ambient_raise_rest_unchanged:
  for +k: C.CapsKernel
  for +c: C.CapCred
  for +x: U32
  {C.CapState.with_ambient(C.CapCred.sets(C.Caps.or(A.Caps.ambient_raise(k, c, x), c)), C.CapSet.empty()) == C.CapState.with_ambient(C.CapCred.sets(c), C.CapSet.empty()) : C.CapState}

law ambient_lower_rest_unchanged:
  for +k: C.CapsKernel
  for +c: C.CapCred
  for +x: U32
  {C.CapState.with_ambient(C.CapCred.sets(C.Caps.or(A.Caps.ambient_lower(k, c, x), c)), C.CapSet.empty()) == C.CapState.with_ambient(C.CapCred.sets(c), C.CapSet.empty()) : C.CapState}

law ambient_clear_all_empty:
  for +c: C.CapCred
  {C.CapState.ambient(C.CapCred.sets(A.Caps.ambient_clear_all(c))) == C.CapSet.empty() : C.CapSet()}

# Vectors

law name_first:
  {C.Cap.name(0) == Some{"CAP_CHOWN"} : Maybe<&2, String>}

law name_last:
  {C.Cap.name(40) == Some{"CAP_CHECKPOINT_RESTORE"} : Maybe<&2, String>}

law name_beyond:
  {C.Cap.name(41) == None{} : Maybe<&2, String>}

law of_name_sys_admin:
  {C.Cap.of_name("CAP_SYS_ADMIN") == Some{21} : Maybe<&2, U32>}

# the full set, as /proc/<pid>/status shows it on Linux 5.9 and later
law show_full:
  {C.CapSet.show(C.CapSet.full()) == "000001ffffffffff" : String}

# CAP_NET_RAW (13) and CAP_NET_BIND_SERVICE (10): 0x2400
law show_two:
  {C.CapSet.show(C.CapSet.from_list([13, 10])) == "0000000000002400" : String}

# A capability-dumb binary (cap_net_raw=ep) run by a non-root user whose
# bounding set lacks CAP_NET_RAW: execve fails with EPERM.
law vector_dumb_binary:
  {E.Caps.execve(C.CapsKernel.linux(), C.CapCred{1000, 1000, 1000, False{}, False{}, C.CapState{C.CapSet.empty(), C.CapSet.empty(), C.CapSet.empty(), C.CapSet.del(C.CapSet.full(), 13), C.CapSet.empty()}}, C.CapFile{0, False{}, False{}, Some{C.CapFileSets{C.CapSet.of(13), C.CapSet.empty(), True{}}}}, False{}) == Fail{C.CapsCapabilityDumb{}} : Result<&2, &2, C.CapsError, C.CapCred>}

# A set-user-ID-root program with file capabilities (cap_net_bind_service=ep)
# run by user 1000: the effective and saved UIDs become 0, and the process
# gains just the file's capabilities.
law vector_suid_root_with_caps:
  {E.Caps.execve(C.CapsKernel.linux(), C.CapCred{1000, 1000, 1000, False{}, False{}, C.CapState{C.CapSet.empty(), C.CapSet.empty(), C.CapSet.empty(), C.CapSet.full(), C.CapSet.empty()}}, C.CapFile{0, True{}, False{}, Some{C.CapFileSets{C.CapSet.of(10), C.CapSet.empty(), True{}}}}, False{}) == Done{C.CapCred{1000, 0, 0, False{}, False{}, C.CapState{C.CapSet.of(10), C.CapSet.empty(), C.CapSet.of(10), C.CapSet.full(), C.CapSet.empty()}}} : Result<&2, &2, C.CapsError, C.CapCred>}

# The same program without file capabilities gains every capability in the
# bounding set.
law vector_suid_root_plain:
  {E.Caps.execve(C.CapsKernel.linux(), C.CapCred{1000, 1000, 1000, False{}, False{}, C.CapState{C.CapSet.empty(), C.CapSet.empty(), C.CapSet.empty(), C.CapSet.del(C.CapSet.full(), 21), C.CapSet.empty()}}, C.CapFile{0, True{}, False{}, None{}}, False{}) == Done{C.CapCred{1000, 0, 0, False{}, False{}, C.CapState{C.CapSet.del(C.CapSet.full(), 21), C.CapSet.empty(), C.CapSet.del(C.CapSet.full(), 21), C.CapSet.del(C.CapSet.full(), 21), C.CapSet.empty()}}} : Result<&2, &2, C.CapsError, C.CapCred>}

# With no_new_privs (ign), the set-user-ID bit is ignored: nothing is gained.
law vector_suid_ignored:
  {E.Caps.execve(C.CapsKernel.linux(), C.CapCred{1000, 1000, 1000, False{}, False{}, C.CapState{C.CapSet.empty(), C.CapSet.empty(), C.CapSet.empty(), C.CapSet.full(), C.CapSet.empty()}}, C.CapFile{0, True{}, False{}, None{}}, True{}) == Done{C.CapCred{1000, 1000, 1000, False{}, False{}, C.CapState{C.CapSet.empty(), C.CapSet.empty(), C.CapSet.empty(), C.CapSet.full(), C.CapSet.empty()}}} : Result<&2, &2, C.CapsError, C.CapCred>}

# capset may not add to the permitted set
law vector_capset_grows:
  {A.Caps.capset(C.CapCred{1000, 1000, 1000, False{}, False{}, C.CapState{C.CapSet.of(13), C.CapSet.empty(), C.CapSet.empty(), C.CapSet.full(), C.CapSet.empty()}}, C.CapSet.empty(), C.CapSet.from_list([13, 12]), C.CapSet.empty()) == Fail{C.CapsPermittedGrows{}} : Result<&2, &2, C.CapsError, C.CapCred>}

# an ambient capability must be permitted and inheritable
law vector_ambient_not_inheritable:
  {A.Caps.ambient_raise(C.CapsKernel.linux(), C.CapCred{1000, 1000, 1000, False{}, False{}, C.CapState{C.CapSet.of(13), C.CapSet.empty(), C.CapSet.empty(), C.CapSet.full(), C.CapSet.empty()}}, 13) == Fail{C.CapsAmbientNotAllowed{}} : Result<&2, &2, C.CapsError, C.CapCred>}

# 41 is beyond CAP_CHECKPOINT_RESTORE
law vector_drop_invalid:
  {A.Caps.bset_drop(C.CapsKernel.linux(), C.CapCred{0, 0, 0, False{}, False{}, C.CapState{C.CapSet.full(), C.CapSet.empty(), C.CapSet.full(), C.CapSet.full(), C.CapSet.empty()}}, 41) == Fail{C.CapsInvalidCap{}} : Result<&2, &2, C.CapsError, C.CapCred>}

# Witnesses: every hypothesis of the laws above holds for some input, so no
# law is vacuous. A valid state with a nonempty ambient set (CAP_NET_BIND_
# SERVICE permitted, inheritable and ambient; CAP_NET_RAW permitted and
# effective):
law witness_valid:
  {C.CapState.valid(C.CapCred.sets(C.CapCred{1000, 1000, 1000, False{}, False{}, C.CapState{C.CapSet.from_list([10, 13]), C.CapSet.of(10), C.CapSet.of(13), C.CapSet.full(), C.CapSet.of(10)}})) == True{} : Bool}

# ambient within inheritable, for a credential's sets and for a state
law witness_ambient_inheritable:
  {C.CapSet.subset(C.CapState.ambient(C.CapCred.sets(C.CapCred{1000, 1000, 1000, False{}, False{}, C.CapState{C.CapSet.from_list([10, 13]), C.CapSet.of(10), C.CapSet.of(13), C.CapSet.full(), C.CapSet.of(10)}})), C.CapState.inheritable(C.CapCred.sets(C.CapCred{1000, 1000, 1000, False{}, False{}, C.CapState{C.CapSet.from_list([10, 13]), C.CapSet.of(10), C.CapSet.of(13), C.CapSet.full(), C.CapSet.of(10)}}))) == True{} : Bool}

law witness_ambient_inheritable_state:
  {C.CapSet.subset(C.CapState.ambient(C.CapState{C.CapSet.of(10), C.CapSet.of(10), C.CapSet.empty(), C.CapSet.full(), C.CapSet.of(10)}), C.CapState.inheritable(C.CapState{C.CapSet.of(10), C.CapSet.of(10), C.CapSet.empty(), C.CapSet.full(), C.CapSet.of(10)})) == True{} : Bool}

# a nonzero user ID (the non-root laws' hypotheses on the real and effective
# user IDs)
law witness_nonzero_uid:
  {U32.is_eq(1000, 0) == False{} : Bool}
