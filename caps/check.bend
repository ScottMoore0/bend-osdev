import Base
import ./caps.bend as C
import ./exec.bend as E
import ./adjust.bend as A

def show_err(e: C.CapsError) -> String:
  match e:
    case C.CapsInvalidCap{}:
      "EINVAL invalid capability"
    case C.CapsPermittedGrows{}:
      "EPERM permitted set grows"
    case C.CapsEffectiveNotPermitted{}:
      "EPERM effective not permitted"
    case C.CapsInheritableNotBounded{}:
      "EPERM inheritable not bounded"
    case C.CapsInheritableNotPermitted{}:
      "EPERM inheritable not permitted"
    case C.CapsNoSetpcap{}:
      "EPERM no CAP_SETPCAP"
    case C.CapsAmbientRaiseLocked{}:
      "EPERM ambient raise locked"
    case C.CapsAmbientNotAllowed{}:
      "EPERM ambient not allowed"
    case C.CapsCapabilityDumb{}:
      "EPERM capability-dumb binary"

def show_sets(s: C.CapState) -> String:
  match s:
    case C.CapState{p, i, e, b, a}:
      "p=" ++ C.CapSet.show(p) ++ " i=" ++ C.CapSet.show(i) ++ " e=" ++ C.CapSet.show(e) ++ " b=" ++ C.CapSet.show(b) ++ " a=" ++ C.CapSet.show(a)

def show(r: Result<&2, &2, C.CapsError, C.CapCred>) -> String:
  match r:
    case Fail{e}:
      show_err(e)
    case Done{C.CapCred{ru, eu, sv, nr, na, s}}:
      "euid=" ++ U32.show(eu) ++ " " ++ show_sets(s)

def show_name(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      "none"
    case Some{s}:
      s

def user(s: C.CapState) -> C.CapCred:
  C.CapCred{1000, 1000, 1000, False{}, False{}, s}

# no capabilities, the full bounding set
def nothing() -> C.CapState:
  C.CapState{C.CapSet.empty(), C.CapSet.empty(), C.CapSet.empty(), C.CapSet.full(), C.CapSet.empty()}

# CAP_NET_BIND_SERVICE permitted, inheritable and ambient
def ambient_bind() -> C.CapState:
  C.CapState{C.CapSet.of(10), C.CapSet.of(10), C.CapSet.empty(), C.CapSet.full(), C.CapSet.of(10)}

def ping() -> C.CapFile:
  C.CapFile{0, False{}, False{}, Some{C.CapFileSets{C.CapSet.of(13), C.CapSet.empty(), True{}}}}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(show_name(C.Cap.name(0)) ++ " " ++ show_name(C.Cap.name(21)) ++ " " ++ show_name(C.Cap.name(40)) ++ " " ++ show_name(C.Cap.name(41)))
    IO.print(C.CapSet.show(C.CapSet.full()))
    IO.print(C.CapSet.show(C.CapSet.from_list([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 31, 32, 40])))
    IO.print(List.show(~&2, ~U32, ~U32.show, C.CapSet.to_list(C.CapSet.from_w64(C.CapSet.to_w64(C.CapSet.from_list([40, 13, 2]))))))
    IO.print(show(E.Caps.execve(C.CapsKernel.linux(), user(nothing()), ping(), False{})))
    IO.print(show(E.Caps.execve(C.CapsKernel.linux(), user(C.CapState.with_bounding(nothing(), C.CapSet.del(C.CapSet.full(), 13))), ping(), False{})))
    IO.print(show(E.Caps.execve(C.CapsKernel.linux(), user(nothing()), C.CapFile{0, True{}, False{}, None{}}, False{})))
    IO.print(show(E.Caps.execve(C.CapsKernel.linux(), user(nothing()), C.CapFile{0, True{}, False{}, None{}}, True{})))
    IO.print(show(E.Caps.execve(C.CapsKernel.linux(), C.CapCred{0, 0, 0, False{}, False{}, nothing()}, C.CapFile{1000, False{}, False{}, None{}}, False{})))
    IO.print(show(E.Caps.execve(C.CapsKernel.linux(), C.CapCred{0, 0, 0, True{}, False{}, nothing()}, C.CapFile{1000, False{}, False{}, None{}}, False{})))
    IO.print(show(E.Caps.execve(C.CapsKernel.linux(), user(ambient_bind()), C.CapFile{1000, False{}, False{}, None{}}, False{})))
    IO.print(show(E.Caps.execve(C.CapsKernel.linux(), user(ambient_bind()), C.CapFile{1000, False{}, True{}, None{}}, False{})))
    IO.print(show(E.Caps.execve(C.CapsKernel{40, False{}}, user(nothing()), ping(), False{})))
    IO.print(show(A.Caps.capset(user(ambient_bind()), C.CapSet.empty(), C.CapSet.of(10), C.CapSet.empty())))
    IO.print(show(A.Caps.capset(user(ambient_bind()), C.CapSet.of(10), C.CapSet.from_list([10, 12]), C.CapSet.of(10))))
    IO.print(show(A.Caps.capset(user(ambient_bind()), C.CapSet.of(12), C.CapSet.of(10), C.CapSet.of(10))))
    IO.print(show(A.Caps.capset(user(ambient_bind()), C.CapSet.empty(), C.CapSet.of(10), C.CapSet.from_list([10, 12]))))
    IO.print(show(A.Caps.bset_drop(C.CapsKernel.linux(), user(ambient_bind()), 13)))
    IO.print(show(A.Caps.bset_drop(C.CapsKernel.linux(), user(C.CapState{C.CapSet.of(8), C.CapSet.empty(), C.CapSet.of(8), C.CapSet.full(), C.CapSet.empty()}), 13)))
    IO.print(show(A.Caps.bset_drop(C.CapsKernel{38, True{}}, user(C.CapState{C.CapSet.of(8), C.CapSet.empty(), C.CapSet.of(8), C.CapSet.full(), C.CapSet.empty()}), 39)))
    IO.print(show(A.Caps.ambient_raise(C.CapsKernel.linux(), user(C.CapState{C.CapSet.of(12), C.CapSet.of(12), C.CapSet.empty(), C.CapSet.full(), C.CapSet.empty()}), 12)))
    IO.print(show(A.Caps.ambient_raise(C.CapsKernel.linux(), C.CapCred{1000, 1000, 1000, False{}, True{}, C.CapState{C.CapSet.of(12), C.CapSet.of(12), C.CapSet.empty(), C.CapSet.full(), C.CapSet.empty()}}, 12)))
    IO.print(show(A.Caps.ambient_lower(C.CapsKernel.linux(), user(ambient_bind()), 10)))

#|CAP_CHOWN CAP_SYS_ADMIN CAP_CHECKPOINT_RESTORE none
#|000001ffffffffff
#|0000010180003fff
#|[2, 13, 40]
#|euid=1000 p=0000000000002000 i=0000000000000000 e=0000000000002000 b=000001ffffffffff a=0000000000000000
#|EPERM capability-dumb binary
#|euid=0 p=000001ffffffffff i=0000000000000000 e=000001ffffffffff b=000001ffffffffff a=0000000000000000
#|euid=1000 p=0000000000000000 i=0000000000000000 e=0000000000000000 b=000001ffffffffff a=0000000000000000
#|euid=0 p=000001ffffffffff i=0000000000000000 e=000001ffffffffff b=000001ffffffffff a=0000000000000000
#|euid=0 p=0000000000000000 i=0000000000000000 e=0000000000000000 b=000001ffffffffff a=0000000000000000
#|euid=1000 p=0000000000000400 i=0000000000000400 e=0000000000000400 b=000001ffffffffff a=0000000000000400
#|euid=1000 p=0000000000000000 i=0000000000000400 e=0000000000000000 b=000001ffffffffff a=0000000000000000
#|euid=1000 p=0000000000000000 i=0000000000000000 e=0000000000000000 b=000001ffffffffff a=0000000000000000
#|euid=1000 p=0000000000000400 i=0000000000000000 e=0000000000000000 b=000001ffffffffff a=0000000000000000
#|EPERM permitted set grows
#|EPERM effective not permitted
#|EPERM inheritable not permitted
#|EPERM no CAP_SETPCAP
#|euid=1000 p=0000000000000100 i=0000000000000000 e=0000000000000100 b=000001ffffffdfff a=0000000000000000
#|EINVAL invalid capability
#|euid=1000 p=0000000000001000 i=0000000000001000 e=0000000000000000 b=000001ffffffffff a=0000000000001000
#|EPERM ambient raise locked
#|euid=1000 p=0000000000000400 i=0000000000000400 e=0000000000000000 b=000001ffffffffff a=0000000000000000
