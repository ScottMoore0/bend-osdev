# bend-osdev-selinux: security contexts.
#
# A security context is a user, a role, a type and an MLS range (SELinux
# Notebook, "Security Context"). Users, roles and types are numbered by the
# policy (policy.bend holds their names); the range is an M.SeRange. A policy
# without MLS still gives every context a range (the single level s0, as
# CIL requires a sensitivity).
import Base
import ./bits.bend as Bits
import ./mls.bend as M

type SeContext is Data:
  SeContext{user: Nat, role: Nat, typ: Nat, range: M.SeRange}

def SeContext.user(x: SeContext) -> Nat:
  match x:
    case SeContext{v, _, _, _}:
      v

def SeContext.role(x: SeContext) -> Nat:
  match x:
    case SeContext{_, v, _, _}:
      v

def SeContext.typ(x: SeContext) -> Nat:
  match x:
    case SeContext{_, _, v, _}:
      v

def SeContext.range(x: SeContext) -> M.SeRange:
  match x:
    case SeContext{_, _, _, v}:
      v

def SeContext.low(c: SeContext) -> M.SeLevel:
  match c:
    case SeContext{u, r, t, rg}:
      match rg:
        case M.SeRange{lo, hi}:
          lo

def SeContext.high(c: SeContext) -> M.SeLevel:
  match c:
    case SeContext{u, r, t, rg}:
      match rg:
        case M.SeRange{lo, hi}:
          hi

def SeContext.with_type(c: SeContext, t: Nat) -> SeContext:
  match c:
    case SeContext{u, r, old, rg}:
      SeContext{u, r, t, rg}

def SeContext.with_role(c: SeContext, r: Nat) -> SeContext:
  match c:
    case SeContext{u, old, t, rg}:
      SeContext{u, r, t, rg}

def SeContext.with_range(c: SeContext, rg: M.SeRange) -> SeContext:
  match c:
    case SeContext{u, r, t, old}:
      SeContext{u, r, t, rg}

def SeContext.is_eq(a: SeContext, b: SeContext) -> Bool:
  match a:
    case SeContext{ua, ra, ta, ga}:
      match b:
        case SeContext{ub, rb, tb, gb}:
          Bool.and(Nat.is_eq(ua, ub), Bool.and(Nat.is_eq(ra, rb), Bool.and(Nat.is_eq(ta, tb), M.SeRange.is_eq(ga, gb))))
