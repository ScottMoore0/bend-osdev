# CBC with ciphertext stealing over any block cipher (the block-cipher
# interface, block.bend), in the variant CBC-CS3 of NIST SP 800-38A
# Addendum, "Three Variants of Ciphertext Stealing for CBC Mode" (2010), the
# one Kerberos 5 (RFC 3962) and the Linux kernel's "cts" use: a message of
# at least one block, of any length, gives a ciphertext of the same length.
#
# For a message of exactly one block: C = E(P xor IV) (plain CBC). Longer,
# with the message cut into P_1 .. P_(n-1) whole blocks and a last piece
# P_n* of d bytes (1 to b, the block size b):
#   C_1 .. C_(n-1) = CBC of P_1 .. P_(n-1) from the IV
#   C_n = E((P_n* || 0^(b-d)) xor C_(n-1))
#   the ciphertext: C_1 .. C_(n-2), C_n, the first d bytes of C_(n-1)
# (CS3 swaps the last two blocks always, even when d = b). Decryption reads
# C_n, recovers C_(n-1) from its first d bytes and the last b - d bytes of
# D(C_n), and P_n* as the first d bytes of D(C_n) xor C_(n-1).
#
# The cipher works on bytes here (a block the format refuses stays as it
# is). A message shorter than a block is refused (CrTooShort), and so is an
# IV that is not one block (CrBadIvLength).
import Base
import ../bytes/bytes.bend as B
import ./crypto.bend as Cr
import ./octets.bend as O

# a block of bytes encrypted or decrypted (f is the cipher's enc or dec)
def cr.cts.b.go(~K: Data, ~Blk: Data, ~f: K -> Blk -> Blk, ~blk_to: Blk -> B.Octets, +k: K, x: Maybe<&2, Blk>, +o: B.Octets) -> B.Octets:
  match x:
    case None{}:
      o
    case Some{b}:
      blk_to(f(k, b))

def cr.cts.b(~K: Data, ~Blk: Data, ~f: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +o: B.Octets) -> B.Octets:
  cr.cts.b.go(~K, ~Blk, ~f, ~blk_to, k, blk_of(o), o)

# the pieces in order, as byte strings, onto acc
def cr.cts.rcat(xs: List<&2, B.Octets>, acc: List<&2, B.Octets>) -> List<&2, B.Octets>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      cr.cts.rcat(t, Con{h, acc})

def cr.cts.out(acc: List<&2, B.Octets>) -> B.Octets:
  B.Octets.concat(cr.cts.rcat(acc, Nil{}))

# Encryption over the pieces (at least two; the last 1 to b bytes) from the
# chaining value v; acc holds the ciphertext so far, last first
def cr.cts.enc.go(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ps: List<&2, List<&2, U32>>, +k: K, +v: B.Octets, acc: List<&2, B.Octets>) -> B.Octets:
  match ps:
    case Con{p, t}:
      match t:
        case Con{q, u}:
          match u:
            case Nil{}:
              +x = cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))
              +last = B.Octets.of_list(q)
              +d = B.Octets.len(last)
              +cn = cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.append(last, B.Octets.zeros(Nat.sub(bsize, d))), x))
              cr.cts.out(Con{B.Octets.take(d, x), Con{cn, acc}})
            case Con{r, w}:
              +c = cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v))
              cr.cts.enc.go(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, Con{q, Con{r, w}}, k, c, Con{c, acc})
        case Nil{}:
          cr.cts.out(Con{cr.cts.b(~K, ~Blk, ~enc, ~blk_of, ~blk_to, k, O.CrOct.xor(B.Octets.of_list(p), v)), acc})
    case Nil{}:
      cr.cts.out(acc)

# Decryption over the pieces from the chaining value v
def cr.cts.dec.go(~K: Data, ~Blk: Data, ~bsize: Nat, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, ps: List<&2, List<&2, U32>>, +k: K, +v: B.Octets, acc: List<&2, B.Octets>) -> B.Octets:
  match ps:
    case Con{p, t}:
      match t:
        case Con{q, u}:
          match u:
            case Nil{}:
              +cn = B.Octets.of_list(p)
              +xs = B.Octets.of_list(q)
              +d = B.Octets.len(xs)
              +z = cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, cn)
              +x = B.Octets.append(xs, B.Octets.drop(d, z))
              +pn = O.CrOct.xor(B.Octets.take(d, z), xs)
              cr.cts.out(Con{pn, Con{O.CrOct.xor(cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, x), v), acc}})
            case Con{r, w}:
              +c = B.Octets.of_list(p)
              cr.cts.dec.go(~K, ~Blk, ~bsize, ~dec, ~blk_of, ~blk_to, Con{q, Con{r, w}}, k, c, Con{O.CrOct.xor(cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, c), v), acc})
        case Nil{}:
          cr.cts.out(Con{O.CrOct.xor(cr.cts.b(~K, ~Blk, ~dec, ~blk_of, ~blk_to, k, B.Octets.of_list(p)), v), acc})
    case Nil{}:
      cr.cts.out(acc)

def cr.cts.check(+bsize: Nat, +iv: B.Octets, +n: Nat) -> Result<&2, &2, Cr.CrError, Unit>:
  do Result<&2, &2, Cr.CrError, Unit>:
    Cr.CrError.check(Nat.is_eq(B.Octets.len(iv), bsize), Cr.CrBadIvLength{B.Octets.len(iv)})
    Cr.CrError.check(Bool.and(Nat.is_lt(0n, bsize), Nat.is_le(bsize, n)), Cr.CrTooShort{n})

# CBC-CS3 encryption of m (at least one block) under a one-block IV
def CrCts.encrypt(~K: Data, ~Blk: Data, ~bsize: Nat, ~enc: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +iv: B.Octets, +m: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.map(&2, &2, Cr.CrError, Unit, B.Octets, u => cr.cts.enc.go(~K, ~Blk, ~bsize, ~enc, ~blk_of, ~blk_to, O.CrOct.pieces(bsize, B.Octets.to_list(m)), k, iv, Nil{}), cr.cts.check(bsize, iv, B.Octets.len(m)))

# CBC-CS3 decryption
def CrCts.decrypt(~K: Data, ~Blk: Data, ~bsize: Nat, ~dec: K -> Blk -> Blk, ~blk_of: B.Octets -> Maybe<&2, Blk>, ~blk_to: Blk -> B.Octets, +k: K, +iv: B.Octets, +c: B.Octets) -> Result<&2, &2, Cr.CrError, B.Octets>:
  Result.map(&2, &2, Cr.CrError, Unit, B.Octets, u => cr.cts.dec.go(~K, ~Blk, ~bsize, ~dec, ~blk_of, ~blk_to, O.CrOct.pieces(bsize, B.Octets.to_list(c)), k, iv, Nil{}), cr.cts.check(bsize, iv, B.Octets.len(c)))
