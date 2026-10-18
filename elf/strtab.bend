# bend-osdev-elf, strtab.bend: a string table indexed by offset (gABI,
# "String Table"), so that looking up many strings in one table (the name of
# every symbol, of every section) costs each lookup the string's length and a
# walk of at most 32 levels, not a walk of the table to the string's offset.
#
# ElfStrtab.of(strtab) builds the index once, in time and memory in
# proportion to the table's size; ElfStrtab.string(ix, i) answers exactly what
# the reference lookup ElfShdr.string(strtab, i) (sections.bend) answers, for
# every table and every offset (LAWS.bend: strtab_string).
#
# The index is a binary trie over the table's suffixes, keyed by offset, least
# significant bit first: the suffixes at even offsets go to one half, those at
# odd offsets to the other, and so on, so that a node with one suffix left
# holds it as a leaf. A suffix is the rest of the table from its offset, and is
# shared with the table, not copied. Its representation is internal.
import Base
import ../bytes/bytes.bend as B
import ./fields.bend as F

# Internal: the trie. ElfTrieOne{s} holds s at key 0 and nothing elsewhere.
type ElfStrTrie is Data:
  ElfTrieNone{}
  ElfTrieOne{s: List<&2, U32>}
  ElfTrieNode{even: ElfStrTrie, odd: ElfStrTrie}

# An indexed string table (opaque)
type ElfStrtab is Data:
  ElfStrtab{trie: ElfStrTrie}

# Internal: building

# every non-empty suffix of xs, longest first (structural: the reference the
# proofs reason about)
def elf_suffixes(xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, +t}:
      Con{Con{h, t}, elf_suffixes(t)}

# the same, tail-recursive (the suffixes so far are kept reversed in acc)
def elf_suffixes.go(xs: List<&2, U32>, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      F.elf_rev_onto(List<&2, U32>, acc, Nil{})
    case Con{+h, +t}:
      elf_suffixes.go(t, Con{Con{h, t}, acc})

def elf_suffixes.fast(xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  elf_suffixes.go(xs, Nil{})

# every other element of ys: those at even positions if keep, else those at
# odd positions (structural: the reference)
def elf_alt(ys: List<&2, List<&2, U32>>, keep: Bool) -> List<&2, List<&2, U32>>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{y, t}:
      match keep:
        case True{}:
          Con{y, elf_alt(t, False{})}
        case False{}:
          elf_alt(t, True{})

# the same, tail-recursive
def elf_alt.go(ys: List<&2, List<&2, U32>>, keep: Bool, acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ys:
    case Nil{}:
      F.elf_rev_onto(List<&2, U32>, acc, Nil{})
    case Con{y, t}:
      match keep:
        case True{}:
          elf_alt.go(t, False{}, Con{y, acc})
        case False{}:
          elf_alt.go(t, True{}, acc)

def elf_alt.fast(ys: List<&2, List<&2, U32>>, keep: Bool) -> List<&2, List<&2, U32>>:
  elf_alt.go(ys, keep, Nil{})

def elf_trie.leaf(ys: List<&2, List<&2, U32>>) -> ElfStrTrie:
  match ys:
    case Nil{}:
      ElfTrieNone{}
    case Con{y, t}:
      ElfTrieOne{y}

# the trie of d levels whose key k holds the k-th element of ys
def elf_trie(d: Nat, +ys: List<&2, List<&2, U32>>) -> ElfStrTrie:
  match d:
    case 0n:
      elf_trie.leaf(ys)
    case 1n+(+p):
      match ys:
        case Nil{}:
          ElfTrieNone{}
        case Con{a, t}:
          match t:
            case Nil{}:
              ElfTrieOne{a}
            case Con{b, r}:
              ElfTrieNode{elf_trie(p, elf_alt.fast(Con{a, Con{b, r}}, True{})), elf_trie(p, elf_alt.fast(Con{a, Con{b, r}}, False{}))}

# Internal: looking up

def elf_trie.here(t: ElfStrTrie) -> Maybe<&2, List<&2, U32>>:
  match t:
    case ElfTrieOne{s}:
      Some{s}
    case other:
      None{}

# whether every bit of w is 0
def elf_trie.zero(d: Nat, w: Word(d)) -> Bool:
  match d:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{False{}, r}:
          elf_trie.zero(p, r)
        case WCon{True{}, r}:
          False{}

def elf_trie.at0(z: Bool, s: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match z:
    case True{}:
      Some{s}
    case False{}:
      None{}

# the element at key w (its bits, least significant first)
def elf_trie.find(d: Nat, t: ElfStrTrie, w: Word(d)) -> Maybe<&2, List<&2, U32>>:
  match d:
    case 0n:
      elf_trie.here(t)
    case 1n+p:
      match t:
        case ElfTrieNone{}:
          None{}
        case ElfTrieOne{s}:
          elf_trie.at0(elf_trie.zero(1n+p, w), s)
        case ElfTrieNode{e, o}:
          match w:
            case WCon{False{}, r}:
              elf_trie.find(p, e, r)
            case WCon{True{}, r}:
              elf_trie.find(p, o, r)

# the string at the front of a suffix, if it has its NUL
def elf_strtab.cut(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{s}:
      F.elf_cstr(s)
    case None{}:
      None{}

# Public

# the index of a string table's bytes
def ElfStrtab.of(strtab: B.Octets) -> ElfStrtab:
  ElfStrtab{elf_trie(32n, elf_suffixes.fast(B.Octets.to_list(strtab)))}

# the NUL-terminated string at offset i of the indexed table (without its
# NUL); ElfBadString if i is past the end or the NUL is missing: the same
# answer as ElfShdr.string on the table's bytes
def ElfStrtab.string(ix: ElfStrtab, i: U32) -> Result<&2, &2, F.ElfError, B.Octets>:
  match ix i:
    case ElfStrtab{t} U32{w}:
      F.elf_string.result(elf_strtab.cut(elf_trie.find(32n, t, w)))
