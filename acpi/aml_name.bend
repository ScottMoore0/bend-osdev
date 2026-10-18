# bend-osdev-acpi, aml_name.bend: AML name strings (ACPI 6.5, sections
# 20.2.2, Name Objects Encoding, and 5.3, ACPI Namespace):
#
#   NameSeg       := <LeadNameChar NameChar NameChar NameChar>
#   LeadNameChar  := 'A'-'Z' | '_'
#   NameChar      := DigitChar | LeadNameChar      (DigitChar: '0'-'9')
#   NameString    := <RootChar NamePath> | <PrefixPath NamePath>
#   RootChar      := '\' (0x5C)
#   PrefixPath    := Nothing | <'^' PrefixPath>     ('^' is 0x5E)
#   NamePath      := NameSeg | DualNamePath | MultiNamePath | NullName
#   DualNamePath  := DualNamePrefix NameSeg NameSeg (DualNamePrefix: 0x2E)
#   MultiNamePath := MultiNamePrefix SegCount NameSeg(SegCount)
#                    (MultiNamePrefix: 0x2F; SegCount: a byte, 1 to 255)
#   NullName      := 0x00
#
# A name is AmlName{root, up, segs}: rooted at '\', or up some number of
# parents, then its segments (4 bytes each, as Octets). The encoder writes
# the shortest NamePath (a NameSeg for one segment, DualNamePath for two,
# MultiNamePath for three or more); the decoder reads every form, and
# refuses a SegCount of 0.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E

type AmlName is Data:
  AmlName{root: Bool, up: Nat, segs: List<&2, B.Octets>}

# a name read from a list of bytes: the name and what follows
type AmlNameL is Data:
  AmlNameL{name: AmlName, rest: List<&2, U32>}

# a name read from Octets
type AmlNameParsed is Data:
  AmlNameParsed{name: AmlName, rest: B.Octets}

def AmlName.root(n: AmlName) -> Bool:
  match n:
    case AmlName{r, u, s}:
      r

def AmlName.up(n: AmlName) -> Nat:
  match n:
    case AmlName{r, u, s}:
      u

def AmlName.segs(n: AmlName) -> List<&2, B.Octets>:
  match n:
    case AmlName{r, u, s}:
      s

# What a byte can begin

type AmlLeadKind is Data:
  AmlLRoot{}
  AmlLParent{}
  AmlLDual{}
  AmlLMulti{}
  AmlLNull{}
  AmlLSeg{}
  AmlLOther{}

def nm.alpha(+c: U32) -> Bool:
  Bool.or(Bool.and(U32.is_le(65, c), U32.is_le(c, 90)), U32.is_eq(c, 95))

def nm.cls.c(seg: Bool) -> AmlLeadKind:
  match seg:
    case True{}:
      AmlLSeg{}
    case False{}:
      AmlLOther{}

def nm.cls.b(z: Bool, +c: U32) -> AmlLeadKind:
  match z:
    case True{}:
      AmlLNull{}
    case False{}:
      nm.cls.c(nm.alpha(c))

def nm.cls.a(m: Bool, +c: U32) -> AmlLeadKind:
  match m:
    case True{}:
      AmlLMulti{}
    case False{}:
      nm.cls.b(U32.is_eq(c, 0), c)

def nm.cls.n9(d: Bool, +c: U32) -> AmlLeadKind:
  match d:
    case True{}:
      AmlLDual{}
    case False{}:
      nm.cls.a(U32.is_eq(c, 47), c)

def nm.cls.n8(p: Bool, +c: U32) -> AmlLeadKind:
  match p:
    case True{}:
      AmlLParent{}
    case False{}:
      nm.cls.n9(U32.is_eq(c, 46), c)

def nm.cls.r(r: Bool, +c: U32) -> AmlLeadKind:
  match r:
    case True{}:
      AmlLRoot{}
    case False{}:
      nm.cls.n8(U32.is_eq(c, 94), c)

# the kind of name element a byte begins
def AmlLead.classify(+c: U32) -> AmlLeadKind:
  nm.cls.r(U32.is_eq(c, 92), c)

def AmlLead.is_seg(k: AmlLeadKind) -> Bool:
  match k:
    case AmlLSeg{}:
      True{}
    case _:
      False{}

# a NameChar: a LeadNameChar or a digit
def AmlName.name_char(+c: U32) -> Bool:
  Bool.or(nm.alpha(c), Bool.and(U32.is_le(48, c), U32.is_le(c, 57)))

def nm.seg_ok4(+c0: U32, +c1: U32, +c2: U32, +c3: U32) -> Bool:
  Bool.and(AmlLead.is_seg(AmlLead.classify(c0)), Bool.and(AmlName.name_char(c1), Bool.and(AmlName.name_char(c2), AmlName.name_char(c3))))

def nm.seg_ok.list(xs: List<&2, U32>) -> Bool:
  match xs:
    case Con{c0, Con{c1, Con{c2, Con{c3, Nil{}}}}}:
      nm.seg_ok4(c0, c1, c2, c3)
    case _:
      False{}

# a NameSeg: four bytes, a LeadNameChar then three NameChars
def AmlName.seg_ok(s: B.Octets) -> Bool:
  nm.seg_ok.list(B.Octets.to_list(s))

def AmlName.segs_ok(ss: List<&2, B.Octets>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, t}:
      Bool.and(AmlName.seg_ok(s), AmlName.segs_ok(t))

def nm.root_up_ok(root: Bool, up: Nat) -> Bool:
  match root:
    case True{}:
      Nat.is_eq(up, 0n)
    case False{}:
      True{}

def nm.len(ss: List<&2, B.Octets>) -> Nat:
  List.length(&2, B.Octets, ss)

# the names a NameString can hold: not both rooted and going up, every
# segment a NameSeg, at most 255 segments
def AmlName.valid(n: AmlName) -> Bool:
  match n:
    case AmlName{r, u, +ss}:
      Bool.and(nm.root_up_ok(r, u), Bool.and(AmlName.segs_ok(ss), Nat.is_lt(nm.len(ss), 256n)))

# Encoding (list layer)

def nm.carets(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n+p:
      Con{94, nm.carets(p)}

def nm.prefix(root: Bool, up: Nat) -> List<&2, U32>:
  match root:
    case True{}:
      [92]
    case False{}:
      nm.carets(up)

def nm.segs.list(ss: List<&2, B.Octets>) -> List<&2, U32>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      B.append(B.Octets.to_list(s), nm.segs.list(t))

def nm.path(ss: List<&2, B.Octets>) -> List<&2, U32>:
  match ss:
    case Nil{}:
      [0]
    case Con{s, Nil{}}:
      nm.segs.list([s])
    case Con{s1, Con{s2, Nil{}}}:
      Con{46, nm.segs.list([s1, s2])}
    case Con{s1, Con{s2, Con{s3, +t}}}:
      Con{47, Con{U32.from_nat(Nat.add(3n, nm.len(t))), nm.segs.list(Con{s1, Con{s2, Con{s3, t}}})}}

def nm.enc(n: AmlName) -> List<&2, U32>:
  match n:
    case AmlName{r, u, ss}:
      B.append(nm.prefix(r, u), nm.path(ss))

# the name as a NameString (AmlName.valid names read back: LAWS.bend,
# namestring_round_trip)
def AmlName.encode(n: AmlName) -> B.Octets:
  B.Octets.of_list(nm.enc(n))

# its size in bytes
def AmlName.size(n: AmlName) -> Nat:
  B.len.fast(nm.enc(n))

# Decoding (list layer)

type AmlSegL is Data:
  AmlSegL{seg: B.Octets, rest: List<&2, U32>}

type AmlSegsL is Data:
  AmlSegsL{segs: List<&2, B.Octets>, rest: List<&2, U32>}

def nm.seg.pick(ok: Bool, c0: U32, c1: U32, c2: U32, c3: U32, t: List<&2, U32>) -> Result<&2, &2, E.AcpiError, AmlSegL>:
  match ok:
    case True{}:
      Done{AmlSegL{B.Octets.of_list([c0, c1, c2, c3]), t}}
    case False{}:
      Fail{E.AcpiAmlBadName{}}

def nm.seg(xs: List<&2, U32>) -> Result<&2, &2, E.AcpiError, AmlSegL>:
  match xs:
    case Con{+c0, Con{+c1, Con{+c2, Con{+c3, t}}}}:
      nm.seg.pick(nm.seg_ok4(c0, c1, c2, c3), c0, c1, c2, c3, t)
    case _:
      Fail{E.AcpiAmlTruncated{}}

def nm.cons(s: B.Octets, r: Result<&2, &2, E.AcpiError, AmlSegsL>) -> Result<&2, &2, E.AcpiError, AmlSegsL>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{AmlSegsL{ss, rest}}:
      Done{AmlSegsL{Con{s, ss}, rest}}

# the segment in r, then p more
def nm.segs.go(p: Nat, r: Result<&2, &2, E.AcpiError, AmlSegL>) -> Result<&2, &2, E.AcpiError, AmlSegsL>:
  match p:
    case 0n:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{AmlSegL{s, rest}}:
          Done{AmlSegsL{[s], rest}}
    case 1n+q:
      match r:
        case Fail{e}:
          Fail{e}
        case Done{AmlSegL{s, rest}}:
          nm.cons(s, nm.segs.go(q, nm.seg(rest)))

# n segments
def nm.segs(n: Nat, xs: List<&2, U32>) -> Result<&2, &2, E.AcpiError, AmlSegsL>:
  match n:
    case 0n:
      Done{AmlSegsL{Nil{}, xs}}
    case 1n+p:
      nm.segs.go(p, nm.seg(xs))

def nm.multi.k(zero: Bool, n: Nat, r: List<&2, U32>) -> Result<&2, &2, E.AcpiError, AmlSegsL>:
  match zero:
    case True{}:
      Fail{E.AcpiAmlBadName{}}
    case False{}:
      nm.segs(n, r)

def nm.multi(t: List<&2, U32>) -> Result<&2, &2, E.AcpiError, AmlSegsL>:
  match t:
    case Nil{}:
      Fail{E.AcpiAmlTruncated{}}
    case Con{c, r}:
      +n = U32.to_nat(c)
      nm.multi.k(Nat.is_eq(n, 0n), n, r)

def nm.path.k(k: AmlLeadKind, c: U32, t: List<&2, U32>) -> Result<&2, &2, E.AcpiError, AmlSegsL>:
  match k:
    case AmlLNull{}:
      Done{AmlSegsL{Nil{}, t}}
    case AmlLDual{}:
      nm.segs(2n, t)
    case AmlLMulti{}:
      nm.multi(t)
    case AmlLSeg{}:
      nm.segs(1n, Con{c, t})
    case _:
      Fail{E.AcpiAmlBadName{}}

def nm.dpath(xs: List<&2, U32>) -> Result<&2, &2, E.AcpiError, AmlSegsL>:
  match xs:
    case Nil{}:
      Fail{E.AcpiAmlTruncated{}}
    case Con{+c, t}:
      nm.path.k(AmlLead.classify(c), c, t)

def nm.named(root: Bool, up: Nat, r: Result<&2, &2, E.AcpiError, AmlSegsL>) -> Result<&2, &2, E.AcpiError, AmlNameL>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{AmlSegsL{ss, rest}}:
      Done{AmlNameL{AmlName{root, up, ss}, rest}}

def nm.up1(r: Result<&2, &2, E.AcpiError, AmlNameL>) -> Result<&2, &2, E.AcpiError, AmlNameL>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{AmlNameL{AmlName{root, up, ss}, rest}}:
      Done{AmlNameL{AmlName{root, 1n+up, ss}, rest}}

def nm.head_kind(xs: List<&2, U32>) -> AmlLeadKind:
  match xs:
    case Nil{}:
      AmlLOther{}
    case Con{+c, t}:
      AmlLead.classify(c)

# parent prefixes, then a path; k is the kind of the first byte
def nm.ups(xs: List<&2, U32>, k: AmlLeadKind) -> Result<&2, &2, E.AcpiError, AmlNameL>:
  match xs:
    case Nil{}:
      Fail{E.AcpiAmlTruncated{}}
    case Con{c, +t}:
      match k:
        case AmlLParent{}:
          nm.up1(nm.ups(t, nm.head_kind(t)))
        case _:
          nm.named(False{}, 0n, nm.path.k(k, c, t))

def nm.dec.k(k: AmlLeadKind, c: U32, t: List<&2, U32>) -> Result<&2, &2, E.AcpiError, AmlNameL>:
  match k:
    case AmlLRoot{}:
      nm.named(True{}, 0n, nm.dpath(t))
    case _:
      nm.ups(Con{c, t}, k)

# the NameString at the front of a list of bytes
def nm.dec(xs: List<&2, U32>) -> Result<&2, &2, E.AcpiError, AmlNameL>:
  match xs:
    case Nil{}:
      Fail{E.AcpiAmlTruncated{}}
    case Con{+c, t}:
      nm.dec.k(AmlLead.classify(c), c, t)

def nm.pub(r: Result<&2, &2, E.AcpiError, AmlNameL>) -> Result<&2, &2, E.AcpiError, AmlNameParsed>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{AmlNameL{n, rest}}:
      Done{AmlNameParsed{n, B.Octets.of_list(rest)}}

# the NameString at the front of o, and what follows it
def AmlName.decode(o: B.Octets) -> Result<&2, &2, E.AcpiError, AmlNameParsed>:
  nm.pub(nm.dec(B.Octets.to_list(o)))

# Text: "\_SB_.PCI0", "^^_STA", and the null name "" (segments in full)

def nm.show.segs(ss: List<&2, B.Octets>, first: Bool) -> String:
  match ss:
    case Nil{}:
      ""
    case Con{s, t}:
      match first:
        case True{}:
          B.Octets.to_string(s) ++ nm.show.segs(t, False{})
        case False{}:
          "." ++ B.Octets.to_string(s) ++ nm.show.segs(t, False{})

def nm.show.pre(root: Bool, up: Nat) -> String:
  match root:
    case True{}:
      "\\"
    case False{}:
      String.repeat("^", up)

def AmlName.show(n: AmlName) -> String:
  match n:
    case AmlName{r, u, ss}:
      nm.show.pre(r, u) ++ nm.show.segs(ss, True{})

# a segment from text: its first four characters, padded with '_' as ASL
# does ("_SB" is "_SB_")
def AmlName.seg(s: String) -> B.Octets:
  +o = B.Octets.take(4n, B.Octets.of_string(s))
  B.Octets.append(o, B.Octets.of_string(String.repeat("_", Nat.sub(4n, B.Octets.len(o)))))

def nm.text.segs(ps: List<&2, String>) -> List<&2, B.Octets>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Con{AmlName.seg(p), nm.text.segs(t)}

def nm.text.split.pick(e: Bool, +s: String) -> List<&2, B.Octets>:
  match e:
    case True{}:
      Nil{}
    case False{}:
      nm.text.segs(String.split(s, '.'))

def nm.text.split(+s: String) -> List<&2, B.Octets>:
  nm.text.split.pick(String.is_empty(s), s)

# leading carets, counted; isc: s starts with one
def nm.text.ups(s: String, isc: Bool, n: Nat) -> AmlName:
  match s:
    case SNil{}:
      AmlName{False{}, n, Nil{}}
    case SCon{h, +t}:
      match isc:
        case True{}:
          nm.text.ups(t, String.starts_with(t, "^"), 1n+n)
        case False{}:
          AmlName{False{}, n, nm.text.split(SCon{h, t})}

def nm.text.root(r: Bool, +s: String) -> AmlName:
  match r:
    case True{}:
      AmlName{True{}, 0n, nm.text.split(String.drop(s, 1n))}
    case False{}:
      nm.text.ups(s, String.starts_with(s, "^"), 0n)

# a name from its text: "\_SB.PCI0" (in Bend source), "^^_STA", "LNKA";
# segments are separated by '.', each padded to four characters with '_'
def AmlName.of_text(+s: String) -> AmlName:
  nm.text.root(String.starts_with(s, "\\"), s)
