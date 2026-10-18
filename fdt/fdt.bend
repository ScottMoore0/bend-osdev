# bend-osdev-fdt: reading and writing the flattened devicetree blob (DTB),
# from the Devicetree Specification v0.4 (devicetree.org), chapter 5.
#
# A blob is a header (header.bend), a memory reservation block
# (rsvmap.bend), a structure block of tokens (structure.bend) describing a
# tree of nodes and properties (tree.bend), and a strings block of property
# names. Fdt.parse checks and reads all of it; Fdt.build writes a version-17
# blob: header, reservation block at offset 40, structure block, strings
# block, with no gaps.
import Base
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./layout.bend as L
import ./header.bend as H
import ./rsvmap.bend as R
import ./structure.bend as S
import ./tree.bend as T

# What a reader accepts (FdtOptions.default(): versions 16 and 17, NOPs
# skipped, properties before children)
type FdtOptions is Data:
  FdtOptions{versions: H.FdtVersions, rules: T.FdtTreeRules}

def FdtOptions.default() -> FdtOptions:
  FdtOptions{H.FdtVersions.default(), T.FdtTreeRules.default()}

# A blob's contents
type FdtBlob is Data:
  FdtBlob{version: U32, boot_cpuid_phys: U32, reservations: List<&2, R.FdtRsv>, root: T.FdtNode}

# Reading

def parse.p9(r: Result<&2, &2, E.FdtError, T.FdtNode>, v: U32, boot: U32, rs: List<&2, R.FdtRsv>) -> Result<&2, &2, E.FdtError, FdtBlob>:
  match r:
    case Done{root}:
      Done{FdtBlob{v, boot, rs, root}}
    case Fail{e}:
      Fail{e}

def parse.p8(tr: Result<&2, &2, E.FdtError, List<&2, S.FdtToken>>, rules: T.FdtTreeRules, v: U32, boot: U32, rs: List<&2, R.FdtRsv>, strs: List<&2, U32>) -> Result<&2, &2, E.FdtError, FdtBlob>:
  match tr:
    case Done{ts}:
      parse.p9(T.tb.run(ts, rules, strs), v, boot, rs)
    case Fail{e}:
      Fail{e}

def parse.p7(rr: Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>, tr: Result<&2, &2, E.FdtError, List<&2, S.FdtToken>>, rules: T.FdtTreeRules, v: U32, boot: U32, strs: List<&2, U32>) -> Result<&2, &2, E.FdtError, FdtBlob>:
  match rr:
    case Done{rs}:
      parse.p8(tr, rules, v, boot, rs, strs)
    case Fail{e}:
      Fail{e}

# the structure block's tokens: from version 17, exactly size_dt_struct
# bytes, ending with FDT_END; for version 16, from off_dt_struct to
# totalsize, up to FDT_END
def parse.struct(is17: Bool, os: Nat, sst: Nat, region: List<&2, U32>) -> Result<&2, &2, E.FdtError, List<&2, S.FdtToken>>:
  match is17:
    case True{}:
      S.FdtLexer.finish(True{}, S.lx.go(B.take(sst, B.drop(os, region)), S.FdtLexer.start()))
    case False{}:
      S.FdtLexer.finish(False{}, S.lx.go(B.drop(os, region), S.FdtLexer.start()))

def parse.p6(rules: T.FdtTreeRules, +v: U32, boot: U32, +region: List<&2, U32>, orsv: Nat, os: Nat, sst: Nat, ostr: Nat, sstr: Nat) -> Result<&2, &2, E.FdtError, FdtBlob>:
  parse.p7(R.rsv.read(B.drop(orsv, region)), parse.struct(U32.is_lt(16, v), os, sst, region), rules, v, boot, B.take(sstr, B.drop(ostr, region)))

def parse.p5(r: Result<&2, &2, E.FdtError, Unit>, rules: T.FdtTreeRules, h: H.FdtHeader, xs: List<&2, U32>) -> Result<&2, &2, E.FdtError, FdtBlob>:
  match r:
    case Done{u}:
      match h:
        case H.FdtHeader{magic, totalsize, off_dt_struct, off_dt_strings, off_mem_rsvmap, version, last_comp_version, boot_cpuid_phys, size_dt_strings, size_dt_struct}:
          parse.p6(rules, version, boot_cpuid_phys, B.take(U32.to_nat(totalsize), xs), U32.to_nat(off_mem_rsvmap), U32.to_nat(off_dt_struct), U32.to_nat(size_dt_struct), U32.to_nat(off_dt_strings), U32.to_nat(size_dt_strings))
    case Fail{e}:
      Fail{e}

def parse.p4(m: Maybe<&2, H.FdtHeader>, opts: FdtOptions, +xs: List<&2, U32>) -> Result<&2, &2, E.FdtError, FdtBlob>:
  match m:
    case Some{+h}:
      match opts:
        case FdtOptions{vs, rules}:
          parse.p5(H.FdtHeader.check(vs, h, B.len(xs)), rules, h, xs)
    case None{}:
      Fail{E.FdtTooShort{}}

def parse.p3(ok: Bool, opts: FdtOptions, +xs: List<&2, U32>) -> Result<&2, &2, E.FdtError, FdtBlob>:
  match ok:
    case True{}:
      parse.p4(H.hdr.decode(xs), opts, xs)
    case False{}:
      Fail{E.FdtBadMagic{}}

def parse.p2(m: Maybe<&2, U32>, opts: FdtOptions, xs: List<&2, U32>) -> Result<&2, &2, E.FdtError, FdtBlob>:
  match m:
    case Some{v}:
      parse.p3(U32.is_eq(v, H.FdtHeader.magic_value()), opts, xs)
    case None{}:
      Fail{E.FdtTooShort{}}

def parse.p1(opts: FdtOptions, +xs: List<&2, U32>) -> Result<&2, &2, E.FdtError, FdtBlob>:
  parse.p2(B.be32_at(xs, 0n), opts, xs)

# The same reader, tail-recursive over the blob: bytes' fast forms for its
# length and its slices, and the tree read with the strings block indexed
# by offset (tree.bend: tb.run.fast). PROOF.bend: parse_fast proves it
# equal to parse.p1 above, the reference the proofs compute through.

def parse.f8(tr: Result<&2, &2, E.FdtError, List<&2, S.FdtToken>>, rules: T.FdtTreeRules, v: U32, boot: U32, rs: List<&2, R.FdtRsv>, strs: List<&2, U32>) -> Result<&2, &2, E.FdtError, FdtBlob>:
  match tr:
    case Done{ts}:
      parse.p9(T.tb.run.fast(ts, rules, strs), v, boot, rs)
    case Fail{e}:
      Fail{e}

def parse.f7(rr: Result<&2, &2, E.FdtError, List<&2, R.FdtRsv>>, tr: Result<&2, &2, E.FdtError, List<&2, S.FdtToken>>, rules: T.FdtTreeRules, v: U32, boot: U32, strs: List<&2, U32>) -> Result<&2, &2, E.FdtError, FdtBlob>:
  match rr:
    case Done{rs}:
      parse.f8(tr, rules, v, boot, rs, strs)
    case Fail{e}:
      Fail{e}

def parse.fstruct(is17: Bool, os: Nat, sst: Nat, region: List<&2, U32>) -> Result<&2, &2, E.FdtError, List<&2, S.FdtToken>>:
  match is17:
    case True{}:
      S.FdtLexer.finish(True{}, S.lx.go(B.take.fast(sst, B.drop(os, region)), S.FdtLexer.start()))
    case False{}:
      S.FdtLexer.finish(False{}, S.lx.go(B.drop(os, region), S.FdtLexer.start()))

def parse.f6(rules: T.FdtTreeRules, +v: U32, boot: U32, +region: List<&2, U32>, orsv: Nat, os: Nat, sst: Nat, ostr: Nat, sstr: Nat) -> Result<&2, &2, E.FdtError, FdtBlob>:
  parse.f7(R.rsv.read(B.drop(orsv, region)), parse.fstruct(U32.is_lt(16, v), os, sst, region), rules, v, boot, B.take.fast(sstr, B.drop(ostr, region)))

def parse.f5(r: Result<&2, &2, E.FdtError, Unit>, rules: T.FdtTreeRules, h: H.FdtHeader, xs: List<&2, U32>) -> Result<&2, &2, E.FdtError, FdtBlob>:
  match r:
    case Done{u}:
      match h:
        case H.FdtHeader{magic, totalsize, off_dt_struct, off_dt_strings, off_mem_rsvmap, version, last_comp_version, boot_cpuid_phys, size_dt_strings, size_dt_struct}:
          parse.f6(rules, version, boot_cpuid_phys, B.take.fast(U32.to_nat(totalsize), xs), U32.to_nat(off_mem_rsvmap), U32.to_nat(off_dt_struct), U32.to_nat(size_dt_struct), U32.to_nat(off_dt_strings), U32.to_nat(size_dt_strings))
    case Fail{e}:
      Fail{e}

def parse.f4(m: Maybe<&2, H.FdtHeader>, opts: FdtOptions, +xs: List<&2, U32>) -> Result<&2, &2, E.FdtError, FdtBlob>:
  match m:
    case Some{+h}:
      match opts:
        case FdtOptions{vs, rules}:
          parse.f5(H.FdtHeader.check(vs, h, B.len.fast(xs)), rules, h, xs)
    case None{}:
      Fail{E.FdtTooShort{}}

def parse.f3(ok: Bool, opts: FdtOptions, +xs: List<&2, U32>) -> Result<&2, &2, E.FdtError, FdtBlob>:
  match ok:
    case True{}:
      parse.f4(H.hdr.decode(xs), opts, xs)
    case False{}:
      Fail{E.FdtBadMagic{}}

def parse.f2(m: Maybe<&2, U32>, opts: FdtOptions, xs: List<&2, U32>) -> Result<&2, &2, E.FdtError, FdtBlob>:
  match m:
    case Some{v}:
      parse.f3(U32.is_eq(v, H.FdtHeader.magic_value()), opts, xs)
    case None{}:
      Fail{E.FdtTooShort{}}

def parse.f1(opts: FdtOptions, +xs: List<&2, U32>) -> Result<&2, &2, E.FdtError, FdtBlob>:
  parse.f2(B.be32_at(xs, 0n), opts, xs)

# the blob's version, boot CPU, reservations and tree, or why it was
# refused. Checked in this order: the magic (FdtBadMagic; FdtTooShort if
# there are fewer than 4 bytes, or than 40 after a good magic), then the
# header (FdtHeader.check), then the reservation block, then the structure
# block's tokens, then the tree they describe.
def Fdt.parse(opts: FdtOptions, o: B.Octets) -> Result<&2, &2, E.FdtError, FdtBlob>:
  parse.f1(opts, B.Octets.to_list(o))

# Writing

# a blob of the reservation block r, structure block s and strings block t
def build.layout(+r: List<&2, U32>, +s: List<&2, U32>, +t: List<&2, U32>, boot: U32) -> List<&2, U32>:
  +rest = B.append(r, B.append(s, t))
  B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n(Nat.add(40n, B.len(rest))), L.fdt.u32n(Nat.add(40n, B.len(r))), L.fdt.u32n(Nat.add(40n, B.len(B.append(r, s)))), 40, 17, 16, boot, L.fdt.u32n(B.len(t)), L.fdt.u32n(B.len(s))}), rest)

def build.simple(+root: T.FdtNode, rsv: List<&2, R.FdtRsv>, boot: U32) -> List<&2, U32>:
  build.layout(R.rsv.list(rsv), S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root]), boot)

# The same writer, tail-recursive over the blob (PROOF.bend: layout_fast,
# build_fast prove it equal to build.simple above, the reference the proofs
# compute through). The header and the reservation block are short, so
# only the structure and strings blocks need the fast forms.
def build.layout.fast(+r: List<&2, U32>, +s: List<&2, U32>, +t: List<&2, U32>, boot: U32) -> List<&2, U32>:
  +rest = B.append(r, B.append.fast(s, t))
  B.append(H.hdr.list(H.FdtHeader{H.FdtHeader.magic_value(), L.fdt.u32n.fast(Nat.add(40n, B.len.fast(rest))), L.fdt.u32n(Nat.add(40n, B.len(r))), L.fdt.u32n.fast(Nat.add(40n, B.len.fast(B.append(r, s)))), 40, 17, 16, boot, L.fdt.u32n.fast(B.len.fast(t)), L.fdt.u32n.fast(B.len.fast(s))}), rest)

def build.fast(+root: T.FdtNode, rsv: List<&2, R.FdtRsv>, boot: U32) -> List<&2, U32>:
  build.layout.fast(R.rsv.list(rsv), S.toks.fast(T.flat.toks.fast([root], 0n)), T.flat.strs.fast([root]), boot)

def build.dedup(d: T.FdtFlatD, rsv: List<&2, R.FdtRsv>, boot: U32) -> List<&2, U32>:
  match d:
    case T.FdtFlatD{ts, tab}:
      match tab:
        case T.FdtStrTab{bytes, size}:
          build.layout.fast(R.rsv.list(rsv), S.toks.fast(ts), bytes, boot)

def build.with(how: T.FdtStrings, +root: T.FdtNode, rsv: List<&2, R.FdtRsv>, boot: U32) -> List<&2, U32>:
  match how:
    case T.FdtStringsSimple{}:
      build.fast(root, rsv, boot)
    case T.FdtStringsDedup{}:
      build.dedup(T.dkx.run(root), rsv, boot)

# a version-17 blob (last_comp_version 16) holding the tree, the
# reservations and the boot CPU, with the strings block laid out as chosen
def Fdt.build_with(how: T.FdtStrings, root: T.FdtNode, rsv: List<&2, R.FdtRsv>, boot: U32) -> B.Octets:
  B.Octets.of_list(build.with(how, root, rsv, boot))

# the same, with the simple strings block (each name in turn)
def Fdt.build(root: T.FdtNode, rsv: List<&2, R.FdtRsv>, boot: U32) -> B.Octets:
  B.Octets.of_list(build.fast(root, rsv, boot))

# the blocks after the header, as Fdt.build writes them (the reference
# form, and the fast form)
def build.rest(+root: T.FdtNode, rsv: List<&2, R.FdtRsv>) -> List<&2, U32>:
  B.append(R.rsv.list(rsv), B.append(S.toks.list(T.flat.toks([root], 0n)), T.flat.strs([root])))

def build.rest.fast(+root: T.FdtNode, rsv: List<&2, R.FdtRsv>) -> List<&2, U32>:
  B.append(R.rsv.list(rsv), B.append.fast(S.toks.fast(T.flat.toks.fast([root], 0n)), T.flat.strs.fast([root])))

# Fdt.buildable as the proofs state it (PROOF.bend: buildable_fast)
def buildable.ref(+root: T.FdtNode, +rsv: List<&2, R.FdtRsv>) -> Bool:
  Bool.and(T.wf.ref(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits(Nat.add(40n, B.len(build.rest(root, rsv))))))

# what Fdt.build can write so that Fdt.parse reads it back: names without
# NULs, values shorter than 4 GiB, no reservation equal to the 0, 0 terminator, and a blob shorter than
# 4 GiB (its sizes and offsets fit their 32-bit fields)
def Fdt.buildable(+root: T.FdtNode, +rsv: List<&2, R.FdtRsv>) -> Bool:
  Bool.and(T.FdtNode.wf(root), Bool.and(R.FdtRsv.valid_all(rsv), L.fdt.fits.fast(Nat.add(40n, B.len.fast(build.rest.fast(root, rsv))))))
