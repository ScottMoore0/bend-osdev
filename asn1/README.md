# bend-osdev-asn1

ASN.1's Basic and Distinguished Encoding Rules: decoding octets to elements
and encoding elements to octets, the typed values X.509 and PKCS use, and a
schema layer that describes a structure as a Bend value and decodes it
generically. The counterpart of Linux's lib/asn1_decoder and the tables its
asn1_compiler generates, written from the ITU-T Recommendations; no kernel
source was read.

## Specifications

* ITU-T Recommendation X.690 (02/2021), *Information technology – ASN.1
  encoding rules: Specification of Basic Encoding Rules (BER), Canonical
  Encoding Rules (CER) and Distinguished Encoding Rules (DER)*: 8.1 (the
  structure of an encoding: identifier octets 8.1.2, length octets 8.1.3,
  end-of-contents octets 8.1.5), 8.2 to 8.14 and 8.19 (the types used
  here), 8.23 (restricted character strings), 10 (DER: definite lengths in
  the fewest octets 10.1, primitive strings 10.2, SET order 10.3) and 11
  (BOOLEAN TRUE as FF 11.1, unused bits zero 11.2, DEFAULT values not
  encoded 11.5, SET OF order 11.6, GeneralizedTime 11.7, UTCTime 11.8). The
  octet-string comparison of 6.3 orders SET OF elements.
* ITU-T Recommendation X.680 (02/2021), *Information technology – Abstract
  Syntax Notation One (ASN.1): Specification of basic notation*: clause 8
  (tags, Table 1's universal tags, 8.6's canonical order of tags), 31.2
  (tagging; 31.2.7 makes a tagged CHOICE explicit), 41 (Table 8, Table 9
  NumericString, Table 10 PrintableString), 46 (GeneralizedTime), 47
  (UTCTime).
* RFC 3629, *UTF-8, a transformation format of ISO 10646* (November 2003),
  section 4: the syntax a UTF8String's octets are checked against.
* RFC 5280, *Internet X.509 Public Key Infrastructure Certificate and
  Certificate Revocation List (CRL) Profile* (May 2008), 4.1.2.5.1: the
  default UTCTime century rule (YY of 50 or more is 19YY, below 50 is 20YY).

## What it implements

* **Elements** (`node.bend`): `Asn1Prim{tag, content}` and
  `Asn1Cons{tag, items}`, a tag being `Asn1Tag{cls, num}` with
  `Asn1Universal`, `Asn1Application`, `Asn1Context`, `Asn1Private`.
* **Decoding** (`asn1.bend`): identifier octets with high tag numbers;
  definite lengths (short and long form) and, under BER, indefinite lengths
  with end-of-contents octets; primitive and constructed encodings, nested
  to any depth. Identifier octets must always be the fewest (8.1.2.2,
  8.1.2.4.2 c). The decoder keeps the octets of each element when asked
  (`Asn1.read`, `Asn1.items`), so signed parts can be checked later.
* **Rules** (`rules.bend`), each a parameter of `Asn1Rules`:
  `indefinite` (the indefinite form), `min_length` (lengths in the fewest
  octets), `forms` (X.690's fixed forms for universal types), `prim_strings`
  (no constructed strings), `set_order` (`Asn1SetAny`, `Asn1SetOfOrder`:
  encodings ascending, `Asn1SetTagOrder`: tags ascending), `trailing`
  (octets after the element allowed), `values` (DER's value restrictions
  in the typed readers). `Asn1Rules.der()` and `Asn1Rules.ber()` are the
  two named sets; `Asn1Rules.default()` is DER.
* **Encoding** (`encode.bend`): DER (definite lengths in the fewest
  octets); `conform.bend` says whether a value conforms to rules (its SETs
  in order, its universal types in their forms).
* **Typed values**: BOOLEAN, NULL, OCTET STRING, INTEGER and ENUMERATED
  (`prim.bend`); BIT STRING (`bits.bend`); OBJECT IDENTIFIER contents
  (`oidval.bend`); the restricted character strings UTF8String,
  NumericString, PrintableString, TeletexString, IA5String, VisibleString,
  UniversalString and BMPString (`string.bend`); UTCTime and
  GeneralizedTime (`time.bend`); SEQUENCE, SET, SET OF in DER order, and
  EXPLICIT and IMPLICIT tagging (`build.bend`). Every reader takes the tag
  it expects, so IMPLICIT-tagged values are read with their own tags.
* **Schemas** (`schema.bend`): `Asn1Schema` describes a type — any element,
  an element of a tag, a SEQUENCE of fields, a SEQUENCE OF or SET OF, a
  CHOICE, an EXPLICIT tag, OPTIONAL and DEFAULT fields — and `Asn1.match`
  reads an element's octets against it into an `Asn1Match` tree that keeps
  every matched element's octets.

## Files

| File | Holds |
|---|---|
| `asn1.bend` | the entry file: the decoder (`Asn1.decode`, `decode_prefix`, `decode_all`, `read`, `read_all`, `contents`, `items`) |
| `error.bend` | `Asn1Error` |
| `tag.bend` | classes, tags, the universal tags used, identifier octets |
| `length.bend` | length octets |
| `number.bend` | numbers in octets (base-128, big-endian), the implementation's bound on them |
| `node.bend` | elements and their spans |
| `rules.bend` | decoding rules and X.690's fixed forms |
| `encode.bend` | the encoder |
| `conform.bend` | SET order and what rules accept of a value |
| `prim.bend` | BOOLEAN, NULL, OCTET STRING, INTEGER, ENUMERATED |
| `bits.bend` | BIT STRING |
| `oidval.bend` | OBJECT IDENTIFIER contents |
| `string.bend` | character strings and UTF-8 |
| `time.bend` | UTCTime and GeneralizedTime |
| `build.bend` | SEQUENCE, SET, SET OF, EXPLICIT and IMPLICIT tags |
| `schema.bend` | schemas and the matcher |
| `LAWS.bend`, `PROOF.bend` | the laws of the decoder, the encoder and the matcher, and their proofs |
| `LAWS_typed.bend`, `PROOF_typed.bend` | the laws of the typed readers and writers, and their proofs |
| `LAWS_conform.bend`, `PROOF_conform.bend` | the law that every schema match conforms to its schema, and its proof (generated by `gen/gen_conform.py`) |
| `proof_nat.bend`, `proof_list.bend`, `proof_u32.bend`, `proof_num.bend`, `proof_head.bend`, `proof_enc.bend`, `proof_within.bend`, `proof_canon.bend`, `proof_oid.bend`, `proof_oct.bend`, `proof_split.bend`, `proof_der.bend`, `proof_match.bend` | lemmas of `PROOF.bend` (see Laws) |
| `proof_int.bend`, `proof_intc.bend`, `proof_prims.bend`, `proof_strict.bend`, `proof_clock.bend` | lemmas of `PROOF_typed.bend` (see Laws) |
| `proof_byte.bend` | generated by `gen/gen_byte.py`: single octets read back (a closed computation per value) |
| `proof_d2.bend` | generated by `gen/gen_digits.py`: the two digit characters written for each number below 100 read back (a closed computation per value) |
| `proof_chars.bend` | generated by `gen/gen_chars.py`: each octet against the character tables of the one-octet string types (a closed computation per octet) |
| `proof_tstrict.bend` | UTCTime and GeneralizedTime contents read under DER are the writer's; its deep patterns over the digit characters are generated by `gen/gen_tstrict.py` |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh`, `ref/show.bend.in` | the differential test (`ref/.gitignore` lists what it generates) |

## API

| Def or type | Meaning |
|---|---|
| `Asn1Node`: `Asn1Prim{tag, content}`, `Asn1Cons{tag, items}`; `Asn1Node.tag`, `.is_cons`, `.content`, `.items` | elements (an open type) |
| `Asn1Tag{cls, num}`, `Asn1Class` (`Asn1Universal`, `Asn1Application`, `Asn1Context`, `Asn1Private`); `Asn1Tag.universal(n)`, `.context(n)`, `.boolean()`, `.integer()`, `.bit_string()`, `.octet_string()`, `.null()`, `.oid()`, `.enumerated()`, `.utf8_string()`, `.sequence()`, `.set()`, `.printable_string()`, `.t61_string()`, `.ia5_string()`, `.utc_time()`, `.generalized_time()`, `.universal_string()`, `.bmp_string()`; `Asn1Tag.is_eq`, `.is_lt` (X.680 8.6's order), `.cls`, `.num`; `Asn1Class.rank`, `.is_eq` | tags |
| `Asn1Error` and `Asn1Error.name(e)` | why octets or values were refused (below) |
| `Asn1Rules{indefinite, min_length, forms, prim_strings, set_order, trailing, values}`, `Asn1SetOrder`; `Asn1Rules.der()`, `.ber()`, `.default()`, the field readers, `Asn1Rules.with_trailing(r, t)` | decoding rules |
| `Asn1.decode(r, b)` | the element `b` holds (`Asn1Trailing` for octets after it unless `r.trailing`) |
| `Asn1.decode_prefix(r, b)` | `Asn1Read{node, rest}`: the first element and the octets after it |
| `Asn1.decode_all(r, b)` | the elements of `b`, one after another |
| `Asn1.read(r, b)`, `Asn1.read_all(r, b)` | `Asn1TlvRead{tlv, rest}` / a list of `Asn1Tlv{node, raw}`: elements with the exact octets each was read from; `Asn1Tlv.node`, `Asn1Tlv.raw`; `Asn1.raws(xs)`, the octets of each, in order |
| `Asn1.contents(r, x)`, `Asn1.items(r, x)` | a read element's contents octets (without end-of-contents octets), its elements with their octets |
| `Asn1.encode(n)`, `Asn1.encode_all(ns)` | DER octets (`Asn1ReservedTag`, `Asn1BadTag`, `Asn1TooLong` for values that have none here) |
| `Asn1.identifier(t, cons)` | the identifier octets the encoder writes for a tag, primitive or constructed |
| `Asn1.conforms(r, n)` | whether rules `r` accept every element of `n` (forms and SET order) |
| `Asn1.span(n)`, `Asn1.spans(ns)` | two octets per element plus primitive contents: what a decoder must read at the least |
| `Asn1.bool(b)`, `Asn1.get_bool(r, n)`, `Asn1.get_bool_as(r, t, n)` | BOOLEAN |
| `Asn1.null()`, `Asn1.get_null(n)`, `Asn1.is_null(n)` | NULL |
| `Asn1.octets(o)`, `Asn1.octets_as(t, o)`, `Asn1.get_octets(r, n)`, `Asn1.get_octets_as(r, t, n)` | OCTET STRING (BER segments joined) |
| `Asn1Int{negative, magnitude}`, `Asn1.int(i)`, `Asn1.int_as(t, i)`, `Asn1.int_nat(n)`, `Asn1.get_int(n)`, `Asn1.get_int_as(t, n)`, `Asn1.get_nat(n)`, `Asn1.get_nat_as(t, n)`, `Asn1.int_of_content(o)`, `Asn1.int_content_ok(xs)` | INTEGER held as a number (six contents octets at most) |
| `Asn1.uint(o)`, `Asn1.get_int_bytes(n)`, `Asn1.get_int_bytes_as(t, n)`, `Asn1.get_uint_bytes(n)`, `Asn1.get_uint_bytes_as(t, n)` | INTEGER of any size as octets (two's complement contents, or the unsigned magnitude) |
| `Asn1.enum(i)`, `Asn1.get_enum(n)` | ENUMERATED |
| `Asn1Bits{unused, octets}`, `Asn1Bits.ok`, `.len`, `.bit(b, i)`, `.of_octets`, `.octets`, `.unused`; `Asn1.bits(b)`, `Asn1.bits_as(t, b)`, `Asn1.get_bits(r, n)`, `Asn1.get_bits_as(r, t, n)` | BIT STRING |
| `Asn1.oid_valid(arcs)`, `Asn1.oid_content(arcs)`, `Asn1.oid_of_content(o)`, `Asn1.oid(arcs)`, `Asn1.get_oid(n)` | OBJECT IDENTIFIER (arcs as `List<&2, Nat>`) |
| `Asn1StrKind` (`Asn1Utf8`, `Asn1Numeric`, `Asn1Printable`, `Asn1Teletex`, `Asn1Ia5`, `Asn1Visible`, `Asn1UniversalStr`, `Asn1Bmp`), `Asn1StrKind.tag`, `.of_tag`, `.num`; `Asn1Str{kind, octets}`, `Asn1Str.chars`, `.text`, `.valid`; `Asn1.get_string(r, n)`, `Asn1.get_string_as(r, t, k, n)`, `Asn1.string(s)`, `Asn1.utf8(text)`, `Asn1.text_string(k, text)`, `Asn1.utf8_decode(xs)`, `Asn1.utf8_encode(cs)`, `Asn1.points_text(cs)` | character strings |
| `Asn1Time{year, month, day, hour, minute, second, frac, zone}`, `Asn1Zone` (`Asn1Zulu`, `Asn1LocalTime`, `Asn1Offset{negative, hours, minutes}`); `Asn1Time.valid`, `.seconds`, `.cmp`, `.show`, `.zone`; `Asn1.utc_pivot()`; `Asn1.get_utc_time(r, pivot, n)`, `Asn1.get_gen_time(r, n)`, `Asn1.get_time(r, pivot, n)`, `Asn1.utc_of_content`, `Asn1.gen_of_content`; `Asn1.utc_time(t)`, `Asn1.gen_time(t)` | times |
| `Asn1.seq(xs)`, `Asn1.set(xs)`, `Asn1.set_of(xs)`, `Asn1.set_sorted(xs)`, `Asn1.explicit(n, x)`, `Asn1.implicit(t, x)`, `Asn1.get_seq(n)`, `Asn1.get_set(n)`, `Asn1.cons_as(t, n)`, `Asn1.get_explicit(n, x)`, `Asn1.has_tag(t, x)`, `Asn1.untag(t, u, x)`, `Asn1.prim_as(t, n)` | constructed values and tagging |
| `Asn1Schema` (`Asn1SAny`, `Asn1SElem`, `Asn1SSeq`, `Asn1SOf`, `Asn1SChoice`, `Asn1SExplicit`, `Asn1SOpt`, `Asn1SDefault`), `Asn1S.seq`, `.seq_of`, `.set_of`, `.elem`, `.any`, `.opt`, `.explicit`, `.ctx`, `.admits`, `.depth` | schemas |
| `Asn1.match(r, s, b)`, `Asn1.match_tlv(r, s, x)` | an element matched against a schema |
| `Asn1Match` (`Asn1MElem`, `Asn1MSeq`, `Asn1MChoice`, `Asn1MExplicit`, `Asn1MAbsent`, `Asn1MDefault`), `Asn1Match.items`, `.at(m, i)`, `.inner`, `.present`, `.tlv`, `.node`, `.raw` | matches |
| `Asn1Step` (`Asn1StepAt{index}`, `Asn1StepInner{}`), `Asn1Match.follow(m, path)` | the match reached by steps: a field (`at`), or inside an EXPLICIT tag or CHOICE (`inner`) |

Defs named `a1.*` are internal.

**Errors.** `Asn1Truncated` (the octets end inside an element),
`Asn1BadTag` (identifier octets not the fewest, 8.1.2; or a tag number
past the implementation's bound), `Asn1ReservedTag` ([UNIVERSAL 0] outside
end-of-contents, X.680 Table 1), `Asn1BadLength` (length octet FF,
8.1.3.5 c), `Asn1NonMinimalLength` (10.1), `Asn1Indefinite` (10.1),
`Asn1PrimIndefinite` (8.1.3.2 a), `Asn1NoEoc` and `Asn1BadEoc`
(end-of-contents missing, or where no indefinite contents end, 8.1.5),
`Asn1BadForm` (8.2.1 and the like, 10.2), `Asn1SetOrder` (10.3, 11.6),
`Asn1Trailing`, `Asn1Exhausted` (decoder fuel; cannot happen, as the fuel
exceeds the octets), `Asn1TooLong` (no length octets here: see Limits), and
the typed readers' and schemas' `Asn1Unexpected`, `Asn1BadValue`,
`Asn1BadInteger` (8.3.2), `Asn1Negative`, `Asn1BadBits` (8.6.2, 11.2),
`Asn1BadOid` (8.19), `Asn1BadString`, `Asn1BadTime`, `Asn1SchemaMismatch`,
`Asn1SchemaExtra`, `Asn1SchemaMissing`, `Asn1SchemaDefault` (11.5).

## Extension points

* **Rules** are a record of independent choices; BER, DER and anything
  between are values of it (for example DER with octets after the element
  allowed, `Asn1Rules.with_trailing`). A new restriction is one more field
  and one more check where elements are built (`a1.mk_prim`, `a1.mk_cons`)
  or in a typed reader.
* **SET order** is a parameter: none, the SET OF order or the SET order.
* **Types**: a new universal type is a reader over `Asn1.prim_as` or
  `Asn1.cons_as`; a new restricted string type is one more `Asn1StrKind`.
* **Schemas** are data: a new structure is a new `Asn1Schema` value. The
  schema layer is the counterpart of asn1_compiler's tables, and the
  `Asn1Match` tree the counterpart of its action callbacks: callers read
  the fields they need from it (as `x509` and `pkcs` do).
* **Time**: the UTCTime century (`pivot`, default `Asn1.utc_pivot()`) is
  a parameter; time zones are kept, and `Asn1Time.seconds` applies them.
* **The number bound** (`a1.max_octets`, number.bend) is one def; when
  Bend's run-time natural numbers grow past 2^48 it can grow with them.

## Laws

`LAWS.bend`, proved for **every** input:

* `decode_encode`: when `Asn1.encode(n)` answers `Done{b}` and `n` conforms
  to rules `r` (`Asn1.conforms`), `Asn1.decode(r, b)` answers `Done{n}`:
  decode(encode(v)) == v, under BER, DER and any rules between;
* `bit_string_conforms`, `octet_string_conforms`: a primitive BIT STRING
  or OCTET STRING conforms to every rules, so `decode_encode` applies to it
  under any rules;
* `encode_decode`: under any rules with `min_length` and without
  `indefinite` or `trailing`, when `Asn1.decode(r, b)` answers `Done{n}`,
  `Asn1.encode(n)` answers `Done{b}`: DER's encoding is unique, so decoding
  and encoding again gives back the input octets; `der_unique` is the same
  for `Asn1Rules.der()`;
* `decode_within`, `prefix_within`, `all_within`: a decode that succeeds
  never reads past its buffer: its elements' spans (two octets for each
  element's identifier and length, and every primitive element's contents)
  fit in the buffer, with the octets left after the element
  (`decode_prefix`);
* `oid_round_trip`, `oid_canonical`: OBJECT IDENTIFIER contents read back
  as the arcs written, and arcs read from contents are written back as the
  same contents (the fewest octets per subidentifier, X.690 8.19.2, is
  checked when reading);
* `read_split`, `read_all_split`: the octets kept for an element are the
  input's own: an element's octets (`Asn1Tlv.raw`) followed by the octets
  after it are exactly the input, and the octets of the elements of a run
  (`Asn1.raws`) join back to the input, under any rules;
* `contents_within`: an element's contents octets (`Asn1.contents`) are a
  slice of its octets; `items_split`: the octets of the elements inside a
  constructed element (`Asn1.items`) join to its contents octets;
* `read_der`: under rules with DER's length checks and without the
  indefinite form, an element's octets are its DER encoding
  (`Asn1.encode(node) == Done{raw}`): identifier, length and contents
  octets as X.690 writes them;
* `encode_retag`: re-tagging a constructed element with a tag of one
  identifier octet (not [UNIVERSAL 0]) changes only its identifier octets
  (`Asn1.identifier`); the vector `vec_identifier` gives [0] IMPLICIT's
  (A0) and SET's (31);
* schema matches: `match_tlv_tlv` (a match holds the element matched),
  `match_split`, `match_whole` (a match's octets are the input's first
  octets, all of them when the rules refuse octets after the element),
  `match_tlv_within`, `match_within` (the octets of the match reached by
  any steps `p ++ q` are a slice of those of the match reached by `p`),
  `match_input` (so a slice of the input), `match_der` (under DER's length
  checks, a match's octets are the DER encoding of its element),
  `match_of_node` (a SEQUENCE OF or SET OF match is of a constructed
  element of its tag), and `follow_nil`, `follow_at`, `follow_inner`,
  `at_items` (what `Asn1Match.follow` and `Asn1Match.at` reach). These are
  what x509 and pkcs build on to show that the octets a signature is
  checked over are a slice of the input;
* vectors from X.690: the SEQUENCE of 8.9.3, the tagging example of 8.14.4
  (Type3), the object identifier {2 999 3} of 8.19.5, the length 201 of
  8.1.3.5, and an indefinite-length SEQUENCE accepted by BER and refused by
  DER.

**How they are proved.** The decoder is one recursive def over a fuel
argument, given the header already read at each place (`A1Head`). Its
header reader checks the identifier octets, and under `min_length` the
whole header, by encoding the tag, form and length read again and comparing
(`a1.canon`): so a header accepted under DER is the encoder's header, and
law 2 follows by induction on the fuel (`proof_canon.bend`). Law 1 goes
element by element: identifier and length octets read back
(`proof_head.bend`, `proof_num.bend`: base-128 and big-endian numbers by
Horner's rule, single octets by `proof_byte.bend`'s closed computations),
contents are cut, and the rules' checks pass because the value conforms
(`proof_enc.bend`). The bounds (`proof_within.bend`) are Bool-valued
functions proved true of every header and every result. The proofs compute
through bytes' public `mask` and `byte` and use its interface laws.

The octets laws (`proof_split.bend`) rest on one fact proved for every
reader of a header (identifier octets, base-128 and big-endian numbers,
length octets, the canonical check): what it leaves (the contents and what
follows, or what follows the header) is the input's last octets. By
induction on the fuel, so is what the decoder leaves after the elements it
read, which makes an element read the input's first octets; and since the
contents octets are cut from what the header leaves, they are a slice of
any octets a header is read from (`contents_within` holds for every
`Asn1Tlv`, not only those read). Under DER, `read_der` takes
`proof_canon.bend`'s result that the elements decoded encode back to the
input. The matcher (`proof_match.bend`) is shown, by induction on its fuel,
to answer for an element matches holding that element, each field's match
holding one of the elements `Asn1.items` read from the contents (so within
the element's octets), to any depth; following steps stays within the
octets. bytes states no laws for appending `Octets` (associativity, the
empty string), for `take` and `drop` at offsets inside a join, or for
`Octets.at`; that is bytes' own batch of laws, and bytes has many
dependents, so the few facts needed here are proved privately in
`proof_oct.bend` from bytes' interface laws (`octets_of_to`,
`octets_to_of`, `octets_append_list`, `octets_concat_*`, `take_drop`).

### Schema matches conform (`LAWS_conform.bend`)

`LAWS_conform.bend` (with `PROOF_conform.bend`), proved for **every**
rules, schema and input: `match_tlv_conforms` and `match_conforms`, every
match `Asn1.match_tlv` or `Asn1.match` answers conforms to its schema
(`asn1law.conf`, defined in the law file, true at some fuel: the fuel
bounds the nesting). Conforming means having the schema's shape all the way
down: an `Asn1SAny` match is an element's, an `Asn1SElem` one an element's
of its tag; an `Asn1SSeq` match is a constructed element of its tag with one
match per field, in order, each conforming to its field; an `Asn1SOf` match
the same with every match conforming to the item; a CHOICE's match conforms
to one of its alternatives; an EXPLICIT match is a constructed `[num]`
element whose match conforms to the inner schema; an OPTIONAL field is
absent or conforms, a DEFAULT field is absent (holding its default value)
or conforms. With the vector `vec_conforms` (X.690 8.9.3's SEQUENCE).

**How it is proved.** By induction on the matcher's fuel, every answer of
each work item (`A1Work`) is what it must be, at conformance fuel twice the
matcher's: each way the matcher builds an answer (a slot and the rest, a
present or absent field, each schema form) is a lemma over the answers it
builds from. A sequence's slots carry its fields in order, a SEQUENCE OF's
slots all carry the item, the alternative a CHOICE picks is one of its
alternatives, and more fuel never hurts. `gen/gen_conform.py` writes the
proof (its cases repeat over the schema and match constructors).

### The typed readers and writers (`LAWS_typed.bend`)

`LAWS_typed.bend` (with `PROOF_typed.bend`, checked in a process of its
own), proved for **every** input. Reading what a writer writes gives the
value back:

* `bool_round_trip`, `null_round_trip`, `octets_round_trip` (any tag),
  under any rules;
* `int_round_trip` (any tag), `enum_round_trip`, `nat_round_trip`: every
  integer whose contents take six octets or fewer (the reader's bound, see
  Limits) other than -0, which the writer writes as 0 (`Asn1Int{True, 0}`
  reads back as `Asn1Int{False, 0}`);
* `bits_round_trip`: a well-formed bit string (`Asn1Bits.ok`) whose
  unused bits are zero (`asn1law.bits_clear`, defined in the law file:
  the low unused bits of the last octet), under any rules;
  `bits_ber_round_trip`: any well-formed one under rules without the
  values checks; `bits_octets_round_trip`: `Asn1Bits.of_octets(o)` under
  any rules;
* `string_round_trip`, `string_implicit_round_trip`: an `Asn1Str` of any
  of the eight types whose octets are valid for it (`Asn1Str.valid`), with
  its universal tag or an IMPLICIT tag, under any rules;
* `utc_round_trip`, `time_utc_round_trip` (through `Asn1.get_time`): a
  valid time (`Asn1Time.valid`) in Zulu time with no fraction, whose year
  is one a UTCTime's two digits stand for under the century rule
  (`asn1law.utc_year(yy, pivot)`: 20yy below the pivot, 19yy from it), for
  any pivot; `gen_round_trip`, `time_gen_round_trip`: the same for a
  GeneralizedTime of any year below 10000 (written as century and year);
* `seq_round_trip`, `set_round_trip`, `cons_round_trip`,
  `explicit_round_trip`, `implicit_round_trip` (`Asn1.untag` of an IMPLICIT
  element gives the element with its own tag), `implicit_tag`.

What the readers accept: under DER's checks, exactly what the writers
write, and only values their checks pass:

* `bool_canonical` (under the values rule: an element read as BOOLEAN is
  `Asn1.bool` of the value read, so its octet is 00 or FF), `null_canonical`;
* `int_canonical` (any tag), `enum_canonical`, `nat_canonical`: an
  element read as INTEGER is `Asn1.int_as` of the integer read: the reader
  takes contents in the fewest octets only (X.690 8.3.2), under any rules;
* `octets_canonical`, `bits_canonical`, `string_canonical`,
  `string_implicit_canonical`: under the primitive-only rule (DER 10.2),
  the element read is the writer's element for the value read (for a bit
  string, its leading octet is the count of unused bits);
* `string_valid`, `string_implicit_valid`: a string read is valid for its
  type (`Asn1Str.valid`: the character checks of every type); `utc_valid`,
  `gen_valid`, `time_valid`: a time read is valid (`Asn1Time.valid`: month
  1 to 12, a day its month has in the Gregorian calendar, hour below 24,
  minute and second below 60, an offset below 24 hours and 60 minutes);
  `utc_zulu`, `gen_zulu`, `time_zulu`: under the values rule, in Zulu
  time;
* `cons_canonical`, `seq_canonical`, `set_canonical`, `explicit_canonical`;
* `numeric_chars`, `printable_chars`, `ia5_chars`, `visible_chars`: a
  NumericString, PrintableString, IA5String or VisibleString is valid
  exactly when every octet is in X.680's table of its characters, given in
  the law file as lists of octets (`asn1law.numeric_chars`: Table 9's
  digits and space; `asn1law.printable_chars`: Table 10's letters, digits,
  space and `'()+,-./:=?`; `asn1law.ia5_chars`: the 128 characters of
  ISO 646; `asn1law.visible_chars`: its graphic characters and space);
  `teletex_chars`: every TeletexString is valid (its octets are taken as
  code points, see Limits);
* `utc_canonical`: under DER's value and primitive-only rules, a UTCTime
  element read is `Asn1.utc_time` of the time read (YYMMDDhhmmssZ, exactly
  the writer's characters); `gen_canonical`: the same for GeneralizedTime
  when the time read has no fraction of a second.

**How they are proved.** Contents are related to numbers through
bend-osdev-u32's value laws (`u32_le_value`, `u32_sub_value`,
`u32_value_eq` and the like): an octet of an `Octets` is the octet the
writer puts down for its value (`proof_intc.bend`), and a digit character
is the writer's character for its value (`proof_tstrict.bend`). INTEGER
(`proof_int.bend`, `proof_intc.bend`): a number's digits in base 256 have
no leading zero, so the writer's contents pass the fewest-octets check and
read back by Horner's rule; conversely the digits of the value of
canonical digits are those digits (division by 256 being unique), which
makes the contents read the writer's (and the same for the complemented
octets of a negative integer). The character tables (`proof_chars.bend`,
generated by `gen/gen_chars.py`) split an octet's eight bits one at a time,
so each of the 256 octets is a closed computation of the four checks and
the four tables. Times (`proof_clock.bend`): each field is
two digits (`proof_d2.bend`: for each number below 100, a closed
computation); a valid time's fields are below 100; division by 100 is
unique, so the year comes back. The strictness of the time readers
(`proof_tstrict.bend`) follows the reader through deep patterns over the
twelve (UTCTime) or fourteen (GeneralizedTime) digit characters: under DER
the seconds must be present, the zone is Z (an offset is not Zulu time,
`pd.off_nz`), and a fraction makes the time read one with a fraction.

**Not stated as laws** (tested only): the UTF-8 encoder and decoder
(`Asn1.utf8_encode`, `Asn1.utf8_decode`, `Asn1.utf8`: their round trip is
arithmetic on code points with shifts, out of reach here), the
one-octet-per-character writer `Asn1.text_string` (whose octets are its
characters' code points, masked), the large-integer octet readers
(`Asn1.get_int_bytes`, `Asn1.uint`, `Asn1.get_uint_bytes`), BER's
constructed strings and bit strings (segments joined; the writers write
the primitive form only), `Asn1.set_of` and `Asn1.set_sorted` (that the
sorted elements are in DER's order), GeneralizedTime's strictness for a
time read with a fraction of a second (the writer drops trailing zeros of
the fraction, so it would need the digit run and its trimming related),
the checks of BMPString, UniversalString and UTF8String (no surrogates,
at most U+10FFFF, RFC 3629's UTF-8; they read pairs, quadruples or UTF-8
sequences of octets as code points), and of the schema matcher's
answers (which conform to their schemas, `LAWS_conform.bend`), the three
checks conformance does not state: that a CHOICE's index is that of the
first alternative whose tags admit the element, that a DEFAULT field
present under the values rule differs from its default, and that a SET
OF's elements are in DER's order.
`contents_within` places the contents octets inside an element's octets,
not at a stated offset: under DER, `read_der` gives the exact layout (the
encoder's identifier and length octets, then the contents); under BER no
law names it (identifier and length octets, contents, then end-of-contents
octets after indefinite contents), because `Asn1.contents` reads the
header again from the element's own octets, and that this second read
agrees with the decoder's read from the whole input (each header reader
depends only on the octets it consumes) is not proved. Elements inside a
constructed element are not stated to be their DER encodings (`read_der`
covers the element read; a match's fields are covered only through
`match_within`).

## Tests

* `check.bend`: X.690's examples (8.9.3, 8.14.4's Type1 to Type5, 8.19.5,
  8.6.4.2's primitive and constructed BIT STRING, 8.1.3.5's L = 201), every
  decoding error, BER against DER on indefinite lengths, non-minimal
  lengths, constructed strings, SET order and trailing octets; INTEGER from
  -65536 to 2^48, BOOLEAN, NULL, OCTET STRING, BIT STRING, object
  identifiers (with the bound), UTF-8 (overlong forms, surrogates, past
  U+10FFFF), PrintableString, IA5String, BMPString, UniversalString,
  NumericString; UTCTime and GeneralizedTime (X.680's and X.690's examples,
  leap days, offsets, DER's forms); and schemas with OPTIONAL, EXPLICIT,
  IMPLICIT, SET OF, CHOICE and DEFAULT fields, and their errors.
* `ref/run.sh` (227 cases with the default seed): random element trees with
  every class, high tag numbers and contents to 400 octets, encoded by a
  model of X.690 written in `ref/gen.py`; each DER encoding is also parsed
  by `openssl asn1parse` (OpenSSL 3.0.13 here), whose element structure
  (offsets, depth, header and contents lengths, forms) must be the model's.
  The package must decode each input under DER and BER to the model's tree
  and encode it back to the model's DER; a BER encoding of each tree (long
  lengths, indefinite lengths) must be refused by DER and decoded by BER;
  each input cut short (which openssl refuses too) and with an octet after
  it must be refused; and fixed cases (X.690's examples, a length octet FF,
  a length past the end, a non-minimal high tag, end-of-contents at the top,
  a primitive indefinite length, a SET out of order, a constructed string).
  It exits 77 without python3 or openssl.

## Limits

* Bend's natural numbers are immediate values below 2^48 at run time (a
  larger one stops the program). So a high tag number and an object
  identifier's subidentifier are read from at most six base-128 octets
  (below 2^42), and a length from at most six octets; longer ones are
  refused (`Asn1BadTag`, `Asn1BadOid`, `Asn1TooLong`) and not encoded.
  INTEGER values are read as numbers from at most six octets
  (`Asn1TooLong` otherwise) and as octets of any size. Object identifiers
  with larger arcs (for example 2.25 UUID arcs) are refused.
* GeneralizedTime fractions of an hour or minute are not read; fractions of
  a second are.
* TeletexString octets are taken as code points 0 to 255 (the T.61
  repertoire is not mapped). REAL, RELATIVE-OID and the TIME types are not
  read (their elements decode generically).
* Decoding works on the buffer's octets as a list, and each constructed
  element's contents are cut into their own list, so the work is the
  octets times the nesting depth.

## Dependencies

`bend-osdev-bytes` (buffers are `Octets`); `bend-osdev-u32` (its value
laws, in the proofs of `LAWS_typed.bend` only).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (32 laws), `--verdict` ALL
PROOFS CHECK (0.43 GB peak); `PROOF_typed.bend` ALL PROOFS CHECK (49
laws), `--verdict` ALL PROOFS CHECK (0.57 GB peak, a minute); `check.bend`
passes, `ref/run.sh` 227 cases (60 against openssl asn1parse) match,
`scripts/deps.sh asn1` ok; `gen/gen_digits.py --check`,
`gen/gen_tstrict.py --check` and `gen/gen_chars.py --check` ok.
`PROOF_conform.bend` ALL PROOFS CHECK and `--verdict` ALL PROOFS CHECK on
Bend 2.0.39 (about 1 s, 0.18 GB peak), `gen/gen_conform.py --check` ok.
