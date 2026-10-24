# bend-osdev-x509

X.509 v3 certificates as RFC 5280 profiles them: the DER of a certificate
read into its fields, keeping the exact octets the issuer signed (the
tbsCertificate) and the octets of each name, algorithm identifier, key and
extension; every check the profile asks of a reader a rule; names compared
as RFC 5280 7.1 says, or by their octets; and the extension points a path
validator and a signature scheme plug into. The counterpart of Linux's
crypto/asymmetric_keys X.509 parser, written from RFC 5280 and the ITU-T
Recommendations; no kernel source was read.

## Specifications

* RFC 5280, *Internet X.509 Public Key Infrastructure Certificate and
  Certificate Revocation List (CRL) Profile* (May 2008)
  (https://www.rfc-editor.org/rfc/rfc5280.txt): 4.1 (the certificate's
  ASN.1), 4.1.1.2 (signatureAlgorithm the same as the signature field),
  4.1.2.1 (versions), 4.1.2.2 (serial numbers: positive, at most 20
  octets; users SHOULD handle others), 4.1.2.4 (a non-empty issuer),
  4.1.2.5, 4.1.2.5.1 and 4.1.2.5.2 (UTCTime through 2049, GeneralizedTime
  from 2050, Zulu time with seconds, no fractions; YY of 50 or more is
  19YY), 4.1.2.7 (SubjectPublicKeyInfo), 4.1.2.8 (unique identifiers only in
  v2 and v3), 4.1.2.9 (extensions only in v3, one or more), 4.2 (no
  extension twice; a certificate-using system must reject an unrecognized
  critical extension), 4.2.1.1 (authorityKeyIdentifier), 4.2.1.2
  (subjectKeyIdentifier), 4.2.1.3 (keyUsage's bits), 4.2.1.6
  (subjectAltName, GeneralName; iPAddress four or sixteen octets),
  4.2.1.9 (basicConstraints), 4.2.1.12 (extKeyUsage), 6.1 (self-issued),
  7.1 (comparing names), section 8 (binary comparison at a minimum), and
  Appendix A (A.1's module with EXPLICIT TAGS, A.2's with IMPLICIT TAGS).
* RFC 4518, *Lightweight Directory Access Protocol (LDAP): Internationalized
  String Preparation* (June 2006)
  (https://www.rfc-editor.org/rfc/rfc4518.txt): 2.2 (case folding, by RFC
  3454 B.2) and 2.6.1 (insignificant space handling), the steps of RFC
  5280 7.1's comparison done here.
* ITU-T Recommendation X.680 (02/2021) 31.2.7 (a tagged CHOICE is
  explicit: GeneralName's directoryName), through bend-osdev-asn1, which
  reads and writes the DER (X.690 (02/2021)).

## What it implements

* **Parsing** (`x509.bend`): `X509.parse(rules, octets)` matches the
  certificate against its ASN.1 (`schema.bend`, as bend-osdev-asn1
  schemas) and reads every field: version, serial number (its octets, any
  size), signature algorithm, issuer, validity, subject, public key,
  unique identifiers, extensions, the outer algorithm and the signature.
  The tbsCertificate's octets are kept exactly as read.
* **Rules** (`rules.bend`), each a field of `X509Rules`: the encoding rules
  (DER), the UTCTime century, the time profile, matching signature
  algorithms, versions against fields, distinct extensions, well-formed
  known extensions, refusing unknown critical extensions, the serial
  number's profile, a non-empty issuer. `X509.rules()` is RFC 5280 as a
  certificate user reads it (everything but the last two checks, which
  4.2 and 4.1.2.2 leave to the validator and to graceful handling);
  `X509.rules_strict()` adds them; `X509.rules_lenient()` reads BER and
  checks nothing.
* **Names** (`name.bend`): RDNs of attribute type and value; values stay
  elements (directory strings or any other type).
* **Comparing names** (`namecmp.bend`): `X509NameRules{fold_case, spaces,
  kinds}`. `X509.name_rules()` is RFC 5280 7.1's comparison as far as it is
  done here: letters A to Z folded (RFC 4518 2.2), insignificant spaces
  (RFC 4518 2.6.1), PrintableString and UTF8String compared by their
  characters, RDN attributes in any order; `X509.name_rules_binary()`
  compares the names' DER octets.
* **Times** (`validity.bend`): both ends as `Asn1Time`, each with which
  type it was; `X509Validity.contains(v, t)`.
* **Keys** (`spki.bend`): the algorithm, the key's BIT STRING, and the
  SubjectPublicKeyInfo's octets.
* **Extensions** (`ext.bend`): every extension with its identifier, critical
  flag, value octets and exact octets; read here (`extval.bend`):
  basicConstraints, keyUsage, subjectKeyIdentifier, authorityKeyIdentifier,
  subjectAltName and extKeyUsage, with GeneralName (`gname.bend`).
* **Extension points** (`verify.bend`): the signature check through
  bend-osdev-crypto's signature interface, and name links for a path.

## Files

| File | Holds |
|---|---|
| `x509.bend` | the entry file: `X509Tbs`, `X509Cert`, `X509.parse`, the checks |
| `error.bend` | `X509Error`, and results of asn1's readers as x509's |
| `rules.bend` | `X509Rules` and its named defaults |
| `schema.bend` | the certificate's ASN.1 as bend-osdev-asn1 schemas |
| `alg.bend` | AlgorithmIdentifier |
| `name.bend` | Name |
| `namecmp.bend` | comparing names |
| `validity.bend` | Validity and the time profile |
| `spki.bend` | SubjectPublicKeyInfo |
| `ext.bend` | Extension, finding and duplicates |
| `extval.bend` | the six extensions read here |
| `gname.bend` | GeneralName |
| `verify.bend` | the signature check and name links (extension points) |
| `LAWS.bend`, `PROOF.bend`, `proof_x509.bend`, `proof_octets.bend` | the laws, their proofs, lemmas (`proof_octets.bend`: the octets a parse keeps) |
| `LAWS_ext.bend`, `PROOF_ext.bend` | the laws of the extension readers, and their proofs |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh`, `ref/show.bend.in` | the differential test (`ref/.gitignore` lists what it generates) |

## API

| Def or type | Meaning |
|---|---|
| `X509Rules{asn1, pivot, time_profile, alg_match, versions, distinct_ext, known_ext, unknown_critical, serial, issuer_nonempty}` and its field readers; `X509.rules()`, `X509.rules_strict()`, `X509.rules_lenient()` | what a parse accepts |
| `X509.parse(r, b)` | the certificate whose DER is `b` |
| `X509Cert{tbs, sig_alg, sig, raw}`; `X509Cert.tbs`, `.sig_alg`, `.signature` (`Asn1Bits`), `.signature_octets`, `.raw`, `.tbs_raw`, `.issuer`, `.subject`, `.serial`, `.validity`, `.spki`, `.extensions`, `.extension(c, id)` | a certificate (open type) |
| `X509Tbs{...}`; `X509Tbs.version` (0 for v1, 2 for v3), `.serial` (INTEGER contents octets), `.signature`, `.issuer`, `.validity`, `.subject`, `.spki`, `.issuer_uid`, `.subject_uid`, `.extensions`, `.has_extensions`, `.raw` | the tbsCertificate (open type) |
| `X509Cert.conforms(r, c)`; `X509.serial_ok(o)` | whether a certificate passes the checks of `r`; the serial number profile |
| `X509Error` (`X509Asn1{error}`, `X509BadVersion`, `X509BadSerial`, `X509BadAlgorithm`, `X509AlgMismatch`, `X509BadName`, `X509EmptyIssuer`, `X509BadTime`, `X509BadKey`, `X509BadUniqueId`, `X509EmptyExtensions`, `X509BadExtension{id}`, `X509DuplicateExtension{id}`, `X509UnknownCritical{id}`), `X509Error.name` | why a certificate was refused |
| `X509AlgId{oid, params, raw}`, `.oid`, `.params`, `.raw`, `.is_eq`; `X509AlgId.of_match(m)` | algorithm identifiers (open type); one read from a match against `X509.schema_alg()` |
| `X509Name{rdns, raw}`, `X509Atv{attr, value}`; `X509Name.rdns`, `.raw`, `.is_empty`, `.show`, `X509Name.of_match(m)`; `X509Atv.attr`, `.value`, `.show` | names (open types); one read from a match against `X509.schema_name()` |
| `X509.schema_alg()`, `X509.schema_name()` | AlgorithmIdentifier and Name as bend-osdev-asn1 schemas, for structures that hold them |
| `X509NameRules{fold_case, spaces, kinds}`, `X509.name_rules()`, `X509.name_rules_binary()`; `X509Name.matches(r, a, b)`, `X509Name.key(r, n)` | comparing names |
| `X509Validity{not_before, not_after}`, `X509Time{time, utc}`; `X509Validity.not_before`, `.not_after`, `.contains(v, t)`, `.profile_ok`; `X509Time.time`, `.utc`, `.profile_ok` | validity |
| `X509Spki{alg, key, raw}`, `.alg`, `.key`, `.raw`, `.key_octets` | public keys |
| `X509Ext{id, critical, value, raw}`, `.id`, `.critical`, `.value`, `.raw`; `X509.find_ext(es, id)`, `X509.duplicate_ext(es)`, `X509.is_known_ext(id)` | extensions |
| `X509.id_basic_constraints()`, `.id_key_usage()`, `.id_subject_key_id()`, `.id_authority_key_id()`, `.id_subject_alt_name()`, `.id_ext_key_usage()` | their identifiers |
| `X509BasicConstraints{ca, path_len}`, `X509.basic_constraints_of(r, e)`; `X509.key_usage_of(r, e)`, `X509.key_usage_bits(b)`; `X509.subject_key_id_of(r, e)`; `X509Aki{key_id, issuer, serial}`, `X509.authority_key_id_of(r, e)`; `X509.subject_alt_name_of(r, e)`; `X509.ext_key_usage_of(r, e)` | the extensions read here |
| `X509GeneralName` (`X509GnOther{type_id, value}`, `X509GnEmail`, `X509GnDns`, `X509GnX400`, `X509GnDir`, `X509GnEdi`, `X509GnUri`, `X509GnIp`, `X509GnRid`), `X509.general_name(r, n)`, `X509.general_names(r, ns)`, `X509GeneralName.show` | GeneralName (open type) |
| `X509.verify_with(~PK, ~pk_of, ~verify, key, c)`, `X509.verify_by(~PK, ~pk_of, ~verify, issuer, c)` | the signature check (extension point) |
| `X509.issued_by(r, child, parent)`, `X509.names_chain(r, cs)`, `X509.self_issued(r, c)` | name links (extension point) |

Defs named `x5.*` are internal.

## Extension points

* **Signature schemes**: `X509.verify_with` takes a scheme's `~PK`, `~pk_of`
  and `~verify`, as bend-osdev-crypto's signature interface
  (`crypto/sign.bend`) defines them, and checks the signature octets over
  exactly the tbsCertificate's octets. A scheme for a signature algorithm
  (chosen by `X509AlgId.oid`, with the registry's names in bend-osdev-oid)
  plugs in there when crypto has one; `verify_signed_if` holds for every
  scheme that satisfies crypto's laws.
* **Path validation** (RFC 5280 section 6): not done here. A validator
  builds on `X509.names_chain` (or `X509.issued_by`) under the name rules it
  chooses, `X509.verify_by` for each link, `X509Validity.contains` for the
  time, the parsed basicConstraints, keyUsage and extKeyUsage, and
  `X509.is_known_ext` to reject unrecognized critical extensions (or
  parses with `X509.rules_strict()`).
* **More extensions**: every extension is kept with its value octets; one
  more is a decoder over `X509Ext.value` and an entry in `x5.kind` (to take
  part in `known_ext` and `unknown_critical`).
* **Rules** are a record: a new check is a field and one more line in
  `x5.conform`.

## Laws

`LAWS.bend`, proved for **every** input:

* `parsed_conforms`: a certificate `X509.parse(r, b)` answers passes every
  check of `r` (`X509Cert.conforms(r, c)`): the checks are the parse's last
  step;
* `verify_signed_if`: for every signature scheme satisfying crypto's
  `pk_format` and `accepts` laws (as hypotheses, as crypto's own
  `sign_verify_bytes_if` takes them), a certificate whose signature octets
  are the issuer's signature of its tbsCertificate octets verifies under
  the issuer's public-key bytes;
* `name_match_refl`: every name matches itself, under any name rules (from
  bytes' `octets_is_eq_refl`);
* `name_match_binary`: under binary rules, names match exactly when their
  octets are the same;
* `find_ext_id`: `X509.find_ext` answers only an extension with the
  identifier asked for;
* `cert_split`, `cert_whole`: the certificate's octets
  (`X509Cert.raw`) are the input's first octets, and all of them when the
  rules' asn1 rules refuse octets after the certificate (as
  `X509.rules()`'s DER does);
* `tbs_slice`, `tbs_within`: the tbsCertificate's octets
  (`X509Cert.tbs_raw`), which `X509.verify_with` checks the signature
  over, are a slice of the input, inside the certificate's octets: the
  signature is checked over exactly octets that were in the input;
* `sig_alg_within`: the outer signatureAlgorithm's octets are a slice of
  the certificate's; `issuer_within`, `subject_within`, `spki_within`,
  `tbs_alg_within`, `ext_within`: the issuer's and subject's octets (which
  binary name comparison and name chaining use), the
  SubjectPublicKeyInfo's, the inner signature algorithm's and each
  extension's octets are slices of the tbsCertificate's octets, so are
  covered by the signature;
* vector: "Example  Org" as a PrintableString matches "example org" as a
  UTF8String under RFC 5280 7.1's comparison and not under binary.

**How the octets laws are proved** (`proof_octets.bend`): `X509.parse`
matches the input against `x5.s.cert()` with bend-osdev-asn1's matcher
and reads each field from a field's match; following each step of the
readers' Result chains (`xq.then`) shows that the octets kept for the
certificate, the tbsCertificate, the names, the algorithm identifiers, the
key and each extension are the octets of the matches at those fields.
asn1's laws `match_split`, `match_whole`, `match_within` and `match_input`
then make them slices, one inside another as the certificate's ASN.1
nests them.

`LAWS_ext.bend` (with `PROOF_ext.bend`, checked in a process of its own),
proved for **every** input: an extension whose value octets are the DER
that bend-osdev-asn1's encoder writes for a value reads back as that value,
under any rules:

* `key_usage_round_trip`: keyUsage, for every well-formed BIT STRING
  whose unused bits are zero (asn1's `asn1law.bits_clear`, the form DER
  gives a named bit list);
* `subject_key_id_round_trip`: subjectKeyIdentifier, for every OCTET
  STRING.

Each follows from asn1's `decode_encode` (a primitive BIT STRING or OCTET
STRING conforms to every rules) and its typed-reader round trips
(`bits_round_trip`, `octets_round_trip`, in asn1's `LAWS_typed.bend`).

**Not stated as laws** (tested only): the other extension decoders.
basicConstraints and authorityKeyIdentifier are read through the schema
matcher (`Asn1.match`), whose answers asn1 states laws for only as to the
octets and elements they keep, not the fields they find (asn1's
README, Laws); subjectAltName reads GeneralNames, which have no writer
here to state a round trip against; extKeyUsage reads each purpose with
bend-osdev-oid's `Oid.of_node`, which oid states no law for at the element
level (its laws are for DER octets and text). Nor are the values read from
the certificate's other fields (the version, serial number, validity times,
unique identifiers, the names' attribute values, the key and signature BIT
STRINGs) stated: asn1's typed-reader laws now cover each reader, but a law
for a field would also need the matcher's laws for the field's place in the
certificate's schema. `ref/run.sh` compares every field with Python
cryptography's and OpenSSL's reading. That the tbsCertificate's octets are
its DER encoding (beyond being a slice of the input that a DER certificate
holds) is not stated: asn1's `read_der` covers the element read, not the
elements inside it.

## Tests

* `check.bend`: an Ed25519 CA certificate from OpenSSL with every
  extension read here, under the three rule sets; refusals: an octet after
  it, cut short, a duplicate extension, an unknown critical extension
  (refused only by the strict rules), extensions in a v1 certificate, an
  empty issuer, a GeneralizedTime before 2050, a malformed basicConstraints,
  different signature algorithms, a negative serial number (refused only
  by the strict rules), each accepted by the lenient rules; serial numbers
  against 4.1.2.2; name comparison under the three kinds of rules
  (spaces, case, string types, all-space values); the name links and the
  signature extension point with a stand-in scheme.
* `ref/run.sh` (323 cases with the default seed, about a minute), against
  Python cryptography 41.0.7 and OpenSSL 3.0.13: 26 certificates (RSA with
  PKCS #1 v1.5 and PSS, ECDSA P-256 and P-384, Ed25519 and Ed448 keys; CA
  and leaf pairs from `cryptography`, one from `openssl req -x509` and a
  v1 from `openssl x509 -req`), with random names (PrintableString,
  UTF8String with non-ASCII text, IA5String, multi-valued RDNs), UTCTime
  and GeneralizedTime, serial numbers to 159 bits, and random
  basicConstraints, keyUsage, subjectKeyIdentifier, authorityKeyIdentifier
  (with issuer and serial), subjectAltName (DNS, email, IPv4, IPv6, URI,
  directory name, registered ID, other name), extKeyUsage and unknown
  extensions, critical or not. Every field the package answers (version,
  serial, both algorithms, names, times, the SubjectPublicKeyInfo octets,
  each extension's identifier, flag, value octets and decoded value, the
  tbsCertificate octets and the signature) must equal `cryptography`'s
  reading, and OpenSSL must agree with `cryptography` on the serial
  number, the times, the version, basicConstraints and keyUsage, and the
  element lengths. Each certificate is also read under the strict rules
  (unknown critical extensions refused) and leaves against their issuer
  (`X509.issued_by`). Then 207 inputs that are not DER: cut short, a length
  past its element, a serial number with a leading zero (refused by both
  tools, 79 inputs); an octet after the certificate, a non-minimal length
  outside or inside, the indefinite form, a critical flag of 01 or an
  encoded FALSE (refused by `cryptography`, accepted by OpenSSL, which
  reads BER and ignores trailing octets: 128 inputs). The package refuses
  every one under its default rules, and under the lenient rules reads the
  BER forms of the outer length as the original. It exits 77 without
  python3, openssl or cryptography.

## Limits

* Name preparation folds A to Z only and does not do RFC 4518's other
  steps (mapping, Form KC, prohibited characters); other values compare by
  their octets. Names whose values differ only by those steps do not
  match.
* bend-osdev-asn1's bounds apply: tag numbers, lengths and object
  identifier subidentifiers below 2^42 (no certificate comes near); INTEGER
  values are kept as octets of any size, but pathLenConstraint is read as
  a number (six octets at most).
* CRLs, attribute certificates and certificate requests are not read.
* A certificate about 1 KB long takes a fraction of a second; the decoder
  reads each nesting level's contents again (asn1's Limits).

## Dependencies

`bend-osdev-bytes` (octets), `bend-osdev-asn1` (DER and schemas),
`bend-osdev-oid` (object identifiers and their names), `bend-osdev-crypto`
(the signature interface).

## Status

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK (16 laws), `--verdict` ALL
PROOFS CHECK (0.82 GB peak); `PROOF_ext.bend` ALL PROOFS CHECK (2 laws),
`--verdict` ALL PROOFS CHECK (0.85 GB peak, a minute); `check.bend`
passes, `ref/run.sh` 323 cases match, `scripts/deps.sh x509` ok.
