# bend-osdev-pkcs

Signed messages and private keys: CMS SignedData (RFC 5652, of which
PKCS #7 v1.5's SignedData, RFC 2315, is version 1) read into its fields,
with each signer's exact signed octets, and unencrypted PKCS #8 private
keys (RFC 5208's PrivateKeyInfo, RFC 5958's OneAsymmetricKey). Signatures
are checked through bend-osdev-crypto's signature interface, digests by a
function the caller gives. The counterpart of Linux's
crypto/asymmetric_keys PKCS #7 and PKCS #8 parsers, written from the RFCs;
no kernel source was read.

## Specifications

* RFC 5652, *Cryptographic Message Syntax (CMS)* (September 2009)
  (https://www.rfc-editor.org/rfc/rfc5652.txt): section 1 (CMS values in
  BER), 5.1 (SignedData; its version), 5.2 (EncapsulatedContentInfo;
  eContent absent for an external signature), 5.3 (SignerInfo; its
  version; signedAttrs in DER, present when the content is not id-data,
  holding content-type and message-digest), 5.4 (what is digested and
  signed: the content's octets, or the signed attributes' DER with the
  EXPLICIT SET OF tag), 10.2.1 and 10.2.2 (RevocationInfoChoice,
  CertificateChoices), 10.2.5 (CMSVersion), 11.1 and 11.2 (content-type
  must match eContentType; message-digest is an OCTET STRING; each one
  value), 12.1 (the module, IMPLICIT TAGS).
* RFC 2315, *PKCS #7: Cryptographic Message Syntax Version 1.5* (March
  1998) (https://www.rfc-editor.org/rfc/rfc2315.txt): 9.1 (SignedData,
  version 1), 9.2 (SignerInfo), 9.3 (the same digesting of attributes).
* RFC 5208, *Public-Key Cryptography Standards (PKCS) #8: Private-Key
  Information Syntax Specification Version 1.2* (May 2008)
  (https://www.rfc-editor.org/rfc/rfc5208.txt): PrivateKeyInfo, version 0.
* RFC 5958, *Asymmetric Key Packages* (August 2010)
  (https://www.rfc-editor.org/rfc/rfc5958.txt), section 2:
  OneAsymmetricKey, attributes [0], publicKey [1], IMPLICIT TAGS, v2 when
  the public key is present.
* RFC 8410, *Algorithm Identifiers for Ed25519, Ed448, X25519, and X448
  for Use in the Internet X.509 Public Key Infrastructure* (August 2018)
  (https://www.rfc-editor.org/rfc/rfc8410.txt), section 7:
  CurvePrivateKey, the raw key as an OCTET STRING inside privateKey.
* Through bend-osdev-asn1 (X.690 (02/2021): BER and DER) and
  bend-osdev-x509 (Name, AlgorithmIdentifier, certificates).

## What it implements

* **SignedData** (`pkcs.bend`): `Cms.parse(rules, octets)` reads a
  ContentInfo holding a SignedData: version, digest algorithms, the
  encapsulated content type and content (BER's constructed OCTET STRINGs
  joined; none for a detached signature), each certificate's and CRL's
  octets, and the signers.
* **SignerInfo** (`signer.bend`): version, identifier (issuer and serial
  number, or subject key identifier), digest algorithm, signed attributes
  with their exact octets, signature algorithm, signature, unsigned
  attributes. **Attributes** (`attr.bend`): type, values, octets.
* **Rules** (`rules.bend`), each a field of `PkcsRules`: the encoding rules
  (BER), signed attributes in DER, the required attributes, versions, and
  digest algorithms listed. `Pkcs.rules()` is RFC 5652's requirements;
  `Pkcs.rules_strict()` adds its recommendation; `Pkcs.rules_lenient()`
  checks nothing.
* **Signed octets and checks** (`signed.bend`): `Cms.signed_message` (5.4),
  `Cms.verify_with` (crypto's interface), `Cms.message_digest`,
  `Cms.digest_matches` (with the caller's digest function),
  `Cms.signer_certificate` (the certificate a signer names).
* **PKCS #8** (`p8.bend`): `Pkcs8.parse`: version, algorithm, private key
  octets, attributes, public key; `Pkcs8.curve_private_key` for the RFC
  8410 curves.

## Files

| File | Holds |
|---|---|
| `pkcs.bend` | the entry file: `CmsSignedData`, `Cms.parse`, the checks |
| `error.bend` | `PkcsError`, and results of other packages' readers as pkcs's |
| `rules.bend` | `PkcsRules` and its named defaults |
| `schema.bend` | the ASN.1 types as bend-osdev-asn1 schemas |
| `attr.bend` | Attribute |
| `signer.bend` | SignerInfo and SignerIdentifier |
| `signed.bend` | signed octets, the signature and digest checks, the signer's certificate |
| `p8.bend` | PKCS #8 keys |
| `LAWS.bend`, `PROOF.bend`, `proof_pkcs.bend`, `proof_octets.bend` | the laws, their proofs, lemmas (`proof_octets.bend`: the octets a parse keeps) |
| `check.bend` | examples, with their expected output |
| `ref/gen.py`, `ref/run.sh`, `ref/show.bend.in` | the differential test (`ref/.gitignore` lists what it generates) |

## API

| Def or type | Meaning |
|---|---|
| `PkcsRules{asn1, attrs_der, attrs_required, versions, digests_listed}` and its field readers; `Pkcs.rules()`, `Pkcs.rules_strict()`, `Pkcs.rules_lenient()` | what a parse accepts |
| `Cms.parse(r, b)` | the SignedData of a ContentInfo's octets |
| `CmsSignedData{version, digest_algs, content_type, content, certificates, crls, signers, raw}` and its field readers; `CmsSignedData.conforms(r, s)`; `Cms.expected_version(s)` | SignedData (open type); whether it passes the checks of `r`; its version by 5.1 |
| `CmsSigner{version, sid, digest_alg, signed_attrs, sig_alg, signature, unsigned_attrs}` and its field readers; `CmsSid` (`CmsSidIssuer{issuer, serial}`, `CmsSidKeyId{key_id}`); `CmsAttrs{attrs, raw}`, `.attrs`, `.raw` | signers (open types) |
| `CmsAttr{attr_type, values, raw}`, `.attr_type`, `.values`, `.raw`, `.single`; `Cms.find_attr(xs, id)`, `Cms.count_attr(xs, id)` | attributes (open type) |
| `Cms.id_data()`, `Cms.id_signed_data()`, `Cms.id_content_type()`, `Cms.id_message_digest()` | object identifiers |
| `Cms.signed_message(g, content)`, `Cms.set_tagged(o)` | what a signer signed (5.4) |
| `Cms.verify_with(~PK, ~pk_of, ~verify, key, g, content)` | the signature check (extension point) |
| `Cms.message_digest(g)`, `Cms.digest_matches(~digest, g, content)` | the message-digest attribute, and its check (extension point) |
| `Cms.signer_certificate(xr, nr, s, g)` | the certificate a signer names, read under x509 rules `xr`, names compared under `nr` |
| `Pkcs8.parse(r, b)`; `Pkcs8Key{version, alg, private_key, attributes, public_key, raw}` and its field readers; `Pkcs8Key.conforms(r, k)`; `Pkcs8.curve_private_key(r, k)` | PKCS #8 keys (open type) |
| `PkcsError` (`PkcsAsn1{error}`, `PkcsX509{error}`, `PkcsNotSignedData`, `PkcsBadVersion`, `PkcsBadSigner`, `PkcsBadContent`, `PkcsBadAttribute{id}`, `PkcsAttrsNotDer`, `PkcsMissingAttrs`, `PkcsContentTypeMismatch`, `PkcsDigestNotListed`, `PkcsBadKey`), `PkcsError.name` | why a message or key was refused |

Defs named `pk.*` are internal.

## Extension points

* **Signature schemes**: `Cms.verify_with` takes a scheme as
  bend-osdev-crypto's signature interface defines it (`crypto/sign.bend`)
  and checks the signature over exactly `Cms.signed_message`; the key's
  bytes come from the signer's certificate (`Cms.signer_certificate`,
  then x509's `X509Spki.key_octets`). `verify_signed_if` holds for every
  scheme that satisfies crypto's laws. Choosing the scheme from
  `CmsSigner.sig_alg` is the caller's.
* **Digests**: `Cms.digest_matches` takes the digest as a function of the
  content's octets (crypto's hash interface supplies one).
* **Content**: other content types than SignedData are refused
  (`PkcsNotSignedData`); the encapsulated content is kept as octets for the
  caller to read as its type.
* **Rules** are a record: a new check is a field and one more line in
  `pk.conform`.

## Laws

`LAWS.bend`, proved for **every** input:

* `cms_parsed_conforms`, `p8_parsed_conforms`: a SignedData or key the
  parse answers passes every check of its rules (the checks are its last
  step);
* `signed_without_attrs`: a signer without signed attributes signed the
  content itself (RFC 5652 5.4);
* `verify_signed_if`: for every signature scheme satisfying crypto's
  `pk_format` and `accepts` laws, a signer whose signature is the scheme's
  signature of `Cms.signed_message` verifies under the signer's key bytes;
* `find_attr_type`: `Cms.find_attr` answers only an attribute of the type
  asked for;
* `signed_data_slice`: the SignedData's octets (`CmsSignedData.raw`) are a
  slice of the input; `signed_attrs_slice`: so are each signer's signed
  attributes' octets (`CmsAttrs.raw`, what the signature is over, 5.4);
  `certificate_slice`: so is each certificate's (`CmsSignedData.certificates`,
  where `Cms.signer_certificate` finds the signer's key);
* `signed_attrs_der`: under the `attrs_der` rule (as in `Pkcs.rules()`),
  for a signer with signed attributes, `Cms.signed_message` is the DER of a
  SET (`Asn1.encode(Asn1Cons{Asn1Tag.set(), ns})`): the attributes'
  elements with SET's tag in place of the IMPLICIT [0], whatever the
  content given;
* vector: signed attributes retagged A0 to 31 (5.4).

**How the octets laws are proved** (`proof_octets.bend`): `Cms.parse`
matches the input against ContentInfo's schema, then the content's octets
against SignedData's; following each step of the readers' Result chains
(`pq.then`) shows the octets kept are the octets of the matches at those
fields, and asn1's `match_input` places each in the content's octets and
those in the input. For `signed_attrs_der`: the parse's checks passed
(`cms_parsed_conforms`), so under `attrs_der` the signed attributes'
octets matched `pk.s.attrs(0)` again under DER; asn1's `match_whole`,
`match_der` and `match_of_node` make them the DER of a constructed [0]
element, and `encode_retag` with `vec_identifier` (A0 and 31) makes
`Cms.set_tagged` of them the DER of the SET of the same elements. The few
facts about joining `Octets` that bytes does not state yet (associativity,
slices of slices) are proved privately there from bytes' interface laws.

**Not stated as laws** (tested only): that the values read from the
fields are the message's (versions, digest and signature algorithms,
content type, the eContent's octets, signer identifiers, signatures, the
attributes' values): these go through bend-osdev-asn1's typed readers
(INTEGER, OCTET STRING, OBJECT IDENTIFIER nodes) and x509's readers, which
have no laws about their values yet, so only the octets the parse keeps
are proved. Without the `attrs_der` rule the signed attributes are kept
as read, and nothing is stated about their DER. `ref/run.sh` checks the
signed octets by verifying the signature over them with Python
cryptography.

## Tests

* `check.bend`: an OpenSSL SignedData with an ECDSA P-256 signer
  (attached, signed attributes, certificate) and a detached one without
  attributes naming its signer by subject key identifier, under the
  default and strict rules; the digest and signature extension points with
  stand-ins; refusals (an octet after the message, cut short, a key where a
  message belongs, a ContentInfo of id-data); an Ed25519 PKCS #8 key, cut,
  and a message where a key belongs.
* `ref/run.sh` (117 cases with the default seed, half a minute), against
  OpenSSL 3.0.13 and Python cryptography 41.0.7: 32 SignedData messages
  from `openssl cms -sign` (RSA, P-256 and P-384 signers; DER and streamed
  BER with indefinite lengths; attached and detached; without signed
  attributes; subject key identifier signers; SHA-384; no certificates; a
  content type other than id-data), two signers with an extra certificate,
  `openssl smime -sign` (PKCS #7), and `cryptography`'s
  PKCS7SignatureBuilder (attached, without attributes, detached). Every
  field must equal a model of X.690 and RFC 5652 written in `ref/gen.py`,
  and the model is held to both tools: `openssl cms -verify` accepts each
  message, `openssl cms -cmsout -print` shows its version and content
  type, `cryptography` verifies each signature over the model's signed
  octets with the signer certificate's key, finds the content's digest in
  the message-digest attribute, and reads the same certificates (26
  messages; it reads PKCS #7, which has no subject key identifier form).
  Each message is read under the strict rules, and cut short (both tools
  refuse) must be refused. A signed attribute not in DER and a
  content-type attribute that does not match must be refused (OpenSSL 3.0
  accepts both: it encodes the attributes in DER again, and does not
  compare the content type). Seven PKCS #8 keys (RSA, P-256, P-384,
  Ed25519, Ed448, X25519, X448) from `cryptography`, read by OpenSSL and
  `cryptography`: the private key octets must be RSAPrivateKey as
  `cryptography` writes it, ECPrivateKey with the private value, and the
  curves' raw keys; each cut short must be refused; an Ed25519 v2 key with
  its public key (made by the model; OpenSSL 3.0 reads only
  PrivateKeyInfo) is read, and the public key in a v1 key is refused by
  the versions rule. It exits 77 without python3, openssl or
  cryptography.

## Limits

* Only SignedData is read (not EnvelopedData, DigestedData,
  EncryptedData, AuthenticatedData); encrypted PKCS #8 keys are not read.
* Certificates and CRLs are kept as octets (read with bend-osdev-x509 on
  demand); attribute certificates and other formats are kept the same
  way.
* Signer identifiers name certificates by issuer and serial number (names
  compared under the caller's name rules) or subject key identifier.

## Dependencies

`bend-osdev-bytes` (octets), `bend-osdev-asn1` (BER, DER and schemas),
`bend-osdev-oid` (object identifiers), `bend-osdev-x509` (names,
algorithm identifiers, certificates), `bend-osdev-crypto` (the signature
interface).

## Status

Bend 2.0.39 (2026-10-26, native, three packages at a time): `PROOF.bend`
(9 s, 0.47 GB peak; `--verdict` 34 s, 0.84 GB peak) ALL PROOFS CHECK, with
and without `--verdict`.

Bend 2.0.37: `PROOF.bend` ALL PROOFS CHECK, `--verdict` ALL PROOFS CHECK,
`check.bend` passes, `ref/run.sh` 117 cases match, `scripts/deps.sh pkcs`
ok.
