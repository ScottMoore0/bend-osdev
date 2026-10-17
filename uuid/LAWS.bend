# DRAFT: not yet reviewed by the maintainer
#
# Properties, for every UUID: a UUID is made of its 16 bytes; the byte form and the GUID layout read back
# what they wrote; the text form reads back what it wrote, in lower case and
# in upper case; the text form is 36 characters. For every 16 bytes: reading
# the GUID layout is reading the RFC order with the first three fields
# byte-reversed (RFC 9562 section 4; the layout of Python's bytes_le).
#
# Vectors: RFC 9562's example UUIDs (appendices A and B), read from the text
# the RFC prints, written back in lower case, with their versions and
# variants; the Nil and Max UUIDs (sections 5.9 and 5.10); byte orders; and
# malformed input.
import Base
import ../bytes/bytes.bend as B
import ./uuid.bend as U

# Properties, for every input

law bytes_round_trip:
  for u: U.Uuid
  {U.Uuid.from_bytes(U.Uuid.to_bytes(u)) == Done{u} : Result<&2, &2, U.UuidError, U.Uuid>}

law guid_round_trip:
  for u: U.Uuid
  {U.Uuid.from_guid(U.Uuid.to_guid(u)) == Done{u} : Result<&2, &2, U.UuidError, U.Uuid>}

law guid_list_round_trip:
  for u: U.Uuid
  {U.Uuid.from_guid_list(U.Uuid.to_guid_list(u)) == Done{u} : Result<&2, &2, U.UuidError, U.Uuid>}

law guid_layout:
  for +a0: U32
  for +a1: U32
  for +a2: U32
  for +a3: U32
  for +a4: U32
  for +a5: U32
  for +a6: U32
  for +a7: U32
  for +a8: U32
  for +a9: U32
  for +a10: U32
  for +a11: U32
  for +a12: U32
  for +a13: U32
  for +a14: U32
  for +a15: U32
  {U.Uuid.from_guid(B.Octets.of_list([a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15])) == U.Uuid.from_bytes(B.Octets.of_list([a3, a2, a1, a0, a5, a4, a7, a6, a8, a9, a10, a11, a12, a13, a14, a15])) : Result<&2, &2, U.UuidError, U.Uuid>}

# a UUID is made of its bytes: what other packages' proofs rely on to treat
# a Uuid as 16 bytes without depending on how it is stored
law make_bytes:
  for +u: U.Uuid
  {U.Uuid.make(U.Uuid.byte(u, 0n), U.Uuid.byte(u, 1n), U.Uuid.byte(u, 2n), U.Uuid.byte(u, 3n), U.Uuid.byte(u, 4n), U.Uuid.byte(u, 5n), U.Uuid.byte(u, 6n), U.Uuid.byte(u, 7n), U.Uuid.byte(u, 8n), U.Uuid.byte(u, 9n), U.Uuid.byte(u, 10n), U.Uuid.byte(u, 11n), U.Uuid.byte(u, 12n), U.Uuid.byte(u, 13n), U.Uuid.byte(u, 14n), U.Uuid.byte(u, 15n)) == u : U.Uuid}

law text_round_trip:
  for u: U.Uuid
  {U.Uuid.parse(U.Uuid.show(u)) == Done{u} : Result<&2, &2, U.UuidError, U.Uuid>}

law text_upper_round_trip:
  for u: U.Uuid
  {U.Uuid.parse(String.to_upper(U.Uuid.show(u))) == Done{u} : Result<&2, &2, U.UuidError, U.Uuid>}

law text_length:
  for u: U.Uuid
  {String.length(U.Uuid.show(u)) == 36n : Nat}

# Vectors: RFC 9562's examples, as printed, written back in lower case

law rfc_v1_text:
  {Result.map(&2, &2, U.UuidError, U.Uuid, String, U.Uuid.show, U.Uuid.parse("C232AB00-9414-11EC-B3C8-9F6BDECED846")) == Done{"c232ab00-9414-11ec-b3c8-9f6bdeced846"} : Result<&2, &2, U.UuidError, String>}

law rfc_v3_text:
  {Result.map(&2, &2, U.UuidError, U.Uuid, String, U.Uuid.show, U.Uuid.parse("5df41881-3aed-3515-88a7-2f4a814cf09e")) == Done{"5df41881-3aed-3515-88a7-2f4a814cf09e"} : Result<&2, &2, U.UuidError, String>}

law rfc_v6_text:
  {Result.map(&2, &2, U.UuidError, U.Uuid, String, U.Uuid.show, U.Uuid.parse("1EC9414C-232A-6B00-B3C8-9F6BDECED846")) == Done{"1ec9414c-232a-6b00-b3c8-9f6bdeced846"} : Result<&2, &2, U.UuidError, String>}

law rfc_v7_text:
  {Result.map(&2, &2, U.UuidError, U.Uuid, String, U.Uuid.show, U.Uuid.parse("017F22E2-79B0-7CC3-98C4-DC0C0C07398F")) == Done{"017f22e2-79b0-7cc3-98c4-dc0c0c07398f"} : Result<&2, &2, U.UuidError, String>}

# Vectors: the version of each example

law rfc_v1_version:
  {Result.map(&2, &2, U.UuidError, U.Uuid, U32, U.Uuid.version, U.Uuid.parse("C232AB00-9414-11EC-B3C8-9F6BDECED846")) == Done{1} : Result<&2, &2, U.UuidError, U32>}

law rfc_v3_version:
  {Result.map(&2, &2, U.UuidError, U.Uuid, U32, U.Uuid.version, U.Uuid.parse("5df41881-3aed-3515-88a7-2f4a814cf09e")) == Done{3} : Result<&2, &2, U.UuidError, U32>}

law rfc_v4_version:
  {Result.map(&2, &2, U.UuidError, U.Uuid, U32, U.Uuid.version, U.Uuid.parse("919108f7-52d1-4320-9bac-f847db4148a8")) == Done{4} : Result<&2, &2, U.UuidError, U32>}

law rfc_v5_version:
  {Result.map(&2, &2, U.UuidError, U.Uuid, U32, U.Uuid.version, U.Uuid.parse("2ed6657d-e927-568b-95e1-2665a8aea6a2")) == Done{5} : Result<&2, &2, U.UuidError, U32>}

law rfc_v6_version:
  {Result.map(&2, &2, U.UuidError, U.Uuid, U32, U.Uuid.version, U.Uuid.parse("1EC9414C-232A-6B00-B3C8-9F6BDECED846")) == Done{6} : Result<&2, &2, U.UuidError, U32>}

law rfc_v7_version:
  {Result.map(&2, &2, U.UuidError, U.Uuid, U32, U.Uuid.version, U.Uuid.parse("017F22E2-79B0-7CC3-98C4-DC0C0C07398F")) == Done{7} : Result<&2, &2, U.UuidError, U32>}

law rfc_v8_time_version:
  {Result.map(&2, &2, U.UuidError, U.Uuid, U32, U.Uuid.version, U.Uuid.parse("2489E9AD-2EE2-8E00-8EC9-32D5F69181C0")) == Done{8} : Result<&2, &2, U.UuidError, U32>}

law rfc_v8_name_version:
  {Result.map(&2, &2, U.UuidError, U.Uuid, U32, U.Uuid.version, U.Uuid.parse("5c146b14-3c52-8afd-938a-375d0df1fbf6")) == Done{8} : Result<&2, &2, U.UuidError, U32>}

# Vectors: variants (octet 8 of the examples is 0x8_, 0x9_ or 0xB_)

law rfc_v4_variant:
  {Result.map(&2, &2, U.UuidError, U.Uuid, U.UuidVariant, U.Uuid.variant, U.Uuid.parse("919108f7-52d1-4320-9bac-f847db4148a8")) == Done{U.UuidRfc{}} : Result<&2, &2, U.UuidError, U.UuidVariant>}

law rfc_v7_variant:
  {Result.map(&2, &2, U.UuidError, U.Uuid, U.UuidVariant, U.Uuid.variant, U.Uuid.parse("017F22E2-79B0-7CC3-98C4-DC0C0C07398F")) == Done{U.UuidRfc{}} : Result<&2, &2, U.UuidError, U.UuidVariant>}

law rfc_v8_name_variant:
  {Result.map(&2, &2, U.UuidError, U.Uuid, U.UuidVariant, U.Uuid.variant, U.Uuid.parse("5c146b14-3c52-8afd-938a-375d0df1fbf6")) == Done{U.UuidRfc{}} : Result<&2, &2, U.UuidError, U.UuidVariant>}

law microsoft_variant:
  {Result.map(&2, &2, U.UuidError, U.Uuid, U.UuidVariant, U.Uuid.variant, U.Uuid.parse("00000000-0000-0000-c000-000000000000")) == Done{U.UuidMicrosoft{}} : Result<&2, &2, U.UuidError, U.UuidVariant>}

# Vectors: Nil and Max (the Nil UUID is in the NCS range, the Max UUID in the
# range reserved for the future, as RFC 9562 section 4.1 notes)

law nil_text:
  {U.Uuid.show(U.Uuid.nil()) == "00000000-0000-0000-0000-000000000000" : String}

law max_text:
  {U.Uuid.show(U.Uuid.max()) == "ffffffff-ffff-ffff-ffff-ffffffffffff" : String}

law nil_variant:
  {U.Uuid.variant(U.Uuid.nil()) == U.UuidNcs{} : U.UuidVariant}

law max_variant:
  {U.Uuid.variant(U.Uuid.max()) == U.UuidFuture{} : U.UuidVariant}

law max_parse:
  {U.Uuid.parse("FFFFFFFF-FFFF-FFFF-FFFF-FFFFFFFFFFFF") == Done{U.Uuid.max()} : Result<&2, &2, U.UuidError, U.Uuid>}

# Vectors: byte orders (the v4 example in RFC order; the v1 example and the
# EFI System Partition type GUID of the UEFI specification in the GUID layout)

law rfc_v4_bytes:
  {Result.map(&2, &2, U.UuidError, U.Uuid, B.Octets, U.Uuid.to_bytes, U.Uuid.parse("919108f7-52d1-4320-9bac-f847db4148a8")) == Done{B.Octets.of_list([145, 145, 8, 247, 82, 209, 67, 32, 155, 172, 248, 71, 219, 65, 72, 168])} : Result<&2, &2, U.UuidError, B.Octets>}

law rfc_v1_guid:
  {Result.map(&2, &2, U.UuidError, U.Uuid, B.Octets, U.Uuid.to_guid, U.Uuid.parse("C232AB00-9414-11EC-B3C8-9F6BDECED846")) == Done{B.Octets.of_list([0, 171, 50, 194, 20, 148, 236, 17, 179, 200, 159, 107, 222, 206, 216, 70])} : Result<&2, &2, U.UuidError, B.Octets>}

law esp_guid:
  {Result.map(&2, &2, U.UuidError, U.Uuid, String, U.Uuid.show, U.Uuid.from_guid(B.Octets.of_list([40, 115, 42, 193, 31, 248, 210, 17, 186, 75, 0, 160, 201, 62, 201, 59]))) == Done{"c12a7328-f81f-11d2-ba4b-00a0c93ec93b"} : Result<&2, &2, U.UuidError, String>}

# Vectors: malformed input, and which failure each is

law short_text:
  {U.Uuid.parse("c232ab00-9414-11ec-b3c8-9f6bdeced84") == Fail{U.UuidBadLength{}} : Result<&2, &2, U.UuidError, U.Uuid>}

law bad_digit:
  {U.Uuid.parse("c232ab00-9414-11ec-b3c8-9f6bdeced84g") == Fail{U.UuidBadDigit{}} : Result<&2, &2, U.UuidError, U.Uuid>}

law missing_dash:
  {U.Uuid.parse("c232ab0009414-11ec-b3c8-9f6bdeced846") == Fail{U.UuidBadDash{}} : Result<&2, &2, U.UuidError, U.Uuid>}

law short_bytes:
  {U.Uuid.from_bytes(B.Octets.zeros(15n)) == Fail{U.UuidBadLength{}} : Result<&2, &2, U.UuidError, U.Uuid>}
