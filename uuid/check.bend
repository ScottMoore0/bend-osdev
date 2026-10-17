import Base
import ../bytes/bytes.bend as B
import ./uuid.bend as U

def show_m(m: Result<&2, &2, U.UuidError, U.Uuid>) -> String:
  match m:
    case Done{u}:
      U.Uuid.show(u)
    case Fail{e}:
      "error: " ++ U.UuidError.show(e)

def show_maybe(m: Maybe<&2, U.Uuid>) -> String:
  match m:
    case Some{u}:
      U.Uuid.show(u)
    case None{}:
      "none"

def info(m: Result<&2, &2, U.UuidError, U.Uuid>) -> String:
  match m:
    case Done{+u}:
      U.Uuid.show(u) ++ " v" ++ U32.show(U.Uuid.version(u)) ++ " " ++ U.UuidVariant.show(U.Uuid.variant(u)) ++ " " ++ B.Octets.hex(U.Uuid.to_guid(u))
    case Fail{e}:
      "error: " ++ U.UuidError.show(e)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(info(U.Uuid.parse("C232AB00-9414-11EC-B3C8-9F6BDECED846")))
    IO.print(info(U.Uuid.parse("5df41881-3aed-3515-88a7-2f4a814cf09e")))
    IO.print(info(U.Uuid.parse("919108f7-52d1-4320-9bac-f847db4148a8")))
    IO.print(info(U.Uuid.parse("2ed6657d-e927-568b-95e1-2665a8aea6a2")))
    IO.print(info(U.Uuid.parse("1EC9414C-232A-6B00-B3C8-9F6BDECED846")))
    IO.print(info(U.Uuid.parse("017F22E2-79B0-7CC3-98C4-DC0C0C07398F")))
    IO.print(info(U.Uuid.parse("2489E9AD-2EE2-8E00-8EC9-32D5F69181C0")))
    IO.print(info(U.Uuid.parse("5c146b14-3c52-8afd-938a-375d0df1fbf6")))
    IO.print(info(Done{U.Uuid.nil()}))
    IO.print(info(Done{U.Uuid.max()}))
    IO.print(info(U.Uuid.parse("C12A7328-F81F-11D2-BA4B-00A0C93EC93B")))
    IO.print(show_m(U.Uuid.from_guid(B.Octets.of_list([40, 115, 42, 193, 31, 248, 210, 17, 186, 75, 0, 160, 201, 62, 201, 59]))))
    IO.print(B.Octets.hex(U.Uuid.to_bytes(U.Uuid.max())))
    IO.print(show_m(U.Uuid.parse("c232ab00-9414-11ec-b3c8-9f6bdeced84")))
    IO.print(show_m(U.Uuid.parse("c232ab00-9414-11ec-b3c8-9f6bdeced84g")))
    IO.print(show_m(U.Uuid.parse("c232ab0009414-11ec-b3c8-9f6bdeced846")))
    IO.print(show_m(U.Uuid.from_bytes(B.Octets.of_list([1, 2, 3]))))
    IO.print(show_maybe(U.Uuid.from_bytes_at(B.Octets.of_list([9, 9, 0, 17, 34, 51, 68, 85, 102, 119, 136, 153, 170, 187, 204, 221, 238, 255]), 2n)))
    IO.print(Bool.show(U.Uuid.is_nil(U.Uuid.nil())))
    IO.print(Bool.show(U.Uuid.is_nil(U.Uuid.max())))

#|c232ab00-9414-11ec-b3c8-9f6bdeced846 v1 rfc9562 00ab32c21494ec11b3c89f6bdeced846
#|5df41881-3aed-3515-88a7-2f4a814cf09e v3 rfc9562 8118f45ded3a153588a72f4a814cf09e
#|919108f7-52d1-4320-9bac-f847db4148a8 v4 rfc9562 f7089191d15220439bacf847db4148a8
#|2ed6657d-e927-568b-95e1-2665a8aea6a2 v5 rfc9562 7d65d62e27e98b5695e12665a8aea6a2
#|1ec9414c-232a-6b00-b3c8-9f6bdeced846 v6 rfc9562 4c41c91e2a23006bb3c89f6bdeced846
#|017f22e2-79b0-7cc3-98c4-dc0c0c07398f v7 rfc9562 e2227f01b079c37c98c4dc0c0c07398f
#|2489e9ad-2ee2-8e00-8ec9-32d5f69181c0 v8 rfc9562 ade98924e22e008e8ec932d5f69181c0
#|5c146b14-3c52-8afd-938a-375d0df1fbf6 v8 rfc9562 146b145c523cfd8a938a375d0df1fbf6
#|00000000-0000-0000-0000-000000000000 v0 ncs 00000000000000000000000000000000
#|ffffffff-ffff-ffff-ffff-ffffffffffff v15 future ffffffffffffffffffffffffffffffff
#|c12a7328-f81f-11d2-ba4b-00a0c93ec93b v1 rfc9562 28732ac11ff8d211ba4b00a0c93ec93b
#|c12a7328-f81f-11d2-ba4b-00a0c93ec93b
#|ffffffffffffffffffffffffffffffff
#|error: bad length
#|error: bad digit
#|error: missing dash
#|error: bad length
#|00112233-4455-6677-8899-aabbccddeeff
#|True
#|False
