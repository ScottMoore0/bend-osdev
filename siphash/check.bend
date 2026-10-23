# bend-osdev-siphash: the published vectors (vectors.h of the reference
# implementation, github.com/veorq/SipHash: the key 00 01 .. 0f, HalfSipHash
# its first 8 bytes, and the messages 00 01 .. (i - 1) for i = 0 to 63),
# then values of the openssl command and pieces, bytes and refusals.
# Written by gen/check.py; do not edit by hand.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./siphash.bend as S
import ./halfsiphash.bend as H

# the bytes 0, 1, .., n - 1
def iota.go(+n: Nat, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      iota.go(p, Con{U32.from_nat(p), acc})

def msg(n: Nat) -> B.Octets:
  B.Octets.of_list(iota.go(n, Nil{}))

# n pseudo-random bytes (a linear congruential generator)
def bulk.go(n: Nat, +s: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +s2 = U32.add(U32.mul(s, 1103515245), 12345)
      bulk.go(p, s2, Con{U32.and(U32.shrn(s2, 16n), 255), acc})

def bulk(n: Nat) -> B.Octets:
  B.Octets.of_list(bulk.go(n, 7, Nil{}))

def key16.of(r: Result<&2, &2, S.SipError, S.SipKey>) -> S.SipKey:
  match r:
    case Done{k}:
      k
    case Fail{e}:
      S.SipKey.of_words(W.W64.zero(), W.W64.zero())

def key16() -> S.SipKey:
  key16.of(S.SipKey.of_octets(msg(16n)))

def key8.of(r: Result<&2, &2, S.SipError, H.HsipKey>) -> H.HsipKey:
  match r:
    case Done{k}:
      k
    case Fail{e}:
      H.HsipKey.of_words(0, 0)

def key8() -> H.HsipKey:
  key8.of(H.HsipKey.of_octets(msg(8n)))

def show_err(r: Result<&2, &2, S.SipError, B.Octets>) -> String:
  match r:
    case Done{o}:
      "accepted " ++ B.Octets.hex(o)
    case Fail{S.SipBadKeyLength{n}}:
      "refused " ++ Nat.show(n)

type ChkKind is Data:
  ChkSip64{}
  ChkSip128{}
  ChkHsip32{}
  ChkHsip64{}

def kind.name(k: ChkKind) -> String:
  match k:
    case ChkSip64{}:
      "sip64"
    case ChkSip128{}:
      "sip128"
    case ChkHsip32{}:
      "hsip32"
    case ChkHsip64{}:
      "hsip64"

def kind.run(k: ChkKind, +m: B.Octets) -> B.Octets:
  match k:
    case ChkSip64{}:
      S.siphash24(key16(), m)
    case ChkSip128{}:
      S.SipHash.hash(S.SipParams.sip24_wide(), key16(), m)
    case ChkHsip32{}:
      H.halfsiphash24(key8(), m)
    case ChkHsip64{}:
      H.HalfSipHash.hash(H.HalfSipParams.hsip24_wide(), key8(), m)

# the lines for messages of n - 1 down to 0 bytes, in front of acc
def table.go(+n: Nat, +k: ChkKind, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      table.go(p, k, kind.name(k) ++ " " ++ Nat.show(p) ++ " " ++ B.Octets.hex(kind.run(k, msg(p))) ++ "\n" ++ acc)

def table(+k: ChkKind) -> String:
  table.go(64n, k, "")

# SipHash-2-4 of 63 bytes in three pieces (7, 1 and 55 bytes), and byte by
# byte through update_byte for the first 9
def pieces() -> B.Octets:
  +k = key16()
  S.SipHash.finish(S.SipHash.update(S.SipHash.update(S.SipHash.update(S.SipHash.start(S.SipParams.sip24(), k), B.Octets.take(7n, msg(63n))), B.Octets.slice(7n, 1n, msg(63n))), B.Octets.drop(8n, msg(63n))))

def bytes9.go(n: Nat, +i: U32, s: S.SipState) -> S.SipState:
  match n:
    case 0n:
      s
    case 1n+p:
      bytes9.go(p, U32.add(i, 1), S.SipHash.update_byte(s, i))

def bytes9() -> B.Octets:
  S.SipHash.finish(bytes9.go(9n, 0, S.SipHash.start(S.SipParams.sip24(), key16())))

def hpieces() -> B.Octets:
  +k = key8()
  H.HalfSipHash.finish(H.HalfSipHash.update(H.HalfSipHash.update(H.HalfSipHash.start(H.HalfSipParams.hsip24(), k), B.Octets.take(5n, msg(63n))), B.Octets.drop(5n, msg(63n))))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(table(ChkSip64{}))
    IO.print(table(ChkSip128{}))
    IO.print(table(ChkHsip32{}))
    IO.print(table(ChkHsip64{}))
    IO.print("sip13 15 " ++ B.Octets.hex(S.siphash13(key16(), msg(15n))))
    IO.print("sip48 15 " ++ B.Octets.hex(S.SipHash.hash(S.SipParams.sip48(), key16(), msg(15n))))
    IO.print("sip13 63 " ++ B.Octets.hex(S.siphash13(key16(), msg(63n))))
    IO.print("sip24 bulk " ++ B.Octets.hex(S.siphash24(key16(), bulk(10000n))))
    IO.print("hsip13 15 " ++ B.Octets.hex(H.halfsiphash13(key8(), msg(15n))))
    IO.print("hsip13 63 " ++ B.Octets.hex(H.halfsiphash13(key8(), msg(63n))))
    IO.print("pieces " ++ B.Octets.hex(pieces()))
    IO.print("bytes9 " ++ B.Octets.hex(bytes9()))
    IO.print("hpieces " ++ B.Octets.hex(hpieces()))
    IO.print("key15 " ++ show_err(S.SipHash.mac(S.SipParams.sip24(), msg(15n), msg(3n))))
    IO.print("key16 " ++ show_err(S.SipHash.mac(S.SipParams.sip24(), msg(16n), msg(3n))))
    IO.print("hkey16 " ++ show_err(H.HalfSipHash.mac(H.HalfSipParams.hsip24(), msg(16n), msg(3n))))
    IO.print("hkey8 " ++ show_err(H.HalfSipHash.mac(H.HalfSipParams.hsip24(), msg(8n), msg(3n))))

#|sip64 0 310e0edd47db6f72
#|sip64 1 fd67dc93c539f874
#|sip64 2 5a4fa9d909806c0d
#|sip64 3 2d7efbd796666785
#|sip64 4 b7877127e09427cf
#|sip64 5 8da699cd64557618
#|sip64 6 cee3fe586e46c9cb
#|sip64 7 37d1018bf50002ab
#|sip64 8 6224939a79f5f593
#|sip64 9 b0e4a90bdf82009e
#|sip64 10 f3b9dd94c5bb5d7a
#|sip64 11 a7ad6b22462fb3f4
#|sip64 12 fbe50e86bc8f1e75
#|sip64 13 903d84c02756ea14
#|sip64 14 eef27a8e90ca23f7
#|sip64 15 e545be4961ca29a1
#|sip64 16 db9bc2577fcc2a3f
#|sip64 17 9447be2cf5e99a69
#|sip64 18 9cd38d96f0b3c14b
#|sip64 19 bd6179a71dc96dbb
#|sip64 20 98eea21af25cd6be
#|sip64 21 c7673b2eb0cbf2d0
#|sip64 22 883ea3e395675393
#|sip64 23 c8ce5ccd8c030ca8
#|sip64 24 94af49f6c650adb8
#|sip64 25 eab8858ade92e1bc
#|sip64 26 f315bb5bb835d817
#|sip64 27 adcf6b0763612e2f
#|sip64 28 a5c91da7acaa4dde
#|sip64 29 716595876650a2a6
#|sip64 30 28ef495c53a387ad
#|sip64 31 42c341d8fa92d832
#|sip64 32 ce7cf2722f512771
#|sip64 33 e37859f94623f3a7
#|sip64 34 381205bb1ab0e012
#|sip64 35 ae97a10fd434e015
#|sip64 36 b4a31508beff4d31
#|sip64 37 81396229f0907902
#|sip64 38 4d0cf49ee5d4dcca
#|sip64 39 5c73336a76d8bf9a
#|sip64 40 d0a704536ba93e0e
#|sip64 41 925958fcd6420cad
#|sip64 42 a915c29bc8067318
#|sip64 43 952b79f3bc0aa6d4
#|sip64 44 f21df2e41d4535f9
#|sip64 45 87577519048f53a9
#|sip64 46 10a56cf5dfcd9adb
#|sip64 47 eb75095ccd986cd0
#|sip64 48 51a9cb9ecba312e6
#|sip64 49 96afadfc2ce666c7
#|sip64 50 72fe52975a4364ee
#|sip64 51 5a1645b276d592a1
#|sip64 52 b274cb8ebf87870a
#|sip64 53 6f9bb4203de7b381
#|sip64 54 eaecb2a30b22a87f
#|sip64 55 9924a43cc1315724
#|sip64 56 bd838d3aafbf8db7
#|sip64 57 0b1a2a3265d51aea
#|sip64 58 135079a3231ce660
#|sip64 59 932b2846e4d70666
#|sip64 60 e1915f5cb1eca46c
#|sip64 61 f325965ca16d629f
#|sip64 62 575ff28e60381be5
#|sip64 63 724506eb4c328a95
#|
#|sip128 0 a3817f04ba25a8e66df67214c7550293
#|sip128 1 da87c1d86b99af44347659119b22fc45
#|sip128 2 8177228da4a45dc7fca38bdef60affe4
#|sip128 3 9c70b60c5267a94e5f33b6b02985ed51
#|sip128 4 f88164c12d9c8faf7d0f6e7c7bcd5579
#|sip128 5 1368875980776f8854527a07690e9627
#|sip128 6 14eeca338b208613485ea0308fd7a15e
#|sip128 7 a1f1ebbed8dbc153c0b84aa61ff08239
#|sip128 8 3b62a9ba6258f5610f83e264f31497b4
#|sip128 9 264499060ad9baabc47f8b02bb6d71ed
#|sip128 10 00110dc378146956c95447d3f3d0fbba
#|sip128 11 0151c568386b6677a2b4dc6f81e5dc18
#|sip128 12 d626b266905ef35882634df68532c125
#|sip128 13 9869e247e9c08b10d029934fc4b952f7
#|sip128 14 31fcefac66d7de9c7ec7485fe4494902
#|sip128 15 5493e99933b0a8117e08ec0f97cfc3d9
#|sip128 16 6ee2a4ca67b054bbfd3315bf85230577
#|sip128 17 473d06e8738db89854c066c47ae47740
#|sip128 18 a426e5e423bf4885294da481feaef723
#|sip128 19 78017731cf65fab074d5208952512eb1
#|sip128 20 9e25fc833f2290733e9344a5e83839eb
#|sip128 21 568e495abe525a218a2214cd3e071d12
#|sip128 22 4a29b54552d16b9a469c10528eff0aae
#|sip128 23 c9d184ddd5a9f5e0cf8ce29a9abf691c
#|sip128 24 2db479ae78bd50d8882a8a178a6132ad
#|sip128 25 8ece5f042d5e447b5051b9eacb8d8f6f
#|sip128 26 9c0b53b4b3c307e87eaee08678141f66
#|sip128 27 abf248af69a6eae4bfd3eb2f129eeb94
#|sip128 28 0664da1668574b88b935f3027358aef4
#|sip128 29 aa4b9dc4bf337de90cd4fd3c467c6ab7
#|sip128 30 ea5c7f471faf6bde2b1ad7d4686d2287
#|sip128 31 2939b0183223fafc1723de4f52c43d35
#|sip128 32 7c3956ca5eeafc3e363e9d556546eb68
#|sip128 33 77c6077146f01c32b6b69d5f4ea9ffcf
#|sip128 34 37a6986cb8847edf0925f0f1309b54de
#|sip128 35 a705f0e69da9a8f907241a2e923c8cc8
#|sip128 36 3dc47d1f29c448461e9e76ed904f6711
#|sip128 37 0d62bf01e6fc0e1a0d3c4751c5d3692b
#|sip128 38 8c03468bca7c669ee4fd5e084bbee7b5
#|sip128 39 528a5bb93baf2c9c4473cce5d0d22bd9
#|sip128 40 df6a301e95c95dad97ae0cc8c6913bd8
#|sip128 41 801189902c857f39e73591285e70b6db
#|sip128 42 e617346ac9c231bb3650ae34ccca0c5b
#|sip128 43 27d93437efb721aa401821dcec5adf89
#|sip128 44 89237d9ded9c5e78d8b1c9b166cc7342
#|sip128 45 4a6d8091bf5e7d651189fa94a250b14c
#|sip128 46 0e33f96055e7ae893ffc0e3dcf492902
#|sip128 47 e61c432b720b19d18ec8d84bdc63151b
#|sip128 48 f7e5aef549f782cf379055a608269b16
#|sip128 49 438d030fd0b7a54fa837f2ad201a6403
#|sip128 50 a590d3ee4fbf04e3247e0d27f286423f
#|sip128 51 5fe2c1a172fe93c4b15cd37caef9f538
#|sip128 52 2c97325cbd06b36eb2133dd08b3a017c
#|sip128 53 92c814227a6bca949ff0659f002ad39e
#|sip128 54 dce850110bd8328cfbd50841d6911d87
#|sip128 55 67f14984c7da791248e32bb5922583da
#|sip128 56 1938f2cf72d54ee97e94166fa91d2a36
#|sip128 57 74481e9646ed49fe0f6224301604698e
#|sip128 58 57fca5de98a9d6d8006438d0583d8a1d
#|sip128 59 9fecde1cefdc1cbed4763674d9575359
#|sip128 60 e3040c00eb28f15366ca73cbd872e740
#|sip128 61 7697009a6a831dfecca91c5993670f7a
#|sip128 62 5853542321f567a005d547a4f04759bd
#|sip128 63 5150d1772f50834a503e069a973fbd7c
#|
#|hsip32 0 a9359f5b
#|hsip32 1 27475ab8
#|hsip32 2 fa62a603
#|hsip32 3 8afee704
#|hsip32 4 2a6e4689
#|hsip32 5 c5fab669
#|hsip32 6 5863fc23
#|hsip32 7 8bcf63c5
#|hsip32 8 d0b8848f
#|hsip32 9 f806e779
#|hsip32 10 94b07934
#|hsip32 11 08083050
#|hsip32 12 57f0872f
#|hsip32 13 77e663ff
#|hsip32 14 d6fff87c
#|hsip32 15 74fe2b97
#|hsip32 16 d9b5ac84
#|hsip32 17 c474645b
#|hsip32 18 465b8d9b
#|hsip32 19 7befe387
#|hsip32 20 e34d1045
#|hsip32 21 613f62b3
#|hsip32 22 70f367fe
#|hsip32 23 e6adb8bd
#|hsip32 24 27400c63
#|hsip32 25 26787875
#|hsip32 26 4f567b5f
#|hsip32 27 3ab0e669
#|hsip32 28 b0644000
#|hsip32 29 ff670fb4
#|hsip32 30 509e338b
#|hsip32 31 5d589f1a
#|hsip32 32 fee72112
#|hsip32 33 33753259
#|hsip32 34 6a434f8c
#|hsip32 35 fe28b729
#|hsip32 36 e75cc6ec
#|hsip32 37 697e8d54
#|hsip32 38 63688b0f
#|hsip32 39 650b62b4
#|hsip32 40 b6bc1840
#|hsip32 41 5d074505
#|hsip32 42 2442fd2e
#|hsip32 43 7bb7863a
#|hsip32 44 7705d548
#|hsip32 45 d75208b1
#|hsip32 46 b6d499c8
#|hsip32 47 0892202e
#|hsip32 48 69e12ce3
#|hsip32 49 8db580e5
#|hsip32 50 369764c6
#|hsip32 51 016e0204
#|hsip32 52 3b85f3d4
#|hsip32 53 fedb66be
#|hsip32 54 1e692a3a
#|hsip32 55 c68984c0
#|hsip32 56 a5c5b940
#|hsip32 57 9be9e88c
#|hsip32 58 7dbc8140
#|hsip32 59 7c078ec5
#|hsip32 60 d4e76c73
#|hsip32 61 428fcbb9
#|hsip32 62 bd83997a
#|hsip32 63 59ea4a74
#|
#|hsip64 0 218d1f59b9b83cc8
#|hsip64 1 be552412f8387315
#|hsip64 2 064f39ef7c50eb57
#|hsip64 3 ce0f1a45f7060679
#|hsip64 4 d5e78a175be52ea1
#|hsip64 5 cb9d7c3f2f3db580
#|hsip64 6 ce3e91358aa2bc25
#|hsip64 7 ff202728b07bc684
#|hsip64 8 edfee820bce4858c
#|hsip64 9 5b51cccc13888307
#|hsip64 10 95b0469f06a6f2ee
#|hsip64 11 ae26333994ddcd48
#|hsip64 12 7bc71f9faef5c799
#|hsip64 13 5a2352d75a0c3744
#|hsip64 14 3bb1a870eae8e658
#|hsip64 15 217d0bcb4e81c902
#|hsip64 16 7336aad25f7bf3b5
#|hsip64 17 37adc0641c4c4f6a
#|hsip64 18 c9b2db2b9a3e42f9
#|hsip64 19 f910e48020ab363c
#|hsip64 20 1bf52b0a6feea7db
#|hsip64 21 00741dc269e8b3ef
#|hsip64 22 e20103fa1ba776ef
#|hsip64 23 4c2210e54b681d73
#|hsip64 24 70741045ae3fa6f1
#|hsip64 25 0c86403739714038
#|hsip64 26 0d899ed8112923f0
#|hsip64 27 226bf5fab81ee1b8
#|hsip64 28 2d925ffb1e0016b5
#|hsip64 29 361958d52cee10f1
#|hsip64 30 291aaf864898179d
#|hsip64 31 863c7f155c34117c
#|hsip64 32 28709d46d811626c
#|hsip64 33 248477681d28f89c
#|hsip64 34 8324e4d7528f9830
#|hsip64 35 f9efd4e13aea6bd8
#|hsip64 36 86d67a40ec4276dc
#|hsip64 37 3f6292eccca97e35
#|hsip64 38 cbd92ee724d42109
#|hsip64 39 368df6808d403d79
#|hsip64 40 5b38c81c67c8ae4c
#|hsip64 41 95ab7189d439acb3
#|hsip64 42 a91a52c025327024
#|hsip64 43 5b0087c69528acea
#|hsip64 44 1e30f3ad27dcb15a
#|hsip64 45 697f5c9a90324ed4
#|hsip64 46 495c0f995557dc38
#|hsip64 47 9427202a3c29f94d
#|hsip64 48 a9eaa8c04ba93e3e
#|hsip64 49 eea4c1737d011218
#|hsip64 50 912d568fd8f65a49
#|hsip64 51 56919596b0ff5c97
#|hsip64 52 02445a7998f550e1
#|hsip64 53 86ec466ce71d1fb2
#|hsip64 54 359569e7d289e3bc
#|hsip64 55 871b05ca62bb7c96
#|hsip64 56 a1a492f942f15f1d
#|hsip64 57 12ec267ff6095b6e
#|hsip64 58 5d1b5ea1b231d89d
#|hsip64 59 d8cfb4453f92ee54
#|hsip64 60 d6762890bf26e460
#|hsip64 61 313563a4b7ed5cf3
#|hsip64 62 f90b3ab572d46693
#|hsip64 63 2ea63c71bf326087
#|
#|sip13 15 5699512a6dd820d3
#|sip48 15 e0a6a97dd589d383
#|sip13 63 a8b3bbb76290199d
#|sip24 bulk 9f3f57d2e8cedb67
#|hsip13 15 047b25d0
#|hsip13 63 04831787
#|pieces 724506eb4c328a95
#|bytes9 b0e4a90bdf82009e
#|hpieces 59ea4a74
#|key15 refused 15
#|key16 accepted 2d7efbd796666785
#|hkey16 refused 16
#|hkey8 accepted 8afee704
