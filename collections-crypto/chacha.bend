# ChaCha20 (RFC 8439 section 2.4) and XChaCha20 (draft-irtf-cfrg-xchacha-03
# section 2.3) as stream ciphers: bend-collections' ChaCha block function
# (chacha/chacha20.bend's keystream, which its laws prove equal to RFC 8439's
# block for every key, counter, nonce and round count) as a keystream
# generator for crypto's CrXor, which makes it a stream cipher whose three
# stream laws hold for every state (LAWS.bend).
#
# The state is the key, nonce and next block counter, and the unused bytes
# of the current keystream block, so data may arrive in pieces of any size.
# The round count is a template argument ~r (double rounds: 10 for ChaCha20,
# the named instances; 6 for ChaCha12, 4 for ChaCha8).
#
# The IV: for ChaCha20, 16 bytes, the initial block counter (32 bits,
# little-endian) then the 12-byte nonce, the last four words of RFC 8439's
# state (section 2.3) in order, as Python's cryptography takes its ChaCha20
# nonce; for XChaCha20, the 24-byte nonce, with the block counter starting
# at 0 (the draft's default, section 2.3; its AEAD starts at 1).
#
# The instances:
#   ChaCha20:  ~CcChaState, ~St.CrXorOut<CcChaState>, ~CcChacha.start,
#              ~CcChacha.update(~10n), ~CcChacha.out_state, ~CcChacha.out_data
#   XChaCha20: the same with ~CcChacha.start_x(~10n)
#   (CcChacha.xchacha20_start is the named XChaCha20 start,
#   CcChacha.chacha20_update the named update)
import Base
import ../bytes/bytes.bend as B
import ../crypto/crypto.bend as Cr
import ../crypto/stream.bend as St
import bend-collections-laws-crypto@1.0.0.0/src/crypto/chacha/chacha20.bend as CH

# A ChaCha state (opaque): key, nonce, the next block's counter, and the
# unused keystream bytes of the current block
type CcChaState is Data:
  CcChaState{key: CH.Key, nonce: CH.Nonce, ctr: U32, buf: List<&2, U32>}

def cc.cha.fresh(+k: CH.Key, +n: CH.Nonce, +c: U32, ks: List<&2, U32>) -> St.CrKsStep<CcChaState>:
  match ks:
    case Nil{}:
      St.CrKsStep{0, CcChaState{k, n, c, Nil{}}}
    case Con{b, t}:
      St.CrKsStep{b, CcChaState{k, n, c, t}}

def cc.cha.pop(~r: Nat, +k: CH.Key, +n: CH.Nonce, +c: U32, buf: List<&2, U32>) -> St.CrKsStep<CcChaState>:
  match buf:
    case Nil{}:
      cc.cha.fresh(k, n, U32.add(c, 1), CH.keystream(r, k, c, n))
    case Con{b, t}:
      St.CrKsStep{b, CcChaState{k, n, c, t}}

# The keystream generator: the next keystream byte and the state after it,
# a new block (bend-collections' keystream, with ~r double rounds) when the
# current one is used up
def CcChacha.next(~r: Nat, s: CcChaState) -> St.CrKsStep<CcChaState>:
  match s:
    case CcChaState{k, n, c, buf}:
      cc.cha.pop(~r, k, n, c, buf)

def cc.cha.len_ok(+o: B.Octets, n: Nat) -> Bool:
  Nat.is_eq(B.Octets.len(o), n)

def cc.cha.start_ok(ok: Bool, +key: B.Octets, +iv: B.Octets) -> Result<&2, &2, Cr.CrError, CcChaState>:
  match ok:
    case False{}:
      Fail{Cr.CrBadIvLength{B.Octets.len(iv)}}
    case True{}:
      +ws = CH.words(B.Octets.to_list(iv))
      Done{CcChaState{CH.key(B.Octets.to_list(key)), CH.N{CH.at(ws, 1n), CH.at(ws, 2n), CH.at(ws, 3n)}, CH.at(ws, 0n), Nil{}}}

def cc.cha.start_key(ok: Bool, +key: B.Octets, +iv: B.Octets) -> Result<&2, &2, Cr.CrError, CcChaState>:
  match ok:
    case False{}:
      Fail{Cr.CrBadKeyLength{B.Octets.len(key)}}
    case True{}:
      cc.cha.start_ok(cc.cha.len_ok(iv, 16n), key, iv)

def cc.cha.start(+key: B.Octets, iv: B.Octets) -> Result<&2, &2, Cr.CrError, CcChaState>:
  cc.cha.start_key(cc.cha.len_ok(key, 32n), key, iv)

# The state for a 32-byte key (CrBadKeyLength) and a 16-byte IV, counter ||
# nonce (CrBadIvLength)
def CcChacha.start(key: B.Octets, iv: B.Octets) -> Result<&2, &2, Cr.CrError, CcChaState>:
  cc.cha.start(key, iv)

def cc.cha.xstart_ok(~r: Nat, ok: Bool, +key: B.Octets, +iv: B.Octets) -> Result<&2, &2, Cr.CrError, CcChaState>:
  match ok:
    case False{}:
      Fail{Cr.CrBadIvLength{B.Octets.len(iv)}}
    case True{}:
      +nl = B.Octets.to_list(iv)
      +ws = CH.words(CH.skip(16n, nl))
      Done{CcChaState{CH.key(CH.hchacha_rounds(r, B.Octets.to_list(key), CH.take(16n, nl))), CH.N{0, CH.at(ws, 0n), CH.at(ws, 1n)}, 0, Nil{}}}

def cc.cha.xstart_key(~r: Nat, ok: Bool, +key: B.Octets, +iv: B.Octets) -> Result<&2, &2, Cr.CrError, CcChaState>:
  match ok:
    case False{}:
      Fail{Cr.CrBadKeyLength{B.Octets.len(key)}}
    case True{}:
      cc.cha.xstart_ok(~r, cc.cha.len_ok(iv, 24n), key, iv)

def cc.cha.xstart(~r: Nat, +key: B.Octets, iv: B.Octets) -> Result<&2, &2, Cr.CrError, CcChaState>:
  cc.cha.xstart_key(~r, cc.cha.len_ok(key, 32n), key, iv)

# The XChaCha20 state for a 32-byte key and a 24-byte nonce: the key is
# HChaCha's subkey of the nonce's first 16 bytes (with the stream's ~r
# double rounds: HChaCha20 for XChaCha20), the ChaCha nonce four zero bytes
# and the nonce's last 8
def CcChacha.start_x(~r: Nat, key: B.Octets, iv: B.Octets) -> Result<&2, &2, Cr.CrError, CcChaState>:
  cc.cha.xstart(~r, key, iv)

# the next piece of data, encrypted or decrypted (CrXor over CcChacha.next)
def CcChacha.update(~r: Nat, s: CcChaState, m: B.Octets) -> St.CrXorOut<CcChaState>:
  St.CrXor.update(~CcChaState, ~CcChacha.next(~r), s, m)

def CcChacha.out_state(o: St.CrXorOut<CcChaState>) -> CcChaState:
  St.CrXor.out_state(~CcChaState, o)

def CcChacha.out_data(o: St.CrXorOut<CcChaState>) -> B.Octets:
  St.CrXor.out_data(~CcChaState, o)

# The named instances: ChaCha20 and XChaCha20 (10 double rounds)
def CcChacha.xchacha20_start(key: B.Octets, iv: B.Octets) -> Result<&2, &2, Cr.CrError, CcChaState>:
  CcChacha.start_x(~10n, key, iv)

def CcChacha.chacha20_update(s: CcChaState, m: B.Octets) -> St.CrXorOut<CcChaState>:
  CcChacha.update(~10n, s, m)
