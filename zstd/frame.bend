# bend-osdev-zstd, frames (RFC 8878, section 3.1): the decoder of a stream
# of frames, as a machine fed one byte at a time.
#
# A stream is frames back to back: Zstandard frames (magic 0xFD2FB528) and
# skippable frames (magic 0x184D2A50 to 0x184D2A5F, a 4-byte size, that many
# bytes). A Zstandard frame is a header (the frame header descriptor, then
# a window descriptor unless single-segment, a dictionary ID and the
# content size, as the descriptor says), blocks (a 3-byte header: last
# block, type, size; then raw bytes, one RLE byte, or a compressed block),
# and a content checksum if the descriptor asks for one.
#
# The machine (ZstdDecoder) takes its input a byte at a time, so the same
# code decodes a stream given whole or in pieces (zstd.bend). It keeps the
# window and the state a frame carries from block to block, and the output
# not yet taken. A compressed block is decoded once all its bytes are in.
import Base
import ../word64/word64.bend as W
import ../bytes/bytes.bend as B
import ./error.bend as E
import ./xxh64.bend as X
import ./block.bend as K
import ./bits.bend as Bi
import ./sequences.bend as S
import ./dict.bend as D

# a limit on the output: none, or at most max bytes
type ZstdLimit is Data:
  ZstdNoLimit{}
  ZstdLimit{max: U32}

# the room left: any, or n bytes
type ZsRoom is Data:
  ZsRoomAny{}
  ZsRoomN{n: Nat}

# what stays the same through a stream: the dictionary (and its content's
# size), whether checksums are verified, the largest window accepted
type ZsCfg is Data:
  ZsCfg{dict: D.ZstdDict, dl: Nat, verify: Bool, max_window: U32}

# the frame being decoded: its window size, Block_Maximum_Size, whether it
# has a checksum, its content size if given, the block state, the hash of
# its content so far
type ZsFrm is Data:
  ZsFrm{window: Nat, block_max: Nat, check: Bool, fcs: Maybe<&2, Nat>, bst: K.ZstdBlockState, hash: X.ZstdXxh64}

# what the next byte is
type ZsPh is Data:
  # n bytes of a magic number so far (reversed)
  ZsPhMagic{n: Nat, acc: List<&2, U32>}
  # a skippable frame's size, n bytes so far; then n bytes to skip
  ZsPhSkipSize{n: Nat, acc: List<&2, U32>}
  ZsPhSkip{n: Nat}
  # the frame header descriptor; then need more header bytes
  ZsPhFhd{}
  ZsPhHdr{fhd: Nat, need: Nat, acc: List<&2, U32>}
  # a block header, n bytes so far
  ZsPhBlock{n: Nat, acc: List<&2, U32>}
  # n bytes of a raw block left; an RLE block of n bytes; n bytes of a
  # compressed block left (the ones so far reversed in acc)
  ZsPhRaw{n: Nat, last: Bool}
  ZsPhRle{n: Nat, last: Bool}
  ZsPhComp{n: Nat, last: Bool, acc: List<&2, U32>}
  # the checksum, n bytes so far
  ZsPhSum{n: Nat, acc: List<&2, U32>}
  # a failure: every later byte is ignored
  ZsPhBad{e: E.ZstdError}

# the decoder: the phase, the frame, the output not yet taken (reversed),
# the room left, the configuration, the window
type ZstdDecoder is Type:
  ZstdDecoder{ph: ZsPh, frm: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow}

def frm.none() -> ZsFrm:
  ZsFrm{0n, 0n, False{}, None{}, K.ZstdBlockState{None{}, S.ZstdSeqTables.none(), K.ZstdReps.initial(), 0n}, X.ZstdXxh64.start(W.W64.zero())}

def frm.bad(e: E.ZstdError, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  ZstdDecoder{ZsPhBad{e}, f, out, room, cfg, win}

def frm.nat(xs: List<&2, U32>, i: Nat) -> Nat:
  U32.to_nat(B.byte(Maybe.default(&2, U32, B.at(xs, i), 0)))

# the little-endian value of k bytes from xs[i] (Horner's rule, from the
# most significant byte: no large factor is carried from step to step)
def frm.le(k: Nat, +xs: List<&2, U32>, +i: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+p:
      Nat.add(frm.nat(xs, i), Nat.mul(256n, frm.le(p, xs, 1n+i)))

# the Frame_Content_Size field: k bytes from xs[i], little-endian, except
# that a value of 2^48 or more (an 8-byte field whose top two bytes are not
# both zero) is held as 2^48 - 1, the largest Nat a native build holds. No
# frame this decoder can finish produces that many bytes, so the frames
# accepted and the errors given are unchanged: a single-segment frame's
# window is still over any limit (ZstdWindowTooLarge), and any other frame
# still fails its content size check
def frm.fcs_raw(fits: Bool, +k: Nat, +xs: List<&2, U32>, +i: Nat) -> Nat:
  match fits:
    case True{}:
      frm.le(k, xs, i)
    case False{}:
      Nat.add(Nat.mul(16777215n, 16777216n), 16777215n)

def frm.fcs_le(+k: Nat, +xs: List<&2, U32>, +i: Nat) -> Nat:
  frm.fcs_raw(Bool.or(Nat.is_le(k, 6n), Nat.is_eq(Nat.add(frm.nat(xs, Nat.add(i, 6n)), frm.nat(xs, Nat.add(i, 7n))), 0n)), k, xs, i)

def ZstdFrame.u32le(+xs: List<&2, U32>) -> U32:
  Bi.ZstdBits.u32le(xs)

# Output

# k less n, if n <= k (both taken apart one at a time, so that a large
# room is never shared: see AGENTS.md on --verdict and large Nat values)
def frm.room_dec(n: Nat, k: Nat) -> Maybe<&2, ZsRoom>:
  match n:
    case 0n:
      Some{ZsRoomN{k}}
    case 1n+m:
      match k:
        case 0n:
          None{}
        case 1n+j:
          frm.room_dec(m, j)

# the room after n bytes
def frm.room_n(r: ZsRoom, n: Nat) -> Maybe<&2, ZsRoom>:
  match r:
    case ZsRoomAny{}:
      Some{ZsRoomAny{}}
    case ZsRoomN{k}:
      frm.room_dec(n, k)

def frm.hash1(check: Bool, h: X.ZstdXxh64, b: U32) -> X.ZstdXxh64:
  match check:
    case True{}:
      X.ZstdXxh64.update_byte(h, b)
    case False{}:
      h

def frm.hash_bytes(xs: List<&2, U32>, +check: Bool, h: X.ZstdXxh64) -> X.ZstdXxh64:
  match xs:
    case Nil{}:
      h
    case Con{b, t}:
      frm.hash_bytes(t, check, frm.hash1(check, h, b))

# the frame after one byte of a raw or RLE block
def frm.put(f: ZsFrm, +b: U32) -> ZsFrm:
  match f:
    case ZsFrm{w, bm, +check, fcs, bst, hash}:
      ZsFrm{w, bm, check, fcs, K.ZstdBlk.put(bst), frm.hash1(check, hash, b)}

# the frame, the output and the window after some bytes
type ZsOut is Type:
  ZsOut{f: ZsFrm, out: List<&2, U32>, win: K.ZstdWindow}

# n copies of b
def frm.puts(n: Nat, +b: U32, f: ZsFrm, out: List<&2, U32>, win: K.ZstdWindow) -> ZsOut:
  match n:
    case 0n:
      ZsOut{f, out, win}
    case 1n+k:
      frm.puts(k, b, frm.put(f, b), Con{b, out}, K.ZstdWin.put(win, b))

# The end of a block, and of a frame

def frm.fcs_ok(fcs: Maybe<&2, Nat>, +produced: Nat) -> Bool:
  match fcs:
    case None{}:
      True{}
    case Some{n}:
      Nat.is_eq(n, produced)

def frm.after_frame(ok: Bool, check: Bool, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match ok:
    case True{}:
      match check:
        case True{}:
          ZstdDecoder{ZsPhSum{0n, Nil{}}, f, out, room, cfg, win}
        case False{}:
          ZstdDecoder{ZsPhMagic{0n, Nil{}}, f, out, room, cfg, win}
    case False{}:
      frm.bad(E.ZstdBadContentSize{}, f, out, room, cfg, win)

def frm.frame_end(f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match f:
    case ZsFrm{w, bm, +check, +fcs, +bst, hash}:
      frm.after_frame(frm.fcs_ok(fcs, K.ZstdBlk.produced(bst)), check, ZsFrm{w, bm, check, fcs, bst, hash}, out, room, cfg, win)

def frm.end_block(last: Bool, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match last:
    case True{}:
      frm.frame_end(f, out, room, cfg, win)
    case False{}:
      ZstdDecoder{ZsPhBlock{0n, Nil{}}, f, out, room, cfg, win}

# Raw, RLE and compressed blocks

# a byte of a raw block, n bytes of it left (n at least 1; the room for
# them was taken at the block header)
def frm.raw(n: Nat, last: Bool, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow, +b: U32) -> ZstdDecoder:
  match n:
    case 0n:
      frm.end_block(last, frm.put(f, b), Con{b, out}, room, cfg, K.ZstdWin.put(win, b))
    case 1n+k:
      match k:
        case 0n:
          frm.end_block(last, frm.put(f, b), Con{b, out}, room, cfg, K.ZstdWin.put(win, b))
        case 1n+j:
          ZstdDecoder{ZsPhRaw{1n+j, last}, frm.put(f, b), Con{b, out}, room, cfg, K.ZstdWin.put(win, b)}

# a raw block of n bytes (n at least 1) starts: its bytes must fit in the room
def frm.raw.start(r: Maybe<&2, ZsRoom>, +n: Nat, last: Bool, f: ZsFrm, out: List<&2, U32>, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match r:
    case None{}:
      frm.bad(E.ZstdOutputTooLarge{}, f, out, ZsRoomN{0n}, cfg, win)
    case Some{room}:
      ZstdDecoder{ZsPhRaw{n, last}, f, out, room, cfg, win}

def frm.rle.out(o: ZsOut, last: Bool, room: ZsRoom, cfg: ZsCfg) -> ZstdDecoder:
  match o:
    case ZsOut{f, out, win}:
      frm.end_block(last, f, out, room, cfg, win)

# the byte of an RLE block of n bytes
def frm.rle(r: Maybe<&2, ZsRoom>, +n: Nat, last: Bool, f: ZsFrm, out: List<&2, U32>, cfg: ZsCfg, win: K.ZstdWindow, +b: U32) -> ZstdDecoder:
  match r:
    case None{}:
      frm.bad(E.ZstdOutputTooLarge{}, f, out, ZsRoomN{0n}, cfg, win)
    case Some{room}:
      frm.rle.out(frm.puts(n, B.byte(b), f, out, win), last, room, cfg)

def frm.comp.emit(r: Maybe<&2, ZsRoom>, +bytes: List<&2, U32>, last: Bool, f: ZsFrm, out: List<&2, U32>, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match r:
    case None{}:
      frm.bad(E.ZstdOutputTooLarge{}, f, out, ZsRoomN{0n}, cfg, win)
    case Some{room}:
      match f:
        case ZsFrm{w, bm, +check, fcs, bst, hash}:
          frm.end_block(last, ZsFrm{w, bm, check, fcs, bst, frm.hash_bytes(bytes, check, hash)}, B.rev_onto(bytes, out), room, cfg, win)

def frm.with_bst(f: ZsFrm, bst: K.ZstdBlockState) -> ZsFrm:
  match f:
    case ZsFrm{w, bm, check, fcs, old, hash}:
      ZsFrm{w, bm, check, fcs, bst, hash}

def frm.comp.done(r: Result<&2, &1, E.ZstdError, K.ZstdBlockOut>, last: Bool, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg) -> ZstdDecoder:
  match r:
    case Fail{e}:
      frm.bad(e, f, out, room, cfg, K.ZstdWin.new(0n))
    case Done{K.ZstdBlockOut{+bytes, bst, win}}:
      frm.comp.emit(frm.room_n(room, B.len.fast(bytes)), bytes, last, frm.with_bst(f, bst), out, cfg, win)

# a compressed block, all its bytes in
def frm.comp(xs: List<&2, U32>, last: Bool, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match f:
    case ZsFrm{+w, +bm, check, fcs, +bst, hash}:
      match cfg:
        case ZsCfg{dict, +dl, verify, mw}:
          frm.comp.done(K.ZstdBlk.decode(xs, bst, win, w, dl, bm), last, ZsFrm{w, bm, check, fcs, bst, hash}, out, room, ZsCfg{dict, dl, verify, mw})

# The block header: last block (bit 0), type (bits 1-2), size (bits 3-23)

def frm.block.kind(t: Nat, +size: Nat, last: Bool, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match t:
    case 0n:
      match size:
        case 0n:
          frm.end_block(last, f, out, room, cfg, win)
        case 1n+k:
          frm.raw.start(frm.room_n(room, 1n+k), 1n+k, last, f, out, cfg, win)
    case 1n+p:
      match p:
        case 0n:
          ZstdDecoder{ZsPhRle{size, last}, f, out, room, cfg, win}
        case 1n+q:
          match q:
            case 0n:
              match size:
                case 0n:
                  frm.comp(Nil{}, last, f, out, room, cfg, win)
                case 1n+k:
                  ZstdDecoder{ZsPhComp{1n+k, last, Nil{}}, f, out, room, cfg, win}
            case 1n+r:
              frm.bad(E.ZstdBadBlockType{}, f, out, room, cfg, win)

# type 3 is reserved; a size past Block_Maximum_Size is refused
def frm.block.check(is3: Bool, ok: Bool, +t: Nat, +size: Nat, last: Bool, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match is3:
    case True{}:
      frm.bad(E.ZstdBadBlockType{}, f, out, room, cfg, win)
    case False{}:
      match ok:
        case True{}:
          frm.block.kind(t, size, last, f, out, room, cfg, win)
        case False{}:
          frm.bad(E.ZstdBlockTooLarge{}, f, out, room, cfg, win)

def frm.bool(+n: Nat) -> Bool:
  Nat.is_eq(n, 1n)

def frm.frame_bm(f: ZsFrm) -> Nat:
  match f:
    case ZsFrm{w, bm, check, fcs, bst, hash}:
      bm

# the third byte of a block header
def frm.block(+xs: List<&2, U32>, +f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  +b0 = frm.nat(xs, 0n)
  +t = Nat.mod(Nat.div(b0, 2n), 4n)
  +size = Nat.add(Nat.div(b0, 8n), Nat.add(Nat.mul(frm.nat(xs, 1n), 32n), Nat.mul(frm.nat(xs, 2n), 8192n)))
  frm.block.check(Nat.is_eq(t, 3n), Nat.is_le(size, frm.frame_bm(f)), t, size, frm.bool(Nat.mod(b0, 2n)), f, out, room, cfg, win)

# The frame header (RFC 8878, section 3.1.1.1)

# the header's length after the descriptor: the window descriptor (unless
# single-segment), the dictionary ID (0, 1, 2 or 4 bytes), the content size
# (0 or 1 when single-segment, 2, 4 or 8 bytes)
def frm.did_size(+flag: Nat) -> Nat:
  match flag:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          1n
        case 1n+q:
          match q:
            case 0n:
              2n
            case 1n+r:
              4n

def frm.fcs_size(+flag: Nat, single: Bool) -> Nat:
  match flag:
    case 0n:
      match single:
        case True{}:
          1n
        case False{}:
          0n
    case 1n+p:
      match p:
        case 0n:
          2n
        case 1n+q:
          match q:
            case 0n:
              4n
            case 1n+r:
              8n

def frm.single(+fhd: Nat) -> Bool:
  frm.bool(Nat.mod(Nat.div(fhd, 32n), 2n))

def frm.wd_size(single: Bool) -> Nat:
  match single:
    case True{}:
      0n
    case False{}:
      1n

def frm.hdr_len(+fhd: Nat) -> Nat:
  Nat.add(Nat.add(frm.wd_size(frm.single(fhd)), frm.did_size(Nat.mod(fhd, 4n))), frm.fcs_size(Nat.div(fhd, 64n), frm.single(fhd)))

# the window size a descriptor gives: 2^(10 + exponent) plus an eighth of
# that per unit of mantissa
def frm.window_of(+wd: Nat) -> Nat:
  +base = Bi.ZstdBits.pow2(Nat.add(10n, Nat.div(wd, 8n)))
  Nat.add(base, Nat.mul(Nat.div(base, 8n), Nat.mod(wd, 8n)))

type ZsHdr is Data:
  ZsHdr{window: Nat, did: U32, fcs: Maybe<&2, Nat>, check: Bool}

def frm.fcs_value(size: Nat, +raw: Nat) -> Maybe<&2, Nat>:
  match size:
    case 0n:
      None{}
    case 1n+p:
      match p:
        case 1n+q:
          match q:
            case 0n:
              Some{Nat.add(raw, 256n)}
            case 1n+r:
              Some{raw}
        case 0n:
          Some{raw}

def frm.window(single: Bool, +fcs: Maybe<&2, Nat>, +xs: List<&2, U32>) -> Nat:
  match single:
    case True{}:
      Maybe.default(&2, Nat, fcs, 0n)
    case False{}:
      frm.window_of(frm.nat(xs, 0n))

# the descriptor fhd and the header bytes after it, xs
def frm.parse_hdr(+fhd: Nat, +xs: List<&2, U32>) -> ZsHdr:
  +single = frm.single(fhd)
  +pos = frm.wd_size(single)
  +dsz = frm.did_size(Nat.mod(fhd, 4n))
  +fsz = frm.fcs_size(Nat.div(fhd, 64n), single)
  +fcs = frm.fcs_value(fsz, frm.fcs_le(fsz, xs, Nat.add(pos, dsz)))
  ZsHdr{frm.window(single, fcs, xs), ZstdFrame.u32le(B.take(dsz, B.drop(pos, xs))), fcs, frm.bool(Nat.mod(Nat.div(fhd, 4n), 2n))}

def frm.new(+window: Nat, check: Bool, fcs: Maybe<&2, Nat>, cfg: ZsCfg) -> ZsFrm:
  match cfg:
    case ZsCfg{dict, dl, verify, mw}:
      match dict:
        case D.ZstdDict{id, content, huf, tables, reps}:
          ZsFrm{window, Nat.min(window, 131072n), check, fcs, K.ZstdBlockState{huf, tables, reps, 0n}, X.ZstdXxh64.start(W.W64.zero())}

# the window a frame starts with: the dictionary's content in a window
# that holds it and the frame's window
def frm.window_new(+window: Nat, cfg: ZsCfg) -> K.ZstdWindow:
  match cfg:
    case ZsCfg{dict, +dl, verify, mw}:
      K.ZstdWin.puts(D.ZstdDict.content(dict), K.ZstdWin.new(K.ZstdWin.depth(window, dl)))

def frm.cfg_max_window(cfg: ZsCfg) -> U32:
  match cfg:
    case ZsCfg{dict, dl, verify, mw}:
      mw

def frm.cfg_dict_id(cfg: ZsCfg) -> U32:
  match cfg:
    case ZsCfg{dict, dl, verify, mw}:
      D.ZstdDict.id(dict)

def frm.cfg_verify(cfg: ZsCfg) -> Bool:
  match cfg:
    case ZsCfg{dict, dl, verify, mw}:
      verify

def frm.start.ok(wok: Bool, dok: Bool, h: ZsHdr, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, +cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match wok:
    case False{}:
      frm.bad(E.ZstdWindowTooLarge{}, f, out, room, cfg, win)
    case True{}:
      match dok:
        case False{}:
          frm.bad(E.ZstdDictionaryMismatch{}, f, out, room, cfg, win)
        case True{}:
          match h:
            case ZsHdr{+window, did, fcs, check}:
              ZstdDecoder{ZsPhBlock{0n, Nil{}}, frm.new(window, check, fcs, cfg), out, room, cfg, frm.window_new(window, cfg)}

# a frame starts: its window must be within the limit, and the dictionary
# it names (if any) the one given
def frm.start(h: ZsHdr, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, +cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match h:
    case ZsHdr{+window, +did, fcs, check}:
      frm.start.ok(Nat.is_le(window, U32.to_nat(frm.cfg_max_window(cfg))), Bool.or(U32.is_eq(did, 0), U32.is_eq(did, frm.cfg_dict_id(cfg))), ZsHdr{window, did, fcs, check}, f, out, room, cfg, win)

# Collecting the fixed fields

def frm.classify(zstd: Bool, skip: Bool, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match zstd:
    case True{}:
      ZstdDecoder{ZsPhFhd{}, f, out, room, cfg, win}
    case False{}:
      match skip:
        case True{}:
          ZstdDecoder{ZsPhSkipSize{0n, Nil{}}, f, out, room, cfg, win}
        case False{}:
          frm.bad(E.ZstdBadMagic{}, f, out, room, cfg, win)

# the first four bytes (each masked to 8 bits) are the Zstandard magic
# number 0xFD2FB528 (little-endian: 0x28 0xB5 0x2F 0xFD), or a skippable
# frame's, 0x184D2A50 to 0x184D2A5F (0x5? 0x2A 0x4D 0x18): compared byte by
# byte, so that LAWS.bend can reason about bytes it does not know
def ZstdFrame.is_zstd(+xs: List<&2, U32>) -> Bool:
  Bool.and(Nat.is_eq(frm.nat(xs, 0n), 40n), Bool.and(Nat.is_eq(frm.nat(xs, 1n), 181n), Bool.and(Nat.is_eq(frm.nat(xs, 2n), 47n), Nat.is_eq(frm.nat(xs, 3n), 253n))))

def ZstdFrame.is_skippable(+xs: List<&2, U32>) -> Bool:
  Bool.and(Nat.is_eq(Nat.div(frm.nat(xs, 0n), 16n), 5n), Bool.and(Nat.is_eq(frm.nat(xs, 1n), 42n), Bool.and(Nat.is_eq(frm.nat(xs, 2n), 77n), Nat.is_eq(frm.nat(xs, 3n), 24n))))

# a byte of a magic number (n before it; full: it is the fourth)
def frm.magic(full: Bool, +n: Nat, acc: List<&2, U32>, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match full:
    case True{}:
      +xs = B.rev(acc)
      frm.classify(ZstdFrame.is_zstd(xs), ZstdFrame.is_skippable(xs), f, out, room, cfg, win)
    case False{}:
      ZstdDecoder{ZsPhMagic{1n+n, acc}, f, out, room, cfg, win}

def frm.skipsize.of(+n: Nat, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match n:
    case 0n:
      ZstdDecoder{ZsPhMagic{0n, Nil{}}, f, out, room, cfg, win}
    case 1n+k:
      ZstdDecoder{ZsPhSkip{n}, f, out, room, cfg, win}

def frm.skipsize(full: Bool, +n: Nat, +acc: List<&2, U32>, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match full:
    case True{}:
      frm.skipsize.of(frm.le(4n, B.rev(acc), 0n), f, out, room, cfg, win)
    case False{}:
      ZstdDecoder{ZsPhSkipSize{1n+n, acc}, f, out, room, cfg, win}

def frm.skip(n: Nat, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match n:
    case 0n:
      ZstdDecoder{ZsPhMagic{0n, Nil{}}, f, out, room, cfg, win}
    case 1n+k:
      match k:
        case 0n:
          ZstdDecoder{ZsPhMagic{0n, Nil{}}, f, out, room, cfg, win}
        case 1n+j:
          ZstdDecoder{ZsPhSkip{1n+j}, f, out, room, cfg, win}

def frm.fhd(reserved: Bool, +fhd: Nat, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match reserved:
    case True{}:
      frm.bad(E.ZstdReservedBit{}, f, out, room, cfg, win)
    case False{}:
      ZstdDecoder{ZsPhHdr{fhd, frm.hdr_len(fhd), Nil{}}, f, out, room, cfg, win}

def frm.hdr(full: Bool, +need: Nat, +fhd: Nat, +acc: List<&2, U32>, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, +cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match full:
    case True{}:
      frm.start(frm.parse_hdr(fhd, B.rev(acc)), f, out, room, cfg, win)
    case False{}:
      ZstdDecoder{ZsPhHdr{fhd, Nat.sub(need, 1n), acc}, f, out, room, cfg, win}

def frm.blockhdr(full: Bool, +n: Nat, +acc: List<&2, U32>, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match full:
    case True{}:
      frm.block(B.rev(acc), f, out, room, cfg, win)
    case False{}:
      ZstdDecoder{ZsPhBlock{1n+n, acc}, f, out, room, cfg, win}

def frm.compb(full: Bool, +n: Nat, last: Bool, +acc: List<&2, U32>, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match full:
    case True{}:
      frm.comp(B.rev(acc), last, f, out, room, cfg, win)
    case False{}:
      ZstdDecoder{ZsPhComp{Nat.sub(n, 1n), last, acc}, f, out, room, cfg, win}

def frm.digest(f: ZsFrm) -> U32:
  match f:
    case ZsFrm{w, bm, check, fcs, bst, hash}:
      W.W64.lo(X.ZstdXxh64.digest(hash))

def frm.sum.check(ok: Bool, f: ZsFrm, out: List<&2, U32>, room: ZsRoom, cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match ok:
    case True{}:
      ZstdDecoder{ZsPhMagic{0n, Nil{}}, f, out, room, cfg, win}
    case False{}:
      frm.bad(E.ZstdBadChecksum{}, f, out, room, cfg, win)

def frm.sum(full: Bool, +n: Nat, +acc: List<&2, U32>, +f: ZsFrm, out: List<&2, U32>, room: ZsRoom, +cfg: ZsCfg, win: K.ZstdWindow) -> ZstdDecoder:
  match full:
    case True{}:
      frm.sum.check(Bool.or(Bool.not(frm.cfg_verify(cfg)), U32.is_eq(ZstdFrame.u32le(B.rev(acc)), frm.digest(f))), f, out, room, cfg, win)
    case False{}:
      ZstdDecoder{ZsPhSum{1n+n, acc}, f, out, room, cfg, win}

# The machine

# the decoder after one more byte b
def ZstdFrame.step(d: ZstdDecoder, +b: U32) -> ZstdDecoder:
  match d:
    case ZstdDecoder{ph, f, out, room, cfg, win}:
      match ph:
        case ZsPhMagic{+n, acc}:
          frm.magic(Nat.is_eq(n, 3n), n, Con{b, acc}, f, out, room, cfg, win)
        case ZsPhSkipSize{+n, acc}:
          frm.skipsize(Nat.is_eq(n, 3n), n, Con{b, acc}, f, out, room, cfg, win)
        case ZsPhSkip{n}:
          frm.skip(n, f, out, room, cfg, win)
        case ZsPhFhd{}:
          +fhd = U32.to_nat(B.byte(b))
          frm.fhd(frm.bool(Nat.mod(Nat.div(fhd, 8n), 2n)), fhd, f, out, room, cfg, win)
        case ZsPhHdr{fhd, +need, acc}:
          frm.hdr(Nat.is_eq(need, 1n), need, fhd, Con{b, acc}, f, out, room, cfg, win)
        case ZsPhBlock{+n, acc}:
          frm.blockhdr(Nat.is_eq(n, 2n), n, Con{b, acc}, f, out, room, cfg, win)
        case ZsPhRaw{n, last}:
          frm.raw(n, last, f, out, room, cfg, win, b)
        case ZsPhRle{+n, last}:
          frm.rle(frm.room_n(room, n), n, last, f, out, cfg, win, b)
        case ZsPhComp{+n, last, acc}:
          frm.compb(Nat.is_eq(n, 1n), n, last, Con{b, acc}, f, out, room, cfg, win)
        case ZsPhSum{+n, acc}:
          frm.sum(Nat.is_eq(n, 3n), n, Con{b, acc}, f, out, room, cfg, win)
        case ZsPhBad{e}:
          ZstdDecoder{ZsPhBad{e}, f, out, room, cfg, win}

# the decoder after the bytes xs
def ZstdFrame.run(xs: List<&2, U32>, d: ZstdDecoder) -> ZstdDecoder:
  match xs:
    case Nil{}:
      d
    case Con{h, t}:
      ZstdFrame.run(t, ZstdFrame.step(d, h))

# a decoder at the start of a stream
def ZstdFrame.new(cfg: ZsCfg, room: ZsRoom) -> ZstdDecoder:
  ZstdDecoder{ZsPhMagic{0n, Nil{}}, frm.none(), Nil{}, room, cfg, K.ZstdWin.new(0n)}

# the output so far (in order) if the decoder is between frames, else the
# failure: the one it met, or ZstdTruncated inside a frame
def ZstdFrame.finish(d: ZstdDecoder) -> Result<&2, &2, E.ZstdError, List<&2, U32>>:
  match d:
    case ZstdDecoder{ph, f, out, room, cfg, win}:
      match ph:
        case ZsPhMagic{n, acc}:
          match n:
            case 0n:
              Done{B.rev(out)}
            case 1n+k:
              Fail{E.ZstdTruncated{}}
        case ZsPhBad{e}:
          Fail{e}
        case _:
          Fail{E.ZstdTruncated{}}

# the output so far (in order), and the decoder without it
type ZstdTaken is Type:
  ZstdTaken{dec: ZstdDecoder, bytes: List<&2, U32>}

def ZstdFrame.take(d: ZstdDecoder) -> ZstdTaken:
  match d:
    case ZstdDecoder{ph, f, out, room, cfg, win}:
      ZstdTaken{ZstdDecoder{ph, f, Nil{}, room, cfg, win}, B.rev(out)}
