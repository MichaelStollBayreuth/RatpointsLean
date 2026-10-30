/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# Bit masks in byte arrays

A mask is a `ByteArray`; bit `j` is bit `j % 8` of byte `j / 8`. Two operations are primitives
implemented in C (`@[extern c inline]`), each with a reference definition in Lean that the
proofs use: `Ratpoints.Mask.andShr`, the AND with a row shifted to the right, in place when the
mask is not shared, and `Ratpoints.Mask.nextSet`, the first set bit from a position on. The C
code reads and writes 64-bit words; it does not depend on the byte order.

The compiled program runs the C code, the proofs are about the reference definitions: that the
two agree is not proved, it is what one has to trust beyond Lean's runtime.
-/

@[expose] public section

namespace Ratpoints

namespace Mask

/-- Byte `i` of `a` as a natural number, `0` past the end. -/
def byte (a : ByteArray) (i : Nat) : Nat := if h : i < a.size then a[i].toNat else 0

/-- Bit `j` of the mask `a`. -/
def bit (a : ByteArray) (j : Nat) : Bool := (byte a (j / 8)).testBit (j % 8)

/-- Byte `i` of the mask `row` shifted to the right by `s` bits. -/
def shrByte (row : ByteArray) (s i : Nat) : UInt8 :=
  ((byte row (s / 8 + i) + 256 * byte row (s / 8 + i + 1)) >>> (s % 8)).toUInt8

/-- The reference definition of `Ratpoints.Mask.andShr`: byte `i` of the result is byte `i` of
`acc` ANDed with byte `i` of `row` shifted to the right by `s` bits, and the result is the empty
array when every byte is `0`. -/
def andShrSpec (acc row : ByteArray) (s : Nat) : ByteArray :=
  let r : ByteArray := ⟨acc.data.mapIdx fun i x ↦ x &&& shrByte row s i⟩
  if r.data.all (· == 0) then .empty else r

/-- The mask `acc` ANDed with the mask `row` shifted to the right by `s` bits: bit `j < 8 n`
of the result (`n` the size of `acc`) is bit `j` of `acc` and bit `j + s` of `row`; the result is
the empty array when no bit is set. The C code works in place when `acc` is not shared. -/
@[extern c inline "({ lean_object * rp_r = lean_sarray_ensure_exclusive(#1); \
  size_t rp_n = lean_sarray_size(rp_r), rp_m = lean_sarray_size(#2); \
  uint8_t * rp_a = lean_sarray_cptr(rp_r); uint8_t const * rp_b = lean_sarray_cptr(#2); \
  size_t rp_s = lean_is_scalar(#3) ? lean_unbox(#3) : SIZE_MAX; \
  size_t rp_q = rp_s >> 3; unsigned rp_k = (unsigned)(rp_s & 7); \
  size_t rp_w = 0; uint64_t rp_or = 0; \
  if (rp_q < rp_m) { \
    rp_w = (rp_m - rp_q - (rp_k ? 1 : 0)) / 8; if (rp_w > rp_n / 8) rp_w = rp_n / 8; } \
  uint8_t const * rp_c = rp_b + (rp_q < rp_m ? rp_q : 0); \
  if (rp_k == 0) { \
    for (size_t rp_i = 0; rp_i < rp_w; rp_i++) { \
      uint64_t rp_x, rp_y; __builtin_memcpy(&rp_x, rp_a + 8 * rp_i, 8); \
      __builtin_memcpy(&rp_y, rp_c + 8 * rp_i, 8); rp_x &= rp_y; rp_or |= rp_x; \
      __builtin_memcpy(rp_a + 8 * rp_i, &rp_x, 8); } \
  } else { \
    for (size_t rp_i = 0; rp_i < rp_w; rp_i++) { \
      uint64_t rp_x, rp_y; __builtin_memcpy(&rp_x, rp_a + 8 * rp_i, 8); \
      __builtin_memcpy(&rp_y, rp_c + 8 * rp_i, 8); \
      if (__BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__) rp_y = __builtin_bswap64(rp_y); \
      rp_y = (rp_y >> rp_k) | ((uint64_t)rp_c[8 * rp_i + 8] << (64 - rp_k)); \
      if (__BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__) rp_y = __builtin_bswap64(rp_y); \
      rp_x &= rp_y; rp_or |= rp_x; __builtin_memcpy(rp_a + 8 * rp_i, &rp_x, 8); } } \
  for (size_t rp_i = 8 * rp_w; rp_i < rp_n; rp_i++) { \
    size_t rp_t = rp_q + rp_i; \
    unsigned rp_v = rp_t < rp_m ? rp_b[rp_t] : 0; \
    if (rp_t + 1 < rp_m) rp_v |= (unsigned)rp_b[rp_t + 1] << 8; \
    rp_a[rp_i] &= (uint8_t)(rp_v >> rp_k); rp_or |= rp_a[rp_i]; } \
  if (rp_or == 0) lean_sarray_set_size(rp_r, 0); \
  rp_r; })"]
def andShr (acc : ByteArray) (row : @& ByteArray) (s : @& Nat) : ByteArray :=
  andShrSpec acc row s

/-- The reference definition of `Ratpoints.Mask.nextSet`: the first `k` from `j` to `8 n - 1`
with bit `k` of `a` set (`n` the size of `a`), or `8 n`. -/
def nextSetSpec (a : ByteArray) (j : Nat) : Nat :=
  ((List.range' j (8 * a.size - j)).find? (bit a)).getD (8 * a.size)

/-- The first set bit of the mask `a` at or after `j`, or `8 n` (`n` the size of `a`) when there
is none. -/
@[extern c inline "({ size_t rp_n = lean_sarray_size(#1); \
  uint8_t const * rp_a = lean_sarray_cptr(#1); \
  size_t rp_j = lean_is_scalar(#2) ? lean_unbox(#2) : SIZE_MAX; size_t rp_res = 8 * rp_n; \
  if (rp_j < 8 * rp_n) { \
    size_t rp_i = rp_j >> 3; unsigned rp_c = (unsigned)rp_a[rp_i] >> (rp_j & 7); \
    if (rp_c) rp_res = rp_j + (size_t)__builtin_ctz(rp_c); \
    else { \
      rp_i++; \
      for (;;) { uint64_t rp_w; if (rp_i + 8 > rp_n) break; \
        __builtin_memcpy(&rp_w, rp_a + rp_i, 8); if (rp_w) break; rp_i += 8; } \
      while (rp_i < rp_n && rp_a[rp_i] == 0) rp_i++; \
      if (rp_i < rp_n) rp_res = 8 * rp_i + (size_t)__builtin_ctz(rp_a[rp_i]); } } \
  lean_usize_to_nat(rp_res); })"]
def nextSet (a : @& ByteArray) (j : @& Nat) : Nat :=
  nextSetSpec a j

/-- Whether no bit of the mask `a` is set. -/
def isZero (a : ByteArray) : Bool := a.size == 0 || nextSet a 0 == 8 * a.size

/-- The mask of `len` bits, all set, in whole 64-bit words. -/
def ones (len : Nat) : ByteArray :=
  ⟨Array.ofFn (n := 8 * ((len + 63) / 64)) fun i ↦
    if 8 * (i.val + 1) ≤ len then 255
    else if 8 * i.val < len then (2 ^ (len - 8 * i.val) - 1).toUInt8 else 0⟩

/-- The set bits of the mask `a` from `j` on, in ascending order (with `fuel` at least the
number of them). -/
def setBitsFrom (a : ByteArray) : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, j =>
    let k := nextSet a j
    if k < 8 * a.size then k :: setBitsFrom a fuel (k + 1) else []

/-- The set bits of the mask `a`, in ascending order. -/
def setBits (a : ByteArray) : List Nat := setBitsFrom a (8 * a.size) 0

end Mask

end Ratpoints
